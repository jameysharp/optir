#![warn(nonstandard_style)]

use egg::{define_language, rewrite, ENodeOrVar, Id, Language, PatternAst, Subst};
use std::collections::HashMap;
use std::io::Read;

pub type Rewrite = egg::Rewrite<Op, Analysis>;
pub type EGraph = egg::EGraph<Op, Analysis>;

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Get(u8);

impl std::fmt::Display for Get {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "get-{}", self.0)
    }
}

impl std::str::FromStr for Get {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, &'static str> {
        let suffix = s.strip_prefix("get-").ok_or("doesn't start with 'get-'")?;
        Ok(Get(suffix
            .parse()
            .map_err(|_| "output index isn't a number")?))
    }
}

define_language! {
    pub enum Op {
        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),
        "/" = Div([Id; 2]),
        "%" = Mod([Id; 2]),
        "<<" = ShiftLeft([Id; 2]),
        ">>" = ShiftRightZero([Id; 2]),
        ">>s" = ShiftRightSign([Id; 2]),
        "&" = BitAnd([Id; 2]),

        // An RVSDG "theta" node representing a structured tail-controlled loop. The first operand
        // is the predicate indicating whether the loop should continue for another iteration. The
        // remaining operands are pairs of (input, result). The input is available in the first
        // iteration as the corresponding argument; on subsequent iterations that argument comes
        // from the corresponding result of the previous iteration. After the final iteration, the
        // result is available as a corresponding output of the loop.
        "loop" = Loop(Box<[Id]>),

        // An RVSDG "gamma" node representing a structured generalized if-then-else block. The
        // first operand is the predicate indicating which case to evaluate. The next operands are
        // "case" expressions, one for each value in the predicate's range. The remaining operands
        // are inputs provided to the selected case. Every case must have the same input signature
        // as the provided inputs to the "switch" node which contains that case. The output
        // signature of the "switch" is the same as for the cases, which all must have identical
        // output signatures.
        "switch" = Switch(Box<[Id]>),

        // The body of one branch of an RVSDG "gamma" node. The operands are the outputs which the
        // switch node should produce, if this case is selected by the predicate.
        "case" = Case(Box<[Id]>),

        "copy" = Copy(Box<[Id]>),

        // A node representing the arguments of the nearest enclosing structured control block,
        // such as "loop" or "case". The operational semantics depend on which block transitively
        // demanded the value of this node at the current point of evaluation.
        Arg(Get),

        // A node which extracts the Nth output from a node which outputs a tuple.
        Get(Get, Id),

        Const(i32),
    }
}

type ConstantFoldData = Option<(i32, PatternAst<Op>)>;
type ArgsUsedData = u64;

#[derive(Debug)]
pub struct AnalysisResults {
    pub constant_fold: ConstantFoldData,
    pub args_used: ArgsUsedData,
}

#[derive(Default)]
pub struct Analysis;

impl egg::Analysis<Op> for Analysis {
    type Data = AnalysisResults;

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> egg::DidMerge {
        fn merge_constant_fold(to: &mut ConstantFoldData, from: ConstantFoldData) -> egg::DidMerge {
            egg::merge_max(to, from)
        }

        fn merge_args_used(to: &mut ArgsUsedData, from: ArgsUsedData) -> egg::DidMerge {
            let combined = *to | from;
            let result = egg::DidMerge(*to != combined, from != combined);
            *to = combined;
            result
        }

        merge_constant_fold(&mut to.constant_fold, from.constant_fold)
            | merge_args_used(&mut to.args_used, from.args_used)
    }

    fn make(egraph: &EGraph, enode: &Op) -> Self::Data {
        fn make_constant_fold(egraph: &EGraph, enode: &Op) -> ConstantFoldData {
            let c = |i: &Id| egraph[*i].data.constant_fold.as_ref().map(|c| c.0);
            let result = match enode {
                Op::Add([l, r]) => c(l)? + c(r)?,
                Op::Mul([l, r]) => c(l)? * c(r)?,
                Op::Div([l, r]) => c(l)? / c(r)?,
                Op::Mod([l, r]) => c(l)? % c(r)?,
                Op::ShiftLeft([l, r]) => c(l)? << c(r)?,
                Op::ShiftRightZero([l, r]) => ((c(l)? as u32) >> c(r)?) as i32,
                Op::ShiftRightSign([l, r]) => c(l)? >> c(r)?,
                Op::BitAnd([l, r]) => c(l)? & c(r)?,
                Op::Loop(_) => return None,
                Op::Switch(_) => return None,
                Op::Case(_) => return None,
                Op::Copy(_) => return None,
                Op::Arg(_) => return None,
                Op::Get(_, _) => return None,
                Op::Const(c) => *c,
            };

            let mut ast = PatternAst::default();
            let mut enode = enode.clone();
            for child in enode.children_mut() {
                *child = ast.add(ENodeOrVar::ENode(Op::Const(c(child)?)));
            }
            ast.add(ENodeOrVar::ENode(enode));
            Some((result, ast))
        }

        fn make_args_used(egraph: &EGraph, enode: &Op) -> ArgsUsedData {
            match enode {
                Op::Arg(idx) => 1 << idx.0,

                // TODO: identify more precise dependencies when selecting from tuples produced by
                // control-flow or copy nodes
                _ => {
                    let mut result = 0;
                    for &child in enode.children() {
                        let child = &egraph[child];
                        if !matches!(&child.nodes[..], [Op::Case(_)]) {
                            result |= child.data.args_used;
                        }
                    }
                    result
                }
            }
        }

        AnalysisResults {
            constant_fold: make_constant_fold(egraph, enode),
            args_used: make_args_used(egraph, enode),
        }
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        if let Some(c) = egraph[id].data.constant_fold.clone() {
            egraph.union_instantiations(
                &c.1,
                &vec![ENodeOrVar::ENode(Op::Const(c.0))].into(),
                &Default::default(),
                "const-fold".to_string(),
            );

            // If this operation is equivalent to a constant, it doesn't matter what else it might
            // also be equivalent to.
            egraph[id].nodes.retain(|n| n.is_leaf());
        }
    }
}

fn is_power_of_two(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        if let Some((c, _)) = egraph[subst[var]].data.constant_fold {
            c & (c - 1) == 0
        } else {
            false
        }
    }
}

pub fn rules() -> Vec<Rewrite> {
    vec![
        rewrite!("comm-add"; "(+ ?x ?y)" => "(+ ?y ?x)"),
        rewrite!("comm-mul"; "(* ?x ?y)" => "(* ?y ?x)"),
        rewrite!("comm-and"; "(& ?x ?y)" => "(& ?y ?x)"),
        rewrite!("zero-add"; "(+ ?x 0)" => "?x"),
        rewrite!("zero-mul"; "(* ?x 0)" => "0"),
        rewrite!("one-mul"; "(* ?x 1)" => "?x"),
        rewrite!("one-div"; "(/ ?x 1)" => "?x"),
        rewrite!("zero-shift-left"; "(<< ?x 0)" => "?x"),
        rewrite!("zero-shift-right-zero"; "(>> ?x 0)" => "?x"),
        rewrite!("zero-shift-right-sign"; "(>>s ?x 0)" => "?x"),
        rewrite!("zero-and"; "(& ?x 0)" => "0"),
        rewrite!("one-and"; "(& ?x -1)" => "?x"),
        rewrite!("factor"; "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),
        // a+a+a becomes a*3 through repeated application of these rules and const folding.
        rewrite!("factor-one"; "(+ ?a (* ?a ?c))" => "(* ?a (+ 1 ?c))"),
        rewrite!("double"; "(+ ?a ?a)" => "(* ?a 2)"),
        //rewrite!("mul-shift"; "(* ?a ?c)" => "(<< ?a ?c.trailing_zeros())" if is_power_of_two("?c")),
        rewrite!("div-div"; "(/ (/ ?a ?b) ?c)" => "(/ ?a (* ?b ?c))"),
        rewrite!("mask"; "(% ?a ?c)" => "(& ?a (+ ?c -1))" if is_power_of_two("?c")),
        rewrite!("shift-mul"; "(<< ?a ?n)" => "(* ?a (<< 1 ?n))"),
        rewrite!("shift-shift-left"; "(<< (<< ?a ?b) ?c)" => "(<< ?a (+ ?b ?c))"),
        rewrite!("shift-left-back"; "(<< (>> ?a ?b) ?b)" => "(& ?a (<< -1 ?b))"),
    ]
}

fn rewrite_args(egraph: &mut EGraph, subst: &HashMap<Get, Id>, id: &mut Id) {
    let class = &egraph[*id];
    if class.data.args_used == 0 {
        return;
    }

    let mut nodes: Vec<Op> = class.iter().cloned().collect();
    for node in nodes.iter_mut() {
        if let Op::Arg(idx) = node {
            *id = subst[idx];
            return;
        }

        for child in node.children_mut() {
            rewrite_args(egraph, subst, child);
        }
    }

    let mut nodes = nodes.into_iter();
    *id = egraph.add(nodes.next().unwrap());
    for node in nodes {
        let new = egraph.add(node);
        egraph.union(*id, new);
    }
}

fn variadic_rules(runner: &mut egg::Runner<Op, Analysis>) -> Result<(), String> {
    let mut switches = Vec::new();

    for class in runner.egraph.classes() {
        for node in class.iter() {
            match node {
                Op::Switch(args) => switches.push((class.id, args.clone())),
                _ => {}
            }
        }
    }

    for (id, switch_args) in switches.iter() {
        let (predicate, switch_args) = switch_args.split_first().unwrap();

        let mut args_used = 0;
        let mut cases = Vec::new();
        let mut input_args = Vec::new();
        for &arg in switch_args.iter() {
            let class = &runner.egraph[arg];
            if let [Op::Case(args)] = &class.nodes[..] {
                debug_assert!(input_args.is_empty()); // cases come before inputs
                args_used |= class.data.args_used;
                cases.push(args.to_vec());
            } else {
                input_args.push(arg);
            }
        }

        assert!(!cases.is_empty());

        // If we know which case this switch will take, then wire up its results in place of
        // the switch's outputs.
        if let Some((v, _)) = runner.egraph[*predicate].data.constant_fold {
            cases.swap(0, v as usize);
            cases.truncate(1);
        }

        if cases.len() > 1 {
            // Remove inputs which are either unused or are redundant with other inputs, and
            // rewrite the cases to use the revised argument order.
            let mut dedup_args = Vec::with_capacity(args_used.count_ones() as usize);
            for (idx, arg) in input_args.iter().enumerate() {
                if args_used & (1 << idx) != 0 && !dedup_args.contains(arg) {
                    dedup_args.push(*arg);
                }
            }

            if dedup_args != input_args {
                let mut subst = HashMap::new();
                for (old_idx, old) in input_args.into_iter().enumerate() {
                    if let Some(new_idx) = dedup_args.iter().position(|new| *new == old) {
                        subst.insert(
                            Get(old_idx as u8),
                            runner.egraph.add(Op::Arg(Get(new_idx as u8))),
                        );
                    }
                }

                for case in cases.iter_mut() {
                    for output in case.iter_mut() {
                        rewrite_args(&mut runner.egraph, &subst, output);
                    }
                }
            }
            input_args = dedup_args;
        }

        // Find outputs which are computed with equivalent expressions in every case.
        let mut common_outputs = Vec::new();
        for outputs in cases.iter() {
            if common_outputs.is_empty() {
                assert!(!outputs.is_empty());
                common_outputs.extend(outputs.iter().copied().map(Some));
                continue;
            }

            assert_eq!(common_outputs.len(), outputs.len());
            for (seen, new) in common_outputs.iter_mut().zip(outputs.iter()) {
                if *seen != Some(*new) {
                    *seen = None;
                }
            }
        }

        let mut has_common = false;
        let mut has_different = false;
        let subst = input_args
            .iter()
            .enumerate()
            .map(|(idx, arg)| (Get(idx as u8), *arg))
            .collect();
        for output in common_outputs.iter_mut() {
            if let Some(output) = output {
                rewrite_args(&mut runner.egraph, &subst, output);
                has_common = true;
            } else {
                has_different = true;
            }
        }

        debug_assert!(has_common || has_different);

        if has_common && has_different {
            for outputs in cases.iter_mut() {
                let mut iter = common_outputs.iter();
                outputs.retain(|_| iter.next().unwrap().is_none());
            }
        }

        let mut new_switch = *id;
        if has_different {
            let switch_args = std::iter::once(*predicate)
                .chain(
                    cases
                        .into_iter()
                        .map(|outputs| runner.egraph.add(Op::Case(outputs.into_boxed_slice()))),
                )
                .chain(input_args.iter().copied())
                .collect::<Vec<Id>>();
            new_switch = runner
                .egraph
                .add(Op::Switch(switch_args.into_boxed_slice()));

            if has_common {
                for (idx, output) in common_outputs
                    .iter_mut()
                    .filter(|x| x.is_none())
                    .enumerate()
                {
                    *output = Some(runner.egraph.add(Op::Get(Get(idx as u8), new_switch)));
                }
            }
        }

        if has_common {
            new_switch = runner.egraph.add(Op::Copy(
                common_outputs.into_iter().map(Option::unwrap).collect(),
            ));
        }

        runner.egraph.union(*id, new_switch);
        // TODO: delete switch node from this class?
    }

    runner.egraph.rebuild();
    Ok(())
}

pub fn best_nodes(g: &EGraph, root: Id, cost: impl Fn(&Op) -> u64) -> Option<HashMap<Id, Op>> {
    let mut z3_cfg = z3::Config::new();
    z3_cfg.set_model_generation(true);
    let z3 = z3::Context::new(&z3_cfg);

    let class_vars: HashMap<Id, (z3::ast::Bool, Vec<z3::ast::Bool>)> = g
        .classes()
        .map(|class| {
            (
                class.id,
                (
                    z3::ast::Bool::new_const(&z3, format!("c{}", class.id)),
                    (0..class.len())
                        .map(|idx| z3::ast::Bool::new_const(&z3, format!("c{}n{}", class.id, idx)))
                        .collect(),
                ),
            )
        })
        .collect();

    let solver = z3::Optimize::new(&z3);
    solver.assert(&class_vars[&root].0);

    for class in g.classes() {
        let mut pb_buf = Vec::new();
        let (class_var, node_vars) = &class_vars[&class.id];
        for (node, node_var) in class.iter().zip(node_vars) {
            pb_buf.push((node_var, 1));
            for child in node.children() {
                solver.assert(&node_var.implies(&class_vars[&child].0));
            }

            let node_cost = cost(node);
            if node_cost != 0 {
                let omit_node = !node_var;
                solver.assert_soft(&omit_node, node_cost, None);
            }
        }

        let omit_class = !class_var;
        pb_buf.push((&omit_class, 1));
        solver.assert(&z3::ast::Bool::pb_eq(&z3, &pb_buf, 1));
    }

    match solver.check(&[]) {
        z3::SatResult::Sat => {
            let model = solver.get_model().unwrap();
            let mut result = HashMap::new();
            for (class, (class_var, node_vars)) in class_vars {
                let use_class = model.eval(&class_var, false).unwrap().as_bool().unwrap();
                if use_class {
                    for (node, node_var) in g[class].iter().zip(node_vars) {
                        let use_node = model.eval(&node_var, false).unwrap().as_bool().unwrap();
                        if use_node {
                            result.insert(class, node.clone());
                            break;
                        }
                    }
                }
            }
            Some(result)
        }
        res => {
            println!("SAT result: {:?}", res);
            None
        }
    }
}

fn get_best_expr(best: &HashMap<Id, Op>, root: Id) -> egg::RecExpr<Op> {
    fn go(
        best: &HashMap<Id, Op>,
        seen: &mut HashMap<Id, Id>,
        expr: &mut egg::RecExpr<Op>,
        class: Id,
    ) -> Id {
        if let Some(known) = seen.get(&class) {
            return *known;
        }

        let mut node = best[&class].clone();
        for child in node.children_mut() {
            *child = go(best, seen, expr, *child);
        }
        let idx = expr.add(node);
        seen.insert(class, idx);
        idx
    }
    let mut seen = HashMap::new();
    let mut expr = egg::RecExpr::default();
    go(best, &mut seen, &mut expr, root);
    expr
}

fn main() -> std::io::Result<()> {
    let mut input = String::new();
    std::io::stdin().read_to_string(&mut input)?;
    let input = input.parse().unwrap();

    let mut runner = egg::Runner::default()
        .with_expr(&input)
        .with_hook(variadic_rules);

    runner = runner.run(&rules());
    runner.print_report();
    println!("{:?}", runner.egraph.dump());

    for &root in runner.roots.iter() {
        let root = runner.egraph.find(root);

        let best = best_nodes(&runner.egraph, root, |op| match op {
            Op::Arg(_) | Op::Const(_) => 0,
            Op::Switch(args) | Op::Case(args) => args.len() as u64,
            // give everything else equal costs for now
            _ => 1,
        })
        .unwrap();

        println!("{:?}", &best);

        println!("{}", get_best_expr(&best, root));
    }

    Ok(())
}
