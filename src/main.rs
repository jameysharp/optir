#![warn(nonstandard_style)]

use egg::{define_language, rewrite, Analysis, ENodeOrVar, Id, Language, PatternAst, Subst};
use std::collections::HashMap;
use std::io::Read;

pub type Rewrite = egg::Rewrite<Op, ConstantFold>;
pub type EGraph = egg::EGraph<Op, ConstantFold>;

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Arg(u16);

impl std::fmt::Display for Arg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "arg-{}", self.0)
    }
}

impl std::str::FromStr for Arg {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, &'static str> {
        let suffix = s.strip_prefix("arg-").ok_or("doesn't start with 'arg-'")?;
        Ok(Arg(suffix
            .parse()
            .map_err(|_| "argument index isn't a number")?))
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
        Const(i32),
        Arg(Arg),
    }
}

#[derive(Default)]
pub struct ConstantFold;

impl Analysis<Op> for ConstantFold {
    type Data = Option<(i32, PatternAst<Op>)>;

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> egg::DidMerge {
        egg::merge_max(to, from)
    }

    fn make(egraph: &EGraph, enode: &Op) -> Self::Data {
        let c = |i: &Id| egraph[*i].data.as_ref().map(|c| c.0);
        let result = match enode {
            Op::Add([l, r]) => c(l)? + c(r)?,
            Op::Mul([l, r]) => c(l)? * c(r)?,
            Op::Div([l, r]) => c(l)? / c(r)?,
            Op::Mod([l, r]) => c(l)? % c(r)?,
            Op::ShiftLeft([l, r]) => c(l)? << c(r)?,
            Op::ShiftRightZero([l, r]) => ((c(l)? as u32) >> c(r)?) as i32,
            Op::ShiftRightSign([l, r]) => c(l)? >> c(r)?,
            Op::BitAnd([l, r]) => c(l)? & c(r)?,
            Op::Const(c) => *c,
            Op::Arg(_) => return None,
        };

        let mut ast = PatternAst::default();
        let mut enode = enode.clone();
        for child in enode.children_mut() {
            *child = ast.add(ENodeOrVar::ENode(Op::Const(c(child)?)));
        }
        ast.add(ENodeOrVar::ENode(enode));
        Some((result, ast))
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        if let Some(c) = egraph[id].data.clone() {
            egraph.union_instantiations(
                &c.1,
                &vec![ENodeOrVar::ENode(Op::Const(c.0))].into(),
                &Default::default(),
                "const-fold".to_string(),
            );

            // If this operation is equivalent to a constant, it doesn't matter what else it
            // might also be equivalent to.
            egraph[id].nodes.retain(|n| n.is_leaf());
        }
    }
}

fn is_power_of_two(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        if let Some((c, _)) = egraph[subst[var]].data {
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

    let mut runner = egg::Runner::default().with_expr(&input);

    runner = runner.run(&rules());
    runner.print_report();
    println!("{:?}", runner.egraph.dump());

    for &root in runner.roots.iter() {
        let root = runner.egraph.find(root);

        let best = best_nodes(&runner.egraph, root, |op| match op {
            Op::Arg(_) | Op::Const(_) => 0,
            // give everything else equal costs for now
            _ => 1,
        })
        .unwrap();

        println!("{}", get_best_expr(&best, root));
    }

    Ok(())
}
