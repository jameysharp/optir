#![warn(nonstandard_style)]

use egg::{define_language, rewrite, ENodeOrVar, Id, Language, PatternAst, Subst};
use std::collections::HashMap;
use std::io::Read;
use std::num::NonZeroU8;

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

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Switch {
    cases: NonZeroU8,
    outputs: NonZeroU8,
}

impl Switch {
    fn total_outputs(&self) -> usize {
        self.cases.get() as usize * self.outputs.get() as usize
    }

    pub fn split_scope<'a>(&self, ids: &'a [Id]) -> (&'a [Id], &'a [Id]) {
        let inputs = ids.len().saturating_sub(self.total_outputs());
        assert!(inputs > 0);
        ids.split_at(inputs)
    }

    pub fn split_scope_mut<'a>(&self, ids: &'a mut [Id]) -> (&'a mut [Id], &'a mut [Id]) {
        let inputs = ids.len().saturating_sub(self.total_outputs());
        assert!(inputs > 0);
        ids.split_at_mut(inputs)
    }
}

impl std::fmt::Display for Switch {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "switch-{}-cases-{}-outputs", self.cases, self.outputs)
    }
}

impl std::str::FromStr for Switch {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, &'static str> {
        s.strip_prefix("switch-")
            .and_then(|suf| suf.strip_suffix("-outputs"))
            .and_then(|suf| suf.split_once("-cases-"))
            .and_then(|(cases, outputs)| {
                cases
                    .parse()
                    .and_then(|cases| outputs.parse().map(|outputs| Switch { cases, outputs }))
                    .ok()
            })
            .ok_or("not in 'switch-N-cases-M-outputs' format")
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

        "copy" = Copy(Box<[Id]>),

        // An RVSDG "theta" node representing a structured tail-controlled loop. The last operand
        // is the predicate indicating whether the loop should continue for another iteration. The
        // other operands are N inputs, followed by N results. The input is available in the first
        // iteration as the corresponding argument; on subsequent iterations that argument comes
        // from the corresponding result of the previous iteration. After the final iteration, the
        // result is available as a corresponding output of the loop.
        "loop" = Loop(Box<[Id]>),

        // An RVSDG "gamma" node representing a structured generalized if-then-else block. The
        // first operand is the predicate indicating which case to evaluate. The next operands are
        // inputs provided to the selected case. The remaining operands are case outputs, according
        // to the signature specified in the operator label: for each case, its outputs are
        // contiguous. Every case must have the same input signature as the provided inputs to the
        // "switch" node.
        Switch(Switch, Box<[Id]>),

        // A node representing the arguments of the nearest enclosing structured control block,
        // such as "loop" or "case". The operational semantics depend on which block transitively
        // demanded the value of this node at the current point of evaluation.
        Arg(Get),

        // A node which extracts the Nth output from a node which outputs a tuple.
        Get(Get, Id),

        Const(i32),
    }
}

impl Op {
    pub fn same_scope_children(&self) -> &[Id] {
        match self {
            Op::Loop(args) => {
                assert!(args.len() % 2 == 1);
                let inputs = args.len() / 2;
                &args[..inputs]
            }

            Op::Switch(spec, args) => spec.split_scope(args).0,
            _ => self.children(),
        }
    }

    pub fn same_scope_children_mut(&mut self) -> &mut [Id] {
        match self {
            Op::Loop(args) => {
                assert!(args.len() % 2 == 1);
                let inputs = args.len() / 2;
                &mut args[..inputs]
            }

            Op::Switch(spec, args) => spec.split_scope_mut(args).0,
            _ => self.children_mut(),
        }
    }
}

type ConstantFoldData = Option<(i32, PatternAst<Op>)>;
type ArgsUsedData = bitvec::BitArr!(for u8::MAX as usize);

#[derive(Debug)]
pub struct AnalysisResults {
    pub constant_fold: ConstantFoldData,
    pub args_used: ArgsUsedData,
}

#[derive(Default)]
pub struct Analysis;

fn make_args_used(egraph: &EGraph, enode: &Op) -> ArgsUsedData {
    let mut result = ArgsUsedData::ZERO;
    match enode {
        Op::Arg(idx) => result.set(idx.0 as usize, true),

        _ => {
            for &child in enode.same_scope_children() {
                result |= egraph[child].data.args_used;
            }
        }
    }
    result
}

impl egg::Analysis<Op> for Analysis {
    type Data = AnalysisResults;

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> egg::DidMerge {
        fn merge_constant_fold(to: &mut ConstantFoldData, from: ConstantFoldData) -> egg::DidMerge {
            egg::merge_max(to, from)
        }

        fn merge_args_used(to: &mut ArgsUsedData, from: ArgsUsedData) -> egg::DidMerge {
            // Assume rewrites never add arguments. (If you can compute a result from a certain
            // number of arguments, why would you introduce more arguments of unspecified values to
            // compute the same result?) Then `from` is a subset of `to`, or vice versa. If they
            // aren't equal, then the subset is lexicographically smaller than the superset, which
            // justifies the use of merge_min to pick the subset.
            //
            // This analysis needs to be conservative, reporting all arguments used by any node in
            // the equivalence class. To maintain that invariant, the modify method below must
            // remove nodes which use more arguments than the minimum.

            // Prove the assumption, that the minimum is a subset, by checking the intersection.
            debug_assert_eq!((&*to).min(&from), &{
                let mut tmp = from;
                tmp &= &*to;
                tmp
            });
            egg::merge_min(to, from)
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
                Op::Copy(_) => return None,
                Op::Loop(_) => return None,
                Op::Switch(_, _) => return None,
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

        let constant_fold = make_constant_fold(egraph, enode);
        let args_used = if constant_fold.is_none() {
            make_args_used(egraph, enode)
        } else {
            ArgsUsedData::ZERO
        };
        AnalysisResults {
            constant_fold,
            args_used,
        }
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        let class = &egraph[id];
        if let Some(c) = class.data.constant_fold.clone() {
            if let [Op::Const(v)] = &class.nodes[..] {
                debug_assert_eq!(*v, c.0);
            } else {
                egraph.union_instantiations(
                    &c.1,
                    &vec![ENodeOrVar::ENode(Op::Const(c.0))].into(),
                    &Default::default(),
                    "const-fold".to_string(),
                );

                // If this operation is equivalent to a constant, it doesn't matter what else it
                // might also be equivalent to.
                egraph[id].nodes.splice(.., [Op::Const(c.0)]);
            }
        }

        let class = &egraph[id];
        if class.nodes.len() > 1 {
            // Remove nodes which use strictly more arguments than the current best in this class.
            // When this happens it means that a rewrite has exposed a simpler way to compute the
            // same result, giving a more precise analysis result than we'd previously discovered.
            // Pruning the less-precise alternatives may expose more opportunities for rewrites.
            // However, we keep all alternatives that have the same precision.
            let args_used = &class.data.args_used;
            let keep: bitvec::vec::BitVec = class
                .iter()
                .map(|node| args_used == &make_args_used(egraph, node))
                .collect();
            if !keep.all() {
                let mut iter = keep.into_iter();
                egraph[id].nodes.retain(|_| iter.next().unwrap());
            }
        } else {
            debug_assert_eq!(
                &class.data.args_used,
                &make_args_used(egraph, &class.nodes[0])
            );
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
    let args_used = &class.data.args_used;
    if subst.keys().all(|idx| !args_used[idx.0 as usize]) {
        return;
    }

    let mut nodes: Vec<Op> = class.iter().cloned().collect();
    for node in nodes.iter_mut() {
        if let Op::Arg(idx) = node {
            *id = subst[idx];
            return;
        }

        for child in node.same_scope_children_mut() {
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
    let egraph = &mut runner.egraph;
    let mut switches = Vec::new();
    let mut unions = Vec::new();

    for class in egraph.classes() {
        for node in class.iter() {
            match node {
                Op::Switch(spec, args) => {
                    let (outer_scope, nested_scope) = spec.split_scope(args);
                    let (predicate, input_args) = outer_scope.split_first().unwrap();
                    switches.push((
                        class.id,
                        *spec,
                        *predicate,
                        input_args.to_vec(),
                        nested_scope.to_vec(),
                    ));
                }

                &Op::Get(idx, src) => {
                    for node in egraph[src].iter() {
                        if let Op::Copy(args) = node {
                            unions.push((class.id, args[idx.0 as usize]));
                        }
                    }
                }
                _ => {}
            }
        }
    }

    for (id, mut spec, predicate, mut input_args, mut nested_scope) in switches {
        // If we know which case this switch will take, then wire up its results in place of
        // the switch's outputs.
        if let Some((v, _)) = egraph[predicate].data.constant_fold {
            let o = spec.outputs.get() as usize;
            if v != 0 {
                let (target, source) = nested_scope.split_at_mut(v as usize * o);
                target[..o].copy_from_slice(&source[..o]);
            }
            nested_scope.truncate(o);
            spec.cases = NonZeroU8::new(1).unwrap();
            debug_assert_eq!(nested_scope.len(), spec.total_outputs());
        }

        if spec.cases.get() > 1 {
            // Remove inputs which are either unused or are redundant with other inputs, and
            // rewrite the cases to use the revised argument order.
            let mut inputs_used = ArgsUsedData::ZERO;
            for &output in nested_scope.iter() {
                inputs_used |= egraph[output].data.args_used;
            }

            let mut dedup_args = Vec::with_capacity(inputs_used.count_ones());
            for (idx, arg) in input_args.iter().enumerate() {
                if inputs_used[idx] && !dedup_args.contains(arg) {
                    dedup_args.push(*arg);
                }
            }

            if dedup_args != input_args {
                let mut subst = HashMap::new();
                for (old_idx, old) in input_args.into_iter().enumerate() {
                    if let Some(new_idx) = dedup_args.iter().position(|new| *new == old) {
                        if old_idx != new_idx {
                            subst.insert(
                                Get(old_idx as u8),
                                egraph.add(Op::Arg(Get(new_idx as u8))),
                            );
                        }
                    }
                }

                for output in nested_scope.iter_mut() {
                    rewrite_args(egraph, &subst, output);
                }

                input_args = dedup_args;
            }
        }

        // Find outputs which are computed with equivalent expressions in every case.
        let mut iter = nested_scope.chunks_exact(spec.outputs.get() as usize);
        let mut common_outputs: Vec<_> = iter.next().unwrap().iter().copied().map(Some).collect();
        for outputs in iter {
            for (seen, new) in common_outputs.iter_mut().zip(outputs.iter()) {
                if *seen != Some(*new) {
                    *seen = None;
                }
            }
        }

        let mut has_common = false;
        let mut has_different = 0;
        let subst = input_args
            .iter()
            .enumerate()
            .map(|(idx, arg)| (Get(idx as u8), *arg))
            .collect();
        for output in common_outputs.iter_mut() {
            if let Some(output) = output {
                rewrite_args(egraph, &subst, output);
                has_common = true;
            } else {
                has_different += 1;
            }
        }

        debug_assert!(has_common || has_different != 0);

        let mut new_switch = id;

        if let Some(outputs) = NonZeroU8::new(has_different) {
            if has_common {
                let mut iter = common_outputs.iter().cycle();
                nested_scope.retain(|_| iter.next().unwrap().is_none());
                spec.outputs = outputs;
                debug_assert_eq!(nested_scope.len(), spec.total_outputs());
            } else {
                debug_assert_eq!(spec.outputs, outputs);
            }

            let switch_args = std::iter::once(predicate)
                .chain(input_args)
                .chain(nested_scope)
                .collect::<Box<[Id]>>();
            new_switch = egraph.add(Op::Switch(spec, switch_args));

            if has_common {
                for (idx, output) in common_outputs
                    .iter_mut()
                    .filter(|x| x.is_none())
                    .enumerate()
                {
                    *output = Some(egraph.add(Op::Get(Get(idx as u8), new_switch)));
                }
            }
        }

        if has_common {
            new_switch = egraph.add(Op::Copy(
                common_outputs.into_iter().map(Option::unwrap).collect(),
            ));
        }

        egraph.union(id, new_switch);
        // TODO: delete switch node from this class?
    }

    for (a, b) in unions {
        egraph.union(a, b);
    }

    egraph.rebuild();
    Ok(())
}

struct OpCost;

impl egg::CostFunction<Op> for OpCost {
    type Cost = usize;

    fn cost<C>(&mut self, enode: &Op, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let base_cost = match enode {
            Op::Arg(_) | Op::Const(_) => 0,
            Op::Loop(args) | Op::Switch(_, args) => args.len(),
            // give everything else equal costs for now
            _ => 1,
        };
        enode.fold(base_cost, |sum, id| sum + costs(id))
    }
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

    let extractor = egg::Extractor::new(&runner.egraph, OpCost);

    for &root in runner.roots.iter() {
        let (cost, expr) = extractor.find_best(root);
        println!("cost {}: {}", cost, expr);
    }

    Ok(())
}
