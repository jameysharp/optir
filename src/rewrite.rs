use egg::{rewrite, Id, Subst};
use std::collections::{HashMap, HashSet};
use std::iter::once;
use std::num::NonZeroU8;

use crate::analysis::{Analysis, ArgsUsedData};
use crate::language::{Get, GetVec, Op, Signature, Switch};

type Rewrite = egg::Rewrite<Op, Analysis>;
type EGraph = egg::EGraph<Op, Analysis>;

fn is_power_of_two(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        if let Some(c) = egraph[subst[var]].data.constant_fold() {
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
        rewrite!("comm-eq"; "(= ?x ?y)" => "(= ?y ?x)"),
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
        rewrite!("equiv-eq"; "(= ?x ?x)" => "1"),
        rewrite!("equiv-gt"; "(> ?x ?x)" => "0"),
        rewrite!("bool-eq-true"; "(= (= ?a ?b) 1)" => "(= ?a ?b)"),
        rewrite!("bool-gt-true"; "(= (> ?a ?b) 1)" => "(> ?a ?b)"),
        rewrite!("triple-not"; "(= (= (= ?x 0) 0) 0)" => "(= ?x 0)"),
    ]
}

#[derive(Default)]
struct DeepSubst {
    used: ArgsUsedData,
    subst: HashMap<Id, Id>,
}

impl DeepSubst {
    fn new(egraph: &mut EGraph, subst: impl IntoIterator<Item = (Get, Id)>) -> Self {
        let mut used = ArgsUsedData::ZERO;
        let subst = subst
            .into_iter()
            .filter_map(|(from, to)| {
                egraph.lookup(Op::Arg(from)).map(|eclass| {
                    used.set(from.into(), true);
                    (eclass, to)
                })
            })
            .collect();
        DeepSubst { used, subst }
    }

    fn rewrite(&self, egraph: &mut EGraph, id: &mut Id) {
        if let Some(new) = self.subst.get(id) {
            *id = *new;
            return;
        }

        let class = &egraph[*id];
        if (self.used.clone() & class.data.args_used()).not_any() {
            return;
        }

        let mut nodes: Vec<Op> = class.iter().cloned().collect();
        for node in nodes.iter_mut() {
            self.rewrite_all(egraph, node.same_scope_children_mut());
        }

        let mut nodes = nodes.into_iter();
        *id = egraph.add(nodes.next().unwrap());
        for node in nodes {
            let new = egraph.add(node);
            egraph.union(*id, new);
        }
        *id = egraph.find(*id);
    }

    fn rewrite_all<'a>(&self, egraph: &mut EGraph, ids: impl IntoIterator<Item = &'a mut Id>) {
        for id in ids {
            self.rewrite(egraph, id);
        }
    }
}

pub fn variadic_rules(runner: &mut egg::Runner<Op, Analysis>) -> Result<(), String> {
    let egraph = &mut runner.egraph;
    let mut loops = Vec::new();
    let mut switches = Vec::new();
    let mut calls = Vec::new();

    for class in egraph.classes() {
        for node in class.iter() {
            match node {
                Op::Loop(args) => {
                    assert!(args.len() % 2 == 1);
                    let (inputs, nested_scope) = args.split_at(args.len() / 2);
                    let (predicate, results) = nested_scope.split_last().unwrap();
                    loops.push((class.id, inputs.to_vec(), results.to_vec(), *predicate));
                }

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

                Op::Call(args) => {
                    let (&target, inputs) = args.split_first().unwrap();
                    for target in egraph[target].iter() {
                        if let Op::Function(sig, f) = target {
                            calls.push((class.id, inputs.to_vec(), *sig, f.to_vec()));
                        }
                    }
                }

                _ => {}
            }
        }
    }

    for (id, inputs, results, predicate) in loops {
        rewrite_loop(egraph, id, inputs, results, predicate);
    }

    for (id, spec, predicate, input_args, nested_scope) in switches {
        rewrite_switch(egraph, id, spec, predicate, input_args, nested_scope);
    }

    for (id, inputs, sig, func) in calls {
        rewrite_call(egraph, id, inputs, sig, func);
    }

    egraph.rebuild();
    Ok(())
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RewriteResult {
    Renumber(Get),
    CopyFrom(Id),
}
use RewriteResult::*;

fn union_outputs<I>(egraph: &mut EGraph, old: Id, new: Id, new_len: usize, outputs: I)
where
    I: IntoIterator<Item = RewriteResult>,
{
    let mut outputs_changed = false;
    for (idx, rewrite) in outputs.into_iter().enumerate() {
        let idx = idx.try_into().unwrap();
        outputs_changed |= rewrite != Renumber(idx);

        if let Some(old_get) = egraph.lookup(Op::Get(idx, old)) {
            let new_get = match rewrite {
                Renumber(new_idx) => {
                    debug_assert!(usize::from(new_idx) < new_len);
                    egraph.add(Op::Get(new_idx, new))
                }
                CopyFrom(input) => input,
            };
            egraph.union(old_get, new_get);
        }
    }

    if !outputs_changed {
        egraph.union(old, new);
    }
}

fn rewrite_loop(
    egraph: &mut EGraph,
    id: Id,
    mut inputs: Vec<Id>,
    mut results: Vec<Id>,
    mut predicate: Id,
) {
    let initial_subst = inputs
        .iter()
        .enumerate()
        .map(|(idx, arg)| (idx.try_into().unwrap(), *arg));
    let initial_subst = DeepSubst::new(egraph, initial_subst);

    // If this loop's predicate is always false on the first iteration, then the loop body always
    // runs exactly once. None of the other rewrites matter then because the result isn't a loop.
    let mut predicate_once = predicate;
    initial_subst.rewrite(egraph, &mut predicate_once);
    if let Some(0) = egraph[predicate_once].data.constant_fold() {
        initial_subst.rewrite_all(egraph, &mut results);
        union_outputs(egraph, id, id, 0, results.into_iter().map(CopyFrom));
        return;
    }

    let mut outputs: Vec<RewriteResult> = (0..results.len())
        .map(|idx| Renumber(idx.try_into().unwrap()))
        .collect();

    // Inductively identify redundant loop variables. Initial hypothesis: if two inputs are
    // equivalent, their corresponding loop variables are equivalent too.
    let mut dedup_inputs = HashMap::new();
    for (idx, input) in inputs.iter().enumerate() {
        dedup_inputs
            .entry(*input)
            .or_insert_with(GetVec::new)
            .push(idx.try_into().unwrap());
    }

    // Try to prove the hypothesis inductively: merge all variables which seem to be equivalent
    // and check that the loop block's results are still equivalent afterward.
    fn is_group(egraph: &mut EGraph) -> impl FnMut((Id, GetVec)) -> Option<(Id, GetVec)> + '_ {
        |(_, group)| {
            if group.len() > 1 {
                Some((egraph.add(Op::Arg(group[0])), group))
            } else {
                None
            }
        }
    }
    let mut input_groups: Vec<_> = dedup_inputs.drain().filter_map(is_group(egraph)).collect();
    let mut next_groups = Vec::new();
    let mut dedup_subst = DeepSubst::default();
    let mut proved = false;
    while !proved && !input_groups.is_empty() {
        // Rewrite every use of variables from seemingly equivalent groups to refer to one
        // representative member of the group.
        let dedup = input_groups.iter().flat_map(|(representative, group)| {
            group[1..].iter().map(|idx| (*idx, *representative))
        });
        dedup_subst = DeepSubst::new(egraph, dedup);

        // Now test if the hypothesis holds.
        proved = true;
        for (_, group) in input_groups.drain(..) {
            for idx in group {
                let mut result = results[usize::from(idx)];
                dedup_subst.rewrite(egraph, &mut result);
                dedup_inputs
                    .entry(result)
                    .or_insert_with(GetVec::new)
                    .push(idx);
            }
            if dedup_inputs.len() > 1 {
                // Hypothesis falsified, with counter-examples: some inputs that we thought
                // might belong together in this group actually belong in separate groups. Try
                // again, but keep the new groups separate this time. This process always produces
                // smaller groups, so the outer loop is guaranteed to terminate.
                proved = false;
            }
            next_groups.extend(dedup_inputs.drain().filter_map(is_group(egraph)));
        }
        std::mem::swap(&mut input_groups, &mut next_groups);
    }

    let mut to_merge = ArgsUsedData::ZERO;
    if proved {
        for (_, group) in input_groups.iter() {
            for &idx in group[1..].iter() {
                outputs[usize::from(idx)] = Renumber(group[0]);
                to_merge.set(idx.into(), true);
            }
        }

        for (idx, result) in results.iter_mut().enumerate() {
            if !to_merge[idx] {
                dedup_subst.rewrite(egraph, result);
            }
        }
        dedup_subst.rewrite(egraph, &mut predicate);
    }

    // A variable is loop-invariant iff its result is equivalent to its argument. If it's
    // loop-invariant and its input is constant, then it stays constant through the body of the
    // loop too and should be substituted everywhere it's used.
    let mut variant = ArgsUsedData::ZERO;
    let mut constant_subst = Vec::new();
    let mut invariant_inputs = HashMap::new();
    for (idx, result) in results.iter().enumerate() {
        if to_merge[idx] {
            continue;
        }
        match egraph.lookup(Op::Arg(idx.try_into().unwrap())) {
            Some(arg) if arg == *result => {
                let input = inputs[usize::from(arg)];
                if egraph[input].data.constant_fold().is_some() {
                    constant_subst.push((idx.try_into().unwrap(), input));
                } else {
                    // We already de-duplicated equivalent inputs so this must be the only unmerged
                    // variable that both is loop-invariant and has this input expression.
                    // Therefore, this map doesn't need to track multiple values per key.
                    let old = invariant_inputs.insert(input, arg);
                    debug_assert_eq!(old, None);
                }
            }

            _ => variant.set(idx, true),
        }
    }

    // An expression is loop-invariant iff the only variables it uses are loop-invariant.
    let constant_subst = DeepSubst::new(egraph, constant_subst);
    let mut seen = HashSet::new();
    let mut invariant_exprs = HashSet::new();
    for idx in variant.iter_ones() {
        let result = &mut results[idx];
        constant_subst.rewrite(egraph, result);
        find_loop_invariant_exprs(egraph, &variant, &mut seen, &mut invariant_exprs, *result);
    }
    constant_subst.rewrite(egraph, &mut predicate);
    find_loop_invariant_exprs(egraph, &variant, &mut seen, &mut invariant_exprs, predicate);
    drop(seen);

    // Now we have a set of loop-invariant expressions to try moving, or "hoisting", out of the
    // loop. Doing so requires that all uses of those expressions are rewritten to refer to
    // loop-invariant variables, initialized to the value of the hoisted expressions. If we're
    // lucky, a hoisted expression is equivalent to some value that's already a loop-invariant
    // input, and we can just reuse that. Otherwise we have to add a new input.
    let mut hoist_rewrites = DeepSubst::default();
    for invariant_expr in invariant_exprs {
        let mut rewritten = invariant_expr;
        initial_subst.rewrite(egraph, &mut rewritten);
        let new = *invariant_inputs.entry(rewritten).or_insert_with(|| {
            let new_arg = egraph.add(Op::Arg(inputs.len().try_into().unwrap()));
            inputs.push(rewritten);
            results.push(new_arg);
            new_arg
        });
        if new != invariant_expr {
            hoist_rewrites.used |= egraph[invariant_expr].data.args_used();
            hoist_rewrites.subst.insert(invariant_expr, new);
        }
    }

    if !hoist_rewrites.subst.is_empty() {
        hoist_rewrites.rewrite_all(egraph, once(&mut predicate).chain(&mut results));
    }

    // Loop-invariant variables are never needed as outputs from the loop, because we can take
    // their values directly from the inputs instead. So if they also aren't needed inside the
    // loop---aside from the definition of the loop-invariant result---then they aren't needed at
    // all. Loop-variant variables need to be computed even if they aren't used inside the loop
    // because we can't easily tell whether anything outside the loop will need their outputs.
    let mut keep = variant | egraph[predicate].data.args_used();
    for idx in variant.iter_ones() {
        keep |= egraph[results[idx]].data.args_used();
    }

    debug_assert!((to_merge & keep).not_any());

    for rewrite in outputs.iter_mut() {
        if let Renumber(new) = *rewrite {
            if !variant[usize::from(new)] {
                *rewrite = CopyFrom(inputs[usize::from(new)]);
            }
        }
    }

    // Now, remove loop variables that have been identified as unnecessary.
    let orig_count = results.len();
    if let Some(first_remove) = keep[..orig_count].first_zero() {
        if !keep[first_remove..orig_count].any() {
            inputs.truncate(first_remove);
            results.truncate(first_remove);
        } else {
            let mut iter = keep.iter();
            inputs.retain(|_| *iter.next().unwrap());
            let mut iter = keep.iter();
            results.retain(|_| *iter.next().unwrap());

            let mut unused_subst = Vec::new();
            for (idx, rewrite) in outputs.iter_mut().enumerate().skip(first_remove) {
                let idx = idx.try_into().unwrap();
                let mut tmp = idx;
                let new = if let Renumber(new) = rewrite {
                    debug_assert!(keep[usize::from(*new)]);
                    debug_assert!(idx == *new || !keep[usize::from(idx)]);
                    if usize::from(*new) < first_remove {
                        // This variable got merged with one that's not moving.
                        continue;
                    }
                    new
                } else if keep[usize::from(idx)] {
                    // This is a CopyFrom, so nobody outside the loop cares what index it's at now.
                    &mut tmp
                } else {
                    continue;
                };
                *new -= keep[first_remove..usize::from(*new)].count_zeros();
                unused_subst.push((idx, egraph.add(Op::Arg(*new))));
            }

            // If we added variables while hoisting invariant computations out of the loop, then
            // those new variables must all be used somewhere.
            let removed = keep[first_remove..outputs.len()].count_zeros();
            for idx in outputs.len()..orig_count {
                debug_assert!(keep[idx]);
                let idx = idx.try_into().unwrap();
                unused_subst.push((idx, egraph.add(Op::Arg(idx - removed))));
            }

            DeepSubst::new(egraph, unused_subst)
                .rewrite_all(egraph, once(&mut predicate).chain(&mut results));
        }
    }

    let final_count = results.len();
    let loop_args = inputs
        .into_iter()
        .chain(results)
        .chain(once(predicate))
        .collect();
    let new_loop = egraph.add(Op::Loop(loop_args));
    union_outputs(egraph, id, new_loop, final_count, outputs);
}

fn find_loop_invariant_exprs(
    egraph: &EGraph,
    variant: &ArgsUsedData,
    seen: &mut HashSet<Id>,
    exprs: &mut HashSet<Id>,
    root: Id,
) {
    let class = &egraph[root];

    if !seen.insert(class.id) {
        return;
    }

    // Hoist expressions which don't depend on any loop-variant variables.
    if (variant.clone() & class.data.args_used()).not_any() {
        // ...but only if they depend on some loop-invariant variables.
        if class.data.args_used().any() {
            exprs.insert(class.id);
        }
        return;
    }

    // Otherwise, recurse looking for subexpressions that match.
    for op in class.iter() {
        for &child in op.same_scope_children() {
            find_loop_invariant_exprs(egraph, variant, seen, exprs, child);
        }
    }
}

fn rewrite_switch(
    egraph: &mut EGraph,
    id: Id,
    mut spec: Switch,
    predicate: Id,
    mut input_args: Vec<Id>,
    mut nested_scope: Vec<Id>,
) {
    // If we know which case this switch will take, then wire up its results in place of the
    // switch's outputs.
    if let Some(v) = egraph[predicate].data.constant_fold() {
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
        // Remove inputs which are either unused or are redundant with other inputs, and rewrite
        // the cases to use the revised argument order.
        let mut inputs_used = ArgsUsedData::ZERO;
        for &output in nested_scope.iter() {
            inputs_used |= egraph[output].data.args_used();
        }

        let mut dedup_args = Vec::with_capacity(inputs_used.count_ones());
        for (idx, arg) in input_args.iter().enumerate() {
            if inputs_used[idx] && !dedup_args.contains(arg) {
                dedup_args.push(*arg);
            }
        }

        if dedup_args != input_args {
            let mut subst = Vec::new();
            for (old_idx, old) in input_args.into_iter().enumerate() {
                if let Some(new_idx) = dedup_args.iter().position(|new| *new == old) {
                    if old_idx != new_idx {
                        subst.push((
                            old_idx.try_into().unwrap(),
                            egraph.add(Op::Arg(new_idx.try_into().unwrap())),
                        ));
                    }
                }
            }

            DeepSubst::new(egraph, subst).rewrite_all(egraph, &mut nested_scope);
            input_args = dedup_args;
        }
    }

    // Find outputs which are computed with equivalent expressions in every case.
    let mut iter = nested_scope.chunks_exact(spec.outputs.get() as usize);
    let mut common_outputs: Vec<_> = iter.next().unwrap().iter().copied().map(CopyFrom).collect();
    for outputs in iter {
        for (idx, (seen, new)) in common_outputs.iter_mut().zip(outputs.iter()).enumerate() {
            if *seen != CopyFrom(*new) {
                *seen = Renumber(idx.try_into().unwrap());
            }
        }
    }

    let mut has_common = 0;
    let mut has_different = 0;
    let subst = input_args
        .iter()
        .enumerate()
        .map(|(idx, arg)| (idx.try_into().unwrap(), *arg));
    let subst = DeepSubst::new(egraph, subst);
    for output in common_outputs.iter_mut() {
        match output {
            CopyFrom(result) => {
                subst.rewrite(egraph, result);
                has_common += 1;
            }
            Renumber(idx) => {
                *idx -= has_common;
                has_different += 1;
            }
        }
    }

    debug_assert!(has_common != 0 || has_different != 0);

    let mut new_switch = id;
    if let Some(outputs) = NonZeroU8::new(has_different.try_into().unwrap()) {
        if has_common != 0 {
            let mut iter = common_outputs.iter().cycle();
            nested_scope.retain(|_| matches!(iter.next().unwrap(), Renumber(_)));
            spec.outputs = outputs;
            debug_assert_eq!(nested_scope.len(), spec.total_outputs());
        } else {
            debug_assert_eq!(spec.outputs, outputs);
        }

        let switch_args = once(predicate)
            .chain(input_args)
            .chain(nested_scope)
            .collect();
        new_switch = egraph.add(Op::Switch(spec, switch_args));
    }

    union_outputs(egraph, id, new_switch, has_different, common_outputs);
    // TODO: delete switch node from this class?
}

fn rewrite_call(egraph: &mut EGraph, id: Id, inputs: Vec<Id>, sig: Signature, mut func: Vec<Id>) {
    assert_eq!(inputs.len(), sig.inputs.into());
    let (const_inputs, results) = sig.split_scope_mut(&mut func);

    let subst = inputs
        .into_iter()
        .chain(const_inputs.iter().copied())
        .enumerate()
        .map(|(idx, arg)| (idx.try_into().unwrap(), arg));

    DeepSubst::new(egraph, subst).rewrite_all(egraph, results.iter_mut());
    union_outputs(egraph, id, id, 0, results.iter().copied().map(CopyFrom));
}
