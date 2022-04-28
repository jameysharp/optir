use egg::{rewrite, Id, Subst};
use std::collections::HashMap;
use std::num::NonZeroU8;

use crate::analysis::{Analysis, ArgsUsedData};
use crate::language::{Get, Op};

type Rewrite = egg::Rewrite<Op, Analysis>;
type EGraph = egg::EGraph<Op, Analysis>;

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

pub fn variadic_rules(runner: &mut egg::Runner<Op, Analysis>) -> Result<(), String> {
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
