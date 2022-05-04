use egg::{ENodeOrVar, Id, Language, PatternAst};

use crate::language::Op;

type EGraph = egg::EGraph<Op, Analysis>;

type ConstantFoldData = Option<(i32, PatternAst<Op>)>;
pub type ArgsUsedData = bitvec::BitArr!(for u8::MAX as usize);

pub struct AnalysisResults {
    args_used: ArgsUsedData,
    constant_fold: ConstantFoldData,
}

impl AnalysisResults {
    pub fn args_used(&self) -> &ArgsUsedData {
        &self.args_used
    }

    pub fn constant_fold(&self) -> Option<i32> {
        self.constant_fold.as_ref().map(|(v, _)| *v)
    }
}

impl std::fmt::Debug for AnalysisResults {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let AnalysisResults {
            args_used,
            constant_fold,
        } = self;
        if let Some((v, pat)) = constant_fold {
            debug_assert!(args_used.not_any());
            write!(f, "constant fold: {} => {}", pat, v)
        } else {
            f.write_str("args used: ")?;
            f.debug_set().entries(args_used.iter_ones()).finish()
        }
    }
}

#[derive(Default)]
pub struct Analysis;

fn make_args_used(egraph: &EGraph, enode: &Op) -> ArgsUsedData {
    let mut result = ArgsUsedData::ZERO;
    match enode {
        &Op::Arg(idx) => result.set(idx.into(), true),

        _ => {
            for &child in enode.same_scope_children() {
                result |= egraph[child].data.args_used();
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
            debug_assert_eq!((&from).min(to), &(from & &*to));
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
                Op::Loop(_) => return None,
                Op::Switch(_, _) => return None,
                Op::Function(_, _) => return None,
                Op::Call(_) => return None,
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
            let args_used = class.data.args_used();
            let keep: bitvec::vec::BitVec = class
                .iter()
                .map(|node| args_used == &make_args_used(egraph, node))
                .collect();
            if !keep.all() {
                let mut iter = keep.into_iter();
                egraph[id].nodes.retain(|_| iter.next().unwrap());
            }
        }
    }
}
