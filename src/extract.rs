use egg::{Id, Language};

use crate::analysis::Analysis;
use crate::language::Op;

pub struct OpCost;

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

type EGraph = egg::EGraph<Op, Analysis>;

impl egg::LpCostFunction<Op, Analysis> for OpCost {
    fn node_cost(&mut self, _egraph: &EGraph, _eclass: Id, enode: &Op) -> f64 {
        match enode {
            Op::Arg(_) | Op::Const(_) => 0.0,
            Op::Loop(args) | Op::Switch(_, args) => args.len() as f64,
            // give everything else equal costs for now
            _ => 1.0,
        }
    }
}
