use egg::{Id, Language};

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
