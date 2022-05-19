use petgraph::graph::node_index;
use petgraph::visit::{GraphBase, VisitMap};
use petgraph::Direction;
use std::collections::{HashMap, HashSet};

use super::{Operand, Operands, CFG};

type CFGNode = <CFG as GraphBase>::NodeId;
pub type LiveVariables = HashMap<CFGNode, (Operands, Operands)>;

// This implementation's use of a worklist is inspired by "Iterative Data-flow Analysis,
// Revisited", by Keith D. Cooper, Timothy J. Harvey, and Ken Kennedy. However I've ignored some of
// their most important advice. I didn't want to figure out how to do, for example, reverse
// post-order on the reversed graph when infinite loops may prevent there being an exit block to
// start from. If you find this to be a performance bottleneck, maybe read that paper.

pub fn live_variables(g: &CFG) -> LiveVariables {
    let mut worklist = Vec::with_capacity(g.node_count());
    let mut kills = HashMap::with_capacity(g.node_count());
    let mut live_in = HashMap::with_capacity(g.node_count());

    let mut dfs = petgraph::visit::DfsPostOrder::new(g, node_index(0));
    while let Some(block) = dfs.next(g) {
        let mut gen: HashSet<Operand> = HashSet::new();
        let mut kill: HashSet<Operand> = HashSet::new();
        for instr in g[block].0.iter().rev() {
            let (inputs, outputs) = instr.split();
            for output in outputs {
                debug_assert!(!output.is_const());
                kill.insert(*output);
                gen.remove(output);
            }
            gen.extend(inputs.iter().filter(|op| !op.is_const()));
        }
        worklist.push(block);
        kills.insert(block, kill);
        live_in.insert(block, gen);
    }

    let live_out = |live_in: &HashMap<_, _>, block| {
        let mut live_out = HashSet::new();
        for succ in g.neighbors(block) {
            live_out.extend(&live_in[&succ]);
        }
        live_out
    };

    let mut on_worklist = dfs.finished;
    while let Some(block) = worklist.pop() {
        on_worklist.set(block.index(), false);

        let mut changed = false;
        let live_out = live_out(&live_in, block);
        let live_in = live_in.get_mut(&block).unwrap();
        for &op in live_out.difference(&kills[&block]) {
            changed |= live_in.insert(op);
        }

        if changed {
            for pred in g.neighbors_directed(block, Direction::Incoming) {
                if on_worklist.visit(pred) {
                    worklist.push(pred);
                }
            }
        }
    }

    fn sorted(set: impl IntoIterator<Item = Operand>) -> Operands {
        let mut result = Operands::from_iter(set);
        result.sort_unstable();
        result
    }

    live_in
        .iter()
        .map(|(&block, final_in)| {
            let final_out = live_out(&live_in, block);
            (block, (sorted(final_in.iter().copied()), sorted(final_out)))
        })
        .collect()
}
