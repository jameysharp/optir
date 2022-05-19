//! Rearrange a CFG into structured form.

use petgraph::graph::node_index;
use petgraph::visit::{EdgeRef, GraphBase, VisitMap, Visitable};
use petgraph::Direction;
use std::collections::{HashMap, HashSet};

use super::{Block, Instruction, Names, Operand, Operands, Value, CFG};

type CFGNode = <CFG as GraphBase>::NodeId;

pub fn restructure_cfg(g: &mut CFG, names: &mut Names) {
    restructure_loops(g, names);
    restructure_branches(g, names);
}

fn restructure_loops(g: &mut CFG, names: &mut Names) {
    // Examine only basic blocks which are reachable from the entry block.
    let mut dfs = petgraph::visit::Dfs::new(&*g, node_index(0));
    while dfs.next(&*g).is_some() {}
    restructure_loops_once(g, dfs.discovered, names);
}

const OP_P: Operand = Operand(u16::MAX - 2);
const OP_Q: Operand = Operand(u16::MAX - 1);
const OP_R: Operand = Operand(u16::MAX - 0);

fn restructure_loops_once(g: &mut CFG, include: <CFG as Visitable>::Map, names: &mut Names) {
    for scc in petgraph::algo::tarjan_scc(&petgraph::visit::NodeFiltered(&*g, include)) {
        if scc.len() < 2 {
            // When there's only one block in the SCC, either it isn't a loop, or it's a self-loop.
            // In either case, it's already structured and doesn't need any help.
            continue;
        }

        let mut hashed = g.visit_map();
        for &block in scc.iter() {
            hashed.visit(block);
        }

        let entry_targets: Vec<CFGNode> = scc
            .iter()
            .copied()
            .filter(|&target| {
                g.neighbors_directed(target, Direction::Incoming)
                    .any(|source| !hashed.is_visited(&source))
            })
            .collect();

        let exit_targets: HashSet<CFGNode> = scc
            .iter()
            .flat_map(|&source| {
                g.neighbors_directed(source, Direction::Outgoing)
                    .filter(|target| !hashed.is_visited(target))
            })
            .collect();
        let exit_targets = Vec::from_iter(exit_targets);

        let mut internal_sources = entry_targets
            .iter()
            .chain(exit_targets.iter())
            .flat_map(|&target| g.neighbors_directed(target, Direction::Incoming))
            .filter(|source| hashed.is_visited(source));

        let single_exit = internal_sources
            .next()
            .filter(|&source| internal_sources.all(|other| other == source));

        let mut todo = RewriteEdges::new(g, names);

        // If either the entry target or the exit target needs a predicate set, make sure both
        // cases set it. Otherwise, it looks like it's used uninitialized.
        todo.force_split_if(exit_targets.len() > 1 || entry_targets.len() > 1);

        let within_loop = |source| hashed.is_visited(&source);
        let entry_target = todo.single_entry(&entry_targets, OP_Q, |_| true).unwrap();
        let exit_target = todo.single_entry(&exit_targets, OP_Q, within_loop);
        let loop_tail =
            single_exit.unwrap_or_else(|| todo.single_exit(entry_target, exit_target, within_loop));

        todo.run();

        // Recurse on the subgraph consisting only of nodes in this SCC. Technically the SCC should
        // now include any nodes we just added to the loop: entry_target, loop_tail, and everything
        // which branches to loop_tail. However, the newly added nodes can't be part of any nested
        // loop by construction, so the recursive call can ignore them.
        if hashed.is_visited(&loop_tail) {
            hashed.set(loop_tail.index(), false);
        }
        restructure_loops_once(g, hashed, names);
    }
}

fn restructure_branches(g: &mut CFG, names: &mut Names) {
    // The head immediately dominates the entry block of every non-empty branch, and also every
    // continuation point that more than one branch exits to. It doesn't immediately dominate
    // anything else.
    //
    // - A continuation can't be the exit target for exactly one branch, because then it should
    //   have been part of the branch instead. So its nearest dominator must be the head.
    // - Only the entry block of a branch can be immediately dominated by the head; all other
    //   blocks in the branch are dominated by that branch's entry block.
    //
    // And we can tell the difference between continuation points, which must have at least two
    // (non-loop-edge) predecessors, and entry blocks, which must have exactly one.

    let dominators = petgraph::algo::dominators::simple_fast(&*g, node_index(0));
    let loop_edge = |source, target| dominators.dominators(source).unwrap().any(|x| x == target);

    let mut groups = HashMap::new();
    for block in g.node_indices() {
        if let Some(idom) = dominators.immediate_dominator(block) {
            let is_continuation = g
                .neighbors_directed(block, Direction::Incoming)
                .filter(|&source| !loop_edge(source, block))
                .nth(1)
                .is_some();
            if is_continuation {
                groups.entry(idom).or_insert_with(Vec::new).push(block);
            }
        }
    }

    let mut todo = RewriteEdges::new(g, names);
    for (_entry, continuations) in groups {
        todo.single_entry(&continuations, OP_P, |source| {
            !continuations.contains(&source)
        });
    }
    todo.run();
}

struct RewriteEdges<'a> {
    g: &'a mut CFG,
    names: &'a mut Names,
    force_split: bool,
    workqueue: Vec<(<CFG as GraphBase>::EdgeId, CFGNode, Operands)>,
}

impl<'a> RewriteEdges<'a> {
    fn new(g: &'a mut CFG, names: &'a mut Names) -> RewriteEdges<'a> {
        RewriteEdges {
            g,
            names,
            force_split: false,
            workqueue: Vec::new(),
        }
    }

    fn force_split_if(&mut self, condition: bool) {
        self.force_split = condition;
    }

    fn single_entry(
        &mut self,
        targets: &[CFGNode],
        var: Operand,
        include: impl Fn(CFGNode) -> bool,
    ) -> Option<CFGNode> {
        let demux = match targets {
            [] => return None,
            &[target] if !self.force_split => return Some(target),
            &[target] => target,

            // This region has multiple entry points so we need to introduce a demux block and
            // redirect incoming branches through it.
            _ => self.g.add_node(Block::switch(var)),
        };

        for (idx, &target) in targets.iter().enumerate() {
            let op = self.names.add(Value::Const(idx.try_into().unwrap()));
            self.split_edges(&include, target, demux, &[op, var], idx, false);
        }
        Some(demux)
    }

    fn single_exit(
        &mut self,
        entry_target: CFGNode,
        exit_target: Option<CFGNode>,
        include: impl Fn(CFGNode) -> bool,
    ) -> CFGNode {
        if let Some(exit_target) = exit_target {
            let exit = self.g.add_node(Block::switch(OP_R));
            for (label, target) in [(0, exit_target), (1, entry_target)] {
                let op = self.names.add(Value::Const(label as _));
                self.split_edges(&include, target, exit, &[op, OP_R], label, self.force_split);
            }
            exit
        } else {
            // No exit target means this is an infinite loop.
            let exit = self.g.add_node(Block::goto());
            self.split_edges(&include, entry_target, exit, &[], 0, self.force_split);
            exit
        }
    }

    fn split_edges(
        &mut self,
        include: impl Fn(CFGNode) -> bool,
        old_target: CFGNode,
        new_target: CFGNode,
        new: &[Operand],
        new_weight: usize,
        resplit: bool,
    ) {
        if resplit {
            for (edge, target, operands) in self.workqueue.iter_mut() {
                if *target == old_target && include(self.g.edge_endpoints(*edge).unwrap().0) {
                    *target = new_target;
                    operands.extend_from_slice(new);
                }
            }
        } else {
            self.workqueue.extend(
                self.g
                    .edges_directed(old_target, Direction::Incoming)
                    .filter(|e| include(e.source()))
                    .map(|e| (e.id(), new_target, Operands::from(new))),
            );
        }
        if old_target != new_target {
            self.g.add_edge(new_target, old_target, new_weight);
        }
    }

    fn run(self) {
        self.g.reserve_nodes(self.workqueue.len());
        self.g.reserve_edges(self.workqueue.len());

        for (edge, target, assigns) in self.workqueue {
            let set_predicates = if assigns.is_empty() {
                target
            } else {
                let body = assigns
                    .chunks_exact(2)
                    .map(|assign| Instruction::new("mov", assign).with_inputs(1))
                    .chain(std::iter::once(Instruction::new("goto", [])))
                    .collect();
                self.g.add_node(Block(body))
            };

            // On petgraph's Graph type, adding an edge, then removing another, should leave the
            // new edge with the same ID as the old one, and all other edges unchanged.
            let source = self.g.edge_endpoints(edge).unwrap().0;
            let weight = self.g[edge];
            self.g.add_edge(source, set_predicates, weight);
            self.g.remove_edge(edge);
            debug_assert_eq!(self.g.edge_endpoints(edge), Some((source, set_predicates)));
            debug_assert_eq!(self.g[edge], weight);

            if set_predicates != target {
                self.g.add_edge(set_predicates, target, 0);
            }
        }
    }
}
