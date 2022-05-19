use petgraph::algo::dominators;
use petgraph::graph::node_index;
use petgraph::visit::{EdgeRef, GraphBase, IntoEdgeReferences};
use petgraph::Direction;

use super::{Block, Instruction, Names, Operand, Operands, Value, CFG};

type CFGNode = <CFG as GraphBase>::NodeId;

pub enum Structure {
    Linear(Vec<Structure>),
    Switch(Operand, Vec<Structure>),
    Loop(Box<Structure>, Operand, usize),
    Block(Block),
}

impl std::fmt::Debug for Structure {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Structure::Block(b) => write!(fmt, "{}", b),
            Structure::Linear(seq) => fmt.debug_list().entries(seq).finish(),
            Structure::Switch(op, branches) => {
                write!(fmt, "switch({}) ", op)?;
                fmt.debug_map()
                    .entries(branches.iter().enumerate())
                    .finish()
            }
            Structure::Loop(body, op, val) => {
                write!(fmt, "do ")?;
                std::fmt::Debug::fmt(body, fmt)?;
                write!(fmt, " while({} == {})", op, val)
            }
        }
    }
}

struct RVSDGBuilder<'a> {
    g: &'a CFG,
    constant_one: Operand,
    dominance: dominators::Dominators<CFGNode>,
}

// a function is either:
// - a block with no successors or predecessors,
// - or a block with a single successor, a linear region, and maybe a return block.
pub fn build_function_region(g: &CFG, names: &mut Names) -> (Structure, Operands) {
    let mut start = node_index(0);
    let builder = RVSDGBuilder {
        g,
        constant_one: names.add(Value::Const(1)),
        dominance: dominators::simple_fast(g, start),
    };

    let mut region = Vec::new();
    while builder.g.neighbors(start).next().is_some() {
        if let Some(next) = builder.loop_region(&mut region, start) {
            start = next;
        } else {
            // this function never returns; fake up a return for form's sake
            return (flatten_linear(region), Operands::new());
        }
    }

    let (term, last) = g[start].0.split_last().unwrap();
    append(&mut region, last);

    debug_assert_eq!(&*term.name, "return");
    (flatten_linear(region), term.operands.clone())
}

fn flatten_linear(region: Vec<Structure>) -> Structure {
    if region.len() == 1 {
        region.into_iter().next().unwrap()
    } else {
        Structure::Linear(region)
    }
}

fn append(region: &mut Vec<Structure>, block: &[Instruction]) {
    if !block.is_empty() {
        match region.last_mut() {
            Some(Structure::Block(Block(prev))) => prev.extend_from_slice(block),
            _ => region.push(Structure::Block(Block(block.to_vec()))),
        }
    }
}

impl<'a> RVSDGBuilder<'a> {
    // a linear region is a series of 0 or more of these:
    // - loops,
    // - switches,
    // - or blocks with a single predecessor and successor.
    // it may be followed by an unmatched end (switch end, loop end, or return).

    fn is_loop_edge(&self, edge: &<&CFG as IntoEdgeReferences>::EdgeRef) -> bool {
        self.dominance
            .dominators(edge.source())
            .unwrap()
            .any(|n| n == edge.target())
    }

    // a loop start must either:
    // - have a self-edge,
    // - or start a nested switch, followed by a linear region, then this loop's end.
    fn loop_region(&self, parent: &mut Vec<Structure>, start: CFGNode) -> Option<CFGNode> {
        let loop_edge = self
            .g
            .edges_directed(start, Direction::Incoming)
            .find(|e| self.is_loop_edge(e));

        let (end, label) = if let Some(e) = loop_edge {
            (e.source(), *e.weight())
        } else {
            // not the beginning of a loop; shouldn't be the end either
            return self.switch_region(parent, start);
        };

        let mut region = Vec::new();

        // If this is a self-loop, there's only one block in the loop and it'll be picked up below
        // when checking the end of the loop. Otherwise we need to collect the linear region from
        // inside the loop, but without re-checking the start to see if it's a loop, since we're
        // already handling its "loopiness" here.
        if start != end {
            // We know there's a back edge from somewhere, so this switch must continue somewhere,
            // and so must any linear region that might follow it.
            let mut next = self.switch_region(&mut region, start).unwrap();
            while next != end {
                next = self.loop_region(&mut region, next).unwrap();
            }
        }

        let (term, body) = self.g[end].0.split_last().unwrap();
        append(&mut region, body);
        let body = Box::new(flatten_linear(region));

        if let Some(next) = self.g.neighbors(end).find(|&n| n != start) {
            parent.push(Structure::Loop(body, expect_switch(term), label));
            Some(next)
        } else {
            expect_goto(term);
            parent.push(Structure::Loop(body, self.constant_one, 1));
            None
        }
    }

    // from a switch start, all outgoing edges must go to blocks that either:
    // - have multiple predecessors (this is the end of the switch)
    // - have a single predecessor and a single successor (namely, the end of the switch)
    // - or start a linear region, followed by this switch's end.
    fn switch_region(&self, parent: &mut Vec<Structure>, start: CFGNode) -> Option<CFGNode> {
        // precondition: `start` is not at the end of a loop
        debug_assert!(self.g.edges(start).all(|e| !self.is_loop_edge(&e)));

        let mut branches: Vec<_> = self.g.edges(start).collect();
        debug_assert!(!branches.is_empty());

        let (term, block) = self.g[start].0.split_last().unwrap();
        append(parent, block);

        if branches.len() == 1 {
            expect_goto(term);
            return Some(branches[0].target());
        }

        branches.sort_unstable_by_key(|e| *e.weight());
        debug_assert!(branches.iter().map(|e| *e.weight()).eq(0..branches.len()));

        let mut end = None;
        let mut region = Vec::new();
        for edge in branches {
            let (branch, next) = self.branch_region(edge.target());
            region.push(branch);
            match (end, next) {
                (_, None) => {}
                (Some(a), Some(b)) => debug_assert_eq!(a, b),
                _ => end = next,
            }
        }

        parent.push(Structure::Switch(expect_switch(term), region));
        end
    }

    fn branch_region(&self, branch_head: CFGNode) -> (Structure, Option<CFGNode>) {
        let is_empty = self
            .g
            .edges_directed(branch_head, Direction::Incoming)
            .filter(|e| !self.is_loop_edge(e))
            .nth(1)
            .is_some();

        let mut branch = Vec::new();
        let mut next = Some(branch_head);
        if !is_empty {
            while let Some(current) = next {
                let in_branch = self.g.neighbors(current).next().is_some()
                    && self
                        .dominance
                        .dominators(current)
                        .unwrap()
                        .any(|n| n == branch_head);
                if !in_branch {
                    break;
                }
                next = self.loop_region(&mut branch, current);
            }
        }
        (flatten_linear(branch), next)
    }
}

fn expect_switch(instr: &Instruction) -> Operand {
    debug_assert_eq!(&*instr.name, "switch");
    debug_assert_eq!(instr.operands.len(), 1);
    instr.operands[0]
}

fn expect_goto(instr: &Instruction) {
    debug_assert_eq!(instr, &Instruction::new("goto", []));
}
