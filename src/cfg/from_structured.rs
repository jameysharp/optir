use egg::{FromOp, Id, RecExpr};
use petgraph::algo::dominators;
use petgraph::graph::node_index;
use petgraph::visit::{EdgeRef, GraphBase, IntoEdgeReferences};
use petgraph::Direction;
use std::collections::HashMap;
use std::num::NonZeroU8;

use super::{Instruction, Names, Operand, Operands, CFG};
use crate::language::{Op, Signature, Switch};

type CFGNode = <CFG as GraphBase>::NodeId;

struct RVSDGBuilder<'a> {
    g: &'a CFG,
    dominance: dominators::Dominators<CFGNode>,
    defs: HashMap<Operand, Id>,
    result: RecExpr<Op>,
    constants: HashMap<i32, Id>,
    inputs: usize,
}

// a function is either:
// - a block with no successors or predecessors,
// - or a block with a single successor, a linear region, and maybe a return block.
pub fn build_rvsdg(g: &CFG, names: &Names) -> RecExpr<Op> {
    let mut start = node_index(0);
    let mut builder = RVSDGBuilder {
        g,
        dominance: dominators::simple_fast(g, start),
        defs: HashMap::new(),
        result: RecExpr::default(),
        constants: HashMap::new(),
        inputs: 0,
    };
    for (&value, &op) in names.constants.iter() {
        let place = builder.constant(value);
        builder.defs.insert(Operand(op), place);
    }

    while builder.g.neighbors(start).next().is_some() {
        if let Some(next) = builder.loop_region(start) {
            start = next;
        } else {
            // this function never returns; fake up a return for form's sake
            return builder.finish(&Operands::new());
        }
    }

    let term = builder.append(start);
    debug_assert_eq!(&*term.name, "return");
    builder.finish(&term.operands)
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
    fn loop_region(&mut self, start: CFGNode) -> Option<CFGNode> {
        let loop_edge = self
            .g
            .edges_directed(start, Direction::Incoming)
            .find(|e| self.is_loop_edge(e));

        let (end, label) = if let Some(e) = loop_edge {
            (e.source(), *e.weight())
        } else {
            // not the beginning of a loop; shouldn't be the end either
            return self.switch_region(start);
        };

        let mut output_vars = Vec::with_capacity(self.defs.len());
        let mut args = Vec::with_capacity(self.defs.len() * 2 + 1);
        for (op, def) in self.defs.iter() {
            if !op.is_const() {
                output_vars.push(*op);
                args.push(*def);
            }
        }

        for (idx, &op) in output_vars.iter().enumerate() {
            self.define(op, Op::Arg(idx.try_into().unwrap()));
        }

        // If this is a self-loop, there's only one block in the loop and it'll be picked up below
        // when checking the end of the loop. Otherwise we need to collect the linear region from
        // inside the loop, but without re-checking the start to see if it's a loop, since we're
        // already handling its "loopiness" here.
        if start != end {
            // We know there's a back edge from somewhere, so this switch must continue somewhere,
            // and so must any linear region that might follow it.
            let mut next = self.switch_region(start).unwrap();
            while next != end {
                next = self.loop_region(next).unwrap();
            }
        }

        let term = self.append(end);

        let (end, pred) = if let Some(next) = self.g.neighbors(end).find(|&n| n != start) {
            let mut pred = self.defs[&expect_switch(term)];
            if label != 1 {
                let val = self.constant(label.try_into().unwrap());
                pred = self.add(Op::Equal([pred, val]));
            };
            (Some(next), pred)
        } else {
            expect_goto(term);
            (None, self.constant(1))
        };

        let mut outputs: Vec<Id> = output_vars
            .iter()
            .map(|op| self.defs.remove(op).unwrap())
            .collect();
        for (&op, &def) in self.defs.iter() {
            if !op.is_const() {
                outputs.push(def);
                output_vars.push(op);
            }
        }

        args.resize(outputs.len(), self.constant(0));
        args.extend_from_slice(&outputs[..]);
        args.push(pred);

        let place = self.add(Op::Loop(args.into_boxed_slice()));
        for (idx, op) in output_vars.into_iter().enumerate() {
            self.define(op, Op::Get(idx.try_into().unwrap(), place));
        }

        end
    }

    // from a switch start, all outgoing edges must go to blocks that either:
    // - have multiple predecessors (this is the end of the switch)
    // - have a single predecessor and a single successor (namely, the end of the switch)
    // - or start a linear region, followed by this switch's end.
    fn switch_region(&mut self, start: CFGNode) -> Option<CFGNode> {
        // precondition: `start` is not at the end of a loop
        debug_assert!(self.g.edges(start).all(|e| !self.is_loop_edge(&e)));

        let mut branches: Vec<_> = self.g.edges(start).collect();
        debug_assert!(!branches.is_empty());

        let term = self.append(start);

        if branches.len() == 1 {
            expect_goto(term);
            return Some(branches[0].target());
        }

        branches.sort_unstable_by_key(|e| *e.weight());
        debug_assert!(branches.iter().map(|e| *e.weight()).eq(0..branches.len()));

        let op = expect_switch(term);
        let mut args = Vec::with_capacity(1 + self.defs.len());
        args.push(self.defs[&op]);

        let mut inner_defs = self.defs.clone();
        for (idx, (_, def)) in inner_defs
            .iter_mut()
            .filter(|(op, _)| !op.is_const())
            .enumerate()
        {
            args.push(*def);
            *def = self.add(Op::Arg(idx.try_into().unwrap()));
        }

        let zero = self.constant(0);
        let mut partial_outputs = Vec::with_capacity(branches.len());
        let mut places = HashMap::new();
        let mut orig_outputs = Vec::new();
        let mut end = None;
        for edge in branches.iter() {
            let orig_defs = std::mem::replace(&mut self.defs, inner_defs.clone());
            let next = self.branch_region(edge.target());
            let new_defs = std::mem::replace(&mut self.defs, orig_defs);

            match (end, next) {
                (_, None) => {}
                (Some(a), Some(b)) => debug_assert_eq!(a, b),
                _ => end = next,
            }

            let mut outputs = Vec::from(&orig_outputs[..]);
            for (op, def) in new_defs {
                let old_def = inner_defs.get(&op).copied();
                if Some(def) != old_def {
                    let idx = *places.entry(op).or_insert_with(|| {
                        let new = orig_outputs.len();
                        let orig_def = old_def.unwrap_or(zero);
                        orig_outputs.push(orig_def);
                        outputs.push(orig_def);
                        debug_assert_eq!(orig_outputs.len(), outputs.len());
                        new
                    });
                    outputs[idx] = def;
                }
            }
            partial_outputs.push(outputs);
        }

        args.reserve(places.len() * partial_outputs.len());
        for outputs in partial_outputs {
            args.extend_from_slice(&outputs[..]);
            args.extend_from_slice(&orig_outputs[outputs.len()..]);
        }

        let spec = Switch {
            cases: NonZeroU8::new(branches.len().try_into().unwrap()).unwrap(),
            outputs: NonZeroU8::new(places.len().try_into().unwrap()).unwrap(),
        };
        let place = self.add(Op::Switch(spec, args.into_boxed_slice()));
        for (op, idx) in places {
            self.define(op, Op::Get(idx.try_into().unwrap(), place));
        }

        end
    }

    fn branch_region(&mut self, branch_head: CFGNode) -> Option<CFGNode> {
        let is_empty = self
            .g
            .edges_directed(branch_head, Direction::Incoming)
            .filter(|e| !self.is_loop_edge(e))
            .nth(1)
            .is_some();

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
                next = self.loop_region(current);
            }
        }
        next
    }

    fn append(&mut self, block: CFGNode) -> &'a Instruction {
        let (term, block) = self.g[block].0.split_last().unwrap();
        for instr in block {
            let (inputs, outputs) = instr.split();
            let inputs: Vec<Id> = inputs.iter().map(|op| self.defs[op]).collect();
            let place = match &*instr.name {
                "function" => {
                    self.inputs = outputs.len();
                    for (idx, &output) in outputs.iter().enumerate() {
                        self.define(output, Op::Arg(idx.try_into().unwrap()));
                    }
                    continue;
                }
                "mov" => inputs[0],
                "-" => {
                    let minus_one = self.constant(-1);
                    if inputs.len() == 1 {
                        self.add(Op::Mul([minus_one, inputs[0]]))
                    } else {
                        let neg = self.add(Op::Mul([minus_one, inputs[1]]));
                        self.add(Op::Add([inputs[0], neg]))
                    }
                }
                "!" => {
                    let zero = self.constant(0);
                    self.add(Op::Equal([inputs[0], zero]))
                }
                "!=" => {
                    let zero = self.constant(0);
                    let eq = self.add(Op::Equal([inputs[0], inputs[1]]));
                    self.add(Op::Equal([eq, zero]))
                }
                _ => self.add(Op::from_op(&instr.name, inputs).unwrap()),
            };

            if instr.name != "call" && outputs.len() == 1 {
                debug_assert!(!outputs[0].is_const());
                self.defs.insert(outputs[0], place);
            } else {
                for (idx, &output) in outputs.iter().enumerate() {
                    debug_assert!(!output.is_const());
                    self.define(output, Op::Get(idx.try_into().unwrap(), place));
                }
            }
        }
        term
    }

    fn add(&mut self, enode: Op) -> Id {
        self.result.add(enode)
    }

    fn constant(&mut self, val: i32) -> Id {
        *self
            .constants
            .entry(val)
            .or_insert_with(|| self.result.add(Op::Const(val)))
    }

    fn define(&mut self, var: Operand, enode: Op) {
        let place = self.add(enode);
        self.defs.insert(var, place);
    }

    fn finish(mut self, outputs: &Operands) -> RecExpr<Op> {
        let sig = Signature {
            inputs: self.inputs.try_into().unwrap(),
            outputs: outputs.len().try_into().unwrap(),
        };
        let outputs = outputs.iter().map(|op| self.defs[op]).collect();
        self.add(Op::Function(sig, outputs));
        self.result
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
