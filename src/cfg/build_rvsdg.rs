use egg::{FromOp, Id, RecExpr};
use std::collections::HashMap;
use std::num::NonZeroU8;

use super::from_structured::Structure;
use super::{Block, Names, Operand, Operands};
use crate::language::{Op, Signature, Switch};

pub fn build_rvsdg(names: &Names, region: &Structure, outputs: &Operands) -> RecExpr<Op> {
    let mut builder = Builder::default();
    for (&value, &op) in names.constants.iter() {
        let place = builder.constant(value);
        builder.defs.insert(Operand(op), place);
    }
    builder.build(region);
    let sig = Signature {
        inputs: builder.inputs.try_into().unwrap(),
        outputs: outputs.len().try_into().unwrap(),
    };
    let outputs = outputs.iter().map(|op| builder.defs[op]).collect();
    builder.add(Op::Function(sig, outputs));
    builder.result
}

#[derive(Debug, Default)]
struct Builder {
    defs: HashMap<Operand, Id>,
    result: RecExpr<Op>,
    constants: HashMap<i32, Id>,
    inputs: usize,
}

impl Builder {
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

    fn build(&mut self, region: &Structure) {
        match region {
            Structure::Block(Block(block)) => {
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
            }

            Structure::Linear(seq) => {
                for region in seq {
                    self.build(region);
                }
            }

            Structure::Switch(op, branches) => {
                let mut args = Vec::with_capacity(1 + self.defs.len());
                args.push(self.defs[op]);

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
                for branch in branches {
                    let orig_defs = std::mem::replace(&mut self.defs, inner_defs.clone());
                    self.build(branch);
                    let new_defs = std::mem::replace(&mut self.defs, orig_defs);

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
            }

            Structure::Loop(body, op, val) => {
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

                self.build(body);

                let pred = self.defs[op];
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
                if *val == 1 {
                    args.push(pred);
                } else {
                    let val = self.constant((*val).try_into().unwrap());
                    let pred = self.add(Op::Equal([pred, val]));
                    args.push(pred);
                }

                let place = self.add(Op::Loop(args.into_boxed_slice()));
                for (idx, op) in output_vars.into_iter().enumerate() {
                    self.define(op, Op::Get(idx.try_into().unwrap(), place));
                }
            }
        }
    }
}
