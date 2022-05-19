use petgraph::graph::{node_index, Graph};
use smallvec::SmallVec;
use std::borrow::Borrow;
use std::collections::HashMap;
use std::mem::{size_of, take};

pub mod from_structured;
pub mod live_variables;
pub mod restructure;

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Value {
    Name(String),
    Const(i32),
}

const NAME_OPERAND: u16 = 1 << 15;

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Operand(u16);

impl Operand {
    pub fn is_const(&self) -> bool {
        self.0 < NAME_OPERAND
    }
}

impl std::fmt::Display for Operand {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        if self.0 >= NAME_OPERAND {
            write!(fmt, "v{}", self.0 - NAME_OPERAND)
        } else {
            write!(fmt, "c{}", self.0)
        }
    }
}

pub type Operands = SmallVec<[Operand; size_of::<usize>() * 2 / size_of::<Operand>()]>;

#[derive(Clone, Debug, Default)]
pub struct Names {
    names: HashMap<String, u16>,
    constants: HashMap<i32, u16>,
}

impl Names {
    fn add(&mut self, v: Value) -> Operand {
        match v {
            Value::Name(n) => {
                let new = self.names.len().try_into().unwrap();
                Operand(*self.names.entry(n).or_insert(new) + NAME_OPERAND)
            }
            Value::Const(c) => {
                let new = self.constants.len().try_into().unwrap();
                Operand(*self.constants.entry(c).or_insert(new))
            }
        }
    }
}

#[derive(Clone, Debug)]
pub enum ParseError {
    DuplicateLabel,
    UnknownLabel,
    MissingReturn,
    BadOperands,
    BadAssignment,
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Instruction {
    name: String,
    operands: Operands,
    inputs: usize,
}

impl Instruction {
    pub fn new<O: Borrow<[Operand]>>(name: &str, operands: O) -> Self {
        Instruction {
            name: name.to_owned(),
            operands: SmallVec::from(operands.borrow()),
            inputs: 0,
        }
    }

    pub fn with_inputs(self, inputs: usize) -> Self {
        debug_assert!(inputs <= self.operands.len());
        Self { inputs, ..self }
    }

    pub fn split(&self) -> (&[Operand], &[Operand]) {
        self.operands.split_at(self.inputs)
    }
}

impl std::fmt::Display for Instruction {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        fmt.write_str(&self.name)?;
        let (inputs, outputs) = self.operands.split_at(self.inputs);
        for operand in inputs {
            write!(fmt, " {}", operand)?;
        }
        if !outputs.is_empty() {
            fmt.write_str(" ->")?;
            for operand in outputs {
                write!(fmt, " {}", operand)?;
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Block(Vec<Instruction>);

impl Block {
    pub fn switch(operand: Operand) -> Self {
        Block(vec![Instruction::new("switch", [operand]).with_inputs(1)])
    }

    pub fn goto() -> Self {
        Block(vec![Instruction::new("goto", [])])
    }
}

impl std::fmt::Display for Block {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        let mut instructions = self.0.iter();
        if let Some(instruction) = instructions.next() {
            std::fmt::Display::fmt(&instruction, fmt)?;
            for instruction in instructions {
                writeln!(fmt)?;
                std::fmt::Display::fmt(&instruction, fmt)?;
            }
        }
        Ok(())
    }
}

pub type CFG = Graph<Block, usize>;

pub fn parse_instructions(
    lines: impl IntoIterator<Item = String>,
) -> Result<(CFG, Names), ParseError> {
    let mut names = Names::default();
    let mut labels = HashMap::new();
    let mut cfg = Graph::new();
    let mut current_block = Block::default();
    for line in lines {
        let mut tokens = line
            .split_once(&['#', ';'])
            .map_or(&line[..], |(s, _comment)| s)
            .split_whitespace();

        let instr = if let Some(instr) = tokens.next() {
            instr
        } else {
            // Empty or comment line: skip
            continue;
        };
        let mut inputs = 0;
        let mut in_outputs = false;
        let operands: Operands = tokens
            .filter(|&s| {
                if s == "->" {
                    in_outputs = true;
                    false
                } else {
                    if !in_outputs {
                        inputs += 1;
                    }
                    true
                }
            })
            .map(|s| {
                names.add(match s.parse() {
                    Ok(c) => Value::Const(c),
                    Err(_) => Value::Name(s.to_owned()),
                })
            })
            .collect();

        for op in &operands[inputs..] {
            if op.is_const() {
                return Err(ParseError::BadAssignment);
            }
        }

        match instr {
            "label" => {
                if operands.len() != 1 {
                    return Err(ParseError::BadOperands);
                }
                if !current_block.0.is_empty() {
                    cfg.add_node(take(&mut current_block));
                }
                let next_block = node_index(cfg.node_count());
                if labels.insert(operands[0], next_block).is_some() {
                    return Err(ParseError::DuplicateLabel);
                }
            }
            "goto" | "switch" | "return" => {
                current_block.0.push(Instruction::new(instr, operands));
                cfg.add_node(take(&mut current_block));
            }
            instr => {
                current_block
                    .0
                    .push(Instruction::new(instr, operands).with_inputs(inputs));
            }
        }
    }

    if cfg.node_count() == 0 || !current_block.0.is_empty() {
        return Err(ParseError::MissingReturn);
    }

    let last_block = node_index(cfg.node_count() - 1);
    if labels.values().any(|idx| *idx > last_block) {
        return Err(ParseError::MissingReturn);
    }

    for block_idx in cfg.node_indices() {
        let instrs = &mut cfg[block_idx];
        let instr = instrs.0.last_mut().unwrap();
        match &instr.name[..] {
            "return" => {
                instr.inputs = instr.operands.len();
            }
            "goto" => {
                if instr.operands.len() != 1 {
                    return Err(ParseError::BadOperands);
                }
                let target = *labels
                    .get(&instr.operands[0])
                    .ok_or(ParseError::UnknownLabel)?;
                instr.operands.clear();
                cfg.add_edge(block_idx, target, 0);
            }
            "switch" => {
                if instr.operands.len() < 3 {
                    return Err(ParseError::BadOperands);
                }
                instr.inputs = 1;
                let operands: Operands = instr.operands.drain(1..).collect();
                for (idx, label) in operands.into_iter().enumerate() {
                    let target = *labels.get(&label).ok_or(ParseError::UnknownLabel)?;
                    cfg.add_edge(block_idx, target, idx);
                }
            }
            _ => {
                let next_block = node_index(block_idx.index() + 1);
                if next_block > last_block {
                    return Err(ParseError::MissingReturn);
                }
                instrs.0.push(Instruction::new("goto", []));
                cfg.add_edge(block_idx, next_block, 0);
            }
        }
    }

    Ok((cfg, names))
}
