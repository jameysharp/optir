use egg::{define_language, Id, Language};
use std::mem::size_of;
use std::num::NonZeroU8;

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Get(u8);

pub type GetVec = smallvec::SmallVec<[Get; size_of::<usize>() * 2 / size_of::<Get>()]>;

impl std::fmt::Display for Get {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "get-{}", self.0)
    }
}

impl std::str::FromStr for Get {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, &'static str> {
        let suffix = s.strip_prefix("get-").ok_or("doesn't start with 'get-'")?;
        Ok(Get(suffix
            .parse()
            .map_err(|_| "output index isn't a number")?))
    }
}

impl std::convert::TryFrom<usize> for Get {
    type Error = std::num::TryFromIntError;

    fn try_from(value: usize) -> Result<Self, Self::Error> {
        u8::try_from(value).map(Get)
    }
}

impl From<Get> for usize {
    fn from(value: Get) -> Self {
        value.0.into()
    }
}

impl std::ops::Sub<usize> for Get {
    type Output = Get;

    fn sub(self, other: usize) -> Self {
        (usize::from(self) - other).try_into().unwrap()
    }
}

impl std::ops::SubAssign<usize> for Get {
    fn sub_assign(&mut self, other: usize) {
        *self = *self - other;
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Switch {
    pub cases: NonZeroU8,
    pub outputs: NonZeroU8,
}

impl Switch {
    pub fn total_outputs(&self) -> usize {
        self.cases.get() as usize * self.outputs.get() as usize
    }

    pub fn split_scope<'a>(&self, ids: &'a [Id]) -> (&'a [Id], &'a [Id]) {
        let inputs = ids.len().saturating_sub(self.total_outputs());
        assert!(inputs > 0);
        ids.split_at(inputs)
    }

    pub fn split_scope_mut<'a>(&self, ids: &'a mut [Id]) -> (&'a mut [Id], &'a mut [Id]) {
        let inputs = ids.len().saturating_sub(self.total_outputs());
        assert!(inputs > 0);
        ids.split_at_mut(inputs)
    }
}

impl std::fmt::Display for Switch {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "switch-{}-cases-{}-outputs", self.cases, self.outputs)
    }
}

impl std::str::FromStr for Switch {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, &'static str> {
        s.strip_prefix("switch-")
            .and_then(|suf| suf.strip_suffix("-outputs"))
            .and_then(|suf| suf.split_once("-cases-"))
            .and_then(|(cases, outputs)| {
                cases
                    .parse()
                    .and_then(|cases| outputs.parse().map(|outputs| Switch { cases, outputs }))
                    .ok()
            })
            .ok_or("not in 'switch-N-cases-M-outputs' format")
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Signature {
    pub inputs: u8,
    pub outputs: u8,
}

impl Signature {
    pub fn split_scope<'a>(&self, ids: &'a [Id]) -> (&'a [Id], &'a [Id]) {
        let const_inputs = ids.len().checked_sub(self.outputs.into()).unwrap();
        ids.split_at(const_inputs)
    }

    pub fn split_scope_mut<'a>(&self, ids: &'a mut [Id]) -> (&'a mut [Id], &'a mut [Id]) {
        let const_inputs = ids.len().checked_sub(self.outputs.into()).unwrap();
        ids.split_at_mut(const_inputs)
    }
}

impl std::fmt::Display for Signature {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "func-{}-inputs-{}-outputs", self.inputs, self.outputs)
    }
}

impl std::str::FromStr for Signature {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, &'static str> {
        s.strip_prefix("func-")
            .and_then(|suf| suf.strip_suffix("-outputs"))
            .and_then(|suf| suf.split_once("-inputs-"))
            .and_then(|(inputs, outputs)| {
                inputs
                    .parse()
                    .and_then(|inputs| outputs.parse().map(|outputs| Signature { inputs, outputs }))
                    .ok()
            })
            .ok_or("not in 'func-N-inputs-M-outputs' format")
    }
}

define_language! {
    pub enum Op {
        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),
        "/" = Div([Id; 2]),
        "%" = Mod([Id; 2]),
        "<<" = ShiftLeft([Id; 2]),
        ">>" = ShiftRightZero([Id; 2]),
        ">>s" = ShiftRightSign([Id; 2]),
        "&" = BitAnd([Id; 2]),
        "=" = Equal([Id; 2]),
        ">" = Greater([Id; 2]),

        // An RVSDG "theta" node representing a structured tail-controlled loop. The last operand
        // is the predicate indicating whether the loop should continue for another iteration. The
        // other operands are N inputs, followed by N results. The input is available in the first
        // iteration as the corresponding argument; on subsequent iterations that argument comes
        // from the corresponding result of the previous iteration. After the final iteration, the
        // result is available as a corresponding output of the loop.
        "loop" = Loop(Box<[Id]>),

        // An RVSDG "gamma" node representing a structured generalized if-then-else block. The
        // first operand is the predicate indicating which case to evaluate. The next operands are
        // inputs provided to the selected case. The remaining operands are case outputs, according
        // to the signature specified in the operator label: for each case, its outputs are
        // contiguous. Every case must have the same input signature as the provided inputs to the
        // "switch" node.
        Switch(Switch, Box<[Id]>),

        // An RVSDG "lambda" node representing the definition of an anonymous function having the
        // specified input and output signature. The last operands are the output expressions; if
        // there are more operands before that, they are compile-time constant inputs which are
        // implicitly appended to the caller's inputs on every call.
        Function(Signature, Box<[Id]>),

        // An RVSDG "apply" node representing a function call. The first operand is the function to
        // call and any remaining operands are inputs to the called function. The result is always
        // a tuple.
        "call" = Call(Box<[Id]>),

        // A node representing the arguments of the nearest enclosing structured control block,
        // such as "loop" or "case". The operational semantics depend on which block transitively
        // demanded the value of this node at the current point of evaluation.
        Arg(Get),

        // A node which extracts the Nth output from a node which outputs a tuple.
        Get(Get, Id),

        Const(i32),
    }
}

impl Op {
    pub fn same_scope_children(&self) -> &[Id] {
        match self {
            Op::Loop(args) => {
                assert!(args.len() % 2 == 1);
                let inputs = args.len() / 2;
                &args[..inputs]
            }

            Op::Switch(spec, args) => spec.split_scope(args).0,
            Op::Function(sig, args) => sig.split_scope(args).0,
            _ => self.children(),
        }
    }

    pub fn same_scope_children_mut(&mut self) -> &mut [Id] {
        match self {
            Op::Loop(args) => {
                assert!(args.len() % 2 == 1);
                let inputs = args.len() / 2;
                &mut args[..inputs]
            }

            Op::Switch(spec, args) => spec.split_scope_mut(args).0,
            Op::Function(sig, args) => sig.split_scope_mut(args).0,
            _ => self.children_mut(),
        }
    }
}
