use egg::{Id, FromOp, Language, RecExpr, Var};
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Binding<L> {
    Bind(Var, [Id; 2]),
    Use(Var),
    ENode(L),
}

impl<L: Language> Language for Binding<L> {
    fn matches(&self, _other: &Self) -> bool {
        panic!("Should never call this")
    }

    fn children(&self) -> &[Id] {
        match self {
            Binding::Bind(_, binding) => binding,
            Binding::Use(_) => &[],
            Binding::ENode(n) => n.children(),
        }
    }

    fn children_mut(&mut self) -> &mut [Id] {
        match self {
            Binding::Bind(_, binding) => binding,
            Binding::Use(_) => &mut [],
            Binding::ENode(n) => n.children_mut(),
        }
    }
}

impl<L: FromOp> FromOp for Binding<L> {
    type Error = L::Error;

    fn from_op(op: &str, children: Vec<Id>) -> Result<Self, Self::Error> {
        if let Ok(var) = op.parse() {
            match &children[..] {
                &[] => return Ok(Self::Use(var)),
                &[val, expr] => return Ok(Self::Bind(var, [val, expr])),
                _ => {}
            }
        }
        L::from_op(op, children).map(Self::ENode)
    }
}

pub fn resolve_bindings<L: Language + Clone>(input: &RecExpr<Binding<L>>) -> RecExpr<L> {
    fn go<L: Language + Clone>(result: &mut Vec<L>, input: &[Binding<L>], id: Id, mut symbol_table: Rc<HashMap<Var, Id>>) -> Id {
        match &input[usize::from(id)] {
            Binding::Use(var) => symbol_table[var],

            &Binding::Bind(var, [val, expr]) => {
                let val = go(result, input, val, symbol_table.clone());
                Rc::make_mut(&mut symbol_table).insert(var, val);
                go(result, input, expr, symbol_table)
            }

            Binding::ENode(op) => {
                let mut op = op.clone();
                for child in op.children_mut() {
                    *child = go(result, input, *child, symbol_table.clone());
                }
                let new_id = result.len().try_into().unwrap();
                result.push(op);
                new_id
            }
        }
    }

    let input = input.as_ref();
    let input_len = input.len();
    let mut result = Vec::with_capacity(input_len);
    go(&mut result, input, (input_len - 1).try_into().unwrap(), Rc::new(HashMap::new()));
    RecExpr::from(result)
}
