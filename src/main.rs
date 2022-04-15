#![warn(nonstandard_style)]

use egg::{
    define_language, rewrite, Analysis, ENodeOrVar, Id, Language, PatternAst, Subst, Symbol,
};
use std::collections::HashSet;
use std::io::Read;

pub type Rewrite = egg::Rewrite<Op, ConstantFold>;
pub type EGraph = egg::EGraph<Op, ConstantFold>;

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
        "global-bind" = Binds(Box<[Id]>),
        "label" = Label(Box<[Id]>),
        "branch-if" = BranchIf([Id; 3]),
        "branch" = Branch(Box<[Id]>),
        "return" = Return(Box<[Id]>),
        Const(i32),
        Arg(Symbol),
    }
}

#[derive(Default)]
pub struct ConstantFold;

impl Analysis<Op> for ConstantFold {
    type Data = Option<(i32, PatternAst<Op>)>;

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> egg::DidMerge {
        egg::merge_max(to, from)
    }

    fn make(egraph: &EGraph, enode: &Op) -> Self::Data {
        let c = |i: &Id| egraph[*i].data.as_ref().map(|c| c.0);
        let result = match enode {
            Op::Add([l, r]) => c(l)? + c(r)?,
            Op::Mul([l, r]) => c(l)? * c(r)?,
            Op::Div([l, r]) => c(l)? / c(r)?,
            Op::Mod([l, r]) => c(l)? % c(r)?,
            Op::ShiftLeft([l, r]) => c(l)? << c(r)?,
            Op::ShiftRightZero([l, r]) => ((c(l)? as u32) >> c(r)?) as i32,
            Op::ShiftRightSign([l, r]) => c(l)? >> c(r)?,
            Op::BitAnd([l, r]) => c(l)? & c(r)?,
            Op::Binds(_) => return None,
            Op::Label(_) => return None,
            Op::BranchIf(_) => return None,
            Op::Branch(_) => return None,
            Op::Return(_) => return None,
            Op::Const(c) => *c,
            Op::Arg(_) => return None,
        };

        let mut ast = PatternAst::default();
        let mut enode = enode.clone();
        for child in enode.children_mut() {
            *child = ast.add(ENodeOrVar::ENode(Op::Const(c(child)?)));
        }
        ast.add(ENodeOrVar::ENode(enode));
        Some((result, ast))
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        if let Some(c) = egraph[id].data.clone() {
            egraph.union_instantiations(
                &c.1,
                &vec![ENodeOrVar::ENode(Op::Const(c.0))].into(),
                &Default::default(),
                "const-fold".to_string(),
            );

            // If this operation is equivalent to a constant, it doesn't matter what else it
            // might also be equivalent to.
            egraph[id].nodes.retain(|n| n.is_leaf());
        }
    }
}

fn is_power_of_two(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        if let Some((c, _)) = egraph[subst[var]].data {
            c & (c - 1) == 0
        } else {
            false
        }
    }
}

pub fn rules() -> Vec<Rewrite> {
    vec![
        rewrite!("comm-add"; "(+ ?x ?y)" => "(+ ?y ?x)"),
        rewrite!("comm-mul"; "(* ?x ?y)" => "(* ?y ?x)"),
        rewrite!("comm-and"; "(& ?x ?y)" => "(& ?y ?x)"),
        rewrite!("zero-add"; "(+ ?x 0)" => "?x"),
        rewrite!("zero-mul"; "(* ?x 0)" => "0"),
        rewrite!("one-mul"; "(* ?x 1)" => "?x"),
        rewrite!("one-div"; "(/ ?x 1)" => "?x"),
        rewrite!("zero-shift-left"; "(<< ?x 0)" => "?x"),
        rewrite!("zero-shift-right-zero"; "(>> ?x 0)" => "?x"),
        rewrite!("zero-shift-right-sign"; "(>>s ?x 0)" => "?x"),
        rewrite!("zero-and"; "(& ?x 0)" => "0"),
        rewrite!("one-and"; "(& ?x -1)" => "?x"),
        rewrite!("factor"; "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),
        // a+a+a becomes a*3 through repeated application of these rules and const folding.
        rewrite!("factor-one"; "(+ ?a (* ?a ?c))" => "(* ?a (+ 1 ?c))"),
        rewrite!("double"; "(+ ?a ?a)" => "(* ?a 2)"),
        //rewrite!("mul-shift"; "(* ?a ?c)" => "(<< ?a ?c.trailing_zeros())" if is_power_of_two("?c")),
        rewrite!("div-div"; "(/ (/ ?a ?b) ?c)" => "(/ ?a (* ?b ?c))"),
        rewrite!("mask"; "(% ?a ?c)" => "(& ?a (+ ?c -1))" if is_power_of_two("?c")),
        rewrite!("shift-mul"; "(<< ?a ?n)" => "(* ?a (<< 1 ?n))"),
        rewrite!("shift-shift-left"; "(<< (<< ?a ?b) ?c)" => "(<< ?a (+ ?b ?c))"),
        rewrite!("shift-left-back"; "(<< (>> ?a ?b) ?b)" => "(& ?a (<< -1 ?b))"),
        rewrite!("branch-if-true"; "(branch-if -1 ?t ?f)" => "?t"),
        rewrite!("branch-if-false"; "(branch-if 0 ?t ?f)" => "?f"),
    ]
}

#[derive(Clone)]
pub enum Branch<'a> {
    Branch(Id, &'a [Id]),
    Return(&'a [Id]),
}

impl<'a> Branch<'a> {
    pub fn from_eclass(g: &'a EGraph, branch: Id) -> Option<Branch<'a>> {
        for n in g[branch].iter() {
            match n {
                Op::Return(args) => {
                    return Some(Branch::Return(args));
                }
                Op::Branch(args) => {
                    let (target, args) = args.split_first().unwrap();
                    return Some(Branch::Branch(*target, args));
                }
                _ => {}
            }
        }
        None
    }

    pub fn dump(&'a self, mut extract: impl FnMut(Id) -> egg::RecExpr<Op>) {
        let args = match self {
            Branch::Branch(target, args) => {
                print!("  goto block {}", target);
                args
            }
            Branch::Return(args) => {
                print!("  return");
                args
            }
        };
        for arg in args.iter() {
            print!(" {}", extract(*arg));
        }
        println!();
    }
}

#[derive(Clone)]
pub struct Block<'a> {
    conditional: Vec<(Id, Branch<'a>)>,
    unconditional: Branch<'a>,
}

impl<'a> Block<'a> {
    pub fn from_eclass(g: &'a EGraph, mut branch: Id) -> Block<'a> {
        let mut conditional = Vec::new();
        'walk_branches: loop {
            if let Some(unconditional) = Branch::from_eclass(g, branch) {
                return Block {
                    conditional,
                    unconditional,
                };
            }
            for n in g[branch].iter() {
                match n {
                    Op::BranchIf([c, t, f]) => {
                        conditional.push((*c, Branch::from_eclass(g, *t).unwrap()));
                        branch = *f;
                        continue 'walk_branches;
                    }
                    _ => {}
                }
            }
            panic!("eclass {} is not a branch", branch);
        }
    }
}

pub fn extract_blocks<'a>(g: &'a EGraph, label: Id) -> Vec<(Id, &'a [Id], Block<'a>)> {
    fn go<'a>(
        g: &'a EGraph,
        seen: &mut HashSet<Id>,
        blocks: &mut Vec<(Id, &'a [Id], Block<'a>)>,
        label: Id,
    ) {
        if !seen.insert(label) {
            return;
        }
        let (branch, args) = g[label]
            .iter()
            .find_map(|n| {
                if let Op::Label(args) = n {
                    Some(args)
                } else {
                    None
                }
            })
            .unwrap()
            .split_last()
            .unwrap();
        let block = Block::from_eclass(g, *branch);

        for (_cond, branch) in block.conditional.iter() {
            if let Branch::Branch(target, _args) = branch {
                go(g, seen, blocks, *target);
            }
        }
        if let Branch::Branch(target, _args) = &block.unconditional {
            go(g, seen, blocks, *target);
        }

        blocks.push((label, args, block));
    }

    let mut seen = HashSet::new();
    let mut blocks = Vec::new();
    go(g, &mut seen, &mut blocks, label);
    blocks.reverse();
    blocks
}

fn main() -> std::io::Result<()> {
    let mut input = String::new();
    std::io::stdin().read_to_string(&mut input)?;
    let input = input.parse().unwrap();

    let mut runner = egg::Runner::default().with_expr(&input);

    let mut bindings = Vec::new();
    for class in runner.egraph.classes() {
        for node in class.iter() {
            if let Op::Binds(binds) = node {
                let mut iter = binds.iter().copied();
                while let Some(lhs) = iter.next() {
                    bindings.push((lhs, iter.next().unwrap_or(class.id)));
                }
            }
        }
    }
    for (lhs, rhs) in bindings {
        runner.egraph[lhs]
            .nodes
            .retain(|op| !matches!(op, Op::Arg(_)));
        runner.egraph.union(lhs, rhs);
    }
    runner.egraph.rebuild();

    runner = runner.run(&rules());
    runner.print_report();
    println!("{:?}", runner.egraph.dump());

    let extractor = egg::Extractor::new(&runner.egraph, egg::AstSize);

    for &root in runner.roots.iter() {
        let blocks = extract_blocks(&runner.egraph, root);

        for (source, args, block) in blocks {
            println!();
            print!("block {}", source);
            for arg in args {
                print!(" {}", extractor.find_best(*arg).1);
            }
            println!(":");

            for (cond, branch) in block.conditional.iter() {
                println!("if {} then:", extractor.find_best(*cond).1);
                branch.dump(|id| extractor.find_best(id).1);
            }
            println!("otherwise:");
            block.unconditional.dump(|id| extractor.find_best(id).1);
        }
    }
    Ok(())
}
