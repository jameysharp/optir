#![warn(nonstandard_style)]

use egg::{
    define_language, rewrite, Analysis, ENodeOrVar, Id, Language, PatternAst, Subst, Symbol,
};
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
    ]
}

fn main() -> std::io::Result<()> {
    let mut input = String::new();
    std::io::stdin().read_to_string(&mut input)?;
    let input = input.parse().unwrap();

    let mut runner = egg::Runner::default()
        .with_explanations_enabled()
        .with_expr(&input)
        .run(&rules());
    runner.print_report();
    println!("{:?}", runner.egraph.dump());

    for root in runner.roots.clone() {
        let extractor = egg::Extractor::new(&runner.egraph, egg::AstSize);
        let (best_cost, best_expr) = extractor.find_best(root);
        println!();
        println!("{}: {}", best_cost, best_expr);
        println!(
            "{}",
            runner
                .explain_equivalence(&input, &best_expr)
                .get_flat_string()
        );
    }
    Ok(())
}
