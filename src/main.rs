#![warn(nonstandard_style)]

use std::io::Read;

use optir::bind::{bind_common_subexprs, resolve_bindings};
use optir::extract;
use optir::rewrite;

fn main() -> std::io::Result<()> {
    let mut input = String::new();
    std::io::stdin().read_to_string(&mut input)?;
    let input = input.parse().unwrap();
    let input = resolve_bindings(&input);

    let mut runner = egg::Runner::default()
        .with_expr(&input)
        .with_hook(rewrite::variadic_rules);

    runner = runner.run(&rewrite::rules());
    runner.print_report();
    println!("{:?}", runner.egraph.dump());

    let mut extractor = egg::LpExtractor::new(&runner.egraph, extract::OpCost);
    let (expr, _roots) = extractor.solve_multiple(&runner.roots);
    println!("{}", bind_common_subexprs(&expr).pretty(80));

    Ok(())
}
