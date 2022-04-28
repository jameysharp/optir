#![warn(nonstandard_style)]

use std::io::Read;

mod analysis;
mod extract;
mod language;
mod rewrite;

fn main() -> std::io::Result<()> {
    let mut input = String::new();
    std::io::stdin().read_to_string(&mut input)?;
    let input = input.parse().unwrap();

    let mut runner = egg::Runner::default()
        .with_expr(&input)
        .with_hook(rewrite::variadic_rules);

    runner = runner.run(&rewrite::rules());
    runner.print_report();
    println!("{:?}", runner.egraph.dump());

    let extractor = egg::Extractor::new(&runner.egraph, extract::OpCost);

    for &root in runner.roots.iter() {
        let (cost, expr) = extractor.find_best(root);
        println!("cost {}: {}", cost, expr);
    }

    Ok(())
}
