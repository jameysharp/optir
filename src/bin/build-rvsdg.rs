#![warn(nonstandard_style)]

use std::io::BufRead;

use optir::bind::bind_common_subexprs;
use optir::cfg::build_rvsdg::build_rvsdg;
use optir::cfg::from_structured::build_function_region;
use optir::cfg::parse_instructions;
use optir::cfg::restructure::restructure_cfg;

fn main() -> std::io::Result<()> {
    let lines = std::io::stdin()
        .lock()
        .lines()
        .collect::<std::io::Result<Vec<String>>>()?;

    let (mut cfg, mut names) = match parse_instructions(lines) {
        Ok(cfg) => cfg,
        Err(oops) => {
            println!("{:?}", oops);
            return Ok(());
        }
    };

    restructure_cfg(&mut cfg, &mut names);
    //println!("{}", petgraph::dot::Dot::new(&cfg));

    let (region, outputs) = build_function_region(&cfg, &mut names);
    let input = build_rvsdg(&names, &region, &outputs);

    println!("{}", bind_common_subexprs(&input).pretty(80));

    Ok(())
}
