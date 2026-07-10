#![feature(rustc_private)]

use std::path::PathBuf;

use clap::Parser;
use utils::compilation::run_compiler_on_str;

#[derive(Parser)]
#[command(version)]
struct Args {
    #[arg(help = "Path to the input .rs file")]
    input: PathBuf,

    #[arg(help = "Kind of the symbol to find")]
    kind: String,

    #[arg(help = "Name of the symbol to find")]
    name: String,
}

fn main() {
    let args = Args::parse();
    run_compiler_on_str("", |tcx| {
        finders::symbol_finder::run(&args.input, &args.kind, &args.name, tcx)
    })
    .unwrap();
}
