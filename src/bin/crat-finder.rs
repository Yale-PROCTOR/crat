#![feature(rustc_private)]

use std::path::PathBuf;

use clap::{Parser, ValueEnum};
use compile_util::run_compiler_on_path;
use crat::*;

#[derive(Parser)]
#[command(version)]
struct Args {
    #[arg(help = "Finder to run")]
    finder: Finder,

    #[arg(help = "Path to the input directory containing c2rust-lib.rs")]
    input: PathBuf,
}

#[derive(Clone, Debug, ValueEnum)]
#[clap(rename_all = "lower")]
enum Finder {
    Example,
    Macro,
    Mapper,
    Unsafe,
}

fn main() {
    let args = Args::parse();
    let file = args.input.join("c2rust-lib.rs");
    match args.finder {
        Finder::Example => {
            run_compiler_on_path(&file, finder::example::run).unwrap();
        }
        Finder::Macro => {
            run_compiler_on_path(&file, finder::macro_finder::find_macros).unwrap();
        }
        Finder::Mapper => {
            run_compiler_on_path(&file, |tcx| finder::mapper::run(&args.input, tcx)).unwrap();
        }
        Finder::Unsafe => {
            run_compiler_on_path(&file, finder::unsafe_finder::find_unsafe).unwrap();
        }
    }
}
