#![feature(rustc_private)]

use std::path::PathBuf;

use clap::{Parser, ValueEnum};
use crat::*;
use utils::compilation::run_compiler_on_path;

#[derive(Parser)]
#[command(version)]
struct Args {
    #[arg(help = "Finder to run")]
    finder: Finder,

    #[arg(help = "Path to the input directory containing Cargo.toml")]
    input: PathBuf,
}

#[derive(Clone, Debug, ValueEnum)]
#[clap(rename_all = "lower")]
enum Finder {
    Example,
    Macro,
    Mapper,
    Mir,
    Unsafe,
}

fn main() {
    let args = Args::parse();
    let lib_path = crat::find_lib_path(&args.input).unwrap_or_else(|e| {
        eprintln!("{e}");
        std::process::exit(1);
    });
    let file = args.input.join(&lib_path);
    match args.finder {
        Finder::Example => {
            run_compiler_on_path(&file, finder::example::run).unwrap();
        }
        Finder::Macro => {
            run_compiler_on_path(&file, finder::macro_finder::find_macros).unwrap();
        }
        Finder::Mapper => {
            run_compiler_on_path(&file, |tcx| {
                finder::mapper::run(&args.input, &lib_path, true, tcx)
            })
            .unwrap();
        }
        Finder::Mir => {
            run_compiler_on_path(&file, finder::mir::run).unwrap();
        }
        Finder::Unsafe => {
            run_compiler_on_path(&file, finder::unsafe_finder::find_unsafe).unwrap();
        }
    }
}
