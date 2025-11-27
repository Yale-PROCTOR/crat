#![feature(rustc_private)]

use std::path::PathBuf;

use clap::{Parser, ValueEnum};
use utils::compilation::run_compiler_on_path;

#[derive(Parser)]
#[command(version)]
struct Args {
    #[arg(long, help = "Show spans for unsafe operations")]
    unsafe_show_spans: bool,

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
    let lib_path = utils::find_lib_path(&args.input).unwrap_or_else(|e| {
        eprintln!("{e}");
        std::process::exit(1);
    });
    let file = args.input.join(&lib_path);
    match args.finder {
        Finder::Example => {
            run_compiler_on_path(&file, finders::example::run).unwrap();
        }
        Finder::Macro => {
            run_compiler_on_path(&file, finders::macro_finder::find_macros).unwrap();
        }
        Finder::Mapper => {
            run_compiler_on_path(&file, |tcx| {
                finders::mapper::run(&args.input, &lib_path, true, tcx)
            })
            .unwrap();
        }
        Finder::Mir => {
            run_compiler_on_path(&file, finders::mir::run).unwrap();
        }
        Finder::Unsafe => {
            run_compiler_on_path(&file, |tcx| {
                finders::unsafe_finder::find_unsafe(args.unsafe_show_spans, tcx)
            })
            .unwrap();
        }
    }
}
