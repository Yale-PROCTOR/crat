#![feature(rustc_private)]

use std::path::PathBuf;

use clap::{Parser, Subcommand};
use utils::compilation::run_compiler_on_path;

#[derive(Parser)]
#[command(version)]
struct Args {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    MakeSkeleton {
        #[arg(long)]
        output: PathBuf,
        input: PathBuf,
    },
    Validate {
        #[arg(long)]
        input: PathBuf,
        #[arg(long)]
        output: PathBuf,
    },
}

fn main() {
    match Args::parse().command {
        Command::MakeSkeleton { output, input } => {
            let lib_path = utils::find_lib_path(&input).unwrap_or_else(|error| {
                eprintln!("{error}");
                std::process::exit(1);
            });
            let source_path = input.join(lib_path);
            let source = std::fs::read_to_string(&source_path).unwrap();
            let records =
                run_compiler_on_path(&source_path, move |tcx| tools::make_skeletons(&source, tcx))
                    .unwrap()
                    .unwrap_or_else(|error| {
                        eprintln!("{}: {}", error.function_path, error.message);
                        std::process::exit(1);
                    });
            let json = tools::skeletons_to_json(&records).unwrap();
            std::fs::write(output, json).unwrap();
        }
        Command::Validate { input, output } => {
            let request = std::fs::read_to_string(input).unwrap();
            let response = tools::validate_json(&request);
            std::fs::write(output, response).unwrap();
        }
    }
}
