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
    NormalizeSafety {
        #[arg(long)]
        output: PathBuf,
        input: PathBuf,
    },
    Replace {
        #[arg(long)]
        request: PathBuf,
        #[arg(long)]
        output: PathBuf,
        current_project: PathBuf,
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
        Command::NormalizeSafety { output, input } => {
            let source = std::fs::read_to_string(input).unwrap();
            let normalized = tools::normalize_target_safety(&source).unwrap_or_else(|error| {
                eprintln!("{:?}: {}", error.kind, error.message);
                std::process::exit(1);
            });
            std::fs::write(output, normalized).unwrap();
        }
        Command::Replace {
            request,
            output,
            current_project,
        } => {
            let request = std::fs::read_to_string(request)
                .map_err(|error| error.to_string())
                .and_then(|request| {
                    tools::replacement_request_from_json(&request)
                        .map_err(|error| format!("{:?}: {}", error.kind, error.message))
                })
                .unwrap_or_else(|error| {
                    eprintln!("{error}");
                    std::process::exit(1);
                });
            let lib_path = utils::find_lib_path(&current_project).unwrap_or_else(|error| {
                eprintln!("{error}");
                std::process::exit(1);
            });
            let source_path = current_project.join(lib_path);
            let source = std::fs::read_to_string(&source_path).unwrap();
            let compiler_source = source.clone();
            let replaced = run_compiler_on_path(&source_path, move |tcx| {
                tools::replace_items(&compiler_source, &request, tcx)
            })
            .unwrap()
            .unwrap_or_else(|error| {
                eprintln!("{:?}: {}", error.kind, error.message);
                std::process::exit(1);
            });
            std::fs::write(output, replaced).unwrap();
        }
    }
}
