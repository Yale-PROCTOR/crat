#![feature(rustc_private)]

use std::path::{Path, PathBuf};

use clap::{Parser, Subcommand};
use serde::Serialize;
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
        #[arg(long)]
        statement_pairs_output: PathBuf,
        current_project: PathBuf,
    },
}

#[derive(Serialize)]
struct StatementPairsSidecar<'a> {
    schema_version: u64,
    statements: &'a [tools::ReplacementStatementPair],
}

fn serialize_replacement_outputs(
    output: tools::ReplacementOutput,
) -> Result<(String, String), serde_json::Error> {
    let sidecar = serde_json::to_string_pretty(&StatementPairsSidecar {
        schema_version: 1,
        statements: &output.statement_pairs,
    })?;
    Ok((output.source, sidecar))
}

fn validate_replace_output_paths(
    output: &Path,
    statement_pairs_output: &Path,
) -> Result<(), String> {
    if output == statement_pairs_output {
        return Err(
            "`--output` and `--statement-pairs-output` must name distinct paths".to_owned(),
        );
    }
    Ok(())
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
            statement_pairs_output,
            current_project,
        } => {
            validate_replace_output_paths(&output, &statement_pairs_output).unwrap_or_else(
                |error| {
                    eprintln!("{error}");
                    std::process::exit(1);
                },
            );
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
            let (source, sidecar) = serialize_replacement_outputs(replaced).unwrap();
            std::fs::write(output, source).unwrap();
            std::fs::write(statement_pairs_output, sidecar).unwrap();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn replace_cli_helper_serializes_both_outputs_exactly() {
        let output = tools::ReplacementOutput {
            source: "pub unsafe fn f() {}\n".to_owned(),
            statement_pairs: vec![
                tools::ReplacementStatementPair {
                    item_id: 2,
                    path: "z::f".to_owned(),
                    label: 0,
                    after_statement: "#[proctor(0)]\nreturn \"quoted\";".to_owned(),
                },
                tools::ReplacementStatementPair {
                    item_id: 7,
                    path: "a::g".to_owned(),
                    label: 3,
                    after_statement: "#[proctor(3)]\ng();".to_owned(),
                },
            ],
        };
        let (source, sidecar) = serialize_replacement_outputs(output).unwrap();
        assert_eq!(source.as_bytes(), b"pub unsafe fn f() {}\n");
        assert_eq!(
            sidecar,
            r##"{
  "schema_version": 1,
  "statements": [
    {
      "item_id": 2,
      "path": "z::f",
      "label": 0,
      "after_statement": "#[proctor(0)]\nreturn \"quoted\";"
    },
    {
      "item_id": 7,
      "path": "a::g",
      "label": 3,
      "after_statement": "#[proctor(3)]\ng();"
    }
  ]
}"##
        );
        assert!(!sidecar.ends_with('\n'));

        let (_, empty) = serialize_replacement_outputs(tools::ReplacementOutput {
            source: String::new(),
            statement_pairs: vec![],
        })
        .unwrap();
        assert_eq!(
            empty,
            "{\n  \"schema_version\": 1,\n  \"statements\": []\n}"
        );

        assert!(
            Args::try_parse_from([
                "crat-tool",
                "replace",
                "--request",
                "request.json",
                "--output",
                "candidate.rs",
                "project",
            ])
            .is_err()
        );
        let args = Args::try_parse_from([
            "crat-tool",
            "replace",
            "--request",
            "request.json",
            "--output",
            "candidate.rs",
            "--statement-pairs-output",
            "pairs.json",
            "project",
        ])
        .unwrap();
        let Command::Replace {
            output,
            statement_pairs_output,
            ..
        } = args.command
        else {
            panic!("expected replace command")
        };
        assert_eq!(output, PathBuf::from("candidate.rs"));
        assert_eq!(statement_pairs_output, PathBuf::from("pairs.json"));
        assert!(validate_replace_output_paths(&output, &statement_pairs_output).is_ok());
        assert!(validate_replace_output_paths(&output, &output).is_err());
    }
}
