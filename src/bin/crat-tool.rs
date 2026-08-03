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
        #[arg(long)]
        observation_source_output: PathBuf,
        #[arg(long)]
        observation_metadata_output: PathBuf,
        current_project: PathBuf,
    },
    ExtractObservations {
        #[arg(long)]
        metadata: PathBuf,
        #[arg(long)]
        output: PathBuf,
        observation_source: PathBuf,
    },
}

#[derive(Serialize)]
struct StatementPairsSidecar<'a> {
    schema_version: u64,
    statements: &'a [tools::ReplacementStatementPair],
}

fn serialize_replacement_outputs(
    output: &tools::ReplacementOutput,
) -> Result<(String, String), serde_json::Error> {
    let sidecar = serde_json::to_string_pretty(&StatementPairsSidecar {
        schema_version: 1,
        statements: &output.statement_pairs,
    })?;
    Ok((output.source.clone(), sidecar))
}

fn validate_replace_output_paths(paths: &[&Path]) -> Result<(), String> {
    for (index, path) in paths.iter().enumerate() {
        if paths[..index].contains(path) {
            return Err("output paths must be pairwise distinct".to_owned());
        }
    }
    Ok(())
}

fn fail(code: &str, message: impl std::fmt::Display) -> ! {
    eprintln!("crat-tool: {code}: {message}");
    std::process::exit(1)
}

fn temporary_path(path: &Path) -> PathBuf {
    let mut value = path.as_os_str().to_owned();
    value.push(".tmp");
    PathBuf::from(value)
}

fn clear_regular_or_symlink(path: &Path) -> Result<(), String> {
    match std::fs::symlink_metadata(path) {
        Ok(metadata) if metadata.file_type().is_symlink() || metadata.is_file() => {
            std::fs::remove_file(path)
                .map_err(|error| format!("failed to remove {}: {error}", path.display()))
        }
        Ok(_) => Err(format!(
            "output destination is not a regular file or symlink: {}",
            path.display()
        )),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(format!("failed to inspect {}: {error}", path.display())),
    }
}

fn validate_clearable(path: &Path) -> Result<(), String> {
    match std::fs::symlink_metadata(path) {
        Ok(metadata) if metadata.file_type().is_symlink() || metadata.is_file() => Ok(()),
        Ok(_) => Err(format!(
            "output destination is not a regular file or symlink: {}",
            path.display()
        )),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(format!("failed to inspect {}: {error}", path.display())),
    }
}

fn prepare_publish_destinations(paths: &[&Path]) -> Result<(), String> {
    let owned = paths
        .iter()
        .flat_map(|path| [(*path).to_path_buf(), temporary_path(path)])
        .collect::<Vec<_>>();
    for path in &owned {
        validate_clearable(path)?;
    }
    for path in &owned {
        clear_regular_or_symlink(path)?;
    }
    Ok(())
}

fn publish_files(files: &[(&Path, &[u8])]) -> Result<(), String> {
    let temporaries = files
        .iter()
        .map(|(path, _)| temporary_path(path))
        .collect::<Vec<_>>();
    let result = (|| {
        for ((path, bytes), temporary) in files.iter().zip(&temporaries) {
            clear_regular_or_symlink(path)?;
            clear_regular_or_symlink(temporary)?;
            std::fs::write(temporary, bytes)
                .map_err(|_| format!("failed to write {}", temporary.display()))?;
        }
        for ((path, _), temporary) in files.iter().zip(&temporaries) {
            std::fs::rename(temporary, path).map_err(|_| {
                format!(
                    "failed to rename {} to {}",
                    temporary.display(),
                    path.display()
                )
            })?;
        }
        Ok(())
    })();
    if let Err(primary) = result {
        let mut cleanup = vec![];
        for path in files
            .iter()
            .map(|(path, _)| *path)
            .chain(temporaries.iter().map(PathBuf::as_path))
        {
            if let Err(error) = clear_regular_or_symlink(path) {
                cleanup.push(error);
            }
        }
        return Err(if cleanup.is_empty() {
            primary
        } else {
            format!("{primary}; cleanup failed: {}", cleanup.join("; "))
        });
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
            observation_source_output,
            observation_metadata_output,
            current_project,
        } => {
            validate_replace_output_paths(&[
                &output,
                &statement_pairs_output,
                &observation_source_output,
                &observation_metadata_output,
            ])
            .unwrap_or_else(|error| fail("output_path_collision", error));
            prepare_publish_destinations(&[
                &output,
                &statement_pairs_output,
                &observation_source_output,
                &observation_metadata_output,
            ])
            .unwrap_or_else(|error| fail("output_io", error));
            let request_text =
                std::fs::read_to_string(request).unwrap_or_else(|error| fail("request_io", error));
            if let Ok(value) = serde_json::from_str::<serde_json::Value>(&request_text)
                && value.get("schema_version") != Some(&serde_json::Value::from(1))
            {
                let observed = value
                    .get("schema_version")
                    .map_or_else(|| "missing".to_owned(), serde_json::Value::to_string);
                fail(
                    "unsupported_schema_version",
                    format!("unsupported schema_version {observed}"),
                );
            }
            let request = tools::replacement_request_from_json(&request_text)
                .unwrap_or_else(|error| fail("invalid_request", error.message));
            let lib_path = utils::find_lib_path(&current_project).unwrap_or_else(|error| {
                eprintln!("{error}");
                std::process::exit(1);
            });
            let source_path = current_project.join(lib_path);
            let source = std::fs::read_to_string(&source_path).unwrap();
            let compiler_source = source.clone();
            let replaced = run_compiler_on_path(&source_path, move |tcx| {
                tools::replace_items_with_observations(&compiler_source, &request, tcx)
            })
            .unwrap_or_else(|_| fail("compiler_failure", "current project failed to compile"))
            .unwrap_or_else(|error| {
                fail(
                    match error.kind {
                        tools::ReplacementErrorKind::InvalidRequest => "invalid_request",
                        tools::ReplacementErrorKind::InvalidTransformation => {
                            "invalid_transformation"
                        }
                        tools::ReplacementErrorKind::TargetResolution => "target_resolution",
                        tools::ReplacementErrorKind::UnsupportedConversion => {
                            "unsupported_conversion"
                        }
                        tools::ReplacementErrorKind::UnsupportedCallRewrite => {
                            "unsupported_call_rewrite"
                        }
                        tools::ReplacementErrorKind::RewriteFailure => "rewrite_failure",
                    },
                    error.message,
                );
            });
            let (source, sidecar) = serialize_replacement_outputs(&replaced.replacement).unwrap();
            let observation_source = replaced.observation_source.clone();
            let metadata = tools::ReplacementObservationMetadata::from_output(
                &replaced,
                source.as_bytes(),
                sidecar.as_bytes(),
                observation_source.as_bytes(),
            );
            let metadata = serde_json::to_string_pretty(&metadata).unwrap();
            publish_files(&[
                (&output, source.as_bytes()),
                (&statement_pairs_output, sidecar.as_bytes()),
                (&observation_source_output, observation_source.as_bytes()),
                (&observation_metadata_output, metadata.as_bytes()),
            ])
            .unwrap_or_else(|error| fail("output_io", error));
        }
        Command::ExtractObservations {
            metadata,
            output,
            observation_source,
        } => {
            validate_replace_output_paths(&[&metadata, &output, &observation_source])
                .unwrap_or_else(|error| fail("output_path_collision", error));
            prepare_publish_destinations(&[&output])
                .unwrap_or_else(|error| fail("output_io", error));
            let metadata_text = std::fs::read_to_string(&metadata).unwrap_or_else(|_| {
                fail(
                    "metadata_io",
                    format!("failed to read {}", metadata.display()),
                )
            });
            let metadata_value = tools::replacement_metadata_from_json(&metadata_text)
                .unwrap_or_else(|error| fail(error.code, error.message));
            let source = std::fs::read(&observation_source).unwrap_or_else(|_| {
                fail(
                    "observation_source_io",
                    format!("failed to read {}", observation_source.display()),
                )
            });
            if tools::sha256_hex(&source) != metadata_value.observation_source_sha256 {
                fail(
                    "observation_source_digest_mismatch",
                    "observation source SHA-256 does not match metadata",
                );
            }
            let document =
                tools::extract_observations_from_path(&observation_source, &metadata_value)
                    .unwrap_or_else(|error| fail(error.code, error.message));
            let json = serde_json::to_string_pretty(&document).unwrap();
            publish_files(&[(&output, json.as_bytes())])
                .unwrap_or_else(|error| fail("output_io", error));
        }
    }
}
