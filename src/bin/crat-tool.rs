#![feature(rustc_private)]

use std::{
    collections::HashSet,
    fs::OpenOptions,
    io::Write,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

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
    MakeInitial {
        #[arg(long)]
        output: PathBuf,
        input: PathBuf,
    },
    MakeSkeleton {
        #[arg(long)]
        output: PathBuf,
        #[arg(long)]
        rules: Option<PathBuf>,
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
    AddFunctions {
        #[arg(long)]
        request: PathBuf,
        #[arg(long)]
        current_project: PathBuf,
        #[arg(long)]
        output: PathBuf,
        #[arg(long)]
        statement_pairs_output: PathBuf,
        #[arg(long)]
        observation_source_output: PathBuf,
        #[arg(long)]
        observation_metadata_output: PathBuf,
        input: PathBuf,
    },
    FinalizeProject {
        #[arg(long)]
        manifest: PathBuf,
        #[arg(long)]
        current_project: PathBuf,
        #[arg(long)]
        output: PathBuf,
        #[arg(long)]
        manifest_output: PathBuf,
        input: PathBuf,
    },
    ExtractObservations {
        #[arg(long)]
        metadata: PathBuf,
        #[arg(long)]
        output: PathBuf,
        observation_source: PathBuf,
    },
    SynthesizeRules {
        #[arg(long)]
        output: PathBuf,
        #[arg(num_args = 1..)]
        observations: Vec<PathBuf>,
    },
    PrettyPrintRules {
        #[arg(long)]
        output: PathBuf,
        rules: PathBuf,
    },
    MergeObservations {
        #[arg(long)]
        output: PathBuf,
        observations: Vec<PathBuf>,
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

fn replacement_failure(error: tools::ReplacementError) -> ! {
    fail(
        match error.kind {
            tools::ReplacementErrorKind::InvalidRequest => "invalid_request",
            tools::ReplacementErrorKind::InvalidTransformation => "invalid_transformation",
            tools::ReplacementErrorKind::TargetResolution => "target_resolution",
            tools::ReplacementErrorKind::UnsupportedConversion => "unsupported_conversion",
            tools::ReplacementErrorKind::UnsupportedCallRewrite => "unsupported_call_rewrite",
            tools::ReplacementErrorKind::RewriteFailure => "rewrite_failure",
        },
        error.message,
    )
}

fn manifest_for_finalization(
    input: &str,
) -> Result<(toml_edit::DocumentMut, String, Vec<String>), String> {
    let document = input
        .parse::<toml_edit::DocumentMut>()
        .map_err(|error| format!("invalid project manifest: {error}"))?;
    let target_kind = document
        .get("target_kind")
        .and_then(toml_edit::Item::as_str)
        .ok_or("project manifest has no string target_kind")?
        .to_owned();
    let api = document
        .get("api_functions")
        .and_then(toml_edit::Item::as_array)
        .ok_or("project manifest has no api_functions array")?
        .iter()
        .map(|item| {
            item.as_str()
                .map(str::to_owned)
                .ok_or("project manifest API entry must be a string")
        })
        .collect::<Result<Vec<_>, _>>()?;
    if document
        .get("target_name")
        .and_then(toml_edit::Item::as_str)
        .is_none()
    {
        return Err("project manifest has no string target_name".to_owned());
    }
    if !document
        .get("wrappers")
        .and_then(toml_edit::Item::as_array)
        .is_some_and(|items| items.is_empty())
    {
        return Err("project manifest must contain an empty wrappers array".to_owned());
    }
    Ok((document, target_kind, api))
}

fn updated_manifest(
    mut document: toml_edit::DocumentMut,
    wrappers: &[tools::FinalWrapper],
) -> String {
    let array = document["wrappers"]
        .as_array_mut()
        .expect("manifest validation checked wrappers");
    for wrapper in wrappers {
        let mut entry = toml_edit::InlineTable::new();
        entry.insert("wrapped", toml_edit::Value::from(wrapper.wrapped.clone()));
        entry.insert("wrapper", toml_edit::Value::from(wrapper.wrapper.clone()));
        array.push(toml_edit::Value::InlineTable(entry));
    }
    document.to_string()
}

fn validate_replace_output_paths(paths: &[&Path]) -> Result<(), String> {
    for (index, path) in paths.iter().enumerate() {
        for other in &paths[..index] {
            if paths_alias(path, other)? {
                return Err("output paths must be pairwise distinct".to_owned());
            }
        }
    }
    Ok(())
}

fn resolved_path(path: &Path) -> Result<PathBuf, String> {
    match std::fs::canonicalize(path) {
        Ok(path) => Ok(path),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            let parent = path.parent().unwrap_or_else(|| Path::new("."));
            let parent = std::fs::canonicalize(parent).map_err(|error| {
                format!("failed to resolve parent of {}: {error}", path.display())
            })?;
            let name = path
                .file_name()
                .ok_or_else(|| format!("path has no file name: {}", path.display()))?;
            Ok(parent.join(name))
        }
        Err(error) => Err(format!("failed to resolve {}: {error}", path.display())),
    }
}

fn paths_alias(left: &Path, right: &Path) -> Result<bool, String> {
    Ok(resolved_path(left)? == resolved_path(right)?)
}

fn validate_output_input_paths(outputs: &[&Path], inputs: &[&Path]) -> Result<(), String> {
    validate_replace_output_paths(outputs)?;
    for output in outputs {
        for input in inputs {
            if paths_alias(output, input)? {
                return Err(format!(
                    "output {} aliases input {}",
                    output.display(),
                    input.display()
                ));
            }
        }
    }
    Ok(())
}

fn path_within_root(path: &Path, root: &Path) -> bool {
    path.starts_with(root)
}

fn validate_outputs_outside_projects(outputs: &[&Path], projects: &[&Path]) -> Result<(), String> {
    let roots = projects
        .iter()
        .map(|project| {
            std::fs::canonicalize(project).map_err(|error| {
                format!("failed to resolve project {}: {error}", project.display())
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    for output in outputs {
        let parent = output.parent().unwrap_or_else(|| Path::new("."));
        let parent = std::fs::canonicalize(parent).map_err(|error| {
            format!(
                "failed to resolve output parent {}: {error}",
                parent.display()
            )
        })?;
        let name = output
            .file_name()
            .ok_or_else(|| format!("output path has no file name: {}", output.display()))?;
        let publication_path = parent.join(name);
        let resolved_target = resolved_path(output)?;
        if roots.iter().any(|root| {
            path_within_root(&publication_path, root) || path_within_root(&resolved_target, root)
        }) {
            return Err(format!(
                "output {} is inside an input project",
                output.display()
            ));
        }
    }
    Ok(())
}

fn validate_observation_inputs(paths: &[PathBuf]) -> Result<(), String> {
    let mut resolved = HashSet::new();
    for path in paths {
        let metadata = std::fs::symlink_metadata(path)
            .map_err(|error| format!("failed to inspect {}: {error}", path.display()))?;
        if metadata.file_type().is_symlink() {
            return Err(format!(
                "observation input must not be a symlink: {}",
                path.display()
            ));
        }
        let canonical = std::fs::canonicalize(path)
            .map_err(|error| format!("failed to resolve {}: {error}", path.display()))?;
        if !resolved.insert(canonical) {
            return Err("observation input path is repeated".to_owned());
        }
    }
    Ok(())
}

fn fail(code: &str, message: impl std::fmt::Display) -> ! {
    let message = message
        .to_string()
        .chars()
        .map(|character| {
            if character.is_control() {
                ' '
            } else {
                character
            }
        })
        .collect::<String>();
    eprintln!("crat-tool: {code}: {message}");
    std::process::exit(1)
}

static PUBLICATION_NONCE: AtomicU64 = AtomicU64::new(0);

fn fresh_publication_path(path: &Path, role: &str) -> PathBuf {
    let mut value = path.as_os_str().to_owned();
    value.push(format!(
        ".{role}.{}.{}",
        std::process::id(),
        PUBLICATION_NONCE.fetch_add(1, Ordering::Relaxed)
    ));
    PathBuf::from(value)
}

fn fresh_unused_publication_path(path: &Path, role: &str) -> Result<PathBuf, String> {
    loop {
        let candidate = fresh_publication_path(path, role);
        match std::fs::symlink_metadata(&candidate) {
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(candidate),
            Ok(_) => continue,
            Err(error) => {
                return Err(format!(
                    "failed to inspect publication path {}: {error}",
                    candidate.display()
                ));
            }
        }
    }
}

fn stage_file(path: &Path, bytes: &[u8]) -> Result<PathBuf, String> {
    loop {
        let temporary = fresh_publication_path(path, "tmp");
        match OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&temporary)
        {
            Ok(mut file) => {
                if let Err(error) = file.write_all(bytes).and_then(|_| file.sync_all()) {
                    let _ = std::fs::remove_file(&temporary);
                    return Err(format!("failed to write {}: {error}", temporary.display()));
                }
                return Ok(temporary);
            }
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => {
                return Err(format!("failed to create {}: {error}", temporary.display()));
            }
        }
    }
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
    for path in paths {
        validate_clearable(path)?;
    }
    Ok(())
}

fn publish_files(files: &[(&Path, &[u8])]) -> Result<(), String> {
    let mut temporaries = vec![];
    for (path, bytes) in files {
        match stage_file(path, bytes) {
            Ok(temporary) => temporaries.push(temporary),
            Err(error) => {
                for temporary in &temporaries {
                    let _ = clear_regular_or_symlink(temporary);
                }
                return Err(error);
            }
        }
    }
    let mut backups = vec![];
    for (path, _) in files {
        match fresh_unused_publication_path(path, "backup") {
            Ok(backup) => backups.push(backup),
            Err(error) => {
                for temporary in &temporaries {
                    let _ = clear_regular_or_symlink(temporary);
                }
                return Err(error);
            }
        }
    }
    let result = (|| {
        for (published, (((path, _), temporary), backup)) in
            files.iter().zip(&temporaries).zip(&backups).enumerate()
        {
            let existed = std::fs::symlink_metadata(path).is_ok();
            if existed {
                std::fs::rename(path, backup).map_err(|error| {
                    format!(
                        "failed to preserve existing {} as {}: {error}",
                        path.display(),
                        backup.display()
                    )
                })?;
            }
            if let Err(error) = std::fs::rename(temporary, path) {
                if existed {
                    let _ = std::fs::rename(backup, path);
                }
                return Err(format!(
                    "failed to rename {} to {}: {error}; published {published} earlier outputs",
                    temporary.display(),
                    path.display()
                ));
            }
        }
        Ok(())
    })();
    if let Err(primary) = result {
        let mut cleanup = vec![];
        for (((path, _), temporary), backup) in files.iter().zip(&temporaries).zip(&backups) {
            if std::fs::symlink_metadata(backup).is_ok() {
                if let Err(error) = clear_regular_or_symlink(path) {
                    cleanup.push(error);
                }
                if let Err(error) = std::fs::rename(backup, path) {
                    cleanup.push(format!(
                        "failed to restore {} from {}: {error}",
                        path.display(),
                        backup.display()
                    ));
                }
            } else if std::fs::symlink_metadata(temporary).is_err()
                && let Err(error) = clear_regular_or_symlink(path)
            {
                cleanup.push(error);
            }
            if let Err(error) = clear_regular_or_symlink(temporary) {
                cleanup.push(error);
            }
        }
        return Err(if cleanup.is_empty() {
            primary
        } else {
            format!("{primary}; cleanup failed: {}", cleanup.join("; "))
        });
    }
    for backup in &backups {
        let _ = clear_regular_or_symlink(backup);
    }
    Ok(())
}

fn main() {
    match Args::parse().command {
        Command::MakeInitial { output, input } => {
            let source_path = input.join(
                utils::find_lib_path(&input).unwrap_or_else(|error| fail("project_layout", error)),
            );
            validate_output_input_paths(&[&output], &[&source_path])
                .unwrap_or_else(|error| fail("output_path_collision", error));
            validate_outputs_outside_projects(&[&output], &[&input])
                .unwrap_or_else(|error| fail("output_path_collision", error));
            let source = std::fs::read_to_string(&source_path)
                .unwrap_or_else(|error| fail("source_io", error));
            let initial = tools::make_initial_source(&source)
                .unwrap_or_else(|error| replacement_failure(error));
            prepare_publish_destinations(&[&output])
                .unwrap_or_else(|error| fail("output_io", error));
            publish_files(&[(&output, initial.as_bytes())])
                .unwrap_or_else(|error| fail("output_io", error));
        }
        Command::MakeSkeleton {
            output,
            rules,
            input,
        } => {
            if let Some(rules) = rules.as_deref() {
                validate_output_input_paths(&[&output], &[rules])
                    .unwrap_or_else(|error| fail("output_path_collision", error));
            }
            let lib_path = utils::find_lib_path(&input).unwrap_or_else(|error| {
                eprintln!("{error}");
                std::process::exit(1);
            });
            let source_path = input.join(lib_path);
            let source = std::fs::read_to_string(&source_path).unwrap();
            let rules = rules.map(|path| {
                let text =
                    std::fs::read_to_string(path).unwrap_or_else(|error| fail("rule_io", error));
                tools::rule_document_from_json(&text)
                    .unwrap_or_else(|error| fail("invalid_rules", error))
            });
            let records = run_compiler_on_path(&source_path, move |tcx| {
                tools::make_skeletons_with_rules(&source, rules.as_ref(), tcx)
            })
            .unwrap()
            .unwrap_or_else(|error| {
                eprintln!("{}: {}", error.function_path, error.message);
                std::process::exit(1);
            });
            let json = tools::skeletons_to_json(&records).unwrap();
            prepare_publish_destinations(&[&output])
                .unwrap_or_else(|error| fail("output_io", error));
            publish_files(&[(&output, json.as_bytes())])
                .unwrap_or_else(|error| fail("output_io", error));
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
        Command::AddFunctions {
            request,
            current_project,
            output,
            statement_pairs_output,
            observation_source_output,
            observation_metadata_output,
            input,
        } => {
            let analysis_path = input.join(
                utils::find_lib_path(&input).unwrap_or_else(|error| fail("project_layout", error)),
            );
            let partial_path = current_project.join(
                utils::find_lib_path(&current_project)
                    .unwrap_or_else(|error| fail("project_layout", error)),
            );
            validate_output_input_paths(
                &[
                    &output,
                    &statement_pairs_output,
                    &observation_source_output,
                    &observation_metadata_output,
                ],
                &[&request, &analysis_path, &partial_path],
            )
            .unwrap_or_else(|error| fail("output_path_collision", error));
            validate_outputs_outside_projects(
                &[
                    &output,
                    &statement_pairs_output,
                    &observation_source_output,
                    &observation_metadata_output,
                ],
                &[&input, &current_project],
            )
            .unwrap_or_else(|error| fail("output_path_collision", error));
            prepare_publish_destinations(&[
                &output,
                &statement_pairs_output,
                &observation_source_output,
                &observation_metadata_output,
            ])
            .unwrap_or_else(|error| fail("output_io", error));
            let request_text =
                std::fs::read_to_string(&request).unwrap_or_else(|error| fail("request_io", error));
            let request = tools::replacement_request_from_json(&request_text)
                .unwrap_or_else(|error| replacement_failure(error));
            let source = std::fs::read_to_string(&analysis_path)
                .unwrap_or_else(|error| fail("source_io", error));
            let partial = std::fs::read_to_string(&partial_path)
                .unwrap_or_else(|error| fail("source_io", error));
            let addition = run_compiler_on_path(&analysis_path, move |tcx| {
                tools::add_functions_with_observations(&source, &partial, &request, tcx)
            })
            .unwrap_or_else(|_| fail("compiler_failure", "analysis project failed to compile"))
            .unwrap_or_else(|error| replacement_failure(error));
            let (candidate, pairs) = serialize_replacement_outputs(&addition.replacement).unwrap();
            let observation = &addition.observation_source;
            let metadata = tools::ReplacementObservationMetadata::from_additive_output(
                &addition,
                candidate.as_bytes(),
                pairs.as_bytes(),
                observation.as_bytes(),
            );
            let metadata = serde_json::to_string_pretty(&metadata).unwrap();
            publish_files(&[
                (&output, candidate.as_bytes()),
                (&statement_pairs_output, pairs.as_bytes()),
                (&observation_source_output, observation.as_bytes()),
                (&observation_metadata_output, metadata.as_bytes()),
            ])
            .unwrap_or_else(|error| fail("output_io", error));
        }
        Command::FinalizeProject {
            manifest,
            current_project,
            output,
            manifest_output,
            input,
        } => {
            let analysis_path = input.join(
                utils::find_lib_path(&input).unwrap_or_else(|error| fail("project_layout", error)),
            );
            let partial_path = current_project.join(
                utils::find_lib_path(&current_project)
                    .unwrap_or_else(|error| fail("project_layout", error)),
            );
            validate_output_input_paths(
                &[&output, &manifest_output],
                &[&manifest, &analysis_path, &partial_path],
            )
            .unwrap_or_else(|error| fail("output_path_collision", error));
            validate_outputs_outside_projects(
                &[&output, &manifest_output],
                &[&input, &current_project],
            )
            .unwrap_or_else(|error| fail("output_path_collision", error));
            prepare_publish_destinations(&[&output, &manifest_output])
                .unwrap_or_else(|error| fail("output_io", error));
            let manifest_text = std::fs::read_to_string(&manifest)
                .unwrap_or_else(|error| fail("manifest_io", error));
            let (document, target_kind, api) = manifest_for_finalization(&manifest_text)
                .unwrap_or_else(|error| fail("invalid_manifest", error));
            let source = std::fs::read_to_string(&analysis_path)
                .unwrap_or_else(|error| fail("source_io", error));
            let partial = std::fs::read_to_string(&partial_path)
                .unwrap_or_else(|error| fail("source_io", error));
            let finalized = run_compiler_on_path(&analysis_path, move |tcx| {
                tools::finalize_additive_source(&source, &partial, &target_kind, &api, tcx)
            })
            .unwrap_or_else(|_| fail("compiler_failure", "analysis project failed to compile"))
            .unwrap_or_else(|error| replacement_failure(error));
            let manifest_text = updated_manifest(document, &finalized.wrappers);
            publish_files(&[
                (&output, finalized.source.as_bytes()),
                (&manifest_output, manifest_text.as_bytes()),
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
            let json = tools::observation_document_to_json(&document)
                .unwrap_or_else(|error| fail("invalid_observations", error));
            publish_files(&[(&output, json.as_bytes())])
                .unwrap_or_else(|error| fail("output_io", error));
        }
        Command::SynthesizeRules {
            output,
            observations,
        } => {
            validate_observation_inputs(&observations)
                .unwrap_or_else(|error| fail("observation_input", error));
            validate_output_input_paths(
                &[&output],
                &observations
                    .iter()
                    .map(PathBuf::as_path)
                    .collect::<Vec<_>>(),
            )
            .unwrap_or_else(|error| fail("output_path_collision", error));
            let documents = observations
                .iter()
                .map(|path| {
                    let text = std::fs::read_to_string(path)
                        .unwrap_or_else(|error| fail("observation_io", error));
                    tools::observation_document_from_json(&text)
                        .unwrap_or_else(|error| fail("invalid_observations", error))
                })
                .collect::<Vec<_>>();
            let document = tools::synthesize_rules(&documents)
                .unwrap_or_else(|error| fail("rule_synthesis", error));
            let json = tools::rule_document_to_json(&document)
                .unwrap_or_else(|error| fail("invalid_rules", error));
            prepare_publish_destinations(&[&output])
                .unwrap_or_else(|error| fail("output_io", error));
            publish_files(&[(&output, json.as_bytes())])
                .unwrap_or_else(|error| fail("output_io", error));
        }
        Command::PrettyPrintRules { output, rules } => {
            validate_output_input_paths(&[&output], &[&rules])
                .unwrap_or_else(|error| fail("output_path_collision", error));
            let text =
                std::fs::read_to_string(&rules).unwrap_or_else(|error| fail("rule_io", error));
            let document = tools::rule_document_from_json(&text)
                .unwrap_or_else(|error| fail("invalid_rules", error));
            let markdown = tools::rule_document_to_markdown(&document)
                .unwrap_or_else(|error| fail("invalid_rules", error));
            prepare_publish_destinations(&[&output])
                .unwrap_or_else(|error| fail("output_io", error));
            publish_files(&[(&output, markdown.as_bytes())])
                .unwrap_or_else(|error| fail("output_io", error));
        }
        Command::MergeObservations {
            output,
            observations,
        } => {
            validate_observation_inputs(&observations)
                .unwrap_or_else(|error| fail("observation_input", error));
            validate_output_input_paths(
                &[&output],
                &observations
                    .iter()
                    .map(PathBuf::as_path)
                    .collect::<Vec<_>>(),
            )
            .unwrap_or_else(|error| fail("output_path_collision", error));
            let documents = observations
                .iter()
                .map(|path| {
                    let text = std::fs::read_to_string(path)
                        .unwrap_or_else(|error| fail("observation_io", error));
                    tools::observation_document_from_json(&text)
                        .unwrap_or_else(|error| fail("invalid_observations", error))
                })
                .collect::<Vec<_>>();
            let document = tools::merge_observation_documents(&documents)
                .unwrap_or_else(|error| fail("observation_merge", error));
            let json = tools::observation_document_to_json(&document)
                .unwrap_or_else(|error| fail("invalid_observations", error));
            prepare_publish_destinations(&[&output])
                .unwrap_or_else(|error| fail("output_io", error));
            publish_files(&[(&output, json.as_bytes())])
                .unwrap_or_else(|error| fail("output_io", error));
        }
    }
}
