use std::{
    collections::{BTreeMap, BTreeSet},
    ffi::OsStr,
    fs::{self, File},
    io::Write,
    path::{Component, Path, PathBuf},
    process::Command,
    time::Instant,
};

use quote::ToTokens;
use syn::{Fields, GenericArgument, Item, PathArguments, Type};

const MACHINE_ID: &str = "lambda7";
const PLATFORM: &str = "linux-x86_64";
const RAW_RUST_MANIFEST_SHA256: &str =
    "916da9b02ef5cac85c197e7a7e38dfe46b5a067d69fa53fb785a1e40df44054e";
const TRANSFORMED_RUST_MANIFEST_SHA256: &str =
    "cc90b03365b2a0bf6930ea1223f4f50abf1b8ebcd69502a9581ace94a1387798";
const RAW_CORPUS_DIGEST: &str = "9fc912af10fd3b235fe4d444d2fbac0bc521509b1c9447fc551acd0130e0e621";
const TRANSFORMED_CORPUS_DIGEST: &str =
    "9a62632d523939ec5c85f7c98f977bfba040a69657676c7ae91bb5f61bd4f14";
const P2_MANIFEST_SHA256: &str = "65a0eb62613431cfdadf9d1b46199a5789a818a1e77bc6e0f71374b34fa547e1";
const A4_MANIFEST_SHA256: &str = "66f85f5a30b77ba7e26c66fda0cccb0becdff13b4a8a03da74bb8d08e34e7c71";
const SOURCE_REFERENCE_MANIFEST_SHA256: &str =
    "b6e652d588e28587399a4c81b892967e6cb18cb6f3e29ee82f71228f6a21afb1";

const P2_HEADER: &str = "platform\tmachine_id\tprogram\tfield_key\tfield_slot\tdiscovery_class\tresolved_stores\tblocked_address_of\tblocked_unresolved\taccepted_kind\tforce_result\tterminal_bucket\tcore_families";
const A4_HEADER: &str = "program\tfield_key\tfield_slot\tbaseline_kind\tbaseline_force\tbaseline_core_families\tproof_eligible\tproof_reason\tselected_own_assumes\tsource_selector_indices\tnecessary_labels\trelaxed_force\trelaxed_kind\trelaxed_core_families\trelaxed_core_labels";
const SOURCE_READING_HEADER: &str = "program\tfield_key\tfield_slot\tordinary_kind\tclosed_world_class\topen_class\tclosed_world_evidence\topen_evidence\tclosed_world_root_count\topen_root_count";
const EXCLUSION_HEADER: &str = "program\tfield_key\tstatus\tevidence_manifest";

type Identity = (String, String);
type FieldMap = BTreeMap<(String, usize), FieldDecl>;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum CrownStatus {
    Box,
    OptionBox,
    Unboxed,
}

impl CrownStatus {
    fn as_str(&self) -> &'static str {
        match self {
            Self::Box => "Box",
            Self::OptionBox => "Option<Box>",
            Self::Unboxed => "unboxed",
        }
    }

    fn is_boxed(&self) -> bool {
        !matches!(self, Self::Unboxed)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldIdentity {
    pub struct_path: String,
    pub ordinal: usize,
    pub depth: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FieldDecl {
    pub struct_path: String,
    pub ordinal: usize,
    pub name: String,
    pub type_text: String,
    pub crown_status: CrownStatus,
    pub source: String,
}

#[derive(Clone, Debug)]
struct P2Row {
    identity: Identity,
    verdict: String,
}

#[derive(Clone, Debug)]
struct A4Row {
    identity: Identity,
    source_candidate: bool,
    baseline_force: String,
}

#[derive(Clone, Debug)]
struct SourceReading {
    closed_class: String,
    open_class: String,
    closed_evidence: String,
    open_evidence: String,
}

#[derive(Clone, Debug)]
struct Exclusion {
    status: String,
    evidence_manifest: String,
}

#[derive(Clone, Debug)]
struct JoinRow {
    identity: Identity,
    verdict: String,
    crown_status: CrownStatus,
    raw: FieldDecl,
    transformed: FieldDecl,
    source_status: String,
    closed_class: String,
    open_class: String,
    closed_evidence: String,
    open_evidence: String,
    source_manifest: String,
}

pub struct JoinInputs {
    pub raw_root: PathBuf,
    pub transformed_root: PathBuf,
    pub p2_root: PathBuf,
    pub a4_root: PathBuf,
    pub source_reference_root: PathBuf,
    pub preregistered_inputs: PathBuf,
    pub output: PathBuf,
}

#[derive(Debug)]
pub struct RunSummary {
    pub manifest: String,
    pub rows: usize,
    pub boxed: usize,
    pub hard_unsat: usize,
    pub force_sat: usize,
}

pub fn parse_field_identity(field_key: &str) -> Result<FieldIdentity, String> {
    let (struct_path, suffix) = field_key
        .rsplit_once("::field")
        .ok_or_else(|| format!("field key lacks ::field ordinal: {field_key}"))?;
    let (ordinal, depth) = suffix
        .split_once("@d")
        .ok_or_else(|| format!("field key lacks @d depth: {field_key}"))?;
    if struct_path.is_empty() || ordinal.is_empty() || depth.is_empty() {
        return Err(format!("malformed field key: {field_key}"));
    }
    Ok(FieldIdentity {
        struct_path: struct_path.to_owned(),
        ordinal: ordinal
            .parse()
            .map_err(|error| format!("invalid field ordinal in {field_key}: {error}"))?,
        depth: depth
            .parse()
            .map_err(|error| format!("invalid field depth in {field_key}: {error}"))?,
    })
}

pub fn classify_box_type(source: &str) -> Result<CrownStatus, String> {
    let ty: Type = syn::parse_str(source).map_err(|error| error.to_string())?;
    Ok(classify_syn_type(&ty))
}

fn classify_syn_type(ty: &Type) -> CrownStatus {
    if type_path_last(ty).is_some_and(|segment| segment.ident == "Box") {
        return CrownStatus::Box;
    }
    let Some(option) = type_path_last(ty).filter(|segment| segment.ident == "Option") else {
        return CrownStatus::Unboxed;
    };
    let PathArguments::AngleBracketed(arguments) = &option.arguments else {
        return CrownStatus::Unboxed;
    };
    let mut types = arguments.args.iter().filter_map(|argument| match argument {
        GenericArgument::Type(ty) => Some(ty),
        _ => None,
    });
    let Some(inner) = types.next() else {
        return CrownStatus::Unboxed;
    };
    if types.next().is_none() && type_path_last(inner).is_some_and(|segment| segment.ident == "Box")
    {
        CrownStatus::OptionBox
    } else {
        CrownStatus::Unboxed
    }
}

fn type_path_last(ty: &Type) -> Option<&syn::PathSegment> {
    let Type::Path(path) = ty else {
        return None;
    };
    path.path.segments.last()
}

pub fn extract_struct_fields(module_path: &str, source: &str) -> Result<FieldMap, String> {
    let file = syn::parse_file(source).map_err(|error| error.to_string())?;
    let mut modules = module_path
        .split("::")
        .filter(|part| !part.is_empty())
        .map(str::to_owned)
        .collect::<Vec<_>>();
    let mut fields = BTreeMap::new();
    collect_items(&file.items, &mut modules, &mut fields, module_path)?;
    Ok(fields)
}

fn collect_items(
    items: &[Item],
    modules: &mut Vec<String>,
    fields: &mut FieldMap,
    source_name: &str,
) -> Result<(), String> {
    for item in items {
        match item {
            Item::Mod(module) => {
                if let Some((_, items)) = &module.content {
                    modules.push(module.ident.to_string());
                    collect_items(items, modules, fields, source_name)?;
                    modules.pop();
                }
            }
            Item::Struct(item_struct) => {
                let Fields::Named(named) = &item_struct.fields else {
                    continue;
                };
                let struct_path = modules
                    .iter()
                    .map(String::as_str)
                    .chain(std::iter::once(item_struct.ident.to_string().as_str()))
                    .collect::<Vec<_>>()
                    .join("::");
                for (ordinal, field) in named.named.iter().enumerate() {
                    let name = field
                        .ident
                        .as_ref()
                        .ok_or_else(|| format!("unnamed field in {struct_path}"))?
                        .to_string();
                    let declaration = FieldDecl {
                        struct_path: struct_path.clone(),
                        ordinal,
                        name,
                        type_text: field.ty.to_token_stream().to_string(),
                        crown_status: classify_syn_type(&field.ty),
                        source: source_name.to_owned(),
                    };
                    if fields
                        .insert((struct_path.clone(), ordinal), declaration)
                        .is_some()
                    {
                        return Err(format!(
                            "duplicate field declaration: {struct_path} ordinal {ordinal}"
                        ));
                    }
                }
            }
            _ => {}
        }
    }
    Ok(())
}

pub fn join_field(
    raw: &FieldMap,
    transformed: &FieldMap,
    identity: &FieldIdentity,
) -> Result<(FieldDecl, FieldDecl), String> {
    if identity.depth != 0 {
        return Err(format!(
            "ordinal bridge is preregistered only for depth zero: {identity:?}"
        ));
    }
    let key = (identity.struct_path.clone(), identity.ordinal);
    let raw = raw
        .get(&key)
        .ok_or_else(|| format!("raw declaration missing for {key:?}"))?;
    let transformed = transformed
        .get(&key)
        .ok_or_else(|| format!("transformed declaration missing for {key:?}"))?;
    if raw.name != transformed.name {
        return Err(format!(
            "ordinal bridge field-name mismatch for {key:?}: raw={} transformed={}",
            raw.name, transformed.name
        ));
    }
    Ok((raw.clone(), transformed.clone()))
}

pub fn validate_source_partition(
    source: &BTreeSet<Identity>,
    measured: &BTreeSet<Identity>,
    excluded: &BTreeMap<Identity, String>,
    expected_source: usize,
    expected_measured: usize,
    expected_excluded: usize,
) -> Result<(), String> {
    if source.len() != expected_source
        || measured.len() != expected_measured
        || excluded.len() != expected_excluded
    {
        return Err(format!(
            "source denominator drift: source={} measured={} excluded={}",
            source.len(),
            measured.len(),
            excluded.len()
        ));
    }
    let excluded_set = excluded.keys().cloned().collect::<BTreeSet<_>>();
    if !measured.is_disjoint(&excluded_set) {
        return Err("measured and excluded source identities overlap".to_owned());
    }
    let union = measured
        .union(&excluded_set)
        .cloned()
        .collect::<BTreeSet<_>>();
    if &union != source {
        return Err(format!(
            "measured/excluded union differs from source universe: missing={:?} extra={:?}",
            source.difference(&union).collect::<Vec<_>>(),
            union.difference(source).collect::<Vec<_>>()
        ));
    }
    Ok(())
}

pub fn run(inputs: &JoinInputs) -> Result<RunSummary, String> {
    if inputs.output.exists() {
        return Err(format!(
            "completed output already exists: {}",
            inputs.output.display()
        ));
    }
    let partial = inputs.output.with_extension("partial");
    if partial.exists() {
        return Err(format!(
            "partial output already exists: {}",
            partial.display()
        ));
    }
    fs::create_dir_all(&partial)
        .map_err(|error| format!("create {}: {error}", partial.display()))?;
    let started = Instant::now();
    match run_inner(inputs, &partial, started) {
        Ok(summary) => {
            fs::rename(&partial, &inputs.output).map_err(|error| {
                format!(
                    "publish {} from {}: {error}",
                    inputs.output.display(),
                    partial.display()
                )
            })?;
            Ok(summary)
        }
        Err(error) => {
            let peak = current_peak_rss_kb().unwrap_or(0);
            let escaped = error.replace(['\n', '\r'], " ");
            let _ = fs::write(
                partial.join("receipt.txt"),
                format!(
                    "machine_id={MACHINE_ID}\nplatform={PLATFORM}\nmeasurement_class=crown-differential-reference-join\nreference_only=true\ndata=false\nphase=join\nerror={escaped}\nwall_s={:.3}\npeak_rss_kb={peak}\n",
                    started.elapsed().as_secs_f64()
                ),
            );
            Err(error)
        }
    }
}

fn run_inner(inputs: &JoinInputs, output: &Path, started: Instant) -> Result<RunSummary, String> {
    verify_machine()?;
    let (head, branch) = verify_git_provenance()?;
    let raw_manifest = inputs.preregistered_inputs.join("rs-crown-rust.sha256");
    let transformed_manifest = inputs
        .preregistered_inputs
        .join("crown-emitted-rust.sha256");
    let raw_files =
        verify_rust_manifest(&inputs.raw_root, &raw_manifest, RAW_RUST_MANIFEST_SHA256)?;
    let transformed_files = verify_rust_manifest(
        &inputs.transformed_root,
        &transformed_manifest,
        TRANSFORMED_RUST_MANIFEST_SHA256,
    )?;
    if raw_files != transformed_files {
        return Err(format!(
            "raw/transformed Rust file identity differs: raw_only={:?} transformed_only={:?}",
            raw_files.difference(&transformed_files).collect::<Vec<_>>(),
            transformed_files.difference(&raw_files).collect::<Vec<_>>()
        ));
    }
    verify_artifact_manifest(&inputs.p2_root, P2_MANIFEST_SHA256)?;
    verify_artifact_manifest(&inputs.a4_root, A4_MANIFEST_SHA256)?;
    verify_artifact_manifest(
        &inputs.source_reference_root,
        SOURCE_REFERENCE_MANIFEST_SHA256,
    )?;

    let p2 = parse_p2(&inputs.p2_root.join("classification.tsv"))?;
    let a4 = parse_a4(&inputs.a4_root.join("combined.tsv"))?;
    let p2_set = p2.keys().cloned().collect::<BTreeSet<_>>();
    let a4_set = a4.keys().cloned().collect::<BTreeSet<_>>();
    if p2_set != a4_set {
        return Err(format!(
            "P2/A4 identity mismatch: p2_only={:?} a4_only={:?}",
            p2_set.difference(&a4_set).collect::<Vec<_>>(),
            a4_set.difference(&p2_set).collect::<Vec<_>>()
        ));
    }
    let source_universe = a4
        .values()
        .filter(|row| row.source_candidate)
        .map(|row| row.identity.clone())
        .collect::<BTreeSet<_>>();
    let source_readings =
        parse_source_readings(&inputs.source_reference_root.join("candidate-readings.tsv"))?;
    let source_exclusions = parse_exclusions(&inputs.source_reference_root.join("exclusions.tsv"))?;
    let exclusion_status = source_exclusions
        .iter()
        .map(|(identity, exclusion)| (identity.clone(), exclusion.status.clone()))
        .collect::<BTreeMap<_, _>>();
    validate_source_partition(
        &source_universe,
        &source_readings.keys().cloned().collect(),
        &exclusion_status,
        237,
        62,
        175,
    )?;
    let non_source_deferrals = parse_exclusions(
        &inputs
            .source_reference_root
            .join("non-source-deferrals.tsv"),
    )?;
    if non_source_deferrals.len() != 1
        || non_source_deferrals
            .keys()
            .any(|identity| source_universe.contains(identity) || !p2.contains_key(identity))
    {
        return Err(
            "non-source deferral must be one P2 identity outside the source universe".to_owned(),
        );
    }

    for row in p2.values() {
        let a4_row = &a4[&row.identity];
        let expected_force = if row.verdict == "force-SAT" {
            "sat"
        } else {
            "unsat"
        };
        if a4_row.baseline_force != expected_force {
            return Err(format!(
                "P2/A4 verdict drift for {:?}: p2={} a4={}",
                row.identity, row.verdict, a4_row.baseline_force
            ));
        }
    }

    let programs = p2
        .keys()
        .map(|identity| identity.0.clone())
        .collect::<BTreeSet<_>>();
    let mut raw_inventory = BTreeMap::<String, FieldMap>::new();
    let mut transformed_inventory = BTreeMap::<String, FieldMap>::new();
    for program in &programs {
        raw_inventory.insert(
            program.clone(),
            inventory_program(&inputs.raw_root.join(program))?,
        );
        transformed_inventory.insert(
            program.clone(),
            inventory_program(&inputs.transformed_root.join(program))?,
        );
    }

    let expected_boxed = expected_boxed_fields();
    let mut boxed_fields = BTreeMap::<Identity, (FieldDecl, FieldDecl)>::new();
    for program in &programs {
        let raw = &raw_inventory[program];
        for ((struct_path, ordinal), transformed) in &transformed_inventory[program] {
            if !transformed.crown_status.is_boxed() {
                continue;
            }
            let raw = raw.get(&(struct_path.clone(), *ordinal)).ok_or_else(|| {
                format!(
                    "CROWN boxed field lacks raw ordinal mate: {program} {struct_path} field{ordinal}"
                )
            })?;
            if raw.name != transformed.name {
                return Err(format!(
                    "CROWN boxed field name drift: {program} {struct_path} field{ordinal} raw={} transformed={}",
                    raw.name, transformed.name
                ));
            }
            let field_key = format!("{struct_path}::field{ordinal}@d0");
            boxed_fields.insert(
                (program.clone(), field_key),
                (raw.clone(), transformed.clone()),
            );
        }
    }
    let actual_boxed = boxed_fields
        .iter()
        .map(|(identity, (_, field))| (identity.clone(), field.crown_status.clone()))
        .collect::<BTreeMap<_, _>>();
    if actual_boxed != expected_boxed {
        return Err(format!(
            "boxed-field premise drift: expected_only={:?} actual_only={:?}",
            expected_boxed
                .keys()
                .filter(|key| !actual_boxed.contains_key(*key))
                .collect::<Vec<_>>(),
            actual_boxed
                .keys()
                .filter(|key| !expected_boxed.contains_key(*key))
                .collect::<Vec<_>>()
        ));
    }

    let mut join_rows = Vec::with_capacity(p2.len());
    for row in p2.values() {
        let field_identity = parse_field_identity(&row.identity.1)?;
        let (raw, transformed) = join_field(
            &raw_inventory[&row.identity.0],
            &transformed_inventory[&row.identity.0],
            &field_identity,
        )?;
        let (
            source_status,
            closed_class,
            open_class,
            closed_evidence,
            open_evidence,
            source_manifest,
        ) = if let Some(reading) = source_readings.get(&row.identity) {
            (
                "measured".to_owned(),
                reading.closed_class.clone(),
                reading.open_class.clone(),
                reading.closed_evidence.clone(),
                reading.open_evidence.clone(),
                SOURCE_REFERENCE_MANIFEST_SHA256.to_owned(),
            )
        } else if let Some(exclusion) = source_exclusions.get(&row.identity) {
            (
                exclusion.status.clone(),
                "not-measured".to_owned(),
                "not-measured".to_owned(),
                "not-measured".to_owned(),
                "not-measured".to_owned(),
                exclusion.evidence_manifest.clone(),
            )
        } else if let Some(exclusion) = non_source_deferrals.get(&row.identity) {
            (
                format!("not-in-source-census;{}", exclusion.status),
                "not-in-source-census".to_owned(),
                "not-in-source-census".to_owned(),
                "not-in-source-census".to_owned(),
                "not-in-source-census".to_owned(),
                exclusion.evidence_manifest.clone(),
            )
        } else {
            (
                "not-in-source-census".to_owned(),
                "not-in-source-census".to_owned(),
                "not-in-source-census".to_owned(),
                "not-in-source-census".to_owned(),
                "not-in-source-census".to_owned(),
                A4_MANIFEST_SHA256.to_owned(),
            )
        };
        join_rows.push(JoinRow {
            identity: row.identity.clone(),
            verdict: row.verdict.clone(),
            crown_status: transformed.crown_status.clone(),
            raw,
            transformed,
            source_status,
            closed_class,
            open_class,
            closed_evidence,
            open_evidence,
            source_manifest,
        });
    }
    if join_rows.len() != 261 {
        return Err(format!(
            "join must contain 261 rows, got {}",
            join_rows.len()
        ));
    }

    write_join(output, &join_rows)?;
    write_boxed_fields(output, &boxed_fields)?;
    write_boxed_witnesses(output, &boxed_fields)?;
    write_intersections(output, &join_rows)?;
    write_provenance_cross(output, &join_rows)?;
    write_per_program(output, &join_rows)?;
    write_sensitivity(output, &join_rows)?;

    let boxed = join_rows
        .iter()
        .filter(|row| row.crown_status.is_boxed())
        .count();
    let hard_unsat = join_rows
        .iter()
        .filter(|row| row.verdict == "hard-UNSAT")
        .count();
    let force_sat = join_rows
        .iter()
        .filter(|row| row.verdict == "force-SAT")
        .count();
    let boxed_hard = join_rows
        .iter()
        .filter(|row| row.crown_status.is_boxed() && row.verdict == "hard-UNSAT")
        .count();
    let boxed_deferred = join_rows
        .iter()
        .filter(|row| {
            row.crown_status.is_boxed()
                && row.source_status != "measured"
                && !row.source_status.starts_with("not-in-source-census")
        })
        .count();
    let wall_s = started.elapsed().as_secs_f64();
    let peak_rss_kb = current_peak_rss_kb()?;
    fs::write(
        output.join("report.md"),
        format!(
            "# CROWN differential join — provisional/reference\n\n- use: intermediate closed-world design reference; not publication numbers\n- exact P2 identities: 261 ({hard_unsat} hard-UNSAT, {force_sat} force-SAT)\n- complete CROWN boxed-field inventory: {boxed} (0 plain Box, 7 Option<Box>)\n- CROWN-boxed ∩ hard-UNSAT: {boxed_hard}\n- CROWN-boxed ∩ force-SAT: {}\n- CROWN-unboxed ∩ hard-UNSAT: {}\n- CROWN-unboxed ∩ force-SAT: {}\n- source provenance: 62 measured, 175 typed deferred/excluded, 24 not in the source census\n- boxed rows with typed source-provenance deferral: {boxed_deferred}\n- exclusion sensitivity: CROWN status and P2 verdict remain exact; only provenance-class cells can move\n- machine-local wall: {wall_s:.3} s\n- peak RSS: {peak_rss_kb} KiB\n",
            join_rows.iter().filter(|row| row.crown_status.is_boxed() && row.verdict == "force-SAT").count(),
            join_rows.iter().filter(|row| !row.crown_status.is_boxed() && row.verdict == "hard-UNSAT").count(),
            join_rows.iter().filter(|row| !row.crown_status.is_boxed() && row.verdict == "force-SAT").count(),
        ),
    )
    .map_err(|error| error.to_string())?;
    fs::write(
        output.join("provenance.txt"),
        format!(
            "machine_id={MACHINE_ID}\nplatform={PLATFORM}\nmeasurement_class=crown-differential-reference-join\nreference_only=true\nanalysis_head={head}\nanalysis_branch={branch}\nraw_corpus_digest={RAW_CORPUS_DIGEST}\ntransformed_corpus_digest={TRANSFORMED_CORPUS_DIGEST}\nraw_rust_manifest_sha256={RAW_RUST_MANIFEST_SHA256}\ntransformed_rust_manifest_sha256={TRANSFORMED_RUST_MANIFEST_SHA256}\np2_manifest_sha256={P2_MANIFEST_SHA256}\na4_manifest_sha256={A4_MANIFEST_SHA256}\nsource_reference_manifest_sha256={SOURCE_REFERENCE_MANIFEST_SHA256}\nidentity_bridge=program+fully-qualified-struct+declaration-ordinal+depth0;raw-transformed-field-name-equality\nrows=261\nhard_unsat={hard_unsat}\nforce_sat={force_sat}\ncrown_boxed={boxed}\nsource_measured=62\nsource_typed_deferred=175\nsource_not_in_census=24\nwall_s={wall_s:.3}\npeak_rss_kb={peak_rss_kb}\ntiming_comparison=forbidden-across-machines\n",
        ),
    )
    .map_err(|error| error.to_string())?;
    fs::write(
        output.join("receipt.txt"),
        format!(
            "machine_id={MACHINE_ID}\nplatform={PLATFORM}\nmeasurement_class=crown-differential-reference-join\nreference_only=true\ndata=true\nphase=complete\nrows=261\nboxed={boxed}\nhard_unsat={hard_unsat}\nforce_sat={force_sat}\nwall_s={wall_s:.3}\npeak_rss_kb={peak_rss_kb}\n"
        ),
    )
    .map_err(|error| error.to_string())?;
    let files = [
        "boxed-fields.tsv",
        "boxed-witnesses.tsv",
        "intersections.tsv",
        "join.tsv",
        "per-program.tsv",
        "provenance-by-crown.tsv",
        "provenance.txt",
        "receipt.txt",
        "report.md",
        "sensitivity.tsv",
    ];
    let manifest = write_manifest(output, &files)?;
    Ok(RunSummary {
        manifest,
        rows: join_rows.len(),
        boxed,
        hard_unsat,
        force_sat,
    })
}

fn parse_p2(path: &Path) -> Result<BTreeMap<Identity, P2Row>, String> {
    let rows = parse_table(path, P2_HEADER, 13)?;
    let mut eligible = BTreeMap::new();
    for row in rows {
        match row[5].as_str() {
            "eligible" => {
                if row[0] != PLATFORM || row[1] != MACHINE_ID {
                    return Err("P2 platform/machine provenance drift".to_owned());
                }
                if !matches!(row[11].as_str(), "hard-UNSAT" | "force-SAT") {
                    return Err(format!("unknown P2 verdict: {}", row[11]));
                }
                let identity = (row[2].clone(), row[3].clone());
                let p2_row = P2Row {
                    identity: identity.clone(),
                    verdict: row[11].clone(),
                };
                if eligible.insert(identity, p2_row).is_some() {
                    return Err("duplicate eligible P2 identity".to_owned());
                }
            }
            "no-owned-capable-store" => {}
            other => return Err(format!("unknown P2 discovery class: {other}")),
        }
    }
    let hard = eligible
        .values()
        .filter(|row| row.verdict == "hard-UNSAT")
        .count();
    let sat = eligible
        .values()
        .filter(|row| row.verdict == "force-SAT")
        .count();
    if (eligible.len(), hard, sat) != (261, 257, 4) {
        return Err(format!(
            "P2 partition drift: total={} hard={hard} sat={sat}",
            eligible.len()
        ));
    }
    Ok(eligible)
}

fn parse_a4(path: &Path) -> Result<BTreeMap<Identity, A4Row>, String> {
    let rows = parse_table(path, A4_HEADER, 15)?;
    let mut parsed = BTreeMap::new();
    for row in rows {
        let identity = (row[0].clone(), row[1].clone());
        let value = A4Row {
            identity: identity.clone(),
            source_candidate: row[7] == "allocation-source-count-0",
            baseline_force: row[4].clone(),
        };
        if parsed.insert(identity, value).is_some() {
            return Err("duplicate A4 identity".to_owned());
        }
    }
    if parsed.len() != 261 || parsed.values().filter(|row| row.source_candidate).count() != 237 {
        return Err("A4 261/237 identity partition drift".to_owned());
    }
    Ok(parsed)
}

fn parse_source_readings(path: &Path) -> Result<BTreeMap<Identity, SourceReading>, String> {
    let rows = parse_table(path, SOURCE_READING_HEADER, 10)?;
    let mut parsed = BTreeMap::new();
    for row in rows {
        let identity = (row[0].clone(), row[1].clone());
        let reading = SourceReading {
            closed_class: row[4].clone(),
            open_class: row[5].clone(),
            closed_evidence: row[6].clone(),
            open_evidence: row[7].clone(),
        };
        if parsed.insert(identity, reading).is_some() {
            return Err("duplicate source reading identity".to_owned());
        }
    }
    Ok(parsed)
}

fn parse_exclusions(path: &Path) -> Result<BTreeMap<Identity, Exclusion>, String> {
    let rows = parse_table(path, EXCLUSION_HEADER, 4)?;
    let mut parsed = BTreeMap::new();
    for row in rows {
        let identity = (row[0].clone(), row[1].clone());
        let exclusion = Exclusion {
            status: row[2].clone(),
            evidence_manifest: row[3].clone(),
        };
        if parsed.insert(identity, exclusion).is_some() {
            return Err("duplicate exclusion identity".to_owned());
        }
    }
    Ok(parsed)
}

fn inventory_program(root: &Path) -> Result<FieldMap, String> {
    if !root.is_dir() {
        return Err(format!("program root is absent: {}", root.display()));
    }
    let mut files = Vec::new();
    collect_rust_files(root, &mut files)?;
    files.sort();
    let mut inventory = BTreeMap::new();
    for path in files {
        let relative = path.strip_prefix(root).map_err(|error| error.to_string())?;
        let module = file_module_path(relative)?;
        let source = fs::read_to_string(&path)
            .map_err(|error| format!("read {}: {error}", path.display()))?;
        let fields = extract_struct_fields(&module, &source)
            .map_err(|error| format!("parse {}: {error}", path.display()))?;
        for (key, mut field) in fields {
            field.source = relative.to_string_lossy().into_owned();
            if inventory.insert(key.clone(), field).is_some() {
                return Err(format!(
                    "duplicate program field path across source files: {key:?}"
                ));
            }
        }
    }
    Ok(inventory)
}

fn file_module_path(relative: &Path) -> Result<String, String> {
    let mut parts = relative
        .with_extension("")
        .components()
        .map(|component| match component {
            Component::Normal(value) => Ok(value.to_string_lossy().replace('-', "_")),
            _ => Err(format!("unsupported source path component: {relative:?}")),
        })
        .collect::<Result<Vec<_>, _>>()?;
    if matches!(
        parts.last().map(String::as_str),
        Some("lib" | "c2rust_lib" | "main" | "mod" | "build")
    ) {
        parts.pop();
    }
    Ok(parts.join("::"))
}

fn expected_boxed_fields() -> BTreeMap<Identity, CrownStatus> {
    [
        ("avl", "src::avl::Node::field1@d0"),
        ("avl", "src::avl::Node::field2@d0"),
        ("bst", "src::bst::node::field1@d0"),
        ("bst", "src::bst::node::field2@d0"),
        ("quadtree", "src::src::bounds::quadtree_bounds::field0@d0"),
        ("quadtree", "src::src::bounds::quadtree_bounds::field1@d0"),
        ("quadtree", "src::src::quadtree::quadtree::field0@d0"),
    ]
    .into_iter()
    .map(|(program, field)| {
        (
            (program.to_owned(), field.to_owned()),
            CrownStatus::OptionBox,
        )
    })
    .collect()
}

fn write_join(output: &Path, rows: &[JoinRow]) -> Result<(), String> {
    let mut text = "program\tfield_key\tp2_verdict\tcrown_status\traw_field_name\ttransformed_field_name\traw_type\ttransformed_type\traw_source\ttransformed_source\tsource_status\tclosed_world_class\topen_class\tclosed_world_evidence\topen_evidence\tsource_evidence_manifest\n".to_owned();
    for row in rows {
        text.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            row.identity.0,
            row.identity.1,
            row.verdict,
            row.crown_status.as_str(),
            row.raw.name,
            row.transformed.name,
            row.raw.type_text,
            row.transformed.type_text,
            row.raw.source,
            row.transformed.source,
            row.source_status,
            row.closed_class,
            row.open_class,
            row.closed_evidence,
            row.open_evidence,
            row.source_manifest,
        ));
    }
    fs::write(output.join("join.tsv"), text).map_err(|error| error.to_string())
}

fn write_boxed_fields(
    output: &Path,
    fields: &BTreeMap<Identity, (FieldDecl, FieldDecl)>,
) -> Result<(), String> {
    let mut text = "program\tfield_key\tstruct_path\tdeclaration_ordinal\tfield_name\tcrown_status\traw_type\ttransformed_type\traw_source\ttransformed_source\n".to_owned();
    for ((program, field_key), (raw, transformed)) in fields {
        text.push_str(&format!(
            "{program}\t{field_key}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            raw.struct_path,
            raw.ordinal,
            raw.name,
            transformed.crown_status.as_str(),
            raw.type_text,
            transformed.type_text,
            raw.source,
            transformed.source,
        ));
    }
    fs::write(output.join("boxed-fields.tsv"), text).map_err(|error| error.to_string())
}

fn write_boxed_witnesses(
    output: &Path,
    fields: &BTreeMap<Identity, (FieldDecl, FieldDecl)>,
) -> Result<(), String> {
    let mut text =
        "program\tfield_key\tfield_name\tcrown_status\traw_source\ttransformed_source\n".to_owned();
    let mut seen = BTreeSet::new();
    for ((program, field_key), (raw, transformed)) in fields {
        if seen.insert(program) {
            text.push_str(&format!(
                "{program}\t{field_key}\t{}\t{}\t{}\t{}\n",
                raw.name,
                transformed.crown_status.as_str(),
                raw.source,
                transformed.source,
            ));
        }
    }
    fs::write(output.join("boxed-witnesses.tsv"), text).map_err(|error| error.to_string())
}

fn write_intersections(output: &Path, rows: &[JoinRow]) -> Result<(), String> {
    let mut text = "crown_partition\tp2_partition\tcount\n".to_owned();
    for crown in ["boxed", "unboxed"] {
        for verdict in ["hard-UNSAT", "force-SAT"] {
            let count = rows
                .iter()
                .filter(|row| {
                    row.verdict == verdict && row.crown_status.is_boxed() == (crown == "boxed")
                })
                .count();
            text.push_str(&format!("{crown}\t{verdict}\t{count}\n"));
        }
    }
    fs::write(output.join("intersections.tsv"), text).map_err(|error| error.to_string())
}

fn write_provenance_cross(output: &Path, rows: &[JoinRow]) -> Result<(), String> {
    let mut counts = BTreeMap::<(String, String, String, String), usize>::new();
    for row in rows {
        *counts
            .entry((
                "source-status".to_owned(),
                row.source_status.clone(),
                row.crown_status.as_str().to_owned(),
                row.verdict.clone(),
            ))
            .or_default() += 1;
        if row.source_status == "measured" {
            for (axis, class) in [
                ("closed-world-class", &row.closed_class),
                ("open-class", &row.open_class),
            ] {
                *counts
                    .entry((
                        axis.to_owned(),
                        class.clone(),
                        row.crown_status.as_str().to_owned(),
                        row.verdict.clone(),
                    ))
                    .or_default() += 1;
            }
        }
    }
    let mut text = "axis\tprovenance_class\tcrown_status\tp2_verdict\tcount\n".to_owned();
    for ((axis, class, crown, verdict), count) in counts {
        text.push_str(&format!("{axis}\t{class}\t{crown}\t{verdict}\t{count}\n"));
    }
    fs::write(output.join("provenance-by-crown.tsv"), text).map_err(|error| error.to_string())
}

fn write_per_program(output: &Path, rows: &[JoinRow]) -> Result<(), String> {
    let programs = rows
        .iter()
        .map(|row| row.identity.0.clone())
        .collect::<BTreeSet<_>>();
    let mut text = "program\ttotal\thard_unsat\tforce_sat\tBox\tOption_Box\tunboxed\tsource_measured\tsource_typed_deferred\tnot_in_source_census\n".to_owned();
    for program in programs {
        let program_rows = rows
            .iter()
            .filter(|row| row.identity.0 == program)
            .collect::<Vec<_>>();
        let count = |predicate: &dyn Fn(&JoinRow) -> bool| {
            program_rows.iter().filter(|row| predicate(row)).count()
        };
        text.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            program,
            program_rows.len(),
            count(&|row| row.verdict == "hard-UNSAT"),
            count(&|row| row.verdict == "force-SAT"),
            count(&|row| row.crown_status == CrownStatus::Box),
            count(&|row| row.crown_status == CrownStatus::OptionBox),
            count(&|row| row.crown_status == CrownStatus::Unboxed),
            count(&|row| row.source_status == "measured"),
            count(&|row| {
                row.source_status != "measured"
                    && !row.source_status.starts_with("not-in-source-census")
            }),
            count(&|row| row.source_status.starts_with("not-in-source-census")),
        ));
    }
    fs::write(output.join("per-program.tsv"), text).map_err(|error| error.to_string())
}

fn write_sensitivity(output: &Path, rows: &[JoinRow]) -> Result<(), String> {
    let programs = rows
        .iter()
        .map(|row| row.identity.0.clone())
        .collect::<BTreeSet<_>>();
    let mut text =
        "program\ttyped_deferred\tboxed_deferred\tunboxed_deferred\tstatuses\tsensitivity\n"
            .to_owned();
    for program in programs {
        let deferred = rows
            .iter()
            .filter(|row| {
                row.identity.0 == program
                    && row.source_status != "measured"
                    && !row.source_status.starts_with("not-in-source-census")
            })
            .collect::<Vec<_>>();
        if deferred.is_empty() {
            continue;
        }
        let boxed = deferred
            .iter()
            .filter(|row| row.crown_status.is_boxed())
            .count();
        let statuses = deferred
            .iter()
            .map(|row| row.source_status.as_str())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>()
            .join("|");
        text.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\tCROWN status and P2 verdict fixed; provenance class unknown for deferred rows{}\n",
            program,
            deferred.len(),
            boxed,
            deferred.len() - boxed,
            statuses,
            if boxed > 0 {
                "; boxed-frontier provenance cells may move"
            } else {
                "; boxed-frontier count cannot move"
            }
        ));
    }
    fs::write(output.join("sensitivity.tsv"), text).map_err(|error| error.to_string())
}

fn verify_machine() -> Result<(), String> {
    let hostname = command_stdout(&mut Command::new("hostname"))?;
    if hostname != MACHINE_ID {
        return Err(format!(
            "machine mismatch: expected {MACHINE_ID}, got {hostname}"
        ));
    }
    let platform = format!("{}-{}", std::env::consts::OS, std::env::consts::ARCH);
    if platform != PLATFORM {
        return Err(format!(
            "platform mismatch: expected {PLATFORM}, got {platform}"
        ));
    }
    Ok(())
}

fn verify_git_provenance() -> Result<(String, String), String> {
    let head = command_stdout(Command::new("git").args(["rev-parse", "HEAD"]))?;
    let branch = command_stdout(Command::new("git").args(["branch", "--show-current"]))?;
    if branch != "codex/a4-source-census" {
        return Err(format!(
            "join harness branch mismatch: expected codex/a4-source-census, got {branch}"
        ));
    }
    let dirty = command_stdout(Command::new("git").args(["status", "--porcelain"]))?;
    if !dirty.is_empty() {
        return Err("join harness worktree is dirty".to_owned());
    }
    let published =
        command_stdout(Command::new("git").args(["branch", "-r", "--contains", head.as_str()]))?;
    if !published
        .lines()
        .any(|line| line.trim() == "origin/codex/a4-source-census")
    {
        return Err(format!("join harness head is not published: {head}"));
    }
    Ok((head, branch))
}

fn command_stdout(command: &mut Command) -> Result<String, String> {
    let output = command.output().map_err(|error| error.to_string())?;
    if !output.status.success() {
        return Err(format!(
            "command failed: status={} stderr={}",
            output.status,
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    Ok(String::from_utf8(output.stdout)
        .map_err(|error| error.to_string())?
        .trim()
        .to_owned())
}

fn sha256(path: &Path) -> Result<String, String> {
    let output = command_stdout(Command::new("sha256sum").arg(path))?;
    let digest = output
        .split_whitespace()
        .next()
        .ok_or_else(|| format!("sha256sum produced no digest for {}", path.display()))?;
    if digest.len() != 64 || !digest.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err(format!("invalid sha256sum digest for {}", path.display()));
    }
    Ok(digest.to_owned())
}

fn verify_artifact_manifest(root: &Path, expected: &str) -> Result<(), String> {
    let manifest = root.join("artifact-manifest.sha256");
    let actual = sha256(&manifest)?;
    if actual != expected {
        return Err(format!(
            "artifact manifest digest mismatch for {}: expected={expected} actual={actual}",
            root.display()
        ));
    }
    for (digest, relative) in parse_sha_manifest(&manifest)? {
        let actual = sha256(&root.join(&relative))?;
        if actual != digest {
            return Err(format!(
                "artifact hash mismatch: {} expected={digest} actual={actual}",
                root.join(relative).display()
            ));
        }
    }
    Ok(())
}

fn verify_rust_manifest(
    root: &Path,
    manifest: &Path,
    expected_manifest_sha: &str,
) -> Result<BTreeSet<String>, String> {
    let actual = sha256(manifest)?;
    if actual != expected_manifest_sha {
        return Err(format!(
            "Rust input manifest digest mismatch: {} expected={expected_manifest_sha} actual={actual}",
            manifest.display()
        ));
    }
    let rows = parse_sha_manifest(manifest)?;
    let mut manifested = BTreeSet::new();
    for (digest, relative) in rows {
        if !relative.ends_with(".rs") || !manifested.insert(relative.clone()) {
            return Err(format!(
                "invalid or duplicate Rust manifest path: {relative}"
            ));
        }
        let actual = sha256(&root.join(&relative))?;
        if actual != digest {
            return Err(format!(
                "Rust input hash mismatch: {} expected={digest} actual={actual}",
                root.join(relative).display()
            ));
        }
    }
    let mut actual_files = Vec::new();
    collect_rust_files(root, &mut actual_files)?;
    let actual = actual_files
        .iter()
        .map(|path| {
            path.strip_prefix(root)
                .map(|relative| relative.to_string_lossy().into_owned())
                .map_err(|error| error.to_string())
        })
        .collect::<Result<BTreeSet<_>, _>>()?;
    if actual != manifested {
        return Err(format!(
            "Rust input file set differs from manifest: unmanifested={:?} missing={:?}",
            actual.difference(&manifested).collect::<Vec<_>>(),
            manifested.difference(&actual).collect::<Vec<_>>()
        ));
    }
    Ok(manifested)
}

fn parse_sha_manifest(path: &Path) -> Result<Vec<(String, String)>, String> {
    let text =
        fs::read_to_string(path).map_err(|error| format!("read {}: {error}", path.display()))?;
    let mut rows = Vec::new();
    for (index, line) in text.lines().enumerate() {
        let (digest, relative) = line
            .split_once("  ")
            .ok_or_else(|| format!("{}:{} malformed SHA row", path.display(), index + 1))?;
        let relative_path = Path::new(relative);
        if relative_path.is_absolute()
            || relative_path
                .components()
                .any(|component| !matches!(component, Component::Normal(_)))
        {
            return Err(format!("unsafe manifest path: {relative}"));
        }
        if digest.len() != 64 || !digest.bytes().all(|byte| byte.is_ascii_hexdigit()) {
            return Err(format!(
                "invalid SHA digest at {}:{}",
                path.display(),
                index + 1
            ));
        }
        rows.push((digest.to_owned(), relative.to_owned()));
    }
    if rows.is_empty() {
        return Err(format!("empty SHA manifest: {}", path.display()));
    }
    Ok(rows)
}

fn parse_table(path: &Path, header: &str, columns: usize) -> Result<Vec<Vec<String>>, String> {
    let text =
        fs::read_to_string(path).map_err(|error| format!("read {}: {error}", path.display()))?;
    let mut lines = text.lines();
    if lines.next() != Some(header) {
        return Err(format!("table header drift: {}", path.display()));
    }
    lines
        .enumerate()
        .map(|(index, line)| {
            let row = line.split('\t').map(str::to_owned).collect::<Vec<_>>();
            if row.len() != columns {
                return Err(format!(
                    "{}:{} expected {columns} columns, got {}",
                    path.display(),
                    index + 2,
                    row.len()
                ));
            }
            Ok(row)
        })
        .collect()
}

fn collect_rust_files(root: &Path, files: &mut Vec<PathBuf>) -> Result<(), String> {
    for entry in fs::read_dir(root).map_err(|error| format!("read {}: {error}", root.display()))? {
        let entry = entry.map_err(|error| error.to_string())?;
        let path = entry.path();
        if entry
            .file_type()
            .map_err(|error| error.to_string())?
            .is_dir()
        {
            if entry.file_name() != OsStr::new("target")
                && entry.file_name() != OsStr::new("analysis_results")
            {
                collect_rust_files(&path, files)?;
            }
        } else if path.extension() == Some(OsStr::new("rs")) {
            files.push(path);
        }
    }
    Ok(())
}

fn current_peak_rss_kb() -> Result<u64, String> {
    let status = fs::read_to_string("/proc/self/status")
        .map_err(|error| format!("read /proc/self/status: {error}"))?;
    let rows = status
        .lines()
        .filter_map(|line| line.strip_prefix("VmHWM:"))
        .collect::<Vec<_>>();
    if rows.len() != 1 {
        return Err(format!("expected one VmHWM row, got {}", rows.len()));
    }
    let columns = rows[0].split_whitespace().collect::<Vec<_>>();
    let [value, "kB"] = columns.as_slice() else {
        return Err(format!("malformed VmHWM row: {:?}", rows[0]));
    };
    value.parse::<u64>().map_err(|error| error.to_string())
}

fn write_manifest(root: &Path, files: &[&str]) -> Result<String, String> {
    let mut manifest = String::new();
    for file in files {
        manifest.push_str(&format!("{}  {file}\n", sha256(&root.join(file))?));
    }
    let path = root.join("artifact-manifest.sha256");
    let mut output = File::create(&path).map_err(|error| error.to_string())?;
    output
        .write_all(manifest.as_bytes())
        .map_err(|error| error.to_string())?;
    output.flush().map_err(|error| error.to_string())?;
    sha256(&path)
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use super::*;

    #[test]
    fn field_identity_and_box_shape_are_typed() {
        assert_eq!(
            parse_field_identity("src::bst::node::field2@d0").unwrap(),
            FieldIdentity {
                struct_path: "src::bst::node".to_owned(),
                ordinal: 2,
                depth: 0,
            }
        );
        assert!(parse_field_identity("src::bst::node::field2").is_err());
        assert_eq!(
            classify_box_type("Option<Box<node>>").unwrap(),
            CrownStatus::OptionBox
        );
        assert_eq!(classify_box_type("Box<node>").unwrap(), CrownStatus::Box);
        assert_eq!(
            classify_box_type("*mut node").unwrap(),
            CrownStatus::Unboxed
        );
    }

    #[test]
    fn struct_inventory_uses_module_path_and_declaration_ordinal() {
        let fields = extract_struct_fields(
            "src::bst",
            "pub struct node { pub key: i32, pub left: *mut node, pub right: Option<Box<node>> }",
        )
        .unwrap();
        assert_eq!(fields.len(), 3);
        assert_eq!(fields[&("src::bst::node".to_owned(), 1)].name, "left");
        assert_eq!(
            fields[&("src::bst::node".to_owned(), 2)].crown_status,
            CrownStatus::OptionBox
        );
    }

    #[test]
    fn ordinal_bridge_rejects_field_name_drift() {
        let raw = extract_struct_fields("src::bst", "struct node { left: *mut node }").unwrap();
        let transformed =
            extract_struct_fields("src::bst", "struct node { right: Box<node> }").unwrap();
        let identity = FieldIdentity {
            struct_path: "src::bst::node".to_owned(),
            ordinal: 0,
            depth: 0,
        };
        assert!(join_field(&raw, &transformed, &identity).is_err());
    }

    #[test]
    fn source_partition_is_exact_and_two_sided() {
        let source = BTreeSet::from([
            ("p".to_owned(), "a".to_owned()),
            ("p".to_owned(), "b".to_owned()),
        ]);
        let measured = BTreeSet::from([("p".to_owned(), "a".to_owned())]);
        let excluded = BTreeMap::from([(
            ("p".to_owned(), "b".to_owned()),
            "typed-deferred".to_owned(),
        )]);
        assert!(validate_source_partition(&source, &measured, &excluded, 2, 1, 1).is_ok());

        let incomplete = BTreeMap::new();
        assert!(validate_source_partition(&source, &measured, &incomplete, 2, 1, 1).is_err());
    }
}
