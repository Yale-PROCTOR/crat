#![feature(rustc_private)]

extern crate rustc_driver;

use std::{
    collections::{BTreeMap, BTreeSet},
    env,
    ffi::OsStr,
    fs::{self, File},
    io::{self, Write},
    path::{Path, PathBuf},
};

use crown_artifact_inventory::{
    analyze_json_claims, analyze_named_rust_sources, analyze_rust_source,
    parse_official_evaluation, JsonClaimCounts, OfficialEvaluation, RustCounts,
};

const CODE_CSV: &str = "2026-07-27-crown-code-counts.csv";
const SITE_CSV: &str = "2026-07-27-crown-site-conversion-rates.csv";
const JSON_CSV: &str = "2026-07-27-crown-json-claims.csv";
const PAPER_CSV: &str = "2026-07-27-crown-paper-declaration-consistency.csv";
const OFFICIAL_CSV: &str = "2026-07-27-crown-official-metric-consistency.csv";

struct ProgramInventory {
    name: String,
    original: RustCounts,
    transformed: RustCounts,
    claims: JsonClaimCounts,
    original_rust_files: usize,
    transformed_rust_files: usize,
    rust_file_sets_match: bool,
    rust_parse_failures: Vec<String>,
    missing_json: Vec<String>,
    official: OfficialEvaluation,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = env::args_os().skip(1).collect();
    if args.len() != 3 {
        return Err(
            "usage: crown_artifact_inventory <rs-crown> <rs-crown-transformed> <out-dir>".into(),
        );
    }
    let original_root = PathBuf::from(&args[0]);
    let transformed_root = PathBuf::from(&args[1]);
    let out_dir = PathBuf::from(&args[2]);

    let original_names = program_names(&original_root)?;
    let transformed_names = program_names(&transformed_root)?;
    let official = parse_official_evaluation(&fs::read_to_string(
        transformed_root.join("evaluation.tsv"),
    )?)
    .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
    if original_names != transformed_names {
        return Err(format!(
            "program directory mismatch: original_only={:?}, transformed_only={:?}",
            original_names
                .difference(&transformed_names)
                .collect::<Vec<_>>(),
            transformed_names
                .difference(&original_names)
                .collect::<Vec<_>>()
        )
        .into());
    }
    if original_names != official.keys().cloned().collect() {
        return Err("evaluation.tsv program names do not match the corpus directories".into());
    }

    let mut inventories = Vec::new();
    for name in original_names {
        inventories.push(inventory_program(
            &name,
            &original_root.join(&name),
            &transformed_root.join(&name),
            official
                .get(&name)
                .expect("program-name equality checked above")
                .clone(),
        )?);
    }
    ensure_complete_inputs(&inventories)?;

    fs::create_dir_all(&out_dir)?;
    write_code_csv(&out_dir.join(CODE_CSV), &inventories)?;
    write_site_csv(&out_dir.join(SITE_CSV), &inventories)?;
    write_json_csv(&out_dir.join(JSON_CSV), &inventories)?;
    write_paper_csv(&out_dir.join(PAPER_CSV), &inventories)?;
    write_official_csv(&out_dir.join(OFFICIAL_CSV), &inventories)?;

    println!("programs={}", inventories.len());
    println!("directory_names_match=true");
    println!("partial_or_failed=none");
    for name in [CODE_CSV, SITE_CSV, JSON_CSV, PAPER_CSV, OFFICIAL_CSV] {
        println!("{}", out_dir.join(name).display());
    }
    Ok(())
}

fn inventory_program(
    name: &str,
    original_dir: &Path,
    transformed_dir: &Path,
    official: OfficialEvaluation,
) -> Result<ProgramInventory, Box<dyn std::error::Error>> {
    let original_files = rust_files(original_dir)?;
    let transformed_files = rust_files(transformed_dir)?;
    let original_rel = relative_set(original_dir, &original_files);
    let transformed_rel = relative_set(transformed_dir, &transformed_files);
    let mut rust_parse_failures = Vec::new();
    let original = inventory_rust_files(
        original_dir,
        &original_files,
        "original",
        &mut rust_parse_failures,
    )?;
    let transformed = inventory_rust_files(
        transformed_dir,
        &transformed_files,
        "transformed",
        &mut rust_parse_failures,
    )?;

    let analysis_dir = transformed_dir.join("analysis_results");
    let mut missing_json = Vec::new();
    let mut json = BTreeMap::new();
    for kind in ["ownership", "statistics", "mutability", "fatness"] {
        let path = analysis_dir.join(format!("{kind}.json"));
        match fs::read_to_string(&path) {
            Ok(content) => {
                json.insert(kind, content);
            }
            Err(error) => {
                missing_json.push(format!("{kind}:{error}"));
            }
        }
    }
    let claims = if missing_json.is_empty() {
        analyze_json_claims(
            &json["ownership"],
            &json["statistics"],
            &json["mutability"],
            &json["fatness"],
        )
        .map_err(|error| format!("{name}: invalid analysis JSON: {error}"))?
    } else {
        JsonClaimCounts::default()
    };

    Ok(ProgramInventory {
        name: name.to_owned(),
        original,
        transformed,
        claims,
        original_rust_files: original_files.len(),
        transformed_rust_files: transformed_files.len(),
        rust_file_sets_match: original_rel == transformed_rel,
        rust_parse_failures,
        missing_json,
        official,
    })
}

fn inventory_rust_files(
    root: &Path,
    files: &[PathBuf],
    input_kind: &str,
    failures: &mut Vec<String>,
) -> io::Result<RustCounts> {
    let mut sources = Vec::new();
    for path in files {
        sources.push((rust_module_path(root, path), fs::read_to_string(path)?));
    }
    let source_refs: Vec<_> = sources
        .iter()
        .map(|(module, source)| (module.as_str(), source.as_str()))
        .collect();
    match analyze_named_rust_sources(&source_refs) {
        Ok(counts) => Ok(counts),
        Err(_) => {
            for (path, (_, source)) in files.iter().zip(&sources) {
                if let Err(error) = analyze_rust_source(source) {
                    failures.push(format!(
                        "{input_kind}:{}:{}",
                        path.strip_prefix(root).unwrap_or(path).display(),
                        error
                    ));
                }
            }
            Ok(RustCounts::default())
        }
    }
}

fn ensure_complete_inputs(rows: &[ProgramInventory]) -> Result<(), String> {
    let mut failures = Vec::new();
    for row in rows {
        if row.original_rust_files == 0 || row.transformed_rust_files == 0 {
            failures.push(format!(
                "{}: missing required Rust input files (original={}, transformed={})",
                row.name, row.original_rust_files, row.transformed_rust_files
            ));
        }
        if !row.rust_file_sets_match {
            failures.push(format!("{}: Rust input file sets do not match", row.name));
        }
        for failure in &row.rust_parse_failures {
            failures.push(format!("{}: unparseable Rust input: {failure}", row.name));
        }
        for missing in &row.missing_json {
            failures.push(format!(
                "{}: missing required analysis JSON: {missing}",
                row.name
            ));
        }
    }
    if failures.is_empty() {
        Ok(())
    } else {
        Err(format!(
            "inventory inputs are incomplete; refusing to write authoritative CSV:\n{}",
            failures.join("\n")
        ))
    }
}

fn rust_module_path(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .with_extension("")
        .iter()
        .map(|component| component.to_string_lossy().replace('-', "_"))
        .collect::<Vec<_>>()
        .join("::")
}

fn program_names(root: &Path) -> io::Result<BTreeSet<String>> {
    let mut names = BTreeSet::new();
    for entry in fs::read_dir(root)? {
        let entry = entry?;
        if entry.file_type()?.is_dir() {
            names.insert(entry.file_name().to_string_lossy().into_owned());
        }
    }
    Ok(names)
}

fn rust_files(root: &Path) -> io::Result<Vec<PathBuf>> {
    let mut files = Vec::new();
    collect_rust_files(root, &mut files)?;
    files.sort();
    Ok(files)
}

fn collect_rust_files(dir: &Path, files: &mut Vec<PathBuf>) -> io::Result<()> {
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if entry.file_type()?.is_dir() {
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

fn relative_set(root: &Path, files: &[PathBuf]) -> BTreeSet<PathBuf> {
    files
        .iter()
        .map(|path| path.strip_prefix(root).unwrap_or(path).to_owned())
        .collect()
}

fn write_code_csv(path: &Path, rows: &[ProgramInventory]) -> io::Result<()> {
    let mut out = File::create(path)?;
    writeln!(
        out,
        "program,artifact_status,original_rust_files,transformed_rust_files,rust_file_sets_match,rust_parse_failures,missing_json_files,local_Box,local_Option_Box,inferred_Box_local_slots,param_Box,param_Option_Box,return_Box,return_Option_Box,field_Box,field_Option_Box,explicit_box_family_type_positions,emitted_Box_function_slots,Box_new_calls,Box_new_local_initializer_evidence,Box_new_assignment_rhs_evidence,Box_expression_evidence_total,reference_plain_positions,reference_mut_positions,Option_reference_positions,Option_mut_reference_positions,reference_family_type_positions,Box_from_raw_calls,Box_into_raw_calls,remaining_raw_malloc,remaining_raw_calloc,remaining_raw_realloc,remaining_raw_free,explicit_drop_calls"
    )?;
    for row in rows {
        let declarations = &row.transformed.declarations;
        let reference_plain = declarations.local_ref
            + declarations.param_ref
            + declarations.return_ref
            + declarations.field_ref;
        let reference_mut = declarations.local_mut_ref
            + declarations.param_mut_ref
            + declarations.return_mut_ref
            + declarations.field_mut_ref;
        let option_reference = declarations.local_option_ref
            + declarations.param_option_ref
            + declarations.return_option_ref
            + declarations.field_option_ref;
        let option_mut_reference = declarations.local_option_mut_ref
            + declarations.param_option_mut_ref
            + declarations.return_option_mut_ref
            + declarations.field_option_mut_ref;
        let values = [
            row.name.clone(),
            "ok".to_owned(),
            row.original_rust_files.to_string(),
            row.transformed_rust_files.to_string(),
            row.rust_file_sets_match.to_string(),
            row.rust_parse_failures.len().to_string(),
            row.missing_json.len().to_string(),
            row.transformed.types.local_box.to_string(),
            row.transformed.types.local_option_box.to_string(),
            row.transformed.inferred_box_local_slots.to_string(),
            row.transformed.types.param_box.to_string(),
            row.transformed.types.param_option_box.to_string(),
            row.transformed.types.return_box.to_string(),
            row.transformed.types.return_option_box.to_string(),
            row.transformed.types.field_box.to_string(),
            row.transformed.types.field_option_box.to_string(),
            row.transformed.box_type_positions().to_string(),
            row.transformed.box_function_slots().to_string(),
            row.transformed.box_new_calls.to_string(),
            row.transformed.box_new_local_initializers.to_string(),
            row.transformed.box_new_assignment_rhs.to_string(),
            row.transformed.box_expression_evidence().to_string(),
            reference_plain.to_string(),
            reference_mut.to_string(),
            option_reference.to_string(),
            option_mut_reference.to_string(),
            row.transformed
                .reference_family_type_positions()
                .to_string(),
            row.transformed.box_from_raw_calls.to_string(),
            row.transformed.box_into_raw_calls.to_string(),
            row.transformed.malloc_calls.to_string(),
            row.transformed.calloc_calls.to_string(),
            row.transformed.realloc_calls.to_string(),
            row.transformed.free_calls.to_string(),
            row.transformed.drop_calls.to_string(),
        ];
        writeln!(out, "{}", values.join(","))?;
    }
    Ok(())
}

fn write_site_csv(path: &Path, rows: &[ProgramInventory]) -> io::Result<()> {
    let mut out = File::create(path)?;
    writeln!(
        out,
        "program,source_malloc,source_calloc,source_realloc,source_malloc_family_total,emitted_raw_malloc,emitted_raw_calloc,emitted_raw_realloc,emitted_raw_malloc_family_total,removed_malloc,removed_calloc,removed_realloc,new_Box_new_conversion_sites,malloc_family_to_Box_rate,unclassified_removed_allocation_delta,source_free,emitted_raw_free,new_explicit_drop_conversion_sites,inferred_implicit_drop_conversion_sites,total_free_to_drop_sites,free_to_drop_rate,free_conversion_residual"
    )?;
    for row in rows {
        let original_alloc = row.original.allocation_calls();
        let emitted_alloc = row.transformed.allocation_calls();
        let removed_malloc = signed_delta(row.original.malloc_calls, row.transformed.malloc_calls);
        let removed_calloc = signed_delta(row.original.calloc_calls, row.transformed.calloc_calls);
        let removed_realloc =
            signed_delta(row.original.realloc_calls, row.transformed.realloc_calls);
        let removed_alloc = signed_delta(original_alloc, emitted_alloc);
        let new_box = positive_delta(row.transformed.box_new_calls, row.original.box_new_calls);
        let new_drop = positive_delta(row.transformed.drop_calls, row.original.drop_calls);
        let removed_free = signed_delta(row.original.free_calls, row.transformed.free_calls);
        let implicit_drop = removed_free - new_drop as i64;
        let total_free_drop = new_drop as i64 + implicit_drop;
        writeln!(
            out,
            "{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{}",
            row.name,
            row.original.malloc_calls,
            row.original.calloc_calls,
            row.original.realloc_calls,
            original_alloc,
            row.transformed.malloc_calls,
            row.transformed.calloc_calls,
            row.transformed.realloc_calls,
            emitted_alloc,
            removed_malloc,
            removed_calloc,
            removed_realloc,
            new_box,
            rate(new_box as i64, original_alloc),
            removed_alloc - new_box as i64,
            row.original.free_calls,
            row.transformed.free_calls,
            new_drop,
            implicit_drop,
            total_free_drop,
            rate(total_free_drop, row.original.free_calls),
            removed_free - total_free_drop,
        )?;
    }
    Ok(())
}

fn write_json_csv(path: &Path, rows: &[ProgramInventory]) -> io::Result<()> {
    let mut out = File::create(path)?;
    writeln!(
        out,
        "program,max_pointer_depth_levels,ownership_fn_d0_Owning,ownership_fn_d0_Transient,ownership_fn_d0_Unknown,ownership_fn_d1_Owning,ownership_fn_d1_Transient,ownership_fn_d1_Unknown,ownership_struct_d0_Owning,ownership_struct_d0_Transient,ownership_struct_d0_Unknown,ownership_struct_d1_Owning,ownership_struct_d1_Transient,ownership_struct_d1_Unknown,ownership_fn_Owning,ownership_fn_Transient,ownership_fn_Unknown,ownership_struct_Owning,ownership_struct_Transient,ownership_struct_Unknown,ownership_total_Owning,ownership_total_Transient,ownership_total_Unknown,mutability_fn_Mut,mutability_fn_Imm,mutability_struct_Mut,mutability_struct_Imm,fatness_fn_Arr,fatness_fn_Ptr,fatness_struct_Arr,fatness_struct_Ptr,num_unsafe_ptrs,num_non_arr_unsafe_ptrs,num_mut_unsafe_ptrs,num_non_arr_mut_unsafe_ptrs,num_unsafe_usages,num_non_arr_unsafe_usages,num_mut_unsafe_usages,num_non_arr_mut_unsafe_usages,num_owning_ptrs_detected,fn_d0_Mut_Ptr_joint"
    )?;
    for row in rows {
        let claims = &row.claims;
        let values = [
            row.name.clone(),
            claims.max_depth.to_string(),
            depth_label(&claims.ownership_fn_by_depth, 0, "Owning").to_string(),
            depth_label(&claims.ownership_fn_by_depth, 0, "Transient").to_string(),
            depth_label(&claims.ownership_fn_by_depth, 0, "Unknown").to_string(),
            depth_label(&claims.ownership_fn_by_depth, 1, "Owning").to_string(),
            depth_label(&claims.ownership_fn_by_depth, 1, "Transient").to_string(),
            depth_label(&claims.ownership_fn_by_depth, 1, "Unknown").to_string(),
            depth_label(&claims.ownership_struct_by_depth, 0, "Owning").to_string(),
            depth_label(&claims.ownership_struct_by_depth, 0, "Transient").to_string(),
            depth_label(&claims.ownership_struct_by_depth, 0, "Unknown").to_string(),
            depth_label(&claims.ownership_struct_by_depth, 1, "Owning").to_string(),
            depth_label(&claims.ownership_struct_by_depth, 1, "Transient").to_string(),
            depth_label(&claims.ownership_struct_by_depth, 1, "Unknown").to_string(),
            label(&claims.ownership_fn, "Owning").to_string(),
            label(&claims.ownership_fn, "Transient").to_string(),
            label(&claims.ownership_fn, "Unknown").to_string(),
            label(&claims.ownership_struct, "Owning").to_string(),
            label(&claims.ownership_struct, "Transient").to_string(),
            label(&claims.ownership_struct, "Unknown").to_string(),
            (label(&claims.ownership_fn, "Owning") + label(&claims.ownership_struct, "Owning"))
                .to_string(),
            (label(&claims.ownership_fn, "Transient")
                + label(&claims.ownership_struct, "Transient"))
            .to_string(),
            (label(&claims.ownership_fn, "Unknown") + label(&claims.ownership_struct, "Unknown"))
                .to_string(),
            label(&claims.mutability_fn, "Mut").to_string(),
            label(&claims.mutability_fn, "Imm").to_string(),
            label(&claims.mutability_struct, "Mut").to_string(),
            label(&claims.mutability_struct, "Imm").to_string(),
            label(&claims.fatness_fn, "Arr").to_string(),
            label(&claims.fatness_fn, "Ptr").to_string(),
            label(&claims.fatness_struct, "Arr").to_string(),
            label(&claims.fatness_struct, "Ptr").to_string(),
            statistic(claims, "num_unsafe_ptrs").to_string(),
            statistic(claims, "num_non_arr_unsafe_ptrs").to_string(),
            statistic(claims, "num_mut_unsafe_ptrs").to_string(),
            statistic(claims, "num_non_arr_mut_unsafe_ptrs").to_string(),
            statistic(claims, "num_unsafe_usages").to_string(),
            statistic(claims, "num_non_arr_unsafe_usages").to_string(),
            statistic(claims, "num_mut_unsafe_usages").to_string(),
            statistic(claims, "num_non_arr_mut_unsafe_usages").to_string(),
            statistic(claims, "num_owning_ptrs_detected").to_string(),
            claims.fn_d0_mut_ptr.to_string(),
        ];
        writeln!(out, "{}", values.join(","))?;
    }
    Ok(())
}

fn write_official_csv(path: &Path, rows: &[ProgramInventory]) -> io::Result<()> {
    let mut out = File::create(path)?;
    writeln!(
        out,
        "program,metric_scope,official_declaration_before,reconstructed_declaration_before,before_integer_match,official_declaration_after,reconstructed_declaration_after,after_integer_match,official_declarations_eliminated,reconstructed_safe_form_function_slots,eliminated_integer_match,official_declaration_reduction_percent,emitted_reference_function_slots_in_official_universe,emitted_Box_function_slots_in_official_universe,emitted_reference_function_slots_outside_official_universe,emitted_Box_function_slots_outside_official_universe,outside_reference_slot_keys,outside_Box_slot_keys,explicit_Box_family_type_positions,inferred_Box_local_slots,Box_new_allocation_call_sites,official_usage_before,official_usage_after,official_usage_reduction_percent,usage_recount_status,BO_declaration_before,BO_declaration_after,BO_Box_function_slots"
    )?;
    for row in rows {
        let reconstructed_before = row.claims.fn_d0_mut_ptr;
        let emitted_refs = row
            .transformed
            .reference_function_slot_keys
            .intersection(&row.claims.fn_d0_mut_ptr_keys)
            .count() as u64;
        let emitted_boxes = row
            .transformed
            .box_function_slot_keys
            .intersection(&row.claims.fn_d0_mut_ptr_keys)
            .count() as u64;
        let outside_refs = row.transformed.reference_function_slots() - emitted_refs;
        let outside_boxes = row.transformed.box_function_slots() - emitted_boxes;
        let outside_ref_keys = row
            .transformed
            .reference_function_slot_keys
            .difference(&row.claims.fn_d0_mut_ptr_keys)
            .cloned()
            .collect::<Vec<_>>()
            .join(";");
        let outside_box_keys = row
            .transformed
            .box_function_slot_keys
            .difference(&row.claims.fn_d0_mut_ptr_keys)
            .cloned()
            .collect::<Vec<_>>()
            .join(";");
        let reconstructed_eliminated = emitted_refs + emitted_boxes;
        let reconstructed_after = reconstructed_before
            .checked_sub(reconstructed_eliminated)
            .ok_or_else(|| {
                io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!(
                        "{}: safe-form slots exceed the official declaration universe",
                        row.name
                    ),
                )
            })?;
        let official_eliminated = row.official.declaration_before - row.official.declaration_after;
        let values = [
            row.name.clone(),
            "unsafe_mutable_non_array_function_d0_slots".to_owned(),
            row.official.declaration_before.to_string(),
            reconstructed_before.to_string(),
            (row.official.declaration_before == reconstructed_before).to_string(),
            row.official.declaration_after.to_string(),
            reconstructed_after.to_string(),
            (row.official.declaration_after == reconstructed_after).to_string(),
            official_eliminated.to_string(),
            reconstructed_eliminated.to_string(),
            (official_eliminated == reconstructed_eliminated).to_string(),
            row.official.declaration_rate.clone(),
            emitted_refs.to_string(),
            emitted_boxes.to_string(),
            outside_refs.to_string(),
            outside_boxes.to_string(),
            outside_ref_keys,
            outside_box_keys,
            row.transformed.box_type_positions().to_string(),
            row.transformed.inferred_box_local_slots.to_string(),
            row.transformed.box_new_calls.to_string(),
            row.official.usage_before.to_string(),
            row.official.usage_after.to_string(),
            row.official.usage_rate.clone(),
            "OFFICIAL_CONTEXT_NOT_RECOUNTED_DECLARATION_ONLY".to_owned(),
            "pending_rewriter".to_owned(),
            "pending_rewriter".to_owned(),
            "pending_rewriter".to_owned(),
        ];
        writeln!(out, "{}", values.join(","))?;
    }
    Ok(())
}

fn write_paper_csv(path: &Path, rows: &[ProgramInventory]) -> io::Result<()> {
    let mut out = File::create(path)?;
    writeln!(
        out,
        "program,paper_table2_declaration_before,official_tsv_declaration_before,declaration_before_integer_match,paper_table2_declaration_reduction_percent,official_tsv_declaration_reduction_percent,declaration_rate_match,paper_prose_declaration_note,paper_table2_usage_before_CONTEXT_ONLY,official_tsv_usage_before_CONTEXT_ONLY,paper_table2_usage_reduction_percent_CONTEXT_ONLY,official_tsv_usage_reduction_percent_CONTEXT_ONLY,use_comparison_status"
    )?;
    for row in rows {
        let paper = paper_metrics(&row.name);
        let paper_declaration_rate = format!(
            "{}.{:01}%",
            paper.declaration_percent_tenths / 10,
            paper.declaration_percent_tenths % 10
        );
        let paper_usage_rate = paper
            .use_percent_tenths
            .map(|value| format!("{}.{:01}%", value / 10, value % 10))
            .unwrap_or_else(|| "NaN%".to_owned());
        let values = [
            row.name.clone(),
            paper.pointer_declarations.to_string(),
            row.official.declaration_before.to_string(),
            (paper.pointer_declarations == row.official.declaration_before).to_string(),
            paper_declaration_rate.clone(),
            row.official.declaration_rate.clone(),
            (paper_declaration_rate == row.official.declaration_rate).to_string(),
            if row.name == "rgba" {
                "paper_prose_says_100.0%_while_Table2_and_tsv_say_83.3%"
            } else {
                "none"
            }
            .to_owned(),
            paper.pointer_usages.to_string(),
            row.official.usage_before.to_string(),
            paper_usage_rate,
            row.official.usage_rate.clone(),
            "PAPER_ONLY_CONTEXT_NOT_MATCHED_OR_MISMATCHED".to_owned(),
        ];
        writeln!(out, "{}", values.join(","))?;
    }
    Ok(())
}

struct PaperMetrics {
    pointer_declarations: u64,
    declaration_percent_tenths: i64,
    pointer_usages: u64,
    use_percent_tenths: Option<i64>,
}

fn paper_metrics(program: &str) -> PaperMetrics {
    let (pointer_declarations, declaration_percent_tenths, pointer_usages, use_percent_tenths) =
        match program {
            "avl" => (8, 1000, 41, Some(1000)),
            "binn" => (103, 650, 247, Some(713)),
            "brotli" => (846, 214, 3686, Some(209)),
            "bst" => (5, 1000, 22, Some(1000)),
            "buffer" => (38, 1000, 56, Some(1000)),
            "bzip2" => (126, 262, 2946, Some(37)),
            "genann" => (28, 71, 160, Some(150)),
            "heman" => (360, 350, 926, Some(602)),
            "ht" => (6, 1000, 28, Some(1000)),
            "json.h" => (128, 234, 647, Some(621)),
            "libcsv" => (20, 700, 141, Some(979)),
            "libtree" => (48, 396, 227, Some(621)),
            "libzahl" => (87, 161, 279, Some(168)),
            "lil" => (202, 188, 1018, Some(694)),
            "lodepng" => (227, 449, 1232, Some(377)),
            "quadtree" => (33, 424, 117, Some(487)),
            "rgba" => (6, 833, 12, Some(1000)),
            "robotfindskitten" => (1, 0, 0, None),
            "tulipindicators" => (134, 7, 625, Some(0)),
            "urlparser" => (9, 111, 40, Some(450)),
            _ => panic!("missing CROWN paper Table 2 metrics for {program}"),
        };
    PaperMetrics {
        pointer_declarations,
        declaration_percent_tenths,
        pointer_usages,
        use_percent_tenths,
    }
}

fn label(counts: &BTreeMap<String, u64>, name: &str) -> u64 {
    counts.get(name).copied().unwrap_or_default()
}

fn depth_label(counts: &[BTreeMap<String, u64>], depth: usize, name: &str) -> u64 {
    counts
        .get(depth)
        .and_then(|counts| counts.get(name))
        .copied()
        .unwrap_or_default()
}

fn statistic(claims: &JsonClaimCounts, name: &str) -> u64 {
    label(&claims.statistics, name)
}

fn positive_delta(after: u64, before: u64) -> u64 {
    after.saturating_sub(before)
}

fn signed_delta(before: u64, after: u64) -> i64 {
    before as i64 - after as i64
}

fn rate(numerator: i64, denominator: u64) -> String {
    if denominator == 0 {
        "NA".to_owned()
    } else {
        format!("{:.6}", numerator as f64 / denominator as f64)
    }
}
