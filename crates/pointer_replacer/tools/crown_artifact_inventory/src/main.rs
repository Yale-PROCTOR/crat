use std::{
    collections::{BTreeMap, BTreeSet},
    env,
    ffi::OsStr,
    fs::{self, File},
    io::{self, Write},
    path::{Path, PathBuf},
};

use crown_artifact_inventory::{
    analyze_json_claims, analyze_rust_source, JsonClaimCounts, RustCounts,
};

const CODE_CSV: &str = "2026-07-27-crown-code-counts.csv";
const SITE_CSV: &str = "2026-07-27-crown-site-conversion-rates.csv";
const JSON_CSV: &str = "2026-07-27-crown-json-claims.csv";

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

    let mut inventories = Vec::new();
    for name in original_names {
        inventories.push(inventory_program(
            &name,
            &original_root.join(&name),
            &transformed_root.join(&name),
        )?);
    }

    fs::create_dir_all(&out_dir)?;
    write_code_csv(&out_dir.join(CODE_CSV), &inventories)?;
    write_site_csv(&out_dir.join(SITE_CSV), &inventories)?;
    write_json_csv(&out_dir.join(JSON_CSV), &inventories)?;

    let partial: Vec<_> = inventories
        .iter()
        .filter(|row| {
            !row.rust_file_sets_match
                || !row.rust_parse_failures.is_empty()
                || !row.missing_json.is_empty()
        })
        .map(|row| row.name.as_str())
        .collect();
    println!("programs={}", inventories.len());
    println!("directory_names_match=true");
    println!(
        "partial_or_failed={}",
        if partial.is_empty() {
            "none".to_owned()
        } else {
            partial.join(";")
        }
    );
    for name in [CODE_CSV, SITE_CSV, JSON_CSV] {
        println!("{}", out_dir.join(name).display());
    }
    Ok(())
}

fn inventory_program(
    name: &str,
    original_dir: &Path,
    transformed_dir: &Path,
) -> Result<ProgramInventory, Box<dyn std::error::Error>> {
    let original_files = rust_files(original_dir)?;
    let transformed_files = rust_files(transformed_dir)?;
    let original_rel = relative_set(original_dir, &original_files);
    let transformed_rel = relative_set(transformed_dir, &transformed_files);
    let mut rust_parse_failures = Vec::new();
    let original = inventory_rust_files(original_dir, &original_files, &mut rust_parse_failures)?;
    let transformed = inventory_rust_files(
        transformed_dir,
        &transformed_files,
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
    })
}

fn inventory_rust_files(
    root: &Path,
    files: &[PathBuf],
    failures: &mut Vec<String>,
) -> io::Result<RustCounts> {
    let mut total = RustCounts::default();
    for path in files {
        let source = fs::read_to_string(path)?;
        match analyze_rust_source(&source) {
            Ok(counts) => total.merge(counts),
            Err(error) => failures.push(format!(
                "{}:{}",
                path.strip_prefix(root).unwrap_or(path).display(),
                error
            )),
        }
    }
    Ok(total)
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
        "program,artifact_status,original_rust_files,transformed_rust_files,rust_file_sets_match,rust_parse_failures,missing_json_files,local_Box,local_Option_Box,param_Box,param_Option_Box,return_Box,return_Option_Box,field_Box,field_Option_Box,box_family_type_positions,Box_new_calls,Box_from_raw_calls,Box_into_raw_calls,remaining_raw_malloc,remaining_raw_calloc,remaining_raw_realloc,remaining_raw_free,explicit_drop_calls"
    )?;
    for row in rows {
        writeln!(
            out,
            "{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{},{}",
            row.name,
            status(row),
            row.original_rust_files,
            row.transformed_rust_files,
            row.rust_file_sets_match,
            row.rust_parse_failures.len(),
            row.missing_json.len(),
            row.transformed.types.local_box,
            row.transformed.types.local_option_box,
            row.transformed.types.param_box,
            row.transformed.types.param_option_box,
            row.transformed.types.return_box,
            row.transformed.types.return_option_box,
            row.transformed.types.field_box,
            row.transformed.types.field_option_box,
            row.transformed.box_type_positions(),
            row.transformed.box_new_calls,
            row.transformed.box_from_raw_calls,
            row.transformed.box_into_raw_calls,
            row.transformed.malloc_calls,
            row.transformed.calloc_calls,
            row.transformed.realloc_calls,
            row.transformed.free_calls,
            row.transformed.drop_calls,
        )?;
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
        "program,max_pointer_depth_levels,ownership_fn_d0_Owning,ownership_fn_d0_Transient,ownership_fn_d0_Unknown,ownership_fn_d1_Owning,ownership_fn_d1_Transient,ownership_fn_d1_Unknown,ownership_struct_d0_Owning,ownership_struct_d0_Transient,ownership_struct_d0_Unknown,ownership_struct_d1_Owning,ownership_struct_d1_Transient,ownership_struct_d1_Unknown,ownership_fn_Owning,ownership_fn_Transient,ownership_fn_Unknown,ownership_struct_Owning,ownership_struct_Transient,ownership_struct_Unknown,ownership_total_Owning,ownership_total_Transient,ownership_total_Unknown,mutability_fn_Mut,mutability_fn_Imm,mutability_struct_Mut,mutability_struct_Imm,fatness_fn_Arr,fatness_fn_Ptr,fatness_struct_Arr,fatness_struct_Ptr,num_unsafe_ptrs,num_non_arr_unsafe_ptrs,num_mut_unsafe_ptrs,num_non_arr_mut_unsafe_ptrs,num_unsafe_usages,num_non_arr_unsafe_usages,num_mut_unsafe_usages,num_non_arr_mut_unsafe_usages,num_owning_ptrs_detected"
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
        ];
        writeln!(out, "{}", values.join(","))?;
    }
    Ok(())
}

fn status(row: &ProgramInventory) -> &'static str {
    if row.rust_file_sets_match && row.rust_parse_failures.is_empty() && row.missing_json.is_empty()
    {
        "ok"
    } else {
        "partial"
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
