#![allow(non_snake_case)]

use std::{
    collections::BTreeMap,
    env, fs,
    path::{Path, PathBuf},
    sync::{
        Mutex, OnceLock,
        atomic::{AtomicUsize, Ordering},
    },
    time::{SystemTime, UNIX_EPOCH},
};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{ItemKind, OwnerNode, def_id::DefId};
use rustc_middle::{
    mir::{Local, VarDebugInfoContents},
    ty::TyCtxt,
};
use rustc_span::def_id::LocalDefId;
use similar::TextDiff;

use crate::{
    analyses::{
        output_params::compute_output_params,
        ownership::{
            AnalysisKind, CrateCtxt, Ownership, Param,
            ssa::AnalysisResults,
            whole_program::{WholeProgramAnalysis, WholeProgramResults},
        },
        type_qualifier::foster::mutability::mutability_analysis,
    },
    utils::rustc::RustProgram,
};

fn run_compiler<F: FnOnce(TyCtxt<'_>) + Send>(code: &str, f: F) {
    ::utils::compilation::run_compiler_on_str(code, f).unwrap_or_else(|e| e.raise());
}

fn collect_program(tcx: TyCtxt<'_>) -> RustProgram<'_> {
    let mut functions = Vec::new();
    let mut structs = Vec::new();

    for maybe_owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let OwnerNode::Item(item) = owner.node() else {
            continue;
        };

        match item.kind {
            ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
            ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
            _ => {}
        }
    }

    RustProgram {
        tcx,
        functions,
        structs,
    }
}

fn analyze_program<'tcx>(program: &RustProgram<'tcx>) -> WholeProgramResults<'tcx> {
    let mutability_result = mutability_analysis(program);
    let aliases: FxHashMap<LocalDefId, FxHashMap<Local, FxHashSet<Local>>> = FxHashMap::default();
    let output_params = compute_output_params(program, &mutability_result, &aliases);
    let crate_ctxt = CrateCtxt::new(program);

    <WholeProgramAnalysis as AnalysisKind>::analyze(crate_ctxt, &output_params)
        .expect("ownership analysis should succeed")
}

pub(super) fn run_ownership_case(case_name: &str, code: &str) {
    run_compiler(code, |tcx| {
        let program = collect_program(tcx);
        let results = analyze_program(&program);
        let fns = program
            .functions
            .iter()
            .map(|did| did.to_def_id())
            .collect::<Vec<DefId>>();

        println!("== {case_name} ==");
        results.print_fn_sigs(program.tcx, &fns);
    });
}

pub(super) fn run_ownership_case_with_assertions(case_name: &str, code: &str) {
    run_compiler(code, |tcx| {
        let program = collect_program(tcx);
        let results = analyze_program(&program);
        let fns = program
            .functions
            .iter()
            .map(|did| did.to_def_id())
            .collect::<Vec<DefId>>();

        assert!(
            !fns.is_empty(),
            "case `{case_name}` should define at least one function"
        );

        let mut pointer_like_slots = 0usize;
        let mut output_slots = 0usize;
        let mut owning_tops = 0usize;

        for did in fns {
            let fn_path = program.tcx.def_path_str(did);
            let fn_sig = tcx.fn_sig(did).skip_binder();
            let mut expected_tys = Vec::with_capacity(fn_sig.inputs().skip_binder().len() + 1);
            expected_tys.push(fn_sig.output().skip_binder());
            expected_tys.extend(fn_sig.inputs().skip_binder().iter().copied());

            let observed = results.fn_sig(did).collect::<Vec<_>>();

            assert_eq!(
                observed.len(),
                expected_tys.len(),
                "signature arity mismatch for `{}` in case `{}`",
                fn_path,
                case_name
            );

            assert!(
                results.fn_results(did).is_some(),
                "missing per-function analysis results for `{}` in case `{}`",
                fn_path,
                case_name
            );

            for (slot_idx, (observed_slot, expected_ty)) in observed
                .into_iter()
                .zip(expected_tys.into_iter())
                .enumerate()
            {
                let is_pointer_like =
                    expected_ty.is_raw_ptr() || expected_ty.is_ref() || expected_ty.is_box();

                if !is_pointer_like {
                    continue;
                }

                pointer_like_slots += 1;

                let observed_slot = observed_slot.unwrap_or_else(|| {
                    panic!(
                        "expected ownership qualifiers for pointer-like slot {} of `{}` in case `{}`",
                        slot_idx, fn_path, case_name
                    )
                });

                match observed_slot {
                    Param::Normal(quals) => {
                        assert!(
                            !quals.is_empty(),
                            "empty qualifier slice for slot {} of `{}` in case `{}`",
                            slot_idx,
                            fn_path,
                            case_name
                        );
                        assert_ne!(
                            quals[0],
                            Ownership::Unknown,
                            "top-level qualifier is unknown for slot {} of `{}` in case `{}`",
                            slot_idx,
                            fn_path,
                            case_name
                        );
                        if quals[0] == Ownership::Owning {
                            owning_tops += 1;
                        }
                    }
                    Param::Output(output) => {
                        output_slots += 1;
                        assert_eq!(
                            output.r#use.len(),
                            output.def.len(),
                            "output use/def arity mismatch for slot {} of `{}` in case `{}`",
                            slot_idx,
                            fn_path,
                            case_name
                        );
                        assert!(
                            !output.r#use.is_empty(),
                            "empty output qualifiers for slot {} of `{}` in case `{}`",
                            slot_idx,
                            fn_path,
                            case_name
                        );
                        assert_ne!(
                            output.r#use[0],
                            Ownership::Unknown,
                            "unknown output-use qualifier for slot {} of `{}` in case `{}`",
                            slot_idx,
                            fn_path,
                            case_name
                        );
                        assert_ne!(
                            output.def[0],
                            Ownership::Unknown,
                            "unknown output-def qualifier for slot {} of `{}` in case `{}`",
                            slot_idx,
                            fn_path,
                            case_name
                        );
                        assert_eq!(
                            output.r#use[0],
                            Ownership::Owning,
                            "mutable/output slot {} of `{}` should be owning at input in case `{}`",
                            slot_idx,
                            fn_path,
                            case_name
                        );
                        assert_eq!(
                            output.def[0],
                            Ownership::Owning,
                            "mutable/output slot {} of `{}` should be owning at output in case `{}`",
                            slot_idx,
                            fn_path,
                            case_name
                        );
                        owning_tops += 1;
                    }
                }
            }
        }

        if code.contains("*mut") || code.contains("*const") || code.contains("&mut ") {
            assert!(
                pointer_like_slots > 0,
                "case `{case_name}` has pointer syntax but no pointer-like slots were analyzed"
            );
        }

        if code.contains("malloc(")
            || code.contains("calloc(")
            || code.contains("realloc(")
            || code.contains("strdup(")
        {
            assert!(
                owning_tops > 0,
                "case `{case_name}` allocates memory but analysis reported no owning top-level qualifiers"
            );
        }

        if code.contains("*mut") {
            assert!(
                output_slots > 0 || owning_tops > 0,
                "case `{case_name}` has mutable pointers but produced no strong ownership evidence"
            );
        }
    });
}

fn collect_raw_ptr_local_ownership<'tcx>(
    program: &RustProgram<'tcx>,
    results: &WholeProgramResults<'tcx>,
) -> FxHashMap<(String, String), bool> {
    let mut by_scoped_name: FxHashMap<(String, String), bool> = FxHashMap::default();
    let solidified = results.solidify(program);

    for local_did in &program.functions {
        let did = local_did.to_def_id();
        let body = program.tcx.optimized_mir(did);
        let fn_path = program.tcx.def_path_str(did);
        let fn_results = solidified.fn_results(&did);
        for debug_info in &body.var_debug_info {
            let VarDebugInfoContents::Place(place) = &debug_info.value else {
                continue;
            };
            let Some(local) = place.as_local() else {
                continue;
            };
            if !body.local_decls[local].ty.is_raw_ptr() {
                continue;
            }

            let is_owning = fn_results
                .local_result(local)
                .first()
                .is_some_and(Ownership::is_owning);
            let name = debug_info.name.as_str().to_owned();
            by_scoped_name
                .entry((fn_path.clone(), name))
                .and_modify(|owning| *owning = *owning || is_owning)
                .or_insert(is_owning);
        }
    }

    by_scoped_name
}

#[derive(Default)]
struct TotalB02Stats {
    case_count: usize,
    fn_count: usize,
    precision_sum: usize,
    precision_samples: usize,
    precision_min: Option<u8>,
    precision_max: Option<u8>,
    raw_ptr_total: usize,
    raw_ptr_owning: usize,
    allocator_related_total: usize,
    allocator_related_owning: usize,
    checks_pos: usize,
    checks_neg: usize,
}

const EXPECTED_B02_CASES: usize = 86;
static B02_CASE_COUNTER: AtomicUsize = AtomicUsize::new(0);
static TOTAL_B02_STATS: OnceLock<Mutex<TotalB02Stats>> = OnceLock::new();

fn record_total_analysis_stats(
    program: &RustProgram<'_>,
    results: &WholeProgramResults<'_>,
    by_scoped_name: &FxHashMap<(String, String), bool>,
    owning_names: &[String],
    allocator_related_candidates: &[String],
    expected_box_candidates: &[String],
    expected_non_candidates: &[String],
) {
    let precisions = program
        .functions
        .iter()
        .map(|did| results.precision(&did.to_def_id()))
        .collect::<Vec<_>>();
    let fn_count = precisions.len();
    let precision_sum = precisions.iter().map(|&p| p as usize).sum::<usize>();
    let (precision_min, precision_max) = if precisions.is_empty() {
        (0u8, 0u8)
    } else {
        let min = *precisions.iter().min().unwrap();
        let max = *precisions.iter().max().unwrap();
        (min, max)
    };

    let raw_ptr_total = by_scoped_name.len();
    let raw_ptr_owning = owning_names.len();

    let owning_set: FxHashSet<&str> = owning_names.iter().map(String::as_str).collect();
    let alloc_total = allocator_related_candidates.len();
    let alloc_owning = allocator_related_candidates
        .iter()
        .filter(|name| owning_set.contains(name.as_str()))
        .count();

    let stats_lock = TOTAL_B02_STATS.get_or_init(|| Mutex::new(TotalB02Stats::default()));
    let mut stats = stats_lock.lock().expect("global B02 stats mutex poisoned");

    stats.case_count += 1;
    stats.fn_count += fn_count;
    stats.precision_sum += precision_sum;
    stats.precision_samples += fn_count;
    if fn_count > 0 {
        stats.precision_min = Some(match stats.precision_min {
            Some(v) => v.min(precision_min),
            None => precision_min,
        });
        stats.precision_max = Some(match stats.precision_max {
            Some(v) => v.max(precision_max),
            None => precision_max,
        });
    }
    stats.raw_ptr_total += raw_ptr_total;
    stats.raw_ptr_owning += raw_ptr_owning;
    stats.allocator_related_total += alloc_total;
    stats.allocator_related_owning += alloc_owning;
    stats.checks_pos += expected_box_candidates.len();
    stats.checks_neg += expected_non_candidates.len();

    let processed = B02_CASE_COUNTER.fetch_add(1, Ordering::SeqCst) + 1;
    if processed == EXPECTED_B02_CASES {
        let precision_avg = if stats.precision_samples == 0 {
            0.0
        } else {
            stats.precision_sum as f64 / stats.precision_samples as f64
        };
        println!(
            "== B02 total stats == cases={}, fns={}, precision[min/avg/max]={}/{:.2}/{}, raw_ptrs[owning/total]={}/{}, allocator_related[owning/total]={}/{}, checks[pos/neg]={}/{}",
            stats.case_count,
            stats.fn_count,
            stats.precision_min.unwrap_or(0),
            precision_avg,
            stats.precision_max.unwrap_or(0),
            stats.raw_ptr_owning,
            stats.raw_ptr_total,
            stats.allocator_related_owning,
            stats.allocator_related_total,
            stats.checks_pos,
            stats.checks_neg,
        );
    }
}

fn find_assignment_eq(stmt: &str) -> Option<usize> {
    let bytes = stmt.as_bytes();
    for i in 0..bytes.len() {
        if bytes[i] != b'=' {
            continue;
        }
        let prev = i.checked_sub(1).map(|idx| bytes[idx]);
        let next = bytes.get(i + 1).copied();
        let is_cmp = matches!(prev, Some(b'=') | Some(b'!') | Some(b'<') | Some(b'>'))
            || matches!(next, Some(b'='));
        if !is_cmp {
            return Some(i);
        }
    }
    None
}

fn parse_fn_name(line: &str) -> Option<String> {
    let fn_idx = line.find("fn ")?;
    let rest = &line[fn_idx + 3..];
    let end = rest.find('(')?;
    let name = rest[..end].trim();
    if name.is_empty() {
        None
    } else {
        Some(name.to_owned())
    }
}

fn parse_ptr_local_decl_name(stmt: &str) -> Option<String> {
    let stmt = stmt.trim_start();
    let rest = stmt.strip_prefix("let ")?;
    let rest = rest.strip_prefix("mut ").unwrap_or(rest);

    if !(rest.contains(": *mut") || rest.contains(":*mut")) {
        return None;
    }

    let end = rest
        .find(|c: char| c == ':' || c.is_whitespace() || c == '=')
        .unwrap_or(rest.len());
    let name = rest[..end].trim();
    if name.is_empty() {
        None
    } else {
        Some(name.to_owned())
    }
}

fn is_simple_ident(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if !(first == '_' || first.is_ascii_alphabetic()) {
        return false;
    }
    chars.all(|c| c == '_' || c.is_ascii_alphanumeric())
}

fn is_ident_char_byte(b: u8) -> bool {
    b == b'_' || b.is_ascii_alphanumeric()
}

fn contains_direct_call(text: &str, callee: &str) -> bool {
    let pattern = format!("{callee}(");
    let mut offset = 0usize;
    let bytes = text.as_bytes();

    while let Some(pos) = text[offset..].find(&pattern) {
        let idx = offset + pos;
        let has_ident_prefix = idx > 0 && is_ident_char_byte(bytes[idx - 1]);
        if !has_ident_prefix {
            return true;
        }
        offset = idx + 1;
    }
    false
}

fn has_allocator_call(text: &str) -> bool {
    ["malloc", "calloc", "realloc", "strdup"]
        .iter()
        .any(|callee| contains_direct_call(text, callee))
}

fn extract_allocator_related_ptr_locals(code: &str) -> Vec<(String, String)> {
    let mut out = Vec::new();

    let mut brace_depth: i32 = 0;
    let mut current_fn: Option<String> = None;
    let mut fn_start_depth: i32 = 0;
    let mut fn_body_started = false;

    let mut ptr_locals_in_fn: FxHashSet<String> = FxHashSet::default();
    let mut stmt_buf = String::new();

    let flush_statement = |stmt: &str,
                           current_fn: &Option<String>,
                           ptr_locals_in_fn: &mut FxHashSet<String>,
                           out: &mut Vec<(String, String)>| {
        let stmt = stmt.replace('\n', " ");
        let stmt = stmt.trim();
        if stmt.is_empty() {
            return;
        }

        if let Some(local) = parse_ptr_local_decl_name(stmt) {
            ptr_locals_in_fn.insert(local.clone());
            if has_allocator_call(stmt) {
                if let Some(fn_name) = current_fn {
                    out.push((fn_name.clone(), local));
                }
            }
        }

        if !has_allocator_call(stmt) {
            return;
        }

        let Some(eq_idx) = find_assignment_eq(stmt) else {
            return;
        };
        let lhs = stmt[..eq_idx].trim();
        let lhs = lhs.trim_start_matches(|c: char| c == '}' || c.is_whitespace());
        let lhs = lhs
            .rsplit(|c: char| c.is_whitespace() || c == '{' || c == '}')
            .next()
            .unwrap_or(lhs)
            .trim();
        if lhs.starts_with("let ") {
            return;
        }
        if !is_simple_ident(lhs) {
            return;
        }
        if let Some(fn_name) = current_fn {
            out.push((fn_name.clone(), lhs.to_owned()));
        }
    };

    for line in code.lines() {
        if current_fn.is_none() {
            if let Some(fn_name) = parse_fn_name(line) {
                current_fn = Some(fn_name);
                fn_start_depth = brace_depth;
                fn_body_started = false;
                ptr_locals_in_fn.clear();
                stmt_buf.clear();
            }
        }

        if current_fn.is_some() {
            stmt_buf.push_str(line);
            stmt_buf.push('\n');

            while let Some(semi_idx) = stmt_buf.find(';') {
                let stmt = stmt_buf[..semi_idx].to_owned();
                flush_statement(&stmt, &current_fn, &mut ptr_locals_in_fn, &mut out);
                let remainder = stmt_buf[semi_idx + 1..].to_owned();
                stmt_buf = remainder;
            }
        }

        for c in line.chars() {
            match c {
                '{' => brace_depth += 1,
                '}' => brace_depth -= 1,
                _ => {}
            }
        }

        if current_fn.is_some() && !fn_body_started && line.trim_end().ends_with(';') {
            stmt_buf.clear();
            ptr_locals_in_fn.clear();
            current_fn = None;
            fn_body_started = false;
            continue;
        }

        if current_fn.is_some() && !fn_body_started && brace_depth > fn_start_depth {
            fn_body_started = true;
        }

        if current_fn.is_some() && fn_body_started && brace_depth <= fn_start_depth {
            if !stmt_buf.trim().is_empty() {
                flush_statement(&stmt_buf, &current_fn, &mut ptr_locals_in_fn, &mut out);
            }
            stmt_buf.clear();
            ptr_locals_in_fn.clear();
            current_fn = None;
            fn_body_started = false;
        }
    }

    out.sort();
    out.dedup();
    out
}

#[derive(Debug, Clone)]
struct AllocatorOriginRewrite {
    function: String,
    local: String,
    allocator: String,
    before_stmt: String,
    after_stmt: Option<String>,
    rewrite_kind: String,
}

fn normalize_stmt(stmt: &str) -> String {
    stmt.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn parse_decl_local_name(stmt: &str) -> Option<String> {
    let stmt = stmt.trim_start();
    for (idx, _) in stmt.rmatch_indices("let ") {
        let has_ident_prefix = idx > 0 && is_ident_char_byte(stmt.as_bytes()[idx - 1]);
        if has_ident_prefix {
            continue;
        }
        let rest = &stmt[idx + "let ".len()..];
        let rest = rest.trim_start();
        let rest = rest.strip_prefix("mut ").unwrap_or(rest);
        let end = rest
            .find(|c: char| c == ':' || c.is_whitespace() || c == '=')
            .unwrap_or(rest.len());
        let name = rest[..end].trim();
        if is_simple_ident(name) {
            return Some(name.to_owned());
        }
    }
    None
}

fn parse_assignment_lhs_name(stmt: &str) -> Option<String> {
    let eq_idx = find_assignment_eq(stmt)?;
    let lhs = stmt[..eq_idx].trim();
    let lhs = lhs.trim_start_matches(|c: char| c == '}' || c.is_whitespace());
    let lhs = lhs
        .rsplit(|c: char| c.is_whitespace() || c == '{' || c == '}')
        .next()
        .unwrap_or(lhs)
        .trim();
    if lhs.starts_with("let ") || !is_simple_ident(lhs) {
        return None;
    }
    Some(lhs.to_owned())
}

fn parse_assigned_local_name(stmt: &str) -> Option<String> {
    parse_decl_local_name(stmt).or_else(|| parse_assignment_lhs_name(stmt))
}

fn extract_allocator_callee(stmt: &str) -> Option<&'static str> {
    ["malloc", "calloc", "realloc", "strdup"]
        .iter()
        .copied()
        .find(|callee| contains_direct_call(stmt, callee))
}

fn collect_fn_statements(code: &str) -> Vec<(String, String)> {
    let mut statements = Vec::new();

    let mut brace_depth: i32 = 0;
    let mut current_fn: Option<String> = None;
    let mut fn_start_depth: i32 = 0;
    let mut fn_body_started = false;
    let mut stmt_buf = String::new();

    let mut push_stmt = |fn_name: &str, stmt: &str| {
        let normalized = normalize_stmt(stmt);
        if !normalized.is_empty() {
            statements.push((fn_name.to_owned(), normalized));
        }
    };

    for line in code.lines() {
        if current_fn.is_none() {
            if let Some(fn_name) = parse_fn_name(line) {
                current_fn = Some(fn_name);
                fn_start_depth = brace_depth;
                fn_body_started = false;
                stmt_buf.clear();
            }
        }

        if let Some(fn_name) = current_fn.as_ref() {
            stmt_buf.push_str(line);
            stmt_buf.push('\n');
            while let Some(semi_idx) = stmt_buf.find(';') {
                let stmt = stmt_buf[..semi_idx].to_owned();
                push_stmt(fn_name, &stmt);
                stmt_buf = stmt_buf[semi_idx + 1..].to_owned();
            }
        }

        for c in line.chars() {
            match c {
                '{' => brace_depth += 1,
                '}' => brace_depth -= 1,
                _ => {}
            }
        }

        if current_fn.is_some() && !fn_body_started && line.trim_end().ends_with(';') {
            stmt_buf.clear();
            current_fn = None;
            fn_body_started = false;
            continue;
        }

        if current_fn.is_some() && !fn_body_started && brace_depth > fn_start_depth {
            fn_body_started = true;
        }

        if current_fn.is_some() && fn_body_started && brace_depth <= fn_start_depth {
            if let Some(fn_name) = current_fn.as_ref() {
                if !stmt_buf.trim().is_empty() {
                    push_stmt(fn_name, &stmt_buf);
                }
            }
            stmt_buf.clear();
            current_fn = None;
            fn_body_started = false;
        }
    }

    statements
}

fn classify_allocator_origin_rewrite(after_stmt: Option<&str>) -> &'static str {
    let Some(stmt) = after_stmt else {
        return "missing_after_assignment";
    };
    if contains_direct_call(stmt, "malloc")
        || contains_direct_call(stmt, "calloc")
        || contains_direct_call(stmt, "realloc")
        || contains_direct_call(stmt, "strdup")
    {
        return "allocator_call_preserved";
    }
    if contains_direct_call(stmt, "Box::new") {
        return "rewritten_to_box_new";
    }
    if contains_direct_call(stmt, "Box::from_raw") {
        return "rewritten_to_box_from_raw";
    }
    if contains_direct_call(stmt, "Box::into_raw") {
        return "rewritten_to_box_into_raw";
    }
    "rewritten_other"
}

fn collect_allocator_origin_rewrites(
    before_code: &str,
    after_code: &str,
) -> Vec<AllocatorOriginRewrite> {
    let before_statements = collect_fn_statements(before_code);
    let after_statements = collect_fn_statements(after_code);

    let mut after_index: BTreeMap<(String, String), String> = BTreeMap::new();
    for (function, stmt) in after_statements {
        let Some(local) = parse_assigned_local_name(&stmt) else {
            continue;
        };
        after_index.entry((function, local)).or_insert(stmt);
    }

    let mut rewrites = Vec::new();
    for (function, stmt) in before_statements {
        let Some(allocator) = extract_allocator_callee(&stmt) else {
            continue;
        };
        let Some(local) = parse_assigned_local_name(&stmt) else {
            continue;
        };
        let after_stmt = after_index.get(&(function.clone(), local.clone())).cloned();
        let rewrite_kind = classify_allocator_origin_rewrite(after_stmt.as_deref()).to_owned();
        rewrites.push(AllocatorOriginRewrite {
            function,
            local,
            allocator: allocator.to_owned(),
            before_stmt: stmt,
            after_stmt,
            rewrite_kind,
        });
    }

    rewrites.sort_by(|lhs, rhs| {
        lhs.function
            .cmp(&rhs.function)
            .then(lhs.local.cmp(&rhs.local))
            .then(lhs.allocator.cmp(&rhs.allocator))
            .then(lhs.before_stmt.cmp(&rhs.before_stmt))
    });
    rewrites
}

fn filter_allocator_origin_rewrites_for_dump(
    rewrites: Vec<AllocatorOriginRewrite>,
) -> Vec<AllocatorOriginRewrite> {
    rewrites
        .into_iter()
        .filter(|rewrite| {
            ALLOCATOR_ORIGIN_DUMP_FILTER
                .iter()
                .any(|callee| rewrite.allocator == *callee)
        })
        .collect()
}

fn render_allocator_origin_rewrites(
    case_name: &str,
    rewrites: &[AllocatorOriginRewrite],
) -> String {
    let mut out = String::new();
    out.push_str(&format!("case={case_name}\n"));
    out.push_str(&format!("allocator_origin_sites={}\n", rewrites.len()));

    for (idx, rewrite) in rewrites.iter().enumerate() {
        out.push_str(&format!(
            "\n[{idx}] fn={} local={} allocator={} rewrite={}\n",
            rewrite.function, rewrite.local, rewrite.allocator, rewrite.rewrite_kind
        ));
        out.push_str(&format!("before: {}\n", rewrite.before_stmt));
        out.push_str(&format!(
            "after: {}\n",
            rewrite.after_stmt.as_deref().unwrap_or("<missing>")
        ));
    }

    out
}

fn extract_b02_source_from_file(path: &Path) -> Option<String> {
    let content = fs::read_to_string(path).ok()?;
    let start_marker = "const SOURCE: &str = r####\"";
    let start = content.find(start_marker)?;
    let rest = &content[start + start_marker.len()..];
    let end = rest.find("\"####;")?;
    Some(rest[..end].to_owned())
}

fn merge_count_maps(dst: &mut BTreeMap<String, usize>, src: &BTreeMap<String, usize>) {
    for (callee, count) in src {
        *dst.entry(callee.clone()).or_default() += *count;
    }
}

fn merge_nested_count_maps(
    dst: &mut BTreeMap<String, BTreeMap<String, usize>>,
    src: &BTreeMap<String, BTreeMap<String, usize>>,
) {
    for (outer, inner_map) in src {
        let dst_inner = dst.entry(outer.clone()).or_default();
        for (inner, count) in inner_map {
            *dst_inner.entry(inner.clone()).or_default() += *count;
        }
    }
}

fn sum_count_map(map: &BTreeMap<String, usize>) -> usize {
    map.values().sum()
}

fn format_counts_by_callee(map: &BTreeMap<String, usize>, fixed_order: &[&str]) -> String {
    let mut parts = Vec::new();
    for &callee in fixed_order {
        parts.push(format!(
            "{}={}",
            callee,
            map.get(callee).copied().unwrap_or(0)
        ));
    }
    for (callee, count) in map {
        if !fixed_order.iter().any(|known| *known == callee.as_str()) {
            parts.push(format!("{callee}={count}"));
        }
    }
    parts.join(", ")
}

fn format_counts(map: &BTreeMap<String, usize>) -> String {
    map.iter()
        .map(|(key, count)| format!("{key}={count}"))
        .collect::<Vec<_>>()
        .join(", ")
}

fn allocator_origin_filter_label() -> String {
    ALLOCATOR_ORIGIN_DUMP_FILTER.join(",")
}

fn ratio_percent(numer: usize, denom: usize) -> f64 {
    if denom == 0 {
        0.0
    } else {
        numer as f64 * 100.0 / denom as f64
    }
}

fn sum_selected_callees(map: &BTreeMap<String, usize>, callees: &[&str]) -> usize {
    callees
        .iter()
        .map(|callee| map.get(*callee).copied().unwrap_or(0))
        .sum()
}

const B02_DUMP_ENV: &str = "POINTER_REPLACER_B02_DUMP";
const B02_DUMP_RUN_ID_ENV: &str = "POINTER_REPLACER_B02_DUMP_RUN_ID";
const ALLOCATOR_ORIGIN_DUMP_FILTER: [&str; 2] = ["malloc", "calloc"];
const BOX_UNSAFE_CALLEES: [&str; 2] = ["Box::from_raw", "Box::into_raw"];

#[derive(Debug, Clone)]
struct B02DumpConfig {
    run_id: String,
    root: PathBuf,
}

#[derive(Debug, Clone)]
struct CaseRewriteStats {
    case_name: String,
    alloc_before: usize,
    alloc_after: usize,
    box_new_before: usize,
    box_new_after: usize,
    raw_unsafe_before: usize,
    raw_unsafe_after: usize,
    box_unsafe_before: usize,
    box_unsafe_after: usize,
    spec_call240_applied: usize,
    spec_call250_non_move_required: usize,
    spec_call240_compile_risk_default_missing: usize,
    rewrite_ok: bool,
    compile_ok: bool,
}

#[derive(Debug, Clone)]
struct CaseFailure {
    case_name: String,
    stage: &'static str,
    message: String,
}

fn parse_env_bool(value: &str) -> Option<bool> {
    match value.trim().to_ascii_lowercase().as_str() {
        "" | "0" | "false" | "no" | "off" => Some(false),
        "1" | "true" | "yes" | "on" => Some(true),
        _ => None,
    }
}

fn b02_dump_config_from_env() -> Option<B02DumpConfig> {
    let enabled = env::var(B02_DUMP_ENV)
        .ok()
        .as_deref()
        .and_then(parse_env_bool)
        .unwrap_or(false);
    if !enabled {
        return None;
    }

    let run_id = env::var(B02_DUMP_RUN_ID_ENV)
        .ok()
        .filter(|value| !value.trim().is_empty())
        .map(|value| sanitize_dump_component(value.trim()))
        .filter(|value| !value.is_empty())
        .unwrap_or_else(default_dump_run_id);

    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("spec/rewrite_dumps")
        .join(&run_id);
    Some(B02DumpConfig { run_id, root })
}

fn sanitize_dump_component(value: &str) -> String {
    value
        .chars()
        .map(|ch| {
            if ch.is_ascii_alphanumeric() || ch == '-' || ch == '_' || ch == '.' {
                ch
            } else {
                '_'
            }
        })
        .collect()
}

fn default_dump_run_id() -> String {
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default();
    format!("b02-{}-{}", now.as_secs(), std::process::id())
}

fn init_dump_root(config: &B02DumpConfig) {
    if config.root.exists() {
        fs::remove_dir_all(&config.root).unwrap_or_else(|e| {
            panic!("failed to clear dump root `{}`: {e}", config.root.display())
        });
    }
    fs::create_dir_all(config.root.join("cases")).unwrap_or_else(|e| {
        panic!(
            "failed to create dump root `{}`: {e}",
            config.root.display()
        )
    });
}

fn write_text_file(path: &Path, text: &str) {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).unwrap_or_else(|e| {
            panic!(
                "failed to create parent dir `{}` for dump artifact: {e}",
                parent.display()
            )
        });
    }
    fs::write(path, text)
        .unwrap_or_else(|e| panic!("failed to write dump artifact `{}`: {e}", path.display()));
}

fn render_unified_diff(before: &str, after: &str) -> String {
    TextDiff::from_lines(before, after)
        .unified_diff()
        .header("before.rs", "after.rs")
        .to_string()
}

fn case_dump_dir(root: &Path, case_name: &str) -> PathBuf {
    root.join("cases").join(case_name)
}

fn validate_case_rewrite_stats(
    case_name: &str,
    stats: &crate::rewriter::stats::RewriteStats,
) -> Result<(), String> {
    if stats.alloc_unsafe.before_total != sum_count_map(&stats.alloc_unsafe.before_by_callee) {
        return Err(format!(
            "allocator before-total mismatch in case `{case_name}`"
        ));
    }
    if stats.alloc_unsafe.after_total != sum_count_map(&stats.alloc_unsafe.after_by_callee) {
        return Err(format!(
            "allocator after-total mismatch in case `{case_name}`"
        ));
    }
    if stats.box_new.before_total != sum_count_map(&stats.box_new.before_by_callee) {
        return Err(format!(
            "Box::new before-total mismatch in case `{case_name}`"
        ));
    }
    if stats.box_new.after_total != sum_count_map(&stats.box_new.after_by_callee) {
        return Err(format!(
            "Box::new after-total mismatch in case `{case_name}`"
        ));
    }
    if stats.raw_constructor_unsafe.before_total
        != sum_count_map(&stats.raw_constructor_unsafe.before_by_callee)
    {
        return Err(format!(
            "raw-constructor before-total mismatch in case `{case_name}`"
        ));
    }
    if stats.raw_constructor_unsafe.after_total
        != sum_count_map(&stats.raw_constructor_unsafe.after_by_callee)
    {
        return Err(format!(
            "raw-constructor after-total mismatch in case `{case_name}`"
        ));
    }
    Ok(())
}

fn render_case_stats_file(row: &CaseRewriteStats) -> String {
    let alloc_removed = row.alloc_before.saturating_sub(row.alloc_after);
    let box_new_added = row.box_new_after.saturating_sub(row.box_new_before);
    let raw_unsafe_added = row.raw_unsafe_after.saturating_sub(row.raw_unsafe_before);
    let box_unsafe_added = row.box_unsafe_after.saturating_sub(row.box_unsafe_before);
    format!(
        "case={}\nrewrite_ok={}\ncompile_ok={}\nalloc_before={}\nalloc_after={}\nalloc_removed={}\nbox_new_before={}\nbox_new_after={}\nbox_new_added={}\nraw_unsafe_before={}\nraw_unsafe_after={}\nraw_unsafe_added={}\nbox_unsafe_before={}\nbox_unsafe_after={}\nbox_unsafe_added={}\nspec_call240_applied={}\nspec_call250_non_move_required={}\nspec_call240_compile_risk_default_missing={}\n",
        row.case_name,
        row.rewrite_ok,
        row.compile_ok,
        row.alloc_before,
        row.alloc_after,
        alloc_removed,
        row.box_new_before,
        row.box_new_after,
        box_new_added,
        row.raw_unsafe_before,
        row.raw_unsafe_after,
        raw_unsafe_added,
        row.box_unsafe_before,
        row.box_unsafe_after,
        box_unsafe_added,
        row.spec_call240_applied,
        row.spec_call250_non_move_required,
        row.spec_call240_compile_risk_default_missing,
    )
}

#[test]
fn rewriter_transformed_b02_cases_compile() {
    let dump_config = b02_dump_config_from_env();
    let dump_enabled = dump_config.is_some();
    if let Some(config) = &dump_config {
        init_dump_root(config);
        println!(
            "B02 rewrite dump enabled: run_id={} root={}",
            config.run_id,
            config.root.display()
        );
    }

    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("src/analyses/B02_tests");
    let mut files = fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("failed to read B02 dir `{}`: {e}", dir.display()))
        .filter_map(|entry| entry.ok().map(|e| e.path()))
        .filter(|path| {
            path.extension().is_some_and(|ext| ext == "rs")
                && path.file_name().is_some_and(|name| name != "mod.rs")
        })
        .collect::<Vec<_>>();
    files.sort();

    let mut source_cases = Vec::new();
    for path in files {
        let Some(source) = extract_b02_source_from_file(&path) else {
            continue;
        };
        let case_name = path
            .file_stem()
            .and_then(|stem| stem.to_str())
            .unwrap_or("<unknown>")
            .to_owned();
        source_cases.push((case_name, source));
    }

    assert_eq!(
        source_cases.len(),
        86,
        "expected 86 B02 SOURCE cases to compile-sweep"
    );

    let mut config = crate::Config::default();
    config.force_box = true;
    let mut case_rows = Vec::with_capacity(source_cases.len());
    let mut failures = Vec::<CaseFailure>::new();
    let mut allocator_origin_global = Vec::<(String, AllocatorOriginRewrite)>::new();

    let mut alloc_before_total = 0usize;
    let mut alloc_after_total = 0usize;
    let mut box_new_before_total = 0usize;
    let mut box_new_after_total = 0usize;
    let mut raw_unsafe_before_total = 0usize;
    let mut raw_unsafe_after_total = 0usize;
    let mut box_unsafe_before_total = 0usize;
    let mut box_unsafe_after_total = 0usize;
    let mut spec_reason_total: BTreeMap<String, usize> = BTreeMap::new();
    let mut spec_reason_by_allocator: BTreeMap<String, BTreeMap<String, usize>> = BTreeMap::new();

    let mut alloc_before_by_callee: BTreeMap<String, usize> = BTreeMap::new();
    let mut alloc_after_by_callee: BTreeMap<String, usize> = BTreeMap::new();
    let mut box_new_before_by_callee: BTreeMap<String, usize> = BTreeMap::new();
    let mut box_new_after_by_callee: BTreeMap<String, usize> = BTreeMap::new();
    let mut raw_unsafe_before_by_callee: BTreeMap<String, usize> = BTreeMap::new();
    let mut raw_unsafe_after_by_callee: BTreeMap<String, usize> = BTreeMap::new();
    let mut box_unsafe_before_by_callee: BTreeMap<String, usize> = BTreeMap::new();
    let mut box_unsafe_after_by_callee: BTreeMap<String, usize> = BTreeMap::new();

    for (case_name, source) in source_cases {
        let mut row = CaseRewriteStats {
            case_name: case_name.clone(),
            alloc_before: 0,
            alloc_after: 0,
            box_new_before: 0,
            box_new_after: 0,
            raw_unsafe_before: 0,
            raw_unsafe_after: 0,
            box_unsafe_before: 0,
            box_unsafe_after: 0,
            spec_call240_applied: 0,
            spec_call250_non_move_required: 0,
            spec_call240_compile_risk_default_missing: 0,
            rewrite_ok: false,
            compile_ok: false,
        };

        let case_dir = dump_config
            .as_ref()
            .map(|config| case_dump_dir(&config.root, &case_name));
        let rewrite_result = ::utils::compilation::run_compiler_on_str(&source, |tcx| {
            crate::rewriter::replace_local_borrows_with_stats(&config, tcx)
        });

        match rewrite_result {
            Err(e) => {
                let error_message = format!("rewriter crashed for B02 case `{case_name}`: {e:?}");
                failures.push(CaseFailure {
                    case_name: case_name.clone(),
                    stage: "rewrite",
                    message: error_message.clone(),
                });
                if let Some(case_dir) = &case_dir {
                    write_text_file(&case_dir.join("before.rs"), &source);
                    write_text_file(&case_dir.join("stats.txt"), &render_case_stats_file(&row));
                    write_text_file(&case_dir.join("error.txt"), &error_message);
                }
                if !dump_enabled {
                    panic!("{error_message}");
                }
                case_rows.push(row);
                continue;
            }
            Ok(output) => {
                row.rewrite_ok = true;
                let rewritten = output.code.clone();
                let stats = output.rewrite_stats.clone();
                let allocator_reason_stats = output.allocator_reason_stats.clone();
                let allocator_origin_rewrites = if dump_enabled {
                    let rewrites = filter_allocator_origin_rewrites_for_dump(
                        collect_allocator_origin_rewrites(
                            &output.before_code,
                            &output.after_core_code,
                        ),
                    );
                    for rewrite in &rewrites {
                        allocator_origin_global.push((case_name.clone(), rewrite.clone()));
                    }
                    Some(rewrites)
                } else {
                    None
                };

                row.alloc_before = stats.alloc_unsafe.before_total;
                row.alloc_after = stats.alloc_unsafe.after_total;
                row.box_new_before = stats.box_new.before_total;
                row.box_new_after = stats.box_new.after_total;
                row.raw_unsafe_before = stats.raw_constructor_unsafe.before_total;
                row.raw_unsafe_after = stats.raw_constructor_unsafe.after_total;
                row.box_unsafe_before =
                    sum_selected_callees(&stats.raw_constructor_unsafe.before_by_callee, &BOX_UNSAFE_CALLEES);
                row.box_unsafe_after =
                    sum_selected_callees(&stats.raw_constructor_unsafe.after_by_callee, &BOX_UNSAFE_CALLEES);
                row.spec_call240_applied = allocator_reason_stats
                    .reason_count(crate::rewriter::stats::AllocatorReason::Call240Applied);
                row.spec_call250_non_move_required = allocator_reason_stats
                    .reason_count(crate::rewriter::stats::AllocatorReason::Call250NonMoveRequired);
                row.spec_call240_compile_risk_default_missing = allocator_reason_stats
                    .reason_count(
                        crate::rewriter::stats::AllocatorReason::Call240CompileRiskDefaultMissing,
                    );

                let stats_validation_error = validate_case_rewrite_stats(&case_name, &stats).err();
                if let Some(message) = &stats_validation_error {
                    failures.push(CaseFailure {
                        case_name: case_name.clone(),
                        stage: "stats",
                        message: message.clone(),
                    });
                    if !dump_enabled {
                        panic!("{message}");
                    }
                } else {
                    alloc_before_total += stats.alloc_unsafe.before_total;
                    alloc_after_total += stats.alloc_unsafe.after_total;
                    box_new_before_total += stats.box_new.before_total;
                    box_new_after_total += stats.box_new.after_total;
                    raw_unsafe_before_total += stats.raw_constructor_unsafe.before_total;
                    raw_unsafe_after_total += stats.raw_constructor_unsafe.after_total;
                    box_unsafe_before_total += row.box_unsafe_before;
                    box_unsafe_after_total += row.box_unsafe_after;

                    merge_count_maps(
                        &mut alloc_before_by_callee,
                        &stats.alloc_unsafe.before_by_callee,
                    );
                    merge_count_maps(
                        &mut alloc_after_by_callee,
                        &stats.alloc_unsafe.after_by_callee,
                    );
                    merge_count_maps(
                        &mut box_new_before_by_callee,
                        &stats.box_new.before_by_callee,
                    );
                    merge_count_maps(&mut box_new_after_by_callee, &stats.box_new.after_by_callee);
                    merge_count_maps(
                        &mut raw_unsafe_before_by_callee,
                        &stats.raw_constructor_unsafe.before_by_callee,
                    );
                    merge_count_maps(
                        &mut raw_unsafe_after_by_callee,
                        &stats.raw_constructor_unsafe.after_by_callee,
                    );
                    for callee in BOX_UNSAFE_CALLEES {
                        let before = stats
                            .raw_constructor_unsafe
                            .before_by_callee
                            .get(callee)
                            .copied()
                            .unwrap_or(0);
                        let after = stats
                            .raw_constructor_unsafe
                            .after_by_callee
                            .get(callee)
                            .copied()
                            .unwrap_or(0);
                        *box_unsafe_before_by_callee
                            .entry(callee.to_owned())
                            .or_default() += before;
                        *box_unsafe_after_by_callee.entry(callee.to_owned()).or_default() +=
                            after;
                    }
                    merge_count_maps(&mut spec_reason_total, &allocator_reason_stats.by_reason);
                    merge_nested_count_maps(
                        &mut spec_reason_by_allocator,
                        &allocator_reason_stats.by_allocator,
                    );
                }

                let compile_error = ::utils::compilation::run_compiler_on_str(
                    &rewritten,
                    ::utils::type_check,
                )
                .err()
                .map(|_| {
                    format!(
                        "transformed code does not compile for B02 case `{case_name}`.\nTransformed:\n{}",
                        rewritten
                    )
                });
                row.compile_ok = compile_error.is_none();

                if let Some(message) = &compile_error {
                    failures.push(CaseFailure {
                        case_name: case_name.clone(),
                        stage: "compile",
                        message: message.clone(),
                    });
                    if !dump_enabled {
                        panic!("{message}");
                    }
                }

                if let Some(case_dir) = &case_dir {
                    write_text_file(&case_dir.join("before.rs"), &output.before_code);
                    write_text_file(&case_dir.join("after.rs"), &output.after_core_code);
                    write_text_file(&case_dir.join("after_full.rs"), &output.code);
                    if let Some(rewrites) = allocator_origin_rewrites.as_ref() {
                        write_text_file(
                            &case_dir.join("allocator_origin_rewrites.txt"),
                            &render_allocator_origin_rewrites(&case_name, rewrites),
                        );
                    }
                    write_text_file(
                        &case_dir.join("diff.patch"),
                        &render_unified_diff(&output.before_code, &output.after_core_code),
                    );
                    write_text_file(&case_dir.join("stats.txt"), &render_case_stats_file(&row));
                    if stats_validation_error.is_some() || compile_error.is_some() {
                        let mut errors = Vec::new();
                        if let Some(message) = stats_validation_error {
                            errors.push(message);
                        }
                        if let Some(message) = compile_error {
                            errors.push(message);
                        }
                        write_text_file(&case_dir.join("error.txt"), &errors.join("\n\n"));
                    }
                }

                case_rows.push(row);
            }
        }
    }

    case_rows.sort_by(|a, b| a.case_name.cmp(&b.case_name));

    let alloc_before_cases_sum = case_rows.iter().map(|row| row.alloc_before).sum::<usize>();
    let alloc_after_cases_sum = case_rows.iter().map(|row| row.alloc_after).sum::<usize>();
    let box_new_before_cases_sum = case_rows
        .iter()
        .map(|row| row.box_new_before)
        .sum::<usize>();
    let box_new_after_cases_sum = case_rows.iter().map(|row| row.box_new_after).sum::<usize>();
    let raw_unsafe_before_cases_sum = case_rows
        .iter()
        .map(|row| row.raw_unsafe_before)
        .sum::<usize>();
    let raw_unsafe_after_cases_sum = case_rows
        .iter()
        .map(|row| row.raw_unsafe_after)
        .sum::<usize>();
    let box_unsafe_before_cases_sum = case_rows
        .iter()
        .map(|row| row.box_unsafe_before)
        .sum::<usize>();
    let box_unsafe_after_cases_sum = case_rows
        .iter()
        .map(|row| row.box_unsafe_after)
        .sum::<usize>();

    if alloc_before_total != alloc_before_cases_sum {
        let message = format!(
            "allocator before total mismatch: aggregate={alloc_before_total} case_sum={alloc_before_cases_sum}"
        );
        failures.push(CaseFailure {
            case_name: "<aggregate>".to_owned(),
            stage: "invariant",
            message: message.clone(),
        });
        if !dump_enabled {
            panic!("{message}");
        }
    }
    if alloc_after_total != alloc_after_cases_sum {
        let message = format!(
            "allocator after total mismatch: aggregate={alloc_after_total} case_sum={alloc_after_cases_sum}"
        );
        failures.push(CaseFailure {
            case_name: "<aggregate>".to_owned(),
            stage: "invariant",
            message: message.clone(),
        });
        if !dump_enabled {
            panic!("{message}");
        }
    }
    if box_new_before_total != box_new_before_cases_sum {
        let message = format!(
            "Box::new before total mismatch: aggregate={box_new_before_total} case_sum={box_new_before_cases_sum}"
        );
        failures.push(CaseFailure {
            case_name: "<aggregate>".to_owned(),
            stage: "invariant",
            message: message.clone(),
        });
        if !dump_enabled {
            panic!("{message}");
        }
    }
    if box_new_after_total != box_new_after_cases_sum {
        let message = format!(
            "Box::new after total mismatch: aggregate={box_new_after_total} case_sum={box_new_after_cases_sum}"
        );
        failures.push(CaseFailure {
            case_name: "<aggregate>".to_owned(),
            stage: "invariant",
            message: message.clone(),
        });
        if !dump_enabled {
            panic!("{message}");
        }
    }
    if raw_unsafe_before_total != raw_unsafe_before_cases_sum {
        let message = format!(
            "raw-constructor before total mismatch: aggregate={raw_unsafe_before_total} case_sum={raw_unsafe_before_cases_sum}"
        );
        failures.push(CaseFailure {
            case_name: "<aggregate>".to_owned(),
            stage: "invariant",
            message: message.clone(),
        });
        if !dump_enabled {
            panic!("{message}");
        }
    }
    if raw_unsafe_after_total != raw_unsafe_after_cases_sum {
        let message = format!(
            "raw-constructor after total mismatch: aggregate={raw_unsafe_after_total} case_sum={raw_unsafe_after_cases_sum}"
        );
        failures.push(CaseFailure {
            case_name: "<aggregate>".to_owned(),
            stage: "invariant",
            message: message.clone(),
        });
        if !dump_enabled {
            panic!("{message}");
        }
    }
    if box_unsafe_before_total != box_unsafe_before_cases_sum {
        let message = format!(
            "box-unsafe before total mismatch: aggregate={box_unsafe_before_total} case_sum={box_unsafe_before_cases_sum}"
        );
        failures.push(CaseFailure {
            case_name: "<aggregate>".to_owned(),
            stage: "invariant",
            message: message.clone(),
        });
        if !dump_enabled {
            panic!("{message}");
        }
    }
    if box_unsafe_after_total != box_unsafe_after_cases_sum {
        let message = format!(
            "box-unsafe after total mismatch: aggregate={box_unsafe_after_total} case_sum={box_unsafe_after_cases_sum}"
        );
        failures.push(CaseFailure {
            case_name: "<aggregate>".to_owned(),
            stage: "invariant",
            message: message.clone(),
        });
        if !dump_enabled {
            panic!("{message}");
        }
    }

    if alloc_before_total != sum_count_map(&alloc_before_by_callee) {
        let message = "allocator before per-callee sum mismatch".to_owned();
        failures.push(CaseFailure {
            case_name: "<aggregate>".to_owned(),
            stage: "invariant",
            message: message.clone(),
        });
        if !dump_enabled {
            panic!("{message}");
        }
    }
    if alloc_after_total != sum_count_map(&alloc_after_by_callee) {
        let message = "allocator after per-callee sum mismatch".to_owned();
        failures.push(CaseFailure {
            case_name: "<aggregate>".to_owned(),
            stage: "invariant",
            message: message.clone(),
        });
        if !dump_enabled {
            panic!("{message}");
        }
    }
    if box_new_before_total != sum_count_map(&box_new_before_by_callee) {
        let message = "Box::new before per-callee sum mismatch".to_owned();
        failures.push(CaseFailure {
            case_name: "<aggregate>".to_owned(),
            stage: "invariant",
            message: message.clone(),
        });
        if !dump_enabled {
            panic!("{message}");
        }
    }
    if box_new_after_total != sum_count_map(&box_new_after_by_callee) {
        let message = "Box::new after per-callee sum mismatch".to_owned();
        failures.push(CaseFailure {
            case_name: "<aggregate>".to_owned(),
            stage: "invariant",
            message: message.clone(),
        });
        if !dump_enabled {
            panic!("{message}");
        }
    }
    if raw_unsafe_before_total != sum_count_map(&raw_unsafe_before_by_callee) {
        let message = "raw-constructor before per-callee sum mismatch".to_owned();
        failures.push(CaseFailure {
            case_name: "<aggregate>".to_owned(),
            stage: "invariant",
            message: message.clone(),
        });
        if !dump_enabled {
            panic!("{message}");
        }
    }
    if raw_unsafe_after_total != sum_count_map(&raw_unsafe_after_by_callee) {
        let message = "raw-constructor after per-callee sum mismatch".to_owned();
        failures.push(CaseFailure {
            case_name: "<aggregate>".to_owned(),
            stage: "invariant",
            message: message.clone(),
        });
        if !dump_enabled {
            panic!("{message}");
        }
    }
    if box_unsafe_before_total != sum_count_map(&box_unsafe_before_by_callee) {
        let message = "box-unsafe before per-callee sum mismatch".to_owned();
        failures.push(CaseFailure {
            case_name: "<aggregate>".to_owned(),
            stage: "invariant",
            message: message.clone(),
        });
        if !dump_enabled {
            panic!("{message}");
        }
    }
    if box_unsafe_after_total != sum_count_map(&box_unsafe_after_by_callee) {
        let message = "box-unsafe after per-callee sum mismatch".to_owned();
        failures.push(CaseFailure {
            case_name: "<aggregate>".to_owned(),
            stage: "invariant",
            message: message.clone(),
        });
        if !dump_enabled {
            panic!("{message}");
        }
    }

    let call240_applied_total = spec_reason_total
        .get("call240_applied")
        .copied()
        .unwrap_or(0);
    let call250_non_move_required_total = spec_reason_total
        .get("call250_non_move_required")
        .copied()
        .unwrap_or(0);
    let call240_scope_allocator_before_total =
        alloc_before_by_callee.get("malloc").copied().unwrap_or(0)
            + alloc_before_by_callee.get("calloc").copied().unwrap_or(0);

    if call240_applied_total > call240_scope_allocator_before_total {
        let message = format!(
            "spec reason invariant failed: call240_applied={} exceeds call240 scope before total={}",
            call240_applied_total, call240_scope_allocator_before_total
        );
        failures.push(CaseFailure {
            case_name: "<aggregate>".to_owned(),
            stage: "invariant",
            message: message.clone(),
        });
        if !dump_enabled {
            panic!("{message}");
        }
    }
    if call240_applied_total + call250_non_move_required_total
        > call240_scope_allocator_before_total
    {
        let message = format!(
            "spec reason invariant failed: call240_applied + call250_non_move_required = {} exceeds call240 scope before total={}",
            call240_applied_total + call250_non_move_required_total,
            call240_scope_allocator_before_total
        );
        failures.push(CaseFailure {
            case_name: "<aggregate>".to_owned(),
            stage: "invariant",
            message: message.clone(),
        });
        if !dump_enabled {
            panic!("{message}");
        }
    }

    let alloc_removed_total = alloc_before_total.saturating_sub(alloc_after_total);
    let box_new_added_total = box_new_after_total.saturating_sub(box_new_before_total);
    let raw_unsafe_added_total = raw_unsafe_after_total.saturating_sub(raw_unsafe_before_total);
    let box_unsafe_added_total = box_unsafe_after_total.saturating_sub(box_unsafe_before_total);

    println!("== B02 rewriter case-wise stats ==");
    for row in &case_rows {
        let alloc_removed = row.alloc_before.saturating_sub(row.alloc_after);
        let box_new_added = row.box_new_after.saturating_sub(row.box_new_before);
        let raw_unsafe_added = row.raw_unsafe_after.saturating_sub(row.raw_unsafe_before);
        let box_unsafe_added = row.box_unsafe_after.saturating_sub(row.box_unsafe_before);
        println!(
            "case={} rewrite_ok={} compile_ok={} alloc_before={} alloc_after={} alloc_removed={} box_new_before={} box_new_after={} box_new_added={} raw_unsafe_before={} raw_unsafe_after={} raw_unsafe_added={} box_unsafe_before={} box_unsafe_after={} box_unsafe_added={} spec_call240_applied={} spec_call250_non_move_required={} spec_call240_compile_risk_default_missing={}",
            row.case_name,
            row.rewrite_ok,
            row.compile_ok,
            row.alloc_before,
            row.alloc_after,
            alloc_removed,
            row.box_new_before,
            row.box_new_after,
            box_new_added,
            row.raw_unsafe_before,
            row.raw_unsafe_after,
            raw_unsafe_added,
            row.box_unsafe_before,
            row.box_unsafe_after,
            box_unsafe_added,
            row.spec_call240_applied,
            row.spec_call250_non_move_required,
            row.spec_call240_compile_risk_default_missing,
        );
    }

    let alloc_removal_rate = ratio_percent(alloc_removed_total, alloc_before_total);
    let box_new_growth_rate = if box_new_before_total == 0 {
        if box_new_after_total == 0 { 0.0 } else { 100.0 }
    } else {
        (box_new_after_total as f64 - box_new_before_total as f64) * 100.0
            / box_new_before_total as f64
    };
    let raw_unsafe_growth_rate = if raw_unsafe_before_total == 0 {
        if raw_unsafe_after_total == 0 {
            0.0
        } else {
            100.0
        }
    } else {
        (raw_unsafe_after_total as f64 - raw_unsafe_before_total as f64) * 100.0
            / raw_unsafe_before_total as f64
    };

    println!("== B02 rewriter totals ==");
    println!("cases={}", case_rows.len());
    println!(
        "allocator_unsafe_before_total={alloc_before_total} allocator_unsafe_after_total={alloc_after_total} allocator_unsafe_removed_total={alloc_removed_total}"
    );
    println!(
        "box_new_before_total={box_new_before_total} box_new_after_total={box_new_after_total} box_new_added_total={box_new_added_total}"
    );
    println!(
        "raw_constructor_unsafe_before_total={raw_unsafe_before_total} raw_constructor_unsafe_after_total={raw_unsafe_after_total} raw_constructor_unsafe_added_total={raw_unsafe_added_total}"
    );
    println!(
        "box_unsafe_before_total={box_unsafe_before_total} box_unsafe_after_total={box_unsafe_after_total} box_unsafe_added_total={box_unsafe_added_total}"
    );
    println!(
        "spec_reason_counts_total: {}",
        format_counts_by_callee(
            &spec_reason_total,
            &crate::rewriter::stats::ALLOCATOR_REASON_KEYS
        )
    );
    for (allocator, reason_counts) in &spec_reason_by_allocator {
        println!(
            "spec_reason_counts_by_allocator[{allocator}]: {}",
            format_counts_by_callee(
                reason_counts,
                &crate::rewriter::stats::ALLOCATOR_REASON_KEYS
            )
        );
    }
    println!(
        "allocator_removal_rate={alloc_removal_rate:.2}% box_new_growth_rate={box_new_growth_rate:.2}% raw_unsafe_growth_rate={raw_unsafe_growth_rate:.2}%"
    );
    println!(
        "allocator_unsafe_before_by_callee: {}",
        format_counts_by_callee(
            &alloc_before_by_callee,
            &crate::rewriter::stats::ALLOC_UNSAFE_CALLEES,
        )
    );
    println!(
        "allocator_unsafe_after_by_callee: {}",
        format_counts_by_callee(
            &alloc_after_by_callee,
            &crate::rewriter::stats::ALLOC_UNSAFE_CALLEES,
        )
    );
    println!(
        "box_new_before_by_callee: {}",
        format_counts_by_callee(
            &box_new_before_by_callee,
            &crate::rewriter::stats::BOX_NEW_CALLEES,
        )
    );
    println!(
        "box_new_after_by_callee: {}",
        format_counts_by_callee(
            &box_new_after_by_callee,
            &crate::rewriter::stats::BOX_NEW_CALLEES,
        )
    );
    println!(
        "raw_constructor_unsafe_before_by_callee: {}",
        format_counts_by_callee(
            &raw_unsafe_before_by_callee,
            &crate::rewriter::stats::RAW_CONSTRUCTOR_UNSAFE_CALLEES,
        )
    );
    println!(
        "raw_constructor_unsafe_after_by_callee: {}",
        format_counts_by_callee(
            &raw_unsafe_after_by_callee,
            &crate::rewriter::stats::RAW_CONSTRUCTOR_UNSAFE_CALLEES,
        )
    );
    println!(
        "box_unsafe_before_by_callee: {}",
        format_counts_by_callee(&box_unsafe_before_by_callee, &BOX_UNSAFE_CALLEES)
    );
    println!(
        "box_unsafe_after_by_callee: {}",
        format_counts_by_callee(&box_unsafe_after_by_callee, &BOX_UNSAFE_CALLEES)
    );

    if let Some(config) = &dump_config {
        let mut origin_sites = allocator_origin_global.clone();
        origin_sites.sort_by(|lhs, rhs| {
            lhs.0
                .cmp(&rhs.0)
                .then(lhs.1.function.cmp(&rhs.1.function))
                .then(lhs.1.local.cmp(&rhs.1.local))
                .then(lhs.1.allocator.cmp(&rhs.1.allocator))
                .then(lhs.1.before_stmt.cmp(&rhs.1.before_stmt))
        });
        let mut origin_rewrite_kind_counts: BTreeMap<String, usize> = BTreeMap::new();
        let mut origin_allocator_counts: BTreeMap<String, usize> = BTreeMap::new();
        for (_, rewrite) in &origin_sites {
            *origin_rewrite_kind_counts
                .entry(rewrite.rewrite_kind.clone())
                .or_default() += 1;
            *origin_allocator_counts
                .entry(rewrite.allocator.clone())
                .or_default() += 1;
        }
        let mut origin_index = String::new();
        origin_index.push_str(&format!(
            "allocator_filter={}\n",
            allocator_origin_filter_label()
        ));
        origin_index.push_str(&format!("allocator_origin_sites={}\n", origin_sites.len()));
        origin_index.push_str(&format!(
            "legacy_shape_counters_rewrite_kind_counts: {}\n",
            format_counts(&origin_rewrite_kind_counts)
        ));
        origin_index.push_str(&format!(
            "legacy_shape_counters_allocator_counts: {}\n",
            format_counts(&origin_allocator_counts)
        ));
        for (idx, (case_name, rewrite)) in origin_sites.iter().enumerate() {
            origin_index.push_str(&format!(
                "\n[{idx}] case={} fn={} local={} allocator={} rewrite={}\n",
                case_name, rewrite.function, rewrite.local, rewrite.allocator, rewrite.rewrite_kind
            ));
            origin_index.push_str(&format!("before: {}\n", rewrite.before_stmt));
            origin_index.push_str(&format!(
                "after: {}\n",
                rewrite.after_stmt.as_deref().unwrap_or("<missing>")
            ));
        }
        write_text_file(
            &config.root.join("allocator_origin_rewrites.txt"),
            &origin_index,
        );

        let passed_cases = case_rows
            .iter()
            .filter(|row| row.rewrite_ok && row.compile_ok)
            .count();
        let failed_cases = case_rows.len().saturating_sub(passed_cases);
        let mut summary = String::new();
        summary.push_str("== B02 rewriter dump summary ==\n");
        summary.push_str(&format!("run_id={}\n", config.run_id));
        summary.push_str(&format!("cases={}\n", case_rows.len()));
        summary.push_str(&format!("passed_cases={passed_cases}\n"));
        summary.push_str(&format!("failed_cases={failed_cases}\n"));
        summary.push_str(&format!(
            "allocator_unsafe_before_total={alloc_before_total} allocator_unsafe_after_total={alloc_after_total} allocator_unsafe_removed_total={alloc_removed_total}\n"
        ));
        summary.push_str(&format!(
            "box_new_before_total={box_new_before_total} box_new_after_total={box_new_after_total} box_new_added_total={box_new_added_total}\n"
        ));
        summary.push_str(&format!(
            "raw_constructor_unsafe_before_total={raw_unsafe_before_total} raw_constructor_unsafe_after_total={raw_unsafe_after_total} raw_constructor_unsafe_added_total={raw_unsafe_added_total}\n"
        ));
        summary.push_str(&format!(
            "box_unsafe_before_total={box_unsafe_before_total} box_unsafe_after_total={box_unsafe_after_total} box_unsafe_added_total={box_unsafe_added_total}\n"
        ));
        summary.push_str(&format!(
            "spec_reason_counts_total: {}\n",
            format_counts_by_callee(
                &spec_reason_total,
                &crate::rewriter::stats::ALLOCATOR_REASON_KEYS
            )
        ));
        for (allocator, reason_counts) in &spec_reason_by_allocator {
            summary.push_str(&format!(
                "spec_reason_counts_by_allocator[{allocator}]: {}\n",
                format_counts_by_callee(
                    reason_counts,
                    &crate::rewriter::stats::ALLOCATOR_REASON_KEYS
                )
            ));
        }
        summary.push_str(&format!(
            "allocator_removal_rate={alloc_removal_rate:.2}% box_new_growth_rate={box_new_growth_rate:.2}% raw_unsafe_growth_rate={raw_unsafe_growth_rate:.2}%\n"
        ));
        summary.push_str(&format!(
            "allocator_unsafe_before_by_callee: {}\n",
            format_counts_by_callee(
                &alloc_before_by_callee,
                &crate::rewriter::stats::ALLOC_UNSAFE_CALLEES,
            )
        ));
        summary.push_str(&format!(
            "allocator_unsafe_after_by_callee: {}\n",
            format_counts_by_callee(
                &alloc_after_by_callee,
                &crate::rewriter::stats::ALLOC_UNSAFE_CALLEES,
            )
        ));
        summary.push_str(&format!(
            "box_new_before_by_callee: {}\n",
            format_counts_by_callee(
                &box_new_before_by_callee,
                &crate::rewriter::stats::BOX_NEW_CALLEES,
            )
        ));
        summary.push_str(&format!(
            "box_new_after_by_callee: {}\n",
            format_counts_by_callee(
                &box_new_after_by_callee,
                &crate::rewriter::stats::BOX_NEW_CALLEES,
            )
        ));
        summary.push_str(&format!(
            "raw_constructor_unsafe_before_by_callee: {}\n",
            format_counts_by_callee(
                &raw_unsafe_before_by_callee,
                &crate::rewriter::stats::RAW_CONSTRUCTOR_UNSAFE_CALLEES,
            )
        ));
        summary.push_str(&format!(
            "raw_constructor_unsafe_after_by_callee: {}\n",
            format_counts_by_callee(
                &raw_unsafe_after_by_callee,
                &crate::rewriter::stats::RAW_CONSTRUCTOR_UNSAFE_CALLEES,
            )
        ));
        summary.push_str(&format!(
            "box_unsafe_before_by_callee: {}\n",
            format_counts_by_callee(&box_unsafe_before_by_callee, &BOX_UNSAFE_CALLEES)
        ));
        summary.push_str(&format!(
            "box_unsafe_after_by_callee: {}\n",
            format_counts_by_callee(&box_unsafe_after_by_callee, &BOX_UNSAFE_CALLEES)
        ));
        summary.push_str(&format!(
            "allocator_origin_sites_total={}\n",
            origin_sites.len()
        ));
        summary.push_str(&format!(
            "allocator_origin_filter={}\n",
            allocator_origin_filter_label()
        ));
        summary.push_str(&format!(
            "legacy_shape_counters_rewrite_kind_counts: {}\n",
            format_counts(&origin_rewrite_kind_counts)
        ));
        summary.push_str(&format!(
            "legacy_shape_counters_by_allocator: {}\n",
            format_counts(&origin_allocator_counts)
        ));
        summary.push_str("allocator_origin_index_file=allocator_origin_rewrites.txt\n");
        if failures.is_empty() {
            summary.push_str("failed_case_details: <none>\n");
        } else {
            summary.push_str("failed_case_details:\n");
            for failure in &failures {
                summary.push_str(&format!(
                    "case={} stage={} message={}\n",
                    failure.case_name, failure.stage, failure.message
                ));
            }
        }

        write_text_file(&config.root.join("summary.txt"), &summary);
        println!("B02 rewrite dump root={}", config.root.display());
    }

    if !failures.is_empty() {
        let mut lines = Vec::new();
        lines.push(format!(
            "B02 rewrite sweep completed with {} failure(s)",
            failures.len()
        ));
        for failure in failures {
            lines.push(format!(
                "case={} stage={} message={}",
                failure.case_name, failure.stage, failure.message
            ));
        }
        panic!("{}", lines.join("\n"));
    }
}

#[test]
fn b02_dump_env_parser_handles_common_flags() {
    assert_eq!(parse_env_bool("1"), Some(true));
    assert_eq!(parse_env_bool("true"), Some(true));
    assert_eq!(parse_env_bool("TRUE"), Some(true));
    assert_eq!(parse_env_bool("0"), Some(false));
    assert_eq!(parse_env_bool("false"), Some(false));
    assert_eq!(parse_env_bool("FALSE"), Some(false));
    assert_eq!(parse_env_bool("  "), Some(false));
    assert_eq!(parse_env_bool("maybe"), None);
}

#[test]
fn b02_dump_unified_diff_has_expected_markers() {
    let diff = render_unified_diff("fn before() {}\n", "fn after() {}\n");
    assert!(diff.contains("--- before.rs"));
    assert!(diff.contains("+++ after.rs"));
    assert!(diff.contains("@@"));
}

#[test]
fn allocator_origin_rewrite_tracker_matches_locals() {
    let before = r#"
        fn f() {
            let ptr: *mut i32 = malloc(4usize) as *mut i32;
        }
    "#;
    let after = r#"
        fn f() {
            let mut ptr: Option<Box<i32>> = Some(Box::new(<i32 as Default>::default()));
        }
    "#;
    let rewrites = collect_allocator_origin_rewrites(before, after);
    assert_eq!(rewrites.len(), 1);
    assert_eq!(rewrites[0].function, "f");
    assert_eq!(rewrites[0].local, "ptr");
    assert_eq!(rewrites[0].allocator, "malloc");
    assert_eq!(rewrites[0].rewrite_kind, "rewritten_to_box_new");
}

pub(super) fn run_ownership_case_with_box_candidates(
    case_name: &str,
    code: &str,
    expected_box_candidates: &[&str],
    expected_non_candidates: &[&str],
) {
    run_compiler(code, |tcx| {
        let program = collect_program(tcx);
        let results = analyze_program(&program);
        let by_scoped_name = collect_raw_ptr_local_ownership(&program, &results);

        let mut owning_names = by_scoped_name
            .iter()
            .filter_map(|((function, local), &is_owning)| {
                is_owning.then_some(format!("{function}#{local}"))
            })
            .collect::<Vec<_>>();
        owning_names.sort();
        owning_names.dedup();

        let mut raw_ptr_names = by_scoped_name
            .keys()
            .map(|(function, local)| format!("{function}#{local}"))
            .collect::<Vec<_>>();
        raw_ptr_names.sort();
        raw_ptr_names.dedup();

        let resolve_spec = |spec: &str| {
            if let Some((function_spec, local_spec)) = spec.rsplit_once('#') {
                let mut matches = by_scoped_name
                    .iter()
                    .filter_map(|((function, local), &is_owning)| {
                        (local == local_spec
                            && (function == function_spec || function.ends_with(function_spec)))
                        .then_some((function.clone(), local.clone(), is_owning))
                    })
                    .collect::<Vec<_>>();
                matches.sort();
                matches.dedup();
                return matches;
            }

            let mut matches = by_scoped_name
                .iter()
                .filter_map(|((function, local), &is_owning)| {
                    (local == spec).then_some((function.clone(), local.clone(), is_owning))
                })
                .collect::<Vec<_>>();
            matches.sort();
            matches.dedup();
            matches
        };

        let extracted_allocator_related = extract_allocator_related_ptr_locals(code);

        let mut malloc_related_candidates = Vec::new();
        for (fn_hint, local) in extracted_allocator_related {
            let mut resolved = by_scoped_name
                .keys()
                .filter_map(|(function, candidate_local)| {
                    (candidate_local == &local && function.ends_with(&fn_hint))
                        .then_some(format!("{function}#{candidate_local}"))
                })
                .collect::<Vec<_>>();
            resolved.sort();
            resolved.dedup();
            malloc_related_candidates.extend(resolved);
        }
        malloc_related_candidates.sort();
        malloc_related_candidates.dedup();
        let mut effective_expected_box_candidates = expected_box_candidates
            .iter()
            .map(|s| (*s).to_owned())
            .collect::<Vec<_>>();
        effective_expected_box_candidates.extend(malloc_related_candidates.iter().cloned());
        effective_expected_box_candidates.sort();
        effective_expected_box_candidates.dedup();
        let mut effective_expected_non_candidates = expected_non_candidates
            .iter()
            .map(|s| (*s).to_owned())
            .collect::<Vec<_>>();
        effective_expected_non_candidates.sort();
        effective_expected_non_candidates.dedup();

        record_total_analysis_stats(
            &program,
            &results,
            &by_scoped_name,
            &owning_names,
            &malloc_related_candidates,
            &effective_expected_box_candidates,
            &effective_expected_non_candidates,
        );

        for spec in &effective_expected_box_candidates {
            let spec = spec.as_str();
            let matches = resolve_spec(spec);
            let is_scoped = spec.contains('#');
            if !is_scoped && matches.len() > 1 {
                let mut candidates = matches
                    .iter()
                    .map(|(function, local, _)| format!("{function}#{local}"))
                    .collect::<Vec<_>>();
                candidates.sort();
                candidates.dedup();
                panic!(
                    "unscoped candidate `{spec}` is ambiguous in case `{case_name}`; use `function_path#{spec}`. Matches: {:?}",
                    candidates
                );
            }
            match matches.as_slice() {
                [(_, _, true)] => {}
                [(_, _, false)] => {
                    panic!(
                        "pointer `{spec}` should be box-promotable in case `{case_name}` but is not owning (owning locals: {:?})",
                        owning_names
                    );
                }
                [] => {
                    panic!(
                        "pointer `{spec}` was not found among raw-pointer locals in case `{case_name}` (available: {:?})",
                        raw_ptr_names
                    );
                }
                _ => unreachable!("ambiguous scoped candidate lookup should have been rejected"),
            }
        }

        for spec in &effective_expected_non_candidates {
            let spec = spec.as_str();
            let matches = resolve_spec(spec);
            let is_scoped = spec.contains('#');
            if !is_scoped && matches.len() > 1 {
                let mut candidates = matches
                    .iter()
                    .map(|(function, local, _)| format!("{function}#{local}"))
                    .collect::<Vec<_>>();
                candidates.sort();
                candidates.dedup();
                panic!(
                    "unscoped negative candidate `{spec}` is ambiguous in case `{case_name}`; use `function_path#{spec}`. Matches: {:?}",
                    candidates
                );
            }
            match matches.as_slice() {
                [(_, _, false)] => {}
                [(_, _, true)] => {
                    panic!(
                        "pointer `{spec}` should NOT be box-promotable in case `{case_name}` but is owning"
                    );
                }
                [] => {
                    panic!(
                        "negative pointer `{spec}` not found among raw-pointer locals in case `{case_name}`"
                    );
                }
                _ => unreachable!("ambiguous scoped negative lookup should have been rejected"),
            }
        }
    });
}

pub mod aabb_lib;
pub mod agglom_lib;
pub mod arity_lib;
pub mod arr_del_lib;
pub mod arr_ins_lib;
pub mod arr_push_lib;
pub mod arrayfunc_lib;
pub mod basename_lib;
pub mod betagamma_lib;
pub mod buffapp_lib;
pub mod cJSON_lib;
pub mod call_predict_lib;
pub mod capsule_lib;
pub mod char_to_bool;
pub mod charinbuf_lib;
pub mod checkshift_lib;
pub mod circle_collide_lib;
pub mod cleanup_lib;
pub mod complexmode_lib;
pub mod confusion_lib;
pub mod container_of;
pub mod convert_pix_lib;
pub mod dataentry_lib;
pub mod decode_base64_lib;
pub mod doubleneg_lib;
pub mod encode_base64_lib;
pub mod envy_lib;
pub mod fallcalc_lib;
pub mod file_queue_lib;
pub mod findrep_lib;
pub mod gen_ray_lib;
pub mod generic_foreach;
pub mod get_predict_func_lib;
pub mod gjk_cache_lib;
pub mod gjk_lib;
pub mod goto_lib;
pub mod gotomach_lib;
pub mod hashmap_tree;
pub mod hatch_lib;
pub mod helxo_lib;
pub mod hm_geti_lib;
pub mod inreftree_lib;
pub mod intput_lib;
pub mod jumpnode_lib;
pub mod lines_in_buffer_lib;
pub mod load_png_mem_lib;
pub mod macrodepth_add_5;
pub mod macrodepth_mul_4;
pub mod macrodepth_sub_6;
pub mod mathop_lib;
pub mod matrix_mult_lib;
pub mod matrixsum_lib;
pub mod maxnmin_lib;
pub mod memchra2_lib;
pub mod memcpy_fun_buffers;
pub mod memmove;
pub mod modeselect_lib;
pub mod mutable_duplication_dag;
pub mod omni_collide_lib;
pub mod omni_manifold_lib;
pub mod overunder_lib;
pub mod parse_number_lib;
pub mod parse_uname_lib;
pub mod pinflate_lib;
pub mod pointer_comparison_ascii_art;
pub mod poly_ray_lib;
pub mod qmath;
pub mod rdg_genstdout_lib;
pub mod reverse_collide_lib;
pub mod search_and_replace_lib;
pub mod sh_geti_lib;
pub mod sh_puts_lib;
pub mod siphash_lib;
pub mod spec_ray_lib;
pub mod static_vars_fpts;
pub mod str_dups_lib;
pub mod str_put_lib;
pub mod strcmp;
pub mod strcpy;
pub mod strdup_lib;
pub mod task_manager_lib;
pub mod tu_linkage;
pub mod underhanded_c_luggage;
pub mod underhanded_c_nuke_lib;
pub mod unfilter_lib;
pub mod utf8_lib;
