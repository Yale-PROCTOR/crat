#![allow(non_snake_case)]

use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Mutex, OnceLock,
};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{ItemKind, OwnerNode, def_id::DefId};
use rustc_middle::{
    mir::{Local, VarDebugInfoContents},
    ty::TyCtxt,
};
use rustc_span::def_id::LocalDefId;

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

            for (slot_idx, (observed_slot, expected_ty)) in
                observed.into_iter().zip(expected_tys.into_iter()).enumerate()
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

fn has_allocator_call(text: &str) -> bool {
    fn is_ident_char(b: u8) -> bool {
        b == b'_' || b.is_ascii_alphanumeric()
    }

    fn contains_direct_call(text: &str, callee: &str) -> bool {
        let pattern = format!("{callee}(");
        let mut offset = 0usize;
        let bytes = text.as_bytes();

        while let Some(pos) = text[offset..].find(&pattern) {
            let idx = offset + pos;
            let has_ident_prefix = idx > 0 && is_ident_char(bytes[idx - 1]);
            if !has_ident_prefix {
                return true;
            }
            offset = idx + 1;
        }
        false
    }

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
        let mut effective_expected_box_candidates =
            expected_box_candidates.iter().map(|s| (*s).to_owned()).collect::<Vec<_>>();
        effective_expected_box_candidates.extend(malloc_related_candidates.iter().cloned());
        effective_expected_box_candidates.sort();
        effective_expected_box_candidates.dedup();
        let mut effective_expected_non_candidates =
            expected_non_candidates.iter().map(|s| (*s).to_owned()).collect::<Vec<_>>();
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
