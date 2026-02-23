#![allow(non_snake_case)]

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
            whole_program::WholeProgramAnalysis,
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

fn analyze_program<'tcx>(
    program: &RustProgram<'tcx>,
) -> crate::analyses::ownership::whole_program::WholeProgramResults<'tcx> {
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
    results: &crate::analyses::ownership::whole_program::WholeProgramResults<'tcx>,
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

        for &spec in expected_box_candidates {
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

        for &spec in expected_non_candidates {
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
