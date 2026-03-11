use rustc_ast::mut_visit::MutVisitor;
use rustc_ast_pretty::pprust;
use rustc_middle::ty::TyCtxt;
use utils::ir::AstToHir;

use super::{
    analysis::analyze,
    callgraph::{build_union_call_contexts, collect_union_seed_functions},
    raw_struct::{
        RawStructVisitor, UnionUseRewriteVisitor, all_union_fields_are_pod,
        classify_union_field_types,
    },
    reverse_cfg::{analyze_reaching_writes, detect_overlapping_types},
    ty_visit::{collect_local_union_types, collect_union_related_types},
    utils::needs_bytemuck,
};

#[derive(Debug)]
pub struct TransformationResult {
    pub code: String,
    pub needs_bytemuck: bool,
}

fn print_union_use_stats(benchmark_all_local: usize, benchmark_targets: usize, overlapping: usize) {
    println!("UNION_USE_STATS,{benchmark_all_local},{benchmark_targets},{overlapping}");
}

pub fn replace_unions(tcx: TyCtxt<'_>, verbose: bool) -> TransformationResult {
    let mut krate = utils::ast::expanded_ast(tcx);

    // for debug
    let print_mir = false;
    let print_result = true;

    // collect union types and build call graphs
    let (union_tys, ty_visitor) = collect_local_union_types(&tcx, verbose);
    let all_local_union_count = union_tys.len();
    let union_field_classes = classify_union_field_types(tcx, &union_tys, true);
    let pod_union_tys = union_tys
        .iter()
        .copied()
        .filter(|union_ty| all_union_fields_are_pod(&union_field_classes, *union_ty))
        .collect::<Vec<_>>();
    let analysis_target_count = pod_union_tys.len();

    if verbose {
        println!("\nPod-only target unions:");
        if pod_union_tys.is_empty() {
            println!("\t(none)");
        } else {
            for union_ty in &pod_union_tys {
                println!("\t{}", tcx.def_path_str(*union_ty));
            }
        }
    }

    if pod_union_tys.is_empty() {
        utils::ast::remove_unnecessary_items_from_ast(&mut krate);
        let code = pprust::crate_to_string_for_macros(&krate);
        print_union_use_stats(all_local_union_count, analysis_target_count, 0);
        return TransformationResult {
            code,
            needs_bytemuck: false,
        };
    }

    let related_types_map = collect_union_related_types(&tcx, &pod_union_tys, &ty_visitor, verbose);
    let seed_functions = collect_union_seed_functions(tcx, &pod_union_tys, verbose);
    let call_contexts =
        build_union_call_contexts(tcx, &seed_functions, &related_types_map, verbose);

    // analyze union uses and detect overlapping unions
    let union_uses = analyze(tcx, &pod_union_tys, &call_contexts, print_mir, verbose);
    let reaching_writes = analyze_reaching_writes(tcx, &union_uses, &call_contexts);
    let overlapping_tys = detect_overlapping_types(tcx, &union_uses, &reaching_writes, verbose);
    let needs_bytemuck = needs_bytemuck(&overlapping_tys, &union_field_classes);

    if print_result {
        if !overlapping_tys.is_empty() {
            println!("\noverlapping:");
            for union_ty in &overlapping_tys {
                println!("{}", tcx.def_path_str(*union_ty));
            }
        } else {
            println!("\noverlapping: none");
        }
    }

    // transform the AST
    let ast_to_hir: AstToHir = utils::ast::make_ast_to_hir(&mut krate, tcx);

    // Step 1: replace unions with raw structs
    let mut raw_struct_visitor = RawStructVisitor::new(tcx, &overlapping_tys, union_field_classes);
    raw_struct_visitor.visit_crate(&mut krate);

    // Step 2: update union uses
    let mut use_visitor = UnionUseRewriteVisitor::new(tcx, ast_to_hir, &overlapping_tys);
    use_visitor.visit_crate(&mut krate);

    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

    let str = pprust::crate_to_string_for_macros(&krate);
    if verbose {
        println!("\n{str}");
    }

    if print_result {
        print_union_use_stats(
            all_local_union_count,
            analysis_target_count,
            overlapping_tys.len(),
        );
    }

    TransformationResult {
        code: str,
        needs_bytemuck,
    }
}
