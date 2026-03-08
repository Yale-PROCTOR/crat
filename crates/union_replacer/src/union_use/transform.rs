use rustc_ast::{ItemKind, mut_visit::MutVisitor, ptr::P};
use rustc_ast_pretty::pprust;
use rustc_middle::ty::TyCtxt;
use rustc_span::Symbol;
use utils::ir::AstToHir;

use super::{
    analysis::analyze,
    callgraph::{build_union_call_contexts, collect_union_seed_functions},
    raw_struct::{
        RawStructVisitor, UnionUseRewriteVisitor, classify_union_field_types,
        has_visible_bytemuck_traits,
    },
    reverse_cfg::{analyze_reaching_writes, detect_overlapping_types},
    ty_visit::{collect_local_union_types, collect_union_related_types},
};

pub fn replace_unions(tcx: TyCtxt<'_>, verbose: bool) -> String {
    let mut krate = utils::ast::expanded_ast(tcx);

    // TODO: bytemuck dependency should be added only if there is an overlapping union
    let missing_all_bytemuck_traits = !has_visible_bytemuck_traits(tcx);
    if missing_all_bytemuck_traits && !has_analysis_bytemuck_extern(&krate) {
        krate.items.insert(
            0,
            P(utils::item!(
                "extern crate bytemuck as {};",
                ANALYSIS_BYTEMUCK_ALIAS
            )),
        );
        println!(
            "bytemuck traits are not visible in current tcx; injected analysis extern crate. rerun this pass once."
        );
        utils::ast::remove_unnecessary_items_from_ast(&mut krate);
        return pprust::crate_to_string_for_macros(&krate);
    }

    // for debug
    let use_optimized_mir = false;
    let print_mir = false;

    // collect union types and build call graphs
    let (union_tys, ty_visitor) = collect_local_union_types(&tcx, verbose);
    let union_field_classes = classify_union_field_types(tcx, &union_tys, true);
    let related_types_map = collect_union_related_types(&tcx, &union_tys, &ty_visitor, verbose);
    let seed_functions = collect_union_seed_functions(tcx, &union_tys, verbose);
    let call_contexts = build_union_call_contexts(
        tcx,
        &seed_functions,
        &related_types_map,
        use_optimized_mir,
        verbose,
    );

    // analyze union uses and detect overlapping unions
    let union_uses = analyze(
        tcx,
        &union_tys,
        &call_contexts,
        print_mir,
        use_optimized_mir,
        verbose,
    );
    let reaching_writes =
        analyze_reaching_writes(tcx, &union_uses, &call_contexts, use_optimized_mir);
    let overlapping_tys = detect_overlapping_types(tcx, &union_uses, &reaching_writes, verbose);
    let mut overlapping_local_union_tys = overlapping_tys
        .iter()
        .filter_map(|def_id| def_id.as_local())
        .collect::<Vec<_>>();
    overlapping_local_union_tys.sort_by_key(|def_id| tcx.def_path_str(*def_id));

    if !overlapping_tys.is_empty() {
        println!("\noverlapping:");
        for union_ty in &overlapping_tys {
            println!("{}", tcx.def_path_str(*union_ty));
        }
    } else {
        println!("\nno overlapping unions detected");
    }

    let ast_to_hir: AstToHir = utils::ast::make_ast_to_hir(&mut krate, tcx);

    let mut raw_struct_visitor =
        RawStructVisitor::new(tcx, &overlapping_local_union_tys, union_field_classes);
    raw_struct_visitor.visit_crate(&mut krate);
    println!("Step 1: replaced unions with raw structs");

    let mut use_visitor =
        UnionUseRewriteVisitor::new(tcx, ast_to_hir, &overlapping_local_union_tys);
    use_visitor.visit_crate(&mut krate);
    println!("Step 2: updated union uses");

    utils::ast::remove_unnecessary_items_from_ast(&mut krate);
    remove_analysis_bytemuck_extern(&mut krate);

    let str = pprust::crate_to_string_for_macros(&krate);
    if true {
        println!("\n{str}");
    }
    str
}

const ANALYSIS_BYTEMUCK_ALIAS: &str = "__crat_bytemuck";

fn has_analysis_bytemuck_extern(krate: &rustc_ast::Crate) -> bool {
    let alias = Symbol::intern(ANALYSIS_BYTEMUCK_ALIAS);
    krate.items.iter().any(|item| match item.kind {
        ItemKind::ExternCrate(_, ident) => ident.name == alias,
        _ => false,
    })
}

fn remove_analysis_bytemuck_extern(krate: &mut rustc_ast::Crate) {
    let alias = Symbol::intern(ANALYSIS_BYTEMUCK_ALIAS);
    krate.items.retain(|item| match item.kind {
        ItemKind::ExternCrate(_, ident) => ident.name != alias,
        _ => true,
    });
}
