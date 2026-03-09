use rustc_ast::{ItemKind, mut_visit::MutVisitor, ptr::P};
use rustc_ast_pretty::pprust;
use rustc_middle::ty::TyCtxt;
use rustc_span::Symbol;
use utils::ir::AstToHir;

use super::{
    analysis::analyze,
    callgraph::{build_union_call_contexts, collect_union_seed_functions},
    raw_struct::{
        RawStructVisitor, UnionUseRewriteVisitor, classify_union_field_types, has_bytemuck_traits,
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

pub fn replace_unions(tcx: TyCtxt<'_>, verbose: bool) -> TransformationResult {
    let mut krate = utils::ast::expanded_ast(tcx);

    // bytemuck trait visibility is needed for field classification
    if !has_bytemuck_traits(tcx) {
        println!("bytemuck traits are not visible in current tcx;");
        println!("add bytemuck dependency and rerun this pass once.");
        krate.items.insert(
            0,
            P(utils::item!(
                "extern crate bytemuck as {};",
                ANALYSIS_BYTEMUCK
            )),
        );
        utils::ast::remove_unnecessary_items_from_ast(&mut krate);
        return TransformationResult {
            code: pprust::crate_to_string_for_macros(&krate),
            needs_bytemuck: true,
        };
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
    let needs_bytemuck = needs_bytemuck(&overlapping_tys, &union_field_classes);

    if !overlapping_tys.is_empty() {
        println!("\noverlapping:");
        for union_ty in &overlapping_tys {
            println!("{}", tcx.def_path_str(*union_ty));
        }
    } else {
        println!("\nno overlapping unions detected");
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
    remove_analysis_bytemuck_extern(&mut krate);

    let str = pprust::crate_to_string_for_macros(&krate);
    if true {
        println!("\n{str}");
    }

    TransformationResult {
        code: str,
        needs_bytemuck,
    }
}

const ANALYSIS_BYTEMUCK: &str = "__crat_bytemuck";

fn remove_analysis_bytemuck_extern(krate: &mut rustc_ast::Crate) {
    let alias = Symbol::intern(ANALYSIS_BYTEMUCK);
    krate.items.retain(|item| match item.kind {
        ItemKind::ExternCrate(_, ident) => ident.name != alias,
        _ => true,
    });
}
