use rustc_ast::mut_visit::MutVisitor;
use rustc_ast_pretty::pprust;
use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::ty::TyCtxt;
use transform::TransformVisitor;

use crate::{
    analyses,
    analyses::{
        borrow::PromotedMutRefs as PromotedMutRefResult,
        output_params::OutputParams as OutputParamResult,
    },
    utils::rustc::RustProgram,
};

mod collector;
mod decision;
mod transform;

pub struct Analysis {
    output_param_result: OutputParamResult,
    promoted_mut_ref_result: PromotedMutRefResult,
}

impl Analysis {
    pub fn new(
        output_param_result: OutputParamResult,
        promoted_mut_ref_result: PromotedMutRefResult,
    ) -> Self {
        Analysis {
            output_param_result,
            promoted_mut_ref_result,
        }
    }
}

pub fn replace_local_borrows(tcx: TyCtxt<'_>) -> String {
    let mut krate = utils::ast::expanded_ast(tcx);
    let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

    let hir_to_thir = utils::ir::map_hir_to_thir(tcx);

    let mut functions = vec![];
    let mut structs = vec![];
    for maybe_owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        match item.kind {
            ItemKind::Fn { .. } => functions.push(item.owner_id.def_id.to_def_id()),
            ItemKind::Struct(..) => structs.push(item.owner_id.def_id.to_def_id()),
            _ => {}
        };
    }
    let input = RustProgram {
        tcx,
        functions,
        structs,
    };

    let mutability_result =
        analyses::type_qualifier::foster::mutability::mutability_analysis(&input);
    let output_params = analyses::output_params::compute_output_params(&input, &mutability_result);
    let source_var_groups = analyses::mir_variable_grouping::SourceVarGroups::new(&input);
    let promoted_mut_refs = source_var_groups
        .postprocess_promoted_mut_refs(analyses::borrow::mutable_references_no_guarantee(&input));
    let analysis_results = Analysis::new(output_params, promoted_mut_refs);

    let mut visitor = TransformVisitor::new(&input, &analysis_results, ast_to_hir, hir_to_thir);
    visitor.visit_crate(&mut krate);

    let mut visitor = transform::post::UnnecessaryRawMutRemover;
    visitor.visit_crate(&mut krate);

    pprust::crate_to_string_for_macros(&krate)
}
