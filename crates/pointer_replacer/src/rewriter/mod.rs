use rustc_ast::mut_visit::MutVisitor;
use rustc_ast_pretty::pprust;
use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::ty::TyCtxt;
use transform::TransformVisitor;

use crate::{
    analyses::{
        self,
        borrow::PromotedMutRefs as PromotedMutRefResult,
        output_params::OutputParams as OutputParamResult,
        type_qualifier::foster::{fatness::FatnessResult, mutability::MutabilityResult},
    },
    utils::rustc::RustProgram,
};

mod collector;
mod decision;
mod transform;

pub struct Analysis {
    mutability_result: MutabilityResult,
    output_param_result: OutputParamResult,
    promoted_mut_ref_result: PromotedMutRefResult,
    fatness_result: FatnessResult,
}

impl Analysis {
    pub fn new(
        mutability_result: MutabilityResult,
        output_param_result: OutputParamResult,
        promoted_mut_ref_result: PromotedMutRefResult,
        fatness_result: FatnessResult,
    ) -> Self {
        Analysis {
            mutability_result,
            output_param_result,
            promoted_mut_ref_result,
            fatness_result,
        }
    }
}

pub fn replace_local_borrows(tcx: TyCtxt<'_>) -> String {
    let mut krate = utils::ast::expanded_ast(tcx);
    let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

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
            ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
            ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
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
    let output_param_result =
        analyses::output_params::compute_output_params(&input, &mutability_result);
    let source_var_groups = analyses::mir_variable_grouping::SourceVarGroups::new(&input);
    // TODO: promoted_mut_ref does mutability analysis again internally
    let promoted_mut_ref_result = source_var_groups
        .postprocess_promoted_mut_refs(analyses::borrow::mutable_references_no_guarantee(&input));
    let fatness_result = analyses::type_qualifier::foster::fatness::fatness_analysis(&input);
    let analysis_results = Analysis::new(
        mutability_result,
        output_param_result,
        promoted_mut_ref_result,
        fatness_result,
    );

    let mut visitor = TransformVisitor::new(&input, &analysis_results, ast_to_hir);
    visitor.visit_crate(&mut krate);

    pprust::crate_to_string_for_macros(&krate)
}
