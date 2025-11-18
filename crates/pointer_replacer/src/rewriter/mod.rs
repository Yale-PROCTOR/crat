use etrace::some_or;
use points_to::andersen;
use rustc_ast::mut_visit::MutVisitor;
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LocalDefId;
use transform::TransformVisitor;

use crate::{
    analyses::{
        self,
        borrow::PromotedMutRefs as PromotedMutRefResult,
        type_qualifier::foster::{fatness::FatnessResult, mutability::MutabilityResult},
    },
    utils::rustc::RustProgram,
};

mod collector;
mod decision;
mod transform;

pub struct Analysis {
    mutability_result: MutabilityResult,
    promoted_mut_ref_result: PromotedMutRefResult,
    fatness_result: FatnessResult,
    aliases: FxHashMap<LocalDefId, FxHashSet<usize>>,
}

pub fn replace_local_borrows(tcx: TyCtxt<'_>) -> String {
    let mut krate = utils::ast::expanded_ast(tcx);
    let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

    let arena = typed_arena::Arena::new();
    let tss = utils::ty_shape::get_ty_shapes(&arena, tcx, false);
    let andersen_config = andersen::Config {
        use_optimized_mir: false,
    };
    let pre_points_to = andersen::pre_analyze(&andersen_config, &tss, tcx);
    let points_to = andersen::analyze(&andersen_config, &pre_points_to, &tss, tcx);
    let aliases = find_param_aliases(pre_points_to, &points_to, tcx);

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
    let source_var_groups = analyses::mir_variable_grouping::SourceVarGroups::new(&input);
    let promoted_mut_ref_result = source_var_groups
        .postprocess_promoted_mut_refs(analyses::borrow::mutable_references_no_guarantee(&input));
    let fatness_result = analyses::type_qualifier::foster::fatness::fatness_analysis(&input);
    let analysis_results = Analysis {
        mutability_result,
        promoted_mut_ref_result,
        fatness_result,
        aliases,
    };

    let mut visitor = TransformVisitor::new(&input, &analysis_results, ast_to_hir);
    visitor.visit_crate(&mut krate);

    pprust::crate_to_string_for_macros(&krate)
}

fn find_param_aliases<'tcx>(
    pre: andersen::PreAnalysisData<'tcx>,
    points_to: &andersen::Solutions,
    tcx: TyCtxt<'tcx>,
) -> FxHashMap<LocalDefId, FxHashSet<usize>> {
    let mut param_aliases = FxHashMap::default();
    for def_id in tcx.hir_body_owners() {
        let calls = some_or!(pre.call_args.get(&def_id), continue);
        let mut aliases = FxHashSet::default();
        let body = tcx.mir_drops_elaborated_and_const_checked(def_id).borrow();
        for call_args in calls {
            for i in 0..body.arg_count {
                for j in i..body.arg_count {
                    if aliases.contains(&i) && aliases.contains(&j) {
                        continue;
                    }
                    let arg_i = some_or!(call_args[i], continue);
                    let arg_j = some_or!(call_args[j], continue);
                    let mut sol_i = points_to[arg_i].clone();
                    sol_i.intersect(&points_to[arg_j]);
                    if !sol_i.is_empty() {
                        aliases.insert(i);
                        aliases.insert(j);
                    }
                }
            }
        }
        if !aliases.is_empty() {
            param_aliases.insert(def_id, aliases);
        }
    }
    param_aliases
}
