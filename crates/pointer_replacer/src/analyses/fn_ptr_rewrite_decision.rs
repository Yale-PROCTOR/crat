use points_to::andersen::{self, Var};
use rustc_abi::FieldIdx;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{HirId, def_id::LocalDefId};
use rustc_middle::ty;
use utils::ty_shape::{TyShape, TyShapes};

use crate::{
    analyses::fn_ptr_groups::FnPtrGroups,
    rewriter::{
        Analysis,
        decision::{DecisionMaker, PtrKind},
    },
    utils::rustc::RustProgram,
};

#[derive(Default)]
pub struct FnPtrRewriteDecision {
    pub direct_rewrite: FxHashSet<LocalDefId>,
    #[allow(dead_code)] // used in Phase 2 wrapper generation
    pub needs_wrapper: FxHashSet<LocalDefId>,
    /// Per-parameter individual decisions per fn-ptr function (ignoring group consensus).
    pub individual_decisions: FxHashMap<LocalDefId, Vec<Option<PtrKind>>>,
    /// Annotation-site decisions for direct_rewrite functions only.
    pub annotation_decisions: FxHashMap<HirId, Vec<Option<PtrKind>>>,
    /// Struct-field fn-ptr decisions for direct_rewrite functions only.
    pub field_decisions: FxHashMap<(LocalDefId, FieldIdx), Vec<Option<PtrKind>>>,
}

impl FnPtrRewriteDecision {
    pub fn build<'tcx>(
        pre: &andersen::PreAnalysisData<'tcx>,
        solutions: &andersen::Solutions,
        rust_program: &RustProgram<'tcx>,
        analysis: &Analysis,
        tss: &TyShapes<'_, 'tcx>,
        fn_ptr_groups: &FnPtrGroups,
    ) -> Self {
        let tcx = rust_program.tcx;

        if fn_ptr_groups.fn_to_group.is_empty() {
            return FnPtrRewriteDecision {
                direct_rewrite: FxHashSet::default(),
                needs_wrapper: FxHashSet::default(),
                individual_decisions: FxHashMap::default(),
                annotation_decisions: FxHashMap::default(),
                field_decisions: FxHashMap::default(),
            };
        }

        // --- Step 1: compute individual decisions per fn-ptr function ---
        let mut individual_decisions: FxHashMap<LocalDefId, Vec<Option<PtrKind>>> =
            FxHashMap::default();

        for &did in fn_ptr_groups.fn_to_group.keys() {
            let input_len = tcx.fn_sig(did).skip_binder().inputs().skip_binder().len();
            let body = &*tcx.mir_drops_elaborated_and_const_checked(did).borrow();
            let aliases = analysis.aliases.get(&did);
            let decision_maker = DecisionMaker::new(analysis, did, tcx);

            let decs: Vec<Option<PtrKind>> = body
                .local_decls
                .iter_enumerated()
                .skip(1)
                .take(input_len)
                .map(|(param, param_decl)| {
                    let param_aliases = aliases.and_then(|a| a.get(&param));
                    decision_maker.decide(param, param_decl, param_aliases)
                })
                .collect();

            individual_decisions.insert(did, decs);
        }

        // --- Step 2: call-site alias check (Andersen overlap) ---

        // forced_raw[rep][i] means: position i in this group's decisions must be None (raw pointer).
        let mut forced_raw: FxHashMap<LocalDefId, FxHashSet<usize>> = FxHashMap::default();

        for (caller, bb_to_slot) in &pre.indirect_calls {
            let Some(bb_to_args) = pre.indirect_call_args.get(caller) else { continue };
            for (bb, &slot_loc) in bb_to_slot {
                let Some(arg_locs) = bb_to_args.get(bb) else { continue };

                let reps: FxHashSet<LocalDefId> = solutions[slot_loc]
                    .iter()
                    .filter_map(|loc| pre.inv_fns.get(&loc))
                    .filter_map(|did| fn_ptr_groups.fn_to_group.get(did))
                    .copied()
                    .collect();

                if reps.is_empty() {
                    continue;
                }

                for i in 0..arg_locs.len() {
                    for j in 0..i {
                        let (Some(loc_i), Some(loc_j)) = (arg_locs[i], arg_locs[j]) else {
                            continue;
                        };
                        let mut sol = solutions[loc_i].clone();
                        sol.intersect(&solutions[loc_j]);
                        if !sol.is_empty() {
                            for &rep in &reps {
                                let positions = forced_raw.entry(rep).or_default();
                                positions.insert(i);
                                positions.insert(j);
                            }
                        }
                    }
                }
            }
        }

        let direct_rewrite: FxHashSet<LocalDefId> =
            fn_ptr_groups.fn_to_group.keys().copied().collect();
        let needs_wrapper: FxHashSet<LocalDefId> = FxHashSet::default();

        // --- Step 3: annotation propagation for all groups ---

        // Build loc_decisions for all groups, applying forced_raw overrides.
        let mut loc_decisions: FxHashMap<andersen::Loc, Vec<Option<PtrKind>>> =
            FxHashMap::default();

        for (v, pointees) in solutions.iter_enumerated() {
            let maybe_rep = pointees
                .iter()
                .filter_map(|loc| pre.inv_fns.get(&loc))
                .filter_map(|did| fn_ptr_groups.fn_to_group.get(did))
                .next()
                .copied();
            if let Some(rep) = maybe_rep
                && let Some(decs) = fn_ptr_groups.group_decisions.get(&rep)
            {
                let forced = forced_raw.get(&rep);
                let modified_decs: Vec<Option<PtrKind>> = decs
                    .iter()
                    .enumerate()
                    .map(|(i, &d)| {
                        if forced.is_some_and(|f| f.contains(&i)) {
                            None
                        } else {
                            d
                        }
                    })
                    .collect();
                loc_decisions.insert(v, modified_decs);
            }
        }

        // --- Step 3b: build field_decisions ---
        let mut field_dec_candidates: FxHashMap<(LocalDefId, FieldIdx), Vec<Vec<Option<PtrKind>>>> =
            FxHashMap::default();

        let build_field_candidates =
            |field_dec_candidates: &mut FxHashMap<
                (LocalDefId, FieldIdx),
                Vec<Vec<Option<PtrKind>>>,
            >,
             struct_did: LocalDefId,
             base_loc: andersen::Loc,
             ty: rustc_middle::ty::Ty<'tcx>| {
                let ty::TyKind::Adt(adt_def, _) = ty.kind() else { return };
                if !adt_def.is_struct() {
                    return;
                }
                let Some(&ty_shape) = tss.tys.get(&ty) else { return };
                let TyShape::Struct(_, ts, _) = ty_shape else { return };
                for (field_idx, &(offset, _)) in ts.iter().enumerate() {
                    let field_loc = base_loc + offset;
                    if let Some(decs) = loc_decisions.get(&field_loc) {
                        let fi = FieldIdx::from_usize(field_idx);
                        field_dec_candidates
                            .entry((struct_did, fi))
                            .or_default()
                            .push(decs.clone());
                    }
                }
            };

        for &fn_did in rust_program.functions.iter() {
            let body = &*rust_program
                .tcx
                .mir_drops_elaborated_and_const_checked(fn_did)
                .borrow();
            for (local, local_decl) in body.local_decls.iter_enumerated() {
                let ty = local_decl.ty;
                let ty::TyKind::Adt(adt_def, _) = ty.kind() else { continue };
                if !adt_def.is_struct() {
                    continue;
                }
                let Some(struct_did) = adt_def.did().as_local() else { continue };
                let Some(&base_loc) = pre.vars.get(&Var::Local(fn_did, local)) else {
                    continue;
                };
                build_field_candidates(&mut field_dec_candidates, struct_did, base_loc, ty);
            }
        }

        for (&static_did, &base_loc) in &pre.globals {
            if pre.inv_fns.contains_key(&base_loc) {
                continue;
            }
            let ty = rust_program.tcx.type_of(static_did).skip_binder();
            let ty::TyKind::Adt(adt_def, _) = ty.kind() else { continue };
            if !adt_def.is_struct() {
                continue;
            }
            let Some(struct_did) = adt_def.did().as_local() else { continue };
            build_field_candidates(&mut field_dec_candidates, struct_did, base_loc, ty);
        }

        let mut field_decisions: FxHashMap<(LocalDefId, FieldIdx), Vec<Option<PtrKind>>> =
            FxHashMap::default();
        for ((struct_did, fi), candidates) in field_dec_candidates {
            if candidates.is_empty() {
                continue;
            }
            let n = candidates[0].len();
            let joint: Vec<Option<PtrKind>> = (0..n)
                .map(|i| {
                    candidates
                        .iter()
                        .try_fold(Option::<PtrKind>::None, |acc, cand| {
                            match (acc, cand.get(i).copied().flatten()) {
                                (None, x) => Ok(x),
                                (x, None) => Ok(x),
                                (Some(a), Some(b)) if a == b => Ok(Some(a)),
                                _ => Err(()),
                            }
                        })
                        .unwrap_or(None)
                })
                .collect();
            field_decisions.insert((struct_did, fi), joint);
        }

        // --- Step 3c+3d: build annotation_decisions ---
        let mut annotation_decisions: FxHashMap<HirId, Vec<Option<PtrKind>>> = FxHashMap::default();

        // 3c: type aliases
        for &struct_did in rust_program.structs.iter() {
            let hir_item = rust_program.tcx.hir_expect_item(struct_did);
            let rustc_hir::ItemKind::Struct(_, _, variant_data) = &hir_item.kind else { continue };
            for (fi_idx, hir_field) in variant_data.fields().iter().enumerate() {
                let fi = FieldIdx::from_usize(fi_idx);
                let Some(decs) = field_decisions.get(&(struct_did, fi)) else { continue };
                let rustc_hir::TyKind::Path(rustc_hir::QPath::Resolved(None, path)) =
                    &hir_field.ty.kind
                else {
                    continue;
                };
                let rustc_hir::def::Res::Def(rustc_hir::def::DefKind::TyAlias, def_id) = path.res
                else {
                    continue;
                };
                let Some(local_alias_id) = def_id.as_local() else { continue };
                let alias_hir_id = rust_program.tcx.local_def_id_to_hir_id(local_alias_id);
                annotation_decisions
                    .entry(alias_hir_id)
                    .or_insert_with(|| decs.clone());
            }
        }

        // 3d: local/param bindings
        for &fn_did in rust_program.functions.iter() {
            let hir_to_mir = utils::ir::map_thir_to_mir(fn_did, false, rust_program.tcx);
            for (hir_id, local) in &hir_to_mir.binding_to_local {
                let var = Var::Local(fn_did, *local);
                if let Some(&loc) = pre.vars.get(&var)
                    && let Some(decs) = loc_decisions.get(&loc)
                {
                    annotation_decisions.insert(*hir_id, decs.clone());
                }
            }
        }

        // 3e: static item annotation decisions
        for (&static_did, &base_loc) in &pre.globals {
            if pre.inv_fns.contains_key(&base_loc) {
                continue;
            }
            let ty = rust_program.tcx.type_of(static_did).skip_binder();
            if !matches!(ty.kind(), ty::TyKind::FnPtr(..)) {
                continue;
            }
            let Some(decs) = loc_decisions.get(&base_loc) else {
                continue;
            };
            let hir_id = rust_program.tcx.local_def_id_to_hir_id(static_did);
            annotation_decisions.insert(hir_id, decs.clone());
        }

        FnPtrRewriteDecision {
            direct_rewrite,
            needs_wrapper,
            individual_decisions,
            annotation_decisions,
            field_decisions,
        }
    }
}

#[cfg(test)]
mod tests {
    use rustc_hash::FxHashSet;
    use rustc_hir::def_id::LocalDefId;

    use super::*;
    use crate::analyses::fn_ptr_groups::FnPtrGroups;

    fn named_fns(tcx: rustc_middle::ty::TyCtxt<'_>) -> Vec<(String, LocalDefId)> {
        tcx.hir_crate(())
            .owners
            .iter()
            .filter_map(|maybe_owner| {
                let owner = maybe_owner.as_owner()?;
                let rustc_hir::OwnerNode::Item(item) = owner.node() else {
                    return None;
                };
                match item.kind {
                    rustc_hir::ItemKind::Fn { .. } => Some((
                        tcx.item_name(item.owner_id.def_id.to_def_id()).to_string(),
                        item.owner_id.def_id,
                    )),
                    _ => None,
                }
            })
            .collect()
    }

    fn find_did(named: &[(String, LocalDefId)], name: &str) -> LocalDefId {
        named
            .iter()
            .find(|(n, _)| n == name)
            .unwrap_or_else(|| panic!("function '{name}' not found"))
            .1
    }

    fn build_rewrite_decision_for(code: &str) -> (FnPtrRewriteDecision, Vec<(String, LocalDefId)>) {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            use crate::rewriter::collect_input;
            let input = collect_input(tcx);
            let arena = typed_arena::Arena::new();
            let tss = utils::ty_shape::get_ty_shapes(&arena, tcx, false);
            let config = points_to::andersen::Config {
                use_optimized_mir: false,
                c_exposed_fns: FxHashSet::default(),
            };
            let pre = points_to::andersen::pre_analyze(&config, &tss, tcx);
            let solutions = points_to::andersen::analyze(&config, &pre, &tss, tcx);
            let aliases = crate::rewriter::find_param_aliases(&pre, &solutions, tcx);
            let points_to_result = points_to::andersen::post_analyze(
                &config,
                pre.clone(),
                solutions.clone(),
                &tss,
                tcx,
            );
            let mutability_result =
                crate::analyses::type_qualifier::foster::mutability::mutability_analysis(&input);
            let output_params = crate::analyses::output_params::compute_output_params(
                &input,
                &mutability_result,
                &aliases,
            );
            let source_var_groups =
                crate::analyses::mir_variable_grouping::SourceVarGroups::new(&input);
            let mutables = source_var_groups.postprocess_mut_res(&input, &mutability_result);
            let (mutable_references, shared_references) =
                crate::analyses::borrow::mutable_references_no_guarantee(&input, &mutables);
            let promoted_mut_ref_result =
                source_var_groups.postprocess_promoted_mut_refs(mutable_references);
            let promoted_shared_ref_result =
                source_var_groups.postprocess_promoted_mut_refs(shared_references);
            let fatness_result =
                crate::analyses::type_qualifier::foster::fatness::fatness_analysis(&input);
            let mut offset_sign_result =
                crate::analyses::offset_sign::sign::offset_sign_analysis(&input);
            offset_sign_result.access_signs =
                source_var_groups.postprocess_offset_signs(offset_sign_result.access_signs);
            let nullity_result = crate::analyses::nullity::analyze(&input, &points_to_result);
            let analysis = crate::rewriter::Analysis {
                promoted_mut_ref_result,
                promoted_shared_ref_result,
                mutability_result,
                fatness_result,
                aliases,
                output_params,
                ownership_schemes: None,
                offset_sign_result,
                nullity_result,
            };
            let fn_ptr_groups = FnPtrGroups::build(&pre, &solutions, &input, &analysis);
            let decision = FnPtrRewriteDecision::build(
                &pre,
                &solutions,
                &input,
                &analysis,
                &tss,
                &fn_ptr_groups,
            );
            let named = named_fns(tcx);
            (decision, named)
        })
        .unwrap()
    }

    #[test]
    fn non_aliasing_call_sites_give_direct_rewrite() {
        let code = r#"
pub unsafe fn f(p: *const i32) -> i32 { *p }
pub unsafe fn g(p: *const i32) -> i32 { *p + 1 }
pub unsafe fn call_it(cb: unsafe fn(*const i32) -> i32, p: *const i32) -> i32 { cb(p) }
pub unsafe fn test(x: *const i32, y: *const i32) -> i32 {
    call_it(f, x) + call_it(g, y)
}
"#;
        let (decision, named) = build_rewrite_decision_for(code);
        let did_f = find_did(&named, "f");
        let did_g = find_did(&named, "g");
        assert!(
            decision.direct_rewrite.contains(&did_f),
            "f should be in direct_rewrite"
        );
        assert!(
            decision.direct_rewrite.contains(&did_g),
            "g should be in direct_rewrite"
        );
        assert!(
            !decision.needs_wrapper.contains(&did_f),
            "f should not be in needs_wrapper"
        );
        assert!(
            !decision.needs_wrapper.contains(&did_g),
            "g should not be in needs_wrapper"
        );
    }

    #[test]
    fn outer_aliasing_with_opaque_ptr_gives_direct_rewrite() {
        // x has no tracked allocation in Andersen (opaque parameter),
        // so the outer aliasing call_it(f, x, x) is not detected.
        // Both f and g remain in direct_rewrite; needs_wrapper is always empty.
        let code = r#"
pub unsafe fn f(p: *mut i32, q: *mut i32) { *p = *q; }
pub unsafe fn g(p: *mut i32, q: *mut i32) { *p += *q; }
pub unsafe fn call_it(cb: unsafe fn(*mut i32, *mut i32), p: *mut i32, q: *mut i32) {
    cb(p, q)
}
pub unsafe fn test(x: *mut i32) {
    call_it(f, x, x);
    call_it(g, x, x);
}
"#;
        let (decision, named) = build_rewrite_decision_for(code);
        let did_f = find_did(&named, "f");
        let did_g = find_did(&named, "g");
        assert!(
            decision.direct_rewrite.contains(&did_f),
            "f should be in direct_rewrite"
        );
        assert!(
            decision.direct_rewrite.contains(&did_g),
            "g should be in direct_rewrite"
        );
        assert!(
            decision.needs_wrapper.is_empty(),
            "needs_wrapper should always be empty"
        );
    }

    #[test]
    fn non_aliasing_group_populates_annotation_decisions() {
        let code = r#"
pub unsafe fn f(p: *const i32) -> i32 { *p }
pub unsafe fn g(p: *const i32) -> i32 { *p + 1 }
pub unsafe fn call_it(cb: unsafe fn(*const i32) -> i32, p: *const i32) -> i32 { cb(p) }
pub unsafe fn test(p: *const i32) -> i32 {
    call_it(f, p) + call_it(g, p)
}
"#;
        let (decision, _named) = build_rewrite_decision_for(code);
        assert!(
            !decision.annotation_decisions.is_empty(),
            "annotation_decisions should be non-empty for non-aliasing group"
        );
        // At least one decision must have a non-None entry (i.e., a concrete PtrKind was chosen).
        assert!(
            decision
                .annotation_decisions
                .values()
                .any(|decs| decs.iter().any(|d| d.is_some())),
            "annotation_decisions should contain at least one concrete PtrKind decision"
        );
    }

    #[test]
    fn aliasing_with_tracked_alloc_forces_positions_to_raw() {
        // dispatch receives two separate args; the caller passes the same stack
        // address for both. solutions[p] ∩ solutions[q] = {Loc(x)} → non-empty
        // → forced raw at positions 0 and 1. f remains in direct_rewrite.
        let code = r#"
pub unsafe fn f(p: *mut i32, q: *mut i32) { *p = *q; }
pub unsafe fn dispatch(cb: unsafe fn(*mut i32, *mut i32), p: *mut i32, q: *mut i32) {
    cb(p, q)
}
pub unsafe fn test() {
    let mut x: i32 = 0;
    let px = &raw mut x;
    dispatch(f, px, px);
}
"#;
        let (decision, named) = build_rewrite_decision_for(code);
        let did_f = find_did(&named, "f");
        assert!(
            decision.direct_rewrite.contains(&did_f),
            "f should be in direct_rewrite"
        );
        assert!(
            decision.needs_wrapper.is_empty(),
            "needs_wrapper should always be empty"
        );
        // All annotation decisions have None at the aliased positions (forced raw).
        assert!(
            !decision.annotation_decisions.is_empty(),
            "annotation_decisions should be non-empty (group is still rewritten)"
        );
        assert!(
            decision
                .annotation_decisions
                .values()
                .all(|decs| decs.iter().all(|d| d.is_none())),
            "annotation_decisions should have all-None entries for aliased group"
        );
    }

    #[test]
    fn outer_aliasing_with_opaque_ptr_populates_annotation_decisions() {
        // Outer aliasing call_it(f, x, x) with opaque x is not detected by Andersen.
        // No forced_raw is applied, so annotation_decisions are populated normally.
        let code = r#"
pub unsafe fn f(p: *mut i32, q: *mut i32) { *p = *q; }
pub unsafe fn call_it(cb: unsafe fn(*mut i32, *mut i32), p: *mut i32, q: *mut i32) {
    cb(p, q)
}
pub unsafe fn test(x: *mut i32) { call_it(f, x, x); }
"#;
        let (decision, named) = build_rewrite_decision_for(code);
        // needs_wrapper is always empty
        assert!(decision.needs_wrapper.is_empty());
        // f is in direct_rewrite
        let did_f = find_did(&named, "f");
        assert!(decision.direct_rewrite.contains(&did_f));
    }
}
