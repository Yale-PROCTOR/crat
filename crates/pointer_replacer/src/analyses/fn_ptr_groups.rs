use points_to::andersen;
use rustc_hash::FxHashMap;
use rustc_hir::def_id::LocalDefId;

use crate::{
    rewriter::{
        Analysis,
        decision::{DecisionMaker, PtrKind},
    },
    utils::{dsa::union_find::UnionFind, rustc::RustProgram},
};

rustc_index::newtype_index! {
    struct FnPtrIdx {}
}

#[derive(Default)]
pub struct FnPtrGroups {
    /// maps each fn-ptr-participating function to its group representative
    pub fn_to_group: FxHashMap<LocalDefId, LocalDefId>,
    /// maps group representative to joint per-parameter input decisions
    pub group_decisions: FxHashMap<LocalDefId, Vec<Option<PtrKind>>>,
}

impl FnPtrGroups {
    pub fn build<'tcx>(
        pre: &andersen::PreAnalysisData<'tcx>,
        solutions: &andersen::Solutions,
        rust_program: &RustProgram<'tcx>,
        analysis: &Analysis,
    ) -> Self {
        // --- Step 1: collect participants and build union-find ---

        // Gather all LocalDefIds from inv_fns that are also in rust_program.functions
        let fn_set: FxHashMap<LocalDefId, ()> =
            rust_program.functions.iter().map(|&d| (d, ())).collect();
        let true_fn_ptr_set = crate::rewriter::collector::collect_fn_ptrs(rust_program);
        let mut participants: Vec<LocalDefId> = true_fn_ptr_set
            .iter()
            .copied()
            .filter(|d| fn_set.contains_key(d))
            .collect();
        participants.sort_unstable_by_key(|d| d.local_def_index);

        if participants.is_empty() {
            return FnPtrGroups::default();
        }

        let did_to_idx: FxHashMap<LocalDefId, FnPtrIdx> = participants
            .iter()
            .enumerate()
            .map(|(i, &did)| (did, FnPtrIdx::from_usize(i)))
            .collect();
        let mut uf = UnionFind::<FnPtrIdx>::new(participants.len());

        for (_, pointees) in solutions.iter_enumerated() {
            let fn_idxs: Vec<FnPtrIdx> = pointees
                .iter()
                .filter_map(|loc| pre.inv_fns.get(&loc))
                .filter_map(|did| did_to_idx.get(did).copied())
                .collect();
            if fn_idxs.len() >= 2 {
                let first = fn_idxs[0];
                for &other in &fn_idxs[1..] {
                    uf.union(first, other);
                }
            }
        }

        let mut fn_to_group: FxHashMap<LocalDefId, LocalDefId> = FxHashMap::default();
        for &did in &participants {
            let idx = did_to_idx[&did];
            let rep_idx = uf.find(idx);
            let rep_did = participants[rep_idx.index()];
            fn_to_group.insert(did, rep_did);
        }

        // --- Step 2: compute joint decisions per group ---

        // Collect members per group representative
        let mut group_members: FxHashMap<LocalDefId, Vec<LocalDefId>> = FxHashMap::default();
        for (&did, &rep) in &fn_to_group {
            group_members.entry(rep).or_default().push(did);
        }

        let mut group_decisions: FxHashMap<LocalDefId, Vec<Option<PtrKind>>> = FxHashMap::default();

        for (rep, members) in &group_members {
            let tcx = rust_program.tcx;
            let input_len = tcx.fn_sig(*rep).skip_binder().inputs().skip_binder().len();

            let mut all_input_decs: Vec<Vec<Option<PtrKind>>> = Vec::new();

            for &did in members {
                let decision_maker = DecisionMaker::new(analysis, did, tcx);
                let body = &*tcx.mir_drops_elaborated_and_const_checked(did).borrow();
                let aliases = analysis.aliases.get(&did);

                let member_input_decs: Vec<Option<PtrKind>> = body
                    .local_decls
                    .iter_enumerated()
                    .skip(1)
                    .take(input_len)
                    .map(|(param, param_decl)| {
                        let param_aliases = aliases.and_then(|a| a.get(&param));
                        decision_maker.decide(param, param_decl, param_aliases)
                    })
                    .collect();
                all_input_decs.push(member_input_decs);
            }

            // Intersect: position i gets Some(k) only if ALL members agree on k
            let joint_inputs: Vec<Option<PtrKind>> = (0..input_len)
                .map(|i| {
                    let mut agreed: Option<PtrKind> = None;
                    for member_decs in &all_input_decs {
                        let dec = member_decs.get(i).copied().flatten();
                        match (agreed, dec) {
                            (_, None) => return None,
                            (Some(k), _) | (_, Some(k)) if k.is_owning_box_like() => return None,
                            (None, Some(k)) => agreed = Some(k),
                            (Some(a), Some(b)) if a == b => {}
                            _ => return None,
                        }
                    }
                    agreed
                })
                .collect();

            group_decisions.insert(*rep, joint_inputs);
        }

        FnPtrGroups {
            fn_to_group,
            group_decisions,
        }
    }
}

#[cfg(test)]
mod tests {
    use rustc_hir::def_id::LocalDefId;

    use super::*;
    use crate::rewriter::{Config, replace_local_borrows};

    fn rewrite(code: &str) -> String {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            replace_local_borrows(&Config::default(), tcx).0
        })
        .unwrap()
    }

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

    fn build_groups_for(code: &str) -> (FnPtrGroups, Vec<(String, LocalDefId)>) {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            use rustc_hash::FxHashSet;

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
            let groups = FnPtrGroups::build(&pre, &solutions, &input, &analysis);
            let named = named_fns(tcx);
            (groups, named)
        })
        .unwrap()
    }

    #[test]
    fn two_fns_sharing_a_slot_are_grouped() {
        let code = r#"
pub unsafe fn f(p: *const i32) -> i32 { *p }
pub unsafe fn g(p: *const i32) -> i32 { *p + 1 }
pub unsafe fn call_it(cb: unsafe fn(*const i32) -> i32, p: *const i32) -> i32 { cb(p) }
pub unsafe fn test(p: *const i32) -> i32 {
    call_it(f, p) + call_it(g, p)
}
"#;
        let (groups, named) = build_groups_for(code);
        let did_f = find_did(&named, "f");
        let did_g = find_did(&named, "g");
        assert!(
            groups.fn_to_group.contains_key(&did_f),
            "f should be a participant"
        );
        assert!(
            groups.fn_to_group.contains_key(&did_g),
            "g should be a participant"
        );
        let rep_f = groups.fn_to_group[&did_f];
        let rep_g = groups.fn_to_group[&did_g];
        assert_eq!(rep_f, rep_g, "f and g should share a group representative");
    }

    #[test]
    fn unrelated_fn_is_not_grouped_with_fn_ptr_fns() {
        let code = r#"
pub unsafe fn f(p: *const i32) -> i32 { *p }
pub unsafe fn g(p: *const i32) -> i32 { *p + 1 }
pub unsafe fn standalone(p: *const i32) -> i32 { *p * 2 }
pub unsafe fn call_it(cb: unsafe fn(*const i32) -> i32, p: *const i32) -> i32 { cb(p) }
pub unsafe fn test(p: *const i32) -> i32 {
    call_it(f, p) + call_it(g, p)
}
"#;
        let (groups, named) = build_groups_for(code);
        let did_f = find_did(&named, "f");
        let did_g = find_did(&named, "g");
        let did_standalone = find_did(&named, "standalone");
        let rep_f = groups.fn_to_group[&did_f];
        let rep_g = groups.fn_to_group[&did_g];
        assert_eq!(rep_f, rep_g, "f and g should share a group representative");
        if let Some(&rep_standalone) = groups.fn_to_group.get(&did_standalone) {
            assert_ne!(
                rep_standalone, rep_f,
                "standalone should not be grouped with f/g"
            );
        }
    }

    #[test]
    fn two_fns_sharing_slot_get_ref_param() {
        let code = r#"
pub unsafe fn f(p: *const i32) -> i32 { *p }
pub unsafe fn g(p: *const i32) -> i32 { *p + 1 }
pub unsafe fn call_it(cb: unsafe fn(*const i32) -> i32, p: *const i32) -> i32 { cb(p) }
pub unsafe fn test(p: *const i32) -> i32 {
    call_it(f, p) + call_it(g, p)
}
"#;
        let (groups, named) = build_groups_for(code);
        let did_f = find_did(&named, "f");
        let rep = groups.fn_to_group[&did_f];
        let decs = groups
            .group_decisions
            .get(&rep)
            .expect("group should have decisions");
        // both f and g take *const i32 as shared borrows → joint decision should be Ref(false)
        assert_eq!(decs.len(), 1, "one parameter");
        assert_eq!(
            decs[0],
            Some(PtrKind::Ref(false)),
            "expected Ref(false) for *const i32 param"
        );
    }

    #[test]
    fn fn_ptr_group_params_rewritten_to_ref() {
        let code = r#"
pub unsafe fn f(p: *const i32) -> i32 { *p }
pub unsafe fn g(p: *const i32) -> i32 { *p + 1 }
pub unsafe fn call_it(cb: unsafe fn(*const i32) -> i32, p: *const i32) -> i32 { cb(p) }
pub unsafe fn test(p: *const i32) -> i32 {
    call_it(f, p) + call_it(g, p)
}
"#;
        let rewritten = rewrite(code);
        // f and g should have their *const i32 param rewritten to &i32
        assert!(
            rewritten.contains("fn f(p: &i32)"),
            "expected f's param rewritten to &i32, got:\n{rewritten}"
        );
        assert!(
            rewritten.contains("fn g(p: &i32)"),
            "expected g's param rewritten to &i32, got:\n{rewritten}"
        );
        // call_it's cb parameter type should be updated
        assert!(
            rewritten.contains("fn(&i32)"),
            "expected call_it's cb type rewritten to fn(&i32), got:\n{rewritten}"
        );
    }

    #[test]
    fn indirect_call_arguments_are_adapted() {
        let code = r#"
pub unsafe fn f(p: *const i32) -> i32 { *p }
pub unsafe fn g(p: *const i32) -> i32 { *p + 1 }
pub unsafe fn call_it(cb: unsafe fn(*const i32) -> i32, p: *const i32) -> i32 { cb(p) }
pub unsafe fn test(p: *const i32) -> i32 {
    call_it(f, p) + call_it(g, p)
}
"#;
        let rewritten = rewrite(code);
        // the call cb(p) inside call_it should pass p directly (p is now &i32)
        // call_it(f, p) at the call site should pass p directly
        assert!(
            !rewritten.contains("cb(&raw const"),
            "expected no raw cast in indirect call, got:\n{rewritten}"
        );
    }

    #[test]
    fn fns_sharing_a_slot_are_grouped_even_without_a_call() {
        // f and g are both coerced to fn-ptr type and stored into the same slot.
        // they SHOULD be grouped — sharing a storage slot implies compatible APIs,
        // regardless of whether the slot is ever called through.
        let code = r#"
pub unsafe fn f(p: *const i32) -> i32 { *p }
pub unsafe fn g(p: *const i32) -> i32 { *p + 1 }
pub unsafe fn store_only(p: *const i32) -> i32 {
    let mut slot: Option<unsafe fn(*const i32) -> i32> = None;
    slot = Some(f);
    slot = Some(g);
    // slot is never called — only assigned
    f(p) + g(p)
}
"#;
        let (groups, named) = build_groups_for(code);
        let did_f = find_did(&named, "f");
        let did_g = find_did(&named, "g");
        let rep_f = groups.fn_to_group.get(&did_f).copied();
        let rep_g = groups.fn_to_group.get(&did_g).copied();
        assert!(
            rep_f.is_some() && rep_f == rep_g,
            "f and g must share a group because both are stored in the same fn-ptr slot"
        );
    }

    #[test]
    fn static_fn_ptr_type_annotation_is_rewritten() {
        // f is grouped (used as fn-ptr via call_it) and stored in a static CB.
        // Because f is in the group, CB's annotation must change from
        //   `unsafe fn(*const i32) -> i32`  to  `unsafe fn(&i32) -> i32`.
        // The assertion checks for "CB:" near the rewritten type to ensure it is
        // the static's annotation specifically, not any other fn(&i32) in the output.
        let code = r#"
pub unsafe fn f(p: *const i32) -> i32 { *p }
static CB: unsafe fn(*const i32) -> i32 = f;
pub unsafe fn call_it(cb: unsafe fn(*const i32) -> i32, p: *const i32) -> i32 { cb(p) }
pub unsafe fn use_all(p: *const i32) -> i32 { call_it(f, p) }
"#;
        let rewritten = rewrite(code);
        assert!(
            rewritten.contains("CB: unsafe fn(&i32)"),
            "expected static CB type annotation rewritten to unsafe fn(&i32), got:\n{rewritten}"
        );
    }

    #[test]
    fn aliasing_indirect_call_args_keep_annotation_raw() {
        // x is passed twice to the same call site through a fn-ptr → aliased.
        // The fn-ptr type annotation must NOT be rewritten to &mut i32
        // because that would create two aliased &mut references (UB).
        let code = r#"
pub unsafe fn f(p: *mut i32, q: *mut i32) { *p = *q; }
pub unsafe fn call_it(cb: unsafe fn(*mut i32, *mut i32), p: *mut i32, q: *mut i32) {
    cb(p, q)
}
pub unsafe fn test(x: *mut i32) { call_it(f, x, x); }
"#;
        let rewritten = rewrite(code);
        assert!(
            !rewritten.contains("fn(&mut i32, &mut i32)"),
            "aliased call site must not rewrite fn-ptr annotation to mut refs:\n{rewritten}"
        );
    }
}
