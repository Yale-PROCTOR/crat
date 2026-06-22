use points_to::andersen::{self, Var};
use rustc_abi::FieldIdx;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    self as hir, HirId,
    def::{DefKind, Res},
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty;
use rustc_span::{Symbol, sym};
use utils::{
    ir::is_option,
    ty_shape::{TyShape, TyShapes},
};

use crate::{
    analyses::fn_ptr_groups::FnPtrGroups,
    rewriter::{
        Analysis,
        decision::{DecisionMaker, PtrKind, SigDecisions},
    },
    utils::rustc::RustProgram,
};

#[derive(Default)]
pub struct FnPtrRewriteDecision {
    pub direct_rewrite: FxHashSet<LocalDefId>,
    #[allow(dead_code)] // used in Phase 2 wrapper generation
    pub needs_wrapper: FxHashSet<LocalDefId>,
    /// maps each rewritten fn-ptr-participating function to its group representative
    pub fn_to_group: FxHashMap<LocalDefId, LocalDefId>,
    /// Canonical final per-parameter input decisions per fn-ptr group.
    pub group_decisions: FxHashMap<LocalDefId, Vec<Option<PtrKind>>>,
    /// Per-parameter individual decisions per fn-ptr function (ignoring group consensus).
    #[allow(dead_code)]
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
        c_exposed_fns: &FxHashSet<String>,
    ) -> Self {
        let tcx = rust_program.tcx;

        if fn_ptr_groups.fn_to_group.is_empty() {
            return FnPtrRewriteDecision {
                direct_rewrite: FxHashSet::default(),
                needs_wrapper: FxHashSet::default(),
                fn_to_group: FxHashMap::default(),
                group_decisions: FxHashMap::default(),
                individual_decisions: FxHashMap::default(),
                annotation_decisions: FxHashMap::default(),
                field_decisions: FxHashMap::default(),
            };
        }

        // --- Step 1: compute individual decisions per fn-ptr function ---
        let mut individual_decisions: FxHashMap<LocalDefId, Vec<Option<PtrKind>>> =
            FxHashMap::default();
        let enum_payload_raw_inputs =
            crate::rewriter::collector::collect_unsupported_enum_payload_fn_ptr_raw_inputs(
                rust_program,
            );

        for &did in fn_ptr_groups.fn_to_group.keys() {
            let input_len = tcx.fn_sig(did).skip_binder().inputs().skip_binder().len();
            let body = &*tcx.mir_drops_elaborated_and_const_checked(did).borrow();
            let aliases = analysis.aliases.get(&did);
            let decision_maker = DecisionMaker::new(analysis, did, tcx);
            let raw_inputs = enum_payload_raw_inputs.get(&did);

            let decs: Vec<Option<PtrKind>> = body
                .local_decls
                .iter_enumerated()
                .skip(1)
                .take(input_len)
                .enumerate()
                .map(|(idx, (param, param_decl))| {
                    if raw_inputs.is_some_and(|inputs| inputs.contains(&idx)) {
                        return raw_input_decision(tcx, did, idx);
                    }
                    let param_aliases = aliases.and_then(|a| a.get(&param));
                    decision_maker.decide(param, param_decl, param_aliases)
                })
                .collect();

            individual_decisions.insert(did, decs);
        }

        // --- Step 2: call-site alias check (Andersen overlap) ---

        // forced_raw[rep][i] means: position i in this group's decisions must be raw.
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
        let final_group_decisions: FxHashMap<LocalDefId, Vec<Option<PtrKind>>> = fn_ptr_groups
            .group_decisions
            .iter()
            .map(|(&rep, decs)| {
                let forced = forced_raw.get(&rep);
                let modified_decs = decs
                    .iter()
                    .enumerate()
                    .map(|(i, &d)| {
                        if forced.is_some_and(|f| f.contains(&i)) {
                            Some(raw_group_input_decision(tcx, fn_ptr_groups, rep, i))
                        } else {
                            d
                        }
                    })
                    .collect();
                (rep, modified_decs)
            })
            .collect();

        let mut decision = FnPtrRewriteDecision {
            direct_rewrite,
            needs_wrapper,
            fn_to_group: fn_ptr_groups.fn_to_group.clone(),
            group_decisions: final_group_decisions,
            individual_decisions,
            annotation_decisions: FxHashMap::default(),
            field_decisions: FxHashMap::default(),
        };
        decision.force_raw_boundary_contracts(rust_program, fn_ptr_groups, c_exposed_fns);
        decision.rebuild_site_decisions(
            pre,
            solutions,
            rust_program,
            tss,
            fn_ptr_groups,
            c_exposed_fns,
        );
        decision
    }

    pub fn sync_from_sig_decs<'tcx>(
        &mut self,
        rust_program: &RustProgram<'tcx>,
        fn_ptr_groups: &FnPtrGroups,
        sig_decs: &mut SigDecisions,
        c_exposed_fns: &FxHashSet<String>,
    ) -> bool {
        let tcx = rust_program.tcx;
        let mut changed = false;
        let mut group_members: FxHashMap<LocalDefId, Vec<LocalDefId>> = FxHashMap::default();
        for (&did, &rep) in &fn_ptr_groups.fn_to_group {
            group_members.entry(rep).or_default().push(did);
        }

        let mut synced_group_decisions = self.group_decisions.clone();
        for (&rep, members) in &group_members {
            let input_len = tcx.fn_sig(rep).skip_binder().inputs().skip_binder().len();
            let mut group_decs = vec![None; input_len];
            for idx in 0..input_len {
                let mut dec = self
                    .group_decisions
                    .get(&rep)
                    .and_then(|decs| decs.get(idx).copied())
                    .flatten();
                for &did in members {
                    let member_dec = sig_decs
                        .data
                        .get(&did)
                        .and_then(|sig| sig.input_decs.get(idx).copied())
                        .flatten()
                        .or_else(|| raw_input_decision(tcx, did, idx));
                    merge_contract_decision(
                        &mut dec,
                        member_dec,
                        Some(raw_group_input_decision(tcx, fn_ptr_groups, rep, idx)),
                    );
                }
                group_decs[idx] = dec;
            }
            synced_group_decisions.insert(rep, group_decs);
        }
        if self.group_decisions != synced_group_decisions {
            self.group_decisions = synced_group_decisions;
            changed = true;
        }

        self.force_raw_boundary_contracts(rust_program, fn_ptr_groups, c_exposed_fns);

        for (&did, &rep) in &fn_ptr_groups.fn_to_group {
            let Some(group_decs) = self.group_decisions.get(&rep) else { continue };
            let Some(sig_dec) = sig_decs.data.get_mut(&did) else { continue };
            if sig_dec.signature_locked {
                continue;
            }
            for (idx, &group_dec) in group_decs.iter().enumerate() {
                let Some(group_dec) = group_dec else { continue };
                if sig_dec.input_decs.get(idx).copied().flatten() != Some(group_dec) {
                    sig_dec.set_input_dec(idx, Some(group_dec));
                    changed = true;
                }
            }
        }
        changed
    }

    pub fn rebuild_site_decisions<'tcx>(
        &mut self,
        pre: &andersen::PreAnalysisData<'tcx>,
        solutions: &andersen::Solutions,
        rust_program: &RustProgram<'tcx>,
        tss: &TyShapes<'_, 'tcx>,
        fn_ptr_groups: &FnPtrGroups,
        c_exposed_fns: &FxHashSet<String>,
    ) {
        let tcx = rust_program.tcx;

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
                && let Some(decs) = self.group_decisions.get(&rep)
            {
                loc_decisions.insert(v, decs.clone());
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

        for (field, decs) in collect_c_exposed_fn_ptr_fields(rust_program, c_exposed_fns) {
            field_dec_candidates.entry(field).or_default().push(decs);
        }

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

        struct FieldInitVisitor<'a, 'tcx> {
            tcx: ty::TyCtxt<'tcx>,
            fn_ptr_groups: &'a FnPtrGroups,
            group_decisions: &'a FxHashMap<LocalDefId, Vec<Option<PtrKind>>>,
            field_dec_candidates:
                &'a mut FxHashMap<(LocalDefId, FieldIdx), Vec<Vec<Option<PtrKind>>>>,
        }

        impl<'tcx> Visitor<'tcx> for FieldInitVisitor<'_, 'tcx> {
            fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
                if let hir::ExprKind::Struct(qpath, fields, _) = expr.kind
                    && let Some(struct_did) = hir_local_struct_did_from_qpath(qpath)
                {
                    for field in fields {
                        let Some(field_idx) =
                            hir_field_index_by_name(self.tcx, struct_did, field.ident.name)
                        else {
                            continue;
                        };
                        let Some(decs) = fn_ptr_decisions_for_expr(
                            self.tcx,
                            field.expr,
                            self.fn_ptr_groups,
                            self.group_decisions,
                        ) else {
                            continue;
                        };
                        self.field_dec_candidates
                            .entry((struct_did, field_idx))
                            .or_default()
                            .push(decs);
                    }
                }
                intravisit::walk_expr(self, expr);
            }
        }

        {
            let mut visitor = FieldInitVisitor {
                tcx,
                fn_ptr_groups,
                group_decisions: &self.group_decisions,
                field_dec_candidates: &mut field_dec_candidates,
            };
            for def_id in tcx.hir_body_owners() {
                let body = tcx.hir_body_owned_by(def_id);
                visitor.visit_body(body);
            }
        }

        let mut field_decisions: FxHashMap<(LocalDefId, FieldIdx), Vec<Option<PtrKind>>> =
            FxHashMap::default();
        for ((struct_did, fi), candidates) in field_dec_candidates {
            if candidates.is_empty() {
                continue;
            }
            let mut joint = candidates[0].clone();
            for candidate in &candidates[1..] {
                merge_decisions_conservatively(&mut joint, candidate);
            }
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
                insert_alias_decisions_for_ty(tcx, &mut annotation_decisions, hir_field.ty, decs);
            }
        }

        struct BindingInitVisitor<'a, 'tcx> {
            tcx: ty::TyCtxt<'tcx>,
            fn_ptr_groups: &'a FnPtrGroups,
            group_decisions: &'a FxHashMap<LocalDefId, Vec<Option<PtrKind>>>,
            field_decisions: &'a FxHashMap<(LocalDefId, FieldIdx), Vec<Option<PtrKind>>>,
            annotation_decisions: &'a mut FxHashMap<HirId, Vec<Option<PtrKind>>>,
        }

        impl<'tcx> Visitor<'tcx> for BindingInitVisitor<'_, 'tcx> {
            fn visit_local(&mut self, let_stmt: &'tcx hir::LetStmt<'tcx>) -> Self::Result {
                if let hir::PatKind::Binding(_, binding_hir_id, _, _) = let_stmt.pat.kind {
                    let init_decs = let_stmt.init.and_then(|init| {
                        field_fn_ptr_decisions_for_expr(self.tcx, init, self.field_decisions)
                            .or_else(|| {
                                fn_ptr_decisions_for_expr(
                                    self.tcx,
                                    init,
                                    self.fn_ptr_groups,
                                    self.group_decisions,
                                )
                            })
                    });
                    if let Some(decs) = init_decs {
                        insert_annotation_decision(
                            self.annotation_decisions,
                            binding_hir_id,
                            &decs,
                        );
                        if let Some(ty) = let_stmt.ty {
                            insert_alias_decisions_for_ty(
                                self.tcx,
                                self.annotation_decisions,
                                ty,
                                &decs,
                            );
                        }
                    }
                }
                intravisit::walk_local(self, let_stmt);
            }
        }

        {
            let mut visitor = BindingInitVisitor {
                tcx,
                fn_ptr_groups,
                group_decisions: &self.group_decisions,
                field_decisions: &field_decisions,
                annotation_decisions: &mut annotation_decisions,
            };
            for def_id in tcx.hir_body_owners() {
                let body = tcx.hir_body_owned_by(def_id);
                visitor.visit_body(body);
            }
        }

        struct CallParamVisitor<'a, 'tcx> {
            tcx: ty::TyCtxt<'tcx>,
            fn_ptr_groups: &'a FnPtrGroups,
            group_decisions: &'a FxHashMap<LocalDefId, Vec<Option<PtrKind>>>,
            field_decisions: &'a FxHashMap<(LocalDefId, FieldIdx), Vec<Option<PtrKind>>>,
            annotation_decisions: &'a mut FxHashMap<HirId, Vec<Option<PtrKind>>>,
        }

        impl<'tcx> Visitor<'tcx> for CallParamVisitor<'_, 'tcx> {
            fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
                if let hir::ExprKind::Call(callee, args) = expr.kind
                    && let Some(callee_did) = hir_callee_local_def_id(callee)
                {
                    for (idx, arg) in args.iter().enumerate() {
                        let Some((param_hir_id, param_ty)) =
                            local_fn_param_hir(self.tcx, callee_did, idx)
                        else {
                            continue;
                        };
                        if !hir_ty_contains_fn_ptr(param_ty)
                            && collect_hir_ty_alias_def_ids_for_ty(param_ty).is_empty()
                        {
                            continue;
                        }
                        let arg_decs =
                            field_fn_ptr_decisions_for_expr(self.tcx, arg, self.field_decisions)
                                .or_else(|| {
                                    fn_ptr_decisions_for_expr(
                                        self.tcx,
                                        arg,
                                        self.fn_ptr_groups,
                                        self.group_decisions,
                                    )
                                });
                        let Some(decs) = arg_decs else { continue };
                        insert_annotation_decision(self.annotation_decisions, param_hir_id, &decs);
                        insert_alias_decisions_for_ty(
                            self.tcx,
                            self.annotation_decisions,
                            param_ty,
                            &decs,
                        );
                    }
                }
                intravisit::walk_expr(self, expr);
            }
        }

        {
            let mut visitor = CallParamVisitor {
                tcx,
                fn_ptr_groups,
                group_decisions: &self.group_decisions,
                field_decisions: &field_decisions,
                annotation_decisions: &mut annotation_decisions,
            };
            for def_id in tcx.hir_body_owners() {
                let body = tcx.hir_body_owned_by(def_id);
                visitor.visit_body(body);
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
                    insert_annotation_decision(&mut annotation_decisions, *hir_id, decs);
                }
            }
        }

        // 3e: static item annotation decisions
        for (&static_did, &base_loc) in &pre.globals {
            if pre.inv_fns.contains_key(&base_loc) {
                continue;
            }
            let ty = rust_program.tcx.type_of(static_did).skip_binder();
            if !ty_contains_fn_ptr(ty) {
                continue;
            }
            let Some(decs) = loc_decisions.get(&base_loc) else {
                continue;
            };
            let hir_id = rust_program.tcx.local_def_id_to_hir_id(static_did);
            insert_annotation_decision(&mut annotation_decisions, hir_id, decs);
        }

        // 3f: static/const item annotations whose initializer contains the function item.
        for item_id in tcx.hir_free_items() {
            let item = tcx.hir_item(item_id);
            let (ty, body_id) = match item.kind {
                hir::ItemKind::Static(_, _, ty, body_id)
                | hir::ItemKind::Const(_, _, ty, body_id) => (ty, body_id),
                _ => continue,
            };
            if !hir_ty_contains_fn_ptr(ty)
                && hir_ty_alias_def_id(ty).is_none()
                && !ty_contains_fn_ptr(tcx.type_of(item.owner_id.def_id).skip_binder())
            {
                continue;
            }
            let body = tcx.hir_body(body_id);
            let Some(decs) =
                fn_ptr_decisions_for_expr(tcx, body.value, fn_ptr_groups, &self.group_decisions)
            else {
                continue;
            };
            insert_annotation_decision(&mut annotation_decisions, item.hir_id(), &decs);
            insert_alias_decisions_for_ty(tcx, &mut annotation_decisions, ty, &decs);
        }

        propagate_return_alias_decisions(
            tcx,
            fn_ptr_groups,
            &self.group_decisions,
            &mut annotation_decisions,
        );
        propagate_alias_decisions(tcx, &mut annotation_decisions);

        self.annotation_decisions = annotation_decisions;
        self.field_decisions = field_decisions;
    }

    fn force_raw_boundary_contracts<'tcx>(
        &mut self,
        rust_program: &RustProgram<'tcx>,
        fn_ptr_groups: &FnPtrGroups,
        c_exposed_fns: &FxHashSet<String>,
    ) {
        force_mixed_foreign_contracts_raw(rust_program, fn_ptr_groups, &mut self.group_decisions);
        force_c_exposed_contracts_raw(
            rust_program,
            fn_ptr_groups,
            c_exposed_fns,
            &mut self.group_decisions,
        );
    }
}

fn insert_annotation_decision(
    annotation_decisions: &mut FxHashMap<HirId, Vec<Option<PtrKind>>>,
    hir_id: HirId,
    decs: &[Option<PtrKind>],
) {
    annotation_decisions
        .entry(hir_id)
        .and_modify(|existing| merge_decisions_conservatively(existing, decs))
        .or_insert_with(|| decs.to_vec());
}

fn merge_decisions_conservatively(
    existing: &mut Vec<Option<PtrKind>>,
    incoming: &[Option<PtrKind>],
) {
    if existing.len() != incoming.len() {
        let len = existing.len().max(incoming.len());
        *existing = vec![None; len];
        return;
    }
    for (existing, incoming) in existing.iter_mut().zip(incoming) {
        if *existing == *incoming {
            continue;
        }
        match (*existing, *incoming) {
            (Some(PtrKind::Raw(_)), _) => {}
            (_, Some(raw @ PtrKind::Raw(_))) => *existing = Some(raw),
            _ => *existing = None,
        }
    }
}

fn merge_contract_decision(
    existing: &mut Option<PtrKind>,
    incoming: Option<PtrKind>,
    raw_fallback: Option<PtrKind>,
) {
    match (*existing, incoming) {
        (_, None) => {}
        (None, Some(kind)) => *existing = Some(kind),
        (Some(existing_kind), Some(incoming_kind)) if existing_kind == incoming_kind => {}
        (Some(PtrKind::Raw(_)), Some(_)) => {}
        (Some(_), Some(raw @ PtrKind::Raw(_))) => *existing = Some(raw),
        (Some(_), Some(_)) => *existing = raw_fallback,
    }
}

fn raw_input_decision(tcx: ty::TyCtxt<'_>, did: LocalDefId, idx: usize) -> Option<PtrKind> {
    let sig = tcx.fn_sig(did).skip_binder().skip_binder();
    let input_ty = sig.inputs().get(idx)?;
    raw_input_decision_from_ty(*input_ty)
}

fn raw_input_decision_from_ty(ty: ty::Ty<'_>) -> Option<PtrKind> {
    let ty::TyKind::RawPtr(_, mutability) = ty.kind() else {
        return None;
    };
    Some(PtrKind::Raw(mutability.is_mut()))
}

fn raw_group_input_decision(
    tcx: ty::TyCtxt<'_>,
    fn_ptr_groups: &FnPtrGroups,
    rep: LocalDefId,
    idx: usize,
) -> PtrKind {
    let mut saw_const = false;
    for (&did, &member_rep) in &fn_ptr_groups.fn_to_group {
        if member_rep != rep {
            continue;
        }
        match raw_input_decision(tcx, did, idx) {
            Some(raw @ PtrKind::Raw(true)) => return raw,
            Some(PtrKind::Raw(false)) => saw_const = true,
            _ => {}
        }
    }
    PtrKind::Raw(!saw_const)
}

fn fn_ptr_input_decisions_from_ty<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
) -> Option<Vec<Option<PtrKind>>> {
    match ty.kind() {
        ty::TyKind::FnPtr(sig, _) => {
            let sig = sig.as_ref().skip_binder();
            Some(
                sig.inputs()
                    .iter()
                    .map(|input| raw_input_decision_from_ty(*input))
                    .collect(),
            )
        }
        ty::TyKind::Adt(adt_def, args) => {
            let mut found = None;
            for arg in args.iter() {
                if let ty::GenericArgKind::Type(arg_ty) = arg.kind()
                    && let Some(decs) = fn_ptr_input_decisions_from_ty(tcx, arg_ty)
                {
                    merge_decision_vec(&mut found, &decs);
                }
            }
            if found.is_none()
                && is_option(adt_def.did(), tcx)
                && let ty::GenericArgKind::Type(inner) = args[0].kind()
            {
                found = fn_ptr_input_decisions_from_ty(tcx, inner);
            }
            found
        }
        ty::TyKind::Tuple(tys) => {
            let mut found = None;
            for ty in tys.iter() {
                if let Some(decs) = fn_ptr_input_decisions_from_ty(tcx, ty) {
                    merge_decision_vec(&mut found, &decs);
                }
            }
            found
        }
        ty::TyKind::Array(inner, _) | ty::TyKind::Slice(inner) => {
            fn_ptr_input_decisions_from_ty(tcx, *inner)
        }
        ty::TyKind::RawPtr(inner, _) | ty::TyKind::Ref(_, inner, _) => {
            fn_ptr_input_decisions_from_ty(tcx, *inner)
        }
        _ => None,
    }
}

fn merge_decision_vec(existing: &mut Option<Vec<Option<PtrKind>>>, incoming: &[Option<PtrKind>]) {
    if let Some(existing) = existing {
        merge_decisions_conservatively(existing, incoming);
    } else {
        *existing = Some(incoming.to_vec());
    }
}

fn fn_ptr_decisions_for_expr<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    expr: &'tcx hir::Expr<'tcx>,
    fn_ptr_groups: &FnPtrGroups,
    final_group_decisions: &FxHashMap<LocalDefId, Vec<Option<PtrKind>>>,
) -> Option<Vec<Option<PtrKind>>> {
    struct FnPtrDecisionFinder<'a, 'tcx> {
        tcx: ty::TyCtxt<'tcx>,
        fn_ptr_groups: &'a FnPtrGroups,
        final_group_decisions: &'a FxHashMap<LocalDefId, Vec<Option<PtrKind>>>,
        found: Option<Vec<Option<PtrKind>>>,
    }

    impl<'tcx> Visitor<'tcx> for FnPtrDecisionFinder<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let Some(decs) = fn_ptr_decisions_for_leaf(
                self.tcx,
                expr,
                self.fn_ptr_groups,
                self.final_group_decisions,
            ) {
                merge_decision_vec(&mut self.found, &decs);
            }

            intravisit::walk_expr(self, expr);
        }
    }

    let mut visitor = FnPtrDecisionFinder {
        tcx,
        fn_ptr_groups,
        final_group_decisions,
        found: None,
    };
    visitor.visit_expr(expr);
    visitor.found
}

fn fn_ptr_decisions_for_leaf<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    expr: &'tcx hir::Expr<'tcx>,
    fn_ptr_groups: &FnPtrGroups,
    group_decisions: &FxHashMap<LocalDefId, Vec<Option<PtrKind>>>,
) -> Option<Vec<Option<PtrKind>>> {
    let def_id = fn_ptr_def_id_from_expr(expr)?;
    let typeck = tcx.typeck(expr.hir_id.owner);
    if !ty_contains_fn_ptr(typeck.expr_ty_adjusted(expr)) {
        return None;
    }
    if let Some(did) = def_id.as_local()
        && let Some(rep) = fn_ptr_groups.fn_to_group.get(&did)
    {
        return group_decisions.get(rep).cloned();
    }
    fn_ptr_input_decisions_from_ty(tcx, typeck.expr_ty_adjusted(expr))
}

fn fn_ptr_def_id_from_expr(expr: &hir::Expr<'_>) -> Option<rustc_hir::def_id::DefId> {
    let expr = utils::hir::unwrap_drop_temps(expr);
    if let hir::ExprKind::Path(ref qpath) = expr.kind
        && let hir::QPath::Resolved(_, path) = qpath
        && let Res::Def(DefKind::Fn | DefKind::AssocFn, def_id) = path.res
    {
        return Some(def_id);
    }
    if let hir::ExprKind::Cast(inner, ty) = expr.kind
        && hir_ty_contains_fn_ptr(ty)
    {
        let inner = utils::hir::unwrap_drop_temps(inner);
        if let hir::ExprKind::Path(ref qpath) = inner.kind
            && let hir::QPath::Resolved(_, path) = qpath
            && let Res::Def(DefKind::Fn | DefKind::AssocFn, def_id) = path.res
        {
            return Some(def_id);
        }
    }
    None
}

fn hir_local_struct_did_from_qpath(qpath: &hir::QPath<'_>) -> Option<LocalDefId> {
    let hir::QPath::Resolved(_, path) = qpath else {
        return None;
    };
    let Res::Def(DefKind::Struct, def_id) = path.res else {
        return None;
    };
    def_id.as_local()
}

fn hir_field_index_by_name(
    tcx: ty::TyCtxt<'_>,
    struct_did: LocalDefId,
    field_name: Symbol,
) -> Option<FieldIdx> {
    let idx = tcx
        .adt_def(struct_did)
        .non_enum_variant()
        .fields
        .iter()
        .position(|field| field.name == field_name)?;
    Some(FieldIdx::from_usize(idx))
}

fn field_fn_ptr_decisions_for_expr<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    expr: &'tcx hir::Expr<'tcx>,
    field_decisions: &FxHashMap<(LocalDefId, FieldIdx), Vec<Option<PtrKind>>>,
) -> Option<Vec<Option<PtrKind>>> {
    struct FieldDecisionFinder<'a, 'tcx> {
        tcx: ty::TyCtxt<'tcx>,
        field_decisions: &'a FxHashMap<(LocalDefId, FieldIdx), Vec<Option<PtrKind>>>,
        found: Option<Vec<Option<PtrKind>>>,
    }

    impl<'tcx> Visitor<'tcx> for FieldDecisionFinder<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if self.found.is_some() {
                return;
            }

            if let hir::ExprKind::Field(struct_expr, field_ident) =
                utils::hir::unwrap_drop_temps(expr).kind
            {
                let typeck = self.tcx.typeck(expr.hir_id.owner);
                let struct_ty = typeck.expr_ty_adjusted(struct_expr);
                if let ty::TyKind::Adt(adt_def, _) = struct_ty.kind()
                    && adt_def.is_struct()
                    && let Some(struct_did) = adt_def.did().as_local()
                    && let Some(field_idx) =
                        hir_field_index_by_name(self.tcx, struct_did, field_ident.name)
                    && let Some(decs) = self.field_decisions.get(&(struct_did, field_idx))
                {
                    self.found = Some(decs.clone());
                    return;
                }
            }

            intravisit::walk_expr(self, expr);
        }
    }

    let mut visitor = FieldDecisionFinder {
        tcx,
        field_decisions,
        found: None,
    };
    visitor.visit_expr(expr);
    visitor.found
}

fn force_mixed_foreign_contracts_raw<'tcx>(
    rust_program: &RustProgram<'tcx>,
    fn_ptr_groups: &FnPtrGroups,
    group_decisions: &mut FxHashMap<LocalDefId, Vec<Option<PtrKind>>>,
) {
    struct MixedForeignVisitor<'a, 'tcx> {
        tcx: ty::TyCtxt<'tcx>,
        fn_ptr_groups: &'a FnPtrGroups,
        group_decisions: &'a mut FxHashMap<LocalDefId, Vec<Option<PtrKind>>>,
    }

    impl<'tcx> Visitor<'tcx> for MixedForeignVisitor<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if matches!(
                expr.kind,
                hir::ExprKind::If(..)
                    | hir::ExprKind::Match(..)
                    | hir::ExprKind::Tup(..)
                    | hir::ExprKind::Array(..)
                    | hir::ExprKind::Struct(..)
            ) {
                let local_fns = local_fn_ptr_group_fns_in_expr(self.tcx, expr, self.fn_ptr_groups);
                let foreign_decs =
                    foreign_fn_ptr_raw_decisions_in_expr(self.tcx, expr, self.fn_ptr_groups);
                if let Some(foreign_decs) = foreign_decs
                    && !local_fns.is_empty()
                {
                    force_fns_to_raw_contract(
                        self.tcx,
                        self.fn_ptr_groups,
                        self.group_decisions,
                        &local_fns,
                        &foreign_decs,
                    );
                }
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut visitor = MixedForeignVisitor {
        tcx: rust_program.tcx,
        fn_ptr_groups,
        group_decisions,
    };
    for def_id in rust_program.tcx.hir_body_owners() {
        let body = rust_program.tcx.hir_body_owned_by(def_id);
        visitor.visit_body(body);
    }
}

fn force_c_exposed_contracts_raw<'tcx>(
    rust_program: &RustProgram<'tcx>,
    fn_ptr_groups: &FnPtrGroups,
    c_exposed_fns: &FxHashSet<String>,
    group_decisions: &mut FxHashMap<LocalDefId, Vec<Option<PtrKind>>>,
) {
    if c_exposed_fns.is_empty() {
        return;
    }
    let tcx = rust_program.tcx;
    let mut c_exposed_fn_ptr_params: FxHashMap<LocalDefId, Vec<Option<Vec<Option<PtrKind>>>>> =
        FxHashMap::default();
    for &did in &rust_program.functions {
        if !is_c_exposed_fn(tcx, did, c_exposed_fns) {
            continue;
        }
        let sig = tcx.fn_sig(did).skip_binder().skip_binder();
        let param_decs = sig
            .inputs()
            .iter()
            .map(|ty| fn_ptr_input_decisions_from_ty(tcx, *ty))
            .collect();
        c_exposed_fn_ptr_params.insert(did, param_decs);
    }
    let c_exposed_fields = collect_c_exposed_fn_ptr_fields(rust_program, c_exposed_fns);

    struct CExposedVisitor<'a, 'tcx> {
        tcx: ty::TyCtxt<'tcx>,
        fn_ptr_groups: &'a FnPtrGroups,
        group_decisions: &'a mut FxHashMap<LocalDefId, Vec<Option<PtrKind>>>,
        c_exposed_fn_ptr_params: &'a FxHashMap<LocalDefId, Vec<Option<Vec<Option<PtrKind>>>>>,
        c_exposed_fields: &'a FxHashMap<(LocalDefId, FieldIdx), Vec<Option<PtrKind>>>,
    }

    impl<'tcx> Visitor<'tcx> for CExposedVisitor<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let hir::ExprKind::Call(callee, args) = expr.kind
                && let Some(callee_did) = hir_callee_local_def_id(callee)
                && let Some(param_decs) = self.c_exposed_fn_ptr_params.get(&callee_did)
            {
                for (arg, maybe_decs) in args.iter().zip(param_decs) {
                    let Some(decs) = maybe_decs else { continue };
                    let local_fns =
                        local_fn_ptr_group_fns_in_expr(self.tcx, arg, self.fn_ptr_groups);
                    force_fns_to_raw_contract(
                        self.tcx,
                        self.fn_ptr_groups,
                        self.group_decisions,
                        &local_fns,
                        decs,
                    );
                }
            }

            if let hir::ExprKind::Struct(qpath, fields, _) = expr.kind
                && let Some(struct_did) = hir_local_struct_did_from_qpath(qpath)
            {
                for field in fields {
                    let Some(field_idx) =
                        hir_field_index_by_name(self.tcx, struct_did, field.ident.name)
                    else {
                        continue;
                    };
                    let Some(decs) = self.c_exposed_fields.get(&(struct_did, field_idx)) else {
                        continue;
                    };
                    let local_fns =
                        local_fn_ptr_group_fns_in_expr(self.tcx, field.expr, self.fn_ptr_groups);
                    force_fns_to_raw_contract(
                        self.tcx,
                        self.fn_ptr_groups,
                        self.group_decisions,
                        &local_fns,
                        decs,
                    );
                }
            }

            intravisit::walk_expr(self, expr);
        }
    }

    let mut visitor = CExposedVisitor {
        tcx,
        fn_ptr_groups,
        group_decisions,
        c_exposed_fn_ptr_params: &c_exposed_fn_ptr_params,
        c_exposed_fields: &c_exposed_fields,
    };
    for def_id in tcx.hir_body_owners() {
        let body = tcx.hir_body_owned_by(def_id);
        visitor.visit_body(body);
    }
}

fn force_fns_to_raw_contract(
    tcx: ty::TyCtxt<'_>,
    fn_ptr_groups: &FnPtrGroups,
    group_decisions: &mut FxHashMap<LocalDefId, Vec<Option<PtrKind>>>,
    fns: &FxHashSet<LocalDefId>,
    raw_decs: &[Option<PtrKind>],
) {
    for &did in fns {
        let Some(&rep) = fn_ptr_groups.fn_to_group.get(&did) else { continue };
        let input_len = tcx.fn_sig(rep).skip_binder().inputs().skip_binder().len();
        let group_decs = group_decisions
            .entry(rep)
            .or_insert_with(|| vec![None; input_len]);
        for (idx, &raw_dec) in raw_decs.iter().enumerate() {
            let Some(raw_dec @ PtrKind::Raw(_)) = raw_dec else {
                continue;
            };
            if let Some(slot) = group_decs.get_mut(idx) {
                *slot = Some(raw_dec);
            }
        }
    }
}

fn local_fn_ptr_group_fns_in_expr<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    expr: &'tcx hir::Expr<'tcx>,
    fn_ptr_groups: &FnPtrGroups,
) -> FxHashSet<LocalDefId> {
    struct LocalFnVisitor<'a, 'tcx> {
        tcx: ty::TyCtxt<'tcx>,
        fn_ptr_groups: &'a FnPtrGroups,
        fns: FxHashSet<LocalDefId>,
    }

    impl<'tcx> Visitor<'tcx> for LocalFnVisitor<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let Some(def_id) = fn_ptr_def_id_from_expr(expr)
                && let Some(did) = def_id.as_local()
                && self.fn_ptr_groups.fn_to_group.contains_key(&did)
            {
                let typeck = self.tcx.typeck(expr.hir_id.owner);
                if ty_contains_fn_ptr(typeck.expr_ty_adjusted(expr)) {
                    self.fns.insert(did);
                }
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut visitor = LocalFnVisitor {
        tcx,
        fn_ptr_groups,
        fns: FxHashSet::default(),
    };
    visitor.visit_expr(expr);
    visitor.fns
}

fn foreign_fn_ptr_raw_decisions_in_expr<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    expr: &'tcx hir::Expr<'tcx>,
    fn_ptr_groups: &FnPtrGroups,
) -> Option<Vec<Option<PtrKind>>> {
    struct ForeignFnVisitor<'a, 'tcx> {
        tcx: ty::TyCtxt<'tcx>,
        fn_ptr_groups: &'a FnPtrGroups,
        found: Option<Vec<Option<PtrKind>>>,
    }

    impl<'tcx> Visitor<'tcx> for ForeignFnVisitor<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let Some(def_id) = fn_ptr_def_id_from_expr(expr) {
                let is_local_group_fn = def_id
                    .as_local()
                    .is_some_and(|did| self.fn_ptr_groups.fn_to_group.contains_key(&did));
                if !is_local_group_fn {
                    let typeck = self.tcx.typeck(expr.hir_id.owner);
                    if ty_contains_fn_ptr(typeck.expr_ty_adjusted(expr))
                        && let Some(decs) =
                            fn_ptr_input_decisions_from_ty(self.tcx, typeck.expr_ty_adjusted(expr))
                    {
                        merge_decision_vec(&mut self.found, &decs);
                    }
                }
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut visitor = ForeignFnVisitor {
        tcx,
        fn_ptr_groups,
        found: None,
    };
    visitor.visit_expr(expr);
    visitor.found
}

fn collect_c_exposed_fn_ptr_fields<'tcx>(
    rust_program: &RustProgram<'tcx>,
    c_exposed_fns: &FxHashSet<String>,
) -> FxHashMap<(LocalDefId, FieldIdx), Vec<Option<PtrKind>>> {
    let tcx = rust_program.tcx;
    let mut fields = FxHashMap::default();
    for &did in &rust_program.functions {
        if !is_c_exposed_fn(tcx, did, c_exposed_fns) {
            continue;
        }
        let sig = tcx.fn_sig(did).skip_binder().skip_binder();
        for &input in sig.inputs() {
            collect_c_exposed_fn_ptr_fields_from_ty(tcx, input, &mut fields);
        }
    }
    fields
}

fn collect_c_exposed_fn_ptr_fields_from_ty<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    fields: &mut FxHashMap<(LocalDefId, FieldIdx), Vec<Option<PtrKind>>>,
) {
    let (ty::TyKind::RawPtr(pointee, _) | ty::TyKind::Ref(_, pointee, _)) = ty.kind() else {
        return;
    };
    collect_fn_ptr_fields_from_struct_ty(tcx, *pointee, fields);
}

fn collect_fn_ptr_fields_from_struct_ty<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    fields: &mut FxHashMap<(LocalDefId, FieldIdx), Vec<Option<PtrKind>>>,
) {
    let ty::TyKind::Adt(adt_def, args) = ty.kind() else {
        return;
    };
    if !adt_def.is_struct() {
        return;
    }
    let Some(struct_did) = adt_def.did().as_local() else {
        return;
    };
    for (field_idx, field) in adt_def.non_enum_variant().fields.iter_enumerated() {
        let field_ty = field.ty(tcx, args);
        if let Some(decs) = fn_ptr_input_decisions_from_ty(tcx, field_ty) {
            fields.insert((struct_did, field_idx), decs);
        }
        collect_fn_ptr_fields_from_struct_ty(tcx, field_ty, fields);
    }
}

fn is_c_exposed_fn(
    tcx: ty::TyCtxt<'_>,
    did: LocalDefId,
    c_exposed_fns: &FxHashSet<String>,
) -> bool {
    let name = tcx.item_name(did.to_def_id());
    c_exposed_fns.contains(name.as_str())
        || tcx
            .get_attrs(did.to_def_id(), sym::export_name)
            .any(|attr| {
                attr.value_str()
                    .is_some_and(|s| c_exposed_fns.contains(s.as_str()))
            })
}

fn hir_callee_local_def_id(expr: &hir::Expr<'_>) -> Option<LocalDefId> {
    let expr = utils::hir::unwrap_drop_temps(expr);
    let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = expr.kind else {
        return None;
    };
    let Res::Def(_, def_id) = path.res else {
        return None;
    };
    def_id.as_local()
}

fn collect_hir_ty_alias_def_ids<I>(ty: &hir::Ty<'_, I>, aliases: &mut Vec<LocalDefId>) {
    match ty.kind {
        hir::TyKind::Path(hir::QPath::Resolved(_, path)) => {
            if let Res::Def(DefKind::TyAlias, def_id) = path.res
                && let Some(alias_did) = def_id.as_local()
                && !aliases.contains(&alias_did)
            {
                aliases.push(alias_did);
            }
            for seg in path.segments {
                if let Some(args) = seg.args {
                    for arg in args.args {
                        if let hir::GenericArg::Type(ty) = arg {
                            collect_hir_ty_alias_def_ids(ty, aliases);
                        }
                    }
                }
            }
        }
        hir::TyKind::Path(hir::QPath::TypeRelative(ty, seg)) => {
            collect_hir_ty_alias_def_ids(ty, aliases);
            if let Some(args) = seg.args {
                for arg in args.args {
                    if let hir::GenericArg::Type(ty) = arg {
                        collect_hir_ty_alias_def_ids(ty, aliases);
                    }
                }
            }
        }
        hir::TyKind::Ptr(mut_ty) | hir::TyKind::Ref(_, mut_ty) => {
            collect_hir_ty_alias_def_ids(mut_ty.ty, aliases);
        }
        hir::TyKind::Slice(ty) | hir::TyKind::Array(ty, _) => {
            collect_hir_ty_alias_def_ids(ty, aliases);
        }
        hir::TyKind::Tup(tys) => {
            for ty in tys {
                collect_hir_ty_alias_def_ids(ty, aliases);
            }
        }
        _ => {}
    }
}

fn collect_hir_ty_alias_def_ids_for_ty<I>(ty: &hir::Ty<'_, I>) -> Vec<LocalDefId> {
    let mut aliases = Vec::new();
    collect_hir_ty_alias_def_ids(ty, &mut aliases);
    aliases
}

fn insert_alias_decisions_for_ty<I>(
    tcx: ty::TyCtxt<'_>,
    annotation_decisions: &mut FxHashMap<HirId, Vec<Option<PtrKind>>>,
    ty: &hir::Ty<'_, I>,
    decs: &[Option<PtrKind>],
) {
    let mut aliases = Vec::new();
    collect_hir_ty_alias_def_ids(ty, &mut aliases);
    for alias_did in aliases {
        insert_annotation_decision(
            annotation_decisions,
            tcx.local_def_id_to_hir_id(alias_did),
            decs,
        );
    }
}

fn local_fn_param_hir<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    did: LocalDefId,
    idx: usize,
) -> Option<(HirId, &'tcx hir::Ty<'tcx>)> {
    let hir::Node::Item(item) = tcx.hir_node_by_def_id(did) else {
        return None;
    };
    let hir::ItemKind::Fn { sig, body, .. } = item.kind else {
        return None;
    };
    let body = tcx.hir_body(body);
    let param = body.params.get(idx)?;
    let hir::PatKind::Binding(_, hir_id, _, _) = param.pat.kind else {
        return None;
    };
    Some((hir_id, sig.decl.inputs.get(idx)?))
}

fn propagate_alias_decisions(
    tcx: ty::TyCtxt<'_>,
    annotation_decisions: &mut FxHashMap<HirId, Vec<Option<PtrKind>>>,
) {
    loop {
        let before_len = annotation_decisions.len();
        let mut pending = Vec::new();
        for item_id in tcx.hir_free_items() {
            let item = tcx.hir_item(item_id);
            let hir::ItemKind::TyAlias(_, _, ty) = item.kind else {
                continue;
            };
            let Some(decs) = annotation_decisions.get(&item.hir_id()).cloned() else {
                continue;
            };
            let mut aliases = Vec::new();
            collect_hir_ty_alias_def_ids(ty, &mut aliases);
            for alias_did in aliases {
                pending.push((tcx.local_def_id_to_hir_id(alias_did), decs.clone()));
            }
        }
        let mut changed = false;
        for (hir_id, decs) in pending {
            let before = annotation_decisions.get(&hir_id).cloned();
            insert_annotation_decision(annotation_decisions, hir_id, &decs);
            changed |= annotation_decisions.get(&hir_id) != before.as_ref();
        }
        if !changed && annotation_decisions.len() == before_len {
            break;
        }
    }
}

fn propagate_return_alias_decisions(
    tcx: ty::TyCtxt<'_>,
    fn_ptr_groups: &FnPtrGroups,
    group_decisions: &FxHashMap<LocalDefId, Vec<Option<PtrKind>>>,
    annotation_decisions: &mut FxHashMap<HirId, Vec<Option<PtrKind>>>,
) {
    struct ReturnAliasVisitor<'a, 'tcx> {
        tcx: ty::TyCtxt<'tcx>,
        fn_ptr_groups: &'a FnPtrGroups,
        group_decisions: &'a FxHashMap<LocalDefId, Vec<Option<PtrKind>>>,
        annotation_decisions: &'a mut FxHashMap<HirId, Vec<Option<PtrKind>>>,
        aliases: Vec<LocalDefId>,
    }

    impl<'tcx> Visitor<'tcx> for ReturnAliasVisitor<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let hir::ExprKind::Ret(Some(value)) = expr.kind
                && let Some(decs) = fn_ptr_decisions_for_expr(
                    self.tcx,
                    value,
                    self.fn_ptr_groups,
                    self.group_decisions,
                )
            {
                for &alias_did in &self.aliases {
                    insert_annotation_decision(
                        self.annotation_decisions,
                        self.tcx.local_def_id_to_hir_id(alias_did),
                        &decs,
                    );
                }
            }
            intravisit::walk_expr(self, expr);
        }
    }

    for item_id in tcx.hir_free_items() {
        let item = tcx.hir_item(item_id);
        let hir::ItemKind::Fn { sig, body, .. } = item.kind else {
            continue;
        };
        let hir::FnRetTy::Return(return_ty) = sig.decl.output else {
            continue;
        };
        let mut aliases = Vec::new();
        collect_hir_ty_alias_def_ids(return_ty, &mut aliases);
        if aliases.is_empty() {
            continue;
        }
        let body = tcx.hir_body(body);
        let mut visitor = ReturnAliasVisitor {
            tcx,
            fn_ptr_groups,
            group_decisions,
            annotation_decisions,
            aliases,
        };
        visitor.visit_body(body);
        if let Some(decs) =
            fn_ptr_decisions_for_expr(tcx, body.value, fn_ptr_groups, group_decisions)
        {
            for &alias_did in &visitor.aliases {
                insert_annotation_decision(
                    visitor.annotation_decisions,
                    tcx.local_def_id_to_hir_id(alias_did),
                    &decs,
                );
            }
        }
    }
}

fn hir_ty_alias_def_id<I>(ty: &hir::Ty<'_, I>) -> Option<LocalDefId> {
    let hir::TyKind::Path(hir::QPath::Resolved(None, path)) = ty.kind else {
        return None;
    };
    let Res::Def(DefKind::TyAlias, def_id) = path.res else {
        return None;
    };
    def_id.as_local()
}

fn hir_ty_contains_fn_ptr<I>(ty: &hir::Ty<'_, I>) -> bool {
    match ty.kind {
        hir::TyKind::BareFn(_) => true,
        hir::TyKind::Path(hir::QPath::Resolved(_, path)) => path.segments.iter().any(|seg| {
            seg.args.is_some_and(|args| {
                args.args.iter().any(|arg| {
                    if let hir::GenericArg::Type(ty) = arg {
                        hir_ty_contains_fn_ptr(*ty)
                    } else {
                        false
                    }
                })
            })
        }),
        hir::TyKind::Path(hir::QPath::TypeRelative(ty, seg)) => {
            hir_ty_contains_fn_ptr(ty)
                || seg.args.is_some_and(|args| {
                    args.args.iter().any(|arg| {
                        if let hir::GenericArg::Type(ty) = arg {
                            hir_ty_contains_fn_ptr(*ty)
                        } else {
                            false
                        }
                    })
                })
        }
        hir::TyKind::Ptr(mut_ty) | hir::TyKind::Ref(_, mut_ty) => hir_ty_contains_fn_ptr(mut_ty.ty),
        hir::TyKind::Slice(ty) | hir::TyKind::Array(ty, _) => hir_ty_contains_fn_ptr(ty),
        hir::TyKind::Tup(tys) => tys.iter().any(|ty| hir_ty_contains_fn_ptr(ty)),
        _ => false,
    }
}

fn ty_contains_fn_ptr(ty: ty::Ty<'_>) -> bool {
    match ty.kind() {
        ty::TyKind::FnPtr(..) => true,
        ty::TyKind::Adt(_, args) => args
            .iter()
            .any(|arg| arg.as_type().is_some_and(ty_contains_fn_ptr)),
        ty::TyKind::Tuple(tys) => tys.iter().any(ty_contains_fn_ptr),
        ty::TyKind::RawPtr(inner, _) | ty::TyKind::Ref(_, inner, _) => ty_contains_fn_ptr(*inner),
        ty::TyKind::Array(inner, _) | ty::TyKind::Slice(inner) => ty_contains_fn_ptr(*inner),
        _ => false,
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
            let borrow_promotion_result =
                crate::analyses::borrow::mutable_references_no_guarantee(&input, &mutables);
            let borrow_lifetime_flows = borrow_promotion_result.lifetime_flows.clone();
            let struct_copy_result = crate::analyses::struct_copy::analyze(
                &input,
                &borrow_promotion_result.mutable_fields,
            );
            let promoted_mut_ref_result = source_var_groups
                .postprocess_promoted_mut_refs(borrow_promotion_result.mutable_locals.clone());
            let promoted_shared_ref_result = source_var_groups
                .postprocess_promoted_mut_refs(borrow_promotion_result.shared_locals.clone());
            let fatness_result =
                crate::analyses::type_qualifier::foster::fatness::fatness_analysis(&input);
            let mut offset_sign_result =
                crate::analyses::offset_sign::sign::offset_sign_analysis(&input);
            offset_sign_result.access_signs =
                source_var_groups.postprocess_offset_signs(offset_sign_result.access_signs);
            let mut nullity_result = crate::analyses::nullity::analyze(&input, &points_to_result);
            nullity_result.non_null_locals =
                source_var_groups.postprocess_non_null_locals(nullity_result.non_null_locals);
            let analysis = crate::rewriter::Analysis {
                borrow_promotion_result,
                borrow_lifetime_flows,
                promoted_mut_ref_result,
                promoted_shared_ref_result,
                mutability_result,
                fatness_result,
                aliases,
                output_params,
                ownership_schemes: None,
                offset_sign_result,
                nullity_result,
                struct_copy_result,
            };
            let fn_ptr_groups = FnPtrGroups::build(&pre, &solutions, &input, &analysis);
            let decision = FnPtrRewriteDecision::build(
                &pre,
                &solutions,
                &input,
                &analysis,
                &tss,
                &fn_ptr_groups,
                &FxHashSet::default(),
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
        // All annotation decisions have explicit raw entries at the aliased positions.
        assert!(
            !decision.annotation_decisions.is_empty(),
            "annotation_decisions should be non-empty (group is still rewritten)"
        );
        assert!(
            decision
                .annotation_decisions
                .values()
                .all(|decs| decs.iter().all(|d| matches!(d, Some(PtrKind::Raw(true))))),
            "annotation_decisions should have explicit raw entries for aliased group"
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
