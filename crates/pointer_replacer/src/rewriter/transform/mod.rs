use std::cell::{Cell, RefCell};

use etrace::some_or;
use rustc_abi::FieldIdx;
use rustc_ast::{
    mut_visit::{self, FnKind, MutVisitor},
    ptr::P,
    *,
};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    self as hir, HirId, LangItem,
    def::{DefKind, Res},
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::{Symbol, sym};
use smallvec::smallvec;
use thin_vec::ThinVec;
use utils::{
    ast::{unwrap_cast_and_paren, unwrap_cast_and_paren_mut, unwrap_paren, unwrap_paren_mut},
    bytemuck::{
        BytemuckDerivePlan, BytemuckDeriveVisitor, BytemuckRequirement, BytemuckTypeClassifier,
    },
    ir::{AstToHir, is_option, mir_ty_to_string},
};

use super::{
    Analysis, BytemuckDependency, Config,
    collector::{collect_diffs, collect_diffs_with_diagnostics},
    decision::{PtrKind, SigDecision, SigDecisions},
    diagnostics::{DecisionDiagnostics, DecisionReason, DecisionStage, DecisionSubject},
};
use crate::{
    analyses::{
        borrow::StructFieldSlot, fn_ptr_groups::FnPtrGroups,
        fn_ptr_rewrite_decision::FnPtrRewriteDecision,
    },
    utils::rustc::RustProgram,
};

pub(crate) struct TransformVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    analysis: &'a Analysis,
    sig_decs: SigDecisions,
    // Function signatures should use the normalized decisions above; plans are retained for
    // later struct field lifetime emission.
    #[allow(dead_code)]
    lifetime_plans: super::lifetimes::LifetimePlans,
    ptr_kinds: FxHashMap<HirId, PtrKind>,
    forced_raw_bindings: FxHashSet<HirId>,
    borrowed_raw_params: FxHashMap<HirId, BorrowedRawParamInfo>,
    raw_bridge_bindings: FxHashMap<HirId, RawBridgeInfo>,
    raw_scalar_bridge_fields: FxHashSet<StructFieldSlot>,
    alloc_wrappers: FxHashMap<LocalDefId, AllocWrapperInfo>,
    free_like_wrappers: FxHashSet<LocalDefId>,
    demoted_fields: FxHashSet<StructFieldSlot>,
    field_cursor_fields: FxHashSet<StructFieldSlot>,
    c_exposed_abi_fields: FxHashSet<StructFieldSlot>,
    c_exposed_thin_abi_fields: FxHashSet<StructFieldSlot>,
    c_exposed_cursor_abi_fields: FxHashSet<StructFieldSlot>,
    impl_self_lifetimes: Vec<(LocalDefId, Vec<Symbol>)>,
    ast_to_hir: AstToHir,
    fn_ptr_rewrite: FnPtrRewriteDecision,
    pub bytemuck: Cell<bool>,
    bytemuck_derives: RefCell<BytemuckDerivePlan>,
    bytemuck_classifier: RefCell<BytemuckTypeClassifier<'tcx>>,
    pub slice_cursor: Cell<bool>,
    diagnostics: DecisionDiagnostics,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum RawBridgeInfo {
    Scalar,
    Array { len_expr: String },
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum AllocWrapperInfo {
    Fixed(RawBridgeInfo),
    Bytes {
        bytes_param: usize,
    },
    CountSize {
        count_param: usize,
        elem_size_param: usize,
    },
    Realloc {
        ptr_param: usize,
        bytes_param: usize,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct BorrowedRawParamInfo {
    alias: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum LocalRawParamSummary {
    BorrowOnly,
    ReturnedToOwningOutput,
    ReturnedToBorrowedOutput,
    Freed,
    Escapes,
}

impl LocalRawParamSummary {
    fn preserves_owning_call_boundary(self) -> bool {
        matches!(
            self,
            LocalRawParamSummary::BorrowOnly
                | LocalRawParamSummary::ReturnedToOwningOutput
                | LocalRawParamSummary::ReturnedToBorrowedOutput
        )
    }
}

impl MutVisitor for TransformVisitor<'_, '_> {
    fn visit_crate(&mut self, krate: &mut Crate) {
        mut_visit::walk_crate(self, krate);
        if self.slice_cursor.get() {
            CursorProjectionSimplifier::default().visit_crate(krate);
        }

        if self.bytemuck_derives.borrow().is_empty() {
            return;
        }
        let mut derive_visitor = BytemuckDeriveVisitor::new(
            self.tcx,
            &self.ast_to_hir,
            self.bytemuck_derives.borrow().clone(),
        );
        derive_visitor.visit_crate(krate);
    }

    fn flat_map_item(&mut self, item: P<Item>) -> smallvec::SmallVec<[P<Item>; 1]> {
        if self.should_remove_generated_copy_clone_impl(&item) {
            return smallvec![];
        }
        mut_visit::walk_flat_map_item(self, item)
    }

    fn visit_item(&mut self, item: &mut Item) {
        let node_id = item.id;
        let mut fn_def_id: Option<LocalDefId> = None;
        let mut fn_output_transform: Option<(LocalDefId, PtrKind)> = None;
        match &mut item.kind {
            ItemKind::Impl(box impl_item) => {
                let Some(struct_did) = self.local_struct_did_for_ast_ty(&impl_item.self_ty) else {
                    return;
                };
                if !self.struct_has_field_rewrite_candidate(struct_did) {
                    return;
                }
                let lifetimes = self.ordered_struct_lifetimes(struct_did);
                if !lifetimes.is_empty() {
                    super::lifetimes::ensure_lifetime_params(&mut impl_item.generics, &lifetimes);
                    self.add_struct_lifetime_args_to_ty_with_lifetimes(
                        &mut impl_item.self_ty,
                        &lifetimes,
                    );
                }
                self.impl_self_lifetimes.push((struct_did, lifetimes));
                mut_visit::walk_item(self, item);
                self.impl_self_lifetimes.pop();
                return;
            }
            ItemKind::Struct(_, generics, VariantData::Struct { fields, .. }) => {
                if let Some(struct_did) = self.ast_to_hir.global_map.get(&node_id).copied() {
                    self.rewrite_struct_definition(struct_did, generics, fields);
                    for (field_idx, field) in fields.iter_mut().enumerate() {
                        let fi = FieldIdx::from_usize(field_idx);
                        if let TyKind::BareFn(bare_fn) = &mut field.ty.kind
                            && let Some(decs) =
                                self.fn_ptr_rewrite.field_decisions.get(&(struct_did, fi))
                        {
                            let decs = decs.clone();
                            if rewrite_bare_fn_inputs(bare_fn, &decs) {
                                self.slice_cursor.set(true);
                            }
                        }
                    }
                }
            }
            ItemKind::Fn(box fn_item) => {
                let def_id = self.ast_to_hir.global_map[&node_id];
                fn_def_id = Some(def_id);
                let mir_body = self
                    .tcx
                    .mir_drops_elaborated_and_const_checked(def_id)
                    .borrow();
                let sig_dec = self.sig_decs.data.get(&def_id).unwrap();

                if !sig_dec.signature_locked {
                    let mut planned_lifetimes = Vec::new();
                    for lifetime in sig_dec
                        .input_lifetimes
                        .iter()
                        .copied()
                        .flatten()
                        .chain(sig_dec.output_lifetime)
                    {
                        if !planned_lifetimes.contains(&lifetime) {
                            planned_lifetimes.push(lifetime);
                        }
                    }
                    for (local_decl, input_dec) in
                        mir_body.local_decls.iter().skip(1).zip(&sig_dec.input_decs)
                    {
                        if input_dec.is_some()
                            && let Some((inner_ty, _)) = unwrap_ptr_from_mir_ty(local_decl.ty)
                        {
                            self.extend_lifetimes_for_ty(&mut planned_lifetimes, inner_ty);
                        }
                    }
                    if sig_dec.output_dec.is_some() {
                        let return_decl =
                            &mir_body.local_decls[rustc_middle::mir::Local::from_u32(0)];
                        if let Some((inner_ty, _)) = unwrap_ptr_from_mir_ty(return_decl.ty) {
                            self.extend_lifetimes_for_ty(&mut planned_lifetimes, inner_ty);
                        }
                    }
                    super::lifetimes::ensure_lifetime_params(
                        &mut fn_item.generics,
                        &planned_lifetimes,
                    );
                }

                for (param_index, ((local_decl, input_dec), param)) in mir_body
                    .local_decls
                    .iter()
                    .skip(1)
                    .zip(&sig_dec.input_decs)
                    .zip(&mut fn_item.sig.decl.inputs)
                    .enumerate()
                {
                    self.mark_param_mut_if_needed(param);
                    let input_lifetime =
                        sig_dec.input_lifetimes.get(param_index).copied().flatten();
                    if matches!(local_decl.ty.kind(), ty::TyKind::Ref(..))
                        && input_lifetime.is_none()
                    {
                        continue;
                    }
                    match input_dec {
                        Some(PtrKind::Ref(m)) => {
                            let (inner_ty, _) = unwrap_ptr_from_mir_ty(local_decl.ty)
                                .unwrap_or_else(|| {
                                    panic!(
                                        "Expected pointer type, got {ty:?} in {local_decl:?}",
                                        ty = local_decl.ty
                                    )
                                });
                            *param.ty = self.mk_ref_ty_with_lifetime(inner_ty, *m, input_lifetime);
                        }
                        Some(PtrKind::OptRef(m)) => {
                            let (inner_ty, _) = unwrap_ptr_from_mir_ty(local_decl.ty)
                                .unwrap_or_else(|| {
                                    panic!(
                                        "Expected pointer type, got {ty:?} in {local_decl:?}",
                                        ty = local_decl.ty
                                    )
                                });
                            *param.ty =
                                self.mk_opt_ref_ty_with_lifetime(inner_ty, *m, input_lifetime);
                        }
                        Some(PtrKind::Box) => {
                            let (inner_ty, _) = unwrap_ptr_from_mir_ty(local_decl.ty)
                                .unwrap_or_else(|| {
                                    panic!(
                                        "Expected pointer type, got {ty:?} in {local_decl:?}",
                                        ty = local_decl.ty
                                    )
                                });
                            *param.ty = self.mk_box_ty(inner_ty);
                        }
                        Some(PtrKind::OptBox) => {
                            let (inner_ty, _) = unwrap_ptr_from_mir_ty(local_decl.ty)
                                .unwrap_or_else(|| {
                                    panic!(
                                        "Expected pointer type, got {ty:?} in {local_decl:?}",
                                        ty = local_decl.ty
                                    )
                                });
                            *param.ty = self.mk_opt_box_ty(inner_ty);
                        }
                        Some(PtrKind::Slice(m)) => {
                            let (inner_ty, _) = unwrap_ptr_from_mir_ty(local_decl.ty)
                                .unwrap_or_else(|| {
                                    panic!(
                                        "Expected pointer type, got {ty:?} in {local_decl:?}",
                                        ty = local_decl.ty
                                    )
                                });
                            *param.ty =
                                self.mk_slice_ty_with_lifetime(inner_ty, *m, input_lifetime);
                        }
                        Some(PtrKind::Raw(m)) => {
                            let (inner_ty, _) = unwrap_ptr_from_mir_ty(local_decl.ty)
                                .unwrap_or_else(|| {
                                    panic!(
                                        "Expected pointer type, got {ty:?} in {local_decl:?}",
                                        ty = local_decl.ty
                                    )
                                });
                            *param.ty = self.mk_raw_ptr_ty(inner_ty, *m);
                        }
                        Some(PtrKind::SliceCursor(m)) => {
                            let (inner_ty, _) = unwrap_ptr_from_mir_ty(local_decl.ty)
                                .unwrap_or_else(|| {
                                    panic!(
                                        "Expected pointer type, got {ty:?} in {local_decl:?}",
                                        ty = local_decl.ty
                                    )
                                });
                            *param.ty =
                                self.mk_cursor_ty_with_lifetime(inner_ty, *m, input_lifetime);
                            self.slice_cursor.set(true);
                        }
                        Some(PtrKind::BoxedSlice) => {
                            let (inner_ty, _) = unwrap_ptr_from_mir_ty(local_decl.ty)
                                .unwrap_or_else(|| {
                                    panic!(
                                        "Expected pointer type, got {ty:?} in {local_decl:?}",
                                        ty = local_decl.ty
                                    )
                                });
                            *param.ty = self.mk_boxed_slice_ty(inner_ty);
                        }
                        Some(PtrKind::OptBoxedSlice) => {
                            let (inner_ty, _) = unwrap_ptr_from_mir_ty(local_decl.ty)
                                .unwrap_or_else(|| {
                                    panic!(
                                        "Expected pointer type, got {ty:?} in {local_decl:?}",
                                        ty = local_decl.ty
                                    )
                                });
                            *param.ty = self.mk_opt_boxed_slice_ty(inner_ty);
                        }
                        None => {
                            if let TyKind::BareFn(bare_fn) = &mut param.ty.kind
                                && let Some(hir_id) =
                                    self.ast_to_hir.local_map.get(&param.pat.id).copied()
                                && let Some(decs) =
                                    self.fn_ptr_rewrite.annotation_decisions.get(&hir_id)
                            {
                                let decs = decs.clone();
                                if rewrite_bare_fn_inputs(bare_fn, &decs) {
                                    self.slice_cursor.set(true);
                                }
                            }
                            continue;
                        }
                    }

                    let needs_mut_binding = input_dec.is_some_and(|kind| {
                        matches!(
                            kind,
                            PtrKind::OptRef(true)
                                | PtrKind::OptBox
                                | PtrKind::OptBoxedSlice
                                | PtrKind::SliceCursor(true)
                        ) || (input_lifetime.is_none() && kind.is_mut())
                    });
                    if needs_mut_binding
                        && let PatKind::Ident(binding_mode, ..) = &mut param.pat.kind
                    {
                        binding_mode.1 = Mutability::Mut;
                    }
                }

                let output_dec_before = sig_dec.output_dec;
                let output_lifetime = sig_dec.output_lifetime;
                let adjusted_output_dec = output_dec_before.map(|output_dec| {
                    let return_decl = &mir_body.local_decls[rustc_middle::mir::Local::from_u32(0)];
                    let Some((inner_ty, _)) = unwrap_ptr_from_mir_ty(return_decl.ty) else {
                        return output_dec;
                    };
                    if output_dec.is_owning_box_like()
                        && fn_tail_returns_unsupported_box_binding(
                            self.tcx,
                            &self.sig_decs,
                            &self.ptr_kinds,
                            def_id,
                            output_dec,
                            inner_ty,
                        )
                    {
                        PtrKind::Raw(true)
                    } else {
                        output_dec
                    }
                });

                if let Some(output_dec) = adjusted_output_dec {
                    let return_decl = &mir_body.local_decls[rustc_middle::mir::Local::from_u32(0)];
                    if let Some((inner_ty, _)) = unwrap_ptr_from_mir_ty(return_decl.ty)
                        && let FnRetTy::Ty(ret_ty) = &mut fn_item.sig.decl.output
                    {
                        *ret_ty = P(match output_dec {
                            PtrKind::Ref(m) => {
                                self.mk_ref_ty_with_lifetime(inner_ty, m, output_lifetime)
                            }
                            PtrKind::OptRef(m) => {
                                self.mk_opt_ref_ty_with_lifetime(inner_ty, m, output_lifetime)
                            }
                            PtrKind::Box => self.mk_box_ty(inner_ty),
                            PtrKind::OptBox => self.mk_opt_box_ty(inner_ty),
                            PtrKind::Raw(m) => self.mk_raw_ptr_ty(inner_ty, m),
                            PtrKind::BoxedSlice => self.mk_boxed_slice_ty(inner_ty),
                            PtrKind::OptBoxedSlice => self.mk_opt_boxed_slice_ty(inner_ty),
                            PtrKind::Slice(m) => self.mk_slice_ty(inner_ty, m),
                            PtrKind::SliceCursor(m) => {
                                self.slice_cursor.set(true);
                                self.mk_cursor_ty(inner_ty, m)
                            }
                        });
                    }
                }
                if adjusted_output_dec != output_dec_before
                    && let Some(after) = adjusted_output_dec
                {
                    self.diagnostics.record(
                        DecisionSubject::Return { did: def_id },
                        DecisionStage::AstRewriteFallback,
                        output_dec_before,
                        Some(after),
                        DecisionReason::AstRewriteUnsupportedBoxRhs,
                        None,
                    );
                }

                let sig = self.tcx.fn_sig(def_id).skip_binder().skip_binder();
                let output_kind = match sig.output().kind() {
                    ty::TyKind::RawPtr(_, m) => {
                        Some(adjusted_output_dec.unwrap_or(PtrKind::Raw(m.is_mut())))
                    }
                    _ => adjusted_output_dec,
                };
                fn_output_transform = output_kind.map(|kind| (def_id, kind));
            }
            ItemKind::Struct(_, _, variant_data) => {
                let struct_def_id = self.ast_to_hir.global_map[&node_id];
                let fields = match variant_data {
                    VariantData::Struct { fields, .. } => fields.as_mut_slice(),
                    VariantData::Tuple(fields, _) => fields.as_mut_slice(),
                    VariantData::Unit(_) => &mut [],
                };
                for (field_idx, field) in fields.iter_mut().enumerate() {
                    let fi = FieldIdx::from_usize(field_idx);
                    if let TyKind::BareFn(bare_fn) = &mut field.ty.kind
                        && let Some(decs) = self
                            .fn_ptr_rewrite
                            .field_decisions
                            .get(&(struct_def_id, fi))
                    {
                        let decs = decs.clone();
                        if rewrite_bare_fn_inputs(bare_fn, &decs) {
                            self.slice_cursor.set(true);
                        }
                    }
                }
            }
            ItemKind::TyAlias(box ty_alias) => {
                let alias_def_id = self.ast_to_hir.global_map[&node_id];
                let alias_hir_id = self.tcx.local_def_id_to_hir_id(alias_def_id);
                if let Some(decs) = self.fn_ptr_rewrite.annotation_decisions.get(&alias_hir_id) {
                    let decs = decs.clone();
                    if let Some(ty) = &mut ty_alias.ty
                        && let Some(bare_fn) = find_bare_fn_in_ty_mut(ty)
                        && rewrite_bare_fn_inputs(bare_fn, &decs)
                    {
                        self.slice_cursor.set(true);
                    }
                }
            }
            ItemKind::Static(box static_item) => {
                // only bare fn-ptr statics (fn(...)) are covered; Option<fn(...)> statics
                // are not in annotation_decisions and their BareFn match fails here
                let static_def_id = self.ast_to_hir.global_map[&node_id];
                let static_hir_id = self.tcx.local_def_id_to_hir_id(static_def_id);
                if let TyKind::BareFn(bare_fn) = &mut static_item.ty.kind
                    && let Some(decs) = self.fn_ptr_rewrite.annotation_decisions.get(&static_hir_id)
                {
                    let decs = decs.clone();
                    if rewrite_bare_fn_inputs(bare_fn, &decs) {
                        self.slice_cursor.set(true);
                    }
                }
            }
            _ => {}
        }

        mut_visit::walk_item(self, item);

        if let Some(def_id) = fn_def_id
            && let ItemKind::Fn(box fn_item) = &mut item.kind
            && let Some(body) = &mut fn_item.body
        {
            self.insert_borrowed_raw_param_aliases(def_id, body);
        }

        if let Some((def_id, output_kind)) = fn_output_transform
            && let ItemKind::Fn(box fn_item) = &mut item.kind
            && let Some(body) = &mut fn_item.body
            && let Some(stmt) = body.stmts.last_mut()
            && let StmtKind::Expr(expr) = &mut stmt.kind
        {
            let hir_item = self.tcx.hir_expect_item(def_id);
            let hir::ItemKind::Fn { body: body_id, .. } = hir_item.kind else { return };
            let hir_body = self.tcx.hir_body(body_id);
            let hir::ExprKind::Block(hir_block, _) = hir_body.value.kind else { return };
            let Some(hir_tail) = hir_block.expr else { return };
            let return_decl = self
                .tcx
                .mir_drops_elaborated_and_const_checked(def_id)
                .borrow()
                .local_decls[rustc_middle::mir::Local::from_u32(0)]
            .ty;
            let Some((lhs_inner_ty, _)) = unwrap_ptr_from_mir_ty(return_decl) else { return };
            self.transform_return_rhs(expr, hir_tail, output_kind, lhs_inner_ty);
        }
    }

    fn flat_map_stmt(&mut self, s: Stmt) -> smallvec::SmallVec<[Stmt; 1]> {
        let stmts = mut_visit::walk_flat_map_stmt(self, s);
        let mut new_stmts = smallvec::SmallVec::new();
        for s in stmts {
            match &s.kind {
                StmtKind::Expr(expr) | StmtKind::Semi(expr) => {
                    if let ExprKind::Assign(lhs, rhs, _) = &expr.kind
                        && let ExprKind::AddrOf(BorrowKind::Ref, mutability, rhs_inner) = &rhs.kind
                        && let ExprKind::MethodCall(_) = rhs_inner.kind
                    {
                        new_stmts.push(utils::stmt!(
                            "let {}_tmp = {};",
                            mutability.prefix_str(),
                            pprust::expr_to_string(rhs_inner),
                        ));
                        new_stmts.push(utils::stmt!(
                            "{} = {}_tmp;",
                            pprust::expr_to_string(lhs),
                            mutability.ref_prefix_str(),
                        ));
                    } else {
                        new_stmts.push(s);
                    }
                }
                _ => {
                    new_stmts.push(s);
                }
            }
        }
        new_stmts
    }

    fn visit_local(&mut self, local: &mut Local) {
        mut_visit::walk_local(self, local);

        if let Some(let_stmt) = self.ast_to_hir.get_let_stmt(local.id, self.tcx)
            && let hir::PatKind::Binding(_, hir_id, _ident, _) = let_stmt.pat.kind
            && (self.local_binding_needs_mut_for_promoted_field_write(hir_id)
                || self.local_binding_needs_mut_for_owned_field_free(hir_id))
            && let PatKind::Ident(binding_mode, ..) = &mut local.pat.kind
        {
            binding_mode.1 = Mutability::Mut;
        }

        if let Some(let_stmt) = self.ast_to_hir.get_let_stmt(local.id, self.tcx)
            && let hir::PatKind::Binding(_, hir_id, _ident, _) = let_stmt.pat.kind
            && let Some(mut lhs_kind) = self.effective_ptr_kind(hir_id)
        {
            let typeck = self.tcx.typeck(hir_id.owner);
            let lhs_ty = typeck.node_type(hir_id);
            let (lhs_inner_ty, lhs_mutability) = unwrap_ptr_from_mir_ty(lhs_ty).unwrap();
            let original_lhs_kind = lhs_kind;
            let mut fallback_events = Vec::new();
            if let Some(init) = let_stmt.init
                && matches!(
                    self.forced_local_callee_output_kind(init),
                    Some(PtrKind::Raw(_))
                )
            {
                fallback_events.push((
                    lhs_kind,
                    PtrKind::Raw(lhs_mutability.is_mut()),
                    DecisionReason::AstRewriteForcedRawCalleeOutput,
                ));
                lhs_kind = PtrKind::Raw(lhs_mutability.is_mut());
            }
            if lhs_kind.is_owning_box_like()
                && let Some(init) = let_stmt.init
                && !self.rhs_supports_box_target(init, lhs_kind, lhs_inner_ty)
            {
                fallback_events.push((
                    lhs_kind,
                    PtrKind::Raw(true),
                    DecisionReason::AstRewriteUnsupportedBoxRhs,
                ));
                lhs_kind = PtrKind::Raw(true);
            }
            if lhs_kind.is_owning_box_like()
                && self.fn_has_unsupported_box_assignment(hir_id, lhs_kind, lhs_inner_ty)
            {
                fallback_events.push((
                    lhs_kind,
                    PtrKind::Raw(true),
                    DecisionReason::AstRewriteUnsupportedBoxAssignment,
                ));
                lhs_kind = PtrKind::Raw(true);
            }
            if lhs_kind != original_lhs_kind && matches!(lhs_kind, PtrKind::Raw(_)) {
                self.ptr_kinds.insert(hir_id, lhs_kind);
                self.forced_raw_bindings.insert(hir_id);
                for (before, after, reason) in fallback_events {
                    self.record_ast_fallback_binding(hir_id, before, after, reason);
                }
            }

            match lhs_kind {
                PtrKind::Ref(m) => {
                    local.ty = Some(P(self.mk_ref_ty(lhs_inner_ty, m)));
                }
                PtrKind::OptRef(m) => {
                    local.ty = Some(P(self.mk_opt_ref_ty(lhs_inner_ty, m)));
                }
                PtrKind::Box => {
                    local.ty = Some(P(self.mk_local_box_ty(lhs_inner_ty)));
                }
                PtrKind::OptBox => {
                    local.ty = Some(P(self.mk_local_opt_box_ty(lhs_inner_ty)));
                }
                PtrKind::BoxedSlice => {
                    local.ty = Some(P(self.mk_boxed_slice_ty(lhs_inner_ty)));
                }
                PtrKind::OptBoxedSlice => {
                    local.ty = Some(P(self.mk_opt_boxed_slice_ty(lhs_inner_ty)));
                }
                PtrKind::Slice(m) => {
                    local.ty = Some(P(self.mk_slice_ty(lhs_inner_ty, m)));
                }
                PtrKind::Raw(m) => {
                    local.ty = Some(P(self.mk_raw_ptr_ty(lhs_inner_ty, m)));
                }
                PtrKind::SliceCursor(m) => {
                    local.ty = Some(P(self.mk_cursor_ty(lhs_inner_ty, m)));
                    self.slice_cursor.set(true);
                }
            }

            if lhs_kind.is_mut()
                && let PatKind::Ident(binding_mode, ..) = &mut local.pat.kind
            {
                binding_mode.1 = Mutability::Mut;
            }

            if let LocalKind::Init(box rhs) | LocalKind::InitElse(box rhs, _) = &mut local.kind {
                let hir_rhs = let_stmt.init.unwrap();
                if !self.try_bridge_raw_root(rhs, hir_rhs, lhs_kind, lhs_inner_ty, Some(hir_id)) {
                    self.transform_rhs(rhs, hir_rhs, lhs_kind);
                }
            }
        }

        // Handle fn-ptr typed locals: rewrite BareFn type annotations
        if let Some(ty) = &mut local.ty
            && let TyKind::BareFn(bare_fn) = &mut ty.kind
            && let Some(let_stmt) = self.ast_to_hir.get_let_stmt(local.id, self.tcx)
            && let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind
            && let Some(decs) = self.fn_ptr_rewrite.annotation_decisions.get(&hir_id)
        {
            let decs = decs.clone();
            if rewrite_bare_fn_inputs(bare_fn, &decs) {
                self.slice_cursor.set(true);
            }
        }
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        mut_visit::walk_expr(self, expr);
        let expr_id = expr.id;

        match &mut expr.kind {
            ExprKind::Field(base, _) => {
                let Some(hir_expr) = self.ast_to_hir.get_expr(expr.id, self.tcx) else {
                    return;
                };
                let hir::ExprKind::Field(hir_base, _) = hir_expr.kind else {
                    return;
                };
                if self.rewrite_borrowed_raw_param_field_base(base, hir_base) {
                    return;
                }
                if matches!(
                    self.expr_ctx(hir_expr),
                    ExprCtx::ImmediatelyAddrTaken | ExprCtx::AddrTaken(_)
                ) {
                    return;
                }
                self.simplify_promoted_ref_field_base(base, hir_base);
            }
            ExprKind::Struct(se) => {
                self.rewrite_struct_literal_fields(expr.id, se);
            }
            ExprKind::MethodCall(call)
                if call.seg.ident.name.as_str() == "map_or" && call.args.len() == 2 =>
            {
                if let Some((m, body, hir_body)) =
                    raw_pointer_map_or_closure_body(self.tcx, &self.ast_to_hir, expr_id, call)
                {
                    self.transform_ptr(body, hir_body, PtrCtx::Rhs(PtrKind::Raw(m)));
                }
            }
            ExprKind::Assign(lhs, rhs, _) => {
                let hir_expr = self.ast_to_hir.get_expr(expr.id, self.tcx).unwrap();
                let typeck = self.tcx.typeck(hir_expr.hir_id.owner);
                let hir::ExprKind::Assign(hir_lhs, hir_rhs, _) = hir_expr.kind else {
                    panic!("{hir_expr:?}")
                };
                if let Some(field) = self.promoted_field_slot_for_hir_field(hir_lhs)
                    && let Some(kind) = self.field_ptr_kind(field)
                {
                    let target_inner_ty =
                        unwrap_ptr_from_mir_ty(typeck.expr_ty(hir_lhs)).map(|(inner, _)| inner);
                    self.transform_promoted_field_rhs(rhs, hir_rhs, kind, target_inner_ty);
                    return;
                }
                let lhs_ty = typeck.expr_ty(hir_lhs);
                let (_, m) = some_or!(unwrap_ptr_from_mir_ty(lhs_ty), return);
                let (lhs_inner_ty, _) = unwrap_ptr_from_mir_ty(lhs_ty).unwrap();
                let lhs_hir_id = if let ExprKind::Path(_, _) = lhs.kind
                    && let Some(hir_id) = self.hir_id_of_path(lhs.id)
                {
                    Some(hir_id)
                } else {
                    None
                };
                let mut lhs_kind = if let Some(hir_id) = lhs_hir_id {
                    self.effective_ptr_kind(hir_id)
                        .unwrap_or(PtrKind::Raw(m.is_mut()))
                } else {
                    PtrKind::Raw(m.is_mut())
                };
                let original_lhs_kind = lhs_kind;
                let mut fallback_events = Vec::new();
                if matches!(
                    self.forced_local_callee_output_kind(hir_rhs),
                    Some(PtrKind::Raw(_))
                ) {
                    fallback_events.push((
                        lhs_kind,
                        PtrKind::Raw(m.is_mut()),
                        DecisionReason::AstRewriteForcedRawCalleeOutput,
                    ));
                    lhs_kind = PtrKind::Raw(m.is_mut());
                }
                if lhs_kind.is_owning_box_like()
                    && !self.rhs_supports_box_target(hir_rhs, lhs_kind, lhs_inner_ty)
                {
                    fallback_events.push((
                        lhs_kind,
                        PtrKind::Raw(true),
                        DecisionReason::AstRewriteUnsupportedBoxRhs,
                    ));
                    lhs_kind = PtrKind::Raw(true);
                } else if matches!(lhs_kind, PtrKind::Box | PtrKind::OptBox) {
                    if hir_is_unsupported_scalar_box_allocator_root(self.tcx, lhs_inner_ty, hir_rhs)
                    {
                        fallback_events.push((
                            lhs_kind,
                            PtrKind::Raw(true),
                            DecisionReason::AstRewriteUnsupportedScalarBoxAllocator,
                        ));
                        lhs_kind = PtrKind::Raw(true);
                    }
                    if let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_rhs.kind
                        && let Res::Local(rhs_hir_id) = path.res
                        && matches!(self.effective_ptr_kind(rhs_hir_id), Some(PtrKind::Raw(_)))
                    {
                        fallback_events.push((
                            lhs_kind,
                            PtrKind::Raw(true),
                            DecisionReason::AstRewriteRawRhsLocal,
                        ));
                        lhs_kind = PtrKind::Raw(true);
                    }
                }
                if lhs_kind != original_lhs_kind
                    && matches!(lhs_kind, PtrKind::Raw(_))
                    && let Some(hir_id) = lhs_hir_id
                {
                    self.ptr_kinds.insert(hir_id, lhs_kind);
                    self.forced_raw_bindings.insert(hir_id);
                    for (before, after, reason) in fallback_events {
                        self.record_ast_fallback_binding(hir_id, before, after, reason);
                    }
                }

                match lhs_kind {
                    PtrKind::SliceCursor(_) => {
                        // Detect self-assignment with offset: p = p.offset(k)
                        if let Some(lhs_hir_id) = self.hir_id_of_path(lhs.id) {
                            let rhs_e = unwrap_addr_of_deref(unwrap_cast_and_paren(rhs));
                            let hir_rhs_e = hir_unwrap_addr_of_deref(hir_unwrap_cast(hir_rhs));
                            let seek_offset = self.ptr_expr(rhs_e, hir_rhs_e).and_then(|pe| {
                                if let PtrExprBaseKind::Path(Res::Local(rhs_hir_id)) = pe.base_kind
                                    && rhs_hir_id == lhs_hir_id
                                    && pe.projs.len() == 1
                                    && let PtrExprProj::Offset(offset_expr) = &pe.projs[0]
                                {
                                    Some(pprust::expr_to_string(offset_expr))
                                } else {
                                    None
                                }
                            });
                            if let Some(ref offset_str) = seek_offset {
                                let lhs_str = pprust::expr_to_string(lhs);
                                *expr = utils::expr!("{}.seek(({}) as isize)", lhs_str, offset_str);
                                return;
                            }
                        }
                        if let Some(lhs_hir_id) = lhs_hir_id
                            && !self.try_bridge_raw_root(
                                rhs,
                                hir_rhs,
                                lhs_kind,
                                lhs_inner_ty,
                                Some(lhs_hir_id),
                            )
                        {
                            self.transform_rhs(rhs, hir_rhs, lhs_kind);
                        } else if lhs_hir_id.is_none() {
                            self.transform_rhs(rhs, hir_rhs, lhs_kind);
                        }
                    }
                    PtrKind::Slice(_)
                    | PtrKind::Ref(_)
                    | PtrKind::OptRef(_)
                    | PtrKind::Box
                    | PtrKind::OptBox
                    | PtrKind::BoxedSlice
                    | PtrKind::OptBoxedSlice
                    | PtrKind::Raw(_) => {
                        if let Some(lhs_hir_id) = lhs_hir_id
                            && !self.try_bridge_raw_root(
                                rhs,
                                hir_rhs,
                                lhs_kind,
                                lhs_inner_ty,
                                Some(lhs_hir_id),
                            )
                        {
                            self.transform_rhs(rhs, hir_rhs, lhs_kind);
                        } else if lhs_hir_id.is_none()
                            && !self.try_bridge_raw_projection_root(
                                rhs,
                                hir_rhs,
                                hir_lhs,
                                lhs_kind,
                                lhs_inner_ty,
                            )
                        {
                            self.transform_rhs(rhs, hir_rhs, lhs_kind);
                        }
                    }
                }
            }
            ExprKind::Binary(bin_op, l, r)
                if matches!(
                    bin_op.node,
                    BinOpKind::Eq
                        | BinOpKind::Ne
                        | BinOpKind::Lt
                        | BinOpKind::Le
                        | BinOpKind::Gt
                        | BinOpKind::Ge
                ) =>
            {
                let hir_expr = self.ast_to_hir.get_expr(expr.id, self.tcx).unwrap();
                let typeck = self.tcx.typeck(hir_expr.hir_id.owner);
                let hir::ExprKind::Binary(_, hir_l, hir_r) = hir_expr.kind else {
                    panic!("{hir_expr:?}")
                };
                let ty = typeck.expr_ty(hir_l);
                if let Some((_, m)) = unwrap_ptr_from_mir_ty(ty) {
                    let kind = PtrKind::Raw(m.is_mut());
                    self.transform_rhs(l, hir_l, kind);
                    self.transform_rhs(r, hir_r, kind);
                }
            }
            ExprKind::Call(func_ast, args) => {
                let hir_expr = self.ast_to_hir.get_expr(expr.id, self.tcx).unwrap();
                let hir::ExprKind::Call(func, hargs) = hir_expr.kind else {
                    panic!("{hir_expr:?}")
                };
                let sig_dec = if let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = func.kind
                    && let Res::Def(_, def_id) = path.res
                    && let Some(def_id) = def_id.as_local()
                {
                    self.sig_decs.data.get(&def_id)
                } else {
                    None
                };

                // for indirect calls via a fn-ptr binding, look up joint decisions
                let fn_ptr_decisions: Option<&Vec<Option<PtrKind>>> = if sig_dec.is_none() {
                    if let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = func.kind
                        && let Res::Local(binding_hir_id) = path.res
                    {
                        self.fn_ptr_rewrite
                            .annotation_decisions
                            .get(&binding_hir_id)
                    } else {
                        None
                    }
                } else {
                    None
                };

                // for calls via struct-field fn-ptrs (e.g., `(s.field).expect(...)(args)`)
                let field_fn_ptr_decisions: Option<&Vec<Option<PtrKind>>> =
                    if sig_dec.is_none() && fn_ptr_decisions.is_none() {
                        self.field_fn_ptr_decisions_for_call(func)
                    } else {
                        None
                    };

                let typeck = self.tcx.typeck(hir_expr.hir_id.owner);

                if let Some(free_rewrite) = self.rewrite_direct_free_call(hir_expr, &args[..]) {
                    *expr = free_rewrite;
                    return;
                }

                for (i, (arg, harg)) in args.iter_mut().zip(hargs).enumerate() {
                    let ty = typeck.expr_ty_adjusted(harg);
                    let param_kind = sig_dec
                        .and_then(|sig| sig.input_decs.get(i).copied())
                        .flatten()
                        .or_else(|| {
                            fn_ptr_decisions
                                .and_then(|decs| decs.get(i).copied())
                                .flatten()
                        })
                        .or_else(|| {
                            field_fn_ptr_decisions
                                .and_then(|decs| decs.get(i).copied())
                                .flatten()
                        })
                        .or_else(|| {
                            unwrap_ptr_from_mir_ty(ty).map(|(_, m)| {
                                PtrKind::Raw(
                                    self.get_mutability_decision(harg).unwrap_or(m.is_mut()),
                                )
                            })
                        });
                    let Some(param_kind) = param_kind else { continue };

                    self.transform_rhs(arg, harg, param_kind);
                    if param_kind == PtrKind::OptRef(true)
                        && (hir_path_source_kind(self.tcx, &self.ptr_kinds, harg)
                            == Some(PtrKind::OptRef(true))
                            || self
                                .promoted_field_slot_for_hir_field(harg)
                                .and_then(|field| self.field_ptr_kind(field))
                                == Some(PtrKind::OptRef(true)))
                    {
                        *arg = P(utils::expr!(
                            "({}).as_deref_mut()",
                            pprust::expr_to_string(arg)
                        ));
                    }
                }

                // when this is a transmute call and an argument casts a fn-ptr group function,
                // replace the first explicit type arg with `_` to match the rewritten cast type
                if let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = func.kind
                    && path
                        .segments
                        .last()
                        .is_some_and(|s| s.ident.name == rustc_span::sym::transmute)
                    && hargs.iter().any(|h| self.hir_expr_has_fn_ptr_group_cast(h))
                    && let ExprKind::Path(_, path) = &mut func_ast.kind
                    && let Some(seg) = path.segments.last_mut()
                    && let Some(gen_args) = &mut seg.args
                    && let GenericArgs::AngleBracketed(angle_args) = &mut **gen_args
                {
                    for arg in &mut angle_args.args {
                        if let AngleBracketedArg::Arg(GenericArg::Type(ty)) = arg {
                            ty.kind = TyKind::Infer;
                            break;
                        }
                    }
                }
                hoist_opt_ref_borrow(expr);
            }
            ExprKind::MethodCall(box MethodCall { seg, receiver, .. })
                if seg.ident.name.as_str() == "is_null" =>
            {
                let receiver = unwrap_paren(receiver);
                let hir_receiver = self.ast_to_hir.get_expr(receiver.id, self.tcx);
                if let Some(field_kind) = hir_receiver
                    .and_then(|hir_receiver| self.promoted_field_slot_for_hir_field(hir_receiver))
                    .and_then(|field| self.field_ptr_kind(field))
                {
                    match field_kind {
                        PtrKind::OptRef(_) | PtrKind::OptBox | PtrKind::OptBoxedSlice => {
                            seg.ident.name = Symbol::intern("is_none");
                        }
                        PtrKind::Slice(_) | PtrKind::SliceCursor(_) => {
                            seg.ident.name = Symbol::intern("is_empty");
                        }
                        PtrKind::Ref(_) | PtrKind::Box | PtrKind::BoxedSlice => {
                            *expr = utils::expr!("false");
                        }
                        PtrKind::Raw(_) => {}
                    }
                } else if let Some(hir_receiver) = hir_receiver
                    && let Some(pe) = self.ptr_expr(receiver, hir_receiver)
                    && matches!(self.ptr_source_kind(&pe), Some(PtrKind::OptRef(_)))
                    && !pe.projs.is_empty()
                {
                    *expr = utils::expr!("({}).is_none()", pprust::expr_to_string(pe.base));
                } else if matches!(receiver.kind, ExprKind::Path(_, _))
                    && let Some(hir_id) = self.hir_id_of_path(receiver.id)
                    && let Some(ptr_kind) = self.effective_ptr_kind(hir_id)
                {
                    match ptr_kind {
                        PtrKind::Ref(_) | PtrKind::Box | PtrKind::BoxedSlice => {
                            *expr = utils::expr!("false");
                        }
                        PtrKind::OptRef(_) => {
                            seg.ident.name = Symbol::intern("is_none");
                        }
                        PtrKind::OptBox | PtrKind::OptBoxedSlice => {
                            seg.ident.name = Symbol::intern("is_none");
                        }
                        PtrKind::Slice(_) | PtrKind::SliceCursor(_) => {
                            seg.ident.name = Symbol::intern("is_empty");
                        }
                        PtrKind::Raw(_) => {}
                    }
                }
            }
            ExprKind::MethodCall(box MethodCall {
                seg,
                receiver,
                args,
                ..
            }) if seg.ident.name.as_str() == "add" && args.len() == 1 => {
                let hir_expr = self.ast_to_hir.get_expr(expr.id, self.tcx).unwrap();
                let hir::ExprKind::MethodCall(_, hir_receiver, _, _) = hir_expr.kind else {
                    panic!("{hir_expr:?}")
                };
                let typeck = self.tcx.typeck(hir_expr.hir_id.owner);
                if let Some((_, raw_mut)) =
                    unwrap_ptr_from_mir_ty(typeck.expr_ty_adjusted(hir_receiver))
                {
                    self.transform_ptr(
                        receiver,
                        hir_receiver,
                        PtrCtx::Rhs(PtrKind::Raw(raw_mut.is_mut())),
                    );
                }
            }
            ExprKind::MethodCall(box MethodCall {
                seg,
                receiver,
                args,
                ..
            }) if seg.ident.name.as_str() == "offset_from" => {
                let hir_receiver = self.ast_to_hir.get_expr(receiver.id, self.tcx).unwrap();
                self.transform_ptr(receiver, hir_receiver, PtrCtx::Rhs(PtrKind::Raw(true)));
                let [arg] = &mut args[..] else { panic!() };
                let hir_arg = self.ast_to_hir.get_expr(arg.id, self.tcx).unwrap();
                self.transform_ptr(arg, hir_arg, PtrCtx::Rhs(PtrKind::Raw(true)));
            }
            ExprKind::Ret(Some(ret)) => {
                let hir_expr = self.ast_to_hir.get_expr(expr.id, self.tcx).unwrap();
                let hir::ExprKind::Ret(Some(hir_ret)) = hir_expr.kind else {
                    panic!("{hir_expr:?}")
                };
                let sig = self
                    .tcx
                    .fn_sig(hir_ret.hir_id.owner)
                    .skip_binder()
                    .skip_binder();
                if let ty::TyKind::RawPtr(_, m) = sig.output().kind() {
                    let (lhs_inner_ty, _) = unwrap_ptr_from_mir_ty(sig.output()).unwrap();
                    let kind = self
                        .sig_decs
                        .data
                        .get(&hir_ret.hir_id.owner.def_id)
                        .and_then(|sd| sd.output_dec)
                        .unwrap_or(PtrKind::Raw(m.is_mut()));
                    self.transform_return_rhs(ret, hir_ret, kind, lhs_inner_ty);
                } else if let ty::TyKind::Tuple(tys) = sig.output().kind() {
                    let ExprKind::Tup(elems) = &mut ret.kind else {
                        panic!("expected tuple expr for tuple return type")
                    };
                    let hir::ExprKind::Tup(hir_elems) = hir_ret.kind else {
                        panic!("expected HIR tuple expr for tuple return type")
                    };
                    for (i, elem_ty) in tys.iter().enumerate() {
                        if let ty::TyKind::RawPtr(_, m) = elem_ty.kind() {
                            let (lhs_inner_ty, _) = unwrap_ptr_from_mir_ty(elem_ty).unwrap();
                            self.transform_return_rhs(
                                &mut elems[i],
                                &hir_elems[i],
                                PtrKind::Raw(m.is_mut()),
                                lhs_inner_ty,
                            );
                        }
                    }
                }
            }
            ExprKind::Unary(UnOp::Deref, e) => {
                let hir_expr = self.ast_to_hir.get_expr(expr.id, self.tcx).unwrap();
                let hir::ExprKind::Unary(UnOp::Deref, hir_e) = hir_expr.kind else {
                    panic!("{hir_expr:?}")
                };
                let m = match self.expr_ctx(hir_expr) {
                    ExprCtx::ImmediatelyAddrTaken => None,
                    ExprCtx::AddrTaken(m) => Some(m),
                    ExprCtx::Rvalue => Some(false),
                    ExprCtx::Lvalue => Some(true),
                };
                if let Some(m) = m {
                    if let Some(field) = self.promoted_field_slot_for_hir_field(hir_e)
                        && let Some(kind) = self.field_ptr_kind(field)
                    {
                        let field_str = pprust::expr_to_string(e);
                        *expr = match kind {
                            PtrKind::OptRef(true) if m => {
                                utils::expr!("*({field_str}).as_deref_mut().unwrap()")
                            }
                            PtrKind::OptRef(true) => {
                                utils::expr!("*({field_str}).as_deref().unwrap()")
                            }
                            PtrKind::OptRef(false) => utils::expr!("*({field_str}.unwrap())"),
                            PtrKind::OptBox if m => {
                                utils::expr!("*({field_str}).as_deref_mut().unwrap()")
                            }
                            PtrKind::OptBox => {
                                utils::expr!("*({field_str}).as_deref().unwrap()")
                            }
                            PtrKind::Slice(_) => {
                                utils::expr!("({field_str})[0]")
                            }
                            PtrKind::SliceCursor(_) => {
                                utils::expr!("({field_str})[0 as usize]")
                            }
                            _ => unreachable!(),
                        };
                        return;
                    }
                    // For SliceCursor with offset projections, try to emit base[offset] directly
                    let inner = unwrap_addr_of_deref(unwrap_cast_and_paren(e));
                    let hir_inner = hir_unwrap_addr_of_deref(hir_unwrap_cast(hir_e));
                    let pe = self.ptr_expr(inner, hir_inner);
                    if let Some(pe) = pe
                        && self.ptr_expr_base_is_cursor(&pe)
                        && let Some(offset) = combined_cursor_offset(&pe.projs)
                        && !pe.addr_of
                        && !pe.as_ptr
                        && !pe.cast_int
                    {
                        let base_str = pprust::expr_to_string(pe.base);
                        let offset_str = pprust::expr_to_string(&offset);
                        *expr = utils::expr!("({})[{}]", base_str, offset_str)
                    } else {
                        match self.transform_ptr(e, hir_e, PtrCtx::Deref(m)) {
                            PtrKind::Raw(_) => {}
                            PtrKind::Ref(_) | PtrKind::Box => {}
                            PtrKind::OptRef(_) => {
                                **e = utils::expr!("{}.unwrap()", pprust::expr_to_string(e));
                            }
                            PtrKind::OptBox => {
                                **e = utils::expr!(
                                    "{}.as_deref{}().unwrap()",
                                    pprust::expr_to_string(e),
                                    if m { "_mut" } else { "" },
                                );
                            }
                            PtrKind::OptBoxedSlice => {
                                *expr = utils::expr!(
                                    "({}).as_deref{}().unwrap()[0]",
                                    pprust::expr_to_string(e),
                                    if m { "_mut" } else { "" },
                                );
                            }
                            PtrKind::BoxedSlice => {
                                *expr = utils::expr!("({})[0]", pprust::expr_to_string(e));
                            }
                            PtrKind::Slice(_) => {
                                *expr = utils::expr!("({})[0]", pprust::expr_to_string(e));
                            }
                            PtrKind::SliceCursor(_) => {
                                *expr = utils::expr!("({})[0 as usize]", pprust::expr_to_string(e));
                            }
                        }
                    }
                }
            }
            ExprKind::Cast(_, cast_ty) => {
                if let TyKind::BareFn(bare_fn) = &mut cast_ty.kind
                    && let Some(hir_expr) = self.ast_to_hir.get_expr(expr.id, self.tcx)
                    && let hir::ExprKind::Cast(hir_inner, _) = hir_expr.kind
                {
                    let inner = utils::hir::unwrap_drop_temps(hir_inner);
                    if let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = inner.kind
                        && let hir::def::Res::Def(_, def_id) = path.res
                        && let Some(local_did) = def_id.as_local()
                        && self.fn_ptr_rewrite.direct_rewrite.contains(&local_did)
                        && let Some(decs) = self.fn_ptr_rewrite.individual_decisions.get(&local_did)
                    {
                        let decs = decs.clone();
                        if rewrite_bare_fn_inputs(bare_fn, &decs) {
                            self.slice_cursor.set(true);
                        }
                    }
                }
            }
            _ => {}
        }
    }

    fn visit_ty(&mut self, ty: &mut Ty) {
        mut_visit::walk_ty(self, ty);
        self.add_struct_lifetime_args_to_ty(ty);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PtrCtx {
    Rhs(PtrKind),
    Deref(bool),
}

fn is_c_exposed_fn(tcx: TyCtxt<'_>, did: LocalDefId, c_exposed_fns: &FxHashSet<String>) -> bool {
    let name = tcx.item_name(did.to_def_id());
    c_exposed_fns.contains(name.as_str())
        || tcx
            .get_attrs(did.to_def_id(), sym::export_name)
            .any(|attr| {
                attr.value_str()
                    .is_some_and(|s| c_exposed_fns.contains(s.as_str()))
            })
}

fn is_local_c_abi_struct(tcx: TyCtxt<'_>, did: LocalDefId) -> bool {
    let adt_def = tcx.adt_def(did);
    let repr = adt_def.repr();
    adt_def.is_struct() && !adt_def.is_union() && repr.c() && repr.pack.is_none()
}

fn collect_local_abi_struct_fields_from_ty(
    tcx: TyCtxt<'_>,
    ty: ty::Ty<'_>,
    fields: &mut FxHashSet<StructFieldSlot>,
) {
    match ty.kind() {
        ty::TyKind::RawPtr(pointee, _) | ty::TyKind::Ref(_, pointee, _) => {
            collect_local_abi_struct_fields_from_ty(tcx, *pointee, fields);
        }
        ty::TyKind::Array(elem, _) | ty::TyKind::Slice(elem) => {
            collect_local_abi_struct_fields_from_ty(tcx, *elem, fields);
        }
        ty::TyKind::Tuple(elems) => {
            for elem in elems.iter() {
                collect_local_abi_struct_fields_from_ty(tcx, elem, fields);
            }
        }
        ty::TyKind::Adt(adt_def, args) => {
            if let Some(struct_did) = adt_def.did().as_local()
                && is_local_c_abi_struct(tcx, struct_did)
            {
                fields.extend(adt_def.non_enum_variant().fields.iter_enumerated().map(
                    |(field_index, _)| StructFieldSlot {
                        struct_did,
                        field_index: field_index.index(),
                    },
                ));
                return;
            }
            for arg in args.iter() {
                if let ty::GenericArgKind::Type(arg_ty) = arg.kind() {
                    collect_local_abi_struct_fields_from_ty(tcx, arg_ty, fields);
                }
            }
        }
        _ => {}
    }
}

fn collect_c_exposed_thin_input_fields_from_ty(
    tcx: TyCtxt<'_>,
    ty: ty::Ty<'_>,
    frozen_fields: &mut FxHashSet<StructFieldSlot>,
    thin_fields: &mut FxHashSet<StructFieldSlot>,
) {
    match ty.kind() {
        ty::TyKind::RawPtr(pointee, _) | ty::TyKind::Ref(_, pointee, _) => {
            collect_local_abi_struct_fields_from_ty(tcx, *pointee, thin_fields);
        }
        _ => collect_local_abi_struct_fields_from_ty(tcx, ty, frozen_fields),
    }
}

fn collect_c_exposed_pointer_input_fields_from_ty(
    tcx: TyCtxt<'_>,
    ty: ty::Ty<'_>,
    fields: &mut FxHashSet<StructFieldSlot>,
) {
    if let ty::TyKind::RawPtr(pointee, _) | ty::TyKind::Ref(_, pointee, _) = ty.kind() {
        collect_local_abi_struct_fields_from_ty(tcx, *pointee, fields);
    }
}

fn collect_c_exposed_abi_fields<'tcx>(
    rust_program: &RustProgram<'tcx>,
    c_exposed_fns: &FxHashSet<String>,
    sig_decs: &SigDecisions,
) -> (
    FxHashSet<StructFieldSlot>,
    FxHashSet<StructFieldSlot>,
    FxHashSet<StructFieldSlot>,
) {
    let tcx = rust_program.tcx;
    let mut frozen_fields = FxHashSet::default();
    let mut thin_fields = FxHashSet::default();
    let mut cursor_fields = FxHashSet::default();

    for did in &rust_program.functions {
        if !is_c_exposed_fn(tcx, *did, c_exposed_fns) {
            continue;
        }
        let Some(sig_dec) = sig_decs.data.get(did) else {
            continue;
        };
        let sig = tcx.fn_sig(*did).skip_binder().skip_binder();
        let direct_interface_fix = sig_dec
            .input_decs
            .iter()
            .any(|dec| matches!(dec, Some(PtrKind::Slice(_) | PtrKind::SliceCursor(_))));

        for (ty, dec) in sig.inputs().iter().copied().zip(&sig_dec.input_decs) {
            collect_c_exposed_pointer_input_fields_from_ty(tcx, ty, &mut cursor_fields);
            if matches!(dec, Some(PtrKind::Slice(_) | PtrKind::SliceCursor(_))) {
                if let Some((inner_ty, _)) = unwrap_ptr_from_mir_ty(ty) {
                    collect_local_abi_struct_fields_from_ty(tcx, inner_ty, &mut frozen_fields);
                }
            } else if !direct_interface_fix {
                collect_c_exposed_thin_input_fields_from_ty(
                    tcx,
                    ty,
                    &mut frozen_fields,
                    &mut thin_fields,
                );
            }
        }

        if !direct_interface_fix {
            collect_local_abi_struct_fields_from_ty(tcx, sig.output(), &mut frozen_fields);
        }
    }

    (frozen_fields, thin_fields, cursor_fields)
}

fn collect_borrowed_raw_params(
    tcx: TyCtxt<'_>,
    initial_sig_decs: &SigDecisions,
    final_sig_decs: &SigDecisions,
) -> FxHashMap<HirId, BorrowedRawParamInfo> {
    let mut params = FxHashMap::default();
    for maybe_owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let hir::OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            continue;
        };
        let did = item.owner_id.def_id;
        let Some(initial_sig_dec) = initial_sig_decs.data.get(&did) else {
            continue;
        };
        let Some(final_sig_dec) = final_sig_decs.data.get(&did) else {
            continue;
        };
        let hir_body = tcx.hir_body(body);
        let sig = tcx.fn_sig(did).skip_binder().skip_binder();
        for (idx, param) in hir_body.params.iter().enumerate() {
            if !matches!(
                initial_sig_dec.input_decs.get(idx).copied().flatten(),
                Some(PtrKind::Ref(true))
            ) || !matches!(
                final_sig_dec.input_decs.get(idx).copied().flatten(),
                Some(PtrKind::Raw(true))
            ) {
                continue;
            }
            let Some(input_ty) = sig.inputs().iter().copied().nth(idx) else {
                continue;
            };
            if !raw_pointer_pointee_is_local_struct(tcx, input_ty) {
                continue;
            }
            let hir::PatKind::Binding(_, hir_id, _, _) = param.pat.kind else {
                continue;
            };
            let facts = borrowed_raw_param_facts(hir_body.value, hir_id);
            if facts.assigned || facts.direct_field_derefs == 0 {
                continue;
            }
            let param_name = tcx.hir_name(hir_id).to_string();
            params.insert(
                hir_id,
                BorrowedRawParamInfo {
                    alias: borrowed_raw_param_alias(&param_name),
                },
            );
        }
    }
    params
}

#[derive(Default)]
struct BorrowedRawParamFacts {
    assigned: bool,
    direct_field_derefs: usize,
}

fn borrowed_raw_param_facts(expr: &hir::Expr<'_>, target: HirId) -> BorrowedRawParamFacts {
    struct ParamUseVisitor {
        target: HirId,
        facts: BorrowedRawParamFacts,
    }

    impl<'tcx> Visitor<'tcx> for ParamUseVisitor {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            match expr.kind {
                hir::ExprKind::Assign(lhs, _, _) | hir::ExprKind::AssignOp(_, lhs, _) => {
                    if hir_unwrapped_local_id(lhs) == Some(self.target) {
                        self.facts.assigned = true;
                    }
                }
                hir::ExprKind::Field(base, _) => {
                    if hir_direct_raw_deref_local_id(base) == Some(self.target) {
                        self.facts.direct_field_derefs += 1;
                    }
                }
                _ => {}
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut visitor = ParamUseVisitor {
        target,
        facts: BorrowedRawParamFacts::default(),
    };
    visitor.visit_expr(expr);
    visitor.facts
}

fn hir_direct_raw_deref_local_id(expr: &hir::Expr<'_>) -> Option<HirId> {
    let hir::ExprKind::Unary(hir::UnOp::Deref, inner) = utils::hir::unwrap_drop_temps(expr).kind
    else {
        return None;
    };
    hir_unwrapped_local_id(hir_unwrap_casts(inner))
}

fn raw_pointer_pointee_is_local_struct<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> bool {
    let Some((pointee, _)) = unwrap_ptr_from_mir_ty(ty) else {
        return false;
    };
    matches!(
        pointee.kind(),
        ty::TyKind::Adt(adt_def, _) if adt_def.did().is_local() && adt_def.is_struct()
    ) && !utils::file::contains_file_ty(pointee, tcx)
}

fn borrowed_raw_param_alias(param_name: &str) -> String {
    let mut component = String::new();
    for c in param_name.chars() {
        if c == '_' || c.is_ascii_alphanumeric() {
            component.push(c);
        } else {
            component.push('_');
        }
    }
    if component.chars().next().is_some_and(|c| c.is_ascii_digit()) {
        component.insert(0, '_');
    }
    format!("__crat_borrowed_{component}")
}

#[derive(Clone, Copy, Debug)]
enum AllocatorRoot<'a> {
    Malloc {
        bytes: &'a Expr,
    },
    Calloc {
        count: &'a Expr,
        elem_size: &'a Expr,
    },
}

impl<'analysis, 'tcx> TransformVisitor<'analysis, 'tcx> {
    pub fn new(
        config: &Config,
        rust_program: &RustProgram<'tcx>,
        analysis: &'analysis Analysis,
        ast_to_hir: AstToHir,
        fn_ptr_groups: FnPtrGroups,
        fn_ptr_rewrite: FnPtrRewriteDecision,
        diagnostics: DecisionDiagnostics,
    ) -> TransformVisitor<'analysis, 'tcx> {
        let mut diagnostics = diagnostics;
        let lifetime_plans = super::lifetimes::LifetimePlans::new(rust_program, analysis);
        let mut sig_decs = SigDecisions::new_with_diagnostics(
            rust_program,
            analysis,
            &lifetime_plans,
            &fn_ptr_groups,
            Some(&mut diagnostics),
        );
        let initial_sig_decs = sig_decs.clone();
        let mut ptr_kinds = collect_diffs_with_diagnostics(
            rust_program,
            analysis,
            &sig_decs,
            &fn_ptr_groups,
            Some(&mut diagnostics),
        );
        let free_like_wrappers = collect_local_free_wrappers(rust_program.tcx);
        let local_raw_free_summaries =
            collect_local_raw_free_summaries(rust_program.tcx, &free_like_wrappers);
        let local_raw_param_summaries =
            collect_local_raw_param_summaries(rust_program.tcx, &sig_decs, &free_like_wrappers);
        let mut forced_raw_bindings =
            downgrade_unsupported_allocator_box_kinds(rust_program.tcx, &ptr_kinds);
        record_binding_events(
            &mut diagnostics,
            rust_program.tcx,
            &ptr_kinds,
            &forced_raw_bindings,
            DecisionReason::UnsupportedAllocatorRoot,
        );
        normalize_forced_raw_bindings(rust_program.tcx, &mut ptr_kinds, &forced_raw_bindings);
        normalize_owning_call_result_bindings(
            rust_program.tcx,
            &sig_decs,
            &mut ptr_kinds,
            &forced_raw_bindings,
        );
        loop {
            let mut changed = false;
            let local_struct_downgrades =
                downgrade_local_struct_bindings(rust_program.tcx, &mut sig_decs, &ptr_kinds);
            record_binding_events_excluding(
                &mut diagnostics,
                rust_program.tcx,
                &ptr_kinds,
                &local_struct_downgrades.call_conflict,
                &forced_raw_bindings,
                DecisionReason::LocalStructCallConflict,
            );
            record_binding_events_excluding(
                &mut diagnostics,
                rust_program.tcx,
                &ptr_kinds,
                &local_struct_downgrades.call_binding_conflict,
                &forced_raw_bindings,
                DecisionReason::LocalStructCallBindingConflict,
            );
            record_binding_events_excluding(
                &mut diagnostics,
                rust_program.tcx,
                &ptr_kinds,
                &local_struct_downgrades.field_borrow_conflict,
                &forced_raw_bindings,
                DecisionReason::LocalStructFieldBorrowConflict,
            );
            record_binding_events_excluding(
                &mut diagnostics,
                rust_program.tcx,
                &ptr_kinds,
                &local_struct_downgrades.reborrow_assignment,
                &forced_raw_bindings,
                DecisionReason::LocalStructReborrowAssignment,
            );
            record_binding_events_excluding(
                &mut diagnostics,
                rust_program.tcx,
                &ptr_kinds,
                &local_struct_downgrades.field_mut_ptr,
                &forced_raw_bindings,
                DecisionReason::LocalStructFieldMutPtr,
            );
            record_binding_events_excluding(
                &mut diagnostics,
                rust_program.tcx,
                &ptr_kinds,
                &local_struct_downgrades.static_projection,
                &forced_raw_bindings,
                DecisionReason::LocalStructStaticProjection,
            );
            record_binding_events_excluding(
                &mut diagnostics,
                rust_program.tcx,
                &ptr_kinds,
                &local_struct_downgrades.foreign_mut_call,
                &forced_raw_bindings,
                DecisionReason::LocalStructForeignMutCall,
            );
            if local_struct_downgrades.changed {
                changed = true;
            }
            let (box_input_changed, unsupported_box_input_bindings) =
                downgrade_unsupported_box_inputs(
                    rust_program.tcx,
                    &mut sig_decs,
                    &local_raw_free_summaries,
                );
            record_binding_events_excluding(
                &mut diagnostics,
                rust_program.tcx,
                &ptr_kinds,
                &unsupported_box_input_bindings,
                &forced_raw_bindings,
                DecisionReason::UnsupportedBoxInput,
            );
            if box_input_changed {
                changed = true;
            }
            let unsupported_box_outputs = downgrade_unsupported_box_outputs(
                rust_program.tcx,
                &mut sig_decs,
                &ptr_kinds,
                &config.c_exposed_fns,
            );
            for did in &unsupported_box_outputs {
                record_signature_output_event(
                    &mut diagnostics,
                    rust_program.tcx,
                    &sig_decs,
                    *did,
                    DecisionReason::UnsupportedBoxOutput,
                );
            }
            if !unsupported_box_outputs.is_empty() {
                changed = true;
            }
            let freed_borrow_outputs = downgrade_freed_borrow_outputs(
                rust_program.tcx,
                &mut sig_decs,
                &free_like_wrappers,
            );
            for did in &freed_borrow_outputs.outputs {
                record_signature_output_event(
                    &mut diagnostics,
                    rust_program.tcx,
                    &sig_decs,
                    *did,
                    DecisionReason::FreedBorrowOutput,
                );
            }
            for &(did, idx) in &freed_borrow_outputs.tied_inputs {
                record_signature_input_event(
                    &mut diagnostics,
                    rust_program.tcx,
                    &sig_decs,
                    did,
                    idx,
                    DecisionReason::FreedBorrowOutputTiedInput,
                );
            }
            if freed_borrow_outputs.changed() {
                changed = true;
            }
            let raw_cast_call_inputs =
                downgrade_raw_cast_call_inputs(rust_program.tcx, &mut sig_decs, &ptr_kinds);
            for &(did, idx) in &raw_cast_call_inputs {
                record_signature_input_event(
                    &mut diagnostics,
                    rust_program.tcx,
                    &sig_decs,
                    did,
                    idx,
                    DecisionReason::RawCastCallInput,
                );
            }
            if !raw_cast_call_inputs.is_empty() {
                changed = true;
            }
            let cursor_input_downgrades = downgrade_cursor_inputs_from_unanchored_raw_callers(
                rust_program.tcx,
                &mut sig_decs,
                &ptr_kinds,
            );
            for &(did, idx) in &cursor_input_downgrades {
                record_signature_input_event(
                    &mut diagnostics,
                    rust_program.tcx,
                    &sig_decs,
                    did,
                    idx,
                    DecisionReason::CursorInputFromUnanchoredRawCaller,
                );
            }
            if !cursor_input_downgrades.is_empty() {
                changed = true;
            }
            let owned_field_free_bindings = collect_owned_field_free_owner_bindings(
                rust_program.tcx,
                analysis,
                &sig_decs,
                &ptr_kinds,
                &free_like_wrappers,
            );
            for hir_id in owned_field_free_bindings {
                if force_signature_input_mut_for_binding(rust_program.tcx, &mut sig_decs, hir_id) {
                    if let Some((did, idx)) = param_index_for_binding(rust_program.tcx, hir_id) {
                        record_signature_input_event(
                            &mut diagnostics,
                            rust_program.tcx,
                            &sig_decs,
                            did,
                            idx,
                            DecisionReason::OwnedFieldFreeRequiresMutableInput,
                        );
                    }
                    changed = true;
                }
            }
            let raw_call_result_bindings =
                collect_raw_call_result_bindings(rust_program.tcx, &sig_decs, &ptr_kinds);
            let raw_local_assignment_bindings =
                collect_raw_local_assignment_bindings(rust_program.tcx, &ptr_kinds);
            record_binding_events_excluding(
                &mut diagnostics,
                rust_program.tcx,
                &ptr_kinds,
                &raw_call_result_bindings,
                &forced_raw_bindings,
                DecisionReason::RawCallResult,
            );
            record_binding_events_excluding(
                &mut diagnostics,
                rust_program.tcx,
                &ptr_kinds,
                &raw_local_assignment_bindings,
                &forced_raw_bindings,
                DecisionReason::RawLocalAssignment,
            );
            for hir_id in &raw_local_assignment_bindings {
                if param_index_for_binding(rust_program.tcx, *hir_id).is_some()
                    && force_signature_input_raw_for_binding(
                        rust_program.tcx,
                        &mut sig_decs,
                        *hir_id,
                    )
                {
                    if let Some((did, idx)) = param_index_for_binding(rust_program.tcx, *hir_id) {
                        record_signature_input_event(
                            &mut diagnostics,
                            rust_program.tcx,
                            &sig_decs,
                            did,
                            idx,
                            DecisionReason::RawLocalAssignment,
                        );
                    }
                    changed = true;
                }
            }
            let unsupported_box_target_bindings =
                collect_unsupported_box_target_bindings(rust_program.tcx, &sig_decs, &ptr_kinds);
            record_binding_events_excluding(
                &mut diagnostics,
                rust_program.tcx,
                &ptr_kinds,
                &unsupported_box_target_bindings,
                &forced_raw_bindings,
                DecisionReason::UnsupportedBoxTarget,
            );
            let unsupported_box_usage_subreasons = if diagnostics.is_enabled() {
                collect_unsupported_box_usage_subreasons(
                    rust_program.tcx,
                    &sig_decs,
                    &ptr_kinds,
                    &free_like_wrappers,
                    &local_raw_param_summaries,
                )
            } else {
                FxHashMap::default()
            };
            let unsupported_box_usage_bindings = collect_unsupported_box_usage_bindings(
                rust_program.tcx,
                &sig_decs,
                &ptr_kinds,
                &free_like_wrappers,
                &local_raw_param_summaries,
            );
            record_binding_events_excluding(
                &mut diagnostics,
                rust_program.tcx,
                &ptr_kinds,
                &unsupported_box_usage_bindings,
                &forced_raw_bindings,
                DecisionReason::UnsupportedBoxUsage,
            );
            for hir_id in &unsupported_box_usage_bindings {
                if forced_raw_bindings.contains(hir_id) {
                    continue;
                }
                if let Some(reasons) = unsupported_box_usage_subreasons.get(hir_id) {
                    for &reason in reasons {
                        record_binding_event(
                            &mut diagnostics,
                            rust_program.tcx,
                            &ptr_kinds,
                            *hir_id,
                            reason,
                        );
                    }
                }
            }
            let old_len = forced_raw_bindings.len();
            local_struct_downgrades.extend_forced_raw_bindings(&mut forced_raw_bindings);
            forced_raw_bindings.extend(unsupported_box_input_bindings);
            forced_raw_bindings.extend(raw_call_result_bindings);
            forced_raw_bindings.extend(raw_local_assignment_bindings);
            forced_raw_bindings.extend(unsupported_box_target_bindings);
            forced_raw_bindings.extend(unsupported_box_usage_bindings);
            if forced_raw_bindings.len() != old_len {
                changed = true;
                normalize_forced_raw_bindings(
                    rust_program.tcx,
                    &mut ptr_kinds,
                    &forced_raw_bindings,
                );
                normalize_owning_call_result_bindings(
                    rust_program.tcx,
                    &sig_decs,
                    &mut ptr_kinds,
                    &forced_raw_bindings,
                );
            }
            if !changed {
                break;
            }
            ptr_kinds = collect_diffs(rust_program, analysis, &sig_decs, &fn_ptr_groups);
            normalize_forced_raw_bindings(rust_program.tcx, &mut ptr_kinds, &forced_raw_bindings);
            normalize_owning_call_result_bindings(
                rust_program.tcx,
                &sig_decs,
                &mut ptr_kinds,
                &forced_raw_bindings,
            );
        }

        let alloc_wrappers = collect_local_allocator_wrappers(rust_program.tcx);
        let raw_scalar_bridge_fields =
            collect_raw_scalar_bridge_fields(rust_program.tcx, &alloc_wrappers);
        let (c_exposed_abi_fields, c_exposed_thin_abi_fields, c_exposed_cursor_abi_fields) =
            collect_c_exposed_abi_fields(rust_program, &config.c_exposed_fns, &sig_decs);
        let field_cursor_fields = analysis.offset_sign_result.field_access_signs.clone();
        let demoted_fields =
            collect_demoted_promoted_fields(rust_program.tcx, analysis, &sig_decs, &ptr_kinds);
        let (demoted_field_source_bindings, raw_field_source_callees) =
            collect_raw_field_source_bindings(
                rust_program.tcx,
                analysis,
                &sig_decs,
                &ptr_kinds,
                &demoted_fields,
            );
        let mut sig_changed = false;
        for hir_id in &demoted_field_source_bindings {
            if force_signature_input_raw_for_binding(rust_program.tcx, &mut sig_decs, *hir_id) {
                sig_changed = true;
                if let Some((did, idx)) = param_index_for_binding(rust_program.tcx, *hir_id) {
                    record_signature_input_event(
                        &mut diagnostics,
                        rust_program.tcx,
                        &sig_decs,
                        did,
                        idx,
                        DecisionReason::DemotedFieldSource,
                    );
                }
            }
        }
        record_binding_events_excluding(
            &mut diagnostics,
            rust_program.tcx,
            &ptr_kinds,
            &demoted_field_source_bindings,
            &forced_raw_bindings,
            DecisionReason::DemotedFieldSource,
        );
        for callee_did in raw_field_source_callees {
            if force_signature_output_raw(rust_program.tcx, &mut sig_decs, callee_did) {
                sig_changed = true;
                record_signature_output_event(
                    &mut diagnostics,
                    rust_program.tcx,
                    &sig_decs,
                    callee_did,
                    DecisionReason::DemotedFieldSourceCalleeOutput,
                );
            }
        }
        forced_raw_bindings.extend(demoted_field_source_bindings);
        if sig_changed {
            ptr_kinds = collect_diffs(rust_program, analysis, &sig_decs, &fn_ptr_groups);
        }
        normalize_forced_raw_bindings(rust_program.tcx, &mut ptr_kinds, &forced_raw_bindings);
        normalize_owning_call_result_bindings(
            rust_program.tcx,
            &sig_decs,
            &mut ptr_kinds,
            &forced_raw_bindings,
        );
        apply_field_storage_input_lifetimes(
            rust_program.tcx,
            analysis,
            &lifetime_plans,
            &demoted_fields,
            &field_cursor_fields,
            &mut sig_decs,
        );
        let raw_bridge_bindings = collect_raw_bridge_bindings(
            rust_program.tcx,
            &ptr_kinds,
            &alloc_wrappers,
            &free_like_wrappers,
            &local_raw_param_summaries,
        );
        let borrowed_raw_params =
            collect_borrowed_raw_params(rust_program.tcx, &initial_sig_decs, &sig_decs);

        let mut visitor = TransformVisitor {
            tcx: rust_program.tcx,
            analysis,
            sig_decs,
            lifetime_plans,
            ptr_kinds,
            forced_raw_bindings,
            borrowed_raw_params,
            raw_bridge_bindings,
            raw_scalar_bridge_fields,
            alloc_wrappers,
            free_like_wrappers,
            demoted_fields,
            field_cursor_fields,
            c_exposed_abi_fields,
            c_exposed_thin_abi_fields,
            c_exposed_cursor_abi_fields,
            impl_self_lifetimes: Vec::new(),
            ast_to_hir,
            fn_ptr_rewrite,
            bytemuck: Cell::new(false),
            bytemuck_derives: RefCell::new(BytemuckDerivePlan::default()),
            bytemuck_classifier: RefCell::new(BytemuckTypeClassifier::new(rust_program.tcx)),
            slice_cursor: Cell::new(false),
            diagnostics,
        };
        visitor.record_field_decisions();
        visitor
    }

    pub(crate) fn bytemuck_dependency(&self) -> BytemuckDependency {
        BytemuckDependency::from_flags(
            self.bytemuck.get(),
            !self.bytemuck_derives.borrow().is_empty(),
        )
    }

    pub(crate) fn emit_diagnostics(&self) {
        self.diagnostics.emit(self.tcx);
    }

    fn record_ast_fallback_binding(
        &mut self,
        hir_id: HirId,
        before: PtrKind,
        after: PtrKind,
        reason: DecisionReason,
    ) {
        if !self.diagnostics.is_enabled() || before == after {
            return;
        }
        let Some(subject) = subject_for_binding(self.tcx, hir_id) else {
            return;
        };
        self.diagnostics.record(
            subject,
            DecisionStage::AstRewriteFallback,
            Some(before),
            Some(after),
            reason,
            None,
        );
    }

    fn field_ptr_kind(&self, field: StructFieldSlot) -> Option<PtrKind> {
        let kind = if struct_field_is_exactly_owning(self.analysis, field) {
            self.ownership_field_kind(field)
        } else {
            self.promoted_field_kind(field)
        };
        if self.c_exposed_abi_fields.contains(&field) {
            return None;
        }
        if self.c_exposed_thin_abi_fields.contains(&field)
            && !matches!(kind, Some(PtrKind::OptRef(_)))
        {
            return None;
        }
        if self.c_exposed_cursor_abi_fields.contains(&field)
            && matches!(kind, Some(PtrKind::SliceCursor(_)))
        {
            return None;
        }
        kind
    }

    fn ownership_field_kind(&self, field: StructFieldSlot) -> Option<PtrKind> {
        ownership_field_ptr_kind(
            self.tcx,
            self.analysis,
            &self.sig_decs,
            &self.ptr_kinds,
            field,
        )
    }

    fn promoted_field_kind(&self, field: StructFieldSlot) -> Option<PtrKind> {
        if self.demoted_fields.contains(&field) {
            return None;
        }
        let mutability = if self
            .analysis
            .borrow_promotion_result
            .mutable_fields
            .contains(&field)
        {
            true
        } else if self
            .analysis
            .borrow_promotion_result
            .shared_fields
            .contains(&field)
        {
            false
        } else {
            return None;
        };
        if self.field_is_array_like(field) {
            if self.field_cursor_fields.contains(&field) {
                Some(PtrKind::SliceCursor(mutability))
            } else {
                Some(PtrKind::Slice(mutability))
            }
        } else {
            Some(PtrKind::OptRef(mutability))
        }
    }

    fn record_field_decisions(&mut self) {
        if !self.diagnostics.is_enabled() {
            return;
        }
        let mut promoted_fields = self.analysis.borrow_promotion_result.mutable_fields.clone();
        promoted_fields.extend(
            self.analysis
                .borrow_promotion_result
                .shared_fields
                .iter()
                .copied(),
        );
        let shape_demoted = collect_struct_shape_demoted_field_reasons(
            self.tcx,
            &promoted_fields,
            &self.analysis.borrow_promotion_result.mutable_fields,
            &self.analysis.struct_copy_result,
            &self.sig_decs,
            &self.ptr_kinds,
        );
        let conflict_reasons = collect_field_conflict_demotion_reasons(
            self.tcx,
            self.analysis,
            &self.sig_decs,
            &self.ptr_kinds,
        );

        let mut scalar_fields = FxHashMap::default();
        for field in local_struct_fields(self.tcx) {
            if let Some(Ok(inner_ty)) =
                owning_struct_field_scalar_inner_ty(self.tcx, self.analysis, field)
            {
                scalar_fields.insert(field, inner_ty);
            }
        }
        let ownership_block_reasons = collect_ownership_field_rhs_block_reasons(
            self.tcx,
            &self.sig_decs,
            &self.ptr_kinds,
            &scalar_fields,
        );

        for field in local_struct_fields(self.tcx) {
            let subject = DecisionSubject::Field {
                struct_did: field.struct_did,
                field_index: field.field_index,
            };
            let start_len = self.diagnostics.events().len();
            let pre_gate_kind = if struct_field_is_exactly_owning(self.analysis, field) {
                match owning_struct_field_scalar_inner_ty(self.tcx, self.analysis, field) {
                    Some(Ok(_)) => {
                        if let Some(reasons) = ownership_block_reasons.get(&field) {
                            for &reason in reasons {
                                self.diagnostics.record(
                                    subject,
                                    DecisionStage::OwnershipAnalysis,
                                    None,
                                    None,
                                    ownership_reason_to_decision_reason(reason),
                                    None,
                                );
                            }
                            None
                        } else {
                            self.diagnostics.record(
                                subject,
                                DecisionStage::OwnershipAnalysis,
                                None,
                                Some(PtrKind::OptBox),
                                DecisionReason::OwnershipFieldSelectedOptBox,
                                None,
                            );
                            Some(PtrKind::OptBox)
                        }
                    }
                    Some(Err(reason)) => {
                        self.diagnostics.record(
                            subject,
                            DecisionStage::OwnershipAnalysis,
                            None,
                            None,
                            ownership_reason_to_decision_reason(reason),
                            None,
                        );
                        None
                    }
                    None => None,
                }
            } else {
                if promoted_fields.contains(&field) {
                    let mutability = self
                        .analysis
                        .borrow_promotion_result
                        .mutable_fields
                        .contains(&field);
                    self.diagnostics.record(
                        subject,
                        DecisionStage::BorrowAnalysis,
                        None,
                        self.promoted_field_kind(field),
                        if mutability {
                            DecisionReason::BorrowFieldPromotedMutable
                        } else {
                            DecisionReason::BorrowFieldPromotedShared
                        },
                        None,
                    );
                    if self.field_is_array_like(field) {
                        self.diagnostics.record(
                            subject,
                            DecisionStage::BorrowAnalysis,
                            None,
                            self.promoted_field_kind(field),
                            DecisionReason::BorrowFieldArrayLike,
                            None,
                        );
                    }
                    if self.field_cursor_fields.contains(&field) {
                        self.diagnostics.record(
                            subject,
                            DecisionStage::BorrowAnalysis,
                            None,
                            self.promoted_field_kind(field),
                            DecisionReason::BorrowFieldNeedsCursor,
                            None,
                        );
                    }
                    if self.demoted_fields.contains(&field) {
                        for &reason in shape_demoted.get(&field).into_iter().flatten() {
                            self.diagnostics.record(
                                subject,
                                DecisionStage::FieldDemotion,
                                self.promoted_field_kind_without_demotions(field),
                                None,
                                reason,
                                None,
                            );
                        }
                        if let Some(reasons) = conflict_reasons.get(&field) {
                            self.diagnostics.record(
                                subject,
                                DecisionStage::FieldDemotion,
                                self.promoted_field_kind_without_demotions(field),
                                None,
                                DecisionReason::BorrowFieldConflictDemotion,
                                None,
                            );
                            for &reason in reasons {
                                self.diagnostics.record(
                                    subject,
                                    DecisionStage::FieldDemotion,
                                    self.promoted_field_kind_without_demotions(field),
                                    None,
                                    conflict_reason_to_decision_reason(reason),
                                    None,
                                );
                            }
                        }
                    }
                } else if hir_field_is_raw_ptr(self.tcx, field) {
                    self.diagnostics.record(
                        subject,
                        DecisionStage::OwnershipAnalysis,
                        None,
                        None,
                        DecisionReason::OwnershipFieldNotExactlyOwning,
                        None,
                    );
                }
                self.promoted_field_kind(field)
            };

            let final_kind = self.field_ptr_kind(field);
            if pre_gate_kind.is_some() && final_kind.is_none() {
                let reason = if self.c_exposed_abi_fields.contains(&field) {
                    Some(DecisionReason::CExposedAbiField)
                } else if self.c_exposed_thin_abi_fields.contains(&field) {
                    Some(DecisionReason::CExposedThinAbiField)
                } else if self.c_exposed_cursor_abi_fields.contains(&field) {
                    Some(DecisionReason::CExposedCursorAbiField)
                } else {
                    None
                };
                if let Some(reason) = reason {
                    self.diagnostics.record(
                        subject,
                        DecisionStage::AbiPreservation,
                        pre_gate_kind,
                        None,
                        reason,
                        None,
                    );
                }
            }
            if final_kind.is_some() || self.diagnostics.events().len() != start_len {
                self.diagnostics.record(
                    subject,
                    DecisionStage::Final,
                    final_kind,
                    final_kind,
                    DecisionReason::FinalDecision,
                    None,
                );
            }
        }
    }

    fn promoted_field_kind_without_demotions(&self, field: StructFieldSlot) -> Option<PtrKind> {
        let mutability = if self
            .analysis
            .borrow_promotion_result
            .mutable_fields
            .contains(&field)
        {
            true
        } else if self
            .analysis
            .borrow_promotion_result
            .shared_fields
            .contains(&field)
        {
            false
        } else {
            return None;
        };
        if self.field_is_array_like(field) {
            if self.field_cursor_fields.contains(&field) {
                Some(PtrKind::SliceCursor(mutability))
            } else {
                Some(PtrKind::Slice(mutability))
            }
        } else {
            Some(PtrKind::OptRef(mutability))
        }
    }

    fn field_is_array_like(&self, field: StructFieldSlot) -> bool {
        analysis_field_is_array_like(self.analysis, field)
    }

    fn mark_param_mut_if_needed(&self, param: &mut Param) {
        let Some(hir_pat) = self.ast_to_hir.get_pat(param.pat.id, self.tcx) else {
            return;
        };
        let hir::PatKind::Binding(_, hir_id, _ident, _) = hir_pat.kind else {
            return;
        };
        if !self.local_binding_needs_mut_for_promoted_field_write(hir_id) {
            return;
        }
        let PatKind::Ident(binding_mode, ..) = &mut param.pat.kind else {
            return;
        };
        binding_mode.1 = Mutability::Mut;
    }

    fn simplify_promoted_ref_field_base(
        &self,
        base: &mut P<Expr>,
        hir_base: &'tcx hir::Expr<'tcx>,
    ) {
        let hir::ExprKind::Unary(hir::UnOp::Deref, hir_inner) =
            utils::hir::unwrap_drop_temps(hir_base).kind
        else {
            return;
        };
        let Some(hir_id) =
            hir_unwrapped_local_id(hir_unwrap_addr_of_deref(hir_unwrap_cast(hir_inner)))
        else {
            return;
        };
        if !matches!(self.effective_ptr_kind(hir_id), Some(PtrKind::Ref(_))) {
            return;
        }
        let ExprKind::Unary(UnOp::Deref, inner) = &mut unwrap_paren_mut(base).kind else {
            return;
        };
        **base = unwrap_addr_of_deref(inner).clone();
    }

    fn rewrite_borrowed_raw_param_field_base(
        &self,
        base: &mut P<Expr>,
        hir_base: &'tcx hir::Expr<'tcx>,
    ) -> bool {
        let Some(hir_id) = hir_direct_raw_deref_local_id(hir_base) else {
            return false;
        };
        let Some(info) = self.borrowed_raw_params.get(&hir_id) else {
            return false;
        };
        **base = utils::expr!("{}", info.alias);
        true
    }

    fn insert_borrowed_raw_param_aliases(&self, def_id: LocalDefId, body: &mut Block) {
        let hir_body = self.tcx.hir_body_owned_by(def_id);
        let mut insert_at = 0usize;
        for param in hir_body.params {
            let hir::PatKind::Binding(_, hir_id, _, _) = param.pat.kind else {
                continue;
            };
            let Some(info) = self.borrowed_raw_params.get(&hir_id) else {
                continue;
            };
            let param_name = self.tcx.hir_name(hir_id).to_string();
            body.stmts.insert(
                insert_at,
                utils::stmt!("let {} = {}.as_mut().unwrap();", info.alias, param_name),
            );
            insert_at += 1;
        }
    }

    fn field_lifetime(&self, field: StructFieldSlot) -> Option<Symbol> {
        self.lifetime_plans
            .structs
            .get(&field.struct_did)
            .and_then(|plan| plan.field_lifetimes.get(&field.field_index).copied())
    }

    fn should_remove_generated_copy_clone_impl(&self, item: &Item) -> bool {
        if !utils::ast::is_automatically_derived(&item.attrs) {
            return false;
        }
        let ItemKind::Impl(box impl_item) = &item.kind else {
            return false;
        };
        let Some(of_trait) = &impl_item.of_trait else {
            return false;
        };
        if !of_trait
            .path
            .segments
            .last()
            .is_some_and(|seg| matches!(seg.ident.name.as_str(), "Copy" | "Clone"))
        {
            return false;
        }
        let Some(struct_did) = self.local_struct_did_for_ast_ty(&impl_item.self_ty) else {
            return false;
        };
        self.analysis
            .struct_copy_result
            .should_remove_generated_impl(struct_did)
            || self.struct_has_owning_box_field_candidate(struct_did)
    }

    fn struct_has_field_rewrite_candidate(&self, struct_did: LocalDefId) -> bool {
        self.tcx
            .adt_def(struct_did)
            .non_enum_variant()
            .fields
            .iter_enumerated()
            .any(|(field_index, _)| {
                self.field_ptr_kind(StructFieldSlot {
                    struct_did,
                    field_index: field_index.index(),
                })
                .is_some()
            })
    }

    fn struct_has_owning_box_field_candidate(&self, struct_did: LocalDefId) -> bool {
        self.tcx
            .adt_def(struct_did)
            .non_enum_variant()
            .fields
            .iter_enumerated()
            .any(|(field_index, _)| {
                self.field_ptr_kind(StructFieldSlot {
                    struct_did,
                    field_index: field_index.index(),
                }) == Some(PtrKind::OptBox)
            })
    }

    fn ordered_struct_lifetimes(&self, struct_did: LocalDefId) -> Vec<Symbol> {
        let Some(plan) = self.lifetime_plans.structs.get(&struct_did) else {
            return vec![];
        };
        let mut field_lifetimes: Vec<_> = plan.field_lifetimes.iter().collect();
        field_lifetimes.sort_by_key(|(field_index, _)| **field_index);
        field_lifetimes
            .into_iter()
            .filter(|(field_index, _)| {
                matches!(
                    self.field_ptr_kind(StructFieldSlot {
                        struct_did,
                        field_index: **field_index,
                    }),
                    Some(
                        PtrKind::Ref(_)
                            | PtrKind::OptRef(_)
                            | PtrKind::Slice(_)
                            | PtrKind::SliceCursor(_)
                    )
                )
            })
            .map(|(_, lifetime)| *lifetime)
            .collect()
    }

    fn rewrite_struct_definition(
        &self,
        struct_did: LocalDefId,
        generics: &mut Generics,
        fields: &mut ThinVec<FieldDef>,
    ) {
        let lifetimes = self.ordered_struct_lifetimes(struct_did);
        if !lifetimes.is_empty() {
            super::lifetimes::ensure_lifetime_params(generics, &lifetimes);
        }

        for (field_index, field_def) in fields.iter_mut().enumerate() {
            let field = StructFieldSlot {
                struct_did,
                field_index,
            };
            let Some(kind) = self.field_ptr_kind(field) else {
                continue;
            };
            let TyKind::Ptr(mut_ty) = &field_def.ty.kind else {
                continue;
            };
            let inner_ty = self.ast_ty_string_with_promoted_lifetimes(&mut_ty.ty);
            match kind {
                PtrKind::OptRef(mutability) => {
                    let Some(lifetime) = self.field_lifetime(field) else {
                        continue;
                    };
                    field_def.ty = P(mk_opt_ref_ast_ty_with_lifetime(
                        inner_ty, mutability, lifetime,
                    ));
                }
                PtrKind::OptBox => {
                    field_def.ty = P(utils::ty!("Option<Box<{inner_ty}>>"));
                }
                PtrKind::Slice(mutability) => {
                    let Some(lifetime) = self.field_lifetime(field) else {
                        continue;
                    };
                    field_def.ty = P(mk_slice_ast_ty_with_lifetime(
                        inner_ty, mutability, lifetime,
                    ));
                }
                PtrKind::SliceCursor(mutability) => {
                    let Some(lifetime) = self.field_lifetime(field) else {
                        continue;
                    };
                    field_def.ty = P(mk_cursor_ast_ty_with_lifetime(
                        inner_ty, mutability, lifetime,
                    ));
                    self.slice_cursor.set(true);
                }
                _ => {}
            }
        }
    }

    fn ast_ty_string_with_promoted_lifetimes(&self, ty: &Ty) -> String {
        let mut ty = ty.clone();
        self.add_promoted_lifetime_args_to_ast_ty(&mut ty);
        pprust::ty_to_string(&ty)
    }

    fn add_promoted_lifetime_args_to_ast_ty(&self, ty: &mut Ty) {
        struct FieldPointeeTyVisitor<'a, 'analysis, 'tcx> {
            transform: &'a TransformVisitor<'analysis, 'tcx>,
        }

        impl MutVisitor for FieldPointeeTyVisitor<'_, '_, '_> {
            fn visit_ty(&mut self, ty: &mut Ty) {
                mut_visit::walk_ty(self, ty);
                self.transform
                    .add_promoted_lifetime_args_to_ast_ty_shallow(ty);
            }
        }

        let mut visitor = FieldPointeeTyVisitor { transform: self };
        visitor.visit_ty(ty);
    }

    fn add_promoted_lifetime_args_to_ast_ty_shallow(&self, ty: &mut Ty) {
        let ty_str = pprust::ty_to_string(ty);
        let Some(hir_ty) = self.ast_to_hir.get_ty(ty.id, self.tcx) else {
            return;
        };
        let hir::TyKind::Path(qpath) = &hir_ty.kind else {
            return;
        };
        let Some(struct_did) = self.local_struct_did_from_qpath(qpath) else {
            return;
        };
        let lifetimes = self.ordered_struct_lifetimes(struct_did);
        if lifetimes.is_empty() {
            return;
        }
        let promoted_lifetime_args = lifetimes
            .iter()
            .map(|lifetime| format!("'{}", lifetime.as_str()))
            .collect::<Vec<_>>();
        *ty = utils::ty!(
            "{}",
            add_lifetime_args_to_type_path_string(
                ty_str,
                self.existing_lifetime_param_count(struct_did),
                &promoted_lifetime_args,
            )
        );
    }

    fn add_struct_lifetime_args_to_ty(&self, ty: &mut Ty) {
        let Some((struct_did, lifetimes)) = self.struct_lifetimes_for_ty(ty) else {
            return;
        };
        if self
            .impl_self_lifetimes
            .last()
            .is_some_and(|(impl_struct_did, _)| *impl_struct_did == struct_did)
        {
            self.add_struct_lifetime_args_to_ty_with_lifetimes(ty, &lifetimes);
        } else {
            self.add_struct_lifetime_args_to_ty_with_lifetime_count(ty, lifetimes.len());
        }
    }

    fn struct_lifetimes_for_ty(&self, ty: &Ty) -> Option<(LocalDefId, Vec<Symbol>)> {
        let struct_did = self.local_struct_did_for_ast_ty(ty)?;
        let lifetimes = self.ordered_struct_lifetimes(struct_did);
        if lifetimes.is_empty() {
            return None;
        }
        Some((struct_did, lifetimes))
    }

    fn local_struct_did_for_ast_ty(&self, ty: &Ty) -> Option<LocalDefId> {
        let hir_ty = self.ast_to_hir.get_ty(ty.id, self.tcx)?;
        let hir::TyKind::Path(hir_qpath) = hir_ty.kind else {
            return None;
        };
        self.local_struct_did_from_qpath(&hir_qpath)
    }

    fn add_struct_lifetime_args_to_ty_with_lifetimes(&self, ty: &mut Ty, lifetimes: &[Symbol]) {
        let Some((struct_did, _)) = self.struct_lifetimes_for_ty(ty) else {
            return;
        };
        let promoted_lifetime_args = lifetimes
            .iter()
            .map(|lifetime| format!("'{}", lifetime.as_str()))
            .collect::<Vec<_>>();
        self.add_struct_lifetime_args_to_ty_with_args(
            ty,
            struct_did,
            lifetimes,
            &promoted_lifetime_args,
        );
    }

    fn add_struct_lifetime_args_to_ty_with_lifetime_count(
        &self,
        ty: &mut Ty,
        lifetime_count: usize,
    ) {
        let Some((struct_did, lifetimes)) = self.struct_lifetimes_for_ty(ty) else {
            return;
        };
        let promoted_lifetime_args = std::iter::repeat_n("'_", lifetime_count)
            .map(str::to_string)
            .collect::<Vec<_>>();
        self.add_struct_lifetime_args_to_ty_with_args(
            ty,
            struct_did,
            &lifetimes,
            &promoted_lifetime_args,
        );
    }

    fn add_struct_lifetime_args_to_ty_with_args(
        &self,
        ty: &mut Ty,
        struct_did: LocalDefId,
        expected_lifetimes: &[Symbol],
        promoted_lifetime_args: &[String],
    ) {
        let TyKind::Path(None, path) = &ty.kind else {
            return;
        };
        if path.segments.last().is_some_and(|seg| {
            path_segment_has_expected_lifetimes(
                seg,
                self.existing_lifetime_param_count(struct_did),
                expected_lifetimes,
            )
        }) {
            return;
        }
        let ty_str = pprust::ty_to_string(ty);
        *ty = utils::ty!(
            "{}",
            add_lifetime_args_to_type_path_string(
                ty_str,
                self.existing_lifetime_param_count(struct_did),
                promoted_lifetime_args,
            )
        );
    }

    fn promoted_field_slot_for_hir_field(
        &self,
        hir_expr: &hir::Expr<'tcx>,
    ) -> Option<StructFieldSlot> {
        let hir::ExprKind::Field(base, ident) = hir_expr.kind else {
            return None;
        };
        let typeck = self.tcx.typeck(hir_expr.hir_id.owner);
        let struct_did = hir_local_struct_did_from_ty(typeck.expr_ty_adjusted(base))?;
        let field_index = self.field_index_by_name(struct_did, ident.name)?;
        let field = StructFieldSlot {
            struct_did,
            field_index,
        };
        self.field_ptr_kind(field).map(|_| field)
    }

    fn promoted_field_slot_for_ast_field(&self, ast_id: NodeId) -> Option<StructFieldSlot> {
        let hir_field = self.ast_to_hir.get_expr_field(ast_id, self.tcx)?;
        let hir::Node::Expr(parent) = self.tcx.parent_hir_node(hir_field.hir_id) else {
            return None;
        };
        let hir::ExprKind::Struct(qpath, _, _) = parent.kind else {
            return None;
        };
        let struct_did = self.local_struct_did_from_qpath(qpath)?;
        let field_index = self.field_index_by_name(struct_did, hir_field.ident.name)?;
        let field = StructFieldSlot {
            struct_did,
            field_index,
        };
        self.field_ptr_kind(field).map(|_| field)
    }

    fn rewrite_struct_literal_fields(&self, expr_id: NodeId, se: &mut StructExpr) {
        let Some(hir_expr) = self.ast_to_hir.get_expr(expr_id, self.tcx) else {
            return;
        };
        let hir::ExprKind::Struct(_, hir_fields, _) = hir_expr.kind else {
            return;
        };
        for ast_field in &mut se.fields {
            let Some(field) = self.promoted_field_slot_for_ast_field(ast_field.id) else {
                continue;
            };
            let Some(kind) = self.field_ptr_kind(field) else {
                continue;
            };
            let Some(hir_field) = hir_fields
                .iter()
                .find(|hir_field| hir_field.ident.name == ast_field.ident.name)
            else {
                continue;
            };
            self.transform_promoted_field_rhs(&mut ast_field.expr, hir_field.expr, kind, None);
        }
    }

    fn local_struct_did_from_qpath(&self, qpath: &hir::QPath<'tcx>) -> Option<LocalDefId> {
        let hir::QPath::Resolved(_, path) = qpath else {
            return None;
        };
        let Res::Def(DefKind::Struct, def_id) = path.res else {
            return None;
        };
        def_id.as_local()
    }

    fn field_index_by_name(&self, struct_did: LocalDefId, field_name: Symbol) -> Option<usize> {
        self.tcx
            .adt_def(struct_did)
            .non_enum_variant()
            .fields
            .iter_enumerated()
            .find_map(|(field_index, field)| {
                (field.name == field_name).then_some(field_index.index())
            })
    }

    fn extend_lifetimes_for_ty(&self, lifetimes: &mut Vec<Symbol>, ty: ty::Ty<'tcx>) {
        for lifetime in self.lifetimes_for_ty(ty) {
            if !lifetimes.contains(&lifetime) {
                lifetimes.push(lifetime);
            }
        }
    }

    fn lifetimes_for_ty(&self, ty: ty::Ty<'tcx>) -> Vec<Symbol> {
        let ty::TyKind::Adt(adt_def, _) = ty.kind() else {
            return vec![];
        };
        if !adt_def.did().is_local() || !adt_def.is_struct() {
            return vec![];
        }
        self.ordered_struct_lifetimes(adt_def.did().expect_local())
    }

    fn existing_lifetime_param_count_for_ty(&self, ty: ty::Ty<'tcx>) -> usize {
        let ty::TyKind::Adt(adt_def, _) = ty.kind() else {
            return 0;
        };
        if !adt_def.did().is_local() || !adt_def.is_struct() {
            return 0;
        }
        self.existing_lifetime_param_count(adt_def.did().expect_local())
    }

    fn existing_lifetime_param_count(&self, did: LocalDefId) -> usize {
        let hir::Node::Item(item) = self.tcx.hir_node_by_def_id(did) else {
            return 0;
        };
        let Some(generics) = item.kind.generics() else {
            return 0;
        };
        generics
            .params
            .iter()
            .filter(|param| matches!(param.kind, hir::GenericParamKind::Lifetime { .. }))
            .count()
    }

    fn ty_name(&self, ty: ty::Ty<'tcx>) -> String {
        self.promoted_mir_ty_name(ty, true)
    }

    fn anonymous_ty_name(&self, ty: ty::Ty<'tcx>) -> String {
        self.promoted_mir_ty_name(ty, false)
    }

    fn promoted_mir_ty_name(&self, ty: ty::Ty<'tcx>, use_named_struct_lifetimes: bool) -> String {
        match ty.kind() {
            ty::TyKind::Adt(adt_def, args) => {
                let mut args = args
                    .iter()
                    .map(|arg| match arg.kind() {
                        ty::GenericArgKind::Type(ty) => {
                            self.promoted_mir_ty_name(ty, use_named_struct_lifetimes)
                        }
                        ty::GenericArgKind::Const(cnst) => cnst.to_string(),
                        ty::GenericArgKind::Lifetime(_) => "'_".to_string(),
                    })
                    .collect::<Vec<_>>();
                let lifetimes = self.lifetimes_for_ty(ty);
                if !lifetimes.is_empty() {
                    let promoted_lifetime_args = if use_named_struct_lifetimes {
                        lifetimes
                            .iter()
                            .map(|lifetime| format!("'{}", lifetime.as_str()))
                            .collect::<Vec<_>>()
                    } else {
                        std::iter::repeat_n("'_".to_string(), lifetimes.len()).collect::<Vec<_>>()
                    };
                    let insert_at = self
                        .existing_lifetime_param_count_for_ty(ty)
                        .min(args.len());
                    if !generic_args_have_lifetimes(&args, insert_at, promoted_lifetime_args.len())
                    {
                        for (offset, lifetime) in promoted_lifetime_args.into_iter().enumerate() {
                            args.insert(insert_at + offset, lifetime);
                        }
                    }
                }
                let base = self.adt_type_name(*adt_def);
                if args.is_empty() {
                    base
                } else {
                    format!("{base}<{}>", args.join(", "))
                }
            }
            ty::TyKind::RawPtr(pointee, mutability) => {
                let m = if mutability.is_mut() { "mut" } else { "const" };
                format!(
                    "*{m} {}",
                    self.promoted_mir_ty_name(*pointee, use_named_struct_lifetimes)
                )
            }
            ty::TyKind::Ref(_, inner, mutability) => {
                let m = if mutability.is_mut() { "mut " } else { "" };
                format!(
                    "&{m}{}",
                    self.promoted_mir_ty_name(*inner, use_named_struct_lifetimes)
                )
            }
            ty::TyKind::Array(elem, len) => {
                format!(
                    "[{}; {len}]",
                    self.promoted_mir_ty_name(*elem, use_named_struct_lifetimes)
                )
            }
            ty::TyKind::Slice(elem) => format!(
                "[{}]",
                self.promoted_mir_ty_name(*elem, use_named_struct_lifetimes)
            ),
            ty::TyKind::Tuple(elems) => {
                let elems = elems
                    .iter()
                    .map(|elem| self.promoted_mir_ty_name(elem, use_named_struct_lifetimes))
                    .collect::<Vec<_>>();
                format!("({})", elems.join(", "))
            }
            ty::TyKind::Param(param) => param.name.as_str().to_owned(),
            _ => mir_ty_to_string(ty, self.tcx),
        }
    }

    fn adt_type_name(&self, adt_def: ty::AdtDef<'tcx>) -> String {
        let path_str = self.tcx.def_path_str(adt_def.did());
        if path_str.starts_with("std") {
            let name = self.tcx.item_name(adt_def.did());
            if matches!(
                name.as_str(),
                "Option" | "Result" | "Vec" | "String" | "Box"
            ) {
                name.as_str().to_owned()
            } else {
                path_str
            }
        } else {
            format!("crate::{path_str}")
        }
    }

    fn mk_ref_ty(&self, ty: ty::Ty<'tcx>, mutability: bool) -> Ty {
        let ty = self.anonymous_ty_name(ty);
        let m = if mutability { "mut " } else { "" };
        utils::ty!("&{m}{ty}")
    }

    fn mk_ref_ty_with_lifetime(
        &self,
        ty: ty::Ty<'tcx>,
        mutability: bool,
        lifetime: Option<Symbol>,
    ) -> Ty {
        let ty = self.ty_name(ty);
        let m = if mutability { "mut " } else { "" };
        let lifetime = lifetime
            .map(|lifetime| format!("'{} ", lifetime.as_str()))
            .unwrap_or_default();
        utils::ty!("&{lifetime}{m}{ty}")
    }

    fn mk_opt_ref_ty(&self, ty: ty::Ty<'tcx>, mutability: bool) -> Ty {
        let ty = self.anonymous_ty_name(ty);
        let m = if mutability { "mut " } else { "" };
        utils::ty!("Option<&{m}{ty}>")
    }

    fn mk_opt_ref_ty_with_lifetime(
        &self,
        ty: ty::Ty<'tcx>,
        mutability: bool,
        lifetime: Option<Symbol>,
    ) -> Ty {
        let ty = self.ty_name(ty);
        let m = if mutability { "mut " } else { "" };
        let lifetime = lifetime
            .map(|lifetime| format!("'{} ", lifetime.as_str()))
            .unwrap_or_default();
        utils::ty!("Option<&{lifetime}{m}{ty}>")
    }

    fn mk_box_ty(&self, ty: ty::Ty<'tcx>) -> Ty {
        let ty = self.ty_name(ty);
        utils::ty!("Box<{ty}>")
    }

    fn mk_local_box_ty(&self, ty: ty::Ty<'tcx>) -> Ty {
        let ty = self.anonymous_ty_name(ty);
        utils::ty!("Box<{ty}>")
    }

    fn mk_opt_box_ty(&self, ty: ty::Ty<'tcx>) -> Ty {
        let ty = self.ty_name(ty);
        utils::ty!("Option<Box<{ty}>>")
    }

    fn mk_local_opt_box_ty(&self, ty: ty::Ty<'tcx>) -> Ty {
        let ty = self.anonymous_ty_name(ty);
        utils::ty!("Option<Box<{ty}>>")
    }

    fn mk_boxed_slice_ty(&self, ty: ty::Ty<'tcx>) -> Ty {
        let ty = self.ty_name(ty);
        utils::ty!("Box<[{ty}]>")
    }

    fn mk_opt_boxed_slice_ty(&self, ty: ty::Ty<'tcx>) -> Ty {
        let ty = self.ty_name(ty);
        utils::ty!("Option<Box<[{ty}]>>")
    }

    fn mk_cursor_ty(&self, ty: ty::Ty<'tcx>, mutability: bool) -> Ty {
        let ty = self.ty_name(ty);
        if mutability {
            utils::ty!("crate::slice_cursor::SliceCursorMut<'_, {ty}>")
        } else {
            utils::ty!("crate::slice_cursor::SliceCursor<'_, {ty}>")
        }
    }

    fn mk_cursor_ty_with_lifetime(
        &self,
        ty: ty::Ty<'tcx>,
        mutability: bool,
        lifetime: Option<Symbol>,
    ) -> Ty {
        let ty = self.ty_name(ty);
        let cursor = if mutability {
            "SliceCursorMut"
        } else {
            "SliceCursor"
        };
        let lifetime = lifetime
            .map(|lifetime| format!("'{}", lifetime.as_str()))
            .unwrap_or_else(|| "'_".to_owned());
        utils::ty!("crate::slice_cursor::{cursor}<{lifetime}, {ty}>")
    }

    fn mk_slice_ty(&self, ty: ty::Ty<'tcx>, mutability: bool) -> Ty {
        let ty = self.ty_name(ty);
        if mutability {
            utils::ty!("&mut [{ty}]")
        } else {
            utils::ty!("&[{ty}]")
        }
    }

    fn mk_slice_ty_with_lifetime(
        &self,
        ty: ty::Ty<'tcx>,
        mutability: bool,
        lifetime: Option<Symbol>,
    ) -> Ty {
        let ty = self.ty_name(ty);
        let m = if mutability { "mut " } else { "" };
        let lifetime = lifetime
            .map(|lifetime| format!("'{} ", lifetime.as_str()))
            .unwrap_or_default();
        utils::ty!("&{lifetime}{m}[{ty}]")
    }

    fn mk_raw_ptr_ty(&self, ty: ty::Ty<'tcx>, mutability: bool) -> Ty {
        let ty = self.ty_name(ty);
        let m = if mutability { "mut" } else { "const" };
        utils::ty!("*{m} {ty}")
    }

    fn raw_from_promoted_field_expr(
        &self,
        field_expr: &Expr,
        mutability: bool,
        inner_ty: ty::Ty<'tcx>,
        field_kind: PtrKind,
    ) -> Expr {
        let field_expr = pprust::expr_to_string(field_expr);
        let inner_ty = self.ty_name(inner_ty);
        match field_kind {
            PtrKind::OptRef(_) | PtrKind::OptBox => {
                if mutability {
                    utils::expr!(
                        "({field_expr}).as_deref_mut().map_or(std::ptr::null_mut(), |r| r as *mut {inner_ty})"
                    )
                } else {
                    utils::expr!(
                        "({field_expr}).as_deref().map_or(std::ptr::null(), |r| r as *const {inner_ty})"
                    )
                }
            }
            PtrKind::Slice(_) | PtrKind::SliceCursor(_) => {
                if mutability {
                    utils::expr!("({field_expr}).as_mut_ptr() as *mut {inner_ty}")
                } else {
                    utils::expr!("({field_expr}).as_ptr() as *const {inner_ty}")
                }
            }
            _ => unreachable!(),
        }
    }

    fn try_bridge_raw_root(
        &self,
        rhs: &mut Expr,
        hir_rhs: &'tcx hir::Expr<'tcx>,
        lhs_kind: PtrKind,
        lhs_inner_ty: ty::Ty<'tcx>,
        lhs_hir_id: Option<HirId>,
    ) -> bool {
        let PtrKind::Raw(m) = lhs_kind else {
            return false;
        };
        let Some(lhs_hir_id) = lhs_hir_id else {
            return false;
        };
        let Some(current_info) = hir_raw_bridge_info(
            self.tcx,
            lhs_inner_ty,
            hir_rhs,
            Some(&self.alloc_wrappers),
            None,
        ) else {
            return false;
        };
        let info = self
            .raw_bridge_bindings
            .get(&lhs_hir_id)
            .cloned()
            .or_else(|| {
                self.alloc_wrappers
                    .contains_key(&lhs_hir_id.owner.def_id)
                    .then_some(current_info.clone())
            })
            .or_else(|| {
                (matches!(current_info, RawBridgeInfo::Scalar)
                    && ty_supports_scalar_box_from_raw_bridge(lhs_inner_ty))
                .then_some(current_info.clone())
            });
        let Some(info) = info else {
            return false;
        };
        if current_info != info {
            return false;
        }
        *rhs = self.raw_bridge_expr(lhs_inner_ty, m, &info);
        true
    }

    fn try_bridge_raw_projection_root(
        &self,
        rhs: &mut Expr,
        hir_rhs: &'tcx hir::Expr<'tcx>,
        hir_lhs: &'tcx hir::Expr<'tcx>,
        lhs_kind: PtrKind,
        lhs_inner_ty: ty::Ty<'tcx>,
    ) -> bool {
        let PtrKind::Raw(m) = lhs_kind else {
            return false;
        };
        if !ty_supports_scalar_box_from_raw_bridge(lhs_inner_ty) {
            return false;
        }
        let Some(field) = hir_struct_field_slot(self.tcx, hir_lhs) else {
            return false;
        };
        if !self.raw_scalar_bridge_fields.contains(&field) {
            return false;
        }
        let Some(info) = hir_raw_bridge_info(
            self.tcx,
            lhs_inner_ty,
            hir_rhs,
            Some(&self.alloc_wrappers),
            None,
        ) else {
            return false;
        };
        if !matches!(info, RawBridgeInfo::Scalar) {
            return false;
        }
        *rhs = self.raw_bridge_expr(lhs_inner_ty, m, &info);
        true
    }

    fn raw_bridge_expr(&self, lhs_inner_ty: ty::Ty<'tcx>, m: bool, info: &RawBridgeInfo) -> Expr {
        let ty = self.ty_name(lhs_inner_ty);
        let default_expr = self.default_value_expr(lhs_inner_ty);
        let default_expr_str = pprust::expr_to_string(&default_expr);
        match info {
            RawBridgeInfo::Scalar => utils::expr!(
                "Box::leak(Box::new({})) as *{} {}",
                default_expr_str,
                if m { "mut" } else { "const" },
                ty,
            ),
            RawBridgeInfo::Array { len_expr } => {
                let ptr_expr = if m {
                    format!(
                        "Box::leak(std::iter::repeat_with(|| {{ {default_expr_str} }}).take(({len_expr}) as usize).collect::<Vec<{ty}>>().into_boxed_slice()).as_mut_ptr()"
                    )
                } else {
                    format!(
                        "Box::leak(std::iter::repeat_with(|| {{ {default_expr_str} }}).take(({len_expr}) as usize).collect::<Vec<{ty}>>().into_boxed_slice()).as_ptr()"
                    )
                };
                utils::expr!("{ptr_expr}")
            }
        }
    }

    fn transform_return_rhs(
        &mut self,
        rhs: &mut Expr,
        hir_rhs: &'tcx hir::Expr<'tcx>,
        output_kind: PtrKind,
        lhs_inner_ty: ty::Ty<'tcx>,
    ) {
        let PtrKind::Raw(m) = output_kind else {
            self.transform_rhs(rhs, hir_rhs, output_kind);
            if matches!(output_kind, PtrKind::Ref(_)) {
                use_moving_opt_ref_unwraps_for_return(rhs);
            }
            return;
        };
        let Some((rhs_inner_ty, _)) = unwrap_ptr_from_mir_ty(
            self.tcx
                .typeck(hir_rhs.hir_id.owner)
                .expr_ty_adjusted(hir_rhs),
        ) else {
            self.transform_rhs(rhs, hir_rhs, output_kind);
            return;
        };
        let rhs_expr = unwrap_addr_of_deref(unwrap_cast_and_paren(rhs));
        let hir_rhs_expr = hir_unwrap_addr_of_deref(hir_unwrap_cast(hir_rhs));
        if let Some(pe) = self.ptr_expr(rhs_expr, hir_rhs_expr)
            && pe.projs.is_empty()
        {
            match self.ptr_source_kind(&pe) {
                Some(PtrKind::Box) => {
                    *rhs = self.raw_from_box_return(pe.base, m, lhs_inner_ty, rhs_inner_ty);
                    return;
                }
                Some(PtrKind::OptBox) => {
                    *rhs = self.raw_from_opt_box_return(pe.base, m, lhs_inner_ty, rhs_inner_ty);
                    return;
                }
                Some(PtrKind::BoxedSlice) => {
                    *rhs = self.raw_from_boxed_slice_return(pe.base, m, lhs_inner_ty, rhs_inner_ty);
                    return;
                }
                Some(PtrKind::OptBoxedSlice) => {
                    *rhs = self.raw_from_opt_boxed_slice_return(
                        pe.base,
                        m,
                        lhs_inner_ty,
                        rhs_inner_ty,
                    );
                    return;
                }
                _ => {}
            }
        }
        self.transform_rhs(rhs, hir_rhs, output_kind);
    }

    fn rewrite_direct_free_call(
        &self,
        hir_expr: &'tcx hir::Expr<'tcx>,
        args: &[P<Expr>],
    ) -> Option<Expr> {
        if let Some(field_free) = self.rewrite_owned_field_free_call(hir_expr, args) {
            return Some(field_free);
        }
        if let Some(call_result_free) = self.rewrite_owned_call_result_free_call(hir_expr) {
            return Some(call_result_free);
        }
        if let Some((hir_id, _harg)) =
            hir_free_like_arg_local_id(self.tcx, hir_expr, &self.free_like_wrappers)
        {
            if hir_call_matches_foreign_name(self.tcx, hir_expr, "free")
                && matches!(
                    self.effective_ptr_kind(hir_id),
                    Some(
                        PtrKind::Box
                            | PtrKind::OptBox
                            | PtrKind::BoxedSlice
                            | PtrKind::OptBoxedSlice
                    )
                )
            {
                let local_name = self.tcx.hir_name(hir_id).to_string();
                return match self.effective_ptr_kind(hir_id) {
                    Some(PtrKind::Box | PtrKind::BoxedSlice) => {
                        Some(utils::expr!("drop({local_name})"))
                    }
                    Some(PtrKind::OptBox | PtrKind::OptBoxedSlice) => {
                        Some(utils::expr!("drop(({local_name}).take())"))
                    }
                    _ => None,
                };
            }
            if let Some(info) = self.raw_bridge_bindings.get(&hir_id) {
                let [arg] = args else { return None };
                let arg_ty = self.tcx.typeck(hir_expr.hir_id.owner).node_type(hir_id);
                let (inner_ty, _) = unwrap_ptr_from_mir_ty(arg_ty)?;
                let arg_str = pprust::expr_to_string(arg);
                let inner_ty_str = mir_ty_to_string(inner_ty, self.tcx);
                return Some(match info {
                    RawBridgeInfo::Scalar => scalar_box_from_raw_free_expr(&arg_str, &inner_ty_str),
                    RawBridgeInfo::Array { len_expr } => {
                        array_box_from_raw_free_expr(&arg_str, &inner_ty_str, len_expr)
                    }
                });
            }
        }
        self.rewrite_scalar_box_from_raw_free_call(hir_expr, args)
    }

    fn rewrite_owned_call_result_free_call(&self, hir_expr: &'tcx hir::Expr<'tcx>) -> Option<Expr> {
        if !hir_call_matches_foreign_name(self.tcx, hir_expr, "free") {
            return None;
        }
        let hir::ExprKind::Call(_, hir_args) = hir_expr.kind else {
            return None;
        };
        let [hir_arg] = hir_args else { return None };
        let hir_arg = hir_unwrap_casts(hir_arg);
        if !matches!(
            hir_callee_output_kind(self.tcx, &self.sig_decs, &self.ptr_kinds, hir_arg),
            Some(PtrKind::Box | PtrKind::OptBox | PtrKind::BoxedSlice | PtrKind::OptBoxedSlice)
        ) {
            return None;
        }
        let call_expr = hir_expr_snippet(self.tcx, hir_arg)?;
        Some(utils::expr!("drop({call_expr})"))
    }

    fn rewrite_scalar_box_from_raw_free_call(
        &self,
        hir_expr: &'tcx hir::Expr<'tcx>,
        args: &[P<Expr>],
    ) -> Option<Expr> {
        if !hir_call_matches_foreign_name(self.tcx, hir_expr, "free") {
            return None;
        }
        let hir::ExprKind::Call(_, hir_args) = hir_expr.kind else {
            return None;
        };
        let [hir_arg] = hir_args else { return None };
        let [arg] = args else { return None };
        let hir_arg = hir_unwrap_casts(hir_arg);
        if let Some(field) = hir_struct_field_slot(self.tcx, hir_arg)
            && !self.raw_scalar_bridge_fields.contains(&field)
        {
            return None;
        }
        let arg_ty = self
            .tcx
            .typeck(hir_expr.hir_id.owner)
            .expr_ty_adjusted(hir_arg);
        let (inner_ty, _) = unwrap_ptr_from_mir_ty(arg_ty)?;
        if !ty_supports_scalar_box_from_raw_bridge(inner_ty) {
            return None;
        }
        let mut raw_arg = (**arg).clone();
        self.transform_rhs(&mut raw_arg, hir_arg, PtrKind::Raw(true));
        let arg_str = pprust::expr_to_string(&raw_arg);
        let inner_ty_str = mir_ty_to_string(inner_ty, self.tcx);
        Some(scalar_box_from_raw_free_expr(&arg_str, &inner_ty_str))
    }

    fn rewrite_owned_field_free_call(
        &self,
        hir_expr: &'tcx hir::Expr<'tcx>,
        args: &[P<Expr>],
    ) -> Option<Expr> {
        if !hir_call_matches_foreign_name(self.tcx, hir_expr, "free")
            && !hir_called_local_fn(self.tcx, hir_expr)
                .is_some_and(|def_id| self.free_like_wrappers.contains(&def_id))
        {
            return None;
        }
        let hir::ExprKind::Call(_, hir_args) = hir_expr.kind else {
            return None;
        };
        let [hir_arg] = hir_args else { return None };
        let [arg] = args else { return None };
        let hir_field = hir_unwrap_casts(hir_arg);
        let field = hir_struct_field_slot(self.tcx, hir_field)?;
        if !matches!(self.field_ptr_kind(field), Some(PtrKind::OptBox)) {
            return None;
        }
        let _ = arg;
        let field_expr = hir_field_access_expr_string(self.tcx, hir_field)?;
        Some(utils::expr!("drop(({}).take())", field_expr))
    }

    fn hir_id_of_path(&self, id: NodeId) -> Option<HirId> {
        let hir_rhs = self.ast_to_hir.get_expr(id, self.tcx)?;
        let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_rhs.kind else { return None };
        let Res::Local(hir_id) = path.res else { return None };
        Some(hir_id)
    }

    /// Returns fn-ptr group decisions for calls via struct-field fn-ptrs like
    /// `(struct.field).expect("...")(args)`. Checks for the `expect`/`unwrap` unwrap pattern.
    fn field_fn_ptr_decisions_for_call<'a>(
        &'a self,
        func: &hir::Expr<'tcx>,
    ) -> Option<&'a Vec<Option<PtrKind>>> {
        let func = utils::hir::unwrap_drop_temps(func);
        let hir::ExprKind::MethodCall(method_seg, receiver, _, _) = func.kind else {
            return None;
        };
        if !matches!(method_seg.ident.name.as_str(), "expect" | "unwrap") {
            return None;
        }
        let receiver = utils::hir::unwrap_drop_temps(receiver);
        let hir::ExprKind::Field(struct_expr, field_ident) = receiver.kind else { return None };
        let typeck = self.tcx.typeck(func.hir_id.owner);
        let struct_ty = typeck.expr_ty_adjusted(struct_expr);
        let ty::TyKind::Adt(adt_def, _) = struct_ty.kind() else { return None };
        if !adt_def.is_struct() {
            return None;
        }
        let struct_did = adt_def.did().as_local()?;
        let field_idx = adt_def
            .all_fields()
            .position(|f| f.name == field_ident.name)
            .map(FieldIdx::from_usize)?;
        self.fn_ptr_rewrite
            .field_decisions
            .get(&(struct_did, field_idx))
    }

    fn hir_expr_has_fn_ptr_group_cast(&self, expr: &'tcx hir::Expr<'tcx>) -> bool {
        struct CastFinder<'a> {
            direct_rewrite: &'a FxHashSet<LocalDefId>,
            found: bool,
        }
        impl<'tcx> Visitor<'tcx> for CastFinder<'_> {
            fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
                if self.found {
                    return;
                }
                if let hir::ExprKind::Cast(inner, _) = expr.kind {
                    let inner = utils::hir::unwrap_drop_temps(inner);
                    if let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = inner.kind
                        && let hir::def::Res::Def(_, def_id) = path.res
                        && let Some(local_did) = def_id.as_local()
                        && self.direct_rewrite.contains(&local_did)
                    {
                        self.found = true;
                        return;
                    }
                }
                intravisit::walk_expr(self, expr);
            }
        }
        let mut finder = CastFinder {
            direct_rewrite: &self.fn_ptr_rewrite.direct_rewrite,
            found: false,
        };
        finder.visit_expr(expr);
        finder.found
    }

    fn effective_ptr_kind(&self, hir_id: HirId) -> Option<PtrKind> {
        let kind = self.ptr_kinds.get(&hir_id).copied()?;
        if self.forced_raw_bindings.contains(&hir_id) {
            match kind {
                PtrKind::Raw(_) => Some(kind),
                other => Some(PtrKind::Raw(other.is_mut())),
            }
        } else {
            Some(kind)
        }
    }

    fn forced_local_callee_output_kind(&self, hir_expr: &hir::Expr<'tcx>) -> Option<PtrKind> {
        let def_id = local_called_fn_def_id(self.tcx, hir_expr)?;
        effective_callee_output_kind(self.tcx, &self.sig_decs, &self.ptr_kinds, def_id)
    }

    fn rhs_supports_box_target(
        &self,
        hir_expr: &hir::Expr<'tcx>,
        target_kind: PtrKind,
        lhs_inner_ty: ty::Ty<'tcx>,
    ) -> bool {
        let hir_uncast = hir_unwrap_casts(hir_expr);
        if hir_is_null_like_ptr_arg(self.tcx, hir_uncast) {
            return true;
        }

        match target_kind {
            PtrKind::Box | PtrKind::OptBox => {
                if hir_supports_scalar_box_allocator_root(self.tcx, lhs_inner_ty, hir_uncast) {
                    return true;
                }
            }
            PtrKind::BoxedSlice | PtrKind::OptBoxedSlice => {
                if hir_is_supported_boxed_slice_allocator_root(self.tcx, hir_uncast) {
                    return true;
                }
            }
            _ => return true,
        }

        let callee_output = self.forced_local_callee_output_kind(hir_expr);
        if callee_output.is_some_and(|kind| ptr_kind_supports_box_target(kind, target_kind)) {
            return true;
        }

        if let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_expr.kind
            && let Res::Local(hir_id) = path.res
            && let Some(rhs_kind) = self.effective_ptr_kind(hir_id)
            && ptr_kind_supports_box_target(rhs_kind, target_kind)
        {
            return true;
        }

        false
    }

    fn fn_has_unsupported_box_assignment(
        &self,
        target_hir_id: HirId,
        target_kind: PtrKind,
        lhs_inner_ty: ty::Ty<'tcx>,
    ) -> bool {
        struct UnsupportedBoxAssignmentVisitor<'a, 'analysis, 'tcx> {
            transform: &'a TransformVisitor<'analysis, 'tcx>,
            target_hir_id: HirId,
            target_kind: PtrKind,
            lhs_inner_ty: ty::Ty<'tcx>,
            found: bool,
        }

        impl<'tcx> Visitor<'tcx> for UnsupportedBoxAssignmentVisitor<'_, '_, 'tcx> {
            fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
                if self.found {
                    return;
                }
                if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                    && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = lhs.kind
                    && let Res::Local(lhs_hir_id) = path.res
                    && lhs_hir_id == self.target_hir_id
                    && !self.transform.rhs_supports_box_target(
                        rhs,
                        self.target_kind,
                        self.lhs_inner_ty,
                    )
                {
                    self.found = true;
                    return;
                }
                intravisit::walk_expr(self, expr);
            }
        }

        let body = self.tcx.hir_body_owned_by(target_hir_id.owner.def_id);
        let mut visitor = UnsupportedBoxAssignmentVisitor {
            transform: self,
            target_hir_id,
            target_kind,
            lhs_inner_ty,
            found: false,
        };
        visitor.visit_body(body);
        visitor.found
    }

    fn transform_rhs(
        &self,
        rhs: &mut Expr,
        hir_rhs: &hir::Expr<'tcx>,
        lhs_kind: PtrKind,
    ) -> PtrKind {
        self.transform_ptr(rhs, hir_rhs, PtrCtx::Rhs(lhs_kind))
    }

    fn transform_promoted_field_rhs(
        &self,
        rhs: &mut Expr,
        hir_rhs: &hir::Expr<'tcx>,
        field_kind: PtrKind,
        target_inner_ty: Option<ty::Ty<'tcx>>,
    ) -> PtrKind {
        if self.try_transform_raw_pointer_to_promoted_field(
            rhs,
            hir_rhs,
            field_kind,
            target_inner_ty,
        ) || self.try_transform_slice_to_promoted_field(
            rhs,
            hir_rhs,
            field_kind,
            target_inner_ty,
        ) {
            field_kind
        } else {
            self.transform_rhs(rhs, hir_rhs, field_kind)
        }
    }

    fn try_transform_raw_pointer_to_promoted_field(
        &self,
        rhs: &mut Expr,
        hir_rhs: &hir::Expr<'tcx>,
        field_kind: PtrKind,
        target_inner_ty: Option<ty::Ty<'tcx>>,
    ) -> bool {
        let PtrKind::OptRef(m) = field_kind else {
            return false;
        };
        if is_null_like_ptr_arg(unwrap_addr_of_deref(unwrap_cast_and_paren(rhs)))
            || hir_raw_addr_local(hir_rhs).is_some()
            || matches!(
                unwrap_cast_and_paren(rhs).kind,
                ExprKind::AddrOf(BorrowKind::Ref, ..)
            )
        {
            return false;
        }
        if let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_unwrap_cast(hir_rhs).kind
            && let Res::Local(hir_id) = path.res
            && !matches!(self.effective_ptr_kind(hir_id), Some(PtrKind::Raw(_)))
        {
            return false;
        }
        let typeck = self.tcx.typeck(hir_rhs.hir_id.owner);
        let Some((rhs_inner_ty, rhs_mut)) =
            unwrap_ptr_from_mir_ty(typeck.expr_ty_adjusted(hir_rhs))
        else {
            return false;
        };
        let lhs_inner_ty = target_inner_ty.unwrap_or(rhs_inner_ty);
        *rhs = self.opt_ref_from_raw_without_unsafe(
            unwrap_addr_of_deref(unwrap_paren(rhs)),
            m,
            rhs_mut.is_mut(),
            lhs_inner_ty,
            rhs_inner_ty,
        );
        true
    }

    fn try_transform_slice_to_promoted_field(
        &self,
        rhs: &mut Expr,
        hir_rhs: &hir::Expr<'tcx>,
        field_kind: PtrKind,
        target_inner_ty: Option<ty::Ty<'tcx>>,
    ) -> bool {
        let PtrKind::OptRef(m) = field_kind else {
            return false;
        };
        let e = unwrap_addr_of_deref(unwrap_cast_and_paren(rhs));
        let hir_e = hir_unwrap_addr_of_deref(hir_unwrap_cast(hir_rhs));
        let Some(pe) = self.ptr_expr(e, hir_e) else {
            return false;
        };
        if !pe.projs.is_empty() {
            return false;
        }
        let source_mutability = match self.ptr_source_kind(&pe) {
            Some(PtrKind::Slice(source_m)) | Some(PtrKind::SliceCursor(source_m)) => source_m,
            _ => return false,
        };
        if m && !source_mutability {
            return false;
        }
        let Some(rhs_inner_ty) = unwrap_ptr_or_arr_from_mir_ty(pe.base_ty, self.tcx) else {
            return false;
        };
        let lhs_inner_ty = target_inner_ty.unwrap_or(rhs_inner_ty);
        let ptr_method = if m { "as_mut_ptr" } else { "as_ptr" };
        let ref_method = if m { "as_mut" } else { "as_ref" };
        *rhs = if lhs_inner_ty == rhs_inner_ty {
            utils::expr!(
                "({}).{}().{}()",
                pprust::expr_to_string(pe.base),
                ptr_method,
                ref_method,
            )
        } else {
            utils::expr!(
                "(({}).{}() as *{} {}).{}()",
                pprust::expr_to_string(pe.base),
                ptr_method,
                if m { "mut" } else { "const" },
                mir_ty_to_string(lhs_inner_ty, self.tcx),
                ref_method,
            )
        };
        true
    }

    fn local_binding_needs_mut_for_promoted_field_write(&self, target_hir_id: HirId) -> bool {
        struct PromotedFieldWriteVisitor<'a, 'analysis, 'tcx> {
            transform: &'a TransformVisitor<'analysis, 'tcx>,
            target_hir_id: HirId,
            found: bool,
        }

        impl<'tcx> Visitor<'tcx> for PromotedFieldWriteVisitor<'_, '_, 'tcx> {
            fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
                if self.found {
                    return;
                }
                if let hir::ExprKind::Unary(UnOp::Deref, field_expr) = expr.kind
                    && matches!(self.transform.expr_ctx(expr), ExprCtx::Lvalue)
                    && hir_field_base_local_id(field_expr)
                        .is_some_and(|id| id == self.target_hir_id)
                    && let Some(field) =
                        self.transform.promoted_field_slot_for_hir_field(field_expr)
                    && matches!(
                        self.transform.field_ptr_kind(field),
                        Some(PtrKind::OptRef(true) | PtrKind::OptBox)
                    )
                {
                    self.found = true;
                    return;
                }
                intravisit::walk_expr(self, expr);
            }
        }

        let body = self.tcx.hir_body_owned_by(target_hir_id.owner.def_id);
        let mut visitor = PromotedFieldWriteVisitor {
            transform: self,
            target_hir_id,
            found: false,
        };
        visitor.visit_body(body);
        visitor.found
    }

    fn local_binding_needs_mut_for_owned_field_free(&self, target_hir_id: HirId) -> bool {
        struct OwnedFieldFreeVisitor<'a, 'analysis, 'tcx> {
            transform: &'a TransformVisitor<'analysis, 'tcx>,
            target_hir_id: HirId,
            found: bool,
        }

        impl<'tcx> Visitor<'tcx> for OwnedFieldFreeVisitor<'_, '_, 'tcx> {
            fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
                if self.found {
                    return;
                }
                let is_direct_free =
                    hir_call_matches_foreign_name(self.transform.tcx, expr, "free");
                let is_wrapper_free = hir_called_local_fn(self.transform.tcx, expr)
                    .is_some_and(|def_id| self.transform.free_like_wrappers.contains(&def_id));
                if (is_direct_free || is_wrapper_free)
                    && let hir::ExprKind::Call(_, args) = expr.kind
                    && let [arg] = args
                {
                    let field_expr = hir_unwrap_casts(arg);
                    if let Some(field) = hir_struct_field_slot(self.transform.tcx, field_expr)
                        && self.transform.field_ptr_kind(field) == Some(PtrKind::OptBox)
                        && hir_projection_root_local_id(field_expr) == Some(self.target_hir_id)
                    {
                        self.found = true;
                        return;
                    }
                }
                intravisit::walk_expr(self, expr);
            }
        }

        let body = self.tcx.hir_body_owned_by(target_hir_id.owner.def_id);
        let mut visitor = OwnedFieldFreeVisitor {
            transform: self,
            target_hir_id,
            found: false,
        };
        visitor.visit_body(body);
        visitor.found
    }

    fn transform_ptr(&self, ptr: &mut Expr, hir_ptr: &hir::Expr<'tcx>, ctx: PtrCtx) -> PtrKind {
        let allocator_root_expr = unwrap_addr_of_deref(unwrap_cast_and_paren(ptr)).clone();
        let e = unwrap_addr_of_deref_mut(unwrap_cast_and_paren_mut(ptr));
        let hir_e = hir_unwrap_addr_of_deref(hir_unwrap_cast(hir_ptr));

        if let ExprKind::If(_, t, Some(f)) = &mut e.kind {
            let hir::ExprKind::If(_, hir_t, Some(hir_f)) = hir_e.kind else {
                panic!("{}", pprust::expr_to_string(e));
            };
            let StmtKind::Expr(t) = &mut t.stmts.last_mut().unwrap().kind else {
                panic!("{}", pprust::expr_to_string(e));
            };
            let hir::ExprKind::Block(hir_t, _) = hir_t.kind else {
                panic!("{}", pprust::expr_to_string(e));
            };
            let kind1 = self.transform_ptr(t, hir_t.expr.unwrap(), ctx);
            let kind2 = if let ExprKind::Block(f, _) = &mut f.kind {
                let StmtKind::Expr(f) = &mut f.stmts.last_mut().unwrap().kind else {
                    panic!("{}", pprust::expr_to_string(e));
                };
                let hir::ExprKind::Block(hir_f, _) = hir_f.kind else {
                    panic!("{}", pprust::expr_to_string(e));
                };
                self.transform_ptr(f, hir_f.expr.unwrap(), ctx)
            } else {
                // if-else chain
                self.transform_ptr(f, hir_f, ctx)
            };
            assert_eq!(kind1, kind2);
            return kind1;
        }

        if let ExprKind::Block(block, _) = &mut e.kind {
            let hir::ExprKind::Block(hir_block, _) = hir_e.kind else {
                panic!("{}", pprust::expr_to_string(e));
            };
            let StmtKind::Expr(inner) = &mut block.stmts.last_mut().unwrap().kind else {
                panic!("{}", pprust::expr_to_string(e));
            };
            return self.transform_ptr(inner, hir_block.expr.unwrap(), ctx);
        }

        if is_null_ptr_constructor(&allocator_root_expr) {
            match ctx {
                PtrCtx::Rhs(PtrKind::Ref(_) | PtrKind::Box | PtrKind::BoxedSlice) => {
                    *ptr = utils::expr!("panic!()");
                    return match ctx {
                        PtrCtx::Rhs(kind) => kind,
                        PtrCtx::Deref(_) => unreachable!(),
                    };
                }
                PtrCtx::Rhs(PtrKind::SliceCursor(m)) => {
                    self.slice_cursor.set(true);
                    *ptr = if m {
                        utils::expr!("crate::slice_cursor::SliceCursorMut::empty()")
                    } else {
                        utils::expr!("crate::slice_cursor::SliceCursor::empty()")
                    };
                    return PtrKind::SliceCursor(m);
                }
                PtrCtx::Rhs(PtrKind::Slice(m)) => {
                    *ptr = if m {
                        utils::expr!("&mut []")
                    } else {
                        utils::expr!("&[]")
                    };
                    return PtrKind::Slice(m);
                }
                PtrCtx::Rhs(PtrKind::OptRef(m)) => {
                    *ptr = utils::expr!("None");
                    return PtrKind::OptRef(m);
                }
                PtrCtx::Rhs(PtrKind::OptBox) => {
                    *ptr = utils::expr!("None");
                    return PtrKind::OptBox;
                }
                PtrCtx::Rhs(PtrKind::OptBoxedSlice) => {
                    *ptr = utils::expr!("None");
                    return PtrKind::OptBoxedSlice;
                }
                PtrCtx::Rhs(PtrKind::Raw(m)) => {
                    *ptr = utils::expr!("std::ptr::null{}()", if m { "_mut" } else { "" });
                    return PtrKind::Raw(m);
                }
                PtrCtx::Deref(m) => return PtrKind::Raw(m),
            }
        }

        if let PtrCtx::Rhs(kind @ (PtrKind::Ref(_) | PtrKind::OptRef(_))) = ctx
            && let Some(pe) = self.ptr_expr(e, hir_e)
            && pe.projs.is_empty()
            && !hir_expr_starts_with_cast(hir_ptr)
            && self.ptr_source_kind(&pe) == Some(kind)
        {
            return kind;
        }

        if let PtrCtx::Rhs(kind @ (PtrKind::Ref(_) | PtrKind::Box | PtrKind::BoxedSlice)) = ctx {
            debug_assert!(!kind.is_optional());
            self.transform_ptr(ptr, hir_ptr, PtrCtx::Rhs(kind.optional_variant()));
            *ptr = match kind {
                PtrKind::Ref(m) if opt_ref_receiver_should_borrow(ptr) => {
                    utils::expr!(
                        "({}).as_deref{}().unwrap()",
                        pprust::expr_to_string(ptr),
                        if m { "_mut" } else { "" },
                    )
                }
                _ => utils::expr!("({}).unwrap()", pprust::expr_to_string(ptr)),
            };
            return kind;
        }

        if let PtrCtx::Rhs(kind @ (PtrKind::OptBox | PtrKind::OptBoxedSlice)) = ctx {
            let lhs_ty = self
                .tcx
                .typeck(hir_ptr.hir_id.owner)
                .expr_ty_adjusted(hir_ptr);
            let lhs_inner_ty = unwrap_ptr_or_arr_from_mir_ty(lhs_ty, self.tcx)
                .unwrap_or_else(|| panic!("{} {}", lhs_ty, pprust::expr_to_string(ptr)));
            if let Some(kind) = self.try_materialize_box_allocator_root(
                ptr,
                &allocator_root_expr,
                Some(hir_e),
                kind,
                lhs_inner_ty,
            ) {
                return kind;
            }
        }

        let e = unwrap_addr_of_deref(unwrap_cast_and_paren(ptr));
        let typeck = self.tcx.typeck(hir_ptr.hir_id.owner);
        let lhs_ty = typeck.expr_ty_adjusted(hir_ptr);
        let rhs_ty = typeck.expr_ty(hir_unwrap_cast(hir_ptr));
        if let PtrCtx::Rhs(
            kind @ (PtrKind::OptRef(_) | PtrKind::Slice(_) | PtrKind::SliceCursor(_)),
        ) = ctx
            && let Some(field) = self.promoted_field_slot_for_hir_field(hir_e)
            && self.field_ptr_kind(field) == Some(kind)
        {
            return kind;
        }
        if let PtrCtx::Rhs(PtrKind::Raw(m)) = ctx
            && let Some(field) = self.promoted_field_slot_for_hir_field(hir_e)
            && let Some(field_kind) = self.field_ptr_kind(field)
            && matches!(
                field_kind,
                PtrKind::OptRef(_) | PtrKind::OptBox | PtrKind::Slice(_) | PtrKind::SliceCursor(_)
            )
            && let Some((lhs_inner_ty, _)) = unwrap_ptr_from_mir_ty(lhs_ty)
        {
            *ptr = self.raw_from_promoted_field_expr(e, m, lhs_inner_ty, field_kind);
            return PtrKind::Raw(m);
        }
        let mut pe = if let Some(pe) = self.ptr_expr(e, hir_e) {
            pe
        } else if let Some((rhs_inner_ty, rhs_mut)) = unwrap_ptr_from_mir_ty(rhs_ty) {
            let lhs_inner_ty =
                unwrap_ptr_or_arr_from_mir_ty(lhs_ty, self.tcx).unwrap_or(rhs_inner_ty);
            match ctx {
                PtrCtx::Rhs(PtrKind::Ref(_) | PtrKind::Box | PtrKind::BoxedSlice) => {
                    unreachable!("non-optional pointer targets are handled before raw fallback")
                }
                PtrCtx::Rhs(PtrKind::Raw(m)) | PtrCtx::Deref(m) => {
                    if lhs_ty != rhs_ty {
                        *ptr = utils::expr!(
                            "{} as *{} {}",
                            pprust::expr_to_string(ptr),
                            if m { "mut" } else { "const" },
                            mir_ty_to_string(lhs_inner_ty, self.tcx),
                        );
                    } else if m && !rhs_mut.is_mut() {
                        *ptr = utils::expr!(
                            "{} as *mut {}",
                            pprust::expr_to_string(ptr),
                            mir_ty_to_string(rhs_inner_ty, self.tcx),
                        );
                    }
                    return PtrKind::Raw(m);
                }
                PtrCtx::Rhs(PtrKind::OptRef(m)) => {
                    *ptr =
                        self.opt_ref_from_raw(e, m, rhs_mut.is_mut(), lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::OptRef(m);
                }
                PtrCtx::Rhs(PtrKind::Slice(m)) => {
                    *ptr = self.slice_from_raw(e, m, rhs_mut.is_mut(), lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::Slice(m);
                }
                PtrCtx::Rhs(PtrKind::SliceCursor(m)) => {
                    self.slice_cursor.set(true);
                    *ptr = self.cursor_from_raw(e, m, rhs_mut.is_mut(), lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::SliceCursor(m);
                }
                PtrCtx::Rhs(PtrKind::OptBox) => {
                    *ptr = self.opt_box_from_raw(e, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::OptBox;
                }
                PtrCtx::Rhs(PtrKind::OptBoxedSlice) => {
                    panic!(
                        "owning array box target requires allocator-root length evidence: {}",
                        pprust::expr_to_string(ptr)
                    );
                }
            }
        } else {
            panic!("{}", pprust::expr_to_string(ptr));
        };

        if pe.is_zero() {
            // rhs_ty will be `usize`, not a pointer, so we early return here
            match ctx {
                PtrCtx::Rhs(PtrKind::Ref(_) | PtrKind::Box | PtrKind::BoxedSlice) => {
                    *ptr = utils::expr!("panic!()");
                    return match ctx {
                        PtrCtx::Rhs(kind) => kind,
                        PtrCtx::Deref(_) => unreachable!(),
                    };
                }
                PtrCtx::Rhs(PtrKind::SliceCursor(m)) => {
                    self.slice_cursor.set(true);
                    *ptr = if m {
                        utils::expr!("crate::slice_cursor::SliceCursorMut::empty()")
                    } else {
                        utils::expr!("crate::slice_cursor::SliceCursor::empty()")
                    };
                    return PtrKind::SliceCursor(m);
                }
                PtrCtx::Rhs(PtrKind::Slice(m)) => {
                    *ptr = if m {
                        utils::expr!("&mut []")
                    } else {
                        utils::expr!("&[]")
                    };
                    return PtrKind::Slice(m);
                }
                PtrCtx::Rhs(PtrKind::OptRef(m)) => {
                    *ptr = utils::expr!("None");
                    return PtrKind::OptRef(m);
                }
                PtrCtx::Rhs(PtrKind::OptBox) => {
                    *ptr = utils::expr!("None");
                    return PtrKind::OptBox;
                }
                PtrCtx::Rhs(PtrKind::OptBoxedSlice) => {
                    *ptr = utils::expr!("None");
                    return PtrKind::OptBoxedSlice;
                }
                PtrCtx::Rhs(PtrKind::Raw(m)) => {
                    *ptr = utils::expr!("std::ptr::null{}()", if m { "_mut" } else { "" });
                    return PtrKind::Raw(m);
                }
                PtrCtx::Deref(m) => {
                    return PtrKind::Raw(m);
                }
            }
        }

        if pe.cast_int {
            match ctx {
                PtrCtx::Rhs(PtrKind::Ref(_) | PtrKind::Box | PtrKind::BoxedSlice) => {
                    unreachable!("non-optional pointer targets are handled before casts")
                }
                PtrCtx::Rhs(PtrKind::Raw(m)) => {
                    let mut base = pe.base.clone();
                    // Rewrite inner pointer before integer casting
                    let kind =
                        self.transform_ptr(&mut base, pe.hir_base, PtrCtx::Rhs(PtrKind::Raw(m)));
                    pe.base = &base;
                    // Assume always need a cast from integer to pointer
                    pe.push_cast(lhs_ty);

                    let is_raw = matches!(kind, PtrKind::Raw(_));
                    *ptr = self.projected_expr(&pe, m, is_raw);
                    return PtrKind::Raw(m);
                }
                _ => panic!("{}", pprust::expr_to_string(ptr)),
            }
        }

        let lhs_inner_ty = unwrap_ptr_or_arr_from_mir_ty(lhs_ty, self.tcx).unwrap_or_else(|| {
            panic!("{} {} {}", lhs_ty, rhs_ty, pprust::expr_to_string(ptr));
        });
        let rhs_inner_ty = unwrap_ptr_or_arr_from_mir_ty(rhs_ty, self.tcx)
            .unwrap_or_else(|| panic!("{} {} {}", lhs_ty, rhs_ty, pprust::expr_to_string(ptr)));
        let need_cast = lhs_inner_ty != rhs_inner_ty;

        let def_id = hir_ptr.hir_id.owner.def_id;
        if let PtrCtx::Rhs(PtrKind::OptRef(m)) = ctx
            && let Some(field) = self.promoted_field_slot_for_hir_field(hir_e)
            && let Some(PtrKind::OptRef(source_m)) = self.field_ptr_kind(field)
        {
            *ptr = self.opt_ref_from_opt_ref(e, m, source_m, lhs_inner_ty, rhs_inner_ty, def_id);
            return PtrKind::OptRef(m);
        }

        if pe.addr_of {
            let addr_source_mut = addr_of_mutability(e).unwrap_or(false);
            let e = unwrap_addr_of(e);
            // if rhs is `&mut x` and `x`'s type has been updated, we need a cast
            let e_inner = unwrap_subscript(e);
            let ty_updated = if matches!(e_inner.kind, ExprKind::Path(_, _))
                && let Some(hir_e) = self.ast_to_hir.get_expr(e_inner.id, self.tcx)
                && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_e.kind
                && let Res::Local(hir_id) = path.res
            {
                matches!(
                    self.effective_ptr_kind(hir_id),
                    Some(
                        PtrKind::Ref(_)
                            | PtrKind::OptRef(_)
                            | PtrKind::Box
                            | PtrKind::OptBox
                            | PtrKind::BoxedSlice
                            | PtrKind::OptBoxedSlice
                            | PtrKind::Slice(_)
                            | PtrKind::SliceCursor(_)
                    )
                )
            } else {
                false
            };
            // Handle addr_of with pointer arithmetic (offset, wrapping_add, etc.)
            // by building a slice from the base and applying projections as slice ops.
            if pe.projs.iter().any(|p| {
                matches!(
                    p,
                    PtrExprProj::Offset(_)
                        | PtrExprProj::IntegerOp(..)
                        | PtrExprProj::IntegerBinOp(..)
                )
            }) {
                let m = match ctx {
                    PtrCtx::Rhs(PtrKind::Ref(m)) => m,
                    PtrCtx::Rhs(PtrKind::Raw(m))
                    | PtrCtx::Rhs(PtrKind::OptRef(m))
                    | PtrCtx::Rhs(PtrKind::Slice(m))
                    | PtrCtx::Rhs(PtrKind::SliceCursor(m))
                    | PtrCtx::Deref(m) => m,
                    PtrCtx::Rhs(
                        PtrKind::Box
                        | PtrKind::OptBox
                        | PtrKind::BoxedSlice
                        | PtrKind::OptBoxedSlice,
                    ) => {
                        panic!("unsupported M4A box target for addr_of arithmetic")
                    }
                };
                // Create initial slice from the single element:
                //   std::slice::from_mut(&mut x) or std::slice::from_ref(&x)
                let base_str = pprust::expr_to_string(pe.base);
                let mut result = utils::expr!(
                    "std::slice::from_{}(&{}({}))",
                    if m { "mut" } else { "ref" },
                    if m { "mut " } else { "" },
                    base_str,
                );
                // Apply projections (mirrors projected_expr logic for !is_raw)
                let mut from_ty = pe.base_ty;
                for proj in &pe.projs {
                    match proj {
                        PtrExprProj::Cast(ty) if !ty.is_usize() => {
                            let (to_ty, _) = unwrap_ptr_from_mir_ty(*ty).unwrap();
                            if from_ty != to_ty {
                                // slice to slice
                                result =
                                    self.plain_slice_from_slice(&result, &pe, m, to_ty, from_ty);
                            }
                            from_ty = to_ty;
                        }
                        PtrExprProj::Offset(offset) => {
                            result = utils::expr!(
                                "({})[({}) as usize..]",
                                pprust::expr_to_string(&result),
                                pprust::expr_to_string(offset),
                            );
                        }
                        // Complex arithmetic or cast-to-usize: leave as raw
                        _ => return PtrKind::Raw(m),
                    }
                }
                // Final wrapping depends on the target context
                match ctx {
                    PtrCtx::Rhs(PtrKind::Ref(_)) => {
                        unreachable!("non-optional pointer targets are handled before addr_of")
                    }
                    PtrCtx::Deref(m) | PtrCtx::Rhs(PtrKind::Slice(m)) => {
                        // slice to slice
                        *ptr = self.plain_slice_from_slice(
                            &result,
                            &pe,
                            m,
                            lhs_inner_ty,
                            rhs_inner_ty,
                        );
                        return PtrKind::Slice(m);
                    }
                    PtrCtx::Rhs(PtrKind::SliceCursor(m)) => {
                        // slice to cursor
                        self.slice_cursor.set(true);
                        *ptr = self.cursor_from_plain_slice(
                            &result,
                            &pe,
                            m,
                            lhs_inner_ty,
                            rhs_inner_ty,
                        );
                        return PtrKind::SliceCursor(m);
                    }
                    PtrCtx::Rhs(PtrKind::OptRef(m)) => {
                        // slice to optref
                        *ptr = self.opt_ref_from_slice_or_cursor(
                            &result,
                            m,
                            lhs_inner_ty,
                            rhs_inner_ty,
                            def_id,
                        );
                        return PtrKind::OptRef(m);
                    }
                    PtrCtx::Rhs(PtrKind::Raw(m)) => {
                        let (_, m_lhs) = unwrap_ptr_from_mir_ty(lhs_ty).unwrap();
                        // slice to raw
                        *ptr = self.raw_from_slice_or_cursor(
                            &result,
                            m,
                            m_lhs.is_mut(),
                            lhs_inner_ty,
                            rhs_inner_ty,
                        );
                        return PtrKind::Raw(m);
                    }
                    PtrCtx::Rhs(
                        PtrKind::Box
                        | PtrKind::OptBox
                        | PtrKind::BoxedSlice
                        | PtrKind::OptBoxedSlice,
                    ) => {
                        panic!("unsupported M4A box target for addr_of slice wrapping")
                    }
                }
            }
            match ctx {
                PtrCtx::Rhs(PtrKind::Slice(m)) => {
                    if let Some(slice) = self
                        .try_byte_slice_from_addr_of(
                            e,
                            pe.base_ty,
                            lhs_inner_ty,
                            m,
                            addr_source_mut,
                        )
                        .or_else(|| {
                            self.try_bytemuck_slice_from_addr_of(
                                e,
                                pe.base_ty,
                                lhs_inner_ty,
                                m,
                                addr_source_mut,
                            )
                        })
                    {
                        *ptr = slice;
                        return PtrKind::Slice(m);
                    }
                }
                PtrCtx::Rhs(PtrKind::SliceCursor(m)) => {
                    if let Some(slice) = self
                        .try_byte_slice_from_addr_of(
                            e,
                            pe.base_ty,
                            lhs_inner_ty,
                            m,
                            addr_source_mut,
                        )
                        .or_else(|| {
                            self.try_bytemuck_slice_from_addr_of(
                                e,
                                pe.base_ty,
                                lhs_inner_ty,
                                m,
                                addr_source_mut,
                            )
                        })
                    {
                        let cursor_ty = if m {
                            "crate::slice_cursor::SliceCursorMut"
                        } else {
                            "crate::slice_cursor::SliceCursor"
                        };
                        self.slice_cursor.set(true);
                        *ptr =
                            utils::expr!("{}::new({})", cursor_ty, pprust::expr_to_string(&slice));
                        return PtrKind::SliceCursor(m);
                    }
                }
                _ => {}
            }
            match ctx {
                PtrCtx::Rhs(PtrKind::Ref(_)) => {
                    unreachable!("non-optional pointer targets are handled before addr_of")
                }
                PtrCtx::Rhs(PtrKind::Raw(m)) => {
                    if !need_cast && !ty_updated {
                        *ptr = utils::expr!(
                            "&raw {} ({})",
                            if m { "mut" } else { "const" },
                            pprust::expr_to_string(e),
                        );
                    } else {
                        *ptr = utils::expr!(
                            "&raw {0} ({1}) as *{0} {2}",
                            if m { "mut" } else { "const" },
                            pprust::expr_to_string(e),
                            mir_ty_to_string(lhs_inner_ty, self.tcx),
                        );
                    }
                    return PtrKind::Raw(m);
                }
                PtrCtx::Rhs(PtrKind::OptRef(m)) | PtrCtx::Deref(m) => {
                    if !need_cast && !ty_updated {
                        let target = borrow_target_expr_string(e);
                        *ptr = utils::expr!("Some(&{}{})", if m { "mut " } else { "" }, target,);
                    } else if !ty_updated
                        && lhs_inner_ty.is_numeric()
                        && rhs_inner_ty.is_numeric()
                        && self.same_size(lhs_inner_ty, rhs_inner_ty, def_id)
                    {
                        self.bytemuck.set(true);
                        // can be used for deref, so type must be specified
                        *ptr = utils::expr!(
                            "Some(bytemuck::cast_{}::<_, {}>(&{}({})))",
                            if m { "mut" } else { "ref" },
                            mir_ty_to_string(lhs_inner_ty, self.tcx),
                            if m { "mut " } else { "" },
                            pprust::expr_to_string(e),
                        );
                    } else {
                        // can be used for deref, so type must be specified
                        *ptr = utils::expr!(
                            "Some(&{}*(&raw {1} ({2}) as *{1} {3}))",
                            if m { "mut " } else { "" },
                            if m { "mut" } else { "const" },
                            pprust::expr_to_string(e),
                            mir_ty_to_string(lhs_inner_ty, self.tcx),
                        );
                    }
                    return PtrKind::OptRef(m);
                }
                PtrCtx::Rhs(PtrKind::SliceCursor(m)) => {
                    // ref -> cursor
                    self.slice_cursor.set(true);
                    if !need_cast && !ty_updated {
                        *ptr = if m {
                            utils::expr!(
                                "crate::slice_cursor::SliceCursorMut::from_mut(&mut ({}))",
                                pprust::expr_to_string(e),
                            )
                        } else {
                            utils::expr!(
                                "crate::slice_cursor::SliceCursor::from_ref(&({}))",
                                pprust::expr_to_string(e),
                            )
                        };
                    } else if !ty_updated
                        && lhs_inner_ty.is_numeric()
                        && rhs_inner_ty.is_numeric()
                        && self.same_size(lhs_inner_ty, rhs_inner_ty, def_id)
                    {
                        self.bytemuck.set(true);
                        *ptr = if m {
                            utils::expr!(
                                "crate::slice_cursor::SliceCursorMut::new(std::slice::from_mut(bytemuck::cast_mut(&mut ({}))))",
                                pprust::expr_to_string(e),
                            )
                        } else {
                            utils::expr!(
                                "crate::slice_cursor::SliceCursor::new(std::slice::from_ref(bytemuck::cast_ref(&({}))))",
                                pprust::expr_to_string(e),
                            )
                        };
                    } else {
                        let rhs_ty_str = mir_ty_to_string(rhs_inner_ty, self.tcx);
                        let lhs_ty_str = mir_ty_to_string(lhs_inner_ty, self.tcx);
                        *ptr = if m {
                            utils::expr!(
                                "crate::slice_cursor::SliceCursorMut::from_raw_parts_mut(&raw mut ({0}) as *mut {1}, std::mem::size_of::<{2}>() / std::mem::size_of::<{1}>())",
                                pprust::expr_to_string(e),
                                lhs_ty_str,
                                rhs_ty_str,
                            )
                        } else {
                            utils::expr!(
                                "crate::slice_cursor::SliceCursor::from_raw_parts(&raw const ({0}) as *const {1}, std::mem::size_of::<{2}>() / std::mem::size_of::<{1}>())",
                                pprust::expr_to_string(e),
                                lhs_ty_str,
                                rhs_ty_str,
                            )
                        };
                    }
                    return PtrKind::SliceCursor(m);
                }
                PtrCtx::Rhs(PtrKind::Slice(m)) => {
                    // ref -> slice
                    if !need_cast && !ty_updated {
                        *ptr = utils::expr!(
                            "std::slice::from_{}(&{}({}))",
                            if m { "mut" } else { "ref" },
                            if m { "mut " } else { "" },
                            pprust::expr_to_string(e),
                        );
                    } else if !ty_updated
                        && lhs_inner_ty.is_numeric()
                        && rhs_inner_ty.is_numeric()
                        && self.same_size(lhs_inner_ty, rhs_inner_ty, def_id)
                    {
                        self.bytemuck.set(true);
                        *ptr = utils::expr!(
                            "std::slice::from_{0}(bytemuck::cast_{0}(&{1}({2})))",
                            if m { "mut" } else { "ref" },
                            if m { "mut " } else { "" },
                            pprust::expr_to_string(e),
                        );
                    } else {
                        *ptr = utils::expr!(
                            "std::slice::from_raw_parts{0}(&raw {1} ({2}) as *{1} _, 1_000_000)",
                            if m { "_mut" } else { "" },
                            if m { "mut" } else { "const" },
                            pprust::expr_to_string(e),
                        );
                    }
                    return PtrKind::Slice(m);
                }
                PtrCtx::Rhs(
                    PtrKind::Box | PtrKind::OptBox | PtrKind::BoxedSlice | PtrKind::OptBoxedSlice,
                ) => {
                    panic!("unsupported M4A box target for addr_of")
                }
            }
        }

        if pe.as_ptr && self.is_base_not_a_raw_ptr(&pe) {
            match ctx {
                PtrCtx::Rhs(PtrKind::OptRef(m)) => {
                    if let Some((base, source_inner_ty, is_slice_ref)) =
                        self.try_safe_slice_view_from_ptr_expr(&pe, m, lhs_inner_ty, def_id, false)
                    {
                        let slice = self.plain_slice_from_safe_view(
                            &base,
                            &pe,
                            m,
                            lhs_inner_ty,
                            source_inner_ty,
                            is_slice_ref,
                        );
                        *ptr = self.opt_ref_from_slice_or_cursor(
                            &slice,
                            m,
                            lhs_inner_ty,
                            lhs_inner_ty,
                            def_id,
                        );
                        return PtrKind::OptRef(m);
                    }
                }
                PtrCtx::Deref(m) => {
                    if let Some((base, source_inner_ty, is_slice_ref)) =
                        self.try_safe_slice_view_from_ptr_expr(&pe, m, lhs_inner_ty, def_id, false)
                    {
                        *ptr = self.plain_slice_from_safe_view(
                            &base,
                            &pe,
                            m,
                            lhs_inner_ty,
                            source_inner_ty,
                            is_slice_ref,
                        );
                        return PtrKind::Slice(m);
                    }
                }
                PtrCtx::Rhs(PtrKind::Slice(m)) => {
                    if let Some((base, source_inner_ty, is_slice_ref)) =
                        self.try_safe_slice_view_from_ptr_expr(&pe, m, lhs_inner_ty, def_id, true)
                    {
                        *ptr = self.plain_slice_from_safe_view(
                            &base,
                            &pe,
                            m,
                            lhs_inner_ty,
                            source_inner_ty,
                            is_slice_ref,
                        );
                        return PtrKind::Slice(m);
                    }
                }
                PtrCtx::Rhs(PtrKind::SliceCursor(m)) => {
                    if let Some((base, source_inner_ty, is_slice_ref)) =
                        self.try_safe_slice_view_from_ptr_expr(&pe, m, lhs_inner_ty, def_id, true)
                    {
                        self.slice_cursor.set(true);
                        *ptr = self.cursor_from_safe_slice_view(
                            &base,
                            &pe,
                            m,
                            lhs_inner_ty,
                            source_inner_ty,
                            is_slice_ref,
                        );
                        return PtrKind::SliceCursor(m);
                    }
                }
                _ => {}
            }
            let raw_expr = if let PtrCtx::Rhs(PtrKind::Raw(m)) = ctx
                && let Some(raw_expr) = self.array_field_offset_raw_ptr(&pe, m)
            {
                raw_expr
            } else if is_array_field_ptr_arithmetic(&pe) {
                e.clone()
            } else {
                let base = self.projected_expr(&pe, pe.as_mut_ptr, false);
                utils::expr!(
                    "({}).as_{}ptr()",
                    pprust::expr_to_string(&base),
                    if pe.as_mut_ptr { "mut_" } else { "" },
                )
            };
            match ctx {
                PtrCtx::Rhs(PtrKind::Ref(_)) => {
                    unreachable!("non-optional pointer targets are handled before as_ptr")
                }
                PtrCtx::Rhs(PtrKind::Raw(m)) => {
                    // when the source used as_ptr() (const) but there is an offset projection
                    // (a materialized cursor), the outer as-*mut cast was stripped by
                    // transform_ptr before ptr_expr ran, so projected_expr produces a const
                    // slice view. we must restore the mut intent via .cast_mut().
                    let has_offset_proj =
                        pe.projs.iter().any(|p| matches!(p, PtrExprProj::Offset(_)));
                    let needs_mut_cast = m && !pe.as_mut_ptr && has_offset_proj;
                    if !need_cast {
                        *ptr = if needs_mut_cast {
                            utils::expr!("({}).cast_mut()", pprust::expr_to_string(&raw_expr))
                        } else {
                            raw_expr
                        };
                    } else {
                        *ptr = utils::expr!(
                            "({}) as *{} _",
                            pprust::expr_to_string(&raw_expr),
                            if m { "mut" } else { "const" },
                        );
                    }
                    return PtrKind::Raw(m);
                }
                PtrCtx::Rhs(PtrKind::OptRef(m)) | PtrCtx::Deref(m) => {
                    *ptr = self.opt_ref_from_raw(
                        &raw_expr,
                        m,
                        pe.as_mut_ptr,
                        lhs_inner_ty,
                        rhs_inner_ty,
                    );
                    return PtrKind::OptRef(m);
                }
                PtrCtx::Rhs(PtrKind::SliceCursor(m)) => {
                    self.slice_cursor.set(true);
                    *ptr = self.cursor_from_raw(
                        &raw_expr,
                        m,
                        pe.as_mut_ptr,
                        lhs_inner_ty,
                        rhs_inner_ty,
                    );
                    return PtrKind::SliceCursor(m);
                }
                PtrCtx::Rhs(PtrKind::Slice(m)) => {
                    *ptr = self.slice_from_raw(
                        &raw_expr,
                        m,
                        pe.as_mut_ptr,
                        lhs_inner_ty,
                        rhs_inner_ty,
                    );
                    return PtrKind::Slice(m);
                }
                PtrCtx::Rhs(
                    PtrKind::Box | PtrKind::OptBox | PtrKind::BoxedSlice | PtrKind::OptBoxedSlice,
                ) => {
                    panic!("unsupported M4A box target for as_ptr")
                }
            }
        }

        if !pe.as_ptr && matches!(pe.base_ty.kind(), ty::TyKind::Array(..)) {
            match ctx {
                PtrCtx::Rhs(PtrKind::Ref(_)) => {
                    unreachable!("non-optional pointer targets are handled before array base")
                }
                PtrCtx::Rhs(PtrKind::Raw(m)) => {
                    let base = self.projected_expr(&pe, m, false);
                    *ptr = utils::expr!(
                        "({}).as_{}ptr()",
                        pprust::expr_to_string(&base),
                        if m { "mut_" } else { "" },
                    );
                    return PtrKind::Raw(m);
                }
                PtrCtx::Rhs(PtrKind::OptRef(m)) | PtrCtx::Deref(m) => {
                    let base = self.projected_expr(&pe, m, false);
                    if !need_cast {
                        *ptr = utils::expr!(
                            "Some(&{}({})[0])",
                            if m { "mut " } else { "" },
                            pprust::expr_to_string(&base),
                        );
                    } else if lhs_inner_ty.is_numeric()
                        && rhs_inner_ty.is_numeric()
                        && self.same_size(lhs_inner_ty, rhs_inner_ty, def_id)
                    {
                        self.bytemuck.set(true);
                        *ptr = utils::expr!(
                            "Some(bytemuck::cast_{}::<_, {}>(&{}({})[0]))",
                            if m { "mut" } else { "ref" },
                            mir_ty_to_string(lhs_inner_ty, self.tcx),
                            if m { "mut " } else { "" },
                            pprust::expr_to_string(&base),
                        );
                    } else {
                        *ptr = utils::expr!(
                            "Some(&{}*(({}).as_{}ptr() as *{} {}))",
                            if m { "mut " } else { "" },
                            pprust::expr_to_string(&base),
                            if m { "mut_" } else { "" },
                            if m { "mut" } else { "const" },
                            mir_ty_to_string(lhs_inner_ty, self.tcx),
                        );
                    }
                    return PtrKind::OptRef(m);
                }
                PtrCtx::Rhs(PtrKind::SliceCursor(m)) => {
                    self.slice_cursor.set(true);
                    let base = self.projected_expr(&pe, m, false);
                    *ptr = self.cursor_from_plain_slice(&base, &pe, m, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::SliceCursor(m);
                }
                PtrCtx::Rhs(PtrKind::Slice(m)) => {
                    let base = self.projected_expr(&pe, m, false);
                    *ptr = self.plain_slice_from_slice(&base, &pe, m, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::Slice(m);
                }
                PtrCtx::Rhs(
                    PtrKind::Box | PtrKind::OptBox | PtrKind::BoxedSlice | PtrKind::OptBoxedSlice,
                ) => {
                    panic!("unsupported M5 box target for array base")
                }
            }
        }

        if let Some(rhs_kind) = self.ptr_source_kind(&pe) {
            match (ctx, rhs_kind) {
                (PtrCtx::Rhs(PtrKind::Raw(m)) | PtrCtx::Deref(m), PtrKind::Raw(m1)) => {
                    if m && !m1 {
                        let inner_ty = mir_ty_to_string(lhs_inner_ty, self.tcx);
                        *ptr = utils::expr!("{} as *mut {}", pprust::expr_to_string(ptr), inner_ty);
                    }
                    return PtrKind::Raw(m);
                }
                (PtrCtx::Rhs(PtrKind::Raw(m)), PtrKind::Ref(m1)) => {
                    assert!(pe.projs.is_empty());
                    *ptr = self.raw_from_ref(pe.base, m, m1, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::Raw(m);
                }
                (PtrCtx::Rhs(PtrKind::Raw(m)), PtrKind::OptRef(m1)) => {
                    if pe.projs.is_empty() {
                        *ptr = self.raw_from_opt_ref(pe.base, m, m1, lhs_inner_ty, rhs_inner_ty);
                    } else if let Some((base, source_inner_ty)) =
                        self.projected_opt_ref_slice_expr(&pe, m, m1)
                    {
                        *ptr = self.raw_from_slice_or_cursor(
                            &base,
                            m,
                            m1,
                            lhs_inner_ty,
                            source_inner_ty,
                        );
                    } else {
                        *ptr =
                            self.raw_from_projected_opt_ref(&pe, m, m1, lhs_inner_ty, rhs_inner_ty);
                    }
                    return PtrKind::Raw(m);
                }
                (PtrCtx::Rhs(PtrKind::Raw(m)), PtrKind::Slice(m1)) => {
                    let base = self.projected_expr(&pe, m, false);
                    *ptr = self.raw_from_slice_or_cursor(&base, m, m1, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::Raw(m);
                }
                (PtrCtx::Rhs(PtrKind::Raw(m)), PtrKind::SliceCursor(m1)) => {
                    self.slice_cursor.set(true);
                    let base = self.projected_expr(&pe, m, false);
                    *ptr = self.raw_from_slice_or_cursor(&base, m, m1, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::Raw(m);
                }
                (PtrCtx::Rhs(PtrKind::OptRef(m)), PtrKind::Raw(m1)) => {
                    // to keep offsets, we use `e` instead of `pe.base`
                    *ptr = self.opt_ref_from_raw(e, m, m1, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::OptRef(m);
                }
                (PtrCtx::Rhs(PtrKind::OptRef(m)), PtrKind::Ref(m1)) => {
                    assert!(pe.projs.is_empty());
                    *ptr =
                        self.opt_ref_from_ref(pe.base, m, m1, lhs_inner_ty, rhs_inner_ty, def_id);
                    return PtrKind::OptRef(m);
                }
                (PtrCtx::Rhs(PtrKind::OptRef(m)), PtrKind::Box) => {
                    assert!(pe.projs.is_empty());
                    *ptr = self.opt_ref_from_box(pe.base, m, lhs_inner_ty, rhs_inner_ty, def_id);
                    return PtrKind::OptRef(m);
                }
                (PtrCtx::Rhs(PtrKind::OptRef(m)), PtrKind::OptBox) => {
                    assert!(pe.projs.is_empty());
                    *ptr =
                        self.opt_ref_from_opt_box(pe.base, m, lhs_inner_ty, rhs_inner_ty, def_id);
                    return PtrKind::OptRef(m);
                }
                (PtrCtx::Deref(m), PtrKind::Ref(m1)) => {
                    assert!(pe.projs.is_empty());
                    *ptr = self.ref_from_ref(pe.base, m, m1, lhs_inner_ty, rhs_inner_ty, def_id);
                    return PtrKind::Ref(m);
                }
                (PtrCtx::Deref(false), PtrKind::OptRef(false))
                    if !need_cast && pe.projs.is_empty() =>
                {
                    return PtrKind::OptRef(false);
                }
                (PtrCtx::Rhs(PtrKind::OptRef(m)) | PtrCtx::Deref(m), PtrKind::OptRef(m1)) => {
                    if pe.projs.is_empty() {
                        // can be used for deref, so type must be specified
                        *ptr = self.opt_ref_from_opt_ref(
                            pe.base,
                            m,
                            m1,
                            lhs_inner_ty,
                            rhs_inner_ty,
                            def_id,
                        );
                        return PtrKind::OptRef(m);
                    }
                    if let Some((base, source_inner_ty)) =
                        self.projected_opt_ref_slice_expr(&pe, m, m1)
                    {
                        match ctx {
                            PtrCtx::Deref(_) => {
                                *ptr = self.plain_slice_from_slice(
                                    &base,
                                    &pe,
                                    m,
                                    lhs_inner_ty,
                                    source_inner_ty,
                                );
                                return PtrKind::Slice(m);
                            }
                            PtrCtx::Rhs(PtrKind::OptRef(_)) => {
                                *ptr = self.opt_ref_from_slice_or_cursor(
                                    &base,
                                    m,
                                    lhs_inner_ty,
                                    source_inner_ty,
                                    def_id,
                                );
                                return PtrKind::OptRef(m);
                            }
                            _ => unreachable!(),
                        }
                    }
                    if matches!(ctx, PtrCtx::Deref(_)) {
                        *ptr = self.opt_ref_from_projected_opt_ref(
                            &pe,
                            m,
                            m1,
                            lhs_inner_ty,
                            rhs_inner_ty,
                        );
                        return PtrKind::OptRef(m);
                    }
                    *ptr = self.raw_from_projected_opt_ref(&pe, m, m1, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::Raw(m);
                }
                (PtrCtx::Rhs(PtrKind::OptRef(m)), PtrKind::BoxedSlice) => {
                    let (base, source_inner_ty) = self
                        .projected_boxed_slice_expr(&pe, m)
                        .unwrap_or_else(|| panic!("{}", pprust::expr_to_string(ptr)));
                    *ptr = self.opt_ref_from_slice_or_cursor(
                        &base,
                        m,
                        lhs_inner_ty,
                        source_inner_ty,
                        def_id,
                    );
                    return PtrKind::OptRef(m);
                }
                (PtrCtx::Rhs(PtrKind::OptRef(m)), PtrKind::OptBoxedSlice) => {
                    let (base, source_inner_ty) = self
                        .projected_opt_boxed_slice_expr(&pe, m)
                        .unwrap_or_else(|| panic!("{}", pprust::expr_to_string(ptr)));
                    *ptr = self.opt_ref_from_slice_or_cursor(
                        &base,
                        m,
                        lhs_inner_ty,
                        source_inner_ty,
                        def_id,
                    );
                    return PtrKind::OptRef(m);
                }
                (PtrCtx::Rhs(PtrKind::OptRef(m)), PtrKind::Slice(_)) => {
                    let base = self.projected_expr(&pe, m, false);
                    *ptr = self.opt_ref_from_slice_or_cursor(
                        &base,
                        m,
                        lhs_inner_ty,
                        rhs_inner_ty,
                        def_id,
                    );
                    return PtrKind::OptRef(m);
                }
                (PtrCtx::Rhs(PtrKind::OptRef(m)), PtrKind::SliceCursor(_)) => {
                    let base_str = pprust::expr_to_string(pe.base);
                    let offsets: Vec<String> = pe
                        .projs
                        .iter()
                        .filter_map(|p| {
                            if let PtrExprProj::Offset(o) = p {
                                Some(pprust::expr_to_string(o))
                            } else {
                                None
                            }
                        })
                        .collect();
                    let only_offsets = offsets.len() == pe.projs.len();

                    if only_offsets {
                        let as_slice = if m { "as_slice_mut" } else { "as_slice" };
                        let slice_expr = if offsets.is_empty() {
                            format!("({base_str}).{as_slice}()")
                        } else {
                            let offset_str = offsets.join(" + ");
                            format!(
                                "&{}({}).{}()[({}) as usize..]",
                                if m { "mut " } else { "" },
                                base_str,
                                as_slice,
                                offset_str,
                            )
                        };
                        *ptr = self.opt_ref_from_slice_or_cursor(
                            &utils::expr!("{}", slice_expr),
                            m,
                            lhs_inner_ty,
                            rhs_inner_ty,
                            def_id,
                        );
                    } else {
                        let base = self.projected_expr(&pe, m, false);
                        *ptr = self.opt_ref_from_slice_or_cursor(
                            &base,
                            m,
                            lhs_inner_ty,
                            rhs_inner_ty,
                            def_id,
                        );
                    }
                    return PtrKind::OptRef(m);
                }
                (PtrCtx::Rhs(PtrKind::Slice(m)), PtrKind::Raw(m1)) => {
                    // // Raw → slice: delegate via cursor then unwrap.
                    // to keep offsets, we use `e` instead of `pe.base`
                    *ptr = self.slice_from_raw(e, m, m1, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::Slice(m);
                }
                (PtrCtx::Rhs(PtrKind::Slice(m)), PtrKind::Ref(m1)) => {
                    assert!(pe.projs.is_empty());
                    *ptr = self.slice_from_ref(pe.base, m, m1, lhs_inner_ty, rhs_inner_ty, def_id);
                    return PtrKind::Slice(m);
                }
                (PtrCtx::Deref(_m), PtrKind::Box) => {
                    assert!(pe.projs.is_empty());
                    *ptr = self.box_from_box(pe.base, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::Box;
                }
                (PtrCtx::Deref(_m), PtrKind::OptBox) => {
                    assert!(pe.projs.is_empty());
                    *ptr = self.opt_box_from_opt_box(pe.base, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::OptBox;
                }
                (PtrCtx::Deref(m), PtrKind::BoxedSlice) => {
                    if pe.projs.is_empty() {
                        *ptr =
                            self.boxed_slice_from_boxed_slice(pe.base, lhs_inner_ty, rhs_inner_ty);
                        return PtrKind::BoxedSlice;
                    }
                    let (base, source_inner_ty) = self
                        .projected_boxed_slice_expr(&pe, m)
                        .unwrap_or_else(|| panic!("{}", pprust::expr_to_string(ptr)));
                    *ptr = self.plain_slice_from_expr(&base, m, lhs_inner_ty, source_inner_ty);
                    return PtrKind::Slice(m);
                }
                (PtrCtx::Deref(m), PtrKind::OptBoxedSlice) => {
                    if pe.projs.is_empty() {
                        *ptr = self.opt_boxed_slice_from_opt_boxed_slice(
                            pe.base,
                            lhs_inner_ty,
                            rhs_inner_ty,
                        );
                        return PtrKind::OptBoxedSlice;
                    }
                    let (base, source_inner_ty) = self
                        .projected_opt_boxed_slice_expr(&pe, m)
                        .unwrap_or_else(|| panic!("{}", pprust::expr_to_string(ptr)));
                    *ptr = self.plain_slice_from_expr(&base, m, lhs_inner_ty, source_inner_ty);
                    return PtrKind::Slice(m);
                }
                (PtrCtx::Rhs(PtrKind::Slice(m)) | PtrCtx::Deref(m), PtrKind::Slice(_)) => {
                    let base = self.projected_expr(&pe, m, false);
                    // can be used for deref, so type must be specified
                    *ptr = self.plain_slice_from_slice(&base, &pe, m, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::Slice(m);
                }
                (PtrCtx::Rhs(PtrKind::Slice(m)), PtrKind::BoxedSlice) => {
                    let (base, source_inner_ty) = self
                        .projected_boxed_slice_expr(&pe, m)
                        .unwrap_or_else(|| panic!("{}", pprust::expr_to_string(ptr)));
                    *ptr = self.plain_slice_from_expr(&base, m, lhs_inner_ty, source_inner_ty);
                    return PtrKind::Slice(m);
                }
                (PtrCtx::Rhs(PtrKind::Slice(m)), PtrKind::OptBoxedSlice) => {
                    let (base, source_inner_ty) = self
                        .projected_opt_boxed_slice_expr(&pe, m)
                        .unwrap_or_else(|| panic!("{}", pprust::expr_to_string(ptr)));
                    *ptr = self.plain_slice_from_expr(&base, m, lhs_inner_ty, source_inner_ty);
                    return PtrKind::Slice(m);
                }
                (PtrCtx::Rhs(PtrKind::Slice(m)), PtrKind::SliceCursor(_)) => {
                    let base = self.projected_expr(&pe, m, false);
                    *ptr = self.cursor_or_slice_to_slice_expr(&base, m);
                    return PtrKind::Slice(m);
                }
                (PtrCtx::Deref(m), PtrKind::SliceCursor(_)) => {
                    self.slice_cursor.set(true);
                    let base = self.projected_expr(&pe, m, false);
                    *ptr = self.cursor_from_cursor(&base, m, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::SliceCursor(m);
                }
                (PtrCtx::Rhs(PtrKind::SliceCursor(m)), PtrKind::Raw(m1)) => {
                    self.slice_cursor.set(true);
                    // to keep offsets, we use `e` instead of `pe.base`
                    *ptr = self.cursor_from_raw(e, m, m1, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::SliceCursor(m);
                }
                (PtrCtx::Rhs(PtrKind::SliceCursor(m)), PtrKind::Ref(m1)) => {
                    self.slice_cursor.set(true);
                    assert!(pe.projs.is_empty());
                    *ptr = self.cursor_from_ref(pe.base, &pe, m, m1, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::SliceCursor(m);
                }
                (PtrCtx::Rhs(PtrKind::SliceCursor(m)), PtrKind::BoxedSlice) => {
                    self.slice_cursor.set(true);
                    let base = self.boxed_slice_view_expr(pe.base, m);
                    *ptr =
                        self.cursor_from_slice_or_cursor(&base, &pe, m, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::SliceCursor(m);
                }
                (PtrCtx::Rhs(PtrKind::SliceCursor(m)), PtrKind::OptBoxedSlice) => {
                    self.slice_cursor.set(true);
                    let (base, source_inner_ty) = self
                        .projected_opt_boxed_slice_expr(&pe, m)
                        .unwrap_or_else(|| panic!("{}", pprust::expr_to_string(ptr)));
                    *ptr = self.cursor_from_slice_or_cursor(
                        &base,
                        &pe,
                        m,
                        lhs_inner_ty,
                        source_inner_ty,
                    );
                    return PtrKind::SliceCursor(m);
                }
                (PtrCtx::Rhs(PtrKind::SliceCursor(m)), PtrKind::Slice(_)) => {
                    // Plain slice → cursor
                    self.slice_cursor.set(true);
                    let base = self.projected_expr(&pe, m, false);
                    *ptr = self.cursor_from_plain_slice(&base, &pe, m, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::SliceCursor(m);
                }
                (PtrCtx::Rhs(PtrKind::SliceCursor(m)), PtrKind::SliceCursor(m1)) => {
                    // Cursor → cursor
                    self.slice_cursor.set(true);
                    let base = self.projected_expr(&pe, m, false);
                    let mut result =
                        self.cursor_from_slice_or_cursor(&base, &pe, m, lhs_inner_ty, rhs_inner_ty);
                    if !m && m1 && pe.projs.is_empty() && lhs_inner_ty == rhs_inner_ty {
                        result = utils::expr!("({}).as_deref()", pprust::expr_to_string(&result),);
                    }
                    // need fork only for identity copy (no projections, no cast)
                    if pe.projs.is_empty() && lhs_inner_ty == rhs_inner_ty && m1 && m {
                        result =
                            utils::expr!("({}).as_deref_mut()", pprust::expr_to_string(&result));
                    }
                    *ptr = result;
                    return PtrKind::SliceCursor(m);
                }
                (PtrCtx::Rhs(PtrKind::Slice(m)), PtrKind::OptRef(m1)) => {
                    let (base, source_inner_ty) = self
                        .projected_opt_ref_slice_expr(&pe, m, m1)
                        .unwrap_or_else(|| panic!("{}", pprust::expr_to_string(ptr)));
                    *ptr =
                        self.plain_slice_from_slice(&base, &pe, m, lhs_inner_ty, source_inner_ty);
                    return PtrKind::Slice(m);
                }
                (PtrCtx::Rhs(PtrKind::SliceCursor(m)), PtrKind::OptRef(m1)) => {
                    self.slice_cursor.set(true);
                    let (base, source_inner_ty) = self
                        .projected_opt_ref_slice_expr(&pe, m, m1)
                        .unwrap_or_else(|| panic!("{}", pprust::expr_to_string(ptr)));
                    *ptr =
                        self.cursor_from_plain_slice(&base, &pe, m, lhs_inner_ty, source_inner_ty);
                    return PtrKind::SliceCursor(m);
                }
                (
                    PtrCtx::Rhs(PtrKind::Slice(_) | PtrKind::SliceCursor(_)),
                    PtrKind::Box | PtrKind::OptBox,
                ) => {
                    panic!("unsupported M4A slice/cursor target from scalar owning box");
                }
                (PtrCtx::Rhs(PtrKind::Raw(m)), PtrKind::Box) => {
                    assert!(pe.projs.is_empty());
                    *ptr = self.raw_from_box(pe.base, m, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::Raw(m);
                }
                (PtrCtx::Rhs(PtrKind::Raw(m)), PtrKind::OptBox) => {
                    assert!(pe.projs.is_empty());
                    *ptr = self.raw_from_opt_box(pe.base, m, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::Raw(m);
                }
                (PtrCtx::Rhs(PtrKind::Raw(m)), PtrKind::BoxedSlice) => {
                    let (base, source_inner_ty) = self
                        .projected_boxed_slice_expr(&pe, m)
                        .unwrap_or_else(|| panic!("{}", pprust::expr_to_string(ptr)));
                    *ptr = self.raw_from_slice_or_cursor(
                        &base,
                        m,
                        true,
                        lhs_inner_ty,
                        source_inner_ty,
                    );
                    return PtrKind::Raw(m);
                }
                (PtrCtx::Rhs(PtrKind::Raw(m)), PtrKind::OptBoxedSlice) => {
                    let (base, source_inner_ty) = self
                        .projected_opt_boxed_slice_expr(&pe, m)
                        .unwrap_or_else(|| panic!("{}", pprust::expr_to_string(ptr)));
                    *ptr = self.raw_from_slice_or_cursor(
                        &base,
                        m,
                        true,
                        lhs_inner_ty,
                        source_inner_ty,
                    );
                    return PtrKind::Raw(m);
                }
                (PtrCtx::Rhs(PtrKind::OptBox), PtrKind::Box) => {
                    assert!(pe.projs.is_empty());
                    *ptr = utils::expr!("Some({})", pprust::expr_to_string(pe.base));
                    return PtrKind::OptBox;
                }
                (PtrCtx::Rhs(PtrKind::OptBox), PtrKind::OptBox) => {
                    assert!(pe.projs.is_empty());
                    *ptr = if matches!(pe.base_kind, PtrExprBaseKind::Path(Res::Local(_))) {
                        utils::expr!("({}).take()", pprust::expr_to_string(pe.base))
                    } else {
                        self.opt_box_from_opt_box(pe.base, lhs_inner_ty, rhs_inner_ty)
                    };
                    return PtrKind::OptBox;
                }
                (PtrCtx::Rhs(PtrKind::OptBox), PtrKind::Raw(_)) => {
                    assert!(pe.projs.is_empty());
                    *ptr = self.opt_box_from_raw(pe.base, lhs_inner_ty, rhs_inner_ty);
                    return PtrKind::OptBox;
                }
                (PtrCtx::Rhs(PtrKind::OptBoxedSlice), PtrKind::BoxedSlice) => {
                    assert!(pe.projs.is_empty());
                    *ptr = utils::expr!("Some({})", pprust::expr_to_string(pe.base));
                    return PtrKind::OptBoxedSlice;
                }
                (PtrCtx::Rhs(PtrKind::OptBoxedSlice), PtrKind::OptBoxedSlice) => {
                    assert!(pe.projs.is_empty());
                    *ptr = if matches!(pe.base_kind, PtrExprBaseKind::Path(Res::Local(_))) {
                        utils::expr!("({}).take()", pprust::expr_to_string(pe.base))
                    } else {
                        self.opt_boxed_slice_from_opt_boxed_slice(
                            pe.base,
                            lhs_inner_ty,
                            rhs_inner_ty,
                        )
                    };
                    return PtrKind::OptBoxedSlice;
                }
                (PtrCtx::Rhs(PtrKind::OptBoxedSlice), PtrKind::Raw(_)) => {
                    panic!(
                        "owning array box target requires allocator-root length evidence: {}",
                        pprust::expr_to_string(ptr)
                    );
                }
                (PtrCtx::Rhs(PtrKind::OptBox), other)
                | (PtrCtx::Rhs(PtrKind::OptBoxedSlice), other) => {
                    panic!("unsupported M4A box target/source combination: {other:?}");
                }
                (PtrCtx::Rhs(PtrKind::Ref(_) | PtrKind::Box | PtrKind::BoxedSlice), _) => {
                    unreachable!("non-optional pointer targets are handled before source matching")
                }
            }
        }

        if pe.base_kind == PtrExprBaseKind::ByteStr {
            match ctx {
                PtrCtx::Rhs(PtrKind::Ref(_) | PtrKind::Box | PtrKind::BoxedSlice) => {
                    unreachable!("non-optional pointer targets are handled before byte strings")
                }
                PtrCtx::Rhs(PtrKind::Raw(m)) => {
                    return PtrKind::Raw(m);
                }
                PtrCtx::Rhs(PtrKind::OptRef(m)) => {
                    assert!(!m, "{}", pprust::expr_to_string(ptr));
                    if lhs_inner_ty == self.tcx.types.u8 {
                        *ptr = utils::expr!("{}.first()", pprust::expr_to_string(e));
                    } else {
                        assert!(lhs_inner_ty.is_numeric());
                        self.bytemuck.set(true);
                        *ptr = utils::expr!(
                            "bytemuck::cast_slice({}).first()",
                            pprust::expr_to_string(e)
                        );
                    }
                    return PtrKind::OptRef(m);
                }
                PtrCtx::Rhs(PtrKind::OptBox | PtrKind::OptBoxedSlice) => {
                    panic!("unsupported M4A box target for byte string source")
                }
                PtrCtx::Rhs(PtrKind::SliceCursor(m)) => {
                    assert!(!m, "{}", pprust::expr_to_string(ptr));
                    self.slice_cursor.set(true);
                    if lhs_inner_ty == self.tcx.types.u8 {
                        *ptr = utils::expr!(
                            "crate::slice_cursor::SliceCursor::new({})",
                            pprust::expr_to_string(e)
                        );
                    } else {
                        assert!(lhs_inner_ty.is_numeric());
                        self.bytemuck.set(true);
                        *ptr = utils::expr!(
                            "crate::slice_cursor::SliceCursor::new(bytemuck::cast_slice({}))",
                            pprust::expr_to_string(e),
                        );
                    }
                    return PtrKind::SliceCursor(m);
                }
                PtrCtx::Rhs(PtrKind::Slice(m)) => {
                    assert!(!m, "{}", pprust::expr_to_string(ptr));
                    if lhs_inner_ty == self.tcx.types.u8 {
                        *ptr = e.clone();
                    } else {
                        assert!(lhs_inner_ty.is_numeric());
                        self.bytemuck.set(true);
                        *ptr = utils::expr!("bytemuck::cast_slice({})", pprust::expr_to_string(e),);
                    }
                    return PtrKind::Slice(m);
                }
                PtrCtx::Deref(_) => panic!(),
            }
        }

        let m1 = if let Some((_, rhs_mut)) = unwrap_ptr_from_mir_ty(rhs_ty) {
            rhs_mut.is_mut()
        } else {
            match pe.base_ty.kind() {
                ty::TyKind::RawPtr(_, m) | ty::TyKind::Ref(_, _, m) => m.is_mut(),
                ty::TyKind::Array(_, _) => match self.behind_subscripts(pe.hir_base) {
                    PathOrDeref::Path => true,
                    PathOrDeref::Deref(hir_id) => self.ptr_kinds[&hir_id].is_mut(),
                    PathOrDeref::Other => {
                        panic!("{}", pprust::expr_to_string(pe.base))
                    }
                },
                _ => panic!("{:?}", pe.base_ty),
            }
        };
        // Override m1 if this is a call to a function whose return type was changed
        let m1 = if let hir::ExprKind::Call(func, _) = pe.hir_base.kind
            && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = func.kind
            && let Res::Def(_, def_id) = path.res
            && let Some(def_id) = def_id.as_local()
            && let Some(PtrKind::Raw(m)) =
                self.sig_decs.data.get(&def_id).and_then(|sd| sd.output_dec)
        {
            m
        } else {
            m1
        };
        match ctx {
            PtrCtx::Rhs(PtrKind::Ref(_) | PtrKind::Box | PtrKind::BoxedSlice) => {
                unreachable!("non-optional pointer targets are handled before final raw fallback")
            }
            PtrCtx::Rhs(PtrKind::Raw(m)) | PtrCtx::Deref(m) => {
                if m && !m1 {
                    let inner_ty = mir_ty_to_string(lhs_inner_ty, self.tcx);
                    *ptr = utils::expr!("{} as *mut {}", pprust::expr_to_string(e), inner_ty);
                }
                PtrKind::Raw(m)
            }
            PtrCtx::Rhs(PtrKind::OptRef(m)) => {
                *ptr = self.opt_ref_from_raw(e, m, m1, lhs_inner_ty, rhs_inner_ty);
                PtrKind::OptRef(m)
            }
            PtrCtx::Rhs(PtrKind::OptBox) => {
                panic!(
                    "owning scalar box target requires allocator-root evidence: {}",
                    pprust::expr_to_string(ptr)
                )
            }
            PtrCtx::Rhs(PtrKind::OptBoxedSlice) => {
                panic!(
                    "owning array box target requires allocator-root length evidence: {}",
                    pprust::expr_to_string(ptr)
                )
            }
            PtrCtx::Rhs(PtrKind::SliceCursor(m)) => {
                self.slice_cursor.set(true);
                *ptr = self.cursor_from_raw(e, m, m1, lhs_inner_ty, rhs_inner_ty);
                PtrKind::SliceCursor(m)
            }
            PtrCtx::Rhs(PtrKind::Slice(m)) => {
                *ptr = self.slice_from_raw(e, m, m1, lhs_inner_ty, rhs_inner_ty);
                PtrKind::Slice(m)
            }
        }
    }

    fn cursor_or_slice_to_slice_expr(&self, e: &Expr, m: bool) -> Expr {
        let e = unwrap_paren(e);
        if matches!(e.kind, ExprKind::Index(..) | ExprKind::Array(..)) {
            utils::expr!(
                "&{}({})",
                if m { "mut " } else { "" },
                pprust::expr_to_string(e),
            )
        } else if let ExprKind::MethodCall(call) = &e.kind
            && matches!(call.seg.ident.name.as_str(), "as_slice" | "as_slice_mut")
        {
            e.clone()
        } else if is_std_slice_constructor_call(e) {
            e.clone()
        } else {
            let s = pprust::expr_to_string(e);
            if m {
                utils::expr!("({}).as_slice_mut()", s)
            } else {
                utils::expr!("({}).as_slice()", s)
            }
        }
    }

    fn ptr_source_kind(&self, pe: &PtrExpr<'_, 'tcx>) -> Option<PtrKind> {
        if let PtrExprBaseKind::Path(Res::Local(hir_id)) = pe.base_kind {
            return self.effective_ptr_kind(hir_id);
        }
        if let Some(field) = self.promoted_field_slot_for_hir_field(pe.hir_base) {
            return self.field_ptr_kind(field);
        }
        if let hir::ExprKind::Call(func, _) = pe.hir_base.kind
            && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = func.kind
            && let Res::Def(_, def_id) = path.res
            && let Some(def_id) = def_id.as_local()
        {
            return self.sig_decs.data.get(&def_id).and_then(|sd| sd.output_dec);
        }
        None
    }

    fn ptr_expr_base_is_cursor(&self, pe: &PtrExpr<'_, 'tcx>) -> bool {
        match pe.base_kind {
            PtrExprBaseKind::Path(Res::Local(hir_id)) => matches!(
                self.effective_ptr_kind(hir_id),
                Some(PtrKind::SliceCursor(_))
            ),
            _ => self
                .promoted_field_slot_for_hir_field(pe.hir_base)
                .and_then(|field| self.field_ptr_kind(field))
                .is_some_and(|kind| matches!(kind, PtrKind::SliceCursor(_))),
        }
    }

    fn allocator_root<'a>(&self, expr: &'a Expr) -> Option<AllocatorRoot<'a>> {
        let ExprKind::Call(callee, args) = &unwrap_cast_and_paren(expr).kind else {
            return None;
        };
        let ExprKind::Path(_, path) = &unwrap_paren(callee).kind else {
            return None;
        };
        let name = path.segments.last()?.ident.name.as_str();
        match (name, &args[..]) {
            ("malloc", [bytes]) => Some(AllocatorRoot::Malloc { bytes }),
            ("calloc", [count, elem_size]) => Some(AllocatorRoot::Calloc { count, elem_size }),
            ("realloc", [ptr, bytes]) if is_null_like_ptr_arg(ptr) => {
                Some(AllocatorRoot::Malloc { bytes })
            }
            _ => None,
        }
    }

    fn default_value_expr(&self, ty: ty::Ty<'tcx>) -> Expr {
        match ty.kind() {
            ty::TyKind::RawPtr(pointee, mutability) => utils::expr!(
                "std::ptr::null{}::<{}>()",
                if mutability.is_mut() { "_mut" } else { "" },
                self.ty_name(*pointee),
            ),
            ty::TyKind::Array(elem, _) => {
                let elem_expr = self.default_value_expr(*elem);
                utils::expr!(
                    "std::array::from_fn(|_| {{ {} }})",
                    pprust::expr_to_string(&elem_expr)
                )
            }
            ty::TyKind::Adt(adt_def, args) if adt_def.did().is_local() && adt_def.is_struct() => {
                let ty_name = strip_top_level_generic_args_from_type_path(self.ty_name(ty));
                let struct_did = adt_def.did().expect_local();
                let fields = adt_def
                    .all_fields()
                    .enumerate()
                    .map(|(field_index, field)| {
                        let field_name = self.tcx.item_name(field.did).as_str().to_owned();
                        let field_slot = StructFieldSlot {
                            struct_did,
                            field_index,
                        };
                        let field_expr = match self.field_ptr_kind(field_slot) {
                            Some(PtrKind::OptRef(_) | PtrKind::OptBox) => utils::expr!("None"),
                            Some(PtrKind::Slice(m)) => self.empty_slice_expr(m),
                            Some(PtrKind::SliceCursor(m)) => {
                                self.slice_cursor.set(true);
                                if m {
                                    utils::expr!("crate::slice_cursor::SliceCursorMut::empty()")
                                } else {
                                    utils::expr!("crate::slice_cursor::SliceCursor::empty()")
                                }
                            }
                            _ => self.default_value_expr(field.ty(self.tcx, args)),
                        };
                        format!("{field_name}: {}", pprust::expr_to_string(&field_expr))
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                utils::expr!("{} {{ {} }}", ty_name, fields)
            }
            ty::TyKind::Adt(adt_def, _) if adt_def.did().is_local() && adt_def.is_enum() => {
                let ty_name = self.ty_name(ty);
                let variant_name = fieldless_enum_zero_variant(self.tcx, *adt_def).unwrap();
                utils::expr!("{}::{}", ty_name, variant_name)
            }
            ty::TyKind::Adt(adt_def, _) if adt_def.did().is_local() && adt_def.is_union() => {
                let ty_name = self.ty_name(ty);
                utils::expr!("std::mem::MaybeUninit::<{ty_name}>::zeroed().assume_init()")
            }
            _ => {
                let ty = self.ty_name(ty);
                utils::expr!("<{ty} as Default>::default()")
            }
        }
    }

    fn empty_slice_expr(&self, m: bool) -> Expr {
        if m {
            utils::expr!("&mut []")
        } else {
            utils::expr!("&[]")
        }
    }

    fn opt_box_view_expr(&self, e: &Expr, m: bool) -> Expr {
        utils::expr!(
            "({}).as_deref{}()",
            pprust::expr_to_string(e),
            if m { "_mut" } else { "" },
        )
    }

    fn opt_boxed_slice_view_expr(&self, e: &Expr, m: bool) -> Expr {
        utils::expr!(
            "({}).as_deref{}().unwrap_or({})",
            pprust::expr_to_string(e),
            if m { "_mut" } else { "" },
            pprust::expr_to_string(&self.empty_slice_expr(m)),
        )
    }

    fn boxed_slice_view_expr(&self, e: &Expr, m: bool) -> Expr {
        utils::expr!(
            "&{}({})[..]",
            if m { "mut " } else { "" },
            pprust::expr_to_string(e),
        )
    }

    fn try_materialize_box_allocator_root(
        &self,
        ptr: &mut Expr,
        expr: &Expr,
        hir_expr: Option<&hir::Expr<'tcx>>,
        target_kind: PtrKind,
        lhs_inner_ty: ty::Ty<'tcx>,
    ) -> Option<PtrKind> {
        let alloc_root = self.allocator_root(expr)?;
        let ty = self.ty_name(lhs_inner_ty);
        let default_expr = self.default_value_expr(lhs_inner_ty);
        let default_expr_str = pprust::expr_to_string(&default_expr);
        match (target_kind, alloc_root) {
            (PtrKind::OptBox, _)
                if hir_expr.is_some_and(|hir_expr| {
                    hir_supports_scalar_box_allocator_root(self.tcx, lhs_inner_ty, hir_expr)
                }) || expr_supports_scalar_opt_box_allocator_root(
                    self.tcx,
                    expr,
                    lhs_inner_ty,
                ) =>
            {
                *ptr = utils::expr!("Some(Box::new({default_expr_str}))");
                Some(PtrKind::OptBox)
            }
            (PtrKind::Box, _)
                if hir_expr.is_some_and(|hir_expr| {
                    hir_supports_scalar_box_allocator_root(self.tcx, lhs_inner_ty, hir_expr)
                }) || expr_supports_scalar_opt_box_allocator_root(
                    self.tcx,
                    expr,
                    lhs_inner_ty,
                ) =>
            {
                *ptr = utils::expr!("Box::new({default_expr_str})");
                Some(PtrKind::Box)
            }
            (PtrKind::OptBoxedSlice, AllocatorRoot::Calloc { count, elem_size }) => {
                *ptr = utils::expr!(
                    "Some(std::iter::repeat_with(|| {0}).take((({1}) * ({2}) / std::mem::size_of::<{3}>()) as usize).collect::<Vec<{3}>>().into_boxed_slice())",
                    default_expr_str,
                    pprust::expr_to_string(count),
                    pprust::expr_to_string(elem_size),
                    ty,
                );
                Some(PtrKind::OptBoxedSlice)
            }
            (PtrKind::BoxedSlice, AllocatorRoot::Calloc { count, elem_size }) => {
                *ptr = utils::expr!(
                    "std::iter::repeat_with(|| {0}).take((({1}) * ({2}) / std::mem::size_of::<{3}>()) as usize).collect::<Vec<{3}>>().into_boxed_slice()",
                    default_expr_str,
                    pprust::expr_to_string(count),
                    pprust::expr_to_string(elem_size),
                    ty,
                );
                Some(PtrKind::BoxedSlice)
            }
            (PtrKind::OptBoxedSlice, AllocatorRoot::Malloc { bytes }) => {
                *ptr = utils::expr!(
                    "Some(std::iter::repeat_with(|| {0}).take((({1}) / std::mem::size_of::<{2}>()) as usize).collect::<Vec<{2}>>().into_boxed_slice())",
                    default_expr_str,
                    pprust::expr_to_string(bytes),
                    ty,
                );
                Some(PtrKind::OptBoxedSlice)
            }
            (PtrKind::BoxedSlice, AllocatorRoot::Malloc { bytes }) => {
                *ptr = utils::expr!(
                    "std::iter::repeat_with(|| {0}).take((({1}) / std::mem::size_of::<{2}>()) as usize).collect::<Vec<{2}>>().into_boxed_slice()",
                    default_expr_str,
                    pprust::expr_to_string(bytes),
                    ty,
                );
                Some(PtrKind::BoxedSlice)
            }
            _ => None,
        }
    }

    fn plain_slice_from_expr(
        &self,
        e: &Expr,
        m: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        let lhs_ty = mir_ty_to_string(lhs_inner_ty, self.tcx);
        let rhs_ty = mir_ty_to_string(rhs_inner_ty, self.tcx);
        if !need_cast {
            if matches!(e.kind, ExprKind::Index(..)) {
                utils::expr!(
                    "&{}({})",
                    if m { "mut " } else { "" },
                    pprust::expr_to_string(e),
                )
            } else {
                e.clone()
            }
        } else if (lhs_inner_ty.is_numeric() && rhs_inner_ty.is_numeric())
            || (!matches!(e.kind, ExprKind::Index(..))
                && self.try_require_bytemuck_slice_cast(rhs_inner_ty, lhs_inner_ty, m))
        {
            self.bytemuck.set(true);
            let reference = if matches!(e.kind, ExprKind::Index(..)) {
                if m { "&mut " } else { "&" }
            } else {
                ""
            };
            if reference.is_empty() {
                utils::expr!(
                    "bytemuck::cast_slice{}::<_, {}>({})",
                    if m { "_mut" } else { "" },
                    lhs_ty,
                    pprust::expr_to_string(e),
                )
            } else {
                utils::expr!(
                    "bytemuck::cast_slice{}::<_, {}>({}({}))",
                    if m { "_mut" } else { "" },
                    lhs_ty,
                    reference,
                    pprust::expr_to_string(e),
                )
            }
        } else {
            let ptr_method = if m { "as_mut_ptr" } else { "as_ptr" };
            utils::expr!(
                "std::slice::from_raw_parts{0}(({1}).{2}() as *{3} {4}, (({1}).len() * std::mem::size_of::<{5}>()) / std::mem::size_of::<{4}>())",
                if m { "_mut" } else { "" },
                pprust::expr_to_string(e),
                ptr_method,
                if m { "mut" } else { "const" },
                lhs_ty,
                rhs_ty,
            )
        }
    }

    fn try_safe_slice_view_from_ptr_expr(
        &self,
        pe: &PtrExpr<'_, 'tcx>,
        want_mut: bool,
        target_inner_ty: ty::Ty<'tcx>,
        def_id: LocalDefId,
        allow_resized_numeric_casts: bool,
    ) -> Option<(Expr, ty::Ty<'tcx>, bool)> {
        if !self.is_base_not_a_raw_ptr(pe) {
            return None;
        }
        if want_mut {
            let source_mut = if pe.as_ptr {
                pe.as_mut_ptr
            } else {
                self.projected_base_mutability(pe, false)
            };
            if !source_mut {
                return None;
            }
        }

        if let Some(base) = self.array_field_offset_slice_ref(pe, want_mut) {
            let source_inner_ty = unwrap_ptr_or_arr_from_mir_ty(pe.base_ty, self.tcx)?;
            if self.safe_slice_view_cast_allowed(
                source_inner_ty,
                target_inner_ty,
                want_mut,
                def_id,
                allow_resized_numeric_casts,
            ) {
                return Some((base, source_inner_ty, true));
            }
            return None;
        }
        if is_array_field_ptr_arithmetic(pe) {
            return None;
        }

        let mut source_inner_ty = slice_like_container_inner_ty(pe.base_ty, self.tcx)
            .or_else(|| unwrap_ptr_or_arr_from_mir_ty(pe.base_ty, self.tcx))?;
        let mut is_slice_ref = ty_is_slice_ref(pe.base_ty)
            || ty_is_borrowed_slice_like_container(pe.base_ty, self.tcx)
            || matches!(self.ptr_source_kind(pe), Some(PtrKind::Slice(_)));
        for proj in &pe.projs {
            match proj {
                PtrExprProj::Offset(_) => {
                    is_slice_ref = false;
                }
                PtrExprProj::Cast(ty) if ty.is_usize() => return None,
                PtrExprProj::Cast(ty) => {
                    let (to_ty, _) = unwrap_ptr_from_mir_ty(*ty)?;
                    if !self.safe_slice_view_cast_allowed(
                        source_inner_ty,
                        to_ty,
                        want_mut,
                        def_id,
                        allow_resized_numeric_casts,
                    ) {
                        return None;
                    }
                    source_inner_ty = to_ty;
                    is_slice_ref = true;
                }
                PtrExprProj::IntegerOp(..) | PtrExprProj::IntegerBinOp(..) => return None,
            }
        }
        if !self.safe_slice_view_cast_allowed(
            source_inner_ty,
            target_inner_ty,
            want_mut,
            def_id,
            allow_resized_numeric_casts,
        ) {
            return None;
        }

        Some((
            self.projected_expr(pe, want_mut, false),
            source_inner_ty,
            is_slice_ref,
        ))
    }

    fn array_field_offset_raw_ptr(&self, pe: &PtrExpr<'_, 'tcx>, m: bool) -> Option<Expr> {
        if m && !pe.as_mut_ptr {
            return None;
        }
        let offset = array_field_direct_offset(pe, true)?;
        let slice = self.array_field_offset_slice_ref_from_offset(pe, offset, m);
        let mut raw = utils::expr!(
            "({}).as_{}ptr()",
            pprust::expr_to_string(&slice),
            if m { "mut_" } else { "" },
        );
        for proj in &pe.projs[1..] {
            let PtrExprProj::Cast(ty) = proj else { unreachable!() };
            let (to_ty, mutability) = unwrap_ptr_from_mir_ty(*ty)?;
            raw = utils::expr!(
                "({}) as *{} {}",
                pprust::expr_to_string(&raw),
                if mutability.is_mut() { "mut" } else { "const" },
                mir_ty_to_string(to_ty, self.tcx),
            );
        }
        Some(raw)
    }

    fn array_field_offset_slice_ref(&self, pe: &PtrExpr<'_, 'tcx>, m: bool) -> Option<Expr> {
        let offset = array_field_direct_offset(pe, false)?;
        Some(self.array_field_offset_slice_ref_from_offset(pe, offset, m))
    }

    fn array_field_offset_slice_ref_from_offset(
        &self,
        pe: &PtrExpr<'_, 'tcx>,
        offset: &Expr,
        m: bool,
    ) -> Expr {
        let base = if matches!(self.behind_subscripts(pe.hir_base), PathOrDeref::Other)
            && place_expr_contains_deref(pe.base)
        {
            utils::expr!(
                "&{}({})",
                if m { "mut " } else { "" },
                pprust::expr_to_string(pe.base),
            )
        } else {
            pe.base.clone()
        };
        utils::expr!(
            "&{}({})[({}) as usize..]",
            if m { "mut " } else { "" },
            pprust::expr_to_string(&base),
            pprust::expr_to_string(offset),
        )
    }

    fn safe_slice_view_cast_allowed(
        &self,
        from_ty: ty::Ty<'tcx>,
        to_ty: ty::Ty<'tcx>,
        mutable: bool,
        def_id: LocalDefId,
        allow_resized_numeric_casts: bool,
    ) -> bool {
        from_ty == to_ty
            || (from_ty.is_numeric()
                && to_ty.is_numeric()
                && (allow_resized_numeric_casts || self.same_size(from_ty, to_ty, def_id)))
            || (!(from_ty.is_numeric() && to_ty.is_numeric())
                && self.bytemuck_slice_cast_allowed(from_ty, to_ty, mutable))
    }

    fn bytemuck_slice_cast_allowed(
        &self,
        from_ty: ty::Ty<'tcx>,
        to_ty: ty::Ty<'tcx>,
        mutable: bool,
    ) -> bool {
        let (from_requirement, to_requirement) = if mutable {
            (BytemuckRequirement::Pod, BytemuckRequirement::Pod)
        } else {
            (
                BytemuckRequirement::NoUninit,
                BytemuckRequirement::AnyBitPattern,
            )
        };

        let mut classifier = self.bytemuck_classifier.borrow_mut();
        classifier.satisfies_requirement(from_ty, from_requirement)
            && classifier.satisfies_requirement(to_ty, to_requirement)
    }

    fn try_require_bytemuck_slice_cast(
        &self,
        from_ty: ty::Ty<'tcx>,
        to_ty: ty::Ty<'tcx>,
        mutable: bool,
    ) -> bool {
        if !self.bytemuck_slice_cast_allowed(from_ty, to_ty, mutable) {
            return false;
        }

        let (from_requirement, to_requirement) = if mutable {
            (BytemuckRequirement::Pod, BytemuckRequirement::Pod)
        } else {
            (
                BytemuckRequirement::NoUninit,
                BytemuckRequirement::AnyBitPattern,
            )
        };

        let mut derives = self.bytemuck_derives.borrow_mut();
        let mut classifier = self.bytemuck_classifier.borrow_mut();
        let from_required =
            derives.require_type(self.tcx, &mut classifier, from_ty, from_requirement);
        let to_required = derives.require_type(self.tcx, &mut classifier, to_ty, to_requirement);
        debug_assert!(from_required && to_required);
        self.bytemuck.set(true);
        true
    }

    fn plain_slice_from_safe_view(
        &self,
        e: &Expr,
        pe: &PtrExpr<'_, 'tcx>,
        m: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
        is_slice_ref: bool,
    ) -> Expr {
        if is_slice_ref {
            self.plain_slice_from_expr(e, m, lhs_inner_ty, rhs_inner_ty)
        } else {
            self.plain_slice_from_slice(e, pe, m, lhs_inner_ty, rhs_inner_ty)
        }
    }

    fn cursor_from_safe_slice_view(
        &self,
        e: &Expr,
        pe: &PtrExpr<'_, 'tcx>,
        m: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
        is_slice_ref: bool,
    ) -> Expr {
        let slice =
            self.plain_slice_from_safe_view(e, pe, m, lhs_inner_ty, rhs_inner_ty, is_slice_ref);
        let cursor_ty = if m {
            "crate::slice_cursor::SliceCursorMut"
        } else {
            "crate::slice_cursor::SliceCursor"
        };
        utils::expr!("{}::new({})", cursor_ty, pprust::expr_to_string(&slice))
    }

    fn try_byte_slice_from_addr_of(
        &self,
        pointee: &Expr,
        pointee_ty: ty::Ty<'tcx>,
        target_inner_ty: ty::Ty<'tcx>,
        mutable: bool,
        source_mut: bool,
    ) -> Option<Expr> {
        if !ty_is_byte_sized_raw_inner(target_inner_ty) || (mutable && !source_mut) {
            return None;
        }
        if place_expr_contains_deref(pointee) {
            return None;
        }
        let pointee_str = pprust::expr_to_string(pointee);
        let target_ty = mir_ty_to_string(target_inner_ty, self.tcx);
        match pointee_ty.kind() {
            ty::TyKind::Array(elem_ty, _) if ty_is_byte_sized_raw_inner(*elem_ty) => {
                if *elem_ty == target_inner_ty {
                    Some(utils::expr!(
                        "&{}({})",
                        if mutable { "mut " } else { "" },
                        pointee_str,
                    ))
                } else {
                    self.bytemuck.set(true);
                    Some(utils::expr!(
                        "bytemuck::cast_slice{}::<_, {}>(&{}({}))",
                        if mutable { "_mut" } else { "" },
                        target_ty,
                        if mutable { "mut " } else { "" },
                        pointee_str,
                    ))
                }
            }
            ty::TyKind::Int(_) | ty::TyKind::Uint(_) | ty::TyKind::Float(_) => {
                self.bytemuck.set(true);
                let bytes = utils::expr!(
                    "bytemuck::bytes_of{}(&{}({}))",
                    if mutable { "_mut" } else { "" },
                    if mutable { "mut " } else { "" },
                    pointee_str,
                );
                if target_inner_ty == self.tcx.types.u8 {
                    Some(bytes)
                } else {
                    Some(utils::expr!(
                        "bytemuck::cast_slice{}::<_, {}>({})",
                        if mutable { "_mut" } else { "" },
                        target_ty,
                        pprust::expr_to_string(&bytes),
                    ))
                }
            }
            ty::TyKind::Adt(adt, _) if adt.is_struct() => {
                let requirement = if mutable {
                    BytemuckRequirement::Pod
                } else {
                    BytemuckRequirement::NoUninit
                };
                let mut derives = self.bytemuck_derives.borrow_mut();
                let mut classifier = self.bytemuck_classifier.borrow_mut();
                if !derives.require_type(self.tcx, &mut classifier, pointee_ty, requirement) {
                    return None;
                }
                self.bytemuck.set(true);
                let bytes = utils::expr!(
                    "bytemuck::bytes_of{}(&{}({}))",
                    if mutable { "_mut" } else { "" },
                    if mutable { "mut " } else { "" },
                    pointee_str,
                );
                if target_inner_ty == self.tcx.types.u8 {
                    Some(bytes)
                } else {
                    Some(utils::expr!(
                        "bytemuck::cast_slice{}::<_, {}>({})",
                        if mutable { "_mut" } else { "" },
                        target_ty,
                        pprust::expr_to_string(&bytes),
                    ))
                }
            }
            _ => None,
        }
    }

    fn try_bytemuck_slice_from_addr_of(
        &self,
        pointee: &Expr,
        pointee_ty: ty::Ty<'tcx>,
        target_inner_ty: ty::Ty<'tcx>,
        mutable: bool,
        source_mut: bool,
    ) -> Option<Expr> {
        if mutable && !source_mut {
            return None;
        }
        if place_expr_contains_deref(pointee) {
            return None;
        }
        let ty::TyKind::Array(source_inner_ty, _) = pointee_ty.kind() else {
            return None;
        };
        if *source_inner_ty == target_inner_ty
            || !self.try_require_bytemuck_slice_cast(*source_inner_ty, target_inner_ty, mutable)
        {
            return None;
        }

        Some(utils::expr!(
            "bytemuck::cast_slice{}::<_, {}>(&{}({}))",
            if mutable { "_mut" } else { "" },
            mir_ty_to_string(target_inner_ty, self.tcx),
            if mutable { "mut " } else { "" },
            pprust::expr_to_string(pointee),
        ))
    }

    fn projected_opt_boxed_slice_expr(
        &self,
        pe: &PtrExpr<'_, 'tcx>,
        m: bool,
    ) -> Option<(Expr, ty::Ty<'tcx>)> {
        let mut expr = self.opt_boxed_slice_view_expr(pe.base, m);
        self.apply_boxed_slice_projections(pe, m, &mut expr)
    }

    fn projected_boxed_slice_expr(
        &self,
        pe: &PtrExpr<'_, 'tcx>,
        m: bool,
    ) -> Option<(Expr, ty::Ty<'tcx>)> {
        let mut expr = self.boxed_slice_view_expr(pe.base, m);
        self.apply_boxed_slice_projections(pe, m, &mut expr)
    }

    fn projected_opt_ref_slice_expr(
        &self,
        pe: &PtrExpr<'_, 'tcx>,
        m: bool,
        source_mut: bool,
    ) -> Option<(Expr, ty::Ty<'tcx>)> {
        if m && !source_mut {
            return None;
        }
        let source_inner_ty = unwrap_ptr_or_arr_from_mir_ty(pe.base_ty, self.tcx)?;
        let raw = self.raw_from_opt_ref(pe.base, m, source_mut, source_inner_ty, source_inner_ty);
        let mut expr = utils::expr!(
            "std::slice::from_raw_parts{}({}, 1_000_000)",
            if m { "_mut" } else { "" },
            pprust::expr_to_string(&raw),
        );
        self.apply_borrowed_slice_projections(pe, m, &mut expr)
    }

    fn apply_boxed_slice_projections(
        &self,
        pe: &PtrExpr<'_, 'tcx>,
        m: bool,
        expr: &mut Expr,
    ) -> Option<(Expr, ty::Ty<'tcx>)> {
        let mut from_ty = unwrap_ptr_or_arr_from_mir_ty(pe.base_ty, self.tcx)?;
        for proj in &pe.projs {
            match proj {
                PtrExprProj::Offset(offset) => {
                    *expr = utils::expr!(
                        "({})[({}) as usize..]",
                        pprust::expr_to_string(expr),
                        pprust::expr_to_string(offset),
                    );
                }
                PtrExprProj::Cast(ty) if ty.is_usize() => return None,
                PtrExprProj::Cast(ty) => {
                    let (to_ty, _) = unwrap_ptr_from_mir_ty(*ty)?;
                    *expr = self.plain_slice_from_expr(expr, m, to_ty, from_ty);
                    from_ty = to_ty;
                }
                PtrExprProj::IntegerOp(..) | PtrExprProj::IntegerBinOp(..) => return None,
            }
        }
        Some((expr.clone(), from_ty))
    }

    fn apply_borrowed_slice_projections(
        &self,
        pe: &PtrExpr<'_, 'tcx>,
        m: bool,
        expr: &mut Expr,
    ) -> Option<(Expr, ty::Ty<'tcx>)> {
        let mut from_ty = unwrap_ptr_or_arr_from_mir_ty(pe.base_ty, self.tcx)?;
        for proj in &pe.projs {
            match proj {
                PtrExprProj::Offset(offset) => {
                    *expr = utils::expr!(
                        "({})[({}) as usize..]",
                        pprust::expr_to_string(expr),
                        pprust::expr_to_string(offset),
                    );
                }
                PtrExprProj::Cast(ty) if ty.is_usize() => return None,
                PtrExprProj::Cast(ty) => {
                    let (to_ty, _) = unwrap_ptr_from_mir_ty(*ty)?;
                    *expr = self.plain_slice_from_expr(expr, m, to_ty, from_ty);
                    from_ty = to_ty;
                }
                PtrExprProj::IntegerOp(..) | PtrExprProj::IntegerBinOp(..) => return None,
            }
        }
        Some((expr.clone(), from_ty))
    }

    fn raw_from_opt_box(
        &self,
        e: &Expr,
        m: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        let deref = if m { "as_deref_mut" } else { "as_deref" };
        let null = if m { "null_mut" } else { "null" };
        let lhs_ty = mir_ty_to_string(lhs_inner_ty, self.tcx);
        if !need_cast {
            utils::expr!(
                "({}).{}().map_or(std::ptr::{}::<{}>(), |_x| _x)",
                pprust::expr_to_string(e),
                deref,
                null,
                lhs_ty,
            )
        } else {
            let rhs_ty = mir_ty_to_string(rhs_inner_ty, self.tcx);
            utils::expr!(
                "({}).{}().map_or(std::ptr::{}::<{}>(), |_x| _x as *{} {} as *{} {})",
                pprust::expr_to_string(e),
                deref,
                null,
                lhs_ty,
                if m { "mut" } else { "const" },
                rhs_ty,
                if m { "mut" } else { "const" },
                lhs_ty,
            )
        }
    }

    fn raw_from_opt_box_return(
        &self,
        e: &Expr,
        m: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let lhs_ty = mir_ty_to_string(lhs_inner_ty, self.tcx);
        let rhs_ty = mir_ty_to_string(rhs_inner_ty, self.tcx);
        let null = if m { "null_mut" } else { "null" };
        if lhs_inner_ty == rhs_inner_ty {
            if m {
                utils::expr!(
                    "({}).map_or(std::ptr::null_mut::<{}>(), |_x| Box::into_raw(_x) as *mut {})",
                    pprust::expr_to_string(e),
                    lhs_ty,
                    lhs_ty,
                )
            } else {
                utils::expr!(
                    "({}).map_or(std::ptr::null::<{}>(), |_x| Box::into_raw(_x) as *const {})",
                    pprust::expr_to_string(e),
                    lhs_ty,
                    lhs_ty,
                )
            }
        } else {
            utils::expr!(
                "({}).map_or(std::ptr::{}::<{}>(), |_x| Box::into_raw(_x) as *{} {} as *{} {})",
                pprust::expr_to_string(e),
                null,
                lhs_ty,
                if m { "mut" } else { "const" },
                rhs_ty,
                if m { "mut" } else { "const" },
                lhs_ty,
            )
        }
    }

    fn raw_from_opt_boxed_slice_return(
        &self,
        e: &Expr,
        m: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let lhs_ty = mir_ty_to_string(lhs_inner_ty, self.tcx);
        let rhs_ty = mir_ty_to_string(rhs_inner_ty, self.tcx);
        let ptr_method = if m { "as_mut_ptr" } else { "as_ptr" };
        let ptr_mut = if m { "mut" } else { "const" };
        let null = if m { "null_mut" } else { "null" };
        if lhs_inner_ty == rhs_inner_ty {
            utils::expr!(
                "({}).map_or(std::ptr::{}::<{}>(), |_x| Box::leak(_x).{}())",
                pprust::expr_to_string(e),
                null,
                lhs_ty,
                ptr_method,
            )
        } else {
            utils::expr!(
                "({}).map_or(std::ptr::{}::<{}>(), |_x| Box::leak(_x).{}() as *{} {} as *{} {})",
                pprust::expr_to_string(e),
                null,
                lhs_ty,
                ptr_method,
                ptr_mut,
                rhs_ty,
                ptr_mut,
                lhs_ty,
            )
        }
    }

    fn raw_from_ref(
        &self,
        e: &Expr,
        m: bool,
        m1: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let lhs_ty = mir_ty_to_string(lhs_inner_ty, self.tcx);
        let rhs_ty = mir_ty_to_string(rhs_inner_ty, self.tcx);
        let source_mut = if m1 { "mut" } else { "const" };
        let target_mut = if m { "mut" } else { "const" };
        if lhs_inner_ty == rhs_inner_ty && m == m1 {
            utils::expr!(
                "({}) as *{} {}",
                pprust::expr_to_string(e),
                target_mut,
                lhs_ty,
            )
        } else {
            utils::expr!(
                "({}) as *{} {} as *{} {}",
                pprust::expr_to_string(e),
                source_mut,
                rhs_ty,
                target_mut,
                lhs_ty,
            )
        }
    }

    fn raw_from_box(
        &self,
        e: &Expr,
        m: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let view = if m {
            utils::expr!("({}).as_mut()", pprust::expr_to_string(e))
        } else {
            utils::expr!("({}).as_ref()", pprust::expr_to_string(e))
        };
        self.raw_from_ref(&view, m, m, lhs_inner_ty, rhs_inner_ty)
    }

    fn raw_from_box_return(
        &self,
        e: &Expr,
        m: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let lhs_ty = mir_ty_to_string(lhs_inner_ty, self.tcx);
        let rhs_ty = mir_ty_to_string(rhs_inner_ty, self.tcx);
        if lhs_inner_ty == rhs_inner_ty {
            utils::expr!(
                "Box::into_raw({}) as *{} {}",
                pprust::expr_to_string(e),
                if m { "mut" } else { "const" },
                lhs_ty,
            )
        } else {
            utils::expr!(
                "Box::into_raw({}) as *{} {} as *{} {}",
                pprust::expr_to_string(e),
                if m { "mut" } else { "const" },
                rhs_ty,
                if m { "mut" } else { "const" },
                lhs_ty,
            )
        }
    }

    fn raw_from_boxed_slice_return(
        &self,
        e: &Expr,
        m: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let lhs_ty = mir_ty_to_string(lhs_inner_ty, self.tcx);
        let rhs_ty = mir_ty_to_string(rhs_inner_ty, self.tcx);
        let ptr_method = if m { "as_mut_ptr" } else { "as_ptr" };
        let ptr_mut = if m { "mut" } else { "const" };
        if lhs_inner_ty == rhs_inner_ty {
            utils::expr!("Box::leak({}).{}()", pprust::expr_to_string(e), ptr_method,)
        } else {
            utils::expr!(
                "Box::leak({}).{}() as *{} {} as *{} {}",
                pprust::expr_to_string(e),
                ptr_method,
                ptr_mut,
                rhs_ty,
                ptr_mut,
                lhs_ty,
            )
        }
    }

    fn ref_from_ref(
        &self,
        e: &Expr,
        m: bool,
        m1: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
        def_id: LocalDefId,
    ) -> Expr {
        if lhs_inner_ty == rhs_inner_ty {
            if m == m1 {
                return e.clone();
            }
            if !m && m1 {
                return utils::expr!("&*({})", pprust::expr_to_string(e));
            }
        }
        let opt = self.opt_ref_from_ref(e, m, m1, lhs_inner_ty, rhs_inner_ty, def_id);
        utils::expr!("({}).unwrap()", pprust::expr_to_string(&opt))
    }

    fn opt_ref_from_ref(
        &self,
        e: &Expr,
        m: bool,
        m1: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
        def_id: LocalDefId,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        let e_str = pprust::expr_to_string(e);
        if !need_cast {
            utils::expr!("Some(&{}*({}))", if m && m1 { "mut " } else { "" }, e_str,)
        } else if lhs_inner_ty.is_numeric()
            && rhs_inner_ty.is_numeric()
            && self.same_size(lhs_inner_ty, rhs_inner_ty, def_id)
        {
            self.bytemuck.set(true);
            utils::expr!(
                "Some(bytemuck::cast_{}::<_, {}>(&{}*({})))",
                if m && m1 { "mut" } else { "ref" },
                mir_ty_to_string(lhs_inner_ty, self.tcx),
                if m && m1 { "mut " } else { "" },
                e_str,
            )
        } else {
            let raw = self.raw_from_ref(e, m, m1, lhs_inner_ty, rhs_inner_ty);
            self.opt_ref_from_raw(&raw, m, m, lhs_inner_ty, lhs_inner_ty)
        }
    }

    fn opt_ref_from_box(
        &self,
        e: &Expr,
        m: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
        def_id: LocalDefId,
    ) -> Expr {
        let view = if m {
            utils::expr!("({}).as_mut()", pprust::expr_to_string(e))
        } else {
            utils::expr!("({}).as_ref()", pprust::expr_to_string(e))
        };
        self.opt_ref_from_ref(&view, m, m, lhs_inner_ty, rhs_inner_ty, def_id)
    }

    fn box_from_box(
        &self,
        e: &Expr,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        assert_eq!(
            lhs_inner_ty, rhs_inner_ty,
            "M4A does not support casted Box<_> reinterpretation"
        );
        e.clone()
    }

    fn boxed_slice_from_boxed_slice(
        &self,
        e: &Expr,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        assert_eq!(
            lhs_inner_ty, rhs_inner_ty,
            "M4A does not support casted Box<[_]> reinterpretation"
        );
        e.clone()
    }

    fn opt_ref_from_opt_box(
        &self,
        e: &Expr,
        m: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
        def_id: LocalDefId,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        if !need_cast {
            self.opt_box_view_expr(e, m)
        } else if lhs_inner_ty.is_numeric()
            && rhs_inner_ty.is_numeric()
            && self.same_size(lhs_inner_ty, rhs_inner_ty, def_id)
        {
            self.bytemuck.set(true);
            utils::expr!(
                "({}).as_deref{}().map(|_x| bytemuck::cast_{}::<_, {}>(_x))",
                pprust::expr_to_string(e),
                if m { "_mut" } else { "" },
                if m { "mut" } else { "ref" },
                mir_ty_to_string(lhs_inner_ty, self.tcx),
            )
        } else {
            panic!("unsupported M4A casted OptBox -> OptRef reinterpretation")
        }
    }

    fn opt_box_from_opt_box(
        &self,
        e: &Expr,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        assert_eq!(
            lhs_inner_ty, rhs_inner_ty,
            "M4A does not support casted Option<Box<_>> reinterpretation"
        );
        e.clone()
    }

    fn opt_box_from_raw(
        &self,
        e: &Expr,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        assert_eq!(
            lhs_inner_ty, rhs_inner_ty,
            "M4B raw-to-box fallback requires matching pointee types"
        );
        let lhs_ty = mir_ty_to_string(lhs_inner_ty, self.tcx);
        if !utils::ast::has_side_effects(e) {
            utils::expr!(
                "if ({0}).is_null() {{
                    None
                }} else {{
                    Some(Box::from_raw(({0}) as *mut {1}))
                }}",
                pprust::expr_to_string(e),
                lhs_ty,
            )
        } else {
            utils::expr!(
                "{{
                    let _x = {};
                    if _x.is_null() {{
                        None
                    }} else {{
                        Some(Box::from_raw(_x as *mut {}))
                    }}
                }}",
                pprust::expr_to_string(e),
                lhs_ty,
            )
        }
    }

    fn opt_boxed_slice_from_opt_boxed_slice(
        &self,
        e: &Expr,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        assert_eq!(
            lhs_inner_ty, rhs_inner_ty,
            "M4A does not support casted Option<Box<[_]>> reinterpretation"
        );
        e.clone()
    }

    fn raw_from_opt_ref(
        &self,
        e: &Expr,
        m: bool,
        m1: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        let cast_mut = if m && !m1 { ".cast_mut()" } else { "" };
        let extern_ty = matches!(rhs_inner_ty.kind(), ty::TyKind::Foreign(_));
        if extern_ty {
            utils::expr!(
                "match &{}({}) {{
                    Some(x) => *x as *{} {},
                    None => std::ptr::null{}(),
                }}",
                if m && m1 { "mut " } else { "" },
                pprust::expr_to_string(e),
                if m && m1 { "mut" } else { "const" },
                mir_ty_to_string(lhs_inner_ty, self.tcx),
                if m && m1 { "_mut" } else { "" },
            )
        } else if !need_cast {
            utils::expr!(
                "({}).as_deref{1}().map_or(std::ptr::null{1}::<{2}>(), |_x| _x){3}",
                pprust::expr_to_string(e),
                if m && m1 { "_mut" } else { "" },
                mir_ty_to_string(lhs_inner_ty, self.tcx),
                cast_mut,
            )
        } else {
            utils::expr!(
                "({}).as_deref{1}().map_or(std::ptr::null{1}::<{2}>(), |_x| _x as *{3} _ as *{3} _){4}",
                pprust::expr_to_string(e),
                if m && m1 { "_mut" } else { "" },
                mir_ty_to_string(lhs_inner_ty, self.tcx),
                if m && m1 { "mut" } else { "const" },
                cast_mut,
            )
        }
    }

    fn raw_from_projected_opt_ref(
        &self,
        pe: &PtrExpr<'_, 'tcx>,
        m: bool,
        m1: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let source_inner_ty =
            unwrap_ptr_or_arr_from_mir_ty(pe.base_ty, self.tcx).unwrap_or(rhs_inner_ty);
        let mut raw = self.raw_from_opt_ref(pe.base, m, m1, source_inner_ty, source_inner_ty);
        let mut from_ty = source_inner_ty;
        for proj in &pe.projs {
            match proj {
                PtrExprProj::Offset(offset) => {
                    raw = utils::expr!(
                        "({}).offset({})",
                        pprust::expr_to_string(&raw),
                        pprust::expr_to_string(offset),
                    );
                }
                PtrExprProj::Cast(ty) if ty.is_usize() => {
                    raw = utils::expr!("({}) as usize", pprust::expr_to_string(&raw));
                }
                PtrExprProj::Cast(ty) => {
                    let (to_ty, _) = unwrap_ptr_from_mir_ty(*ty).unwrap();
                    raw = utils::expr!(
                        "({}) as *{} {}",
                        pprust::expr_to_string(&raw),
                        if m { "mut" } else { "const" },
                        mir_ty_to_string(to_ty, self.tcx),
                    );
                    from_ty = to_ty;
                }
                PtrExprProj::IntegerOp(expr, op) => {
                    let method = match op {
                        OpKind::WrappingAdd => "wrapping_add",
                        OpKind::WrappingSub => "wrapping_sub",
                    };
                    raw = utils::expr!(
                        "({}).{}({})",
                        pprust::expr_to_string(&raw),
                        method,
                        pprust::expr_to_string(expr),
                    );
                }
                PtrExprProj::IntegerBinOp(expr, op) => {
                    let op_str = match op {
                        BinOpKind::BitAnd => "&",
                        BinOpKind::BitOr => "|",
                        _ => panic!(),
                    };
                    raw = utils::expr!(
                        "({}) {} ({})",
                        pprust::expr_to_string(&raw),
                        op_str,
                        pprust::expr_to_string(expr),
                    );
                }
            }
        }
        if from_ty != lhs_inner_ty {
            utils::expr!(
                "({}) as *{} {}",
                pprust::expr_to_string(&raw),
                if m { "mut" } else { "const" },
                mir_ty_to_string(lhs_inner_ty, self.tcx),
            )
        } else {
            raw
        }
    }

    fn opt_ref_from_projected_opt_ref(
        &self,
        pe: &PtrExpr<'_, 'tcx>,
        m: bool,
        m1: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let raw = self.raw_from_projected_opt_ref(pe, m, m1, lhs_inner_ty, rhs_inner_ty);
        self.opt_ref_from_raw(&raw, m, m, lhs_inner_ty, lhs_inner_ty)
    }

    fn raw_from_slice_or_cursor(
        &self,
        e: &Expr,
        m: bool,
        m1: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        let cast_mut = if m && !m1 { ".cast_mut()" } else { "" };
        if !need_cast {
            utils::expr!(
                "({}).as_{}ptr(){}",
                pprust::expr_to_string(e),
                if m && m1 { "mut_" } else { "" },
                cast_mut
            )
        } else {
            utils::expr!(
                "({}).as_{}ptr(){} as *{} _",
                pprust::expr_to_string(e),
                if m && m1 { "mut_" } else { "" },
                cast_mut,
                if m { "mut" } else { "const" },
            )
        }
    }

    fn opt_ref_from_raw(
        &self,
        e: &Expr,
        m: bool,
        m1: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        let cast_mut = if m && !m1 { ".cast_mut()" } else { "" };
        if !need_cast {
            utils::expr!(
                "({}){}.as_{}()",
                pprust::expr_to_string(e),
                cast_mut,
                if m { "mut" } else { "ref" },
            )
        } else {
            utils::expr!(
                "(({}){} as *{} {}).as_{}()",
                pprust::expr_to_string(e),
                cast_mut,
                if m { "mut" } else { "const" },
                mir_ty_to_string(lhs_inner_ty, self.tcx),
                if m { "mut" } else { "ref" },
            )
        }
    }

    fn opt_ref_from_raw_without_unsafe(
        &self,
        e: &Expr,
        m: bool,
        m1: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        let cast_mut = if m && !m1 { ".cast_mut()" } else { "" };
        if !need_cast {
            utils::expr!(
                "({}){}.as_{}()",
                pprust::expr_to_string(e),
                cast_mut,
                if m { "mut" } else { "ref" },
            )
        } else {
            utils::expr!(
                "(({}){} as *{} {}).as_{}()",
                pprust::expr_to_string(e),
                cast_mut,
                if m { "mut" } else { "const" },
                mir_ty_to_string(lhs_inner_ty, self.tcx),
                if m { "mut" } else { "ref" },
            )
        }
    }

    fn opt_ref_from_opt_ref(
        &self,
        e: &Expr,
        m: bool,
        m1: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
        def_id: LocalDefId,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        if !need_cast {
            utils::expr!(
                "({}).as_deref{}()",
                pprust::expr_to_string(e),
                if m && m1 { "_mut" } else { "" },
            )
        } else if lhs_inner_ty.is_numeric()
            && rhs_inner_ty.is_numeric()
            && self.same_size(lhs_inner_ty, rhs_inner_ty, def_id)
        {
            // can be used for deref, so type must be specified
            self.bytemuck.set(true);
            utils::expr!(
                "({}).as_deref{}().map(|_x| bytemuck::cast_{}::<_, {}>(_x))",
                pprust::expr_to_string(e),
                if m && m1 { "_mut" } else { "" },
                if m && m1 { "mut" } else { "ref" },
                mir_ty_to_string(lhs_inner_ty, self.tcx),
            )
        } else {
            // can be used for deref, so type must be specified
            utils::expr!(
                "({}).as_deref{}().map(|_x| &{}*(_x as *{3} _ as *{3} {4}))",
                pprust::expr_to_string(e),
                if m && m1 { "_mut" } else { "" },
                if m && m1 { "mut " } else { "" },
                if m && m1 { "mut" } else { "const" },
                mir_ty_to_string(lhs_inner_ty, self.tcx),
            )
        }
    }

    fn opt_ref_from_slice_or_cursor(
        &self,
        e: &Expr,
        m: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
        def_id: LocalDefId,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        if !need_cast {
            utils::expr!(
                "({}).first{}()",
                pprust::expr_to_string(e),
                if m { "_mut" } else { "" },
            )
        } else if lhs_inner_ty.is_numeric()
            && rhs_inner_ty.is_numeric()
            && self.same_size(lhs_inner_ty, rhs_inner_ty, def_id)
        {
            self.bytemuck.set(true);
            utils::expr!(
                "({}).first{}().map(|_x| bytemuck::cast_{}(_x))",
                pprust::expr_to_string(e),
                if m { "_mut" } else { "" },
                if m { "mut" } else { "ref" },
            )
        } else {
            utils::expr!(
                "({}).first{}().map(|_x| &{}*(_x as *{3} _ as *{3} _))",
                pprust::expr_to_string(e),
                if m { "_mut" } else { "" },
                if m { "mut " } else { "" },
                if m { "mut" } else { "const" },
            )
        }
    }

    fn slice_from_raw(
        &self,
        e: &Expr,
        m: bool,
        m1: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        let cast_mut = if m && !m1 { " as *mut _" } else { "" };
        if let Some(name) = method_call_name(e)
            && let name = name.as_str()
            && (name == "offset" || name == "as_mut_ptr" || name == "as_ptr")
        {
            // we assume that the pointer is not null when such methods are called
            if let Some(slice) = self.plain_slice_from_as_ptr_receiver(e, m, lhs_inner_ty) {
                return slice;
            }
            if !need_cast {
                utils::expr!(
                    "std::slice::from_raw_parts{}(({}){}, 1_000_000)",
                    if m { "_mut" } else { "" },
                    pprust::expr_to_string(e),
                    cast_mut,
                )
            } else {
                utils::expr!(
                    "std::slice::from_raw_parts{}(({}){} as *{} _, 1_000_000)",
                    if m { "_mut" } else { "" },
                    pprust::expr_to_string(e),
                    cast_mut,
                    if m { "mut" } else { "const" },
                )
            }
        } else if !utils::ast::has_side_effects(e) {
            if !need_cast {
                utils::expr!(
                    "if ({0}).is_null() {{
                        &{1}[]
                    }} else {{
                        std::slice::from_raw_parts{2}(({0}){3}, 1_000_000)
                    }}",
                    pprust::expr_to_string(e),
                    if m { "mut " } else { "" },
                    if m { "_mut" } else { "" },
                    cast_mut,
                )
            } else {
                utils::expr!(
                    "if ({0}).is_null() {{
                        &{1}[]
                    }} else {{
                        std::slice::from_raw_parts{2}(({0}){3} as *{4} _, 1_000_000)
                    }}",
                    pprust::expr_to_string(e),
                    if m { "mut " } else { "" },
                    if m { "_mut" } else { "" },
                    cast_mut,
                    if m { "mut" } else { "const" },
                )
            }
        } else if !need_cast {
            utils::expr!(
                "{{
                    let _x = {};
                    if _x.is_null() {{
                        &{}[]
                    }} else {{
                        std::slice::from_raw_parts{}(_x{}, 1_000_000)
                    }}
                }}",
                pprust::expr_to_string(e),
                if m { "mut " } else { "" },
                if m { "_mut" } else { "" },
                cast_mut,
            )
        } else {
            utils::expr!(
                "{{
                    let _x = {};
                    if _x.is_null() {{
                        &{}[]
                    }} else {{
                        std::slice::from_raw_parts{}(_x{} as *{} _, 1_000_000)
                    }}
                }}",
                pprust::expr_to_string(e),
                if m { "mut " } else { "" },
                if m { "_mut" } else { "" },
                cast_mut,
                if m { "mut" } else { "const" },
            )
        }
    }

    fn plain_slice_from_as_ptr_receiver(
        &self,
        e: &Expr,
        target_mut: bool,
        target_inner_ty: ty::Ty<'tcx>,
    ) -> Option<Expr> {
        let ExprKind::MethodCall(call) = &unwrap_cast_and_paren(e).kind else {
            return None;
        };
        let name = call.seg.ident.name.as_str();
        if !matches!(name, "as_ptr" | "as_mut_ptr")
            || target_mut && name != "as_mut_ptr"
            || utils::ast::has_side_effects(&call.receiver)
        {
            return None;
        }

        let hir_e = self.ast_to_hir.get_expr(e.id, self.tcx)?;
        let hir::ExprKind::MethodCall(_, hir_receiver, _, _) = hir_unwrap_casts(hir_e).kind else {
            return None;
        };
        let typeck = self.tcx.typeck(hir_receiver.hir_id.owner);
        let source_inner_ty =
            slice_like_container_inner_ty(typeck.expr_ty(hir_receiver), self.tcx)?;
        if source_inner_ty != target_inner_ty {
            return None;
        }

        if target_mut {
            Some(utils::expr!(
                "&mut (&mut ({}))[..]",
                pprust::expr_to_string(&call.receiver),
            ))
        } else {
            Some(utils::expr!(
                "&(&({}))[..]",
                pprust::expr_to_string(&call.receiver),
            ))
        }
    }

    fn slice_from_ref(
        &self,
        e: &Expr,
        m: bool,
        m1: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
        def_id: LocalDefId,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        let e_str = pprust::expr_to_string(e);
        if !need_cast {
            utils::expr!(
                "std::slice::from_{}(&{}*({}))",
                if m && m1 { "mut" } else { "ref" },
                if m && m1 { "mut " } else { "" },
                e_str,
            )
        } else if lhs_inner_ty.is_numeric()
            && rhs_inner_ty.is_numeric()
            && self.same_size(lhs_inner_ty, rhs_inner_ty, def_id)
        {
            self.bytemuck.set(true);
            utils::expr!(
                "std::slice::from_{0}(bytemuck::cast_{0}(&{1}*({2})))",
                if m && m1 { "mut" } else { "ref" },
                if m && m1 { "mut " } else { "" },
                e_str,
            )
        } else {
            let raw = self.raw_from_ref(e, m, m1, lhs_inner_ty, rhs_inner_ty);
            self.slice_from_raw(&raw, m, m, lhs_inner_ty, lhs_inner_ty)
        }
    }

    fn cursor_from_raw(
        &self,
        e: &Expr,
        m: bool,
        m1: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        let cast_mut = if m && !m1 { " as *mut _" } else { "" };
        let cursor_ty = if m {
            "crate::slice_cursor::SliceCursorMut"
        } else {
            "crate::slice_cursor::SliceCursor"
        };

        if let Some(name) = method_call_name(e)
            && let name = name.as_str()
            && (name == "offset" || name == "as_mut_ptr" || name == "as_ptr")
        {
            // we assume that the pointer is not null when such methods are called
            if !need_cast {
                utils::expr!(
                    "{}::from_raw_parts{}(({}){}, 1_000_000)",
                    cursor_ty,
                    if m { "_mut" } else { "" },
                    pprust::expr_to_string(e),
                    cast_mut,
                )
            } else {
                utils::expr!(
                    "{}::from_raw_parts{}(({}){} as *{} _, 1_000_000)",
                    cursor_ty,
                    if m { "_mut" } else { "" },
                    pprust::expr_to_string(e),
                    cast_mut,
                    if m { "mut" } else { "const" },
                )
            }
        } else if !utils::ast::has_side_effects(e) {
            if !need_cast {
                utils::expr!(
                    "if ({0}).is_null() {{
                        {1}::empty()
                    }} else {{
                        {1}::from_raw_parts{2}(({0}){3}, 1_000_000)
                    }}",
                    pprust::expr_to_string(e),
                    cursor_ty,
                    if m { "_mut" } else { "" },
                    cast_mut,
                )
            } else {
                utils::expr!(
                    "if ({0}).is_null() {{
                        {1}::empty()
                    }} else {{
                        {1}::from_raw_parts{2}(({0}){3} as *{4} _, 1_000_000)
                    }}",
                    pprust::expr_to_string(e),
                    cursor_ty,
                    if m { "_mut" } else { "" },
                    cast_mut,
                    if m { "mut" } else { "const" },
                )
            }
        } else if !need_cast {
            utils::expr!(
                "{{
                    let _x = {};
                    if _x.is_null() {{
                        {}::empty()
                    }} else {{
                        {}::from_raw_parts{}(_x{}, 1_000_000)
                    }}
                }}",
                pprust::expr_to_string(e),
                cursor_ty,
                cursor_ty,
                if m { "_mut" } else { "" },
                cast_mut,
            )
        } else {
            utils::expr!(
                "{{
                    let _x = {};
                    if _x.is_null() {{
                        {}::empty()
                    }} else {{
                        {}::from_raw_parts{}(_x{} as *{} _, 1_000_000)
                    }}
                }}",
                pprust::expr_to_string(e),
                cursor_ty,
                cursor_ty,
                if m { "_mut" } else { "" },
                cast_mut,
                if m { "mut" } else { "const" },
            )
        }
    }

    fn cursor_from_ref(
        &self,
        e: &Expr,
        pe: &PtrExpr<'_, 'tcx>,
        m: bool,
        m1: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let slice = self.slice_from_ref(
            e,
            m,
            m1,
            lhs_inner_ty,
            rhs_inner_ty,
            pe.hir_base.hir_id.owner.def_id,
        );
        self.cursor_from_plain_slice(&slice, pe, m, lhs_inner_ty, lhs_inner_ty)
    }

    // slice -> slice
    fn plain_slice_from_slice(
        &self,
        e: &Expr,
        pe: &PtrExpr<'_, 'tcx>,
        m: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        let is_rewritten_slice_like_local =
            matches!(pe.base_kind, PtrExprBaseKind::Path(Res::Local(_)))
                && matches!(
                    self.ptr_source_kind(pe),
                    Some(
                        PtrKind::Slice(_)
                            | PtrKind::SliceCursor(_)
                            | PtrKind::BoxedSlice
                            | PtrKind::OptBoxedSlice,
                    )
                )
                && pe.projs.is_empty();
        let get_reference = |use_ref| {
            if use_ref {
                if m { "&mut " } else { "&" }
            } else {
                ""
            }
        };
        if !need_cast {
            let reference = get_reference(
                pe.base_kind != PtrExprBaseKind::Alloca && !is_rewritten_slice_like_local,
            );
            utils::expr!("{}({})", reference, pprust::expr_to_string(e),)
        } else if (lhs_inner_ty.is_numeric() && rhs_inner_ty.is_numeric())
            || (!matches!(e.kind, ExprKind::Index(..))
                && self.try_require_bytemuck_slice_cast(rhs_inner_ty, lhs_inner_ty, m))
        {
            self.bytemuck.set(true);
            let reference = get_reference(
                matches!(e.kind, ExprKind::Index(..))
                    || (pe.base_kind != PtrExprBaseKind::Alloca && !is_rewritten_slice_like_local),
            );
            // can be used for deref, so type must be specified
            utils::expr!(
                "bytemuck::cast_slice{}::<_, {}>({}({}))",
                if m { "_mut" } else { "" },
                mir_ty_to_string(lhs_inner_ty, self.tcx),
                reference,
                pprust::expr_to_string(e),
            )
        } else {
            // can be used for deref, so type must be specified
            utils::expr!(
                "std::slice::from_raw_parts{0}(({1}).as{0}_ptr() as *{2} {3}, 1_000_000)",
                if m { "_mut" } else { "" },
                pprust::expr_to_string(e),
                if m { "mut" } else { "const" },
                mir_ty_to_string(lhs_inner_ty, self.tcx),
            )
        }
    }

    fn cursor_from_slice_or_cursor(
        &self,
        e: &Expr,
        pe: &PtrExpr<'_, 'tcx>,
        m: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        if is_plain_slice_expr(e) {
            self.cursor_from_plain_slice(e, pe, m, lhs_inner_ty, rhs_inner_ty)
        } else {
            self.cursor_from_cursor(e, m, lhs_inner_ty, rhs_inner_ty)
        }
    }

    fn cursor_from_plain_slice(
        &self,
        e: &Expr,
        pe: &PtrExpr<'_, 'tcx>,
        m: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        if !m && let Some(receiver) = slice_cursor_mut_temp_as_slice_receiver(e) {
            let shared_cursor = utils::expr!("({}).as_deref()", pprust::expr_to_string(receiver));
            return self.cursor_from_cursor(&shared_cursor, m, lhs_inner_ty, rhs_inner_ty);
        }
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        let is_rewritten_slice_like_local =
            matches!(pe.base_kind, PtrExprBaseKind::Path(Res::Local(_)))
                && matches!(
                    self.ptr_source_kind(pe),
                    Some(
                        PtrKind::Slice(_)
                            | PtrKind::SliceCursor(_)
                            | PtrKind::BoxedSlice
                            | PtrKind::OptBoxedSlice,
                    )
                )
                && pe.projs.is_empty();
        let get_reference = |use_ref| {
            if use_ref {
                if m { "&mut " } else { "&" }
            } else {
                ""
            }
        };
        let cursor_ty = if m {
            "crate::slice_cursor::SliceCursorMut"
        } else {
            "crate::slice_cursor::SliceCursor"
        };

        if !need_cast {
            let reference = get_reference(
                pe.base_kind != PtrExprBaseKind::Alloca
                    && !is_rewritten_slice_like_local
                    && !is_slice_ref_expr(e),
            );
            if pe.projs.len() == 1
                && let PtrExprProj::Offset(offset) = pe.projs[0]
            {
                // if there are only offsets, we can use the original slice and let the cursor handle the offsets
                let source_kind = self.ptr_source_kind(pe);
                let cursor_base = if matches!(source_kind, Some(PtrKind::BoxedSlice)) {
                    self.boxed_slice_view_expr(pe.base, m)
                } else if matches!(source_kind, Some(PtrKind::OptBoxedSlice)) {
                    self.opt_boxed_slice_view_expr(pe.base, m)
                } else {
                    pe.base.clone()
                };
                let reference = get_reference(
                    pe.base_kind != PtrExprBaseKind::Alloca
                        && !is_rewritten_slice_like_local
                        && !matches!(
                            source_kind,
                            Some(PtrKind::BoxedSlice | PtrKind::OptBoxedSlice)
                        )
                        && !is_slice_ref_expr(&cursor_base),
                );
                utils::expr!(
                    "{}::with_pos({}{}, ({}) as usize)",
                    cursor_ty,
                    reference,
                    pprust::expr_to_string(&cursor_base),
                    pprust::expr_to_string(offset),
                )
            } else {
                utils::expr!(
                    "{}::new({}{})",
                    cursor_ty,
                    reference,
                    pprust::expr_to_string(e),
                )
            }
        } else if lhs_inner_ty.is_numeric() && rhs_inner_ty.is_numeric() {
            let reference = get_reference(
                pe.base_kind != PtrExprBaseKind::Alloca && !is_rewritten_slice_like_local,
            );
            self.bytemuck.set(true);
            utils::expr!(
                "{}::new(bytemuck::cast_slice{}::<_, {}>({}({})))",
                cursor_ty,
                if m { "_mut" } else { "" },
                mir_ty_to_string(lhs_inner_ty, self.tcx),
                reference,
                pprust::expr_to_string(e),
            )
        } else {
            utils::expr!(
                "{}::from_raw_parts{}(({}).as_{}ptr() as *{} {}, 1_000_000)",
                cursor_ty,
                if m { "_mut" } else { "" },
                pprust::expr_to_string(e),
                if m { "mut_" } else { "" },
                if m { "mut" } else { "const" },
                mir_ty_to_string(lhs_inner_ty, self.tcx),
            )
        }
    }

    fn cursor_from_cursor(
        &self,
        e: &Expr,
        m: bool,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs_inner_ty: ty::Ty<'tcx>,
    ) -> Expr {
        let need_cast = lhs_inner_ty != rhs_inner_ty;
        let cursor_ty = if m {
            "crate::slice_cursor::SliceCursorMut"
        } else {
            "crate::slice_cursor::SliceCursor"
        };
        if !need_cast {
            e.clone()
        } else if !m
            && lhs_inner_ty.is_numeric()
            && rhs_inner_ty.is_numeric()
            && !utils::ast::has_side_effects(e)
        {
            self.bytemuck.set(true);
            utils::expr!(
                "{}::new(bytemuck::cast_slice::<_, {}>(({}).as_slice()))",
                cursor_ty,
                mir_ty_to_string(lhs_inner_ty, self.tcx),
                pprust::expr_to_string(e),
            )
        } else {
            utils::expr!(
                "{}::from_raw_parts{}(({}).as_ptr() as *{} {}, 1_000_000)",
                cursor_ty,
                if m { "_mut" } else { "" },
                pprust::expr_to_string(e),
                if m { "mut" } else { "const" },
                mir_ty_to_string(lhs_inner_ty, self.tcx),
            )
        }
    }

    fn same_size(&self, ty1: ty::Ty<'tcx>, ty2: ty::Ty<'tcx>, def_id: LocalDefId) -> bool {
        utils::ir::ty_size(ty1, def_id, self.tcx) == utils::ir::ty_size(ty2, def_id, self.tcx)
    }

    fn get_mutability_decision(&self, hexpr: &hir::Expr<'tcx>) -> Option<bool> {
        // find the root of this hir expr and if it's a path, get its decision from ptr_kinds and return its mutability
        let mut curr_expr = hexpr;
        loop {
            match &curr_expr.kind {
                hir::ExprKind::MethodCall(seg, receiver, ..)
                    if seg.ident.name.as_str() == "offset" =>
                {
                    curr_expr = receiver;
                }
                _ => break,
            }
        }
        if let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = &curr_expr.kind
            && let Res::Local(hir_id) = path.res
        {
            match self.effective_ptr_kind(hir_id) {
                Some(PtrKind::Ref(m)) => Some(m),
                Some(PtrKind::OptRef(m)) => Some(m),
                Some(
                    PtrKind::Box | PtrKind::OptBox | PtrKind::BoxedSlice | PtrKind::OptBoxedSlice,
                ) => Some(true),
                Some(PtrKind::Slice(m)) | Some(PtrKind::SliceCursor(m)) => Some(m),
                Some(PtrKind::Raw(m)) => Some(m),
                None => None,
            }
        } else {
            None
        }
    }

    fn ptr_expr<'a>(
        &self,
        expr: &'a Expr,
        hir_expr: &'a hir::Expr<'tcx>,
    ) -> Option<PtrExpr<'a, 'tcx>> {
        let expr = unwrap_addr_of_deref(expr);
        let hir_expr = hir_unwrap_addr_of_deref(hir_expr);
        let typeck = self.tcx.typeck(hir_expr.hir_id.owner);
        let base_ty = typeck.expr_ty(hir_expr);
        match &expr.kind {
            ExprKind::Path(_, _) => {
                let hir::ExprKind::Path(hir::QPath::Resolved(_, hpath)) = hir_expr.kind else {
                    panic!()
                };
                Some(PtrExpr::new(
                    expr,
                    hir_expr,
                    base_ty,
                    PtrExprBaseKind::Path(hpath.res),
                ))
            }
            ExprKind::Cast(e, _) => {
                let e = unwrap_cast_and_paren(e);
                let he = hir_unwrap_cast(hir_expr);
                let mut ptr_expr = self.ptr_expr(e, he)?;
                ptr_expr.push_cast(base_ty);
                if base_ty.is_usize() {
                    ptr_expr.cast_int = true;
                }
                Some(ptr_expr)
            }
            ExprKind::Field(_, _) => Some(PtrExpr::new(
                expr,
                hir_expr,
                base_ty,
                PtrExprBaseKind::Other,
            )),
            ExprKind::Index(_, _, _) => Some(PtrExpr::new(
                expr,
                hir_expr,
                base_ty,
                PtrExprBaseKind::Other,
            )),
            ExprKind::Unary(UnOp::Deref, _) => Some(PtrExpr::new(
                expr,
                hir_expr,
                base_ty,
                PtrExprBaseKind::Other,
            )),
            ExprKind::Call(_, _) => Some(PtrExpr::new(
                expr,
                hir_expr,
                base_ty,
                PtrExprBaseKind::Other,
            )),
            ExprKind::Lit(lit) => match lit.kind {
                token::LitKind::Integer if lit.symbol.as_str() == "0" => {
                    Some(PtrExpr::new(expr, hir_expr, base_ty, PtrExprBaseKind::Zero))
                }
                token::LitKind::ByteStr => Some(PtrExpr::new(
                    expr,
                    hir_expr,
                    base_ty,
                    PtrExprBaseKind::ByteStr,
                )),
                _ => None,
            },
            ExprKind::AddrOf(_, _, pointee) => {
                let hir::ExprKind::AddrOf(_, _, hpointee) = hir_expr.kind else { panic!() };
                let mut ptr_expr = self.ptr_expr(pointee, hpointee)?;
                if ptr_expr.addr_of {
                    None
                } else {
                    ptr_expr.addr_of = true;
                    Some(ptr_expr)
                }
            }
            ExprKind::MethodCall(call) => {
                let hir::ExprKind::MethodCall(seg, hreceiver, _, _) = hir_expr.kind else {
                    return Some(PtrExpr::new(
                        expr,
                        hir_expr,
                        base_ty,
                        PtrExprBaseKind::Other,
                    ));
                };
                let name = seg.ident.name.as_str();
                if name == "offset" || name == "add" {
                    let mut ptr_expr = self.ptr_expr(&call.receiver, hreceiver)?;
                    ptr_expr.push_offset(&call.args[0]);
                    Some(ptr_expr)
                } else if name == "as_mut_ptr" || name == "as_ptr" {
                    let mut ptr_expr = self.ptr_expr(&call.receiver, hreceiver)?;
                    if ptr_expr.as_ptr {
                        None
                    } else {
                        ptr_expr.as_ptr = true;
                        ptr_expr.as_mut_ptr = name == "as_mut_ptr";
                        Some(ptr_expr)
                    }
                } else if name == "unwrap"
                    && let ExprKind::MethodCall(call) = &call.receiver.kind
                    && let name = call.seg.ident.name.as_str()
                    && (name == "last_mut" || name == "last")
                {
                    Some(PtrExpr::new(
                        expr,
                        hir_expr,
                        base_ty,
                        PtrExprBaseKind::Alloca,
                    ))
                } else if name == "wrapping_add" || name == "wrapping_sub" {
                    let opkind = match name {
                        "wrapping_add" => OpKind::WrappingAdd,
                        "wrapping_sub" => OpKind::WrappingSub,
                        _ => panic!(),
                    };
                    let mut ptr_expr = self.ptr_expr(&call.receiver, hreceiver)?;
                    ptr_expr.push_integer_op(&call.args[0], opkind);
                    Some(ptr_expr)
                } else {
                    Some(PtrExpr::new(
                        expr,
                        hir_expr,
                        base_ty,
                        PtrExprBaseKind::Other,
                    ))
                }
            }
            ExprKind::Binary(binop, lhs, rhs) if base_ty.is_usize() => {
                let hir::ExprKind::Binary(_, hlhs, _) = hir_expr.kind else { panic!() };
                let mut ptr_expr = self.ptr_expr(lhs, hlhs)?;
                ptr_expr.push_integer_bin_op(rhs, binop.node);
                Some(ptr_expr)
            }
            ExprKind::Array(..) => Some(PtrExpr::new(
                expr,
                hir_expr,
                base_ty,
                PtrExprBaseKind::Array,
            )),
            _ => None,
        }
    }

    fn expr_ctx(&self, expr: &hir::Expr<'tcx>) -> ExprCtx {
        let mut init_id = expr.hir_id;
        let mut curr_id = expr.hir_id;
        for (parent_id, parent_node) in self.tcx.hir_parent_iter(expr.hir_id) {
            let hir::Node::Expr(parent) = parent_node else { return ExprCtx::Rvalue };
            match parent.kind {
                hir::ExprKind::Cast(..) | hir::ExprKind::Field(..) => {}
                hir::ExprKind::DropTemps(..) => {
                    if curr_id == init_id {
                        init_id = parent_id;
                    }
                }
                hir::ExprKind::Assign(l, _r, _) | hir::ExprKind::AssignOp(_, l, _r) => {
                    if curr_id == l.hir_id {
                        return ExprCtx::Lvalue;
                    } else {
                        return ExprCtx::Rvalue;
                    }
                }
                hir::ExprKind::Index(e, _idx, _) => {
                    if curr_id != e.hir_id {
                        return ExprCtx::Rvalue;
                    }
                }
                hir::ExprKind::AddrOf(_, m, _) => {
                    if curr_id == init_id {
                        return ExprCtx::ImmediatelyAddrTaken;
                    } else {
                        return ExprCtx::AddrTaken(m.is_mut());
                    }
                }
                hir::ExprKind::MethodCall(seg, receiver, _, _) => {
                    let name = seg.ident.name.as_str();
                    if curr_id != receiver.hir_id {
                        return ExprCtx::Rvalue;
                    } else if name == "as_mut_ptr" || name.starts_with("set_") {
                        return ExprCtx::AddrTaken(true);
                    } else if name == "as_ptr" {
                        return ExprCtx::AddrTaken(false);
                    } else {
                        return ExprCtx::Rvalue;
                    }
                }
                _ => return ExprCtx::Rvalue,
            }
            curr_id = parent_id;
        }
        ExprCtx::Rvalue
    }

    fn behind_subscripts(&self, expr: &hir::Expr<'tcx>) -> PathOrDeref {
        match hir_unwrap_subscript(expr).kind {
            hir::ExprKind::Path(_) => PathOrDeref::Path,
            hir::ExprKind::Unary(UnOp::Deref, e) => {
                let e = utils::hir::unwrap_drop_temps(e);
                let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = e.kind else {
                    return PathOrDeref::Other;
                };
                let Res::Local(hir_id) = path.res else { return PathOrDeref::Other };
                PathOrDeref::Deref(hir_id)
            }
            _ => PathOrDeref::Other,
        }
    }

    fn projected_base_mutability(&self, pe: &PtrExpr<'_, 'tcx>, fallback: bool) -> bool {
        match self.behind_subscripts(pe.hir_base) {
            PathOrDeref::Deref(hir_id) => self
                .effective_ptr_kind(hir_id)
                .or_else(|| self.ptr_kinds.get(&hir_id).copied())
                .map_or(fallback, |kind| kind.is_mut()),
            PathOrDeref::Path | PathOrDeref::Other => fallback,
        }
    }

    fn is_base_not_a_raw_ptr(&self, pe: &PtrExpr<'_, 'tcx>) -> bool {
        match pe.base_kind {
            PtrExprBaseKind::Path(_) | PtrExprBaseKind::Alloca | PtrExprBaseKind::Array => true,
            PtrExprBaseKind::Other => match self.behind_subscripts(pe.hir_base) {
                PathOrDeref::Path => true,
                PathOrDeref::Deref(hir_id) => {
                    matches!(
                        self.effective_ptr_kind(hir_id)
                            .unwrap_or(self.ptr_kinds[&hir_id]),
                        PtrKind::Ref(_)
                            | PtrKind::OptRef(_)
                            | PtrKind::Box
                            | PtrKind::OptBox
                            | PtrKind::BoxedSlice
                            | PtrKind::OptBoxedSlice
                            | PtrKind::Slice(_)
                            | PtrKind::SliceCursor(_)
                    )
                }
                PathOrDeref::Other => pe.base_ty.is_array(),
            },
            _ => false,
        }
    }

    fn projected_expr(&self, pe: &PtrExpr<'_, 'tcx>, m: bool, mut is_raw: bool) -> Expr {
        let current_mut = self.ptr_source_kind(pe).map_or_else(
            || match pe.base_ty.kind() {
                ty::TyKind::RawPtr(_, m) => m.is_mut(),
                ty::TyKind::Array(..) => self.projected_base_mutability(pe, m),
                _ => m,
            },
            |kind| kind.is_mut(),
        );
        let mut is_plain_slice = matches!(self.ptr_source_kind(pe), Some(PtrKind::Slice(_)));
        // A "data container" is a Vec/array accessed via as_ptr that is NOT a cursor.
        // For these, offsets should produce re-sliced expressions, not cursor operations.
        let is_data_container = pe.as_ptr
            || matches!(
                pe.base_kind,
                PtrExprBaseKind::Array | PtrExprBaseKind::Alloca
            );
        let is_mut_cursor_base =
            matches!(self.ptr_source_kind(pe), Some(PtrKind::SliceCursor(true)));
        let mut owns_cursor = false;
        let mut e = pe.base.clone();
        if pe.projs.is_empty() {
            return e;
        }
        let mut from_ty = slice_like_container_inner_ty(pe.base_ty, self.tcx)
            .or_else(|| unwrap_ptr_or_arr_from_mir_ty(pe.base_ty, self.tcx))
            .unwrap();
        let mut is_array = pe.base_ty.is_array();
        for proj in &pe.projs {
            match proj {
                PtrExprProj::Offset(offset) => {
                    if is_raw {
                        e = utils::expr!(
                            "({}).offset({})",
                            pprust::expr_to_string(&e),
                            pprust::expr_to_string(offset),
                        );
                    } else if is_data_container || is_plain_slice {
                        // Base is a data container (Vec, array) — return a re-sliced expression.
                        let base_str = pprust::expr_to_string(&e);
                        if is_array {
                            e = utils::expr!(
                                "(&{}({}))[({}) as usize..]",
                                if current_mut { "mut " } else { "" },
                                base_str,
                                pprust::expr_to_string(offset),
                            );
                            is_plain_slice = true;
                        } else {
                            e = utils::expr!(
                                "({})[({}) as usize..]",
                                base_str,
                                pprust::expr_to_string(offset),
                            );
                        }
                    } else if is_mut_cursor_base {
                        if m {
                            if owns_cursor {
                                e = utils::expr!(
                                    "({}).offset_by(({}) as isize)",
                                    pprust::expr_to_string(&e),
                                    pprust::expr_to_string(offset),
                                );
                            } else {
                                e = utils::expr!(
                                    "({}).as_deref_mut().offset_by(({}) as isize)",
                                    pprust::expr_to_string(&e),
                                    pprust::expr_to_string(offset),
                                );
                                owns_cursor = true;
                            }
                        } else if is_slice_cursor_mut_constructor_call(&e) {
                            e = utils::expr!(
                                "({}).as_deref().offset_by(({}) as isize)",
                                pprust::expr_to_string(&e),
                                pprust::expr_to_string(offset),
                            );
                        } else {
                            e = utils::expr!(
                                "crate::slice_cursor::SliceCursor::new(({}).as_slice()).offset_by(({}) as isize)",
                                pprust::expr_to_string(&e),
                                pprust::expr_to_string(offset),
                            );
                        }
                    } else {
                        e = utils::expr!(
                            "({}).offset_by(({}) as isize)",
                            pprust::expr_to_string(&e),
                            pprust::expr_to_string(offset),
                        );
                    }
                }
                PtrExprProj::Cast(ty) if ty.is_usize() => {
                    owns_cursor = false;
                    if is_raw {
                        e = utils::expr!("({}) as usize", pprust::expr_to_string(&e),);
                    } else {
                        e = utils::expr!(
                            "({}).as{}_ptr() as usize",
                            pprust::expr_to_string(&e),
                            if current_mut { "_mut" } else { "" },
                        );
                    }
                    is_raw = true;
                }
                PtrExprProj::Cast(ty) => {
                    owns_cursor = false;
                    let (to_ty, _) = unwrap_ptr_from_mir_ty(*ty).unwrap();
                    if is_raw {
                        e = utils::expr!(
                            "({}) as *{} {}",
                            pprust::expr_to_string(&e),
                            if m { "mut" } else { "const" },
                            mir_ty_to_string(to_ty, self.tcx),
                        );
                        from_ty = to_ty;
                    } else {
                        if matches!(e.kind, ExprKind::Index(..))
                            || is_data_container
                            || is_array
                            || is_plain_slice
                        {
                            e = self.plain_slice_from_slice(&e, pe, current_mut, to_ty, from_ty);
                            is_plain_slice = true;
                        } else {
                            e = self.cursor_from_slice_or_cursor(
                                &e,
                                pe,
                                current_mut,
                                to_ty,
                                from_ty,
                            );
                        }
                        from_ty = to_ty;
                    }
                }
                PtrExprProj::IntegerOp(expr, op) => {
                    owns_cursor = false;
                    let method = match op {
                        OpKind::WrappingAdd => "wrapping_add",
                        OpKind::WrappingSub => "wrapping_sub",
                    };
                    e = utils::expr!(
                        "({}).{}({})",
                        pprust::expr_to_string(&e),
                        method,
                        pprust::expr_to_string(expr),
                    );
                }
                PtrExprProj::IntegerBinOp(expr, op) => {
                    owns_cursor = false;
                    let op_str = match op {
                        BinOpKind::BitAnd => "&",
                        BinOpKind::BitOr => "|",
                        _ => panic!(),
                    };
                    e = utils::expr!(
                        "({}) {} ({})",
                        pprust::expr_to_string(&e),
                        op_str,
                        pprust::expr_to_string(expr),
                    );
                }
            }
            is_array = false;
        }
        e
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PathOrDeref {
    Path,
    Deref(HirId),
    Other,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExprCtx {
    Lvalue,
    Rvalue,
    ImmediatelyAddrTaken,
    AddrTaken(bool),
}

#[inline]
pub fn unwrap_ptr_from_mir_ty(ty: ty::Ty<'_>) -> Option<(ty::Ty<'_>, ty::Mutability)> {
    match ty.kind() {
        ty::TyKind::RawPtr(ty, m) | ty::TyKind::Ref(_, ty, m) => Some((*ty, *m)),
        _ => None,
    }
}

fn unwrap_ptr_or_arr_from_mir_ty<'tcx>(
    ty: ty::Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<ty::Ty<'tcx>> {
    match ty.kind() {
        ty::TyKind::RawPtr(ty, _)
        | ty::TyKind::Ref(_, ty, _)
        | ty::TyKind::Slice(ty)
        | ty::TyKind::Array(ty, _) => Some(*ty),
        ty::TyKind::Adt(adt_def, gargs) => {
            let name = tcx.item_name(adt_def.did());
            if name == rustc_span::sym::Vec {
                let ty::GenericArgKind::Type(ty) = gargs[0].kind() else { panic!() };
                Some(ty)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn slice_like_container_inner_ty<'tcx>(
    ty: ty::Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> Option<ty::Ty<'tcx>> {
    match ty.kind() {
        ty::TyKind::Ref(_, inner, _) => slice_like_container_inner_ty(*inner, tcx),
        ty::TyKind::Slice(ty) | ty::TyKind::Array(ty, _) => Some(*ty),
        ty::TyKind::Adt(adt_def, gargs) => {
            let name = tcx.item_name(adt_def.did());
            if name == rustc_span::sym::Vec {
                let ty::GenericArgKind::Type(ty) = gargs[0].kind() else { panic!() };
                Some(ty)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn ty_is_borrowed_slice_like_container<'tcx>(ty: ty::Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    matches!(
        ty.kind(),
        ty::TyKind::Ref(_, inner, _) if slice_like_container_inner_ty(*inner, tcx).is_some()
    )
}

fn ty_is_slice_ref(ty: ty::Ty<'_>) -> bool {
    matches!(ty.kind(), ty::TyKind::Ref(_, inner, _) if matches!(inner.kind(), ty::TyKind::Slice(_)))
        || matches!(ty.kind(), ty::TyKind::Slice(_))
}

#[inline]
fn mk_opt_ref_ast_ty_with_lifetime(inner_ty: String, mutability: bool, lifetime: Symbol) -> Ty {
    let m = if mutability { "mut " } else { "" };
    let lifetime = lifetime.as_str();
    utils::ty!("Option<&'{lifetime} {m}{inner_ty}>")
}

#[inline]
fn mk_slice_ast_ty_with_lifetime(inner_ty: String, mutability: bool, lifetime: Symbol) -> Ty {
    let m = if mutability { "mut " } else { "" };
    let lifetime = lifetime.as_str();
    utils::ty!("&'{lifetime} {m}[{inner_ty}]")
}

#[inline]
fn mk_cursor_ast_ty_with_lifetime(inner_ty: String, mutability: bool, lifetime: Symbol) -> Ty {
    let cursor = if mutability {
        "SliceCursorMut"
    } else {
        "SliceCursor"
    };
    let lifetime = lifetime.as_str();
    utils::ty!("crate::slice_cursor::{cursor}<'{lifetime}, {inner_ty}>")
}

/// Finds a `BareFn` type nested inside wrappers like `Option<fn(...)>`.
fn find_bare_fn_in_ty_mut(ty: &mut Ty) -> Option<&mut rustc_ast::BareFnTy> {
    match &mut ty.kind {
        TyKind::BareFn(bare_fn) => Some(bare_fn),
        TyKind::Path(_, path) => {
            let seg = path.segments.last_mut()?;
            let gen_args = seg.args.as_mut()?;
            let GenericArgs::AngleBracketed(angle_args) = &mut **gen_args else { return None };
            for arg in &mut angle_args.args {
                if let AngleBracketedArg::Arg(GenericArg::Type(inner_ty)) = arg
                    && let Some(bare_fn) = find_bare_fn_in_ty_mut(inner_ty)
                {
                    return Some(bare_fn);
                }
            }
            None
        }
        _ => None,
    }
}

/// Returns `true` if any parameter was rewritten to a SliceCursor type.
fn rewrite_bare_fn_inputs(
    bare_fn: &mut rustc_ast::BareFnTy,
    decisions: &[Option<PtrKind>],
) -> bool {
    let mut used_slice_cursor = false;
    for (param, decision) in bare_fn.decl.inputs.iter_mut().zip(decisions) {
        let Some(kind) = decision else { continue };
        let TyKind::Ptr(MutTy { ty: inner_ty, .. }) = &param.ty.kind else { continue };
        let inner_str = pprust::ty_to_string(inner_ty);
        let new_ty = match kind {
            PtrKind::Ref(m) => {
                let m = if *m { "mut " } else { "" };
                utils::ty!("&{m}{inner_str}")
            }
            PtrKind::OptRef(m) => {
                let m = if *m { "mut " } else { "" };
                utils::ty!("Option<&{m}{inner_str}>")
            }
            PtrKind::Slice(m) => {
                let m = if *m { "mut " } else { "" };
                utils::ty!("&{m}[{inner_str}]")
            }
            PtrKind::Raw(m) => {
                let m = if *m { "mut" } else { "const" };
                utils::ty!("*{m} {inner_str}")
            }
            PtrKind::Box => utils::ty!("Box<{inner_str}>"),
            PtrKind::OptBox => utils::ty!("Option<Box<{inner_str}>>"),
            PtrKind::BoxedSlice => utils::ty!("Box<[{inner_str}]>"),
            PtrKind::OptBoxedSlice => utils::ty!("Option<Box<[{inner_str}]>>"),
            PtrKind::SliceCursor(m) => {
                used_slice_cursor = true;
                if *m {
                    utils::ty!("crate::slice_cursor::SliceCursorMut<'_, {inner_str}>")
                } else {
                    utils::ty!("crate::slice_cursor::SliceCursor<'_, {inner_str}>")
                }
            }
        };
        param.ty = P(new_ty);
    }
    used_slice_cursor
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PtrExprBaseKind {
    Path(Res),
    Alloca,
    ByteStr,
    Zero,
    Array,
    Other,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OpKind {
    WrappingAdd,
    WrappingSub,
}

#[derive(Debug, Clone, Copy)]
enum PtrExprProj<'a, 'tcx> {
    Offset(&'a Expr),
    Cast(ty::Ty<'tcx>),
    IntegerOp(&'a Expr, OpKind),
    IntegerBinOp(&'a Expr, BinOpKind),
}

#[derive(Debug, Clone)]
struct PtrExpr<'a, 'tcx> {
    addr_of: bool,
    base: &'a Expr,
    hir_base: &'a hir::Expr<'tcx>,
    base_ty: ty::Ty<'tcx>,
    base_kind: PtrExprBaseKind,
    as_ptr: bool,
    as_mut_ptr: bool,
    projs: Vec<PtrExprProj<'a, 'tcx>>,
    cast_int: bool,
}

impl<'a, 'tcx> PtrExpr<'a, 'tcx> {
    #[inline]
    fn new(
        base: &'a Expr,
        hir_base: &'a hir::Expr<'tcx>,
        base_ty: ty::Ty<'tcx>,
        base_kind: PtrExprBaseKind,
    ) -> Self {
        PtrExpr {
            addr_of: false,
            base,
            hir_base,
            base_ty,
            base_kind,
            as_ptr: false,
            as_mut_ptr: false,
            projs: vec![],
            cast_int: false,
        }
    }

    #[inline]
    fn push_offset(&mut self, offset: &'a Expr) {
        self.projs.push(PtrExprProj::Offset(offset));
    }

    #[inline]
    fn push_cast(&mut self, ty: ty::Ty<'tcx>) {
        self.projs.push(PtrExprProj::Cast(ty));
    }

    #[inline]
    fn push_integer_op(&mut self, expr: &'a Expr, op: OpKind) {
        self.projs.push(PtrExprProj::IntegerOp(expr, op));
    }

    #[inline]
    fn push_integer_bin_op(&mut self, expr: &'a Expr, op: BinOpKind) {
        self.projs.push(PtrExprProj::IntegerBinOp(expr, op));
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.base_kind == PtrExprBaseKind::Zero
            && self.projs.is_empty()
            && !self.addr_of
            && !self.as_ptr
    }
}

fn combined_offsets(offsets: &[&Expr], cast_to_isize: bool) -> Option<Expr> {
    let (first, rest) = offsets.split_first()?;
    let format_offset = |offset: &Expr| {
        let offset = if cast_to_isize {
            offset
        } else {
            remove_redundant_isize_casts(offset)
        };
        let offset = pprust::expr_to_string(offset);
        if cast_to_isize {
            format!("({offset}) as isize")
        } else {
            format!("({offset})")
        }
    };
    let mut combined = format_offset(first);
    for offset in rest {
        combined = format!("({combined}).wrapping_add({})", format_offset(offset));
    }
    Some(utils::expr!("{combined}"))
}

fn remove_redundant_isize_casts(mut expr: &Expr) -> &Expr {
    loop {
        let ExprKind::Cast(inner, ty) = &unwrap_paren(expr).kind else {
            return expr;
        };
        let ExprKind::Cast(_, inner_ty) = &unwrap_paren(inner).kind else {
            return expr;
        };
        if !is_isize_ty(ty) || !is_isize_ty(inner_ty) {
            return expr;
        }
        expr = inner;
    }
}

fn is_isize_ty(ty: &Ty) -> bool {
    let TyKind::Path(None, path) = &ty.kind else {
        return false;
    };
    path.segments.len() == 1 && path.segments[0].ident.name.as_str() == "isize"
}

fn combined_cursor_offset(projs: &[PtrExprProj<'_, '_>]) -> Option<Expr> {
    let offsets = projs
        .iter()
        .map(|proj| match proj {
            PtrExprProj::Offset(offset) => Some(*offset),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    combined_offsets(&offsets, true)
}

#[derive(Default)]
struct CursorProjectionSimplifier {
    binding_scopes: Vec<FxHashMap<Symbol, bool>>,
    binding_counts: FxHashMap<Symbol, usize>,
}

impl MutVisitor for CursorProjectionSimplifier {
    fn visit_item(&mut self, item: &mut Item) {
        let outer_scopes = std::mem::take(&mut self.binding_scopes);
        let outer_counts = std::mem::take(&mut self.binding_counts);
        mut_visit::walk_item(self, item);
        self.binding_scopes = outer_scopes;
        self.binding_counts = outer_counts;
    }

    fn visit_fn(&mut self, fn_kind: FnKind<'_>, _span: rustc_span::Span, _id: NodeId) {
        match fn_kind {
            FnKind::Fn(context, visibility, function) => {
                let outer_scopes = std::mem::take(&mut self.binding_scopes);
                let outer_counts = std::mem::take(&mut self.binding_counts);

                let mut counter = BindingCounter::default();
                for param in &mut function.sig.decl.inputs {
                    counter.visit_pat(&mut param.pat);
                }
                if let Some(body) = &mut function.body {
                    counter.visit_block(body);
                }
                self.binding_counts = counter.counts;

                let mut param_scope = FxHashMap::default();
                for param in &function.sig.decl.inputs {
                    if let Some(name) = simple_binding_name(&param.pat) {
                        param_scope.insert(name, is_cursor_ty(&param.ty));
                    }
                }
                self.binding_scopes.push(param_scope);
                mut_visit::walk_fn(self, FnKind::Fn(context, visibility, function));

                self.binding_scopes = outer_scopes;
                self.binding_counts = outer_counts;
            }
            FnKind::Closure(binder, coroutine_kind, decl, body) => {
                let mut param_scope = FxHashMap::default();
                for param in &decl.inputs {
                    if let Some(name) = simple_binding_name(&param.pat) {
                        param_scope.insert(name, is_cursor_ty(&param.ty));
                    }
                }
                self.binding_scopes.push(param_scope);
                mut_visit::walk_fn(self, FnKind::Closure(binder, coroutine_kind, decl, body));
                self.binding_scopes.pop();
            }
        }
    }

    fn visit_block(&mut self, block: &mut Block) {
        self.binding_scopes.push(FxHashMap::default());
        mut_visit::walk_block(self, block);
        self.binding_scopes.pop();
    }

    fn visit_local(&mut self, local: &mut Local) {
        let binding = simple_binding_name(&local.pat)
            .map(|name| (name, local.ty.as_deref().is_some_and(is_cursor_ty)));
        mut_visit::walk_local(self, local);
        if let Some((name, is_cursor)) = binding {
            self.binding_scopes
                .last_mut()
                .expect("local outside a lexical scope")
                .insert(name, is_cursor);
        }
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        mut_visit::walk_expr(self, expr);

        if let ExprKind::MethodCall(call) = &mut unwrap_paren_mut(expr).kind
            && call.seg.ident.name.as_str() == "offset_by"
            && let Some(receiver) = cursor_offset_without_reborrow(&call.receiver)
        {
            call.receiver = receiver;
        }

        let replacement = if let ExprKind::Index(base, index, _) = &unwrap_paren(expr).kind
            && is_zero_integer_expr(index)
        {
            let mut offsets = Vec::new();
            self.cursor_offset_chain(base, &mut offsets)
                .and_then(|base| {
                    let offset = combined_offsets(&offsets, false)?;
                    let offset = pprust::expr_to_string(&offset);
                    Some(match base {
                        CursorIndexBase::Cursor(base) => {
                            let base = pprust::expr_to_string(base);
                            utils::expr!("({base})[{offset}]")
                        }
                        CursorIndexBase::Slice(slice) => {
                            let slice = pprust::expr_to_string(slice);
                            utils::expr!("({slice})[({offset}) as usize]")
                        }
                    })
                })
        } else {
            None
        };
        if let Some(replacement) = replacement {
            *expr = replacement;
        }
    }
}

impl CursorProjectionSimplifier {
    fn cursor_offset_chain<'a>(
        &self,
        expr: &'a Expr,
        offsets: &mut Vec<&'a Expr>,
    ) -> Option<CursorIndexBase<'a>> {
        match &unwrap_paren(expr).kind {
            ExprKind::MethodCall(call) => match call.seg.ident.name.as_str() {
                "offset_by" if call.args.len() == 1 => {
                    let base = self.cursor_offset_chain(&call.receiver, offsets)?;
                    offsets.push(&call.args[0]);
                    Some(base)
                }
                "as_deref_mut" if call.args.is_empty() => {
                    Some(CursorIndexBase::Cursor(&call.receiver))
                }
                _ => None,
            },
            ExprKind::Call(callee, args) if args.len() == 1 && is_slice_cursor_new(callee) => {
                let ExprKind::MethodCall(as_slice) = &unwrap_paren(&args[0]).kind else {
                    return None;
                };
                if as_slice.seg.ident.name.as_str() != "as_slice" || !as_slice.args.is_empty() {
                    return None;
                }
                self.cursor_offset_chain(&as_slice.receiver, offsets)
                    .or_else(|| {
                        self.is_cursor_binding(&as_slice.receiver)
                            .then_some(CursorIndexBase::Cursor(&as_slice.receiver))
                    })
                    .or(Some(CursorIndexBase::Slice(&args[0])))
            }
            _ => None,
        }
    }

    fn is_cursor_binding(&self, expr: &Expr) -> bool {
        let ExprKind::Path(None, path) = &unwrap_paren(expr).kind else {
            return false;
        };
        let [segment] = path.segments.as_slice() else {
            return false;
        };
        self.binding_scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(&segment.ident.name).copied())
            .unwrap_or(false)
            && self.binding_counts.get(&segment.ident.name) == Some(&1)
    }
}

#[derive(Default)]
struct BindingCounter {
    counts: FxHashMap<Symbol, usize>,
}

impl MutVisitor for BindingCounter {
    fn visit_pat(&mut self, pat: &mut Pat) {
        if let PatKind::Ident(_, ident, _) = &pat.kind {
            *self.counts.entry(ident.name).or_default() += 1;
        }
        mut_visit::walk_pat(self, pat);
    }
}

fn simple_binding_name(pat: &Pat) -> Option<Symbol> {
    let PatKind::Ident(_, ident, None) = &pat.kind else {
        return None;
    };
    Some(ident.name)
}

fn is_cursor_ty(ty: &Ty) -> bool {
    match &ty.kind {
        TyKind::Paren(ty) => is_cursor_ty(ty),
        TyKind::Path(None, path) => {
            let [crate_segment, module_segment, ty_segment] = path.segments.as_slice() else {
                return false;
            };
            crate_segment.ident.name.as_str() == "crate"
                && module_segment.ident.name.as_str() == "slice_cursor"
                && matches!(
                    ty_segment.ident.name.as_str(),
                    "SliceCursor" | "SliceCursorMut"
                )
        }
        _ => false,
    }
}

fn cursor_offset_without_reborrow(expr: &Expr) -> Option<P<Expr>> {
    let ExprKind::MethodCall(reborrow) = &unwrap_paren(expr).kind else {
        return None;
    };
    if reborrow.seg.ident.name.as_str() != "as_deref_mut" || !reborrow.args.is_empty() {
        return None;
    }
    let ExprKind::MethodCall(offset) = &unwrap_paren(&reborrow.receiver).kind else {
        return None;
    };
    (offset.seg.ident.name.as_str() == "offset_by").then(|| reborrow.receiver.clone())
}

enum CursorIndexBase<'a> {
    Cursor(&'a Expr),
    Slice(&'a Expr),
}

fn is_slice_cursor_new(expr: &Expr) -> bool {
    let ExprKind::Path(_, path) = &unwrap_paren(expr).kind else {
        return false;
    };
    let segments = &path.segments;
    segments.len() >= 2
        && segments[segments.len() - 2].ident.name.as_str() == "SliceCursor"
        && segments[segments.len() - 1].ident.name.as_str() == "new"
}

fn is_zero_integer_expr(expr: &Expr) -> bool {
    let ExprKind::Lit(lit) = &unwrap_cast_and_paren(expr).kind else {
        return false;
    };
    lit.kind == token::LitKind::Integer && lit.symbol.as_str() == "0"
}

fn unwrap_addr_of_deref(expr: &Expr) -> &Expr {
    if let ExprKind::AddrOf(_, _, e) = &unwrap_paren(expr).kind
        && let ExprKind::Unary(UnOp::Deref, e) = &unwrap_paren(e).kind
    {
        unwrap_addr_of_deref(e)
    } else {
        unwrap_paren(expr)
    }
}

fn unwrap_addr_of_deref_mut(expr: &mut Expr) -> &mut Expr {
    let expr = unwrap_paren_mut(expr);
    if let ExprKind::AddrOf(_, _, e) = &unwrap_paren(expr).kind
        && let ExprKind::Unary(UnOp::Deref, _) = &unwrap_paren(e).kind
    {
        let ExprKind::AddrOf(_, _, e) = &mut expr.kind else { unreachable!() };
        let e = unwrap_paren_mut(e);
        let ExprKind::Unary(UnOp::Deref, e) = &mut e.kind else { unreachable!() };
        unwrap_addr_of_deref_mut(e)
    } else {
        expr
    }
}

fn unwrap_addr_of(expr: &Expr) -> &Expr {
    if let ExprKind::AddrOf(_, _, e) = &unwrap_paren(expr).kind {
        unwrap_addr_of(e)
    } else {
        unwrap_paren(expr)
    }
}

fn addr_of_mutability(expr: &Expr) -> Option<bool> {
    if let ExprKind::AddrOf(_, mutability, _) = &unwrap_paren(expr).kind {
        Some(mutability.is_mut())
    } else {
        None
    }
}

fn place_expr_contains_deref(expr: &Expr) -> bool {
    match &unwrap_paren(expr).kind {
        ExprKind::Unary(UnOp::Deref, _) => true,
        ExprKind::Index(e, _, _) | ExprKind::Field(e, _) => place_expr_contains_deref(e),
        _ => false,
    }
}

#[allow(unused)]
fn unwrap_subscript(expr: &Expr) -> &Expr {
    match &expr.kind {
        ExprKind::Index(e, _, _) | ExprKind::Field(e, _) | ExprKind::Paren(e) => {
            unwrap_subscript(e)
        }
        _ => expr,
    }
}

#[allow(unused)]
fn unwrap_subscript_mut(expr: &mut Expr) -> &mut Expr {
    if !matches!(
        expr.kind,
        ExprKind::Index(_, _, _) | ExprKind::Field(_, _) | ExprKind::Paren(_)
    ) {
        return expr;
    }
    let (ExprKind::Index(e, _, _) | ExprKind::Field(e, _) | ExprKind::Paren(e)) = &mut expr.kind
    else {
        unreachable!()
    };
    unwrap_subscript_mut(e)
}

fn hir_unwrap_cast<'a, 'tcx>(expr: &'a hir::Expr<'tcx>) -> &'a hir::Expr<'tcx> {
    if let hir::ExprKind::Cast(e, _) = utils::hir::unwrap_drop_temps(expr).kind {
        hir_unwrap_cast(e)
    } else {
        utils::hir::unwrap_drop_temps(expr)
    }
}

fn hir_expr_starts_with_cast(expr: &hir::Expr<'_>) -> bool {
    matches!(
        utils::hir::unwrap_drop_temps(expr).kind,
        hir::ExprKind::Cast(..)
    )
}

fn hir_unwrap_addr_of_deref<'a, 'tcx>(expr: &'a hir::Expr<'tcx>) -> &'a hir::Expr<'tcx> {
    if let hir::ExprKind::AddrOf(_, _, e) = utils::hir::unwrap_drop_temps(expr).kind
        && let hir::ExprKind::Unary(UnOp::Deref, e) = utils::hir::unwrap_drop_temps(e).kind
    {
        hir_unwrap_addr_of_deref(e)
    } else {
        utils::hir::unwrap_drop_temps(expr)
    }
}

fn hir_unwrap_subscript<'a, 'tcx>(expr: &'a hir::Expr<'tcx>) -> &'a hir::Expr<'tcx> {
    match expr.kind {
        hir::ExprKind::Index(e, _, _)
        | hir::ExprKind::Field(e, _)
        | hir::ExprKind::DropTemps(e) => hir_unwrap_subscript(e),
        _ => expr,
    }
}

fn method_call_name(expr: &Expr) -> Option<Symbol> {
    if let ExprKind::MethodCall(call) = &unwrap_cast_and_paren(expr).kind {
        Some(call.seg.ident.name)
    } else {
        None
    }
}

fn is_null_ptr_constructor(expr: &Expr) -> bool {
    let ExprKind::Call(callee, args) = &unwrap_cast_and_paren(expr).kind else {
        return false;
    };
    if !args.is_empty() {
        return false;
    }
    let ExprKind::Path(_, path) = &unwrap_paren(callee).kind else {
        return false;
    };
    path.segments
        .last()
        .is_some_and(|seg| matches!(seg.ident.name.as_str(), "null" | "null_mut"))
}

fn is_null_like_ptr_arg(expr: &Expr) -> bool {
    let expr = unwrap_cast_and_paren(expr);
    if is_null_ptr_constructor(expr) {
        return true;
    }
    match &expr.kind {
        ExprKind::Lit(lit) => {
            matches!(lit.kind, token::LitKind::Integer) && lit.symbol.as_str() == "0"
        }
        ExprKind::Path(_, path) => path
            .segments
            .last()
            .is_some_and(|seg| seg.ident.name.as_str() == "NULL"),
        _ => false,
    }
}

fn expr_snippet(tcx: TyCtxt<'_>, expr: &Expr) -> Option<String> {
    tcx.sess
        .source_map()
        .span_to_snippet(expr.span)
        .ok()
        .map(|snippet| normalize_expr_snippet(&snippet))
}

fn borrow_target_expr_string(expr: &Expr) -> String {
    let expr = unwrap_paren(expr);
    let expr_str = pprust::expr_to_string(expr);
    match expr.kind {
        ExprKind::Path(..) | ExprKind::Field(..) | ExprKind::Index(..) => expr_str,
        _ => format!("({expr_str})"),
    }
}

fn add_lifetime_args_to_type_path_string(
    ty_name: String,
    existing_lifetime_count: usize,
    promoted_lifetime_args: &[String],
) -> String {
    if promoted_lifetime_args.is_empty() {
        return ty_name;
    }
    let Some(generic_start) = ty_name.find('<') else {
        return format!("{}<{}>", ty_name, promoted_lifetime_args.join(", "));
    };
    let Some(generic_end) = matching_angle_bracket(&ty_name, generic_start) else {
        return ty_name;
    };

    let prefix = &ty_name[..generic_start];
    let suffix = &ty_name[generic_end + 1..];
    let mut args = split_top_level_generic_args(&ty_name[generic_start + 1..generic_end]);
    let insert_at = existing_lifetime_count.min(args.len());
    if generic_args_have_lifetimes(&args, insert_at, promoted_lifetime_args.len()) {
        return ty_name;
    }
    for (offset, lifetime) in promoted_lifetime_args.iter().enumerate() {
        args.insert(insert_at + offset, lifetime.clone());
    }

    if args.is_empty() {
        format!("{prefix}<{}>{suffix}", promoted_lifetime_args.join(", "))
    } else {
        format!("{prefix}<{}>{suffix}", args.join(", "))
    }
}

fn strip_top_level_generic_args_from_type_path(ty_name: String) -> String {
    let Some(generic_start) = ty_name.find('<') else {
        return ty_name;
    };
    let Some(generic_end) = matching_angle_bracket(&ty_name, generic_start) else {
        return ty_name;
    };
    format!(
        "{}{}",
        &ty_name[..generic_start],
        &ty_name[generic_end + 1..]
    )
}

fn matching_angle_bracket(s: &str, generic_start: usize) -> Option<usize> {
    let mut depth = 0usize;
    for (offset, ch) in s[generic_start..].char_indices() {
        match ch {
            '<' => depth += 1,
            '>' => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some(generic_start + offset);
                }
            }
            _ => {}
        }
    }
    None
}

fn split_top_level_generic_args(args: &str) -> Vec<String> {
    let mut result = Vec::new();
    let mut depth = 0isize;
    let mut start = 0usize;
    for (index, ch) in args.char_indices() {
        match ch {
            '<' | '(' | '[' => depth += 1,
            '>' | ')' | ']' => depth -= 1,
            ',' if depth == 0 => {
                let arg = args[start..index].trim();
                if !arg.is_empty() {
                    result.push(arg.to_string());
                }
                start = index + ch.len_utf8();
            }
            _ => {}
        }
    }
    let arg = args[start..].trim();
    if !arg.is_empty() {
        result.push(arg.to_string());
    }
    result
}

fn generic_args_have_lifetimes(args: &[String], start: usize, count: usize) -> bool {
    args.get(start..start + count)
        .is_some_and(|args| args.iter().all(|arg| arg.trim_start().starts_with('\'')))
}

fn path_segment_has_expected_lifetimes(
    seg: &PathSegment,
    existing_lifetime_count: usize,
    promoted_lifetimes: &[Symbol],
) -> bool {
    if promoted_lifetimes.is_empty() {
        return true;
    }
    let Some(args) = &seg.args else {
        return false;
    };
    let GenericArgs::AngleBracketed(args) = &**args else {
        return false;
    };
    if args.args.len() < existing_lifetime_count + promoted_lifetimes.len() {
        return false;
    }
    args.args
        .iter()
        .skip(existing_lifetime_count)
        .take(promoted_lifetimes.len())
        .all(|arg| matches!(arg, AngleBracketedArg::Arg(GenericArg::Lifetime(_))))
}

fn size_of_type_name_candidates(ty_name: &str) -> Vec<String> {
    let mut candidates = vec![ty_name.to_string()];
    if let Some(stripped) = ty_name.strip_prefix("crate::") {
        candidates.push(stripped.to_string());
    }
    if let Some(last) = ty_name.rsplit("::").next() {
        candidates.push(last.to_string());
    }
    candidates.sort();
    candidates.dedup();
    candidates
}

fn ast_is_exact_size_of_expr(tcx: TyCtxt<'_>, expr: &Expr, ty_name: &str) -> bool {
    let Some(snippet) = expr_snippet(tcx, unwrap_cast_and_paren(expr)) else {
        return false;
    };
    size_of_type_name_candidates(ty_name)
        .into_iter()
        .flat_map(|candidate_ty| {
            [
                format!("::core::mem::size_of::<{candidate_ty}>()"),
                format!("core::mem::size_of::<{candidate_ty}>()"),
                format!("::std::mem::size_of::<{candidate_ty}>()"),
                format!("std::mem::size_of::<{candidate_ty}>()"),
            ]
        })
        .map(|candidate| normalize_expr_snippet(&candidate))
        .any(|candidate| snippet == candidate)
}

fn ast_is_literal_one(expr: &Expr) -> bool {
    let expr = unwrap_cast_and_paren(expr);
    matches!(expr.kind, ExprKind::Lit(lit) if matches!(lit.kind, token::LitKind::Integer) && lit.symbol.as_str() == "1")
}

fn expr_supports_scalar_opt_box_allocator_root<'tcx>(
    tcx: TyCtxt<'tcx>,
    expr: &Expr,
    lhs_inner_ty: ty::Ty<'tcx>,
) -> bool {
    let ExprKind::Call(callee, args) = &unwrap_cast_and_paren(expr).kind else {
        return false;
    };
    let ExprKind::Path(_, path) = &unwrap_paren(callee).kind else {
        return false;
    };
    let Some(name) = path.segments.last().map(|seg| seg.ident.name.as_str()) else {
        return false;
    };
    let ty_name = mir_ty_to_string(lhs_inner_ty, tcx);
    match (name, &args[..]) {
        ("malloc", [bytes]) => ast_is_exact_size_of_expr(tcx, bytes, &ty_name),
        ("calloc", [count, elem_size]) => {
            ast_is_literal_one(count) && ast_is_exact_size_of_expr(tcx, elem_size, &ty_name)
        }
        ("realloc", [ptr, bytes]) if is_null_like_ptr_arg(ptr) => {
            ast_is_exact_size_of_expr(tcx, bytes, &ty_name)
        }
        _ => false,
    }
}

fn hir_unwrap_casts<'a, 'tcx>(mut expr: &'a hir::Expr<'tcx>) -> &'a hir::Expr<'tcx> {
    loop {
        match expr.kind {
            hir::ExprKind::Cast(inner, _) | hir::ExprKind::DropTemps(inner) => expr = inner,
            _ => return expr,
        }
    }
}

fn hir_call_name(expr: &hir::Expr<'_>) -> Option<Symbol> {
    let hir::ExprKind::Call(callee, _) = hir_unwrap_casts(expr).kind else {
        return None;
    };
    let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_unwrap_casts(callee).kind else {
        return None;
    };
    path.segments.last().map(|seg| seg.ident.name)
}

fn normalize_expr_snippet(snippet: &str) -> String {
    snippet.chars().filter(|c| !c.is_whitespace()).collect()
}

fn hir_expr_snippet(tcx: TyCtxt<'_>, expr: &hir::Expr<'_>) -> Option<String> {
    tcx.sess
        .source_map()
        .span_to_snippet(expr.span)
        .ok()
        .map(|snippet| normalize_expr_snippet(&snippet))
}

fn hir_size_of_call_matches_expected<'tcx>(
    tcx: TyCtxt<'tcx>,
    expr: &hir::Expr<'_>,
    expected_ty: ty::Ty<'tcx>,
) -> bool {
    let hir::ExprKind::Call(callee, args) = hir_unwrap_casts(expr).kind else {
        return false;
    };
    if !args.is_empty() {
        return false;
    }
    let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_unwrap_casts(callee).kind else {
        return false;
    };
    let Some(seg) = path.segments.last() else {
        return false;
    };
    if seg.ident.name != Symbol::intern("size_of") {
        return false;
    }
    let Some(args) = seg.args else {
        return false;
    };
    let [hir::GenericArg::Type(hir_ty)] = args.args else {
        return false;
    };
    let matched_ty = tcx.typeck(hir_ty.hir_id.owner).node_type(hir_ty.hir_id);
    match expected_ty.kind() {
        ty::TyKind::Bool => matches!(matched_ty.kind(), ty::TyKind::Bool),
        ty::TyKind::Char => matches!(matched_ty.kind(), ty::TyKind::Char),
        ty::TyKind::Int(expected) => {
            matches!(matched_ty.kind(), ty::TyKind::Int(found) if found == expected)
        }
        ty::TyKind::Uint(expected) => {
            matches!(matched_ty.kind(), ty::TyKind::Uint(found) if found == expected)
        }
        ty::TyKind::Float(expected) => {
            matches!(matched_ty.kind(), ty::TyKind::Float(found) if found == expected)
        }
        ty::TyKind::Adt(expected, _) => {
            matches!(matched_ty.kind(), ty::TyKind::Adt(found, _) if found.did() == expected.did())
        }
        ty::TyKind::Foreign(expected) => {
            matches!(matched_ty.kind(), ty::TyKind::Foreign(found) if found == expected)
        }
        _ => matched_ty == expected_ty,
    }
}

fn hir_is_exact_size_of_expr(tcx: TyCtxt<'_>, expr: &hir::Expr<'_>, ty_name: &str) -> bool {
    let Some(snippet) = hir_expr_snippet(tcx, hir_unwrap_casts(expr)) else {
        return false;
    };
    size_of_type_name_candidates(ty_name)
        .into_iter()
        .flat_map(|candidate_ty| {
            [
                format!("::core::mem::size_of::<{candidate_ty}>()"),
                format!("core::mem::size_of::<{candidate_ty}>()"),
                format!("::std::mem::size_of::<{candidate_ty}>()"),
                format!("std::mem::size_of::<{candidate_ty}>()"),
            ]
        })
        .map(|candidate| normalize_expr_snippet(&candidate))
        .any(|candidate| snippet == candidate)
}

fn hir_is_exact_c_char_size_of_expr(tcx: TyCtxt<'_>, expr: &hir::Expr<'_>) -> bool {
    let Some(snippet) = hir_expr_snippet(tcx, hir_unwrap_casts(expr)) else {
        return false;
    };
    [
        "::core::mem::size_of::<core::ffi::c_char>()",
        "core::mem::size_of::<core::ffi::c_char>()",
        "::std::mem::size_of::<core::ffi::c_char>()",
        "std::mem::size_of::<core::ffi::c_char>()",
        "::core::mem::size_of::<std::ffi::c_char>()",
        "core::mem::size_of::<std::ffi::c_char>()",
        "::std::mem::size_of::<std::ffi::c_char>()",
        "std::mem::size_of::<std::ffi::c_char>()",
    ]
    .into_iter()
    .map(normalize_expr_snippet)
    .any(|candidate| snippet == candidate)
}

fn ty_is_byte_sized_raw_inner(ty: ty::Ty<'_>) -> bool {
    matches!(
        ty.kind(),
        ty::TyKind::Int(ty::IntTy::I8) | ty::TyKind::Uint(ty::UintTy::U8)
    )
}

fn array_field_direct_offset<'a, 'tcx>(
    pe: &PtrExpr<'a, 'tcx>,
    allow_casts: bool,
) -> Option<&'a Expr> {
    if !pe.as_ptr
        || !pe.base_ty.is_array()
        || !matches!(unwrap_paren(pe.base).kind, ExprKind::Field(..))
    {
        return None;
    }
    let [PtrExprProj::Offset(offset), rest @ ..] = pe.projs.as_slice() else {
        return None;
    };
    if allow_casts {
        if !rest.iter().all(
            |proj| matches!(proj, PtrExprProj::Cast(ty) if unwrap_ptr_from_mir_ty(*ty).is_some()),
        ) {
            return None;
        }
    } else if !rest.is_empty() {
        return None;
    }
    Some(*offset)
}

fn is_array_field_ptr_arithmetic(pe: &PtrExpr<'_, '_>) -> bool {
    pe.as_ptr
        && pe.as_mut_ptr
        && pe.base_ty.is_array()
        && matches!(unwrap_paren(pe.base).kind, ExprKind::Field(..))
        && pe.projs.iter().any(|proj| {
            matches!(
                proj,
                PtrExprProj::Offset(_) | PtrExprProj::IntegerOp(..) | PtrExprProj::IntegerBinOp(..)
            )
        })
}

fn hir_is_casted_local(rhs: &hir::Expr<'_>, target: HirId) -> bool {
    match rhs.kind {
        hir::ExprKind::Cast(inner, _) | hir::ExprKind::DropTemps(inner) => {
            hir_unwrapped_local_id(inner) == Some(target) || hir_is_casted_local(inner, target)
        }
        _ => false,
    }
}

fn hir_is_byte_view_self_update(target: HirId, rhs: &hir::Expr<'_>) -> bool {
    let rhs = hir_unwrap_casts(rhs);
    matches!(
        rhs.kind,
        hir::ExprKind::MethodCall(seg, receiver, args, _)
            if hir_unwrapped_local_id(receiver) == Some(target)
                && args.len() == 1
                && matches!(
                    seg.ident.name.as_str(),
                    "offset" | "add" | "wrapping_offset"
                )
    )
}

fn hir_is_literal_one(tcx: TyCtxt<'_>, expr: &hir::Expr<'_>) -> bool {
    hir_expr_snippet(tcx, hir_unwrap_casts(expr)).is_some_and(|snippet| snippet == "1")
}

fn ty_contains_param(ty: ty::Ty<'_>) -> bool {
    match ty.kind() {
        ty::TyKind::Param(_) => true,
        ty::TyKind::Adt(_, args) => args.iter().any(|arg| match arg.kind() {
            ty::GenericArgKind::Type(ty) => ty_contains_param(ty),
            _ => false,
        }),
        ty::TyKind::RawPtr(inner, _)
        | ty::TyKind::Ref(_, inner, _)
        | ty::TyKind::Array(inner, _)
        | ty::TyKind::Slice(inner) => ty_contains_param(*inner),
        ty::TyKind::Tuple(elems) => elems.iter().any(ty_contains_param),
        _ => false,
    }
}

fn hir_is_null_ptr_constructor(expr: &hir::Expr<'_>) -> bool {
    let hir::ExprKind::Call(callee, args) = hir_unwrap_casts(expr).kind else {
        return false;
    };
    if !args.is_empty() {
        return false;
    }
    let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_unwrap_casts(callee).kind else {
        return false;
    };
    path.segments
        .last()
        .is_some_and(|seg| matches!(seg.ident.name.as_str(), "null" | "null_mut"))
}

fn hir_is_null_like_ptr_arg(tcx: TyCtxt<'_>, expr: &hir::Expr<'_>) -> bool {
    let expr = hir_unwrap_casts(expr);
    if hir_is_null_ptr_constructor(expr) {
        return true;
    }
    match expr.kind {
        hir::ExprKind::Lit(_) => hir_expr_snippet(tcx, expr).is_some_and(|snippet| snippet == "0"),
        hir::ExprKind::Path(hir::QPath::Resolved(_, path)) => path
            .segments
            .last()
            .is_some_and(|seg| seg.ident.name.as_str() == "NULL"),
        _ => false,
    }
}

fn hir_supports_scalar_box_allocator_root<'tcx>(
    tcx: TyCtxt<'tcx>,
    lhs_inner_ty: ty::Ty<'tcx>,
    rhs: &hir::Expr<'tcx>,
) -> bool {
    let expected_ty_name =
        (!ty_contains_param(lhs_inner_ty)).then(|| mir_ty_to_string(lhs_inner_ty, tcx));
    let hir::ExprKind::Call(_, args) = hir_unwrap_casts(rhs).kind else {
        return false;
    };
    let Some(name) = hir_call_name(rhs) else {
        return false;
    };
    match (name, args) {
        (name, [bytes]) if name == Symbol::intern("malloc") => {
            hir_size_of_call_matches_expected(tcx, bytes, lhs_inner_ty)
                || expected_ty_name
                    .as_ref()
                    .is_some_and(|ty_name| hir_is_exact_size_of_expr(tcx, bytes, ty_name))
        }
        (name, [count, elem_size]) if name == Symbol::intern("calloc") => {
            hir_is_literal_one(tcx, count)
                && (hir_size_of_call_matches_expected(tcx, elem_size, lhs_inner_ty)
                    || expected_ty_name
                        .as_ref()
                        .is_some_and(|ty_name| hir_is_exact_size_of_expr(tcx, elem_size, ty_name)))
        }
        (name, [ptr, bytes])
            if name == Symbol::intern("realloc") && hir_is_null_like_ptr_arg(tcx, ptr) =>
        {
            hir_size_of_call_matches_expected(tcx, bytes, lhs_inner_ty)
                || expected_ty_name
                    .as_ref()
                    .is_some_and(|ty_name| hir_is_exact_size_of_expr(tcx, bytes, ty_name))
        }
        _ => false,
    }
}

fn hir_is_supported_boxed_slice_allocator_root(tcx: TyCtxt<'_>, rhs: &hir::Expr<'_>) -> bool {
    let hir::ExprKind::Call(_, args) = hir_unwrap_casts(rhs).kind else {
        return false;
    };
    let Some(name) = hir_call_name(rhs) else {
        return false;
    };
    match (name, args) {
        (name, [_]) if name == Symbol::intern("malloc") => true,
        (name, [_, _]) if name == Symbol::intern("calloc") => true,
        (name, [ptr, _]) if name == Symbol::intern("realloc") => hir_is_null_like_ptr_arg(tcx, ptr),
        _ => false,
    }
}

fn hir_is_unsupported_scalar_box_allocator_root<'tcx>(
    tcx: TyCtxt<'tcx>,
    lhs_inner_ty: ty::Ty<'tcx>,
    rhs: &hir::Expr<'tcx>,
) -> bool {
    matches!(
        hir_call_name(rhs),
        Some(name)
            if name == Symbol::intern("malloc")
                || name == Symbol::intern("calloc")
                || name == Symbol::intern("realloc")
    ) && !hir_supports_scalar_box_allocator_root(tcx, lhs_inner_ty, rhs)
}

fn fn_has_unsupported_box_assignment<'tcx>(
    tcx: TyCtxt<'tcx>,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    target_hir_id: HirId,
    target_kind: PtrKind,
    lhs_inner_ty: ty::Ty<'tcx>,
) -> bool {
    struct AssignmentVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        sig_decs: &'a SigDecisions,
        ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
        target_hir_id: HirId,
        target_kind: PtrKind,
        lhs_inner_ty: ty::Ty<'tcx>,
        found: bool,
    }

    impl<'tcx> Visitor<'tcx> for AssignmentVisitor<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if self.found {
                return;
            }
            if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = lhs.kind
                && let Res::Local(lhs_hir_id) = path.res
                && lhs_hir_id == self.target_hir_id
                && !hir_rhs_supports_box_target(
                    self.tcx,
                    self.sig_decs,
                    self.ptr_kinds,
                    rhs,
                    self.target_kind,
                    self.lhs_inner_ty,
                )
            {
                self.found = true;
                return;
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let body_id = tcx.hir_body_owned_by(target_hir_id.owner.def_id);
    let mut visitor = AssignmentVisitor {
        tcx,
        sig_decs,
        ptr_kinds,
        target_hir_id,
        target_kind,
        lhs_inner_ty,
        found: false,
    };
    visitor.visit_body(body_id);
    visitor.found
}

fn fn_tail_returns_unsupported_box_binding<'tcx>(
    tcx: TyCtxt<'tcx>,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    owner: LocalDefId,
    target_kind: PtrKind,
    lhs_inner_ty: ty::Ty<'tcx>,
) -> bool {
    fn returned_expr_is_unsupported<'tcx>(
        tcx: TyCtxt<'tcx>,
        sig_decs: &SigDecisions,
        ptr_kinds: &FxHashMap<HirId, PtrKind>,
        expr: &'tcx hir::Expr<'tcx>,
        target_kind: PtrKind,
        lhs_inner_ty: ty::Ty<'tcx>,
    ) -> bool {
        if !hir_rhs_supports_box_target(tcx, sig_decs, ptr_kinds, expr, target_kind, lhs_inner_ty)
            && !hir_rhs_supports_optional_box_return(tcx, sig_decs, ptr_kinds, expr, target_kind)
        {
            return true;
        }
        let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_unwrap_casts(expr).kind else {
            return false;
        };
        let Res::Local(hir_id) = path.res else {
            return false;
        };
        fn_has_unsupported_box_assignment(
            tcx,
            sig_decs,
            ptr_kinds,
            hir_id,
            target_kind,
            lhs_inner_ty,
        )
    }

    struct ReturnVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        sig_decs: &'a SigDecisions,
        ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
        target_kind: PtrKind,
        lhs_inner_ty: ty::Ty<'tcx>,
        found: bool,
    }

    impl<'tcx> Visitor<'tcx> for ReturnVisitor<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if self.found {
                return;
            }
            if let hir::ExprKind::Ret(Some(ret)) = expr.kind
                && returned_expr_is_unsupported(
                    self.tcx,
                    self.sig_decs,
                    self.ptr_kinds,
                    ret,
                    self.target_kind,
                    self.lhs_inner_ty,
                )
            {
                self.found = true;
                return;
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let body = tcx.hir_body_owned_by(owner);
    let mut visitor = ReturnVisitor {
        tcx,
        sig_decs,
        ptr_kinds,
        target_kind,
        lhs_inner_ty,
        found: false,
    };
    visitor.visit_body(body);
    if visitor.found {
        return true;
    }

    let hir::ExprKind::Block(block, _) = body.value.kind else {
        return false;
    };
    let Some(tail) = block.expr else {
        return false;
    };
    returned_expr_is_unsupported(tcx, sig_decs, ptr_kinds, tail, target_kind, lhs_inner_ty)
}

fn normalize_forced_raw_bindings(
    tcx: TyCtxt<'_>,
    ptr_kinds: &mut FxHashMap<HirId, PtrKind>,
    forced_raw_bindings: &FxHashSet<HirId>,
) {
    for (hir_id, kind) in ptr_kinds.iter_mut() {
        if forced_raw_bindings.contains(hir_id) {
            let ty = tcx.typeck(hir_id.owner).node_type(*hir_id);
            let raw_mut = unwrap_ptr_from_mir_ty(ty)
                .map(|(_, m)| m.is_mut())
                .unwrap_or_else(|| kind.is_mut());
            *kind = PtrKind::Raw(raw_mut);
        }
    }
}

fn normalize_owning_call_result_bindings(
    tcx: TyCtxt<'_>,
    sig_decs: &SigDecisions,
    ptr_kinds: &mut FxHashMap<HirId, PtrKind>,
    forced_raw_bindings: &FxHashSet<HirId>,
) {
    struct OwningCallResultVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        sig_decs: &'a SigDecisions,
        ptr_kinds: &'a mut FxHashMap<HirId, PtrKind>,
        forced_raw_bindings: &'a FxHashSet<HirId>,
    }

    impl<'tcx> OwningCallResultVisitor<'_, 'tcx> {
        fn normalize_binding(&mut self, hir_id: HirId, rhs: &'tcx hir::Expr<'tcx>) {
            if self.forced_raw_bindings.contains(&hir_id) {
                return;
            }
            let Some(output_kind) =
                hir_callee_output_kind(self.tcx, self.sig_decs, self.ptr_kinds, rhs)
            else {
                return;
            };
            if output_kind.is_owning_box_like() {
                self.ptr_kinds.insert(hir_id, output_kind);
            }
        }
    }

    impl<'tcx> Visitor<'tcx> for OwningCallResultVisitor<'_, 'tcx> {
        fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
            if let hir::StmtKind::Let(let_stmt) = stmt.kind
                && let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind
                && let Some(init) = let_stmt.init
            {
                self.normalize_binding(hir_id, init);
            }
            intravisit::walk_stmt(self, stmt);
        }

        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = lhs.kind
                && let Res::Local(hir_id) = path.res
            {
                self.normalize_binding(hir_id, rhs);
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let crate_hir = tcx.hir_crate(());
    for maybe_owner in crate_hir.owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let hir::OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            continue;
        };
        let body = tcx.hir_body(body);
        let mut visitor = OwningCallResultVisitor {
            tcx,
            sig_decs,
            ptr_kinds,
            forced_raw_bindings,
        };
        visitor.visit_body(body);
    }
}

#[derive(Default)]
struct LocalStructDowngradeResult {
    changed: bool,
    call_conflict: FxHashSet<HirId>,
    call_binding_conflict: FxHashSet<HirId>,
    field_borrow_conflict: FxHashSet<HirId>,
    reborrow_assignment: FxHashSet<HirId>,
    field_mut_ptr: FxHashSet<HirId>,
    static_projection: FxHashSet<HirId>,
    foreign_mut_call: FxHashSet<HirId>,
}

impl LocalStructDowngradeResult {
    fn extend_forced_raw_bindings(&self, forced_raw_bindings: &mut FxHashSet<HirId>) {
        forced_raw_bindings.extend(self.call_conflict.iter().copied());
        forced_raw_bindings.extend(self.call_binding_conflict.iter().copied());
        forced_raw_bindings.extend(self.field_borrow_conflict.iter().copied());
        forced_raw_bindings.extend(self.reborrow_assignment.iter().copied());
        forced_raw_bindings.extend(self.field_mut_ptr.iter().copied());
        forced_raw_bindings.extend(self.static_projection.iter().copied());
        forced_raw_bindings.extend(self.foreign_mut_call.iter().copied());
    }
}

struct LocalStructDowngradeFacts {
    bodies: Vec<LocalStructBodyFacts>,
}

struct LocalStructBodyFacts {
    body_local_counts: FxHashMap<HirId, usize>,
    body_field_projection_counts: FxHashMap<(HirId, Symbol), usize>,
    calls: Vec<LocalStructCallFact>,
    lets: Vec<LocalStructLetFact>,
    reborrow_assignments: Vec<LocalStructReborrowAssignmentFact>,
    field_mut_ptrs: Vec<LocalStructFieldMutPtrFact>,
    static_projection_events: Vec<LocalStructStaticProjectionFact>,
}

impl LocalStructBodyFacts {
    fn new() -> Self {
        Self {
            body_local_counts: FxHashMap::default(),
            body_field_projection_counts: FxHashMap::default(),
            calls: Vec::new(),
            lets: Vec::new(),
            reborrow_assignments: Vec::new(),
            field_mut_ptrs: Vec::new(),
            static_projection_events: Vec::new(),
        }
    }
}

struct LocalStructCallFact {
    callee_did: Option<LocalDefId>,
    arg_local_ids: Vec<FxHashSet<HirId>>,
    arg_non_field_local_ids: Vec<FxHashSet<HirId>>,
    arg_field_projection_uses: Vec<Vec<(HirId, Symbol)>>,
    arg_whole_local_struct_roots: Vec<Option<HirId>>,
    arg_points_to_any: Vec<bool>,
    arg_points_to_mutable: Vec<bool>,
}

struct LocalStructLetFact {
    binding_hir_id: HirId,
    init_points_to_mutable: bool,
    init_local_counts: FxHashMap<HirId, usize>,
    init_field_projection_counts: FxHashMap<(HirId, Symbol), usize>,
    init_array_field_ptr_alias: Option<(HirId, Symbol)>,
    init_non_raw_field_projection_roots: FxHashSet<HirId>,
}

struct LocalStructReborrowAssignmentFact {
    lhs_hir_id: Option<HirId>,
    rhs_whole_root: Option<HirId>,
}

struct LocalStructFieldMutPtrFact {
    expr_hir_id: HirId,
    receiver_local_ids: Vec<HirId>,
    receiver_field_projection_roots: FxHashSet<HirId>,
}

struct LocalStructStaticProjectionFact {
    binding_hir_id: HirId,
    uses_mut_local_struct_static: bool,
}

fn downgrade_local_struct_bindings<'tcx>(
    tcx: TyCtxt<'tcx>,
    sig_decs: &mut SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
) -> LocalStructDowngradeResult {
    let facts = collect_local_struct_downgrade_facts(tcx);
    let mut result = LocalStructDowngradeResult::default();

    let (changed, bindings) =
        downgrade_conflicting_local_struct_call_inputs(tcx, &facts, sig_decs, ptr_kinds);
    result.changed |= changed;
    result.call_conflict = bindings;

    let (changed, bindings) =
        downgrade_conflicting_local_struct_call_bindings(tcx, &facts, sig_decs, ptr_kinds);
    result.changed |= changed;
    result.call_binding_conflict = bindings;

    let (changed, bindings) =
        downgrade_long_lived_local_struct_field_borrow_bindings(tcx, &facts, sig_decs, ptr_kinds);
    result.changed |= changed;
    result.field_borrow_conflict = bindings;

    let (changed, bindings) =
        downgrade_local_struct_reborrow_assignment_bindings(tcx, &facts, sig_decs, ptr_kinds);
    result.changed |= changed;
    result.reborrow_assignment = bindings;

    let (changed, bindings) =
        downgrade_local_struct_field_mut_ptr_bindings(tcx, &facts, sig_decs, ptr_kinds);
    result.changed |= changed;
    result.field_mut_ptr = bindings;

    let (changed, bindings) =
        downgrade_static_local_struct_projection_bindings(tcx, &facts, sig_decs, ptr_kinds);
    result.changed |= changed;
    result.static_projection = bindings;

    let (changed, bindings) =
        downgrade_foreign_mutable_local_struct_call_bindings(tcx, &facts, sig_decs, ptr_kinds);
    result.changed |= changed;
    result.foreign_mut_call = bindings;

    result
}

fn collect_local_struct_downgrade_facts<'tcx>(tcx: TyCtxt<'tcx>) -> LocalStructDowngradeFacts {
    struct FactVisitor<'tcx> {
        tcx: TyCtxt<'tcx>,
        typeck: &'tcx rustc_middle::ty::TypeckResults<'tcx>,
        body: LocalStructBodyFacts,
    }

    impl<'tcx> FactVisitor<'tcx> {
        fn visit_call_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
            let expr = hir_unwrap_casts(expr);
            let hir::ExprKind::Call(_, args) = expr.kind else {
                return;
            };
            let arg_local_ids = args
                .iter()
                .map(|arg| {
                    hir_local_ids_in_expr(arg)
                        .into_iter()
                        .collect::<FxHashSet<_>>()
                })
                .collect();
            let arg_non_field_local_ids = args
                .iter()
                .map(|arg| {
                    hir_local_ids_outside_top_level_field_projections(arg)
                        .into_iter()
                        .collect::<FxHashSet<_>>()
                })
                .collect();
            let arg_field_projection_uses = args
                .iter()
                .map(|arg| hir_top_level_field_projection_uses_in_expr(arg))
                .collect();
            let arg_whole_local_struct_roots = args
                .iter()
                .map(|arg| hir_whole_ptr_root_for_local_struct_arg(self.tcx, self.typeck, arg))
                .collect();
            let arg_points_to_any = args
                .iter()
                .map(|arg| ty_points_to_any(self.tcx, self.typeck.expr_ty_adjusted(arg)))
                .collect();
            let arg_points_to_mutable = args
                .iter()
                .map(|arg| ty_points_to_mutable(self.tcx, self.typeck.expr_ty_adjusted(arg)))
                .collect();

            self.body.calls.push(LocalStructCallFact {
                callee_did: hir_called_local_fn(self.tcx, expr),
                arg_local_ids,
                arg_non_field_local_ids,
                arg_field_projection_uses,
                arg_whole_local_struct_roots,
                arg_points_to_any,
                arg_points_to_mutable,
            });
        }

        fn visit_let_stmt(&mut self, let_stmt: &'tcx hir::LetStmt<'tcx>) {
            let hir::PatKind::Binding(_, binding_hir_id, _, _) = let_stmt.pat.kind else {
                return;
            };
            let Some(init) = let_stmt.init else {
                return;
            };
            self.body.lets.push(LocalStructLetFact {
                binding_hir_id,
                init_points_to_mutable: ty_points_to_mutable(
                    self.tcx,
                    self.typeck.expr_ty_adjusted(init),
                ),
                init_local_counts: hir_local_id_counts_in_expr(init),
                init_field_projection_counts: hir_field_projection_counts_in_expr(init),
                init_array_field_ptr_alias: hir_array_field_ptr_alias(self.typeck, init),
                init_non_raw_field_projection_roots: hir_non_raw_field_projection_roots_in_expr(
                    self.typeck,
                    init,
                ),
            });
            self.body
                .static_projection_events
                .push(LocalStructStaticProjectionFact {
                    binding_hir_id,
                    uses_mut_local_struct_static: hir_expr_uses_mut_local_struct_static(
                        self.tcx, init,
                    ),
                });
        }

        fn visit_assignment(&mut self, lhs: &'tcx hir::Expr<'tcx>, rhs: &'tcx hir::Expr<'tcx>) {
            self.body
                .reborrow_assignments
                .push(LocalStructReborrowAssignmentFact {
                    lhs_hir_id: hir_unwrapped_local_id(lhs),
                    rhs_whole_root: hir_whole_ptr_root(rhs),
                });
            if let Some(binding_hir_id) = hir_unwrapped_local_id(lhs) {
                self.body
                    .static_projection_events
                    .push(LocalStructStaticProjectionFact {
                        binding_hir_id,
                        uses_mut_local_struct_static: hir_expr_uses_mut_local_struct_static(
                            self.tcx, rhs,
                        ),
                    });
            }
        }

        fn visit_method_call(&mut self, expr: &'tcx hir::Expr<'tcx>) {
            let hir::ExprKind::MethodCall(seg, receiver, args, _) = expr.kind else {
                return;
            };
            match seg.ident.name.as_str() {
                "as_mut_ptr" if args.is_empty() => {
                    self.body.field_mut_ptrs.push(LocalStructFieldMutPtrFact {
                        expr_hir_id: expr.hir_id,
                        receiver_local_ids: hir_local_ids_in_expr(receiver),
                        receiver_field_projection_roots: hir_field_projection_roots_in_expr(
                            receiver,
                        ),
                    });
                }
                _ => {}
            }
        }
    }

    impl<'tcx> Visitor<'tcx> for FactVisitor<'tcx> {
        fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
            if let hir::StmtKind::Let(let_stmt) = stmt.kind {
                self.visit_let_stmt(let_stmt);
            }
            intravisit::walk_stmt(self, stmt);
        }

        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let Some(hir_id) = hir_unwrapped_local_id(expr) {
                *self.body.body_local_counts.entry(hir_id).or_default() += 1;
            }
            if let Some(field_use) = hir_top_level_field_projection_use(expr) {
                *self
                    .body
                    .body_field_projection_counts
                    .entry(field_use)
                    .or_default() += 1;
            }
            self.visit_call_expr(expr);
            if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind {
                self.visit_assignment(lhs, rhs);
            }
            self.visit_method_call(expr);
            intravisit::walk_expr(self, expr);
        }
    }

    let mut facts = LocalStructDowngradeFacts { bodies: Vec::new() };
    let crate_hir = tcx.hir_crate(());
    for maybe_owner in crate_hir.owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let hir::OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        let hir::ItemKind::Fn { body: body_id, .. } = item.kind else {
            continue;
        };
        let body = tcx.hir_body(body_id);
        let typeck = tcx.typeck_body(body_id);
        let mut visitor = FactVisitor {
            tcx,
            typeck,
            body: LocalStructBodyFacts::new(),
        };
        visitor.visit_body(body);
        facts.bodies.push(visitor.body);
    }
    facts
}

fn downgrade_conflicting_local_struct_call_inputs<'tcx>(
    tcx: TyCtxt<'tcx>,
    facts: &LocalStructDowngradeFacts,
    sig_decs: &mut SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
) -> (bool, FxHashSet<HirId>) {
    let mut changed = false;
    let mut bindings = FxHashSet::default();
    for body in &facts.bodies {
        for call in &body.calls {
            let Some(callee_did) = call.callee_did else {
                continue;
            };
            let conflicting_inputs = {
                let Some(sig_dec) = sig_decs.data.get(&callee_did) else {
                    continue;
                };
                if sig_dec.signature_locked {
                    continue;
                }
                let mut conflicting_inputs = Vec::new();
                for (idx, root) in call.arg_whole_local_struct_roots.iter().enumerate() {
                    let Some(kind) = sig_dec.input_decs.get(idx).copied().flatten() else {
                        continue;
                    };
                    if !is_borrow_like_decision(kind) {
                        continue;
                    }
                    let Some(root) = *root else {
                        continue;
                    };
                    if matches!(ptr_kinds.get(&root), Some(PtrKind::Raw(_))) {
                        continue;
                    }
                    if param_index_for_binding(tcx, root).is_some()
                        && call_other_root_uses_are_field_pointer_args(call, root, idx)
                    {
                        continue;
                    }
                    if !call
                        .arg_local_ids
                        .iter()
                        .enumerate()
                        .any(|(other_idx, locals)| {
                            other_idx != idx
                                && locals.contains(&root)
                                && (kind.is_mut()
                                    || arg_may_mutably_borrow(
                                        call.arg_points_to_mutable[other_idx],
                                        sig_dec.input_decs.get(other_idx).copied().flatten(),
                                    ))
                        })
                    {
                        continue;
                    }
                    let Some(param_hir_id) = callee_input_param_binding(tcx, callee_did, idx)
                    else {
                        continue;
                    };
                    conflicting_inputs.push((idx, param_hir_id));
                }
                conflicting_inputs
            };

            if conflicting_inputs.is_empty() {
                continue;
            }

            let Some(sig_dec) = sig_decs.data.get_mut(&callee_did) else {
                continue;
            };
            for (idx, param_hir_id) in conflicting_inputs {
                if !sig_dec
                    .input_decs
                    .get(idx)
                    .copied()
                    .flatten()
                    .is_some_and(is_borrow_like_decision)
                {
                    continue;
                }
                sig_dec.set_input_dec(idx, Some(PtrKind::Raw(true)));
                bindings.insert(param_hir_id);
                changed = true;
            }
        }
    }
    (changed, bindings)
}

fn downgrade_conflicting_local_struct_call_bindings<'tcx>(
    tcx: TyCtxt<'tcx>,
    facts: &LocalStructDowngradeFacts,
    sig_decs: &mut SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
) -> (bool, FxHashSet<HirId>) {
    let mut changed = false;
    let mut bindings = FxHashSet::default();
    for body in &facts.bodies {
        for call in &body.calls {
            let conflicting_roots = {
                let callee_sig_dec = call.callee_did.and_then(|did| sig_decs.data.get(&did));
                let mut roots = FxHashSet::default();
                for locals in &call.arg_local_ids {
                    roots.extend(locals.iter().copied());
                }

                let mut conflicting_roots = Vec::new();
                for root in roots {
                    let Some(kind) = ptr_kinds.get(&root).copied() else {
                        continue;
                    };
                    if !is_borrow_like_decision(kind) {
                        continue;
                    }
                    let root_ty = tcx.typeck(root.owner).node_type(root);
                    if !ty_points_to_local_struct(tcx, root_ty) {
                        continue;
                    }

                    let mut use_count = 0usize;
                    let mut has_mutable_arg = false;
                    for (idx, locals) in call.arg_local_ids.iter().enumerate() {
                        if !locals.contains(&root) {
                            continue;
                        }
                        use_count += 1;
                        let input_dec = callee_sig_dec
                            .and_then(|sig_dec| sig_dec.input_decs.get(idx).copied().flatten());
                        if arg_may_mutably_borrow(call.arg_points_to_mutable[idx], input_dec) {
                            has_mutable_arg = true;
                        }
                    }
                    if use_count > 1
                        && has_mutable_arg
                        && !call_uses_root_only_through_disjoint_field_args(
                            call,
                            root,
                            callee_sig_dec,
                        )
                    {
                        conflicting_roots.push(root);
                    }
                }
                conflicting_roots
            };

            for root in conflicting_roots {
                if !force_signature_input_raw_for_binding(tcx, sig_decs, root) {
                    continue;
                }
                bindings.insert(root);
                changed = true;
            }
        }
    }
    (changed, bindings)
}

fn downgrade_long_lived_local_struct_field_borrow_bindings<'tcx>(
    tcx: TyCtxt<'tcx>,
    facts: &LocalStructDowngradeFacts,
    sig_decs: &mut SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
) -> (bool, FxHashSet<HirId>) {
    let mut changed = false;
    let mut bindings = FxHashSet::default();
    for body in &facts.bodies {
        for let_fact in &body.lets {
            let Some(binding_kind) = ptr_kinds.get(&let_fact.binding_hir_id).copied() else {
                continue;
            };
            if !is_mutable_borrow_like_decision(binding_kind) || !let_fact.init_points_to_mutable {
                continue;
            }

            for (root, init_count) in &let_fact.init_local_counts {
                if !local_struct_borrow_binding(tcx, ptr_kinds, *root) {
                    continue;
                }
                if !let_fact.init_non_raw_field_projection_roots.contains(root) {
                    continue;
                }
                if body.body_local_counts.get(root).copied().unwrap_or(0) <= *init_count {
                    continue;
                }
                if long_lived_borrow_uses_only_disjoint_array_fields(
                    body,
                    let_fact,
                    *root,
                    *init_count,
                ) {
                    continue;
                }
                if !force_signature_input_raw_for_binding(tcx, sig_decs, let_fact.binding_hir_id) {
                    continue;
                }
                bindings.insert(let_fact.binding_hir_id);
                changed = true;
            }
        }
    }
    (changed, bindings)
}

fn long_lived_borrow_uses_only_disjoint_array_fields(
    body: &LocalStructBodyFacts,
    let_fact: &LocalStructLetFact,
    root: HirId,
    init_count: usize,
) -> bool {
    let Some((alias_root, alias_field)) = let_fact.init_array_field_ptr_alias else {
        return false;
    };
    if alias_root != root {
        return false;
    }

    let root_uses = body.body_local_counts.get(&root).copied().unwrap_or(0);
    let Some(extra_root_uses) = root_uses.checked_sub(init_count) else {
        return false;
    };
    if extra_root_uses == 0 {
        return true;
    }

    let init_alias_field_uses = let_fact
        .init_field_projection_counts
        .get(&(root, alias_field))
        .copied()
        .unwrap_or(0);
    let body_alias_field_uses = body
        .body_field_projection_counts
        .get(&(root, alias_field))
        .copied()
        .unwrap_or(0);
    if body_alias_field_uses > init_alias_field_uses {
        return false;
    }

    let disjoint_field_uses = body
        .body_field_projection_counts
        .iter()
        .filter(|((field_root, field), _)| *field_root == root && *field != alias_field)
        .map(|(_, count)| *count)
        .sum::<usize>();
    disjoint_field_uses == extra_root_uses
}

fn downgrade_local_struct_reborrow_assignment_bindings<'tcx>(
    tcx: TyCtxt<'tcx>,
    facts: &LocalStructDowngradeFacts,
    sig_decs: &mut SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
) -> (bool, FxHashSet<HirId>) {
    fn force_raw(
        tcx: TyCtxt<'_>,
        sig_decs: &mut SigDecisions,
        bindings: &mut FxHashSet<HirId>,
        hir_id: HirId,
    ) -> bool {
        if !force_signature_input_raw_for_binding(tcx, sig_decs, hir_id) {
            return false;
        }
        bindings.insert(hir_id);
        true
    }

    let mut changed = false;
    let mut bindings = FxHashSet::default();
    for body in &facts.bodies {
        for assignment in &body.reborrow_assignments {
            let Some(lhs_hir_id) = assignment.lhs_hir_id else {
                continue;
            };
            let Some(rhs_hir_id) = assignment.rhs_whole_root else {
                continue;
            };
            if lhs_hir_id == rhs_hir_id
                || !local_struct_borrow_binding(tcx, ptr_kinds, lhs_hir_id)
                || !local_struct_borrow_binding(tcx, ptr_kinds, rhs_hir_id)
            {
                continue;
            }
            changed |= force_raw(tcx, sig_decs, &mut bindings, lhs_hir_id);
            changed |= force_raw(tcx, sig_decs, &mut bindings, rhs_hir_id);
        }
    }
    (changed, bindings)
}

fn downgrade_local_struct_field_mut_ptr_bindings<'tcx>(
    tcx: TyCtxt<'tcx>,
    facts: &LocalStructDowngradeFacts,
    sig_decs: &mut SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
) -> (bool, FxHashSet<HirId>) {
    let mut changed = false;
    let mut bindings = FxHashSet::default();
    for body in &facts.bodies {
        for field_mut_ptr in &body.field_mut_ptrs {
            for root in &field_mut_ptr.receiver_local_ids {
                let Some(root_kind) = ptr_kinds.get(root).copied() else {
                    continue;
                };
                if !field_mut_ptr.receiver_field_projection_roots.contains(root)
                    || !local_struct_borrow_binding(tcx, ptr_kinds, *root)
                    || is_mutable_borrow_like_decision(root_kind)
                    || !local_struct_field_mut_ptr_consumer_requires_raw(
                        tcx,
                        sig_decs,
                        ptr_kinds,
                        field_mut_ptr.expr_hir_id,
                    )
                    || !force_signature_input_raw_for_binding(tcx, sig_decs, *root)
                {
                    continue;
                }
                bindings.insert(*root);
                changed = true;
            }
        }
    }
    (changed, bindings)
}

fn local_struct_field_mut_ptr_consumer_requires_raw(
    tcx: TyCtxt<'_>,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    expr_hir_id: HirId,
) -> bool {
    let local_consumer_requires_raw = |hir_id: HirId| {
        ptr_kinds
            .get(&hir_id)
            .copied()
            .map(consumer_kind_requires_raw)
            .unwrap_or_else(|| {
                consumer_ty_requires_raw(tcx, tcx.typeck(hir_id.owner).node_type(hir_id))
            })
    };

    let mut curr_id = expr_hir_id;
    for (parent_id, parent_node) in tcx.hir_parent_iter(expr_hir_id) {
        match parent_node {
            hir::Node::Expr(parent) => match parent.kind {
                hir::ExprKind::DropTemps(_)
                | hir::ExprKind::Cast(_, _)
                | hir::ExprKind::Unary(hir::UnOp::Deref, _)
                | hir::ExprKind::AddrOf(_, _, _) => {}
                hir::ExprKind::MethodCall(seg, receiver, args, _) if curr_id == receiver.hir_id => {
                    match seg.ident.name.as_str() {
                        "offset" | "add" => {
                            if args.is_empty() {
                                return true;
                            }
                        }
                        "sub" | "wrapping_offset" | "wrapping_add" | "wrapping_sub" => {
                            return true;
                        }
                        _ => return true,
                    }
                }
                hir::ExprKind::Block(block, _)
                    if block.expr.is_some_and(|expr| expr.hir_id == curr_id) => {}
                hir::ExprKind::Call(_, args) => {
                    let Some(arg_idx) = args.iter().position(|arg| arg.hir_id == curr_id) else {
                        return true;
                    };
                    if let Some(callee_did) = hir_called_local_fn(tcx, parent)
                        && let Some(kind) = sig_decs
                            .data
                            .get(&callee_did)
                            .and_then(|sig_dec| sig_dec.input_decs.get(arg_idx).copied().flatten())
                    {
                        return consumer_kind_requires_raw(kind);
                    }
                    let typeck = tcx.typeck(parent.hir_id.owner);
                    return consumer_ty_requires_raw(tcx, typeck.expr_ty_adjusted(&args[arg_idx]));
                }
                hir::ExprKind::Assign(lhs, rhs, _) if rhs.hir_id == curr_id => {
                    return hir_unwrapped_local_id(lhs)
                        .map(local_consumer_requires_raw)
                        .unwrap_or(true);
                }
                hir::ExprKind::Ret(Some(ret)) if ret.hir_id == curr_id => {
                    let did = parent.hir_id.owner.def_id;
                    if let Some(kind) = sig_decs.data.get(&did).and_then(|sig| sig.output_dec) {
                        return consumer_kind_requires_raw(kind);
                    }
                    let output = tcx.fn_sig(did).skip_binder().skip_binder().output();
                    return consumer_ty_requires_raw(tcx, output);
                }
                _ => return true,
            },
            hir::Node::LetStmt(let_stmt)
                if let_stmt.init.is_some_and(|init| init.hir_id == curr_id) =>
            {
                let hir::PatKind::Binding(_, binding_hir_id, _, _) = let_stmt.pat.kind else {
                    return true;
                };
                return local_consumer_requires_raw(binding_hir_id);
            }
            hir::Node::Stmt(_) => {}
            _ => return true,
        }
        curr_id = parent_id;
    }
    true
}

fn consumer_kind_requires_raw(kind: PtrKind) -> bool {
    match kind {
        PtrKind::Ref(m)
        | PtrKind::OptRef(m)
        | PtrKind::Raw(m)
        | PtrKind::Slice(m)
        | PtrKind::SliceCursor(m) => m,
        PtrKind::Box | PtrKind::OptBox | PtrKind::BoxedSlice | PtrKind::OptBoxedSlice => true,
    }
}

fn consumer_ty_requires_raw<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> bool {
    if ty_points_to_any(tcx, ty) {
        ty_points_to_mutable(tcx, ty)
    } else {
        true
    }
}

fn downgrade_static_local_struct_projection_bindings<'tcx>(
    tcx: TyCtxt<'tcx>,
    facts: &LocalStructDowngradeFacts,
    sig_decs: &mut SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
) -> (bool, FxHashSet<HirId>) {
    let mut changed = false;
    let mut bindings = FxHashSet::default();
    for body in &facts.bodies {
        for event in &body.static_projection_events {
            if !local_struct_borrow_binding(tcx, ptr_kinds, event.binding_hir_id)
                || !event.uses_mut_local_struct_static
                || !force_signature_input_raw_for_binding(tcx, sig_decs, event.binding_hir_id)
            {
                continue;
            }
            bindings.insert(event.binding_hir_id);
            changed = true;
        }
    }
    (changed, bindings)
}

fn downgrade_foreign_mutable_local_struct_call_bindings<'tcx>(
    tcx: TyCtxt<'tcx>,
    facts: &LocalStructDowngradeFacts,
    sig_decs: &mut SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
) -> (bool, FxHashSet<HirId>) {
    let mut changed = false;
    let mut bindings = FxHashSet::default();
    for body in &facts.bodies {
        for call in &body.calls {
            if call.callee_did.is_some() {
                continue;
            }
            for (idx, root) in call.arg_whole_local_struct_roots.iter().enumerate() {
                if !call.arg_points_to_mutable[idx] {
                    continue;
                }
                let Some(root) = *root else {
                    continue;
                };
                if !local_struct_borrow_binding(tcx, ptr_kinds, root)
                    || !force_signature_input_raw_for_binding(tcx, sig_decs, root)
                {
                    continue;
                }
                bindings.insert(root);
                changed = true;
            }
        }
    }
    (changed, bindings)
}

fn is_borrow_like_decision(kind: PtrKind) -> bool {
    matches!(
        kind,
        PtrKind::Ref(_) | PtrKind::OptRef(_) | PtrKind::Slice(_) | PtrKind::SliceCursor(_)
    )
}

fn local_callee_arg_preserves_owning_usage(
    sig_decs: &SigDecisions,
    local_raw_param_summaries: &FxHashMap<(LocalDefId, usize), LocalRawParamSummary>,
    callee: LocalDefId,
    arg_index: usize,
) -> bool {
    if let Some(summary) = local_raw_param_summaries.get(&(callee, arg_index)).copied() {
        return summary.preserves_owning_call_boundary();
    }
    sig_decs
        .data
        .get(&callee)
        .and_then(|sig_dec| sig_dec.input_decs.get(arg_index).copied().flatten())
        .is_some_and(is_borrow_like_decision)
}

fn is_mutable_borrow_like_decision(kind: PtrKind) -> bool {
    matches!(
        kind,
        PtrKind::Ref(true)
            | PtrKind::OptRef(true)
            | PtrKind::Slice(true)
            | PtrKind::SliceCursor(true)
    )
}

fn is_borrow_bridgeable_source_decision(kind: PtrKind) -> bool {
    matches!(kind, PtrKind::Raw(_)) || is_borrow_like_decision(kind)
}

fn arg_may_mutably_borrow(arg_points_to_mutable: bool, decision: Option<PtrKind>) -> bool {
    decision.is_some_and(is_mutable_borrow_like_decision) || arg_points_to_mutable
}

fn call_other_root_uses_are_field_pointer_args(
    call: &LocalStructCallFact,
    root: HirId,
    whole_root_arg_idx: usize,
) -> bool {
    let mut found = false;
    for (idx, locals) in call.arg_local_ids.iter().enumerate() {
        if idx == whole_root_arg_idx || !locals.contains(&root) {
            continue;
        }
        if !call.arg_points_to_any[idx] || call.arg_non_field_local_ids[idx].contains(&root) {
            return false;
        }
        if !call.arg_field_projection_uses[idx]
            .iter()
            .any(|(field_root, _)| *field_root == root)
        {
            return false;
        }
        found = true;
    }
    found
}

fn call_uses_root_only_through_disjoint_field_args(
    call: &LocalStructCallFact,
    root: HirId,
    callee_sig_dec: Option<&SigDecision>,
) -> bool {
    let mut fields = FxHashSet::default();
    let mut found = false;
    let mut has_mutable_borrow_like_arg = false;
    let mut has_shared_borrow_like_arg = false;
    for (idx, locals) in call.arg_local_ids.iter().enumerate() {
        if !locals.contains(&root) {
            continue;
        }
        if !call.arg_points_to_any[idx] || call.arg_non_field_local_ids[idx].contains(&root) {
            return false;
        }

        let mut arg_has_field = false;
        for (field_root, field) in &call.arg_field_projection_uses[idx] {
            if *field_root != root {
                continue;
            }
            arg_has_field = true;
            if !fields.insert(*field) {
                return false;
            }
        }
        if !arg_has_field {
            return false;
        }
        let input_dec =
            callee_sig_dec.and_then(|sig_dec| sig_dec.input_decs.get(idx).copied().flatten());
        if input_dec.is_some_and(is_mutable_borrow_like_decision) {
            has_mutable_borrow_like_arg = true;
        } else if input_dec.is_some_and(is_borrow_like_decision) {
            has_shared_borrow_like_arg = true;
        }
        found = true;
    }
    found && !(has_mutable_borrow_like_arg && has_shared_borrow_like_arg)
}

fn callee_input_param_binding(tcx: TyCtxt<'_>, did: LocalDefId, idx: usize) -> Option<HirId> {
    let hir::Node::Item(item) = tcx.hir_node_by_def_id(did) else {
        return None;
    };
    let hir::ItemKind::Fn { body, .. } = item.kind else {
        return None;
    };
    let body = tcx.hir_body(body);
    let param = body.params.get(idx)?;
    let hir::PatKind::Binding(_, hir_id, _, _) = param.pat.kind else {
        return None;
    };
    Some(hir_id)
}

fn force_signature_input_raw_for_binding(
    tcx: TyCtxt<'_>,
    sig_decs: &mut SigDecisions,
    hir_id: HirId,
) -> bool {
    let Some((did, idx)) = param_index_for_binding(tcx, hir_id) else {
        return true;
    };
    let Some(sig_dec) = sig_decs.data.get_mut(&did) else {
        return false;
    };
    if sig_dec.signature_locked {
        return false;
    }
    let raw_mut = unwrap_ptr_from_mir_ty(tcx.typeck(hir_id.owner).node_type(hir_id))
        .map(|(_, mutability)| mutability.is_mut())
        .unwrap_or(true);
    let decision = match sig_dec.input_decs.get(idx).copied().flatten() {
        Some(raw @ PtrKind::Raw(_)) => Some(raw),
        _ => Some(PtrKind::Raw(raw_mut)),
    };
    if sig_dec.input_decs.get(idx).copied().flatten() == decision {
        return false;
    }
    sig_dec.set_input_dec(idx, decision);
    true
}

fn force_signature_input_mut_for_binding(
    tcx: TyCtxt<'_>,
    sig_decs: &mut SigDecisions,
    hir_id: HirId,
) -> bool {
    let Some((did, idx)) = param_index_for_binding(tcx, hir_id) else {
        return false;
    };
    let Some(sig_dec) = sig_decs.data.get_mut(&did) else {
        return false;
    };
    if sig_dec.signature_locked {
        return false;
    }
    let decision = match sig_dec.input_decs.get(idx).copied().flatten() {
        Some(PtrKind::Ref(false)) => Some(PtrKind::Ref(true)),
        Some(PtrKind::OptRef(false)) => Some(PtrKind::OptRef(true)),
        Some(PtrKind::Raw(false)) => Some(PtrKind::Raw(true)),
        _ => return false,
    };
    sig_dec.set_input_dec(idx, decision);
    true
}

fn force_signature_output_raw(
    tcx: TyCtxt<'_>,
    sig_decs: &mut SigDecisions,
    did: LocalDefId,
) -> bool {
    let Some(sig_dec) = sig_decs.data.get_mut(&did) else {
        return false;
    };
    if sig_dec.signature_locked {
        return false;
    }
    let output_mut = sig_dec
        .output_dec
        .map(|kind| kind.is_mut())
        .or_else(|| {
            let sig = tcx.fn_sig(did).skip_binder().skip_binder();
            let ty::TyKind::RawPtr(_, mutability) = sig.output().kind() else {
                return None;
            };
            Some(mutability.is_mut())
        })
        .unwrap_or(true);
    sig_dec.set_output_dec(Some(PtrKind::Raw(output_mut)));
    true
}

fn param_index_for_binding(tcx: TyCtxt<'_>, hir_id: HirId) -> Option<(LocalDefId, usize)> {
    let did = hir_id.owner.def_id;
    let hir::Node::Item(item) = tcx.hir_node_by_def_id(did) else {
        return None;
    };
    let hir::ItemKind::Fn { body, .. } = item.kind else {
        return None;
    };
    let body = tcx.hir_body(body);
    body.params
        .iter()
        .enumerate()
        .find_map(|(idx, param)| match param.pat.kind {
            hir::PatKind::Binding(_, param_hir_id, _, _) if param_hir_id == hir_id => {
                Some((did, idx))
            }
            _ => None,
        })
}

fn record_binding_events(
    diagnostics: &mut DecisionDiagnostics,
    tcx: TyCtxt<'_>,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    bindings: &FxHashSet<HirId>,
    reason: DecisionReason,
) {
    for &hir_id in bindings {
        record_binding_event(diagnostics, tcx, ptr_kinds, hir_id, reason);
    }
}

fn record_binding_events_excluding(
    diagnostics: &mut DecisionDiagnostics,
    tcx: TyCtxt<'_>,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    bindings: &FxHashSet<HirId>,
    existing: &FxHashSet<HirId>,
    reason: DecisionReason,
) {
    for &hir_id in bindings {
        if !existing.contains(&hir_id) {
            record_binding_event(diagnostics, tcx, ptr_kinds, hir_id, reason);
        }
    }
}

fn record_binding_event(
    diagnostics: &mut DecisionDiagnostics,
    tcx: TyCtxt<'_>,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    hir_id: HirId,
    reason: DecisionReason,
) {
    if !diagnostics.is_enabled() {
        return;
    }
    let Some(subject) = subject_for_binding(tcx, hir_id) else {
        return;
    };
    let before = ptr_kinds.get(&hir_id).copied();
    let after = raw_kind_for_hir_id(tcx, hir_id).or(before);
    diagnostics.record(
        subject,
        DecisionStage::Downgrade,
        before,
        after,
        reason,
        None,
    );
}

fn record_signature_input_event(
    diagnostics: &mut DecisionDiagnostics,
    tcx: TyCtxt<'_>,
    sig_decs: &SigDecisions,
    did: LocalDefId,
    idx: usize,
    reason: DecisionReason,
) {
    if !diagnostics.is_enabled() {
        return;
    }
    let Some(sig_dec) = sig_decs.data.get(&did) else {
        return;
    };
    let Some(after) = sig_dec.input_decs.get(idx).copied().flatten() else {
        return;
    };
    let Some(hir_id) = callee_input_param_binding(tcx, did, idx) else {
        return;
    };
    diagnostics.record(
        DecisionSubject::Param {
            did,
            index: idx,
            hir_id,
            local: rustc_middle::mir::Local::from_usize(idx + 1),
        },
        DecisionStage::Downgrade,
        None,
        Some(after),
        reason,
        None,
    );
}

fn record_signature_output_event(
    diagnostics: &mut DecisionDiagnostics,
    _tcx: TyCtxt<'_>,
    sig_decs: &SigDecisions,
    did: LocalDefId,
    reason: DecisionReason,
) {
    if !diagnostics.is_enabled() {
        return;
    }
    let Some(after) = sig_decs
        .data
        .get(&did)
        .and_then(|sig_dec| sig_dec.output_dec)
    else {
        return;
    };
    diagnostics.record(
        DecisionSubject::Return { did },
        DecisionStage::Downgrade,
        None,
        Some(after),
        reason,
        None,
    );
}

fn subject_for_binding(tcx: TyCtxt<'_>, hir_id: HirId) -> Option<DecisionSubject> {
    if let Some((did, index)) = param_index_for_binding(tcx, hir_id) {
        return Some(DecisionSubject::Param {
            did,
            index,
            hir_id,
            local: rustc_middle::mir::Local::from_usize(index + 1),
        });
    }
    let did = hir_id.owner.def_id;
    let hir_to_mir = utils::ir::map_thir_to_mir(did, false, tcx);
    let local = hir_to_mir.binding_to_local.get(&hir_id).copied()?;
    Some(DecisionSubject::Local { did, hir_id, local })
}

fn raw_kind_for_hir_id(tcx: TyCtxt<'_>, hir_id: HirId) -> Option<PtrKind> {
    unwrap_ptr_from_mir_ty(tcx.typeck(hir_id.owner).node_type(hir_id))
        .map(|(_, mutability)| PtrKind::Raw(mutability.is_mut()))
}

fn hir_whole_ptr_root_for_local_struct_arg<'tcx>(
    tcx: TyCtxt<'tcx>,
    typeck: &rustc_middle::ty::TypeckResults<'tcx>,
    expr: &'tcx hir::Expr<'tcx>,
) -> Option<HirId> {
    ty_points_to_local_struct(tcx, typeck.expr_ty_adjusted(expr))
        .then(|| hir_whole_ptr_root(expr))
        .flatten()
}

fn ty_points_to_local_struct<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> bool {
    match ty.kind() {
        ty::TyKind::RawPtr(inner, _) | ty::TyKind::Ref(_, inner, _) => ty_is_local_struct(*inner),
        ty::TyKind::Adt(adt_def, args) if is_option(adt_def.did(), tcx) => {
            let ty::GenericArgKind::Type(inner) = args[0].kind() else {
                return false;
            };
            ty_points_to_local_struct(tcx, inner)
        }
        _ => false,
    }
}

fn local_struct_borrow_binding(
    tcx: TyCtxt<'_>,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    hir_id: HirId,
) -> bool {
    ptr_kinds
        .get(&hir_id)
        .copied()
        .is_some_and(is_borrow_like_decision)
        && ty_points_to_local_struct(tcx, tcx.typeck(hir_id.owner).node_type(hir_id))
}

fn ty_points_to_any<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> bool {
    match ty.kind() {
        ty::TyKind::RawPtr(..) | ty::TyKind::Ref(..) => true,
        ty::TyKind::Adt(adt_def, args) if is_option(adt_def.did(), tcx) => {
            let ty::GenericArgKind::Type(inner) = args[0].kind() else {
                return false;
            };
            ty_points_to_any(tcx, inner)
        }
        _ => false,
    }
}

fn ty_points_to_mutable(tcx: TyCtxt<'_>, ty: ty::Ty<'_>) -> bool {
    match ty.kind() {
        ty::TyKind::RawPtr(_, mutability) | ty::TyKind::Ref(_, _, mutability) => {
            mutability.is_mut()
        }
        ty::TyKind::Adt(adt_def, args) if is_option(adt_def.did(), tcx) => {
            let ty::GenericArgKind::Type(inner) = args[0].kind() else {
                return false;
            };
            ty_points_to_mutable(tcx, inner)
        }
        _ => false,
    }
}

fn ty_is_local_struct(ty: ty::Ty<'_>) -> bool {
    matches!(
        ty.kind(),
        ty::TyKind::Adt(adt_def, _) if adt_def.did().is_local() && adt_def.is_struct()
    )
}

fn ty_contains_local_struct(ty: ty::Ty<'_>) -> bool {
    match ty.kind() {
        ty::TyKind::RawPtr(inner, _) | ty::TyKind::Ref(_, inner, _) => {
            ty_contains_local_struct(*inner)
        }
        ty::TyKind::Array(inner, _) | ty::TyKind::Slice(inner) => ty_contains_local_struct(*inner),
        ty::TyKind::Adt(adt_def, args) => {
            adt_def.did().is_local() && adt_def.is_struct()
                || args.types().any(ty_contains_local_struct)
        }
        _ => false,
    }
}

fn hir_whole_ptr_root(expr: &hir::Expr<'_>) -> Option<HirId> {
    let expr = hir_unwrap_casts(expr);
    match expr.kind {
        hir::ExprKind::Path(hir::QPath::Resolved(_, path)) => {
            let Res::Local(hir_id) = path.res else {
                return None;
            };
            Some(hir_id)
        }
        hir::ExprKind::AddrOf(_, _, inner) | hir::ExprKind::Unary(hir::UnOp::Deref, inner) => {
            hir_whole_ptr_root(inner)
        }
        hir::ExprKind::MethodCall(seg, receiver, args, _)
            if args.is_empty()
                && matches!(
                    seg.ident.name.as_str(),
                    "as_deref_mut" | "as_deref" | "unwrap" | "unwrap_unchecked"
                ) =>
        {
            hir_whole_ptr_root(receiver)
        }
        hir::ExprKind::Call(callee, [arg]) if hir_path_name_is(callee, "Some") => {
            hir_whole_ptr_root(arg)
        }
        _ => None,
    }
}

fn hir_path_name_is(expr: &hir::Expr<'_>, name: &str) -> bool {
    let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_unwrap_casts(expr).kind else {
        return false;
    };
    path.segments
        .last()
        .is_some_and(|seg| seg.ident.name.as_str() == name)
}

fn hir_local_id_counts_in_expr(expr: &hir::Expr<'_>) -> FxHashMap<HirId, usize> {
    let mut counts = FxHashMap::default();
    for hir_id in hir_local_ids_in_expr(expr) {
        *counts.entry(hir_id).or_default() += 1;
    }
    counts
}

fn hir_top_level_field_projection_use(expr: &hir::Expr<'_>) -> Option<(HirId, Symbol)> {
    if let hir::ExprKind::Field(base, ident) = expr.kind
        && let Some(root) = hir_whole_ptr_root(base)
    {
        return Some((root, ident.name));
    }
    None
}

fn hir_field_projection_counts_in_expr(expr: &hir::Expr<'_>) -> FxHashMap<(HirId, Symbol), usize> {
    let mut counts = FxHashMap::default();
    for field_use in hir_top_level_field_projection_uses_in_expr(expr) {
        *counts.entry(field_use).or_default() += 1;
    }
    counts
}

fn hir_array_field_ptr_alias<'tcx>(
    typeck: &'tcx rustc_middle::ty::TypeckResults<'tcx>,
    expr: &'tcx hir::Expr<'tcx>,
) -> Option<(HirId, Symbol)> {
    let hir::ExprKind::MethodCall(seg, receiver, args, _) = hir_unwrap_casts(expr).kind else {
        return None;
    };
    if !args.is_empty() || !matches!(seg.ident.name.as_str(), "as_ptr" | "as_mut_ptr") {
        return None;
    }
    if !matches!(typeck.expr_ty(receiver).kind(), ty::TyKind::Array(..)) {
        return None;
    }
    let hir::ExprKind::Field(base, ident) = hir_unwrap_casts(receiver).kind else {
        return None;
    };
    Some((hir_whole_ptr_root(base)?, ident.name))
}

fn hir_field_projection_roots_in_expr(expr: &hir::Expr<'_>) -> FxHashSet<HirId> {
    struct FieldProjectionVisitor {
        roots: FxHashSet<HirId>,
    }

    impl<'tcx> Visitor<'tcx> for FieldProjectionVisitor {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let hir::ExprKind::Field(base, _) = expr.kind {
                self.roots.extend(hir_local_ids_in_expr(base));
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut visitor = FieldProjectionVisitor {
        roots: FxHashSet::default(),
    };
    visitor.visit_expr(expr);
    visitor.roots
}

fn hir_non_raw_field_projection_roots_in_expr<'tcx>(
    typeck: &'tcx rustc_middle::ty::TypeckResults<'tcx>,
    expr: &'tcx hir::Expr<'tcx>,
) -> FxHashSet<HirId> {
    struct FieldProjectionVisitor<'tcx> {
        typeck: &'tcx rustc_middle::ty::TypeckResults<'tcx>,
        roots: FxHashSet<HirId>,
    }

    impl<'tcx> Visitor<'tcx> for FieldProjectionVisitor<'tcx> {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let hir::ExprKind::Field(base, _) = expr.kind
                && !self.typeck.expr_ty_adjusted(expr).is_raw_ptr()
            {
                self.roots.extend(hir_local_ids_in_expr(base));
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut visitor = FieldProjectionVisitor {
        typeck,
        roots: FxHashSet::default(),
    };
    visitor.visit_expr(expr);
    visitor.roots
}

fn hir_expr_uses_mut_local_struct_static<'tcx>(
    tcx: TyCtxt<'tcx>,
    expr: &'tcx hir::Expr<'tcx>,
) -> bool {
    struct StaticVisitor<'tcx> {
        tcx: TyCtxt<'tcx>,
        found: bool,
    }

    impl<'tcx> StaticVisitor<'tcx> {
        fn is_mut_local_struct_static(&self, def_id: LocalDefId) -> bool {
            let hir::Node::Item(item) = self.tcx.hir_node_by_def_id(def_id) else {
                return false;
            };
            let hir::ItemKind::Static(mutability, _, _, _) = item.kind else {
                return false;
            };
            mutability.is_mut()
                && ty_contains_local_struct(self.tcx.type_of(def_id).instantiate_identity())
        }
    }

    impl<'tcx> Visitor<'tcx> for StaticVisitor<'tcx> {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if self.found {
                return;
            }
            if let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_unwrap_casts(expr).kind
                && let Res::Def(DefKind::Static { .. }, def_id) = path.res
                && let Some(local_def_id) = def_id.as_local()
                && self.is_mut_local_struct_static(local_def_id)
            {
                self.found = true;
                return;
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut visitor = StaticVisitor { tcx, found: false };
    visitor.visit_expr(expr);
    visitor.found
}

fn downgrade_unsupported_box_inputs(
    tcx: TyCtxt<'_>,
    sig_decs: &mut SigDecisions,
    local_raw_param_summaries: &FxHashMap<(LocalDefId, usize), LocalRawParamSummary>,
) -> (bool, FxHashSet<HirId>) {
    let mut changed = false;
    let mut bindings = FxHashSet::default();
    for (did, sig_dec) in &mut sig_decs.data {
        let hir::Node::Item(item) = tcx.hir_node_by_def_id(*did) else {
            continue;
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            continue;
        };
        let body = tcx.hir_body(body);
        for (idx, param) in body.params.iter().enumerate() {
            let Some(kind) = sig_dec.input_decs.get(idx).copied().flatten() else {
                continue;
            };
            if !kind.is_owning_box_like() {
                continue;
            }
            let hir::PatKind::Binding(_, hir_id, _, _) = param.pat.kind else {
                continue;
            };
            if local_raw_param_summaries.get(&(*did, idx))
                != Some(&LocalRawParamSummary::BorrowOnly)
            {
                sig_dec.set_input_dec(idx, Some(PtrKind::Raw(kind.is_mut())));
                bindings.insert(hir_id);
                changed = true;
            }
        }
    }
    (changed, bindings)
}

#[derive(Default)]
struct FreedBorrowOutputDowngrades {
    outputs: FxHashSet<LocalDefId>,
    tied_inputs: FxHashSet<(LocalDefId, usize)>,
}

impl FreedBorrowOutputDowngrades {
    fn changed(&self) -> bool {
        !self.outputs.is_empty() || !self.tied_inputs.is_empty()
    }
}

fn downgrade_freed_borrow_outputs(
    tcx: TyCtxt<'_>,
    sig_decs: &mut SigDecisions,
    free_like_wrappers: &FxHashSet<LocalDefId>,
) -> FreedBorrowOutputDowngrades {
    struct FreedBorrowOutputVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        free_like_wrappers: &'a FxHashSet<LocalDefId>,
        call_results: FxHashMap<HirId, LocalDefId>,
        freed_locals: FxHashSet<HirId>,
        freed_call_results: FxHashSet<LocalDefId>,
    }

    impl<'tcx> FreedBorrowOutputVisitor<'_, 'tcx> {
        fn record_call_result(&mut self, hir_id: HirId, expr: &'tcx hir::Expr<'tcx>) {
            let Some(callee_did) = hir_called_local_fn(self.tcx, expr) else {
                return;
            };
            self.call_results.insert(hir_id, callee_did);
        }

        fn record_freed_call_result(&mut self, expr: &'tcx hir::Expr<'tcx>) {
            let is_direct_free = hir_call_matches_foreign_name(self.tcx, expr, "free");
            let is_wrapper_free = hir_called_local_fn(self.tcx, expr)
                .is_some_and(|def_id| self.free_like_wrappers.contains(&def_id));
            if !is_direct_free && !is_wrapper_free {
                return;
            }
            let hir::ExprKind::Call(_, args) = expr.kind else {
                return;
            };
            let [arg] = args else { return };
            if let Some(callee_did) = hir_called_local_fn(self.tcx, hir_unwrap_casts(arg)) {
                self.freed_call_results.insert(callee_did);
            }
        }
    }

    impl<'tcx> Visitor<'tcx> for FreedBorrowOutputVisitor<'_, 'tcx> {
        fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
            if let hir::StmtKind::Let(let_stmt) = stmt.kind
                && let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind
                && let Some(init) = let_stmt.init
            {
                self.record_call_result(hir_id, init);
            }
            intravisit::walk_stmt(self, stmt);
        }

        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                && let Some(hir_id) = hir_unwrapped_local_id(lhs)
            {
                self.record_call_result(hir_id, rhs);
            }
            if let Some((hir_id, _)) =
                hir_free_like_arg_local_id(self.tcx, expr, self.free_like_wrappers)
            {
                self.freed_locals.insert(hir_id);
            } else {
                self.record_freed_call_result(expr);
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut callees_to_raw = FxHashSet::default();
    for maybe_owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let hir::OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            continue;
        };
        let body = tcx.hir_body(body);
        let mut visitor = FreedBorrowOutputVisitor {
            tcx,
            free_like_wrappers,
            call_results: FxHashMap::default(),
            freed_locals: FxHashSet::default(),
            freed_call_results: FxHashSet::default(),
        };
        visitor.visit_body(body);
        for freed_local in visitor.freed_locals {
            if let Some(callee_did) = visitor.call_results.get(&freed_local) {
                callees_to_raw.insert(*callee_did);
            }
        }
        callees_to_raw.extend(visitor.freed_call_results);
    }

    let mut changed = FreedBorrowOutputDowngrades::default();
    for callee_did in callees_to_raw {
        let Some(sig_dec) = sig_decs.data.get_mut(&callee_did) else {
            continue;
        };
        if sig_dec.signature_locked {
            continue;
        }
        let Some(output_kind) = sig_dec.output_dec else {
            continue;
        };
        let should_downgrade = is_borrow_like_decision(output_kind)
            || output_kind.is_owning_box_like() && fn_output_may_return_input(tcx, callee_did);
        if !should_downgrade {
            continue;
        }
        let output_lifetime = sig_dec.output_lifetime;
        sig_dec.set_output_dec(Some(PtrKind::Raw(output_kind.is_mut())));
        changed.outputs.insert(callee_did);
        if let Some(output_lifetime) = output_lifetime {
            for idx in 0..sig_dec.input_decs.len() {
                if sig_dec.input_lifetimes.get(idx).copied().flatten() != Some(output_lifetime) {
                    continue;
                }
                let Some(input_kind) = sig_dec.input_decs[idx] else {
                    continue;
                };
                if is_borrow_like_decision(input_kind) {
                    sig_dec.set_input_dec(idx, Some(PtrKind::Raw(input_kind.is_mut())));
                    changed.tied_inputs.insert((callee_did, idx));
                }
            }
        } else if output_kind.is_owning_box_like() {
            for idx in 0..sig_dec.input_decs.len() {
                let Some(input_kind) = sig_dec.input_decs[idx] else {
                    continue;
                };
                sig_dec.set_input_dec(idx, Some(PtrKind::Raw(input_kind.is_mut())));
                changed.tied_inputs.insert((callee_did, idx));
            }
        }
    }
    changed
}

fn fn_output_may_return_input(tcx: TyCtxt<'_>, did: LocalDefId) -> bool {
    let sig = tcx.fn_sig(did).skip_binder().skip_binder();
    let input_len = sig.inputs().len();
    let return_local = rustc_middle::mir::Local::from_u32(0);
    let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();

    for bb in body.basic_blocks.iter() {
        for stmt in &bb.statements {
            let rustc_middle::mir::StatementKind::Assign(box (place, rvalue)) = &stmt.kind else {
                continue;
            };
            if place.as_local() != Some(return_local) {
                continue;
            }
            if rvalue_uses_input_local(rvalue, input_len) {
                return true;
            }
        }
    }

    false
}

fn rvalue_uses_input_local(rvalue: &rustc_middle::mir::Rvalue<'_>, input_len: usize) -> bool {
    match rvalue {
        rustc_middle::mir::Rvalue::Use(operand)
        | rustc_middle::mir::Rvalue::Cast(_, operand, _) => {
            operand_uses_input_local(operand, input_len)
        }
        rustc_middle::mir::Rvalue::Ref(_, _, place) => place_uses_input_local(place, input_len),
        _ => false,
    }
}

fn operand_uses_input_local(operand: &rustc_middle::mir::Operand<'_>, input_len: usize) -> bool {
    match operand {
        rustc_middle::mir::Operand::Copy(place) | rustc_middle::mir::Operand::Move(place) => {
            place_uses_input_local(place, input_len)
        }
        rustc_middle::mir::Operand::Constant(_) => false,
    }
}

fn place_uses_input_local(place: &rustc_middle::mir::Place<'_>, input_len: usize) -> bool {
    place
        .as_local()
        .is_some_and(|local| (1..=input_len).contains(&local.as_usize()))
}

fn downgrade_raw_cast_call_inputs(
    tcx: TyCtxt<'_>,
    sig_decs: &mut SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
) -> FxHashSet<(LocalDefId, usize)> {
    struct RawCastCallVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        sig_decs: &'a mut SigDecisions,
        ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
        changed: FxHashSet<(LocalDefId, usize)>,
    }

    impl<'tcx> Visitor<'tcx> for RawCastCallVisitor<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            let hir::ExprKind::Call(_, args) = expr.kind else {
                intravisit::walk_expr(self, expr);
                return;
            };
            let Some(callee_did) = hir_called_local_fn(self.tcx, expr) else {
                intravisit::walk_expr(self, expr);
                return;
            };
            let typeck = self.tcx.typeck(expr.hir_id.owner);
            let Some(sig_dec) = self.sig_decs.data.get_mut(&callee_did) else {
                intravisit::walk_expr(self, expr);
                return;
            };
            if sig_dec.signature_locked {
                intravisit::walk_expr(self, expr);
                return;
            }
            for (idx, arg) in args.iter().enumerate() {
                let Some((_, mutability)) = unwrap_ptr_from_mir_ty(typeck.expr_ty_adjusted(arg))
                else {
                    continue;
                };
                let Some(source_hir_id) = hir_casted_pointer_local_source(self.tcx, typeck, arg)
                else {
                    continue;
                };
                let input_dec = sig_dec.input_decs.get(idx).copied().flatten();
                if input_dec.is_some_and(is_borrow_like_decision)
                    && self
                        .ptr_kinds
                        .get(&source_hir_id)
                        .copied()
                        .is_some_and(is_borrow_bridgeable_source_decision)
                {
                    continue;
                }
                let raw = PtrKind::Raw(mutability.is_mut());
                if sig_dec.input_decs.get(idx).copied().flatten() != Some(raw) {
                    sig_dec.set_input_dec(idx, Some(raw));
                    self.changed.insert((callee_did, idx));
                }
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut changed = FxHashSet::default();
    for maybe_owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let hir::OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            continue;
        };
        let body = tcx.hir_body(body);
        let mut visitor = RawCastCallVisitor {
            tcx,
            sig_decs,
            ptr_kinds,
            changed: FxHashSet::default(),
        };
        visitor.visit_body(body);
        changed.extend(visitor.changed);
    }
    changed
}

fn downgrade_cursor_inputs_from_unanchored_raw_callers(
    tcx: TyCtxt<'_>,
    sig_decs: &mut SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
) -> FxHashSet<(LocalDefId, usize)> {
    let raw_origin_locals = collect_unanchored_raw_pointer_locals(tcx, sig_decs, ptr_kinds);

    struct CursorInputVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        sig_decs: &'a mut SigDecisions,
        ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
        raw_origin_locals: &'a FxHashSet<HirId>,
        changed: FxHashSet<(LocalDefId, usize)>,
    }

    impl<'tcx> Visitor<'tcx> for CursorInputVisitor<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            let hir::ExprKind::Call(_, args) = hir_unwrap_casts(expr).kind else {
                intravisit::walk_expr(self, expr);
                return;
            };
            let Some(callee_did) = hir_called_local_fn(self.tcx, expr) else {
                intravisit::walk_expr(self, expr);
                return;
            };

            let updates = {
                let Some(sig_dec) = self.sig_decs.data.get(&callee_did) else {
                    intravisit::walk_expr(self, expr);
                    return;
                };
                if sig_dec.signature_locked {
                    intravisit::walk_expr(self, expr);
                    return;
                }
                args.iter()
                    .enumerate()
                    .filter_map(|(idx, arg)| {
                        let Some(PtrKind::SliceCursor(m)) =
                            sig_dec.input_decs.get(idx).copied().flatten()
                        else {
                            return None;
                        };
                        if !callee_input_has_syntactic_negative_offset(self.tcx, callee_did, idx) {
                            return None;
                        }
                        hir_expr_is_unanchored_raw_pointer_arg(
                            self.tcx,
                            self.sig_decs,
                            self.ptr_kinds,
                            self.raw_origin_locals,
                            arg,
                        )
                        .then_some((idx, m))
                    })
                    .collect::<Vec<_>>()
            };

            if !updates.is_empty()
                && let Some(sig_dec) = self.sig_decs.data.get_mut(&callee_did)
            {
                for (idx, m) in updates {
                    if matches!(
                        sig_dec.input_decs.get(idx).copied().flatten(),
                        Some(PtrKind::SliceCursor(_))
                    ) {
                        sig_dec.set_input_dec(idx, Some(PtrKind::Raw(m)));
                        self.changed.insert((callee_did, idx));
                    }
                }
            }

            intravisit::walk_expr(self, expr);
        }
    }

    let mut changed = FxHashSet::default();
    for maybe_owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let hir::OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            continue;
        };
        let body = tcx.hir_body(body);
        let mut visitor = CursorInputVisitor {
            tcx,
            sig_decs,
            ptr_kinds,
            raw_origin_locals: &raw_origin_locals,
            changed: FxHashSet::default(),
        };
        visitor.visit_body(body);
        changed.extend(visitor.changed);
    }
    changed
}

fn callee_input_has_syntactic_negative_offset(
    tcx: TyCtxt<'_>,
    did: LocalDefId,
    idx: usize,
) -> bool {
    let Some(param_hir_id) = callee_input_param_binding(tcx, did, idx) else {
        return false;
    };

    struct NegativeOffsetVisitor<'tcx> {
        tcx: TyCtxt<'tcx>,
        param_hir_id: HirId,
        found: bool,
    }

    impl<'tcx> Visitor<'tcx> for NegativeOffsetVisitor<'tcx> {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if self.found {
                return;
            }
            if let hir::ExprKind::MethodCall(seg, receiver, args, _) = expr.kind
                && hir_unwrapped_local_id(receiver) == Some(self.param_hir_id)
                && match seg.ident.name.as_str() {
                    "sub" | "wrapping_sub" => true,
                    "offset" | "wrapping_offset" => args
                        .first()
                        .is_some_and(|arg| hir_expr_is_syntactically_negative(self.tcx, arg)),
                    _ => false,
                }
            {
                self.found = true;
                return;
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let hir::Node::Item(item) = tcx.hir_node_by_def_id(did) else {
        return false;
    };
    let hir::ItemKind::Fn { body, .. } = item.kind else {
        return false;
    };
    let mut visitor = NegativeOffsetVisitor {
        tcx,
        param_hir_id,
        found: false,
    };
    visitor.visit_body(tcx.hir_body(body));
    visitor.found
}

fn hir_expr_is_syntactically_negative(tcx: TyCtxt<'_>, expr: &hir::Expr<'_>) -> bool {
    if matches!(
        hir_unwrap_casts(expr).kind,
        hir::ExprKind::Unary(hir::UnOp::Neg, _)
    ) {
        return true;
    }
    tcx.sess
        .source_map()
        .span_to_snippet(expr.span)
        .ok()
        .is_some_and(|snippet| snippet.trim_start().starts_with('-'))
}

fn collect_unanchored_raw_pointer_locals(
    tcx: TyCtxt<'_>,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
) -> FxHashSet<HirId> {
    struct RawOriginVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        sig_decs: &'a SigDecisions,
        ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
        locals: FxHashSet<HirId>,
    }

    impl<'tcx> RawOriginVisitor<'_, 'tcx> {
        fn record_assignment(&mut self, lhs: &'tcx hir::Expr<'tcx>, rhs: &'tcx hir::Expr<'tcx>) {
            let Some(hir_id) = hir_unwrapped_local_id(lhs) else {
                return;
            };
            if !tcx_node_ty_is_raw_ptr(self.tcx, hir_id) {
                return;
            }
            if hir_expr_is_unanchored_raw_pointer_source(
                self.tcx,
                self.sig_decs,
                self.ptr_kinds,
                rhs,
            ) {
                self.locals.insert(hir_id);
            }
        }
    }

    impl<'tcx> Visitor<'tcx> for RawOriginVisitor<'_, 'tcx> {
        fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
            if let hir::StmtKind::Let(let_stmt) = stmt.kind
                && let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind
                && let Some(init) = let_stmt.init
                && tcx_node_ty_is_raw_ptr(self.tcx, hir_id)
                && hir_expr_is_unanchored_raw_pointer_source(
                    self.tcx,
                    self.sig_decs,
                    self.ptr_kinds,
                    init,
                )
            {
                self.locals.insert(hir_id);
            }
            intravisit::walk_stmt(self, stmt);
        }

        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind {
                self.record_assignment(lhs, rhs);
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut visitor = RawOriginVisitor {
        tcx,
        sig_decs,
        ptr_kinds,
        locals: FxHashSet::default(),
    };
    for maybe_owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let hir::OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            continue;
        };
        visitor.visit_body(tcx.hir_body(body));
    }
    visitor.locals
}

fn hir_expr_is_unanchored_raw_pointer_arg(
    tcx: TyCtxt<'_>,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    raw_origin_locals: &FxHashSet<HirId>,
    expr: &hir::Expr<'_>,
) -> bool {
    if hir_expr_uses_non_pointer_local(tcx, expr) {
        return false;
    }
    if let Some(hir_id) = hir_unwrapped_local_id(expr)
        && raw_origin_locals.contains(&hir_id)
    {
        return true;
    }
    hir_expr_is_unanchored_raw_pointer_source(tcx, sig_decs, ptr_kinds, expr)
}

fn hir_expr_is_unanchored_raw_pointer_source(
    tcx: TyCtxt<'_>,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    expr: &hir::Expr<'_>,
) -> bool {
    let expr = hir_unwrap_casts(expr);
    if !hir_expr_ty_is_raw_ptr(tcx, expr) {
        return false;
    }

    match expr.kind {
        hir::ExprKind::Path(hir::QPath::Resolved(_, path)) => {
            let Res::Local(hir_id) = path.res else {
                return true;
            };
            let kind = ptr_kinds.get(&hir_id).copied().or_else(|| {
                unwrap_ptr_from_mir_ty(tcx.typeck(hir_id.owner).node_type(hir_id))
                    .map(|(_, mutability)| PtrKind::Raw(mutability.is_mut()))
            });
            !kind.is_some_and(is_cursor_anchor_decision)
        }
        hir::ExprKind::Call(..) => hir_callee_output_kind(tcx, sig_decs, ptr_kinds, expr)
            .is_none_or(|kind| !is_cursor_anchor_decision(kind)),
        hir::ExprKind::MethodCall(seg, receiver, _, _) => match seg.ident.name.as_str() {
            "offset" | "add" | "sub" | "wrapping_add" | "wrapping_sub" => {
                hir_expr_is_unanchored_raw_pointer_source(tcx, sig_decs, ptr_kinds, receiver)
            }
            "as_ptr" | "as_mut_ptr" => {
                if hir_expr_ty_is_raw_ptr(tcx, receiver) {
                    hir_expr_is_unanchored_raw_pointer_source(tcx, sig_decs, ptr_kinds, receiver)
                } else {
                    false
                }
            }
            _ => true,
        },
        hir::ExprKind::AddrOf(_, _, pointee) => !hir_expr_ty_is_slice_or_array(tcx, pointee),
        _ => true,
    }
}

fn is_cursor_anchor_decision(kind: PtrKind) -> bool {
    matches!(
        kind,
        PtrKind::Slice(_) | PtrKind::SliceCursor(_) | PtrKind::BoxedSlice | PtrKind::OptBoxedSlice
    )
}

fn hir_expr_ty_is_raw_ptr(tcx: TyCtxt<'_>, expr: &hir::Expr<'_>) -> bool {
    unwrap_ptr_from_mir_ty(tcx.typeck(expr.hir_id.owner).expr_ty_adjusted(expr)).is_some()
}

fn raw_pointer_map_or_closure_body<'a, 'tcx>(
    tcx: TyCtxt<'tcx>,
    ast_to_hir: &AstToHir,
    expr_id: NodeId,
    ast_call: &'a mut MethodCall,
) -> Option<(bool, &'a mut Expr, &'tcx hir::Expr<'tcx>)> {
    if ast_call.seg.ident.name.as_str() != "map_or" || ast_call.args.len() != 2 {
        return None;
    }
    let ExprKind::Closure(box ast_closure) = &mut ast_call.args[1].kind else {
        return None;
    };

    let hir_expr = ast_to_hir.get_expr(expr_id, tcx)?;
    let typeck = tcx.typeck(hir_expr.hir_id.owner);
    let (_, raw_mutability) = unwrap_ptr_from_mir_ty(typeck.expr_ty_adjusted(hir_expr))?;

    let hir::ExprKind::MethodCall(_, hir_receiver, hir_args, _) = hir_expr.kind else {
        return None;
    };
    let ty::TyKind::Adt(adt_def, _) = typeck.expr_ty_adjusted(hir_receiver).kind() else {
        return None;
    };
    if !tcx.is_lang_item(adt_def.did(), LangItem::Option) {
        return None;
    }
    let hir_closure_arg = hir_args.get(1)?;
    let hir::ExprKind::Closure(hir::Closure { body, .. }) = hir_closure_arg.kind else {
        return None;
    };
    let hir_body = tcx.hir_body(*body);
    let ty::TyKind::RawPtr(_, _) = typeck.expr_ty(hir_body.value).kind() else {
        return None;
    };

    Some((
        raw_mutability.is_mut(),
        &mut ast_closure.body,
        hir_body.value,
    ))
}

fn tcx_node_ty_is_raw_ptr(tcx: TyCtxt<'_>, hir_id: HirId) -> bool {
    unwrap_ptr_from_mir_ty(tcx.typeck(hir_id.owner).node_type(hir_id)).is_some()
}

fn hir_expr_uses_non_pointer_local(tcx: TyCtxt<'_>, expr: &hir::Expr<'_>) -> bool {
    hir_local_ids_in_expr(expr)
        .into_iter()
        .any(|hir_id| !tcx_node_ty_is_raw_ptr(tcx, hir_id))
}

fn hir_expr_ty_is_slice_or_array(tcx: TyCtxt<'_>, expr: &hir::Expr<'_>) -> bool {
    match tcx.typeck(expr.hir_id.owner).expr_ty_adjusted(expr).kind() {
        ty::TyKind::Array(..) | ty::TyKind::Slice(..) => true,
        ty::TyKind::Ref(_, inner, _) => {
            matches!(inner.kind(), ty::TyKind::Array(..) | ty::TyKind::Slice(..))
        }
        _ => false,
    }
}

fn downgrade_unsupported_box_outputs<'tcx>(
    tcx: TyCtxt<'tcx>,
    sig_decs: &mut SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    c_exposed_fns: &FxHashSet<String>,
) -> FxHashSet<LocalDefId> {
    let mut to_raw = Vec::new();
    for (did, sig_dec) in &sig_decs.data {
        let Some(output_kind) = sig_dec.output_dec else {
            continue;
        };
        if !output_kind.is_owning_box_like() {
            continue;
        }
        let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
        let Some((inner_ty, _)) =
            unwrap_ptr_from_mir_ty(body.local_decls[rustc_middle::mir::Local::from_u32(0)].ty)
        else {
            continue;
        };
        if is_c_exposed_fn(tcx, *did, c_exposed_fns)
            || fn_tail_returns_unsupported_box_binding(
                tcx,
                sig_decs,
                ptr_kinds,
                *did,
                output_kind,
                inner_ty,
            )
            || fn_output_has_unsupported_nonlocal_consumers(tcx, ptr_kinds, *did, output_kind)
        {
            to_raw.push(*did);
        }
    }
    let mut changed = FxHashSet::default();
    for did in to_raw {
        if let Some(sig_dec) = sig_decs.data.get_mut(&did) {
            sig_dec.set_output_dec(Some(PtrKind::Raw(true)));
            changed.insert(did);
        }
    }
    changed
}

fn fn_output_has_unsupported_nonlocal_consumers(
    tcx: TyCtxt<'_>,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    callee_did: LocalDefId,
    output_kind: PtrKind,
) -> bool {
    struct NonlocalCallConsumerVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
        callee_did: LocalDefId,
        output_kind: PtrKind,
        found: bool,
    }

    impl<'tcx> NonlocalCallConsumerVisitor<'_, 'tcx> {
        fn call_targets_callee(&self, expr: &'tcx hir::Expr<'tcx>) -> bool {
            let expr = hir_unwrap_casts(expr);
            let hir::ExprKind::Call(func, _) = expr.kind else {
                return false;
            };
            let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_unwrap_casts(func).kind
            else {
                return false;
            };
            let Res::Def(_, def_id) = path.res else {
                return false;
            };
            def_id.as_local() == Some(self.callee_did)
        }

        fn expr_target_kind(&self, expr: &'tcx hir::Expr<'tcx>) -> Option<PtrKind> {
            let expr = hir_unwrap_casts(expr);
            if let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = expr.kind
                && let Res::Local(hir_id) = path.res
            {
                return self.ptr_kinds.get(&hir_id).copied();
            }
            let ty = self.tcx.typeck(expr.hir_id.owner).expr_ty(expr);
            unwrap_ptr_from_mir_ty(ty).map(|(_, m)| PtrKind::Raw(m.is_mut()))
        }
    }

    impl<'tcx> Visitor<'tcx> for NonlocalCallConsumerVisitor<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if self.found {
                return;
            }
            if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                && self.call_targets_callee(rhs)
            {
                if matches!(
                    hir_unwrap_casts(lhs).kind,
                    hir::ExprKind::Path(hir::QPath::Resolved(
                        _,
                        hir::Path {
                            res: Res::Local(_),
                            ..
                        }
                    ))
                ) {
                    intravisit::walk_expr(self, expr);
                    return;
                }
                if self.expr_target_kind(lhs) != Some(self.output_kind) {
                    self.found = true;
                    return;
                }
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let crate_hir = tcx.hir_crate(());
    for maybe_owner in crate_hir.owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let hir::OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            continue;
        };
        let body = tcx.hir_body(body);
        let mut visitor = NonlocalCallConsumerVisitor {
            tcx,
            ptr_kinds,
            callee_did,
            output_kind,
            found: false,
        };
        visitor.visit_body(body);
        if visitor.found {
            return true;
        }
    }

    false
}

fn local_called_fn_def_id(tcx: TyCtxt<'_>, hir_expr: &hir::Expr<'_>) -> Option<LocalDefId> {
    let hir_expr = hir_unwrap_casts(hir_expr);
    let hir::ExprKind::Call(func, _) = hir_expr.kind else {
        return None;
    };
    let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_unwrap_casts(func).kind else {
        return None;
    };
    let Res::Def(_, def_id) = path.res else {
        return None;
    };
    let def_id = def_id.as_local()?;
    local_def_id_has_fn_body(tcx, def_id).then_some(def_id)
}

fn effective_callee_output_kind(
    tcx: TyCtxt<'_>,
    sig_decs: &SigDecisions,
    _ptr_kinds: &FxHashMap<HirId, PtrKind>,
    def_id: LocalDefId,
) -> Option<PtrKind> {
    let sig_dec = sig_decs.data.get(&def_id)?;
    if let Some(output_dec) = sig_dec.output_dec {
        return Some(output_dec);
    }
    let sig = tcx.fn_sig(def_id).skip_binder().skip_binder();
    match sig.output().kind() {
        ty::TyKind::RawPtr(_, m) => Some(PtrKind::Raw(m.is_mut())),
        _ => None,
    }
}

fn hir_callee_output_kind(
    tcx: TyCtxt<'_>,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    hir_expr: &hir::Expr<'_>,
) -> Option<PtrKind> {
    let def_id = local_called_fn_def_id(tcx, hir_expr)?;
    effective_callee_output_kind(tcx, sig_decs, ptr_kinds, def_id)
}

fn local_def_id_has_fn_body(tcx: TyCtxt<'_>, def_id: LocalDefId) -> bool {
    matches!(
        tcx.hir_node_by_def_id(def_id),
        hir::Node::Item(hir::Item {
            kind: hir::ItemKind::Fn { .. },
            ..
        })
    )
}

fn hir_call_matches_foreign_name(tcx: TyCtxt<'_>, expr: &hir::Expr<'_>, name: &str) -> bool {
    let expr = hir_unwrap_casts(expr);
    let hir::ExprKind::Call(func, _) = expr.kind else {
        return false;
    };
    let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_unwrap_casts(func).kind else {
        return false;
    };
    if path
        .segments
        .last()
        .is_none_or(|seg| seg.ident.name.as_str() != name)
    {
        return false;
    }
    let Res::Def(_, def_id) = path.res else {
        return false;
    };
    !def_id
        .as_local()
        .is_some_and(|local| local_def_id_has_fn_body(tcx, local))
}

fn hir_called_local_fn(tcx: TyCtxt<'_>, expr: &hir::Expr<'_>) -> Option<LocalDefId> {
    local_called_fn_def_id(tcx, expr)
}

fn hir_is_borrow_only_foreign_buffer_arg(
    tcx: TyCtxt<'_>,
    expr: &hir::Expr<'_>,
    arg_index: usize,
) -> bool {
    if hir_called_local_fn(tcx, expr).is_some() {
        return false;
    }
    let Some(name) = hir_call_name(expr) else {
        return false;
    };
    match name.as_str() {
        "memcpy" | "memmove" => arg_index < 2,
        "memchr" => arg_index == 0,
        "memset" => arg_index == 0,
        "strncpy" => arg_index < 2,
        _ => false,
    }
}

fn hir_free_like_arg_local_id<'tcx>(
    tcx: TyCtxt<'tcx>,
    expr: &'tcx hir::Expr<'tcx>,
    free_like_wrappers: &FxHashSet<LocalDefId>,
) -> Option<(HirId, &'tcx hir::Expr<'tcx>)> {
    let is_direct_free = hir_call_matches_foreign_name(tcx, expr, "free");
    let is_wrapper_free =
        hir_called_local_fn(tcx, expr).is_some_and(|def_id| free_like_wrappers.contains(&def_id));
    if !is_direct_free && !is_wrapper_free {
        return None;
    }
    let hir::ExprKind::Call(_, args) = expr.kind else {
        return None;
    };
    let [arg] = args else { return None };
    let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_unwrap_casts(arg).kind else {
        return None;
    };
    let Res::Local(hir_id) = path.res else {
        return None;
    };
    Some((hir_id, arg))
}

fn hir_unwrapped_local_id(expr: &hir::Expr<'_>) -> Option<HirId> {
    let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_unwrap_casts(expr).kind else {
        return None;
    };
    let Res::Local(hir_id) = path.res else {
        return None;
    };
    Some(hir_id)
}

fn hir_path_source_kind(
    tcx: TyCtxt<'_>,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    expr: &hir::Expr<'_>,
) -> Option<PtrKind> {
    let hir_id = hir_unwrapped_local_id(expr)?;
    ptr_kinds.get(&hir_id).copied().or_else(|| {
        unwrap_ptr_from_mir_ty(tcx.typeck(hir_id.owner).node_type(hir_id))
            .map(|(_, mutability)| PtrKind::Raw(mutability.is_mut()))
    })
}

fn hir_local_ids_in_expr(expr: &hir::Expr<'_>) -> Vec<HirId> {
    struct LocalUseVisitor {
        locals: Vec<HirId>,
    }

    impl<'tcx> Visitor<'tcx> for LocalUseVisitor {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let Some(hir_id) = hir_unwrapped_local_id(expr) {
                self.locals.push(hir_id);
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut visitor = LocalUseVisitor { locals: Vec::new() };
    visitor.visit_expr(expr);
    visitor.locals
}

fn hir_local_ids_outside_top_level_field_projections(expr: &hir::Expr<'_>) -> Vec<HirId> {
    struct LocalUseVisitor {
        locals: Vec<HirId>,
    }

    impl<'tcx> Visitor<'tcx> for LocalUseVisitor {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let hir::ExprKind::Field(base, _) = expr.kind
                && hir_whole_ptr_root(base).is_some()
            {
                return;
            }
            if let Some(hir_id) = hir_unwrapped_local_id(expr) {
                self.locals.push(hir_id);
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut visitor = LocalUseVisitor { locals: Vec::new() };
    visitor.visit_expr(expr);
    visitor.locals
}

fn hir_top_level_field_projection_uses_in_expr(expr: &hir::Expr<'_>) -> Vec<(HirId, Symbol)> {
    struct FieldProjectionVisitor {
        uses: Vec<(HirId, Symbol)>,
    }

    impl<'tcx> Visitor<'tcx> for FieldProjectionVisitor {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let hir::ExprKind::Field(base, ident) = expr.kind
                && let Some(root) = hir_whole_ptr_root(base)
            {
                self.uses.push((root, ident.name));
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut visitor = FieldProjectionVisitor { uses: Vec::new() };
    visitor.visit_expr(expr);
    visitor.uses
}

fn hir_expr_verbatim_snippet(tcx: TyCtxt<'_>, expr: &hir::Expr<'_>) -> Option<String> {
    tcx.sess.source_map().span_to_snippet(expr.span).ok()
}

struct WrapperScalarDagContext<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    param_positions: &'a FxHashMap<HirId, usize>,
    scalar_defs: &'a FxHashMap<HirId, &'tcx hir::Expr<'tcx>>,
}

fn ty_is_wrapper_scalar_dag_ty(ty: ty::Ty<'_>) -> bool {
    matches!(
        ty.kind(),
        ty::TyKind::Bool
            | ty::TyKind::Char
            | ty::TyKind::Int(_)
            | ty::TyKind::Uint(_)
            | ty::TyKind::Float(_)
    )
}

fn hir_expr_uses_any_local(expr: &hir::Expr<'_>) -> bool {
    struct LocalUseVisitor {
        found: bool,
    }
    impl<'tcx> Visitor<'tcx> for LocalUseVisitor {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if self.found {
                return;
            }
            if hir_unwrapped_local_id(expr).is_some() {
                self.found = true;
                return;
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut visitor = LocalUseVisitor { found: false };
    visitor.visit_expr(expr);
    visitor.found
}

fn hir_is_const_like_scalar_path(expr: &hir::Expr<'_>) -> bool {
    let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_unwrap_casts(expr).kind else {
        return false;
    };
    matches!(
        path.res,
        Res::Def(
            rustc_hir::def::DefKind::Const
                | rustc_hir::def::DefKind::AssocConst
                | rustc_hir::def::DefKind::ConstParam,
            _
        )
    )
}

fn hir_is_any_size_of_expr(tcx: TyCtxt<'_>, expr: &hir::Expr<'_>) -> bool {
    hir_expr_snippet(tcx, hir_unwrap_casts(expr)).is_some_and(|snippet| {
        snippet.contains("::core::mem::size_of::<")
            || snippet.contains("core::mem::size_of::<")
            || snippet.contains("::std::mem::size_of::<")
            || snippet.contains("std::mem::size_of::<")
    })
}

fn hir_is_allowed_size_query_arg(expr: &hir::Expr<'_>) -> bool {
    let expr = hir_unwrap_casts(expr);
    matches!(expr.kind, hir::ExprKind::Path(..) | hir::ExprKind::Lit(..))
}

fn hir_is_allowed_size_query_call<'tcx>(tcx: TyCtxt<'tcx>, expr: &'tcx hir::Expr<'tcx>) -> bool {
    let hir::ExprKind::Call(_, args) = hir_unwrap_casts(expr).kind else {
        return false;
    };
    let Some(name) = hir_call_name(expr) else {
        return false;
    };
    matches!(name.as_str(), "strlen" | "strnlen" | "strcspn")
        && args.iter().all(|arg| hir_is_allowed_size_query_arg(arg))
        && tcx.typeck(expr.hir_id.owner).expr_ty(expr).is_integral()
}

fn resolve_wrapper_param_index<'tcx>(
    ctx: &WrapperScalarDagContext<'_, 'tcx>,
    expr: &'tcx hir::Expr<'tcx>,
    visiting: &mut FxHashSet<HirId>,
) -> Option<usize> {
    let expr = hir_unwrap_casts(expr);
    let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = expr.kind else {
        return None;
    };
    let Res::Local(hir_id) = path.res else {
        return None;
    };
    if let Some(index) = ctx.param_positions.get(&hir_id) {
        return Some(*index);
    }
    let rhs = ctx.scalar_defs.get(&hir_id).copied()?;
    if !visiting.insert(hir_id) {
        return None;
    }
    let resolved = resolve_wrapper_param_index(ctx, rhs, visiting);
    visiting.remove(&hir_id);
    resolved
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum WrapperScalarDagStatus {
    Allowed,
    Rejected,
    Inconclusive,
}

fn combine_wrapper_scalar_dag_status(
    left: WrapperScalarDagStatus,
    right: WrapperScalarDagStatus,
) -> WrapperScalarDagStatus {
    match (left, right) {
        (WrapperScalarDagStatus::Rejected, _) | (_, WrapperScalarDagStatus::Rejected) => {
            WrapperScalarDagStatus::Rejected
        }
        (WrapperScalarDagStatus::Allowed, WrapperScalarDagStatus::Allowed) => {
            WrapperScalarDagStatus::Allowed
        }
        _ => WrapperScalarDagStatus::Inconclusive,
    }
}

fn hir_wrapper_scalar_dag_status<'tcx>(
    ctx: &WrapperScalarDagContext<'_, 'tcx>,
    expr: &'tcx hir::Expr<'tcx>,
    visiting: &mut FxHashSet<HirId>,
    depth: usize,
) -> WrapperScalarDagStatus {
    if depth > 16 {
        return WrapperScalarDagStatus::Inconclusive;
    }
    let expr = hir_unwrap_casts(expr);
    match expr.kind {
        hir::ExprKind::Lit(..) => WrapperScalarDagStatus::Allowed,
        hir::ExprKind::Path(hir::QPath::Resolved(_, path)) => match path.res {
            Res::Local(hir_id) => {
                if ctx.param_positions.contains_key(&hir_id) {
                    return WrapperScalarDagStatus::Allowed;
                }
                let Some(rhs) = ctx.scalar_defs.get(&hir_id).copied() else {
                    return WrapperScalarDagStatus::Inconclusive;
                };
                if !visiting.insert(hir_id) {
                    return WrapperScalarDagStatus::Inconclusive;
                }
                let admissible = hir_wrapper_scalar_dag_status(ctx, rhs, visiting, depth + 1);
                visiting.remove(&hir_id);
                admissible
            }
            _ => {
                if hir_is_const_like_scalar_path(expr) {
                    WrapperScalarDagStatus::Allowed
                } else {
                    WrapperScalarDagStatus::Rejected
                }
            }
        },
        hir::ExprKind::Unary(hir::UnOp::Neg, inner) => {
            hir_wrapper_scalar_dag_status(ctx, inner, visiting, depth + 1)
        }
        hir::ExprKind::Binary(op, lhs, rhs) => {
            if !matches!(
                op.node,
                BinOpKind::Add | BinOpKind::Sub | BinOpKind::Mul | BinOpKind::Div | BinOpKind::Rem
            ) {
                return WrapperScalarDagStatus::Rejected;
            }
            combine_wrapper_scalar_dag_status(
                hir_wrapper_scalar_dag_status(ctx, lhs, visiting, depth + 1),
                hir_wrapper_scalar_dag_status(ctx, rhs, visiting, depth + 1),
            )
        }
        hir::ExprKind::MethodCall(seg, receiver, args, _) => {
            if !matches!(
                seg.ident.name.as_str(),
                "wrapping_add" | "wrapping_sub" | "wrapping_mul" | "wrapping_div" | "wrapping_rem"
            ) {
                return WrapperScalarDagStatus::Rejected;
            }
            let mut status = hir_wrapper_scalar_dag_status(ctx, receiver, visiting, depth + 1);
            for arg in args.iter() {
                status = combine_wrapper_scalar_dag_status(
                    status,
                    hir_wrapper_scalar_dag_status(ctx, arg, visiting, depth + 1),
                );
            }
            status
        }
        _ => {
            if hir_is_any_size_of_expr(ctx.tcx, expr)
                || hir_is_allowed_size_query_call(ctx.tcx, expr)
            {
                WrapperScalarDagStatus::Allowed
            } else {
                WrapperScalarDagStatus::Rejected
            }
        }
    }
}

fn ty_supports_raw_bridge_default_expr<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> bool {
    match ty.kind() {
        ty::TyKind::Bool
        | ty::TyKind::Char
        | ty::TyKind::Int(_)
        | ty::TyKind::Uint(_)
        | ty::TyKind::Float(_) => true,
        ty::TyKind::RawPtr(..) => true,
        ty::TyKind::Array(elem, _) => ty_supports_raw_bridge_default_expr(tcx, *elem),
        ty::TyKind::Tuple(elems) => elems
            .iter()
            .all(|elem| ty_supports_raw_bridge_default_expr(tcx, elem)),
        ty::TyKind::Adt(adt_def, _) if adt_def.did().is_local() && adt_def.is_enum() => {
            fieldless_enum_zero_variant(tcx, *adt_def).is_some()
        }
        ty::TyKind::Adt(adt_def, args) if adt_def.did().is_local() && adt_def.is_struct() => {
            adt_def
                .all_fields()
                .all(|field| ty_supports_raw_bridge_default_expr(tcx, field.ty(tcx, args)))
        }
        _ => false,
    }
}

fn ty_supports_scalar_box_from_raw_bridge(ty: ty::Ty<'_>) -> bool {
    matches!(
        ty.kind(),
        ty::TyKind::Adt(adt_def, _) if adt_def.did().is_local() && adt_def.is_struct()
    )
}

fn scalar_box_from_raw_free_expr(arg_str: &str, inner_ty_str: &str) -> Expr {
    utils::expr!(
        "{{ let __crat_raw_free = {}; if !(__crat_raw_free).is_null() {{ drop(Box::from_raw((__crat_raw_free) as *mut {})); }} }}",
        arg_str,
        inner_ty_str,
    )
}

fn array_box_from_raw_free_expr(arg_str: &str, inner_ty_str: &str, len_expr: &str) -> Expr {
    utils::expr!(
        "{{ let __crat_raw_free = {}; if !(__crat_raw_free).is_null() {{ drop(Box::from_raw(std::ptr::slice_from_raw_parts_mut((__crat_raw_free) as *mut {}, ({}) as usize))); }} }}",
        arg_str,
        inner_ty_str,
        len_expr,
    )
}

fn fieldless_enum_zero_variant<'tcx>(
    tcx: TyCtxt<'tcx>,
    adt_def: ty::AdtDef<'tcx>,
) -> Option<Symbol> {
    if !adt_def.is_enum()
        || !adt_def
            .variants()
            .iter()
            .all(|variant| variant.fields.is_empty())
    {
        return None;
    }

    adt_def
        .discriminants(tcx)
        .find(|(_, discr)| discr.val == 0)
        .map(|(idx, _)| adt_def.variant(idx).name)
}

fn raw_array_len_expr_from_bytes<'tcx>(
    tcx: TyCtxt<'tcx>,
    lhs_inner_ty: ty::Ty<'tcx>,
    bytes: &hir::Expr<'_>,
) -> Option<String> {
    let bytes = hir_expr_verbatim_snippet(tcx, hir_unwrap_casts(bytes))?;
    if ty_contains_param(lhs_inner_ty) {
        return None;
    }
    let ty = mir_ty_to_string(lhs_inner_ty, tcx);
    Some(format!(
        "((({bytes}) as usize) / std::mem::size_of::<{ty}>())"
    ))
}

fn raw_bridge_info_from_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    lhs_inner_ty: ty::Ty<'tcx>,
    name: Symbol,
    args: &[&'tcx hir::Expr<'tcx>],
    scalar_ctx: Option<&WrapperScalarDagContext<'_, 'tcx>>,
) -> Option<RawBridgeInfo> {
    let scalar_arg_rejected = |expr: &'tcx hir::Expr<'tcx>| {
        scalar_ctx.is_some_and(|ctx| {
            hir_expr_uses_any_local(expr)
                && hir_wrapper_scalar_dag_status(ctx, expr, &mut FxHashSet::default(), 0)
                    == WrapperScalarDagStatus::Rejected
        })
    };
    let byte_sized_elem = matches!(
        lhs_inner_ty.kind(),
        ty::TyKind::Int(ty::IntTy::I8) | ty::TyKind::Uint(ty::UintTy::U8)
    );
    if !ty_supports_raw_bridge_default_expr(tcx, lhs_inner_ty) {
        return None;
    }
    let ty_name = (!ty_contains_param(lhs_inner_ty)).then(|| mir_ty_to_string(lhs_inner_ty, tcx));
    match (name, args) {
        (name, [bytes]) if name == Symbol::intern("malloc") => {
            if hir_size_of_call_matches_expected(tcx, bytes, lhs_inner_ty)
                || ty_name
                    .as_ref()
                    .is_some_and(|ty_name| hir_is_exact_size_of_expr(tcx, bytes, ty_name))
            {
                Some(RawBridgeInfo::Scalar)
            } else if scalar_arg_rejected(bytes) {
                None
            } else {
                raw_array_len_expr_from_bytes(tcx, lhs_inner_ty, bytes)
                    .map(|len_expr| RawBridgeInfo::Array { len_expr })
            }
        }
        (name, [count, elem_size]) if name == Symbol::intern("calloc") => {
            if hir_is_literal_one(tcx, count)
                && (hir_size_of_call_matches_expected(tcx, elem_size, lhs_inner_ty)
                    || ty_name
                        .as_ref()
                        .is_some_and(|ty_name| hir_is_exact_size_of_expr(tcx, elem_size, ty_name)))
            {
                Some(RawBridgeInfo::Scalar)
            } else if scalar_arg_rejected(count) || scalar_arg_rejected(elem_size) {
                None
            } else if ty_name
                .as_ref()
                .is_some_and(|ty_name| hir_is_exact_size_of_expr(tcx, count, ty_name))
                || (byte_sized_elem && hir_is_exact_c_char_size_of_expr(tcx, count))
            {
                if byte_sized_elem {
                    Some(RawBridgeInfo::Array {
                        len_expr: hir_expr_verbatim_snippet(tcx, hir_unwrap_casts(elem_size))?,
                    })
                } else {
                    None
                }
            } else {
                Some(RawBridgeInfo::Array {
                    len_expr: hir_expr_verbatim_snippet(tcx, hir_unwrap_casts(count))?,
                })
            }
        }
        (name, [ptr, bytes])
            if name == Symbol::intern("realloc") && hir_is_null_like_ptr_arg(tcx, ptr) =>
        {
            if hir_size_of_call_matches_expected(tcx, bytes, lhs_inner_ty)
                || ty_name
                    .as_ref()
                    .is_some_and(|ty_name| hir_is_exact_size_of_expr(tcx, bytes, ty_name))
            {
                Some(RawBridgeInfo::Scalar)
            } else if scalar_arg_rejected(bytes) {
                None
            } else {
                raw_array_len_expr_from_bytes(tcx, lhs_inner_ty, bytes)
                    .map(|len_expr| RawBridgeInfo::Array { len_expr })
            }
        }
        _ => None,
    }
}

fn hir_raw_bridge_info<'tcx>(
    tcx: TyCtxt<'tcx>,
    lhs_inner_ty: ty::Ty<'tcx>,
    rhs: &'tcx hir::Expr<'tcx>,
    alloc_wrappers: Option<&FxHashMap<LocalDefId, AllocWrapperInfo>>,
    scalar_ctx: Option<&WrapperScalarDagContext<'_, 'tcx>>,
) -> Option<RawBridgeInfo> {
    let rhs = hir_unwrap_casts(rhs);
    if let hir::ExprKind::Call(_, args) = rhs.kind
        && let Some(name) = hir_call_name(rhs)
    {
        let arg_refs = args.iter().collect::<Vec<_>>();
        if let Some(info) =
            raw_bridge_info_from_call(tcx, lhs_inner_ty, name, &arg_refs, scalar_ctx)
        {
            return Some(info);
        }
    }

    let alloc_wrappers = alloc_wrappers?;
    let def_id = hir_called_local_fn(tcx, rhs)?;
    let wrapper = alloc_wrappers.get(&def_id)?;
    let hir::ExprKind::Call(_, args) = rhs.kind else {
        return None;
    };
    let arg = |idx: usize| args.get(idx);
    match *wrapper {
        AllocWrapperInfo::Fixed(ref info) => Some(info.clone()),
        AllocWrapperInfo::Bytes { bytes_param } => raw_bridge_info_from_call(
            tcx,
            lhs_inner_ty,
            Symbol::intern("malloc"),
            &[arg(bytes_param)?],
            None,
        ),
        AllocWrapperInfo::CountSize {
            count_param,
            elem_size_param,
        } => raw_bridge_info_from_call(
            tcx,
            lhs_inner_ty,
            Symbol::intern("calloc"),
            &[arg(count_param)?, arg(elem_size_param)?],
            None,
        ),
        AllocWrapperInfo::Realloc {
            ptr_param,
            bytes_param,
        } => raw_bridge_info_from_call(
            tcx,
            lhs_inner_ty,
            Symbol::intern("realloc"),
            &[arg(ptr_param)?, arg(bytes_param)?],
            None,
        ),
    }
}

fn raw_wrapper_info_from_rhs<'tcx>(
    tcx: TyCtxt<'tcx>,
    lhs_inner_ty: ty::Ty<'tcx>,
    rhs: &'tcx hir::Expr<'tcx>,
    param_positions: &FxHashMap<HirId, usize>,
    scalar_defs: &FxHashMap<HirId, &'tcx hir::Expr<'tcx>>,
) -> Option<AllocWrapperInfo> {
    let rhs = hir_unwrap_casts(rhs);
    let hir::ExprKind::Call(_, args) = rhs.kind else {
        return None;
    };
    let name = hir_call_name(rhs)?;
    let scalar_ctx = WrapperScalarDagContext {
        tcx,
        param_positions,
        scalar_defs,
    };
    let param_index = |expr: &'tcx hir::Expr<'tcx>| {
        resolve_wrapper_param_index(&scalar_ctx, expr, &mut FxHashSet::default())
    };
    let mentions_only_params = |expr: &'tcx hir::Expr<'tcx>| {
        struct LocalUseVisitor {
            locals: Vec<HirId>,
        }
        impl<'tcx> Visitor<'tcx> for LocalUseVisitor {
            fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
                if let Some(hir_id) = hir_unwrapped_local_id(expr) {
                    self.locals.push(hir_id);
                }
                intravisit::walk_expr(self, expr);
            }
        }
        let mut visitor = LocalUseVisitor { locals: Vec::new() };
        visitor.visit_expr(expr);
        visitor
            .locals
            .into_iter()
            .all(|hir_id| param_positions.contains_key(&hir_id))
    };

    match (name, args) {
        (name, [bytes]) if name == Symbol::intern("malloc") => {
            if let Some(bytes_param) = param_index(bytes) {
                Some(AllocWrapperInfo::Bytes { bytes_param })
            } else if mentions_only_params(bytes) {
                raw_bridge_info_from_call(tcx, lhs_inner_ty, name, &[bytes], None)
                    .map(AllocWrapperInfo::Fixed)
            } else {
                None
            }
        }
        (name, [count, elem_size]) if name == Symbol::intern("calloc") => {
            if let (Some(count_param), Some(elem_size_param)) =
                (param_index(count), param_index(elem_size))
            {
                Some(AllocWrapperInfo::CountSize {
                    count_param,
                    elem_size_param,
                })
            } else if mentions_only_params(count) && mentions_only_params(elem_size) {
                raw_bridge_info_from_call(tcx, lhs_inner_ty, name, &[count, elem_size], None)
                    .map(AllocWrapperInfo::Fixed)
            } else {
                None
            }
        }
        (name, [ptr, bytes]) if name == Symbol::intern("realloc") => {
            if let (Some(ptr_param), Some(bytes_param)) = (param_index(ptr), param_index(bytes)) {
                Some(AllocWrapperInfo::Realloc {
                    ptr_param,
                    bytes_param,
                })
            } else if (hir_is_null_like_ptr_arg(tcx, ptr) && param_index(bytes).is_some())
                || (mentions_only_params(ptr) && mentions_only_params(bytes))
            {
                raw_bridge_info_from_call(tcx, lhs_inner_ty, name, &[ptr, bytes], None)
                    .map(AllocWrapperInfo::Fixed)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn collect_local_allocator_wrappers(tcx: TyCtxt<'_>) -> FxHashMap<LocalDefId, AllocWrapperInfo> {
    let mut wrappers = FxHashMap::default();
    let crate_hir = tcx.hir_crate(());
    for maybe_owner in crate_hir.owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let hir::OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            continue;
        };
        let def_id = item.owner_id.def_id;
        let body = tcx.hir_body(body);
        let typeck = tcx.typeck(def_id);
        let param_positions = body
            .params
            .iter()
            .enumerate()
            .filter_map(|(idx, param)| {
                let hir::PatKind::Binding(_, hir_id, _, _) = param.pat.kind else {
                    return None;
                };
                Some((hir_id, idx))
            })
            .collect::<FxHashMap<_, _>>();
        #[derive(Default)]
        struct Candidate {
            info: Option<AllocWrapperInfo>,
            aliases: FxHashSet<HirId>,
            byte_view_aliases: FxHashSet<HirId>,
            returned: bool,
            disqualified: bool,
        }

        struct WrapperVisitor<'a, 'tcx> {
            tcx: TyCtxt<'tcx>,
            param_positions: &'a FxHashMap<HirId, usize>,
            typeck: &'a rustc_middle::ty::TypeckResults<'tcx>,
            candidates: FxHashMap<HirId, Candidate>,
            root_of: FxHashMap<HirId, HirId>,
            scalar_defs: FxHashMap<HirId, &'tcx hir::Expr<'tcx>>,
        }

        impl<'a, 'tcx> WrapperVisitor<'a, 'tcx> {
            fn mark_root(&mut self, hir_id: HirId, info: AllocWrapperInfo) {
                let candidate = self.candidates.entry(hir_id).or_default();
                if let Some(existing) = &candidate.info {
                    if *existing != info {
                        candidate.disqualified = true;
                    }
                } else {
                    candidate.info = Some(info);
                }
                candidate.aliases.insert(hir_id);
                self.root_of.insert(hir_id, hir_id);
            }

            fn mark_alias(&mut self, alias: HirId, source: HirId) {
                let Some(root) = self.root_of.get(&source).copied() else {
                    return;
                };
                self.root_of.insert(alias, root);
                self.candidates
                    .entry(root)
                    .or_default()
                    .aliases
                    .insert(alias);
            }

            fn mark_byte_view_alias(&mut self, alias: HirId, source: HirId) {
                self.mark_alias(alias, source);
                self.candidates
                    .entry(self.root_of[&source])
                    .or_default()
                    .byte_view_aliases
                    .insert(alias);
            }

            fn mark_disqualified(&mut self, hir_id: HirId) {
                if let Some(root) = self.root_of.get(&hir_id).copied() {
                    self.candidates.entry(root).or_default().disqualified = true;
                }
            }

            fn mark_disqualified_for_lhs_use(&mut self, hir_id: HirId) {
                if let Some(root) = self.root_of.get(&hir_id).copied()
                    && self
                        .candidates
                        .get(&root)
                        .is_some_and(|candidate| candidate.byte_view_aliases.contains(&hir_id))
                {
                    return;
                }
                self.mark_disqualified(hir_id);
            }

            fn mark_returned(&mut self, hir_id: HirId) {
                if let Some(root) = self.root_of.get(&hir_id).copied() {
                    if self
                        .candidates
                        .get(&root)
                        .is_some_and(|candidate| candidate.byte_view_aliases.contains(&hir_id))
                    {
                        self.candidates.entry(root).or_default().disqualified = true;
                        return;
                    }
                    self.candidates.entry(root).or_default().returned = true;
                }
            }

            fn record_scalar_local(&mut self, hir_id: HirId, rhs: &'tcx hir::Expr<'tcx>) {
                if ty_is_wrapper_scalar_dag_ty(self.typeck.node_type(hir_id)) {
                    self.scalar_defs.insert(hir_id, rhs);
                }
            }
        }

        impl<'tcx> Visitor<'tcx> for WrapperVisitor<'_, 'tcx> {
            fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
                if let hir::StmtKind::Let(let_stmt) = stmt.kind
                    && let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind
                    && let Some(init) = let_stmt.init
                {
                    let lhs_ty = self.typeck.node_type(hir_id);
                    if lhs_ty.is_raw_ptr()
                        && let Some((lhs_inner_ty, _)) = unwrap_ptr_from_mir_ty(lhs_ty)
                    {
                        if let Some(info) = raw_wrapper_info_from_rhs(
                            self.tcx,
                            lhs_inner_ty,
                            init,
                            self.param_positions,
                            &self.scalar_defs,
                        ) {
                            self.mark_root(hir_id, info);
                        } else if let Some(rhs_hir_id) = hir_unwrapped_local_id(init) {
                            let rhs_ty = self.typeck.node_type(rhs_hir_id);
                            let is_byte_view_alias = hir_is_casted_local(init, rhs_hir_id)
                                && ty_is_byte_sized_raw_inner(lhs_inner_ty)
                                && unwrap_ptr_from_mir_ty(rhs_ty).is_some_and(
                                    |(rhs_inner_ty, _)| ty_is_byte_sized_raw_inner(rhs_inner_ty),
                                )
                                && self
                                    .root_of
                                    .get(&rhs_hir_id)
                                    .and_then(|root| self.candidates.get(root))
                                    .and_then(|candidate| candidate.info.as_ref())
                                    .is_some_and(|info| {
                                        matches!(
                                            info,
                                            AllocWrapperInfo::Fixed(RawBridgeInfo::Array { .. })
                                        )
                                    });
                            if is_byte_view_alias {
                                self.mark_byte_view_alias(hir_id, rhs_hir_id);
                            } else {
                                self.mark_alias(hir_id, rhs_hir_id);
                            }
                        }
                    }
                    self.record_scalar_local(hir_id, init);
                }
                intravisit::walk_stmt(self, stmt);
            }

            fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
                match expr.kind {
                    hir::ExprKind::Assign(lhs, rhs, _) => {
                        if let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = lhs.kind
                            && let Res::Local(lhs_hir_id) = path.res
                        {
                            let lhs_ty = self.typeck.expr_ty(lhs);
                            if lhs_ty.is_raw_ptr()
                                && let Some((lhs_inner_ty, _)) = unwrap_ptr_from_mir_ty(lhs_ty)
                            {
                                if let Some(info) = raw_wrapper_info_from_rhs(
                                    self.tcx,
                                    lhs_inner_ty,
                                    rhs,
                                    self.param_positions,
                                    &self.scalar_defs,
                                ) {
                                    self.mark_root(lhs_hir_id, info);
                                } else if let Some(rhs_hir_id) = hir_unwrapped_local_id(rhs) {
                                    let rhs_ty = self.typeck.node_type(rhs_hir_id);
                                    let is_byte_view_alias = hir_is_casted_local(rhs, rhs_hir_id)
                                        && ty_is_byte_sized_raw_inner(lhs_inner_ty)
                                        && unwrap_ptr_from_mir_ty(rhs_ty).is_some_and(
                                            |(rhs_inner_ty, _)| {
                                                ty_is_byte_sized_raw_inner(rhs_inner_ty)
                                            },
                                        )
                                        && self
                                            .root_of
                                            .get(&rhs_hir_id)
                                            .and_then(|root| self.candidates.get(root))
                                            .and_then(|candidate| candidate.info.as_ref())
                                            .is_some_and(|info| {
                                                matches!(
                                                    info,
                                                    AllocWrapperInfo::Fixed(
                                                        RawBridgeInfo::Array { .. }
                                                    )
                                                )
                                            });
                                    if is_byte_view_alias {
                                        self.mark_byte_view_alias(lhs_hir_id, rhs_hir_id);
                                    } else {
                                        self.mark_alias(lhs_hir_id, rhs_hir_id);
                                    }
                                }
                            }
                            self.record_scalar_local(lhs_hir_id, rhs);
                        } else {
                            for lhs_hir_id in hir_local_ids_in_expr(lhs) {
                                self.mark_disqualified_for_lhs_use(lhs_hir_id);
                            }
                            if let Some(rhs_hir_id) = hir_unwrapped_local_id(rhs) {
                                self.mark_disqualified(rhs_hir_id);
                            }
                        }
                    }
                    hir::ExprKind::AssignOp(_, lhs, _) => {
                        for lhs_hir_id in hir_local_ids_in_expr(lhs) {
                            self.mark_disqualified_for_lhs_use(lhs_hir_id);
                        }
                    }
                    hir::ExprKind::Ret(Some(ret)) => {
                        if let Some(hir_id) = hir_unwrapped_local_id(ret) {
                            self.mark_returned(hir_id);
                        }
                    }
                    hir::ExprKind::Call(_, args) => {
                        let is_local_callee = hir_called_local_fn(self.tcx, expr).is_some();
                        for arg in args {
                            if let Some(hir_id) = hir_unwrapped_local_id(arg)
                                && is_local_callee
                            {
                                self.mark_disqualified(hir_id);
                            }
                        }
                    }
                    _ => {}
                }
                intravisit::walk_expr(self, expr);
            }

            fn visit_body(&mut self, body: &hir::Body<'tcx>) -> Self::Result {
                intravisit::walk_body(self, body);
                let mut tail = body.value;
                while let hir::ExprKind::Block(block, _) = tail.kind {
                    let Some(expr) = block.expr else {
                        break;
                    };
                    tail = expr;
                }
                if let Some(hir_id) = hir_unwrapped_local_id(tail) {
                    self.mark_returned(hir_id);
                }
            }
        }

        let mut visitor = WrapperVisitor {
            tcx,
            param_positions: &param_positions,
            typeck,
            candidates: FxHashMap::default(),
            root_of: FxHashMap::default(),
            scalar_defs: FxHashMap::default(),
        };
        visitor.visit_body(body);

        let eligible = visitor
            .candidates
            .into_iter()
            .filter_map(|(_root, candidate)| {
                if candidate.disqualified || !candidate.returned {
                    return None;
                }
                candidate.info
            })
            .collect::<Vec<_>>();
        if eligible.len() == 1 {
            wrappers.insert(def_id, eligible.into_iter().next().unwrap());
        }
    }
    wrappers
}

fn collect_local_free_wrappers(tcx: TyCtxt<'_>) -> FxHashSet<LocalDefId> {
    fn wrapper_name_allows_free(tcx: TyCtxt<'_>, def_id: LocalDefId) -> bool {
        let name = tcx
            .item_name(def_id.to_def_id())
            .as_str()
            .to_ascii_lowercase();
        name.contains("free") || name.contains("dealloc")
    }

    struct FreeWrapperVisitor {
        target: HirId,
        found: bool,
    }

    impl<'tcx> Visitor<'tcx> for FreeWrapperVisitor {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if self.found {
                return;
            }
            if let hir::ExprKind::Call(_, args) = expr.kind
                && args.len() == 1
                && hir_unwrapped_local_id(&args[0]) == Some(self.target)
            {
                self.found = true;
                return;
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut wrappers = FxHashSet::default();
    let crate_hir = tcx.hir_crate(());
    for maybe_owner in crate_hir.owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let hir::OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            continue;
        };
        let def_id = item.owner_id.def_id;
        if !wrapper_name_allows_free(tcx, def_id) {
            continue;
        }
        let body = tcx.hir_body(body);
        let [param] = body.params else {
            continue;
        };
        let hir::PatKind::Binding(_, param_hir_id, _, _) = param.pat.kind else {
            continue;
        };
        if !tcx.typeck(def_id).node_type(param_hir_id).is_raw_ptr() {
            continue;
        }
        let mut visitor = FreeWrapperVisitor {
            target: param_hir_id,
            found: false,
        };
        visitor.visit_body(body);
        if visitor.found {
            wrappers.insert(def_id);
        }
    }
    wrappers
}

fn collect_locally_called_fns(tcx: TyCtxt<'_>) -> FxHashSet<LocalDefId> {
    struct LocalCallVisitor<'a> {
        tcx: TyCtxt<'a>,
        called: FxHashSet<LocalDefId>,
    }

    impl<'tcx> Visitor<'tcx> for LocalCallVisitor<'tcx> {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let Some(def_id) = hir_called_local_fn(self.tcx, expr) {
                self.called.insert(def_id);
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut visitor = LocalCallVisitor {
        tcx,
        called: FxHashSet::default(),
    };
    for maybe_owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let hir::OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            continue;
        };
        visitor.visit_body(tcx.hir_body(body));
    }
    visitor.called
}

fn collect_local_raw_free_summaries(
    tcx: TyCtxt<'_>,
    free_like_wrappers: &FxHashSet<LocalDefId>,
) -> FxHashMap<(LocalDefId, usize), LocalRawParamSummary> {
    #[derive(Default)]
    struct ParamFacts {
        direct_free: bool,
        deps: FxHashSet<(LocalDefId, usize)>,
    }

    let crate_hir = tcx.hir_crate(());
    let mut raw_params_by_fn = FxHashMap::<LocalDefId, FxHashMap<HirId, usize>>::default();
    for maybe_owner in crate_hir.owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let hir::OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            continue;
        };
        let def_id = item.owner_id.def_id;
        let body = tcx.hir_body(body);
        let typeck = tcx.typeck(def_id);
        let raw_params = body
            .params
            .iter()
            .enumerate()
            .filter_map(|(idx, param)| {
                let hir::PatKind::Binding(_, hir_id, _, _) = param.pat.kind else {
                    return None;
                };
                typeck
                    .node_type(hir_id)
                    .is_raw_ptr()
                    .then_some((hir_id, idx))
            })
            .collect::<FxHashMap<_, _>>();
        if !raw_params.is_empty() {
            raw_params_by_fn.insert(def_id, raw_params);
        }
    }

    struct RawFreeSummaryVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        free_like_wrappers: &'a FxHashSet<LocalDefId>,
        raw_params_by_fn: &'a FxHashMap<LocalDefId, FxHashMap<HirId, usize>>,
        current_raw_params: &'a FxHashMap<HirId, usize>,
        facts: FxHashMap<usize, ParamFacts>,
    }

    impl<'tcx> RawFreeSummaryVisitor<'_, 'tcx> {
        fn mark_free(&mut self, param_index: usize) {
            self.facts.entry(param_index).or_default().direct_free = true;
        }

        fn add_dep(&mut self, param_index: usize, dep: (LocalDefId, usize)) {
            self.facts.entry(param_index).or_default().deps.insert(dep);
        }
    }

    impl<'tcx> Visitor<'tcx> for RawFreeSummaryVisitor<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let hir::ExprKind::Call(_, args) = expr.kind {
                let free_arg = hir_free_like_arg_local_id(self.tcx, expr, self.free_like_wrappers)
                    .map(|(hir_id, _)| hir_id);
                let local_callee = hir_called_local_fn(self.tcx, expr);
                for (arg_index, arg) in args.iter().enumerate() {
                    let Some(hir_id) = hir_unwrapped_local_id(arg) else {
                        continue;
                    };
                    let Some(param_index) = self.current_raw_params.get(&hir_id).copied() else {
                        continue;
                    };
                    if Some(hir_id) == free_arg {
                        self.mark_free(param_index);
                        continue;
                    }
                    let Some(local_callee) = local_callee else {
                        continue;
                    };
                    let Some(callee_raw_params) = self.raw_params_by_fn.get(&local_callee) else {
                        continue;
                    };
                    if callee_raw_params.values().any(|idx| *idx == arg_index) {
                        self.add_dep(param_index, (local_callee, arg_index));
                    }
                }
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut facts_by_param = FxHashMap::<(LocalDefId, usize), ParamFacts>::default();
    for (def_id, raw_params) in &raw_params_by_fn {
        for index in raw_params.values().copied() {
            facts_by_param.entry((*def_id, index)).or_default();
        }
        let hir::Node::Item(item) = tcx.hir_node_by_def_id(*def_id) else {
            continue;
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            continue;
        };
        let body = tcx.hir_body(body);
        let mut visitor = RawFreeSummaryVisitor {
            tcx,
            free_like_wrappers,
            raw_params_by_fn: &raw_params_by_fn,
            current_raw_params: raw_params,
            facts: FxHashMap::default(),
        };
        visitor.visit_body(body);
        for (param_index, facts) in visitor.facts {
            facts_by_param
                .entry((*def_id, param_index))
                .or_default()
                .direct_free |= facts.direct_free;
            facts_by_param
                .entry((*def_id, param_index))
                .or_default()
                .deps
                .extend(facts.deps);
        }
    }

    let mut summaries = facts_by_param
        .keys()
        .copied()
        .map(|key| (key, LocalRawParamSummary::BorrowOnly))
        .collect::<FxHashMap<_, _>>();
    loop {
        let mut changed = false;
        for (key, facts) in &facts_by_param {
            let next = if facts.direct_free
                || facts
                    .deps
                    .iter()
                    .any(|dep| summaries.get(dep) != Some(&LocalRawParamSummary::BorrowOnly))
            {
                LocalRawParamSummary::Escapes
            } else {
                LocalRawParamSummary::BorrowOnly
            };
            if summaries.get(key) != Some(&next) {
                summaries.insert(*key, next);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    summaries
}

fn collect_local_raw_param_summaries(
    tcx: TyCtxt<'_>,
    sig_decs: &SigDecisions,
    free_like_wrappers: &FxHashSet<LocalDefId>,
) -> FxHashMap<(LocalDefId, usize), LocalRawParamSummary> {
    #[derive(Default)]
    struct ParamFacts {
        direct_free: bool,
        direct_escape: bool,
        returned_to_owning_output: bool,
        returned_to_borrowed_output: bool,
        deps: FxHashSet<(LocalDefId, usize)>,
    }

    let crate_hir = tcx.hir_crate(());
    let mut raw_params_by_fn = FxHashMap::<LocalDefId, FxHashMap<HirId, usize>>::default();
    for maybe_owner in crate_hir.owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let hir::OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            continue;
        };
        let def_id = item.owner_id.def_id;
        let body = tcx.hir_body(body);
        let typeck = tcx.typeck(def_id);
        let raw_params = body
            .params
            .iter()
            .enumerate()
            .filter_map(|(idx, param)| {
                let hir::PatKind::Binding(_, hir_id, _, _) = param.pat.kind else {
                    return None;
                };
                typeck
                    .node_type(hir_id)
                    .is_raw_ptr()
                    .then_some((hir_id, idx))
            })
            .collect::<FxHashMap<_, _>>();
        if !raw_params.is_empty() {
            raw_params_by_fn.insert(def_id, raw_params);
        }
    }

    struct RawParamSummaryVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        free_like_wrappers: &'a FxHashSet<LocalDefId>,
        raw_params_by_fn: &'a FxHashMap<LocalDefId, FxHashMap<HirId, usize>>,
        current_raw_params: &'a FxHashMap<HirId, usize>,
        output_dec: Option<PtrKind>,
        local_storage_params: FxHashMap<HirId, FxHashSet<usize>>,
        facts: FxHashMap<usize, ParamFacts>,
    }

    impl<'a, 'tcx> RawParamSummaryVisitor<'a, 'tcx> {
        fn param_index(&self, expr: &'tcx hir::Expr<'tcx>) -> Option<usize> {
            let hir_id = hir_unwrapped_local_id(expr)?;
            self.current_raw_params.get(&hir_id).copied()
        }

        fn param_indices_in_expr(&self, expr: &'tcx hir::Expr<'tcx>) -> FxHashSet<usize> {
            let mut params = FxHashSet::default();
            if let Some(param_index) = self.param_index(expr) {
                params.insert(param_index);
            }
            if let Some(root) = hir_local_place_root_without_deref(expr)
                && let Some(stored_params) = self.local_storage_params.get(&root)
            {
                params.extend(stored_params.iter().copied());
            }
            params
        }

        fn track_local_storage(
            &mut self,
            lhs: &'tcx hir::Expr<'tcx>,
            params: &FxHashSet<usize>,
        ) -> bool {
            let Some(root) = hir_local_place_root_without_deref(lhs) else {
                return false;
            };
            if self.current_raw_params.contains_key(&root) {
                return false;
            }
            self.local_storage_params
                .entry(root)
                .or_default()
                .extend(params.iter().copied());
            true
        }

        fn mark_escape(&mut self, param_index: usize) {
            self.facts.entry(param_index).or_default().direct_escape = true;
        }

        fn mark_free(&mut self, param_index: usize) {
            self.facts.entry(param_index).or_default().direct_free = true;
        }

        fn mark_returned_to_owning_output(&mut self, param_index: usize) {
            self.facts
                .entry(param_index)
                .or_default()
                .returned_to_owning_output = true;
        }

        fn mark_returned_to_borrowed_output(&mut self, param_index: usize) {
            self.facts
                .entry(param_index)
                .or_default()
                .returned_to_borrowed_output = true;
        }

        fn mark_return(&mut self, param_index: usize) {
            match self.output_dec {
                Some(kind) if kind.is_owning_box_like() => {
                    self.mark_returned_to_owning_output(param_index);
                }
                Some(kind) if is_borrow_bridgeable_source_decision(kind) => {
                    self.mark_returned_to_borrowed_output(param_index);
                }
                _ => self.mark_escape(param_index),
            }
        }

        fn add_dep(&mut self, param_index: usize, dep: (LocalDefId, usize)) {
            self.facts.entry(param_index).or_default().deps.insert(dep);
        }
    }

    impl<'tcx> Visitor<'tcx> for RawParamSummaryVisitor<'_, 'tcx> {
        fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
            if let hir::StmtKind::Let(let_stmt) = stmt.kind
                && let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind
                && let Some(init) = let_stmt.init
            {
                let params = self.param_indices_in_expr(init);
                if !params.is_empty() {
                    self.local_storage_params
                        .entry(hir_id)
                        .or_default()
                        .extend(params);
                }
            }
            intravisit::walk_stmt(self, stmt);
        }

        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            match expr.kind {
                hir::ExprKind::Assign(_, rhs, _) => {
                    let params = self.param_indices_in_expr(rhs);
                    if !params.is_empty()
                        && let hir::ExprKind::Assign(lhs, _, _) = expr.kind
                        && !self.track_local_storage(lhs, &params)
                    {
                        for param_index in params {
                            self.mark_escape(param_index);
                        }
                    }
                }
                hir::ExprKind::Ret(Some(ret)) => {
                    for param_index in self.param_indices_in_expr(ret) {
                        self.mark_return(param_index);
                    }
                }
                hir::ExprKind::Call(_, args) => {
                    let free_arg =
                        hir_free_like_arg_local_id(self.tcx, expr, self.free_like_wrappers)
                            .map(|(hir_id, _)| hir_id);
                    let local_callee = hir_called_local_fn(self.tcx, expr);
                    for (arg_index, arg) in args.iter().enumerate() {
                        let params = self.param_indices_in_expr(arg);
                        if params.is_empty() {
                            continue;
                        }
                        let arg_hir_id = hir_unwrapped_local_id(arg);
                        if arg_hir_id == free_arg {
                            for param_index in params {
                                self.mark_free(param_index);
                            }
                            continue;
                        }
                        match local_callee {
                            Some(callee) => {
                                let Some(callee_raw_params) = self.raw_params_by_fn.get(&callee)
                                else {
                                    for param_index in params {
                                        self.mark_escape(param_index);
                                    }
                                    continue;
                                };
                                if callee_raw_params.values().any(|idx| *idx == arg_index) {
                                    for param_index in params {
                                        self.add_dep(param_index, (callee, arg_index));
                                    }
                                } else {
                                    for param_index in params {
                                        self.mark_escape(param_index);
                                    }
                                }
                            }
                            None => {
                                if !hir_is_borrow_only_foreign_buffer_arg(self.tcx, expr, arg_index)
                                {
                                    for param_index in params {
                                        self.mark_escape(param_index);
                                    }
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
            intravisit::walk_expr(self, expr);
        }

        fn visit_body(&mut self, body: &hir::Body<'tcx>) -> Self::Result {
            intravisit::walk_body(self, body);
            let mut tail = body.value;
            while let hir::ExprKind::Block(block, _) = tail.kind {
                let Some(expr) = block.expr else {
                    break;
                };
                tail = expr;
            }
            for param_index in self.param_indices_in_expr(tail) {
                self.mark_return(param_index);
            }
        }
    }

    let mut facts_by_param = FxHashMap::<(LocalDefId, usize), ParamFacts>::default();
    for (def_id, raw_params) in &raw_params_by_fn {
        for index in raw_params.values().copied() {
            facts_by_param.entry((*def_id, index)).or_default();
        }
        let hir::Node::Item(item) = tcx.hir_node_by_def_id(*def_id) else {
            continue;
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            continue;
        };
        let body = tcx.hir_body(body);
        let output_dec = sig_decs
            .data
            .get(def_id)
            .and_then(|sig_dec| sig_dec.output_dec);
        let mut visitor = RawParamSummaryVisitor {
            tcx,
            free_like_wrappers,
            raw_params_by_fn: &raw_params_by_fn,
            current_raw_params: raw_params,
            output_dec,
            local_storage_params: FxHashMap::default(),
            facts: FxHashMap::default(),
        };
        visitor.visit_body(body);
        for (param_index, facts) in visitor.facts {
            facts_by_param
                .entry((*def_id, param_index))
                .or_default()
                .direct_free |= facts.direct_free;
            facts_by_param
                .entry((*def_id, param_index))
                .or_default()
                .direct_escape |= facts.direct_escape;
            facts_by_param
                .entry((*def_id, param_index))
                .or_default()
                .returned_to_owning_output |= facts.returned_to_owning_output;
            facts_by_param
                .entry((*def_id, param_index))
                .or_default()
                .returned_to_borrowed_output |= facts.returned_to_borrowed_output;
            facts_by_param
                .entry((*def_id, param_index))
                .or_default()
                .deps
                .extend(facts.deps);
        }
    }

    let mut summaries = facts_by_param
        .keys()
        .copied()
        .map(|key| (key, LocalRawParamSummary::BorrowOnly))
        .collect::<FxHashMap<_, _>>();
    loop {
        let mut changed = false;
        for (key, facts) in &facts_by_param {
            let next = if facts.direct_free {
                LocalRawParamSummary::Freed
            } else if facts.direct_escape
                || facts
                    .deps
                    .iter()
                    .any(|dep| summaries.get(dep) != Some(&LocalRawParamSummary::BorrowOnly))
            {
                LocalRawParamSummary::Escapes
            } else if facts.returned_to_owning_output {
                LocalRawParamSummary::ReturnedToOwningOutput
            } else if facts.returned_to_borrowed_output {
                LocalRawParamSummary::ReturnedToBorrowedOutput
            } else {
                LocalRawParamSummary::BorrowOnly
            };
            if summaries.get(key) != Some(&next) {
                summaries.insert(*key, next);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    summaries
}

fn collect_raw_scalar_bridge_fields(
    tcx: TyCtxt<'_>,
    alloc_wrappers: &FxHashMap<LocalDefId, AllocWrapperInfo>,
) -> FxHashSet<StructFieldSlot> {
    #[derive(Default)]
    struct State {
        saw_scalar: bool,
        disqualified: bool,
    }

    struct RawScalarFieldBridgeVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        typeck: &'a rustc_middle::ty::TypeckResults<'tcx>,
        alloc_wrappers: &'a FxHashMap<LocalDefId, AllocWrapperInfo>,
        states: &'a mut FxHashMap<StructFieldSlot, State>,
        local_bridges: FxHashMap<HirId, RawBridgeInfo>,
    }

    impl<'tcx> RawScalarFieldBridgeVisitor<'_, 'tcx> {
        fn raw_bridge_info_for_rhs(
            &self,
            lhs_inner_ty: ty::Ty<'tcx>,
            rhs: &'tcx hir::Expr<'tcx>,
        ) -> Option<RawBridgeInfo> {
            if !ty_supports_scalar_box_from_raw_bridge(lhs_inner_ty) {
                return None;
            }
            if hir_is_null_like_ptr_arg(self.tcx, rhs) {
                return None;
            }

            hir_raw_bridge_info(self.tcx, lhs_inner_ty, rhs, Some(self.alloc_wrappers), None)
        }

        fn record_local_assignment(&mut self, lhs_hir_id: HirId, rhs: &'tcx hir::Expr<'tcx>) {
            let lhs_ty = self.typeck.node_type(lhs_hir_id);
            let Some((lhs_inner_ty, _)) = unwrap_ptr_from_mir_ty(lhs_ty) else {
                self.local_bridges.remove(&lhs_hir_id);
                return;
            };
            if let Some(info) = self.raw_bridge_info_for_rhs(lhs_inner_ty, rhs) {
                self.local_bridges.insert(lhs_hir_id, info);
            } else if !hir_is_null_like_ptr_arg(self.tcx, rhs) {
                self.local_bridges.remove(&lhs_hir_id);
            }
        }

        fn record_field_assignment(
            &mut self,
            lhs: &'tcx hir::Expr<'tcx>,
            rhs: &'tcx hir::Expr<'tcx>,
        ) {
            let Some(field) = hir_struct_field_slot(self.tcx, lhs) else {
                return;
            };
            let lhs_ty = self.typeck.expr_ty_adjusted(lhs);
            let Some((lhs_inner_ty, _)) = unwrap_ptr_from_mir_ty(lhs_ty) else {
                return;
            };
            if !ty_supports_scalar_box_from_raw_bridge(lhs_inner_ty) {
                return;
            }
            if hir_is_null_like_ptr_arg(self.tcx, rhs) {
                return;
            }

            let info = self.raw_bridge_info_for_rhs(lhs_inner_ty, rhs).or_else(|| {
                hir_unwrapped_local_id(rhs)
                    .and_then(|hir_id| self.local_bridges.get(&hir_id).cloned())
            });
            let state = self.states.entry(field).or_default();
            match info {
                Some(RawBridgeInfo::Scalar) => state.saw_scalar = true,
                Some(RawBridgeInfo::Array { .. }) | None => state.disqualified = true,
            }
        }
    }

    impl<'tcx> Visitor<'tcx> for RawScalarFieldBridgeVisitor<'_, 'tcx> {
        fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
            if let hir::StmtKind::Let(let_stmt) = stmt.kind
                && let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind
                && let Some(init) = let_stmt.init
            {
                self.record_local_assignment(hir_id, init);
            }
            intravisit::walk_stmt(self, stmt);
        }

        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind {
                if let Some(lhs_hir_id) = hir_unwrapped_local_id(lhs) {
                    self.record_local_assignment(lhs_hir_id, rhs);
                } else {
                    self.record_field_assignment(lhs, rhs);
                }
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut states = FxHashMap::default();
    for_each_hir_fn_body(tcx, |body, typeck| {
        let mut visitor = RawScalarFieldBridgeVisitor {
            tcx,
            typeck,
            alloc_wrappers,
            states: &mut states,
            local_bridges: FxHashMap::default(),
        };
        visitor.visit_body(body);
    });

    states
        .into_iter()
        .filter_map(|(field, state)| (state.saw_scalar && !state.disqualified).then_some(field))
        .collect()
}

fn collect_raw_bridge_bindings(
    tcx: TyCtxt<'_>,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    alloc_wrappers: &FxHashMap<LocalDefId, AllocWrapperInfo>,
    free_like_wrappers: &FxHashSet<LocalDefId>,
    local_raw_param_summaries: &FxHashMap<(LocalDefId, usize), LocalRawParamSummary>,
) -> FxHashMap<HirId, RawBridgeInfo> {
    #[derive(Default)]
    struct State {
        bridge: Option<RawBridgeInfo>,
        saw_free: bool,
        saw_return: bool,
        disqualified: bool,
        aliases: FxHashSet<HirId>,
    }

    struct RawBridgeVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
        alloc_wrappers: &'a FxHashMap<LocalDefId, AllocWrapperInfo>,
        free_like_wrappers: &'a FxHashSet<LocalDefId>,
        local_raw_param_summaries: &'a FxHashMap<(LocalDefId, usize), LocalRawParamSummary>,
        wrapper_like_bodies: &'a FxHashSet<LocalDefId>,
        typeck: &'a rustc_middle::ty::TypeckResults<'tcx>,
        body_owner: LocalDefId,
        param_positions: FxHashMap<HirId, usize>,
        alias_roots: FxHashMap<HirId, HirId>,
        byte_view_aliases: FxHashSet<HirId>,
        states: FxHashMap<HirId, State>,
        scalar_defs: FxHashMap<HirId, &'tcx hir::Expr<'tcx>>,
    }

    impl<'tcx> RawBridgeVisitor<'_, 'tcx> {
        fn mark_root(&mut self, hir_id: HirId, info: RawBridgeInfo) {
            let state = self.states.entry(hir_id).or_default();
            match &state.bridge {
                None => state.bridge = Some(info.clone()),
                Some(existing) if *existing == info => {}
                Some(_) => state.disqualified = true,
            }
            state.aliases.insert(hir_id);
            self.alias_roots.insert(hir_id, hir_id);
        }

        fn mark_alias(&mut self, alias: HirId, source: HirId) {
            let Some(root) = self.alias_roots.get(&source).copied() else {
                return;
            };
            self.alias_roots.insert(alias, root);
            self.states.entry(root).or_default().aliases.insert(alias);
        }

        fn mark_byte_view_alias(&mut self, alias: HirId, source: HirId) {
            self.mark_alias(alias, source);
            self.byte_view_aliases.insert(alias);
        }

        fn state_for_local_mut(&mut self, hir_id: HirId) -> Option<&mut State> {
            let root = self.alias_roots.get(&hir_id).copied().unwrap_or(hir_id);
            self.states.get_mut(&root)
        }

        fn disqualify_local(&mut self, hir_id: HirId) {
            if let Some(state) = self.state_for_local_mut(hir_id) {
                state.disqualified = true;
            }
        }

        fn disqualify_lhs_use(&mut self, hir_id: HirId) {
            if self.byte_view_aliases.contains(&hir_id) {
                return;
            }
            self.disqualify_local(hir_id);
        }

        fn update_local_from_rhs(
            &mut self,
            lhs_hir_id: HirId,
            rhs: &'tcx hir::Expr<'tcx>,
            lhs_inner_ty: ty::Ty<'tcx>,
        ) {
            if self.byte_view_aliases.contains(&lhs_hir_id)
                && hir_is_byte_view_self_update(lhs_hir_id, rhs)
            {
                return;
            }
            let scalar_ctx = self
                .wrapper_like_bodies
                .contains(&self.body_owner)
                .then_some(WrapperScalarDagContext {
                    tcx: self.tcx,
                    param_positions: &self.param_positions,
                    scalar_defs: &self.scalar_defs,
                });
            if let Some(info) = hir_raw_bridge_info(
                self.tcx,
                lhs_inner_ty,
                rhs,
                Some(self.alloc_wrappers),
                scalar_ctx.as_ref(),
            ) {
                self.mark_root(lhs_hir_id, info);
            } else if let Some(rhs_hir_id) = hir_unwrapped_local_id(rhs) {
                if self.byte_view_aliases.contains(&rhs_hir_id) && lhs_hir_id != rhs_hir_id {
                    self.disqualify_local(rhs_hir_id);
                    return;
                }
                let rhs_ty = self.tcx.typeck(rhs_hir_id.owner).node_type(rhs_hir_id);
                let can_mark_byte_view_alias = hir_is_casted_local(rhs, rhs_hir_id)
                    && ty_is_byte_sized_raw_inner(lhs_inner_ty)
                    && unwrap_ptr_from_mir_ty(rhs_ty)
                        .is_some_and(|(rhs_inner_ty, _)| ty_is_byte_sized_raw_inner(rhs_inner_ty))
                    && self
                        .state_for_local_mut(rhs_hir_id)
                        .and_then(|state| state.bridge.as_ref())
                        .is_some_and(|info| matches!(info, RawBridgeInfo::Array { .. }));
                if can_mark_byte_view_alias {
                    self.mark_byte_view_alias(lhs_hir_id, rhs_hir_id);
                    return;
                }
                if self.alloc_wrappers.contains_key(&self.body_owner) {
                    self.mark_alias(lhs_hir_id, rhs_hir_id);
                } else {
                    self.disqualify_local(rhs_hir_id);
                }
            } else if !hir_is_null_like_ptr_arg(self.tcx, rhs) {
                self.disqualify_local(lhs_hir_id);
            }
        }

        fn record_scalar_local(&mut self, hir_id: HirId, rhs: &'tcx hir::Expr<'tcx>) {
            if ty_is_wrapper_scalar_dag_ty(self.typeck.node_type(hir_id)) {
                self.scalar_defs.insert(hir_id, rhs);
            }
        }
    }

    impl<'tcx> Visitor<'tcx> for RawBridgeVisitor<'_, 'tcx> {
        fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
            if let hir::StmtKind::Let(let_stmt) = stmt.kind
                && let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind
                && let Some(init) = let_stmt.init
            {
                if matches!(self.ptr_kinds.get(&hir_id), Some(PtrKind::Raw(_))) {
                    let lhs_ty = self.tcx.typeck(hir_id.owner).node_type(hir_id);
                    if let Some((lhs_inner_ty, _)) = unwrap_ptr_from_mir_ty(lhs_ty) {
                        self.update_local_from_rhs(hir_id, init, lhs_inner_ty);
                    }
                }
                self.record_scalar_local(hir_id, init);
            }
            intravisit::walk_stmt(self, stmt);
        }

        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = lhs.kind
                && let Res::Local(hir_id) = path.res
            {
                if matches!(self.ptr_kinds.get(&hir_id), Some(PtrKind::Raw(_))) {
                    let lhs_ty = self.tcx.typeck(expr.hir_id.owner).expr_ty(lhs);
                    if let Some((lhs_inner_ty, _)) = unwrap_ptr_from_mir_ty(lhs_ty) {
                        self.update_local_from_rhs(hir_id, rhs, lhs_inner_ty);
                    }
                }
                self.record_scalar_local(hir_id, rhs);
            }
            if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                && let Some(rhs_hir_id) = hir_unwrapped_local_id(rhs)
                && hir_unwrapped_local_id(lhs).is_none()
            {
                self.disqualify_local(rhs_hir_id);
            }
            if let hir::ExprKind::Assign(lhs, _, _) | hir::ExprKind::AssignOp(_, lhs, _) = expr.kind
                && hir_unwrapped_local_id(lhs).is_none()
            {
                for lhs_hir_id in hir_local_ids_in_expr(lhs) {
                    self.disqualify_lhs_use(lhs_hir_id);
                }
            }
            if let hir::ExprKind::Call(_, args) = expr.kind {
                let free_arg = hir_free_like_arg_local_id(self.tcx, expr, self.free_like_wrappers)
                    .map(|(hir_id, _)| hir_id);
                let local_callee = hir_called_local_fn(self.tcx, expr);
                let free_arg_is_byte_view =
                    free_arg.is_some_and(|hir_id| self.byte_view_aliases.contains(&hir_id));
                if let Some(hir_id) = free_arg
                    && let Some(state) = self.state_for_local_mut(hir_id)
                {
                    if free_arg_is_byte_view {
                        state.disqualified = true;
                    } else {
                        state.saw_free = true;
                    }
                }
                for (arg_index, arg) in args.iter().enumerate() {
                    if let Some(hir_id) = hir_unwrapped_local_id(arg)
                        && Some(hir_id) != free_arg
                    {
                        if self.byte_view_aliases.contains(&hir_id) {
                            self.disqualify_local(hir_id);
                            continue;
                        }
                        if local_callee.is_none() {
                            continue;
                        }
                        let local_callee = local_callee.unwrap();
                        if self
                            .local_raw_param_summaries
                            .get(&(local_callee, arg_index))
                            != Some(&LocalRawParamSummary::BorrowOnly)
                        {
                            self.disqualify_local(hir_id);
                        }
                    }
                }
            }
            if let hir::ExprKind::Ret(Some(ret)) = expr.kind
                && let Some(hir_id) = hir_unwrapped_local_id(ret)
            {
                if self.byte_view_aliases.contains(&hir_id) {
                    self.disqualify_local(hir_id);
                } else if let Some(state) = self.state_for_local_mut(hir_id) {
                    state.saw_return = true;
                }
            }
            intravisit::walk_expr(self, expr);
        }

        fn visit_body(&mut self, body: &hir::Body<'tcx>) -> Self::Result {
            intravisit::walk_body(self, body);
            if let Some(hir_id) = hir_unwrapped_local_id(body.value) {
                if self.byte_view_aliases.contains(&hir_id) {
                    self.disqualify_local(hir_id);
                } else if let Some(state) = self.state_for_local_mut(hir_id) {
                    state.saw_return = true;
                }
            }
        }
    }

    let mut bindings = FxHashMap::default();
    let wrapper_like_bodies = collect_locally_called_fns(tcx);
    let crate_hir = tcx.hir_crate(());
    for maybe_owner in crate_hir.owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let hir::OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            continue;
        };
        let body = tcx.hir_body(body);
        let typeck = tcx.typeck(item.owner_id.def_id);
        let mut visitor = RawBridgeVisitor {
            tcx,
            ptr_kinds,
            alloc_wrappers,
            free_like_wrappers,
            local_raw_param_summaries,
            wrapper_like_bodies: &wrapper_like_bodies,
            typeck,
            body_owner: item.owner_id.def_id,
            param_positions: body
                .params
                .iter()
                .enumerate()
                .filter_map(|(idx, param)| {
                    let hir::PatKind::Binding(_, hir_id, _, _) = param.pat.kind else {
                        return None;
                    };
                    Some((hir_id, idx))
                })
                .collect(),
            alias_roots: FxHashMap::default(),
            byte_view_aliases: FxHashSet::default(),
            states: FxHashMap::default(),
            scalar_defs: FxHashMap::default(),
        };
        visitor.visit_body(body);
        for (_hir_id, state) in visitor.states {
            let allow_return_bridge =
                state.saw_return && alloc_wrappers.contains_key(&visitor.body_owner);
            if (state.saw_free || allow_return_bridge)
                && !state.disqualified
                && let Some(info) = state.bridge
            {
                for alias in state.aliases {
                    bindings.insert(alias, info.clone());
                }
            }
        }
    }
    bindings
}

fn collect_raw_call_result_bindings(
    tcx: TyCtxt<'_>,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
) -> FxHashSet<HirId> {
    struct RawCallResultVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        sig_decs: &'a SigDecisions,
        ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
        bindings: FxHashSet<HirId>,
    }

    impl<'tcx> Visitor<'tcx> for RawCallResultVisitor<'_, 'tcx> {
        fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
            if let hir::StmtKind::Let(let_stmt) = stmt.kind
                && let hir::PatKind::Binding(_, hir_id, ident, _) = let_stmt.pat.kind
                && let Some(init) = let_stmt.init
                && matches!(
                    hir_callee_output_kind(self.tcx, self.sig_decs, self.ptr_kinds, init),
                    Some(PtrKind::Raw(_))
                )
            {
                let _ = ident;
                self.bindings.insert(hir_id);
            }
            intravisit::walk_stmt(self, stmt);
        }

        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = lhs.kind
                && let Res::Local(hir_id) = path.res
                && matches!(
                    hir_callee_output_kind(self.tcx, self.sig_decs, self.ptr_kinds, rhs),
                    Some(PtrKind::Raw(_))
                )
            {
                self.bindings.insert(hir_id);
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut bindings: FxHashSet<HirId> = FxHashSet::default();
    let crate_hir = tcx.hir_crate(());
    for maybe_owner in crate_hir.owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let hir::OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            continue;
        };
        let body = tcx.hir_body(body);
        let mut visitor = RawCallResultVisitor {
            tcx,
            sig_decs,
            ptr_kinds,
            bindings: FxHashSet::default(),
        };
        visitor.visit_expr(body.value);
        bindings.extend(visitor.bindings);
    }
    bindings
}

fn collect_raw_local_assignment_bindings(
    tcx: TyCtxt<'_>,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
) -> FxHashSet<HirId> {
    struct RawLocalBindingVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
        bindings: FxHashSet<HirId>,
    }

    impl<'tcx> Visitor<'tcx> for RawLocalBindingVisitor<'_, 'tcx> {
        fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
            if let hir::StmtKind::Let(let_stmt) = stmt.kind
                && let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind
                && let Some(init) = let_stmt.init
                && self.tcx.typeck(hir_id.owner).node_type(hir_id).is_raw_ptr()
                && let Some(rhs_hir_id) =
                    hir_casted_pointer_local_source(self.tcx, self.tcx.typeck(hir_id.owner), init)
            {
                if self
                    .ptr_kinds
                    .get(&hir_id)
                    .copied()
                    .is_some_and(is_borrow_like_decision)
                    && self
                        .ptr_kinds
                        .get(&rhs_hir_id)
                        .copied()
                        .is_some_and(is_borrow_bridgeable_source_decision)
                {
                    intravisit::walk_stmt(self, stmt);
                    return;
                }
                self.bindings.insert(hir_id);
                if raw_pointer_binding_is_const(self.tcx, rhs_hir_id) {
                    self.bindings.insert(rhs_hir_id);
                }
            }
            intravisit::walk_stmt(self, stmt);
        }

        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                && let hir::ExprKind::Path(hir::QPath::Resolved(_, lhs_path)) = lhs.kind
                && let Res::Local(lhs_hir_id) = lhs_path.res
                && let hir::ExprKind::Path(hir::QPath::Resolved(_, rhs_path)) = rhs.kind
                && let Res::Local(rhs_hir_id) = rhs_path.res
                && matches!(self.ptr_kinds.get(&rhs_hir_id), Some(PtrKind::Raw(_)))
            {
                self.bindings.insert(lhs_hir_id);
            }
            if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                && let Some(lhs_hir_id) = hir_deref_addr_of_local(lhs)
                && self.tcx.typeck(rhs.hir_id.owner).expr_ty(rhs).is_raw_ptr()
            {
                self.bindings.insert(lhs_hir_id);
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut bindings: FxHashSet<HirId> = FxHashSet::default();
    let crate_hir = tcx.hir_crate(());
    for maybe_owner in crate_hir.owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let hir::OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            continue;
        };
        let body = tcx.hir_body(body);
        let mut visitor = RawLocalBindingVisitor {
            tcx,
            ptr_kinds,
            bindings: FxHashSet::default(),
        };
        visitor.visit_expr(body.value);
        bindings.extend(visitor.bindings);
    }
    bindings
}

fn hir_casted_pointer_local_source<'tcx>(
    tcx: TyCtxt<'tcx>,
    typeck: &rustc_middle::ty::TypeckResults<'tcx>,
    expr: &hir::Expr<'tcx>,
) -> Option<HirId> {
    match expr.kind {
        hir::ExprKind::Cast(inner, _) | hir::ExprKind::DropTemps(inner) => {
            if let Some(hir_id) = hir_unwrapped_local_id(inner)
                && let Some((source_inner_ty, _)) =
                    unwrap_ptr_from_mir_ty(tcx.typeck(hir_id.owner).node_type(hir_id))
                && let Some((target_inner_ty, _)) =
                    unwrap_ptr_from_mir_ty(typeck.expr_ty_adjusted(expr))
                && source_inner_ty == target_inner_ty
            {
                return Some(hir_id);
            }
            hir_casted_pointer_local_source(tcx, typeck, inner)
        }
        _ => None,
    }
}

fn raw_pointer_binding_is_const(tcx: TyCtxt<'_>, hir_id: HirId) -> bool {
    unwrap_ptr_from_mir_ty(tcx.typeck(hir_id.owner).node_type(hir_id))
        .is_some_and(|(_, mutability)| !mutability.is_mut())
}

fn hir_deref_addr_of_local(expr: &hir::Expr<'_>) -> Option<HirId> {
    let hir::ExprKind::Unary(hir::UnOp::Deref, addr_of) = expr.kind else {
        return None;
    };
    let hir::ExprKind::AddrOf(hir::BorrowKind::Ref, hir::Mutability::Mut, pointee) =
        utils::hir::unwrap_drop_temps(addr_of).kind
    else {
        return None;
    };
    hir_unwrapped_local_id(pointee)
}

fn hir_rhs_supports_box_target<'tcx>(
    tcx: TyCtxt<'tcx>,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    hir_expr: &'tcx hir::Expr<'tcx>,
    target_kind: PtrKind,
    lhs_inner_ty: ty::Ty<'tcx>,
) -> bool {
    let hir_uncast = hir_unwrap_casts(hir_expr);
    if hir_is_null_like_ptr_arg(tcx, hir_uncast) {
        return true;
    }

    match target_kind {
        PtrKind::Box | PtrKind::OptBox => {
            if hir_supports_scalar_box_allocator_root(tcx, lhs_inner_ty, hir_uncast) {
                return true;
            }
        }
        PtrKind::BoxedSlice | PtrKind::OptBoxedSlice => {
            if hir_is_supported_boxed_slice_allocator_root(tcx, hir_uncast) {
                return true;
            }
        }
        _ => return true,
    }

    if let hir::ExprKind::Call(..) = hir_expr.kind
        && let Some(output_kind) = hir_callee_output_kind(tcx, sig_decs, ptr_kinds, hir_expr)
        && ptr_kind_supports_box_target(output_kind, target_kind)
    {
        return true;
    }

    if let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_expr.kind
        && let Res::Local(hir_id) = path.res
        && let Some(rhs_kind) = ptr_kinds.get(&hir_id).copied()
        && ptr_kind_supports_box_target(rhs_kind, target_kind)
    {
        return true;
    }

    false
}

fn ptr_kind_supports_box_target(source_kind: PtrKind, target_kind: PtrKind) -> bool {
    source_kind == target_kind || source_kind == target_kind.optional_variant()
}

fn hir_rhs_supports_optional_box_return(
    tcx: TyCtxt<'_>,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    hir_expr: &hir::Expr<'_>,
    target_kind: PtrKind,
) -> bool {
    if !matches!(target_kind, PtrKind::OptBox | PtrKind::OptBoxedSlice) {
        return false;
    }
    if let hir::ExprKind::Call(..) = hir_expr.kind
        && let Some(output_kind) = hir_callee_output_kind(tcx, sig_decs, ptr_kinds, hir_expr)
    {
        return output_kind.optional_variant() == target_kind;
    }
    if let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_expr.kind
        && let Res::Local(hir_id) = path.res
        && let Some(rhs_kind) = ptr_kinds.get(&hir_id).copied()
    {
        return rhs_kind.optional_variant() == target_kind;
    }
    false
}

fn collect_unsupported_box_target_bindings(
    tcx: TyCtxt<'_>,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
) -> FxHashSet<HirId> {
    struct UnsupportedBoxBindingVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        sig_decs: &'a SigDecisions,
        ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
        bindings: FxHashSet<HirId>,
    }

    impl<'tcx> Visitor<'tcx> for UnsupportedBoxBindingVisitor<'_, 'tcx> {
        fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
            if let hir::StmtKind::Let(let_stmt) = stmt.kind
                && let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind
                && let Some(init) = let_stmt.init
                && let Some(kind) = self.ptr_kinds.get(&hir_id).copied()
                && kind.is_owning_box_like()
            {
                let lhs_ty = self.tcx.typeck(hir_id.owner).node_type(hir_id);
                let (lhs_inner_ty, _) = unwrap_ptr_from_mir_ty(lhs_ty).unwrap();
                if !hir_rhs_supports_box_target(
                    self.tcx,
                    self.sig_decs,
                    self.ptr_kinds,
                    init,
                    kind,
                    lhs_inner_ty,
                ) {
                    self.bindings.insert(hir_id);
                }
            }
            intravisit::walk_stmt(self, stmt);
        }

        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = lhs.kind
                && let Res::Local(hir_id) = path.res
                && let Some(kind) = self.ptr_kinds.get(&hir_id).copied()
                && kind.is_owning_box_like()
            {
                let lhs_ty = self.tcx.typeck(expr.hir_id.owner).expr_ty(lhs);
                let (lhs_inner_ty, _) = unwrap_ptr_from_mir_ty(lhs_ty).unwrap();
                if !hir_rhs_supports_box_target(
                    self.tcx,
                    self.sig_decs,
                    self.ptr_kinds,
                    rhs,
                    kind,
                    lhs_inner_ty,
                ) {
                    self.bindings.insert(hir_id);
                }
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut bindings: FxHashSet<HirId> = FxHashSet::default();
    let crate_hir = tcx.hir_crate(());
    for maybe_owner in crate_hir.owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let hir::OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            continue;
        };
        let body = tcx.hir_body(body);
        let mut visitor = UnsupportedBoxBindingVisitor {
            tcx,
            sig_decs,
            ptr_kinds,
            bindings: FxHashSet::default(),
        };
        visitor.visit_expr(body.value);
        bindings.extend(visitor.bindings);
    }
    bindings
}

fn collect_unsupported_box_usage_bindings(
    tcx: TyCtxt<'_>,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    free_like_wrappers: &FxHashSet<LocalDefId>,
    local_raw_param_summaries: &FxHashMap<(LocalDefId, usize), LocalRawParamSummary>,
) -> FxHashSet<HirId> {
    struct UnsupportedBoxUsageVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        sig_decs: &'a SigDecisions,
        ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
        free_like_wrappers: &'a FxHashSet<LocalDefId>,
        local_raw_param_summaries: &'a FxHashMap<(LocalDefId, usize), LocalRawParamSummary>,
        byte_view_roots: FxHashMap<HirId, HirId>,
        returned_alias_roots: FxHashMap<HirId, HirId>,
        bindings: FxHashSet<HirId>,
    }

    impl<'tcx> UnsupportedBoxUsageVisitor<'_, 'tcx> {
        fn owning_root_of(&self, hir_id: HirId) -> Option<HirId> {
            if self
                .ptr_kinds
                .get(&hir_id)
                .is_some_and(PtrKind::is_owning_box_like)
            {
                Some(hir_id)
            } else if let Some(root) = self.returned_alias_roots.get(&hir_id).copied() {
                Some(root)
            } else {
                self.byte_view_roots.get(&hir_id).copied()
            }
        }

        fn maybe_mark_byte_view_alias(
            &mut self,
            lhs_hir_id: HirId,
            lhs_ty: ty::Ty<'tcx>,
            rhs: &'tcx hir::Expr<'tcx>,
        ) {
            let Some((lhs_inner_ty, _)) = unwrap_ptr_from_mir_ty(lhs_ty) else {
                return;
            };
            if !ty_is_byte_sized_raw_inner(lhs_inner_ty) {
                return;
            }
            let Some(rhs_hir_id) = hir_unwrapped_local_id(rhs) else {
                return;
            };
            let Some(root) = self.owning_root_of(rhs_hir_id) else {
                return;
            };
            let rhs_ty = self.tcx.typeck(rhs_hir_id.owner).node_type(rhs_hir_id);
            let Some((rhs_inner_ty, _)) = unwrap_ptr_from_mir_ty(rhs_ty) else {
                return;
            };
            if !ty_is_byte_sized_raw_inner(rhs_inner_ty) || !hir_is_casted_local(rhs, rhs_hir_id) {
                return;
            }
            self.byte_view_roots.insert(lhs_hir_id, root);
            self.bindings.insert(root);
        }

        fn maybe_mark_returned_alias(&mut self, lhs_hir_id: HirId, rhs: &'tcx hir::Expr<'tcx>) {
            let Some(local_callee) = hir_called_local_fn(self.tcx, rhs) else {
                return;
            };
            let hir::ExprKind::Call(_, args) = rhs.kind else {
                return;
            };
            let mut roots = FxHashSet::default();
            for (arg_index, arg) in args.iter().enumerate() {
                let Some(arg_hir_id) = hir_unwrapped_local_id(arg) else {
                    continue;
                };
                let Some(root) = self.owning_root_of(arg_hir_id) else {
                    continue;
                };
                if self
                    .local_raw_param_summaries
                    .get(&(local_callee, arg_index))
                    == Some(&LocalRawParamSummary::ReturnedToBorrowedOutput)
                {
                    roots.insert(root);
                }
            }
            if roots.len() == 1
                && let Some(root) = roots.into_iter().next()
            {
                self.returned_alias_roots.insert(lhs_hir_id, root);
            }
        }

        fn collect_owning_roots_in_expr(&self, expr: &'tcx hir::Expr<'tcx>) -> FxHashSet<HirId> {
            struct RootCollector<'a, 'tcx, 'me> {
                visitor: &'me UnsupportedBoxUsageVisitor<'a, 'tcx>,
                roots: FxHashSet<HirId>,
            }

            impl<'tcx> Visitor<'tcx> for RootCollector<'_, 'tcx, '_> {
                fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
                    if let Some(hir_id) = hir_unwrapped_local_id(expr)
                        && let Some(root) = self.visitor.owning_root_of(hir_id)
                    {
                        self.roots.insert(root);
                    }
                    intravisit::walk_expr(self, expr);
                }
            }

            let mut collector = RootCollector {
                visitor: self,
                roots: FxHashSet::default(),
            };
            collector.visit_expr(expr);
            collector.roots
        }
    }

    impl<'tcx> Visitor<'tcx> for UnsupportedBoxUsageVisitor<'_, 'tcx> {
        fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
            if let hir::StmtKind::Let(let_stmt) = stmt.kind
                && let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind
                && let Some(init) = let_stmt.init
            {
                let lhs_ty = self.tcx.typeck(hir_id.owner).node_type(hir_id);
                self.maybe_mark_byte_view_alias(hir_id, lhs_ty, init);
                self.maybe_mark_returned_alias(hir_id, init);
            }
            intravisit::walk_stmt(self, stmt);
        }

        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = lhs.kind
                && let Res::Local(lhs_hir_id) = path.res
            {
                let lhs_ty = self.tcx.typeck(expr.hir_id.owner).expr_ty(lhs);
                self.maybe_mark_byte_view_alias(lhs_hir_id, lhs_ty, rhs);
                self.maybe_mark_returned_alias(lhs_hir_id, rhs);
            }

            if let Some(local_callee) = hir_called_local_fn(self.tcx, expr)
                && let hir::ExprKind::Call(_, args) = expr.kind
            {
                for (arg_index, arg) in args.iter().enumerate() {
                    let Some(hir_id) = hir_unwrapped_local_id(arg) else {
                        continue;
                    };
                    let Some(root) = self.owning_root_of(hir_id) else {
                        continue;
                    };
                    if !local_callee_arg_preserves_owning_usage(
                        self.sig_decs,
                        self.local_raw_param_summaries,
                        local_callee,
                        arg_index,
                    ) {
                        self.bindings.insert(root);
                    }
                }
            }

            if let Some((hir_id, _)) =
                hir_free_like_arg_local_id(self.tcx, expr, self.free_like_wrappers)
                && let Some(root) = self.owning_root_of(hir_id)
            {
                let is_direct_free = hir_call_matches_foreign_name(self.tcx, expr, "free");
                let direct_box_consume = is_direct_free
                    && hir_id == root
                    && self
                        .ptr_kinds
                        .get(&hir_id)
                        .is_some_and(PtrKind::is_owning_box_like);
                if !direct_box_consume {
                    self.bindings.insert(root);
                }
            } else if let hir::ExprKind::Call(_, args) = expr.kind
                && (hir_call_matches_foreign_name(self.tcx, expr, "free")
                    || hir_called_local_fn(self.tcx, expr)
                        .is_some_and(|def_id| self.free_like_wrappers.contains(&def_id)))
                && let [arg] = args
            {
                self.bindings.extend(self.collect_owning_roots_in_expr(arg));
            }

            intravisit::walk_expr(self, expr);
        }
    }

    let mut bindings = FxHashSet::default();
    let crate_hir = tcx.hir_crate(());
    for maybe_owner in crate_hir.owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let hir::OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            continue;
        };
        let body = tcx.hir_body(body);
        let mut visitor = UnsupportedBoxUsageVisitor {
            tcx,
            sig_decs,
            ptr_kinds,
            free_like_wrappers,
            local_raw_param_summaries,
            byte_view_roots: FxHashMap::default(),
            returned_alias_roots: FxHashMap::default(),
            bindings: FxHashSet::default(),
        };
        visitor.visit_body(body);
        bindings.extend(visitor.bindings);
    }

    bindings
}

fn collect_unsupported_box_usage_subreasons(
    tcx: TyCtxt<'_>,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    free_like_wrappers: &FxHashSet<LocalDefId>,
    local_raw_param_summaries: &FxHashMap<(LocalDefId, usize), LocalRawParamSummary>,
) -> FxHashMap<HirId, Vec<DecisionReason>> {
    struct UsageSubreasonVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        sig_decs: &'a SigDecisions,
        ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
        free_like_wrappers: &'a FxHashSet<LocalDefId>,
        local_raw_param_summaries: &'a FxHashMap<(LocalDefId, usize), LocalRawParamSummary>,
        byte_view_roots: FxHashMap<HirId, HirId>,
        reasons: FxHashMap<HirId, FxHashSet<DecisionReason>>,
    }

    impl<'tcx> UsageSubreasonVisitor<'_, 'tcx> {
        fn record(&mut self, root: HirId, reason: DecisionReason) {
            self.reasons.entry(root).or_default().insert(reason);
        }

        fn owning_root_of(&self, hir_id: HirId) -> Option<HirId> {
            if self
                .ptr_kinds
                .get(&hir_id)
                .is_some_and(PtrKind::is_owning_box_like)
            {
                Some(hir_id)
            } else {
                self.byte_view_roots.get(&hir_id).copied()
            }
        }

        fn maybe_mark_byte_view_alias(
            &mut self,
            lhs_hir_id: HirId,
            lhs_ty: ty::Ty<'tcx>,
            rhs: &'tcx hir::Expr<'tcx>,
        ) {
            let Some((lhs_inner_ty, _)) = unwrap_ptr_from_mir_ty(lhs_ty) else {
                return;
            };
            if !ty_is_byte_sized_raw_inner(lhs_inner_ty) {
                return;
            }
            let Some(rhs_hir_id) = hir_unwrapped_local_id(rhs) else {
                return;
            };
            let Some(root) = self.owning_root_of(rhs_hir_id) else {
                return;
            };
            let rhs_ty = self.tcx.typeck(rhs_hir_id.owner).node_type(rhs_hir_id);
            let Some((rhs_inner_ty, _)) = unwrap_ptr_from_mir_ty(rhs_ty) else {
                return;
            };
            if !ty_is_byte_sized_raw_inner(rhs_inner_ty) || !hir_is_casted_local(rhs, rhs_hir_id) {
                return;
            }
            self.byte_view_roots.insert(lhs_hir_id, root);
            self.record(root, DecisionReason::UnsupportedBoxUsageByteViewAlias);
        }
    }

    impl<'tcx> Visitor<'tcx> for UsageSubreasonVisitor<'_, 'tcx> {
        fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
            if let hir::StmtKind::Let(let_stmt) = stmt.kind
                && let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind
                && let Some(init) = let_stmt.init
            {
                let lhs_ty = self.tcx.typeck(hir_id.owner).node_type(hir_id);
                self.maybe_mark_byte_view_alias(hir_id, lhs_ty, init);
            }
            intravisit::walk_stmt(self, stmt);
        }

        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = lhs.kind
                && let Res::Local(lhs_hir_id) = path.res
            {
                let lhs_ty = self.tcx.typeck(expr.hir_id.owner).expr_ty(lhs);
                self.maybe_mark_byte_view_alias(lhs_hir_id, lhs_ty, rhs);
            }

            if let Some(local_callee) = hir_called_local_fn(self.tcx, expr)
                && let hir::ExprKind::Call(_, args) = expr.kind
            {
                for (arg_index, arg) in args.iter().enumerate() {
                    let Some(hir_id) = hir_unwrapped_local_id(arg) else {
                        continue;
                    };
                    let Some(root) = self.owning_root_of(hir_id) else {
                        continue;
                    };
                    if !local_callee_arg_preserves_owning_usage(
                        self.sig_decs,
                        self.local_raw_param_summaries,
                        local_callee,
                        arg_index,
                    ) {
                        self.record(
                            root,
                            DecisionReason::UnsupportedBoxUsageLocalCalleeNonBorrowOnly,
                        );
                    }
                }
            }

            if let Some((hir_id, _)) =
                hir_free_like_arg_local_id(self.tcx, expr, self.free_like_wrappers)
                && let Some(root) = self.owning_root_of(hir_id)
            {
                let is_direct_free = hir_call_matches_foreign_name(self.tcx, expr, "free");
                let direct_box_consume = is_direct_free
                    && hir_id == root
                    && self
                        .ptr_kinds
                        .get(&hir_id)
                        .is_some_and(PtrKind::is_owning_box_like);
                if !direct_box_consume {
                    self.record(root, DecisionReason::UnsupportedBoxUsageFreeLikeWrapper);
                }
            }

            intravisit::walk_expr(self, expr);
        }
    }

    let mut visitor = UsageSubreasonVisitor {
        tcx,
        sig_decs,
        ptr_kinds,
        free_like_wrappers,
        local_raw_param_summaries,
        byte_view_roots: FxHashMap::default(),
        reasons: FxHashMap::default(),
    };
    for_each_hir_fn_body(tcx, |body, _typeck| visitor.visit_body(body));
    let mut out = FxHashMap::default();
    for (hir_id, reasons) in visitor.reasons {
        let mut reasons = reasons.into_iter().collect::<Vec<_>>();
        reasons.sort_by_key(|reason| reason.as_str());
        out.insert(hir_id, reasons);
    }
    out
}

fn collect_owned_field_free_owner_bindings(
    tcx: TyCtxt<'_>,
    analysis: &Analysis,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    free_like_wrappers: &FxHashSet<LocalDefId>,
) -> FxHashSet<HirId> {
    struct OwnedFieldFreeVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        analysis: &'a Analysis,
        sig_decs: &'a SigDecisions,
        ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
        free_like_wrappers: &'a FxHashSet<LocalDefId>,
        bindings: FxHashSet<HirId>,
    }

    impl<'tcx> Visitor<'tcx> for OwnedFieldFreeVisitor<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            let is_direct_free = hir_call_matches_foreign_name(self.tcx, expr, "free");
            let is_wrapper_free = hir_called_local_fn(self.tcx, expr)
                .is_some_and(|def_id| self.free_like_wrappers.contains(&def_id));
            if (is_direct_free || is_wrapper_free)
                && let hir::ExprKind::Call(_, args) = expr.kind
                && let [arg] = args
            {
                let field_expr = hir_unwrap_casts(arg);
                if let Some(field) = hir_struct_field_slot(self.tcx, field_expr)
                    && ownership_field_ptr_kind(
                        self.tcx,
                        self.analysis,
                        self.sig_decs,
                        self.ptr_kinds,
                        field,
                    ) == Some(PtrKind::OptBox)
                    && let Some(root) = hir_projection_root_local_id(field_expr)
                {
                    self.bindings.insert(root);
                }
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut bindings = FxHashSet::default();
    for_each_hir_fn_body(tcx, |body, _typeck| {
        let mut visitor = OwnedFieldFreeVisitor {
            tcx,
            analysis,
            sig_decs,
            ptr_kinds,
            free_like_wrappers,
            bindings: FxHashSet::default(),
        };
        visitor.visit_body(body);
        bindings.extend(visitor.bindings);
    });
    bindings
}

fn collect_demoted_promoted_fields(
    tcx: TyCtxt<'_>,
    analysis: &Analysis,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
) -> FxHashSet<StructFieldSlot> {
    let mut promoted_fields = analysis.borrow_promotion_result.mutable_fields.clone();
    promoted_fields.extend(
        analysis
            .borrow_promotion_result
            .shared_fields
            .iter()
            .copied(),
    );
    if promoted_fields.is_empty() {
        return FxHashSet::default();
    }
    let mut demoted_fields = collect_struct_shape_demoted_fields(
        tcx,
        &promoted_fields,
        &analysis.borrow_promotion_result.mutable_fields,
        &analysis.struct_copy_result,
        sig_decs,
        ptr_kinds,
    );
    demoted_fields.extend(
        collect_field_conflict_demotion_reasons(tcx, analysis, sig_decs, ptr_kinds)
            .keys()
            .copied(),
    );

    demoted_fields
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[allow(dead_code)]
enum ConflictDemotionReason {
    ActiveBorrowOverlap,
    LocalAssignmentWhileBorrowed,
    ConflictingReborrow,
    MutableFieldCopy,
    RawPointeeFieldMove,
    RawFieldPointerProjection,
    RawStorageAllocator,
    RawStoragePointer,
    RawBindingFromField,
    RawLocalCallArg,
    RawUnknownCallArg,
}

impl ConflictDemotionReason {
    #[allow(dead_code)]
    const ALL: [Self; 11] = [
        Self::ActiveBorrowOverlap,
        Self::LocalAssignmentWhileBorrowed,
        Self::ConflictingReborrow,
        Self::MutableFieldCopy,
        Self::RawPointeeFieldMove,
        Self::RawFieldPointerProjection,
        Self::RawStorageAllocator,
        Self::RawStoragePointer,
        Self::RawBindingFromField,
        Self::RawLocalCallArg,
        Self::RawUnknownCallArg,
    ];

    #[allow(dead_code)]
    fn as_str(self) -> &'static str {
        match self {
            Self::ActiveBorrowOverlap => "active_borrow_overlap",
            Self::LocalAssignmentWhileBorrowed => "local_assignment_while_borrowed",
            Self::ConflictingReborrow => "conflicting_reborrow",
            Self::MutableFieldCopy => "mutable_field_copy",
            Self::RawPointeeFieldMove => "raw_pointee_field_move",
            Self::RawFieldPointerProjection => "raw_field_pointer_projection",
            Self::RawStorageAllocator => "raw_storage_allocator",
            Self::RawStoragePointer => "raw_storage_pointer",
            Self::RawBindingFromField => "raw_binding_from_field",
            Self::RawLocalCallArg => "raw_local_call_arg",
            Self::RawUnknownCallArg => "raw_unknown_call_arg",
        }
    }
}

fn collect_field_conflict_demotion_reasons(
    tcx: TyCtxt<'_>,
    analysis: &Analysis,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
) -> FxHashMap<StructFieldSlot, FxHashSet<ConflictDemotionReason>> {
    let mut promoted_fields = analysis.borrow_promotion_result.mutable_fields.clone();
    promoted_fields.extend(
        analysis
            .borrow_promotion_result
            .shared_fields
            .iter()
            .copied(),
    );
    if promoted_fields.is_empty() {
        return FxHashMap::default();
    }

    struct FieldBorrowConflictVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        typeck: &'tcx rustc_middle::ty::TypeckResults<'tcx>,
        sig_decs: &'a SigDecisions,
        ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
        promoted_fields: &'a FxHashSet<StructFieldSlot>,
        mutable_fields: &'a FxHashSet<StructFieldSlot>,
        allocator_locals: FxHashSet<HirId>,
        active_borrows: FxHashMap<HirId, FxHashMap<StructFieldSlot, bool>>,
        ignored_borrow_exprs: FxHashSet<HirId>,
        conflict_reasons: FxHashMap<StructFieldSlot, FxHashSet<ConflictDemotionReason>>,
    }

    impl<'tcx> FieldBorrowConflictVisitor<'_, 'tcx> {
        fn record_conflict(&mut self, field: StructFieldSlot, reason: ConflictDemotionReason) {
            if self.promoted_fields.contains(&field) {
                self.conflict_reasons
                    .entry(field)
                    .or_default()
                    .insert(reason);
            }
        }

        fn record_conflicts(
            &mut self,
            fields: impl IntoIterator<Item = StructFieldSlot>,
            reason: ConflictDemotionReason,
        ) {
            for field in fields {
                self.record_conflict(field, reason);
            }
        }

        fn record_field_borrow(&mut self, field: StructFieldSlot, rhs: &'tcx hir::Expr<'tcx>) {
            if !self.promoted_fields.contains(&field) {
                return;
            }
            let Some((local, new_mut)) = hir_raw_addr_local(rhs) else {
                return;
            };
            self.ignored_borrow_exprs.insert(rhs.hir_id);
            let conflicting_fields = {
                let fields = self.active_borrows.entry(local).or_default();
                let has_conflict = !fields.is_empty()
                    && (new_mut || fields.values().any(|existing_mut| *existing_mut));
                let conflicting_fields = if has_conflict {
                    fields.keys().copied().collect::<Vec<_>>()
                } else {
                    Vec::new()
                };
                fields.insert(field, new_mut);
                conflicting_fields
            };
            if !conflicting_fields.is_empty() {
                self.record_conflicts(
                    conflicting_fields,
                    ConflictDemotionReason::ActiveBorrowOverlap,
                );
                self.record_conflict(field, ConflictDemotionReason::ActiveBorrowOverlap);
            }
        }

        fn record_local_assignment(&mut self, lhs: &'tcx hir::Expr<'tcx>) {
            let Some(local) = hir_unwrapped_local_id(lhs) else {
                return;
            };
            if let Some(fields) = self.active_borrows.get(&local) {
                self.record_conflicts(
                    fields.keys().copied().collect::<Vec<_>>(),
                    ConflictDemotionReason::LocalAssignmentWhileBorrowed,
                );
            }
        }

        fn record_conflicting_reborrow(&mut self, expr: &'tcx hir::Expr<'tcx>) {
            if self.ignored_borrow_exprs.contains(&expr.hir_id) {
                return;
            }
            let Some((local, new_mut)) = hir_addr_local(expr) else {
                return;
            };
            if let Some(fields) = self.active_borrows.get(&local)
                && (new_mut || fields.values().any(|existing_mut| *existing_mut))
            {
                self.record_conflicts(
                    fields.keys().copied().collect::<Vec<_>>(),
                    ConflictDemotionReason::ConflictingReborrow,
                );
            }
        }

        fn clear_field_borrow(&mut self, field: StructFieldSlot) {
            for fields in self.active_borrows.values_mut() {
                fields.remove(&field);
            }
        }

        fn record_mutable_field_copy_to_slot(
            &mut self,
            lhs_field: StructFieldSlot,
            rhs: &'tcx hir::Expr<'tcx>,
        ) {
            if !self.promoted_fields.contains(&lhs_field) {
                return;
            }
            let Some(rhs_field) = hir_struct_field_slot(self.tcx, rhs) else {
                return;
            };
            if !self.mutable_fields.contains(&rhs_field) {
                return;
            }
            self.record_conflict(lhs_field, ConflictDemotionReason::MutableFieldCopy);
            self.record_conflict(rhs_field, ConflictDemotionReason::MutableFieldCopy);
        }

        fn promoted_field_slots_in_expr(
            &self,
            expr: &'tcx hir::Expr<'tcx>,
        ) -> FxHashSet<StructFieldSlot> {
            struct FieldUseVisitor<'a, 'tcx> {
                tcx: TyCtxt<'tcx>,
                promoted_fields: &'a FxHashSet<StructFieldSlot>,
                fields: FxHashSet<StructFieldSlot>,
            }

            impl<'tcx> Visitor<'tcx> for FieldUseVisitor<'_, 'tcx> {
                fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
                    if let Some(field) = hir_struct_field_slot(self.tcx, expr)
                        && self.promoted_fields.contains(&field)
                    {
                        self.fields.insert(field);
                    }
                    intravisit::walk_expr(self, expr);
                }
            }

            let mut visitor = FieldUseVisitor {
                tcx: self.tcx,
                promoted_fields: self.promoted_fields,
                fields: FxHashSet::default(),
            };
            visitor.visit_expr(expr);
            visitor.fields
        }

        fn record_promoted_fields_in_expr(
            &mut self,
            expr: &'tcx hir::Expr<'tcx>,
            reason: ConflictDemotionReason,
        ) {
            self.record_conflicts(self.promoted_field_slots_in_expr(expr), reason);
        }

        fn record_moved_mutable_fields_from_raw_pointee_arg(
            &mut self,
            expr: &'tcx hir::Expr<'tcx>,
        ) {
            struct RawPointeeFieldMoveVisitor<'a, 'tcx> {
                tcx: TyCtxt<'tcx>,
                typeck: &'tcx rustc_middle::ty::TypeckResults<'tcx>,
                promoted_fields: &'a FxHashSet<StructFieldSlot>,
                mutable_fields: &'a FxHashSet<StructFieldSlot>,
                fields: FxHashSet<StructFieldSlot>,
            }

            impl<'tcx> RawPointeeFieldMoveVisitor<'_, 'tcx> {
                fn expr_contains_raw_deref(&self, expr: &'tcx hir::Expr<'tcx>) -> bool {
                    struct RawDerefVisitor<'a, 'tcx> {
                        typeck: &'a rustc_middle::ty::TypeckResults<'tcx>,
                        found: bool,
                    }

                    impl<'tcx> Visitor<'tcx> for RawDerefVisitor<'_, 'tcx> {
                        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
                            if self.found {
                                return;
                            }
                            if let hir::ExprKind::Unary(hir::UnOp::Deref, inner) = expr.kind
                                && self.typeck.expr_ty(inner).is_raw_ptr()
                            {
                                self.found = true;
                                return;
                            }
                            intravisit::walk_expr(self, expr);
                        }
                    }

                    let mut visitor = RawDerefVisitor {
                        typeck: self.typeck,
                        found: false,
                    };
                    visitor.visit_expr(expr);
                    visitor.found
                }
            }

            impl<'tcx> Visitor<'tcx> for RawPointeeFieldMoveVisitor<'_, 'tcx> {
                fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
                    if let Some(field) = hir_struct_field_slot(self.tcx, expr)
                        && self.promoted_fields.contains(&field)
                        && self.mutable_fields.contains(&field)
                        && let hir::ExprKind::Field(base, _) = expr.kind
                        && self.expr_contains_raw_deref(base)
                    {
                        self.fields.insert(field);
                    }
                    intravisit::walk_expr(self, expr);
                }
            }

            let mut visitor = RawPointeeFieldMoveVisitor {
                tcx: self.tcx,
                typeck: self.typeck,
                promoted_fields: self.promoted_fields,
                mutable_fields: self.mutable_fields,
                fields: FxHashSet::default(),
            };
            visitor.visit_expr(expr);
            self.record_conflicts(visitor.fields, ConflictDemotionReason::RawPointeeFieldMove);
        }

        fn expr_contains_allocator_call(&self, expr: &'tcx hir::Expr<'tcx>) -> bool {
            struct AllocCallVisitor {
                found: bool,
            }

            impl<'tcx> Visitor<'tcx> for AllocCallVisitor {
                fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
                    if self.found {
                        return;
                    }
                    if matches!(
                        hir_call_name(expr),
                        Some(name)
                            if name == Symbol::intern("malloc")
                                || name == Symbol::intern("calloc")
                                || name == Symbol::intern("realloc")
                                || name == Symbol::intern("strdup")
                    ) {
                        self.found = true;
                        return;
                    }
                    intravisit::walk_expr(self, expr);
                }
            }

            let mut visitor = AllocCallVisitor { found: false };
            visitor.visit_expr(expr);
            visitor.found
        }

        fn expr_is_null_constructor(&self, expr: &'tcx hir::Expr<'tcx>) -> bool {
            matches!(
                hir_call_name(expr),
                Some(name)
                    if name == Symbol::intern("null") || name == Symbol::intern("null_mut")
            )
        }

        fn expr_is_allocator_root_source(&self, expr: &'tcx hir::Expr<'tcx>) -> bool {
            self.expr_contains_allocator_call(expr)
                || hir_unwrapped_local_id(expr)
                    .is_some_and(|hir_id| self.allocator_locals.contains(&hir_id))
        }

        fn raw_field_storage_reason(
            &self,
            field: StructFieldSlot,
            expr: &'tcx hir::Expr<'tcx>,
        ) -> Option<ConflictDemotionReason> {
            if self.expr_is_null_constructor(expr) || hir_raw_addr_local(expr).is_some() {
                return None;
            }
            if self.expr_is_allocator_root_source(expr) {
                return Some(ConflictDemotionReason::RawStorageAllocator);
            }
            if self.raw_storage_source_loses_mutability(field, expr) {
                return Some(ConflictDemotionReason::RawStoragePointer);
            }
            None
        }

        fn raw_storage_source_loses_mutability(
            &self,
            field: StructFieldSlot,
            expr: &'tcx hir::Expr<'tcx>,
        ) -> bool {
            if !self.mutable_fields.contains(&field) {
                return false;
            }
            if let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_unwrap_cast(expr).kind
                && let Res::Local(hir_id) = path.res
            {
                return matches!(
                    self.ptr_kinds.get(&hir_id),
                    Some(
                        PtrKind::Ref(false)
                            | PtrKind::OptRef(false)
                            | PtrKind::Slice(false)
                            | PtrKind::SliceCursor(false)
                    )
                );
            }
            if let Some(callee_did) = hir_called_local_fn(self.tcx, expr)
                && let Some(sig_dec) = self.sig_decs.data.get(&callee_did)
            {
                return matches!(
                    sig_dec.output_dec,
                    Some(
                        PtrKind::Ref(false)
                            | PtrKind::OptRef(false)
                            | PtrKind::Slice(false)
                            | PtrKind::SliceCursor(false)
                    )
                );
            }
            false
        }

        fn record_allocator_binding(&mut self, hir_id: HirId, expr: &'tcx hir::Expr<'tcx>) {
            if self.expr_contains_allocator_call(expr)
                || hir_unwrapped_local_id(expr)
                    .is_some_and(|rhs_id| self.allocator_locals.contains(&rhs_id))
            {
                self.allocator_locals.insert(hir_id);
            }
        }

        fn record_raw_field_storage(&mut self, field: StructFieldSlot, rhs: &'tcx hir::Expr<'tcx>) {
            if let Some(reason) = self.raw_field_storage_reason(field, rhs) {
                self.record_conflict(field, reason);
            }
        }

        fn record_raw_field_binding(&mut self, binding_hir_id: HirId, init: &'tcx hir::Expr<'tcx>) {
            self.record_allocator_binding(binding_hir_id, init);
            if unwrap_ptr_from_mir_ty(self.typeck.node_type(binding_hir_id)).is_none() {
                return;
            }
            if let Some(kind) = self.ptr_kinds.get(&binding_hir_id)
                && !matches!(kind, PtrKind::Raw(_))
            {
                if kind.is_mut() {
                    self.record_promoted_fields_in_expr(
                        init,
                        ConflictDemotionReason::RawBindingFromField,
                    );
                }
                return;
            }
            self.record_promoted_fields_in_expr(init, ConflictDemotionReason::RawBindingFromField);
        }

        fn record_raw_field_call(&mut self, expr: &'tcx hir::Expr<'tcx>) {
            let hir::ExprKind::Call(_, args) = hir_unwrap_casts(expr).kind else {
                return;
            };
            for arg in args.iter() {
                self.record_moved_mutable_fields_from_raw_pointee_arg(arg);
            }
        }

        fn record_raw_field_pointer_projection(&mut self, expr: &'tcx hir::Expr<'tcx>) {
            let hir::ExprKind::MethodCall(seg, receiver, _, _) = expr.kind else {
                return;
            };
            if !matches!(seg.ident.name.as_str(), "wrapping_offset" | "sub") {
                return;
            }
            self.record_promoted_fields_in_expr(
                receiver,
                ConflictDemotionReason::RawFieldPointerProjection,
            );
        }

        fn record_mutable_field_copy(
            &mut self,
            lhs: &'tcx hir::Expr<'tcx>,
            rhs: &'tcx hir::Expr<'tcx>,
        ) {
            let Some(lhs_field) = hir_struct_field_slot(self.tcx, lhs) else {
                return;
            };
            self.record_mutable_field_copy_to_slot(lhs_field, rhs);
        }
    }

    impl<'tcx> Visitor<'tcx> for FieldBorrowConflictVisitor<'_, 'tcx> {
        fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
            if let hir::StmtKind::Let(let_stmt) = stmt.kind
                && let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind
                && let Some(init) = let_stmt.init
            {
                self.record_raw_field_binding(hir_id, init);
            }
            intravisit::walk_stmt(self, stmt);
        }

        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            self.record_conflicting_reborrow(expr);
            self.record_raw_field_pointer_projection(expr);
            match expr.kind {
                hir::ExprKind::Struct(qpath, fields, _) => {
                    if let Some(struct_did) = hir_local_struct_did_from_qpath(qpath) {
                        for field in fields {
                            if let Some(field_index) =
                                hir_field_index_by_name(self.tcx, struct_did, field.ident.name)
                            {
                                let field_slot = StructFieldSlot {
                                    struct_did,
                                    field_index,
                                };
                                self.record_mutable_field_copy_to_slot(field_slot, field.expr);
                                self.record_field_borrow(field_slot, field.expr);
                                self.record_raw_field_storage(field_slot, field.expr);
                            }
                        }
                    }
                }
                hir::ExprKind::Assign(lhs, rhs, _) => {
                    if let Some(lhs_hir_id) = hir_unwrapped_local_id(lhs) {
                        self.record_allocator_binding(lhs_hir_id, rhs);
                    }
                    self.record_mutable_field_copy(lhs, rhs);
                    self.record_local_assignment(lhs);
                    if let Some(field) = hir_struct_field_slot(self.tcx, lhs) {
                        self.clear_field_borrow(field);
                        self.record_field_borrow(field, rhs);
                        self.record_raw_field_storage(field, rhs);
                    }
                }
                hir::ExprKind::AssignOp(_, lhs, _) => {
                    self.record_local_assignment(lhs);
                }
                hir::ExprKind::Call(_, _) => self.record_raw_field_call(expr),
                _ => {}
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut conflict_reasons: FxHashMap<StructFieldSlot, FxHashSet<ConflictDemotionReason>> =
        FxHashMap::default();
    for_each_hir_fn_body(tcx, |body, typeck| {
        let mut visitor = FieldBorrowConflictVisitor {
            tcx,
            typeck,
            sig_decs,
            ptr_kinds,
            promoted_fields: &promoted_fields,
            mutable_fields: &analysis.borrow_promotion_result.mutable_fields,
            allocator_locals: FxHashSet::default(),
            active_borrows: FxHashMap::default(),
            ignored_borrow_exprs: FxHashSet::default(),
            conflict_reasons: FxHashMap::default(),
        };
        visitor.visit_body(body);
        for (field, reasons) in visitor.conflict_reasons {
            conflict_reasons.entry(field).or_default().extend(reasons);
        }
    });

    conflict_reasons
}

fn for_each_hir_fn_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    mut f: impl FnMut(&'tcx hir::Body<'tcx>, &'tcx rustc_middle::ty::TypeckResults<'tcx>),
) {
    for maybe_owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let body_id = match owner.node() {
            hir::OwnerNode::Item(item) => match item.kind {
                hir::ItemKind::Fn { body, .. } => body,
                _ => continue,
            },
            hir::OwnerNode::ImplItem(item) => match item.kind {
                hir::ImplItemKind::Fn(_, body) => body,
                _ => continue,
            },
            _ => continue,
        };
        let body = tcx.hir_body(body_id);
        f(body, tcx.typeck_body(body.id()));
    }
}

fn collect_raw_field_source_bindings(
    tcx: TyCtxt<'_>,
    analysis: &Analysis,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    demoted_fields: &FxHashSet<StructFieldSlot>,
) -> (FxHashSet<HirId>, FxHashSet<LocalDefId>) {
    let mut promoted_fields = analysis.borrow_promotion_result.mutable_fields.clone();
    promoted_fields.extend(
        analysis
            .borrow_promotion_result
            .shared_fields
            .iter()
            .copied(),
    );

    struct DemotedFieldSourceVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        typeck: &'tcx rustc_middle::ty::TypeckResults<'tcx>,
        analysis: &'a Analysis,
        sig_decs: &'a SigDecisions,
        ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
        promoted_fields: &'a FxHashSet<StructFieldSlot>,
        demoted_fields: &'a FxHashSet<StructFieldSlot>,
        bindings: FxHashSet<HirId>,
        callees: FxHashSet<LocalDefId>,
    }

    impl<'tcx> DemotedFieldSourceVisitor<'_, 'tcx> {
        fn field_stays_raw(&self, field: StructFieldSlot) -> bool {
            if scalar_owning_raw_field_inner_ty(self.tcx, self.analysis, field).is_some() {
                return ownership_field_ptr_kind(
                    self.tcx,
                    self.analysis,
                    self.sig_decs,
                    self.ptr_kinds,
                    field,
                )
                .is_none();
            }
            if ownership_field_ptr_kind(
                self.tcx,
                self.analysis,
                self.sig_decs,
                self.ptr_kinds,
                field,
            )
            .is_some()
            {
                return false;
            }
            if self.demoted_fields.contains(&field) {
                return true;
            }
            if self.promoted_fields.contains(&field) {
                return false;
            }
            hir_field_is_raw_ptr(self.tcx, field)
        }

        fn record_rhs(&mut self, rhs: &'tcx hir::Expr<'tcx>) {
            if let Some(callee_did) = hir_called_local_fn(self.tcx, rhs)
                && self.typeck.expr_ty_adjusted(rhs).is_raw_ptr()
            {
                self.callees.insert(callee_did);
            }
            if let Some(hir_id) = hir_unwrapped_local_id(rhs)
                && unwrap_ptr_from_mir_ty(self.tcx.typeck(hir_id.owner).node_type(hir_id)).is_some()
            {
                self.bindings.insert(hir_id);
            }
        }
    }

    impl<'tcx> Visitor<'tcx> for DemotedFieldSourceVisitor<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            match expr.kind {
                hir::ExprKind::Struct(qpath, fields, _) => {
                    if let Some(struct_did) = hir_local_struct_did_from_qpath(qpath)
                        .or_else(|| hir_local_struct_did_from_ty(self.typeck.expr_ty(expr)))
                    {
                        for field in fields {
                            if let Some(field_index) =
                                hir_field_index_by_name(self.tcx, struct_did, field.ident.name)
                            {
                                let slot = StructFieldSlot {
                                    struct_did,
                                    field_index,
                                };
                                if self.field_stays_raw(slot) {
                                    self.record_rhs(field.expr);
                                }
                            }
                        }
                    }
                }
                hir::ExprKind::Assign(lhs, rhs, _) => {
                    if let Some(slot) = hir_struct_field_slot(self.tcx, lhs)
                        && self.field_stays_raw(slot)
                    {
                        self.record_rhs(rhs);
                    }
                }
                _ => {}
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut bindings = FxHashSet::default();
    let mut callees = FxHashSet::default();
    for_each_hir_fn_body(tcx, |body, typeck| {
        let mut visitor = DemotedFieldSourceVisitor {
            tcx,
            typeck,
            analysis,
            sig_decs,
            ptr_kinds,
            promoted_fields: &promoted_fields,
            demoted_fields,
            bindings: FxHashSet::default(),
            callees: FxHashSet::default(),
        };
        visitor.visit_body(body);
        bindings.extend(visitor.bindings);
        callees.extend(visitor.callees);
    });
    (bindings, callees)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum OwnershipFieldBlockReason {
    NonRawFieldType,
    NonScalarPointee,
    CVoidOrFilePointee,
    UnsupportedStructLiteralRhs,
    UnsupportedAssignmentRhs,
    UnsupportedCallRhs,
    UnsupportedRawLocalSource,
    AllocatorSizeMismatch,
    ReallocOrBufferPattern,
    CStringOrStrFunctionPattern,
}

impl OwnershipFieldBlockReason {
    const ALL: [Self; 10] = [
        Self::NonRawFieldType,
        Self::NonScalarPointee,
        Self::CVoidOrFilePointee,
        Self::UnsupportedStructLiteralRhs,
        Self::UnsupportedAssignmentRhs,
        Self::UnsupportedCallRhs,
        Self::UnsupportedRawLocalSource,
        Self::AllocatorSizeMismatch,
        Self::ReallocOrBufferPattern,
        Self::CStringOrStrFunctionPattern,
    ];

    #[allow(dead_code)]
    fn as_str(self) -> &'static str {
        match self {
            Self::NonRawFieldType => "non_raw_field_type",
            Self::NonScalarPointee => "non_scalar_pointee",
            Self::CVoidOrFilePointee => "c_void_or_file_pointee",
            Self::UnsupportedStructLiteralRhs => "unsupported_struct_literal_rhs",
            Self::UnsupportedAssignmentRhs => "unsupported_assignment_rhs",
            Self::UnsupportedCallRhs => "unsupported_call_rhs",
            Self::UnsupportedRawLocalSource => "unsupported_raw_local_source",
            Self::AllocatorSizeMismatch => "allocator_size_mismatch",
            Self::ReallocOrBufferPattern => "realloc_or_buffer_pattern",
            Self::CStringOrStrFunctionPattern => "cstring_or_str_function_pattern",
        }
    }
}

#[cfg(test)]
#[derive(Default, Debug)]
struct OwnershipFieldDiagnostics {
    total: usize,
    selected_opt_box: usize,
    blocked_total: usize,
    block_reason_counts: FxHashMap<OwnershipFieldBlockReason, usize>,
}

#[cfg(test)]
impl OwnershipFieldDiagnostics {
    fn record_blocked(&mut self, reasons: impl IntoIterator<Item = OwnershipFieldBlockReason>) {
        self.blocked_total += 1;
        let mut saw_reason = false;
        for reason in reasons {
            saw_reason = true;
            *self.block_reason_counts.entry(reason).or_default() += 1;
        }
        if !saw_reason {
            *self
                .block_reason_counts
                .entry(OwnershipFieldBlockReason::UnsupportedAssignmentRhs)
                .or_default() += 1;
        }
    }
}

fn ownership_field_ptr_kind<'tcx>(
    tcx: TyCtxt<'tcx>,
    analysis: &Analysis,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    field: StructFieldSlot,
) -> Option<PtrKind> {
    let inner_ty = scalar_owning_raw_field_inner_ty(tcx, analysis, field)?;
    if field_has_unsupported_opt_box_rhs(tcx, sig_decs, ptr_kinds, field, inner_ty) {
        return None;
    }
    Some(PtrKind::OptBox)
}

fn scalar_owning_raw_field_inner_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    analysis: &Analysis,
    field: StructFieldSlot,
) -> Option<ty::Ty<'tcx>> {
    owning_struct_field_scalar_inner_ty(tcx, analysis, field)?.ok()
}

fn owning_struct_field_scalar_inner_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    analysis: &Analysis,
    field: StructFieldSlot,
) -> Option<Result<ty::Ty<'tcx>, OwnershipFieldBlockReason>> {
    if !struct_field_is_exactly_owning(analysis, field) {
        return None;
    }

    let struct_ty = tcx.type_of(field.struct_did).skip_binder();
    let ty::TyKind::Adt(adt_def, args) = struct_ty.kind() else {
        return Some(Err(OwnershipFieldBlockReason::NonRawFieldType));
    };
    let Some(field_ty) = adt_def
        .all_fields()
        .nth(field.field_index)
        .map(|field| field.ty(tcx, args))
    else {
        return Some(Err(OwnershipFieldBlockReason::NonRawFieldType));
    };
    let ty::TyKind::RawPtr(inner_ty, _) = field_ty.kind() else {
        return Some(Err(OwnershipFieldBlockReason::NonRawFieldType));
    };
    if inner_ty.is_c_void(tcx) || utils::file::contains_file_ty(*inner_ty, tcx) {
        return Some(Err(OwnershipFieldBlockReason::CVoidOrFilePointee));
    }
    if matches!(
        inner_ty.kind(),
        ty::TyKind::RawPtr(..) | ty::TyKind::Ref(..) | ty::TyKind::Slice(_) | ty::TyKind::Array(..)
    ) {
        return Some(Err(OwnershipFieldBlockReason::NonScalarPointee));
    }
    Some(Ok(*inner_ty))
}

fn struct_field_is_exactly_owning(analysis: &Analysis, field: StructFieldSlot) -> bool {
    let Some(ownership_schemes) = analysis.ownership_schemes.as_ref() else {
        return false;
    };
    let field_ownership =
        ownership_schemes.struct_field_result(&field.struct_did.to_def_id(), field.field_index);
    field_ownership.len() == 1
        && field_ownership
            .first()
            .is_some_and(crate::analyses::ownership::Ownership::is_owning)
}

fn field_has_unsupported_opt_box_rhs<'tcx>(
    tcx: TyCtxt<'tcx>,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    target_field: StructFieldSlot,
    lhs_inner_ty: ty::Ty<'tcx>,
) -> bool {
    struct FieldBoxTargetVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        sig_decs: &'a SigDecisions,
        ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
        target_field: StructFieldSlot,
        lhs_inner_ty: ty::Ty<'tcx>,
        found_unsupported: bool,
    }

    impl<'tcx> FieldBoxTargetVisitor<'_, 'tcx> {
        fn rhs_supported(&self, rhs: &'tcx hir::Expr<'tcx>) -> bool {
            if hir_rhs_supports_box_target(
                self.tcx,
                self.sig_decs,
                self.ptr_kinds,
                rhs,
                PtrKind::OptBox,
                self.lhs_inner_ty,
            ) {
                return true;
            }
            hir_unwrapped_local_id(rhs).is_some_and(|hir_id| {
                matches!(self.ptr_kinds.get(&hir_id), Some(PtrKind::Raw(_)))
                    && raw_local_has_supported_scalar_box_source(
                        self.tcx,
                        self.sig_decs,
                        self.ptr_kinds,
                        hir_id,
                        self.lhs_inner_ty,
                    )
            })
        }
    }

    impl<'tcx> Visitor<'tcx> for FieldBoxTargetVisitor<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if self.found_unsupported {
                return;
            }
            match expr.kind {
                hir::ExprKind::Struct(qpath, fields, _) => {
                    if let Some(struct_did) = hir_local_struct_did_from_qpath(qpath) {
                        for field in fields {
                            if let Some(field_index) =
                                hir_field_index_by_name(self.tcx, struct_did, field.ident.name)
                            {
                                let slot = StructFieldSlot {
                                    struct_did,
                                    field_index,
                                };
                                if slot == self.target_field && !self.rhs_supported(field.expr) {
                                    self.found_unsupported = true;
                                    return;
                                }
                            }
                        }
                    }
                }
                hir::ExprKind::Assign(lhs, rhs, _) => {
                    if hir_struct_field_slot(self.tcx, lhs) == Some(self.target_field)
                        && !self.rhs_supported(rhs)
                    {
                        self.found_unsupported = true;
                        return;
                    }
                }
                _ => {}
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut found_unsupported = false;
    for_each_hir_fn_body(tcx, |body, _typeck| {
        if found_unsupported {
            return;
        }
        let mut visitor = FieldBoxTargetVisitor {
            tcx,
            sig_decs,
            ptr_kinds,
            target_field,
            lhs_inner_ty,
            found_unsupported: false,
        };
        visitor.visit_body(body);
        found_unsupported |= visitor.found_unsupported;
    });
    found_unsupported
}

fn collect_ownership_field_rhs_block_reasons<'tcx>(
    tcx: TyCtxt<'tcx>,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    target_fields: &FxHashMap<StructFieldSlot, ty::Ty<'tcx>>,
) -> FxHashMap<StructFieldSlot, FxHashSet<OwnershipFieldBlockReason>> {
    struct FieldBoxTargetVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        sig_decs: &'a SigDecisions,
        ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
        target_fields: &'a FxHashMap<StructFieldSlot, ty::Ty<'tcx>>,
        reasons: FxHashMap<StructFieldSlot, FxHashSet<OwnershipFieldBlockReason>>,
    }

    impl<'tcx> FieldBoxTargetVisitor<'_, 'tcx> {
        fn record_rhs(
            &mut self,
            field: StructFieldSlot,
            rhs: &'tcx hir::Expr<'tcx>,
            fallback: OwnershipFieldBlockReason,
        ) {
            let Some(lhs_inner_ty) = self.target_fields.get(&field).copied() else {
                return;
            };
            if let Some(reason) = opt_box_rhs_block_reason(
                self.tcx,
                self.sig_decs,
                self.ptr_kinds,
                rhs,
                lhs_inner_ty,
                fallback,
            ) {
                self.reasons.entry(field).or_default().insert(reason);
            }
        }
    }

    impl<'tcx> Visitor<'tcx> for FieldBoxTargetVisitor<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            match expr.kind {
                hir::ExprKind::Struct(qpath, fields, _) => {
                    if let Some(struct_did) = hir_local_struct_did_from_qpath(qpath) {
                        for field in fields {
                            if let Some(field_index) =
                                hir_field_index_by_name(self.tcx, struct_did, field.ident.name)
                            {
                                let slot = StructFieldSlot {
                                    struct_did,
                                    field_index,
                                };
                                if self.target_fields.contains_key(&slot) {
                                    self.record_rhs(
                                        slot,
                                        field.expr,
                                        OwnershipFieldBlockReason::UnsupportedStructLiteralRhs,
                                    );
                                }
                            }
                        }
                    }
                }
                hir::ExprKind::Assign(lhs, rhs, _) => {
                    if let Some(field) = hir_struct_field_slot(self.tcx, lhs)
                        && self.target_fields.contains_key(&field)
                    {
                        self.record_rhs(
                            field,
                            rhs,
                            OwnershipFieldBlockReason::UnsupportedAssignmentRhs,
                        );
                    }
                }
                _ => {}
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut reasons: FxHashMap<StructFieldSlot, FxHashSet<OwnershipFieldBlockReason>> =
        FxHashMap::default();
    for_each_hir_fn_body(tcx, |body, _typeck| {
        let mut visitor = FieldBoxTargetVisitor {
            tcx,
            sig_decs,
            ptr_kinds,
            target_fields,
            reasons: FxHashMap::default(),
        };
        visitor.visit_body(body);
        for (field, field_reasons) in visitor.reasons {
            reasons.entry(field).or_default().extend(field_reasons);
        }
    });
    reasons
}

fn opt_box_rhs_block_reason<'tcx>(
    tcx: TyCtxt<'tcx>,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    rhs: &'tcx hir::Expr<'tcx>,
    lhs_inner_ty: ty::Ty<'tcx>,
    fallback: OwnershipFieldBlockReason,
) -> Option<OwnershipFieldBlockReason> {
    if hir_rhs_supports_box_target(tcx, sig_decs, ptr_kinds, rhs, PtrKind::OptBox, lhs_inner_ty) {
        return None;
    }
    if let Some(hir_id) = hir_unwrapped_local_id(rhs)
        && matches!(ptr_kinds.get(&hir_id), Some(PtrKind::Raw(_)))
    {
        if raw_local_has_supported_scalar_box_source(tcx, sig_decs, ptr_kinds, hir_id, lhs_inner_ty)
        {
            return None;
        }
        return Some(
            raw_local_scalar_box_source_block_reason(
                tcx,
                sig_decs,
                ptr_kinds,
                hir_id,
                lhs_inner_ty,
            )
            .unwrap_or(OwnershipFieldBlockReason::UnsupportedRawLocalSource),
        );
    }
    Some(direct_opt_box_rhs_block_reason(
        tcx,
        lhs_inner_ty,
        rhs,
        fallback,
    ))
}

fn direct_opt_box_rhs_block_reason<'tcx>(
    tcx: TyCtxt<'tcx>,
    lhs_inner_ty: ty::Ty<'tcx>,
    rhs: &'tcx hir::Expr<'tcx>,
    fallback: OwnershipFieldBlockReason,
) -> OwnershipFieldBlockReason {
    let Some(name) = hir_call_name(rhs) else {
        return fallback;
    };
    if call_name_is_cstring_or_str_pattern(name) {
        return OwnershipFieldBlockReason::CStringOrStrFunctionPattern;
    }
    if call_name_is_realloc_or_buffer_pattern(name) {
        return OwnershipFieldBlockReason::ReallocOrBufferPattern;
    }
    if call_name_is_libc_allocator(name)
        && !hir_supports_scalar_box_allocator_root(tcx, lhs_inner_ty, rhs)
    {
        return OwnershipFieldBlockReason::AllocatorSizeMismatch;
    }
    OwnershipFieldBlockReason::UnsupportedCallRhs
}

fn call_name_is_libc_allocator(name: Symbol) -> bool {
    matches!(name.as_str(), "malloc" | "calloc" | "realloc")
}

fn call_name_is_realloc_or_buffer_pattern(name: Symbol) -> bool {
    let name = name.as_str();
    name.contains("realloc") || name.contains("allocarray")
}

fn call_name_is_cstring_or_str_pattern(name: Symbol) -> bool {
    let name = name.as_str();
    name.starts_with("str") || name.contains("_str") || name.contains("cstr")
}

fn raw_local_scalar_box_source_block_reason<'tcx>(
    tcx: TyCtxt<'tcx>,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    target_hir_id: HirId,
    lhs_inner_ty: ty::Ty<'tcx>,
) -> Option<OwnershipFieldBlockReason> {
    struct LocalSourceReasonVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        sig_decs: &'a SigDecisions,
        ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
        target_hir_id: HirId,
        lhs_inner_ty: ty::Ty<'tcx>,
        reasons: FxHashSet<OwnershipFieldBlockReason>,
    }

    impl<'tcx> LocalSourceReasonVisitor<'_, 'tcx> {
        fn record_source(&mut self, rhs: &'tcx hir::Expr<'tcx>) {
            if hir_rhs_supports_box_target(
                self.tcx,
                self.sig_decs,
                self.ptr_kinds,
                rhs,
                PtrKind::OptBox,
                self.lhs_inner_ty,
            ) {
                return;
            }
            self.reasons.insert(direct_opt_box_rhs_block_reason(
                self.tcx,
                self.lhs_inner_ty,
                rhs,
                OwnershipFieldBlockReason::UnsupportedRawLocalSource,
            ));
        }
    }

    impl<'tcx> Visitor<'tcx> for LocalSourceReasonVisitor<'_, 'tcx> {
        fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
            if let hir::StmtKind::Let(let_stmt) = stmt.kind
                && let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind
                && hir_id == self.target_hir_id
                && let Some(init) = let_stmt.init
            {
                self.record_source(init);
            }
            intravisit::walk_stmt(self, stmt);
        }

        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = lhs.kind
                && path.res == Res::Local(self.target_hir_id)
            {
                self.record_source(rhs);
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let body = tcx.hir_body_owned_by(target_hir_id.owner.def_id);
    let mut visitor = LocalSourceReasonVisitor {
        tcx,
        sig_decs,
        ptr_kinds,
        target_hir_id,
        lhs_inner_ty,
        reasons: FxHashSet::default(),
    };
    visitor.visit_body(body);
    OwnershipFieldBlockReason::ALL
        .into_iter()
        .find(|reason| visitor.reasons.contains(reason))
}

fn raw_local_has_supported_scalar_box_source<'tcx>(
    tcx: TyCtxt<'tcx>,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    target_hir_id: HirId,
    lhs_inner_ty: ty::Ty<'tcx>,
) -> bool {
    struct LocalSourceVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        sig_decs: &'a SigDecisions,
        ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
        target_hir_id: HirId,
        lhs_inner_ty: ty::Ty<'tcx>,
        saw_supported_source: bool,
        saw_unsupported_source: bool,
    }

    impl<'tcx> LocalSourceVisitor<'_, 'tcx> {
        fn record_source(&mut self, rhs: &'tcx hir::Expr<'tcx>) {
            if hir_rhs_supports_box_target(
                self.tcx,
                self.sig_decs,
                self.ptr_kinds,
                rhs,
                PtrKind::OptBox,
                self.lhs_inner_ty,
            ) {
                self.saw_supported_source = true;
            } else {
                self.saw_unsupported_source = true;
            }
        }
    }

    impl<'tcx> Visitor<'tcx> for LocalSourceVisitor<'_, 'tcx> {
        fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
            if let hir::StmtKind::Let(let_stmt) = stmt.kind
                && let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind
                && hir_id == self.target_hir_id
                && let Some(init) = let_stmt.init
            {
                self.record_source(init);
            }
            intravisit::walk_stmt(self, stmt);
        }

        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = lhs.kind
                && path.res == Res::Local(self.target_hir_id)
            {
                self.record_source(rhs);
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let body = tcx.hir_body_owned_by(target_hir_id.owner.def_id);
    let mut visitor = LocalSourceVisitor {
        tcx,
        sig_decs,
        ptr_kinds,
        target_hir_id,
        lhs_inner_ty,
        saw_supported_source: false,
        saw_unsupported_source: false,
    };
    visitor.visit_body(body);
    visitor.saw_supported_source && !visitor.saw_unsupported_source
}

#[cfg(test)]
fn collect_ownership_field_diagnostics<'tcx>(
    tcx: TyCtxt<'tcx>,
    analysis: &Analysis,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
) -> OwnershipFieldDiagnostics {
    let mut diagnostics = OwnershipFieldDiagnostics::default();
    let mut scalar_fields = FxHashMap::default();

    for maybe_owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let hir::OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        if !matches!(item.kind, hir::ItemKind::Struct(..)) {
            continue;
        }
        let struct_did = item.owner_id.def_id;
        let field_count = tcx.adt_def(struct_did).non_enum_variant().fields.len();
        for field_index in 0..field_count {
            let field = StructFieldSlot {
                struct_did,
                field_index,
            };
            let Some(inner_ty) = owning_struct_field_scalar_inner_ty(tcx, analysis, field) else {
                continue;
            };
            diagnostics.total += 1;
            let inner_ty = match inner_ty {
                Ok(inner_ty) => inner_ty,
                Err(reason) => {
                    diagnostics.record_blocked([reason]);
                    continue;
                }
            };
            scalar_fields.insert(field, inner_ty);
        }
    }

    let block_reasons =
        collect_ownership_field_rhs_block_reasons(tcx, sig_decs, ptr_kinds, &scalar_fields);
    for field in scalar_fields.keys() {
        if let Some(reasons) = block_reasons.get(field) {
            if reasons.is_empty() {
                diagnostics.selected_opt_box += 1;
            } else {
                diagnostics.record_blocked(reasons.iter().copied());
            }
        } else {
            diagnostics.selected_opt_box += 1;
        }
    }

    diagnostics
}

fn collect_struct_shape_demoted_fields(
    tcx: TyCtxt<'_>,
    promoted_fields: &FxHashSet<StructFieldSlot>,
    mutable_fields: &FxHashSet<StructFieldSlot>,
    struct_copy_result: &crate::analyses::struct_copy::StructCopyAnalysisResult,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
) -> FxHashSet<StructFieldSlot> {
    collect_struct_shape_demoted_field_reasons(
        tcx,
        promoted_fields,
        mutable_fields,
        struct_copy_result,
        sig_decs,
        ptr_kinds,
    )
    .into_keys()
    .collect()
}

fn collect_struct_shape_demoted_field_reasons(
    tcx: TyCtxt<'_>,
    promoted_fields: &FxHashSet<StructFieldSlot>,
    mutable_fields: &FxHashSet<StructFieldSlot>,
    struct_copy_result: &crate::analyses::struct_copy::StructCopyAnalysisResult,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
) -> FxHashMap<StructFieldSlot, FxHashSet<DecisionReason>> {
    let mut demoted = FxHashMap::<StructFieldSlot, FxHashSet<DecisionReason>>::default();

    for &field in promoted_fields {
        if !struct_has_named_fields(tcx, field.struct_did) {
            demoted
                .entry(field)
                .or_default()
                .insert(DecisionReason::BorrowFieldShapeUnnamedFields);
        }
        if mutable_fields.contains(&field)
            && struct_copy_result.must_preserve_copy(field.struct_did)
        {
            demoted
                .entry(field)
                .or_default()
                .insert(DecisionReason::BorrowFieldShapePreserveCopy);
        }
    }

    for did in tcx.hir_crate(()).owners.iter().filter_map(|owner| {
        let owner = owner.as_owner()?;
        match owner.node() {
            hir::OwnerNode::Item(item) => {
                matches!(item.kind, hir::ItemKind::Fn { .. }).then_some(item.owner_id.def_id)
            }
            hir::OwnerNode::ForeignItem(item) => {
                matches!(item.kind, hir::ForeignItemKind::Fn(..)).then_some(item.owner_id.def_id)
            }
            _ => None,
        }
    }) {
        let sig = tcx.fn_sig(did).skip_binder().skip_binder();
        if signature_output_rewrites_to_owning(tcx, sig_decs, ptr_kinds, did, sig.output())
            || signature_output_rewrites_to_borrow(sig_decs, did)
        {
            continue;
        }
        let mut by_value_demoted = FxHashSet::default();
        collect_promoted_fields_in_by_value_ty(
            sig.output(),
            promoted_fields,
            &mut by_value_demoted,
        );
        for field in by_value_demoted {
            demoted
                .entry(field)
                .or_default()
                .insert(DecisionReason::BorrowFieldShapeByValueOutput);
        }
    }

    demoted
}

#[cfg(test)]
fn field_slot_label(tcx: TyCtxt<'_>, field: StructFieldSlot) -> String {
    let struct_name = tcx.def_path_str(field.struct_did);
    let field_name = tcx
        .adt_def(field.struct_did)
        .non_enum_variant()
        .fields
        .iter()
        .nth(field.field_index)
        .map(|field| field.name.as_str().to_owned())
        .unwrap_or_else(|| format!("#{}", field.field_index));
    format!("{struct_name}.{field_name}")
}

fn local_struct_fields(tcx: TyCtxt<'_>) -> Vec<StructFieldSlot> {
    let mut fields = Vec::new();
    for maybe_owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let hir::OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        if !matches!(item.kind, hir::ItemKind::Struct(..)) {
            continue;
        }
        let struct_did = item.owner_id.def_id;
        let field_count = tcx.adt_def(struct_did).non_enum_variant().fields.len();
        for field_index in 0..field_count {
            fields.push(StructFieldSlot {
                struct_did,
                field_index,
            });
        }
    }
    fields
}

fn conflict_reason_to_decision_reason(reason: ConflictDemotionReason) -> DecisionReason {
    match reason {
        ConflictDemotionReason::ActiveBorrowOverlap => DecisionReason::ActiveBorrowOverlap,
        ConflictDemotionReason::LocalAssignmentWhileBorrowed => {
            DecisionReason::LocalAssignmentWhileBorrowed
        }
        ConflictDemotionReason::ConflictingReborrow => DecisionReason::ConflictingReborrow,
        ConflictDemotionReason::MutableFieldCopy => DecisionReason::MutableFieldCopy,
        ConflictDemotionReason::RawPointeeFieldMove => DecisionReason::RawPointeeFieldMove,
        ConflictDemotionReason::RawFieldPointerProjection => {
            DecisionReason::RawFieldPointerProjection
        }
        ConflictDemotionReason::RawStorageAllocator => DecisionReason::RawStorageAllocator,
        ConflictDemotionReason::RawStoragePointer => DecisionReason::RawStoragePointer,
        ConflictDemotionReason::RawBindingFromField => DecisionReason::RawBindingFromField,
        ConflictDemotionReason::RawLocalCallArg => DecisionReason::RawLocalCallArg,
        ConflictDemotionReason::RawUnknownCallArg => DecisionReason::RawUnknownCallArg,
    }
}

fn ownership_reason_to_decision_reason(reason: OwnershipFieldBlockReason) -> DecisionReason {
    match reason {
        OwnershipFieldBlockReason::NonRawFieldType => DecisionReason::NonRawFieldType,
        OwnershipFieldBlockReason::NonScalarPointee => DecisionReason::NonScalarPointee,
        OwnershipFieldBlockReason::CVoidOrFilePointee => DecisionReason::CVoidOrFilePointee,
        OwnershipFieldBlockReason::UnsupportedStructLiteralRhs => {
            DecisionReason::UnsupportedStructLiteralRhs
        }
        OwnershipFieldBlockReason::UnsupportedAssignmentRhs => {
            DecisionReason::UnsupportedAssignmentRhs
        }
        OwnershipFieldBlockReason::UnsupportedCallRhs => DecisionReason::UnsupportedCallRhs,
        OwnershipFieldBlockReason::UnsupportedRawLocalSource => {
            DecisionReason::UnsupportedRawLocalSource
        }
        OwnershipFieldBlockReason::AllocatorSizeMismatch => DecisionReason::AllocatorSizeMismatch,
        OwnershipFieldBlockReason::ReallocOrBufferPattern => DecisionReason::ReallocOrBufferPattern,
        OwnershipFieldBlockReason::CStringOrStrFunctionPattern => {
            DecisionReason::CStringOrStrFunctionPattern
        }
    }
}

#[allow(dead_code)]
fn count_promoted_field_usages(
    tcx: TyCtxt<'_>,
    promoted_fields: &FxHashSet<StructFieldSlot>,
) -> FxHashMap<StructFieldSlot, usize> {
    struct FieldUsageVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        typeck: &'tcx rustc_middle::ty::TypeckResults<'tcx>,
        promoted_fields: &'a FxHashSet<StructFieldSlot>,
        usages: FxHashMap<StructFieldSlot, usize>,
    }

    impl FieldUsageVisitor<'_, '_> {
        fn record(&mut self, field: StructFieldSlot) {
            if self.promoted_fields.contains(&field) {
                *self.usages.entry(field).or_default() += 1;
            }
        }
    }

    impl<'tcx> Visitor<'tcx> for FieldUsageVisitor<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let Some(field) = hir_struct_field_slot(self.tcx, expr) {
                self.record(field);
            }

            if let hir::ExprKind::Struct(qpath, fields, _) = expr.kind
                && let Some(struct_did) = hir_local_struct_did_from_qpath(qpath)
                    .or_else(|| hir_local_struct_did_from_ty(self.typeck.expr_ty(expr)))
            {
                for field in fields {
                    if let Some(field_index) =
                        hir_field_index_by_name(self.tcx, struct_did, field.ident.name)
                    {
                        self.record(StructFieldSlot {
                            struct_did,
                            field_index,
                        });
                    }
                }
            }

            intravisit::walk_expr(self, expr);
        }
    }

    let mut usages = FxHashMap::default();
    for_each_hir_fn_body(tcx, |body, typeck| {
        let mut visitor = FieldUsageVisitor {
            tcx,
            typeck,
            promoted_fields,
            usages: FxHashMap::default(),
        };
        visitor.visit_body(body);
        for (field, count) in visitor.usages {
            *usages.entry(field).or_default() += count;
        }
    });
    usages
}

fn signature_output_rewrites_to_owning<'tcx>(
    tcx: TyCtxt<'tcx>,
    sig_decs: &SigDecisions,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
    did: LocalDefId,
    output_ty: ty::Ty<'tcx>,
) -> bool {
    let Some(output_dec) = sig_decs.data.get(&did).and_then(|sig| sig.output_dec) else {
        return false;
    };
    if !output_dec.is_owning_box_like() {
        return false;
    }
    let Some((inner_ty, _)) = unwrap_ptr_from_mir_ty(output_ty) else {
        return false;
    };
    !fn_tail_returns_unsupported_box_binding(tcx, sig_decs, ptr_kinds, did, output_dec, inner_ty)
}

fn signature_output_rewrites_to_borrow(sig_decs: &SigDecisions, did: LocalDefId) -> bool {
    sig_decs.data.get(&did).is_some_and(|sig| {
        matches!(
            sig.output_dec,
            Some(
                PtrKind::Ref(_) | PtrKind::OptRef(_) | PtrKind::Slice(_) | PtrKind::SliceCursor(_)
            )
        )
    })
}

fn struct_has_named_fields(tcx: TyCtxt<'_>, did: LocalDefId) -> bool {
    let hir::Node::Item(item) = tcx.hir_node_by_def_id(did) else {
        return false;
    };
    let hir::ItemKind::Struct(_, _, variant_data) = item.kind else {
        return false;
    };
    matches!(variant_data, hir::VariantData::Struct { .. })
}

fn collect_promoted_fields_in_by_value_ty(
    ty: ty::Ty<'_>,
    promoted_fields: &FxHashSet<StructFieldSlot>,
    demoted: &mut FxHashSet<StructFieldSlot>,
) {
    match ty.kind() {
        ty::TyKind::RawPtr(inner, _) | ty::TyKind::Ref(_, inner, _) => {
            collect_promoted_fields_in_by_value_ty(*inner, promoted_fields, demoted);
        }
        ty::TyKind::Adt(adt_def, args) => {
            if adt_def.did().is_local() && adt_def.is_struct() && !adt_def.is_union() {
                let struct_did = adt_def.did().expect_local();
                demoted.extend(
                    promoted_fields
                        .iter()
                        .copied()
                        .filter(|field| field.struct_did == struct_did),
                );
            }
            for arg in args.iter() {
                if let ty::GenericArgKind::Type(ty) = arg.kind() {
                    collect_promoted_fields_in_by_value_ty(ty, promoted_fields, demoted);
                }
            }
        }
        ty::TyKind::Tuple(tys) => {
            for ty in tys.iter() {
                collect_promoted_fields_in_by_value_ty(ty, promoted_fields, demoted);
            }
        }
        ty::TyKind::Array(ty, _) | ty::TyKind::Slice(ty) => {
            collect_promoted_fields_in_by_value_ty(*ty, promoted_fields, demoted);
        }
        _ => {}
    }
}

fn hir_raw_addr_local(expr: &hir::Expr<'_>) -> Option<(HirId, bool)> {
    let expr = hir_unwrap_casts(expr);
    let hir::ExprKind::AddrOf(hir::BorrowKind::Raw, mutability, pointee) = expr.kind else {
        return None;
    };
    Some((hir_unwrapped_local_id(pointee)?, mutability.is_mut()))
}

fn hir_addr_local(expr: &hir::Expr<'_>) -> Option<(HirId, bool)> {
    let expr = hir_unwrap_casts(expr);
    let hir::ExprKind::AddrOf(_, mutability, pointee) = expr.kind else {
        return None;
    };
    Some((hir_unwrapped_local_id(pointee)?, mutability.is_mut()))
}

fn hir_struct_field_slot(tcx: TyCtxt<'_>, hir_expr: &hir::Expr<'_>) -> Option<StructFieldSlot> {
    let hir::ExprKind::Field(base, ident) = hir_expr.kind else {
        return None;
    };
    let typeck = tcx.typeck(hir_expr.hir_id.owner);
    let struct_did = hir_local_struct_did_from_ty(typeck.expr_ty_adjusted(base))?;
    let field_index = hir_field_index_by_name(tcx, struct_did, ident.name)?;
    Some(StructFieldSlot {
        struct_did,
        field_index,
    })
}

fn apply_field_storage_input_lifetimes(
    tcx: TyCtxt<'_>,
    analysis: &Analysis,
    lifetime_plans: &super::lifetimes::LifetimePlans,
    demoted_fields: &FxHashSet<StructFieldSlot>,
    field_cursor_fields: &FxHashSet<StructFieldSlot>,
    sig_decs: &mut SigDecisions,
) {
    struct FieldStorageLifetimeVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        analysis: &'a Analysis,
        lifetime_plans: &'a super::lifetimes::LifetimePlans,
        demoted_fields: &'a FxHashSet<StructFieldSlot>,
        field_cursor_fields: &'a FxHashSet<StructFieldSlot>,
        sig_decs: &'a mut SigDecisions,
    }

    impl FieldStorageLifetimeVisitor<'_, '_> {
        fn record_storage(&mut self, field: StructFieldSlot, rhs: &hir::Expr<'_>) {
            if !matches!(
                borrow_promoted_array_field_kind(
                    self.analysis,
                    self.demoted_fields,
                    self.field_cursor_fields,
                    field,
                ),
                Some(PtrKind::Slice(_) | PtrKind::SliceCursor(_))
            ) {
                return;
            }
            let Some(lifetime) = self
                .lifetime_plans
                .structs
                .get(&field.struct_did)
                .and_then(|plan| plan.field_lifetimes.get(&field.field_index))
                .copied()
            else {
                return;
            };
            let Some(rhs_hir_id) = hir_unwrapped_local_id(hir_unwrap_addr_of_deref(rhs)) else {
                return;
            };
            let Some((did, input_index)) = param_index_for_binding(self.tcx, rhs_hir_id) else {
                return;
            };
            let Some(sig_dec) = self.sig_decs.data.get_mut(&did) else {
                return;
            };
            if let Some(input_lifetime) = sig_dec.input_lifetimes.get_mut(input_index)
                && (input_lifetime.is_none() || *input_lifetime == Some(lifetime))
            {
                *input_lifetime = Some(lifetime);
            }
        }
    }

    impl<'tcx> Visitor<'tcx> for FieldStorageLifetimeVisitor<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            match expr.kind {
                hir::ExprKind::Assign(lhs, rhs, _) => {
                    if let Some(field) = hir_struct_field_slot(self.tcx, lhs) {
                        self.record_storage(field, rhs);
                    }
                }
                hir::ExprKind::Struct(qpath, fields, _) => {
                    if let Some(struct_did) = hir_local_struct_did_from_qpath(qpath) {
                        for field_expr in fields {
                            if let Some(field_index) =
                                hir_field_index_by_name(self.tcx, struct_did, field_expr.ident.name)
                            {
                                self.record_storage(
                                    StructFieldSlot {
                                        struct_did,
                                        field_index,
                                    },
                                    field_expr.expr,
                                );
                            }
                        }
                    }
                }
                _ => {}
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut visitor = FieldStorageLifetimeVisitor {
        tcx,
        analysis,
        lifetime_plans,
        demoted_fields,
        field_cursor_fields,
        sig_decs,
    };
    for def_id in tcx.hir_body_owners() {
        visitor.visit_body(tcx.hir_body_owned_by(def_id));
    }
}

fn borrow_promoted_array_field_kind(
    analysis: &Analysis,
    demoted_fields: &FxHashSet<StructFieldSlot>,
    field_cursor_fields: &FxHashSet<StructFieldSlot>,
    field: StructFieldSlot,
) -> Option<PtrKind> {
    if demoted_fields.contains(&field) || struct_field_is_exactly_owning(analysis, field) {
        return None;
    }
    let mutability = if analysis
        .borrow_promotion_result
        .mutable_fields
        .contains(&field)
    {
        true
    } else if analysis
        .borrow_promotion_result
        .shared_fields
        .contains(&field)
    {
        false
    } else {
        return None;
    };
    if !analysis_field_is_array_like(analysis, field) {
        return None;
    }
    if field_cursor_fields.contains(&field) {
        Some(PtrKind::SliceCursor(mutability))
    } else {
        Some(PtrKind::Slice(mutability))
    }
}

fn analysis_field_is_array_like(analysis: &Analysis, field: StructFieldSlot) -> bool {
    analysis
        .fatness_result
        .struct_facts(field.struct_did)
        .nth(field.field_index)
        .is_some_and(|fatnesses| fatnesses.iter().any(|fatness| fatness.is_arr()))
}

fn hir_field_base_local_id(hir_expr: &hir::Expr<'_>) -> Option<HirId> {
    let hir::ExprKind::Field(base, _) = hir_expr.kind else {
        return None;
    };
    hir_unwrapped_local_id(base)
}

fn hir_projection_root_local_id(hir_expr: &hir::Expr<'_>) -> Option<HirId> {
    match hir_unwrap_casts(hir_expr).kind {
        hir::ExprKind::Path(hir::QPath::Resolved(_, path)) => match path.res {
            Res::Local(hir_id) => Some(hir_id),
            _ => None,
        },
        hir::ExprKind::Unary(hir::UnOp::Deref, inner) => hir_projection_root_local_id(inner),
        hir::ExprKind::Field(base, _) => hir_projection_root_local_id(base),
        _ => None,
    }
}

fn hir_local_place_root_without_deref(hir_expr: &hir::Expr<'_>) -> Option<HirId> {
    match hir_unwrap_casts(hir_expr).kind {
        hir::ExprKind::Path(hir::QPath::Resolved(_, path)) => match path.res {
            Res::Local(hir_id) => Some(hir_id),
            _ => None,
        },
        hir::ExprKind::Field(base, _) | hir::ExprKind::Index(base, _, _) => {
            hir_local_place_root_without_deref(base)
        }
        _ => None,
    }
}

fn hir_field_access_expr_string(tcx: TyCtxt<'_>, hir_expr: &hir::Expr<'_>) -> Option<String> {
    match hir_unwrap_casts(hir_expr).kind {
        hir::ExprKind::Path(hir::QPath::Resolved(_, path)) => match path.res {
            Res::Local(hir_id) => Some(tcx.hir_name(hir_id).to_string()),
            _ => None,
        },
        hir::ExprKind::Unary(hir::UnOp::Deref, inner) => {
            Some(format!("(*{})", hir_field_access_expr_string(tcx, inner)?))
        }
        hir::ExprKind::Field(base, ident) => Some(format!(
            "{}.{}",
            hir_field_access_expr_string(tcx, base)?,
            ident.name
        )),
        _ => None,
    }
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

fn hir_local_struct_did_from_ty(ty: ty::Ty<'_>) -> Option<LocalDefId> {
    match ty.kind() {
        ty::TyKind::Adt(adt_def, _) if adt_def.did().is_local() && adt_def.is_struct() => {
            Some(adt_def.did().expect_local())
        }
        ty::TyKind::Ref(_, inner, _) => hir_local_struct_did_from_ty(*inner),
        _ => None,
    }
}

fn hir_field_index_by_name(
    tcx: TyCtxt<'_>,
    struct_did: LocalDefId,
    field_name: Symbol,
) -> Option<usize> {
    tcx.adt_def(struct_did)
        .non_enum_variant()
        .fields
        .iter_enumerated()
        .find_map(|(field_index, field)| (field.name == field_name).then_some(field_index.index()))
}

fn hir_field_is_raw_ptr(tcx: TyCtxt<'_>, field: StructFieldSlot) -> bool {
    let hir::Node::Item(item) = tcx.hir_node_by_def_id(field.struct_did) else {
        return false;
    };
    let hir::ItemKind::Struct(_, _, variant_data) = item.kind else {
        return false;
    };
    variant_data
        .fields()
        .get(field.field_index)
        .is_some_and(|field_def| matches!(field_def.ty.kind, hir::TyKind::Ptr(_)))
}

fn downgrade_unsupported_allocator_box_kinds(
    tcx: TyCtxt<'_>,
    ptr_kinds: &FxHashMap<HirId, PtrKind>,
) -> FxHashSet<HirId> {
    struct BoxDowngradeVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
        downgraded: FxHashSet<HirId>,
    }

    impl<'tcx> BoxDowngradeVisitor<'_, 'tcx> {
        fn maybe_downgrade(
            &mut self,
            hir_id: HirId,
            lhs_ty: ty::Ty<'tcx>,
            rhs: &'tcx hir::Expr<'tcx>,
        ) {
            let Some((inner_ty, _)) = unwrap_ptr_from_mir_ty(lhs_ty) else {
                return;
            };
            if !matches!(
                self.ptr_kinds.get(&hir_id).copied(),
                Some(PtrKind::Box | PtrKind::OptBox)
            ) {
                return;
            }
            if !matches!(
                hir_call_name(rhs),
                Some(name)
                    if matches!(
                        name,
                        _ if name == Symbol::intern("malloc")
                            || name == Symbol::intern("calloc")
                            || name == Symbol::intern("realloc")
                    )
            ) {
                return;
            }
            if !hir_supports_scalar_box_allocator_root(self.tcx, inner_ty, rhs) {
                self.downgraded.insert(hir_id);
            }
        }
    }

    impl<'tcx> Visitor<'tcx> for BoxDowngradeVisitor<'_, 'tcx> {
        fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
            if let hir::StmtKind::Let(let_stmt) = stmt.kind
                && let hir::PatKind::Binding(_, hir_id, ident, _) = let_stmt.pat.kind
                && let Some(init) = let_stmt.init
            {
                let lhs_ty = self.tcx.typeck(hir_id.owner).node_type(hir_id);
                let _ = ident;
                self.maybe_downgrade(hir_id, lhs_ty, init);
            }
            intravisit::walk_stmt(self, stmt);
        }

        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = lhs.kind
                && let Res::Local(hir_id) = path.res
            {
                let lhs_ty = self.tcx.typeck(expr.hir_id.owner).expr_ty(lhs);
                self.maybe_downgrade(hir_id, lhs_ty, rhs);
            }
            intravisit::walk_expr(self, expr);
        }
    }

    let mut downgraded: FxHashSet<HirId> = FxHashSet::default();
    let crate_hir = tcx.hir_crate(());
    for maybe_owner in crate_hir.owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let hir::OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            continue;
        };
        let body = tcx.hir_body(body);
        let mut visitor = BoxDowngradeVisitor {
            tcx,
            ptr_kinds,
            downgraded: FxHashSet::default(),
        };
        visitor.visit_expr(body.value);
        downgraded.extend(visitor.downgraded);
    }

    downgraded
}

fn is_std_slice_constructor_call(expr: &Expr) -> bool {
    if let ExprKind::Call(callee, _) = &unwrap_cast_and_paren(expr).kind
        && let ExprKind::Path(_, path) = &unwrap_paren(callee).kind
    {
        let segs = &path.segments;
        if segs.len() >= 2 {
            let ctor = segs[segs.len() - 1].ident.name.as_str();
            let owner = segs[segs.len() - 2].ident.name.as_str();
            return owner == "slice"
                && matches!(
                    ctor,
                    "from_mut" | "from_ref" | "from_raw_parts" | "from_raw_parts_mut"
                );
        }
    }
    false
}

fn slice_cursor_mut_temp_as_slice_receiver(expr: &Expr) -> Option<&Expr> {
    let expr = unwrap_paren(expr);
    let ExprKind::MethodCall(call) = &expr.kind else {
        return None;
    };
    if !matches!(call.seg.ident.name.as_str(), "as_slice" | "as_slice_mut") {
        return None;
    }
    let receiver = unwrap_paren(&call.receiver);
    is_slice_cursor_mut_constructor_call(receiver).then_some(receiver)
}

fn is_slice_cursor_mut_constructor_call(expr: &Expr) -> bool {
    if let ExprKind::Call(callee, _) = &unwrap_cast_and_paren(expr).kind
        && let ExprKind::Path(_, path) = &unwrap_paren(callee).kind
    {
        let segs = &path.segments;
        if segs.len() >= 2 {
            let ctor = segs[segs.len() - 1].ident.name.as_str();
            let owner = segs[segs.len() - 2].ident.name.as_str();
            return owner == "SliceCursorMut"
                && matches!(
                    ctor,
                    "new" | "with_pos" | "from_mut" | "from_raw_parts" | "from_raw_parts_mut"
                );
        }
    }
    false
}

fn is_plain_slice_expr(expr: &Expr) -> bool {
    let expr = unwrap_paren(expr);
    if matches!(expr.kind, ExprKind::Index(..) | ExprKind::Array(..)) {
        return true;
    }
    if is_slice_ref_expr(expr) {
        return true;
    }
    if let ExprKind::MethodCall(call) = &expr.kind
        && matches!(call.seg.ident.name.as_str(), "as_slice" | "as_slice_mut")
    {
        return true;
    }
    if is_std_slice_constructor_call(expr) {
        return true;
    }
    false
}

fn is_slice_ref_expr(expr: &Expr) -> bool {
    let expr = unwrap_paren(expr);
    matches!(
        expr.kind,
        ExprKind::AddrOf(
            _,
            _,
            box Expr {
                kind: ExprKind::Index(..),
                ..
            },
        )
    )
}

fn opt_ref_receiver_should_borrow(expr: &Expr) -> bool {
    match &unwrap_paren(expr).kind {
        ExprKind::Path(..) | ExprKind::Field(..) | ExprKind::Index(..) => true,
        ExprKind::MethodCall(call)
            if matches!(call.seg.ident.name.as_str(), "as_deref" | "as_deref_mut") =>
        {
            true
        }
        _ => false,
    }
}

fn hoist_opt_ref_borrow(expr: &mut Expr) {
    let mut visitor = OptRefBorrowVisitor::default();
    visitor.visit_expr(expr);

    let mut lets = String::new();
    for (name, uses) in &visitor.args {
        let total_uses = uses.raw_mut + uses.unwrap_mut + uses.unwrap_shared;
        if uses.unwrap_mut == 0 && !(uses.raw_mut > 0 && total_uses > 1) {
            continue;
        }
        use std::fmt::Write as _;
        let new_name = format!("{name}_borrowed");
        write!(
            &mut lets,
            "let {new_name} = {name}.as_deref_mut().unwrap();",
        )
        .unwrap();
        visitor.rewrite_targets.insert(*name, new_name);
    }
    if !lets.is_empty() {
        visitor.visit_expr(expr);
        *expr = utils::expr!("{{ {lets} {} }}", pprust::expr_to_string(expr))
    }
}

fn use_moving_opt_ref_unwraps_for_return(expr: &mut Expr) {
    struct ReturnOptRefUnwrapVisitor;

    impl mut_visit::MutVisitor for ReturnOptRefUnwrapVisitor {
        fn visit_expr(&mut self, expr: &mut Expr) {
            mut_visit::walk_expr(self, expr);
            let ExprKind::MethodCall(call) = &mut unwrap_paren_mut(expr).kind else {
                return;
            };
            if call.seg.ident.name != rustc_span::sym::unwrap {
                return;
            }
            let ExprKind::MethodCall(receiver_call) =
                &mut unwrap_paren_mut(&mut call.receiver).kind
            else {
                return;
            };
            if !matches!(
                receiver_call.seg.ident.name.as_str(),
                "as_deref" | "as_deref_mut"
            ) {
                return;
            }
            let receiver = pprust::expr_to_string(&receiver_call.receiver);
            *expr = utils::expr!("({receiver}).unwrap()");
        }
    }

    ReturnOptRefUnwrapVisitor.visit_expr(expr);
}

#[derive(Default)]
struct OptRefBorrowVisitor {
    rewrite_targets: FxHashMap<Symbol, String>,
    args: FxHashMap<Symbol, BorrowUseCounts>,
}

#[derive(Default)]
struct BorrowUseCounts {
    raw_mut: usize,
    unwrap_mut: usize,
    unwrap_shared: usize,
}

struct CapturePathRewriter<'a> {
    from: Symbol,
    to: &'a str,
}

impl mut_visit::MutVisitor for CapturePathRewriter<'_> {
    fn visit_expr(&mut self, expr: &mut Expr) {
        mut_visit::walk_expr(self, expr);
        if let ExprKind::Path(_, path) = &expr.kind
            && path.segments.len() == 1
            && path.segments[0].ident.name == self.from
        {
            *expr = utils::expr!("{}", self.to);
        }
    }
}

fn unwrap_opt_deref_call(expr: &mut Expr) -> Option<(Symbol, bool)> {
    let ExprKind::MethodCall(call) = &mut unwrap_paren_mut(expr).kind else {
        return None;
    };
    if call.seg.ident.name != rustc_span::sym::unwrap {
        return None;
    }
    let ExprKind::MethodCall(call) = &mut unwrap_paren_mut(&mut call.receiver).kind else {
        return None;
    };
    let method = call.seg.ident.name.as_str();
    let is_mut = method == "as_deref_mut";
    if !is_mut && method != "as_deref" {
        return None;
    }
    let ExprKind::Path(_, path) = &mut unwrap_paren_mut(&mut call.receiver).kind else {
        return None;
    };
    Some((path.segments.last()?.ident.name, is_mut))
}

fn null_ptr_inner_ty(expr: &Expr) -> Option<String> {
    let expr = pprust::expr_to_string(expr);
    let (_, rest) = expr.rsplit_once("::<")?;
    let (ty, _) = rest.split_once(">()")?;
    Some(ty.to_string())
}

fn raw_map_or_opt_deref(expr: &mut Expr) -> Option<(Symbol, String, &mut Expr)> {
    let ExprKind::MethodCall(call) = &mut unwrap_paren_mut(expr).kind else {
        return None;
    };
    if call.seg.ident.name.as_str() != "map_or" || call.args.len() != 2 {
        return None;
    }
    let ExprKind::MethodCall(receiver_call) = &mut unwrap_paren_mut(&mut call.receiver).kind else {
        return None;
    };
    if receiver_call.seg.ident.name.as_str() != "as_deref_mut" {
        return None;
    }
    let ExprKind::Path(_, path) = &mut unwrap_paren_mut(&mut receiver_call.receiver).kind else {
        return None;
    };
    let pointee_ty = null_ptr_inner_ty(&call.args[0])?;
    let ExprKind::Closure(box closure) = &mut call.args[1].kind else {
        return None;
    };
    Some((
        path.segments.last()?.ident.name,
        pointee_ty,
        &mut closure.body,
    ))
}

impl mut_visit::MutVisitor for OptRefBorrowVisitor {
    fn visit_expr(&mut self, expr: &mut Expr) {
        mut_visit::walk_expr(self, expr);

        if let Some((name, is_mut)) = unwrap_opt_deref_call(expr) {
            if self.rewrite_targets.is_empty() {
                let uses = self.args.entry(name).or_default();
                if is_mut {
                    uses.unwrap_mut += 1;
                } else {
                    uses.unwrap_shared += 1;
                }
            } else if let Some(new_name) = self.rewrite_targets.get(&name) {
                *expr = utils::expr!("{new_name}");
            }
            return;
        }

        if let Some((name, pointee_ty, body)) = raw_map_or_opt_deref(expr) {
            if self.rewrite_targets.is_empty() {
                self.args.entry(name).or_default().raw_mut += 1;
            } else if let Some(new_name) = self.rewrite_targets.get(&name) {
                let mut replacement = body.clone();
                let replacement_expr = format!("({new_name} as *mut {pointee_ty})");
                let mut rewriter = CapturePathRewriter {
                    from: Symbol::intern("_x"),
                    to: &replacement_expr,
                };
                rewriter.visit_expr(&mut replacement);
                *expr = replacement;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use rustc_hash::{FxHashMap, FxHashSet};
    use rustc_hir::{self as hir, HirId, ItemKind as HirItemKind, OwnerNode};
    use rustc_middle::{
        hir::nested_filter::OnlyBodies,
        ty::{self, TyCtxt},
    };
    use rustc_span::def_id::LocalDefId;

    use super::*;
    use crate::{
        analyses::{self, mir_variable_grouping::SourceVarGroups},
        rewriter::{Config, replace_local_borrows},
        utils::rustc::RustProgram,
    };

    fn with_simplified_cursor_projection(source: &str, check: impl FnOnce(&Expr) + Send) {
        utils::compilation::run_compiler_on_str("fn f() {}", move |_| {
            let mut krate = utils::ast::parse_crate(source.to_string());
            CursorProjectionSimplifier::default().visit_crate(&mut krate);

            #[derive(Default)]
            struct WildInitializer(Option<P<Expr>>);

            impl MutVisitor for WildInitializer {
                fn visit_local(&mut self, local: &mut Local) {
                    if matches!(local.pat.kind, PatKind::Wild)
                        && let Some(init) = local.kind.init()
                    {
                        assert!(self.0.is_none(), "multiple wildcard initializers");
                        self.0 = Some(Box::new(init.clone()));
                    }
                    mut_visit::walk_local(self, local);
                }
            }

            let mut initializer = WildInitializer::default();
            initializer.visit_crate(&mut krate);
            check(&initializer.0.expect("missing wildcard initializer"));
        })
        .unwrap();
    }

    fn assert_path(expr: &Expr, expected: &str) {
        let ExprKind::Path(None, path) = &unwrap_paren(expr).kind else {
            panic!(
                "expected path {expected}, got {}",
                pprust::expr_to_string(expr)
            );
        };
        assert_eq!(path.segments.len(), 1, "{}", pprust::expr_to_string(expr));
        assert_eq!(path.segments[0].ident.name.as_str(), expected);
    }

    fn assert_simple_ty(ty: &Ty, expected: &str) {
        let TyKind::Path(None, path) = &ty.kind else {
            panic!("expected type {expected}, got {}", pprust::ty_to_string(ty));
        };
        assert_eq!(path.segments.len(), 1, "{}", pprust::ty_to_string(ty));
        assert_eq!(path.segments[0].ident.name.as_str(), expected);
    }

    fn assert_combined_cursor_index(index: &Expr) {
        let ExprKind::MethodCall(call) = &unwrap_paren(index).kind else {
            panic!(
                "expected wrapping_add, got {}",
                pprust::expr_to_string(index)
            );
        };
        assert_eq!(call.seg.ident.name.as_str(), "wrapping_add");
        assert_path(&call.receiver, "raw_idx");
        let [offset] = call.args.as_slice() else {
            panic!("expected one wrapping_add argument");
        };
        let ExprKind::Cast(offset, ty) = &unwrap_paren(offset).kind else {
            panic!(
                "expected x as isize, got {}",
                pprust::expr_to_string(offset)
            );
        };
        assert_path(offset, "x");
        assert_simple_ty(ty, "isize");
    }

    #[test]
    fn cursor_projection_simplifier_indexes_proven_cursor_parameter() {
        with_simplified_cursor_projection(
            r#"
            fn f(
                raw: crate::slice_cursor::SliceCursorMut<'_, u8>,
                raw_idx: isize,
                x: i32,
            ) {
                let _ = crate::slice_cursor::SliceCursor::new(
                    crate::slice_cursor::SliceCursor::new(raw.as_slice())
                        .offset_by(raw_idx)
                        .as_slice(),
                )
                .offset_by(x as isize)[0usize];
            }
            "#,
            |initializer| {
                let ExprKind::Index(base, index, _) = &unwrap_paren(initializer).kind else {
                    panic!(
                        "expected index, got {}",
                        pprust::expr_to_string(initializer)
                    );
                };
                assert_path(base, "raw");
                assert_combined_cursor_index(index);
            },
        );
    }

    #[test]
    fn cursor_projection_simplifier_indexes_proven_cursor_local() {
        with_simplified_cursor_projection(
            r#"
            fn f(
                cursor: crate::slice_cursor::SliceCursorMut<'_, u8>,
                raw_idx: isize,
                x: i32,
            ) {
                let raw: crate::slice_cursor::SliceCursorMut<'_, u8> = cursor;
                let _ = crate::slice_cursor::SliceCursor::new(
                    crate::slice_cursor::SliceCursor::new(raw.as_slice())
                        .offset_by(raw_idx)
                        .as_slice(),
                )
                .offset_by(x as isize)[0usize];
            }
            "#,
            |initializer| {
                let ExprKind::Index(base, index, _) = &unwrap_paren(initializer).kind else {
                    panic!(
                        "expected index, got {}",
                        pprust::expr_to_string(initializer)
                    );
                };
                assert_path(base, "raw");
                assert_combined_cursor_index(index);
            },
        );
    }

    #[test]
    fn cursor_projection_simplifier_respects_non_cursor_shadowing() {
        with_simplified_cursor_projection(
            r#"
            fn f(
                raw: crate::slice_cursor::SliceCursorMut<'_, u8>,
                values: &[u8],
                raw_idx: isize,
                x: i32,
            ) {
                {
                    let raw: &[u8] = values;
                    let _ = crate::slice_cursor::SliceCursor::new(
                        crate::slice_cursor::SliceCursor::new(raw.as_slice())
                            .offset_by(raw_idx)
                            .as_slice(),
                    )
                    .offset_by(x as isize)[0usize];
                }
            }
            "#,
            |initializer| {
                let ExprKind::Index(base, index, _) = &unwrap_paren(initializer).kind else {
                    panic!(
                        "expected index, got {}",
                        pprust::expr_to_string(initializer)
                    );
                };
                let ExprKind::MethodCall(call) = &unwrap_paren(base).kind else {
                    panic!(
                        "expected raw.as_slice(), got {}",
                        pprust::expr_to_string(base)
                    );
                };
                assert_eq!(call.seg.ident.name.as_str(), "as_slice");
                assert!(call.args.is_empty());
                assert_path(&call.receiver, "raw");

                let ExprKind::Cast(index, ty) = &unwrap_paren(index).kind else {
                    panic!("expected usize cast, got {}", pprust::expr_to_string(index));
                };
                assert_simple_ty(ty, "usize");
                assert_combined_cursor_index(index);
            },
        );
    }

    #[test]
    fn cursor_projection_simplifier_respects_closure_parameter_shadowing() {
        with_simplified_cursor_projection(
            r#"
            fn f(
                raw: crate::slice_cursor::SliceCursorMut<'_, u8>,
                raw_idx: isize,
                x: i32,
            ) {
                let _closure = |raw: &[u8]| {
                    let _ = crate::slice_cursor::SliceCursor::new(
                        crate::slice_cursor::SliceCursor::new(raw.as_slice())
                            .offset_by(raw_idx)
                            .as_slice(),
                    )
                    .offset_by(x as isize)[0usize];
                };
            }
            "#,
            |initializer| {
                let ExprKind::Index(base, index, _) = &unwrap_paren(initializer).kind else {
                    panic!(
                        "expected index, got {}",
                        pprust::expr_to_string(initializer)
                    );
                };
                let ExprKind::MethodCall(call) = &unwrap_paren(base).kind else {
                    panic!(
                        "expected raw.as_slice(), got {}",
                        pprust::expr_to_string(base)
                    );
                };
                assert_eq!(call.seg.ident.name.as_str(), "as_slice");
                assert!(call.args.is_empty());
                assert_path(&call.receiver, "raw");

                let ExprKind::Cast(index, ty) = &unwrap_paren(index).kind else {
                    panic!("expected usize cast, got {}", pprust::expr_to_string(index));
                };
                assert_simple_ty(ty, "usize");
                assert_combined_cursor_index(index);
            },
        );
    }

    #[test]
    fn cursor_projection_simplifier_simplifies_unshadowed_closure_capture() {
        with_simplified_cursor_projection(
            r#"
            fn f(
                raw: crate::slice_cursor::SliceCursorMut<'_, u8>,
                raw_idx: isize,
                x: i32,
            ) {
                let _closure = || {
                    let _ = crate::slice_cursor::SliceCursor::new(
                        crate::slice_cursor::SliceCursor::new(raw.as_slice())
                            .offset_by(raw_idx)
                            .as_slice(),
                    )
                    .offset_by(x as isize)[0usize];
                };
            }
            "#,
            |initializer| {
                let ExprKind::Index(base, index, _) = &unwrap_paren(initializer).kind else {
                    panic!(
                        "expected index, got {}",
                        pprust::expr_to_string(initializer)
                    );
                };
                assert_path(base, "raw");
                assert_combined_cursor_index(index);
            },
        );
    }

    #[test]
    fn cursor_projection_simplifier_isolates_nested_items() {
        with_simplified_cursor_projection(
            r#"
            fn f(
                raw: crate::slice_cursor::SliceCursorMut<'_, u8>,
                raw_idx: isize,
                x: i32,
            ) {
                static raw: &[u8] = &[];
                const VALUE: () = {
                    let _ = crate::slice_cursor::SliceCursor::new(
                        crate::slice_cursor::SliceCursor::new(raw.as_slice())
                            .offset_by(raw_idx)
                            .as_slice(),
                    )
                    .offset_by(x as isize)[0usize];
                };
            }
            "#,
            |initializer| {
                let ExprKind::Index(base, index, _) = &unwrap_paren(initializer).kind else {
                    panic!(
                        "expected index, got {}",
                        pprust::expr_to_string(initializer)
                    );
                };
                let ExprKind::MethodCall(call) = &unwrap_paren(base).kind else {
                    panic!(
                        "expected raw.as_slice(), got {}",
                        pprust::expr_to_string(base)
                    );
                };
                assert_eq!(call.seg.ident.name.as_str(), "as_slice");
                assert!(call.args.is_empty());
                assert_path(&call.receiver, "raw");

                let ExprKind::Cast(index, ty) = &unwrap_paren(index).kind else {
                    panic!("expected usize cast, got {}", pprust::expr_to_string(index));
                };
                assert_simple_ty(ty, "usize");
                assert_combined_cursor_index(index);
            },
        );
    }

    #[test]
    fn cursor_projection_simplifier_respects_destructuring_shadowing() {
        with_simplified_cursor_projection(
            r#"
            fn f(
                raw: crate::slice_cursor::SliceCursorMut<'_, u8>,
                values: (&[u8],),
                raw_idx: isize,
                x: i32,
            ) {
                let (raw,) = values;
                let _ = crate::slice_cursor::SliceCursor::new(
                    crate::slice_cursor::SliceCursor::new(raw.as_slice())
                        .offset_by(raw_idx)
                        .as_slice(),
                )
                .offset_by(x as isize)[0usize];
            }
            "#,
            |initializer| {
                let ExprKind::Index(base, index, _) = &unwrap_paren(initializer).kind else {
                    panic!(
                        "expected index, got {}",
                        pprust::expr_to_string(initializer)
                    );
                };
                let ExprKind::MethodCall(call) = &unwrap_paren(base).kind else {
                    panic!(
                        "expected raw.as_slice(), got {}",
                        pprust::expr_to_string(base)
                    );
                };
                assert_eq!(call.seg.ident.name.as_str(), "as_slice");
                assert!(call.args.is_empty());
                assert_path(&call.receiver, "raw");

                let ExprKind::Cast(index, ty) = &unwrap_paren(index).kind else {
                    panic!("expected usize cast, got {}", pprust::expr_to_string(index));
                };
                assert_simple_ty(ty, "usize");
                assert_combined_cursor_index(index);
            },
        );
    }

    #[test]
    fn cursor_projection_simplifier_indexes_proven_associated_function_parameter() {
        with_simplified_cursor_projection(
            r#"
            struct S;

            impl S {
                fn f(
                    raw: crate::slice_cursor::SliceCursorMut<'_, u8>,
                    raw_idx: isize,
                    x: i32,
                ) {
                    let _ = crate::slice_cursor::SliceCursor::new(
                        crate::slice_cursor::SliceCursor::new(raw.as_slice())
                            .offset_by(raw_idx)
                            .as_slice(),
                    )
                    .offset_by(x as isize)[0usize];
                }
            }
            "#,
            |initializer| {
                let ExprKind::Index(base, index, _) = &unwrap_paren(initializer).kind else {
                    panic!(
                        "expected index, got {}",
                        pprust::expr_to_string(initializer)
                    );
                };
                assert_path(base, "raw");
                assert_combined_cursor_index(index);
            },
        );
    }

    #[test]
    fn cursor_projection_simplifier_rejects_noncanonical_cursor_type() {
        with_simplified_cursor_projection(
            r#"
            fn f(
                raw: other::SliceCursor<'_, u8>,
                raw_idx: isize,
                x: i32,
            ) {
                let _ = crate::slice_cursor::SliceCursor::new(
                    crate::slice_cursor::SliceCursor::new(raw.as_slice())
                        .offset_by(raw_idx)
                        .as_slice(),
                )
                .offset_by(x as isize)[0usize];
            }
            "#,
            |initializer| {
                let ExprKind::Index(base, index, _) = &unwrap_paren(initializer).kind else {
                    panic!(
                        "expected index, got {}",
                        pprust::expr_to_string(initializer)
                    );
                };
                let ExprKind::MethodCall(call) = &unwrap_paren(base).kind else {
                    panic!(
                        "expected raw.as_slice(), got {}",
                        pprust::expr_to_string(base)
                    );
                };
                assert_eq!(call.seg.ident.name.as_str(), "as_slice");
                assert!(call.args.is_empty());
                assert_path(&call.receiver, "raw");

                let ExprKind::Cast(index, ty) = &unwrap_paren(index).kind else {
                    panic!("expected usize cast, got {}", pprust::expr_to_string(index));
                };
                assert_simple_ty(ty, "usize");
                assert_combined_cursor_index(index);
            },
        );
    }

    #[test]
    fn cursor_projection_simplifier_combines_offset_index() {
        utils::compilation::run_compiler_on_str("fn f() {}", |_| {
            let mut expr = utils::expr!(
                "p.as_deref_mut().offset_by(a).as_deref_mut().offset_by(b)[0 as usize]"
            );
            CursorProjectionSimplifier::default().visit_expr(&mut expr);
            let expr = pprust::expr_to_string(&expr);
            assert!(expr.contains("wrapping_add"), "{expr}");
            assert!(!expr.contains("as_deref_mut"), "{expr}");
            assert!(!expr.contains("offset_by"), "{expr}");
        })
        .unwrap();
    }

    #[test]
    fn cursor_projection_simplifier_reborrows_once() {
        utils::compilation::run_compiler_on_str("fn f() {}", |_| {
            let mut expr =
                utils::expr!("p.as_deref_mut().offset_by(a).as_deref_mut().offset_by(b)");
            CursorProjectionSimplifier::default().visit_expr(&mut expr);
            let expr = pprust::expr_to_string(&expr);
            assert_eq!(expr.matches("as_deref_mut").count(), 1, "{expr}");
            assert_eq!(expr.matches("offset_by").count(), 2, "{expr}");
        })
        .unwrap();
    }

    #[test]
    fn cursor_projection_simplifier_removes_shared_cursor_constructors() {
        utils::compilation::run_compiler_on_str("fn f() {}", |_| {
            let mut expr = utils::expr!(
                "crate::slice_cursor::SliceCursor::new(
                    crate::slice_cursor::SliceCursor::new(raw.as_slice())
                        .offset_by(a)
                        .as_slice()
                )
                .offset_by(b)[0usize]"
            );
            CursorProjectionSimplifier::default().visit_expr(&mut expr);
            let expr = pprust::expr_to_string(&expr);
            assert!(expr.contains("wrapping_add"), "{expr}");
            assert!(expr.contains("raw.as_slice"), "{expr}");
            assert!(expr.contains("as usize"), "{expr}");
            assert!(!expr.contains("SliceCursor::new"), "{expr}");
            assert!(!expr.contains("offset_by"), "{expr}");
        })
        .unwrap();
    }

    #[test]
    fn cursor_projection_simplifier_indexes_unproven_as_slice_receiver() {
        utils::compilation::run_compiler_on_str("fn f() {}", |_| {
            let mut expr = utils::expr!(
                "crate::slice_cursor::SliceCursor::new(values.as_slice()).offset_by(a)[0usize]"
            );
            CursorProjectionSimplifier::default().visit_expr(&mut expr);
            let expr = pprust::expr_to_string(&expr);
            assert!(expr.contains("values.as_slice"), "{expr}");
            assert!(expr.contains("as usize"), "{expr}");
            assert!(!expr.contains("SliceCursor::new"), "{expr}");
            assert!(!expr.contains("offset_by"), "{expr}");
            assert!(!expr.starts_with("(values)["), "{expr}");
        })
        .unwrap();
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
                HirItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
                HirItemKind::Struct(..) => structs.push(item.owner_id.def_id),
                _ => {}
            }
        }

        RustProgram {
            tcx,
            functions,
            structs,
        }
    }

    fn build_analysis<'tcx>(tcx: TyCtxt<'tcx>) -> (RustProgram<'tcx>, super::super::Analysis) {
        let arena = typed_arena::Arena::new();
        let tss = utils::ty_shape::get_ty_shapes(&arena, tcx, false);
        let andersen_config = points_to::andersen::Config {
            use_optimized_mir: false,
            c_exposed_fns: FxHashSet::default(),
        };
        let pre_points_to = points_to::andersen::pre_analyze(&andersen_config, &tss, tcx);
        let points_to_solutions =
            points_to::andersen::analyze(&andersen_config, &pre_points_to, &tss, tcx);
        let aliases = super::super::find_param_aliases(&pre_points_to, &points_to_solutions, tcx);
        let points_to = points_to::andersen::post_analyze(
            &andersen_config,
            pre_points_to,
            points_to_solutions,
            &tss,
            tcx,
        );

        let input = collect_program(tcx);
        let mutability_result =
            analyses::type_qualifier::foster::mutability::mutability_analysis(&input);
        let output_params =
            analyses::output_params::compute_output_params(&input, &mutability_result, &aliases);
        let ownership_schemes = super::super::maybe_solidified_ownership(
            &super::super::Config::default(),
            &input,
            &output_params,
        );
        let source_var_groups = SourceVarGroups::new(&input);
        let mutables = source_var_groups.postprocess_mut_res(&input, &mutability_result);
        let borrow_promotion_result =
            analyses::borrow::mutable_references_no_guarantee(&input, &mutables);
        let borrow_lifetime_flows = borrow_promotion_result.lifetime_flows.clone();
        let struct_copy_result =
            analyses::struct_copy::analyze(&input, &borrow_promotion_result.mutable_fields);
        let promoted_mut_ref_result = source_var_groups
            .postprocess_promoted_mut_refs(borrow_promotion_result.mutable_locals.clone());
        let promoted_shared_ref_result = source_var_groups
            .postprocess_promoted_mut_refs(borrow_promotion_result.shared_locals.clone());
        let fatness_result = analyses::type_qualifier::foster::fatness::fatness_analysis(&input);
        let mut offset_sign_result = analyses::offset_sign::sign::offset_sign_analysis(&input);
        offset_sign_result.access_signs =
            source_var_groups.postprocess_offset_signs(offset_sign_result.access_signs);
        let mut nullity_result = analyses::nullity::analyze(&input, &points_to);
        nullity_result.non_null_locals =
            source_var_groups.postprocess_non_null_locals(nullity_result.non_null_locals);
        let analysis = super::super::Analysis {
            borrow_promotion_result,
            borrow_lifetime_flows,
            promoted_mut_ref_result,
            promoted_shared_ref_result,
            mutability_result,
            fatness_result,
            aliases,
            output_params,
            ownership_schemes,
            offset_sign_result,
            nullity_result,
            struct_copy_result,
        };

        (input, analysis)
    }

    fn field_conflict_reason_names_for_code(code: &str) -> FxHashMap<String, Vec<&'static str>> {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let (input, analysis) = build_analysis(tcx);
            let (sig_decs, ptr_kinds, _reason_map, _usage_subreason_map) =
                simulate_transform_reasons(tcx, &input, &analysis);
            let mut sig_decs = sig_decs;
            force_test_input_raw(tcx, &mut sig_decs, "raw_local");
            let reasons =
                collect_field_conflict_demotion_reasons(tcx, &analysis, &sig_decs, &ptr_kinds);
            reasons
                .into_iter()
                .map(|(field, reasons)| {
                    let mut reason_names = reasons
                        .into_iter()
                        .map(|reason| reason.as_str())
                        .collect::<Vec<_>>();
                    reason_names.sort();
                    (field_slot_label(tcx, field), reason_names)
                })
                .collect()
        })
        .unwrap()
    }

    fn force_test_input_raw(tcx: TyCtxt<'_>, sig_decs: &mut SigDecisions, name: &str) {
        for maybe_owner in tcx.hir_crate(()).owners.iter() {
            let Some(owner) = maybe_owner.as_owner() else {
                continue;
            };
            let OwnerNode::Item(item) = owner.node() else {
                continue;
            };
            if !matches!(item.kind, HirItemKind::Fn { .. }) {
                continue;
            }
            if tcx.item_name(item.owner_id.def_id.to_def_id()).as_str() != name {
                continue;
            }
            if let Some(sig_dec) = sig_decs.data.get_mut(&item.owner_id.def_id)
                && !sig_dec.input_decs.is_empty()
            {
                sig_dec.input_decs[0] = Some(PtrKind::Raw(true));
            }
        }
    }

    #[test]
    fn promotion_diagnostics_collect_all_conflict_reasons_for_field() {
        let reasons = field_conflict_reason_names_for_code(
            r#"
extern "C" {
    fn foreign(p: *mut i32);
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}

#[repr(C)]
pub struct Holder {
    pub p: *mut i32,
    pub q: *mut i32,
}

#[repr(C)]
pub struct Other {
    pub r: *mut i32,
}

pub unsafe fn raw_local(p: *mut i32) {
    foreign(p);
}

pub unsafe fn conflict(mut x: i32, mut y: i32, raw: *mut i32, owner: *mut Holder) {
    let mut h = Holder { p: &raw mut x, q: &raw mut x };
    let mut other = Other { r: &raw mut x };
    *h.p = 1;
    *h.q = 2;
    *other.r = 3;
    let _raw_binding: *mut i32 = h.p;
    let _q_raw_binding: *mut i32 = h.q;
    x = 2;
    let _reborrow = &mut x;
    foreign(h.p);
    foreign(h.q);
    raw_local(h.p);
    let _offset = h.p.sub(1);
    h.p = raw;
    h.p = malloc(4) as *mut i32;
    y = 2;
    h.q = &raw mut y;
    y = 3;
    (*owner).p = h.p;
    raw_local((*owner).p);
}
"#,
        );
        let incompatible_raw_storage_reasons = field_conflict_reason_names_for_code(
            r#"
#[repr(C)]
pub struct State {
    pub value: i32,
}

#[repr(C)]
pub struct PrintBuf {
    pub buffer: *mut State,
}

pub unsafe fn print_preallocated_like(buffer: *mut State) -> i32 {
    let mut p = PrintBuf { buffer: std::ptr::null_mut::<State>() };
    p.buffer = buffer;
    if p.buffer.is_null() {
        0
    } else {
        1
    }
}
"#,
        );

        let all_reasons = reasons
            .values()
            .chain(incompatible_raw_storage_reasons.values())
            .flat_map(|reasons| reasons.iter().copied())
            .collect::<FxHashSet<_>>();
        for expected in [
            "active_borrow_overlap",
            "conflicting_reborrow",
            "local_assignment_while_borrowed",
            "mutable_field_copy",
            "raw_binding_from_field",
            "raw_field_pointer_projection",
            "raw_pointee_field_move",
            "raw_storage_allocator",
            "raw_storage_pointer",
        ] {
            assert!(
                all_reasons.contains(expected),
                "expected {expected} in conflict reasons: {all_reasons:?}; all reasons: {reasons:?}"
            );
        }

        let holder_p = reasons
            .iter()
            .find(|(field, _)| field.ends_with("Holder.p"))
            .map(|(_, reasons)| reasons)
            .unwrap_or_else(|| panic!("Holder.p missing from conflict reasons: {reasons:?}"));
        for expected in [
            "mutable_field_copy",
            "raw_binding_from_field",
            "raw_field_pointer_projection",
            "raw_pointee_field_move",
            "raw_storage_allocator",
        ] {
            assert!(
                holder_p.contains(&expected),
                "expected {expected} in Holder.p conflict reasons: {holder_p:?}; all reasons: {reasons:?}"
            );
        }
    }

    #[test]
    fn ownership_field_diagnostics_count_selected_and_blocked_fields() {
        let diagnostics = ::utils::compilation::run_compiler_on_str(
            r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

#[repr(C)]
pub struct Good {
    pub data: *mut i32,
}

#[repr(C)]
pub struct Bad {
    pub data: *mut i32,
}

pub unsafe fn stash_good(owner: *mut Good) {
    (*owner).data = malloc(std::mem::size_of::<i32>());
}

pub unsafe fn stash_bad(owner: *mut Bad) {
    (*owner).data = malloc(2 * std::mem::size_of::<i32>());
}
"#,
            |tcx| {
                let (input, analysis) = build_analysis(tcx);
                let (sig_decs, ptr_kinds, _reason_map, _usage_subreason_map) =
                    simulate_transform_reasons(tcx, &input, &analysis);
                collect_ownership_field_diagnostics(tcx, &analysis, &sig_decs, &ptr_kinds)
            },
        )
        .unwrap();

        assert_eq!(diagnostics.total, 2);
        assert_eq!(diagnostics.selected_opt_box, 1);
        assert_eq!(diagnostics.blocked_total, 1);
        assert_eq!(
            diagnostics
                .block_reason_counts
                .get(&OwnershipFieldBlockReason::AllocatorSizeMismatch)
                .copied(),
            Some(1),
        );
    }

    fn unified_decision_events_for_code(
        code: &str,
    ) -> Vec<crate::rewriter::diagnostics::DecisionEvent> {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let mut krate = utils::ast::expanded_ast(tcx);
            let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
            utils::ast::remove_unnecessary_items_from_ast(&mut krate);
            let (input, analysis) = build_analysis(tcx);
            let visitor = TransformVisitor::new(
                &Config::default(),
                &input,
                &analysis,
                ast_to_hir,
                FnPtrGroups::default(),
                FnPtrRewriteDecision::default(),
                crate::rewriter::diagnostics::DecisionDiagnostics::for_test(
                    crate::rewriter::diagnostics::DiagnosticsMode::Full,
                ),
            );
            visitor.diagnostics.events().to_vec()
        })
        .unwrap()
    }

    #[test]
    fn unified_decision_diagnostics_record_ownership_field_reasons() {
        let events = unified_decision_events_for_code(
            r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

#[repr(C)]
pub struct Good {
    pub data: *mut i32,
}

#[repr(C)]
pub struct Bad {
    pub data: *mut i32,
}

pub unsafe fn stash_good(owner: *mut Good) {
    (*owner).data = malloc(std::mem::size_of::<i32>());
}

pub unsafe fn stash_bad(owner: *mut Bad) {
    (*owner).data = malloc(2 * std::mem::size_of::<i32>());
}
"#,
        );
        let reasons = events
            .iter()
            .map(|event| event.reason)
            .collect::<FxHashSet<_>>();
        assert!(
            reasons.contains(&DecisionReason::OwnershipFieldSelectedOptBox),
            "missing selected ownership field event: {events:#?}"
        );
        assert!(
            reasons.contains(&DecisionReason::AllocatorSizeMismatch),
            "missing allocator-size block event: {events:#?}"
        );
    }

    #[test]
    fn unified_decision_diagnostics_record_raw_local_assignment() {
        let events = unified_decision_events_for_code(
            r#"
pub unsafe fn assign(mut p: *mut core::ffi::c_void, q: *mut core::ffi::c_void) {
    p = q;
}
"#,
        );
        assert!(
            events
                .iter()
                .any(|event| event.reason == DecisionReason::RawLocalAssignment),
            "missing raw local assignment event: {events:#?}"
        );
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum SafetyAllocKind {
        Scalar,
        Array,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum SafetySiteShape {
        DirectLocalRoot,
        AllocatorWrapperPrincipalLocal,
        NonOutermostLocalRoot,
    }

    #[derive(Clone, Debug)]
    struct TrackedSemanticAllocSite {
        hir_id: HirId,
        fn_name: String,
        binding_name: String,
        kind: SafetyAllocKind,
        outermost: bool,
        shape: SafetySiteShape,
        deref_count: usize,
        free_count: usize,
    }

    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
    struct SplitKindCounts {
        scalar: usize,
        array: usize,
    }

    impl SplitKindCounts {
        fn bump(&mut self, kind: SafetyAllocKind) {
            self.bump_by(kind, 1);
        }

        fn bump_by(&mut self, kind: SafetyAllocKind, amount: usize) {
            match kind {
                SafetyAllocKind::Scalar => self.scalar += amount,
                SafetyAllocKind::Array => self.array += amount,
            }
        }

        fn total(self) -> usize {
            self.scalar + self.array
        }
    }

    impl std::ops::AddAssign for SplitKindCounts {
        fn add_assign(&mut self, rhs: Self) {
            self.scalar += rhs.scalar;
            self.array += rhs.array;
        }
    }

    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
    struct SafetyBeforeStats {
        allocation_sites: SplitKindCounts,
        dereferences: SplitKindCounts,
        frees: SplitKindCounts,
    }

    impl SafetyBeforeStats {
        fn record_site(&mut self, site: &TrackedSemanticAllocSite) {
            self.allocation_sites.bump(site.kind);
            self.dereferences.bump_by(site.kind, site.deref_count);
            self.frees.bump_by(site.kind, site.free_count);
        }
    }

    impl std::ops::AddAssign for SafetyBeforeStats {
        fn add_assign(&mut self, rhs: Self) {
            self.allocation_sites += rhs.allocation_sites;
            self.dereferences += rhs.dereferences;
            self.frees += rhs.frees;
        }
    }

    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
    struct BridgeCallCounts {
        leak: usize,
        from_raw: usize,
        into_raw: usize,
    }

    impl std::ops::AddAssign for BridgeCallCounts {
        fn add_assign(&mut self, rhs: Self) {
            self.leak += rhs.leak;
            self.from_raw += rhs.from_raw;
            self.into_raw += rhs.into_raw;
        }
    }

    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
    struct RewrittenUnsafeStats {
        dereferences: usize,
        frees: usize,
        bridge_calls: BridgeCallCounts,
    }

    impl std::ops::AddAssign for RewrittenUnsafeStats {
        fn add_assign(&mut self, rhs: Self) {
            self.dereferences += rhs.dereferences;
            self.frees += rhs.frees;
            self.bridge_calls += rhs.bridge_calls;
        }
    }

    #[derive(Clone, Debug)]
    struct PointerSafetyAnalysisResult {
        before_total: SafetyBeforeStats,
        before_outermost: SafetyBeforeStats,
        safe_box_sites: SplitKindCounts,
        tracked_sites: Vec<TrackedSemanticAllocSite>,
    }

    #[derive(Clone, Debug, Default)]
    struct TrackedBindingSpecs {
        by_fn: FxHashMap<String, FxHashSet<String>>,
    }

    fn hir_is_direct_allocator_root(tcx: TyCtxt<'_>, expr: &hir::Expr<'_>) -> bool {
        let Some(name) = hir_call_name(expr) else {
            return false;
        };
        match (name, hir_unwrap_casts(expr).kind) {
            (name, hir::ExprKind::Call(_, _)) if name == Symbol::intern("malloc") => true,
            (name, hir::ExprKind::Call(_, _)) if name == Symbol::intern("calloc") => true,
            (name, hir::ExprKind::Call(_, args)) if name == Symbol::intern("realloc") => {
                matches!(args, [ptr, _] if hir_is_null_like_ptr_arg(tcx, ptr))
            }
            _ => false,
        }
    }

    fn classify_semantic_allocator_kind<'tcx>(
        tcx: TyCtxt<'tcx>,
        lhs_inner_ty: ty::Ty<'tcx>,
        rhs: &'tcx hir::Expr<'tcx>,
    ) -> SafetyAllocKind {
        if hir_supports_scalar_box_allocator_root(tcx, lhs_inner_ty, rhs)
            || matches!(
                hir_raw_bridge_info(tcx, lhs_inner_ty, rhs, None, None),
                Some(RawBridgeInfo::Scalar)
            )
        {
            SafetyAllocKind::Scalar
        } else {
            SafetyAllocKind::Array
        }
    }

    fn root_of_raw_expr(
        expr: &hir::Expr<'_>,
        root_of_local: &FxHashMap<HirId, HirId>,
    ) -> Option<HirId> {
        let expr = hir_unwrap_casts(expr);
        match expr.kind {
            hir::ExprKind::Path(hir::QPath::Resolved(_, path)) => {
                let hir::def::Res::Local(hir_id) = path.res else {
                    return None;
                };
                root_of_local.get(&hir_id).copied()
            }
            hir::ExprKind::MethodCall(seg, receiver, _, _)
                if matches!(
                    seg.ident.name.as_str(),
                    "offset" | "add" | "sub" | "wrapping_offset" | "wrapping_add" | "wrapping_sub"
                ) =>
            {
                root_of_raw_expr(receiver, root_of_local)
            }
            _ => None,
        }
    }

    fn unwrap_body_tail<'tcx>(mut expr: &'tcx hir::Expr<'tcx>) -> &'tcx hir::Expr<'tcx> {
        while let hir::ExprKind::Block(block, _) = expr.kind {
            let Some(tail) = block.expr else {
                break;
            };
            expr = tail;
        }
        expr
    }

    fn box_bridge_call_kind(expr: &hir::Expr<'_>) -> Option<&'static str> {
        let hir::ExprKind::Call(callee, _) = hir_unwrap_casts(expr).kind else {
            return None;
        };
        let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = hir_unwrap_casts(callee).kind
        else {
            return None;
        };
        let segments = &path.segments;
        if segments.len() < 2 {
            return None;
        }
        let owner = segments[segments.len() - 2].ident.name.as_str();
        let method = segments[segments.len() - 1].ident.name.as_str();
        if owner != "Box" {
            return None;
        }
        match method {
            "leak" => Some("leak"),
            "from_raw" => Some("from_raw"),
            "into_raw" => Some("into_raw"),
            _ => None,
        }
    }

    fn bridge_call_counts_from_source(source: &str) -> BridgeCallCounts {
        BridgeCallCounts {
            leak: source.matches("Box::leak(").count(),
            from_raw: source.matches("Box::from_raw(").count(),
            into_raw: source.matches("Box::into_raw(").count(),
        }
    }

    fn tracked_binding_specs_from_sites(sites: &[TrackedSemanticAllocSite]) -> TrackedBindingSpecs {
        let mut specs = TrackedBindingSpecs::default();
        for site in sites {
            specs
                .by_fn
                .entry(site.fn_name.clone())
                .or_default()
                .insert(site.binding_name.clone());
        }
        specs
    }

    fn collect_rewritten_tracked_unsafe_stats(
        tcx: TyCtxt<'_>,
        tracked_bindings: &TrackedBindingSpecs,
    ) -> RewrittenUnsafeStats {
        struct Visitor<'a, 'tcx> {
            tcx: TyCtxt<'tcx>,
            typeck: &'a rustc_middle::ty::TypeckResults<'tcx>,
            tracked_bindings: &'a FxHashSet<String>,
            free_like_wrappers: &'a FxHashSet<LocalDefId>,
            root_of_local: FxHashMap<HirId, HirId>,
            stats: RewrittenUnsafeStats,
        }

        impl<'a, 'tcx> Visitor<'a, 'tcx> {
            fn maybe_seed_tracked_binding(&mut self, hir_id: HirId) {
                if !self.typeck.node_type(hir_id).is_raw_ptr() {
                    return;
                }
                let binding_name = self.tcx.hir_name(hir_id).to_string();
                if self.tracked_bindings.contains(&binding_name) {
                    self.root_of_local.insert(hir_id, hir_id);
                }
            }

            fn assign_or_clear_local_alias(
                &mut self,
                lhs_hir_id: HirId,
                lhs_ty: ty::Ty<'tcx>,
                rhs: &'tcx hir::Expr<'tcx>,
            ) {
                if !lhs_ty.is_raw_ptr() {
                    return;
                }
                if let Some(root) = root_of_raw_expr(rhs, &self.root_of_local) {
                    self.root_of_local.insert(lhs_hir_id, root);
                } else if !hir_is_null_like_ptr_arg(self.tcx, rhs) {
                    self.root_of_local.remove(&lhs_hir_id);
                }
            }
        }

        impl<'tcx> hir::intravisit::Visitor<'tcx> for Visitor<'_, 'tcx> {
            type NestedFilter = OnlyBodies;

            fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
                self.tcx
            }

            fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
                if let hir::StmtKind::Let(let_stmt) = stmt.kind
                    && let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind
                {
                    self.maybe_seed_tracked_binding(hir_id);
                    if let Some(init) = let_stmt.init {
                        let lhs_ty = self.typeck.node_type(hir_id);
                        self.assign_or_clear_local_alias(hir_id, lhs_ty, init);
                    }
                }
                hir::intravisit::walk_stmt(self, stmt);
            }

            fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
                if let Some(kind) = box_bridge_call_kind(expr) {
                    match kind {
                        "leak" => self.stats.bridge_calls.leak += 1,
                        "from_raw" => self.stats.bridge_calls.from_raw += 1,
                        "into_raw" => self.stats.bridge_calls.into_raw += 1,
                        _ => {}
                    }
                }

                if let hir::ExprKind::Unary(hir::UnOp::Deref, inner) = expr.kind
                    && self
                        .tcx
                        .typeck(expr.hir_id.owner)
                        .expr_ty(inner)
                        .is_raw_ptr()
                    && root_of_raw_expr(inner, &self.root_of_local).is_some()
                {
                    self.stats.dereferences += 1;
                }

                if let hir::ExprKind::Call(_, args) = expr.kind
                    && args.len() == 1
                    && (hir_call_matches_foreign_name(self.tcx, expr, "free")
                        || hir_called_local_fn(self.tcx, expr)
                            .is_some_and(|def_id| self.free_like_wrappers.contains(&def_id)))
                    && self
                        .tcx
                        .typeck(expr.hir_id.owner)
                        .expr_ty(&args[0])
                        .is_raw_ptr()
                    && root_of_raw_expr(&args[0], &self.root_of_local).is_some()
                {
                    self.stats.frees += 1;
                }

                if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                    && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = lhs.kind
                    && let hir::def::Res::Local(lhs_hir_id) = path.res
                {
                    let lhs_ty = self.typeck.expr_ty(lhs);
                    self.assign_or_clear_local_alias(lhs_hir_id, lhs_ty, rhs);
                }

                hir::intravisit::walk_expr(self, expr);
            }
        }

        let free_like_wrappers = collect_local_free_wrappers(tcx);
        let mut stats = RewrittenUnsafeStats::default();
        let crate_hir = tcx.hir_crate(());
        for maybe_owner in crate_hir.owners.iter() {
            let Some(owner) = maybe_owner.as_owner() else {
                continue;
            };
            let hir::OwnerNode::Item(item) = owner.node() else {
                continue;
            };
            let hir::ItemKind::Fn { body, .. } = item.kind else {
                continue;
            };
            let fn_name = tcx.item_name(item.owner_id.def_id.to_def_id()).to_string();
            let Some(fn_tracked_bindings) = tracked_bindings.by_fn.get(&fn_name) else {
                continue;
            };
            let mut visitor = Visitor {
                tcx,
                typeck: tcx.typeck(item.owner_id.def_id),
                tracked_bindings: fn_tracked_bindings,
                free_like_wrappers: &free_like_wrappers,
                root_of_local: FxHashMap::default(),
                stats: RewrittenUnsafeStats::default(),
            };
            visitor.visit_body(tcx.hir_body(body));
            stats += visitor.stats;
        }
        stats
    }

    fn analyze_local_allocator_roots(
        tcx: TyCtxt<'_>,
        did: LocalDefId,
        alloc_wrappers: &FxHashMap<LocalDefId, AllocWrapperInfo>,
        free_like_wrappers: &FxHashSet<LocalDefId>,
    ) -> Vec<TrackedSemanticAllocSite> {
        #[derive(Clone, Debug)]
        struct RootState {
            site: TrackedSemanticAllocSite,
            stored_to_projection: bool,
            returned: bool,
        }

        struct Visitor<'a, 'tcx> {
            tcx: TyCtxt<'tcx>,
            did: LocalDefId,
            typeck: &'a rustc_middle::ty::TypeckResults<'tcx>,
            free_like_wrappers: &'a FxHashSet<LocalDefId>,
            root_of_local: FxHashMap<HirId, HirId>,
            states: FxHashMap<HirId, RootState>,
        }

        impl<'a, 'tcx> Visitor<'a, 'tcx> {
            fn register_root(
                &mut self,
                hir_id: HirId,
                rhs: &'tcx hir::Expr<'tcx>,
                lhs_ty: ty::Ty<'tcx>,
            ) {
                let Some((lhs_inner_ty, _)) = unwrap_ptr_from_mir_ty(lhs_ty) else {
                    return;
                };
                let state = RootState {
                    site: TrackedSemanticAllocSite {
                        hir_id,
                        fn_name: self.tcx.item_name(self.did.to_def_id()).to_string(),
                        binding_name: self.tcx.hir_name(hir_id).to_string(),
                        kind: classify_semantic_allocator_kind(self.tcx, lhs_inner_ty, rhs),
                        outermost: false,
                        shape: SafetySiteShape::NonOutermostLocalRoot,
                        deref_count: 0,
                        free_count: 0,
                    },
                    stored_to_projection: false,
                    returned: false,
                };
                self.root_of_local.insert(hir_id, hir_id);
                self.states.insert(hir_id, state);
            }

            fn assign_or_clear_local_alias(
                &mut self,
                lhs_hir_id: HirId,
                lhs_ty: ty::Ty<'tcx>,
                rhs: &'tcx hir::Expr<'tcx>,
            ) {
                if !lhs_ty.is_raw_ptr() {
                    return;
                }
                if let Some(root) = root_of_raw_expr(rhs, &self.root_of_local) {
                    self.root_of_local.insert(lhs_hir_id, root);
                } else if !hir_is_null_like_ptr_arg(self.tcx, rhs) {
                    self.root_of_local.remove(&lhs_hir_id);
                }
            }

            fn mark_projection_escape(&mut self, rhs: &'tcx hir::Expr<'tcx>) {
                if let Some(root) = root_of_raw_expr(rhs, &self.root_of_local)
                    && let Some(state) = self.states.get_mut(&root)
                {
                    state.stored_to_projection = true;
                }
            }

            fn mark_returned(&mut self, expr: &'tcx hir::Expr<'tcx>) {
                if let Some(root) = root_of_raw_expr(expr, &self.root_of_local)
                    && let Some(state) = self.states.get_mut(&root)
                {
                    state.returned = true;
                }
            }

            fn record_raw_deref(&mut self, expr: &'tcx hir::Expr<'tcx>) {
                let hir::ExprKind::Unary(hir::UnOp::Deref, inner) = expr.kind else {
                    return;
                };
                if !self.typeck.expr_ty(inner).is_raw_ptr() {
                    return;
                }
                let Some(root) = root_of_raw_expr(inner, &self.root_of_local) else {
                    return;
                };
                if let Some(state) = self.states.get_mut(&root) {
                    state.site.deref_count += 1;
                }
            }

            fn record_free_like_use(&mut self, expr: &'tcx hir::Expr<'tcx>) {
                let hir::ExprKind::Call(_, args) = expr.kind else {
                    return;
                };
                let [arg] = args else {
                    return;
                };
                let is_free_like = hir_call_matches_foreign_name(self.tcx, expr, "free")
                    || hir_called_local_fn(self.tcx, expr)
                        .is_some_and(|def_id| self.free_like_wrappers.contains(&def_id));
                if !is_free_like {
                    return;
                }
                let Some(root) = root_of_raw_expr(arg, &self.root_of_local) else {
                    return;
                };
                if let Some(state) = self.states.get_mut(&root) {
                    state.site.free_count += 1;
                }
            }
        }

        impl<'tcx> hir::intravisit::Visitor<'tcx> for Visitor<'_, 'tcx> {
            type NestedFilter = OnlyBodies;

            fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
                self.tcx
            }

            fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
                if let hir::StmtKind::Let(let_stmt) = stmt.kind
                    && let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind
                    && let Some(init) = let_stmt.init
                {
                    let lhs_ty = self.typeck.node_type(hir_id);
                    if hir_is_direct_allocator_root(self.tcx, init) {
                        self.register_root(hir_id, init, lhs_ty);
                    } else {
                        self.assign_or_clear_local_alias(hir_id, lhs_ty, init);
                    }
                }
                hir::intravisit::walk_stmt(self, stmt);
            }

            fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
                self.record_raw_deref(expr);
                self.record_free_like_use(expr);

                match expr.kind {
                    hir::ExprKind::Assign(lhs, rhs, _) => {
                        if let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = lhs.kind
                            && let hir::def::Res::Local(lhs_hir_id) = path.res
                        {
                            let lhs_ty = self.typeck.expr_ty(lhs);
                            if hir_is_direct_allocator_root(self.tcx, rhs) {
                                self.register_root(lhs_hir_id, rhs, lhs_ty);
                            } else {
                                self.assign_or_clear_local_alias(lhs_hir_id, lhs_ty, rhs);
                            }
                        } else {
                            self.mark_projection_escape(rhs);
                        }
                    }
                    hir::ExprKind::Ret(Some(ret)) => self.mark_returned(ret),
                    _ => {}
                }

                hir::intravisit::walk_expr(self, expr);
            }

            fn visit_body(&mut self, body: &hir::Body<'tcx>) -> Self::Result {
                hir::intravisit::walk_body(self, body);
                self.mark_returned(unwrap_body_tail(body.value));
            }
        }

        let hir::Node::Item(item) = tcx.hir_node_by_def_id(did) else {
            return Vec::new();
        };
        let hir::ItemKind::Fn { body, .. } = item.kind else {
            return Vec::new();
        };
        let body = tcx.hir_body(body);
        let mut visitor = Visitor {
            tcx,
            did,
            typeck: tcx.typeck(did),
            free_like_wrappers,
            root_of_local: FxHashMap::default(),
            states: FxHashMap::default(),
        };
        visitor.visit_body(body);

        let wrapper_principal_root = if alloc_wrappers.contains_key(&did) {
            visitor
                .states
                .iter()
                .find_map(|(hir_id, state)| state.returned.then_some(*hir_id))
        } else {
            None
        };

        let mut sites = visitor
            .states
            .into_iter()
            .map(|(hir_id, mut state)| {
                if Some(hir_id) == wrapper_principal_root {
                    state.site.outermost = true;
                    state.site.shape = SafetySiteShape::AllocatorWrapperPrincipalLocal;
                } else if alloc_wrappers.contains_key(&did) {
                    state.site.outermost = false;
                    state.site.shape = SafetySiteShape::NonOutermostLocalRoot;
                } else if !state.stored_to_projection {
                    state.site.outermost = true;
                    state.site.shape = SafetySiteShape::DirectLocalRoot;
                } else {
                    state.site.outermost = false;
                    state.site.shape = SafetySiteShape::NonOutermostLocalRoot;
                }
                state.site
            })
            .collect::<Vec<_>>();
        sites.sort_by_key(|site| (site.fn_name.clone(), site.binding_name.clone()));
        sites
    }

    fn collect_semantic_allocator_sites(
        tcx: TyCtxt<'_>,
        input: &RustProgram<'_>,
    ) -> Vec<TrackedSemanticAllocSite> {
        let alloc_wrappers = collect_local_allocator_wrappers(tcx);
        let free_like_wrappers = collect_local_free_wrappers(tcx);
        let mut sites = Vec::new();
        for did in &input.functions {
            sites.extend(analyze_local_allocator_roots(
                tcx,
                *did,
                &alloc_wrappers,
                &free_like_wrappers,
            ));
        }
        sites
    }

    fn analyze_pointer_safety_for_program(tcx: TyCtxt<'_>) -> PointerSafetyAnalysisResult {
        let (input, analysis) = build_analysis(tcx);
        let tracked_sites = collect_semantic_allocator_sites(tcx, &input);
        let lifetime_plans = super::super::lifetimes::LifetimePlans::new(&input, &analysis);
        let fn_ptr_groups = FnPtrGroups::default();
        let sig_decs = SigDecisions::new(&input, &analysis, &lifetime_plans, &fn_ptr_groups);
        let initial_ptr_kinds = collect_diffs(&input, &analysis, &sig_decs, &fn_ptr_groups);
        let (_sig_decs, final_ptr_kinds, _reason_map, _usage_subreason_map) =
            simulate_transform_reasons(tcx, &input, &analysis);

        let mut before_total = SafetyBeforeStats::default();
        let mut before_outermost = SafetyBeforeStats::default();
        let mut safe_box_sites = SplitKindCounts::default();

        let mir_local_maps = input
            .functions
            .iter()
            .map(|did| (*did, utils::ir::map_thir_to_mir(*did, false, tcx)))
            .collect::<FxHashMap<_, _>>();

        for site in &tracked_sites {
            before_total.record_site(site);
            if site.outermost {
                before_outermost.record_site(site);
            }

            if !site.outermost {
                continue;
            }

            let final_kind = final_ptr_kinds.get(&site.hir_id).copied();
            match final_kind {
                Some(PtrKind::Box | PtrKind::OptBox) => {
                    safe_box_sites.bump(SafetyAllocKind::Scalar);
                    continue;
                }
                Some(PtrKind::BoxedSlice | PtrKind::OptBoxedSlice) => {
                    safe_box_sites.bump(SafetyAllocKind::Array);
                    continue;
                }
                _ => {}
            }

            if matches!(
                initial_ptr_kinds.get(&site.hir_id).copied(),
                Some(PtrKind::Raw(_))
            ) {
                let did = site.hir_id.owner.def_id;
                let hir_to_mir = mir_local_maps
                    .get(&did)
                    .expect("expected THIR->MIR map for tracked site");
                let local = *hir_to_mir
                    .binding_to_local
                    .get(&site.hir_id)
                    .expect("expected tracked site local mapping");
                let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
                let _ = classify_initial_raw_reason(
                    &analysis,
                    did,
                    local,
                    &body.local_decls[local],
                    tcx,
                );
            }
        }

        PointerSafetyAnalysisResult {
            before_total,
            before_outermost,
            safe_box_sites,
            tracked_sites,
        }
    }

    fn analyze_pointer_safety_for_code(
        code: &str,
    ) -> (PointerSafetyAnalysisResult, RewrittenUnsafeStats) {
        let result = ::utils::compilation::run_compiler_on_str(code, |tcx| {
            analyze_pointer_safety_for_program(tcx)
        })
        .unwrap();
        let tracked_bindings = tracked_binding_specs_from_sites(&result.tracked_sites);
        let (rewritten, _) = ::utils::compilation::run_compiler_on_str(code, |tcx| {
            replace_local_borrows(&Config::default(), tcx)
        })
        .unwrap();
        let mut after = ::utils::compilation::run_compiler_on_str(&rewritten, |tcx| {
            collect_rewritten_tracked_unsafe_stats(tcx, &tracked_bindings)
        })
        .unwrap_or_else(|_| panic!("rewritten snippet failed to compile:\n{rewritten}"));
        after.bridge_calls = bridge_call_counts_from_source(&rewritten);
        (result, after)
    }

    fn classify_initial_raw_reason<'tcx>(
        analysis: &super::super::Analysis,
        did: LocalDefId,
        local: rustc_middle::mir::Local,
        decl: &rustc_middle::mir::LocalDecl<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> &'static str {
        let (inner_ty, _) = unwrap_ptr_from_mir_ty(decl.ty).expect("expected pointer local");
        if inner_ty.is_c_void(tcx) || utils::file::contains_file_ty(inner_ty, tcx) {
            return "c_void_or_file";
        }

        let mutable_pointers = analysis
            .mutability_result
            .function_body_facts(did)
            .map(|mutabilities| mutabilities.iter().any(|m| m.is_mutable()))
            .collect::<rustc_index::IndexVec<rustc_middle::mir::Local, _>>();
        let aliases = analysis.aliases.get(&did).and_then(|map| map.get(&local));
        if aliases.is_some_and(|aliases| {
            std::iter::once(local)
                .chain(aliases.iter().copied())
                .any(|alias_local| mutable_pointers[alias_local])
        }) {
            return "alias_cluster";
        }

        let array_pointers = analysis
            .fatness_result
            .function_body_facts(did)
            .map(|fatnesses| fatnesses.iter().next().map(|f| f.is_arr()).unwrap_or(false))
            .collect::<rustc_index::IndexVec<rustc_middle::mir::Local, _>>();
        let needs_cursor = analysis
            .offset_sign_result
            .access_signs
            .get(&did)
            .is_some_and(|signs| signs.contains(local));
        let is_local_struct = matches!(
            inner_ty.kind(),
            ty::TyKind::Adt(adt_def, _) if adt_def.did().is_local() && adt_def.is_struct()
        );
        let owning = analysis
            .ownership_schemes
            .as_ref()
            .expect("ownership analysis should exist")
            .fn_results(&did.to_def_id())
            .local_result(local)
            .first()
            .is_some_and(crate::analyses::ownership::Ownership::is_owning);

        if owning && array_pointers[local] {
            if needs_cursor {
                return "array_needs_cursor";
            }
            if is_local_struct {
                return "array_local_struct";
            }
        }

        if owning
            && matches!(
                inner_ty.kind(),
                ty::TyKind::RawPtr(..) | ty::TyKind::Ref(..)
            )
        {
            return "nested_raw_or_ref";
        }

        "other_initial_raw"
    }

    fn simulate_transform_reasons<'tcx>(
        tcx: TyCtxt<'tcx>,
        input: &RustProgram<'tcx>,
        analysis: &super::super::Analysis,
    ) -> (
        SigDecisions,
        FxHashMap<HirId, PtrKind>,
        FxHashMap<HirId, Vec<&'static str>>,
        FxHashMap<HirId, Vec<&'static str>>,
    ) {
        let lifetime_plans = super::super::lifetimes::LifetimePlans::new(input, analysis);
        let fn_ptr_groups = FnPtrGroups::default();
        let mut sig_decs = SigDecisions::new(input, analysis, &lifetime_plans, &fn_ptr_groups);
        let mut ptr_kinds = collect_diffs(input, analysis, &sig_decs, &fn_ptr_groups);
        let free_like_wrappers = collect_local_free_wrappers(tcx);
        let local_raw_free_summaries = collect_local_raw_free_summaries(tcx, &free_like_wrappers);
        let local_raw_param_summaries =
            collect_local_raw_param_summaries(tcx, &sig_decs, &free_like_wrappers);
        let mut reason_map: FxHashMap<HirId, Vec<&'static str>> = FxHashMap::default();
        let mut usage_subreason_map: FxHashMap<HirId, Vec<&'static str>> = FxHashMap::default();
        let mut forced_raw_bindings = downgrade_unsupported_allocator_box_kinds(tcx, &ptr_kinds);
        for hir_id in &forced_raw_bindings {
            reason_map
                .entry(*hir_id)
                .or_default()
                .push("unsupported_allocator_root");
        }
        normalize_forced_raw_bindings(tcx, &mut ptr_kinds, &forced_raw_bindings);
        normalize_owning_call_result_bindings(tcx, &sig_decs, &mut ptr_kinds, &forced_raw_bindings);

        loop {
            let mut changed = false;
            let local_struct_downgrades =
                downgrade_local_struct_bindings(tcx, &mut sig_decs, &ptr_kinds);
            if local_struct_downgrades.changed {
                changed = true;
            }
            let (box_input_changed, unsupported_box_input_bindings) =
                downgrade_unsupported_box_inputs(tcx, &mut sig_decs, &local_raw_free_summaries);
            if box_input_changed {
                changed = true;
            }
            if !downgrade_unsupported_box_outputs(
                tcx,
                &mut sig_decs,
                &ptr_kinds,
                &FxHashSet::default(),
            )
            .is_empty()
            {
                changed = true;
            }
            if downgrade_freed_borrow_outputs(tcx, &mut sig_decs, &free_like_wrappers).changed() {
                changed = true;
            }
            if !downgrade_cursor_inputs_from_unanchored_raw_callers(tcx, &mut sig_decs, &ptr_kinds)
                .is_empty()
            {
                changed = true;
            }
            normalize_owning_call_result_bindings(
                tcx,
                &sig_decs,
                &mut ptr_kinds,
                &forced_raw_bindings,
            );

            let raw_call_result_bindings =
                collect_raw_call_result_bindings(tcx, &sig_decs, &ptr_kinds);
            let raw_local_assignment_bindings =
                collect_raw_local_assignment_bindings(tcx, &ptr_kinds);
            let unsupported_box_target_bindings =
                collect_unsupported_box_target_bindings(tcx, &sig_decs, &ptr_kinds);
            let unsupported_box_usage_subreasons = collect_unsupported_box_usage_subreasons(
                tcx,
                &sig_decs,
                &ptr_kinds,
                &free_like_wrappers,
                &local_raw_param_summaries,
            );
            let unsupported_box_usage_bindings = collect_unsupported_box_usage_bindings(
                tcx,
                &sig_decs,
                &ptr_kinds,
                &free_like_wrappers,
                &local_raw_param_summaries,
            );

            let mut record_new = |bindings: &FxHashSet<HirId>, reason: &'static str| {
                for hir_id in bindings {
                    if !forced_raw_bindings.contains(hir_id) {
                        reason_map.entry(*hir_id).or_default().push(reason);
                    }
                }
            };
            record_new(
                &local_struct_downgrades.call_conflict,
                "local_struct_call_conflict",
            );
            record_new(
                &local_struct_downgrades.call_binding_conflict,
                "local_struct_call_binding_conflict",
            );
            record_new(
                &local_struct_downgrades.field_borrow_conflict,
                "local_struct_field_borrow_conflict",
            );
            record_new(
                &local_struct_downgrades.reborrow_assignment,
                "local_struct_reborrow_assignment",
            );
            record_new(
                &local_struct_downgrades.field_mut_ptr,
                "local_struct_field_mut_ptr",
            );
            record_new(
                &local_struct_downgrades.static_projection,
                "local_struct_static_projection",
            );
            record_new(
                &local_struct_downgrades.foreign_mut_call,
                "local_struct_foreign_mut_call",
            );
            record_new(&unsupported_box_input_bindings, "unsupported_box_input");
            record_new(&raw_call_result_bindings, "raw_call_result");
            record_new(&raw_local_assignment_bindings, "raw_local_assignment");
            record_new(&unsupported_box_target_bindings, "unsupported_box_target");
            record_new(&unsupported_box_usage_bindings, "unsupported_box_usage");
            for hir_id in &unsupported_box_usage_bindings {
                if forced_raw_bindings.contains(hir_id) {
                    continue;
                }
                let entry = usage_subreason_map.entry(*hir_id).or_default();
                for subreason in unsupported_box_usage_subreasons
                    .get(hir_id)
                    .into_iter()
                    .flatten()
                    .copied()
                {
                    if !entry.contains(&subreason) {
                        entry.push(subreason);
                    }
                }
            }

            let old_len = forced_raw_bindings.len();
            local_struct_downgrades.extend_forced_raw_bindings(&mut forced_raw_bindings);
            forced_raw_bindings.extend(unsupported_box_input_bindings);
            forced_raw_bindings.extend(raw_call_result_bindings);
            forced_raw_bindings.extend(raw_local_assignment_bindings);
            forced_raw_bindings.extend(unsupported_box_target_bindings);
            forced_raw_bindings.extend(unsupported_box_usage_bindings);
            if forced_raw_bindings.len() != old_len {
                changed = true;
                normalize_forced_raw_bindings(tcx, &mut ptr_kinds, &forced_raw_bindings);
                normalize_owning_call_result_bindings(
                    tcx,
                    &sig_decs,
                    &mut ptr_kinds,
                    &forced_raw_bindings,
                );
            }

            if !changed {
                break;
            }
        }

        (sig_decs, ptr_kinds, reason_map, usage_subreason_map)
    }

    fn collect_unsupported_box_usage_subreasons(
        tcx: TyCtxt<'_>,
        sig_decs: &SigDecisions,
        ptr_kinds: &FxHashMap<HirId, PtrKind>,
        free_like_wrappers: &FxHashSet<LocalDefId>,
        local_raw_param_summaries: &FxHashMap<(LocalDefId, usize), LocalRawParamSummary>,
    ) -> FxHashMap<HirId, Vec<&'static str>> {
        struct UsageSubreasonVisitor<'a, 'tcx> {
            tcx: TyCtxt<'tcx>,
            sig_decs: &'a SigDecisions,
            ptr_kinds: &'a FxHashMap<HirId, PtrKind>,
            free_like_wrappers: &'a FxHashSet<LocalDefId>,
            local_raw_param_summaries: &'a FxHashMap<(LocalDefId, usize), LocalRawParamSummary>,
            byte_view_roots: FxHashMap<HirId, HirId>,
            reasons: FxHashMap<HirId, FxHashSet<&'static str>>,
        }

        impl<'tcx> UsageSubreasonVisitor<'_, 'tcx> {
            fn record(&mut self, root: HirId, reason: &'static str) {
                self.reasons.entry(root).or_default().insert(reason);
            }

            fn owning_root_of(&self, hir_id: HirId) -> Option<HirId> {
                if self
                    .ptr_kinds
                    .get(&hir_id)
                    .is_some_and(PtrKind::is_owning_box_like)
                {
                    Some(hir_id)
                } else {
                    self.byte_view_roots.get(&hir_id).copied()
                }
            }

            fn maybe_mark_byte_view_alias(
                &mut self,
                lhs_hir_id: HirId,
                lhs_ty: ty::Ty<'tcx>,
                rhs: &'tcx hir::Expr<'tcx>,
            ) {
                let Some((lhs_inner_ty, _)) = unwrap_ptr_from_mir_ty(lhs_ty) else {
                    return;
                };
                if !ty_is_byte_sized_raw_inner(lhs_inner_ty) {
                    return;
                }
                let Some(rhs_hir_id) = hir_unwrapped_local_id(rhs) else {
                    return;
                };
                let Some(root) = self.owning_root_of(rhs_hir_id) else {
                    return;
                };
                let rhs_ty = self.tcx.typeck(rhs_hir_id.owner).node_type(rhs_hir_id);
                let Some((rhs_inner_ty, _)) = unwrap_ptr_from_mir_ty(rhs_ty) else {
                    return;
                };
                if !ty_is_byte_sized_raw_inner(rhs_inner_ty)
                    || !hir_is_casted_local(rhs, rhs_hir_id)
                {
                    return;
                }
                self.byte_view_roots.insert(lhs_hir_id, root);
                self.record(root, "byte_view_alias");
            }
        }

        impl<'tcx> Visitor<'tcx> for UsageSubreasonVisitor<'_, 'tcx> {
            fn visit_stmt(&mut self, stmt: &'tcx hir::Stmt<'tcx>) -> Self::Result {
                if let hir::StmtKind::Let(let_stmt) = stmt.kind
                    && let hir::PatKind::Binding(_, hir_id, _, _) = let_stmt.pat.kind
                    && let Some(init) = let_stmt.init
                {
                    let lhs_ty = self.tcx.typeck(hir_id.owner).node_type(hir_id);
                    self.maybe_mark_byte_view_alias(hir_id, lhs_ty, init);
                }
                intravisit::walk_stmt(self, stmt);
            }

            fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
                if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
                    && let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = lhs.kind
                    && let Res::Local(lhs_hir_id) = path.res
                {
                    let lhs_ty = self.tcx.typeck(expr.hir_id.owner).expr_ty(lhs);
                    self.maybe_mark_byte_view_alias(lhs_hir_id, lhs_ty, rhs);
                }

                if let Some(local_callee) = hir_called_local_fn(self.tcx, expr)
                    && let hir::ExprKind::Call(_, args) = expr.kind
                {
                    for (arg_index, arg) in args.iter().enumerate() {
                        let Some(hir_id) = hir_unwrapped_local_id(arg) else {
                            continue;
                        };
                        let Some(root) = self.owning_root_of(hir_id) else {
                            continue;
                        };
                        if !local_callee_arg_preserves_owning_usage(
                            self.sig_decs,
                            self.local_raw_param_summaries,
                            local_callee,
                            arg_index,
                        ) {
                            self.record(root, "local_callee_non_borrow_only");
                        }
                    }
                }

                if let Some((hir_id, _)) =
                    hir_free_like_arg_local_id(self.tcx, expr, self.free_like_wrappers)
                    && let Some(root) = self.owning_root_of(hir_id)
                {
                    self.record(root, "free_like_wrapper");
                }

                intravisit::walk_expr(self, expr);
            }
        }

        let mut visitor = UsageSubreasonVisitor {
            tcx,
            sig_decs,
            ptr_kinds,
            free_like_wrappers,
            local_raw_param_summaries,
            byte_view_roots: FxHashMap::default(),
            reasons: FxHashMap::default(),
        };
        let crate_hir = tcx.hir_crate(());
        for maybe_owner in crate_hir.owners.iter() {
            let Some(owner) = maybe_owner.as_owner() else {
                continue;
            };
            let hir::OwnerNode::Item(item) = owner.node() else {
                continue;
            };
            let hir::ItemKind::Fn { body, .. } = item.kind else {
                continue;
            };
            visitor.visit_body(tcx.hir_body(body));
        }

        let mut out = FxHashMap::default();
        for (hir_id, reasons) in visitor.reasons {
            let mut reasons = reasons.into_iter().collect::<Vec<_>>();
            reasons.sort();
            out.insert(hir_id, reasons);
        }
        out
    }

    fn find_fn_did(tcx: TyCtxt<'_>, fn_name: &str) -> LocalDefId {
        tcx.hir_crate(())
            .owners
            .iter()
            .filter_map(|maybe_owner| maybe_owner.as_owner())
            .find_map(|owner| {
                let OwnerNode::Item(item) = owner.node() else {
                    return None;
                };
                let HirItemKind::Fn { .. } = item.kind else {
                    return None;
                };
                (tcx.item_name(item.owner_id.def_id.to_def_id()).as_str() == fn_name)
                    .then_some(item.owner_id.def_id)
            })
            .expect("expected matching function")
    }

    fn find_param_hir_id(tcx: TyCtxt<'_>, fn_name: &str, param_name: &str) -> HirId {
        tcx.hir_crate(())
            .owners
            .iter()
            .filter_map(|maybe_owner| maybe_owner.as_owner())
            .find_map(|owner| {
                let OwnerNode::Item(item) = owner.node() else {
                    return None;
                };
                let HirItemKind::Fn { body, .. } = item.kind else {
                    return None;
                };
                if tcx.item_name(item.owner_id.def_id.to_def_id()).as_str() != fn_name {
                    return None;
                }
                let body = tcx.hir_body(body);
                body.params.iter().find_map(|param| {
                    let hir::PatKind::Binding(_, hir_id, ident, _) = param.pat.kind else {
                        return None;
                    };
                    (ident.name.as_str() == param_name).then_some(hir_id)
                })
            })
            .expect("expected matching param hir id")
    }

    #[test]
    fn pointer_safety_stats_count_scalar_outermost_root_and_safe_box_free_consumption() {
        let code = r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn free_scalar() {
    let mut p: *mut i32 = malloc(std::mem::size_of::<i32>());
    *p = 7;
    free(p as *mut core::ffi::c_void);
}
"#;

        let (analysis, after) = analyze_pointer_safety_for_code(code);
        assert_eq!(
            analysis.before_total,
            SafetyBeforeStats {
                allocation_sites: SplitKindCounts {
                    scalar: 1,
                    array: 0
                },
                dereferences: SplitKindCounts {
                    scalar: 1,
                    array: 0
                },
                frees: SplitKindCounts {
                    scalar: 1,
                    array: 0
                },
            }
        );
        assert_eq!(analysis.before_outermost, analysis.before_total);
        assert_eq!(
            analysis.safe_box_sites,
            SplitKindCounts {
                scalar: 1,
                array: 0
            }
        );
        assert_eq!(after.dereferences, 0);
        assert_eq!(after.frees, 0);
        assert_eq!(after.bridge_calls, BridgeCallCounts::default());
    }

    #[test]
    fn pointer_safety_stats_count_array_outermost_root_and_safe_boxed_slice_free_consumption() {
        let code = r#"
extern "C" {
    fn calloc(count: usize, size: usize) -> *mut i32;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn free_array() {
    let mut p: *mut i32 = calloc(4, std::mem::size_of::<i32>());
    *p.offset(1) = 7;
    free(p as *mut core::ffi::c_void);
}
"#;

        let (analysis, after) = analyze_pointer_safety_for_code(code);
        assert_eq!(
            analysis.before_total,
            SafetyBeforeStats {
                allocation_sites: SplitKindCounts {
                    scalar: 0,
                    array: 1
                },
                dereferences: SplitKindCounts {
                    scalar: 0,
                    array: 1
                },
                frees: SplitKindCounts {
                    scalar: 0,
                    array: 1
                },
            }
        );
        assert_eq!(analysis.before_outermost, analysis.before_total);
        assert_eq!(
            analysis.safe_box_sites,
            SplitKindCounts {
                scalar: 0,
                array: 1
            }
        );
        assert_eq!(after.dereferences, 0);
        assert_eq!(after.frees, 0);
        assert_eq!(after.bridge_calls, BridgeCallCounts::default());
    }

    #[test]
    fn pointer_safety_stats_mark_allocator_wrapper_principal_local_as_outermost() {
        let code = r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

pub unsafe fn alloc_one() -> *mut i32 {
    let p: *mut i32 = malloc(std::mem::size_of::<i32>());
    p
}
"#;

        let (analysis, _after) = analyze_pointer_safety_for_code(code);
        assert_eq!(analysis.tracked_sites.len(), 1);
        let site = &analysis.tracked_sites[0];
        assert_eq!(site.shape, SafetySiteShape::AllocatorWrapperPrincipalLocal);
        assert!(site.outermost);
        assert_eq!(analysis.before_total.allocation_sites.total(), 1);
        assert_eq!(analysis.before_outermost.allocation_sites.total(), 1);
    }

    #[test]
    fn pointer_safety_stats_mark_field_stored_root_as_non_outermost() {
        let code = r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

#[repr(C)]
pub struct Holder {
    pub data: *mut i32,
}

pub unsafe fn stash(owner: *mut Holder) {
    let data: *mut i32 = malloc(std::mem::size_of::<i32>());
    (*owner).data = data;
}
"#;

        let (analysis, _after) = analyze_pointer_safety_for_code(code);
        assert_eq!(analysis.tracked_sites.len(), 1);
        let site = &analysis.tracked_sites[0];
        assert_eq!(site.shape, SafetySiteShape::NonOutermostLocalRoot);
        assert!(!site.outermost);
        assert_eq!(analysis.before_total.allocation_sites.total(), 1);
        assert_eq!(analysis.before_outermost.allocation_sites.total(), 0);
    }

    #[test]
    fn pointer_safety_stats_capture_scalar_raw_bridge_calls() {
        let code = r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn free_nested() {
    let mut p: *mut *mut i32 =
        malloc(std::mem::size_of::<*mut i32>()) as *mut *mut i32;
    free(p as *mut core::ffi::c_void);
}
"#;

        let (analysis, after) = analyze_pointer_safety_for_code(code);
        assert_eq!(analysis.safe_box_sites.total(), 0);
        assert_eq!(after.frees, 0);
        assert_eq!(after.bridge_calls.leak, 1);
        assert_eq!(after.bridge_calls.from_raw, 1);
        assert_eq!(after.bridge_calls.into_raw, 0);
    }

    #[test]
    fn pointer_safety_stats_capture_array_raw_bridge_calls() {
        let code = r#"
extern "C" {
    fn realloc(ptr: *mut core::ffi::c_void, size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn alloc_chars(len: usize) {
    let buf: *mut core::ffi::c_char =
        realloc(std::ptr::null_mut::<core::ffi::c_void>(), len) as *mut core::ffi::c_char;
    free(buf as *mut core::ffi::c_void);
}
"#;

        let (analysis, after) = analyze_pointer_safety_for_code(code);
        assert_eq!(analysis.safe_box_sites.total(), 0);
        assert_eq!(after.frees, 0);
        assert_eq!(after.bridge_calls.leak, 1);
        assert_eq!(after.bridge_calls.from_raw, 1);
        assert_eq!(after.bridge_calls.into_raw, 0);
    }

    #[test]
    fn pointer_safety_stats_ignore_untracked_remaining_raw_dereferences() {
        let code = r#"
extern "C" {
    fn malloc(size: usize) -> *mut i32;
}

pub unsafe fn mixed(arg: *mut i32) -> i32 {
    let mut p: *mut i32 = malloc(std::mem::size_of::<i32>());
    *p = 7;
    *arg
}
"#;

        let (analysis, after) = analyze_pointer_safety_for_code(code);
        assert_eq!(
            analysis.before_total,
            SafetyBeforeStats {
                allocation_sites: SplitKindCounts {
                    scalar: 1,
                    array: 0
                },
                dereferences: SplitKindCounts {
                    scalar: 1,
                    array: 0
                },
                frees: SplitKindCounts::default(),
            }
        );
        assert_eq!(after.dereferences, 0);
    }

    #[test]
    fn wrapper_collector_recognizes_returning_local_after_mutation() {
        let code = r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn snprintf(dst: *mut core::ffi::c_char, size: usize, fmt: *const core::ffi::c_char, ...);
}

pub unsafe fn create_msg(v: i32) -> *mut core::ffi::c_char {
    let msg: *mut core::ffi::c_char = malloc(64) as *mut core::ffi::c_char;
    if msg.is_null() {
        return std::ptr::null_mut();
    }
    snprintf(msg, 64, b"value=%d\0" as *const u8 as *const core::ffi::c_char, v);
    msg
}
"#;
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let wrappers = collect_local_allocator_wrappers(tcx);
            let did = tcx
                .hir_crate(())
                .owners
                .iter()
                .filter_map(|maybe_owner| maybe_owner.as_owner())
                .filter_map(|owner| {
                    let OwnerNode::Item(item) = owner.node() else {
                        return None;
                    };
                    let HirItemKind::Fn { .. } = item.kind else {
                        return None;
                    };
                    (tcx.item_name(item.owner_id.def_id.to_def_id()).as_str() == "create_msg")
                        .then_some(item.owner_id.def_id)
                })
                .next()
                .expect("create_msg should exist");
            let names = wrappers
                .keys()
                .map(|def_id| tcx.item_name(def_id.to_def_id()).as_str().to_owned())
                .collect::<Vec<_>>();
            assert!(wrappers.contains_key(&did), "{names:?}");
        })
        .unwrap();
    }

    #[test]
    fn local_struct_call_binding_allows_disjoint_raw_mutable_and_shared_fields() {
        let code = r#"
#[repr(C)]
pub struct Inner {
    pub value: u8,
}

#[repr(C)]
pub struct Ctx {
    pub s: [u8; 65],
    pub inner: Inner,
}

pub unsafe fn consume(mut out: *mut u8, mut inner: *const Inner) {
    let _ = out;
    let _ = inner;
}

pub unsafe fn drive(mut ctx: *mut Ctx) {
    consume((*ctx).s.as_mut_ptr(), &(*ctx).inner);
}
"#;

        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let facts = collect_local_struct_downgrade_facts(tcx);
            let consume_did = find_fn_did(tcx, "consume");
            let drive_did = find_fn_did(tcx, "drive");
            let ctx_hir_id = find_param_hir_id(tcx, "drive", "ctx");
            let mut sig_decs = SigDecisions {
                data: FxHashMap::default(),
            };
            sig_decs.data.insert(
                consume_did,
                SigDecision {
                    input_decs: vec![Some(PtrKind::Raw(true)), Some(PtrKind::OptRef(false))],
                    input_lifetimes: vec![None, None],
                    output_dec: None,
                    output_lifetime: None,
                    signature_locked: false,
                },
            );
            sig_decs.data.insert(
                drive_did,
                SigDecision {
                    input_decs: vec![Some(PtrKind::OptRef(true))],
                    input_lifetimes: vec![None],
                    output_dec: None,
                    output_lifetime: None,
                    signature_locked: false,
                },
            );
            let mut ptr_kinds = FxHashMap::default();
            ptr_kinds.insert(ctx_hir_id, PtrKind::OptRef(true));

            let (changed, bindings) = downgrade_conflicting_local_struct_call_bindings(
                tcx,
                &facts,
                &mut sig_decs,
                &ptr_kinds,
            );
            assert!(!changed && !bindings.contains(&ctx_hir_id), "{bindings:?}");
            assert_eq!(
                sig_decs.data[&drive_did].input_decs[0],
                Some(PtrKind::OptRef(true))
            );

            let mut sig_decs = SigDecisions {
                data: FxHashMap::default(),
            };
            sig_decs.data.insert(
                consume_did,
                SigDecision {
                    input_decs: vec![Some(PtrKind::Slice(true)), Some(PtrKind::OptRef(false))],
                    input_lifetimes: vec![None, None],
                    output_dec: None,
                    output_lifetime: None,
                    signature_locked: false,
                },
            );
            sig_decs.data.insert(
                drive_did,
                SigDecision {
                    input_decs: vec![Some(PtrKind::OptRef(true))],
                    input_lifetimes: vec![None],
                    output_dec: None,
                    output_lifetime: None,
                    signature_locked: false,
                },
            );

            let (changed, bindings) = downgrade_conflicting_local_struct_call_bindings(
                tcx,
                &facts,
                &mut sig_decs,
                &ptr_kinds,
            );
            assert!(changed && bindings.contains(&ctx_hir_id), "{bindings:?}");
            assert_eq!(
                sig_decs.data[&drive_did].input_decs[0],
                Some(PtrKind::Raw(true))
            );
        })
        .unwrap();
    }

    #[test]
    fn force_signature_input_raw_for_binding_clears_input_lifetime() {
        let code = r#"
pub unsafe fn id(x: *mut i32) -> *mut i32 {
    x
}
"#;

        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let did = find_fn_did(tcx, "id");
            let x_hir_id = find_param_hir_id(tcx, "id", "x");
            let lifetime = Symbol::intern("a");
            let mut sig_decs = SigDecisions {
                data: FxHashMap::default(),
            };
            sig_decs.data.insert(
                did,
                SigDecision {
                    input_decs: vec![Some(PtrKind::OptRef(true))],
                    input_lifetimes: vec![Some(lifetime)],
                    output_dec: Some(PtrKind::OptRef(true)),
                    output_lifetime: Some(lifetime),
                    signature_locked: false,
                },
            );

            assert!(force_signature_input_raw_for_binding(
                tcx,
                &mut sig_decs,
                x_hir_id,
            ));

            let sig_dec = &sig_decs.data[&did];
            assert_eq!(sig_dec.input_decs[0], Some(PtrKind::Raw(true)));
            assert_eq!(sig_dec.input_lifetimes[0], None);
            assert_eq!(sig_dec.output_lifetime, Some(lifetime));
        })
        .unwrap();
    }
}
