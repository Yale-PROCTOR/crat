use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    self as hir, HirId,
    def::Res,
    intravisit::{self, Visitor},
};
use rustc_index::{IndexVec, bit_set::DenseBitSet};
use rustc_middle::{
    mir::{Local, LocalDecl, Operand, Rvalue, StatementKind, TerminatorKind},
    ty::{self, TyCtxt},
};
use rustc_span::{Symbol, def_id::LocalDefId};

use super::{
    Analysis,
    collector::collect_fn_ptrs,
    diagnostics::{DecisionDiagnostics, DecisionReason, DecisionStage, DecisionSubject},
};
use crate::{analyses::ownership::Ownership, utils::rustc::RustProgram};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PtrKind {
    /// reference: &mut T for Ref(true), or &T for Ref(false)
    Ref(bool),
    /// optional reference: Option<&mut T> for OptRef(true), or Option<&T> for OptRef(false)
    OptRef(bool),
    /// owning scalar pointer rewritten to Box<T>
    Box,
    /// owning scalar pointer rewritten to Option<Box<T>>
    OptBox,
    /// raw pointer: *mut T for Raw(true), or *const T for Raw(false)
    Raw(bool),
    /// owning array pointer rewritten to Box<[T]>
    BoxedSlice,
    /// owning array pointer rewritten to Option<Box<[T]>>
    OptBoxedSlice,
    /// plain slice: &mut [T] for Slice(true), or &[T] for Slice(false)
    Slice(bool),
    /// slice cursor with offset tracking: SliceCursor<T> for SliceCursor(false),
    /// or SliceCursorMut<T> for SliceCursor(true)
    SliceCursor(bool),
}

impl PtrKind {
    pub fn is_mut(&self) -> bool {
        match self {
            PtrKind::Ref(m)
            | PtrKind::OptRef(m)
            | PtrKind::Raw(m)
            | PtrKind::Slice(m)
            | PtrKind::SliceCursor(m) => *m,
            PtrKind::Box | PtrKind::OptBox | PtrKind::BoxedSlice | PtrKind::OptBoxedSlice => true,
        }
    }

    pub fn is_owning_box_like(&self) -> bool {
        matches!(
            self,
            PtrKind::Box | PtrKind::OptBox | PtrKind::BoxedSlice | PtrKind::OptBoxedSlice
        )
    }

    pub fn is_optional(&self) -> bool {
        matches!(
            self,
            PtrKind::OptRef(_) | PtrKind::OptBox | PtrKind::OptBoxedSlice
        )
    }

    pub fn non_null_variant(self) -> Self {
        match self {
            PtrKind::OptRef(m) => PtrKind::Ref(m),
            PtrKind::OptBox => PtrKind::Box,
            PtrKind::OptBoxedSlice => PtrKind::BoxedSlice,
            other => other,
        }
    }

    pub fn optional_variant(self) -> Self {
        match self {
            PtrKind::Ref(m) => PtrKind::OptRef(m),
            PtrKind::Box => PtrKind::OptBox,
            PtrKind::BoxedSlice => PtrKind::OptBoxedSlice,
            other => other,
        }
    }
}

pub struct DecisionMaker<'tcx> {
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    mutable_pointers: IndexVec<Local, bool>,
    array_pointers: IndexVec<Local, bool>,
    _owning_pointers: IndexVec<Local, bool>,
    _output_params: DenseBitSet<Local>,
    promoted_mut_refs: DenseBitSet<Local>,
    promoted_shared_refs: DenseBitSet<Local>,
    /// Locals that need a SliceCursor because they are offset with potentially-negative values.
    needs_cursor: DenseBitSet<Local>,
    non_null_locals: DenseBitSet<Local>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DecisionInfo {
    pub kind: Option<PtrKind>,
    pub events: Vec<DecisionInfoEvent>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DecisionInfoEvent {
    pub before: Option<PtrKind>,
    pub after: Option<PtrKind>,
    pub reason: DecisionReason,
    pub detail: Option<String>,
}

impl<'tcx> DecisionMaker<'tcx> {
    fn preserve_original_pointer_constness(
        &self,
        decision: Option<PtrKind>,
        is_mut: bool,
    ) -> Option<PtrKind> {
        if is_mut {
            return decision;
        }
        match decision {
            Some(PtrKind::Ref(_)) => Some(PtrKind::Ref(false)),
            Some(PtrKind::OptRef(_)) => Some(PtrKind::OptRef(false)),
            Some(PtrKind::Raw(_)) => Some(PtrKind::Raw(false)),
            Some(PtrKind::Slice(_)) => Some(PtrKind::Slice(false)),
            Some(PtrKind::SliceCursor(_)) => Some(PtrKind::SliceCursor(false)),
            other => other,
        }
    }

    pub fn new(analysis: &Analysis, did: LocalDefId, tcx: TyCtxt<'tcx>) -> Self {
        let mutable_pointers = analysis
            .mutability_result
            .function_body_facts(did)
            .map(|mutabilities| mutabilities.iter().any(|m| m.is_mutable()))
            .collect::<IndexVec<Local, _>>();
        let array_pointers = analysis
            .fatness_result
            .function_body_facts(did)
            .map(|fatnesses| fatnesses.iter().next().map(|f| f.is_arr()).unwrap_or(false))
            .collect::<IndexVec<Local, _>>();
        let promoted_mut_refs = analysis.promoted_mut_ref_result.get(&did).unwrap().clone();
        let promoted_shared_refs = analysis
            .promoted_shared_ref_result
            .get(&did)
            .unwrap()
            .clone();
        let _owning_pointers = if let Some(ownership_schemes) = analysis.ownership_schemes.as_ref()
        {
            let fn_results = ownership_schemes.fn_results(&did.to_def_id());
            (0..mutable_pointers.len())
                .map(|index| {
                    fn_results
                        .local_result(Local::from_usize(index))
                        .first()
                        .is_some_and(Ownership::is_owning)
                })
                .collect::<IndexVec<Local, _>>()
        } else {
            (0..mutable_pointers.len())
                .map(|_| false)
                .collect::<IndexVec<Local, _>>()
        };
        let mut _output_params = DenseBitSet::new_empty(mutable_pointers.len());
        if let Some(output_params) = analysis.output_params.get(&did) {
            for local in output_params.iter() {
                _output_params.insert(local);
            }
        }
        let fn_offset_signs = analysis.offset_sign_result.access_signs.get(&did);
        let mut needs_cursor = DenseBitSet::new_empty(mutable_pointers.len());
        if let Some(signs) = fn_offset_signs {
            needs_cursor.union(signs);
        }
        let non_null_locals = analysis
            .nullity_result
            .non_null_locals
            .get(&did)
            .cloned()
            .unwrap_or_else(|| DenseBitSet::new_empty(mutable_pointers.len()));
        DecisionMaker {
            tcx,
            typing_env: ty::TypingEnv::post_analysis(tcx, did),
            array_pointers,
            mutable_pointers,
            _owning_pointers,
            _output_params,
            promoted_mut_refs,
            promoted_shared_refs,
            needs_cursor,
            non_null_locals,
        }
    }

    pub fn decide(
        &self,
        local: Local,
        decl: &LocalDecl<'tcx>,
        aliases: Option<&FxHashSet<Local>>,
    ) -> Option<PtrKind> {
        self.decide_with_info(local, decl, aliases).kind
    }

    pub fn decide_with_info(
        &self,
        local: Local,
        decl: &LocalDecl<'tcx>,
        aliases: Option<&FxHashSet<Local>>,
    ) -> DecisionInfo {
        let mut events = Vec::new();
        let Some((ty, m)) = super::transform::unwrap_ptr_from_mir_ty(decl.ty) else {
            return DecisionInfo { kind: None, events };
        };
        let is_local_struct = matches!(
            ty.kind(),
            ty::TyKind::Adt(adt_def, _) if adt_def.did().is_local() && adt_def.is_struct()
        );
        let (mut decision, reason) =
            if ty.is_c_void(self.tcx) || utils::file::contains_file_ty(ty, self.tcx) {
                (
                    Some(PtrKind::Raw(m.is_mut())),
                    DecisionReason::CVoidOrFilePointee,
                )
            } else if pointee_forces_raw(self.tcx, self.typing_env, ty) {
                (
                    Some(PtrKind::Raw(m.is_mut())),
                    DecisionReason::OpaqueOrUnsizedPointee,
                )
            } else if aliases.is_some_and(|aliases| {
                std::iter::once(local)
                    .chain(aliases.iter().copied())
                    .any(|l| self.mutable_pointers[l])
            }) {
                (
                    Some(PtrKind::Raw(self.mutable_pointers[local])),
                    DecisionReason::MutableAliasCluster,
                )
            } else if self._owning_pointers[local] && self.array_pointers[local] {
                if self._output_params.contains(local) {
                    if self.needs_cursor.contains(local) {
                        (
                            Some(PtrKind::SliceCursor(true)),
                            DecisionReason::OwningArrayOutputParam,
                        )
                    } else {
                        (
                            Some(PtrKind::Slice(true)),
                            DecisionReason::OwningArrayOutputParam,
                        )
                    }
                } else if is_local_struct {
                    (
                        Some(PtrKind::Raw(self.mutable_pointers[local])),
                        DecisionReason::OwningArrayLocalStruct,
                    )
                } else {
                    (
                        Some(PtrKind::OptBoxedSlice),
                        DecisionReason::OwningArrayBoxedSlice,
                    )
                }
            } else if self._owning_pointers[local] {
                if self._output_params.contains(local) {
                    (
                        Some(PtrKind::OptRef(true)),
                        DecisionReason::OwningScalarOutputParam,
                    )
                } else if matches!(ty.kind(), ty::TyKind::RawPtr(..) | ty::TyKind::Ref(..)) {
                    (
                        Some(PtrKind::Raw(self.mutable_pointers[local])),
                        DecisionReason::OwningScalarNestedPointer,
                    )
                } else {
                    (Some(PtrKind::OptBox), DecisionReason::OwningScalarBox)
                }
            } else if self.array_pointers[local] {
                if self.promoted_shared_refs.contains(local) {
                    if self.needs_cursor.contains(local) {
                        (
                            Some(PtrKind::SliceCursor(false)),
                            DecisionReason::ArrayBorrowPromotedShared,
                        )
                    } else {
                        (
                            Some(PtrKind::Slice(false)),
                            DecisionReason::ArrayBorrowPromotedShared,
                        )
                    }
                } else if self.promoted_mut_refs.contains(local) {
                    if self.needs_cursor.contains(local) {
                        (
                            Some(PtrKind::SliceCursor(true)),
                            DecisionReason::ArrayBorrowPromotedMut,
                        )
                    } else {
                        (
                            Some(PtrKind::Slice(true)),
                            DecisionReason::ArrayBorrowPromotedMut,
                        )
                    }
                } else {
                    (
                        Some(PtrKind::Raw(self.mutable_pointers[local])),
                        DecisionReason::RawPtrNotBorrowPromoted,
                    )
                }
            } else if self.promoted_shared_refs.contains(local) {
                (
                    Some(PtrKind::OptRef(false)),
                    DecisionReason::BorrowPromotedShared,
                )
            } else if self.promoted_mut_refs.contains(local) {
                (
                    Some(PtrKind::OptRef(true)),
                    DecisionReason::BorrowPromotedMut,
                )
            } else if decl.ty.is_raw_ptr() {
                (
                    Some(PtrKind::Raw(self.mutable_pointers[local])),
                    DecisionReason::RawPtrNotBorrowPromoted,
                )
            } else {
                (None, DecisionReason::RawPtrNotBorrowPromoted)
            };
        if decision.is_some() {
            events.push(DecisionInfoEvent {
                before: None,
                after: decision,
                reason,
                detail: None,
            });
            if matches!(decision, Some(PtrKind::SliceCursor(_))) {
                events.push(DecisionInfoEvent {
                    before: decision.map(|kind| match kind {
                        PtrKind::SliceCursor(m) => PtrKind::Slice(m),
                        other => other,
                    }),
                    after: decision,
                    reason: DecisionReason::ArrayNeedsCursor,
                    detail: None,
                });
            }
        }

        let const_preserved = self.preserve_original_pointer_constness(decision, m.is_mut());
        if const_preserved != decision {
            events.push(DecisionInfoEvent {
                before: decision,
                after: const_preserved,
                reason: DecisionReason::PreserveOriginalConstness,
                detail: None,
            });
        }
        decision = const_preserved;
        if self.non_null_locals.contains(local) {
            let non_null = decision.map(PtrKind::non_null_variant);
            if non_null != decision {
                events.push(DecisionInfoEvent {
                    before: decision,
                    after: non_null,
                    reason: DecisionReason::ProvenNonNull,
                    detail: None,
                });
            }
            decision = non_null;
        }
        DecisionInfo {
            kind: decision,
            events,
        }
    }
}

pub(crate) fn pointee_forces_raw<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    pointee: ty::Ty<'tcx>,
) -> bool {
    matches!(pointee.kind(), ty::TyKind::Foreign(_)) || !pointee.is_sized(tcx, typing_env)
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct SigDecision {
    /// None means no change
    pub input_decs: Vec<Option<PtrKind>>,
    pub input_lifetimes: Vec<Option<Symbol>>,
    pub output_dec: Option<PtrKind>,
    pub output_lifetime: Option<Symbol>,
    pub signature_locked: bool,
}

impl SigDecision {
    pub(crate) fn set_input_dec(&mut self, idx: usize, decision: Option<PtrKind>) {
        self.input_decs[idx] = decision;
        if !decision_carries_lifetime(decision)
            && let Some(lifetime) = self.input_lifetimes.get_mut(idx)
        {
            *lifetime = None;
        }
    }

    pub(crate) fn set_output_dec(&mut self, decision: Option<PtrKind>) {
        self.output_dec = decision;
        if !decision_carries_lifetime(decision) {
            self.output_lifetime = None;
        }
    }

    fn normalize_lifetimes(&mut self) {
        for idx in 0..self.input_decs.len() {
            if !decision_carries_lifetime(self.input_decs[idx])
                && let Some(lifetime) = self.input_lifetimes.get_mut(idx)
            {
                *lifetime = None;
            }
        }
        if !decision_carries_lifetime(self.output_dec) {
            self.output_lifetime = None;
        }
    }
}

fn decision_carries_lifetime(decision: Option<PtrKind>) -> bool {
    matches!(decision, Some(PtrKind::Ref(_) | PtrKind::OptRef(_)))
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct SigDecisions {
    pub data: FxHashMap<LocalDefId, SigDecision>,
}

impl SigDecisions {
    #[allow(dead_code)]
    pub fn new(
        rust_program: &RustProgram,
        analysis: &Analysis,
        lifetime_plans: &super::lifetimes::LifetimePlans,
        fn_ptr_groups: &crate::analyses::fn_ptr_groups::FnPtrGroups,
    ) -> Self {
        Self::new_with_diagnostics(rust_program, analysis, lifetime_plans, fn_ptr_groups, None)
    }

    pub fn new_with_diagnostics(
        rust_program: &RustProgram,
        analysis: &Analysis,
        lifetime_plans: &super::lifetimes::LifetimePlans,
        fn_ptr_groups: &crate::analyses::fn_ptr_groups::FnPtrGroups,
        mut diagnostics: Option<&mut DecisionDiagnostics>,
    ) -> Self {
        let mut data = FxHashMap::default();
        data.reserve(rust_program.functions.len());

        let fn_ptrs = collect_fn_ptrs(rust_program);

        for did in rust_program.functions.iter() {
            let input_len = rust_program
                .tcx
                .fn_sig(*did)
                .skip_binder()
                .inputs()
                .skip_binder()
                .len();
            if fn_ptrs.contains(did) {
                let input_decs = fn_ptr_groups
                    .fn_to_group
                    .get(did)
                    .and_then(|rep| fn_ptr_groups.group_decisions.get(rep).cloned())
                    .unwrap_or_else(|| vec![None; input_len]);
                if let Some(diagnostics) = diagnostics.as_deref_mut() {
                    record_param_decisions(
                        diagnostics,
                        rust_program.tcx,
                        *did,
                        &input_decs,
                        DecisionStage::Signature,
                        DecisionReason::FnPtrGroupDecision,
                    );
                }
                // don't rewrite output for fn-ptr group members: the fn-ptr type
                // annotations (casts, parameter types) don't yet track output types,
                // and the existing internal local-variable transformation handles
                // the return conversion back to raw.
                data.insert(
                    *did,
                    SigDecision {
                        input_decs,
                        input_lifetimes: vec![None; input_len],
                        output_dec: None,
                        output_lifetime: None,
                        signature_locked: false,
                    },
                );
                continue;
            }
            let decision_maker = DecisionMaker::new(analysis, *did, rust_program.tcx);

            let body = &*rust_program
                .tcx
                .mir_drops_elaborated_and_const_checked(did)
                .borrow();

            let sig = rust_program.tcx.fn_sig(*did).skip_binder();
            debug_assert_eq!(input_len, sig.inputs().skip_binder().len());
            let lifetime_plan = lifetime_plans
                .functions
                .get(did)
                .cloned()
                .unwrap_or_default();
            let output_lifetime = lifetime_plan.output_lifetime;
            let input_lifetimes = if lifetime_plan.input_lifetimes.len() == input_len {
                lifetime_plan.input_lifetimes.clone()
            } else {
                vec![None; input_len]
            };

            let aliases = analysis.aliases.get(did);

            let mut input_decs = Vec::new();
            for (idx, (param, param_decl)) in body
                .local_decls
                .iter_enumerated()
                .skip(1)
                .take(input_len)
                .enumerate()
            {
                let aliases = aliases.and_then(|aliases| aliases.get(&param));
                let info = decision_maker.decide_with_info(param, param_decl, aliases);
                if let Some(diagnostics) = diagnostics.as_deref_mut()
                    && let Some(hir_id) = param_hir_id(rust_program.tcx, *did, idx)
                {
                    let subject = DecisionSubject::Param {
                        did: *did,
                        index: idx,
                        hir_id,
                        local: param,
                    };
                    record_decision_info(diagnostics, subject, DecisionStage::Initial, &info);
                }
                input_decs.push(info.kind);
            }

            let return_local = Local::from_u32(0);
            let return_decl = &body.local_decls[return_local];
            let return_aliases = aliases.and_then(|a| a.get(&return_local));
            let return_info =
                decision_maker.decide_with_info(return_local, return_decl, return_aliases);
            if let Some(diagnostics) = diagnostics.as_deref_mut() {
                let subject = DecisionSubject::Return { did: *did };
                record_decision_info(diagnostics, subject, DecisionStage::Initial, &return_info);
            }
            let direct_output_dec = match return_info.kind {
                Some(kind @ (PtrKind::Ref(_) | PtrKind::OptRef(_)))
                    if output_lifetime.is_some() =>
                {
                    Some(kind)
                }
                other => get_direct_output_dec(other),
            };
            if let Some(diagnostics) = diagnostics.as_deref_mut()
                && let Some(direct_output_dec) = direct_output_dec
            {
                diagnostics.record(
                    DecisionSubject::Return { did: *did },
                    DecisionStage::ReturnInference,
                    return_info.kind,
                    Some(direct_output_dec),
                    DecisionReason::ReturnDirectCandidate,
                    None,
                );
            }
            let returned_local_output_dec = infer_returned_local_box_kind_with_local(
                body,
                &decision_maker,
                aliases,
                return_local,
            );
            if let Some(diagnostics) = diagnostics.as_deref_mut()
                && let Some((local, kind)) = returned_local_output_dec
            {
                diagnostics.record(
                    DecisionSubject::Return { did: *did },
                    DecisionStage::ReturnInference,
                    direct_output_dec,
                    Some(kind),
                    DecisionReason::ReturnFromLocalBoxCandidate,
                    Some(format!("local={local:?}")),
                );
            }
            let returned_local_output_dec = returned_local_output_dec.map(|(_, kind)| kind);
            let output_dec = get_output_dec(direct_output_dec, returned_local_output_dec);
            if let Some(diagnostics) = diagnostics.as_deref_mut()
                && output_dec.is_some()
            {
                diagnostics.record(
                    DecisionSubject::Return { did: *did },
                    DecisionStage::ReturnInference,
                    direct_output_dec,
                    output_dec,
                    DecisionReason::ReturnDecisionMerge,
                    None,
                );
            }

            data.insert(*did, {
                let mut sig_dec = SigDecision {
                    input_decs,
                    input_lifetimes,
                    output_dec,
                    output_lifetime,
                    signature_locked: false,
                };
                apply_return_borrow_lifetime_plan(
                    *did,
                    body,
                    &lifetime_plan,
                    &decision_maker,
                    &mut sig_dec,
                    diagnostics.as_deref_mut(),
                );
                sig_dec.normalize_lifetimes();
                sig_dec
            });
        }
        SigDecisions { data }
    }
}

fn apply_return_borrow_lifetime_plan<'tcx>(
    did: LocalDefId,
    body: &rustc_middle::mir::Body<'tcx>,
    lifetime_plan: &super::lifetimes::FnLifetimePlan,
    decision_maker: &DecisionMaker<'tcx>,
    sig_dec: &mut SigDecision,
    mut diagnostics: Option<&mut DecisionDiagnostics>,
) {
    let Some(output_lifetime) = lifetime_plan.output_lifetime else {
        return;
    };
    let return_local = Local::from_u32(0);
    let Some((_, output_mutability)) =
        super::transform::unwrap_ptr_from_mir_ty(body.local_decls[return_local].ty)
    else {
        return;
    };

    let mut returned_inputs = Vec::new();
    for (idx, lifetime) in lifetime_plan.input_lifetimes.iter().enumerate() {
        if *lifetime != Some(output_lifetime) {
            continue;
        }
        if !matches!(
            sig_dec.input_decs.get(idx).copied().flatten(),
            Some(PtrKind::Ref(_) | PtrKind::OptRef(_))
        ) {
            return;
        }
        let local = Local::from_usize(idx + 1);
        let Some((_, input_mutability)) =
            super::transform::unwrap_ptr_from_mir_ty(body.local_decls[local].ty)
        else {
            return;
        };
        returned_inputs.push((idx, input_mutability.is_mut()));
    }
    if returned_inputs.is_empty() {
        return;
    }

    let return_nullable =
        return_place_may_receive_null_constructor(body, decision_maker.tcx, return_local);
    let return_kind = if return_nullable {
        PtrKind::OptRef(output_mutability.is_mut())
    } else {
        PtrKind::Ref(output_mutability.is_mut())
    };
    if return_nullable && let Some(diagnostics) = diagnostics.as_deref_mut() {
        diagnostics.record(
            DecisionSubject::Return { did },
            DecisionStage::LifetimePlan,
            sig_dec.output_dec,
            Some(return_kind),
            DecisionReason::ReturnNullable,
            None,
        );
    }
    for (idx, is_mut) in returned_inputs {
        let input_kind = if return_kind.is_optional()
            || returned_input_is_observed_nullable(decision_maker.tcx, did, idx)
        {
            PtrKind::OptRef
        } else {
            PtrKind::Ref
        };
        let before = sig_dec.input_decs.get(idx).copied().flatten();
        let after = Some(input_kind(is_mut));
        sig_dec.set_input_dec(idx, Some(input_kind(is_mut)));
        sig_dec.input_lifetimes[idx] = Some(output_lifetime);
        if let Some(diagnostics) = diagnostics.as_deref_mut()
            && before != after
            && let Some(hir_id) = param_hir_id(decision_maker.tcx, did, idx)
        {
            diagnostics.record(
                DecisionSubject::Param {
                    did,
                    index: idx,
                    hir_id,
                    local: Local::from_usize(idx + 1),
                },
                DecisionStage::LifetimePlan,
                before,
                after,
                DecisionReason::ReturnBorrowLifetimePlan,
                Some(format!("lifetime={output_lifetime}")),
            );
        }
    }
    let before = sig_dec.output_dec;
    sig_dec.set_output_dec(Some(return_kind));
    sig_dec.output_lifetime = Some(output_lifetime);
    if before != Some(return_kind)
        && let Some(diagnostics) = diagnostics
    {
        diagnostics.record(
            DecisionSubject::Return { did },
            DecisionStage::LifetimePlan,
            before,
            Some(return_kind),
            DecisionReason::ReturnBorrowLifetimePlan,
            Some(format!("lifetime={output_lifetime}")),
        );
    }
}

fn record_decision_info(
    diagnostics: &mut DecisionDiagnostics,
    subject: DecisionSubject,
    stage: DecisionStage,
    info: &DecisionInfo,
) {
    for event in &info.events {
        diagnostics.record(
            subject,
            stage,
            event.before,
            event.after,
            event.reason,
            event.detail.clone(),
        );
    }
}

fn record_param_decisions(
    diagnostics: &mut DecisionDiagnostics,
    tcx: TyCtxt<'_>,
    did: LocalDefId,
    input_decs: &[Option<PtrKind>],
    stage: DecisionStage,
    reason: DecisionReason,
) {
    for (index, decision) in input_decs.iter().copied().enumerate() {
        let Some(decision) = decision else {
            continue;
        };
        let Some(hir_id) = param_hir_id(tcx, did, index) else {
            continue;
        };
        diagnostics.record(
            DecisionSubject::Param {
                did,
                index,
                hir_id,
                local: Local::from_usize(index + 1),
            },
            stage,
            None,
            Some(decision),
            reason,
            None,
        );
    }
}

fn param_hir_id(tcx: TyCtxt<'_>, did: LocalDefId, index: usize) -> Option<HirId> {
    let hir::Node::Item(item) = tcx.hir_node_by_def_id(did) else {
        return None;
    };
    let hir::ItemKind::Fn { body, .. } = item.kind else {
        return None;
    };
    let body = tcx.hir_body(body);
    let param = body.params.get(index)?;
    let hir::PatKind::Binding(_, hir_id, _, _) = param.pat.kind else {
        return None;
    };
    Some(hir_id)
}

fn returned_input_is_observed_nullable(tcx: TyCtxt<'_>, did: LocalDefId, idx: usize) -> bool {
    fn hir_unwrapped_local_id(expr: &hir::Expr<'_>) -> Option<HirId> {
        let expr = match expr.kind {
            hir::ExprKind::Cast(inner, _) | hir::ExprKind::DropTemps(inner) => inner,
            _ => expr,
        };
        let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = expr.kind else {
            return None;
        };
        let Res::Local(hir_id) = path.res else {
            return None;
        };
        Some(hir_id)
    }

    struct NullableUseVisitor {
        param: HirId,
        found: bool,
    }

    impl<'tcx> Visitor<'tcx> for NullableUseVisitor {
        fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
            if self.found {
                return;
            }
            if let hir::ExprKind::MethodCall(seg, receiver, _, _) = expr.kind
                && seg.ident.name.as_str() == "is_null"
                && hir_unwrapped_local_id(receiver) == Some(self.param)
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
    let body = tcx.hir_body(body);
    let Some(param) = body.params.get(idx) else {
        return false;
    };
    let hir::PatKind::Binding(_, param_hir_id, _, _) = param.pat.kind else {
        return false;
    };
    let mut visitor = NullableUseVisitor {
        param: param_hir_id,
        found: false,
    };
    visitor.visit_body(body);
    visitor.found
}

fn return_place_may_receive_null_constructor<'tcx>(
    body: &rustc_middle::mir::Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    return_local: Local,
) -> bool {
    fn is_null_like_call<'tcx>(tcx: TyCtxt<'tcx>, func: &Operand<'tcx>) -> bool {
        let Some(func_const) = func.constant() else {
            return false;
        };
        let ty::TyKind::FnDef(def_id, _) = func_const.ty().kind() else {
            return false;
        };
        matches!(tcx.item_name(*def_id).as_str(), "null" | "null_mut")
    }

    fn const_is_zero(value: &rustc_middle::mir::Const<'_>, tcx: TyCtxt<'_>) -> bool {
        if let Some(scalar) = value.try_to_scalar()
            && let Ok(int) = scalar.try_to_scalar_int()
        {
            return int.to_bits(int.size()) == 0;
        }
        if let rustc_middle::mir::Const::Unevaluated(unevaluated, _) = value
            && unevaluated.promoted.is_none()
            && let Ok(rustc_middle::mir::ConstValue::Scalar(scalar)) =
                tcx.const_eval_poly(unevaluated.def)
            && let Ok(int) = scalar.try_to_scalar_int()
        {
            return int.to_bits(int.size()) == 0;
        }
        false
    }

    fn operand_is_zero(operand: &Operand<'_>, tcx: TyCtxt<'_>) -> bool {
        let Operand::Constant(constant) = operand else {
            return false;
        };
        const_is_zero(&constant.const_, tcx)
    }

    let mut nullable = DenseBitSet::new_empty(body.local_decls.len());
    loop {
        let mut changed = false;
        for bb in body.basic_blocks.iter() {
            for stmt in &bb.statements {
                let StatementKind::Assign(box (place, rvalue)) = &stmt.kind else {
                    continue;
                };
                let Some(destination) = place.as_local() else {
                    continue;
                };
                let source_nullable = match rvalue {
                    Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) => src
                        .as_local()
                        .is_some_and(|source| nullable.contains(source)),
                    Rvalue::Use(operand) if body.local_decls[destination].ty.is_raw_ptr() => {
                        operand_is_zero(operand, tcx)
                    }
                    Rvalue::Cast(_, operand, ty) if ty.is_raw_ptr() => {
                        operand_is_zero(operand, tcx)
                    }
                    _ => false,
                };
                if source_nullable {
                    changed |= nullable.insert(destination);
                }
            }

            let Some(terminator) = &bb.terminator else {
                continue;
            };
            let TerminatorKind::Call {
                func, destination, ..
            } = &terminator.kind
            else {
                continue;
            };
            if is_null_like_call(tcx, func)
                && let Some(destination) = destination.as_local()
            {
                changed |= nullable.insert(destination);
            }
        }

        if !changed {
            break;
        }
    }

    nullable.contains(return_local)
}

fn infer_returned_local_box_kind_with_local<'tcx>(
    body: &rustc_middle::mir::Body<'tcx>,
    decision_maker: &DecisionMaker<'tcx>,
    aliases: Option<&FxHashMap<Local, FxHashSet<Local>>>,
    return_local: Local,
) -> Option<(Local, PtrKind)> {
    fn is_null_like_return_call<'tcx>(tcx: TyCtxt<'tcx>, func: &Operand<'tcx>) -> bool {
        let Some(func_const) = func.constant() else {
            return false;
        };
        let ty::TyKind::FnDef(def_id, _) = func_const.ty().kind() else {
            return false;
        };
        matches!(tcx.item_name(*def_id).as_str(), "null" | "null_mut")
    }

    let mut candidate = None;
    for bb in body.basic_blocks.iter() {
        for stmt in &bb.statements {
            let StatementKind::Assign(box (place, rvalue)) = &stmt.kind else {
                continue;
            };
            if place.as_local() != Some(return_local) {
                continue;
            }
            let Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) = rvalue else {
                return None;
            };
            let src_local = src.as_local()?;
            match candidate {
                Some(prev) if prev != src_local => return None,
                None => candidate = Some(src_local),
                _ => {}
            }
        }
        let Some(terminator) = &bb.terminator else {
            continue;
        };
        let TerminatorKind::Call {
            func, destination, ..
        } = &terminator.kind
        else {
            continue;
        };
        if destination.as_local() != Some(return_local) {
            continue;
        }
        if is_null_like_return_call(decision_maker.tcx, func) {
            continue;
        }
        return None;
    }

    let local = candidate?;
    let decl = &body.local_decls[local];
    let aliases = aliases.and_then(|aliases| aliases.get(&local));
    let return_non_null = decision_maker.non_null_locals.contains(return_local);
    match decision_maker.decide(local, decl, aliases) {
        Some(kind @ (PtrKind::OptBox | PtrKind::OptBoxedSlice)) => Some((local, kind)),
        Some(kind @ (PtrKind::Box | PtrKind::BoxedSlice)) if return_non_null => Some((local, kind)),
        Some(kind @ (PtrKind::Box | PtrKind::BoxedSlice)) => Some((local, kind.optional_variant())),
        _ => None,
    }
}

pub fn get_direct_output_dec(decision: Option<PtrKind>) -> Option<PtrKind> {
    match decision {
        Some(
            kind @ (PtrKind::Raw(_)
            | PtrKind::OptBox
            | PtrKind::OptBoxedSlice
            | PtrKind::Box
            | PtrKind::BoxedSlice),
        ) => Some(kind),
        _ => None,
    }
}

pub fn get_output_dec(
    direct_output_dec: Option<PtrKind>,
    returned_local_output_dec: Option<PtrKind>,
) -> Option<PtrKind> {
    match (direct_output_dec, returned_local_output_dec) {
        (
            Some(PtrKind::Raw(_)),
            Some(
                kind @ (PtrKind::OptBox
                | PtrKind::OptBoxedSlice
                | PtrKind::Box
                | PtrKind::BoxedSlice),
            ),
        ) => Some(kind),
        (Some(PtrKind::Raw(m)), _) => Some(PtrKind::Raw(m)),
        (
            Some(PtrKind::OptBox | PtrKind::Box),
            Some(kind @ (PtrKind::OptBoxedSlice | PtrKind::BoxedSlice)),
        ) => Some(kind),
        (Some(kind), None) | (None, Some(kind)) => Some(kind),
        (Some(kind), Some(_)) => Some(kind),
        (None, None) => None,
    }
}

#[cfg(test)]
mod tests {
    use rustc_hir::{ItemKind, OwnerNode};
    use rustc_index::{IndexVec, bit_set::DenseBitSet};
    use rustc_middle::{mir::Body, ty::TyCtxt};

    use super::*;

    fn with_test_fn_body<F>(code: &str, f: F)
    where F: for<'tcx> FnOnce(TyCtxt<'tcx>, LocalDefId, &Body<'tcx>) + Send {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let did = tcx
                .hir_crate(())
                .owners
                .iter()
                .filter_map(|maybe_owner| {
                    let owner = maybe_owner.as_owner()?;
                    let OwnerNode::Item(item) = owner.node() else {
                        return None;
                    };
                    match item.kind {
                        ItemKind::Fn { .. } => Some(item.owner_id.def_id),
                        _ => None,
                    }
                })
                .next()
                .expect("expected test function");
            let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
            f(tcx, did, &body);
        })
        .unwrap();
    }

    #[allow(clippy::too_many_arguments)]
    fn synthetic_decision_maker_with_non_null<'tcx>(
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        local: Local,
        mutable: bool,
        is_array: bool,
        owning: bool,
        output: bool,
        promoted_mut: bool,
        promoted_shared: bool,
        needs_cursor: bool,
        non_null: bool,
    ) -> DecisionMaker<'tcx> {
        let len = body.local_decls.len();
        let mut mutable_pointers = IndexVec::from_elem_n(false, len);
        mutable_pointers[local] = mutable;
        let mut array_pointers = IndexVec::from_elem_n(false, len);
        array_pointers[local] = is_array;
        let mut owning_pointers = IndexVec::from_elem_n(false, len);
        owning_pointers[local] = owning;
        let mut output_params = DenseBitSet::new_empty(len);
        if output {
            output_params.insert(local);
        }
        let mut promoted_mut_refs = DenseBitSet::new_empty(len);
        if promoted_mut {
            promoted_mut_refs.insert(local);
        }
        let mut promoted_shared_refs = DenseBitSet::new_empty(len);
        if promoted_shared {
            promoted_shared_refs.insert(local);
        }
        let mut needs_cursor_set = DenseBitSet::new_empty(len);
        if needs_cursor {
            needs_cursor_set.insert(local);
        }
        let mut non_null_locals = DenseBitSet::new_empty(len);
        if non_null {
            non_null_locals.insert(local);
        }

        DecisionMaker {
            tcx,
            typing_env: ty::TypingEnv::fully_monomorphized(),
            mutable_pointers,
            array_pointers,
            _owning_pointers: owning_pointers,
            _output_params: output_params,
            promoted_mut_refs,
            promoted_shared_refs,
            needs_cursor: needs_cursor_set,
            non_null_locals,
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn decide_for_param_with_ty(
        pointer_ty: &str,
        owning: bool,
        output: bool,
        is_array: bool,
        needs_cursor: bool,
        promoted_mut: bool,
        promoted_shared: bool,
        mutable: bool,
    ) -> PtrKind {
        decide_for_param_with_ty_and_non_null(
            pointer_ty,
            owning,
            output,
            is_array,
            needs_cursor,
            promoted_mut,
            promoted_shared,
            mutable,
            false,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn decide_for_param_with_ty_and_non_null(
        pointer_ty: &str,
        owning: bool,
        output: bool,
        is_array: bool,
        needs_cursor: bool,
        promoted_mut: bool,
        promoted_shared: bool,
        mutable: bool,
        non_null: bool,
    ) -> PtrKind {
        let mut decision = None;
        let code = format!(
            r#"
pub unsafe fn foo(p: {pointer_ty}) {{
    let _ = p;
}}
"#
        );
        with_test_fn_body(&code, |tcx, _did, body| {
            let local = Local::from_u32(1);
            let decision_maker = synthetic_decision_maker_with_non_null(
                tcx,
                body,
                local,
                mutable,
                is_array,
                owning,
                output,
                promoted_mut,
                promoted_shared,
                needs_cursor,
                non_null,
            );
            let decl = &body.local_decls[local];
            decision = Some(
                decision_maker
                    .decide(local, decl, None)
                    .expect("expected pointer decision"),
            );
        });
        decision.expect("decision should be set")
    }

    fn decide_for_param(
        owning: bool,
        output: bool,
        is_array: bool,
        needs_cursor: bool,
        promoted_mut: bool,
        promoted_shared: bool,
        mutable: bool,
    ) -> PtrKind {
        decide_for_param_with_ty(
            "*mut i32",
            owning,
            output,
            is_array,
            needs_cursor,
            promoted_mut,
            promoted_shared,
            mutable,
        )
    }

    #[test]
    fn owning_scalar_output_becomes_mut_opt_ref() {
        assert_eq!(
            decide_for_param(true, true, false, false, false, false, true),
            PtrKind::OptRef(true)
        );
    }

    #[test]
    fn owning_pointer_to_pointer_output_becomes_mut_opt_ref() {
        assert_eq!(
            decide_for_param_with_ty(
                "*mut *const i32",
                true,
                true,
                false,
                false,
                true,
                false,
                true
            ),
            PtrKind::OptRef(true)
        );
    }

    #[test]
    fn owning_scalar_non_output_becomes_opt_box() {
        assert_eq!(
            decide_for_param(true, false, false, false, false, false, true),
            PtrKind::OptBox
        );
    }

    #[test]
    fn owning_array_output_with_cursor_need_becomes_mut_cursor() {
        assert_eq!(
            decide_for_param(true, true, true, true, false, false, true),
            PtrKind::SliceCursor(true)
        );
    }

    #[test]
    fn owning_array_non_output_with_cursor_need_becomes_opt_boxed_slice() {
        assert_eq!(
            decide_for_param(true, false, true, true, false, false, true),
            PtrKind::OptBoxedSlice
        );
    }

    #[test]
    fn owning_array_output_without_cursor_need_becomes_mut_slice() {
        assert_eq!(
            decide_for_param(true, true, true, false, false, false, true),
            PtrKind::Slice(true)
        );
    }

    #[test]
    fn owning_array_non_output_without_cursor_need_becomes_opt_boxed_slice() {
        assert_eq!(
            decide_for_param(true, false, true, false, false, false, true),
            PtrKind::OptBoxedSlice
        );
    }

    #[test]
    fn non_owning_scalar_regression_stays_opt_ref() {
        assert_eq!(
            decide_for_param(false, false, false, false, true, false, true),
            PtrKind::OptRef(true)
        );
    }

    #[test]
    fn non_owning_array_with_cursor_need_stays_slice_cursor() {
        assert_eq!(
            decide_for_param(false, false, true, true, true, false, true),
            PtrKind::SliceCursor(true)
        );
    }

    #[test]
    fn const_scalar_pointer_does_not_become_mut_opt_ref() {
        assert_eq!(
            decide_for_param_with_ty("*const i32", false, false, false, false, true, false, true),
            PtrKind::OptRef(false)
        );
    }

    #[test]
    fn non_null_promoted_scalar_param_becomes_ref() {
        assert_eq!(
            decide_for_param_with_ty_and_non_null(
                "*mut i32", false, false, false, false, true, false, true, true,
            ),
            PtrKind::Ref(true)
        );
        assert_eq!(
            decide_for_param_with_ty_and_non_null(
                "*const i32",
                false,
                false,
                false,
                false,
                true,
                false,
                true,
                true,
            ),
            PtrKind::Ref(false)
        );
    }

    #[test]
    fn non_null_owning_params_become_non_optional() {
        assert_eq!(
            decide_for_param_with_ty_and_non_null(
                "*mut i32", true, false, false, false, false, false, true, true,
            ),
            PtrKind::Box
        );
        assert_eq!(
            decide_for_param_with_ty_and_non_null(
                "*mut i32", true, false, true, false, false, false, true, true,
            ),
            PtrKind::BoxedSlice
        );
    }

    #[test]
    fn const_array_pointer_does_not_become_mut_slice() {
        assert_eq!(
            decide_for_param_with_ty("*const i32", false, false, true, false, true, false, true),
            PtrKind::Slice(false)
        );
    }

    #[test]
    fn alias_overlap_takes_precedence_over_owning_output_promotion() {
        let mut decision = None;
        let mut reasons = Vec::new();
        let code = r#"
pub unsafe fn foo(p: *mut i32, q: *mut i32) {
    let _ = (p, q);
}
"#;
        with_test_fn_body(code, |tcx, _did, body| {
            let local = Local::from_u32(1);
            let decision_maker = synthetic_decision_maker_with_non_null(
                tcx, body, local, true, true, true, true, false, false, false, true,
            );
            let decl = &body.local_decls[local];
            let aliases = FxHashSet::from_iter([Local::from_u32(2)]);
            let info = decision_maker.decide_with_info(local, decl, Some(&aliases));
            reasons = info.events.iter().map(|event| event.reason).collect();
            decision = Some(info.kind.expect("expected pointer decision"));
        });
        assert_eq!(decision, Some(PtrKind::Raw(true)));
        assert!(reasons.contains(&DecisionReason::MutableAliasCluster));
    }

    #[test]
    fn decide_with_info_records_constness_adjustment() {
        let mut events = Vec::new();
        let code = r#"
pub unsafe fn foo(p: *const i32) {
    let _ = p;
}
"#;
        with_test_fn_body(code, |tcx, _did, body| {
            let local = Local::from_u32(1);
            let decision_maker = synthetic_decision_maker_with_non_null(
                tcx, body, local, true, false, false, false, true, false, false, false,
            );
            let decl = &body.local_decls[local];
            events = decision_maker.decide_with_info(local, decl, None).events;
        });
        assert_eq!(
            events.iter().map(|event| event.reason).collect::<Vec<_>>(),
            vec![
                DecisionReason::BorrowPromotedMut,
                DecisionReason::PreserveOriginalConstness,
            ],
        );
    }

    #[test]
    fn sig_decision_clears_input_lifetime_when_downgraded_to_raw() {
        let lifetime = Symbol::new(1);
        let mut sig_dec = SigDecision {
            input_decs: vec![Some(PtrKind::OptRef(true))],
            input_lifetimes: vec![Some(lifetime)],
            output_dec: Some(PtrKind::OptRef(true)),
            output_lifetime: Some(lifetime),
            signature_locked: false,
        };

        sig_dec.set_input_dec(0, Some(PtrKind::Raw(true)));

        assert_eq!(sig_dec.input_lifetimes, vec![None]);
        assert_eq!(sig_dec.output_lifetime, Some(lifetime));
    }

    #[test]
    fn sig_decision_clears_output_lifetime_when_downgraded_to_raw() {
        let lifetime = Symbol::new(1);
        let mut sig_dec = SigDecision {
            input_decs: vec![Some(PtrKind::OptRef(true))],
            input_lifetimes: vec![Some(lifetime)],
            output_dec: Some(PtrKind::OptRef(true)),
            output_lifetime: Some(lifetime),
            signature_locked: false,
        };

        sig_dec.set_output_dec(Some(PtrKind::Raw(true)));

        assert_eq!(sig_dec.input_lifetimes, vec![Some(lifetime)]);
        assert_eq!(sig_dec.output_lifetime, None);
    }
}
