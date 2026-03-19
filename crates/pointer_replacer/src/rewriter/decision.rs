use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::{IndexVec, bit_set::DenseBitSet};
use rustc_middle::{
    mir::{Local, LocalDecl, Operand, Rvalue, StatementKind, TerminatorKind},
    ty::{self, TyCtxt},
};
use rustc_span::def_id::LocalDefId;

use super::{Analysis, collector::collect_fn_ptrs};
use crate::{analyses::ownership::Ownership, utils::rustc::RustProgram};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PtrKind {
    /// reference: &mut T for Ref(true), or &T for Ref(false)
    OptRef(bool),
    /// owning scalar pointer rewritten to Option<Box<T>>
    OptBox,
    /// raw pointer: *mut T for Raw(true), or *const T for Raw(false)
    Raw(bool),
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
            PtrKind::OptRef(m) | PtrKind::Raw(m) | PtrKind::Slice(m) | PtrKind::SliceCursor(m) => {
                *m
            }
            PtrKind::OptBox | PtrKind::OptBoxedSlice => true,
        }
    }
}

pub struct DecisionMaker<'tcx> {
    tcx: TyCtxt<'tcx>,
    mutable_pointers: IndexVec<Local, bool>,
    array_pointers: IndexVec<Local, bool>,
    _owning_pointers: IndexVec<Local, bool>,
    _output_params: DenseBitSet<Local>,
    promoted_mut_refs: DenseBitSet<Local>,
    promoted_shared_refs: DenseBitSet<Local>,
    /// Locals that need a SliceCursor because they are offset with potentially-negative values.
    needs_cursor: DenseBitSet<Local>,
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
            Some(PtrKind::OptRef(_)) => Some(PtrKind::OptRef(false)),
            Some(PtrKind::Raw(_)) => Some(PtrKind::Raw(false)),
            Some(PtrKind::Slice(_)) => Some(PtrKind::Slice(false)),
            Some(PtrKind::SliceCursor(_)) => Some(PtrKind::SliceCursor(false)),
            other => other,
        }
    }

    fn force_raw_local_struct_borrows(
        &self,
        decision: Option<PtrKind>,
        ty: ty::Ty<'tcx>,
        is_mut: bool,
    ) -> Option<PtrKind> {
        let is_local_struct = matches!(
            ty.kind(),
            ty::TyKind::Adt(adt_def, _) if adt_def.did().is_local() && adt_def.is_struct()
        );
        if is_local_struct
            && is_mut
            && matches!(
                decision,
                Some(PtrKind::OptRef(true) | PtrKind::Slice(true) | PtrKind::SliceCursor(true))
            )
        {
            Some(PtrKind::Raw(true))
        } else {
            decision
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
        DecisionMaker {
            tcx,
            array_pointers,
            mutable_pointers,
            _owning_pointers,
            _output_params,
            promoted_mut_refs,
            promoted_shared_refs,
            needs_cursor,
        }
    }

    pub fn decide(
        &self,
        local: Local,
        decl: &LocalDecl<'tcx>,
        aliases: Option<&FxHashSet<Local>>,
    ) -> Option<PtrKind> {
        let (ty, m) = super::transform::unwrap_ptr_from_mir_ty(decl.ty)?;
        let is_local_struct = matches!(
            ty.kind(),
            ty::TyKind::Adt(adt_def, _) if adt_def.did().is_local() && adt_def.is_struct()
        );
        let decision = if ty.is_c_void(self.tcx) || utils::file::contains_file_ty(ty, self.tcx) {
            Some(PtrKind::Raw(m.is_mut()))
        } else if aliases.is_some_and(|aliases| {
            std::iter::once(local)
                .chain(aliases.iter().copied())
                .any(|l| self.mutable_pointers[l])
        }) {
            Some(PtrKind::Raw(self.mutable_pointers[local]))
        } else if self._owning_pointers[local] && self.array_pointers[local] {
            if self.needs_cursor.contains(local) || is_local_struct {
                Some(PtrKind::Raw(self.mutable_pointers[local]))
            } else if self._output_params.contains(local) {
                Some(PtrKind::Slice(true))
            } else {
                Some(PtrKind::OptBoxedSlice)
            }
        } else if self._owning_pointers[local] {
            if matches!(ty.kind(), ty::TyKind::RawPtr(..) | ty::TyKind::Ref(..)) {
                Some(PtrKind::Raw(self.mutable_pointers[local]))
            } else if self._output_params.contains(local) {
                Some(PtrKind::OptRef(true))
            } else {
                Some(PtrKind::OptBox)
            }
        } else if is_local_struct && m.is_mut() {
            Some(PtrKind::Raw(true))
        } else if self.array_pointers[local] {
            if self.promoted_shared_refs.contains(local) {
                if self.needs_cursor.contains(local) {
                    Some(PtrKind::SliceCursor(false))
                } else {
                    Some(PtrKind::Slice(false))
                }
            } else if self.promoted_mut_refs.contains(local) {
                if self.needs_cursor.contains(local) {
                    Some(PtrKind::SliceCursor(true))
                } else {
                    Some(PtrKind::Slice(true))
                }
            } else {
                Some(PtrKind::Raw(self.mutable_pointers[local]))
            }
        } else if self.promoted_shared_refs.contains(local) {
            Some(PtrKind::OptRef(false))
        } else if self.promoted_mut_refs.contains(local) {
            Some(PtrKind::OptRef(true))
        } else if decl.ty.is_raw_ptr() {
            Some(PtrKind::Raw(self.mutable_pointers[local]))
        } else {
            None
        };

        let decision = self.preserve_original_pointer_constness(decision, m.is_mut());
        self.force_raw_local_struct_borrows(decision, ty, m.is_mut())
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct SigDecision {
    /// None means no change
    pub input_decs: Vec<Option<PtrKind>>,
    pub output_dec: Option<PtrKind>,
    pub signature_locked: bool,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct SigDecisions {
    pub data: FxHashMap<LocalDefId, SigDecision>,
}

impl SigDecisions {
    pub fn new(rust_program: &RustProgram, analysis: &Analysis) -> Self {
        let mut data = FxHashMap::default();
        data.reserve(rust_program.functions.len());

        // do not change function signatures that are used as function pointers
        let fn_ptrs = collect_fn_ptrs(rust_program);

        for did in rust_program.functions.iter() {
            if fn_ptrs.contains(did) {
                data.insert(
                    *did,
                    SigDecision {
                        input_decs: vec![
                            None;
                            rust_program
                                .tcx
                                .fn_sig(*did)
                                .skip_binder()
                                .inputs()
                                .skip_binder()
                                .len()
                        ],
                        output_dec: None,
                        signature_locked: true,
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
            let input_len = sig.inputs().skip_binder().len();

            let aliases = analysis.aliases.get(did);

            let input_decs = body
                .local_decls
                .iter_enumerated()
                .skip(1)
                .take(input_len)
                .map(|(param, param_decl)| {
                    let aliases = aliases.and_then(|aliases| aliases.get(&param));
                    decision_maker.decide(param, param_decl, aliases)
                })
                .collect();

            let return_local = Local::from_u32(0);
            let return_decl = &body.local_decls[return_local];
            let return_aliases = aliases.and_then(|a| a.get(&return_local));
            let direct_output_dec =
                match decision_maker.decide(return_local, return_decl, return_aliases) {
                    Some(kind @ (PtrKind::Raw(_) | PtrKind::OptBox | PtrKind::OptBoxedSlice)) => {
                        Some(kind)
                    }
                    _ => None,
                };
            let returned_local_output_dec =
                infer_returned_local_box_kind(body, &decision_maker, aliases, return_local);
            let output_dec = match (direct_output_dec, returned_local_output_dec) {
                (
                    Some(PtrKind::Raw(_)),
                    Some(kind @ (PtrKind::OptBox | PtrKind::OptBoxedSlice)),
                ) => Some(kind),
                (Some(PtrKind::Raw(m)), _) => Some(PtrKind::Raw(m)),
                (Some(PtrKind::OptBox), Some(PtrKind::OptBoxedSlice)) => {
                    Some(PtrKind::OptBoxedSlice)
                }
                (Some(kind), None) | (None, Some(kind)) => Some(kind),
                (Some(kind), Some(_)) => Some(kind),
                (None, None) => None,
            };

            data.insert(
                *did,
                SigDecision {
                    input_decs,
                    output_dec,
                    signature_locked: false,
                },
            );
        }
        SigDecisions { data }
    }
}

fn infer_returned_local_box_kind<'tcx>(
    body: &rustc_middle::mir::Body<'tcx>,
    decision_maker: &DecisionMaker<'tcx>,
    aliases: Option<&FxHashMap<Local, FxHashSet<Local>>>,
    return_local: Local,
) -> Option<PtrKind> {
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
            let Some(src_local) = src.as_local() else {
                return None;
            };
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
    match decision_maker.decide(local, decl, aliases) {
        Some(kind @ (PtrKind::OptBox | PtrKind::OptBoxedSlice)) => Some(kind),
        _ => None,
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

    fn synthetic_decision_maker<'tcx>(
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

        DecisionMaker {
            tcx,
            mutable_pointers,
            array_pointers,
            _owning_pointers: owning_pointers,
            _output_params: output_params,
            promoted_mut_refs,
            promoted_shared_refs,
            needs_cursor: needs_cursor_set,
        }
    }

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
            let decision_maker = synthetic_decision_maker(
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
    fn owning_scalar_non_output_becomes_opt_box() {
        assert_eq!(
            decide_for_param(true, false, false, false, false, false, true),
            PtrKind::OptBox
        );
    }

    #[test]
    fn owning_array_output_with_cursor_need_stays_raw() {
        assert_eq!(
            decide_for_param(true, true, true, true, false, false, true),
            PtrKind::Raw(true)
        );
    }

    #[test]
    fn owning_array_non_output_with_cursor_need_stays_raw() {
        assert_eq!(
            decide_for_param(true, false, true, true, false, false, true),
            PtrKind::Raw(true)
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
    fn const_array_pointer_does_not_become_mut_slice() {
        assert_eq!(
            decide_for_param_with_ty("*const i32", false, false, true, false, true, false, true),
            PtrKind::Slice(false)
        );
    }

    #[test]
    fn alias_overlap_takes_precedence_over_owning_output_promotion() {
        let mut decision = None;
        let code = r#"
pub unsafe fn foo(p: *mut i32, q: *mut i32) {
    let _ = (p, q);
}
"#;
        with_test_fn_body(code, |tcx, _did, body| {
            let local = Local::from_u32(1);
            let decision_maker = synthetic_decision_maker(
                tcx, body, local, true, true, true, true, false, false, false,
            );
            let decl = &body.local_decls[local];
            let aliases = FxHashSet::from_iter([Local::from_u32(2)]);
            decision = Some(
                decision_maker
                    .decide(local, decl, Some(&aliases))
                    .expect("expected pointer decision"),
            );
        });
        assert_eq!(decision, Some(PtrKind::Raw(true)));
    }
}
