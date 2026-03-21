use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::{IndexVec, bit_set::DenseBitSet};
use rustc_middle::{
    mir::{Local, LocalDecl},
    ty::TyCtxt,
};
use rustc_span::def_id::LocalDefId;

use super::{Analysis, collector::collect_fn_ptrs};
use crate::utils::rustc::RustProgram;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PtrKind {
    /// reference: &mut T for Ref(true), or &T for Ref(false)
    OptRef(bool),
    /// raw pointer: *mut T for Raw(true), or *const T for Raw(false)
    Raw(bool),
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
        }
    }
}

pub struct DecisionMaker<'tcx> {
    tcx: TyCtxt<'tcx>,
    mutable_pointers: IndexVec<Local, bool>,
    array_pointers: IndexVec<Local, bool>,
    promoted_mut_refs: DenseBitSet<Local>,
    promoted_shared_refs: DenseBitSet<Local>,
    /// Locals that need a SliceCursor because they are offset with potentially-negative values.
    needs_cursor: DenseBitSet<Local>,
}

impl<'tcx> DecisionMaker<'tcx> {
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
        let fn_offset_signs = analysis.offset_sign_result.access_signs.get(&did);
        let mut needs_cursor = DenseBitSet::new_empty(mutable_pointers.len());
        if let Some(signs) = fn_offset_signs {
            needs_cursor.union(signs);
        }
        DecisionMaker {
            tcx,
            array_pointers,
            mutable_pointers,
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
        if ty.is_c_void(self.tcx) || utils::file::contains_file_ty(ty, self.tcx) {
            Some(PtrKind::Raw(m.is_mut()))
        } else if aliases.is_some_and(|aliases| {
            std::iter::once(local)
                .chain(aliases.iter().copied())
                .any(|l| self.mutable_pointers[l])
        }) {
            Some(PtrKind::Raw(self.mutable_pointers[local]))
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
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct SigDecision {
    /// None means no change
    pub input_decs: Vec<Option<PtrKind>>,
    pub output_dec: Option<PtrKind>,
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
            let output_dec = match decision_maker.decide(return_local, return_decl, return_aliases)
            {
                Some(PtrKind::Raw(m)) => Some(PtrKind::Raw(m)),
                _ => None, // no borrow inference for returns yet
            };

            data.insert(
                *did,
                SigDecision {
                    input_decs,
                    output_dec,
                },
            );
        }
        SigDecisions { data }
    }
}
