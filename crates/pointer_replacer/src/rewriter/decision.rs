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
    /// slice: &mut [T] for Slice(true), or &[T] for Slice(false)
    Slice(bool),
}

impl PtrKind {
    pub fn is_mut(&self) -> bool {
        match self {
            PtrKind::OptRef(m) | PtrKind::Raw(m) | PtrKind::Slice(m) => *m,
        }
    }
}

pub struct DecisionMaker<'tcx> {
    tcx: TyCtxt<'tcx>,
    array_pointers: IndexVec<Local, bool>,
    promoted_mut_refs: DenseBitSet<Local>,
    promoted_shared_refs: DenseBitSet<Local>,
}

impl<'tcx> DecisionMaker<'tcx> {
    pub fn new(analysis: &Analysis, did: LocalDefId, tcx: TyCtxt<'tcx>) -> Self {
        let array_pointers = analysis
            .fatness_result
            .function_body_facts(did)
            .map(|fatnesses| {
                fatnesses
                    .iter()
                    .next()
                    .map(|&f| f.is_arr())
                    .unwrap_or(false)
            })
            .collect::<IndexVec<Local, _>>();
        let promoted_mut_refs = analysis.promoted_mut_ref_result.get(&did).unwrap().clone();
        let promoted_shared_refs = analysis
            .promoted_shared_ref_result
            .get(&did)
            .unwrap()
            .clone();
        DecisionMaker {
            tcx,
            array_pointers,
            promoted_mut_refs,
            promoted_shared_refs,
        }
    }

    pub fn decide(
        &self,
        local: Local,
        decl: &LocalDecl,
        aliases: Option<&FxHashSet<usize>>,
    ) -> Option<PtrKind> {
        let (ty, m) = super::transform::unwrap_ptr_from_mir_ty(decl.ty)?;
        let mutability = m.is_mut();
        if ty.is_c_void(self.tcx)
            || aliases.is_some_and(|aliases| aliases.contains(&(local.index() - 1)))
        {
            Some(PtrKind::Raw(mutability))
        } else if self.array_pointers[local] {
            if self.promoted_shared_refs.contains(local) {
                Some(PtrKind::Slice(false))
            } else if self.promoted_mut_refs.contains(local) {
                Some(PtrKind::Slice(true))
            } else {
                Some(PtrKind::Raw(mutability))
            }
        } else if self.promoted_shared_refs.contains(local) {
            Some(PtrKind::OptRef(false))
        } else if self.promoted_mut_refs.contains(local) {
            Some(PtrKind::OptRef(true))
        } else if decl.ty.is_raw_ptr() {
            Some(PtrKind::Raw(mutability))
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
                .map(|(param, param_decl)| decision_maker.decide(param, param_decl, aliases))
                .collect();

            data.insert(
                *did,
                SigDecision {
                    input_decs,
                    output_dec: None, // Currently intra-procedural borrow inference
                },
            );
        }
        SigDecisions { data }
    }
}
