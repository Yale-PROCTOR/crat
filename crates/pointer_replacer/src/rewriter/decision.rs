use rustc_hash::FxHashMap;
use rustc_index::IndexVec;
use rustc_middle::mir::Local;
use rustc_span::def_id::LocalDefId;

use super::{Analysis, collector::collect_fn_ptrs};
use crate::utils::rustc::RustProgram;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PtrKind {
    /// reference: &mut T for Ref(true), or &T for Ref(false)
    OptRef(bool),
    /// raw pointer: *mut T for Raw(true), or *const T for Raw(false)
    Raw(bool),
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
            let promoted_shared_refs = analysis
                .mutability_result
                .function_facts(*did, rust_program.tcx) // output + inputs
                .map(|mutabilities| mutabilities.iter().all(|&m| m.is_immutable())) // No mutables behind shared refs
                .collect::<IndexVec<Local, _>>();
            let _array_pointers = analysis
                .fatness_result
                .function_facts(*did, rust_program.tcx) // output + inputs
                .map(|fatnesses| fatnesses.iter().next().map(|&f| f.is_arr()).unwrap_or(false))
                .collect::<IndexVec<Local, _>>();
            let promoted_mut_refs = analysis.promoted_mut_ref_result.get(did).unwrap();

            let body = &*rust_program
                .tcx
                .mir_drops_elaborated_and_const_checked(did)
                .borrow();

            let sig = rust_program.tcx.fn_sig(*did).skip_binder();
            let input_len = sig.inputs().skip_binder().len();

            let input_decs = body
                .local_decls.iter().collect::<IndexVec<Local, _>>()
                .iter_enumerated().skip(1)
                .take(input_len) // exclude variadic arguments
                .map(|(param, param_decl)| {
                    if !param_decl.ty.is_any_ptr() {
                        None
                    }
                    // TODO: More precise filtering of array pointers
                    // else if array_pointers[param] {
                    //     None
                    // }
                    else if promoted_shared_refs[param] {
                        Some(PtrKind::OptRef(false))
                    } else if promoted_mut_refs.contains(param) {
                        Some(PtrKind::OptRef(body.local_decls[param].ty.is_mutable_ptr()))
                    } else {
                        None
                    }
                })
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
