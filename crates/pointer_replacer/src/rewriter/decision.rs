use rustc_hash::FxHashMap;
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
            let output_params = analysis.output_param_result.get(did).unwrap();
            let promoted_mut_refs = analysis.promoted_mut_ref_result.get(did).unwrap();

            let body = &*rust_program
                .tcx
                .mir_drops_elaborated_and_const_checked(did)
                .borrow();

            let sig = rust_program.tcx.fn_sig(*did).skip_binder();
            let input_len = sig.inputs().skip_binder().len();

            let input_decs = body
                .args_iter()
                .take(input_len) // exclude variadic arguments
                .map(|param| {
                    let mutability = body.local_decls[param].ty.is_mutable_ptr();
                    if output_params.contains(param) {
                        Some(PtrKind::OptRef(true))
                    } else if promoted_mut_refs.contains(param) {
                        Some(PtrKind::OptRef(mutability))
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
