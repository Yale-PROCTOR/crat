//! Experimental unified borrow/ownership analysis.
//!
//! This module is intentionally self-contained while it is being built out. The
//! existing `borrow` and `ownership` analyses remain the production baseline.
#![allow(dead_code)]

mod domain;
pub mod crate_slots;
pub mod resolve;
pub mod slots;
mod assoc;
mod call_graph;
#[cfg(not(test))]
mod ptr;
#[cfg(test)]
pub(crate) mod ptr;
mod struct_ctxt;
mod vec_vec;
pub mod ssa;

#[allow(unused_imports)]
pub use domain::SlotKind;

use crate::utils::rustc::RustProgram;

pub type Precision = u8;

pub struct CrateCtxt<'tcx> {
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    fn_ctxt: call_graph::CallGraph,
    struct_ctxt: struct_ctxt::StructCtxt<'tcx>,
}

impl<'tcx> CrateCtxt<'tcx> {
    pub fn new(program: &RustProgram<'tcx>) -> Self {
        let fns = program
            .functions
            .iter()
            .map(|did| did.to_def_id())
            .collect::<Vec<_>>();
        let structs = program
            .structs
            .iter()
            .map(|did| did.to_def_id())
            .collect::<Vec<_>>();

        CrateCtxt {
            tcx: program.tcx,
            fn_ctxt: call_graph::CallGraph::new(program.tcx, &fns),
            struct_ctxt: struct_ctxt::StructCtxt::new(program.tcx, &structs),
        }
    }

    #[inline]
    pub fn fns(&self) -> &[rustc_hir::def_id::DefId] {
        self.fn_ctxt.fns()
    }
}
