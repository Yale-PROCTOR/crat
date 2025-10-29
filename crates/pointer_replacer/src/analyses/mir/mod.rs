//! Auxilary definitions for MIR

use std::hash::Hash;

use petgraph::{algo::TarjanScc, prelude::DiGraphMap};
use rustc_middle::{
    mir::{Terminator, visit::Visitor},
    ty::TyCtxt,
};
use rustc_span::def_id::LocalDefId;

use crate::utils::{dsa::fixed_shape::VecVec, rustc::RustProgram};

pub mod terminator;
pub mod ty;

pub use terminator::*;

pub struct CallGraphPostOrder(pub VecVec<LocalDefId>);

impl CallGraphPostOrder {
    pub fn new(program: &RustProgram) -> Self {
        let mut graph = DiGraphMap::new();
        for &did in &program.functions {
            graph.add_node(CxDefId::new(program.tcx, did));
        }

        for &did in &program.functions {
            StaticCallGraphBuilder {
                tcx: program.tcx,
                caller: did,
                graph: &mut graph,
            }
            .visit_body(
                &program
                    .tcx
                    .mir_drops_elaborated_and_const_checked(did)
                    .borrow(),
            );
        }

        let mut tarjan_scc = TarjanScc::new();
        let mut post_order = VecVec::with_indices_capacity(program.functions.len());
        tarjan_scc.run(&graph, |nodes| {
            post_order.push_vec(nodes.iter().map(|cxdid| cxdid.did))
        });
        let post_order = post_order.complete();

        CallGraphPostOrder(post_order)
    }

    pub fn sccs(&self) -> impl Iterator<Item = &[LocalDefId]> {
        self.0.iter()
    }
}

/// FIXME: Hmmmm does it make sense at all?
/// Is it possible that two [`DefId`] can have the same name?
#[derive(Clone, Copy)]
pub(crate) struct CxDefId<'tcx> {
    tcx: TyCtxt<'tcx>,
    pub(crate) did: LocalDefId,
}

impl<'tcx> CxDefId<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, did: LocalDefId) -> Self {
        CxDefId { tcx, did }
    }
}

impl Hash for CxDefId<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.did.hash(state);
    }
}

impl PartialEq for CxDefId<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.did == other.did
    }
}

impl Eq for CxDefId<'_> {}

impl PartialOrd for CxDefId<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<'tcx> Ord for CxDefId<'tcx> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.tcx
            .item_name(self.did.to_def_id())
            .cmp(&other.tcx.item_name(other.did.to_def_id()))
    }
}

struct StaticCallGraphBuilder<'me, 'tcx> {
    tcx: TyCtxt<'tcx>,
    caller: LocalDefId,
    /// We use the `def_path_str` of [`DefId`] as keys
    graph: &'me mut DiGraphMap<CxDefId<'tcx>, ()>,
}

impl<'me, 'tcx> Visitor<'tcx> for StaticCallGraphBuilder<'me, 'tcx> {
    fn visit_terminator(
        &mut self,
        terminator: &Terminator<'tcx>,
        _location: rustc_middle::mir::Location,
    ) {
        let Some(MirFunctionCall { func, .. }) = terminator.as_call(self.tcx) else { return };
        let Some(callee) = func.did() else { return };
        let Some(callee) = callee.as_local() else { return };
        if !self.graph.contains_node(CxDefId::new(self.tcx, callee)) {
            return;
        }

        self.graph.add_edge(
            CxDefId::new(self.tcx, self.caller),
            CxDefId::new(self.tcx, callee),
            (),
        );
    }
}
