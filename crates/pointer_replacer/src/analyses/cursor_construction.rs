//! enforces the cursor-construction discipline rule for definitely-negative
//! cursor params: never emit a construction whose below-entry range is
//! knowably empty. A call-site argument whose pointer-flow provenance yields
//! a unique allocation base (param, local array, heap alloc, opaque return)
//! gets a base-preserving construction from the existing emission paths; an
//! argument with no such base (raw borrow of a field, int-to-ptr, unknown or
//! multiple bases) would be rebased to position 0, turning below-entry seeks
//! into latent panics, so the param must fall back to a raw pointer.
//!
//! params whose derivability hinges on a forwarded caller param cascade: if
//! the caller's param falls back to raw, the forwarded argument is a raw
//! pointer and its cursor construction would rebase, so the callee's param
//! falls back too.
//!
//! rewriter-agnostic: knows nothing about pointer-kind decisions. consumers
//! intersect `needs_raw_fallback` with the params they decide to make
//! cursors.

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    mir::{Body, Local, Operand, Place, TerminatorKind},
    ty::{self, TyCtxt},
};

use crate::{
    analyses::{
        offset_sign::sign::OffsetSignResult,
        pointer_flow::{
            self, PointerFlowResult,
            graph::{BaseId, PfgNode},
        },
    },
    utils::rustc::RustProgram,
};

pub struct CursorConstruction {
    /// definitely-negative params with a call site whose argument has no
    /// derivable allocation base: cursor constructions there would rebase,
    /// so these params must stay raw pointers
    raw_fallback: FxHashSet<(LocalDefId, Local)>,
}

impl CursorConstruction {
    pub fn compute(
        input: &RustProgram<'_>,
        offset_signs: &OffsetSignResult,
        fn_ptr_participants: &FxHashSet<LocalDefId>,
        alloc_fns: &FxHashSet<LocalDefId>,
    ) -> Self {
        let tcx = input.tcx;
        let flows = pointer_flow::pointer_flow_analysis(input, alloc_fns);

        // params that definitely move below their entry position and so stay
        // cursors after demotion; fn-ptr participants keep cursors
        // pessimistically and are out of scope
        let mut candidates: FxHashMap<LocalDefId, Vec<Local>> = FxHashMap::default();
        for &did in &input.functions {
            if fn_ptr_participants.contains(&did) {
                continue;
            }
            let Some(definite) = offset_signs.definite_signs.get(&did) else {
                continue;
            };
            let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
            let params: Vec<_> = body.args_iter().filter(|&l| definite.contains(l)).collect();
            if !params.is_empty() {
                candidates.insert(did, params);
            }
        }

        let mut raw_fallback: FxHashSet<(LocalDefId, Local)> = FxHashSet::default();
        // caller param -> candidate callee params fed by it, for the cascade
        let mut forwards: FxHashMap<(LocalDefId, Local), Vec<(LocalDefId, Local)>> =
            FxHashMap::default();

        for &did in &input.functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
            let flow = flows.get(&did);
            for bb_data in body.basic_blocks.iter() {
                let TerminatorKind::Call { func, args, .. } = &bb_data.terminator().kind else {
                    continue;
                };
                let Operand::Constant(box constant) = func else { continue };
                let ty::TyKind::FnDef(callee, _) = constant.const_.ty().kind() else {
                    continue;
                };
                let Some(callee) = callee.as_local() else { continue };
                let Some(params) = candidates.get(&callee) else { continue };
                for &param in params {
                    let Some(arg) = args.get(param.index() - 1) else { continue };
                    let base = match &arg.node {
                        Operand::Copy(place) | Operand::Move(place) => {
                            flow.and_then(|f| arg_base(f, &body, tcx, *place))
                        }
                        Operand::Constant(_) => None,
                    };
                    match base {
                        Some(BaseId::Param { local, .. }) => forwards
                            .entry((did, local))
                            .or_default()
                            .push((callee, param)),
                        Some(
                            BaseId::LocalArray { .. }
                            | BaseId::HeapAlloc { .. }
                            | BaseId::OpaqueReturn { .. },
                        ) => {}
                        _ => {
                            raw_fallback.insert((callee, param));
                        }
                    }
                }
            }
        }

        // cascade: a forwarded argument of a raw-fallback param is itself a
        // raw pointer at the call site
        let mut worklist: Vec<_> = raw_fallback.iter().copied().collect();
        while let Some(param) = worklist.pop() {
            if let Some(targets) = forwards.get(&param) {
                for &target in targets {
                    if raw_fallback.insert(target) {
                        worklist.push(target);
                    }
                }
            }
        }

        Self { raw_fallback }
    }

    pub fn needs_raw_fallback(&self, did: LocalDefId, local: Local) -> bool {
        self.raw_fallback.contains(&(did, local))
    }
}

fn arg_base<'tcx>(
    flow: &PointerFlowResult,
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    place: Place<'tcx>,
) -> Option<BaseId> {
    let slot = flow
        .slot_table
        .place_slots(place, body, tcx)
        .and_then(|mut slots| slots.next())?;
    flow.provenance.unique_non_null_base(&PfgNode::Slot(slot))
}
