//! §NB4-4a-ii — **pointee-effect analysis**: may a callee ACCESS (read or write) the POINTEE
//! of a given pointer parameter?
//!
//! **LEAST FIXPOINT.** "May access" taint is GENERATED at direct `Deref` projections and at
//! every escape the analysis cannot track, then PROPAGATED along call edges to a fixpoint.
//! Starting from ⊥ and only ever ADDING facts is sound inside cycles: a real dereference
//! anywhere in an SCC generates the fact, which then propagates around the cycle. There is no
//! optimistic "assume no-access" for an unresolved callee — **every unresolved callee (extern,
//! non-local, fn-pointer) is WORST-CASE access**, except the `NoAccess` boundary rows
//! (`is_null`/`addr`), matched with `library.rs`'s exact `RustPtrPath` discipline.
//!
//! Consumed by `borrow_engine::invalidates`: a `no-access` argument gets a SHALLOW access (the
//! pointer VALUE) instead of the blanket `Deep` access to `(*arg)` that the Call arm emits for
//! EVERY argument of EVERY call — which manufactures conflicts a callee cannot possibly cause.
//!
//! A parameter is tainted `may-access` if ANY of:
//!   * an alias of it is `Deref`-projected (the direct access);
//!   * an alias of it reaches `RETURN_PLACE` — **LOAD-BEARING, see below**;
//!   * an alias of it is stored through a projection, put in an aggregate, or address-taken
//!     (it escapes into memory this analysis does not model);
//!   * it is passed to a non-local / extern / fn-pointer callee that is not a `NoAccess` row;
//!   * it is passed to a local callee whose corresponding parameter is tainted (the fixpoint).
//!
//! ⚠ **"returned ⇒ access" is LOAD-BEARING — do not relax it casually.** `id(q) -> *mut { q }`
//! returns its parameter, so `id` is NOT `no-access` and calls to it keep their `Deep` access.
//! The whole NB4-4a-i fixture set (`nb4_returned_borrow_vs_base_mutation`,
//! `nb4_callee_write_invalidates_caller_loan`, `nb4_returned_immutable_borrow_vs_base_write`)
//! routes its conflict through `id`, so weakening this rule would silently un-demote all three.
//! `nb4_returned_param_is_not_no_access` pins it.

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::mir::{
    Body, CopyNonOverlapping, NonDivergingIntrinsic, Operand, Place, PlaceElem, RETURN_PLACE,
    Rvalue, StatementKind, TerminatorKind,
};
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LocalDefId;

use super::boundary_table;
use crate::utils::rustc::RustProgram;

/// Per-callee, per-parameter "may access the pointee" facts.
pub(crate) struct CallEffects {
    /// `may_access[f][i]` — `f` may read or write the pointee of parameter `i` (0-based; the
    /// MIR local is `Local::from_usize(i + 1)`).
    may_access: FxHashMap<LocalDefId, Vec<bool>>,
}

/// A call edge: `caller`'s param `caller_param` flows into `callee`'s param `callee_param`.
struct CallEdge {
    caller: LocalDefId,
    caller_param: usize,
    callee: LocalDefId,
    callee_param: usize,
}

impl CallEffects {
    pub(crate) fn analyze(program: &RustProgram<'_>) -> Self {
        let tcx = program.tcx;
        let mut may_access: FxHashMap<LocalDefId, Vec<bool>> = FxHashMap::default();
        let mut edges: Vec<CallEdge> = Vec::new();

        for &f in program.functions.iter() {
            let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
            let n_params = body.arg_count;
            let aliases = param_aliases(&body, n_params);
            let mut tainted = vec![false; n_params];
            scan_body(tcx, f, &body, &aliases, &mut tainted, &mut edges);
            may_access.insert(f, tainted);
        }

        // Least fixpoint over call edges: taint only ever grows.
        loop {
            let mut changed = false;
            for e in &edges {
                // An unknown callee shape is worst-case (`true`).
                let callee_tainted = may_access
                    .get(&e.callee)
                    .and_then(|v| v.get(e.callee_param).copied())
                    .unwrap_or(true);
                if !callee_tainted {
                    continue;
                }
                if let Some(v) = may_access.get_mut(&e.caller)
                    && let Some(slot) = v.get_mut(e.caller_param)
                    && !*slot
                {
                    *slot = true;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }

        CallEffects { may_access }
    }

    /// `true` iff `f`'s parameter `param` (0-based) provably never has its pointee accessed.
    /// Unknown functions and out-of-range parameters are WORST-CASE (`false`).
    pub(crate) fn is_no_access(&self, f: LocalDefId, param: usize) -> bool {
        self.may_access
            .get(&f)
            .and_then(|v| v.get(param))
            .is_some_and(|tainted| !*tainted)
    }
}

/// For each MIR local, the set of parameter indices whose POINTER VALUE it may hold.
/// Propagates ONLY through plain local-to-local copies/moves/casts; every other flow is an
/// escape that `scan_body` taints. `RETURN_PLACE` participates, which is exactly how the
/// load-bearing "returned ⇒ access" rule is detected.
fn param_aliases(body: &Body<'_>, n_params: usize) -> Vec<FxHashSet<usize>> {
    let mut aliases: Vec<FxHashSet<usize>> = vec![FxHashSet::default(); body.local_decls.len()];
    for i in 0..n_params {
        aliases[i + 1].insert(i);
    }
    loop {
        let mut changed = false;
        for bb in body.basic_blocks.iter() {
            for stmt in &bb.statements {
                let StatementKind::Assign(box (lhs, rhs)) = &stmt.kind else {
                    continue;
                };
                if !lhs.projection.is_empty() {
                    continue; // a store THROUGH something — an escape, not an alias copy
                }
                let src = match rhs {
                    Rvalue::Use(op) | Rvalue::Cast(_, op, _) => op.place(),
                    Rvalue::CopyForDeref(p) => Some(*p),
                    _ => None,
                };
                let Some(src) = src else { continue };
                if !src.projection.is_empty() {
                    continue; // reading THROUGH a pointer yields the pointee, not the pointer
                }
                let add: Vec<usize> = aliases[src.local.as_usize()].iter().copied().collect();
                for a in add {
                    if aliases[lhs.local.as_usize()].insert(a) {
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
    aliases
}

fn is_deref(place: &Place<'_>) -> bool {
    place.projection.iter().any(|e| e == PlaceElem::Deref)
}

/// Taint every parameter that `place`'s base local may alias.
fn taint_aliases(place: &Place<'_>, aliases: &[FxHashSet<usize>], tainted: &mut [bool]) {
    for &p in &aliases[place.local.as_usize()] {
        if p < tainted.len() {
            tainted[p] = true;
        }
    }
}

/// A `Deref`-projected place is a direct pointee ACCESS (read or write).
fn mark_deref(place: &Place<'_>, aliases: &[FxHashSet<usize>], tainted: &mut [bool]) {
    if is_deref(place) {
        taint_aliases(place, aliases, tainted);
    }
}

/// Every place mentioned by an rvalue we do not special-case. Conservative: each is treated
/// both as a possible deref AND as a possible escape.
fn rvalue_places<'tcx>(rv: &Rvalue<'tcx>) -> Vec<Place<'tcx>> {
    let mut out = Vec::new();
    let mut push_op = |op: &Operand<'tcx>| {
        if let Some(p) = op.place() {
            out.push(p);
        }
    };
    match rv {
        Rvalue::Use(op)
        | Rvalue::Repeat(op, _)
        | Rvalue::Cast(_, op, _)
        | Rvalue::UnaryOp(_, op)
        | Rvalue::ShallowInitBox(op, _)
        | Rvalue::WrapUnsafeBinder(op, _) => push_op(op),
        Rvalue::BinaryOp(_, box (a, b)) => {
            push_op(a);
            push_op(b);
        }
        Rvalue::Aggregate(_, ops) => {
            for op in ops.iter() {
                push_op(op);
            }
        }
        Rvalue::CopyForDeref(p)
        | Rvalue::Ref(_, _, p)
        | Rvalue::RawPtr(_, p)
        | Rvalue::Len(p)
        | Rvalue::Discriminant(p) => out.push(*p),
        Rvalue::ThreadLocalRef(_) | Rvalue::NullaryOp(..) => {}
    }
    out
}

fn scan_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: LocalDefId,
    body: &Body<'tcx>,
    aliases: &[FxHashSet<usize>],
    tainted: &mut [bool],
    edges: &mut Vec<CallEdge>,
) {
    // ⚠ LOAD-BEARING: an alias reaching `RETURN_PLACE` means the parameter's provenance leaves
    // the callee, so the caller's loan on `(*arg)` stays live past the call. `id(q) -> *mut { q }`
    // is exactly this, and the whole 4a-i fixture set depends on it. See the module doc.
    for &p in &aliases[RETURN_PLACE.as_usize()] {
        if p < tainted.len() {
            tainted[p] = true;
        }
    }

    for bb in body.basic_blocks.iter() {
        for stmt in &bb.statements {
            match &stmt.kind {
                StatementKind::Assign(box (lhs, rhs)) => {
                    // A write THROUGH the pointer.
                    mark_deref(lhs, aliases, tainted);
                    let lhs_plain = lhs.projection.is_empty();
                    match rhs {
                        Rvalue::Use(op) | Rvalue::Cast(_, op, _) => {
                            if let Some(p) = op.place() {
                                mark_deref(&p, aliases, tainted);
                                // A plain copy into a plain local is TRACKED by `param_aliases`.
                                // Anything else stores the pointer into memory we cannot follow.
                                if p.projection.is_empty() && !lhs_plain {
                                    taint_aliases(&p, aliases, tainted);
                                }
                            }
                        }
                        Rvalue::CopyForDeref(p) => {
                            mark_deref(p, aliases, tainted);
                            if p.projection.is_empty() && !lhs_plain {
                                taint_aliases(p, aliases, tainted);
                            }
                        }
                        // Taking the ADDRESS of the pointer local itself: it escapes.
                        Rvalue::Ref(_, _, p) | Rvalue::RawPtr(_, p) => {
                            mark_deref(p, aliases, tainted);
                            if p.projection.is_empty() {
                                taint_aliases(p, aliases, tainted);
                            }
                        }
                        other => {
                            for p in rvalue_places(other) {
                                mark_deref(&p, aliases, tainted);
                                taint_aliases(&p, aliases, tainted);
                            }
                        }
                    }
                }
                // `copy_nonoverlapping` reads/writes THROUGH both pointers.
                StatementKind::Intrinsic(box NonDivergingIntrinsic::CopyNonOverlapping(
                    CopyNonOverlapping { src, dst, .. },
                )) => {
                    for op in [src, dst] {
                        if let Some(p) = op.place() {
                            taint_aliases(&p, aliases, tainted);
                        }
                    }
                }
                _ => {}
            }
        }

        let Some(term) = &bb.terminator else { continue };
        match &term.kind {
            TerminatorKind::Call { func, args, .. } | TerminatorKind::TailCall { func, args, .. } => {
                let callee = func.const_fn_def().map(|(did, _)| did);
                for (i, arg) in args.iter().enumerate() {
                    let Some(place) = arg.node.place() else { continue };
                    // Passing `(*p)` is a deref regardless of the callee.
                    mark_deref(&place, aliases, tainted);
                    if !place.projection.is_empty() {
                        continue;
                    }
                    if aliases[place.local.as_usize()].is_empty() {
                        continue;
                    }
                    match callee.and_then(|did| did.as_local().map(|l| (did, l))) {
                        // Local callee: defer to the fixpoint — one edge per aliased caller param.
                        Some((_, local_callee)) => {
                            for &cp in &aliases[place.local.as_usize()] {
                                edges.push(CallEdge {
                                    caller,
                                    caller_param: cp,
                                    callee: local_callee,
                                    callee_param: i,
                                });
                            }
                        }
                        // A `NoAccess` boundary row (`is_null`/`addr`) inspects the POINTER only.
                        None if callee
                            .is_some_and(|did| boundary_table::callee_is_no_access(tcx, did)) => {}
                        // Everything else — extern C, unknown non-local, fn-pointer (`None`) —
                        // is WORST-CASE access (rider 1: never silently drop the alias).
                        None => taint_aliases(&place, aliases, tainted),
                    }
                }
            }
            TerminatorKind::InlineAsm { operands, .. } => {
                // Anything reaching inline asm escapes entirely.
                use rustc_middle::mir::InlineAsmOperand;
                for op in operands {
                    let places: Vec<Place<'_>> = match op {
                        InlineAsmOperand::In { value, .. } => {
                            value.place().into_iter().collect()
                        }
                        InlineAsmOperand::Out { place, .. } => place.iter().copied().collect(),
                        InlineAsmOperand::InOut {
                            in_value, out_place, ..
                        } => in_value
                            .place()
                            .into_iter()
                            .chain(out_place.iter().copied())
                            .collect(),
                        _ => vec![],
                    };
                    for p in places {
                        taint_aliases(&p, aliases, tainted);
                    }
                }
            }
            TerminatorKind::Drop { place, .. } => taint_aliases(place, aliases, tainted),
            _ => {}
        }
    }
}
