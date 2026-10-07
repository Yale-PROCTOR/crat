//! **R864-1 (relay 299; fan-out 081) — the pairs the pair pass drops.** At an
//! in-program call, an argument handed to a formal the settled table delivers as
//! a reference, beside an argument handed to a formal that stays raw, may name
//! one object: libzahl's `zsqr(x.as_mut_ptr(), &mut *x.as_mut_ptr())` hands the
//! same `z_t` to `zsqr(a: *mut Z, b: &mut Z)`, which reads through `b` and writes
//! through `a` while `b` is a live, protected argument (UB under both models; the
//! fan-out's `repro/`). The pair pass keeps a may-overlap pair only when both
//! formals convert (`co_conversion.rs:1001`), and A5 replays only pairs both of
//! whose formals are Ref in the baseline, so no row, proof or receipt existed.
//!
//! The rule is R833-1's: a pair that may overlap at a call inside the program
//! keeps both sides raw. **Its scope is R870-1's (a), the gaps only:** a
//! contained pair, unresolved roots on both sides, one subject at a PAIR-owned
//! `clear` call. The pairs the PAIR knows (its raw view and ordering proof), the
//! seam's aliased-storage twin, and the field-load exemption keep their answers,
//! and the `overlapping` pairs are wave-5d's callee-peer rule's. The raw side is raw already; the reference side, the
//! callee's formal, is held (`held:pair-not-shown-disjoint`, detail
//! `ref-beside-raw`), and `into-held-formal` holds the caller's binding behind it
//! in the same fixpoint.
//!
//! **The same-subject rule (class 2)** comes first: two arguments rooted at one
//! binding are never disjoint, whatever a proof says (`zmul`'s
//! `zadd(&mut *b_low.as_mut_ptr(), b_low.as_mut_ptr(), …)` read
//! `clear:a5-proven-disjoint`).
//!
//! **The containment pair (R866-1, fan-out 083)** next: two arguments one of
//! which derives from the other's object overlap by construction. brotli's
//! `ProcessCommandsInternal` hands `SafeReadDistance(&mut *s, &mut *br)` with
//! `br = &mut (*s).br`: both formals delivered as `&mut`, no pair row at that
//! call. Where both formals are delivered references, both are held; where one
//! is raw, the reference side is (`ref-beside-ref` / `ref-beside-raw`).

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{HirId, def_id::LocalDefId};
use rustc_middle::ty::TyCtxt;

use super::{
    Decision, DecisionTable, DegradeReason, SubjectKind,
    a5_site_proof::{A5SeamProofIndex, A5SiteProofVerdict},
    co_conversion::{PairRole, PairSiteDecision},
    emitability::{Arg, ArgShape, EmitabilityFacts},
};

/// What an argument names, as far as the caller's text shows.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Object {
    /// Storage of the caller's own frame: a binding that holds its object (an
    /// array, a struct), however it is reached (`x.as_mut_ptr()`,
    /// `&mut *x.as_mut_ptr()`), or a binding's own storage (`&mut p`).
    Frame(HirId),
    /// The pointee of a pointer binding (`p`, `p as *mut T`, `p.offset(k)`,
    /// `&mut *p`, `&mut (*p).f`).
    Pointee(HirId),
    /// The null literal: no object.
    Null,
    Unknown,
}

fn holds_its_object(tcx: TyCtxt<'_>, function: LocalDefId, binding: HirId) -> bool {
    let ty = tcx.typeck(function).node_type(binding);
    !(ty.is_any_ptr() || ty.is_box())
}

fn object_of(tcx: TyCtxt<'_>, caller: LocalDefId, argument: &Arg) -> Object {
    if let Some((binding, _)) = argument.direct_storage {
        return Object::Frame(binding);
    }
    match argument.shape {
        ArgShape::NullLit => Object::Null,
        ArgShape::AddrOf {
            base: Some(binding),
            through_deref: false,
            ..
        } => Object::Frame(binding),
        ArgShape::AddrOf {
            base: Some(binding),
            through_deref: true,
            ..
        }
        | ArgShape::RawExpr {
            root: Some(binding),
        }
        | ArgShape::BareLocal(binding)
        | ArgShape::CastOfLocal { binding, .. } => {
            if holds_its_object(tcx, caller, binding) {
                Object::Frame(binding)
            } else {
                Object::Pointee(binding)
            }
        }
        ArgShape::AddrOf { base: None, .. }
        | ArgShape::RawExpr { root: None }
        | ArgShape::AddrOfCast { .. }
        | ArgShape::Cast { .. }
        | ArgShape::Other => Object::Unknown,
    }
}

/// Is this decision a reference family's (the reference side of a pair), and
/// is it mutable? Exhaustive by rule (`import_denylist`): a `Box` is an owner
/// the call moves, never a view, and a degraded subject is raw.
fn reference_family(decision: &Decision) -> Option<bool> {
    match decision {
        Decision::Ref { mutable }
        | Decision::InferredRef { mutable, .. }
        | Decision::Slice { mutable, .. }
        | Decision::NestedSlice { mutable, .. }
        | Decision::Opt { mutable, .. }
        | Decision::Cursor { mutable, .. } => Some(*mutable),
        Decision::Box(_) | Decision::Degraded(_) => None,
    }
}

fn is_raw(decision: &Decision) -> bool {
    match decision {
        Decision::Degraded(_) => true,
        Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::NestedSlice { .. }
        | Decision::Opt { .. }
        | Decision::Cursor { .. }
        | Decision::Box(_) => false,
    }
}

/// How two arguments' objects relate, as far as the caller shows.
enum Relation {
    /// Rooted at one binding (the same-subject rule, R864-1 (b)).
    Same,
    /// One derived from the other's object (a field projection, a copy, a step:
    /// R866-1, brotli's `&mut *s` beside `&mut *br` with `br = &mut (*s).br`).
    Contained,
    Disjoint,
    /// Neither argument's root resolves to a binding (a static, an opaque
    /// expression): the seam's aliased-storage twin sees no binding, so nothing
    /// else answers (libzahl's class 1, `libzahl_tmp_pow_b` at both positions).
    Unresolved,
    /// One side resolves: the PAIR, the twin or the field-load exemption answer
    /// (R870-1, scope (a)).
    Unknown,
}

/// The reference-side formals R864-1 / R866-1 hold on this table, each with its
/// reason.
pub(crate) fn holds(
    tcx: TyCtxt<'_>,
    facts: &EmitabilityFacts,
    table: &DecisionTable,
    proofs: &A5SeamProofIndex,
    mut_facts: &crate::analyses::borrow_ownership::mutability_facts::MutFacts,
    pair_sites: &[PairSiteDecision],
) -> Vec<((LocalDefId, HirId), DegradeReason)> {
    struct Formal<'a> {
        node: (LocalDefId, HirId),
        local: rustc_middle::mir::Local,
        decision: &'a Decision,
    }
    let formals: FxHashMap<(LocalDefId, usize), Formal<'_>> = table
        .entries
        .iter()
        .filter_map(|(subject, decision)| match subject.kind {
            SubjectKind::Param { hir_index } => Some((
                (subject.fn_did, hir_index),
                Formal {
                    node: (subject.fn_did, subject.hir_id),
                    local: subject.local,
                    decision,
                },
            )),
            _ => None,
        })
        .collect();
    // Every subject binding's MIR local, both ways, for the derivations.
    let local_of: FxHashMap<(LocalDefId, HirId), rustc_middle::mir::Local> = table
        .entries
        .iter()
        .map(|(subject, _)| ((subject.fn_did, subject.hir_id), subject.local))
        .collect();
    let binding_of: FxHashMap<(LocalDefId, rustc_middle::mir::Local), HirId> = table
        .entries
        .iter()
        .map(|(subject, _)| ((subject.fn_did, subject.local), subject.hir_id))
        .collect();
    // The bindings a pointer binding's value derives from, itself included.
    let mut derived: FxHashMap<(LocalDefId, HirId), FxHashSet<HirId>> = FxHashMap::default();
    let mut derivation = |function: LocalDefId, binding: HirId| -> FxHashSet<HirId> {
        derived
            .entry((function, binding))
            .or_insert_with(|| {
                let mut out: FxHashSet<HirId> = FxHashSet::default();
                out.insert(binding);
                if let Some(&local) = local_of.get(&(function, binding)) {
                    out.extend(
                        super::settled_holds::locals_flowing_into(tcx, function, local)
                            .into_iter()
                            .filter_map(|source| binding_of.get(&(function, source)).copied()),
                    );
                }
                out
            })
            .clone()
    };
    let mut out: FxHashMap<(LocalDefId, HirId), DegradeReason> = FxHashMap::default();
    let mut hold = |node: (LocalDefId, HirId), detail: String| {
        out.entry(node)
            .or_insert(DegradeReason::PairNotShownDisjoint { detail });
    };
    let mut callees: Vec<_> = facts.call_args.keys().copied().collect();
    callees.sort_by_key(|callee| callee.local_def_index.as_u32());
    for callee in callees {
        for call in &facts.call_args[&callee] {
            for (position, left) in call.args.iter().enumerate() {
                for right in &call.args[position + 1..] {
                    let (Some(fl), Some(fr)) = (
                        formals.get(&(callee, left.index)),
                        formals.get(&(callee, right.index)),
                    ) else {
                        continue;
                    };
                    let (ml, mr) = (reference_family(fl.decision), reference_family(fr.decision));
                    // The held sides, and whether the pair can conflict: a mutable
                    // reference with any access, a shared one with a write through
                    // a raw side.
                    let (held, conflict, kind) = match (ml, mr) {
                        (Some(m), None) if is_raw(fr.decision) => (
                            vec![(fl.node, left.index)],
                            m || mut_facts.is_mutable(callee, fr.local),
                            "ref-beside-raw",
                        ),
                        (None, Some(m)) if is_raw(fl.decision) => (
                            vec![(fr.node, right.index)],
                            m || mut_facts.is_mutable(callee, fl.local),
                            "ref-beside-raw",
                        ),
                        (Some(a), Some(b)) => (
                            vec![(fl.node, left.index), (fr.node, right.index)],
                            a || b,
                            "ref-beside-ref",
                        ),
                        _ => continue,
                    };
                    if !conflict {
                        continue;
                    }
                    let relation = match (
                        object_of(tcx, call.caller, left),
                        object_of(tcx, call.caller, right),
                    ) {
                        (Object::Null, _) | (_, Object::Null) => Relation::Disjoint,
                        (Object::Frame(a), Object::Frame(b))
                        | (Object::Pointee(a), Object::Pointee(b))
                            if a == b =>
                        {
                            Relation::Same
                        }
                        (Object::Frame(_), Object::Frame(_)) => Relation::Disjoint,
                        (Object::Pointee(a), Object::Pointee(b))
                            if !derivation(call.caller, a)
                                .is_disjoint(&derivation(call.caller, b)) =>
                        {
                            Relation::Contained
                        }
                        (Object::Frame(_), Object::Pointee(formal))
                        | (Object::Pointee(formal), Object::Frame(_))
                            if is_entry_formal(tcx, call.caller, formal) =>
                        {
                            Relation::Disjoint
                        }
                        (Object::Unknown, Object::Unknown) => Relation::Unresolved,
                        _ => Relation::Unknown,
                    };
                    // The PAIR machinery's roles at this call (co-conversion's pair
                    // sites): a placed view (`primary` / `raw-view`) carries its own
                    // ordering proof; a `clear` rests on the classifier.
                    // A role is per position, so the PAIR speaks for this pair
                    // only where it placed a site at both of its positions.
                    let role_at = |index: usize| {
                        pair_sites
                            .iter()
                            .find(|pair| {
                                pair.caller == call.caller
                                    && pair.callee == callee
                                    && pair
                                        .call_span
                                        .source_callsite()
                                        .contains(call.span.source_callsite())
                                    && pair.argument_index == index
                            })
                            .map(|pair| pair.role)
                    };
                    let roles: Vec<PairRole> = match (role_at(left.index), role_at(right.index)) {
                        (Some(a), Some(b)) => vec![a, b],
                        _ => Vec::new(),
                    };
                    let ordered = roles.iter().any(|role| match role {
                        PairRole::Primary | PairRole::RawView => true,
                        PairRole::Clear | PairRole::Blocked => false,
                    });
                    let pair_owned = roles.iter().any(|role| match role {
                        PairRole::Clear | PairRole::Primary | PairRole::RawView => true,
                        PairRole::Blocked => false,
                    });
                    // The counted-void family routes a call at its counted positions
                    // itself (split with a proof, else the pristine raw twin): its
                    // answer stands (R870-1).
                    if ordered
                        || super::counted_void::contract_at(table, callee, left.index).is_some()
                        || super::counted_void::contract_at(table, callee, right.index).is_some()
                    {
                        continue;
                    }
                    let why = match relation {
                        Relation::Disjoint => continue,
                        // One local at two positions of a call the PAIR machinery
                        // does not own is the seam's aliased-storage twin (a raw twin,
                        // or the call held): R408-7, wave-6v. Where the PAIR owns it
                        // with `clear`, the twin is never consulted and the clear may
                        // be the classifier's false one (class 2).
                        Relation::Same if !pair_owned => continue,
                        Relation::Same => "same-subject".to_owned(),
                        Relation::Contained => "contained".to_owned(),
                        // R870-1 (scope (a)): where one root resolves, another layer
                        // answers; two converting formals are the pair pass's and
                        // A5's own question.
                        Relation::Unknown => continue,
                        Relation::Unresolved if kind == "ref-beside-ref" => continue,
                        Relation::Unresolved
                            if call_arguments(tcx, call.caller, call.span).is_some_and(
                                |arguments| match (
                                    arguments.get(left.index),
                                    arguments.get(right.index),
                                ) {
                                    (Some(l), Some(r)) => {
                                        super::counted_void::disjoint_roots(tcx, call.caller, l, r)
                                    }
                                    _ => false,
                                },
                            ) =>
                        {
                            continue;
                        }
                        Relation::Unresolved => {
                            let proof = proofs.lookup(
                                call.caller.local_def_index.as_u32(),
                                callee.local_def_index.as_u32(),
                                left.index,
                                right.index,
                                left.span,
                                right.span,
                            );
                            if proof.verdict == A5SiteProofVerdict::Clear {
                                continue;
                            }
                            format!("unresolved;proof={}", proof.verdict.key())
                        }
                    };
                    for (node, index) in held {
                        let other = if index == left.index {
                            right.index
                        } else {
                            left.index
                        };
                        hold(
                            node,
                            format!(
                                "pair-not-shown-disjoint:{kind}:{}#{}:peer#{}:caller={};{why}",
                                tcx.def_path_str(callee.to_def_id()),
                                index + 1,
                                other + 1,
                                tcx.def_path_str(call.caller.to_def_id()),
                            ),
                        );
                    }
                }
            }
        }
    }
    let mut out: Vec<_> = out.into_iter().collect();
    out.sort_by_key(|((function, binding), _)| {
        (function.local_def_index.as_u32(), binding.local_id.as_u32())
    });
    out
}

/// A formal of `caller` that still holds its entry value (premise (a)'s own
/// condition, as `sibling_overlap` reads it).
fn is_entry_formal(tcx: TyCtxt<'_>, caller: LocalDefId, binding: HirId) -> bool {
    tcx.hir_body_owned_by(caller)
        .params
        .iter()
        .any(|param| param.pat.hir_id == binding)
        && super::sibling_overlap::formal_keeps_its_entry_value(tcx, caller, binding)
}

/// The call's argument expressions at `call_span` in `caller`'s body.
fn call_arguments<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: LocalDefId,
    call_span: rustc_span::Span,
) -> Option<&'tcx [rustc_hir::Expr<'tcx>]> {
    use rustc_hir::{Expr, ExprKind, intravisit};
    struct Find<'tcx> {
        call_span: rustc_span::Span,
        found: Option<&'tcx [Expr<'tcx>]>,
    }
    impl<'tcx> intravisit::Visitor<'tcx> for Find<'tcx> {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            if self.found.is_none()
                && let ExprKind::Call(_, arguments) = expr.kind
                && expr.span.source_callsite() == self.call_span.source_callsite()
            {
                self.found = Some(arguments);
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let mut find = Find {
        call_span,
        found: None,
    };
    intravisit::Visitor::visit_body(&mut find, tcx.hir_body_owned_by(caller));
    find.found
}
