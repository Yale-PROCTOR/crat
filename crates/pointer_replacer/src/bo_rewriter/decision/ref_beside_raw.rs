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
//! and the `overlapping` pairs are wave-5d's callee-peer rule's. The raw side is
//! raw already; the reference side, the callee's formal, is held
//! (`held:pair-not-shown-disjoint`, detail `ref-beside-raw`), and
//! `into-held-formal` holds the caller's binding behind it in the same fixpoint.
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
    /// A static item, however it is reached (`TMP.as_mut_ptr()`; the review's
    /// MED-5): one static at two positions is one object, two statics are two.
    Static(rustc_hir::def_id::DefId),
    /// The null literal: no object.
    Null,
    Unknown,
}

fn holds_its_object(tcx: TyCtxt<'_>, function: LocalDefId, binding: HirId) -> bool {
    let ty = tcx.typeck(function).node_type(binding);
    !(ty.is_any_ptr() || ty.is_box())
}

/// The static item an argument's place is rooted at, beneath casts, borrows,
/// dereferences, fields, indices and method receivers.
fn static_root(expr: &rustc_hir::Expr<'_>) -> Option<rustc_hir::def_id::DefId> {
    use rustc_hir::{
        ExprKind, QPath,
        def::{DefKind, Res},
    };
    let mut cur = expr;
    loop {
        cur = match &cur.kind {
            ExprKind::Unary(rustc_hir::UnOp::Deref, base)
            | ExprKind::Field(base, _)
            | ExprKind::Index(base, _, _)
            | ExprKind::AddrOf(_, _, base)
            | ExprKind::Cast(base, _)
            | ExprKind::DropTemps(base) => base,
            ExprKind::MethodCall(_, receiver, _, _) => receiver,
            ExprKind::Path(QPath::Resolved(None, path)) => {
                return match path.res {
                    Res::Def(DefKind::Static { .. }, def_id) => Some(def_id),
                    _ => None,
                };
            }
            _ => return None,
        };
    }
}

/// Does the argument's place cross a field projection on its way to its root
/// (`&mut (*s).f`, `(*s).f.as_mut_ptr()`)? Two such places under one root may be
/// disjoint fields (the PAIR's rule (c)); an index never diverges (two elements
/// may coincide), so it does not count.
fn projects_field(expr: &rustc_hir::Expr<'_>) -> bool {
    use rustc_hir::ExprKind;
    let mut cur = expr;
    loop {
        cur = match &cur.kind {
            ExprKind::Field(..) => return true,
            ExprKind::Unary(rustc_hir::UnOp::Deref, base)
            | ExprKind::Index(base, _, _)
            | ExprKind::AddrOf(_, _, base)
            | ExprKind::Cast(base, _)
            | ExprKind::DropTemps(base) => base,
            ExprKind::MethodCall(_, receiver, _, _) => receiver,
            _ => return false,
        };
    }
}

fn object_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: LocalDefId,
    argument: &Arg,
    expression: Option<&'tcx rustc_hir::Expr<'tcx>>,
) -> Object {
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
        | ArgShape::Other => expression
            .and_then(static_root)
            .map_or(Object::Unknown, Object::Static),
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
    /// Rooted at one local binding (the same-subject rule, R864-1 (b)).
    Same,
    /// One static item at both positions: no twin sees it.
    SameStatic,
    /// One argument's value derives from the other's object (a field
    /// projection, a copy, a cast, a pointer step, a borrow of the frame object:
    /// R866-1, brotli's `&mut *s` beside `&mut *br` with `br = &mut (*s).br`).
    Contained,
    Disjoint,
    /// Neither root resolves to a binding (an opaque expression, a static beside
    /// a pointer): nothing else answers (libzahl's class 1).
    Unresolved,
    /// One side resolves: the PAIR, the twin or the field-load exemption answer
    /// (R870-1, scope (a)).
    Unknown,
}

/// The pair's own edge in the PAIR's receipts at this call (`l/r->…:verdict:
/// reason:family`, the review's MED-1): its verdict and whether a `clear` is a
/// certificate's (trusted) or the classifier's (`a5-proven-disjoint`).
enum Edge {
    /// The PAIR places its raw view for this pair: overlapping or undeterminable.
    Ordered,
    CertifiedClear,
    ClassifierClear,
    None,
}

fn pair_edge(
    pair_sites: &[PairSiteDecision],
    caller: LocalDefId,
    callee: LocalDefId,
    call_span: rustc_span::Span,
    left: usize,
    right: usize,
) -> Edge {
    let (low, high) = (left.min(right), left.max(right));
    let key = format!("{low}/{high}->");
    for pair in pair_sites.iter().filter(|pair| {
        pair.caller == caller
            && pair.callee == callee
            && pair
                .call_span
                .source_callsite()
                .contains(call_span.source_callsite())
            && (pair.argument_index == left || pair.argument_index == right)
            && match pair.role {
                PairRole::Clear | PairRole::Primary | PairRole::RawView => true,
                PairRole::Blocked => false,
            }
    }) {
        for receipt in pair.peer_receipts.split(';') {
            let Some(rest) = receipt.strip_prefix(&key) else {
                continue;
            };
            let mut fields = rest.splitn(4, ':');
            let _positions = fields.next();
            let verdict = fields.next().unwrap_or_default();
            let reason = fields.next().unwrap_or_default();
            return match verdict {
                "clear" if reason.contains("a5-proven-disjoint") => Edge::ClassifierClear,
                "clear" => Edge::CertifiedClear,
                _ => Edge::Ordered,
            };
        }
    }
    Edge::None
}

/// The MIR locals a local's value derives from by construction (the review's
/// HIGH-2: no arbitrary call edges): copies and casts through temporaries, the
/// pointer steps and `as_ptr` / `as_mut_ptr` by name, and borrows of a place —
/// through a dereference of a local (`&mut (*s).br`) or of a frame object
/// itself (`&mut x`). Closed backward from `target`, `target` included.
fn strict_sources(
    tcx: TyCtxt<'_>,
    function: LocalDefId,
    target: rustc_middle::mir::Local,
) -> FxHashSet<rustc_middle::mir::Local> {
    use rustc_middle::mir::{Local, Operand, Rvalue, StatementKind, TerminatorKind};
    fn whole(operand: &Operand<'_>) -> Option<Local> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                Some(place.local)
            }
            _ => None,
        }
    }
    let body = tcx
        .mir_drops_elaborated_and_const_checked(function)
        .borrow();
    let mut sources: FxHashMap<Local, Vec<Local>> = FxHashMap::default();
    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (place, rvalue) = &**assign;
            if !place.projection.is_empty() {
                continue;
            }
            let from = match rvalue {
                Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => whole(operand),
                Rvalue::Ref(_, _, borrowed) | Rvalue::RawPtr(_, borrowed) => Some(borrowed.local),
                _ => None,
            };
            if let Some(from) = from {
                sources.entry(place.local).or_default().push(from);
            }
        }
        if let Some(terminator) = &block.terminator
            && let TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &terminator.kind
            && destination.projection.is_empty()
            && let Some((callee, _)) = func.const_fn_def()
            && matches!(
                tcx.item_name(callee).as_str(),
                "offset"
                    | "add"
                    | "sub"
                    | "wrapping_offset"
                    | "wrapping_add"
                    | "wrapping_sub"
                    | "byte_offset"
                    | "byte_add"
                    | "byte_sub"
                    | "cast"
                    | "cast_mut"
                    | "cast_const"
                    | "as_ptr"
                    | "as_mut_ptr"
            )
            && let Some(from) = args.first().and_then(|argument| whole(&argument.node))
        {
            sources.entry(destination.local).or_default().push(from);
        }
    }
    let mut seen = FxHashSet::default();
    seen.insert(target);
    let mut work = vec![target];
    while let Some(local) = work.pop() {
        for &from in sources.get(&local).into_iter().flatten() {
            if seen.insert(from) {
                work.push(from);
            }
        }
    }
    seen
}

/// The MIR local of a HIR binding of `function`: a subject's own, else the
/// debug info's place at the binding's span.
fn mir_local_of(
    tcx: TyCtxt<'_>,
    function: LocalDefId,
    binding: HirId,
    subjects: &FxHashMap<(LocalDefId, HirId), rustc_middle::mir::Local>,
) -> Option<rustc_middle::mir::Local> {
    if let Some(&local) = subjects.get(&(function, binding)) {
        return Some(local);
    }
    let span = tcx.hir_span(binding);
    let body = tcx
        .mir_drops_elaborated_and_const_checked(function)
        .borrow();
    body.var_debug_info
        .iter()
        .find_map(|info| match &info.value {
            rustc_middle::mir::VarDebugInfoContents::Place(place)
                if place.projection.is_empty() && info.source_info.span == span =>
            {
                Some(place.local)
            }
            _ => None,
        })
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
    let local_of: FxHashMap<(LocalDefId, HirId), rustc_middle::mir::Local> = table
        .entries
        .iter()
        .map(|(subject, _)| ((subject.fn_did, subject.hir_id), subject.local))
        .collect();
    let mut sources: FxHashMap<
        (LocalDefId, rustc_middle::mir::Local),
        FxHashSet<rustc_middle::mir::Local>,
    > = FxHashMap::default();
    // Does `inner`'s value derive from `outer`'s object (inclusion, not a
    // shared ancestor: the review's HIGH-2)?
    let mut derives = |function: LocalDefId, inner: HirId, outer: HirId| -> bool {
        let (Some(inner), Some(outer)) = (
            mir_local_of(tcx, function, inner, &local_of),
            mir_local_of(tcx, function, outer, &local_of),
        ) else {
            return false;
        };
        sources
            .entry((function, inner))
            .or_insert_with(|| strict_sources(tcx, function, inner))
            .contains(&outer)
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
            let expressions = call_arguments(tcx, call.caller, call.span);
            let expression = |index: usize| expressions.and_then(|arguments| arguments.get(index));
            // An argument naming its root's whole object (no field projection on
            // the way); unknown text reads as whole (the conservative side).
            let whole = |index: usize| expression(index).is_none_or(|expr| !projects_field(expr));
            // The seam consults its aliased-storage twin only at a call no PAIR
            // row owns (`seam.rs`'s `pair_owned_call`; the review's HIGH-1).
            let seam_pair_owned = pair_sites.iter().any(|pair| {
                pair.caller == call.caller
                    && pair.callee == callee
                    && pair
                        .call_span
                        .source_callsite()
                        .contains(call.span.source_callsite())
                    && match pair.role {
                        PairRole::Clear | PairRole::Primary | PairRole::RawView => true,
                        PairRole::Blocked => false,
                    }
            });
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
                    let edge = pair_edge(
                        pair_sites,
                        call.caller,
                        callee,
                        call.span,
                        left.index,
                        right.index,
                    );
                    // The PAIR answers this pair with its raw view; the counted-void
                    // family routes a call whose two positions it counts (split with
                    // a proof, else the pristine raw twin): their answers stand.
                    if matches!(edge, Edge::Ordered)
                        || (super::counted_void::contract_at(table, callee, left.index).is_some()
                            && super::counted_void::contract_at(table, callee, right.index)
                                .is_some())
                    {
                        continue;
                    }
                    let relation = match (
                        object_of(tcx, call.caller, left, expression(left.index)),
                        object_of(tcx, call.caller, right, expression(right.index)),
                    ) {
                        (Object::Null, _) | (_, Object::Null) => Relation::Disjoint,
                        (Object::Static(a), Object::Static(b)) => {
                            if a == b {
                                Relation::SameStatic
                            } else {
                                Relation::Disjoint
                            }
                        }
                        (Object::Static(_), Object::Frame(_))
                        | (Object::Frame(_), Object::Static(_)) => Relation::Disjoint,
                        (Object::Static(_), _) | (_, Object::Static(_)) => Relation::Unresolved,
                        // One binding at both positions, at least one of them its
                        // whole object (two field places under one root are the
                        // PAIR's field rule; the review's MED-4).
                        (Object::Frame(a), Object::Frame(b))
                        | (Object::Pointee(a), Object::Pointee(b))
                            if a == b =>
                        {
                            if whole(left.index) || whole(right.index) {
                                Relation::Same
                            } else {
                                Relation::Unknown
                            }
                        }
                        (Object::Frame(_), Object::Frame(_)) => Relation::Disjoint,
                        // One argument's value derives from the other's object, the
                        // outer one taken whole (`&mut *s` beside `br = &mut (*s).br`).
                        (Object::Pointee(a), Object::Pointee(b))
                            if (whole(right.index) && derives(call.caller, a, b))
                                || (whole(left.index) && derives(call.caller, b, a)) =>
                        {
                            Relation::Contained
                        }
                        (Object::Frame(frame), Object::Pointee(pointer))
                            if whole(left.index) && derives(call.caller, pointer, frame) =>
                        {
                            Relation::Contained
                        }
                        (Object::Pointee(pointer), Object::Frame(frame))
                            if whole(right.index) && derives(call.caller, pointer, frame) =>
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
                    let certified = matches!(edge, Edge::CertifiedClear);
                    let why = match relation {
                        Relation::Disjoint | Relation::Unknown => continue,
                        // One local at two positions of a call no PAIR row owns is
                        // the seam's aliased-storage twin (a raw twin, or the call
                        // held): R408-7, wave-6v.
                        Relation::Same if !seam_pair_owned => continue,
                        Relation::Same | Relation::SameStatic | Relation::Contained
                            if certified =>
                        {
                            continue;
                        }
                        Relation::Same => "same-subject".to_owned(),
                        Relation::SameStatic => "same-static".to_owned(),
                        Relation::Contained => "contained".to_owned(),
                        Relation::Unresolved if kind == "ref-beside-ref" => continue,
                        Relation::Unresolved
                            if matches!(
                                (expression(left.index), expression(right.index)),
                                (Some(l), Some(r))
                                    if super::counted_void::disjoint_roots(tcx, call.caller, l, r)
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
