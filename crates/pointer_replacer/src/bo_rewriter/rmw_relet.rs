//! **R1130-1 (USER; relay wave-6a/164) — the read-modify-write temporary,
//! restored.** c2rust writes a read-modify-write through a raw pointer as
//! `let ref mut fresh0 = PLACE; *fresh0 = RHS;` and the preprocessor inlines it
//! ("Remove `let ref`", `crates/passes/src/preprocessor.rs`) into
//! `PLACE = RHS` / `PLACE op= RHS`, which names the raw place twice. Where the
//! place's root stays raw in the emitted program, this pass puts c2rust's
//! temporary back:
//!
//! ```text
//! (*a).used = ((*a).used).wrapping_sub(1)
//!   =>  { let __crat_fresh_0 = &mut (*a).used; *__crat_fresh_0 = (*__crat_fresh_0).wrapping_sub(1); }
//! *p.offset(i) += 1
//!   =>  { let __crat_fresh_1 = &mut *p.offset(i); *__crat_fresh_1 += 1; }
//! ```
//!
//! Emission only, behind `CRAT_RMW_RELET=on` (default off); it runs after every
//! other AST pass, so no decision and no planned edit is touched. The rule:
//! - a statement `PLACE = RHS` whose RHS mentions PLACE, or `PLACE op= RHS`;
//! - PLACE is a place (fields, indexing, `offset`-family steps, parentheses)
//!   with a dereference in its projection, rooted at a local or formal that is a
//!   raw pointer AS EMITTED: raw in the input, and not delivered in a safe form
//!   (degraded, not a subject, or its class reverted);
//! - the RHS, outside the occurrences of PLACE, contains no call (the integer
//!   methods aside) and no side effect (no assignment, compound assignment,
//!   block, control flow, macro or borrow). Reads of anything are allowed
//!   (R1160-1: the model of record is Tree Borrows, where a foreign read keeps
//!   the unprotected `&mut` Reserved and the write through it then activates
//!   it; reports 165b / 165d's Miri TB runs). A call is refused because a
//!   callee may WRITE the place through another pointer, which disables the
//!   reference; with no side effect, the place's earlier evaluation changes
//!   nothing;
//! - no field step names a field of a `packed` struct (`&mut` of a packed
//!   field is E0793; by name, conservatively);
//! - skipped and counted: an index or step argument containing a call (c2rust
//!   hoisted those itself), a root that cannot be resolved to a local.
//!
//! A function the compile check reverted keeps its text (R1160-1), and a
//! round in which EVERY class is withheld is left alone (R216).
//!
//! Semantics: the reference lives for one statement, over the very place the
//! input reads and writes; `&mut PLACE` of a raw place is the input's own
//! pattern before preprocessing.

use rustc_ast::{
    AssignOpKind, Expr, ExprKind, StmtKind, UnOp,
    mut_visit::{self, MutVisitor},
};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{HirId, def::Res, def_id::LocalDefId, intravisit};

use super::decision::{Decision, DecisionTable};

/// The switch `CRAT_RMW_RELET`: `on` applies the pass; anything else (the
/// default, absent) leaves the emission as it was.
pub(crate) fn enabled() -> bool {
    std::env::var("CRAT_RMW_RELET").as_deref() == Ok("on")
}

/// A test crate opts in by defining an item of this name: the switch is
/// process-global state, and the suite runs in parallel.
#[cfg(test)]
pub(crate) const TEST_MARKER: &str = "__crat_rmw_relet_test";

/// Deliberate faults for the witness test (`rmw_relet_tests`), test builds only.
#[cfg(test)]
pub(crate) static FAULT: std::sync::atomic::AtomicU8 = std::sync::atomic::AtomicU8::new(0);

#[cfg(test)]
fn fault(n: u8) -> bool {
    FAULT.load(std::sync::atomic::Ordering::SeqCst) == n
}

#[cfg(not(test))]
fn fault(_: u8) -> bool {
    false
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct RmwStats {
    /// Statements re-let.
    pub(crate) relet: usize,
    /// Skipped: an index or step argument contains a call.
    pub(crate) skipped_call_index: usize,
    /// Skipped: the root is not a local the HIR resolves (a grafted node, a static).
    pub(crate) skipped_unresolved: usize,
    /// Not applied: the root is delivered in a safe form.
    pub(crate) safe_root: usize,
    /// Not applied: another edit already claims the statement.
    pub(crate) claimed: usize,
    /// Not applied: the function is reverted by the compile check.
    pub(crate) reverted: usize,
    /// Not applied (R1160-1): the RHS calls or has a side effect.
    pub(crate) rhs_touches_memory: usize,
    /// Not applied: a field step names a field of a `packed` struct.
    pub(crate) packed: usize,
}

/// Apply the pass to the emitted crate (after every other AST pass).
pub(crate) fn apply(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    table: &DecisionTable,
    reverts: &super::ast_transform::RevertSet,
    krate: &mut rustc_ast::Crate,
    guard: &mut super::ast_transform::Composition,
) -> RmwStats {
    let mut on = enabled() && !fault(5);
    #[cfg(test)]
    {
        on = on
            || (!fault(5)
                && krate
                    .items
                    .iter()
                    .any(|item| item.kind.ident().is_some_and(|i| i.as_str() == TEST_MARKER)));
    }
    if !on {
        return RmwStats::default();
    }
    // R216: a crate whose EVERY class is withheld keeps its input bytes (the
    // revert-all identity), so that round is left alone. A withheld class in
    // an otherwise kept crate is still emitted text, and its raw places are
    // as raw as anywhere: libzahl's fully raw functions are such classes.
    if table.entries.iter().all(|(subject, _)| {
        !reverts.keeps(super::bridge_receipt::SignatureClassId::of(subject.fn_did))
    }) {
        return RmwStats::default();
    }
    let roots = root_locals(tcx);
    let decisions: FxHashMap<(LocalDefId, HirId), &Decision> = table
        .entries
        .iter()
        .map(|(subject, decision)| ((subject.fn_did, subject.hir_id), decision))
        .collect();
    let raw_root = |owner: LocalDefId, local: HirId| -> bool {
        if fault(1) {
            return true;
        }
        let input_raw = tcx.typeck(owner).node_type(local).is_raw_ptr();
        if !input_raw {
            return false;
        }
        // Exhaustive by rule (`import_denylist`).
        match decisions.get(&(owner, local)) {
            None | Some(Decision::Degraded(_)) => true,
            Some(
                Decision::Ref { .. }
                | Decision::InferredRef { .. }
                | Decision::Slice { .. }
                | Decision::NestedSlice { .. }
                | Decision::Cursor { .. }
                | Decision::Opt { .. }
                | Decision::Box(_),
            ) => !reverts.keeps_subject(owner, local),
        }
    };
    let kept = |owner: LocalDefId| !reverts.fns.contains(&owner);
    let packed = packed_field_names(tcx);
    let mut pass = Relet {
        roots: &roots,
        raw_root: &raw_root,
        kept: &kept,
        packed: &packed,
        guard,
        stats: RmwStats::default(),
        next: 0,
    };
    pass.visit_crate(krate);
    pass.stats
}

/// Every HIR path expression resolving to a local, by its source span:
/// `(lo, hi) -> (owner, the binding's HirId)`.
fn root_locals(tcx: rustc_middle::ty::TyCtxt<'_>) -> FxHashMap<(u32, u32), (LocalDefId, HirId)> {
    struct Paths<'tcx> {
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
        owner: LocalDefId,
        out: FxHashMap<(u32, u32), (LocalDefId, HirId)>,
    }
    impl<'tcx> intravisit::Visitor<'tcx> for Paths<'tcx> {
        type NestedFilter = rustc_middle::hir::nested_filter::OnlyBodies;

        fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
            self.tcx
        }

        fn visit_expr(&mut self, e: &'tcx rustc_hir::Expr<'tcx>) {
            if let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(None, path)) = e.kind
                && let Res::Local(local) = path.res
            {
                self.out
                    .insert((e.span.lo().0, e.span.hi().0), (self.owner, local));
            }
            intravisit::walk_expr(self, e);
        }
    }
    let mut out = FxHashMap::default();
    for owner in tcx.hir_body_owners() {
        let body = tcx.hir_body_owned_by(owner);
        let mut paths = Paths {
            tcx,
            owner,
            out: FxHashMap::default(),
        };
        intravisit::Visitor::visit_body(&mut paths, body);
        out.extend(paths.out);
    }
    out
}

struct Relet<'a, F: Fn(LocalDefId, HirId) -> bool> {
    roots: &'a FxHashMap<(u32, u32), (LocalDefId, HirId)>,
    raw_root: &'a F,
    /// The function is not reverted by the compile check.
    kept: &'a dyn Fn(LocalDefId) -> bool,
    /// Field names of the crate's `packed` structs.
    packed: &'a FxHashSet<String>,
    /// The emitter reprints a function only where a claimed span lies in it.
    guard: &'a mut super::ast_transform::Composition,
    stats: RmwStats,
    next: usize,
}

/// Does `e` contain a call or a method call?
fn contains_call(e: &Expr) -> bool {
    struct Calls(bool);
    impl<'a> rustc_ast::visit::Visitor<'a> for Calls {
        fn visit_expr(&mut self, e: &'a Expr) {
            if matches!(e.kind, ExprKind::Call(..) | ExprKind::MethodCall(..)) {
                self.0 = true;
            }
            rustc_ast::visit::walk_expr(self, e);
        }
    }
    let mut calls = Calls(false);
    rustc_ast::visit::Visitor::visit_expr(&mut calls, e);
    calls.0
}

enum Place<'e> {
    /// The root path expression, with whether a dereference was crossed.
    Rooted(&'e Expr, bool),
    CallInIndex,
    NotAPlace,
}

/// Walk a place to its root: fields, indexing, `offset`-family steps,
/// parentheses, dereferences.
fn place_root(mut e: &Expr) -> Place<'_> {
    let mut deref = false;
    loop {
        e = match &e.kind {
            ExprKind::Field(base, _) | ExprKind::Paren(base) => base,
            ExprKind::Unary(UnOp::Deref, base) => {
                deref = true;
                base
            }
            ExprKind::Index(base, index, _) => {
                if contains_call(index) && !fault(3) {
                    return Place::CallInIndex;
                }
                base
            }
            ExprKind::MethodCall(call)
                if matches!(
                    call.seg.ident.as_str(),
                    "offset" | "add" | "sub" | "wrapping_offset" | "wrapping_add" | "wrapping_sub"
                ) =>
            {
                if call.args.iter().any(|a| contains_call(a)) && !fault(3) {
                    return Place::CallInIndex;
                }
                &call.receiver
            }
            ExprKind::Path(None, path) if path.segments.len() == 1 => {
                return Place::Rooted(e, deref);
            }
            _ => return Place::NotAPlace,
        };
    }
}

/// The field names of the crate's `#[repr(packed)]` structs and unions.
fn packed_field_names(tcx: rustc_middle::ty::TyCtxt<'_>) -> FxHashSet<String> {
    tcx.hir_crate_items(())
        .definitions()
        .filter(|&did| {
            matches!(
                tcx.def_kind(did),
                rustc_hir::def::DefKind::Struct | rustc_hir::def::DefKind::Union
            )
        })
        .map(|did| tcx.adt_def(did))
        .filter(|adt| adt.repr().packed())
        .flat_map(|adt| {
            adt.all_fields()
                .map(|f| f.name.to_string())
                .collect::<Vec<_>>()
        })
        .collect()
}

/// Does a field step of the place name a field of a `packed` struct?
fn names_packed_field(place: &Expr, packed: &FxHashSet<String>) -> bool {
    let mut e = place;
    loop {
        e = match &e.kind {
            ExprKind::Field(base, field) => {
                if packed.contains(field.as_str()) {
                    return true;
                }
                base
            }
            ExprKind::Paren(base)
            | ExprKind::Unary(UnOp::Deref, base)
            | ExprKind::Index(base, ..) => base,
            ExprKind::MethodCall(call) => &call.receiver,
            _ => return false,
        };
    }
}

/// **R1160-1.** Does `rhs`, outside the occurrences of the place itself,
/// contain no call (the integer methods aside) and no side effect? Reads are
/// allowed: under Tree Borrows a foreign read keeps the unprotected `&mut`
/// temporary Reserved. A call may write the place through another pointer (a
/// foreign write disables the temporary); an assignment, a block, control flow,
/// a macro or a borrow is refused with it.
fn rhs_reads_only(rhs: &Expr, place: &str) -> bool {
    struct Reads<'p> {
        place: &'p str,
        ok: bool,
    }
    impl<'a> rustc_ast::visit::Visitor<'a> for Reads<'_> {
        fn visit_expr(&mut self, e: &'a Expr) {
            if !self.ok || pprust::expr_to_string(e) == self.place {
                return;
            }
            match &e.kind {
                ExprKind::Lit(_)
                | ExprKind::Paren(_)
                | ExprKind::Binary(..)
                | ExprKind::Unary(..)
                | ExprKind::Cast(..)
                | ExprKind::Index(..)
                | ExprKind::Field(..)
                | ExprKind::Path(..) => {}
                // Integer methods and the pointer step `offset` (address
                // arithmetic): no memory access, no user code.
                ExprKind::MethodCall(call)
                    if call.seg.ident.as_str().starts_with("wrapping_")
                        || matches!(
                            call.seg.ident.as_str(),
                            "offset"
                                | "rotate_left"
                                | "rotate_right"
                                | "swap_bytes"
                                | "to_be"
                                | "to_le"
                                | "count_ones"
                                | "leading_zeros"
                                | "trailing_zeros"
                        ) => {}
                _ => {
                    self.ok = false;
                    return;
                }
            }
            rustc_ast::visit::walk_expr(self, e);
        }
    }
    let mut reads = Reads { place, ok: true };
    rustc_ast::visit::Visitor::visit_expr(&mut reads, rhs);
    reads.ok || fault(6)
}

/// Replace every occurrence of `place` in `text` that is not part of a longer
/// identifier or field path by `*name` — bare where the occurrence is already
/// parenthesized (`((*a).used).wrapping_sub(1)` -> `(*fresh).wrapping_sub(1)`,
/// c2rust's own text), else as `(*name)`, so a method or field after it binds
/// to the place.
fn replace_place(text: &str, place: &str, name: &str) -> (String, usize) {
    let bare = format!("*{name}");
    let wrapped = format!("(*{name})");
    let mut out = String::with_capacity(text.len());
    let mut count = 0;
    let mut rest = text;
    while let Some(at) = rest.find(place) {
        let after = &rest[at + place.len()..];
        let continues = after
            .chars()
            .next()
            .is_some_and(|c| c.is_alphanumeric() || c == '_');
        let preceded = rest[..at]
            .chars()
            .next_back()
            .is_some_and(|c| c.is_alphanumeric() || c == '_' || c == '.');
        let in_parens = rest[..at].ends_with('(') && after.starts_with(')');
        out.push_str(&rest[..at]);
        if continues || preceded {
            out.push_str(place);
        } else {
            out.push_str(if in_parens { &bare } else { &wrapped });
            count += 1;
        }
        rest = after;
    }
    out.push_str(rest);
    (out, count)
}

impl<F: Fn(LocalDefId, HirId) -> bool> Relet<'_, F> {
    /// The re-let block for `stmt_expr`, or `None` where the rule does not apply.
    fn relet(&mut self, stmt_expr: &Expr) -> Option<Expr> {
        let (place, rhs, op) = match &stmt_expr.kind {
            ExprKind::Assign(place, rhs, _) => (place, rhs, None),
            ExprKind::AssignOp(op, place, rhs) => (place, rhs, Some(op.node)),
            _ => return None,
        };
        if op.is_some() && fault(4) {
            return None;
        }
        let root = match place_root(place) {
            // This pass's own temporaries (`*__crat_fresh_N = …`) are not re-let.
            Place::Rooted(root, true)
                if pprust::expr_to_string(root).starts_with("__crat_fresh_") =>
            {
                return None;
            }
            Place::Rooted(root, true) => root,
            Place::Rooted(_, false) | Place::NotAPlace => return None,
            Place::CallInIndex => {
                self.stats.skipped_call_index += 1;
                return None;
            }
        };
        let place_text = pprust::expr_to_string(place);
        let rhs_text = pprust::expr_to_string(rhs);
        let name = format!("__crat_fresh_{}", self.next);
        let (rhs_new, mentions) = replace_place(&rhs_text, &place_text, &name);
        if op.is_none() && mentions == 0 && !fault(2) {
            return None;
        }
        if !rhs_reads_only(rhs, &place_text) {
            self.stats.rhs_touches_memory += 1;
            return None;
        }
        if names_packed_field(place, self.packed) && !fault(7) {
            self.stats.packed += 1;
            return None;
        }
        if root.span.is_dummy() {
            self.stats.skipped_unresolved += 1;
            return None;
        }
        let Some(&(owner, local)) = self.roots.get(&(root.span.lo().0, root.span.hi().0)) else {
            self.stats.skipped_unresolved += 1;
            return None;
        };
        if !(self.kept)(owner) {
            self.stats.reverted += 1;
            return None;
        }
        if !(self.raw_root)(owner, local) {
            self.stats.safe_root += 1;
            return None;
        }
        let assign = match op {
            None => "=".to_owned(),
            Some(op) => assign_op(op).to_owned(),
        };
        let text = format!("{{ let {name} = &mut {place_text}; *{name} {assign} {rhs_new}; }}");
        let parsed = super::ast_transform::graft_expr(&text).ok()?;
        if !self.guard.claim(stmt_expr.id, stmt_expr.span, "rmw-relet") {
            self.stats.claimed += 1;
            return None;
        }
        self.next += 1;
        self.stats.relet += 1;
        Some(parsed)
    }
}

fn assign_op(op: AssignOpKind) -> &'static str {
    match op {
        AssignOpKind::AddAssign => "+=",
        AssignOpKind::SubAssign => "-=",
        AssignOpKind::MulAssign => "*=",
        AssignOpKind::DivAssign => "/=",
        AssignOpKind::RemAssign => "%=",
        AssignOpKind::BitXorAssign => "^=",
        AssignOpKind::BitAndAssign => "&=",
        AssignOpKind::BitOrAssign => "|=",
        AssignOpKind::ShlAssign => "<<=",
        AssignOpKind::ShrAssign => ">>=",
    }
}

impl<F: Fn(LocalDefId, HirId) -> bool> MutVisitor for Relet<'_, F> {
    fn visit_block(&mut self, block: &mut rustc_ast::Block) {
        for stmt in block.stmts.iter_mut() {
            if let StmtKind::Semi(expr) = &mut stmt.kind
                && let Some(relet) = self.relet(expr)
            {
                **expr = relet;
                continue;
            }
        }
        mut_visit::walk_block(self, block);
    }
}
