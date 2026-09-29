//! Thin references at multi-element foreign positions (seat rulings R272-1 and
//! R280-1, route (A)).
//!
//! A thin `&T` carries provenance for exactly ONE element. A foreign position
//! whose contract consumes more than one — `strlen(s)` reading to the NUL,
//! `strncpy(dest, src, n)` reading up to `n`, `snprintf(buf, len, ..)` writing
//! up to `len` — is handed that one-element claim and accesses past it. That is
//! the same Stacked-Borrows violation `&c_void` commits, with a typed pointee
//! instead of an opaque one: the retag covers one element and the callee reads
//! or writes beyond it. Miri confirms it on the `strlen` shape (R272-1(d)).
//!
//! **The predicate is the contract's extent, not a symbol list.** The counted
//! family this started as — `memcpy`, `strncpy`, `snprintf` — is four of the 88
//! census sites; 80 are NUL-terminated, where no length exists at the call at
//! all. Both are the same defect, so both are held, and the classification
//! lives in ONE place: the extent column of the pinned contract table
//! (`raw_boundary_contracts::ArgumentExtent`). A symbol list here would be a
//! second table that could drift from the first.
//!
//! What is deliberately NOT held:
//!
//! - **Slices and Options of slices.** A slice carries `len · size_of::<T>()`,
//!   which is an extent; the rule is about extent, not about references. The
//!   hold therefore sits at the thin-`Ref` return, below every arm that yields
//!   a form carrying its own extent, and below the owning arm for the reason
//!   R271-1 recorded (a void allocation becomes `Box<[u8]>` with a real byte
//!   count).
//! - **`one-element` and `lifecycle` positions.** One element is exactly what a
//!   thin reference carries; a lifecycle position accesses no elements.
//! - **Unmodeled foreign positions.** No contract row means no extent claim,
//!   and inventing one would hold on absence of evidence.
//! - **Local callees.** `foreign_call_args` carries foreign positions only, and
//!   a local callee's parameter is a subject in its own right.

use rustc_hash::FxHashSet;
use rustc_hir::{HirId, def_id::LocalDefId};
use rustc_middle::ty::TyCtxt;

use super::{
    emitability::{ArgShape, EmitabilityFacts},
    raw_boundary_contracts::classify_contract,
};

/// Does this exact foreign position consume more than one element?
///
/// Answered by the pinned contract table, so a position's extent is stated once
/// and read here. A position with no row, or one whose row does not apply at
/// this target type, answers `false`: absence of a contract is not evidence of
/// a multi-element access.
pub(crate) fn position_consumes_many_elements(
    callee: &super::raw_boundary::ForeignSymbolKey,
    argument_index: usize,
    target: &super::raw_boundary::RawTargetType,
) -> bool {
    classify_contract(callee, argument_index, target)
        .is_ok_and(|contract| !contract.extent.fits_one_element())
}

/// A byte count that spells the pointee's OWN size — `memset(p, 0,
/// size_of::<T>())` on a `*mut T` — is exactly one element: the claim a thin
/// reference carries. Read from the count operand's spelling beneath its
/// casts, against the operand's own pointee (a `c_void` position types the
/// argument, not the row). Anything else at a `ByteCount` position keeps the
/// row's multi-element extent.
///
/// The two forms are compared on the type's FINAL PATH SEGMENT, which is all
/// they can share: the pointee is a printed type, carrying the path from the
/// crate root (`src::libtree::small_vec_u64_t`), while the count is the source
/// text of `size_of::<..>()`, which names the type as the call's own module
/// sees it (`small_vec_u64_t`). Measured at batch 8: with a whole-path
/// comparison the refinement missed every corpus site and libtree's
/// `small_vec_u64_init::v#1` lost its delivery.
pub(crate) fn byte_count_is_one_element(fact: &super::raw_boundary::ForeignCallArgFact) -> bool {
    fact.contract_count
        .as_ref()
        .is_some_and(|count| count.one_pointee)
}

/// Subjects that reach such a position. A subject in this set may not take a
/// THIN reference form.
///
/// **wave-6l (R641): a NUL walk directly, or through a local callee's
/// parameter.** A subject handed, bare or under casts, to a local callee
/// parameter that reaches a NUL-terminated position reaches the same walk one
/// call deeper: brotli's `CopyStat(input_path)` calls C2Rust's local copy of
/// glibc's inline `stat(p, b) { __xstat(1, p, b) }`, and the NUL walk is
/// `__xstat`'s. Followed to a fixpoint, so a chain of such forwarders is one
/// fact. A counted footprint behind a local callee is
/// `local_callee_extent`'s contract arm, not this set's.
///
/// A parameter with pointer arithmetic of its own (`offset`, `add`, … but
/// not C's `p[0]` in place) does not carry the walk to its callers: its extent
/// is its own, and a thin caller of it is `local_callee_extent`'s (a raw
/// callee: `pointer-arithmetic`, the same test) or main's
/// one-element-into-wider guard's (a slice callee, R365-2). **A model-`Raw`
/// callee does carry it** (Codex 062 finding 1): keeping the callee raw does
/// not protect a caller that converts, and wave-4's CE-D06 emitted exactly
/// that, `find(name: &mut i8)` into `find_local`'s `strcmp`.
pub(crate) fn collect(tcx: TyCtxt<'_>, facts: &EmitabilityFacts) -> FxHashSet<(LocalDefId, HirId)> {
    // The arithmetic gate is a PARAMETER's: its thin callers are the local
    // callee hold's, so the gate is that hold's own arithmetic test (relay 064
    // review: C's `p[0]` in place carries the walk, as the hold exempts it). A
    // LOCAL copy that steps (`q = q.offset(1)`) before the walk carries it on
    // to its source (the line A review).
    let carries = |(function, binding): (LocalDefId, HirId)| {
        let parameter = tcx.hir_node_by_def_id(function).body_id().is_some_and(|_| {
            tcx.hir_body_owned_by(function)
                .params
                .iter()
                .any(|param| param.pat.hir_id == binding)
        });
        !parameter
            || !super::local_callee_extent::leaves_its_extent(tcx, (function, binding), facts)
    };
    let mut out = FxHashSet::default();
    let mut walked = FxHashSet::default();
    for fact in &facts.foreign_call_args {
        if !position_consumes_many_elements(&fact.callee, fact.argument_index, &fact.target)
            || byte_count_is_one_element(fact)
        {
            continue;
        }
        if let Some(root) = fact.direct_subject_root() {
            out.insert((fact.caller, root));
            if classify_contract(&fact.callee, fact.argument_index, &fact.target).is_ok_and(
                |contract| {
                    contract.extent == super::raw_boundary_contracts::ArgumentExtent::NulTerminated
                },
            ) && carries((fact.caller, root))
            {
                walked.insert((fact.caller, root));
            }
        }
    }
    // Relay 063 (R645-5 item 3): a copy of a binding into a local (`let q =
    // p;`, `q = p;`, under casts) reaches whatever the local reaches. Walked
    // backward in the same fixpoint: a many-element position holds the copy's
    // source, and a NUL walk carries on to its callers.
    let copies = copy_edges(tcx);
    loop {
        let mut grew = false;
        for &(function, copy, source) in &copies {
            if out.contains(&(function, copy)) {
                grew |= out.insert((function, source));
            }
            if walked.contains(&(function, copy)) && carries((function, source)) {
                grew |= walked.insert((function, source));
            }
        }
        for (callee, sites) in &facts.call_args {
            if tcx.hir_node_by_def_id(*callee).body_id().is_none() {
                continue;
            }
            let params = tcx.hir_body_owned_by(*callee).params;
            for site in sites {
                for arg in &site.args {
                    let (ArgShape::BareLocal(root) | ArgShape::CastOfLocal { binding: root, .. }) =
                        arg.shape
                    else {
                        continue;
                    };
                    let Some(param) = params.get(arg.index) else {
                        continue;
                    };
                    if walked.contains(&(*callee, param.pat.hir_id)) {
                        grew |= out.insert((site.caller, root));
                        if carries((site.caller, root)) {
                            grew |= walked.insert((site.caller, root));
                        }
                    }
                }
            }
        }
        if !grew {
            return out;
        }
    }
}

/// `(function, copy, source)` for every `let copy = source;` and
/// `copy = source;` in the program: the source a bare local under casts, or
/// every arm of an `if` / `match` / block that yields one (C2Rust's ternary).
/// Every body owner is its own function, closures included, as the facts
/// key them.
fn copy_edges(tcx: TyCtxt<'_>) -> Vec<(LocalDefId, HirId, HirId)> {
    copy_edges_of(tcx, tcx.hir_body_owners())
}

/// The copy edges of one body, `(copy, source)` (relay 065: the local callee
/// hold reads a parameter's copies).
pub(super) fn copy_edges_in(tcx: TyCtxt<'_>, function: LocalDefId) -> Vec<(HirId, HirId)> {
    copy_edges_of(tcx, std::iter::once(function))
        .into_iter()
        .map(|(_, copy, source)| (copy, source))
        .collect()
}

fn copy_edges_of(
    tcx: TyCtxt<'_>,
    owners: impl Iterator<Item = LocalDefId>,
) -> Vec<(LocalDefId, HirId, HirId)> {
    use rustc_hir::{
        Expr, ExprKind, LetStmt, PatKind, QPath,
        def::Res,
        intravisit::{self, Visitor},
    };
    fn sources(mut e: &Expr<'_>, out: &mut Vec<HirId>) {
        while let ExprKind::Cast(inner, _) | ExprKind::DropTemps(inner) = e.kind {
            e = inner;
        }
        match e.kind {
            ExprKind::Path(QPath::Resolved(_, path)) => {
                if let Res::Local(id) = path.res {
                    out.push(id);
                }
            }
            ExprKind::If(_, then, otherwise) => {
                sources(then, out);
                if let Some(otherwise) = otherwise {
                    sources(otherwise, out);
                }
            }
            ExprKind::Match(_, arms, _) => {
                for arm in arms {
                    sources(arm.body, out);
                }
            }
            ExprKind::Block(block, _) => {
                if let Some(tail) = block.expr {
                    sources(tail, out);
                }
            }
            _ => {}
        }
    }
    fn local_of(e: &Expr<'_>) -> Option<HirId> {
        let mut found = Vec::new();
        sources(e, &mut found);
        (found.len() == 1).then(|| found[0])
    }
    struct Copies {
        function: LocalDefId,
        edges: Vec<(LocalDefId, HirId, HirId)>,
    }
    impl<'tcx> Visitor<'tcx> for Copies {
        fn visit_local(&mut self, local: &'tcx LetStmt<'tcx>) {
            if let PatKind::Binding(_, copy, _, None) = local.pat.kind
                && let Some(init) = local.init
            {
                let mut found = Vec::new();
                sources(init, &mut found);
                for source in found {
                    self.edges.push((self.function, copy, source));
                }
            }
            intravisit::walk_local(self, local);
        }

        fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
            if let ExprKind::Assign(left, right, _) = e.kind
                && let Some(copy) = local_of(left)
            {
                let mut found = Vec::new();
                sources(right, &mut found);
                for source in found {
                    self.edges.push((self.function, copy, source));
                }
            }
            intravisit::walk_expr(self, e);
        }
    }
    let mut copies = Copies {
        function: rustc_hir::def_id::CRATE_DEF_ID,
        edges: Vec::new(),
    };
    for owner in owners {
        copies.function = owner;
        copies.visit_body(tcx.hir_body_owned_by(owner));
    }
    copies.edges
}
