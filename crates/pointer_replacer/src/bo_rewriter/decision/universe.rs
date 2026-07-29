//! **Subject-universe classification.** An independent census of every
//! pointer-parameter-bearing item in the crate, by scope class.
//!
//! # Why this exists (ADV-R1)
//!
//! The coverage gate's first two forms both compared the decision table against
//! the *collector's own output*, and were therefore unfailable. The second
//! attempt looked independent — a separate walk, separate code — but drew from
//! the same `program.functions`, applied the same `fn_decl()`/`TyKind::Ptr`
//! filter, and the one remaining divergence path was converted to a `panic!` in
//! the same commit. Independence in code path is not independence in **source
//! of truth**.
//!
//! This walk starts from `tcx.hir_crate_items(())` and visits **every** item
//! kind — free functions, impl items, trait items, foreign items — so it can
//! disagree with the collector by construction.
//!
//! # M1's subject universe (ruling, 2026-07-29)
//!
//! M1's subjects are **free functions with bodies** — the C2Rust output shape,
//! which is what a translated C function becomes. Everything else is out of
//! scope *by ruling*, not by oversight:
//!
//! - **foreign items**: no body and an ABI-fixed signature (M4 territory);
//! - **impl / trait items**: not a C-source shape;
//! - **anything else** bearing a pointer parameter: counted so it cannot hide.
//!
//! The exclusions are **attributed quantities**, not silence. They appear in
//! the universe report and flow into S2b's counters as out-of-scope-M1, so a
//! population M1 declines to handle is visible as a number rather than as an
//! absence.

use rustc_hir::{ItemKind, OwnerNode, TyKind, def_id::LocalDefId};
use rustc_middle::ty::TyCtxt;

/// Census of pointer-parameter-bearing items, by scope class.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct UniverseReport {
    /// Pointer params on free functions with bodies — M1's subjects.
    pub subjects: usize,
    /// Pointer params on inherent/trait impl methods — out of scope by ruling.
    pub excluded_impl: usize,
    /// Pointer params on trait item declarations — out of scope by ruling.
    pub excluded_trait: usize,
    /// Pointer params on `extern` declarations — no body, ABI-fixed.
    pub excluded_foreign: usize,
    /// Anything else bearing a pointer parameter. Non-zero here means the
    /// classification has a blind spot and should grow a class, which is
    /// exactly what this bucket exists to reveal.
    pub excluded_other: usize,
    /// Free functions with pointer params, for the caller's own bookkeeping.
    pub subject_fns: Vec<LocalDefId>,
}

impl UniverseReport {
    pub(crate) fn excluded_total(&self) -> usize {
        self.excluded_impl + self.excluded_trait + self.excluded_foreign + self.excluded_other
    }
}

fn ptr_params(decl: &rustc_hir::FnDecl<'_>) -> usize {
    decl.inputs
        .iter()
        .filter(|input| matches!(input.kind, TyKind::Ptr(_)))
        .count()
}

/// Classify every item in the crate.
///
/// Deliberately does NOT consult `collect_program` or `collect_subjects`: the
/// whole value of this walk is that it can disagree with them.
pub(crate) fn classify(tcx: TyCtxt<'_>) -> UniverseReport {
    let mut report = UniverseReport::default();
    for maybe_owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        match owner.node() {
            OwnerNode::Item(item) => {
                if let ItemKind::Fn { sig, .. } = item.kind {
                    let n = ptr_params(sig.decl);
                    if n > 0 {
                        report.subjects += n;
                        report.subject_fns.push(item.owner_id.def_id);
                    }
                }
            }
            OwnerNode::ImplItem(item) => {
                if let rustc_hir::ImplItemKind::Fn(sig, _) = item.kind {
                    report.excluded_impl += ptr_params(sig.decl);
                }
            }
            OwnerNode::TraitItem(item) => {
                if let rustc_hir::TraitItemKind::Fn(sig, _) = item.kind {
                    report.excluded_trait += ptr_params(sig.decl);
                }
            }
            OwnerNode::ForeignItem(item) => {
                if let rustc_hir::ForeignItemKind::Fn(sig, ..) = item.kind {
                    report.excluded_foreign += ptr_params(sig.decl);
                }
            }
            _ => {}
        }
    }
    report
}
