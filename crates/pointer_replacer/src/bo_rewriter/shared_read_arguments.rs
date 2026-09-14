//! Realize native read/read address operators, including in raw callers.

use rustc_ast::{
    BorrowKind, ExprKind, Mutability,
    mut_visit::{self, MutVisitor},
};
use rustc_span::Span;

use super::{
    ast_transform::{Composition, RevertSet},
    decision::DecisionTable,
};

pub(super) fn apply(
    table: &DecisionTable,
    reverts: &RevertSet,
    krate: &mut rustc_ast::Crate,
    guard: &mut Composition,
) -> Result<(), String> {
    let mut sites = rustc_hash::FxHashMap::<Span, Span>::default();
    for call in &table.seams.shared_read_calls {
        let active = call
            .subjects
            .iter()
            .filter(|&&hir| reverts.keeps_subject(call.callee, hir))
            .count();
        if active == 0 {
            continue;
        }
        if active != call.subjects.len() {
            return Err("shared-read-partial-callee-withdrawal".into());
        }
        for address in &call.addresses {
            if sites.insert(address.argument, address.place).is_some() {
                return Err("shared-read-address-duplicate".into());
            }
        }
    }
    struct Apply<'a> {
        sites: rustc_hash::FxHashMap<Span, Span>,
        guard: &'a mut Composition,
        failure: Option<&'static str>,
    }
    impl MutVisitor for Apply<'_> {
        fn visit_expr(&mut self, expr: &mut rustc_ast::Expr) {
            mut_visit::walk_expr(self, expr);
            let Some(place_span) = self.sites.remove(&expr.span) else {
                return;
            };
            let ExprKind::AddrOf(BorrowKind::Ref, permission, place) = &mut expr.kind else {
                self.failure = Some("shared-read-address-shape-changed");
                return;
            };
            if place.span != place_span {
                self.failure = Some("shared-read-address-place-changed");
                return;
            }
            if *permission == Mutability::Not {
                return;
            }
            if !self
                .guard
                .claim(expr.id, expr.span, "native-shared-read-address")
            {
                self.failure = Some("shared-read-address-collision");
                return;
            }
            *permission = Mutability::Not;
        }
    }
    let mut apply = Apply {
        sites,
        guard,
        failure: None,
    };
    apply.visit_crate(krate);
    if let Some(reason) = apply.failure {
        return Err(reason.into());
    }
    if !apply.sites.is_empty() {
        return Err("shared-read-address-unmatched".into());
    }
    Ok(())
}

/// Caller withdrawal does not own these operators. Partial callee retirement
/// does: restore its complete original signature and argument construction.
pub(super) fn close_reverts(table: &DecisionTable, reverts: &mut RevertSet) {
    for call in &table.seams.shared_read_calls {
        if call
            .subjects
            .iter()
            .any(|&subject| !reverts.keeps_subject(call.callee, subject))
        {
            reverts.fns.insert(call.callee);
        }
    }
}

/// The text planner and common class receipts own the same address-prefix
/// edit as the structural consumer. The pointee expression remains untouched.
pub(super) fn plan(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    table: &DecisionTable,
    reverted: &rustc_hash::FxHashSet<rustc_hir::def_id::LocalDefId>,
    plan: &mut super::plan::Plan,
    locate: impl Fn(Span) -> Result<(super::plan::FileKey, usize, usize), &'static str>,
) -> Result<(), String> {
    use super::{
        bridge_receipt::{BridgeSitePlan, SignatureClassId},
        plan::{Edit, Justification},
    };
    for call in &table.seams.shared_read_calls {
        if reverted.contains(&call.callee) {
            continue;
        }
        for address in &call.addresses {
            let prefix = address.argument.with_hi(address.place.lo());
            let (file, lo, hi) =
                locate(prefix).map_err(|why| format!("shared-read-address-unplaceable:{why}"))?;
            let mut bridge = BridgeSitePlan::local(
                call.caller,
                call.callee,
                super::decision::Arm::Pair.key(),
                format!("arg:{}", address.index),
                "native-shared-read-address",
            );
            bridge.expected_form = "ref-shared".into();
            bridge.found_form = "ref-mut".into();
            bridge.argument_kind = "pure-field-address".into();
            plan.by_file.entry(file).or_default().push(Edit {
                lo,
                hi,
                replacement: "&".into(),
                justification: Justification::SeamAdapter {
                    family: "safe",
                    fabricated: false,
                },
                owner_class: Some(SignatureClassId::of(call.callee)),
                owner_path: tcx.def_path_str(call.callee.to_def_id()),
                bridge: Some(bridge),
                atom_ids: Vec::new(),
                subject_id: format!("shared-read-arg:{}", address.index),
                required_arms: super::decision::Arm::Pair.key().into(),
                edit_kind: "native-shared-read-address",
            });
        }
    }
    Ok(())
}
