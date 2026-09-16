//! Unannotated slice locals with a sealed construction plan get an explicit
//! declaration: `let d = base.offset(k);` → `let d: &mut [T] = <construction>;`.
//! The value is item 2's own constructor (evidence-backed length or the §77
//! fallback with its receipt); only the missing splice target is supplied.

use rustc_hir::{Node, PatKind};
use rustc_middle::ty::{TyCtxt, TyKind};

use super::{Ctx, Decision, DeclShape, Subject, SubjectKind, construction, declaration, seam};
use crate::bo_rewriter::{additive::FamilyStage, bridge_receipt::SignatureClassId};

/// The declaration shape this rule supplies a type for: a plain by-value
/// binding of a raw pointer local, unannotated, with an initializer, whose
/// pointee can be named at the declaration.
pub(crate) fn emitted_type(tcx: TyCtxt<'_>, subject: &Subject, mutable: bool) -> Option<String> {
    if subject.kind != SubjectKind::Local
        || subject.ty_span.is_some()
        || subject.decl_shape != DeclShape::RawPtr
        || subject.ptr_depth != 1
        || subject.binding_span.from_expansion()
    {
        return None;
    }
    let Node::LetStmt(local) = tcx.parent_hir_node(subject.hir_id) else { return None };
    let PatKind::Binding(mode, hir, _, None) = local.pat.kind else { return None };
    if hir != subject.hir_id || mode.0 != rustc_hir::ByRef::No || local.ty.is_some() {
        return None;
    }
    let initializer = local.init?;
    if initializer.span.from_expansion() || call_initialised(initializer) {
        return None;
    }
    let typeck = tcx.typeck(subject.fn_did);
    let TyKind::RawPtr(pointee, _) = typeck.pat_ty(local.pat).kind() else { return None };
    if !declaration::pointee_is_nameable(tcx, subject.fn_did, *pointee) {
        return None;
    }
    declaration::emitted_type(
        &Decision::Slice {
            mutable,
            uses: Vec::new(),
        },
        &declaration::pointee_source(tcx, *pointee),
        None,
    )
}

/// A call result is never this rule's value: a LOCAL callee's converted
/// return is the return receiver's (a `from_raw_parts` over it is ill-typed),
/// a foreign allocator's is the Box family's. Casts and parentheses around
/// the call are peeled; `p.offset(k)`-style method calls on a place remain
/// this rule's offset-derived copies.
fn call_initialised(initializer: &rustc_hir::Expr<'_>) -> bool {
    use rustc_hir::ExprKind;
    let mut expr = initializer;
    loop {
        match expr.kind {
            ExprKind::Cast(inner, _) | ExprKind::DropTemps(inner) | ExprKind::Type(inner, _) => {
                expr = inner;
            }
            ExprKind::Call(..) => return true,
            _ => return false,
        }
    }
}

fn slice_mutability(decision: &Decision) -> Option<bool> {
    match decision {
        Decision::Slice { mutable, .. } => Some(*mutable),
        Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::NestedSlice { .. }
        | Decision::Opt { .. }
        | Decision::Box(_)
        | Decision::Cursor { .. }
        | Decision::Degraded(_) => None,
    }
}

/// The Slice arm's own need and licence: every raw-only use is arithmetic
/// (the need) and fatness concludes array (the licence). A thin candidate
/// keeps its residual reason; this rule never speaks for it.
fn slice_form_evidence(ctx: &Ctx<'_, '_>, subject: &Subject) -> bool {
    let node = (subject.fn_did, subject.hir_id);
    ctx.facts.raw_only_uses.get(&node).is_some_and(|uses| {
        !uses.is_empty()
            && uses
                .iter()
                .all(|(op, _)| super::emitability::SLICE_ARITHMETIC_OPS.contains(&op.as_str()))
    }) && ctx.fat.is_array(subject.fn_did, subject.local)
}

/// R397-6(b) / R398-1: a candidate whose local is an argument of a LOCAL
/// callee sits on a shared interface. Attempting it adds an interface edge
/// that withdraws the callee's prior deliveries and then fails at the call
/// adapter, so it is declined before selection and keeps its typed hold.
pub(crate) fn argument_of_local_callee(tcx: TyCtxt<'_>, subject: &Subject) -> bool {
    use rustc_hir::{
        ExprKind, QPath,
        def::{DefKind, Res},
        intravisit::Visitor,
    };
    struct Find<'tcx> {
        typeck: &'tcx rustc_middle::ty::TypeckResults<'tcx>,
        binding: rustc_hir::HirId,
        found: bool,
    }
    impl<'tcx> Visitor<'tcx> for Find<'tcx> {
        fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
            if let ExprKind::Call(callee, args) = expr.kind
                && let ExprKind::Path(QPath::Resolved(_, path)) = &callee.kind
                && let Res::Def(DefKind::Fn, def_id) = path.res
                && def_id.is_local()
                && args.iter().any(|arg| {
                    matches!(&arg.kind, ExprKind::Path(path)
                        if self.typeck.qpath_res(path, arg.hir_id) == Res::Local(self.binding))
                })
            {
                self.found = true;
            }
            rustc_hir::intravisit::walk_expr(self, expr);
        }
    }
    let mut find = Find {
        typeck: tcx.typeck(subject.fn_did),
        binding: subject.hir_id,
        found: false,
    };
    find.visit_body(tcx.hir_body_owned_by(subject.fn_did));
    find.found
}

pub(super) fn permits(ctx: &Ctx<'_, '_>, subject: &Subject) -> bool {
    let node = (subject.fn_did, subject.hir_id);
    ctx.family_policy
        .enabled(subject.fn_did, FamilyStage::Declaration)
        && ctx
            .family_policy
            .enabled(subject.fn_did, FamilyStage::SliceConstruction)
        && construction::slice_constructor_available(ctx.constructions, node)
        && slice_form_evidence(ctx, subject)
        && !argument_of_local_callee(ctx.tcx, subject)
        // relay 012 §1: the refusal every constructor-typing rule shares
        // (wave-6a): a thin-Ref root the Slice arm would not deliver fat is
        // never widened by a construction over it (R395-2 fix-2), a receiver
        // of a local callee is the return family's, an argument of one is
        // declined.
        && !super::slice_local_construction::refuses(ctx, subject)
        && emitted_type(ctx.tcx, subject, subject.mutable).is_some()
}

/// After item 2 has sealed the construction plans: every unannotated slice
/// local whose plan rendered a value gets its explicit declaration.
pub(crate) fn append_declarations(tcx: TyCtxt<'_>, table: &mut super::DecisionTable) {
    let mut sites = Vec::new();
    for (subject, decision) in &table.entries {
        let Some(mutable) = slice_mutability(decision) else { continue };
        let node = (subject.fn_did, subject.hir_id);
        if !table
            .slice_constructions
            .iter()
            .any(|plan| plan.node == node && plan.replacement.is_some())
        {
            continue;
        }
        let Some(emitted_type) = emitted_type(tcx, subject, mutable) else { continue };
        if table
            .seams
            .explicit_declarations
            .iter()
            .any(|site| site.node == Some(node))
        {
            continue;
        }
        sites.push(seam::ExplicitDeclarationSite {
            owner_class: SignatureClassId::of(subject.fn_did),
            caller: subject.fn_did,
            node: Some(node),
            span: Some(subject.binding_span.shrink_to_hi()),
            category: "local",
            replacement: Some(format!(": {emitted_type}")),
            emitted_type,
            arm: "surface",
        });
    }
    table.seams.explicit_declarations.extend(sites);
}

/// An unannotated slice local whose value is a rendered construction plan and
/// whose type is an explicit local declaration site.
pub(crate) fn has_declaration(table: &super::DecisionTable, subject: &Subject) -> bool {
    let node = (subject.fn_did, subject.hir_id);
    subject.ty_span.is_none()
        && table
            .slice_constructions
            .iter()
            .any(|plan| plan.node == node && plan.replacement.is_some())
        && table.seams.explicit_declarations.iter().any(|site| {
            site.node == Some(node)
                && site.category == "local"
                && site.owner_class == SignatureClassId::of(subject.fn_did)
        })
}
