//! Counted byte accesses in program-defined callees. No symbol-name contracts.
//!
//! The complete occurrence walk binds each byte access to an unsigned index
//! below one unchanged scalar parameter. Writes use MaybeUninit bytes: a valid
//! C fill/copy may target fresh, uninitialized allocation storage.
use rustc_hash::FxHashMap;
use rustc_hir::{
    Expr, ExprKind, HirId, Node, PatKind,
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{TyCtxt, TyKind};

use super::{
    Subject, SubjectKind,
    declaration::{DeclarationPointees, ResolvedPointee},
    emitability::{SliceUses, UseEdit},
};

type Key = (LocalDefId, HirId);
pub(crate) type Contracts = FxHashMap<Key, Contract>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ByteElement {
    Read,
    Write,
}
impl ByteElement {
    pub(crate) fn pointee(self) -> &'static str {
        match self {
            Self::Read => "u8",
            Self::Write => "core::mem::MaybeUninit<u8>",
        }
    }
}
#[derive(Clone, Debug)]
pub(crate) struct Contract {
    pub(crate) count_index: usize,
    pub(crate) element: ByteElement,
    pub(crate) uses: Vec<UseEdit>,
}
fn prove(tcx: TyCtxt<'_>, s: &Subject) -> Option<Contract> {
    if s.ptr_depth != 1 || !matches!(s.kind, SubjectKind::Param { .. }) {
        return None;
    }
    let Node::Pat(pat) = tcx.hir_node(s.hir_id) else { return None };
    if !super::void_pointee::has_void_pointee(tcx, tcx.typeck(s.fn_did).pat_ty(pat), 1) {
        return None;
    }
    let schedule = super::counted_void_loop::prove(tcx, s.fn_did)?;
    let write = if s.hir_id == schedule.destination {
        true
    } else if Some(s.hir_id) == schedule.source {
        false
    } else {
        return None;
    };
    // A single source/destination binding would need two simultaneous forms.
    if schedule.source == Some(schedule.destination) || write != s.mutable {
        return None;
    }
    let Node::Expr(assignment) = tcx.hir_node(schedule.assignment) else { return None };
    let ExprKind::Assign(lhs, rhs, _) = assignment.kind else { return None };
    let access = if write { lhs } else { rhs };
    if access.span.from_expansion() {
        return None;
    }
    let Node::Pat(index) = tcx.hir_node(schedule.index) else { return None };
    let PatKind::Binding(_, _, index_name, _) = index.kind else { return None };
    let name = s.param_name.as_ref()?;
    let signed = matches!(
        tcx.typeck(s.fn_did).expr_ty(access).kind(),
        TyKind::Int(rustc_middle::ty::IntTy::I8)
    );
    let ty = if signed { "i8" } else { "u8" };
    let replacement = if write {
        format!(
            "*{name}.get_mut({index_name} as usize).expect(\"counted byte index\").as_mut_ptr().cast::<{ty}>()"
        )
    } else {
        format!("({name}[{index_name} as usize] as {ty})")
    };
    let body = tcx.hir_body_owned_by(s.fn_did);
    let count_index = body
        .params
        .iter()
        .position(|p| matches!(p.pat.kind,PatKind::Binding(_,h,_,_) if h==schedule.count))?;
    Some(Contract {
        count_index,
        element: if write {
            ByteElement::Write
        } else {
            ByteElement::Read
        },
        uses: vec![UseEdit {
            span: access.span,
            replacement,
            bridge_kind: "counted-void-byte-access",
        }],
    })
}

pub(crate) fn collect(
    tcx: TyCtxt<'_>,
    subjects: &[Subject],
    pointees: &mut DeclarationPointees,
) -> Contracts {
    let mut out = Contracts::default();
    for s in subjects {
        let Some(contract) = prove(tcx, s) else { continue };
        let Some(span) = s.ty_span else { continue };
        let Ok(original_alias) = tcx.sess.source_map().span_to_snippet(span) else { continue };
        let Node::Pat(pat) = tcx.hir_node(s.hir_id) else { continue };
        pointees.insert(
            (s.fn_did, s.hir_id),
            ResolvedPointee {
                original_alias,
                input_type: super::declaration::pointee_source(
                    tcx,
                    tcx.typeck(s.fn_did).pat_ty(pat),
                ),
                pointee: contract.element.pointee().to_owned(),
            },
        );
        out.insert((s.fn_did, s.hir_id), contract);
    }
    out
}
pub(crate) fn install(contracts: &Contracts, uses: &mut FxHashMap<Key, SliceUses>) {
    for (key, c) in contracts {
        uses.insert(
            *key,
            SliceUses {
                rewrites: c.uses.clone(),
                ..Default::default()
            },
        );
    }
}

pub(crate) fn parameter(
    table: &super::DecisionTable,
    callee: LocalDefId,
    index: usize,
) -> Option<&Contract> {
    table.entries.iter().find_map(|(s, d)| {
        (s.fn_did == callee
            && matches!(s.kind,SubjectKind::Param{hir_index} if hir_index == index)
            && slice_edits(d).is_some())
        .then(|| table.counted_void.get(&(s.fn_did, s.hir_id)))
        .flatten()
    })
}

pub(crate) fn count_argument(
    tcx: TyCtxt<'_>,
    table: &super::DecisionTable,
    site: &super::emitability::CallSite,
    c: &Contract,
) -> Option<String> {
    // Repeating a scalar read is permitted only in a call with no side effects
    // in any argument. More involved evaluation-order plans remain held.
    struct Pure<'a, 'tcx> {
        table: &'a super::DecisionTable,
        scalar_only: bool,
        argument_locals: Vec<HirId>,
        ok: bool,
        tcx: TyCtxt<'tcx>,
        owner: LocalDefId,
    }
    impl<'tcx> Visitor<'tcx> for Pure<'_, 'tcx> {
        fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
            if self
                .tcx
                .typeck(self.owner)
                .type_dependent_def_id(e.hir_id)
                .is_some()
            {
                self.ok = false;
            }
            if self.scalar_only
                && !matches!(
                    self.tcx.typeck(self.owner).expr_ty(e).kind(),
                    TyKind::Int(_) | TyKind::Uint(_)
                )
            {
                self.ok = false;
            }
            if let ExprKind::Path(path) = &e.kind {
                match self.tcx.typeck(self.owner).qpath_res(path, e.hir_id) {
                    rustc_hir::def::Res::Local(id) => self.argument_locals.push(id),
                    rustc_hir::def::Res::Def(
                        rustc_hir::def::DefKind::Const | rustc_hir::def::DefKind::AssocConst,
                        _,
                    ) => {}
                    _ => self.ok = false,
                }
            }
            if let ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = e.kind
                && let rustc_hir::def::Res::Local(id) = path.res
                && self
                    .table
                    .entries
                    .iter()
                    .any(|(s, d)| s.fn_did == self.owner && s.hir_id == id && !unchanged_pointer(d))
            {
                self.ok = false; // a raw expression must not hide a new thin view
            }
            match e.kind {
                ExprKind::Path(..)
                | ExprKind::Lit(..)
                | ExprKind::Cast(..)
                | ExprKind::Unary(..)
                | ExprKind::Binary(..) => {}
                _ => self.ok = false,
            }
            if matches!(e.kind, ExprKind::Unary(rustc_hir::UnOp::Deref, _)) {
                self.ok = false;
            }
            intravisit::walk_expr(self, e);
        }
    }
    for arg in &site.args {
        struct Find<'tcx> {
            span: rustc_span::Span,
            found: Option<&'tcx Expr<'tcx>>,
        }
        impl<'tcx> Visitor<'tcx> for Find<'tcx> {
            fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
                if e.span == self.span {
                    self.found = Some(e);
                }
                intravisit::walk_expr(self, e);
            }
        }
        let mut find = Find {
            span: arg.span,
            found: None,
        };
        find.visit_expr(tcx.hir_body_owned_by(site.caller).value);
        let e = find.found?;
        let mut pure = Pure {
            ok: true,
            table,
            scalar_only: matches!(
                tcx.typeck(site.caller).expr_ty(e).kind(),
                TyKind::Int(_) | TyKind::Uint(_)
            ),
            argument_locals: Vec::new(),
            tcx,
            owner: site.caller,
        };
        pure.visit_expr(e);
        if !pure.ok || !argument_storage_is_private(tcx, site.caller, &pure.argument_locals) {
            return None;
        }
    }
    let arg = site.args.iter().find(|a| a.index == c.count_index)?;
    tcx.sess.source_map().span_to_snippet(arg.span).ok()
}

pub(crate) fn render_bridge(
    spec: &super::seam::GlueSpec,
    element: ByteElement,
    text: &str,
) -> Option<String> {
    let super::seam::SeamLen::Licensed(count) = spec.len.as_ref()? else { return None };
    if spec.core != super::seam::GlueCore::FromRawParts || spec.optional || spec.unwrap.is_some() {
        return None;
    }
    let (pointer, ctor) = if spec.mutable {
        ("mut", "from_raw_parts_mut")
    } else {
        ("const", "from_raw_parts")
    };
    // SAFETY: the source is a raw full-extent pointer, never a thin reference.
    // Original byte reads establish initialized u8; writes use MaybeUninit.
    // The zero-count branch never constructs a slice from a null pointer.
    Some(format!(
        "{{ let (__crat_counted_ptr, __crat_counted_len) = (({text}) as *{pointer} {}, ({count}) as usize); if __crat_counted_len == 0 {{ &{} [] }} else {{ unsafe {{ core::slice::{ctor}(__crat_counted_ptr, __crat_counted_len) }} }} }}",
        element.pointee(),
        if spec.mutable { "mut" } else { "" }
    ))
}

pub(crate) fn bridge_ast(
    spec: &super::seam::GlueSpec,
    element: ByteElement,
    argument: &rustc_ast::Expr,
) -> Option<rustc_ast::ExprKind> {
    // Keep the argument's original subtree; only scaffold text is parsed.
    const MARKER: &str = "__crat_counted_original_argument";
    let text = render_bridge(spec, element, MARKER)?;
    let parsed = crate::bo_rewriter::ast_transform::graft_expr(&text).ok()?;
    struct Replace<'a> {
        argument: &'a rustc_ast::Expr,
        count: usize,
    }
    impl rustc_ast::mut_visit::MutVisitor for Replace<'_> {
        fn visit_expr(&mut self, e: &mut rustc_ast::Expr) {
            if matches!(&e.kind,rustc_ast::ExprKind::Path(None,p) if p.segments.len()==1 && p.segments[0].ident.name.as_str()==MARKER)
            {
                *e = self.argument.clone();
                self.count += 1;
                return;
            }
            rustc_ast::mut_visit::walk_expr(self, e);
        }
    }
    let mut visitor = Replace { argument, count: 0 };
    let mut root = rustc_ast::ptr::P(parsed);
    visitor.count = 0;
    rustc_ast::mut_visit::MutVisitor::visit_expr(&mut visitor, &mut root);
    (visitor.count == 1).then(|| root.kind.clone())
}

pub(crate) fn active<'a>(ctx: &super::Ctx<'a, '_>, s: &Subject) -> Option<&'a Contract> {
    use crate::bo_rewriter::additive::FamilyStage;
    (ctx.family_policy
        .enabled(s.fn_did, FamilyStage::Declaration)
        && ctx.family_policy.enabled(s.fn_did, FamilyStage::SliceUse))
    .then(|| ctx.counted_void.get(&(s.fn_did, s.hir_id)))
    .flatten()
}

pub(crate) fn owns_address(
    table: &super::DecisionTable,
    site: &super::raw_boundary::AddressViewSite,
) -> bool {
    if site.op != "ptr-cast" {
        return false;
    }
    let Some(contract) = table.counted_void.get(&site.node) else { return false };
    table.entries.iter().any(|(s, d)| {
        (s.fn_did, s.hir_id) == site.node
            && slice_edits(d).is_some_and(|uses| {
                contract
                    .uses
                    .iter()
                    .any(|owned| owned.span.contains(site.span) && uses.contains(owned))
            })
    })
}

/// Evaluating another argument after an adapter creates a borrow is harmless
/// only when no pointer can address that argument binding's storage. Otherwise the call needs
/// a complete argument snapshot before any borrow, which this rule holds.
fn argument_storage_is_private(tcx: TyCtxt<'_>, owner: LocalDefId, locals: &[HirId]) -> bool {
    if locals.is_empty() {
        return true;
    }
    struct Private<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        owner: LocalDefId,
        locals: &'a [HirId],
        ok: bool,
    }
    impl<'tcx> Visitor<'tcx> for Private<'_, 'tcx> {
        fn visit_pat(&mut self, p: &'tcx rustc_hir::Pat<'tcx>) {
            if matches!(p.kind,PatKind::Binding(mode,..) if mode.0 != rustc_ast::ByRef::No) {
                self.ok = false;
            }
            intravisit::walk_pat(self, p);
        }

        fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
            if matches!(e.kind, ExprKind::Closure(..)) {
                self.ok = false;
            }
            if let ExprKind::Path(path) = &e.kind
                && let rustc_hir::def::Res::Local(id) =
                    self.tcx.typeck(self.owner).qpath_res(path, e.hir_id)
                && self.locals.contains(&id)
            {
                if !self.tcx.typeck(self.owner).expr_adjustments(e).is_empty()
                    || matches!(self.tcx.parent_hir_node(e.hir_id),Node::Expr(p) if matches!(p.kind,ExprKind::AddrOf(..)))
                {
                    self.ok = false;
                }
            }
            intravisit::walk_expr(self, e);
        }
    }
    let mut private = Private {
        tcx,
        owner,
        locals,
        ok: true,
    };
    private.visit_expr(tcx.hir_body_owned_by(owner).value);
    private.ok
}

fn slice_edits(decision: &super::Decision) -> Option<&[UseEdit]> {
    use super::Decision;
    match decision {
        Decision::Slice { uses, .. } => Some(uses),
        Decision::Cursor { .. }
        | Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::NestedSlice { .. }
        | Decision::Opt { .. }
        | Decision::Box(_)
        | Decision::Degraded(_) => None,
    }
}
fn unchanged_pointer(decision: &super::Decision) -> bool {
    use super::Decision;
    match decision {
        Decision::Degraded(_) => true,
        Decision::Cursor { .. }
        | Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::NestedSlice { .. }
        | Decision::Opt { .. }
        | Decision::Box(_) => false,
    }
}
