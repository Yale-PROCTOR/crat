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
    /// The parameter is null-tested (or forwards to a null-tested one): its
    /// form is `Option<&[u8]>` and a raw caller bridges through the null arm.
    pub(crate) nullable: bool,
    /// A `void *` handle to ONE struct: the declared pointee type's text. The
    /// form is a plain reference; no count, no use edits beyond null tests.
    pub(crate) handle: Option<String>,
    /// wave-6v2: the byte count is a width the callee's own typed accesses
    /// fix (a constant, or one width per literal of a sibling discriminant);
    /// `count_index` is then the discriminant's index, or the parameter's own.
    pub(crate) width: Option<super::binn_counted::WidthTable>,
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
        nullable: false,
        handle: None,
        width: None,
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
    model_raw: impl Fn(&Subject) -> bool,
) -> Contracts {
    let mut out = Contracts::default();
    let mut proven: Vec<(&Subject, Contract)> = subjects
        .iter()
        .filter(|s| !model_raw(s))
        .filter_map(|s| {
            prove(tcx, s)
                .or_else(|| super::counted_void_read::prove(tcx, s))
                .or_else(|| super::counted_void_handle::prove(tcx, s))
                .or_else(|| super::binn_counted::prove(tcx, s))
                .or_else(|| super::binn_counted::prove_foreign_copy(tcx, s))
                .map(|c| (s, c))
        })
        .collect();
    // Forwarded parameters, to a fixpoint (a wrapper of a wrapper).
    loop {
        let known: FxHashMap<Key, Contract> = proven
            .iter()
            .map(|(s, c)| ((s.fn_did, s.hir_id), c.clone()))
            .collect();
        let mut added = 0;
        for s in subjects {
            if known.contains_key(&(s.fn_did, s.hir_id)) || model_raw(s) {
                continue;
            }
            if let Some(contract) = prove_forward(tcx, s, subjects, &known) {
                proven.push((s, contract));
                added += 1;
            }
        }
        // wave-6v2: the forward-only shape runs only once the sibling-count
        // forwards have converged, so a wrapper of a counted pair takes the
        // pair's contract, never the width-less view.
        if added == 0 {
            for s in subjects {
                if known.contains_key(&(s.fn_did, s.hir_id)) {
                    continue;
                }
                if let Some(contract) =
                    super::binn_counted::prove_forward_only(tcx, s, subjects, &known)
                {
                    proven.push((s, contract));
                    added += 1;
                }
            }
        }
        if added == 0 {
            break;
        }
    }
    for (s, contract) in proven {
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
                pointee: contract
                    .handle
                    .clone()
                    .unwrap_or_else(|| contract.element.pointee().to_owned()),
            },
        );
        out.insert((s.fn_did, s.hir_id), contract);
    }
    out
}
/// A `void *` parameter whose only uses are null tests and ONE pass-through as
/// the counted pointer argument of a local counted callee, with a sibling
/// parameter passed unchanged as that callee's count: the pair travels together
/// and the parameter takes the callee's contract (element, nullability).
fn prove_forward(
    tcx: TyCtxt<'_>,
    s: &Subject,
    subjects: &[Subject],
    known: &FxHashMap<Key, Contract>,
) -> Option<Contract> {
    if s.ptr_depth != 1 || !matches!(s.kind, SubjectKind::Param { .. }) {
        return None;
    }
    let Node::Pat(pat) = tcx.hir_node(s.hir_id) else { return None };
    if !super::void_pointee::has_void_pointee(tcx, tcx.typeck(s.fn_did).pat_ty(pat), 1) {
        return None;
    }
    let body = tcx.hir_body_owned_by(s.fn_did);
    let params = body
        .params
        .iter()
        .map(|p| match p.pat.kind {
            PatKind::Binding(_, id, _, None) => Some(id),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    struct Uses<'tcx> {
        target: HirId,
        found: Vec<&'tcx Expr<'tcx>>,
        writes: bool,
        closures: bool,
    }
    impl<'tcx> Visitor<'tcx> for Uses<'tcx> {
        fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
            if let ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = e.kind
                && path.res == rustc_hir::def::Res::Local(self.target)
            {
                self.found.push(e);
            }
            match e.kind {
                ExprKind::Assign(lhs, _, _) | ExprKind::AssignOp(_, lhs, _) if matches!(lhs.kind, ExprKind::Path(rustc_hir::QPath::Resolved(_, p)) if p.res == rustc_hir::def::Res::Local(self.target)) =>
                {
                    self.writes = true;
                }
                ExprKind::Closure(..) => self.closures = true,
                _ => {}
            }
            intravisit::walk_expr(self, e);
        }
    }
    let mut uses = Uses {
        target: s.hir_id,
        found: Vec::new(),
        writes: false,
        closures: false,
    };
    uses.visit_expr(body.value);
    if uses.writes || uses.closures {
        return None;
    }
    let name = s.param_name.as_ref()?;
    let typeck = tcx.typeck(s.fn_did);
    let mut edits = Vec::new();
    let mut forwarded: Option<Contract> = None;
    let mut nullable = false;
    for use_ in uses.found {
        let Node::Expr(parent) = tcx.parent_hir_node(use_.hir_id) else { return None };
        match parent.kind {
            ExprKind::MethodCall(segment, receiver, [], _)
                if receiver.hir_id == use_.hir_id && segment.ident.name.as_str() == "is_null" =>
            {
                nullable = true;
                edits.push(UseEdit {
                    span: parent.span,
                    replacement: format!("{name}.is_none()"),
                    bridge_kind: "counted-void-null-test",
                });
            }
            ExprKind::Call(callee, args) => {
                if forwarded.is_some() {
                    return None;
                }
                let index = args.iter().position(|a| a.hir_id == use_.hir_id)?;
                let ExprKind::Path(path) = &callee.kind else { return None };
                let rustc_hir::def::Res::Def(rustc_hir::def::DefKind::Fn, did) =
                    typeck.qpath_res(path, callee.hir_id)
                else {
                    return None;
                };
                let callee = did.as_local()?;
                let (_, contract) = known.iter().find(|((f, h), _)| {
                    *f == callee
                        && subjects.iter().any(|t| {
                            t.fn_did == callee
                                && t.hir_id == *h
                                && matches!(t.kind, SubjectKind::Param { hir_index } if hir_index == index)
                        })
                })?;
                let count = args.get(contract.count_index)?;
                let ExprKind::Path(rustc_hir::QPath::Resolved(_, count_path)) = count.kind else {
                    return None;
                };
                let rustc_hir::def::Res::Local(count_local) = count_path.res else { return None };
                let count_index = params.iter().position(|p| *p == count_local)?;
                if count_index == params.iter().position(|p| *p == s.hir_id)? {
                    return None;
                }
                if contract.handle.is_some() {
                    return None;
                }
                nullable |= contract.nullable;
                forwarded = Some(Contract {
                    count_index,
                    element: contract.element,
                    nullable: contract.nullable,
                    handle: None,
                    width: contract
                        .width
                        .as_ref()
                        .map(|width| width.rekey(count_index)),
                    uses: Vec::new(),
                });
            }
            _ => return None,
        }
    }
    let mut contract = forwarded?;
    contract.nullable = nullable;
    contract.uses = edits;
    Some(contract)
}

pub(crate) fn install(contracts: &Contracts, uses: &mut FxHashMap<Key, SliceUses>) {
    for (key, c) in contracts {
        if c.handle.is_some() {
            continue;
        }
        uses.insert(
            *key,
            SliceUses {
                rewrites: c.uses.clone(),
                ..Default::default()
            },
        );
    }
}

/// The optional form reads its rewrites from the Option use map.
pub(crate) fn install_opt(
    contracts: &Contracts,
    uses: &mut FxHashMap<Key, super::emitability::OptUses>,
) {
    for (key, c) in contracts {
        if c.nullable && c.handle.is_none() {
            uses.insert(
                *key,
                super::emitability::OptUses {
                    rewrites: c.uses.clone(),
                    non_test_uses: 1,
                    ..Default::default()
                },
            );
        }
    }
}

pub(crate) fn parameter(
    table: &super::DecisionTable,
    callee: LocalDefId,
    index: usize,
) -> Option<&Contract> {
    contract_at(table, callee, index).map(|(_, c)| c)
}

/// The closure-call snapshot's parameter name for one argument position.
pub(crate) fn placeholder(index: usize) -> String {
    format!("__crat_cv_{index}")
}

/// How one counted call is emitted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Route {
    /// One bridged position: the closure snapshot.
    Direct,
    /// Two bridged positions whose roots are provably distinct allocations:
    /// the closure snapshot with both views.
    Split,
    /// Two bridged positions without a disjointness proof: the call keeps its
    /// original arguments and is routed to the callee's pristine raw twin.
    RawTwin,
    /// A `void *` handle to one struct: the raw argument is cast to the
    /// declared pointee and reborrowed at the argument itself (no snapshot).
    Handle,
    /// A converted `&mut` place argument beside an argument that READS the
    /// same local: every unconverted argument is evaluated into a `let`
    /// before the call, so the borrow starts after the reads.
    Hoist,
}
impl Route {
    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::Direct => "direct",
            Self::Split => "split",
            Self::RawTwin => "raw-twin",
            Self::Handle => "handle",
            Self::Hoist => "hoist",
        }
    }
}

/// One byte-view adapter inside a snapshotted call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct CountedByte {
    pub(crate) element: ByteElement,
    pub(crate) arg_index: usize,
    pub(crate) route: Route,
    /// The handle's declared pointee (route `Handle` only).
    pub(crate) handle_pointee: Option<rustc_span::Symbol>,
}

/// The raw twin's name: the original body under this name, called from every
/// site that could not be split.
pub(crate) fn raw_twin_name(callee: &str) -> String {
    format!("__crat_raw_{callee}")
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BridgedArg {
    pub(crate) index: usize,
    pub(crate) param: HirId,
    pub(crate) element: ByteElement,
    pub(crate) mutable: bool,
    /// The adapter over the snapshot parameters, exactly as the seam rendered it.
    pub(crate) bridge: String,
}

/// One call whose arguments are all evaluated before any byte view is formed.
///
/// Emitted as `(|__crat_cv_0, .., __crat_cv_n| callee(..))(a0, .., an)`: the
/// closure call evaluates every original argument exactly once, left to right,
/// exactly as the original call did, and only its body forms the byte views
/// from the snapshotted pointer and count values. No argument expression is
/// therefore ever evaluated while a generated `&mut` view is live.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CallPlan {
    pub(crate) owner_class: crate::bo_rewriter::bridge_receipt::SignatureClassId,
    pub(crate) caller: LocalDefId,
    pub(crate) callee: LocalDefId,
    pub(crate) call_span: rustc_span::Span,
    pub(crate) count_index: usize,
    pub(crate) route: Route,
    pub(crate) bridged: Vec<BridgedArg>,
    /// Typed receipt of the count argument's form (R397-4): `elements:<n>*size_of::<T>`
    /// when the byte count is an exact element count times an element size,
    /// else `bytes`. The emitted length is the count argument's exact value in
    /// both cases; nothing is fabricated.
    pub(crate) count_form: String,
}

pub(crate) fn render_bridge(
    spec: &super::seam::GlueSpec,
    counted: CountedByte,
    text: &str,
) -> Option<String> {
    if counted.route == Route::RawTwin {
        // Zero syntax at the argument: the call itself is renamed to the twin.
        return Some(text.to_owned());
    }
    if counted.route == Route::Handle {
        let pointee = counted.handle_pointee?;
        // SAFETY: the input passes a pointer to one `T` here (its own
        // contract); the reborrow is of exactly that element.
        return Some(if spec.mutable {
            format!("&mut *(({text}) as *mut {pointee})")
        } else {
            format!("&*(({text}) as *const {pointee})")
        });
    }
    let super::seam::SeamLen::Licensed(count) = spec.len.as_ref()? else { return None };
    if spec.core != super::seam::GlueCore::FromRawParts || spec.unwrap.is_some() {
        return None;
    }
    let (pointer, ctor) = if spec.mutable {
        ("mut", "from_raw_parts_mut")
    } else {
        ("const", "from_raw_parts")
    };
    let text = placeholder(counted.arg_index);
    if spec.optional {
        // Null is `None`; a non-null pointer with a zero count is an empty
        // view; otherwise the counted view (the same obligations as below).
        return Some(format!(
            "{{ let (__crat_counted_ptr, __crat_counted_len) = (({text}) as *{pointer} {}, ({count}) as usize); if __crat_counted_ptr.is_null() {{ None }} else if __crat_counted_len == 0 {{ Some(&{} []) }} else {{ Some(unsafe {{ core::slice::{ctor}(__crat_counted_ptr, __crat_counted_len) }}) }} }}",
            counted.element.pointee(),
            if spec.mutable { "mut" } else { "" }
        ));
    }
    // SAFETY: the source is a raw full-extent pointer, never a thin reference.
    // Original byte reads establish initialized u8; writes use MaybeUninit.
    // The zero-count branch never constructs a slice from a null pointer.
    // Both operands are the closure call's snapshot parameters, so the view is
    // formed after every original argument was evaluated.
    Some(format!(
        "{{ let (__crat_counted_ptr, __crat_counted_len) = (({text}) as *{pointer} {}, ({count}) as usize); if __crat_counted_len == 0 {{ &{} [] }} else {{ unsafe {{ core::slice::{ctor}(__crat_counted_ptr, __crat_counted_len) }} }} }}",
        counted.element.pointee(),
        if spec.mutable { "mut" } else { "" }
    ))
}

/// The argument-level graft is the identity for counted routes: the argument
/// subtree stays where it is and is moved into the closure call by
/// [`graft_calls`], which owns the whole call expression. The seam still
/// claims the node, so the placement is counted exactly once and a colliding
/// transform is refused. A handle argument is cast and reborrowed in place.
pub(crate) fn bridge_ast(
    spec: &super::seam::GlueSpec,
    counted: CountedByte,
    argument: &rustc_ast::Expr,
) -> Option<rustc_ast::ExprKind> {
    if counted.route != Route::Handle {
        return Some(argument.kind.clone());
    }
    const MARKER: &str = "__crat_handle_original_argument";
    let text = render_bridge(spec, counted, MARKER)?;
    let parsed = crate::bo_rewriter::ast_transform::graft_expr(&text).ok()?;
    struct Replace<'a> {
        argument: &'a rustc_ast::Expr,
        count: usize,
    }
    impl rustc_ast::mut_visit::MutVisitor for Replace<'_> {
        fn visit_expr(&mut self, e: &mut rustc_ast::Expr) {
            if matches!(&e.kind, rustc_ast::ExprKind::Path(None, p) if p.segments.len() == 1 && p.segments[0].ident.name.as_str() == MARKER)
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
    rustc_ast::mut_visit::MutVisitor::visit_expr(&mut visitor, &mut root);
    (visitor.count == 1).then(|| root.kind.clone())
}

pub(crate) fn active<'a>(ctx: &super::Ctx<'a, '_>, s: &Subject) -> Option<&'a Contract> {
    use crate::bo_rewriter::additive::FamilyStage;
    let contract = ctx.counted_void.get(&(s.fn_did, s.hir_id))?;
    let declaration = ctx
        .family_policy
        .enabled_for((s.fn_did, s.hir_id), FamilyStage::Declaration);
    // A handle has no slice uses to place; a counted view has.
    let uses = contract.handle.is_some()
        || ctx
            .family_policy
            .enabled_for((s.fn_did, s.hir_id), FamilyStage::SliceUse);
    (declaration && uses).then_some(contract)
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

fn find_expr<'tcx>(body: &'tcx Expr<'tcx>, span: rustc_span::Span) -> Option<&'tcx Expr<'tcx>> {
    struct Find<'tcx> {
        span: rustc_span::Span,
        found: Option<&'tcx Expr<'tcx>>,
    }
    impl<'tcx> Visitor<'tcx> for Find<'tcx> {
        fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
            if self.found.is_none() && e.span == self.span {
                self.found = Some(e);
                return;
            }
            intravisit::walk_expr(self, e);
        }
    }
    let mut find = Find { span, found: None };
    find.visit_expr(body);
    find.found
}

fn strip_casts<'tcx>(mut e: &'tcx Expr<'tcx>) -> &'tcx Expr<'tcx> {
    loop {
        match e.kind {
            ExprKind::Cast(inner, _) | ExprKind::DropTemps(inner) => e = inner,
            _ => return e,
        }
    }
}

/// `size_of::<T>()` — the element type, when `e` is exactly that call.
fn size_of_element<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    e: &'tcx Expr<'tcx>,
) -> Option<rustc_middle::ty::Ty<'tcx>> {
    let ExprKind::Call(callee, []) = e.kind else { return None };
    let ExprKind::Path(path) = &callee.kind else { return None };
    let rustc_hir::def::Res::Def(rustc_hir::def::DefKind::Fn, did) =
        tcx.typeck(owner).qpath_res(path, callee.hir_id)
    else {
        return None;
    };
    if !tcx.is_diagnostic_item(rustc_span::sym::mem_size_of, did) {
        return None;
    }
    tcx.typeck(owner).node_args(callee.hir_id).types().next()
}

/// The count argument's form. `Elements` is the R397-4 form `n * size_of::<T>()`
/// (either operand order, through `wrapping_mul` or `*`, under any integer
/// casts); a bare `size_of::<T>()` is one element.
struct CountForm<'tcx> {
    element: Option<(rustc_middle::ty::Ty<'tcx>, Option<u128>, String)>,
}
fn count_form<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    count: &'tcx Expr<'tcx>,
) -> CountForm<'tcx> {
    let sm = tcx.sess.source_map();
    let count = strip_casts(count);
    let operands: Option<(&Expr<'_>, &Expr<'_>)> = match count.kind {
        ExprKind::MethodCall(segment, receiver, [argument], _)
            if segment.ident.name.as_str() == "wrapping_mul" =>
        {
            Some((receiver, argument))
        }
        ExprKind::Binary(op, left, right) if op.node == rustc_hir::BinOpKind::Mul => {
            Some((left, right))
        }
        _ => None,
    };
    let element = match operands {
        Some((left, right)) => [(left, right), (right, left)]
            .into_iter()
            .find_map(|(size, n)| {
                let ty = size_of_element(tcx, owner, strip_casts(size))?;
                let literal = match strip_casts(n).kind {
                    ExprKind::Lit(lit) => match lit.node {
                        rustc_ast::LitKind::Int(value, _) => Some(value.get()),
                        _ => None,
                    },
                    _ => None,
                };
                Some((ty, literal, sm.span_to_snippet(n.span).unwrap_or_default()))
            }),
        None => size_of_element(tcx, owner, count).map(|ty| (ty, Some(1), "1".to_owned())),
    };
    CountForm { element }
}
impl CountForm<'_> {
    fn receipt(&self) -> String {
        match &self.element {
            Some((ty, _, n)) => {
                let n: String = n.split_whitespace().collect::<Vec<_>>().join(" ");
                format!("elements:{n}*size_of::<{ty}>")
            }
            None => "bytes".to_owned(),
        }
    }
}

/// Where the bridged pointer's provenance comes from, read off the argument
/// expression of the INPUT program.
pub(crate) enum Root {
    /// The value of this local: its referent is what the view covers.
    Value(HirId),
    /// This local's own storage is what the view covers.
    Storage(HirId),
    /// A loaded pointer, a call result, a literal: no subject's claim is at stake.
    Opaque,
}
pub(crate) fn value_root(e: &Expr<'_>) -> Root {
    match e.kind {
        ExprKind::Cast(inner, _) | ExprKind::DropTemps(inner) => value_root(inner),
        ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) => match path.res {
            rustc_hir::def::Res::Local(id) => Root::Value(id),
            _ => Root::Opaque,
        },
        ExprKind::MethodCall(segment, receiver, _, _) => match segment.ident.name.as_str() {
            "as_mut_ptr" | "as_ptr" => place_root(receiver),
            _ => value_root(receiver),
        },
        ExprKind::AddrOf(_, _, place) => place_root(place),
        _ => Root::Opaque,
    }
}
fn place_root(e: &Expr<'_>) -> Root {
    match e.kind {
        ExprKind::Field(base, _) | ExprKind::Index(base, _, _) => place_root(base),
        ExprKind::Unary(rustc_hir::UnOp::Deref, pointer) => value_root(pointer),
        ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) => match path.res {
            rustc_hir::def::Res::Local(id) => Root::Storage(id),
            _ => Root::Opaque,
        },
        ExprKind::DropTemps(inner) => place_root(inner),
        _ => Root::Opaque,
    }
}
/// The place whose bytes the view starts at, for the fitting proof: the
/// receiver of `as_mut_ptr`/`as_ptr`, the operand of `&`/`&mut`, or the
/// pointee of a bare pointer local.
pub(crate) fn viewed_type<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    e: &'tcx Expr<'tcx>,
) -> Option<rustc_middle::ty::Ty<'tcx>> {
    let typeck = tcx.typeck(owner);
    match strip_casts(e).kind {
        ExprKind::MethodCall(segment, receiver, [], _)
            if matches!(segment.ident.name.as_str(), "as_mut_ptr" | "as_ptr") =>
        {
            Some(typeck.expr_ty(receiver))
        }
        ExprKind::AddrOf(_, _, place) => Some(typeck.expr_ty(place)),
        ExprKind::Path(..) => match typeck.expr_ty(strip_casts(e)).kind() {
            TyKind::RawPtr(pointee, _) => Some(*pointee),
            _ => None,
        },
        _ => None,
    }
}
pub(crate) fn thin(decision: &super::Decision) -> bool {
    use super::Decision;
    match decision {
        Decision::Ref { .. } | Decision::InferredRef { .. } => true,
        Decision::Opt { slice, .. } => !slice,
        Decision::Box(plan) => plan.shape == super::box_facts::BoxShape::Sized,
        Decision::Slice { .. } | Decision::NestedSlice { .. } | Decision::Cursor { .. } => false,
        Decision::Degraded(_) => false,
    }
}

/// Never widen a thin reference (R395-2). A bridged pointer whose provenance is
/// a local this table decided THIN may be viewed only over exactly the place the
/// argument names, and only when the count is a literal element count times the
/// element size of that place (`[T; n]`, or `T` for one element). A local whose
/// own storage is viewed must not be a converted subject at all. Every other
/// root is raw or fat: the extent obligation rests on the input program (§28) or
/// on the fat form's own extent receipt.
fn root_rule<'tcx>(
    tcx: TyCtxt<'tcx>,
    table: &super::DecisionTable,
    caller: LocalDefId,
    argument: &'tcx Expr<'tcx>,
    form: &CountForm<'tcx>,
) -> Result<(), super::seam::SeamBlock> {
    let decision_of = |id: HirId| {
        table
            .entries
            .iter()
            .find(|(s, _)| s.fn_did == caller && s.hir_id == id)
            .map(|(_, d)| d)
    };
    match value_root(argument) {
        Root::Opaque => Ok(()),
        Root::Storage(id) => match decision_of(id) {
            Some(super::Decision::Degraded(_)) | None => Ok(()),
            Some(_) => Err(super::seam::SeamBlock::CountedVoidRoot),
        },
        Root::Value(id) => {
            let Some(decision) = decision_of(id) else { return Ok(()) };
            if !thin(decision) {
                return Ok(());
            }
            let Some((element, Some(n), _)) = &form.element else {
                return Err(super::seam::SeamBlock::CountedVoidRoot);
            };
            let Some(viewed) = viewed_type(tcx, caller, argument) else {
                return Err(super::seam::SeamBlock::CountedVoidRoot);
            };
            let fits = if *n == 1 {
                viewed == *element
            } else {
                match viewed.kind() {
                    TyKind::Array(item, len) => {
                        *item == *element
                            && len
                                .try_to_target_usize(tcx)
                                .is_some_and(|len| u128::from(len) == *n)
                    }
                    _ => false,
                }
            };
            fits.then_some(())
                .ok_or(super::seam::SeamBlock::CountedVoidRoot)
        }
    }
}

/// The count argument's value plan for one bridged position at one call: the
/// closure snapshot's count parameter and the call's route, or a typed hold.
pub(crate) fn count_argument<'tcx>(
    tcx: TyCtxt<'tcx>,
    table: &super::DecisionTable,
    site: &super::emitability::CallSite,
    callee: LocalDefId,
    c: &Contract,
    arg_index: usize,
) -> Result<(String, Route), super::seam::SeamBlock> {
    use super::seam::SeamBlock;
    if c.handle.is_some() {
        return Ok((String::new(), Route::Handle));
    }
    let body = tcx.hir_body_owned_by(site.caller).value;
    let Some(ExprKind::Call(_, args)) =
        find_expr(body, site.span).map(|call| strip_casts(call).kind)
    else {
        return Err(SeamBlock::UnnameableOperand);
    };
    if args.iter().any(|argument| argument.span.from_expansion()) {
        return Err(SeamBlock::UnnameableOperand);
    }
    let count = args.get(c.count_index).ok_or(SeamBlock::LengthUnknown)?;
    let argument = args.get(arg_index).ok_or(SeamBlock::UnnameableOperand)?;
    let form = count_form(tcx, site.caller, count);
    let bridged = site
        .args
        .iter()
        .filter(|argument| contract_at(table, callee, argument.index).is_some())
        .map(|argument| argument.index)
        .collect::<Vec<_>>();
    let route = match bridged.as_slice() {
        [_] => Route::Direct,
        // Two byte views at one call may cover overlapping bytes: a
        // program-defined byte loop (unlike libc `memcpy`) is defined on
        // overlap, so overlap is not the input's fault, and one raw access
        // under a live view is as forbidden as two views. Two positions are
        // bridged only when their roots are provably distinct allocations;
        // otherwise the call keeps its raw arguments and calls the raw twin.
        [a, b] => {
            let (Some(left), Some(right)) = (args.get(*a), args.get(*b)) else {
                return Err(SeamBlock::UnnameableOperand);
            };
            if disjoint_roots(tcx, site.caller, left, right) {
                Route::Split
            } else if only_counted_params_convert(table, callee)
                && twin_is_a_leaf(tcx, table, callee)
            {
                Route::RawTwin
            } else {
                return Err(SeamBlock::SiteOverlap);
            }
        }
        _ => return Err(SeamBlock::SiteOverlap),
    };
    if let Some(width) = &c.width {
        // wave-6v2: the count is the callee's own width (table), never an
        // argument's value; the root rule reads the literal discriminant. A
        // forward-only parameter of unknown width has no count for a raw
        // caller: the site holds typed.
        if width.is_unknown() {
            return Err(SeamBlock::LengthUnknown);
        }
        if route != Route::RawTwin {
            let discriminant = width.discriminant.map(|k| args.get(k)).flatten();
            super::binn_counted::root_rule(tcx, table, site.caller, argument, width, discriminant)?;
        }
        return Ok((width.render(), route));
    }
    if route != Route::RawTwin {
        root_rule(tcx, table, site.caller, argument, &form)?;
    }
    Ok((placeholder(c.count_index), route))
}

/// The raw twin is the callee's pristine body under a new name: it calls every
/// local function with the input's raw arguments, so it compiles only when none
/// of those callees converts a parameter or its return (the leaf gate, relay
/// 011 §2). A call through a function pointer is not a local function here.
pub(crate) fn twin_is_a_leaf(
    tcx: TyCtxt<'_>,
    table: &super::DecisionTable,
    callee: LocalDefId,
) -> bool {
    use super::Decision;
    struct LocalCalls {
        found: Vec<LocalDefId>,
    }
    impl<'v> Visitor<'v> for LocalCalls {
        fn visit_expr(&mut self, e: &'v Expr<'v>) {
            if let ExprKind::Call(target, _) = e.kind
                && let ExprKind::Path(rustc_hir::QPath::Resolved(None, path)) = target.kind
                && let rustc_hir::def::Res::Def(rustc_hir::def::DefKind::Fn, def_id) = path.res
                && let Some(local) = def_id.as_local()
            {
                self.found.push(local);
            }
            intravisit::walk_expr(self, e);
        }
    }
    let mut calls = LocalCalls { found: Vec::new() };
    calls.visit_expr(tcx.hir_body_owned_by(callee).value);
    calls.found.iter().all(|g| {
        table.entries.iter().all(|(s, d)| {
            s.fn_did != *g
                || match d {
                    Decision::Degraded(_) => true,
                    Decision::Cursor { .. }
                    | Decision::Ref { .. }
                    | Decision::InferredRef { .. }
                    | Decision::Slice { .. }
                    | Decision::NestedSlice { .. }
                    | Decision::Opt { .. }
                    | Decision::Box(_) => false,
                }
        })
    })
}

/// The raw twin is the callee's pristine body, so it is only a faithful target
/// when no parameter other than the counted ones is emitted in a safe form.
fn only_counted_params_convert(table: &super::DecisionTable, callee: LocalDefId) -> bool {
    use super::Decision;
    table.entries.iter().all(|(s, d)| {
        let converted = match d {
            Decision::Degraded(_) => false,
            Decision::Cursor { .. }
            | Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Slice { .. }
            | Decision::NestedSlice { .. }
            | Decision::Opt { .. }
            | Decision::Box(_) => true,
        };
        s.fn_did != callee
            || !matches!(s.kind, SubjectKind::Param { .. })
            || !converted
            || table.counted_void.contains_key(&(s.fn_did, s.hir_id))
    })
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum RootClass {
    /// Assigned exactly once from `malloc` / `calloc` (directly or through a
    /// transparent local wrapper), otherwise only null, never address-taken.
    Fresh,
    /// A parameter of the caller that is never reassigned or address-taken.
    Parameter,
    Other,
}

/// Two argument roots are distinct allocations when one is a fresh allocation
/// of this call and the other is another fresh allocation or a value that
/// existed before it (a stable parameter). Anything else is unproved.
fn disjoint_roots<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: LocalDefId,
    left: &'tcx Expr<'tcx>,
    right: &'tcx Expr<'tcx>,
) -> bool {
    let (Root::Value(a), Root::Value(b)) = (value_root(left), value_root(right)) else {
        return false;
    };
    if a == b {
        return false;
    }
    let facts = LocalFacts::collect(tcx, caller);
    matches!(
        (facts.class(tcx, caller, a), facts.class(tcx, caller, b)),
        (RootClass::Fresh, RootClass::Fresh)
            | (RootClass::Fresh, RootClass::Parameter)
            | (RootClass::Parameter, RootClass::Fresh)
    )
}

/// Per-local facts of one body: every value written to the local (its `let`
/// initializer and every assignment), and whether its address is ever taken.
struct LocalFacts<'tcx> {
    written: FxHashMap<HirId, Vec<&'tcx Expr<'tcx>>>,
    addressed: rustc_hash::FxHashSet<HirId>,
    closures: bool,
}
impl<'tcx> LocalFacts<'tcx> {
    fn collect(tcx: TyCtxt<'tcx>, owner: LocalDefId) -> Self {
        struct Walk<'tcx> {
            tcx: TyCtxt<'tcx>,
            owner: LocalDefId,
            facts: LocalFacts<'tcx>,
        }
        impl<'tcx> Visitor<'tcx> for Walk<'tcx> {
            fn visit_local(&mut self, local: &'tcx rustc_hir::LetStmt<'tcx>) {
                if let PatKind::Binding(mode, id, _, _) = local.pat.kind {
                    if mode.0 != rustc_ast::ByRef::No {
                        self.facts.addressed.insert(id);
                    }
                    if let Some(init) = local.init {
                        self.facts.written.entry(id).or_default().push(init);
                    }
                }
                intravisit::walk_local(self, local);
            }

            fn visit_pat(&mut self, p: &'tcx rustc_hir::Pat<'tcx>) {
                if let PatKind::Binding(mode, id, _, _) = p.kind
                    && mode.0 != rustc_ast::ByRef::No
                {
                    self.facts.addressed.insert(id);
                }
                intravisit::walk_pat(self, p);
            }

            fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
                let local_of = |e: &Expr<'_>| match e.kind {
                    ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) => match path.res {
                        rustc_hir::def::Res::Local(id) => Some(id),
                        _ => None,
                    },
                    _ => None,
                };
                match e.kind {
                    ExprKind::Assign(lhs, rhs, _) => {
                        if let Some(id) = local_of(lhs) {
                            self.facts.written.entry(id).or_default().push(rhs);
                        }
                    }
                    ExprKind::AssignOp(_, lhs, _) => {
                        if let Some(id) = local_of(lhs) {
                            self.facts.written.entry(id).or_default().push(e);
                        }
                    }
                    ExprKind::AddrOf(_, _, inner) => {
                        if let Some(id) = local_of(inner) {
                            self.facts.addressed.insert(id);
                        }
                    }
                    ExprKind::Closure(..) => self.facts.closures = true,
                    _ => {}
                }
                if local_of(e).is_some()
                    && !self.tcx.typeck(self.owner).expr_adjustments(e).is_empty()
                {
                    // An auto-ref adjustment is an address taken without syntax.
                    self.facts.addressed.insert(local_of(e).unwrap());
                }
                intravisit::walk_expr(self, e);
            }
        }
        let mut walk = Walk {
            tcx,
            owner,
            facts: LocalFacts {
                written: FxHashMap::default(),
                addressed: rustc_hash::FxHashSet::default(),
                closures: false,
            },
        };
        walk.visit_expr(tcx.hir_body_owned_by(owner).value);
        walk.facts
    }

    fn class(&self, tcx: TyCtxt<'tcx>, owner: LocalDefId, id: HirId) -> RootClass {
        if self.closures || self.addressed.contains(&id) {
            return RootClass::Other;
        }
        let written = self.written.get(&id).map(Vec::as_slice).unwrap_or(&[]);
        let is_param = tcx
            .hir_body_owned_by(owner)
            .params
            .iter()
            .any(|p| matches!(p.pat.kind, PatKind::Binding(_, pid, _, _) if pid == id));
        if is_param {
            return if written.is_empty() {
                RootClass::Parameter
            } else {
                RootClass::Other
            };
        }
        let allocations = written
            .iter()
            .filter(|e| is_allocation_call(tcx, owner, e))
            .count();
        let nulls = written.iter().filter(|e| is_null_literal(e)).count();
        if allocations == 1 && allocations + nulls == written.len() && written.len() <= 2 {
            RootClass::Fresh
        } else {
            RootClass::Other
        }
    }
}

fn is_null_literal(e: &Expr<'_>) -> bool {
    matches!(strip_casts(e).kind, ExprKind::Lit(lit) if matches!(lit.node, rustc_ast::LitKind::Int(v, _) if v.get() == 0))
}

/// `malloc(..)` / `calloc(..)` (a foreign item), or a local function whose whole
/// body is `return malloc(..)` / `return calloc(..)` (lodepng's `lodepng_malloc`).
fn is_allocation_call(tcx: TyCtxt<'_>, owner: LocalDefId, e: &Expr<'_>) -> bool {
    let ExprKind::Call(callee, _) = strip_casts(e).kind else { return false };
    let ExprKind::Path(path) = &callee.kind else { return false };
    let rustc_hir::def::Res::Def(rustc_hir::def::DefKind::Fn, did) =
        tcx.typeck(owner).qpath_res(path, callee.hir_id)
    else {
        return false;
    };
    if tcx.is_foreign_item(did) {
        return matches!(tcx.item_name(did).as_str(), "malloc" | "calloc");
    }
    let Some(local) = did.as_local() else { return false };
    if !tcx.hir_maybe_body_owned_by(local).is_some() {
        return false;
    }
    let body = tcx.hir_body_owned_by(local).value;
    let ExprKind::Block(block, _) = body.kind else { return false };
    let returned = match (block.stmts, block.expr) {
        ([], Some(tail)) => tail,
        ([stmt], None) => match stmt.kind {
            rustc_hir::StmtKind::Semi(e) | rustc_hir::StmtKind::Expr(e) => e,
            _ => return false,
        },
        _ => return false,
    };
    let value = match returned.kind {
        ExprKind::Ret(Some(value)) => value,
        _ => returned,
    };
    let ExprKind::Call(inner, _) = strip_casts(value).kind else { return false };
    let ExprKind::Path(inner_path) = &inner.kind else { return false };
    matches!(
        tcx.typeck(local).qpath_res(inner_path, inner.hir_id),
        rustc_hir::def::Res::Def(rustc_hir::def::DefKind::Fn, inner_did)
            if tcx.is_foreign_item(inner_did)
                && matches!(tcx.item_name(inner_did).as_str(), "malloc" | "calloc")
    )
}

/// Record one placed byte-view adapter into its call's plan (seam pass 3).
pub(crate) fn record_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    table: &super::DecisionTable,
    calls: &mut std::collections::BTreeMap<(u32, u32, u32), CallPlan>,
    site: &super::emitability::CallSite,
    callee: LocalDefId,
    index: usize,
    spec: &super::seam::GlueSpec,
) {
    let Some(counted) = spec.counted_byte else { return };
    if counted.route == Route::Handle {
        return;
    }
    let Some((param, contract)) = contract_at(table, callee, index) else { return };
    let body = tcx.hir_body_owned_by(site.caller).value;
    let count_form = find_expr(body, site.span)
        .and_then(|call| match strip_casts(call).kind {
            ExprKind::Call(_, args) => args.get(contract.count_index),
            _ => None,
        })
        .map(|count| count_form(tcx, site.caller, count).receipt())
        .unwrap_or_else(|| "bytes".to_owned());
    let count_form = contract
        .width
        .as_ref()
        .map_or(count_form, super::binn_counted::WidthTable::receipt);
    let key = (
        site.caller.local_def_index.as_u32(),
        site.span.lo().0,
        site.span.hi().0,
    );
    let call = calls.entry(key).or_insert_with(|| CallPlan {
        owner_class: crate::bo_rewriter::bridge_receipt::SignatureClassId::of(callee),
        caller: site.caller,
        callee,
        call_span: site.span,
        count_index: contract.count_index,
        route: counted.route,
        bridged: Vec::new(),
        count_form,
    });
    let Some(bridge) = render_bridge(spec, counted, "") else { return };
    if call.bridged.iter().all(|b| b.index != counted.arg_index) {
        call.bridged.push(BridgedArg {
            index: counted.arg_index,
            param,
            element: counted.element,
            mutable: spec.mutable,
            bridge,
        });
        call.bridged.sort_by_key(|b| b.index);
    }
}
/// A call where a CONVERTED position's storage root (`&mut local`, a local
/// pointer, a place rooted at a local) is also the root of an argument at a
/// RAW callee position: the view would live beside a raw alias of the same
/// storage for the whole call. When every converted position's argument
/// coerces to the raw parameter (a raw expression, or a plain reference of the
/// same pointee), the call takes the pristine raw twin. Returns the converted
/// positions' indices.
pub(crate) fn aliased_storage_twin(
    tcx: TyCtxt<'_>,
    table: &super::DecisionTable,
    site: &super::emitability::CallSite,
    callee: LocalDefId,
    positions: &[(usize, super::seam::Form, super::seam::Form)],
) -> Option<Result<Vec<usize>, super::seam::SeamBlock>> {
    use super::seam::Form;
    // A position whose callee parameter stays raw is not a view: only a
    // safe expected form forms one beside the alias.
    let positions = positions
        .iter()
        .filter(|(_, expected, _)| *expected != Form::Raw)
        .map(|(i, _, found)| (*i, *found))
        .collect::<Vec<_>>();
    if positions.is_empty() {
        return None;
    }
    let converted: rustc_hash::FxHashSet<usize> = positions.iter().map(|(i, _)| *i).collect();
    let root_of = |index: usize| {
        site.args
            .iter()
            .find(|a| a.index == index)
            .and_then(|a| a.shape.place_root())
    };
    let aliased = positions.iter().any(|(i, _)| {
        let Some(root) = root_of(*i) else { return false };
        site.args.iter().any(|other| {
            !converted.contains(&other.index) && other.shape.place_root() == Some(root)
        })
    });
    if !aliased {
        return None;
    }
    let coercible = positions.iter().all(|(_, found)| match found {
        Form::Raw | Form::Ref { .. } => true,
        Form::Slice { .. } | Form::Opt { .. } | Form::Cursor { .. } | Form::NestedSlice { .. } => {
            false
        }
    });
    if !coercible {
        return None;
    }
    // The twin is the pristine body; without a leaf body it cannot be
    // emitted, and the aliased call holds typed instead.
    Some(if twin_is_a_leaf(tcx, table, callee) {
        Ok(positions.iter().map(|(i, _)| *i).collect())
    } else {
        Err(super::seam::SeamBlock::SiteOverlap)
    })
}

/// The plan row for an aliased-storage call: every converted position keeps
/// its original argument and the call is renamed to the raw twin.
pub(crate) fn record_alias_twin(
    table: &super::DecisionTable,
    calls: &mut std::collections::BTreeMap<(u32, u32, u32), CallPlan>,
    site: &super::emitability::CallSite,
    callee: LocalDefId,
    indices: &[usize],
) {
    let bridged = indices
        .iter()
        .filter_map(|index| {
            let param = table.entries.iter().find_map(|(s, _)| {
                (s.fn_did == callee
                    && matches!(s.kind, SubjectKind::Param { hir_index } if hir_index == *index))
                .then_some(s.hir_id)
            })?;
            Some(BridgedArg {
                index: *index,
                param,
                element: ByteElement::Read,
                mutable: false,
                bridge: String::new(),
            })
        })
        .collect::<Vec<_>>();
    if bridged.is_empty() {
        return;
    }
    let key = (
        site.caller.local_def_index.as_u32(),
        site.span.lo().0,
        site.span.hi().0,
    );
    calls.entry(key).or_insert_with(|| CallPlan {
        owner_class: crate::bo_rewriter::bridge_receipt::SignatureClassId::of(callee),
        caller: site.caller,
        callee,
        call_span: site.span,
        count_index: 0,
        route: Route::RawTwin,
        bridged,
        count_form: "aliased-storage".to_owned(),
    });
}

/// A converted `&mut` position whose argument is a pure place borrow of a
/// local (`&mut local`, or a reference local reborrowed), while some OTHER
/// argument of the same call reads that local: json.h's
/// `json_get_value_size(&mut state, (f & state.flags_bitset) as i32)`. In C
/// the address is taken and the read follows; with the view the borrow would
/// be live across the read (E0503). Every unconverted argument is hoisted
/// into a `let` before the call — the address-of has no effect, so the order
/// of effects is the input's. Returns the converted positions.
pub(crate) fn aliased_read_hoist(
    tcx: TyCtxt<'_>,
    site: &super::emitability::CallSite,
    positions: &[(usize, super::seam::Form, super::seam::Form)],
) -> Option<Vec<usize>> {
    use super::{emitability::ArgShape, seam::Form};
    let body = tcx.hir_body_owned_by(site.caller).value;
    let ExprKind::Call(_, args) = find_expr(body, site.span).map(|call| strip_casts(call).kind)?
    else {
        return None;
    };
    if args.iter().any(|argument| argument.span.from_expansion()) {
        return None;
    }
    let converted: rustc_hash::FxHashSet<usize> = positions.iter().map(|(i, _, _)| *i).collect();
    let mut roots = Vec::new();
    for (index, expected, _) in positions {
        if !matches!(
            expected,
            Form::Ref { mutable: true }
                | Form::Slice { mutable: true }
                | Form::Opt { mutable: true, .. }
        ) {
            continue;
        }
        let shape = site.args.iter().find(|a| a.index == *index)?.shape;
        // Only a pure place borrow may be evaluated after the other arguments.
        let root = match shape {
            ArgShape::AddrOf {
                mutable: true,
                base: Some(base),
                through_deref: false,
            } => base,
            ArgShape::BareLocal(base) => base,
            _ => continue,
        };
        roots.push(root);
    }
    if roots.is_empty() {
        return None;
    }
    let reads = args.iter().enumerate().any(|(i, argument)| {
        !converted.contains(&i) && roots.iter().any(|root| mentions_local(argument, *root))
    });
    reads.then(|| positions.iter().map(|(i, _, _)| *i).collect())
}

fn mentions_local(expr: &Expr<'_>, local: HirId) -> bool {
    struct Mentions {
        local: HirId,
        found: bool,
    }
    impl<'v> Visitor<'v> for Mentions {
        fn visit_expr(&mut self, e: &'v Expr<'v>) {
            if let ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = e.kind
                && path.res == rustc_hir::def::Res::Local(self.local)
            {
                self.found = true;
            }
            intravisit::walk_expr(self, e);
        }
    }
    let mut visitor = Mentions {
        local,
        found: false,
    };
    visitor.visit_expr(expr);
    visitor.found
}

/// The plan row for a hoisted call: the converted positions keep their
/// arguments in the call, every other argument moves into a `let` before it.
pub(crate) fn record_hoist(
    table: &super::DecisionTable,
    calls: &mut std::collections::BTreeMap<(u32, u32, u32), CallPlan>,
    site: &super::emitability::CallSite,
    callee: LocalDefId,
    indices: &[usize],
) {
    let bridged = indices
        .iter()
        .filter_map(|index| {
            let param = table.entries.iter().find_map(|(s, _)| {
                (s.fn_did == callee
                    && matches!(s.kind, SubjectKind::Param { hir_index } if hir_index == *index))
                .then_some(s.hir_id)
            })?;
            Some(BridgedArg {
                index: *index,
                param,
                element: ByteElement::Read,
                mutable: true,
                bridge: String::new(),
            })
        })
        .collect::<Vec<_>>();
    if bridged.is_empty() {
        return;
    }
    let key = (
        site.caller.local_def_index.as_u32(),
        site.span.lo().0,
        site.span.hi().0,
    );
    calls.entry(key).or_insert_with(|| CallPlan {
        owner_class: crate::bo_rewriter::bridge_receipt::SignatureClassId::of(callee),
        caller: site.caller,
        callee,
        call_span: site.span,
        count_index: 0,
        route: Route::Hoist,
        bridged,
        count_form: "aliased-read".to_owned(),
    });
}

fn contract_at(
    table: &super::DecisionTable,
    callee: LocalDefId,
    index: usize,
) -> Option<(HirId, &Contract)> {
    use super::Decision;
    table.entries.iter().find_map(|(s, d)| {
        if s.fn_did != callee
            || !matches!(s.kind, SubjectKind::Param { hir_index } if hir_index == index)
        {
            return None;
        }
        let c = table.counted_void.get(&(s.fn_did, s.hir_id))?;
        let live = if c.handle.is_some() {
            match d {
                Decision::Ref { .. } | Decision::InferredRef { .. } => true,
                Decision::Opt { slice, .. } => !slice,
                Decision::Slice { .. }
                | Decision::NestedSlice { .. }
                | Decision::Cursor { .. }
                | Decision::Box(_)
                | Decision::Degraded(_) => false,
            }
        } else {
            slice_edits(d).is_some()
        };
        live.then_some((s.hir_id, c))
    })
}

/// Snapshot every counted call: `(|__crat_cv_0, ..| callee(..))(a0, ..)`; route
/// every unproved two-position call to the callee's pristine raw twin and emit
/// that twin once per callee.
///
/// Runs after the argument seams. A bridged argument whose callee subject was
/// withheld is passed through unchanged; a call with no surviving bridged
/// argument is left as it is.
pub(crate) fn graft_calls(
    calls: &[CallPlan],
    reverts: &crate::bo_rewriter::ast_transform::RevertSet,
    guard: &mut crate::bo_rewriter::ast_transform::Composition,
    krate: &mut rustc_ast::Crate,
    pristine: &rustc_ast::Crate,
    global_map: &rustc_ast::node_id::NodeMap<LocalDefId>,
) -> Result<(), String> {
    let mut by_span: FxHashMap<(u32, u32), (&CallPlan, Vec<&BridgedArg>)> = FxHashMap::default();
    for call in calls.iter().filter(|call| reverts.keeps(call.owner_class)) {
        let kept = call
            .bridged
            .iter()
            .filter(|b| reverts.keeps_subject(call.callee, b.param))
            .collect::<Vec<_>>();
        if kept.is_empty() {
            continue;
        }
        // The twin and its callers are ONE unit: a callee whose emitted
        // signature is the input's (its class withheld by any route) keeps
        // its original calls — the twin would not be printed beside an
        // unedited item, and the renamed calls would dangle (E0425).
        if call.route == Route::RawTwin
            && !signature_converted(krate, pristine, global_map, call.callee)
        {
            continue;
        }
        let key = (call.call_span.lo().0, call.call_span.hi().0);
        if by_span.insert(key, (call, kept)).is_some() {
            return Err(format!(
                "multiple counted-void call plans target call span {}..{}",
                key.0, key.1
            ));
        }
    }
    if by_span.is_empty() {
        return Ok(());
    }
    let mut visitor = CallGraft {
        calls: &by_span,
        guard,
        consumed: rustc_hash::FxHashSet::default(),
        failure: None,
        unsafe_fn: false,
        yielded: Vec::new(),
        twins: std::collections::BTreeMap::new(),
    };
    rustc_ast::mut_visit::MutVisitor::visit_crate(&mut visitor, krate);
    if let Some(why) = visitor.failure {
        return Err(why);
    }
    let unmatched = by_span
        .keys()
        .filter(|key| !visitor.consumed.contains(key))
        .copied()
        .collect::<Vec<_>>();
    if !unmatched.is_empty() {
        return Err(format!("unmatched counted-void call spans: {unmatched:?}"));
    }
    for (_, (callee, name)) in visitor.twins {
        insert_raw_twin(krate, pristine, global_map, callee, &name)?;
    }
    Ok(())
}

/// Clone the callee's PRISTINE item (the input's body, before any edit), rename
/// it to the raw twin, and place it right after the converted item.
/// Does the callee's item in the emitted crate carry a signature other than
/// the pristine one? (`pprust` of the `fn` signature, both trees.)
fn signature_converted(
    krate: &rustc_ast::Crate,
    pristine: &rustc_ast::Crate,
    global_map: &rustc_ast::node_id::NodeMap<LocalDefId>,
    callee: LocalDefId,
) -> bool {
    fn find<'a>(
        items: &'a [rustc_ast::ptr::P<rustc_ast::Item>],
        global_map: &rustc_ast::node_id::NodeMap<LocalDefId>,
        callee: LocalDefId,
    ) -> Option<&'a rustc_ast::Item> {
        for item in items {
            if global_map.get(&item.id) == Some(&callee)
                && matches!(item.kind, rustc_ast::ItemKind::Fn(_))
            {
                return Some(item);
            }
            if let rustc_ast::ItemKind::Mod(_, _, rustc_ast::ModKind::Loaded(inner, ..)) =
                &item.kind
                && let Some(found) = find(inner, global_map, callee)
            {
                return Some(found);
            }
        }
        None
    }
    let sig = |item: &rustc_ast::Item| match &item.kind {
        rustc_ast::ItemKind::Fn(function) => {
            let decl = &function.sig.decl;
            let inputs = decl
                .inputs
                .iter()
                .map(|param| rustc_ast_pretty::pprust::ty_to_string(&param.ty))
                .collect::<Vec<_>>()
                .join(", ");
            let output = match &decl.output {
                rustc_ast::FnRetTy::Default(_) => String::new(),
                rustc_ast::FnRetTy::Ty(ty) => rustc_ast_pretty::pprust::ty_to_string(ty),
            };
            Some(format!("({inputs}) -> {output}"))
        }
        _ => None,
    };
    match (
        find(&krate.items, global_map, callee).and_then(sig),
        find(&pristine.items, global_map, callee).and_then(sig),
    ) {
        (Some(emitted), Some(original)) => emitted != original,
        _ => false,
    }
}

fn insert_raw_twin(
    krate: &mut rustc_ast::Crate,
    pristine: &rustc_ast::Crate,
    global_map: &rustc_ast::node_id::NodeMap<LocalDefId>,
    callee: LocalDefId,
    name: &str,
) -> Result<(), String> {
    fn find<'a>(
        items: &'a [rustc_ast::ptr::P<rustc_ast::Item>],
        global_map: &rustc_ast::node_id::NodeMap<LocalDefId>,
        callee: LocalDefId,
    ) -> Option<&'a rustc_ast::Item> {
        for item in items {
            if global_map.get(&item.id) == Some(&callee)
                && matches!(item.kind, rustc_ast::ItemKind::Fn(_))
            {
                return Some(item);
            }
            if let rustc_ast::ItemKind::Mod(_, _, rustc_ast::ModKind::Loaded(inner, ..)) =
                &item.kind
                && let Some(found) = find(inner, global_map, callee)
            {
                return Some(found);
            }
        }
        None
    }
    fn place(
        items: &mut ThinVec<rustc_ast::ptr::P<rustc_ast::Item>>,
        global_map: &rustc_ast::node_id::NodeMap<LocalDefId>,
        callee: LocalDefId,
        twin: &rustc_ast::Item,
    ) -> bool {
        for index in 0..items.len() {
            if global_map.get(&items[index].id) == Some(&callee)
                && matches!(items[index].kind, rustc_ast::ItemKind::Fn(_))
            {
                items.insert(index + 1, rustc_ast::ptr::P(twin.clone()));
                return true;
            }
            if let rustc_ast::ItemKind::Mod(_, _, rustc_ast::ModKind::Loaded(inner, ..)) =
                &mut items[index].kind
                && place(inner, global_map, callee, twin)
            {
                return true;
            }
        }
        false
    }
    let Some(original) = find(&pristine.items, global_map, callee) else {
        return Err(format!(
            "counted-void raw twin: pristine item for {callee:?} not found"
        ));
    };
    let mut twin = original.clone();
    let rustc_ast::ItemKind::Fn(function) = &mut twin.kind else { unreachable!() };
    function.ident = rustc_span::Ident::new(rustc_span::Symbol::intern(name), function.ident.span);
    twin.vis = rustc_ast::Visibility {
        kind: rustc_ast::VisibilityKind::Inherited,
        span: rustc_span::DUMMY_SP,
        tokens: None,
    };
    if !place(&mut krate.items, global_map, callee, &twin) {
        return Err(format!(
            "counted-void raw twin: converted item for {callee:?} not found"
        ));
    }
    Ok(())
}

use thin_vec::ThinVec;

struct CallGraft<'a> {
    calls: &'a FxHashMap<(u32, u32), (&'a CallPlan, Vec<&'a BridgedArg>)>,
    guard: &'a mut crate::bo_rewriter::ast_transform::Composition,
    consumed: rustc_hash::FxHashSet<(u32, u32)>,
    failure: Option<String>,
    unsafe_fn: bool,
    /// Calls yielded to another family's replacement (R410-2(d)).
    yielded: Vec<((u32, u32), rustc_span::Span)>,
    /// Callees whose raw twin must be emitted, with the twin's name.
    twins: std::collections::BTreeMap<u32, (LocalDefId, String)>,
}

impl rustc_ast::mut_visit::MutVisitor for CallGraft<'_> {
    fn visit_item(&mut self, item: &mut rustc_ast::Item) {
        let previous = self.unsafe_fn;
        if let rustc_ast::ItemKind::Fn(function) = &item.kind {
            self.unsafe_fn = matches!(function.sig.header.safety, rustc_ast::Safety::Unsafe(_));
        }
        rustc_ast::mut_visit::walk_item(self, item);
        self.unsafe_fn = previous;
    }

    fn visit_assoc_item(
        &mut self,
        item: &mut rustc_ast::AssocItem,
        ctxt: rustc_ast::visit::AssocCtxt,
    ) {
        let previous = self.unsafe_fn;
        if let rustc_ast::AssocItemKind::Fn(function) = &item.kind {
            self.unsafe_fn = matches!(function.sig.header.safety, rustc_ast::Safety::Unsafe(_));
        }
        rustc_ast::mut_visit::walk_assoc_item(self, item, ctxt);
        self.unsafe_fn = previous;
    }

    fn visit_expr(&mut self, e: &mut rustc_ast::Expr) {
        if self.failure.is_some() {
            return;
        }
        if e.span.is_dummy() {
            rustc_ast::mut_visit::walk_expr(self, e);
            return;
        }
        let key = (e.span.lo().0, e.span.hi().0);
        let Some((call, kept)) = self.calls.get(&key) else {
            rustc_ast::mut_visit::walk_expr(self, e);
            return;
        };
        // Inner grafts first: an argument may itself carry a snapshotted call.
        rustc_ast::mut_visit::walk_expr(self, e);
        if self.failure.is_some() {
            return;
        }
        let rustc_ast::ExprKind::Call(callee, args) = &mut e.kind else {
            // R410-2(d): a call another family's edit already replaced (an
            // A5 / PAIR raw-view snapshot wraps the call in a block) — the
            // counted-void plan YIELDS the call: it is consumed, unplaced,
            // and its class pays at the compile gate rather than the whole
            // round failing. A node no family claimed is still an error.
            if self.guard.holder(e.id).is_some() {
                self.consumed.insert(key);
                self.yielded.push((key, e.span));
                return;
            }
            self.failure = Some(format!(
                "counted-void call at {}..{} resolved to a non-call AST node",
                key.0, key.1
            ));
            return;
        };
        if call.route == Route::RawTwin {
            // The arguments stay exactly as written; only the callee name moves.
            let rustc_ast::ExprKind::Path(None, path) = &mut callee.kind else {
                self.failure = Some(format!(
                    "counted-void raw-twin call at {}..{} has no plain path callee",
                    key.0, key.1
                ));
                return;
            };
            let Some(last) = path.segments.last_mut() else {
                self.failure = Some("counted-void raw-twin call: empty callee path".to_owned());
                return;
            };
            let name = raw_twin_name(last.ident.name.as_str());
            if !self.guard.claim(e.id, e.span, "counted-void-call") {
                self.failure = Some(format!(
                    "counted-void call at {}..{} collided with another AST transform",
                    key.0, key.1
                ));
                return;
            }
            last.ident = rustc_span::Ident::new(rustc_span::Symbol::intern(&name), last.ident.span);
            self.twins
                .insert(call.callee.local_def_index.as_u32(), (call.callee, name));
            self.consumed.insert(key);
            return;
        }
        if call.route == Route::Hoist {
            self.graft_hoist(e, key, kept);
            return;
        }
        let arity = args.len();
        if call.count_index >= arity || kept.iter().any(|b| b.index >= arity) {
            self.failure = Some(format!(
                "counted-void call at {}..{} has arity {arity}, outside its plan",
                key.0, key.1
            ));
            return;
        }
        const CALLEE: &str = "__crat_cv_callee";
        let params = (0..arity).map(placeholder).collect::<Vec<_>>().join(", ");
        let body_args = (0..arity)
            .map(|i| {
                kept.iter()
                    .find(|b| b.index == i)
                    .map_or_else(|| placeholder(i), |b| b.bridge.clone())
            })
            .collect::<Vec<_>>()
            .join(", ");
        let body = crate::bo_rewriter::mechanical_receipt::present_unsafe_text(
            format!("{CALLEE}({body_args})"),
            self.unsafe_fn,
        );
        let originals = (0..arity)
            .map(|i| format!("{}_orig", placeholder(i)))
            .collect::<Vec<_>>()
            .join(", ");
        let text = format!("(|{params}| {body})({originals})");
        let mut parsed = match crate::bo_rewriter::ast_transform::graft_expr(&text) {
            Ok(parsed) => parsed,
            Err(_) => {
                self.failure = Some(format!(
                    "counted-void call at {}..{} did not round-trip: {text}",
                    key.0, key.1
                ));
                return;
            }
        };
        let mut subst = Substitute {
            callee: Some(std::mem::replace(callee, rustc_ast::ptr::P(dummy_expr()))),
            originals: std::mem::take(args).into_iter().map(Some).collect(),
            substituted: 0,
        };
        rustc_ast::mut_visit::MutVisitor::visit_expr(&mut subst, &mut parsed);
        if subst.substituted != arity + 1
            || subst.callee.is_some()
            || subst.originals.iter().any(Option::is_some)
        {
            self.failure = Some(format!(
                "counted-void call at {}..{} substituted {} of {} operands",
                key.0,
                key.1,
                subst.substituted,
                arity + 1
            ));
            return;
        }
        if !self.guard.claim(e.id, e.span, "counted-void-call") {
            self.failure = Some(format!(
                "counted-void call at {}..{} collided with another AST transform",
                key.0, key.1
            ));
            return;
        }
        self.consumed.insert(key);
        e.kind = parsed.kind;
    }
}

impl CallGraft<'_> {
    /// `{ let __crat_cv_i = <arg i>; .. callee(<converted args>, __crat_cv_i, ..) }`:
    /// the unconverted arguments are evaluated, in order, before the call
    /// forms its `&mut` borrow.
    fn graft_hoist(&mut self, e: &mut rustc_ast::Expr, key: (u32, u32), kept: &[&BridgedArg]) {
        let rustc_ast::ExprKind::Call(callee, args) = &mut e.kind else {
            return;
        };
        let arity = args.len();
        if kept.iter().any(|b| b.index >= arity) {
            self.failure = Some(format!(
                "counted-void hoist at {}..{} has arity {arity}, outside its plan",
                key.0, key.1
            ));
            return;
        }
        let converted = |i: usize| kept.iter().any(|b| b.index == i);
        let lets = (0..arity)
            .filter(|i| !converted(*i))
            .map(|i| format!("let {} = {}_orig;", placeholder(i), placeholder(i)))
            .collect::<Vec<_>>()
            .join(" ");
        let call_args = (0..arity)
            .map(|i| {
                if converted(i) {
                    format!("{}_orig", placeholder(i))
                } else {
                    placeholder(i)
                }
            })
            .collect::<Vec<_>>()
            .join(", ");
        let call = crate::bo_rewriter::mechanical_receipt::present_unsafe_text(
            format!("__crat_cv_callee({call_args})"),
            self.unsafe_fn,
        );
        let text = format!("{{ {lets} {call} }}");
        let mut parsed = match crate::bo_rewriter::ast_transform::graft_expr(&text) {
            Ok(parsed) => parsed,
            Err(_) => {
                self.failure = Some(format!(
                    "counted-void hoist at {}..{} did not round-trip: {text}",
                    key.0, key.1
                ));
                return;
            }
        };
        let mut subst = Substitute {
            callee: Some(std::mem::replace(callee, rustc_ast::ptr::P(dummy_expr()))),
            originals: std::mem::take(args).into_iter().map(Some).collect(),
            substituted: 0,
        };
        rustc_ast::mut_visit::MutVisitor::visit_expr(&mut subst, &mut parsed);
        if subst.substituted != arity + 1
            || subst.callee.is_some()
            || subst.originals.iter().any(Option::is_some)
        {
            self.failure = Some(format!(
                "counted-void hoist at {}..{} substituted {} of {} operands",
                key.0,
                key.1,
                subst.substituted,
                arity + 1
            ));
            return;
        }
        if !self.guard.claim(e.id, e.span, "counted-void-call") {
            self.failure = Some(format!(
                "counted-void hoist at {}..{} collided with another AST transform",
                key.0, key.1
            ));
            return;
        }
        self.consumed.insert(key);
        e.kind = parsed.kind;
    }
}

fn dummy_expr() -> rustc_ast::Expr {
    rustc_ast::Expr {
        id: rustc_ast::node_id::DUMMY_NODE_ID,
        kind: rustc_ast::ExprKind::Tup(Default::default()),
        span: rustc_span::DUMMY_SP,
        attrs: Default::default(),
        tokens: None,
    }
}

/// Move the callee and the original arguments into the parsed scaffold.
struct Substitute {
    callee: Option<rustc_ast::ptr::P<rustc_ast::Expr>>,
    originals: Vec<Option<rustc_ast::ptr::P<rustc_ast::Expr>>>,
    substituted: usize,
}
impl rustc_ast::mut_visit::MutVisitor for Substitute {
    fn visit_expr(&mut self, e: &mut rustc_ast::Expr) {
        if let rustc_ast::ExprKind::Path(None, path) = &e.kind
            && path.segments.len() == 1
        {
            let name = path.segments[0].ident.name;
            let name = name.as_str();
            let taken = if name == "__crat_cv_callee" {
                self.callee.take()
            } else if let Some(index) = name
                .strip_prefix("__crat_cv_")
                .and_then(|rest| rest.strip_suffix("_orig"))
                .and_then(|index| index.parse::<usize>().ok())
            {
                self.originals.get_mut(index).and_then(Option::take)
            } else {
                None
            };
            if let Some(taken) = taken {
                *e = *taken;
                self.substituted += 1;
                return;
            }
        }
        rustc_ast::mut_visit::walk_expr(self, e);
    }
}

/// The use edits of a counted view: a slice, or its optional twin.
fn slice_edits(decision: &super::Decision) -> Option<&[UseEdit]> {
    use super::Decision;
    match decision {
        Decision::Slice { uses, .. } => Some(uses),
        Decision::Opt {
            slice: true, uses, ..
        } => Some(uses),
        Decision::Opt { slice: false, .. }
        | Decision::Cursor { .. }
        | Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::NestedSlice { .. }
        | Decision::Box(_)
        | Decision::Degraded(_) => None,
    }
}
