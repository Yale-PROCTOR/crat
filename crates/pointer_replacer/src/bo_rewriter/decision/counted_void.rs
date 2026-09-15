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
    contract_at(table, callee, index).map(|(_, c)| c)
}

/// The closure-call snapshot's parameter name for one argument position.
pub(crate) fn placeholder(index: usize) -> String {
    format!("__crat_cv_{index}")
}

/// One byte-view adapter inside a snapshotted call.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct CountedByte {
    pub(crate) element: ByteElement,
    pub(crate) arg_index: usize,
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
    pub(crate) bridged: Vec<BridgedArg>,
    /// Typed receipt of the count argument's form (R397-4): `elements:<n>*size_of::<T>`
    /// when the byte count is an exact element count times an element size,
    /// else `bytes`. The emitted length is the count argument's exact value in
    /// both cases; nothing is fabricated.
    pub(crate) count_form: String,
}

pub(crate) fn render_bridge(spec: &super::seam::GlueSpec, counted: CountedByte) -> Option<String> {
    let super::seam::SeamLen::Licensed(count) = spec.len.as_ref()? else { return None };
    if spec.core != super::seam::GlueCore::FromRawParts || spec.optional || spec.unwrap.is_some() {
        return None;
    }
    let (pointer, ctor) = if spec.mutable {
        ("mut", "from_raw_parts_mut")
    } else {
        ("const", "from_raw_parts")
    };
    let text = placeholder(counted.arg_index);
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

/// The argument-level graft is the identity: the argument subtree stays where
/// it is and is moved into the closure call by [`graft_calls`], which owns the
/// whole call expression. The seam still claims the node, so the placement is
/// counted exactly once and a colliding transform is refused.
pub(crate) fn bridge_ast(argument: &rustc_ast::Expr) -> Option<rustc_ast::ExprKind> {
    Some(argument.kind.clone())
}

pub(crate) fn active<'a>(ctx: &super::Ctx<'a, '_>, s: &Subject) -> Option<&'a Contract> {
    use crate::bo_rewriter::additive::FamilyStage;
    (ctx.family_policy
        .enabled_for((s.fn_did, s.hir_id), FamilyStage::Declaration)
        && ctx
            .family_policy
            .enabled_for((s.fn_did, s.hir_id), FamilyStage::SliceUse))
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
enum Root {
    /// The value of this local: its referent is what the view covers.
    Value(HirId),
    /// This local's own storage is what the view covers.
    Storage(HirId),
    /// A loaded pointer, a call result, a literal: no subject's claim is at stake.
    Opaque,
}
fn value_root(e: &Expr<'_>) -> Root {
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
fn viewed_type<'tcx>(
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
fn thin(decision: &super::Decision) -> bool {
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
/// closure snapshot's count parameter, or a typed hold.
pub(crate) fn count_argument<'tcx>(
    tcx: TyCtxt<'tcx>,
    table: &super::DecisionTable,
    site: &super::emitability::CallSite,
    callee: LocalDefId,
    c: &Contract,
    arg_index: usize,
) -> Result<String, super::seam::SeamBlock> {
    use super::seam::SeamBlock;
    // Two byte views at one call may cover overlapping bytes: a program-defined
    // byte loop (unlike libc `memcpy`) is defined on overlap, so overlap is not
    // the input's fault, and one raw access under a live view is as forbidden
    // as two views. Without a disjointness proof, a call bridges one position
    // at most; a read+write callee therefore holds at every call.
    if site
        .args
        .iter()
        .filter(|argument| contract_at(table, callee, argument.index).is_some())
        .count()
        > 1
    {
        return Err(SeamBlock::SiteOverlap);
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
    root_rule(tcx, table, site.caller, argument, &form)?;
    Ok(placeholder(c.count_index))
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
    let Some((param, contract)) = contract_at(table, callee, index) else { return };
    let body = tcx.hir_body_owned_by(site.caller).value;
    let count_form = find_expr(body, site.span)
        .and_then(|call| match strip_casts(call).kind {
            ExprKind::Call(_, args) => args.get(contract.count_index),
            _ => None,
        })
        .map(|count| count_form(tcx, site.caller, count).receipt())
        .unwrap_or_else(|| "bytes".to_owned());
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
        bridged: Vec::new(),
        count_form,
    });
    let Some(bridge) = render_bridge(spec, counted) else { return };
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
fn contract_at(
    table: &super::DecisionTable,
    callee: LocalDefId,
    index: usize,
) -> Option<(HirId, &Contract)> {
    table.entries.iter().find_map(|(s, d)| {
        (s.fn_did == callee
            && matches!(s.kind,SubjectKind::Param{hir_index} if hir_index == index)
            && slice_edits(d).is_some())
        .then(|| {
            table
                .counted_void
                .get(&(s.fn_did, s.hir_id))
                .map(|c| (s.hir_id, c))
        })
        .flatten()
    })
}

/// Snapshot every counted call: `(|__crat_cv_0, ..| callee(..))(a0, ..)`.
///
/// Runs after the argument seams. A bridged argument whose callee subject was
/// withheld is passed through unchanged; a call with no surviving bridged
/// argument is left as it is.
pub(crate) fn graft_calls(
    calls: &[CallPlan],
    reverts: &crate::bo_rewriter::ast_transform::RevertSet,
    guard: &mut crate::bo_rewriter::ast_transform::Composition,
    krate: &mut rustc_ast::Crate,
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
    Ok(())
}

struct CallGraft<'a> {
    calls: &'a FxHashMap<(u32, u32), (&'a CallPlan, Vec<&'a BridgedArg>)>,
    guard: &'a mut crate::bo_rewriter::ast_transform::Composition,
    consumed: rustc_hash::FxHashSet<(u32, u32)>,
    failure: Option<String>,
    unsafe_fn: bool,
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
            self.failure = Some(format!(
                "counted-void call at {}..{} resolved to a non-call AST node",
                key.0, key.1
            ));
            return;
        };
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
