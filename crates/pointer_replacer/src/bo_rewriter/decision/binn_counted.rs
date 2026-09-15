//! binn's counted `void *` parameters (wave-6v2, seat addendum 403): the byte
//! count is a WIDTH the callee's own typed accesses fix.
//!
//! binn hands opaque pointers to helpers that read them at one width — the
//! header magic (`*(ptr as *mut c_uint)` in `binn_get_ptr_type`) — or at a
//! width selected by a sibling type parameter, one type per literal arm
//! (`match source_type { 33 => *(psource as *mut c_schar), 65 => .. }` in
//! `copy_int_value`). Neither carries a count argument, but both fix the extent
//! exactly: the callee accesses `size_of::<T>()` bytes at offset zero and
//! nothing else, so the view is `&[u8]` of that width and every read through it
//! is a checked prefix followed by a receipted unaligned read.
//!
//! The contract is [`super::counted_void::Contract`] with a [`WidthTable`]: the
//! parent lane's snapshot, seam and bridge machinery is called, not copied.
//! The count text a raw caller receives is the table over the snapshotted
//! discriminant (`match __crat_cv_k { 33 => size_of::<c_schar>(), .., _ => 0 }`)
//! or the constant width; nothing is fabricated. An unknown discriminant
//! selects the zero-length view, which is exactly the callee's own `_ =>` arm.
//!
//! Held, typed, in this build: writes through the cast, reads at an offset,
//! reads outside every arm of the discriminant match when arms exist, two
//! widths in one arm, a discriminant that is written, and every other use of
//! the parameter (pass-ons, casts that escape, returns). Never widened: a thin
//! caller root admits only when the literal discriminant selects a width equal
//! to the viewed place's size ([`root_rule`]).
use rustc_hash::FxHashMap;
use rustc_hir::{
    Expr, ExprKind, HirId, Node, PatKind,
    def::Res,
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{Ty, TyCtxt, TyKind, TypingEnv};

use super::{
    Subject, SubjectKind,
    counted_void::{ByteElement, Contract, Root, placeholder},
    emitability::UseEdit,
};

/// One width per literal of a sibling discriminant, or one constant width.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct WidthTable {
    /// The parameter index of the discriminant the width is selected by;
    /// `None` when every access uses the one type in `arms[0]`.
    pub(crate) discriminant: Option<usize>,
    /// `(literal, pointee type as spelled at the cast, size in bytes)`, in
    /// source order; a constant table has exactly one arm whose literal is
    /// unused.
    pub(crate) arms: Vec<(u128, String, u64)>,
}

impl WidthTable {
    /// The count text at a snapshotted call.
    pub(crate) fn render(&self) -> String {
        match self.discriminant {
            // An unknown width never renders: `count_argument` holds the site.
            None if self.arms.is_empty() => "0".to_owned(),
            None => format!("core::mem::size_of::<{}>()", self.arms[0].1),
            Some(k) => {
                let arms = self
                    .arms
                    .iter()
                    .map(|(literal, ty, _)| format!("{literal} => core::mem::size_of::<{ty}>()"))
                    .collect::<Vec<_>>()
                    .join(", ");
                // The trailing comma is the pretty-printer's spelling; the graft's
                // round trip compares non-whitespace text against it.
                format!("match {} {{ {arms}, _ => 0, }}", placeholder(k))
            }
        }
    }

    /// The typed receipt of the count's form.
    pub(crate) fn receipt(&self) -> String {
        match self.discriminant {
            None if self.arms.is_empty() => "width:inherited-unknown".to_owned(),
            None => format!("width:size_of::<{}>", self.arms[0].1),
            Some(k) => format!(
                "width-table:arg{k}:{{{}}}",
                self.arms
                    .iter()
                    .map(|(literal, ty, _)| format!("{literal}:{ty}"))
                    .collect::<Vec<_>>()
                    .join(",")
            ),
        }
    }

    /// No width is known here: a forward-only parameter whose pass-ons reach
    /// a raw or held position. Safe callers pass their own view through; a
    /// raw caller's site holds (`seam-len-unknown`).
    pub(crate) fn unknown() -> Self {
        Self {
            discriminant: None,
            arms: Vec::new(),
        }
    }

    pub(crate) fn is_unknown(&self) -> bool {
        self.arms.is_empty()
    }

    /// The same table keyed on another parameter index (a forwarder's own
    /// discriminant position).
    pub(crate) fn rekey(&self, discriminant: usize) -> Self {
        Self {
            discriminant: self.discriminant.map(|_| discriminant),
            arms: self.arms.clone(),
        }
    }

    /// The width in bytes a literal discriminant selects; the constant width
    /// when there is no discriminant; `None` when it cannot be known statically.
    fn width_for(&self, literal: Option<u128>) -> Option<u64> {
        match self.discriminant {
            None => self.arms.first().map(|(_, _, size)| *size),
            Some(_) => self
                .arms
                .iter()
                .find(|(arm, _, _)| Some(*arm) == literal)
                .map(|(_, _, size)| *size),
        }
    }
}

fn local_of(e: &Expr<'_>) -> Option<HirId> {
    match e.kind {
        ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) => match path.res {
            Res::Local(id) => Some(id),
            _ => None,
        },
        _ => None,
    }
}

fn literal_of(e: &Expr<'_>) -> Option<u128> {
    let e = strip_casts(e);
    match e.kind {
        ExprKind::Lit(lit) => match lit.node {
            rustc_ast::LitKind::Int(value, _) => Some(value.get()),
            _ => None,
        },
        _ => None,
    }
}

fn strip_casts<'tcx>(mut e: &'tcx Expr<'tcx>) -> &'tcx Expr<'tcx> {
    loop {
        match e.kind {
            ExprKind::Cast(inner, _) | ExprKind::DropTemps(inner) => e = inner,
            _ => return e,
        }
    }
}

/// Every use of one local and every write to any local in a body.
struct Uses<'tcx> {
    target: HirId,
    found: Vec<&'tcx Expr<'tcx>>,
    writes: FxHashMap<HirId, usize>,
    closures: bool,
}
impl<'tcx> Visitor<'tcx> for Uses<'tcx> {
    fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
        if local_of(e) == Some(self.target) {
            self.found.push(e);
        }
        match e.kind {
            ExprKind::Assign(lhs, _, _) | ExprKind::AssignOp(_, lhs, _) => {
                if let Some(id) = local_of(lhs) {
                    *self.writes.entry(id).or_default() += 1;
                }
            }
            ExprKind::AddrOf(_, rustc_hir::Mutability::Mut, place) => {
                if let Some(id) = local_of(place) {
                    *self.writes.entry(id).or_default() += 1;
                }
            }
            ExprKind::Closure(..) => self.closures = true,
            _ => {}
        }
        intravisit::walk_expr(self, e);
    }
}

/// The literal arm of a `match <sibling>` enclosing `e`, walking up through
/// blocks and expressions: `Some((sibling, literals))`, or `None` when no
/// enclosing match has a bare local scrutinee with a literal pattern.
fn enclosing_literal_arm(tcx: TyCtxt<'_>, e: &Expr<'_>) -> Option<(HirId, Vec<u128>)> {
    let mut id = e.hir_id;
    loop {
        let parent = tcx.parent_hir_node(id);
        match parent {
            Node::Arm(arm) => {
                let Node::Expr(matched) = tcx.parent_hir_node(arm.hir_id) else { return None };
                let ExprKind::Match(scrutinee, _, _) = matched.kind else { return None };
                let scrutinee = local_of(strip_casts(scrutinee))?;
                let mut literals = Vec::new();
                let mut patterns = vec![arm.pat];
                while let Some(pat) = patterns.pop() {
                    match pat.kind {
                        PatKind::Expr(lit) => match lit.kind {
                            rustc_hir::PatExprKind::Lit {
                                lit,
                                negated: false,
                            } => match lit.node {
                                rustc_ast::LitKind::Int(value, _) => literals.push(value.get()),
                                _ => return None,
                            },
                            _ => return None,
                        },
                        PatKind::Or(alternatives) => patterns.extend(alternatives),
                        _ => return None,
                    }
                }
                return Some((scrutinee, literals));
            }
            Node::Expr(e) => id = e.hir_id,
            Node::Stmt(s) => id = s.hir_id,
            Node::Block(b) => id = b.hir_id,
            Node::LetStmt(l) => id = l.hir_id,
            _ => return None,
        }
    }
}

/// Is `e` the operand of an assignment's left-hand side (a write)?
fn is_written(tcx: TyCtxt<'_>, e: &Expr<'_>) -> bool {
    match tcx.parent_hir_node(e.hir_id) {
        Node::Expr(parent) => match parent.kind {
            ExprKind::Assign(lhs, _, _) | ExprKind::AssignOp(_, lhs, _) => lhs.hir_id == e.hir_id,
            ExprKind::AddrOf(_, rustc_hir::Mutability::Mut, place) => place.hir_id == e.hir_id,
            _ => false,
        },
        _ => false,
    }
}

/// Is `e` (through casts and temporaries) the operand of a `return`, or the
/// value the enclosing body evaluates to?
fn is_returned_value(tcx: TyCtxt<'_>, e: &Expr<'_>) -> bool {
    let mut id = e.hir_id;
    loop {
        match tcx.parent_hir_node(id) {
            Node::Expr(parent) => match parent.kind {
                ExprKind::Ret(Some(operand)) => return operand.hir_id == id,
                ExprKind::Cast(inner, _) | ExprKind::DropTemps(inner) if inner.hir_id == id => {
                    id = parent.hir_id;
                }
                ExprKind::Block(block, _)
                    if block.hir_id == id || block.expr.is_some_and(|tail| tail.hir_id == id) =>
                {
                    id = parent.hir_id;
                }
                _ => return false,
            },
            Node::Block(block) => {
                if !block.expr.is_some_and(|tail| tail.hir_id == id) {
                    return false;
                }
                id = block.hir_id;
            }
            // The body's own value.
            Node::Item(_) | Node::ImplItem(_) | Node::TraitItem(_) => return true,
            _ => return false,
        }
    }
}

fn size_of<'tcx>(tcx: TyCtxt<'tcx>, owner: LocalDefId, ty: Ty<'tcx>) -> Option<u64> {
    tcx.layout_of(TypingEnv::post_analysis(tcx, owner).as_query_input(ty))
        .ok()
        .map(|layout| layout.size.bytes())
}

/// A typed-width read parameter's contract, or `None` (the R271-1 hold stands).
pub(crate) fn prove(tcx: TyCtxt<'_>, s: &Subject) -> Option<Contract> {
    if s.ptr_depth != 1 || !matches!(s.kind, SubjectKind::Param { .. }) {
        return None;
    }
    let Node::Pat(pat) = tcx.hir_node(s.hir_id) else { return None };
    let typeck = tcx.typeck(s.fn_did);
    if !super::void_pointee::has_void_pointee(tcx, typeck.pat_ty(pat), 1) {
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
    let own_index = params.iter().position(|p| *p == s.hir_id)?;
    let mut uses = Uses {
        target: s.hir_id,
        found: Vec::new(),
        writes: FxHashMap::default(),
        closures: false,
    };
    uses.visit_expr(body.value);
    if uses.closures || uses.writes.contains_key(&s.hir_id) {
        return None;
    }
    let name = s.param_name.as_ref()?;
    let sm = tcx.sess.source_map();
    let unsafe_fn = tcx
        .fn_sig(s.fn_did.to_def_id())
        .skip_binder()
        .skip_binder()
        .safety
        .is_unsafe();
    let mut nullable = false;
    let mut edits = Vec::new();
    // `(read expression, pointee type text, pointee size, enclosing literal arm)`
    let mut reads: Vec<(&Expr<'_>, String, u64, Option<(HirId, Vec<u128>)>)> = Vec::new();
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
                    bridge_kind: "binn-counted-null-test",
                });
            }
            ExprKind::Cast(operand, cast_ty) if operand.hir_id == use_.hir_id => {
                let TyKind::RawPtr(pointee, _) = typeck.expr_ty(parent).kind() else { return None };
                let Node::Expr(deref) = tcx.parent_hir_node(parent.hir_id) else { return None };
                let ExprKind::Unary(rustc_hir::UnOp::Deref, _) = deref.kind else { return None };
                if is_written(tcx, deref) || deref.span.from_expansion() {
                    return None;
                }
                let rustc_hir::TyKind::Ptr(mut_ty) = cast_ty.kind else { return None };
                let ty_text = sm.span_to_snippet(mut_ty.ty.span).ok()?;
                let size = size_of(tcx, s.fn_did, *pointee)?;
                reads.push((deref, ty_text, size, enclosing_literal_arm(tcx, deref)));
            }
            _ => return None,
        }
    }
    if reads.is_empty() {
        return None;
    }
    // R410-2(d): a width reader — every typed read is the value RETURNED
    // (`return *(p as *const u32)`) — is wave-6b's region shape, and the
    // region wins; this rule yields.
    if reads
        .iter()
        .all(|(deref, _, _, _)| is_returned_value(tcx, deref))
    {
        return None;
    }
    let width = if reads.iter().all(|(_, _, _, arm)| arm.is_none()) {
        let (_, ty, size, _) = &reads[0];
        if reads.iter().any(|(_, t, _, _)| t != ty) {
            return None;
        }
        WidthTable {
            discriminant: None,
            arms: vec![(0, ty.clone(), *size)],
        }
    } else {
        // Every read sits under a literal arm of ONE match over an unchanged
        // sibling parameter, and each literal selects exactly one type.
        let scrutinee = reads
            .iter()
            .find_map(|(_, _, _, arm)| arm.as_ref().map(|(s, _)| *s))?;
        let discriminant = params.iter().position(|p| *p == scrutinee)?;
        if discriminant == own_index || uses.writes.contains_key(&scrutinee) {
            return None;
        }
        let mut arms: Vec<(u128, String, u64)> = Vec::new();
        for (_, ty, size, arm) in &reads {
            let (arm_scrutinee, literals) = arm.as_ref()?;
            if *arm_scrutinee != scrutinee {
                return None;
            }
            for literal in literals {
                match arms.iter().find(|(l, _, _)| l == literal) {
                    Some((_, known, _)) if known != ty => return None,
                    Some(_) => {}
                    None => arms.push((*literal, ty.clone(), *size)),
                }
            }
        }
        WidthTable {
            discriminant: Some(discriminant),
            arms,
        }
    };
    let view = if nullable {
        format!("{name}.unwrap_or(&[])")
    } else {
        name.clone()
    };
    for (deref, ty, _, _) in &reads {
        edits.push(UseEdit {
            span: deref.span,
            replacement: crate::bo_rewriter::mechanical_receipt::present_unsafe_text(
                format!("{view}[..core::mem::size_of::<{ty}>()].as_ptr().cast::<{ty}>().read_unaligned()"),
                unsafe_fn,
            ),
            bridge_kind: "binn-counted-typed-read",
        });
    }
    Some(Contract {
        count_index: width.discriminant.unwrap_or(own_index),
        element: ByteElement::Read,
        nullable,
        width: Some(width),
        uses: edits,
    })
}

/// A forward-only `void *` parameter: its uses are null tests and pass-ons of
/// the bare binding as an argument of a LOCAL call. It takes the byte view.
/// Where every pass-on reaches a position that carries a typed-width contract,
/// the element and the width are inherited (re-keyed by the sibling the
/// forwarder passes as the discriminant), its seams are safe-to-safe and a raw
/// caller's count is the inherited width. Where a pass-on reaches a raw or
/// held position (R407-11, admitted), the width is UNKNOWN — a raw caller of
/// this forwarder holds at its seam — the element follows the parameter's own
/// mutability, and the pass-on is the seam's outbound R130 bridge at that
/// position (`raw_boundary`'s byte-view void templates: T1 where the callee's
/// retention is attested no-retain, T2 under the named waiver where unknown,
/// a positive retention drops the class — never an unbridged view).
/// Sibling-COUNT contracts (the parent lane's) are the parent's
/// `prove_forward` and are not taken here.
pub(crate) fn prove_forward_only(
    tcx: TyCtxt<'_>,
    s: &Subject,
    subjects: &[Subject],
    known: &FxHashMap<(LocalDefId, HirId), Contract>,
) -> Option<Contract> {
    if s.ptr_depth != 1 || !matches!(s.kind, SubjectKind::Param { .. }) {
        return None;
    }
    let Node::Pat(pat) = tcx.hir_node(s.hir_id) else { return None };
    let typeck = tcx.typeck(s.fn_did);
    if !super::void_pointee::has_void_pointee(tcx, typeck.pat_ty(pat), 1) {
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
    let own_index = params.iter().position(|p| *p == s.hir_id)?;
    let mut uses = Uses {
        target: s.hir_id,
        found: Vec::new(),
        writes: FxHashMap::default(),
        closures: false,
    };
    uses.visit_expr(body.value);
    if uses.closures || uses.writes.contains_key(&s.hir_id) {
        return None;
    }
    let name = s.param_name.as_ref()?;
    let mut nullable = false;
    let mut edits = Vec::new();
    let mut pass_ons = 0usize;
    let mut inherited: Option<(ByteElement, WidthTable)> = None;
    let mut reaches_raw = false;
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
                    bridge_kind: "binn-counted-null-test",
                });
            }
            ExprKind::Call(callee, args) => {
                let index = args.iter().position(|a| a.hir_id == use_.hir_id)?;
                let ExprKind::Path(path) = &callee.kind else { return None };
                let Res::Def(rustc_hir::def::DefKind::Fn, did) =
                    typeck.qpath_res(path, callee.hir_id)
                else {
                    return None;
                };
                // A foreign position is wave-4's pinned-contract territory.
                let callee = did.as_local().filter(|_| !tcx.is_foreign_item(did))?;
                pass_ons += 1;
                let position = known.iter().find(|((f, h), _)| {
                    *f == callee
                        && subjects.iter().any(|t| {
                            t.fn_did == callee
                                && t.hir_id == *h
                                && matches!(t.kind, SubjectKind::Param { hir_index } if hir_index == index)
                        })
                });
                let Some((_, contract)) = position else {
                    reaches_raw = true;
                    continue;
                };
                // A sibling-count contract is the parent's forward; a void
                // position that already forwards an unknown width is a raw
                // position for the width's purpose.
                let Some(width) = contract.width.as_ref() else { return None };
                let width = match width.discriminant {
                    None => width.clone(),
                    Some(k) => {
                        let discriminant = local_of(args.get(k)?)?;
                        let sibling = params.iter().position(|p| *p == discriminant)?;
                        if sibling == own_index {
                            return None;
                        }
                        width.rekey(sibling)
                    }
                };
                nullable |= contract.nullable;
                match &inherited {
                    None => inherited = Some((contract.element, width)),
                    Some((element, known_width)) => {
                        if *element != contract.element
                            || known_width.is_unknown() != width.is_unknown()
                            || (!width.is_unknown() && *known_width != width)
                        {
                            return None;
                        }
                    }
                }
            }
            _ => return None,
        }
    }
    if pass_ons == 0 {
        return None;
    }
    let (element, width) = match inherited {
        Some((element, width)) if !reaches_raw => (element, width),
        // A raw position among the pass-ons: no width travels, and a
        // delivered `u8` view is never widened to a writable one.
        Some((element, _)) => (element, WidthTable::unknown()),
        None => (
            if s.mutable {
                ByteElement::Write
            } else {
                ByteElement::Read
            },
            WidthTable::unknown(),
        ),
    };
    Some(Contract {
        count_index: width.discriminant.unwrap_or(own_index),
        element,
        nullable,
        width: Some(width),
        uses: edits,
    })
}

/// Never widen a thin reference (R395-2). A bridged pointer whose provenance
/// is a local this table decided THIN admits only when the width is known at
/// the site — the constant, or the literal the discriminant argument names —
/// and equals the size of the place the argument views; a local whose own
/// storage is viewed must not be a converted subject. Raw and fat roots carry
/// the input's obligation (§28) or their own extent receipt.
pub(crate) fn root_rule<'tcx>(
    tcx: TyCtxt<'tcx>,
    table: &super::DecisionTable,
    caller: LocalDefId,
    argument: &'tcx Expr<'tcx>,
    width: &WidthTable,
    discriminant: Option<&'tcx Expr<'tcx>>,
) -> Result<(), super::seam::SeamBlock> {
    use super::seam::SeamBlock;
    let decision_of = |id: HirId| {
        table
            .entries
            .iter()
            .find(|(s, _)| s.fn_did == caller && s.hir_id == id)
            .map(|(_, d)| d)
    };
    match super::counted_void::value_root(argument) {
        Root::Opaque => Ok(()),
        Root::Storage(id) => match decision_of(id) {
            Some(super::Decision::Degraded(_)) | None => Ok(()),
            Some(_) => Err(SeamBlock::CountedVoidRoot),
        },
        Root::Value(id) => {
            let Some(decision) = decision_of(id) else { return Ok(()) };
            if !super::counted_void::thin(decision) {
                return Ok(());
            }
            let selected = width.width_for(discriminant.and_then(literal_of));
            let viewed = super::counted_void::viewed_type(tcx, caller, argument)
                .and_then(|ty| size_of(tcx, caller, ty));
            match (selected, viewed) {
                (Some(selected), Some(viewed)) if selected == viewed => Ok(()),
                _ => Err(SeamBlock::CountedVoidRoot),
            }
        }
    }
}

/// Is this caller local FRAME-CONFINED — storage whose contents never leave
/// the caller (R406-6, finding B)? A callee that stores a pointer derived from
/// a bridged view into such a local retains it only for the caller's frame,
/// where the view itself is live, so the retention is T1.
///
/// Every use of the local in the caller's body must be one of: (1) an address
/// taken INSIDE the certified call (`&mut local` at `call_span`); (2) a field
/// read whose field type cannot carry a pointer, not under an address-of; (3)
/// a whole-value read when the local's own type cannot carry a pointer; (4)
/// an assignment target (`local = ..`, `local.f = ..`). Anything else — an
/// address taken at another site, a pointer-carrying field read, a move or
/// copy of a pointer-carrying value, a return, a closure capture — is an
/// escape or an unknown, and the local is not confined.
pub(crate) fn frame_confined<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: LocalDefId,
    local: HirId,
    call_span: rustc_span::Span,
) -> bool {
    let body = tcx.hir_body_owned_by(caller);
    let typeck = tcx.typeck(caller);
    let mut uses = Uses {
        target: local,
        found: Vec::new(),
        writes: FxHashMap::default(),
        closures: false,
    };
    uses.visit_expr(body.value);
    if uses.closures {
        return false;
    }
    let carries = |ty: Ty<'tcx>| super::raw_boundary::may_carry_pointer(tcx, ty, 4);
    let assigned = |e: &Expr<'_>| match tcx.parent_hir_node(e.hir_id) {
        Node::Expr(parent) => matches!(parent.kind,
            ExprKind::Assign(lhs, _, _) | ExprKind::AssignOp(_, lhs, _) if lhs.hir_id == e.hir_id),
        _ => false,
    };
    for use_ in uses.found {
        // The outermost field projection over this use, if any.
        let mut place = use_;
        while let Node::Expr(parent) = tcx.parent_hir_node(place.hir_id)
            && let ExprKind::Field(base, _) = parent.kind
            && base.hir_id == place.hir_id
        {
            place = parent;
        }
        let parent = tcx.parent_hir_node(place.hir_id);
        let confined = match parent {
            Node::Expr(parent) => match parent.kind {
                ExprKind::AddrOf(_, _, operand) if operand.hir_id == place.hir_id => {
                    place.hir_id == use_.hir_id && call_span.contains(parent.span)
                }
                ExprKind::Assign(lhs, _, _) | ExprKind::AssignOp(_, lhs, _)
                    if lhs.hir_id == place.hir_id =>
                {
                    true
                }
                _ => !carries(typeck.expr_ty(place)),
            },
            Node::Stmt(_) | Node::LetStmt(_) | Node::Block(_) => !carries(typeck.expr_ty(place)),
            _ => false,
        };
        if !confined && !assigned(place) {
            return false;
        }
    }
    true
}
