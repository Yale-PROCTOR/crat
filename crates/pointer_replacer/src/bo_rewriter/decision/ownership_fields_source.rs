//! R376 native constructor/free source proofs for scalar boxed-slice roots.
//! Source occurrence identity is not allocation-generation identity. Ordinary
//! call and generated-unwind obligations remain explicit for the bundle owner.
use std::collections::{BTreeMap, BTreeSet};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    Expr, ExprKind, HirId, Node, QPath,
    def::Res,
    intravisit::{self, Visitor},
};
use rustc_middle::{
    mir::{
        BasicBlock, CastKind, Local, Location, Operand, Place, Rvalue, StatementKind,
        TerminatorKind,
        visit::{PlaceContext, Visitor as MirVisitor},
    },
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_span::{
    Span,
    def_id::{DefId, LocalDefId},
};

use super::{
    Subject,
    box_facts::{BoxExprEdit, BoxShape},
    construction::ConstructionFacts,
};
use crate::utils::rustc::RustProgram;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct SourceCallKey {
    pub(crate) owner: u32,
    pub(crate) call_hir: u32,
    pub(crate) block: u32,
    pub(crate) statement: usize,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum SourceHold {
    Missing(&'static str),
    Identity,
    ConstructorIdentity,
    ConstructorShape,
    UnsupportedOwnerUse,
    FreeIdentity,
    NormalExitCoverage,
    UnsupportedControlFlow,
    Duplicate(SourceCallKey),
    Unexpected(SourceCallKey),
    Absent(SourceCallKey),
}
#[derive(Clone, Debug)]
pub(crate) struct CallObligation {
    key: SourceCallKey,
    callee: DefId,
    argument: usize,
    /// The lent local: the owner itself, or one of its view aliases.
    lent: LentLocal,
    argument_span: Span,
    call_span: Span,
    scalar_arguments: BTreeSet<usize>,
    deallocator_events:
        Option<Vec<crate::analyses::borrow_ownership::source_events::SourceEventKey>>,
    raw_argument_type: String,
}
/// Which local is lent at a call: the owner or a view alias of it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LentLocal {
    pub(crate) hir_id: HirId,
    pub(crate) spelling: String,
    pub(crate) is_view_alias: bool,
}

/// `let mut a = root.offset(start);` — a per-iteration alias of the owner
/// whose every use is an element access or a raw argument to a local callee.
/// Emitted as a runtime-checked mutable view `&mut (*root)[(start) as usize..]`
/// (R394-1: the bounds checks replace a static window proof).
#[derive(Clone, Debug)]
pub(crate) struct ViewAlias {
    pub(crate) hir_id: HirId,
    pub(crate) spelling: String,
    pub(crate) initializer_span: Span,
    pub(crate) start: String,
    pub(crate) access_edits: Vec<BoxExprEdit>,
}

impl CallObligation {
    pub(crate) fn key(&self) -> SourceCallKey {
        self.key
    }

    pub(crate) fn lent(&self) -> &LentLocal {
        &self.lent
    }

    pub(crate) fn callee(&self) -> DefId {
        self.callee
    }

    pub(crate) fn argument(&self) -> usize {
        self.argument
    }

    pub(crate) fn argument_span(&self) -> Span {
        self.argument_span
    }

    pub(crate) fn call_span(&self) -> Span {
        self.call_span
    }

    pub(crate) fn scalar_arguments(&self) -> &BTreeSet<usize> {
        &self.scalar_arguments
    }

    pub(crate) fn deallocator_events(
        &self,
    ) -> Option<&[crate::analyses::borrow_ownership::source_events::SourceEventKey]> {
        self.deallocator_events.as_deref()
    }

    pub(crate) fn raw_argument_type(&self) -> &str {
        &self.raw_argument_type
    }
}
#[derive(Clone, Debug)]
pub(crate) struct SourceFreeSite {
    key: SourceCallKey,
    owner: LocalDefId,
    binding: HirId,
    callee: DefId,
    span: Span,
    root_spelling: String,
}
impl SourceFreeSite {
    pub(crate) fn key(&self) -> SourceCallKey {
        self.key
    }

    pub(crate) fn span(&self) -> Span {
        self.span
    }

    pub(crate) fn owner(&self) -> LocalDefId {
        self.owner
    }

    pub(crate) fn binding(&self) -> HirId {
        self.binding
    }

    pub(crate) fn callee(&self) -> DefId {
        self.callee
    }
}
/// Structural source permit only. The final bundle must discharge every call
/// and unwind obligation before treating these source edits as admissible.
#[derive(Clone, Debug)]
pub(crate) struct SourcePlan {
    owner: LocalDefId,
    binding: HirId,
    count: String,
    shape: BoxShape,
    nonempty: bool,
    element: String,
    constructor: BoxExprEdit,
    scalar_edits: Vec<BoxExprEdit>,
    frees: Vec<SourceFreeSite>,
    calls: Vec<CallObligation>,
    /// Every intervening native call while this root is live, including other
    /// allocations whose emitted helpers may unwind. Never inferred empty from
    /// `retained_sink`, and never itself an R101 waiver authorization.
    unwind_obligations: Vec<SourceCallKey>,
    mir_aliases: BTreeSet<u32>,
    /// The owner handed to the caller raw at a `return`: the close is the
    /// transfer, the caller's C free stays where it is.
    return_transfer: Option<Span>,
    /// The owner stored raw into a field of another object
    /// (`(*rb).data_ = new_data`): the close is the transfer, the field's
    /// own C free stays where it is (R415, wave-6f 012 STOP 3).
    store_transfer: Option<Span>,
    /// The field the store transfer fills: `(struct, field index)` — the
    /// identity a field transaction (wave-6f) is keyed by.
    store_field: Option<(DefId, usize)>,
    /// The MIR local that receives the allocator's result: the one source of
    /// every pointer into this fresh allocation while the root never escapes.
    allocation_local: u32,
    element_spelling: String,
    view_aliases: Vec<ViewAlias>,
}
impl SourcePlan {
    pub(crate) fn view_aliases(&self) -> &[ViewAlias] {
        &self.view_aliases
    }

    pub(crate) fn element_spelling(&self) -> &str {
        &self.element_spelling
    }

    pub(crate) fn return_transfer(&self) -> Option<Span> {
        self.return_transfer
    }

    pub(crate) fn store_transfer(&self) -> Option<Span> {
        self.store_transfer
    }

    pub(crate) fn store_field(&self) -> Option<(DefId, usize)> {
        self.store_field
    }

    pub(crate) fn allocation_local(&self) -> u32 {
        self.allocation_local
    }

    pub(crate) fn owner(&self) -> LocalDefId {
        self.owner
    }

    pub(crate) fn binding(&self) -> HirId {
        self.binding
    }

    pub(crate) fn count(&self) -> &str {
        &self.count
    }

    pub(crate) fn shape(&self) -> BoxShape {
        self.shape
    }

    pub(crate) fn nonempty(&self) -> bool {
        self.nonempty
    }

    pub(crate) fn element(&self) -> &str {
        &self.element
    }

    pub(crate) fn constructor(&self) -> &BoxExprEdit {
        &self.constructor
    }

    pub(crate) fn scalar_edits(&self) -> &[BoxExprEdit] {
        &self.scalar_edits
    }

    pub(crate) fn frees(&self) -> &[SourceFreeSite] {
        &self.frees
    }

    pub(crate) fn calls(&self) -> &[CallObligation] {
        &self.calls
    }

    pub(crate) fn unwind_obligations(&self) -> &[SourceCallKey] {
        &self.unwind_obligations
    }

    pub(crate) fn mir_aliases(&self) -> &BTreeSet<u32> {
        &self.mir_aliases
    }
}

impl super::super::ownership_fields::free_sites::FreePlanSite for SourceFreeSite {
    type Emitted = BoxExprEdit;
    type Hold = SourceHold;
    type Key = SourceCallKey;

    fn key(&self) -> &Self::Key {
        &self.key
    }

    fn missing(key: Self::Key) -> Self::Hold {
        SourceHold::Absent(key)
    }

    fn extra(key: Self::Key) -> Self::Hold {
        SourceHold::Unexpected(key)
    }

    fn duplicate(key: Self::Key) -> Self::Hold {
        SourceHold::Duplicate(key)
    }

    fn plan(&self) -> Result<Self::Emitted, Self::Hold> {
        // These private fields exist only after the constructor/owner-root,
        // exact native free and complete normal-path checks below. This edit
        // is still conditional on SourcePlan's explicit bundle obligations.
        Ok(BoxExprEdit {
            span: self.span,
            replacement: format!("::std::mem::drop({})", self.root_spelling),
            receipt: "c-free-site-drop",
        })
    }
}

#[derive(Default)]
struct Expressions<'tcx>(Vec<&'tcx Expr<'tcx>>);
impl<'tcx> Visitor<'tcx> for Expressions<'tcx> {
    fn visit_expr(&mut self, expression: &'tcx Expr<'tcx>) {
        self.0.push(expression);
        intravisit::walk_expr(self, expression);
    }
}
fn definition(expression: &Expr<'_>) -> Option<DefId> {
    match expression.kind {
        ExprKind::Path(QPath::Resolved(_, path)) => match path.res {
            Res::Def(rustc_hir::def::DefKind::Fn, did) => Some(did),
            _ => None,
        },
        _ => None,
    }
}
fn void_pointer(tcx: TyCtxt<'_>, ty: Ty<'_>) -> bool {
    matches!(ty.kind(), TyKind::RawPtr(pointee, rustc_hir::Mutability::Mut)
        if matches!(pointee.kind(), TyKind::Adt(def, _) if Some(def.did()) == tcx.lang_items().c_void()))
}
fn c_function(tcx: TyCtxt<'_>, callee: DefId, expected: &str) -> bool {
    let Some(local) = callee.as_local() else { return false };
    if !matches!(tcx.hir_node_by_def_id(local), Node::ForeignItem(_)) {
        return false;
    }
    let symbol = tcx
        .codegen_fn_attrs(callee)
        .link_name
        .unwrap_or_else(|| tcx.item_name(callee));
    let sig = tcx.fn_sig(callee).skip_binder().skip_binder();
    if symbol.as_str() != expected
        || sig.c_variadic
        || sig.abi != (rustc_abi::ExternAbi::C { unwind: false })
    {
        return false;
    }
    match expected {
        "free" => {
            sig.inputs().len() == 1 && void_pointer(tcx, sig.inputs()[0]) && sig.output().is_unit()
        }
        _ => false,
    }
}
fn peel<'tcx>(
    mut expression: &'tcx Expr<'tcx>,
    typeck: &rustc_middle::ty::TypeckResults<'tcx>,
) -> Result<&'tcx Expr<'tcx>, SourceHold> {
    while let ExprKind::Cast(inner, _) = expression.kind {
        if !matches!(typeck.expr_ty(expression).kind(), TyKind::RawPtr(..))
            || !matches!(typeck.expr_ty(inner).kind(), TyKind::RawPtr(..))
        {
            return Err(SourceHold::UnsupportedOwnerUse);
        }
        expression = inner;
    }
    Ok(expression)
}
/// A reference to static data: a literal, or a `transmute` of one.
fn static_reference(
    tcx: TyCtxt<'_>,
    typeck: &rustc_middle::ty::TypeckResults<'_>,
    expression: &Expr<'_>,
) -> bool {
    match expression.kind {
        ExprKind::Lit(_) => true,
        ExprKind::Call(callee, [argument]) => {
            let ExprKind::Path(QPath::Resolved(_, path)) = callee.kind else { return false };
            let Res::Def(_, did) = path.res else { return false };
            tcx.item_name(did).as_str() == "transmute"
                && matches!(typeck.expr_ty(argument).kind(), TyKind::Ref(..))
                && static_reference(tcx, typeck, argument)
        }
        _ => false,
    }
}
fn root_path(expression: &Expr<'_>, binding: HirId) -> bool {
    matches!(expression.kind, ExprKind::Path(QPath::Resolved(_, path))
        if path.res == Res::Local(binding))
}
/// `expression` names a local bound by `let a = root.offset(start)` — the
/// shape the view-alias permit admits (its start and uses are checked there).
fn view_alias_of(
    tcx: TyCtxt<'_>,
    typeck: &rustc_middle::ty::TypeckResults<'_>,
    expression: &Expr<'_>,
    binding: HirId,
) -> bool {
    let ExprKind::Path(QPath::Resolved(_, path)) = expression.kind else { return false };
    let Res::Local(alias) = path.res else { return false };
    let Node::LetStmt(local) = tcx.parent_hir_node(alias) else { return false };
    let Some(init) = local.init else { return false };
    let ExprKind::MethodCall(_, receiver, [_], _) = init.kind else { return false };
    root_path(receiver, binding)
        && typeck
            .type_dependent_def_id(init.hir_id)
            .is_some_and(|did| tcx.item_name(did).as_str() == "offset")
}
/// The raw-pointer locals reachable from `seeds` through plain copies and
/// pointer-to-pointer casts (both directions), a must-alias set.
fn copy_closure(body: &rustc_middle::mir::Body<'_>, seeds: BTreeSet<u32>) -> BTreeSet<u32> {
    let mut aliases = seeds;
    loop {
        let before = aliases.len();
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(box (destination, rvalue)) = &statement.kind else {
                    continue;
                };
                let Some(destination) = destination.as_local() else { continue };
                let operand = match rvalue {
                    Rvalue::Use(operand) | Rvalue::Cast(CastKind::PtrToPtr, operand, _) => operand,
                    _ => continue,
                };
                let Some(source) = plain_local(operand) else { continue };
                if !matches!(body.local_decls[destination].ty.kind(), TyKind::RawPtr(..))
                    || !matches!(body.local_decls[source].ty.kind(), TyKind::RawPtr(..))
                {
                    continue;
                }
                if aliases.contains(&source.as_u32()) || aliases.contains(&destination.as_u32()) {
                    aliases.insert(source.as_u32());
                    aliases.insert(destination.as_u32());
                }
            }
        }
        if before == aliases.len() {
            return aliases;
        }
    }
}
/// `(*base).field = <alias of the owner>` in MIR: the destination is a
/// projected place whose base is not the owner, the value a plain alias
/// local (a copy, a move, or a pointer-to-pointer cast of one).
fn is_store_transfer(
    statement: &rustc_middle::mir::Statement<'_>,
    aliases: &BTreeSet<u32>,
) -> bool {
    let StatementKind::Assign(box (destination, rvalue)) = &statement.kind else { return false };
    if destination.projection.is_empty() || aliases.contains(&destination.local.as_u32()) {
        return false;
    }
    match rvalue {
        Rvalue::Use(operand) | Rvalue::Cast(CastKind::PtrToPtr, operand, _) => {
            plain_local(operand).is_some_and(|local| aliases.contains(&local.as_u32()))
        }
        _ => false,
    }
}
fn plain_local(operand: &Operand<'_>) -> Option<Local> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place.as_local(),
        Operand::Constant(_) => None,
    }
}
// The original call's scalar arguments introduce no reference, effect or
// trap between the generated peer borrows. Count operands are a different
// phase: they remain evaluated once at their original allocation site.
fn scalar_arguments(
    tcx: TyCtxt<'_>,
    expression: &Expr<'_>,
    typeck: &rustc_middle::ty::TypeckResults<'_>,
) -> Result<BTreeSet<usize>, SourceHold> {
    let ExprKind::Call(_, arguments) = expression.kind else { return Err(SourceHold::Identity) };
    let mut scalars = BTreeSet::new();
    for (index, argument) in arguments.iter().enumerate() {
        if typeck.expr_ty(argument).is_raw_ptr() {
            continue;
        }
        if !pure(tcx, argument, typeck) {
            return Err(SourceHold::UnsupportedOwnerUse);
        }
        scalars.insert(index);
    }
    Ok(scalars)
}
/// A side-effect-free scalar read: literals, locals, casts, arithmetic and
/// comparisons over those.
fn pure(
    tcx: TyCtxt<'_>,
    expression: &Expr<'_>,
    typeck: &rustc_middle::ty::TypeckResults<'_>,
) -> bool {
    {
        if !matches!(
            typeck.expr_ty(expression).kind(),
            TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) | TyKind::Bool
        ) {
            return false;
        }
        match expression.kind {
            ExprKind::Lit(_) => true,
            ExprKind::Path(QPath::Resolved(_, path)) => matches!(path.res, Res::Local(_)),
            ExprKind::Cast(inner, _) => pure(tcx, inner, typeck),
            // A scalar FIELD of another object read through a PARAMETER's raw
            // pointer (`(*rb).cur_size_`): a parameter cannot alias the
            // fresh allocation, and a raw read is not a borrow, so the read
            // commutes with the owner's lend (E5C-3: nothing to hoist).
            ExprKind::Field(base, _) => {
                let ExprKind::Unary(rustc_hir::UnOp::Deref, through) = base.kind else {
                    return false;
                };
                let ExprKind::Path(QPath::Resolved(_, path)) = through.kind else {
                    return false;
                };
                let Res::Local(local) = path.res else { return false };
                typeck.expr_ty(through).is_raw_ptr()
                    && matches!(tcx.parent_hir_node(local), Node::Param(_))
            }
            // A wrapping integer operation over pure operands: no memory, no
            // trap (C's unsigned arithmetic as the substrate spells it).
            ExprKind::MethodCall(segment, receiver, [argument], _) => {
                matches!(
                    segment.ident.name.as_str(),
                    "wrapping_add" | "wrapping_sub" | "wrapping_mul"
                ) && pure(tcx, receiver, typeck)
                    && pure(tcx, argument, typeck)
            }
            // Scalar arithmetic over pure operands reads no memory and
            // introduces no reference; an overflow or zero-divisor trap is
            // the input's own UB in C (§28) and unwinds through the
            // receipted cleanup drops.
            ExprKind::Binary(operator, left, right) => {
                use rustc_hir::BinOpKind::*;
                matches!(
                    operator.node,
                    Add | Sub
                        | Mul
                        | Div
                        | Rem
                        | BitAnd
                        | BitOr
                        | BitXor
                        | Shl
                        | Shr
                        | Eq
                        | Ne
                        | Lt
                        | Le
                        | Gt
                        | Ge
                ) && pure(tcx, left, typeck)
                    && pure(tcx, right, typeck)
            }
            ExprKind::Unary(rustc_hir::UnOp::Neg | rustc_hir::UnOp::Not, inner) => {
                pure(tcx, inner, typeck)
            }
            _ => false,
        }
    }
}
/// Actual MIR reads (including pointer bases of payload stores), excluding
/// StorageLive/Dead and writes of the fresh initializer into its destination.
struct RootReads<'a> {
    aliases: &'a BTreeSet<u32>,
    found: bool,
}
impl<'tcx> MirVisitor<'tcx> for RootReads<'_> {
    fn visit_operand(&mut self, operand: &Operand<'tcx>, location: Location) {
        if let Operand::Copy(place) | Operand::Move(place) = operand
            && self.aliases.contains(&place.local.as_u32())
        {
            self.found = true;
        }
        self.super_operand(operand, location);
    }

    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        if !place.projection.is_empty() && self.aliases.contains(&place.local.as_u32()) {
            self.found = true;
        }
        self.super_place(place, context, location);
    }
}
struct MirCall<'tcx> {
    key: SourceCallKey,
    expression: &'tcx Expr<'tcx>,
    callee: DefId,
    destination: Option<Local>,
}

pub(crate) fn derive<'tcx>(
    program: &RustProgram<'tcx>,
    subject: &Subject,
    constructions: &ConstructionFacts,
) -> Result<SourcePlan, SourceHold> {
    let tcx = program.tcx;
    if !program.functions.contains(&subject.fn_did)
        || subject.hir_id.owner.def_id != subject.fn_did
        || !matches!(subject.kind, super::SubjectKind::Local)
        || !matches!(subject.ptr_depth, 1 | 2)
    {
        return Err(SourceHold::Identity);
    }
    let body = tcx
        .mir_drops_elaborated_and_const_checked(subject.fn_did)
        .borrow();
    let TyKind::RawPtr(element, rustc_hir::Mutability::Mut) =
        body.local_decls[subject.local].ty.kind()
    else {
        return Err(SourceHold::ConstructorShape);
    };
    let key = (subject.fn_did, subject.hir_id);
    let init_hir = *constructions
        .init_hirs
        .get(&key)
        .ok_or(SourceHold::Missing("initializer-hir"))?;
    let Node::Expr(init) = tcx.hir_node(init_hir) else { return Err(SourceHold::Identity) };
    if constructions.init_spans.get(&key) != Some(&init.span) {
        return Err(SourceHold::Identity);
    }
    let typeck = tcx.typeck(subject.fn_did);
    let constructor =
        super::ownership_fields_constructor::derive(tcx, subject.fn_did, init, *element)?;
    // A depth-2 owner is admitted only as a pointer ARRAY (`Box<[*mut T]>`,
    // the count from the allocation); a single boxed pointer cell stays
    // outside the wave (BOX-N5).
    if subject.ptr_depth == 2 && constructor.shape != BoxShape::Slice {
        return Err(SourceHold::ConstructorShape);
    }
    let allocation = constructor.allocation;
    let allocator = constructor.allocator;
    let Node::Pat(pattern) = tcx.hir_node(subject.hir_id) else { return Err(SourceHold::Identity) };
    let rustc_hir::PatKind::Binding(_, binding, ident, None) = pattern.kind else {
        return Err(SourceHold::Identity);
    };
    if binding != subject.hir_id {
        return Err(SourceHold::Identity);
    }
    let root_spelling = tcx
        .sess
        .source_map()
        .span_to_snippet(ident.span)
        .map_err(|_| SourceHold::Missing("root-spelling"))?;
    let body_id = tcx
        .hir_node_by_def_id(subject.fn_did)
        .body_id()
        .ok_or(SourceHold::Identity)?;
    let mut expressions = Expressions::default();
    expressions.visit_body(tcx.hir_body(body_id));
    // F04 (R350-4): an aggregate owner is admitted only when the source
    // supplies every field through the root before anything reads it — the
    // spelled zero literal is then a placeholder the program overwrites. A
    // whole-element store (`*root = v`, `*root.offset(k) = v`, or the same
    // through a view alias of the root) supplies every field at once.
    if let TyKind::Adt(def, _) = element.kind() {
        let mut supplied = BTreeSet::new();
        let mut whole = false;
        for e in &expressions.0 {
            let ExprKind::Assign(lhs, _, _) = e.kind else { continue };
            match lhs.kind {
                ExprKind::Field(base, ident) => {
                    if let ExprKind::Unary(rustc_hir::UnOp::Deref, operand) = base.kind
                        && root_path(operand, binding)
                    {
                        supplied.insert(ident.name);
                    }
                }
                ExprKind::Unary(rustc_hir::UnOp::Deref, operand) => {
                    let place = match operand.kind {
                        ExprKind::MethodCall(_, receiver, [_], _) => receiver,
                        _ => operand,
                    };
                    whole |=
                        root_path(place, binding) || view_alias_of(tcx, typeck, place, binding);
                }
                _ => {}
            }
        }
        if !whole
            && def
                .non_enum_variant()
                .fields
                .iter()
                .any(|field| !supplied.contains(&field.name))
        {
            return Err(SourceHold::Missing("native-aggregate-fields-supplied"));
        }
    }
    // Whole-caller reference/closure absence is a deliberately narrow scope.
    // Merely recognizing the scalar deref nested inside &*root is not enough.
    // A string / byte-string literal is a `&'static` reference to static
    // data (the corpus's assertion messages), and so is a `transmute` of one
    // (the corpus's `__PRETTY_FUNCTION__` spelling); neither can alias the
    // owner.
    if expressions.0.iter().any(|e| {
        matches!(
            e.kind,
            ExprKind::AddrOf(..) | ExprKind::Closure(..) | ExprKind::InlineAsm(..)
        ) || (matches!(typeck.expr_ty(e).kind(), TyKind::Ref(..))
            && !static_reference(tcx, typeck, e))
    }) {
        return Err(SourceHold::UnsupportedOwnerUse);
    }
    // The delivered-slice walker owns index syntax. Only its complete direct
    // dereference edits are consumed here; raw aliases/cursors and self-advance
    // still need their own view/ownership transactions.
    let mut covered = BTreeSet::new();
    let mut root_calls = Vec::new();
    let mut boundary_arguments = FxHashSet::default();
    let mut returns = Vec::new();
    let mut stores = Vec::new();
    let mut store_fields = Vec::new();
    for &expression in &expressions.0 {
        if let ExprKind::Ret(Some(returned)) = expression.kind
            && let Ok(operand) = peel(returned, typeck)
            && root_path(operand, binding)
        {
            covered.insert(operand.hir_id.local_id.as_u32());
            returns.push(returned);
        }
        // A store into a FIELD of another object through a raw base
        // (`(*rb).data_ = new_data`): ownership leaves as a raw pointer,
        // exactly as at a return. The destination is never the owner's own
        // storage (the owner is a plain binding, never a field).
        if let ExprKind::Assign(lhs, stored, _) = expression.kind
            && let Ok(operand) = peel(stored, typeck)
            && root_path(operand, binding)
            && let ExprKind::Field(base, _) = lhs.kind
            && let ExprKind::Unary(rustc_hir::UnOp::Deref, through) = base.kind
            && typeck.expr_ty(through).is_raw_ptr()
            && !root_path(through, binding)
        {
            covered.insert(operand.hir_id.local_id.as_u32());
            stores.push(stored);
            if let TyKind::Adt(def, _) = typeck.expr_ty(base).kind() {
                store_fields.push((def.did(), typeck.field_index(lhs.hir_id).as_usize()));
            }
        }
        if let ExprKind::Call(callee, arguments) = expression.kind {
            for (index, argument) in arguments.iter().enumerate() {
                let Ok(operand) = peel(argument, typeck) else { continue };
                if !root_path(operand, binding) {
                    continue;
                }
                let did = definition(callee).ok_or(SourceHold::UnsupportedOwnerUse)?;
                // A pointer-valued result could be an alias of the owner; a
                // FOREIGN call whose value is DISCARDED (`memcpy(dst, …);` as
                // a statement) returns it to no one. A local callee's returned
                // alias is the native stage's to certify (rule C), so its
                // permit-level refusal stands.
                let discarded = matches!(
                    tcx.parent_hir_node(expression.hir_id),
                    Node::Stmt(rustc_hir::Stmt {
                        kind: rustc_hir::StmtKind::Semi(_),
                        ..
                    })
                ) && did.as_local().is_some_and(|local| {
                    matches!(tcx.hir_node_by_def_id(local), Node::ForeignItem(_))
                });
                if !typeck.expr_ty(expression).is_unit()
                    && !discarded
                    && !matches!(
                        typeck.expr_ty(expression).kind(),
                        TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) | TyKind::Bool
                    )
                {
                    return Err(SourceHold::UnsupportedOwnerUse);
                }
                covered.insert(operand.hir_id.local_id.as_u32());
                boundary_arguments.insert((
                    subject.fn_did,
                    binding,
                    argument.span.lo().0,
                    argument.span.hi().0,
                ));
                root_calls.push((expression, did, index, argument.span));
            }
        }
    }
    // View aliases: `let mut a = root.offset(start);` with a pure `start`,
    // a plain raw-pointer binding, inside a slice owner. The root use in the
    // initializer is covered here; the alias's own uses are accounted below.
    let mut alias_bindings: Vec<(HirId, &Expr<'_>, &Expr<'_>)> = Vec::new();
    let mut alias_receivers: BTreeSet<(u32, Span)> = BTreeSet::new();
    if constructor.shape == BoxShape::Slice {
        struct Lets<'tcx>(Vec<&'tcx rustc_hir::LetStmt<'tcx>>);
        impl<'tcx> Visitor<'tcx> for Lets<'tcx> {
            fn visit_local(&mut self, local: &'tcx rustc_hir::LetStmt<'tcx>) {
                self.0.push(local);
                intravisit::walk_local(self, local);
            }
        }
        let mut lets = Lets(Vec::new());
        lets.visit_body(tcx.hir_body(body_id));
        for local in lets.0 {
            let Some(init) = local.init else { continue };
            let ExprKind::MethodCall(_, receiver, [start], _) = init.kind else { continue };
            if !root_path(receiver, binding) {
                continue;
            }
            let Some(did) = typeck.type_dependent_def_id(init.hir_id) else { continue };
            if tcx.crate_name(did.krate).as_str() != "core"
                || tcx.item_name(did).as_str() != "offset"
                || !typeck.expr_ty(init).is_raw_ptr()
                || local.els.is_some()
                || local.ty.is_some()
                || !pure(tcx, start, typeck)
            {
                continue;
            }
            let rustc_hir::PatKind::Binding(
                rustc_hir::BindingMode::NONE | rustc_hir::BindingMode::MUT,
                alias,
                _,
                None,
            ) = local.pat.kind
            else {
                continue;
            };
            covered.insert(receiver.hir_id.local_id.as_u32());
            alias_receivers.insert((receiver.hir_id.local_id.as_u32(), receiver.span));
            alias_bindings.push((alias, init, start));
        }
    }
    let names = FxHashMap::from_iter([(key, root_spelling.clone())]);
    let slice_uses = super::emitability::collect_slice_uses(
        tcx,
        &[subject.fn_did],
        &names,
        &FxHashSet::from_iter([key]),
        &FxHashSet::default(),
        &boundary_arguments,
    );
    let uses = slice_uses
        .get(&key)
        .ok_or(SourceHold::UnsupportedOwnerUse)?;
    // The walker reports a view alias's initializer as a cursor use of the
    // root; that use is accounted by the alias's own permit above.
    let is_alias_receiver = |hir: u32, span: Span| alias_receivers.contains(&(hir, span));
    // The walker reports the stored owner (`(*h).buf = new_data`) as a raw
    // use without a boundary; that use is the transfer accounted above.
    let is_store_operand = |span: Span| stores.iter().any(|stored| stored.span == span);
    if uses.unsupported.is_some_and(|span| {
        !returns.iter().any(|r| r.span == span)
            && !is_store_operand(span)
            && !alias_receivers
                .iter()
                .any(|(_, receiver)| *receiver == span)
    }) || uses
        .return_handoffs
        .iter()
        .any(|site| !returns.iter().any(|r| r.span == site.span))
        || uses.raw_uses.iter().any(|u| {
            !covered.contains(&u.hir_id.local_id.as_u32())
                || (u.boundary_span.is_none()
                    && !is_alias_receiver(u.hir_id.local_id.as_u32(), u.span)
                    && !is_store_operand(u.span))
        })
    {
        return Err(SourceHold::UnsupportedOwnerUse);
    }
    let mut scalar_edits = Vec::new();
    for edit in &uses.rewrites {
        let access = expressions
            .0
            .iter()
            .find(|e| e.span == edit.span)
            .ok_or(SourceHold::UnsupportedOwnerUse)?;
        let ExprKind::Unary(rustc_hir::UnOp::Deref, operand) = access.kind else {
            return Err(SourceHold::UnsupportedOwnerUse);
        };
        if constructor.shape == BoxShape::Sized && !root_path(operand, binding) {
            return Err(SourceHold::UnsupportedOwnerUse);
        }
        let root = if root_path(operand, binding) {
            operand
        } else {
            let ExprKind::MethodCall(_, receiver, arguments, _) = operand.kind else {
                return Err(SourceHold::UnsupportedOwnerUse);
            };
            let did = typeck
                .type_dependent_def_id(operand.hir_id)
                .ok_or(SourceHold::UnsupportedOwnerUse)?;
            if !root_path(receiver, binding)
                || arguments.len() != 1
                || !typeck.expr_ty(receiver).is_raw_ptr()
                || tcx.crate_name(did.krate).as_str() != "core"
                || tcx.item_name(did).as_str() != "offset"
            {
                return Err(SourceHold::UnsupportedOwnerUse);
            }
            receiver
        };
        if typeck.expr_ty(access) != *element {
            return Err(SourceHold::UnsupportedOwnerUse);
        }
        covered.insert(root.hir_id.local_id.as_u32());
        let replacement = if constructor.shape == BoxShape::Sized {
            format!("(*{root_spelling})")
        } else {
            edit.replacement.clone()
        };
        // A sized owner's `(*root)` already reads through the Box; an edit
        // whose text equals the source would only claim the interval (and
        // collide with a call bridge composed over the same argument).
        if tcx.sess.source_map().span_to_snippet(edit.span).as_deref() == Ok(&replacement) {
            continue;
        }
        scalar_edits.push(BoxExprEdit {
            span: edit.span,
            replacement,
            receipt: "native-box-slice-access",
        });
    }
    // Nested index edits need a composed expression transaction; they cannot
    // silently consume overlapping source bytes in this fragment.
    scalar_edits.sort_by_key(|e| (e.span.lo(), e.span.hi()));
    if scalar_edits
        .windows(2)
        .any(|w| w[0].span.hi() > w[1].span.lo())
    {
        return Err(SourceHold::UnsupportedOwnerUse);
    }
    let all_uses: BTreeSet<_> = expressions
        .0
        .iter()
        .filter(|e| root_path(e, binding))
        .map(|e| e.hir_id.local_id.as_u32())
        .collect();
    if all_uses != covered {
        return Err(SourceHold::UnsupportedOwnerUse);
    }
    // Each view alias: every use is an element access the slice walker
    // rewrites or a raw argument to a LOCAL callee (a call obligation with
    // the callee proofs); anything else (a copy, a free, a return, a
    // reassignment, an address) holds.
    let mut view_aliases = Vec::new();
    let mut alias_calls: Vec<(&Expr<'_>, DefId, usize, Span, LentLocal)> = Vec::new();
    for (alias, init, start) in alias_bindings {
        let Node::Pat(pattern) = tcx.hir_node(alias) else { return Err(SourceHold::Identity) };
        let rustc_hir::PatKind::Binding(_, _, ident, _) = pattern.kind else {
            return Err(SourceHold::Identity);
        };
        let spelling = ident.name.to_string();
        let mut alias_covered = BTreeSet::new();
        let mut alias_boundary = FxHashSet::default();
        for &expression in &expressions.0 {
            if let ExprKind::Assign(lhs, ..) | ExprKind::AssignOp(_, lhs, _) = expression.kind
                && root_path(lhs, alias)
            {
                return Err(SourceHold::UnsupportedOwnerUse);
            }
            let ExprKind::Call(callee, arguments) = expression.kind else { continue };
            for (index, argument) in arguments.iter().enumerate() {
                let Ok(operand) = peel(argument, typeck) else { continue };
                if !root_path(operand, alias) {
                    continue;
                }
                let did = definition(callee).ok_or(SourceHold::UnsupportedOwnerUse)?;
                if did.as_local().is_none()
                    || !typeck.expr_ty(expression).is_unit()
                        && !matches!(
                            typeck.expr_ty(expression).kind(),
                            TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) | TyKind::Bool
                        )
                {
                    return Err(SourceHold::UnsupportedOwnerUse);
                }
                alias_covered.insert(operand.hir_id.local_id.as_u32());
                alias_boundary.insert((
                    subject.fn_did,
                    alias,
                    argument.span.lo().0,
                    argument.span.hi().0,
                ));
                alias_calls.push((
                    expression,
                    did,
                    index,
                    argument.span,
                    LentLocal {
                        hir_id: alias,
                        spelling: spelling.clone(),
                        is_view_alias: true,
                    },
                ));
            }
        }
        let alias_key = (subject.fn_did, alias);
        let alias_names = FxHashMap::from_iter([(alias_key, spelling.clone())]);
        let alias_slice_uses = super::emitability::collect_slice_uses(
            tcx,
            &[subject.fn_did],
            &alias_names,
            &FxHashSet::from_iter([alias_key]),
            &FxHashSet::default(),
            &alias_boundary,
        );
        let alias_uses = alias_slice_uses
            .get(&alias_key)
            .ok_or(SourceHold::UnsupportedOwnerUse)?;
        if alias_uses.unsupported.is_some()
            || !alias_uses.return_handoffs.is_empty()
            || alias_uses.raw_uses.iter().any(|u| {
                !alias_covered.contains(&u.hir_id.local_id.as_u32()) || u.boundary_span.is_none()
            })
        {
            return Err(SourceHold::UnsupportedOwnerUse);
        }
        let mut access_edits = Vec::new();
        for edit in &alias_uses.rewrites {
            let access = expressions
                .0
                .iter()
                .find(|e| e.span == edit.span)
                .ok_or(SourceHold::UnsupportedOwnerUse)?;
            let ExprKind::Unary(rustc_hir::UnOp::Deref, operand) = access.kind else {
                return Err(SourceHold::UnsupportedOwnerUse);
            };
            let ExprKind::MethodCall(_, receiver, arguments, _) = operand.kind else {
                return Err(SourceHold::UnsupportedOwnerUse);
            };
            let did = typeck
                .type_dependent_def_id(operand.hir_id)
                .ok_or(SourceHold::UnsupportedOwnerUse)?;
            if !root_path(receiver, alias)
                || arguments.len() != 1
                || tcx.crate_name(did.krate).as_str() != "core"
                || tcx.item_name(did).as_str() != "offset"
                || typeck.expr_ty(access) != *element
            {
                return Err(SourceHold::UnsupportedOwnerUse);
            }
            alias_covered.insert(receiver.hir_id.local_id.as_u32());
            access_edits.push(BoxExprEdit {
                span: edit.span,
                replacement: edit.replacement.clone(),
                receipt: "native-box-view-alias-access",
            });
        }
        access_edits.sort_by_key(|e| (e.span.lo(), e.span.hi()));
        if access_edits
            .windows(2)
            .any(|w| w[0].span.hi() > w[1].span.lo())
        {
            return Err(SourceHold::UnsupportedOwnerUse);
        }
        let alias_all_uses: BTreeSet<_> = expressions
            .0
            .iter()
            .filter(|e| root_path(e, alias))
            .map(|e| e.hir_id.local_id.as_u32())
            .collect();
        if alias_all_uses != alias_covered {
            return Err(SourceHold::UnsupportedOwnerUse);
        }
        let start_spelling = tcx
            .sess
            .source_map()
            .span_to_snippet(start.span)
            .map_err(|_| SourceHold::Missing("view-alias-start-spelling"))?;
        view_aliases.push(ViewAlias {
            hir_id: alias,
            spelling,
            initializer_span: init.span,
            start: start_spelling,
            access_edits,
        });
    }

    // Join every native MIR call to exactly one resolved HIR call. The key
    // includes both identities; no source-order zip or name repair is used.
    let mut mir_calls = BTreeMap::new();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        let TerminatorKind::Call {
            func, destination, ..
        } = &data.terminator().kind
        else {
            continue;
        };
        let did = func
            .constant()
            .and_then(|c| match c.ty().kind() {
                TyKind::FnDef(did, _) => Some(*did),
                _ => None,
            })
            .ok_or(SourceHold::UnsupportedControlFlow)?;
        let span = data.terminator().source_info.span.source_callsite();
        let matches: Vec<_> = expressions
            .0
            .iter()
            .copied()
            .filter(|e| {
                (match e.kind {
                    ExprKind::Call(callee, _) => definition(callee),
                    ExprKind::MethodCall(..) => typeck.type_dependent_def_id(e.hir_id),
                    _ => None,
                }) == Some(did)
                    && e.span.source_callsite() == span
            })
            .collect();
        let [expression] = matches.as_slice() else {
            return Err(SourceHold::Missing("hir-mir-call-join"));
        };
        let key = SourceCallKey {
            owner: subject.fn_did.local_def_index.as_u32(),
            call_hir: expression.hir_id.local_id.as_u32(),
            block: block.as_u32(),
            statement: data.statements.len(),
        };
        mir_calls.insert(
            block,
            MirCall {
                key,
                expression,
                callee: did,
                destination: destination.as_local(),
            },
        );
    }
    let allocations: Vec<_> = mir_calls
        .values()
        .filter(|c| c.expression.hir_id == allocation.hir_id && c.callee == allocator)
        .collect();
    let [allocation_call] = allocations.as_slice() else {
        return Err(SourceHold::ConstructorIdentity);
    };
    let allocator_destination = allocation_call
        .destination
        .ok_or(SourceHold::ConstructorShape)?;
    let aliases = copy_closure(&body, BTreeSet::from([subject.local.as_u32()]));
    if !aliases.contains(&allocator_destination.as_u32()) {
        return Err(SourceHold::ConstructorIdentity);
    }
    for call in mir_calls.values() {
        if call
            .destination
            .is_some_and(|local| aliases.contains(&local.as_u32()))
            && call.key != allocation_call.key
        {
            return Err(SourceHold::UnsupportedOwnerUse);
        }
    }
    // An alias's MIR locals: the derivation closure of the allocation result
    // minus the owner's own copy aliases, restricted to the alias's name.
    let alias_locals: BTreeSet<u32> = {
        let names: BTreeSet<_> = view_aliases.iter().map(|a| a.spelling.as_str()).collect();
        let seeds = body
            .var_debug_info
            .iter()
            .filter(|info| names.contains(info.name.as_str()))
            .filter_map(|info| match info.value {
                rustc_middle::mir::VarDebugInfoContents::Place(place) => {
                    place.as_local().map(|l| l.as_u32())
                }
                _ => None,
            })
            .collect();
        copy_closure(&body, seeds)
    };
    let owner_lent = LentLocal {
        hir_id: binding,
        spelling: root_spelling.clone(),
        is_view_alias: false,
    };
    let mut frees = Vec::new();
    let mut calls = Vec::new();
    let every_call = root_calls
        .into_iter()
        .map(|(expression, callee, argument, span)| {
            (expression, callee, argument, span, owner_lent.clone())
        })
        .chain(alias_calls);
    for (expression, callee, argument, argument_span, lent) in every_call {
        let matched: Vec<_> = mir_calls
            .values()
            .filter(|c| c.expression.hir_id == expression.hir_id && c.callee == callee)
            .collect();
        let [call] = matched.as_slice() else { return Err(SourceHold::Missing("owner-call-join")) };
        let data = &body.basic_blocks[BasicBlock::from_u32(call.key.block)];
        let TerminatorKind::Call { args, .. } = &data.terminator().kind else {
            return Err(SourceHold::Identity);
        };
        let actual = args
            .get(argument)
            .and_then(|arg| plain_local(&arg.node))
            .ok_or(SourceHold::UnsupportedOwnerUse)?;
        let expected_locals = if lent.is_view_alias {
            &alias_locals
        } else {
            &aliases
        };
        if !expected_locals.contains(&actual.as_u32()) {
            return Err(SourceHold::Identity);
        }
        if lent.is_view_alias && c_function(tcx, callee, "free") {
            return Err(SourceHold::UnsupportedOwnerUse);
        }
        if c_function(tcx, callee, "free") {
            if argument != 0 {
                return Err(SourceHold::FreeIdentity);
            }
            frees.push(SourceFreeSite {
                key: call.key,
                owner: subject.fn_did,
                binding,
                callee,
                span: expression.span,
                root_spelling: root_spelling.clone(),
            });
        } else {
            let deallocator_events = callee.as_local().and_then(|local| {
                super::ownership_fields_deallocator::derive(program, local, argument)
                    .ok()
                    .filter(|p| p.matches(program, local, argument))
                    .map(|p| p.events().to_vec())
            });
            calls.push(CallObligation {
                key: call.key,
                callee,
                argument,
                lent,
                argument_span,
                call_span: expression.span,
                scalar_arguments: scalar_arguments(tcx, expression, typeck)?,
                deallocator_events,
                raw_argument_type: typeck
                    .expr_ty(match expression.kind {
                        ExprKind::Call(_, args) => &args[argument],
                        _ => unreachable!(),
                    })
                    .to_string(),
            });
        }
    }
    let transfers: Vec<_> = calls
        .iter()
        .filter(|c| c.deallocator_events.is_some())
        .collect();
    if frees.len() + transfers.len() + returns.len() + stores.len() != 1 {
        return Err(SourceHold::FreeIdentity);
    }
    let (close_key, close_span) = if let Some(free) = frees.first() {
        (Some(free.key), free.span)
    } else if let Some(transfer) = transfers.first() {
        (Some(transfer.key), transfer.call_span)
    } else if let Some(store) = stores.first() {
        (None, store.span)
    } else {
        (None, returns[0].span)
    };
    if close_span.lo() < init.span.hi()
        || scalar_edits
            .iter()
            .any(|edit| edit.span.lo() < init.span.hi() || edit.span.hi() > close_span.lo())
        || calls.iter().any(|call| {
            call.call_span.lo() < init.span.hi()
                || (Some(call.key) != close_key && call.call_span.hi() > close_span.lo())
        })
    {
        return Err(SourceHold::UnsupportedOwnerUse);
    }
    // A source occurrence may execute repeatedly in a loop. Track each
    // reachable normal state, never fabricate a dynamic allocation generation.
    // An iteration can allocate again only after its previous exact C free.
    #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    enum State {
        Before,
        Live,
        Freed,
    }
    let mut pending = vec![(BasicBlock::from_u32(0), State::Before)];
    let mut visited = BTreeSet::new();
    let mut unwind_obligations = BTreeSet::new();
    while let Some((block, mut state)) = pending.pop() {
        if !visited.insert((block.as_u32(), state)) {
            continue;
        }
        let data = &body.basic_blocks[block];
        let mut reads = RootReads {
            aliases: &aliases,
            found: false,
        };
        for (statement_index, statement) in data.statements.iter().enumerate() {
            // The store transfer (`(*rb).data_ = new_data`) closes the owner
            // at this statement: it must be live here, and no later
            // statement or terminator of the path may read it.
            if !stores.is_empty() && is_store_transfer(statement, &aliases) {
                if state != State::Live {
                    return Err(SourceHold::NormalExitCoverage);
                }
                state = State::Freed;
                continue;
            }
            reads.found = false;
            reads.visit_statement(
                statement,
                Location {
                    block,
                    statement_index,
                },
            );
            if reads.found && state != State::Live {
                return Err(SourceHold::NormalExitCoverage);
            }
        }
        reads.found = false;
        reads.visit_terminator(
            data.terminator(),
            Location {
                block,
                statement_index: data.statements.len(),
            },
        );
        if reads.found && state != State::Live {
            return Err(SourceHold::NormalExitCoverage);
        }
        if let Some(call) = mir_calls.get(&block) {
            if call.key == allocation_call.key {
                if state == State::Live {
                    return Err(SourceHold::NormalExitCoverage);
                }
                state = State::Live;
            } else if Some(call.key) == close_key {
                if state != State::Live {
                    return Err(SourceHold::NormalExitCoverage);
                }
                state = State::Freed;
            } else if state == State::Live {
                unwind_obligations.insert(call.key);
            }
        }
        let successors = match &data.terminator().kind {
            TerminatorKind::Goto { target }
            | TerminatorKind::Call {
                target: Some(target),
                ..
            }
            | TerminatorKind::Assert { target, .. } => vec![*target],
            TerminatorKind::SwitchInt { targets, .. } => targets.all_targets().to_vec(),
            // A diverging call (`__assert_fail`, `abort`) and an unreachable
            // block end the path without returning: the owner is neither
            // freed nor dropped there, exactly as in C.
            TerminatorKind::Call { target: None, .. } | TerminatorKind::Unreachable => Vec::new(),
            TerminatorKind::FalseEdge { real_target, .. }
            | TerminatorKind::FalseUnwind { real_target, .. } => vec![*real_target],
            TerminatorKind::Return if state != State::Live => Vec::new(),
            // A return transfer: this block must hand the owner (an alias of
            // it) to the return place; any other live exit is uncovered.
            TerminatorKind::Return
                if close_key.is_none()
                    && data.statements.iter().rev().find_map(|statement| {
                        let StatementKind::Assign(box (destination, rvalue)) = &statement.kind
                        else {
                            return None;
                        };
                        (destination.as_local() == Some(rustc_middle::mir::RETURN_PLACE)).then(
                            || match rvalue {
                                Rvalue::Use(operand)
                                | Rvalue::Cast(CastKind::PtrToPtr, operand, _) => {
                                    plain_local(operand)
                                        .is_some_and(|local| aliases.contains(&local.as_u32()))
                                }
                                _ => false,
                            },
                        )
                    }) == Some(true) =>
            {
                Vec::new()
            }
            TerminatorKind::Return => return Err(SourceHold::NormalExitCoverage),
            _ => return Err(SourceHold::UnsupportedControlFlow),
        };
        pending.extend(successors.into_iter().map(|next| (next, state)));
    }
    if mir_calls
        .values()
        .any(|call| !visited.iter().any(|(block, _)| *block == call.key.block))
    {
        return Err(SourceHold::UnsupportedControlFlow);
    }
    Ok(SourcePlan {
        owner: subject.fn_did,
        binding,
        count: constructor.count,
        shape: constructor.shape,
        nonempty: constructor.nonempty,
        element: constructor.element.to_string(),
        constructor: constructor.edit,
        scalar_edits,
        frees,
        calls,
        unwind_obligations: unwind_obligations.into_iter().collect(),
        mir_aliases: aliases,
        return_transfer: returns.first().map(|r| r.span),
        store_transfer: stores.first().map(|s| s.span),
        store_field: store_fields.first().copied(),
        allocation_local: allocator_destination.as_u32(),
        element_spelling: constructor.element_spelling,
        view_aliases,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bo_rewriter as bo;

    fn inspect(source: &str, name: &str) -> Result<(String, usize, usize, usize), SourceHold> {
        let name = name.to_owned();
        ::utils::compilation::run_compiler_on_str(source, move |tcx| {
            let (table, ctx) = bo::decide_table_with_ctx_config(
                tcx,
                Some((
                    bo::A5Mode::PreciseReplay,
                    Some(bo::WholeProgramAttestation::FrozenBenchmarkGraph),
                )),
            )
            .expect("native source fixture analysis");
            let program = bo::collect_program(tcx);
            let subjects: Vec<_> = table
                .entries
                .iter()
                .filter(|(subject, _)| subject.param_name.as_deref() == Some(name.as_str()))
                .collect();
            assert_eq!(subjects.len(), 1);
            let plan = derive(&program, &subjects[0].0, &ctx.constructions)?;
            assert_eq!(plan.binding(), subjects[0].0.hir_id);
            assert_eq!(plan.owner(), subjects[0].0.fn_did);
            assert!(
                plan.constructor()
                    .receipt
                    .starts_with("native-calloc-zero-")
            );
            assert!(plan.constructor().replacement.contains("into_boxed_slice"));
            for free in plan.frees() {
                assert_eq!(free.binding(), plan.binding());
                assert_eq!(free.owner(), plan.owner());
                assert!(
                    tcx.sess
                        .source_map()
                        .span_to_snippet(free.span())
                        .unwrap()
                        .starts_with("free(")
                );
            }
            Ok((
                plan.count().to_owned(),
                plan.frees().len(),
                plan.calls().len(),
                plan.unwind_obligations().len(),
            ))
        })
        .expect("native source fixture compiles")
    }

    /// R415 (wave-6f 012 STOP 3): a `malloc`ed local stored into a FIELD of
    /// another object through its raw base (`(*h).buf = new_data`, the
    /// derived substrate's spelling of brotli's `RingBufferInitBuffer`) is a
    /// transfer — the close of the owner, exactly as a return transfer; the
    /// field's own C free stays where it is. The permit is exercised directly
    /// (on this base the model does not grant the local Owning; wave-6f's
    /// frame does on the composition, where the emission is witnessed).
    #[test]
    fn r415_store_into_a_field_through_a_raw_base_is_the_transfer() {
        let declarations = r#"#![allow(non_camel_case_types)] pub mod libc { pub use core::ffi::c_int; pub use core::ffi::c_ulong; pub use core::ffi::c_void; } extern "C" { fn malloc(n:libc::c_ulong)->*mut libc::c_void; fn free(p:*mut libc::c_void); }
#[repr(C)] #[derive(Copy, Clone)] pub struct Holder { pub count: u32, pub buf: *mut u8 }
unsafe extern "C" fn holder_free(mut h: *mut Holder) { free((*h).buf as *mut libc::c_void); (*h).buf = 0 as *mut u8; }"#;
        let store = |body: &str| {
            format!(
                "{declarations}\nunsafe extern \"C\" fn holder_init(mut h: *mut Holder, n: u32) {{ let mut new_data = malloc((n as libc::c_ulong).wrapping_mul(::std::mem::size_of::<u8>() as libc::c_ulong)) as *mut u8; {body} }}"
            )
        };
        let admitted =
            store("*new_data.offset(0 as isize) = 7 as u8; (*h).buf = new_data; (*h).count = n;");
        ::utils::compilation::run_compiler_on_str(&admitted, |tcx| {
            let (table, ctx) = bo::decide_table_with_ctx_config(
                tcx,
                Some((
                    bo::A5Mode::PreciseReplay,
                    Some(bo::WholeProgramAttestation::FrozenBenchmarkGraph),
                )),
            )
            .unwrap();
            let program = bo::collect_program(tcx);
            let (subject, _) = table
                .entries
                .iter()
                .find(|(subject, _)| subject.param_name.as_deref() == Some("new_data"))
                .unwrap();
            let plan = derive(&program, subject, &ctx.constructions).unwrap();
            let span = plan.store_transfer().expect("the store is the transfer");
            assert_eq!(
                tcx.sess.source_map().span_to_snippet(span).unwrap(),
                "new_data"
            );
            assert!(plan.frees().is_empty() && plan.return_transfer().is_none());
            assert_eq!(plan.scalar_edits().len(), 1);
        })
        .unwrap();
        // A use of the owner AFTER the store (the allocation is no longer
        // this function's) and a store into the owner's own storage are
        // refused; a second close (the store and a free) is not one close.
        for body in [
            "(*h).buf = new_data; *new_data.offset(0 as isize) = 7 as u8;",
            "(*h).buf = new_data; free(new_data as *mut libc::c_void);",
            "let mut other = new_data; (*h).buf = other;",
            // A read that FOLLOWS the store in control flow though it
            // precedes it in the text (the second trip round the loop).
            "let mut i = 0; loop { if i == 1 { let v = *new_data.offset(0 as isize); (*h).count = v as u32; return; } (*h).buf = new_data; i += 1; }",
        ] {
            ::utils::compilation::run_compiler_on_str(&store(body), |tcx| {
                let (table, ctx) = bo::decide_table_with_ctx_config(
                    tcx,
                    Some((
                        bo::A5Mode::PreciseReplay,
                        Some(bo::WholeProgramAttestation::FrozenBenchmarkGraph),
                    )),
                )
                .unwrap();
                let program = bo::collect_program(tcx);
                let (subject, _) = table
                    .entries
                    .iter()
                    .find(|(subject, _)| subject.param_name.as_deref() == Some("new_data"))
                    .unwrap();
                assert!(
                    derive(&program, subject, &ctx.constructions).is_err(),
                    "{body}"
                );
            })
            .unwrap();
        }
    }

    /// R416-12: brotli's `RingBufferInitBuffer` as the derived substrate
    /// spells it — a byte-sized element's count is the byte count whatever
    /// its spelling; a `memcpy` whose pointer result is DISCARDED returns no
    /// alias; a scalar argument may read a field through a PARAMETER's raw
    /// pointer and use wrapping arithmetic; the store is the transfer. The
    /// permit admits the body; the foreign lend itself is the native stage's
    /// (`native-lend-source-join` until `memcpy` has a contract row).
    #[test]
    fn r416_ring_buffer_substrate_body_passes_the_permit() {
        let declarations = r#"#![allow(non_camel_case_types)] pub mod libc { pub use core::ffi::c_int; pub use core::ffi::c_ulong; pub use core::ffi::c_void; } extern "C" { fn malloc(n:libc::c_ulong)->*mut libc::c_void; fn free(p:*mut libc::c_void); fn memcpy(d: *mut libc::c_void, s: *const libc::c_void, n: libc::c_ulong) -> *mut libc::c_void; }
#[repr(C)] #[derive(Copy, Clone)] pub struct RingBuffer { pub cur_size_: u32, pub data_: *mut u8, pub buffer_: *mut u8 }"#;
        let body = |copy: &str| {
            format!(
                "{declarations}\nunsafe extern \"C\" fn RingBufferInitBuffer(buflen: u32, mut rb: *mut RingBuffer) {{ let mut new_data = malloc((2 as u32).wrapping_add(buflen) as libc::c_ulong) as *mut u8; if !((*rb).data_).is_null() {{ {copy} free((*rb).data_ as *mut libc::c_void); (*rb).data_ = 0 as *mut u8; }} (*rb).data_ = new_data; (*rb).cur_size_ = buflen; }}"
            )
        };
        let admitted = body(
            "memcpy(new_data as *mut libc::c_void, (*rb).data_ as *const libc::c_void, (2 as u32).wrapping_add((*rb).cur_size_) as libc::c_ulong);",
        );
        ::utils::compilation::run_compiler_on_str(&admitted, |tcx| {
            let (table, ctx) = bo::decide_table_with_ctx_config(
                tcx,
                Some((
                    bo::A5Mode::PreciseReplay,
                    Some(bo::WholeProgramAttestation::FrozenBenchmarkGraph),
                )),
            )
            .unwrap();
            let program = bo::collect_program(tcx);
            let (subject, _) = table
                .entries
                .iter()
                .find(|(subject, _)| subject.param_name.as_deref() == Some("new_data"))
                .unwrap();
            let plan = derive(&program, subject, &ctx.constructions).unwrap();
            assert_eq!(plan.constructor().receipt, "native-malloc-zero-byte-count");
            assert_eq!(
                plan.count(),
                "(((2 as u32).wrapping_add(buflen) as libc::c_ulong) as usize)"
            );
            assert!(plan.store_transfer().is_some() && plan.store_field().is_some());
            assert_eq!(
                plan.calls().len(),
                1,
                "the memcpy lend is a call obligation"
            );
            assert_eq!(plan.calls()[0].scalar_arguments().len(), 1);
        })
        .unwrap();
        // A KEPT pointer result may alias the owner; a field read through a
        // LOCAL (not a parameter) is not known disjoint from the owner.
        for copy in [
            "let kept = memcpy(new_data as *mut libc::c_void, (*rb).data_ as *const libc::c_void, 2 as libc::c_ulong);",
            "let mut other = rb; memcpy(new_data as *mut libc::c_void, (*rb).data_ as *const libc::c_void, (*other).cur_size_ as libc::c_ulong);",
        ] {
            ::utils::compilation::run_compiler_on_str(&body(copy), |tcx| {
                let (table, ctx) = bo::decide_table_with_ctx_config(
                    tcx,
                    Some((
                        bo::A5Mode::PreciseReplay,
                        Some(bo::WholeProgramAttestation::FrozenBenchmarkGraph),
                    )),
                )
                .unwrap();
                let program = bo::collect_program(tcx);
                let (subject, _) = table
                    .entries
                    .iter()
                    .find(|(subject, _)| subject.param_name.as_deref() == Some("new_data"))
                    .unwrap();
                assert!(
                    derive(&program, subject, &ctx.constructions).is_err(),
                    "{copy}"
                );
            })
            .unwrap();
        }
    }

    /// R425-2 (era-5c 003 claim 6): a traversal / recursive-call argument
    /// that is a TOKEN LOAD (`temp = (*root).right`, `minValueNode(node)`)
    /// licenses NO drop — the only deallocation sites of bst's entry are its
    /// two C `free`s, and a `Box` dropped at such a local's scope exit would
    /// free a subtree the input keeps linked. The owner permit cannot admit
    /// one by construction: a subject with no fresh allocation of its own is
    /// refused at the constructor, whatever the model kind, so no drop is
    /// ever emitted for it.
    #[test]
    fn r425_token_loads_and_traversal_arguments_license_no_drop() {
        let source = format!(
            r#"{} #[repr(C)] pub struct node {{ pub key: libc::c_int, pub left: *mut node, pub right: *mut node }}
unsafe extern "C" fn minValueNode(mut node_0: *mut node) -> *mut node {{
    let mut current = node_0;
    while !((*current).left).is_null() {{ current = (*current).left; }}
    return current;
}}
unsafe extern "C" fn newNode(mut key: libc::c_int) -> *mut node {{
    let mut temp = malloc(::std::mem::size_of::<node>() as libc::c_ulong) as *mut node;
    (*temp).key = key;
    (*temp).left = 0 as *mut node;
    (*temp).right = 0 as *mut node;
    return temp;
}}
pub unsafe extern "C" fn deleteNode(mut root: *mut node, mut key: libc::c_int) -> *mut node {{
    if root.is_null() {{ return root; }}
    if key < (*root).key {{
        (*root).left = deleteNode((*root).left, key);
    }} else if key > (*root).key {{
        (*root).right = deleteNode((*root).right, key);
    }} else {{
        if ((*root).left).is_null() {{
            let mut temp = (*root).right;
            free(root as *mut libc::c_void);
            return temp;
        }}
        let mut temp_0 = minValueNode((*root).right);
        (*root).key = (*temp_0).key;
        (*root).right = deleteNode((*root).right, (*temp_0).key);
    }}
    return root;
}}"#,
            r#"#![allow(non_camel_case_types)] pub mod libc { pub use core::ffi::c_int; pub use core::ffi::c_ulong; pub use core::ffi::c_void; } extern "C" { fn malloc(n:libc::c_ulong)->*mut libc::c_void; fn free(p:*mut libc::c_void); }"#
        );
        ::utils::compilation::run_compiler_on_str(&source, |tcx| {
            let (table, ctx) = bo::decide_table_with_ctx_config(
                tcx,
                Some((
                    bo::A5Mode::PreciseReplay,
                    Some(bo::WholeProgramAttestation::FrozenBenchmarkGraph),
                )),
            )
            .unwrap();
            let program = bo::collect_program(tcx);
            // Every token load of the traversal — whatever the model says —
            // is refused by the permit: it owns no allocation of its own.
            for (owner, name) in [
                ("minValueNode", "current"),
                ("deleteNode", "temp"),
                ("deleteNode", "temp_0"),
            ] {
                let (subject, _) = table
                    .entries
                    .iter()
                    .find(|(subject, _)| {
                        subject.param_name.as_deref() == Some(name)
                            && tcx.def_path_str(subject.fn_did.to_def_id()) == owner
                    })
                    .unwrap_or_else(|| panic!("{owner}::{name}"));
                assert!(
                    matches!(
                        derive(&program, subject, &ctx.constructions),
                        Err(SourceHold::ConstructorIdentity | SourceHold::ConstructorShape)
                    ),
                    "{owner}::{name} must own no allocation"
                );
            }
            // `newNode`'s own allocation IS an owner — closed by its return
            // transfer, never by a scope-exit drop.
            let (subject, _) = table
                .entries
                .iter()
                .find(|(subject, _)| {
                    subject.param_name.as_deref() == Some("temp")
                        && tcx.def_path_str(subject.fn_did.to_def_id()) == "newNode"
                })
                .expect("newNode::temp");
            let plan = derive(&program, subject, &ctx.constructions).expect("newNode::temp");
            assert!(plan.frees().is_empty() && plan.return_transfer().is_some());
        })
        .unwrap();
        // End to end: the emitted program drops nothing anywhere and keeps
        // its C free exactly where it was (R395-2's free timing).
        let outcome = bo::rewrite_core_injected(
            ::utils::compilation::str_to_input(&source),
            None,
            bo::MAX_REVERT_ROUNDS,
            &|_| {},
            false,
            true,
            true,
            Some((
                bo::A5Mode::PreciseReplay,
                Some(bo::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        );
        let bo::RewriteOutcome::Emitted { source, .. } = outcome else { panic!("{outcome:?}") };
        assert!(!source.contains("::std::mem::drop("), "{source}");
        assert_eq!(
            source.matches("free(root as *mut libc::c_void);").count(),
            1,
            "{source}"
        );
    }

    #[test]
    fn source_two_buffer_constructor_free_and_unwind_inventory() {
        let source = bo::ownership_fields_native_tests::native_fixture_source(
            "edt_with_payload",
            "edt_with_payload(pl1,pl2);",
        );
        for name in ["pl1", "pl2"] {
            let (count, frees, calls, unwinds) = inspect(&source, name).unwrap();
            assert_eq!((count, frees, calls), ("2".into(), 1, 1));
            assert!(
                unwinds >= 1,
                "the ordinary call's generated unwind remains owed"
            );
        }
    }
    #[test]
    fn source_repeated_calls_keep_exact_owner_and_free() {
        let source = bo::ownership_fields_native_tests::native_fixture_source(
            "edt",
            "edt(pl1,pl2);*pl1=*pl2;edt(pl1,pl2);",
        );
        for name in ["pl1", "pl2"] {
            let (count, frees, calls, unwinds) = inspect(&source, name).unwrap();
            assert_eq!((count, frees, calls), ("2".into(), 1, 2));
            assert!(unwinds >= 2);
        }
    }
    #[test]
    fn source_missing_free_is_not_no_extra_close_evidence() {
        let source =
            bo::ownership_fields_native_tests::native_fixture_source("edt", "edt(pl1,pl2);")
                .replace("free(pl1 as *mut core::ffi::c_void);", "");
        assert!(matches!(
            inspect(&source, "pl1"),
            Err(SourceHold::FreeIdentity | SourceHold::NormalExitCoverage)
        ));
    }
    #[test]
    fn source_pointer_reassignment_and_escape_hold() {
        let source = bo::ownership_fields_native_tests::native_fixture_source(
            "edt",
            "pl1=pl2;edt(pl1,pl2);",
        );
        assert!(matches!(
            inspect(&source, "pl1"),
            Err(SourceHold::UnsupportedOwnerUse)
        ));
    }
    #[test]
    fn source_reference_and_raw_address_ancestors_hold() {
        for extra in [
            "let r = &*pl1;",
            "let r = &raw const *pl1;",
            "let alias = pl1;",
        ] {
            let source = bo::ownership_fields_native_tests::native_fixture_source(
                "edt",
                &format!("{extra} edt(pl1,pl2);"),
            );
            assert!(matches!(
                inspect(&source, "pl1"),
                Err(SourceHold::UnsupportedOwnerUse)
            ));
        }
    }
    #[test]
    fn source_pointer_returning_call_is_not_a_lend() {
        let source = bo::ownership_fields_native_tests::native_fixture_source(
            "edt",
            "edt(pl1,pl2);",
        )
        .replace(
            "unsafe fn edt(input:*mut f32,output:*mut f32) { *output=*input+1.0; }",
            "unsafe fn edt(input:*mut f32,output:*mut f32)->*mut f32 { *output=*input+1.0; input }",
        );
        assert!(matches!(
            inspect(&source, "pl1"),
            Err(SourceHold::UnsupportedOwnerUse)
        ));
    }
    #[test]
    fn source_local_allocator_impostor_is_not_a_c_contract() {
        let source = bo::ownership_fields_native_tests::native_fixture_source("edt", "edt(pl1,pl2);")
            .replace("fn calloc(count:usize,size:usize)->*mut core::ffi::c_void;", "")
            .replace("unsafe fn edt", "unsafe fn calloc(count:usize,size:usize)->*mut core::ffi::c_void { core::ptr::null_mut() } unsafe fn edt");
        assert!(matches!(
            inspect(&source, "pl1"),
            Err(SourceHold::ConstructorIdentity)
        ));
    }

    #[test]
    fn source_zero_count_is_not_a_nonempty_constructor() {
        let source =
            bo::ownership_fields_native_tests::native_fixture_source("edt", "edt(pl1,pl2);")
                .replace("calloc(2,", "calloc(0,");
        assert!(matches!(
            inspect(&source, "pl1"),
            Err(SourceHold::ConstructorShape)
        ));
    }
    #[test]
    fn source_cp2_loop_local_allocation_has_one_close_per_iteration() {
        let source = r#"
            extern "C" {
                fn calloc(n:usize,s:usize)->*mut core::ffi::c_void;
                fn free(p:*mut core::ffi::c_void);
            }
            unsafe fn edt(p:*mut f32) { *p=2.0; }
            pub unsafe fn transform_to_coordfield(mut width:i32) {
                while width>0 {
                    let mut pl1=calloc(2,core::mem::size_of::<f32>()) as *mut f32;
                    let mut y=0;
                    while y<2 { *pl1.offset(y as isize)=1.0; y+=1; }
                    edt(pl1);
                    free(pl1 as *mut core::ffi::c_void);
                    width-=1;
                }
            }
        "#;
        assert!(
            inspect(source, "pl1").is_ok(),
            "R376 loop-local root, direct offsets and C-free backedge"
        );
    }
    #[test]
    fn source_cp2_branch_and_loop_preserve_the_single_sink() {
        for operation in [
            "if *pl1>0.0 { edt(pl1,pl2); }",
            "while *pl1>0.0 { edt(pl1,pl2); *pl1=0.0; }",
            "*pl1.offset(1 as isize)=*pl2.offset(0 as isize); edt(pl1,pl2);",
        ] {
            let source = bo::ownership_fields_native_tests::native_fixture_source("edt", operation);
            for name in ["pl1", "pl2"] {
                assert!(inspect(&source, name).is_ok(), "R376 {name}: {operation}");
            }
        }
    }
    #[test]
    fn source_cp2_constructor_shapes_share_native_source_evidence() {
        let base = bo::ownership_fields_native_tests::native_fixture_source("edt", "edt(pl1,pl2);");
        for count in ["size", "(height+1)*(width+1)"] {
            let source=base.replace("count:usize,size:usize", "count:core::ffi::c_ulong,size:core::ffi::c_ulong")
                .replace("let mut pl1=", "let (width,height)=(2,3); let size=width*height; let mut pl1=")
                .replace("calloc(2,core::mem::size_of::<f32>())", &format!("calloc(({count}) as core::ffi::c_ulong,core::mem::size_of::<f32>() as core::ffi::c_ulong)"));
            assert!(
                inspect(&source, "pl1").is_ok(),
                "R376 same count value {count}"
            );
        }
        let source = base
            .replace("f32", "u16")
            .replace("1.0", "1u16")
            .replace("3.0", "3u16");
        assert!(inspect(&source, "pl1").is_ok(), "R376 uint16_t cast target");
    }
    #[test]
    fn source_cp2_live_exit_and_repeat_free_hold() {
        for operation in [
            "if *pl1>0.0 { return 0.0; } edt(pl1,pl2);",
            "while *pl1>0.0 { free(pl1 as *mut core::ffi::c_void); } edt(pl1,pl2);",
        ] {
            let source = bo::ownership_fields_native_tests::native_fixture_source("edt", operation);
            assert!(
                matches!(
                    inspect(&source, "pl1"),
                    Err(SourceHold::NormalExitCoverage
                        | SourceHold::FreeIdentity
                        | SourceHold::UnsupportedOwnerUse)
                ),
                "R376 unclosed/repeated free: {operation}"
            );
        }
    }
}
