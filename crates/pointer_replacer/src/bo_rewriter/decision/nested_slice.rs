//! R384: relocate already-admitted local slice formations into finite wrapper
//! descriptors. This module inherits dispositions; it does not classify aliases.

#[path = "nested_accumulator.rs"]
mod accumulator;

#[path = "nested_one_sided.rs"]
mod one_sided;

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    BinOpKind, Expr, ExprKind, HirId, PatKind, QPath, StmtKind, UnOp,
    def::Res,
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{TyCtxt, TyKind};

use super::{
    Arm, Decision, DecisionTable, SubjectKind,
    construction::{SliceLengthPlan, SliceLengthSource},
    exposure::ExposureSurfacePlan,
};
use crate::{
    analyses::borrow_ownership::{SlotKind, crate_slots::CrateSlots, solver::SlotRef},
    bo_rewriter::{
        additive::{FamilyPolicy, FamilyStage},
        bridge_receipt::{BridgeExtentKind, SignatureClassId},
        mechanical_receipt::MechanicalExtent,
        plan::ClassFinalization,
    },
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Hold {
    OuterNotDelivered,
    InnerNotRef,
    StorageUnproved,
    PairRequired,
    IntervalChanged,
    CountRelationUnproved,
    NullableLevelUnbuilt,
    RawBoundaryUnbuilt,
    DirectCallerUnbuilt,
    DeclarationUnbuilt,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Row {
    pub(crate) parameter: HirId,
    pub(crate) local: HirId,
    pub(crate) init: HirId,
    pub(crate) index: u64,
    pub(crate) mutable: bool,
    pub(crate) was_fallback: bool,
    /// The length expression the WRAPPER uses to build this row's view. The
    /// pair rule binds the positive count once (`__crat_nested_count`); N1
    /// carries the row's own already-planned expression across unchanged, so a
    /// fabricated extent stays fabricated and keeps its receipt.
    pub(crate) length: String,
    pub(crate) raw_name: String,
    pub(crate) view_name: String,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Parameter {
    pub(crate) hir: HirId,
    pub(crate) index: usize,
    pub(crate) name: String,
    pub(crate) descriptor_name: String,
    pub(crate) mutable: bool,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Plan {
    /// **The arm discriminator** (relay 042, R447-3). `true` for THIS rule —
    /// the pair arm (R384), which binds one positive count
    /// (`__crat_nested_count`) and guards the whole wrapper with it. R435-1
    /// chartered a second producer for the same receipt list, and a control
    /// that means "the pair arm did not admit" must ask for the arm rather
    /// than for the list being empty.
    ///
    /// Nested N1 (R450-10, the composition's single definition): the pair
    /// rule's wrapper returns early on a non-positive count and binds it once.
    /// N1 does not — its rows carry their own length expressions and the
    /// helper body it leaves behind still runs at a non-positive count, so N1
    /// sets this `false` and `prefix()`'s guard, `promote`'s length branch and
    /// `observe`'s `arm` key all read it.
    pub(crate) count_guard: bool,
    pub(crate) owner: LocalDefId,
    pub(crate) count: HirId,
    pub(crate) count_name: String,
    pub(crate) accumulator: Option<HirId>,
    pub(crate) conditional_updates: Vec<HirId>,
    pub(crate) rows: Vec<Row>,
    pub(crate) parameters: Vec<Parameter>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Receipt {
    pub(crate) owner: LocalDefId,
    pub(crate) result: Result<Plan, Hold>,
}
impl Plan {
    pub(crate) fn argument(&self, index: usize) -> Option<String> {
        self.parameters.iter().find(|p| p.index == index).map(|p| {
            format!(
                "&{}{}",
                if p.mutable { "mut " } else { "" },
                p.descriptor_name
            )
        })
    }

    pub(crate) fn required_nodes(&self) -> impl Iterator<Item = HirId> + '_ {
        self.parameters
            .iter()
            .map(|p| p.hir)
            .chain(self.rows.iter().map(|r| r.local))
    }

    pub(crate) fn prefix(&self) -> String {
        let mut s = String::new();
        for row in &self.rows {
            let parameter = self
                .parameters
                .iter()
                .find(|p| p.hir == row.parameter)
                .unwrap();
            s += &format!(
                "let {} = *{}.add({});\n",
                row.raw_name, parameter.name, row.index
            );
        }
        // Source table cells are loaded even on this branch; dormant inner
        // values are never converted to references or negative usize counts.
        if self.count_guard {
            s += &format!(
                "if {} <= 0 {{ return 0; }}\nlet __crat_nested_count = {} as usize;\n",
                self.count_name, self.count_name
            );
        }
        for row in &self.rows {
            s += &format!(
                "let {} = ::core::slice::from_raw_parts{}({}, {});\n",
                row.view_name,
                if row.mutable { "_mut" } else { "" },
                row.raw_name,
                row.length
            );
        }
        for parameter in &self.parameters {
            let rows = self
                .rows
                .iter()
                .filter(|r| r.parameter == parameter.hir)
                .map(|r| r.view_name.clone())
                .collect::<Vec<_>>()
                .join(", ");
            s += &format!(
                "let {}{} = [{rows}];\n",
                if parameter.mutable { "mut " } else { "" },
                parameter.descriptor_name
            );
        }
        s
    }
}

fn peel<'a, 'tcx>(mut e: &'a Expr<'tcx>) -> &'a Expr<'tcx> {
    while let ExprKind::DropTemps(inner) = e.kind {
        e = inner;
    }
    e
}
fn binding(e: &Expr<'_>) -> Option<HirId> {
    match peel(e).kind {
        ExprKind::Path(QPath::Resolved(_, p)) => {
            if let Res::Local(h) = p.res {
                Some(h)
            } else {
                None
            }
        }
        _ => None,
    }
}
fn integer(mut e: &Expr<'_>) -> Option<u64> {
    while let ExprKind::Cast(inner, _) | ExprKind::DropTemps(inner) = e.kind {
        e = inner;
    }
    match peel(e).kind {
        ExprKind::Lit(lit) => {
            if let rustc_ast::LitKind::Int(value, _) = lit.node {
                u64::try_from(value.get()).ok().filter(|v| *v <= 127)
            } else {
                None
            }
        }
        _ => None,
    }
}
fn named(pat: &rustc_hir::Pat<'_>) -> Option<(HirId, String)> {
    if let PatKind::Binding(_, id, ident, None) = pat.kind {
        Some((id, ident.to_string()))
    } else {
        None
    }
}
fn offset<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    e: &'tcx Expr<'tcx>,
) -> Option<(&'tcx Expr<'tcx>, &'tcx Expr<'tcx>)> {
    let ExprKind::MethodCall(_, receiver, [arg], _) = e.kind else { return None };
    let method = tcx.typeck(owner).type_dependent_def_id(e.hir_id)?;
    (tcx.crate_name(method.krate).as_str() == "core"
        && tcx.item_name(method).as_str() == "offset"
        && tcx.typeck(owner).expr_ty(receiver).is_raw_ptr())
    .then_some((receiver, arg))
}

fn index_binding(tcx: TyCtxt<'_>, owner: LocalDefId, e: &Expr<'_>) -> Option<HirId> {
    let ExprKind::Cast(inner, _) = peel(e).kind else { return None };
    let types = tcx.typeck(owner);
    (types.expr_ty(e).to_string() == "isize"
        && types.expr_ty(inner).to_string() == "i32"
        && tcx.data_layout.pointer_size.bits() >= 32)
        .then(|| binding(inner))
        .flatten()
}
struct Names {
    valid: bool,
}
impl<'tcx> Visitor<'tcx> for Names {
    fn visit_pat(&mut self, pat: &'tcx rustc_hir::Pat<'tcx>) {
        if let Some((_, name)) = named(pat) {
            self.valid &= !name.starts_with("__crat_nested_");
        }
        intravisit::walk_pat(self, pat);
    }
}

struct LoopCheck<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    index: HirId,
    count: HirId,
    rows: &'a FxHashSet<HirId>,
    tables: &'a FxHashSet<HirId>,
    valid: bool,
    offsets: FxHashMap<HirId, usize>,
    increments: usize,
    accumulator: Option<HirId>,
    conditional_updates: Vec<HirId>,
}
impl<'tcx> Visitor<'tcx> for LoopCheck<'_, 'tcx> {
    fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
        if let Some(id) = binding(e) {
            if self.tables.contains(&id) || self.rows.contains(&id) {
                self.valid = false;
            }
        }
        match e.kind {
            ExprKind::Unary(UnOp::Deref, inner) => {
                if let Some((receiver, arg)) = offset(self.tcx, self.owner, inner)
                    && binding(receiver).is_some_and(|id| self.rows.contains(&id))
                    && index_binding(self.tcx, self.owner, arg) == Some(self.index)
                {
                    *self.offsets.entry(binding(receiver).unwrap()).or_default() += 1;
                    return;
                }
                self.valid = false;
            }
            ExprKind::AssignOp(op, left, right) if binding(left) == Some(self.index) => {
                self.increments += 1;
                self.valid &=
                    op.node == rustc_ast::AssignOpKind::AddAssign && integer(right) == Some(1);
                return;
            }
            ExprKind::Assign(left, _, _) | ExprKind::AssignOp(_, left, _) if matches!(binding(left), Some(id) if id == self.index || id == self.count) => {
                self.valid = false
            }
            ExprKind::If(condition, then, None) => {
                let Some(accumulator) = self.accumulator else {
                    self.valid = false;
                    return;
                };
                if !accumulator::condition(self, condition)
                    || !accumulator::update(self, then, accumulator)
                {
                    self.valid = false;
                    return;
                }
                self.conditional_updates.push(e.hir_id);
                // The strict scalar whitelist has excluded pointer/index/count
                // writes and calls. Reuse the existing row-use collector only
                // after validation; these are syntactic, not per-path accesses.
                self.visit_expr(condition);
                self.visit_expr(then);
                return;
            }
            ExprKind::Loop(..)
            | ExprKind::Ret(..)
            | ExprKind::Break(..)
            | ExprKind::Continue(..)
            | ExprKind::InlineAsm(..)
            | ExprKind::AddrOf(..)
            | ExprKind::Closure(..)
            | ExprKind::MethodCall(..)
            | ExprKind::If(..)
            | ExprKind::Match(..) => self.valid = false,
            ExprKind::Call(_, args) => {
                self.valid &= args
                    .iter()
                    .all(|arg| !self.tcx.typeck(self.owner).expr_ty(arg).is_raw_ptr());
            }
            _ => {}
        }
        intravisit::walk_expr(self, e);
    }
}

fn flat_slice(decision: &Decision) -> Option<(bool, &Vec<super::emitability::UseEdit>)> {
    match decision {
        Decision::Slice { mutable, uses } => Some((*mutable, uses)),
        Decision::NestedSlice { .. }
        | Decision::Cursor { .. }
        | Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Opt { .. }
        | Decision::Box(_)
        | Decision::Degraded(_) => None,
    }
}
pub(crate) fn inherited_pair(required: super::RequiredArmSet) -> Result<(), Hold> {
    if required.contains(Arm::Pair) {
        Err(Hold::PairRequired)
    } else {
        Ok(())
    }
}

pub(super) struct Prelude<'tcx> {
    pub(super) block: &'tcx rustc_hir::Block<'tcx>,
    pub(super) count: HirId,
    pub(super) count_name: String,
    pub(super) signature: rustc_middle::ty::FnSig<'tcx>,
}

/// The conditions both nested arms share: the class is ready, the owner has an
/// exposure wrapper this lane may extend, no other seam edits that wrapper, no
/// generated name is already taken, and the body is a `size: i32 -> i32` unsafe
/// block with no tail expression.
pub(super) fn prelude<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    table: &DecisionTable,
    ready: &ClassFinalization,
) -> Result<Prelude<'tcx>, Hold> {
    if !ready
        .classes
        .get(&SignatureClassId::of(owner))
        .is_some_and(|c| c.is_ready())
    {
        return Err(Hold::OuterNotDelivered);
    }
    let exposure = table.exposure.as_ref().ok_or(Hold::OuterNotDelivered)?;
    if !matches!(
        exposure.plan(owner),
        ExposureSurfacePlan::PositiveSeedShim | ExposureSurfacePlan::FnPtrRawWrapper
    ) {
        return Err(Hold::DirectCallerUnbuilt);
    }
    // No direct safe caller or raw inner seam is changed by this first P3 arm.
    if table
        .seams
        .edits
        .iter()
        .any(|s| s.owner_class == SignatureClassId::of(owner))
    {
        return Err(Hold::DirectCallerUnbuilt);
    }
    let body = tcx.hir_body(
        tcx.hir_node_by_def_id(owner)
            .body_id()
            .ok_or(Hold::StorageUnproved)?,
    );
    let mut names = Names { valid: true };
    for p in body.params {
        names.visit_pat(p.pat);
    }
    names.visit_expr(body.value);
    if !names.valid {
        return Err(Hold::DeclarationUnbuilt);
    }
    let count_param = body.params.first().ok_or(Hold::CountRelationUnproved)?;
    let (count, count_name) = named(count_param.pat).ok_or(Hold::DeclarationUnbuilt)?;
    let signature = tcx.fn_sig(owner.to_def_id()).skip_binder().skip_binder();
    if signature.inputs()[0].to_string() != "i32"
        || signature.output().to_string() != "i32"
        || !signature.safety.is_unsafe()
    {
        return Err(Hold::CountRelationUnproved);
    }
    let ExprKind::Block(block, _) = body.value.kind else { return Err(Hold::IntervalChanged) };
    if block.expr.is_some() {
        return Err(Hold::IntervalChanged);
    }
    Ok(Prelude {
        block,
        count,
        count_name,
        signature,
    })
}

/// The pair rule leads; where it holds, N1 (R436-1) tries the per-parameter
/// substitution on the same owner. A held owner keeps the PAIR's hold, so no
/// receipt already in the census moves unless N1 actually delivers.
fn inspect<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    table: &DecisionTable,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
    ready: &ClassFinalization,
) -> Result<Plan, Hold> {
    match inspect_pair(tcx, owner, table, slots, model, ready) {
        Ok(plan) => Ok(plan),
        Err(pair) => one_sided::inspect(tcx, owner, table, slots, model, ready).map_err(|_| pair),
    }
}

fn inspect_pair<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    table: &DecisionTable,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
    ready: &ClassFinalization,
) -> Result<Plan, Hold> {
    let Prelude {
        block,
        count,
        count_name,
        signature,
    } = prelude(tcx, owner, table, ready)?;
    let subjects = table
        .entries
        .iter()
        .filter(|(s, _)| s.fn_did == owner)
        .collect::<Vec<_>>();
    let mut parameters = Vec::new();
    for (s, d) in &subjects {
        if s.ptr_depth != 2 {
            continue;
        }
        let SubjectKind::Param { hir_index } = s.kind else { return Err(Hold::StorageUnproved) };
        if !flat_slice(d).is_some_and(|(mutable, _)| !mutable) {
            return Err(Hold::NullableLevelUnbuilt);
        }
        let spelling = s
            .pointee_span
            .and_then(|span| tcx.sess.source_map().span_to_snippet(span).ok())
            .ok_or(Hold::DeclarationUnbuilt)?;
        if !spelling.trim_start().starts_with("*const ")
            && !spelling.trim_start().starts_with("*mut ")
        {
            return Err(Hold::DeclarationUnbuilt);
        }

        let slot = slots.fn_local_slots[&owner]
            .slot_for_local_depth(s.local, 1)
            .ok_or(Hold::InnerNotRef)?;
        if model.get(&SlotRef::Local(owner, slot)) != Some(&SlotKind::Ref) {
            return Err(Hold::InnerNotRef);
        }
        let TyKind::RawPtr(inner, _) = signature.inputs()[hir_index].kind() else {
            return Err(Hold::StorageUnproved);
        };
        let TyKind::RawPtr(element, _) = inner.kind() else { return Err(Hold::StorageUnproved) };
        if element.to_string() != "f64" {
            return Err(Hold::StorageUnproved);
        }
        parameters.push(Parameter {
            hir: s.hir_id,
            index: hir_index,
            name: s.param_name.clone().ok_or(Hold::DeclarationUnbuilt)?,
            descriptor_name: format!("__crat_nested_{}_rows", s.hir_id.local_id.as_u32()),
            mutable: false,
        });
    }
    if parameters.len() != 2 {
        return Err(Hold::StorageUnproved);
    }
    let tables = parameters.iter().map(|p| p.hir).collect::<FxHashSet<_>>();
    let mut rows = Vec::new();
    let mut index = None;
    let mut accumulator = None;
    let mut conditional_updates = Vec::new();
    let mut loop_seen = false;
    let mut returned = false;
    for stmt in block.stmts {
        match stmt.kind {
            StmtKind::Let(local) if !loop_seen => {
                let (id, name) = named(local.pat).ok_or(Hold::DeclarationUnbuilt)?;
                if name.starts_with("__crat_nested_") {
                    return Err(Hold::DeclarationUnbuilt);
                }
                let init = local.init.ok_or(Hold::IntervalChanged)?;
                if let ExprKind::Unary(UnOp::Deref, operand) = peel(init).kind
                    && let Some((receiver, arg)) = offset(tcx, owner, operand)
                    && let Some(parameter) = binding(receiver).filter(|p| tables.contains(p))
                {
                    if index.is_some() || accumulator.is_some() {
                        return Err(Hold::IntervalChanged);
                    }
                    let projection = integer(arg).ok_or(Hold::CountRelationUnproved)?;
                    let (_, decision) = subjects
                        .iter()
                        .find(|(s, _)| s.hir_id == id)
                        .ok_or(Hold::OuterNotDelivered)?;
                    let (mutable, _) = flat_slice(decision).ok_or(Hold::OuterNotDelivered)?;
                    inherited_pair(
                        table
                            .arm_requirements
                            .get(&(owner, id))
                            .copied()
                            .unwrap_or_default(),
                    )?;
                    let construction = table
                        .slice_constructions
                        .iter()
                        .find(|c| c.node == (owner, id))
                        .ok_or(Hold::OuterNotDelivered)?;
                    if construction.init_hir != init.hir_id
                        || construction.mutable != mutable
                        || tcx
                            .typeck(owner)
                            .expr_ty(init)
                            .builtin_deref(true)
                            .is_none()
                        || construction.hold_reason.is_some()
                        || construction.replacement.is_none()
                        || construction.nullable
                    {
                        return Err(Hold::OuterNotDelivered);
                    }
                    rows.push(Row {
                        parameter,
                        local: id,
                        init: construction.init_hir,
                        index: projection,
                        mutable,
                        was_fallback: construction.length.is_fallback(),
                        length: "__crat_nested_count".to_owned(),
                        raw_name: format!("__crat_nested_{}_raw", id.local_id.as_u32()),
                        view_name: format!("__crat_nested_{}_view", id.local_id.as_u32()),
                    });
                } else if integer(init) == Some(0)
                    && tcx.typeck(owner).node_type(id).to_string() == "f64"
                    && index.is_none()
                    && accumulator.is_none()
                    && !rows.is_empty()
                {
                    // Pure scalar zero initialization remains in the original
                    // body. No table load may occur after it in this rule.
                    accumulator = Some(id);
                } else if integer(init) == Some(0)
                    && tcx.typeck(owner).node_type(id).to_string() == "i32"
                    && index.is_none()
                {
                    index = Some(id);
                } else {
                    return Err(Hold::IntervalChanged);
                }
            }
            StmtKind::Expr(e) | StmtKind::Semi(e) => match e.kind {
                ExprKind::Assign(left, right, _)
                    if !loop_seen
                        && index.is_some()
                        && binding(left) == index
                        && integer(right) == Some(0) => {}
                ExprKind::Loop(b, None, rustc_hir::LoopSource::While, _) if !loop_seen => {
                    let ExprKind::If(condition, then, _) =
                        b.expr.ok_or(Hold::CountRelationUnproved)?.kind
                    else {
                        return Err(Hold::CountRelationUnproved);
                    };
                    let ExprKind::Binary(op, left, right) = peel(condition).kind else {
                        return Err(Hold::CountRelationUnproved);
                    };
                    if op.node != BinOpKind::Lt
                        || binding(left) != index
                        || binding(right) != Some(count)
                    {
                        return Err(Hold::CountRelationUnproved);
                    }
                    let ExprKind::Block(loop_body, _) = then.kind else {
                        return Err(Hold::CountRelationUnproved);
                    };
                    let last = loop_body
                        .expr
                        .or_else(|| {
                            loop_body.stmts.last().and_then(|s| match s.kind {
                                StmtKind::Expr(e) | StmtKind::Semi(e) => Some(e),
                                _ => None,
                            })
                        })
                        .ok_or(Hold::CountRelationUnproved)?;
                    if !matches!(last.kind, ExprKind::AssignOp(op, left, right) if op.node == rustc_ast::AssignOpKind::AddAssign && binding(left) == index && integer(right) == Some(1))
                    {
                        return Err(Hold::CountRelationUnproved);
                    }
                    let row_ids = rows.iter().map(|r| r.local).collect::<FxHashSet<_>>();
                    let mut check = LoopCheck {
                        tcx,
                        owner,
                        index: index.ok_or(Hold::CountRelationUnproved)?,
                        count,
                        rows: &row_ids,
                        tables: &tables,
                        valid: true,
                        offsets: FxHashMap::default(),
                        increments: 0,
                        accumulator,
                        conditional_updates: Vec::new(),
                    };
                    check.visit_expr(then);
                    if !check.valid
                        || check.increments != 1
                        || row_ids.iter().any(|id| !check.offsets.contains_key(id))
                    {
                        return Err(Hold::RawBoundaryUnbuilt);
                    }
                    conditional_updates = check.conditional_updates;
                    loop_seen = true;
                }
                ExprKind::Ret(Some(value))
                    if loop_seen && integer(value) == Some(0) && !returned =>
                {
                    returned = true
                }
                _ => return Err(Hold::IntervalChanged),
            },
            _ => return Err(Hold::IntervalChanged),
        }
    }
    if !loop_seen || !returned {
        return Err(Hold::IntervalChanged);
    }
    for p in &mut parameters {
        let group = rows
            .iter()
            .filter(|r| r.parameter == p.hir)
            .collect::<Vec<_>>();
        if group.is_empty() || group.iter().enumerate().any(|(i, r)| r.index != i as u64) {
            return Err(Hold::StorageUnproved);
        }
        p.mutable = group[0].mutable;
        if group.iter().any(|r| r.mutable != p.mutable) {
            return Err(Hold::StorageUnproved);
        }
    }
    // Never relocate a local with an unbuilt raw boundary or an atom-level
    // withdrawal. Whole-class rollback is the supported transaction boundary.
    if subjects.iter().any(|(s, _)| {
        table
            .seams
            .raw_boundary_atom_groups
            .get(&(owner, s.hir_id))
            .is_some_and(|v| !v.is_empty())
    }) {
        return Err(Hold::RawBoundaryUnbuilt);
    }
    Ok(Plan {
        count_guard: true,
        owner,
        count,
        count_name,
        accumulator,
        conditional_updates,
        rows,
        parameters,
    })
}

pub(crate) fn promote(
    tcx: TyCtxt<'_>,
    table: &mut DecisionTable,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
    ready: &ClassFinalization,
    policy: &FamilyPolicy,
) -> bool {
    let mut owners = table
        .entries
        .iter()
        .filter(|(s, _)| {
            s.ptr_depth == 2 && policy.enabled_for((s.fn_did, s.hir_id), FamilyStage::Return)
        })
        .map(|(s, _)| s.fn_did)
        .collect::<Vec<_>>();
    owners.sort_by_key(|o| o.local_def_index.as_u32());
    owners.dedup();
    let mut changed = false;
    for owner in owners {
        let result = inspect(tcx, owner, table, slots, model, ready);
        if let Ok(plan) = &result {
            for p in &plan.parameters {
                let (_, d) = table
                    .entries
                    .iter_mut()
                    .find(|(s, _)| s.fn_did == owner && s.hir_id == p.hir)
                    .unwrap();
                let uses = flat_slice(d).expect("admitted flat predecessor").1.clone();
                *d = Decision::NestedSlice {
                    mutable: p.mutable,
                    inner_mutable: p.mutable,
                    uses,
                };
                for surface in table
                    .seams
                    .surface_arguments
                    .iter_mut()
                    .filter(|a| a.node == (owner, p.hir))
                {
                    surface.form = super::seam::form_of(d);
                    surface.spec.len = None;
                    surface.bridge.expected_form = surface.form.key().into();
                    surface.bridge.extent = BridgeExtentKind::Evidence(format!(
                        "nested-descriptor-array:{}",
                        plan.rows.iter().filter(|r| r.parameter == p.hir).count()
                    ));
                    surface.obligation.planned.expected_form = surface.form.key().into();
                    surface.obligation.planned.evidence.extent =
                        MechanicalExtent::Evidence("finite-scoped-descriptor-array".into());
                }
            }
            for row in &plan.rows {
                let p = plan
                    .parameters
                    .iter()
                    .find(|p| p.hir == row.parameter)
                    .unwrap();
                // N2 (R452-6/R475-3). A row whose inner value is consumed as a
                // CURSOR has no slice construction to rewrite: its constructor
                // belongs to the cursor family and is rebuilt there, by
                // `cursor_native::replan_delivered_table_elements`, after this
                // flip. A post-hoc rewrite of a finalised cursor plan costs the
                // cursor entirely (nested 007's A/B), and unwrapping here for a
                // row that has no slice construction panics outright.
                let Some(c) = table
                    .slice_constructions
                    .iter_mut()
                    .find(|c| c.node == (owner, row.local))
                else {
                    continue;
                };
                c.replacement = Some(format!(
                    "{}{}[{}]",
                    if row.mutable { "&mut *" } else { "" },
                    p.name,
                    row.index
                ));
                if plan.count_guard {
                    c.length = SliceLengthPlan {
                        expression: plan.count_name.clone(),
                        source: SliceLengthSource::AssociatedArgument {
                            owner,
                            argument_index: 0,
                        },
                        provenance: vec![super::construction::SliceLengthProvenance::Inherited {
                            owner,
                            binding: plan.count,
                        }],
                    };
                }
                // N1 relocates the extent; it does not re-source it, so a
                // fabricated length keeps its plan and its receipt.
                c.initializer_kind = if plan.count_guard {
                    "nested-reborrow-relocated"
                } else {
                    "nested-reborrow-relocated-fallback"
                };
            }
            changed = true;
        }
        table.nested_receipts.push(Receipt { owner, result });
    }
    changed
}

/// Only terminal decision data is serialized; the observer grants nothing.
pub(crate) fn observe(tcx: TyCtxt<'_>, table: &DecisionTable) {
    let Some(root) = std::env::var_os("CRAT_NESTED_ADMISSION_OUTPUT") else { return };
    assert_eq!(
        std::env::var("CRAT_ERA5_EXECUTION_ROLE").as_deref(),
        Ok("cache-only")
    );
    let program = std::env::var("CRAT_ERA5_PROGRAM").expect("nested receipt program identity");
    assert!(
        !program.is_empty()
            && program
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || "._-".contains(c))
    );
    let rows = table.nested_receipts.iter().map(|receipt| {
        let owner = tcx.def_path_str(receipt.owner.to_def_id());
        match &receipt.result {
            Ok(plan) => serde_json::json!({"owner":owner, "status":"planned", "inherited_pair":"not-required", "arm": if plan.count_guard { "pair" } else { "per-parameter" }, "count_hir":plan.count.local_id.as_u32(), "count":plan.count_name, "scalar_accumulator_hir":plan.accumulator.map(|h|h.local_id.as_u32()), "conditional_updates":plan.conditional_updates.iter().map(|h|h.local_id.as_u32()).collect::<Vec<_>>(),
                "parameters":plan.parameters.iter().map(|p|serde_json::json!({"hir":p.hir.local_id.as_u32(),"argument":p.index,"name":p.name,"inner_depth":1,"outer_mutable":p.mutable,"inner_mutable":p.mutable})).collect::<Vec<_>>(),
                "rows":plan.rows.iter().map(|r|serde_json::json!({"source_local_hir":r.local.local_id.as_u32(),"source_formation_hir":r.init.local_id.as_u32(),"table_hir":r.parameter.local_id.as_u32(),"projection":r.index,"destination":r.view_name,"inner_depth":1,"fabricated_before":r.was_fallback,"fabricated_after": !plan.count_guard && r.was_fallback})).collect::<Vec<_>>() }),
            Err(hold) => serde_json::json!({"owner":owner,"status":"held","hold":format!("{hold:?}")}),
        }
    }).collect::<Vec<_>>();
    let root = std::path::Path::new(&root);
    std::fs::create_dir_all(root).expect("nested receipt directory");
    let value = serde_json::json!({"program":program,"source":std::env::var("CRAT_RAW_BOUNDARY_CODE_FRAME").ok(),"pid":std::process::id(),"rows":rows,"custody":"planned-not-delivered"});
    std::fs::write(
        root.join(format!("{program}.json")),
        serde_json::to_vec_pretty(&value).unwrap(),
    )
    .expect("nested receipt write");
}
