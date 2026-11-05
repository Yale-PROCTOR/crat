//! **Wave-6o (relay 096, fan-out 008 finding 12) — a null literal one field
//! away.**
//!
//! The optional arm's construction-site fact is local: a null initializer, a
//! null assignment, a caller's null argument. A value that reaches a local
//! THROUGH a pointer field carries the field's constructions, and a field the
//! program writes the null literal into (`(*array).start = 0 as *mut T`,
//! `S { next: 0 as *mut T, .. }`) makes every read of it possibly null. When
//! the field itself is converted, the load into a non-nullable local is
//! bridged by the field family's `.unwrap()`, which panics on null and never
//! forms a reference from it. When the field STAYS RAW, the only bridge is
//! `&*(*array).start`, and a null there is a null reference.
//!
//! json.h's `json_extract_get_{array,object}_size::element` is the corpus
//! shape. The parser writes null into `start` (an empty array) and into the
//! last element's `next`. The size walk is bounded by the count, so it holds
//! the null without dereferencing it, and the input is UB-free. The plain
//! reference was UB on `[]` and on `[1]` (Miri, wave-6o report 082).
//!
//! The rule: a LOCAL subject whose initializer or any assignment is a read
//! of such a field (under identity casts) is nullable. The optional arm
//! decides the form from there, exactly as it does for `let p = 0 as *mut T`.
//! A field stays raw when its depth-0 model kind is neither Ref nor Owning,
//! or when the field family holds it.
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    Expr, ExprKind, HirId, LetStmt, PatKind, QPath,
    def::Res,
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{TyKind, TypeckResults};

use super::field_reference::{FieldCandidates, FieldKey};
use crate::{
    analyses::borrow_ownership::{
        SlotKind, crate_slots::CrateSlots, slots::StructFieldSlot, solver::SlotRef,
    },
    utils::rustc::RustProgram,
};

/// `(fn, binding)` of every local whose value may be a null read from a raw
/// field.
pub(crate) type NullFieldReads = FxHashSet<(LocalDefId, HirId)>;

pub(crate) fn derive(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
    fields: &FieldCandidates,
) -> NullFieldReads {
    let tcx = program.tcx;
    let held: FxHashSet<FieldKey> = fields.holds.iter().map(|(key, ..)| *key).collect();
    let stays_raw = |key: FieldKey| {
        let slot = StructFieldSlot {
            struct_did: key.struct_did,
            field_index: key.field_index,
        };
        let kind = slots
            .field_slots
            .slot_for_field_depth(slot, 0)
            .and_then(|id| model.get(&SlotRef::Field(id)));
        !matches!(kind, Some(SlotKind::Ref | SlotKind::Owning)) || held.contains(&key)
    };
    let mut null_written = FxHashSet::default();
    for &owner in &program.functions {
        let Some(body_id) = tcx.hir_node_by_def_id(owner).body_id() else { continue };
        NullStores {
            typeck: tcx.typeck(owner),
            out: &mut null_written,
        }
        .visit_body(tcx.hir_body(body_id));
    }
    null_written.retain(|key| stays_raw(*key));
    let mut out = NullFieldReads::default();
    if null_written.is_empty() {
        return out;
    }
    for &owner in &program.functions {
        let Some(body_id) = tcx.hir_node_by_def_id(owner).body_id() else { continue };
        FieldReads {
            owner,
            typeck: tcx.typeck(owner),
            fields: &null_written,
            out: &mut out,
        }
        .visit_body(tcx.hir_body(body_id));
    }
    out
}

/// The field a field-projection expression names.
fn field_key(typeck: &TypeckResults<'_>, expr: &Expr<'_>) -> Option<FieldKey> {
    let ExprKind::Field(base, _) = expr.kind else { return None };
    let TyKind::Adt(def, _) = typeck.expr_ty_adjusted(base).kind() else { return None };
    let struct_did = def.did().as_local()?;
    let index = typeck.opt_field_index(expr.hir_id)?;
    Some(FieldKey {
        struct_did,
        field_index: index.as_usize(),
    })
}

fn is_raw_pointer(typeck: &TypeckResults<'_>, expr: &Expr<'_>) -> bool {
    matches!(typeck.expr_ty(expr).kind(), TyKind::RawPtr(..))
}

struct NullStores<'a, 'tcx> {
    typeck: &'tcx TypeckResults<'tcx>,
    out: &'a mut FxHashSet<FieldKey>,
}

impl<'tcx> Visitor<'tcx> for NullStores<'_, 'tcx> {
    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        match expr.kind {
            ExprKind::Assign(lhs, rhs, _) if super::emitability::is_zero_literal(rhs) => {
                if is_raw_pointer(self.typeck, lhs)
                    && let Some(key) = field_key(self.typeck, lhs)
                {
                    self.out.insert(key);
                }
            }
            ExprKind::Struct(_, literal_fields, _) => {
                if let TyKind::Adt(def, _) = self.typeck.expr_ty(expr).kind()
                    && let Some(struct_did) = def.did().as_local()
                {
                    for field in literal_fields {
                        if super::emitability::is_zero_literal(field.expr)
                            && is_raw_pointer(self.typeck, field.expr)
                            && let Some(index) = self.typeck.opt_field_index(field.hir_id)
                        {
                            self.out.insert(FieldKey {
                                struct_did,
                                field_index: index.as_usize(),
                            });
                        }
                    }
                }
            }
            _ => {}
        }
        intravisit::walk_expr(self, expr);
    }
}

struct FieldReads<'a, 'tcx> {
    owner: LocalDefId,
    typeck: &'tcx TypeckResults<'tcx>,
    fields: &'a FxHashSet<FieldKey>,
    out: &'a mut NullFieldReads,
}

impl FieldReads<'_, '_> {
    /// Does `value` (under identity casts) read a null-written raw field?
    fn reads_null_field(&self, value: &Expr<'_>) -> bool {
        let mut value = value;
        while let ExprKind::Cast(inner, _) | ExprKind::DropTemps(inner) = value.kind {
            value = inner;
        }
        field_key(self.typeck, value).is_some_and(|key| self.fields.contains(&key))
    }
}

impl<'tcx> Visitor<'tcx> for FieldReads<'_, 'tcx> {
    fn visit_local(&mut self, local: &'tcx LetStmt<'tcx>) {
        if let PatKind::Binding(_, binding, _, None) = local.pat.kind
            && let Some(init) = local.init
            && self.reads_null_field(init)
        {
            self.out.insert((self.owner, binding));
        }
        intravisit::walk_local(self, local);
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if let ExprKind::Assign(lhs, rhs, _) = expr.kind
            && let ExprKind::Path(QPath::Resolved(None, path)) = lhs.kind
            && let Res::Local(binding) = path.res
            && self.reads_null_field(rhs)
        {
            self.out.insert((self.owner, binding));
        }
        intravisit::walk_expr(self, expr);
    }
}
