/// Pointer-offset sign analysis.
///
/// Determines, for each pointer-typed local variable in each function, whether
/// any `.offset()` call on that pointer uses a potentially-negative argument.
///
/// - `needs_cursor() == false` → the pointer is only ever offset by non-negative
///   values; a plain `Slice`/`SliceRef` is sufficient.
/// - `needs_cursor() == true`  → the pointer may be offset negatively;
///   `SliceCursor`/`SliceCursorRef` is required.
use std::collections::VecDeque;

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::{IndexVec, bit_set::DenseBitSet};
use rustc_middle::{
    mir::{
        self, Body, Local, Location, Operand, Place, Rvalue, StatementKind, TerminatorEdges,
        TerminatorKind, visit::Visitor as MVisitor,
    },
    ty::{self, ScalarInt, Ty, TyCtxt},
};
use rustc_mir_dataflow::{
    Analysis, Forward, JoinSemiLattice, ResultsCursor, fmt::DebugWithContext,
};
use rustc_span::def_id::LocalDefId;
use utils::graph;

use crate::utils::rustc::RustProgram;

// Analysis output
#[derive(Debug, Default)]
pub struct OffsetSignResult {
    pub access_signs: FxHashMap<LocalDefId, DenseBitSet<Local>>,
}

/// abstract-value lattice combining concrete constants with sign
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AbsValue {
    Bottom,
    Zero,
    /// signed constant (non-zero)
    ConstI(i128),
    /// unsigned constant (non-zero)
    ConstU(u128),
    Pos,
    Neg,
    NonNeg,
    NonPos,
    Top,
}

// helpers
fn abs_from_i128(c: i128) -> AbsValue {
    if c == 0 {
        AbsValue::Zero
    } else {
        AbsValue::ConstI(c)
    }
}

fn abs_from_u128(c: u128) -> AbsValue {
    if c == 0 {
        AbsValue::Zero
    } else {
        AbsValue::ConstU(c)
    }
}

#[allow(dead_code)]
fn to_i128(v: AbsValue) -> Option<i128> {
    match v {
        AbsValue::Zero => Some(0),
        AbsValue::ConstI(c) => Some(c),
        AbsValue::ConstU(c) if c <= i128::MAX as u128 => Some(c as i128),
        _ => None,
    }
}

impl AbsValue {
    /// returns `true` when the value may be negative (cursor representation needed)
    pub fn needs_cursor(&self) -> bool {
        match self {
            AbsValue::Neg | AbsValue::NonPos | AbsValue::Top => true,
            AbsValue::ConstI(c) => *c < 0,
            _ => false,
        }
    }

    /// least upper bound in the lattice, returns `true` if `self` changed
    pub fn join(&mut self, other: &Self) -> bool {
        use AbsValue::*;
        let new = match (*self, *other) {
            (Bottom, v) | (v, Bottom) => v,
            (Top, _) | (_, Top) => Top,
            (v1, v2) if v1 == v2 => v1,
            // --- Zero ---
            (Zero, ConstI(c)) | (ConstI(c), Zero) => {
                if c > 0 {
                    NonNeg
                } else {
                    NonPos
                }
            }
            (Zero, ConstU(_))
            | (ConstU(_), Zero)
            | (Zero, Pos)
            | (Pos, Zero)
            | (Zero, NonNeg)
            | (NonNeg, Zero) => NonNeg,
            (Zero, Neg) | (Neg, Zero) | (Zero, NonPos) | (NonPos, Zero) => NonPos,
            // --- ConstI ---
            (ConstI(c1), ConstI(c2)) => {
                if c1 > 0 && c2 > 0 {
                    Pos
                } else if c1 < 0 && c2 < 0 {
                    Neg
                } else {
                    Top
                }
            }
            (ConstI(c), ConstU(_)) | (ConstU(_), ConstI(c)) => {
                if c > 0 {
                    Pos
                } else {
                    Top
                }
            }
            (ConstI(c), Pos) | (Pos, ConstI(c)) => {
                if c > 0 {
                    Pos
                } else {
                    Top
                }
            }
            (ConstI(c), Neg) | (Neg, ConstI(c)) => {
                if c < 0 {
                    Neg
                } else {
                    Top
                }
            }
            (ConstI(c), NonNeg) | (NonNeg, ConstI(c)) => {
                if c > 0 {
                    NonNeg
                } else {
                    Top
                }
            }
            (ConstI(c), NonPos) | (NonPos, ConstI(c)) => {
                if c < 0 {
                    NonPos
                } else {
                    Top
                }
            }
            // --- ConstU ---
            (ConstU(_), ConstU(_)) => Pos,
            (ConstU(_), Pos) | (Pos, ConstU(_)) => Pos,
            (ConstU(_), Neg) | (Neg, ConstU(_)) => Top,
            (ConstU(_), NonNeg) | (NonNeg, ConstU(_)) => NonNeg,
            (ConstU(_), NonPos) | (NonPos, ConstU(_)) => Top,
            // --- else ---
            (Pos, NonNeg) | (NonNeg, Pos) => NonNeg,
            (Neg, NonPos) | (NonPos, Neg) => NonPos,
            _ => Top,
        };
        if new != *self {
            *self = new;
            true
        } else {
            false
        }
    }

    pub fn add(&self, other: &AbsValue) -> AbsValue {
        use AbsValue::*;
        match (*self, *other) {
            (Bottom, _) | (_, Bottom) => Bottom,
            (Top, _) | (_, Top) => Top,
            // --- Zero ---
            (Zero, v) | (v, Zero) => v,
            // --- unsigned ---
            (ConstU(c1), ConstU(c2)) => abs_from_u128(c1.wrapping_add(c2)),
            // --- signed arithmetic ---
            (ConstI(c1), ConstI(c2)) => abs_from_i128(c1.wrapping_add(c2)),
            // --- sign-based rules ---
            (ConstI(c), Pos) | (Pos, ConstI(c)) if c > 0 => Pos,
            (ConstI(c), NonNeg) | (NonNeg, ConstI(c)) if c > 0 => Pos,
            (ConstI(c), Neg) | (Neg, ConstI(c)) if c < 0 => Neg,
            (ConstI(c), NonPos) | (NonPos, ConstI(c)) if c < 0 => Neg,
            (ConstU(_), Pos) | (Pos, ConstU(_)) => Pos,
            (ConstU(_), NonNeg) | (NonNeg, ConstU(_)) => Pos,
            (Pos, Pos) | (Pos, NonNeg) | (NonNeg, Pos) => Pos,
            (Neg, Neg) | (Neg, NonPos) | (NonPos, Neg) => Neg,
            (NonNeg, NonNeg) => NonNeg,
            (NonPos, NonPos) => NonPos,
            _ => Top,
        }
    }

    pub fn neg(&self) -> AbsValue {
        use AbsValue::*;
        match *self {
            Bottom => Bottom,
            Zero => Zero,
            ConstI(c) => abs_from_i128(c.wrapping_neg()),
            ConstU(c) => abs_from_u128(c.wrapping_neg()),
            Pos => Neg,
            Neg => Pos,
            NonNeg => NonPos,
            NonPos => NonNeg,
            Top => Top,
        }
    }

    /// subtraction: a − b = a + (−b)
    pub fn sub(&self, other: &AbsValue) -> AbsValue {
        let neg = other.neg();
        self.add(&neg)
    }

    pub fn mul(&self, other: &AbsValue) -> AbsValue {
        use AbsValue::*;
        match (*self, *other) {
            (Bottom, _) | (_, Bottom) => Bottom,
            (Top, _) | (_, Top) => Top,
            // --- zero ---
            (Zero, _) | (_, Zero) => Zero,
            // --- signed ---
            (ConstI(c1), ConstI(c2)) => abs_from_i128(c1.wrapping_mul(c2)),
            // --- unsigned ---
            (ConstU(c1), ConstU(c2)) => abs_from_u128(c1.wrapping_mul(c2)),
            // -- sign-based rules ---
            (Pos, Pos) | (Neg, Neg) => Pos,
            (ConstI(c), Pos) | (Pos, ConstI(c)) if c > 0 => Pos,
            (ConstI(c), Neg) | (Neg, ConstI(c)) if c < 0 => Pos,
            (ConstU(_), Pos) | (Pos, ConstU(_)) => Pos,
            (Pos, Neg) | (Neg, Pos) => Neg,
            (ConstI(c), Pos) | (Pos, ConstI(c)) if c < 0 => Neg,
            (ConstI(c), Neg) | (Neg, ConstI(c)) if c > 0 => Neg,
            (ConstU(_), Neg) | (Neg, ConstU(_)) => Neg,
            (NonNeg, NonNeg) | (NonPos, NonPos) => NonNeg,
            (Pos, NonNeg) | (NonNeg, Pos) => NonNeg,
            (Neg, NonPos) | (NonPos, Neg) => NonNeg,
            (ConstU(_), NonNeg) | (NonNeg, ConstU(_)) => NonNeg,
            (ConstI(c), NonNeg) | (NonNeg, ConstI(c)) if c > 0 => NonNeg,
            (ConstI(c), NonPos) | (NonPos, ConstI(c)) if c < 0 => NonNeg,
            (NonNeg, NonPos) | (NonPos, NonNeg) => NonPos,
            (Pos, NonPos) | (NonPos, Pos) => NonPos,
            (Neg, NonNeg) | (NonNeg, Neg) => NonPos,
            (ConstU(_), NonPos) | (NonPos, ConstU(_)) => NonPos,
            (ConstI(c), NonNeg) | (NonNeg, ConstI(c)) if c < 0 => NonPos,
            (ConstI(c), NonPos) | (NonPos, ConstI(c)) if c > 0 => NonPos,
            _ => Top,
        }
    }

    /// division truncated toward zero.
    pub fn div(&self, other: &AbsValue) -> AbsValue {
        use AbsValue::*;
        match (*self, *other) {
            (Bottom, _) | (_, Bottom) => Bottom,
            (_, Zero) | (Top, _) | (_, Top) => Top,
            (Zero, _) => Zero,
            // --- signed ---
            (ConstI(c1), ConstI(c2)) => abs_from_i128(c1.wrapping_div(c2)),
            // --- unsigned ---
            (ConstU(c1), ConstU(c2)) => abs_from_u128(c1.wrapping_div(c2)),
            // -- sign-based rules ---
            (Pos, Pos) | (Neg, Neg) => NonNeg,
            (NonNeg, NonNeg) | (NonPos, NonPos) => NonNeg,
            (Pos, NonNeg) | (NonNeg, Pos) => NonNeg,
            (Neg, NonPos) | (NonPos, Neg) => NonNeg,
            (ConstI(c), Pos) | (ConstI(c), NonNeg) if c > 0 => NonNeg,
            (ConstI(c), Neg) | (ConstI(c), NonPos) if c < 0 => NonNeg,
            (Pos, ConstI(c)) if c > 0 => NonNeg,
            (Neg, ConstI(c)) if c < 0 => NonNeg,
            (NonNeg, ConstI(c)) if c > 0 => NonNeg,
            (NonPos, ConstI(c)) if c < 0 => NonNeg,
            (ConstU(_), Pos) | (ConstU(_), NonNeg) => NonNeg,
            (Pos, ConstU(_)) | (NonNeg, ConstU(_)) => NonNeg,
            (Pos, Neg) | (Neg, Pos) => NonPos,
            (NonNeg, NonPos) | (NonPos, NonNeg) => NonPos,
            (Pos, NonPos) | (NonPos, Pos) => NonPos,
            (Neg, NonNeg) | (NonNeg, Neg) => NonPos,
            (ConstI(c), Neg) | (ConstI(c), NonPos) if c > 0 => NonPos,
            (ConstI(c), Pos) | (ConstI(c), NonNeg) if c < 0 => NonPos,
            (Pos, ConstI(c)) if c < 0 => NonPos,
            (Neg, ConstI(c)) if c > 0 => NonPos,
            (NonNeg, ConstI(c)) if c < 0 => NonPos,
            (NonPos, ConstI(c)) if c > 0 => NonPos,
            (ConstU(_), Neg) | (ConstU(_), NonPos) => NonPos,
            (Neg, ConstU(_)) | (NonPos, ConstU(_)) => NonPos,
            _ => Top,
        }
    }

    /// sign of result = sign of dividend.
    pub fn rem(&self, other: &AbsValue) -> AbsValue {
        use AbsValue::*;
        match (*self, *other) {
            (Bottom, _) | (_, Bottom) => Bottom,
            (_, Zero) => Top,
            (Top, _) | (_, Top) => Top,
            (Zero, _) => Zero,
            // --- signed ---
            (ConstI(c1), ConstI(c2)) => abs_from_i128(c1.wrapping_rem(c2)),
            // --- unsigned ---
            (ConstU(c1), ConstU(c2)) => abs_from_u128(c1.wrapping_rem(c2)),
            // -- sign-based rules ---
            (Pos, _) | (NonNeg, _) | (ConstU(_), _) => NonNeg,
            (ConstI(c), _) if c > 0 => NonNeg,
            (Neg, _) | (NonPos, _) => NonPos,
            (ConstI(_), _) => NonPos, // c < 0
        }
    }

    /// sign is preserved
    pub fn shr(&self, other: &AbsValue) -> AbsValue {
        use AbsValue::*;
        let shift: Option<u32> = match *other {
            Zero => Some(0),
            ConstI(n) if n >= 0 => Some(n as u32),
            ConstU(n) => Some(n as u32),
            _ => None,
        };
        match *self {
            Bottom => Bottom,
            Top => Top,
            Zero => Zero,
            ConstI(c) => {
                if let Some(s) = shift {
                    abs_from_i128(c.wrapping_shr(s))
                } else if c > 0 {
                    NonNeg
                } else {
                    Neg
                }
            }
            ConstU(c) => {
                if let Some(s) = shift {
                    abs_from_u128(c.wrapping_shr(s))
                } else {
                    NonNeg
                }
            }
            Pos | NonNeg => NonNeg,
            Neg => Neg,
            NonPos => NonPos,
        }
    }

    pub fn shl(&self, other: &AbsValue) -> AbsValue {
        use AbsValue::*;
        let shift: Option<u32> = match *other {
            Zero => Some(0),
            ConstI(n) if n >= 0 => Some(n as u32),
            ConstU(n) => Some(n as u32),
            _ => None,
        };
        match *self {
            Bottom => Bottom,
            Top => Top,
            Zero => Zero,
            ConstI(c) => {
                if let Some(s) = shift {
                    abs_from_i128(c.wrapping_shl(s))
                } else {
                    Top
                }
            }
            ConstU(c) => {
                if let Some(s) = shift {
                    abs_from_u128(c.wrapping_shl(s))
                } else {
                    NonNeg
                }
            }
            // overflow can change the sign so we conservatively return Top
            v => {
                if shift == Some(0) {
                    v
                } else {
                    Top
                }
            }
        }
    }
}

/// abstract state for functions
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SignState(pub IndexVec<Local, AbsValue>);

impl JoinSemiLattice for SignState {
    fn join(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for (a, b) in self.0.iter_mut().zip(&other.0) {
            changed |= a.join(b);
        }
        changed
    }
}

impl<C> DebugWithContext<C> for SignState {
    fn fmt_with(&self, _ctxt: &C, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

/// constrain an abstract value using a type-based lower bound.
fn constrain_by_bound(v: AbsValue, bound: AbsValue) -> AbsValue {
    if bound == AbsValue::NonNeg {
        match v {
            AbsValue::Top | AbsValue::NonPos | AbsValue::Neg => AbsValue::NonNeg,
            AbsValue::ConstI(c) if c < 0 => AbsValue::NonNeg,
            other => other,
        }
    } else {
        v
    }
}

/// forward MIR dataflow analysis that tracks the abstract sign of locals
pub struct Signedness<'a, 'tcx> {
    pub tcx: TyCtxt<'tcx>,
    /// declared type for each local
    pub local_tys: IndexVec<Local, ty::Ty<'tcx>>,
    /// locals whose address is taken via MIR references/raw pointers
    pub addr_takens: &'a FxHashSet<Local>,
}

impl<'tcx> Analysis<'tcx> for Signedness<'_, 'tcx> {
    type Direction = Forward;
    type Domain = SignState;

    const NAME: &'static str = "signedness";

    fn bottom_value(&self, body: &Body<'tcx>) -> Self::Domain {
        SignState(IndexVec::from_elem(AbsValue::Bottom, &body.local_decls))
    }

    /// initalize function arguments from their declared type (e.g., unsigned args are NonNeg)
    fn initialize_start_block(&self, body: &Body<'tcx>, state: &mut Self::Domain) {
        for arg in body.args_iter() {
            state.0[arg] = abs_value_for_ty(body.local_decls[arg].ty);
        }
    }

    fn apply_primary_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &mir::Statement<'tcx>,
        _location: Location,
    ) {
        if let mir::StatementKind::Assign(box (place, rvalue)) = &statement.kind {
            let val = eval_rvalue(rvalue, &state.0, self.tcx);
            let bound = abs_value_for_ty(self.local_tys[place.local]);
            let val = constrain_by_bound(val, bound);

            if contains_deref(place) {
                for local in self.addr_takens.iter() {
                    state.0[*local].join(&val);
                }
                return;
            }

            if place.projection.is_empty() {
                state.0[place.local] = val;
            } else {
                state.0[place.local].join(&val);
            }
        }
    }

    fn apply_primary_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir mir::Terminator<'tcx>,
        _location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        if let mir::TerminatorKind::Call { destination, .. } = &terminator.kind {
            let dest_ty = self.local_tys[destination.local];
            let bound = abs_value_for_ty(dest_ty);
            let val = if is_integer_ty(dest_ty) {
                eval_integer_terminator_call(terminator, self.tcx, &state.0)
            } else {
                None
            }
            .map_or_else(
                || constrain_by_bound(AbsValue::Top, bound),
                |v| constrain_by_bound(v, bound),
            );
            state.0[destination.local].join(&val);
        }
        terminator.edges()
    }
}

/// helpers
fn is_unsigned_ty(ty: ty::Ty<'_>) -> bool {
    matches!(ty.kind(), ty::TyKind::Uint(_))
}

fn is_integer_ty(ty: ty::Ty<'_>) -> bool {
    matches!(ty.kind(), ty::TyKind::Int(_) | ty::TyKind::Uint(_))
}

fn abs_value_for_ty(ty: ty::Ty<'_>) -> AbsValue {
    if is_unsigned_ty(ty) {
        AbsValue::NonNeg
    } else if is_integer_ty(ty) {
        AbsValue::Top
    } else {
        AbsValue::Bottom
    }
}

fn collect_addr_takens<'tcx>(body: &Body<'tcx>) -> FxHashSet<Local> {
    let mut locals = FxHashSet::default();

    for statement in body.basic_blocks.iter().flat_map(|bb| bb.statements.iter()) {
        if let StatementKind::Assign(box (_, Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place))) =
            &statement.kind
            && !contains_deref(place)
        {
            locals.insert(place.local);
        }
    }

    locals
}
fn const_int_to_val(int_val: ScalarInt, ty: Ty) -> AbsValue {
    let size = int_val.size();
    let bits = int_val.to_bits(size);
    if is_unsigned_ty(ty) {
        abs_from_u128(bits)
    } else {
        let val = size.sign_extend(bits);
        abs_from_i128(val)
    }
}

fn eval_constant_operand<'tcx>(c: &mir::ConstOperand<'tcx>, tcx: TyCtxt<'tcx>) -> AbsValue {
    if let Some(scalar) = c.const_.try_to_scalar()
        && let Ok(int_val) = scalar.try_to_scalar_int()
    {
        let ty = c.const_.ty();
        const_int_to_val(int_val, ty)
    } else if let mir::Const::Unevaluated(unevaluated, ty) = &c.const_
        && unevaluated.promoted.is_none()
        && let Ok(v) = tcx.const_eval_poly(unevaluated.def)
        && let mir::ConstValue::Scalar(scalar) = v
        && let Ok(int_val) = scalar.try_to_scalar_int()
    {
        const_int_to_val(int_val, *ty)
    } else {
        AbsValue::Top
    }
}

/// cast abstract value to an unsigned target type.
fn cast_to_unsigned(v: AbsValue) -> AbsValue {
    use AbsValue::*;
    match v {
        Bottom => Bottom,
        Zero => Zero,
        // non-negative signed constant: value is the same as unsigned
        ConstI(c) if c >= 0 => abs_from_u128(c as u128),
        // negative signed constant: wraps to a large unsigned value whose
        // exact magnitude depends on the concrete bit-width, so lose exactness
        ConstI(_) => NonNeg,
        ConstU(c) => ConstU(c),
        // sign-only values: unsigned target is always non-negative
        _ => NonNeg,
    }
}

/// cast abstract value to a signed target type.
fn cast_to_signed(v: AbsValue) -> AbsValue {
    use AbsValue::*;
    match v {
        Bottom => Bottom,
        Zero => Zero,
        ConstI(c) => ConstI(c),
        // unsigned constant that fits in signed i128: preserve as ConstI
        ConstU(c) if c <= i128::MAX as u128 => abs_from_i128(c as i128),
        // too large: sign after truncation is bit-width–dependent
        ConstU(_) => Top,
        // sign-only values: preserve existing sign information
        other => other,
    }
}

fn eval_operand<'tcx>(
    op: &Operand<'tcx>,
    state: &IndexVec<Local, AbsValue>,
    tcx: TyCtxt<'tcx>,
) -> AbsValue {
    match op {
        Operand::Copy(place) | Operand::Move(place) => {
            if contains_deref(place) {
                AbsValue::Top
            } else {
                state[place.local]
            }
        }
        Operand::Constant(c) => eval_constant_operand(c, tcx),
    }
}

fn eval_rvalue<'tcx>(
    rvalue: &Rvalue<'tcx>,
    state: &IndexVec<Local, AbsValue>,
    tcx: TyCtxt<'tcx>,
) -> AbsValue {
    use AbsValue::*;
    match rvalue {
        Rvalue::Use(op) => eval_operand(op, state, tcx),
        Rvalue::UnaryOp(mir::UnOp::Neg, op) => eval_operand(op, state, tcx).neg(),
        Rvalue::BinaryOp(op, box (lhs, rhs)) => {
            let l = eval_operand(lhs, state, tcx);
            let r = eval_operand(rhs, state, tcx);
            match op {
                mir::BinOp::Add => l.add(&r),
                mir::BinOp::Sub => l.sub(&r),
                mir::BinOp::Mul => l.mul(&r),
                mir::BinOp::Div => l.div(&r),
                mir::BinOp::Rem => l.rem(&r),
                mir::BinOp::Shr => l.shr(&r),
                mir::BinOp::Shl => l.shl(&r),
                // comparisons produce bool (0 or 1), so always NonNeg
                mir::BinOp::Eq
                | mir::BinOp::Ne
                | mir::BinOp::Lt
                | mir::BinOp::Le
                | mir::BinOp::Gt
                | mir::BinOp::Ge => NonNeg,
                _ => Top,
            }
        }
        // preserve concrete constants through casts when possible
        Rvalue::Cast(_, op, ty) => {
            let v = eval_operand(op, state, tcx);
            if is_unsigned_ty(*ty) {
                cast_to_unsigned(v)
            } else {
                cast_to_signed(v)
            }
        }
        Rvalue::Aggregate(_, ops) => {
            let mut res = Bottom;
            for op in ops {
                res.join(&eval_operand(op, state, tcx));
            }
            res
        }
        _ => Top,
    }
}

fn eval_integer_terminator_call<'tcx>(
    terminator: &mir::Terminator<'tcx>,
    tcx: TyCtxt<'tcx>,
    state: &IndexVec<Local, AbsValue>,
) -> Option<AbsValue> {
    let mir::TerminatorKind::Call { func, args, .. } = &terminator.kind else {
        return None;
    };
    let Operand::Constant(box constant) = func else {
        return None;
    };

    let ty = constant.const_.ty();
    let ty::TyKind::FnDef(def_id, _) = ty.kind() else {
        return None;
    };
    let name = tcx
        .def_path(*def_id)
        .data
        .last()
        .map(|d| d.data.to_string())
        .unwrap_or_default();

    let unary = |f: fn(&AbsValue) -> AbsValue| {
        args.first().map(|a| {
            let v = eval_operand(&a.node, state, tcx);
            f(&v)
        })
    };
    let binary = |f: fn(&AbsValue, &AbsValue) -> AbsValue| {
        if args.len() < 2 {
            return None;
        }
        let l = eval_operand(&args[0].node, state, tcx);
        let r = eval_operand(&args[1].node, state, tcx);
        Some(f(&l, &r))
    };

    match name.as_str() {
        "wrapping_add" | "saturating_add" => binary(AbsValue::add),
        "wrapping_sub" | "saturating_sub" => binary(AbsValue::sub),
        "wrapping_mul" | "saturating_mul" => binary(AbsValue::mul),
        "wrapping_div" | "saturating_div" => binary(AbsValue::div),
        "wrapping_neg" | "saturating_neg" => unary(AbsValue::neg),
        "wrapping_rem" => binary(AbsValue::rem),
        "wrapping_shl" => binary(AbsValue::shl),
        "wrapping_shr" => binary(AbsValue::shr),
        _ => None,
    }
}

// graph structure used for propagation
type Node = (LocalDefId, Local);
type SignGraph = FxHashMap<Node, FxHashSet<Node>>;

// collect flow-edges of offset inforamtion in program
#[allow(dead_code)]
struct Collector<'mir, 'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    cursor: &'a mut ResultsCursor<'mir, 'tcx, Signedness<'a, 'tcx>>,
    graph: &'a mut FxHashMap<Node, FxHashSet<Node>>,
    tainted: &'a mut FxHashSet<Node>,
    addr_takens: &'a FxHashSet<Local>,
}

fn contains_deref(place: &Place<'_>) -> bool {
    place
        .projection
        .iter()
        .any(|elem| matches!(elem, mir::ProjectionElem::Deref))
}

fn is_pointer_offset_like_call(name: &str) -> bool {
    if !name.contains("ptr::") {
        return false;
    }
    matches!(
        name.rsplit("::").next(),
        Some("offset" | "wrapping_offset" | "byte_offset" | "wrapping_byte_offset")
    )
}

impl<'mir, 'tcx, 'a> MVisitor<'tcx> for Collector<'mir, 'tcx, 'a> {
    fn visit_statement(&mut self, stmt: &mir::Statement<'tcx>, _location: Location) {
        if let StatementKind::Assign(box (place, rvalue)) = &stmt.kind {
            if contains_deref(place) {
                match rvalue {
                    Rvalue::Use(Operand::Copy(dst) | Operand::Move(dst))
                    | Rvalue::Cast(_, Operand::Copy(dst) | Operand::Move(dst), _)
                        if !contains_deref(dst) =>
                    {
                        let rhs = (self.def_id, dst.local);

                        for local in self.addr_takens.iter() {
                            let lhs = (self.def_id, *local);
                            self.graph.entry(lhs).or_default().insert(rhs);
                        }
                    }
                    _ => {}
                }
                return;
            }

            match rvalue {
                Rvalue::Use(Operand::Copy(dst) | Operand::Move(dst))
                | Rvalue::Cast(_, Operand::Copy(dst) | Operand::Move(dst), _)
                    if !contains_deref(dst) =>
                {
                    // when p = q (or p = q as T), cursor requirement on p implies
                    // cursor requirement on q, so we add p -> q
                    let lhs = (self.def_id, place.local);
                    let rhs = (self.def_id, dst.local);
                    self.graph.entry(lhs).or_default().insert(rhs);
                }
                _ => {}
            }
        }
    }

    fn visit_terminator(&mut self, terminator: &mir::Terminator<'tcx>, location: Location) {
        if let TerminatorKind::Call { func, args, .. } = &terminator.kind
            && let Operand::Constant(box constant) = func
        {
            let ty = constant.const_.ty();
            let ty::TyKind::FnDef(def_id, _) = ty.kind() else { unreachable!() };
            let name = self.tcx.def_path(*def_id).to_string_no_crate_verbose();
            if is_pointer_offset_like_call(&name) {
                if let Operand::Copy(place) | Operand::Move(place) = &args[0].node {
                    // check if the offset argument is negative.
                    // If so, mark the source as tainted
                    if let Some(offset_arg) = args.get(1) {
                        self.cursor.seek_before_primary_effect(location);
                        let state = self.cursor.get();
                        let offset_val = eval_operand(&offset_arg.node, &state.0, self.tcx);
                        if offset_val.needs_cursor() {
                            self.tainted.insert((self.def_id, place.local));
                        }
                    }
                }
            } else {
                // collect flow edges for offset arguments
                // if f(a) is called on f(p), add p -> a
                for (idx, arg) in args.iter().enumerate() {
                    if let Operand::Copy(place) | Operand::Move(place) = &arg.node
                        && let Some(local_def_id) = def_id.as_local()
                    {
                        let caller_arg = (self.def_id, place.local);
                        let param = Local::from_usize(idx + 1); // skip return
                        let callee_param = (local_def_id, param);
                        // if callee param needs cursor, corresponding caller arg also needs it
                        self.graph
                            .entry(callee_param)
                            .or_default()
                            .insert(caller_arg);
                    }
                }
            };
        }
    }
}

/// main entry point for offset sign analysis
pub fn offset_sign_analysis(rust_program: &RustProgram<'_>) -> OffsetSignResult {
    use rustc_mir_dataflow::Analysis as _;

    let mut graph: SignGraph = FxHashMap::default();
    let mut tainted: FxHashSet<Node> = FxHashSet::default();
    let mut access_signs: FxHashMap<LocalDefId, DenseBitSet<Local>> = FxHashMap::default();
    let tcx = rust_program.tcx;

    // phase 1: analyze signedness and collect taints
    for &def_id in &rust_program.functions {
        let body = tcx.mir_drops_elaborated_and_const_checked(def_id).borrow();

        for (local, _) in body.local_decls.iter_enumerated() {
            graph.insert((def_id, local), FxHashSet::default());
        }

        let local_tys = body.local_decls.iter().map(|d| d.ty).collect();
        let addr_takens = collect_addr_takens(&body);
        let mut cursor = Signedness {
            tcx,
            local_tys,
            addr_takens: &addr_takens,
        }
        .iterate_to_fixpoint(tcx, &body, None)
        .into_results_cursor(&body);

        let mut collector = Collector {
            tcx,
            def_id,
            cursor: &mut cursor,
            graph: &mut graph,
            tainted: &mut tainted,
            addr_takens: &addr_takens,
        };
        collector.visit_body(&body);
    }

    // phase 2: propagate taint through graph using SCC-based worklist.
    let sccs = graph::sccs_copied::<_, false>(&graph);

    // seed the worklist with every SCC that contains an initially-tainted node.
    let mut worklist: VecDeque<graph::SccId> = tainted
        .iter()
        .filter_map(|node| sccs.indices.get(node).copied())
        .collect();

    // mark tainted SCCs and propagate to successor SCCs.
    let mut tainted_sccs: FxHashSet<graph::SccId> = FxHashSet::default();
    while let Some(scc_id) = worklist.pop_front() {
        if !tainted_sccs.insert(scc_id) {
            continue;
        }
        worklist.extend(sccs.successors(scc_id));
    }

    // collect results for all nodes in tainted SCCs
    let cursor_locals = tainted_sccs
        .iter()
        .flat_map(|&scc_id| &sccs.scc_elems[scc_id])
        .collect::<FxHashSet<_>>();

    // post-process results to map v
    for &def_id in &rust_program.functions {
        let body = tcx.mir_drops_elaborated_and_const_checked(def_id).borrow();
        let mut access_sign: DenseBitSet<Local> = DenseBitSet::new_empty(body.local_decls.len());

        for (local, _) in body.local_decls.iter_enumerated().skip(1) {
            if cursor_locals.contains(&(def_id, local)) {
                access_sign.insert(local);
            }
        }
        access_signs.insert(def_id, access_sign);
    }

    OffsetSignResult { access_signs }
}
