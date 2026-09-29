//! **wave-6l — the extent prover** (design record
//! `agents/plan/2026-09-28-extent-analysis-design.md`, approved as the build
//! plan by R645-5; steps 1–3 started by R666-2).
//!
//! For a pointer parameter `p` of `f` and an integer parameter `n` licensed
//! as its length, the claim is **(E)**: every access `f` makes through `p`, or
//! through a pointer derived from `p`, touches only elements `[0, n)` of `p`.
//! Too short a proof is a panic where C read on; too long a licence is
//! §77's out-of-scope slice-length class. So the prover owes exactly
//! reads ⊆ `[0, n)`.
//!
//! Step 1 (this file): the MIR domain and the access check.
//!
//! **The domain.** A forward dataflow over MIR holds difference-bound facts
//! (`x − y ≤ c`) between the constant zero, integer locals, and the offset
//! (in elements) of each pointer local derived from `p`. Facts come from:
//! - assignments (copies, constants, `± c`, value-preserving casts);
//! - dominating branch conditions, which hold on the edge that takes them;
//! - loop heads, which widen to the facts that survive every back edge.
//!
//! **What is lost:** a local whose address is taken, a truncating cast, a
//! sign change without a proven lower bound, and every write to the
//! companion, which is refused outright since `n` must be the caller's
//! argument.
//!
//! **The access check.** `*q`, with `q = p + off`, is proven when the facts
//! entail `0 ≤ off` and `off + 1 ≤ n`. Everything else is refused, and the
//! first refusing access is named. A derived pointer handed to a callee is
//! refused until step 3's summaries; one cast to another pointee is refused
//! until step 2's C7.
//!
//! **Premises** (the design record's §1 and §2):
//! - the input is UB-free (§28);
//! - a `usize` offset cast to `isize` keeps its value, because an index
//!   below a real length is below `isize::MAX`;
//! - `+ c` on an index does not wrap, because C's signed overflow is UB and
//!   an unsigned index that wraps cannot be below the length it is compared
//!   with.

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    mir::{
        BasicBlock, BinOp, Body, CastKind, Local, Operand, Place, ProjectionElem, Rvalue,
        StatementKind, TerminatorKind,
    },
    ty::{Ty, TyCtxt, TyKind},
};

/// Why a proof failed: the first refusing access or operation, and where.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Refusal {
    pub reason: String,
    pub span: rustc_span::Span,
}

/// The largest body the step-1 domain takes (tracked locals); a larger one
/// is refused, typed, not analysed slowly.
const MAX_TRACKED: usize = 600;

/// **(E)** for parameter `pointer` of `function` against the length
/// parameter `length` (both indices into the function's parameters).
pub(crate) fn prove_parameter_extent(
    tcx: TyCtxt<'_>,
    function: LocalDefId,
    pointer: usize,
    length: usize,
) -> Result<(), Refusal> {
    let refuse = |reason: &str| Refusal {
        reason: reason.to_owned(),
        span: tcx.def_span(function),
    };
    if !tcx.hir_body_owners().any(|owner| owner == function)
        || !tcx.is_mir_available(function.to_def_id())
    {
        return Err(refuse("no-body"));
    }
    let body = tcx
        .mir_drops_elaborated_and_const_checked(function)
        .borrow();
    if pointer.max(length) >= body.arg_count {
        return Err(refuse("no-such-parameter"));
    }
    let p = Local::from_usize(pointer + 1);
    let n = Local::from_usize(length + 1);
    let Some(element) = pointee(body.local_decls[p].ty) else {
        return Err(refuse("pointer-not-a-pointer"));
    };
    if !body.local_decls[n].ty.is_integral() {
        return Err(refuse("length-not-an-integer"));
    }
    let analysis = Analysis::new(tcx, &body, p, n, element);
    if analysis.address_taken.contains(&n) || analysis.assigned.contains(&n) {
        return Err(refuse("companion-written"));
    }
    if analysis.address_taken.contains(&p) {
        return Err(refuse("pointer-address-taken"));
    }
    if analysis.vars.len() > MAX_TRACKED {
        return Err(refuse("too-many-locals"));
    }
    analysis.run()
}

/// The pointee of a raw pointer or reference type.
fn pointee(ty: Ty<'_>) -> Option<Ty<'_>> {
    match ty.kind() {
        TyKind::RawPtr(pointee, _) | TyKind::Ref(_, pointee, _) => Some(*pointee),
        _ => None,
    }
}

/// The bit width and signedness of an integer type (`isize` / `usize` as 64).
fn int_shape(ty: Ty<'_>) -> Option<(u64, bool)> {
    match ty.kind() {
        TyKind::Int(int) => Some((int.bit_width().unwrap_or(64), true)),
        TyKind::Uint(uint) => Some((uint.bit_width().unwrap_or(64), false)),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// The difference-bound matrix.
// ---------------------------------------------------------------------------

/// +∞ in the matrix; bounds are kept far from overflow.
const INF: i64 = i64::MAX / 4;

/// A (closed, outside widening) difference-bound matrix: `m[i * n + j]`
/// bounds `x_i − x_j`. Variable 0 is the constant zero.
#[derive(Clone, PartialEq, Eq, Debug)]
struct Dbm {
    n: usize,
    m: Vec<i64>,
}

impl Dbm {
    fn top(n: usize) -> Self {
        let mut m = vec![INF; n * n];
        for i in 0..n {
            m[i * n + i] = 0;
        }
        Dbm { n, m }
    }

    fn get(&self, i: usize, j: usize) -> i64 {
        self.m[i * self.n + j]
    }

    fn sum(a: i64, b: i64) -> i64 {
        if a >= INF || b >= INF {
            INF
        } else {
            (a + b).clamp(-INF, INF)
        }
    }

    /// Adds `x_i − x_j ≤ c` and restores closure (O(n²)).
    fn constrain(&mut self, i: usize, j: usize, c: i64) {
        if c >= self.get(i, j) {
            return;
        }
        let n = self.n;
        let into_i: Vec<i64> = (0..n).map(|k| self.get(k, i)).collect();
        let out_of_j: Vec<i64> = (0..n).map(|l| self.get(j, l)).collect();
        for k in 0..n {
            if into_i[k] >= INF {
                continue;
            }
            let through = Self::sum(into_i[k], c);
            for l in 0..n {
                let bound = Self::sum(through, out_of_j[l]);
                if bound < self.m[k * n + l] {
                    self.m[k * n + l] = bound;
                }
            }
        }
    }

    /// Drops every fact on `x` (a closed matrix stays closed).
    fn forget(&mut self, x: usize) {
        let n = self.n;
        for k in 0..n {
            if k != x {
                self.m[x * n + k] = INF;
                self.m[k * n + x] = INF;
            }
        }
    }

    /// `x := y + c`.
    fn assign(&mut self, x: usize, y: usize, c: i64) {
        if x == y {
            // A shift: every bound on x moves by c.
            let n = self.n;
            for k in 0..n {
                if k == x {
                    continue;
                }
                let out = self.m[x * n + k];
                if out < INF {
                    self.m[x * n + k] = (out + c).clamp(-INF, INF);
                }
                let into = self.m[k * n + x];
                if into < INF {
                    self.m[k * n + x] = (into - c).clamp(-INF, INF);
                }
            }
            return;
        }
        self.forget(x);
        self.constrain(x, y, c);
        self.constrain(y, x, -c);
    }

    /// The exact value of `x`, when the facts pin it.
    fn exact(&self, x: usize) -> Option<i64> {
        let (upper, lower) = (self.get(x, 0), self.get(0, x));
        (upper < INF && upper == -lower).then_some(upper)
    }

    fn bottom(&self) -> bool {
        (0..self.n).any(|i| self.get(i, i) < 0)
    }

    fn join(&self, other: &Dbm) -> Dbm {
        Dbm {
            n: self.n,
            m: self
                .m
                .iter()
                .zip(&other.m)
                .map(|(a, b)| *a.max(b))
                .collect(),
        }
    }

    /// The standard widening: a bound that grew is dropped.
    fn widen(&self, newer: &Dbm) -> Dbm {
        Dbm {
            n: self.n,
            m: self
                .m
                .iter()
                .zip(&newer.m)
                .map(|(old, new)| if new > old { INF } else { *old })
                .collect(),
        }
    }

    fn leq(&self, other: &Dbm) -> bool {
        self.m.iter().zip(&other.m).all(|(a, b)| a <= b)
    }
}

// ---------------------------------------------------------------------------
// The abstract state.
// ---------------------------------------------------------------------------

/// What a pointer local holds with respect to `p`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Derivation {
    /// Not derived from `p` (another object, or nothing).
    Other,
    /// `p + off`, `off` the local's own variable, at `p`'s element width.
    Derived,
    /// Maybe `p`, or `p` under another width: any access through it refuses.
    Tainted,
}

/// A value a local may stand for: a matrix term plus a constant.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Term {
    Var(usize),
    Const(i64),
}

/// A comparison a boolean local holds.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Cond {
    op: BinOp,
    left: Term,
    right: Term,
}

#[derive(Clone, PartialEq, Eq, Debug)]
struct State {
    dbm: Dbm,
    derivation: FxHashMap<Local, Derivation>,
    conds: FxHashMap<Local, Cond>,
    /// `t = AddWithOverflow(y, c)`: field 0 of `t` is `y + c` (an
    /// overflow-checked build).
    checked: FxHashMap<Local, (Term, i64)>,
}

impl State {
    fn derivation(&self, local: Local) -> Derivation {
        self.derivation
            .get(&local)
            .copied()
            .unwrap_or(Derivation::Other)
    }

    fn join(&self, other: &State, widen: bool) -> State {
        let dbm = if widen {
            self.dbm.widen(&self.dbm.join(&other.dbm))
        } else {
            self.dbm.join(&other.dbm)
        };
        let mut derivation = FxHashMap::default();
        for local in self.derivation.keys().chain(other.derivation.keys()) {
            let (a, b) = (self.derivation(*local), other.derivation(*local));
            let joined = if a == b { a } else { Derivation::Tainted };
            if joined != Derivation::Other {
                derivation.insert(*local, joined);
            }
        }
        let conds = self
            .conds
            .iter()
            .filter(|(local, cond)| other.conds.get(local) == Some(cond))
            .map(|(local, cond)| (*local, *cond))
            .collect();
        let checked = self
            .checked
            .iter()
            .filter(|(local, value)| other.checked.get(local) == Some(value))
            .map(|(local, value)| (*local, *value))
            .collect();
        State {
            dbm,
            derivation,
            conds,
            checked,
        }
    }

    /// `self ⊑ other`: every fact `other` keeps, `self` has.
    fn leq(&self, other: &State) -> bool {
        self.dbm.leq(&other.dbm)
            && self
                .derivation
                .keys()
                .chain(other.derivation.keys())
                .all(|local| {
                    let (a, b) = (self.derivation(*local), other.derivation(*local));
                    a == b || b == Derivation::Tainted
                })
            && other
                .conds
                .iter()
                .all(|(local, cond)| self.conds.get(local) == Some(cond))
            && other
                .checked
                .iter()
                .all(|(local, value)| self.checked.get(local) == Some(value))
    }
}

// ---------------------------------------------------------------------------
// The analysis.
// ---------------------------------------------------------------------------

struct Analysis<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    p: Local,
    n: Local,
    element: Ty<'tcx>,
    /// Tracked locals (integers and pointers, not address-taken) and their
    /// matrix variable; variable 0 is zero.
    vars: FxHashMap<Local, usize>,
    /// The local of each variable (index `var − 1`).
    var_locals: Vec<Local>,
    address_taken: FxHashSet<Local>,
    assigned: FxHashSet<Local>,
}

impl<'a, 'tcx> Analysis<'a, 'tcx> {
    fn new(tcx: TyCtxt<'tcx>, body: &'a Body<'tcx>, p: Local, n: Local, element: Ty<'tcx>) -> Self {
        let mut address_taken = FxHashSet::default();
        let mut assigned = FxHashSet::default();
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                if let StatementKind::Assign(box (place, rvalue)) = &statement.kind {
                    assigned.insert(place.local);
                    if let Rvalue::Ref(_, _, borrowed) | Rvalue::RawPtr(_, borrowed) = rvalue
                        && !borrowed
                            .projection
                            .iter()
                            .any(|elem| matches!(elem, ProjectionElem::Deref))
                    {
                        address_taken.insert(borrowed.local);
                    }
                }
            }
            if let TerminatorKind::Call { destination, .. } = &data.terminator().kind {
                assigned.insert(destination.local);
            }
        }
        let mut vars = FxHashMap::default();
        let mut var_locals = Vec::new();
        for (local, decl) in body.local_decls.iter_enumerated() {
            if address_taken.contains(&local) {
                continue;
            }
            if decl.ty.is_integral() || pointee(decl.ty).is_some() {
                let next = vars.len() + 1;
                vars.insert(local, next);
                var_locals.push(local);
            }
        }
        Analysis {
            tcx,
            body,
            p,
            n,
            element,
            vars,
            var_locals,
            address_taken,
            assigned,
        }
    }

    fn var(&self, local: Local) -> Option<usize> {
        self.vars.get(&local).copied()
    }

    fn unsigned(&self, local: Local) -> bool {
        matches!(self.body.local_decls[local].ty.kind(), TyKind::Uint(_))
    }

    fn initial(&self) -> State {
        let mut dbm = Dbm::top(self.vars.len() + 1);
        let p = self.var(self.p).expect("p is tracked");
        dbm.constrain(p, 0, 0);
        dbm.constrain(0, p, 0);
        for (local, var) in &self.vars {
            if self.unsigned(*local) {
                dbm.constrain(0, *var, 0);
            }
        }
        let mut derivation = FxHashMap::default();
        derivation.insert(self.p, Derivation::Derived);
        State {
            dbm,
            derivation,
            conds: FxHashMap::default(),
            checked: FxHashMap::default(),
        }
    }

    /// The fixpoint, then one checking pass over the converged states.
    fn run(&self) -> Result<(), Refusal> {
        let blocks = self.body.basic_blocks.len();
        let mut entry: Vec<Option<State>> = vec![None; blocks];
        let mut visits = vec![0usize; blocks];
        entry[0] = Some(self.initial());
        let mut work = vec![BasicBlock::from_u32(0)];
        let mut steps = 0usize;
        while let Some(block) = work.pop() {
            steps += 1;
            if steps > 50_000 {
                return Err(Refusal {
                    reason: "fixpoint-budget".to_owned(),
                    span: self.body.span,
                });
            }
            let Some(state) = entry[block.index()].clone() else {
                continue;
            };
            for (target, out) in self.transfer_block(block, state, &mut |_| {}) {
                if out.dbm.bottom() {
                    continue;
                }
                let slot = &mut entry[target.index()];
                let next = match slot {
                    None => out,
                    Some(old) => {
                        if out.leq(old) {
                            continue;
                        }
                        visits[target.index()] += 1;
                        old.join(&out, visits[target.index()] > 2)
                    }
                };
                *slot = Some(next);
                if !work.contains(&target) {
                    work.push(target);
                }
            }
        }
        let mut refusal = None;
        for (index, state) in entry.iter().enumerate() {
            let Some(state) = state.clone() else { continue };
            self.transfer_block(BasicBlock::from_usize(index), state, &mut |r| {
                refusal.get_or_insert(r);
            });
            if refusal.is_some() {
                break;
            }
        }
        refusal.map_or(Ok(()), Err)
    }

    /// One block: the statements, then the terminator's edges with their
    /// conditions. `refuse` receives every refusal met on the way.
    fn transfer_block(
        &self,
        block: BasicBlock,
        mut state: State,
        refuse: &mut dyn FnMut(Refusal),
    ) -> Vec<(BasicBlock, State)> {
        let data = &self.body.basic_blocks[block];
        for statement in &data.statements {
            let span = statement.source_info.span;
            match &statement.kind {
                StatementKind::Assign(box (place, rvalue)) => {
                    self.check_rvalue_accesses(&state, rvalue, span, refuse);
                    self.check_place_access(&state, place, span, refuse);
                    self.assign(&mut state, place, rvalue, span, refuse);
                }
                StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
                    self.kill(&mut state, *local);
                }
                _ => {}
            }
        }
        let terminator = data.terminator();
        let span = terminator.source_info.span;
        match &terminator.kind {
            TerminatorKind::Goto { target } => vec![(*target, state)],
            TerminatorKind::SwitchInt { discr, targets } => {
                self.check_operand_access(&state, discr, span, refuse);
                let cond = operand_local(discr).and_then(|local| state.conds.get(&local).copied());
                let values: Vec<_> = targets.iter().collect();
                let two_way = values.len() == 1 && values[0].0 == 0;
                let mut out = Vec::new();
                for (_, target) in &values {
                    let mut edge = state.clone();
                    if let (Some(cond), true) = (cond, two_way) {
                        self.apply(&mut edge, cond, false);
                    }
                    out.push((*target, edge));
                }
                let mut otherwise = state;
                if let (Some(cond), true) = (cond, two_way) {
                    self.apply(&mut otherwise, cond, true);
                }
                out.push((targets.otherwise(), otherwise));
                out
            }
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => {
                for arg in args.iter() {
                    self.check_operand_access(&state, &arg.node, span, refuse);
                }
                self.check_place_access(&state, destination, span, refuse);
                self.call(&mut state, func, args, destination, span, refuse);
                target.map(|t| vec![(t, state)]).unwrap_or_default()
            }
            TerminatorKind::Assert { cond, target, .. } => {
                self.check_operand_access(&state, cond, span, refuse);
                vec![(*target, state)]
            }
            TerminatorKind::Drop { target, place, .. } => {
                self.check_place_access(&state, place, span, refuse);
                vec![(*target, state)]
            }
            TerminatorKind::FalseEdge { real_target, .. }
            | TerminatorKind::FalseUnwind { real_target, .. } => vec![(*real_target, state)],
            TerminatorKind::InlineAsm { .. } => {
                refuse(Refusal {
                    reason: "inline-asm".to_owned(),
                    span,
                });
                vec![]
            }
            _ => vec![],
        }
    }

    /// Forgets a local entirely: its facts, its derivation, and the
    /// conditions that mention it.
    fn kill(&self, state: &mut State, local: Local) {
        if let Some(var) = self.var(local) {
            state.dbm.forget(var);
            let mentions = |term: Term| matches!(term, Term::Var(v) if v == var);
            state.conds.retain(|held, cond| {
                *held != local && !mentions(cond.left) && !mentions(cond.right)
            });
            state
                .checked
                .retain(|held, (term, _)| *held != local && !mentions(*term));
        } else {
            state.conds.remove(&local);
            state.checked.remove(&local);
        }
        state.derivation.remove(&local);
    }

    /// The value an integer operand has, as a matrix term.
    fn term(&self, state: &State, operand: &Operand<'tcx>) -> Option<Term> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                if let Some(local) = place.as_local() {
                    // A pointer's variable is its offset from `p` only while
                    // it is `Derived` (the relay 066 review's B4).
                    if pointee(self.body.local_decls[local].ty).is_some()
                        && state.derivation(local) != Derivation::Derived
                    {
                        return None;
                    }
                    return self.var(local).map(Term::Var);
                }
                // `move (t.0)` of an overflow-checked step.
                if let [ProjectionElem::Field(field, _)] = place.projection.as_slice()
                    && field.as_u32() == 0
                    && let Some((term, c)) = state.checked.get(&place.local)
                {
                    return match term {
                        Term::Const(k) => Some(Term::Const(k + c)),
                        Term::Var(_) if *c == 0 => Some(*term),
                        // (y + c) needs an offset; the caller of `term`
                        // reads it through `checked_step`.
                        Term::Var(_) => None,
                    };
                }
                None
            }
            Operand::Constant(constant) => {
                let (bits, signed) = int_shape(constant.ty())?;
                let raw = constant
                    .const_
                    .try_eval_bits(self.tcx, rustc_middle::ty::TypingEnv::fully_monomorphized())?;
                let value: i128 = if signed && bits < 128 && (raw >> (bits - 1)) & 1 == 1 {
                    raw as i128 - (1i128 << bits)
                } else {
                    raw as i128
                };
                i64::try_from(value)
                    .ok()
                    .filter(|v| v.abs() < INF / 4)
                    .map(Term::Const)
            }
        }
    }

    /// `move (t.0)` of `t = AddWithOverflow(y, c)`: `y + c`.
    fn checked_step(&self, state: &State, operand: &Operand<'tcx>) -> Option<(Term, i64)> {
        let (Operand::Copy(place) | Operand::Move(place)) = operand else {
            return None;
        };
        match place.projection.as_slice() {
            [ProjectionElem::Field(field, _)] if field.as_u32() == 0 => {
                state.checked.get(&place.local).copied()
            }
            _ => None,
        }
    }

    /// `x := term + c`.
    fn assign_term(&self, state: &mut State, x: usize, term: Term, c: i64) {
        match term {
            Term::Var(y) => state.dbm.assign(x, y, c),
            Term::Const(k) => state.dbm.assign(x, 0, k + c),
        }
    }

    /// Adds a comparison's outcome on the edge that takes it.
    fn apply(&self, state: &mut State, cond: Cond, holds: bool) {
        let var = |term: Term| match term {
            Term::Var(v) => (v, 0),
            Term::Const(k) => (0, k),
        };
        let ((a, ka), (b, kb)) = (var(cond.left), var(cond.right));
        // a + ka  OP  b + kb, i.e. a − b  OP  kb − ka.
        let d = kb - ka;
        let (first, second) = match (cond.op, holds) {
            (BinOp::Lt, true) | (BinOp::Ge, false) => ((a, b, d - 1), None),
            (BinOp::Le, true) | (BinOp::Gt, false) => ((a, b, d), None),
            (BinOp::Gt, true) | (BinOp::Le, false) => ((b, a, -d - 1), None),
            (BinOp::Ge, true) | (BinOp::Lt, false) => ((b, a, -d), None),
            (BinOp::Eq, true) | (BinOp::Ne, false) => ((a, b, d), Some((b, a, -d))),
            _ => return,
        };
        state.dbm.constrain(first.0, first.1, first.2);
        if let Some((i, j, c)) = second {
            state.dbm.constrain(i, j, c);
        }
    }

    fn assign(
        &self,
        state: &mut State,
        place: &Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        span: rustc_span::Span,
        refuse: &mut dyn FnMut(Refusal),
    ) {
        let carries = self.rvalue_carries_derived(state, rvalue);
        // A derived pointer stored anywhere but a plain local, returned, or
        // turned into an integer, escapes the domain.
        if carries && place.as_local().is_none() {
            refuse(Refusal {
                reason: "stored".to_owned(),
                span,
            });
            return;
        }
        if place.as_local().is_none() {
            return;
        }
        let x = place.local;
        if carries && x == Local::from_u32(0) {
            refuse(Refusal {
                reason: "returned".to_owned(),
                span,
            });
        }
        let x_ty = self.body.local_decls[x].ty;
        if carries && pointee(x_ty).is_none() && !matches!(rvalue, Rvalue::BinaryOp(..)) {
            refuse(Refusal {
                reason: "exposed".to_owned(),
                span,
            });
        }
        // The relay 066 review's B2: `&q` of a derived pointer lets any
        // callee or later load read through it.
        if let Rvalue::Ref(_, _, borrowed) | Rvalue::RawPtr(_, borrowed) = rvalue
            && !borrowed
                .projection
                .iter()
                .any(|elem| matches!(elem, ProjectionElem::Deref))
            && state.derivation(borrowed.local) != Derivation::Other
        {
            refuse(Refusal {
                reason: "address-of-a-derived-pointer".to_owned(),
                span,
            });
        }
        let x_var = self.var(x);
        // The new value, computed against the state BEFORE x is overwritten.
        enum New {
            Term(Term, i64),
            Pointer(Local, Derivation),
            Cond(Cond),
            Checked(Term, i64),
            Unknown,
        }
        let new = match rvalue {
            Rvalue::Use(operand) | Rvalue::Cast(CastKind::PtrToPtr, operand, _)
                if pointee(x_ty).is_some() =>
            {
                match operand_local(operand) {
                    Some(src) => match state.derivation(src) {
                        Derivation::Other => New::Unknown,
                        d => {
                            let same = pointee(x_ty).is_some_and(|pointee| pointee == self.element);
                            New::Pointer(src, if same { d } else { Derivation::Tainted })
                        }
                    },
                    None => New::Unknown,
                }
            }
            Rvalue::Use(operand) => {
                match (self.term(state, operand), self.checked_step(state, operand)) {
                    (Some(term), _) => New::Term(term, 0),
                    (None, Some((term, c))) => New::Term(term, c),
                    _ => New::Unknown,
                }
            }
            Rvalue::CopyForDeref(src) if src.as_local().is_some() && pointee(x_ty).is_some() => {
                match state.derivation(src.local) {
                    Derivation::Other => New::Unknown,
                    d => New::Pointer(src.local, d),
                }
            }
            Rvalue::Ref(_, _, borrowed) | Rvalue::RawPtr(_, borrowed)
                if matches!(borrowed.projection.first(), Some(ProjectionElem::Deref)) =>
            {
                // `&*q` (and `&(*q).f`): a view of q's element.
                match state.derivation(borrowed.local) {
                    Derivation::Other => New::Unknown,
                    Derivation::Derived if borrowed.projection.len() == 1 => {
                        New::Pointer(borrowed.local, Derivation::Derived)
                    }
                    _ => New::Pointer(borrowed.local, Derivation::Tainted),
                }
            }
            Rvalue::Cast(CastKind::IntToInt, operand, target) => {
                let from = int_shape(operand.ty(&self.body.local_decls, self.tcx));
                match (self.term(state, operand), from, int_shape(*target)) {
                    (Some(term), Some(from), Some(to))
                        if self.value_preserving(state, term, from, to) =>
                    {
                        New::Term(term, 0)
                    }
                    _ => New::Unknown,
                }
            }
            Rvalue::BinaryOp(op, box (left, right)) => {
                let (l, r) = (self.term(state, left), self.term(state, right));
                match op {
                    BinOp::Add | BinOp::AddUnchecked => match (l, r) {
                        (Some(Term::Var(v)), Some(Term::Const(c)))
                        | (Some(Term::Const(c)), Some(Term::Var(v))) => New::Term(Term::Var(v), c),
                        (Some(Term::Const(a)), Some(Term::Const(b))) => {
                            New::Term(Term::Const(a + b), 0)
                        }
                        _ => New::Unknown,
                    },
                    BinOp::Sub | BinOp::SubUnchecked => match (l, r) {
                        (Some(Term::Var(v)), Some(Term::Const(c))) => New::Term(Term::Var(v), -c),
                        (Some(Term::Const(a)), Some(Term::Const(b))) => {
                            New::Term(Term::Const(a - b), 0)
                        }
                        _ => New::Unknown,
                    },
                    BinOp::AddWithOverflow => match (l, r) {
                        (Some(term), Some(Term::Const(c))) | (Some(Term::Const(c)), Some(term)) => {
                            New::Checked(term, c)
                        }
                        _ => New::Unknown,
                    },
                    BinOp::SubWithOverflow => match (l, r) {
                        (Some(term), Some(Term::Const(c))) => New::Checked(term, -c),
                        _ => New::Unknown,
                    },
                    BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Eq | BinOp::Ne => {
                        match (l, r) {
                            (Some(left), Some(right)) => New::Cond(Cond {
                                op: *op,
                                left,
                                right,
                            }),
                            _ => New::Unknown,
                        }
                    }
                    _ => New::Unknown,
                }
            }
            _ => New::Unknown,
        };
        // The relay 066 review's B1: an unsigned step that may wrap is not
        // exact.
        let new = match new {
            New::Term(term, c) if !self.step_exact(state, x, term, c) => New::Unknown,
            other => other,
        };
        // Overwrite x: its old facts go first (the new value was computed
        // above, against the old state).
        match new {
            New::Term(Term::Var(y), c) if Some(y) == x_var => {
                let mentions = |term: Term| matches!(term, Term::Var(v) if v == y);
                state
                    .conds
                    .retain(|_, cond| !mentions(cond.left) && !mentions(cond.right));
                state.checked.retain(|_, (term, _)| !mentions(*term));
                state.dbm.assign(y, y, c);
            }
            New::Term(term, c) => {
                self.kill(state, x);
                if let Some(x_var) = x_var {
                    self.assign_term(state, x_var, term, c);
                }
            }
            New::Pointer(src, derivation) => {
                let src_var = self.var(src);
                self.kill(state, x);
                if derivation == Derivation::Derived
                    && let (Some(x_var), Some(src_var)) = (x_var, src_var)
                    && x_var != src_var
                {
                    state.dbm.assign(x_var, src_var, 0);
                }
                state.derivation.insert(x, derivation);
            }
            New::Cond(cond) => {
                self.kill(state, x);
                state.conds.insert(x, cond);
            }
            New::Checked(term, c) => {
                self.kill(state, x);
                state.checked.insert(x, (term, c));
            }
            New::Unknown => self.kill(state, x),
        }
        if let Some(x_var) = x_var
            && self.unsigned(x)
        {
            state.dbm.constrain(0, x_var, 0);
        }
    }

    /// Does the cast keep the value? Widening within a signedness, unsigned
    /// into a signed type at least as wide (`usize` into `isize`: a length is
    /// below `isize::MAX`), and signed into unsigned when the value is proven
    /// non-negative.
    fn value_preserving(
        &self,
        state: &State,
        term: Term,
        from: (u64, bool),
        to: (u64, bool),
    ) -> bool {
        let non_negative = match term {
            Term::Const(k) => k >= 0,
            Term::Var(v) => state.dbm.get(0, v) <= 0,
        };
        match (from.1, to.1) {
            (false, false) | (true, true) => to.0 >= from.0,
            // Unsigned into signed: wider always; the same width only for a
            // value bounded by the length (the relay 066 review's B5: `u32
            // as i32` of `0xFFFF_FFFF` is -1).
            (false, true) => {
                to.0 > from.0
                    || (to.0 == from.0
                        && match term {
                            Term::Const(k) => k >= 0,
                            Term::Var(v) => {
                                let n = self.var(self.n).expect("the companion is tracked");
                                state.dbm.get(v, n) <= 0
                            }
                        })
            }
            (true, false) => to.0 >= from.0 && non_negative,
        }
    }

    /// Is `x := term + c` exact? A signed step is (C's signed overflow is UB,
    /// §28). An unsigned one only when it provably does not wrap: `− c` needs
    /// `term ≥ c`, and `+ c` needs a bound `term ≤ z − c` on a variable `z`
    /// no wider than x, or a constant upper bound with room for `c` (the relay
    /// 066 review's B1: `n.wrapping_sub(1)` at `n = 0`).
    fn step_exact(&self, state: &State, x: Local, term: Term, c: i64) -> bool {
        let Some((bits, signed)) = int_shape(self.body.local_decls[x].ty) else {
            return true;
        };
        if signed {
            return true;
        }
        let max: i128 = if bits >= 64 {
            i128::MAX
        } else {
            (1i128 << bits) - 1
        };
        match term {
            Term::Const(k) => (k as i128 + c as i128) >= 0 && (k as i128 + c as i128) <= max,
            Term::Var(_) if c == 0 => true,
            Term::Var(y) if c < 0 => state.dbm.get(0, y) <= c,
            Term::Var(y) => {
                let upper = state.dbm.get(y, 0);
                (upper < INF && upper as i128 + c as i128 <= max)
                    || self.var_locals.iter().enumerate().any(|(index, local)| {
                        let z = index + 1;
                        z != y
                            && state.dbm.get(y, z) <= -c
                            && int_shape(self.body.local_decls[*local].ty)
                                .is_some_and(|(width, _)| width <= bits)
                    })
            }
        }
    }

    /// Does an rvalue carry a derived (or maybe-derived) pointer out?
    fn rvalue_carries_derived(&self, state: &State, rvalue: &Rvalue<'tcx>) -> bool {
        let derived = |operand: &Operand<'tcx>| {
            operand_local(operand).is_some_and(|local| state.derivation(local) != Derivation::Other)
        };
        match rvalue {
            Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) | Rvalue::Repeat(operand, _) => {
                derived(operand)
            }
            Rvalue::Aggregate(_, operands) => operands.iter().any(derived),
            Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) | Rvalue::CopyForDeref(place) => {
                state.derivation(place.local) != Derivation::Other
            }
            _ => false,
        }
    }

    /// The calls step 1 models: pointer steps on a derived pointer, and
    /// `wrapping_add` / `wrapping_sub` by a constant on an integer. Every
    /// other call that receives a derived pointer is refused (step 3's
    /// summaries).
    fn call(
        &self,
        state: &mut State,
        func: &Operand<'tcx>,
        args: &[rustc_span::source_map::Spanned<Operand<'tcx>>],
        destination: &Place<'tcx>,
        span: rustc_span::Span,
        refuse: &mut dyn FnMut(Refusal),
    ) {
        let callee = func.const_fn_def().map(|(def, _)| def);
        let name = callee
            .map(|def| self.tcx.item_name(def).to_string())
            .unwrap_or_default();
        // The relay 066 review's B3: the INHERENT raw-pointer and integer
        // methods, not any callee that shares their names.
        let path = callee
            .map(|def| self.tcx.def_path_str(def))
            .unwrap_or_default();
        let raw_pointer_method =
            path.contains("ptr::const_ptr::<impl") || path.contains("ptr::mut_ptr::<impl");
        let integer_method = path.contains("num::<impl");
        let dest = destination.as_local();
        let receiver = args.first().and_then(|arg| operand_local(&arg.node));
        let pointer_step = raw_pointer_method
            && matches!(
                name.as_str(),
                "offset" | "add" | "sub" | "wrapping_offset" | "wrapping_add" | "wrapping_sub"
            )
            && receiver.is_some_and(|local| pointee(self.body.local_decls[local].ty).is_some());
        if pointer_step && args.len() == 2 {
            let receiver = receiver.expect("a pointer step has a receiver");
            let derivation = state.derivation(receiver);
            let Some(dest) = dest else {
                if derivation != Derivation::Other {
                    refuse(Refusal {
                        reason: "stored".to_owned(),
                        span,
                    });
                }
                return;
            };
            let step = self.term(state, &args[1].node);
            let backwards = matches!(name.as_str(), "sub" | "wrapping_sub");
            let src_var = self.var(receiver);
            let exact = src_var.and_then(|v| state.dbm.exact(v));
            let old = state.clone();
            self.kill(state, dest);
            if derivation == Derivation::Other {
                return;
            }
            state.derivation.insert(dest, derivation);
            // A tainted receiver's step keeps no offset (B4).
            let (Some(dest_var), Some(src_var), Derivation::Derived) =
                (self.var(dest), src_var, derivation)
            else {
                return;
            };
            match (step, backwards) {
                (Some(Term::Const(c)), _) => {
                    let c = if backwards { -c } else { c };
                    if dest_var == src_var {
                        state.dbm = old.dbm.clone();
                        state.dbm.assign(dest_var, dest_var, c);
                    } else {
                        state.dbm.assign(dest_var, src_var, c);
                    }
                }
                (Some(Term::Var(k)), false) if k != dest_var => {
                    if let Some(base) = exact {
                        state.dbm.assign(dest_var, k, base);
                    }
                }
                _ => {}
            }
            return;
        }
        // Integer steps by a constant.
        if integer_method
            && matches!(name.as_str(), "wrapping_add" | "wrapping_sub")
            && args.len() == 2
            && let Some(dest) = dest
            && let Some(dest_var) = self.var(dest)
            && self.body.local_decls[dest].ty.is_integral()
        {
            let (left, right) = (
                self.term(state, &args[0].node),
                self.term(state, &args[1].node),
            );
            let sign = if name == "wrapping_add" { 1 } else { -1 };
            self.kill(state, dest);
            let old = state.clone();
            match (left, right) {
                (Some(term), Some(Term::Const(c)))
                    if self.step_exact(&old, dest, term, sign * c) =>
                {
                    self.assign_term(state, dest_var, term, sign * c)
                }
                (Some(Term::Const(c)), Some(term))
                    if sign == 1 && self.step_exact(&old, dest, term, c) =>
                {
                    self.assign_term(state, dest_var, term, c)
                }
                _ => {}
            }
            if self.unsigned(dest) {
                state.dbm.constrain(0, dest_var, 0);
            }
            return;
        }
        // `q.is_null()` reads nothing and keeps nothing.
        if raw_pointer_method
            && name == "is_null"
            && args.len() == 1
            && receiver.is_some_and(|local| pointee(self.body.local_decls[local].ty).is_some())
        {
            if let Some(dest) = dest {
                self.kill(state, dest);
            }
            return;
        }
        // Any other call: a derived pointer handed to it escapes the domain.
        for arg in args {
            if operand_local(&arg.node)
                .is_some_and(|local| state.derivation(local) != Derivation::Other)
            {
                refuse(Refusal {
                    reason: format!(
                        "handed-to:{}",
                        callee.map(|d| self.tcx.def_path_str(d)).unwrap_or_default()
                    ),
                    span,
                });
            }
        }
        if let Some(dest) = dest {
            self.kill(state, dest);
            if let Some(dest_var) = self.var(dest)
                && self.unsigned(dest)
            {
                state.dbm.constrain(0, dest_var, 0);
            }
        }
    }

    /// The access check on a place that dereferences a pointer.
    fn check_place_access(
        &self,
        state: &State,
        place: &Place<'tcx>,
        span: rustc_span::Span,
        refuse: &mut dyn FnMut(Refusal),
    ) {
        if !matches!(place.projection.first(), Some(ProjectionElem::Deref)) {
            return;
        }
        match state.derivation(place.local) {
            Derivation::Other => {}
            Derivation::Tainted => refuse(Refusal {
                reason: "access-through-a-cast-or-merged-pointer".to_owned(),
                span,
            }),
            Derivation::Derived => {
                let Some(q) = self.var(place.local) else {
                    refuse(Refusal {
                        reason: "access-untracked".to_owned(),
                        span,
                    });
                    return;
                };
                let n = self.var(self.n).expect("the companion is tracked");
                let lower = state.dbm.get(0, q) <= 0;
                let upper = state.dbm.get(q, n) <= -1;
                if !(lower && upper) {
                    refuse(Refusal {
                        reason: format!(
                            "access-unproven:{}",
                            if lower { "upper" } else { "lower" }
                        ),
                        span,
                    });
                }
            }
        }
    }

    fn check_operand_access(
        &self,
        state: &State,
        operand: &Operand<'tcx>,
        span: rustc_span::Span,
        refuse: &mut dyn FnMut(Refusal),
    ) {
        if let Operand::Copy(place) | Operand::Move(place) = operand {
            self.check_place_access(state, place, span, refuse);
        }
    }

    fn check_rvalue_accesses(
        &self,
        state: &State,
        rvalue: &Rvalue<'tcx>,
        span: rustc_span::Span,
        refuse: &mut dyn FnMut(Refusal),
    ) {
        match rvalue {
            Rvalue::Use(operand)
            | Rvalue::Cast(_, operand, _)
            | Rvalue::UnaryOp(_, operand)
            | Rvalue::Repeat(operand, _) => self.check_operand_access(state, operand, span, refuse),
            Rvalue::BinaryOp(_, box (left, right)) => {
                self.check_operand_access(state, left, span, refuse);
                self.check_operand_access(state, right, span, refuse);
            }
            Rvalue::Aggregate(_, operands) => {
                for operand in operands {
                    self.check_operand_access(state, operand, span, refuse);
                }
            }
            Rvalue::Ref(_, _, place)
            | Rvalue::RawPtr(_, place)
            | Rvalue::CopyForDeref(place)
            | Rvalue::Discriminant(place) => self.check_place_access(state, place, span, refuse),
            _ => {}
        }
    }
}

fn operand_local(operand: &Operand<'_>) -> Option<Local> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place.as_local(),
        Operand::Constant(_) => None,
    }
}
