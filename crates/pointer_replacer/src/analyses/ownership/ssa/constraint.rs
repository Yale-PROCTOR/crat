use std::{num::NonZeroU32, ops::Range};

use rustc_hir::def_id::DefId;
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{ClearCrossCrate, LocalDecl, LocalInfo},
    ty::TyKind,
};

use super::consume::Voidable;
use crate::analyses::ownership::{
    CrateCtxt, ptr::Measurable, struct_ctxt::StructCtxt, vec_vec::VecVec,
    whole_program::OwnershipSolver,
};

pub mod infer;
// pub mod prune;

rustc_index::newtype_index! {
    #[orderable]
    #[debug_format = "{}"]
    pub struct Var {
        // DEBUG_FORMAT = "{}"// "𝕆({})"
    }
}

impl std::fmt::Display for Var {
    // \mathbb{O}
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("𝕆({})", self.as_u32()))
    }
}

impl Var {
    pub const INVALID: Self = Var::from_u32(0);
    pub const MIN: Self = Var::from_u32(1);

    pub fn into_lit(self) -> i32 {
        self.as_u32() as i32
    }
}

impl std::ops::Add<u32> for Var {
    type Output = Self;

    fn add(self, rhs: u32) -> Self::Output {
        Var::from_u32(self.as_u32() + rhs)
    }
}

impl std::ops::AddAssign<u32> for Var {
    fn add_assign(&mut self, rhs: u32) {
        *self = *self + rhs
    }
}

#[inline]
pub fn local_has_non_zero_measure<'tcx>(
    local_decl: &LocalDecl,
    measurable: impl Measurable<'tcx>,
) -> bool {
    local_measure(local_decl, measurable).is_some()
}

/// test whether a local might be owning
#[inline]
pub fn local_measure<'tcx>(
    local_decl: &LocalDecl,
    measurable: impl Measurable<'tcx>,
) -> Option<NonZeroU32> {
    let ty = local_decl.ty;
    let measure = measurable.measure(ty, 0);
    let is_deref_temp = matches!(
        local_decl.local_info.as_ref(),
        ClearCrossCrate::Set(local_info) if matches!(local_info.as_ref(), LocalInfo::DerefTemp)
    );
    (!is_deref_temp).then(|| NonZeroU32::new(measure)).flatten()
}

#[inline]
pub fn initialize_local<'tcx>(
    local_decl: &LocalDecl,
    var_gen: &mut Gen,
    database: &mut impl Database,
    measurable: impl Measurable<'tcx>,
) -> Option<Range<Var>> {
    local_measure(local_decl, measurable).map(|measure| database.new_vars(var_gen, measure.get()))
}

pub struct GlobalAssumptions {
    struct_fields: VecVec<Var>,
}

impl GlobalAssumptions {
    pub fn new<'tcx>(
        crate_ctxt: &CrateCtxt<'tcx>,
        var_gen: &mut Gen,
        database: &mut impl Database,
    ) -> Self {
        let CrateCtxt {
            tcx,
            ref struct_ctxt,
            ..
        } = *crate_ctxt;
        let mut struct_fields = VecVec::with_indices_capacity(struct_ctxt.post_order.len());

        for &did in &struct_ctxt.post_order {
            let ty = tcx.type_of(did).skip_binder();
            let TyKind::Adt(adt_def, subst) = ty.kind() else { unreachable!() };
            struct_fields.push_inner(var_gen.next());
            for field_def in adt_def.all_fields() {
                let field_ty = field_def.ty(tcx, subst);
                let ptr_depth = struct_ctxt.measure_ptr(field_ty);
                database.new_vars(var_gen, ptr_depth);
                struct_fields.push_inner(var_gen.next());
            }
            struct_fields.push();
        }

        let struct_fields = struct_fields.done();

        GlobalAssumptions { struct_fields }
    }

    pub fn fields<'a, 'tcx>(
        &'a self,
        struct_ctxt: &'a StructCtxt<'tcx>,
        did: &DefId,
    ) -> impl Iterator<Item = Range<Var>> + 'a {
        let idx = struct_ctxt.did_idx(did);
        self.struct_fields[idx]
            .array_windows()
            .map(|&[start, end]| start..end)
    }
}

impl Voidable for Range<Var> {
    const VOID: Self = Range {
        start: Var::INVALID,
        end: Var::INVALID,
    };

    #[inline]
    fn is_void(&self) -> bool {
        self.start == Var::INVALID && self.end == Var::INVALID
    }
}

/// A generator for [Var]
pub struct Gen {
    next: Var,
}

impl Gen {
    #[inline]
    pub const fn new() -> Self {
        Gen { next: Var::MIN }
    }

    pub fn new_sigs(&mut self, size: u32) -> Range<Var> {
        let start = self.next;
        self.next += size;
        let end = self.next;
        start..end
    }

    #[inline]
    pub fn next(&self) -> Var {
        self.next
    }
}

#[derive(Clone, Debug)]
pub enum Constraint {
    /// x + y = z
    /// CNF | (¬x ∨ ¬y) ∧ (¬x ∨ z) ∧ (x ∨ y ∨ ¬z) ∧ (¬y ∨ z)
    Linear { x: Var, y: Var, z: Var },
    /// assert [sign]x
    Assume { x: Var, sign: bool },
    /// x = y
    Equal { x: Var, y: Var },
    /// x <= y
    LessEqual { x: Var, y: Var },
    /// x = y and z
    EqMin { x: Var, y: Var, z: Var },
}

impl std::fmt::Display for Constraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            Constraint::Linear { x, y, z } => f.write_fmt(format_args!("{x} + {y} = {z}")),
            Constraint::Assume { x, sign } => {
                if sign {
                    f.write_fmt(format_args!("{x} = 1"))
                } else {
                    f.write_fmt(format_args!("{x} = 0"))
                }
            }
            Constraint::Equal { x, y } => f.write_fmt(format_args!("{x} = {y}")),
            Constraint::LessEqual { x, y } => f.write_fmt(format_args!("{x} <= {y}")),
            Constraint::EqMin { x, y, z } => f.write_fmt(format_args!("{x} = min({y}, {z})")),
        }
    }
}

pub trait Mode {
    /// `Store<'a>` is a reference to a storage that holds
    /// the newly added constraint.
    type Store<'a>
    where Self: 'a;
    fn store_linear(store: Self::Store<'_>, x: Var, y: Var, z: Var);

    fn store_assumption(store: Self::Store<'_>, x: Var, sign: bool);

    fn store_equal(store: Self::Store<'_>, x: Var, y: Var);

    fn store_less_equal(store: Self::Store<'_>, x: Var, y: Var);

    fn store_eq_min(store: Self::Store<'_>, x: Var, y: Var, z: Var);
}

macro_rules! tracing_for {
    (Debug, $args:tt) => {
        tracing::debug!($args)
    };
}

macro_rules! make_logging_mode {
    ($level:ident) => {
        pub struct $level;
        impl Mode for $level {
            type Store<'a> = ();

            #[inline]
            fn store_linear((): Self::Store<'_>, x: Var, y: Var, z: Var) {
                let constraint = Constraint::Linear { x, y, z };
                tracing_for!($level, "emitting constraint: {constraint}")
            }

            #[inline]
            fn store_assumption((): Self::Store<'_>, x: Var, sign: bool) {
                let constraint = Constraint::Assume { x, sign };
                tracing_for!($level, "emitting constraint: {constraint}")
            }

            fn store_equal((): Self::Store<'_>, x: Var, y: Var) {
                let constraint = Constraint::Equal { x, y };
                tracing_for!($level, "emitting constraint: {constraint}")
            }

            fn store_less_equal((): Self::Store<'_>, x: Var, y: Var) {
                let constraint = Constraint::LessEqual { x, y };
                tracing_for!($level, "emitting constraint: {constraint}")
            }

            fn store_eq_min((): Self::Store<'_>, x: Var, y: Var, z: Var) {
                let constraint = Constraint::EqMin { x, y, z };
                tracing_for!($level, "emitting constraint: {constraint}")
            }
        }
    };
}

make_logging_mode!(Debug);

pub trait Database {
    #[inline]
    fn new_vars(&mut self, var_gen: &mut Gen, size: u32) -> Range<Var> {
        var_gen.new_sigs(size)
    }

    fn push_linear_impl(&mut self, x: Var, y: Var, z: Var);
    fn push_linear<Infer: Mode>(&mut self, store: Infer::Store<'_>, x: Var, y: Var, z: Var) {
        self.push_linear_impl(x, y, z);
        Infer::store_linear(store, x, y, z);
    }
    fn push_assume_impl(&mut self, x: Var, sign: bool);
    fn push_assume<Infer: Mode>(&mut self, store: Infer::Store<'_>, x: Var, sign: bool) {
        self.push_assume_impl(x, sign);
        Infer::store_assumption(store, x, sign);
    }
    fn push_equal_impl(&mut self, x: Var, y: Var);
    fn push_equal<Infer: Mode>(&mut self, store: Infer::Store<'_>, x: Var, y: Var) {
        self.push_equal_impl(x, y);
        Infer::store_equal(store, x, y);
    }
    fn push_less_equal_impl(&mut self, x: Var, y: Var);
    fn push_less_equal<Infer: Mode>(&mut self, store: Infer::Store<'_>, x: Var, y: Var) {
        self.push_less_equal_impl(x, y);
        Infer::store_less_equal(store, x, y);
    }

    fn push_eq_min_impl(&mut self, x: Var, y: Var, z: Var);
    fn push_eq_min<Infer: Mode>(&mut self, store: Infer::Store<'_>, x: Var, y: Var, z: Var) {
        self.push_eq_min_impl(x, y, z);
        Infer::store_eq_min(store, x, y, z);
    }
}

impl Database for () {
    fn push_linear_impl(&mut self, _: Var, _: Var, _: Var) {}

    fn push_assume_impl(&mut self, _: Var, _: bool) {}

    fn push_equal_impl(&mut self, _: Var, _: Var) {}

    fn push_less_equal_impl(&mut self, _: Var, _: Var) {}

    fn push_eq_min_impl(&mut self, _: Var, _: Var, _: Var) {}
}

/// The database of the selected [OwnershipSolver]: the driver's scope calls and the constraints go
/// to [SatDatabase] (CaDiCaL) or to [Z3Database] (z3, as on master).
pub enum SolverDatabase {
    Cadical(SatDatabase),
    Z3(Z3Database),
}

impl SolverDatabase {
    pub fn new(solver: OwnershipSolver) -> Self {
        match solver {
            OwnershipSolver::Cadical => Self::Cadical(SatDatabase::new()),
            OwnershipSolver::Z3 => Self::Z3(Z3Database::new()),
        }
    }

    /// Opens one function's scope (z3: `push`).
    pub fn open_scope(&mut self) {
        match self {
            Self::Cadical(db) => db.open_scope(),
            Self::Z3(db) => db.solver.push(),
        }
    }

    /// Whether the constraints so far are satisfiable; `None` when the solver cannot tell.
    pub fn check_scope(&mut self) -> Option<bool> {
        match self {
            Self::Cadical(db) => db.check_scope(),
            Self::Z3(db) => match db.solver.check() {
                z3::SatResult::Sat => Some(true),
                z3::SatResult::Unsat => Some(false),
                z3::SatResult::Unknown => None,
            },
        }
    }

    /// Closes the scope: kept, or discarded (z3: `pop`; a kept z3 scope is never popped).
    pub fn close_scope(&mut self, keep: bool) {
        match self {
            Self::Cadical(db) => db.close_scope(keep),
            Self::Z3(db) => {
                if !keep {
                    db.solver.pop(1);
                }
            }
        }
    }

    /// The value of each [Var] below `end` (`None`: Unknown). z3 reads its model without model
    /// completion, so a [Var] the model leaves out is Unknown, as on master.
    pub fn model(&mut self, end: Var) -> anyhow::Result<Vec<Option<bool>>> {
        match self {
            Self::Cadical(db) => db.model(end),
            Self::Z3(db) => {
                assert!(matches!(db.solver.check(), z3::SatResult::Sat));
                let model = db.solver.get_model().unwrap();
                Ok((Var::MIN..end)
                    .map(|x| model.eval(&db.z3_ast[x], false).unwrap().as_bool())
                    .collect())
            }
        }
    }
}

impl Database for SolverDatabase {
    fn new_vars(&mut self, var_gen: &mut Gen, size: u32) -> Range<Var> {
        match self {
            Self::Cadical(db) => db.new_vars(var_gen, size),
            Self::Z3(db) => db.new_vars(var_gen, size),
        }
    }

    fn push_linear_impl(&mut self, x: Var, y: Var, z: Var) {
        match self {
            Self::Cadical(db) => db.push_linear_impl(x, y, z),
            Self::Z3(db) => db.push_linear_impl(x, y, z),
        }
    }

    fn push_assume_impl(&mut self, x: Var, sign: bool) {
        match self {
            Self::Cadical(db) => db.push_assume_impl(x, sign),
            Self::Z3(db) => db.push_assume_impl(x, sign),
        }
    }

    fn push_equal_impl(&mut self, x: Var, y: Var) {
        match self {
            Self::Cadical(db) => db.push_equal_impl(x, y),
            Self::Z3(db) => db.push_equal_impl(x, y),
        }
    }

    fn push_less_equal_impl(&mut self, x: Var, y: Var) {
        match self {
            Self::Cadical(db) => db.push_less_equal_impl(x, y),
            Self::Z3(db) => db.push_less_equal_impl(x, y),
        }
    }

    fn push_eq_min_impl(&mut self, x: Var, y: Var, z: Var) {
        match self {
            Self::Cadical(db) => db.push_eq_min_impl(x, y, z),
            Self::Z3(db) => db.push_eq_min_impl(x, y, z),
        }
    }
}

pub struct Z3Database {
    pub solver: z3::Solver,
    pub z3_ast: IndexVec<Var, z3::ast::Bool>,
}

impl Z3Database {
    pub fn new() -> Self {
        let mut z3_ast = IndexVec::with_capacity(100);
        z3_ast.push(z3::ast::Bool::new_const("dummy"));
        Z3Database {
            solver: z3::Solver::new(),
            z3_ast,
        }
    }
}

impl Database for Z3Database {
    fn new_vars(&mut self, var_gen: &mut Gen, size: u32) -> Range<Var> {
        let sigs = var_gen.new_sigs(size);
        for sig in sigs.clone() {
            assert_eq!(
                sig,
                self.z3_ast.push(z3::ast::Bool::new_const(sig.as_u32()))
            )
        }
        sigs
    }

    fn push_linear_impl(&mut self, x: Var, y: Var, z: Var) {
        let [x, y, z] = [x, y, z].map(|sig| &self.z3_ast[sig]);
        self.solver.assert(z3::ast::Bool::or(&[&!x, &!y]));
        self.solver.assert(z3::ast::Bool::or(&[&!x, z]));
        self.solver.assert(z3::ast::Bool::or(&[x, y, &!z]));
        self.solver.assert(z3::ast::Bool::or(&[&!y, z]));
    }

    fn push_assume_impl(&mut self, x: Var, sign: bool) {
        let x = &self.z3_ast[x];
        let value = z3::ast::Bool::from_bool(sign);
        self.solver.assert(&!(x.xor(&value)))
        // self.solver.assert(&!z3::ast::Bool::xor(x, &value));
    }

    fn push_equal_impl(&mut self, x: Var, y: Var) {
        let [x, y] = [x, y].map(|sig| &self.z3_ast[sig]);
        self.solver.assert(&!(x.xor(y)));
    }

    fn push_less_equal_impl(&mut self, x: Var, y: Var) {
        let [x, y] = [x, y].map(|sig| &self.z3_ast[sig]);
        self.solver.assert(z3::ast::Bool::or(&[&!x, y]));
    }

    fn push_eq_min_impl(&mut self, x: Var, y: Var, z: Var) {
        let [x, y, z] = [x, y, z].map(|sig| &self.z3_ast[sig]);
        self.solver.assert(z3::ast::Bool::or(&[&!x, y]));
        self.solver.assert(z3::ast::Bool::or(&[&!x, z]));
        self.solver.assert(z3::ast::Bool::or(&[x, &!y, &!z]));
    }
}

/// The ownership constraints as CNF, solved in-process and incrementally by CaDiCaL.
///
/// One function's constraints are solved in a scope ([SatDatabase::open_scope]). Each clause added
/// while the scope is open is guarded by the scope's activation literal `a` (it is added as
/// `¬a ∨ C`), and [SatDatabase::check_scope] solves under the assumption `a`. The scope is then
/// closed ([SatDatabase::close_scope]): kept, where the unit `a` makes its clauses permanent, or
/// discarded, where the unit `¬a` satisfies them so that they constrain nothing more. Clauses
/// added outside a scope are permanent.
///
/// The solver variable of a [Var] means "the [Var] is NOT owning"; the [Var]'s own literal is its
/// negation. CaDiCaL decides a free variable true first (its initial phase), so a [Var] the kept
/// clauses leave free tends toward not owning. For the same reason [SatDatabase::model] solves
/// under a fresh assumption: CaDiCaL's lucky phases, which run only in a solve without
/// assumptions and may try all-false (here: all owning) first, stay out of it.
///
/// This is a tendency, not a guarantee. A variable that bounded variable elimination removed is
/// never decided: its value is rebuilt starting from false (changed only where a removed clause
/// needs it), and false here means owning. Phase saving records every assignment, including those
/// made while solving a scope that was then discarded, so a later solve can start a [Var] from a
/// phase an earlier scope left. Rephasing and local search can move the saved phases too. The
/// validity of the model rests on none of this: the self-check covers every kept clause.
pub struct SatDatabase {
    solver: cadical::Solver,
    /// The solver variable of each [Var], true when the [Var] is NOT owning: 0 until the [Var]
    /// first occurs in a clause.
    lits: IndexVec<Var, i32>,
    /// Whether each [Var] occurs in a kept clause (outside every scope, or in a kept scope).
    kept: IndexVec<Var, bool>,
    /// The last solver variable handed out, to a [Var] or to a scope's activation literal.
    last_lit: i32,
    /// The kept clauses over solver literals, each followed by 0, for the model's self-check.
    clauses: Vec<i32>,
    scope: Option<Scope>,
}

struct Scope {
    activation: i32,
    /// The scope's clauses over solver literals (without the activation literal), each followed
    /// by 0.
    clauses: Vec<i32>,
    /// The [Var]s the scope's clauses name that were not kept before.
    vars: Vec<Var>,
}

impl SatDatabase {
    pub fn new() -> Self {
        let mut lits = IndexVec::with_capacity(100);
        let mut kept = IndexVec::with_capacity(100);
        // [Var::INVALID]
        lits.push(0);
        kept.push(false);
        SatDatabase {
            solver: cadical::Solver::new(),
            lits,
            kept,
            last_lit: 0,
            clauses: Vec::new(),
            scope: None,
        }
    }

    fn fresh_lit(&mut self) -> i32 {
        self.last_lit = self
            .last_lit
            .checked_add(1)
            .expect("too many SAT variables");
        self.last_lit
    }

    /// The solver literal of `x` (owning) when `positive`, else of `¬x`. The solver variable of
    /// `x` means "`x` is NOT owning", so `x` itself is its negation.
    fn lit(&mut self, x: Var, positive: bool) -> i32 {
        if self.lits[x] == 0 {
            let lit = self.fresh_lit();
            self.lits[x] = lit;
        }
        if positive {
            -self.lits[x]
        } else {
            self.lits[x]
        }
    }

    /// Adds the clause of the given literals, each a [Var] and its polarity.
    fn clause<const N: usize>(&mut self, literals: [(Var, bool); N]) {
        let clause = literals.map(|(x, positive)| self.lit(x, positive));
        match &mut self.scope {
            Some(scope) => {
                self.solver
                    .add_clause(std::iter::once(-scope.activation).chain(clause));
                scope.clauses.extend(clause);
                scope.clauses.push(0);
                for (x, _) in literals {
                    if !self.kept[x] {
                        scope.vars.push(x);
                    }
                }
            }
            None => {
                self.solver.add_clause(clause);
                self.clauses.extend(clause);
                self.clauses.push(0);
                for (x, _) in literals {
                    self.kept[x] = true;
                }
            }
        }
    }

    /// Opens the scope of one function's constraints.
    pub fn open_scope(&mut self) {
        assert!(self.scope.is_none(), "ownership scopes do not nest");
        let activation = self.fresh_lit();
        self.scope = Some(Scope {
            activation,
            clauses: Vec::new(),
            vars: Vec::new(),
        });
    }

    /// Solves the kept clauses together with the open scope's: `Some(true)` satisfiable,
    /// `Some(false)` unsatisfiable, `None` when the solver gave no answer.
    pub fn check_scope(&mut self) -> Option<bool> {
        let activation = self.scope.as_ref().expect("no open scope").activation;
        self.solver.solve_with([activation])
    }

    /// Closes the open scope: its clauses are kept, and constrain every later check and the model,
    /// or discarded, and constrain nothing more.
    pub fn close_scope(&mut self, keep: bool) {
        let scope = self.scope.take().expect("no open scope");
        if keep {
            self.solver.add_clause([scope.activation]);
            self.clauses.extend(scope.clauses);
            for x in scope.vars {
                self.kept[x] = true;
            }
        } else {
            self.solver.add_clause([-scope.activation]);
        }
    }

    /// The value of each [Var] in `Var::MIN..end` under a model of the kept clauses.
    ///
    /// A [Var] that occurs in no kept clause reads `None` (unknown): no kept constraint gives it a
    /// value, and the solver's model, which is total, would otherwise report an arbitrary one.
    /// z3's model evaluation without completion gave such a [Var] no value either; it could also
    /// leave out a [Var] that does occur in kept clauses (one its search did not need), which
    /// here reads the value of CaDiCaL's model.
    ///
    /// Self-check: every kept clause must be true under the model read out; otherwise an error.
    pub fn model(&mut self, end: Var) -> anyhow::Result<Vec<Option<bool>>> {
        assert!(self.scope.is_none(), "a scope is still open");
        // A fresh literal in no clause, assumed only to keep the lucky phases out of this solve.
        let fresh = self.fresh_lit();
        assert_eq!(self.solver.solve_with([fresh]), Some(true));

        for (index, clause) in self.clauses.split(|&lit| lit == 0).enumerate() {
            if !clause.is_empty()
                && !clause
                    .iter()
                    .any(|&lit| self.solver.value(lit) == Some(true))
            {
                anyhow::bail!("the SAT model violates kept ownership clause {index}: {clause:?}");
            }
        }

        Ok((Var::MIN..end)
            .map(|x| {
                self.kept[x]
                    .then_some(self.lits[x])
                    .and_then(|not_owning| self.solver.value(-not_owning))
            })
            .collect())
    }
}

impl Database for SatDatabase {
    fn new_vars(&mut self, var_gen: &mut Gen, size: u32) -> Range<Var> {
        let sigs = var_gen.new_sigs(size);
        for sig in sigs.clone() {
            assert_eq!(sig, self.lits.push(0));
            assert_eq!(sig, self.kept.push(false));
        }
        sigs
    }

    fn push_linear_impl(&mut self, x: Var, y: Var, z: Var) {
        self.clause([(x, false), (y, false)]);
        self.clause([(x, false), (z, true)]);
        self.clause([(x, true), (y, true), (z, false)]);
        self.clause([(y, false), (z, true)]);
    }

    fn push_assume_impl(&mut self, x: Var, sign: bool) {
        self.clause([(x, sign)]);
    }

    fn push_equal_impl(&mut self, x: Var, y: Var) {
        self.clause([(x, false), (y, true)]);
        self.clause([(x, true), (y, false)]);
    }

    fn push_less_equal_impl(&mut self, x: Var, y: Var) {
        self.clause([(x, false), (y, true)]);
    }

    fn push_eq_min_impl(&mut self, x: Var, y: Var, z: Var) {
        self.clause([(x, false), (y, true)]);
        self.clause([(x, false), (z, true)]);
        self.clause([(x, true), (y, false), (z, false)]);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// x is kept outside any scope; a kept scope adds x <= y, z = min(x, y) and f <= g, which
    /// leaves f and g free; a discarded scope adds y = 0, which contradicts them, and w = y, the
    /// only clause that names w; v is in no clause.
    fn build() -> (SatDatabase, Gen, [Var; 7]) {
        let mut var_gen = Gen::new();
        let mut db = SatDatabase::new();
        let vars = db.new_vars(&mut var_gen, 7);
        let [x, y, z, w, v, f, g] = std::array::from_fn(|i| vars.start + i as u32);

        db.push_assume_impl(x, true);

        db.open_scope();
        db.push_less_equal_impl(x, y);
        db.push_eq_min_impl(z, x, y);
        db.push_less_equal_impl(f, g);
        assert_eq!(db.check_scope(), Some(true));
        db.close_scope(true);

        db.open_scope();
        db.push_assume_impl(y, false);
        db.push_equal_impl(w, y);
        assert_eq!(db.check_scope(), Some(false));
        db.close_scope(false);

        (db, var_gen, [x, y, z, w, v, f, g])
    }

    #[test]
    fn sat_database_scopes_unknown_and_self_check() {
        let (mut db, var_gen, [x, _, _, w, ..]) = build();
        let model = db.model(var_gen.next()).expect("every kept clause holds");
        // x by its unit, y by x <= y, z = min(x, y); w and v occur in no kept clause; f and g are
        // free but kept: not owning, the bias of the negated solver variable.
        assert_eq!(
            model,
            [
                Some(true),
                Some(true),
                Some(true),
                None,
                None,
                Some(false),
                Some(false)
            ]
        );

        // The discarded scope constrains nothing more (w = 1 would contradict its w = y, y = 0);
        // the kept clauses still do (x = 0 contradicts the unit x).
        db.open_scope();
        db.push_assume_impl(w, true);
        assert_eq!(db.check_scope(), Some(true));
        db.close_scope(false);
        db.open_scope();
        db.push_assume_impl(x, false);
        assert_eq!(db.check_scope(), Some(false));
        db.close_scope(false);

        // The same calls give the same model, the free f and g included.
        let (mut again, var_gen, _) = build();
        assert_eq!(again.model(var_gen.next()).unwrap(), model);
    }

    #[test]
    fn sat_database_self_check_rejects_a_false_kept_clause() {
        let (mut db, var_gen, [x, ..]) = build();
        // A kept clause ¬x that the solver never saw: the model (x owning) falsifies it.
        let lit = db.lit(x, false);
        db.clauses.extend([lit, 0]);
        assert!(db.model(var_gen.next()).is_err());
    }
}
