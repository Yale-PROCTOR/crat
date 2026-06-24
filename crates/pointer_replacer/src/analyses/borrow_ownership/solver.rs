use std::ops::Range;

use rustc_hash::FxHashMap;
use rustc_index::IndexVec;
use rustc_span::def_id::LocalDefId;
use z3::{Model, Optimize, SatResult, ast::Bool};

use super::{
    SlotKind,
    crate_slots::CrateSlots,
    slots::{SlotId, SlotUniverse},
    ssa::constraint::{Database, Gen, Var},
};

/// Global identity for a flattened pointer slot.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SlotRef {
    Field(SlotId),
    Local(LocalDefId, SlotId),
}

struct KindVars {
    raw: Bool,
    ref_: Bool,
    own: Bool,
}

pub struct KindSolver {
    solver: Optimize,
    vars: FxHashMap<SlotRef, KindVars>,
}

impl KindSolver {
    pub fn new(slots: &CrateSlots) -> Self {
        let solver = Optimize::new();
        let mut vars = FxHashMap::default();

        add_universe(&solver, &mut vars, &slots.field_slots, SlotRef::Field);
        for (&fn_did, universe) in &slots.fn_local_slots {
            add_universe(&solver, &mut vars, universe, |slot| {
                SlotRef::Local(fn_did, slot)
            });
        }

        // Prefer Ref where hard constraints allow it, then Raw over unnecessary Owning.
        let big = vars.len() as u64 + 1;
        for kind_vars in vars.values() {
            solver.assert_soft(&kind_vars.ref_, big, None);
            solver.assert_soft(&kind_vars.raw, 1u64, None);
        }

        KindSolver { solver, vars }
    }

    pub fn assume(&self, slot: SlotRef, kind: SlotKind) {
        let vars = self
            .vars
            .get(&slot)
            .unwrap_or_else(|| panic!("unknown slot: {slot:?}"));
        match kind {
            SlotKind::Raw => self.solver.assert(&vars.raw),
            SlotKind::Ref => self.solver.assert(&vars.ref_),
            SlotKind::Owning => self.solver.assert(&vars.own),
        }
    }

    pub fn equate(&self, a: SlotRef, b: SlotRef) {
        let va = self
            .vars
            .get(&a)
            .unwrap_or_else(|| panic!("unknown slot: {a:?}"));
        let vb = self
            .vars
            .get(&b)
            .unwrap_or_else(|| panic!("unknown slot: {b:?}"));
        self.solver.assert(&!va.raw.xor(&vb.raw));
        self.solver.assert(&!va.ref_.xor(&vb.ref_));
        self.solver.assert(&!va.own.xor(&vb.own));
    }

    /// Solidification link: tie a slot's `own` one-hot bit to an external Bool
    /// (the disjunction of the slot's per-version ownership Bools). Mirrors the
    /// biconditional idiom in `equate`.
    pub(crate) fn link_own(&self, slot: SlotRef, external: &Bool) {
        let vars = self
            .vars
            .get(&slot)
            .unwrap_or_else(|| panic!("unknown slot: {slot:?}"));
        self.solver.assert(&!vars.own.xor(external));
    }

    /// §8 BB1 — assert a borrow-exclusion guard for one conflict edge: at least one
    /// of the involved slots must NOT be a reference. `¬ref(issuer) ∨ ⋁ ¬ref(requirer)`,
    /// a hard clause over the slots' `ref_` one-hot bits. Committing `¬ref` (not `raw`)
    /// is deliberate — a borrow conflict only refutes the *reference* reading; the
    /// slot's ownership bit may still legitimately settle `Owning`. NO-OP when no slot
    /// is supplied (an all-`Field`-owner edge that BB0's Local-only mapping dropped):
    /// an empty `Bool::or` is `false` and would force spurious UNSAT, so the
    /// field-exclusivity gap is left unconstrained here rather than crashing the
    /// solve (deferred to the struct field-slot mapping).
    ///
    /// A non-empty guard is *not* guaranteed satisfiable: it is unsatisfiable iff
    /// every involved slot is independently pinned to `Ref` by hard ownership facts
    /// (`own(d+1)` true forces `¬raw(d)` via I1, and `own(d)` false), which
    /// `model_kinds_relaxing` cannot repair — it only drops malloc source selectors.
    /// Harmless while BO output is unconsumed; once consumed (post-BB2) the caller
    /// must treat a `None` model as a real possibility, not assume guards never UNSAT.
    ///
    /// Precondition: every supplied `SlotRef` must be registered in this solver — i.e.
    /// derived from the *same* `CrateSlots` the solver was built from. A foreign slot
    /// panics (`unknown slot`). Today's callers share one `CrateSlots`; a debug-assert
    /// is unnecessary while that discipline holds, but BB2's loop must preserve it.
    pub(crate) fn add_borrow_exclusion(&self, issuer: Option<SlotRef>, requirers: &[SlotRef]) {
        let not_ref = |slot: SlotRef| {
            let vars = self
                .vars
                .get(&slot)
                .unwrap_or_else(|| panic!("unknown slot: {slot:?}"));
            !&vars.ref_
        };
        let literals: Vec<Bool> = issuer
            .into_iter()
            .chain(requirers.iter().copied())
            .map(not_ref)
            .collect();
        if literals.is_empty() {
            return;
        }
        let refs: Vec<&Bool> = literals.iter().collect();
        self.solver.assert(&Bool::or(&refs));
    }

    pub fn check(&self) -> SatResult {
        self.solver.check(&[])
    }

    pub(crate) fn optimize(&self) -> &Optimize {
        &self.solver
    }

    pub fn model_kinds(&self) -> Option<FxHashMap<SlotRef, SlotKind>> {
        if self.check() != SatResult::Sat {
            return None;
        }
        let model = self.solver.get_model()?;
        Some(self.read_kinds(&model))
    }

    /// Solve assuming all `source_selectors` (reproducing the hard sources). On
    /// UNSAT, leak the **minimal** set of conflicting sources and return the
    /// resulting per-slot kinds, or `None` if the system is UNSAT for non-source
    /// reasons.
    ///
    /// All z3 Bools share the single thread-local context (the analysis is
    /// single-threaded), so `c == s` is `Z3_is_eq_ast` node identity — valid
    /// because `Bool::clone` shares the `Z3_ast` pointer and `get_unsat_core`
    /// returns the original assumption literals.
    ///
    /// Terminates: phase 1 drops one of finitely many selectors per UNSAT round;
    /// phase 2 visits each dropped selector once. Leaking a source classifies
    /// that allocation non-Owning, which is memory-safe.
    pub(crate) fn model_kinds_relaxing(
        &self,
        source_selectors: &[Bool],
    ) -> Option<FxHashMap<SlotRef, SlotKind>> {
        let mut assumptions: Vec<Bool> = source_selectors.to_vec();
        let mut leaked: Vec<Bool> = Vec::new();

        // Phase 1: drop conflicting source selectors until SAT (or give up).
        loop {
            match self.solver.check(&assumptions) {
                SatResult::Sat => break,
                SatResult::Unsat => {
                    let core = self.solver.get_unsat_core();
                    let idx = assumptions.iter().position(|s| core.iter().any(|c| c == s))?;
                    leaked.push(assumptions.swap_remove(idx));
                }
                SatResult::Unknown => return None,
            }
        }

        // Phase 2: restore any selector that is not actually needed, so we leak
        // the minimal set. z3's unsat core is not guaranteed minimal, so phase 1
        // may drop more than necessary; re-adding a selector that keeps the
        // system SAT proves that allocation did not need to be leaked.
        let mut i = 0;
        while i < leaked.len() {
            assumptions.push(leaked[i].clone());
            if self.solver.check(&assumptions) == SatResult::Sat {
                leaked.swap_remove(i);
            } else {
                assumptions.pop();
                i += 1;
            }
        }

        // Final SAT model under the maximal-retention assumption set.
        match self.solver.check(&assumptions) {
            SatResult::Sat => Some(self.read_kinds(&self.solver.get_model()?)),
            _ => None,
        }
    }

    fn read_kinds(&self, model: &Model) -> FxHashMap<SlotRef, SlotKind> {
        let mut kinds = FxHashMap::default();
        kinds.reserve(self.vars.len());
        for (&slot, vars) in &self.vars {
            let kind = if is_true(model, &vars.own) {
                SlotKind::Owning
            } else if is_true(model, &vars.ref_) {
                SlotKind::Ref
            } else {
                SlotKind::Raw
            };
            kinds.insert(slot, kind);
        }
        kinds
    }
}

fn add_universe<F>(
    solver: &Optimize,
    vars: &mut FxHashMap<SlotRef, KindVars>,
    universe: &SlotUniverse,
    mut slot_ref: F,
) where
    F: FnMut(SlotId) -> SlotRef,
{
    for i in 0..universe.len() {
        let id = SlotId::from_usize(i);
        let kind_vars = KindVars {
            raw: Bool::fresh_const("raw"),
            ref_: Bool::fresh_const("ref"),
            own: Bool::fresh_const("own"),
        };

        assert_exactly_one(solver, &kind_vars);
        vars.insert(slot_ref(id), kind_vars);
    }

    for i in 0..universe.len().saturating_sub(1) {
        let a = SlotId::from_usize(i);
        let b = SlotId::from_usize(i + 1);
        if universe.slot(a).owner == universe.slot(b).owner {
            let a_vars = vars
                .get(&slot_ref(a))
                .unwrap_or_else(|| panic!("missing solver vars for slot {a:?}"));
            let b_vars = vars
                .get(&slot_ref(b))
                .unwrap_or_else(|| panic!("missing solver vars for slot {b:?}"));
            assert_not_both(solver, &a_vars.raw, &b_vars.own);
        }
    }
}

fn assert_exactly_one(solver: &Optimize, vars: &KindVars) {
    solver.assert(&Bool::or(&[&vars.raw, &vars.ref_, &vars.own]));
    assert_not_both(solver, &vars.raw, &vars.ref_);
    assert_not_both(solver, &vars.raw, &vars.own);
    assert_not_both(solver, &vars.ref_, &vars.own);
}

fn assert_not_both(solver: &Optimize, a: &Bool, b: &Bool) {
    solver.assert(&Bool::or(&[&!a, &!b]));
}

fn is_true(model: &Model, b: &Bool) -> bool {
    model
        .eval(b, true)
        .and_then(|value| value.as_bool())
        .unwrap_or(false)
}

pub(crate) struct BoOwnDatabase<'opt> {
    optimize: &'opt Optimize,
    z3_ast: IndexVec<Var, Bool>,
    source_sink_emissions: usize,
    /// One selector literal per `source` (malloc) ownership assertion. The owning
    /// is asserted as `selector ⇒ owning`; assuming all selectors reproduces the
    /// hard source, while the relax loop can drop a selector to leak that source.
    source_selectors: Vec<Bool>,
}

impl<'opt> BoOwnDatabase<'opt> {
    pub(crate) fn new(optimize: &'opt Optimize) -> Self {
        let mut z3_ast = IndexVec::with_capacity(100);
        z3_ast.push(Bool::fresh_const("own_dummy"));
        BoOwnDatabase {
            optimize,
            z3_ast,
            source_sink_emissions: 0,
            source_selectors: Vec::new(),
        }
    }

    pub(crate) fn z3_ast_len(&self) -> usize {
        self.z3_ast.len()
    }

    pub(crate) fn source_sink_emissions(&self) -> usize {
        self.source_sink_emissions
    }

    /// The per-version ownership Bool for `var` (for solidification linking).
    pub(crate) fn own_bool(&self, var: Var) -> &Bool {
        &self.z3_ast[var]
    }

    /// Selector literals for the emitted `source` ownerships. Assume all of them
    /// to reproduce the hard source; the relax loop drops some on UNSAT.
    pub(crate) fn source_selectors(&self) -> &[Bool] {
        &self.source_selectors
    }
}

impl Database for BoOwnDatabase<'_> {
    fn new_vars(&mut self, var_gen: &mut Gen, size: u32) -> Range<Var> {
        let sigs = var_gen.new_sigs(size);
        for sig in sigs.clone() {
            assert_eq!(sig, self.z3_ast.push(Bool::fresh_const("own")));
        }
        sigs
    }

    fn push_linear_impl(&mut self, x: Var, y: Var, z: Var) {
        let [x, y, z] = [x, y, z].map(|sig| &self.z3_ast[sig]);
        let clause = Bool::or(&[&!x, &!y]);
        self.optimize.assert(&clause);
        let clause = Bool::or(&[&!x, z]);
        self.optimize.assert(&clause);
        let clause = Bool::or(&[x, y, &!z]);
        self.optimize.assert(&clause);
        let clause = Bool::or(&[&!y, z]);
        self.optimize.assert(&clause);
    }

    fn push_assume_impl(&mut self, x: Var, sign: bool) {
        let x = &self.z3_ast[x];
        let value = Bool::from_bool(sign);
        let clause = !(x.xor(&value));
        self.optimize.assert(&clause);
    }

    fn push_equal_impl(&mut self, x: Var, y: Var) {
        let [x, y] = [x, y].map(|sig| &self.z3_ast[sig]);
        let clause = !(x.xor(y));
        self.optimize.assert(&clause);
    }

    fn push_less_equal_impl(&mut self, x: Var, y: Var) {
        let [x, y] = [x, y].map(|sig| &self.z3_ast[sig]);
        let clause = Bool::or(&[&!x, y]);
        self.optimize.assert(&clause);
    }

    fn push_eq_min_impl(&mut self, x: Var, y: Var, z: Var) {
        let [x, y, z] = [x, y, z].map(|sig| &self.z3_ast[sig]);
        let clause = Bool::or(&[&!x, y]);
        self.optimize.assert(&clause);
        let clause = Bool::or(&[&!x, z]);
        self.optimize.assert(&clause);
        let clause = Bool::or(&[x, &!y, &!z]);
        self.optimize.assert(&clause);
    }

    fn record_source_sink(&mut self) {
        self.source_sink_emissions += 1;
    }

    fn push_source_owning(&mut self, var: Var) {
        // Gate the owning behind a fresh selector: `selector ⇒ owning`.
        // Assuming the selector forces owning (the hard source); the relax loop
        // can drop the selector to leak this allocation instead. The selector
        // shares `self.optimize`'s thread-local z3 context (single-threaded
        // analysis), so it matches the literal `get_unsat_core` returns.
        let selector = Bool::fresh_const("src_sel");
        let not_sel = !&selector;
        let clause = Bool::or(&[&not_sel, &self.z3_ast[var]]);
        self.optimize.assert(&clause);
        self.source_selectors.push(selector);
    }
}
