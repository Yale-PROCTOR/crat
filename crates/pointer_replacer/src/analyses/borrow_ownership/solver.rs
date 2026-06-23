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
        let mut kinds = FxHashMap::default();
        kinds.reserve(self.vars.len());

        for (&slot, vars) in &self.vars {
            let kind = if is_true(&model, &vars.own) {
                SlotKind::Owning
            } else if is_true(&model, &vars.ref_) {
                SlotKind::Ref
            } else {
                SlotKind::Raw
            };
            kinds.insert(slot, kind);
        }

        Some(kinds)
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
}

impl<'opt> BoOwnDatabase<'opt> {
    pub(crate) fn new(optimize: &'opt Optimize) -> Self {
        let mut z3_ast = IndexVec::with_capacity(100);
        z3_ast.push(Bool::fresh_const("own_dummy"));
        BoOwnDatabase {
            optimize,
            z3_ast,
            source_sink_emissions: 0,
        }
    }

    pub(crate) fn z3_ast_len(&self) -> usize {
        self.z3_ast.len()
    }

    pub(crate) fn source_sink_emissions(&self) -> usize {
        self.source_sink_emissions
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
}
