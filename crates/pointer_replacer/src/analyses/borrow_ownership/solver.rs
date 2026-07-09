use std::cell::RefCell;
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

/// §NB-R — opt-in tracked-core diagnostic. When a `KindSolver` is built via
/// `new_tracked`, every HARD constraint is asserted as `track ⇒ constraint`
/// with a fresh track literal recorded here alongside a human-readable label
/// (`{context}::{family}(…)`). Solving `check(&[tracks ∪ source selectors])`
/// then yields, on UNSAT, a core whose literals map back to labeled emission
/// sites — the tool that turns the corpus's opaque `unsat-nonsource` declines
/// into a named contradicting constraint set. Soft asserts (the Ref≻Raw
/// objective) are never tracked; `push_source_owning`'s selectors stay their
/// own (retractable) assumption class and are never double-gated.
///
/// A tracked solver is meaningful ONLY under assumption-solving: its hard
/// constraints are vacuously satisfiable without the tracks. The production
/// solve paths (`model_kinds`, `model_kinds_relaxing`, `verify_to_fixpoint`)
/// carry release-active guards refusing tracked instances.
pub(crate) struct CoreTracker {
    entries: RefCell<Vec<(Bool, String)>>,
    context: RefCell<String>,
}

impl CoreTracker {
    fn new() -> Self {
        CoreTracker {
            entries: RefCell::new(Vec::new()),
            context: RefCell::new(String::from("init")),
        }
    }

    /// Set the provenance context (e.g. the fn being emitted, or the
    /// construction phase) prefixed onto subsequent labels.
    pub(crate) fn set_context(&self, context: &str) {
        *self.context.borrow_mut() = context.to_string();
    }

    /// Mint a fresh track literal for one hard constraint and record its label.
    fn record(&self, label: String) -> Bool {
        let track = Bool::fresh_const("nbr_track");
        self.entries
            .borrow_mut()
            .push((track.clone(), format!("{}::{}", self.context.borrow(), label)));
        track
    }

    /// All track literals, for `check(&assumptions)`.
    pub(crate) fn tracks(&self) -> Vec<Bool> {
        self.entries
            .borrow()
            .iter()
            .map(|(track, _)| track.clone())
            .collect()
    }

    /// Label of a core literal (z3 node identity, valid on the shared
    /// thread-local context — same basis as `model_kinds_relaxing`'s
    /// selector matching).
    pub(crate) fn label_of(&self, literal: &Bool) -> Option<String> {
        self.entries
            .borrow()
            .iter()
            .find(|(track, _)| track == literal)
            .map(|(_, label)| label.clone())
    }
}

/// The label families `CoreTracker` emits — the parse contract for the
/// mechanism test and the corpus histogram. Kept in one place so a new
/// emission site cannot invent an unlisted family silently.
pub(crate) const CORE_LABEL_FAMILIES: &[&str] = &[
    "kind-pin",
    "kind-equate",
    // NOTE: matching is first-containment (`family_of`), so the longer
    // "field-and-rev" MUST precede its prefix "field-and".
    "field-and-rev",
    "field-and",
    "field-forbid",
    "link-own",
    "borrow-exclusion",
    "one-hot",
    // §NB1 per-site safety monotonicity (no substring overlap with the others).
    "safe-mono",
    "i1-adjacency",
    "own-linear",
    "own-assume",
    "own-equal",
    "own-le",
    "own-eqmin",
    "source-selector",
    // §NB-F: free/realloc sink selectors (no substring overlap with
    // "source-selector" — first-containment matching stays unambiguous).
    "sink-selector",
];

pub struct KindSolver {
    solver: Optimize,
    vars: FxHashMap<SlotRef, KindVars>,
    tracker: Option<CoreTracker>,
}

impl KindSolver {
    pub fn new(slots: &CrateSlots) -> Self {
        Self::build(slots, None)
    }

    /// §NB-R diagnostic constructor: every hard constraint is track-gated.
    /// The result must ONLY be driven via assumption solving (see
    /// `CoreTracker`); production solve paths refuse it.
    pub(crate) fn new_tracked(slots: &CrateSlots) -> Self {
        Self::build(slots, Some(CoreTracker::new()))
    }

    pub(crate) fn tracker(&self) -> Option<&CoreTracker> {
        self.tracker.as_ref()
    }

    fn build(slots: &CrateSlots, tracker: Option<CoreTracker>) -> Self {
        let solver = Optimize::new();
        let mut vars = FxHashMap::default();

        add_universe(
            &solver,
            tracker.as_ref(),
            &mut vars,
            &slots.field_slots,
            SlotRef::Field,
        );
        for (&fn_did, universe) in &slots.fn_local_slots {
            add_universe(&solver, tracker.as_ref(), &mut vars, universe, |slot| {
                SlotRef::Local(fn_did, slot)
            });
        }

        // Prefer Ref where hard constraints allow it, then Raw over unnecessary Owning.
        let big = vars.len() as u64 + 1;
        for kind_vars in vars.values() {
            solver.assert_soft(&kind_vars.ref_, big, None);
            solver.assert_soft(&kind_vars.raw, 1u64, None);
        }

        KindSolver {
            solver,
            vars,
            tracker,
        }
    }

    pub fn assume(&self, slot: SlotRef, kind: SlotKind) {
        let vars = self
            .vars
            .get(&slot)
            .unwrap_or_else(|| panic!("unknown slot: {slot:?}"));
        let bit = match kind {
            SlotKind::Raw => &vars.raw,
            SlotKind::Ref => &vars.ref_,
            SlotKind::Owning => &vars.own,
        };
        assert_hard(
            &self.solver,
            self.tracker.as_ref(),
            || format!("kind-pin({slot:?},{kind:?})"),
            bit,
        );
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
        let tracker = self.tracker.as_ref();
        assert_hard(
            &self.solver,
            tracker,
            || format!("kind-equate({a:?},{b:?},raw)"),
            &!va.raw.xor(&vb.raw),
        );
        assert_hard(
            &self.solver,
            tracker,
            || format!("kind-equate({a:?},{b:?},ref)"),
            &!va.ref_.xor(&vb.ref_),
        );
        assert_hard(
            &self.solver,
            tracker,
            || format!("kind-equate({a:?},{b:?},own)"),
            &!va.own.xor(&vb.own),
        );
    }

    /// §9.10.2 field-ownership constraint: a struct field slot is one crate-wide slot that
    /// (flow-insensitively) holds EVERY value stored into the field. It may be `Owning` — the
    /// rewriter would `Box`/free it — ONLY if every stored value is itself owned; if any store
    /// is a borrowed value the field must not be `Owning` (else it would free borrowed memory
    /// -> UAF). This asserts `field.own <=> AND(rhs.own)` over the field's stores, using BO's
    /// OWN ownership verdict for each `rhs` (so interprocedural / wrapper-returned allocations
    /// and borrowed returns are handled with no syntactic detection). Unlike a plain `equate`
    /// per store, it does NOT transitively equate the stored values to each other, so an owned
    /// source stored in one function does not drag a borrowed value stored in another to
    /// `Owning`. Empty `rhs` is a no-op (an AND over no stores is vacuously true and must not
    /// force `Owning`). Touches only the ownership bit; the borrow reading is left to the
    /// borrow constraints.
    pub(crate) fn constrain_field_own(&self, field: SlotRef, rhs: &[SlotRef]) {
        if rhs.is_empty() {
            return;
        }
        let field_own = &self
            .vars
            .get(&field)
            .unwrap_or_else(|| panic!("unknown slot: {field:?}"))
            .own;
        let rhs_own: Vec<&Bool> = rhs
            .iter()
            .map(|r| {
                &self
                    .vars
                    .get(r)
                    .unwrap_or_else(|| panic!("unknown slot: {r:?}"))
                    .own
            })
            .collect();
        // field.own => rhs_i.own for each store (freeing requires every stored value owned).
        for (slot, r) in rhs.iter().zip(&rhs_own) {
            assert_hard(
                &self.solver,
                self.tracker.as_ref(),
                || format!("field-and({field:?}=>{slot:?})"),
                &Bool::or(&[&!field_own, r]),
            );
        }
        // AND(rhs.own) => field.own : `field.own OR (OR ¬rhs_i.own)`.
        let negs: Vec<Bool> = rhs_own.iter().map(|&r| !r).collect();
        let mut clause: Vec<&Bool> = vec![field_own];
        clause.extend(negs.iter());
        assert_hard(
            &self.solver,
            self.tracker.as_ref(),
            || format!("field-and-rev({field:?})"),
            &Bool::or(&clause),
        );
    }

    /// §9.10.2 companion to `constrain_field_own`: hard-assert a field slot is NOT `Owning`.
    /// Used when a field receives a value that is definitely not an owned heap allocation — an
    /// address-of (`Ref`/`RawPtr`) store, or a store whose RHS cannot be resolved to a slot
    /// (so its ownership is unknown). Such a store means the field can hold non-owned memory,
    /// so it must never be `Owning` (freeing it would be UAF). Conservative and sound: an
    /// unresolved/address store BLOCKS ownership rather than being silently dropped from the
    /// `AND` (which would wrongly permit `Owning`).
    pub(crate) fn forbid_field_own(&self, field: SlotRef) {
        let vars = self
            .vars
            .get(&field)
            .unwrap_or_else(|| panic!("unknown slot: {field:?}"));
        assert_hard(
            &self.solver,
            self.tracker.as_ref(),
            || format!("field-forbid({field:?})"),
            &!&vars.own,
        );
    }

    /// Solidification link: tie a slot's `own` one-hot bit to an external Bool
    /// (the disjunction of the slot's per-version ownership Bools). Mirrors the
    /// biconditional idiom in `equate`.
    pub(crate) fn link_own(&self, slot: SlotRef, external: &Bool) {
        let vars = self
            .vars
            .get(&slot)
            .unwrap_or_else(|| panic!("unknown slot: {slot:?}"));
        assert_hard(
            &self.solver,
            self.tracker.as_ref(),
            || format!("link-own({slot:?})"),
            &!vars.own.xor(external),
        );
    }

    /// §NB1 SAFE-MONO clause: `safe(target) ⇒ safe(layer)` — a safe (`¬raw`)
    /// target cannot sit behind a raw pointer `layer` that was dereferenced to
    /// reach it. `safe(x) ≡ ¬raw(x)` (one-hot), so this is `raw(target) ∨
    /// ¬raw(layer)`, a hard clause over the two slots' `raw` bits. It is
    /// `¬safe`-only: it can only push a slot toward `raw`, never force
    /// `ref`/`own` (theorems-doc invariant 7). `target` and `layer` are always
    /// distinct slots (the target is never among the layers dereferenced to
    /// reach it).
    pub(crate) fn safe_mono(&self, target: SlotRef, layer: SlotRef) {
        let t = self
            .vars
            .get(&target)
            .unwrap_or_else(|| panic!("unknown slot: {target:?}"));
        let l = self
            .vars
            .get(&layer)
            .unwrap_or_else(|| panic!("unknown slot: {layer:?}"));
        assert_hard(
            &self.solver,
            self.tracker.as_ref(),
            || format!("safe-mono({target:?}=>{layer:?})"),
            &Bool::or(&[&t.raw, &!&l.raw]),
        );
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
    ///
    /// BB2-ii's Mode-A loop also calls this with a *single* slot
    /// (`add_borrow_exclusion(Some(slot), &[])`) to commit a monotone `¬ref(slot)` —
    /// the one-literal degenerate case of the same exclusion clause.
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
        assert_hard(
            &self.solver,
            self.tracker.as_ref(),
            || format!("borrow-exclusion({issuer:?},{requirers:?})"),
            &Bool::or(&refs),
        );
    }

    pub fn check(&self) -> SatResult {
        // §NB-R guard: a no-assumption check on a tracked solver is vacuously
        // SAT (all hard constraints are track-gated) — refuse, like the other
        // production solve paths.
        assert!(
            self.tracker.is_none(),
            "tracked KindSolver must not enter check() (constraints are track-gated)"
        );
        self.solver.check(&[])
    }

    pub(crate) fn optimize(&self) -> &Optimize {
        &self.solver
    }

    pub fn model_kinds(&self) -> Option<FxHashMap<SlotRef, SlotKind>> {
        // §NB-R guard (release-active, BB3-c style): a tracked solver's hard
        // constraints are `track ⇒ c` — without the tracks assumed they are
        // vacuously satisfiable, so this path would return a silently wrong
        // model instead of an error.
        assert!(
            self.tracker.is_none(),
            "tracked KindSolver must not enter model_kinds (constraints are track-gated)"
        );
        if self.check() != SatResult::Sat {
            return None;
        }
        let model = self.solver.get_model()?;
        Some(self.read_kinds(&model))
    }

    /// Solve assuming all of `selectors` (reproducing the hard sources and
    /// sinks). On UNSAT, leak a **subset-minimal** set of conflicting
    /// selectors (phase 2 proves no leaked selector is individually
    /// restorable) and return the resulting per-slot kinds, or `None` if the
    /// system is UNSAT for non-selector reasons. Subset-minimal is NOT
    /// minimum-cardinality: the §S2-1 sinks-first policy deliberately retains
    /// a source even where leaking it alone would have been fewer total
    /// leaks (a source's Owning conversion outweighs leaked frees —
    /// `nbs2_mixed_fanout_prefers_source_over_two_sinks` pins the trade).
    ///
    /// All z3 Bools share the single thread-local context (the analysis is
    /// single-threaded), so `c == s` is `Z3_is_eq_ast` node identity — valid
    /// because `Bool::clone` shares the `Z3_ast` pointer and `get_unsat_core`
    /// returns the original assumption literals.
    ///
    /// Terminates: phase 1 drops one of finitely many selectors per UNSAT round;
    /// phase 2 visits each dropped selector once. Leaking a source classifies
    /// that allocation non-Owning, which is memory-safe; leaking a sink leaves
    /// an unprovable free a raw-pointer free.
    pub(crate) fn model_kinds_relaxing(
        &self,
        selectors: &Selectors,
    ) -> Option<FxHashMap<SlotRef, SlotKind>> {
        self.model_kinds_relaxing_reporting(selectors)
            .map(|(kinds, _dropped)| kinds)
    }

    /// §NB-F reporting twin of `model_kinds_relaxing`: also returns WHICH
    /// selectors were dropped (leaked sources and/or leaked sinks — classify
    /// via `Selectors`). Same semantics; the plain fn delegates here.
    pub(crate) fn model_kinds_relaxing_reporting(
        &self,
        selectors: &Selectors,
    ) -> Option<(FxHashMap<SlotRef, SlotKind>, Vec<Bool>)> {
        // §NB-R guard (release-active): under tracking, this loop's unsat-core
        // search would see foreign track literals in cores and its selector
        // matching would silently misbehave. Tracked instances are driven only
        // by the explain path.
        assert!(
            self.tracker.is_none(),
            "tracked KindSolver must not enter model_kinds_relaxing (constraints are track-gated)"
        );
        let mut assumptions: Vec<Bool> = selectors.all().to_vec();
        let mut leaked: Vec<Bool> = Vec::new();

        // Phase 1: drop conflicting selectors until SAT (or give up).
        loop {
            match self.solver.check(&assumptions) {
                SatResult::Sat => break,
                SatResult::Unsat => {
                    let core = self.solver.get_unsat_core();
                    let in_core = |s: &Bool| core.iter().any(|c| c == s);
                    // §S2-1 (NB-F review F2): the drop choice on a MIXED
                    // source/sink core is a deliberate policy — drop sinks
                    // first, retain sources. A leaked sink costs a leak (the
                    // free stays a raw-pointer free); a leaked source costs
                    // Owning-conversion precision (D7's driver). On a true
                    // either/or tie phase 2 cannot undo the choice, so it must
                    // be made here. Within a class, and on cores with no sink
                    // at all, the pick stays positional — the pre-S2-1
                    // behavior exactly.
                    let idx = assumptions
                        .iter()
                        .position(|s| selectors.is_sink(s) && in_core(s))
                        .or_else(|| assumptions.iter().position(|s| in_core(s)))?;
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
            SatResult::Sat => Some((self.read_kinds(&self.solver.get_model()?), leaked)),
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
    tracker: Option<&CoreTracker>,
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

        let sref = slot_ref(id);
        assert_exactly_one(solver, tracker, sref, &kind_vars);
        vars.insert(sref, kind_vars);
    }

    // §NB1: the structural `i1-adjacency` chain clause. Emitted under `Chain`
    // AND `PerSite`, skipped only under `Off`. It is NOT redundant under
    // `PerSite`: the per-site SAFE-MONO walk fires only on READ/borrow sites
    // (write destinations excluded — `safety_mono`), so this clause is what
    // still covers write-only and never-dereferenced same-owner chains. It
    // stays under `PerSite` PERMANENTLY (the NB-plan's "delete after subsumption"
    // is resolved the other way). Ablation stays clean: `Chain` = this clause
    // only; `PerSite` = this clause + the read-site walk. See `SafeMonoMode`.
    if super::SafeMonoMode::current() == super::SafeMonoMode::Off {
        return;
    }
    for i in 0..universe.len().saturating_sub(1) {
        let a = SlotId::from_usize(i);
        let b = SlotId::from_usize(i + 1);
        if universe.slot(a).owner == universe.slot(b).owner {
            let sref_a = slot_ref(a);
            let sref_b = slot_ref(b);
            let a_vars = vars
                .get(&sref_a)
                .unwrap_or_else(|| panic!("missing solver vars for slot {a:?}"));
            let b_vars = vars
                .get(&sref_b)
                .unwrap_or_else(|| panic!("missing solver vars for slot {b:?}"));
            assert_not_both(
                solver,
                tracker,
                || format!("i1-adjacency({sref_a:?},{sref_b:?})"),
                &a_vars.raw,
                &b_vars.own,
            );
        }
    }
}

fn assert_exactly_one(
    solver: &Optimize,
    tracker: Option<&CoreTracker>,
    slot: SlotRef,
    vars: &KindVars,
) {
    assert_hard(
        solver,
        tracker,
        || format!("one-hot({slot:?},exists)"),
        &Bool::or(&[&vars.raw, &vars.ref_, &vars.own]),
    );
    assert_not_both(
        solver,
        tracker,
        || format!("one-hot({slot:?},raw-ref)"),
        &vars.raw,
        &vars.ref_,
    );
    assert_not_both(
        solver,
        tracker,
        || format!("one-hot({slot:?},raw-own)"),
        &vars.raw,
        &vars.own,
    );
    assert_not_both(
        solver,
        tracker,
        || format!("one-hot({slot:?},ref-own)"),
        &vars.ref_,
        &vars.own,
    );
}

fn assert_not_both(
    solver: &Optimize,
    tracker: Option<&CoreTracker>,
    label: impl FnOnce() -> String,
    a: &Bool,
    b: &Bool,
) {
    assert_hard(solver, tracker, label, &Bool::or(&[&!a, &!b]));
}

/// §NB-R — the single hard-assert choke point. Untracked: byte-identical to a
/// plain `assert` (the label closure is never evaluated). Tracked: assert
/// `track ⇒ constraint` and record the labeled track literal.
fn assert_hard(
    solver: &Optimize,
    tracker: Option<&CoreTracker>,
    label: impl FnOnce() -> String,
    constraint: &Bool,
) {
    match tracker {
        None => solver.assert(constraint),
        Some(tracker) => {
            let track = tracker.record(label());
            solver.assert(&Bool::or(&[&!&track, constraint]));
        }
    }
}

fn is_true(model: &Model, b: &Bool) -> bool {
    model
        .eval(b, true)
        .and_then(|value| value.as_bool())
        .unwrap_or(false)
}

pub(crate) struct BoOwnDatabase<'opt> {
    optimize: &'opt Optimize,
    /// §NB-R: present iff the owning `KindSolver` is tracked; every hard
    /// constraint pushed here is then track-gated with an `own-*` family
    /// label (`push_source_owning` excepted — its selectors are already
    /// their own retractable assumption class).
    tracker: Option<&'opt CoreTracker>,
    z3_ast: IndexVec<Var, Bool>,
    source_sink_emissions: usize,
    /// One selector literal per `source` (malloc) ownership assertion. The owning
    /// is asserted as `selector ⇒ owning`; assuming all selectors reproduces the
    /// hard source, while the relax loop can drop a selector to leak that source.
    source_selectors: Vec<Bool>,
    /// §NB-F: one selector per `sink` (free/realloc arg) ownership assertion —
    /// the sink twin of `source_selectors`. Dropping one LEAKS THE FREE (the
    /// freed value's owning is no longer forced; nothing asserts ¬own/¬ref).
    sink_selectors: Vec<Bool>,
}

impl<'opt> BoOwnDatabase<'opt> {
    pub(crate) fn new(optimize: &'opt Optimize, tracker: Option<&'opt CoreTracker>) -> Self {
        let mut z3_ast = IndexVec::with_capacity(100);
        z3_ast.push(Bool::fresh_const("own_dummy"));
        BoOwnDatabase {
            optimize,
            tracker,
            z3_ast,
            source_sink_emissions: 0,
            source_selectors: Vec::new(),
            sink_selectors: Vec::new(),
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

    /// §NB-F: selector literals for the emitted `sink` ownerships.
    pub(crate) fn sink_selectors(&self) -> &[Bool] {
        &self.sink_selectors
    }
}

/// §NB-F: the retractable-assumption set emission returns — malloc SOURCE
/// selectors plus free/realloc SINK selectors. Stored combined (`all` is what
/// `verify_to_fixpoint`/`model_kinds_relaxing` consume) with a typed split so
/// no caller has to remember an ordering convention.
pub(crate) struct Selectors {
    all: Vec<Bool>,
    n_sources: usize,
}

impl Selectors {
    pub(crate) fn new(sources: Vec<Bool>, sinks: Vec<Bool>) -> Self {
        let n_sources = sources.len();
        let mut all = sources;
        all.extend(sinks);
        Selectors { all, n_sources }
    }

    pub(crate) fn all(&self) -> &[Bool] {
        &self.all
    }

    pub(crate) fn sources(&self) -> &[Bool] {
        &self.all[..self.n_sources]
    }

    pub(crate) fn sinks(&self) -> &[Bool] {
        &self.all[self.n_sources..]
    }

    /// Whether a (core/dropped) literal is a sink selector — z3 node identity,
    /// same basis as the relax loop's selector matching.
    pub(crate) fn is_sink(&self, literal: &Bool) -> bool {
        self.sinks().iter().any(|s| s == literal)
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
        let label = || format!("own-linear({x:?}+{y:?}={z:?})");
        let [x, y, z] = [x, y, z].map(|sig| &self.z3_ast[sig]);
        assert_hard(self.optimize, self.tracker, label, &Bool::or(&[&!x, &!y]));
        assert_hard(self.optimize, self.tracker, label, &Bool::or(&[&!x, z]));
        assert_hard(self.optimize, self.tracker, label, &Bool::or(&[x, y, &!z]));
        assert_hard(self.optimize, self.tracker, label, &Bool::or(&[&!y, z]));
    }

    fn push_assume_impl(&mut self, x: Var, sign: bool) {
        let label = || format!("own-assume({x:?}={sign})");
        let x = &self.z3_ast[x];
        let value = Bool::from_bool(sign);
        assert_hard(self.optimize, self.tracker, label, &!(x.xor(&value)));
    }

    fn push_equal_impl(&mut self, x: Var, y: Var) {
        let label = || format!("own-equal({x:?},{y:?})");
        let [x, y] = [x, y].map(|sig| &self.z3_ast[sig]);
        assert_hard(self.optimize, self.tracker, label, &!(x.xor(y)));
    }

    fn push_less_equal_impl(&mut self, x: Var, y: Var) {
        let label = || format!("own-le({x:?}<={y:?})");
        let [x, y] = [x, y].map(|sig| &self.z3_ast[sig]);
        assert_hard(self.optimize, self.tracker, label, &Bool::or(&[&!x, y]));
    }

    fn push_eq_min_impl(&mut self, x: Var, y: Var, z: Var) {
        let label = || format!("own-eqmin({x:?}=min({y:?},{z:?}))");
        let [x, y, z] = [x, y, z].map(|sig| &self.z3_ast[sig]);
        assert_hard(self.optimize, self.tracker, label, &Bool::or(&[&!x, y]));
        assert_hard(self.optimize, self.tracker, label, &Bool::or(&[&!x, z]));
        assert_hard(self.optimize, self.tracker, label, &Bool::or(&[x, &!y, &!z]));
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

    fn push_sink_owning(&mut self, var: Var) {
        // §NB-F: `selector ⇒ owning`, the sink twin of `push_source_owning` —
        // the relax loop may drop the selector to LEAK THE FREE (decline
        // becomes leak; the freed value's owning is then unconstrained: no
        // ¬own/¬ref is asserted — there is deliberately no sink analogue of
        // NB0's eager ¬ref(source)). Like source selectors, never track-gated
        // (selectors are their own assumption class).
        let selector = Bool::fresh_const("sink_sel");
        let not_sel = !&selector;
        let clause = Bool::or(&[&not_sel, &self.z3_ast[var]]);
        self.optimize.assert(&clause);
        self.sink_selectors.push(selector);
    }
}
