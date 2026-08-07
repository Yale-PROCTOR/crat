//! **Phase 1 — decision.** Analysis in, decision table out. No AST mutation.
//!
//! Everything that reads BO output or an auxiliary analysis happens here and
//! nowhere else. The table this phase produces is **immutable and complete
//! before any edit is planned**: A1 emitability, A2 degradation closure, and
//! the owning-reachable fixpoint all live here, so no later phase ever has to
//! ask an analysis a question.
//!
//! # E1 state visibility
//!
//! This phase may read `crate::analyses::*` (read-only, §2 precedence rule) and
//! the `BoExport`. It hands [`super::plan`] a finished table by value. It holds
//! no back-pointer to a later phase, and no later phase holds one to it.
//!
//! # Status
//!
//! S1 lands the **G01 arm only**: depth-0 pointer *parameters* whose BO kind is
//! `Ref`. Every other subject degrades with a named reason — the channel S2's
//! envelope-demotion counters aggregate. A2's degradation closure and the
//! owning-reachable fixpoint arrive with S2's breadth.

use rustc_hash::FxHashMap;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{mir::Local, ty::TyCtxt};
use rustc_span::Span;

use crate::analyses::borrow_ownership::{SlotKind, crate_slots::CrateSlots, solver::SlotRef};

pub(crate) mod construction;
pub(crate) mod emitability;
pub(crate) mod universe;

use emitability::EmitabilityFacts;

/// How the parameter's **declaration** is written in source, for a subject
/// whose **resolved** type is a pointer.
///
/// The two can disagree, and that disagreement is the whole reason subject
/// collection moved to resolved types: a C2Rust alias
/// (`pub type lil_value_t = *mut _lil_value_t`) is a pointer parameter that
/// *reads* as a path. Under R-A such parameters are collected — they are real C
/// pointer parameters and excluding them would shrink the universe artificially
/// — and the shape is carried so that an emission obstacle specific to the
/// shape can be attributed with its own reason instead of vanishing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DeclShape {
    /// `*mut T` / `*const T`, written literally. The only emittable shape at M1.
    RawPtr,
    /// A path that resolves to a pointer — the C2Rust type-alias class.
    Alias,
    /// Already a reference in source.
    Reference,
    /// Resolved as a pointer through some other declaration form.
    Other,
}

impl DeclShape {
    fn key(self) -> &'static str {
        match self {
            DeclShape::RawPtr => "raw-ptr",
            DeclShape::Alias => "alias",
            DeclShape::Reference => "reference",
            DeclShape::Other => "other",
        }
    }
}

/// Which universe a [`Subject`] came from.
///
/// The two universes are **disjoint by construction**: parameters occupy MIR
/// locals `_1 ..= arg_count`, locals occupy `_(arg_count + 1) ..`. Nothing
/// reconciles them afterwards because nothing has to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SubjectKind {
    /// A pointer parameter. Carries its position in the HIR declaration,
    /// **0-based**, recorded as collected.
    ///
    /// Kept separate from [`Subject::local`] deliberately. The two coincide
    /// (`local == hir_index + 1`), but deriving the artifact's `arg_index`
    /// *from* the local would make it a restatement of the alignment key — and a
    /// pairing field that restates the key can never disagree with it. F1 is
    /// precisely what such a field looks like.
    Param { hir_index: usize },
    /// A named pointer local. **Has no argument position**, so the artifact's
    /// `arg_index` is `None` for it — which means *not a parameter*, never
    /// *unpaired*: `compare::pairing_agrees` compares that field by equality and
    /// nothing presence-tests it (S3.1 pre-flight, swept).
    Local,
}

/// One thing M1 must decide about: a pointer **parameter** or a named pointer
/// **local**.
///
/// Subjects and decisions are counted against each other by the structural gate
/// (`|decisions| == |subjects|`), so a subject that is silently skipped rather
/// than explicitly degraded fails the gate instead of vanishing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Subject {
    pub fn_did: LocalDefId,
    /// MIR local of the parameter: params are `_1 ..= arg_count`.
    pub local: Local,
    /// HIR binding of this subject, used to attribute uses to it without
    /// relying on a name that could be shadowed.
    ///
    /// **Must be the binding's real `HirId` — the one `Res::Local` resolves a
    /// use to.** The two A1 emitability gates key on `(fn_did, hir_id)`, so a
    /// placeholder here does not weaken them, it makes them *unreachable*: the
    /// lookup cannot hit and the subject sails past both checks. S3.1 shipped
    /// `CRATE_HIR_ID` for every local, and both gates were dead over that whole
    /// population — 0 of 3,142 locals stopped, against 1,231 of 4,306
    /// parameters. `production_subjects_carry_a_real_hir_binding` bans the
    /// placeholder in production source so the next population cannot repeat it.
    ///
    /// Said the other way: this field is not describable as "a parameter's".
    /// The doc that said so predated the locals universe and read as true while
    /// half the population carried a placeholder.
    pub hir_id: rustc_hir::HirId,
    /// **Pairing term 1** in the reconciliation artifact: the parameter's
    /// source name. `None` when the pattern is not a plain binding.
    pub param_name: Option<String>,
    /// Which universe this subject came from — and, for a parameter, **pairing
    /// term 2**.
    ///
    /// **An enum rather than `Option<usize>`, deliberately (S3.1).** The
    /// artifact's `arg_index` derivation matches on this, so adding the locals
    /// kind made every consumer a compile error until it said what it meant.
    /// An `Option` would have let a consumer write `unwrap_or(0)` and compile —
    /// the same silent-acceptance shape S3.0 removed from the `Decision`
    /// consumers.
    pub kind: SubjectKind,
    /// Pointer-chain depth of the RESOLVED subject type.
    pub ptr_depth: u8,
    /// Human-readable identity for attribution: `fn_name::param_name`.
    pub label: String,
    /// Source span of the subject's declared **type** — the splice target.
    ///
    /// **`None` when there is no declared type**, which S3.1 makes reachable:
    /// `let p = malloc(4) as *mut i32;` has no annotation, and a
    /// tuple-destructuring `let (a, b): (…)` annotates the *pattern*, not its
    /// components (measured 2026-08-05: MIR reports per-binding spans while the
    /// HIR `let` carries one whole-pattern type). Such subjects degrade with
    /// [`DegradeReason::NoDeclaredType`]; nothing splices them.
    ///
    /// Kept distinct from [`Self::binding_span`] because they mean different
    /// things: this one is *where an edit would go*, that one is *where the
    /// subject is*. Using the binding span here would put a non-splice-target
    /// into the artifact's `decl_span_lo/hi`, whose doc says the audited number
    /// IS the edit target.
    pub ty_span: Option<Span>,
    /// Source span of the subject's **binding** — always present.
    ///
    /// Attribution only: it is what a site string renders when there is no
    /// declared type to point at. For a parameter this is the pattern; for a
    /// local it is the `var_debug_info` entry's span, which is exactly the HIR
    /// binding pattern's span (measured, including the `mut p` case).
    pub binding_span: Span,
    /// Source span of the pointee type, kept so the plan can preserve the
    /// pointee's text verbatim rather than re-render it.
    ///
    /// `None` when the declaration is not a syntactic raw pointer: an alias
    /// carries its pointer-ness inside the alias, so there is no pointee text
    /// to copy. Such subjects are degraded in [`decide_one`], so a `Ref`
    /// decision always has a pointee span.
    pub pointee_span: Option<Span>,
    /// How the declaration is written — see [`DeclShape`].
    pub decl_shape: DeclShape,
    pub mutable: bool,
    /// **The freed-slot fact**: the span of the first deallocator call this
    /// subject's binding is passed to, or `None`.
    ///
    /// Stamped once, in `finish_decide`, over BOTH universes from a single
    /// [`super::free_sites`] walk — the same call the S2-2 census asks. One
    /// stamping site rather than one per collector, so the parameter and locals
    /// populations cannot acquire different freed-ness by construction, and one
    /// recognizer rather than two so the gate below and the census cannot
    /// disagree about what "freed" means.
    ///
    /// An `Option<Span>` rather than a `bool` + lookup: the predicate and the
    /// attribution site are the same fact, and splitting them is how a gate
    /// ends up degrading with a declaration site that says nothing about why.
    pub freed_at: Option<Span>,
    /// **U-2′** — did the construction-site recognizer recover a real length?
    ///
    /// Stamped alongside `freed_at`, from the same single pass. `false` is the
    /// approximation path, which U-2′ ratified as the PRIMARY one for borrowed
    /// forms (measured 2.8 % recoverable over the slice market), with this flag
    /// as the assumption-violation counter rather than a caveat.
    ///
    /// A parameter has no construction site in its own crate, so it reads
    /// `false` — *"this analysis did not recover a length"*, a statement about
    /// reach, never a claim about the program. Same rule as `param-no-site`.
    pub len_recovered: bool,
    /// **S3.2′-3** — is this binding CONSTRUCTED from a null literal?
    ///
    /// Stamped from the same construction pass as `len_recovered`. It is the
    /// second of the two in-force nullability signals (micro-plan §1): the
    /// first is a use-site `is_null`, this one is `0 as *mut T` at the
    /// initializer.
    ///
    /// A parameter has no construction site, so it reads `false` — reach, not a
    /// claim, the `param-no-site` rule again.
    pub null_init: bool,
    /// **S3.2′-3** — is the binding itself declared `mut`?
    ///
    /// A mutable optional with more than one use is accessed through
    /// `as_mut()`, and `as_mut()` takes `&mut self`. Without a `mut` binding
    /// that is `error[E0596]`, so the fact has to be available where the form is
    /// chosen rather than discovered by the verify loop.
    pub mut_binding: bool,
}

/// Bindings passed to a deallocator, keyed exactly as A1's emitability gates are
/// — `(owner, HirId)`.
///
/// Takes the resolved slice rather than the parent's `FreeSites` struct: this
/// phase needs the *fact*, not the recognizer's return type, and a narrower
/// surface is a narrower coupling.
#[derive(Default)]
pub(crate) struct FreedBindings(FxHashMap<(LocalDefId, rustc_hir::HirId), Span>);

impl FreedBindings {
    /// First site wins, so the attribution is deterministic under a program with
    /// several frees of one binding — `bst::deleteNode::_1` is freed twice on
    /// the corpus, and a last-wins rule would make the reported site depend on
    /// HIR walk order.
    pub(crate) fn from_resolved(resolved: &[(rustc_hir::HirId, bool, Span)]) -> Self {
        let mut map = FxHashMap::default();
        for (hir_id, _cast, span) in resolved {
            map.entry((hir_id.owner.def_id, *hir_id)).or_insert(*span);
        }
        Self(map)
    }

    pub(crate) fn site_of(&self, fn_did: LocalDefId, hir_id: rustc_hir::HirId) -> Option<Span> {
        self.0.get(&(fn_did, hir_id)).copied()
    }
}

impl Subject {
    /// **THE subject identity — one definition, three consumers.**
    ///
    /// `plan` stamps it into [`super::plan::Unplaceable::subject`], the driver
    /// rebuilds it to subtract unplaceable decisions from the emitted set, and
    /// it is the string rendering of the pair the artifact `Row` already keys
    /// by: `fn_path` + `mir_local` (`artifact/mod.rs`). Those three must agree
    /// or the accounting identity compares different populations, so there is
    /// one function rather than three `format!`s.
    ///
    /// **The identity is `owner` + `mir_local`. The name is carried for
    /// READABILITY and carries none of it.** Two subjects in one function can
    /// render the same name:
    ///
    /// - **today** — `fn anon(_: *mut i32, _: *mut i32)` gives both parameters
    ///   `param_name: None`, so a name-keyed identity renders `anon::<unnamed>`
    ///   twice. Measured: both reach `Decision::Ref`, so this is on the emitting
    ///   path, not a curiosity. With one of them unplaceable, the driver's
    ///   `contains` check then skips the OTHER — the emitted source shows the
    ///   rewrite while `emitted_count` reports 0, and
    ///   `emitted + degraded + unplaceable == rows` fails 1 ≠ 2. It has never
    ///   fired on the corpus only because `unplaceable == 0` there.
    /// - **S3.1** — locals may legitimately share a name: `let p = …; let p = …;`
    ///   binds two distinct locals, each with its own `var_debug_info` entry,
    ///   both named `p`.
    ///
    /// `Local::as_u32` rather than `Local`'s `Debug` so the rendering matches
    /// the artifact's `mir_local` exactly rather than approximately.
    /// The span a human-facing site string points at: the declared type when
    /// there is one, the binding otherwise. Never `None`, so attribution never
    /// degrades along with the type.
    pub(crate) fn attribution_span(&self) -> Span {
        self.ty_span.unwrap_or(self.binding_span)
    }

    pub(crate) fn identity_key(&self, owner: &str) -> String {
        format!(
            "{owner}::{}#{}",
            self.param_name.as_deref().unwrap_or("<unnamed>"),
            self.local.as_u32()
        )
    }
}

/// Why a subject was not emitted.
///
/// A typed reason rather than a string: the counters S2b aggregates need to
/// group by cause, and `CallSiteNotAdapted` in particular is **temporary** —
/// S3's call-site adaptation retires it, and a free-text reason would make that
/// transition invisible in the data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum DegradeReason {
    /// The verify loop took this subject's rewrite back after the emitted crate
    /// failed to type-check, and its own function was attributed the error.
    ///
    /// **Its own reason key so the accounting identity survives the loop:** a
    /// reverted subject moves from emitted to degraded, keeping
    /// `emitted_final + degraded == row count`. Folding it into an existing
    /// reason would make a loop-driven revert indistinguishable from a
    /// decision-phase degradation, which is a different thing entirely — the
    /// decision stands; only the emission was withdrawn.
    RevertedAfterVerifyFailure,
    /// BO decided the slot is a raw pointer; leaving the source alone is the
    /// decision, not a failure.
    KindRaw,
    /// BO decided owning; Box forms and the drop policy arrive in S3.
    KindOwning,
    /// The parameter is used in an operation that exists only on raw pointers.
    RawPointerOperation { op: String },
    /// The function is referenced in-crate — called, address-taken, or cast to
    /// a fn pointer — and use sites are not yet adapted. **Retired by S3.**
    CallSiteNotAdapted,
    /// The parameter is compared with `<`, `==`, … (F5).
    ///
    /// Blocking in both directions. The dangerous one is silent: the same
    /// expression compares ADDRESSES on raw pointers and POINTEES on
    /// references, so a rewritten bounds check type-checks, passes the gate,
    /// and inverts. Refusing here is the only place that catches it before a
    /// behavioral gate exists.
    PtrComparison,
    /// Structural: the subject has no depth-0 slot, or none in the model.
    NoSlot,
    /// The resolved parameter type is a pointer but the **declaration** is not
    /// a syntactic `*mut`/`*const` — the C2Rust alias class, or a parameter
    /// that is already a reference.
    ///
    /// **Renamed from `UnsupportedDeclShape` at S3.1** (register 4, reason honesty).
    /// The old name asserted the opposite of the truth for its largest
    /// population: a C2Rust alias declaration IS a pointer declaration, just not
    /// one M1 can splice. The new name is true of every shape it carries —
    /// `alias`, `reference`, `other` — and prejudges none of them.
    ///
    /// R-A: collect these, do not exclude them. They are real C pointer
    /// parameters, so excluding them would shrink the universe artificially;
    /// what they get instead is a decision and an attributed reason. Emitting
    /// *through* an alias is a separate design question — the alias already
    /// contains the `*mut`, so `&mut lil_value_t` would be wrong — and
    /// conflating it with the collection fix would repeat this milestone's
    /// pattern of bundling.
    UnsupportedDeclShape { shape: &'static str },
    /// The subject has **no declared type**, so there is no splice target.
    ///
    /// Locals only, and reachable two ways (both measured 2026-08-05):
    /// an unannotated `let p = malloc(4) as *mut i32;`, and a destructuring
    /// `let (a, b): (*mut i32, *mut i32)` whose annotation belongs to the
    /// PATTERN — MIR reports per-binding spans while the HIR `let` carries one
    /// whole-pattern type, so a component has no type of its own.
    ///
    /// A parameter always has a declared type, so this reason never appears on
    /// the parameter universe. A count of 0 means the locals universe is empty,
    /// not that the reason is inert.
    NoDeclaredType,
    /// **The freed-slot gate.** The subject's binding is passed to a
    /// deallocator, so emitting a reference form for it would hand codegen a
    /// reference to freed memory.
    ///
    /// # Why this is its own reason and fires LAST
    ///
    /// Backlog S2-2 recorded that a leaked free's value kind is *observed, not
    /// designed*: a freed slot can settle `Ref` in the model, and the census
    /// measured 44 such subjects on the derived corpus. None of them reaches
    /// `Decision::Ref` today — every one is stopped earlier, mostly by an
    /// `as`-cast on the free argument or by having no declared type. That is an
    /// **incidental** mitigation, not a discharge: it is a property of how
    /// C2Rust happens to spell `free`, and `lodepng_free` already shows the
    /// shape that survives it (`free(ptr)` with no cast, stopped only by
    /// `call-site-not-adapted` — which **S3 retires**).
    ///
    /// So the gate is placed **last**, immediately before the `Ref` return: it
    /// vetoes an emission nothing else stopped, and it displaces no existing
    /// attribution. That ordering is what makes it a zero-movement change on
    /// today's corpus and a live veto the moment S3 removes the reason that is
    /// carrying it.
    ///
    /// Never folded into [`Self::KindOwning`]. Those are different claims —
    /// "BO says this slot owns" versus "the program frees this binding" — and a
    /// freed subject whose kind is `Ref` is exactly the case that has neither
    /// name nor counter if they are merged.
    FreedSlot,
    /// The subject is a borrowed-slice candidate whose **uses** cannot all be
    /// rewritten — some occurrence is not `*p.offset(e)`.
    ///
    /// Blocking for the whole subject, never partially applied: `&[T]` changes
    /// the type at every occurrence, so rewriting the recognized uses and
    /// leaving the rest is an ill-typed crate rather than a partial win.
    SliceUseUnsupported,
    /// The subject is a borrowed-slice candidate but is a **local**, so a slice
    /// value would have to be CONSTRUCTED at its initializer.
    ///
    /// A parameter needs no construction — the caller supplies the slice, and on
    /// this market no in-crate caller exists (every subject is
    /// non-`referenced`). A local's initializer is a raw-pointer expression that
    /// would need `from_raw_parts` and a length, which is a different mechanism
    /// with a different soundness argument. Scoped out of this slice explicitly
    /// and counted, rather than attempted.
    SliceLocalConstruction,
    /// **S3.2′-3 — positive evidence of nullness, so no plain form may emit.**
    ///
    /// The binding is initialized from a null literal. `Option` would serve it,
    /// but only with the INITIALIZER rewritten to `None` — a construction-site
    /// edit this slice does not own — so the disposition is an attributed
    /// degrade.
    ///
    /// **Fires after every other gate, including the freed-slot veto**, so it
    /// can only ever convert a would-be emission. That bounds its transitions
    /// to the subjects that emit today, which is what the pre-registration
    /// counts.
    NullInit,
    /// An optional subject carries a use the wrapper has no image for.
    OptUseUnsupported,
    /// A LOCAL cannot take an optional form without its initializer rewritten.
    ///
    /// `let p: Option<&i32> = <a raw pointer expression>` is `E0308` whatever
    /// the uses do, so the blocker is the construction site and not the uses —
    /// the same shape as [`Self::SliceLocalConstruction`], and its own key
    /// because "slice" would misreport a thin optional.
    ///
    /// **Found by a fixture, not by the corpus**: every subject in this slice's
    /// measured market is a parameter, so the corpus could not have exercised
    /// this arm at all.
    OptLocalConstruction,
    /// A mutable optional subject with more than one use needs `as_mut()`, and
    /// `as_mut()` needs a `mut` binding this declaration does not have.
    ///
    /// Its own key rather than folded into `OptUseUnsupported`: the blocker is
    /// the *binding mode*, one edit away, where a genuinely unsupported use is
    /// a missing capability. Two different owed items must not read as one.
    OptNeedsMutBinding,
}

impl DegradeReason {
    /// Stable key for counter aggregation (S2b).
    #[allow(
        dead_code,
        reason = "the aggregation that consumes this is S2b, the next slice. \
                  Targeted rather than module-wide so the lint keeps working \
                  everywhere else."
    )]
    pub(crate) fn key(&self) -> &'static str {
        match self {
            DegradeReason::RevertedAfterVerifyFailure => "reverted-after-verify-failure",
            DegradeReason::KindRaw => "kind-raw",
            DegradeReason::KindOwning => "kind-owning",
            DegradeReason::RawPointerOperation { .. } => "raw-pointer-operation",
            DegradeReason::CallSiteNotAdapted => "call-site-not-adapted",
            DegradeReason::PtrComparison => "ptr-comparison",
            DegradeReason::NoSlot => "no-slot",
            DegradeReason::UnsupportedDeclShape { .. } => "unsupported-decl-shape",
            DegradeReason::NoDeclaredType => "no-declared-type",
            DegradeReason::FreedSlot => "freed-slot",
            DegradeReason::SliceUseUnsupported => "slice-use-unsupported",
            DegradeReason::SliceLocalConstruction => "slice-local-construction",
            DegradeReason::NullInit => "null-init",
            DegradeReason::OptUseUnsupported => "opt-use-unsupported",
            DegradeReason::OptLocalConstruction => "opt-local-construction",
            DegradeReason::OptNeedsMutBinding => "opt-needs-mut-binding",
        }
    }
}

/// A degradation, **attributed**: subject, site and reason.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Degradation {
    pub subject: String,
    pub site: String,
    pub reason: DegradeReason,
}

/// What M1 decided for one subject.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Decision {
    /// Emit a reference form: `&T` or `&mut T`.
    Ref { mutable: bool },
    /// **S3.2′-2 — emit a borrowed slice form: `&[T]` or `&mut [T]`.**
    ///
    /// Carries its use-site rewrites, because a slice form is the first M1
    /// disposition that is **not declaration-only**: `p.offset(i)` does not
    /// exist on `&[T]`, so the declaration edit alone yields an ill-typed
    /// crate. The rewrites are computed HERE, where HIR and the analyses are
    /// available, and handed to `plan` as data — E1's rule that no later phase
    /// asks an analysis a question.
    Slice {
        mutable: bool,
        uses: Vec<emitability::UseEdit>,
    },
    /// **S3.2′-3 — emit an optional form: `Option<&T>`, `Option<&mut T>`, or
    /// their slice twins.**
    ///
    /// Taken when a use-site `is_null` is present: the program itself says this
    /// pointer may be null, and the nullability directive's optional form is
    /// what a nullable pointer maps to. `slice` selects the fat twin, on
    /// exactly the -2 authority rule — op-facts supply the need, fatness the
    /// licence.
    ///
    /// Carries its use rewrites for the same reason `Slice` does, plus one more:
    /// `p.is_null()` has no image on an `Option` and `*p` has no image either,
    /// so **every** use of an optional subject moves, not only the arithmetic
    /// ones.
    Opt {
        mutable: bool,
        slice: bool,
        uses: Vec<emitability::UseEdit>,
    },
    /// Not emitted, with the reason ATTRIBUTED. **A first-class outcome.**
    ///
    /// §1.6 admits only conflict-non-increasing rewrites; everything outside
    /// that envelope degrades *here*, with a subject and a site — never
    /// silently, and never by an emitter discovering downstream that it cannot
    /// proceed and reporting it as a property of the whole crate.
    Degraded(Degradation),
}

/// The finished, immutable table handed to [`super::plan`].
#[derive(Clone, Debug, Default)]
pub(crate) struct DecisionTable {
    pub entries: Vec<(Subject, Decision)>,
}

impl DecisionTable {
    /// Structural self-consistency: the table covers exactly the subjects it
    /// was given, once each.
    ///
    /// **This is not the coverage gate**, and the distinction is the lesson of
    /// three failed rounds. Every check here compares the table against the
    /// collector's own output, so none of them can detect a subject the
    /// collector never produced. They catch two real but narrower defects: a
    /// **duplicate subject** (which would otherwise plan two edits for one span
    /// and surface only as an `apply` overlap rollback) and a **dropped
    /// decision**.
    ///
    /// Detecting a subject that was never collected requires an instrument with
    /// a different derivation — see [`coverage::reconcile`], which owns that
    /// job and is the only thing in this module entitled to be called a
    /// coverage gate.
    pub(crate) fn is_self_consistent_over(&self, subjects: &[Subject]) -> Result<(), String> {
        let mut seen = rustc_hash::FxHashSet::default();
        for (subject, _) in &self.entries {
            let key = (subject.fn_did.local_def_index.as_u32(), subject.local);
            if !seen.insert(key) {
                return Err(format!("duplicate decision for subject {}", subject.label));
            }
        }
        for subject in subjects {
            if !seen.contains(&(subject.fn_did.local_def_index.as_u32(), subject.local)) {
                return Err(format!("no decision for subject {}", subject.label));
            }
        }
        if self.entries.len() != subjects.len() {
            return Err(format!(
                "table has {} entries for {} subjects",
                self.entries.len(),
                subjects.len()
            ));
        }
        Ok(())
    }

    /// The envelope-demotion records. S2b aggregates these into the counters.
    ///
    /// C.2: coverage gaps no longer live here. A parameter no subject was
    /// built for is now detected by the harness reconciliation as a
    /// producer-B-only row, which is a property of the ARTIFACTS rather than of
    /// this table — and S2b's coverage-class counters consume those artifacts.
    pub(crate) fn degradations(&self) -> impl Iterator<Item = &Degradation> {
        self.entries.iter().filter_map(|(_, d)| match d {
            Decision::Degraded(record) => Some(record),
            Decision::Ref { .. } | Decision::Slice { .. } | Decision::Opt { .. } => None,
        })
    }

    // `emitted_count()` — a count of `Ref` DECISIONS — lived here until S2b.3
    // made `emitted` count PLACEMENTS. It is deleted rather than kept behind an
    // allow: it is orphaned by that change, and what it computes is now
    // precisely the wrong number to report. Leaving it available is an
    // invitation to re-adopt it.
    //
    // The placement-truth witnesses define themselves against it as a
    // counterfactual, so their recorded mutation names the expression
    // (`entries.iter().filter(|(_, d)| matches!(d, Decision::Ref { .. })).count()`)
    // rather than a call, and stays runnable without it.
}

/// Build the decision table from BO's accepted model **and the A1 facts**.
///
/// The accepted model is the only BO input S1/S2a consume. `BoExport`
/// (E-R2..E-R4) is opened by the driver but deliberately not read here: the
/// reference arm needs no move point, no loan identity and no certificate, and
/// consuming facts the arm does not use would make this phase's dependencies a
/// lie.
pub(crate) fn decide(
    tcx: TyCtxt<'_>,
    subjects: &[Subject],
    model: &FxHashMap<SlotRef, SlotKind>,
    slots: &CrateSlots,
    facts: &EmitabilityFacts,
    fat: &super::fat_facts::FatFacts,
    slice_uses: &FxHashMap<(LocalDefId, rustc_hir::HirId), emitability::SliceUses>,
    opt_uses: &FxHashMap<(LocalDefId, rustc_hir::HirId), emitability::OptUses>,
) -> DecisionTable {
    let entries = subjects
        .iter()
        .map(|subject| {
            let decision =
                decide_one(tcx, subject, model, slots, facts, fat, slice_uses, opt_uses);
            (subject.clone(), decision)
        })
        .collect();
    DecisionTable { entries }
}

fn degrade(subject: &Subject, site: String, reason: DegradeReason) -> Decision {
    Decision::Degraded(Degradation {
        subject: subject.label.clone(),
        site,
        reason,
    })
}

fn decide_one(
    tcx: TyCtxt<'_>,
    subject: &Subject,
    model: &FxHashMap<SlotRef, SlotKind>,
    slots: &CrateSlots,
    facts: &EmitabilityFacts,
    fat: &super::fat_facts::FatFacts,
    slice_uses: &FxHashMap<(LocalDefId, rustc_hir::HirId), emitability::SliceUses>,
    opt_uses: &FxHashMap<(LocalDefId, rustc_hir::HirId), emitability::OptUses>,
) -> Decision {
    let decl_site = EmitabilityFacts::site(tcx, subject.attribution_span());

    // The declaration's SHAPE comes FIRST, before any analysis is consulted.
    //
    // R-A collects alias-typed parameters so they are decided rather than
    // dropped; this is where that collection turns into an attributed reason.
    // It is checked ahead of BO's kind because it is knowable without any
    // analysis at all — the plan copies the pointee's source text and an alias
    // has none to copy, whatever BO concluded. Ordering it first also keeps the
    // witness for this class independent of the solver's verdict, which is the
    // §5.3 rule: test the layer you name, not a composition that routes through
    // it.
    //
    // The cost, stated: an alias-typed parameter's BO kind does not reach the
    // counters. That is S2b's question to reopen with a reason if it wants the
    // "how many alias params would have been Ref" breakdown.
    // BEFORE the shape test, because "no declared type" is not a shape. A local
    // with no annotation has no `decl_shape` worth reporting, and routing it
    // through the shape arm would attribute it to a syntax it does not have.
    if subject.ty_span.is_none() {
        return degrade(subject, decl_site, DegradeReason::NoDeclaredType);
    }
    if subject.decl_shape != DeclShape::RawPtr {
        return degrade(
            subject,
            decl_site,
            DegradeReason::UnsupportedDeclShape {
                shape: subject.decl_shape.key(),
            },
        );
    }

    let Some(universe) = slots.fn_local_slots.get(&subject.fn_did) else {
        return degrade(subject, decl_site, DegradeReason::NoSlot);
    };
    let Some(slot_id) = universe.slot_for_local_depth(subject.local, 0) else {
        return degrade(subject, decl_site, DegradeReason::NoSlot);
    };

    // BO's kind first: it is the authority on WHETHER a reference is sound.
    match model.get(&SlotRef::Local(subject.fn_did, slot_id)) {
        Some(SlotKind::Ref) => {}
        Some(SlotKind::Raw) => return degrade(subject, decl_site, DegradeReason::KindRaw),
        Some(SlotKind::Owning) => return degrade(subject, decl_site, DegradeReason::KindOwning),
        None => return degrade(subject, decl_site, DegradeReason::NoSlot),
    }

    // A1 emitability: BO says a reference is SOUND; these say whether one can
    // actually be EMITTED. Both are decision-phase questions, which is the
    // whole point — S1 let them fall through to an anonymous gate failure.
    // **S3.2′-2 — the borrowed-slice arm.** A raw-only use is not automatically
    // a degradation any more: if EVERY such use is arithmetic and fatness
    // independently concludes array, the subject wants a slice form rather than
    // a reference.
    //
    // The authority split is deliberate and measured (micro-plan §1):
    // **op-facts supply the NEED** — this pointer indexes, so a slice is the
    // form — and **fatness supplies the LICENSE**, since `Arr` is evidence
    // forced down the lattice while `Ptr` is an unconstrained default that
    // licenses nothing. Fatness ALONE would convert 138 subjects that already
    // emit thin references, inventing a length for pointers that never index.
    //
    // `all` over the whole use vector, never the first: a subject carrying both
    // `offset` and `is_null` must not read as arithmetic because the walk met
    // `offset` first.
    let raw_uses = facts.raw_only_uses.get(&(subject.fn_did, subject.hir_id));
    // **S3.2′-3 — the OPTIONAL arm shares this block**, because both forms are
    // selected from the same fact: the set of raw-only uses. A subject the
    // program itself null-tests is nullable *by the program's own evidence*, and
    // the nullability directive's optional form is what it maps to.
    //
    // The disjunctive authority (micro-plan §1) is why `is_null` alone is
    // enough. It runs opposite to -2's conjunction on purpose: there the unsafe
    // direction was ADOPTING a form (fatness alone would invent a length), here
    // it is REFUSING one (an optional costs ergonomics, never soundness).
    let form = match raw_uses {
        Some(uses) => {
            let arith = |op: &str| emitability::SLICE_ARITHMETIC_OPS.contains(&op);
            let all_arithmetic = uses.iter().all(|(op, _)| arith(op));
            let is_array = fat.is_array(subject.fn_did, subject.local);
            let null_tested = uses.iter().any(|(op, _)| op == "is_null");
            let has_arithmetic = uses.iter().any(|(op, _)| arith(op));
            // Everything that is not the null test must be arithmetic: any other
            // raw-only method (`read`, `copy_to`, …) has no image under the
            // wrapper, and admitting it would be the mixed-use hazard again.
            let rest_arithmetic = uses.iter().all(|(op, _)| op == "is_null" || arith(op));

            if all_arithmetic && is_array {
                Form::Slice
            } else if null_tested
                && rest_arithmetic
                // A null-initialized binding needs its INITIALIZER rewritten to
                // `None`, which is a construction-site edit this slice does not
                // own. Falling through to the existing degrade leaves such a
                // subject exactly where it is today.
                && !subject.null_init
                // A thin optional has no image for arithmetic; the fat twin does,
                // and fatness is the licence for it — the -2 rule, unchanged.
                && (!has_arithmetic || is_array)
            {
                Form::Opt {
                    slice: has_arithmetic && is_array,
                }
            } else {
                let (op, span) = uses.first().expect("a recorded use vector is non-empty");
                return degrade(
                    subject,
                    EmitabilityFacts::site(tcx, *span),
                    DegradeReason::RawPointerOperation { op: op.clone() },
                );
            }
        }
        None => Form::Plain,
    };
    if let Some(span) = facts.ptr_comparisons.get(&(subject.fn_did, subject.hir_id)) {
        return degrade(
            subject,
            EmitabilityFacts::site(tcx, *span),
            DegradeReason::PtrComparison,
        );
    }
    if let Some(spans) = facts.referenced.get(&subject.fn_did)
        && let Some(span) = spans.first()
    {
        return degrade(
            subject,
            EmitabilityFacts::site(tcx, *span),
            DegradeReason::CallSiteNotAdapted,
        );
    }

    // LAST — see `DegradeReason::FreedSlot`. A veto on emission, not a
    // reordering: every subject that reaches here passed every other test, so
    // this arm can only ever convert a `Ref` into a `freed-slot` degradation and
    // can never displace another reason. That is what makes it measurable as
    // zero decision movement rather than merely asserted to be.
    if let Some(span) = subject.freed_at {
        return degrade(
            subject,
            EmitabilityFacts::site(tcx, span),
            DegradeReason::FreedSlot,
        );
    }

    // **S3.2′-3 — the null-init gate.** Positive evidence of nullness, so no
    // PLAIN form may emit.
    //
    // Placed after every degrade arm, including the freed veto, so it can only
    // ever convert a subject that would otherwise emit. That is what bounds its
    // transitions to the emitting population and makes the pre-registered count
    // a count rather than an estimate — the same construction that made the
    // freed gate's zero movement structural.
    if matches!(form, Form::Plain) {
        if subject.null_init {
            return degrade(subject, decl_site, DegradeReason::NullInit);
        }
        return Decision::Ref {
            mutable: subject.mutable,
        };
    }

    if let Form::Opt { slice } = form {
        // The construction-site guard, exactly as the slice arm has one: an
        // optional's VALUE has to be built at the initializer, and this phase
        // owns declarations and uses, not initializers.
        if matches!(subject.kind, SubjectKind::Local) {
            return degrade(subject, decl_site, DegradeReason::OptLocalConstruction);
        }
        let uses = opt_uses
            .get(&(subject.fn_did, subject.hir_id))
            .cloned()
            .unwrap_or_default();
        if let Some(span) = uses.unsupported {
            return degrade(
                subject,
                EmitabilityFacts::site(tcx, span),
                DegradeReason::OptUseUnsupported,
            );
        }
        // The idiom rule, from the corpus (micro-plan §9c): multiplicity ×
        // mutability. One use of a mutable optional takes `unwrap()` — g02's
        // ratified text, and the move is fine exactly once. More than one needs
        // `as_mut()`, and `as_mut()` needs a `mut` binding, which is one edit
        // away in a phase that does not own the binding pattern.
        if subject.mutable && uses.non_test_uses > 1 && !subject.mut_binding {
            return degrade(subject, decl_site, DegradeReason::OptNeedsMutBinding);
        }
        return Decision::Opt {
            mutable: subject.mutable,
            slice,
            uses: uses.rewrites,
        };
    }

    // A local would need the slice VALUE constructed at its initializer —
    // `from_raw_parts` and a length. Different mechanism, different soundness
    // argument; scoped out of this slice and counted rather than attempted.
    if matches!(subject.kind, SubjectKind::Local) {
        return degrade(subject, decl_site, DegradeReason::SliceLocalConstruction);
    }
    let uses = slice_uses
        .get(&(subject.fn_did, subject.hir_id))
        .cloned()
        .unwrap_or_default();
    if let Some(span) = uses.unsupported {
        return degrade(
            subject,
            EmitabilityFacts::site(tcx, span),
            DegradeReason::SliceUseUnsupported,
        );
    }
    // The same gate as the plain arm: a slice form is still not an optional one,
    // so positive evidence of nullness blocks it too. Unreachable on the current
    // corpus — every null-initialized slice candidate is a local and degrades
    // above — and kept as the backstop that keeps the rule "no plain form on
    // positive null evidence" true of every form rather than of one.
    if subject.null_init {
        return degrade(subject, decl_site, DegradeReason::NullInit);
    }
    Decision::Slice {
        mutable: subject.mutable,
        uses: uses.rewrites,
    }
}

/// Which form `decide_one` selected, before the gates that can still refuse it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Form {
    /// `&T` / `&mut T`.
    Plain,
    /// `&[T]` / `&mut [T]`.
    Slice,
    /// `Option<…>`; `slice` picks the fat twin.
    Opt { slice: bool },
}

#[cfg(test)]
mod self_consistency_tests {
    //! Witnesses for [`DecisionTable::is_self_consistent_over`] — and for what
    //! it deliberately does **not** do.
    //!
    //! The dropped-subject arm that used to live here has moved to
    //! [`super::coverage`], where it belongs: detecting a subject the collector
    //! never produced needs an instrument with a different derivation, and this
    //! check has none — every comparison in it is against the collector's own
    //! output. Keeping a "coverage" test next to a self-comparison is how three
    //! rounds of unfailable gates read as covered.

    use super::*;

    fn subject(local: u32, label: &str) -> Subject {
        Subject {
            fn_did: rustc_hir::def_id::CRATE_DEF_ID,
            local: Local::from_u32(local),
            hir_id: rustc_hir::CRATE_HIR_ID,
            param_name: Some(label.rsplit("::").next().unwrap_or(label).to_owned()),
            kind: SubjectKind::Param { hir_index: local as usize - 1 },
            ptr_depth: 1,
            label: label.to_owned(),
            ty_span: Some(rustc_span::DUMMY_SP),
            binding_span: rustc_span::DUMMY_SP,
            pointee_span: Some(rustc_span::DUMMY_SP),
            decl_shape: DeclShape::RawPtr,
            mutable: true,
            freed_at: None,
            len_recovered: false,
            null_init: false,
            mut_binding: false,
        }
    }

    fn table(entries: Vec<Subject>) -> DecisionTable {
        DecisionTable {
            entries: entries
                .into_iter()
                .map(|s| (s, Decision::Ref { mutable: true }))
                .collect(),
        }
    }

    /// A table that covers its subjects, once each, is self-consistent.
    ///
    /// **Positive control, and no deletion mutation fails it** — recorded
    /// rather than dressed up. A test asserting that a checker *accepts* valid
    /// input cannot be broken by deleting one of that checker's rejection arms;
    /// only making the function unconditionally reject would fail it. Its job is
    /// to prove the three negatives below are not passing because
    /// `is_self_consistent_over` errors on everything.
    #[test]
    fn matching_entries_are_self_consistent() {
        let subjects = vec![subject(1, "f::a"), subject(2, "f::b")];
        assert!(
            table(subjects.clone())
                .is_self_consistent_over(&subjects)
                .is_ok()
        );
    }

    /// A duplicate subject is caught before it can plan two edits for one span
    /// — which `apply` would otherwise surface only as an overlap rollback.
    ///
    /// *Mutation-tested (Rider 0, deletion first):* deleting the `seen.insert`
    /// arm makes this pass.
    #[test]
    fn a_duplicate_subject_is_rejected() {
        let subjects = vec![subject(1, "f::a")];
        let dup = table(vec![subject(1, "f::a"), subject(1, "f::a")]);
        let err = dup
            .is_self_consistent_over(&subjects)
            .expect_err("a duplicate decision must be rejected");
        assert!(err.contains("duplicate"), "wrong failure arm: {err}");
    }

    /// A subject with no decision is caught.
    ///
    /// *Mutation-tested (Rider 0, deletion first):* deleting the
    /// `for subject in subjects` arm makes this pass — the length check alone
    /// does not catch it, because the perturbation changes membership without
    /// changing the count.
    #[test]
    fn a_subject_with_no_decision_is_rejected() {
        let subjects = vec![subject(1, "f::a"), subject(2, "f::b")];
        // Same cardinality, different membership: `f::b` has no decision and
        // `f::c` has one for a subject that was never handed in.
        let skewed = table(vec![subject(1, "f::a"), subject(3, "f::c")]);
        let err = skewed
            .is_self_consistent_over(&subjects)
            .expect_err("a subject with no decision must be rejected");
        assert!(err.contains("no decision for"), "wrong failure arm: {err}");
    }

}
