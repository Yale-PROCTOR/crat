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

pub(crate) mod co_conversion;
pub(crate) mod construction;
pub(crate) mod emitability;
pub(crate) mod seam;
pub(crate) mod universe;

use emitability::EmitabilityFacts;

/// **S3.6-1 — what the `referenced` gate does on this pass.**
///
/// The gate at `decide_one` position 8 degrades every subject of an in-crate
/// referenced function. S3.6-1 is the slice that lifts it, and lifting it needs
/// a question asked one step earlier: *which subjects would convert if the gate
/// were not there?* That question is what builds the co-conversion classes, and
/// it must be answered by **this** ladder rather than by a replay of it —
/// micro-plan §1b measured what a replay costs (a `facts.tsv`-only replay
/// reported 2,133 against a true 2,075 and was retracted).
///
/// So the gate becomes a mode, and the class builder runs the real
/// [`decide_one`] under [`Self::LiftAdaptable`].
///
/// # Why the lifting variant names ADAPTABLE, and why that is not a comment
///
/// The pinned population — 295 functions / 640 subjects, 87 % of it
/// tulipindicators — is **excluded from M1** and deferred to M2/M3 (ruling
/// 2026-08-10). A variant spelled `Lift` would have made every pinned
/// parameter a class node, and the exclusion would then have lived only in
/// prose. Banked rule (2026-08-10): *a parked capability is excluded
/// structurally — in the types and the count pins — never in prose alone.*
/// This enum is where that rule is paid for at the decision layer.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RefGate {
    /// Adaptable functions pass the gate; **pinned ones still block**.
    ///
    /// The hypothetical the class builder asks about. Task 3 is where a
    /// production call site may pass it, and then only for admissible classes.
    LiftAdaptable,
}

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
    /// HIR `let` carries one whole-pattern type).
    ///
    /// **Such subjects cannot emit — nothing splices them — but this is no
    /// longer a REASON.** The dissolution (2026-08-12) put the ladder ahead of
    /// it: 1,084 of the 1,196 name a gate that was already there, and the 112
    /// for which the missing declaration IS the binding constraint get a
    /// residual key from [`residual_reason`] naming the owed capability. What
    /// enforces the no-emission half is the veto in [`decide_one`].
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
    /// **The dissolution pass** — where this binding's VALUE comes from.
    ///
    /// Stamped from the same construction pass as [`Self::null_init`] and
    /// [`Self::len_recovered`], so the three cannot disagree about what the
    /// initializer is. The class itself rather than a boolean projection of it,
    /// because [`residual_reason`] has to name *which* owed capability an
    /// unspliceable subject is waiting on, and a boolean cannot.
    ///
    /// **Read only by [`residual_reason`]**, which runs after every other gate
    /// has declined to speak. That containment is the point: before the
    /// dissolution this module read nothing from the construction recognizer
    /// except two booleans, and that is still true of every gate that can BLOCK
    /// a subject. The class decides an attribution, never a decision.
    ///
    /// `None` for a parameter — no construction site in this crate — and for a
    /// `let` the recognizer does not classify. The `param-no-site` rule again:
    /// a statement about reach, never a claim about the program.
    pub ctor: Option<construction::Construction>,
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
    /// **The dissolution's residue** — the subject has no declared type, every
    /// other gate has declined to speak, and the type would have to come from
    /// the **callee's return type**.
    ///
    /// Its own key rather than `escapes-via-return`, which is a different
    /// claim: that one says a converted reference would escape THROUGH a
    /// return, this one says the declaration's type LIVES in one. Reusing it
    /// would attribute to these subjects a hazard they do not carry.
    ///
    /// Return position is not in M1's subject universe at all, so this reason
    /// is owed forward to S3.6-5 rather than to the locals-conversion slice.
    ReturnNotAdapted,
    /// **The dissolution's residue** — as [`Self::ReturnNotAdapted`], but the
    /// type lives in a **pointee or struct field**: `(*s).f`, `&arr[i]`, `&x`,
    /// `((*h).arr).as_mut_ptr()`. Owed to M3, not to this milestone.
    PlaceReadPointee,
    /// **The dissolution's residue** — as [`Self::ReturnNotAdapted`], but the
    /// type is **coupled to another binding's**: a copy, pointer arithmetic off
    /// another local, or a conditional over two statics. This is the one
    /// residual class the registered locals-conversion follow-up owns, because
    /// initializer edges in the co-conversion graph are exactly what would
    /// resolve it.
    CopySourceCoupled,
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
    /// **S3.2′-5 — the offset may be negative, so no `&[T]` form may emit.**
    ///
    /// `*p.offset(e)` becomes `p[(e) as usize]`. Where `e` is negative at
    /// runtime the cast wraps to a huge index and the bounds check panics:
    /// memory-safe, and a **behaviour change** against a program that
    /// legitimately indexed backwards. The `-2` arm authorised that position
    /// while consulting no sign at all; this is the gate that closes it.
    ///
    /// **Its own key rather than folded into `SliceUseUnsupported`**, on the
    /// `OptNeedsMutBinding` precedent: the occurrence *is* `*p.offset(e)`, so
    /// the use shape is supported and nothing about it is unsupported. What
    /// blocks it is the argument's sign, and the form that serves a negative
    /// offset — `SliceCursor` — is an owed capability, not a missing use
    /// rewrite. Two different owed items must not read as one.
    ///
    /// **The verdict is two-way, and the name says so.** `SignFacts` fuses
    /// `Neg` and `Top` into one taint bit (`sign_facts.rs:7-24`), so a subject
    /// counted here may be *unknown* rather than *provably negative* — the key
    /// reads `neg-or-unknown` and never `negative` for that reason.
    ///
    /// **Fires in the `Form::Slice` arm only.** Placed there rather than
    /// earlier because 61 of the 534 emitting `Ref` subjects also read
    /// `neg-or-unknown`; they are thin, form no index, and a gate above form
    /// selection would move every one of them.
    SliceNegOrUnknownOffset,
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
    /// **The subject's own use-edits NEST, so no flat splice can express them.**
    ///
    /// brotli's shape: `table = table.offset((*table).value as isize)`. The use
    /// walk fires once per OCCURRENCE, so the self-advance source yields an edit
    /// spanning the whole `offset` call and the plain deref inside its index
    /// yields a second edit *within* that span.
    ///
    /// **Its own key rather than folded into `SliceUseUnsupported`**, on the
    /// `SliceNegOrUnknownOffset` precedent: every occurrence here *is* a
    /// supported shape — each would rewrite correctly in isolation. What blocks
    /// the subject is that two correct rewrites overlap, which is a property of
    /// the pair, not of either use. Two different owed items must not read as
    /// one.
    ///
    /// **Degraded rather than resolved by picking a winner, because neither
    /// choice is correct.** `index_text` renders the index with
    /// `span_to_snippet`, so the outer replacement embeds the inner use's
    /// ORIGINAL text — `(*table)`, which has no meaning on a `&[T]`. Dropping
    /// the inner edit emits that stale text; dropping the outer leaves the
    /// `offset` call. The rewrite is simply not expressible as byte splices, and
    /// the honest response is to decline the subject.
    ///
    /// Resolving it properly means rendering the index from REWRITTEN text
    /// rather than source — registered as a yield follow-up, not attempted here.
    ///
    /// **Fires LAST in its arm**, on the freed-slot placement rule: every
    /// subject reaching it has passed every other gate, so its count is exactly
    /// the population this defect costs and it can never displace another
    /// reason.
    NestedUseEdits,
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
    /// **S3.6-1 step 2 — the subject's own reference can reach a RAW context.**
    ///
    /// `&mut T → *mut T` is an implicit coercion at a call argument, a
    /// `static mut` store, a field store and a return (§5a, compiler-measured,
    /// all four exit 0). So this flow presents as **nothing at all**: it is not
    /// ill-typed, the verify loop has nothing to absorb, and no counter moves.
    /// The record's E3b premise said such flows are ill-typed; that was refuted,
    /// and this reason is the decision-time gate replacing the retracted revert
    /// prediction.
    ///
    /// **`via` itemizes, and the key IS the block reason's key**, so the census
    /// and the reason field speak ONE vocabulary and a join between them needs
    /// no translation. A ruling asked for the population itemized; a shared
    /// `silent-coercion` bucket would have made that unrecoverable.
    ///
    /// **Scope, stated:** only plain-`Ref` subjects can carry it, because only
    /// they are class nodes. A `&mut [T]` or `Option<&mut T>` reaching a raw
    /// context is the same hazard and is **not** gated here.
    SilentCoercion { via: co_conversion::BlockReason },
    /// **S3.6-1 step 3 — the subject's CLASS cannot convert, though the subject
    /// contributes no blocking fact of its own.**
    ///
    /// Conversion is a property of the connected component: converting a callee
    /// parameter while the caller feeding it stays raw is `E0308`, so one
    /// blocked member blocks the class, and a collateral member is blocked by
    /// **transitivity**.
    ///
    /// **The variant names the INDIRECTION; the payload preserves the blocking
    /// class's key.** Reporting the class's key directly would attribute to this
    /// subject a hazard it does not carry — the third application of the
    /// reason-honesty rule in this slice. The collateral itemization is read
    /// from the census's `class_block` column: one vocabulary, two columns.
    ClassBlocked { via: co_conversion::BlockReason },
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
            DegradeReason::ReturnNotAdapted => "return-not-adapted",
            DegradeReason::PlaceReadPointee => "place-read-pointee",
            DegradeReason::CopySourceCoupled => "copy-source-coupled",
            DegradeReason::FreedSlot => "freed-slot",
            DegradeReason::SliceUseUnsupported => "slice-use-unsupported",
            DegradeReason::NestedUseEdits => "nested-use-edits",
            DegradeReason::SliceNegOrUnknownOffset => "slice-neg-or-unknown-offset",
            DegradeReason::SliceLocalConstruction => "slice-local-construction",
            DegradeReason::NullInit => "null-init",
            DegradeReason::OptUseUnsupported => "opt-use-unsupported",
            DegradeReason::OptLocalConstruction => "opt-local-construction",
            DegradeReason::OptNeedsMutBinding => "opt-needs-mut-binding",
            // ONE vocabulary with the census, deliberately.
            DegradeReason::SilentCoercion { via } => via.key(),
            // Names the indirection: the class's key is payload, reported by
            // the census and never conflated with a hazard this subject has.
            DegradeReason::ClassBlocked { .. } => "class-blocked",
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
    /// **S3.6-1 seam adapters.** Computed in this phase — it is the only phase
    /// that may read an analysis — and handed to `plan` as data, exactly as
    /// `Decision::Slice`'s use-edits are.
    ///
    /// Carried BESIDE `entries` rather than inside a `Decision` because a seam
    /// belongs to a *pair*: the callee subject justifies it and the caller's
    /// file receives it. Attaching it to either end alone would misplace one of
    /// the two.
    pub seams: seam::SeamPlan,
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
/// Everything `decide_one` reads, gathered once.
///
/// **Carried from S3.2′-3 and 2b, landed at the touch they named.** Both slices
/// recorded this as owed "at the next natural touch of those signatures";
/// S3.2′-5 was that touch and deliberately declined it, because a signature
/// refactor inside a gate-only slice adds churn its must-not-move discipline
/// could not cheaply verify. It lands here instead, alone, before any mechanism.
///
/// **Every field is a read-only borrow**, which is the phase-separation rule
/// (E1) expressed in a type: the decision phase reads analyses and hands the
/// next phase a finished value, so a context that could not be mutated is the
/// honest shape for it.
pub(crate) struct Ctx<'a, 'tcx> {
    pub(crate) tcx: TyCtxt<'tcx>,
    pub(crate) model: &'a FxHashMap<SlotRef, SlotKind>,
    pub(crate) slots: &'a CrateSlots,
    pub(crate) facts: &'a EmitabilityFacts,
    pub(crate) fat: &'a super::fat_facts::FatFacts,
    pub(crate) sign: &'a super::sign_facts::SignFacts,
    pub(crate) slice_uses: &'a FxHashMap<(LocalDefId, rustc_hir::HirId), emitability::SliceUses>,
    pub(crate) opt_uses: &'a FxHashMap<(LocalDefId, rustc_hir::HirId), emitability::OptUses>,
    /// **S3.6-1** — see [`RefGate`]. A mode rather than a fact, which is why it
    /// is `Copy` and not a borrow like everything else here.
    pub(crate) gate: RefGate,
    /// **S3.6-1 step 2.** `None` while the classes are being BUILT — the
    /// hypothetical pass must not consult a verdict derived from itself — and
    /// `Some` on the production pass that consumes them.
    pub(crate) coconv: Option<&'a co_conversion::CoConv>,
}

pub(crate) fn decide(ctx: &Ctx<'_, '_>, subjects: &[Subject]) -> DecisionTable {
    let entries = subjects
        .iter()
        .map(|subject| (subject.clone(), decide_one(ctx, subject)))
        .collect();
    DecisionTable {
        entries,
        // `decide` stays PURE over subjects; seams need the call graph and are
        // filled by the driver, which is also where the analyses live.
        seams: Default::default(),
    }
}

/// **Refuse every use-edit NESTING, across the whole table.**
///
/// `apply` rejects overlapping edits, and a plan that produces them has not
/// decided. Nesting arises two ways, and only a table-level pass sees both:
///
/// - **within one subject** — `table = table.offset((*table).value as isize)`
///   yields an edit for the whole `offset` call and another for the `(*table)`
///   inside its index;
/// - **across two subjects** — `*new_id.offset(*block_ids.offset(i) as isize)`
///   yields `new_id`'s edit containing `block_ids`'s.
///
/// A per-subject check sees only the first. Measured, not reasoned: it left 15
/// of brotli's 17 collisions standing.
///
/// # Which subject is refused, and why it differs by case
///
/// **The INNER one** — and for the cross-subject case that is not merely the
/// conservative pick, it is the *correct* one. `index_text` renders an index by
/// `span_to_snippet`, so the outer replacement embeds the inner expression's
/// ORIGINAL text. If the inner subject stays raw, that text stays valid:
/// `new_id[(*block_ids.offset(i as isize)) as usize]` is well-typed exactly
/// when `block_ids` is still a pointer. Refusing the inner subject therefore
/// removes the collision *and* leaves the outer rewrite correct.
///
/// When inner and outer are the SAME subject the two coincide, and refusing it
/// drops both edits — which is the only sound answer there, since the outer's
/// embedded text would otherwise name a binding that is no longer a pointer.
///
/// # Fixpoint
///
/// Refusing a subject removes its edits, which can leave a formerly-inner edit
/// with no container. The loop repeats until no nesting remains, so a chain
/// `a ⊃ b ⊃ c` refuses `b` and `c` but keeps `a` — never more than the
/// containment relation forces.
pub(crate) fn refuse_nested_use_edits(tcx: TyCtxt<'_>, table: &mut DecisionTable) {
    loop {
        // (entry index, edit span) for every entry still emitting use-edits.
        let mut edits: Vec<(usize, Span)> = Vec::new();
        for (i, (_, decision)) in table.entries.iter().enumerate() {
            let uses = match decision {
                Decision::Slice { uses, .. } | Decision::Opt { uses, .. } => uses.as_slice(),
                _ => &[],
            };
            edits.extend(uses.iter().map(|u| (i, u.span)));
        }
        // Outermost first at equal starts, so the container is seen before what
        // it contains.
        edits.sort_by_key(|(_, s)| (s.lo(), std::cmp::Reverse(s.hi())));

        let mut refuse: Option<(usize, Span)> = None;
        let mut open: Vec<(usize, Span)> = Vec::new();
        for (entry, span) in edits {
            while open.last().is_some_and(|(_, o)| o.hi() <= span.lo()) {
                open.pop();
            }
            // Same entry or not, the INNER one is refused; see above.
            if open.last().is_some_and(|(_, outer)| outer.contains(span)) {
                refuse = Some((entry, span));
                break;
            }
            open.push((entry, span));
        }

        let Some((entry, span)) = refuse else { return };
        let (subject, decision) = &mut table.entries[entry];
        *decision = degrade(
            subject,
            EmitabilityFacts::site(tcx, span),
            DegradeReason::NestedUseEdits,
        );
    }
}

fn degrade(subject: &Subject, site: String, reason: DegradeReason) -> Decision {
    Decision::Degraded(Degradation {
        subject: subject.label.clone(),
        site,
        reason,
    })
}

/// **The dissolution's residual attribution.** Which owed capability an
/// unspliceable subject is waiting on, from where its value comes from.
///
/// Reached only when every gate in [`decide_one_ladder`] has declined — that
/// is, when the missing declaration is the *binding* constraint rather than one
/// blocker among several. On the corpus that is 112 of 1,196 (measured
/// 2026-08-12); the other 1,084 name a real gate and never arrive here.
///
/// The folds onto the three keys are by **type source**, not by construction
/// spelling, and each was measured before it was written (micro-plan §1):
/// `Alloc` is `strdup(url)`, whose type is the callee's return type;
/// `ArrayDecay` is `((*h).next_symbol).as_mut_ptr()`, whose type is the
/// field's element type; `Other` is, over all 19 on the corpus, either
/// `q.offset(…)` off another local or a conditional over two statics.
///
/// `None` — no recognized initializer — folds to source-coupled: such a local
/// takes its type from a later assignment, which is that claim. **Corpus-empty
/// (0 of 1,196) and pinned as empty**, not asserted away.
fn residual_reason(ctor: Option<&construction::Construction>) -> DegradeReason {
    use construction::Construction as C;
    match ctor {
        Some(C::CallResult | C::Alloc { .. }) => DegradeReason::ReturnNotAdapted,
        Some(C::PlaceRead | C::ArrayDecay | C::IndexAddr | C::AddrOf) => {
            DegradeReason::PlaceReadPointee
        }
        Some(C::CopyOf | C::Other) | None => DegradeReason::CopySourceCoupled,
        // The null-init gate above owns this class and fires before the
        // residue can. Kept explicit rather than folded into an arm it does not
        // belong to, so the ordering is legible where it matters.
        Some(C::NullLit) => DegradeReason::NullInit,
    }
}

/// **The dissolution's structural guarantee: a subject with no splice target
/// cannot emit.**
///
/// Separate from the residue gate inside [`decide_one_ladder`], and both earn
/// their place. That one is about ATTRIBUTION — it keeps the co-conversion gate
/// from claiming 158 subjects it has nothing to say about. This one is about
/// the LEDGER: today the `Slice` and `Opt` arms cannot reach an emission for a
/// local because `slice-local-construction` and `opt-local-construction` fire
/// first, but "zero decision flips" must not rest on those two gates staying
/// where they are.
///
/// Corpus-unreachable by construction, which is precisely why it is witnessed
/// through the `perturb` hook rather than by a sweep: a guard no test can break
/// is not a guard.
fn decide_one(ctx: &Ctx<'_, '_>, subject: &Subject) -> Decision {
    let decision = decide_one_ladder(ctx, subject);
    if subject.ty_span.is_some() {
        return decision;
    }
    // EXHAUSTIVE, not `matches!(.., Degraded(_))` — the import denylist rejects
    // the bypass shape and is right to: a new emitting disposition must be a
    // compile error here, because a form this veto does not name is a form that
    // escapes it.
    match decision {
        Decision::Ref { .. } | Decision::Slice { .. } | Decision::Opt { .. } => degrade(
            subject,
            EmitabilityFacts::site(ctx.tcx, subject.attribution_span()),
            residual_reason(subject.ctor.as_ref()),
        ),
        Decision::Degraded(_) => decision,
    }
}

fn decide_one_ladder(ctx: &Ctx<'_, '_>, subject: &Subject) -> Decision {
    let &Ctx {
        tcx,
        model,
        slots,
        facts,
        fat,
        sign,
        slice_uses,
        opt_uses,
        gate,
        coconv,
    } = ctx;
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
    //
    // **The dissolution removed an earlier gate from ahead of this one.** Every
    // vintage before it returned `no-declared-type` here for a missing
    // `ty_span`, ahead of the shape test and ahead of every analysis — one
    // reason over 1,196 subjects, naming the splice mechanism rather than
    // anything about the subject. The ladder now speaks for them, and the
    // measured result is that 1,084 of the 1,196 hit a gate that was already
    // there. Only 112 reach the residue.
    //
    // The shape test comes first for them too, and it is correct for them
    // because the collector derives the shape from the RESOLVED type when there
    // is no annotation: 51 of these locals are `let ref mut fresh…`
    // temporaries whose type is already `&mut T`, and this is the arm that says
    // so.
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
    // **S3.6-0 recorded the reference KIND; S3.6-1 makes the gate a MODE.**
    //
    // Under the former `RefGate::BlockAll` — task 2's setting and every setting
    // before it, **deleted at M-3 as measured-dead** — any reference degraded,
    // adaptable or pinned alike, exactly as at S3.6-0. Under the surviving
    // [`RefGate::LiftAdaptable`] the
    // adaptable population passes and the pinned population still blocks, which
    // is the hypothetical `co_conversion` builds its node set from.
    if let Some(refs) = facts.referenced.get(&subject.fn_did)
        && let Some((_kind, span)) = refs.first()
    {
        let blocks = match gate {
            RefGate::LiftAdaptable => !emitability::RefKind::is_adaptable(refs),
        };
        if blocks {
            return degrade(
                subject,
                EmitabilityFacts::site(tcx, *span),
                DegradeReason::CallSiteNotAdapted,
            );
        }
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
        // **LAST, on the freed-slot placement rule.** Every subject reaching
        // here passed every other test, so this arm can only convert a would-be
        // emission and can never displace another reason.
        //
        // Only the subject's OWN blocking fact gates. Class collateral is not
        // consulted: while the referenced gate still blocks, a blocked
        // classmate is not converting either, so nothing is jointly decided
        // yet. Collateral becomes load-bearing at the lift, not before.
        // **THE RESIDUE, and it must precede the class gate.**
        //
        // Not a preference — an attribution requirement. The co-conversion node
        // set is built from the HYPOTHETICAL decision, in which a subject with
        // no splice target still degrades, so an unannotated local is **never a
        // node**: 0 of 1,196, against 2,609 of the annotated 4,819 (measured
        // 2026-08-12). `admits` therefore returns false for every one of them
        // and the gate below falls into its not-a-node arm, which reports
        // `call-site-not-adapted`.
        //
        // That arm's own comment predicts this case — *"an unreachable arm that
        // falls through is how a subject escapes its own gate once the premise
        // stops holding"* — and the dissolution is where the premise stops
        // holding. Without this placement 158 subjects would be attributed to a
        // gate that is not blocking them, 121 of them in functions that are not
        // even pinned.
        if subject.ty_span.is_none() {
            return degrade(subject, decl_site, residual_reason(subject.ctor.as_ref()));
        }
        // **S3.6-1 step 3 — THE CLASS GATE, and it consults `admits`.**
        //
        // That is what UNIFORM means: the class verdict governs every node, not
        // only those the `referenced` gate would have blocked. A subject whose
        // function nothing calls is decided by its class exactly like one whose
        // function is called — no vintage exemption.
        if let Some(cc) = coconv {
            let key = (subject.fn_did, subject.hir_id);
            if !cc.admits(key) {
                let reason = match cc.node_block(key) {
                    Some(via) => DegradeReason::SilentCoercion { via },
                    None => match cc.class_block(key) {
                        Some(via) => DegradeReason::ClassBlocked { via },
                        // Not a node. Unreachable through the pipeline —
                        // production and the hypothetical differ ONLY by
                        // `coconv` — and attributed rather than silently
                        // emitted, because an unreachable arm that falls
                        // through is how a subject escapes its own gate once
                        // the premise stops holding.
                        None => DegradeReason::CallSiteNotAdapted,
                    },
                };
                return degrade(subject, decl_site, reason);
            }
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
        // **S3.2′-5 hardening — LAST in this arm**, the same placement rule the
        // plain-slice twin uses, so it can only ever convert a would-be `Opt`
        // emission and never displace `OptUseUnsupported` or
        // `OptNeedsMutBinding`.
        //
        // **Gated on `slice`** — the narrowest arm that owns the hazard. The
        // index is what can wrap, and only the FAT twin forms one: form
        // selection admits `Opt { slice: false }` only under
        // `!has_arithmetic || is_array` with `slice = has_arithmetic &&
        // is_array`, so a thin optional has no arithmetic at all. Gating the
        // whole arm would additionally degrade any thin optional whose sign
        // lookup MISSES, because `may_be_negative` folds `None` conservatively
        // — the 61-thin-`Ref` mistake in a second place.
        //
        // Reason key **shared** with the plain arm by ruling: the hazard and
        // the owed capability are the same, and the subject's own outcome keeps
        // the two arms attributable in the facts join.
        if slice && sign.may_be_negative(subject.fn_did, subject.local) {
            return degrade(subject, decl_site, DegradeReason::SliceNegOrUnknownOffset);
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
    // **S3.2′-5 — LAST in this arm**, on the freed-slot placement rule: every
    // subject reaching here has passed every other test, so this can only ever
    // convert a would-be `Slice` emission and can never displace another
    // reason. That is what makes its movement measurable as a pre-registered
    // count rather than merely asserted to be bounded.
    //
    // The same verdict the self-advance gate reads at `mod.rs:1799` — one sign
    // authority, no parallel notion. `may_be_negative` folds a lookup miss to
    // the conservative side, so an unanalyzed local is refused rather than
    // emitted on absent evidence.
    if sign.may_be_negative(subject.fn_did, subject.local) {
        return degrade(subject, decl_site, DegradeReason::SliceNegOrUnknownOffset);
    }
    Decision::Slice {
        mutable: subject.mutable,
        uses: uses.rewrites,
    }
}

#[cfg(test)]
mod residual_tests {
    use super::{construction::Construction as C, *};

    /// **The residual fold table, exhaustively.** Every `Construction` variant
    /// plus the no-recognized-initializer case names an owed capability.
    ///
    /// A pure function tested as one. The end-to-end witness in `emit_tests`
    /// covers only the four classes that can actually REACH the residue in a
    /// small fixture — `Alloc` cannot, because BO settles a `malloc` local
    /// `Owning` or `Raw` and `kind-*` fires first — so a fold witnessed only
    /// there would be a fold no mutation can break for the other five.
    ///
    /// The list is written out rather than iterated over a variant list,
    /// because there is no such list: the *compiler* enforces exhaustiveness
    /// inside `residual_reason`, and this enforces that each arm sends its
    /// class where the measured witness says it goes (micro-plan §1).
    ///
    /// *Mutation-tested:* collapsing any two arms of `residual_reason` fails
    /// the class whose key was swallowed; making the `None` arm return
    /// `ReturnNotAdapted` fails the last row.
    #[test]
    fn every_construction_class_names_an_owed_capability() {
        let alloc = C::Alloc {
            callee: "malloc".to_owned(),
            size: "4".to_owned(),
            count: None,
        };
        for (ctor, want) in [
            (Some(&C::CallResult), "return-not-adapted"),
            (Some(&alloc), "return-not-adapted"),
            (Some(&C::PlaceRead), "place-read-pointee"),
            (Some(&C::ArrayDecay), "place-read-pointee"),
            (Some(&C::IndexAddr), "place-read-pointee"),
            (Some(&C::AddrOf), "place-read-pointee"),
            (Some(&C::CopyOf), "copy-source-coupled"),
            (Some(&C::Other), "copy-source-coupled"),
            (Some(&C::NullLit), "null-init"),
            // No recognized initializer: the type would come from a later
            // assignment, which IS the source-coupled claim. Corpus-empty
            // (0 of 1,196) and pinned as empty rather than asserted away.
            (None, "copy-source-coupled"),
        ] {
            assert_eq!(
                residual_reason(ctor).key(),
                want,
                "{ctor:?} must name the capability that would unblock it — a \
                 residual key routes an owed item to a slice, and two owed \
                 items must not read as one"
            );
        }
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
            kind: SubjectKind::Param {
                hir_index: local as usize - 1,
            },
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
            ctor: None,
        }
    }

    fn table(entries: Vec<Subject>) -> DecisionTable {
        DecisionTable {
            seams: Default::default(),
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
