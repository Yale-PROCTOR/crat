//! **S3.6-1 task 2 — co-conversion classes.**
//!
//! # Why conversion is a property of a CLASS and not of a subject
//!
//! Converting a callee parameter while the caller passes a bare local that
//! stays raw does not lose precision — it does not compile (`E0308`, measured,
//! micro-plan §4). So a callee parameter and the caller binding feeding it are
//! joined by an **undirected** edge, and the unit of decision is the connected
//! component.
//!
//! # The measured shape, and the risk inversion that fixed the design
//!
//! The coupling does not globally collapse: mean class size 2.1, 89.5 % of
//! nodes in unblocked classes. But the *reason* the class test is the mechanism
//! is not yield, it is safety. rustc's borrow checker is **blind through a
//! raw-pointer deref** (§5a, compiler-measured): `two_mut(&mut *p, &mut *p)`
//! compiles with zero diagnostics where `two_mut(&mut v, &mut v)` is `E0499`.
//! Full co-conversion keeps the aliasing in the region the compiler checks — a
//! mistake there costs a revert. A reborrow bridge would move the same case
//! into the region it cannot check, where a mistake is silent UB. That is why
//! the bridge arm is **parked** (g22, unratified) and why no shape in
//! [`ArgShape`] can construct one.
//!
//! # What this module does at task 2, and what it deliberately does not
//!
//! It **computes**. Nothing here is consulted by [`super::decide_one`]: the
//! production call site passed `RefGate::BlockAll`, so the corpus cannot
//! move. Zero delta is a property of the code — the S3.6-0 pattern — and task 3
//! is where the verdict becomes load-bearing.
//!
//! ⚠ **STALE SINCE S3.6-1, AND THE VARIANT IS GONE (X-3, closed 2026-08-18).**
//! Production has passed `RefGate::LiftAdaptable` since S3.6-1; the claim above
//! describes task 2 only, and it cost one wrong calibration run before it was
//! caught. `BlockAll` was deleted at M-3 as measured-dead, and this note is its
//! other direction — one fact, both places, closed together.

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    Expr, ExprKind, HirId, QPath,
    def::Res,
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use super::{
    Arm, Decision, DecisionTable, RequiredArmSet, Subject, SubjectKind,
    emitability::{ArgShape, EmitabilityFacts, RefKind},
    lifetime::LifetimeEligibility,
    raw_boundary::RawBoundaryDispositionIndex,
};
use crate::analyses::borrow_ownership::{a5_overlap::PairSide, a5_producer::PlannedC9Mark};

/// A node's identity — the same `(owner, binding)` key A1's emitability gates
/// use, so a call argument that resolves to `Res::Local(b)` needs no
/// translation to find the subject it names.
pub(crate) type NodeKey = (LocalDefId, HirId);

/// Why a class may not convert.
///
/// One variant per distinct owed capability or hazard, never a shared
/// "blocked": a cast argument is one edit away in task 4, a null literal is a
/// permanent block, and a silent coercion into a raw parameter is a soundness
/// gate. Collapsing them would make the census unable to answer the only
/// question it exists to answer — *what would it take to unblock this?*
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BlockReason {
    /// A call site supplies a bare local that will **not** convert, so the
    /// callee's parameter cannot either: `E0308` (H5, measured).
    ///
    /// The bridge that would fix it — `f(&mut *r)` — is **parked**.
    ArgStaysRaw,
    /// The member's own binding is passed to a callee parameter that does not
    /// convert. **`&mut T → *mut T` is an implicit coercion**, so this compiles
    /// at exit 0 and produces no counter movement at all (§5a, measured) — the
    /// record's E3b premise, refuted.
    ///
    /// It therefore needs a **decision-time** gate; there is no compile-time
    /// backstop to catch it if the test is wrong. Banked rule 2, 2026-08-09.
    FlowsIntoRawParam,
    /// The member's binding reaches a parameter that converts to a **different
    /// form** — `&mut [T]` or `Option<&mut T>`, not `&mut T`.
    ///
    /// **Its own variant because the hazard class is different, not because the
    /// wording is nicer.** `&mut T` into `*mut T` coerces silently; `&mut T`
    /// into `&mut [T]` is `E0308`. Banked rule 1 — the checked region versus
    /// the unchecked one — is exactly this distinction, so a census that
    /// reported both as `flows-into-raw-param` would file a compiler-caught
    /// revert risk under a silent-UB reason.
    FlowsIntoOtherForm,
    /// The same silent coercion, into a **pinned** callee — one whose signature
    /// is fixed by a fn-pointer cast and which M1 will never adapt.
    ///
    /// Its own variant rather than folded into [`Self::FlowsIntoRawParam`]:
    /// that one is unblockable by a later slice of the same ladder, this one
    /// waits on the M2/M3 pinned population.
    FlowsIntoPinnedCallee,
    /// The member's converting binding is `as`-cast at a call site
    /// (`q as *mut T`). A reference casts to a raw pointer silently, so this is
    /// [`Self::FlowsIntoRawParam`] wearing a cast.
    CastOfConvertingLocal,
    /// The argument is `&mut e as *mut T` or `q as *mut T` — the **cast-strip**
    /// form, whose edit arm is **task 4's** and is not built yet.
    ArgCastFormUnbuilt,
    /// A null literal. `&mut T` cannot represent null (`E0308`, H4 measured);
    /// the form that serves it is `Option`, i.e. a different arm.
    ArgNullLiteral,
    /// A shared borrow (`&e`) at a position that must become `&mut T`.
    ArgSharedIntoMut,
    /// A cast, a call result, an index, arithmetic — no adaptation form exists.
    ArgUnadaptableShape,
    /// The member's binding is **borrowed** at a call site (`f(&mut *r)`) and
    /// the parameter it reaches does not convert.
    ///
    /// Today `&mut *r` on a raw `r` already coerces to `*mut T`. After `r`
    /// converts, the same expression reborrows a **reference**, so the raw
    /// pointer the callee keeps can outlive the borrow. **S3.6-1's conversion
    /// changes the case's character**, which puts it inside banked rule 2
    /// rather than outside it — the gap the adversarial review named (P1).
    BorrowedIntoRawParam,
    /// The member's reference can leave through a **`return`**.
    EscapesViaReturn,
    /// … through an argument to a callee the class machinery cannot see —
    /// `extern` block entries and anything not a direct call to a local `fn`.
    EscapesViaForeignArg,
    /// … through a store into a place projection (`(*t).f = p`).
    EscapesViaFieldStore,
    /// … through a store into a `static mut`.
    EscapesViaStaticStore,
    /// Two argument positions at one call site may name overlapping places, and
    /// both would become references: `E0499`.
    ///
    /// **Demoting one side to shared does not rescue it** — `E0502`, measured
    /// (H6) — so there is no mutability re-assignment that saves the class.
    ///
    /// A shared place ROOT is a *may*-overlap, and an UNKNOWN root is treated
    /// as one: blocking costs yield and never soundness.
    DuplicatePlaceRoot,
}

impl BlockReason {
    pub(crate) fn key(self) -> &'static str {
        match self {
            BlockReason::ArgStaysRaw => "arg-stays-raw",
            BlockReason::FlowsIntoRawParam => "flows-into-raw-param",
            BlockReason::FlowsIntoOtherForm => "flows-into-other-form",
            BlockReason::FlowsIntoPinnedCallee => "flows-into-pinned-callee",
            BlockReason::CastOfConvertingLocal => "cast-of-converting-local",
            BlockReason::ArgCastFormUnbuilt => "arg-cast-form-unbuilt",
            BlockReason::ArgNullLiteral => "arg-null-literal",
            BlockReason::ArgSharedIntoMut => "arg-shared-into-mut",
            BlockReason::ArgUnadaptableShape => "arg-unadaptable-shape",
            BlockReason::BorrowedIntoRawParam => "borrowed-into-raw-param",
            BlockReason::EscapesViaReturn => "escapes-via-return",
            BlockReason::EscapesViaForeignArg => "escapes-via-foreign-arg",
            BlockReason::EscapesViaFieldStore => "escapes-via-field-store",
            BlockReason::EscapesViaStaticStore => "escapes-via-static-store",
            BlockReason::DuplicatePlaceRoot => "duplicate-place-root",
        }
    }
}

/// **P2 — how the within-site overlap gate treats two node positions.**
///
/// A measurement parameter, not a policy. ⚠ **The `RootDisjoint` baseline this
/// doc used to name was deleted at M-3 as measured-dead**; production is
/// [`Self::BlindOnly`], ruled 2026-08-10 on the split census. The per-node lesson applies to this estimate too —
/// blocking a node blocks its class, so neither option can be costed by
/// counting positions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum OverlapRule {
    /// **PRODUCTION, ruled 2026-08-10 on the split census.** Block a pair only
    /// where the compiler cannot see it: at least one side is a place reached
    /// through a base that stays RAW after conversion, or has an unknown root.
    ///
    /// Measured, class-level: this costs **8** admissible nodes against the
    /// unsound baseline and **zero** additional regression — the 8 all sit in
    /// the gate-blocked population. Maximal conservatism costs **391** and
    /// turns the slice negative (net −137). Banked rule 1 in one line:
    /// conservatism belongs where the compiler cannot see, and nowhere else.
    ///
    /// The other pairs are in the **checked** region — if they really alias,
    /// borrowck answers `E0499`/`E0502`, which costs a revert. Yield, not
    /// soundness.
    BlindOnly,
    /// Block every mutable pair regardless of roots — maximal conservatism.
    AllPairs,
}

/// One connected component.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Class {
    /// Members in subject-collection order — **not** a `HashSet`. D19: a report
    /// whose order permutes between runs is not comparable, and the union-find
    /// this is derived from tracks members in a `HashSet`.
    pub members: Vec<NodeKey>,
    /// `None` means every member's every call site supplies a compatible
    /// argument. **One blocked member blocks the class**, which the measured
    /// structure says is affordable — and which libzahl says is not free: one
    /// duplicated-argument site (`zadd(a, a, …)`) blocks a 104-node class.
    pub blocked: Option<BlockReason>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum EdgeForm {
    Raw,
    Ref,
    Slice,
    Optional,
    Box,
}

impl EdgeForm {
    fn of(decision: &Decision) -> Self {
        match decision {
            Decision::Ref { .. } | Decision::InferredRef { .. } => Self::Ref,
            Decision::Slice { .. } => Self::Slice,
            Decision::Opt { .. } => Self::Optional,
            Decision::Box(_) => Self::Box,
            Decision::Degraded(_) => Self::Raw,
        }
    }

    fn key(self) -> &'static str {
        match self {
            Self::Raw => "raw",
            Self::Ref => "ref",
            Self::Slice => "slice",
            Self::Optional => "optional",
            Self::Box => "box",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum EdgeRoute {
    ZeroSyntax,
    ArmA,
    ArmC,
    Glue,
}

impl EdgeRoute {
    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::ZeroSyntax => "zero-syntax",
            Self::ArmA => "arm-a",
            Self::ArmC => "arm-c",
            Self::Glue => "glue",
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct EdgeObligation {
    pub(crate) source: NodeKey,
    pub(crate) target: NodeKey,
    pub(crate) caller: LocalDefId,
    pub(crate) callee: LocalDefId,
    pub(crate) argument_index: usize,
    pub(crate) span: Span,
    pub(crate) source_form: EdgeForm,
    pub(crate) target_form: EdgeForm,
    pub(crate) route: EdgeRoute,
}

#[derive(Clone, Debug)]
struct EdgeCandidate {
    source: NodeKey,
    target: NodeKey,
    caller: LocalDefId,
    callee: LocalDefId,
    argument_index: usize,
    span: Span,
    source_form: EdgeForm,
    target_form: EdgeForm,
}

/// The finished class structure. **Measurement at task 2; the gate at task 3.**
#[derive(Clone, Debug, Default)]
pub(crate) struct CoConv {
    class_of: FxHashMap<NodeKey, usize>,
    classes: Vec<Class>,
    /// The reason a node CONTRIBUTED, as opposed to the one its class carries.
    ///
    /// Kept separately because they answer different questions: the class
    /// reason says why the component cannot convert, this one says which member
    /// is responsible. A census with only the first cannot be acted on.
    node_block: FxHashMap<NodeKey, BlockReason>,
    edges: Vec<EdgeObligation>,
}

impl CoConv {
    /// Would this subject convert, given its class? **Task 3's entry point.**
    ///
    /// A subject that is not a node at all answers `false`: it did not reach
    /// the gate under the hypothetical, so nothing about the class structure
    /// can license it.
    pub(crate) fn admits(&self, key: NodeKey) -> bool {
        self.class_of.contains_key(&key) && !self.node_block.contains_key(&key)
    }

    /// The reason this subject's CLASS carries, as opposed to the one the
    /// subject itself contributed. Step 3's collateral arm reads this: a
    /// subject blocked through a class edge carries no hazard of its own, so
    /// the reason field names the indirection and keeps the class's key as
    /// payload.
    pub(crate) fn class_block(&self, key: NodeKey) -> Option<BlockReason> {
        self.class_of(key).and_then(|id| self.classes[id].blocked)
    }

    pub(crate) fn class_of(&self, key: NodeKey) -> Option<usize> {
        self.class_of.get(&key).copied()
    }

    pub(crate) fn classes(&self) -> &[Class] {
        &self.classes
    }

    pub(crate) fn node_block(&self, key: NodeKey) -> Option<BlockReason> {
        self.node_block.get(&key).copied()
    }

    pub(crate) fn edges(&self) -> &[EdgeObligation] {
        &self.edges
    }

    pub(crate) fn edge_routes(&self, key: NodeKey) -> Vec<&'static str> {
        let mut routes = self
            .edges
            .iter()
            .filter(|edge| edge.source == key || edge.target == key)
            .map(|edge| edge.route.key())
            .collect::<Vec<_>>();
        routes.sort_unstable();
        routes.dedup();
        routes
    }

    pub(crate) fn required_arms(&self, key: NodeKey) -> RequiredArmSet {
        let mut arms = RequiredArmSet::default();
        if self.class_of(key).is_some_and(|id| {
            self.classes[id].members.len() > 1 || self.classes[id].blocked.is_some()
        }) {
            arms.insert(Arm::D4);
        }
        for edge in self
            .edges
            .iter()
            .filter(|edge| edge.source == key || edge.target == key)
        {
            match edge.route {
                EdgeRoute::ArmC => arms.insert(Arm::C),
                EdgeRoute::Glue => arms.insert(Arm::Glue),
                EdgeRoute::ZeroSyntax | EdgeRoute::ArmA => {}
            }
        }
        arms
    }

    pub(crate) fn edge_receipts_tsv(&self, tcx: TyCtxt<'_>) -> String {
        let mut out = String::from(
            "caller\tcallee\targument_index\tsource\ttarget\tsource_form\ttarget_form\troute\tsite\n",
        );
        for edge in &self.edges {
            out.push_str(&format!(
                "{}\t{}\t{}\t{}:{}\t{}:{}\t{}\t{}\t{}\t{}\n",
                tcx.def_path_str(edge.caller.to_def_id()),
                tcx.def_path_str(edge.callee.to_def_id()),
                edge.argument_index,
                tcx.def_path_str(edge.source.0.to_def_id()),
                edge.source.1.local_id.as_u32(),
                tcx.def_path_str(edge.target.0.to_def_id()),
                edge.target.1.local_id.as_u32(),
                edge.source_form.key(),
                edge.target_form.key(),
                edge.route.key(),
                super::emitability::EmitabilityFacts::site(tcx, edge.span),
            ));
        }
        out
    }
}

/// A tiny disjoint-set over dense node ids.
///
/// Not [`crate::utils::dsa::union_find::UnionFind`]: that one carries a
/// `HashSet` of members per root, and iterating it to build the census would
/// reintroduce exactly the nondeterministic report ordering D19 bans. Members
/// are derived here by one deterministic pass over the node order instead.
struct Dsu(Vec<usize>);

impl Dsu {
    fn new(n: usize) -> Self {
        Self((0..n).collect())
    }

    fn find(&mut self, mut x: usize) -> usize {
        while self.0[x] != x {
            self.0[x] = self.0[self.0[x]];
            x = self.0[x];
        }
        x
    }

    fn union(&mut self, a: usize, b: usize) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra != rb {
            self.0[rb] = ra;
        }
    }
}

/// Build the classes from the **hypothetical** decision table.
///
/// `hypothetical` must be the table produced under
/// [`super::RefGate::LiftAdaptable`] — i.e. the answer to *"what would convert
/// if the gate were lifted for the adaptable population?"*. It is produced by
/// the real [`super::decide_one`] and never by a replay of it: micro-plan §1b
/// measured what a replay costs, reporting 2,133 against a true 2,075 because
/// `facts.tsv` alone cannot see the freed, `ctor` and fatness exits. That
/// retraction is this function's contract, not a footnote.
pub(crate) fn build(
    facts: &EmitabilityFacts,
    subjects: &[Subject],
    hypothetical: &DecisionTable,
    escapes: &[Escape],
    overlap: OverlapRule,
) -> CoConv {
    build_with_c9_marks(facts, subjects, hypothetical, escapes, overlap, &[])
}

pub(crate) fn retained_c9_shared_params(
    marks: &[PlannedC9Mark],
    site: &super::emitability::CallSite,
    callee: LocalDefId,
) -> FxHashSet<usize> {
    marks
        .iter()
        .filter(|mark| {
            mark.caller_did == site.caller
                && mark.call_span.lo() == site.span.lo()
                && mark.call_span.hi() == site.span.hi()
                && mark.key.pair.function() == callee.local_def_index.as_u32()
        })
        .filter_map(|mark| {
            let params = mark.key.pair.params();
            let shared = match mark.key.shared_side {
                PairSide::Left => params.first(),
                PairSide::Right => params.second(),
            };
            usize::try_from(shared).ok()?.checked_sub(1)
        })
        .collect()
}

pub(crate) fn build_with_c9_marks(
    facts: &EmitabilityFacts,
    subjects: &[Subject],
    hypothetical: &DecisionTable,
    escapes: &[Escape],
    overlap: OverlapRule,
    c9_marks: &[PlannedC9Mark],
) -> CoConv {
    build_with_c9_marks_and_lifetimes(
        facts,
        subjects,
        hypothetical,
        escapes,
        overlap,
        c9_marks,
        &LifetimeEligibility::default(),
    )
}

pub(crate) fn build_with_c9_marks_and_lifetimes(
    facts: &EmitabilityFacts,
    subjects: &[Subject],
    hypothetical: &DecisionTable,
    escapes: &[Escape],
    overlap: OverlapRule,
    c9_marks: &[PlannedC9Mark],
    lifetime_eligibility: &LifetimeEligibility,
) -> CoConv {
    build_with_c9_marks_lifetimes_and_raw_boundary(
        facts,
        subjects,
        hypothetical,
        escapes,
        overlap,
        c9_marks,
        lifetime_eligibility,
        &RawBoundaryDispositionIndex::default(),
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn build_with_c9_marks_lifetimes_and_raw_boundary(
    facts: &EmitabilityFacts,
    subjects: &[Subject],
    hypothetical: &DecisionTable,
    escapes: &[Escape],
    overlap: OverlapRule,
    c9_marks: &[PlannedC9Mark],
    lifetime_eligibility: &LifetimeEligibility,
    raw_boundary: &RawBoundaryDispositionIndex,
) -> CoConv {
    // ---- 1. the node set: subjects that would emit a PLAIN reference ----
    //
    // Slice and optional forms are deliberately excluded. `&mut [T]` and
    // `Option<&mut T>` are not `&mut T`, so passing one where the other is
    // expected is `E0308`; a class mixing forms is not a class. They keep their
    // own arms and their own slices (-2 / -3), which is also why lifting the
    // gate is reported as an ENTRY count for them and a yield count only here.
    let mut order: Vec<NodeKey> = Vec::new();
    let mut wants_mut: FxHashMap<NodeKey, bool> = FxHashMap::default();
    for (subject, decision) in &hypothetical.entries {
        // EXHAUSTIVE (S3.0, ruling 5), and **the standing guard caught this
        // site**: an `if let Decision::Ref` compiled clean and would have
        // silently classified a fourth disposition as "not a node" — the same
        // shape that once dropped a subject from `emitted_subjects` entirely.
        // A `match` makes the next disposition a compile error here.
        let mutable = match decision {
            Decision::Ref { mutable } | Decision::InferredRef { mutable, .. } => *mutable,
            Decision::Slice { .. }
            | Decision::Opt { .. }
            | Decision::Box(_)
            | Decision::Degraded(_) => continue,
        };
        let key = (subject.fn_did, subject.hir_id);
        order.push(key);
        wants_mut.insert(key, mutable);
    }
    // Subjects that convert, but **not to `&mut T`**. Not nodes — a class
    // mixing forms is not a class — but their positions must be told apart from
    // positions that stay raw, because the two fail in different regions.
    let other_form: FxHashSet<NodeKey> = hypothetical
        .entries
        .iter()
        .filter_map(|(subject, decision)| match decision {
            Decision::Slice { .. } | Decision::Opt { .. } => Some((subject.fn_did, subject.hir_id)),
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Box(_)
            | Decision::Degraded(_) => None,
        })
        .collect();
    let decision_of = hypothetical
        .entries
        .iter()
        .map(|(subject, decision)| ((subject.fn_did, subject.hir_id), decision))
        .collect::<FxHashMap<_, _>>();
    let index: FxHashMap<NodeKey, usize> = order.iter().enumerate().map(|(i, k)| (*k, i)).collect();
    let converts: FxHashSet<NodeKey> = order.iter().copied().collect();

    // Every parameter POSITION that is a subject at all — node or not. The
    // distinction is load-bearing: a position that is not a subject carries no
    // pointer to convert, while a position that is a subject and not a node is
    // a parameter that stays raw, which is what makes an argument into it a
    // silent coercion rather than a non-event.
    let mut param_key: FxHashMap<(LocalDefId, usize), NodeKey> = FxHashMap::default();
    for subject in subjects {
        if let SubjectKind::Param { hir_index } = subject.kind {
            param_key.insert(
                (subject.fn_did, hir_index),
                (subject.fn_did, subject.hir_id),
            );
        }
    }

    let mut dsu = Dsu::new(order.len());
    let mut node_block: FxHashMap<NodeKey, BlockReason> = FxHashMap::default();
    let mut edge_candidates = Vec::<EdgeCandidate>::new();
    /// First reason wins, so the census is deterministic under a node that
    /// contributes two.
    fn block(node_block: &mut FxHashMap<NodeKey, BlockReason>, key: NodeKey, reason: BlockReason) {
        node_block.entry(key).or_insert(reason);
    }

    // ---- 1b. THE ESCAPE GATE — P1, and it runs FIRST ----
    //
    // An escape is a property of the node alone, unconditional, and no later
    // slice of this ladder retires it. The reason-honesty rule therefore names
    // it before any call-site reason: a census must never name a reason whose
    // removal would not unblock the class.
    //
    // **One variant per shape, by ruling**, so the population stays separately
    // attributable and the conservative scope is reversible by a ruling rather
    // than by archaeology.
    for escape in escapes {
        if !converts.contains(&escape.subject) {
            continue;
        }
        if escape.kind == EscapeKind::ForeignArg
            && raw_boundary.opens_span(escape.subject, escape.span)
        {
            continue;
        }
        let Some(reason) = escape_block_reason(escape, lifetime_eligibility) else {
            continue;
        };
        block(&mut node_block, escape.subject, reason);
    }

    // ---- 2. edges and argument admissibility, in ONE pass over call sites ----
    //
    // Callees sorted: `FxHashMap` iteration order is not stable across runs,
    // and "the first reason a node contributed" would permute with it.
    let mut callees: Vec<&LocalDefId> = facts.call_args.keys().collect();
    callees.sort_unstable_by_key(|d| d.local_def_index.as_u32());

    for callee in callees {
        // PINNED means referenced by something that is not a direct call.
        // Deliberately not `is_none_or`: a callee with recorded arguments is
        // referenced by construction, but a fallback that labelled an
        // unreferenced function "pinned" would put a wrong owed capability in
        // the census — the M2/M3 population is not where such a node waits.
        let pinned = facts
            .referenced
            .get(callee)
            .is_some_and(|refs| !RefKind::is_adaptable(refs));
        for site in &facts.call_args[callee] {
            let marked_shared = retained_c9_shared_params(c9_marks, site, *callee);
            // **The within-site overlap gate runs FIRST**, and the ordering is
            // not cosmetic — it is reason honesty.
            //
            // A site like `aliased(q, q)` where `q` itself stays raw satisfies
            // TWO blocking rules: the argument does not convert, and the two
            // positions share a place root. First-reason-wins would report
            // `arg-stays-raw`, which reads as *"convert `q` and this
            // unblocks"* — and that is false, because converting `q` is
            // exactly what makes the overlap an `E0499`.
            //
            // The rule the census has to satisfy: **never name a reason whose
            // removal would not unblock the class.** The overlap is
            // unconditional and no later slice retires it, so it is named
            // first. Measured on the g21 fixture, which reported the wrong
            // reason until this pass was split out.
            // `blind` = the compiler cannot see an overlap at this position
            // after conversion. §5a measured the rule: a borrow rooted at a
            // REAL place (a local, or a place through a REFERENCE) is checked;
            // one rooted through a RAW-pointer deref compiles with zero
            // diagnostics. So `&mut (*s).g` is checked exactly when `s` itself
            // converts, and an unknown root is treated as blind.
            let node_positions: Vec<(NodeKey, Option<HirId>, bool, bool)> = site
                .args
                .iter()
                .filter_map(|arg| {
                    if marked_shared.contains(&arg.index) {
                        return None;
                    }
                    let key = param_key
                        .get(&(*callee, arg.index))
                        .copied()
                        .filter(|k| converts.contains(k))?;
                    let blind = match arg.shape {
                        // A reborrow built over an arbitrary raw expression is
                        // outside borrowck's place reasoning. Keep the existing
                        // overlap contract: one mutable position makes an
                        // unknown/may-overlap pair refuse.
                        ArgShape::RawExpr { .. } => true,
                        ArgShape::AddrOf { base: None, .. } => true,
                        ArgShape::AddrOf {
                            base: Some(b),
                            through_deref: true,
                            ..
                        } => !converts.contains(&(b.owner.def_id, b)),
                        _ => false,
                    };
                    Some((key, arg.shape.place_root(), wants_mut[&key], blind))
                })
                .collect();
            for i in 0..node_positions.len() {
                for j in (i + 1)..node_positions.len() {
                    let (a, root_a, mut_a, blind_a) = node_positions[i];
                    let (b, root_b, mut_b, blind_b) = node_positions[j];
                    // Two SHARED borrows of one place are legal, so a conflict
                    // needs at least one `&mut`; H6 measured that demoting the
                    // other side to shared does not rescue it.
                    if !mut_a && !mut_b {
                        continue;
                    }
                    let same_root = !matches!((root_a, root_b), (Some(x), Some(y)) if x != y);
                    let conflicts = match overlap {
                        OverlapRule::BlindOnly => same_root || blind_a || blind_b,
                        OverlapRule::AllPairs => true,
                    };
                    if conflicts {
                        block(&mut node_block, a, BlockReason::DuplicatePlaceRoot);
                        block(&mut node_block, b, BlockReason::DuplicatePlaceRoot);
                    }
                }
            }

            for arg in &site.args {
                // The retained C-9 temp replaces this argument with a fresh
                // shared reference. It therefore contributes neither a
                // duplicate-root conflict nor a caller/callee conversion
                // edge at this site. Every other witness remains unchanged.
                if marked_shared.contains(&arg.index) {
                    continue;
                }
                let callee_subject = param_key.get(&(*callee, arg.index)).copied();
                let callee_node = callee_subject.filter(|k| converts.contains(k));

                // The CALLER side of this argument: the binding whose own
                // conversion this argument would carry.
                // `via_borrow` distinguishes `f(r)` from `f(&mut *r)`. Both
                // put `r`'s value in front of the callee, but only the first
                // can form a class EDGE — a reborrow's type is not the
                // binding's, so joining them would be a category error. The
                // borrow case is a P1 hazard and nothing else.
                let (caller_binding, via_borrow) = match arg.shape {
                    ArgShape::BareLocal(b) | ArgShape::CastOfLocal { binding: b, .. } => {
                        (Some(b), false)
                    }
                    ArgShape::AddrOf { base: Some(b), .. } => (Some(b), true),
                    _ => (None, false),
                };
                let caller_subject = caller_binding
                    .map(|b| (b.owner.def_id, b))
                    .filter(|key| decision_of.contains_key(key));
                let caller_node = caller_subject.filter(|k| converts.contains(k));
                if !via_borrow
                    && let (Some(source), Some(target)) = (caller_subject, callee_subject)
                {
                    edge_candidates.push(EdgeCandidate {
                        source,
                        target,
                        caller: site.caller,
                        callee: *callee,
                        argument_index: arg.index,
                        span: arg.span,
                        source_form: EdgeForm::of(decision_of[&source]),
                        target_form: EdgeForm::of(decision_of[&target]),
                    });
                }

                // (a) the CALLER-side gate — banked rule 2. A converting
                // binding that reaches a parameter which stays raw coerces
                // SILENTLY, so it is caught here or not at all.
                if let Some(caller) = caller_node {
                    let reaches_a_converting_param = callee_node.is_some();
                    if !reaches_a_converting_param {
                        if raw_boundary.opens_argument(caller, arg.span, arg.index) {
                            continue;
                        }
                        // The three arms are DISJOINT, not merely ordered: a
                        // pinned callee's parameters degrade
                        // `call-site-not-adapted` even under `LiftAdaptable`,
                        // so they are never `other_form` either.
                        let reason = if via_borrow {
                            BlockReason::BorrowedIntoRawParam
                        } else if callee_subject.is_some_and(|k| other_form.contains(&k)) {
                            continue;
                        } else if pinned {
                            BlockReason::FlowsIntoPinnedCallee
                        } else {
                            BlockReason::FlowsIntoRawParam
                        };
                        block(&mut node_block, caller, reason);
                    } else if matches!(arg.shape, ArgShape::CastOfLocal { .. }) {
                        // The parameter converts, but the argument casts the
                        // binding on the way in — `q as *mut T` where `q` is
                        // now `&mut T` is a silent coercion in the other
                        // direction, and stripping the cast is task 4's arm.
                        block(&mut node_block, caller, BlockReason::CastOfConvertingLocal);
                    }
                }

                // (b) the CALLEE-side gate — the admissibility table.
                let Some(callee_key) = callee_node else {
                    continue;
                };
                match arg.shape {
                    ArgShape::BareLocal(_) => match caller_node {
                        // The edge. Undirected: converting either alone is
                        // `E0308`, so neither end is the cause of the other.
                        Some(caller) => dsu.union(index[&callee_key], index[&caller]),
                        None if caller_subject.is_some() => {}
                        None => block(&mut node_block, callee_key, BlockReason::ArgStaysRaw),
                    },
                    // `&mut e` satisfies `&mut T` and `&T` alike; `&e` satisfies
                    // only `&T`. Both already coerce to the raw form today,
                    // which is why this arm needs no edit in either direction.
                    ArgShape::AddrOf { mutable, .. } => {
                        if wants_mut[&callee_key] && !mutable {
                            block(&mut node_block, callee_key, BlockReason::ArgSharedIntoMut);
                        }
                    }
                    ArgShape::AddrOfCast { .. } | ArgShape::CastOfLocal { .. } => {
                        block(&mut node_block, callee_key, BlockReason::ArgCastFormUnbuilt);
                    }
                    // Wave 1's type-aware, nameable raw-expression arm. It
                    // forms no caller/callee class edge: an offset/call/field
                    // expression is a value at this site, not the caller
                    // binding's kind identity. The seam and the unchanged
                    // whole-site overlap gate decide its presentation.
                    ArgShape::RawExpr { .. } => {}
                    ArgShape::NullLit => {
                        block(&mut node_block, callee_key, BlockReason::ArgNullLiteral);
                    }
                    ArgShape::Cast { .. } | ArgShape::Other => {
                        block(
                            &mut node_block,
                            callee_key,
                            BlockReason::ArgUnadaptableShape,
                        );
                    }
                }
            }
        }
    }

    // ---- 3. components, then ONE blocked member blocks the class ----
    let mut class_id: FxHashMap<usize, usize> = FxHashMap::default();
    let mut classes: Vec<Class> = Vec::new();
    let mut class_of: FxHashMap<NodeKey, usize> = FxHashMap::default();
    for (i, key) in order.iter().enumerate() {
        let root = dsu.find(i);
        let id = *class_id.entry(root).or_insert_with(|| {
            classes.push(Class {
                members: Vec::new(),
                blocked: None,
            });
            classes.len() - 1
        });
        classes[id].members.push(*key);
        class_of.insert(*key, id);
        if let Some(reason) = node_block.get(key)
            && classes[id].blocked.is_none()
        {
            classes[id].blocked = Some(*reason);
        }
    }

    let settled = |key: NodeKey, form: EdgeForm| {
        if form == EdgeForm::Ref && node_block.contains_key(&key) {
            EdgeForm::Raw
        } else {
            form
        }
    };
    let mut edges = edge_candidates
        .into_iter()
        .map(|edge| {
            let source_form = settled(edge.source, edge.source_form);
            let target_form = settled(edge.target, edge.target_form);
            let route = match (source_form, target_form) {
                (left, right) if left == right => EdgeRoute::ZeroSyntax,
                (EdgeForm::Raw, _) => EdgeRoute::ArmC,
                (_, EdgeForm::Raw) => EdgeRoute::ArmA,
                _ => EdgeRoute::Glue,
            };
            EdgeObligation {
                source: edge.source,
                target: edge.target,
                caller: edge.caller,
                callee: edge.callee,
                argument_index: edge.argument_index,
                span: edge.span,
                source_form,
                target_form,
                route,
            }
        })
        .collect::<Vec<_>>();
    edges.sort_by_key(|edge| {
        (
            edge.caller.local_def_index.as_u32(),
            edge.callee.local_def_index.as_u32(),
            edge.argument_index,
            edge.span.lo(),
            edge.span.hi(),
        )
    });
    edges.dedup_by(|left, right| {
        left.caller == right.caller
            && left.callee == right.callee
            && left.argument_index == right.argument_index
            && left.span == right.span
            && left.source == right.source
            && left.target == right.target
    });

    CoConv {
        class_of,
        classes,
        node_block,
        edges,
    }
}

fn escape_block_reason(
    escape: &Escape,
    lifetime_eligibility: &LifetimeEligibility,
) -> Option<BlockReason> {
    match escape.kind {
        EscapeKind::Return if lifetime_eligibility.return_permit(escape.subject).is_some() => None,
        EscapeKind::Return => Some(BlockReason::EscapesViaReturn),
        EscapeKind::ForeignArg => Some(BlockReason::EscapesViaForeignArg),
        EscapeKind::FieldStore
            if escape.target.is_some_and(|target| {
                lifetime_eligibility.permits_output_storage(escape.subject, target)
            }) =>
        {
            None
        }
        EscapeKind::FieldStore => Some(BlockReason::EscapesViaFieldStore),
        EscapeKind::StaticStore => Some(BlockReason::EscapesViaStaticStore),
    }
}

#[cfg(test)]
fn escape_block_reason_for_test(
    kind: EscapeKind,
    subject: NodeKey,
    lifetime_eligibility: &LifetimeEligibility,
) -> Option<BlockReason> {
    escape_block_reason(
        &Escape {
            subject,
            kind,
            span: rustc_span::DUMMY_SP,
            target: None,
        },
        lifetime_eligibility,
    )
}

// ---------------------------------------------------------------------------
// The escape census — MEASUREMENT ONLY, and the boundary is the point
// ---------------------------------------------------------------------------

/// Where a subject's value can leave the borrow the reference form would give
/// it, **without the compiler objecting**.
///
/// # Why this is measured and not gated
///
/// `&mut T → *mut T` is an implicit coercion at a call argument, a `static mut`
/// store, a field store **and** a return position — all four compile at exit 0
/// (§5a, `probe_coerce.rs`, pinned toolchain). So none of them presents as a
/// revert; they produce no counter movement at all.
///
/// The *call-argument* case is the one S3.6-1 creates, because lifting the gate
/// is what puts converting bindings in front of unconverted parameters. It is
/// gated at decision time, in [`build`], as [`BlockReason::FlowsIntoRawParam`]
/// and [`BlockReason::FlowsIntoPinnedCallee`].
///
/// The other three are **pre-existing and orthogonal**: a parameter of an
/// uncalled function escapes exactly as readily, so the already-emitting 562
/// carry the same shape today. S3.6-1 multiplies the population but does not
/// introduce the class. Gating them here would silently widen this slice's
/// scope into a standing M1 hazard; omitting them would hide the multiplication.
/// The handoff's instruction is to do neither, so they are counted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum EscapeKind {
    /// `G = p` where `G` is a `static mut`.
    StaticStore,
    /// `(*t).f = p`, `t[i] = p` — a store through a place projection.
    FieldStore,
    /// `return p`, or `p` in tail position.
    Return,
    /// An argument to a callee that is **not a local `fn`** — an `extern` block
    /// entry or anything else `call_args` cannot see, so the class test above
    /// structurally cannot reach it.
    ForeignArg,
}

impl EscapeKind {
    pub(crate) fn key(self) -> &'static str {
        match self {
            EscapeKind::StaticStore => "static-store",
            EscapeKind::FieldStore => "field-store",
            EscapeKind::Return => "return",
            EscapeKind::ForeignArg => "foreign-arg",
        }
    }
}

/// One escaping use of one subject.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Escape {
    pub subject: NodeKey,
    pub kind: EscapeKind,
    pub span: Span,
    pub target: Option<NodeKey>,
}

/// Count the escape shapes, per subject, over every subject-bearing function.
///
/// **No silent caps**: a use is classified or it is not an escape; nothing is
/// skipped for being awkward. What the pass does NOT model is stated rather
/// than hidden — a value that reaches a store through an intermediate binding
/// (`let q = p; G = q;`) is attributed to `q`, not to `p`, because this is a
/// syntactic use classifier and not a flow analysis. That under-counts, in the
/// direction that makes the hazard look smaller, which is why the figure is
/// reported as a **lower bound** wherever it is quoted.
pub(crate) fn escapes(
    tcx: TyCtxt<'_>,
    functions: &[LocalDefId],
    subjects: &[Subject],
) -> Vec<Escape> {
    let owned: FxHashSet<NodeKey> = subjects.iter().map(|s| (s.fn_did, s.hir_id)).collect();
    let mut fns: Vec<LocalDefId> = subjects.iter().map(|s| s.fn_did).collect();
    fns.sort_unstable_by_key(|d| d.local_def_index.as_u32());
    fns.dedup();

    struct V<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        fn_did: LocalDefId,
        owned: &'a FxHashSet<NodeKey>,
        /// The **same list** `emitability::collect` was handed, so "a callee
        /// the class machinery can see" means one thing in both places.
        locals: &'a [LocalDefId],
        /// The body's tail expression, if it has one: `p` in tail position is a
        /// return without the keyword, and treating only `Ret` would miss it.
        tail: Option<HirId>,
        out: &'a mut Vec<Escape>,
    }

    impl<'tcx> Visitor<'tcx> for V<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            if let ExprKind::Path(QPath::Resolved(_, path)) = &expr.kind
                && let Res::Local(hir_id) = path.res
                && self.owned.contains(&(self.fn_did, hir_id))
                && let Some(kind) = self.classify(expr)
            {
                let target = (kind == EscapeKind::FieldStore)
                    .then(|| self.field_store_target(expr))
                    .flatten();
                self.out.push(Escape {
                    subject: (self.fn_did, hir_id),
                    kind,
                    span: expr.span,
                    target,
                });
            }
            intravisit::walk_expr(self, expr);
        }
    }

    impl V<'_, '_> {
        fn field_store_target(&self, use_expr: &Expr<'_>) -> Option<NodeKey> {
            let rustc_hir::Node::Expr(parent) = self.tcx.parent_hir_node(use_expr.hir_id) else {
                return None;
            };
            let ExprKind::Assign(lhs, rhs, _) = &parent.kind else {
                return None;
            };
            if rhs.hir_id != use_expr.hir_id {
                return None;
            }
            let ExprKind::Unary(rustc_hir::UnOp::Deref, base) = &lhs.kind else {
                return None;
            };
            let ExprKind::Path(QPath::Resolved(_, path)) = &base.kind else {
                return None;
            };
            let Res::Local(binding) = path.res else {
                return None;
            };
            Some((self.fn_did, binding))
        }

        /// Is this callee one the class machinery can actually see?
        ///
        /// **Membership in the program's function list, not `DefId` locality.**
        /// A `fn` declared in an `extern "C" { … }` block has a `DefKind::Fn`
        /// and a perfectly LOCAL `DefId`, so an `as_local()` test calls
        /// `memcpy` a local function and reports zero foreign escapes. Measured
        /// — the witness for this arm failed on exactly that, which is why the
        /// predicate now consults the same list `emitability::collect` filters
        /// its call arm by rather than a second test that looks equivalent.
        fn is_visible_callee(&self, callee: &Expr<'_>) -> bool {
            let ExprKind::Path(QPath::Resolved(_, path)) = &callee.kind else {
                return false;
            };
            matches!(
                path.res,
                Res::Def(rustc_hir::def::DefKind::Fn, did)
                    if did.as_local().is_some_and(|d| self.locals.contains(&d))
            )
        }

        fn classify(&self, use_expr: &Expr<'_>) -> Option<EscapeKind> {
            if self.tail == Some(use_expr.hir_id) {
                return Some(EscapeKind::Return);
            }
            let rustc_hir::Node::Expr(parent) = self.tcx.parent_hir_node(use_expr.hir_id) else {
                return None;
            };
            match &parent.kind {
                ExprKind::Ret(Some(value)) if value.hir_id == use_expr.hir_id => {
                    Some(EscapeKind::Return)
                }
                ExprKind::Assign(lhs, rhs, _) if rhs.hir_id == use_expr.hir_id => {
                    match &lhs.kind {
                        ExprKind::Path(QPath::Resolved(_, p))
                            if matches!(
                                p.res,
                                Res::Def(rustc_hir::def::DefKind::Static { .. }, _)
                            ) =>
                        {
                            Some(EscapeKind::StaticStore)
                        }
                        ExprKind::Field(..)
                        | ExprKind::Index(..)
                        | ExprKind::Unary(rustc_hir::UnOp::Deref, _) => {
                            Some(EscapeKind::FieldStore)
                        }
                        // A store into another LOCAL is not an escape: the
                        // target is itself a subject or a raw local in the same
                        // body, and either way nothing leaves the function.
                        _ => None,
                    }
                }
                // A FOREIGN callee. The local-fn case is `build`'s, and routing
                // it here as well would double-count the one flow that IS gated.
                ExprKind::Call(callee, args)
                    if args.iter().any(|a| a.hir_id == use_expr.hir_id)
                        && !self.is_visible_callee(callee) =>
                {
                    Some(EscapeKind::ForeignArg)
                }
                _ => None,
            }
        }
    }

    let mut out = Vec::new();
    for fn_did in fns {
        let Some(body_id) = tcx.hir_node_by_def_id(fn_did).body_id() else {
            continue;
        };
        let body = tcx.hir_body(body_id);
        let tail = match &body.value.kind {
            ExprKind::Block(block, _) => block.expr.map(|e| e.hir_id),
            _ => Some(body.value.hir_id),
        };
        let mut v = V {
            tcx,
            fn_did,
            owned: &owned,
            locals: functions,
            tail,
            out: &mut out,
        };
        v.visit_body(body);
    }
    out
}

#[cfg(test)]
mod e2_return_permit_tests {
    use rustc_hir::{CRATE_HIR_ID, def_id::CRATE_DEF_ID};

    use super::*;
    use crate::bo_rewriter::decision::lifetime::LifetimeEligibility;

    #[test]
    fn e2_return_permit_skips_only_the_named_return_escape() {
        let subject = (CRATE_DEF_ID, CRATE_HIR_ID);
        let permitted = LifetimeEligibility::with_return_permit_for_test(subject);
        let empty = LifetimeEligibility::default();

        assert_eq!(
            escape_block_reason_for_test(EscapeKind::Return, subject, &permitted),
            None
        );
        assert_eq!(
            escape_block_reason_for_test(EscapeKind::Return, subject, &empty),
            Some(BlockReason::EscapesViaReturn)
        );
        assert_eq!(
            escape_block_reason_for_test(EscapeKind::ForeignArg, subject, &permitted),
            Some(BlockReason::EscapesViaForeignArg)
        );
        assert_eq!(
            escape_block_reason_for_test(EscapeKind::FieldStore, subject, &permitted),
            Some(BlockReason::EscapesViaFieldStore)
        );
        assert_eq!(
            escape_block_reason_for_test(EscapeKind::StaticStore, subject, &permitted),
            Some(BlockReason::EscapesViaStaticStore)
        );
    }
}

#[cfg(test)]
mod pair_plan_tests {
    use super::*;
    use super::super::a5_site_proof::A5SiteProofVerdict;

    #[test]
    fn pair_w1_clear_component_keeps_every_position_safe() {
        assert_eq!(
            resolve_pair_roles_for_test(&[
                (0, 1, A5SiteProofVerdict::Clear, false),
                (1, 0, A5SiteProofVerdict::Clear, false),
            ]),
            ["clear", "clear"]
        );
    }

    #[test]
    fn pair_w2_overlap_chooses_one_primary_and_one_raw_view() {
        assert_eq!(
            resolve_pair_roles_for_test(&[
                (0, 1, A5SiteProofVerdict::Overlapping, false),
                (1, 0, A5SiteProofVerdict::Overlapping, false),
            ]),
            ["primary", "raw-view"]
        );
    }

    #[test]
    fn pair_w3_three_way_component_has_one_canonical_primary() {
        assert_eq!(
            resolve_pair_roles_for_test(&[
                (2, 0, A5SiteProofVerdict::Overlapping, false),
                (0, 2, A5SiteProofVerdict::Overlapping, false),
                (1, 2, A5SiteProofVerdict::Overlapping, false),
            ]),
            ["primary", "raw-view", "raw-view"]
        );
    }

    #[test]
    fn pair_n1_unknown_is_never_mapped_to_clear() {
        assert_eq!(
            resolve_pair_roles_for_test(&[
                (0, 1, A5SiteProofVerdict::Undeterminable, false),
                (1, 0, A5SiteProofVerdict::Undeterminable, false),
            ]),
            ["blocked", "blocked"]
        );
    }

    #[test]
    fn pair_positive_retention_selects_the_retaining_position_as_primary() {
        assert_eq!(
            resolve_pair_roles_for_test(&[
                (0, 1, A5SiteProofVerdict::Overlapping, false),
                (1, 0, A5SiteProofVerdict::Overlapping, true),
            ]),
            ["raw-view", "primary"]
        );
    }
}
