//! **Type-directed seam adapters** at mismatched argument positions.
//!
//! S3.6-1 converts a callee's parameter and the caller's binding *jointly* where
//! the co-conversion class links them. Where the class graph has no edge, the
//! two ends convert independently and the argument position is left ill-typed —
//! measured at 2,950 positions, **100 % `E0308`**, which is the whole of the
//! 95.7 % revert load.
//!
//! A seam adapter is one expression of glue at that position, bridging the form
//! the caller supplies to the form the callee now expects.
//!
//! # Two families, and the exposure the reborrow one carries
//!
//! - **Safe** — `Some(x)`, `x.unwrap()`, `slice::from_mut/from_ref`, `&mut x[0]`
//!   and their compositions. No `unsafe`, compiler-checked end to end.
//! - **Reborrow** — `&mut *p` / `&*p`. One expression, borrow scoped to the
//!   call.
//!
//! **The reborrow family is placed exactly where the compiler stops checking
//! aliasing** (`-1` micro-plan §5a, the inversion finding): `two_mut(&mut v,
//! &mut v)` on a real local is `E0499`, but through a raw base it compiles with
//! zero diagnostics. That is why the site gates — `duplicate-place-root` and P2
//! `BlindOnly` — apply to adapter-generated arguments **exactly as to converted
//! ones**, with no bypass. A gate that skipped glue would move the argument from
//! the checked region into the unchecked one and book it as yield.
//!
//! # Slice seams are length-gated, and no length is ever fabricated
//!
//! `*mut T → &[T]` needs a length. `slice::from_raw_parts` with an oversized
//! `len` is **UB at construction** by its own safety contract — not on first
//! out-of-bounds read — so a guessed constant is unsound the moment it is built.
//! Those positions gate under [`SeamBlock::LengthUnknown`] until a length source
//! is proven. **65.7 % of the measured market sits behind that gate**, which is
//! why it is a first-class outcome here rather than a `None`.

use std::collections::{BTreeMap, BTreeSet};

use rustc_span::Span;

use super::a5_site_proof::{A5PeerProof, A5SeamProofIndex, A5SiteProofVerdict};
use crate::bo_rewriter::bridge_receipt::{
    BridgeCalleeId, BridgeExtentKind, BridgeRetentionTier, BridgeSitePlan,
    RAW_BOUNDARY_T2_WAIVER_ID, SignatureClassId,
};

/// The pointer-ish form a value has at an argument position.
///
/// `Raw` carries no mutability: the glue's mutability follows the **expected**
/// side. `&*p` is well-formed on a `*mut T` and `&mut *p` is not obtainable from
/// a `*const T` at all, so reading the raw side's constness would only let a
/// caller ask for something the callee's own converted type already forbids.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Form {
    Raw,
    Ref { mutable: bool },
    Slice { mutable: bool },
    Opt { mutable: bool, slice: bool },
}

impl Form {
    pub(crate) fn key(self) -> &'static str {
        match self {
            Form::Raw => "raw",
            Form::Ref { mutable: true } => "ref-mut",
            Form::Ref { mutable: false } => "ref-shared",
            Form::Slice { mutable: true } => "slice-mut",
            Form::Slice { mutable: false } => "slice-shared",
            Form::Opt {
                mutable: true,
                slice: true,
            } => "opt-slice-mut",
            Form::Opt {
                mutable: false,
                slice: true,
            } => "opt-slice-shared",
            Form::Opt {
                mutable: true,
                slice: false,
            } => "opt-ref-mut",
            Form::Opt {
                mutable: false,
                slice: false,
            } => "opt-ref-shared",
        }
    }
}

/// Why a position could not be adapted. **A first-class outcome**, never a
/// silent skip — an unadapted position is a revert, and a revert with no reason
/// is a yield number nobody can attribute.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SeamBlock {
    /// A slice form is expected and the argument is raw: a length is needed and
    /// **none may be invented**. Ruling item 4.
    LengthUnknown,
    /// `&mut T` expected, a shared borrow supplied. Not upgradable.
    SharedToMut,
    /// The argument's expression is not one this slice can name — a bare cast, a
    /// null literal, a call result, arithmetic.
    UnnameableOperand,
    /// An optional source cannot satisfy a required target without a positive
    /// non-null/nonempty proof. Wave 2 has no such proof at this seam, so it
    /// never inserts an unchecked or panicking unwrap.
    NullabilityInsufficient,
    /// Two positions at one call site may borrow the same place, and at least
    /// one wants `&mut`. **The gate applies to adapter-generated arguments
    /// exactly as to converted ones** (ruling item 3, 2026-08-11): glue may not
    /// bypass it, because the reborrow family places its borrow precisely where
    /// §5a measured borrowck as blind.
    SiteOverlap,
    /// The converted callee is known to retain this parameter. A call-scoped
    /// raw-to-safe bridge cannot license a reference that escapes the call.
    PositiveRetention,
    /// A slice cannot be projected to a required thin reference without a
    /// carried proof that the slice has at least one element.
    NonemptyUnknown,
    /// A raw expression cannot enter a safe return without the typed origin
    /// permit that supplies the emitted return lifetime.
    ReturnLifetimeAbsent,
}

impl SeamBlock {
    pub(crate) fn key(self) -> &'static str {
        match self {
            SeamBlock::LengthUnknown => "seam-len-unknown",
            SeamBlock::SharedToMut => "seam-shared-to-mut",
            SeamBlock::UnnameableOperand => "seam-unnameable-operand",
            SeamBlock::NullabilityInsufficient => "glue-nullability-insufficient",
            SeamBlock::SiteOverlap => "seam-site-overlap",
            SeamBlock::PositiveRetention => "seam-positive-retention",
            SeamBlock::NonemptyUnknown => "seam-nonempty-unknown",
            SeamBlock::ReturnLifetimeAbsent => "return-lifetime-permit-absent",
        }
    }
}

/// What the callee's own signature says about a companion length.
///
/// Measured on the SIGNATURE rather than the call site, because the C idiom
/// this is looking for — `void f(int *buf, size_t len)` — is a property of the
/// declaration: every caller of such a function supplies the length in the same
/// position, so the signature answers for all of them at once.
///
/// **Adjacency is evidence, not proof.** `f(dst, src, n)` has an integer in the
/// position after `src` that is the length of BOTH pointers, and `f(p, flags)`
/// has one that is a length of nothing. This enum records what was seen; it
/// does not certify a length, and no seam is placed from it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LenEvidence {
    /// An integer-typed parameter immediately AFTER the pointer — the dominant
    /// C spelling.
    Following,
    /// An integer-typed parameter immediately BEFORE it.
    Preceding,
    /// An integer parameter exists somewhere in the signature, but not adjacent.
    Elsewhere,
    /// The signature carries no integer parameter at all. **A length cannot come
    /// from the call site**, so such a position can only ever be served by
    /// certified `approx-len` (U-2') or stay gated.
    None,
}

impl LenEvidence {
    pub(crate) fn key(self) -> &'static str {
        match self {
            LenEvidence::Following => "len-following",
            LenEvidence::Preceding => "len-preceding",
            LenEvidence::Elsewhere => "len-elsewhere",
            LenEvidence::None => "len-absent",
        }
    }
}

/// **Which arm produced a placed slice seam's length** — the ruled audit tag
/// (user ruling 2026-08-12, marker ruled 2026-08-15).
///
/// A two-arm type rather than a `bool` beside the evidence, so a fabricated site
/// can never be counted inside the licensed 277 by accident. `Fabricated`
/// carries the signature evidence that WAS available, because
/// bound-verification's derivability question is exactly `Elsewhere` (a
/// non-adjacent integer exists) vs `None` (none does).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LenArm {
    /// Ruling B adjacency evidence — the length is the caller's own companion.
    Licensed(LenEvidence),
    /// FABRICATED. The placeholder was placed where no companion exists.
    Fabricated(LenEvidence),
}

impl LenArm {
    pub(crate) fn key(self) -> &'static str {
        match self {
            // **Byte-identical to the pre-ruling column for all 277 licensed
            // placements** — the licensed population's artifact bytes do not
            // move, which is what makes the fabricated count a clean addition
            // rather than a re-keying.
            LenArm::Licensed(e) => e.key(),
            LenArm::Fabricated(_) => "len-fabricated",
        }
    }

    /// The signature evidence, whichever arm placed the length. The
    /// `lengated` rows read this so the `len-elsewhere` / `len-absent` split
    /// survives fabrication as bound-verification's derivability input.
    pub(crate) fn evidence(self) -> LenEvidence {
        match self {
            LenArm::Licensed(e) | LenArm::Fabricated(e) => e,
        }
    }
}

/// **A slice seam's length, WITH ITS PROVENANCE** (marker ruling, 2026-08-15).
///
/// The provenance rides *in* the value rather than beside it, so "fabricate
/// without tagging it" is not expressible **in the emitted text**.
///
/// ⚠ **That was originally claimed for the ARTIFACT too, and it was false.**
/// `synthesize` decided the audit arm by its own `match` on the companion text,
/// so the tag and the length were two expressions reading one variable — they
/// agreed by coincidence, and forcing the tag one way left the emitted text
/// untouched with the whole suite green (ADV-FAB-01). Repaired 2026-08-15: the
/// arm is derived from this field after `glue` answers, so the claim now holds
/// because of the code rather than in spite of it. The prefix-testing
/// `glue_shape` classifier was retired for the same reason — a second derivation
/// of a fact the decision already holds is a defect waiting for a mutation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum SeamLen {
    /// The caller's own companion argument text (ruling B adjacency).
    Licensed(String),
    /// The fabricated placeholder, rendered as the named const the emitter
    /// inserts. Carries no text because there is none to carry — which is the
    /// point.
    Fabricated,
}

impl SeamLen {
    /// The length's source text. **The single place both emitters read it
    /// from**, so the span layer's string and the AST layer's parsed node come
    /// from one derivation rather than two spellings of the same const.
    pub(crate) fn text(&self) -> &str {
        match self {
            SeamLen::Licensed(t) => t,
            SeamLen::Fabricated => FABRICATED_LEN_PATH,
        }
    }

    pub(crate) fn is_fabricated(&self) -> bool {
        matches!(self, SeamLen::Fabricated)
    }
}

/// The one ruled fallback slice extent (§39 addendum 77). This is the numeric
/// source of truth for call-site adapters and the existing borrowed-slice
/// emission path alike.
pub(crate) const FALLBACK_SLICE_EXTENT: usize = 1024;

/// The const's name in the emitted crate (marker ruling, 2026-08-15).
pub(crate) const SEAM_LEN_CONST: &str = "FALLBACK_SLICE_EXTENT";

/// The path a fabricated extent is spelled as at the call site.
///
/// Crate-qualified so a fabricated site in a non-root file resolves — the
/// spelling the frozen legacy rewriter already used for `crate::slice_cursor::`.
pub(crate) const FABRICATED_LEN_PATH: &str = "crate::FALLBACK_SLICE_EXTENT";

/// **The const item, as emitted text — produced from a real AST item.**
///
/// The marker ruling says *named const via `item!`*, and this is that: the text
/// is `pprust`'s rendering of a node the parser accepted, not a hand-written
/// string that merely looks like Rust. A typo in a string blob would reach the
/// emitted crate and fail at the callers' `verify`, attributed to them; a typo
/// here fails at `parse_item`, attributed to itself.
///
/// The parsed node is **printed and discarded**, never inserted into a krate, so
/// the fresh-`ParseSess` span-aliasing hazard cannot follow it — the node's spans
/// never leave this function.
///
/// One producer, two consumers: the span layer splices this string and the AST
/// layer appends it, so the two emitters cannot disagree about the const's text.
pub(crate) fn fabricated_len_item() -> String {
    let item = ::utils::item!("const {SEAM_LEN_CONST}: usize = {FALLBACK_SLICE_EXTENT};");
    rustc_ast_pretty::pprust::item_to_string(&item)
}

/// Which family a placed adapter came from. Reported in the artifacts' seam
/// column so the reborrow population — the one carrying the aliasing exposure —
/// stays countable on its own.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SeamFamily {
    Safe,
    Reborrow,
}

/// One placed adapter.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SeamEdit {
    /// The **argument expression's** span, in the CALLER's file.
    pub span: Span,
    /// Whole call expression used only for class attribution.
    pub call_span: Span,
    pub replacement: String,
    /// Direct identity of the converted signature class. This is the sole
    /// ownership key used by verification; `owner_fn` is display-only.
    pub owner_class: SignatureClassId,
    pub bridge: BridgeSitePlan,
    /// The callee subject whose conversion justifies this edit — the revert key.
    /// The edit lands in the caller's file and is owned by the callee, which is
    /// the divergence `plan`'s `owner_fn` doc was written for.
    pub owner_fn: String,
    /// Digest of the callee's finalized E2 signature plan. `None` means this
    /// seam is unrelated to E2; it may never be reconstructed downstream.
    pub lifetime_plan_digest: Option<String>,
    /// The caller side of `CallAdapterKey`.
    pub caller_fn: String,
    /// The callee's zero-based parameter position.
    pub param_index: usize,
    /// The HIR argument classifier's carried answer. This is receipt-only; no
    /// consumer re-infers the source shape from replacement text.
    pub source_shape: &'static str,
    pub family: SeamFamily,
    /// **Which adjacency arm licensed this slice seam's length** (ruling B,
    /// 2026-08-11). `None` for every non-slice seam, which needs no length.
    ///
    /// Carried NOW rather than added when the bound-verification follow-up runs:
    /// that check certifies or corrects each selection, and it can only be
    /// surgical if it can tell a `following` selection from a `preceding` one
    /// without re-deriving the choice.
    /// **Fabricated placements ride the same field, tagged** (2026-08-15), so
    /// the licensed 277 and the fabricated 93 are one vocabulary in two arms —
    /// never one blended count.
    pub len_arm: Option<LenArm>,
    /// **The adapter, DESCRIBED** — option A's carried interface (2026-08-13).
    ///
    /// [`Self::replacement`] is `spec.render(<the argument's source text>)`, so
    /// the two are redundant *by construction* and the span layer keeps reading
    /// the string. The AST layer reads this instead, because it cannot rebuild a
    /// wrapper from a rendered string without re-parsing the argument it was
    /// told to keep as a subtree.
    pub spec: GlueSpec,
    /// **The span whose TEXT the replacement was built from** — which is NOT
    /// always [`Self::span`].
    ///
    /// `span` is the whole argument and is what the span layer overwrites. For
    /// the two cast shapes (`AddrOfCast`, `CastOfLocal`) the decision layer
    /// builds the replacement from the cast's OPERAND (`ArgShape`'s `inner`),
    /// so the surviving subtree is nested one level inside the replaced node.
    ///
    /// Carried rather than re-derived: an AST layer that peeled casts by
    /// pattern would be guessing at exactly the point where the span layer
    /// already knows, and a `Paren` between the cast and its operand would make
    /// the guess silently wrong.
    pub arg_span: Span,
    /// Candidate facts retained for the common receipt schema.
    pub expected: Form,
    pub found: Form,
    pub root_identity: String,
    pub blind: bool,
    /// The attested site proof that discharged the conservative overlap gate.
    /// `None` means this position never needed that gate.
    pub overlap: Option<A5PositionProof>,
    /// Raw-boundary subject/site dependency group. Empty for every older seam
    /// family; populated once by the decision layer and never inferred from
    /// replacement text.
    pub atom_ids: Vec<String>,
}

/// One placed initializer/assignment adapter. It deliberately carries the
/// same `GlueSpec`/family pair as [`SeamEdit`]; only ownership and context
/// differ.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BodyEdit {
    pub span: Span,
    pub replacement: String,
    pub owner_class: SignatureClassId,
    pub bridge: BridgeSitePlan,
    pub owner_fn: String,
    pub destination: String,
    pub context: super::emitability::BodyAdapterContext,
    pub source_shape: &'static str,
    pub family: SeamFamily,
    pub spec: GlueSpec,
    pub arg_span: Span,
    pub expected: Form,
    pub found: Form,
    pub root_identity: String,
    pub blind: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PeerConflict {
    pub left: usize,
    pub right: usize,
    pub same_root: bool,
    pub left_blind: bool,
    pub right_blind: bool,
    pub proof: A5PeerProof,
}

/// One position-level aggregation of all peer proofs consulted by the seam.
/// Carried into both placed and blocked receipts; a clear no-op candidate also
/// remains in `SeamPlan::overlap_proofs` so it cannot vanish from the control.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct A5PositionProof {
    pub caller: LocalDefId,
    pub callee: LocalDefId,
    pub index: usize,
    pub span: Span,
    pub candidate_template: String,
    pub verdict: A5SiteProofVerdict,
    pub reason: String,
    pub locations: String,
    pub peer_receipts: String,
    pub world: &'static str,
    pub guard: &'static str,
}

impl A5PositionProof {
    fn from_conflicts(
        caller: LocalDefId,
        callee: LocalDefId,
        index: usize,
        span: Span,
        candidate_template: String,
        conflicts: &[PeerConflict],
        proofs: &A5SeamProofIndex,
    ) -> Self {
        debug_assert!(!conflicts.is_empty());
        let verdict = if conflicts
            .iter()
            .any(|conflict| conflict.proof.verdict == A5SiteProofVerdict::Overlapping)
        {
            A5SiteProofVerdict::Overlapping
        } else if conflicts
            .iter()
            .any(|conflict| conflict.proof.verdict == A5SiteProofVerdict::Undeterminable)
        {
            A5SiteProofVerdict::Undeterminable
        } else {
            A5SiteProofVerdict::Clear
        };
        let reason = match verdict {
            A5SiteProofVerdict::Clear => "all-peers-clear".to_owned(),
            A5SiteProofVerdict::Overlapping => "at-least-one-peer-overlapping".to_owned(),
            A5SiteProofVerdict::Undeterminable => conflicts
                .iter()
                .filter(|conflict| conflict.proof.verdict == A5SiteProofVerdict::Undeterminable)
                .map(|conflict| conflict.proof.reason)
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>()
                .join(";"),
        };
        let locations = conflicts
            .iter()
            .map(|conflict| conflict.proof.location_key())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>()
            .join(";");
        let peer_receipts = conflicts
            .iter()
            .map(|conflict| conflict.proof.receipt(conflict.left, conflict.right))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>()
            .join(";");
        Self {
            caller,
            callee,
            index,
            span,
            candidate_template,
            verdict,
            reason,
            locations,
            peer_receipts,
            world: proofs.world(),
            guard: proofs.guard(),
        }
    }

    fn clears_site_overlap(&self) -> bool {
        self.verdict == A5SiteProofVerdict::Clear
    }
}

impl PeerConflict {
    pub(crate) fn key(&self) -> String {
        format!(
            "{}/{}[same_root={},left_blind={},right_blind={}]",
            self.left,
            self.right,
            u8::from(self.same_root),
            u8::from(self.left_blind),
            u8::from(self.right_blind)
        )
    }
}

/// A call position rejected after candidate construction. Strings are carried
/// here so the receipt never re-derives a form from emitted text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BlockedSeam {
    pub caller: LocalDefId,
    pub callee: LocalDefId,
    pub index: usize,
    pub span: Span,
    pub block: SeamBlock,
    pub expected: Option<Form>,
    pub found: Option<Form>,
    pub source_shape: &'static str,
    pub candidate_template: String,
    pub null_arm: String,
    pub extent_arm: String,
    pub root_identity: String,
    pub blind: bool,
    pub peers: Vec<PeerConflict>,
    pub overlap: Option<A5PositionProof>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BodyBlock {
    SideEffectingRhs,
    UnnameableRhs,
    NullRequiredRef,
    SharedToMut,
    RenderRefused,
}

impl BodyBlock {
    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::SideEffectingRhs => "body-side-effecting-rhs",
            Self::UnnameableRhs => "body-unnameable-rhs",
            Self::NullRequiredRef => "body-null-required-ref",
            Self::SharedToMut => "body-shared-to-mut",
            Self::RenderRefused => "body-render-refused",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BlockedBody {
    pub owner_class: SignatureClassId,
    pub owner_fn: String,
    pub destination: String,
    pub span: Span,
    pub context: super::emitability::BodyAdapterContext,
    pub block: BodyBlock,
    pub expected: Form,
    pub found: Option<Form>,
    pub source_shape: &'static str,
    pub candidate_template: Option<&'static str>,
    pub root_identity: String,
    pub blind: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BlockedRawBoundary {
    pub owner_class: SignatureClassId,
    pub bridge: BridgeSitePlan,
    pub span: Span,
    pub reason: String,
}

/// Final explicit type for a source or generated declaration whose surrounding
/// inference context changes with its signature class. The type is selected in
/// the decision phase and consumed verbatim by both receipt and AST emission.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ExplicitDeclarationSite {
    pub owner_class: SignatureClassId,
    pub caller: LocalDefId,
    pub node: Option<(LocalDefId, HirId)>,
    pub span: Option<Span>,
    pub category: &'static str,
    pub emitted_type: String,
    pub replacement: Option<String>,
    pub arm: &'static str,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ZeroBridgeSite {
    pub owner_class: SignatureClassId,
    pub caller: LocalDefId,
    pub span: Option<Span>,
    pub arm: &'static str,
    pub position: String,
    pub bridge_kind: &'static str,
    pub retention: BridgeRetentionTier,
    pub waiver_id: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PairRawViewTemp {
    pub argument_index: usize,
    pub raw_expression: String,
    pub target_type: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PairRawViewCall {
    pub owner_class: SignatureClassId,
    pub caller: LocalDefId,
    pub callee: LocalDefId,
    pub call_span: Span,
    pub views: Vec<PairRawViewTemp>,
    pub reasons: Vec<String>,
    pub atom_ids: Vec<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct InterfaceInventoryKey {
    pub(crate) caller: SignatureClassId,
    pub(crate) callee: SignatureClassId,
    pub(crate) block: u32,
    pub(crate) argument_index: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct InterfaceInventorySite {
    pub(crate) key: InterfaceInventoryKey,
    pub(crate) call_span: Span,
    pub(crate) argument_span: Span,
    pub(crate) source_shape: &'static str,
    pub(crate) non_subject: bool,
    pub(crate) disposition: &'static str,
}

/// **The authorization rule for fabrication, as a pure function** (R8).
///
/// One place decides *licensed vs fabricated*, and it decides it from the only
/// input that may decide it: whether the call site supplied a companion length.
/// Lifted out of `glue`'s two arms rather than written twice, because two copies
/// of an authorization rule is one copy too many — and because a rule inside a
/// match arm is a rule only a corpus sweep can exercise.
///
/// **This is the whole of "fabricate exactly when authorized":** a `Some` input
/// can only produce `Licensed`, a `None` input can only produce `Fabricated`,
/// and neither can produce the other.
fn with_length(spec: GlueSpec, len: Option<&str>) -> GlueSpec {
    match len {
        Some(text) => spec.with_len(text),
        None => spec.with_fabricated_len(),
    }
}

/// `&mut ` or `&`.
fn amp(mutable: bool) -> &'static str {
    if mutable { "&mut " } else { "&" }
}

/// Unwrap an optional **without consuming it**.
///
/// `Option<&T>` is `Copy`, so a plain `.unwrap()` leaves the binding usable.
/// **`Option<&mut T>` is not**, and `.unwrap()` MOVES it — a caller that passes
/// the same optional to two calls would compile before the rewrite and fail
/// `E0382` after, which is a rewrite that breaks a working program.
///
/// `.as_mut().unwrap()` yields `&mut &mut T`, which deref-coerces to `&mut T` at
/// the argument position and borrows rather than moves.
///
/// **Compile-verified on the pinned toolchain, twice-in-one-body**, because the
/// single-use spelling passes and the defect only appears on the second use.
/// The moving form was written first and caught by compiling, not by review.
fn unwrap_expr(text: &str, mutable: bool) -> String {
    if mutable {
        format!("{text}.as_mut().unwrap()")
    } else {
        format!("{text}.unwrap()")
    }
}

/// **THE GLUE SPEC — the reification ruled at the arm-3 boundary (2026-08-13).**
///
/// Glue used to be manufactured as TEXT here and consumed as text downstream.
/// The AST application layer cannot build a node from a rendered string without
/// re-parsing the argument it was told to keep as a subtree — the round-trip
/// arm 1 declined — so the shape the decision layer already knew is now
/// CARRIED rather than re-derived.
///
/// **Reification only.** No decision, gate, family or position-walk change: the
/// spec is computed at exactly the sites that already computed the string, and
/// [`GlueSpec::render`] reproduces that string byte-for-byte. That equality is
/// GATED, not asserted — see `render_is_byte_identical_to_the_frozen_glue_text`.
///
/// The dependency arrow runs application→decision: this type lives here, and
/// the AST layer consumes it. The import denylist is untouched.
///
/// Every arm of [`glue`] is one point in a small algebra —
/// `[Some(] core([unwrap(] text [)]) [)]` — which is why five cores suffice for
/// all fourteen emitting arms.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum GlueCore {
    /// `X` — the argument unchanged (the payload already fits).
    Bare,
    /// `&mut *X` / `&*X`
    Reborrow,
    /// `unsafe { X.as_mut() }` / `unsafe { X.as_ref() }` for a nullable raw
    /// pointer crossing into an optional safe parameter.
    RawOption,
    /// `X.first().unwrap()` / `X.first_mut().unwrap()` under a carried
    /// nonempty contract.
    First,
    /// `&mut X[0]` / `&X[0]`
    Index0,
    /// `core::slice::from_raw_parts{_mut}(X, (LEN) as usize)`
    FromRawParts,
    /// `core::slice::from_mut(X)` / `core::slice::from_ref(X)`
    FromRefMut,
}

/// How an optional TARGET treats null at the call boundary.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum NullArm {
    /// Not a raw-to-optional boundary. `optional=true` still means a known-safe
    /// reference/slice is wrapped in `Some`.
    None,
    /// The source expression is a raw pointer. Evaluate it once, test
    /// `is_null`, and construct the payload only on the non-null branch.
    Checked,
    /// The raw pointer's `as_ref`/`as_mut` API performs the null-to-Option
    /// mapping directly and evaluates the receiver once.
    PointerApi,
    /// The source expression is syntactically a null literal.
    LiteralNone,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RawBoundaryGlue {
    pub template: super::raw_boundary::BridgeTemplate,
    pub target_mutability: super::raw_boundary::RawMutability,
    pub box_slice: bool,
    pub force_explicit: bool,
    pub cast_pointee: Option<String>,
}

/// One adapter, described rather than rendered.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct GlueSpec {
    pub core: GlueCore,
    /// The EXPECTED side's mutability — selects `&`/`&mut` and
    /// `from_ref`/`from_mut`.
    pub mutable: bool,
    /// The unwrap that precedes the core when the FOUND side is optional.
    /// `Some(true)` is `.as_mut().unwrap()`, `Some(false)` is `.unwrap()` —
    /// the distinction `unwrap_expr` exists for, carried rather than inferred.
    pub unwrap: Option<bool>,
    /// The length, `FromRawParts` only, **with its provenance**.
    ///
    /// The held fabricated-length slice landed HERE, exactly as this doc
    /// predicted, rather than at a string substitution. `None` still means
    /// refused — but after the 2026-08-12 ruling `glue` no longer produces it
    /// for the two length-needing arms, which fabricate instead. What `None`
    /// now guards is the layer BELOW the gate: a builder handed a length-less
    /// `FromRawParts` still places nothing.
    pub len: Option<SeamLen>,
    /// Wrap the result in `Some(...)`.
    pub optional: bool,
    /// The §29 boundary behavior. Separate from `optional`: a safe reference
    /// uses ordinary `Some`, while a raw expression must be checked.
    pub null_arm: NullArm,
    /// Raw-boundary wave-1's explicit safe-to-raw form. Kept inside the seam
    /// algebra so span and AST consumers share one carried template.
    pub raw_boundary: Option<RawBoundaryGlue>,
    pub nonempty_evidence: bool,
    /// Exact source type for the one-evaluation local introduced by a checked
    /// nullable bridge. `None` means this spec introduces no local.
    pub checked_binding_type: Option<String>,
}

impl GlueSpec {
    pub(crate) fn core(core: GlueCore, mutable: bool) -> Self {
        Self {
            core,
            mutable,
            unwrap: None,
            len: None,
            optional: false,
            null_arm: NullArm::None,
            raw_boundary: None,
            nonempty_evidence: false,
            checked_binding_type: None,
        }
    }

    pub(crate) fn with_unwrap(mut self, found_mutable: bool) -> Self {
        self.unwrap = Some(found_mutable);
        self
    }

    pub(crate) fn with_len(mut self, len: &str) -> Self {
        self.len = Some(SeamLen::Licensed(len.to_owned()));
        self
    }

    /// **The fabricated extent** (user ruling 2026-08-12; marker 2026-08-15).
    ///
    /// Deliberately a *separate* constructor from [`Self::with_len`] rather than
    /// a flag on it: the two produce different emitted text and different
    /// artifact rows, and a caller must name which one it means.
    pub(crate) fn with_fabricated_len(mut self) -> Self {
        self.len = Some(SeamLen::Fabricated);
        self
    }

    pub(crate) fn wrapped(mut self) -> Self {
        self.optional = true;
        self
    }

    pub(crate) fn checked(mut self) -> Self {
        self.optional = true;
        self.null_arm = NullArm::Checked;
        self
    }

    pub(crate) fn pointer_option(mut self) -> Self {
        self.optional = true;
        self.null_arm = NullArm::PointerApi;
        self
    }

    pub(crate) fn with_nonempty_evidence(mut self) -> Self {
        self.nonempty_evidence = true;
        self
    }

    pub(crate) fn with_checked_binding_type(mut self, ty: String) -> Self {
        self.checked_binding_type = Some(ty);
        self
    }

    pub(crate) fn literal_none(mutable: bool) -> Self {
        Self {
            core: GlueCore::Bare,
            mutable,
            unwrap: None,
            len: None,
            optional: true,
            null_arm: NullArm::LiteralNone,
            raw_boundary: None,
            nonempty_evidence: false,
            checked_binding_type: None,
        }
    }

    pub(crate) fn raw_boundary(
        template: super::raw_boundary::BridgeTemplate,
        target_mutability: super::raw_boundary::RawMutability,
        box_slice: bool,
        force_explicit: bool,
    ) -> Self {
        Self {
            core: GlueCore::Bare,
            mutable: target_mutability == super::raw_boundary::RawMutability::Mut,
            unwrap: None,
            len: None,
            optional: false,
            null_arm: NullArm::None,
            raw_boundary: Some(RawBoundaryGlue {
                template,
                target_mutability,
                box_slice,
                force_explicit,
                cast_pointee: None,
            }),
            nonempty_evidence: false,
            checked_binding_type: None,
        }
    }

    pub(crate) fn raw_boundary_target(
        template: super::raw_boundary::BridgeTemplate,
        target: &super::raw_boundary::RawTargetType,
        box_slice: bool,
        force_explicit: bool,
    ) -> Self {
        let mut spec = Self::raw_boundary(template, target.mutability, box_slice, force_explicit);
        spec.raw_boundary
            .as_mut()
            .expect("constructed")
            .cast_pointee = target
            .depth2
            .as_ref()
            .map(|depth2| depth2.inner_pointee.clone())
            .or_else(|| {
                (target.is_void_pointee()
                    || matches!(
                        template,
                        super::raw_boundary::BridgeTemplate::OptRefMutToRawMut
                            | super::raw_boundary::BridgeTemplate::OptRefToRawConst
                            | super::raw_boundary::BridgeTemplate::OptRefToRawMut
                            | super::raw_boundary::BridgeTemplate::OptSliceToRaw
                            | super::raw_boundary::BridgeTemplate::OptSliceToRawMut
                    ))
                .then(|| target.pointee.clone())
            });
        spec
    }

    pub(crate) fn null_arm_key(&self) -> &'static str {
        if self.unwrap.is_some() {
            return "callee-required";
        }
        match self.null_arm {
            NullArm::Checked => "checked-is-null",
            NullArm::PointerApi => "raw-pointer-option",
            NullArm::LiteralNone => "literal-none",
            NullArm::None if self.optional => "known-some",
            NullArm::None => "-",
        }
    }

    pub(crate) fn extent_arm_key(&self) -> &'static str {
        match self.len.as_ref() {
            Some(SeamLen::Licensed(_)) => "evidence-backed",
            Some(SeamLen::Fabricated) => "fallback-1024",
            None => "-",
        }
    }

    pub(crate) fn template_key(&self) -> &'static str {
        if let Some(raw) = self.raw_boundary.as_ref() {
            return raw.template.key();
        }
        if self.null_arm == NullArm::PointerApi {
            return match self.core {
                GlueCore::RawOption if self.mutable => "c-raw-option-mut",
                GlueCore::RawOption => "c-raw-option-shared",
                GlueCore::FromRawParts => "c-raw-option-slice",
                GlueCore::Bare
                | GlueCore::Reborrow
                | GlueCore::First
                | GlueCore::Index0
                | GlueCore::FromRefMut => "optional",
            };
        }
        if self.null_arm == NullArm::Checked && matches!(self.core, GlueCore::FromRawParts) {
            return "c-raw-option-slice";
        }
        if self.unwrap.is_some() {
            return "nullable-required-unwrap";
        }
        if !self.optional {
            match self.core {
                GlueCore::Reborrow if self.mutable => return "c-raw-reborrow-mut",
                GlueCore::Reborrow => return "c-raw-reborrow-shared",
                GlueCore::FromRawParts if self.mutable => return "c-raw-slice-mut",
                GlueCore::FromRawParts => return "c-raw-slice-shared",
                GlueCore::Bare | GlueCore::RawOption | GlueCore::Index0 | GlueCore::FromRefMut => {}
                GlueCore::First => {}
            }
        }
        if self.optional {
            "optional"
        } else {
            match self.core {
                GlueCore::FromRawParts => "slice",
                GlueCore::FromRefMut if self.mutable => "thin-to-slice-mut",
                GlueCore::FromRefMut => "thin-to-slice-shared",
                GlueCore::First if self.mutable => "slice-to-thin-mut",
                GlueCore::First => "slice-to-thin-shared",
                GlueCore::Reborrow | GlueCore::RawOption | GlueCore::Index0 | GlueCore::Bare => {
                    "scalar-reference"
                }
            }
        }
    }

    /// **The census's `glue_shape`, CARRIED rather than inferred** — condition 5
    /// of the option-A ruling.
    ///
    /// `seam_tsv` used to recover the shape by testing PREFIXES of the rendered
    /// replacement. Same column, same ten-word vocabulary, strictly better
    /// provenance — but it IS a schema semantics change, because the prefix test
    /// reads a string the argument's own text contributes to and this reads the
    /// decision.
    ///
    /// **Two inherited quirks are reproduced deliberately, not repaired here.**
    /// The classifier tested `.contains(".unwrap()")` BEFORE the `Some(` tests,
    /// so an unwrap under a wrapper reported `unwrap`/`as_mut_unwrap` rather
    /// than the wrapper's shape; and `Some(&X[0])` fell through the
    /// `Some(&mut *`/`Some(&*` test to `some_wrap`. Both are kept so this
    /// function is provably zero-delta wherever the classifier was right, and
    /// the places it was NOT right are the measured movement rather than a
    /// change of vocabulary mixed in with it.
    pub(crate) fn shape_key(&self) -> &'static str {
        if self.raw_boundary.is_some() {
            return "raw-boundary";
        }
        match self.null_arm {
            NullArm::LiteralNone => return "none",
            NullArm::Checked => {
                return match self.core {
                    GlueCore::FromRawParts => "checked_from_raw_parts",
                    GlueCore::RawOption => "checked_optional",
                    GlueCore::Reborrow => "checked_reborrow",
                    _ => "checked_optional",
                };
            }
            NullArm::PointerApi => return "raw_option",
            NullArm::None => {}
        }
        if let Some(found_mutable) = self.unwrap {
            return if found_mutable {
                "as_mut_unwrap"
            } else {
                "unwrap"
            };
        }
        match (self.optional, &self.core) {
            (true, GlueCore::FromRawParts) => "some_from_raw_parts",
            (true, GlueCore::Reborrow) => "some_reborrow",
            (true, GlueCore::RawOption) => "checked_optional",
            (true, GlueCore::First) => "some_wrap",
            (true, GlueCore::FromRefMut) => "some_from_ref_mut",
            // `Some(&X[0])` matches neither `Some(&mut *` nor `Some(&*`.
            (true, GlueCore::Bare | GlueCore::Index0) => "some_wrap",
            (false, GlueCore::FromRawParts) => "from_raw_parts",
            (false, GlueCore::Reborrow) => "reborrow",
            (false, GlueCore::RawOption) => "checked_optional",
            (false, GlueCore::First) => "first",
            (false, GlueCore::FromRefMut) => "from_ref_mut",
            // `index` is the classifier's FALLBACK arm, and the two cores that
            // land in it are **not** in the same position — a distinction this
            // comment previously got wrong, in the direction this track calls
            // its founding failure class.
            //
            // - `Index0` here is REACHABLE and REAL: `glue`'s `(Ref, Slice)`
            //   arm builds exactly `core(Index0, w)` with no unwrap and no
            //   wrapper, rendering `&w X[0]`, which the retired classifier fell
            //   through to `index`. It is corpus-ZERO on the frozen corpus, and
            //   corpus-zero is not unreachable.
            // - `Bare` here is genuinely unreachable: with neither an unwrap
            //   nor a wrapper it renders the argument unchanged, and `glue`
            //   returns `Ok(None)` for every pairing that would need it.
            //
            // Both are matched together because the classifier gave both the
            // same answer; only the reachability claim differed.
            (false, GlueCore::Bare | GlueCore::Index0) => "index",
        }
    }

    /// Render the spec as the span layer's text. **Byte-identical to the
    /// pre-reification `format!` set, and gated as such.**
    ///
    /// `None` when a length-bearing core carries no length. **This used to
    /// substitute an empty string**, printing
    /// `core::slice::from_raw_parts(p, () as usize)` — not merely invalid Rust
    /// but a *silent length substitution*, in the one place this milestone's
    /// hardest invariant says none may ever happen, while [`Self::len`]'s own
    /// doc promised `None`-means-refused. Prose asserting a check the code did
    /// not have, on the exact socket the HELD fabricated-length slice is
    /// designed to plug into. The AST builder already refused this input and
    /// counted it (`len_absent`); the renderer did not. Found by the
    /// adversarial review.
    ///
    /// Unreachable through [`glue`], which returns [`SeamBlock::LengthUnknown`]
    /// first — so this is fail-closed structure rather than a live path, and it
    /// moves no corpus line.
    pub(crate) fn render(&self, text: &str) -> Option<String> {
        if let Some(raw) = self.raw_boundary.as_ref() {
            let rendered = if raw.force_explicit {
                raw.template.render_explicit(
                    text,
                    raw.target_mutability,
                    raw.box_slice,
                    raw.cast_pointee.as_deref(),
                )
            } else {
                raw.template.render(
                    text,
                    raw.target_mutability,
                    raw.box_slice,
                    raw.cast_pointee.as_deref(),
                )
            };
            return match rendered.ok()? {
                super::raw_boundary::BridgeRender::ZeroSyntax => Some(text.to_owned()),
                super::raw_boundary::BridgeRender::Edit(replacement) => Some(replacement),
                super::raw_boundary::BridgeRender::Lifecycle => Some(text.to_owned()),
            };
        }
        if self.null_arm == NullArm::LiteralNone {
            return Some("None".to_owned());
        }
        let argument = text;
        if self.null_arm == NullArm::PointerApi && matches!(self.core, GlueCore::RawOption) {
            let method = if self.mutable { "as_mut" } else { "as_ref" };
            return Some(format!("unsafe {{ {argument}.{method}() }}"));
        }
        let checked_name = "__crat_call_adapter_ptr";
        let text = if self.null_arm == NullArm::Checked {
            checked_name
        } else {
            text
        };
        let base = match self.unwrap {
            None => text.to_owned(),
            Some(found_mutable) => unwrap_expr(text, found_mutable),
        };
        let inner = match self.core {
            GlueCore::Bare => base,
            GlueCore::Reborrow => {
                format!("unsafe {{ {}*{base} }}", amp(self.mutable))
            }
            GlueCore::RawOption => {
                let method = if self.mutable { "as_mut" } else { "as_ref" };
                format!("unsafe {{ {base}.{method}() }}")
            }
            GlueCore::First => {
                let method = if self.mutable { "first_mut" } else { "first" };
                format!("{base}.{method}().unwrap()")
            }
            GlueCore::Index0 => format!("{}{base}[0]", amp(self.mutable)),
            GlueCore::FromRawParts => {
                let ctor = if self.mutable {
                    "from_raw_parts_mut"
                } else {
                    "from_raw_parts"
                };
                let call = match self.len.as_ref()? {
                    // The C spelling is `size_t`/`c_int`/`c_ulong` depending on
                    // the header and `from_raw_parts` takes `usize`, so the
                    // companion is cast; parenthesised because it may be an
                    // arbitrary expression.
                    SeamLen::Licensed(len) => {
                        format!("core::slice::{ctor}({base}, ({len}) as usize)")
                    }
                    // **No cast and no parentheses**: the const is declared
                    // `usize`, and casting it would make a fabricated site
                    // textually indistinguishable from a licensed one whose
                    // companion happened to be a path.
                    SeamLen::Fabricated => {
                        format!("core::slice::{ctor}({base}, {FABRICATED_LEN_PATH})")
                    }
                };
                format!("unsafe {{ {call} }}")
            }
            GlueCore::FromRefMut => {
                let ctor = if self.mutable { "from_mut" } else { "from_ref" };
                format!("core::slice::{ctor}({base})")
            }
        };
        Some(if self.null_arm == NullArm::Checked {
            let ty = self.checked_binding_type.as_deref()?;
            format!(
                "{{ let {checked_name}: {ty} = {argument}; if {checked_name}.is_null() {{ None }} else {{ Some({inner}) }} }}"
            )
        } else if self.optional {
            format!("Some({inner})")
        } else {
            inner
        })
    }
}

/// The glue that turns a value of `found` into one of `expected`.
///
/// - `Ok(None)` — the forms already agree, or coerce. **No edit.**
/// - `Ok(Some(spec))` — the adapter, DESCRIBED.
/// - `Err(block)` — this position cannot be adapted, with its reason.
///
/// # Half 2 of the option-A reification (2026-08-13)
///
/// Every arm used to `format!` its answer over the argument's source text.
/// It now names a [`GlueSpec`], and the caller renders that spec over the same
/// text — so `spec.render(text)` is the string this function used to return,
/// **byte for byte**, and the argument no longer reaches this function at all.
///
/// That the text is not a parameter here is the substance of the change rather
/// than a tidy-up: an adapter is a shape, the argument is a subtree, and the
/// AST layer needs the first without being handed a rendering of the second.
///
/// **Reification only** — no arm's `(expected, found)` pattern, guard, family
/// or `Err` moved. Each `format!` became the spec that renders to it.
pub(crate) fn glue(
    expected: Form,
    found: Form,
    len: Option<&str>,
) -> Result<Option<(GlueSpec, SeamFamily)>, SeamBlock> {
    glue_with_nonempty(expected, found, len, true)
}

fn glue_with_nonempty(
    expected: Form,
    found: Form,
    len: Option<&str>,
    nonempty: bool,
) -> Result<Option<(GlueSpec, SeamFamily)>, SeamBlock> {
    use Form::*;
    // A shared borrow can never satisfy a `&mut` position, whatever the shapes
    // either side. Checked first so every arm below may assume mutability is
    // obtainable.
    let shared_to_mut = |want: bool, have: bool| want && !have;

    Ok(match (expected, found) {
        // ---- identities and coercions: no edit ----
        (Ref { mutable: w }, Ref { mutable: h }) => {
            if shared_to_mut(w, h) {
                return Err(SeamBlock::SharedToMut);
            }
            None // `&mut T` coerces to `&T`
        }
        (Slice { mutable: w }, Slice { mutable: h }) => {
            if shared_to_mut(w, h) {
                return Err(SeamBlock::SharedToMut);
            }
            None
        }
        (
            Opt {
                mutable: w,
                slice: ws,
            },
            Opt {
                mutable: h,
                slice: hs,
            },
        ) if ws == hs => {
            if shared_to_mut(w, h) {
                return Err(SeamBlock::SharedToMut);
            }
            None
        }

        // ---- reborrow family: a raw base becomes a reference ----
        (Ref { mutable }, Raw) => Some((
            GlueSpec::core(GlueCore::Reborrow, mutable),
            SeamFamily::Reborrow,
        )),
        (
            Opt {
                mutable,
                slice: false,
            },
            Raw,
        ) => Some((
            GlueSpec::core(GlueCore::RawOption, mutable).pointer_option(),
            SeamFamily::Reborrow,
        )),

        // ---- slice seams: a length from the CALL SITE, or FABRICATED ----
        //
        // Ruling B (2026-08-11): both adjacency arms license the companion
        // argument as the length — `len` is that argument's own source text.
        //
        // **Ruling B's `None` arm is SUPERSEDED (2026-08-12).** Where no
        // companion exists — `len-elsewhere` and `len-absent`, the full
        // `seam-len-unknown` population — the position no longer refuses; it
        // places the seam with the fabricated placeholder extent, uniformly.
        // The premise is contribution scope: the guarantee is aliasing UB, not
        // spatial bounds. The carve-out is per SITE and the site is TAGGED, so
        // it stays countable apart from the licensed placements.
        //
        // `LengthUnknown` **stays in the enum** — it is still the honest name
        // for the condition and the census reports the underlying evidence
        // under it. What changed is that `glue` no longer returns it.
        (Slice { mutable }, Raw) => Some((
            with_length(GlueSpec::core(GlueCore::FromRawParts, mutable), len),
            SeamFamily::Reborrow,
        )),
        (
            Opt {
                mutable,
                slice: true,
            },
            Raw,
        ) => Some((
            with_length(GlueSpec::core(GlueCore::FromRawParts, mutable), len).checked(),
            SeamFamily::Reborrow,
        )),

        // ---- safe family ----
        (Slice { mutable: w }, Ref { mutable: h }) => {
            if shared_to_mut(w, h) {
                return Err(SeamBlock::SharedToMut);
            }
            // `from_ref` accepts a `&mut T` by coercion, which is what makes the
            // measured `&mut T → &[T]` row (30 positions) a safe one rather than
            // a gap.
            Some((GlueSpec::core(GlueCore::FromRefMut, w), SeamFamily::Safe))
        }
        (Ref { mutable: w }, Slice { mutable: h }) => {
            if shared_to_mut(w, h) {
                return Err(SeamBlock::SharedToMut);
            }
            if !nonempty {
                return Err(SeamBlock::NonemptyUnknown);
            }
            Some((
                GlueSpec::core(GlueCore::First, w).with_nonempty_evidence(),
                SeamFamily::Safe,
            ))
        }
        (
            Opt {
                mutable: w,
                slice: false,
            },
            Ref { mutable: h },
        ) => {
            if shared_to_mut(w, h) {
                return Err(SeamBlock::SharedToMut);
            }
            Some((
                GlueSpec::core(GlueCore::Bare, w).wrapped(),
                SeamFamily::Safe,
            ))
        }
        (
            Opt {
                mutable: w,
                slice: true,
            },
            Ref { mutable: h },
        ) => {
            if shared_to_mut(w, h) {
                return Err(SeamBlock::SharedToMut);
            }
            Some((
                GlueSpec::core(GlueCore::FromRefMut, w).wrapped(),
                SeamFamily::Safe,
            ))
        }
        (
            Opt {
                mutable: w,
                slice: false,
            },
            Slice { mutable: h },
        ) => {
            if shared_to_mut(w, h) {
                return Err(SeamBlock::SharedToMut);
            }
            Some((
                GlueSpec::core(GlueCore::Index0, w).wrapped(),
                SeamFamily::Safe,
            ))
        }
        // The FAT twin of the arm above: the slice is already the payload, so
        // this is a bare wrap. Found by the exhaustiveness guard rather than by
        // enumeration — the arms were written from the measured census, and the
        // census has no `Slice → Option<&[T]>` row because nothing has reached
        // that position yet.
        (
            Opt {
                mutable: w,
                slice: true,
            },
            Slice { mutable: h },
        ) => {
            if shared_to_mut(w, h) {
                return Err(SeamBlock::SharedToMut);
            }
            Some((
                GlueSpec::core(GlueCore::Bare, w).wrapped(),
                SeamFamily::Safe,
            ))
        }

        // Under §29, a required callee contract opens the nullable source by a
        // one-evaluation unwrap. Cross-shape cases compose the same core used
        // by the non-optional matrix.
        (
            Ref { mutable: w },
            Opt {
                mutable: h,
                slice: false,
            },
        ) => {
            if shared_to_mut(w, h) {
                return Err(SeamBlock::SharedToMut);
            }
            Some((
                GlueSpec::core(GlueCore::Bare, w).with_unwrap(h),
                SeamFamily::Safe,
            ))
        }
        (
            Slice { mutable: w },
            Opt {
                mutable: h,
                slice: true,
            },
        ) => {
            if shared_to_mut(w, h) {
                return Err(SeamBlock::SharedToMut);
            }
            Some((
                GlueSpec::core(GlueCore::Bare, w).with_unwrap(h),
                SeamFamily::Safe,
            ))
        }
        (
            Slice { mutable: w },
            Opt {
                mutable: h,
                slice: false,
            },
        ) => {
            if shared_to_mut(w, h) {
                return Err(SeamBlock::SharedToMut);
            }
            Some((
                GlueSpec::core(GlueCore::FromRefMut, w).with_unwrap(h),
                SeamFamily::Safe,
            ))
        }
        (
            Ref { mutable: w },
            Opt {
                mutable: h,
                slice: true,
            },
        ) => {
            if shared_to_mut(w, h) {
                return Err(SeamBlock::SharedToMut);
            }
            if !nonempty {
                return Err(SeamBlock::NonemptyUnknown);
            }
            Some((
                GlueSpec::core(GlueCore::First, w)
                    .with_unwrap(h)
                    .with_nonempty_evidence(),
                SeamFamily::Safe,
            ))
        }
        (Opt { slice: ws, .. }, Opt { slice: hs, .. }) => {
            debug_assert_ne!(ws, hs, "identical optional twins matched above");
            return Err(SeamBlock::NullabilityInsufficient);
        }

        // A raw position needs no adapter: `&mut T` coerces to `*mut T` at a
        // call. Measured, and it is why E3b predicts no counter movement here.
        (Raw, _) => None,
    })
}

/// The §29 null-literal arm. Kept beside [`glue`] so both the span and AST
/// consumers receive an ordinary carried [`GlueSpec`]; null is not a special
/// rewrite path below the decision layer.
fn glue_null(expected: Form) -> Result<Option<(GlueSpec, SeamFamily)>, SeamBlock> {
    match expected {
        Form::Opt { mutable, .. } => Ok(Some((GlueSpec::literal_none(mutable), SeamFamily::Safe))),
        _ => Err(SeamBlock::UnnameableOperand),
    }
}

#[cfg(test)]
mod tests {
    use Form::*;

    use super::*;

    const T: &str = "p";

    /// **THE RENDERER PARITY ORACLE — every emitting arm of [`glue`], by hand.**
    ///
    /// Condition 2 of the option-A ruling: spec + renderer must reproduce
    /// today's text byte-identically. This pins the RENDERER half of that gate
    /// now, before any arm is converted, so the conversion lands against a
    /// fixed target rather than co-evolving with it.
    ///
    /// Each row is `(spec, expected text)` transcribed from the corresponding
    /// `format!` in `glue`. The algebra is `[Some(] core([unwrap(] X [)]) [)]`,
    /// and these fourteen rows are every composition `glue` can emit.
    ///
    /// *Mutation-tested:* dropping the parens in the `FromRawParts` cast, or
    /// swapping `from_ref`/`from_mut`, fails here.
    #[test]
    fn render_reproduces_every_emitting_glue_arm_byte_for_byte() {
        let cases: Vec<(GlueSpec, &str)> = vec![
            // (Ref, Raw) and its optional twin
            (
                GlueSpec::core(GlueCore::Reborrow, true),
                "unsafe { &mut *p }",
            ),
            (GlueSpec::core(GlueCore::Reborrow, false), "unsafe { &*p }"),
            (
                GlueSpec::core(GlueCore::RawOption, true).pointer_option(),
                "unsafe { p.as_mut() }",
            ),
            // (Slice, Raw) and its optional twin
            (
                GlueSpec::core(GlueCore::FromRawParts, true).with_len("n"),
                "unsafe { core::slice::from_raw_parts_mut(p, (n) as usize) }",
            ),
            (
                GlueSpec::core(GlueCore::FromRawParts, false).with_len("n"),
                "unsafe { core::slice::from_raw_parts(p, (n) as usize) }",
            ),
            (
                GlueSpec::core(GlueCore::FromRawParts, true)
                    .with_len("n")
                    .checked()
                    .with_checked_binding_type("*mut i32".to_owned()),
                "{ let __crat_call_adapter_ptr: *mut i32 = p; if __crat_call_adapter_ptr.is_null() { None } else { Some(unsafe { core::slice::from_raw_parts_mut(__crat_call_adapter_ptr, (n) as usize) }) } }",
            ),
            // safe family
            (
                GlueSpec::core(GlueCore::FromRefMut, true),
                "core::slice::from_mut(p)",
            ),
            (
                GlueSpec::core(GlueCore::FromRefMut, false),
                "core::slice::from_ref(p)",
            ),
            (GlueSpec::core(GlueCore::Index0, true), "&mut p[0]"),
            (GlueSpec::core(GlueCore::Bare, false).wrapped(), "Some(p)"),
            (
                GlueSpec::core(GlueCore::FromRefMut, false).wrapped(),
                "Some(core::slice::from_ref(p))",
            ),
            (
                GlueSpec::core(GlueCore::Index0, false).wrapped(),
                "Some(&p[0])",
            ),
            // the null-panic convention: unwrap under each core
            (
                GlueSpec::core(GlueCore::Bare, false).with_unwrap(false),
                "p.unwrap()",
            ),
            (
                GlueSpec::core(GlueCore::Index0, true).with_unwrap(true),
                "&mut p.as_mut().unwrap()[0]",
            ),
        ];
        for (spec, expected) in cases {
            assert_eq!(
                spec.render(T).expect("every emitting spec renders"),
                expected,
                "renderer must be byte-identical to the arm it replaces: {spec:?}"
            );
        }
    }

    fn g(expected: Form, found: Form) -> Result<Option<(GlueSpec, SeamFamily)>, SeamBlock> {
        glue(expected, found, None)
    }

    /// The glue's TEXT — `glue` names a spec and the caller renders it, which is
    /// exactly what `seams` does in production. These assertions therefore still
    /// read the string the span layer writes, over the same argument, and they
    /// are the reason half 2 could not quietly change one.
    fn text(expected: Form, found: Form) -> String {
        rendered(g(expected, found), T)
    }

    fn rendered(got: Result<Option<(GlueSpec, SeamFamily)>, SeamBlock>, arg: &str) -> String {
        let mut spec = got
            .unwrap_or_else(|b| panic!("blocked: {b:?}"))
            .unwrap_or_else(|| panic!("no edit"))
            .0;
        if spec.null_arm == NullArm::Checked && spec.checked_binding_type.is_none() {
            spec = spec.with_checked_binding_type("*mut i32".to_owned());
        }
        spec.render(arg).expect("an emitting spec always renders")
    }

    /// **Reborrow, BOTH SIDES.** `*mut T → &mut T` needs glue; the reverse needs
    /// none, because a reference coerces to a raw pointer at a call.
    ///
    /// A witness on one direction witnesses half a table: an implementation that
    /// emitted `&mut *p` in *both* directions would pass a one-sided test and
    /// produce `&mut *(&mut x)` at every raw position.
    #[test]
    fn reborrow_is_directional() {
        assert_eq!(text(Ref { mutable: true }, Raw), "unsafe { &mut *p }");
        assert_eq!(text(Ref { mutable: false }, Raw), "unsafe { &*p }");
        assert_eq!(g(Raw, Ref { mutable: true }), Ok(None), "reverse: coercion");
        assert_eq!(g(Raw, Slice { mutable: true }), Ok(None));
    }

    /// **Optional, BOTH SIDES.** `Some(..)` one way, `.unwrap()` the other —
    /// the latter on `-3`'s null-panic convention.
    #[test]
    fn optional_wrap_and_required_unwrap_are_directional() {
        assert_eq!(
            text(
                Opt {
                    mutable: true,
                    slice: false
                },
                Ref { mutable: true }
            ),
            "Some(p)"
        );
        assert_eq!(
            text(
                Ref { mutable: false },
                Opt {
                    mutable: false,
                    slice: false
                }
            ),
            "p.unwrap()"
        );
        assert_eq!(
            text(
                Ref { mutable: true },
                Opt {
                    mutable: true,
                    slice: false
                }
            ),
            "p.as_mut().unwrap()"
        );
    }

    /// **THE UNWRAP SPELLING FOLLOWS THE *FOUND* SIDE — witnessed OFF THE
    /// DIAGONAL.**
    ///
    /// [`unwrap_expr`]'s whole reason for existing is that `Option<&mut T>` is
    /// not `Copy` and `.unwrap()` MOVES it, so the seam must spell that case
    /// `.as_mut().unwrap()`. Which spelling applies is therefore a fact about
    /// the value the caller HAS, never about the position it is going into.
    ///
    /// [`optional_wraps_one_way_and_unwraps_the_other`] pins both spellings but
    /// only where the two sides agree, so it is blind to a `glue` that read the
    /// EXPECTED side's mutability — the two are equal on the diagonal, which is
    /// the shape this module's own reborrow test warns about ("a witness on one
    /// direction witnesses half a table"). Found by mutation (M26): passing `w`
    /// where `h` belongs left the entire suite green.
    ///
    /// A shared position fed from a mutable optional is the discriminating
    /// case, and it is not exotic: `&T` is exactly what a read-only callee
    /// parameter converts to.
    #[test]
    fn required_unwrap_reads_mutability_from_the_found_side() {
        assert_eq!(
            text(
                Ref { mutable: false },
                Opt {
                    mutable: true,
                    slice: false
                }
            ),
            "p.as_mut().unwrap()"
        );
        // The other off-diagonal pairing cannot occur: `shared_to_mut` blocks a
        // `&mut` position fed from a shared optional before any spec is built.
        // Asserted so the pair above is not mistaken for half a table in turn.
        assert_eq!(
            g(
                Ref { mutable: true },
                Opt {
                    mutable: false,
                    slice: false
                }
            ),
            Err(SeamBlock::SharedToMut)
        );
    }

    /// **The `Slice`-expected-from-`Opt`-found arm, BOTH fat/thin twins.**
    ///
    /// The arm picks its core on the FOUND optional's fatness: a fat optional
    /// already carries the slice and needs only the unwrap, while a thin one
    /// yields a reference that must be widened by `from_ref`/`from_mut`.
    /// Swapping the two produces glue that is well-formed and wrong in both
    /// directions — `core::slice::from_ref` applied to a slice, and a slice
    /// position handed a bare reference.
    ///
    /// Unwitnessed until mutation M25 swapped them and the suite stayed green.
    #[test]
    fn optional_to_required_uses_the_matching_cross_shape_core() {
        assert_eq!(
            text(
                Slice { mutable: false },
                Opt {
                    mutable: false,
                    slice: true
                }
            ),
            "p.unwrap()"
        );
        assert_eq!(
            text(
                Slice { mutable: true },
                Opt {
                    mutable: true,
                    slice: false
                }
            ),
            "core::slice::from_mut(p.as_mut().unwrap())"
        );
        assert_eq!(
            g(
                Opt {
                    mutable: false,
                    slice: true
                },
                Opt {
                    mutable: false,
                    slice: false
                }
            ),
            Err(SeamBlock::NullabilityInsufficient)
        );
        assert_eq!(
            g(
                Opt {
                    mutable: false,
                    slice: false
                },
                Opt {
                    mutable: false,
                    slice: true
                }
            ),
            Err(SeamBlock::NullabilityInsufficient)
        );
    }

    /// **Optional over a raw base uses the raw-pointer Option API directly.**
    /// The method evaluates the source once and maps null to `None` without an
    /// unconditional dereference.
    #[test]
    fn optional_over_raw_uses_as_mut_once() {
        let (spec, fam) = g(
            Opt {
                mutable: true,
                slice: false,
            },
            Raw,
        )
        .unwrap()
        .unwrap();
        assert_eq!(spec.render(T).unwrap(), "unsafe { p.as_mut() }");
        assert_eq!(fam, SeamFamily::Reborrow, "the raw base carries the family");
    }

    /// **Slice, BOTH SIDES**, and the measured table amendment.
    ///
    /// `&mut T → &[T]` (30 positions) is SAFE: `from_ref` takes a `&mut T` by
    /// coercion. The census found it; the ratified table did not have it.
    #[test]
    fn slice_construction_and_projection_are_both_safe() {
        assert_eq!(
            text(Slice { mutable: true }, Ref { mutable: true }),
            "core::slice::from_mut(p)"
        );
        assert_eq!(
            text(Slice { mutable: false }, Ref { mutable: false }),
            "core::slice::from_ref(p)"
        );
        // THE AMENDMENT: shared slice expected, mutable reference supplied.
        assert_eq!(
            text(Slice { mutable: false }, Ref { mutable: true }),
            "core::slice::from_ref(p)"
        );
        // The reverse projection.
        assert_eq!(
            text(Ref { mutable: true }, Slice { mutable: true }),
            "p.first_mut().unwrap()"
        );
        assert_eq!(
            text(Ref { mutable: false }, Slice { mutable: false }),
            "p.first().unwrap()"
        );
        assert_eq!(
            glue_with_nonempty(
                Ref { mutable: false },
                Slice { mutable: false },
                None,
                false,
            ),
            Err(SeamBlock::NonemptyUnknown),
            "reverse conversion without the class's nonempty contract must hold"
        );
    }

    /// **The length rule — evolved from a gate to an authorization**
    /// (user ruling 2026-08-12).
    ///
    /// # What this witness USED to pin, and why it changed
    ///
    /// It read *"raw → {expected} must gate, never fabricate a length"*, over
    /// 65.7 % of the measured market. The reasoning was sound and is
    /// **unretracted**: `from_raw_parts` with an oversized extent is UB at
    /// construction, so a fabricated length is unsound the moment it is built.
    ///
    /// The **policy** over that fact changed, on a premise the technical
    /// objection does not own — contribution scope. The paper's guarantee is
    /// aliasing UB, not spatial bounds; fabricated sites are a knowing,
    /// **tagged, per-site** carve-out. The objection stays on record as the
    /// flagged technical fact; it was not withdrawn and it is not wrong.
    ///
    /// # What it pins NOW
    ///
    /// The old guard's protection is being spent, so it is replaced by three
    /// obligations rather than deleted — a guard that quietly changes meaning is
    /// worse than one that is retired in the open:
    ///
    /// - **W1** a fabricated length is ALWAYS TAGGED,
    /// - **W2** fabrication happens ONLY where no companion exists,
    /// - **W3** the non-length-bearing cores never carry a length.
    ///
    /// **The builder-layer guard is deliberately NOT touched.**
    /// `a_slice_seam_with_no_length_places_nothing_and_is_counted` pins *no
    /// layer below the gate may invent a length*; fabrication happens **at** the
    /// gate, so that guard stands and `len_absent` stays 0 on the corpus.
    #[test]
    fn every_raw_to_slice_direction_gets_a_length_or_a_fabricated_one() {
        for expected in [
            Slice { mutable: true },
            Slice { mutable: false },
            Opt {
                mutable: true,
                slice: true,
            },
            Opt {
                mutable: false,
                slice: true,
            },
        ] {
            // ---- W1: a fabricated length is ALWAYS TAGGED ----
            //
            // The whole point of `SeamLen` being a two-arm type. A mutation
            // that fabricates by building `Licensed("1024")` fails HERE, and it
            // fails at the artifact too, because both read this one field.
            let Ok(Some((spec, _))) = g(expected, Raw) else {
                panic!("raw → {expected:?} must fabricate, not refuse")
            };
            assert_eq!(
                spec.len,
                Some(SeamLen::Fabricated),
                "raw → {expected:?} with no companion must fabricate, TAGGED"
            );

            // ---- W2: fabrication ONLY where no companion exists ----
            //
            // The other direction of the same authorization rule: an arm that
            // ignored its input and fabricated unconditionally would satisfy W1
            // and destroy all 277 licensed placements.
            let Ok(Some((spec, _))) = glue(expected, Raw, Some("n")) else {
                panic!("a companion length must still place a licensed seam")
            };
            assert_eq!(
                spec.len,
                Some(SeamLen::Licensed("n".to_owned())),
                "a companion was supplied — fabricating over it is forbidden"
            );
        }

        // ---- W3: the NON-length-bearing cores never carry a length ----
        //
        // `with_length` is only reachable from the two `FromRawParts` arms; a
        // mutation that routed a reborrow or a `from_ref` through it would
        // render a length into a constructor that takes none.
        for (expected, found) in [
            (Ref { mutable: true }, Raw),
            (Ref { mutable: false }, Raw),
            (Slice { mutable: false }, Ref { mutable: false }),
            (Slice { mutable: true }, Ref { mutable: true }),
        ] {
            if let Ok(Some((spec, _))) = glue(expected, found, None) {
                assert_eq!(
                    spec.len, None,
                    "{expected:?} ← {found:?} needs no length and must carry none"
                );
            }
        }
    }

    /// **The authorization rule, witnessed on the pure function itself** (R8).
    ///
    /// `with_length` is the single place that decides licensed-vs-fabricated.
    /// Witnessing it here as well as through `glue` is not redundancy: `glue`'s
    /// witness proves the two slice arms are wired to it, and this one proves
    /// the rule those arms are wired to is the right rule — the split M28 and
    /// M40 were banked for.
    #[test]
    fn the_authorization_rule_is_decided_by_the_companion_alone() {
        let base = || GlueSpec::core(GlueCore::FromRawParts, false);
        assert_eq!(
            with_length(base(), Some("n")).len,
            Some(SeamLen::Licensed("n".to_owned()))
        );
        assert_eq!(with_length(base(), None).len, Some(SeamLen::Fabricated));
        // An EMPTY companion is still a companion: the call site supplied text,
        // and inventing an extent over supplied text is the failure this rule
        // exists to prevent. (`glue` never sees one — `span_to_snippet` of a
        // real argument is non-empty — so this pins the rule, not the corpus.)
        assert_eq!(
            with_length(base(), Some("")).len,
            Some(SeamLen::Licensed(String::new()))
        );
    }

    /// **The two arms render DIFFERENT text, and the difference is auditable.**
    ///
    /// A fabricated site must be recognizable in the emitted crate by someone
    /// holding the code and not the TSV — the ruling's own reason for rejecting
    /// artifact-tag-only. `1024` spelled as a literal would be
    /// indistinguishable from a real length that happens to be 1024; the named
    /// const is not.
    #[test]
    fn a_fabricated_extent_is_named_in_the_emitted_text() {
        let fabricated = GlueSpec::core(GlueCore::FromRawParts, false)
            .with_fabricated_len()
            .render("p")
            .expect("fabricated specs render");
        assert_eq!(
            fabricated,
            "unsafe { core::slice::from_raw_parts(p, crate::FALLBACK_SLICE_EXTENT) }"
        );
        assert!(
            !fabricated.contains("1024"),
            "the extent is NAMED, never spelled as a bare literal: {fabricated}"
        );
        assert!(
            !fabricated.contains("as usize"),
            "the const is already `usize`; casting it would make a fabricated \
             site textually indistinguishable from a licensed path companion"
        );
        // And the licensed arm is byte-identical to its pre-ruling text.
        assert_eq!(
            GlueSpec::core(GlueCore::FromRawParts, true)
                .with_len("n")
                .render("p")
                .as_deref(),
            Some("unsafe { core::slice::from_raw_parts_mut(p, (n) as usize) }")
        );
    }

    /// The audit tag's two arms key differently, and the LICENSED bytes do not
    /// move — which is what makes the fabricated count an addition to the
    /// census rather than a re-keying of it.
    #[test]
    fn the_audit_tag_separates_fabricated_from_licensed() {
        for e in [
            LenEvidence::Following,
            LenEvidence::Preceding,
            LenEvidence::Elsewhere,
            LenEvidence::None,
        ] {
            assert_eq!(LenArm::Licensed(e).key(), e.key(), "licensed bytes move");
            assert_eq!(LenArm::Fabricated(e).key(), "len-fabricated");
            // The signature evidence survives BOTH arms — bound-verification's
            // derivability input (`Elsewhere` vs `None`) must not be erased by
            // the fabrication that made the position placeable.
            assert_eq!(LenArm::Fabricated(e).evidence(), e);
            assert_eq!(LenArm::Licensed(e).evidence(), e);
        }
    }

    /// **Ruling B — a companion length turns the gate into a seam.**
    ///
    /// The same pair that gates with no length produces `from_raw_parts` with
    /// one, and the length is the caller's own text, cast rather than rendered.
    ///
    /// *Mutation-tested:* drop the `as usize` cast and the emitted call fails to
    /// type-check against `from_raw_parts`, whose length is a `usize` while the
    /// C spelling is `size_t`/`c_int`/`c_ulong` depending on the header.
    #[test]
    fn a_companion_length_converts_the_gate_into_a_slice_seam() {
        assert_eq!(
            rendered(glue(Slice { mutable: true }, Raw, Some("n")), "p"),
            "unsafe { core::slice::from_raw_parts_mut(p, (n) as usize) }"
        );
        assert_eq!(
            rendered(glue(Slice { mutable: false }, Raw, Some("len")), "p"),
            "unsafe { core::slice::from_raw_parts(p, (len) as usize) }"
        );
        // The fat optional composes the wrap around it.
        assert_eq!(
            rendered(
                glue(
                    Opt {
                        mutable: true,
                        slice: true
                    },
                    Raw,
                    Some("n")
                ),
                "p"
            ),
            "{ let __crat_call_adapter_ptr: *mut i32 = p; if __crat_call_adapter_ptr.is_null() { None } else { Some(unsafe { core::slice::from_raw_parts_mut(__crat_call_adapter_ptr, (n) as usize) }) } }"
        );
        // **Without one, the position now FABRICATES** (ruling 2026-08-12,
        // superseding ruling item 4's `None` arm). What ruling B settled is
        // untouched: adjacency licenses the companion, and a licensed companion
        // is never overridden by an invented extent.
        let Ok(Some((spec, _))) = glue(Slice { mutable: true }, Raw, None) else {
            panic!("the no-companion position must place a fabricated seam")
        };
        assert_eq!(spec.len, Some(SeamLen::Fabricated));
        assert_eq!(
            spec.render("p").as_deref(),
            Some("unsafe { core::slice::from_raw_parts_mut(p, crate::FALLBACK_SLICE_EXTENT) }")
        );
    }

    /// The length is a **raw base**, so a slice seam is REBORROW family however
    /// safe its constructor name reads.
    ///
    /// `from_raw_parts` is `unsafe` and carries the pointer-validity obligation;
    /// filing it under `Safe` would put the corpus's largest adapter population
    /// in the column that means "compiler-checked end to end".
    #[test]
    fn a_slice_seam_over_a_raw_base_is_reborrow_family() {
        assert_eq!(
            glue(Slice { mutable: true }, Raw, Some("n"))
                .unwrap()
                .unwrap()
                .1,
            SeamFamily::Reborrow
        );
    }

    /// **A shared borrow never satisfies a `&mut` position**, in every pair that
    /// can express the mismatch.
    ///
    /// *Mutation-tested:* drop the `shared_to_mut` guard from any arm and the
    /// corresponding row here fails — the glue would compile-fail at `E0596`
    /// instead of degrading with a reason, turning an attributable gate into a
    /// revert.
    #[test]
    fn a_shared_borrow_never_satisfies_a_mut_position() {
        let shared = Ref { mutable: false };
        for expected in [
            Ref { mutable: true },
            Slice { mutable: true },
            Opt {
                mutable: true,
                slice: false,
            },
            Opt {
                mutable: true,
                slice: true,
            },
        ] {
            assert_eq!(
                g(expected, shared),
                Err(SeamBlock::SharedToMut),
                "{expected:?} from a shared borrow must gate"
            );
        }
        // ... and the same-form case, which has its own arm.
        assert_eq!(
            g(Slice { mutable: true }, Slice { mutable: false }),
            Err(SeamBlock::SharedToMut)
        );
    }

    /// Matching forms produce **no edit at all** — the 58.6 % of positions §4
    /// measured as needing no caller-side text.
    #[test]
    fn matching_forms_need_no_edit() {
        for f in [
            Ref { mutable: true },
            Slice { mutable: false },
            Opt {
                mutable: true,
                slice: false,
            },
        ] {
            assert_eq!(g(f, f), Ok(None), "{f:?} against itself must need no glue");
        }
        // `&mut T` supplied where `&T` is wanted: coercion, still no edit.
        assert_eq!(g(Ref { mutable: false }, Ref { mutable: true }), Ok(None));
    }

    /// **THE CAST PEEL, at the side that decides it.**
    ///
    /// [`text_span_of`] is the whole of the decision layer's answer to *which
    /// subtree survives inside the adapter*, and getting it wrong is silent: the
    /// span layer replaces the whole argument either way, so a `&mut *(q as *mut
    /// u8)` would differ from the span layer's `&mut *q` only in the corpus
    /// differential, and only if this corpus places a seam on a cast at all.
    ///
    /// Mutation M28 collapsed the two cast arms onto the argument span and the
    /// entire suite stayed green — because the mapping lived inside a loop that
    /// needs a `TyCtxt`, a call site and a decision map to run. Lifting it out
    /// is what makes it witnessable.
    ///
    /// The `None` arms matter as much as the `Some` ones: a default of
    /// `arg.span` for an unnameable operand would hand the AST layer a subtree
    /// the replacement was never built from.
    #[test]
    fn the_replacement_text_comes_from_the_cast_operand_and_nowhere_else() {
        rustc_span::create_default_session_globals_then(|| {
            let whole = Span::with_root_ctxt(rustc_span::BytePos(100), rustc_span::BytePos(120));
            let operand = Span::with_root_ctxt(rustc_span::BytePos(100), rustc_span::BytePos(101));
            let hir = HirId::INVALID;

            // The shapes that read their OWN span.
            assert_eq!(text_span_of(ArgShape::BareLocal(hir), whole), Some(whole));
            assert_eq!(
                text_span_of(
                    ArgShape::AddrOf {
                        mutable: true,
                        base: None,
                        through_deref: false
                    },
                    whole
                ),
                Some(whole)
            );

            // The two that read the cast's OPERAND, which is strictly inside.
            assert_eq!(
                text_span_of(
                    ArgShape::AddrOfCast {
                        mutable: true,
                        inner: operand
                    },
                    whole
                ),
                Some(operand),
                "the replacement is built from the operand's snippet, so the \
                 operand is the subtree that must survive"
            );
            assert_eq!(
                text_span_of(
                    ArgShape::CastOfLocal {
                        binding: hir,
                        inner: operand
                    },
                    whole
                ),
                Some(operand)
            );
            assert_ne!(
                operand, whole,
                "the assertions above only mean anything if the two spans differ"
            );

            // A null literal is now a nameable whole-argument target: the AST
            // layer replaces it with `None` and deliberately keeps no payload.
            assert_eq!(text_span_of(ArgShape::NullLit, whole), Some(whole));
            assert_eq!(
                text_span_of(ArgShape::RawExpr { root: None }, whole),
                Some(whole)
            );
            // The genuinely unnameable shapes still answer NOTHING.
            assert_eq!(text_span_of(ArgShape::Cast { inner: operand }, whole), None);
            assert_eq!(text_span_of(ArgShape::Other, whole), None);
        });
    }

    /// **THE RETIRED CLASSIFIER, kept as this test's oracle.**
    ///
    /// A verbatim transcription of the ten prefix tests `seam_tsv` ran over
    /// `edit.replacement` before condition 5 replaced them with
    /// [`GlueSpec::shape_key`]. Kept here and nowhere else: the census must
    /// carry the shape, and the only remaining question is *where the carried
    /// answer differs from the inferred one*, which needs both.
    fn inferred_shape(r: &str) -> &'static str {
        if r.starts_with("core::slice::from_raw_parts") {
            "from_raw_parts"
        } else if r.starts_with("Some(core::slice::from_raw_parts") {
            "some_from_raw_parts"
        } else if r.contains(".as_mut().unwrap()") {
            "as_mut_unwrap"
        } else if r.contains(".unwrap()") {
            "unwrap"
        } else if r.starts_with("Some(&mut *") || r.starts_with("Some(&*") {
            "some_reborrow"
        } else if r.starts_with("Some(core::slice::from_") {
            "some_from_ref_mut"
        } else if r.starts_with("Some(") {
            "some_wrap"
        } else if r.starts_with("&mut *") || r.starts_with("&*") {
            "reborrow"
        } else if r.starts_with("core::slice::from_") {
            "from_ref_mut"
        } else {
            "index"
        }
    }

    /// **Every spec `glue` can name agrees with the retired classifier — over a
    /// WELL-BEHAVED argument.** Condition 5's "same column" as a measurement.
    ///
    /// The argument is a bare identifier here deliberately, because that is the
    /// case in which the prefix classifier was *right*. The cases in which it
    /// was not are the next test, and they are the schema movement.
    #[test]
    fn the_carried_shape_agrees_with_the_retired_classifier() {
        for spec in every_emitting_spec().into_iter().filter(|spec| {
            spec.null_arm == NullArm::None
                && !matches!(
                    spec.core,
                    GlueCore::Reborrow
                        | GlueCore::RawOption
                        | GlueCore::First
                        | GlueCore::FromRawParts
                )
        }) {
            assert_eq!(
                spec.shape_key(),
                inferred_shape(&spec.render("p").expect("emitting spec renders")),
                "carried and inferred shapes must agree on a bare argument: {spec:?}"
            );
        }
    }

    /// **THE RENDERER REFUSES A LENGTH-LESS SLICE ADAPTER.**
    ///
    /// It used to substitute an empty string and print
    /// `core::slice::from_raw_parts(p, () as usize)`. That is not merely
    /// "invalid Rust the compiler catches" — it is a **silent length
    /// substitution**, produced by the layer whose own field doc promises
    /// `None`-means-refused, at the socket the HELD fabricated-length slice
    /// plugs into. The AST builder refused the same input and counted it
    /// (`len_absent`), so the two halves of one contract disagreed and only the
    /// half with a witness was right.
    ///
    /// Unreachable through [`glue`] — asserted below — so this is fail-closed
    /// structure rather than a behaviour change, and it moves no corpus line.
    #[test]
    fn the_renderer_refuses_a_slice_adapter_with_no_length() {
        let lengthless = GlueSpec::core(GlueCore::FromRawParts, false);
        assert_eq!(
            lengthless.render("p"),
            None,
            "a length-bearing core with no length must REFUSE, never render \
             `() as usize` around an empty string"
        );
        assert_eq!(
            lengthless.wrapped().render("p"),
            None,
            "and the `Some` wrapper must not launder it either"
        );
        // With a length it renders normally, so the refusal is the missing
        // length rather than the shape.
        assert_eq!(
            GlueSpec::core(GlueCore::FromRawParts, false)
                .with_len("n")
                .render("p")
                .as_deref(),
            Some("unsafe { core::slice::from_raw_parts(p, (n) as usize) }")
        );
        // The gate is UPSTREAM and STAYS upstream after the fabrication ruling
        // — what changed is which answer it gives. `glue` still never names the
        // refusing shape: a `None` companion now yields a FABRICATED length, so
        // this renderer arm remains fail-closed structure with no live path.
        //
        // **This is the distinction the ruling's guard-evolution turns on.**
        // Fabrication happens AT the gate; no layer *below* it may invent a
        // length, so the refusal above is untouched.
        assert!(
            matches!(
                glue(Slice { mutable: false }, Raw, None),
                Ok(Some((
                    GlueSpec {
                        len: Some(SeamLen::Fabricated),
                        ..
                    },
                    _
                )))
            ),
            "glue must fabricate, not refuse — and the renderer's own refusal \
             must therefore stay unreachable through it"
        );
        assert!(
            every_emitting_spec()
                .iter()
                .all(|s| s.render("p").is_some()),
            "and every spec `glue` CAN name must still render, or the corpus \
             would move"
        );
    }

    /// **`index` IS REACHABLE, and `Bare`-without-a-wrapper is not** — the two
    /// halves of `shape_key`'s fallback arm, separated by measurement.
    ///
    /// The doc on that arm originally called the whole pairing unreachable
    /// "matched only to keep the function total". That is true of `Bare` and
    /// **false of `Index0`**: `glue`'s `(Ref, Slice)` arm builds exactly
    /// `core(Index0, w)`, which renders `&w X[0]` and classifies `index`. It is
    /// corpus-zero on the frozen corpus — and corpus-zero is not unreachable,
    /// which is the distinction this project has had to re-learn by name.
    ///
    /// Found by the maintainability reviewer at the arm-3 boundary. The code
    /// was right; the prose was not, so this is the witness the corrected prose
    /// needed rather than a second correction of it.
    #[test]
    fn first_and_optional_index_shapes_are_both_reachable() {
        let (spec, family) = glue(Ref { mutable: true }, Slice { mutable: true }, None)
            .expect("a mutable reference from a mutable slice is adaptable")
            .expect("and it needs an edit");
        assert_eq!(
            spec.shape_key(),
            "first",
            "reached through `glue`, not by hand"
        );
        assert_eq!(spec.render("p").unwrap(), "p.first_mut().unwrap()");
        assert_eq!(family, SeamFamily::Safe);
        assert!(
            !spec.optional && spec.unwrap.is_none(),
            "and with neither wrapper nor source unwrap: {spec:?}"
        );

        // The other half: no pairing `glue` accepts produces a bare core with
        // neither an unwrap nor a wrapper. Asserted over the SAME enumeration
        // the agreement test uses, so the claim is checked rather than argued.
        assert!(
            every_emitting_spec()
                .iter()
                .all(|s| !(matches!(s.core, GlueCore::Bare) && !s.optional && s.unwrap.is_none())),
            "a bare core with no wrapper renders the argument unchanged; `glue` \
             returns `Ok(None)` for every pairing that would need it"
        );
        // `Index0` remains reachable for the optional thin target over a slice.
        assert!(
            every_emitting_spec()
                .iter()
                .any(|s| matches!(s.core, GlueCore::Index0)),
            "the enumeration must still reach the optional `index` arm"
        );
    }

    /// **Where the two DISAGREE, and why that is the point of carrying it.**
    ///
    /// The classifier reads a string the argument's own text contributes to, so
    /// an argument that happens to start with `*` or contain `.unwrap()` moves
    /// the inferred label while the decision is unchanged. These rows are the
    /// schema semantics change condition 5 requires to be recorded — *strictly
    /// better provenance*, stated as a witness rather than as a claim.
    #[test]
    fn the_classifier_was_argument_text_sensitive_and_the_carried_shape_is_not() {
        // An `Index0` wrap over an argument spelled `*q` renders `Some(&*q[0])`,
        // whose prefix is `Some(&*` — the classifier called that `some_reborrow`.
        let index0_wrapped = GlueSpec::core(GlueCore::Index0, false).wrapped();
        assert_eq!(index0_wrapped.render("*q").unwrap(), "Some(&*q[0])");
        assert_eq!(
            inferred_shape(&index0_wrapped.render("*q").unwrap()),
            "some_reborrow"
        );
        assert_eq!(index0_wrapped.shape_key(), "some_wrap");

        // An argument that is itself an `.unwrap()` call captured rule 4, which
        // sits ABOVE every `Some(` test.
        let some_wrap = GlueSpec::core(GlueCore::Bare, false).wrapped();
        assert_eq!(
            inferred_shape(&some_wrap.render("o.unwrap()").unwrap()),
            "unwrap"
        );
        assert_eq!(some_wrap.shape_key(), "some_wrap");

        // And the carried answer does not move with the argument at all — the
        // property that makes the column mean the decision.
        for arg in ["p", "*q", "o.unwrap()", "(*s).ptr", "&mut *raw"] {
            assert_eq!(
                some_wrap.shape_key(),
                "some_wrap",
                "the carried shape must not depend on the argument text ({arg})"
            );
        }
    }

    /// Every `(spec, family)` `glue` can return, enumerated by driving `glue`
    /// over the whole `(expected, found)` product rather than by transcribing
    /// the arms a second time.
    ///
    /// Transcription is what the renderer oracle does, and doing it twice would
    /// make both copies agree with each other instead of with the function.
    fn every_emitting_spec() -> Vec<GlueSpec> {
        let forms = [
            Raw,
            Ref { mutable: true },
            Ref { mutable: false },
            Slice { mutable: true },
            Slice { mutable: false },
            Opt {
                mutable: true,
                slice: false,
            },
            Opt {
                mutable: false,
                slice: false,
            },
            Opt {
                mutable: true,
                slice: true,
            },
            Opt {
                mutable: false,
                slice: true,
            },
        ];
        let mut out = Vec::new();
        for expected in forms {
            for found in forms {
                if let Ok(Some((spec, _))) = glue(expected, found, Some("n")) {
                    out.push(if spec.null_arm == NullArm::Checked {
                        spec.with_checked_binding_type("*mut i32".to_owned())
                    } else {
                        spec
                    });
                }
            }
        }
        // **THE EXACT CARDINALITY, not a floor.** Wave 3 opens the twelve
        // §29 required-unwrap cells over the former 26-cell matrix.
        assert_eq!(
            out.len(),
            38,
            "the product must reach every emitting arm exactly; got {}",
            out.len()
        );
        out
    }
}

// ---------------------------------------------------------------------------
// The call-site walk
// ---------------------------------------------------------------------------

use rustc_hash::FxHashMap;
use rustc_hir::{HirId, def_id::LocalDefId};
use rustc_middle::ty::TyCtxt;

use super::{Decision, DecisionTable, Subject, SubjectKind, emitability::ArgShape};

/// What the walk produced: placed adapters, and every position it refused with
/// the reason it refused it.
///
/// **Blocked positions are carried, not dropped.** The ledger rule this module
/// exists under: an unadapted position becomes a revert, and a revert with no
/// reason is a yield number nobody can attribute.
#[derive(Clone, Debug, Default)]
pub(crate) struct SeamPlan {
    pub edits: Vec<SeamEdit>,
    pub body_edits: Vec<BodyEdit>,
    pub body_blocked: Vec<BlockedBody>,
    /// Rejected call positions, including the candidate and peer facts that
    /// existed before the gate.
    ///
    /// **The callee rides here because the CALLER is the wrong axis for
    /// pricing** (2026-08-12). A refused seam costs the *callee's* conversion —
    /// [`SeamEdit::owner_fn`] is the callee for exactly that reason, so that a
    /// reverted callee takes its seams with it — while this row named only the
    /// caller. Anything asking *"which functions would gain if this refusal
    /// went away"* was therefore answerable only on the axis that does not
    /// revert.
    ///
    /// Two names rather than one, because they are two different functions and
    /// collapsing them is what made the question unanswerable.
    pub blocked: Vec<BlockedSeam>,
    /// Every syntactic site-overlap position, including clear positions whose
    /// candidate is `none` and therefore has no placed/blocked edit row.
    pub overlap_proofs: Vec<A5PositionProof>,
    /// **Ruling item 4a — companion-length coverage**, one row per
    /// length-gated position: `(callee path, pointer param index, evidence)`.
    ///
    /// MEASUREMENT ONLY. Nothing branches on it and no seam is placed from it:
    /// the ruling sequences the instrument ahead of the decision, so this
    /// answers *whether a length exists* without yet claiming which expression
    /// it is.
    pub length_evidence: Vec<(String, usize, LenEvidence)>,
    /// Pairs that fired with **no row in the measured census** — rule 1
    /// (2026-08-11): coverage derives from the type-level matrix, and the census
    /// is a prioritization overlay. A pair appearing here is not an error; it is
    /// the overlay being incomplete, which is expected and must be visible.
    pub uncensused: Vec<(Form, Form)>,
    /// Raw-boundary T1/T2/blocked receipts, including zero-syntax sites.
    pub raw_boundary_receipts: String,
    /// Exact site atoms grouped by their converted subject. This is the sole
    /// source for declaration/use dependency closure during atom reverts.
    pub raw_boundary_atom_groups:
        rustc_hash::FxHashMap<(LocalDefId, HirId), Vec<super::raw_boundary::SubjectAtomKey>>,
    /// Exact call-argument regions already owned by a subject-use edit.
    ///
    /// A raw-boundary bridge over the same expression would be a second edit
    /// with an obsolete view of that expression.  These rows are the loud
    /// disposition of that collision: the existing use edit remains the sole
    /// owner and the raw arm emits no competing edit.
    pub raw_boundary_edit_region_owned: Vec<(String, String)>,
    /// Typed PAIR sites, including zero-syntax and blocked roles, retained for
    /// signature-class completeness rather than reconstructed from TSV.
    pub pair_sites: Vec<super::co_conversion::PairSiteDecision>,
    /// Raw-boundary sites whose source had a safe presentation but whose
    /// required bridge was held. These become terminal dropped class sites.
    pub raw_boundary_blocked: Vec<BlockedRawBoundary>,
    /// Inference-sensitive declaration shapes carried with their final type.
    pub explicit_declarations: Vec<ExplicitDeclarationSite>,
    /// Generated/zero-syntax bridge sites that still require plan and terminal
    /// receipts in their owning signature class.
    pub zero_bridges: Vec<ZeroBridgeSite>,
    /// Same-object T2 raw views grouped by call so every raw temp is created
    /// before any surviving safe borrow in the call expression.
    pub pair_raw_calls: Vec<PairRawViewCall>,
    /// Every resolved MIR call position whose callee parameter is emitted in a
    /// safe form. This inventory is independent of pointer-subject membership.
    pub interface_inventory: Vec<InterfaceInventorySite>,
    /// Required MIR sites derived directly from the emitted signature diff.
    ///
    /// Kept separate from `interface_inventory`: the latter is the observed
    /// receipt population and therefore cannot also be the control universe.
    pub emitted_signature_required_sites: BTreeSet<InterfaceInventoryKey>,
    pub interface_required_sites: BTreeSet<InterfaceInventoryKey>,
    /// A zero-syntax safe/safe site relies on the caller class remaining live.
    /// The callee therefore depends on that caller and follows its reversion.
    pub interface_dependencies: Vec<(SignatureClassId, SignatureClassId)>,
    /// A surfaced caller body names the callee's generated safe inner. The
    /// caller is therefore Ready only while the defining callee class is Ready.
    pub generated_item_dependencies: Vec<(SignatureClassId, SignatureClassId)>,
}

impl SeamPlan {
    pub(crate) fn converted_callee_without_site_receipt(&self) -> usize {
        let receipted = self
            .interface_inventory
            .iter()
            .map(|site| site.key)
            .collect::<BTreeSet<_>>();
        self.emitted_signature_required_sites
            .difference(&receipted)
            .map(|key| key.callee)
            .collect::<BTreeSet<_>>()
            .len()
    }

    pub(crate) fn sites_from_non_subject_arguments(&self) -> usize {
        self.interface_inventory
            .iter()
            .filter(|site| site.non_subject)
            .count()
    }

    pub(crate) fn interface_inventory_tsv(&self, tcx: TyCtxt<'_>) -> String {
        let mut out = String::from(
            "caller\tcallee\tblock\targument_index\tsource_shape\tnon_subject\tdisposition\n",
        );
        let mut rows = self.interface_inventory.clone();
        rows.sort_by_key(|site| site.key);
        for site in rows {
            out.push_str(&format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
                tcx.def_path_str(site.key.caller.local_def_id().to_def_id()),
                tcx.def_path_str(site.key.callee.local_def_id().to_def_id()),
                site.key.block,
                site.key.argument_index,
                site.source_shape,
                u8::from(site.non_subject),
                site.disposition,
            ));
        }
        out
    }
}

/// The form a decision emits.
fn form_of(decision: &Decision) -> Form {
    match decision {
        Decision::Ref { mutable } | Decision::InferredRef { mutable, .. } => {
            Form::Ref { mutable: *mutable }
        }
        Decision::Slice { mutable, .. } => Form::Slice { mutable: *mutable },
        Decision::Opt { mutable, slice, .. } => Form::Opt {
            mutable: *mutable,
            slice: *slice,
        },
        // A degraded subject keeps its raw pointer type.
        Decision::Box(_) | Decision::Degraded(_) => Form::Raw,
    }
}

fn receipt_arm(expected: Form, found: Form) -> &'static str {
    if expected != Form::Raw && found != Form::Raw {
        "glue"
    } else {
        "c"
    }
}

fn receipt_extent(spec: &GlueSpec) -> BridgeExtentKind {
    match spec.len.as_ref() {
        Some(SeamLen::Licensed(source)) => BridgeExtentKind::Evidence(source.clone()),
        Some(SeamLen::Fabricated) => BridgeExtentKind::Fallback,
        None => BridgeExtentKind::None,
    }
}

/// The 17 `(found, expected)` rows the 2026-08-11 census measured. **Not a
/// coverage bound** — see [`SeamPlan::uncensused`].
fn in_census(found: Form, expected: Form) -> bool {
    use Form::*;
    matches!(
        (found, expected),
        (Raw, Ref { .. })
            | (Raw, Slice { .. })
            | (Raw, Opt { slice: false, .. })
            | (Raw, Opt { slice: true, .. })
            | (Ref { .. }, Opt { slice: false, .. })
            | (Ref { .. }, Slice { .. })
            | (Ref { .. }, Raw)
    )
}

#[derive(Clone)]
struct Candidate {
    spec: GlueSpec,
    family: SeamFamily,
    replacement: String,
    len_arm: Option<LenArm>,
    retention: BridgeRetentionTier,
    waiver_id: Option<String>,
}

fn inbound_retention(
    retention: &super::raw_boundary::RetentionSummaries,
    callee: LocalDefId,
    argument_index: usize,
    return_tied: bool,
) -> Result<(BridgeRetentionTier, Option<String>), SeamBlock> {
    use super::raw_boundary::{RetentionEventKind, RetentionVerdict};

    match retention.get(callee, argument_index) {
        Some(RetentionVerdict::NoRetain { .. }) => Ok((BridgeRetentionTier::T1, None)),
        Some(RetentionVerdict::Retains { sink, .. })
            if sink.kind == RetentionEventKind::Return && return_tied =>
        {
            Ok((BridgeRetentionTier::T1, None))
        }
        Some(RetentionVerdict::Retains { .. }) => Err(SeamBlock::PositiveRetention),
        Some(RetentionVerdict::Unknown { .. }) | None => Ok((
            BridgeRetentionTier::T2,
            Some(RAW_BOUNDARY_T2_WAIVER_ID.to_owned()),
        )),
    }
}

fn root_label(
    labels: &FxHashMap<(LocalDefId, HirId), String>,
    owner: LocalDefId,
    root: Option<HirId>,
) -> String {
    root.and_then(|hir| labels.get(&(owner, hir)).cloned())
        .unwrap_or_else(|| "-".to_owned())
}

fn blocked_call(
    caller: LocalDefId,
    callee: LocalDefId,
    index: usize,
    span: Span,
    block: SeamBlock,
) -> BlockedSeam {
    BlockedSeam {
        caller,
        callee,
        index,
        span,
        block,
        expected: None,
        found: None,
        source_shape: "-",
        candidate_template: "unavailable".to_owned(),
        null_arm: "unavailable".to_owned(),
        extent_arm: "unavailable".to_owned(),
        root_identity: "-".to_owned(),
        blind: false,
        peers: Vec::new(),
        overlap: None,
    }
}

fn block_pair_raw_view(
    plan: &mut SeamPlan,
    pair: &super::co_conversion::PairSiteDecision,
    reason: &str,
) {
    plan.raw_boundary_blocked.push(BlockedRawBoundary {
        owner_class: SignatureClassId::of(pair.callee),
        bridge: BridgeSitePlan {
            caller: pair.caller,
            callee: BridgeCalleeId::Local(pair.callee),
            arm: "pair".to_owned(),
            position: format!("arg{}", pair.argument_index),
            bridge_kind: "pair-t2-raw-view".to_owned(),
            extent: BridgeExtentKind::None,
            retention: BridgeRetentionTier::T2,
            waiver_id: Some(RAW_BOUNDARY_T2_WAIVER_ID.to_owned()),
        },
        span: pair.span,
        reason: reason.to_owned(),
    });
}

fn call_spans_match(left: Span, right: Span) -> bool {
    let left = left.source_callsite();
    let right = right.source_callsite();
    left == right || left.contains(right) || right.contains(left)
}

fn existing_interface_disposition(
    plan: &SeamPlan,
    caller: LocalDefId,
    callee: LocalDefId,
    call_span: Span,
    index: usize,
) -> Option<&'static str> {
    if plan.edits.iter().any(|edit| {
        edit.bridge.caller == caller
            && edit.owner_class.local_def_id() == callee
            && edit.param_index == index
            && call_spans_match(edit.call_span, call_span)
    }) {
        return Some("bridged");
    }
    if plan.blocked.iter().any(|site| {
        site.caller == caller
            && site.callee == callee
            && site.index == index
            && call_spans_match(site.span, call_span)
    }) || plan.raw_boundary_blocked.iter().any(|site| {
        site.bridge.caller == caller
            && matches!(site.bridge.callee, BridgeCalleeId::Local(did) if did == callee)
            && site.bridge.position == format!("arg{index}")
            && call_spans_match(site.span, call_span)
    }) {
        return Some("held");
    }
    if plan.pair_sites.iter().any(|site| {
        site.caller == caller
            && site.callee == callee
            && site.argument_index == index
            && call_spans_match(site.call_span, call_span)
    }) {
        return Some("pair");
    }
    if plan.zero_bridges.iter().any(|site| {
        site.caller == caller
            && site.owner_class.local_def_id() == callee
            && site.position == format!("arg{index}")
            && site
                .span
                .is_some_and(|span| call_spans_match(span, call_span))
    }) {
        return Some("zero-syntax");
    }
    None
}

fn argument_form(
    caller: LocalDefId,
    arg: &super::emitability::Arg,
    decisions: &FxHashMap<(LocalDefId, HirId), &Decision>,
) -> Form {
    match arg.shape {
        ArgShape::BareLocal(hir) | ArgShape::CastOfLocal { binding: hir, .. } => decisions
            .get(&(caller, hir))
            .map_or(Form::Raw, |decision| form_of(decision)),
        ArgShape::AddrOf { mutable, .. } | ArgShape::AddrOfCast { mutable, .. } => {
            Form::Ref { mutable }
        }
        ArgShape::RawExpr { .. } | ArgShape::NullLit | ArgShape::Cast { .. } | ArgShape::Other => {
            Form::Raw
        }
    }
}

fn complete_interface_inventory(
    facts: &super::emitability::EmitabilityFacts,
    table: &DecisionTable,
    c9_marks: &[crate::analyses::borrow_ownership::a5_producer::PlannedC9Mark],
    lifetime_eligibility: &super::lifetime::LifetimeEligibility,
    decisions: &FxHashMap<(LocalDefId, HirId), &Decision>,
    params: &FxHashMap<(LocalDefId, usize), (LocalDefId, HirId)>,
    plan: &mut SeamPlan,
) {
    let Some(web) = lifetime_eligibility.fnptr_web() else {
        return;
    };

    // Derive the required universe before observing any bridge/inventory row.
    // Base-path parameter decisions are the source of truth for emitted type
    // changes; lifetime plans and wrapper surfaces can add signature syntax,
    // but their pointer parameter positions are already represented here.
    let emitted_parameters = params
        .iter()
        .filter_map(|(&(callee, index), node)| {
            decisions
                .get(node)
                .map(|decision| form_of(decision))
                .filter(|form| *form != Form::Raw)
                .map(|form| ((callee, index), form))
        })
        .collect::<FxHashMap<_, _>>();
    let mut emitted_signature_classes = emitted_parameters
        .keys()
        .map(|&(callee, _)| callee)
        .collect::<rustc_hash::FxHashSet<_>>();
    emitted_signature_classes.extend(table.lifetime_plan.functions().map(|(callee, _)| callee));
    if let Some(exposure) = table.exposure.as_ref() {
        emitted_signature_classes.extend(exposure.functions().iter().filter_map(|row| {
            (!matches!(
                row.plan,
                super::exposure::ExposureSurfacePlan::NotApplicable
            ))
            .then_some(row.did)
        }));
    }
    for mir_site in web.mir_call_sites() {
        if let Some(exposure) = table.exposure.as_ref()
            && matches!(
                exposure.plan(mir_site.caller),
                super::exposure::ExposureSurfacePlan::PositiveSeedShim
                    | super::exposure::ExposureSurfacePlan::FnPtrRawWrapper
            )
            && matches!(
                exposure.plan(mir_site.callee),
                super::exposure::ExposureSurfacePlan::PositiveSeedShim
                    | super::exposure::ExposureSurfacePlan::FnPtrRawWrapper
            )
            && mir_site.caller != mir_site.callee
        {
            plan.generated_item_dependencies.push((
                SignatureClassId::of(mir_site.caller),
                SignatureClassId::of(mir_site.callee),
            ));
        }
        if !emitted_signature_classes.contains(&mir_site.callee) {
            continue;
        }
        for index in 0..mir_site.argument_count {
            if !emitted_parameters.contains_key(&(mir_site.callee, index)) {
                continue;
            }
            plan.emitted_signature_required_sites
                .insert(InterfaceInventoryKey {
                    caller: SignatureClassId::of(mir_site.caller),
                    callee: SignatureClassId::of(mir_site.callee),
                    block: mir_site.block,
                    argument_index: index,
                });
        }
    }

    for mir_site in web.mir_call_sites() {
        let hir_site = facts.call_args.get(&mir_site.callee).and_then(|sites| {
            sites.iter().find(|site| {
                site.caller == mir_site.caller && call_spans_match(site.span, mir_site.span)
            })
        });
        let c9_positions = hir_site.map_or_else(rustc_hash::FxHashSet::default, |site| {
            super::co_conversion::retained_c9_shared_params(c9_marks, site, mir_site.callee)
        });
        for index in 0..mir_site.argument_count {
            let Some(&expected) = emitted_parameters.get(&(mir_site.callee, index)) else {
                continue;
            };
            let key = InterfaceInventoryKey {
                caller: SignatureClassId::of(mir_site.caller),
                callee: SignatureClassId::of(mir_site.callee),
                block: mir_site.block,
                argument_index: index,
            };
            plan.interface_required_sites.insert(key);
            let argument =
                hir_site.and_then(|site| site.args.iter().find(|arg| arg.index == index));
            let argument_span = argument.map_or(mir_site.span, |arg| arg.span);
            let non_subject = argument.is_none_or(|arg| {
                !matches!(
                    arg.shape,
                    ArgShape::BareLocal(hir) if decisions.contains_key(&(mir_site.caller, hir))
                )
            });

            let disposition = if c9_positions.contains(&index) {
                "c9-snapshot"
            } else if let Some(disposition) = existing_interface_disposition(
                plan,
                mir_site.caller,
                mir_site.callee,
                mir_site.span,
                index,
            ) {
                disposition
            } else if let Some(argument) = argument {
                let found = argument_form(mir_site.caller, argument, decisions);
                if matches!(glue(expected, found, None), Ok(None)) {
                    plan.zero_bridges.push(ZeroBridgeSite {
                        owner_class: SignatureClassId::of(mir_site.callee),
                        caller: mir_site.caller,
                        span: Some(argument.span),
                        arm: receipt_arm(expected, found),
                        position: format!("arg{index}"),
                        bridge_kind: "interface-call-zero-syntax",
                        retention: BridgeRetentionTier::None,
                        waiver_id: None,
                    });
                    if matches!(
                        argument.shape,
                        ArgShape::BareLocal(_) | ArgShape::CastOfLocal { .. }
                    ) && found != Form::Raw
                        && mir_site.caller != mir_site.callee
                    {
                        plan.interface_dependencies.push((
                            SignatureClassId::of(mir_site.callee),
                            SignatureClassId::of(mir_site.caller),
                        ));
                    }
                    "zero-syntax"
                } else {
                    plan.raw_boundary_blocked.push(BlockedRawBoundary {
                        owner_class: SignatureClassId::of(mir_site.callee),
                        bridge: BridgeSitePlan::local(
                            mir_site.caller,
                            mir_site.callee,
                            receipt_arm(expected, found),
                            format!("arg{index}"),
                            "inventory-non-subject-held",
                        ),
                        span: argument.span,
                        reason: "inventory-missing-expression-bridge".to_owned(),
                    });
                    "held"
                }
            } else if table.exposure.as_ref().is_some_and(|exposure| {
                matches!(
                    exposure.plan(mir_site.callee),
                    super::exposure::ExposureSurfacePlan::PositiveSeedShim
                        | super::exposure::ExposureSurfacePlan::FnPtrRawWrapper
                )
            }) {
                plan.zero_bridges.push(ZeroBridgeSite {
                    owner_class: SignatureClassId::of(mir_site.callee),
                    caller: mir_site.caller,
                    span: Some(mir_site.span),
                    arm: "surface",
                    position: format!("arg{index}"),
                    bridge_kind: "interface-fnptr-raw-wrapper",
                    retention: BridgeRetentionTier::None,
                    waiver_id: None,
                });
                "raw-wrapper"
            } else {
                plan.raw_boundary_blocked.push(BlockedRawBoundary {
                    owner_class: SignatureClassId::of(mir_site.callee),
                    bridge: BridgeSitePlan::local(
                        mir_site.caller,
                        mir_site.callee,
                        receipt_arm(expected, Form::Raw),
                        format!("arg{index}"),
                        "inventory-non-subject-held",
                    ),
                    span: mir_site.span,
                    reason: "inventory-missing-hir-argument-site".to_owned(),
                });
                "held"
            };
            plan.interface_inventory.push(InterfaceInventorySite {
                key,
                call_span: mir_site.span,
                argument_span,
                source_shape: argument.map_or("mir-only", |arg| arg.shape.key()),
                non_subject,
                disposition,
            });
        }
    }
    plan.interface_inventory.sort_by_key(|site| site.key);
    plan.interface_inventory.dedup_by_key(|site| site.key);
    plan.interface_dependencies.sort();
    plan.interface_dependencies.dedup();
    plan.generated_item_dependencies.sort();
    plan.generated_item_dependencies.dedup();
}

/// Compute every seam adapter the crate needs.
///
/// Driven by the **type-level matrix**: the walk asks [`glue`] about every
/// `(expected, found)` pair it meets and the `match` there is exhaustive, so a
/// pair with no census row is adapted rather than skipped. The census only says
/// which pairs are *common*.
pub(crate) fn synthesize(
    tcx: TyCtxt<'_>,
    facts: &super::emitability::EmitabilityFacts,
    subjects: &[Subject],
    table: &DecisionTable,
    c9_marks: &[crate::analyses::borrow_ownership::a5_producer::PlannedC9Mark],
    a5_site_proofs: &A5SeamProofIndex,
    retention: &super::raw_boundary::RetentionSummaries,
    lifetime_eligibility: &super::lifetime::LifetimeEligibility,
) -> SeamPlan {
    let coconv = super::co_conversion::CoConv::default();
    synthesize_with_raw_boundary(
        tcx,
        facts,
        subjects,
        table,
        c9_marks,
        a5_site_proofs,
        &super::raw_boundary::RawBoundaryDispositionIndex::default(),
        &coconv,
        retention,
        lifetime_eligibility,
    )
}

pub(crate) fn synthesize_with_raw_boundary(
    tcx: TyCtxt<'_>,
    facts: &super::emitability::EmitabilityFacts,
    subjects: &[Subject],
    table: &DecisionTable,
    c9_marks: &[crate::analyses::borrow_ownership::a5_producer::PlannedC9Mark],
    a5_site_proofs: &A5SeamProofIndex,
    raw_boundary: &super::raw_boundary::RawBoundaryDispositionIndex,
    coconv: &super::co_conversion::CoConv,
    retention: &super::raw_boundary::RetentionSummaries,
    lifetime_eligibility: &super::lifetime::LifetimeEligibility,
) -> SeamPlan {
    let sm = tcx.sess.source_map();
    let mut plan = SeamPlan::default();
    plan.pair_sites = coconv.pair_sites().to_vec();

    // subject key -> decision, and (fn, param index) -> subject key.
    let mut decision_of: FxHashMap<(LocalDefId, HirId), &Decision> = FxHashMap::default();
    let mut labels: FxHashMap<(LocalDefId, HirId), String> = FxHashMap::default();
    for (subject, decision) in &table.entries {
        decision_of.insert((subject.fn_did, subject.hir_id), decision);
        labels.insert((subject.fn_did, subject.hir_id), subject.label.clone());
    }
    let mut param_key: FxHashMap<(LocalDefId, usize), (LocalDefId, HirId)> = FxHashMap::default();
    for subject in subjects {
        if let SubjectKind::Param { hir_index } = subject.kind {
            param_key.insert(
                (subject.fn_did, hir_index),
                (subject.fn_did, subject.hir_id),
            );
        }
    }

    // Deterministic callee order: `FxHashMap` iteration permutes between runs,
    // and D19 makes a report whose order permutes non-comparable.
    let mut callees: Vec<&LocalDefId> = facts.call_args.keys().collect();
    callees.sort_unstable_by_key(|d| d.local_def_index.as_u32());

    for callee in callees {
        for site in &facts.call_args[callee] {
            let marked_shared =
                super::co_conversion::retained_c9_shared_params(c9_marks, site, *callee);
            // ---- pass 1: what each position will look like after conversion ----
            //
            // Computed for the WHOLE site before any edit is emitted, because
            // the overlap gate below is a within-site question and cannot be
            // answered one argument at a time.
            //
            // A named struct rather than a tuple: `positions` deliberately does
            // NOT align with `site.args` (raw and unnameable positions are
            // dropped), so every field a later pass needs must be carried here.
            // Recovering the span by re-searching `site.args` was the first
            // shape and it reconstructed an alignment this list does not have.
            struct Pos {
                span: Span,
                /// The CALLEE's parameter index — item 4a asks about the
                /// signature, so the position must carry which parameter it is.
                index: usize,
                expected: Form,
                found: Form,
                text: Option<String>,
                /// **Where `text` was read from.** Equal to `span` for every
                /// shape except the two cast shapes, whose snippet comes from
                /// the cast's OPERAND while the replaced range is the whole
                /// argument. Carried because the AST layer must keep that
                /// operand as its subtree, and only this side knows which it
                /// was.
                text_span: Span,
                root: Option<HirId>,
                blind: bool,
                /// A literal `None` carries no borrow and therefore cannot
                /// participate in the site's overlap relation.
                borrows: bool,
                literal_null: bool,
                /// The raw-boundary arm already owns (or has rendered inert)
                /// this position. It enters PAIR for proof/receipt coverage,
                /// never so this seam stage can block or edit it.
                raw_boundary_observation: bool,
                source_shape: &'static str,
                source_type: String,
            }
            let mut positions: Vec<Pos> = Vec::new();
            for arg in &site.args {
                // C-9 rewrites this argument to `&snapshot_tmp` after the
                // ordinary use/seam passes. No seam or within-site overlap
                // gate applies to the original expression at this position.
                if marked_shared.contains(&arg.index) {
                    continue;
                }
                let expected = param_key
                    .get(&(*callee, arg.index))
                    .and_then(|k| decision_of.get(k))
                    .map_or(Form::Raw, |d| form_of(d));
                let raw_boundary_observation = raw_boundary.tracks_call_argument(
                    site.caller,
                    &tcx.def_path_str(callee.to_def_id()),
                    arg.span,
                    arg.index,
                );
                // A raw parameter needs nothing: a reference coerces to a raw
                // pointer at a call, so every found form satisfies it. The
                // raw-boundary market is the one exception to dropping the
                // position entirely: PAIR owes its A5 receipt even when the
                // boundary bridge itself rendered as zero syntax.
                if matches!(expected, Form::Raw) && !raw_boundary_observation {
                    continue;
                }
                // The third element is the span `text` is read from — carried
                // out of this match rather than reconstructed below, because
                // the two cast shapes read the OPERAND's snippet while every
                // other shape reads the argument's own.
                let (found, text, blind, borrows, literal_null) = match arg.shape {
                    ArgShape::BareLocal(hir) => (
                        decision_of
                            .get(&(site.caller, hir))
                            .map_or(Form::Raw, |d| form_of(d)),
                        sm.span_to_snippet(arg.span).ok(),
                        false,
                        true,
                        false,
                    ),
                    ArgShape::AddrOf {
                        mutable,
                        base,
                        through_deref,
                    } => {
                        // §5a: a borrow rooted through a RAW deref is invisible
                        // to borrowck. Blind exactly when the base does not
                        // itself convert.
                        let blind = match (base, through_deref) {
                            (None, _) => true,
                            (Some(b), true) => !decision_of
                                .get(&(site.caller, b))
                                .is_some_and(|d| !matches!(d, Decision::Degraded(_))),
                            (Some(_), false) => false,
                        };
                        (
                            Form::Ref { mutable },
                            sm.span_to_snippet(arg.span).ok(),
                            blind,
                            true,
                            false,
                        )
                    }
                    ArgShape::AddrOfCast { mutable, inner } => (
                        Form::Ref { mutable },
                        sm.span_to_snippet(inner).ok(),
                        true,
                        true,
                        false,
                    ),
                    ArgShape::CastOfLocal { binding, inner } => (
                        decision_of
                            .get(&(site.caller, binding))
                            .map_or(Form::Raw, |d| form_of(d)),
                        sm.span_to_snippet(inner).ok(),
                        false,
                        true,
                        false,
                    ),
                    ArgShape::RawExpr { .. } => (
                        Form::Raw,
                        sm.span_to_snippet(arg.span).ok(),
                        true,
                        true,
                        false,
                    ),
                    ArgShape::NullLit if matches!(expected, Form::Opt { .. }) => (
                        Form::Raw,
                        sm.span_to_snippet(arg.span).ok(),
                        false,
                        false,
                        true,
                    ),
                    // Not an expression this slice can name.
                    ArgShape::NullLit | ArgShape::Cast { .. } | ArgShape::Other => {
                        plan.blocked.push(blocked_call(
                            site.caller,
                            *callee,
                            arg.index,
                            arg.span,
                            SeamBlock::UnnameableOperand,
                        ));
                        continue;
                    }
                };
                // The two reads are kept in step by CONSTRUCTION: `text` is
                // the snippet of exactly this span, so a shape whose operand
                // moves moves both or neither.
                let Some(text_span) = text_span_of(arg.shape, arg.span) else {
                    // Unreachable — the shapes with no nameable operand are
                    // blocked above. Fail-closed rather than defaulting to
                    // `arg.span`, which would hand the AST layer a subtree the
                    // replacement was not built from.
                    plan.blocked.push(blocked_call(
                        site.caller,
                        *callee,
                        arg.index,
                        arg.span,
                        SeamBlock::UnnameableOperand,
                    ));
                    continue;
                };
                positions.push(Pos {
                    span: arg.span,
                    index: arg.index,
                    expected,
                    found,
                    text,
                    text_span,
                    root: arg.shape.place_root(),
                    blind,
                    borrows,
                    literal_null,
                    raw_boundary_observation,
                    source_shape: arg.shape.key(),
                    source_type: arg.source_type.clone(),
                });
            }

            // ---- pass 1.5: build every candidate BEFORE the site gate ----
            //
            // The old tuple receipt was poor because the gate ran before the
            // only `glue` call. Building here is observational: no AST node is
            // claimed and no edit is emitted until pass 3.
            let candidates = positions
                .iter()
                .map(|pos| {
                    let Some(text) = pos.text.as_deref() else {
                        return Err(SeamBlock::UnnameableOperand);
                    };
                    let wants_len = matches!(
                        (pos.expected, pos.found),
                        (Form::Slice { .. }, Form::Raw)
                            | (Form::Opt { slice: true, .. }, Form::Raw)
                    ) && !pos.literal_null;
                    let (len_text, len_evidence) = if wants_len {
                        let arm = length_evidence(tcx, *callee, pos.index);
                        let companion = match arm {
                            LenEvidence::Following => Some(pos.index + 1),
                            LenEvidence::Preceding => pos.index.checked_sub(1),
                            LenEvidence::Elsewhere | LenEvidence::None => None,
                        };
                        (
                            companion
                                .and_then(|i| site.args.iter().find(|a| a.index == i))
                                .and_then(|a| sm.span_to_snippet(a.span).ok()),
                            Some(arm),
                        )
                    } else {
                        (None, None)
                    };
                    let result = if pos.literal_null {
                        glue_null(pos.expected)
                    } else {
                        glue(pos.expected, pos.found, len_text.as_deref())
                    };
                    result.and_then(|answer| {
                        answer
                            .map(|(spec, family)| {
                                let spec = if spec.null_arm == NullArm::Checked {
                                    spec.with_checked_binding_type(pos.source_type.clone())
                                } else {
                                    spec
                                };
                                let replacement =
                                    spec.render(text).ok_or(SeamBlock::LengthUnknown)?;
                                let len_arm = spec.len.as_ref().zip(len_evidence).map(|(l, e)| {
                                    if l.is_fabricated() {
                                        LenArm::Fabricated(e)
                                    } else {
                                        LenArm::Licensed(e)
                                    }
                                });
                                let (retention, waiver_id) =
                                    if pos.found == Form::Raw && pos.expected != Form::Raw {
                                        inbound_retention(
                                            retention,
                                            *callee,
                                            pos.index,
                                            table
                                                .lifetime_plan
                                                .function(*callee)
                                                .and_then(|plan| {
                                                    plan.lifetime_for(
                                                        super::lifetime::FnSignatureSlot::RETURN,
                                                    )
                                                })
                                                .is_some(),
                                        )?
                                    } else {
                                        (BridgeRetentionTier::None, None)
                                    };
                                Ok(Candidate {
                                    spec,
                                    family,
                                    replacement,
                                    len_arm,
                                    retention,
                                    waiver_id,
                                })
                            })
                            .transpose()
                    })
                })
                .collect::<Vec<_>>();

            // ---- pass 2: THE SITE GATES, applied to adapter-generated
            // arguments exactly as to converted ones (ruling item 3) ----
            //
            // No bypass. The reborrow family puts its borrow in the region §5a
            // measured borrowck as blind in, so this gate is the only thing
            // standing between a seam and silent UB.
            let is_mut = |f: &Form| {
                matches!(
                    f,
                    Form::Ref { mutable: true }
                        | Form::Slice { mutable: true }
                        | Form::Opt { mutable: true, .. }
                )
            };
            let mut conflicts = vec![Vec::<PeerConflict>::new(); positions.len()];
            for i in 0..positions.len() {
                for j in (i + 1)..positions.len() {
                    if !positions[i].borrows || !positions[j].borrows {
                        continue;
                    }
                    // Two SHARED borrows of one place are legal, so a conflict
                    // needs at least one `&mut`.
                    let left_form = if positions[i].raw_boundary_observation {
                        positions[i].found
                    } else {
                        positions[i].expected
                    };
                    let right_form = if positions[j].raw_boundary_observation {
                        positions[j].found
                    } else {
                        positions[j].expected
                    };
                    if !is_mut(&left_form) && !is_mut(&right_form) {
                        continue;
                    }
                    let same_root = !matches!(
                        (positions[i].root, positions[j].root),
                        (Some(x), Some(y)) if x != y
                    );
                    // An active raw-boundary pair already owns its syntax and
                    // therefore cannot be blocked here, but the external PAIR
                    // control still requires the attested A5 verdict even when
                    // the syntactic roots look distinct. Ordinary seam pairs
                    // retain the established same-root/blind trigger exactly.
                    let boundary_observation = positions[i].raw_boundary_observation
                        && positions[j].raw_boundary_observation;
                    if same_root || positions[i].blind || positions[j].blind || boundary_observation
                    {
                        let (left_blind, right_blind) = if positions[i].index <= positions[j].index
                        {
                            (positions[i].blind, positions[j].blind)
                        } else {
                            (positions[j].blind, positions[i].blind)
                        };
                        let proof = a5_site_proofs.lookup(
                            site.caller.local_def_index.as_u32(),
                            callee.local_def_index.as_u32(),
                            positions[i].index,
                            positions[j].index,
                            positions[i].span,
                            positions[j].span,
                        );
                        let conflict = PeerConflict {
                            left: positions[i].index.min(positions[j].index),
                            right: positions[i].index.max(positions[j].index),
                            same_root,
                            left_blind,
                            right_blind,
                            proof,
                        };
                        conflicts[i].push(conflict.clone());
                        conflicts[j].push(conflict);
                    }
                }
            }

            // ---- pass 3: emit ----
            for (idx, pos) in positions.iter().enumerate() {
                let (candidate_template, null_arm, extent_arm) = match &candidates[idx] {
                    Ok(Some(candidate)) => (
                        candidate.spec.template_key().to_owned(),
                        match candidate.spec.null_arm_key() {
                            "-" => "none".to_owned(),
                            value => value.to_owned(),
                        },
                        match candidate.spec.extent_arm_key() {
                            "-" => "none".to_owned(),
                            value => value.to_owned(),
                        },
                    ),
                    Ok(None) => ("none".to_owned(), "none".to_owned(), "none".to_owned()),
                    Err(block) => (
                        format!("error:{}", block.key()),
                        "unavailable".to_owned(),
                        "unavailable".to_owned(),
                    ),
                };
                let overlap = (!conflicts[idx].is_empty()).then(|| {
                    A5PositionProof::from_conflicts(
                        site.caller,
                        *callee,
                        pos.index,
                        pos.span,
                        candidate_template.clone(),
                        &conflicts[idx],
                        a5_site_proofs,
                    )
                });
                let pair_owned = coconv.pair_sites().iter().any(|pair| {
                    pair.caller == site.caller
                        && pair.callee == *callee
                        && pair.argument_index == pos.index
                        && pair
                            .call_span
                            .source_callsite()
                            .contains(site.span.source_callsite())
                        && pair.role != super::co_conversion::PairRole::Blocked
                });
                if !pair_owned && let Some(proof) = &overlap {
                    plan.overlap_proofs.push(proof.clone());
                }
                if overlap
                    .as_ref()
                    .is_some_and(|proof| !proof.clears_site_overlap())
                    && !pos.raw_boundary_observation
                    && !pair_owned
                {
                    plan.blocked.push(BlockedSeam {
                        caller: site.caller,
                        callee: *callee,
                        index: pos.index,
                        span: pos.span,
                        block: SeamBlock::SiteOverlap,
                        expected: Some(pos.expected),
                        found: Some(pos.found),
                        source_shape: pos.source_shape,
                        candidate_template: candidate_template.clone(),
                        null_arm: null_arm.clone(),
                        extent_arm: extent_arm.clone(),
                        root_identity: root_label(&labels, site.caller, pos.root),
                        blind: pos.blind,
                        peers: conflicts[idx].clone(),
                        overlap,
                    });
                    continue;
                }
                match &candidates[idx] {
                    Ok(None) => {}
                    Ok(Some(candidate)) => {
                        if let Some(emitted_type) = candidate.spec.checked_binding_type.clone() {
                            plan.explicit_declarations.push(ExplicitDeclarationSite {
                                owner_class: SignatureClassId::of(*callee),
                                caller: site.caller,
                                node: None,
                                span: Some(pos.span),
                                category: "local-temp",
                                emitted_type,
                                replacement: None,
                                arm: "glue",
                            });
                        }
                        // Rule 1 (2026-08-11): the census is a prioritization
                        // overlay, so a pair with no row is REPORTED, not
                        // refused.
                        if !in_census(pos.found, pos.expected) {
                            plan.uncensused.push((pos.found, pos.expected));
                        }
                        // The `lengated` census row is keyed on the SPEC too,
                        // for the same reason: it exists to preserve the 42/51
                        // derivability split across fabrication, so it must fire
                        // exactly where fabrication happened.
                        if let Some(LenArm::Fabricated(e)) = candidate.len_arm {
                            plan.length_evidence.push((
                                tcx.def_path_str(callee.to_def_id()),
                                pos.index,
                                e,
                            ));
                        }
                        plan.edits.push(SeamEdit {
                            span: pos.span,
                            call_span: site.span,
                            replacement: candidate.replacement.clone(),
                            owner_class: SignatureClassId::of(*callee),
                            bridge: BridgeSitePlan {
                                caller: site.caller,
                                callee: BridgeCalleeId::Local(*callee),
                                arm: receipt_arm(pos.expected, pos.found).to_owned(),
                                position: format!("arg{}", pos.index),
                                bridge_kind: candidate.spec.template_key().to_owned(),
                                extent: receipt_extent(&candidate.spec),
                                retention: candidate.retention,
                                waiver_id: candidate.waiver_id.clone(),
                            },
                            owner_fn: tcx.def_path_str(callee.to_def_id()),
                            lifetime_plan_digest: table
                                .lifetime_plan
                                .function(*callee)
                                .map(super::lifetime::FunctionPlan::digest),
                            caller_fn: tcx.def_path_str(site.caller.to_def_id()),
                            param_index: pos.index,
                            source_shape: pos.source_shape,
                            family: candidate.family,
                            len_arm: candidate.len_arm,
                            spec: candidate.spec.clone(),
                            arg_span: pos.text_span,
                            expected: pos.expected,
                            found: pos.found,
                            root_identity: root_label(&labels, site.caller, pos.root),
                            blind: pos.blind,
                            overlap,
                            atom_ids: Vec::new(),
                        });
                    }
                    Err(block) => {
                        plan.blocked.push(BlockedSeam {
                            caller: site.caller,
                            callee: *callee,
                            index: pos.index,
                            span: pos.span,
                            block: *block,
                            expected: Some(pos.expected),
                            found: Some(pos.found),
                            source_shape: pos.source_shape,
                            candidate_template: format!("error:{}", block.key()),
                            null_arm: "unavailable".to_owned(),
                            extent_arm: "unavailable".to_owned(),
                            root_identity: root_label(&labels, site.caller, pos.root),
                            blind: pos.blind,
                            peers: Vec::new(),
                            overlap,
                        });
                    }
                }
            }
        }
    }

    // Raw-boundary wave 1 — explicit safe-to-raw sites. Zero-syntax and
    // lifecycle templates remain in the receipt but produce no edit.
    plan.raw_boundary_receipts = raw_boundary.receipts_tsv();
    plan.raw_boundary_atom_groups = raw_boundary.subject_atom_groups();
    for pair in coconv
        .pair_sites()
        .iter()
        .filter(|pair| pair.role == super::co_conversion::PairRole::RawView)
    {
        if let Some(node) = pair.source_node {
            plan.raw_boundary_atom_groups.entry(node).or_default().push(
                super::raw_boundary::SubjectAtomKey {
                    id: pair.atom_id(),
                    node,
                    owner: tcx.def_path_str(pair.caller.to_def_id()),
                },
            );
        }
    }
    for atoms in plan.raw_boundary_atom_groups.values_mut() {
        atoms.sort_by(|left, right| left.id.cmp(&right.id));
        atoms.dedup_by(|left, right| left.id == right.id);
    }
    for (key, disposition, site) in raw_boundary.emission_sites() {
        let Some(template) = disposition.template() else {
            if let super::raw_boundary::RawBoundaryDisposition::Blocked { reason, .. } = disposition
                && site.target.depth2.is_some()
                && let Some((owner_did, node)) = site.node
                && decision_of
                    .get(&(owner_did, node))
                    .is_some_and(|decision| !matches!(decision, Decision::Degraded(_)))
            {
                plan.raw_boundary_blocked.push(BlockedRawBoundary {
                    owner_class: SignatureClassId::of(owner_did),
                    bridge: BridgeSitePlan {
                        caller: owner_did,
                        callee: site.callee_local.map_or_else(
                            || BridgeCalleeId::Foreign(key.callee.path.clone()),
                            BridgeCalleeId::Local,
                        ),
                        arm: "c".to_owned(),
                        position: format!("arg{}", key.argument_index),
                        bridge_kind: if site.target.depth2.is_some() {
                            "depth2-npo-bridge".to_owned()
                        } else {
                            reason.key().to_owned()
                        },
                        extent: BridgeExtentKind::None,
                        retention: BridgeRetentionTier::None,
                        waiver_id: None,
                    },
                    span: site.span,
                    reason: reason.key().to_owned(),
                });
            }
            continue;
        };
        let argument_span = site
            .direct_storage_span
            .unwrap_or(site.adapter_operand_span);
        let Ok(argument) = sm.span_to_snippet(argument_span) else {
            continue;
        };
        let spec = GlueSpec::raw_boundary_target(template, &site.target, site.box_slice, false);
        let exact_subject_use = site
            .node
            .and_then(|node| decision_of.get(&node).copied())
            .into_iter()
            .flat_map(|decision| match decision {
                Decision::Slice { uses, .. } | Decision::Opt { uses, .. } => uses.as_slice(),
                Decision::Ref { .. }
                | Decision::InferredRef { .. }
                | Decision::Box(_)
                | Decision::Degraded(_) => &[],
            })
            .filter(|edit| edit.span == site.span)
            .collect::<Vec<_>>();
        if exact_subject_use.len() == 1 {
            plan.raw_boundary_edit_region_owned.push((
                super::raw_boundary::site_atom_id(key),
                "raw-boundary-edit-region-owned".to_owned(),
            ));
            continue;
        }
        let Some(replacement) = spec.render(&argument) else {
            continue;
        };
        match template.render(
            &argument,
            site.target.mutability,
            site.box_slice,
            spec.raw_boundary
                .as_ref()
                .and_then(|raw| raw.cast_pointee.as_deref()),
        ) {
            Ok(super::raw_boundary::BridgeRender::Edit(_)) => {}
            Ok(
                super::raw_boundary::BridgeRender::ZeroSyntax
                | super::raw_boundary::BridgeRender::Lifecycle,
            ) => continue,
            Err(_) => continue,
        }
        let found = site
            .node
            .and_then(|node| decision_of.get(&node).copied())
            .map_or(Form::Raw, form_of);
        let atom_ids = site
            .node
            .and_then(|node| plan.raw_boundary_atom_groups.get(&node))
            .map(|atoms| atoms.iter().map(|atom| atom.id.clone()).collect())
            .unwrap_or_default();
        let Some((owner_did, _)) = site.node else {
            continue;
        };
        let (retention, waiver_id) = match disposition {
            super::raw_boundary::RawBoundaryDisposition::T1 { .. } => {
                (BridgeRetentionTier::T1, None)
            }
            super::raw_boundary::RawBoundaryDisposition::T2 { waiver_id, .. } => {
                debug_assert_eq!(*waiver_id, RAW_BOUNDARY_T2_WAIVER_ID);
                (BridgeRetentionTier::T2, Some((*waiver_id).to_owned()))
            }
            super::raw_boundary::RawBoundaryDisposition::Blocked { .. }
            | super::raw_boundary::RawBoundaryDisposition::OwnedByOtherArm { .. } => continue,
        };
        plan.edits.push(SeamEdit {
            span: site.span,
            call_span: site.call_span,
            replacement,
            owner_class: SignatureClassId::of(owner_did),
            bridge: BridgeSitePlan {
                caller: owner_did,
                callee: site.callee_local.map_or_else(
                    || BridgeCalleeId::Foreign(key.callee.path.clone()),
                    BridgeCalleeId::Local,
                ),
                arm: "c".to_owned(),
                position: format!("arg{}", key.argument_index),
                bridge_kind: template.key().to_owned(),
                extent: receipt_extent(&spec),
                retention,
                waiver_id,
            },
            owner_fn: key.caller.clone(),
            lifetime_plan_digest: None,
            caller_fn: key.caller.clone(),
            param_index: key.argument_index,
            source_shape: site.source_shape,
            family: SeamFamily::Safe,
            len_arm: None,
            spec,
            arg_span: argument_span,
            expected: Form::Raw,
            found,
            root_identity: key.subject.clone(),
            blind: false,
            overlap: None,
            atom_ids,
        });
    }

    // PAIR raw views are grouped by call. Their temps must be evaluated before
    // any surviving safe borrow, so an argument-local edit is insufficient.
    let mut pair_raw_calls = BTreeMap::<(u32, u32, u32, u32), PairRawViewCall>::new();
    for pair in coconv
        .pair_sites()
        .iter()
        .filter(|pair| pair.role == super::co_conversion::PairRole::RawView)
    {
        if pair.tier != super::co_conversion::PairTier::T2 {
            continue;
        }
        let Some(target) = pair.target.as_ref() else {
            block_pair_raw_view(&mut plan, pair, "pair-raw-view-target-missing");
            continue;
        };
        let Ok(argument) = sm.span_to_snippet(pair.span) else {
            block_pair_raw_view(&mut plan, pair, "pair-raw-view-source-unplaceable");
            continue;
        };
        let raw_expression = pair
            .source_node
            .and_then(|source_node| decision_of.get(&source_node).copied())
            .and_then(|source_decision| {
                let template =
                    super::raw_boundary::template_for(source_decision, target, None, false).ok()?;
                GlueSpec::raw_boundary_target(template, target, false, true).render(&argument)
            })
            .or_else(|| match (pair.source_shape, target.mutability) {
                ("addr-of-mut", super::raw_boundary::RawMutability::Mut) => {
                    Some(format!("core::ptr::from_mut({argument})"))
                }
                ("addr-of-mut", super::raw_boundary::RawMutability::Const) => {
                    Some(format!("core::ptr::from_ref(&*{argument})"))
                }
                ("addr-of", super::raw_boundary::RawMutability::Const) => {
                    Some(format!("core::ptr::from_ref({argument})"))
                }
                _ => None,
            });
        let Some(raw_expression) = raw_expression else {
            block_pair_raw_view(&mut plan, pair, "pair-raw-view-template-unavailable");
            continue;
        };
        let key = (
            pair.caller.local_def_index.as_u32(),
            pair.callee.local_def_index.as_u32(),
            pair.call_span.lo().0,
            pair.call_span.hi().0,
        );
        let call = pair_raw_calls
            .entry(key)
            .or_insert_with(|| PairRawViewCall {
                owner_class: SignatureClassId::of(pair.callee),
                caller: pair.caller,
                callee: pair.callee,
                call_span: pair.call_span,
                views: Vec::new(),
                reasons: Vec::new(),
                atom_ids: Vec::new(),
            });
        call.views.push(PairRawViewTemp {
            argument_index: pair.argument_index,
            raw_expression,
            target_type: target.rendered.clone(),
        });
        call.reasons.push(pair.reason.clone());
        call.atom_ids.push(pair.atom_id());
    }
    plan.pair_raw_calls = pair_raw_calls.into_values().collect();
    for call in &mut plan.pair_raw_calls {
        call.views.sort_by_key(|view| view.argument_index);
        call.reasons.sort();
        call.reasons.dedup();
        call.atom_ids.sort();
        call.atom_ids.dedup();
    }
    for site in raw_boundary.address_sites() {
        let Ok(argument) = sm.span_to_snippet(site.span) else {
            continue;
        };
        let spec = GlueSpec::raw_boundary_target(site.template, &site.target, false, true);
        let Some(replacement) = spec.render(&argument) else {
            continue;
        };
        let found = decision_of
            .get(&site.node)
            .copied()
            .map_or(Form::Raw, form_of);
        let atom_ids = plan
            .raw_boundary_atom_groups
            .get(&site.node)
            .map(|atoms| atoms.iter().map(|atom| atom.id.clone()).collect())
            .unwrap_or_default();
        plan.edits.push(SeamEdit {
            span: site.span,
            call_span: site.span,
            replacement,
            owner_class: SignatureClassId::of(site.node.0),
            bridge: BridgeSitePlan {
                caller: site.node.0,
                callee: BridgeCalleeId::Local(site.node.0),
                arm: "addr".to_owned(),
                position: format!(
                    "{}={}:hir{}@{}..{}:target={}:sink={}",
                    if site.op == "ptr-eq" {
                        if site.operand_index == 0 {
                            "lhs"
                        } else {
                            "rhs"
                        }
                    } else {
                        "operand"
                    },
                    site.op,
                    site.node.1.local_id.as_u32(),
                    site.span.lo().0,
                    site.span.hi().0,
                    site.target.rendered,
                    site.target_type,
                ),
                bridge_kind: site.bridge_kind.to_owned(),
                extent: receipt_extent(&spec),
                retention: BridgeRetentionTier::None,
                waiver_id: None,
            },
            owner_fn: site.owner.clone(),
            lifetime_plan_digest: None,
            caller_fn: site.owner.clone(),
            param_index: usize::MAX,
            source_shape: "raw-op-address-observation",
            family: SeamFamily::Safe,
            len_arm: None,
            spec,
            arg_span: site.span,
            expected: Form::Raw,
            found,
            root_identity: format!("address:{}:{}", site.op, site.span.lo().0),
            blind: false,
            overlap: None,
            atom_ids,
        });
    }

    // Return seams are owned by the returning function's signature class. The
    // original expression is raw, so even a converted local receives the same
    // explicit reborrow algebra as an inbound raw boundary. A typed origin
    // permit is mandatory and supplies the lifetime-plan receipt.
    let mut return_sites = facts.return_sites.clone();
    return_sites.sort_by_key(|site| {
        (
            site.owner.local_def_index.as_u32(),
            site.span.lo().0,
            site.span.hi().0,
        )
    });
    for site in return_sites {
        let Some(function_plan) = table.lifetime_plan.function(site.owner) else {
            continue;
        };
        if function_plan
            .lifetime_for(super::lifetime::FnSignatureSlot::RETURN)
            .is_none()
        {
            continue;
        }
        let signature = tcx
            .fn_sig(site.owner.to_def_id())
            .skip_binder()
            .skip_binder();
        let output = signature.output();
        let rustc_middle::ty::TyKind::RawPtr(_, output_mutability) = *output.kind() else {
            continue;
        };
        let expected_mutable = output_mutability == rustc_middle::ty::Mutability::Mut;
        let expected = Form::Ref {
            mutable: expected_mutable,
        };
        let Some(root) = site.root else {
            plan.blocked.push(BlockedSeam {
                caller: site.owner,
                callee: site.owner,
                index: usize::MAX,
                span: site.span,
                block: SeamBlock::ReturnLifetimeAbsent,
                expected: Some(expected),
                found: Some(Form::Raw),
                source_shape: "return-seam",
                candidate_template: "return-raw-to-ref".to_owned(),
                null_arm: "none".to_owned(),
                extent_arm: "none".to_owned(),
                root_identity: "-".to_owned(),
                blind: false,
                peers: Vec::new(),
                overlap: None,
            });
            continue;
        };
        let node = (site.owner, root);
        if lifetime_eligibility.return_permit(node).is_none() {
            plan.blocked.push(BlockedSeam {
                caller: site.owner,
                callee: site.owner,
                index: usize::MAX,
                span: site.span,
                block: SeamBlock::ReturnLifetimeAbsent,
                expected: Some(expected),
                found: Some(Form::Raw),
                source_shape: "return-seam",
                candidate_template: "return-raw-to-ref".to_owned(),
                null_arm: "none".to_owned(),
                extent_arm: "none".to_owned(),
                root_identity: root_label(&labels, site.owner, Some(root)),
                blind: false,
                peers: Vec::new(),
                overlap: None,
            });
            continue;
        }
        let final_mutable = decision_of.get(&node).is_some_and(|decision| {
            matches!(
                decision,
                Decision::Ref { mutable: true }
                    | Decision::InferredRef { mutable: true, .. }
                    | Decision::Slice { mutable: true, .. }
                    | Decision::Opt { mutable: true, .. }
            )
        });
        if expected_mutable && !final_mutable {
            plan.blocked.push(BlockedSeam {
                caller: site.owner,
                callee: site.owner,
                index: usize::MAX,
                span: site.span,
                block: SeamBlock::SharedToMut,
                expected: Some(expected),
                found: Some(Form::Raw),
                source_shape: "return-seam",
                candidate_template: "return-raw-to-ref".to_owned(),
                null_arm: "none".to_owned(),
                extent_arm: "none".to_owned(),
                root_identity: root_label(&labels, site.owner, Some(root)),
                blind: false,
                peers: Vec::new(),
                overlap: None,
            });
            continue;
        }
        let Ok(text) = sm.span_to_snippet(site.span) else {
            plan.blocked.push(BlockedSeam {
                caller: site.owner,
                callee: site.owner,
                index: usize::MAX,
                span: site.span,
                block: SeamBlock::UnnameableOperand,
                expected: Some(expected),
                found: Some(Form::Raw),
                source_shape: "return-seam",
                candidate_template: "return-raw-to-ref".to_owned(),
                null_arm: "none".to_owned(),
                extent_arm: "none".to_owned(),
                root_identity: root_label(&labels, site.owner, Some(root)),
                blind: false,
                peers: Vec::new(),
                overlap: None,
            });
            continue;
        };
        let spec = GlueSpec::core(GlueCore::Reborrow, expected_mutable);
        let Some(replacement) = spec.render(&text) else {
            continue;
        };
        let digest = function_plan.digest();
        plan.edits.push(SeamEdit {
            span: site.span,
            call_span: site.span,
            replacement,
            owner_class: SignatureClassId::of(site.owner),
            bridge: BridgeSitePlan {
                caller: site.owner,
                callee: BridgeCalleeId::Local(site.owner),
                arm: "glue".to_owned(),
                position: format!(
                    "return@{}..{}:target={}:lifetime_plan={digest}",
                    site.span.lo().0,
                    site.span.hi().0,
                    site.source_type.rendered,
                ),
                bridge_kind: "return-raw-to-ref".to_owned(),
                extent: BridgeExtentKind::None,
                retention: BridgeRetentionTier::T1,
                waiver_id: None,
            },
            owner_fn: tcx.def_path_str(site.owner.to_def_id()),
            lifetime_plan_digest: Some(digest),
            caller_fn: tcx.def_path_str(site.owner.to_def_id()),
            param_index: usize::MAX,
            source_shape: "return-seam",
            family: SeamFamily::Reborrow,
            len_arm: None,
            spec,
            arg_span: site.span,
            expected,
            found: Form::Raw,
            root_identity: root_label(&labels, site.owner, Some(root)),
            blind: false,
            overlap: None,
            atom_ids: Vec::new(),
        });
    }

    // Item E wave 2 — scalar-reference body adapters. The allowlist lives in
    // the HIR producer, so there is no second scope decision here.
    let mut body_sites = facts.body_adapters.clone();
    body_sites.sort_by_key(|site| {
        (
            site.owner.local_def_index.as_u32(),
            site.rhs_span.lo().0,
            site.rhs_span.hi().0,
        )
    });
    for site in body_sites {
        let Some(destination_decision) = decision_of.get(&(site.owner, site.destination)) else {
            continue;
        };
        let expected = form_of(destination_decision);
        if !matches!(expected, Form::Ref { .. }) {
            continue;
        }
        let owner_fn = tcx.def_path_str(site.owner.to_def_id());
        let destination = labels
            .get(&(site.owner, site.destination))
            .cloned()
            .unwrap_or_else(|| format!("{owner_fn}::<unknown-destination>"));
        if site.side_effecting {
            plan.body_blocked.push(BlockedBody {
                owner_class: SignatureClassId::of(site.owner),
                owner_fn,
                destination,
                span: site.rhs_span,
                context: site.context,
                block: BodyBlock::SideEffectingRhs,
                expected,
                found: Some(Form::Raw),
                source_shape: site.shape.key(),
                candidate_template: None,
                root_identity: root_label(&labels, site.owner, site.shape.place_root()),
                blind: true,
            });
            continue;
        }

        let (found, text_span, root, blind) = match site.shape {
            ArgShape::BareLocal(hir) => (
                decision_of
                    .get(&(site.owner, hir))
                    .map_or(Form::Raw, |decision| form_of(decision)),
                site.rhs_span,
                Some(hir),
                false,
            ),
            ArgShape::AddrOf {
                mutable,
                base,
                through_deref,
            } => {
                let blind = match (base, through_deref) {
                    (None, _) => true,
                    (Some(binding), true) => !decision_of
                        .get(&(site.owner, binding))
                        .is_some_and(|decision| !matches!(decision, Decision::Degraded(_))),
                    (Some(_), false) => false,
                };
                (Form::Ref { mutable }, site.rhs_span, base, blind)
            }
            ArgShape::AddrOfCast { mutable, inner } => (Form::Ref { mutable }, inner, None, true),
            ArgShape::CastOfLocal { binding, inner } => (
                decision_of
                    .get(&(site.owner, binding))
                    .map_or(Form::Raw, |decision| form_of(decision)),
                inner,
                Some(binding),
                false,
            ),
            ArgShape::NullLit => {
                plan.body_blocked.push(BlockedBody {
                    owner_class: SignatureClassId::of(site.owner),
                    owner_fn,
                    destination,
                    span: site.rhs_span,
                    context: site.context,
                    block: BodyBlock::NullRequiredRef,
                    expected,
                    found: Some(Form::Raw),
                    source_shape: site.shape.key(),
                    candidate_template: None,
                    root_identity: "-".to_owned(),
                    blind: false,
                });
                continue;
            }
            ArgShape::RawExpr { .. } | ArgShape::Cast { .. } | ArgShape::Other => {
                plan.body_blocked.push(BlockedBody {
                    owner_class: SignatureClassId::of(site.owner),
                    owner_fn,
                    destination,
                    span: site.rhs_span,
                    context: site.context,
                    block: BodyBlock::UnnameableRhs,
                    expected,
                    found: Some(Form::Raw),
                    source_shape: site.shape.key(),
                    candidate_template: None,
                    root_identity: root_label(&labels, site.owner, site.shape.place_root()),
                    blind: true,
                });
                continue;
            }
        };
        let text = sm.span_to_snippet(text_span).ok();
        let result = glue(expected, found, None);
        match result {
            Ok(None) => {}
            Ok(Some((spec, family))) => {
                let Some(text) = text.as_deref() else {
                    plan.body_blocked.push(BlockedBody {
                        owner_class: SignatureClassId::of(site.owner),
                        owner_fn,
                        destination,
                        span: site.rhs_span,
                        context: site.context,
                        block: BodyBlock::RenderRefused,
                        expected,
                        found: Some(found),
                        source_shape: site.shape.key(),
                        candidate_template: Some(spec.template_key()),
                        root_identity: root_label(&labels, site.owner, root),
                        blind,
                    });
                    continue;
                };
                let Some(replacement) = spec.render(text) else {
                    plan.body_blocked.push(BlockedBody {
                        owner_class: SignatureClassId::of(site.owner),
                        owner_fn,
                        destination,
                        span: site.rhs_span,
                        context: site.context,
                        block: BodyBlock::RenderRefused,
                        expected,
                        found: Some(found),
                        source_shape: site.shape.key(),
                        candidate_template: Some(spec.template_key()),
                        root_identity: root_label(&labels, site.owner, root),
                        blind,
                    });
                    continue;
                };
                plan.body_edits.push(BodyEdit {
                    span: site.rhs_span,
                    replacement,
                    owner_class: SignatureClassId::of(site.owner),
                    bridge: BridgeSitePlan {
                        caller: site.owner,
                        callee: BridgeCalleeId::Local(site.owner),
                        arm: "glue".to_owned(),
                        position: format!("body:{}", site.context.key()),
                        bridge_kind: spec.template_key().to_owned(),
                        extent: receipt_extent(&spec),
                        retention: BridgeRetentionTier::None,
                        waiver_id: None,
                    },
                    owner_fn,
                    destination,
                    context: site.context,
                    source_shape: site.shape.key(),
                    family,
                    spec,
                    arg_span: text_span,
                    expected,
                    found,
                    root_identity: root_label(&labels, site.owner, root),
                    blind,
                });
            }
            Err(SeamBlock::SharedToMut) => plan.body_blocked.push(BlockedBody {
                owner_class: SignatureClassId::of(site.owner),
                owner_fn,
                destination,
                span: site.rhs_span,
                context: site.context,
                block: BodyBlock::SharedToMut,
                expected,
                found: Some(found),
                source_shape: site.shape.key(),
                candidate_template: None,
                root_identity: root_label(&labels, site.owner, root),
                blind,
            }),
            Err(_) => plan.body_blocked.push(BlockedBody {
                owner_class: SignatureClassId::of(site.owner),
                owner_fn,
                destination,
                span: site.rhs_span,
                context: site.context,
                block: BodyBlock::UnnameableRhs,
                expected,
                found: Some(found),
                source_shape: site.shape.key(),
                candidate_template: None,
                root_identity: root_label(&labels, site.owner, root),
                blind,
            }),
        }
    }
    complete_interface_inventory(
        facts,
        table,
        c9_marks,
        lifetime_eligibility,
        &decision_of,
        &param_key,
        &mut plan,
    );
    plan
}

/// **Where an argument's REPLACEMENT TEXT is read from**, which is not always
/// the argument's own span.
///
/// The two cast shapes build from the cast's OPERAND while the replaced range
/// stays the whole argument, so the surviving subtree is nested one level inside
/// the node the span layer overwrites. Everything else reads its own span.
///
/// A free function rather than three lines inside the position loop, because
/// that loop needs a `TyCtxt`, a call site and a decision map to run at all —
/// and a mapping that only a corpus sweep can exercise is a mapping with no
/// witness. Mutation M28 collapsed it onto `arg.span` and the entire suite
/// stayed green.
///
/// `None` for the shapes that carry no nameable operand; those positions are
/// already blocked as `UnnameableOperand` before any text is read.
fn text_span_of(shape: ArgShape, arg_span: Span) -> Option<Span> {
    match shape {
        ArgShape::BareLocal(_)
        | ArgShape::AddrOf { .. }
        | ArgShape::RawExpr { .. }
        | ArgShape::NullLit => Some(arg_span),
        ArgShape::AddrOfCast { inner, .. } | ArgShape::CastOfLocal { inner, .. } => Some(inner),
        ArgShape::Cast { .. } | ArgShape::Other => None,
    }
}

/// **Ruling item 4a — is there a companion length in the callee's signature?**
///
/// Reads the RESOLVED signature, on the `ptr_params` precedent: a C2Rust alias
/// lowers to a path, so a syntactic test would miss exactly the parameters this
/// corpus is made of.
pub(crate) fn length_evidence(tcx: TyCtxt<'_>, callee: LocalDefId, index: usize) -> LenEvidence {
    let sig = tcx.fn_sig(callee).skip_binder().skip_binder();
    let inputs = sig.inputs();
    let is_int = |i: usize| {
        inputs.get(i).is_some_and(|ty| {
            matches!(
                ty.kind(),
                rustc_middle::ty::TyKind::Int(_) | rustc_middle::ty::TyKind::Uint(_)
            )
        })
    };
    if index + 1 < inputs.len() && is_int(index + 1) {
        LenEvidence::Following
    } else if index > 0 && is_int(index - 1) {
        LenEvidence::Preceding
    } else if (0..inputs.len()).any(is_int) {
        LenEvidence::Elsewhere
    } else {
        LenEvidence::None
    }
}
