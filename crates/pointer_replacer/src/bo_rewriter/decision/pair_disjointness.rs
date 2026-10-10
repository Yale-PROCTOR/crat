//! Pair-disjointness certificates for the PAIR consumer (wave-6p, R400-4).
//!
//! A callee parameter is held `pair-raw-view` when one call passes it beside
//! another pointer that MAY alias it and at least one of the two is written:
//! two live safe views that alias are UB in Rust, so the hold is a soundness
//! hold. It lifts exactly where DISJOINTNESS is proven. This module proves it
//! three ways, each a typed receipt on the pair, and never by waiver:
//!
//! * **(a) distinct roots.** At least one argument is a view into an object the
//!   CALLER itself creates — a fresh allocation local (`p = malloc(..)`, and
//!   nothing else is ever assigned to `p`) or a stack object (an array or
//!   struct local, or a scalar whose address is taken) — and the other argument
//!   is a view into a different such object or into storage that existed at
//!   function entry (a parameter that is never reassigned and never has its
//!   own address taken, or a place inside that parameter's pointee). A fresh
//!   object is disjoint from every object that already existed when it was
//!   created, and on a UB-free input (§28) no pointer that existed at entry
//!   dangles into storage the function allocates later.
//! * **(b) the strict-aliasing type rule** (R399-10, sharpened by R400-4). C11
//!   6.5p7: an object's stored value is accessed only through an lvalue of its
//!   effective type, the signed/unsigned counterpart, an aggregate or union
//!   containing one of those among its members, or a character type. So two
//!   pointers whose pointee types are distinct (modulo signedness), neither a
//!   character or `void` wildcard, neither a union, neither (transitively) a
//!   member type of the other, and not both members of one union type in the
//!   program, cannot address overlapping bytes on a UB-free input. The
//!   argument does not apply to the same syntactic place cast two ways, which
//!   is refused before the types are read.
//! * **(c) disjoint fields of one object.** `&mut s.a` beside `&s.b`: two
//!   places under one root that diverge at a `Field` projection are disjoint
//!   by layout. An `Index` projection is never a divergence point (two
//!   elements of one array may coincide), and a deref past the root is not
//!   followed.
//!
//! Everything else stays held with the reason
//! `pair-disjointness-unproved:<why>`, recorded in the ledger. The consumer is
//! the existing A5 site-proof lookup ([`super::a5_site_proof`]): a certificate
//! turns a non-clear verdict into `Clear` with the certificate as its reason,
//! so the ordinary delivered forms (`&mut T` / `&T`) are emitted through the
//! unchanged pair machinery. No `Decision` / `Form` / `DeclForm` is added.

use std::cell::RefCell;

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    Expr, ExprKind, HirId, LangItem, PatKind, QPath, StmtKind, UnOp,
    def::{DefKind, Res},
    def_id::{DefId, LocalDefId},
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{self, Ty, TyCtxt, TypeckResults};
use rustc_span::{Span, Symbol};

use crate::{analyses::borrow_ownership::mutability_facts::MutFacts, utils::rustc::RustProgram};

/// libc allocators whose result is a fresh block: disjoint from every object
/// live at the call. `realloc` returns either a fresh block or the caller's own
/// block with every other pointer to it dead — on a UB-free input the result
/// aliases nothing else live either way.
const LIBC_ALLOCATORS: &[&str] = &["malloc", "calloc", "realloc"];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CertificateKind {
    DistinctRoots,
    /// (a) again, but the freshness of one root rests on R409-1's allocator
    /// contract rather than on a resolved allocator: the program stores a
    /// caller-supplied function pointer into the allocator field, and the
    /// contract is what says a conforming allocator returns a fresh block.
    /// A separate kind so the receipt is countable wherever it is consumed.
    DistinctRootsUnderContract,
    TypeRule,
    DisjointFields,
    /// R479-4b: one side is the null literal. Null is `Option::None` (the
    /// standing null semantics), and `None` overlaps no object, so the pair is
    /// separated whatever the other operand is.
    NullOperand,
    /// (e) R462-1. The CALLEE's two parameters never alias, because at every
    /// in-program call the two arguments are disjoint — by (a)/(b)/(c) at that
    /// caller, or by (e) again on the caller's own parameters.
    ParameterPair,
    /// **R931-1** — (e) on the CALLER's side: the two arguments are distinct
    /// formals of the caller (or places inside their pointees), and every
    /// in-program call of the caller passes them disjoint objects. Its own key
    /// so the census counts R931-1's share apart from (e)'s.
    CallerParameterPair,
    /// **P11 (R936-1, the USER with the advisor).** The LAST arm: one side's
    /// provenance passes through a global or an integer, and the premise says
    /// such a pointer designates no object another argument designates. An
    /// assumption, never a proof: receipted per pair and counted
    /// (`<p>.raw-boundary-pair-premise.tsv`).
    GlobalOrIntegerPremise(super::global_or_integer::ProvenanceKind),
    /// **P5 (the pinned allocator contract, addendum 409; wave-5d 150g).** At
    /// the contract's deallocator, the block argument is what one of the
    /// contract's allocators returned: a fresh block, never the object another
    /// argument designates (`BrotliFree(m, p)`: `p` is not the manager). Rests
    /// on the stated premise P5 as `DistinctRootsUnderContract` does;
    /// receipted.
    AllocatorContractFree,
    /// R466-5, temporal rather than class-based: one side is the address of a
    /// stack local FIRST taken at this very call, and the callee never retains
    /// that position. No pointer VALUE computed before the call can name that
    /// object — on a UB-free input none exists yet (§28) — and the callee
    /// creates none that outlives the call, so the pair is disjoint however
    /// unknown the other side is.
    FreshStackAddress,
    /// (e) bottoming out at an EXPORTED entry under the user's waiver
    /// (R462-1): an embedder's two pointer arguments to a `#[no_mangle]` entry
    /// are assumed not to alias. An assumption, never a proof — receipted at
    /// every site that rests on it, as the other waivers are.
    ExportedEntryWaiver,
    /// R483-3(f): (e) extended to statics. One side is a `static` item, the
    /// other a parameter's pointee, and EVERY in-crate call site of that
    /// function passes, at that position, something whose root is known and is
    /// not this static. The payload is how many call sites were checked, so
    /// the evidence behind each certificate is countable in the ledger.
    StaticVsEntry(u32),
    /// R486-2, USER Decision C, waiver id `exported-entry-static-waiver
    /// (2026-09-21)`: the same rule where the function is an exported
    /// `#[no_mangle]` entry, so the callers the closed world CANNOT see are
    /// assumed not to pass the address of a program-internal static. An
    /// assumption, never a proof, and receipted as one. The in-crate callers
    /// are still read, and one of them passing the static still refuses.
    StaticVsEntryWaived(u32),
    /// R492-3 (wave-6k 038's rule, built here under R217-2(a)): the pair needs
    /// no disjointness at all, because both peer formals are MODEL-SHARED
    /// READS — `*const` in the input, nothing written through them, and no
    /// mutable reborrow anywhere in the callee. `&T` beside `&T` is the one
    /// aliasing question Rust answers for us, so two shared borrows of one
    /// place are legal and there is nothing to prove.
    ReadReadShared,
    /// R624-1 rule (f): one side is a direct read of an admitted field (not
    /// offset-admitted) that was stored on every path since the calling
    /// function's entry, so its block was allocated after that entry; the
    /// other side's object existed AT that entry. An allocator never returns
    /// storage overlapping a live object, so the two are distinct allocations
    /// whatever their types — no P3 is needed.
    AllocationIdentity,
    /// R645-10: the same, where the block came from an allocator admitted
    /// under R409-1's CONTRACT rather than a resolved allocator call — the
    /// contract is what says it returns storage overlapping no live object. A
    /// separate kind so the census counts the sites that rest on it.
    AllocationIdentityUnderContract,
}

impl CertificateKind {
    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::DistinctRoots => "pair-disjoint:distinct-roots",
            Self::DistinctRootsUnderContract => "pair-disjoint:distinct-roots:allocator-contract",
            Self::TypeRule => "pair-disjoint:type-rule",
            Self::DisjointFields => "pair-disjoint:disjoint-fields",
            Self::NullOperand => "pair-disjoint:null-operand",
            Self::FreshStackAddress => "pair-disjoint:fresh-stack-address",
            Self::ParameterPair => "pair-disjoint:parameter-pair",
            Self::CallerParameterPair => "pair-disjoint:caller-parameter-pair",
            Self::AllocatorContractFree => "pair-disjoint:allocator-contract-free",
            Self::GlobalOrIntegerPremise(kind) => match kind {
                super::global_or_integer::ProvenanceKind::GlobalValue => {
                    "pair-disjoint:premise=global-or-integer-provenance:global-value"
                }
                super::global_or_integer::ProvenanceKind::GlobalStorage => {
                    "pair-disjoint:premise=global-or-integer-provenance:global-storage"
                }
                super::global_or_integer::ProvenanceKind::Integer => {
                    "pair-disjoint:premise=global-or-integer-provenance:integer"
                }
            },
            Self::ExportedEntryWaiver => "pair-disjoint:exported-entry-waiver",
            Self::StaticVsEntry(_) => "pair-disjoint:static-vs-entry",
            // R672-4: the waiver is in the census key, so its sites are counted
            // there and not only in the lane's ledger.
            Self::StaticVsEntryWaived(_) => {
                "pair-disjoint:static-vs-entry:exported-entry-static-waiver"
            }
            Self::ReadReadShared => "pair-disjoint:read-read-shared",
            Self::AllocationIdentity => "pair-disjoint:allocation-identity",
            Self::AllocationIdentityUnderContract => {
                "pair-disjoint:allocation-identity:allocator-contract"
            }
        }
    }

    /// The receipt with its evidence count. `key()` stays a fixed vocabulary so
    /// the census can count it; this is what the lane's ledger records.
    pub(crate) fn receipt(self) -> String {
        match self {
            Self::StaticVsEntry(callers) => format!("{}:callers={callers}", self.key()),
            Self::StaticVsEntryWaived(callers) => format!(
                "{}:callers={callers}:{}",
                Self::StaticVsEntry(callers).key(),
                EXPORTED_ENTRY_STATIC_WAIVER
            ),
            _ => self.key().to_owned(),
        }
    }
}

pub(crate) const CERTIFICATE_FAMILY: &str = "pair-disjointness-certificate";

/// P11's family: the premise, not the roots, clears the pair.
pub(crate) const PREMISE_FAMILY: &str =
    "pair-disjointness-certificate:premise=global-or-integer-provenance";

/// R619-4: the certificate family with the root class of each side, in
/// argument-index order — `entry` (a pointer parameter of the calling function
/// or a place inside its pointee), `internal` (storage the program made: a
/// fresh block, a stack object, a static, an admitted field's block) or
/// `other` (no known root). Every certificate receipt carries one, so a
/// `type-rule` certificate reads as entry / entry (counted under W4, R462-1),
/// entry / internal or internal / internal.
const CERTIFICATE_FAMILY_BY_ROOTS: [[&str; 3]; 3] = [
    [
        "pair-disjointness-certificate:roots=entry/entry",
        "pair-disjointness-certificate:roots=entry/internal",
        "pair-disjointness-certificate:roots=entry/other",
    ],
    [
        "pair-disjointness-certificate:roots=internal/entry",
        "pair-disjointness-certificate:roots=internal/internal",
        "pair-disjointness-certificate:roots=internal/other",
    ],
    [
        "pair-disjointness-certificate:roots=other/entry",
        "pair-disjointness-certificate:roots=other/internal",
        "pair-disjointness-certificate:roots=other/other",
    ],
];

/// R619-4: a side's row in [`CERTIFICATE_FAMILY_BY_ROOTS`].
fn root_side(class: RootClass) -> usize {
    match class {
        RootClass::EntryStorage(_) => 0,
        RootClass::FreshAlloc(..)
        | RootClass::StackObject(_)
        | RootClass::Static(_)
        | RootClass::FreshField { .. }
        | RootClass::AllocatedHere(..) => 1,
        RootClass::Unknown => 2,
    }
}

/// R486-2 (USER Decision C, 2026-09-21). Named so every site that rests on the
/// assumption can be counted and, if it is ever withdrawn, found.
pub(crate) const EXPORTED_ENTRY_STATIC_WAIVER: &str = "exported-entry-static-waiver";

/// Why a pair stayed unproved. One fixed vocabulary, so the census can count.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Unproved {
    SiteUnresolved,
    SamePlace,
    WildcardPointee,
    SameType,
    UnionPointee,
    MemberType,
    UnionSibling,
    TypeUnresolved,
    RootsUnknown,
    /// Both formals carry a non-defaulted immutable fact: a READ/READ pair,
    /// which is wave-6k's shared-read consumer's (charter (d)); this lane
    /// leaves it untouched so that consumer's receipts stay identical.
    ReadReadPeers,
    /// R619-4: the type rule would certify the pair, but one side is `entry`
    /// storage and the other program-internal, and no later rule separated
    /// them.
    EntryBesideInternal,
    /// R939-1 (the seat): the P11 premise is not asked for a pair the caller's
    /// own text relates (a copy flow or a store into the global); counted.
    PremiseShownRelation,
}

impl Unproved {
    #[allow(
        dead_code,
        reason = "the unproved vocabulary is rendered by `ledger_tsv` and the witnesses"
    )]
    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::SiteUnresolved => "pair-disjointness-unproved:site-unresolved",
            Self::SamePlace => "pair-disjointness-unproved:same-place",
            Self::WildcardPointee => "pair-disjointness-unproved:wildcard-pointee",
            Self::SameType => "pair-disjointness-unproved:same-type",
            Self::UnionPointee => "pair-disjointness-unproved:union-pointee",
            Self::MemberType => "pair-disjointness-unproved:member-type",
            Self::UnionSibling => "pair-disjointness-unproved:union-sibling",
            Self::TypeUnresolved => "pair-disjointness-unproved:type-unresolved",
            Self::RootsUnknown => "pair-disjointness-unproved:roots-unknown",
            Self::ReadReadPeers => "pair-disjointness-unproved:read-read-peers",
            Self::EntryBesideInternal => "pair-disjointness-unproved:entry-beside-internal",
            Self::PremiseShownRelation => {
                "pair-disjointness-unproved:premise-refused-shown-relation"
            }
        }
    }
}

/// Where the freshness of an allocation comes from: a resolved allocator, or
/// R409-1's allocator contract (the program stores a caller-supplied function
/// pointer into the allocator field, so the closed world cannot name the
/// callee and the CONTRACT is what says a conforming allocator returns a fresh
/// block). Every certificate that rests on the second carries a receipt.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Freshness {
    Proven,
    Contract,
}

impl Freshness {
    /// The weaker of the two: a chain is contract-backed as soon as one link
    /// is.
    fn join(self, other: Self) -> Self {
        if self == Self::Contract || other == Self::Contract {
            Self::Contract
        } else {
            Self::Proven
        }
    }
}

/// The provenance class of one call argument, read in the caller's body.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RootClass {
    /// A pointer local whose every assignment is an allocator result (or
    /// null) and whose own address is never taken: it names one fresh block.
    FreshAlloc(HirId, Freshness),
    /// A view into a stack object of the caller — an array / struct / scalar
    /// `let` local, or a parameter's own slot (`&mut param`).
    StackObject(HirId),
    /// A parameter's VALUE, fixed at entry (never reassigned, address never
    /// taken), or a place inside its pointee: storage that existed at entry.
    EntryStorage(HirId),
    /// R482-4(4): a `static` item — a NAMED global object. Two different
    /// statics are two objects, and a static is neither this frame's stack nor
    /// a block an allocator has just returned. It is NOT separable from a
    /// parameter's pointee: a caller may pass the static itself.
    Static(DefId),
    /// R479-4a: the value read out of a pointer field whose EVERY store in the
    /// program is a directly called named allocator. `base` is the root binding
    /// of the place the field was read from, because the sound claim is
    /// *same-base*: `*base` was live when the allocator wrote the field, and an
    /// allocator never returns storage overlapping a live object. Against an
    /// unrelated root the claim fails (report 022 §2), so nothing else is
    /// certified from it.
    FreshField {
        adt: DefId,
        field: Symbol,
        base: HirId,
        /// `Contract` when any admitting store called an allocator that is
        /// itself contract-backed (brotli's `BrotliAllocate`, which allocates
        /// through `(*m).alloc_func`). The certificate says so by name.
        freshness: Freshness,
        /// R579-3: the field was admitted through a fresh LOCAL or an in-block
        /// OFFSET of another field ([`FreshFieldFact`]). Its block may be
        /// another admitted field's (`buffer_ = data_ + 2`), so it separates
        /// from another field only as R603-4 allows.
        same_base_only: bool,
        /// R603-4: some store into the field is an OFFSET (R579-3 (d)), so its
        /// block may be another admitted field's.
        via_offset: bool,
    },
    /// R641-9 (the fold): a pointer local — not a parameter, its own address
    /// never taken — whose every assignment is null, an allocator result, or a
    /// derivation of a binding that is fresh or already such a local (a least
    /// fixpoint). Every block it holds was allocated during this activation,
    /// after its entry. It names no ONE object: after `pairs = new_array` two
    /// locals are one block, so it separates only from storage no such block
    /// can be.
    AllocatedHere(HirId, Freshness),
    Unknown,
}

/// R479-4a / R579-3: what the whole-program store scan admitted a pointer field
/// with.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct FreshFieldFact {
    freshness: Freshness,
    same_base_only: bool,
    via_offset: bool,
}

impl RootClass {
    /// The contract receipt this root carries, if its freshness rests on one.
    fn freshness(self) -> Freshness {
        match self {
            Self::FreshAlloc(_, freshness)
            | Self::AllocatedHere(_, freshness)
            | Self::FreshField { freshness, .. } => freshness,
            _ => Freshness::Proven,
        }
    }

    fn is_fresh_object(self) -> bool {
        matches!(self, Self::FreshAlloc(..) | Self::StackObject(_))
    }

    fn object_id(self) -> Option<HirId> {
        match self {
            Self::FreshAlloc(id, _) | Self::StackObject(id) | Self::EntryStorage(id) => Some(id),
            Self::FreshField { .. } | Self::Static(_) | Self::AllocatedHere(..) | Self::Unknown => {
                None
            }
        }
    }
}

/// A place path: the root binding, whether the path passes through one deref
/// of that root, and the projections after it (Erratum 9d (i)'s place spine).
///
/// R550-2: `retyped` records that a cast changed the pointee type somewhere
/// on the way to the root — at the root dereference base, the argument itself,
/// an `as_mut_ptr()` receiver, or a folded view binding's initializer. The path
/// still names the PLACE, so the same-place refusal keeps reading it; it is
/// not a SPINE, so rule (c) does not.
#[derive(Clone, Debug, PartialEq, Eq)]
struct PlacePath {
    root: HirId,
    deref_root: bool,
    projections: Vec<Projection>,
    retyped: bool,
}

/// R550-2: one projection of a place spine. A field carries its PARENT — the
/// ADT it is a field of, and whether that ADT is a union — because two fields
/// are disjoint only as fields of one structure (Erratum 9d (ii)); a name alone
/// cannot say that. `parent` is `None` when the base is not an ADT (a tuple).
#[derive(Clone, Debug, PartialEq, Eq)]
enum Projection {
    Field {
        parent: Option<DefId>,
        union: bool,
        name: String,
    },
    Index,
}

impl PlacePath {
    /// The same syntactic place, however either side was cast: the same-place
    /// refusal must survive a cast that `retyped` records, and a cast that
    /// changes a field's PARENT (`(*(h as *mut U)).a` beside `(*h).a`) — that
    /// is still one place written two ways, so it compares field NAMES, as the
    /// refusal always did, never the parents rule (c) reads.
    fn same_place(&self, other: &PlacePath) -> bool {
        let syntactic = |projection: &Projection| match projection {
            Projection::Field { name, .. } => Some(name.clone()),
            Projection::Index => None,
        };
        self.root == other.root
            && self.deref_root == other.deref_root
            && self.projections.len() == other.projections.len()
            && self
                .projections
                .iter()
                .zip(&other.projections)
                .all(|(x, y)| syntactic(x) == syntactic(y))
    }
}

#[derive(Clone, Debug)]
struct ArgRecord {
    index: usize,
    span: Span,
    class: RootClass,
    place: Option<PlacePath>,
    /// R479-4b: this argument IS the null literal. A rule-side fact, kept
    /// apart from the probe column below, which no rule may read.
    is_null: bool,
    /// R478-5 probe column; no rule reads it.
    why: UnknownWhy,
    /// R478-5: whether this argument is pointer-typed at all. The probe
    /// enumerates EVERY argument pair, scalars included; the census only ever
    /// asks about pointer positions, so the column's table filters on this.
    /// Probe-only; no rule reads it.
    is_pointer: bool,
    /// R624-1 (f): this argument is a direct read `(b).F` of an admitted,
    /// not offset-admitted field, and a store into `F` of the same object runs
    /// on every path from the caller's entry to this call.
    stored_since_entry: bool,
    /// R628-7 (f′): this argument is a direct read `(*formal).F` of such a
    /// field through a stable formal of the caller: `(formal index, F)`.
    field_of_formal: Option<(usize, (DefId, Symbol))>,
    /// R628-7 (f′): the admitted fields stored into this argument's pointee
    /// place on every path from the caller's entry to this call.
    stored_fields: Vec<(DefId, Symbol)>,
    /// R628-7 (f′): the argument's place is rooted at a stable binding.
    place_stable: bool,
    /// P11 (R936-1): the argument's provenance passes through a global or an
    /// integer on every path the text shows.
    premise: Option<super::global_or_integer::Provenance>,
    /// R939-1: what the caller's text says this argument's value flows from.
    flow_roots: Vec<super::global_or_integer::FlowRoot>,
}

#[derive(Clone, Debug)]
struct SiteRecord {
    call_span: Span,
    args: Vec<ArgRecord>,
}

/// The normalized type class of a pointee, for the strict-aliasing rule.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum TypeClass {
    /// Character types and `void`: may alias anything.
    Wildcard,
    /// Integers by width, signedness folded (6.5p7's "corresponding signed or
    /// unsigned type"); `usize` / `isize` take the pointer width.
    Int(u64),
    Float(u64),
    Bool,
    /// Every pointer type is one class: conservative (two pointer objects are
    /// never held distinct by this rule).
    Pointer,
    FnPointer,
    Adt(DefId),
    Unresolved,
}

#[derive(Clone, Debug)]
struct PairTypeVerdict {
    /// `Ok(())` when the type rule certifies; `Err(why)` otherwise.
    verdict: Result<(), Unproved>,
}

/// A foreign-callee premise row: (caller, call span, left, right, kind).
type PremiseRow = (
    u32,
    Span,
    usize,
    usize,
    super::global_or_integer::ProvenanceKind,
);

#[derive(Clone, Debug)]
#[allow(
    dead_code,
    reason = "read by the certificate witnesses and by `ledger_tsv`; the census \
              artifact column is main's additive change, not this lane's"
)]
pub(crate) struct LedgerRow {
    pub(crate) caller: u32,
    pub(crate) callee: u32,
    pub(crate) left: usize,
    pub(crate) right: usize,
    pub(crate) outcome: Result<CertificateKind, Unproved>,
    /// The asked call's left argument (one per call): the P11 table's site.
    pub(crate) site: Span,
}

/// Every certificate the caller bodies and callee signatures support, derived
/// once per program. Lookups are by compiler identity (caller / callee
/// `LocalDefId` indices, argument spans at their call sites), the same key
/// shape the A5 site-proof index uses.
#[derive(Clone, Debug)]
pub(crate) struct PairDisjointnessIndex {
    sites: FxHashMap<(u32, u32), Vec<SiteRecord>>,
    /// `(callee, left, right)` with `left < right`, zero-based.
    type_rule: FxHashMap<(u32, usize, usize), PairTypeVerdict>,
    /// `(callee, index)` formals with a non-defaulted immutable fact.
    immutable_formals: FxHashSet<(u32, usize)>,
    /// R492-3: formals that are model-shared reads — the conjunction in
    /// `CertificateKind::ReadReadShared`. Keyed on the CALLEE alone, so the
    /// answer is per pair and identical at every call site.
    shared_reads: FxHashSet<(u32, usize)>,
    /// Each function's pointer-parameter bindings, in formal order: what lets
    /// (e) map an argument's entry root back to the caller's own formal.
    param_bindings: FxHashMap<u32, Vec<HirId>>,
    /// Functions the embedder can call: `#[no_mangle]` / `export_name`. Only
    /// these may bottom out on R462-1's waiver.
    exported: FxHashSet<u32>,
    /// R931-1 (USER; wave-5d 149): the local functions referenced other than
    /// as a direct callee (an address taken, a fn-pointer cast, a table
    /// entry). Their callers are not all recorded, so no pair of their formals
    /// is ever certified from the direct calls.
    address_taken: FxHashSet<u32>,
    /// P5 (wave-5d 150g): the allocator contracts' deallocators among the
    /// program's functions, by the block argument's index.
    contract_frees: FxHashMap<u32, usize>,
    /// R466-5: `(caller, callee, argument index)` where that argument is the
    /// address of a stack local taken exactly once in the caller's body, at a
    /// callee position wave-6r's walk proves never retained.
    fresh_stack: FxHashSet<(u32, u32, usize)>,
    /// (e)'s memo, keyed by `(callee, i, j)` with `i < j`.
    parameter_pairs: RefCell<FxHashMap<(u32, usize, usize), Option<PairSeparation>>>,
    ledger: RefCell<Vec<LedgerRow>>,
    /// R939-1: the foreign-callee pairs whose premise was refused for a shown
    /// relation (counted apart).
    premise_refused_foreign: RefCell<Vec<PremiseRow>>,
    /// P11 (R936-1): the foreign-callee pairs `certify_call_arguments` cleared
    /// by the premise, as (caller, left span, right span, kind).
    #[allow(clippy::type_complexity)]
    premise_foreign: RefCell<
        Vec<(
            u32,
            Span,
            usize,
            usize,
            super::global_or_integer::ProvenanceKind,
        )>,
    >,
    /// R544-3: every function's binding root classes, as the call sites read
    /// them, so a pair of bindings of ONE function can be certified without a
    /// call between them ([`Self::certify_bindings`]).
    binding_roots: FxHashMap<u32, FxHashMap<HirId, RootClass>>,
}

/// How (e) separated a parameter pair: by the rules alone, or resting on
/// R462-1's exported-entry waiver somewhere in the chain.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PairSeparation {
    Proven,
    Waived,
}

impl PairSeparation {
    fn join(self, other: Self) -> Self {
        if self == Self::Waived || other == Self::Waived {
            Self::Waived
        } else {
            Self::Proven
        }
    }
}

impl PairDisjointnessIndex {
    /// `indirect_calls`: the closed-world resolution of every MIR call site
    /// (the P-b fn-pointer web's inventory, attested only under the frozen
    /// benchmark graph); `None` admits no call through a function pointer.
    pub(crate) fn derive(
        program: &RustProgram<'_>,
        mut_facts: &MutFacts,
        indirect_calls: Option<&[super::lifetime::MirCallTargetSite]>,
    ) -> Self {
        let tcx = program.tcx;
        let local_functions: FxHashSet<LocalDefId> = program.functions.iter().copied().collect();
        let allocators = allocator_wrappers(tcx, &local_functions, indirect_calls);
        // R479-4a: needs the wrapper set, so it is derived after it.
        let fresh_fields = allocator_data_fields(tcx, &local_functions, &allocators);
        // R601-4 (G4): needs the admitted fields, so it is derived after them.
        let getters = field_getters(tcx, &local_functions, &allocators, &fresh_fields);
        // R628-7 (f′): so do the must-store summaries.
        let summaries = must_store_summaries(tcx, &local_functions, &fresh_fields);
        #[cfg(test)]
        if std::env::var_os("W6P_DUMP_FIELDS").is_some() {
            for (did, (position, (_, field))) in &getters {
                println!(
                    "W6P_GETTER\t{}\t{position}\t{field}",
                    tcx.def_path_str(*did)
                );
            }
            for ((adt, field), fact) in &fresh_fields {
                println!(
                    "W6P_FIELD\t{}\t{field}\t{:?}{}{}",
                    tcx.def_path_str(*adt),
                    fact.freshness,
                    if fact.same_base_only {
                        "\tsame-base-only"
                    } else {
                        ""
                    },
                    if fact.via_offset { "\tvia-offset" } else { "" }
                );
            }
            for (did, index) in &allocators.views {
                println!("W6P_VIEW\t{}\t{index}", tcx.def_path_str(*did));
            }
            for (did, freshness) in &allocators.wrappers {
                println!("W6P_WRAPPER\t{}\t{freshness:?}", tcx.def_path_str(*did));
            }
        }
        let unions = union_member_classes(tcx, program);
        // Member closures are shared across every pair: brotli's ~3k functions
        // ask about the same few hundred pointee types, and recomputing the
        // closure per pair cost the first census its 20-minute slot.
        let mut closures: FxHashMap<TypeClass, FxHashSet<TypeClass>> = FxHashMap::default();

        let mut sites: FxHashMap<(u32, u32), Vec<SiteRecord>> = FxHashMap::default();
        let mut binding_roots: FxHashMap<u32, FxHashMap<HirId, RootClass>> = FxHashMap::default();
        for &caller in &program.functions {
            let Some(body_id) = tcx.hir_node_by_def_id(caller).body_id() else {
                continue;
            };
            let body = tcx.hir_body(body_id);
            let typeck = tcx.typeck(caller);
            let (mut classes, why, prefixes) =
                classify_locals(tcx, typeck, body, &allocators, caller);
            carry_fresh_field_reads(tcx, typeck, body, &mut classes, &fresh_fields, &getters);
            binding_roots.insert(caller.local_def_index.as_u32(), classes.clone());
            let stable = stable_bindings(typeck, body);
            let mut collector = CallCollector {
                tcx,
                caller,
                typeck,
                locals: &local_functions,
                classes: &classes,
                fresh_fields: &fresh_fields,
                why: &why,
                prefixes: &prefixes,
                stable: &stable,
                summaries: &summaries,
                params: body
                    .params
                    .iter()
                    .map(|param| match param.pat.kind {
                        PatKind::Binding(_, hir_id, ..) => Some(hir_id),
                        _ => None,
                    })
                    .collect(),
                calls: Vec::new(),
            };
            collector.visit_body(body);
            for (callee, record) in collector.calls {
                sites
                    .entry((
                        caller.local_def_index.as_u32(),
                        callee.local_def_index.as_u32(),
                    ))
                    .or_default()
                    .push(record);
            }
        }

        let mut type_verdicts = FxHashMap::default();
        let mut immutable_formals = FxHashSet::default();
        let mut shared_reads = FxHashSet::default();
        let mutably_reborrowed = mutably_reborrowed_formals(tcx, &program.functions);
        for &callee in &program.functions {
            let inputs = tcx.fn_sig(callee).skip_binder().skip_binder().inputs();
            for index in 0..inputs.len() {
                let local = rustc_middle::mir::Local::from_usize(index + 1);
                if !mut_facts.is_defaulted(callee, local) && !mut_facts.is_mutable(callee, local) {
                    immutable_formals.insert((callee.local_def_index.as_u32(), index));
                    // R492-3, the other two conjuncts: `*const` in the INPUT,
                    // and no mutable reborrow of this formal in the body.
                    if matches!(
                        inputs[index].kind(),
                        ty::RawPtr(_, rustc_middle::mir::Mutability::Not)
                    ) && !mutably_reborrowed.contains(&(callee, index))
                    {
                        shared_reads.insert((callee.local_def_index.as_u32(), index));
                    }
                }
            }
            let pointees: Vec<Option<Ty<'_>>> = inputs
                .iter()
                .map(|ty| match ty.kind() {
                    ty::RawPtr(pointee, _) => Some(*pointee),
                    _ => None,
                })
                .collect();
            for left in 0..pointees.len() {
                for right in (left + 1)..pointees.len() {
                    let (Some(a), Some(b)) = (pointees[left], pointees[right]) else {
                        continue;
                    };
                    let verdict = type_rule(tcx, a, b, &unions, &mut closures);
                    type_verdicts.insert(
                        (callee.local_def_index.as_u32(), left, right),
                        PairTypeVerdict { verdict },
                    );
                }
            }
        }

        // (e) R462-1: each function's pointer-parameter bindings in formal
        // order, and the entries an embedder can call.
        let mut param_bindings: FxHashMap<u32, Vec<HirId>> = FxHashMap::default();
        let mut exported: FxHashSet<u32> = FxHashSet::default();
        for &function in &program.functions {
            let key = function.local_def_index.as_u32();
            if let Some(body_id) = tcx.hir_node_by_def_id(function).body_id() {
                let bindings = tcx
                    .hir_body(body_id)
                    .params
                    .iter()
                    .map(|param| match param.pat.kind {
                        PatKind::Binding(_, hir_id, ..) => Some(hir_id),
                        _ => None,
                    })
                    .collect::<Vec<_>>();
                param_bindings.insert(key, bindings.into_iter().flatten().collect());
            }
            let attrs = tcx.codegen_fn_attrs(function);
            if attrs.export_name.is_some()
                || attrs
                    .flags
                    .contains(rustc_middle::middle::codegen_fn_attrs::CodegenFnAttrFlags::NO_MANGLE)
            {
                exported.insert(key);
            }
        }
        let address_taken = address_taken_functions(tcx, &local_functions);
        // P5: the contracts' deallocators, by the block argument's index.
        let contract_frees: FxHashMap<u32, usize> = local_functions
            .iter()
            .filter_map(|function| {
                let name = tcx.item_name(function.to_def_id());
                super::allocator_contract::CONTRACTS
                    .iter()
                    .find(|contract| name.as_str() == contract.free)
                    .map(|contract| (function.local_def_index.as_u32(), contract.pointer_index))
            })
            .collect();

        // R466-5. The address-takings of every binding, then the sites where a
        // stack argument is the ONLY address-taking of its local and the
        // callee never retains that position.
        let mut address_takes: FxHashMap<(u32, HirId), usize> = FxHashMap::default();
        for &function in &program.functions {
            let Some(body_id) = tcx.hir_node_by_def_id(function).body_id() else {
                continue;
            };
            let mut counter = AddressTakes {
                typeck: tcx.typeck(function),
                counts: FxHashMap::default(),
            };
            counter.visit_body(tcx.hir_body(body_id));
            for (binding, count) in counter.counts {
                address_takes.insert((function.local_def_index.as_u32(), binding), count);
            }
        }
        let by_index: FxHashMap<u32, LocalDefId> = program
            .functions
            .iter()
            .map(|did| (did.local_def_index.as_u32(), *did))
            .collect();
        let mut retention: FxHashMap<(u32, usize), bool> = FxHashMap::default();
        let mut fresh_stack: FxHashSet<(u32, u32, usize)> = FxHashSet::default();
        for (&(caller, callee), records) in &sites {
            let Some(&callee_did) = by_index.get(&callee) else {
                continue;
            };
            for record in records {
                for arg in &record.args {
                    let RootClass::StackObject(binding) = arg.class else {
                        continue;
                    };
                    if address_takes.get(&(caller, binding)) != Some(&1) {
                        continue;
                    }
                    let free = *retention.entry((callee, arg.index)).or_insert_with(|| {
                        tcx.is_mir_available(callee_did)
                            && crate::bo_rewriter::wave6r_child_access::position_is_descendant_free(
                                tcx,
                                &program.functions,
                                callee_did,
                                arg.index,
                            )
                    });
                    if free {
                        fresh_stack.insert((caller, callee, arg.index));
                    }
                }
            }
        }

        Self {
            sites,
            fresh_stack,
            type_rule: type_verdicts,
            immutable_formals,
            shared_reads,
            param_bindings,
            exported,
            address_taken,
            contract_frees,
            parameter_pairs: RefCell::new(FxHashMap::default()),
            ledger: RefCell::new(Vec::new()),
            premise_foreign: RefCell::new(Vec::new()),
            premise_refused_foreign: RefCell::new(Vec::new()),
            binding_roots,
        }
    }

    /// **R544-3 — route (a) between two bindings of one function.** The
    /// certificate the degraded-partner hold asks for: `a` and `b` are the
    /// binding `HirId`s of two pointer subjects of `function`, classified as
    /// its call sites classify them. Only the root rules apply (fresh
    /// allocation / stack object against another object or entry storage, and
    /// statics), never the type rule: there is no call, so there is no pair of
    /// pointee types fixed at one site. `None` when either binding is unknown.
    /// **R924-1 (USER; wave-5d 148).** The root certificate for two ARGUMENTS of
    /// one call in `function` that no recorded site covers — a foreign callee's
    /// pair (`memcpy(ret, src, n)`), whose calls the collector does not record.
    /// Each argument is classified exactly as a recorded site classifies its
    /// own (`argument_provenance` over the function's binding roots), and the
    /// pair is certified by `certify_roots` alone: distinct roots (a fresh
    /// allocation, a stack object or storage that existed at entry, a static),
    /// never by a rule that reads the callee (the type rule, the parameter
    /// pair), which a foreign callee does not have.
    pub(crate) fn certify_call_arguments<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        function: LocalDefId,
        left: &'tcx Expr<'tcx>,
        right: &'tcx Expr<'tcx>,
        // The call and the two positions, for the P11 table's row.
        call: (Span, usize, usize),
    ) -> Option<CertificateKind> {
        let classes = self.binding_roots.get(&function.local_def_index.as_u32())?;
        let typeck = tcx.typeck(function);
        let (a, _) = argument_provenance(tcx, typeck, classes, left);
        let (b, _) = argument_provenance(tcx, typeck, classes, right);
        certify_roots(a, b).or_else(|| {
            // P11 (R936-1), the last arm.
            let (pl, pr) = (
                super::global_or_integer::provenance(tcx, function, left),
                super::global_or_integer::provenance(tcx, function, right),
            );
            let kind = super::global_or_integer::premise(pl, pr)?;
            // R939-1 (the seat): never for a pair the caller's own text relates.
            if super::global_or_integer::shown_related(
                &super::global_or_integer::flow_roots(tcx, function, left, pl),
                &super::global_or_integer::flow_roots(tcx, function, right, pr),
            ) {
                self.premise_refused_foreign.borrow_mut().push((
                    function.local_def_index.as_u32(),
                    call.0,
                    call.1.min(call.2),
                    call.1.max(call.2),
                    kind,
                ));
                return None;
            }
            self.premise_foreign.borrow_mut().push((
                function.local_def_index.as_u32(),
                call.0,
                call.1.min(call.2),
                call.1.max(call.2),
                kind,
            ));
            Some(CertificateKind::GlobalOrIntegerPremise(kind))
        })
    }

    pub(crate) fn certify_bindings(
        &self,
        function: LocalDefId,
        a: HirId,
        b: HirId,
    ) -> Option<CertificateKind> {
        let classes = self.binding_roots.get(&function.local_def_index.as_u32())?;
        certify_roots(*classes.get(&a)?, *classes.get(&b)?)
    }

    /// (e) R462-1. Do parameters `left` and `right` of `callee` ever alias?
    /// They do not when EVERY in-program call passes arguments the rules
    /// separate — by (a) roots or (c) fields at that caller, or, when both
    /// arguments are the caller's own parameters, by (e) on the caller. The
    /// chain bottoms out at an EXPORTED entry under the user's waiver: an
    /// embedder's two pointer arguments are assumed not to alias (R462-1),
    /// which is an assumption and is receipted as one. A non-exported callee
    /// with no in-program caller, an argument this read cannot map, two
    /// arguments that are the caller's SAME parameter, a same-place call, a
    /// cycle or eight levels of depth all refuse.
    /// R492-3: why (e) declined, for the decline table. Test-only; no rule
    /// reads it, and it is keyed on the pair so a memoised decline is counted
    /// once.
    #[cfg(test)]
    fn note_decline(callee: u32, left: usize, right: usize, cause: &str) {
        if std::env::var_os("W6P_DUMP_EDECLINE").is_some() {
            println!("W6P_EDECLINE\t{callee}\t{left}\t{right}\t{cause}");
        }
    }

    fn parameter_pair(
        &self,
        callee: u32,
        left: usize,
        right: usize,
        depth: usize,
        seen: &mut Vec<(u32, usize, usize)>,
    ) -> Option<PairSeparation> {
        let key = (callee, left.min(right), left.max(right));
        if let Some(memo) = self.parameter_pairs.borrow().get(&key) {
            return *memo;
        }
        if depth > 8 || seen.contains(&key) {
            #[cfg(test)]
            Self::note_decline(callee, left, right, "recursion-or-depth");
            return None;
        }
        // R931-1: a function reached indirectly has callers the records do not
        // show; nothing about its formals is certified from the direct calls.
        if self.address_taken.contains(&callee) {
            #[cfg(test)]
            Self::note_decline(callee, left, right, "address-taken");
            self.parameter_pairs.borrow_mut().insert(key, None);
            return None;
        }
        seen.push(key);
        let mut result = if self.exported.contains(&callee) {
            Some(PairSeparation::Waived)
        } else {
            Some(PairSeparation::Proven)
        };
        let mut callers = 0usize;
        for ((caller, target), records) in &self.sites {
            if *target != callee {
                continue;
            }
            for record in records {
                let find = |index: usize| record.args.iter().find(|arg| arg.index == index);
                let (Some(a), Some(b)) = (find(left), find(right)) else {
                    #[cfg(test)]
                    Self::note_decline(callee, left, right, "argument-not-recorded");
                    result = None;
                    break;
                };
                callers += 1;
                // R462-1 (2): an in-crate caller that hands the callee the
                // same place refuses the pair, waiver or not.
                if let (Some(pa), Some(pb)) = (&a.place, &b.place)
                    && pa.same_place(pb)
                {
                    #[cfg(test)]
                    Self::note_decline(callee, left, right, "a-caller-passes-one-place");
                    result = None;
                    break;
                }
                if certify_roots(a.class, b.class).is_some() {
                    continue;
                }
                if let (Some(pa), Some(pb)) = (&a.place, &b.place)
                    && disjoint_fields(pa, pb)
                {
                    continue;
                }
                let (Some(up_left), Some(up_right)) = (
                    self.formal_of(*caller, a.class),
                    self.formal_of(*caller, b.class),
                ) else {
                    // R493-3: which SIDE failed, not just what the classes
                    // were. Report 031's label printed the class of both sides
                    // whichever one `formal_of` refused, which is why its
                    // `entry-but-not-a-formal` count could not be read.
                    #[cfg(test)]
                    Self::note_decline(
                        callee,
                        left,
                        right,
                        &format!(
                            "root-is-not-a-caller-formal:{}:{}@caller={}",
                            describe_side(self.formal_of(*caller, a.class), a.class),
                            describe_side(self.formal_of(*caller, b.class), b.class),
                            caller
                        ),
                    );
                    result = None;
                    break;
                };
                if up_left == up_right {
                    #[cfg(test)]
                    Self::note_decline(
                        callee,
                        left,
                        right,
                        &format!(
                            "a-caller-passes-one-formal-twice@caller={caller} formal={up_left} \
                             places={:?}/{:?}",
                            a.place, b.place
                        ),
                    );
                    result = None;
                    break;
                }
                match self.parameter_pair(*caller, up_left, up_right, depth + 1, seen) {
                    Some(up) => result = result.map(|acc| acc.join(up)),
                    None => {
                        #[cfg(test)]
                        Self::note_decline(callee, left, right, "declined-further-up-the-chain");
                        result = None;
                    }
                }
            }
            if result.is_none() {
                break;
            }
        }
        if callers == 0 && !self.exported.contains(&callee) {
            #[cfg(test)]
            Self::note_decline(callee, left, right, "no-in-crate-caller-reaches-it");
            result = None;
        }
        seen.pop();
        self.parameter_pairs.borrow_mut().insert(key, result);
        result
    }

    /// Test-only reader for (e)'s verdict on a callee's formal pair.
    #[cfg(test)]
    pub(crate) fn parameter_pair_for_tests(
        &self,
        callee: LocalDefId,
        left: usize,
        right: usize,
    ) -> Option<&'static str> {
        self.parameter_pair(
            callee.local_def_index.as_u32(),
            left,
            right,
            0,
            &mut Vec::new(),
        )
        .map(|separation| match separation {
            PairSeparation::Proven => "proven",
            PairSeparation::Waived => "waived",
        })
    }

    /// The formal index of `class` when its root IS one of `function`'s own
    /// pointer parameters.
    fn formal_of(&self, function: u32, class: RootClass) -> Option<usize> {
        let id = class.object_id()?;
        if !matches!(class, RootClass::EntryStorage(_)) {
            return None;
        }
        self.param_bindings
            .get(&function)?
            .iter()
            .position(|binding| *binding == id)
    }

    /// R628-7 (f′): at every in-crate call of `function`, is field `key` of the
    /// object handed to formal `q` stored since the caller's entry, with the
    /// object handed to formal `p` existing at that entry — or, when both are
    /// the caller's own formals passed through, the same one level up? At an
    /// EXPORTED function the embedder's calls are unseen: R462-1's contract is
    /// the entry's, and it covers that external edge whatever the other side's
    /// root (R631-11), so the chain rests on the waiver there — its in-crate
    /// callers must still hold, as in (e).
    fn stored_before_call(
        &self,
        function: u32,
        q: usize,
        key: (DefId, Symbol),
        p: usize,
        depth: usize,
        seen: &mut Vec<(u32, usize, usize)>,
    ) -> Option<PairSeparation> {
        if depth > 8 || seen.contains(&(function, q, p)) {
            return None;
        }
        seen.push((function, q, p));
        // wave-5d 149g (the stand-in review's HIGH-2): as in (e) (R931-1), a
        // function reached indirectly has callers the records do not show.
        if self.address_taken.contains(&function) {
            return None;
        }
        let exported = self.exported.contains(&function);
        let mut separation = if exported {
            PairSeparation::Waived
        } else {
            PairSeparation::Proven
        };
        let mut callers = 0usize;
        let mut every = true;
        'sites: for ((caller, target), records) in &self.sites {
            if *target != function {
                continue;
            }
            for record in records {
                let find = |index: usize| record.args.iter().find(|arg| arg.index == index);
                let (Some(field), Some(other)) = (find(q), find(p)) else {
                    every = false;
                    break 'sites;
                };
                callers += 1;
                if field.stored_fields.contains(&key) && predates_or_is_not_a_block(other.class) {
                    continue;
                }
                // One level up: both arguments are the caller's own stable
                // formals, the field side passed as itself.
                let up_q = field
                    .place
                    .as_ref()
                    .filter(|place| {
                        field.place_stable && place.deref_root && place.projections.is_empty()
                    })
                    .and_then(|place| {
                        self.param_bindings
                            .get(caller)?
                            .iter()
                            .position(|binding| *binding == place.root)
                    });
                let (Some(up_q), Some(up_p)) = (up_q, self.formal_of(*caller, other.class)) else {
                    every = false;
                    break 'sites;
                };
                match (up_q != up_p)
                    .then(|| self.stored_before_call(*caller, up_q, key, up_p, depth + 1, seen))
                    .flatten()
                {
                    Some(up) => separation = separation.join(up),
                    None => {
                        every = false;
                        break 'sites;
                    }
                }
            }
        }
        seen.pop();
        (every && (callers > 0 || exported)).then_some(separation)
    }

    /// Certify the argument pair `(left, right)` of the call `caller → callee`
    /// whose arguments sit at `left_span` / `right_span`. Every outcome is
    /// recorded in the ledger.
    pub(crate) fn certify(
        &self,
        caller: u32,
        callee: u32,
        left: usize,
        right: usize,
        left_span: Span,
        right_span: Span,
    ) -> Result<CertificateKind, Unproved> {
        let outcome = self.certify_inner(caller, callee, left, right, left_span, right_span);
        self.ledger.borrow_mut().push(LedgerRow {
            caller,
            callee,
            left: left.min(right),
            right: left.max(right),
            outcome,
            site: if left <= right { left_span } else { right_span },
        });
        outcome
    }

    /// The recorded call `caller → callee` holding both argument spans, and its
    /// two argument records.
    fn site_args(
        &self,
        caller: u32,
        callee: u32,
        left: usize,
        right: usize,
        left_span: Span,
        right_span: Span,
    ) -> Option<(&SiteRecord, &ArgRecord, &ArgRecord)> {
        let left_span = left_span.source_callsite();
        let right_span = right_span.source_callsite();
        let site = self
            .sites
            .get(&(caller, callee))
            .into_iter()
            .flatten()
            .find(|site| {
                site.call_span.source_callsite().contains(left_span)
                    && site.call_span.source_callsite().contains(right_span)
            })?;
        let arg = |index: usize, span: Span| {
            site.args
                .iter()
                .find(|arg| arg.index == index && arg.span.source_callsite() == span)
        };
        Some((site, arg(left, left_span)?, arg(right, right_span)?))
    }

    /// R619-4: the family a certificate at this pair is receipted under — the
    /// root class of each side, lower argument index first. The bare family
    /// when the call is not resolved.
    pub(crate) fn certificate_family(
        &self,
        caller: u32,
        callee: u32,
        left: usize,
        right: usize,
        left_span: Span,
        right_span: Span,
    ) -> &'static str {
        let Some((_, a, b)) = self.site_args(caller, callee, left, right, left_span, right_span)
        else {
            return CERTIFICATE_FAMILY;
        };
        let (low, high) = if a.index <= b.index { (a, b) } else { (b, a) };
        CERTIFICATE_FAMILY_BY_ROOTS[root_side(low.class)][root_side(high.class)]
    }

    fn certify_inner(
        &self,
        caller: u32,
        callee: u32,
        left: usize,
        right: usize,
        left_span: Span,
        right_span: Span,
    ) -> Result<CertificateKind, Unproved> {
        let (site, a, b) = self
            .site_args(caller, callee, left, right, left_span, right_span)
            .ok_or(Unproved::SiteUnresolved)?;
        if self.immutable_formals.contains(&(callee, left))
            && self.immutable_formals.contains(&(callee, right))
        {
            // R492-3: the FACT is derived here (`is_shared_read_pair`).
            // `decision/shared_read_pairs.rs` owns the shared/shared case in the
            // CONSUMER role (R396-2) for every TWO-argument call — it rewrites
            // the addresses itself and pins that such a call's A5 overlap
            // verdict stays `Overlapping` — so there this index refuses the pair
            // to it on purpose (report 031 STOP 1).
            //
            // R593-4: in any OTHER call the consumer never takes the pair, and a
            // pair whose two positions both carry the fact — `*const` in the
            // input, nothing written through either, no mutable reborrow of
            // either — needs no disjointness: two shared borrows of one place
            // are what Rust permits. One position without the fact keeps the
            // refusal.
            if site.args.len() != 2
                && self.shared_reads.contains(&(callee, left))
                && self.shared_reads.contains(&(callee, right))
            {
                return Ok(CertificateKind::ReadReadShared);
            }
            return Err(Unproved::ReadReadPeers);
        }
        // The same syntactic place, however it is cast, is never disjoint from
        // itself; refused before any rule is consulted.
        if let (Some(pa), Some(pb)) = (&a.place, &b.place)
            && pa.same_place(pb)
        {
            return Err(Unproved::SamePlace);
        }
        // R479-4b, before every root rule: `None` overlaps no object, so a
        // null-literal operand separates the pair on its own.
        if a.is_null || b.is_null {
            return Ok(CertificateKind::NullOperand);
        }
        if let Some(kind) = certify_roots(a.class, b.class) {
            return Ok(kind);
        }
        let key = (callee, left.min(right), left.max(right));
        let type_verdict = self
            .type_rule
            .get(&key)
            .map_or(Err(Unproved::TypeUnresolved), |row| row.verdict);
        // R619-4 (Erratum 9a (i)): storage that entered through a pointer
        // parameter may be an exported entry's, which the effective-type
        // premise does not cover, and beside program-internal storage no waiver
        // covers the pair either. So the type rule yields there and the rules
        // below decide. Entry beside entry keeps it (its receipt's root
        // classes count it under W4, R462-1); internal beside internal is P3's.
        let yields = matches!((root_side(a.class), root_side(b.class)), (0, 1) | (1, 0));
        if type_verdict.is_ok() && !yields {
            return Ok(CertificateKind::TypeRule);
        }
        // R550-2: a divergence at two members of one union is remembered, so the
        // pair is held for the reason it has rather than whatever came before.
        let mut union_members = false;
        if let (Some(pa), Some(pb)) = (&a.place, &b.place) {
            match divergence(pa, pb) {
                Divergence::StructFields => return Ok(CertificateKind::DisjointFields),
                Divergence::UnionMembers => union_members = true,
                Divergence::NotAField => {}
            }
        }
        // R466-5, before (e): a fresh stack address at this call cannot be
        // aliased by a pointer value that existed before it.
        if self.fresh_stack.contains(&(caller, callee, a.index))
            || self.fresh_stack.contains(&(caller, callee, b.index))
        {
            return Ok(CertificateKind::FreshStackAddress);
        }
        // R483-3(f), before (e): a static beside a parameter's pointee, with
        // the closed world reading every caller of the function the parameter
        // belongs to.
        for (statik, entry) in [(a, b), (b, a)] {
            if let RootClass::Static(did) = statik.class
                && let Some(formal) = self.formal_of(caller, entry.class)
                && let Some((callers, waived)) =
                    self.static_vs_formal(caller, formal, did, 0, &mut Vec::new())
            {
                return Ok(if waived {
                    CertificateKind::StaticVsEntryWaived(callers)
                } else {
                    CertificateKind::StaticVsEntry(callers)
                });
            }
        }
        // R624-1 (f): allocation identity. The field's block was allocated
        // after this function's entry (every store into an admitted field is an
        // allocation, and one ran on every path here); the entry object existed
        // at that entry. An allocator never returns storage overlapping a live
        // object, so they are distinct allocations whatever their types.
        for (field, other) in [(a, b), (b, a)] {
            if field.stored_since_entry && predates_or_is_not_a_block(other.class) {
                return Ok(allocation_identity(field.class.freshness()));
            }
        }
        // R628-7 (f′), the same claim one call up: the field is read through
        // this function's formal `q`, the other side is its formal `p`'s entry
        // object, and at every in-crate call the field of the object handed to
        // `q` was stored since THAT caller's entry while the object handed to
        // `p` existed at it (or both are that caller's formals, one level up).
        for (field, other) in [(a, b), (b, a)] {
            if let Some((q, key)) = field.field_of_formal
                && let Some(p) = self.formal_of(caller, other.class)
                && q != p
            {
                match self.stored_before_call(caller, q, key, p, 0, &mut Vec::new()) {
                    Some(PairSeparation::Proven) => {
                        return Ok(allocation_identity(field.class.freshness()));
                    }
                    // R631-11: the chain reached an exported entry, W4's edge.
                    Some(PairSeparation::Waived) => {
                        return Ok(CertificateKind::ExportedEntryWaiver);
                    }
                    None => {}
                }
            }
        }
        // (e) R462-1, last: the callee's two parameters may be separable even
        // where this call site's arguments are not, if every in-program call
        // separates them (or the chain reaches an exported entry's waiver).
        match self.parameter_pair(callee, left, right, 0, &mut Vec::new()) {
            Some(PairSeparation::Proven) => return Ok(CertificateKind::ParameterPair),
            Some(PairSeparation::Waived) => return Ok(CertificateKind::ExportedEntryWaiver),
            None => {}
        }
        // **R931-1 (USER; wave-5d 149) — (e) on the CALLER's side.** Two of the
        // caller's own formals (or places inside their pointees) handed on are
        // disjoint at this call when every in-program call of the CALLER passes
        // them disjoint objects (the same greatest fixpoint as (e), up the
        // chain); the callee's other callers do not matter at this site.
        if let (Some(up_left), Some(up_right)) = (
            self.formal_of(caller, a.class),
            self.formal_of(caller, b.class),
        ) && up_left != up_right
        {
            match self.parameter_pair(caller, up_left, up_right, 0, &mut Vec::new()) {
                Some(PairSeparation::Proven) => return Ok(CertificateKind::CallerParameterPair),
                Some(PairSeparation::Waived) => return Ok(CertificateKind::ExportedEntryWaiver),
                None => {}
            }
        }
        // Report the type rule's reason when it was consulted, the roots
        // otherwise: whichever is the most specific thing the input lacked.
        if union_members {
            return Err(Unproved::UnionSibling);
        }
        // P5 (the pinned allocator contract): at the contract's deallocator the
        // block is a fresh allocation, never the other argument's object.
        if let Some(&block) = self.contract_frees.get(&callee)
            && (left == block) != (right == block)
        {
            return Ok(CertificateKind::AllocatorContractFree);
        }
        // P11 (R936-1), the LAST arm: every structural certificate failed.
        if let Some(kind) = super::global_or_integer::premise(a.premise, b.premise) {
            // R939-1 (the seat): never for a pair the caller's own text relates.
            if super::global_or_integer::shown_related(&a.flow_roots, &b.flow_roots) {
                return Err(Unproved::PremiseShownRelation);
            }
            return Ok(CertificateKind::GlobalOrIntegerPremise(kind));
        }
        Err(match type_verdict {
            Err(Unproved::TypeUnresolved) => Unproved::RootsUnknown,
            Err(why) => why,
            // Only a yielded type rule reaches here accepted.
            Ok(()) => Unproved::EntryBesideInternal,
        })
    }

    /// Certify a pair at the FIRST recorded call `caller → callee`, using the
    /// recorded argument spans. Witness surface for refusals the analysis frame
    /// otherwise reaches first (a place passed twice is already decided raw
    /// before any pair is consulted).
    #[cfg(test)]
    pub(crate) fn certify_recorded(
        &self,
        caller: LocalDefId,
        callee: LocalDefId,
        left: usize,
        right: usize,
    ) -> Result<CertificateKind, Unproved> {
        let caller = caller.local_def_index.as_u32();
        let callee = callee.local_def_index.as_u32();
        let site = self
            .sites
            .get(&(caller, callee))
            .and_then(|sites| sites.first())
            .ok_or(Unproved::SiteUnresolved)?;
        let span = |index: usize| {
            site.args
                .iter()
                .find(|arg| arg.index == index)
                .map(|arg| arg.span)
                .ok_or(Unproved::SiteUnresolved)
        };
        let (left_span, right_span) = (span(left)?, span(right)?);
        self.certify(caller, callee, left, right, left_span, right_span)
    }

    /// Test surface (wave-5d 150d): certify the pair at EVERY recorded call
    /// `caller → callee` (by item name), as a rule asking at each would.
    #[cfg(test)]
    pub(crate) fn certify_recorded_all(
        &self,
        tcx: TyCtxt<'_>,
        caller: &str,
        callee: &str,
        left: usize,
        right: usize,
    ) -> Vec<Result<CertificateKind, Unproved>> {
        let named = |index: u32, name: &str| {
            tcx.item_name(
                LocalDefId {
                    local_def_index: rustc_hir::def_id::DefIndex::from_u32(index),
                }
                .to_def_id(),
            )
            .as_str()
                == name
        };
        let mut out = Vec::new();
        for (&(c, e), sites) in &self.sites {
            if !named(c, caller) || !named(e, callee) {
                continue;
            }
            for site in sites {
                let span = |index: usize| {
                    site.args
                        .iter()
                        .find(|arg| arg.index == index)
                        .map(|arg| arg.span)
                };
                if let (Some(l), Some(r)) = (span(left), span(right)) {
                    out.push(self.certify(c, e, left, right, l, r));
                }
            }
        }
        out
    }

    /// R619-4: [`Self::certificate_family`] at the FIRST recorded call, for the
    /// witnesses.
    #[cfg(test)]
    pub(crate) fn certificate_family_recorded(
        &self,
        caller: LocalDefId,
        callee: LocalDefId,
        left: usize,
        right: usize,
    ) -> &'static str {
        let caller = caller.local_def_index.as_u32();
        let callee = callee.local_def_index.as_u32();
        let Some(site) = self
            .sites
            .get(&(caller, callee))
            .and_then(|sites| sites.first())
        else {
            return CERTIFICATE_FAMILY;
        };
        let span = |index: usize| {
            site.args
                .iter()
                .find(|arg| arg.index == index)
                .map(|arg| arg.span)
        };
        match (span(left), span(right)) {
            (Some(left_span), Some(right_span)) => {
                self.certificate_family(caller, callee, left, right, left_span, right_span)
            }
            _ => CERTIFICATE_FAMILY,
        }
    }

    #[allow(
        dead_code,
        reason = "witness surface: every certify() outcome, for the RED-first tests \
                  and the census ledger column main may add"
    )]
    /// R483-3(f). Can the pointee of `function`'s formal `formal` be the static
    /// `statik`? The closed world answers by reading every in-crate call site:
    /// each must pass something whose root is known and is not that static, or
    /// its own formal, which recurses. Returns how many sites were checked.
    ///
    /// Refused for an EXPORTED function — an embedder is outside the closed
    /// world, and R462-1's waiver is about two of an entry's own parameters,
    /// not about a program-internal static's address — and for a function no
    /// in-crate caller reaches, where there is no evidence at all.
    fn static_vs_formal(
        &self,
        function: u32,
        formal: usize,
        statik: DefId,
        depth: usize,
        seen: &mut Vec<(u32, usize)>,
    ) -> Option<(u32, bool)> {
        if depth > 8 || seen.contains(&(function, formal)) {
            return None;
        }
        seen.push((function, formal));
        // wave-5d 149g (the stand-in review's HIGH-2): as in (e) (R931-1), a
        // function reached indirectly has callers the records do not show.
        if self.address_taken.contains(&function) {
            return None;
        }
        // R486-2: an exported entry's unseen callers are assumed not to pass
        // the static. Its IN-CRATE callers are still read below.
        let mut waived = self.exported.contains(&function);
        let mut callers = 0u32;
        let mut ok = true;
        'sites: for ((caller, target), records) in &self.sites {
            if *target != function {
                continue;
            }
            for record in records {
                let Some(arg) = record.args.iter().find(|arg| arg.index == formal) else {
                    ok = false;
                    break 'sites;
                };
                callers += 1;
                match arg.class {
                    RootClass::Static(other) if other != statik => {}
                    RootClass::StackObject(_)
                    | RootClass::FreshAlloc(..)
                    | RootClass::FreshField { .. }
                    | RootClass::AllocatedHere(..) => {}
                    RootClass::EntryStorage(_) => {
                        let Some(up) = self.formal_of(*caller, arg.class) else {
                            ok = false;
                            break 'sites;
                        };
                        match self.static_vs_formal(*caller, up, statik, depth + 1, seen) {
                            Some((up_callers, up_waived)) => {
                                callers += up_callers;
                                waived |= up_waived;
                            }
                            None => {
                                ok = false;
                                break 'sites;
                            }
                        }
                    }
                    RootClass::Static(_) | RootClass::Unknown => {
                        ok = false;
                        break 'sites;
                    }
                }
            }
        }
        seen.pop();
        // Without the waiver a function no in-crate caller reaches is no
        // evidence at all; with it, the exported entry IS the evidence.
        (ok && (callers > 0 || waived)).then_some((callers, waived))
    }

    /// R492-3: are both peer formals model-shared reads — `*const` in the
    /// input, nothing written through them, and no mutable reborrow anywhere in
    /// the callee? The fact only; `certify_inner` deliberately does not turn it
    /// into a verdict, because the shared/shared case belongs to
    /// `shared_read_pairs`'s consumer role (R396-2).
    pub(crate) fn is_shared_read_pair(
        &self,
        callee: LocalDefId,
        left: usize,
        right: usize,
    ) -> bool {
        let callee = callee.local_def_index.as_u32();
        self.shared_reads.contains(&(callee, left)) && self.shared_reads.contains(&(callee, right))
    }

    pub(crate) fn ledger(&self) -> Vec<LedgerRow> {
        self.ledger.borrow().clone()
    }

    /// **P11 (R936-1) — the receipt table.** Every pair a rule ASKED the
    /// certificates about (the ledger) and the premise arm cleared, once per
    /// pair, plus the foreign-callee pairs `certify_call_arguments` cleared by
    /// it (the round-3 review's M3): `caller callee site left right kind`. The
    /// census writes it as `<p>.raw-boundary-pair-premise.tsv`; its rows are
    /// the program's P11 count. Read it after the rules have run. The `site`
    /// column is the asked pair's lower argument on an in-program row, and the
    /// call itself on a `<foreign>` row (round-5 LOW-2).
    pub(crate) fn premise_receipts_tsv(&self, tcx: TyCtxt<'_>) -> String {
        let name = |index: u32| {
            tcx.def_path_str(
                LocalDefId {
                    local_def_index: rustc_hir::def_id::DefIndex::from_u32(index),
                }
                .to_def_id(),
            )
        };
        let source_map = tcx.sess.source_map();
        let mut rows = std::collections::BTreeSet::new();
        for row in self.ledger.borrow().iter() {
            let kind = match row.outcome {
                Ok(CertificateKind::GlobalOrIntegerPremise(kind)) => kind.key(),
                // R939-1: a refusal for a shown relation, its own kind.
                Err(Unproved::PremiseShownRelation) => "refused-shown-relation",
                _ => continue,
            };
            // The asked call's own argument span (round-4 MED-3), at its macro
            // call site (rules pass different spans for one argument: round-5
            // LOW-1).
            let site = source_map.span_to_diagnostic_string(row.site.source_callsite());
            rows.insert(format!(
                "{}\t{}\t{}\t{}\t{}\t{}\n",
                name(row.caller),
                name(row.callee),
                site,
                row.left.min(row.right),
                row.left.max(row.right),
                kind,
            ));
        }
        for (caller, call, left, right, _) in self.premise_refused_foreign.borrow().iter() {
            rows.insert(format!(
                "{}\t<foreign>\t{}\t{}\t{}\trefused-shown-relation\n",
                name(*caller),
                source_map.span_to_diagnostic_string(call.source_callsite()),
                left,
                right,
            ));
        }
        for (caller, call, left, right, kind) in self.premise_foreign.borrow().iter() {
            rows.insert(format!(
                "{}\t<foreign>\t{}\t{}\t{}\t{}\n",
                name(*caller),
                source_map.span_to_diagnostic_string(call.source_callsite()),
                left,
                right,
                kind.key(),
            ));
        }
        let mut out = String::from("caller\tcallee\tsite\tleft\tright\tkind\n");
        out.extend(rows);
        out
    }

    #[allow(
        dead_code,
        reason = "witness surface: every certify() outcome, for the RED-first tests \
                  and the census ledger column main may add"
    )]
    pub(crate) fn ledger_tsv(&self, tcx: TyCtxt<'_>, program: &RustProgram<'_>) -> String {
        let names: FxHashMap<u32, LocalDefId> = program
            .functions
            .iter()
            .map(|did| (did.local_def_index.as_u32(), *did))
            .collect();
        let name = |index: u32| {
            names.get(&index).map_or_else(
                || format!("#{index}"),
                |did| tcx.def_path_str(did.to_def_id()),
            )
        };
        let mut out = String::from("caller\tcallee\tleft\tright\toutcome\n");
        for row in self.ledger.borrow().iter() {
            let outcome = match row.outcome {
                Ok(kind) => kind.key(),
                Err(why) => why.key(),
            };
            out.push_str(&format!(
                "{}\t{}\t{}\t{}\t{outcome}\n",
                name(row.caller),
                name(row.callee),
                row.left,
                row.right,
            ));
        }
        out
    }
}

/// R624-1 / R628-7 (f): the other side of an allocation-identity pair. An
/// entry object existed at the caller's entry, before the field's block was
/// allocated; a stack object or a static is no block an allocator ever returns.
/// Either way the two are distinct allocations. A fresh local is not: the field
/// may have been admitted through that very local (R579-3 (c)).
/// R645-10: allocation identity, receipted by where the block's freshness came
/// from.
fn allocation_identity(freshness: Freshness) -> CertificateKind {
    match freshness {
        Freshness::Proven => CertificateKind::AllocationIdentity,
        Freshness::Contract => CertificateKind::AllocationIdentityUnderContract,
    }
}

fn predates_or_is_not_a_block(class: RootClass) -> bool {
    matches!(
        class,
        RootClass::EntryStorage(_) | RootClass::StackObject(_) | RootClass::Static(_)
    )
}

/// (a): one side a fresh object of the caller, the other a distinct fresh
/// object or storage that existed at entry.
/// R931-1: the local functions any body names other than as the callee of a
/// direct call: an address taken, a fn-pointer cast, a static table's entry.
/// wave-5d 149g (the stand-in review's MED-2): also any function named inside
/// a closure (the call records do not visit closure bodies), and any function
/// an `extern` block redeclares (calls through the redeclaration resolve to
/// the foreign item, so the records do not show them).
fn address_taken_functions(
    tcx: TyCtxt<'_>,
    local_functions: &FxHashSet<LocalDefId>,
) -> FxHashSet<u32> {
    struct Find<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        local_functions: &'a FxHashSet<LocalDefId>,
        found: FxHashSet<u32>,
        in_closure: bool,
    }
    impl<'tcx> Visitor<'tcx> for Find<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            if let ExprKind::Path(QPath::Resolved(_, path)) = &expr.kind
                && let Res::Def(DefKind::Fn, did) = path.res
                && let Some(local) = did.as_local()
                && self.local_functions.contains(&local)
            {
                let called = matches!(
                    self.tcx.parent_hir_node(expr.hir_id),
                    rustc_hir::Node::Expr(Expr { kind: ExprKind::Call(callee, _), .. })
                        if callee.hir_id == expr.hir_id
                );
                if !called || self.in_closure {
                    self.found.insert(local.local_def_index.as_u32());
                }
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let mut find = Find {
        tcx,
        local_functions,
        found: FxHashSet::default(),
        in_closure: false,
    };
    for owner in tcx.hir_body_owners() {
        find.in_closure = tcx.is_closure_like(owner.to_def_id());
        find.visit_body(tcx.hir_body_owned_by(owner));
    }
    for function in local_functions {
        if super::outside_byte_view::declared_extern(tcx, *function) {
            find.found.insert(function.local_def_index.as_u32());
        }
    }
    find.found
}

fn certify_roots(a: RootClass, b: RootClass) -> Option<CertificateKind> {
    // R479-4a, same-base only. `(*base).f` holds a block the allocator returned
    // while `*base` was live, so it cannot overlap `*base` or any place inside
    // it. Two DIFFERENT admitted fields are two different allocations. The same
    // field on both sides is the same block, and an unrelated root is refused:
    // a pointer taken out of the field after the allocation is that same block.
    // A stack object or a static is the exception (R631-11): no allocator
    // returns either.
    match (a, b) {
        (
            RootClass::FreshField {
                adt,
                field,
                base,
                freshness,
                same_base_only,
                via_offset,
            },
            other,
        )
        | (
            other,
            RootClass::FreshField {
                adt,
                field,
                base,
                freshness,
                same_base_only,
                via_offset,
            },
        ) => {
            let kind = |freshness: Freshness| match freshness {
                Freshness::Proven => CertificateKind::DistinctRoots,
                Freshness::Contract => CertificateKind::DistinctRootsUnderContract,
            };
            return match other {
                // R579-3 / R603-4: two DIFFERENT fields hold two different
                // allocations unless one block can reach both. An OFFSET store
                // (d) puts another field's block into the field, and one local
                // stored through (c) into BOTH fields is one block; a field
                // admitted through a local beside one that never is holds a
                // different allocator evaluation's block.
                RootClass::FreshField {
                    adt: other_adt,
                    field: other_field,
                    freshness: other_freshness,
                    same_base_only: other_same_base_only,
                    via_offset: other_via_offset,
                    ..
                } => ((adt, field) != (other_adt, other_field)
                    && !via_offset
                    && !other_via_offset
                    && !(same_base_only && other_same_base_only))
                    .then(|| kind(freshness.join(other_freshness))),
                // R631-11: every store into an admitted field is an allocation
                // or null, and an allocator never returns a stack object or a
                // static, so the field's block is neither — no store needed.
                // An entry object may be the block itself, and a fresh local
                // may be the one the field was admitted through; both stay
                // refused here.
                _ => (other.object_id() == Some(base)
                    || matches!(other, RootClass::StackObject(_) | RootClass::Static(_)))
                .then(|| kind(freshness.join(other.freshness()))),
            };
        }
        _ => {}
    }
    // R641-9: a local that only ever holds blocks allocated during this
    // activation. An entry object existed at the activation's entry and an
    // allocator never returns storage overlapping a live object; a stack object
    // or a static is no block an allocator returns — rule (f)'s argument, so its
    // receipt. Beside another fresh local, or another such local, it may be the
    // same block.
    match (a, b) {
        (RootClass::AllocatedHere(_, freshness), other)
        | (other, RootClass::AllocatedHere(_, freshness)) => {
            return predates_or_is_not_a_block(other).then(|| allocation_identity(freshness));
        }
        _ => {}
    }
    // R482-4(4). A static is a named global: distinct from another static,
    // from this frame's stack and from a block allocated inside this body. A
    // parameter's pointee may BE the static, so that pair is refused.
    match (a, b) {
        (RootClass::Static(x), RootClass::Static(y)) => {
            return (x != y).then_some(CertificateKind::DistinctRoots);
        }
        (RootClass::Static(_), other) | (other, RootClass::Static(_)) => {
            return match other {
                RootClass::StackObject(_) => Some(CertificateKind::DistinctRoots),
                RootClass::FreshAlloc(_, Freshness::Proven) => Some(CertificateKind::DistinctRoots),
                RootClass::FreshAlloc(_, Freshness::Contract) => {
                    Some(CertificateKind::DistinctRootsUnderContract)
                }
                RootClass::EntryStorage(_)
                | RootClass::FreshField { .. }
                | RootClass::Static(_)
                | RootClass::Unknown => None,
                // Answered by R641-9's arm above.
                RootClass::AllocatedHere(..) => None,
            };
        }
        _ => {}
    }
    let (fresh, other) = if a.is_fresh_object() {
        (a, b)
    } else if b.is_fresh_object() {
        (b, a)
    } else {
        return None;
    };
    match other {
        RootClass::Unknown
        | RootClass::FreshField { .. }
        | RootClass::Static(_)
        | RootClass::AllocatedHere(..) => None,
        RootClass::FreshAlloc(..) | RootClass::StackObject(_) | RootClass::EntryStorage(_) => {
            (fresh.object_id() != other.object_id()).then(|| {
                match fresh.freshness().join(other.freshness()) {
                    Freshness::Proven => CertificateKind::DistinctRoots,
                    Freshness::Contract => CertificateKind::DistinctRootsUnderContract,
                }
            })
        }
    }
}

/// Where two place spines first differ, for rule (c).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Divergence {
    /// Two fields of ONE structure: disjoint byte ranges by layout.
    StructFields,
    /// Two members of one union: they overlap.
    UnionMembers,
    /// No common base, no divergence, an index divergence, or a spine a cast
    /// retyped: rule (c) says nothing.
    NotAField,
}

/// (c), Erratum 9d (ii): the same root, the same deref status, the same
/// projection at every position before the first differing one, and that
/// first difference a field projection on both sides OF THE SAME PARENT
/// STRUCTURE. Index projections before it may agree or differ (9c (iii)): an
/// `Index` carries no payload, so two indices compare equal and the walk goes
/// on. A spine a cast retyped is not a base (R550-2).
fn divergence(a: &PlacePath, b: &PlacePath) -> Divergence {
    if a.retyped || b.retyped || a.root != b.root || a.deref_root != b.deref_root {
        return Divergence::NotAField;
    }
    for (x, y) in a.projections.iter().zip(&b.projections) {
        if x == y {
            continue;
        }
        return match (x, y) {
            (
                Projection::Field {
                    parent: Some(pa),
                    union: ua,
                    ..
                },
                Projection::Field {
                    parent: Some(pb), ..
                },
            ) if pa == pb => {
                if *ua {
                    Divergence::UnionMembers
                } else {
                    Divergence::StructFields
                }
            }
            _ => Divergence::NotAField,
        };
    }
    Divergence::NotAField
}

fn disjoint_fields(a: &PlacePath, b: &PlacePath) -> bool {
    divergence(a, b) == Divergence::StructFields
}

// ---------------------------------------------------------------------------
// (b) the type rule
// ---------------------------------------------------------------------------

fn type_rule<'tcx>(
    tcx: TyCtxt<'tcx>,
    a: Ty<'tcx>,
    b: Ty<'tcx>,
    unions: &[FxHashSet<TypeClass>],
    closures: &mut FxHashMap<TypeClass, FxHashSet<TypeClass>>,
) -> Result<(), Unproved> {
    let ca = type_class(tcx, a);
    let cb = type_class(tcx, b);
    if ca == TypeClass::Unresolved || cb == TypeClass::Unresolved {
        return Err(Unproved::TypeUnresolved);
    }
    if ca == TypeClass::Wildcard || cb == TypeClass::Wildcard {
        return Err(Unproved::WildcardPointee);
    }
    if ca == cb {
        return Err(Unproved::SameType);
    }
    if is_union_class(tcx, &ca) || is_union_class(tcx, &cb) {
        return Err(Unproved::UnionPointee);
    }
    let members_a = closures
        .entry(ca.clone())
        .or_insert_with(|| member_closure(tcx, &ca))
        .clone();
    let members_b = closures
        .entry(cb.clone())
        .or_insert_with(|| member_closure(tcx, &cb))
        .clone();
    if members_a.contains(&TypeClass::Unresolved) || members_b.contains(&TypeClass::Unresolved) {
        return Err(Unproved::TypeUnresolved);
    }
    if members_a.contains(&cb) || members_b.contains(&ca) {
        return Err(Unproved::MemberType);
    }
    if unions
        .iter()
        .any(|members| members.contains(&ca) && members.contains(&cb))
    {
        return Err(Unproved::UnionSibling);
    }
    Ok(())
}

fn is_c_void(tcx: TyCtxt<'_>, ty: Ty<'_>) -> bool {
    matches!(ty.kind(), ty::Adt(definition, _)
        if tcx.lang_items().get(LangItem::CVoid) == Some(definition.did()))
}

fn type_class<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> TypeClass {
    let pointer_width = tcx.data_layout.pointer_size.bits();
    match ty.kind() {
        ty::Int(ty::IntTy::I8) | ty::Uint(ty::UintTy::U8) => TypeClass::Wildcard,
        ty::Int(int) => TypeClass::Int(int.bit_width().unwrap_or(pointer_width)),
        ty::Uint(uint) => TypeClass::Int(uint.bit_width().unwrap_or(pointer_width)),
        ty::Float(float) => TypeClass::Float(float.bit_width()),
        ty::Bool => TypeClass::Bool,
        ty::RawPtr(..) | ty::Ref(..) => TypeClass::Pointer,
        ty::FnPtr(..) | ty::FnDef(..) => TypeClass::FnPointer,
        ty::Array(element, _) => type_class(tcx, *element),
        ty::Adt(definition, _) if is_c_void(tcx, ty) => {
            let _ = definition;
            TypeClass::Wildcard
        }
        // `Option<fn ptr>` is the C2Rust spelling of a nullable function
        // pointer; any other generic ADT is not a C object type.
        ty::Adt(definition, args)
            if tcx.is_diagnostic_item(rustc_span::sym::Option, definition.did()) =>
        {
            match args.first().and_then(|arg| arg.as_type()) {
                Some(inner) if matches!(inner.kind(), ty::FnPtr(..)) => TypeClass::FnPointer,
                _ => TypeClass::Unresolved,
            }
        }
        ty::Adt(definition, _) => TypeClass::Adt(definition.did()),
        _ => TypeClass::Unresolved,
    }
}

fn is_union_class(tcx: TyCtxt<'_>, class: &TypeClass) -> bool {
    matches!(class, TypeClass::Adt(did) if tcx.adt_def(*did).is_union())
}

/// Every type class reachable from `class` through struct / union fields and
/// array elements. Pointer members stop the walk: the pointee is a different
/// object. Includes `class` itself.
fn member_closure(tcx: TyCtxt<'_>, class: &TypeClass) -> FxHashSet<TypeClass> {
    let mut out = FxHashSet::default();
    let mut stack = vec![class.clone()];
    while let Some(current) = stack.pop() {
        if !out.insert(current.clone()) {
            continue;
        }
        let TypeClass::Adt(did) = current else {
            continue;
        };
        let adt = tcx.adt_def(did);
        if adt.is_enum() {
            // A C2Rust enum is a type alias to an integer; a Rust enum here is
            // `c_void`-like or foreign to C. Its variants carry no C member
            // object that a pointer could address.
            continue;
        }
        for variant in adt.variants() {
            for field in &variant.fields {
                let field_ty = tcx.type_of(field.did).instantiate_identity();
                stack.push(type_class(tcx, field_ty));
            }
        }
    }
    out
}

/// The transitive member classes of every union in the program.
///
/// Enumerated from the crate's free items, NOT from `RustProgram::structs`:
/// that list is built from `ItemKind::Struct` alone and never sees a union,
/// which is exactly the type this clause exists for (caught by the
/// `w6p_type_rule_union_sibling_stays_held` witness on the first build).
fn union_member_classes(tcx: TyCtxt<'_>, _program: &RustProgram<'_>) -> Vec<FxHashSet<TypeClass>> {
    tcx.hir_crate_items(())
        .free_items()
        .map(|id| id.owner_id.def_id)
        .filter(|did| tcx.def_kind(*did) == DefKind::Union)
        .map(|did| member_closure(tcx, &TypeClass::Adt(did.to_def_id())))
        .collect()
}

// ---------------------------------------------------------------------------
// (a) root classes, read from the caller body
// ---------------------------------------------------------------------------

fn peel_casts<'e>(mut expr: &'e Expr<'e>) -> &'e Expr<'e> {
    while let ExprKind::Cast(inner, _) = &expr.kind {
        expr = inner;
    }
    expr
}

/// R550-2: `peel_casts`, also reporting whether any peeled cast changed the
/// POINTEE type (`*mut T as *mut U`, an integer cast to a pointer). A cast that
/// only changes mutability or turns a reference into a raw pointer keeps it.
fn peel_casts_retyping<'e, 'tcx>(
    typeck: &TypeckResults<'tcx>,
    mut expr: &'e Expr<'e>,
) -> (&'e Expr<'e>, bool) {
    let mut retyped = false;
    while let ExprKind::Cast(inner, _) = &expr.kind {
        let from = typeck.expr_ty(inner).builtin_deref(true);
        let to = typeck.expr_ty(expr).builtin_deref(true);
        retyped |= match (from, to) {
            (Some(from), Some(to)) => from != to,
            _ => true,
        };
        expr = inner;
    }
    (expr, retyped)
}

/// R550-2: mark a place a cast retyped on the way to it.
fn retyped_by(place: Option<PlacePath>, retyped: bool) -> Option<PlacePath> {
    place.map(|mut path| {
        path.retyped |= retyped;
        path
    })
}

fn callee_def_id(expr: &Expr<'_>) -> Option<DefId> {
    let ExprKind::Path(QPath::Resolved(_, path)) = &expr.kind else {
        return None;
    };
    match path.res {
        Res::Def(DefKind::Fn, did) => Some(did),
        _ => None,
    }
}

fn is_null_literal(expr: &Expr<'_>) -> bool {
    match &peel_casts(expr).kind {
        ExprKind::Lit(lit) => matches!(lit.node, rustc_ast::LitKind::Int(value, _) if value == 0),
        ExprKind::Call(callee, args) if args.is_empty() => {
            callee_def_id(callee).is_some_and(|_| {
                // `core::ptr::null_mut()` / `null()`
                matches!(&callee.kind, ExprKind::Path(QPath::Resolved(_, path))
                if path.segments.last().is_some_and(|segment| {
                    matches!(segment.ident.name.as_str(), "null" | "null_mut")
                }))
            })
        }
        _ => false,
    }
}

/// What counts as an allocator: the libc allocators by name, the local
/// wrappers found so far, and — through the closed-world fn-pointer web — a
/// call through a function pointer every resolved target of which is one of
/// those (R402-5(6): `BrotliAllocate`'s `(*m).alloc_func` resolves to
/// `BrotliDefaultAllocFunc`, itself a wrapper of `malloc`).
struct AllocatorOracle<'a> {
    wrappers: FxHashMap<DefId, Freshness>,
    /// Function-pointer FIELDS every assignment to which, program-wide, stores
    /// a known allocator (R433-6(2)). Keyed by the struct's `DefId` and the
    /// field's name.
    allocator_fields: FxHashMap<(DefId, Symbol), Freshness>,
    /// R482-4(3): callees whose EVERY return is null or a view of one formal,
    /// with that formal's index. A call of one is a derivation of the argument
    /// at that index.
    views: FxHashMap<DefId, usize>,
    indirect_calls: Option<&'a [super::lifetime::MirCallTargetSite]>,
}

impl AllocatorOracle<'_> {
    /// A libc allocator is a FOREIGN item (C2Rust declares it in an
    /// `extern "C"` block inside the crate, so its `DefId` IS local — the test
    /// is foreignness, not locality) with the allocator's name.
    fn is_libc_allocator(tcx: TyCtxt<'_>, did: DefId) -> bool {
        let name = tcx.item_name(did);
        tcx.is_foreign_item(did) && LIBC_ALLOCATORS.contains(&name.as_str())
    }

    /// Is `expr` (after casts) a call whose result is a fresh allocation, in
    /// the body of `function`?
    fn is_allocator_call(
        &self,
        tcx: TyCtxt<'_>,
        function: LocalDefId,
        expr: &Expr<'_>,
    ) -> Option<Freshness> {
        let ExprKind::Call(callee, _) = &peel_casts(expr).kind else {
            return None;
        };
        if let Some(did) = callee_def_id(callee) {
            if let Some(freshness) = self.wrappers.get(&did) {
                return Some(*freshness);
            }
            return Self::is_libc_allocator(tcx, did).then_some(Freshness::Proven);
        }
        // A call through a FUNCTION-POINTER FIELD: admitted when every
        // assignment to that field in the program stores a known allocator
        // (R433-6(2)). brotli's `((*m).alloc_func).expect(..)(..)` is the
        // shape; the field is written once, by `BrotliInitMemoryManager`.
        if let Some(key) = fn_pointer_field_key(tcx, function, callee)
            && let Some(freshness) = self.allocator_fields.get(&key)
        {
            return Some(*freshness);
        }
        // A call through a function pointer: every closed-world target must be
        // an allocator wrapper already admitted. Foreign targets (libc
        // `malloc` stored in a static, as binn does) are not in the web's
        // local inventory, so such a call has no resolved target and is NOT
        // admitted — a typed residue, not a gap in the closed world.
        let Some(sites) = self.indirect_calls else {
            return None;
        };
        let span = expr.span.source_callsite();
        let targets = sites
            .iter()
            .filter(|site| site.caller == function && site.span.source_callsite().contains(span))
            .map(|site| site.callee.to_def_id())
            .collect::<Vec<_>>();
        if targets.is_empty() {
            return None;
        }
        targets
            .iter()
            .map(|target| self.wrappers.get(target).copied())
            .try_fold(Freshness::Proven, |acc, target| Some(acc.join(target?)))
    }
}

/// R459-4(2) PROBE ONLY — no emission path reads this. For every call site
/// the index recorded, one row per ordered formal pair: the two roots' classes
/// and, when a root is the caller's own parameter, that parameter's index.
/// Report 011's source-text read could not map 88 pairs to a caller parameter;
/// this is the same question asked of the compiler instead of the text.
#[cfg(test)]
pub(crate) struct ProbeRow {
    /// R466-5 sizing: for a side whose root is a STACK object, how many times
    /// the caller's body takes that local's address, and whether the callee's
    /// formal at that position is never retained (wave-6r's MIR walk).
    pub left_takes: Option<usize>,
    pub right_takes: Option<usize>,
    pub left_free: Option<bool>,
    pub right_free: Option<bool>,
    pub caller: LocalDefId,
    pub callee: LocalDefId,
    pub left: usize,
    pub right: usize,
    pub left_class: String,
    pub right_class: String,
    pub left_param: Option<usize>,
    pub right_param: Option<usize>,
    /// R478-5: why each side's root is `Unknown` (`known` when it is not).
    pub left_why: String,
    pub right_why: String,
    /// R500-9: is this pair a model-shared READ/READ pair — both formals
    /// `*const`, unwritten and never mutably reborrowed? The fact
    /// `is_shared_read_pair` exposes, so the frame's read-read set can be
    /// stated without reusing an older pair list.
    pub shared_read: bool,
    pub outcome: String,
    /// R550-2 audit: the call's source line and each side's place spine,
    /// every field with its parent (`.name@Parent`, `U` marks a union parent),
    /// `!` when a cast retyped it, `-` when no place was formed.
    pub site: String,
    pub left_place: String,
    pub right_place: String,
}

#[cfg(test)]
impl PairDisjointnessIndex {
    /// Every recorded pair of pointer arguments, with each side's root class
    /// and its caller-parameter index when the root IS a parameter binding.
    pub(crate) fn probe_rows(&self, program: &RustProgram<'_>) -> Vec<ProbeRow> {
        let tcx = program.tcx;
        let mut params: FxHashMap<LocalDefId, Vec<HirId>> = FxHashMap::default();
        for &function in &program.functions {
            let Some(body_id) = tcx.hir_node_by_def_id(function).body_id() else {
                continue;
            };
            let mut ids = Vec::new();
            for param in tcx.hir_body(body_id).params {
                if let PatKind::Binding(_, hir_id, ..) = param.pat.kind {
                    ids.push(hir_id);
                }
            }
            params.insert(function, ids);
        }
        let index_of = |function: LocalDefId, class: RootClass| -> Option<usize> {
            let id = class.object_id()?;
            params
                .get(&function)?
                .iter()
                .position(|candidate| *candidate == id)
        };
        let describe = |class: RootClass| -> String {
            match class {
                RootClass::FreshAlloc(_, Freshness::Proven) => "fresh".to_owned(),
                RootClass::FreshAlloc(_, Freshness::Contract) => "fresh-contract".to_owned(),
                RootClass::StackObject(_) => "stack".to_owned(),
                RootClass::EntryStorage(_) => "entry".to_owned(),
                RootClass::AllocatedHere(_, Freshness::Proven) => "allocated-here".to_owned(),
                RootClass::AllocatedHere(_, Freshness::Contract) => {
                    "allocated-here-contract".to_owned()
                }
                RootClass::FreshField {
                    field, freshness, ..
                } => match freshness {
                    Freshness::Proven => format!("fresh-field:{field}"),
                    Freshness::Contract => format!("fresh-field-contract:{field}"),
                },
                RootClass::Static(_) => "static".to_owned(),
                RootClass::Unknown => "unknown".to_owned(),
            }
        };
        // R466-5 sizing inputs, memoized: address-takings per (function,
        // binding) and the retention verdict per (callee, formal).
        let functions = program.functions.clone();
        let mut takes: FxHashMap<(LocalDefId, HirId), usize> = FxHashMap::default();
        for &function in &program.functions {
            let Some(body_id) = tcx.hir_node_by_def_id(function).body_id() else {
                continue;
            };
            let mut counter = AddressTakes {
                typeck: tcx.typeck(function),
                counts: FxHashMap::default(),
            };
            counter.visit_body(tcx.hir_body(body_id));
            for (binding, count) in counter.counts {
                takes.insert((function, binding), count);
            }
        }
        let mut free: FxHashMap<(LocalDefId, usize), bool> = FxHashMap::default();
        let mut retention = |callee: LocalDefId, index: usize| -> bool {
            *free.entry((callee, index)).or_insert_with(|| {
                crate::bo_rewriter::wave6r_child_access::position_is_descendant_free(
                    tcx, &functions, callee, index,
                )
            })
        };

        let mut rows = Vec::new();
        for (&(caller, callee), records) in &self.sites {
            let caller_did = program
                .functions
                .iter()
                .find(|did| did.local_def_index.as_u32() == caller)
                .copied();
            let callee_did = program
                .functions
                .iter()
                .find(|did| did.local_def_index.as_u32() == callee)
                .copied();
            let (Some(caller_did), Some(callee_did)) = (caller_did, callee_did) else {
                continue;
            };
            for record in records {
                for (position, left) in record.args.iter().enumerate() {
                    if !left.is_pointer {
                        continue;
                    }
                    for right in record.args.iter().skip(position + 1) {
                        if !right.is_pointer {
                            continue;
                        }
                        let spine = |place: &Option<PlacePath>| -> String {
                            let Some(path) = place else {
                                return "-".to_owned();
                            };
                            let mut out = format!(
                                "{}{}",
                                if path.deref_root { "*" } else { "" },
                                tcx.hir_name(path.root)
                            );
                            for projection in &path.projections {
                                match projection {
                                    Projection::Field {
                                        parent,
                                        union,
                                        name,
                                    } => {
                                        let parent = parent.map_or("?".to_owned(), |did| {
                                            tcx.item_name(did).to_string()
                                        });
                                        out += &format!(
                                            ".{name}@{parent}{}",
                                            if *union { "U" } else { "" }
                                        );
                                    }
                                    Projection::Index => out += "[]",
                                }
                            }
                            if path.retyped {
                                out += "!";
                            }
                            out
                        };
                        let outcome = self
                            .certify(
                                caller,
                                callee,
                                left.index,
                                right.index,
                                left.span,
                                right.span,
                            )
                            .map_or_else(|why| why.key().to_owned(), CertificateKind::receipt);
                        let stack_take = |class: RootClass| match class {
                            RootClass::StackObject(id) => {
                                takes.get(&(caller_did, id)).copied().or(Some(0))
                            }
                            _ => None,
                        };
                        let left_takes = stack_take(left.class);
                        let right_takes = stack_take(right.class);
                        let left_free = left_takes.map(|_| retention(callee_did, left.index));
                        let right_free = right_takes.map(|_| retention(callee_did, right.index));
                        rows.push(ProbeRow {
                            left_takes,
                            right_takes,
                            left_free,
                            right_free,
                            caller: caller_did,
                            callee: callee_did,
                            left: left.index,
                            right: right.index,
                            left_class: describe(left.class),
                            right_class: describe(right.class),
                            left_param: index_of(caller_did, left.class),
                            right_param: index_of(caller_did, right.class),
                            left_why: left.why.key().to_owned(),
                            right_why: right.why.key().to_owned(),
                            shared_read: self.shared_reads.contains(&(callee, left.index))
                                && self.shared_reads.contains(&(callee, right.index)),
                            outcome,
                            site: {
                                let at =
                                    tcx.sess.source_map().lookup_char_pos(record.call_span.lo());
                                format!("{}:{}", at.line, at.col.0 + 1)
                            },
                            left_place: spine(&left.place),
                            right_place: spine(&right.place),
                        });
                    }
                }
            }
        }
        rows
    }
}

/// R466-5: how many times each binding's ADDRESS is taken in one body
/// (`&mut x`, `&x`, `x.as_mut_ptr()` on an array). Exactly one taking is the
/// shape the temporal certificate needs; a second is an escape it refuses.
struct AddressTakes<'a, 'tcx> {
    typeck: &'a TypeckResults<'tcx>,
    counts: FxHashMap<HirId, usize>,
}

impl<'tcx> Visitor<'tcx> for AddressTakes<'_, 'tcx> {
    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        match &expr.kind {
            // EVERY address-taking counts, raw borrows (`&raw mut x`) included:
            // this counter is what makes "first taken at this call" true, so it
            // must over-count rather than miss one.
            ExprKind::AddrOf(_, _, operand) => {
                if let Some(binding) = derivation_place_base(self.typeck, peel_casts(operand)) {
                    *self.counts.entry(binding).or_default() += 1;
                }
            }
            ExprKind::MethodCall(segment, receiver, args, _)
                if args.is_empty()
                    && matches!(segment.ident.name.as_str(), "as_mut_ptr" | "as_ptr") =>
            {
                if let Some(binding) = derivation_place_base(self.typeck, peel_casts(receiver)) {
                    *self.counts.entry(binding).or_default() += 1;
                }
            }
            _ => {}
        }
        intravisit::walk_expr(self, expr);
    }
}

/// Local functions that are allocator WRAPPERS: every value the function
/// returns is (a cast of) an allocator call, a null literal, or a local that
/// is itself a fresh-allocation binding of that body. Iterated to a fixpoint
/// so a wrapper of a wrapper qualifies, and so a call through a function
/// pointer qualifies once every target has (R402-5(6)).
fn allocator_wrappers<'a>(
    tcx: TyCtxt<'_>,
    functions: &FxHashSet<LocalDefId>,
    indirect_calls: Option<&'a [super::lifetime::MirCallTargetSite]>,
) -> AllocatorOracle<'a> {
    let mut oracle = AllocatorOracle {
        wrappers: FxHashMap::default(),
        allocator_fields: FxHashMap::default(),
        views: FxHashMap::default(),
        indirect_calls,
    };
    loop {
        let before = (
            oracle.wrappers.len(),
            oracle.allocator_fields.len(),
            oracle.views.len(),
        );
        oracle.allocator_fields = allocator_fn_pointer_fields(tcx, functions, &oracle);
        oracle.views = view_of_formal(tcx, functions, &oracle);
        for &function in functions {
            if oracle.wrappers.contains_key(&function.to_def_id()) {
                continue;
            }
            let Some(body_id) = tcx.hir_node_by_def_id(function).body_id() else {
                continue;
            };
            let output = tcx.fn_sig(function).skip_binder().skip_binder().output();
            if !matches!(output.kind(), ty::RawPtr(..)) {
                continue;
            }
            let body = tcx.hir_body(body_id);
            let mut returns = ReturnCollector {
                returns: Vec::new(),
            };
            returns.visit_body(body);
            if let ExprKind::Block(block, _) = &body.value.kind
                && let Some(tail) = block.expr
            {
                returns.returns.push(tail);
            }
            if returns.returns.is_empty() {
                continue;
            }
            let typeck = tcx.typeck(function);
            let (classes, _why, _prefixes) = classify_locals(tcx, typeck, body, &oracle, function);
            // Every returned value must be fresh; the wrapper is only as
            // strong as its weakest return, so one contract-backed return
            // makes the wrapper contract-backed.
            let mut freshness = Some(Freshness::Proven);
            for expr in &returns.returns {
                if is_null_literal(expr) {
                    continue;
                }
                let value =
                    oracle
                        .is_allocator_call(tcx, function, expr)
                        .or_else(|| {
                            match resolved_local(peel_casts(expr))
                                .map(|binding| classes.get(&binding))
                            {
                                Some(Some(RootClass::FreshAlloc(_, value))) => Some(*value),
                                _ => None,
                            }
                        });
                freshness = match (freshness, value) {
                    (Some(acc), Some(value)) => Some(acc.join(value)),
                    _ => None,
                };
                if freshness.is_none() {
                    break;
                }
            }
            if let Some(freshness) = freshness {
                oracle.wrappers.insert(function.to_def_id(), freshness);
            }
        }
        if (
            oracle.wrappers.len(),
            oracle.allocator_fields.len(),
            oracle.views.len(),
        ) == before
        {
            return oracle;
        }
    }
}

/// The function-pointer fields a call may be routed through and still count as
/// an allocation (R433-6(2)). A field qualifies when the program assigns it at
/// least once and EVERY assignment — an ordinary store or a struct literal —
/// stores a libc allocator or an already-admitted wrapper. One assignment this
/// read cannot resolve refuses the field, so the closed world is the same one
/// the R409-1 allocator contract rests on: nothing outside the crate's own
/// bodies may have written it. A union's field is never admitted — a union
/// member shares storage with its siblings.
fn allocator_fn_pointer_fields(
    tcx: TyCtxt<'_>,
    functions: &FxHashSet<LocalDefId>,
    oracle: &AllocatorOracle<'_>,
) -> FxHashMap<(DefId, Symbol), Freshness> {
    let mut assignments: FxHashMap<(DefId, Symbol), Vec<FieldStore>> = FxHashMap::default();
    for &function in functions {
        let Some(body_id) = tcx.hir_node_by_def_id(function).body_id() else {
            continue;
        };
        let mut collector = FieldStoreCollector {
            tcx,
            typeck: tcx.typeck(function),
            oracle,
            assignments: &mut assignments,
        };
        collector.visit_body(tcx.hir_body(body_id));
    }
    // R434-4(5). Resolved allocator stores only  -> the field is an allocator,
    // proven. At least one resolved allocator plus stores this read cannot
    // resolve (a caller-supplied pointer, as brotli's `alloc_func` is) -> the
    // field is an allocator UNDER R409-1's contract, and every certificate
    // that rests on it says so. A store that resolves to a function which is
    // NOT an allocator refuses the field outright — the contract speaks for
    // conforming allocators, not for whatever else a program may store.
    assignments
        .into_iter()
        .filter_map(|(key, stores)| {
            if stores
                .iter()
                .any(|store| *store == FieldStore::NotAnAllocator)
            {
                return None;
            }
            let strongest = stores
                .iter()
                .filter_map(|store| match store {
                    FieldStore::Allocator(freshness) => Some(*freshness),
                    FieldStore::Unresolved | FieldStore::NotAnAllocator => None,
                })
                .reduce(Freshness::join)?;
            let unresolved = stores.iter().any(|store| *store == FieldStore::Unresolved);
            Some((
                key,
                if unresolved {
                    Freshness::Contract
                } else {
                    strongest
                },
            ))
        })
        .collect()
}

/// One store into a function-pointer field.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FieldStore {
    /// A known allocator: a libc allocator or an admitted wrapper.
    Allocator(Freshness),
    /// A function item that is not an allocator. Refuses the field.
    NotAnAllocator,
    /// Not resolvable to a function item at all — a parameter, another field,
    /// an unknown cast. Admitted only under the contract.
    Unresolved,
}

/// `(*m).alloc_func` (or `m.alloc_func`), possibly behind `.expect(..)` /
/// `.unwrap()` as C2Rust spells an `Option<fn>` call: the struct and the field
/// it reads, when that field's declared type is a function pointer.
fn fn_pointer_field_key(
    tcx: TyCtxt<'_>,
    function: LocalDefId,
    callee: &Expr<'_>,
) -> Option<(DefId, Symbol)> {
    let mut expr = peel_casts(callee);
    while let ExprKind::MethodCall(segment, receiver, ..) = &expr.kind {
        if !matches!(segment.ident.name.as_str(), "expect" | "unwrap") {
            return None;
        }
        expr = peel_casts(receiver);
    }
    let ExprKind::Field(base, field) = &expr.kind else {
        return None;
    };
    adt_field_key(tcx, tcx.typeck(function), base, field.name)
}

/// The `(struct, field)` key of a field access, refusing unions and fields
/// whose declared type is not a function pointer.
/// R479-4a: the `(adt, field)` key of a POINTER-typed field access. A union's
/// field is never keyed — a union member shares storage with its siblings.
fn data_field_key<'tcx>(
    tcx: TyCtxt<'tcx>,
    typeck: &TypeckResults<'tcx>,
    base: &Expr<'_>,
    field: Symbol,
) -> Option<(DefId, Symbol)> {
    let ty::Adt(def, args) = typeck.expr_ty_adjusted(base).peel_refs().kind() else {
        return None;
    };
    if def.is_union() {
        return None;
    }
    let declared = def
        .all_fields()
        .find(|candidate| candidate.name == field)?
        .ty(tcx, args);
    matches!(declared.kind(), ty::RawPtr(..)).then_some((def.did(), field))
}

/// R482-4(3): the callees whose EVERY return is the null literal or a view of
/// ONE formal — `return p` where `p` only ever walks within the storage it
/// entered with. A call of such a callee hands back its argument's object, so
/// the caller's local keeps that argument's root instead of going `Unknown`.
///
/// Computed to a fixpoint with the allocator wrappers, because a view can be
/// built out of another: binn's `SearchForKey` is a view of its formal 0 only
/// once `AdvanceDataPos` is known to be one. A callee still unknown on this
/// round simply contributes no view, so the map only grows and the outer loop
/// terminates.
fn view_of_formal(
    tcx: TyCtxt<'_>,
    functions: &FxHashSet<LocalDefId>,
    oracle: &AllocatorOracle<'_>,
) -> FxHashMap<DefId, usize> {
    let mut views = FxHashMap::default();
    for &function in functions {
        let Some(body_id) = tcx.hir_node_by_def_id(function).body_id() else {
            continue;
        };
        let output = tcx.fn_sig(function).skip_binder().skip_binder().output();
        if !matches!(output.kind(), ty::RawPtr(..)) {
            continue;
        }
        let body = tcx.hir_body(body_id);
        let mut returns = ReturnCollector {
            returns: Vec::new(),
        };
        returns.visit_body(body);
        if let ExprKind::Block(block, _) = &body.value.kind
            && let Some(tail) = block.expr
        {
            returns.returns.push(tail);
        }
        if returns.returns.is_empty() {
            continue;
        }
        let params: Vec<HirId> = body
            .params
            .iter()
            .filter_map(|param| match param.pat.kind {
                PatKind::Binding(_, hir_id, ..) => Some(hir_id),
                _ => None,
            })
            .collect();
        let typeck = tcx.typeck(function);
        let (classes, _why, _prefixes) = classify_locals(tcx, typeck, body, oracle, function);
        let mut index = None;
        let mut every = true;
        for expr in &returns.returns {
            if is_null_literal(expr) {
                continue;
            }
            // `EntryStorage(h)` is exactly "the storage this parameter entered
            // with": a fresh allocation, a stack object or an unknown root all
            // fail here, and so does a second formal.
            let (class, _) = argument_provenance(tcx, typeck, &classes, expr);
            let Some(position) = (match class {
                RootClass::EntryStorage(h) => params.iter().position(|p| *p == h),
                _ => None,
            }) else {
                every = false;
                break;
            };
            match index {
                None => index = Some(position),
                Some(seen) if seen == position => {}
                Some(_) => {
                    every = false;
                    break;
                }
            }
        }
        if let Some(position) = index.filter(|_| every) {
            views.insert(function.to_def_id(), position);
        }
    }
    views
}

/// R479-4a: the pointer fields every one of whose stores in the program is a
/// DIRECTLY CALLED NAMED allocator — a libc allocator or a wrapper whose own
/// freshness is proven — or the null literal. One store of anything else (a
/// copy of a local or another field, a parameter, an indirect allocator call
/// through a function pointer) refuses the field outright, so the admitted set
/// is exactly the fields whose contents the closed world can account for.
///
/// R579-3 widens the admission by two store shapes, each keeping the claim the
/// pair rule reads — the block was returned while the base object was live:
///
/// * **(c)** a `FreshAlloc` local of the storing body (every assignment an
///   allocator result or null, its address never taken) stored into a field of
///   ENTRY storage. The base object existed at the storing function's entry and
///   the allocation happened in its body.
/// * **(d)** `(*b).g.offset(k)` (`add`, `wrapping_*`) where `g` is itself
///   admitted and read out of the SAME base object: the value stays inside
///   `g`'s block. Admitted only while `g` is — a greatest fixpoint.
///
/// A field admitted either way is `same_base_only`: under (d) it names another
/// field's block, and under (c) one local may be stored into two fields. R603-4
/// keeps (d) apart as `via_offset`, which the different-fields clause never
/// separates, while a (c) field separates from a field that is neither.
///
/// And every admission — R479-4a's own included — is refused for a struct that
/// the program writes WITHOUT a field store ([`struct_writes_outside_field_stores`]):
/// a whole-struct copy, a byte writer aimed at it or at a container of it, or
/// a pointer reaching it cast to another non-byte, non-void pointee (R538-7 /
/// R544-4). Any of those can put another object's pointer in the field.
fn allocator_data_fields(
    tcx: TyCtxt<'_>,
    functions: &FxHashSet<LocalDefId>,
    oracle: &AllocatorOracle<'_>,
) -> FxHashMap<(DefId, Symbol), FreshFieldFact> {
    let mut allocator: FxHashMap<(DefId, Symbol), Freshness> = FxHashMap::default();
    let mut refused: FxHashSet<(DefId, Symbol)> = FxHashSet::default();
    let mut same_base_only: FxHashSet<(DefId, Symbol)> = FxHashSet::default();
    let mut offsets: Vec<((DefId, Symbol), (DefId, Symbol))> = Vec::new();
    for &function in functions {
        let Some(body_id) = tcx.hir_node_by_def_id(function).body_id() else {
            continue;
        };
        let mut collector = DataFieldStoreCollector {
            tcx,
            typeck: tcx.typeck(function),
            oracle,
            function,
            body: tcx.hir_body(body_id),
            classes: None,
            allocator: &mut allocator,
            refused: &mut refused,
            same_base_only: &mut same_base_only,
            offsets: &mut offsets,
        };
        collector.visit_body(tcx.hir_body(body_id));
    }
    // R583-5 (G3): every OTHER body the program owns is a store site too. A
    // `static` or `const` initializer's struct literal writes each pointer
    // field it names exactly as a store does — a self-referential sentinel
    // (`Node { next: &raw mut SENTINEL }`) puts the base object into its own
    // field — and a visit of a function does not enter a closure's body. Such
    // a literal can never call an allocator, so every non-null pointer it
    // names refuses the field.
    for owner in tcx.hir_body_owners() {
        if functions.contains(&owner) {
            continue;
        }
        let body = tcx.hir_body_owned_by(owner);
        let mut collector = DataFieldStoreCollector {
            tcx,
            typeck: tcx.typeck(owner),
            oracle,
            function: owner,
            body,
            classes: None,
            allocator: &mut allocator,
            refused: &mut refused,
            same_base_only: &mut same_base_only,
            offsets: &mut offsets,
        };
        collector.visit_body(body);
    }
    // (d)'s fields are candidates on their offset stores alone.
    for (field, _) in &offsets {
        allocator.entry(*field).or_insert(Freshness::Proven);
    }
    let structs: FxHashSet<DefId> = allocator.keys().map(|(adt, _)| *adt).collect();
    let written = struct_writes_outside_field_stores(tcx, &structs);
    allocator.retain(|key, _| !refused.contains(key) && !written.contains(&key.0));
    // The greatest fixpoint over (d): a field derived from an unadmitted field
    // leaves, and a derived field is as contract-backed as its source.
    loop {
        let mut changed = false;
        for (field, source) in &offsets {
            let Some(&current) = allocator.get(field) else {
                continue;
            };
            match allocator.get(source).copied() {
                Some(freshness) => {
                    let joined = current.join(freshness);
                    if joined != current {
                        allocator.insert(*field, joined);
                        changed = true;
                    }
                }
                None => {
                    allocator.remove(field);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    allocator
        .into_iter()
        .map(|(key, freshness)| {
            (
                key,
                FreshFieldFact {
                    freshness,
                    same_base_only: same_base_only.contains(&key),
                    via_offset: offsets.iter().any(|(field, _)| *field == key),
                },
            )
        })
        .collect()
}

/// libc and `core::ptr` writers that can put bytes into a struct without a
/// field store. Matched by name, as R538-7 matches them; `realloc` moves the
/// object's bytes into a new block.
const STRUCT_BYTE_WRITERS: &[&str] = &[
    "memcpy",
    "memmove",
    "memset",
    "realloc",
    "bcopy",
    "bzero",
    "fread",
    "read",
    "recv",
    "strcpy",
    "strncpy",
    "memccpy",
    "copy",
    "copy_nonoverlapping",
    "write",
    "write_bytes",
    "write_unaligned",
    "copy_from",
    "copy_to",
    "copy_from_nonoverlapping",
    "copy_to_nonoverlapping",
    // R583-5 G2: whole-value movers of `core::mem` / `core::ptr`.
    "swap",
    "replace",
    "take",
    "swap_nonoverlapping",
    "write_volatile",
];

/// R583-5 G1: is `callee` a deallocator, and if so which argument does it
/// release? The allocator contracts' free functions by name (`free`,
/// `BrotliFree`), and a call through a `free_func` function-pointer field —
/// `((*m).free_func).expect(..)(opaque, p)` or a local copy of that field —
/// which releases its second argument.
fn deallocator_pointer_index(tcx: TyCtxt<'_>, callee: &Expr<'_>) -> Option<usize> {
    if let Some(did) = callee_def_id(callee) {
        let name = tcx.item_name(did);
        return super::allocator_contract::CONTRACTS
            .iter()
            .find(|contract| contract.free == name.as_str())
            .map(|contract| contract.pointer_index);
    }
    let ExprKind::MethodCall(segment, receiver, _, _) = &peel_casts(callee).kind else {
        return None;
    };
    if !matches!(segment.ident.name.as_str(), "expect" | "unwrap") {
        return None;
    }
    let named_free_func = match &peel_casts(receiver).kind {
        ExprKind::Field(_, field) => field.name.as_str() == "free_func",
        ExprKind::Path(QPath::Resolved(_, path)) => path
            .segments
            .last()
            .is_some_and(|segment| segment.ident.name.as_str() == "free_func"),
        _ => false,
    };
    named_free_func.then_some(1)
}

/// R579-3 refusals (3) and (4): the structs among `structs` that the program
/// writes other than through a field store — so a pointer field of one may
/// hold another object's pointer without any store the admission scan reads.
///
/// * a whole-value write of a type that holds the struct at any depth (`*dst =
///   *src`, a container assigned whole, a struct literal field copied from a
///   place): a struct LITERAL is exempt as a whole, because its own fields are
///   scanned as stores;
/// * a byte writer ([`STRUCT_BYTE_WRITERS`]) any of whose arguments points at
///   a type holding the struct (R538-7);
/// * a pointer reaching the struct cast to another pointee that is neither a
///   byte nor `void` (R544-4's pun: `*(rb as *mut *mut u8) = p` writes the
///   first field);
/// * R583-5 G1: the same cast to a byte or `void` pointee, too — the bytes go
///   to code this scan cannot read — UNLESS the cast's value goes straight to
///   a deallocator ([`deallocator_pointer_index`]), which only releases the
///   object.
fn struct_writes_outside_field_stores<'tcx>(
    tcx: TyCtxt<'tcx>,
    structs: &FxHashSet<DefId>,
) -> FxHashSet<DefId> {
    struct Writes<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        typeck: &'a TypeckResults<'tcx>,
        structs: &'a [(DefId, Ty<'tcx>)],
        written: &'a mut FxHashSet<DefId>,
        /// G1: the casts that are a deallocator's released argument (every
        /// cast of the chain), recorded when the call is visited — before its
        /// arguments are.
        released: FxHashSet<HirId>,
    }
    impl<'tcx> Writes<'_, 'tcx> {
        /// Every struct `ty` holds by value, at any depth.
        fn held_by(&mut self, ty: Ty<'tcx>) {
            for &(adt, adt_ty) in self.structs {
                if super::counted_void::type_contains(self.tcx, ty, adt_ty) {
                    self.written.insert(adt);
                }
            }
        }

        /// Every struct the pointee of `ty` holds, when `ty` is a pointer.
        fn reached_by(&mut self, ty: Ty<'tcx>) {
            if let Some(pointee) = ty.builtin_deref(true) {
                self.held_by(pointee);
            }
        }

        fn is_struct_literal(expr: &Expr<'_>) -> bool {
            matches!(peel_casts(expr).kind, ExprKind::Struct(..))
        }
    }
    impl<'tcx> Visitor<'tcx> for Writes<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            match &expr.kind {
                ExprKind::Assign(place, value, _) if !Self::is_struct_literal(value) => {
                    self.held_by(self.typeck.expr_ty(place));
                }
                ExprKind::Struct(_, fields, _) => {
                    for field in *fields {
                        if !Self::is_struct_literal(field.expr) {
                            self.held_by(self.typeck.expr_ty(field.expr));
                        }
                    }
                }
                ExprKind::Cast(inner, _) => {
                    let from = self.typeck.expr_ty(inner);
                    let to = self.typeck.expr_ty(expr);
                    if let (Some(from_pointee), Some(to_pointee)) =
                        (from.builtin_deref(true), to.builtin_deref(true))
                        && from_pointee != to_pointee
                        && !self.released.contains(&expr.hir_id)
                    {
                        self.held_by(from_pointee);
                    }
                }
                ExprKind::Call(callee, args) => {
                    if let Some(index) = deallocator_pointer_index(self.tcx, callee)
                        && let Some(mut arg) = args.get(index)
                    {
                        while let ExprKind::Cast(inner, _) = &arg.kind {
                            self.released.insert(arg.hir_id);
                            arg = inner;
                        }
                    }
                    if let Some(did) = callee_def_id(callee)
                        && STRUCT_BYTE_WRITERS.contains(&self.tcx.item_name(did).as_str())
                    {
                        for arg in *args {
                            self.reached_by(self.typeck.expr_ty(peel_casts(arg)));
                        }
                    }
                }
                ExprKind::MethodCall(segment, receiver, args, _)
                    if STRUCT_BYTE_WRITERS.contains(&segment.ident.name.as_str()) =>
                {
                    self.reached_by(self.typeck.expr_ty(peel_casts(receiver)));
                    for arg in *args {
                        self.reached_by(self.typeck.expr_ty(peel_casts(arg)));
                    }
                }
                _ => {}
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let structs: Vec<(DefId, Ty<'tcx>)> = structs
        .iter()
        .map(|&adt| (adt, tcx.type_of(adt).instantiate_identity()))
        .collect();
    let mut written = FxHashSet::default();
    for owner in tcx.hir_body_owners() {
        let mut writes = Writes {
            tcx,
            typeck: tcx.typeck(owner),
            structs: &structs,
            written: &mut written,
            released: FxHashSet::default(),
        };
        writes.visit_body(tcx.hir_body_owned_by(owner));
    }
    written
}

struct DataFieldStoreCollector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck: &'a TypeckResults<'tcx>,
    oracle: &'a AllocatorOracle<'a>,
    function: LocalDefId,
    body: &'tcx rustc_hir::Body<'tcx>,
    /// The storing body's binding classes, derived on first need for (c).
    classes: Option<FxHashMap<HirId, RootClass>>,
    allocator: &'a mut FxHashMap<(DefId, Symbol), Freshness>,
    refused: &'a mut FxHashSet<(DefId, Symbol)>,
    same_base_only: &'a mut FxHashSet<(DefId, Symbol)>,
    /// (d): `(field, source)` — `field` was stored an offset of `source` read
    /// out of the same base object.
    offsets: &'a mut Vec<((DefId, Symbol), (DefId, Symbol))>,
}

impl<'tcx> DataFieldStoreCollector<'_, 'tcx> {
    /// A DIRECT call of a NAMED allocator: the fn-pointer-field path that
    /// `AllocatorOracle::is_allocator_call` also admits is deliberately not
    /// consulted here, and a contract-backed wrapper is not a proof.
    fn is_direct_named_allocator(&self, value: &Expr<'_>) -> Option<Freshness> {
        let value = peel_casts(value);
        // The C2Rust idiom stores `if size > 0 { alloc(..) } else { null }`.
        // Every arm being an allocation or null still leaves the field holding
        // "null or a block the allocator returned", which is the whole claim,
        // so the walk goes through conditionals and block tails.
        match &value.kind {
            ExprKind::If(_, then, els) => {
                let Some(els) = els else { return None };
                return match (self.is_fresh_or_null(then)?, self.is_fresh_or_null(els)?) {
                    (Some(a), Some(b)) => Some(a.join(b)),
                    (found, None) | (None, found) => found,
                }
                .or(Some(Freshness::Proven));
            }
            ExprKind::Block(block, _) => {
                if !block.stmts.is_empty() {
                    return None;
                }
                return self
                    .is_fresh_or_null(block.expr?)?
                    .or(Some(Freshness::Proven));
            }
            _ => {}
        }
        let ExprKind::Call(callee, _) = &value.kind else {
            return None;
        };
        let did = callee_def_id(callee)?;
        if let Some(freshness) = self.oracle.wrappers.get(&did) {
            return Some(*freshness);
        }
        AllocatorOracle::is_libc_allocator(self.tcx, did).then_some(Freshness::Proven)
    }

    /// `None` = not admissible. `Some(None)` = the null literal, which admits
    /// nothing on its own but refuses nothing either. `Some(Some(f))` = an
    /// allocation with that freshness.
    fn is_fresh_or_null(&self, value: &Expr<'_>) -> Option<Option<Freshness>> {
        if is_null_literal(value) {
            return Some(None);
        }
        self.is_direct_named_allocator(value).map(Some)
    }

    fn record(&mut self, place: &Expr<'_>, value: &Expr<'_>) {
        let ExprKind::Field(base, field) = &peel_casts(place).kind else {
            return;
        };
        let Some(key) = data_field_key(self.tcx, self.typeck, base, field.name) else {
            return;
        };
        if let Some(freshness) = self.is_direct_named_allocator(value) {
            self.allocator
                .entry(key)
                .and_modify(|seen| *seen = seen.join(freshness))
                .or_insert(freshness);
        } else if !is_null_literal(value) && !self.admits_through_local_or_offset(key, base, value)
        {
            self.refused.insert(key);
        }
    }

    /// R579-3 (c) and (d). `base` is the place the field is stored into.
    fn admits_through_local_or_offset(
        &mut self,
        key: (DefId, Symbol),
        base: &Expr<'_>,
        value: &Expr<'_>,
    ) -> bool {
        let (tcx, typeck, body, oracle, function) =
            (self.tcx, self.typeck, self.body, self.oracle, self.function);
        let classes = self
            .classes
            .get_or_insert_with(|| classify_locals(tcx, typeck, body, oracle, function).0);
        let value = peel_casts(value);
        let (base_class, _) = place_provenance(tcx, typeck, classes, base);
        // (c): the base existed at entry, the block was allocated in this body.
        if let Some(local) = resolved_local(value)
            && let Some(RootClass::FreshAlloc(_, freshness)) = classes.get(&local).copied()
            && matches!(base_class, RootClass::EntryStorage(_))
        {
            self.allocator
                .entry(key)
                .and_modify(|seen| *seen = seen.join(freshness))
                .or_insert(freshness);
            self.same_base_only.insert(key);
            return true;
        }
        // (d): an offset of an admitted field of the SAME base object.
        if let ExprKind::MethodCall(segment, receiver, [_], _) = &value.kind
            && matches!(
                segment.ident.name.as_str(),
                "offset" | "add" | "wrapping_add" | "wrapping_offset"
            )
            && let ExprKind::Field(source_base, source_field) = &peel_casts(receiver).kind
            && let Some(source) = data_field_key(tcx, typeck, source_base, source_field.name)
            && let Some(object) = base_class.object_id()
            && place_provenance(tcx, typeck, classes, source_base)
                .0
                .object_id()
                == Some(object)
        {
            self.offsets.push((key, source));
            self.same_base_only.insert(key);
            return true;
        }
        false
    }
}

impl<'tcx> Visitor<'tcx> for DataFieldStoreCollector<'_, 'tcx> {
    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        match &expr.kind {
            ExprKind::Assign(place, value, _) => self.record(place, value),
            // A compound assignment is pointer ARITHMETIC on the field, never
            // an allocation: it refuses whatever the field held.
            ExprKind::AssignOp(_, place, value) => {
                let _ = value;
                if let ExprKind::Field(base, field) = &peel_casts(place).kind
                    && let Some(key) = data_field_key(self.tcx, self.typeck, base, field.name)
                {
                    self.refused.insert(key);
                }
            }
            // A struct literal initialises every field it names.
            ExprKind::Struct(_, fields, rest) => {
                if let ty::Adt(def, args) = self.typeck.expr_ty(expr).kind()
                    && !def.is_union()
                {
                    for field in *fields {
                        let Some(declared) = def
                            .all_fields()
                            .find(|candidate| candidate.name == field.ident.name)
                            .map(|candidate| candidate.ty(self.tcx, args))
                        else {
                            continue;
                        };
                        if !matches!(declared.kind(), ty::RawPtr(..)) {
                            continue;
                        }
                        let key = (def.did(), field.ident.name);
                        if let Some(freshness) = self.is_direct_named_allocator(field.expr) {
                            self.allocator
                                .entry(key)
                                .and_modify(|seen| *seen = seen.join(freshness))
                                .or_insert(freshness);
                        } else if !is_null_literal(field.expr) {
                            self.refused.insert(key);
                        }
                    }
                    // `..base` copies every field it fills in from elsewhere.
                    if !matches!(rest, rustc_hir::StructTailExpr::None) {
                        for candidate in def.all_fields() {
                            if matches!(candidate.ty(self.tcx, args).kind(), ty::RawPtr(..)) {
                                self.refused.insert((def.did(), candidate.name));
                            }
                        }
                    }
                }
            }
            // The field's own ADDRESS escapes: whatever holds that address may
            // store anything through it, so the closed world stops here.
            ExprKind::AddrOf(_, _, operand) => {
                if let ExprKind::Field(base, field) = &peel_casts(operand).kind
                    && let Some(key) = data_field_key(self.tcx, self.typeck, base, field.name)
                {
                    self.refused.insert(key);
                }
            }
            _ => {}
        }
        let _ = self.function;
        intravisit::walk_expr(self, expr);
    }
}

fn adt_field_key<'tcx>(
    tcx: TyCtxt<'tcx>,
    typeck: &TypeckResults<'tcx>,
    base: &Expr<'_>,
    field: Symbol,
) -> Option<(DefId, Symbol)> {
    let ty::Adt(def, args) = typeck.expr_ty_adjusted(base).peel_refs().kind() else {
        return None;
    };
    if def.is_union() {
        return None;
    }
    let declared = def
        .all_fields()
        .find(|candidate| candidate.name == field)?
        .ty(tcx, args);
    is_fn_pointer(declared).then_some((def.did(), field))
}

/// A function pointer, or C2Rust's `Option<unsafe extern "C" fn(..) -> ..>`.
fn is_fn_pointer(ty: Ty<'_>) -> bool {
    match ty.kind() {
        ty::FnPtr(..) => true,
        ty::Adt(def, args) => {
            def.is_enum()
                && args.types().count() == 1
                && args
                    .types()
                    .all(|inner| matches!(inner.kind(), ty::FnPtr(..)))
        }
        _ => false,
    }
}

/// Every store into a function-pointer field, with whether it stores a known
/// allocator. An assignment whose value this read cannot resolve to a function
/// item records `false`, which refuses the field.
struct FieldStoreCollector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck: &'tcx TypeckResults<'tcx>,
    oracle: &'a AllocatorOracle<'a>,
    assignments: &'a mut FxHashMap<(DefId, Symbol), Vec<FieldStore>>,
}

impl<'tcx> FieldStoreCollector<'_, 'tcx> {
    /// What `value` (a cast, or `Some(..)` of one) stores into the field.
    fn stores_allocator(&self, value: &Expr<'_>) -> FieldStore {
        let value = peel_casts(value);
        if let ExprKind::Call(callee, args) = &value.kind
            && args.len() == 1
            && matches!(&callee.kind, ExprKind::Path(QPath::Resolved(_, path))
                if matches!(path.res, Res::Def(DefKind::Ctor(..), _)))
        {
            return self.stores_allocator(&args[0]);
        }
        if is_null_literal(value) {
            // `None` / a null function pointer is never called.
            return FieldStore::Allocator(Freshness::Proven);
        }
        let ExprKind::Path(QPath::Resolved(_, path)) = &peel_casts(value).kind else {
            return FieldStore::Unresolved;
        };
        let Res::Def(DefKind::Fn, did) = path.res else {
            return FieldStore::Unresolved;
        };
        if let Some(freshness) = self.oracle.wrappers.get(&did) {
            FieldStore::Allocator(*freshness)
        } else if AllocatorOracle::is_libc_allocator(self.tcx, did) {
            FieldStore::Allocator(Freshness::Proven)
        } else {
            FieldStore::NotAnAllocator
        }
    }

    fn record(&mut self, place: &Expr<'_>, value: &Expr<'_>) {
        let ExprKind::Field(base, field) = &place.kind else {
            return;
        };
        let Some(key) = adt_field_key(self.tcx, self.typeck, base, field.name) else {
            return;
        };
        let store = self.stores_allocator(value);
        self.assignments.entry(key).or_default().push(store);
    }
}

impl<'tcx> Visitor<'tcx> for FieldStoreCollector<'_, 'tcx> {
    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        match &expr.kind {
            ExprKind::Assign(place, value, _) | ExprKind::AssignOp(_, place, value) => {
                self.record(place, value);
            }
            ExprKind::Struct(_, fields, _) => {
                if let ty::Adt(def, args) = self.typeck.expr_ty(expr).kind()
                    && !def.is_union()
                {
                    for field in *fields {
                        if let Some(declared) = def
                            .all_fields()
                            .find(|candidate| candidate.name == field.ident.name)
                            .map(|candidate| candidate.ty(self.tcx, args))
                            && is_fn_pointer(declared)
                        {
                            let store = self.stores_allocator(field.expr);
                            self.assignments
                                .entry((def.did(), field.ident.name))
                                .or_default()
                                .push(store);
                        }
                    }
                }
            }
            _ => {}
        }
        intravisit::walk_expr(self, expr);
    }
}

struct ReturnCollector<'tcx> {
    returns: Vec<&'tcx Expr<'tcx>>,
}

impl<'tcx> Visitor<'tcx> for ReturnCollector<'tcx> {
    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if let ExprKind::Ret(Some(value)) = &expr.kind {
            self.returns.push(value);
        }
        intravisit::walk_expr(self, expr);
    }
}

#[derive(Default)]
struct LocalFacts {
    is_param: bool,
    is_pointer: bool,
    /// Every value assigned to the binding: the `let` initializer and each
    /// `binding = rhs`. `None` marks an assignment whose RHS is unclassified.
    assignments: Vec<AssignKind>,
    address_taken: bool,
    /// One tag per `AssignKind::Other` source, in order: what the RHS was.
    /// Probe-only (R478-5); no rule reads it.
    other_shapes: Vec<&'static str>,
    /// R513-3: the place this binding's `let` INITIALIZER took the address of
    /// (`let br = &mut (*s).br` -> `(*s).br`). Only the initializer sets it, so
    /// a binding with exactly one assignment has no window in which it holds
    /// anything else; `prefixes` below applies the other two conjuncts.
    view_prefix: Option<PlacePath>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AssignKind {
    Null,
    Allocator(Freshness),
    /// The value derives its ADDRESS from one place, whose root binding this
    /// is: `&mut (*b).f`, `b.offset(k)`, `arr.as_mut_ptr()`, a cast of one of
    /// those, or the bare local `b`. Every such form addresses the same object
    /// as `b` on a UB-free input (§28: pointer arithmetic leaves its object
    /// only as UB), so the local's root IS `b`'s root.
    Derived(HirId),
    Other,
}

/// R478-5, the probe column: WHY a binding's root came out `Unknown`. It is
/// written at derive time and read only by `#[cfg(test)]` sizing code — no rule
/// consults it, so the column cannot move a decision. The ban is mechanized by
/// `w6p_the_probe_column_is_never_read_by_a_rule`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum UnknownWhy {
    /// The root is not `Unknown` at all.
    Known,
    /// The binding's own address escapes, so its value is not one provenance.
    AddressTaken,
    /// More than one source, or a source that is not a derivation of one place.
    MixedSources,
    /// Every unclassified source is a call result (report 019's rule 1: a
    /// callee whose returns are all views of one formal would give these a
    /// root).
    CallResult,
    /// A pointer VALUE loaded out of a field (report 020's wall: the loaded
    /// pointer's pointee is not the field slot).
    FieldRead,
    /// A pointer value read out of an index projection.
    IndexRead,
    /// A local with no allocator source and no single derivation.
    NoFreshSource,
    /// The argument is the null literal.
    NullLiteral,
    /// The argument names a binding whose root IS known, but the argument's own
    /// expression shape is one `argument_provenance` does not carry a root
    /// through (`x.as_mut_ptr()` on a non-array, an unrecognised method).
    ShapeUnsupported,
    /// The argument expression names no binding at all; the tag is the HIR
    /// shape that stopped the walk, so the residue is never opaque.
    NotALocal(&'static str),
}

impl UnknownWhy {
    fn key(self) -> &'static str {
        match self {
            Self::Known => "known",
            Self::AddressTaken => "address-taken",
            Self::MixedSources => "mixed-sources",
            Self::CallResult => "call-result",
            Self::FieldRead => "field-read",
            Self::IndexRead => "index-read",
            Self::NoFreshSource => "no-fresh-source",
            Self::NullLiteral => "null-literal",
            Self::ShapeUnsupported => "shape-unsupported",
            Self::NotALocal(shape) => shape,
        }
    }
}

fn classify_locals<'tcx>(
    tcx: TyCtxt<'tcx>,
    typeck: &TypeckResults<'tcx>,
    body: &'tcx rustc_hir::Body<'tcx>,
    allocators: &AllocatorOracle<'_>,
    function: LocalDefId,
) -> (
    FxHashMap<HirId, RootClass>,
    FxHashMap<HirId, UnknownWhy>,
    FxHashMap<HirId, PlacePath>,
) {
    let mut facts: FxHashMap<HirId, LocalFacts> = FxHashMap::default();
    for param in body.params {
        if let PatKind::Binding(_, hir_id, ..) = param.pat.kind {
            let ty = typeck.node_type(hir_id);
            facts.insert(
                hir_id,
                LocalFacts {
                    is_param: true,
                    is_pointer: matches!(ty.kind(), ty::RawPtr(..)),
                    assignments: Vec::new(),
                    address_taken: false,
                    other_shapes: Vec::new(),
                    view_prefix: None,
                },
            );
        }
    }
    let mut collector = LocalCollector {
        tcx,
        typeck,
        allocators,
        function,
        facts: &mut facts,
    };
    collector.visit_body(body);

    let mut classes: FxHashMap<HirId, RootClass> = facts
        .iter()
        .map(|(&hir_id, fact)| {
            let class =
                if fact.is_pointer {
                    if fact.address_taken {
                        RootClass::Unknown
                    } else if fact.is_param {
                        // R460-8: a parameter that only walks WITHIN its own object
                        // (`p = p.offset(1)`, C2Rust's cursor idiom) still names
                        // the storage it entered with; any other assignment makes
                        // its value another object's and is resolved below.
                        if fact.assignments.iter().all(
                            |kind| matches!(kind, AssignKind::Derived(base) if *base == hir_id),
                        ) {
                            RootClass::EntryStorage(hir_id)
                        } else {
                            RootClass::Unknown
                        }
                    } else {
                        let all_fresh = fact.assignments.iter().all(|kind| {
                            matches!(kind, AssignKind::Null | AssignKind::Allocator(_))
                        });
                        let freshness = fact
                            .assignments
                            .iter()
                            .filter_map(|kind| match kind {
                                AssignKind::Allocator(freshness) => Some(*freshness),
                                _ => None,
                            })
                            .reduce(Freshness::join);
                        match (all_fresh, freshness) {
                            (true, Some(freshness)) => RootClass::FreshAlloc(hir_id, freshness),
                            _ => RootClass::Unknown,
                        }
                    }
                } else {
                    // A non-pointer binding IS an object on the caller's stack:
                    // every view into it (`&mut x`, `x.as_mut_ptr()`, `&mut x.f`)
                    // addresses that object.
                    RootClass::StackObject(hir_id)
                };
            (hir_id, class)
        })
        .collect();

    // R460-8, the derived-root rule. A binding still `Unknown` whose every
    // assignment is a null or a derivation of ONE other binding names the same
    // object as that binding, so it inherits its class. Two different sources
    // keep it `Unknown` — this is single derivation, not any derivation — and
    // a derivation of ITSELF carries no information (the cursor case above).
    // It only ever replaces `Unknown` with a class the rules already judge, so
    // no certificate widens; the fixpoint is bounded and a cycle stays
    // `Unknown`.
    for _ in 0..8 {
        let mut changed = false;
        for (&hir_id, fact) in &facts {
            if !fact.is_pointer
                || fact.address_taken
                || classes.get(&hir_id).copied() != Some(RootClass::Unknown)
            {
                continue;
            }
            let mut bases = FxHashSet::default();
            let mut derived_only = true;
            for kind in &fact.assignments {
                match kind {
                    AssignKind::Null => {}
                    AssignKind::Derived(base) if *base == hir_id => {}
                    AssignKind::Derived(base) => {
                        bases.insert(*base);
                    }
                    _ => {
                        derived_only = false;
                        break;
                    }
                }
            }
            if !derived_only || bases.len() != 1 {
                continue;
            }
            let base = bases.into_iter().next().expect("one base");
            let inherited = classes.get(&base).copied().unwrap_or(RootClass::Unknown);
            if inherited != RootClass::Unknown {
                classes.insert(hir_id, inherited);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    // R641-9 (the fold), after R460-8's single derivation: a pointer local still
    // `Unknown` — not a parameter, its own address never taken — whose every
    // assignment is null, an allocator result, or a derivation of a binding
    // that is fresh or already such a local holds only blocks allocated during
    // this activation. A least fixpoint: a cycle of derivations with no
    // allocation under it stays `Unknown`, and so does a local that is only
    // ever null.
    for _ in 0..8 {
        let mut changed = false;
        for (&hir_id, fact) in &facts {
            if !fact.is_pointer
                || fact.is_param
                || fact.address_taken
                || classes.get(&hir_id).copied() != Some(RootClass::Unknown)
            {
                continue;
            }
            let mut freshness: Option<Freshness> = None;
            let mut allocated = true;
            for kind in &fact.assignments {
                let source = match kind {
                    AssignKind::Null => continue,
                    AssignKind::Derived(base) if *base == hir_id => continue,
                    AssignKind::Allocator(source) => *source,
                    AssignKind::Derived(base) => match classes.get(base).copied() {
                        Some(
                            RootClass::FreshAlloc(_, source) | RootClass::AllocatedHere(_, source),
                        ) => source,
                        _ => {
                            allocated = false;
                            break;
                        }
                    },
                    AssignKind::Other => {
                        allocated = false;
                        break;
                    }
                };
                freshness = Some(freshness.map_or(source, |acc| acc.join(source)));
            }
            if allocated && let Some(freshness) = freshness {
                classes.insert(hir_id, RootClass::AllocatedHere(hir_id, freshness));
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    // R478-5: the reason is read AFTER the fixpoint, so a binding the fixpoint
    // rescued reads `Known` and only the residue is attributed.
    let why = facts
        .iter()
        .map(|(&hir_id, fact)| {
            #[cfg(test)]
            if std::env::var_os("W6P_DUMP_MIXED").is_some()
                && classes.get(&hir_id).copied() == Some(RootClass::Unknown)
                && fact.is_pointer
                && !fact.address_taken
            {
                let kinds: Vec<&str> = fact
                    .assignments
                    .iter()
                    .map(|kind| match kind {
                        AssignKind::Null => "null",
                        AssignKind::Allocator(_) => "alloc",
                        AssignKind::Derived(_) => "derived",
                        AssignKind::Other => "other",
                    })
                    .collect();
                println!(
                    "W6P_MIXED\t{}\t{}\t{}",
                    kinds.join(","),
                    fact.other_shapes.join(","),
                    if fact.is_param { "param" } else { "local" }
                );
            }
            let why = if classes.get(&hir_id).copied() != Some(RootClass::Unknown) {
                UnknownWhy::Known
            } else if fact.address_taken {
                UnknownWhy::AddressTaken
            } else if !fact.other_shapes.is_empty()
                && fact.other_shapes.iter().all(|shape| *shape == "call")
            {
                UnknownWhy::CallResult
            } else if fact.other_shapes.iter().any(|shape| *shape == "field") {
                UnknownWhy::FieldRead
            } else if fact.other_shapes.iter().any(|shape| *shape == "index") {
                UnknownWhy::IndexRead
            } else if fact.assignments.is_empty() {
                UnknownWhy::NoFreshSource
            } else {
                UnknownWhy::MixedSources
            };
            (hir_id, why)
        })
        .collect();

    // R513-3, the three conjuncts. A binding whose `let` initializer took the
    // address of a place (1) IS that place for its whole live range provided
    // (2) nothing else is ever assigned to it and (3) its own address is never
    // taken, so no callee can retarget it. Then a path through its pointee is a
    // path through the place, and folding the prefix back in restores the field
    // projections the binding consumed. Parameters are excluded structurally:
    // they have no `let`, so they never carry a prefix.
    let prefixes: FxHashMap<HirId, PlacePath> = facts
        .iter()
        .filter(|(_, fact)| fact.assignments.len() == 1 && !fact.address_taken)
        .filter_map(|(&hir_id, fact)| Some((hir_id, fact.view_prefix.clone()?)))
        .collect();
    (classes, why, prefixes)
}

/// R579-3 (ii), the carry. A pointer local still `Unknown` takes the root of an
/// admitted field it reads — `data = (*s).ringbuffer_.buffer_` names the block
/// that field holds, separated from `*s` — when:
///
/// * it is declared by a `let` with a plain binding and is not a parameter
///   (a parameter's entry value is another source nobody reads here);
/// * its address is never taken, so no callee can retarget it;
/// * every assignment, the initializer included, is null or a read `X.F` of
///   ONE admitted `F` out of ONE base object.
///
/// R601-4 (G4): a call of a [`field_getters`] callee is the same read one call
/// boundary away — `storage_0 = GetBrotliStorage(s, n)` reads `(*s).storage_` —
/// and its base object is the root of the argument at the getter's formal.
///
/// Two fields, two bases, or any other source leave it `Unknown`.
fn carry_fresh_field_reads<'tcx>(
    tcx: TyCtxt<'tcx>,
    typeck: &TypeckResults<'tcx>,
    body: &'tcx rustc_hir::Body<'tcx>,
    classes: &mut FxHashMap<HirId, RootClass>,
    fresh_fields: &FxHashMap<(DefId, Symbol), FreshFieldFact>,
    getters: &FxHashMap<DefId, (usize, (DefId, Symbol))>,
) {
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Reads {
        /// Only null so far.
        Null,
        One {
            key: (DefId, Symbol),
            base: HirId,
        },
        Refused,
    }
    struct Scan<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        typeck: &'a TypeckResults<'tcx>,
        classes: &'a FxHashMap<HirId, RootClass>,
        fresh_fields: &'a FxHashMap<(DefId, Symbol), FreshFieldFact>,
        getters: &'a FxHashMap<DefId, (usize, (DefId, Symbol))>,
        declared: FxHashSet<HirId>,
        reads: FxHashMap<HirId, Reads>,
    }
    impl Scan<'_, '_> {
        fn assign(&mut self, local: HirId, value: &Expr<'_>) {
            let value = peel_casts(value);
            let next = if is_null_literal(value) {
                Reads::Null
            } else {
                match &value.kind {
                    ExprKind::Field(base, field) => {
                        data_field_key(self.tcx, self.typeck, base, field.name)
                            .filter(|key| self.fresh_fields.contains_key(key))
                            .and_then(|key| {
                                let (class, _) =
                                    place_provenance(self.tcx, self.typeck, self.classes, base);
                                Some(Reads::One {
                                    key,
                                    base: class.object_id()?,
                                })
                            })
                            .unwrap_or(Reads::Refused)
                    }
                    ExprKind::Call(callee, args) => callee_def_id(callee)
                        .and_then(|did| self.getters.get(&did).copied())
                        .and_then(|(position, key)| {
                            let (class, _) = argument_provenance(
                                self.tcx,
                                self.typeck,
                                self.classes,
                                args.get(position)?,
                            );
                            Some(Reads::One {
                                key,
                                base: class.object_id()?,
                            })
                        })
                        .unwrap_or(Reads::Refused),
                    _ => Reads::Refused,
                }
            };
            let joined = match (self.reads.get(&local).copied(), next) {
                (None | Some(Reads::Null), next) => next,
                (Some(current), Reads::Null) => current,
                (Some(current), next) if current == next => current,
                _ => Reads::Refused,
            };
            self.reads.insert(local, joined);
        }
    }
    impl<'tcx> Visitor<'tcx> for Scan<'_, 'tcx> {
        fn visit_local(&mut self, local: &'tcx rustc_hir::LetStmt<'tcx>) {
            if let PatKind::Binding(_, hir_id, _, None) = local.pat.kind {
                self.declared.insert(hir_id);
                if let Some(init) = local.init {
                    self.assign(hir_id, init);
                }
            }
            intravisit::walk_local(self, local);
        }

        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            match &expr.kind {
                ExprKind::Assign(place, value, _) => {
                    if let Some(local) = resolved_local(place) {
                        self.assign(local, value);
                    }
                }
                // A compound assignment, or the binding's own address taken:
                // its value is no longer one read.
                ExprKind::AssignOp(_, place, _) | ExprKind::AddrOf(_, _, place) => {
                    if let Some(local) = resolved_local(peel_casts(place)) {
                        self.reads.insert(local, Reads::Refused);
                    }
                }
                _ => {}
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let mut scan = Scan {
        tcx,
        typeck,
        classes,
        fresh_fields,
        getters,
        declared: FxHashSet::default(),
        reads: FxHashMap::default(),
    };
    scan.visit_body(body);
    let (declared, reads) = (scan.declared, scan.reads);
    for (local, reads) in reads {
        let Reads::One { key, base } = reads else {
            continue;
        };
        // `declared` holds only `let`-bound plain bindings, so a parameter —
        // whose entry value is a source this scan never sees — is out.
        if !declared.contains(&local) || classes.get(&local).copied() != Some(RootClass::Unknown) {
            continue;
        }
        let FreshFieldFact {
            freshness,
            same_base_only,
            via_offset,
        } = fresh_fields[&key];
        classes.insert(
            local,
            RootClass::FreshField {
                adt: key.0,
                field: key.1,
                base,
                freshness,
                same_base_only,
                via_offset,
            },
        );
    }
}

/// R601-4 (G4): the callees whose EVERY return is the null literal or a read
/// `(*f).F` of ONE admitted field `F` out of the pointee of ONE formal `f` —
/// brotli's `GetBrotliStorage`, `return (*s).storage_`. Such a call hands back
/// the block that field holds, exactly as a direct read would, so the carry
/// keys the caller's local to the root of the argument at `f`.
///
/// The formal must still name the storage it entered with (`EntryStorage`), or
/// the object the field was read out of is not the argument's. Any other return
/// — a view of the formal's own storage (`GetHashTable`'s `small_table_`), a
/// second field, the same field of a second formal — refuses the callee: the
/// result may then be that other storage, so no single block names it.
fn field_getters(
    tcx: TyCtxt<'_>,
    functions: &FxHashSet<LocalDefId>,
    oracle: &AllocatorOracle<'_>,
    fresh_fields: &FxHashMap<(DefId, Symbol), FreshFieldFact>,
) -> FxHashMap<DefId, (usize, (DefId, Symbol))> {
    let mut getters = FxHashMap::default();
    for &function in functions {
        let Some(body_id) = tcx.hir_node_by_def_id(function).body_id() else {
            continue;
        };
        let output = tcx.fn_sig(function).skip_binder().skip_binder().output();
        if !matches!(output.kind(), ty::RawPtr(..)) {
            continue;
        }
        let body = tcx.hir_body(body_id);
        let mut returns = ReturnCollector {
            returns: Vec::new(),
        };
        returns.visit_body(body);
        if let ExprKind::Block(block, _) = &body.value.kind
            && let Some(tail) = block.expr
        {
            returns.returns.push(tail);
        }
        let params: Vec<HirId> = body
            .params
            .iter()
            .filter_map(|param| match param.pat.kind {
                PatKind::Binding(_, hir_id, ..) => Some(hir_id),
                _ => None,
            })
            .collect();
        let typeck = tcx.typeck(function);
        let (classes, _why, _prefixes) = classify_locals(tcx, typeck, body, oracle, function);
        let mut read = None;
        let mut every = true;
        for expr in &returns.returns {
            if is_null_literal(expr) {
                continue;
            }
            let this = match &peel_casts(expr).kind {
                ExprKind::Field(base, field) => data_field_key(tcx, typeck, base, field.name)
                    .filter(|key| fresh_fields.contains_key(key))
                    .and_then(|key| {
                        let (class, _) = place_provenance(tcx, typeck, &classes, base);
                        let RootClass::EntryStorage(formal) = class else {
                            return None;
                        };
                        Some((params.iter().position(|p| *p == formal)?, key))
                    }),
                _ => None,
            };
            match (read, this) {
                (None, Some(this)) => read = Some(this),
                (Some(seen), Some(this)) if seen == this => {}
                _ => {
                    every = false;
                    break;
                }
            }
        }
        if let Some(read) = read.filter(|_| every) {
            getters.insert(function.to_def_id(), read);
        }
    }
    getters
}

/// R513-3. Replace a path rooted at a single-definition view local by the path
/// it is a view OF: `*br` with `br = &mut (*s).br` is `(*s).br`. Only a path
/// through the local's POINTEE folds — a path at the local's own slot names its
/// storage, not the place it points at. Bounded, so a cycle cannot spin.
fn fold_place_prefix(path: PlacePath, prefixes: &FxHashMap<HirId, PlacePath>) -> PlacePath {
    let mut path = path;
    for _ in 0..8 {
        if !path.deref_root {
            return path;
        }
        let Some(prefix) = prefixes.get(&path.root) else {
            return path;
        };
        let mut projections = prefix.projections.clone();
        projections.extend(path.projections);
        path = PlacePath {
            root: prefix.root,
            deref_root: prefix.deref_root,
            projections,
            retyped: path.retyped || prefix.retyped,
        };
    }
    path
}

/// R478-5: what an unclassified RHS was, for the probe column only.
fn rhs_shape(rhs: &Expr<'_>) -> &'static str {
    match &peel_casts(rhs).kind {
        ExprKind::Call(..) => "call",
        ExprKind::MethodCall(..) => "method",
        ExprKind::Field(..) => "field",
        ExprKind::Index(..) => "index",
        ExprKind::If(..) => "if",
        ExprKind::Block(..) => "block",
        ExprKind::Binary(..) => "binary",
        ExprKind::Lit(..) => "literal",
        ExprKind::Unary(..) => "unary",
        ExprKind::Path(..) => "path",
        ExprKind::AddrOf(..) => "addr-of",
        ExprKind::Struct(..) => "struct",
        _ => "other",
    }
}

struct LocalCollector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck: &'a TypeckResults<'tcx>,
    allocators: &'a AllocatorOracle<'a>,
    function: LocalDefId,
    facts: &'a mut FxHashMap<HirId, LocalFacts>,
}

impl<'a, 'tcx> LocalCollector<'a, 'tcx> {
    /// R513-3: the PLACE an initializer takes the address of. `&mut (*s).br`,
    /// `&(*s).br` and the raw `&raw mut (*s).br` all give `(*s).br`; anything
    /// else gives nothing, so a
    /// binding initialized from a call, a cast of an integer or another
    /// pointer's VALUE records no prefix and folds nowhere.
    fn address_of_place(&self, rhs: &Expr<'_>) -> Option<PlacePath> {
        let (rhs, outer) = peel_casts_retyping(self.typeck, rhs);
        let ExprKind::AddrOf(_, _, operand) = &rhs.kind else {
            return None;
        };
        let (operand, inner) = peel_casts_retyping(self.typeck, operand);
        let (_, place) = place_provenance(self.tcx, self.typeck, &FxHashMap::default(), operand);
        // R550-2: `let br = &mut (*s).x as *mut U` views `(*s).x` as a `U`.
        retyped_by(place, outer || inner)
    }

    /// R482-4(3): the root binding of the argument a view-of-formal call hands
    /// back.
    fn view_call_base(&self, rhs: &Expr<'_>) -> Option<HirId> {
        let ExprKind::Call(callee, args) = &peel_casts(rhs).kind else {
            return None;
        };
        let did = callee_def_id(callee)?;
        let index = *self.allocators.views.get(&did)?;
        derivation_base(self.typeck, args.get(index)?)
    }

    /// R485-4(e): every arm of a conditional allocates or is null, and at
    /// least one allocates. Mirrors the allocator-field admission's walk; a
    /// conditional is only as strong as its weakest allocating arm.
    ///
    /// `None` refuses. `Some(None)` is an arm that allocates nothing and names
    /// nothing — the null literal. `Some(Some(f))` is an allocation.
    fn conditional_allocator_arm(&self, value: &Expr<'_>) -> Option<Option<Freshness>> {
        let value = peel_casts(value);
        match &value.kind {
            ExprKind::If(_, then, els) => {
                let els = (*els)?;
                match (
                    self.conditional_allocator_arm(then)?,
                    self.conditional_allocator_arm(els)?,
                ) {
                    (Some(a), Some(b)) => Some(Some(a.join(b))),
                    (found, None) | (None, found) => Some(found),
                }
            }
            ExprKind::Block(block, _) => {
                if !block.stmts.is_empty() {
                    return None;
                }
                self.conditional_allocator_arm(block.expr?)
            }
            // The null check is at the LEAF, after the block descent: an arm
            // written `else { 0 as *mut T }` is a block around a null literal,
            // and checking it before descending refuses the whole conditional.
            _ if is_null_literal(value) => Some(None),
            _ => self
                .allocators
                .is_allocator_call(self.tcx, self.function, value)
                .map(Some),
        }
    }

    /// The conditional as a whole: admitted only when it is a CONDITIONAL (a
    /// bare allocator call is already handled ahead of this) and at least one
    /// arm allocates. R603-4 (G5): a statement-less BLOCK around an allocator
    /// call is that allocation too — its value is the call's result
    /// (`storage = { BrotliAllocate(..) as *mut u8 }`); the arm walk refuses a
    /// block with statements.
    fn conditional_allocator(&self, value: &Expr<'_>) -> Option<Freshness> {
        let value = peel_casts(value);
        if !matches!(value.kind, ExprKind::If(..) | ExprKind::Block(..)) {
            return None;
        }
        self.conditional_allocator_arm(value)?
    }

    fn assign_kind(&self, rhs: &Expr<'_>) -> AssignKind {
        if is_null_literal(rhs) {
            AssignKind::Null
        } else if let Some(freshness) =
            self.allocators
                .is_allocator_call(self.tcx, self.function, rhs)
        {
            AssignKind::Allocator(freshness)
        } else if let Some(freshness) = self.conditional_allocator(rhs) {
            // R485-4(e), the shape the corpus actually has: null or a block the
            // allocator returned is one fresh object either way — the claim
            // already ratified for the allocator FIELD at `f065993a2`.
            AssignKind::Allocator(freshness)
        } else if let Some(Some(base)) = conditional_base(self.typeck, rhs) {
            // R485-4(e): every arm walks within one object, so the value does.
            AssignKind::Derived(base)
        } else if let Some(base) = self.view_call_base(rhs) {
            // R482-4(3): the call hands back the argument's own object.
            AssignKind::Derived(base)
        } else if let Some(base) = derivation_base(self.typeck, rhs) {
            AssignKind::Derived(base)
        } else {
            AssignKind::Other
        }
    }
}

/// R485-4(e): the base of a CONDITIONAL store, if every arm derives from one.
///
/// `None` refuses the value. `Some(None)` is an arm that names no object — the
/// null literal — which constrains nothing and lets its siblings govern, the
/// same tolerance `classify_locals` already gives an `AssignKind::Null` beside
/// a derivation. `Some(Some(base))` is one named object for the whole value.
///
/// An arm that allocates is deliberately refused: "a fresh block or a view of
/// `base`" is two objects. That is the one place this walk differs from the
/// allocator-field admission it is modelled on, whose claim is the weaker
/// "null or fresh".
fn conditional_base<'tcx>(typeck: &TypeckResults<'tcx>, value: &Expr<'_>) -> Option<Option<HirId>> {
    let value = peel_casts(value);
    #[cfg(test)]
    if std::env::var_os("W6P_DUMP_COND").is_some()
        && let ExprKind::If(_, then, els) = &value.kind
    {
        let arm = |e: &Expr<'_>| -> &'static str {
            let e = peel_casts(e);
            match &e.kind {
                ExprKind::Block(b, _) if !b.stmts.is_empty() => "block-stmts",
                ExprKind::Block(b, _) if b.expr.is_none() => "block-empty",
                _ if is_null_literal(e) => "null",
                ExprKind::Call(..) => "call",
                ExprKind::Field(..) => "field",
                ExprKind::Index(..) => "index",
                ExprKind::If(..) => "if",
                _ if derivation_base(typeck, e).is_some() => "derived",
                _ => "other",
            }
        };
        let inner = |e: &Expr<'_>| -> &'static str {
            let e = peel_casts(e);
            match &e.kind {
                ExprKind::Block(b, _) if b.stmts.is_empty() => b.expr.map_or("block-empty", arm),
                _ => arm(e),
            }
        };
        println!(
            "W6P_COND\t{}\t{}",
            inner(then),
            els.map_or("no-else", inner)
        );
    }
    match &value.kind {
        ExprKind::If(_, then, els) => {
            // An `if` with no `else` leaves the local holding whatever it held
            // before, which this walk cannot see.
            let els = (*els)?;
            let then = conditional_base(typeck, then)?;
            let els = conditional_base(typeck, els)?;
            match (then, els) {
                (Some(a), Some(b)) if a == b => Some(Some(a)),
                (Some(_), Some(_)) => None,
                (found, None) | (None, found) => Some(found),
            }
        }
        ExprKind::Block(block, _) => {
            if !block.stmts.is_empty() {
                return None;
            }
            conditional_base(typeck, block.expr?)
        }
        _ if is_null_literal(value) => Some(None),
        _ => derivation_base(typeck, value).map(Some),
    }
}

/// R492-3, guard (2): the formals a callee's own body takes a MUTABLE view of,
/// however little it then does with it — `&mut *p`, `p.as_mut_ptr()`, a cast to
/// `*mut`, or any `&mut` derivation rooted at the formal. The mutability
/// analysis answers "is anything written through this"; this answers "does a
/// mutable view of it exist at all", which is the question `&T` beside `&T`
/// actually needs, and one such view anywhere kills the licence for every pair
/// the formal is in.
fn mutably_reborrowed_formals(
    tcx: TyCtxt<'_>,
    functions: &[LocalDefId],
) -> FxHashSet<(LocalDefId, usize)> {
    let mut out = FxHashSet::default();
    for &function in functions {
        let Some(body_id) = tcx.hir_node_by_def_id(function).body_id() else {
            continue;
        };
        let body = tcx.hir_body(body_id);
        let params: Vec<HirId> = body
            .params
            .iter()
            .filter_map(|param| match param.pat.kind {
                PatKind::Binding(_, hir_id, ..) => Some(hir_id),
                _ => None,
            })
            .collect();
        let mut visitor = MutableReborrows {
            typeck: tcx.typeck(function),
            params: &params,
            function,
            out: &mut out,
        };
        visitor.visit_body(body);
    }
    out
}

struct MutableReborrows<'a, 'tcx> {
    typeck: &'a TypeckResults<'tcx>,
    params: &'a [HirId],
    function: LocalDefId,
    out: &'a mut FxHashSet<(LocalDefId, usize)>,
}

impl MutableReborrows<'_, '_> {
    fn mark(&mut self, expr: &Expr<'_>) {
        // Walk the derivation back to a binding: `(*p).f`, `p.offset(k)` and a
        // cast all address the same object as `p`.
        if let Some(base) = derivation_base(self.typeck, expr)
            && let Some(index) = self.params.iter().position(|p| *p == base)
        {
            self.out.insert((self.function, index));
        }
    }
}

impl<'tcx> Visitor<'tcx> for MutableReborrows<'_, 'tcx> {
    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        match &expr.kind {
            ExprKind::AddrOf(_, rustc_middle::mir::Mutability::Mut, operand) => {
                self.mark(peel_casts(operand));
            }
            ExprKind::MethodCall(segment, receiver, _, _)
                if segment.ident.name.as_str() == "as_mut_ptr" =>
            {
                self.mark(peel_casts(receiver));
            }
            // A cast that turns a shared raw pointer into a mutable one is a
            // mutable view even though nothing is written through it yet.
            ExprKind::Cast(inner, _)
                if matches!(
                    self.typeck.expr_ty(expr).kind(),
                    ty::RawPtr(_, rustc_middle::mir::Mutability::Mut)
                ) =>
            {
                self.mark(peel_casts(inner));
            }
            _ => {}
        }
        intravisit::walk_expr(self, expr);
    }
}

/// R493-3: a side of a `root-is-not-a-caller-formal` decline, tagged with
/// whether THIS side is the one `formal_of` refused.
#[cfg(test)]
fn describe_side(resolved: Option<usize>, class: RootClass) -> String {
    format!(
        "{}{}",
        describe_class(class),
        if resolved.is_some() { "" } else { "-FAILED" }
    )
}

/// R492-3, for the decline table only.
#[cfg(test)]
fn describe_class(class: RootClass) -> &'static str {
    match class {
        RootClass::FreshAlloc(..) => "fresh",
        RootClass::StackObject(_) => "stack",
        RootClass::EntryStorage(_) => "entry-but-not-a-formal",
        RootClass::FreshField { .. } => "fresh-field",
        RootClass::Static(_) => "static",
        RootClass::AllocatedHere(..) => "allocated-here",
        RootClass::Unknown => "unknown",
    }
}

/// R482-4(4): the `DefId` of a `static` item named by a path.
fn resolved_static(expr: &Expr<'_>) -> Option<DefId> {
    let ExprKind::Path(QPath::Resolved(_, path)) = &peel_casts(expr).kind else {
        return None;
    };
    match path.res {
        Res::Def(rustc_hir::def::DefKind::Static { .. }, did) => Some(did),
        _ => None,
    }
}

fn resolved_local(expr: &Expr<'_>) -> Option<HirId> {
    let ExprKind::Path(QPath::Resolved(_, path)) = &expr.kind else {
        return None;
    };
    match path.res {
        Res::Local(hir_id) => Some(hir_id),
        _ => None,
    }
}

impl<'tcx> Visitor<'tcx> for LocalCollector<'_, 'tcx> {
    fn visit_stmt(&mut self, stmt: &'tcx rustc_hir::Stmt<'tcx>) {
        if let StmtKind::Let(local) = stmt.kind
            && let PatKind::Binding(_, hir_id, ..) = local.pat.kind
        {
            let ty = self.typeck.node_type(hir_id);
            let mut fact = LocalFacts {
                is_param: false,
                is_pointer: matches!(ty.kind(), ty::RawPtr(..)),
                assignments: Vec::new(),
                address_taken: false,
                other_shapes: Vec::new(),
                view_prefix: None,
            };
            if let Some(init) = local.init {
                let kind = self.assign_kind(init);
                if kind == AssignKind::Other {
                    fact.other_shapes.push(rhs_shape(init));
                }
                fact.assignments.push(kind);
                fact.view_prefix = self.address_of_place(init);
            }
            self.facts.insert(hir_id, fact);
        }
        intravisit::walk_stmt(self, stmt);
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        match &expr.kind {
            ExprKind::Assign(lhs, rhs, _) | ExprKind::AssignOp(_, lhs, rhs) => {
                if let Some(binding) = resolved_local(lhs) {
                    let kind = match &expr.kind {
                        ExprKind::Assign(..) => self.assign_kind(rhs),
                        _ => AssignKind::Other,
                    };
                    if let Some(fact) = self.facts.get_mut(&binding) {
                        if kind == AssignKind::Other {
                            fact.other_shapes.push(rhs_shape(rhs));
                        }
                        fact.assignments.push(kind);
                    }
                }
            }
            // R624-1: a raw borrow (`&raw mut p`, `addr_of_mut!(p)`) takes the
            // address exactly as `&mut p` does.
            ExprKind::AddrOf(_, _, operand) => {
                // `&mut p` / `&p` of the binding ITSELF (not of a place inside
                // it): a pointer local can then be reassigned through the
                // address, so its value is no longer a single provenance.
                if let Some(binding) = resolved_local(operand)
                    && let Some(fact) = self.facts.get_mut(&binding)
                    && fact.is_pointer
                {
                    fact.address_taken = true;
                }
            }
            // Auto-ref method receivers on a pointer local (`p.offset(..)`,
            // `p.is_null()`) take the value, not the slot; `p.as_mut_ptr()` on
            // an array is a view into the object. Neither reassigns.
            _ => {}
        }
        intravisit::walk_expr(self, expr);
    }
}

struct CallCollector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    caller: LocalDefId,
    typeck: &'a TypeckResults<'tcx>,
    locals: &'a FxHashSet<LocalDefId>,
    classes: &'a FxHashMap<HirId, RootClass>,
    fresh_fields: &'a FxHashMap<(DefId, Symbol), FreshFieldFact>,
    why: &'a FxHashMap<HirId, UnknownWhy>,
    /// R513-3: the place each single-definition view local is a view OF.
    prefixes: &'a FxHashMap<HirId, PlacePath>,
    /// R628-7: the bindings that name one storage for the whole body.
    stable: &'a FxHashSet<HirId>,
    /// R628-7: the must-store summaries, and the caller's formals in order.
    summaries: &'a FxHashMap<(DefId, usize), FxHashSet<(DefId, Symbol)>>,
    params: Vec<Option<HirId>>,
    calls: Vec<(LocalDefId, SiteRecord)>,
}

impl<'tcx> Visitor<'tcx> for CallCollector<'_, 'tcx> {
    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if let ExprKind::Call(callee, args) = &expr.kind
            && let Some(did) = callee_def_id(callee)
            && let Some(local) = did.as_local()
            && self.locals.contains(&local)
        {
            let facts = StoreFacts {
                tcx: self.tcx,
                typeck: self.typeck,
                classes: self.classes,
                fresh_fields: self.fresh_fields,
                summaries: self.summaries,
                stable: self.stable,
            };
            let before = facts.before(expr);
            let args = args
                .iter()
                .enumerate()
                .map(|(index, arg)| {
                    let (class, place) =
                        argument_provenance(self.tcx, self.typeck, self.classes, arg);
                    // R479-4a: a read of an admitted pointer field names the
                    // block its allocator returned, keyed to the base it was
                    // read from.
                    let class = fresh_field_root(
                        self.tcx,
                        self.typeck,
                        self.classes,
                        self.fresh_fields,
                        arg,
                    )
                    .unwrap_or(class);
                    let why = if class == RootClass::Unknown {
                        argument_why(self.why, arg)
                    } else {
                        UnknownWhy::Known
                    };
                    // R624-1 (f): only a read AT the call; a local carried from
                    // an earlier read may hold a block from before the store.
                    let read = match (class, &peel_casts(arg).kind) {
                        (
                            RootClass::FreshField {
                                adt,
                                field,
                                via_offset: false,
                                ..
                            },
                            ExprKind::Field(object, _),
                        ) => facts
                            .stable_place(
                                place_provenance(self.tcx, self.typeck, self.classes, object).1,
                            )
                            .map(|base| ((adt, field), base)),
                        _ => None,
                    };
                    let stored_since_entry = read.as_ref().is_some_and(|(key, base)| {
                        before.iter().any(|(stored, stored_key)| {
                            stored_key == key && stored.same_place(base)
                        })
                    });
                    let field_of_formal = read.as_ref().and_then(|(key, base)| {
                        let formal = (base.deref_root && base.projections.is_empty())
                            .then(|| self.params.iter().position(|p| *p == Some(base.root)))??;
                        Some((formal, *key))
                    });
                    let pointee = facts.stable_place(place.clone());
                    let stored_fields = pointee
                        .as_ref()
                        .map(|pointee| {
                            before
                                .iter()
                                .filter(|(stored, _)| stored.same_place(pointee))
                                .map(|(_, key)| *key)
                                .collect()
                        })
                        .unwrap_or_default();
                    ArgRecord {
                        index,
                        span: arg.span,
                        class,
                        // R513-3: restore the field projections the caller's
                        // view locals consumed, so a pair written as two locals
                        // reads as the two places it always was.
                        place: place.map(|path| fold_place_prefix(path, self.prefixes)),
                        is_null: is_null_literal(arg),
                        why,
                        is_pointer: matches!(
                            self.typeck.expr_ty(arg).kind(),
                            ty::RawPtr(..) | ty::Ref(..)
                        ),
                        stored_since_entry,
                        field_of_formal,
                        stored_fields,
                        place_stable: pointee.is_some(),
                        premise: super::global_or_integer::provenance(self.tcx, self.caller, arg),
                        flow_roots: super::global_or_integer::flow_roots(
                            self.tcx,
                            self.caller,
                            arg,
                            super::global_or_integer::provenance(self.tcx, self.caller, arg),
                        ),
                    }
                })
                .collect();
            self.calls.push((
                local,
                SiteRecord {
                    call_span: expr.span,
                    args,
                },
            ));
        }
        intravisit::walk_expr(self, expr);
    }
}

/// R628-7: the bindings that name ONE storage for the whole body — never the
/// whole target of an assignment and, for a pointer, whose own address is never
/// taken (a callee could re-point it). A place rooted at one is the same place
/// at a store and at a later read.
fn stable_bindings<'tcx>(
    typeck: &TypeckResults<'tcx>,
    body: &'tcx rustc_hir::Body<'tcx>,
) -> FxHashSet<HirId> {
    struct Scan<'a, 'tcx> {
        typeck: &'a TypeckResults<'tcx>,
        bindings: FxHashSet<HirId>,
        moved: FxHashSet<HirId>,
    }
    impl<'tcx> Visitor<'tcx> for Scan<'_, 'tcx> {
        fn visit_pat(&mut self, pat: &'tcx rustc_hir::Pat<'tcx>) {
            if let PatKind::Binding(_, hir_id, ..) = pat.kind {
                self.bindings.insert(hir_id);
            }
            intravisit::walk_pat(self, pat);
        }

        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            match &expr.kind {
                ExprKind::Assign(place, _, _) | ExprKind::AssignOp(_, place, _) => {
                    if let Some(binding) = resolved_local(peel_casts(place)) {
                        self.moved.insert(binding);
                    }
                }
                ExprKind::AddrOf(_, _, operand) => {
                    if let Some(binding) = resolved_local(peel_casts(operand))
                        && matches!(self.typeck.node_type(binding).kind(), ty::RawPtr(..))
                    {
                        self.moved.insert(binding);
                    }
                }
                _ => {}
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let mut scan = Scan {
        typeck,
        bindings: FxHashSet::default(),
        moved: FxHashSet::default(),
    };
    scan.visit_body(body);
    scan.bindings
        .retain(|binding| !scan.moved.contains(binding));
    scan.bindings
}

/// R628-7: what the index reads about stores into admitted fields. A store is
/// `(place).F = v` with `F` admitted and not offset-admitted — `v` is null or an
/// allocation by the admission — or a call to a local function whose summary
/// stores `F` through the formal the place is handed to. Every place is rooted at
/// a stable binding ([`stable_bindings`]).
struct StoreFacts<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck: &'a TypeckResults<'tcx>,
    classes: &'a FxHashMap<HirId, RootClass>,
    fresh_fields: &'a FxHashMap<(DefId, Symbol), FreshFieldFact>,
    summaries: &'a FxHashMap<(DefId, usize), FxHashSet<(DefId, Symbol)>>,
    stable: &'a FxHashSet<HirId>,
}

type AdmittedStore = (PlacePath, (DefId, Symbol));

impl StoreFacts<'_, '_> {
    fn stable_place(&self, place: Option<PlacePath>) -> Option<PlacePath> {
        place.filter(|place| self.stable.contains(&place.root))
    }

    /// The stores `expr` makes on every path that continues past it. `strict`:
    /// a block's statements after one that may `return` do not count (a
    /// summary's claim is every path to the RETURN); for dominance they do,
    /// because an exit only removes paths to the call.
    fn stores(&self, expr: &Expr<'_>, strict: bool) -> Vec<AdmittedStore> {
        match &expr.kind {
            ExprKind::Assign(place, _, _) => {
                let ExprKind::Field(object, field) = &peel_casts(place).kind else {
                    return Vec::new();
                };
                let Some(key) =
                    data_field_key(self.tcx, self.typeck, object, field.name).filter(|key| {
                        self.fresh_fields
                            .get(key)
                            .is_some_and(|fact| !fact.via_offset)
                    })
                else {
                    return Vec::new();
                };
                self.stable_place(place_provenance(self.tcx, self.typeck, self.classes, object).1)
                    .map(|place| vec![(place, key)])
                    .unwrap_or_default()
            }
            ExprKind::Block(block, None) => self.block_stores(block, strict),
            // Both arms run one of them: a store both make is made.
            ExprKind::If(_, then, Some(otherwise)) => {
                let (then, otherwise) = (self.stores(then, strict), self.stores(otherwise, strict));
                then.into_iter()
                    .filter(|(place, key)| {
                        otherwise
                            .iter()
                            .any(|(other, other_key)| other_key == key && other.same_place(place))
                    })
                    .collect()
            }
            ExprKind::Call(callee, args) => {
                let Some(did) = callee_def_id(callee) else {
                    return Vec::new();
                };
                let mut out = Vec::new();
                for (index, arg) in args.iter().enumerate() {
                    let Some(keys) = self.summaries.get(&(did, index)) else {
                        continue;
                    };
                    if let Some(place) = self.stable_place(
                        argument_provenance(self.tcx, self.typeck, self.classes, arg).1,
                    ) {
                        out.extend(keys.iter().map(|key| (place.clone(), *key)));
                    }
                }
                out
            }
            _ => Vec::new(),
        }
    }

    fn block_stores<'b>(
        &self,
        block: &'b rustc_hir::Block<'b>,
        strict: bool,
    ) -> Vec<AdmittedStore> {
        let mut out = Vec::new();
        for stmt in block.stmts {
            if let StmtKind::Semi(expr) | StmtKind::Expr(expr) = stmt.kind {
                out.extend(self.stores(expr, strict));
            }
            if strict && may_return(stmt) {
                return out;
            }
        }
        if let Some(tail) = block.expr {
            out.extend(self.stores(tail, strict));
        }
        out
    }

    /// R624-1 (f): the stores that run on every path from the function's entry
    /// to `call`. Every EARLIER statement of every block enclosing the call lies
    /// on each such path — structured control flow: a `return`, `break` or
    /// `continue` only removes paths — so its stores are made before the call.
    /// A store inside a loop or on one branch is not.
    fn before(&self, call: &Expr<'_>) -> Vec<AdmittedStore> {
        let mut out = Vec::new();
        for (_, node) in self.tcx.hir_parent_iter(call.hir_id) {
            match node {
                rustc_hir::Node::Block(block) => {
                    for stmt in block.stmts {
                        if stmt.span.contains(call.span) {
                            break;
                        }
                        if let StmtKind::Semi(expr) | StmtKind::Expr(expr) = stmt.kind {
                            out.extend(self.stores(expr, false));
                        }
                    }
                }
                rustc_hir::Node::Expr(expr) if matches!(expr.kind, ExprKind::Closure(..)) => {
                    return out;
                }
                rustc_hir::Node::Item(_)
                | rustc_hir::Node::ImplItem(_)
                | rustc_hir::Node::TraitItem(_) => return out,
                _ => {}
            }
        }
        out
    }
}

/// Does the statement hold a `return` (outside closures)?
fn may_return<'tcx>(stmt: &'tcx rustc_hir::Stmt<'tcx>) -> bool {
    struct Find(bool);
    impl<'tcx> Visitor<'tcx> for Find {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            match expr.kind {
                ExprKind::Ret(_) => self.0 = true,
                ExprKind::Closure(..) => {}
                _ => intravisit::walk_expr(self, expr),
            }
        }
    }
    let mut find = Find(false);
    find.visit_stmt(stmt);
    find.0
}

/// R628-7: the admitted fields each local function stores through each of its
/// pointer formals on EVERY path to its return — `(*formal).F = v`, or a call
/// whose own summary stores `F` through the formal it is handed. The least
/// fixpoint: a function starts storing nothing, so recursion adds nothing it
/// has not shown.
fn must_store_summaries<'tcx>(
    tcx: TyCtxt<'tcx>,
    functions: &FxHashSet<LocalDefId>,
    fresh_fields: &FxHashMap<(DefId, Symbol), FreshFieldFact>,
) -> FxHashMap<(DefId, usize), FxHashSet<(DefId, Symbol)>> {
    let bodies: Vec<_> = functions
        .iter()
        .filter_map(|&function| {
            let body = tcx.hir_body(tcx.hir_node_by_def_id(function).body_id()?);
            let typeck = tcx.typeck(function);
            let params: Vec<Option<HirId>> = body
                .params
                .iter()
                .map(|param| match param.pat.kind {
                    PatKind::Binding(_, hir_id, ..) => Some(hir_id),
                    _ => None,
                })
                .collect();
            Some((
                function.to_def_id(),
                body,
                typeck,
                params,
                stable_bindings(typeck, body),
            ))
        })
        .collect();
    let classes = FxHashMap::default();
    let mut summaries: FxHashMap<(DefId, usize), FxHashSet<(DefId, Symbol)>> = FxHashMap::default();
    for _ in 0..16 {
        let mut grown = Vec::new();
        for (did, body, typeck, params, stable) in &bodies {
            let facts = StoreFacts {
                tcx,
                typeck,
                classes: &classes,
                fresh_fields,
                summaries: &summaries,
                stable,
            };
            for (place, key) in facts.stores(body.value, true) {
                if !place.deref_root || !place.projections.is_empty() {
                    continue;
                }
                if let Some(index) = params.iter().position(|param| *param == Some(place.root))
                    && !summaries
                        .get(&(*did, index))
                        .is_some_and(|keys| keys.contains(&key))
                {
                    grown.push(((*did, index), key));
                }
            }
        }
        if grown.is_empty() {
            break;
        }
        for (formal, key) in grown {
            summaries.entry(formal).or_default().insert(key);
        }
    }
    summaries
}

/// The provenance class and place path of one argument expression.
///
/// Recognized shapes, each staying inside the object it starts from on a
/// UB-free input: a bare local; `e as *mut T`; `e.offset(k)` / `e.add(k)`;
/// `&mut place` / `&place`; `&mut *e`; `place.as_mut_ptr()` / `.as_ptr()`;
/// and a place = local, `(*local)`, `.field`, `[index]` chains with at most
/// one deref, at the root. A pointer VALUE read out of a place (`(*s).buf`)
/// is a different object and classifies `Unknown`.
fn argument_provenance<'tcx>(
    tcx: TyCtxt<'tcx>,
    typeck: &TypeckResults<'tcx>,
    classes: &FxHashMap<HirId, RootClass>,
    arg: &Expr<'_>,
) -> (RootClass, Option<PlacePath>) {
    let (expr, outer) = peel_casts_retyping(typeck, arg);
    let (class, place) = argument_provenance_peeled(tcx, typeck, classes, expr);
    (class, retyped_by(place, outer))
}

fn argument_provenance_peeled<'tcx>(
    tcx: TyCtxt<'tcx>,
    typeck: &TypeckResults<'tcx>,
    classes: &FxHashMap<HirId, RootClass>,
    expr: &Expr<'_>,
) -> (RootClass, Option<PlacePath>) {
    match &expr.kind {
        // `&mut place` / `&place`: a view into the place's object. R624-1: a
        // raw borrow is the same view — and every other shape below hands an
        // `AddrOf` back here, so a raw borrow left to them never returns.
        ExprKind::AddrOf(_, _, operand) => {
            let (operand, cast) = peel_casts_retyping(typeck, operand);
            // `&mut *e` — a reborrow of whatever `e` addresses.
            if let ExprKind::Unary(UnOp::Deref, inner) = &operand.kind
                && matches!(typeck.expr_ty(inner).kind(), ty::RawPtr(..))
            {
                let (class, place) = pointer_value_provenance(tcx, typeck, classes, inner);
                return (class, retyped_by(place, cast));
            }
            let (class, place) = place_provenance(tcx, typeck, classes, operand);
            (class, retyped_by(place, cast))
        }
        // `place.as_mut_ptr()` / `place.as_ptr()`: a view into the array
        // object. `e.offset(k)` / `e.add(k)`: the pointer's own object.
        ExprKind::MethodCall(segment, receiver, method_args, _) => {
            match segment.ident.name.as_str() {
                "as_mut_ptr" | "as_ptr" if method_args.is_empty() => {
                    let (receiver, cast) = peel_casts_retyping(typeck, receiver);
                    if matches!(typeck.expr_ty(receiver).kind(), ty::Array(..)) {
                        let (class, place) = place_provenance(tcx, typeck, classes, receiver);
                        (class, retyped_by(place, cast))
                    } else {
                        (RootClass::Unknown, None)
                    }
                }
                "offset" | "add" | "wrapping_add" | "wrapping_offset" | "cast" => {
                    let (class, _) = pointer_value_provenance(tcx, typeck, classes, receiver);
                    (class, None)
                }
                _ => (RootClass::Unknown, None),
            }
        }
        _ => pointer_value_provenance(tcx, typeck, classes, expr),
    }
}

/// R479-4a: the root of `(*b).f` / `b.f` when `f` is an admitted allocator
/// field — the block the allocator returned, keyed to `b` so `certify_roots`
/// can apply the same-base claim and nothing wider.
fn fresh_field_root<'tcx>(
    tcx: TyCtxt<'tcx>,
    typeck: &TypeckResults<'tcx>,
    classes: &FxHashMap<HirId, RootClass>,
    fresh_fields: &FxHashMap<(DefId, Symbol), FreshFieldFact>,
    arg: &Expr<'_>,
) -> Option<RootClass> {
    let ExprKind::Field(base, field) = &peel_casts(arg).kind else {
        return None;
    };
    let key = data_field_key(tcx, typeck, base, field.name)?;
    let FreshFieldFact {
        freshness,
        same_base_only,
        via_offset,
    } = *fresh_fields.get(&key)?;
    // The base must itself name one object, or "same base" names nothing.
    let (base_class, _) = place_provenance(tcx, typeck, classes, base);
    Some(RootClass::FreshField {
        adt: key.0,
        field: key.1,
        base: base_class.object_id()?,
        freshness,
        same_base_only,
        via_offset,
    })
}

/// R478-5: attribute an `Unknown` ARGUMENT. When the expression names a binding
/// the binding's own reason governs; otherwise the expression's own shape does,
/// which is where the `field-read` bucket (report 020's wall) comes from.
fn argument_why(why: &FxHashMap<HirId, UnknownWhy>, arg: &Expr<'_>) -> UnknownWhy {
    if is_null_literal(arg) {
        return UnknownWhy::NullLiteral;
    }
    let mut cur = peel_casts(arg);
    loop {
        match &cur.kind {
            ExprKind::Path(..) => {
                return match resolved_local(cur).and_then(|binding| why.get(&binding).copied()) {
                    // The binding's own root is known, so what stopped the
                    // argument is the expression shape around it.
                    Some(UnknownWhy::Known) | None => UnknownWhy::ShapeUnsupported,
                    Some(reason) => reason,
                };
            }
            ExprKind::Field(..) => return UnknownWhy::FieldRead,
            ExprKind::Index(..) => return UnknownWhy::IndexRead,
            ExprKind::Call(..) => return UnknownWhy::CallResult,
            ExprKind::AddrOf(_, _, base)
            | ExprKind::MethodCall(_, base, ..)
            | ExprKind::Unary(UnOp::Deref, base)
            | ExprKind::DropTemps(base) => cur = peel_casts(base),
            other => {
                return UnknownWhy::NotALocal(match other {
                    ExprKind::Binary(..) => "not-a-local:binary",
                    ExprKind::Lit(..) => "not-a-local:literal",
                    ExprKind::If(..) => "not-a-local:if",
                    ExprKind::Block(..) => "not-a-local:block",
                    ExprKind::Struct(..) => "not-a-local:struct",
                    ExprKind::Array(..) | ExprKind::Repeat(..) => "not-a-local:array",
                    ExprKind::Unary(..) => "not-a-local:unary",
                    ExprKind::Tup(..) => "not-a-local:tuple",
                    _ => "not-a-local:other",
                });
            }
        }
    }
}

/// A pointer-typed VALUE expression: a bare local's class, or unknown.
fn pointer_value_provenance<'tcx>(
    tcx: TyCtxt<'tcx>,
    typeck: &TypeckResults<'tcx>,
    classes: &FxHashMap<HirId, RootClass>,
    expr: &Expr<'_>,
) -> (RootClass, Option<PlacePath>) {
    let (expr, cast) = peel_casts_retyping(typeck, expr);
    let (class, place) = pointer_value_provenance_peeled(tcx, typeck, classes, expr);
    (class, retyped_by(place, cast))
}

fn pointer_value_provenance_peeled<'tcx>(
    tcx: TyCtxt<'tcx>,
    typeck: &TypeckResults<'tcx>,
    classes: &FxHashMap<HirId, RootClass>,
    expr: &Expr<'_>,
) -> (RootClass, Option<PlacePath>) {
    match &expr.kind {
        // wave-5d 148b: a static's VALUE is whatever was stored in it, not the
        // static's own storage (that is `&mut G` / `G.as_mut_ptr()`, a place,
        // read by `place_provenance`). `G = tmp; f(G, tmp)` is one block.
        ExprKind::Path(..) if resolved_local(expr).is_none() => (RootClass::Unknown, None),
        // wave-5d 148b: only a raw POINTER binding's value is classed by the
        // binding. An integer (`n as *mut T`, possibly `(uintptr_t)buf`) or a
        // reference binding's value addresses some other object, never the
        // binding's own stack slot, which is what its `StackObject` class names.
        ExprKind::Path(..) if !typeck.expr_ty(expr).is_raw_ptr() => (RootClass::Unknown, None),
        ExprKind::Path(..) => match resolved_local(expr) {
            Some(binding) => {
                let class = classes.get(&binding).copied().unwrap_or(RootClass::Unknown);
                // A pointer local's VALUE addresses its pointee: the place path
                // is `*binding` with no projections.
                let place = PlacePath {
                    root: binding,
                    deref_root: true,
                    projections: Vec::new(),
                    retyped: false,
                };
                (class, Some(place))
            }
            None => (RootClass::Unknown, None),
        },
        ExprKind::MethodCall(..) | ExprKind::AddrOf(..) => {
            argument_provenance_peeled(tcx, typeck, classes, expr)
        }
        _ => (RootClass::Unknown, None),
    }
}

/// R460-8. The binding whose OBJECT an address-producing expression stays
/// inside. A pointer VALUE loaded out of a place (`(*s).field`) is deliberately
/// NOT a derivation: it addresses whatever was stored there, which is another
/// object, so such a local keeps `Unknown` and the pair stays held.
fn derivation_base<'tcx>(typeck: &TypeckResults<'tcx>, expr: &Expr<'_>) -> Option<HirId> {
    let expr = peel_casts(expr);
    match &expr.kind {
        // wave-5d 148b: only a raw pointer binding's value derives from it.
        ExprKind::Path(..) if typeck.expr_ty(expr).is_raw_ptr() => resolved_local(expr),
        ExprKind::Path(..) => None,
        ExprKind::AddrOf(_, _, operand) => derivation_place_base(typeck, peel_casts(operand)),
        ExprKind::MethodCall(segment, receiver, method_args, _) => {
            let receiver = peel_casts(receiver);
            match segment.ident.name.as_str() {
                "as_mut_ptr" | "as_ptr"
                    if method_args.is_empty()
                        && matches!(typeck.expr_ty(receiver).kind(), ty::Array(..)) =>
                {
                    derivation_place_base(typeck, receiver)
                }
                "offset" | "add" | "wrapping_add" | "wrapping_offset" | "cast" => {
                    derivation_base(typeck, receiver)
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// The root binding of a PLACE: `(*b).f.g` / `b.arr[i]` → `b`, allowing one
/// deref of a pointer at the root (the place is inside that pointee).
fn derivation_place_base<'tcx>(typeck: &TypeckResults<'tcx>, place: &Expr<'_>) -> Option<HirId> {
    match &place.kind {
        ExprKind::Field(base, _) => derivation_place_base(typeck, peel_casts(base)),
        ExprKind::Index(base, ..) => derivation_place_base(typeck, peel_casts(base)),
        ExprKind::Unary(UnOp::Deref, inner) => derivation_base(typeck, inner),
        ExprKind::Path(..) => resolved_local(place),
        _ => None,
    }
}

/// A PLACE expression: walk `Field` / `Index` projections down to the root,
/// allowing one deref of a pointer local at the root.
fn place_provenance<'tcx>(
    _tcx: TyCtxt<'tcx>,
    typeck: &TypeckResults<'tcx>,
    classes: &FxHashMap<HirId, RootClass>,
    place: &Expr<'_>,
) -> (RootClass, Option<PlacePath>) {
    let mut projections: Vec<Projection> = Vec::new();
    let mut cur = place;
    loop {
        match &cur.kind {
            ExprKind::Field(base, ident) => {
                // R550-2: the field's parent is the type of the base it is
                // projected from, after the base's own adjustments.
                let (parent, union) = match typeck.expr_ty_adjusted(base).peel_refs().kind() {
                    ty::Adt(def, _) => (Some(def.did()), def.is_union()),
                    _ => (None, false),
                };
                projections.push(Projection::Field {
                    parent,
                    union,
                    name: ident.name.to_string(),
                });
                cur = base;
            }
            ExprKind::Index(base, _, _) => {
                projections.push(Projection::Index);
                cur = base;
            }
            ExprKind::DropTemps(base) => cur = base,
            ExprKind::Unary(UnOp::Deref, base) => {
                // One deref, at the root, of a pointer local: a place inside
                // its pointee. R550-2: a cast here changes what the
                // projections below are projections OF.
                let (base, cast) = peel_casts_retyping(typeck, base);
                let Some(binding) = resolved_local(base) else {
                    return (RootClass::Unknown, None);
                };
                if !matches!(typeck.expr_ty(base).kind(), ty::RawPtr(..) | ty::Ref(..)) {
                    return (RootClass::Unknown, None);
                }
                projections.reverse();
                let class = classes.get(&binding).copied().unwrap_or(RootClass::Unknown);
                return (
                    class,
                    Some(PlacePath {
                        root: binding,
                        deref_root: true,
                        projections,
                        retyped: cast,
                    }),
                );
            }
            ExprKind::Path(..) => {
                let Some(binding) = resolved_local(cur) else {
                    // A `static` is a named object of its own; it carries no
                    // `PlacePath`, whose root is a binding.
                    return match resolved_static(cur) {
                        Some(did) => (RootClass::Static(did), None),
                        None => (RootClass::Unknown, None),
                    };
                };
                projections.reverse();
                let class = match classes.get(&binding).copied() {
                    // The binding's own slot: a stack object whatever its type
                    // (a pointer parameter's slot included).
                    Some(RootClass::StackObject(id)) => RootClass::StackObject(id),
                    Some(_) | None => RootClass::StackObject(binding),
                };
                return (
                    class,
                    Some(PlacePath {
                        root: binding,
                        deref_root: false,
                        projections,
                        retyped: false,
                    }),
                );
            }
            _ => return (RootClass::Unknown, None),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn w6p_root_certificate_needs_one_fresh_object_and_one_fixed_other() {
        let a = HirId::make_owner(rustc_hir::def_id::CRATE_DEF_ID);
        let b = HirId {
            owner: a.owner,
            local_id: rustc_hir::hir_id::ItemLocalId::from_u32(1),
        };
        assert_eq!(
            certify_roots(
                RootClass::FreshAlloc(a, Freshness::Proven),
                RootClass::EntryStorage(b)
            ),
            Some(CertificateKind::DistinctRoots)
        );
        assert_eq!(
            certify_roots(
                RootClass::FreshAlloc(a, Freshness::Contract),
                RootClass::EntryStorage(b)
            ),
            Some(CertificateKind::DistinctRootsUnderContract),
            "a contract-backed root is receipted as such"
        );
        assert_eq!(
            certify_roots(
                RootClass::FreshAlloc(a, Freshness::Contract),
                RootClass::FreshAlloc(b, Freshness::Proven)
            ),
            Some(CertificateKind::DistinctRootsUnderContract),
            "one contract-backed side is enough to receipt the pair"
        );
        assert_eq!(
            certify_roots(RootClass::StackObject(a), RootClass::StackObject(b)),
            Some(CertificateKind::DistinctRoots)
        );
        assert_eq!(
            certify_roots(RootClass::StackObject(a), RootClass::StackObject(a)),
            None
        );
        assert_eq!(
            certify_roots(RootClass::EntryStorage(a), RootClass::EntryStorage(b)),
            None,
            "two entry pointers may alias each other"
        );
        assert_eq!(
            certify_roots(
                RootClass::FreshAlloc(a, Freshness::Proven),
                RootClass::Unknown
            ),
            None
        );
    }

    /// R513-3. `fold_place_prefix` is exercised directly because its
    /// `deref_root` guard is unreachable from a fixture: the only way to build
    /// a path at a local's own SLOT is `&local`, which sets `address_taken` and
    /// so keeps that local out of `prefixes` in the first place. The guard is
    /// the second wall, and this is what holds it up.
    #[test]
    fn w6p_a_prefix_folds_through_a_pointee_and_never_through_a_slot() {
        let local = HirId::make_owner(rustc_hir::def_id::CRATE_DEF_ID);
        let base = HirId::make_owner(rustc_hir::def_id::LocalDefId {
            local_def_index: rustc_hir::def_id::DefIndex::from_u32(1),
        });
        let parent = Some(rustc_hir::def_id::CRATE_DEF_ID.to_def_id());
        let path = |root, deref_root: bool, projections: &[&str]| PlacePath {
            root,
            deref_root,
            projections: projections
                .iter()
                .map(|p| Projection::Field {
                    parent,
                    union: false,
                    name: (*p).to_owned(),
                })
                .collect(),
            retyped: false,
        };
        let mut prefixes = FxHashMap::default();
        prefixes.insert(local, path(base, true, &["br"]));

        // `*local` with `local = &mut (*base).br` IS `(*base).br`.
        assert_eq!(
            fold_place_prefix(path(local, true, &["bits"]), &prefixes),
            path(base, true, &["br", "bits"])
        );
        // `local` itself is the binding's own storage, which is NOT the place
        // it points at; folding here would name another object entirely.
        assert_eq!(
            fold_place_prefix(path(local, false, &[]), &prefixes),
            path(local, false, &[])
        );
        // A root with no recorded prefix is left exactly as it came.
        assert_eq!(
            fold_place_prefix(path(base, true, &["br"]), &prefixes),
            path(base, true, &["br"])
        );
        // R550-2: a view whose initializer was retyped retypes the fold.
        let mut retyped = path(base, true, &["br"]);
        retyped.retyped = true;
        prefixes.insert(local, retyped);
        assert!(fold_place_prefix(path(local, true, &["bits"]), &prefixes).retyped);
    }

    #[test]
    fn w6p_disjoint_fields_diverge_only_at_a_field() {
        let root = HirId::make_owner(rustc_hir::def_id::CRATE_DEF_ID);
        let parent = Some(rustc_hir::def_id::CRATE_DEF_ID.to_def_id());
        let path = |deref_root: bool, projections: &[Option<&str>]| PlacePath {
            root,
            deref_root,
            projections: projections
                .iter()
                .map(|p| match p {
                    Some(name) => Projection::Field {
                        parent,
                        union: false,
                        name: (*name).to_owned(),
                    },
                    None => Projection::Index,
                })
                .collect(),
            retyped: false,
        };
        assert!(disjoint_fields(
            &path(true, &[Some("a")]),
            &path(true, &[Some("b")])
        ));
        assert!(disjoint_fields(
            &path(true, &[Some("a"), Some("x")]),
            &path(true, &[Some("a"), Some("y")])
        ));
        assert!(
            !disjoint_fields(
                &path(true, &[Some("a")]),
                &path(true, &[Some("a"), Some("y")])
            ),
            "a prefix overlaps"
        );
        assert!(
            !disjoint_fields(&path(true, &[None]), &path(true, &[None])),
            "two indices of one array may coincide"
        );
        assert!(
            disjoint_fields(
                &path(true, &[None, Some("f")]),
                &path(true, &[None, Some("g")])
            ),
            "distinct fields of any two elements are disjoint"
        );
        assert!(
            !disjoint_fields(&path(true, &[None]), &path(true, &[Some("a")])),
            "an index never diverges from a field"
        );
        assert!(
            !disjoint_fields(&path(true, &[Some("a")]), &path(true, &[Some("a")])),
            "the same place is not disjoint from itself"
        );
        assert!(
            !disjoint_fields(&path(true, &[Some("a")]), &path(false, &[Some("b")])),
            "the pointee and the pointer slot are different objects, not fields of one"
        );

        // R550-2, Erratum 9d (ii): the divergence must be at fields OF ONE
        // STRUCTURE — not of a union, not of two different parents, not on a
        // spine a cast retyped.
        let field = |parent, union: bool, name: &str| Projection::Field {
            parent,
            union,
            name: name.to_owned(),
        };
        let spine = |projections: Vec<Projection>| PlacePath {
            root,
            deref_root: true,
            projections,
            retyped: false,
        };
        let other = Some(
            rustc_hir::def_id::LocalDefId {
                local_def_index: rustc_hir::def_id::DefIndex::from_u32(1),
            }
            .to_def_id(),
        );
        assert_eq!(
            divergence(
                &spine(vec![field(parent, true, "x")]),
                &spine(vec![field(parent, true, "y")])
            ),
            Divergence::UnionMembers,
            "two members of one union overlap"
        );
        assert!(
            !disjoint_fields(
                &spine(vec![field(parent, false, "a")]),
                &spine(vec![field(other, false, "b")])
            ),
            "fields of two different parents at one position are not fields of one structure"
        );
        assert!(
            !disjoint_fields(
                &spine(vec![field(None, false, "0")]),
                &spine(vec![field(None, false, "1")])
            ),
            "a field whose parent is not known is not a structure field"
        );
        let mut retyped = spine(vec![field(parent, false, "a")]);
        retyped.retyped = true;
        assert!(
            !disjoint_fields(&retyped, &spine(vec![field(parent, false, "b")])),
            "a retyped spine is not a base"
        );
        assert!(
            retyped.same_place(&spine(vec![field(parent, false, "a")])),
            "but it still names the same place"
        );
    }
}
