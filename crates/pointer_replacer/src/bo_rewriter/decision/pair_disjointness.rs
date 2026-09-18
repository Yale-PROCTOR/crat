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
    BorrowKind, Expr, ExprKind, HirId, LangItem, PatKind, QPath, StmtKind, UnOp,
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
    /// (e) R462-1. The CALLEE's two parameters never alias, because at every
    /// in-program call the two arguments are disjoint — by (a)/(b)/(c) at that
    /// caller, or by (e) again on the caller's own parameters.
    ParameterPair,
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
}

impl CertificateKind {
    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::DistinctRoots => "pair-disjoint:distinct-roots",
            Self::DistinctRootsUnderContract => "pair-disjoint:distinct-roots:allocator-contract",
            Self::TypeRule => "pair-disjoint:type-rule",
            Self::DisjointFields => "pair-disjoint:disjoint-fields",
            Self::FreshStackAddress => "pair-disjoint:fresh-stack-address",
            Self::ParameterPair => "pair-disjoint:parameter-pair",
            Self::ExportedEntryWaiver => "pair-disjoint:exported-entry-waiver",
        }
    }
}

pub(crate) const CERTIFICATE_FAMILY: &str = "pair-disjointness-certificate";

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
    Unknown,
}

impl RootClass {
    /// The contract receipt this root carries, if its freshness rests on one.
    fn freshness(self) -> Freshness {
        match self {
            Self::FreshAlloc(_, freshness) => freshness,
            _ => Freshness::Proven,
        }
    }

    fn is_fresh_object(self) -> bool {
        matches!(self, Self::FreshAlloc(..) | Self::StackObject(_))
    }

    fn object_id(self) -> Option<HirId> {
        match self {
            Self::FreshAlloc(id, _) | Self::StackObject(id) | Self::EntryStorage(id) => Some(id),
            Self::Unknown => None,
        }
    }
}

/// A place path: the root binding, whether the path passes through one deref
/// of that root, and the projections after it. `None` in a projection slot is
/// an `Index`; `Some(name)` a `Field`.
#[derive(Clone, Debug, PartialEq, Eq)]
struct PlacePath {
    root: HirId,
    deref_root: bool,
    projections: Vec<Option<String>>,
}

#[derive(Clone, Debug)]
struct ArgRecord {
    index: usize,
    span: Span,
    class: RootClass,
    place: Option<PlacePath>,
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
    /// Each function's pointer-parameter bindings, in formal order: what lets
    /// (e) map an argument's entry root back to the caller's own formal.
    param_bindings: FxHashMap<u32, Vec<HirId>>,
    /// Functions the embedder can call: `#[no_mangle]` / `export_name`. Only
    /// these may bottom out on R462-1's waiver.
    exported: FxHashSet<u32>,
    /// R466-5: `(caller, callee, argument index)` where that argument is the
    /// address of a stack local taken exactly once in the caller's body, at a
    /// callee position wave-6r's walk proves never retained.
    fresh_stack: FxHashSet<(u32, u32, usize)>,
    /// (e)'s memo, keyed by `(callee, i, j)` with `i < j`.
    parameter_pairs: RefCell<FxHashMap<(u32, usize, usize), Option<PairSeparation>>>,
    ledger: RefCell<Vec<LedgerRow>>,
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
        let unions = union_member_classes(tcx, program);
        // Member closures are shared across every pair: brotli's ~3k functions
        // ask about the same few hundred pointee types, and recomputing the
        // closure per pair cost the first census its 20-minute slot.
        let mut closures: FxHashMap<TypeClass, FxHashSet<TypeClass>> = FxHashMap::default();

        let mut sites: FxHashMap<(u32, u32), Vec<SiteRecord>> = FxHashMap::default();
        for &caller in &program.functions {
            let Some(body_id) = tcx.hir_node_by_def_id(caller).body_id() else {
                continue;
            };
            let body = tcx.hir_body(body_id);
            let typeck = tcx.typeck(caller);
            let classes = classify_locals(tcx, typeck, body, &allocators, caller);
            let mut collector = CallCollector {
                tcx,
                typeck,
                locals: &local_functions,
                classes: &classes,
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
        for &callee in &program.functions {
            let inputs = tcx.fn_sig(callee).skip_binder().skip_binder().inputs();
            for index in 0..inputs.len() {
                let local = rustc_middle::mir::Local::from_usize(index + 1);
                if !mut_facts.is_defaulted(callee, local) && !mut_facts.is_mutable(callee, local) {
                    immutable_formals.insert((callee.local_def_index.as_u32(), index));
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
            param_bindings,
            exported,
            parameter_pairs: RefCell::new(FxHashMap::default()),
            ledger: RefCell::new(Vec::new()),
        }
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
                    result = None;
                    break;
                };
                callers += 1;
                // R462-1 (2): an in-crate caller that hands the callee the
                // same place refuses the pair, waiver or not.
                if let (Some(pa), Some(pb)) = (&a.place, &b.place)
                    && pa == pb
                {
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
                    result = None;
                    break;
                };
                if up_left == up_right {
                    result = None;
                    break;
                }
                match self.parameter_pair(*caller, up_left, up_right, depth + 1, seen) {
                    Some(up) => result = result.map(|acc| acc.join(up)),
                    None => {
                        result = None;
                    }
                }
            }
            if result.is_none() {
                break;
            }
        }
        if callers == 0 && !self.exported.contains(&callee) {
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
        });
        outcome
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
            })
            .ok_or(Unproved::SiteUnresolved)?;
        let arg = |index: usize, span: Span| {
            site.args
                .iter()
                .find(|arg| arg.index == index && arg.span.source_callsite() == span)
        };
        let (Some(a), Some(b)) = (arg(left, left_span), arg(right, right_span)) else {
            return Err(Unproved::SiteUnresolved);
        };
        if self.immutable_formals.contains(&(callee, left))
            && self.immutable_formals.contains(&(callee, right))
        {
            return Err(Unproved::ReadReadPeers);
        }
        // The same syntactic place, however it is cast, is never disjoint from
        // itself; refused before any rule is consulted.
        if let (Some(pa), Some(pb)) = (&a.place, &b.place)
            && pa == pb
        {
            return Err(Unproved::SamePlace);
        }
        if let Some(kind) = certify_roots(a.class, b.class) {
            return Ok(kind);
        }
        let key = (callee, left.min(right), left.max(right));
        let type_verdict = self
            .type_rule
            .get(&key)
            .map_or(Err(Unproved::TypeUnresolved), |row| row.verdict);
        if type_verdict.is_ok() {
            return Ok(CertificateKind::TypeRule);
        }
        if let (Some(pa), Some(pb)) = (&a.place, &b.place)
            && disjoint_fields(pa, pb)
        {
            return Ok(CertificateKind::DisjointFields);
        }
        // R466-5, before (e): a fresh stack address at this call cannot be
        // aliased by a pointer value that existed before it.
        if self.fresh_stack.contains(&(caller, callee, a.index))
            || self.fresh_stack.contains(&(caller, callee, b.index))
        {
            return Ok(CertificateKind::FreshStackAddress);
        }
        // (e) R462-1, last: the callee's two parameters may be separable even
        // where this call site's arguments are not, if every in-program call
        // separates them (or the chain reaches an exported entry's waiver).
        match self.parameter_pair(callee, left, right, 0, &mut Vec::new()) {
            Some(PairSeparation::Proven) => return Ok(CertificateKind::ParameterPair),
            Some(PairSeparation::Waived) => return Ok(CertificateKind::ExportedEntryWaiver),
            None => {}
        }
        // Report the type rule's reason when it was consulted, the roots
        // otherwise: whichever is the most specific thing the input lacked.
        Err(match type_verdict {
            Err(Unproved::TypeUnresolved) => Unproved::RootsUnknown,
            Err(why) => why,
            Ok(()) => unreachable!("an accepted type rule returned above"),
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

    #[allow(
        dead_code,
        reason = "witness surface: every certify() outcome, for the RED-first tests \
                  and the census ledger column main may add"
    )]
    pub(crate) fn ledger(&self) -> Vec<LedgerRow> {
        self.ledger.borrow().clone()
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

/// (a): one side a fresh object of the caller, the other a distinct fresh
/// object or storage that existed at entry.
fn certify_roots(a: RootClass, b: RootClass) -> Option<CertificateKind> {
    let (fresh, other) = if a.is_fresh_object() {
        (a, b)
    } else if b.is_fresh_object() {
        (b, a)
    } else {
        return None;
    };
    match other {
        RootClass::Unknown => None,
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

/// (c): same root, same deref status, and the first differing projection is a
/// `Field` on both sides.
fn disjoint_fields(a: &PlacePath, b: &PlacePath) -> bool {
    if a.root != b.root || a.deref_root != b.deref_root {
        return false;
    }
    for (x, y) in a.projections.iter().zip(&b.projections) {
        if x != y {
            return x.is_some() && y.is_some();
        }
    }
    false
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
    pub outcome: String,
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
                    for right in record.args.iter().skip(position + 1) {
                        let outcome = self
                            .certify(
                                caller,
                                callee,
                                left.index,
                                right.index,
                                left.span,
                                right.span,
                            )
                            .map_or_else(|why| why.key().to_owned(), |kind| kind.key().to_owned());
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
                            outcome,
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
        indirect_calls,
    };
    loop {
        let before = (oracle.wrappers.len(), oracle.allocator_fields.len());
        oracle.allocator_fields = allocator_fn_pointer_fields(tcx, functions, &oracle);
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
            let classes = classify_locals(tcx, typeck, body, &oracle, function);
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
        if (oracle.wrappers.len(), oracle.allocator_fields.len()) == before {
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

fn classify_locals<'tcx>(
    tcx: TyCtxt<'tcx>,
    typeck: &TypeckResults<'tcx>,
    body: &'tcx rustc_hir::Body<'tcx>,
    allocators: &AllocatorOracle<'_>,
    function: LocalDefId,
) -> FxHashMap<HirId, RootClass> {
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
    classes
}

struct LocalCollector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck: &'a TypeckResults<'tcx>,
    allocators: &'a AllocatorOracle<'a>,
    function: LocalDefId,
    facts: &'a mut FxHashMap<HirId, LocalFacts>,
}

impl<'a, 'tcx> LocalCollector<'a, 'tcx> {
    fn assign_kind(&self, rhs: &Expr<'_>) -> AssignKind {
        if is_null_literal(rhs) {
            AssignKind::Null
        } else if let Some(freshness) =
            self.allocators
                .is_allocator_call(self.tcx, self.function, rhs)
        {
            AssignKind::Allocator(freshness)
        } else if let Some(base) = derivation_base(self.typeck, rhs) {
            AssignKind::Derived(base)
        } else {
            AssignKind::Other
        }
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
            };
            if let Some(init) = local.init {
                fact.assignments.push(self.assign_kind(init));
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
                        fact.assignments.push(kind);
                    }
                }
            }
            ExprKind::AddrOf(BorrowKind::Ref, _, operand) => {
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
    typeck: &'a TypeckResults<'tcx>,
    locals: &'a FxHashSet<LocalDefId>,
    classes: &'a FxHashMap<HirId, RootClass>,
    calls: Vec<(LocalDefId, SiteRecord)>,
}

impl<'tcx> Visitor<'tcx> for CallCollector<'_, 'tcx> {
    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if let ExprKind::Call(callee, args) = &expr.kind
            && let Some(did) = callee_def_id(callee)
            && let Some(local) = did.as_local()
            && self.locals.contains(&local)
        {
            let args = args
                .iter()
                .enumerate()
                .map(|(index, arg)| {
                    let (class, place) =
                        argument_provenance(self.tcx, self.typeck, self.classes, arg);
                    ArgRecord {
                        index,
                        span: arg.span,
                        class,
                        place,
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
    let expr = peel_casts(arg);
    match &expr.kind {
        // `&mut place` / `&place`: a view into the place's object.
        ExprKind::AddrOf(BorrowKind::Ref, _, operand) => {
            let operand = peel_casts(operand);
            // `&mut *e` — a reborrow of whatever `e` addresses.
            if let ExprKind::Unary(UnOp::Deref, inner) = &operand.kind
                && matches!(typeck.expr_ty(inner).kind(), ty::RawPtr(..))
            {
                return pointer_value_provenance(tcx, typeck, classes, inner);
            }
            place_provenance(tcx, typeck, classes, operand)
        }
        // `place.as_mut_ptr()` / `place.as_ptr()`: a view into the array
        // object. `e.offset(k)` / `e.add(k)`: the pointer's own object.
        ExprKind::MethodCall(segment, receiver, method_args, _) => {
            match segment.ident.name.as_str() {
                "as_mut_ptr" | "as_ptr" if method_args.is_empty() => {
                    let receiver = peel_casts(receiver);
                    if matches!(typeck.expr_ty(receiver).kind(), ty::Array(..)) {
                        place_provenance(tcx, typeck, classes, receiver)
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

/// A pointer-typed VALUE expression: a bare local's class, or unknown.
fn pointer_value_provenance<'tcx>(
    tcx: TyCtxt<'tcx>,
    typeck: &TypeckResults<'tcx>,
    classes: &FxHashMap<HirId, RootClass>,
    expr: &Expr<'_>,
) -> (RootClass, Option<PlacePath>) {
    let expr = peel_casts(expr);
    match &expr.kind {
        ExprKind::Path(..) => match resolved_local(expr) {
            Some(binding) => {
                let class = classes.get(&binding).copied().unwrap_or(RootClass::Unknown);
                // A pointer local's VALUE addresses its pointee: the place path
                // is `*binding` with no projections.
                let place = PlacePath {
                    root: binding,
                    deref_root: true,
                    projections: Vec::new(),
                };
                (class, Some(place))
            }
            None => (RootClass::Unknown, None),
        },
        ExprKind::MethodCall(..) | ExprKind::AddrOf(..) => {
            argument_provenance(tcx, typeck, classes, expr)
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
        ExprKind::Path(..) => resolved_local(expr),
        ExprKind::AddrOf(BorrowKind::Ref, _, operand) => {
            derivation_place_base(typeck, peel_casts(operand))
        }
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
    let mut projections: Vec<Option<String>> = Vec::new();
    let mut cur = place;
    loop {
        match &cur.kind {
            ExprKind::Field(base, ident) => {
                projections.push(Some(ident.name.to_string()));
                cur = base;
            }
            ExprKind::Index(base, _, _) => {
                projections.push(None);
                cur = base;
            }
            ExprKind::DropTemps(base) => cur = base,
            ExprKind::Unary(UnOp::Deref, base) => {
                // One deref, at the root, of a pointer local: a place inside
                // its pointee.
                let base = peel_casts(base);
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
                    }),
                );
            }
            ExprKind::Path(..) => {
                let Some(binding) = resolved_local(cur) else {
                    return (RootClass::Unknown, None);
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

    #[test]
    fn w6p_disjoint_fields_diverge_only_at_a_field() {
        let root = HirId::make_owner(rustc_hir::def_id::CRATE_DEF_ID);
        let path = |deref_root: bool, projections: &[Option<&str>]| PlacePath {
            root,
            deref_root,
            projections: projections.iter().map(|p| p.map(str::to_owned)).collect(),
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
    }
}
