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
use rustc_span::Span;

use crate::{analyses::borrow_ownership::mutability_facts::MutFacts, utils::rustc::RustProgram};

/// libc allocators whose result is a fresh block: disjoint from every object
/// live at the call. `realloc` returns either a fresh block or the caller's own
/// block with every other pointer to it dead — on a UB-free input the result
/// aliases nothing else live either way.
const LIBC_ALLOCATORS: &[&str] = &["malloc", "calloc", "realloc"];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CertificateKind {
    DistinctRoots,
    TypeRule,
    DisjointFields,
}

impl CertificateKind {
    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::DistinctRoots => "pair-disjoint:distinct-roots",
            Self::TypeRule => "pair-disjoint:type-rule",
            Self::DisjointFields => "pair-disjoint:disjoint-fields",
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
    /// Two views under one NULLABLE pointer root (`is_null`-tested or
    /// null-assigned, so it delivers as `Option<&mut T>`): each view is bridged
    /// through `root.as_mut().unwrap()`, and two of them live in one call are
    /// two `&mut` borrows of the Option — E0499, a compile revert (report 002,
    /// binn `binn_load`). Refused until the per-call reborrow hoist exists
    /// (R406-2: wave-6o's row).
    OptionRootMultiView,
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
            Self::OptionRootMultiView => "pair-disjointness-unproved:option-root-multi-view",
        }
    }
}

/// The provenance class of one call argument, read in the caller's body.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RootClass {
    /// A pointer local whose every assignment is an allocator result (or
    /// null) and whose own address is never taken: it names one fresh block.
    FreshAlloc(HirId),
    /// A view into a stack object of the caller — an array / struct / scalar
    /// `let` local, or a parameter's own slot (`&mut param`).
    StackObject(HirId),
    /// A parameter's VALUE, fixed at entry (never reassigned, address never
    /// taken), or a place inside its pointee: storage that existed at entry.
    EntryStorage(HirId),
    Unknown,
}

impl RootClass {
    fn is_fresh_object(self) -> bool {
        matches!(self, Self::FreshAlloc(_) | Self::StackObject(_))
    }

    fn object_id(self) -> Option<HirId> {
        match self {
            Self::FreshAlloc(id) | Self::StackObject(id) | Self::EntryStorage(id) => Some(id),
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
    /// The innermost local binding the argument expression is built from
    /// (through derefs, fields, indices, casts and method receivers), when
    /// there is one. Used only to refuse two views under one nullable root.
    syntactic_root: Option<HirId>,
    /// That root is `is_null`-tested or null-assigned in the caller.
    nullable_root: bool,
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
    ledger: RefCell<Vec<LedgerRow>>,
}

impl PairDisjointnessIndex {
    /// `indirect_calls`: the closed-world resolution of every MIR call site
    /// (the P-b fn-pointer web's inventory, attested only under the frozen
    /// benchmark graph); `None` admits no call through a function pointer.
    pub(crate) fn derive(
        program: &RustProgram<'_>,
        mut_facts: &MutFacts,
        indirect_calls: Option<&[super::lifetime::MirCallTargetSite]>,
        null_tested: &FxHashSet<HirId>,
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
            let (classes, null_assigned) =
                classify_locals_with_nullability(tcx, typeck, body, &allocators, caller);
            let mut collector = CallCollector {
                tcx,
                typeck,
                locals: &local_functions,
                classes: &classes,
                null_tested,
                null_assigned: &null_assigned,
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

        Self {
            sites,
            type_rule: type_verdicts,
            immutable_formals,
            ledger: RefCell::new(Vec::new()),
        }
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
        if let (Some(ra), Some(rb)) = (a.syntactic_root, b.syntactic_root)
            && ra == rb
            && (a.nullable_root || b.nullable_root)
        {
            return Err(Unproved::OptionRootMultiView);
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
        RootClass::FreshAlloc(_) | RootClass::StackObject(_) | RootClass::EntryStorage(_) => {
            (fresh.object_id() != other.object_id()).then_some(CertificateKind::DistinctRoots)
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
    wrappers: FxHashSet<DefId>,
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
    fn is_allocator_call(&self, tcx: TyCtxt<'_>, function: LocalDefId, expr: &Expr<'_>) -> bool {
        let ExprKind::Call(callee, _) = &peel_casts(expr).kind else {
            return false;
        };
        if let Some(did) = callee_def_id(callee) {
            return self.wrappers.contains(&did) || Self::is_libc_allocator(tcx, did);
        }
        // A call through a function pointer: every closed-world target must be
        // an allocator wrapper already admitted. Foreign targets (libc
        // `malloc` stored in a static, as binn does) are not in the web's
        // local inventory, so such a call has no resolved target and is NOT
        // admitted — a typed residue, not a gap in the closed world.
        let Some(sites) = self.indirect_calls else {
            return false;
        };
        let span = expr.span.source_callsite();
        let targets = sites
            .iter()
            .filter(|site| site.caller == function && site.span.source_callsite().contains(span))
            .map(|site| site.callee.to_def_id())
            .collect::<Vec<_>>();
        !targets.is_empty() && targets.iter().all(|target| self.wrappers.contains(target))
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
        wrappers: FxHashSet::default(),
        indirect_calls,
    };
    loop {
        let before = oracle.wrappers.len();
        for &function in functions {
            if oracle.wrappers.contains(&function.to_def_id()) {
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
            let all_fresh = returns.returns.iter().all(|expr| {
                is_null_literal(expr)
                    || oracle.is_allocator_call(tcx, function, expr)
                    || resolved_local(peel_casts(expr)).is_some_and(|binding| {
                        matches!(classes.get(&binding), Some(RootClass::FreshAlloc(_)))
                    })
            });
            if all_fresh {
                oracle.wrappers.insert(function.to_def_id());
            }
        }
        if oracle.wrappers.len() == before {
            return oracle;
        }
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
    Allocator,
    Other,
}

fn classify_locals<'tcx>(
    tcx: TyCtxt<'tcx>,
    typeck: &TypeckResults<'tcx>,
    body: &'tcx rustc_hir::Body<'tcx>,
    allocators: &AllocatorOracle<'_>,
    function: LocalDefId,
) -> FxHashMap<HirId, RootClass> {
    classify_locals_with_nullability(tcx, typeck, body, allocators, function).0
}

/// [`classify_locals`] plus the bindings that are assigned a null literal
/// anywhere in the body (the other half of the Option-form evidence; the
/// `is_null` half comes from the emitability facts).
fn classify_locals_with_nullability<'tcx>(
    tcx: TyCtxt<'tcx>,
    typeck: &TypeckResults<'tcx>,
    body: &'tcx rustc_hir::Body<'tcx>,
    allocators: &AllocatorOracle<'_>,
    function: LocalDefId,
) -> (FxHashMap<HirId, RootClass>, FxHashSet<HirId>) {
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

    let null_assigned = facts
        .iter()
        .filter(|(_, fact)| fact.assignments.contains(&AssignKind::Null))
        .map(|(hir_id, _)| *hir_id)
        .collect::<FxHashSet<_>>();
    let classes = facts
        .into_iter()
        .map(|(hir_id, fact)| {
            let class = if fact.is_pointer {
                if fact.address_taken {
                    RootClass::Unknown
                } else if fact.is_param {
                    if fact.assignments.is_empty() {
                        RootClass::EntryStorage(hir_id)
                    } else {
                        RootClass::Unknown
                    }
                } else {
                    let fresh = fact
                        .assignments
                        .iter()
                        .all(|kind| matches!(kind, AssignKind::Null | AssignKind::Allocator))
                        && fact
                            .assignments
                            .iter()
                            .any(|kind| matches!(kind, AssignKind::Allocator));
                    if fresh {
                        RootClass::FreshAlloc(hir_id)
                    } else {
                        RootClass::Unknown
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
    (classes, null_assigned)
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
        } else if self
            .allocators
            .is_allocator_call(self.tcx, self.function, rhs)
        {
            AssignKind::Allocator
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
    null_tested: &'a FxHashSet<HirId>,
    null_assigned: &'a FxHashSet<HirId>,
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
                    let syntactic_root = syntactic_root(arg);
                    let nullable_root = syntactic_root.is_some_and(|root| {
                        self.null_tested.contains(&root) || self.null_assigned.contains(&root)
                    });
                    ArgRecord {
                        index,
                        span: arg.span,
                        class,
                        place,
                        syntactic_root,
                        nullable_root,
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

/// The innermost local binding an argument expression is built from, walking
/// derefs, fields, indices, address-ofs, casts and method receivers (the
/// emitability `place_root` walk).
fn syntactic_root(expr: &Expr<'_>) -> Option<HirId> {
    let mut cur = expr;
    loop {
        match &cur.kind {
            ExprKind::Unary(UnOp::Deref, base)
            | ExprKind::Field(base, _)
            | ExprKind::Index(base, _, _)
            | ExprKind::AddrOf(_, _, base)
            | ExprKind::Cast(base, _)
            | ExprKind::DropTemps(base) => cur = base,
            ExprKind::MethodCall(_, receiver, _, _) => cur = receiver,
            _ => return resolved_local(cur),
        }
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
            certify_roots(RootClass::FreshAlloc(a), RootClass::EntryStorage(b)),
            Some(CertificateKind::DistinctRoots)
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
            certify_roots(RootClass::FreshAlloc(a), RootClass::Unknown),
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
