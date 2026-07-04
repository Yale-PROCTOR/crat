//! §NB0 — the unified BO boundary table.
//!
//! ONE registry mapping every callee name the BO analyses know anything about
//! to its roles, unifying knowledge that previously lived in three legacy
//! lists (plus a fourth found during NB0 recon):
//!   1. `sources.rs::ALLOCATOR_NAMES` (BO malloc-source slot walk),
//!   2. production `borrow/mod.rs::is_borrowing_method` (3 names),
//!   3. production `borrow/lifetime_flow.rs` whitelists (pointer arithmetic,
//!      slice views/indexing/splits, C-string search, null constructors),
//!   4. `call_graph.rs`'s Alloc/Dealloc monotonicity ranking lists.
//! Production `borrow/` keeps its own copies untouched (NB plan prime
//! directive); the subset tests below pin its lists as literals.
//!
//! Data-only in NB0: BO's `infer/boundary/{libc,library}.rs` hooks keep their
//! dispatch arms (behavior), and consistency tests enforce that every
//! dispatched name appears here with the matching role. Rewiring dispatch
//! through the table is NB3/NB4's job, when roles become behavior.
//!
//! Matching disciplines deliberately DIFFER per row (`Matcher`): a naive
//! name-union would silently change semantics — e.g. `sources.rs` insists on
//! a crate-local `Node::ForeignItem` (a crate-local fn merely *named*
//! `malloc` is not a source), while production's C-string entries match by
//! bare name across every callee kind. Type guards (slice-shaped args/dests)
//! are recorded in `note` as documentation, not enforced here.

/// Semantic role of a callee, per the NB0 taxonomy (source / sink /
/// loan-creating / provenance-preserving flow / unknown), refined by the
/// concrete role kinds the legacy lists actually encode.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Role {
    /// Allocates owned heap; result is an ownership source (selector-gated).
    Source,
    /// Consumes/deallocates its pointer argument (hard use-version owning).
    Sink,
    /// Byte-level transfer through pointer args (BO `memset` hook).
    FlowTransfer,
    /// Reborrow-like method: creates a loan of arg0 for the destination
    /// (production "borrowing method"; BO `offset` hook's lend+borrow).
    LoanCreating,
    /// Flows arg0's provenance to the return value (pointer arithmetic,
    /// slice views/indexing, C-string search).
    ///
    /// ⚠ NB3/NB4 consumers: several rows carrying this role are TYPE-GUARDED
    /// in production (slice views require a slice-like-ref destination;
    /// slice indexing and `memchr` require a slice-like-ref arg0 — see each
    /// row's `note`). Consuming the role WITHOUT re-implementing the guard
    /// over-matches production semantics. The guards live only in `note`
    /// because NB0 is data-only; they MUST become code when roles become
    /// behavior.
    ProvenanceFlow,
    /// Recognized only to SUPPRESS unknown-target poisoning; adds no flow
    /// edge (production slice-split handling).
    FlowSuppression,
    /// Produces a fresh pointer with no provenance (`null`/`null_mut`).
    NullConstructor,
    /// BO boundary hook lends the argument without borrowing a destination
    /// (`is_null`).
    Lend,
    /// BO boundary hook deliberately ignores the argument (`addr`).
    Ignore,
}

/// The match discipline a row's origin list uses. Recorded per row so the
/// unification does not flatten semantics.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Matcher {
    /// Crate-local `Node::ForeignItem` with this ident (extern "C" decl).
    /// Used by `sources.rs::is_allocator_call`, BO's `libc_call` dispatch,
    /// and `call_graph.rs`'s monotonicity ranking.
    ForeignC,
    /// Non-local `DefId` + `DefKind::AssocFn` + bare item name
    /// (production `is_borrowing_method` and most `lifetime_flow` lists).
    RustLibAssoc,
    /// Non-local `DefId` + bare item name, NO def-kind check
    /// (production slice-view constructors and null constructors).
    RustLibNonLocal,
    /// Bare name across every callee kind — local fns, impl methods,
    /// stdlib, and extern decls alike (production C-string/memchr lists).
    AnyName,
    /// Non-local `DefId` whose `def_path` starts at `TypeNs("ptr")` AND whose
    /// 4th path element (`def_path.data.get(3)`) is a `ValueNs` with this
    /// name — the exact discipline of BO's `library_call` dispatch in
    /// `infer/boundary/library.rs:20-59`; anything else there falls through
    /// to `unknown_call`. Do not loosen to "starts at `ptr` + bare name".
    RustPtrPath,
}

pub(crate) struct Entry {
    pub name: &'static str,
    pub matcher: Matcher,
    pub roles: &'static [Role],
    /// Guard conditions / provenance notes carried as documentation (not
    /// enforced by the table). Read by humans and audits, not by code.
    #[allow(dead_code)]
    pub note: &'static str,
}

const fn entry(
    name: &'static str,
    matcher: Matcher,
    roles: &'static [Role],
    note: &'static str,
) -> Entry {
    Entry {
        name,
        matcher,
        roles,
        note,
    }
}

/// The unified table. Contents are EXACTLY the union of the four legacy
/// lists plus BO's own boundary hooks — NB0's non-goal forbids new names
/// (expansion changes fragment F and is its own decision).
pub(crate) const TABLE: &[Entry] = &[
    // --- extern "C" callees (ForeignC): BO libc hooks + sources.rs +
    // --- call_graph.rs monotonicity ranking.
    entry("malloc", Matcher::ForeignC, &[Role::Source], "libc.rs call_malloc; sources.rs; call_graph Alloc"),
    entry("calloc", Matcher::ForeignC, &[Role::Source], "libc.rs call_calloc; sources.rs; call_graph Alloc"),
    entry(
        "strdup",
        Matcher::ForeignC,
        &[Role::Source],
        "libc.rs call_strdup; sources.rs. INTENTIONALLY absent from call_graph's \
         Alloc ranking (monotonicity only; the lists need not be identical — see \
         the sources.rs coupling note). Do NOT unify.",
    ),
    entry(
        "realloc",
        Matcher::ForeignC,
        &[Role::Source, Role::Sink],
        "libc.rs call_realloc: source(destination) + sink(arg0); sources.rs; call_graph Alloc. \
         Sink owning selector-retractable since NB-F.",
    ),
    entry(
        "free",
        Matcher::ForeignC,
        &[Role::Sink],
        "libc.rs call_free: sink(arg0); call_graph Dealloc. \
         Sink owning selector-retractable since NB-F (leak-the-free).",
    ),
    entry("memset", Matcher::ForeignC, &[Role::FlowTransfer], "libc.rs call_memset: transfer(dest, arg)"),
    // --- BO library hooks (RustPtrPath: def_path starts at TypeNs("ptr")).
    entry(
        "offset",
        Matcher::RustPtrPath,
        &[Role::LoanCreating],
        "library.rs call_offset: lend(arg) + borrow(dest); release-active assert!(!is_ref)",
    ),
    entry(
        "is_null",
        Matcher::RustPtrPath,
        &[Role::Lend],
        "library.rs call_is_null: lend(arg); §NB-F an is_ref arg has its leading \
         outer-reference slot peeled before the lend (the former uthash tripwire \
         assert!(!is_ref) is gone)",
    ),
    entry("addr", Matcher::RustPtrPath, &[Role::Ignore], "library.rs call_addr: arg ignored"),
    // --- production is_borrowing_method (borrow/mod.rs:779-785): reborrow of
    // --- arg0 into the destination = loan creation.
    entry("offset", Matcher::RustLibAssoc, &[Role::LoanCreating], "is_borrowing_method"),
    entry("as_ptr", Matcher::RustLibAssoc, &[Role::LoanCreating], "is_borrowing_method"),
    entry("as_mut_ptr", Matcher::RustLibAssoc, &[Role::LoanCreating], "is_borrowing_method"),
    // --- production lifetime_flow pointer arithmetic (:1314-1334).
    entry("wrapping_offset", Matcher::RustLibAssoc, &[Role::ProvenanceFlow], "lifetime_flow arith: arg0 -> return"),
    entry("byte_offset", Matcher::RustLibAssoc, &[Role::ProvenanceFlow], "lifetime_flow arith: arg0 -> return"),
    entry("wrapping_byte_offset", Matcher::RustLibAssoc, &[Role::ProvenanceFlow], "lifetime_flow arith: arg0 -> return"),
    entry("add", Matcher::RustLibAssoc, &[Role::ProvenanceFlow], "lifetime_flow arith: arg0 -> return"),
    entry("wrapping_add", Matcher::RustLibAssoc, &[Role::ProvenanceFlow], "lifetime_flow arith: arg0 -> return"),
    entry("sub", Matcher::RustLibAssoc, &[Role::ProvenanceFlow], "lifetime_flow arith: arg0 -> return"),
    entry("wrapping_sub", Matcher::RustLibAssoc, &[Role::ProvenanceFlow], "lifetime_flow arith: arg0 -> return"),
    // --- production lifetime_flow slice views (:1336-1350; RustLib without a
    // --- def-kind check; guarded on a slice-like-ref destination type).
    entry("cast_slice", Matcher::RustLibNonLocal, &[Role::ProvenanceFlow], "lifetime_flow slice view; dest must be slice-like ref"),
    entry("cast_slice_mut", Matcher::RustLibNonLocal, &[Role::ProvenanceFlow], "lifetime_flow slice view; dest must be slice-like ref"),
    entry("from_raw_parts", Matcher::RustLibNonLocal, &[Role::ProvenanceFlow], "lifetime_flow slice view; dest must be slice-like ref"),
    entry("from_raw_parts_mut", Matcher::RustLibNonLocal, &[Role::ProvenanceFlow], "lifetime_flow slice view; dest must be slice-like ref"),
    // --- production lifetime_flow slice indexing (:1352-1366; arg0 must be
    // --- slice-like ref).
    entry("index", Matcher::RustLibAssoc, &[Role::ProvenanceFlow], "lifetime_flow slice index; arg0 must be slice-like ref"),
    entry("index_mut", Matcher::RustLibAssoc, &[Role::ProvenanceFlow], "lifetime_flow slice index; arg0 must be slice-like ref"),
    entry("get_unchecked", Matcher::RustLibAssoc, &[Role::ProvenanceFlow], "lifetime_flow slice index; arg0 must be slice-like ref"),
    entry("get_unchecked_mut", Matcher::RustLibAssoc, &[Role::ProvenanceFlow], "lifetime_flow slice index; arg0 must be slice-like ref"),
    // --- production lifetime_flow slice splits (:1368-1382; suppression only
    // --- — no flow edge; arg0 slice-like ref AND dest a slice-ref pair).
    entry("split_at", Matcher::RustLibAssoc, &[Role::FlowSuppression], "lifetime_flow split; suppresses poisoning, adds no edge"),
    entry("split_at_mut", Matcher::RustLibAssoc, &[Role::FlowSuppression], "lifetime_flow split; suppresses poisoning, adds no edge"),
    entry("split_at_unchecked", Matcher::RustLibAssoc, &[Role::FlowSuppression], "lifetime_flow split; suppresses poisoning, adds no edge"),
    entry("split_at_mut_unchecked", Matcher::RustLibAssoc, &[Role::FlowSuppression], "lifetime_flow split; suppresses poisoning, adds no edge"),
    // --- production lifetime_flow C-string search (:1384-1408; bare name
    // --- across EVERY callee kind — no foreign/local gate at all).
    entry("strchr", Matcher::AnyName, &[Role::ProvenanceFlow], "lifetime_flow C-string search: arg0 -> return"),
    entry("strrchr", Matcher::AnyName, &[Role::ProvenanceFlow], "lifetime_flow C-string search: arg0 -> return"),
    entry("strstr", Matcher::AnyName, &[Role::ProvenanceFlow], "lifetime_flow C-string search: arg0 -> return"),
    entry("memchr", Matcher::AnyName, &[Role::ProvenanceFlow], "lifetime_flow memchr; arg0 must be slice-like ref"),
    // --- production lifetime_flow null constructors (:1306-1312).
    entry("null", Matcher::RustLibNonLocal, &[Role::NullConstructor], "lifetime_flow: fresh pointer, no provenance"),
    entry("null_mut", Matcher::RustLibNonLocal, &[Role::NullConstructor], "lifetime_flow: fresh pointer, no provenance"),
];

/// The allocator names `sources.rs` consumes: ForeignC rows carrying
/// `Role::Source`. Must stay a subset of the libc boundary hook's source
/// arms (consistency-tested below).
pub(crate) fn sources_foreign() -> impl Iterator<Item = &'static str> {
    TABLE
        .iter()
        .filter(|e| e.matcher == Matcher::ForeignC && e.roles.contains(&Role::Source))
        .map(|e| e.name)
}

/// Look up a row by (name, matcher).
pub(crate) fn lookup(name: &str, matcher: Matcher) -> Option<&'static Entry> {
    TABLE
        .iter()
        .find(|e| e.name == name && e.matcher == matcher)
}

// ---------------------------------------------------------------------------
// PRECONDITION for every test below: the pinned production name lists are
// literals copied from `analyses/borrow/` (file:line noted per test), valid
// while the production `borrow/` + `ownership/` freeze (NB plan prime
// directive, docs/agents/tasks/2026-07-03-bo-native-borrow-plan.md §0) holds.
// If that freeze is ever lifted, RE-AUDIT the pins against the live code
// before trusting either a failure or a pass of these tests.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod tests {
    use super::*;

    fn has_role(name: &str, matcher: Matcher, role: Role) -> bool {
        lookup(name, matcher).is_some_and(|e| e.roles.contains(&role))
    }

    /// Structural sanity: (name, matcher) unique, no empty role sets.
    #[test]
    fn nb0_table_self_consistent() {
        for (i, e) in TABLE.iter().enumerate() {
            assert!(!e.roles.is_empty(), "empty role set for `{}`", e.name);
            assert!(
                !TABLE[..i]
                    .iter()
                    .any(|p| p.name == e.name && p.matcher == e.matcher),
                "duplicate row ({}, {:?})",
                e.name,
                e.matcher
            );
        }
        assert!(!TABLE.is_empty(), "the table must not be a stub");
    }

    /// Legacy list 1 — `sources.rs::ALLOCATOR_NAMES` (pre-NB0 const, formerly
    /// sources.rs:46): every allocator is a ForeignC Source row, and
    /// `sources_foreign()` reproduces the set exactly.
    #[test]
    fn nb0_subset_sources_allocators() {
        let legacy = ["malloc", "calloc", "realloc", "strdup"];
        for name in legacy {
            assert!(
                has_role(name, Matcher::ForeignC, Role::Source),
                "`{name}` must be a ForeignC Source row"
            );
        }
        let mut derived: Vec<_> = sources_foreign().collect();
        derived.sort_unstable();
        let mut expected = legacy;
        expected.sort_unstable();
        assert_eq!(derived, expected, "sources_foreign() must equal the legacy set");
    }

    /// Legacy list 2 — production `borrow/mod.rs:779-785 is_borrowing_method`
    /// (non-local AssocFn, bare name): the 3 names are LoanCreating.
    #[test]
    fn nb0_subset_is_borrowing_method() {
        for name in ["offset", "as_ptr", "as_mut_ptr"] {
            assert!(
                has_role(name, Matcher::RustLibAssoc, Role::LoanCreating),
                "`{name}` must be a RustLibAssoc LoanCreating row (is_borrowing_method)"
            );
        }
    }

    /// Legacy list 3 — production `borrow/lifetime_flow.rs` whitelists, full
    /// union, per classifier group with its match discipline:
    /// pointer arithmetic :1314-1334 (RustLib+AssocFn), slice views
    /// :1336-1350 (RustLib, no def-kind check, dest-type guard), slice index
    /// :1352-1366 (RustLib+AssocFn, arg0 guard), splits :1368-1382
    /// (RustLib+AssocFn, guards, suppression-only), C-string search
    /// :1384-1393 + :1406-1408 (bare name, ANY callee kind), memchr
    /// :1395-1404 (bare name, any kind, arg0 guard), null constructors
    /// :1306-1312 (non-local only).
    #[test]
    fn nb0_subset_lifetime_flow() {
        let arith = [
            "wrapping_offset",
            "byte_offset",
            "wrapping_byte_offset",
            "add",
            "wrapping_add",
            "sub",
            "wrapping_sub",
        ];
        for name in arith {
            assert!(
                has_role(name, Matcher::RustLibAssoc, Role::ProvenanceFlow),
                "`{name}` must be RustLibAssoc ProvenanceFlow (pointer arithmetic)"
            );
        }
        for name in ["cast_slice", "cast_slice_mut", "from_raw_parts", "from_raw_parts_mut"] {
            assert!(
                has_role(name, Matcher::RustLibNonLocal, Role::ProvenanceFlow),
                "`{name}` must be RustLibNonLocal ProvenanceFlow (slice view)"
            );
        }
        for name in ["index", "index_mut", "get_unchecked", "get_unchecked_mut"] {
            assert!(
                has_role(name, Matcher::RustLibAssoc, Role::ProvenanceFlow),
                "`{name}` must be RustLibAssoc ProvenanceFlow (slice index)"
            );
        }
        for name in ["split_at", "split_at_mut", "split_at_unchecked", "split_at_mut_unchecked"] {
            assert!(
                has_role(name, Matcher::RustLibAssoc, Role::FlowSuppression),
                "`{name}` must be RustLibAssoc FlowSuppression (slice split)"
            );
        }
        for name in ["strchr", "strrchr", "strstr", "memchr"] {
            assert!(
                has_role(name, Matcher::AnyName, Role::ProvenanceFlow),
                "`{name}` must be AnyName ProvenanceFlow (C-string search)"
            );
        }
        for name in ["null", "null_mut"] {
            assert!(
                has_role(name, Matcher::RustLibNonLocal, Role::NullConstructor),
                "`{name}` must be RustLibNonLocal NullConstructor"
            );
        }
    }

    /// Legacy list 4 (NB0 recon extension; zero new names) —
    /// `call_graph.rs:90-104` monotonicity ranking: Alloc = malloc, calloc,
    /// realloc; Dealloc = free; both ForeignC. NOTE: `strdup` is
    /// INTENTIONALLY absent from call_graph's Alloc list (it ranks
    /// alloc/dealloc monotonicity only — per the coupling note in
    /// `sources.rs`, the lists need not be identical). Do NOT "fix" that by
    /// adding strdup to call_graph; the subset direction below is
    /// legacy ⊆ table, which holds regardless.
    #[test]
    fn nb0_subset_call_graph_monotonicity() {
        for name in ["malloc", "calloc", "realloc"] {
            assert!(
                has_role(name, Matcher::ForeignC, Role::Source),
                "`{name}` (call_graph Alloc) must be a ForeignC Source row"
            );
        }
        assert!(
            has_role("free", Matcher::ForeignC, Role::Sink),
            "`free` (call_graph Dealloc) must be a ForeignC Sink row"
        );
    }

    /// BO libc boundary hooks (`infer/boundary/libc.rs:27-38` dispatch):
    /// every dispatched name appears with exactly the hook's role(s).
    #[test]
    fn nb0_consistency_libc_dispatch() {
        let expect: &[(&str, &[Role])] = &[
            ("malloc", &[Role::Source]),
            ("calloc", &[Role::Source]),
            ("strdup", &[Role::Source]),
            ("realloc", &[Role::Source, Role::Sink]),
            ("free", &[Role::Sink]),
            ("memset", &[Role::FlowTransfer]),
        ];
        for (name, roles) in expect {
            let e = lookup(name, Matcher::ForeignC)
                .unwrap_or_else(|| panic!("libc hook `{name}` missing a ForeignC row"));
            assert_eq!(e.roles, *roles, "role mismatch for libc hook `{name}`");
        }
    }

    /// BO library boundary hooks (`infer/boundary/library.rs:20-59` dispatch,
    /// def_path `ptr::*`): offset / is_null / addr with the hook semantics.
    #[test]
    fn nb0_consistency_library_dispatch() {
        let expect: &[(&str, &[Role])] = &[
            ("offset", &[Role::LoanCreating]),
            ("is_null", &[Role::Lend]),
            ("addr", &[Role::Ignore]),
        ];
        for (name, roles) in expect {
            let e = lookup(name, Matcher::RustPtrPath)
                .unwrap_or_else(|| panic!("library hook `{name}` missing a RustPtrPath row"));
            assert_eq!(e.roles, *roles, "role mismatch for library hook `{name}`");
        }
    }
}
