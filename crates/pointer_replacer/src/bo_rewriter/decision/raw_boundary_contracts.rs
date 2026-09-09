//! Exact-symbol, per-argument contracts for raw boundaries.
//!
//! This emission table is independent of the frozen analysis table. Where a
//! name exists in both, tests require role agreement; production never widens
//! an analysis row or matches a same-spelled local body.

use super::raw_boundary::{ForeignSymbolKey, RawMutability, RawTargetType};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RetentionContract {
    NoRetain,
    Retains,
    Unknown,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PointeeAccess {
    None,
    Read,
    Write,
    /// Opaque stdio state may change through the FILE* while the pointer is
    /// not retained. This is intentionally distinct from an ordinary write.
    Stream,
    Lifecycle,
}

impl PointeeAccess {
    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::None => "none",
            Self::Read => "read",
            Self::Write => "write",
            Self::Stream => "stream",
            Self::Lifecycle => "lifecycle",
        }
    }
}

/// How many elements a foreign position's contract consumes, and where that
/// number comes from (§39 addendum 272, R272-1(b)).
///
/// **This is the axis the `&c_void` finding generalises to.** An emitted `&T`
/// carries provenance over exactly `size_of::<T>()` bytes, so a THIN reference
/// delivered to any position that consumes more than one element is the same
/// Stacked-Borrows extent violation `held:void-pointee` repairs — the pointee
/// merely happens to be typed instead of opaque. `strlen(str)` on a
/// `&libc::c_char` is the worked example: a one-byte retag read to the NUL.
///
/// The seat's taxonomy is one-element / NUL-terminated / byte-count /
/// element-count / unmodeled-foreign. Two more are recorded because the table
/// has them and forcing them into the five would misstate the contract:
/// `UnboundedWrite` (a destination whose size is set by the SOURCE, never
/// stated at the call — `strcpy`, `strcat`, `sprintf`, the scanf `%s` tail)
/// and `Lifecycle` (a position that consumes an allocation rather than
/// accessing elements). `unmodeled-foreign` is not a value here: it is the
/// absence of a row, which `classify_contract` already reports as
/// `PositionUnmodeled`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ArgumentExtent {
    /// Exactly one `T`. The only extent a thin `&T` can carry.
    OneElement,
    /// Elements up to a NUL the callee finds. Unbounded from the caller's side.
    NulTerminated,
    /// A byte count stated at the call site.
    ByteCount,
    /// A count and an element size stated at the call site.
    ElementCount,
    /// A destination whose extent is set by the source, not by the call.
    UnboundedWrite,
    /// The allocation itself is consumed; no element access.
    Lifecycle,
    /// No extent decided yet. A row may not ship in this state; the table
    /// completeness control below is what enforces that.
    Unclassified,
}

impl ArgumentExtent {
    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::OneElement => "one-element",
            Self::NulTerminated => "nul-terminated",
            Self::ByteCount => "byte-count",
            Self::ElementCount => "element-count",
            Self::UnboundedWrite => "unbounded-write",
            Self::Lifecycle => "lifecycle",
            Self::Unclassified => "unclassified",
        }
    }

    /// Can a THIN `&T` carry this position's extent? Only a single element
    /// can. Everything else needs a slice, a stated count, or a hold.
    pub(crate) fn fits_one_element(self) -> bool {
        matches!(self, Self::OneElement | Self::Lifecycle)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum OwnershipContract {
    BorrowView,
    Consume,
    Produce,
    AtomicSourceSink,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ArgumentContract {
    pub retention: RetentionContract,
    pub access: PointeeAccess,
    pub ownership: OwnershipContract,
    /// R272-1(b). How many elements this position consumes.
    pub extent: ArgumentExtent,
    /// Function-level relation: a non-null returned view derives from this
    /// zero-based argument. Consumers must compare it with their own argument
    /// index; its presence does not make every argument the returned parent.
    pub returns_alias_of: Option<usize>,
    pub provenance: &'static str,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ContractFailure {
    NotForeign,
    AbiMismatch,
    SignatureMismatch,
    PositionUnmodeled,
    MutabilityMismatch,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Position {
    Exact(usize),
}

impl Position {
    fn matches(self, index: usize) -> bool {
        match self {
            Self::Exact(expected) => index == expected,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ContractRow {
    symbol: &'static str,
    position: Position,
    access: PointeeAccess,
    ownership: OwnershipContract,
    returns_alias_of: Option<usize>,
    extent: ArgumentExtent,
}

impl ContractRow {
    /// Every row states its extent explicitly. The base constructors leave it
    /// `Unclassified` on purpose, so a row added without one is caught by the
    /// completeness control rather than inheriting a plausible default.
    const fn with(self, extent: ArgumentExtent) -> Self {
        Self { extent, ..self }
    }
}

const fn row(symbol: &'static str, position: usize, access: PointeeAccess) -> ContractRow {
    ContractRow {
        symbol,
        position: Position::Exact(position),
        access,
        ownership: OwnershipContract::BorrowView,
        returns_alias_of: None,
        extent: ArgumentExtent::Unclassified,
    }
}

/// Only existing table symbols are annotated. Primary source: WG14 N1570
/// <https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf>:
/// fgets §7.21.7.2 p3; strcpy §7.24.2.3 p3; strncpy §7.24.2.4 p4;
/// strcat §7.24.3.1 p3; strncat §7.24.3.2 p3;
/// strchr §7.24.5.2 p3; strstr §7.24.5.7 p3.
/// The copy/concatenation functions return argument 0 itself. fgets may return
/// null; the search functions may return null or an interior view of argument
/// 0. This records lineage metadata without changing the access/retention rule.
const fn return_alias_row(
    symbol: &'static str,
    position: usize,
    access: PointeeAccess,
) -> ContractRow {
    ContractRow {
        returns_alias_of: Some(0),
        ..row(symbol, position, access)
    }
}

/// Per-argument no-retention contracts. Fixed positions and variadic positions
/// are explicit so a destination never inherits a source's access mode.
const TABLE: &[ContractRow] = &[
    row("fdopen", 1, PointeeAccess::Read).with(ArgumentExtent::NulTerminated),
    return_alias_row("fgets", 0, PointeeAccess::Write).with(ArgumentExtent::ByteCount),
    row("fopen", 0, PointeeAccess::Read).with(ArgumentExtent::NulTerminated),
    row("fopen", 1, PointeeAccess::Read).with(ArgumentExtent::NulTerminated),
    row("fprintf", 1, PointeeAccess::Read).with(ArgumentExtent::NulTerminated),
    row("fputs", 0, PointeeAccess::Read).with(ArgumentExtent::NulTerminated),
    row("fscanf", 1, PointeeAccess::Read).with(ArgumentExtent::NulTerminated),
    row("getenv", 0, PointeeAccess::Read).with(ArgumentExtent::NulTerminated),
    row("glob", 0, PointeeAccess::Read).with(ArgumentExtent::NulTerminated),
    row("glob", 3, PointeeAccess::Write).with(ArgumentExtent::OneElement),
    row("lstat", 0, PointeeAccess::Read).with(ArgumentExtent::NulTerminated),
    row("lstat", 1, PointeeAccess::Write).with(ArgumentExtent::OneElement),
    row("open", 0, PointeeAccess::Read).with(ArgumentExtent::NulTerminated),
    row("perror", 0, PointeeAccess::Read).with(ArgumentExtent::NulTerminated),
    row("printf", 0, PointeeAccess::Read).with(ArgumentExtent::NulTerminated),
    row("scanf", 0, PointeeAccess::Read).with(ArgumentExtent::NulTerminated),
    row("snprintf", 0, PointeeAccess::Write).with(ArgumentExtent::ByteCount),
    row("snprintf", 2, PointeeAccess::Read).with(ArgumentExtent::NulTerminated),
    row("sprintf", 0, PointeeAccess::Write).with(ArgumentExtent::UnboundedWrite),
    row("sprintf", 1, PointeeAccess::Read).with(ArgumentExtent::NulTerminated),
    row("sscanf", 0, PointeeAccess::Read).with(ArgumentExtent::NulTerminated),
    row("sscanf", 1, PointeeAccess::Read).with(ArgumentExtent::NulTerminated),
    row("stat", 0, PointeeAccess::Read).with(ArgumentExtent::NulTerminated),
    row("stat", 1, PointeeAccess::Write).with(ArgumentExtent::OneElement),
    return_alias_row("strcat", 0, PointeeAccess::Write).with(ArgumentExtent::UnboundedWrite),
    return_alias_row("strcat", 1, PointeeAccess::Read).with(ArgumentExtent::NulTerminated),
    return_alias_row("strchr", 0, PointeeAccess::Read).with(ArgumentExtent::NulTerminated),
    row("strcmp", 0, PointeeAccess::Read).with(ArgumentExtent::NulTerminated),
    row("strcmp", 1, PointeeAccess::Read).with(ArgumentExtent::NulTerminated),
    return_alias_row("strcpy", 0, PointeeAccess::Write).with(ArgumentExtent::UnboundedWrite),
    return_alias_row("strcpy", 1, PointeeAccess::Read).with(ArgumentExtent::NulTerminated),
    row("strlen", 0, PointeeAccess::Read).with(ArgumentExtent::NulTerminated),
    row("strncasecmp", 0, PointeeAccess::Read).with(ArgumentExtent::ByteCount),
    row("strncasecmp", 1, PointeeAccess::Read).with(ArgumentExtent::ByteCount),
    return_alias_row("strncat", 0, PointeeAccess::Write).with(ArgumentExtent::UnboundedWrite),
    return_alias_row("strncat", 1, PointeeAccess::Read).with(ArgumentExtent::ByteCount),
    return_alias_row("strncpy", 0, PointeeAccess::Write).with(ArgumentExtent::ByteCount),
    return_alias_row("strncpy", 1, PointeeAccess::Read).with(ArgumentExtent::ByteCount),
    return_alias_row("strstr", 0, PointeeAccess::Read).with(ArgumentExtent::NulTerminated),
    return_alias_row("strstr", 1, PointeeAccess::Read).with(ArgumentExtent::NulTerminated),
    row("utime", 0, PointeeAccess::Read).with(ArgumentExtent::NulTerminated),
    row("utime", 1, PointeeAccess::Read).with(ArgumentExtent::OneElement),
    ContractRow {
        symbol: "fclose",
        position: Position::Exact(0),
        access: PointeeAccess::Lifecycle,
        ownership: OwnershipContract::Consume,
        returns_alias_of: None,
        extent: ArgumentExtent::Lifecycle,
    },
    ContractRow {
        symbol: "free",
        position: Position::Exact(0),
        access: PointeeAccess::Lifecycle,
        ownership: OwnershipContract::Consume,
        returns_alias_of: None,
        extent: ArgumentExtent::Lifecycle,
    },
    ContractRow {
        symbol: "realloc",
        position: Position::Exact(0),
        access: PointeeAccess::Lifecycle,
        ownership: OwnershipContract::AtomicSourceSink,
        returns_alias_of: None,
        extent: ArgumentExtent::Lifecycle,
    },
];

fn function_return_alias(symbol: &str) -> Option<usize> {
    TABLE
        .iter()
        .find(|row| row.symbol == symbol)
        .and_then(|row| row.returns_alias_of)
}

fn printf_tail_first(symbol: &str) -> Option<usize> {
    match symbol {
        "printf" => Some(1),
        "fprintf" | "sprintf" => Some(2),
        "snprintf" => Some(3),
        _ => None,
    }
}

fn scanf_tail_first(symbol: &str) -> Option<usize> {
    match symbol {
        "scanf" => Some(1),
        "fscanf" | "sscanf" => Some(2),
        _ => None,
    }
}

fn is_stdio_stream_position(symbol: &str, argument_index: usize) -> bool {
    matches!(
        (symbol, argument_index),
        ("fgetc", 0) | ("fgets", 2) | ("fprintf", 0) | ("fputs", 1) | ("fscanf", 0) | ("ungetc", 1)
    )
}

fn family_contract(
    symbol: &str,
    argument_index: usize,
    target: &RawTargetType,
) -> Result<Option<ArgumentContract>, ContractFailure> {
    // A pointer in a printf tail is a `%s` argument: read to the NUL. In a
    // scanf tail it is a destination whose size the call never states. A
    // stdio stream position is one `FILE`.
    let (access, extent, provenance) =
        if printf_tail_first(symbol).is_some_and(|first| argument_index >= first) {
            (
                PointeeAccess::Read,
                ArgumentExtent::NulTerminated,
                "pinned-libc-family-printf-tail-0.2.184",
            )
        } else if scanf_tail_first(symbol).is_some_and(|first| argument_index >= first) {
            (
                PointeeAccess::Write,
                ArgumentExtent::UnboundedWrite,
                "pinned-libc-family-scanf-tail-0.2.184",
            )
        } else if is_stdio_stream_position(symbol, argument_index) {
            (
                PointeeAccess::Stream,
                ArgumentExtent::OneElement,
                "pinned-libc-family-stdio-stream-0.2.184",
            )
        } else {
            return Ok(None);
        };
    if access == PointeeAccess::Write && target.mutability != RawMutability::Mut {
        return Err(ContractFailure::MutabilityMismatch);
    }
    Ok(Some(ArgumentContract {
        retention: RetentionContract::NoRetain,
        access,
        ownership: OwnershipContract::BorrowView,
        extent,
        returns_alias_of: function_return_alias(symbol),
        provenance,
    }))
}

pub(crate) fn classify_contract(
    callee: &ForeignSymbolKey,
    argument_index: usize,
    target: &RawTargetType,
) -> Result<ArgumentContract, ContractFailure> {
    if !callee.foreign {
        return Err(ContractFailure::NotForeign);
    }
    if !callee.abi.starts_with('C') {
        return Err(ContractFailure::AbiMismatch);
    }
    if callee.signature.is_empty() || target.rendered.is_empty() || target.pointee.is_empty() {
        return Err(ContractFailure::SignatureMismatch);
    }
    if let Some(contract) = family_contract(&callee.symbol, argument_index, target)? {
        return Ok(contract);
    }
    let Some(row) = TABLE
        .iter()
        .find(|row| row.symbol == callee.symbol && row.position.matches(argument_index))
    else {
        return Err(ContractFailure::PositionUnmodeled);
    };
    if matches!(row.access, PointeeAccess::Write | PointeeAccess::Lifecycle)
        && target.mutability != RawMutability::Mut
    {
        return Err(ContractFailure::MutabilityMismatch);
    }
    Ok(ArgumentContract {
        retention: RetentionContract::NoRetain,
        access: row.access,
        ownership: row.ownership,
        extent: row.extent,
        returns_alias_of: row.returns_alias_of,
        provenance: "pinned-libc-0.2.184",
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// R272-1(b) completeness. A row without a deliberate extent may not
    /// ship: the constructors leave `Unclassified` so that adding a symbol
    /// without deciding what its position consumes fails here rather than
    /// inheriting a plausible default.
    #[test]
    fn r272_every_contract_row_states_its_extent() {
        let unclassified = TABLE
            .iter()
            .filter(|row| row.extent == ArgumentExtent::Unclassified)
            .map(|row| (row.symbol, row.position))
            .collect::<Vec<_>>();
        assert!(
            unclassified.is_empty(),
            "contract rows without an extent: {unclassified:?}"
        );
    }

    /// The finding this column exists for, as a property rather than a list:
    /// only a one-element position can be reached by a THIN reference. Every
    /// other row is a position where a delivered `&T` carries less provenance
    /// than the callee consumes.
    #[test]
    fn r272_only_one_element_positions_fit_a_thin_reference() {
        for row in TABLE {
            assert_eq!(
                row.extent.fits_one_element(),
                matches!(
                    row.extent,
                    ArgumentExtent::OneElement | ArgumentExtent::Lifecycle
                ),
                "{} position {:?}",
                row.symbol,
                row.position
            );
        }
        assert!(
            TABLE
                .iter()
                .any(|row| row.extent == ArgumentExtent::NulTerminated),
            "the NUL-terminated family is the population R272-1 widened to"
        );
    }

    /// The two worked examples the seat named, pinned by symbol so a table
    /// edit that reclassified them would have to say so.
    #[test]
    fn r272_named_examples_keep_their_measured_extent() {
        let extent = |symbol: &str, position: usize| {
            TABLE
                .iter()
                .find(|row| row.symbol == symbol && row.position.matches(position))
                .unwrap_or_else(|| panic!("{symbol} position {position}"))
                .extent
        };
        // `buffer_new_with_copy(mut str: &libc::c_char)` then `strlen(str)`:
        // a one-byte retag read to the NUL.
        assert_eq!(extent("strlen", 0), ArgumentExtent::NulTerminated);
        // bzip2 `copyFileName::from` at `strncpy(to, from, 1024)`.
        assert_eq!(extent("strncpy", 1), ArgumentExtent::ByteCount);
        assert_eq!(extent("strncpy", 0), ArgumentExtent::ByteCount);
        // rgba `rgba_to_string::buf` at `snprintf(buf, len, ...)`.
        assert_eq!(extent("snprintf", 0), ArgumentExtent::ByteCount);
        // A destination sized by its source, never by the call.
        assert_eq!(extent("strcpy", 0), ArgumentExtent::UnboundedWrite);
        // The genuinely single-element positions.
        assert_eq!(extent("stat", 1), ArgumentExtent::OneElement);
        assert_eq!(extent("fclose", 0), ArgumentExtent::Lifecycle);
    }

    /// The family path carries an extent too, so a `%s` in a printf tail is
    /// not silently one element.
    #[test]
    fn r272_family_positions_state_their_extent() {
        let target = RawTargetType {
            rendered: "*const i8".to_owned(),
            pointee: "i8".to_owned(),
            mutability: RawMutability::Const,
            depth2: None,
        };
        let contract =
            classify_contract(&callee("printf", true), 1, &target).expect("printf tail is modeled");
        assert_eq!(contract.extent, ArgumentExtent::NulTerminated);
        let stream = RawTargetType {
            rendered: "*mut FILE".to_owned(),
            pointee: "FILE".to_owned(),
            mutability: RawMutability::Mut,
            depth2: None,
        };
        let contract =
            classify_contract(&callee("fprintf", true), 0, &stream).expect("stdio stream position");
        assert_eq!(contract.extent, ArgumentExtent::OneElement);
    }

    fn callee(name: &str, foreign: bool) -> ForeignSymbolKey {
        ForeignSymbolKey {
            symbol: name.to_owned(),
            path: format!("fixture::{name}"),
            abi: "C".to_owned(),
            signature: "fixture-signature".to_owned(),
            foreign,
        }
    }

    fn target(mutability: RawMutability) -> RawTargetType {
        RawTargetType {
            rendered: "*mut i8".to_owned(),
            pointee: "i8".to_owned(),
            mutability,
            depth2: None,
        }
    }

    #[test]
    fn rb_w1_exact_foreign_strlen_position_is_no_retain() {
        let got = classify_contract(&callee("strlen", true), 0, &target(RawMutability::Const));
        assert_eq!(
            got,
            Ok(ArgumentContract {
                retention: RetentionContract::NoRetain,
                access: PointeeAccess::Read,
                ownership: OwnershipContract::BorrowView,
                extent: ArgumentExtent::NulTerminated,
                returns_alias_of: None,
                provenance: "pinned-libc-0.2.184",
            })
        );
    }

    #[test]
    fn rb_w1b_strcpy_positions_keep_distinct_access_contracts() {
        let dest = classify_contract(&callee("strcpy", true), 0, &target(RawMutability::Mut));
        let source = classify_contract(&callee("strcpy", true), 1, &target(RawMutability::Const));
        assert_eq!(dest.expect("destination").access, PointeeAccess::Write);
        assert_eq!(source.expect("source").access, PointeeAccess::Read);
    }

    #[test]
    fn rb_retalias_metadata_is_exactly_the_seven_existing_symbols() {
        let expected = std::collections::BTreeSet::from([
            "fgets", "strcat", "strchr", "strcpy", "strncat", "strncpy", "strstr",
        ]);
        let observed = TABLE
            .iter()
            .filter(|row| row.returns_alias_of.is_some())
            .map(|row| row.symbol)
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(observed, expected);
        for row in TABLE {
            let relation = expected.contains(row.symbol).then_some(0);
            assert_eq!(row.returns_alias_of, relation, "{row:?}");
            let Position::Exact(argument_index) = row.position;
            let contract = classify_contract(
                &callee(row.symbol, true),
                argument_index,
                &target(RawMutability::Mut),
            )
            .expect("existing exact row");
            assert_eq!(contract.returns_alias_of, relation, "{row:?}");
            assert_eq!(contract.retention, RetentionContract::NoRetain);
            assert_eq!(contract.access, row.access);
            assert_eq!(contract.ownership, row.ownership);
        }
    }

    #[test]
    fn rb_retalias_source_argument_does_not_own_the_function_result() {
        for symbol in ["strcpy", "strstr"] {
            let parent =
                classify_contract(&callee(symbol, true), 0, &target(RawMutability::Mut)).unwrap();
            let source =
                classify_contract(&callee(symbol, true), 1, &target(RawMutability::Const)).unwrap();
            assert_eq!(parent.returns_alias_of, Some(0));
            assert_eq!(source.returns_alias_of, Some(0), "function-level relation");
            assert_ne!(
                source.returns_alias_of,
                Some(1),
                "argument 1 is not the returned parent"
            );
            assert_eq!(source.access, PointeeAccess::Read);
        }
        let stream =
            classify_contract(&callee("fgets", true), 2, &target(RawMutability::Mut)).unwrap();
        assert_eq!(
            stream.returns_alias_of,
            Some(0),
            "family rows retain the same function relation"
        );
        assert_ne!(stream.returns_alias_of, Some(2));
        assert_eq!(stream.access, PointeeAccess::Stream);
    }

    #[test]
    fn rb_retalias_lifecycle_contracts_have_no_borrowed_return_alias() {
        for (symbol, ownership) in [
            ("free", OwnershipContract::Consume),
            ("fclose", OwnershipContract::Consume),
            ("realloc", OwnershipContract::AtomicSourceSink),
        ] {
            let contract =
                classify_contract(&callee(symbol, true), 0, &target(RawMutability::Mut)).unwrap();
            assert_eq!(contract.returns_alias_of, None, "{symbol}");
            assert_eq!(contract.ownership, ownership);
        }
    }

    /// RB-X3 variadic-family witness. Mutation: moving the printf tail start
    /// past argument 2 changes this exact contract and is observed here.
    #[test]
    fn rb_x3_printf_and_scanf_variadic_tails_keep_distinct_access() {
        let printf = classify_contract(&callee("fprintf", true), 2, &target(RawMutability::Mut))
            .expect("fprintf variadic tail");
        assert_eq!(printf.retention, RetentionContract::NoRetain);
        assert_eq!(printf.access, PointeeAccess::Read);
        assert_eq!(printf.provenance, "pinned-libc-family-printf-tail-0.2.184");

        let scanf = classify_contract(&callee("fscanf", true), 2, &target(RawMutability::Mut))
            .expect("fscanf variadic tail");
        assert_eq!(scanf.retention, RetentionContract::NoRetain);
        assert_eq!(scanf.access, PointeeAccess::Write);
        assert_eq!(scanf.provenance, "pinned-libc-family-scanf-tail-0.2.184");
    }

    /// RB-X3 stream-position witness. Mutation: routing the FILE* position
    /// through the ordinary write rule loses the distinct stream receipt;
    /// routing fclose through it loses lifecycle-hard ownership.
    #[test]
    fn rb_x3_stdio_stream_positions_are_no_retain_but_fclose_is_lifecycle_hard() {
        let stream = classify_contract(&callee("fprintf", true), 0, &target(RawMutability::Mut))
            .expect("fprintf stream");
        assert_eq!(stream.retention, RetentionContract::NoRetain);
        assert_eq!(stream.access, PointeeAccess::Stream);
        assert_eq!(stream.provenance, "pinned-libc-family-stdio-stream-0.2.184");

        let close = classify_contract(&callee("fclose", true), 0, &target(RawMutability::Mut))
            .expect("fclose lifecycle");
        assert_eq!(close.access, PointeeAccess::Lifecycle);
        assert_eq!(close.ownership, OwnershipContract::Consume);
    }

    #[test]
    fn rb_n2b_same_spelled_local_never_matches_the_libc_contract() {
        assert_eq!(
            classify_contract(&callee("strlen", false), 0, &target(RawMutability::Const)),
            Err(ContractFailure::NotForeign)
        );
    }

    #[test]
    fn exact_rows_and_family_domains_are_pairwise_disjoint() {
        for (index, left) in TABLE.iter().enumerate() {
            for right in &TABLE[..index] {
                let overlap = left.symbol == right.symbol && left.position == right.position;
                assert!(!overlap, "overlapping contract rows: {left:?} / {right:?}");
            }
            for argument in 0..16 {
                let family = usize::from(
                    printf_tail_first(left.symbol).is_some_and(|first| argument >= first),
                ) + usize::from(
                    scanf_tail_first(left.symbol).is_some_and(|first| argument >= first),
                ) + usize::from(is_stdio_stream_position(left.symbol, argument));
                assert!(
                    family <= 1,
                    "overlapping family rules: {left:?} arg {argument}"
                );
                assert!(
                    family == 0 || !left.position.matches(argument),
                    "exact/family overlap: {left:?} arg {argument}"
                );
            }
        }
    }

    #[test]
    fn canonical_free_and_realloc_roles_agree_with_the_analysis_table() {
        use crate::analyses::borrow_ownership::boundary_table::{Matcher, Role, lookup};

        let free = lookup("free", Matcher::ForeignC).expect("canonical free");
        assert_eq!(free.roles, &[Role::Sink]);
        let realloc = lookup("realloc", Matcher::ForeignC).expect("canonical realloc");
        assert_eq!(realloc.roles, &[Role::Source, Role::Sink]);
        let free_contract = TABLE.iter().find(|row| row.symbol == "free").unwrap();
        let realloc_contract = TABLE.iter().find(|row| row.symbol == "realloc").unwrap();
        assert_eq!(free_contract.ownership, OwnershipContract::Consume);
        assert_eq!(
            realloc_contract.ownership,
            OwnershipContract::AtomicSourceSink
        );
    }
}
