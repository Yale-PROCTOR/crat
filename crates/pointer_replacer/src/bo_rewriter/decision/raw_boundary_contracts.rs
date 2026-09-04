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
    pub permits_shared_to_mut: bool,
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
}

const fn row(symbol: &'static str, position: usize, access: PointeeAccess) -> ContractRow {
    ContractRow {
        symbol,
        position: Position::Exact(position),
        access,
        ownership: OwnershipContract::BorrowView,
    }
}

/// Per-argument no-retention contracts. Fixed positions and variadic positions
/// are explicit so a destination never inherits a source's access mode.
const TABLE: &[ContractRow] = &[
    row("fdopen", 1, PointeeAccess::Read),
    row("fgets", 0, PointeeAccess::Write),
    row("fopen", 0, PointeeAccess::Read),
    row("fopen", 1, PointeeAccess::Read),
    row("fprintf", 1, PointeeAccess::Read),
    row("fputs", 0, PointeeAccess::Read),
    row("fscanf", 1, PointeeAccess::Read),
    row("getenv", 0, PointeeAccess::Read),
    row("glob", 0, PointeeAccess::Read),
    row("glob", 3, PointeeAccess::Write),
    row("lstat", 0, PointeeAccess::Read),
    row("lstat", 1, PointeeAccess::Write),
    row("open", 0, PointeeAccess::Read),
    row("perror", 0, PointeeAccess::Read),
    row("printf", 0, PointeeAccess::Read),
    row("scanf", 0, PointeeAccess::Read),
    row("snprintf", 0, PointeeAccess::Write),
    row("snprintf", 2, PointeeAccess::Read),
    row("sprintf", 0, PointeeAccess::Write),
    row("sprintf", 1, PointeeAccess::Read),
    row("sscanf", 0, PointeeAccess::Read),
    row("sscanf", 1, PointeeAccess::Read),
    row("stat", 0, PointeeAccess::Read),
    row("stat", 1, PointeeAccess::Write),
    row("strcat", 0, PointeeAccess::Write),
    row("strcat", 1, PointeeAccess::Read),
    row("strchr", 0, PointeeAccess::Read),
    row("strcmp", 0, PointeeAccess::Read),
    row("strcmp", 1, PointeeAccess::Read),
    row("strcpy", 0, PointeeAccess::Write),
    row("strcpy", 1, PointeeAccess::Read),
    row("strlen", 0, PointeeAccess::Read),
    row("strncasecmp", 0, PointeeAccess::Read),
    row("strncasecmp", 1, PointeeAccess::Read),
    row("strncat", 0, PointeeAccess::Write),
    row("strncat", 1, PointeeAccess::Read),
    row("strncpy", 0, PointeeAccess::Write),
    row("strncpy", 1, PointeeAccess::Read),
    row("strstr", 0, PointeeAccess::Read),
    row("strstr", 1, PointeeAccess::Read),
    row("utime", 0, PointeeAccess::Read),
    row("utime", 1, PointeeAccess::Read),
    ContractRow {
        symbol: "fclose",
        position: Position::Exact(0),
        access: PointeeAccess::Lifecycle,
        ownership: OwnershipContract::Consume,
    },
    ContractRow {
        symbol: "free",
        position: Position::Exact(0),
        access: PointeeAccess::Lifecycle,
        ownership: OwnershipContract::Consume,
    },
    ContractRow {
        symbol: "realloc",
        position: Position::Exact(0),
        access: PointeeAccess::Lifecycle,
        ownership: OwnershipContract::AtomicSourceSink,
    },
];

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
    let (access, permits_shared_to_mut, provenance) =
        if printf_tail_first(symbol).is_some_and(|first| argument_index >= first) {
            (
                PointeeAccess::Read,
                true,
                "pinned-libc-family-printf-tail-0.2.184",
            )
        } else if scanf_tail_first(symbol).is_some_and(|first| argument_index >= first) {
            (
                PointeeAccess::Write,
                false,
                "pinned-libc-family-scanf-tail-0.2.184",
            )
        } else if is_stdio_stream_position(symbol, argument_index) {
            (
                PointeeAccess::Stream,
                true,
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
        permits_shared_to_mut,
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
        permits_shared_to_mut: false,
        provenance: "pinned-libc-0.2.184",
    })
}

#[cfg(test)]
mod tests {
    use super::*;

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
                permits_shared_to_mut: false,
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

    /// RB-X3 variadic-family witness. Mutation: moving the printf tail start
    /// past argument 2 (or dropping its shared-to-mut permission) changes this
    /// exact contract and is observed here.
    #[test]
    fn rb_x3_printf_and_scanf_variadic_tails_keep_distinct_access() {
        let printf = classify_contract(&callee("fprintf", true), 2, &target(RawMutability::Mut))
            .expect("fprintf variadic tail");
        assert_eq!(printf.retention, RetentionContract::NoRetain);
        assert_eq!(printf.access, PointeeAccess::Read);
        assert!(printf.permits_shared_to_mut);
        assert_eq!(printf.provenance, "pinned-libc-family-printf-tail-0.2.184");

        let scanf = classify_contract(&callee("fscanf", true), 2, &target(RawMutability::Mut))
            .expect("fscanf variadic tail");
        assert_eq!(scanf.retention, RetentionContract::NoRetain);
        assert_eq!(scanf.access, PointeeAccess::Write);
        assert!(!scanf.permits_shared_to_mut);
        assert_eq!(scanf.provenance, "pinned-libc-family-scanf-tail-0.2.184");
    }

    /// RB-X3 stream-position witness. Mutation: routing the FILE* position
    /// through the ordinary write rule loses the explicit stream permission;
    /// routing fclose through it loses lifecycle-hard ownership.
    #[test]
    fn rb_x3_stdio_stream_positions_are_no_retain_but_fclose_is_lifecycle_hard() {
        let stream = classify_contract(&callee("fprintf", true), 0, &target(RawMutability::Mut))
            .expect("fprintf stream");
        assert_eq!(stream.retention, RetentionContract::NoRetain);
        assert_eq!(stream.access, PointeeAccess::Stream);
        assert!(stream.permits_shared_to_mut);
        assert_eq!(stream.provenance, "pinned-libc-family-stdio-stream-0.2.184");

        let close = classify_contract(&callee("fclose", true), 0, &target(RawMutability::Mut))
            .expect("fclose lifecycle");
        assert_eq!(close.access, PointeeAccess::Lifecycle);
        assert_eq!(close.ownership, OwnershipContract::Consume);
        assert!(!close.permits_shared_to_mut);
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
