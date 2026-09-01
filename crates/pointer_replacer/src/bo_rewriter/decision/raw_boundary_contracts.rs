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
    VarArgsFrom(usize),
}

impl Position {
    fn matches(self, index: usize) -> bool {
        match self {
            Self::Exact(expected) => index == expected,
            Self::VarArgsFrom(first) => index >= first,
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

const fn varargs(symbol: &'static str, first: usize, access: PointeeAccess) -> ContractRow {
    ContractRow {
        symbol,
        position: Position::VarArgsFrom(first),
        access,
        ownership: OwnershipContract::BorrowView,
    }
}

/// Per-argument no-retention contracts. Fixed positions and variadic positions
/// are explicit so a destination never inherits a source's access mode.
const TABLE: &[ContractRow] = &[
    row("fdopen", 1, PointeeAccess::Read),
    row("fgetc", 0, PointeeAccess::Write),
    row("fgets", 0, PointeeAccess::Write),
    row("fgets", 2, PointeeAccess::Write),
    row("fopen", 0, PointeeAccess::Read),
    row("fopen", 1, PointeeAccess::Read),
    row("fprintf", 0, PointeeAccess::Write),
    row("fprintf", 1, PointeeAccess::Read),
    varargs("fprintf", 2, PointeeAccess::Read),
    row("fputs", 0, PointeeAccess::Read),
    row("fputs", 1, PointeeAccess::Write),
    row("fscanf", 0, PointeeAccess::Write),
    row("fscanf", 1, PointeeAccess::Read),
    varargs("fscanf", 2, PointeeAccess::Write),
    row("getenv", 0, PointeeAccess::Read),
    row("glob", 0, PointeeAccess::Read),
    row("glob", 3, PointeeAccess::Write),
    row("lstat", 0, PointeeAccess::Read),
    row("lstat", 1, PointeeAccess::Write),
    row("open", 0, PointeeAccess::Read),
    row("perror", 0, PointeeAccess::Read),
    row("printf", 0, PointeeAccess::Read),
    varargs("printf", 1, PointeeAccess::Read),
    row("snprintf", 0, PointeeAccess::Write),
    row("snprintf", 2, PointeeAccess::Read),
    varargs("snprintf", 3, PointeeAccess::Read),
    row("sprintf", 0, PointeeAccess::Write),
    row("sprintf", 1, PointeeAccess::Read),
    varargs("sprintf", 2, PointeeAccess::Read),
    row("sscanf", 0, PointeeAccess::Read),
    row("sscanf", 1, PointeeAccess::Read),
    varargs("sscanf", 2, PointeeAccess::Write),
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
    row("ungetc", 1, PointeeAccess::Write),
    row("utime", 0, PointeeAccess::Read),
    row("utime", 1, PointeeAccess::Read),
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
    fn rb_n2b_same_spelled_local_never_matches_the_libc_contract() {
        assert_eq!(
            classify_contract(&callee("strlen", false), 0, &target(RawMutability::Const)),
            Err(ContractFailure::NotForeign)
        );
    }

    #[test]
    fn contract_rows_are_unique_and_variadic_ranges_do_not_overlap_fixed_rows() {
        for (index, left) in TABLE.iter().enumerate() {
            for right in &TABLE[..index] {
                let overlap = left.symbol == right.symbol
                    && (0..16).any(|arg| left.position.matches(arg) && right.position.matches(arg));
                assert!(!overlap, "overlapping contract rows: {left:?} / {right:?}");
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
