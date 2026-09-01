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

pub(crate) fn classify_contract(
    _callee: &ForeignSymbolKey,
    _argument_index: usize,
    _target: &RawTargetType,
) -> Result<ArgumentContract, ContractFailure> {
    Err(ContractFailure::PositionUnmodeled)
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
}
