//! The strdup contract is enabled only for R394 wrapper endpoints.
use crate::bo_rewriter::decision::{
    Decision,
    raw_boundary::{ForeignSymbolKey, RawMutability, RawTargetType},
    raw_boundary_contracts::{
        self as ordinary, ArgumentContract, ArgumentExtent, ContractFailure, OwnershipContract,
        PointeeAccess, RetentionContract,
    },
};

pub(crate) fn for_decision(
    decision: &Decision,
    callee: &ForeignSymbolKey,
    argument_index: usize,
    target: &RawTargetType,
) -> Result<ArgumentContract, ContractFailure> {
    match decision {
        Decision::Cursor { plan, .. } if plan.wrapper => {
            classify_contract(callee, argument_index, target)
        }
        Decision::Cursor { .. }
        | Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::Opt { .. }
        | Decision::Box(_)
        | Decision::NestedSlice { .. }
        | Decision::Degraded(_) => ordinary::classify_contract(callee, argument_index, target),
    }
}
fn classify_contract(
    callee: &ForeignSymbolKey,
    argument_index: usize,
    target: &RawTargetType,
) -> Result<ArgumentContract, ContractFailure> {
    let baseline = ordinary::classify_contract(callee, argument_index, target);
    if baseline != Err(ContractFailure::PositionUnmodeled) {
        return baseline;
    }
    if callee.symbol == "strdup" {
        if argument_index != 0 {
            return Err(ContractFailure::PositionUnmodeled);
        }
        // The key carries rustc's canonical FnSig rendering, not a source
        // declaration. Require the complete one-argument byte signature:
        // an identically named foreign function with a different signature
        // has no strdup contract. The target itself is compiler-type-backed.
        let signature = format!(
            "unsafe extern \"{}\" fn(*const {}) -> *mut {}",
            callee.abi, target.pointee, target.pointee
        );
        if target.mutability != RawMutability::Const
            || target.depth2.is_some()
            || !matches!(target.pointee.as_str(), "i8" | "u8")
            || target.rendered != format!("*const {}", target.pointee)
            || callee.signature != signature
        {
            return Err(ContractFailure::SignatureMismatch);
        }
        // POSIX strdup copies into a new allocation; its source is only read
        // and is neither retained nor the parent of the returned allocation.
        // https://pubs.opengroup.org/onlinepubs/9699919799/functions/strdup.html
        return Ok(ArgumentContract {
            retention: RetentionContract::NoRetain,
            access: PointeeAccess::Read,
            ownership: OwnershipContract::BorrowView,
            extent: ArgumentExtent::NulTerminated,
            returns_alias_of: None,
            provenance: "pinned-libc-0.2.184",
        });
    }
    baseline
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn slicecursor_strdup_contract_reads_const_source_without_retaining_or_aliasing() {
        let source = r#"
            extern "C" { fn strdup(p: *const i8) -> *mut i8; }
            unsafe fn caller(p: *const i8) -> *mut i8 { strdup(p) }
        "#;
        let fact = ::utils::compilation::run_compiler_on_str(source, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let facts = crate::bo_rewriter::decision::emitability::collect(tcx, &program.functions);
            assert_eq!(facts.foreign_call_args.len(), 1);
            facts.foreign_call_args[0].clone()
        })
        .expect("strdup declaration compiles");
        assert_eq!(fact.target.mutability, RawMutability::Const);
        assert_eq!(
            crate::bo_rewriter::decision::raw_boundary_contracts::classify_contract(
                &fact.callee,
                0,
                &fact.target
            ),
            Err(ContractFailure::PositionUnmodeled),
            "the cursor rule must leave other families unchanged"
        );
        assert_eq!(
            classify_contract(&fact.callee, 0, &fact.target),
            Ok(ArgumentContract {
                retention: RetentionContract::NoRetain,
                access: PointeeAccess::Read,
                ownership: OwnershipContract::BorrowView,
                extent: ArgumentExtent::NulTerminated,
                returns_alias_of: None,
                provenance: "pinned-libc-0.2.184",
            }),
            "compiler-resolved strdup: {fact:#?}"
        );
        let mut local = fact.callee.clone();
        local.foreign = false;
        assert_eq!(
            classify_contract(&local, 0, &fact.target),
            Err(ContractFailure::NotForeign)
        );
        assert_eq!(
            classify_contract(&fact.callee, 1, &fact.target),
            Err(ContractFailure::PositionUnmodeled)
        );
        let mut wrong_target = fact.target.clone();
        wrong_target.mutability = RawMutability::Mut;
        wrong_target.rendered = "*mut i8".into();
        assert_eq!(
            classify_contract(&fact.callee, 0, &wrong_target),
            Err(ContractFailure::SignatureMismatch)
        );
        let mut wrong_pointee = fact.target.clone();
        wrong_pointee.pointee = "i32".into();
        wrong_pointee.rendered = "*const i32".into();
        assert_eq!(
            classify_contract(&fact.callee, 0, &wrong_pointee),
            Err(ContractFailure::SignatureMismatch)
        );
        for signature in [
            "unsafe extern C fn(*const i8, usize) -> *mut i8",
            "unsafe extern C fn(*const i8) -> *const i8",
            "unsafe extern C fn(*const i32) -> *mut i32",
        ] {
            let mut lookalike = fact.callee.clone();
            lookalike.signature = signature.into();
            assert_eq!(
                classify_contract(&lookalike, 0, &fact.target),
                Err(ContractFailure::SignatureMismatch),
                "{signature}"
            );
        }
    }
}
