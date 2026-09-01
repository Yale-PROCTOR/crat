//! Raw-boundary facts and decisions.
//!
//! This module is rewriter-side by design. It consumes the frozen model/MIR and
//! never contributes a solver constraint or cache field.

/// A lifetime-free, artifact-stable call-site identity.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct RawBoundarySiteKey {
    pub caller: String,
    pub block: u32,
    pub statement_index: u32,
    pub callee: ForeignSymbolKey,
    pub argument_index: usize,
    pub subject: String,
}

/// Resolved callee identity. `foreign` is load-bearing: a same-spelled local
/// function is not a libc contract match.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct ForeignSymbolKey {
    pub symbol: String,
    pub abi: String,
    pub signature: String,
    pub foreign: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RawMutability {
    Const,
    Mut,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MirCallCandidate {
    pub block: u32,
    pub statement_index: u32,
    pub callee: ForeignSymbolKey,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SiteMatchFailure {
    Missing,
    Ambiguous,
    CalleeMismatch,
}

/// Select the one MIR call which represents an already-resolved HIR call site.
/// Zero and multiple matches stay typed rather than choosing by traversal
/// order.
pub(crate) fn select_unique_site(
    expected: &ForeignSymbolKey,
    candidates: &[MirCallCandidate],
) -> Result<(u32, u32), SiteMatchFailure> {
    let mut matching = candidates.iter().filter(|site| site.callee == *expected);
    let Some(site) = matching.next() else {
        return Err(if candidates.is_empty() {
            SiteMatchFailure::Missing
        } else {
            SiteMatchFailure::CalleeMismatch
        });
    };
    if matching.next().is_some() {
        return Err(SiteMatchFailure::Ambiguous);
    }
    Ok((site.block, site.statement_index))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn symbol(name: &str, foreign: bool) -> ForeignSymbolKey {
        ForeignSymbolKey {
            symbol: name.to_owned(),
            abi: "C".to_owned(),
            signature: "(*mut i32)->()".to_owned(),
            foreign,
        }
    }

    #[test]
    fn rb_x1_exact_single_call_candidate_builds_owned_key() {
        let expected = symbol("consume", true);
        let site = select_unique_site(
            &expected,
            &[MirCallCandidate {
                block: 7,
                statement_index: 3,
                callee: expected.clone(),
            }],
        );
        assert_eq!(site, Ok((7, 3)));
    }

    #[test]
    fn rb_x1_zero_or_multiple_candidates_fail_closed() {
        let expected = symbol("consume", true);
        assert_eq!(
            select_unique_site(&expected, &[]),
            Err(SiteMatchFailure::Missing)
        );
        let one = MirCallCandidate {
            block: 1,
            statement_index: 0,
            callee: expected.clone(),
        };
        assert_eq!(
            select_unique_site(&expected, &[one.clone(), one]),
            Err(SiteMatchFailure::Ambiguous)
        );
    }

    #[test]
    fn rb_x1_same_spelled_local_is_not_the_foreign_site() {
        let expected = symbol("consume", true);
        let local = symbol("consume", false);
        assert_eq!(
            select_unique_site(
                &expected,
                &[MirCallCandidate {
                    block: 2,
                    statement_index: 1,
                    callee: local,
                }],
            ),
            Err(SiteMatchFailure::CalleeMismatch)
        );
    }

    #[test]
    fn rb_x1_target_mutability_is_not_collapsed() {
        assert_ne!(RawMutability::Const, RawMutability::Mut);
    }
}
