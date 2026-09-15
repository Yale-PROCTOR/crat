//! R345-6: pure contract-extent selection, consumed by `contract_extent_adapter`.
//!
//! The integration adapter must obtain contract sites from the canonical
//! classifier, fatness from `FatFacts`, and non-length eligibility from the
//! existing proof gates. These input records do not establish those proofs.
//! No symbols are classified here, no analysis is run, and no Rust is emitted.
//! `Keep` means resume the unchanged decision ladder, including ThinExtent.

use crate::analyses::borrow_ownership::SlotKind;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CurrentForm {
    Ref { mutable: bool, nullable: bool },
    Slice,
    Other,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum NonLengthHold {
    Uninitialized,
    MissingRangeAlias,
    Evaluation,
    ReturnCustody,
    Existing(String),
}

#[derive(Clone, Debug)]
pub(crate) struct SubjectFacts {
    pub key: String,
    pub construction: String,
    pub model_kind: Option<SlotKind>,
    pub depth: u32,
    pub form: CurrentForm,
    /// `Some(true)` = Arr, `Some(false)` = Ptr, `None` = lookup missing.
    pub array: Option<bool>,
    /// R407-14: EVERY use of the subject is a foreign NUL-terminated contract
    /// position (no dereference, index, arithmetic, local callee, store or
    /// return). Read by the adapter from the subject's own use facts; lifts
    /// the `Ptr` fatness hold ONLY when every site here is NUL-terminated.
    pub contract_alone: bool,
    pub non_length: Result<(), NonLengthHold>,
    /// R397-6(b): the up-front decline for this form, read from the subject's
    /// own pre-selection use facts. Checked after every promotability gate, so
    /// `Keep(Declined)` names exactly a candidate that would otherwise promote.
    pub decline: Option<DeclineCause>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum CountGap {
    UnitsUnproved,
    TransportMissing,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CountOperand {
    /// Identity of the exact contract call, not just an expression spelling.
    pub site: String,
    pub construction: String,
    pub argument_index: usize,
    /// Already normalized to elements by a proved association at construction.
    /// A byte count with unproved division must be `Err(UnitsUnproved)`.
    pub elements: Result<String, CountGap>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Requirement {
    OneElement,
    Lifecycle,
    ExactAccess(Option<CountOperand>),
    UpperBound(Option<CountOperand>),
    NulTerminated,
    ElementCount(Option<CountOperand>),
    UnboundedWrite,
    LocalAccess,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ContractSite {
    pub subject: String,
    pub site: String,
    /// Canonical contract/version plus resolved foreign identity and position.
    pub contract: String,
    pub requirement: Requirement,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BackingExtent {
    pub subject: String,
    pub construction: String,
    pub elements: String,
    pub evidence: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum FallbackReason {
    NulTerminated,
    ElementCount,
    UnboundedWrite,
    LocalAccess,
    UpperBound,
    CountMissing,
    CountGap(CountGap),
    MultipleRequirements,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum LengthSource {
    Backing(String),
    ExactContract { site: String, argument_index: usize },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum LengthPlan {
    Evidence {
        elements: String,
        source: LengthSource,
    },
    /// Integration must map this marker to the existing named 1024 constant
    /// and MechanicalExtent::Fallback. It may never become Evidence.
    Fallback(FallbackReason),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Waiver {
    /// The existing slice-extent-out-of-scope@addendum-77, not a new waiver.
    SliceExtent,
}

impl LengthPlan {
    pub(crate) fn waiver(&self) -> Option<Waiver> {
        match self {
            Self::Evidence { .. } => None,
            Self::Fallback(_) => Some(Waiver::SliceExtent),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Promotion {
    pub subject: String,
    pub construction: String,
    pub mutable: bool,
    pub nullable: bool,
    pub length: LengthPlan,
    /// All supporting multi-element sites, retained through entry/exit plans.
    pub sites: Vec<ContractSite>,
    /// R407-14: admitted on the contract positions ALONE — the whole-program
    /// fatness says `Ptr`, but every use of the subject is a foreign
    /// NUL-terminated contract position, read only through `as_ptr()`.
    pub contract_alone: bool,
}

/// R397-6(b): why a contract candidate is DECLINED before selection.
///
/// A candidate that is never attempted withdraws no sibling, so every cause
/// here is one whose terminal outcome is already fixed by the candidate's own
/// pre-selection Slice-use facts; the ladder resumes at the thin-extent hold.
/// Causes the plan stage decides later (class reverts, interface restoration,
/// pair overlap) are NOT readable here and are not claimed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum DeclineCause {
    /// A use of the subject that no slice form has an image for.
    SliceUseUnsupported,
    /// A raw use at a LOCAL callee argument: the slice-use adapter needs an
    /// interface carrier there, and a zero-syntax carrier is unwired (10 of 10
    /// corpus subjects with this shape reclassified at the third census).
    LocalCalleeBoundary,
    /// A raw use stored into a field: positive retention, always terminal.
    FieldStore,
    /// A raw use with no boundary that is neither a pointer distance, a copy
    /// into a local, nor a discarded const view.
    UnsupportedRawUse,
    /// R395-2: a caller hands this parameter a THIN reference subject (BO
    /// `Ref`, no array arithmetic of its own). Promoting the parameter would
    /// widen that one-element reference into the slice with `from_ref` and
    /// hand it to the foreign read; the candidate is declined instead and the
    /// caller keeps its prior form.
    ThinCallerArgument,
}

impl DeclineCause {
    pub(crate) fn key(&self) -> &'static str {
        match self {
            Self::SliceUseUnsupported => "slice-use-unsupported",
            Self::LocalCalleeBoundary => "local-callee-boundary",
            Self::FieldStore => "field-store",
            Self::UnsupportedRawUse => "unsupported-raw-use",
            Self::ThinCallerArgument => "thin-caller-argument",
        }
    }

    /// The typed receipt text.
    pub(crate) fn receipt(&self) -> String {
        format!("contract-candidate-declined:{}", self.key())
    }
}

/// The candidate's own pre-selection Slice-use facts, summarized.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct UseSummary {
    pub unsupported: bool,
    pub local_callee_boundary_uses: usize,
    pub field_store_uses: usize,
    pub unsupported_raw_uses: usize,
    pub thin_caller_arguments: usize,
}

/// The up-front decline. Pure; the first fixed cause in ladder order wins.
pub(crate) fn decline(summary: &UseSummary) -> Option<DeclineCause> {
    if summary.unsupported {
        return Some(DeclineCause::SliceUseUnsupported);
    }
    if summary.local_callee_boundary_uses > 0 {
        return Some(DeclineCause::LocalCalleeBoundary);
    }
    if summary.field_store_uses > 0 {
        return Some(DeclineCause::FieldStore);
    }
    if summary.unsupported_raw_uses > 0 {
        return Some(DeclineCause::UnsupportedRawUse);
    }
    if summary.thin_caller_arguments > 0 {
        return Some(DeclineCause::ThinCallerArgument);
    }
    None
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum KeepReason {
    /// R397-6(b): declined before selection; the ladder resumes unchanged.
    Declined(DeclineCause),
    ExistingForm,
    ModelNotRef,
    Depth,
    NoContractOperation,
    FatnessPtr,
    FatnessMissing,
    NonLength(NonLengthHold),
    WrongSubject,
    DuplicateSite,
    WrongCountSite,
    WrongConstruction,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Selection {
    Keep(KeepReason),
    Promote(Promotion),
}

pub(crate) fn select(
    subject: &SubjectFacts,
    sites: &[ContractSite],
    backing: Option<&BackingExtent>,
) -> Selection {
    let CurrentForm::Ref { mutable, nullable } = subject.form else {
        return Selection::Keep(KeepReason::ExistingForm);
    };
    if subject.model_kind != Some(SlotKind::Ref) {
        return Selection::Keep(KeepReason::ModelNotRef);
    }
    if subject.depth != 1 {
        return Selection::Keep(KeepReason::Depth);
    }
    let sites: Vec<_> = sites
        .iter()
        .filter(|site| {
            !matches!(
                site.requirement,
                Requirement::OneElement | Requirement::Lifecycle
            )
        })
        .cloned()
        .collect();
    if sites.is_empty() {
        return Selection::Keep(KeepReason::NoContractOperation);
    }
    // R407-14: the contract positions alone admit a `Ptr`-fat subject whose
    // every use is a NUL-terminated position; the slice is read only through
    // `as_ptr()`, so no element is ever addressed beyond the C string.
    let contract_alone = subject.contract_alone
        && sites
            .iter()
            .all(|site| matches!(site.requirement, Requirement::NulTerminated));
    match subject.array {
        Some(true) => {}
        Some(false) if contract_alone => {}
        Some(false) => return Selection::Keep(KeepReason::FatnessPtr),
        None => return Selection::Keep(KeepReason::FatnessMissing),
    }
    if let Err(hold) = &subject.non_length {
        return Selection::Keep(KeepReason::NonLength(hold.clone()));
    }
    let mut seen = std::collections::BTreeSet::new();
    for site in &sites {
        if site.subject != subject.key {
            return Selection::Keep(KeepReason::WrongSubject);
        }
        if !seen.insert(&site.site) {
            return Selection::Keep(KeepReason::DuplicateSite);
        }
        if let Requirement::ExactAccess(Some(count)) | Requirement::UpperBound(Some(count)) =
            &site.requirement
        {
            if count.site != site.site {
                return Selection::Keep(KeepReason::WrongCountSite);
            }
            if count.construction != subject.construction {
                return Selection::Keep(KeepReason::WrongConstruction);
            }
        }
    }
    if let Some(cause) = &subject.decline {
        return Selection::Keep(KeepReason::Declined(cause.clone()));
    }
    let length = if let Some(backing) = backing {
        if backing.subject != subject.key {
            return Selection::Keep(KeepReason::WrongSubject);
        }
        if backing.construction != subject.construction {
            return Selection::Keep(KeepReason::WrongConstruction);
        }
        LengthPlan::Evidence {
            elements: backing.elements.clone(),
            source: LengthSource::Backing(backing.evidence.clone()),
        }
    } else if sites.len() != 1 {
        // Equal expression text at two calls is not an equal dynamic value.
        // Until a covering backing extent is proved, retain both sites and
        // attribute the missing length instead of selecting a source-order win.
        LengthPlan::Fallback(FallbackReason::MultipleRequirements)
    } else {
        match &sites[0].requirement {
            Requirement::ExactAccess(Some(count)) => match &count.elements {
                Ok(elements) => LengthPlan::Evidence {
                    elements: elements.clone(),
                    source: LengthSource::ExactContract {
                        site: count.site.clone(),
                        argument_index: count.argument_index,
                    },
                },
                Err(gap) => LengthPlan::Fallback(FallbackReason::CountGap(gap.clone())),
            },
            Requirement::ExactAccess(None) => LengthPlan::Fallback(FallbackReason::CountMissing),
            Requirement::UpperBound(_) => LengthPlan::Fallback(FallbackReason::UpperBound),
            Requirement::NulTerminated => LengthPlan::Fallback(FallbackReason::NulTerminated),
            // #1b (R386-3): `size * nmemb` proved in elements is exact evidence.
            Requirement::ElementCount(Some(count)) => match &count.elements {
                Ok(elements) => LengthPlan::Evidence {
                    elements: elements.clone(),
                    source: LengthSource::ExactContract {
                        site: count.site.clone(),
                        argument_index: count.argument_index,
                    },
                },
                Err(gap) => LengthPlan::Fallback(FallbackReason::CountGap(gap.clone())),
            },
            Requirement::ElementCount(None) => LengthPlan::Fallback(FallbackReason::ElementCount),
            Requirement::UnboundedWrite => LengthPlan::Fallback(FallbackReason::UnboundedWrite),
            Requirement::LocalAccess => LengthPlan::Fallback(FallbackReason::LocalAccess),
            Requirement::OneElement | Requirement::Lifecycle => unreachable!("filtered above"),
        }
    };
    let contract_alone = subject.array == Some(false) && contract_alone;
    Selection::Promote(Promotion {
        subject: subject.key.clone(),
        construction: subject.construction.clone(),
        // A contract-alone promotion is the shared form: every position reads.
        mutable: mutable && !contract_alone,
        nullable,
        length,
        sites,
        contract_alone,
    })
}

#[cfg(test)]
mod decline_tests {
    use super::*;

    #[test]
    fn a_clean_summary_is_not_declined() {
        assert_eq!(decline(&UseSummary::default()), None);
    }

    #[test]
    fn each_fixed_cause_declines_with_its_own_typed_receipt() {
        let cases = [
            (
                UseSummary {
                    unsupported: true,
                    ..Default::default()
                },
                DeclineCause::SliceUseUnsupported,
                "contract-candidate-declined:slice-use-unsupported",
            ),
            (
                UseSummary {
                    local_callee_boundary_uses: 1,
                    ..Default::default()
                },
                DeclineCause::LocalCalleeBoundary,
                "contract-candidate-declined:local-callee-boundary",
            ),
            (
                UseSummary {
                    field_store_uses: 2,
                    ..Default::default()
                },
                DeclineCause::FieldStore,
                "contract-candidate-declined:field-store",
            ),
            (
                UseSummary {
                    unsupported_raw_uses: 1,
                    ..Default::default()
                },
                DeclineCause::UnsupportedRawUse,
                "contract-candidate-declined:unsupported-raw-use",
            ),
            (
                UseSummary {
                    thin_caller_arguments: 1,
                    ..Default::default()
                },
                DeclineCause::ThinCallerArgument,
                "contract-candidate-declined:thin-caller-argument",
            ),
        ];
        for (summary, cause, receipt) in cases {
            let got = decline(&summary).expect("declined");
            assert_eq!(got, cause, "{summary:?}");
            assert_eq!(got.receipt(), receipt);
        }
    }

    /// The ladder order: the use wall is reported before a boundary cause, so
    /// a receipt never names a carrier problem on a subject that has no slice
    /// image at all.
    #[test]
    fn the_use_wall_is_reported_first() {
        let summary = UseSummary {
            unsupported: true,
            local_callee_boundary_uses: 3,
            field_store_uses: 1,
            unsupported_raw_uses: 1,
            thin_caller_arguments: 2,
        };
        assert_eq!(decline(&summary), Some(DeclineCause::SliceUseUnsupported));
    }
}
