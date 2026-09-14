//! R345-6: pure contract-extent selection, deliberately unwired under R244-1.
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
    pub non_length: Result<(), NonLengthHold>,
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
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum KeepReason {
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
    match subject.array {
        Some(true) => {}
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
            Requirement::OneElement | Requirement::Lifecycle => unreachable!("filtered above"),
        }
    };
    Selection::Promote(Promotion {
        subject: subject.key.clone(),
        construction: subject.construction.clone(),
        mutable,
        nullable,
        length,
        sites,
    })
}
