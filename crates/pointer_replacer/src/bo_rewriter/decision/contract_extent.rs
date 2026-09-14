//! R345-6: pure contract-extent selection, deliberately unwired under R244-1.
//!
//! The integration adapter must obtain contract sites from the canonical
//! classifier, fatness from `FatFacts`, and non-length eligibility from the
//! existing proof gates. These input records do not establish those proofs.
//! No symbols are classified here, no analysis is run, and no Rust is emitted.
//! `Keep` means resume the unchanged decision ladder, including ThinExtent.

use rustc_hash::FxHashMap;
use rustc_hir::{HirId, def_id::LocalDefId};

use super::{
    Subject, SubjectKind,
    construction::{Construction, ConstructionFacts},
    emitability::{ArgShape, EmitabilityFacts},
    local_callee_extent::LocalCalleeAccess,
    raw_boundary_contracts::{ArgumentExtent, PointeeAccess, classify_contract},
};
use crate::{analyses::borrow_ownership::SlotKind, bo_rewriter::fat_facts::FatFacts};

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
            Requirement::ElementCount(_) => LengthPlan::Fallback(FallbackReason::ElementCount),
            Requirement::UnboundedWrite => LengthPlan::Fallback(FallbackReason::UnboundedWrite),
            Requirement::LocalAccess => LengthPlan::Fallback(FallbackReason::LocalAccess),
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

#[derive(Clone, Debug)]
struct Candidate {
    subject: String,
    construction: String,
    sites: Vec<ContractSite>,
}

/// Compiler-derived contract sites, shared by hypothetical and settled
/// decisions. The pure selector above remains the sole admission rule.
#[derive(Clone, Debug, Default)]
pub(crate) struct CandidateIndex {
    by_subject: FxHashMap<(LocalDefId, HirId), Candidate>,
}

fn subject_key(subject: &Subject) -> String {
    format!(
        "owner={}:binding={}:depth={}",
        subject.fn_did.local_def_index.as_u32(),
        subject.hir_id.local_id.as_u32(),
        subject.ptr_depth,
    )
}

fn construction_key(subject: &Subject, constructions: &ConstructionFacts) -> String {
    constructions
        .init_hirs
        .get(&(subject.fn_did, subject.hir_id))
        .map_or_else(
            || {
                format!(
                    "entry:{}:{}",
                    subject.fn_did.local_def_index.as_u32(),
                    subject.hir_id.local_id.as_u32(),
                )
            },
            |init| {
                format!(
                    "initializer:{}:{}",
                    subject.fn_did.local_def_index.as_u32(),
                    init.local_id.as_u32(),
                )
            },
        )
}

fn byte_pointee(pointee: &str) -> bool {
    matches!(pointee.trim(), "u8" | "i8")
}

fn initialized_write_source(
    subject: &Subject,
    constructions: &ConstructionFacts,
    facts: &EmitabilityFacts,
) -> bool {
    match subject.kind {
        SubjectKind::Local => matches!(
            constructions
                .by_binding
                .get(&(subject.fn_did, subject.hir_id)),
            Some(Construction::ArrayDecay)
        ),
        SubjectKind::Param { hir_index } => {
            facts.call_args.get(&subject.fn_did).is_some_and(|calls| {
                !calls.is_empty()
                    && calls.iter().all(|call| {
                        call.args.iter().any(|argument| {
                            argument.index == hir_index
                                && argument.initialized_array_elements.is_some()
                        })
                    })
            })
        }
    }
}

/// Build exact subject/site associations from compiler facts. A writable
/// position is admitted only for an initialized array-decay local; allocator
/// capacity alone is not initialized `T` evidence.
pub(crate) fn collect(
    subjects: &[Subject],
    facts: &EmitabilityFacts,
    constructions: &ConstructionFacts,
    local_callee_extent: &FxHashMap<(LocalDefId, HirId), LocalCalleeAccess>,
) -> CandidateIndex {
    let subjects = subjects
        .iter()
        .map(|subject| ((subject.fn_did, subject.hir_id), subject))
        .collect::<FxHashMap<_, _>>();
    let mut by_subject = FxHashMap::<_, Candidate>::default();
    for fact in &facts.foreign_call_args {
        let root = fact.direct_storage.map(|(root, _)| root).or(fact.root);
        let Some(root) = root else { continue };
        let node = (fact.caller, root);
        let Some(subject) = subjects.get(&node).copied() else { continue };
        let Ok(contract) = classify_contract(&fact.callee, fact.argument_index, &fact.target)
        else {
            continue;
        };
        if matches!(
            contract.extent,
            ArgumentExtent::ByteCount | ArgumentExtent::ElementCount
        ) && contract.count_argument_index.is_some()
            && fact.contract_count.is_none()
        {
            // A canonical counted contract with no actual count operand is an
            // incompatible declaration, not a length-only gap.
            continue;
        }
        if contract.access == PointeeAccess::Write
            && !initialized_write_source(subject, constructions, facts)
        {
            continue;
        }
        let key = subject_key(subject);
        let construction = construction_key(subject, constructions);
        let site_key = format!(
            "owner={}:call={}..{}:callee={}:arg={}",
            fact.caller.local_def_index.as_u32(),
            fact.call_span.lo().0,
            fact.call_span.hi().0,
            fact.callee.path,
            fact.argument_index,
        );
        let count = fact.contract_count.as_ref().map(|count| CountOperand {
            site: site_key.clone(),
            construction: construction.clone(),
            argument_index: count.argument_index,
            elements: if byte_pointee(&fact.target.pointee) {
                Ok(count.expression.clone())
            } else {
                Err(CountGap::UnitsUnproved)
            },
        });
        let requirement = match contract.extent {
            ArgumentExtent::OneElement => Requirement::OneElement,
            ArgumentExtent::Lifecycle => Requirement::Lifecycle,
            ArgumentExtent::NulTerminated => Requirement::NulTerminated,
            ArgumentExtent::ByteCount if contract.count_is_exact => Requirement::ExactAccess(count),
            ArgumentExtent::ByteCount => Requirement::UpperBound(count),
            ArgumentExtent::ElementCount => Requirement::ElementCount(count),
            ArgumentExtent::UnboundedWrite => Requirement::UnboundedWrite,
            ArgumentExtent::Unclassified => continue,
        };
        let site = ContractSite {
            subject: key.clone(),
            site: site_key,
            contract: format!(
                "{}:{}:{}:{}",
                fact.callee.path,
                contract.provenance,
                fact.argument_index,
                contract.extent.key(),
            ),
            requirement,
        };
        let candidate = by_subject.entry(node).or_insert_with(|| Candidate {
            subject: key,
            construction,
            sites: Vec::new(),
        });
        candidate.sites.push(site);
    }
    for (&node, access) in local_callee_extent {
        let Some(subject) = subjects.get(&node).copied() else { continue };
        let Some(calls) = facts.call_args.get(&access.callee_id) else { continue };
        let key = subject_key(subject);
        let construction = construction_key(subject, constructions);
        for call in calls.iter().filter(|call| call.caller == node.0) {
            for argument in call.args.iter().filter(|argument| {
                argument.index == access.parameter_index
                    && matches!(
                        argument.shape,
                        ArgShape::BareLocal(root) | ArgShape::CastOfLocal { binding: root, .. }
                            if root == node.1
                    )
            }) {
                let site_key = format!(
                    "owner={}:call={}..{}:callee=local:{}:arg={}",
                    call.caller.local_def_index.as_u32(),
                    call.span.lo().0,
                    call.span.hi().0,
                    access.callee_id.local_def_index.as_u32(),
                    argument.index,
                );
                let site = ContractSite {
                    subject: key.clone(),
                    site: site_key,
                    contract: format!(
                        "local-body-access:{}:{}:{}",
                        access.callee_id.local_def_index.as_u32(),
                        access.parameter_index,
                        access.detail(),
                    ),
                    requirement: Requirement::LocalAccess,
                };
                let candidate = by_subject.entry(node).or_insert_with(|| Candidate {
                    subject: key.clone(),
                    construction: construction.clone(),
                    sites: Vec::new(),
                });
                candidate.sites.push(site);
            }
        }
    }
    for candidate in by_subject.values_mut() {
        candidate
            .sites
            .sort_by(|left, right| left.site.cmp(&right.site));
    }
    CandidateIndex { by_subject }
}

impl CandidateIndex {
    pub(crate) fn select(
        &self,
        subject: &Subject,
        form: CurrentForm,
        model_kind: Option<SlotKind>,
        fat: &FatFacts,
    ) -> Selection {
        let Some(candidate) = self.by_subject.get(&(subject.fn_did, subject.hir_id)) else {
            return Selection::Keep(KeepReason::NoContractOperation);
        };
        select(
            &SubjectFacts {
                key: candidate.subject.clone(),
                construction: candidate.construction.clone(),
                model_kind,
                depth: u32::from(subject.ptr_depth),
                form,
                array: fat.verdict(subject.fn_did, subject.local).map(|verdict| {
                    matches!(
                        verdict,
                        crate::analyses::type_qualifier::foster::fatness::Fatness::Arr
                    )
                }),
                non_length: Ok(()),
            },
            &candidate.sites,
            None,
        )
    }

    pub(crate) fn promotion(
        &self,
        subject: &Subject,
        nullable: bool,
        fat: &FatFacts,
    ) -> Option<Promotion> {
        match self.select(
            subject,
            CurrentForm::Ref {
                mutable: subject.mutable,
                nullable,
            },
            Some(SlotKind::Ref),
            fat,
        ) {
            Selection::Promote(promotion) => Some(promotion),
            Selection::Keep(_) => None,
        }
    }
}
