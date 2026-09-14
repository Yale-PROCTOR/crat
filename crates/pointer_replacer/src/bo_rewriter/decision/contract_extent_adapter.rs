//! Compiler-fact adapter and terminal receipt helpers for contract extent.

use rustc_hash::FxHashMap;
use rustc_hir::{HirId, def_id::LocalDefId};

use super::{
    Subject, SubjectKind,
    construction::{Construction, ConstructionFacts},
    contract_extent::*,
    emitability::{ArgShape, EmitabilityFacts},
    local_callee_extent::LocalCalleeAccess,
    raw_boundary_contracts::{ArgumentExtent, PointeeAccess, classify_contract},
};
use crate::{analyses::borrow_ownership::SlotKind, bo_rewriter::fat_facts::FatFacts};

impl Promotion {
    pub(crate) fn receipt_sites(&self) -> String {
        self.sites
            .iter()
            .map(|site| {
                format!(
                    "{}|{}|{}",
                    site.site,
                    site.contract,
                    site.requirement.receipt_key()
                )
            })
            .collect::<Vec<_>>()
            .join(";")
    }

    pub(crate) fn receipt_count_operands(&self) -> String {
        self.sites
            .iter()
            .filter_map(|site| match &site.requirement {
                Requirement::ExactAccess(Some(count))
                | Requirement::UpperBound(Some(count))
                | Requirement::ElementCount(Some(count)) => Some(format!(
                    "site={}:arg={}:elements={}",
                    count.site,
                    count.argument_index,
                    count.elements.as_ref().map_or_else(
                        |gap| format!("missing:{gap:?}"),
                        |elements| elements.clone(),
                    ),
                )),
                Requirement::OneElement
                | Requirement::Lifecycle
                | Requirement::ExactAccess(None)
                | Requirement::UpperBound(None)
                | Requirement::NulTerminated
                | Requirement::ElementCount(None)
                | Requirement::UnboundedWrite
                | Requirement::LocalAccess => None,
            })
            .collect::<Vec<_>>()
            .join(";")
    }

    pub(crate) fn receipt_length(&self) -> String {
        match &self.length {
            LengthPlan::Evidence { elements, .. } => elements.clone(),
            LengthPlan::Fallback(_) => "crate::FALLBACK_SLICE_EXTENT".to_owned(),
        }
    }

    pub(crate) fn receipt_extent_kind(&self) -> &'static str {
        match self.length {
            LengthPlan::Evidence { .. } => "evidence",
            LengthPlan::Fallback(_) => "fallback",
        }
    }

    pub(crate) fn receipt_waiver(&self) -> &'static str {
        match self.length {
            LengthPlan::Evidence { .. } => "-",
            LengthPlan::Fallback(_) => super::super::mechanical_receipt::SLICE_EXTENT_WAIVER_ID,
        }
    }

    pub(crate) fn mechanical_extent(&self) -> super::super::mechanical_receipt::MechanicalExtent {
        use super::super::mechanical_receipt::{
            FALLBACK_EXTENT_RECEIPT, MechanicalExtent, SLICE_EXTENT_WAIVER_ID,
        };
        match &self.length {
            LengthPlan::Evidence { source, .. } => {
                MechanicalExtent::Evidence(format!("contract-extent:{source:?}"))
            }
            LengthPlan::Fallback(_) => MechanicalExtent::Fallback {
                receipt: FALLBACK_EXTENT_RECEIPT.to_owned(),
                waiver_id: SLICE_EXTENT_WAIVER_ID.to_owned(),
            },
        }
    }
}

impl Requirement {
    fn receipt_key(&self) -> &'static str {
        match self {
            Self::OneElement => "one-element",
            Self::Lifecycle => "lifecycle",
            Self::ExactAccess(_) => "exact-access",
            Self::UpperBound(_) => "upper-bound",
            Self::NulTerminated => "nul-terminated",
            Self::ElementCount(_) => "element-count",
            Self::UnboundedWrite => "unbounded-write",
            Self::LocalAccess => "local-access",
        }
    }
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
        if contract.returns_alias_of == Some(fact.argument_index) {
            // #1a does not yet carry the returned-child custody needed to
            // replace the parent pointer. Exact-count memcpy destination
            // ownership is the separately bounded #1b transaction.
            continue;
        }
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
        let sites = candidate
            .sites
            .iter()
            .filter(|site| !matches!(site.requirement, Requirement::LocalAccess))
            .cloned()
            .collect::<Vec<_>>();
        if sites.is_empty() {
            return Selection::Keep(KeepReason::NonLength(NonLengthHold::Existing(
                "local-callee-contract-deferred-1a".to_owned(),
            )));
        }
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
            &sites,
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
