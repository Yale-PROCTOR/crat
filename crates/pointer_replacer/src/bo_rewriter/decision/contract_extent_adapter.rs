//! Compiler-fact adapter and terminal receipt helpers for contract extent.

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{HirId, def_id::LocalDefId};

use super::{
    Subject, SubjectKind,
    construction::{Construction, ConstructionFacts},
    contract_extent::*,
    emitability::{ArgShape, EmitabilityFacts, OptUses, SliceUses},
    local_callee_extent::LocalCalleeAccess,
    raw_boundary::RawMutability,
    raw_boundary_contracts::{ArgumentExtent, PointeeAccess, classify_contract},
};
use crate::{
    analyses::borrow_ownership::{SlotKind, crate_slots::CrateSlots, solver::SlotRef},
    bo_rewriter::fat_facts::FatFacts,
};

/// Receipt fields are single-line TSV cells. Keep the compiler spelling in the
/// semantic plan and normalize only the copy written to a receipt.
fn receipt_expression(value: &str) -> String {
    value.replace(['\t', '\r', '\n'], " ")
}

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
                        |elements| receipt_expression(elements),
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
            LengthPlan::Evidence { elements, .. } => receipt_expression(elements),
            LengthPlan::Fallback(_) => "crate::FALLBACK_SLICE_EXTENT".to_owned(),
        }
    }

    pub(crate) fn receipt_extent_kind(&self) -> &'static str {
        match self.length {
            LengthPlan::Evidence { .. } => "evidence",
            LengthPlan::Fallback(_) => "fallback",
        }
    }

    /// The `contract_extent_fatness` receipt column: the fatness conjunct
    /// that admitted the promotion.
    pub(crate) fn receipt_fatness(&self) -> &'static str {
        if self.contract_alone {
            "contract-alone"
        } else {
            "arr"
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
    /// R397-6(b): candidates declined at the selection INPUT, with the cause,
    /// for the plain form (the slice walker's use wall).
    declines: FxHashMap<(LocalDefId, HirId), DeclineCause>,
    /// The same for the nullable form, whose use wall is the Option walker's.
    nullable_declines: FxHashMap<(LocalDefId, HirId), DeclineCause>,
    /// R407-14: subjects whose EVERY use is a foreign NUL-terminated contract
    /// position — the contract positions alone admit them over `Ptr` fatness.
    contract_alone: FxHashSet<(LocalDefId, HirId)>,
}

/// The candidate's own pre-selection Slice-use facts. A raw use at a LOCAL
/// callee argument is recognized by its exact argument span in `call_args`,
/// the same identity `raw_boundary_argument_paths` records it under.
fn use_summary(
    owner: LocalDefId,
    uses: Option<&SliceUses>,
    unsupported: bool,
    local_boundaries: &rustc_hash::FxHashSet<(LocalDefId, u32, u32)>,
) -> UseSummary {
    let Some(uses) = uses else {
        return UseSummary {
            unsupported,
            ..UseSummary::default()
        };
    };
    let mut summary = UseSummary {
        unsupported,
        ..UseSummary::default()
    };
    for raw in &uses.raw_uses {
        match raw.boundary_span {
            Some(span) => {
                if local_boundaries.contains(&(owner, span.lo().0, span.hi().0)) {
                    summary.local_callee_boundary_uses += 1;
                }
            }
            None => match raw.source_shape {
                "pointer-distance" if raw.contract.is_some() => {}
                "body-copy" => {}
                "raw-discard" if raw.target.mutability == RawMutability::Const => {}
                "field-store" => summary.field_store_uses += 1,
                _ => summary.unsupported_raw_uses += 1,
            },
        }
    }
    summary
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

/// The element type the count is measured against: the callee's pointee, or
/// — at a `c_void` position such as `fwrite`'s — the ARGUMENT's own pointee,
/// which is what the subject is a slice of.
fn element_pointee(fact: &super::raw_boundary::ForeignCallArgFact) -> String {
    let target = fact.target.pointee.trim();
    if target == "c_void" || target.ends_with("::c_void") {
        fact.operand_pointee.trim().to_owned()
    } else {
        target.to_owned()
    }
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
    slice_uses: &FxHashMap<(LocalDefId, HirId), SliceUses>,
    opt_uses: &FxHashMap<(LocalDefId, HirId), OptUses>,
    model: &FxHashMap<SlotRef, SlotKind>,
    slots: &CrateSlots,
    fat: &FatFacts,
) -> CandidateIndex {
    let subjects = subjects
        .iter()
        .map(|subject| ((subject.fn_did, subject.hir_id), subject))
        .collect::<FxHashMap<_, _>>();
    let mut by_subject = FxHashMap::<_, Candidate>::default();
    // R407-14: the foreign NUL-terminated positions by argument span — the
    // identity the slice walker records a boundary use under.
    let mut nul_positions = FxHashSet::<(LocalDefId, u32, u32)>::default();
    for fact in &facts.foreign_call_args {
        let Some(root) = fact.direct_subject_root() else {
            continue;
        };
        let node = (fact.caller, root);
        let Some(subject) = subjects.get(&node).copied() else { continue };
        let Ok(contract) = classify_contract(&fact.callee, fact.argument_index, &fact.target)
        else {
            continue;
        };
        if contract.extent == ArgumentExtent::NulTerminated {
            nul_positions.insert((
                fact.caller,
                fact.argument_span.lo().0,
                fact.argument_span.hi().0,
            ));
        }
        if contract.returns_alias_of == Some(fact.argument_index) && !fact.return_unused {
            // #1b: a returned alias of this argument (`memcpy` returns its
            // destination) is admitted only where the caller discards the
            // return, so nothing retains the alias while the slice lives; a
            // used return stays with the returned-child custody it needs.
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
            elements: if byte_pointee(&element_pointee(fact)) {
                Ok(count.expression.clone())
            } else {
                Err(CountGap::UnitsUnproved)
            },
        });
        let requirement = match contract.extent {
            ArgumentExtent::OneElement => Requirement::OneElement,
            // A byte count spelling the pointee's own size is one element
            // (`thin_extent::byte_count_is_one_element`): no slice to build.
            ArgumentExtent::ByteCount if super::thin_extent::byte_count_is_one_element(fact) => {
                Requirement::OneElement
            }
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
    // #1b — the reader chain (relay 005 §2 / R349-1, made native): a caller
    // argument that DENOTES a caller subject and is handed to a local callee
    // parameter that reaches a foreign multi-element position is itself read
    // to that extent. The callee's requirement is propagated to the caller as
    // a `via-local-callee` site, transitively, so the whole chain takes the
    // slice form and no hop narrows to a thin reference. Exact counts do not
    // transport (they belong to the callee's own call): a counted requirement
    // arrives as its count-less twin and takes the fallback extent.
    // Only a callee whose slice form would be DUE to the contract seeds the
    // chain: a parameter that is a slice by its own arithmetic stays R365-2's
    // census item, and its callers are not re-decided here.
    let arithmetic_slice = |node: (LocalDefId, HirId)| -> bool {
        subjects.get(&node).is_some_and(|subject| {
            facts.raw_only_uses.get(&node).is_some_and(|uses| {
                uses.iter()
                    .any(|(op, _)| super::emitability::SLICE_ARITHMETIC_OPS.contains(&op.as_str()))
                    && fat.is_array(node.0, subject.local)
            })
        })
    };
    let mut worklist = by_subject
        .iter()
        .filter(|(node, candidate)| {
            !arithmetic_slice(**node)
                && candidate
                    .sites
                    .iter()
                    .any(|site| !matches!(site.requirement, Requirement::LocalAccess))
        })
        .map(|(&node, _)| node)
        .collect::<Vec<_>>();
    let mut propagated_from = FxHashSet::<((LocalDefId, HirId), (LocalDefId, HirId))>::default();
    while let Some(callee_node) = worklist.pop() {
        let Some(callee_subject) = subjects.get(&callee_node).copied() else { continue };
        let SubjectKind::Param { hir_index } = callee_subject.kind else { continue };
        let Some(sites) = by_subject.get(&callee_node).map(|candidate| {
            candidate
                .sites
                .iter()
                .filter(|site| !matches!(site.requirement, Requirement::LocalAccess))
                .cloned()
                .collect::<Vec<_>>()
        }) else {
            continue;
        };
        let Some(calls) = facts.call_args.get(&callee_node.0) else { continue };
        for call in calls {
            for argument in call
                .args
                .iter()
                .filter(|argument| argument.index == hir_index)
            {
                let root = match argument.shape {
                    ArgShape::BareLocal(root) | ArgShape::CastOfLocal { binding: root, .. } => root,
                    _ => continue,
                };
                let caller_node = (call.caller, root);
                let Some(caller_subject) = subjects.get(&caller_node).copied() else { continue };
                if caller_subject.ptr_depth != 1
                    || arithmetic_slice(caller_node)
                    || !propagated_from.insert((callee_node, caller_node))
                {
                    continue;
                }
                let key = subject_key(caller_subject);
                let construction = construction_key(caller_subject, constructions);
                let had_sites = by_subject.contains_key(&caller_node);
                let candidate = by_subject.entry(caller_node).or_insert_with(|| Candidate {
                    subject: key.clone(),
                    construction: construction.clone(),
                    sites: Vec::new(),
                });
                for site in &sites {
                    candidate.sites.push(ContractSite {
                        subject: key.clone(),
                        site: format!(
                            "owner={}:call={}..{}:callee=local:{}:arg={}:via={}",
                            call.caller.local_def_index.as_u32(),
                            call.span.lo().0,
                            call.span.hi().0,
                            callee_node.0.local_def_index.as_u32(),
                            argument.index,
                            site.site,
                        ),
                        contract: format!(
                            "via-local-callee:{}:{}:{}",
                            callee_node.0.local_def_index.as_u32(),
                            hir_index,
                            site.contract,
                        ),
                        requirement: match &site.requirement {
                            Requirement::ExactAccess(_) => Requirement::ExactAccess(None),
                            Requirement::UpperBound(_) => Requirement::UpperBound(None),
                            Requirement::ElementCount(_) => Requirement::ElementCount(None),
                            other => other.clone(),
                        },
                    });
                }
                if !had_sites {
                    worklist.push(caller_node);
                } else if !worklist.contains(&caller_node) {
                    worklist.push(caller_node);
                }
            }
        }
    }
    for candidate in by_subject.values_mut() {
        candidate
            .sites
            .sort_by(|left, right| left.site.cmp(&right.site));
        candidate
            .sites
            .dedup_by(|left, right| left.site == right.site);
    }
    // R397-6(b): the up-front decline, read from the candidate's own uses
    // before any selection. A declined candidate is never attempted, so no
    // owner or class transaction can withdraw a sibling on its account.
    let local_boundaries = facts
        .call_args
        .values()
        .flatten()
        .flat_map(|call| {
            call.args
                .iter()
                .map(move |argument| (call.caller, argument.span.lo().0, argument.span.hi().0))
        })
        .collect::<rustc_hash::FxHashSet<_>>();
    // R395-2: a caller argument that DENOTES a would-be-thin caller subject —
    // BO `Ref` at its own slot and no array arithmetic of its own — would be
    // widened into the promoted slice by `from_ref`. Counted per candidate
    // parameter over every call site; the callee is declined, never the caller
    // re-decided.
    let model_ref = |node: (LocalDefId, HirId)| -> bool {
        subjects.get(&node).is_some_and(|subject| {
            slots
                .fn_local_slots
                .get(&node.0)
                .and_then(|universe| universe.slot_for_local_depth(subject.local, 0))
                .is_some_and(|slot| {
                    model.get(&SlotRef::Local(node.0, slot)) == Some(&SlotKind::Ref)
                })
        })
    };
    let own_slice = |node: (LocalDefId, HirId)| -> bool {
        subjects.get(&node).is_some_and(|subject| {
            facts.raw_only_uses.get(&node).is_some_and(|uses| {
                uses.iter()
                    .any(|(op, _)| super::emitability::SLICE_ARITHMETIC_OPS.contains(&op.as_str()))
                    && fat.is_array(node.0, subject.local)
            })
        })
    };
    // R407-14 (contract-alone): every use of the subject is a foreign
    // NUL-terminated contract position — no dereference or index (`rewrites`),
    // no return handoff, no raw-only operation, no unsupported use, and every
    // raw use a foreign boundary at a NUL position. The contract positions
    // alone then admit the subject over `Ptr` fatness: the slice is read only
    // through `as_ptr()`.
    let contract_alone = |node: (LocalDefId, HirId)| -> bool {
        slice_uses.get(&node).is_some_and(|uses| {
            uses.unsupported.is_none()
                && uses.rewrites.is_empty()
                && uses.return_handoffs.is_empty()
                && facts
                    .raw_only_uses
                    .get(&node)
                    .is_none_or(|ops| ops.is_empty())
                && !uses.raw_uses.is_empty()
                && uses.raw_uses.iter().all(|raw| {
                    !raw.native_element
                        && raw.boundary_span.is_some_and(|span| {
                            nul_positions.contains(&(node.0, span.lo().0, span.hi().0))
                        })
                })
        })
    };
    let contract_alone_nodes = by_subject
        .keys()
        .copied()
        .filter(|&node| contract_alone(node))
        .collect::<FxHashSet<_>>();
    // A candidate that would PROMOTE under the pure selector's own gates
    // (BO `Ref`, depth 1, `Arr` or contract-alone, at least one multi-element
    // site) and is not declined at this iteration. The chain is decided as a greatest fixpoint:
    // every candidate starts promotable, a decline removes it, and a removal
    // may decline the callee it fed (thin caller) or the caller it carried
    // (local-callee boundary), until nothing moves.
    let promotable = |node: (LocalDefId, HirId), declined: &FxHashMap<_, DeclineCause>| -> bool {
        !declined.contains_key(&node)
            && model_ref(node)
            && subjects.get(&node).is_some_and(|subject| {
                subject.ptr_depth == 1
                    && (fat.is_array(node.0, subject.local) || contract_alone_nodes.contains(&node))
            })
            && by_subject.get(&node).is_some_and(|candidate| {
                candidate.sites.iter().any(|site| {
                    !matches!(
                        site.requirement,
                        Requirement::LocalAccess | Requirement::OneElement | Requirement::Lifecycle
                    )
                })
            })
    };
    // A caller subject with a raw-only use that is neither arithmetic nor a
    // null test is decided raw by the ladder (`raw-pointer-operation`) and is
    // bridged raw, never widened.
    let own_raw_use = |node: (LocalDefId, HirId)| -> bool {
        facts.raw_only_uses.get(&node).is_some_and(|uses| {
            uses.iter().any(|(op, _)| {
                !super::emitability::SLICE_ARITHMETIC_OPS.contains(&op.as_str()) && op != "is_null"
            })
        })
    };
    let would_be_thin =
        |caller: LocalDefId, root: HirId, declined: &FxHashMap<_, DeclineCause>| -> bool {
            let node = (caller, root);
            subjects.contains_key(&node)
                && model_ref(node)
                && !own_slice(node)
                && !own_raw_use(node)
                && !promotable(node, declined)
        };
    let thin_caller_arguments = |node: (LocalDefId, HirId),
                                 declined: &FxHashMap<_, DeclineCause>|
     -> usize {
        let Some(subject) = subjects.get(&node) else { return 0 };
        let SubjectKind::Param { hir_index } = subject.kind else { return 0 };
        facts
            .call_args
            .get(&node.0)
            .into_iter()
            .flatten()
            .flat_map(|call| {
                call.args
                    .iter()
                    .map(move |argument| (call.caller, argument))
            })
            .filter(|(caller, argument)| {
                argument.index == hir_index
                    && match argument.shape {
                        ArgShape::BareLocal(root) | ArgShape::CastOfLocal { binding: root, .. } => {
                            would_be_thin(*caller, root, declined)
                        }
                        _ => false,
                    }
            })
            .count()
    };
    // A raw use at a LOCAL callee argument whose parameter is a promotable
    // candidate of the SAME slice form is carried by the zero-syntax interface
    // carrier (`slice_use.rs`); every other local boundary use stays declined.
    let local_boundary_uses = |node: (LocalDefId, HirId),
                               declined: &FxHashMap<_, DeclineCause>|
     -> usize {
        let Some(uses) = slice_uses.get(&node) else { return 0 };
        let Some(subject) = subjects.get(&node) else { return 0 };
        uses.raw_uses
            .iter()
            .filter(|raw| {
                let Some(span) = raw.boundary_span else { return false };
                // Wave-5c's equal-slice carrier takes a bare-local argument
                // into a parameter that promotes to the same form.
                let carried = raw.source_shape == "bare-local"
                    && facts.call_args.iter().any(|(callee, calls)| {
                    calls.iter().any(|call| {
                        call.caller == node.0
                            && call.args.iter().any(|argument| {
                                argument.span.lo() == span.lo()
                                    && argument.span.hi() == span.hi()
                                    && subjects.values().any(|parameter| {
                                        parameter.fn_did == *callee
                                            && matches!(parameter.kind, SubjectKind::Param { hir_index } if hir_index == argument.index)
                                            && promotable((parameter.fn_did, parameter.hir_id), declined)
                                            && (subject.mutable || !parameter.mutable)
                                    })
                            })
                    })
                });
                local_boundaries.contains(&(node.0, span.lo().0, span.hi().0)) && !carried
            })
            .count()
    };
    let declines_for = |nullable: bool| {
        let mut declined = FxHashMap::<(LocalDefId, HirId), DeclineCause>::default();
        loop {
            let mut changed = false;
            for &node in by_subject.keys() {
                if declined.contains_key(&node) {
                    continue;
                }
                let uses = slice_uses.get(&node);
                let unsupported = if nullable {
                    opt_uses
                        .get(&node)
                        .is_some_and(|uses| uses.unsupported.is_some())
                } else {
                    uses.is_some_and(|uses| uses.unsupported.is_some())
                };
                let mut summary = use_summary(node.0, uses, unsupported, &local_boundaries);
                summary.local_callee_boundary_uses = local_boundary_uses(node, &declined);
                summary.thin_caller_arguments = thin_caller_arguments(node, &declined);
                if let Some(cause) = decline(&summary) {
                    declined.insert(node, cause);
                    changed = true;
                }
            }
            if !changed {
                break declined;
            }
        }
    };
    let declines = declines_for(false);
    let nullable_declines = declines_for(true);
    CandidateIndex {
        by_subject,
        declines,
        nullable_declines,
        contract_alone: contract_alone_nodes,
    }
}

impl CandidateIndex {
    /// R397-6(b): the declined candidates, for the receipt.
    pub(crate) fn declines(&self) -> impl Iterator<Item = (&(LocalDefId, HirId), &DeclineCause)> {
        self.declines.iter()
    }

    /// One TSV row per declined candidate and form — only candidates that
    /// would otherwise PROMOTE (the decline is read after every promotability
    /// gate in [`select`]).
    pub(crate) fn declines_tsv(
        &self,
        tcx: rustc_middle::ty::TyCtxt<'_>,
        subjects: &[Subject],
        model: &FxHashMap<SlotRef, SlotKind>,
        slots: &CrateSlots,
        fat: &FatFacts,
    ) -> String {
        let mut rows = Vec::new();
        for subject in subjects {
            let node = (subject.fn_did, subject.hir_id);
            let Some(candidate) = self.by_subject.get(&node) else { continue };
            let model_kind = slots
                .fn_local_slots
                .get(&subject.fn_did)
                .and_then(|universe| universe.slot_for_local_depth(subject.local, 0))
                .and_then(|slot| model.get(&SlotRef::Local(subject.fn_did, slot)))
                .copied();
            for (form, nullable) in [("plain", false), ("nullable", true)] {
                let selection = self.select(
                    subject,
                    CurrentForm::Ref {
                        mutable: subject.mutable,
                        nullable,
                    },
                    model_kind,
                    fat,
                );
                let Selection::Keep(KeepReason::Declined(cause)) = selection else { continue };
                rows.push(format!(
                    "{}\t{}\t{}\t{}\t{}\t{}\n",
                    tcx.def_path_str(subject.fn_did.to_def_id()),
                    subject.label,
                    candidate.subject,
                    form,
                    cause.receipt(),
                    candidate
                        .sites
                        .iter()
                        .map(|site| site.contract.as_str())
                        .collect::<Vec<_>>()
                        .join(";"),
                ));
            }
        }
        rows.sort();
        let mut out =
            String::from("owner_path\tsubject\tsubject_key\tform\treceipt\tcontract_sites\n");
        out.extend(rows);
        out
    }

    pub(crate) fn select(
        &self,
        subject: &Subject,
        form: CurrentForm,
        model_kind: Option<SlotKind>,
        fat: &FatFacts,
    ) -> Selection {
        let node = (subject.fn_did, subject.hir_id);
        let declines = match form {
            CurrentForm::Ref { nullable: true, .. } => &self.nullable_declines,
            CurrentForm::Ref {
                nullable: false, ..
            }
            | CurrentForm::Slice
            | CurrentForm::Other => &self.declines,
        };
        let Some(candidate) = self.by_subject.get(&node) else {
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
                contract_alone: self.contract_alone.contains(&node),
                non_length: Ok(()),
                decline: declines.get(&node).cloned(),
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
