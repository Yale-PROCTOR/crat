//! Selected returned-borrow obligations. Uses existing native CallArg loans
//! and the ordinary loan-liveness engine, independently of optional export.
use std::{cell::RefCell, rc::Rc};

use rustc_middle::mir::{Body, Local};
use rustc_span::def_id::LocalDefId;
use serde::{Deserialize, Serialize};

use super::{
    super::{
        coherence::SelectedCopyLendLoan,
        crate_slots::CrateSlots,
        export::{BorrowerKind, PlaceKey, ProjKey},
        l2::MirLocationKey,
        ownership_access::PlaceSyntax,
        solver::SlotRef,
    },
    facts::Facts,
    traversal_correspondence::Proof,
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Receipt {
    pub(crate) origin: Proof,
    /// Native call temporary before the authenticated owner normalization.
    pub(crate) native_loan: PlaceSyntax,
    pub(crate) target: PlaceSyntax,
    pub(crate) receiver: PlaceSyntax,
    pub(crate) live_points: Vec<(u32, usize)>,
    /// CFG frontier of the live-point set; never a numeric min/max interval.
    pub(crate) live_endpoints: Vec<(u32, usize)>,
}

#[derive(Clone)]
pub(crate) struct Expected {
    pub(crate) origin: Proof,
    pub(crate) identity: SelectedCopyLendLoan,
    pub(crate) owner_input: PlaceSyntax,
    pub(crate) receiver: Local,
    target: SlotRef,
}

struct Row {
    function: LocalDefId,
    expected: Expected,
    observed: Vec<Receipt>,
}
#[derive(Default)]
struct Round {
    rows: Vec<Row>,
    missing: Vec<Option<SlotRef>>,
}
thread_local! {static ROUND: RefCell<Option<Round>> = const {RefCell::new(None)};}
pub(crate) struct Scope(Option<Round>);
impl Drop for Scope {
    fn drop(&mut self) {
        ROUND.with(|r| *r.borrow_mut() = self.0.take());
    }
}
impl Scope {
    pub(crate) fn finish(self) -> (Vec<Receipt>, Vec<Option<SlotRef>>) {
        let round = ROUND
            .with(|r| r.borrow_mut().take())
            .expect("traversal replay round");
        let mut failures = round.missing;
        let mut receipts = Vec::new();
        for row in round.rows {
            if row.observed.len() != 1 {
                failures.push(Some(row.expected.target));
            } else {
                receipts.extend(row.observed);
            }
        }
        (receipts, failures)
    }
}

pub(crate) fn begin(
    facts: Option<Rc<Facts>>,
    slots: &CrateSlots,
    is_ref: &impl Fn(SlotRef) -> bool,
) -> Scope {
    let mut round = Round::default();
    if let Some(facts) = facts
        && let Some(frozen) = &facts.licensing
    {
        let selected = super::model_selection::current(&facts);
        for candidate in &frozen.traversal_calls {
            let value = selected
                .as_ref()
                .and_then(|s| s.value(&facts, candidate.guard));
            if value == Some(false) {
                continue;
            }
            let proof = super::traversal_correspondence::certify(&facts, candidate).ok();
            let target = proof
                .as_ref()
                .and_then(|p| {
                    facts.slot_refs.get(&format!(
                        "{}::_{}@d0",
                        candidate.call.caller, p.native.receiver.local
                    ))
                })
                .copied();
            let expected = (|| {
                if value != Some(true) {
                    return None;
                }
                let proof = proof?;
                let target = target?;
                if !is_ref(target) {
                    return None;
                }
                let SlotRef::Local(function, id) = target else { return None };
                let receiver = Local::from_u32(proof.native.receiver.local);
                if slots
                    .fn_local_slots
                    .get(&function)?
                    .slot_for_local_depth(receiver, 0)
                    != Some(id)
                {
                    return None;
                }
                let input = super::traversal_call::input_target(&facts, &proof)?;
                if !proof.native.argument.projection.is_empty() {
                    return None;
                }
                let SlotRef::Local(callee, _) = *facts
                    .slot_refs
                    .get(&format!("{}::_0@d0", candidate.call.callee))?
                else {
                    return None;
                };
                let identity = SelectedCopyLendLoan {
                    location: MirLocationKey {
                        block: candidate.call.block,
                        statement_index: candidate.call.statement,
                    },
                    borrowed: PlaceKey {
                        local: Local::from_u32(proof.native.argument.local),
                        proj: vec![ProjKey::Deref],
                    },
                    borrower: BorrowerKind::CallArg {
                        callee: callee.local_def_index.as_u32(),
                        arg_index: proof.native.argument_index,
                    },
                };
                Some((
                    function,
                    Expected {
                        origin: proof,
                        identity,
                        owner_input: input.place,
                        receiver,
                        target,
                    },
                ))
            })();
            if let Some((function, expected)) = expected {
                round.rows.push(Row {
                    function,
                    expected,
                    observed: Vec::new(),
                });
            } else {
                round.missing.push(target);
            }
        }
    }
    Scope(ROUND.with(|r| r.replace(Some(round))))
}

pub(crate) fn begin_function(function: LocalDefId) -> Vec<Expected> {
    ROUND.with(|r| {
        let mut r = r.borrow_mut();
        let Some(round) = r.as_mut() else { return Vec::new() };
        round
            .rows
            .iter_mut()
            .filter(|r| r.function == function)
            .map(|r| {
                r.observed.clear();
                r.expected.clone()
            })
            .collect()
    })
}

pub(crate) fn observe(
    function: LocalDefId,
    body: &Body<'_>,
    inference: &crate::analyses::borrow::BorrowInferenceResults<'_>,
    expected: &Expected,
    loan: crate::analyses::borrow::Loan,
) {
    let mut live_points = Vec::new();
    let mut live_endpoints = Vec::new();
    let live = |location| {
        inference
            .loan_liveness
            .contains(inference.location_map.point_from_location(location), loan)
    };
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for statement_index in 0..=data.statements.len() {
            let location = rustc_middle::mir::Location {
                block,
                statement_index,
            };
            if !live(location) {
                continue;
            }
            let key = (block.as_u32(), statement_index);
            live_points.push(key);
            let exits_live_set = if statement_index < data.statements.len() {
                !live(rustc_middle::mir::Location {
                    block,
                    statement_index: statement_index + 1,
                })
            } else {
                let successors: Vec<_> = data.terminator().successors().collect();
                successors.is_empty()
                    || successors.into_iter().any(|block| {
                        !live(rustc_middle::mir::Location {
                            block,
                            statement_index: 0,
                        })
                    })
            };
            if exits_live_set {
                live_endpoints.push(key);
            }
        }
    }
    let receipt = Receipt {
        origin: expected.origin.clone(),
        native_loan: PlaceSyntax {
            local: expected.identity.borrowed.local.as_u32(),
            projection: expected.identity.borrowed.proj.clone(),
        },
        target: {
            let mut place = expected.owner_input.clone();
            place.projection.push(ProjKey::Deref);
            place
        },
        receiver: PlaceSyntax {
            local: expected.receiver.as_u32(),
            projection: vec![],
        },
        live_points,
        live_endpoints,
    };
    ROUND.with(|r| {
        if let Some(round) = r.borrow_mut().as_mut() {
            for row in round
                .rows
                .iter_mut()
                .filter(|r| r.function == function && r.expected.identity == expected.identity)
            {
                row.observed.push(receipt.clone());
            }
        }
    });
}

/// Match the accepted obligation to both its selected guard/correspondence and
/// the actual final native Loan record. Standard liveness is a replay output,
/// not reconstructed from a source-name or numeric interval.
pub(crate) fn validate_export(
    accepted: &super::stack_export::Accepted,
    snapshot: &super::snapshot::Snapshot,
    portable: &super::super::portable_export::PortableExport,
) -> Result<(), String> {
    use std::collections::BTreeSet;

    use super::super::portable_export::ExportFamily;
    let required: BTreeSet<_> = accepted
        .traversal_guards
        .iter()
        .filter_map(|(g, selected)| selected.then_some(*g))
        .collect();
    let observed: BTreeSet<_> = accepted
        .traversal_loans
        .iter()
        .map(|r| r.origin.candidate.guard)
        .collect();
    if required != observed || observed.len() != accepted.traversal_loans.len() {
        return Err("accepted returned-loan coverage differs".into());
    }
    let loan_rows: Vec<_> = portable.families[&ExportFamily::Loans]
        .records
        .iter()
        .filter(|r| r.fields.contains_key("returned_borrow"))
        .collect();
    if loan_rows.len() != accepted.traversal_loans.len() {
        return Err("native returned-loan coverage differs".into());
    }
    for receipt in &accepted.traversal_loans {
        let proof = &receipt.origin;
        let call = &proof.candidate.call;
        if !snapshot
            .traversal_correspondences
            .iter()
            .any(|p| p.as_ref().ok() == Some(proof))
        {
            return Err("returned-loan origin differs".into());
        }
        let input = super::traversal_call::input_target(&snapshot.metadata.facts(), proof)
            .ok_or("returned-loan target missing")?;
        let mut borrowed = input.place;
        borrowed.projection.push(ProjKey::Deref);
        if receipt.target != borrowed
            || receipt.receiver != proof.native.receiver
            || receipt.native_loan
                != (PlaceSyntax {
                    local: proof.native.argument.local,
                    projection: vec![ProjKey::Deref],
                })
        {
            return Err("returned-loan target/receiver differs".into());
        }
        let points: BTreeSet<_> = receipt.live_points.iter().copied().collect();
        let endpoints: BTreeSet<_> = receipt.live_endpoints.iter().copied().collect();
        if points.len() != receipt.live_points.len()
            || endpoints.len() != receipt.live_endpoints.len()
            || !endpoints.is_subset(&points)
        {
            return Err("returned-loan liveness shape differs".into());
        }
        let encoded = serde_json::to_value(receipt).map_err(|e| e.to_string())?;
        let matching: Vec<_> = loan_rows
            .iter()
            .filter(|r| r.fields.get("returned_borrow") == Some(&encoded))
            .collect();
        let [row] = matching.as_slice() else {
            return Err("returned-loan native replay differs".into());
        };
        let fields = &row.fields;
        let projections: Vec<_> = borrowed
            .projection
            .iter()
            .map(|p| match p {
                ProjKey::Deref => serde_json::json!({"kind":"deref"}),
                ProjKey::Field(index) => serde_json::json!({"kind":"field","field":index}),
                _ => unreachable!("validated traversal input projection"),
            })
            .collect();
        if fields.get("function") != Some(&serde_json::json!(call.caller))
            || fields.get("location")
                != Some(&serde_json::json!({"block":call.block,"statement":call.statement}))
            || fields.get("place")
                != Some(&serde_json::json!({"local":borrowed.local,"projections":projections}))
            || fields.get("invalid") != Some(&serde_json::json!(false))
        {
            return Err("returned-loan native identity differs".into());
        }
    }
    Ok(())
}
