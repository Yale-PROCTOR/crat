//! Native cursor decisions and compiler-bound admission receipts. The observer
//! reports candidate-stage facts; terminal delivery remains custody-owned.

use std::{collections::BTreeMap, fs::OpenOptions, io::Write, path::Path};

use rustc_hash::FxHashMap;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{mir::Local, ty::TyCtxt};

use super::{Ctx, Decision, DegradeReason, Subject};
use crate::analyses::borrow_ownership::{SlotKind, crate_slots::CrateSlots, solver::SlotRef};

#[path = "cursor/admission.rs"]
mod admission;
#[path = "cursor/delivered.rs"]
mod delivered;
#[path = "cursor/emission.rs"]
mod emission;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CursorPlan {
    pub(crate) uses: Vec<super::emitability::UseEdit>,
    pub(crate) use_hirs: Vec<rustc_hir::HirId>,
    pub(crate) base: Local,
    pub(crate) component: Vec<Local>,
    pub(crate) extent: u64,
    pub(crate) delivered_base: Option<DeliveredBase>,
    pub(crate) bridges: Vec<CursorBridge>,
    pub(crate) local_bridges: Vec<CursorLocalBridge>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct DeliveredBase {
    pub(crate) binding: rustc_hir::HirId,
    pub(crate) window_binding: rustc_hir::HirId,
    pub(crate) initializer: Option<rustc_hir::HirId>,
    pub(crate) provider: DeliveredBaseProvider,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum DeliveredBaseProvider {
    OriginalSlice,
    Slice {
        producer: super::construction::SliceConstructionPlan,
    },
    Box {
        producer: super::box_facts::BoxPlan,
        elements: u64,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CursorLocalBridge {
    pub(crate) destination: rustc_hir::HirId,
    pub(crate) initializer: rustc_hir::HirId,
    pub(crate) access: rustc_hir::HirId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CursorBridge {
    pub(crate) call_hir: rustc_hir::HirId,
    pub(crate) callee: LocalDefId,
    pub(crate) argument_span: rustc_span::Span,
    pub(crate) argument_index: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CursorHold {
    SourceUnavailable,
    UseUnbuilt,
    IndexRangeMissing,
    WindowMissing,
    BaseMissing,
    LayoutUnbuilt,
    ScheduleMissing,
    RawBoundaryUnbuilt,
    DeclarationUnbuilt,
    OptionalUnbuilt,
    RefMissing,
    ComponentAliasUnbuilt,
    BorrowedElementUnbuilt,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CursorReceipt {
    pub(crate) owner: LocalDefId,
    pub(crate) hir_id: rustc_hir::HirId,
    pub(crate) local: Local,
    pub(crate) disposition: Result<(), CursorHold>,
}

pub(crate) fn promote(
    ctx: &Ctx<'_, '_>,
    entries: &mut [(Subject, Decision)],
) -> Vec<CursorReceipt> {
    if !matches!(
        ctx.family_policy.stage,
        super::super::additive::FamilyStage::Return
            | super::super::additive::FamilyStage::Ownership
    ) {
        return vec![];
    }
    let proposals = entries
        .iter()
        .enumerate()
        .filter_map(|(index, (subject, decision))| {
            if !ctx
                .family_policy
                .enabled(subject.fn_did, super::super::additive::FamilyStage::Return)
            {
                return None;
            }
            let proposed = match decision {
                Decision::Degraded(record) => {
                    if is_cursor_reason(&record.reason) {
                        Some(
                            delivered::plan(ctx, subject, entries)
                                .unwrap_or_else(|| emission::plan(ctx, subject, entries)),
                        )
                    } else if matches!(
                        record.reason,
                        DegradeReason::KindRaw | DegradeReason::RawPointerOperation { .. }
                    ) {
                        // An original typed slice is already a reference capability.
                        // The closed administrative rewrite does not fabricate a Ref
                        // model verdict or license a raw base construction.
                        delivered::plan(ctx, subject, entries)
                    } else {
                        None
                    }
                }
                Decision::Ref { .. }
                | Decision::InferredRef { .. }
                | Decision::Slice { .. }
                | Decision::Opt { .. }
                | Decision::Box(_)
                | Decision::NestedSlice { .. }
                | Decision::Cursor { .. } => None,
            };
            proposed.map(|plan| (index, plan))
        })
        .collect::<Vec<_>>();
    let mut receipts = Vec::new();
    for (index, proposed) in proposals {
        let (subject, decision) = &mut entries[index];
        receipts.push(CursorReceipt {
            owner: subject.fn_did,
            hir_id: subject.hir_id,
            local: subject.local,
            disposition: proposed.as_ref().map(|_| ()).map_err(|e| *e),
        });
        if let Ok(plan) = proposed {
            *decision = Decision::Cursor {
                mutable: subject.mutable,
                plan,
            };
        }
    }
    receipts
}

pub(crate) fn inspect_subject(
    tcx: TyCtxt<'_>,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
    subject: &Subject,
) -> admission::Admission {
    let body = tcx
        .mir_drops_elaborated_and_const_checked(subject.fn_did)
        .borrow();
    let kinds = model_kinds(subject.fn_did, body.local_decls.indices(), slots, model);
    admission::inspect(
        tcx,
        subject.fn_did,
        &body,
        admission::Candidate {
            local: subject.local,
            slot_depth: usize::from(subject.ptr_depth.saturating_sub(1)),
            model_kind: kinds
                .get(&subject.local)
                .copied()
                .unwrap_or(admission::ModelKind::Missing),
        },
        &kinds,
    )
}

fn model_kinds(
    owner: LocalDefId,
    locals: impl Iterator<Item = Local>,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
) -> BTreeMap<Local, admission::ModelKind> {
    locals
        .map(|local| {
            let kind = slots
                .fn_local_slots
                .get(&owner)
                .and_then(|universe| universe.slot_for_local_depth(local, 0))
                .and_then(|slot| model.get(&SlotRef::Local(owner, slot)));
            let kind = match kind {
                Some(SlotKind::Ref) => admission::ModelKind::Ref,
                Some(SlotKind::Raw) => admission::ModelKind::Raw,
                Some(SlotKind::Owning) => admission::ModelKind::Owning,
                None => admission::ModelKind::Missing,
            };
            (local, kind)
        })
        .collect()
}

pub(crate) fn observe(
    ctx: &Ctx<'_, '_>,
    entries: &[(Subject, Decision)],
    receipts: &[CursorReceipt],
) {
    let Some(directory) = std::env::var_os("CRAT_CURSOR_ADMISSION_OUTPUT") else { return };
    if ctx.raw_boundary.is_none()
        || !matches!(
            ctx.family_policy.stage,
            super::super::additive::FamilyStage::Return
                | super::super::additive::FamilyStage::Ownership
        )
    {
        return;
    }
    // A cache-only corpus worker has one compiler session and one model. The
    // archive belongs to one worker/frame. Repeated family passes replace a
    // provisional row so the last candidate includes the settled owner stage.
    // Terminal placement/recovery remains a separate custody observation.
    let program =
        std::env::var("CRAT_ERA5_PROGRAM").expect("cursor audit needs compiler worker program pin");
    assert_eq!(
        std::env::var("CRAT_ERA5_EXECUTION_ROLE").as_deref(),
        Ok("cache-only")
    );
    assert!(
        !program.is_empty()
            && program
                .chars()
                .all(|ch| ch.is_ascii_alphanumeric() || "._-".contains(ch))
    );
    let root = Path::new(&directory).join(&program);
    std::fs::create_dir_all(&root).expect("cursor audit directory");
    let frame =
        std::env::var("CRAT_RAW_BOUNDARY_CODE_FRAME").expect("cursor audit needs source frame");
    let custody =
        serde_json::json!({"program": program, "pid": std::process::id(), "frame": frame});
    let guard = root.join("custody.json");
    match OpenOptions::new().write(true).create_new(true).open(&guard) {
        Ok(mut file) => writeln!(file, "{custody}").expect("write native archive custody"),
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
            let prior: serde_json::Value = serde_json::from_slice(
                &std::fs::read(&guard).expect("read native archive custody"),
            )
            .expect("parse native archive custody");
            assert_eq!(
                prior, custody,
                "cursor archive belongs to another worker/frame"
            );
        }
        Err(error) => panic!("cursor archive custody: {error}"),
    }
    for (subject, decision) in entries {
        let path = root.join(format!(
            "{}-{}.json",
            subject.fn_did.local_def_index.as_u32(),
            subject.hir_id.local_id.as_u32()
        ));
        // Collect all named identities, not a docs-derived admission allowlist.
        // The later market join selects 70/44 and the newly routed population.
        let sign = ctx.sign.render(subject.fn_did, subject.local);
        let fat = ctx.fat.is_array(subject.fn_did, subject.local);
        let cursor_reason = match decision {
            Decision::Degraded(d) => is_cursor_reason(&d.reason),
            Decision::Ref { .. }
            | Decision::NestedSlice { .. }
            | Decision::Cursor { .. }
            | Decision::InferredRef { .. }
            | Decision::Slice { .. }
            | Decision::Opt { .. }
            | Decision::Box(_) => false,
        };
        let is_candidate = cursor_reason || (fat && sign == "neg-or-unknown");
        let row = if is_candidate {
            Some(inspect_subject(ctx.tcx, ctx.slots, ctx.model, subject))
        } else {
            None
        };
        let owner = ctx.tcx.def_path_str(subject.fn_did.to_def_id());
        let receipt = serde_json::json!({
            "schema": "cursor-admission-native-v1", "program": program,
            "subject_key": subject.identity_key(&owner), "owner_fn": owner,
            "owner": subject.fn_did.local_def_index.as_u32(), "hir": subject.hir_id.local_id.as_u32(),
            "mir_local": subject.local.index(), "ptr_depth": subject.ptr_depth,
            "candidate": is_candidate, "sign": sign, "fat_array": fat,
            "admission": row.as_ref().map(|r| format!("{:?}", r.status)),
            "shape": row.as_ref().map(|r| format!("{:?}", r.shape)),
            "predicates": row.as_ref().map(|r| r.findings.iter().map(|f| serde_json::json!({
                "predicate": format!("{:?}", f.predicate), "outcome": format!("{:?}", f.outcome),
                "root": f.root.map(|l| l.index()), "site": f.site.map(|s| [s.block, s.statement]),
            })).collect::<Vec<_>>()),
            "component": row.as_ref().map(|r| r.component.iter().map(|l| l.index()).collect::<Vec<_>>()),
            "native_outcome": receipts.iter().find(|r| r.owner == subject.fn_did && r.hir_id == subject.hir_id).map(|r| format!("{:?}", r.disposition)),
            "emission": match decision { Decision::Cursor { .. } => "planned-cursor", Decision::NestedSlice { .. } | Decision::Ref { .. } | Decision::InferredRef { .. } | Decision::Slice { .. } | Decision::Opt { .. } | Decision::Box(_) | Decision::Degraded(_) => "unchanged" },
            "delivered_base": match decision {
                Decision::Cursor { plan, .. } => plan.delivered_base.as_ref().map(|base| serde_json::json!({
                    "binding_hir": base.binding.local_id.as_u32(), "window_hir": base.window_binding.local_id.as_u32(),
                    "initializer_hir": base.initializer.map(|hir| hir.local_id.as_u32()),
                    "provider": format!("{:?}", base.provider), "window": "binding.len()",
                })),
                Decision::NestedSlice { .. } | Decision::Ref { .. } | Decision::InferredRef { .. } | Decision::Slice { .. }
                | Decision::Opt { .. } | Decision::Box(_) | Decision::Degraded(_) => None,
            },
            "stage": "candidate-pre-finalization", "source_frame": frame,
        });
        let mut file = OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(true)
            .open(&path)
            .expect("fresh cursor identity receipt");
        writeln!(file, "{receipt}").expect("write cursor identity receipt");
    }
}

fn is_cursor_reason(reason: &DegradeReason) -> bool {
    matches!(
        reason,
        DegradeReason::SliceNegOrUnknownOffset
            | DegradeReason::SliceCursorUse
            | DegradeReason::SliceUseUnsupported
    )
}

#[cfg(test)]
#[path = "cursor/native_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "cursor/delivered_tests.rs"]
mod delivered_tests;

#[cfg(test)]
#[path = "cursor/custody_tests.rs"]
mod custody_tests;
