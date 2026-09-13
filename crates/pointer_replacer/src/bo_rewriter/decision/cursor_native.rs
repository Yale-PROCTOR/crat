//! R368 native admission observation hook. This hook does not change decisions,
//! types, plans, or delivery. Cursor emission needs explicit shared form support.

use std::{collections::BTreeMap, fs::OpenOptions, io::Write, path::Path};

use rustc_hash::FxHashMap;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{mir::Local, ty::TyCtxt};

use super::{Ctx, Decision, DegradeReason, Subject};
use crate::analyses::borrow_ownership::{SlotKind, crate_slots::CrateSlots, solver::SlotRef};

#[path = "cursor/admission.rs"]
mod admission;

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

pub(crate) fn observe(ctx: &Ctx<'_, '_>, entries: &[(Subject, Decision)]) {
    let Some(directory) = std::env::var_os("CRAT_CURSOR_ADMISSION_OUTPUT") else { return };
    if ctx.raw_boundary.is_none()
        || ctx.family_policy.stage != super::super::additive::FamilyStage::Return
    {
        return;
    }
    // A cache-only corpus worker has one compiler session and one model. The
    // archive is single-use per program; each identity is observed once. The
    // admission proof does not depend on later placement/recovery decisions.
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
    for (subject, decision) in entries {
        let path = root.join(format!(
            "{}-{}.json",
            subject.fn_did.local_def_index.as_u32(),
            subject.hir_id.local_id.as_u32()
        ));
        if path.exists() {
            continue;
        }
        // Collect all named identities, not a docs-derived admission allowlist.
        // The later market join selects 70/44 and the newly routed population.
        let sign = ctx.sign.render(subject.fn_did, subject.local);
        let fat = ctx.fat.is_array(subject.fn_did, subject.local);
        let cursor_reason = match decision {
            Decision::Degraded(d) => is_cursor_reason(&d.reason),
            Decision::Ref { .. }
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
            "emission": is_candidate.then_some("Held(CursorFormUnbuilt)"), "changes_decision": false,
        });
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
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
