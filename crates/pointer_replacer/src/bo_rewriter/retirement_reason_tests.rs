//! **R316-1 / R318-3 — the analysis's OWN reason for a subject's Raw.**
//!
//! Reads a fixture source from `CRAT_R316_SOURCE` and prints, from the
//! retirement review rather than from any assertion: every `RetirementConflict`
//! with its `OverlapReason` **and its source event** — role, phase,
//! block:statement, storage local, condition — every unresolved row, the
//! demotions, the coverage dispositions, and a MIR local→name last-use table so
//! "is the subject live at the event" is read from the body.
//!
//! It lives here and not under `analyses/` on purpose: the analyses tree is
//! pinned to the frame's `analyses_tree`, and a diagnostic must not move it.
//!
//! Diagnostic only, `#[ignore]`; nothing gates on it.

use crate::analyses::borrow_ownership::{
    SlotKind,
    a5_overlap::{A5Mode, WholeProgramAttestation},
    construction::solve_bo_a5_config_reporting,
    crate_slots::CrateSlots,
    export::with_bo_export,
    mutability_facts::MutFacts,
    origins::compute_origins,
};

#[test]
#[ignore]
fn r316_1_analysis_reason_for_raw_subjects() {
    let Ok(code) = std::env::var("CRAT_R316_SOURCE") else {
        println!("R316-1: no CRAT_R316_SOURCE");
        return;
    };
    let label = std::env::var("CRAT_R316_LABEL").unwrap_or_default();
    ::utils::compilation::run_compiler_on_str(&code, |tcx| {
        let mut functions = Vec::new();
        let mut structs = Vec::new();
        for owner in tcx.hir_crate(()).owners.iter() {
            let Some(owner) = owner.as_owner() else { continue };
            let rustc_hir::OwnerNode::Item(item) = owner.node() else {
                continue;
            };
            match item.kind {
                rustc_hir::ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
                rustc_hir::ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
                _ => {}
            }
        }
        let program = crate::utils::rustc::RustProgram {
            tcx,
            functions,
            structs,
        };
        let slots = CrateSlots::build(&program);
        let origins = compute_origins(&program);
        let facts = MutFacts::from_program(&program);
        let (result, capture) = with_bo_export(|| {
            solve_bo_a5_config_reporting(
                &program,
                &slots,
                &origins,
                &facts,
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )
        });
        let raw = match &result {
            Ok(model) => model
                .model
                .iter()
                .filter(|(_, kind)| **kind == SlotKind::Raw)
                .count(),
            Err(_) => usize::MAX,
        };
        println!("R316-1 label={label} raw_slots={raw}");

        for &fn_did in &program.functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(fn_did).borrow();
            let owner = tcx.def_path_str(fn_did.to_def_id());
            let named = body
                .var_debug_info
                .iter()
                .filter_map(|info| match &info.value {
                    rustc_middle::mir::VarDebugInfoContents::Place(place) => {
                        place.as_local().map(|l| (l.as_u32(), info.name.to_string()))
                    }
                    _ => None,
                })
                .collect::<Vec<_>>();
            let mut last = std::collections::BTreeMap::<u32, (u32, usize)>::new();
            for (block, data) in body.basic_blocks.iter_enumerated() {
                for (index, statement) in data.statements.iter().enumerate() {
                    let text = format!("{statement:?}");
                    if text.starts_with("StorageDead") || text.starts_with("StorageLive") {
                        continue;
                    }
                    for (local, _) in &named {
                        if text.contains(&format!("_{local}")) {
                            last.insert(*local, (block.as_u32(), index));
                        }
                    }
                }
                let terminator = format!("{:?}", data.terminator().kind);
                for (local, _) in &named {
                    if terminator.contains(&format!("_{local}")) {
                        last.insert(*local, (block.as_u32(), data.statements.len()));
                    }
                }
            }
            for (local, name) in &named {
                if let Some((block, index)) = last.get(local) {
                    println!(
                        "R318-3 label={label} kind=last-use owner={owner} local=_{local} name={name} at={block}:{index}"
                    );
                }
            }
        }

        let mut rounds = capture.retirement_rounds.clone();
        if let Some(final_review) = capture.source_retirement.clone() {
            rounds.push(final_review);
        }
        println!("R316-1 label={label} rounds={}", rounds.len());
        for (index, round) in rounds.iter().enumerate() {
            for conflict in &round.conflicts {
                println!(
                    "R318-3 label={label} kind=round-conflict round={index} target={} overlap={:?} role={:?} phase={:?} event_at={}:{} storage_local={:?} condition={:?} conflict_at={:?}",
                    conflict.target_key,
                    conflict.overlap,
                    conflict.source.role,
                    conflict.source.phase,
                    conflict.source.block,
                    conflict.source.statement,
                    conflict.source.storage_local,
                    conflict.source.condition,
                    conflict.location,
                );
            }
            for row in &round.unresolved {
                println!("R316-1 label={label} kind=unresolved round={index} reason={row:?}");
            }
            for demotion in &round.demotions {
                println!("R316-1 label={label} kind=demotion round={index} {demotion:?}");
            }
        }
    })
    .expect("R316-1 diagnostic compiles its fixture");
}
