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

use rustc_mir_dataflow::Analysis;

use crate::analyses::{
    borrow_ownership::{
        SlotKind,
        a5_overlap::{A5Mode, WholeProgramAttestation},
        construction::solve_bo_a5_config_reporting,
        crate_slots::CrateSlots,
        export::with_bo_export,
        mutability_facts::MutFacts,
        origins::compute_origins,
    },
    liveness::MaybeLiveLocals,
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

        // **R320-2 — liveness by DATAFLOW at the event, not by last-use.**
        //
        // The carry rests on the subject being dead at the conflicting event,
        // and a normal-path last-use table is weaker than the claim: it says
        // nothing about an unwind edge directly. `MaybeLiveLocals` is queried
        // at each event's own location, after the primary effect, and the
        // answer is printed per named local.
        // **R321-1 — the ordering is COMPUTED, not eyeballed.** The seat's
        // criterion (b) is an escape *before* the event, and "before" across
        // basic blocks is CFG reachability, not block numbering. Escape points
        // and a per-function reachability relation are collected here and
        // joined against each conflict's event location below.
        let mut escapes = std::collections::BTreeMap::<String, Vec<(u32, usize, String)>>::new();
        let mut reach = std::collections::BTreeMap::<String, Vec<Vec<u32>>>::new();
        for &fn_did in &program.functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(fn_did).borrow();
            let owner = tcx.def_path_str(fn_did.to_def_id());
            {
                // Forward reachability over ALL successors, unwind edges
                // included: the question is whether control can get from the
                // escape to the event at all.
                let count = body.basic_blocks.len();
                let mut rows = vec![Vec::<u32>::new(); count];
                for start in 0..count {
                    let mut seen = vec![false; count];
                    let mut stack = vec![start];
                    while let Some(current) = stack.pop() {
                        for successor in
                            body.basic_blocks[rustc_middle::mir::BasicBlock::from_usize(current)]
                                .terminator()
                                .successors()
                        {
                            let next = successor.as_usize();
                            if !seen[next] {
                                seen[next] = true;
                                stack.push(next);
                            }
                        }
                    }
                    rows[start] = (0..count)
                        .filter(|block| seen[*block])
                        .map(|block| block as u32)
                        .collect();
                }
                reach.insert(owner.clone(), rows);
            }
            let named = body
                .var_debug_info
                .iter()
                .filter_map(|info| match &info.value {
                    rustc_middle::mir::VarDebugInfoContents::Place(place) => {
                        place.as_local().map(|l| (l, info.name.to_string()))
                    }
                    _ => None,
                })
                .collect::<Vec<_>>();
            let mut cursor = MaybeLiveLocals
                .iterate_to_fixpoint(tcx, &body, None)
                .into_results_cursor(&body);
            // **R321-1 — the query point is the UNWIND SUCCESSOR, not the
            // event's own location.**
            //
            // An `UnwindStorage` event sits at a Call terminator, and the state
            // after that terminator's primary effect is the join of the normal
            // and cleanup successors: it reports every subject with a later
            // NORMAL-path use, which is why the previous reading looked like a
            // live subject everywhere. What obliges a reference is a use
            // reachable on the unwind path itself — the cleanup block's live-in
            // — or an escape of the reference out of the frame before the
            // event.
            for (block, data) in body.basic_blocks.iter_enumerated() {
                let terminator = data.terminator();
                let action = terminator.unwind();
                println!(
                    "R321-1 label={label} kind=unwind-action owner={owner} at=bb{} action={:?}",
                    block.as_u32(),
                    action
                );
                let cleanup = match action {
                    Some(rustc_middle::mir::UnwindAction::Cleanup(target)) => Some(*target),
                    _ => None,
                };
                let Some(cleanup) = cleanup else { continue };
                cursor.seek_to_block_start(cleanup);
                let live_in = cursor.get();
                let names = named
                    .iter()
                    .filter(|(local, _)| live_in.contains(*local))
                    .map(|(local, name)| format!("_{}={name}", local.as_u32()))
                    .collect::<Vec<_>>();
                println!(
                    "R321-1 label={label} kind=unwind-live-in owner={owner} at={}:{} cleanup=bb{} live_in=[{}]",
                    block.as_u32(),
                    data.statements.len(),
                    cleanup.as_u32(),
                    names.join(",")
                );
            }

            // The escape check. Two corrections the CONTROL forced, recorded
            // because without them "not escaped" would have meant nothing:
            //
            //  * the destination must be outside the frame's own locals AND the
            //    local's VALUE must flow into it. `(*q) = *q + 2` mentions the
            //    local on both sides and escapes nothing.
            //  * the store usually goes through an unnamed temporary —
            //    `_5 = copy _1; (*_2).0 = move _5` — so one level of copy is
            //    followed back to the named local. Without this the control
            //    `(*h).first = p` did not fire.
            //
            // The chain is TRANSITIVE and a single-level map does not see it:
            // `consume(p)` against a `*const` parameter lowers to
            // `_6 = copy _1; _5 = move _6 as *const i32 (PtrToPtr); consume(move _5)`,
            // so `_5` reaches the named local only through `_6`. The map is
            // therefore built to a fixpoint, following bare copies AND pointer
            // casts, seeded by the named locals.
            let mut alias = std::collections::BTreeMap::<u32, (u32, String)>::new();
            loop {
                let before = alias.len();
                for data in body.basic_blocks.iter() {
                    for statement in &data.statements {
                        let rustc_middle::mir::StatementKind::Assign(assign) = &statement.kind
                        else {
                            continue;
                        };
                        let Some(dest) = assign.0.as_local() else { continue };
                        if alias.contains_key(&dest.as_u32()) {
                            continue;
                        }
                        let text = format!("{:?}", assign.1);
                        let mut roots = named
                            .iter()
                            .map(|(local, name)| (local.as_u32(), local.as_u32(), name.clone()))
                            .collect::<Vec<_>>();
                        roots.extend(
                            alias
                                .iter()
                                .map(|(temp, (root, name))| (*temp, *root, name.clone())),
                        );
                        for (source, root, name) in roots {
                            let carries = text.trim() == format!("copy _{source}")
                                || text.trim() == format!("move _{source}")
                                || text.starts_with(&format!("copy _{source} as "))
                                || text.starts_with(&format!("move _{source} as "));
                            if carries {
                                alias.insert(dest.as_u32(), (root, name));
                                break;
                            }
                        }
                    }
                }
                if alias.len() == before {
                    break;
                }
            }
            for (block, data) in body.basic_blocks.iter_enumerated() {
                for (index, statement) in data.statements.iter().enumerate() {
                    let rustc_middle::mir::StatementKind::Assign(assign) = &statement.kind else {
                        continue;
                    };
                    let (place, rvalue) = (&assign.0, &assign.1);
                    // The destination must be OUTSIDE the frame's own locals:
                    // a projection through something else, or the return place.
                    let outside = place.as_local().is_none() || place.local.as_u32() == 0;
                    if std::env::var("CRAT_R321_DUMP").is_ok() {
                        println!(
                            "R321-1 label={label} kind=assign owner={owner} at={}:{index} place={place:?} outside={outside} rvalue={:?}",
                            block.as_u32(),
                            rvalue
                        );
                    }
                    if !outside {
                        continue;
                    }
                    // And the local's VALUE must flow into it. `(*q) = *q + 2`
                    // mentions `_2` on both sides and escapes nothing; only a
                    // bare operand, a borrow of it, or a cast of it is the
                    // pointer itself leaving.
                    let text = format!("{rvalue:?}");
                    for (local, name) in &named {
                        let n = local.as_u32();
                        let value_flows = [
                            format!("copy _{n})"),
                            format!("move _{n})"),
                            format!("copy _{n},"),
                            format!("move _{n},"),
                            format!("copy _{n} "),
                            format!("move _{n} "),
                            format!("&_{n}"),
                            format!("&mut _{n}"),
                        ]
                        .iter()
                        .any(|pattern| text.contains(pattern.as_str()))
                            || text.trim() == format!("copy _{n}")
                            || text.trim() == format!("move _{n}");
                        let via_temp = alias.iter().any(|(temp, (root, _))| {
                            *root == n
                                && (text.trim() == format!("copy _{temp}")
                                    || text.trim() == format!("move _{temp}"))
                        });
                        if value_flows || via_temp {
                            println!(
                                "R321-1 label={label} kind=escape owner={owner} at={}:{index} local=_{n} name={name} into={place:?} rvalue={text}",
                                block.as_u32()
                            );
                            escapes.entry(owner.clone()).or_default().push((
                                block.as_u32(),
                                index,
                                name.clone(),
                            ));
                        }
                    }
                }
                // A call argument is a FOURTH escape form. The seat named
                // three — a store to a non-local place, a return, an
                // out-parameter write — and `escape_seam/foreign_arg` is built
                // out of this one: an opaque callee may retain the pointer past
                // the frame. The scan above reads only `Assign` statements, so
                // without this arm that fixture's zero would be a property of
                // the instrument and not of the program.
                if let rustc_middle::mir::TerminatorKind::Call { func, args, .. } =
                    &data.terminator().kind
                {
                    for arg in args.iter() {
                        let text = format!("{:?}", arg.node);
                        for (local, name) in &named {
                            let n = local.as_u32();
                            let direct = text.trim() == format!("copy _{n}")
                                || text.trim() == format!("move _{n}");
                            let via_temp = alias.iter().any(|(temp, (root, _))| {
                                *root == n
                                    && (text.trim() == format!("copy _{temp}")
                                        || text.trim() == format!("move _{temp}"))
                            });
                            if direct || via_temp {
                                // Not every call argument is an escape. A
                                // `core`/`std` pointer intrinsic — `offset`,
                                // `is_null`, `read`, `write`, `cast_mut` — takes
                                // the pointer by value and retains nothing, and
                                // counting those made every fixture look
                                // escaped. The classification is PRINTED rather
                                // than filtered silently, so the reading is
                                // auditable.
                                let callee = format!("{func:?}");
                                let intrinsic = (callee.starts_with("std::ptr::")
                                    || callee.starts_with("core::ptr::"))
                                    && callee.contains("<impl *");
                                println!(
                                    "R321-1 label={label} kind=escape-call owner={owner} at=bb{} callee={callee} retaining={} local=_{n} name={name} arg={text}",
                                    block.as_u32(),
                                    !intrinsic
                                );
                                if !intrinsic {
                                    // A terminator sits after every statement
                                    // in its own block.
                                    escapes.entry(owner.clone()).or_default().push((
                                        block.as_u32(),
                                        data.statements.len(),
                                        name.clone(),
                                    ));
                                }
                            }
                        }
                    }
                }
                if let rustc_middle::mir::TerminatorKind::Return = data.terminator().kind {
                    println!(
                        "R321-1 label={label} kind=return-point owner={owner} at=bb{}",
                        block.as_u32()
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
                // **R321-1 verdict, per event.** An `UnwindStorage` conflict
                // obliges the reference only through (a) a use reachable on the
                // unwind path or (b) an escape of the reference out of the
                // frame BEFORE the event. (a) is reported by the
                // `unwind-live-in` rows above — empty wherever the unwind
                // action is `Continue`/`Unreachable`, because then there is no
                // cleanup block to be live at. (b) is decided here: an escape
                // precedes the event when the escape's block reaches the
                // event's block, or they share a block and the escape comes
                // first.
                let owner = conflict
                    .target_key
                    .split("::")
                    .next()
                    .unwrap_or_default()
                    .to_string();
                let event_block = conflict.source.block;
                let event_statement = conflict.source.statement;
                let preceding = escapes
                    .get(&owner)
                    .map(|rows| {
                        rows.iter()
                            .filter(|(block, statement, _)| {
                                let reaches = reach
                                    .get(&owner)
                                    .and_then(|rows| rows.get(*block as usize))
                                    .map(|targets| targets.contains(&event_block))
                                    .unwrap_or(false);
                                reaches
                                    || (*block == event_block && *statement < event_statement)
                            })
                            .map(|(block, statement, name)| format!("{name}@{block}:{statement}"))
                            .collect::<Vec<_>>()
                    })
                    .unwrap_or_default();
                println!(
                    "R321-1 label={label} kind=event-verdict owner={owner} event_at={}:{} escapes_before=[{}] verdict={}",
                    event_block,
                    event_statement,
                    preceding.join(","),
                    if preceding.is_empty() {
                        "dead-on-unwind-successor-not-escaped"
                    } else {
                        "escaped-before-event"
                    }
                );
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
