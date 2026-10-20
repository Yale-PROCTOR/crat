//! RED-first caller closure controls. Embedded programs are never executed.

use std::collections::{BTreeMap, BTreeSet};

use super::{
    facts::Facts,
    fold_call,
    fold_caller::{self, Hold},
    fold_chain_tests::CODE,
    fold_declaration::Declaration,
    matched::TerminalTarget,
    transport::CandidateGraph,
};

fn with_case(code: &str, check: impl FnOnce(&Facts, &Declaration, &fold_call::Proof) + Send) {
    super::graph_tests::with_facts(code, move |facts| {
        let [declaration] = facts
            .fold_declarations
            .as_deref()
            .expect("declaration inventory")
        else {
            panic!("one exact conditional child call")
        };
        let fold = fold_call::certify(
            facts,
            &declaration.call,
            declaration.argument,
            &BTreeSet::new(),
        )
        .expect("callee and call correspondence qualify independently of caller closure");
        check(facts, declaration, &fold);
    });
}

#[test]
fn gf08_caller_certificate_keeps_two_endpoint_identities_and_exact_cell_closure() {
    with_case(CODE, |facts, declaration, fold| {
        let proof = fold_caller::certify(facts, declaration, fold)
            .expect("complete straight caller needs its conditional certificate");
        assert_eq!(proof.guard, declaration.guard);
        assert_eq!(&proof.fold, fold);
        assert!(proof.required_closed_frame);
        assert_ne!(proof.payload.source, proof.container.source);
        assert_ne!(
            proof.payload.source.endpoint,
            proof.container.source.endpoint
        );
        assert_ne!(proof.payload.free, proof.container.free);
        let graph = CandidateGraph::build(facts);
        let sources: BTreeSet<_> = graph.sources.iter().map(|s| s.equation).collect();
        let frees: BTreeSet<_> = graph.sinks.iter().map(|s| s.equation).collect();
        assert_eq!(
            sources,
            BTreeSet::from([
                proof.payload.source.endpoint,
                proof.container.source.endpoint,
            ])
        );
        assert_eq!(
            frees,
            BTreeSet::from([proof.payload.free, proof.container.free])
        );
        for route in [&proof.payload, &proof.container] {
            assert_eq!(route.meet.source, route.source);
            assert_eq!(route.meet.terminal.target, TerminalTarget::Free(route.free));
            assert!(!route.source_nodes.is_empty());
            assert!(!route.source_meets.is_empty());
            assert!(
                route
                    .source_meets
                    .iter()
                    .all(|meet| meet.source == route.source)
            );
        }
        assert_eq!(proof.store.site.place, proof.reset.site.place);
        assert_eq!(proof.store.site.field_key, proof.reset.site.field_key);
        assert_ne!(proof.null_init.site.field_key, proof.store.site.field_key);
        assert_eq!(proof.forwarding.guard, proof.guard);
        assert_eq!(proof.forwarding.fold.as_ref(), fold);
        assert_eq!(
            proof.forwarding.forwarding.continuation.source,
            proof.payload.source
        );
        assert_eq!(
            proof.forwarding.forwarding.continuation.terminal.target,
            TerminalTarget::Free(proof.payload.free),
        );
        let guards: BTreeMap<_, _> = proof.requirements.guards.iter().copied().collect();
        for endpoint in sources.iter().chain(&frees) {
            assert_eq!(
                guards.get(endpoint),
                Some(&true),
                "retain original endpoint {endpoint:?}"
            );
        }
        assert!(proof.requirements.zero.contains(&fold.actual_after));
        assert!(proof.requirements.zero.contains(&proof.reset.after));
        assert!(!proof.checked_occurrences.is_empty());
        assert!(!proof.checked_consumes.is_empty());
        assert!(!proof.checked_equations.is_empty());
        assert!(!proof.terminal_inventory.is_empty());
        for receipt in [&proof.store, &proof.reset, &proof.null_init] {
            assert!(!receipt.equations.is_empty());
            assert!(proof.checked_consumes.contains(&receipt.consume));
            assert!(
                receipt
                    .equations
                    .iter()
                    .all(|id| proof.checked_equations.contains(id))
            );
        }
        let caller = &fold.call.caller;
        let expected_occurrences: BTreeSet<_> = facts.source_occurrences[caller]
            .iter()
            .map(|row| row.site.clone())
            .collect();
        assert_eq!(
            proof
                .checked_occurrences
                .iter()
                .cloned()
                .collect::<BTreeSet<_>>(),
            expected_occurrences,
            "caller source rows may not disappear from the effect audit",
        );
        let snapshot = super::snapshot::Snapshot::capture(facts, 0).unwrap();
        let rebuilt = snapshot.metadata.facts();
        assert!(rebuilt.guards.is_empty());
        assert_eq!(
            fold_caller::certify_metadata(
                &rebuilt,
                declaration,
                fold,
                &snapshot.metadata.guard_aliases.iter().copied().collect(),
                &snapshot.metadata.slot_keys.iter().cloned().collect(),
            ),
            Ok(proof),
            "caller closure reconstructs without guard ASTs or runtime SlotRefs",
        );
    });
}

#[test]
fn gf08_caller_partner_free_is_competing_responsibility() {
    let code = CODE.replace(
        " free(result as *mut core::ffi::c_void);",
        " free(node as *mut core::ffi::c_void);\n free(result as *mut core::ffi::c_void);",
    );
    assert_ne!(code, CODE, "partner-free fixture mutation applied");
    with_case(&code, |facts, declaration, fold| {
        let graph = CandidateGraph::build(facts);
        assert_eq!(graph.sources.len(), 2);
        assert_eq!(
            graph.sinks.len(),
            3,
            "the extra original free remains visible"
        );
        assert_eq!(
            fold_caller::certify(facts, declaration, fold),
            Err(Hold::CompetingResponsibility),
        );
    });
}

#[test]
fn gf08_caller_opaque_escape_is_an_unsupported_effect() {
    let code = CODE
        .replace(
            "pub struct Holder",
            "unsafe extern \"C\"{fn retain(p:*mut Node);}\npub struct Holder",
        )
        .replace(
            " free(result as *mut core::ffi::c_void);",
            " retain(result);\n free(result as *mut core::ffi::c_void);",
        );
    assert_ne!(code, CODE, "opaque-call fixture mutation applied");
    with_case(&code, |facts, declaration, fold| {
        assert!(
            facts.source_occurrences[&fold.call.caller]
                .iter()
                .any(|row| {
                    row.callee
                        == Some(super::super::origin_evidence::SourceCallee::ForeignC(
                            "retain".into(),
                        ))
                })
        );
        assert_eq!(
            fold_caller::certify(facts, declaration, fold),
            Err(Hold::UnsupportedEffect),
        );
    });
}

#[test]
fn gf08_caller_missing_reset_stays_outside_the_initial_scope() {
    let code = CODE.replace(" (*holder).ptr=0 as *mut Node;\n", "");
    assert_ne!(code, CODE, "only the container-cell reset was removed");
    with_case(&code, |facts, declaration, fold| {
        assert_eq!(
            fold_caller::certify(facts, declaration, fold),
            Err(Hold::MissingReset),
        );
    });
}

#[test]
fn gf08_endpoint_subcheck_joins_both_sources_and_all_original_frees() {
    with_case(CODE, |facts, declaration, fold| {
        let (payload, container) = fold_caller::endpoint_routes(
            facts,
            declaration,
            fold,
            &super::matched::guard_aliases(&facts.guards),
        )
        .unwrap();
        assert_ne!(payload.source, container.source);
        assert_ne!(payload.free, container.free);
        let graph = CandidateGraph::build(facts);
        assert_eq!(
            graph
                .sources
                .iter()
                .map(|s| s.equation)
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([payload.source.endpoint, container.source.endpoint])
        );
        assert_eq!(
            graph
                .sinks
                .iter()
                .map(|s| s.equation)
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([payload.free, container.free])
        );
        for route in [&payload, &container] {
            assert!(route.source_meets.contains(&route.meet));
            assert_eq!(route.meet.terminal.target, TerminalTarget::Free(route.free));
        }
    });
}

#[test]
fn gf08_endpoint_subcheck_keeps_partner_frees_before_the_field_route() {
    let code = CODE.replace(
        " free(result as *mut core::ffi::c_void);",
        " free(node as *mut core::ffi::c_void);\n free(result as *mut core::ffi::c_void);",
    );
    with_case(&code, |facts, declaration, fold| {
        assert_eq!(
            fold_caller::endpoint_routes(
                facts,
                declaration,
                fold,
                &super::matched::guard_aliases(&facts.guards)
            ),
            Err(Hold::CompetingResponsibility)
        );
    });
}

#[test]
fn gf08_cell_subcheck_authenticates_null_store_load_reset_and_order() {
    with_case(CODE, |facts, declaration, fold| {
        let aliases = super::matched::guard_aliases(&facts.guards);
        let (payload, container) =
            fold_caller::endpoint_routes(facts, declaration, fold, &aliases).unwrap();
        let plan = fold_caller::cell_plan(facts, fold, &payload, &container, &aliases).unwrap();
        assert_eq!(plan.store.site.place, plan.reset.site.place);
        let at = |site: &super::field_support::Site| (plan.order[&site.block], site.statement);
        assert!(at(&plan.null_init.site) < at(&plan.store.site));
        assert!(at(&plan.store.site) < (plan.order[&fold.call.block], fold.call.statement));
        assert!((plan.order[&fold.call.block], fold.call.statement) < at(&plan.reset.site));
        assert_eq!(
            plan.sites.len(),
            facts.source_occurrences[&fold.call.caller].len()
        );
        assert!(!plan.terminals.is_empty());
    });
}

#[test]
fn gf08_cell_subcheck_missing_reset_and_opaque_effect_are_typed() {
    let missing = CODE.replace(" (*holder).ptr=0 as *mut Node;\n", "");
    with_case(&missing, |facts, declaration, fold| {
        let aliases = super::matched::guard_aliases(&facts.guards);
        let (payload, container) =
            fold_caller::endpoint_routes(facts, declaration, fold, &aliases).unwrap();
        assert_eq!(
            fold_caller::cell_plan(facts, fold, &payload, &container, &aliases),
            Err(Hold::MissingReset)
        );
    });
    let opaque = CODE
        .replace(
            "pub struct Holder",
            "unsafe extern \"C\"{fn retain(p:*mut Node);}\npub struct Holder",
        )
        .replace(
            " free(result as *mut core::ffi::c_void);",
            " retain(result);\n free(result as *mut core::ffi::c_void);",
        );
    with_case(&opaque, |facts, _declaration, fold| {
        assert_eq!(
            fold_caller::check_effects(facts, fold, &super::matched::guard_aliases(&facts.guards)),
            Err(Hold::UnsupportedEffect)
        );
    });
}

#[test]
fn gf08_law_subcheck_requires_linear_choices_components_and_final_zeros() {
    with_case(CODE, |facts, declaration, fold| {
        let aliases = super::matched::guard_aliases(&facts.guards);
        let (payload, container) =
            fold_caller::endpoint_routes(facts, declaration, fold, &aliases).unwrap();
        let cell = fold_caller::cell_plan(facts, fold, &payload, &container, &aliases).unwrap();
        let plan =
            super::fold_laws::audit(facts, fold, &payload, &container, &cell, &aliases).unwrap();
        assert!(plan.owning.contains(&fold.actual_before) && plan.owning.contains(&fold.receiver));
        assert!(plan.zero.contains(&fold.actual_after) && plan.zero.contains(&cell.reset.after));
        let mut missing = facts.clone();
        let index = missing
            .equations
            .iter()
            .position(|e| {
                e.point.function.as_ref() == Some(&fold.call.caller)
                    && e.assumption_class.as_deref() == Some("temporary-finalization")
            })
            .unwrap();
        missing.equations.remove(index);
        assert_eq!(
            super::fold_laws::audit(&missing, fold, &payload, &container, &cell, &aliases),
            Err(Hold::LawCoverage)
        );
        let mut missing = facts.clone();
        let equation=missing.equations.iter().find(|e|e.point.function.as_ref()==Some(&fold.call.caller) && e.operation=="linear"
            && e.transfer.as_ref().is_some_and(|t|matches!(&t.source,super::super::ownership_occurrence::Availability::Present(s) if !s.path.is_empty()))).unwrap().clone();
        let transfer = equation.transfer.as_ref().unwrap();
        missing
            .equations
            .retain(|e| !(e.point == equation.point && e.transfer.as_ref() == Some(transfer)));
        assert_eq!(
            super::fold_laws::audit(&missing, fold, &payload, &container, &cell, &aliases),
            Err(Hold::LawCoverage),
            "joint descendant law/old-zero omission cannot shrink coverage"
        );
    });
}

#[test]
fn gf08_caller_borrowed_container_and_global_escape_remain_held() {
    let borrowed = CODE
        .replace(
            " let holder=malloc(core::mem::size_of::<Holder>()) as *mut Holder;",
            " let mut storage=Holder{ptr:0 as *mut Node};let holder=&mut storage as *mut Holder;",
        )
        .replace(" free(holder as *mut core::ffi::c_void);", "");
    with_case(&borrowed, |facts, declaration, fold| {
        assert_eq!(
            fold_caller::certify(facts, declaration, fold),
            Err(Hold::UnsupportedEffect),
            "borrowed-container view requires its own certificate"
        );
    });
    let global = CODE
        .replace(
            "pub struct Holder",
            "static mut SAVED:*mut Node=0 as *mut Node;\npub struct Holder",
        )
        .replace(
            " free(result as *mut core::ffi::c_void);",
            " SAVED=result;\n free(result as *mut core::ffi::c_void);",
        );
    with_case(&global, |facts, declaration, fold| {
        assert_eq!(
            fold_caller::certify(facts, declaration, fold),
            Err(Hold::UnsupportedEffect),
            "global escape is not a closed caller"
        );
    });
}

#[test]
fn gf08_caller_reset_after_payload_free_stays_outside_initial_order() {
    let code = CODE
        .replace(" (*holder).ptr=0 as *mut Node;\n", "")
        .replace(
            " free(result as *mut core::ffi::c_void);",
            " free(result as *mut core::ffi::c_void);\n (*holder).ptr=0 as *mut Node;",
        );
    with_case(&code, |facts, declaration, fold| {
        assert_eq!(
            fold_caller::certify(facts, declaration, fold),
            Err(Hold::CellIdentity)
        );
    });
}

/// R348-1(i): the occurrence behind `Caller.UnsupportedEffect`, read back out
/// of a recorded entry.
///
/// `fold_caller::Hold` has ten variants and none carries a payload, so an
/// entry records that the caller gate refused but not what it refused. The
/// occurrence is recoverable without a solve: `snapshot.metadata` carries the
/// facts the gate reads, exactly as `fold_custody::validate` already rebuilds
/// them, so the gate can be asked again over the recorded metadata.
///
/// Diagnostic only — it writes nothing and solves nothing. Point
/// `CRAT_ERA5B_ENTRY` at a joint cache entry and run it directly:
///
/// ```text
/// CRAT_ERA5B_ENTRY=<cache>/era5b-model-cache-v1/<key>.json \
///   pointer_replacer-<hash> --ignored --exact \
///   analyses::borrow_ownership::licensing::fold_caller_tests::r348_caller_gate_occurrences_of_a_recorded_entry \
///   --nocapture --test-threads=1
/// ```
#[test]
#[ignore = "reads a recorded cache entry named by the environment"]
fn r348_caller_gate_occurrences_of_a_recorded_entry() {
    use super::{
        super::origin_evidence::{OriginEvidence, SourceCallee},
        fold_eligibility::Hold as Eligibility,
    };

    // R325-1: the first line of a `--nocapture` run shares the test-name line.
    eprintln!();
    let path = std::env::var("CRAT_ERA5B_ENTRY").expect("CRAT_ERA5B_ENTRY names a cache entry");
    let bytes = std::fs::read(&path).expect("readable cache entry");
    let entry: serde_json::Value = serde_json::from_slice(&bytes).expect("entry json");
    let program = entry["inputs"]["program"]
        .as_str()
        .unwrap_or("?")
        .to_owned();
    let origin: OriginEvidence =
        serde_json::from_value(entry["origin"].clone()).expect("recorded origin evidence");
    let snapshots = origin.licensing.as_deref().unwrap_or_default();
    eprintln!("ENTRY {program} snapshots={}", snapshots.len());

    let mut reported = BTreeSet::new();
    for snapshot in snapshots {
        let facts = snapshot.metadata.facts();
        // A re-derived snapshot has no Z3-valued guards, so the whole-facts
        // builders would see none: the recorded aliases are the only ones.
        let aliases: BTreeMap<_, _> = snapshot.metadata.guard_aliases.iter().copied().collect();
        let sites: BTreeSet<_> = facts
            .fold_declarations
            .as_deref()
            .unwrap_or_default()
            .iter()
            .map(|d| (d.call.caller.clone(), d.call.block, d.call.statement))
            .collect();
        for decision in snapshot.fold_callers.as_deref().unwrap_or_default() {
            let call = &decision.declaration.call;
            let recorded = match &decision.outcome {
                Ok(_) => "certified".to_owned(),
                Err(Eligibility::Caller(hold)) => format!("Caller.{hold:?}"),
                Err(Eligibility::Call(error)) => format!("Call.{error:?}"),
                Err(Eligibility::Declaration) => "Declaration".to_owned(),
            };
            // One line per declaration even when the gate is not the reason,
            // so a reader can see which refusals this census cannot explain.
            if !reported.insert((call.caller.clone(), call.block, call.statement)) {
                continue;
            }
            let Ok(refused) = fold_caller::unsupported_occurrences(&facts, call, &aliases) else {
                eprintln!(
                    "CALLERGATE {program} {} {}:{} recorded={recorded} coverage-hold",
                    call.caller, call.block, call.statement
                );
                continue;
            };
            if refused.is_empty() {
                // R365-3: the gate refuses nothing, so the hold is past it. Print
                // the payload endpoint's origin atoms and this call's argument
                // substitutions — the two sides of the owner-return premise.
                let payload = payload_atoms(&facts, &aliases, decision);
                eprintln!(
                    "CALLERGATE {program} {} {}:{} recorded={recorded} occurrences=0{payload}",
                    call.caller, call.block, call.statement
                );
                continue;
            }
            let body = facts
                .reader_inputs
                .bodies
                .iter()
                .find(|body| body.function == call.caller);
            for occurrence in &refused {
                let site = (occurrence.site.block, occurrence.site.statement);
                let class = match &occurrence.callee {
                    Some(SourceCallee::RustLibrary(_))
                        if body.is_some_and(|b| b.readonly_intrinsic(site.0, site.1)) =>
                    {
                        "read-only-intrinsic"
                    }
                    Some(SourceCallee::Local(name)) => {
                        let reader = (0..4).any(|index| {
                            facts.reader_plan.lends_parameter(name, index)
                                || facts.reader_plan.borrows_parameter(name, index)
                        });
                        if sites.contains(&(call.caller.clone(), site.0, site.1)) {
                            "another-fold-site"
                        } else if reader {
                            "reader-call"
                        } else {
                            "producing-local-call"
                        }
                    }
                    _ => "other",
                };
                // R363-1: the two halves of D3, printed for the class it
                // governs, so a producer that stays refused says which half.
                let d3 = if class == "producing-local-call" {
                    use super::super::origin_evidence::OriginAvailability;
                    let pointers = occurrence
                        .arguments
                        .iter()
                        .filter(|argument| matches!(argument, OriginAvailability::Present(_)))
                        .count();
                    let node = facts
                        .consumes
                        .iter()
                        .filter(|consume| {
                            consume.point.function.as_deref() == Some(call.caller.as_str())
                                && consume.point.block == Some(site.0)
                                && consume.point.statement == Some(site.1)
                                && consume.local == occurrence.syntax.destination.local
                                && consume.projection == occurrence.syntax.destination.projection
                        })
                        .map(|consume| (consume.point.construction, consume.projected.clone()))
                        .collect::<Vec<_>>();
                    let origins =
                        super::value_origins::ValueOrigins::build_metadata(&facts, &aliases)
                            .expect("recorded aliases rebuild the origins");
                    let atoms = node
                        .iter()
                        .filter_map(|(construction, projected)| match projected {
                            super::super::ownership_occurrence::Availability::Present(window)
                                if window.def_start != window.def_end =>
                            {
                                Some(origins.at(super::transport::Node {
                                    construction: *construction,
                                    var: window.def_start,
                                }))
                            }
                            _ => None,
                        })
                        .collect::<Vec<_>>();
                    // The callee's OWN exit-return ports and their origins:
                    // "fresh on every path by its own certificate" is a
                    // question about the callee, not about the caller's
                    // substituted value.
                    let callee_name = match &occurrence.callee {
                        Some(SourceCallee::Local(name)) => name.clone(),
                        _ => String::new(),
                    };
                    use super::super::ownership_boundary::{Role, Variables};
                    let returns = facts
                        .boundary_substitutions
                        .iter()
                        .filter(|row| {
                            row.point.function.as_deref() == Some(callee_name.as_str())
                                && row.role == Role::ExitReturn
                        })
                        .flat_map(|row| {
                            row.matched
                                .iter()
                                .filter_map(move |pair| match pair.formal {
                                    Variables::Single { var } => Some(super::transport::Node {
                                        construction: row.point.construction,
                                        var,
                                    }),
                                    _ => None,
                                })
                        })
                        .map(|node| (node.var, origins.at(node)))
                        .collect::<Vec<_>>();
                    // Which of the two readings: no source seed in the
                    // callee at all, or a seed whose chain never reaches the
                    // exit-return port.
                    let graph = CandidateGraph::build_metadata(&facts, &aliases)
                        .expect("recorded aliases rebuild the graph");
                    let sources = graph
                        .sources
                        .iter()
                        .filter(|source| {
                            facts.equations.iter().any(|equation| {
                                equation.point.construction == source.equation.construction
                                    && equation.ordinal == source.equation.ordinal
                                    && equation.point.function.as_deref()
                                        == Some(callee_name.as_str())
                            })
                        })
                        .map(|source| (source.node.var, origins.at(source.node)))
                        .collect::<Vec<_>>();
                    let every_source = graph
                        .sources
                        .iter()
                        .map(|source| {
                            facts
                                .equations
                                .iter()
                                .find(|equation| {
                                    equation.point.construction == source.equation.construction
                                        && equation.ordinal == source.equation.ordinal
                                })
                                .and_then(|equation| equation.point.function.clone())
                                .unwrap_or_default()
                        })
                        .collect::<std::collections::BTreeSet<_>>();
                    format!(
                        " d3-pointer-arguments={pointers} d3-consumes={} d3-origins={atoms:?} d3-callee-returns={returns:?} d3-callee-sources={sources:?} d3-source-functions={every_source:?}",
                        node.len()
                    )
                } else {
                    String::new()
                };
                eprintln!(
                    "CALLERGATE {program} {} {}:{} recorded={recorded} refused={}:{} class={class} kind={:?} callee={:?} expr={:?}{d3}",
                    call.caller,
                    call.block,
                    call.statement,
                    site.0,
                    site.1,
                    occurrence.kind,
                    occurrence.callee,
                    occurrence.syntax.expression
                );
            }
        }
    }
}

/// R350-3(2): the certificate re-derived over a recorded entry, so a refusal
/// that carried no payload when the entry was written can be read with one now.
///
/// `fold_custody::validate` already re-derives the plan from
/// `snapshot.metadata` in production; this prints what that re-derivation says
/// beside what the entry recorded. A disagreement is expected exactly where the
/// certificate has since learned to say more — it is not a custody failure,
/// because nothing here validates an entry.
#[test]
#[ignore = "reads a recorded cache entry named by the environment"]
fn r350_internal_certificate_gap_of_a_recorded_entry() {
    use super::super::origin_evidence::OriginEvidence;

    eprintln!(); // R325-1
    let path = std::env::var("CRAT_ERA5B_ENTRY").expect("CRAT_ERA5B_ENTRY names a cache entry");
    let bytes = std::fs::read(&path).expect("readable cache entry");
    let entry: serde_json::Value = serde_json::from_slice(&bytes).expect("entry json");
    let program = entry["inputs"]["program"]
        .as_str()
        .unwrap_or("?")
        .to_owned();
    let origin: OriginEvidence =
        serde_json::from_value(entry["origin"].clone()).expect("recorded origin evidence");

    let mut seen = BTreeSet::new();
    for snapshot in origin.licensing.as_deref().unwrap_or_default() {
        let facts = snapshot.metadata.facts();
        let aliases = snapshot.metadata.guard_aliases.iter().copied().collect();
        let keys = snapshot.metadata.slot_keys.iter().cloned().collect();
        let rederived = super::fold_eligibility::plan_metadata(&facts, &aliases, &keys);
        let recorded = snapshot.fold_callers.as_deref().unwrap_or_default();
        for row in rederived.as_deref().unwrap_or_default() {
            let call = &row.declaration.call;
            if !seen.insert((call.caller.clone(), call.block, call.statement)) {
                continue;
            }
            let was = recorded
                .iter()
                .find(|other| other.declaration.guard == row.declaration.guard)
                .map(|other| match &other.outcome {
                    Ok(_) => "certified".to_owned(),
                    Err(hold) => format!("{hold:?}"),
                })
                .unwrap_or_else(|| "absent".to_owned());
            let now = match &row.outcome {
                Ok(_) => "certified".to_owned(),
                Err(hold) => format!("{hold:?}"),
            };
            eprintln!(
                "REDERIVED {program} {} {}:{} recorded={was} rederived={now} agree={}",
                call.caller,
                call.block,
                call.statement,
                was == now
            );
        }
    }
}

/// R363-1 D3/K-D3. The admitted branch and both halves of its conjunction.
/// A producer handed no pointer, whose return is fresh on every path by its own
/// certificate, moves no token out of this caller. A callee handed a pointer
/// does, and so does one whose return is not fresh — neither is admitted by the
/// freshness half or the argument half alone.
#[test]
fn r363_producer_return_is_admitted_and_both_halves_of_d3_still_refuse() {
    const PRELUDE: &str = r#"
unsafe extern "C"{fn malloc(n:usize)->*mut core::ffi::c_void;fn free(p:*mut core::ffi::c_void);}
pub struct Node{child:*mut Node}
pub struct Holder{ptr:*mut Node}
pub static mut ROOT:*mut Node=0 as *mut Node;
pub unsafe fn identity(node:*mut Node)->*mut Node{node}
pub unsafe fn make()->*mut Node{malloc(core::mem::size_of::<Node>()) as *mut Node}
pub unsafe fn swap(old:*mut Node)->*mut Node{
 free(old as *mut core::ffi::c_void);
 malloc(core::mem::size_of::<Node>()) as *mut Node
}
pub unsafe fn peek()->*mut Node{ROOT}
"#;
    let body = |producer: &str| {
        format!(
            r#"{PRELUDE}
pub unsafe fn run(){{
 let node=malloc(core::mem::size_of::<Node>()) as *mut Node;
 (*node).child=0 as *mut Node;
 let holder=malloc(core::mem::size_of::<Holder>()) as *mut Holder;
 (*holder).ptr=node;
 let extra={producer};
 let result=identity((*holder).ptr);
 (*holder).ptr=0 as *mut Node;
 free(result as *mut core::ffi::c_void);
 free(extra as *mut core::ffi::c_void);
 free(holder as *mut core::ffi::c_void);
}}
"#
        )
    };
    let refused_local = |code: String, callee: &'static str| {
        let (send, recv) = std::sync::mpsc::channel();
        super::graph_tests::with_facts(&code, move |facts| {
            let declarations = facts.fold_declarations.as_deref().unwrap_or_default();
            let declaration = declarations
                .iter()
                .find(|declaration| declaration.call.callee == "identity")
                .expect("the identity fold declaration");
            let refused = fold_caller::unsupported_occurrences(
                facts,
                &declaration.call,
                &super::matched::guard_aliases(&facts.guards),
            )
            .expect("the gate itself is covered");
            send.send(refused.iter().any(|occurrence| {
                matches!(
                    &occurrence.callee,
                    Some(super::super::origin_evidence::SourceCallee::Local(name))
                        if name == callee
                )
            }))
            .expect("one verdict");
        });
        recv.recv().expect("the gate ran")
    };
    assert!(
        !refused_local(body("make()"), "make"),
        "D3: no pointer in, a fresh pointer out — no token leaves this caller"
    );
    assert!(
        refused_local(body("swap(node)"), "swap"),
        "K-D3: a pointer argument can be consumed, and a fresh return does not \
         say it was not"
    );
    assert!(
        refused_local(body("peek()"), "peek"),
        "K-D3: taking no pointer does not make the return fresh"
    );
}

/// R365-3: the payload endpoint's origin atoms for one recorded declaration,
/// plus this call's argument substitutions. Reproduces `endpoint_routes`' own
/// lookup up to the point where it asks `ValueOrigins`, so the two read the same
/// node.
fn payload_atoms(
    facts: &Facts,
    aliases: &BTreeMap<super::facts::EquationId, super::facts::EquationId>,
    decision: &super::fold_eligibility::Decision,
) -> String {
    use super::{
        super::{
            origin_evidence::SourceCallee, ownership_boundary::Role,
            ownership_occurrence::Availability::Present,
        },
        transport::Node,
    };
    let _ = SourceCallee::ForeignC(String::new());
    let call = &decision.declaration.call;
    let Ok(fold) = fold_call::certify_metadata(
        facts,
        call,
        decision.declaration.argument,
        &BTreeSet::new(),
        aliases,
    ) else {
        return " payload=no-fold".to_owned();
    };
    let scope = |p: &super::super::ownership_evidence::Point| {
        p.construction == call.construction && p.function.as_ref() == Some(&call.caller)
    };
    let Some(actual) = facts
        .consumes
        .iter()
        .find(|c| scope(&c.point) && c.ordinal == fold.actual_consume)
    else {
        return " payload=no-consume".to_owned();
    };
    let Some(store) = facts.field_support_inputs.stores.iter().find(|s| {
        s.site.function == call.caller
            && s.site.place.local == actual.local
            && s.site.place.projection == actual.projection
            && matches!(s.value, super::field_support::StoredValue::Value(_))
    }) else {
        return " payload=no-store".to_owned();
    };
    let Some(equation) = facts.equations.iter().find(|e| {
        scope(&e.point)
            && e.point.block == Some(store.site.block)
            && e.point.statement == Some(store.site.statement)
            && matches!(e.operation.as_str(), "linear" | "equal")
            && e.transfer.as_ref().is_some_and(|t| {
                matches!(&t.destination, Present(d)
                    if d.local == actual.local && d.projection == actual.projection)
            })
    }) else {
        return " payload=no-equation".to_owned();
    };
    let Some(transfer) = equation.transfer.as_ref() else {
        return " payload=no-transfer".to_owned();
    };
    let Ok(origins) = super::value_origins::ValueOrigins::build_metadata(facts, aliases) else {
        return " payload=no-origins".to_owned();
    };
    let node = Node {
        construction: call.construction,
        var: transfer.source_use,
    };
    // `endpoint_routes` asks `fresh` twice — the payload and the container.
    let container = match (&actual.base, &actual.pointer_paths) {
        (Present(base), Present(_)) => Some(Node {
            construction: call.construction,
            var: base.use_start,
        }),
        _ => None,
    };
    let arguments: Vec<_> = facts
        .boundary_substitutions
        .iter()
        .filter(|row| {
            row.role == Role::CallArgument
                && row.point.construction == call.construction
                && row.point.function.as_deref() == Some(call.caller.as_str())
                && row.point.block == Some(call.block)
                && row.point.statement == Some(call.statement)
                && row.callee.as_deref() == Some(call.callee.as_str())
        })
        .map(|row| {
            (
                row.licensing_role.clone(),
                matches!(row.actual_occurrence, Present(_)),
                row.matched
                    .iter()
                    .map(|m| m.formal.clone())
                    .collect::<Vec<_>>(),
                row.formal.clone(),
                row.unmatched_formal_vars.clone(),
            )
        })
        .collect();
    // The callee's own entry ports. `ValueOrigins` seeds `Input` on these and
    // resolves it through `call.inputs`, which is keyed on the CallArgument
    // row's formal USE var. If the two disagree the atom degrades to `Unknown`.
    let entries: Vec<_> = facts
        .boundary_substitutions
        .iter()
        .filter(|row| {
            row.role == Role::Entry
                && row.point.construction == call.construction
                && row.point.function.as_deref() == Some(call.callee.as_str())
        })
        .flat_map(|row| row.matched.iter().map(|m| m.formal.clone()))
        .collect();
    let admitted: Vec<_> = origins
        .at(node)
        .iter()
        .map(|atom| {
            (
                format!("{atom:?}"),
                fold_caller::returned_token(facts, call, atom),
            )
        })
        .collect();
    let container_atoms: Vec<_> = container
        .map(|node| {
            origins
                .at(node)
                .iter()
                .map(|atom| {
                    (
                        format!("{atom:?}"),
                        fold_caller::returned_token(facts, call, atom),
                    )
                })
                .collect()
        })
        .unwrap_or_default();
    format!(
        " payload-node={} payload-atoms={admitted:?} container-node={container:?} \
container-atoms={container_atoms:?} call-arguments={arguments:?} \
callee-entry-ports={entries:?}",
        node.var
    )
}

/// R365-3 and its K-witnesses. The caller certificate admits an `Input` in the
/// payload origin only when THIS call recorded a transfer of that argument into
/// the callee: one token in, the same token out. Every other shape is a second
/// owner or a different token, and each clause of the premise has its own case.
#[test]
fn r365_the_owner_return_admits_only_the_argument_this_call_consumed() {
    use super::{
        super::{
            ownership_boundary::{LicensingRole, Matched, Role, Substitution, Variables, Window},
            ownership_evidence::Point,
            ownership_occurrence::Availability,
        },
        matched::CallKey,
        transport::Node,
        value_origins::OriginAtom,
    };

    let call = CallKey {
        construction: 0,
        caller: "caller".to_owned(),
        block: 4,
        statement: 7,
        callee: "callee".to_owned(),
    };
    let port = Node {
        construction: 0,
        var: 11,
    };
    let unresolved = OriginAtom::UnresolvedInput {
        formal: port,
        actual: Node {
            construction: 0,
            var: 90,
        },
    };
    let row = |licensing_role, actual_occurrence, formal_window| Substitution {
        point: Point {
            construction: 0,
            function: Some(call.caller.clone()),
            phase: "licensing".to_owned(),
            block: Some(call.block),
            statement: Some(call.statement),
        },
        ordinal: 0,
        role: Role::CallArgument,
        licensing_role,
        callee: Some(call.callee.clone()),
        argument_index: Some(0),
        formal_local: Some(1),
        actual: Availability::Missing("not read here".to_owned()),
        formal: formal_window,
        actual_occurrence,
        call_arg_registration: Availability::Missing("not read here".to_owned()),
        reference_peel: None,
        // The root pair the boundary matched. The deeper components of the same
        // argument stay unmatched, which is the shape this rule is about.
        matched: vec![Matched {
            actual: Variables::Single { var: 90 },
            formal: Variables::UseDef {
                use_var: 10,
                def_var: 20,
            },
        }],
        unmatched_formal_vars: vec![11, 12, 21, 22],
        unmatched_actual_vars: Vec::new(),
    };
    let facts = |substitution| Facts {
        boundary_substitutions: vec![substitution],
        ..Facts::default()
    };
    // The argument's formal entry window: use ports 10..13, def ports 20..23.
    // `port` is 11 — a component the substitution left unmatched.
    let consumed = || {
        Availability::Present(Window::UseDef {
            use_start: 10,
            use_end: 13,
            def_start: 20,
            def_end: 23,
        })
    };

    let transferred = facts(row(
        LicensingRole::Legacy,
        Availability::Present(3),
        consumed(),
    ));
    assert!(
        fold_caller::returned_token(&transferred, &call, &OriginAtom::Input(port)),
        "the caller's token moved into this call and the return carries it back"
    );
    // R367-2: the unmatched component of that same argument, kept typed instead
    // of collapsed to `Unknown`, is the same token.
    assert!(
        fold_caller::returned_token(&transferred, &call, &unresolved),
        "an unmatched component of the consumed argument is still its token"
    );

    // K-R365-a: a lend. The caller kept its token; admitting the return would
    // let it hold the same token twice.
    for lending in [LicensingRole::Borrowed, LicensingRole::TraversalBorrow] {
        let lent = facts(row(lending, Availability::Present(3), consumed()));
        assert!(
            !fold_caller::returned_token(&lent, &call, &OriginAtom::Input(port)),
            "a lent argument coming back is not the owner-return shape"
        );
        assert!(
            !fold_caller::returned_token(&lent, &call, &unresolved),
            "nor is an unresolved component of a lent argument"
        );
    }

    // The same row without an identified caller place is not evidence that the
    // caller's own token is what moved.
    let unplaced = facts(row(
        LicensingRole::Legacy,
        Availability::Missing("no caller occurrence".to_owned()),
        consumed(),
    ));
    assert!(
        !fold_caller::returned_token(&unplaced, &call, &OriginAtom::Input(port)),
        "an unidentified actual does not witness the caller's token"
    );

    // K-R365-b: an `Input` port this call did not consume is a different token.
    let other = facts(row(
        LicensingRole::Legacy,
        Availability::Present(3),
        Availability::Present(Window::UseDef {
            use_start: 40,
            use_end: 43,
            def_start: 50,
            def_end: 53,
        }),
    ));
    assert!(
        !fold_caller::returned_token(&other, &call, &OriginAtom::Input(port)),
        "a port this call did not consume is another token"
    );
    // R367-2: the same K case for the unresolved atom. A component of another
    // argument is another token, however it reached the origin set.
    assert!(
        !fold_caller::returned_token(&other, &call, &unresolved),
        "an unresolved port outside this argument's window is another token"
    );
    // And a formal window the boundary could not represent names no ports.
    let unrepresented = facts(row(
        LicensingRole::Legacy,
        Availability::Present(3),
        Availability::Missing("formal ownership window not represented".to_owned()),
    ));
    assert!(
        !fold_caller::returned_token(&unrepresented, &call, &unresolved),
        "an unrepresented formal window names no consumed port"
    );

    // A transfer into a DIFFERENT call at another site says nothing about this
    // one.
    let elsewhere = {
        let mut substitution = row(LicensingRole::Legacy, Availability::Present(3), consumed());
        substitution.point.block = Some(call.block + 1);
        facts(substitution)
    };
    assert!(
        !fold_caller::returned_token(&elsewhere, &call, &OriginAtom::Input(port)),
        "the premise is THIS call's transfer, not any transfer of the same argument"
    );

    // Nothing but an `Input` is this shape at all.
    for atom in [
        OriginAtom::Null,
        OriginAtom::Borrow(port),
        OriginAtom::Unknown(port),
    ] {
        assert!(
            !fold_caller::returned_token(&transferred, &call, &atom),
            "only an input port is a token that came in: {atom:?}"
        );
    }
}

/// R372-3: the whole declaration plan re-derived over a recorded entry, under
/// whatever environment arm is pinned. The certificate runs without Z3 —
/// `fold_custody::validate` already re-derives it that way in production — so a
/// probe that only changes which declarations the certificate admits costs no
/// solve and no corpus slot.
#[test]
#[ignore = "reads a recorded cache entry named by the environment"]
fn r372_declaration_plan_of_a_recorded_entry() {
    use super::{super::origin_evidence::OriginEvidence, fold_eligibility};

    // R325-1: the first line of a `--nocapture` run shares the test-name line.
    eprintln!();
    let path = std::env::var("CRAT_ERA5B_ENTRY").expect("CRAT_ERA5B_ENTRY names a cache entry");
    let entry: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&path).expect("readable cache entry"))
            .expect("entry json");
    let program = entry["inputs"]["program"]
        .as_str()
        .unwrap_or("?")
        .to_owned();
    let origin: OriginEvidence =
        serde_json::from_value(entry["origin"].clone()).expect("recorded origin evidence");
    let snapshots = origin.licensing.as_deref().unwrap_or_default();
    let relaxed = super::facts::relax_frame();
    eprintln!(
        "PLAN {program} snapshots={} relax_frame={relaxed}",
        snapshots.len()
    );

    let Some(snapshot) = snapshots.first() else { return };
    let facts = snapshot.metadata.facts();
    let aliases: BTreeMap<_, _> = snapshot.metadata.guard_aliases.iter().copied().collect();
    let slots: BTreeSet<_> = snapshot.metadata.slot_keys.iter().cloned().collect();
    let line = |call: &super::matched::CallKey| {
        format!(
            "{} -> {} @ {}:{}",
            call.caller.rsplit("::").next().unwrap_or(&call.caller),
            call.callee.rsplit("::").next().unwrap_or(&call.callee),
            call.block,
            call.statement
        )
    };
    for decision in fold_eligibility::plan_metadata(&facts, &aliases, &slots)
        .unwrap_or_default()
        .iter()
    {
        eprintln!(
            "PLAN {program} caller {} {}",
            line(&decision.declaration.call),
            match &decision.outcome {
                Ok(_) => "CERTIFIED".to_owned(),
                Err(hold) => format!("{hold:?}"),
            }
        );
    }
    for decision in fold_eligibility::member_plan_metadata(&facts, &aliases, &slots)
        .unwrap_or_default()
        .iter()
    {
        eprintln!(
            "PLAN {program} member {} {}",
            line(&decision.declaration.call),
            match &decision.outcome {
                Ok(_) => "CERTIFIED".to_owned(),
                Err(hold) => format!("{hold:?}"),
            }
        );
    }
}

/// R377-1: the return-port rule. W1 admits; every killer refuses, each for its
/// own reason. The three STOP-1 killers (K8–K10) and K3 all refuse through the
/// same coarse clause — a frame with any in-frame free is refused — which is
/// sound and is why K3 is listed as refused here although R377-1 §2 ruled its
/// shape admissible: see report 047's STOP.
#[test]
fn r377_the_return_port_rule_admits_only_a_token_that_escapes_by_the_return() {
    const PRELUDE: &str = r#"
unsafe extern "C"{fn malloc(n:usize)->*mut core::ffi::c_void;fn free(p:*mut core::ffi::c_void);}
pub struct Node{child:*mut Node}
pub static mut ROOT:*mut Node=0 as *mut Node;
pub unsafe fn keep(p:*mut Node){ROOT=p;}
"#;
    let admitted = |body: &str, function: &'static str| {
        let code = format!("{PRELUDE}{body}");
        let (send, recv) = std::sync::mpsc::channel();
        super::graph_tests::with_facts(&code, move |facts| {
            let origins = super::value_origins::ValueOrigins::build(facts);
            let (keys, _holds) = fold_caller::return_port_owning(facts, &origins);
            // The rule's own readout, for a fixture that refuses unexpectedly.
            if std::env::var("CRAT_R377_DEBUG").is_ok() {
                eprintln!("R377DBG fn={function} admitted={keys:?}");
                for row in &facts.boundary_substitutions {
                    if format!("{:?}", row.role) == "ExitReturn"
                        && row.point.function.as_deref() == Some(function)
                    {
                        for pair in &row.matched {
                            if let super::super::ownership_boundary::Variables::Single { var } =
                                pair.formal
                            {
                                let n = super::transport::Node {
                                    construction: row.point.construction,
                                    var,
                                };
                                eprintln!("R377DBG port {var} atoms {:?}", origins.at(n));
                            }
                        }
                    }
                }
            }
            send.send(keys.iter().any(|key| key.contains(function)))
                .expect("one verdict");
        });
        recv.recv().expect("the rule ran")
    };

    // K11 (R378-2): a producer whose ownership some OTHER rule refuses. The
    // premise is about escape and cannot see the refusal — `buffer_new`'s token
    // does escape only by the return, so the rule ADMITS it. What protects the
    // model is the yield at emission: `require_own` tries the row in a scope and
    // drops it when the system is unsatisfiable with it, which here is the
    // CALLER's unchanged live-local final-zero on `read_length::buffer`. The
    // sentinels for that are `o03` and `o07` staying green with the pin on.
    assert!(
        admitted(
            r#"pub struct Buffer{data:*mut Node,len:usize}
pub unsafe fn buffer_new()->*mut Buffer{let b=malloc(core::mem::size_of::<Buffer>()) as *mut Buffer;(*b).data=0 as *mut Node;(*b).len=1;b}
pub unsafe fn read_length()->usize{let b=buffer_new();(*b).len}"#,
            "buffer_new"
        ),
        "K11: the premise admits a refused owner — the yield at emission is what protects it"
    );

    // W1: one source, one return, nothing else.
    assert!(
        admitted(
            "pub unsafe fn make()->*mut Node{let p=malloc(core::mem::size_of::<Node>()) as *mut Node;(*p).child=0 as *mut Node;p}",
            "make"
        ),
        "W1: a fresh allocation whose only escape is the return"
    );

    // K6, admitted: two different fresh allocations on two paths. The rule is
    // about freshness, not about a unique allocation identity — the fold
    // certificate's `one(Fresh)` is custody routing, a different obligation.
    assert!(
        admitted(
            "pub unsafe fn two(c:bool)->*mut Node{if c{let a=malloc(core::mem::size_of::<Node>()) as *mut Node;(*a).child=0 as *mut Node;a}else{let b=malloc(core::mem::size_of::<Node>()) as *mut Node;(*b).child=0 as *mut Node;b}}",
            "two"
        ),
        "K6: two fresh allocations on two paths are each the frame's own token"
    );

    for (label, body, function) in [
        // K1: stored into a global before returning.
        (
            "K1 global escape",
            "pub unsafe fn make()->*mut Node{let p=malloc(core::mem::size_of::<Node>()) as *mut Node;ROOT=p;p}",
            "make",
        ),
        // K2: stored into a field of a handed-in object.
        (
            "K2 field escape",
            "pub unsafe fn make(h:*mut Node)->*mut Node{let p=malloc(core::mem::size_of::<Node>()) as *mut Node;(*h).child=p;p}",
            "make",
        ),
        // K3: frees on an error path (R377-1 ruled the shape admissible; the
        // built rule refuses it — report 047's STOP).
        (
            "K3 error-path free",
            "pub unsafe fn make(c:bool)->*mut Node{let p=malloc(core::mem::size_of::<Node>()) as *mut Node;if c{free(p as *mut core::ffi::c_void);return 0 as *mut Node;}p}",
            "make",
        ),
        // K4: returns an input, not a fresh allocation.
        (
            "K4 returns an input",
            "pub unsafe fn make(q:*mut Node)->*mut Node{q}",
            "make",
        ),
        // K5: two returns of different KINDS of origin.
        (
            "K5 mixed origins",
            "pub unsafe fn make(c:bool)->*mut Node{if c{malloc(core::mem::size_of::<Node>()) as *mut Node}else{ROOT}}",
            "make",
        ),
        // K7: handed to a callee that stores it.
        (
            "K7 call-argument escape",
            "pub unsafe fn make()->*mut Node{let p=malloc(core::mem::size_of::<Node>()) as *mut Node;keep(p);p}",
            "make",
        ),
        // K8: frees and then returns the same pointer.
        (
            "K8 free then return it",
            "pub unsafe fn make()->*mut Node{let p=malloc(core::mem::size_of::<Node>()) as *mut Node;free(p as *mut core::ffi::c_void);p}",
            "make",
        ),
        // K9: frees and returns a non-fresh non-null value.
        (
            "K9 free then return a global",
            "pub unsafe fn make()->*mut Node{let p=malloc(core::mem::size_of::<Node>()) as *mut Node;free(p as *mut core::ffi::c_void);ROOT}",
            "make",
        ),
        // K10: a free on the very path that returns the token.
        (
            "K10 free on the returning path",
            "pub unsafe fn make(c:bool)->*mut Node{let p=malloc(core::mem::size_of::<Node>()) as *mut Node;if c{free(p as *mut core::ffi::c_void);return p;}p}",
            "make",
        ),
    ] {
        assert!(!admitted(body, function), "{label} must refuse");
    }
}

/// R382-1: the return-port rule read over a recorded entry — what it admits,
/// what it holds and why. No solve: the premise is a function of recorded
/// evidence, so a probe that asks "which producers did the rule reach" costs
/// nothing. What it cannot show is the YIELD, which happens at materialisation;
/// a producer that is admitted here and still `raw` in the entry was dropped by
/// a refusal, and the entry's model is the evidence of that.
#[test]
#[ignore = "reads a recorded cache entry named by the environment"]
fn r382_return_port_reading_of_a_recorded_entry() {
    use super::super::origin_evidence::OriginEvidence;

    eprintln!();
    let path = std::env::var("CRAT_ERA5B_ENTRY").expect("CRAT_ERA5B_ENTRY names a cache entry");
    let entry: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&path).expect("readable cache entry"))
            .expect("entry json");
    let program = entry["inputs"]["program"]
        .as_str()
        .unwrap_or("?")
        .to_owned();
    let model: BTreeMap<String, String> =
        serde_json::from_value(entry["model"].clone()).expect("model");
    let origin: OriginEvidence =
        serde_json::from_value(entry["origin"].clone()).expect("recorded origin evidence");
    let Some(snapshot) = origin.licensing.as_deref().unwrap_or_default().first() else {
        eprintln!("PORT {program} no licensing snapshot");
        return;
    };
    let facts = snapshot.metadata.facts();
    let aliases: BTreeMap<_, _> = snapshot.metadata.guard_aliases.iter().copied().collect();
    let origins = super::value_origins::ValueOrigins::build_metadata(&facts, &aliases)
        .expect("recorded aliases rebuild the origins");
    let (admitted, holds) = fold_caller::return_port_owning(&facts, &origins);
    eprintln!(
        "PORT {program} admitted={} held={}",
        admitted.len(),
        holds.len()
    );
    for key in &admitted {
        eprintln!(
            "PORT {program} ADMITTED {key} model={}",
            model.get(key).map(String::as_str).unwrap_or("?")
        );
    }
    for (key, reason) in &holds {
        eprintln!(
            "PORT {program} HELD {key} {reason:?} model={}",
            model.get(key).map(String::as_str).unwrap_or("?")
        );
    }
}
