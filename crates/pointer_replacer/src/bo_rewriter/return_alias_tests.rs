//! RB-RETALIAS READ controls over real MIR, without decisions or rewriting.

use rustc_middle::{
    mir::{
        Location, Operand, RETURN_PLACE, Rvalue, StatementKind, TerminatorKind,
        VarDebugInfoContents,
    },
    ty::TyKind,
};

use super::decision::return_alias::{self, ReturnUseObservation, ReturnUseState};

#[derive(Debug)]
struct ReadWitness {
    observation: ReturnUseObservation,
    projected_destination: bool,
    return_destination: bool,
    ordinary_destination_reassignments: usize,
    result_projected_stores: usize,
    normal_flow_reenters_call: bool,
    destination_debug_names: Vec<String>,
    destination_storage_markers: usize,
    destination_fake_reads: usize,
}

fn observe_strchr(body_source: &str) -> ReadWitness {
    let input = format!(
        "#![allow(dead_code, unused_variables, unused_assignments, unused_mut, unused_unsafe)]\n\
         extern \"C\" {{ fn strchr(s: *const i8, c: i32) -> *mut i8; }}\n\
         static mut SAVED: *mut i8 = 0 as *mut i8;\n{body_source}"
    );
    ::utils::compilation::run_compiler_on_str(&input, |tcx| {
        let owner = tcx.hir_body_owners()
            .find(|owner| tcx.def_path_str(owner.to_def_id()) == "target")
            .expect("real target body");
        let body = tcx.mir_drops_elaborated_and_const_checked(owner).borrow();
        let calls = body.basic_blocks.iter_enumerated().filter_map(|(block, data)| {
            let TerminatorKind::Call { func, destination, target, .. } = &data.terminator().kind else {
                return None;
            };
            let constant = func.constant()?;
            let TyKind::FnDef(callee, _) = *constant.ty().kind() else { return None };
            if tcx.item_name(callee).as_str() != "strchr" {
                return None;
            }
            assert!(matches!(tcx.hir_node_by_def_id(callee.expect_local()), rustc_hir::Node::ForeignItem(_)),
                "the call must resolve to the actual extern DefId, not a same-spelled local function");
            Some((Location { block, statement_index: data.statements.len() }, *destination, *target))
        }).collect::<Vec<_>>();
        assert_eq!(calls.len(), 1, "one resolved strchr call per real-MIR witness: {body:?}");
        let (call, destination, target) = calls[0];
        let mut reassignments = 0;
        let mut storage_markers = 0;
        let mut fake_reads = 0;
        let mut projected_stores = 0;
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                match &statement.kind {
                    StatementKind::Assign(assignment)
                        if assignment.0.as_local() == Some(destination.local) => reassignments += 1,
                    StatementKind::StorageLive(local) | StatementKind::StorageDead(local)
                        if *local == destination.local => storage_markers += 1,
                    StatementKind::FakeRead(read) if read.1.local == destination.local => fake_reads += 1,
                    _ => {}
                }
                if let StatementKind::Assign(assignment) = &statement.kind
                    && !assignment.0.projection.is_empty()
                    && let Rvalue::Use(operand) = &assignment.1
                    && matches!(operand, Operand::Copy(place) | Operand::Move(place)
                        if place.as_local() == Some(destination.local))
                {
                    projected_stores += 1;
                }
            }
        }
        let mut reachable = std::collections::BTreeSet::new();
        let mut frontier = target.into_iter().collect::<Vec<_>>();
        while let Some(block) = frontier.pop() {
            if reachable.insert(block) {
                frontier.extend(body.basic_blocks[block].terminator().successors());
            }
        }
        let destination_debug_names = body.var_debug_info.iter().filter_map(|info| {
            let VarDebugInfoContents::Place(place) = &info.value else { return None };
            (place.as_local() == Some(destination.local)).then(|| info.name.to_string())
        }).collect::<Vec<_>>();
        let observation = return_alias::observe(&body, call);
        assert_eq!(observation.call, call);
        assert_eq!(observation.destination.as_ref().map(|place| place.local), Some(destination.local));
        ReadWitness {
            observation,
            projected_destination: !destination.projection.is_empty(),
            return_destination: destination.local == RETURN_PLACE,
            ordinary_destination_reassignments: reassignments,
            result_projected_stores: projected_stores,
            normal_flow_reenters_call: reachable.contains(&call.block),
            destination_debug_names,
            destination_storage_markers: storage_markers,
            destination_fake_reads: fake_reads,
        }
    }).expect("real-MIR return-use fixture type-checks")
}

#[test]
fn retalias_read_discarded_and_named_unused_results_are_unused() {
    for (label, source) in [
        (
            "discarded",
            "pub unsafe fn target(p: *const i8, c: i32) { strchr(p, c); }",
        ),
        (
            "named-unused",
            "pub unsafe fn target(p: *const i8, c: i32) { let named_unused = strchr(p, c); }",
        ),
    ] {
        let witness = observe_strchr(source);
        if label == "named-unused" {
            assert!(
                witness
                    .destination_debug_names
                    .iter()
                    .any(|name| name == "named_unused"),
                "invalid named-unused premise: the call destination lacks the actual debug binding: {witness:?}"
            );
        }
        assert_eq!(
            witness.observation.state,
            ReturnUseState::Unused,
            "{label}: {witness:?}"
        );
        assert!(
            witness.observation.uses.is_empty(),
            "bookkeeping cannot consume a return: {witness:?}"
        );
        assert!(witness.observation.unknowns.is_empty(), "{witness:?}");
        assert_eq!(witness.observation.definitions.len(), 1, "{witness:?}");
        assert_eq!(
            witness.observation.definitions[0].location,
            witness.observation.call
        );
        eprintln!(
            "RB-RETALIAS {label}: ignored debug={:?}, storage={}, fake-read={}",
            witness.destination_debug_names,
            witness.destination_storage_markers,
            witness.destination_fake_reads
        );
    }
}

#[test]
fn retalias_read_read_copy_return_global_and_projected_results_are_used() {
    for (label, source) in [
        (
            "read",
            "pub unsafe fn target(p: *const i8, c: i32) -> i8 { let child = strchr(p, c); *child }",
        ),
        (
            "copy",
            "pub unsafe fn target(p: *const i8, c: i32) -> bool { let child = strchr(p, c); let copied = child; copied.is_null() }",
        ),
        (
            "returned",
            "pub unsafe fn target(p: *const i8, c: i32) -> *mut i8 { strchr(p, c) }",
        ),
        (
            "global",
            "pub unsafe fn target(p: *const i8, c: i32) { SAVED = strchr(p, c); }",
        ),
        (
            "projected",
            "pub unsafe fn target(p: *const i8, c: i32, out: *mut *mut i8) { *out = strchr(p, c); }",
        ),
    ] {
        let witness = observe_strchr(source);
        if label == "returned" {
            assert!(
                witness.return_destination,
                "invalid returned-call destination premise: {witness:?}"
            );
        }
        if label == "projected" {
            assert!(
                witness.projected_destination || witness.result_projected_stores > 0,
                "real MIR must either call into the projected destination or store its result there: {witness:?}"
            );
            if witness.projected_destination {
                assert!(
                    witness
                        .observation
                        .uses
                        .iter()
                        .any(|site| site.reason == "projected-output-destination"),
                    "{witness:?}"
                );
            }
        }
        assert_eq!(
            witness.observation.state,
            ReturnUseState::Used,
            "{label}: {witness:?}"
        );
        assert!(!witness.observation.uses.is_empty(), "{label}: {witness:?}");
        assert!(
            witness.observation.unknowns.is_empty(),
            "{label}: {witness:?}"
        );
    }
}

#[test]
fn retalias_read_pointee_store_records_write_through_result() {
    let witness = observe_strchr(
        "pub unsafe fn target(p: *const i8, c: i32) { let child = strchr(p, c); *child = 7; }",
    );
    assert_eq!(
        witness.observation.state,
        ReturnUseState::Used,
        "{witness:?}"
    );
    assert!(
        witness
            .observation
            .uses
            .iter()
            .any(|site| site.reason == "write-through-result"),
        "a descendant pointee store must retain its write evidence: {witness:?}"
    );
}

#[test]
fn retalias_read_actual_destination_reassignment_is_unknown() {
    let witness = observe_strchr(
        "pub unsafe fn target(p: *const i8, c: i32) -> bool { let mut child = strchr(p, c); child = 0 as *mut i8; child.is_null() }",
    );
    assert!(
        witness.ordinary_destination_reassignments > 0,
        "invalid reassignment premise: real MIR did not reassign the observed call destination: {witness:?}"
    );
    assert_eq!(
        witness.observation.state,
        ReturnUseState::Unknown,
        "{witness:?}"
    );
    assert!(
        witness
            .observation
            .unknowns
            .iter()
            .any(|site| site.reason == "multiple-or-unresolved-destination-definitions"),
        "{witness:?}"
    );
}

#[test]
fn retalias_read_actual_normal_flow_call_cycle_is_unknown() {
    let witness = observe_strchr(
        "pub unsafe fn target(p: *const i8, c: i32, repeat: bool) { loop { strchr(p, c); if !repeat { break; } } }",
    );
    assert!(
        witness.normal_flow_reenters_call,
        "invalid call-cycle premise: real normal successors do not return to the call block: {witness:?}"
    );
    assert_eq!(
        witness.observation.state,
        ReturnUseState::Unknown,
        "{witness:?}"
    );
    assert!(
        witness
            .observation
            .unknowns
            .iter()
            .any(|site| site.reason == "normal-flow-reenters-call"),
        "{witness:?}"
    );
}

#[derive(Clone, Debug, serde::Deserialize, serde::Serialize)]
struct ReadSourcePin {
    path: std::path::PathBuf,
    sha256: String,
}

#[derive(Clone, Debug, serde::Deserialize, serde::Serialize)]
struct ReadProgramInput {
    program: String,
    root: std::path::PathBuf,
    sources: Vec<ReadSourcePin>,
}

fn verify_read_sources(
    input: &ReadProgramInput,
) -> std::collections::BTreeMap<std::path::PathBuf, String> {
    use sha2::{Digest, Sha256};

    assert!(
        !input.program.is_empty() && !input.sources.is_empty(),
        "empty READ program/source manifest"
    );
    assert!(
        input.root.is_absolute(),
        "READ root must be absolute: {}",
        input.root.display()
    );
    let mut verified = std::collections::BTreeMap::new();
    for source in &input.sources {
        assert!(
            source.path.is_absolute(),
            "READ source must be absolute: {}",
            source.path.display()
        );
        let path = source.path.canonicalize().expect("READ source path exists");
        let bytes = std::fs::read(&path).expect("READ source bytes");
        let actual = format!("{:x}", Sha256::digest(&bytes));
        assert_eq!(
            actual,
            source.sha256,
            "READ input SHA: {}",
            source.path.display()
        );
        assert!(
            verified.insert(path, actual).is_none(),
            "duplicate READ source path"
        );
    }
    assert!(
        verified.contains_key(&input.root.canonicalize().expect("READ root exists")),
        "READ root must be explicitly hash-pinned: {}",
        input.root.display()
    );
    verified
}

fn read_location(location: Location) -> serde_json::Value {
    serde_json::json!({"block": location.block.as_u32(), "statement_index": location.statement_index})
}

fn read_use_sites(sites: &[return_alias::ReturnUseSite]) -> Vec<serde_json::Value> {
    sites
        .iter()
        .map(|site| {
            serde_json::json!({
                "location": read_location(site.location), "reason": site.reason,
            })
        })
        .collect()
}

fn read_source_span(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    span: rustc_span::Span,
) -> serde_json::Value {
    let span = span.source_callsite();
    if span.is_dummy() {
        return serde_json::json!({"unavailable": "dummy-source-span"});
    }
    let source = tcx.sess.source_map().lookup_source_file(span.lo());
    let path = match &source.name {
        rustc_span::FileName::Real(real) => real
            .local_path()
            .map(|path| path.to_string_lossy().into_owned()),
        _ => None,
    };
    serde_json::json!({
        "path": path,
        "diagnostic_site": tcx.sess.source_map().span_to_diagnostic_string(span),
        "source_lo": span.lo().0,
        "source_hi": span.hi().0,
        "file_relative_lo": span.lo().0.checked_sub(source.start_pos.0),
        "file_relative_hi": span.hi().0.checked_sub(source.start_pos.0),
    })
}

fn read_program_returns(
    input: &ReadProgramInput,
    pinned_sources: &std::collections::BTreeMap<std::path::PathBuf, String>,
) -> serde_json::Value {
    use super::decision::{raw_boundary, raw_boundary_contracts};

    ::utils::compilation::run_compiler_on_path(&input.root, |tcx| {
        let mut owners = tcx.hir_body_owners().collect::<Vec<_>>();
        owners.sort_by_key(|owner| owner.local_def_index.as_u32());
        let mut calls = Vec::new();
        let mut seen = std::collections::BTreeSet::new();
        let mut symbols = std::collections::BTreeSet::new();
        for &owner in &owners {
            let body = tcx.mir_drops_elaborated_and_const_checked(owner).borrow();
            for (block, data) in body.basic_blocks.iter_enumerated() {
                let (func, arguments) = match &data.terminator().kind {
                    TerminatorKind::Call { func, args, .. } | TerminatorKind::TailCall { func, args, .. } => (func, args),
                    _ => continue,
                };
                let Some(constant) = func.constant() else { continue };
                let TyKind::FnDef(callee, _) = *constant.ty().kind() else { continue };
                let callee_key = raw_boundary::symbol_key(tcx, callee, &owners);
                if !callee_key.foreign {
                    continue;
                }
                let signature = tcx.fn_sig(callee).skip_binder().skip_binder();
                let mut pointer_arguments = Vec::new();
                let mut alias_positions = std::collections::BTreeSet::new();
                for (argument_index, argument) in arguments.iter().enumerate() {
                    let source_type = argument.node.ty(&*body, tcx);
                    let target = signature.inputs().get(argument_index).copied()
                        .and_then(|ty| raw_boundary::raw_target_type(tcx, ty))
                        .or_else(|| signature.c_variadic.then(|| raw_boundary::raw_target_type(tcx, source_type)).flatten());
                    let Some(target) = target else { continue };
                    let contract = raw_boundary_contracts::classify_contract(&callee_key, argument_index, &target);
                    let contract_value = match contract {
                        Ok(contract) => {
                            if let Some(position) = contract.returns_alias_of {
                                alias_positions.insert(position);
                            }
                            serde_json::json!({
                                "status": "classified", "returns_alias_of": contract.returns_alias_of,
                                "is_return_parent": contract.returns_alias_of == Some(argument_index),
                                "retention": format!("{:?}", contract.retention),
                                "access": contract.access.key(), "ownership": format!("{:?}", contract.ownership),
                                "provenance": contract.provenance,
                            })
                        }
                        Err(reason) => serde_json::json!({"status": "unmodeled", "reason": format!("{reason:?}")}),
                    };
                    pointer_arguments.push(serde_json::json!({
                        "argument_index": argument_index, "source_type": source_type.to_string(),
                        "target_type": target.rendered, "target_pointee": target.pointee,
                        "target_mutability": format!("{:?}", target.mutability),
                        "source_span": read_source_span(tcx, argument.span), "contract": contract_value,
                    }));
                }
                if alias_positions.is_empty() {
                    continue;
                }
                assert_eq!(alias_positions.len(), 1, "conflicting returned-parent contract positions: {callee_key:?}");
                assert!(matches!(callee_key.symbol.as_str(), "fgets" | "strcat" | "strchr" | "strcpy" | "strncat" | "strncpy" | "strstr"),
                    "READ scope expanded beyond the seven existing return-alias contracts: {callee_key:?}");
                let parent_argument = *alias_positions.iter().next().unwrap();
                assert!(parent_argument < arguments.len(), "return-alias parent argument absent");
                let location = Location { block, statement_index: data.statements.len() };
                let caller = tcx.def_path_str(owner.to_def_id());
                let site_key = format!("{}:bb={}:stmt={}:callee={}", caller, block.as_u32(), location.statement_index, callee_key.path);
                assert!(seen.insert(site_key.clone()), "duplicate READ call site: {}:{site_key}", input.program);
                let observation = return_alias::observe(&body, location);
                symbols.insert(callee_key.symbol.clone());
                calls.push(serde_json::json!({
                    "site_key": site_key, "caller": caller, "caller_local_def_index": owner.local_def_index.as_u32(),
                    "callee_def_id": format!("{callee:?}"), "callee_path": callee_key.path,
                    "callee_symbol": callee_key.symbol, "callee_abi": callee_key.abi,
                    "callee_signature": callee_key.signature, "foreign": callee_key.foreign,
                    "location": read_location(location), "call_source_span": read_source_span(tcx, data.terminator().source_info.span),
                    "returns_alias_of": parent_argument, "pointer_arguments": pointer_arguments,
                    "destination": observation.destination.as_ref().map(|place| serde_json::json!({
                        "local": place.local.as_u32(), "projection": place.projection,
                    })),
                    "normal_target": observation.normal_target.map(|target| target.as_u32()),
                    "return_use_state": observation.state.key(), "uses": read_use_sites(&observation.uses),
                    "definitions": read_use_sites(&observation.definitions), "unknowns": read_use_sites(&observation.unknowns),
                }));
            }
        }
        tcx.dcx().abort_if_errors();
        let mut observed_sources = std::collections::BTreeSet::new();
        for source in tcx.sess.source_map().files().iter() {
            if source.src.is_none() {
                continue;
            }
            if let rustc_span::FileName::Real(real) = &source.name {
                let path = real.local_path().expect("READ local source path").canonicalize().expect("READ parsed source exists");
                assert!(pinned_sources.contains_key(&path), "compiler read an unpinned source: {}", path.display());
                observed_sources.insert(path);
            }
        }
        assert!(observed_sources.contains(&input.root.canonicalize().expect("READ root exists")), "compiler did not observe the pinned root");
        serde_json::json!({
            "program": input.program, "root": input.root, "sources": input.sources,
            "observed_sources": observed_sources, "body_owners_inspected": owners.len(),
            "call_count": calls.len(), "symbols": symbols, "calls": calls,
        })
    }).unwrap_or_else(|error| panic!("READ compiler failure for {}: {error:?}", input.program))
}

#[test]
fn retalias_manifest_read() {
    use std::io::Write;

    use sha2::{Digest, Sha256};

    // Same opt-in test-instrument pattern as F01: ordinary suites perform no
    // corpus work and keep the standing ignored-test identity set unchanged.
    let Some(input_path) = std::env::var_os("CRAT_RETALIAS_READ_INPUT") else { return };
    let input_path = std::path::PathBuf::from(input_path);
    let output_path = std::path::PathBuf::from(
        std::env::var_os("CRAT_RETALIAS_READ_OUTPUT").expect("CRAT_RETALIAS_READ_OUTPUT"),
    );
    assert!(
        input_path.is_absolute() && output_path.is_absolute(),
        "READ manifest/output paths must be absolute"
    );
    assert!(
        !output_path.exists(),
        "READ never overwrites a published output"
    );
    let mut pending_name = output_path.as_os_str().to_os_string();
    pending_name.push(".pending");
    let pending_path = std::path::PathBuf::from(pending_name);
    assert!(!pending_path.exists(), "READ pending output already exists");
    let manifest_bytes = std::fs::read(&input_path).expect("READ manifest bytes");
    let manifest_sha256 = format!("{:x}", Sha256::digest(&manifest_bytes));
    let programs: Vec<ReadProgramInput> =
        serde_json::from_slice(&manifest_bytes).expect("READ manifest schema");
    assert!(!programs.is_empty(), "empty READ program manifest");
    let mut names = std::collections::BTreeSet::new();
    let mut roots = std::collections::BTreeSet::new();
    let mut pins = Vec::new();
    for program in &programs {
        assert!(
            names.insert(program.program.clone()),
            "duplicate READ program identity"
        );
        assert!(
            roots.insert(program.root.canonicalize().expect("READ root exists")),
            "duplicate READ root"
        );
        pins.push(verify_read_sources(program));
    }
    let mut observations = Vec::new();
    for (program, pinned) in programs.iter().zip(&pins) {
        assert_eq!(
            &verify_read_sources(program),
            pinned,
            "READ pre-compiler source movement"
        );
        eprintln!("RB-RETALIAS MIR READ starting {}", program.program);
        let observed = read_program_returns(program, pinned);
        assert_eq!(
            &verify_read_sources(program),
            pinned,
            "READ post-compiler source movement"
        );
        eprintln!(
            "RB-RETALIAS MIR READ completed {} calls={}",
            program.program, observed["call_count"]
        );
        observations.push(observed);
    }
    for (program, pinned) in programs.iter().zip(&pins) {
        assert_eq!(
            &verify_read_sources(program),
            pinned,
            "READ final source movement"
        );
    }
    assert_eq!(
        std::fs::read(&input_path).expect("READ final manifest bytes"),
        manifest_bytes,
        "READ manifest movement"
    );
    let output = serde_json::json!({
        "schema": "rb-retalias-mir-read/v1", "manifest_path": input_path, "manifest_sha256": manifest_sha256,
        "mir_phase": "mir_drops_elaborated_and_const_checked", "programs": observations,
        "publication_protocol": "root promotes .pending only after successful process exit and log closure",
        "scope": "resolved foreign calls with one of the seven existing return-alias contracts; all pointer argument classifications retained",
        "rewriter_model_worker_solver_cache_invoked": false,
    });
    let bytes = serde_json::to_vec_pretty(&output).expect("owned READ observation serialization");
    let mut pending = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&pending_path)
        .expect("new pending READ output");
    pending
        .write_all(&bytes)
        .expect("pending READ output bytes");
    pending
        .sync_all()
        .expect("closed READ payload reaches storage");
    drop(pending);
    eprintln!(
        "RB-RETALIAS MIR READ pending output complete: {}; sha256={:x}",
        pending_path.display(),
        Sha256::digest(&bytes)
    );
}
