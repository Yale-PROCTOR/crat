//! A16 no-solve classifier: local-call return kind mismatches in launch-6 precise models.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
    time::{Duration, Instant},
};

use rustc_middle::{
    mir::{RETURN_PLACE, TerminatorKind},
    ty::TyKind,
};
use sha2::{Digest, Sha256};

use crate::{
    analyses::borrow_ownership::{
        SlotKind,
        coherence::positive_opaque_return_slots,
        crate_slots::{CrateSlots, ptr_chain_depth},
        l2::SlotKey,
        origin_summary::SignatureRoot,
        origins::compute_origins,
        resolve::{ResolvedSlot, resolve_place},
        slots::SlotId,
        solver::SlotRef,
        sources::collect_malloc_source_slots,
    },
    utils::rustc::RustProgram,
};

#[derive(Clone, Copy, Debug)]
struct OriginEvidence {
    class: &'static str,
    modeled: bool,
    unknown: bool,
    fresh: bool,
    opaque: bool,
    refined_eligible: bool,
}

fn origin_evidence(
    origins: &crate::analyses::borrow_ownership::origin_summary::OriginSummaries,
    callee: rustc_hir::def_id::LocalDefId,
    depth: u8,
    returned: SlotRef,
    fresh_slots: &rustc_hash::FxHashSet<SlotRef>,
    opaque_slots: &rustc_hash::FxHashSet<SlotRef>,
) -> OriginEvidence {
    let summary = &origins[&callee];
    let signature_return = summary.slots.iter_enumerated().find_map(|(id, slot)| {
        (slot.place.root == SignatureRoot::Return
            && slot.place.deref_depth == 0
            && slot.place.field.is_none()
            && slot.depth == depth)
            .then_some(id)
    });
    let unknown = signature_return.is_none_or(|id| summary.unknown.contains(id));
    let modeled = signature_return.is_some_and(|returned_id| {
        summary.subset.rows().any(|source| {
            source != returned_id
                && !summary.unknown.contains(source)
                && summary.subset.contains(source, returned_id)
                && !summary.subset.contains(returned_id, source)
                && matches!(summary.slots[source].place.root, SignatureRoot::Arg(_))
        })
    });
    let fresh = fresh_slots.contains(&returned);
    let opaque = opaque_slots.contains(&returned);
    let class = if opaque {
        "foreign-opaque"
    } else if fresh {
        "fresh-owning"
    } else if unknown {
        "unknown"
    } else if modeled {
        "modeled-borrow-origin"
    } else {
        "unknown"
    };
    OriginEvidence {
        class,
        modeled,
        unknown,
        fresh,
        opaque,
        refined_eligible: modeled && !unknown && !fresh && !opaque,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Cell {
    CallerNonRef,
    RefRef,
    RefNonRef,
}

fn classify(caller: SlotKind, callee: SlotKind) -> Cell {
    if caller != SlotKind::Ref {
        Cell::CallerNonRef
    } else if callee == SlotKind::Ref {
        Cell::RefRef
    } else {
        Cell::RefNonRef
    }
}

fn slot_ref(fn_did: rustc_hir::def_id::LocalDefId, slot: ResolvedSlot) -> SlotRef {
    match slot {
        ResolvedSlot::Local(slot) => SlotRef::Local(fn_did, slot),
        ResolvedSlot::Field(slot) => SlotRef::Field(slot),
    }
}

fn model_sha256(path: &Path) -> String {
    let bytes = fs::read(path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
    format!("{:x}", Sha256::digest(bytes))
}

fn boundary_key(caller: &str, block: &str, statement: &str, callee: &str, depth: &str) -> String {
    format!("{caller}\t{block}\t{statement}\t{callee}\t{depth}")
}

fn registered_upper_bound(path: &Path, program: &str) -> Result<BTreeSet<String>, String> {
    let input = fs::read_to_string(path)
        .map_err(|error| format!("read registered A16 ledger {}: {error}", path.display()))?;
    let mut keys = BTreeSet::new();
    for (line_no, line) in input.lines().enumerate() {
        if line_no == 0 {
            if !line.starts_with("program\tcaller\tblock\tstatement\tcallee\tdepth\t") {
                return Err("registered A16 ledger header mismatch".to_owned());
            }
            continue;
        }
        let fields = line.split('\t').collect::<Vec<_>>();
        if fields.len() != 15 {
            return Err(format!(
                "registered A16 ledger line {} has {} fields",
                line_no + 1,
                fields.len()
            ));
        }
        if fields[0] == program && fields[14] == "ref-nonref" {
            let key = boundary_key(fields[1], fields[2], fields[3], fields[4], fields[5]);
            if !keys.insert(key) {
                return Err(format!(
                    "duplicate registered boundary at line {}",
                    line_no + 1
                ));
            }
        }
    }
    Ok(keys)
}

fn parse_model(
    path: &Path,
    program: &RustProgram<'_>,
    slots: &CrateSlots,
) -> Result<rustc_hash::FxHashMap<SlotRef, SlotKind>, String> {
    let input = fs::read_to_string(path)
        .map_err(|error| format!("read landed model {}: {error}", path.display()))?;
    let functions = program
        .functions
        .iter()
        .map(|did| (did.local_def_index.as_u32(), *did))
        .collect::<BTreeMap<_, _>>();
    let mut model = rustc_hash::FxHashMap::default();
    for (line_no, line) in input.lines().enumerate() {
        if line_no == 0 {
            if line != "variant\towner\tslot\tkind" {
                return Err(format!("unexpected model header: {line}"));
            }
            continue;
        }
        let fields = line.split('\t').collect::<Vec<_>>();
        if fields.len() != 4 {
            return Err(format!(
                "model line {} has {} fields",
                line_no + 1,
                fields.len()
            ));
        }
        let slot_index = fields[2]
            .parse::<usize>()
            .map_err(|error| format!("model slot {}: {error}", fields[2]))?;
        let slot = match fields[0] {
            "0" => {
                if slot_index >= slots.field_slots.len() {
                    return Err(format!("field model slot {slot_index} is out of range"));
                }
                SlotRef::Field(SlotId::from_usize(slot_index))
            }
            "1" => {
                let owner = fields[1]
                    .parse::<u32>()
                    .map_err(|error| format!("model owner {}: {error}", fields[1]))?;
                let did = functions
                    .get(&owner)
                    .copied()
                    .ok_or_else(|| format!("model owner {owner} is not a local function"))?;
                if slot_index >= slots.fn_local_slots[&did].len() {
                    return Err(format!(
                        "local model slot {owner}:{slot_index} is out of range"
                    ));
                }
                SlotRef::Local(did, SlotId::from_usize(slot_index))
            }
            variant => return Err(format!("unknown model slot variant {variant}")),
        };
        let kind = match fields[3] {
            "Raw" => SlotKind::Raw,
            "Ref" => SlotKind::Ref,
            "Owning" => SlotKind::Owning,
            other => return Err(format!("unknown model kind {other}")),
        };
        if model.insert(slot, kind).is_some() {
            return Err(format!("duplicate model slot {:?}", SlotKey::of(slot)));
        }
    }
    let expected = slots.field_slots.len()
        + slots
            .fn_local_slots
            .values()
            .map(|universe| universe.len())
            .sum::<usize>();
    if model.len() != expected {
        return Err(format!(
            "model has {} slots; current universe has {expected}",
            model.len()
        ));
    }
    Ok(model)
}

pub(super) fn run_worker(tcx: rustc_middle::ty::TyCtxt<'_>, t_tcx: Duration) -> super::report::Row {
    let started = Instant::now();
    let name = std::env::var("CRAT_BOC1_NAME").expect("A16 program name");
    let model_path = std::path::PathBuf::from(
        std::env::var_os("CRAT_A16_MODEL").expect("A16 launch-6 precise model"),
    );
    let upper_bound_path = std::path::PathBuf::from(
        std::env::var_os("CRAT_A16_UPPER_BOUND_LEDGER").expect("A16 registered upper-bound ledger"),
    );
    let output =
        std::path::PathBuf::from(std::env::var_os("CRAT_A16_OUT").expect("A16 output directory"));
    let observer_head = std::env::var("CRAT_A16_OBSERVER").expect("A16 observer head");
    let program = super::collect_program(tcx);
    let slots = CrateSlots::build(&program);
    let origins = compute_origins(&program);
    let fresh_slots = collect_malloc_source_slots(tcx, &program.functions, &slots);
    let opaque_slots = positive_opaque_return_slots(&slots, &program, origins.native_flows());
    let model = parse_model(&model_path, &program, &slots)
        .unwrap_or_else(|error| panic!("A16 model join: {error}"));
    let upper_bound = registered_upper_bound(&upper_bound_path, &name)
        .unwrap_or_else(|error| panic!("A16 upper-bound join: {error}"));

    let mut universe = 0usize;
    let mut caller_non_ref = 0usize;
    let mut ref_ref = 0usize;
    let mut ref_non_ref = 0usize;
    let mut exposure_raw = 0usize;
    let mut exposure_owning = 0usize;
    let mut exposure_slots = BTreeSet::new();
    let mut origin_counts = BTreeMap::<&'static str, usize>::new();
    let mut exposure_origin_counts = BTreeMap::<&'static str, usize>::new();
    let mut refined_eligible = 0usize;
    let mut refined_eligible_exposure = 0usize;
    let mut matched_upper_bound = BTreeSet::new();
    let mut ledger = String::from(
        "program\tcaller\tblock\tstatement\tcallee\tdepth\tcaller_variant\tcaller_owner\tcaller_slot\tcallee_variant\tcallee_owner\tcallee_slot\tcaller_kind\tcallee_kind\tcell\tregistered_upper_bound\torigin_class\torigin_modeled\torigin_unknown\torigin_fresh\torigin_opaque\trefined_eligible\n",
    );

    for &caller in &program.functions {
        let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
        for (block, data) in body.basic_blocks.iter_enumerated() {
            let TerminatorKind::Call {
                func, destination, ..
            } = &data.terminator().kind
            else {
                continue;
            };
            let TyKind::FnDef(callee, _) = func.ty(&*body, tcx).kind() else {
                continue;
            };
            let Some(callee) = callee.as_local() else {
                continue;
            };
            if !matches!(tcx.hir_node_by_def_id(callee), rustc_hir::Node::Item(_)) {
                continue;
            }
            let depths = ptr_chain_depth(destination.ty(&*body, tcx).ty);
            for depth in 0..depths {
                universe += 1;
                let caller_slot = resolve_place(&slots, caller, &body, *destination, depth, None)
                    .map(|slot| slot_ref(caller, slot))
                    .unwrap_or_else(|| {
                        panic!(
                            "A16 unresolved caller slot: {name} {} bb{} depth{}",
                            tcx.def_path_str(caller.to_def_id()),
                            block.index(),
                            depth,
                        )
                    });
                let callee_slot_id = slots.fn_local_slots[&callee]
                    .slot_for_local_depth(RETURN_PLACE, depth)
                    .unwrap_or_else(|| {
                        panic!(
                            "A16 unresolved callee return: {name} {} depth{}",
                            tcx.def_path_str(callee.to_def_id()),
                            depth,
                        )
                    });
                let callee_slot = SlotRef::Local(callee, callee_slot_id);
                let caller_kind = *model
                    .get(&caller_slot)
                    .unwrap_or_else(|| panic!("A16 caller slot missing from model"));
                let callee_kind = *model
                    .get(&callee_slot)
                    .unwrap_or_else(|| panic!("A16 callee slot missing from model"));
                let evidence = origin_evidence(
                    &origins,
                    callee,
                    u8::try_from(depth).expect("A16 depth exceeds u8"),
                    callee_slot,
                    &fresh_slots,
                    &opaque_slots,
                );
                let caller_path = tcx.def_path_str(caller.to_def_id());
                let callee_path = tcx.def_path_str(callee.to_def_id());
                let block_index = block.index().to_string();
                let statement_index = data.statements.len().to_string();
                let depth_label = depth.to_string();
                let boundary = boundary_key(
                    &caller_path,
                    &block_index,
                    &statement_index,
                    &callee_path,
                    &depth_label,
                );
                let registered_upper_bound = upper_bound.contains(&boundary);
                if registered_upper_bound {
                    matched_upper_bound.insert(boundary);
                    *exposure_origin_counts.entry(evidence.class).or_default() += 1;
                    refined_eligible_exposure += usize::from(evidence.refined_eligible);
                }
                *origin_counts.entry(evidence.class).or_default() += 1;
                refined_eligible += usize::from(evidence.refined_eligible);
                let cell = classify(caller_kind, callee_kind);
                let cell_label = match cell {
                    Cell::CallerNonRef => {
                        caller_non_ref += 1;
                        "caller-nonref"
                    }
                    Cell::RefRef => {
                        ref_ref += 1;
                        "ref-ref"
                    }
                    Cell::RefNonRef => {
                        ref_non_ref += 1;
                        exposure_slots.insert(SlotKey::of(caller_slot));
                        match callee_kind {
                            SlotKind::Raw => exposure_raw += 1,
                            SlotKind::Owning => exposure_owning += 1,
                            SlotKind::Ref => unreachable!(),
                        }
                        "ref-nonref"
                    }
                };
                let caller_key = SlotKey::of(caller_slot);
                let callee_key = SlotKey::of(callee_slot);
                ledger.push_str(&format!(
                    "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{:?}\t{:?}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
                    name,
                    caller_path,
                    block.index(),
                    data.statements.len(),
                    callee_path,
                    depth,
                    caller_key.variant,
                    caller_key.owner,
                    caller_key.slot,
                    callee_key.variant,
                    callee_key.owner,
                    callee_key.slot,
                    caller_kind,
                    callee_kind,
                    cell_label,
                    registered_upper_bound,
                    evidence.class,
                    evidence.modeled,
                    evidence.unknown,
                    evidence.fresh,
                    evidence.opaque,
                    evidence.refined_eligible,
                ));
            }
        }
    }
    assert_eq!(
        caller_non_ref + ref_ref + ref_non_ref,
        universe,
        "A16 partition residual"
    );
    assert_eq!(
        matched_upper_bound, upper_bound,
        "registered A16 upper-bound identity mismatch"
    );

    fs::create_dir_all(&output).expect("create A16 output directory");
    fs::write(output.join("return-kind-ledger.tsv"), ledger).expect("write A16 ledger");
    let model_digest = model_sha256(&model_path);
    let upper_bound_digest = model_sha256(&upper_bound_path);
    let count = |map: &BTreeMap<&'static str, usize>, key| map.get(key).copied().unwrap_or(0);
    let receipt = format!(
        "schema=a16-origin-census-v2\nstatus=ok\ndata=provisional\ncorpus=rs-crown\nanalysis_head=fec2e82c123e847f6497e2a0c583dbac0c947bdf\nobserver_head={observer_head}\nprogram={name}\nmodel_mode=a14-precise\na5_world=closed_world_frozen_graph\ncopy_lend_mode=baseline\na2_mode=off\nsolve_calls=0\nmodel={}\nmodel_sha256={model_digest}\nupper_bound_ledger={}\nupper_bound_ledger_sha256={upper_bound_digest}\nupper_bound_rows={}\nuniverse={universe}\ncaller_non_ref={caller_non_ref}\nref_ref={ref_ref}\nref_non_ref={ref_non_ref}\nexposure_raw={exposure_raw}\nexposure_owning={exposure_owning}\nexposure_unique_caller_slots={}\norigin_modeled={}\norigin_unknown={}\norigin_fresh={}\norigin_opaque={}\nexposure_origin_modeled={}\nexposure_origin_unknown={}\nexposure_origin_fresh={}\nexposure_origin_opaque={}\nrefined_eligible={refined_eligible}\nrefined_eligible_exposure={refined_eligible_exposure}\nunresolved=0\n",
        model_path.display(),
        upper_bound_path.display(),
        upper_bound.len(),
        exposure_slots.len(),
        count(&origin_counts, "modeled-borrow-origin"),
        count(&origin_counts, "unknown"),
        count(&origin_counts, "fresh-owning"),
        count(&origin_counts, "foreign-opaque"),
        count(&exposure_origin_counts, "modeled-borrow-origin"),
        count(&exposure_origin_counts, "unknown"),
        count(&exposure_origin_counts, "fresh-owning"),
        count(&exposure_origin_counts, "foreign-opaque"),
    );
    fs::write(output.join("receipt.txt"), receipt).expect("write A16 receipt");

    let mut row = super::report::Row::default();
    row.set("status", "ok");
    row.set("data", "true");
    row.set("corpus", "rs-crown");
    row.set("program", name);
    row.set("observer_head", observer_head);
    row.set("analysis_head", "fec2e82c123e847f6497e2a0c583dbac0c947bdf");
    row.set("model_mode", "a14-precise");
    row.set("solve_calls", 0);
    row.set("upper_bound_rows", upper_bound.len());
    row.set("universe", universe);
    row.set("caller_non_ref", caller_non_ref);
    row.set("ref_ref", ref_ref);
    row.set("ref_non_ref", ref_non_ref);
    row.set("exposure_raw", exposure_raw);
    row.set("exposure_owning", exposure_owning);
    row.set("exposure_unique_caller_slots", exposure_slots.len());
    row.set(
        "origin_modeled",
        count(&origin_counts, "modeled-borrow-origin"),
    );
    row.set("origin_unknown", count(&origin_counts, "unknown"));
    row.set("origin_fresh", count(&origin_counts, "fresh-owning"));
    row.set("origin_opaque", count(&origin_counts, "foreign-opaque"));
    row.set(
        "exposure_origin_modeled",
        count(&exposure_origin_counts, "modeled-borrow-origin"),
    );
    row.set(
        "exposure_origin_unknown",
        count(&exposure_origin_counts, "unknown"),
    );
    row.set(
        "exposure_origin_fresh",
        count(&exposure_origin_counts, "fresh-owning"),
    );
    row.set(
        "exposure_origin_opaque",
        count(&exposure_origin_counts, "foreign-opaque"),
    );
    row.set("refined_eligible", refined_eligible);
    row.set("refined_eligible_exposure", refined_eligible_exposure);
    row.set("unresolved", 0);
    row.set("t_tcx_s", t_tcx.as_secs_f64());
    row.set(
        "t_total_s",
        started.elapsed().as_secs_f64() + t_tcx.as_secs_f64(),
    );
    row
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exposure_partition_is_exact() {
        assert_eq!(classify(SlotKind::Raw, SlotKind::Ref), Cell::CallerNonRef);
        assert_eq!(classify(SlotKind::Ref, SlotKind::Ref), Cell::RefRef);
        assert_eq!(classify(SlotKind::Ref, SlotKind::Raw), Cell::RefNonRef);
        assert_eq!(classify(SlotKind::Ref, SlotKind::Owning), Cell::RefNonRef);
    }
}
