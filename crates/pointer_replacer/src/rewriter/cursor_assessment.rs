//! diagnostics-only impact assessment for cursor-parameter demotion.
//! enabled via `CRAT_CURSOR_ASSESS=1`; prints to stderr and changes nothing.
//!
//! classifies every parameter that would be rewritten to `SliceCursor`:
//! - class 1: no definitely-negative movement reaches it (demotable to slice)
//! - class 2: definitely goes below its entry position (must stay cursor;
//!   call sites need a base-preserving construction or bail to raw)
//! - class 3: function is reachable through a function pointer (keep cursor)
//!
//! for class-2 parameters, each call-site argument is checked against the
//! pointer-flow provenance to see whether a unique allocation base is known
//! (i.e. whether `with_pos` construction is derivable).

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    mir::{Body, Local, Operand, Place, TerminatorKind},
    ty::{self, TyCtxt},
};

use super::decision::{DecisionMaker, PtrKind};
use crate::{
    analyses::{
        fn_ptr_groups::FnPtrGroups,
        pointer_flow::{
            self, PointerFlowResult,
            graph::{BaseId, PfgNode},
        },
    },
    rewriter::Analysis,
    utils::rustc::RustProgram,
};

pub(super) fn assess(
    input: &RustProgram<'_>,
    analysis: &Analysis,
    fn_ptr_groups: &FnPtrGroups,
    alloc_fns: &FxHashSet<LocalDefId>,
) {
    let tcx = input.tcx;
    let flows = pointer_flow::pointer_flow_analysis(input, alloc_fns);
    let demotion = &analysis.cursor_demotion;

    let mut class_counts = [0usize; 3];
    let mut class2_params: FxHashMap<LocalDefId, Vec<Local>> = FxHashMap::default();
    let mut class2_local_bases: FxHashMap<String, usize> = FxHashMap::default();
    let mut callsite_bases: FxHashMap<String, usize> = FxHashMap::default();
    // stage-0 gap set: params tainted may-negative but not definitely negative
    let mut gap_shapes: FxHashMap<String, usize> = FxHashMap::default();
    let mut gap_params = 0usize;

    // pass 1: classify cursor params and definitely-negative non-param locals
    for &did in &input.functions {
        let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
        let decision_maker = DecisionMaker::new(analysis, did, tcx);
        let aliases = analysis.aliases.get(&did);
        let addr_taken = fn_ptr_groups.fn_to_group.contains_key(&did);
        let definite = analysis.offset_sign_result.definite_signs.get(&did);

        for (local, decl) in body.local_decls.iter_enumerated().skip(1) {
            let local_aliases = aliases.and_then(|a| a.get(&local));
            let decision = decision_maker.decide(local, decl, local_aliases);
            if !matches!(decision, Some(PtrKind::SliceCursor(_))) {
                continue;
            }
            let is_definite = definite.is_some_and(|d| d.contains(local));
            if local.index() <= body.arg_count {
                let class = if demotion.is_demotable(did, local) {
                    1
                } else if addr_taken {
                    3
                } else {
                    2
                };
                class_counts[class - 1] += 1;
                eprintln!(
                    "CURSOR-ASSESS param fn={} local={:?} class={} seeds=[{}]",
                    tcx.def_path_str(did),
                    local,
                    class,
                    seed_summary(analysis, tcx, did, local),
                );
                if class == 2 {
                    class2_params.entry(did).or_default().push(local);
                }
            } else if is_definite {
                let status = flows
                    .get(&did)
                    .map(|flow| base_status(flow, &body, tcx, Place::from(local)))
                    .unwrap_or_else(|| "no-flow".to_string());
                eprintln!(
                    "CURSOR-ASSESS local fn={} local={:?} base={}",
                    tcx.def_path_str(did),
                    local,
                    status,
                );
                *class2_local_bases.entry(status).or_default() += 1;
            }
        }
    }

    // pass 1b: the gap set, measured from the sign analysis alone so it is
    // independent of demotion having already turned these params into slices.
    // a param is in the gap when taint reaches it (`access_signs`: it would
    // need a cursor under a sound criterion) but it is not definitely negative
    // (`definite_signs`) -- i.e. where cursor selection rests on imprecision
    // rather than on proof. bucketed by which fact family would refute it.
    for &did in &input.functions {
        let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
        let Some(access) = analysis.offset_sign_result.access_signs.get(&did) else {
            continue;
        };
        let definite = analysis.offset_sign_result.definite_signs.get(&did);
        for local in body.args_iter() {
            if !access.contains(local) || definite.is_some_and(|d| d.contains(local)) {
                continue;
            }
            gap_params += 1;
            let shapes = shape_summary(analysis, did, local);
            eprintln!(
                "CURSOR-GAP param fn={} local={:?} shapes=[{}] seeds=[{}]",
                tcx.def_path_str(did),
                local,
                shapes,
                seed_summary(analysis, tcx, did, local),
            );
            *gap_shapes.entry(shapes).or_default() += 1;
        }
    }

    // pass 2: provenance of every call-site argument feeding a class-2 param
    for &did in &input.functions {
        let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
        let flow = flows.get(&did);
        for bb_data in body.basic_blocks.iter() {
            let TerminatorKind::Call { func, args, .. } = &bb_data.terminator().kind else {
                continue;
            };
            let Operand::Constant(box constant) = func else { continue };
            let ty::TyKind::FnDef(callee, _) = constant.const_.ty().kind() else { continue };
            let Some(callee) = callee.as_local() else { continue };
            let Some(params) = class2_params.get(&callee) else { continue };
            for &param in params {
                let Some(arg) = args.get(param.index() - 1) else { continue };
                let status = match &arg.node {
                    Operand::Copy(place) | Operand::Move(place) => flow
                        .map(|f| base_status(f, &body, tcx, *place))
                        .unwrap_or_else(|| "no-flow".to_string()),
                    Operand::Constant(_) => "constant".to_string(),
                };
                eprintln!(
                    "CURSOR-ASSESS callsite caller={} callee={} param={:?} base={}",
                    tcx.def_path_str(did),
                    tcx.def_path_str(callee),
                    param,
                    status,
                );
                *callsite_bases.entry(status).or_default() += 1;
            }
        }
    }

    let mut callsite_bases: Vec<_> = callsite_bases.into_iter().collect();
    callsite_bases.sort();
    let mut class2_local_bases: Vec<_> = class2_local_bases.into_iter().collect();
    class2_local_bases.sort();
    eprintln!(
        "CURSOR-ASSESS summary cursor_params={} class1={} class2={} class3={} \
         class2_callsites={:?} class2_locals={:?}",
        class_counts.iter().sum::<usize>(),
        class_counts[0],
        class_counts[1],
        class_counts[2],
        callsite_bases,
        class2_local_bases,
    );
    let mut gap_shapes: Vec<_> = gap_shapes.into_iter().collect();
    gap_shapes.sort();
    eprintln!("CURSOR-GAP summary gap_params={gap_params} shapes={gap_shapes:?}");
}

/// deduplicated, sorted shape names of the seeds reaching this local; these
/// bucket the gap set by which non-negativity fact would refute the taint
fn shape_summary(analysis: &Analysis, did: LocalDefId, local: Local) -> String {
    let Some(seeds) = analysis.offset_sign_result.reaching_seeds.get(&(did, local)) else {
        return "via-alias-group".to_string();
    };
    let mut shapes: Vec<&'static str> = seeds.iter().map(|seed| seed.shape.as_str()).collect();
    shapes.sort();
    shapes.dedup();
    shapes.join("+")
}

/// deduplicated `sign@fn@file:line` list of the offset-call seeds whose taint
/// reaches this local; empty means the taint arrived via alias-group widening
fn seed_summary(
    analysis: &Analysis,
    tcx: TyCtxt<'_>,
    did: LocalDefId,
    local: Local,
) -> String {
    let Some(seeds) = analysis.offset_sign_result.reaching_seeds.get(&(did, local)) else {
        return "via-alias-group".to_string();
    };
    let mut entries: Vec<String> = seeds
        .iter()
        .map(|seed| {
            let span = tcx.sess.source_map().span_to_embeddable_string(seed.span);
            let file_line = span
                .rsplit_once('/')
                .map(|(_, tail)| tail)
                .unwrap_or(&span)
                .to_string();
            format!(
                "{:?}@{}@{}",
                seed.abs,
                tcx.def_path_str(seed.def_id),
                file_line,
            )
        })
        .collect();
    entries.sort();
    entries.dedup();
    entries.join(", ")
}

fn base_status<'tcx>(
    flow: &PointerFlowResult,
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    place: Place<'tcx>,
) -> String {
    let Some(slot) = flow
        .slot_table
        .place_slots(place, body, tcx)
        .and_then(|mut slots| slots.next())
    else {
        return "no-slot".to_string();
    };
    let node = PfgNode::Slot(slot);
    if let Some(base) = flow.provenance.unique_non_null_base(&node) {
        format!("unique:{}", base_name(&base))
    } else {
        match flow.provenance.reachable_bases.get(&node) {
            Some(bases) if bases.len() > 1 => format!("multi:{}", bases.len()),
            _ => "none".to_string(),
        }
    }
}

fn base_name(base: &BaseId) -> &'static str {
    match base {
        BaseId::Param { .. } => "param",
        BaseId::LocalArray { .. } => "local_array",
        BaseId::LocalScalar { .. } => "local_scalar",
        BaseId::RawBorrow { .. } => "raw_borrow",
        BaseId::HeapAlloc { .. } => "heap_alloc",
        BaseId::OpaqueReturn { .. } => "opaque_return",
        BaseId::IntToPtr { .. } => "int_to_ptr",
        BaseId::Unknown { .. } => "unknown",
    }
}
