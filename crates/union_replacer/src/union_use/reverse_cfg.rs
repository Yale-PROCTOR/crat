use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def::DefKind;
use rustc_index::Idx;
use rustc_middle::{
    mir::{Body, Location, TerminatorKind},
    ty::TyCtxt,
};
use rustc_span::def_id::{DefId, LocalDefId};

use super::{
    analysis::{UnionInstanceUses, UnionMemoryInstance, UnionRead, UnionUseResult, UnionWrite},
    callgraph::CallGraph,
};

pub type ReachingWrites = FxHashMap<UnionRead, Vec<UnionWrite>>;

pub struct ReverseCfgAnalysis {
    pub uses: FxHashMap<DefId, ReverseCfgTypeResult>,
}

#[derive(Default)]
pub struct ReverseCfgTypeResult {
    pub instances: FxHashMap<UnionMemoryInstance, ReachingWrites>,
}

pub fn analyze_reaching_writes<'tcx>(
    tcx: TyCtxt<'tcx>,
    union_uses: &UnionUseResult,
    callgraphs: &FxHashMap<LocalDefId, CallGraph>,
    use_optimized_mir: bool,
) -> ReverseCfgAnalysis {
    let mut result = FxHashMap::default();

    for (&union_ty, type_uses) in &union_uses.uses {
        let Some(local_union_ty) = union_ty.as_local() else {
            continue;
        };
        let Some(callgraph) = callgraphs.get(&local_union_ty) else {
            continue;
        };

        let mut instances = FxHashMap::default();
        for (&instance, instance_uses) in &type_uses.instances {
            let reaching =
                analyze_instance_reaching_writes(tcx, instance_uses, callgraph, use_optimized_mir);
            instances.insert(instance, reaching);
        }

        result.insert(union_ty, ReverseCfgTypeResult { instances });
    }

    ReverseCfgAnalysis { uses: result }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum SearchPoint {
    Entry(LocalDefId),
    Location {
        def_id: LocalDefId,
        location: Location,
    },
}

#[derive(Default)]
struct InstanceIndex {
    reads_by_fn: FxHashMap<LocalDefId, Vec<UnionRead>>,
    writes_by_loc: FxHashMap<(LocalDefId, Location), Vec<UnionWrite>>,
}

#[derive(Default)]
struct CallIndex {
    callers_of: FxHashMap<LocalDefId, Vec<(LocalDefId, Location)>>,
    callees_of: FxHashMap<(LocalDefId, Location), Vec<LocalDefId>>,
}

fn analyze_instance_reaching_writes<'tcx>(
    tcx: TyCtxt<'tcx>,
    instance_uses: &UnionInstanceUses,
    callgraph: &CallGraph,
    use_optimized_mir: bool,
) -> ReachingWrites {
    let instance_index = build_instance_index(instance_uses);
    let call_index = build_call_index(tcx, callgraph, use_optimized_mir);

    let mut all_reads = instance_index
        .reads_by_fn
        .values()
        .flat_map(|reads| reads.iter().copied())
        .collect::<Vec<_>>();
    all_reads.sort_by_key(|read| sort_location_key(read.site.def_id, read.site.location));

    let mut result = FxHashMap::default();
    for read in all_reads {
        let writes = collect_reaching_writes_for_read(
            tcx,
            read,
            &instance_index,
            &call_index,
            use_optimized_mir,
        );
        result.insert(read, writes);
    }
    result
}

fn collect_reaching_writes_for_read<'tcx>(
    tcx: TyCtxt<'tcx>,
    read: UnionRead,
    instance_index: &InstanceIndex,
    call_index: &CallIndex,
    use_optimized_mir: bool,
) -> Vec<UnionWrite> {
    let mut found = FxHashSet::default();
    let mut visited = FxHashSet::default();
    let mut stack = vec![SearchPoint::Location {
        def_id: read.site.def_id,
        location: read.site.location,
    }];

    while let Some(point) = stack.pop() {
        if !visited.insert(point) {
            continue;
        }

        match point {
            SearchPoint::Entry(def_id) => {
                if let Some(callers) = call_index.callers_of.get(&def_id) {
                    for &(caller, call_location) in callers {
                        with_body(tcx, caller, use_optimized_mir, |body| {
                            stack.extend(previous_relevant_points(
                                body,
                                caller,
                                call_location,
                                instance_index,
                                call_index,
                            ));
                        });
                    }
                }
            }
            SearchPoint::Location { def_id, location } => {
                if let Some(writes) = instance_index.writes_by_loc.get(&(def_id, location)) {
                    found.extend(writes.iter().copied());
                    continue;
                }

                with_body(tcx, def_id, use_optimized_mir, |body| {
                    if let Some(callees) = call_index.callees_of.get(&(def_id, location)) {
                        let mut entered_callee = false;
                        for &callee in callees {
                            with_body(tcx, callee, use_optimized_mir, |callee_body| {
                                let returns = return_predecessors(
                                    callee_body,
                                    callee,
                                    instance_index,
                                    call_index,
                                );
                                if !returns.is_empty() {
                                    entered_callee = true;
                                    stack.extend(returns);
                                }
                            });
                        }
                        if entered_callee {
                            return;
                        }
                    }

                    stack.extend(previous_relevant_points(
                        body,
                        def_id,
                        location,
                        instance_index,
                        call_index,
                    ));
                });
            }
        }
    }

    let mut writes = found.into_iter().collect::<Vec<_>>();
    writes.sort_by_key(|write| sort_location_key(write.site.def_id, write.site.location));
    writes
}

fn build_instance_index(instance_uses: &UnionInstanceUses) -> InstanceIndex {
    let mut index = InstanceIndex::default();

    for (&def_id, reads) in &instance_uses.reads {
        let mut reads = reads.clone();
        reads.sort_by_key(|read| sort_location_key(def_id, read.site.location));
        index.reads_by_fn.insert(def_id, reads);
    }

    for (&def_id, writes) in &instance_uses.writes {
        for &write in writes {
            index
                .writes_by_loc
                .entry((def_id, write.site.location))
                .or_default()
                .push(write);
        }
    }

    index
}

fn build_call_index<'tcx>(
    tcx: TyCtxt<'tcx>,
    callgraph: &CallGraph,
    use_optimized_mir: bool,
) -> CallIndex {
    let mut relevant_callees: FxHashMap<LocalDefId, FxHashSet<LocalDefId>> = FxHashMap::default();
    for (&caller, callees) in callgraph {
        let Some(caller) = caller.as_local() else {
            continue;
        };
        for callee in callees.iter().filter_map(|callee| callee.as_local()) {
            relevant_callees.entry(caller).or_default().insert(callee);
        }
    }

    let mut index = CallIndex::default();
    for (&caller, candidate_callees) in &relevant_callees {
        with_body(tcx, caller, use_optimized_mir, |body| {
            for (block, bbd) in body.basic_blocks.iter_enumerated() {
                let location = Location {
                    block,
                    statement_index: bbd.statements.len(),
                };
                let TerminatorKind::Call { func, .. } = &bbd.terminator().kind else {
                    continue;
                };
                let Some((callee, _)) = func.const_fn_def() else {
                    continue;
                };
                let Some(callee) = callee.as_local() else {
                    continue;
                };
                if !candidate_callees.contains(&callee) {
                    continue;
                }

                index
                    .callees_of
                    .entry((caller, location))
                    .or_default()
                    .push(callee);
                index
                    .callers_of
                    .entry(callee)
                    .or_default()
                    .push((caller, location));
            }
        });
    }

    for callees in index.callees_of.values_mut() {
        callees.sort_by_key(|def_id| def_id.index());
        callees.dedup();
    }
    for callers in index.callers_of.values_mut() {
        callers.sort_by_key(|(def_id, location)| {
            (
                def_id.index(),
                location.block.index(),
                location.statement_index,
            )
        });
        callers.dedup();
    }

    index
}

fn previous_relevant_points<'tcx>(
    body: &Body<'tcx>,
    def_id: LocalDefId,
    location: Location,
    instance_index: &InstanceIndex,
    call_index: &CallIndex,
) -> Vec<SearchPoint> {
    let mut out = FxHashSet::default();
    let mut visited_blocks = FxHashSet::default();
    collect_previous_relevant_points(
        body,
        def_id,
        location,
        instance_index,
        call_index,
        &mut visited_blocks,
        &mut out,
    );

    let mut out = out.into_iter().collect::<Vec<_>>();
    out.sort_by_key(sort_point_key);
    out
}

fn collect_previous_relevant_points<'tcx>(
    body: &Body<'tcx>,
    def_id: LocalDefId,
    location: Location,
    instance_index: &InstanceIndex,
    call_index: &CallIndex,
    visited_blocks: &mut FxHashSet<rustc_middle::mir::BasicBlock>,
    out: &mut FxHashSet<SearchPoint>,
) {
    for stmt_index in (0..location.statement_index).rev() {
        let candidate = Location {
            block: location.block,
            statement_index: stmt_index,
        };
        if is_relevant_location(body, def_id, candidate, instance_index, call_index) {
            out.insert(SearchPoint::Location {
                def_id,
                location: candidate,
            });
            return;
        }
    }

    if !visited_blocks.insert(location.block) {
        return;
    }

    if location.block.index() == 0 {
        out.insert(SearchPoint::Entry(def_id));
    }

    for pred_block in body.basic_blocks.predecessors()[location.block]
        .iter()
        .copied()
    {
        let pred_location = body.terminator_loc(pred_block);
        if is_relevant_location(body, def_id, pred_location, instance_index, call_index) {
            out.insert(SearchPoint::Location {
                def_id,
                location: pred_location,
            });
            continue;
        }

        collect_previous_relevant_points(
            body,
            def_id,
            pred_location,
            instance_index,
            call_index,
            visited_blocks,
            out,
        );
    }
}

fn return_predecessors<'tcx>(
    body: &Body<'tcx>,
    def_id: LocalDefId,
    instance_index: &InstanceIndex,
    call_index: &CallIndex,
) -> Vec<SearchPoint> {
    let mut out = Vec::new();
    for (block, bbd) in body.basic_blocks.iter_enumerated() {
        if !matches!(bbd.terminator().kind, TerminatorKind::Return) {
            continue;
        }

        let location = Location {
            block,
            statement_index: bbd.statements.len(),
        };
        if is_relevant_location(body, def_id, location, instance_index, call_index) {
            out.push(SearchPoint::Location { def_id, location });
        } else {
            out.extend(previous_relevant_points(
                body,
                def_id,
                location,
                instance_index,
                call_index,
            ));
        }
    }

    out.sort_by_key(sort_point_key);
    out.dedup();
    out
}

fn is_relevant_location(
    _body: &Body<'_>,
    def_id: LocalDefId,
    location: Location,
    instance_index: &InstanceIndex,
    call_index: &CallIndex,
) -> bool {
    instance_index
        .writes_by_loc
        .contains_key(&(def_id, location))
        || instance_index
            .reads_by_fn
            .get(&def_id)
            .is_some_and(|reads| reads.iter().any(|read| read.site.location == location))
        || call_index.callees_of.contains_key(&(def_id, location))
}

fn with_body<'tcx, R, F: FnOnce(&Body<'tcx>) -> R>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    use_optimized_mir: bool,
    f: F,
) -> R {
    debug_assert!(matches!(
        tcx.def_kind(def_id),
        DefKind::Fn | DefKind::AssocFn
    ));
    if use_optimized_mir {
        f(tcx.optimized_mir(def_id.to_def_id()))
    } else {
        let body = tcx.mir_drops_elaborated_and_const_checked(def_id);
        let body = body.borrow();
        f(&body)
    }
}

fn sort_location_key(def_id: LocalDefId, location: Location) -> (usize, usize, usize) {
    (
        def_id.index(),
        location.block.index(),
        location.statement_index,
    )
}

fn sort_point_key(point: &SearchPoint) -> (usize, usize, usize, u8) {
    match point {
        SearchPoint::Entry(def_id) => (def_id.index(), 0, 0, 0),
        SearchPoint::Location { def_id, location } => (
            def_id.index(),
            location.block.index(),
            location.statement_index,
            1,
        ),
    }
}
