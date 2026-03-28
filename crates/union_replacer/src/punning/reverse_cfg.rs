use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::{
    mir::{Body, Location},
    ty::TyCtxt,
};
use rustc_span::def_id::{DefId, LocalDefId};

use super::{
    analysis::{
        CopyPoint, CopySource, UnionInstanceUses, UnionMemoryInstance, UnionRead, UnionUseResult,
        UnionWrite, format_access, union_field_ty,
    },
    callgraph::{CallIndex, CallSite, UnionCallContext},
    utils::with_body,
};

pub type ReadToWrites = FxHashMap<UnionRead, Vec<UnionWrite>>;

pub struct ReverseCfgResult {
    pub uses: FxHashMap<DefId, InstanceResult>,
}

#[derive(Default)]
pub struct InstanceResult {
    pub instances: FxHashMap<UnionMemoryInstance, ReadToWrites>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum SearchPoint {
    Entry(LocalDefId),
    Location {
        def_id: LocalDefId,
        location: Location,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct SearchState {
    point: SearchPoint,
    active_callsite: Option<CallSite>,
}

#[derive(Default)]
struct InstanceIndex {
    writes_by_loc: FxHashMap<(LocalDefId, Location), Vec<UnionWrite>>,
    copies_by_loc: FxHashMap<(LocalDefId, Location), Vec<CopySource>>,
    entry_copies: FxHashMap<LocalDefId, Vec<CopySource>>,
}

struct ReachingWriteAnalyzer<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    call_index: &'a CallIndex,
    indices: &'a FxHashMap<UnionMemoryInstance, InstanceIndex>,
    cache: FxHashMap<(UnionMemoryInstance, SearchState), Vec<UnionWrite>>,
    active: FxHashSet<(UnionMemoryInstance, SearchState)>,
}

pub fn analyze_reaching_writes<'tcx>(
    tcx: TyCtxt<'tcx>,
    union_uses: &UnionUseResult,
    call_contexts: &FxHashMap<LocalDefId, UnionCallContext>,
) -> ReverseCfgResult {
    let mut result = FxHashMap::default();

    for (&union_ty, type_uses) in &union_uses.uses {
        let Some(local_union_ty) = union_ty.as_local() else {
            continue;
        };
        let Some(call_context) = call_contexts.get(&local_union_ty) else {
            continue;
        };

        let instance_indices = type_uses
            .instances
            .iter()
            .map(|(&instance, instance_uses)| (instance, build_instance_index(instance_uses)))
            .collect::<FxHashMap<_, _>>();
        let mut analyzer = ReachingWriteAnalyzer {
            tcx,
            call_index: &call_context.call_index,
            indices: &instance_indices,
            cache: FxHashMap::default(),
            active: FxHashSet::default(),
        };

        let mut instances = FxHashMap::default();
        for (&instance, instance_uses) in &type_uses.instances {
            let reaching = analyze_instance_reaching_writes(&mut analyzer, instance, instance_uses);
            instances.insert(instance, reaching);
        }

        result.insert(union_ty, InstanceResult { instances });
    }

    ReverseCfgResult { uses: result }
}

pub fn print_reaching_writes<'tcx>(
    tcx: TyCtxt<'tcx>,
    union_uses: &UnionUseResult,
    analysis: &ReverseCfgResult,
) {
    let union_tys = union_uses.uses.keys().copied().collect::<Vec<_>>();
    println!("\nReaching Writes:");

    for union_ty in union_tys {
        let Some(type_uses) = union_uses.uses.get(&union_ty) else {
            continue;
        };
        let Some(type_result) = analysis.uses.get(&union_ty) else {
            continue;
        };
        println!("\t{}:", tcx.def_path_str(union_ty));

        for instance in type_uses.instances.keys() {
            let Some(reaching) = type_result.instances.get(instance) else {
                continue;
            };

            let reads = reaching.iter().collect::<Vec<_>>();
            if reads.is_empty() {
                continue;
            }
            for (read, writes) in reads {
                let read_field = format_access(tcx, union_ty, read);
                let read_fields = read.field.to_fields(tcx, union_ty);
                let read_field_ty = if read_fields.len() == 1 {
                    let read_index = *read_fields.iter().next().unwrap();
                    union_field_ty(
                        tcx,
                        union_ty,
                        super::analysis::UnionAccessField::Field(read_index),
                    )
                } else {
                    None
                };
                let writes = writes.clone();

                let write_sites = writes
                    .into_iter()
                    .map(|write| {
                        format!(
                            "{:?}@{:?}\n\t\t\t\t\tfield:\t{}",
                            write.site.def_id,
                            write.site.location,
                            format_access(tcx, union_ty, &write),
                        )
                    })
                    .collect::<Vec<_>>()
                    .join("\n\t\t\t\t");

                println!(
                    "\t\t\tRead {:?}@{:?}\n\t\t\t\tfield:\t{}",
                    read.site.def_id, read.site.location, read_field
                );
                if let Some(ty) = read_field_ty {
                    println!("\t\t\t\ttype:\t{ty:?}");
                }
                if write_sites.is_empty() {
                    println!("\t\t\t\tWrites:\t(none)");
                } else {
                    println!("\t\t\t\tWrites:\n\t\t\t\t{write_sites}");
                }
            }
        }
    }
}

fn analyze_instance_reaching_writes<'tcx>(
    analyzer: &mut ReachingWriteAnalyzer<'_, 'tcx>,
    instance: UnionMemoryInstance,
    instance_uses: &UnionInstanceUses,
) -> ReadToWrites {
    let reads = instance_uses
        .reads
        .values()
        .flat_map(|reads| reads.iter().copied())
        .collect::<Vec<_>>();

    let mut result = FxHashMap::default();
    for read in reads {
        let writes = analyzer.collect_reaching_writes(
            instance,
            SearchState {
                point: SearchPoint::Location {
                    def_id: read.site.def_id,
                    location: read.site.location,
                },
                active_callsite: None,
            },
        );
        result.insert(read, writes);
    }
    result
}

impl<'a, 'tcx> ReachingWriteAnalyzer<'a, 'tcx> {
    fn collect_reaching_writes(
        &mut self,
        instance: UnionMemoryInstance,
        start: SearchState,
    ) -> Vec<UnionWrite> {
        let key = (instance, start);
        if let Some(cached) = self.cache.get(&key) {
            return cached.clone();
        }
        if !self.active.insert(key) {
            return Vec::new();
        }

        let Some(instance_index) = self.indices.get(&instance) else {
            self.active.remove(&key);
            return Vec::new();
        };

        let mut found = FxHashSet::default();
        let mut visited = FxHashSet::default();
        let mut entered_callsites = FxHashSet::default();
        let mut worklist = vec![start];

        while let Some(state) = worklist.pop() {
            if !visited.insert(state) {
                continue;
            }

            match state.point {
                SearchPoint::Entry(def_id) => {
                    if let Some(copies) = instance_index.entry_copies.get(&def_id).cloned() {
                        self.apply_copies(&mut found, &copies, None);
                        continue;
                    }

                    if let Some(active_callsite) = state.active_callsite {
                        if let Some(writes) = instance_index
                            .writes_by_loc
                            .get(&(active_callsite.caller, active_callsite.call_location))
                        {
                            found.extend(writes.iter().copied());
                        }
                        if let Some(copies) = instance_index
                            .copies_by_loc
                            .get(&(active_callsite.caller, active_callsite.call_location))
                            .cloned()
                        {
                            self.apply_copies(&mut found, &copies, Some(active_callsite));
                            continue;
                        }
                        with_body(self.tcx, active_callsite.caller, |body| {
                            for point in previous_points(
                                body,
                                active_callsite.caller,
                                active_callsite.call_location,
                            ) {
                                worklist.push(SearchState {
                                    point,
                                    active_callsite: None,
                                });
                            }
                        });
                        continue;
                    }

                    if let Some(callers) = self.call_index.callers_of.get(&def_id) {
                        for &callsite in callers {
                            if !entered_callsites.insert(callsite) {
                                continue;
                            }
                            if let Some(writes) = instance_index
                                .writes_by_loc
                                .get(&(callsite.caller, callsite.call_location))
                            {
                                found.extend(writes.iter().copied());
                            }
                            if let Some(copies) = instance_index
                                .copies_by_loc
                                .get(&(callsite.caller, callsite.call_location))
                                .cloned()
                            {
                                self.apply_copies(&mut found, &copies, Some(callsite));
                                continue;
                            }
                            with_body(self.tcx, callsite.caller, |body| {
                                for point in
                                    previous_points(body, callsite.caller, callsite.call_location)
                                {
                                    worklist.push(SearchState {
                                        point,
                                        active_callsite: None,
                                    });
                                }
                            });
                        }
                    }
                }
                SearchPoint::Location { def_id, location } => {
                    if let Some(writes) = instance_index.writes_by_loc.get(&(def_id, location)) {
                        found.extend(writes.iter().copied());
                        continue;
                    }

                    let callsite = CallSite {
                        caller: def_id,
                        call_location: location,
                    };
                    if let Some(copies) = instance_index
                        .copies_by_loc
                        .get(&(def_id, location))
                        .cloned()
                    {
                        let copy_callsite = if self.call_index.callees_of.contains_key(&callsite) {
                            Some(callsite)
                        } else {
                            state.active_callsite
                        };
                        self.apply_copies(&mut found, &copies, copy_callsite);
                        continue;
                    }

                    if self.call_index.callees_of.contains_key(&callsite) {
                        if entered_callsites.insert(callsite)
                            && let Some(entries) = self.call_index.return_entries_of.get(&callsite)
                        {
                            for &(callee, return_location) in entries {
                                worklist.push(SearchState {
                                    point: SearchPoint::Location {
                                        def_id: callee,
                                        location: return_location,
                                    },
                                    active_callsite: Some(callsite),
                                });
                            }
                        }
                        continue;
                    }

                    with_body(self.tcx, def_id, |body| {
                        for point in previous_points(body, def_id, location) {
                            worklist.push(SearchState {
                                point,
                                active_callsite: state.active_callsite,
                            });
                        }
                    });
                }
            }
        }

        let out = found.into_iter().collect::<Vec<_>>();
        self.active.remove(&key);
        self.cache.insert(key, out.clone());
        out
    }

    fn apply_copies(
        &mut self,
        found: &mut FxHashSet<UnionWrite>,
        copies: &[CopySource],
        active_callsite: Option<CallSite>,
    ) {
        for copy in copies {
            found.extend(self.copy_writes(*copy, active_callsite));
        }
    }

    fn copy_writes(
        &mut self,
        copy: CopySource,
        active_callsite: Option<CallSite>,
    ) -> Vec<UnionWrite> {
        self.collect_reaching_writes(
            copy.source_instance,
            SearchState {
                point: SearchPoint::Location {
                    def_id: copy.source_site.def_id,
                    location: copy.source_site.location,
                },
                active_callsite,
            },
        )
    }
}

fn build_instance_index(instance_uses: &UnionInstanceUses) -> InstanceIndex {
    let mut index = InstanceIndex {
        writes_by_loc: FxHashMap::default(),
        copies_by_loc: FxHashMap::default(),
        entry_copies: FxHashMap::default(),
    };

    for (&def_id, writes) in &instance_uses.writes {
        for &write in writes {
            index
                .writes_by_loc
                .entry((def_id, write.site.location))
                .or_default()
                .push(write);
        }
    }

    for &copy_init in &instance_uses.copies {
        match copy_init.point {
            CopyPoint::Entry(def_id) => {
                index
                    .entry_copies
                    .entry(def_id)
                    .or_default()
                    .push(copy_init);
            }
            CopyPoint::Location { def_id, location } => {
                index
                    .copies_by_loc
                    .entry((def_id, location))
                    .or_default()
                    .push(copy_init);
            }
        }
    }

    index
}

fn previous_points<'tcx>(
    body: &Body<'tcx>,
    def_id: LocalDefId,
    location: Location,
) -> Vec<SearchPoint> {
    if location.statement_index > 0 {
        return vec![SearchPoint::Location {
            def_id,
            location: Location {
                block: location.block,
                statement_index: location.statement_index - 1,
            },
        }];
    }

    let mut out = Vec::new();
    if location.block.index() == 0 {
        out.push(SearchPoint::Entry(def_id));
    }

    for pred_block in body.basic_blocks.predecessors()[location.block]
        .iter()
        .copied()
    {
        out.push(SearchPoint::Location {
            def_id,
            location: body.terminator_loc(pred_block),
        });
    }

    let mut seen = FxHashSet::default();
    out.retain(|p| seen.insert(*p));
    out
}
