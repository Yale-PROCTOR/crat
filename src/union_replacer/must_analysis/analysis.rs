use std::collections::BTreeMap;

use rustc_data_structures::graph::Successors;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{ItemKind, def_id::DefId};
use rustc_index::{
    IndexVec,
    bit_set::{ChunkedBitSet, DenseBitSet},
};
use rustc_middle::{
    mir::{BasicBlock, BinOp, Body, Local, Location, Rvalue, StatementKind, TerminatorKind},
    ty::TyCtxt,
};
use rustc_mir_dataflow::Analysis as _;
use rustc_span::def_id::LocalDefId;
use typed_arena::Arena;

use super::domains::*;
use crate::{
    graph_util,
    points_to::andersen,
    ty_shape::{self, TyShapes},
};

#[derive(Debug, Clone)]
pub struct AnalysisResult {
    pub functions: FxHashMap<LocalDefId, FxHashMap<Location, AbsMem>>,
}

pub fn analyze(gc: bool, tcx: TyCtxt<'_>) -> AnalysisResult {
    let arena = Arena::new();
    let tss = ty_shape::get_ty_shapes(&arena, tcx);
    let pre_config = andersen::Config {
        use_optimized_mir: true,
    };
    let pre = andersen::pre_analyze(&pre_config, &tss, tcx);
    let solutions = andersen::analyze(&pre_config, &pre, &tss, tcx);
    let may_points_to = andersen::post_analyze(&pre_config, pre, solutions, &tss, tcx);
    let functions = tcx
        .hir_free_items()
        .filter_map(|item_id| {
            let item = tcx.hir_item(item_id);
            let local_def_id = item.owner_id.def_id;
            let body = match item.kind {
                ItemKind::Fn { ident, .. } if ident.name.as_str() != "main" => {
                    tcx.optimized_mir(local_def_id)
                }
                ItemKind::Static(_, _, _, _) => tcx.mir_for_ctfe(local_def_id),
                _ => return None,
            };
            let ctx = AnalysisContext {
                local_def_id,
                tss: &tss,
                may_points_to: &may_points_to,
                no_gc_locals: None,
                gc,
            };
            Some((local_def_id, analyze_body(body, ctx, tcx).states))
        })
        .collect();
    AnalysisResult { functions }
}

pub fn analyze_body<'tcx>(
    body: &'tcx Body<'tcx>,
    ctx: AnalysisContext<'_, '_, 'tcx>,
    tcx: TyCtxt<'tcx>,
) -> BodyAnalysisResult {
    let pre_rpo_map = get_rpo_map(body);
    let loop_blocks = get_loop_blocks(body, &pre_rpo_map);
    let loop_heads: FxHashSet<_> = loop_blocks.keys().map(|bb| bb.start_location()).collect();
    let rpo_map = compute_rpo_map(body, &loop_blocks);
    let join_terminators = compute_join_terminators(body);
    let mut dead_locals = get_dead_locals(body, tcx);
    if let Some(no_gc) = ctx.no_gc_locals {
        for dead in &mut dead_locals {
            dead.subtract(no_gc);
        }
    }
    let discriminant_values = find_discriminant_values(body);
    let analyzer = Analyzer {
        ctx,
        tcx,
        body,
        loop_heads,
        rpo_map,
        join_terminators,
        dead_locals,
        discriminant_values,
    };
    analyzer.analyze()
}

#[allow(missing_debug_implementations)]
#[derive(Clone, Copy)]
pub struct AnalysisContext<'a, 'b, 'tcx> {
    pub local_def_id: LocalDefId,
    pub tss: &'a TyShapes<'a, 'tcx>,
    pub may_points_to: &'b andersen::AnalysisResult,
    pub no_gc_locals: Option<&'b DenseBitSet<Local>>,
    pub gc: bool,
}

#[allow(missing_debug_implementations)]
pub struct Analyzer<'tcx, 'a, 'b> {
    pub ctx: AnalysisContext<'a, 'b, 'tcx>,
    pub tcx: TyCtxt<'tcx>,
    pub body: &'tcx Body<'tcx>,
    pub loop_heads: FxHashSet<Location>,
    pub rpo_map: FxHashMap<BasicBlock, BId>,
    pub join_terminators: FxHashSet<Location>,
    pub dead_locals: Vec<DenseBitSet<Local>>,
    pub discriminant_values: FxHashMap<BasicBlock, DiscrVal>,
}

#[derive(Debug)]
pub struct BodyAnalysisResult {
    pub states: FxHashMap<Location, AbsMem>,
    pub out_states: FxHashMap<Location, AbsMem>,
}

impl Analyzer<'_, '_, '_> {
    fn analyze(&self) -> BodyAnalysisResult {
        let bot = AbsMem::bot();

        let mut work_list = WorkList::new(&self.rpo_map);
        work_list.push(Location::START);

        let mut states = FxHashMap::default();
        states.insert(Location::START, AbsMem::top());

        let mut out_states: FxHashMap<Location, AbsMem> = FxHashMap::default();

        while let Some(location) = work_list.pop() {
            let state = states.get(&location).unwrap_or(&bot);
            let (nexts, is_call) = self.body.stmt_at(location).either(
                |stmt| {
                    let mut next_state = state.clone();
                    self.transfer_stmt(stmt, location, &mut next_state);
                    (vec![(location.successor_within_block(), next_state)], false)
                },
                |terminator| {
                    let v = self.discriminant_values.get(&location.block);
                    (
                        self.transfer_term(terminator, v, location, state),
                        matches!(terminator.kind, TerminatorKind::Call { .. }),
                    )
                },
            );
            for (next_location, new_next_state) in nexts {
                if self.join_terminators.contains(&location) || is_call {
                    let out_state = out_states.get(&location).unwrap_or(&bot);
                    let joined = out_state.join(&new_next_state);
                    out_states.insert(location, joined);
                }

                let next_state = states.get(&next_location).unwrap_or(&bot);
                let mut joined = if self.loop_heads.contains(&next_location) {
                    next_state.widen(&new_next_state)
                } else {
                    next_state.join(&new_next_state)
                };
                if self.ctx.gc && next_location.statement_index == 0 {
                    let dead_locals = &self.dead_locals[next_location.block.as_usize()];
                    joined.clear_dead_locals(dead_locals);
                }
                if !joined.ord(next_state) {
                    states.insert(next_location, joined);
                    work_list.push(next_location);
                }
            }
        }

        BodyAnalysisResult { states, out_states }
    }

    pub fn resolve_indirect_call(&self, loc: Location) -> &[LocalDefId] {
        &self.ctx.may_points_to.indirect_calls[&self.ctx.local_def_id][&loc.block]
    }

    pub fn get_assign_writes(&self, loc: Location) -> Option<&ChunkedBitSet<andersen::Loc>> {
        let w = &self.ctx.may_points_to.writes[&self.ctx.local_def_id][&loc];
        if w.is_empty() { None } else { Some(w) }
    }

    pub fn get_bitfield_writes(&self, loc: Location) -> Option<&ChunkedBitSet<andersen::Loc>> {
        let w = self.ctx.may_points_to.bitfield_writes[&self.ctx.local_def_id].get(&loc)?;
        if w.is_empty() { None } else { Some(w) }
    }

    pub fn get_call_writes(&self, callees: &[LocalDefId]) -> Option<ChunkedBitSet<andersen::Loc>> {
        let c0 = callees.first()?;
        let mut writes = self.ctx.may_points_to.call_writes(*c0);
        for c in &callees[1..] {
            writes.union(&self.ctx.may_points_to.call_writes(*c));
        }
        if writes.is_empty() {
            None
        } else {
            Some(writes)
        }
    }

    pub fn get_arg_writes<I: Iterator<Item = Local>>(
        &self,
        locals: I,
    ) -> Option<ChunkedBitSet<andersen::Loc>> {
        let mut writes = locals
            .flat_map(|local| {
                let start = self.ctx.may_points_to.var_nodes[&(self.ctx.local_def_id, local)].index;
                let end = self.ctx.may_points_to.ends[start];
                start..=end
            })
            .map(|index| &self.ctx.may_points_to.solutions[index]);
        let mut w = writes.next()?.clone();
        for write in writes {
            w.union(write);
        }
        if w.is_empty() { None } else { Some(w) }
    }

    pub fn def_id_to_string(&self, def_id: DefId) -> String {
        self.tcx.def_path(def_id).to_string_no_crate_verbose()
    }
}

#[derive(Debug)]
struct WorkList<'a> {
    rpo_map: &'a FxHashMap<BasicBlock, BId>,
    /// From the BId and statement index to the location.
    locations: BTreeMap<(BId, usize), Location>,
}

impl<'a> WorkList<'a> {
    fn new(rpo_map: &'a FxHashMap<BasicBlock, BId>) -> Self {
        Self {
            rpo_map,
            locations: BTreeMap::new(),
        }
    }

    fn pop(&mut self) -> Option<Location> {
        let (_, loc) = self.locations.pop_first()?;
        Some(loc)
    }

    fn push(&mut self, location: Location) {
        let block_idx = self.rpo_map[&location.block];
        self.locations
            .insert((block_idx, location.statement_index), location);
    }
}

rustc_index::newtype_index! {
    #[orderable]
    #[debug_format = "B{}"]
    /// A unique identifier for a basic block in the reverse postorder traversal.
    pub struct BId {}
}

fn get_rpo_map(body: &Body<'_>) -> FxHashMap<BasicBlock, BId> {
    body.basic_blocks
        .reverse_postorder()
        .iter()
        .enumerate()
        .map(|(i, bb)| (*bb, BId::from_usize(i)))
        .collect()
}

fn get_loop_blocks(
    body: &Body<'_>,
    rpo_map: &FxHashMap<BasicBlock, BId>,
) -> FxHashMap<BasicBlock, FxHashSet<BasicBlock>> {
    let dominators = body.basic_blocks.dominators();
    let loop_heads: FxHashSet<_> = body
        .basic_blocks
        .indices()
        .flat_map(|bb| {
            assert!(dominators.is_reachable(bb));
            let mut doms: Vec<_> =
                std::iter::successors(Some(bb), |&bb_| dominators.immediate_dominator(bb_))
                    .collect();
            let succs: FxHashSet<_> = body.basic_blocks.successors(bb).collect();
            doms.retain(|dom| succs.contains(dom));
            doms
        })
        .collect();
    let mut loop_heads: Vec<_> = loop_heads.into_iter().collect();
    loop_heads.sort_by_key(|bb| rpo_map[bb]);

    let succ_map: IndexVec<_, ChunkedBitSet<_>> = body
        .basic_blocks
        .indices()
        .map(|bb| {
            let mut succs = ChunkedBitSet::new_empty(body.basic_blocks.len());
            for succ in body.basic_blocks.successors(bb) {
                succs.insert(succ);
            }
            succs
        })
        .collect();
    let mut inv_map = graph_util::bitset_inverse(&succ_map);
    loop_heads
        .into_iter()
        .map(|head| {
            let reachables = graph_util::bitset_reachable_vertices(&inv_map, head);
            for succs in &mut inv_map {
                succs.remove(head);
            }
            let loop_blocks = body
                .basic_blocks
                .indices()
                .filter(|bb| dominators.dominates(head, *bb) && reachables.contains(*bb))
                .collect();
            (head, loop_blocks)
        })
        .collect()
}

fn compute_rpo_map(
    body: &Body<'_>,
    loop_blocks: &FxHashMap<BasicBlock, FxHashSet<BasicBlock>>,
) -> FxHashMap<BasicBlock, BId> {
    fn traverse(
        current: BasicBlock,
        visited: &mut FxHashSet<BasicBlock>,
        po: &mut Vec<BasicBlock>,
        body: &Body<'_>,
        loop_blocks: &FxHashMap<BasicBlock, FxHashSet<BasicBlock>>,
    ) {
        if visited.contains(&current) {
            return;
        }
        visited.insert(current);
        let loops: Vec<_> = loop_blocks
            .values()
            .filter(|blocks| blocks.contains(&current))
            .collect();
        let mut succs: Vec<_> = body.basic_blocks.successors(current).collect();
        succs.sort_by_key(|succ| loops.iter().filter(|blocks| blocks.contains(succ)).count());
        for succ in succs {
            traverse(succ, visited, po, body, loop_blocks);
        }
        po.push(current);
    }
    let mut visited = FxHashSet::default();
    let mut rpo = vec![];
    traverse(
        BasicBlock::from_usize(0),
        &mut visited,
        &mut rpo,
        body,
        loop_blocks,
    );
    rpo.reverse();
    rpo.into_iter()
        .enumerate()
        .map(|(i, bb)| (bb, BId::from_usize(i)))
        .collect()
}

fn compute_join_terminators(body: &Body<'_>) -> FxHashSet<Location> {
    let mut blocks: FxHashMap<_, FxHashSet<_>> = FxHashMap::default();
    for (block, bbd) in body.basic_blocks.iter_enumerated() {
        let loc = Location {
            block,
            statement_index: bbd.statements.len(),
        };
        for succ in bbd.terminator().successors() {
            blocks.entry(succ).or_default().insert(loc);
        }
    }
    blocks
        .into_iter()
        .filter(|(_, locs)| locs.len() > 1)
        .flat_map(|(_, locs)| locs)
        .collect()
}

fn get_dead_locals<'tcx>(body: &Body<'tcx>, tcx: TyCtxt<'tcx>) -> Vec<DenseBitSet<Local>> {
    let mut borrowed_locals = rustc_mir_dataflow::impls::borrowed_locals(body);
    borrowed_locals.insert(Local::from_usize(0));
    let mut cursor = rustc_mir_dataflow::impls::MaybeLiveLocals
        .iterate_to_fixpoint(tcx, body, None)
        .into_results_cursor(body);
    body.basic_blocks
        .indices()
        .map(|bb| {
            cursor.seek_to_block_start(bb);
            let live_locals = cursor.get();
            let mut borrowed_or_live_locals = borrowed_locals.clone();
            borrowed_or_live_locals.union(live_locals);
            let mut dead_locals = DenseBitSet::new_filled(body.local_decls.len());
            dead_locals.subtract(&borrowed_or_live_locals);
            dead_locals
        })
        .collect()
}

fn find_discriminant_values(body: &Body<'_>) -> FxHashMap<BasicBlock, DiscrVal> {
    body.basic_blocks
        .iter_enumerated()
        .filter_map(|(bb, bbd)| {
            let TerminatorKind::SwitchInt { discr, .. } = &bbd.terminator().kind else {
                return None;
            };
            let place = discr.place()?;
            let local = place.as_local()?;
            let v = bbd.statements.iter().rev().find_map(|stmt| {
                let StatementKind::Assign(box (lhs, rhs)) = &stmt.kind else { return None };
                if lhs.as_local()? != local {
                    return None;
                }
                let Rvalue::BinaryOp(op, box (lhs, rhs)) = rhs else { return None };
                let equal = match op {
                    BinOp::Eq => true,
                    BinOp::Ne => false,
                    _ => return None,
                };
                let lhs = lhs.place()?.as_local()?;
                let rhs = rhs.place()?.as_local()?;
                Some(DiscrVal { equal, lhs, rhs })
            })?;
            Some((bb, v))
        })
        .collect()
}
