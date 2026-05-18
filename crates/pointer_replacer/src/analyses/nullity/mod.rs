#![allow(dead_code)]

use points_to::andersen;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::bit_set::DenseBitSet;
use rustc_middle::{
    mir::{
        self, BasicBlock, Body, Local, Location, Operand, Place, Rvalue, Statement, StatementKind,
        Terminator, TerminatorEdges, TerminatorKind,
    },
    ty::{self, Ty, TyCtxt},
};
use rustc_mir_dataflow::{Analysis as MirDataflowAnalysis, Forward};
use rustc_span::{
    Symbol,
    def_id::{DefId, LocalDefId},
};
use utils::graph;

use crate::{
    analyses::mir::{CallGraphPostOrder, CallKind, MirFunctionCall, TerminatorExt},
    utils::rustc::RustProgram,
};

#[derive(Debug, Default)]
pub struct NullityResult {
    pub non_null_params: FxHashMap<LocalDefId, DenseBitSet<Local>>,
    pub non_null_locals: FxHashMap<LocalDefId, DenseBitSet<Local>>,
}

pub fn analyze<'tcx>(
    program: &RustProgram<'tcx>,
    points_to: &andersen::AnalysisResult,
) -> NullityResult {
    let non_null_params = analyze_non_null_params(program);
    let function_set: FxHashSet<_> = program.functions.iter().copied().collect();
    let null_write_facts = NullWriteFacts::new(program, points_to, &function_set);
    let call_graph = CallGraphPostOrder::new(program);
    let mut return_summaries = FxHashMap::default();
    return_summaries.reserve(program.functions.len());
    for &did in &program.functions {
        return_summaries.insert(
            did,
            ReturnSummary {
                may_return_null: false,
            },
        );
    }

    for scc in call_graph.sccs() {
        loop {
            let mut scc_changed = false;

            for &did in scc {
                let did = did.expect_local();
                let res = run_local_nullity(
                    program,
                    did,
                    points_to,
                    &non_null_params,
                    &return_summaries,
                    &null_write_facts,
                    &function_set,
                );
                let summary = return_summaries.get_mut(&did).unwrap();
                if res.return_may_null && !summary.may_return_null {
                    summary.may_return_null = true;
                    scc_changed = true;
                }
            }

            if !scc_changed {
                break;
            }
        }
    }

    let mut non_null_locals = FxHashMap::default();
    for &did in &program.functions {
        let res = run_local_nullity(
            program,
            did,
            points_to,
            &non_null_params,
            &return_summaries,
            &null_write_facts,
            &function_set,
        );
        if !res.non_null_locals.is_empty() {
            non_null_locals.insert(did, res.non_null_locals);
        }
    }

    NullityResult {
        non_null_params,
        non_null_locals,
    }
}

fn analyze_non_null_params(program: &RustProgram<'_>) -> FxHashMap<LocalDefId, DenseBitSet<Local>> {
    let tcx = program.tcx;
    let function_set: FxHashSet<_> = program.functions.iter().copied().collect();
    let mut summaries = FxHashMap::default();
    summaries.reserve(program.functions.len());

    for &did in &program.functions {
        let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
        summaries.insert(did, DenseBitSet::new_empty(body.local_decls.len()));
    }

    let call_graph = CallGraphPostOrder::new(program);
    loop {
        let mut changed = false;

        for scc in call_graph.sccs() {
            loop {
                let mut scc_changed = false;

                for &did in scc {
                    let did = did.expect_local();
                    let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
                    let params_to_add = raw_pointer_params(&body)
                        .into_iter()
                        .filter(|param| !summaries[&did].contains(*param))
                        .filter(|param| {
                            SingleParamAnalyzer {
                                tcx,
                                body: &body,
                                summaries: &summaries,
                                function_set: &function_set,
                                positive_memo: FxHashSet::default(),
                            }
                            .proves_non_null(*param)
                        })
                        .collect::<Vec<_>>();

                    let summary = summaries.get_mut(&did).unwrap();
                    for param in params_to_add {
                        scc_changed |= summary.insert(param);
                    }
                }

                changed |= scc_changed;
                if !scc_changed {
                    break;
                }
            }
        }

        if !changed {
            break;
        }
    }

    summaries
        .into_iter()
        .filter(|(_, params)| !params.is_empty())
        .collect()
}

fn raw_pointer_params(body: &Body<'_>) -> Vec<Local> {
    body.args_iter()
        .filter(|&local| is_raw_pointer_ty(body.local_decls[local].ty))
        .collect()
}

fn is_raw_pointer_ty(ty: Ty<'_>) -> bool {
    matches!(ty.kind(), ty::TyKind::RawPtr(..))
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct GlobalLocal {
    def_id: LocalDefId,
    local: Local,
}

#[derive(Default)]
struct NullWriteFacts {
    site_targets: FxHashMap<(LocalDefId, Location), FxHashSet<GlobalLocal>>,
    fn_effects: FxHashMap<LocalDefId, FxHashSet<GlobalLocal>>,
}

#[derive(Clone, Copy)]
struct ReturnSummary {
    may_return_null: bool,
}

struct LocalNullityOutput {
    non_null_locals: DenseBitSet<Local>,
    return_may_null: bool,
}

impl NullWriteFacts {
    fn new<'tcx>(
        program: &RustProgram<'tcx>,
        points_to: &andersen::AnalysisResult,
        function_set: &FxHashSet<LocalDefId>,
    ) -> Self {
        let tcx = program.tcx;
        let reverse_locs = reverse_pointer_local_locs(program, points_to, function_set);
        let mut site_targets = FxHashMap::default();
        let mut own_fn_effects: FxHashMap<LocalDefId, FxHashSet<GlobalLocal>> =
            FxHashMap::default();

        for &did in &program.functions {
            own_fn_effects.entry(did).or_default();
            let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
            let mut trivially_non_null = DenseBitSet::new_empty(body.local_decls.len());
            for (block, block_data) in body.basic_blocks.iter_enumerated() {
                for (statement_index, statement) in block_data.statements.iter().enumerate() {
                    let StatementKind::Assign(box (lhs, rhs)) = &statement.kind else {
                        continue;
                    };
                    if lhs.is_indirect_first_projection()
                        && is_raw_pointer_ty(lhs.ty(&body.local_decls, tcx).ty)
                        && !rvalue_is_trivially_non_null(rhs, &body, tcx, &trivially_non_null)
                    {
                        let location = Location {
                            block,
                            statement_index,
                        };
                        record_null_write_site(
                            did,
                            location,
                            points_to,
                            &reverse_locs,
                            &mut site_targets,
                            &mut own_fn_effects,
                        );
                    }

                    if let Some(local) = lhs.as_local()
                        && is_raw_pointer_ty(body.local_decls[local].ty)
                    {
                        trivially_non_null.remove(local);
                        if rvalue_is_trivially_non_null(rhs, &body, tcx, &trivially_non_null) {
                            trivially_non_null.insert(local);
                        }
                    }
                }

                let terminator = block_data.terminator();
                let Some(call) = terminator.as_call(tcx) else {
                    continue;
                };
                if !call.destination.is_indirect_first_projection()
                    || !is_raw_pointer_ty(call.destination.ty(&body.local_decls, tcx).ty)
                    || call_return_is_trivially_non_null(tcx, &call)
                {
                    continue;
                }
                let location = Location {
                    block,
                    statement_index: block_data.statements.len(),
                };
                record_null_write_site(
                    did,
                    location,
                    points_to,
                    &reverse_locs,
                    &mut site_targets,
                    &mut own_fn_effects,
                );
            }
        }

        let side_effect_graph = side_effect_call_graph(program, points_to, function_set);
        let reachables = graph::reflexive_transitive_closure(&side_effect_graph);
        let mut fn_effects = FxHashMap::default();
        for &did in &program.functions {
            let mut effects = FxHashSet::default();
            if let Some(reachable) = reachables.get(&did) {
                for callee in reachable {
                    if let Some(callee_effects) = own_fn_effects.get(callee) {
                        effects.extend(callee_effects.iter().copied());
                    }
                }
            }
            fn_effects.insert(did, effects);
        }

        Self {
            site_targets,
            fn_effects,
        }
    }
}

fn reverse_pointer_local_locs<'tcx>(
    program: &RustProgram<'tcx>,
    points_to: &andersen::AnalysisResult,
    function_set: &FxHashSet<LocalDefId>,
) -> FxHashMap<andersen::Loc, Vec<GlobalLocal>> {
    let mut reverse = FxHashMap::default();
    for (&(def_id, local), node) in &points_to.var_nodes {
        if !function_set.contains(&def_id) {
            continue;
        }
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(def_id)
            .borrow();
        if !is_raw_pointer_ty(body.local_decls[local].ty) {
            continue;
        }

        let global = GlobalLocal { def_id, local };
        let mut loc = node.index;
        let end = points_to.ends[node.index];
        loop {
            reverse.entry(loc).or_insert_with(Vec::new).push(global);
            if loc == end {
                break;
            }
            loc += 1;
        }
    }
    reverse
}

fn record_null_write_site(
    did: LocalDefId,
    location: Location,
    points_to: &andersen::AnalysisResult,
    reverse_locs: &FxHashMap<andersen::Loc, Vec<GlobalLocal>>,
    site_targets: &mut FxHashMap<(LocalDefId, Location), FxHashSet<GlobalLocal>>,
    own_fn_effects: &mut FxHashMap<LocalDefId, FxHashSet<GlobalLocal>>,
) {
    let targets = null_write_targets(did, location, points_to, reverse_locs);
    if targets.is_empty() {
        return;
    }
    own_fn_effects
        .entry(did)
        .or_default()
        .extend(targets.iter().copied());
    site_targets.insert((did, location), targets);
}

fn null_write_targets(
    did: LocalDefId,
    location: Location,
    points_to: &andersen::AnalysisResult,
    reverse_locs: &FxHashMap<andersen::Loc, Vec<GlobalLocal>>,
) -> FxHashSet<GlobalLocal> {
    let mut targets = FxHashSet::default();
    let Some(writes) = points_to
        .writes
        .get(&did)
        .and_then(|writes| writes.get(&location))
    else {
        return targets;
    };
    for loc in writes.iter() {
        if let Some(locals) = reverse_locs.get(&loc) {
            targets.extend(locals.iter().copied());
        }
    }
    targets
}

fn side_effect_call_graph<'tcx>(
    program: &RustProgram<'tcx>,
    points_to: &andersen::AnalysisResult,
    function_set: &FxHashSet<LocalDefId>,
) -> FxHashMap<LocalDefId, FxHashSet<LocalDefId>> {
    let tcx = program.tcx;
    let mut graph = program
        .functions
        .iter()
        .map(|&did| (did, FxHashSet::default()))
        .collect::<FxHashMap<_, _>>();

    for &did in &program.functions {
        let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
        for (block, block_data) in body.basic_blocks.iter_enumerated() {
            if let Some(call) = block_data.terminator().as_call(tcx) {
                match call.func {
                    CallKind::FreeStanding(callee) | CallKind::Impl(callee)
                        if function_set.contains(&callee) =>
                    {
                        graph.entry(did).or_default().insert(callee);
                    }
                    _ => {}
                }
            }

            if let Some(callees) = points_to
                .indirect_calls
                .get(&did)
                .and_then(|calls| calls.get(&block))
            {
                for &callee in callees {
                    if function_set.contains(&callee) {
                        graph.entry(did).or_default().insert(callee);
                    }
                }
            }
        }
    }

    graph
}

#[allow(clippy::too_many_arguments)]
fn run_local_nullity<'tcx>(
    program: &RustProgram<'tcx>,
    did: LocalDefId,
    points_to: &andersen::AnalysisResult,
    non_null_params: &FxHashMap<LocalDefId, DenseBitSet<Local>>,
    return_summaries: &FxHashMap<LocalDefId, ReturnSummary>,
    null_write_facts: &NullWriteFacts,
    function_set: &FxHashSet<LocalDefId>,
) -> LocalNullityOutput {
    let tcx = program.tcx;
    let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
    let mut cursor = LocalNullity {
        tcx,
        def_id: did,
        body: &body,
        function_set,
        non_null_params,
        return_summaries,
        null_write_facts,
        points_to,
    }
    .iterate_to_fixpoint(tcx, &body, None)
    .into_results_cursor(&body);

    let mut ever_nullable = DenseBitSet::new_empty(body.local_decls.len());
    let mut return_may_null = false;

    for (block, block_data) in body.basic_blocks.iter_enumerated() {
        cursor.seek_to_block_start(block);
        ever_nullable.union(cursor.get());

        for (statement_index, _) in block_data.statements.iter().enumerate() {
            let location = Location {
                block,
                statement_index,
            };
            cursor.seek_before_primary_effect(location);
            ever_nullable.union(cursor.get());
            cursor.seek_after_primary_effect(location);
            ever_nullable.union(cursor.get());
        }

        let location = Location {
            block,
            statement_index: block_data.statements.len(),
        };
        cursor.seek_before_primary_effect(location);
        ever_nullable.union(cursor.get());
        if matches!(block_data.terminator().kind, TerminatorKind::Return)
            && cursor.get().contains(Local::ZERO)
        {
            return_may_null = true;
        }
        cursor.seek_after_primary_effect(location);
        ever_nullable.union(cursor.get());
        if matches!(
            block_data.terminator().kind,
            TerminatorKind::TailCall { .. }
        ) && cursor.get().contains(Local::ZERO)
        {
            return_may_null = true;
        }
    }

    let mut non_null_locals = DenseBitSet::new_empty(body.local_decls.len());
    for (local, decl) in body.local_decls.iter_enumerated() {
        if is_raw_pointer_ty(decl.ty) {
            non_null_locals.insert(local);
        }
    }
    for local in ever_nullable.iter() {
        non_null_locals.remove(local);
    }

    LocalNullityOutput {
        non_null_locals,
        return_may_null,
    }
}

struct LocalNullity<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    body: &'a Body<'tcx>,
    function_set: &'a FxHashSet<LocalDefId>,
    non_null_params: &'a FxHashMap<LocalDefId, DenseBitSet<Local>>,
    return_summaries: &'a FxHashMap<LocalDefId, ReturnSummary>,
    null_write_facts: &'a NullWriteFacts,
    points_to: &'a andersen::AnalysisResult,
}

impl<'tcx> MirDataflowAnalysis<'tcx> for LocalNullity<'_, 'tcx> {
    type Direction = Forward;
    type Domain = DenseBitSet<Local>;

    const NAME: &'static str = "local_nullity";

    fn bottom_value(&self, body: &Body<'tcx>) -> Self::Domain {
        DenseBitSet::new_empty(body.local_decls.len())
    }

    fn initialize_start_block(&self, body: &Body<'tcx>, state: &mut Self::Domain) {
        let non_null_params = self.non_null_params.get(&self.def_id);
        for arg in body.args_iter() {
            if is_raw_pointer_ty(body.local_decls[arg].ty)
                && !non_null_params.is_some_and(|params| params.contains(arg))
            {
                state.insert(arg);
            }
        }
    }

    fn apply_primary_statement_effect(
        &mut self,
        state: &mut Self::Domain,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        let StatementKind::Assign(box (lhs, rhs)) = &statement.kind else {
            return;
        };

        if lhs.is_indirect_first_projection() {
            self.apply_site_targets(state, location);
            return;
        }

        if let Some(local) = lhs.as_local()
            && is_raw_pointer_ty(self.body.local_decls[local].ty)
        {
            state.remove(local);
            if self.rvalue_may_be_null(rhs, state) {
                state.insert(local);
            }
        } else if !lhs.projection.is_empty()
            && is_raw_pointer_ty(self.body.local_decls[lhs.local].ty)
        {
            state.insert(lhs.local);
        }
    }

    fn apply_primary_terminator_effect<'mir>(
        &mut self,
        state: &mut Self::Domain,
        terminator: &'mir Terminator<'tcx>,
        location: Location,
    ) -> TerminatorEdges<'mir, 'tcx> {
        let Some(call) = terminator.as_call(self.tcx) else {
            return terminator.edges();
        };

        let return_may_be_null = self.call_return_may_be_null(&call, state);
        for callee in self.callees_for_side_effects(&call, location.block) {
            if let Some(effects) = self.null_write_facts.fn_effects.get(&callee) {
                for target in effects {
                    if target.def_id == self.def_id {
                        state.insert(target.local);
                    }
                }
            }
        }

        if call.destination.is_indirect_first_projection() {
            self.apply_site_targets(state, location);
        } else if let Some(local) = call.destination.as_local()
            && is_raw_pointer_ty(self.body.local_decls[local].ty)
        {
            state.remove(local);
            if return_may_be_null {
                state.insert(local);
            }
        }

        terminator.edges()
    }
}

impl<'tcx> LocalNullity<'_, 'tcx> {
    fn apply_site_targets(&self, state: &mut DenseBitSet<Local>, location: Location) {
        if let Some(targets) = self
            .null_write_facts
            .site_targets
            .get(&(self.def_id, location))
        {
            for target in targets {
                if target.def_id == self.def_id {
                    state.insert(target.local);
                }
            }
        }
    }

    fn callees_for_side_effects(
        &self,
        call: &MirFunctionCall<'_, 'tcx>,
        block: BasicBlock,
    ) -> Vec<LocalDefId> {
        let mut callees = Vec::new();
        match &call.func {
            CallKind::FreeStanding(callee) | CallKind::Impl(callee)
                if self.function_set.contains(callee) =>
            {
                callees.push(*callee);
            }
            _ => {}
        }
        if let Some(indirect) = self
            .points_to
            .indirect_calls
            .get(&self.def_id)
            .and_then(|calls| calls.get(&block))
        {
            callees.extend(
                indirect
                    .iter()
                    .copied()
                    .filter(|callee| self.function_set.contains(callee)),
            );
        }
        callees
    }

    fn rvalue_may_be_null(&self, rvalue: &Rvalue<'tcx>, state: &DenseBitSet<Local>) -> bool {
        match rvalue {
            Rvalue::Use(operand) => self.operand_may_be_null(operand, state),
            Rvalue::Cast(_, operand, ty) if is_raw_pointer_ty(*ty) => {
                let operand_ty = operand.ty(&self.body.local_decls, self.tcx);
                if is_raw_pointer_ty(operand_ty) || matches!(operand_ty.kind(), ty::TyKind::Ref(..))
                {
                    self.operand_may_be_null(operand, state)
                } else {
                    true
                }
            }
            Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                !place_address_is_non_null(place, self.body)
            }
            Rvalue::ThreadLocalRef(_) => false,
            Rvalue::CopyForDeref(place) => {
                if place.projection.is_empty() {
                    state.contains(place.local)
                } else {
                    true
                }
            }
            _ => true,
        }
    }

    fn operand_may_be_null(&self, operand: &Operand<'tcx>, state: &DenseBitSet<Local>) -> bool {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                if place.projection.is_empty() {
                    state.contains(place.local)
                } else {
                    true
                }
            }
            Operand::Constant(_) => true,
        }
    }

    fn call_return_may_be_null(
        &self,
        call: &MirFunctionCall<'_, 'tcx>,
        state: &DenseBitSet<Local>,
    ) -> bool {
        match &call.func {
            CallKind::FreeStanding(callee) if self.function_set.contains(callee) => self
                .return_summaries
                .get(callee)
                .is_none_or(|summary| summary.may_return_null),
            CallKind::Impl(callee) if self.function_set.contains(callee) => self
                .return_summaries
                .get(callee)
                .is_none_or(|summary| summary.may_return_null),
            CallKind::LibC(name) => match name.as_str() {
                "malloc" | "calloc" => false,
                "realloc" => call
                    .args
                    .first()
                    .is_none_or(|arg| !operand_is_trivially_null(&arg.node, self.tcx)),
                _ => true,
            },
            CallKind::RustLib(def_id) if is_raw_pointer_null_constructor(self.tcx, *def_id) => true,
            CallKind::FreeStanding(_)
            | CallKind::RustLib(_)
            | CallKind::Impl(_)
            | CallKind::Closure
            | CallKind::Dynamic => {
                let _ = state;
                true
            }
        }
    }
}

fn rvalue_is_trivially_non_null<'tcx>(
    rvalue: &Rvalue<'tcx>,
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    trivially_non_null: &DenseBitSet<Local>,
) -> bool {
    match rvalue {
        Rvalue::Use(operand) => operand_is_trivially_non_null(operand, trivially_non_null),
        Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
            place_address_is_non_null(place, body)
        }
        Rvalue::ThreadLocalRef(_) => true,
        Rvalue::Cast(_, operand, ty) if is_raw_pointer_ty(*ty) => {
            let operand_ty = operand.ty(&body.local_decls, tcx);
            (is_raw_pointer_ty(operand_ty) || matches!(operand_ty.kind(), ty::TyKind::Ref(..)))
                && operand_is_trivially_non_null(operand, trivially_non_null)
        }
        _ => false,
    }
}

fn operand_is_trivially_non_null(
    operand: &Operand<'_>,
    trivially_non_null: &DenseBitSet<Local>,
) -> bool {
    matches!(
        operand,
        Operand::Copy(place) | Operand::Move(place)
            if place.projection.is_empty() && trivially_non_null.contains(place.local)
    )
}

fn place_address_is_non_null(place: &Place<'_>, body: &Body<'_>) -> bool {
    if !place_has_deref(place) {
        return true;
    }
    matches!(body.local_decls[place.local].ty.kind(), ty::TyKind::Ref(..))
        && place
            .projection
            .iter()
            .filter(|elem| matches!(elem, mir::ProjectionElem::Deref))
            .count()
            == 1
}

fn call_return_is_trivially_non_null(tcx: TyCtxt<'_>, call: &MirFunctionCall<'_, '_>) -> bool {
    match &call.func {
        CallKind::LibC(name) => match name.as_str() {
            "malloc" | "calloc" => true,
            "realloc" => call
                .args
                .first()
                .is_some_and(|arg| operand_is_trivially_null(&arg.node, tcx)),
            _ => false,
        },
        _ => false,
    }
}

fn operand_is_trivially_null(operand: &Operand<'_>, tcx: TyCtxt<'_>) -> bool {
    let Operand::Constant(constant) = operand else {
        return false;
    };
    const_is_zero(&constant.const_, tcx)
}

fn const_is_zero(value: &mir::Const<'_>, tcx: TyCtxt<'_>) -> bool {
    if let Some(scalar) = value.try_to_scalar()
        && let Ok(int) = scalar.try_to_scalar_int()
    {
        return int.to_bits(int.size()) == 0;
    }
    if let mir::Const::Unevaluated(unevaluated, _) = value
        && unevaluated.promoted.is_none()
        && let Ok(mir::ConstValue::Scalar(scalar)) = tcx.const_eval_poly(unevaluated.def)
        && let Ok(int) = scalar.try_to_scalar_int()
    {
        return int.to_bits(int.size()) == 0;
    }
    false
}

fn is_raw_pointer_null_constructor(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    matches!(tcx.item_name(def_id).as_str(), "null" | "null_mut")
}

struct SingleParamAnalyzer<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    summaries: &'a FxHashMap<LocalDefId, DenseBitSet<Local>>,
    function_set: &'a FxHashSet<LocalDefId>,
    positive_memo: FxHashSet<TraversalKey>,
}

impl<'a, 'tcx> SingleParamAnalyzer<'a, 'tcx> {
    fn proves_non_null(mut self, param: Local) -> bool {
        self.prove_from(
            Location::START,
            Aliases::new(param),
            &mut FxHashSet::default(),
        )
    }

    fn prove_from(
        &mut self,
        location: Location,
        aliases: Aliases,
        path: &mut FxHashSet<TraversalKey>,
    ) -> bool {
        let key = TraversalKey::new(location, &aliases);
        if self.positive_memo.contains(&key) {
            return true;
        }
        if !path.insert(key.clone()) {
            return false;
        }

        let proved = self.prove_from_uncached(location, aliases, path);

        path.remove(&key);
        if proved {
            self.positive_memo.insert(key);
        }
        proved
    }

    fn prove_from_uncached(
        &mut self,
        location: Location,
        aliases: Aliases,
        path: &mut FxHashSet<TraversalKey>,
    ) -> bool {
        let block = &self.body.basic_blocks[location.block];
        if location.statement_index < block.statements.len() {
            return match self
                .transfer_statement(&block.statements[location.statement_index], aliases)
            {
                Step::Proof => true,
                Step::Barrier => false,
                Step::Continue(aliases) => {
                    self.prove_from(location.successor_within_block(), aliases, path)
                }
            };
        }

        self.transfer_terminator(block.terminator(), aliases, path)
    }

    fn transfer_statement(&self, statement: &Statement<'tcx>, mut aliases: Aliases) -> Step {
        let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind else {
            return Step::Continue(aliases);
        };

        if place_derefs_alias(lhs, &aliases) || rvalue_derefs_alias(rvalue, &aliases) {
            return Step::Proof;
        }

        if rvalue_takes_alias_address(rvalue, &aliases) {
            return Step::Barrier;
        }

        let rhs_direct_alias = rvalue_direct_alias_source(rvalue, &aliases)
            && is_raw_pointer_ty(self.body.local_decls[lhs.local].ty);
        let rhs_contains_alias = rvalue_contains_alias_value(rvalue, &aliases);

        if lhs.projection.is_empty() {
            if rhs_direct_alias {
                aliases.insert(lhs.local);
                return Step::Continue(aliases);
            }

            if aliases.contains(lhs.local) || rhs_contains_alias {
                return Step::Barrier;
            }
        } else if rhs_direct_alias || rhs_contains_alias {
            return Step::Barrier;
        }

        Step::Continue(aliases)
    }

    fn transfer_terminator(
        &mut self,
        terminator: &Terminator<'tcx>,
        aliases: Aliases,
        path: &mut FxHashSet<TraversalKey>,
    ) -> bool {
        if let Some(call) = terminator.as_call(self.tcx) {
            return self.transfer_call(terminator, call, aliases, path);
        }

        if terminator_derefs_alias(terminator, &aliases) {
            return true;
        }

        self.prove_successors(terminator.successors(), aliases, path)
    }

    fn transfer_call(
        &mut self,
        terminator: &Terminator<'tcx>,
        call: MirFunctionCall<'_, 'tcx>,
        aliases: Aliases,
        path: &mut FxHashSet<TraversalKey>,
    ) -> bool {
        let mut alias_arg_indices = vec![];

        for (idx, arg) in call.args.iter().enumerate() {
            if operand_derefs_alias(&arg.node, &aliases) {
                return true;
            }
            if operand_contains_alias_value(&arg.node, &aliases) {
                alias_arg_indices.push(idx);
            }
        }

        if place_derefs_alias(&call.destination, &aliases) {
            return true;
        }

        if !alias_arg_indices.is_empty() {
            return self.call_requires_non_null(&call.func, &alias_arg_indices);
        }

        if call.destination.projection.is_empty() && aliases.contains(call.destination.local) {
            return false;
        }

        self.prove_successors(terminator.successors(), aliases, path)
    }

    fn call_requires_non_null(&self, func: &CallKind, alias_arg_indices: &[usize]) -> bool {
        match func {
            CallKind::FreeStanding(callee) if self.function_set.contains(callee) => {
                let Some(summary) = self.summaries.get(callee) else {
                    return false;
                };
                alias_arg_indices
                    .iter()
                    .all(|idx| summary.contains(Local::from_usize(idx + 1)))
            }
            CallKind::LibC(name) => libc_requires_non_null(*name, alias_arg_indices),
            CallKind::RustLib(def_id) if is_raw_pointer_is_null(self.tcx, *def_id) => false,
            CallKind::FreeStanding(_)
            | CallKind::RustLib(_)
            | CallKind::Impl(_)
            | CallKind::Closure
            | CallKind::Dynamic => false,
        }
    }

    fn prove_successors(
        &mut self,
        successors: impl Iterator<Item = BasicBlock>,
        aliases: Aliases,
        path: &mut FxHashSet<TraversalKey>,
    ) -> bool {
        let successors = successors.collect::<Vec<_>>();
        if successors.is_empty() {
            return false;
        }

        successors.into_iter().all(|block| {
            self.prove_from(
                Location {
                    block,
                    statement_index: 0,
                },
                aliases.clone(),
                path,
            )
        })
    }
}

enum Step {
    Proof,
    Barrier,
    Continue(Aliases),
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Aliases(Vec<Local>);

impl Aliases {
    fn new(local: Local) -> Self {
        Self(vec![local])
    }

    fn contains(&self, local: Local) -> bool {
        self.0
            .binary_search_by_key(&local.index(), |local| local.index())
            .is_ok()
    }

    fn insert(&mut self, local: Local) {
        match self
            .0
            .binary_search_by_key(&local.index(), |local| local.index())
        {
            Ok(_) => {}
            Err(idx) => self.0.insert(idx, local),
        }
    }

    fn key(&self) -> Vec<usize> {
        self.0.iter().map(|local| local.index()).collect()
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct TraversalKey {
    block: usize,
    statement_index: usize,
    aliases: Vec<usize>,
}

impl TraversalKey {
    fn new(location: Location, aliases: &Aliases) -> Self {
        Self {
            block: location.block.as_usize(),
            statement_index: location.statement_index,
            aliases: aliases.key(),
        }
    }
}

fn libc_requires_non_null(name: Symbol, alias_arg_indices: &[usize]) -> bool {
    let non_null_args: &[usize] = match name.as_str() {
        "strlen" | "strchr" | "strrchr" | "atoi" | "atol" | "atof" | "puts" => &[0],
        "strcmp" | "strcasecmp" | "strcpy" | "strcat" | "strstr" => &[0, 1],
        "fputs" => &[0],
        _ => return false,
    };

    alias_arg_indices
        .iter()
        .all(|idx| non_null_args.contains(idx))
}

fn is_raw_pointer_is_null(tcx: TyCtxt<'_>, def_id: rustc_span::def_id::DefId) -> bool {
    let name = tcx.def_path(def_id).to_string_no_crate_verbose();
    let mut segs = name.rsplit("::");
    matches!(segs.next(), Some("is_null"))
        && segs.next().is_some()
        && matches!(segs.next(), Some("mut_ptr" | "const_ptr"))
        && matches!(segs.next(), Some("ptr"))
}

fn terminator_derefs_alias(terminator: &Terminator<'_>, aliases: &Aliases) -> bool {
    match &terminator.kind {
        TerminatorKind::SwitchInt { discr, .. } | TerminatorKind::Assert { cond: discr, .. } => {
            operand_derefs_alias(discr, aliases)
        }
        TerminatorKind::Drop { place, .. } => place_derefs_alias(place, aliases),
        TerminatorKind::Yield { value, .. } => operand_derefs_alias(value, aliases),
        _ => false,
    }
}

fn rvalue_direct_alias_source(rvalue: &Rvalue<'_>, aliases: &Aliases) -> bool {
    match rvalue {
        Rvalue::Use(operand) => operand_plain_alias(operand, aliases),
        Rvalue::Cast(_, operand, ty) if is_raw_pointer_ty(*ty) => {
            operand_plain_alias(operand, aliases)
        }
        _ => false,
    }
}

fn rvalue_takes_alias_address(rvalue: &Rvalue<'_>, aliases: &Aliases) -> bool {
    matches!(
        rvalue,
        Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place)
            if aliases.contains(place.local) && !place_has_deref(place)
    )
}

fn rvalue_derefs_alias(rvalue: &Rvalue<'_>, aliases: &Aliases) -> bool {
    match rvalue {
        Rvalue::Use(operand)
        | Rvalue::Repeat(operand, _)
        | Rvalue::UnaryOp(_, operand)
        | Rvalue::Cast(_, operand, _) => operand_derefs_alias(operand, aliases),
        Rvalue::BinaryOp(_, box (lhs, rhs)) => {
            operand_derefs_alias(lhs, aliases) || operand_derefs_alias(rhs, aliases)
        }
        Rvalue::Ref(_, _, place)
        | Rvalue::RawPtr(_, place)
        | Rvalue::Len(place)
        | Rvalue::Discriminant(place) => place_derefs_alias(place, aliases),
        Rvalue::CopyForDeref(place) => aliases.contains(place.local),
        Rvalue::Aggregate(_, operands) => operands
            .iter()
            .any(|operand| operand_derefs_alias(operand, aliases)),
        _ => false,
    }
}

fn rvalue_contains_alias_value(rvalue: &Rvalue<'_>, aliases: &Aliases) -> bool {
    match rvalue {
        Rvalue::Use(operand)
        | Rvalue::Repeat(operand, _)
        | Rvalue::UnaryOp(_, operand)
        | Rvalue::Cast(_, operand, _) => operand_contains_alias_value(operand, aliases),
        Rvalue::BinaryOp(_, box (lhs, rhs)) => {
            operand_contains_alias_value(lhs, aliases) || operand_contains_alias_value(rhs, aliases)
        }
        Rvalue::Aggregate(_, operands) => operands
            .iter()
            .any(|operand| operand_contains_alias_value(operand, aliases)),
        _ => false,
    }
}

fn operand_plain_alias(operand: &Operand<'_>, aliases: &Aliases) -> bool {
    matches!(
        operand,
        Operand::Copy(place) | Operand::Move(place)
            if place.projection.is_empty() && aliases.contains(place.local)
    )
}

fn operand_derefs_alias(operand: &Operand<'_>, aliases: &Aliases) -> bool {
    matches!(
        operand,
        Operand::Copy(place) | Operand::Move(place) if place_derefs_alias(place, aliases)
    )
}

fn operand_contains_alias_value(operand: &Operand<'_>, aliases: &Aliases) -> bool {
    matches!(
        operand,
        Operand::Copy(place) | Operand::Move(place)
            if aliases.contains(place.local) && !place_has_deref(place)
    )
}

fn place_derefs_alias(place: &Place<'_>, aliases: &Aliases) -> bool {
    aliases.contains(place.local) && place_has_deref(place)
}

fn place_has_deref(place: &Place<'_>) -> bool {
    place
        .projection
        .iter()
        .any(|elem| matches!(elem, mir::ProjectionElem::Deref))
}

#[cfg(test)]
mod tests;
