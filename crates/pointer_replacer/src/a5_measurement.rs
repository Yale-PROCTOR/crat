use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
    time::{Duration, Instant},
};

use points_to::andersen::{self, Var};
use rustc_hash::FxHashSet;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    mir::{BasicBlock, Body, Local, Operand, TerminatorKind},
    ty::TyCtxt,
};
use rustc_type_ir::TyKind;

use crate::{
    analyses::{
        borrow::lifetime_flow::{self, BodyLifetimeFlow},
        borrow_ownership::{
            CrateCtxt, SlotKind,
            borrow_verify::verify_to_fixpoint,
            coherence::add_coherence,
            crate_slots::CrateSlots,
            emit_crate_ownership_constraints,
            export::with_bo_export,
            mutability_facts::MutFacts,
            origins::compute_origins,
            solver::{KindSolver, SlotRef},
        },
    },
    coverage_recon::schema::Outcome,
    utils::rustc::RustProgram,
};

#[path = "analyses/borrow/places_conflict.rs"]
#[allow(dead_code)]
mod projection_conflict;

use projection_conflict::{AccessDepth, PlaceConflictBias, places_conflict};

const COUNT_SENTINEL: &str = "A5P1 ";
const BASE_SENTINEL: &str = "A5P1BASE ";

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct FormalKey {
    function: String,
    parameter: u32,
    depth: u8,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct FormalDecision {
    settles_ref: bool,
    currently_predicted_refs: BTreeSet<FormalKey>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ArtifactFormal {
    settles_ref: bool,
    currently_predicted_ref: bool,
    ptr_depth: u8,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct CoverageCounts {
    calls_total: usize,
    direct_local: usize,
    indirect_local: usize,
    direct_external: usize,
    indirect_unresolved: usize,
    non_fn_def_constant: usize,
}

impl CoverageCounts {
    fn validate(&self) -> Result<(), String> {
        let classified = self.direct_local
            + self.indirect_local
            + self.direct_external
            + self.indirect_unresolved
            + self.non_fn_def_constant;
        if classified != self.calls_total {
            return Err(format!(
                "call coverage mismatch: total={} classified={classified}",
                self.calls_total
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Default)]
struct Timings {
    origins: Duration,
    andersen: Duration,
    accepted_model: Duration,
}

#[derive(Clone, Debug)]
struct Measurement {
    counts: ProgramCounts,
    coverage: CoverageCounts,
    timings: Timings,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
enum SetPairEvidence {
    #[default]
    Unknown,
    Complete {
        left: BTreeSet<String>,
        right: BTreeSet<String>,
    },
    Incomplete {
        left: BTreeSet<String>,
        right: BTreeSet<String>,
    },
}

impl SetPairEvidence {
    fn proves_disjoint(&self) -> bool {
        let Self::Complete { left, right } = self else {
            return false;
        };
        !left.is_empty() && !right.is_empty() && left.is_disjoint(right)
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct PairFacts {
    storage_alias: bool,
    projection_disjoint: bool,
    origins: SetPairEvidence,
    points_to: SetPairEvidence,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PairClass {
    ProvenDisjoint,
    NotProvenDisjoint,
}

fn classify_pair(facts: &PairFacts) -> PairClass {
    if facts.storage_alias {
        return PairClass::NotProvenDisjoint;
    }
    if facts.projection_disjoint
        || facts.origins.proves_disjoint()
        || facts.points_to.proves_disjoint()
    {
        PairClass::ProvenDisjoint
    } else {
        PairClass::NotProvenDisjoint
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CallSite {
    id: String,
    arguments: Vec<FormalDecision>,
    pair_facts: BTreeMap<(usize, usize), PairFacts>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct FunctionNode {
    unknown_caller_root: bool,
    callees: BTreeSet<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ProgramInput {
    name: String,
    call_sites: Vec<CallSite>,
    functions: BTreeMap<String, FunctionNode>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ProgramCounts {
    program: String,
    sites_with_two_ref_args: usize,
    sites_not_proven_disjoint: usize,
    attributed_predicted_refs: usize,
    attributed_predicted_refs_depth0: usize,
    unknown_caller_reachable: usize,
    local_functions: usize,
}

impl ProgramCounts {
    fn validate(&self) -> Result<(), String> {
        if self.program.is_empty() || self.program.chars().any(char::is_whitespace) {
            return Err("program must be a non-empty whitespace-free key".to_owned());
        }
        if self.sites_not_proven_disjoint > self.sites_with_two_ref_args {
            return Err("count 2 exceeds count 1".to_owned());
        }
        if self.attributed_predicted_refs_depth0 > self.attributed_predicted_refs {
            return Err("depth-0 count exceeds the all-depth count".to_owned());
        }
        if self.unknown_caller_reachable > self.local_functions {
            return Err("call-graph numerator exceeds its denominator".to_owned());
        }
        Ok(())
    }
}

fn measure_program(input: &ProgramInput) -> Result<ProgramCounts, String> {
    let mut site_ids = BTreeSet::new();
    let mut sites_with_two_ref_args = 0usize;
    let mut sites_not_proven_disjoint = 0usize;
    let mut attributed = BTreeSet::new();

    for site in &input.call_sites {
        if !site_ids.insert(site.id.as_str()) {
            return Err(format!("duplicate call-site id `{}`", site.id));
        }
        let ref_args = site
            .arguments
            .iter()
            .enumerate()
            .filter_map(|(index, formal)| formal.settles_ref.then_some(index))
            .collect::<Vec<_>>();
        if ref_args.len() < 2 {
            continue;
        }
        sites_with_two_ref_args += 1;

        let mut risky = false;
        for (offset, &left) in ref_args.iter().enumerate() {
            for &right in &ref_args[offset + 1..] {
                let facts = site
                    .pair_facts
                    .get(&(left, right))
                    .cloned()
                    .unwrap_or_default();
                if classify_pair(&facts) == PairClass::NotProvenDisjoint {
                    risky = true;
                    for index in [left, right] {
                        let formal = &site.arguments[index];
                        attributed.extend(formal.currently_predicted_refs.iter().cloned());
                    }
                }
            }
        }
        sites_not_proven_disjoint += usize::from(risky);
    }

    let reachable = unknown_reachable(&input.functions)?;

    let counts = ProgramCounts {
        program: input.name.clone(),
        sites_with_two_ref_args,
        sites_not_proven_disjoint,
        attributed_predicted_refs: attributed.len(),
        attributed_predicted_refs_depth0: attributed.iter().filter(|key| key.depth == 0).count(),
        unknown_caller_reachable: reachable.len(),
        local_functions: input.functions.len(),
    };
    counts.validate()?;
    Ok(counts)
}

fn unknown_reachable(
    functions: &BTreeMap<String, FunctionNode>,
) -> Result<BTreeSet<String>, String> {
    let mut reachable = BTreeSet::new();
    let mut pending = functions
        .iter()
        .filter_map(|(name, node)| node.unknown_caller_root.then_some(name.clone()))
        .collect::<Vec<_>>();
    while let Some(function) = pending.pop() {
        if !reachable.insert(function.clone()) {
            continue;
        }
        let Some(node) = functions.get(&function) else {
            return Err(format!(
                "call graph references unknown local function `{function}`"
            ));
        };
        for callee in &node.callees {
            if !functions.contains_key(callee) {
                return Err(format!(
                    "call graph references unknown local callee `{callee}`"
                ));
            }
            pending.push(callee.clone());
        }
    }
    Ok(reachable)
}

fn parse_formals(
    a_text: &str,
    b_text: &str,
    facts_text: &str,
) -> Result<BTreeMap<(String, u32), ArtifactFormal>, String> {
    let a = crate::coverage_recon::schema::decode(a_text)
        .map_err(|why| format!("producer A: {why}"))?;
    let b = crate::coverage_recon::schema::decode(b_text)
        .map_err(|why| format!("producer B: {why}"))?;
    let verdict = crate::coverage_recon::compare::compare(&a, &b);
    if !verdict.passed() {
        return Err(format!(
            "reconciliation failed: {} violation(s), {} finding(s)",
            verdict.violations.len(),
            verdict.findings.len()
        ));
    }

    const FACTS_HEADER: &str = "fn_path\tmir_local\tis_param\tannotated\tslot\tkind\traw_op\tptr_cmp\tctor\tlen_class\tsize_expr";
    let mut lines = facts_text.lines();
    if lines.next() != Some(FACTS_HEADER) {
        return Err("facts join header does not match the registered schema".to_owned());
    }
    let mut facts = BTreeMap::new();
    for (offset, line) in lines.enumerate() {
        let columns = line.split('\t').collect::<Vec<_>>();
        if columns.len() != 11 {
            return Err(format!(
                "facts line {} has {} columns, expected 11",
                offset + 2,
                columns.len()
            ));
        }
        if !matches!(columns[2], "0" | "1")
            || !matches!(columns[3], "0" | "1")
            || !matches!(columns[4], "0" | "1")
            || !matches!(columns[5], "ref" | "raw" | "owning" | "-")
        {
            return Err(format!(
                "facts line {} contains an invalid enum",
                offset + 2
            ));
        }
        let mir_local = columns[1]
            .parse::<u32>()
            .map_err(|why| format!("facts line {} mir_local: {why}", offset + 2))?;
        let key = (columns[0].to_owned(), mir_local);
        if facts
            .insert(key.clone(), (columns[2] == "1", columns[5]))
            .is_some()
        {
            return Err(format!("duplicate facts identity {}#{}", key.0, key.1));
        }
    }

    let a_keys = a
        .iter()
        .map(|row| (row.fn_path.clone(), row.mir_local))
        .collect::<BTreeSet<_>>();
    let fact_keys = facts.keys().cloned().collect::<BTreeSet<_>>();
    if a_keys.len() != a.len() {
        return Err("producer A contains a duplicate subject identity".to_owned());
    }
    if a_keys != fact_keys {
        return Err(format!(
            "facts/A population mismatch: A={} facts={}",
            a_keys.len(),
            fact_keys.len()
        ));
    }

    let mut formals = BTreeMap::new();
    for row in &a {
        let Some(parameter) = row.arg_index else {
            continue;
        };
        let key = (row.fn_path.clone(), row.mir_local);
        let &(is_param, kind) = facts
            .get(&key)
            .ok_or_else(|| format!("missing facts row {}#{}", key.0, key.1))?;
        if !is_param {
            return Err(format!(
                "artifact parameter {}#{} is not a facts parameter",
                key.0, key.1
            ));
        }
        let formal_key = (row.fn_path.clone(), parameter);
        let formal = ArtifactFormal {
            settles_ref: kind == "ref",
            currently_predicted_ref: matches!(
                row.outcome,
                Some(Outcome::RefMut | Outcome::RefShared)
            ),
            ptr_depth: row.ptr_depth,
        };
        if formals.insert(formal_key.clone(), formal).is_some() {
            return Err(format!(
                "duplicate formal identity {}#arg{}",
                formal_key.0, formal_key.1
            ));
        }
    }
    Ok(formals)
}

fn snapshot_formals(
    snapshot: &Path,
    program: &str,
) -> Result<BTreeMap<(String, u32), ArtifactFormal>, String> {
    let read = |suffix: &str| {
        let path = snapshot.join(format!("{program}.{suffix}"));
        fs::read_to_string(&path).map_err(|why| format!("read {}: {why}", path.display()))
    };
    parse_formals(&read("a.jsonl")?, &read("b.jsonl")?, &read("facts.tsv")?)
}

fn unknown_caller_roots(tcx: TyCtxt<'_>, functions: &[LocalDefId]) -> FxHashSet<LocalDefId> {
    let program = super::collect_program(tcx);
    let fn_ptrs = crate::rewriter::collector::collect_fn_ptrs(&program);
    functions
        .iter()
        .copied()
        .filter(|did| tcx.visibility(did.to_def_id()).is_public() || fn_ptrs.contains(did))
        .collect()
}

fn indirect_targets(
    pre: &andersen::PreAnalysisData<'_>,
    solutions: &andersen::Solutions,
    caller: LocalDefId,
    block: BasicBlock,
) -> Result<Vec<LocalDefId>, String> {
    let location = pre
        .indirect_calls
        .get(&caller)
        .and_then(|calls| calls.get(&block))
        .ok_or_else(|| format!("missing Andersen indirect-call site {caller:?}/{block:?}"))?;
    let mut targets = solutions[*location]
        .iter()
        .filter_map(|location| pre.inv_fns.get(&location).copied())
        .collect::<Vec<_>>();
    targets.sort_unstable_by_key(|did| did.local_def_index.as_u32());
    targets.dedup();
    Ok(targets)
}

fn operand_points(
    pre: &andersen::PreAnalysisData<'_>,
    solutions: &andersen::Solutions,
    unknown_locations: &BTreeSet<usize>,
    caller: LocalDefId,
    operand: &Operand<'_>,
) -> Option<(BTreeSet<String>, bool)> {
    let place = operand.place()?;
    if !place.projection.is_empty() {
        return None;
    }
    let location = *pre.vars.get(&Var::Local(caller, place.local))?;
    let points = solutions[location]
        .iter()
        .map(|target| target.index())
        .collect::<BTreeSet<_>>();
    let complete = points.is_disjoint(unknown_locations);
    Some((
        points.into_iter().map(|index| index.to_string()).collect(),
        complete,
    ))
}

fn origin_points(
    body: &Body<'_>,
    flow: &BodyLifetimeFlow,
    caller_reachable_from_unknown: bool,
    operand: &Operand<'_>,
) -> Option<(
    rustc_index::bit_set::DenseBitSet<lifetime_flow::LifetimeSlot>,
    bool,
)> {
    let place = operand.place()?;
    if !place.projection.is_empty() {
        return None;
    }
    let target = flow.slot_for_local(place.local, 0)?;
    let mut origins = rustc_index::bit_set::DenseBitSet::new_empty(flow.slots.len());
    for (source, _) in flow.slots.iter_enumerated() {
        if source == target || flow.value_flows.contains(source, target) {
            origins.insert(source);
        }
    }
    let mut complete = !flow.unknown_targets.contains(target);
    if caller_reachable_from_unknown {
        for argument in body.args_iter() {
            let Some(source) = flow.slot_for_local(argument, 0) else {
                continue;
            };
            if source == target || flow.value_flows.contains(source, target) {
                complete = false;
                break;
            }
        }
    }
    Some((origins, complete))
}

fn origin_pair_facts<'tcx>(
    body: &Body<'tcx>,
    flow: &BodyLifetimeFlow,
    caller_reachable_from_unknown: bool,
    left: &Operand<'tcx>,
    right: &Operand<'tcx>,
) -> (bool, SetPairEvidence) {
    let left_place = left.place();
    let right_place = right.place();
    let storage_alias = match (left_place, right_place) {
        (Some(left), Some(right)) if left == right => true,
        (Some(left), Some(right)) if left.projection.is_empty() && right.projection.is_empty() => {
            match (
                flow.slot_for_local(left.local, 0),
                flow.slot_for_local(right.local, 0),
            ) {
                (Some(left), Some(right)) => flow.storage_aliases.contains(left, right),
                _ => false,
            }
        }
        _ => false,
    };
    let evidence = match (
        origin_points(body, flow, caller_reachable_from_unknown, left),
        origin_points(body, flow, caller_reachable_from_unknown, right),
    ) {
        (Some((left, left_complete)), Some((right, right_complete))) => {
            let left = left
                .iter()
                .map(|slot| slot.index().to_string())
                .collect::<BTreeSet<_>>();
            let right = right
                .iter()
                .map(|slot| slot.index().to_string())
                .collect::<BTreeSet<_>>();
            if left_complete && right_complete {
                SetPairEvidence::Complete { left, right }
            } else {
                SetPairEvidence::Incomplete { left, right }
            }
        }
        _ => SetPairEvidence::Unknown,
    };
    (storage_alias, evidence)
}

fn call_pair_facts<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    pre: &andersen::PreAnalysisData<'tcx>,
    solutions: &andersen::Solutions,
    unknown_locations: &BTreeSet<usize>,
    flow: &BodyLifetimeFlow,
    caller_reachable_from_unknown: bool,
    caller: LocalDefId,
    left: &Operand<'tcx>,
    right: &Operand<'tcx>,
) -> PairFacts {
    let left_place = left.place();
    let right_place = right.place();
    let (storage_alias, origins) =
        origin_pair_facts(body, flow, caller_reachable_from_unknown, left, right);
    let projection_disjoint = matches!((left_place, right_place), (Some(left), Some(right))
    if left.local == right.local
        && !places_conflict(
            tcx,
            body,
            left,
            right,
            AccessDepth::Deep,
            PlaceConflictBias::Overlap,
        ));
    let points_to = match (
        operand_points(pre, solutions, unknown_locations, caller, left),
        operand_points(pre, solutions, unknown_locations, caller, right),
    ) {
        (Some((left, left_complete)), Some((right, right_complete)))
            if left_complete && right_complete =>
        {
            SetPairEvidence::Complete { left, right }
        }
        (Some((left, _)), Some((right, _))) => SetPairEvidence::Incomplete { left, right },
        _ => SetPairEvidence::Unknown,
    };
    PairFacts {
        storage_alias,
        projection_disjoint,
        origins,
        points_to,
    }
}

fn formal_for_argument(
    tcx: TyCtxt<'_>,
    targets: &[LocalDefId],
    parameter: usize,
    formals: &BTreeMap<(String, u32), ArtifactFormal>,
    deep_refs: &BTreeMap<(String, u32), BTreeSet<FormalKey>>,
) -> Result<FormalDecision, String> {
    let mut settles_ref = true;
    let mut currently_predicted_refs = BTreeSet::new();
    for &target in targets {
        let body = tcx.mir_drops_elaborated_and_const_checked(target).borrow();
        if parameter >= body.arg_count {
            return Err(format!(
                "call argument {} exceeds target {} arity {}",
                parameter + 1,
                tcx.def_path_str(target.to_def_id()),
                body.arg_count
            ));
        }
        let local = rustc_middle::mir::Local::from_usize(parameter + 1);
        let path = tcx.def_path_str(target.to_def_id());
        let key = (path.clone(), parameter as u32 + 1);
        let Some(formal) = formals.get(&key) else {
            if body.local_decls[local].ty.is_raw_ptr() {
                return Err(format!(
                    "pointer formal {}#arg{} has no artifact row",
                    path,
                    parameter + 1
                ));
            }
            settles_ref = false;
            continue;
        };
        settles_ref &= formal.settles_ref;
        if formal.currently_predicted_ref {
            currently_predicted_refs.insert(FormalKey {
                function: path.clone(),
                parameter: parameter as u32 + 1,
                depth: 0,
            });
        }
        if let Some(deeper) = deep_refs.get(&key) {
            currently_predicted_refs.extend(deeper.iter().cloned());
        }
    }
    if !settles_ref {
        currently_predicted_refs.clear();
    }
    Ok(FormalDecision {
        settles_ref,
        currently_predicted_refs,
    })
}

fn accepted_deep_refs(
    tcx: TyCtxt<'_>,
    program: &RustProgram<'_>,
    formals: &BTreeMap<(String, u32), ArtifactFormal>,
) -> Result<BTreeMap<(String, u32), BTreeSet<FormalKey>>, String> {
    let slots = CrateSlots::build(program);
    let mutable = MutFacts::from_program(program);
    let (model, _export) = with_bo_export(|| {
        let crate_ctxt = CrateCtxt::new(program);
        let solver = KindSolver::new(&slots);
        let Ok((_stats, selectors)) = emit_crate_ownership_constraints(
            &crate_ctxt,
            &slots,
            &compute_origins(program),
            &solver,
        ) else {
            return None;
        };
        for &function in &program.functions {
            let body = tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            add_coherence(&solver, &slots, function, &body);
        }
        verify_to_fixpoint(program, &slots, &solver, &selectors, &mutable)
    });
    let model = model.ok_or_else(|| "targeted accepted-model export declined".to_owned())?;

    let mut refs = BTreeMap::new();
    for &function in &program.functions {
        let path = tcx.def_path_str(function.to_def_id());
        let body = tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        let universe = slots
            .fn_local_slots
            .get(&function)
            .ok_or_else(|| format!("accepted model lacks slot universe for {path}"))?;
        for parameter in 0..body.arg_count {
            let key = (path.clone(), parameter as u32 + 1);
            let Some(formal) = formals.get(&key) else {
                continue;
            };
            let local = Local::from_usize(parameter + 1);
            let mut deeper = BTreeSet::new();
            for depth in 1..formal.ptr_depth {
                let slot = universe.slot_for_local_depth(local, depth).ok_or_else(|| {
                    format!("accepted model lacks {path}#arg{}@{depth}", parameter + 1)
                })?;
                if model.get(&SlotRef::Local(function, slot)) == Some(&SlotKind::Ref) {
                    deeper.insert(FormalKey {
                        function: path.clone(),
                        parameter: parameter as u32 + 1,
                        depth,
                    });
                }
            }
            refs.insert(key, deeper);
        }
    }
    Ok(refs)
}

fn measure_tcx(
    program_name: &str,
    tcx: TyCtxt<'_>,
    formals: &BTreeMap<(String, u32), ArtifactFormal>,
    deep_refs: &BTreeMap<(String, u32), BTreeSet<FormalKey>>,
    accepted_model_time: Duration,
) -> Result<Measurement, String> {
    let program = super::collect_program(tcx);
    let functions = program.functions.iter().copied().collect::<FxHashSet<_>>();
    let roots = unknown_caller_roots(tcx, &program.functions);

    let t_origins = Instant::now();
    let lifetime_flows = lifetime_flow::analyze_program_lifetime_flow(&program);
    let origins_time = t_origins.elapsed();

    let t_andersen = Instant::now();
    let arena = typed_arena::Arena::new();
    let type_shapes = utils::ty_shape::get_ty_shapes(&arena, tcx, false);
    let config = andersen::Config {
        use_optimized_mir: false,
        c_exposed_fns: roots
            .iter()
            .map(|did| tcx.item_name(did.to_def_id()).to_string())
            .collect(),
    };
    let pre = andersen::pre_analyze(&config, &type_shapes, tcx);
    let solutions = andersen::analyze(&config, &pre, &type_shapes, tcx);
    let andersen_time = t_andersen.elapsed();

    let mut unknown_locations = BTreeSet::new();
    for variable in &pre.exposed_fn_arg_vars {
        let start = pre.vars[variable];
        let end = pre.index_info.get_end(start);
        unknown_locations.extend(start.index()..=end.index());
    }

    let mut coverage = CoverageCounts::default();
    let mut function_nodes = BTreeMap::new();
    for &function in &program.functions {
        function_nodes.insert(
            tcx.def_path_str(function.to_def_id()),
            FunctionNode {
                unknown_caller_root: roots.contains(&function),
                callees: BTreeSet::new(),
            },
        );
    }

    let mut resolved_targets = rustc_hash::FxHashMap::default();
    for &caller in &program.functions {
        let caller_path = tcx.def_path_str(caller.to_def_id());
        let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
        for (block, block_data) in body.basic_blocks.iter_enumerated() {
            let function = match &block_data.terminator().kind {
                TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. } => func,
                _ => continue,
            };
            coverage.calls_total += 1;
            let targets = if let Some(function) = function.constant() {
                let TyKind::FnDef(target, _) = *function.ty().kind() else {
                    coverage.non_fn_def_constant += 1;
                    continue;
                };
                let Some(target) = target.as_local() else {
                    coverage.direct_external += 1;
                    continue;
                };
                if !functions.contains(&target) {
                    coverage.direct_external += 1;
                    continue;
                }
                coverage.direct_local += 1;
                vec![target]
            } else {
                let targets = indirect_targets(&pre, &solutions, caller, block)?;
                let targets = targets
                    .into_iter()
                    .filter(|target| functions.contains(target))
                    .collect::<Vec<_>>();
                if targets.is_empty() {
                    coverage.indirect_unresolved += 1;
                    continue;
                }
                coverage.indirect_local += 1;
                targets
            };

            let target_paths = targets
                .iter()
                .map(|target| tcx.def_path_str(target.to_def_id()))
                .collect::<BTreeSet<_>>();
            function_nodes
                .get_mut(&caller_path)
                .expect("caller node")
                .callees
                .extend(target_paths.iter().cloned());
            resolved_targets.insert((caller, block), targets);
        }
    }

    let unknown_reachable = unknown_reachable(&function_nodes)?;
    let mut call_sites = Vec::new();
    for &caller in &program.functions {
        let caller_path = tcx.def_path_str(caller.to_def_id());
        let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
        let flow = &lifetime_flows
            .get(&caller)
            .ok_or_else(|| format!("missing lifetime flow for {caller_path}"))?
            .body;
        for (block, block_data) in body.basic_blocks.iter_enumerated() {
            let call_args = match &block_data.terminator().kind {
                TerminatorKind::Call { args, .. } | TerminatorKind::TailCall { args, .. } => {
                    &args[..]
                }
                _ => continue,
            };
            let Some(targets) = resolved_targets.get(&(caller, block)) else {
                continue;
            };
            let target_paths = targets
                .iter()
                .map(|target| tcx.def_path_str(target.to_def_id()))
                .collect::<BTreeSet<_>>();

            let arguments = (0..call_args.len())
                .map(|parameter| formal_for_argument(tcx, targets, parameter, formals, deep_refs))
                .collect::<Result<Vec<_>, _>>()?;
            let mut pair_facts = BTreeMap::new();
            for left in 0..call_args.len() {
                for right in left + 1..call_args.len() {
                    pair_facts.insert(
                        (left, right),
                        call_pair_facts(
                            tcx,
                            &body,
                            &pre,
                            &solutions,
                            &unknown_locations,
                            flow,
                            unknown_reachable.contains(&caller_path),
                            caller,
                            &call_args[left].node,
                            &call_args[right].node,
                        ),
                    );
                }
            }
            call_sites.push(CallSite {
                id: format!(
                    "{}:bb{}:{}:{}",
                    caller_path,
                    block.index(),
                    tcx.sess
                        .source_map()
                        .span_to_diagnostic_string(block_data.terminator().source_info.span),
                    target_paths.into_iter().collect::<Vec<_>>().join("|")
                ),
                arguments,
                pair_facts,
            });
        }
    }

    let counts = measure_program(&ProgramInput {
        name: program_name.to_owned(),
        call_sites,
        functions: function_nodes,
    })?;
    coverage.validate()?;
    Ok(Measurement {
        counts,
        coverage,
        timings: Timings {
            origins: origins_time,
            andersen: andersen_time,
            accepted_model: accepted_model_time,
        },
    })
}

pub(super) fn run_worker(tcx: TyCtxt<'_>, t_tcx: Duration) -> super::report::Row {
    let t0 = Instant::now();
    let mut row = super::report::Row::default();
    let program = std::env::var("CRAT_BOC1_NAME").unwrap_or_else(|_| "unnamed".to_owned());
    let Some(snapshot) = std::env::var_os("CRAT_A5_SNAPSHOT").map(std::path::PathBuf::from) else {
        row.set("status", "missing-snapshot");
        return row;
    };
    let deep = std::env::var("CRAT_A5_DEEP").as_deref() == Ok("1");
    let measured = snapshot_formals(&snapshot, &program).and_then(|formals| {
        let t_model = Instant::now();
        let deep_refs = if deep {
            let rust_program = super::collect_program(tcx);
            accepted_deep_refs(tcx, &rust_program, &formals)?
        } else {
            BTreeMap::new()
        };
        let model_time = deep.then(|| t_model.elapsed()).unwrap_or_default();
        measure_tcx(&program, tcx, &formals, &deep_refs, model_time)
    });
    match measured {
        Ok(measured) => {
            let counts = &measured.counts;
            let needs_depth = !deep && counts.sites_not_proven_disjoint > 0;
            if needs_depth {
                println!("{}", render_base_line(counts));
                row.set("status", "needs-depth");
            } else {
                println!("{}", render_count_line(counts));
                row.set("status", "ok");
            }
            row.set("c1", counts.sites_with_two_ref_args);
            row.set("c2", counts.sites_not_proven_disjoint);
            row.set("c3", counts.attributed_predicted_refs);
            row.set("c3_depth0", counts.attributed_predicted_refs_depth0);
            row.set("cg_num", counts.unknown_caller_reachable);
            row.set("cg_den", counts.local_functions);
            row.set("calls_total", measured.coverage.calls_total);
            row.set("direct_local", measured.coverage.direct_local);
            row.set("indirect_local", measured.coverage.indirect_local);
            row.set("direct_external", measured.coverage.direct_external);
            row.set("indirect_unresolved", measured.coverage.indirect_unresolved);
            row.set("non_fn_def_constant", measured.coverage.non_fn_def_constant);
            row.set(
                "t_origins_s",
                format!("{:.3}", measured.timings.origins.as_secs_f64()),
            );
            row.set(
                "t_andersen_s",
                format!("{:.3}", measured.timings.andersen.as_secs_f64()),
            );
            row.set(
                "t_model_s",
                format!("{:.3}", measured.timings.accepted_model.as_secs_f64()),
            );
        }
        Err(why) => {
            row.set("status", "a5-error");
            row.set("detail", super::report::sanitize(&why));
        }
    }
    row.set("t_tcx_s", format!("{:.3}", t_tcx.as_secs_f64()));
    row.set(
        "t_total_s",
        format!("{:.3}", (t0.elapsed() + t_tcx).as_secs_f64()),
    );
    row
}

fn render_base_line(counts: &ProgramCounts) -> String {
    render_count_line_with_sentinel(BASE_SENTINEL, counts)
}

fn render_count_line(counts: &ProgramCounts) -> String {
    render_count_line_with_sentinel(COUNT_SENTINEL, counts)
}

fn render_count_line_with_sentinel(sentinel: &str, counts: &ProgramCounts) -> String {
    counts
        .validate()
        .expect("only valid P1 counts may be rendered");
    format!(
        "{sentinel}program={} c1={} c2={} c3={} c3_depth0={} cg_num={} cg_den={}",
        counts.program,
        counts.sites_with_two_ref_args,
        counts.sites_not_proven_disjoint,
        counts.attributed_predicted_refs,
        counts.attributed_predicted_refs_depth0,
        counts.unknown_caller_reachable,
        counts.local_functions,
    )
}

fn parse_count_line(line: &str) -> Result<ProgramCounts, String> {
    parse_count_line_with_sentinel(COUNT_SENTINEL, line)
}

fn parse_base_line(line: &str) -> Result<ProgramCounts, String> {
    parse_count_line_with_sentinel(BASE_SENTINEL, line)
}

fn parse_count_line_with_sentinel(sentinel: &str, line: &str) -> Result<ProgramCounts, String> {
    let body = line
        .trim()
        .strip_prefix(sentinel)
        .ok_or_else(|| format!("missing {} sentinel", sentinel.trim()))?;
    let mut fields = BTreeMap::new();
    for token in body.split_whitespace() {
        let (key, value) = token
            .split_once('=')
            .ok_or_else(|| format!("malformed token `{token}`"))?;
        if fields.insert(key, value).is_some() {
            return Err(format!("duplicate field `{key}`"));
        }
    }
    const EXPECTED: [&str; 7] = ["program", "c1", "c2", "c3", "c3_depth0", "cg_num", "cg_den"];
    if fields.len() != EXPECTED.len() || EXPECTED.iter().any(|key| !fields.contains_key(key)) {
        return Err("count row does not contain the exact P1 schema".to_owned());
    }
    let number = |key: &str| -> Result<usize, String> {
        fields[key]
            .parse::<usize>()
            .map_err(|error| format!("invalid `{key}`: {error}"))
    };
    let counts = ProgramCounts {
        program: fields["program"].to_owned(),
        sites_with_two_ref_args: number("c1")?,
        sites_not_proven_disjoint: number("c2")?,
        attributed_predicted_refs: number("c3")?,
        attributed_predicted_refs_depth0: number("c3_depth0")?,
        unknown_caller_reachable: number("cg_num")?,
        local_functions: number("cg_den")?,
    };
    counts.validate()?;
    Ok(counts)
}

fn parse_single_raw_line(stdout: &str, sentinel: &str) -> Result<(String, ProgramCounts), String> {
    let lines = stdout
        .lines()
        .filter(|line| line.starts_with(sentinel))
        .collect::<Vec<_>>();
    if lines.len() != 1 {
        return Err(format!(
            "expected exactly one {} raw row, found {}",
            sentinel.trim(),
            lines.len()
        ));
    }
    let counts = parse_count_line_with_sentinel(sentinel, lines[0])?;
    Ok((lines[0].to_owned(), counts))
}

fn aggregate(rows: &[ProgramCounts]) -> Result<ProgramCounts, String> {
    let mut programs = BTreeSet::new();
    let mut total = ProgramCounts {
        program: "TOTAL".to_owned(),
        sites_with_two_ref_args: 0,
        sites_not_proven_disjoint: 0,
        attributed_predicted_refs: 0,
        attributed_predicted_refs_depth0: 0,
        unknown_caller_reachable: 0,
        local_functions: 0,
    };
    for row in rows {
        if !programs.insert(row.program.as_str()) {
            return Err(format!("duplicate aggregate program `{}`", row.program));
        }
        total.sites_with_two_ref_args += row.sites_with_two_ref_args;
        total.sites_not_proven_disjoint += row.sites_not_proven_disjoint;
        total.attributed_predicted_refs += row.attributed_predicted_refs;
        total.attributed_predicted_refs_depth0 += row.attributed_predicted_refs_depth0;
        total.unknown_caller_reachable += row.unknown_caller_reachable;
        total.local_functions += row.local_functions;
    }
    total.validate()?;
    Ok(total)
}

fn a5_substrate_dir(selector: Option<&str>) -> Result<&'static str, String> {
    match selector {
        None | Some("derived") => Ok("benchmarks/rs-crown-derived"),
        Some(other) => Err(format!(
            "A5/P1 is anchored to the derived substrate; got CRAT_BOC1_SUBSTRATE={other:?}"
        )),
    }
}

#[derive(Clone, Debug)]
struct FinalRun {
    counts: ProgramCounts,
    metadata: super::report::Row,
    raw_line: String,
    wall_seconds: f64,
}

#[test]
#[ignore = "A5/P1 artifact-first corpus measurement; requires CRAT_A5_SNAPSHOT and a private CRAT_BOC1_OUT"]
fn a5_p1_corpus() {
    use std::{fs, path::PathBuf};

    const DATE: &str = "2026-08-07";
    const SNAPSHOT_PRODUCER_HEAD: &str = "3b26a0ff85517a33acf916e8dbe2624ffc924a85";
    const SNAPSHOT_PRODUCER_BRANCH_HEAD: &str = "52da86648db9d76d8945063792f37da61bf8c8b9";
    const MANIFEST_COMMIT: &str = "a654d5ecde8a0ea9fccc8a3e7b9caaa8fac5812d";
    const RAW_FROZEN_DIGEST: &str =
        "9fc912af10fd3b235fe4d444d2fbac0bc521509b1c9447fc551acd0130e0e621";
    const DERIVED_SUBSTRATE_DIGEST: &str =
        "db96829b5c2b0db28fb4bb9ddd3d32901b5d4e6e4134da07ada0d513d94eb4c6";

    assert_eq!(
        super::CORPUS.len(),
        20,
        "P1 requires the frozen 20-program catalog"
    );
    assert!(
        std::env::var_os("CRAT_BOC1_PROGRAMS").is_none(),
        "P1 cannot run a post-selected corpus subset"
    );
    assert_eq!(
        std::env::var("CRAT_BO_REPAIR").as_deref(),
        Ok("mode_a"),
        "P1 requires the accepted-model repair profile explicitly"
    );
    assert_eq!(
        std::env::var("CRAT_BO_L2_GUARDED_COMMITS").as_deref(),
        Ok("0"),
        "P1 measures the snapshot's L2-off accepted model"
    );
    assert_eq!(
        std::env::var("CRAT_BO_SAFE_MONO").as_deref(),
        Ok("per_site"),
        "P1 requires the shipped safety-mono profile explicitly"
    );
    assert_eq!(
        std::env::var("CRAT_BO_FORK_ENGINE").as_deref(),
        Ok("fork"),
        "P1 requires the shipped fork engine explicitly"
    );
    let root = super::orchestrate::workspace_root()
        .canonicalize()
        .expect("canonical workspace root");
    let analysis_head = super::orchestrate::git_sha();
    assert_ne!(analysis_head, "unknown", "P1 requires a code HEAD stamp");
    assert!(
        !super::orchestrate::git_dirty(),
        "commit the green harness before running P1"
    );
    let resolver_cwd = root.join("crates/pointer_replacer");
    assert_eq!(
        std::env::current_dir()
            .expect("current directory")
            .canonicalize()
            .expect("canonical current directory"),
        resolver_cwd
            .canonicalize()
            .expect("canonical pointer_replacer directory"),
        "Cargo must run the driver with CWD=crates/pointer_replacer; workers resolve deps through DIR=<root>"
    );
    let substrate_selector = std::env::var("CRAT_BOC1_SUBSTRATE").ok();
    let substrate_dir = a5_substrate_dir(substrate_selector.as_deref())
        .expect("P1 requires the derived substrate/default selector");
    let corpus_link = root.join(substrate_dir);
    assert!(
        fs::symlink_metadata(&corpus_link)
            .expect("derived corpus metadata")
            .file_type()
            .is_symlink(),
        "P1 records the guarded read-only derived-corpus symlink shape"
    );
    let corpus_target = corpus_link
        .canonicalize()
        .expect("canonical derived corpus");
    let out = PathBuf::from(
        std::env::var_os("CRAT_BOC1_OUT").expect("P1 requires an explicit private CRAT_BOC1_OUT"),
    );
    assert!(
        !out.starts_with(root.join("target/boc1")),
        "P1 must not write the ladder lane's target/boc1 tree"
    );
    let snapshot =
        PathBuf::from(std::env::var_os("CRAT_A5_SNAPSHOT").expect("P1 requires CRAT_A5_SNAPSHOT"));
    assert!(snapshot.is_dir(), "immutable snapshot is not a directory");
    assert_eq!(
        fs::read_dir(&snapshot)
            .expect("read immutable snapshot")
            .filter_map(Result::ok)
            .filter(|entry| entry.file_type().is_ok_and(|kind| kind.is_file()))
            .count(),
        100,
        "snapshot inventory moved after Boundary 0"
    );

    let deps_link = root.join("deps_crate/target");
    assert!(
        fs::symlink_metadata(&deps_link)
            .expect("deps target metadata")
            .file_type()
            .is_symlink(),
        "P1 records the approved read-only symlink provisioning shape"
    );
    let deps_target = deps_link.canonicalize().expect("canonical deps target");
    let deps_dir = deps_target.join("debug/deps");
    let deps_entries = fs::read_dir(&deps_dir).expect("read linked deps directory");
    let mut rlibs = 0usize;
    let mut bytemuck_derive = false;
    for entry in deps_entries.filter_map(Result::ok) {
        let name = entry.file_name();
        let name = name.to_string_lossy();
        rlibs += usize::from(name.ends_with(".rlib"));
        bytemuck_derive |= name.starts_with("libbytemuck_derive") && name.ends_with(".dylib");
    }
    assert!(rlibs > 0, "linked deps target contains no rlibs");
    assert!(
        bytemuck_derive,
        "linked deps target lacks bytemuck_derive dylib"
    );

    let base_timeout = Duration::from_secs(
        std::env::var("CRAT_A5_BASE_TIMEOUT_SECS")
            .ok()
            .and_then(|value| value.parse().ok())
            .unwrap_or(900),
    );
    let deep_timeout = Duration::from_secs(
        std::env::var("CRAT_A5_DEEP_TIMEOUT_SECS")
            .ok()
            .and_then(|value| value.parse().ok())
            .unwrap_or(3000),
    );
    let snapshot_env = snapshot.display().to_string();

    let mut final_runs = BTreeMap::new();
    let mut needs_depth = Vec::new();
    for program in super::CORPUS {
        let input = corpus_link.join(program.name).join(program.lib_root);
        let outcome = super::orchestrate::run_child_env(
            program.name,
            &input,
            "a5-p1",
            base_timeout,
            &[("CRAT_A5_SNAPSHOT", snapshot_env.clone())],
        );
        match outcome.status.as_str() {
            "ok" => {
                let (raw_line, counts) = parse_single_raw_line(&outcome.stdout, COUNT_SENTINEL)
                    .unwrap_or_else(|why| panic!("{}: {why}", program.name));
                assert_eq!(counts.program, program.name);
                assert_eq!(
                    counts.sites_not_proven_disjoint, 0,
                    "{} returned a final base row despite needing a depth export",
                    program.name
                );
                final_runs.insert(
                    program.name,
                    FinalRun {
                        counts,
                        metadata: outcome.row.expect("final worker BOC1 row"),
                        raw_line,
                        wall_seconds: outcome.wall_s,
                    },
                );
            }
            "needs-depth" => {
                let (_, counts) = parse_single_raw_line(&outcome.stdout, BASE_SENTINEL)
                    .unwrap_or_else(|why| panic!("{}: {why}", program.name));
                assert_eq!(counts.program, program.name);
                assert!(counts.sites_not_proven_disjoint > 0);
                needs_depth.push((*program, counts, outcome.wall_s));
            }
            other => panic!(
                "{}: base worker status={other} note={}",
                program.name, outcome.note
            ),
        }
    }

    assert!(
        needs_depth.len() < super::CORPUS.len(),
        "all 20 programs require a targeted accepted-model export; P1 refuses a suite-wide re-solve"
    );
    let targeted_count = needs_depth.len();
    for (program, base, base_wall) in needs_depth {
        let input = corpus_link.join(program.name).join(program.lib_root);
        let outcome = super::orchestrate::run_child_env(
            program.name,
            &input,
            "a5-p1",
            deep_timeout,
            &[
                ("CRAT_A5_SNAPSHOT", snapshot_env.clone()),
                ("CRAT_A5_DEEP", "1".to_owned()),
            ],
        );
        assert_eq!(
            outcome.status, "ok",
            "{}: targeted depth worker failed: {}",
            program.name, outcome.note
        );
        let (raw_line, counts) = parse_single_raw_line(&outcome.stdout, COUNT_SENTINEL)
            .unwrap_or_else(|why| panic!("{}: {why}", program.name));
        assert_eq!(counts.program, program.name);
        assert_eq!(counts.sites_with_two_ref_args, base.sites_with_two_ref_args);
        assert_eq!(
            counts.sites_not_proven_disjoint,
            base.sites_not_proven_disjoint
        );
        assert_eq!(
            counts.attributed_predicted_refs_depth0,
            base.attributed_predicted_refs_depth0
        );
        assert_eq!(
            counts.unknown_caller_reachable,
            base.unknown_caller_reachable
        );
        assert_eq!(counts.local_functions, base.local_functions);
        final_runs.insert(
            program.name,
            FinalRun {
                counts,
                metadata: outcome.row.expect("targeted worker BOC1 row"),
                raw_line,
                wall_seconds: base_wall + outcome.wall_s,
            },
        );
    }

    assert_eq!(final_runs.len(), super::CORPUS.len());
    let rows = super::CORPUS
        .iter()
        .map(|program| {
            final_runs
                .get(program.name)
                .expect("final row for every catalog program")
                .counts
                .clone()
        })
        .collect::<Vec<_>>();
    let total = aggregate(&rows).expect("valid P1 aggregate");

    let output = out.join("a5-p1");
    fs::create_dir_all(&output).expect("create P1 output directory");
    let mut raw = String::new();
    let mut tsv = String::from(
        "program\tc1\tc2\tc3\tc3_depth0\tcg_num\tcg_den\tcalls_total\tdirect_local\tindirect_local\tdirect_external\tindirect_unresolved\tnon_fn_def_constant\tt_origins_s\tt_andersen_s\tt_model_s\twall_s\n",
    );
    let mut markdown = format!(
        "# A5/P1 raw measurement\n\nHEAD `{analysis_head}`, date {DATE}; manifest docs `{MANIFEST_COMMIT}`.\n\n| program | C1 | C2 | C3-all | C3-d0 | unknown-reachable / local functions |\n|---|---:|---:|---:|---:|---:|\n"
    );
    for program in super::CORPUS {
        let run = &final_runs[program.name];
        raw.push_str(&run.raw_line);
        raw.push('\n');
        let get = |key: &str| run.metadata.get(key).unwrap_or("missing");
        tsv.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{:.3}\n",
            program.name,
            run.counts.sites_with_two_ref_args,
            run.counts.sites_not_proven_disjoint,
            run.counts.attributed_predicted_refs,
            run.counts.attributed_predicted_refs_depth0,
            run.counts.unknown_caller_reachable,
            run.counts.local_functions,
            get("calls_total"),
            get("direct_local"),
            get("indirect_local"),
            get("direct_external"),
            get("indirect_unresolved"),
            get("non_fn_def_constant"),
            get("t_origins_s"),
            get("t_andersen_s"),
            get("t_model_s"),
            run.wall_seconds,
        ));
        markdown.push_str(&format!(
            "| {} | {} | {} | {} | {} | {} / {} |\n",
            program.name,
            run.counts.sites_with_two_ref_args,
            run.counts.sites_not_proven_disjoint,
            run.counts.attributed_predicted_refs,
            run.counts.attributed_predicted_refs_depth0,
            run.counts.unknown_caller_reachable,
            run.counts.local_functions,
        ));
    }
    markdown.push_str(&format!(
        "| **TOTAL / micro-average** | **{}** | **{}** | **{}** | **{}** | **{} / {} ({:.2}%)** |\n",
        total.sites_with_two_ref_args,
        total.sites_not_proven_disjoint,
        total.attributed_predicted_refs,
        total.attributed_predicted_refs_depth0,
        total.unknown_caller_reachable,
        total.local_functions,
        100.0 * total.unknown_caller_reachable as f64 / total.local_functions as f64,
    ));
    let provenance = format!(
        "date={DATE}\nanalysis_worktree_head={analysis_head}\nsnapshot_producer_head={SNAPSHOT_PRODUCER_HEAD}\nsnapshot_producer_branch_head={SNAPSHOT_PRODUCER_BRANCH_HEAD}\nsnapshot_producer_branch_delta=one-test-only-commit-after-capture\nmanifest_commit={MANIFEST_COMMIT}\nraw_frozen_corpus_sha256={RAW_FROZEN_DIGEST}\nderived_substrate_sha256={DERIVED_SUBSTRATE_DIGEST}\nsubstrate=derived\nsubstrate_selector={}\nrepair=mode_a\nl2=0\nsafe_mono=per_site\nfork_engine=fork\nmutability_facts=on-direct-from-program\nz3_smt_seed=0\nz3_sat_seed=0\ncorpus_shape=read-only-symlink-to-main-checkout-derived-corpus\ncorpus_link={}\ncorpus_target={}\nsnapshot={}\ndeps_shape=read-only-symlink-to-main-checkout-build\ndeps_link={}\ndeps_target={}\ndeps_rlibs={}\ndeps_bytemuck_derive=present\nresolver_DIR={}\nresolver_CWD={}\nbase_timeout_s={}\ndeep_timeout_s={}\ntargeted_programs={}\n",
        substrate_selector.as_deref().unwrap_or("default-derived"),
        corpus_link.display(),
        corpus_target.display(),
        snapshot.display(),
        deps_link.display(),
        deps_target.display(),
        rlibs,
        root.display(),
        resolver_cwd.display(),
        base_timeout.as_secs(),
        deep_timeout.as_secs(),
        targeted_count,
    );
    fs::write(output.join("raw-counts.txt"), raw).expect("write raw P1 rows");
    fs::write(output.join("per-program.tsv"), tsv).expect("write P1 TSV");
    fs::write(output.join("report.md"), markdown).expect("write P1 markdown");
    fs::write(output.join("provenance.txt"), provenance).expect("write P1 provenance");
    println!("{}", render_count_line(&total));
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use super::*;

    fn set(values: &[&str]) -> BTreeSet<String> {
        values.iter().map(|value| (*value).to_owned()).collect()
    }

    fn formal(function: &str, parameter: u32, depth: u8) -> FormalDecision {
        FormalDecision {
            settles_ref: true,
            currently_predicted_refs: BTreeSet::from([FormalKey {
                function: function.to_owned(),
                parameter,
                depth,
            }]),
        }
    }

    #[test]
    fn absence_of_storage_alias_is_unknown_not_disjoint() {
        let facts = PairFacts {
            storage_alias: false,
            ..PairFacts::default()
        };

        assert_eq!(classify_pair(&facts), PairClass::NotProvenDisjoint);
    }

    #[test]
    fn only_complete_positive_evidence_proves_disjointness() {
        let projection_disjoint = PairFacts {
            projection_disjoint: true,
            ..PairFacts::default()
        };
        let complete_disjoint_origins = PairFacts {
            origins: SetPairEvidence::Complete {
                left: set(&["origin-a"]),
                right: set(&["origin-b"]),
            },
            ..PairFacts::default()
        };
        let complete_disjoint_points_to = PairFacts {
            points_to: SetPairEvidence::Complete {
                left: set(&["alloc-a"]),
                right: set(&["alloc-b"]),
            },
            ..PairFacts::default()
        };
        let incomplete_disjoint = PairFacts {
            points_to: SetPairEvidence::Incomplete {
                left: set(&["alloc-a"]),
                right: set(&["alloc-b"]),
            },
            ..PairFacts::default()
        };
        let known_storage_alias = PairFacts {
            storage_alias: true,
            projection_disjoint: true,
            ..PairFacts::default()
        };

        assert_eq!(
            classify_pair(&projection_disjoint),
            PairClass::ProvenDisjoint
        );
        assert_eq!(
            classify_pair(&complete_disjoint_origins),
            PairClass::ProvenDisjoint
        );
        assert_eq!(
            classify_pair(&complete_disjoint_points_to),
            PairClass::ProvenDisjoint
        );
        assert_eq!(
            classify_pair(&incomplete_disjoint),
            PairClass::NotProvenDisjoint
        );
        assert_eq!(
            classify_pair(&known_storage_alias),
            PairClass::NotProvenDisjoint
        );
    }

    #[test]
    fn risky_sites_deduplicate_formals_and_report_the_depth_zero_subset() {
        let outer = formal("callee", 1, 0);
        let deeper = formal("callee", 2, 1);
        let mut pair_facts = BTreeMap::new();
        pair_facts.insert((0, 1), PairFacts::default());
        let site = CallSite {
            id: "caller:bb0".to_owned(),
            arguments: vec![outer.clone(), deeper.clone()],
            pair_facts,
        };
        let one_ref_site = CallSite {
            id: "caller:bb2".to_owned(),
            arguments: vec![formal("callee", 3, 0)],
            pair_facts: BTreeMap::new(),
        };
        let program = ProgramInput {
            name: "fixture".to_owned(),
            call_sites: vec![
                site.clone(),
                CallSite {
                    id: "caller:bb1".to_owned(),
                    ..site
                },
                one_ref_site,
            ],
            functions: BTreeMap::new(),
        };

        let measured = measure_program(&program).expect("valid fixture");

        assert_eq!(measured.sites_with_two_ref_args, 2);
        assert_eq!(measured.sites_not_proven_disjoint, 2);
        assert_eq!(measured.attributed_predicted_refs, 2);
        assert_eq!(measured.attributed_predicted_refs_depth0, 1);
    }

    #[test]
    fn closedness_is_the_forward_closure_of_unknown_caller_roots() {
        let functions = BTreeMap::from([
            (
                "root".to_owned(),
                FunctionNode {
                    unknown_caller_root: true,
                    callees: set(&["mid"]),
                },
            ),
            (
                "mid".to_owned(),
                FunctionNode {
                    unknown_caller_root: false,
                    callees: set(&["leaf"]),
                },
            ),
            ("leaf".to_owned(), FunctionNode::default()),
            ("closed".to_owned(), FunctionNode::default()),
        ]);
        let program = ProgramInput {
            name: "fixture".to_owned(),
            call_sites: Vec::new(),
            functions,
        };

        let measured = measure_program(&program).expect("valid fixture");

        assert_eq!(measured.unknown_caller_reachable, 3);
        assert_eq!(measured.local_functions, 4);
    }

    #[test]
    fn raw_count_rows_round_trip_and_missing_fields_fail_closed() {
        let counts = ProgramCounts {
            program: "fixture".to_owned(),
            sites_with_two_ref_args: 7,
            sites_not_proven_disjoint: 5,
            attributed_predicted_refs: 4,
            attributed_predicted_refs_depth0: 3,
            unknown_caller_reachable: 2,
            local_functions: 6,
        };
        let encoded = render_count_line(&counts);

        assert_eq!(parse_count_line(&encoded), Ok(counts.clone()));
        assert!(parse_count_line("A5P1 program=fixture c1=7").is_err());
        assert!(
            parse_count_line(
                "A5P1 program=fixture program=fixture c1=7 c2=5 c3=4 c3_depth0=3 cg_num=2 cg_den=6"
            )
            .is_err()
        );
        assert!(
            parse_count_line("A5P1 program=fixture c1=1 c2=2 c3=4 c3_depth0=3 cg_num=2 cg_den=6")
                .is_err()
        );
        let raw = format!("noise\n{}\nother", render_count_line(&counts));
        assert_eq!(
            parse_single_raw_line(&raw, COUNT_SENTINEL),
            Ok((render_count_line(&counts), counts.clone()))
        );
        assert!(
            parse_single_raw_line(
                &format!(
                    "{}\n{}",
                    render_count_line(&counts),
                    render_count_line(&counts)
                ),
                COUNT_SENTINEL,
            )
            .is_err()
        );
        assert!(parse_count_line(&render_base_line(&counts)).is_err());
        assert_eq!(parse_base_line(&render_base_line(&counts)), Ok(counts));
    }

    #[test]
    fn aggregation_sums_closedness_for_the_micro_average() {
        let rows = [
            ProgramCounts {
                program: "small".to_owned(),
                sites_with_two_ref_args: 1,
                sites_not_proven_disjoint: 1,
                attributed_predicted_refs: 2,
                attributed_predicted_refs_depth0: 1,
                unknown_caller_reachable: 1,
                local_functions: 2,
            },
            ProgramCounts {
                program: "large".to_owned(),
                sites_with_two_ref_args: 3,
                sites_not_proven_disjoint: 2,
                attributed_predicted_refs: 4,
                attributed_predicted_refs_depth0: 3,
                unknown_caller_reachable: 9,
                local_functions: 10,
            },
        ];

        let total = aggregate(&rows).expect("valid aggregate");

        assert_eq!(total.sites_with_two_ref_args, 4);
        assert_eq!(total.sites_not_proven_disjoint, 3);
        assert_eq!(total.attributed_predicted_refs, 6);
        assert_eq!(total.attributed_predicted_refs_depth0, 4);
        assert_eq!(total.unknown_caller_reachable, 10);
        assert_eq!(total.local_functions, 12);
    }

    #[test]
    fn p1_substrate_defaults_to_derived_and_refuses_raw() {
        assert_eq!(a5_substrate_dir(None), Ok("benchmarks/rs-crown-derived"));
        assert_eq!(
            a5_substrate_dir(Some("derived")),
            Ok("benchmarks/rs-crown-derived")
        );
        assert!(a5_substrate_dir(Some("raw")).is_err());
    }

    #[test]
    fn artifact_join_distinguishes_settled_from_currently_predicted_ref() {
        // Minimized from the manifest-verified libcsv/csv_fwrite rows.  Reconciliation
        // requires binding_i.hi <= decl_i.lo and decl_(i-1).hi <= binding_i.lo;
        // the synthetic change is limited to fp's outcome/degrade_reason under test.
        let a = concat!(
            "{\"fn_path\":\"src::libcsv::csv_fwrite\",\"mir_local\":1,\"param_name\":\"fp\",\"arg_index\":1,\"ptr_depth\":1,\"pairing_confidence\":\"high\",\"decl_span\":\"/Users/p51lee/dev/agent-worktrees/crat-m1/crates/pointer_replacer/../../benchmarks/rs-crown/libcsv/src/libcsv.rs:856:13: 856:22\",\"decl_span_lo\":34779,\"decl_span_hi\":34788,\"binding_span_lo\":null,\"binding_span_hi\":null,\"decl_shape\":\"raw-ptr\",\"outcome\":\"degraded\",\"degrade_reason\":\"raw-pointer-operation\"}\n",
            "{\"fn_path\":\"src::libcsv::csv_fwrite\",\"mir_local\":2,\"param_name\":\"src\",\"arg_index\":2,\"ptr_depth\":1,\"pairing_confidence\":\"high\",\"decl_span\":\"/Users/p51lee/dev/agent-worktrees/crat-m1/crates/pointer_replacer/../../benchmarks/rs-crown/libcsv/src/libcsv.rs:857:14: 857:33\",\"decl_span_lo\":34803,\"decl_span_hi\":34822,\"binding_span_lo\":null,\"binding_span_hi\":null,\"decl_shape\":\"raw-ptr\",\"outcome\":\"ref-shared\",\"degrade_reason\":null}\n",
        );
        let b = concat!(
            "{\"fn_path\":\"src::libcsv::csv_fwrite\",\"mir_local\":1,\"param_name\":\"fp\",\"arg_index\":1,\"ptr_depth\":1,\"pairing_confidence\":\"high\",\"decl_span\":null,\"decl_span_lo\":null,\"decl_span_hi\":null,\"binding_span_lo\":34771,\"binding_span_hi\":34777,\"decl_shape\":null,\"outcome\":null,\"degrade_reason\":null}\n",
            "{\"fn_path\":\"src::libcsv::csv_fwrite\",\"mir_local\":2,\"param_name\":\"src\",\"arg_index\":2,\"ptr_depth\":1,\"pairing_confidence\":\"high\",\"decl_span\":null,\"decl_span_lo\":null,\"decl_span_hi\":null,\"binding_span_lo\":34794,\"binding_span_hi\":34801,\"decl_shape\":null,\"outcome\":null,\"degrade_reason\":null}\n",
        );
        let facts = concat!(
            "fn_path\tmir_local\tis_param\tannotated\tslot\tkind\traw_op\tptr_cmp\tctor\tlen_class\tsize_expr\n",
            "src::libcsv::csv_fwrite\t1\t1\t1\t1\tref\t-\t0\tparam\tparam-no-site\t\n",
            "src::libcsv::csv_fwrite\t2\t1\t1\t1\tref\t-\t0\tparam\tparam-no-site\t\n",
        );

        let formals = parse_formals(a, b, facts).expect("valid joined fixture");
        let fp = &formals[&("src::libcsv::csv_fwrite".to_owned(), 1)];
        let src = &formals[&("src::libcsv::csv_fwrite".to_owned(), 2)];

        assert!(fp.settles_ref);
        assert!(!fp.currently_predicted_ref);
        assert!(src.settles_ref);
        assert!(src.currently_predicted_ref);
    }

    #[test]
    fn unknown_root_parameters_keep_a_direct_call_pair_risky() {
        ::utils::compilation::run_compiler_on_str(
            r#"
unsafe fn two(x: *mut i32, y: *mut i32) { *x = *y + 1; }
pub unsafe fn entry(p: *mut i32, q: *mut i32) { two(p, q); }
"#,
            |tcx| {
                let program = super::super::collect_program(tcx);
                let two = program
                    .functions
                    .iter()
                    .copied()
                    .find(|did| tcx.item_name(did.to_def_id()).as_str() == "two")
                    .expect("two");
                let path = tcx.def_path_str(two.to_def_id());
                let formals = BTreeMap::from([
                    (
                        (path.clone(), 1),
                        ArtifactFormal {
                            settles_ref: true,
                            currently_predicted_ref: true,
                            ptr_depth: 1,
                        },
                    ),
                    (
                        (path, 2),
                        ArtifactFormal {
                            settles_ref: true,
                            currently_predicted_ref: true,
                            ptr_depth: 1,
                        },
                    ),
                ]);

                let measured =
                    measure_tcx("fixture", tcx, &formals, &BTreeMap::new(), Duration::ZERO)
                        .expect("measured fixture");

                assert_eq!(measured.counts.sites_with_two_ref_args, 1);
                assert_eq!(measured.counts.sites_not_proven_disjoint, 1);
                assert_eq!(measured.counts.attributed_predicted_refs, 2);
                assert_eq!(measured.counts.attributed_predicted_refs_depth0, 2);
                assert_eq!(measured.counts.unknown_caller_reachable, 2);
                assert_eq!(measured.counts.local_functions, 2);
            },
        )
        .expect("fixture compiles");
    }
}
