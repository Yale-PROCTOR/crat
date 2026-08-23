//! Pure domain for A5 parameter may-overlap summaries.

use std::collections::{BTreeMap, BTreeSet};

use petgraph::{algo::kosaraju_scc, graphmap::DiGraphMap};

use super::{
    l2::{FnKey, MirLocationKey, SlotKey},
    solver::{KindSolver, SlotRef},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct ParamPair {
    first: u32,
    second: u32,
}

impl ParamPair {
    pub(crate) fn new(left: u32, right: u32) -> Option<Self> {
        (left != right).then(|| Self {
            first: left.min(right),
            second: left.max(right),
        })
    }

    pub(crate) fn first(self) -> u32 {
        self.first
    }

    pub(crate) fn second(self) -> u32 {
        self.second
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct FunctionPairKey {
    function: FnKey,
    params: ParamPair,
}

impl FunctionPairKey {
    pub(crate) fn new(function: FnKey, left: u32, right: u32) -> Option<Self> {
        Some(Self {
            function,
            params: ParamPair::new(left, right)?,
        })
    }

    pub(crate) fn function(self) -> FnKey {
        self.function
    }

    pub(crate) fn params(self) -> ParamPair {
        self.params
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct CallSiteWitnessKey {
    pair: FunctionPairKey,
    caller: FnKey,
    location: MirLocationKey,
    actuals: (SlotKey, SlotKey),
}

impl CallSiteWitnessKey {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        callee: FnKey,
        left_param: u32,
        left_actual: SlotKey,
        right_param: u32,
        right_actual: SlotKey,
        caller: FnKey,
        location: MirLocationKey,
    ) -> Option<Self> {
        let pair = FunctionPairKey::new(callee, left_param, right_param)?;
        let actuals = if left_param < right_param {
            (left_actual, right_actual)
        } else {
            (right_actual, left_actual)
        };
        Some(Self {
            pair,
            caller,
            location,
            actuals,
        })
    }

    pub(crate) fn pair(self) -> FunctionPairKey {
        self.pair
    }

    pub(crate) fn actuals(self) -> (SlotKey, SlotKey) {
        self.actuals
    }

    pub(crate) fn caller(self) -> FnKey {
        self.caller
    }

    pub(crate) fn location(self) -> MirLocationKey {
        self.location
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct MayOverlapSummary {
    witnesses: BTreeMap<FunctionPairKey, BTreeSet<CallSiteWitnessKey>>,
}

impl MayOverlapSummary {
    pub(crate) fn insert(&mut self, witness: CallSiteWitnessKey) -> bool {
        self.witnesses
            .entry(witness.pair())
            .or_default()
            .insert(witness)
    }

    pub(crate) fn union_from(&mut self, other: &Self) -> bool {
        let mut changed = false;
        for witnesses in other.witnesses.values() {
            for &witness in witnesses {
                changed |= self.insert(witness);
            }
        }
        changed
    }

    pub(crate) fn witnesses(&self, pair: FunctionPairKey) -> &BTreeSet<CallSiteWitnessKey> {
        self.witnesses
            .get(&pair)
            .expect("may-overlap pair must have at least one witness")
    }

    pub(crate) fn contains(&self, pair: FunctionPairKey) -> bool {
        self.witnesses.contains_key(&pair)
    }

    pub(crate) fn ordered_rows(&self) -> Vec<(FunctionPairKey, CallSiteWitnessKey)> {
        self.witnesses
            .iter()
            .flat_map(|(&pair, witnesses)| {
                witnesses
                    .iter()
                    .copied()
                    .map(move |witness| (pair, witness))
            })
            .collect()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum TransferCause {
    DirectEvidence,
    CallerPair(FunctionPairKey),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct CallTransfer {
    witness: CallSiteWitnessKey,
    cause: TransferCause,
}

impl CallTransfer {
    pub(crate) fn direct(witness: CallSiteWitnessKey) -> Self {
        Self {
            witness,
            cause: TransferCause::DirectEvidence,
        }
    }

    pub(crate) fn forwarded(
        witness: CallSiteWitnessKey,
        caller_pair: FunctionPairKey,
    ) -> Result<Self, String> {
        if caller_pair.function() != witness.caller() {
            return Err(format!(
                "A5 transfer dependency belongs to function {}, but call witness belongs to {}",
                caller_pair.function(),
                witness.caller()
            ));
        }
        Ok(Self {
            witness,
            cause: TransferCause::CallerPair(caller_pair),
        })
    }

    fn caller(self) -> FnKey {
        self.witness.caller()
    }

    fn callee(self) -> FnKey {
        self.witness.pair().function()
    }

    fn is_active(self, summary: &MayOverlapSummary) -> bool {
        match self.cause {
            TransferCause::DirectEvidence => true,
            TransferCause::CallerPair(pair) => summary.contains(pair),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MayOverlapFixpoint {
    summary: MayOverlapSummary,
    sccs: Vec<Vec<FnKey>>,
    scc_iterations: usize,
}

impl MayOverlapFixpoint {
    pub(crate) fn summary(&self) -> &MayOverlapSummary {
        &self.summary
    }

    pub(crate) fn sccs(&self) -> &[Vec<FnKey>] {
        &self.sccs
    }

    pub(crate) fn scc_iterations(&self) -> usize {
        self.scc_iterations
    }
}

pub(crate) fn solve_may_overlap(
    transfers: impl IntoIterator<Item = CallTransfer>,
) -> MayOverlapFixpoint {
    let transfers = transfers.into_iter().collect::<BTreeSet<_>>();
    let mut functions = BTreeSet::new();
    for transfer in &transfers {
        functions.insert(transfer.caller());
        functions.insert(transfer.callee());
    }

    let mut graph = DiGraphMap::<FnKey, ()>::new();
    for &function in &functions {
        graph.add_node(function);
    }
    for transfer in &transfers {
        graph.add_edge(transfer.caller(), transfer.callee(), ());
    }

    let mut components = kosaraju_scc(&graph);
    for component in &mut components {
        component.sort_unstable();
    }
    let mut component_of = BTreeMap::new();
    for (index, component) in components.iter().enumerate() {
        for &function in component {
            component_of.insert(function, index);
        }
    }
    let mut outgoing = vec![BTreeSet::new(); components.len()];
    let mut indegree = vec![0usize; components.len()];
    for transfer in &transfers {
        let caller = component_of[&transfer.caller()];
        let callee = component_of[&transfer.callee()];
        if caller != callee && outgoing[caller].insert(callee) {
            indegree[callee] += 1;
        }
    }
    let mut ready = components
        .iter()
        .enumerate()
        .filter_map(|(index, component)| (indegree[index] == 0).then_some((component[0], index)))
        .collect::<BTreeSet<_>>();
    let mut schedule = Vec::with_capacity(components.len());
    while let Some(&(minimum, component)) = ready.iter().next() {
        ready.remove(&(minimum, component));
        schedule.push(component);
        for &successor in &outgoing[component] {
            indegree[successor] -= 1;
            if indegree[successor] == 0 {
                ready.insert((components[successor][0], successor));
            }
        }
    }
    assert_eq!(schedule.len(), components.len(), "SCC DAG must be acyclic");

    let mut summary = MayOverlapSummary::default();
    let mut scc_iterations = 0;
    let mut ordered_sccs = Vec::with_capacity(schedule.len());
    for component in schedule {
        let functions = &components[component];
        loop {
            scc_iterations += 1;
            let mut changed = false;
            for &transfer in &transfers {
                if functions.binary_search(&transfer.callee()).is_ok()
                    && transfer.is_active(&summary)
                {
                    changed |= summary.insert(transfer.witness);
                }
            }
            if !changed {
                break;
            }
        }
        ordered_sccs.push(functions.clone());
    }

    MayOverlapFixpoint {
        summary,
        sccs: ordered_sccs,
        scc_iterations,
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum SetPairEvidence<T> {
    Unknown,
    Complete {
        left: BTreeSet<T>,
        right: BTreeSet<T>,
    },
    Incomplete {
        left: BTreeSet<T>,
        right: BTreeSet<T>,
    },
}

impl<T> Default for SetPairEvidence<T> {
    fn default() -> Self {
        Self::Unknown
    }
}

impl<T: Ord> SetPairEvidence<T> {
    pub(crate) fn proves_disjoint(&self) -> bool {
        let Self::Complete { left, right } = self else {
            return false;
        };
        !left.is_empty() && !right.is_empty() && left.is_disjoint(right)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PairFacts<T> {
    pub(crate) storage_alias: bool,
    pub(crate) projection_disjoint: bool,
    pub(crate) origins: SetPairEvidence<T>,
    pub(crate) points_to: SetPairEvidence<T>,
}

impl<T> Default for PairFacts<T> {
    fn default() -> Self {
        Self {
            storage_alias: false,
            projection_disjoint: false,
            origins: SetPairEvidence::Unknown,
            points_to: SetPairEvidence::Unknown,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PairClass {
    ProvenDisjoint,
    NotProvenDisjoint,
}

impl PairClass {
    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::ProvenDisjoint => "proven-disjoint",
            Self::NotProvenDisjoint => "not-proven-disjoint",
        }
    }
}

pub(crate) fn classify_pair<T: Ord>(facts: &PairFacts<T>) -> PairClass {
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

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum PairSide {
    Left,
    Right,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum WitnessMutability {
    MutMut,
    MutReadOnly { read_only: PairSide },
    SharedShared,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct WitnessMutabilityJoin {
    pub(crate) class: WitnessMutability,
    pub(crate) missing_defaults: usize,
}

pub(crate) fn join_witness_mutability(
    left: impl IntoIterator<Item = Option<bool>>,
    right: impl IntoIterator<Item = Option<bool>>,
) -> WitnessMutabilityJoin {
    let join_side = |values: &mut dyn Iterator<Item = Option<bool>>| {
        let mut seen = false;
        let mut mutable = false;
        let mut missing = 0;
        for value in values {
            seen = true;
            match value {
                Some(value) => mutable |= value,
                None => {
                    mutable = true;
                    missing += 1;
                }
            }
        }
        if !seen {
            mutable = true;
            missing = 1;
        }
        (mutable, missing)
    };
    let (left_mutable, left_missing) = join_side(&mut left.into_iter());
    let (right_mutable, right_missing) = join_side(&mut right.into_iter());
    let class = match (left_mutable, right_mutable) {
        (true, true) => WitnessMutability::MutMut,
        (true, false) => WitnessMutability::MutReadOnly {
            read_only: PairSide::Right,
        },
        (false, true) => WitnessMutability::MutReadOnly {
            read_only: PairSide::Left,
        },
        (false, false) => WitnessMutability::SharedShared,
    };
    WitnessMutabilityJoin {
        class,
        missing_defaults: left_missing + right_missing,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SnapshotEffect {
    None,
    SharedRead,
    MutableWrite,
    OpaqueEscape,
    Volatile,
    Atomic,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SnapshotEffectGraph {
    events: Vec<SnapshotEffect>,
    successors: Vec<BTreeSet<usize>>,
    recursive: bool,
}

impl SnapshotEffectGraph {
    pub(crate) fn new(
        events: Vec<SnapshotEffect>,
        edges: impl IntoIterator<Item = (usize, usize)>,
    ) -> Result<Self, String> {
        let mut successors = vec![BTreeSet::new(); events.len()];
        for (from, to) in edges {
            if from >= events.len() || to >= events.len() {
                return Err("snapshot effect edge is outside the node universe".to_owned());
            }
            successors[from].insert(to);
        }
        Ok(Self {
            events,
            successors,
            recursive: false,
        })
    }

    pub(crate) fn recursive(events: Vec<SnapshotEffect>) -> Self {
        Self {
            successors: vec![BTreeSet::new(); events.len()],
            events,
            recursive: true,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SnapshotVerdict {
    Markable,
    ReadAfterWrite,
    OpaqueEscape,
    Recursive,
    VolatileOrAtomic,
}

pub(crate) fn check_snapshot_equivalence(graph: &SnapshotEffectGraph) -> SnapshotVerdict {
    if graph.recursive {
        return SnapshotVerdict::Recursive;
    }
    if graph
        .events
        .iter()
        .any(|effect| matches!(effect, SnapshotEffect::Volatile | SnapshotEffect::Atomic))
    {
        return SnapshotVerdict::VolatileOrAtomic;
    }
    if graph
        .events
        .iter()
        .any(|effect| *effect == SnapshotEffect::OpaqueEscape)
    {
        return SnapshotVerdict::OpaqueEscape;
    }
    for (start, effect) in graph.events.iter().enumerate() {
        if *effect != SnapshotEffect::MutableWrite {
            continue;
        }
        let mut pending = graph.successors[start].iter().copied().collect::<Vec<_>>();
        let mut seen = BTreeSet::new();
        while let Some(node) = pending.pop() {
            if !seen.insert(node) {
                continue;
            }
            if graph.events[node] == SnapshotEffect::SharedRead {
                return SnapshotVerdict::ReadAfterWrite;
            }
            pending.extend(graph.successors[node].iter().copied());
        }
    }
    SnapshotVerdict::Markable
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct WitnessMarkability {
    pub(crate) effect: SnapshotVerdict,
    pub(crate) target_types_agree: bool,
    pub(crate) copy_scalar: bool,
    pub(crate) unknown_caller: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum MarkabilityFailure {
    MissingWitness,
    ReadAfterWrite,
    OpaqueEscape,
    Recursive,
    VolatileOrAtomic,
    TargetTypeMismatch,
    NonCopyScalar,
    UnknownCaller,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum AllWitnessesGate {
    Discharged,
    Demote {
        reasons: BTreeSet<MarkabilityFailure>,
    },
}

pub(crate) fn all_witnesses_gate(
    witnesses: impl IntoIterator<Item = WitnessMarkability>,
) -> AllWitnessesGate {
    let mut seen = false;
    let mut reasons = BTreeSet::new();
    for witness in witnesses {
        seen = true;
        match witness.effect {
            SnapshotVerdict::Markable => {}
            SnapshotVerdict::ReadAfterWrite => {
                reasons.insert(MarkabilityFailure::ReadAfterWrite);
            }
            SnapshotVerdict::OpaqueEscape => {
                reasons.insert(MarkabilityFailure::OpaqueEscape);
            }
            SnapshotVerdict::Recursive => {
                reasons.insert(MarkabilityFailure::Recursive);
            }
            SnapshotVerdict::VolatileOrAtomic => {
                reasons.insert(MarkabilityFailure::VolatileOrAtomic);
            }
        }
        if !witness.target_types_agree {
            reasons.insert(MarkabilityFailure::TargetTypeMismatch);
        }
        if !witness.copy_scalar {
            reasons.insert(MarkabilityFailure::NonCopyScalar);
        }
        if witness.unknown_caller {
            reasons.insert(MarkabilityFailure::UnknownCaller);
        }
    }
    if !seen {
        reasons.insert(MarkabilityFailure::MissingWitness);
    }
    if reasons.is_empty() {
        AllWitnessesGate::Discharged
    } else {
        AllWitnessesGate::Demote { reasons }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct C9MarkKey {
    pub(crate) caller: FnKey,
    pub(crate) location: MirLocationKey,
    pub(crate) targets: Vec<FnKey>,
    pub(crate) pair: FunctionPairKey,
    pub(crate) actuals: (SlotKey, SlotKey),
    pub(crate) shared_side: PairSide,
    pub(crate) pointee_type: String,
}

impl C9MarkKey {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        caller: FnKey,
        location: MirLocationKey,
        targets: impl IntoIterator<Item = FnKey>,
        callee: FnKey,
        left_param: u32,
        left_actual: SlotKey,
        right_param: u32,
        right_actual: SlotKey,
        shared_side: PairSide,
        pointee_type: String,
    ) -> Option<Self> {
        let pair = FunctionPairKey::new(callee, left_param, right_param)?;
        let (actuals, shared_side) = if left_param < right_param {
            ((left_actual, right_actual), shared_side)
        } else {
            (
                (right_actual, left_actual),
                match shared_side {
                    PairSide::Left => PairSide::Right,
                    PairSide::Right => PairSide::Left,
                },
            )
        };
        let mut targets = targets.into_iter().collect::<Vec<_>>();
        targets.sort_unstable();
        targets.dedup();
        Some(Self {
            caller,
            location,
            targets,
            pair,
            actuals,
            shared_side,
            pointee_type,
        })
    }
}

pub(crate) fn plan_c9_marks(
    witnesses: impl IntoIterator<Item = (C9MarkKey, WitnessMarkability)>,
) -> BTreeSet<C9MarkKey> {
    let witnesses = witnesses.into_iter().collect::<Vec<_>>();
    if !matches!(
        all_witnesses_gate(witnesses.iter().map(|(_, evidence)| *evidence)),
        AllWitnessesGate::Discharged
    ) {
        return BTreeSet::new();
    }
    witnesses.into_iter().map(|(mark, _)| mark).collect()
}

/// The only A5 call-world policy authorized for loop 2. Keeping the complete
/// option set here makes the absence of an O1 build/config arm testable.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum A5World {
    ClosedWorldFrozenGraph,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum A5Mode {
    Baseline,
    PreciseReplay,
    CoarseConstraint,
}

impl A5Mode {
    pub(crate) fn production() -> Self {
        Self::PreciseReplay
    }

    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Baseline => "baseline",
            Self::PreciseReplay => "precise_replay",
            Self::CoarseConstraint => "coarse_constraint",
        }
    }

    pub(crate) fn proposed_landing() -> Self {
        Self::PreciseReplay
    }

    pub(crate) fn is_pricing_control(self) -> bool {
        self == Self::CoarseConstraint
    }
}

pub(crate) fn apply_coarse_constraints(
    mode: A5Mode,
    solver: &KindSolver,
    pairs: impl IntoIterator<Item = (SlotRef, SlotRef)>,
) -> usize {
    if mode != A5Mode::CoarseConstraint {
        return 0;
    }
    let mut canonical = BTreeMap::new();
    for (left, right) in pairs {
        assert_ne!(left, right, "A5 coarse pair must contain distinct slots");
        let left_key = SlotKey::of(left);
        let right_key = SlotKey::of(right);
        let (key, pair) = if left_key < right_key {
            ((left_key, right_key), (left, right))
        } else {
            ((right_key, left_key), (right, left))
        };
        canonical.insert(key, pair);
    }
    for &(left, right) in canonical.values() {
        solver.add_a5_coarse_exclusion(left, right);
    }
    canonical.len()
}

impl A5World {
    pub(crate) const ALL: [Self; 1] = [Self::ClosedWorldFrozenGraph];

    pub(crate) fn parse(value: &str) -> Result<Self, String> {
        match value {
            "closed_world_frozen_graph" => Ok(Self::ClosedWorldFrozenGraph),
            other => Err(format!("unsupported A5 world {other:?}")),
        }
    }

    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::ClosedWorldFrozenGraph => "closed_world_frozen_graph",
        }
    }

    pub(crate) fn seeds_unknown_callers(self) -> bool {
        match self {
            Self::ClosedWorldFrozenGraph => false,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum WholeProgramAttestation {
    FrozenBenchmarkGraph,
}

impl WholeProgramAttestation {
    pub(crate) const ENV: &'static str = "CRAT_BO_A5_ATTESTATION";

    pub(crate) fn current() -> Option<Self> {
        match std::env::var(Self::ENV) {
            Err(std::env::VarError::NotPresent) => None,
            Ok(value) => match value.as_str() {
                "none" => None,
                "frozen_benchmark_graph" => Some(Self::FrozenBenchmarkGraph),
                other => panic!(
                    "{} must be none or frozen_benchmark_graph; got {other:?}",
                    Self::ENV
                ),
            },
            Err(error) => panic!("{} is not valid Unicode: {error}", Self::ENV),
        }
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct AbiBoundaryFacts {
    pub(crate) externally_visible: bool,
    pub(crate) address_taken: bool,
    pub(crate) function_target: bool,
    pub(crate) unresolved_target: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum AbiGuardReason {
    ExternallyVisible,
    AddressTaken,
    FunctionTarget,
    UnresolvedTarget,
}

impl AbiGuardReason {
    fn label(self) -> &'static str {
        match self {
            Self::ExternallyVisible => "externally-visible",
            Self::AddressTaken => "address-taken",
            Self::FunctionTarget => "function-target",
            Self::UnresolvedTarget => "unresolved-target",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum AbiGuardDisposition {
    Permitted { attested: bool },
    Refused { reasons: BTreeSet<AbiGuardReason> },
}

impl AbiGuardDisposition {
    pub(crate) fn refused(reasons: impl IntoIterator<Item = AbiGuardReason>) -> Self {
        Self::Refused {
            reasons: reasons.into_iter().collect(),
        }
    }

    pub(crate) fn stamp(&self) -> String {
        match self {
            Self::Permitted { attested: true } => {
                "permitted:measurement-frozen-graph-attested".to_owned()
            }
            Self::Permitted { attested: false } => "permitted:internal".to_owned(),
            Self::Refused { reasons } => format!(
                "refused:{}",
                reasons
                    .iter()
                    .map(|reason| reason.label())
                    .collect::<Vec<_>>()
                    .join(",")
            ),
        }
    }
}

pub(crate) fn a5_abi_guard(
    facts: &AbiBoundaryFacts,
    attestation: Option<WholeProgramAttestation>,
) -> AbiGuardDisposition {
    if attestation == Some(WholeProgramAttestation::FrozenBenchmarkGraph) {
        return AbiGuardDisposition::Permitted { attested: true };
    }

    let mut reasons = BTreeSet::new();
    reasons.extend(
        [
            (facts.externally_visible, AbiGuardReason::ExternallyVisible),
            (facts.address_taken, AbiGuardReason::AddressTaken),
            (facts.function_target, AbiGuardReason::FunctionTarget),
            (facts.unresolved_target, AbiGuardReason::UnresolvedTarget),
        ]
        .into_iter()
        .filter_map(|(present, reason)| present.then_some(reason)),
    );
    if reasons.is_empty() {
        AbiGuardDisposition::Permitted { attested: false }
    } else {
        AbiGuardDisposition::Refused { reasons }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct A5SummaryArtifact {
    pub(crate) summary_tsv: String,
    pub(crate) receipt: String,
}

pub(crate) fn render_summary_artifact(
    fixpoint: &MayOverlapFixpoint,
    mode: A5Mode,
    guard: &AbiGuardDisposition,
) -> A5SummaryArtifact {
    let world = A5World::ClosedWorldFrozenGraph;
    let mut summary_tsv = String::from(
        "callee_fn\tleft_param\tright_param\tcaller_fn\tblock\tstatement_index\t\
         left_variant\tleft_owner\tleft_slot\tright_variant\tright_owner\tright_slot\t\
         a5_world\ta5_mode\n",
    );
    for (pair, witness) in fixpoint.summary.ordered_rows() {
        let params = pair.params();
        let (left, right) = witness.actuals();
        summary_tsv.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            pair.function(),
            params.first(),
            params.second(),
            witness.caller,
            witness.location.block,
            witness.location.statement_index,
            left.variant,
            left.owner,
            left.slot,
            right.variant,
            right.owner,
            right.slot,
            world.label(),
            mode.label(),
        ));
    }
    let pair_count = fixpoint.summary.witnesses.len();
    let witness_count = fixpoint
        .summary
        .witnesses
        .values()
        .map(BTreeSet::len)
        .sum::<usize>();
    let sccs = fixpoint
        .sccs
        .iter()
        .map(|component| {
            component
                .iter()
                .map(u32::to_string)
                .collect::<Vec<_>>()
                .join(",")
        })
        .collect::<Vec<_>>()
        .join(";");
    let receipt = format!(
        "schema=a5-summary-v1\nstatus=ok\ndata=true\na5_mode={}\na5_world={}\n\
         unknown_caller_seeding={}\nabi_guard={}\npairs={pair_count}\nwitnesses={witness_count}\n\
         scc_count={}\nsccs={}\nscc_iterations={}\nunresolved=0\n",
        mode.label(),
        world.label(),
        world.seeds_unknown_callers(),
        guard.stamp(),
        fixpoint.sccs.len(),
        sccs,
        fixpoint.scc_iterations,
    );
    A5SummaryArtifact {
        summary_tsv,
        receipt,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn slot(owner: u32, slot: usize) -> SlotKey {
        SlotKey {
            variant: 1,
            owner,
            slot,
        }
    }

    fn witness(
        callee: u32,
        caller: u32,
        block: u32,
        left_param: u32,
        left_actual: SlotKey,
        right_param: u32,
        right_actual: SlotKey,
    ) -> CallSiteWitnessKey {
        CallSiteWitnessKey::new(
            callee,
            left_param,
            left_actual,
            right_param,
            right_actual,
            caller,
            MirLocationKey::new(block, 0),
        )
        .expect("distinct formal parameters")
    }

    #[test]
    fn parameter_pair_keys_are_unordered_and_reject_self_pairs() {
        let forward = ParamPair::new(2, 5).expect("distinct pair");
        let reverse = ParamPair::new(5, 2).expect("distinct pair");

        assert_eq!(forward, reverse);
        assert_eq!((forward.first(), forward.second()), (2, 5));
        assert_eq!(ParamPair::new(3, 3), None);
    }

    #[test]
    fn witness_keys_canonicalize_formals_and_actual_correspondence() {
        let left = slot(10, 2);
        let right = slot(10, 7);
        let forward = witness(8, 3, 4, 1, left, 6, right);
        let reverse = witness(8, 3, 4, 6, right, 1, left);

        assert_eq!(forward, reverse);
        assert_eq!(forward.pair(), FunctionPairKey::new(8, 1, 6).unwrap());
        assert_eq!(forward.actuals(), (left, right));
    }

    #[test]
    fn may_overlap_union_is_monotone_and_deduplicates_witnesses() {
        let first = witness(8, 3, 4, 1, slot(3, 1), 2, slot(3, 2));
        let second = witness(8, 5, 1, 1, slot(5, 4), 2, slot(5, 9));
        let pair = first.pair();
        let mut left = MayOverlapSummary::default();
        let mut right = MayOverlapSummary::default();
        assert!(left.insert(first));
        assert!(right.insert(first));
        assert!(right.insert(second));

        assert!(left.union_from(&right));
        assert!(!left.union_from(&right));
        assert_eq!(left.witnesses(pair).len(), 2);
    }

    #[test]
    fn summary_order_is_stable_across_registration_order() {
        let witnesses = [
            witness(9, 7, 2, 4, slot(7, 8), 1, slot(7, 3)),
            witness(8, 5, 3, 2, slot(5, 9), 1, slot(5, 4)),
            witness(8, 3, 1, 1, slot(3, 1), 2, slot(3, 2)),
        ];
        let mut forward = MayOverlapSummary::default();
        let mut reverse = MayOverlapSummary::default();
        for witness in witnesses {
            forward.insert(witness);
        }
        for witness in witnesses.into_iter().rev() {
            reverse.insert(witness);
        }

        assert_eq!(forward.ordered_rows(), reverse.ordered_rows());
        assert_eq!(
            forward
                .ordered_rows()
                .into_iter()
                .map(|(pair, _)| pair.function())
                .collect::<Vec<_>>(),
            vec![8, 8, 9]
        );
    }

    #[test]
    fn missing_or_incomplete_positive_evidence_is_conservatively_overlap() {
        let missing = PairFacts::<String>::default();
        let incomplete = PairFacts {
            points_to: SetPairEvidence::Incomplete {
                left: BTreeSet::from(["left".to_owned()]),
                right: BTreeSet::from(["right".to_owned()]),
            },
            ..PairFacts::default()
        };
        let complete = PairFacts {
            origins: SetPairEvidence::Complete {
                left: BTreeSet::from(["left".to_owned()]),
                right: BTreeSet::from(["right".to_owned()]),
            },
            ..PairFacts::default()
        };
        let storage_alias_dominates = PairFacts::<String> {
            storage_alias: true,
            projection_disjoint: true,
            ..PairFacts::default()
        };

        assert_eq!(classify_pair(&missing), PairClass::NotProvenDisjoint);
        assert_eq!(classify_pair(&incomplete), PairClass::NotProvenDisjoint);
        assert_eq!(classify_pair(&complete), PairClass::ProvenDisjoint);
        assert_eq!(
            classify_pair(&storage_alias_dominates),
            PairClass::NotProvenDisjoint
        );
    }

    #[test]
    fn o2_is_the_only_world_and_never_seeds_unknown_callers() {
        assert_eq!(A5World::ALL, [A5World::ClosedWorldFrozenGraph]);
        assert_eq!(
            A5World::parse("closed_world_frozen_graph"),
            Ok(A5World::ClosedWorldFrozenGraph)
        );
        assert!(A5World::parse("open_world").is_err());
        assert!(!A5World::ClosedWorldFrozenGraph.seeds_unknown_callers());
    }

    #[test]
    fn accepted_precise_mode_is_the_single_production_selector() {
        assert_eq!(A5Mode::production(), A5Mode::PreciseReplay);
        assert_eq!(A5Mode::proposed_landing(), A5Mode::PreciseReplay);
        assert!(A5Mode::CoarseConstraint.is_pricing_control());
    }

    #[test]
    fn abi_guard_refuses_externally_visible_without_attestation() {
        let facts = AbiBoundaryFacts {
            externally_visible: true,
            ..AbiBoundaryFacts::default()
        };

        assert_eq!(
            a5_abi_guard(&facts, None),
            AbiGuardDisposition::refused([AbiGuardReason::ExternallyVisible])
        );
    }

    #[test]
    fn abi_guard_refuses_address_taken_without_attestation() {
        let facts = AbiBoundaryFacts {
            address_taken: true,
            ..AbiBoundaryFacts::default()
        };

        assert_eq!(
            a5_abi_guard(&facts, None),
            AbiGuardDisposition::refused([AbiGuardReason::AddressTaken])
        );
    }

    #[test]
    fn abi_guard_refuses_function_target_groups_without_attestation() {
        let facts = AbiBoundaryFacts {
            function_target: true,
            ..AbiBoundaryFacts::default()
        };

        assert_eq!(
            a5_abi_guard(&facts, None),
            AbiGuardDisposition::refused([AbiGuardReason::FunctionTarget])
        );
    }

    #[test]
    fn abi_guard_refuses_unresolved_targets_without_attestation() {
        let facts = AbiBoundaryFacts {
            unresolved_target: true,
            ..AbiBoundaryFacts::default()
        };

        assert_eq!(
            a5_abi_guard(&facts, None),
            AbiGuardDisposition::refused([AbiGuardReason::UnresolvedTarget])
        );
    }

    #[test]
    fn abi_guard_collects_every_refusal_reason() {
        let facts = AbiBoundaryFacts {
            externally_visible: true,
            address_taken: true,
            function_target: true,
            unresolved_target: true,
        };

        assert_eq!(
            a5_abi_guard(&facts, None),
            AbiGuardDisposition::refused([
                AbiGuardReason::ExternallyVisible,
                AbiGuardReason::AddressTaken,
                AbiGuardReason::FunctionTarget,
                AbiGuardReason::UnresolvedTarget,
            ])
        );
    }

    #[test]
    fn frozen_graph_attestation_permits_a_resolved_abi_boundary() {
        let facts = AbiBoundaryFacts {
            externally_visible: true,
            address_taken: true,
            function_target: true,
            unresolved_target: false,
        };

        assert_eq!(
            a5_abi_guard(&facts, Some(WholeProgramAttestation::FrozenBenchmarkGraph)),
            AbiGuardDisposition::Permitted { attested: true }
        );
    }

    #[test]
    fn batch_attestation_permits_unresolved_while_product_context_refuses() {
        let facts = AbiBoundaryFacts {
            unresolved_target: true,
            ..AbiBoundaryFacts::default()
        };

        let batch = a5_abi_guard(&facts, Some(WholeProgramAttestation::FrozenBenchmarkGraph));
        assert_eq!(batch, AbiGuardDisposition::Permitted { attested: true });
        assert_eq!(batch.stamp(), "permitted:measurement-frozen-graph-attested");
        assert_eq!(
            a5_abi_guard(&facts, None),
            AbiGuardDisposition::refused([AbiGuardReason::UnresolvedTarget])
        );
    }

    #[test]
    fn private_resolved_boundary_needs_no_global_attestation() {
        assert_eq!(
            a5_abi_guard(&AbiBoundaryFacts::default(), None),
            AbiGuardDisposition::Permitted { attested: false }
        );
    }

    #[test]
    fn scc_fixpoint_kills_the_one_pass_mutation() {
        let pair1 = FunctionPairKey::new(1, 1, 2).unwrap();
        let pair2 = FunctionPairKey::new(2, 1, 2).unwrap();
        let pair3 = FunctionPairKey::new(3, 1, 2).unwrap();
        let seed = CallTransfer::direct(witness(1, 0, 0, 1, slot(0, 1), 2, slot(0, 2)));
        let one_to_two =
            CallTransfer::forwarded(witness(2, 1, 1, 1, slot(1, 1), 2, slot(1, 2)), pair1).unwrap();
        let two_to_one =
            CallTransfer::forwarded(witness(1, 2, 2, 1, slot(2, 1), 2, slot(2, 2)), pair2).unwrap();
        let two_to_three =
            CallTransfer::forwarded(witness(3, 2, 3, 1, slot(2, 3), 2, slot(2, 4)), pair2).unwrap();

        let solved = solve_may_overlap([two_to_three, two_to_one, one_to_two, seed]);

        assert!(solved.summary().contains(pair1));
        assert!(solved.summary().contains(pair2));
        assert!(solved.summary().contains(pair3));
        assert!(solved.scc_iterations() > solved.sccs().len());
    }

    #[test]
    fn transfer_direction_is_caller_to_callee_only() {
        let caller_pair = FunctionPairKey::new(1, 1, 2).unwrap();
        let callee_pair = FunctionPairKey::new(2, 1, 2).unwrap();
        let callee_seed = CallTransfer::direct(witness(2, 0, 0, 1, slot(0, 1), 2, slot(0, 2)));
        let caller_to_callee =
            CallTransfer::forwarded(witness(2, 1, 1, 1, slot(1, 1), 2, slot(1, 2)), caller_pair)
                .unwrap();

        let solved = solve_may_overlap([caller_to_callee, callee_seed]);

        assert!(!solved.summary().contains(caller_pair));
        assert!(solved.summary().contains(callee_pair));
    }

    #[test]
    fn fixpoint_is_byte_stable_under_unsorted_registration() {
        let pair1 = FunctionPairKey::new(1, 1, 2).unwrap();
        let pair2 = FunctionPairKey::new(2, 1, 2).unwrap();
        let transfers = [
            CallTransfer::direct(witness(1, 0, 4, 1, slot(0, 1), 2, slot(0, 2))),
            CallTransfer::forwarded(witness(2, 1, 3, 1, slot(1, 1), 2, slot(1, 2)), pair1).unwrap(),
            CallTransfer::direct(witness(2, 0, 2, 1, slot(0, 3), 2, slot(0, 4))),
        ];
        let forward = solve_may_overlap(transfers);
        let reverse = solve_may_overlap(transfers.into_iter().rev());

        assert!(forward.summary().contains(pair2));
        assert_eq!(forward, reverse);
        assert_eq!(
            forward.summary().ordered_rows(),
            reverse.summary().ordered_rows()
        );
    }

    #[test]
    fn forwarded_transfer_rejects_a_reverse_edge_dependency() {
        let wrong_caller = FunctionPairKey::new(9, 1, 2).unwrap();
        let edge = witness(2, 1, 1, 1, slot(1, 1), 2, slot(1, 2));

        assert!(CallTransfer::forwarded(edge, wrong_caller).is_err());
    }

    #[test]
    fn summary_artifact_is_byte_identical_under_reverse_registration() {
        let pair1 = FunctionPairKey::new(1, 1, 2).unwrap();
        let transfers = [
            CallTransfer::direct(witness(1, 0, 4, 1, slot(0, 1), 2, slot(0, 2))),
            CallTransfer::forwarded(witness(2, 1, 3, 1, slot(1, 1), 2, slot(1, 2)), pair1).unwrap(),
        ];
        let forward = render_summary_artifact(
            &solve_may_overlap(transfers),
            A5Mode::PreciseReplay,
            &AbiGuardDisposition::Permitted { attested: true },
        );
        let reverse = render_summary_artifact(
            &solve_may_overlap(transfers.into_iter().rev()),
            A5Mode::PreciseReplay,
            &AbiGuardDisposition::Permitted { attested: true },
        );

        assert_eq!(forward, reverse);
        assert_eq!(forward.summary_tsv.lines().count(), 3);
    }

    #[test]
    fn summary_receipt_stamps_mode_world_guard_and_counts() {
        let solved = solve_may_overlap([CallTransfer::direct(witness(
            1,
            0,
            4,
            1,
            slot(0, 1),
            2,
            slot(0, 2),
        ))]);
        let artifact = render_summary_artifact(
            &solved,
            A5Mode::PreciseReplay,
            &AbiGuardDisposition::refused([
                AbiGuardReason::ExternallyVisible,
                AbiGuardReason::AddressTaken,
            ]),
        );

        assert!(artifact.receipt.contains("a5_mode=precise_replay\n"));
        assert!(
            artifact
                .receipt
                .contains("a5_world=closed_world_frozen_graph\n")
        );
        assert!(artifact.receipt.contains("unknown_caller_seeding=false\n"));
        assert!(
            artifact
                .receipt
                .contains("abi_guard=refused:externally-visible,address-taken\n")
        );
        assert!(artifact.receipt.contains("pairs=1\nwitnesses=1\n"));
    }

    #[test]
    fn foster_join_classifies_mut_mut() {
        let joined = join_witness_mutability([Some(true)], [Some(true)]);
        assert_eq!(joined.class, WitnessMutability::MutMut);
        assert_eq!(joined.missing_defaults, 0);
    }

    #[test]
    fn foster_join_classifies_mut_read_only_with_side() {
        assert_eq!(
            join_witness_mutability([Some(true)], [Some(false)]).class,
            WitnessMutability::MutReadOnly {
                read_only: PairSide::Right,
            }
        );
    }

    #[test]
    fn foster_join_classifies_shared_shared() {
        assert_eq!(
            join_witness_mutability([Some(false)], [Some(false)]).class,
            WitnessMutability::SharedShared
        );
    }

    #[test]
    fn foster_join_defaults_missing_facts_to_mutable() {
        let joined = join_witness_mutability([None], [Some(false)]);
        assert_eq!(
            joined.class,
            WitnessMutability::MutReadOnly {
                read_only: PairSide::Right,
            }
        );
        assert_eq!(joined.missing_defaults, 1);
    }

    #[test]
    fn foster_join_ors_mutability_across_resolved_targets() {
        let joined = join_witness_mutability([Some(false), Some(true)], [Some(false), Some(false)]);
        assert_eq!(
            joined.class,
            WitnessMutability::MutReadOnly {
                read_only: PairSide::Right,
            }
        );
        assert_eq!(joined.missing_defaults, 0);
    }

    fn effects(events: &[SnapshotEffect], edges: &[(usize, usize)]) -> SnapshotEffectGraph {
        SnapshotEffectGraph::new(events.to_vec(), edges.iter().copied()).unwrap()
    }

    #[test]
    fn snapshot_read_before_write_is_markable() {
        let graph = effects(
            &[SnapshotEffect::SharedRead, SnapshotEffect::MutableWrite],
            &[(0, 1)],
        );
        assert_eq!(
            check_snapshot_equivalence(&graph),
            SnapshotVerdict::Markable
        );
    }

    #[test]
    fn snapshot_read_after_write_is_unmarkable() {
        let graph = effects(
            &[SnapshotEffect::MutableWrite, SnapshotEffect::SharedRead],
            &[(0, 1)],
        );
        assert_eq!(
            check_snapshot_equivalence(&graph),
            SnapshotVerdict::ReadAfterWrite
        );
    }

    #[test]
    fn snapshot_conditional_write_reaching_read_is_unmarkable() {
        let graph = effects(
            &[
                SnapshotEffect::None,
                SnapshotEffect::MutableWrite,
                SnapshotEffect::None,
                SnapshotEffect::SharedRead,
            ],
            &[(0, 1), (0, 2), (1, 3), (2, 3)],
        );
        assert_eq!(
            check_snapshot_equivalence(&graph),
            SnapshotVerdict::ReadAfterWrite
        );
    }

    #[test]
    fn snapshot_opaque_escape_and_recursion_fail_closed() {
        let opaque = effects(&[SnapshotEffect::OpaqueEscape], &[]);
        let recursive = SnapshotEffectGraph::recursive(vec![SnapshotEffect::SharedRead]);
        assert_eq!(
            check_snapshot_equivalence(&opaque),
            SnapshotVerdict::OpaqueEscape
        );
        assert_eq!(
            check_snapshot_equivalence(&recursive),
            SnapshotVerdict::Recursive
        );
    }

    #[test]
    fn snapshot_volatile_and_atomic_effects_are_excluded() {
        for effect in [SnapshotEffect::Volatile, SnapshotEffect::Atomic] {
            assert_eq!(
                check_snapshot_equivalence(&effects(&[effect], &[])),
                SnapshotVerdict::VolatileOrAtomic
            );
        }
    }

    fn markability(effect: SnapshotVerdict) -> WitnessMarkability {
        WitnessMarkability {
            effect,
            target_types_agree: true,
            copy_scalar: true,
            unknown_caller: false,
        }
    }

    #[test]
    fn w8_read_after_write_kills_discharge() {
        assert!(matches!(
            all_witnesses_gate([markability(SnapshotVerdict::ReadAfterWrite)]),
            AllWitnessesGate::Demote { .. }
        ));
    }

    #[test]
    fn every_nonmarkable_snapshot_verdict_kills_discharge_at_the_all_witness_gate() {
        for verdict in [
            SnapshotVerdict::ReadAfterWrite,
            SnapshotVerdict::OpaqueEscape,
            SnapshotVerdict::Recursive,
            SnapshotVerdict::VolatileOrAtomic,
        ] {
            assert!(
                matches!(
                    all_witnesses_gate([markability(verdict)]),
                    AllWitnessesGate::Demote { .. }
                ),
                "{verdict:?} escaped the all-witness gate"
            );
        }
    }

    #[test]
    fn w9_one_unmarkable_witness_kills_partial_discharge() {
        assert!(matches!(
            all_witnesses_gate([
                markability(SnapshotVerdict::Markable),
                markability(SnapshotVerdict::OpaqueEscape),
            ]),
            AllWitnessesGate::Demote { .. }
        ));
    }

    #[test]
    fn w10_target_type_disagreement_and_noncopy_demote() {
        let mut mismatch = markability(SnapshotVerdict::Markable);
        mismatch.target_types_agree = false;
        let mut noncopy = markability(SnapshotVerdict::Markable);
        noncopy.copy_scalar = false;
        assert!(matches!(
            all_witnesses_gate([mismatch]),
            AllWitnessesGate::Demote { .. }
        ));
        assert!(matches!(
            all_witnesses_gate([noncopy]),
            AllWitnessesGate::Demote { .. }
        ));
    }

    #[test]
    fn unknown_caller_witness_kills_discharge() {
        let mut unknown = markability(SnapshotVerdict::Markable);
        unknown.unknown_caller = true;
        assert!(matches!(
            all_witnesses_gate([unknown]),
            AllWitnessesGate::Demote { .. }
        ));
    }

    #[test]
    fn every_markable_witness_discharges_pair() {
        assert_eq!(
            all_witnesses_gate([
                markability(SnapshotVerdict::Markable),
                markability(SnapshotVerdict::Markable),
            ]),
            AllWitnessesGate::Discharged
        );
    }

    fn c9(block: u32) -> C9MarkKey {
        C9MarkKey::new(
            3,
            MirLocationKey::new(block, 0),
            [8, 7, 8],
            7,
            1,
            slot(3, 1),
            2,
            slot(3, 2),
            PairSide::Right,
            "i32".to_owned(),
        )
        .unwrap()
    }

    #[test]
    fn c9_mark_identity_sorts_targets_and_is_location_typed() {
        let first = c9(1);
        let second = c9(2);
        assert_eq!(first.targets, vec![7, 8]);
        assert_ne!(first, second);
    }

    #[test]
    fn c9_planner_emits_all_marks_or_none() {
        let good = markability(SnapshotVerdict::Markable);
        assert_eq!(plan_c9_marks([(c9(1), good), (c9(2), good)]).len(), 2);
        let bad = markability(SnapshotVerdict::ReadAfterWrite);
        assert!(plan_c9_marks([(c9(1), good), (c9(2), bad)]).is_empty());
    }
}
