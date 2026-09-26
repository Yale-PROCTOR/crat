//! Call-matched candidate transport. Static applications are not dynamic
//! allocation generations; origin completeness and licensing gates stay pending.

use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};

use super::{
    super::{
        ownership_boundary::{Role, Variables},
        ownership_occurrence::Availability,
    },
    facts::{EquationId, Facts},
    transport::{CandidateGraph, Evidence, Node},
};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub(crate) struct CallKey {
    pub(crate) construction: u32,
    pub(crate) caller: String,
    pub(crate) block: u32,
    pub(crate) statement: usize,
    pub(crate) callee: String,
}

/// Exact static application chains remain distinct through enclosing calls.
/// A recursive fold is explicitly not an exact allocation identity; T12/G-ID
/// must certify its per-invocation binder before it can support a grant.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub(crate) enum SourceLineage {
    Exact(Vec<CallKey>),
    Recursive { application: CallKey },
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub(crate) struct SourceInstance {
    pub(crate) endpoint: EquationId,
    pub(crate) lineage: SourceLineage,
}

impl SourceLineage {
    fn through(&self, call: &CallKey) -> Self {
        match self {
            Self::Exact(calls) if !calls.contains(call) => {
                let mut applications = vec![call.clone()];
                applications.extend(calls.iter().cloned());
                Self::Exact(applications)
            }
            _ => Self::Recursive {
                application: call.clone(),
            },
        }
    }
}

impl SourceInstance {
    fn through(&self, call: &CallKey) -> Self {
        Self {
            endpoint: self.endpoint,
            lineage: self.lineage.through(call),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub(crate) enum TerminalTarget {
    Free(EquationId),
    Output { node: Node, ordinal: usize },
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub(crate) struct TerminalInstance {
    pub(crate) target: TerminalTarget,
    pub(crate) lineage: SourceLineage,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct Meet {
    pub(crate) source: SourceInstance,
    pub(crate) terminal: TerminalInstance,
    #[serde(with = "ordered_pairs")]
    pub(crate) guards: BTreeMap<EquationId, bool>,
    proof: Vec<Step>,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) enum InputStoreStatus {
    MissingCorrespondence,
    Observed,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct InputStoreAnchor {
    pub(crate) source: SourceInstance,
    #[serde(with = "ordered_pairs")]
    pub(crate) guards: BTreeMap<EquationId, bool>,
    proof: Vec<Step>,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct InputStoreRoute {
    pub(crate) formal_input: Node,
    pub(crate) formal_output: Node,
    pub(crate) actual_input: Node,
    pub(crate) actual_output: Node,
    pub(crate) input_boundary: usize,
    pub(crate) output_boundary: usize,
    #[serde(with = "ordered_pairs")]
    pub(crate) guards: BTreeMap<EquationId, bool>,
    /// Empty anchors is an explicit unanchored application, never permission.
    pub(crate) anchors: Vec<InputStoreAnchor>,
    pub(crate) meets: Vec<Meet>,
    /// All terminals visible from the same caller source, including partners
    /// which split before this store. No selector valuation filters this list.
    pub(crate) source_terminals: Vec<Meet>,
    store_witness: Vec<Step>,
    application: Step,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct InputStoreApplication {
    pub(crate) call: CallKey,
    pub(crate) store: EquationId,
    pub(crate) status: InputStoreStatus,
    pub(crate) routes: Vec<InputStoreRoute>,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct ForwardedReturn {
    pub(crate) output: Meet,
    pub(crate) continuation: Meet,
    pub(crate) call: CallKey,
    pub(crate) call_path: Vec<CallKey>,
    pub(crate) returned: Node,
    pub(crate) formal: Node,
    pub(crate) receiver_old: Node,
    pub(crate) receiver: Node,
    pub(crate) exit_boundary: usize,
    pub(crate) receiver_boundary: usize,
    pub(crate) receiver_consume: usize,
    pub(crate) exit_equation: EquationId,
    pub(crate) receiver_equation: EquationId,
    pub(crate) receiver_old_zero: EquationId,
    #[serde(with = "ordered_pairs")]
    pub(crate) guards: BTreeMap<EquationId, bool>,
    application: Step,
    relation_witness: Vec<Step>,
}

type Scope = (u32, String);
type Guards = BTreeMap<EquationId, bool>;

/// Full receiver forwarding justified by one exact subtree-fold contract.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct MemberReturn {
    pub(crate) forwarding: ForwardedReturn,
    pub(crate) membership: Box<super::fold_subtree::Membership>,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct FoldedReturn {
    pub(crate) forwarding: ForwardedReturn,
    pub(crate) guard: EquationId,
    pub(crate) fold: Box<super::fold_call::Proof>,
}

/// JSON objects cannot represent these compound keys. Preserve BTreeMap order
/// as key/value pairs and refuse duplicate keys, including identical values.
pub(crate) mod ordered_pairs {
    use std::collections::BTreeMap;

    use serde::{Deserialize, Deserializer, Serialize, Serializer, de::Error, ser::SerializeSeq};

    pub(crate) fn serialize<K: Serialize, V: Serialize, S: Serializer>(
        map: &BTreeMap<K, V>,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        let mut sequence = serializer.serialize_seq(Some(map.len()))?;
        for pair in map {
            sequence.serialize_element(&pair)?;
        }
        sequence.end()
    }

    pub(crate) fn deserialize<
        'de,
        K: Deserialize<'de> + Ord,
        V: Deserialize<'de>,
        D: Deserializer<'de>,
    >(
        deserializer: D,
    ) -> Result<BTreeMap<K, V>, D::Error> {
        let pairs = Vec::<(K, V)>::deserialize(deserializer)?;
        let mut result = BTreeMap::new();
        for (key, value) in pairs {
            if result.insert(key, value).is_some() {
                return Err(D::Error::custom("duplicate ordered-map key"));
            }
        }
        Ok(result)
    }
}

/// era-5c R541-3 / report 048: write a sequence as `[e0,e1,…]` with each element
/// passed through a `serde_json::Value` on its own. Byte-identical to the element
/// run of `to_writer(&to_value(whole))` (a `Value` only sorts OBJECT keys, and
/// every element is sorted the same way alone), with memory bounded by the
/// largest element instead of the whole sequence.
pub(crate) fn write_value_seq<T: serde::Serialize>(
    w: &mut dyn std::io::Write,
    items: impl IntoIterator<Item = T>,
) -> Result<(), String> {
    w.write_all(b"[").map_err(|e| e.to_string())?;
    for (n, item) in items.into_iter().enumerate() {
        if n > 0 {
            w.write_all(b",").map_err(|e| e.to_string())?;
        }
        let value = serde_json::to_value(&item).map_err(|e| e.to_string())?;
        serde_json::to_writer(&mut *w, &value).map_err(|e| e.to_string())?;
    }
    w.write_all(b"]").map_err(|e| e.to_string())
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
enum Seed {
    Input(Node),
    Source(SourceInstance),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
enum Destination {
    Port(Node),
    Terminal(TerminalInstance),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
struct Relation {
    scope: Scope,
    seed: Seed,
    output: Destination,
    #[serde(with = "ordered_pairs")]
    guards: Guards,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
struct BoundaryPart {
    #[serde(with = "ordered_pairs")]
    guards: Guards,
    construction: u32,
    ordinal: usize,
    #[serde(flatten)]
    binding: BoundaryBinding,
    formal: Node,
    actual: Node,
}

/// Native JSON retains its original matched index. A folded member has no
/// native pair index and must be authenticated through its own certificate.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
#[serde(untagged)]
enum BoundaryBinding {
    Native {
        matched: usize,
    },
    Folded {
        folded_member: Box<super::fold_subtree::Membership>,
    },
}
impl<'de> serde::Deserialize<'de> for BoundaryPart {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        fn present<'de, D: serde::Deserializer<'de>>(
            deserializer: D,
        ) -> Result<Option<serde_json::Value>, D::Error> {
            <serde_json::Value as serde::Deserialize>::deserialize(deserializer).map(Some)
        }
        #[derive(serde::Deserialize)]
        struct Wire {
            #[serde(with = "ordered_pairs")]
            guards: Guards,
            construction: u32,
            ordinal: usize,
            #[serde(default, deserialize_with = "present")]
            matched: Option<serde_json::Value>,
            #[serde(default, deserialize_with = "present")]
            folded_member: Option<serde_json::Value>,
            formal: Node,
            actual: Node,
        }
        let wire = <Wire as serde::Deserialize>::deserialize(deserializer)?;
        let binding = match (wire.matched, wire.folded_member) {
            (Some(_), Some(_)) => {
                return Err(serde::de::Error::custom("ambiguous boundary binding"));
            }
            (Some(value), None) => BoundaryBinding::Native {
                matched: serde_json::from_value(value).map_err(serde::de::Error::custom)?,
            },
            (None, Some(value)) => BoundaryBinding::Folded {
                folded_member: serde_json::from_value(value).map_err(serde::de::Error::custom)?,
            },
            (None, None) => return Err(serde::de::Error::custom("missing boundary binding")),
        };
        Ok(Self {
            guards: wire.guards,
            construction: wire.construction,
            ordinal: wire.ordinal,
            binding,
            formal: wire.formal,
            actual: wire.actual,
        })
    }
}

impl BoundaryPart {
    fn native_match(&self) -> Option<usize> {
        match &self.binding {
            BoundaryBinding::Native { matched } => Some(*matched),
            BoundaryBinding::Folded { .. } => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
enum Step {
    Local(Evidence),
    Apply {
        call: CallKey,
        relation: Relation,
        input: Option<BoundaryPart>,
        output: BoundaryPart,
    },
    EndApply {
        call: CallKey,
        relation: Relation,
        input: BoundaryPart,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
struct Arc {
    from: Node,
    to: Node,
    #[serde(with = "ordered_pairs")]
    guards: Guards,
    step: Step,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
struct Source {
    node: Node,
    instance: SourceInstance,
    #[serde(with = "ordered_pairs")]
    guards: Guards,
    proof: Vec<Step>,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
struct EndAt {
    node: Node,
    terminal: TerminalInstance,
    #[serde(with = "ordered_pairs")]
    guards: Guards,
    suffix: Vec<Step>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
struct Function {
    edges: Vec<Arc>,
    sources: Vec<Source>,
    inputs: BTreeSet<Node>,
    outputs: BTreeSet<Node>,
    terminals: Vec<EndAt>,
}

#[derive(Default, Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
struct Call {
    inputs: Vec<BoundaryPart>,
    outputs: Vec<BoundaryPart>,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) enum DenialReason {
    MissingTransferBinding,
    FoldedPointerPath,
    InvalidEquation,
    MissingGuard,
    UnmatchedBoundary,
    MissingBoundaryOccurrence,
    ReturnCoverage,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct Denial {
    pub(crate) function: Option<String>,
    pub(crate) construction: u32,
    pub(crate) equation: Option<EquationId>,
    pub(crate) boundary: Option<usize>,
    pub(crate) reason: DenialReason,
}

/// Each relation has an anchored finite witness. A recursive application uses
/// a relation already derived in an earlier round; output demand is no seed.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct MatchedTransport {
    #[serde(with = "ordered_pairs")]
    functions: BTreeMap<Scope, Function>,
    #[serde(with = "ordered_pairs")]
    relations: BTreeMap<Relation, Vec<Step>>,
    #[serde(with = "ordered_pairs")]
    guard_aliases: BTreeMap<EquationId, EquationId>,
    denials: Vec<Denial>,
}

impl MatchedTransport {
    /// Report 048: the streamed form of `serde_json::to_writer(&to_value(self))`,
    /// byte for byte. The object's keys in `Value`'s sorted order, each
    /// `ordered_pairs` field as its pairs, each pair through its own `Value`.
    /// lil's cache write died building this whole `Value` (report 042).
    pub(crate) fn write_canonical(&self, w: &mut dyn std::io::Write) -> Result<(), String> {
        let raw = |w: &mut dyn std::io::Write, bytes: &[u8]| -> Result<(), String> {
            w.write_all(bytes).map_err(|e| e.to_string())
        };
        raw(w, b"{\"denials\":")?;
        write_value_seq(w, &self.denials)?;
        raw(w, b",\"functions\":")?;
        write_value_seq(w, &self.functions)?;
        raw(w, b",\"guard_aliases\":")?;
        write_value_seq(w, &self.guard_aliases)?;
        raw(w, b",\"relations\":")?;
        write_value_seq(w, &self.relations)?;
        raw(w, b"}")
    }
}

fn combine(left: &Guards, right: &Guards) -> Option<Guards> {
    let mut result = left.clone();
    for (&key, &value) in right {
        if result.insert(key, value).is_some_and(|old| old != value) {
            return None;
        }
    }
    Some(result)
}

fn only<T>(mut values: impl Iterator<Item = T>) -> Option<T> {
    let value = values.next()?;
    values.next().is_none().then_some(value)
}

pub(crate) fn guard_aliases(
    bindings: &[super::facts::GuardBinding],
) -> BTreeMap<EquationId, EquationId> {
    let mut ordered: Vec<_> = bindings.iter().collect();
    ordered.sort_by_key(|binding| binding.equation);
    let mut predicates = HashMap::new();
    ordered
        .into_iter()
        .map(|binding| {
            // Bool Hash/PartialEq use the actual Z3 AST identity. Neither its
            // printed name nor an occurrence ordinal defines a new predicate.
            let canonical = *predicates
                .entry((binding.equation.construction, binding.predicate.clone()))
                .or_insert(binding.equation);
            (binding.equation, canonical)
        })
        .collect()
}

fn normalize(guards: &Guards, aliases: &BTreeMap<EquationId, EquationId>) -> Option<Guards> {
    let mut normalized = Guards::new();
    for (key, value) in guards {
        let key = *aliases.get(key)?;
        if normalized
            .insert(key, *value)
            .is_some_and(|previous| previous != *value)
        {
            return None;
        }
    }
    Some(normalized)
}

impl Function {
    fn normalize_guards(&mut self, aliases: &BTreeMap<EquationId, EquationId>) {
        self.edges.retain_mut(|edge| {
            let Some(guards) = normalize(&edge.guards, aliases) else { return false };
            edge.guards = guards;
            true
        });
        self.sources.retain_mut(|source| {
            let Some(guards) = normalize(&source.guards, aliases) else { return false };
            source.guards = guards;
            true
        });
        self.terminals.retain_mut(|terminal| {
            let Some(guards) = normalize(&terminal.guards, aliases) else { return false };
            terminal.guards = guards;
            true
        });
    }

    fn paths(
        &self,
        start: Node,
        guards: Guards,
        proof: Vec<Step>,
    ) -> BTreeMap<(Node, Guards), Vec<Step>> {
        let mut result = BTreeMap::new();
        let mut pending = VecDeque::from([(start, guards, proof)]);
        while let Some((node, guards, proof)) = pending.pop_front() {
            if result.contains_key(&(node, guards.clone())) {
                continue;
            }
            result.insert((node, guards.clone()), proof.clone());
            for edge in self.edges.iter().filter(|edge| edge.from == node) {
                let Some(next) = combine(&guards, &edge.guards) else { continue };
                let mut witness = proof.clone();
                witness.push(edge.step.clone());
                pending.push_back((edge.to, next, witness));
            }
        }
        result
    }

    fn contains(&self, node: Node) -> bool {
        self.inputs.contains(&node)
            || self.outputs.contains(&node)
            || self.terminals.iter().any(|terminal| terminal.node == node)
            || self.sources.iter().any(|source| source.node == node)
            || self
                .edges
                .iter()
                .any(|edge| edge.from == node || edge.to == node)
    }
}

impl MatchedTransport {
    /// Conditional forwarding only. The returned token is not zeroed, and no
    /// competing output/free is removed from the underlying transport.
    pub(crate) fn forward_folded_return(
        &self,
        facts: &Facts,
        output: &Meet,
        continuation: &Meet,
        guard: EquationId,
        fold: &super::fold_call::Proof,
    ) -> Option<FoldedReturn> {
        let declaration =
            only(facts.fold_declarations.as_ref()?.iter().filter(|d| {
                d.guard == guard && d.boundary == fold.boundary && d.call == fold.call
            }))?;
        let fields = fold
            .descendants
            .iter()
            .filter_map(|d| match &d.premise {
                super::fold_call::FieldPremise::Owning { field } => Some(field.clone()),
                super::fold_call::FieldPremise::Unused { .. } => None,
            })
            .collect();
        if super::fold_call::certify_metadata(
            facts,
            &fold.call,
            declaration.argument,
            &fields,
            &self.guard_aliases,
        )
        .ok()
        .as_ref()
            != Some(fold)
            || continuation.guards.get(&guard) != Some(&true)
        {
            return None;
        }
        // The supplied Facts may differ from those behind this transport.
        // Authenticate source/free operands and every retained route against
        // the current conditional construction before forwarding its token.
        let current = Self::build_with_conditional_folds_metadata(
            facts,
            &[(guard, fold.clone())],
            &self.guard_aliases,
        )
        .ok()?;
        let forwarding = current.forward_return_checked(
            facts,
            output,
            continuation,
            Some((guard, fold)),
            None,
        )?;
        Some(FoldedReturn {
            forwarding,
            guard,
            fold: Box::new(fold.clone()),
        })
    }

    pub(crate) fn forward_member_return(
        &self,
        facts: &Facts,
        output: &Meet,
        continuation: &Meet,
        member: &super::fold_subtree::Membership,
    ) -> Option<MemberReturn> {
        self.forward_member_return_metadata(
            facts,
            output,
            continuation,
            member,
            &facts.slot_refs.keys().cloned().collect(),
        )
    }

    pub(crate) fn forward_member_return_metadata(
        &self,
        facts: &Facts,
        output: &Meet,
        continuation: &Meet,
        member: &super::fold_subtree::Membership,
        slots: &BTreeSet<String>,
    ) -> Option<MemberReturn> {
        if output.source != member.member
            || continuation.source != member.member
            || output.terminal.lineage != SourceLineage::Exact(vec![member.fold.call.clone()])
        {
            return None;
        }
        let current = Self::build_with_subtree_folds_metadata(
            facts,
            &[(member.declaration.guard, member.fold.clone())],
            &[member.clone()],
            &self.guard_aliases,
            slots,
        )
        .ok()?;
        let forwarding = current.forward_return_checked(
            facts,
            output,
            continuation,
            Some((member.declaration.guard, &member.fold)),
            Some(member),
        )?;
        Some(MemberReturn {
            forwarding,
            membership: Box::new(member.clone()),
        })
    }

    pub(crate) fn forward_return(
        &self,
        facts: &Facts,
        output: &Meet,
        continuation: &Meet,
    ) -> Option<ForwardedReturn> {
        self.forward_return_checked(facts, output, continuation, None, None)
    }

    fn forward_return_checked(
        &self,
        facts: &Facts,
        output: &Meet,
        continuation: &Meet,
        fold: Option<(EquationId, &super::fold_call::Proof)>,
        member: Option<&super::fold_subtree::Membership>,
    ) -> Option<ForwardedReturn> {
        let TerminalTarget::Output {
            node: returned,
            ordinal,
        } = output.terminal.target
        else {
            return None;
        };
        let TerminalTarget::Free(free_id) = continuation.terminal.target else { return None };
        if output.source != continuation.source
            || !matches!(output.source.lineage, SourceLineage::Exact(_))
        {
            return None;
        }
        let SourceLineage::Exact(path) = &output.terminal.lineage else { return None };
        let call = path.last()?;
        if returned.construction != call.construction
            || !matches!(continuation.terminal.lineage, SourceLineage::Exact(_))
        {
            return None;
        }
        let guards = combine(&output.guards, &continuation.guards)?;
        // These are actual retained meets, not caller-supplied endpoint labels.
        let observed: Vec<_> = self
            .source_nodes(call.construction, &path.first()?.caller, &output.source)
            .into_iter()
            .flat_map(|seed| self.meets_for(seed))
            .collect();
        if !observed.contains(output) || !observed.contains(continuation) {
            return None;
        }
        let free = only(facts.equations.iter().filter(|e| {
            e.point.construction == free_id.construction && e.ordinal == free_id.ordinal
        }))?;
        if free.validate().is_err()
            || free.operation != "sink"
            || !free
                .endpoint
                .as_ref()
                .is_some_and(|e| e.callee == "free" && e.outcome.is_none())
        {
            return None;
        }
        let terminal =
            only(facts.terminals.iter().filter(|t| {
                t.point.construction == returned.construction && t.ordinal == ordinal
            }))?;
        let Availability::Present(values) = &terminal.values else { return None };
        if terminal.role != "return-output"
            || terminal.local != 0
            || terminal.point.function.as_ref() != Some(&call.callee)
            || !values
                .iter()
                .any(|v| v.var == returned.var && v.path == Availability::Present(Vec::new()))
        {
            return None;
        }
        let mut applications = Vec::new();
        self.return_applications(
            &continuation.proof,
            &[],
            path,
            &mut BTreeSet::new(),
            &mut applications,
        )?;
        let application = only(applications.into_iter())?;
        let Step::Apply {
            call: witnessed_call,
            relation,
            input,
            output: receiver_part,
        } = &application
        else {
            return None;
        };
        let part_matches = |part: &BoundaryPart, incoming: bool| {
            let Some((guard, proof)) = fold else {
                return self.input_store_part_matches(facts, call, part, incoming);
            };
            if &proof.call != call || part.construction != call.construction {
                return false;
            }
            if incoming && let Some(member) = member {
                return part.ordinal == member.declaration.boundary
                    && part.actual == member.member_before
                    && part.formal == member.formal
                    && guard == member.declaration.guard
                    && part.guards == member.requirements.guards.iter().copied().collect()
                    && matches!(&part.binding,BoundaryBinding::Folded{folded_member} if folded_member.as_ref()==member);
            }
            if part.native_match() != Some(0) || part.guards != BTreeMap::from([(guard, true)]) {
                return false;
            }
            if incoming {
                if part.ordinal != proof.boundary || part.actual != proof.actual_before {
                    return false;
                }
                let Some(boundary) = facts.boundary_substitutions.iter().find(|b| {
                    b.point.construction == call.construction && b.ordinal == proof.boundary
                }) else {
                    return false;
                };
                matches!(&boundary.matched[0].formal,Variables::UseDef{use_var,..} if part.formal.var==*use_var)
            } else {
                if part.ordinal != proof.receiver_boundary || part.actual != proof.receiver {
                    return false;
                }
                let Some(boundary) = facts.boundary_substitutions.iter().find(|b| {
                    b.point.construction == call.construction
                        && b.ordinal == proof.receiver_boundary
                }) else {
                    return false;
                };
                matches!(boundary.matched.first(),Some(pair) if matches!((&pair.formal,&pair.actual),
                    (Variables::Single{var},Variables::UseDef{def_var,..}) if part.formal.var==*var && part.actual.var==*def_var))
            }
        };
        if witnessed_call != call
            || relation.scope != (call.construction, call.callee.clone())
            || relation.output != Destination::Port(receiver_part.formal)
            || !part_matches(receiver_part, false)
            || (fold.is_some() && input.is_none())
            || input.as_ref().is_some_and(|part| !part_matches(part, true))
        {
            return None;
        }
        if relation
            .guards
            .iter()
            .chain(receiver_part.guards.iter())
            .chain(input.iter().flat_map(|part| part.guards.iter()))
            .any(|(key, value)| continuation.guards.get(key) != Some(value))
        {
            return None;
        }
        let receiver = only(facts.boundary_substitutions.iter().filter(|b| {
            b.point.construction == call.construction
                && b.ordinal == receiver_part.ordinal
                && b.role == Role::ReturnReceiver
        }))?;
        let Availability::Present(consume_id) = receiver.actual_occurrence else { return None };
        let consume = only(
            facts
                .consumes
                .iter()
                .filter(|c| c.point.construction == call.construction && c.ordinal == consume_id),
        )?;
        let Availability::Present(window) = &consume.projected else { return None };
        if consume.point != receiver.point
            || window.def_start != receiver_part.actual.var
            || match fold {
                None => {
                    window.def_end.checked_sub(window.def_start) != Some(1)
                        || window.use_end.checked_sub(window.use_start) != Some(1)
                }
                Some((_, proof)) => {
                    receiver.ordinal != proof.receiver_boundary
                        || receiver_part.actual != proof.receiver
                        || window.def_end.checked_sub(window.def_start)
                            != Some(proof.internal.input_components.len() as u32)
                        || window.use_end.checked_sub(window.use_start)
                            != Some(proof.internal.input_components.len() as u32)
                }
            }
        {
            return None;
        }
        let exit = only(facts.boundary_substitutions.iter().filter(|b| {
            b.point == terminal.point
                && b.role == Role::ExitReturn
                && b.matched.iter().any(|pair| {
                    pair.actual == (Variables::Single { var: returned.var })
                        && pair.formal
                            == (Variables::Single {
                                var: receiver_part.formal.var,
                            })
                })
        }))?;
        let exit_eq = only(facts.equations.iter().filter(|e| {
            e.point == exit.point
                && e.operation == "equal"
                && e.guard.is_none()
                && e.variables == [returned.var, receiver_part.formal.var]
                && e.validate().is_ok()
        }))?;
        let receiver_eq = only(facts.equations.iter().filter(|e| {
            e.point == receiver.point
                && e.operation == "equal"
                && e.guard.is_none()
                && e.variables == [receiver_part.actual.var, receiver_part.formal.var]
                && e.validate().is_ok()
        }))?;
        let old_zero = only(facts.equations.iter().filter(|e| {
            e.point == receiver.point
                && e.operation == "assume"
                && e.value == Some(false)
                && e.guard.is_none()
                && e.variables == [window.use_start]
                && e.validate().is_ok()
        }))?;
        let witness = self.relations.get(relation)?;
        if !witness.contains(&Step::Local(Evidence::Boundary {
            construction: call.construction,
            ordinal: exit.ordinal,
            matched: exit.matched.iter().position(|pair| {
                pair.actual == (Variables::Single { var: returned.var })
                    && pair.formal
                        == (Variables::Single {
                            var: receiver_part.formal.var,
                        })
            })?,
        })) {
            return None;
        }
        let id = |e: &super::super::ownership_evidence::Equation| EquationId {
            construction: e.point.construction,
            ordinal: e.ordinal,
        };
        Some(ForwardedReturn {
            output: output.clone(),
            continuation: continuation.clone(),
            call: call.clone(),
            call_path: path.clone(),
            returned,
            formal: receiver_part.formal,
            receiver_old: Node {
                construction: call.construction,
                var: window.use_start,
            },
            receiver: receiver_part.actual,
            exit_boundary: exit.ordinal,
            receiver_boundary: receiver.ordinal,
            receiver_consume: consume_id,
            exit_equation: id(exit_eq),
            receiver_equation: id(receiver_eq),
            receiver_old_zero: id(old_zero),
            guards,
            application: application.clone(),
            relation_witness: witness.clone(),
        })
    }

    fn return_applications(
        &self,
        steps: &[Step],
        prefix: &[CallKey],
        wanted: &[CallKey],
        active: &mut BTreeSet<Relation>,
        found: &mut Vec<Step>,
    ) -> Option<()> {
        for step in steps {
            let (call, relation) = match step {
                Step::Apply { call, relation, .. } | Step::EndApply { call, relation, .. } => {
                    (call, relation)
                }
                Step::Local(_) => continue,
            };
            let mut path = prefix.to_vec();
            path.push(call.clone());
            if path == wanted && matches!(step, Step::Apply { .. }) {
                found.push(step.clone());
            }
            if path.len() < wanted.len() && wanted.starts_with(&path) {
                if !active.insert(relation.clone()) {
                    return None;
                }
                self.return_applications(
                    self.relations.get(relation)?,
                    &path,
                    wanted,
                    active,
                    found,
                )?;
                active.remove(relation);
            }
        }
        Some(())
    }

    /// Symbolic Input-to-store/output applications; no source is inserted into
    /// a callee and no origin, output disposition, or ownership role is granted.
    pub(crate) fn input_store_applications(
        &self,
        facts: &Facts,
        store: EquationId,
    ) -> Vec<InputStoreApplication> {
        use super::super::{origin_evidence::SourceCallee, ownership_occurrence::PathStep};
        let stores: Vec<_> = facts
            .equations
            .iter()
            .filter(|row| {
                row.point.construction == store.construction && row.ordinal == store.ordinal
            })
            .collect();
        let [equation] = stores.as_slice() else { return Vec::new() };
        let Some(callee) = equation.point.function.as_ref() else { return Vec::new() };
        if equation.validate().is_err()
            || !matches!(equation.operation.as_str(), "equal" | "linear")
            || !equation.transfer.as_ref().is_some_and(|transfer| {
                matches!(&transfer.destination, Availability::Present(binding)
                    if matches!(binding.path.last(), Some(PathStep::Field { .. })))
            })
        {
            return Vec::new();
        }
        // Original calls, not just successful application arcs, define the
        // expected roster. Missing arguments/relations cannot erase a caller.
        let mut expected = BTreeSet::new();
        let mut source_calls = BTreeSet::new();
        for rows in facts.source_occurrences.values() {
            for row in rows
                .iter()
                .filter(|row| row.callee.as_ref() == Some(&SourceCallee::Local(callee.clone())))
            {
                let call = CallKey {
                    construction: store.construction,
                    caller: row.site.function.clone(),
                    block: row.site.block,
                    statement: row.site.statement,
                    callee: callee.clone(),
                };
                source_calls.insert(call.clone());
                expected.insert(call);
            }
        }
        for boundary in facts.boundary_substitutions.iter().filter(|row| {
            row.point.construction == store.construction && row.callee.as_ref() == Some(callee)
        }) {
            if let (Some(caller), Some(block), Some(statement)) = (
                &boundary.point.function,
                boundary.point.block,
                boundary.point.statement,
            ) {
                expected.insert(CallKey {
                    construction: store.construction,
                    caller: caller.clone(),
                    block,
                    statement,
                    callee: callee.clone(),
                });
            }
        }
        expected
            .into_iter()
            .map(|call| {
                let mut application = InputStoreApplication {
                    call: call.clone(),
                    store,
                    status: InputStoreStatus::MissingCorrespondence,
                    routes: Vec::new(),
                };
                let Some(function) = self
                    .functions
                    .get(&(call.construction, call.caller.clone()))
                else {
                    return application;
                };
                if !source_calls.contains(&call) {
                    return application;
                }
                for arc in &function.edges {
                    let Step::Apply {
                        call: actual_call,
                        relation,
                        input: Some(input),
                        output,
                    } = &arc.step
                    else {
                        continue;
                    };
                    if actual_call != &call
                        || relation.scope != (store.construction, callee.clone())
                        || relation.seed != Seed::Input(input.formal)
                        || relation.output != Destination::Port(output.formal)
                        || arc.from != input.actual
                        || arc.to != output.actual
                        || !self.input_store_part_matches(facts, &call, input, true)
                        || !self.input_store_part_matches(facts, &call, output, false)
                    {
                        continue;
                    }
                    let Some(witness) = self.relations.get(relation) else { continue };
                    if !witness.contains(&Step::Local(Evidence::Transfer(store))) {
                        continue;
                    }
                    let Some(guards) = combine(&relation.guards, &input.guards)
                        .and_then(|guards| combine(&guards, &output.guards))
                    else {
                        continue;
                    };
                    if guards != arc.guards {
                        continue;
                    }
                    let mut route = InputStoreRoute {
                        formal_input: input.formal,
                        formal_output: output.formal,
                        actual_input: input.actual,
                        actual_output: output.actual,
                        input_boundary: input.ordinal,
                        output_boundary: output.ordinal,
                        guards,
                        anchors: Vec::new(),
                        meets: Vec::new(),
                        source_terminals: Vec::new(),
                        store_witness: witness.clone(),
                        application: arc.step.clone(),
                    };
                    for source in &function.sources {
                        for ((reached, prefix_guards), prefix) in
                            function.paths(source.node, source.guards.clone(), source.proof.clone())
                        {
                            if reached != arc.from {
                                continue;
                            }
                            let Some(joined) = combine(&prefix_guards, &arc.guards) else {
                                continue;
                            };
                            let mut proof = prefix;
                            proof.push(arc.step.clone());
                            let anchor = InputStoreAnchor {
                                source: source.instance.clone(),
                                guards: joined.clone(),
                                proof: proof.clone(),
                            };
                            if !route.anchors.contains(&anchor) {
                                route.anchors.push(anchor);
                            }
                            for ((node, suffix_guards), suffix) in
                                function.paths(arc.to, joined, proof)
                            {
                                for end in function.terminals.iter().filter(|end| end.node == node)
                                {
                                    let Some(guards) = combine(&suffix_guards, &end.guards) else {
                                        continue;
                                    };
                                    let mut proof = suffix.clone();
                                    proof.extend(end.suffix.iter().cloned());
                                    let meet = Meet {
                                        source: source.instance.clone(),
                                        terminal: end.terminal.clone(),
                                        guards,
                                        proof,
                                    };
                                    if !route.meets.contains(&meet) {
                                        route.meets.push(meet);
                                    }
                                }
                            }
                        }
                    }
                    // A partner before the selected store is intentionally absent
                    // from the through-store suffix; retain its separate raw meet.
                    let sources: BTreeSet<_> = route
                        .anchors
                        .iter()
                        .map(|anchor| anchor.source.clone())
                        .collect();
                    for source in sources {
                        for seed in self.source_nodes(call.construction, &call.caller, &source) {
                            for meet in self
                                .meets_for(seed)
                                .into_iter()
                                .filter(|meet| meet.source == source)
                            {
                                if !route.source_terminals.contains(&meet) {
                                    route.source_terminals.push(meet);
                                }
                            }
                        }
                    }
                    if !application.routes.contains(&route) {
                        application.routes.push(route);
                    }
                }
                if !application.routes.is_empty() {
                    application.status = InputStoreStatus::Observed;
                }
                application
            })
            .collect()
    }

    fn input_store_part_matches(
        &self,
        facts: &Facts,
        call: &CallKey,
        part: &BoundaryPart,
        input: bool,
    ) -> bool {
        use super::super::ownership_boundary::LicensingRole;
        let rows: Vec<_> = facts
            .boundary_substitutions
            .iter()
            .filter(|row| {
                row.point.construction == part.construction && row.ordinal == part.ordinal
            })
            .collect();
        let [row] = rows.as_slice() else { return false };
        if part.construction != call.construction
            || row.point.function.as_ref() != Some(&call.caller)
            || row.point.block != Some(call.block)
            || row.point.statement != Some(call.statement)
            || row.callee.as_ref() != Some(&call.callee)
            || !matches!(row.actual_occurrence, Availability::Present(_))
            || !row.unmatched_actual_vars.is_empty()
            || !row.unmatched_formal_vars.is_empty()
        {
            return false;
        }
        if row.licensing_role == LicensingRole::OriginalCell {
            let Some(arm) = super::cell_effects::call_arm(facts, row, &self.guard_aliases) else {
                return false;
            };
            return part.native_match() == Some(0)
                && [(arm.original, true), (arm.legacy, false)]
                    .iter()
                    .any(|(actual, required)| {
                        part.formal.var == if input { arm.formal.0 } else { arm.formal.1 }
                            && part.actual.var == if input { actual.0 } else { actual.1 }
                            && part.guards == BTreeMap::from([(arm.guard, *required)])
                    });
        }
        if row.licensing_role != LicensingRole::Legacy || !part.guards.is_empty() {
            return false;
        }
        let Some(pair) = part.native_match().and_then(|index| row.matched.get(index)) else {
            return false;
        };
        let node = |var| Node {
            construction: call.construction,
            var,
        };
        match (&pair.formal, &pair.actual, row.role, input) {
            (
                Variables::UseDef {
                    use_var: formal, ..
                },
                Variables::UseDef {
                    use_var: actual, ..
                },
                Role::CallArgument,
                true,
            )
            | (
                Variables::UseDef {
                    def_var: formal, ..
                },
                Variables::UseDef {
                    def_var: actual, ..
                },
                Role::CallArgument,
                false,
            )
            | (
                Variables::Single { var: formal },
                Variables::UseDef {
                    def_var: actual, ..
                },
                Role::ReturnReceiver,
                false,
            ) => part.formal == node(*formal) && part.actual == node(*actual),
            _ => false,
        }
    }

    /// Provisional guarded routes; caller closure and model selection remain external.
    pub(crate) fn build_with_conditional_folds(
        facts: &Facts,
        folds: &[(EquationId, super::fold_call::Proof)],
    ) -> Result<Self, String> {
        Self::build_with_conditional_folds_metadata(facts, folds, &guard_aliases(&facts.guards))
    }

    pub(crate) fn build_with_conditional_folds_metadata(
        facts: &Facts,
        folds: &[(EquationId, super::fold_call::Proof)],
        aliases: &BTreeMap<EquationId, EquationId>,
    ) -> Result<Self, String> {
        super::fold_declaration::validate(facts, aliases)?;
        let mut folded = BTreeMap::new();
        for (guard, proof) in folds {
            let declaration = facts
                .fold_declarations
                .as_ref()
                .into_iter()
                .flatten()
                .find(|d| d.guard == *guard && d.boundary == proof.boundary && d.call == proof.call)
                .ok_or("conditional fold declaration missing")?;
            let fields = proof
                .descendants
                .iter()
                .filter_map(|d| match &d.premise {
                    super::fold_call::FieldPremise::Owning { field } => Some(field.clone()),
                    super::fold_call::FieldPremise::Unused { .. } => None,
                })
                .collect();
            let rebuilt = super::fold_call::certify_metadata(
                facts,
                &proof.call,
                declaration.argument,
                &fields,
                aliases,
            )
            .map_err(|e| format!("conditional fold proof rejected: {e:?}"))?;
            if &rebuilt != proof {
                return Err("conditional fold proof differs".into());
            }
            for boundary in [proof.boundary, proof.receiver_boundary] {
                if folded
                    .insert((proof.call.construction, boundary), *guard)
                    .is_some()
                {
                    return Err("overlapping conditional folds".into());
                }
            }
        }
        let graph = CandidateGraph::build_metadata(facts, aliases)?;
        Ok(Self::build_using(
            facts,
            aliases.clone(),
            graph,
            &folded,
            &[],
        ))
    }

    /// Conditional owned members are authenticated before any new call input.
    pub(crate) fn build_with_subtree_folds(
        facts: &Facts,
        folds: &[(EquationId, super::fold_call::Proof)],
        members: &[super::fold_subtree::Membership],
    ) -> Result<Self, String> {
        Self::build_with_subtree_folds_metadata(
            facts,
            folds,
            members,
            &guard_aliases(&facts.guards),
            &facts.slot_refs.keys().cloned().collect(),
        )
    }

    pub(crate) fn build_with_subtree_folds_metadata(
        facts: &Facts,
        folds: &[(EquationId, super::fold_call::Proof)],
        members: &[super::fold_subtree::Membership],
        aliases: &BTreeMap<EquationId, EquationId>,
        slots: &BTreeSet<String>,
    ) -> Result<Self, String> {
        let ordinary = Self::build_with_conditional_folds_metadata(facts, folds, aliases)?;
        let mut seen = BTreeSet::new();
        for member in members {
            if !seen.insert((member.declaration.guard, member.formal)) {
                return Err("duplicate folded member".into());
            }
            if !folds
                .iter()
                .any(|(guard, fold)| *guard == member.declaration.guard && fold == &member.fold)
            {
                return Err("folded member has no matching conditional fold".into());
            }
            let current = super::fold_subtree::certify_metadata(
                facts,
                &member.declaration,
                &member.fold,
                aliases,
                slots,
            )
            .map_err(|e| format!("folded member rejected: {e:?}"))?;
            if &current != member {
                return Err("folded member differs from current metadata".into());
            }
        }
        if members.is_empty() {
            return Ok(ordinary);
        }
        let folded = folds
            .iter()
            .flat_map(|(guard, proof)| {
                [proof.boundary, proof.receiver_boundary]
                    .map(|boundary| ((proof.call.construction, boundary), *guard))
            })
            .collect();
        let graph = CandidateGraph::build_metadata(facts, aliases)?;
        Ok(Self::build_using(
            facts,
            aliases.clone(),
            graph,
            &folded,
            members,
        ))
    }

    /// Read-only canonical predicate identity metadata from the ordinary build.
    pub(crate) fn guard_aliases(&self) -> &BTreeMap<EquationId, EquationId> {
        &self.guard_aliases
    }

    /// Metadata reconstruction performs no Bool/solver operation.
    pub(crate) fn build_metadata(
        facts: &Facts,
        guard_aliases: &BTreeMap<EquationId, EquationId>,
    ) -> Result<Self, String> {
        let graph = CandidateGraph::build_metadata(facts, guard_aliases)?;
        Ok(Self::build_using(
            facts,
            guard_aliases.clone(),
            graph,
            &BTreeMap::new(),
            &[],
        ))
    }

    /// Deterministic metadata serialization; no predicate AST is included.
    pub(crate) fn encode_json(&self) -> Result<Vec<u8>, String> {
        serde_json::to_vec(self).map_err(|error| error.to_string())
    }

    /// No predicate or solver state is reconstructed by this metadata interface.
    pub(crate) fn decode_json(bytes: &[u8]) -> Result<Self, String> {
        serde_json::from_slice(bytes).map_err(|error| error.to_string())
    }

    pub(crate) fn build(facts: &Facts) -> Self {
        Self::build_using(
            facts,
            guard_aliases(&facts.guards),
            CandidateGraph::build(facts),
            &BTreeMap::new(),
            &[],
        )
    }

    fn build_using(
        facts: &Facts,
        guard_aliases: BTreeMap<EquationId, EquationId>,
        mut graph: CandidateGraph,
        folded: &BTreeMap<(u32, usize), EquationId>,
        members: &[super::fold_subtree::Membership],
    ) -> Self {
        let mut denials = Vec::new();
        let mut blocked_equations = BTreeSet::new();
        for row in &facts.equations {
            let id = EquationId {
                construction: row.point.construction,
                ordinal: row.ordinal,
            };
            let mut reasons = Vec::new();
            if let Some(transfer) = &row.transfer {
                match (&transfer.destination, &transfer.source) {
                    (Availability::Present(destination), Availability::Present(source)) => {
                        if destination
                            .path
                            .contains(&super::super::ownership_occurrence::PathStep::ArrayElement)
                            || source.path.contains(
                                &super::super::ownership_occurrence::PathStep::ArrayElement,
                            )
                        {
                            reasons.push(DenialReason::FoldedPointerPath);
                        }
                    }
                    _ => reasons.push(DenialReason::MissingTransferBinding),
                }
            }
            if row.validate().is_err() {
                reasons.push(DenialReason::InvalidEquation);
            }
            if (row.operation.starts_with("guarded-")
                || matches!(row.operation.as_str(), "source" | "sink"))
                && !guard_aliases.contains_key(&id)
            {
                reasons.push(DenialReason::MissingGuard);
            }
            for reason in reasons {
                blocked_equations.insert(id);
                denials.push(Denial {
                    function: row.point.function.clone(),
                    construction: id.construction,
                    equation: Some(id),
                    boundary: None,
                    reason,
                });
            }
        }
        let mut blocked_boundaries = BTreeSet::new();
        for row in &facts.boundary_substitutions {
            let reason = if (!row.unmatched_actual_vars.is_empty()
                || !row.unmatched_formal_vars.is_empty())
                && !folded.contains_key(&(row.point.construction, row.ordinal))
            {
                Some(DenialReason::UnmatchedBoundary)
            } else if matches!(row.role, Role::CallArgument | Role::ReturnReceiver)
                && !row.matched.is_empty()
                && !matches!(row.actual_occurrence, Availability::Present(_))
            {
                Some(DenialReason::MissingBoundaryOccurrence)
            } else {
                None
            };
            if let Some(reason) = reason {
                blocked_boundaries.insert((row.point.construction, row.ordinal));
                denials.push(Denial {
                    function: row.point.function.clone(),
                    construction: row.point.construction,
                    equation: None,
                    boundary: Some(row.ordinal),
                    reason,
                });
            }
        }
        let mut blocked_scopes = BTreeSet::new();
        let scopes: BTreeSet<_> = facts
            .equations
            .iter()
            .filter_map(|row| {
                row.point
                    .function
                    .clone()
                    .map(|function| (row.point.construction, function))
            })
            .chain(facts.body_rosters.iter().filter_map(|row| {
                row.point
                    .function
                    .clone()
                    .map(|function| (row.point.construction, function))
            }))
            .chain((0..facts.constructions).flat_map(|construction| {
                facts
                    .source_occurrences
                    .keys()
                    .cloned()
                    .map(move |function| (construction, function))
            }))
            .collect();
        for (construction, function) in scopes {
            if super::coverage::validate_returns(facts, construction, &function).is_err() {
                blocked_scopes.insert((construction, function.clone()));
                denials.push(Denial {
                    function: Some(function),
                    construction,
                    equation: None,
                    boundary: None,
                    reason: DenialReason::ReturnCoverage,
                });
            }
        }
        graph
            .sources
            .retain(|source| !blocked_equations.contains(&source.equation));
        graph
            .sinks
            .retain(|sink| !blocked_equations.contains(&sink.equation));
        graph.edges.retain(|edge| match edge.evidence {
            Evidence::Transfer(id)
            | Evidence::Phi(id)
            | Evidence::Frame { equation: id, .. }
            | Evidence::TraversalFrame(id)
            | Evidence::ReferenceEffect(id) => !blocked_equations.contains(&id),
            Evidence::Boundary {
                construction,
                ordinal,
                ..
            } => !blocked_boundaries.contains(&(construction, ordinal)),
        });
        let equations: BTreeMap<_, _> = facts
            .equations
            .iter()
            .map(|row| {
                (
                    EquationId {
                        construction: row.point.construction,
                        ordinal: row.ordinal,
                    },
                    row,
                )
            })
            .collect();
        let boundaries: BTreeMap<_, _> = facts
            .boundary_substitutions
            .iter()
            .map(|row| ((row.point.construction, row.ordinal), row))
            .collect();
        let mut base: BTreeMap<Scope, Function> = BTreeMap::new();
        for edge in &graph.edges {
            let point = match edge.evidence {
                Evidence::Transfer(id)
                | Evidence::Phi(id)
                | Evidence::Frame { equation: id, .. }
                | Evidence::TraversalFrame(id)
                | Evidence::ReferenceEffect(id) => {
                    let Some(row) = equations.get(&id) else { continue };
                    &row.point
                }
                Evidence::Boundary {
                    construction,
                    ordinal,
                    ..
                } => {
                    let Some(row) = boundaries.get(&(construction, ordinal)) else { continue };
                    if matches!(row.role, Role::CallArgument | Role::ReturnReceiver)
                        && row.licensing_role
                            != super::super::ownership_boundary::LicensingRole::Borrowed
                    {
                        continue;
                    }
                    &row.point
                }
            };
            let Some(function) = &point.function else { continue };
            let guards = edge
                .guard
                .map(|guard| (guard.binding, guard.required))
                .into_iter()
                .collect();
            base.entry((point.construction, function.clone()))
                .or_default()
                .edges
                .push(Arc {
                    from: edge.from,
                    to: edge.to,
                    guards,
                    step: Step::Local(edge.evidence),
                });
        }
        for source in &graph.sources {
            let Some(row) = equations.get(&source.equation) else { continue };
            let Some(function) = &row.point.function else { continue };
            base.entry((row.point.construction, function.clone()))
                .or_default()
                .sources
                .push(Source {
                    node: source.node,
                    instance: SourceInstance {
                        endpoint: source.equation,
                        lineage: SourceLineage::Exact(Vec::new()),
                    },
                    guards: BTreeMap::from([(source.equation, true)]),
                    proof: Vec::new(),
                });
        }
        for sink in &graph.sinks {
            let Some(row) = equations.get(&sink.equation) else { continue };
            let Some(function) = &row.point.function else { continue };
            base.entry((row.point.construction, function.clone()))
                .or_default()
                .terminals
                .push(EndAt {
                    node: sink.node,
                    terminal: TerminalInstance {
                        target: TerminalTarget::Free(sink.equation),
                        lineage: SourceLineage::Exact(Vec::new()),
                    },
                    guards: Guards::from([(sink.equation, true)]),
                    suffix: Vec::new(),
                });
        }
        for exit in &graph.exits {
            let Some(row) = facts.terminals.iter().find(|row| {
                row.point.construction == exit.node.construction
                    && row.ordinal == exit.terminal_ordinal
            }) else {
                continue;
            };
            let Some(function) = &row.point.function else { continue };
            base.entry((row.point.construction, function.clone()))
                .or_default()
                .terminals
                .push(EndAt {
                    node: exit.node,
                    terminal: TerminalInstance {
                        target: TerminalTarget::Output {
                            node: exit.node,
                            ordinal: exit.terminal_ordinal,
                        },
                        lineage: SourceLineage::Exact(Vec::new()),
                    },
                    guards: Guards::new(),
                    suffix: Vec::new(),
                });
        }
        base.retain(|scope, _| !blocked_scopes.contains(scope));
        let mut calls: BTreeMap<CallKey, Call> = BTreeMap::new();
        for row in &facts.boundary_substitutions {
            let Some(function) = &row.point.function else { continue };
            if blocked_boundaries.contains(&(row.point.construction, row.ordinal))
                || blocked_scopes.contains(&(row.point.construction, function.clone()))
            {
                continue;
            }
            let node = |var| Node {
                construction: row.point.construction,
                var,
            };
            let scope = (row.point.construction, function.clone());
            match row.role {
                Role::Entry | Role::ExitReturn | Role::ExitOutput => {
                    let function = base.entry(scope).or_default();
                    for pair in &row.matched {
                        let Variables::Single { var } = pair.formal else { continue };
                        if row.role == Role::Entry {
                            function.inputs.insert(node(var));
                        } else {
                            function.outputs.insert(node(var));
                        }
                    }
                }
                Role::CallArgument | Role::ReturnReceiver => {
                    if row.licensing_role
                        == super::super::ownership_boundary::LicensingRole::Borrowed
                    {
                        continue;
                    }
                    // Matched numeric ranges do not replace actual occurrence
                    // correspondence, target resolution or complete components.
                    if !matches!(row.actual_occurrence, Availability::Present(_))
                        || ((!row.unmatched_actual_vars.is_empty()
                            || !row.unmatched_formal_vars.is_empty())
                            && !folded.contains_key(&(row.point.construction, row.ordinal)))
                    {
                        continue;
                    }
                    let (Some(block), Some(statement), Some(callee)) =
                        (row.point.block, row.point.statement, row.callee.clone())
                    else {
                        continue;
                    };
                    let key = CallKey {
                        construction: row.point.construction,
                        caller: function.clone(),
                        block,
                        statement,
                        callee,
                    };
                    let call = calls.entry(key).or_default();
                    if row.licensing_role
                        == super::super::ownership_boundary::LicensingRole::OriginalCell
                    {
                        if let Some(arm) = super::cell_effects::call_arm(facts, row, &guard_aliases)
                        {
                            for (actual, required) in [(arm.original, true), (arm.legacy, false)] {
                                let part = |formal, actual| BoundaryPart {
                                    guards: BTreeMap::from([(arm.guard, required)]),
                                    construction: row.point.construction,
                                    ordinal: row.ordinal,
                                    binding: BoundaryBinding::Native { matched: 0 },
                                    formal: node(formal),
                                    actual: node(actual),
                                };
                                call.inputs.push(part(arm.formal.0, actual.0));
                                call.outputs.push(part(arm.formal.1, actual.1));
                            }
                        }
                        continue;
                    }
                    let part_guards =
                        if let Some(guard) = folded.get(&(row.point.construction, row.ordinal)) {
                            BTreeMap::from([(*guard, true)])
                        } else if row.licensing_role
                            == super::super::ownership_boundary::LicensingRole::TraversalBorrow
                        {
                            let Some(guard) =
                                super::traversal_call::guard_for(facts, row, &guard_aliases)
                            else {
                                continue;
                            };
                            BTreeMap::from([(guard, false)])
                        } else {
                            Guards::new()
                        };
                    for (matched, pair) in row.matched.iter().enumerate() {
                        let part = |formal, actual| BoundaryPart {
                            guards: part_guards.clone(),
                            construction: row.point.construction,
                            ordinal: row.ordinal,
                            binding: BoundaryBinding::Native { matched },
                            formal: node(formal),
                            actual: node(actual),
                        };
                        match (&pair.formal, &pair.actual) {
                            (
                                Variables::UseDef {
                                    use_var: formal_use,
                                    def_var: formal_def,
                                },
                                Variables::UseDef {
                                    use_var: actual_use,
                                    def_var: actual_def,
                                },
                            ) => {
                                call.inputs.push(part(*formal_use, *actual_use));
                                call.outputs.push(part(*formal_def, *actual_def));
                            }
                            (Variables::Single { var }, Variables::UseDef { def_var, .. })
                                if row.role == Role::ReturnReceiver =>
                            {
                                call.outputs.push(part(*var, *def_var));
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
        for member in members {
            let key = &member.declaration.call;
            if blocked_scopes.contains(&(key.construction, key.caller.clone()))
                || blocked_scopes.contains(&(key.construction, key.callee.clone()))
                || !base
                    .get(&(key.construction, key.callee.clone()))
                    .is_some_and(|f| f.inputs.contains(&member.formal))
            {
                continue;
            }
            let Some(call) = calls.get_mut(key) else { continue };
            if !call.inputs.iter().any(|part| {
                part.native_match() == Some(0)
                    && part.ordinal == member.declaration.boundary
                    && part.actual == member.cell
                    && part.guards.get(&member.declaration.guard) == Some(&true)
            }) {
                continue;
            }
            call.inputs.push(BoundaryPart {
                guards: member.requirements.guards.iter().copied().collect(),
                construction: key.construction,
                ordinal: member.declaration.boundary,
                binding: BoundaryBinding::Folded {
                    folded_member: Box::new(member.clone()),
                },
                formal: member.formal,
                actual: member.member_before,
            });
        }
        for function in base.values_mut() {
            function.normalize_guards(&guard_aliases);
        }
        let mut relations = BTreeMap::new();
        loop {
            let functions = Self::apply(&base, &calls, &relations);
            let mut added = Vec::new();
            for (scope, function) in &functions {
                let inputs = function
                    .inputs
                    .iter()
                    .map(|&node| (Seed::Input(node), node, Guards::new(), Vec::new()));
                let sources = function.sources.iter().map(|source| {
                    (
                        Seed::Source(source.instance.clone()),
                        source.node,
                        source.guards.clone(),
                        source.proof.clone(),
                    )
                });
                for (seed, node, guards, proof) in inputs.chain(sources) {
                    for ((output, guards), proof) in function.paths(node, guards, proof) {
                        if function.outputs.contains(&output) {
                            let relation = Relation {
                                scope: scope.clone(),
                                seed: seed.clone(),
                                output: Destination::Port(output),
                                guards: guards.clone(),
                            };
                            if !relations.contains_key(&relation) {
                                added.push((relation, proof.clone()));
                            }
                        }
                        for terminal in function.terminals.iter().filter(|end| end.node == output) {
                            let Some(guards) = combine(&guards, &terminal.guards) else { continue };
                            let mut proof = proof.clone();
                            proof.extend(terminal.suffix.iter().cloned());
                            let relation = Relation {
                                scope: scope.clone(),
                                seed: seed.clone(),
                                output: Destination::Terminal(terminal.terminal.clone()),
                                guards,
                            };
                            if !relations.contains_key(&relation) {
                                added.push((relation, proof));
                            }
                        }
                    }
                }
            }
            if added.is_empty() {
                return Self {
                    functions,
                    relations,
                    guard_aliases,
                    denials,
                };
            }
            for (relation, proof) in added {
                relations.entry(relation).or_insert(proof);
            }
        }
    }

    fn apply(
        base: &BTreeMap<Scope, Function>,
        calls: &BTreeMap<CallKey, Call>,
        relations: &BTreeMap<Relation, Vec<Step>>,
    ) -> BTreeMap<Scope, Function> {
        let mut functions = base.clone();
        for (key, call) in calls {
            let caller = functions
                .entry((key.construction, key.caller.clone()))
                .or_default();
            for relation in relations
                .keys()
                .filter(|row| row.scope == (key.construction, key.callee.clone()))
            {
                match &relation.output {
                    Destination::Port(formal_output) => {
                        for output in call
                            .outputs
                            .iter()
                            .filter(|part| part.formal == *formal_output)
                        {
                            match &relation.seed {
                                Seed::Input(formal) => {
                                    for input in
                                        call.inputs.iter().filter(|part| part.formal == *formal)
                                    {
                                        let Some(guards) = combine(&relation.guards, &input.guards)
                                            .and_then(|guards| combine(&guards, &output.guards))
                                        else {
                                            continue;
                                        };
                                        caller.edges.push(Arc {
                                            from: input.actual,
                                            to: output.actual,
                                            guards,
                                            step: Step::Apply {
                                                call: key.clone(),
                                                relation: relation.clone(),
                                                input: Some(input.clone()),
                                                output: output.clone(),
                                            },
                                        });
                                    }
                                }
                                Seed::Source(source) => {
                                    let Some(guards) = combine(&relation.guards, &output.guards)
                                    else {
                                        continue;
                                    };
                                    caller.sources.push(Source {
                                        node: output.actual,
                                        instance: source.through(key),
                                        guards,
                                        proof: vec![Step::Apply {
                                            call: key.clone(),
                                            relation: relation.clone(),
                                            input: None,
                                            output: output.clone(),
                                        }],
                                    });
                                }
                            }
                        }
                    }
                    Destination::Terminal(terminal) => {
                        if let Seed::Input(formal) = &relation.seed {
                            for input in call.inputs.iter().filter(|part| part.formal == *formal) {
                                let Some(guards) = combine(&relation.guards, &input.guards) else {
                                    continue;
                                };
                                caller.terminals.push(EndAt {
                                    node: input.actual,
                                    terminal: TerminalInstance {
                                        target: terminal.target.clone(),
                                        lineage: terminal.lineage.through(key),
                                    },
                                    guards,
                                    suffix: vec![Step::EndApply {
                                        call: key.clone(),
                                        relation: relation.clone(),
                                        input: input.clone(),
                                    }],
                                });
                            }
                        }
                        // A callee-local source/terminal relation remains in
                        // that function's record. It creates no caller carrier.
                    }
                }
            }
        }
        functions
    }

    /// Candidate existence with compatible guards; this does not select a model
    /// or assert source/sink activation, ownership, origin or gate completeness.
    pub(crate) fn denials(&self) -> &[Denial] {
        &self.denials
    }

    pub(crate) fn reaches(&self, from: Node, to: Node) -> bool {
        self.functions.values().any(|function| {
            function.contains(from)
                && function.contains(to)
                && function
                    .paths(from, Guards::new(), Vec::new())
                    .keys()
                    .any(|(node, _)| *node == to)
        })
    }

    /// Existential, call-matched F/B candidates. Token conservation, all-inflow
    /// origin closure and the remaining gates are required before licensing.
    pub(crate) fn meets_for(&self, node: Node) -> Vec<Meet> {
        let mut result = Vec::new();
        let mut seen = BTreeSet::new();
        for function in self
            .functions
            .values()
            .filter(|function| function.contains(node))
        {
            let backward = function.paths(node, Guards::new(), Vec::new());
            for source in &function.sources {
                let forward =
                    function.paths(source.node, source.guards.clone(), source.proof.clone());
                for ((reached, forward_guards), forward_proof) in
                    forward.iter().filter(|((n, _), _)| *n == node)
                {
                    debug_assert_eq!(*reached, node);
                    for terminal in &function.terminals {
                        for ((_, backward_guards), backward_proof) in
                            backward.iter().filter(|((n, _), _)| *n == terminal.node)
                        {
                            let Some(guards) = combine(forward_guards, backward_guards)
                                .and_then(|guards| combine(&guards, &terminal.guards))
                            else {
                                continue;
                            };
                            if !seen.insert((
                                source.instance.clone(),
                                terminal.terminal.clone(),
                                guards.clone(),
                            )) {
                                continue;
                            }
                            let mut proof = forward_proof.clone();
                            proof.extend(backward_proof.iter().cloned());
                            proof.extend(terminal.suffix.iter().cloned());
                            result.push(Meet {
                                source: source.instance.clone(),
                                terminal: terminal.terminal.clone(),
                                guards,
                                proof,
                            });
                        }
                    }
                }
            }
        }
        result
    }

    /// The allocation's entry occurrences in this exact function application.
    /// Store-local reachability alone misses partners split off before a store.
    pub(crate) fn source_nodes(
        &self,
        construction: u32,
        function: &str,
        instance: &SourceInstance,
    ) -> Vec<Node> {
        self.functions
            .get(&(construction, function.to_owned()))
            .into_iter()
            .flat_map(|function| &function.sources)
            .filter(|source| &source.instance == instance)
            .map(|source| source.node)
            .collect()
    }

    pub(crate) fn meets_selected(
        &self,
        node: Node,
        value: impl Fn(EquationId) -> Option<bool>,
    ) -> Vec<Meet> {
        self.meets_for(node)
            .into_iter()
            .filter(|meet| {
                meet.guards
                    .iter()
                    .all(|(&guard, &required)| value(guard) == Some(required))
            })
            .collect()
    }

    pub(crate) fn sources_for(&self, node: Node) -> BTreeSet<SourceInstance> {
        self.functions
            .values()
            .filter(|function| function.contains(node))
            .flat_map(|function| {
                function.sources.iter().filter_map(|source| {
                    function
                        .paths(source.node, source.guards.clone(), source.proof.clone())
                        .keys()
                        .any(|(reached, _)| *reached == node)
                        .then(|| source.instance.clone())
                })
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use z3::ast::Bool;

    use super::{super::facts::GuardBinding, *};

    #[test]
    fn t11_one_actual_predicate_cannot_have_opposite_polarities_under_two_record_keys() {
        // A constructed candidate graph using real Bool predicates, not a
        // claim about a particular fixture's emitted SSA or accepted model.
        let first = EquationId {
            construction: 0,
            ordinal: 0,
        };
        let second = EquationId {
            construction: 0,
            ordinal: 1,
        };
        let predicate = Bool::fresh_const("t11_shared_guard");
        let bindings = [
            GuardBinding {
                equation: first,
                predicate: predicate.clone(),
            },
            GuardBinding {
                equation: second,
                predicate: predicate.clone(),
            },
        ];
        let node = |var| Node {
            construction: 0,
            var,
        };
        let mut function = Function::default();
        for (from, to, binding, required) in [(1, 2, first, true), (2, 3, second, false)] {
            function.edges.push(Arc {
                from: node(from),
                to: node(to),
                guards: BTreeMap::from([(binding, required)]),
                step: Step::Local(Evidence::Phi(binding)),
            });
        }
        let mut independent = function.clone();
        independent.normalize_guards(&guard_aliases(&[
            bindings[0].clone(),
            GuardBinding {
                equation: second,
                predicate: Bool::fresh_const("t11_other_guard"),
            },
        ]));
        assert!(
            independent
                .paths(node(1), Guards::new(), Vec::new())
                .keys()
                .any(|(n, _)| *n == node(3)),
            "distinct actual predicates remain independent"
        );
        function.normalize_guards(&guard_aliases(&bindings));
        assert!(
            !function
                .paths(node(1), Guards::new(), Vec::new())
                .keys()
                .any(|(n, _)| *n == node(3)),
            "same actual predicate must not be both true and false via distinct equation ordinals"
        );
    }
}

#[cfg(test)]
mod folded_binding_tests {
    use super::*;
    #[test]
    fn oc03_boundary_decode_rejects_competing_wire_bindings() {
        let native = serde_json::json!({"guards":[],"construction":0,"ordinal":3,"matched":1,"formal":{"construction":0,"var":6},"actual":{"construction":0,"var":83}});
        for member in [
            serde_json::Value::Null,
            serde_json::json!({"malformed":true}),
        ] {
            let mut both = native.clone();
            both["folded_member"] = member;
            let error = serde_json::from_value::<BoundaryPart>(both)
                .expect_err("both native and member keys must reject");
            assert!(
                error.to_string().contains("ambiguous boundary binding"),
                "{error}"
            );
        }
    }

    #[test]
    fn oc03_native_boundary_binding_keeps_legacy_json_bytes() {
        let bytes=br#"{"guards":[],"construction":0,"ordinal":3,"matched":1,"formal":{"construction":0,"var":6},"actual":{"construction":0,"var":83}}"#;
        let part: BoundaryPart = serde_json::from_slice(bytes).unwrap();
        assert_eq!(part.native_match(), Some(1));
        assert_eq!(serde_json::to_vec(&part).unwrap(), bytes);
    }
}
