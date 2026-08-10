//! Test-only P-b census of function-pointer-rooted local call webs.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    io::Write,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};

use points_to::andersen;
use rustc_hash::FxHashSet;
use rustc_hir::{
    def::{DefKind, Res},
    def_id::LocalDefId,
    intravisit::{walk_expr, Visitor},
    ExprKind, QPath,
};
use rustc_middle::{
    mir::{BasicBlock, TerminatorKind},
    ty::TyCtxt,
};
use rustc_type_ir::TyKind;
use serde::Deserialize;

const MACHINE_ID: &str = "lambda7";
const PLATFORM: &str = "linux-x86_64";
const WALL_LIVENESS_SECS: u64 = 14_400;
const RAW_CORPUS_SHA256: &str = "9fc912af10fd3b235fe4d444d2fbac0bc521509b1c9447fc551acd0130e0e621";
const DERIVED_CORPUS_SHA256: &str =
    "db96829b5c2b0db28fb4bb9ddd3d32901b5d4e6e4134da07ada0d513d94eb4c6";
const SNAPSHOT_PRODUCER: &str = "e0f33f80560696bead5a6dbcd39341e3681f687a";
const SNAPSHOT_MANIFEST_COMMIT: &str = "e0f33f80560696bead5a6dbcd39341e3681f687a";
const SNAPSHOT_MANIFEST_DOCUMENT_SHA256: &str =
    "4bd51fbc5eb162d5372cfb67feb64a1cc0caaef072763bcaa33b3d9c4616c952";
const SNAPSHOT_SHA256SUMS_SHA256: &str =
    "ec0b48d8f40ae34b96550c51a72d6b44ce80e87cba8bb33f6c44e51dc91c81ac";
const S36_RS_CORPUS_SHA256: &str =
    "f158c7c81c6f96b1710afa1450a03b434853f4abad8d5b64c34e922276121b57";
const HISTORICAL_AGGREGATE_MANIFEST_SHA256: &str =
    "12acf99ef73dbea55cb869351840dceac7004732b008d4c6c9b574c54826f961";
const LIBTEST_WORKER_PREFIX: &str = "test bo_c1::boc1_run_one ... ";

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct CoverageCounts {
    calls_total: usize,
    direct_local: usize,
    indirect_local: usize,
    direct_external: usize,
    indirect_unresolved: usize,
    non_fn_def_constant: usize,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct ResolutionEdgeCounts {
    direct_local_edges: usize,
    andersen_local_edges: usize,
    indirect_unresolved_sites: usize,
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

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct GraphNode {
    fn_ptr_root: bool,
    public_root: bool,
    callees: BTreeSet<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum ReferenceKind {
    Call,
    FnPtrCast,
    AddrTaken,
}

impl ReferenceKind {
    fn key(self) -> &'static str {
        match self {
            Self::Call => "call",
            Self::FnPtrCast => "fnptr-cast",
            Self::AddrTaken => "addr-taken",
        }
    }

    fn parse(value: &str) -> Result<Self, String> {
        match value {
            "call" => Ok(Self::Call),
            "fnptr-cast" => Ok(Self::FnPtrCast),
            "addr-taken" => Ok(Self::AddrTaken),
            other => Err(format!("unknown S3.6 reference kind {other:?}")),
        }
    }

    fn is_pinning(self) -> bool {
        matches!(self, Self::FnPtrCast | Self::AddrTaken)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum BodyOwnerKind {
    FunctionBody,
    StaticInitializer,
    ConstInitializer,
    AnonConst,
    OtherBodyOwner,
}

impl BodyOwnerKind {
    fn key(self) -> &'static str {
        match self {
            Self::FunctionBody => "function-body",
            Self::StaticInitializer => "static-initializer",
            Self::ConstInitializer => "const-initializer",
            Self::AnonConst => "anon-const",
            Self::OtherBodyOwner => "other-body-owner",
        }
    }

    fn parse(value: &str) -> Result<Self, String> {
        match value {
            "function-body" => Ok(Self::FunctionBody),
            "static-initializer" => Ok(Self::StaticInitializer),
            "const-initializer" => Ok(Self::ConstInitializer),
            "anon-const" => Ok(Self::AnonConst),
            "other-body-owner" => Ok(Self::OtherBodyOwner),
            other => Err(format!("unknown body-owner kind {other:?}")),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ReferenceSite {
    owner_path: String,
    owner_kind: BodyOwnerKind,
    ref_kind: ReferenceKind,
    site: String,
}

impl ReferenceSite {
    #[cfg(test)]
    fn fixture(owner_kind: BodyOwnerKind, ref_kind: ReferenceKind) -> Self {
        Self {
            owner_path: "fixture::owner".to_owned(),
            owner_kind,
            ref_kind,
            site: "fixture.rs:1:1".to_owned(),
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct S36FunctionEvidence {
    ref_kinds: BTreeSet<ReferenceKind>,
    ref_class: String,
    pointer_subjects: usize,
    blocked_subjects: usize,
}

impl S36FunctionEvidence {
    #[cfg(test)]
    fn pinned(
        pointer_subjects: usize,
        blocked_subjects: usize,
        ref_kinds: impl IntoIterator<Item = ReferenceKind>,
    ) -> Self {
        Self {
            ref_kinds: ref_kinds.into_iter().collect(),
            ref_class: "pinned".to_owned(),
            pointer_subjects,
            blocked_subjects,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum RootDifferenceCause {
    OutsideS36PointerSubjectPopulation,
    S36ReferencePredicateDifference,
    StaticInitializerOutsideCollectFnPtrs,
    ConstInitializerOutsideCollectFnPtrs,
    MixedInitializerOutsideCollectFnPtrs,
}

impl RootDifferenceCause {
    fn key(self) -> &'static str {
        match self {
            Self::OutsideS36PointerSubjectPopulation => "outside-s36-pointer-subject-population",
            Self::S36ReferencePredicateDifference => "s36-reference-predicate-difference",
            Self::StaticInitializerOutsideCollectFnPtrs => {
                "static-initializer-outside-collect-fn-ptrs"
            }
            Self::ConstInitializerOutsideCollectFnPtrs => {
                "const-initializer-outside-collect-fn-ptrs"
            }
            Self::MixedInitializerOutsideCollectFnPtrs => {
                "mixed-initializer-outside-collect-fn-ptrs"
            }
        }
    }

    fn parse(value: &str) -> Result<Self, String> {
        match value {
            "outside-s36-pointer-subject-population" => {
                Ok(Self::OutsideS36PointerSubjectPopulation)
            }
            "s36-reference-predicate-difference" => Ok(Self::S36ReferencePredicateDifference),
            "static-initializer-outside-collect-fn-ptrs" => {
                Ok(Self::StaticInitializerOutsideCollectFnPtrs)
            }
            "const-initializer-outside-collect-fn-ptrs" => {
                Ok(Self::ConstInitializerOutsideCollectFnPtrs)
            }
            "mixed-initializer-outside-collect-fn-ptrs" => {
                Ok(Self::MixedInitializerOutsideCollectFnPtrs)
            }
            other => Err(format!("unknown root-difference cause {other:?}")),
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct RootReconciliation {
    intersection: BTreeSet<String>,
    p_b_only: BTreeMap<String, RootDifferenceCause>,
    s36_only: BTreeMap<String, RootDifferenceCause>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct GraphMeasurement {
    fn_ptr_roots: BTreeSet<String>,
    public_roots: BTreeSet<String>,
    root_public_overlap: BTreeSet<String>,
    reachable: BTreeSet<String>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct WorkerArtifact {
    graph: GraphMeasurement,
    aligned_graph: GraphMeasurement,
    local_functions: usize,
    coverage: CoverageCounts,
    aligned_coverage: CoverageCounts,
    aligned_resolution: ResolutionEdgeCounts,
    s36_functions: BTreeMap<String, S36FunctionEvidence>,
    reconciliation: RootReconciliation,
    reference_sites: BTreeMap<String, Vec<ReferenceSite>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CallRoute {
    Direct,
    AndersenIndirect,
    UnsupportedConstant,
}

fn classify_call_route(is_constant: bool, constant_is_fn_def: bool) -> CallRoute {
    match (is_constant, constant_is_fn_def) {
        (true, true) => CallRoute::Direct,
        (false, false) => CallRoute::AndersenIndirect,
        (true, false) => CallRoute::UnsupportedConstant,
        (false, true) => unreachable!("a non-constant operand cannot be a constant FnDef"),
    }
}

fn add_local_call_edges(
    graph: &mut BTreeMap<String, GraphNode>,
    caller: &str,
    route: CallRoute,
    targets: impl IntoIterator<Item = String>,
) -> Result<(), String> {
    if route == CallRoute::UnsupportedConstant {
        return Err(format!(
            "unsupported constant non-FnDef callable in `{caller}`; Andersen has no indirect-call site"
        ));
    }
    graph
        .get_mut(caller)
        .ok_or_else(|| format!("missing caller graph node {caller}"))?
        .callees
        .extend(targets);
    Ok(())
}

fn measure_web(
    graph: &BTreeMap<String, GraphNode>,
    roots: &BTreeSet<String>,
) -> Result<BTreeSet<String>, String> {
    for root in roots {
        if !graph.contains_key(root) {
            return Err(format!("web root is not a local function: {root}"));
        }
    }
    let mut reachable = BTreeSet::new();
    let mut pending = roots.iter().cloned().collect::<Vec<_>>();
    while let Some(function) = pending.pop() {
        if !reachable.insert(function.clone()) {
            continue;
        }
        let node = graph
            .get(&function)
            .ok_or_else(|| format!("call graph references unknown local function `{function}`"))?;
        pending.extend(node.callees.iter().cloned());
    }
    Ok(reachable)
}

fn resolution_counts_for_web(
    reachable: &BTreeSet<String>,
    direct_edges: &BTreeSet<(String, String)>,
    andersen_edges: &BTreeSet<(String, String)>,
    unresolved_sites: &BTreeSet<(String, usize)>,
) -> ResolutionEdgeCounts {
    ResolutionEdgeCounts {
        direct_local_edges: direct_edges
            .iter()
            .filter(|(caller, _)| reachable.contains(caller))
            .count(),
        andersen_local_edges: andersen_edges
            .iter()
            .filter(|(caller, _)| reachable.contains(caller))
            .count(),
        indirect_unresolved_sites: unresolved_sites
            .iter()
            .filter(|(caller, _)| reachable.contains(caller))
            .count(),
    }
}

fn measure_graph(graph: &BTreeMap<String, GraphNode>) -> Result<GraphMeasurement, String> {
    for (caller, node) in graph {
        for callee in &node.callees {
            if !graph.contains_key(callee) {
                return Err(format!(
                    "call graph references unknown local callee `{callee}` from `{caller}`"
                ));
            }
        }
    }
    let fn_ptr_roots = graph
        .iter()
        .filter_map(|(name, node)| node.fn_ptr_root.then_some(name.clone()))
        .collect::<BTreeSet<_>>();
    let public_roots = graph
        .iter()
        .filter_map(|(name, node)| node.public_root.then_some(name.clone()))
        .collect::<BTreeSet<_>>();
    let root_public_overlap = fn_ptr_roots
        .intersection(&public_roots)
        .cloned()
        .collect::<BTreeSet<_>>();
    let reachable = measure_web(graph, &fn_ptr_roots)?;
    Ok(GraphMeasurement {
        fn_ptr_roots,
        public_roots,
        root_public_overlap,
        reachable,
    })
}

fn body_owner_kind(tcx: TyCtxt<'_>, owner: LocalDefId) -> BodyOwnerKind {
    match tcx.def_kind(owner) {
        DefKind::Fn | DefKind::AssocFn => BodyOwnerKind::FunctionBody,
        DefKind::Static { .. } => BodyOwnerKind::StaticInitializer,
        DefKind::Const | DefKind::AssocConst => BodyOwnerKind::ConstInitializer,
        DefKind::AnonConst | DefKind::InlineConst => BodyOwnerKind::AnonConst,
        _ => BodyOwnerKind::OtherBodyOwner,
    }
}

fn collect_reference_sites(
    tcx: TyCtxt<'_>,
    functions: &[LocalDefId],
) -> Result<BTreeMap<String, Vec<ReferenceSite>>, String> {
    struct ReferenceVisitor<'a, 'tcx> {
        tcx: TyCtxt<'tcx>,
        local: &'a FxHashSet<LocalDefId>,
        owner_path: String,
        owner_kind: BodyOwnerKind,
        sites: &'a mut BTreeMap<String, Vec<ReferenceSite>>,
    }

    impl<'tcx> Visitor<'tcx> for ReferenceVisitor<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) -> Self::Result {
            if let ExprKind::Path(QPath::Resolved(_, path)) = &expr.kind
                && let Res::Def(DefKind::Fn, def_id) = path.res
                && let Some(target) = def_id.as_local()
                && self.local.contains(&target)
            {
                let ref_kind = match self.tcx.parent_hir_node(expr.hir_id) {
                    rustc_hir::Node::Expr(parent) => match parent.kind {
                        ExprKind::Call(callee, _) if callee.hir_id == expr.hir_id => {
                            ReferenceKind::Call
                        }
                        ExprKind::Cast(..) => ReferenceKind::FnPtrCast,
                        _ => ReferenceKind::AddrTaken,
                    },
                    _ => ReferenceKind::AddrTaken,
                };
                self.sites
                    .entry(self.tcx.def_path_str(target.to_def_id()))
                    .or_default()
                    .push(ReferenceSite {
                        owner_path: self.owner_path.clone(),
                        owner_kind: self.owner_kind,
                        ref_kind,
                        site: self
                            .tcx
                            .sess
                            .source_map()
                            .span_to_diagnostic_string(expr.span),
                    });
            }
            walk_expr(self, expr);
        }
    }

    let local = functions.iter().copied().collect::<FxHashSet<_>>();
    let mut sites = BTreeMap::new();
    for owner in tcx.hir_body_owners() {
        let mut visitor = ReferenceVisitor {
            tcx,
            local: &local,
            owner_path: tcx.def_path_str(owner.to_def_id()),
            owner_kind: body_owner_kind(tcx, owner),
            sites: &mut sites,
        };
        visitor.visit_body(tcx.hir_body_owned_by(owner));
    }
    for rows in sites.values_mut() {
        rows.sort();
        rows.dedup();
        for row in rows.iter() {
            validate_atom("reference owner", &row.owner_path)?;
            validate_atom("reference site", &row.site)?;
        }
    }
    Ok(sites)
}

fn parse_reference_kinds(value: &str) -> Result<BTreeSet<ReferenceKind>, String> {
    if value == "-" {
        return Ok(BTreeSet::new());
    }
    value.split(',').map(ReferenceKind::parse).collect()
}

fn validate_s36_function(name: &str, evidence: &S36FunctionEvidence) -> Result<(), String> {
    match evidence.ref_class.as_str() {
        "-" if evidence.ref_kinds.is_empty() => Ok(()),
        "adaptable" if evidence.ref_kinds == BTreeSet::from([ReferenceKind::Call]) => Ok(()),
        "pinned" if evidence.ref_kinds.iter().any(|kind| kind.is_pinning()) => Ok(()),
        class => Err(format!(
            "S3.6 function {name} has inconsistent ref_class={class:?} ref_kinds={:?}",
            evidence
                .ref_kinds
                .iter()
                .map(|kind| kind.key())
                .collect::<Vec<_>>()
        )),
    }
}

#[derive(Deserialize)]
struct S36OutcomeRow {
    fn_path: String,
    mir_local: u32,
    outcome: Option<String>,
    degrade_reason: Option<String>,
}

fn parse_s36_program(
    facts_text: &str,
    outcome_text: &str,
) -> Result<BTreeMap<String, S36FunctionEvidence>, String> {
    const HEADER: &str = "fn_path\tmir_local\tis_param\tannotated\tslot\tkind\traw_op\tptr_cmp\treferenced\tref_kinds\tref_class\tctor\tlen_class\tsize_expr";
    let mut lines = facts_text.lines();
    if lines.next() != Some(HEADER) {
        return Err("S3.6 facts header drifted".to_owned());
    }
    let mut functions = BTreeMap::<String, S36FunctionEvidence>::new();
    let mut subject_keys = BTreeMap::<(String, u32), ()>::new();
    for (offset, line) in lines.enumerate() {
        let fields = line.split('\t').collect::<Vec<_>>();
        if fields.len() != 14 {
            return Err(format!(
                "S3.6 facts line {} has {} fields, expected 14",
                offset + 2,
                fields.len()
            ));
        }
        validate_atom("S3.6 function", fields[0])?;
        let mir_local = fields[1]
            .parse::<u32>()
            .map_err(|error| format!("S3.6 facts line {} mir_local: {error}", offset + 2))?;
        let key = (fields[0].to_owned(), mir_local);
        if subject_keys.insert(key, ()).is_some() {
            return Err(format!(
                "duplicate S3.6 subject identity {} / {mir_local}",
                fields[0]
            ));
        }
        let ref_kinds = parse_reference_kinds(fields[9])?;
        let ref_class = fields[10].to_owned();
        let entry = functions
            .entry(fields[0].to_owned())
            .or_insert_with(|| S36FunctionEvidence {
                ref_kinds: ref_kinds.clone(),
                ref_class: ref_class.clone(),
                ..Default::default()
            });
        if entry.ref_kinds != ref_kinds || entry.ref_class != ref_class {
            return Err(format!(
                "S3.6 function {} changes reference classification across subjects",
                fields[0]
            ));
        }
        let referenced = fields[8];
        if (referenced == "0") != (ref_class == "-") {
            return Err(format!(
                "S3.6 function {} has inconsistent referenced/ref_class",
                fields[0]
            ));
        }
        entry.pointer_subjects += 1;
    }
    for (name, evidence) in &functions {
        validate_s36_function(name, evidence)?;
    }

    let mut outcome_keys = BTreeSet::new();
    for (offset, line) in outcome_text.lines().enumerate() {
        if line.trim().is_empty() {
            continue;
        }
        let row: S36OutcomeRow = serde_json::from_str(line)
            .map_err(|error| format!("S3.6 outcome line {}: {error}", offset + 1))?;
        let key = (row.fn_path.clone(), row.mir_local);
        if !outcome_keys.insert(key.clone()) {
            return Err(format!(
                "duplicate S3.6 outcome identity {} / {}",
                row.fn_path, row.mir_local
            ));
        }
        if row.degrade_reason.as_deref() != Some("call-site-not-adapted") {
            continue;
        }
        if row.outcome.as_deref() != Some("degraded") {
            return Err(format!(
                "S3.6 blocked subject {} / {} is not degraded",
                row.fn_path, row.mir_local
            ));
        }
        if !subject_keys.contains_key(&key) {
            return Err(format!(
                "S3.6 blocked subject {} / {} has missing facts identity",
                row.fn_path, row.mir_local
            ));
        }
        let evidence = functions
            .get_mut(&row.fn_path)
            .expect("subject key proves function exists");
        if evidence.ref_class == "-" {
            return Err(format!(
                "S3.6 blocked subject {} / {} belongs to an unreferenced function",
                row.fn_path, row.mir_local
            ));
        }
        evidence.blocked_subjects += 1;
    }
    Ok(functions)
}

fn reconcile_roots(
    p_b_roots: &BTreeSet<String>,
    s36_functions: &BTreeMap<String, S36FunctionEvidence>,
    reference_sites: &BTreeMap<String, Vec<ReferenceSite>>,
) -> Result<RootReconciliation, String> {
    let s36_roots = s36_functions
        .iter()
        .filter_map(|(name, evidence)| (evidence.ref_class == "pinned").then_some(name.clone()))
        .collect::<BTreeSet<_>>();
    let intersection = p_b_roots
        .intersection(&s36_roots)
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut p_b_only = BTreeMap::new();
    for name in p_b_roots.difference(&s36_roots) {
        let cause = if s36_functions.contains_key(name) {
            RootDifferenceCause::S36ReferencePredicateDifference
        } else {
            RootDifferenceCause::OutsideS36PointerSubjectPopulation
        };
        p_b_only.insert(name.clone(), cause);
    }
    let mut s36_only = BTreeMap::new();
    for name in s36_roots.difference(p_b_roots) {
        let sites = reference_sites
            .get(name)
            .ok_or_else(|| format!("unexplained S3.6-only root {name}: no reference sites"))?;
        let observed_kinds = sites
            .iter()
            .map(|site| site.ref_kind)
            .collect::<BTreeSet<_>>();
        let expected_kinds = &s36_functions[name].ref_kinds;
        if &observed_kinds != expected_kinds {
            return Err(format!(
                "unexplained S3.6-only root {name}: snapshot kinds {:?}, measured kinds {:?}",
                expected_kinds
                    .iter()
                    .map(|kind| kind.key())
                    .collect::<Vec<_>>(),
                observed_kinds
                    .iter()
                    .map(|kind| kind.key())
                    .collect::<Vec<_>>()
            ));
        }
        let pinning = sites
            .iter()
            .filter(|site| site.ref_kind.is_pinning())
            .collect::<Vec<_>>();
        if pinning.is_empty() {
            return Err(format!(
                "unexplained S3.6-only root {name}: no measured pinning site"
            ));
        }
        if pinning
            .iter()
            .any(|site| site.owner_kind == BodyOwnerKind::FunctionBody)
        {
            return Err(format!(
                "unexplained S3.6-only root {name}: function-body pinning reference"
            ));
        }
        if pinning
            .iter()
            .any(|site| site.owner_kind == BodyOwnerKind::OtherBodyOwner)
        {
            return Err(format!(
                "unexplained S3.6-only root {name}: other body-owner pinning reference"
            ));
        }
        let owner_kinds = pinning
            .iter()
            .map(|site| site.owner_kind)
            .collect::<BTreeSet<_>>();
        let cause = if owner_kinds == BTreeSet::from([BodyOwnerKind::StaticInitializer]) {
            RootDifferenceCause::StaticInitializerOutsideCollectFnPtrs
        } else if owner_kinds.iter().all(|kind| {
            matches!(
                kind,
                BodyOwnerKind::ConstInitializer | BodyOwnerKind::AnonConst
            )
        }) {
            RootDifferenceCause::ConstInitializerOutsideCollectFnPtrs
        } else {
            RootDifferenceCause::MixedInitializerOutsideCollectFnPtrs
        };
        s36_only.insert(name.clone(), cause);
    }
    Ok(RootReconciliation {
        intersection,
        p_b_only,
        s36_only,
    })
}

fn validate_atom(kind: &str, value: &str) -> Result<(), String> {
    if value.is_empty() || value.contains(['\t', '\n', '\r']) {
        Err(format!("invalid {kind} identity {value:?}"))
    } else {
        Ok(())
    }
}

fn render_worker_artifact(
    machine_id: &str,
    platform: &str,
    program: &str,
    graph: &GraphMeasurement,
    local_functions: usize,
    coverage: CoverageCounts,
) -> Result<String, String> {
    for (kind, value) in [
        ("machine", machine_id),
        ("platform", platform),
        ("program", program),
    ] {
        validate_atom(kind, value)?;
    }
    coverage.validate()?;
    if graph.root_public_overlap
        != graph
            .fn_ptr_roots
            .intersection(&graph.public_roots)
            .cloned()
            .collect()
    {
        return Err("root/public overlap does not match the inventories".to_owned());
    }
    if !graph.fn_ptr_roots.is_subset(&graph.reachable) {
        return Err("function-pointer roots are missing from the web closure".to_owned());
    }
    if graph.reachable.len() > local_functions {
        return Err("web closure exceeds the local-function population".to_owned());
    }
    for name in graph
        .fn_ptr_roots
        .iter()
        .chain(&graph.public_roots)
        .chain(&graph.reachable)
    {
        validate_atom("function", name)?;
    }

    let mut out = format!(
        "PBCOUNT\tv1\t{machine_id}\t{platform}\t{program}\t{}\t{}\t{}\t{}\t{local_functions}\t{}\t{}\t{}\t{}\t{}\t{}\n",
        graph.fn_ptr_roots.len(),
        graph.public_roots.len(),
        graph.root_public_overlap.len(),
        graph.reachable.len(),
        coverage.calls_total,
        coverage.direct_local,
        coverage.indirect_local,
        coverage.direct_external,
        coverage.indirect_unresolved,
        coverage.non_fn_def_constant,
    );
    for name in &graph.fn_ptr_roots {
        out.push_str(&format!(
            "PBROOT\tv1\t{machine_id}\t{platform}\t{program}\t{name}\t{}\n",
            usize::from(graph.public_roots.contains(name))
        ));
    }
    for name in &graph.public_roots {
        out.push_str(&format!(
            "PBPUBLIC\tv1\t{machine_id}\t{platform}\t{program}\t{name}\n"
        ));
    }
    for name in &graph.reachable {
        out.push_str(&format!(
            "PBREACH\tv1\t{machine_id}\t{platform}\t{program}\t{name}\t{}\n",
            usize::from(graph.fn_ptr_roots.contains(name))
        ));
    }
    Ok(out)
}

fn render_reconciled_worker_artifact(
    machine_id: &str,
    platform: &str,
    program: &str,
    artifact: &WorkerArtifact,
) -> Result<String, String> {
    artifact.coverage.validate()?;
    artifact.aligned_coverage.validate()?;
    if artifact.aligned_resolution.indirect_unresolved_sites
        > artifact.aligned_coverage.indirect_unresolved
    {
        return Err("aligned-closure unresolved sites exceed whole-program coverage".to_owned());
    }
    if artifact.aligned_graph.fn_ptr_roots
        != artifact
            .s36_functions
            .keys()
            .cloned()
            .collect::<BTreeSet<_>>()
    {
        return Err("aligned roots do not equal the S3.6 pinned inventory".to_owned());
    }
    let expected_intersection = artifact
        .graph
        .fn_ptr_roots
        .intersection(&artifact.aligned_graph.fn_ptr_roots)
        .cloned()
        .collect::<BTreeSet<_>>();
    if artifact.reconciliation.intersection != expected_intersection
        || artifact
            .reconciliation
            .p_b_only
            .keys()
            .cloned()
            .collect::<BTreeSet<_>>()
            != artifact
                .graph
                .fn_ptr_roots
                .difference(&artifact.aligned_graph.fn_ptr_roots)
                .cloned()
                .collect()
        || artifact
            .reconciliation
            .s36_only
            .keys()
            .cloned()
            .collect::<BTreeSet<_>>()
            != artifact
                .aligned_graph
                .fn_ptr_roots
                .difference(&artifact.graph.fn_ptr_roots)
                .cloned()
                .collect()
    {
        return Err("reconciliation sets do not match the two root inventories".to_owned());
    }
    let difference_names = artifact
        .reconciliation
        .p_b_only
        .keys()
        .chain(artifact.reconciliation.s36_only.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    if artifact
        .reference_sites
        .keys()
        .cloned()
        .collect::<BTreeSet<_>>()
        != difference_names
    {
        return Err("difference identities lack exact reference-site evidence".to_owned());
    }
    let pointer_subjects = artifact
        .s36_functions
        .values()
        .map(|evidence| evidence.pointer_subjects)
        .sum::<usize>();
    let blocked_subjects = artifact
        .s36_functions
        .values()
        .map(|evidence| evidence.blocked_subjects)
        .sum::<usize>();
    let reference_site_count = artifact
        .reference_sites
        .values()
        .map(Vec::len)
        .sum::<usize>();
    let mut out = render_worker_artifact(
        machine_id,
        platform,
        program,
        &artifact.graph,
        artifact.local_functions,
        artifact.coverage.clone(),
    )?;
    out.push_str(&format!(
        "PBALIGNCOUNT\tv1\t{machine_id}\t{platform}\t{program}\t{}\t{}\t{}\t{}\t{}\t{pointer_subjects}\t{blocked_subjects}\t{}\t{}\t{}\t{}\t{}\t{}\t{reference_site_count}\t{}\t{}\t{}\n",
        artifact.aligned_graph.fn_ptr_roots.len(),
        artifact.aligned_graph.reachable.len(),
        artifact.reconciliation.intersection.len(),
        artifact.reconciliation.p_b_only.len(),
        artifact.reconciliation.s36_only.len(),
        artifact.aligned_coverage.calls_total,
        artifact.aligned_coverage.direct_local,
        artifact.aligned_coverage.indirect_local,
        artifact.aligned_coverage.direct_external,
        artifact.aligned_coverage.indirect_unresolved,
        artifact.aligned_coverage.non_fn_def_constant,
        artifact.aligned_resolution.direct_local_edges,
        artifact.aligned_resolution.andersen_local_edges,
        artifact.aligned_resolution.indirect_unresolved_sites,
    ));
    for (name, evidence) in &artifact.s36_functions {
        validate_atom("function", name)?;
        let (relation, cause) = if artifact.reconciliation.intersection.contains(name) {
            ("intersection", "-")
        } else {
            (
                "s36-only",
                artifact
                    .reconciliation
                    .s36_only
                    .get(name)
                    .ok_or_else(|| format!("missing S3.6-only cause for {name}"))?
                    .key(),
            )
        };
        let ref_kinds = evidence
            .ref_kinds
            .iter()
            .map(|kind| kind.key())
            .collect::<Vec<_>>()
            .join(",");
        out.push_str(&format!(
            "PBALIGNROOT\tv1\t{machine_id}\t{platform}\t{program}\t{name}\t{}\t{ref_kinds}\t{}\t{}\t{relation}\t{cause}\n",
            usize::from(artifact.graph.fn_ptr_roots.contains(name)),
            evidence.pointer_subjects,
            evidence.blocked_subjects,
        ));
    }
    for name in &artifact.aligned_graph.reachable {
        out.push_str(&format!(
            "PBALIGNREACH\tv1\t{machine_id}\t{platform}\t{program}\t{name}\t{}\n",
            usize::from(artifact.aligned_graph.fn_ptr_roots.contains(name))
        ));
    }
    for (name, cause) in &artifact.reconciliation.p_b_only {
        out.push_str(&format!(
            "PBROOTDIFF\tv1\t{machine_id}\t{platform}\t{program}\t{name}\tp-b-only\t{}\n",
            cause.key()
        ));
    }
    for (name, cause) in &artifact.reconciliation.s36_only {
        out.push_str(&format!(
            "PBROOTDIFF\tv1\t{machine_id}\t{platform}\t{program}\t{name}\ts36-only\t{}\n",
            cause.key()
        ));
    }
    for (name, sites) in &artifact.reference_sites {
        for site in sites {
            for (kind, value) in [("owner", site.owner_path.as_str()), ("site", &site.site)] {
                validate_atom(kind, value)?;
            }
            out.push_str(&format!(
                "PBREFSITE\tv1\t{machine_id}\t{platform}\t{program}\t{name}\t{}\t{}\t{}\t{}\n",
                site.owner_kind.key(),
                site.ref_kind.key(),
                site.owner_path,
                site.site,
            ));
        }
    }
    Ok(out)
}

fn parse_usize(field: &str, value: &str) -> Result<usize, String> {
    value
        .parse::<usize>()
        .map_err(|error| format!("invalid {field} {value:?}: {error}"))
}

fn p_b_schema_line(line: &str) -> Option<&str> {
    if line.starts_with("PB") {
        return Some(line);
    }
    line.strip_prefix(LIBTEST_WORKER_PREFIX)
        .filter(|line| line.starts_with("PBCOUNT\t"))
}

fn parse_worker_artifact(
    machine_id: &str,
    platform: &str,
    program: &str,
    text: &str,
) -> Result<WorkerArtifact, String> {
    let mut declared = None;
    let mut roots = BTreeMap::new();
    let mut public_roots = BTreeSet::new();
    let mut reachable = BTreeMap::new();
    for (offset, raw_line) in text.lines().enumerate() {
        let Some(line) = p_b_schema_line(raw_line) else {
            continue;
        };
        let fields = line.split('\t').collect::<Vec<_>>();
        let check_identity = |expected_len: usize| -> Result<(), String> {
            if fields.len() != expected_len {
                return Err(format!(
                    "P-b schema line {} has {} columns, expected {expected_len}",
                    offset + 1,
                    fields.len()
                ));
            }
            if fields[1] != "v1"
                || fields[2] != machine_id
                || fields[3] != platform
                || fields[4] != program
            {
                return Err(format!("P-b identity mismatch on line {}", offset + 1));
            }
            Ok(())
        };
        match fields[0] {
            "PBCOUNT" => {
                check_identity(16)?;
                let coverage = CoverageCounts {
                    calls_total: parse_usize("calls_total", fields[10])?,
                    direct_local: parse_usize("direct_local", fields[11])?,
                    indirect_local: parse_usize("indirect_local", fields[12])?,
                    direct_external: parse_usize("direct_external", fields[13])?,
                    indirect_unresolved: parse_usize("indirect_unresolved", fields[14])?,
                    non_fn_def_constant: parse_usize("non_fn_def_constant", fields[15])?,
                };
                coverage.validate()?;
                let counts = (
                    parse_usize("root_count", fields[5])?,
                    parse_usize("public_root_count", fields[6])?,
                    parse_usize("root_public_overlap", fields[7])?,
                    parse_usize("web_count", fields[8])?,
                    parse_usize("local_functions", fields[9])?,
                    coverage,
                );
                if declared.replace(counts).is_some() {
                    return Err("duplicate PBCOUNT row".to_owned());
                }
            }
            "PBROOT" => {
                check_identity(7)?;
                validate_atom("function", fields[5])?;
                let is_public = match fields[6] {
                    "0" => false,
                    "1" => true,
                    value => return Err(format!("invalid root public flag {value:?}")),
                };
                if roots.insert(fields[5].to_owned(), is_public).is_some() {
                    return Err(format!("duplicate root identity {}", fields[5]));
                }
            }
            "PBPUBLIC" => {
                check_identity(6)?;
                validate_atom("function", fields[5])?;
                if !public_roots.insert(fields[5].to_owned()) {
                    return Err(format!("duplicate public-root identity {}", fields[5]));
                }
            }
            "PBREACH" => {
                check_identity(7)?;
                validate_atom("function", fields[5])?;
                let is_root = match fields[6] {
                    "0" => false,
                    "1" => true,
                    value => return Err(format!("invalid reach root flag {value:?}")),
                };
                if reachable.insert(fields[5].to_owned(), is_root).is_some() {
                    return Err(format!("duplicate reachable identity {}", fields[5]));
                }
            }
            "PBALIGNCOUNT" | "PBALIGNROOT" | "PBALIGNREACH" | "PBROOTDIFF" | "PBREFSITE" => {
                continue;
            }
            other => return Err(format!("unknown P-b schema sentinel {other:?}")),
        }
    }
    let (root_count, public_count, overlap_count, web_count, local_functions, coverage) =
        declared.ok_or_else(|| "missing PBCOUNT row".to_owned())?;
    if roots.len() != root_count {
        return Err(format!(
            "root inventory mismatch: declared={root_count} rows={}",
            roots.len()
        ));
    }
    if public_roots.len() != public_count {
        return Err(format!(
            "public-root inventory mismatch: declared={public_count} rows={}",
            public_roots.len()
        ));
    }
    if reachable.len() != web_count {
        return Err(format!(
            "web inventory mismatch: declared={web_count} rows={}",
            reachable.len()
        ));
    }
    if web_count > local_functions {
        return Err("web closure exceeds the local-function population".to_owned());
    }
    let fn_ptr_roots = roots.keys().cloned().collect::<BTreeSet<_>>();
    let reachable_set = reachable.keys().cloned().collect::<BTreeSet<_>>();
    if !fn_ptr_roots.is_subset(&reachable_set) {
        return Err("root inventory is not a subset of the web closure".to_owned());
    }
    for (name, is_public) in &roots {
        if *is_public != public_roots.contains(name) {
            return Err(format!("root/public flag mismatch for {name}"));
        }
    }
    for (name, is_root) in &reachable {
        if *is_root != fn_ptr_roots.contains(name) {
            return Err(format!("reachable/root flag mismatch for {name}"));
        }
    }
    let overlap = fn_ptr_roots
        .intersection(&public_roots)
        .cloned()
        .collect::<BTreeSet<_>>();
    if overlap.len() != overlap_count {
        return Err(format!(
            "root/public overlap mismatch: declared={overlap_count} rows={}",
            overlap.len()
        ));
    }
    Ok(WorkerArtifact {
        graph: GraphMeasurement {
            fn_ptr_roots,
            public_roots,
            root_public_overlap: overlap,
            reachable: reachable_set,
        },
        aligned_graph: GraphMeasurement::default(),
        local_functions,
        aligned_coverage: coverage.clone(),
        aligned_resolution: ResolutionEdgeCounts::default(),
        coverage,
        s36_functions: BTreeMap::new(),
        reconciliation: RootReconciliation::default(),
        reference_sites: BTreeMap::new(),
    })
}

fn parse_reconciled_worker_artifact(
    machine_id: &str,
    platform: &str,
    program: &str,
    text: &str,
) -> Result<WorkerArtifact, String> {
    let mut artifact = parse_worker_artifact(machine_id, platform, program, text)?;
    let mut declared = None;
    let mut aligned_roots = BTreeMap::<String, (bool, String, String)>::new();
    let mut aligned_reachable = BTreeMap::<String, bool>::new();
    let mut reconciliation = RootReconciliation::default();
    let mut reference_sites = BTreeMap::<String, Vec<ReferenceSite>>::new();
    for (offset, line) in text.lines().enumerate() {
        if !matches!(
            line.split('\t').next(),
            Some("PBALIGNCOUNT" | "PBALIGNROOT" | "PBALIGNREACH" | "PBROOTDIFF" | "PBREFSITE")
        ) {
            continue;
        }
        let fields = line.split('\t').collect::<Vec<_>>();
        let check_identity = |expected_len: usize| -> Result<(), String> {
            if fields.len() != expected_len {
                return Err(format!(
                    "P-b aligned schema line {} has {} columns, expected {expected_len}",
                    offset + 1,
                    fields.len()
                ));
            }
            if fields[1] != "v1"
                || fields[2] != machine_id
                || fields[3] != platform
                || fields[4] != program
            {
                return Err(format!(
                    "P-b aligned identity mismatch on line {}",
                    offset + 1
                ));
            }
            Ok(())
        };
        match fields[0] {
            "PBALIGNCOUNT" => {
                check_identity(22)?;
                let coverage = CoverageCounts {
                    calls_total: parse_usize("aligned_calls_total", fields[12])?,
                    direct_local: parse_usize("aligned_direct_local", fields[13])?,
                    indirect_local: parse_usize("aligned_indirect_local", fields[14])?,
                    direct_external: parse_usize("aligned_direct_external", fields[15])?,
                    indirect_unresolved: parse_usize("aligned_indirect_unresolved", fields[16])?,
                    non_fn_def_constant: parse_usize("aligned_non_fn_def_constant", fields[17])?,
                };
                coverage.validate()?;
                let resolution = ResolutionEdgeCounts {
                    direct_local_edges: parse_usize("aligned_direct_local_edges", fields[19])?,
                    andersen_local_edges: parse_usize("aligned_andersen_local_edges", fields[20])?,
                    indirect_unresolved_sites: parse_usize(
                        "aligned_indirect_unresolved_sites",
                        fields[21],
                    )?,
                };
                if resolution.indirect_unresolved_sites > coverage.indirect_unresolved {
                    return Err(
                        "aligned-closure unresolved sites exceed whole-program coverage".to_owned(),
                    );
                }
                let counts = (
                    parse_usize("aligned_root_count", fields[5])?,
                    parse_usize("aligned_web_count", fields[6])?,
                    parse_usize("intersection_count", fields[7])?,
                    parse_usize("p_b_only_count", fields[8])?,
                    parse_usize("s36_only_count", fields[9])?,
                    parse_usize("S3.6 pointer subjects", fields[10])?,
                    parse_usize("S3.6 blocked subjects", fields[11])?,
                    coverage,
                    resolution,
                    parse_usize("reference_site_count", fields[18])?,
                );
                if declared.replace(counts).is_some() {
                    return Err("duplicate PBALIGNCOUNT row".to_owned());
                }
            }
            "PBALIGNROOT" => {
                check_identity(12)?;
                validate_atom("function", fields[5])?;
                let historical = match fields[6] {
                    "0" => false,
                    "1" => true,
                    value => return Err(format!("invalid historical-root flag {value:?}")),
                };
                let evidence = S36FunctionEvidence {
                    ref_kinds: parse_reference_kinds(fields[7])?,
                    ref_class: "pinned".to_owned(),
                    pointer_subjects: parse_usize("pointer_subjects", fields[8])?,
                    blocked_subjects: parse_usize("blocked_subjects", fields[9])?,
                };
                validate_s36_function(fields[5], &evidence)?;
                if artifact
                    .s36_functions
                    .insert(fields[5].to_owned(), evidence)
                    .is_some()
                {
                    return Err(format!("duplicate aligned root identity {}", fields[5]));
                }
                if aligned_roots
                    .insert(
                        fields[5].to_owned(),
                        (historical, fields[10].to_owned(), fields[11].to_owned()),
                    )
                    .is_some()
                {
                    return Err(format!("duplicate aligned root row {}", fields[5]));
                }
            }
            "PBALIGNREACH" => {
                check_identity(7)?;
                validate_atom("function", fields[5])?;
                let is_root = match fields[6] {
                    "0" => false,
                    "1" => true,
                    value => return Err(format!("invalid aligned reach root flag {value:?}")),
                };
                if aligned_reachable
                    .insert(fields[5].to_owned(), is_root)
                    .is_some()
                {
                    return Err(format!(
                        "duplicate aligned reachable identity {}",
                        fields[5]
                    ));
                }
            }
            "PBROOTDIFF" => {
                check_identity(8)?;
                validate_atom("function", fields[5])?;
                let cause = RootDifferenceCause::parse(fields[7])?;
                let previous = match fields[6] {
                    "p-b-only" => reconciliation.p_b_only.insert(fields[5].to_owned(), cause),
                    "s36-only" => reconciliation.s36_only.insert(fields[5].to_owned(), cause),
                    value => return Err(format!("invalid root-difference side {value:?}")),
                };
                if previous.is_some() {
                    return Err(format!("duplicate root-difference identity {}", fields[5]));
                }
            }
            "PBREFSITE" => {
                check_identity(10)?;
                for (kind, value) in [
                    ("function", fields[5]),
                    ("reference owner", fields[8]),
                    ("reference site", fields[9]),
                ] {
                    validate_atom(kind, value)?;
                }
                reference_sites
                    .entry(fields[5].to_owned())
                    .or_default()
                    .push(ReferenceSite {
                        owner_path: fields[8].to_owned(),
                        owner_kind: BodyOwnerKind::parse(fields[6])?,
                        ref_kind: ReferenceKind::parse(fields[7])?,
                        site: fields[9].to_owned(),
                    });
            }
            _ => unreachable!(),
        }
    }
    let (
        root_count,
        web_count,
        intersection_count,
        p_b_only_count,
        s36_only_count,
        pointer_subjects,
        blocked_subjects,
        aligned_coverage,
        aligned_resolution,
        reference_site_count,
    ) = declared.ok_or_else(|| "missing PBALIGNCOUNT row".to_owned())?;
    if aligned_roots.len() != root_count || aligned_reachable.len() != web_count {
        return Err(format!(
            "aligned inventory mismatch: roots={}/{} web={}/{}",
            aligned_roots.len(),
            root_count,
            aligned_reachable.len(),
            web_count
        ));
    }
    let aligned_root_set = aligned_roots.keys().cloned().collect::<BTreeSet<_>>();
    let aligned_reachable_set = aligned_reachable.keys().cloned().collect::<BTreeSet<_>>();
    if !aligned_root_set.is_subset(&aligned_reachable_set) {
        return Err("aligned roots are not a subset of the aligned web".to_owned());
    }
    for (name, is_root) in &aligned_reachable {
        if *is_root != aligned_root_set.contains(name) {
            return Err(format!("aligned reachable/root flag mismatch for {name}"));
        }
    }
    let intersection = artifact
        .graph
        .fn_ptr_roots
        .intersection(&aligned_root_set)
        .cloned()
        .collect::<BTreeSet<_>>();
    if intersection.len() != intersection_count
        || reconciliation.p_b_only.len() != p_b_only_count
        || reconciliation.s36_only.len() != s36_only_count
        || reconciliation
            .p_b_only
            .keys()
            .cloned()
            .collect::<BTreeSet<_>>()
            != artifact
                .graph
                .fn_ptr_roots
                .difference(&aligned_root_set)
                .cloned()
                .collect()
        || reconciliation
            .s36_only
            .keys()
            .cloned()
            .collect::<BTreeSet<_>>()
            != aligned_root_set
                .difference(&artifact.graph.fn_ptr_roots)
                .cloned()
                .collect()
    {
        return Err("root reconciliation inventory mismatch".to_owned());
    }
    reconciliation.intersection = intersection.clone();
    for (name, (historical, relation, cause)) in &aligned_roots {
        if *historical != artifact.graph.fn_ptr_roots.contains(name) {
            return Err(format!("aligned historical-root flag mismatch for {name}"));
        }
        match (
            intersection.contains(name),
            relation.as_str(),
            cause.as_str(),
        ) {
            (true, "intersection", "-") => {}
            (false, "s36-only", value)
                if reconciliation
                    .s36_only
                    .get(name)
                    .is_some_and(|entry| entry.key() == value) => {}
            _ => return Err(format!("aligned root relation/cause mismatch for {name}")),
        }
    }
    if artifact
        .s36_functions
        .values()
        .map(|evidence| evidence.pointer_subjects)
        .sum::<usize>()
        != pointer_subjects
        || artifact
            .s36_functions
            .values()
            .map(|evidence| evidence.blocked_subjects)
            .sum::<usize>()
            != blocked_subjects
    {
        return Err("S3.6 subject totals do not match aligned root rows".to_owned());
    }
    let measured_site_count = reference_sites.values().map(Vec::len).sum::<usize>();
    let difference_names = reconciliation
        .p_b_only
        .keys()
        .chain(reconciliation.s36_only.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    if measured_site_count != reference_site_count
        || reference_sites.keys().cloned().collect::<BTreeSet<_>>() != difference_names
    {
        return Err("reference-site evidence inventory mismatch".to_owned());
    }
    let aligned_overlap = aligned_root_set
        .intersection(&artifact.graph.public_roots)
        .cloned()
        .collect::<BTreeSet<_>>();
    artifact.aligned_graph = GraphMeasurement {
        fn_ptr_roots: aligned_root_set,
        public_roots: artifact.graph.public_roots.clone(),
        root_public_overlap: aligned_overlap,
        reachable: aligned_reachable_set,
    };
    artifact.aligned_coverage = aligned_coverage;
    artifact.aligned_resolution = aligned_resolution;
    artifact.reconciliation = reconciliation;
    artifact.reference_sites = reference_sites;
    Ok(artifact)
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

fn load_s36_program(
    snapshot: &Path,
    program: &str,
) -> Result<BTreeMap<String, S36FunctionEvidence>, String> {
    let facts_path = snapshot.join(format!("{program}.facts.tsv"));
    let outcome_path = snapshot.join(format!("{program}.a.jsonl"));
    let facts = fs::read_to_string(&facts_path)
        .map_err(|error| format!("read S3.6 facts {}: {error}", facts_path.display()))?;
    let outcomes = fs::read_to_string(&outcome_path)
        .map_err(|error| format!("read S3.6 outcomes {}: {error}", outcome_path.display()))?;
    parse_s36_program(&facts, &outcomes)
}

fn validate_s36_reference_sites(
    functions: &BTreeMap<String, S36FunctionEvidence>,
    sites: &BTreeMap<String, Vec<ReferenceSite>>,
) -> Result<(), String> {
    for (name, evidence) in functions {
        let measured = sites
            .get(name)
            .into_iter()
            .flatten()
            .map(|site| site.ref_kind)
            .collect::<BTreeSet<_>>();
        if measured != evidence.ref_kinds {
            return Err(format!(
                "S3.6 reference identity mismatch for {name}: snapshot={:?} measured={:?}",
                evidence
                    .ref_kinds
                    .iter()
                    .map(|kind| kind.key())
                    .collect::<Vec<_>>(),
                measured.iter().map(|kind| kind.key()).collect::<Vec<_>>()
            ));
        }
    }
    Ok(())
}

fn measure_call_graph(
    tcx: TyCtxt<'_>,
    program: &crate::utils::rustc::RustProgram<'_>,
    roots: &FxHashSet<LocalDefId>,
    public_roots: &FxHashSet<LocalDefId>,
    program_name: &str,
    label: &str,
) -> Result<
    (
        GraphMeasurement,
        CoverageCounts,
        ResolutionEdgeCounts,
        Duration,
    ),
    String,
> {
    let functions = program.functions.iter().copied().collect::<FxHashSet<_>>();
    mark_phase(program_name, &format!("{label}-andersen"))?;
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

    mark_phase(program_name, &format!("{label}-call-graph"))?;
    let mut coverage = CoverageCounts::default();
    let mut direct_edges = BTreeSet::new();
    let mut andersen_edges = BTreeSet::new();
    let mut unresolved_sites = BTreeSet::new();
    let mut graph = BTreeMap::new();
    for &function in &program.functions {
        graph.insert(
            tcx.def_path_str(function.to_def_id()),
            GraphNode {
                fn_ptr_root: roots.contains(&function),
                public_root: public_roots.contains(&function),
                callees: BTreeSet::new(),
            },
        );
    }
    for &caller in &program.functions {
        let caller_path = tcx.def_path_str(caller.to_def_id());
        let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
        for (block, block_data) in body.basic_blocks.iter_enumerated() {
            let function = match &block_data.terminator().kind {
                TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. } => func,
                _ => continue,
            };
            coverage.calls_total += 1;
            let constant = function.constant();
            let constant_target = constant.and_then(|function| {
                let TyKind::FnDef(target, _) = *function.ty().kind() else {
                    return None;
                };
                Some(target)
            });
            let route = classify_call_route(constant.is_some(), constant_target.is_some());
            let targets = match route {
                CallRoute::UnsupportedConstant => {
                    coverage.non_fn_def_constant += 1;
                    return Err(format!(
                        "unsupported constant non-FnDef callable in {caller_path}:bb{}; Andersen has no indirect-call site",
                        block.index()
                    ));
                }
                CallRoute::Direct => {
                    let target = constant_target.expect("direct route has a FnDef target");
                    let Some(target) = target.as_local() else {
                        coverage.direct_external += 1;
                        continue;
                    };
                    if !functions.contains(&target) {
                        coverage.direct_external += 1;
                        continue;
                    }
                    coverage.direct_local += 1;
                    direct_edges
                        .insert((caller_path.clone(), tcx.def_path_str(target.to_def_id())));
                    vec![target]
                }
                CallRoute::AndersenIndirect => {
                    let targets = indirect_targets(&pre, &solutions, caller, block)?
                        .into_iter()
                        .filter(|target| functions.contains(target))
                        .collect::<Vec<_>>();
                    if targets.is_empty() {
                        coverage.indirect_unresolved += 1;
                        unresolved_sites.insert((caller_path.clone(), block.index()));
                        continue;
                    }
                    coverage.indirect_local += 1;
                    andersen_edges.extend(
                        targets.iter().map(|target| {
                            (caller_path.clone(), tcx.def_path_str(target.to_def_id()))
                        }),
                    );
                    targets
                }
            };
            add_local_call_edges(
                &mut graph,
                &caller_path,
                route,
                targets
                    .iter()
                    .map(|target| tcx.def_path_str(target.to_def_id())),
            )?;
        }
    }
    coverage.validate()?;
    let measured = measure_graph(&graph)?;
    let resolution = resolution_counts_for_web(
        &measured.reachable,
        &direct_edges,
        &andersen_edges,
        &unresolved_sites,
    );
    Ok((measured, coverage, resolution, andersen_time))
}

fn measure_tcx(tcx: TyCtxt<'_>) -> Result<(WorkerArtifact, Duration, Duration), String> {
    let program_name = std::env::var("CRAT_BOC1_NAME").unwrap_or_else(|_| "unnamed".to_owned());
    let snapshot = PathBuf::from(
        std::env::var_os("CRAT_PB_SNAPSHOT")
            .ok_or_else(|| "worker requires CRAT_PB_SNAPSHOT".to_owned())?,
    );
    mark_phase(&program_name, "snapshot-input")?;
    let s36_all = load_s36_program(&snapshot, &program_name)?;
    let program = super::collect_program(tcx);
    let reference_sites = collect_reference_sites(tcx, &program.functions)?;
    validate_s36_reference_sites(&s36_all, &reference_sites)?;

    let function_by_name = program
        .functions
        .iter()
        .copied()
        .map(|did| (tcx.def_path_str(did.to_def_id()), did))
        .collect::<BTreeMap<_, _>>();
    let fn_ptrs = crate::rewriter::collector::collect_fn_ptrs(&program);
    let fn_ptr_roots = program
        .functions
        .iter()
        .copied()
        .filter(|function| fn_ptrs.contains(function))
        .collect::<FxHashSet<_>>();
    let p_b_names = fn_ptr_roots
        .iter()
        .map(|did| tcx.def_path_str(did.to_def_id()))
        .collect::<BTreeSet<_>>();
    let reconciliation = reconcile_roots(&p_b_names, &s36_all, &reference_sites)?;
    let s36_functions = s36_all
        .iter()
        .filter_map(|(name, evidence)| {
            (evidence.ref_class == "pinned").then_some((name.clone(), evidence.clone()))
        })
        .collect::<BTreeMap<_, _>>();
    let aligned_roots = s36_functions
        .keys()
        .map(|name| {
            function_by_name
                .get(name)
                .copied()
                .ok_or_else(|| format!("S3.6 pinned identity is not a local function: {name}"))
        })
        .collect::<Result<FxHashSet<_>, String>>()?;
    let public_roots = program
        .functions
        .iter()
        .copied()
        .filter(|function| tcx.visibility(function.to_def_id()).is_public())
        .collect::<FxHashSet<_>>();

    let (graph, coverage, _historical_resolution, historical_andersen) = measure_call_graph(
        tcx,
        &program,
        &fn_ptr_roots,
        &public_roots,
        &program_name,
        "historical",
    )?;
    let (aligned_graph, aligned_coverage, aligned_resolution, aligned_andersen) =
        measure_call_graph(
            tcx,
            &program,
            &aligned_roots,
            &public_roots,
            &program_name,
            "aligned",
        )?;
    mark_phase(&program_name, "reconcile")?;
    let difference_names = reconciliation
        .p_b_only
        .keys()
        .chain(reconciliation.s36_only.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    let reference_sites = reference_sites
        .into_iter()
        .filter(|(name, _)| difference_names.contains(name))
        .collect::<BTreeMap<_, _>>();
    Ok((
        WorkerArtifact {
            graph,
            aligned_graph,
            local_functions: program.functions.len(),
            coverage,
            aligned_coverage,
            aligned_resolution,
            s36_functions,
            reconciliation,
            reference_sites,
        },
        historical_andersen,
        aligned_andersen,
    ))
}

pub(super) fn run_worker(tcx: TyCtxt<'_>, t_tcx: Duration) -> super::report::Row {
    let t0 = Instant::now();
    let program = std::env::var("CRAT_BOC1_NAME").unwrap_or_else(|_| "unnamed".to_owned());
    let machine_id = std::env::var("CRAT_MEASUREMENT_MACHINE_ID")
        .unwrap_or_else(|_| "missing-machine".to_owned());
    let platform = std::env::var("CRAT_MEASUREMENT_PLATFORM")
        .unwrap_or_else(|_| "missing-platform".to_owned());
    let initial_phase = mark_phase(&program, "collect-roots");
    let mut row = super::report::Row::default();
    row.set("machine_id", &machine_id);
    row.set("platform", &platform);
    match initial_phase.and_then(|()| measure_tcx(tcx)).and_then(
        |(artifact, historical_andersen, aligned_andersen)| {
            let rendered =
                render_reconciled_worker_artifact(&machine_id, &platform, &program, &artifact)?;
            print!("{rendered}");
            row.set("status", "ok");
            row.set("roots", artifact.graph.fn_ptr_roots.len());
            row.set("aligned_roots", artifact.aligned_graph.fn_ptr_roots.len());
            row.set("public_roots", artifact.graph.public_roots.len());
            row.set(
                "root_public_overlap",
                artifact.graph.root_public_overlap.len(),
            );
            row.set("web", artifact.graph.reachable.len());
            row.set("aligned_web", artifact.aligned_graph.reachable.len());
            row.set(
                "root_intersection",
                artifact.reconciliation.intersection.len(),
            );
            row.set("p_b_only", artifact.reconciliation.p_b_only.len());
            row.set("s36_only", artifact.reconciliation.s36_only.len());
            row.set(
                "s36_pointer_subjects",
                artifact
                    .s36_functions
                    .values()
                    .map(|evidence| evidence.pointer_subjects)
                    .sum::<usize>(),
            );
            row.set(
                "s36_blocked_subjects",
                artifact
                    .s36_functions
                    .values()
                    .map(|evidence| evidence.blocked_subjects)
                    .sum::<usize>(),
            );
            row.set("local_functions", artifact.local_functions);
            row.set("calls_total", artifact.coverage.calls_total);
            row.set("direct_local", artifact.coverage.direct_local);
            row.set("indirect_local", artifact.coverage.indirect_local);
            row.set("direct_external", artifact.coverage.direct_external);
            row.set("indirect_unresolved", artifact.coverage.indirect_unresolved);
            row.set("non_fn_def_constant", artifact.coverage.non_fn_def_constant);
            row.set(
                "aligned_indirect_local",
                artifact.aligned_coverage.indirect_local,
            );
            row.set(
                "aligned_indirect_unresolved",
                artifact.aligned_coverage.indirect_unresolved,
            );
            row.set(
                "aligned_direct_local_edges",
                artifact.aligned_resolution.direct_local_edges,
            );
            row.set(
                "aligned_andersen_local_edges",
                artifact.aligned_resolution.andersen_local_edges,
            );
            row.set(
                "t_historical_andersen_s",
                format!("{:.3}", historical_andersen.as_secs_f64()),
            );
            row.set(
                "t_aligned_andersen_s",
                format!("{:.3}", aligned_andersen.as_secs_f64()),
            );
            Ok::<(), String>(())
        },
    ) {
        Ok(()) => {
            if let Err(error) = mark_phase(&program, "complete") {
                row.set("status", "schema-error");
                row.set("detail", error);
            }
        }
        Err(error) => {
            row.set("status", "schema-error");
            row.set("detail", error);
        }
    }
    row.set("t_tcx_s", format!("{:.3}", t_tcx.as_secs_f64()));
    row.set("t_total_s", format!("{:.3}", t0.elapsed().as_secs_f64()));
    row
}

fn sha256_file(path: &Path) -> Result<String, String> {
    let output = Command::new("sha256sum")
        .arg(path)
        .output()
        .map_err(|error| format!("run sha256sum for {}: {error}", path.display()))?;
    if !output.status.success() {
        return Err(format!(
            "sha256sum failed for {}: {}",
            path.display(),
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    String::from_utf8_lossy(&output.stdout)
        .split_whitespace()
        .next()
        .filter(|digest| digest.len() == 64)
        .map(str::to_owned)
        .ok_or_else(|| format!("invalid sha256sum output for {}", path.display()))
}

fn sha256_text(input: &str) -> Result<String, String> {
    let mut child = Command::new("sha256sum")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| format!("spawn sha256sum: {error}"))?;
    child
        .stdin
        .take()
        .ok_or_else(|| "open sha256sum stdin".to_owned())?
        .write_all(input.as_bytes())
        .map_err(|error| format!("write sha256sum stdin: {error}"))?;
    let output = child
        .wait_with_output()
        .map_err(|error| format!("wait for sha256sum: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "sha256sum failed: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    String::from_utf8_lossy(&output.stdout)
        .split_whitespace()
        .next()
        .filter(|digest| digest.len() == 64)
        .map(str::to_owned)
        .ok_or_else(|| "invalid sha256sum output for text".to_owned())
}

fn raw_corpus_digest(workspace: &Path, relative: &str) -> Result<String, String> {
    let output = Command::new("find")
        .args(["-L", relative, "-type", "f", "-name", "*.rs"])
        .current_dir(workspace)
        .output()
        .map_err(|error| format!("enumerate {relative}: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "enumerate {relative}: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    let mut files = String::from_utf8(output.stdout)
        .map_err(|error| format!("non-UTF8 corpus path: {error}"))?
        .lines()
        .map(str::to_owned)
        .collect::<Vec<_>>();
    files.sort();
    let mut first_level = String::new();
    for chunk in files.chunks(200) {
        let output = Command::new("sha256sum")
            .args(chunk)
            .current_dir(workspace)
            .output()
            .map_err(|error| format!("hash {relative}: {error}"))?;
        if !output.status.success() {
            return Err(format!(
                "hash {relative}: {}",
                String::from_utf8_lossy(&output.stderr).trim()
            ));
        }
        first_level.push_str(&String::from_utf8_lossy(&output.stdout));
    }
    sha256_text(&first_level)
}

fn collect_tree_files(
    root: &Path,
    directory: &Path,
    files: &mut Vec<(String, String)>,
) -> Result<(), String> {
    let mut entries = fs::read_dir(directory)
        .map_err(|error| format!("read digest directory {}: {error}", directory.display()))?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| format!("read digest entry: {error}"))?;
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        let path = entry.path();
        let metadata = fs::symlink_metadata(&path)
            .map_err(|error| format!("digest metadata {}: {error}", path.display()))?;
        if metadata.file_type().is_symlink() {
            continue;
        }
        if metadata.is_dir() {
            if entry.file_name() != "target" {
                collect_tree_files(root, &path, files)?;
            }
        } else if metadata.is_file() {
            let relative = path
                .strip_prefix(root)
                .map_err(|_| format!("digest path {} escaped {}", path.display(), root.display()))?
                .to_string_lossy()
                .replace('\\', "/");
            files.push((relative, sha256_file(&path)?));
        }
    }
    Ok(())
}

fn derived_program_digest(program: &Path) -> Result<String, String> {
    let mut files = Vec::new();
    collect_tree_files(program, program, &mut files)?;
    files.sort();
    let mut identity = String::new();
    for (relative, digest) in files {
        identity.push_str(&relative);
        identity.push('\0');
        identity.push_str(&digest);
        identity.push('\n');
    }
    sha256_text(&identity)
}

fn derived_corpus_digest(root: &Path) -> Result<String, String> {
    let mut programs = fs::read_dir(root)
        .map_err(|error| format!("read derived corpus {}: {error}", root.display()))?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| format!("read derived corpus entry: {error}"))?;
    programs.sort_by_key(|entry| entry.file_name());
    let mut identity = String::new();
    for program in programs {
        let metadata = fs::metadata(program.path())
            .map_err(|error| format!("derived program metadata: {error}"))?;
        if !metadata.is_dir() || program.file_name() == "_logs" {
            continue;
        }
        let name = program.file_name().to_string_lossy().into_owned();
        identity.push_str(&name);
        identity.push('\0');
        identity.push_str(&derived_program_digest(&program.path())?);
        identity.push('\n');
    }
    sha256_text(&identity)
}

fn s36_rs_corpus_digest(root: &Path) -> Result<String, String> {
    let output = Command::new("find")
        .args([".", "-type", "f", "-name", "*.rs"])
        .current_dir(root)
        .output()
        .map_err(|error| format!("enumerate S3.6 Rust substrate: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "enumerate S3.6 Rust substrate: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    let mut files = String::from_utf8(output.stdout)
        .map_err(|error| format!("non-UTF8 S3.6 corpus path: {error}"))?
        .lines()
        .map(str::to_owned)
        .collect::<Vec<_>>();
    files.sort();
    let mut first_level = String::new();
    for chunk in files.chunks(200) {
        let output = Command::new("sha256sum")
            .args(chunk)
            .current_dir(root)
            .output()
            .map_err(|error| format!("hash S3.6 Rust substrate: {error}"))?;
        if !output.status.success() {
            return Err(format!(
                "hash S3.6 Rust substrate: {}",
                String::from_utf8_lossy(&output.stderr).trim()
            ));
        }
        first_level.push_str(&String::from_utf8_lossy(&output.stdout));
    }
    sha256_text(&first_level)
}

fn verify_s36_population(snapshot: &Path) -> Result<(), String> {
    let mut pinned_functions = 0usize;
    let mut pinned_subject_rows = 0usize;
    let mut pinned_blocked_subjects = 0usize;
    let mut adaptable_blocked_subjects = 0usize;
    let mut all_blocked_subjects = 0usize;
    let mut tulip_blocked = 0usize;
    let mut addr_taken = 0usize;
    for corpus_program in super::CORPUS {
        let functions = load_s36_program(snapshot, corpus_program.name)?;
        for evidence in functions.values() {
            all_blocked_subjects += evidence.blocked_subjects;
            if evidence.ref_class == "adaptable" {
                adaptable_blocked_subjects += evidence.blocked_subjects;
            }
            if evidence.ref_kinds.contains(&ReferenceKind::AddrTaken) {
                addr_taken += 1;
            }
            if evidence.ref_class == "pinned" {
                pinned_functions += 1;
                pinned_subject_rows += evidence.pointer_subjects;
                pinned_blocked_subjects += evidence.blocked_subjects;
                if corpus_program.name == "tulipindicators" {
                    tulip_blocked += evidence.blocked_subjects;
                }
            }
        }
    }
    if (
        pinned_functions,
        pinned_subject_rows,
        pinned_blocked_subjects,
        adaptable_blocked_subjects,
        all_blocked_subjects,
        tulip_blocked,
        addr_taken,
    ) != (295, 992, 640, 2_686, 3_326, 558, 0)
    {
        return Err(format!(
            "S3.6 aggregate drift: pinned_functions={pinned_functions} pinned_subject_rows={pinned_subject_rows} pinned_blocked_subjects={pinned_blocked_subjects} adaptable_blocked_subjects={adaptable_blocked_subjects} all_blocked_subjects={all_blocked_subjects} tulip_blocked={tulip_blocked} addr_taken_functions={addr_taken}"
        ));
    }
    Ok(())
}

fn verify_snapshot(snapshot: &Path) -> Result<String, String> {
    let document = snapshot.join("MANIFEST.md");
    let sums = snapshot.join("SHA256SUMS.txt");
    if sha256_file(&document)? != SNAPSHOT_MANIFEST_DOCUMENT_SHA256 {
        return Err("snapshot manifest document SHA-256 drifted".to_owned());
    }
    if sha256_file(&sums)? != SNAPSHOT_SHA256SUMS_SHA256 {
        return Err("snapshot SHA256SUMS.txt SHA-256 drifted".to_owned());
    }
    let document_text = fs::read_to_string(&document)
        .map_err(|error| format!("read snapshot manifest {}: {error}", document.display()))?;
    for required in [SNAPSHOT_PRODUCER, S36_RS_CORPUS_SHA256, "295", "640", "558"] {
        if !document_text.contains(required) {
            return Err(format!(
                "snapshot MANIFEST.md lacks required witness {required}"
            ));
        }
    }
    let input = fs::read_to_string(&sums)
        .map_err(|error| format!("read snapshot sums {}: {error}", sums.display()))?;
    let mut entries = BTreeMap::new();
    for line in input.lines() {
        let fields = line.split_whitespace().collect::<Vec<_>>();
        if fields.len() != 2 || fields[0].len() != 64 {
            return Err(format!("invalid snapshot manifest row {line:?}"));
        }
        if entries
            .insert(fields[1].to_owned(), fields[0].to_owned())
            .is_some()
        {
            return Err(format!("duplicate snapshot filename {}", fields[1]));
        }
    }
    if entries.len() != 100 {
        return Err(format!(
            "snapshot manifest population mismatch: expected 100, got {}",
            entries.len()
        ));
    }
    let actual = fs::read_dir(snapshot)
        .map_err(|error| format!("read snapshot {}: {error}", snapshot.display()))?
        .map(|entry| {
            let entry = entry.map_err(|error| format!("snapshot entry: {error}"))?;
            if !entry
                .file_type()
                .map_err(|error| format!("snapshot file type: {error}"))?
                .is_file()
            {
                return Err(format!(
                    "snapshot contains non-file {}",
                    entry.path().display()
                ));
            }
            Ok(entry.file_name().to_string_lossy().into_owned())
        })
        .collect::<Result<BTreeSet<_>, String>>()?;
    let mut expected_files = entries.keys().cloned().collect::<BTreeSet<_>>();
    expected_files.extend(["MANIFEST.md".to_owned(), "SHA256SUMS.txt".to_owned()]);
    if actual != expected_files {
        return Err("snapshot filename inventory drifted".to_owned());
    }
    for (name, expected) in &entries {
        let actual = sha256_file(&snapshot.join(name))?;
        if &actual != expected {
            return Err(format!(
                "snapshot hash mismatch for {name}: expected {expected}, got {actual}"
            ));
        }
    }
    let canonical = entries
        .iter()
        .map(|(name, digest)| format!("{digest}  {name}\n"))
        .collect::<String>();
    let inventory = sha256_text(&canonical)?;
    if inventory != SNAPSHOT_SHA256SUMS_SHA256 {
        return Err("snapshot canonical inventory differs from SHA256SUMS.txt".to_owned());
    }
    verify_s36_population(snapshot)?;
    Ok(inventory)
}

fn write_sha256_manifest(root: &Path, files: &[PathBuf], manifest: &Path) -> Result<(), String> {
    let mut entries = files
        .iter()
        .map(|path| {
            let relative = path.strip_prefix(root).map_err(|_| {
                format!(
                    "manifest path {} is outside {}",
                    path.display(),
                    root.display()
                )
            })?;
            Ok((relative.to_path_buf(), sha256_file(path)?))
        })
        .collect::<Result<Vec<_>, String>>()?;
    entries.sort_by(|left, right| left.0.cmp(&right.0));
    let rendered = entries
        .iter()
        .map(|(relative, digest)| format!("{digest}  ./{}\n", relative.display()))
        .collect::<String>();
    fs::write(manifest, rendered)
        .map_err(|error| format!("write manifest {}: {error}", manifest.display()))
}

fn verify_sha256_manifest(root: &Path, manifest: &Path) -> Result<(), String> {
    let relative = manifest.strip_prefix(root).map_err(|_| {
        format!(
            "manifest {} is outside {}",
            manifest.display(),
            root.display()
        )
    })?;
    let output = Command::new("sha256sum")
        .args(["-c"])
        .arg(relative)
        .current_dir(root)
        .output()
        .map_err(|error| format!("verify manifest {}: {error}", manifest.display()))?;
    if output.status.success() {
        Ok(())
    } else {
        Err(format!(
            "manifest verification failed at {}: {} {}",
            manifest.display(),
            String::from_utf8_lossy(&output.stdout).trim(),
            String::from_utf8_lossy(&output.stderr).trim()
        ))
    }
}

fn parse_receipt(path: &Path) -> Result<BTreeMap<String, String>, String> {
    let input = fs::read_to_string(path)
        .map_err(|error| format!("read receipt {}: {error}", path.display()))?;
    let mut values = BTreeMap::new();
    for (offset, line) in input.lines().enumerate() {
        let Some((key, value)) = line.split_once('=') else {
            return Err(format!("receipt line {} lacks '='", offset + 1));
        };
        if values.insert(key.to_owned(), value.to_owned()).is_some() {
            return Err(format!("duplicate receipt key {key:?}"));
        }
    }
    Ok(values)
}

fn phase_from_stderr(stderr: &str) -> &str {
    stderr
        .lines()
        .filter_map(|line| line.strip_prefix("BOC1PHASE p-b phase="))
        .next_back()
        .and_then(|rest| rest.split_whitespace().next())
        .unwrap_or("not-started")
}

fn write_phase_checkpoint(
    path: &Path,
    program: &str,
    phase: &str,
    timestamp_unix_ms: u128,
) -> Result<(), String> {
    validate_atom("program", program)?;
    validate_atom("phase", phase)?;
    let parent = path
        .parent()
        .ok_or_else(|| format!("checkpoint {} has no parent", path.display()))?;
    fs::create_dir_all(parent)
        .map_err(|error| format!("create checkpoint parent {}: {error}", parent.display()))?;
    let extension = path
        .extension()
        .and_then(|value| value.to_str())
        .map_or_else(|| "tmp".to_owned(), |value| format!("{value}.tmp"));
    let temporary = path.with_extension(extension);
    fs::write(
        &temporary,
        format!(
            "machine_id={MACHINE_ID}\nplatform={PLATFORM}\nprogram={program}\nphase={phase}\ntimestamp_unix_ms={timestamp_unix_ms}\n"
        ),
    )
    .map_err(|error| format!("write checkpoint {}: {error}", temporary.display()))?;
    fs::rename(&temporary, path).map_err(|error| {
        format!(
            "publish checkpoint {} -> {}: {error}",
            temporary.display(),
            path.display()
        )
    })
}

fn mark_phase(program: &str, phase: &str) -> Result<(), String> {
    eprintln!("BOC1PHASE p-b phase={phase} program={program}");
    let Some(path) = std::env::var_os("CRAT_PB_CHECKPOINT") else {
        return Ok(());
    };
    let timestamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|error| format!("checkpoint clock before epoch: {error}"))?
        .as_millis();
    write_phase_checkpoint(&PathBuf::from(path), program, phase, timestamp)
}

fn validate_completed_state(status: &str, data: bool, phase: &str) -> Result<(), String> {
    if status == "ok" && data && phase == "complete" {
        Ok(())
    } else {
        Err(format!(
            "incomplete data: status={status} data={data} phase={phase}"
        ))
    }
}

fn wall_liveness(value: Option<&str>) -> Result<Duration, String> {
    let seconds = match value {
        Some(value) => value
            .parse::<u64>()
            .map_err(|error| format!("invalid P-b wall liveness {value:?}: {error}"))?,
        None => WALL_LIVENESS_SECS,
    };
    if seconds != WALL_LIVENESS_SECS {
        return Err(format!(
            "P-b wall-liveness bound must be exactly {WALL_LIVENESS_SECS}s, got {seconds}s"
        ));
    }
    Ok(Duration::from_secs(seconds))
}

fn render_root_rows(program: &str, artifact: &WorkerArtifact) -> String {
    let mut out = String::from("platform\tmachine_id\tprogram\tfunction\tis_public\n");
    for name in &artifact.graph.fn_ptr_roots {
        out.push_str(&format!(
            "{PLATFORM}\t{MACHINE_ID}\t{program}\t{name}\t{}\n",
            usize::from(artifact.graph.public_roots.contains(name))
        ));
    }
    out
}

fn render_public_root_rows(program: &str, artifact: &WorkerArtifact) -> String {
    let mut out = String::from("platform\tmachine_id\tprogram\tfunction\tis_fn_ptr_root\n");
    for name in &artifact.graph.public_roots {
        out.push_str(&format!(
            "{PLATFORM}\t{MACHINE_ID}\t{program}\t{name}\t{}\n",
            usize::from(artifact.graph.fn_ptr_roots.contains(name))
        ));
    }
    out
}

fn render_reachable_rows(program: &str, artifact: &WorkerArtifact) -> String {
    let mut out = String::from("platform\tmachine_id\tprogram\tfunction\tis_root\n");
    for name in &artifact.graph.reachable {
        out.push_str(&format!(
            "{PLATFORM}\t{MACHINE_ID}\t{program}\t{name}\t{}\n",
            usize::from(artifact.graph.fn_ptr_roots.contains(name))
        ));
    }
    out
}

fn render_aligned_root_rows(program: &str, artifact: &WorkerArtifact) -> String {
    let mut out = String::from(
        "platform\tmachine_id\tprogram\tfunction\tis_historical_root\tref_kinds\tpointer_subjects\tblocked_subjects\trelation\tcause\n",
    );
    for (name, evidence) in &artifact.s36_functions {
        let (relation, cause) = if artifact.reconciliation.intersection.contains(name) {
            ("intersection", "-")
        } else {
            ("s36-only", artifact.reconciliation.s36_only[name].key())
        };
        let kinds = evidence
            .ref_kinds
            .iter()
            .map(|kind| kind.key())
            .collect::<Vec<_>>()
            .join(",");
        out.push_str(&format!(
            "{PLATFORM}\t{MACHINE_ID}\t{program}\t{name}\t{}\t{kinds}\t{}\t{}\t{relation}\t{cause}\n",
            usize::from(artifact.graph.fn_ptr_roots.contains(name)),
            evidence.pointer_subjects,
            evidence.blocked_subjects,
        ));
    }
    out
}

fn render_aligned_reachable_rows(program: &str, artifact: &WorkerArtifact) -> String {
    let mut out = String::from("platform\tmachine_id\tprogram\tfunction\tis_root\n");
    for name in &artifact.aligned_graph.reachable {
        out.push_str(&format!(
            "{PLATFORM}\t{MACHINE_ID}\t{program}\t{name}\t{}\n",
            usize::from(artifact.aligned_graph.fn_ptr_roots.contains(name))
        ));
    }
    out
}

fn render_reconciliation_rows(program: &str, artifact: &WorkerArtifact) -> String {
    let mut out = String::from("platform\tmachine_id\tprogram\tfunction\tclass\tcause\n");
    for name in &artifact.reconciliation.intersection {
        out.push_str(&format!(
            "{PLATFORM}\t{MACHINE_ID}\t{program}\t{name}\tintersection\t-\n"
        ));
    }
    for (name, cause) in &artifact.reconciliation.p_b_only {
        out.push_str(&format!(
            "{PLATFORM}\t{MACHINE_ID}\t{program}\t{name}\tp-b-only\t{}\n",
            cause.key()
        ));
    }
    for (name, cause) in &artifact.reconciliation.s36_only {
        out.push_str(&format!(
            "{PLATFORM}\t{MACHINE_ID}\t{program}\t{name}\ts36-only\t{}\n",
            cause.key()
        ));
    }
    out
}

fn render_reference_site_rows(program: &str, artifact: &WorkerArtifact) -> String {
    let mut out = String::from(
        "platform\tmachine_id\tprogram\treferenced_function\towner_path\towner_kind\tref_kind\tsite\n",
    );
    for (name, sites) in &artifact.reference_sites {
        for site in sites {
            out.push_str(&format!(
                "{PLATFORM}\t{MACHINE_ID}\t{program}\t{name}\t{}\t{}\t{}\t{}\n",
                site.owner_path,
                site.owner_kind.key(),
                site.ref_kind.key(),
                site.site,
            ));
        }
    }
    out
}

#[derive(Clone, Debug)]
struct CompletedProgram {
    program: String,
    artifact: WorkerArtifact,
    wall_s: f64,
    peak_rss_kb: u64,
    manifest_sha256: String,
}

fn completed_shard(
    shard: &Path,
    program: &str,
    snapshot_inventory_sha256: &str,
) -> Result<CompletedProgram, String> {
    let manifest = shard.join("artifact-manifest.sha256");
    verify_sha256_manifest(shard, &manifest)?;
    let receipt = parse_receipt(&shard.join("receipt.txt"))?;
    let status = receipt
        .get("status")
        .map(String::as_str)
        .unwrap_or("missing");
    let data = receipt.get("data").map(String::as_str) == Some("true");
    let phase = receipt
        .get("phase")
        .map(String::as_str)
        .unwrap_or("missing");
    if let Err(error) = validate_completed_state(status, data, phase) {
        return Err(format!("published data=false shard: {error}"));
    }
    let checkpoint = parse_receipt(&shard.join("checkpoint.txt"))?;
    for (key, expected) in [
        ("machine_id", MACHINE_ID),
        ("platform", PLATFORM),
        ("program", program),
        ("phase", "complete"),
    ] {
        if checkpoint.get(key).map(String::as_str) != Some(expected) {
            return Err(format!(
                "completed shard {program} checkpoint {key} drifted"
            ));
        }
    }
    let analysis_head = super::orchestrate::git_sha();
    for (key, expected) in [
        ("machine_id", MACHINE_ID),
        ("platform", PLATFORM),
        ("program", program),
        ("status", "ok"),
        ("data", "true"),
        ("phase", "complete"),
        ("analysis_head", analysis_head.as_str()),
        ("raw_corpus_sha256", RAW_CORPUS_SHA256),
        ("derived_corpus_sha256", DERIVED_CORPUS_SHA256),
        ("snapshot_producer", SNAPSHOT_PRODUCER),
        ("snapshot_manifest_commit", SNAPSHOT_MANIFEST_COMMIT),
        (
            "snapshot_manifest_document_sha256",
            SNAPSHOT_MANIFEST_DOCUMENT_SHA256,
        ),
        ("snapshot_inventory_sha256", snapshot_inventory_sha256),
        ("substrate", "derived"),
        ("memory_limit", "uncapped"),
        ("cpu_limit", "uncapped"),
        ("wall_bound_kind", "liveness"),
        ("wall_cap_s", "14400"),
    ] {
        if receipt.get(key).map(String::as_str) != Some(expected) {
            return Err(format!("completed shard {program} receipt {key} drifted"));
        }
    }
    let stdout = fs::read_to_string(shard.join("stdout.txt"))
        .map_err(|error| format!("read {program} stdout: {error}"))?;
    let artifact = parse_reconciled_worker_artifact(MACHINE_ID, PLATFORM, program, &stdout)?;
    if fs::read_to_string(shard.join("roots.tsv")).ok().as_deref()
        != Some(&render_root_rows(program, &artifact))
        || fs::read_to_string(shard.join("public-roots.tsv"))
            .ok()
            .as_deref()
            != Some(&render_public_root_rows(program, &artifact))
        || fs::read_to_string(shard.join("reachable.tsv"))
            .ok()
            .as_deref()
            != Some(&render_reachable_rows(program, &artifact))
        || fs::read_to_string(shard.join("aligned-roots.tsv"))
            .ok()
            .as_deref()
            != Some(&render_aligned_root_rows(program, &artifact))
        || fs::read_to_string(shard.join("aligned-reachable.tsv"))
            .ok()
            .as_deref()
            != Some(&render_aligned_reachable_rows(program, &artifact))
        || fs::read_to_string(shard.join("reconciliation.tsv"))
            .ok()
            .as_deref()
            != Some(&render_reconciliation_rows(program, &artifact))
        || fs::read_to_string(shard.join("reference-sites.tsv"))
            .ok()
            .as_deref()
            != Some(&render_reference_site_rows(program, &artifact))
    {
        return Err(format!("completed shard {program} projection drifted"));
    }
    Ok(CompletedProgram {
        program: program.to_owned(),
        artifact,
        wall_s: receipt
            .get("wall_s")
            .ok_or_else(|| format!("{program} missing wall_s"))?
            .parse()
            .map_err(|error| format!("{program} wall_s: {error}"))?,
        peak_rss_kb: receipt
            .get("peak_rss_kb")
            .ok_or_else(|| format!("{program} missing peak_rss_kb"))?
            .parse()
            .map_err(|error| format!("{program} peak_rss_kb: {error}"))?,
        manifest_sha256: sha256_file(&manifest)?,
    })
}

fn write_shard_receipt(
    path: &Path,
    program: &str,
    status: &str,
    data: bool,
    phase: &str,
    wall_s: f64,
    peak_rss_kb: u64,
    snapshot_inventory_sha256: &str,
    detail: &str,
) -> Result<(), String> {
    let detail = detail.replace(['\n', '\r'], " ");
    fs::write(
        path,
        format!(
            "machine_id={MACHINE_ID}\nplatform={PLATFORM}\nprogram={program}\nstatus={status}\ndata={}\nphase={phase}\nanalysis_head={}\nsubstrate=derived\nraw_corpus_sha256={RAW_CORPUS_SHA256}\nderived_corpus_sha256={DERIVED_CORPUS_SHA256}\nsnapshot_producer={SNAPSHOT_PRODUCER}\nsnapshot_manifest_commit={SNAPSHOT_MANIFEST_COMMIT}\nsnapshot_manifest_document_sha256={SNAPSHOT_MANIFEST_DOCUMENT_SHA256}\nsnapshot_inventory_sha256={snapshot_inventory_sha256}\nmemory_limit=uncapped\ncpu_limit=uncapped\nwall_bound_kind=liveness\nwall_cap_s={WALL_LIVENESS_SECS}\nwall_s={wall_s:.3}\npeak_rss_kb={peak_rss_kb}\ndetail={detail}\n",
            if data { "true" } else { "false" },
            super::orchestrate::git_sha(),
        ),
    )
    .map_err(|error| format!("write receipt {}: {error}", path.display()))
}

#[test]
#[ignore = "P-b function-pointer-web census; run explicitly on the measurement host"]
fn p_b_fn_ptr_web_census() {
    let root = super::orchestrate::workspace_root()
        .canonicalize()
        .expect("canonical workspace root");

    // STOP contract: all invariants are checked before the first worker starts.
    assert_eq!(super::CORPUS.len(), 20, "P-b corpus population drifted");
    assert!(
        std::env::var_os("CRAT_BOC1_PROGRAMS").is_none(),
        "P-b refuses corpus subsets"
    );
    assert_eq!(
        std::env::var("CRAT_MEASUREMENT_MACHINE_ID").as_deref(),
        Ok(MACHINE_ID),
        "P-b requires the registered machine identity"
    );
    assert_eq!(
        std::env::var("CRAT_MEASUREMENT_PLATFORM").as_deref(),
        Ok(PLATFORM),
        "P-b requires the registered platform identity"
    );
    assert_eq!(
        std::env::var("CRAT_BOC1_MEM_MB").as_deref(),
        Ok("uncapped"),
        "P-b runs without a harness RAM cap"
    );
    assert!(
        matches!(
            std::env::var("CRAT_BOC1_SUBSTRATE").as_deref(),
            Err(_) | Ok("derived")
        ),
        "P-b uses only the derived substrate"
    );
    let timeout = wall_liveness(std::env::var("CRAT_PB_TIMEOUT_SECS").ok().as_deref())
        .unwrap_or_else(|error| panic!("P-b STOP: {error}"));
    assert!(
        !super::orchestrate::git_dirty(),
        "commit the green P-b harness before measurement"
    );

    let corpus_link = root.join("benchmarks/rs-crown-derived");
    assert!(
        fs::symlink_metadata(&corpus_link)
            .expect("derived corpus metadata")
            .file_type()
            .is_symlink(),
        "derived corpus must retain its read-only symlink shape"
    );
    let deps_link = root.join("deps_crate/target");
    assert!(
        fs::symlink_metadata(&deps_link)
            .expect("deps metadata")
            .file_type()
            .is_symlink(),
        "deps_crate provisioning must retain its read-only symlink shape"
    );
    let deps = deps_link.join("debug/deps");
    let dep_names = fs::read_dir(&deps)
        .expect("read deps_crate artifacts")
        .filter_map(Result::ok)
        .map(|entry| entry.file_name().to_string_lossy().into_owned())
        .collect::<Vec<_>>();
    assert!(
        dep_names.iter().any(|name| name.ends_with(".rlib")),
        "deps_crate has no Rust library artifacts"
    );
    assert!(
        dep_names.iter().any(|name| name.ends_with(".so")),
        "deps_crate has no Linux proc-macro shared object"
    );

    let raw_digest = raw_corpus_digest(&root, "benchmarks/rs-crown")
        .unwrap_or_else(|error| panic!("raw corpus digest: {error}"));
    assert_eq!(raw_digest, RAW_CORPUS_SHA256, "raw corpus digest drifted");
    let derived_digest = derived_corpus_digest(&corpus_link)
        .unwrap_or_else(|error| panic!("derived corpus digest: {error}"));
    assert_eq!(
        derived_digest, DERIVED_CORPUS_SHA256,
        "derived corpus digest drifted"
    );
    let s36_rs_digest = s36_rs_corpus_digest(&corpus_link)
        .unwrap_or_else(|error| panic!("S3.6 digest-method bridge: {error}"));
    assert_eq!(
        s36_rs_digest, S36_RS_CORPUS_SHA256,
        "S3.6 digest-method bridge drifted"
    );
    let producer_object = Command::new("git")
        .args(["cat-file", "-e", &format!("{SNAPSHOT_PRODUCER}^{{commit}}")])
        .current_dir(&root)
        .status()
        .expect("check S3.6 producer object");
    assert!(producer_object.success(), "S3.6 producer object is absent");

    let snapshot =
        PathBuf::from(std::env::var_os("CRAT_PB_SNAPSHOT").expect("P-b requires CRAT_PB_SNAPSHOT"));
    assert_eq!(
        snapshot.file_name().and_then(|name| name.to_str()),
        Some("e0f33f80"),
        "P-b reconciliation requires snapshot e0f33f80"
    );
    let snapshot_inventory_sha256 =
        verify_snapshot(&snapshot).unwrap_or_else(|error| panic!("P-b snapshot STOP: {error}"));
    let historical_aggregate = PathBuf::from(
        std::env::var_os("CRAT_PB_HISTORICAL_AGGREGATE")
            .expect("P-b reconciliation requires CRAT_PB_HISTORICAL_AGGREGATE"),
    );
    let historical_manifest = historical_aggregate.join("artifact-manifest.sha256");
    assert_eq!(
        sha256_file(&historical_manifest).expect("hash historical P-b manifest"),
        HISTORICAL_AGGREGATE_MANIFEST_SHA256,
        "historical P-b aggregate manifest drifted"
    );
    verify_sha256_manifest(&historical_aggregate, &historical_manifest)
        .unwrap_or_else(|error| panic!("historical P-b aggregate STOP: {error}"));

    let private_out = PathBuf::from(
        std::env::var_os("CRAT_BOC1_OUT").expect("P-b requires a private CRAT_BOC1_OUT"),
    );
    assert!(private_out.is_absolute(), "P-b output must be absolute");
    assert!(
        !private_out.starts_with(root.join("target")),
        "P-b must not write the shared target tree"
    );
    let run_root = private_out.join("p-b");
    let shards = run_root.join("shards");
    fs::create_dir_all(&shards).expect("create P-b shard root");

    let mut completed = Vec::new();
    for corpus_program in super::CORPUS {
        let program = corpus_program.name;
        let shard = shards.join(program);
        let manifest = shard.join("artifact-manifest.sha256");
        if manifest.is_file() {
            completed.push(
                completed_shard(&shard, program, &snapshot_inventory_sha256)
                    .unwrap_or_else(|error| panic!("P-b STOP at {program}: {error}")),
            );
            continue;
        }
        assert!(
            !shard.exists(),
            "P-b STOP: unmanifested partial shard exists for {program} at {}",
            shard.display()
        );
        fs::create_dir(&shard).expect("create program shard");
        let input = corpus_link.join(program).join(corpus_program.lib_root);
        let checkpoint = shard.join("checkpoint.txt");
        let checkpoint_text = checkpoint.to_string_lossy().into_owned();
        let snapshot_text = snapshot.to_string_lossy().into_owned();
        let outcome = super::orchestrate::run_child_labeled(
            program,
            &input,
            "p-b",
            "p-b",
            timeout,
            &[
                ("CRAT_PB_CHECKPOINT", checkpoint_text),
                ("CRAT_PB_SNAPSHOT", snapshot_text),
            ],
        );
        let stdout = shard.join("stdout.txt");
        let stderr = shard.join("stderr.txt");
        fs::write(&stdout, &outcome.stdout).expect("write worker stdout");
        fs::write(&stderr, &outcome.stderr).expect("write worker stderr");
        let phase = phase_from_stderr(&outcome.stderr);
        let parsed =
            parse_reconciled_worker_artifact(MACHINE_ID, PLATFORM, program, &outcome.stdout);
        let (status, detail) = if outcome.status != "ok" {
            (
                outcome.status.as_str(),
                outcome
                    .row
                    .as_ref()
                    .and_then(|row| row.get("detail"))
                    .unwrap_or(&outcome.note)
                    .to_owned(),
            )
        } else if let Err(error) = &parsed {
            ("schema-violation", error.clone())
        } else if phase != "complete" {
            (
                "schema-violation",
                format!("worker reported ok without complete phase (last={phase})"),
            )
        } else {
            ("ok", String::new())
        };
        let data = status == "ok";
        let receipt = shard.join("receipt.txt");
        write_shard_receipt(
            &receipt,
            program,
            status,
            data,
            phase,
            outcome.wall_s,
            outcome.peak_rss_kb,
            &snapshot_inventory_sha256,
            &detail,
        )
        .expect("write shard receipt");
        let mut artifacts = vec![stdout.clone(), stderr.clone(), receipt.clone()];
        if checkpoint.is_file() {
            artifacts.push(checkpoint.clone());
        }
        if let Ok(parsed) = &parsed {
            let roots = shard.join("roots.tsv");
            let public_roots = shard.join("public-roots.tsv");
            let reachable = shard.join("reachable.tsv");
            let aligned_roots = shard.join("aligned-roots.tsv");
            let aligned_reachable = shard.join("aligned-reachable.tsv");
            let reconciliation = shard.join("reconciliation.tsv");
            let reference_sites = shard.join("reference-sites.tsv");
            fs::write(&roots, render_root_rows(program, parsed)).expect("write root inventory");
            fs::write(&public_roots, render_public_root_rows(program, parsed))
                .expect("write public-root inventory");
            fs::write(&reachable, render_reachable_rows(program, parsed))
                .expect("write web inventory");
            fs::write(&aligned_roots, render_aligned_root_rows(program, parsed))
                .expect("write aligned-root inventory");
            fs::write(
                &aligned_reachable,
                render_aligned_reachable_rows(program, parsed),
            )
            .expect("write aligned web inventory");
            fs::write(&reconciliation, render_reconciliation_rows(program, parsed))
                .expect("write reconciliation inventory");
            fs::write(
                &reference_sites,
                render_reference_site_rows(program, parsed),
            )
            .expect("write reference-site evidence");
            artifacts.extend([
                roots,
                public_roots,
                reachable,
                aligned_roots,
                aligned_reachable,
                reconciliation,
                reference_sites,
            ]);
        }
        write_sha256_manifest(&shard, &artifacts, &manifest)
            .unwrap_or_else(|error| panic!("write {program} manifest: {error}"));
        verify_sha256_manifest(&shard, &manifest)
            .unwrap_or_else(|error| panic!("verify {program} manifest: {error}"));
        if !data {
            panic!(
                "P-b STOP: phase={phase} program={program} status={status} wall_s={:.3} peak_rss_kb={} detail={detail}",
                outcome.wall_s, outcome.peak_rss_kb
            );
        }
        completed.push(
            completed_shard(&shard, program, &snapshot_inventory_sha256)
                .unwrap_or_else(|error| panic!("P-b STOP at {program}: {error}")),
        );
    }
    assert_eq!(completed.len(), 20, "P-b completed shard count drifted");

    let aggregate = run_root.join("aggregate");
    let aggregate_manifest = aggregate.join("artifact-manifest.sha256");
    let aggregate_complete = aggregate_manifest.is_file();
    if aggregate_complete {
        verify_sha256_manifest(&aggregate, &aggregate_manifest)
            .unwrap_or_else(|error| panic!("P-b aggregate verification: {error}"));
    } else {
        assert!(
            !aggregate.exists(),
            "P-b STOP: unmanifested partial aggregate exists at {}",
            aggregate.display()
        );
        fs::create_dir(&aggregate).expect("create aggregate");
    }

    let mut per_program = String::from(
        "platform\tmachine_id\tprogram\thistorical_roots\thistorical_web\taligned_shim_functions\taligned_web\taligned_web_minus_roots\tintersection\tp_b_only\ts36_only\tp_b_only_outside_population\tp_b_only_predicate_difference\ts36_only_static_initializer\ts36_only_const_initializer\ts36_only_mixed_initializer\tpinned_pointer_subject_rows\tpinned_blocked_subjects\taligned_calls_total\taligned_direct_local_sites\taligned_indirect_local_sites\taligned_direct_external_sites\taligned_indirect_unresolved_sites\taligned_non_fn_def_constant_sites\taligned_direct_local_edges\taligned_andersen_local_edges\taligned_closure_unresolved_sites\thistorical_calls_total\thistorical_direct_local\thistorical_indirect_local\thistorical_direct_external\thistorical_indirect_unresolved\thistorical_non_fn_def_constant\twall_s\tpeak_rss_kb\tshard_manifest_sha256\n",
    );
    let mut root_rows = String::from("platform\tmachine_id\tprogram\tfunction\tis_public\n");
    let mut public_rows = String::from("platform\tmachine_id\tprogram\tfunction\tis_fn_ptr_root\n");
    let mut reachable_rows = String::from("platform\tmachine_id\tprogram\tfunction\tis_root\n");
    let mut aligned_root_rows = String::from(
        "platform\tmachine_id\tprogram\tfunction\tis_historical_root\tref_kinds\tpointer_subjects\tblocked_subjects\trelation\tcause\n",
    );
    let mut aligned_reachable_rows =
        String::from("platform\tmachine_id\tprogram\tfunction\tis_root\n");
    let mut reconciliation_rows =
        String::from("platform\tmachine_id\tprogram\tfunction\tclass\tcause\n");
    let mut reference_site_rows = String::from(
        "platform\tmachine_id\tprogram\treferenced_function\towner_path\towner_kind\tref_kind\tsite\n",
    );
    let mut table = String::new();
    let mut cause_table = String::new();
    let mut total_historical_roots = 0usize;
    let mut total_historical_web = 0usize;
    let mut total_aligned_roots = 0usize;
    let mut total_aligned_web = 0usize;
    let mut total_intersection = 0usize;
    let mut total_p_b_only = 0usize;
    let mut total_s36_only = 0usize;
    let mut total_pointer_subject_rows = 0usize;
    let mut total_blocked_subjects = 0usize;
    let mut static_s36_only = 0usize;
    let mut outside_population_p_b_only = 0usize;
    let mut wall_sum = 0.0;
    let mut peak_rss_kb = 0u64;
    let mut unresolved_programs = Vec::new();
    for result in &completed {
        let historical = &result.artifact.graph;
        let aligned = &result.artifact.aligned_graph;
        let historical_coverage = &result.artifact.coverage;
        let aligned_coverage = &result.artifact.aligned_coverage;
        let aligned_extra = aligned.reachable.len() - aligned.fn_ptr_roots.len();
        let pointer_subject_rows = result
            .artifact
            .s36_functions
            .values()
            .map(|evidence| evidence.pointer_subjects)
            .sum::<usize>();
        let blocked_subjects = result
            .artifact
            .s36_functions
            .values()
            .map(|evidence| evidence.blocked_subjects)
            .sum::<usize>();
        let cause_count = |rows: &BTreeMap<String, RootDifferenceCause>, expected| {
            rows.values().filter(|cause| **cause == expected).count()
        };
        let p_b_outside = cause_count(
            &result.artifact.reconciliation.p_b_only,
            RootDifferenceCause::OutsideS36PointerSubjectPopulation,
        );
        let p_b_predicate = cause_count(
            &result.artifact.reconciliation.p_b_only,
            RootDifferenceCause::S36ReferencePredicateDifference,
        );
        let s36_static = cause_count(
            &result.artifact.reconciliation.s36_only,
            RootDifferenceCause::StaticInitializerOutsideCollectFnPtrs,
        );
        let s36_const = cause_count(
            &result.artifact.reconciliation.s36_only,
            RootDifferenceCause::ConstInitializerOutsideCollectFnPtrs,
        );
        let s36_mixed = cause_count(
            &result.artifact.reconciliation.s36_only,
            RootDifferenceCause::MixedInitializerOutsideCollectFnPtrs,
        );
        total_historical_roots += historical.fn_ptr_roots.len();
        total_historical_web += historical.reachable.len();
        total_aligned_roots += aligned.fn_ptr_roots.len();
        total_aligned_web += aligned.reachable.len();
        total_intersection += result.artifact.reconciliation.intersection.len();
        total_p_b_only += result.artifact.reconciliation.p_b_only.len();
        total_s36_only += result.artifact.reconciliation.s36_only.len();
        total_pointer_subject_rows += pointer_subject_rows;
        total_blocked_subjects += blocked_subjects;
        static_s36_only += result
            .artifact
            .reconciliation
            .s36_only
            .values()
            .filter(|cause| **cause == RootDifferenceCause::StaticInitializerOutsideCollectFnPtrs)
            .count();
        outside_population_p_b_only += result
            .artifact
            .reconciliation
            .p_b_only
            .values()
            .filter(|cause| **cause == RootDifferenceCause::OutsideS36PointerSubjectPopulation)
            .count();
        wall_sum += result.wall_s;
        peak_rss_kb = peak_rss_kb.max(result.peak_rss_kb);
        if result.artifact.aligned_resolution.indirect_unresolved_sites > 0 {
            unresolved_programs.push(format!(
                "{}:{}",
                result.program, result.artifact.aligned_resolution.indirect_unresolved_sites
            ));
        }
        per_program.push_str(&format!(
            "{PLATFORM}\t{MACHINE_ID}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{:.3}\t{}\t{}\n",
            result.program,
            historical.fn_ptr_roots.len(),
            historical.reachable.len(),
            aligned.fn_ptr_roots.len(),
            aligned.reachable.len(),
            aligned_extra,
            result.artifact.reconciliation.intersection.len(),
            result.artifact.reconciliation.p_b_only.len(),
            result.artifact.reconciliation.s36_only.len(),
            p_b_outside,
            p_b_predicate,
            s36_static,
            s36_const,
            s36_mixed,
            pointer_subject_rows,
            blocked_subjects,
            aligned_coverage.calls_total,
            aligned_coverage.direct_local,
            aligned_coverage.indirect_local,
            aligned_coverage.direct_external,
            aligned_coverage.indirect_unresolved,
            aligned_coverage.non_fn_def_constant,
            result.artifact.aligned_resolution.direct_local_edges,
            result.artifact.aligned_resolution.andersen_local_edges,
            result.artifact.aligned_resolution.indirect_unresolved_sites,
            historical_coverage.calls_total,
            historical_coverage.direct_local,
            historical_coverage.indirect_local,
            historical_coverage.direct_external,
            historical_coverage.indirect_unresolved,
            historical_coverage.non_fn_def_constant,
            result.wall_s,
            result.peak_rss_kb,
            result.manifest_sha256,
        ));
        table.push_str(&format!(
            "| `{}` | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {:.3} | {} |\n",
            result.program,
            historical.fn_ptr_roots.len(),
            historical.reachable.len(),
            aligned.fn_ptr_roots.len(),
            aligned.reachable.len(),
            aligned_extra,
            blocked_subjects,
            result.artifact.aligned_resolution.direct_local_edges,
            result.artifact.aligned_resolution.andersen_local_edges,
            result.artifact.aligned_resolution.indirect_unresolved_sites,
            result.artifact.reconciliation.p_b_only.len(),
            result.artifact.reconciliation.s36_only.len(),
            result.wall_s,
            result.peak_rss_kb,
        ));
        for (side, rows) in [
            ("P-b-only", &result.artifact.reconciliation.p_b_only),
            ("S3.6-only", &result.artifact.reconciliation.s36_only),
        ] {
            let mut by_cause = BTreeMap::<RootDifferenceCause, Vec<&String>>::new();
            for (name, cause) in rows {
                by_cause.entry(*cause).or_default().push(name);
            }
            for (cause, names) in by_cause {
                let witness = names[0];
                let site = result
                    .artifact
                    .reference_sites
                    .get(witness)
                    .and_then(|sites| sites.first());
                cause_table.push_str(&format!(
                    "| `{}` | {} | `{}` | {} | `{}` | `{}` | `{}` | `{}` |\n",
                    result.program,
                    side,
                    cause.key(),
                    names.len(),
                    witness,
                    site.map(|site| site.owner_kind.key()).unwrap_or("n/a"),
                    site.map(|site| site.ref_kind.key()).unwrap_or("n/a"),
                    site.map(|site| site.site.as_str())
                        .unwrap_or("collect_fn_ptrs-root-present; S3.6-facts-identity-absent"),
                ));
            }
        }
        for (target, rendered) in [
            (
                &mut root_rows,
                render_root_rows(&result.program, &result.artifact),
            ),
            (
                &mut public_rows,
                render_public_root_rows(&result.program, &result.artifact),
            ),
            (
                &mut reachable_rows,
                render_reachable_rows(&result.program, &result.artifact),
            ),
            (
                &mut aligned_root_rows,
                render_aligned_root_rows(&result.program, &result.artifact),
            ),
            (
                &mut aligned_reachable_rows,
                render_aligned_reachable_rows(&result.program, &result.artifact),
            ),
            (
                &mut reconciliation_rows,
                render_reconciliation_rows(&result.program, &result.artifact),
            ),
            (
                &mut reference_site_rows,
                render_reference_site_rows(&result.program, &result.artifact),
            ),
        ] {
            target.push_str(
                &rendered
                    .lines()
                    .skip(1)
                    .map(|line| format!("{line}\n"))
                    .collect::<String>(),
            );
        }
    }

    assert_eq!(
        (total_historical_roots, total_historical_web),
        (93, 164),
        "historical analysis-lane P-b baseline drifted"
    );
    assert_eq!(
        (
            total_aligned_roots,
            total_intersection,
            total_p_b_only,
            total_s36_only,
            total_pointer_subject_rows,
            total_blocked_subjects,
        ),
        (295, 87, 6, 208, 992, 640),
        "aligned P-b/S3.6 population drifted"
    );
    assert_eq!(
        outside_population_p_b_only, 6,
        "P-b-only remainder is not fully attributed"
    );
    assert_eq!(
        static_s36_only, 208,
        "S3.6-only remainder is not fully attributed to static initializer scope"
    );
    assert_eq!(
        total_aligned_roots as isize - total_historical_roots as isize,
        total_s36_only as isize - total_p_b_only as isize,
        "93-vs-295 gap does not decompose exactly"
    );
    assert!(
        total_aligned_web >= total_aligned_roots,
        "aligned web is smaller than its roots"
    );
    assert_eq!(
        fs::read_to_string(historical_aggregate.join("roots.tsv")).expect("read historical roots"),
        root_rows,
        "historical root identities drifted"
    );
    assert_eq!(
        fs::read_to_string(historical_aggregate.join("reachable.tsv"))
            .expect("read historical web"),
        reachable_rows,
        "historical web identities drifted"
    );

    let per_program_path = aggregate.join("per-program.tsv");
    let roots_path = aggregate.join("roots.tsv");
    let public_path = aggregate.join("public-roots.tsv");
    let reachable_path = aggregate.join("reachable.tsv");
    let aligned_roots_path = aggregate.join("aligned-roots.tsv");
    let aligned_reachable_path = aggregate.join("aligned-reachable.tsv");
    let reconciliation_path = aggregate.join("reconciliation.tsv");
    let reference_sites_path = aggregate.join("reference-sites.tsv");
    let report_path = aggregate.join("report.md");
    let provenance_path = aggregate.join("provenance.txt");
    let shard_manifests = completed
        .iter()
        .map(|result| format!("{}:{}", result.program, result.manifest_sha256))
        .collect::<Vec<_>>()
        .join(",");
    let unresolved = if unresolved_programs.is_empty() {
        "none".to_owned()
    } else {
        unresolved_programs.join(", ")
    };
    let analysis_head = super::orchestrate::git_sha();
    let report = format!(
        "# P-b / S3.6 aligned function-pointer web census\n\n- Measurement identity: machine `{MACHINE_ID}`, platform `{PLATFORM}`. Timings are machine-local and are not compared across machines.\n- **Historical state retained:** analysis-lane's `collect_fn_ptrs` pricing re-verifies at **{total_historical_roots} SHIM roots / {total_historical_web} web functions / +{}** with exact root and web identity.\n- **Aligned pricing:** one SHIM unit per distinct S3.6 cast-pinned function gives **{total_aligned_roots} SHIM functions**. Their local direct + Andersen-resolved forward web is **{total_aligned_web} functions / +{}**.\n- **Benefit view:** the aligned functions carry **{total_blocked_subjects}** `call-site-not-adapted` subjects (from {total_pointer_subject_rows} pointer-subject rows in pinned functions). Cost scales with {total_aligned_roots} functions; benefit scales with {total_blocked_subjects} subjects. The complete blocked-subject join is **3,326 = 2,686 adaptable + 640 pinned**; blocked unreferenced subjects are rejected.\n- Exact reconciliation: intersection **{total_intersection}**, P-b-only **{total_p_b_only}**, S3.6-only **{total_s36_only}**; `93 = 87 + 6`, `295 = 87 + 208`, and `295 - 93 = 208 - 6`.\n- Pre-registered hypothesis outcome: **partly confirmed, partly falsified**. All {total_s36_only} S3.6-only functions are certified static-initializer casts in `tulipindicators`, but the predicted empty P-b-only set is false: all {total_p_b_only} are outside S3.6's pointer-subject export population.\n- Substrate cause: **zero**. The canonical digest is `{DERIVED_CORPUS_SHA256}`; the same source tree reproduces S3.6's alternate `*.rs` digest `{S36_RS_CORPUS_SHA256}`.\n- Resolution scope does not cause the root gap; it prices the web. Direct and Andersen counts below are unique route-tagged `(caller, callee)` pairs whose caller is in the aligned closure; the same pair reached by both routes counts once in each route category. Unresolved counts are aligned-reachable indirect call sites with zero local Andersen target. Programs with unresolved sites: **{unresolved}**.\n- Execution: 20/20 sequential, RAM/CPU uncapped, 14,400-second per-program liveness bound, atomic phase checkpoints; Linux-local wall sum **{wall_sum:.3}s**, maximum observed per-program RSS **{peak_rss_kb} KiB**.\n\n## Per-program aligned prices and resolution coverage\n\n| program | old roots | old web | aligned SHIM fns | aligned web | extra web | blocked subjects | direct local edges | Andersen local edges | unresolved sites | P-b-only | S3.6-only | wall s | peak RSS KiB |\n|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|\n{table}\n## Named cause witnesses\n\n| program | side | cause | count | witness function | owner kind | reference kind | site / population witness |\n|---|---|---|---:|---|---|---|---|\n{cause_table}",
        total_historical_web - total_historical_roots,
        total_aligned_web - total_aligned_roots,
    );
    let provenance = format!(
        "machine_id={MACHINE_ID}\nplatform={PLATFORM}\nanalysis_head={analysis_head}\nbaseline_branch=analysis-lane\nprograms=20\nexecution=sequential\nhistorical_root_definition=collect_fn_ptrs-over-adjusted-function-bodies\naligned_root_definition=s36-pinned-distinct-functions-referenced-via-fn-pointer-cast\nweb_definition=forward-local-direct-plus-andersen-resolved-indirect\nresolution_edge_definition=unique-route-tagged-caller-callee-pairs-with-caller-in-aligned-closure\nunresolved_definition=aligned-reachable-indirect-call-sites-with-zero-local-andersen-target\npublic_only_roots=excluded\nraw_corpus_sha256={RAW_CORPUS_SHA256}\nderived_corpus_sha256={DERIVED_CORPUS_SHA256}\ns36_rs_corpus_sha256={S36_RS_CORPUS_SHA256}\ndigest_bridge=same-tree-canonical-and-s36-rs-line-method\nsnapshot_producer={SNAPSHOT_PRODUCER}\nsnapshot_manifest_commit={SNAPSHOT_MANIFEST_COMMIT}\nsnapshot_manifest_document_sha256={SNAPSHOT_MANIFEST_DOCUMENT_SHA256}\nsnapshot_sha256s_sha256={SNAPSHOT_SHA256SUMS_SHA256}\nsnapshot_inventory_sha256={snapshot_inventory_sha256}\nhistorical_aggregate_manifest_sha256={HISTORICAL_AGGREGATE_MANIFEST_SHA256}\nmemory_limit=uncapped\ncpu_limit=uncapped\nwall_bound_kind=liveness\nwall_cap_s={WALL_LIVENESS_SECS}\ncheckpoints=atomic-phase-per-program\ndata_false_aggregation=excluded\nwall_sum_s={wall_sum:.3}\npeak_program_rss_kb={peak_rss_kb}\nhistorical_shim_units={total_historical_roots}\nhistorical_web_units={total_historical_web}\nhistorical_web_minus_roots={}\naligned_shim_units={total_aligned_roots}\naligned_web_units={total_aligned_web}\naligned_web_minus_roots={}\nall_blocked_subjects=3326\nadaptable_blocked_subjects=2686\npinned_pointer_subject_rows={total_pointer_subject_rows}\npinned_blocked_subjects={total_blocked_subjects}\nblocked_unreferenced_subjects=0\nroot_intersection={total_intersection}\np_b_only={total_p_b_only}\ns36_only={total_s36_only}\np_b_only_expected_empty=false\np_b_only_preregistered_expectation=empty\np_b_only_cause=outside-s36-pointer-subject-population\ns36_only_cause=static-initializer-outside-collect-fn-ptrs\nunresolved_programs={unresolved}\nshard_manifest_sha256s={shard_manifests}\ntiming_comparison=forbidden-across-machines\n",
        total_historical_web - total_historical_roots,
        total_aligned_web - total_aligned_roots,
    );
    if aggregate_complete {
        for (path, expected) in [
            (&per_program_path, per_program.as_str()),
            (&roots_path, root_rows.as_str()),
            (&public_path, public_rows.as_str()),
            (&reachable_path, reachable_rows.as_str()),
            (&aligned_roots_path, aligned_root_rows.as_str()),
            (&aligned_reachable_path, aligned_reachable_rows.as_str()),
            (&reconciliation_path, reconciliation_rows.as_str()),
            (&reference_sites_path, reference_site_rows.as_str()),
            (&report_path, report.as_str()),
            (&provenance_path, provenance.as_str()),
        ] {
            let actual = fs::read_to_string(path).unwrap_or_else(|error| {
                panic!("read completed aggregate {}: {error}", path.display())
            });
            assert_eq!(
                actual,
                expected,
                "P-b STOP: completed aggregate projection drifted at {}",
                path.display()
            );
        }
        println!(
            "PBCENSUS machine_id={MACHINE_ID} platform={PLATFORM} status=verified-skip programs=20 historical_shim_units={total_historical_roots} historical_web_units={total_historical_web} aligned_shim_units={total_aligned_roots} aligned_web_units={total_aligned_web}"
        );
        return;
    }
    for (path, contents) in [
        (&per_program_path, per_program),
        (&roots_path, root_rows),
        (&public_path, public_rows),
        (&reachable_path, reachable_rows),
        (&aligned_roots_path, aligned_root_rows),
        (&aligned_reachable_path, aligned_reachable_rows),
        (&reconciliation_path, reconciliation_rows),
        (&reference_sites_path, reference_site_rows),
        (&report_path, report),
        (&provenance_path, provenance),
    ] {
        fs::write(path, contents)
            .unwrap_or_else(|error| panic!("write aggregate {}: {error}", path.display()));
    }
    write_sha256_manifest(
        &aggregate,
        &[
            per_program_path,
            roots_path,
            public_path,
            reachable_path,
            aligned_roots_path,
            aligned_reachable_path,
            reconciliation_path,
            reference_sites_path,
            report_path,
            provenance_path,
        ],
        &aggregate_manifest,
    )
    .unwrap_or_else(|error| panic!("write P-b aggregate manifest: {error}"));
    verify_sha256_manifest(&aggregate, &aggregate_manifest)
        .unwrap_or_else(|error| panic!("verify P-b aggregate: {error}"));
    println!(
        "PBCENSUS machine_id={MACHINE_ID} platform={PLATFORM} programs=20 historical_shim_units={total_historical_roots} historical_web_units={total_historical_web} aligned_shim_units={total_aligned_roots} aligned_web_units={total_aligned_web} aligned_web_minus_roots={} blocked_subjects={total_blocked_subjects} wall_sum_s={wall_sum:.3} peak_program_rss_kb={peak_rss_kb}",
        total_aligned_web - total_aligned_roots,
    );
}

#[cfg(test)]
mod tests {
    use std::{
        collections::{BTreeMap, BTreeSet},
        fs,
    };

    use super::{
        add_local_call_edges, classify_call_route, collect_reference_sites, derived_corpus_digest,
        measure_graph, measure_web, parse_reconciled_worker_artifact, parse_s36_program,
        parse_worker_artifact, raw_corpus_digest, reconcile_roots,
        render_reconciled_worker_artifact, render_worker_artifact, resolution_counts_for_web,
        validate_completed_state, wall_liveness, write_phase_checkpoint, BodyOwnerKind, CallRoute,
        CoverageCounts, GraphNode, ReferenceKind, ReferenceSite, RootDifferenceCause,
        S36FunctionEvidence, WorkerArtifact, DERIVED_CORPUS_SHA256, RAW_CORPUS_SHA256,
    };

    fn node(fn_ptr_root: bool, public_root: bool, callees: &[&str]) -> GraphNode {
        GraphNode {
            fn_ptr_root,
            public_root,
            callees: callees.iter().map(|name| (*name).to_owned()).collect(),
        }
    }

    #[test]
    fn p_b_separates_public_only_from_fn_ptr_only_roots() {
        let graph = BTreeMap::from([
            ("fn_ptr".to_owned(), node(true, false, &["fn_leaf"])),
            ("fn_leaf".to_owned(), node(false, false, &[])),
            ("public".to_owned(), node(false, true, &["public_leaf"])),
            ("public_leaf".to_owned(), node(false, false, &[])),
        ]);

        let measured = measure_graph(&graph).expect("valid fixture");
        assert_eq!(
            measured.fn_ptr_roots,
            ["fn_ptr"].into_iter().map(str::to_owned).collect()
        );
        assert_eq!(
            measured.public_roots,
            ["public"].into_iter().map(str::to_owned).collect()
        );
        assert!(measured.root_public_overlap.is_empty());
        assert_eq!(
            measured.reachable,
            ["fn_leaf", "fn_ptr"]
                .into_iter()
                .map(str::to_owned)
                .collect()
        );

        let text = render_worker_artifact(
            "lambda7",
            "linux-x86_64",
            "separated",
            &measured,
            4,
            Default::default(),
        )
        .expect("render fixture");
        let parsed = parse_worker_artifact("lambda7", "linux-x86_64", "separated", &text)
            .expect("parse fixture");
        assert_eq!(parsed.graph, measured);
        assert!(text.contains("PBCOUNT\tv1\tlambda7\tlinux-x86_64\tseparated\t1\t1\t0\t2\t4\t"));
        assert!(text.contains("PBROOT\tv1\tlambda7\tlinux-x86_64\tseparated\tfn_ptr\t0"));
        assert!(!text.contains("PBROOT\tv1\tlambda7\tlinux-x86_64\tseparated\tpublic\t"));
    }

    #[test]
    fn p_b_reports_when_public_and_fn_ptr_root_inventories_coincide() {
        let graph = BTreeMap::from([
            ("shared".to_owned(), node(true, true, &["leaf"])),
            ("leaf".to_owned(), node(false, false, &[])),
        ]);

        let measured = measure_graph(&graph).expect("valid fixture");
        assert_eq!(measured.fn_ptr_roots, measured.public_roots);
        assert_eq!(measured.root_public_overlap, measured.fn_ptr_roots);

        let text = render_worker_artifact(
            "lambda7",
            "linux-x86_64",
            "coincident",
            &measured,
            2,
            Default::default(),
        )
        .expect("render fixture");
        let parsed = parse_worker_artifact("lambda7", "linux-x86_64", "coincident", &text)
            .expect("parse fixture");
        assert_eq!(parsed.graph, measured);
        assert!(text.contains("PBCOUNT\tv1\tlambda7\tlinux-x86_64\tcoincident\t1\t1\t1\t2\t2\t"));
        assert!(text.contains("PBROOT\tv1\tlambda7\tlinux-x86_64\tcoincident\tshared\t1"));
    }

    #[test]
    fn p_b_schema_rejects_incomplete_root_inventory() {
        let graph = BTreeMap::from([
            ("root".to_owned(), node(true, false, &[])),
            ("other".to_owned(), node(false, false, &[])),
        ]);
        let measured = measure_graph(&graph).expect("valid fixture");
        let text = render_worker_artifact(
            "lambda7",
            "linux-x86_64",
            "fixture",
            &measured,
            2,
            Default::default(),
        )
        .expect("render fixture");
        let incomplete = text
            .lines()
            .filter(|line| !line.starts_with("PBROOT"))
            .collect::<Vec<_>>()
            .join("\n");

        assert!(
            parse_worker_artifact("lambda7", "linux-x86_64", "fixture", &incomplete)
                .expect_err("missing root row must fail")
                .contains("root inventory")
        );
        assert_eq!(
            parse_worker_artifact("lambda7", "linux-x86_64", "fixture", &text)
                .expect("complete fixture")
                .graph,
            measured
        );
    }

    #[test]
    fn p_b_schema_accepts_exact_libtest_prefix_on_first_count_row() {
        let graph = BTreeMap::from([("root".to_owned(), node(true, false, &[]))]);
        let measured = measure_graph(&graph).expect("valid fixture");
        let text = render_worker_artifact(
            "lambda7",
            "linux-x86_64",
            "fixture",
            &measured,
            1,
            Default::default(),
        )
        .expect("render fixture");
        let wrapped = text.replacen("PBCOUNT\t", "test bo_c1::boc1_run_one ... PBCOUNT\t", 1);

        assert_eq!(
            parse_worker_artifact("lambda7", "linux-x86_64", "fixture", &wrapped)
                .expect("the exact libtest framing prefix must be accepted")
                .graph,
            measured
        );
        let near_match = text.replacen("PBCOUNT\t", "test other::worker ... PBCOUNT\t", 1);
        assert!(
            parse_worker_artifact("lambda7", "linux-x86_64", "fixture", &near_match)
                .expect_err("other stdout prefixes must remain rejected")
                .contains("missing PBCOUNT")
        );
    }

    #[test]
    fn p_b_schema_rejects_call_coverage_mismatch() {
        let graph = BTreeMap::from([("root".to_owned(), node(true, false, &[]))]);
        let measured = measure_graph(&graph).expect("valid fixture");
        let coverage = CoverageCounts {
            calls_total: 1,
            ..Default::default()
        };
        assert!(render_worker_artifact(
            "lambda7",
            "linux-x86_64",
            "fixture",
            &measured,
            1,
            coverage,
        )
        .expect_err("coverage mismatch must fail")
        .contains("call coverage mismatch"));
    }

    #[test]
    fn p_b_wall_liveness_is_pinned() {
        assert_eq!(wall_liveness(None).expect("default").as_secs(), 14_400);
        assert_eq!(
            wall_liveness(Some("14400"))
                .expect("registered override")
                .as_secs(),
            14_400
        );
        assert!(wall_liveness(Some("3600")).is_err());
    }

    #[test]
    fn p_b_direct_and_andersen_indirect_edges_share_one_closure() {
        assert_eq!(classify_call_route(true, true), CallRoute::Direct);
        assert_eq!(
            classify_call_route(false, false),
            CallRoute::AndersenIndirect
        );
        assert_eq!(
            classify_call_route(true, false),
            CallRoute::UnsupportedConstant
        );

        let mut graph = BTreeMap::from([
            ("root".to_owned(), node(true, false, &[])),
            ("direct".to_owned(), node(false, false, &[])),
            ("indirect".to_owned(), node(false, false, &[])),
        ]);
        add_local_call_edges(&mut graph, "root", CallRoute::Direct, ["direct".to_owned()])
            .expect("direct edge");
        add_local_call_edges(
            &mut graph,
            "direct",
            CallRoute::AndersenIndirect,
            ["indirect".to_owned()],
        )
        .expect("indirect edge");
        assert_eq!(
            measure_graph(&graph).expect("combined closure").reachable,
            ["direct", "indirect", "root"]
                .into_iter()
                .map(str::to_owned)
                .collect()
        );
        assert!(add_local_call_edges(
            &mut graph,
            "root",
            CallRoute::UnsupportedConstant,
            ["direct".to_owned()],
        )
        .expect_err("unsupported constant must STOP")
        .contains("Andersen has no indirect-call site"));
    }

    #[test]
    fn p_b_resolution_counts_are_route_tagged_and_closure_scoped() {
        let reachable = BTreeSet::from(["root".to_owned(), "a".to_owned(), "b".to_owned()]);
        let direct = BTreeSet::from([
            ("root".to_owned(), "a".to_owned()),
            ("outside".to_owned(), "a".to_owned()),
        ]);
        let andersen = BTreeSet::from([
            ("a".to_owned(), "b".to_owned()),
            ("a".to_owned(), "root".to_owned()),
            ("outside".to_owned(), "b".to_owned()),
        ]);
        let unresolved = BTreeSet::from([("a".to_owned(), 1), ("outside".to_owned(), 2)]);

        let counts = resolution_counts_for_web(&reachable, &direct, &andersen, &unresolved);
        assert_eq!(counts.direct_local_edges, 1);
        assert_eq!(counts.andersen_local_edges, 2);
        assert_eq!(counts.indirect_unresolved_sites, 1);
    }

    #[test]
    fn p_b_historical_and_aligned_roots_price_distinct_webs() {
        let graph = BTreeMap::from([
            ("historical".to_owned(), node(false, false, &["shared"])),
            (
                "aligned".to_owned(),
                node(false, false, &["shared", "extra"]),
            ),
            ("shared".to_owned(), node(false, false, &[])),
            ("extra".to_owned(), node(false, false, &[])),
        ]);
        let historical = BTreeSet::from(["historical".to_owned()]);
        let aligned = BTreeSet::from(["aligned".to_owned()]);

        assert_eq!(
            measure_web(&graph, &historical).expect("historical web"),
            BTreeSet::from(["historical".to_owned(), "shared".to_owned()])
        );
        assert_eq!(
            measure_web(&graph, &aligned).expect("aligned web"),
            BTreeSet::from([
                "aligned".to_owned(),
                "extra".to_owned(),
                "shared".to_owned(),
            ])
        );
    }

    #[test]
    fn p_b_reconciliation_names_owner_scope_and_population_causes() {
        let p_b = BTreeSet::from(["shared".to_owned(), "no_subject".to_owned()]);
        let s36 = BTreeMap::from([
            (
                "shared".to_owned(),
                S36FunctionEvidence::pinned(1, 1, [ReferenceKind::FnPtrCast]),
            ),
            (
                "static_only".to_owned(),
                S36FunctionEvidence::pinned(3, 2, [ReferenceKind::FnPtrCast]),
            ),
        ]);
        let sites = BTreeMap::from([(
            "static_only".to_owned(),
            vec![ReferenceSite::fixture(
                BodyOwnerKind::StaticInitializer,
                ReferenceKind::FnPtrCast,
            )],
        )]);

        let got = reconcile_roots(&p_b, &s36, &sites).expect("fully explained fixture");
        assert_eq!(got.intersection, BTreeSet::from(["shared".to_owned()]));
        assert_eq!(
            got.p_b_only.get("no_subject"),
            Some(&RootDifferenceCause::OutsideS36PointerSubjectPopulation)
        );
        assert_eq!(
            got.s36_only.get("static_only"),
            Some(&RootDifferenceCause::StaticInitializerOutsideCollectFnPtrs)
        );
    }

    #[test]
    fn p_b_reconciliation_stops_on_unexplained_body_cast() {
        let s36 = BTreeMap::from([(
            "missed".to_owned(),
            S36FunctionEvidence::pinned(1, 1, [ReferenceKind::FnPtrCast]),
        )]);
        let sites = BTreeMap::from([(
            "missed".to_owned(),
            vec![ReferenceSite::fixture(
                BodyOwnerKind::FunctionBody,
                ReferenceKind::FnPtrCast,
            )],
        )]);

        assert!(reconcile_roots(&BTreeSet::new(), &s36, &sites)
            .expect_err("a function-body cast missed by collect_fn_ptrs is unexplained")
            .contains("unexplained"));
    }

    #[test]
    fn p_b_s36_join_requires_complete_subject_data() {
        let facts = "fn_path\tmir_local\tis_param\tannotated\tslot\tkind\traw_op\tptr_cmp\treferenced\tref_kinds\tref_class\tctor\tlen_class\tsize_expr\n\
                     crate::target\t1\t1\t1\t1\tref\t-\t0\t1\tfnptr-cast\tpinned\tparam\tparam-no-site\t\n";
        let complete = "{\"fn_path\":\"crate::target\",\"mir_local\":1,\"outcome\":\"degraded\",\"degrade_reason\":\"call-site-not-adapted\"}\n";
        let parsed = parse_s36_program(facts, complete).expect("complete S3.6 fixture");
        assert_eq!(parsed["crate::target"].pointer_subjects, 1);
        assert_eq!(parsed["crate::target"].blocked_subjects, 1);

        let incomplete = "{\"fn_path\":\"crate::missing\",\"mir_local\":9,\"outcome\":\"degraded\",\"degrade_reason\":\"call-site-not-adapted\"}\n";
        assert!(parse_s36_program(facts, incomplete)
            .expect_err("blocked subject without a facts identity must fail")
            .contains("missing facts identity"));
    }

    #[test]
    fn p_b_s36_join_rejects_blocked_unreferenced_subject() {
        let facts = "fn_path\tmir_local\tis_param\tannotated\tslot\tkind\traw_op\tptr_cmp\treferenced\tref_kinds\tref_class\tctor\tlen_class\tsize_expr\n\
                     crate::target\t1\t1\t1\t1\tref\t-\t0\t0\t-\t-\tparam\tparam-no-site\t\n";
        let outcomes = "{\"fn_path\":\"crate::target\",\"mir_local\":1,\"outcome\":\"degraded\",\"degrade_reason\":\"call-site-not-adapted\"}\n";

        assert!(parse_s36_program(facts, outcomes)
            .expect_err("blocked unreferenced subjects must fail")
            .contains("unreferenced"));
    }

    #[test]
    fn p_b_reconciled_schema_gate_is_two_sided() {
        let historical_graph = BTreeMap::from([
            ("shared".to_owned(), node(true, false, &[])),
            ("no_subject".to_owned(), node(true, false, &[])),
            ("static_only".to_owned(), node(false, false, &[])),
        ]);
        let aligned_graph = BTreeMap::from([
            ("shared".to_owned(), node(true, false, &[])),
            ("no_subject".to_owned(), node(false, false, &[])),
            ("static_only".to_owned(), node(true, false, &[])),
        ]);
        let s36 = BTreeMap::from([
            (
                "shared".to_owned(),
                S36FunctionEvidence::pinned(1, 1, [ReferenceKind::FnPtrCast]),
            ),
            (
                "static_only".to_owned(),
                S36FunctionEvidence::pinned(3, 2, [ReferenceKind::FnPtrCast]),
            ),
        ]);
        let sites = BTreeMap::from([
            (
                "no_subject".to_owned(),
                vec![ReferenceSite::fixture(
                    BodyOwnerKind::FunctionBody,
                    ReferenceKind::AddrTaken,
                )],
            ),
            (
                "static_only".to_owned(),
                vec![ReferenceSite::fixture(
                    BodyOwnerKind::StaticInitializer,
                    ReferenceKind::FnPtrCast,
                )],
            ),
        ]);
        let historical = measure_graph(&historical_graph).expect("historical fixture");
        let aligned = measure_graph(&aligned_graph).expect("aligned fixture");
        let reconciliation =
            reconcile_roots(&historical.fn_ptr_roots, &s36, &sites).expect("reconciled fixture");
        let artifact = WorkerArtifact {
            graph: historical,
            aligned_graph: aligned,
            local_functions: 3,
            coverage: Default::default(),
            aligned_coverage: Default::default(),
            aligned_resolution: Default::default(),
            s36_functions: s36,
            reconciliation,
            reference_sites: sites,
        };
        let text =
            render_reconciled_worker_artifact("lambda7", "linux-x86_64", "fixture", &artifact)
                .expect("render reconciliation fixture");
        let parsed = parse_reconciled_worker_artifact("lambda7", "linux-x86_64", "fixture", &text)
            .expect("parse complete reconciliation fixture");
        assert_eq!(parsed, artifact);

        let incomplete = text
            .lines()
            .filter(|line| {
                !line.contains("PBALIGNROOT\tv1\tlambda7\tlinux-x86_64\tfixture\tstatic_only")
            })
            .collect::<Vec<_>>()
            .join("\n");
        assert!(parse_reconciled_worker_artifact(
            "lambda7",
            "linux-x86_64",
            "fixture",
            &incomplete,
        )
        .expect_err("incomplete aligned inventory must fail")
        .contains("aligned inventory"));
    }

    #[test]
    fn p_b_completed_data_gate_is_two_sided() {
        assert!(validate_completed_state("ok", true, "complete").is_ok());
        assert!(validate_completed_state("ok", false, "complete").is_err());
        assert!(validate_completed_state("timeout", false, "andersen").is_err());
    }

    #[test]
    fn p_b_phase_checkpoint_write_fires_atomically() {
        let root = std::env::temp_dir().join(format!("crat-p-b-checkpoint-{}", std::process::id()));
        fs::create_dir_all(&root).expect("create checkpoint fixture");
        let checkpoint = root.join("checkpoint.txt");
        write_phase_checkpoint(&checkpoint, "fixture", "andersen", 123).expect("write checkpoint");
        let text = fs::read_to_string(&checkpoint).expect("read checkpoint");
        assert!(text.contains("program=fixture"));
        assert!(text.contains("phase=andersen"));
        assert!(text.contains("timestamp_unix_ms=123"));
        assert!(!checkpoint.with_extension("txt.tmp").exists());
        fs::remove_dir_all(root).expect("remove checkpoint fixture");
    }

    #[test]
    fn p_b_owner_scope_fixture_separates_body_and_static_casts() {
        let src = "#![allow(dead_code, unused_unsafe)]\n\
                   pub unsafe fn body_target(p: *mut i32) -> i32 { *p }\n\
                   pub unsafe fn static_target(p: *mut i32) -> i32 { *p }\n\
                   pub static TABLE: [unsafe fn(*mut i32) -> i32; 1] = \
                       [static_target as unsafe fn(*mut i32) -> i32];\n\
                   pub unsafe fn body_use() -> usize { \
                       body_target as unsafe fn(*mut i32) -> i32 as usize \
                   }\n";
        let (p_b, sites) = ::utils::compilation::run_compiler_on_str(src, |tcx| {
            let program = super::super::collect_program(tcx);
            let p_b = crate::rewriter::collector::collect_fn_ptrs(&program)
                .into_iter()
                .map(|did| tcx.def_path_str(did.to_def_id()))
                .collect::<BTreeSet<_>>();
            let sites =
                collect_reference_sites(tcx, &program.functions).expect("collect reference sites");
            (p_b, sites)
        })
        .expect("owner-scope fixture compiles");

        assert!(p_b.iter().any(|name| name.ends_with("body_target")));
        assert!(!p_b.iter().any(|name| name.ends_with("static_target")));
        let static_sites = sites
            .iter()
            .find(|(name, _)| name.ends_with("static_target"))
            .map(|(_, sites)| sites)
            .expect("static target evidence");
        assert!(static_sites.iter().any(|site| {
            site.owner_kind == BodyOwnerKind::StaticInitializer
                && site.ref_kind == ReferenceKind::FnPtrCast
        }));
    }

    #[test]
    #[ignore = "reads both frozen corpus trees; run explicitly before the P-b sweep"]
    fn p_b_registered_corpus_digests_match() {
        let root = super::super::orchestrate::workspace_root()
            .canonicalize()
            .expect("workspace root");
        assert_eq!(
            raw_corpus_digest(&root, "benchmarks/rs-crown").expect("raw digest"),
            RAW_CORPUS_SHA256
        );
        assert_eq!(
            derived_corpus_digest(&root.join("benchmarks/rs-crown-derived"))
                .expect("derived digest"),
            DERIVED_CORPUS_SHA256
        );
    }
}
