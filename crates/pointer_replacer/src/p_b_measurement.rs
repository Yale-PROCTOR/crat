//! Test-only P-b census of function-pointer-rooted local call webs.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    io::Write,
    path::{Path, PathBuf},
    process::{Command, Stdio},
    time::{Duration, Instant},
};

use points_to::andersen;
use rustc_hash::FxHashSet;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    mir::{BasicBlock, TerminatorKind},
    ty::TyCtxt,
};
use rustc_type_ir::TyKind;

const MACHINE_ID: &str = "lambda7";
const PLATFORM: &str = "linux-x86_64";
const WALL_LIVENESS_SECS: u64 = 3_600;
const RAW_CORPUS_SHA256: &str = "9fc912af10fd3b235fe4d444d2fbac0bc521509b1c9447fc551acd0130e0e621";
const DERIVED_CORPUS_SHA256: &str =
    "db96829b5c2b0db28fb4bb9ddd3d32901b5d4e6e4134da07ada0d513d94eb4c6";
const SNAPSHOT_PRODUCER: &str = "3b26a0ff85517a33acf916e8dbe2624ffc924a85";
const SNAPSHOT_MANIFEST_COMMIT: &str = "a654d5ecde8a0ea9fccc8a3e7b9caaa8fac5812d";
const SNAPSHOT_MANIFEST_DOCUMENT_SHA256: &str =
    "832b8839d0ffed70b2203b3bf1859ffcb0142bcec170f5faa10990214b3d04b5";

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

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct GraphNode {
    fn_ptr_root: bool,
    public_root: bool,
    callees: BTreeSet<String>,
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
    local_functions: usize,
    coverage: CoverageCounts,
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
    let mut reachable = BTreeSet::new();
    let mut pending = fn_ptr_roots.iter().cloned().collect::<Vec<_>>();
    while let Some(function) = pending.pop() {
        if !reachable.insert(function.clone()) {
            continue;
        }
        let node = graph
            .get(&function)
            .ok_or_else(|| format!("call graph references unknown local function `{function}`"))?;
        pending.extend(node.callees.iter().cloned());
    }
    Ok(GraphMeasurement {
        fn_ptr_roots,
        public_roots,
        root_public_overlap,
        reachable,
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

fn parse_usize(field: &str, value: &str) -> Result<usize, String> {
    value
        .parse::<usize>()
        .map_err(|error| format!("invalid {field} {value:?}: {error}"))
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
    for (offset, line) in text.lines().enumerate() {
        if !line.starts_with("PB") {
            continue;
        }
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
        local_functions,
        coverage,
    })
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

fn measure_tcx(tcx: TyCtxt<'_>) -> Result<(WorkerArtifact, Duration), String> {
    let program = super::collect_program(tcx);
    let functions = program.functions.iter().copied().collect::<FxHashSet<_>>();
    let fn_ptrs = crate::rewriter::collector::collect_fn_ptrs(&program);
    let fn_ptr_roots = program
        .functions
        .iter()
        .copied()
        .filter(|function| fn_ptrs.contains(function))
        .collect::<FxHashSet<_>>();
    let public_roots = program
        .functions
        .iter()
        .copied()
        .filter(|function| tcx.visibility(function.to_def_id()).is_public())
        .collect::<FxHashSet<_>>();

    let program_name = std::env::var("CRAT_BOC1_NAME").unwrap_or_else(|_| "unnamed".to_owned());
    eprintln!("BOC1PHASE p-b phase=andersen program={program_name}");
    let t_andersen = Instant::now();
    let arena = typed_arena::Arena::new();
    let type_shapes = utils::ty_shape::get_ty_shapes(&arena, tcx, false);
    let config = andersen::Config {
        use_optimized_mir: false,
        c_exposed_fns: fn_ptr_roots
            .iter()
            .map(|did| tcx.item_name(did.to_def_id()).to_string())
            .collect(),
    };
    let pre = andersen::pre_analyze(&config, &type_shapes, tcx);
    let solutions = andersen::analyze(&config, &pre, &type_shapes, tcx);
    let andersen_time = t_andersen.elapsed();

    eprintln!("BOC1PHASE p-b phase=call-graph program={program_name}");
    let mut coverage = CoverageCounts::default();
    let mut graph = BTreeMap::new();
    for &function in &program.functions {
        graph.insert(
            tcx.def_path_str(function.to_def_id()),
            GraphNode {
                fn_ptr_root: fn_ptr_roots.contains(&function),
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
                    vec![target]
                }
                CallRoute::AndersenIndirect => {
                    let targets = indirect_targets(&pre, &solutions, caller, block)?
                        .into_iter()
                        .filter(|target| functions.contains(target))
                        .collect::<Vec<_>>();
                    if targets.is_empty() {
                        coverage.indirect_unresolved += 1;
                        continue;
                    }
                    coverage.indirect_local += 1;
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
    Ok((
        WorkerArtifact {
            graph: measured,
            local_functions: graph.len(),
            coverage,
        },
        andersen_time,
    ))
}

pub(super) fn run_worker(tcx: TyCtxt<'_>, t_tcx: Duration) -> super::report::Row {
    let t0 = Instant::now();
    let program = std::env::var("CRAT_BOC1_NAME").unwrap_or_else(|_| "unnamed".to_owned());
    let machine_id = std::env::var("CRAT_MEASUREMENT_MACHINE_ID")
        .unwrap_or_else(|_| "missing-machine".to_owned());
    let platform = std::env::var("CRAT_MEASUREMENT_PLATFORM")
        .unwrap_or_else(|_| "missing-platform".to_owned());
    eprintln!("BOC1PHASE p-b phase=collect-roots program={program}");
    let mut row = super::report::Row::default();
    row.set("machine_id", &machine_id);
    row.set("platform", &platform);
    match measure_tcx(tcx).and_then(|(artifact, andersen_time)| {
        let rendered = render_worker_artifact(
            &machine_id,
            &platform,
            &program,
            &artifact.graph,
            artifact.local_functions,
            artifact.coverage.clone(),
        )?;
        print!("{rendered}");
        row.set("status", "ok");
        row.set("roots", artifact.graph.fn_ptr_roots.len());
        row.set("public_roots", artifact.graph.public_roots.len());
        row.set(
            "root_public_overlap",
            artifact.graph.root_public_overlap.len(),
        );
        row.set("web", artifact.graph.reachable.len());
        row.set("local_functions", artifact.local_functions);
        row.set("calls_total", artifact.coverage.calls_total);
        row.set("direct_local", artifact.coverage.direct_local);
        row.set("indirect_local", artifact.coverage.indirect_local);
        row.set("direct_external", artifact.coverage.direct_external);
        row.set("indirect_unresolved", artifact.coverage.indirect_unresolved);
        row.set("non_fn_def_constant", artifact.coverage.non_fn_def_constant);
        row.set(
            "t_andersen_s",
            format!("{:.3}", andersen_time.as_secs_f64()),
        );
        Ok::<(), String>(())
    }) {
        Ok(()) => eprintln!("BOC1PHASE p-b phase=complete program={program}"),
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

fn verify_snapshot(snapshot: &Path, document: &Path) -> Result<String, String> {
    if sha256_file(document)? != SNAPSHOT_MANIFEST_DOCUMENT_SHA256 {
        return Err("snapshot manifest document SHA-256 drifted".to_owned());
    }
    let input = fs::read_to_string(document)
        .map_err(|error| format!("read snapshot manifest {}: {error}", document.display()))?;
    let mut in_block = false;
    let mut entries = BTreeMap::new();
    for line in input.lines() {
        if line == "```text" {
            if in_block || !entries.is_empty() {
                return Err("snapshot document contains multiple text manifests".to_owned());
            }
            in_block = true;
            continue;
        }
        if in_block && line == "```" {
            in_block = false;
            continue;
        }
        if !in_block {
            continue;
        }
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
    if in_block || entries.len() != 100 {
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
    if actual != entries.keys().cloned().collect() {
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
    sha256_text(&canonical)
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

fn root_relation(graph: &GraphMeasurement) -> &'static str {
    if graph.fn_ptr_roots == graph.public_roots {
        "coincident"
    } else if graph.root_public_overlap.is_empty() {
        "separated"
    } else {
        "overlap"
    }
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
    if receipt.get("status").map(String::as_str) != Some("ok")
        || receipt.get("data").map(String::as_str) != Some("true")
    {
        return Err(format!(
            "published data=false shard: status={} phase={}",
            receipt
                .get("status")
                .map(String::as_str)
                .unwrap_or("missing"),
            receipt
                .get("phase")
                .map(String::as_str)
                .unwrap_or("missing")
        ));
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
        ("wall_cap_s", "3600"),
    ] {
        if receipt.get(key).map(String::as_str) != Some(expected) {
            return Err(format!("completed shard {program} receipt {key} drifted"));
        }
    }
    let stdout = fs::read_to_string(shard.join("stdout.txt"))
        .map_err(|error| format!("read {program} stdout: {error}"))?;
    let artifact = parse_worker_artifact(MACHINE_ID, PLATFORM, program, &stdout)?;
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

    let snapshot =
        PathBuf::from(std::env::var_os("CRAT_PB_SNAPSHOT").expect("P-b requires CRAT_PB_SNAPSHOT"));
    assert_eq!(
        snapshot.file_name().and_then(|name| name.to_str()),
        Some("3b26a0ff"),
        "P-b requires snapshot 3b26a0ff"
    );
    let snapshot_document = PathBuf::from(
        std::env::var_os("CRAT_PB_SNAPSHOT_MANIFEST")
            .expect("P-b requires CRAT_PB_SNAPSHOT_MANIFEST"),
    );
    let snapshot_inventory_sha256 = verify_snapshot(&snapshot, &snapshot_document)
        .unwrap_or_else(|error| panic!("P-b snapshot STOP: {error}"));

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
        let outcome =
            super::orchestrate::run_child_labeled(program, &input, "p-b", "p-b", timeout, &[]);
        let stdout = shard.join("stdout.txt");
        let stderr = shard.join("stderr.txt");
        fs::write(&stdout, &outcome.stdout).expect("write worker stdout");
        fs::write(&stderr, &outcome.stderr).expect("write worker stderr");
        let phase = phase_from_stderr(&outcome.stderr);
        let parsed = parse_worker_artifact(MACHINE_ID, PLATFORM, program, &outcome.stdout);
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
        if let Ok(parsed) = &parsed {
            let roots = shard.join("roots.tsv");
            let public_roots = shard.join("public-roots.tsv");
            let reachable = shard.join("reachable.tsv");
            fs::write(&roots, render_root_rows(program, parsed)).expect("write root inventory");
            fs::write(&public_roots, render_public_root_rows(program, parsed))
                .expect("write public-root inventory");
            fs::write(&reachable, render_reachable_rows(program, parsed))
                .expect("write web inventory");
            artifacts.extend([roots, public_roots, reachable]);
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
        "platform\tmachine_id\tprogram\troot_relation\tfn_ptr_roots\tpublic_roots\troot_public_overlap\tweb_closure\tweb_minus_roots\tlocal_functions\tcalls_total\tdirect_local\tindirect_local\tdirect_external\tindirect_unresolved\tnon_fn_def_constant\twall_s\tpeak_rss_kb\tshard_manifest_sha256\n",
    );
    let mut root_rows = String::from("platform\tmachine_id\tprogram\tfunction\tis_public\n");
    let mut public_rows = String::from("platform\tmachine_id\tprogram\tfunction\tis_fn_ptr_root\n");
    let mut reachable_rows = String::from("platform\tmachine_id\tprogram\tfunction\tis_root\n");
    let mut table = String::new();
    let mut inventories = String::new();
    let mut total_roots = 0usize;
    let mut total_web = 0usize;
    let mut wall_sum = 0.0;
    let mut peak_rss_kb = 0u64;
    for result in &completed {
        let graph = &result.artifact.graph;
        let coverage = &result.artifact.coverage;
        let extra = graph.reachable.len() - graph.fn_ptr_roots.len();
        total_roots += graph.fn_ptr_roots.len();
        total_web += graph.reachable.len();
        wall_sum += result.wall_s;
        peak_rss_kb = peak_rss_kb.max(result.peak_rss_kb);
        per_program.push_str(&format!(
            "{PLATFORM}\t{MACHINE_ID}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{:.3}\t{}\t{}\n",
            result.program,
            root_relation(graph),
            graph.fn_ptr_roots.len(),
            graph.public_roots.len(),
            graph.root_public_overlap.len(),
            graph.reachable.len(),
            extra,
            result.artifact.local_functions,
            coverage.calls_total,
            coverage.direct_local,
            coverage.indirect_local,
            coverage.direct_external,
            coverage.indirect_unresolved,
            coverage.non_fn_def_constant,
            result.wall_s,
            result.peak_rss_kb,
            result.manifest_sha256,
        ));
        table.push_str(&format!(
            "| `{PLATFORM}` | `{MACHINE_ID}` | `{}` | {} | {} | {} | `{}` | {:.3} | {} |\n",
            result.program,
            graph.fn_ptr_roots.len(),
            graph.reachable.len(),
            extra,
            root_relation(graph),
            result.wall_s,
            result.peak_rss_kb,
        ));
        let names = if graph.fn_ptr_roots.is_empty() {
            "(none)".to_owned()
        } else {
            graph
                .fn_ptr_roots
                .iter()
                .map(|name| format!("`{name}`"))
                .collect::<Vec<_>>()
                .join(", ")
        };
        inventories.push_str(&format!(
            "- `{PLATFORM}` / `{MACHINE_ID}` / `{}`: {} SHIM unit(s): {}\n",
            result.program,
            graph.fn_ptr_roots.len(),
            names
        ));
        root_rows.push_str(
            render_root_rows(&result.program, &result.artifact)
                .lines()
                .skip(1)
                .map(|line| format!("{line}\n"))
                .collect::<String>()
                .as_str(),
        );
        public_rows.push_str(
            render_public_root_rows(&result.program, &result.artifact)
                .lines()
                .skip(1)
                .map(|line| format!("{line}\n"))
                .collect::<String>()
                .as_str(),
        );
        reachable_rows.push_str(
            render_reachable_rows(&result.program, &result.artifact)
                .lines()
                .skip(1)
                .map(|line| format!("{line}\n"))
                .collect::<String>()
                .as_str(),
        );
    }

    let per_program_path = aggregate.join("per-program.tsv");
    let roots_path = aggregate.join("roots.tsv");
    let public_path = aggregate.join("public-roots.tsv");
    let reachable_path = aggregate.join("reachable.tsv");
    let report_path = aggregate.join("report.md");
    let provenance_path = aggregate.join("provenance.txt");
    let shard_manifests = completed
        .iter()
        .map(|result| format!("{}:{}", result.program, result.manifest_sha256))
        .collect::<Vec<_>>()
        .join(",");
    if aggregate_complete {
        for (path, expected) in [
            (&per_program_path, per_program.as_str()),
            (&roots_path, root_rows.as_str()),
            (&public_path, public_rows.as_str()),
            (&reachable_path, reachable_rows.as_str()),
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
        let provenance = parse_receipt(&provenance_path)
            .unwrap_or_else(|error| panic!("P-b aggregate provenance: {error}"));
        let analysis_head = super::orchestrate::git_sha();
        let total_roots_text = total_roots.to_string();
        let total_web_text = total_web.to_string();
        for (key, expected) in [
            ("machine_id", MACHINE_ID),
            ("platform", PLATFORM),
            ("analysis_head", analysis_head.as_str()),
            ("raw_corpus_sha256", RAW_CORPUS_SHA256),
            ("derived_corpus_sha256", DERIVED_CORPUS_SHA256),
            (
                "snapshot_inventory_sha256",
                snapshot_inventory_sha256.as_str(),
            ),
            ("shim_units", total_roots_text.as_str()),
            ("web_closure_units", total_web_text.as_str()),
            ("shard_manifest_sha256s", shard_manifests.as_str()),
        ] {
            assert_eq!(
                provenance.get(key).map(String::as_str),
                Some(expected),
                "P-b STOP: completed aggregate provenance {key} drifted"
            );
        }
        println!(
            "PBCENSUS machine_id={MACHINE_ID} platform={PLATFORM} status=verified-skip programs=20 shim_units={total_roots} web_closure_units={total_web}"
        );
        return;
    }
    fs::write(&per_program_path, per_program).expect("write per-program aggregate");
    fs::write(&roots_path, root_rows).expect("write root aggregate");
    fs::write(&public_path, public_rows).expect("write public-root aggregate");
    fs::write(&reachable_path, reachable_rows).expect("write reachable aggregate");
    fs::write(
        &report_path,
        format!(
            "# P-b function-pointer web census\n\n- Measurement identity: machine `{MACHINE_ID}`, platform `{PLATFORM}`. Every count and timing below belongs to this identity; timings are not compared across machines.\n- Registered web: forward reachability from `collect_fn_ptrs` roots only over local direct-call edges plus Andersen-resolved local indirect targets. Public-only roots are excluded.\n- SHIM price: **{total_roots} root units** on `{MACHINE_ID}` / `{PLATFORM}`.\n- Web-closure price: **{total_web} local function units** on `{MACHINE_ID}` / `{PLATFORM}` (**{} beyond the roots**).\n- Execution: 20/20 programs sequential, memory/CPU uncapped; Linux-local wall sum **{wall_sum:.3}s**, maximum observed per-program RSS **{peak_rss_kb} KiB**.\n- Signature-compatibility partition: **not measured**. The ratified history defines a safety obligation but no census identity/schema (`f746b9e593b9e0c3f8cf6494be160edd794b7f9b`, `b263a8e16897f2b5480a339d7aadda795963cfeb`). Reusing `FnPtrGroups` from `269b83ab2d8f22c6187e4ba8e4df00dcc462fca8` would execute new legacy analyses and a broader transitive storage-cell grouping, so this remains a priced gap.\n\n## Per-program prices\n\n| platform | machine | program | SHIM roots | web closure | extra web | root/public relation | wall s | peak RSS KiB |\n|---|---|---|---:|---:|---:|---|---:|---:|\n{table}\n## Root inventory (SHIM units)\n\n{inventories}\n",
            total_web - total_roots,
        ),
    )
    .expect("write P-b report");
    fs::write(
        &provenance_path,
        format!(
            "machine_id={MACHINE_ID}\nplatform={PLATFORM}\nanalysis_head={}\nprograms=20\nexecution=sequential\ndefinition=collect_fn_ptrs-forward-local-direct-plus-andersen-local-indirect\npublic_only_roots=excluded\nraw_corpus_sha256={RAW_CORPUS_SHA256}\nderived_corpus_sha256={DERIVED_CORPUS_SHA256}\nsnapshot_producer={SNAPSHOT_PRODUCER}\nsnapshot_manifest_commit={SNAPSHOT_MANIFEST_COMMIT}\nsnapshot_manifest_document_sha256={SNAPSHOT_MANIFEST_DOCUMENT_SHA256}\nsnapshot_inventory_sha256={snapshot_inventory_sha256}\nmemory_limit=uncapped\ncpu_limit=uncapped\nwall_bound_kind=liveness\nwall_cap_s={WALL_LIVENESS_SECS}\nwall_sum_s={wall_sum:.3}\npeak_program_rss_kb={peak_rss_kb}\nshim_units={total_roots}\nweb_closure_units={total_web}\nweb_minus_roots={}\nsignature_compatibility_groups=not-measured-new-analysis-required\nsignature_gap_commits=f746b9e593b9e0c3f8cf6494be160edd794b7f9b,b263a8e16897f2b5480a339d7aadda795963cfeb,269b83ab2d8f22c6187e4ba8e4df00dcc462fca8\nshard_manifest_sha256s={shard_manifests}\ntiming_comparison=forbidden-across-machines\n",
            super::orchestrate::git_sha(),
            total_web - total_roots,
        ),
    )
    .expect("write P-b provenance");
    write_sha256_manifest(
        &aggregate,
        &[
            per_program_path,
            roots_path,
            public_path,
            reachable_path,
            report_path,
            provenance_path,
        ],
        &aggregate_manifest,
    )
    .unwrap_or_else(|error| panic!("write P-b aggregate manifest: {error}"));
    verify_sha256_manifest(&aggregate, &aggregate_manifest)
        .unwrap_or_else(|error| panic!("verify P-b aggregate: {error}"));
    println!(
        "PBCENSUS machine_id={MACHINE_ID} platform={PLATFORM} programs=20 shim_units={total_roots} web_closure_units={total_web} web_minus_roots={} wall_sum_s={wall_sum:.3} peak_program_rss_kb={peak_rss_kb}",
        total_web - total_roots,
    );
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::{
        CallRoute, CoverageCounts, DERIVED_CORPUS_SHA256, GraphNode, RAW_CORPUS_SHA256,
        add_local_call_edges, classify_call_route, derived_corpus_digest, measure_graph,
        parse_worker_artifact, raw_corpus_digest, render_worker_artifact, wall_liveness,
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
    fn p_b_schema_rejects_call_coverage_mismatch() {
        let graph = BTreeMap::from([("root".to_owned(), node(true, false, &[]))]);
        let measured = measure_graph(&graph).expect("valid fixture");
        let coverage = CoverageCounts {
            calls_total: 1,
            ..Default::default()
        };
        assert!(
            render_worker_artifact("lambda7", "linux-x86_64", "fixture", &measured, 1, coverage,)
                .expect_err("coverage mismatch must fail")
                .contains("call coverage mismatch")
        );
    }

    #[test]
    fn p_b_wall_liveness_is_pinned() {
        assert_eq!(wall_liveness(None).expect("default").as_secs(), 3_600);
        assert_eq!(
            wall_liveness(Some("3600"))
                .expect("registered override")
                .as_secs(),
            3_600
        );
        assert!(wall_liveness(Some("3599")).is_err());
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
        assert!(
            add_local_call_edges(
                &mut graph,
                "root",
                CallRoute::UnsupportedConstant,
                ["direct".to_owned()],
            )
            .expect_err("unsupported constant must STOP")
            .contains("Andersen has no indirect-call site")
        );
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
