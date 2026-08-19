//! Test-only harness for the Item 1.5 kind-equate core census.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
};

use rustc_middle::{mir::Local, ty::TyCtxt};
use sha2::{Digest, Sha256};
use z3::{SatResult, ast::Bool};

use super::{collect_program, report};
use crate::analyses::borrow_ownership::{
    CrateCtxt,
    coherence::{add_coherence_tagging_uses, constrain_field_ownership},
    crate_slots::CrateSlots,
    emit_crate_ownership_constraints,
    origins::compute_origins,
    solver::{KindSolver, SlotRef, core_label_family},
};

const SUBJECTS_SHA256: &str = "0c032a35cf9e5fc96df43f7291e4484709a6038030dd7c76e5a5c2acfbee8d57";
const SUBJECT_COUNT: usize = 4_895;
const KIND_RAW_COUNT: usize = 867;
const CLASS_BLOCKED_COUNT: usize = 698;
const USE_KIND_EQUATE_TAG: &str = "coherence-use::kind-equate";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Check {
    Sat,
    Unsat,
    Unknown,
}

#[derive(Debug, PartialEq, Eq)]
enum MinimizeError {
    Unknown(String),
    Invalid(String),
}

fn canonical_minimize<T: Clone>(
    mut core: Vec<T>,
    key: impl Fn(&T) -> String,
    mut check: impl FnMut(&[T]) -> Check,
) -> Result<Vec<T>, MinimizeError> {
    core.sort_by_key(&key);
    match check(&core) {
        Check::Unsat => {}
        Check::Sat => {
            return Err(MinimizeError::Invalid(
                "raw core did not recheck UNSAT".to_owned(),
            ));
        }
        Check::Unknown => {
            return Err(MinimizeError::Unknown(
                "raw core recheck returned Unknown".to_owned(),
            ));
        }
    }

    let mut index = 0;
    while index < core.len() {
        let mut candidate = core.clone();
        candidate.remove(index);
        match check(&candidate) {
            Check::Unsat => core = candidate,
            Check::Sat => index += 1,
            Check::Unknown => {
                return Err(MinimizeError::Unknown(format!(
                    "drop check returned Unknown at sorted index {index}"
                )));
            }
        }
    }

    match check(&core) {
        Check::Unsat => {}
        Check::Sat => {
            return Err(MinimizeError::Invalid(
                "final minimized core did not recheck UNSAT".to_owned(),
            ));
        }
        Check::Unknown => {
            return Err(MinimizeError::Unknown(
                "final minimized core recheck returned Unknown".to_owned(),
            ));
        }
    }
    for index in 0..core.len() {
        let mut candidate = core.clone();
        candidate.remove(index);
        match check(&candidate) {
            Check::Sat => {}
            Check::Unsat => {
                return Err(MinimizeError::Invalid(format!(
                    "final core is not 1-minimal at sorted index {index}"
                )));
            }
            Check::Unknown => {
                return Err(MinimizeError::Unknown(format!(
                    "1-minimality verification returned Unknown at sorted index {index}"
                )));
            }
        }
    }
    Ok(core)
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Subject {
    program: String,
    fn_path: String,
    mir_local: u32,
    degrade_reason: String,
}

impl Subject {
    fn identity(&self) -> String {
        format!("{}::{}::_{}", self.program, self.fn_path, self.mir_local)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CensusRow {
    subject: Subject,
    status: String,
    original_result: String,
    core_minimized: String,
    core_size: String,
    core_families: String,
    core_sha256: String,
    kind_equate_member: String,
    counterfactual_result: String,
    removal_sufficient: String,
    typed_absence: String,
    solver_reason: String,
}

impl CensusRow {
    fn baseline_not_sat(subject: Subject, result: &str, reason: &str) -> Self {
        Self {
            subject,
            status: "typed-absence".to_owned(),
            original_result: "not-queried".to_owned(),
            core_minimized: "not-applicable".to_owned(),
            core_size: "not-applicable".to_owned(),
            core_families: "not-applicable".to_owned(),
            core_sha256: "not-applicable".to_owned(),
            kind_equate_member: "not-applicable".to_owned(),
            counterfactual_result: "not-queried".to_owned(),
            removal_sufficient: "not-applicable".to_owned(),
            typed_absence: "baseline-not-SAT".to_owned(),
            solver_reason: format!("baseline-{result}:{reason}"),
        }
    }
}

fn parse_subjects(text: &str) -> Result<Vec<Subject>, String> {
    let mut lines = text.lines();
    let header = lines.next().ok_or("subject table is empty")?;
    let columns: Vec<_> = header.split('\t').collect();
    let column = |name: &str| {
        columns
            .iter()
            .position(|candidate| *candidate == name)
            .ok_or_else(|| format!("subject table lacks {name:?} column"))
    };
    let program_column = column("program")?;
    let function_column = column("fn_path")?;
    let local_column = column("mir_local")?;
    let reason_column = column("degrade_reason")?;
    let mut subjects = Vec::new();
    let mut identities = BTreeSet::new();
    for (offset, line) in lines.enumerate() {
        if line.is_empty() {
            return Err(format!("empty subject row at line {}", offset + 2));
        }
        let fields: Vec<_> = line.split('\t').collect();
        if fields.len() != columns.len() {
            return Err(format!(
                "subject row {} has {} columns, expected {}",
                offset + 2,
                fields.len(),
                columns.len()
            ));
        }
        let mir_local = fields[local_column]
            .parse::<u32>()
            .map_err(|error| format!("subject row {} mir_local: {error}", offset + 2))?;
        let subject = Subject {
            program: fields[program_column].to_owned(),
            fn_path: fields[function_column].to_owned(),
            mir_local,
            degrade_reason: fields[reason_column].to_owned(),
        };
        let identity = (
            subject.program.clone(),
            subject.fn_path.clone(),
            subject.mir_local,
        );
        if !identities.insert(identity) {
            return Err(format!("duplicate subject identity at line {}", offset + 2));
        }
        subjects.push(subject);
    }
    Ok(subjects)
}

fn render_rows(rows: &[CensusRow]) -> String {
    let mut output = String::from(
        "program\tfn_path\tmir_local\tdegrade_reason\tstatus\toriginal_result\tcore_minimized\tcore_size\tcore_families\tcore_sha256\tkind_equate_member\tcounterfactual_result\tremoval_sufficient\ttyped_absence\tsolver_reason\n",
    );
    for row in rows {
        output.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            row.subject.program,
            row.subject.fn_path,
            row.subject.mir_local,
            row.subject.degrade_reason,
            row.status,
            row.original_result,
            row.core_minimized,
            row.core_size,
            row.core_families,
            row.core_sha256,
            row.kind_equate_member,
            row.counterfactual_result,
            row.removal_sufficient,
            row.typed_absence,
            row.solver_reason,
        ));
    }
    output
}

fn write_atomic(path: &Path, contents: &str) -> Result<(), String> {
    let name = path
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(|| format!("non-UTF-8 output path: {}", path.display()))?;
    let temporary = path.with_file_name(format!(".{name}.tmp"));
    fs::write(&temporary, contents)
        .map_err(|error| format!("write {}: {error}", temporary.display()))?;
    fs::rename(&temporary, path).map_err(|error| {
        format!(
            "publish {} from {}: {error}",
            path.display(),
            temporary.display()
        )
    })
}

fn sha256_bytes(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn sha256_file(path: &Path) -> Result<String, String> {
    let bytes = fs::read(path).map_err(|error| format!("read {}: {error}", path.display()))?;
    Ok(sha256_bytes(&bytes))
}

fn check_kind_solver(solver: &KindSolver, assumptions: &[Bool]) -> Check {
    match solver.check_with_assumptions(assumptions) {
        SatResult::Sat => Check::Sat,
        SatResult::Unsat => Check::Unsat,
        SatResult::Unknown => Check::Unknown,
    }
}

fn solver_unknown_reason(solver: &KindSolver) -> String {
    solver
        .optimize()
        .get_reason_unknown()
        .unwrap_or_else(|| "no-reason-returned".to_owned())
        .replace(['\t', '\n', '\r'], " ")
}

fn build_tracked_solver<'tcx>(
    tcx: TyCtxt<'tcx>,
    program: &crate::utils::rustc::RustProgram<'tcx>,
) -> (CrateSlots, KindSolver) {
    let slots = CrateSlots::build(program);
    let crate_ctxt = CrateCtxt::new(program);
    let solver = KindSolver::new_tracked(&slots);
    solver.set_random_seed(0);
    emit_crate_ownership_constraints(&crate_ctxt, &slots, &compute_origins(program), &solver)
        .expect("tracked constraint emission");
    let tracker = solver.tracker().expect("tracked solver");
    tracker.set_context("coherence");
    for &did in &program.functions {
        let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
        add_coherence_tagging_uses(&solver, &slots, did, &body);
    }
    tracker.set_context("field-law");
    constrain_field_ownership(&solver, &slots, program);
    (slots, solver)
}

fn unknown_threshold(program_rows: usize) -> usize {
    5.max(program_rows.div_ceil(100))
}

fn check_label(check: Check) -> &'static str {
    match check {
        Check::Sat => "SAT",
        Check::Unsat => "UNSAT",
        Check::Unknown => "Unknown",
    }
}

fn core_key(
    tracker: &crate::analyses::borrow_ownership::solver::CoreTracker,
    force: &Bool,
    literal: &Bool,
) -> String {
    let label = tracker.label_of(literal).unwrap_or_else(|| {
        assert_eq!(literal, force, "unrecognized core assumption");
        "probe-force-own".to_owned()
    });
    format!("{label}\t{literal}")
}

fn resolve_subject_slots(
    tcx: TyCtxt<'_>,
    program: &crate::utils::rustc::RustProgram<'_>,
    slots: &CrateSlots,
    subjects: &[Subject],
) -> Result<Vec<(Subject, SlotRef)>, String> {
    let mut functions = BTreeMap::new();
    for &did in &program.functions {
        let path = tcx.def_path_str(did.to_def_id());
        if functions.insert(path.clone(), did).is_some() {
            return Err(format!("multiply-resolved function path {path}"));
        }
    }
    subjects
        .iter()
        .map(|subject| {
            let did = *functions
                .get(&subject.fn_path)
                .ok_or_else(|| format!("missing function path for {}", subject.identity()))?;
            let local = Local::from_u32(subject.mir_local);
            let slot = slots
                .fn_local_slots
                .get(&did)
                .and_then(|universe| universe.slot_for_local_depth(local, 0))
                .map(|slot| SlotRef::Local(did, slot))
                .ok_or_else(|| format!("missing depth-zero slot for {}", subject.identity()))?;
            Ok((subject.clone(), slot))
        })
        .collect()
}

fn count_unknown(row: &CensusRow) -> bool {
    row.original_result == "Unknown"
        || row.counterfactual_result == "Unknown"
        || row.typed_absence == "minimization-Unknown"
        || row.solver_reason.starts_with("baseline-Unknown")
}

pub(super) fn run_worker(tcx: TyCtxt<'_>, t_tcx: std::time::Duration) -> report::Row {
    let t0 = std::time::Instant::now();
    let program_name = std::env::var("CRAT_BOC1_NAME").expect("worker program name");
    let subjects_path = PathBuf::from(
        std::env::var_os("CRAT_KIND_EQUATE_SUBJECTS").expect("CRAT_KIND_EQUATE_SUBJECTS"),
    );
    let shard_dir = PathBuf::from(
        std::env::var_os("CRAT_KIND_EQUATE_SHARD_DIR").expect("CRAT_KIND_EQUATE_SHARD_DIR"),
    );
    fs::create_dir_all(&shard_dir).expect("create kind-equate worker shard directory");
    assert_eq!(
        sha256_file(&subjects_path).expect("hash frozen subject table"),
        SUBJECTS_SHA256,
        "frozen subject table digest mismatch"
    );
    let all_subjects =
        parse_subjects(&fs::read_to_string(&subjects_path).expect("read frozen subject table"))
            .expect("parse frozen subject table");
    assert_eq!(all_subjects.len(), SUBJECT_COUNT);
    assert_eq!(
        all_subjects
            .iter()
            .filter(|subject| subject.degrade_reason == "kind-raw")
            .count(),
        KIND_RAW_COUNT
    );
    assert_eq!(
        all_subjects
            .iter()
            .filter(|subject| subject.degrade_reason == "class-blocked")
            .count(),
        CLASS_BLOCKED_COUNT
    );
    let subjects: Vec<_> = all_subjects
        .into_iter()
        .filter(|subject| subject.program == program_name)
        .collect();
    assert!(!subjects.is_empty(), "{program_name}: zero query subjects");

    eprintln!("BOC1PHASE kind-equate-build program={program_name}");
    let program = collect_program(tcx);
    let (slots, solver) = build_tracked_solver(tcx, &program);
    let resolved = resolve_subject_slots(tcx, &program, &slots, &subjects)
        .unwrap_or_else(|error| panic!("kind-equate identity STOP: {error}"));
    let tracker = solver.tracker().expect("tracked solver");
    let labeled_tracks = tracker.labeled_tracks();
    let hard_tracks: Vec<_> = labeled_tracks
        .iter()
        .map(|(literal, _)| literal.clone())
        .collect();
    let counterfactual_tracks: Vec<_> = labeled_tracks
        .iter()
        .filter(|(_, label)| !label.contains(USE_KIND_EQUATE_TAG))
        .map(|(literal, _)| literal.clone())
        .collect();

    eprintln!("BOC1PHASE kind-equate-baseline program={program_name}");
    let baseline = check_kind_solver(&solver, &hard_tracks);
    let baseline_reason = if baseline == Check::Unknown {
        solver_unknown_reason(&solver)
    } else {
        "not-applicable".to_owned()
    };
    let mut rows = Vec::with_capacity(resolved.len());
    if baseline != Check::Sat {
        for (subject, _) in resolved {
            rows.push(CensusRow::baseline_not_sat(
                subject,
                check_label(baseline),
                &baseline_reason,
            ));
        }
        write_atomic(&shard_dir.join("checkpoint.tsv"), &render_rows(&rows))
            .expect("write atomic baseline-not-SAT checkpoint");
        let unknowns = rows.iter().filter(|row| count_unknown(row)).count();
        let threshold = unknown_threshold(subjects.len());
        if unknowns > threshold {
            panic!(
                "kind-equate Unknown threshold STOP: phase=baseline program={program_name} unknowns={unknowns} threshold={threshold} reason={baseline_reason}"
            );
        }
    } else {
        for (index, (subject, slot)) in resolved.into_iter().enumerate() {
            eprintln!(
                "BOC1PHASE kind-equate-original program={program_name} candidate={} index={}/{}",
                subject.identity(),
                index + 1,
                subjects.len()
            );
            let force_own = solver.owning_literal(slot);
            let mut original_assumptions = hard_tracks.clone();
            original_assumptions.push(force_own.clone());
            let original = check_kind_solver(&solver, &original_assumptions);
            let mut row = CensusRow {
                subject,
                status: "ok".to_owned(),
                original_result: check_label(original).to_owned(),
                core_minimized: "not-applicable".to_owned(),
                core_size: "not-applicable".to_owned(),
                core_families: "not-applicable".to_owned(),
                core_sha256: "not-applicable".to_owned(),
                kind_equate_member: "not-applicable".to_owned(),
                counterfactual_result: "not-queried".to_owned(),
                removal_sufficient: "not-applicable".to_owned(),
                typed_absence: "none".to_owned(),
                solver_reason: "not-applicable".to_owned(),
            };
            match original {
                Check::Sat => {
                    row.typed_absence = "original-not-hard-UNSAT".to_owned();
                    row.removal_sufficient = "not-applicable-original-sat".to_owned();
                }
                Check::Unknown => {
                    row.status = "typed-absence".to_owned();
                    row.typed_absence = "original-Unknown".to_owned();
                    row.solver_reason = solver_unknown_reason(&solver);
                }
                Check::Unsat => {
                    eprintln!(
                        "BOC1PHASE kind-equate-minimize program={program_name} candidate={}",
                        row.subject.identity()
                    );
                    let raw_core = solver.optimize().get_unsat_core();
                    match canonical_minimize(
                        raw_core,
                        |literal| core_key(tracker, &force_own, literal),
                        |candidate| check_kind_solver(&solver, candidate),
                    ) {
                        Ok(core) => {
                            assert!(
                                core.iter().any(|literal| literal == &force_own),
                                "{}: extracted core omitted force-own despite SAT hard baseline",
                                row.subject.identity()
                            );
                            let mut keys: Vec<_> = core
                                .iter()
                                .map(|literal| core_key(tracker, &force_own, literal))
                                .collect();
                            keys.sort();
                            let mut families = BTreeSet::new();
                            let mut member = false;
                            for literal in &core {
                                if let Some(label) = tracker.label_of(literal) {
                                    member |= label.contains("kind-equate");
                                    if let Some(family) = core_label_family(&label) {
                                        families.insert(family);
                                    }
                                } else {
                                    families.insert("probe-force-own");
                                }
                            }
                            row.core_minimized = "true".to_owned();
                            row.core_size = core.len().to_string();
                            row.core_families = families.into_iter().collect::<Vec<_>>().join(",");
                            row.core_sha256 = sha256_bytes(keys.join("\n").as_bytes());
                            row.kind_equate_member = member.to_string();
                        }
                        Err(MinimizeError::Unknown(phase)) => {
                            row.status = "typed-absence".to_owned();
                            row.typed_absence = "minimization-Unknown".to_owned();
                            row.solver_reason =
                                format!("{phase}:{}", solver_unknown_reason(&solver));
                        }
                        Err(MinimizeError::Invalid(error)) => {
                            panic!(
                                "kind-equate minimization STOP for {}: {error}",
                                row.subject.identity()
                            );
                        }
                    }
                }
            }

            eprintln!(
                "BOC1PHASE kind-equate-counterfactual program={program_name} candidate={}",
                row.subject.identity()
            );
            let mut counterfactual_assumptions = counterfactual_tracks.clone();
            counterfactual_assumptions.push(force_own);
            let counterfactual = check_kind_solver(&solver, &counterfactual_assumptions);
            row.counterfactual_result = check_label(counterfactual).to_owned();
            match counterfactual {
                Check::Sat => {
                    if original == Check::Unsat && row.typed_absence == "none" {
                        row.removal_sufficient = "true".to_owned();
                    }
                }
                Check::Unsat => {
                    if original == Check::Sat {
                        panic!(
                            "kind-equate monotonicity STOP for {}: dropping constraints changed SAT to UNSAT",
                            row.subject.identity()
                        );
                    }
                    if original == Check::Unsat && row.typed_absence == "none" {
                        row.removal_sufficient = "false".to_owned();
                    }
                }
                Check::Unknown => {
                    row.status = "typed-absence".to_owned();
                    if row.typed_absence == "none" {
                        row.typed_absence = "counterfactual-Unknown".to_owned();
                    } else {
                        row.typed_absence.push_str("+counterfactual-Unknown");
                    }
                    row.removal_sufficient = "not-applicable-Unknown".to_owned();
                    row.solver_reason = solver_unknown_reason(&solver);
                }
            }
            rows.push(row);
            write_atomic(&shard_dir.join("checkpoint.tsv"), &render_rows(&rows))
                .expect("write atomic per-subject checkpoint");
            let unknowns = rows.iter().filter(|row| count_unknown(row)).count();
            let threshold = unknown_threshold(subjects.len());
            if unknowns > threshold {
                panic!(
                    "kind-equate Unknown threshold STOP: phase=subject-complete program={program_name} candidate={} unknowns={unknowns} threshold={threshold} reason={}",
                    rows.last().expect("just pushed row").subject.identity(),
                    rows.last().expect("just pushed row").solver_reason
                );
            }
        }
    }

    write_atomic(&shard_dir.join("rows.tsv"), &render_rows(&rows))
        .expect("publish completed worker rows");
    let unknowns = rows.iter().filter(|row| count_unknown(row)).count();
    let hard_unsat = rows
        .iter()
        .filter(|row| row.original_result == "UNSAT" && row.typed_absence == "none")
        .count();
    let member = rows
        .iter()
        .filter(|row| row.kind_equate_member == "true")
        .count();
    let sufficient = rows
        .iter()
        .filter(|row| row.removal_sufficient == "true")
        .count();
    let mut output = report::Row::default();
    output.set("status", "ok");
    output.set("subjects", rows.len());
    output.set("hard_unsat", hard_unsat);
    output.set("kind_equate_member", member);
    output.set("removal_sufficient", sufficient);
    output.set("unknowns", unknowns);
    output.set("unknown_threshold", unknown_threshold(rows.len()));
    output.set("hard_tracks", hard_tracks.len());
    output.set(
        "dropped_use_equates",
        hard_tracks.len() - counterfactual_tracks.len(),
    );
    output.set("t_tcx_s", format!("{:.3}", t_tcx.as_secs_f64()));
    output.set("t_query_s", format!("{:.3}", t0.elapsed().as_secs_f64()));
    output
}

fn verify_manifest(dir: &Path, name: &str) -> Result<(), String> {
    let contents = fs::read_to_string(dir.join(name))
        .map_err(|error| format!("read {name} under {}: {error}", dir.display()))?;
    for (offset, line) in contents.lines().enumerate() {
        let (expected, relative) = line
            .split_once("  ./")
            .ok_or_else(|| format!("{name} line {} is malformed", offset + 1))?;
        let path = dir.join(relative);
        let actual = sha256_file(&path)?;
        if actual != expected {
            return Err(format!(
                "{name} hash mismatch for {}: {actual} != {expected}",
                path.display()
            ));
        }
    }
    Ok(())
}

fn write_manifest(dir: &Path, files: &[&str], name: &str) -> Result<String, String> {
    let mut files = files.to_vec();
    files.sort_unstable();
    let mut contents = String::new();
    for file in files {
        let path = dir.join(file);
        if !path.is_file() {
            return Err(format!("manifest input missing: {}", path.display()));
        }
        contents.push_str(&format!("{}  ./{}\n", sha256_file(&path)?, file));
    }
    write_atomic(&dir.join(name), &contents)?;
    sha256_file(&dir.join(name))
}

fn parse_output_rows(text: &str) -> Result<Vec<BTreeMap<String, String>>, String> {
    let mut lines = text.lines();
    let header = lines.next().ok_or("completed output is empty")?;
    let columns: Vec<_> = header.split('\t').collect();
    let expected = [
        "program",
        "fn_path",
        "mir_local",
        "degrade_reason",
        "status",
        "original_result",
        "core_minimized",
        "core_size",
        "core_families",
        "core_sha256",
        "kind_equate_member",
        "counterfactual_result",
        "removal_sufficient",
        "typed_absence",
        "solver_reason",
    ];
    if columns != expected {
        return Err(format!("completed output header mismatch: {columns:?}"));
    }
    lines
        .enumerate()
        .map(|(offset, line)| {
            let values: Vec<_> = line.split('\t').collect();
            if values.len() != columns.len() {
                return Err(format!(
                    "completed output line {} has {} columns, expected {}",
                    offset + 2,
                    values.len(),
                    columns.len()
                ));
            }
            Ok(columns
                .iter()
                .zip(values)
                .map(|(column, value)| ((*column).to_owned(), value.to_owned()))
                .collect())
        })
        .collect()
}

fn output_identity(row: &BTreeMap<String, String>) -> Result<(String, String, u32), String> {
    let field = |name: &str| {
        row.get(name)
            .cloned()
            .ok_or_else(|| format!("output row lacks {name}"))
    };
    Ok((
        field("program")?,
        field("fn_path")?,
        field("mir_local")?
            .parse::<u32>()
            .map_err(|error| format!("invalid output mir_local: {error}"))?,
    ))
}

fn validate_output_rows(
    program: &str,
    expected_subjects: &[Subject],
    rows: &[BTreeMap<String, String>],
) -> Result<(), String> {
    if rows.len() != expected_subjects.len() {
        return Err(format!(
            "{program}: output rows {} != expected {}",
            rows.len(),
            expected_subjects.len()
        ));
    }
    let expected: BTreeSet<_> = expected_subjects
        .iter()
        .map(|subject| {
            (
                subject.program.clone(),
                subject.fn_path.clone(),
                subject.mir_local,
            )
        })
        .collect();
    let actual: BTreeSet<_> = rows.iter().map(output_identity).collect::<Result<_, _>>()?;
    if actual.len() != rows.len() {
        return Err(format!("{program}: duplicate output identity"));
    }
    if actual != expected {
        let missing: Vec<_> = expected.difference(&actual).take(3).collect();
        let extra: Vec<_> = actual.difference(&expected).take(3).collect();
        return Err(format!(
            "{program}: output identity mismatch missing={missing:?} extra={extra:?}"
        ));
    }
    let mut unknowns = 0usize;
    for row in rows {
        let get = |name: &str| row.get(name).map(String::as_str).unwrap_or("<missing>");
        let status = get("status");
        let original = get("original_result");
        let typed = get("typed_absence");
        let counterfactual = get("counterfactual_result");
        if !matches!(status, "ok" | "typed-absence") {
            return Err(format!("{program}: invalid row status {status}"));
        }
        unknowns += usize::from(
            original == "Unknown"
                || counterfactual == "Unknown"
                || typed == "minimization-Unknown"
                || get("solver_reason").starts_with("baseline-Unknown"),
        );
        if original == "UNSAT" && typed == "none" {
            if get("core_minimized") != "true"
                || !matches!(get("kind_equate_member"), "true" | "false")
                || !matches!(counterfactual, "SAT" | "UNSAT")
                || !matches!(get("removal_sufficient"), "true" | "false")
            {
                return Err(format!(
                    "{program}: completed hard-UNSAT row violates core/flip schema: {row:?}"
                ));
            }
            let core_size = get("core_size")
                .parse::<usize>()
                .map_err(|error| format!("{program}: invalid core_size: {error}"))?;
            if core_size == 0 || get("core_sha256").len() != 64 {
                return Err(format!(
                    "{program}: invalid minimized core receipt: {row:?}"
                ));
            }
            if (counterfactual == "SAT") != (get("removal_sufficient") == "true") {
                return Err(format!("{program}: removal-sufficient/result mismatch"));
            }
        } else if original == "SAT" && typed != "original-not-hard-UNSAT" {
            return Err(format!(
                "{program}: SAT row lacks typed non-hard-UNSAT status"
            ));
        } else if original == "Unknown" && !typed.contains("Unknown") {
            return Err(format!("{program}: Unknown row lacks typed absence"));
        } else if original == "not-queried" && typed != "baseline-not-SAT" {
            return Err(format!(
                "{program}: unqueried row lacks baseline-not-SAT type"
            ));
        }
    }
    let threshold = unknown_threshold(rows.len());
    if unknowns > threshold {
        return Err(format!(
            "{program}: Unknown count {unknowns} exceeds threshold {threshold}"
        ));
    }
    Ok(())
}

fn git_output(root: &Path, args: &[&str]) -> Result<String, String> {
    let output = std::process::Command::new("git")
        .args(args)
        .current_dir(root)
        .output()
        .map_err(|error| format!("spawn git {}: {error}", args.join(" ")))?;
    if !output.status.success() {
        return Err(format!(
            "git {} failed: {}",
            args.join(" "),
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_owned())
}

fn render_map_rows(rows: &[BTreeMap<String, String>]) -> String {
    let header = [
        "program",
        "fn_path",
        "mir_local",
        "degrade_reason",
        "status",
        "original_result",
        "core_minimized",
        "core_size",
        "core_families",
        "core_sha256",
        "kind_equate_member",
        "counterfactual_result",
        "removal_sufficient",
        "typed_absence",
        "solver_reason",
    ];
    let mut output = format!("{}\n", header.join("\t"));
    for row in rows {
        output.push_str(
            &header
                .iter()
                .map(|column| row.get(*column).expect("validated output column").as_str())
                .collect::<Vec<_>>()
                .join("\t"),
        );
        output.push('\n');
    }
    output
}

fn aggregate_outputs(
    root: &Path,
    subjects: &[Subject],
    shard_metrics: &BTreeMap<String, (f64, u64, String)>,
) -> Result<(), String> {
    let aggregate = root.join("aggregate");
    fs::create_dir(&aggregate).map_err(|error| format!("create aggregate directory: {error}"))?;
    let mut all_rows = Vec::new();
    for program in super::CORPUS {
        let shard = root.join("shards").join(program.name);
        verify_manifest(&shard, "data-manifest.sha256")?;
        verify_manifest(&shard, "artifact-manifest.sha256")?;
        let receipt = fs::read_to_string(shard.join("receipt.txt"))
            .map_err(|error| format!("read {} receipt: {error}", program.name))?;
        if !receipt.contains("completed=true\ndata=true\n") {
            return Err(format!("{} shard is not completed data", program.name));
        }
        all_rows.extend(parse_output_rows(
            &fs::read_to_string(shard.join("rows.tsv"))
                .map_err(|error| format!("read {} rows: {error}", program.name))?,
        )?);
    }
    if all_rows.len() != SUBJECT_COUNT {
        return Err(format!(
            "aggregate rows {} != frozen {SUBJECT_COUNT}",
            all_rows.len()
        ));
    }
    let expected: BTreeSet<_> = subjects
        .iter()
        .map(|subject| {
            (
                subject.program.clone(),
                subject.fn_path.clone(),
                subject.mir_local,
            )
        })
        .collect();
    let actual: BTreeSet<_> = all_rows
        .iter()
        .map(output_identity)
        .collect::<Result<_, _>>()?;
    if actual.len() != SUBJECT_COUNT || actual != expected {
        return Err("aggregate identity is not exactly the frozen 4,895".to_owned());
    }
    write_atomic(&aggregate.join("rows.tsv"), &render_map_rows(&all_rows))?;

    let mut typed = String::from(
        "program\tfn_path\tmir_local\ttyped_absence\toriginal_result\tcounterfactual_result\tsolver_reason\n",
    );
    for row in &all_rows {
        if row["typed_absence"] != "none" {
            typed.push_str(&format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
                row["program"],
                row["fn_path"],
                row["mir_local"],
                row["typed_absence"],
                row["original_result"],
                row["counterfactual_result"],
                row["solver_reason"],
            ));
        }
    }
    write_atomic(&aggregate.join("typed-absences.tsv"), &typed)?;

    let mut per_program = String::from(
        "program\tquery_rows\thard_unsat_eligible\tkind_equate_member\tremoval_sufficient\toriginal_sat\ttyped_absences\tunknowns\twall_s\tpeak_rss_kb\tshard_manifest_sha256\n",
    );
    for program in super::CORPUS {
        let rows: Vec<_> = all_rows
            .iter()
            .filter(|row| row["program"] == program.name)
            .collect();
        let eligible = rows
            .iter()
            .filter(|row| row["original_result"] == "UNSAT" && row["typed_absence"] == "none")
            .count();
        let member = rows
            .iter()
            .filter(|row| row["kind_equate_member"] == "true")
            .count();
        let sufficient = rows
            .iter()
            .filter(|row| row["removal_sufficient"] == "true")
            .count();
        let original_sat = rows
            .iter()
            .filter(|row| row["original_result"] == "SAT")
            .count();
        let typed_absences = rows
            .iter()
            .filter(|row| row["typed_absence"] != "none")
            .count();
        let unknowns = rows
            .iter()
            .filter(|row| {
                row["original_result"] == "Unknown"
                    || row["counterfactual_result"] == "Unknown"
                    || row["typed_absence"] == "minimization-Unknown"
                    || row["solver_reason"].starts_with("baseline-Unknown")
            })
            .count();
        let (wall_s, peak_rss_kb, manifest) = &shard_metrics[program.name];
        per_program.push_str(&format!(
            "{}\t{}\t{eligible}\t{member}\t{sufficient}\t{original_sat}\t{typed_absences}\t{unknowns}\t{wall_s:.3}\t{peak_rss_kb}\t{manifest}\n",
            program.name,
            rows.len(),
        ));
    }
    write_atomic(&aggregate.join("per-program.tsv"), &per_program)?;

    let mut overlaps = String::from(
        "program\tpopulation\tpopulation_rows\thard_unsat_eligible\tkind_equate_member\tremoval_sufficient\n",
    );
    for program in std::iter::once("ALL").chain(super::CORPUS.iter().map(|program| program.name)) {
        for (population, reason) in [
            ("all-degraded", None),
            ("kind-raw", Some("kind-raw")),
            ("class-blocked", Some("class-blocked")),
        ] {
            let rows: Vec<_> = all_rows
                .iter()
                .filter(|row| program == "ALL" || row["program"] == program)
                .filter(|row| reason.is_none_or(|reason| row["degrade_reason"] == reason))
                .collect();
            let eligible = rows
                .iter()
                .filter(|row| row["original_result"] == "UNSAT" && row["typed_absence"] == "none")
                .count();
            let member = rows
                .iter()
                .filter(|row| row["kind_equate_member"] == "true")
                .count();
            let sufficient = rows
                .iter()
                .filter(|row| row["removal_sufficient"] == "true")
                .count();
            overlaps.push_str(&format!(
                "{program}\t{population}\t{}\t{eligible}\t{member}\t{sufficient}\n",
                rows.len()
            ));
        }
    }
    write_atomic(&aggregate.join("overlaps.tsv"), &overlaps)?;

    let eligible = all_rows
        .iter()
        .filter(|row| row["original_result"] == "UNSAT" && row["typed_absence"] == "none")
        .count();
    let member = all_rows
        .iter()
        .filter(|row| row["kind_equate_member"] == "true")
        .count();
    let sufficient = all_rows
        .iter()
        .filter(|row| row["removal_sufficient"] == "true")
        .count();
    let unknowns = all_rows
        .iter()
        .filter(|row| {
            row["original_result"] == "Unknown"
                || row["counterfactual_result"] == "Unknown"
                || row["typed_absence"] == "minimization-Unknown"
                || row["solver_reason"].starts_with("baseline-Unknown")
        })
        .count();
    let typed_absences = all_rows
        .iter()
        .filter(|row| row["typed_absence"] != "none")
        .count();
    let summary = format!(
        "machine_id=lambda7\nplatform=linux-x86_64\nstatus=complete\ncompleted=true\ndata=true\nquery_population={SUBJECT_COUNT}\nhard_unsat_eligible={eligible}\nkind_equate_member={member}\nremoval_sufficient={sufficient}\ntyped_absences={typed_absences}\nunknowns={unknowns}\ncore_definition=one_deterministic_drop-order-dependent_1-minimal_core\nhonesty_clause=membership_means_participation_in_the_extracted_explanation_not_necessity_to_every_explanation\nminimum_cardinality=out-of-scope\nevery-minimal-core-membership=out-of-scope\n"
    );
    write_atomic(&aggregate.join("summary.txt"), &summary)?;
    let data_manifest = write_manifest(
        &aggregate,
        &[
            "overlaps.tsv",
            "per-program.tsv",
            "rows.tsv",
            "summary.txt",
            "typed-absences.tsv",
        ],
        "data-manifest.sha256",
    )?;
    let receipt = format!(
        "machine_id=lambda7\nplatform=linux-x86_64\nphase=aggregate-complete\nstatus=ok\ncompleted=true\ndata=true\nrows={SUBJECT_COUNT}\nmanifest_sha256={data_manifest}\n"
    );
    write_atomic(&aggregate.join("receipt.txt"), &receipt)?;
    write_manifest(
        &aggregate,
        &[
            "data-manifest.sha256",
            "overlaps.tsv",
            "per-program.tsv",
            "receipt.txt",
            "rows.tsv",
            "summary.txt",
            "typed-absences.tsv",
        ],
        "artifact-manifest.sha256",
    )?;
    verify_manifest(&aggregate, "data-manifest.sha256")?;
    verify_manifest(&aggregate, "artifact-manifest.sha256")?;
    Ok(())
}

#[test]
#[ignore = "Item 1.5 official sequential kind-equate 1-minimal-core census"]
fn kind_equate_core_corpus() {
    use std::time::Duration;

    let root = super::orchestrate::workspace_root();
    let out = PathBuf::from(
        std::env::var_os("CRAT_KIND_EQUATE_OUT").expect("CRAT_KIND_EQUATE_OUT is required"),
    );
    let generic_out = PathBuf::from(
        std::env::var_os("CRAT_BOC1_OUT").expect("CRAT_BOC1_OUT must equal CRAT_KIND_EQUATE_OUT"),
    );
    assert_eq!(
        out, generic_out,
        "worker log/output roots must be identical"
    );
    assert!(
        !out.exists(),
        "fresh output directory already exists: {out:?}"
    );
    assert_eq!(
        std::env::var("CRAT_BOC1_MEM_MB").as_deref(),
        Ok("uncapped"),
        "Item 1.5 runs uncapped"
    );
    assert_eq!(
        std::env::var("CRAT_BOC1_SUBSTRATE").as_deref(),
        Ok("derived"),
        "Item 1.5 measures only the derived substrate of record"
    );
    assert_eq!(super::CORPUS.len(), 20);
    let expected_head = std::env::var("CRAT_KIND_EQUATE_HEAD").expect("expected analysis head");
    assert_eq!(super::orchestrate::git_sha(), expected_head);
    assert!(
        !super::orchestrate::git_dirty(),
        "measurement head is dirty"
    );
    assert_eq!(
        git_output(&root, &["branch", "--show-current"]).expect("read branch"),
        "codex/kind-equate-core-census"
    );
    assert_eq!(
        git_output(
            &root,
            &["rev-parse", "origin/codex/kind-equate-core-census"]
        )
        .expect("read published analysis head"),
        expected_head,
        "measurement head is not published"
    );
    assert_eq!(
        git_output(&root, &["rev-parse", "origin/tmp/bo-owning-probe"])
            .expect("read published user probe"),
        "852ba92a84757650713687182eeca8800db1bdfc",
        "user probe seed moved or was not fetched"
    );
    assert!(
        root.join("deps_crate/target/debug/deps").is_dir(),
        "deps_crate must be built in this worktree"
    );
    let substrate = super::a4_source_census::registered_substrate_digest(&root)
        .expect("verify registered substrate digest");
    assert_eq!(
        substrate,
        "db96829b5c2b0db28fb4bb9ddd3d32901b5d4e6e4134da07ada0d513d94eb4c6"
    );
    let source_root = PathBuf::from(
        std::env::var_os("CRAT_KIND_EQUATE_SOURCE_ROOT")
            .expect("CRAT_KIND_EQUATE_SOURCE_ROOT is required"),
    );
    assert_eq!(
        sha256_file(&source_root.join("artifact-manifest.sha256"))
            .expect("hash source artifact manifest"),
        "81e7047653cb647b875b58811b1aa79abffa576fa9ebd768b4354779847635f4"
    );
    verify_manifest(&source_root, "artifact-manifest.sha256")
        .expect("verify source artifact manifest");
    verify_manifest(&source_root, "data-manifest.sha256").expect("verify source data manifest");
    let subjects_path = source_root.join("reason-rows.tsv");
    assert_eq!(sha256_file(&subjects_path).unwrap(), SUBJECTS_SHA256);
    let subjects = parse_subjects(&fs::read_to_string(&subjects_path).expect("read subjects"))
        .expect("parse subjects");
    assert_eq!(subjects.len(), SUBJECT_COUNT);
    assert_eq!(
        subjects
            .iter()
            .filter(|subject| subject.degrade_reason == "kind-raw")
            .count(),
        KIND_RAW_COUNT
    );
    assert_eq!(
        subjects
            .iter()
            .filter(|subject| subject.degrade_reason == "class-blocked")
            .count(),
        CLASS_BLOCKED_COUNT
    );

    fs::create_dir(&out).expect("create fresh Item 1.5 output directory");
    fs::create_dir(out.join("shards")).expect("create shard directory");
    let hostname = std::process::Command::new("hostname")
        .output()
        .expect("run hostname");
    assert!(hostname.status.success());
    assert_eq!(String::from_utf8_lossy(&hostname.stdout).trim(), "lambda7");
    let rustc = std::process::Command::new("rustc")
        .arg("-Vv")
        .output()
        .expect("run rustc -Vv");
    assert!(rustc.status.success());
    let preflight = format!(
        "machine_id=lambda7\nplatform=linux-x86_64\nstatus=ok\nmeasurement_started=false\nanalysis_branch=codex/kind-equate-core-census\nanalysis_head={expected_head}\npreregistration_docs_commit=c5c7b2d\nuser_probe_commit=852ba92a84757650713687182eeca8800db1bdfc\nsource_rows_sha256={SUBJECTS_SHA256}\nsource_manifest_sha256=81e7047653cb647b875b58811b1aa79abffa576fa9ebd768b4354779847635f4\nsubstrate_sha256={substrate}\nquery_rows={SUBJECT_COUNT}\nkind_raw_rows={KIND_RAW_COUNT}\nclass_blocked_rows={CLASS_BLOCKED_COUNT}\nmemory_policy=uncapped\nwall_bound_kind=liveness\nwall_cap_per_program_s=14400\ntotal_liveness_envelope_s=288000\npeak_rss_metric=supervisor_poll_ps_rss_max_kb\nz3_full_version={}\nrustc={}\n",
        z3::full_version().replace('\n', " "),
        String::from_utf8_lossy(&rustc.stdout).replace('\n', " | ")
    );
    write_atomic(&out.join("preflight.txt"), &preflight).expect("write preflight");
    write_manifest(&out, &["preflight.txt"], "preflight-manifest.sha256")
        .expect("manifest preflight");

    let mut checkpoints = String::from(
        "program\tstatus\tcompleted\tdata\twall_s\tpeak_rss_kb\tshard_manifest_sha256\n",
    );
    let mut shard_metrics = BTreeMap::new();
    for program in super::CORPUS {
        let expected: Vec<_> = subjects
            .iter()
            .filter(|subject| subject.program == program.name)
            .cloned()
            .collect();
        assert!(!expected.is_empty(), "{} has zero subjects", program.name);
        let shard = out.join("shards").join(program.name);
        assert!(!shard.exists(), "fresh shard already exists: {shard:?}");
        eprintln!(
            "KIND-EQUATE phase=program-start program={} subjects={}",
            program.name,
            expected.len()
        );
        let input = program.input_path(&root);
        let outcome = super::orchestrate::run_child_env(
            program.name,
            &input,
            "kind-equate-core",
            Duration::from_secs(14_400),
            &[
                (
                    "CRAT_KIND_EQUATE_SUBJECTS",
                    subjects_path.display().to_string(),
                ),
                ("CRAT_KIND_EQUATE_SHARD_DIR", shard.display().to_string()),
            ],
        );
        fs::create_dir_all(&shard).expect("preserve worker shard directory");
        write_atomic(&shard.join("worker.stdout.log"), &outcome.stdout)
            .expect("write worker stdout receipt");
        write_atomic(&shard.join("worker.stderr.log"), &outcome.stderr)
            .expect("write worker stderr receipt");
        if outcome.status != "ok" {
            let note = outcome.note.replace(['\n', '\r'], " ");
            let receipt = format!(
                "machine_id=lambda7\nplatform=linux-x86_64\nphase=program-failed\nprogram={}\nstatus={}\ncompleted=false\ndata=false\nmeasurement_started=true\nanalysis_head={expected_head}\nwall_bound_kind=liveness\nwall_cap_s=14400\nmemory_policy=uncapped\npeak_rss_metric=supervisor_poll_ps_rss_max_kb\nwall_s={:.3}\npeak_rss_kb={}\nlast_phase={}\n",
                program.name, outcome.status, outcome.wall_s, outcome.peak_rss_kb, note
            );
            write_atomic(&shard.join("receipt.txt"), &receipt).expect("write failure receipt");
            let mut files = vec!["receipt.txt", "worker.stderr.log", "worker.stdout.log"];
            if shard.join("checkpoint.tsv").is_file() {
                files.push("checkpoint.tsv");
            }
            write_manifest(&shard, &files, "failure-manifest.sha256")
                .expect("manifest failed shard");
            panic!(
                "Item 1.5 STOP: phase=program program={} status={} note={}",
                program.name, outcome.status, outcome.note
            );
        }
        assert!(
            outcome.wall_s > 0.0 && outcome.peak_rss_kb > 0,
            "{} completed without real wall/RSS provenance: wall_s={} peak_rss_kb={}",
            program.name,
            outcome.wall_s,
            outcome.peak_rss_kb
        );
        let sentinel = outcome.row.as_ref().expect("successful worker sentinel");
        assert_eq!(
            sentinel
                .get("subjects")
                .and_then(|value| value.parse().ok()),
            Some(expected.len()),
            "{} sentinel subject count",
            program.name
        );
        let rows_text = fs::read_to_string(shard.join("rows.tsv"))
            .unwrap_or_else(|error| panic!("{} completed rows: {error}", program.name));
        let checkpoint = fs::read_to_string(shard.join("checkpoint.tsv"))
            .unwrap_or_else(|error| panic!("{} checkpoint: {error}", program.name));
        assert_eq!(
            rows_text, checkpoint,
            "{} final rows differ from last atomic checkpoint",
            program.name
        );
        let rows = parse_output_rows(&rows_text)
            .unwrap_or_else(|error| panic!("{} output schema STOP: {error}", program.name));
        validate_output_rows(program.name, &expected, &rows)
            .unwrap_or_else(|error| panic!("{} output validation STOP: {error}", program.name));
        let source_digests = format!(
            "artifact\tsha256\nreason-rows.tsv\t{SUBJECTS_SHA256}\nsource-artifact-manifest.sha256\t81e7047653cb647b875b58811b1aa79abffa576fa9ebd768b4354779847635f4\nsubstrate\t{substrate}\n"
        );
        write_atomic(&shard.join("source-digests.tsv"), &source_digests)
            .expect("write shard source digests");
        let data_manifest = write_manifest(
            &shard,
            &["checkpoint.tsv", "rows.tsv", "source-digests.tsv"],
            "data-manifest.sha256",
        )
        .expect("write shard data manifest");
        let receipt = format!(
            "machine_id=lambda7\nplatform=linux-x86_64\nphase=program-complete\nprogram={}\nstatus=ok\ncompleted=true\ndata=true\nmeasurement_started=true\nanalysis_head={expected_head}\nwall_bound_kind=liveness\nwall_cap_s=14400\nmemory_policy=uncapped\npeak_rss_metric=supervisor_poll_ps_rss_max_kb\nwall_s={:.3}\npeak_rss_kb={}\nrows={}\nunknown_threshold={}\nmanifest_sha256={data_manifest}\n",
            program.name,
            outcome.wall_s,
            outcome.peak_rss_kb,
            rows.len(),
            unknown_threshold(rows.len())
        );
        write_atomic(&shard.join("receipt.txt"), &receipt).expect("write shard receipt");
        let manifest = write_manifest(
            &shard,
            &[
                "checkpoint.tsv",
                "data-manifest.sha256",
                "receipt.txt",
                "rows.tsv",
                "source-digests.tsv",
                "worker.stderr.log",
                "worker.stdout.log",
            ],
            "artifact-manifest.sha256",
        )
        .expect("write shard artifact manifest");
        verify_manifest(&shard, "data-manifest.sha256").expect("verify shard data manifest");
        verify_manifest(&shard, "artifact-manifest.sha256")
            .expect("verify shard artifact manifest");
        checkpoints.push_str(&format!(
            "{}\tok\ttrue\ttrue\t{:.3}\t{}\t{manifest}\n",
            program.name, outcome.wall_s, outcome.peak_rss_kb
        ));
        write_atomic(&out.join("checkpoints.tsv"), &checkpoints)
            .expect("write aggregate checkpoint");
        shard_metrics.insert(
            program.name.to_owned(),
            (outcome.wall_s, outcome.peak_rss_kb, manifest),
        );
        eprintln!(
            "KIND-EQUATE phase=program-complete program={} wall_s={:.3} peak_rss_kb={}",
            program.name, outcome.wall_s, outcome.peak_rss_kb
        );
    }
    aggregate_outputs(&out, &subjects, &shard_metrics).expect("aggregate exact completed shards");
}

#[cfg(test)]
mod tests {
    use rustc_middle::mir::{Local, VarDebugInfoContents};

    use super::*;

    #[derive(Debug)]
    struct FixtureResult {
        hard_unsat: bool,
        kind_equate_member: bool,
    }

    fn function_and_local(
        tcx: TyCtxt<'_>,
        program: &crate::utils::rustc::RustProgram<'_>,
        function: &str,
        local_name: &str,
    ) -> (rustc_span::def_id::LocalDefId, Local) {
        let function = *program
            .functions
            .iter()
            .find(|&&did| tcx.def_path_str(did.to_def_id()).rsplit("::").next() == Some(function))
            .unwrap_or_else(|| panic!("no exact function named {function}"));
        if local_name == "_0" {
            return (function, Local::from_u32(0));
        }
        let body = tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        let local = body
            .var_debug_info
            .iter()
            .find_map(|info| {
                if info.name.as_str() != local_name {
                    return None;
                }
                let VarDebugInfoContents::Place(place) = &info.value else {
                    return None;
                };
                place.as_local()
            })
            .unwrap_or_else(|| panic!("no local named {local_name} in {function:?}"));
        (function, local)
    }

    fn probe_fixture(source: &str, function: &str, local_name: &str) -> FixtureResult {
        ::utils::compilation::run_compiler_on_str(source, |tcx| {
            let program = super::super::collect_program(tcx);
            let (function, local) = function_and_local(tcx, &program, function, local_name);
            let (slots, solver) = build_tracked_solver(tcx, &program);
            let tracker = solver.tracker().expect("tracked solver");
            let baseline = tracker.tracks();
            assert_eq!(
                check_kind_solver(&solver, &baseline),
                Check::Sat,
                "fixture hard baseline must be SAT"
            );
            let slot = slots
                .fn_local_slots
                .get(&function)
                .and_then(|universe| universe.slot_for_local_depth(local, 0))
                .map(|slot| SlotRef::Local(function, slot))
                .expect("fixture depth-zero local slot");
            let force_own = solver.owning_literal(slot);
            let mut assumptions = baseline;
            assumptions.push(force_own.clone());
            let hard_unsat = check_kind_solver(&solver, &assumptions) == Check::Unsat;
            if !hard_unsat {
                return FixtureResult {
                    hard_unsat,
                    kind_equate_member: false,
                };
            }
            let core = solver.optimize().get_unsat_core();
            let core = canonical_minimize(
                core,
                |literal| core_key(tracker, &force_own, literal),
                |candidate| check_kind_solver(&solver, candidate),
            )
            .expect("fixture core must minimize exactly");
            let kind_equate_member = core.iter().any(|literal| {
                tracker
                    .label_of(literal)
                    .is_some_and(|label| label.contains("kind-equate"))
            });
            FixtureResult {
                hard_unsat,
                kind_equate_member,
            }
        })
        .unwrap_or_else(|error| error.raise())
    }

    fn tagged_track_families(source: &str) -> (Vec<String>, Vec<String>) {
        ::utils::compilation::run_compiler_on_str(source, |tcx| {
            let program = super::super::collect_program(tcx);
            let (_slots, solver) = build_tracked_solver(tcx, &program);
            let tracker = solver.tracker().expect("tracked solver");
            let mut dropped = Vec::new();
            let mut retained = Vec::new();
            for (_literal, label) in tracker.labeled_tracks() {
                if label.contains(USE_KIND_EQUATE_TAG) {
                    dropped.push(label);
                } else if label.contains("coherence::kind-equate") {
                    retained.push(label);
                }
            }
            dropped.sort();
            retained.sort();
            (dropped, retained)
        })
        .unwrap_or_else(|error| error.raise())
    }

    const COPY_ALIASED_OWNING: &str = r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn s1(val: i32) -> i32 {
    let ptr1: *mut i32 = malloc(core::mem::size_of::<i32>()) as *mut i32;
    let alias: *mut i32 = ptr1;
    *alias = val;
    let result = *alias;
    free(ptr1 as *mut core::ffi::c_void);
    result
}
"#;

    const LINES_IN_BUFFER: &str = r#"
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}

pub unsafe fn lines_in_buffer(
    buffer: *mut i8,
    num_lines: usize,
) -> *mut *const i8 {
    let buffer_ptrs: *mut core::ffi::c_void =
        malloc(num_lines.wrapping_mul(core::mem::size_of::<*const i8>()));
    let line_pointers: *mut *const i8 = buffer_ptrs as *mut *const i8;
    if buffer_ptrs.is_null() {
        return core::ptr::null_mut();
    }
    if num_lines == 0 {
        free(buffer_ptrs);
        return core::ptr::null_mut();
    }
    *line_pointers = buffer;
    line_pointers
}
"#;

    const TRACK_PARTITION: &str = r#"
#[repr(C)]
pub struct Pair {
    pub p: *mut i32,
}

pub unsafe fn partition(p: *mut i32, pair: Pair) -> *mut i32 {
    let copied: *mut i32 = p;
    let deref_copied: *mut i32 = pair.p;
    let address: *const *mut i32 = &raw const copied;
    if deref_copied.is_null() { *address } else { copied }
}
"#;

    #[test]
    fn red_copy_aliased_owning_core_contains_kind_equate() {
        let result = probe_fixture(COPY_ALIASED_OWNING, "s1", "ptr1");
        assert!(result.hard_unsat, "positive control must be hard-UNSAT");
        assert!(
            result.kind_equate_member,
            "positive control's extracted 1-minimal core must contain kind-equate"
        );
    }

    #[test]
    fn red_lines_in_buffer_core_excludes_kind_equate() {
        let result = probe_fixture(LINES_IN_BUFFER, "lines_in_buffer", "_0");
        assert!(result.hard_unsat, "negative control must be hard-UNSAT");
        assert!(
            !result.kind_equate_member,
            "negative control's extracted 1-minimal core must omit kind-equate"
        );
    }

    #[test]
    fn red_use_track_partition_drops_only_use_and_copy_for_deref_equates() {
        let (dropped, retained) = tagged_track_families(TRACK_PARTITION);
        assert!(!dropped.is_empty(), "fixture must emit tagged Use tracks");
        assert!(
            dropped
                .iter()
                .all(|label| label.contains(USE_KIND_EQUATE_TAG)),
            "every dropped track must be a Use/CopyForDeref kind-equate: {dropped:?}"
        );
        assert!(
            retained
                .iter()
                .any(|label| label.contains("coherence::kind-equate")),
            "the non-Use kind-equate control must remain assumed: {retained:?}"
        );
    }

    #[test]
    fn red_canonical_minimizer_is_pinned_and_one_minimal() {
        let raw = vec!["c", "b", "a"];
        let minimized = canonical_minimize(
            raw,
            |item| (*item).to_owned(),
            |items| {
                if items.contains(&"a") && items.contains(&"b") {
                    Check::Unsat
                } else {
                    Check::Sat
                }
            },
        )
        .expect("deterministic minimization must complete");
        assert_eq!(minimized, vec!["a", "b"]);
    }

    #[test]
    fn parser_rejects_duplicate_subject_identity() {
        let text = "program\tfn_path\tmir_local\tdegrade_reason\n\
                    bst\tbst::f\t1\tkind-raw\n\
                    bst\tbst::f\t1\tclass-blocked\n";
        assert!(parse_subjects(text).unwrap_err().contains("duplicate"));
    }

    #[test]
    fn unknown_threshold_is_five_or_one_percent_rounded_up() {
        assert_eq!(unknown_threshold(1), 5);
        assert_eq!(unknown_threshold(500), 5);
        assert_eq!(unknown_threshold(501), 6);
        assert_eq!(unknown_threshold(1_666), 17);
    }
}
