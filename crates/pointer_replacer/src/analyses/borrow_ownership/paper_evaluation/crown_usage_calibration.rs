//! Calibration harness that derives and validates CROWN's official usage
//! metric for the BO paper evaluation. The pinned counter itself lives under
//! `tools/crown_usage_metric/`.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::Path,
    process::Command,
};

use rustc_hash::FxHashMap;
use rustc_index::bit_set::DenseBitSet;
use rustc_middle::{
    mir::{
        Local, Location, Place, ProjectionElem, VarDebugInfoContents,
        visit::{PlaceContext, Visitor},
    },
    ty::TyCtxt,
};
use rustc_span::def_id::LocalDefId;

use crate::{
    analyses::{
        DefUse,
        mir_variable_grouping::SourceVarGroups,
        type_qualifier::foster::{
            fatness::{Fatness, fatness_analysis},
            mutability::{Mutability, mutability_analysis},
        },
    },
    rewriter::collect_input,
};

#[allow(dead_code, clippy::collapsible_if)]
mod artifact_inventory {
    include!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tools/crown_artifact_inventory/src/inventory.rs"
    ));
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Candidate {
    DerefDebugRoots,
    DerefSourceGroups,
    AllPlacesDebugRoots,
    AllPlacesSourceGroups,
    ReadPlacesDebugRoots,
    ReadPlacesSourceGroups,
    ReadWriteSitesDebugRoots,
    ReadWriteSitesSourceGroups,
    DerefBuiltDebugRoots,
    ReadPlacesBuiltDebugRoots,
    DerefLevelsDebugRoots,
    DerefLevelsSourceGroups,
    DerefAllRawInUniverseFunctions,
    ReadAllRawInUniverseFunctions,
    DerefFosterMutPtrLocals,
    DerefOptimizedMir2023DebugRoots,
}

impl Candidate {
    const ALL: [Self; 16] = [
        Self::DerefDebugRoots,
        Self::DerefSourceGroups,
        Self::AllPlacesDebugRoots,
        Self::AllPlacesSourceGroups,
        Self::ReadPlacesDebugRoots,
        Self::ReadPlacesSourceGroups,
        Self::ReadWriteSitesDebugRoots,
        Self::ReadWriteSitesSourceGroups,
        Self::DerefBuiltDebugRoots,
        Self::ReadPlacesBuiltDebugRoots,
        Self::DerefLevelsDebugRoots,
        Self::DerefLevelsSourceGroups,
        Self::DerefAllRawInUniverseFunctions,
        Self::ReadAllRawInUniverseFunctions,
        Self::DerefFosterMutPtrLocals,
        Self::DerefOptimizedMir2023DebugRoots,
    ];

    const fn label(self) -> &'static str {
        match self {
            Self::DerefDebugRoots => "deref-debug-roots",
            Self::DerefSourceGroups => "deref-source-groups",
            Self::AllPlacesDebugRoots => "all-places-debug-roots",
            Self::AllPlacesSourceGroups => "all-places-source-groups",
            Self::ReadPlacesDebugRoots => "read-places-debug-roots",
            Self::ReadPlacesSourceGroups => "read-places-source-groups",
            Self::ReadWriteSitesDebugRoots => "read-write-sites-debug-roots",
            Self::ReadWriteSitesSourceGroups => "read-write-sites-source-groups",
            Self::DerefBuiltDebugRoots => "deref-built-debug-roots",
            Self::ReadPlacesBuiltDebugRoots => "read-places-built-debug-roots",
            Self::DerefLevelsDebugRoots => "deref-levels-debug-roots",
            Self::DerefLevelsSourceGroups => "deref-levels-source-groups",
            Self::DerefAllRawInUniverseFunctions => "deref-all-raw-in-universe-functions",
            Self::ReadAllRawInUniverseFunctions => "read-all-raw-in-universe-functions",
            Self::DerefFosterMutPtrLocals => "deref-foster-mut-ptr-locals",
            Self::DerefOptimizedMir2023DebugRoots => "deref-optimized-mir-2023-debug-roots",
        }
    }
}

#[derive(Clone, Debug)]
struct ProgramMeasurement {
    program: String,
    declaration_universe: usize,
    official_usage: u64,
    native_json_usage: u64,
    unmapped_declarations: Vec<String>,
    candidates: BTreeMap<Candidate, Result<u64, String>>,
}

impl ProgramMeasurement {
    fn usage(&self, candidate: Candidate) -> Option<u64> {
        self.candidates.get(&candidate)?.as_ref().ok().copied()
    }
}

const CORPUS: [(&str, &str); 20] = [
    ("bst", "lib.rs"),
    ("avl", "lib.rs"),
    ("ht", "lib.rs"),
    ("libcsv", "lib.rs"),
    ("buffer", "lib.rs"),
    ("quadtree", "lib.rs"),
    ("urlparser", "lib.rs"),
    ("robotfindskitten", "lib.rs"),
    ("rgba", "lib.rs"),
    ("genann", "lib.rs"),
    ("libtree", "lib.rs"),
    ("json.h", "lib.rs"),
    ("binn", "lib.rs"),
    ("libzahl", "lib.rs"),
    ("lil", "lib.rs"),
    ("heman", "lib.rs"),
    ("bzip2", "c2rust-lib.rs"),
    ("lodepng", "lib.rs"),
    ("tulipindicators", "c2rust-lib.rs"),
    ("brotli", "lib.rs"),
];

#[derive(Clone)]
struct OfficialInputs {
    universe: BTreeSet<String>,
    official_usage: u64,
    native_json_usage: u64,
}

fn load_official_inputs(artifact_root: &Path, program: &str) -> Result<OfficialInputs, String> {
    let evaluation = artifact_inventory::parse_official_evaluation(
        &fs::read_to_string(artifact_root.join("evaluation.tsv"))
            .map_err(|error| format!("read evaluation.tsv: {error}"))?,
    )?
    .remove(program)
    .ok_or_else(|| format!("evaluation.tsv lacks {program}"))?;
    let analysis_root = artifact_root.join(program).join("analysis_results");
    let read_json = |name: &str| {
        fs::read_to_string(analysis_root.join(format!("{name}.json")))
            .map_err(|error| format!("{program}: read {name}.json: {error}"))
    };
    let claims = artifact_inventory::analyze_json_claims(
        &read_json("ownership")?,
        &read_json("statistics")?,
        &read_json("mutability")?,
        &read_json("fatness")?,
    )?;
    if claims.fn_d0_mut_ptr != evaluation.declaration_before {
        return Err(format!(
            "{program}: Mut ∩ Ptr d0 universe {} != official declaration BEFORE {}",
            claims.fn_d0_mut_ptr, evaluation.declaration_before
        ));
    }
    let native_json_usage = claims
        .statistics
        .get("num_non_arr_mut_unsafe_usages")
        .copied()
        .ok_or_else(|| format!("{program}: statistics lacks native usage counter"))?;
    Ok(OfficialInputs {
        universe: claims.fn_d0_mut_ptr_keys,
        official_usage: evaluation.usage_before,
        native_json_usage,
    })
}

fn measure_program(
    program: &str,
    input: &Path,
    artifact_root: &Path,
) -> Result<ProgramMeasurement, String> {
    let official = load_official_inputs(artifact_root, program)?;
    let historical_universe = official.universe.clone();
    let program_name = program.to_owned();
    let mut measurement = ::utils::compilation::run_compiler_on_path(input, move |tcx| {
        measure_tcx(tcx, &program_name, official)
    })
    .map_err(|_| format!("{program}: rustc rejected {}", input.display()))??;
    let historical_usage = measure_optimized_mir_2023(program, input, &historical_universe)?;
    let previous = measurement
        .candidates
        .insert(
            Candidate::DerefOptimizedMir2023DebugRoots,
            Ok(historical_usage),
        )
        .expect("candidate catalog initialized");
    assert_eq!(previous, Ok(0), "historical candidate placeholder drifted");
    Ok(measurement)
}

fn measure_optimized_mir_2023(
    program: &str,
    input: &Path,
    universe: &BTreeSet<String>,
) -> Result<u64, String> {
    let temp_universe = std::env::temp_dir().join(format!(
        "crat-crown-usage-universe-{}-{program}.txt",
        std::process::id()
    ));
    let contents = universe
        .iter()
        .map(|key| format!("{key}\n"))
        .collect::<String>();
    fs::write(&temp_universe, contents)
        .map_err(|error| format!("write {}: {error}", temp_universe.display()))?;

    let manifest =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tools/crown_usage_metric/Cargo.toml");
    let target = std::env::var_os("CRAT_CROWN_USAGE_2023_TARGET")
        .map(Into::into)
        .unwrap_or_else(|| std::env::temp_dir().join("crat-crown-usage-metric-2023-target"));
    let output = Command::new("cargo")
        .args([
            "+nightly-2023-01-26",
            "run",
            "--quiet",
            "--locked",
            "--manifest-path",
        ])
        .arg(&manifest)
        .args(["--", "--input"])
        .arg(input)
        .arg("--universe")
        .arg(&temp_universe)
        .env("CARGO_TARGET_DIR", target)
        .env_remove("RUSTC")
        .env_remove("RUSTDOC")
        .env_remove("RUSTFLAGS")
        .env_remove("CARGO_ENCODED_RUSTFLAGS")
        .output()
        .map_err(|error| format!("run historical usage counter: {error}"));
    let cleanup = fs::remove_file(&temp_universe)
        .map_err(|error| format!("remove {}: {error}", temp_universe.display()));
    let output = output?;
    cleanup?;
    if !output.status.success() {
        return Err(format!(
            "{program}: historical usage counter failed:\n{}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    String::from_utf8(output.stdout)
        .map_err(|error| format!("{program}: historical counter emitted non-UTF-8: {error}"))?
        .trim()
        .parse()
        .map_err(|error| format!("{program}: historical counter emitted a non-integer: {error}"))
}

fn source_group(
    groups: &SourceVarGroups,
    did: LocalDefId,
    root: Local,
    domain_size: usize,
) -> Vec<Local> {
    let mut without_root = DenseBitSet::new_filled(domain_size);
    without_root.remove(root);
    let processed = groups
        .postprocess_non_null_locals(FxHashMap::from_iter([(did, without_root)]))
        .remove(&did)
        .unwrap_or_else(|| DenseBitSet::new_empty(domain_size));
    (0..domain_size)
        .map(Local::from_usize)
        .filter(|local| !processed.contains(*local))
        .collect()
}

fn insert_mapping(
    mapping: &mut FxHashMap<Local, String>,
    local: Local,
    key: &str,
    function: &str,
) -> Result<(), String> {
    if let Some(existing) = mapping.insert(local, key.to_owned())
        && existing != key
    {
        return Err(format!(
            "{function}: MIR local _{} maps to both {existing} and {key}",
            local.index()
        ));
    }
    Ok(())
}

fn debug_root_mapping(
    tcx: TyCtxt<'_>,
    did: LocalDefId,
    body: &rustc_middle::mir::Body<'_>,
    universe: &BTreeSet<String>,
    seen_declarations: &mut BTreeSet<String>,
) -> Result<FxHashMap<Local, String>, String> {
    let function = tcx.def_path_str(did);
    let mut debug_roots = FxHashMap::default();
    for info in &body.var_debug_info {
        let VarDebugInfoContents::Place(place) = &info.value else {
            continue;
        };
        let Some(local) = place.as_local() else {
            continue;
        };
        let key = format!("{function}::{}", info.name);
        if universe.contains(&key) {
            insert_mapping(&mut debug_roots, local, &key, &function)?;
            seen_declarations.insert(key);
        }
    }
    Ok(debug_roots)
}

fn measure_tcx(
    tcx: TyCtxt<'_>,
    program_name: &str,
    official: OfficialInputs,
) -> Result<ProgramMeasurement, String> {
    let program = collect_input(tcx);
    let mut seen_declarations = BTreeSet::new();
    let mut totals = BTreeMap::from_iter(Candidate::ALL.map(|candidate| (candidate, 0u64)));
    let mut candidate_errors = BTreeMap::new();

    for &did in &program.functions {
        let built = tcx.mir_built(did);
        let body = built.borrow();
        let debug_roots =
            debug_root_mapping(tcx, did, &body, &official.universe, &mut seen_declarations)?;
        if debug_roots.is_empty() {
            continue;
        }
        let empty = FxHashMap::default();
        let mut visitor = UsageVisitor::new(&debug_roots, &empty);
        visitor.visit_body(&body);
        *totals
            .get_mut(&Candidate::DerefBuiltDebugRoots)
            .expect("candidate catalog initialized") += visitor.debug_root_counts.derefs;
        *totals
            .get_mut(&Candidate::ReadPlacesBuiltDebugRoots)
            .expect("candidate catalog initialized") += visitor.debug_root_counts.read_places;
    }

    let groups = SourceVarGroups::new(&program);
    let foster_qualifiers = if program_name == "urlparser" {
        candidate_errors.insert(
            Candidate::DerefFosterMutPtrLocals,
            "not evaluated: pre-existing current-toolchain fscanf parser panic".to_owned(),
        );
        None
    } else {
        Some((mutability_analysis(&program), fatness_analysis(&program)))
    };
    for &did in &program.functions {
        let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
        let function = tcx.def_path_str(did);
        let debug_roots =
            debug_root_mapping(tcx, did, &body, &official.universe, &mut seen_declarations)?;

        if let Some((mutability, fatness)) = &foster_qualifiers {
            let mut foster_mut_ptr_locals = DenseBitSet::new_empty(body.local_decls.len());
            for local in body.local_decls.indices().filter(|local| {
                mutability.function_body_fact(did, local.index(), 0) == Some(Mutability::Mut)
                    && fatness.function_body_fact(did, local.index(), 0) == Some(Fatness::Ptr)
            }) {
                foster_mut_ptr_locals.insert(local);
            }
            let mut foster_visitor = DerefVisitor {
                locals: &foster_mut_ptr_locals,
                derefs: 0,
            };
            foster_visitor.visit_body(&body);
            *totals
                .get_mut(&Candidate::DerefFosterMutPtrLocals)
                .expect("candidate catalog initialized") += foster_visitor.derefs;
        }

        if debug_roots.is_empty() {
            continue;
        }

        let mut source_groups = FxHashMap::default();
        for (&root, key) in &debug_roots {
            for local in source_group(&groups, did, root, body.local_decls.len()) {
                insert_mapping(&mut source_groups, local, key, &function)?;
            }
        }

        let mut visitor = UsageVisitor::new(&debug_roots, &source_groups);
        visitor.visit_body(&body);
        for (candidate, usages) in visitor.finish() {
            *totals
                .get_mut(&candidate)
                .expect("candidate catalog initialized") += usages;
        }
        let mut raw_visitor = RawUsageVisitor {
            body: &body,
            derefs: 0,
            reads: 0,
        };
        raw_visitor.visit_body(&body);
        *totals
            .get_mut(&Candidate::DerefAllRawInUniverseFunctions)
            .expect("candidate catalog initialized") += raw_visitor.derefs;
        *totals
            .get_mut(&Candidate::ReadAllRawInUniverseFunctions)
            .expect("candidate catalog initialized") += raw_visitor.reads;
    }

    let unmapped_declarations = official
        .universe
        .difference(&seen_declarations)
        .cloned()
        .collect();
    let candidates = Candidate::ALL
        .into_iter()
        .map(|candidate| {
            let result = candidate_errors
                .remove(&candidate)
                .map_or_else(|| Ok(totals[&candidate]), Err);
            (candidate, result)
        })
        .collect();
    Ok(ProgramMeasurement {
        program: program_name.to_owned(),
        declaration_universe: official.universe.len(),
        official_usage: official.official_usage,
        native_json_usage: official.native_json_usage,
        unmapped_declarations,
        candidates,
    })
}

fn candidate_csv(measurements: &[ProgramMeasurement]) -> String {
    let mut output = String::from(
        "program,candidate,declaration_universe,official_usage_before,observed_usage,delta_observed_minus_official,exact,native_json_usage,native_minus_official,unmapped_declarations,candidate_error\n",
    );
    for measurement in measurements {
        for candidate in Candidate::ALL {
            let result = &measurement.candidates[&candidate];
            let observed = result.as_ref().ok().copied();
            let delta =
                observed.map(|usages| i128::from(usages) - i128::from(measurement.official_usage));
            let native_delta =
                i128::from(measurement.native_json_usage) - i128::from(measurement.official_usage);
            output.push_str(&format!(
                "{},{},{},{},{},{},{},{},{},{},{}\n",
                measurement.program,
                candidate.label(),
                measurement.declaration_universe,
                measurement.official_usage,
                observed.map_or_else(String::new, |usages| usages.to_string()),
                delta.map_or_else(String::new, |delta| delta.to_string()),
                delta == Some(0),
                measurement.native_json_usage,
                native_delta,
                measurement.unmapped_declarations.join(";"),
                result.as_ref().err().map_or("", String::as_str)
            ));
        }
    }
    output
}

fn validation_csv(measurements: &[ProgramMeasurement]) -> String {
    let mut output = String::from(
        "program,declaration_universe,official_usage_before,observed_usage,delta_observed_minus_official,native_json_usage,native_minus_official\n",
    );
    let mut totals = (0usize, 0u64, 0u64, 0u64);
    for measurement in measurements {
        let observed = measurement
            .usage(Candidate::DerefOptimizedMir2023DebugRoots)
            .expect("winning candidate measured");
        output.push_str(&format!(
            "{},{},{},{},{},{},{}\n",
            measurement.program,
            measurement.declaration_universe,
            measurement.official_usage,
            observed,
            i128::from(observed) - i128::from(measurement.official_usage),
            measurement.native_json_usage,
            i128::from(measurement.native_json_usage) - i128::from(measurement.official_usage)
        ));
        totals.0 += measurement.declaration_universe;
        totals.1 += measurement.official_usage;
        totals.2 += observed;
        totals.3 += measurement.native_json_usage;
    }
    output.push_str(&format!(
        "TOTAL,{},{},{},{},{},{}\n",
        totals.0,
        totals.1,
        totals.2,
        i128::from(totals.2) - i128::from(totals.1),
        totals.3,
        i128::from(totals.3) - i128::from(totals.1)
    ));
    output
}

fn exact_candidates(measurements: &[ProgramMeasurement]) -> Vec<Candidate> {
    Candidate::ALL
        .into_iter()
        .filter(|candidate| {
            measurements.iter().all(|measurement| {
                measurement.usage(*candidate) == Some(measurement.official_usage)
            })
        })
        .collect()
}

struct UsageVisitor<'maps> {
    debug_roots: &'maps FxHashMap<Local, String>,
    source_groups: &'maps FxHashMap<Local, String>,
    debug_root_counts: UsageCounts,
    source_group_counts: UsageCounts,
}

#[derive(Default)]
struct UsageCounts {
    derefs: u64,
    deref_levels: u64,
    all_places: u64,
    read_places: u64,
    sites: BTreeSet<(String, Location)>,
}

struct RawUsageVisitor<'body, 'tcx> {
    body: &'body rustc_middle::mir::Body<'tcx>,
    derefs: u64,
    reads: u64,
}

struct DerefVisitor<'locals> {
    locals: &'locals DenseBitSet<Local>,
    derefs: u64,
}

impl UsageCounts {
    fn observe(
        &mut self,
        mapping: &FxHashMap<Local, String>,
        place: &Place<'_>,
        location: Location,
        def_use: &DefUse,
    ) {
        let Some(key) = mapping.get(&place.local) else {
            return;
        };
        self.all_places += 1;
        if matches!(def_use, DefUse::Use) {
            self.read_places += 1;
        }
        let levels = place
            .projection
            .iter()
            .filter(|projection| matches!(projection, ProjectionElem::Deref))
            .count() as u64;
        if levels != 0 {
            self.derefs += 1;
            self.deref_levels += levels;
        }
        self.sites.insert((key.clone(), location));
    }
}

impl<'maps> UsageVisitor<'maps> {
    fn new(
        debug_roots: &'maps FxHashMap<Local, String>,
        source_groups: &'maps FxHashMap<Local, String>,
    ) -> Self {
        Self {
            debug_roots,
            source_groups,
            debug_root_counts: UsageCounts::default(),
            source_group_counts: UsageCounts::default(),
        }
    }

    fn finish(self) -> [(Candidate, u64); 10] {
        [
            (Candidate::DerefDebugRoots, self.debug_root_counts.derefs),
            (
                Candidate::DerefSourceGroups,
                self.source_group_counts.derefs,
            ),
            (
                Candidate::AllPlacesDebugRoots,
                self.debug_root_counts.all_places,
            ),
            (
                Candidate::AllPlacesSourceGroups,
                self.source_group_counts.all_places,
            ),
            (
                Candidate::ReadPlacesDebugRoots,
                self.debug_root_counts.read_places,
            ),
            (
                Candidate::ReadPlacesSourceGroups,
                self.source_group_counts.read_places,
            ),
            (
                Candidate::ReadWriteSitesDebugRoots,
                self.debug_root_counts.sites.len() as u64,
            ),
            (
                Candidate::ReadWriteSitesSourceGroups,
                self.source_group_counts.sites.len() as u64,
            ),
            (
                Candidate::DerefLevelsDebugRoots,
                self.debug_root_counts.deref_levels,
            ),
            (
                Candidate::DerefLevelsSourceGroups,
                self.source_group_counts.deref_levels,
            ),
        ]
    }
}

impl<'tcx> Visitor<'tcx> for UsageVisitor<'_> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        let Some(def_use) = DefUse::for_place(*place, context) else {
            return;
        };
        self.debug_root_counts
            .observe(self.debug_roots, place, location, &def_use);
        self.source_group_counts
            .observe(self.source_groups, place, location, &def_use);
        self.visit_projection(place.as_ref(), context, location);
    }
}

impl<'tcx> Visitor<'tcx> for RawUsageVisitor<'_, 'tcx> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        if matches!(
            self.body.local_decls[place.local].ty.kind(),
            rustc_middle::ty::TyKind::RawPtr(..)
        ) && let Some(def_use) = DefUse::for_place(*place, context)
        {
            if matches!(def_use, DefUse::Use) {
                self.reads += 1;
            }
            if place.is_indirect() {
                self.derefs += 1;
            }
        }
        self.visit_projection(place.as_ref(), context, location);
    }
}

impl<'tcx> Visitor<'tcx> for DerefVisitor<'_> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        if self.locals.contains(place.local)
            && DefUse::for_place(*place, context).is_some()
            && place
                .projection
                .iter()
                .any(|projection| matches!(projection, ProjectionElem::Deref))
        {
            self.derefs += 1;
        }
        self.visit_projection(place.as_ref(), context, location);
    }
}

#[cfg(test)]
mod tests {
    use std::{fs, path::Path, sync::Mutex};

    use super::{
        CORPUS, Candidate, candidate_csv, exact_candidates, measure_program, validation_csv,
    };

    static CORPUS_LOCK: Mutex<()> = Mutex::new(());

    #[test]
    fn candidate_catalog_covers_registered_hypotheses() {
        assert_eq!(
            Candidate::ALL.map(Candidate::label),
            [
                "deref-debug-roots",
                "deref-source-groups",
                "all-places-debug-roots",
                "all-places-source-groups",
                "read-places-debug-roots",
                "read-places-source-groups",
                "read-write-sites-debug-roots",
                "read-write-sites-source-groups",
                "deref-built-debug-roots",
                "read-places-built-debug-roots",
                "deref-levels-debug-roots",
                "deref-levels-source-groups",
                "deref-all-raw-in-universe-functions",
                "read-all-raw-in-universe-functions",
                "deref-foster-mut-ptr-locals",
                "deref-optimized-mir-2023-debug-roots",
            ]
        );
    }

    #[test]
    #[ignore = "frozen rs-crown calibration: set CRAT_CROWN_USAGE_CORPUS and CRAT_CROWN_USAGE_ARTIFACT"]
    fn smallest_programs_match_official_usage_targets() {
        let _guard = CORPUS_LOCK.lock().expect("serialize CROWN usage runs");
        let corpus = std::env::var("CRAT_CROWN_USAGE_CORPUS")
            .expect("CRAT_CROWN_USAGE_CORPUS must name frozen rs-crown");
        let artifact = std::env::var("CRAT_CROWN_USAGE_ARTIFACT")
            .expect("CRAT_CROWN_USAGE_ARTIFACT must name frozen rs-crown-transformed");

        for (program, root, expected) in [
            ("bst", "lib.rs", 22),
            ("avl", "lib.rs", 41),
            ("ht", "lib.rs", 28),
        ] {
            let measured = measure_program(
                program,
                &Path::new(&corpus).join(program).join(root),
                Path::new(&artifact),
            )
            .unwrap_or_else(|error| panic!("{program}: {error}"));
            eprintln!(
                "{program}: official={} native={} declarations={} unmapped={:?} candidates={:?}",
                measured.official_usage,
                measured.native_json_usage,
                measured.declaration_universe,
                measured.unmapped_declarations,
                measured.candidates
            );
            let observed = measured
                .usage(Candidate::DerefOptimizedMir2023DebugRoots)
                .expect("winning candidate measured");
            assert_eq!(observed, expected, "{program}: winning candidate drift");
        }
    }

    #[test]
    #[ignore = "frozen 20-program calibration: set CRAT_CROWN_USAGE_CORPUS, CRAT_CROWN_USAGE_ARTIFACT, and CRAT_CROWN_USAGE_OUT"]
    fn corpus_candidate_scan() {
        let _guard = CORPUS_LOCK.lock().expect("serialize CROWN usage runs");
        let corpus = std::env::var("CRAT_CROWN_USAGE_CORPUS")
            .expect("CRAT_CROWN_USAGE_CORPUS must name frozen rs-crown");
        let artifact = std::env::var("CRAT_CROWN_USAGE_ARTIFACT")
            .expect("CRAT_CROWN_USAGE_ARTIFACT must name frozen rs-crown-transformed");
        let output = std::env::var("CRAT_CROWN_USAGE_OUT")
            .expect("CRAT_CROWN_USAGE_OUT must name a writable output directory");
        let mut measurements = Vec::new();
        for (program, root) in CORPUS {
            eprintln!("crown-usage: measuring {program}");
            measurements.push(
                measure_program(
                    program,
                    &Path::new(&corpus).join(program).join(root),
                    Path::new(&artifact),
                )
                .unwrap_or_else(|error| panic!("{program}: {error}")),
            );
        }
        assert!(
            measurements
                .iter()
                .all(|measurement| measurement.unmapped_declarations.is_empty()),
            "official declarations must all map to MIR debug roots: {:?}",
            measurements
                .iter()
                .filter(|measurement| !measurement.unmapped_declarations.is_empty())
                .map(|measurement| (
                    measurement.program.as_str(),
                    &measurement.unmapped_declarations
                ))
                .collect::<Vec<_>>()
        );
        fs::create_dir_all(&output).expect("create candidate output directory");
        fs::write(
            Path::new(&output).join("crown-usage-candidates.csv"),
            candidate_csv(&measurements),
        )
        .expect("write candidate CSV");
        fs::write(
            Path::new(&output).join("crown-usage-validation.csv"),
            validation_csv(&measurements),
        )
        .expect("write validation CSV");
        let exact = exact_candidates(&measurements);
        eprintln!(
            "crown-usage: exact candidates = {:?}",
            exact
                .iter()
                .map(|candidate| candidate.label())
                .collect::<Vec<_>>()
        );
        assert_eq!(
            exact,
            vec![Candidate::DerefOptimizedMir2023DebugRoots],
            "exactly the registered winner must reproduce all 20 programs"
        );
        assert_eq!(
            measurements
                .iter()
                .map(|measurement| measurement.declaration_universe)
                .sum::<usize>(),
            2_414
        );
        assert_eq!(
            measurements
                .iter()
                .map(|measurement| measurement.official_usage)
                .sum::<u64>(),
            12_448
        );
        assert_eq!(
            measurements
                .iter()
                .map(|measurement| {
                    measurement
                        .usage(Candidate::DerefOptimizedMir2023DebugRoots)
                        .expect("winning candidate measured")
                })
                .sum::<u64>(),
            12_448
        );
        assert_eq!(
            measurements
                .iter()
                .map(|measurement| measurement.native_json_usage)
                .sum::<u64>(),
            13_028
        );
    }
}
