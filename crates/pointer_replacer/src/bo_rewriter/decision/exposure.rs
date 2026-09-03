//! Raw-boundary wave-2 exposure input and surface policy.
//!
//! Configured names arrive as owned data. This module never imports or calls
//! the legacy rewriter; the import denylist enforces that boundary.

use std::collections::{BTreeMap, BTreeSet};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::{LOCAL_CRATE, LocalDefId};
use rustc_span::symbol::sym;
use sha2::{Digest, Sha256};

use super::lifetime::FnPtrWeb;
use crate::utils::rustc::RustProgram;

pub(crate) const EXPOSURE_INPUT_VERSION: &str = "raw-boundary-exposure-seed/v1";

fn sha256(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn canonical_name_bytes(names: &BTreeSet<String>) -> Vec<u8> {
    names
        .iter()
        .cloned()
        .collect::<Vec<_>>()
        .join("\n")
        .into_bytes()
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ConfiguredExposureInput {
    pub(crate) version: &'static str,
    pub(crate) provenance: String,
    pub(crate) names: BTreeSet<String>,
    pub(crate) names_sha256: String,
}

impl ConfiguredExposureInput {
    pub(crate) fn checked(
        provenance: impl Into<String>,
        names: impl IntoIterator<Item = String>,
        claimed_sha256: impl Into<String>,
    ) -> Result<Self, ExposureInputFailure> {
        let mut canonical = BTreeSet::new();
        for name in names {
            if !canonical.insert(name.clone()) {
                return Err(ExposureInputFailure::DuplicateName(name));
            }
        }
        let observed = sha256(&canonical_name_bytes(&canonical));
        let claimed = claimed_sha256.into();
        if observed != claimed {
            return Err(ExposureInputFailure::DigestMismatch { claimed, observed });
        }
        Ok(Self {
            version: EXPOSURE_INPUT_VERSION,
            provenance: provenance.into(),
            names: canonical,
            names_sha256: observed,
        })
    }

    pub(crate) fn explicit_empty(provenance: impl Into<String>) -> Self {
        Self::checked(
            provenance,
            std::iter::empty(),
            sha256(&canonical_name_bytes(&BTreeSet::new())),
        )
        .expect("the canonical empty exposure input is valid")
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ExposureInputFailure {
    DigestMismatch {
        claimed: String,
        observed: String,
    },
    DuplicateName(String),
    UnmatchedName(String),
    AmbiguousName {
        name: String,
        functions: Vec<String>,
    },
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct SeedProvenance {
    pub(crate) configured_name: bool,
    pub(crate) address_taken: bool,
}

impl SeedProvenance {
    pub(crate) fn key(self) -> &'static str {
        match (self.configured_name, self.address_taken) {
            (true, true) => "both",
            (true, false) => "configured-name",
            (false, true) => "address-taken",
            (false, false) => "none",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ExposureSurfacePlan {
    PositiveSeedShim,
    FnPtrRawWrapper,
    ClosedWorldDirect,
    NotApplicable,
}

impl ExposureSurfacePlan {
    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::PositiveSeedShim => "positive-seed-entry-shim",
            Self::FnPtrRawWrapper => "fnptr-web-raw-wrapper",
            Self::ClosedWorldDirect => "internal-by-configuration",
            Self::NotApplicable => "not-applicable",
        }
    }
}

pub(crate) fn choose_surface_plan(
    positive_seed: bool,
    fnptr_web: bool,
    has_converting_signature_subject: bool,
) -> ExposureSurfacePlan {
    if !has_converting_signature_subject {
        ExposureSurfacePlan::NotApplicable
    } else if positive_seed {
        ExposureSurfacePlan::PositiveSeedShim
    } else if fnptr_web {
        ExposureSurfacePlan::FnPtrRawWrapper
    } else {
        ExposureSurfacePlan::ClosedWorldDirect
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct SeedCounts {
    pub(crate) configured_matches: usize,
    pub(crate) address_taken_roots: usize,
    pub(crate) both: usize,
    pub(crate) union: usize,
}

#[derive(Clone, Debug)]
pub(crate) struct ExposureSeed {
    members: FxHashMap<LocalDefId, SeedProvenance>,
    pub(crate) configured_input_sha256: String,
    pub(crate) manifest_sha256: String,
}

impl ExposureSeed {
    pub(crate) fn derive(
        program: &RustProgram<'_>,
        configured: &ConfiguredExposureInput,
        web: Option<&FnPtrWeb>,
    ) -> Result<Self, ExposureInputFailure> {
        let tcx = program.tcx;
        let mut by_name = BTreeMap::<String, Vec<LocalDefId>>::new();
        for &did in &program.functions {
            by_name
                .entry(tcx.item_name(did.to_def_id()).to_string())
                .or_default()
                .push(did);
            for attr in tcx.get_attrs(did.to_def_id(), sym::export_name) {
                if let Some(name) = attr.value_str() {
                    by_name.entry(name.to_string()).or_default().push(did);
                }
            }
        }
        for candidates in by_name.values_mut() {
            candidates.sort_unstable_by_key(|did| did.local_def_index.as_u32());
            candidates.dedup();
        }

        let mut members = FxHashMap::<LocalDefId, SeedProvenance>::default();
        for name in &configured.names {
            let Some(candidates) = by_name.get(name) else {
                return Err(ExposureInputFailure::UnmatchedName(name.clone()));
            };
            let [did] = candidates.as_slice() else {
                return Err(ExposureInputFailure::AmbiguousName {
                    name: name.clone(),
                    functions: candidates
                        .iter()
                        .map(|did| tcx.def_path_str(did.to_def_id()))
                        .collect(),
                });
            };
            members.entry(*did).or_default().configured_name = true;
        }
        if let Some(web) = web {
            for did in web.roots() {
                members.entry(did).or_default().address_taken = true;
            }
        }

        let crate_name = tcx.crate_name(LOCAL_CRATE);
        let mut rows = members
            .iter()
            .map(|(&did, &provenance)| {
                (
                    format!("{:?}", tcx.def_path_hash(did.to_def_id())),
                    format!(
                        "{}\t{}\t{}",
                        tcx.def_path_str(did.to_def_id()),
                        provenance.key(),
                        did.local_def_index.as_u32(),
                    ),
                )
            })
            .collect::<Vec<_>>();
        rows.sort_by(|left, right| left.0.cmp(&right.0));
        let mut manifest = format!(
            "version\t{EXPOSURE_INPUT_VERSION}\nprogram\t{crate_name}\nconfigured_provenance\t{}\nconfigured_sha256\t{}\n",
            configured.provenance, configured.names_sha256,
        );
        for (_, row) in rows {
            manifest.push_str("member\t");
            manifest.push_str(&row);
            manifest.push('\n');
        }
        let manifest_sha256 = sha256(manifest.as_bytes());
        Ok(Self {
            members,
            configured_input_sha256: configured.names_sha256.clone(),
            manifest_sha256,
        })
    }

    pub(crate) fn provenance(&self, did: LocalDefId) -> Option<SeedProvenance> {
        self.members.get(&did).copied()
    }

    pub(crate) fn contains(&self, did: LocalDefId) -> bool {
        self.members.contains_key(&did)
    }

    pub(crate) fn counts(&self) -> SeedCounts {
        let mut counts = SeedCounts::default();
        for provenance in self.members.values().copied() {
            counts.configured_matches += usize::from(provenance.configured_name);
            counts.address_taken_roots += usize::from(provenance.address_taken);
            counts.both += usize::from(provenance.configured_name && provenance.address_taken);
            counts.union += 1;
        }
        counts
    }
}

#[derive(Clone, Debug)]
pub(crate) struct FunctionExposure {
    pub(crate) did: LocalDefId,
    pub(crate) path: String,
    pub(crate) seed: Option<SeedProvenance>,
    pub(crate) fnptr_web: bool,
    pub(crate) plan: ExposureSurfacePlan,
}

#[derive(Clone, Debug)]
pub(crate) struct ExposurePolicy {
    functions: Vec<FunctionExposure>,
    seed_counts: SeedCounts,
    pub(crate) configured_input_sha256: String,
    pub(crate) manifest_sha256: String,
}

impl ExposurePolicy {
    pub(crate) fn derive(
        program: &RustProgram<'_>,
        seed: &ExposureSeed,
        web: Option<&FnPtrWeb>,
        converting_signature_functions: &FxHashSet<LocalDefId>,
    ) -> Self {
        let tcx = program.tcx;
        let mut functions = program
            .functions
            .iter()
            .copied()
            .map(|did| FunctionExposure {
                did,
                path: tcx.def_path_str(did.to_def_id()),
                seed: seed.provenance(did),
                fnptr_web: web.is_some_and(|web| web.contains(did)),
                plan: choose_surface_plan(
                    seed.contains(did),
                    web.is_some_and(|web| web.contains(did)),
                    converting_signature_functions.contains(&did),
                ),
            })
            .collect::<Vec<_>>();
        functions.sort_by(|left, right| left.path.cmp(&right.path));
        Self {
            functions,
            seed_counts: seed.counts(),
            configured_input_sha256: seed.configured_input_sha256.clone(),
            manifest_sha256: seed.manifest_sha256.clone(),
        }
    }

    pub(crate) fn plan(&self, did: LocalDefId) -> ExposureSurfacePlan {
        self.functions
            .iter()
            .find(|row| row.did == did)
            .map_or(ExposureSurfacePlan::NotApplicable, |row| row.plan)
    }

    pub(crate) fn seed_counts(&self) -> SeedCounts {
        self.seed_counts
    }

    pub(crate) fn receipts_tsv(&self) -> String {
        let mut out = String::from(
            "function\tconfigured_name\taddress_taken\tseed_provenance\tfnptr_web\tsurface_plan\tsurface_edit\touter_identity\tinner_identity\touter_metric\tinner_metric\tconfigured_input_sha256\tseed_manifest_sha256\n",
        );
        for row in &self.functions {
            let seed = row.seed.unwrap_or_default();
            let (surface_edit, outer_identity, inner_identity, outer_metric, inner_metric) =
                match row.plan {
                    ExposureSurfacePlan::PositiveSeedShim
                    | ExposureSurfacePlan::FnPtrRawWrapper => {
                        let name = row.path.rsplit("::").next().unwrap_or(&row.path);
                        (
                            "planned",
                            row.path.as_str(),
                            format!("__crat_safe_{name}"),
                            "unconverted",
                            "converted",
                        )
                    }
                    ExposureSurfacePlan::ClosedWorldDirect => (
                        "direct",
                        row.path.as_str(),
                        String::new(),
                        "converted",
                        "not-applicable",
                    ),
                    ExposureSurfacePlan::NotApplicable => (
                        "none",
                        row.path.as_str(),
                        String::new(),
                        "not-applicable",
                        "not-applicable",
                    ),
                };
            out.push_str(&format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
                row.path,
                u8::from(seed.configured_name),
                u8::from(seed.address_taken),
                seed.key(),
                u8::from(row.fnptr_web),
                row.plan.key(),
                surface_edit,
                outer_identity,
                inner_identity,
                outer_metric,
                inner_metric,
                self.configured_input_sha256,
                self.manifest_sha256,
            ));
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const EMPTY_SHA256: &str = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";

    #[test]
    fn c_w5a_configured_seed_selects_one_entry_shim() {
        let input = ConfiguredExposureInput::checked(
            "fixture-config",
            ["api".to_owned()],
            "14c2529eb4498c5d1ffd6915d05bf58a91bdda796af59f41d480d11c099d0479",
        )
        .expect("configured exposure input");
        assert_eq!(input.names.into_iter().collect::<Vec<_>>(), ["api"]);
        assert_eq!(
            choose_surface_plan(true, false, true),
            ExposureSurfacePlan::PositiveSeedShim
        );
    }

    #[test]
    fn c_w5b_address_taken_seed_selects_one_entry_shim() {
        assert_eq!(
            choose_surface_plan(true, true, true),
            ExposureSurfacePlan::PositiveSeedShim,
            "the positive seed owns the one raw outer surface"
        );
    }

    #[test]
    fn c_w5c_nonseed_is_closed_world_direct_never_internal() {
        assert_eq!(
            choose_surface_plan(false, false, true),
            ExposureSurfacePlan::ClosedWorldDirect
        );
        assert_eq!(
            ExposureSurfacePlan::ClosedWorldDirect.key(),
            "internal-by-configuration"
        );
    }

    #[test]
    fn c_w5d_explicit_empty_is_typed_and_not_all_internal() {
        let input = ConfiguredExposureInput::explicit_empty("fixture-empty");
        assert!(input.names.is_empty());
        assert_eq!(input.names_sha256, EMPTY_SHA256);
        assert_eq!(
            choose_surface_plan(false, false, true),
            ExposureSurfacePlan::ClosedWorldDirect
        );
    }

    #[test]
    fn c_w5e_seed_and_web_still_select_exactly_one_surface() {
        assert_eq!(
            choose_surface_plan(true, true, true),
            ExposureSurfacePlan::PositiveSeedShim
        );
        assert_eq!(
            choose_surface_plan(false, true, true),
            ExposureSurfacePlan::FnPtrRawWrapper
        );
    }

    #[test]
    fn c_w5_no_signature_subject_has_no_pointless_surface_edit() {
        assert_eq!(
            choose_surface_plan(true, true, false),
            ExposureSurfacePlan::NotApplicable
        );
    }

    #[test]
    fn c_n1_digest_mismatch_is_loud() {
        let Err(ExposureInputFailure::DigestMismatch { claimed, observed }) =
            ConfiguredExposureInput::checked("fixture-config", ["api".to_owned()], EMPTY_SHA256)
        else {
            panic!("digest mismatch must be typed")
        };
        assert_eq!(claimed, EMPTY_SHA256);
        assert_ne!(claimed, observed);
    }

    #[test]
    fn c_n1_duplicate_configured_name_is_loud() {
        assert_eq!(
            ConfiguredExposureInput::checked(
                "fixture-config",
                ["api".to_owned(), "api".to_owned()],
                EMPTY_SHA256,
            ),
            Err(ExposureInputFailure::DuplicateName("api".to_owned()))
        );
    }

    #[test]
    fn configured_exposure_input_digest_is_order_independent() {
        let digest = "7e18f737311b2dc3b2f269dd78396b0351f14fb66efa879f768cb23181883c78";
        let left = ConfiguredExposureInput::checked(
            "fixture-config",
            ["a".to_owned(), "b".to_owned()],
            digest,
        )
        .expect("left input");
        let right = ConfiguredExposureInput::checked(
            "fixture-config",
            ["b".to_owned(), "a".to_owned()],
            digest,
        )
        .expect("right input");
        assert_eq!(left, right);
    }

    fn inspect_seed<T: Send>(
        source: &str,
        inspect: impl FnOnce(&RustProgram<'_>, &ExposureSeed) -> T + Send,
    ) -> T {
        ::utils::compilation::run_compiler_on_str(source, |tcx| {
            let program = super::super::super::collect_program(tcx);
            let web = super::super::lifetime::derive_fn_ptr_web(
                &program,
                Some(
                    crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
                ),
            )
            .expect("attested fixture web");
            let configured = ConfiguredExposureInput::explicit_empty("fixture-empty");
            let seed = ExposureSeed::derive(&program, &configured, Some(&web)).expect("fixture seed");
            inspect(&program, &seed)
        })
        .expect("exposure fixture compiles")
    }

    #[test]
    fn c_w5b_attested_fnptr_root_is_address_taken_seed() {
        inspect_seed(
            "#![allow(dead_code, unused_unsafe)]\n\
             pub unsafe fn callback(p: *const i32) -> *const i32 { p }\n\
             pub unsafe fn install() {\n\
                 let _f: unsafe fn(*const i32) -> *const i32 = callback;\n\
             }\n",
            |program, seed| {
                let did = program
                    .functions
                    .iter()
                    .copied()
                    .find(|did| program.tcx.item_name(did.to_def_id()).as_str() == "callback")
                    .expect("callback function");
                assert_eq!(
                    seed.provenance(did),
                    Some(SeedProvenance {
                        configured_name: false,
                        address_taken: true,
                    })
                );
                assert_eq!(seed.counts().address_taken_roots, 1);
            },
        );
    }

    #[test]
    fn c_w5a_export_name_resolves_configured_data_without_legacy_helper() {
        ::utils::compilation::run_compiler_on_str(
            "#![allow(dead_code, unused_unsafe)]\n\
             #[export_name = \"public_api\"]\n\
             pub unsafe fn implementation(p: *const i32) -> *const i32 { p }\n",
            |tcx| {
                let program = super::super::super::collect_program(tcx);
                let web = super::super::lifetime::derive_fn_ptr_web(
                    &program,
                    Some(
                        crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
                    ),
                )
                .expect("attested fixture web");
                let names = ["public_api".to_owned()];
                let input = ConfiguredExposureInput::checked(
                    "fixture-config",
                    names.clone(),
                    sha256(&canonical_name_bytes(&names.into_iter().collect())),
                )
                .expect("configured input");
                let seed =
                    ExposureSeed::derive(&program, &input, Some(&web)).expect("configured seed");
                assert_eq!(seed.counts().configured_matches, 1);
            },
        )
        .expect("configured-name fixture compiles");
    }

    #[test]
    fn c_n1_unmatched_and_ambiguous_configured_names_are_loud() {
        ::utils::compilation::run_compiler_on_str(
            "#![allow(dead_code, unused_unsafe)]\n\
             mod a { pub unsafe fn api(p: *const i32) -> *const i32 { p } }\n\
             mod b { pub unsafe fn api(p: *const i32) -> *const i32 { p } }\n",
            |tcx| {
                let program = super::super::super::collect_program(tcx);
                let web = super::super::lifetime::derive_fn_ptr_web(
                    &program,
                    Some(
                        crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
                    ),
                )
                .expect("attested fixture web");
                let input = |name: &str| {
                    let names = [name.to_owned()];
                    ConfiguredExposureInput::checked(
                        "fixture-config",
                        names.clone(),
                        sha256(&canonical_name_bytes(&names.into_iter().collect())),
                    )
                    .expect("configured input")
                };
                assert!(matches!(
                    ExposureSeed::derive(&program, &input("missing"), Some(&web)),
                    Err(ExposureInputFailure::UnmatchedName(name)) if name == "missing"
                ));
                assert!(matches!(
                    ExposureSeed::derive(&program, &input("api"), Some(&web)),
                    Err(ExposureInputFailure::AmbiguousName { name, functions })
                        if name == "api" && functions.len() == 2
                ));
            },
        )
        .expect("ambiguous-name fixture compiles");
    }

    #[test]
    fn c_w5_pipeline_carries_configured_seed_and_closed_world_receipts() {
        ::utils::compilation::run_compiler_on_str(
            "#![allow(dead_code, unused_unsafe)]\n\
             pub unsafe fn api(p: *const i32) -> *const i32 { p }\n\
             pub unsafe fn helper(p: *const i32) -> *const i32 { p }\n",
            |tcx| {
                let names = ["api".to_owned()];
                let configured = ConfiguredExposureInput::checked(
                    "fixture-config",
                    names.clone(),
                    sha256(&canonical_name_bytes(&names.into_iter().collect())),
                )
                .expect("configured input");
                let run_config = super::super::super::EmissionRunConfig {
                    configured_exposure: configured,
                };
                let (_, ctx) = super::super::super::decide_table_with_emission_config(
                    tcx,
                    Some((
                        crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
                        Some(
                            crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph,
                        ),
                    )),
                    &run_config,
                )
                .expect("configured exposure decision table");
                let receipt = &ctx.raw_boundary_artifacts.exposure;
                let api = receipt
                    .lines()
                    .find(|line| {
                        line.starts_with(
                            "api\t1\t0\tconfigured-name\t0\tpositive-seed-entry-shim\t",
                        )
                    })
                    .expect("configured surface receipt");
                let api = api.split('\t').collect::<Vec<_>>();
                assert_eq!(api[6], "planned");
                assert_eq!(api[7], "api");
                assert_eq!(api[8], "__crat_safe_api");
                assert_eq!(&api[9..11], ["unconverted", "converted"]);
                assert!(
                    receipt.lines().any(|line| {
                        line.starts_with(
                            "helper\t0\t0\tnone\t0\tinternal-by-configuration\t",
                        )
                    }),
                    "{receipt}"
                );
                assert_eq!(ctx.exposure.seed_counts().configured_matches, 1);
                assert_eq!(ctx.exposure.seed_counts().union, 1);
            },
        )
        .expect("pipeline exposure fixture compiles");
    }
}
