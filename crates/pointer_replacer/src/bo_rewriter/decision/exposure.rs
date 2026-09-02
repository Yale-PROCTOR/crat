//! Raw-boundary wave-2 exposure input and surface policy.
//!
//! Configured names arrive as owned data. This module never imports or calls
//! the legacy rewriter; the import denylist enforces that boundary.

use std::collections::BTreeSet;

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
        let _ = (provenance, names, claimed_sha256);
        todo!("C-W5/C-N1 RED: configured exposure input is not implemented")
    }

    pub(crate) fn explicit_empty(provenance: impl Into<String>) -> Self {
        let _ = provenance;
        todo!("C-W5d RED: explicit empty input is not implemented")
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ExposureInputFailure {
    DigestMismatch,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ExposureSurfacePlan {
    PositiveSeedShim,
    FnPtrRawWrapper,
    ClosedWorldDirect,
    NotApplicable,
}

pub(crate) fn choose_surface_plan(
    positive_seed: bool,
    fnptr_web: bool,
    has_converting_signature_subject: bool,
) -> ExposureSurfacePlan {
    let _ = (positive_seed, fnptr_web, has_converting_signature_subject);
    todo!("C-W5 RED: exposure surface precedence is not implemented")
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
        assert_eq!(
            ConfiguredExposureInput::checked("fixture-config", ["api".to_owned()], EMPTY_SHA256,),
            Err(ExposureInputFailure::DigestMismatch)
        );
    }
}
