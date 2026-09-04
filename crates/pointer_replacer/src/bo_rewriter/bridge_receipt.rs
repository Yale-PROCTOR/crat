//! Wave-3 bridge/class receipt vocabulary.
//!
//! This module records facts only. It neither chooses a bridge nor compares a
//! corpus control; those decisions stay in `decision` and `bo_c1` respectively.

use std::collections::BTreeMap;

use rustc_hir::def_id::LocalDefId;

pub(crate) const RAW_BOUNDARY_T2_WAIVER_ID: &str =
    "c-aliasing-semantics-at-unsafe-bridges/v1@2026-09-01";

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct SignatureClassId(LocalDefId);

impl SignatureClassId {
    pub(crate) fn of(did: LocalDefId) -> Self {
        Self(did)
    }

    pub(crate) fn local_def_id(self) -> LocalDefId {
        self.0
    }

    pub(crate) fn order_key(self) -> u32 {
        self.0.local_def_index.as_u32()
    }
}

impl PartialOrd for SignatureClassId {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for SignatureClassId {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.order_key().cmp(&other.order_key())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BridgeReceiptStage {
    Plan,
    Terminal,
}

impl BridgeReceiptStage {
    fn key(self) -> &'static str {
        match self {
            Self::Plan => "plan",
            Self::Terminal => "terminal",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BridgeReceiptState {
    Planned,
    Applied,
    Dropped,
}

impl BridgeReceiptState {
    fn key(self) -> &'static str {
        match self {
            Self::Planned => "planned",
            Self::Applied => "applied",
            Self::Dropped => "dropped",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum BridgeExtentKind {
    None,
    Evidence(String),
    Fallback,
}

impl BridgeExtentKind {
    fn key(&self) -> String {
        match self {
            Self::None => "none".to_owned(),
            Self::Evidence(source) => format!("evidence({source})"),
            Self::Fallback => "fallback(FALLBACK_SLICE_EXTENT=1024)".to_owned(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BridgeRetentionTier {
    None,
    T1,
    T2,
}

impl BridgeRetentionTier {
    fn key(self) -> &'static str {
        match self {
            Self::None => "none",
            Self::T1 => "T1",
            Self::T2 => "T2",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum BridgeCalleeId {
    Local(LocalDefId),
    Foreign(String),
}

impl BridgeCalleeId {
    fn receipt_key(&self) -> String {
        match self {
            Self::Local(did) => format!("local:{}", did.local_def_index.as_u32()),
            Self::Foreign(key) => format!("foreign:{key}"),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct BridgeSiteKey {
    pub(crate) owner_class: SignatureClassId,
    pub(crate) caller: LocalDefId,
    pub(crate) callee: BridgeCalleeId,
    pub(crate) arm: String,
    pub(crate) position: String,
    pub(crate) file: String,
    pub(crate) lo: u32,
    pub(crate) hi: u32,
    pub(crate) bridge_kind: String,
}

impl BridgeSiteKey {
    pub(crate) fn receipt_key(&self) -> String {
        format!(
            "{}:{}:{}:{}:{}:{}:{}:{}:{}",
            self.owner_class.order_key(),
            self.caller.local_def_index.as_u32(),
            self.callee.receipt_key(),
            self.arm,
            self.position,
            self.file,
            self.lo,
            self.hi,
            self.bridge_kind,
        )
    }

    #[cfg(test)]
    fn for_test(label: &str) -> Self {
        Self {
            owner_class: SignatureClassId::of(rustc_hir::def_id::CRATE_DEF_ID),
            caller: rustc_hir::def_id::CRATE_DEF_ID,
            callee: BridgeCalleeId::Local(rustc_hir::def_id::CRATE_DEF_ID),
            arm: "test".to_owned(),
            position: "arg0".to_owned(),
            file: "main.rs".to_owned(),
            lo: 0,
            hi: 1,
            bridge_kind: label.to_owned(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BridgeReceiptEvent {
    pub(crate) site: BridgeSiteKey,
    pub(crate) stage: BridgeReceiptStage,
    pub(crate) state: BridgeReceiptState,
    pub(crate) drop_reason: Option<String>,
    pub(crate) extent: BridgeExtentKind,
    pub(crate) retention: BridgeRetentionTier,
    pub(crate) waiver_id: Option<String>,
}

impl BridgeReceiptEvent {
    #[cfg(test)]
    pub(crate) fn for_test(
        label: &str,
        stage: BridgeReceiptStage,
        state: BridgeReceiptState,
    ) -> Self {
        Self {
            site: BridgeSiteKey::for_test(label),
            stage,
            state,
            drop_reason: (state == BridgeReceiptState::Dropped).then(|| "test-drop".to_owned()),
            extent: BridgeExtentKind::None,
            retention: BridgeRetentionTier::None,
            waiver_id: None,
        }
    }

    pub(crate) fn with_extent(mut self, extent: BridgeExtentKind) -> Self {
        self.extent = extent;
        self
    }

    pub(crate) fn with_retention(
        mut self,
        tier: BridgeRetentionTier,
        waiver_id: Option<&str>,
    ) -> Self {
        self.retention = tier;
        self.waiver_id = waiver_id.map(str::to_owned);
        self
    }

    fn validate(&self) -> Result<(), String> {
        match (self.stage, self.state) {
            (BridgeReceiptStage::Plan, BridgeReceiptState::Planned)
            | (
                BridgeReceiptStage::Terminal,
                BridgeReceiptState::Applied | BridgeReceiptState::Dropped,
            ) => {}
            _ => {
                return Err(format!(
                    "invalid bridge receipt stage/state: {}/{}",
                    self.stage.key(),
                    self.state.key()
                ));
            }
        }
        if self.state == BridgeReceiptState::Dropped
            && self.drop_reason.as_deref().is_none_or(str::is_empty)
        {
            return Err("dropped bridge receipt has no reason".to_owned());
        }
        if self.state != BridgeReceiptState::Dropped && self.drop_reason.is_some() {
            return Err("non-dropped bridge receipt has a drop reason".to_owned());
        }
        match (self.retention, self.waiver_id.as_deref()) {
            (BridgeRetentionTier::T2, Some(RAW_BOUNDARY_T2_WAIVER_ID)) => {}
            (BridgeRetentionTier::T2, _) => {
                return Err("T2 bridge receipt lacks the exact waiver ID".to_owned());
            }
            (BridgeRetentionTier::None | BridgeRetentionTier::T1, None) => {}
            (BridgeRetentionTier::None | BridgeRetentionTier::T1, Some(_)) => {
                return Err("non-T2 bridge receipt carries a waiver ID".to_owned());
            }
        }
        if matches!(&self.extent, BridgeExtentKind::Evidence(source) if source.is_empty()) {
            return Err("bridge extent has empty evidence source".to_owned());
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct BridgeReceiptSummary {
    pub(crate) required_sites: usize,
    pub(crate) planned_events: usize,
    pub(crate) applied_events: usize,
    pub(crate) dropped_events: usize,
}

pub(crate) fn reconcile_bridge_events(
    events: &[BridgeReceiptEvent],
) -> Result<BridgeReceiptSummary, String> {
    let mut by_site =
        BTreeMap::<String, (Option<&BridgeReceiptEvent>, Option<&BridgeReceiptEvent>)>::new();
    for event in events {
        event.validate()?;
        let key = event.site.receipt_key();
        let slot = by_site.entry(key.clone()).or_default();
        let destination = match event.stage {
            BridgeReceiptStage::Plan => &mut slot.0,
            BridgeReceiptStage::Terminal => &mut slot.1,
        };
        if destination.replace(event).is_some() {
            return Err(format!("duplicate {} event for {key}", event.stage.key()));
        }
    }

    let mut summary = BridgeReceiptSummary {
        required_sites: by_site.len(),
        ..BridgeReceiptSummary::default()
    };
    for (site, (plan, terminal)) in by_site {
        let Some(plan) = plan else {
            return Err(format!("bridge site {site} has no plan event"));
        };
        let Some(terminal) = terminal else {
            return Err(format!("bridge site {site} has no terminal event"));
        };
        if plan.extent != terminal.extent
            || plan.retention != terminal.retention
            || plan.waiver_id != terminal.waiver_id
        {
            return Err(format!(
                "bridge site {site} changed evidence between stages"
            ));
        }
        summary.planned_events += 1;
        match terminal.state {
            BridgeReceiptState::Applied => summary.applied_events += 1,
            BridgeReceiptState::Dropped => summary.dropped_events += 1,
            BridgeReceiptState::Planned => unreachable!("validated terminal event"),
        }
    }
    Ok(summary)
}

pub(crate) fn bridge_receipt_header() -> String {
    "site_key\towner_class\tcaller\tcallee\tarm\tposition\tfile\tlo\thi\tbridge_kind\textent_kind\tretention_tier\twaiver_id\tstage\tstate\tdrop_reason\n".to_owned()
}

pub(crate) fn render_bridge_events(events: &[BridgeReceiptEvent]) -> String {
    let mut rows = events
        .iter()
        .map(|event| {
            let site = &event.site;
            format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                site.receipt_key(),
                site.owner_class.order_key(),
                site.caller.local_def_index.as_u32(),
                site.callee.receipt_key(),
                site.arm,
                site.position,
                site.file,
                site.lo,
                site.hi,
                site.bridge_kind,
                event.extent.key(),
                event.retention.key(),
                event.waiver_id.as_deref().unwrap_or("-"),
                event.stage.key(),
                event.state.key(),
                event.drop_reason.as_deref().unwrap_or("-"),
            )
        })
        .collect::<Vec<_>>();
    rows.sort();
    let mut out = bridge_receipt_header();
    for row in rows {
        out.push_str(&row);
        out.push('\n');
    }
    out
}

pub(crate) fn class_cost_header() -> String {
    "program\tsignature_class_count\tattribution_exact_edit\tattribution_exact_seam\tattribution_related_span\tattribution_enclosing_region\tattribution_unresolved\tclass_bisect_probes\tverify_rounds\tverify_wall_s\temit_budget_s\n".to_owned()
}

pub(crate) fn class_collision_header() -> String {
    "program\tleft_class\tright_class\tleft_edit_key\tright_edit_key\tfile\tlo\thi\tleft_kind\tright_kind\n".to_owned()
}

pub(crate) fn unresolved_class_header() -> String {
    "program\tclass_local_def_index\tclass_path\treason\n".to_owned()
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use super::*;

    /// CLS-W3 — two real local functions may share the same display label, but
    /// their signature-class identity and revert membership stay distinct.
    #[test]
    fn signature_class_identity_is_not_a_display_name() {
        let result = ::utils::compilation::run_compiler_on_str(
            "mod left { pub fn same() {} } mod right { pub fn same() {} }",
            |tcx| {
                let mut functions = tcx
                    .hir_body_owners()
                    .filter(|did| tcx.item_name(did.to_def_id()).as_str() == "same")
                    .map(SignatureClassId::of)
                    .collect::<Vec<_>>();
                functions.sort();
                assert_eq!(functions.len(), 2);
                assert_ne!(functions[0], functions[1]);

                let labels = functions
                    .iter()
                    .copied()
                    .map(|id| (id, "same".to_owned()))
                    .collect::<BTreeMap<_, _>>();
                assert_eq!(labels.len(), 2, "equal display labels collapsed IDs");

                for (target_index, target) in functions.iter().copied().enumerate() {
                    let twin = functions[1 - target_index];
                    let reverted = BTreeSet::from([target]);
                    assert!(reverted.contains(&target));
                    assert_eq!(reverted.len(), 1);
                    let direct =
                        crate::bo_rewriter::ast_transform::revert_set_from_classes_and_atoms(
                            &reverted,
                            &BTreeSet::new(),
                            &crate::bo_rewriter::decision::DecisionTable::default(),
                        )
                        .expect("direct class set");
                    assert!(
                        !direct.keeps(target),
                        "target survived its direct-ID revert"
                    );
                    assert!(
                        direct.keeps(twin),
                        "homonymous twin was over-reverted with the target"
                    );
                    let receipt = super::super::render_raw_boundary_final_reverts(
                        &reverted,
                        &BTreeSet::new(),
                        &labels,
                    );
                    assert!(receipt.contains("function\tsame\tlocal-def-index:"));
                    assert!(receipt.contains(&target.order_key().to_string()));
                }
            },
        );
        assert!(result.is_ok());
    }

    /// Production verification must consume class IDs directly. Historical
    /// text-oracle name resolution may remain only behind `cfg(test)`.
    #[test]
    fn production_verify_path_never_resolves_class_names() {
        let source = include_str!("mod.rs");
        let start = source
            .find("fn round_files(")
            .expect("round_files definition");
        let tail = &source[start..];
        let end = tail
            .find("\nfn verify_and_revert(")
            .expect("verify_and_revert follows round_files");
        let production = &tail[..end];
        assert!(
            !production.contains("revert_set_from_names_and_atoms(tcx, reverted"),
            "round_files still resolves rendered owner names"
        );
    }

    #[test]
    fn bridge_receipt_render_is_order_independent_and_keeps_typed_evidence() {
        let plan = BridgeReceiptEvent::for_test(
            "site",
            BridgeReceiptStage::Plan,
            BridgeReceiptState::Planned,
        )
        .with_extent(BridgeExtentKind::Evidence("arg2".to_owned()))
        .with_retention(BridgeRetentionTier::T1, None);
        let terminal = BridgeReceiptEvent::for_test(
            "site",
            BridgeReceiptStage::Terminal,
            BridgeReceiptState::Applied,
        )
        .with_extent(BridgeExtentKind::Evidence("arg2".to_owned()))
        .with_retention(BridgeRetentionTier::T1, None);

        assert_eq!(
            render_bridge_events(&[plan.clone(), terminal.clone()]),
            render_bridge_events(&[terminal, plan])
        );
        let rendered = render_bridge_events(&[BridgeReceiptEvent::for_test(
            "foreign-site",
            BridgeReceiptStage::Plan,
            BridgeReceiptState::Planned,
        )
        .with_extent(BridgeExtentKind::None)]);
        assert!(rendered.starts_with("site_key\towner_class\tcaller\tcallee\t"));
    }

    #[test]
    fn foreign_callee_has_a_typed_identity_without_a_local_sentinel() {
        let mut event = BridgeReceiptEvent::for_test(
            "foreign-site",
            BridgeReceiptStage::Plan,
            BridgeReceiptState::Planned,
        );
        event.site.callee = BridgeCalleeId::Foreign("libc::strlen#0".to_owned());
        assert!(event.site.receipt_key().contains("foreign:libc::strlen#0"));
    }
}
