//! Raw-boundary wave-1 worker/parent wire keys.
//!
//! Every shared producer/consumer names these identifiers. A migration changes
//! one authority and lets stale consumers fail at compile time.

#[cfg(test)]
pub(crate) const UNSAFE_CONTEXT_PRESENTATION_ROWS: &str = "unsafe-context-presentation.tsv";
#[cfg(test)]
pub(crate) const A5_PROOF_SITE_FALLBACK_ROWS: &str = "a5-proof-site-fallback.tsv";
#[cfg(test)]
pub(crate) const SLICE_CONSTRUCTION_RECEIPT_ROWS: &str = "slice-construction-receipt.tsv";
#[cfg(test)]
pub(crate) const SLICE_USE_ADAPTER_ROWS: &str = "slice-use-adapter.tsv";
#[cfg(test)]
pub(crate) const OPTION_PRESENTATION_RECEIPT_ROWS: &str = "option-presentation-receipt.tsv";
#[cfg(test)]
pub(crate) const DECLARATION_SHAPE_RECEIPT_ROWS: &str = "declaration-shape-receipt.tsv";
#[cfg(test)]
pub(crate) const OUTBOUND_RETURN_BRIDGE_ROWS: &str = "outbound-return-bridge.tsv";
#[cfg(test)]
pub(crate) const RAW_SINK_ADAPTER_ROWS: &str = "raw-sink-adapter.tsv";
#[cfg(test)]
pub(crate) const COMPOSITION_DEPENDENCY_ROWS: &str = "composition-dependency.tsv";
#[cfg(test)]
pub(crate) const MISSING_C_SHAPE_ROWS: &str = "missing-c-shapes.tsv";
#[cfg(test)]
pub(crate) const DIAGNOSTIC_PRIMARY_MESSAGE_ROWS: &str = "diagnostic-primary-message.tsv";
#[cfg(test)]
pub(crate) const JSON_H_RECOVERY_ROWS: &str = "json-h-recovery.tsv";
