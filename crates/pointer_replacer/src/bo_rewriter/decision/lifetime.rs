//! E2-FN lifetime planning.
//!
//! This module is the sole rewriter-side consumer of the intact NB5-O
//! [`OriginSummaries`] carrier for lifetime semantics.  It starts with the
//! carrier-shape witness; eligibility, SCC planning, and emission receipts are
//! filled by the subsequent RED-first steps.

use crate::analyses::borrow_ownership::origin_summary::OriginSummaries;

/// The minimal E2-X1 observation used to prove that the carrier reaches this
/// module without an A5-specific projection.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct CarrierReceipt {
    pub(crate) summary_count: usize,
    pub(crate) native_flows: bool,
}

pub(crate) fn carrier_receipt(origins: Option<&OriginSummaries>) -> CarrierReceipt {
    CarrierReceipt {
        summary_count: origins.map_or(0, |origins| origins.len()),
        native_flows: origins.is_some_and(|origins| origins.try_native_flows().is_some()),
    }
}
