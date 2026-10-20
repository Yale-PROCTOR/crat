//! M-BST-R predicate over complete typed observations of one sealed emitted
//! tree. Native observation collection and real-program execution remain gated.
use std::collections::BTreeSet;

use super::{OwnerId, SiteId};
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct PrintfLiteralCast {
    pub site: SiteId,
    pub callee: OwnerId,
    pub argument: u32,
    pub literal: [u8; 32],
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawKind {
    DeclarationType,
    InferredPointer,
    Operation,
    LiteralCast(PrintfLiteralCast),
}
#[derive(Clone, Debug)]
pub struct RawOccurrence {
    pub site: SiteId,
    pub kind: RawKind,
}
#[derive(Clone, Debug)]
pub struct TreeCheck {
    pub source_hash: [u8; 32],
    pub passed: bool,
}
#[derive(Clone, Debug)]
pub struct RawAudit {
    pub source_hash: [u8; 32],
    pub complete_inventory: Option<[u8; 32]>,
    pub occurrences: Vec<RawOccurrence>,
    pub compile: TreeCheck,
    pub custody: TreeCheck,
    pub literal_exceptions: BTreeSet<PrintfLiteralCast>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RawAuditHold {
    Inventory,
    Compile,
    Custody,
    Duplicate(SiteId),
    Residual(SiteId),
}
pub fn bst_emitted_zero_raw(audit: &RawAudit) -> Result<(), RawAuditHold> {
    if audit.complete_inventory != Some(audit.source_hash) {
        return Err(RawAuditHold::Inventory);
    }
    if !audit.compile.passed || audit.compile.source_hash != audit.source_hash {
        return Err(RawAuditHold::Compile);
    }
    if !audit.custody.passed || audit.custody.source_hash != audit.source_hash {
        return Err(RawAuditHold::Custody);
    }
    let mut sites = BTreeSet::new();
    for occurrence in &audit.occurrences {
        if !sites.insert(occurrence.site) {
            return Err(RawAuditHold::Duplicate(occurrence.site));
        }
        match &occurrence.kind {
            RawKind::LiteralCast(key)
                if key.site == occurrence.site
                    && key.argument == 0
                    && audit.literal_exceptions.contains(key) => {}
            _ => return Err(RawAuditHold::Residual(occurrence.site)),
        }
    }
    Ok(())
}
