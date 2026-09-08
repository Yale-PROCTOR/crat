//! Complete captured observations with compiler identities resolved before transport.
//! This transport grants neither ownership nor a missing proof correspondence.

use std::collections::{BTreeMap, BTreeSet};

use super::{crate_slots::CrateSlots, export::BoExport};
use crate::utils::rustc::RustProgram;

pub(crate) const SCHEMA: &str = "era5a-portable-export-v1";

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum ExportFamily {
    OwnershipVersions,
    OwnershipValues,
    SourceSelectors,
    SinkSelectors,
    Loans,
    ResidualConflicts,
    ReallocVersions,
    ReallocCases,
    SourceInventory,
    ReplaySourceInventory,
    EntryProtection,
    EntryAccesses,
    EntryWitnesses,
    RetirementFinal,
    RetirementRounds,
    Comparisons,
    QualifierFacts,
    ArrayFields,
    DemandEvidence,
    ProofEvidence,
}

pub(crate) const REQUIRED_FAMILIES: [ExportFamily; 20] = [
    ExportFamily::OwnershipVersions,
    ExportFamily::OwnershipValues,
    ExportFamily::SourceSelectors,
    ExportFamily::SinkSelectors,
    ExportFamily::Loans,
    ExportFamily::ResidualConflicts,
    ExportFamily::ReallocVersions,
    ExportFamily::ReallocCases,
    ExportFamily::SourceInventory,
    ExportFamily::ReplaySourceInventory,
    ExportFamily::EntryProtection,
    ExportFamily::EntryAccesses,
    ExportFamily::EntryWitnesses,
    ExportFamily::RetirementFinal,
    ExportFamily::RetirementRounds,
    ExportFamily::Comparisons,
    ExportFamily::QualifierFacts,
    ExportFamily::ArrayFields,
    ExportFamily::DemandEvidence,
    ExportFamily::ProofEvidence,
];

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(tag = "state", rename_all = "kebab-case")]
pub(crate) enum CaptureAvailability {
    Captured,
    /// In particular, the existing L2 residual certificate is not recorded.
    NotRecorded {
        reason: String,
    },
}

#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum ScopeGap {
    OwnershipOccurrenceConstructionNotRecorded,
    OwnershipValuesAreLatestSuppliedValuation,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub(crate) enum CanonicalOwner {
    Local {
        function: String,
        local: u32,
    },
    Field {
        structure: String,
        field: String,
        field_index: usize,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub(crate) enum CanonicalBorrower {
    Assign { owner: CanonicalOwner },
    CallArg { callee: String, arg_index: usize },
}

/// Fields contain canonical source/slot/site/projection/owner/callee data.
/// A field holding an erased compiler definition index is never valid output.
/// Repeated stable keys are permitted: ER2 can contain repeated observations
/// across internal constructions. Retain multiplicity, do not invent a scope.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct PortableRecord {
    pub(crate) key: String,
    pub(crate) references: Vec<String>,
    pub(crate) fields: BTreeMap<String, serde_json::Value>,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct PortableFamily {
    pub(crate) availability: CaptureAvailability,
    /// Count from the actual capture, before conversion. No row deduplication.
    pub(crate) source_rows: usize,
    pub(crate) records: Vec<PortableRecord>,
}

/// Diagnostic labels are transported without becoming source identities.
/// Unreferenced Var valuations belong here; an old occurrence is not silently
/// assigned a value from a later construction's reused Var number.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct DiagnosticRecord {
    pub(crate) family: ExportFamily,
    pub(crate) source_key: String,
    pub(crate) labels: BTreeMap<String, serde_json::Value>,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct PortableExport {
    pub(crate) schema: String,
    pub(crate) licensing_deferred: bool,
    /// Resolved canonical identities; references never rely on numeric handles.
    pub(crate) identities: BTreeSet<String>,
    pub(crate) scope_gaps: BTreeSet<ScopeGap>,
    pub(crate) families: BTreeMap<ExportFamily, PortableFamily>,
    pub(crate) diagnostics: Vec<DiagnosticRecord>,
}

impl PortableExport {
    pub(crate) fn validate(&self) -> Result<(), String> {
        if self.schema != SCHEMA || !self.licensing_deferred {
            return Err("portable export schema/licensing mismatch".into());
        }
        if self.families.keys().copied().collect::<BTreeSet<_>>()
            != REQUIRED_FAMILIES.into_iter().collect()
        {
            return Err("missing or extra portable export family".into());
        }
        for (family, payload) in &self.families {
            match &payload.availability {
                CaptureAvailability::Captured => {}
                CaptureAvailability::NotRecorded { reason }
                    if *family == ExportFamily::ResidualConflicts
                        && !reason.is_empty()
                        && payload.source_rows == 0
                        && payload.records.is_empty() => {}
                _ => return Err(format!("required capture unavailable: {family:?}")),
            }
            if payload.source_rows != payload.records.len() {
                return Err(format!("incomplete portable family: {family:?}"));
            }
            if matches!(
                family,
                ExportFamily::RetirementFinal
                    | ExportFamily::DemandEvidence
                    | ExportFamily::ProofEvidence
            ) && payload.records.len() != 1
            {
                return Err(format!("missing singleton portable capture: {family:?}"));
            }
            for row in &payload.records {
                if row.key != record_key(*family, &row.fields)? {
                    return Err(format!("portable source identity mismatch: {family:?}"));
                }
                if row.key.is_empty()
                    || !self.identities.contains(&row.key)
                    || row
                        .references
                        .iter()
                        .any(|key| !self.identities.contains(key))
                {
                    return Err(format!("unresolved portable identity: {family:?}"));
                }
            }
        }
        if !self
            .scope_gaps
            .contains(&ScopeGap::OwnershipOccurrenceConstructionNotRecorded)
            || !self
                .scope_gaps
                .contains(&ScopeGap::OwnershipValuesAreLatestSuppliedValuation)
        {
            return Err("ownership occurrence/valuation scope gap erased".into());
        }
        for row in &self.diagnostics {
            if !self.families.contains_key(&row.family)
                || !self.identities.contains(&row.source_key)
            {
                return Err("dangling diagnostic source identity".into());
            }
        }
        Ok(())
    }

    pub(crate) fn canonical_json(&self) -> Result<String, String> {
        self.validate()?;
        let mut ordered = self.clone();
        for family in ordered.families.values_mut() {
            // Sorting retains repeated identical observations and ordered paths.
            family
                .records
                .sort_by_cached_key(|row| serde_json::to_string(row).expect("record JSON"));
        }
        ordered
            .diagnostics
            .sort_by_cached_key(|row| serde_json::to_string(row).expect("diagnostic JSON"));
        serde_json::to_string(&ordered).map_err(|error| error.to_string())
    }
}

// Only compiler identity lookup occurs here; no model, origin, or loan analysis.
use rustc_middle::mir::{Local, Location};
use rustc_span::def_id::LocalDefId;
use serde_json::{Value, json};

use super::{
    export as e, protected_entry as pe, realloc as ra, retirement as rt, slots::SlotOwner,
    solver::SlotRef, source_events as se,
};

fn tag(value: impl std::fmt::Debug) -> Value {
    json!(format!("{value:?}"))
}
fn location(value: Location) -> Value {
    json!({"block": value.block.as_u32(), "statement": value.statement_index})
}
fn mir_location(value: super::l2::MirLocationKey) -> Value {
    json!({"block": value.block, "statement": value.statement_index})
}
fn place(value: &e::PlaceKey) -> Value {
    use e::ProjKey;
    let projections = value.proj.iter().map(|projection| match *projection {
        ProjKey::Deref => json!({"kind":"deref"}),
        ProjKey::Field(field) => json!({"kind":"field", "field":field}),
        ProjKey::Index(local) => json!({"kind":"index", "local":local}),
        ProjKey::ConstantIndex {offset,min_length,from_end} => json!({"kind":"constant-index", "offset":offset,"min_length":min_length,"from_end":from_end}),
        ProjKey::Subslice {from,to,from_end} => json!({"kind":"subslice","from":from,"to":to,"from_end":from_end}),
        ProjKey::Downcast(variant) => json!({"kind":"downcast","variant":variant}),
        ProjKey::OpaqueCast => json!({"kind":"opaque-cast"}),
        ProjKey::Subtype => json!({"kind":"subtype"}),
        ProjKey::UnwrapUnsafeBinder => json!({"kind":"unwrap-unsafe-binder"}),
    }).collect::<Vec<_>>();
    json!({"local":value.local.as_u32(),"projections":projections})
}
fn source_key(key: &se::SourceEventKey) -> Value {
    json!({"function":key.function,"block":key.block,"statement":key.statement,
        "phase":tag(key.phase),"role":tag(key.role),"storage_local":key.storage_local,"condition":tag(key.condition)})
}
fn realloc_key(key: &ra::ReallocSiteKey) -> Value {
    json!({"function":key.function,"block":key.block,"statement":key.statement,"phase":tag(key.phase)})
}
fn source_event(event: &se::SourceRetirement) -> Value {
    let object = match &event.object {
        se::SourceObject::HeapThrough(p) => json!({"kind":"heap-through","place":place(p)}),
        se::SourceObject::PointerStorage(p) => json!({"kind":"pointer-storage","place":place(p)}),
        se::SourceObject::Storage(p) => json!({"kind":"storage","place":place(p)}),
        se::SourceObject::Null => json!({"kind":"null"}),
        se::SourceObject::UnknownOperand => json!({"kind":"unknown-operand"}),
    };
    json!({"key":source_key(&event.key),"object":object,"coverage":tag(event.coverage),
        "generation":tag(event.generation),"region":tag(event.region)})
}
fn source_route(route: &se::SourceCallRoute) -> Value {
    json!({"caller":route.caller,"callee":route.callee,"block":route.block,
        "events":route.events.iter().map(source_key).collect::<Vec<_>>(),
        "arguments":route.arguments.iter().map(|p|p.as_ref().map(place)).collect::<Vec<_>>(),
        "storage_relation_missing":route.storage_relation_missing})
}
fn transport(row: &ra::ResultTransport) -> Value {
    json!({"location":location(row.location),"source":row.source.as_u32(),"destination":row.destination.as_u32()})
}
fn realloc_site(site: &ra::ReallocSite) -> Value {
    let continuation = |row: &ra::ReallocContinuation| {
        let witness = row.witness.as_ref().map(|w| match w {
            ra::ReallocUseWitness::DirectDeref{location:loc,place:p,access_bytes} => json!({"kind":"direct-deref","location":location(*loc),"place":place(p),"access_bytes":access_bytes}),
            ra::ReallocUseWitness::LocalCall{location:loc,callee,argument,callee_deref,access_bytes} => json!({"kind":"local-call","location":location(*loc),"callee":callee,"argument":argument,"callee_deref":location(*callee_deref),"access_bytes":access_bytes}),
        });
        json!({"old":row.old.map(Local::as_u32),"old_place":row.old_place.as_ref().map(place),
            "result":row.result.map(Local::as_u32),"result_place":place(&row.result_place),
            "normal":row.normal.as_u32(),"transports":row.transports.iter().map(transport).collect::<Vec<_>>(),"witness":witness})
    };
    let result = match &site.result {
        ra::ReallocResult::DirectBranch(row) => {
            json!({"kind":"direct-branch","old":row.old.map(Local::as_u32),"result":row.result.as_u32(),"test":location(row.test),"success":row.success.as_u32(),"failure":row.failure.as_u32(),"transports":row.transports.iter().map(transport).collect::<Vec<_>>()})
        }
        ra::ReallocResult::SuccessImplied(row) => {
            json!({"kind":"success-implied","continuation":continuation(row)})
        }
        ra::ReallocResult::Unobserved(row) => {
            json!({"kind":"unobserved","continuation":continuation(row)})
        }
        ra::ReallocResult::FieldBranch {
            branch,
            continuation: row,
            field_transports,
        } => {
            json!({"kind":"field-branch","branch":{"old":branch.old.map(Local::as_u32),"result":branch.result.as_u32(),"test":location(branch.test),"success":branch.success.as_u32(),"failure":branch.failure.as_u32()},"continuation":continuation(row),"field_transports":field_transports.iter().map(|r|json!({"location":location(r.location),"source":place(&r.source),"destination":place(&r.destination)})).collect::<Vec<_>>()})
        }
        ra::ReallocResult::FallbackBothOutcomes(row) => {
            json!({"kind":"fallback-both-outcomes","receipt":site.result.result_test_receipt().map(|r|r.label()),"continuation":continuation(row)})
        }
        ra::ReallocResult::Discarded => json!({"kind":"discarded"}),
        ra::ReallocResult::UnresolvedTest => json!({"kind":"unresolved-test"}),
    };
    let callee = match &site.callee {
        ra::ReallocCalleeIdentity::ForeignC(name) => json!({"kind":"foreign-c","name":name}),
        ra::ReallocCalleeIdentity::LocalFunction(name) => {
            json!({"kind":"local-function","name":name})
        }
        ra::ReallocCalleeIdentity::Other => json!({"kind":"other"}),
    };
    let zero = site.zero_size.map(|z| match z {
        ra::ZeroSizeFeasibility::Possible => json!({"kind":"possible"}),
        ra::ZeroSizeFeasibility::ExcludedBySourceGuard(loc) => {
            json!({"kind":"excluded-by-source-guard","location":location(loc)})
        }
    });
    json!({"key":realloc_key(&site.key),"callee":callee,"old_input":tag(site.old_input),"size":tag(site.size),"zero_size":zero,"result":result,"success_address":tag(site.success_address)})
}

struct Resolver<'a, 'tcx> {
    program: &'a RustProgram<'tcx>,
    slots: &'a CrateSlots,
}
impl Resolver<'_, '_> {
    fn function(&self, did: LocalDefId) -> Result<String, String> {
        if !self.program.functions.contains(&did) {
            return Err("unresolved function identity".into());
        }
        Ok(self.program.tcx.def_path_str(did.to_def_id()))
    }

    fn named_function(&self, name: &str) -> Result<LocalDefId, String> {
        self.program
            .functions
            .iter()
            .copied()
            .find(|did| self.program.tcx.def_path_str(did.to_def_id()) == name)
            .ok_or_else(|| format!("unresolved source function: {name}"))
    }

    fn local(&self, function: LocalDefId, local: u32) -> Result<Value, String> {
        let name = self.function(function)?;
        let body = self
            .program
            .tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        if local as usize >= body.local_decls.len() {
            return Err("unresolved MIR local".into());
        }
        Ok(json!({"function":name,"local":local}))
    }

    fn field(&self, erased: u32, index: usize) -> Result<CanonicalOwner, String> {
        let did = self
            .program
            .structs
            .iter()
            .copied()
            .find(|did| did.local_def_index.as_u32() == erased)
            .ok_or("unresolved erased field owner")?;
        let ty = self.program.tcx.type_of(did).skip_binder();
        let rustc_middle::ty::TyKind::Adt(adt, _) = ty.kind() else {
            return Err("field owner is not ADT".into());
        };
        let field = adt
            .all_fields()
            .nth(index)
            .ok_or("unresolved field index")?;
        Ok(CanonicalOwner::Field {
            structure: self.program.tcx.def_path_str(did.to_def_id()),
            field: field.name.to_string(),
            field_index: index,
        })
    }

    fn owner(&self, function: LocalDefId, owner: e::OwnerKey) -> Result<CanonicalOwner, String> {
        match owner {
            e::OwnerKey::Local(local) => {
                self.local(function, local)?;
                Ok(CanonicalOwner::Local {
                    function: self.function(function)?,
                    local,
                })
            }
            e::OwnerKey::Field {
                struct_did,
                field_index,
            } => self.field(struct_did, field_index),
        }
    }

    fn slot(&self, reference: SlotRef) -> Result<String, String> {
        let (universe, id) = match reference {
            SlotRef::Local(function, id) => (
                self.slots
                    .fn_local_slots
                    .get(&function)
                    .ok_or("unknown slot function")?,
                id,
            ),
            SlotRef::Field(id) => (&self.slots.field_slots, id),
        };
        if id.as_usize() >= universe.len() {
            return Err("unresolved slot index".into());
        }
        let row = universe.slot(id);
        match (reference, row.owner) {
            (SlotRef::Local(function, _), SlotOwner::Local(local)) => {
                self.local(function, local.as_u32())?;
                Ok(super::slot_key::local_key(
                    self.program.tcx,
                    function,
                    local.as_usize(),
                    row.depth,
                ))
            }
            (SlotRef::Field(_), SlotOwner::Field(field)) => {
                self.field(field.struct_did.local_def_index.as_u32(), field.field_index)?;
                Ok(super::slot_key::field_key(
                    self.program.tcx,
                    field.struct_did,
                    field.field_index,
                    row.depth,
                ))
            }
            _ => Err("slot owner kind mismatch".into()),
        }
    }

    fn borrower(&self, function: LocalDefId, borrower: e::BorrowerKind) -> Result<Value, String> {
        let canonical = match borrower {
            e::BorrowerKind::Assign { owner } => CanonicalBorrower::Assign {
                owner: self.owner(function, owner)?,
            },
            e::BorrowerKind::CallArg { callee, arg_index } => {
                let did = self
                    .program
                    .functions
                    .iter()
                    .copied()
                    .find(|did| did.local_def_index.as_u32() == callee)
                    .ok_or("unresolved erased callee")?;
                let body = self
                    .program
                    .tcx
                    .mir_drops_elaborated_and_const_checked(did)
                    .borrow();
                if arg_index >= body.arg_count {
                    return Err("unresolved callee argument".into());
                }
                CanonicalBorrower::CallArg {
                    callee: self.function(did)?,
                    arg_index,
                }
            }
        };
        serde_json::to_value(canonical).map_err(|e| e.to_string())
    }

    fn entry(&self, row: pe::EntryKey) -> Result<Value, String> {
        Ok(
            json!({"function":self.function(row.function)?,"parameter":row.parameter.as_u32(),"depth":row.depth,"slot":self.slot(row.slot)?}),
        )
    }

    fn target(&self, row: pe::IncomingTarget) -> Result<Value, String> {
        Ok(json!({"entry":self.entry(row.entry)?,"dereferences":row.dereferences}))
    }

    fn fact(&self, row: &pe::EntryFact) -> Result<Value, String> {
        Ok(match row {
            pe::EntryFact::Entry(row) => {
                json!({"kind":"entry","entry":self.entry(row.key)?,"target":self.target(row.target)?,"condition":tag(row.condition),"representation":tag(row.representation)})
            }
            pe::EntryFact::Observation(row) => {
                let binding = match row.current_binding {
                    pe::CurrentBinding::Incoming(t) => {
                        json!({"kind":"incoming","target":self.target(t)?})
                    }
                    pe::CurrentBinding::Unknown => json!({"kind":"unknown"}),
                };
                json!({"kind":"observation","entry":self.entry(row.entry)?,"target":self.target(row.target)?,"location":location(row.location),"phase":tag(row.phase),"moment":tag(row.moment),"live":row.live,"demand":row.demand.map(|e|self.entry(e)).transpose()?,"current_binding":binding})
            }
            pe::EntryFact::Binding(row) => {
                json!({"kind":"binding","function":self.function(row.function)?,"local":row.local.as_u32(),"depth":row.depth,"location":location(row.location),"phase":tag(row.phase),"moment":tag(row.moment),"target":self.target(row.target)?})
            }
        })
    }

    fn steps(&self, rows: &[rt::RouteStep]) -> Result<Vec<Value>, String> {
        rows.iter().map(|row|Ok(json!({"caller":self.function(row.caller)?,"callee":self.function(row.callee)?,"location":location(row.location)}))).collect()
    }

    fn route_reason(&self, reason: &rt::RouteReason) -> Result<Value, String> {
        use rt::RouteReason as R;
        Ok(match reason {
            R::UnknownFunction(name) => json!({"kind":"unknown-function","name":name}),
            R::ForeignInputFrame(f) => {
                json!({"kind":"foreign-input-frame","function":self.function(*f)?})
            }
            R::Recursive(f) => json!({"kind":"recursive","function":self.function(*f)?}),
            R::MissingArgument { parameter, depth } => {
                json!({"kind":"missing-argument","parameter":parameter,"depth":depth})
            }
            R::InvalidEvent
            | R::InvalidCall
            | R::MissingSourceEvent
            | R::MissingRouteEvent
            | R::UnreachableRouteEvent
            | R::UnknownObject
            | R::DropEffects => json!({"kind":tag(reason)}),
        })
    }

    fn unresolved(&self, row: &rt::RetirementUnresolved) -> Result<(Value, Value), String> {
        use rt::UnresolvedReason as R;
        let mut diagnostic = Value::Null;
        let reason = match &row.reason {
            R::Route(problem) => {
                json!({"kind":"route","source":problem.source.as_ref().map(source_event),"route":problem.route.as_ref().map(source_route),"reason":self.route_reason(&problem.reason)?})
            }
            R::Entry(error) => {
                let (kind, key, loc) = match *error {
                    pe::EntryCoverageError::MissingEntry(key) => ("missing-entry", key, None),
                    pe::EntryCoverageError::MissingPoint(key, loc) => {
                        ("missing-point", key, Some(loc))
                    }
                    pe::EntryCoverageError::InconsistentDemand(key, loc) => {
                        ("inconsistent-demand", key, Some(loc))
                    }
                };
                json!({"kind":kind,"entry":self.entry(key)?,"location":loc.map(location)})
            }
            R::MissingOwner { loan, owner } => {
                diagnostic = json!({"loan":loan});
                let owner = owner
                    .map(|owner| {
                        self.owner(
                            row.function.ok_or("missing owner function context")?,
                            e::OwnerKey::from_owner(owner),
                        )
                    })
                    .transpose()?;
                json!({"kind":"missing-owner","owner":owner})
            }
            R::MissingInnerLoan { slot, depth } => {
                json!({"kind":"missing-inner-loan","slot":self.slot(*slot)?,"depth":depth})
            }
            R::MissingSlotKey(slot) => json!({"kind":"missing-slot-key","slot":self.slot(*slot)?}),
            R::MissingEntryFacts
            | R::DifferentEntryFacts
            | R::MissingContext
            | R::DuplicateContext
            | R::UnexpectedContext
            | R::MissingSourceEvent => json!({"kind":tag(&row.reason)}),
        };
        Ok((
            json!({"source":row.source.as_ref().map(source_key),"function":row.function.map(|f|self.function(f)).transpose()?,"location":row.location.map(location),"phase":row.phase.map(tag),"route":self.steps(&row.route)?,"reason":reason}),
            diagnostic,
        ))
    }

    fn review(&self, review: &rt::RetirementReview) -> Result<(Value, Value), String> {
        let mut diagnostics = Vec::new();
        let conflicts=review.conflicts.iter().map(|row|{
            let target=self.slot(row.target)?;
            if target!=row.target_key{return Err("retirement target canonical key mismatch".into());}
            let loan=row.loan.as_ref().map(|loan|{
                let owners=loan.owners.iter().map(|owner|self.owner(row.function,e::OwnerKey::from_owner(*owner))).collect::<Result<Vec<_>,_>>()?;
                let value=json!({"reservation":location(loan.reservation),"borrowed":place(&loan.borrowed),"owners":owners});
                diagnostics.push(json!({"source":source_key(&row.source),"function":self.function(row.function)?,"loan":loan.index,"loan_key":value}));
                Ok::<_,String>(value)
            }).transpose()?;
            Ok(json!({"function":self.function(row.function)?,"target":target,"source":source_key(&row.source),"phase":tag(row.phase),"location":location(row.location),"route":self.steps(&row.route)?,"loan":loan,"entry":row.entry.map(|e|self.entry(e)).transpose()?,"overlap":tag(row.overlap)}))
        }).collect::<Result<Vec<_>,String>>()?;
        let unresolved = review
            .unresolved
            .iter()
            .map(|row| {
                let (value, labels) = self.unresolved(row)?;
                if !labels.is_null() {
                    diagnostics.push(json!({"source":value,"labels":labels}));
                }
                Ok(value)
            })
            .collect::<Result<Vec<_>, String>>()?;
        let coverage=review.coverage.iter().map(|row|Ok(json!({"source":source_key(&row.source),"function":self.function(row.function)?,"location":location(row.location),"phase":tag(row.phase),"route":self.steps(&row.route)?,"disposition":tag(row.disposition)}))).collect::<Result<Vec<_>,String>>()?;
        let terminal = review
            .terminal
            .iter()
            .map(|(key, state)| json!({"source":source_key(key),"disposition":tag(state)}))
            .collect::<Vec<_>>();
        Ok((
            json!({"conflicts":conflicts,"unresolved":unresolved,"coverage":coverage,"ordinary_error_points":review.ordinary_error_points,"terminal":terminal}),
            json!(diagnostics),
        ))
    }
}

// A diagnostic number, a loan attribute, and a later valuation do not
// participate in a source occurrence's identity.
fn record_key(family: ExportFamily, fields: &BTreeMap<String, Value>) -> Result<String, String> {
    use ExportFamily as F;
    let selected: Vec<&str> = match family {
        F::Loans => vec!["function", "place", "location", "borrower"],
        F::OwnershipVersions => vec!["owner", "location"],
        F::OwnershipValues => vec!["scope"],
        F::SourceSelectors | F::SinkSelectors => vec!["role", "call"],
        F::ReallocVersions => vec!["function", "event", "outcome", "edge", "location", "local"],
        F::ReallocCases => vec!["event", "outcome"],
        F::RetirementRounds => vec!["round"],
        F::RetirementFinal | F::DemandEvidence | F::ProofEvidence => vec![],
        _ => fields.keys().map(String::as_str).collect(),
    };
    let identity = selected
        .into_iter()
        .map(|key| {
            fields
                .get(key)
                .cloned()
                .map(|value| (key, value))
                .ok_or_else(|| format!("missing identity field: {key}"))
        })
        .collect::<Result<BTreeMap<_, _>, String>>()?;
    Ok(format!(
        "{family:?}/{}",
        serde_json::to_string(&identity).map_err(|e| e.to_string())?
    ))
}

impl PortableExport {
    fn add(&mut self, family: ExportFamily, fields: Value, labels: Value) -> Result<(), String> {
        let Value::Object(fields) = fields else {
            return Err("portable row is not an object".into());
        };
        let fields = fields.into_iter().collect::<BTreeMap<_, _>>();
        let key = record_key(family, &fields)?;
        self.identities.insert(key.clone());
        if !labels.is_null() {
            self.diagnostics.push(DiagnosticRecord {
                family,
                source_key: key.clone(),
                labels: BTreeMap::from([("labels".into(), labels)]),
            });
        }
        let payload = self
            .families
            .get_mut(&family)
            .ok_or("unregistered export family")?;
        payload.records.push(PortableRecord {
            key,
            references: vec![],
            fields,
        });
        payload.source_rows += 1;
        Ok(())
    }
}

pub(crate) fn collect(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    export: &BoExport,
) -> Result<PortableExport, String> {
    use ExportFamily as F;
    let resolver = Resolver { program, slots };
    let required = |present: bool, name: &str| {
        if present {
            Ok(())
        } else {
            Err(format!("missing required capture: {name}"))
        }
    };
    required(export.source_events.is_some(), "source inventory")?;
    required(
        export.replay_source_events.is_some(),
        "replay source inventory",
    )?;
    required(export.entry_protection.is_some(), "entry protection")?;
    required(export.source_retirement.is_some(), "retirement final")?;
    required(export.version_owns.is_some(), "ownership values")?;
    required(export.comparisons.is_some(), "comparison ledger")?;
    required(export.qualifier_facts.is_some(), "qualifier facts")?;
    required(export.array_fields.is_some(), "array fields")?;
    required(export.demand_evidence.is_some(), "demand evidence")?;
    let mut out = PortableExport {
        schema: SCHEMA.into(),
        licensing_deferred: true,
        identities: BTreeSet::new(),
        scope_gaps: BTreeSet::from([
            ScopeGap::OwnershipOccurrenceConstructionNotRecorded,
            ScopeGap::OwnershipValuesAreLatestSuppliedValuation,
        ]),
        families: REQUIRED_FAMILIES
            .into_iter()
            .map(|family| {
                (
                    family,
                    PortableFamily {
                        availability: CaptureAvailability::Captured,
                        source_rows: 0,
                        records: vec![],
                    },
                )
            })
            .collect(),
        diagnostics: vec![],
    };
    // Index only actual registered slots, never reconstructed erased SlotIds.
    for (&function, universe) in &slots.fn_local_slots {
        for index in 0..universe.len() {
            out.identities.insert(resolver.slot(SlotRef::Local(
                function,
                super::slots::SlotId::from_usize(index),
            ))?);
        }
    }
    for index in 0..slots.field_slots.len() {
        out.identities
            .insert(resolver.slot(SlotRef::Field(super::slots::SlotId::from_usize(index)))?);
    }
    for row in &export.version_sites {
        out.add(F::OwnershipVersions,json!({"owner":resolver.local(row.fn_did,row.local.as_u32())?,"location":mir_location(row.location),"use_present":row.use_var.is_some(),"def_present":row.def_var.is_some(),"construction_correspondence":"not-recorded"}),json!({"use_var":row.use_var.map(|v|v.as_u32()),"def_var":row.def_var.map(|v|v.as_u32())}))?;
    }
    for (var, owns) in export.version_owns.as_ref().unwrap().iter_enumerated() {
        out.add(F::OwnershipValues,json!({"owns":owns,"scope":"latest-supplied-valuation","occurrence_correspondence":"not-recorded"}),json!({"var":var.as_u32()}))?;
    }
    for (family, rows) in [
        (F::SourceSelectors, &export.source_sites),
        (F::SinkSelectors, &export.sink_sites),
    ] {
        for row in rows {
            let call=row.call.as_ref().map(|call| -> Result<Value, String> {
                let function=resolver.function(call.fn_did)?;
                if function!=call.function_path{return Err("selector function path mismatch".into());}
                Ok(json!({"function":function,"location":mir_location(call.location),"callee":call.callee}))
            }).transpose()?;
            out.add(family,json!({"role":tag(row.role),"call":call,"operand_correspondence":"not-recorded","construction_correspondence":"not-recorded"}),json!({"var":row.var.as_u32()}))?;
        }
    }
    for row in &export.loans {
        out.add(F::Loans,json!({"function":resolver.function(row.key.fn_did)?,"place":place(&row.key.place),"location":mir_location(row.key.location),"borrower":resolver.borrower(row.key.fn_did,row.key.borrower)?,"kind":tag(row.kind),"class":tag(row.class),"invalid":row.invalid}),json!({"loan":row.run_local_handle}))?;
    }
    if let Some(rows) = &export.residual_conflicts {
        for row in rows {
            out.add(F::ResidualConflicts,json!({"function":resolver.function(row.fn_did)?,"issuer":row.issuer.map(|s|resolver.slot(s)).transpose()?,"requirers":row.requirers.iter().map(|s|resolver.slot(*s)).collect::<Result<Vec<_>,_>>()?}),Value::Null)?;
        }
    } else {
        out.families
            .get_mut(&F::ResidualConflicts)
            .unwrap()
            .availability = CaptureAvailability::NotRecorded {
            reason: "producer did not record an L2 residual certificate".into(),
        };
    }
    for row in &export.realloc_version_sites {
        out.add(F::ReallocVersions,json!({"function":resolver.function(row.fn_did)?,"event":realloc_key(&row.event),"outcome":tag(row.outcome),"edge":row.edge,"location":mir_location(row.location),"local":row.local.as_u32(),"use_present":row.use_var.is_some()}),json!({"use_var":row.use_var.map(|v|v.as_u32()),"def_var":row.def_var.as_u32()}))?;
    }
    for row in &export.realloc_cases {
        resolver.named_function(&row.event.function)?;
        out.add(F::ReallocCases,json!({"event":realloc_key(&row.event),"outcome":tag(row.case.outcome),"old":tag(row.case.old),"result":tag(row.case.result),"contents":tag(row.case.contents),"old_before_present":row.old_before.is_some(),"old_after_present":row.old_after.is_some(),"result_claim_present":row.result_claim.is_some()}),json!({"old_before":row.old_before.map(|v|v.as_u32()),"old_after":row.old_after.map(|v|v.as_u32()),"result_claim":row.result_claim.map(|v|v.as_u32())}))?;
    }
    for (family, inventory) in [
        (F::SourceInventory, export.source_events.as_ref().unwrap()),
        (
            F::ReplaySourceInventory,
            export.replay_source_events.as_ref().unwrap(),
        ),
    ] {
        for (key, row) in &inventory.retirements {
            if key != &row.key {
                return Err("source inventory event key mismatch".into());
            }
            resolver.named_function(&key.function)?;
            out.add(
                family,
                json!({"kind":"retirement","event":source_event(row)}),
                Value::Null,
            )?;
        }
        for row in &inventory.calls {
            resolver.named_function(&row.caller)?;
            resolver.named_function(&row.callee)?;
            out.add(
                family,
                json!({"kind":"route","route":source_route(row)}),
                Value::Null,
            )?;
        }
        for row in &inventory.reallocations {
            resolver.named_function(&row.key.function)?;
            out.add(
                family,
                json!({"kind":"realloc","site":realloc_site(row)}),
                Value::Null,
            )?;
        }
        for (&(function, loc), targets) in &inventory.call_targets {
            let mut known = targets
                .known
                .iter()
                .map(|did| program.tcx.def_path_str(*did))
                .collect::<Vec<_>>();
            known.sort();
            out.add(family,json!({"kind":"call-targets","function":resolver.function(function)?,"location":location(loc),"known":known,"unknown":targets.unknown}),Value::Null)?;
        }
    }
    let entry = export.entry_protection.as_ref().unwrap();
    for fact in entry
        .entries
        .iter()
        .cloned()
        .map(pe::EntryFact::Entry)
        .chain(
            entry
                .observations
                .iter()
                .cloned()
                .map(pe::EntryFact::Observation),
        )
        .chain(
            entry
                .binding_facts
                .iter()
                .cloned()
                .map(pe::EntryFact::Binding),
        )
    {
        out.add(F::EntryProtection, resolver.fact(&fact)?, Value::Null)?;
    }
    for row in &export.entry_accesses {
        out.add(F::EntryAccesses,json!({"function":resolver.function(row.function)?,"location":location(row.location),"phase":tag(row.phase),"place":place(&row.place),"extent":tag(row.extent),"mode":tag(row.mode),"cause":tag(row.cause)}),Value::Null)?;
    }
    for row in &export.entry_fact_witnesses {
        use pe::evidence::FactRule;
        let (rule, key) = match row.rule {
            FactRule::ParameterEntry(k) => ("parameter-entry", k),
            FactRule::WholeCallReachability(k) => ("whole-call-reachability", k),
            FactRule::FrameExit(k) => ("frame-exit", k),
            FactRule::LocatedInputBinding(k) => ("located-input-binding", k),
        };
        let predecessors=row.predecessors.iter().map(|p|Ok(json!({"function":resolver.function(p.function)?,"location":location(p.location),"phase":tag(p.phase),"moment":tag(p.moment)}))).collect::<Result<Vec<_>,String>>()?;
        out.add(F::EntryWitnesses,json!({"fact":resolver.fact(&row.fact)?,"rule":rule,"entry":resolver.entry(key)?,"predecessors":predecessors}),Value::Null)?;
    }
    let (value, labels) = resolver.review(export.source_retirement.as_ref().unwrap())?;
    out.add(F::RetirementFinal, value, labels)?;
    for (round, review) in export.retirement_rounds.iter().enumerate() {
        let (mut value, labels) = resolver.review(review)?;
        value["round"] = json!(round);
        out.add(F::RetirementRounds, value, labels)?;
    }
    let comparison = export.comparisons.as_ref().unwrap();
    out.add(
        F::Comparisons,
        json!({"kind":"disposition","disposition":tag(comparison.disposition)}),
        Value::Null,
    )?;
    for row in &comparison.sites {
        resolver.named_function(&row.function)?;
        out.add(F::Comparisons,json!({"kind":"site","function":row.function,"block":row.block,"statement":row.statement,"operator":row.operator,"operands":row.operands.iter().map(|o|json!({"place":o.place.as_ref().map(place),"slot":o.slot})).collect::<Vec<_>>()}),Value::Null)?;
    }
    for row in &comparison.guards {
        if !out.identities.contains(&row.slot) {
            return Err("unresolved comparison guard slot".into());
        }
        out.add(
            F::Comparisons,
            json!({"kind":"guard","slot":row.slot,"rule":tag(row.rule)}),
            Value::Null,
        )?;
    }
    for row in &export.qualifier_facts.as_ref().unwrap().rows {
        if !out.identities.contains(&row.slot) {
            return Err("unresolved qualifier slot".into());
        }
        out.add(
            F::QualifierFacts,
            serde_json::to_value(row).map_err(|e| e.to_string())?,
            Value::Null,
        )?;
    }
    for row in &export.array_fields.as_ref().unwrap().rows {
        for key in row
            .slot_keys
            .iter()
            .chain(&row.source_slots)
            .chain(&row.loaded_slots)
        {
            if !out.identities.contains(key) {
                return Err("unresolved array field slot".into());
            }
        }
        out.add(
            F::ArrayFields,
            serde_json::to_value(row).map_err(|e| e.to_string())?,
            Value::Null,
        )?;
    }
    let demand = export.demand_evidence.as_ref().unwrap().canonical_json()?;
    out.add(
        F::DemandEvidence,
        serde_json::from_str(&demand).map_err(|e| e.to_string())?,
        Value::Null,
    )?;
    let proof = super::proof_evidence::ProofEvidence::from_export(program.tcx, export);
    let proof = proof.canonical_json()?;
    out.add(
        F::ProofEvidence,
        serde_json::from_str(&proof).map_err(|e| e.to_string())?,
        Value::Null,
    )?;
    out.validate()?;
    Ok(out)
}

#[cfg(test)]
mod tests;
