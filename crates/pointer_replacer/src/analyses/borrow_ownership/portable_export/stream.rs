//! Bounded temporary JSON graphs and on-disk canonical ordering.
//! The parent materializer remains the independent byte oracle.
use std::{
    cmp::Ordering,
    fs::File,
    io::{Seek, Write},
    os::unix::fs::FileExt,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering as AtomicOrdering},
};

use serde::Serialize;

use crate::analyses::borrow_ownership::portable_export::*;

const COPY_BUFFER: usize = 8192;
static NEXT: AtomicU64 = AtomicU64::new(0);
fn error(e: impl std::fmt::Display) -> String {
    e.to_string()
}
fn json(w: &mut impl Write, value: &impl Serialize) -> Result<(), String> {
    serde_json::to_writer(w, value).map_err(error)
}
fn raw(w: &mut impl Write, value: &[u8]) -> Result<(), String> {
    w.write_all(value).map_err(error)
}

struct OwnedFile {
    path: PathBuf,
    file: File,
}
impl OwnedFile {
    fn create(directory: &Path, kind: &str) -> Result<Self, String> {
        let path = directory.join(format!(
            ".portable-{}-{}-{kind}",
            std::process::id(),
            NEXT.fetch_add(1, AtomicOrdering::Relaxed)
        ));
        let file = File::options()
            .read(true)
            .write(true)
            .create_new(true)
            .open(&path)
            .map_err(error)?;
        Ok(Self { path, file })
    }
}
impl Drop for OwnedFile {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.path);
    }
}

pub(crate) struct ExportSpool {
    pub(crate) path: PathBuf,
    _wire: OwnedFile,
    typed: OwnedFile,
    #[cfg(test)]
    pub(super) peak_materialized_nodes: usize,
}
impl ExportSpool {
    pub(crate) fn write_portable_typed(&self, writer: &mut impl Write) -> Result<(), String> {
        copy_range(
            &self.typed.file,
            writer,
            Fragment {
                offset: 0,
                length: self.typed.file.metadata().map_err(error)?.len(),
            },
        )
    }
}
pub(crate) fn expected_key(
    family: ExportFamily,
    fields: &BTreeMap<String, Value>,
) -> Result<String, String> {
    crate::analyses::borrow_ownership::portable_export::record_key(family, fields)
}

#[derive(Default)]
struct Residency {
    #[cfg(test)]
    peak: usize,
}
impl Residency {
    fn observe(&mut self, values: &[&Value]) {
        #[cfg(test)]
        {
            fn nodes(value: &Value) -> usize {
                1 + match value {
                    Value::Array(values) => values.iter().map(nodes).sum(),
                    Value::Object(values) => values.values().map(nodes).sum(),
                    _ => 0,
                }
            }
            self.peak = self.peak.max(values.iter().map(|v| nodes(v)).sum());
        }
        #[cfg(not(test))]
        let _ = values;
    }
}
#[derive(Clone, Copy)]
struct Fragment {
    offset: u64,
    length: u64,
}
#[derive(Clone, Copy)]
struct Record {
    typed: Fragment,
    wire: Fragment,
}
struct Family {
    availability: CaptureAvailability,
    records: Vec<Record>,
}
struct StreamCollector {
    directory: PathBuf,
    fragments: OwnedFile,
    identities: BTreeSet<String>,
    families: BTreeMap<ExportFamily, Family>,
    diagnostics: Vec<Record>,
    residency: Residency,
}
fn copy_range(source: &File, target: &mut impl Write, range: Fragment) -> Result<(), String> {
    let mut buffer = [0; COPY_BUFFER];
    let mut position = 0;
    while position < range.length {
        let amount = (range.length - position).min(buffer.len() as u64) as usize;
        source
            .read_exact_at(&mut buffer[..amount], range.offset + position)
            .map_err(error)?;
        raw(target, &buffer[..amount])?;
        position += amount as u64;
    }
    Ok(())
}
fn compare(source: &File, a: Fragment, b: Fragment) -> Result<Ordering, String> {
    let mut left = [0; COPY_BUFFER];
    let mut right = [0; COPY_BUFFER];
    let mut offset = 0;
    while offset < a.length.min(b.length) {
        let amount = (a.length.min(b.length) - offset).min(COPY_BUFFER as u64) as usize;
        source
            .read_exact_at(&mut left[..amount], a.offset + offset)
            .map_err(error)?;
        source
            .read_exact_at(&mut right[..amount], b.offset + offset)
            .map_err(error)?;
        let order = left[..amount].cmp(&right[..amount]);
        if order != Ordering::Equal {
            return Ok(order);
        }
        offset += amount as u64;
    }
    Ok(a.length.cmp(&b.length))
}
fn sort_records(source: &File, records: &mut [Record]) -> Result<(), String> {
    let mut failure = None;
    records.sort_by(|a, b| match compare(source, a.typed, b.typed) {
        Ok(order) => order,
        Err(error) => {
            failure.get_or_insert(error);
            Ordering::Equal
        }
    });
    failure.map_or(Ok(()), Err)
}
impl StreamCollector {
    fn new(directory: &Path) -> Result<Self, String> {
        std::fs::create_dir_all(directory).map_err(error)?;
        Ok(Self {
            directory: directory.to_owned(),
            fragments: OwnedFile::create(directory, "fragments")?,
            identities: BTreeSet::new(),
            families: REQUIRED_FAMILIES
                .into_iter()
                .map(|f| {
                    (
                        f,
                        Family {
                            availability: CaptureAvailability::Captured,
                            records: Vec::new(),
                        },
                    )
                })
                .collect(),
            diagnostics: Vec::new(),
            residency: Residency::default(),
        })
    }

    fn append(
        &mut self,
        write: impl FnOnce(&mut std::io::BufWriter<&mut File>) -> Result<(), String>,
    ) -> Result<Fragment, String> {
        let offset = self.fragments.file.stream_position().map_err(error)?;
        {
            let mut writer =
                std::io::BufWriter::with_capacity(COPY_BUFFER, &mut self.fragments.file);
            write(&mut writer)?;
            writer.flush().map_err(error)?;
        }
        Ok(Fragment {
            offset,
            length: self.fragments.file.stream_position().map_err(error)? - offset,
        })
    }

    fn add(&mut self, family: ExportFamily, fields: Value, labels: Value) -> Result<(), String> {
        self.residency.observe(&[&fields, &labels]);
        let Value::Object(fields) = fields else {
            return Err("portable row is not an object".into());
        };
        let fields = fields.into_iter().collect::<BTreeMap<_, _>>();
        let key = expected_key(family, &fields)?;
        self.identities.insert(key.clone());
        let typed = self.append(|w| {
            raw(w, b"{\"key\":")?;
            json(w, &key)?;
            raw(w, b",\"references\":[],\"fields\":")?;
            json(w, &fields)?;
            raw(w, b"}")
        })?;
        let wire = self.append(|w| {
            raw(w, b"{\"fields\":")?;
            json(w, &fields)?;
            raw(w, b",\"key\":")?;
            json(w, &key)?;
            raw(w, b",\"references\":[]}")
        })?;
        self.families
            .get_mut(&family)
            .ok_or("unregistered export family")?
            .records
            .push(Record { typed, wire });
        if !labels.is_null() {
            let labels = self.append(|w| json(w, &labels))?;
            self.add_diagnostic(family, &key, labels)?;
        }
        Ok(())
    }

    fn add_diagnostic(
        &mut self,
        family: ExportFamily,
        key: &str,
        labels: Fragment,
    ) -> Result<(), String> {
        let source = self.fragments.file.try_clone().map_err(error)?;
        let typed = self.append(|w| {
            raw(w, b"{\"family\":")?;
            json(w, &family)?;
            raw(w, b",\"source_key\":")?;
            json(w, &key)?;
            raw(w, b",\"labels\":{\"labels\":")?;
            copy_range(&source, w, labels)?;
            raw(w, b"}}")
        })?;
        let wire = self.append(|w| {
            raw(w, b"{\"family\":")?;
            json(w, &family)?;
            raw(w, b",\"labels\":{\"labels\":")?;
            copy_range(&source, w, labels)?;
            raw(w, b"},\"source_key\":")?;
            json(w, &key)?;
            raw(w, b"}")
        })?;
        self.diagnostics.push(Record { typed, wire });
        Ok(())
    }

    fn add_review(
        &mut self,
        resolver: &Resolver<'_, '_>,
        review: &rt::RetirementReview,
        round: Option<usize>,
    ) -> Result<(), String> {
        let family = if round.is_some() {
            ExportFamily::RetirementRounds
        } else {
            ExportFamily::RetirementFinal
        };
        let fields = round
            .map(|r| BTreeMap::from([("round".into(), json!(r))]))
            .unwrap_or_default();
        let key = expected_key(family, &fields)?;
        self.identities.insert(key.clone());
        let offset = self.fragments.file.stream_position().map_err(error)?;
        {
            let mut writer =
                std::io::BufWriter::with_capacity(COPY_BUFFER, &mut self.fragments.file);
            write_review_fields(&mut writer, resolver, review, round, &mut self.residency)?;
            writer.flush().map_err(error)?;
        }
        let fields = Fragment {
            offset,
            length: self.fragments.file.stream_position().map_err(error)? - offset,
        };
        let source = self.fragments.file.try_clone().map_err(error)?;
        let typed = self.append(|w| {
            raw(w, b"{\"key\":")?;
            json(w, &key)?;
            raw(w, b",\"references\":[],\"fields\":")?;
            copy_range(&source, w, fields)?;
            raw(w, b"}")
        })?;
        let wire = self.append(|w| {
            raw(w, b"{\"fields\":")?;
            copy_range(&source, w, fields)?;
            raw(w, b",\"key\":")?;
            json(w, &key)?;
            raw(w, b",\"references\":[]}")
        })?;
        self.families
            .get_mut(&family)
            .unwrap()
            .records
            .push(Record { typed, wire });
        let offset = self.fragments.file.stream_position().map_err(error)?;
        {
            let mut writer =
                std::io::BufWriter::with_capacity(COPY_BUFFER, &mut self.fragments.file);
            write_review_labels(&mut writer, resolver, review, &mut self.residency)?;
            writer.flush().map_err(error)?;
        }
        let labels = Fragment {
            offset,
            length: self.fragments.file.stream_position().map_err(error)? - offset,
        };
        self.add_diagnostic(family, &key, labels)
    }

    fn finish(mut self) -> Result<ExportSpool, String> {
        for family in [
            ExportFamily::RetirementFinal,
            ExportFamily::DemandEvidence,
            ExportFamily::ProofEvidence,
        ] {
            if self.families[&family].records.len() != 1 {
                return Err(format!("missing singleton portable capture: {family:?}"));
            }
        }
        for family in self.families.values_mut() {
            sort_records(&self.fragments.file, &mut family.records)?;
        }
        sort_records(&self.fragments.file, &mut self.diagnostics)?;
        let mut typed = OwnedFile::create(&self.directory, "typed.json")?;
        let mut wire = OwnedFile::create(&self.directory, "wire.json")?;
        {
            let mut writer = std::io::BufWriter::with_capacity(COPY_BUFFER, &mut typed.file);
            self.write_packet(&mut writer, false)?;
            writer.flush().map_err(error)?;
        }
        {
            let mut writer = std::io::BufWriter::with_capacity(COPY_BUFFER, &mut wire.file);
            self.write_packet(&mut writer, true)?;
            writer.flush().map_err(error)?;
        }
        Ok(ExportSpool {
            path: wire.path.clone(),
            _wire: wire,
            typed,
            #[cfg(test)]
            peak_materialized_nodes: self.residency.peak,
        })
    }

    fn write_records(
        &self,
        w: &mut impl Write,
        records: &[Record],
        wire: bool,
    ) -> Result<(), String> {
        raw(w, b"[")?;
        for (index, record) in records.iter().enumerate() {
            if index > 0 {
                raw(w, b",")?;
            }
            copy_range(
                &self.fragments.file,
                w,
                if wire { record.wire } else { record.typed },
            )?;
        }
        raw(w, b"]")
    }

    fn write_families(&self, w: &mut impl Write, wire: bool) -> Result<(), String> {
        let mut families: Vec<_> = self.families.iter().collect();
        if wire {
            families.sort_by_cached_key(|(family, _)| {
                serde_json::to_string(family).expect("family name")
            });
        }
        raw(w, b"{")?;
        for (index, (name, family)) in families.into_iter().enumerate() {
            if index > 0 {
                raw(w, b",")?;
            }
            json(w, name)?;
            raw(w, b":{\"availability\":")?;
            if wire {
                json(
                    w,
                    &serde_json::to_value(&family.availability).map_err(error)?,
                )?;
            } else {
                json(w, &family.availability)?;
            }
            if !wire {
                raw(w, b",\"source_rows\":")?;
                json(w, &family.records.len())?;
            }
            raw(w, b",\"records\":")?;
            self.write_records(w, &family.records, wire)?;
            if wire {
                raw(w, b",\"source_rows\":")?;
                json(w, &family.records.len())?;
            }
            raw(w, b"}")?;
        }
        raw(w, b"}")
    }

    fn write_packet(&self, w: &mut impl Write, wire: bool) -> Result<(), String> {
        let gaps = BTreeSet::from([
            ScopeGap::OwnershipOccurrenceConstructionNotRecorded,
            ScopeGap::OwnershipValuesAreLatestSuppliedValuation,
        ]);
        if wire {
            raw(w, b"{\"diagnostics\":")?;
            self.write_records(w, &self.diagnostics, true)?;
            raw(w, b",\"families\":")?;
            self.write_families(w, true)?;
            raw(w, b",\"identities\":")?;
            json(w, &self.identities)?;
            raw(w, b",\"licensing_deferred\":true,\"schema\":")?;
            json(w, &SCHEMA)?;
            raw(w, b",\"scope_gaps\":")?;
            json(w, &gaps)?;
        } else {
            raw(w, b"{\"schema\":")?;
            json(w, &SCHEMA)?;
            raw(w, b",\"licensing_deferred\":true,\"identities\":")?;
            json(w, &self.identities)?;
            raw(w, b",\"scope_gaps\":")?;
            json(w, &gaps)?;
            raw(w, b",\"families\":")?;
            self.write_families(w, false)?;
            raw(w, b",\"diagnostics\":")?;
            self.write_records(w, &self.diagnostics, false)?;
        }
        raw(w, b"}")
    }
}
fn values<T>(
    w: &mut impl Write,
    rows: impl IntoIterator<Item = T>,
    mut convert: impl FnMut(T) -> Result<Value, String>,
    residency: &mut Residency,
) -> Result<(), String> {
    raw(w, b"[")?;
    for (index, row) in rows.into_iter().enumerate() {
        if index > 0 {
            raw(w, b",")?;
        }
        let value = convert(row)?;
        residency.observe(&[&value]);
        json(w, &value)?;
    }
    raw(w, b"]")
}
fn loan_value(
    resolver: &Resolver<'_, '_>,
    row: &rt::RetirementConflict,
) -> Result<Option<Value>, String> {
    row.loan.as_ref().map(|loan| {
        let owners=loan.owners.iter().map(|owner|resolver.owner(row.function,e::OwnerKey::from_owner(*owner))).collect::<Result<Vec<_>,_>>()?;
        Ok(json!({"reservation":location(loan.reservation),"borrowed":place(&loan.borrowed),"owners":owners}))
    }).transpose()
}
fn write_review_fields(
    w: &mut impl Write,
    r: &Resolver<'_, '_>,
    review: &rt::RetirementReview,
    round: Option<usize>,
    residency: &mut Residency,
) -> Result<(), String> {
    raw(w, b"{\"conflicts\":")?;
    values(
        w,
        &review.conflicts,
        |row| {
            let target = r.slot(row.target)?;
            if target != row.target_key {
                return Err("retirement target canonical key mismatch".into());
            }
            Ok(
                json!({"function":r.function(row.function)?,"target":target,"source":source_key(&row.source),"phase":tag(row.phase),"location":location(row.location),"route":r.steps(&row.route)?,"loan":loan_value(r,row)?,"entry":row.entry.map(|e|r.entry(e)).transpose()?,"overlap":tag(row.overlap)}),
            )
        },
        residency,
    )?;
    raw(w, b",\"coverage\":")?;
    values(
        w,
        &review.coverage,
        |row| {
            Ok(
                json!({"source":source_key(&row.source),"function":r.function(row.function)?,"location":location(row.location),"phase":tag(row.phase),"route":r.steps(&row.route)?,"disposition":tag(row.disposition),"receipt":(row.disposition==rt::CoverageDisposition::IrrelevantNoSafeHolder).then_some("retirement:irrelevant-no-safe-holder")}),
            )
        },
        residency,
    )?;
    raw(w, b",\"demotions\":")?;
    values(
        w,
        &review.demotions,
        |row| {
            Ok(
                json!({"source":source_key(&row.source),"function":r.function(row.function)?,"location":location(row.location),"phase":tag(row.phase),"route":r.steps(&row.route)?,"holder":r.slot(row.holder)?,"receipt":row.reason.label(),"chain":row.chain.iter().map(|s|r.slot(*s)).collect::<Result<Vec<_>,_>>()?}),
            )
        },
        residency,
    )?;
    raw(w, b",\"ordinary_error_points\":")?;
    json(w, &review.ordinary_error_points)?;
    if let Some(round) = round {
        raw(w, b",\"round\":")?;
        json(w, &round)?;
    }
    raw(w, b",\"terminal\":")?;
    values(
        w,
        &review.terminal,
        |(key, state)| {
            Ok(
                json!({"source":source_key(key),"disposition":tag(state),"receipt":(*state==rt::EventDisposition::CheckedWithoutConflict).then_some("retirement:checked-without-conflict")}),
            )
        },
        residency,
    )?;
    raw(w, b",\"unresolved\":")?;
    values(
        w,
        &review.unresolved,
        |row| r.unresolved(row).map(|(value, _)| value),
        residency,
    )?;
    raw(w, b"}")
}
fn write_review_labels(
    w: &mut impl Write,
    r: &Resolver<'_, '_>,
    review: &rt::RetirementReview,
    residency: &mut Residency,
) -> Result<(), String> {
    raw(w, b"[")?;
    let mut comma = false;
    for row in &review.conflicts {
        if let Some(loan) = &row.loan {
            let value = json!({"source":source_key(&row.source),"function":r.function(row.function)?,"loan":loan.index,"loan_key":loan_value(r,row)?});
            residency.observe(&[&value]);
            if comma {
                raw(w, b",")?;
            }
            comma = true;
            json(w, &value)?;
        }
    }
    for row in &review.unresolved {
        let (value, labels) = r.unresolved(row)?;
        if !labels.is_null() {
            let value = json!({"source":value,"labels":labels});
            residency.observe(&[&value]);
            if comma {
                raw(w, b",")?;
            }
            comma = true;
            json(w, &value)?;
        }
    }
    raw(w, b"]")
}

pub(crate) fn collect_to_path(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    export: &BoExport,
    directory: &Path,
) -> Result<ExportSpool, String> {
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
    let mut out = StreamCollector::new(directory)?;
    // Index only actual registered slots, never reconstructed erased SlotIds.
    for (&function, universe) in &slots.fn_local_slots {
        for index in 0..universe.len() {
            out.identities.insert(resolver.slot(SlotRef::Local(
                function,
                crate::analyses::borrow_ownership::slots::SlotId::from_usize(index),
            ))?);
        }
    }
    for index in 0..slots.field_slots.len() {
        out.identities.insert(resolver.slot(SlotRef::Field(
            crate::analyses::borrow_ownership::slots::SlotId::from_usize(index),
        ))?);
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
    for row in &export.realloc_coverage_holds {
        out.add(F::ReallocCases,json!({"event":realloc_key(&row.site),"kind":"coverage-hold","receipt":"realloc-ssa-coverage:hold-raw","reason":row.reason.label(),"slots":row.slots.iter().map(|slot|resolver.slot(*slot)).collect::<Result<Vec<_>,_>>()?}),Value::Null)?;
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
    out.add_review(&resolver, export.source_retirement.as_ref().unwrap(), None)?;
    for (round, review) in export.retirement_rounds.iter().enumerate() {
        out.add_review(&resolver, review, Some(round))?;
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
    let proof = crate::analyses::borrow_ownership::proof_evidence::ProofEvidence::from_export(
        program.tcx,
        export,
    );
    let proof = proof.canonical_json()?;
    out.add(
        F::ProofEvidence,
        serde_json::from_str(&proof).map_err(|e| e.to_string())?,
        Value::Null,
    )?;
    out.finish()
}

#[cfg(test)]
mod fragment_tests {
    use crate::analyses::borrow_ownership::portable_export::stream::*;
    #[test]
    fn r281_w04_fragment_order_reads_past_buffer_and_rejects_truncation() {
        let mut file = OwnedFile::create(&std::env::temp_dir(), "sort-fault").unwrap();
        let prefix = vec![b'a'; COPY_BUFFER + 7];
        file.file.write_all(&prefix).unwrap();
        file.file.write_all(b"z").unwrap();
        let length = prefix.len() as u64 + 1;
        file.file.write_all(&prefix).unwrap();
        file.file.write_all(b"b").unwrap();
        let a = Fragment { offset: 0, length };
        let b = Fragment {
            offset: length,
            length,
        };
        assert_eq!(compare(&file.file, a, b).unwrap(), Ordering::Greater);
        file.file.set_len(length + 1).unwrap();
        assert!(
            compare(&file.file, a, b).is_err(),
            "short fragment cannot sort as equal"
        );
    }
}
