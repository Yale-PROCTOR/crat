//! Complete-entry validation without retaining portable review bodies.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
    io::Read,
};

use serde::{
    Deserializer as _,
    de::{self, DeserializeOwned, DeserializeSeed, MapAccess, SeqAccess, Visitor},
};
use serde_json::Value;

use crate::analyses::borrow_ownership::{
    cache_contract::{CompleteEntry, SCHEMA, SemanticInputs, semantic_key},
    origin_evidence::{OriginAvailability, OriginEvidence, OriginMissing},
    portable_export::{self, CaptureAvailability, ExportFamily, REQUIRED_FAMILIES, ScopeGap},
    strict_json::{Discard, UniqueValue},
};

#[derive(Clone, Debug)]
pub(crate) struct Metadata {
    pub(crate) schema: String,
    pub(crate) key: String,
    pub(crate) inputs: SemanticInputs,
    pub(crate) functions: Vec<String>,
    pub(crate) universe: Vec<String>,
    pub(crate) model: BTreeMap<String, String>,
    pub(crate) baseline: BTreeMap<String, String>,
    pub(crate) receipt: String,
    pub(crate) origin: Value,
}

impl Metadata {
    pub(crate) fn validate_meta(&self) -> Result<(), String> {
        if self.schema != SCHEMA || self.key != semantic_key(&self.inputs)? {
            return Err("cache schema or semantic key mismatch".into());
        }
        let universe: BTreeSet<_> = self.universe.iter().cloned().collect();
        if universe.len() != self.universe.len()
            || universe.iter().any(String::is_empty)
            || self.model.keys().cloned().collect::<BTreeSet<_>>() != universe
            || self.baseline.keys().cloned().collect::<BTreeSet<_>>() != universe
            || self
                .model
                .values()
                .chain(self.baseline.values())
                .any(|kind| !matches!(kind.as_str(), "raw" | "ref" | "owning"))
        {
            return Err("incomplete or invalid model universe".into());
        }
        if !self.receipt.lines().any(|line| line == "status=ok")
            || !self.receipt.lines().any(|line| line == "data=true")
        {
            return Err("cache requires a complete accepted receipt".into());
        }
        let origin: OriginEvidence = serde_json::from_value(self.origin.clone())
            .map_err(|error| format!("required origin evidence: {error}"))?;
        let functions: BTreeSet<_> = self.functions.iter().cloned().collect();
        if functions.len() != self.functions.len()
            || functions.iter().any(String::is_empty)
            || origin.functions.len() != functions.len()
            || origin
                .functions
                .iter()
                .map(|function| function.function.clone())
                .collect::<BTreeSet<_>>()
                != functions
        {
            return Err("incomplete origin function universe".into());
        }
        for function in &origin.functions {
            let gaps = &function.ownership;
            if gaps.equations != OriginMissing::OwnershipEquationsNotExported
                || gaps.dynamic_epochs != OriginMissing::DynamicEpochNotRepresented
                || gaps.partner_free != OriginMissing::PartnerFreeCorrespondenceNotExported
                || gaps.conservation != OriginMissing::ConservationNotProved
            {
                return Err("ownership proof availability changed".into());
            }
            let mut signatures = BTreeSet::new();
            for slot in &function.signature_slots {
                if !signatures.insert(slot) {
                    return Err("duplicate signature evidence".into());
                }
                if let OriginAvailability::Present(key) = &slot.kind_slot
                    && !universe.contains(key)
                {
                    return Err("unresolved signature kind slot".into());
                }
            }
        }
        Ok(())
    }

    /// Hash a writer-owned canonical entry without decoding its portable history.
    /// Exact header/footer comparisons establish the exported section's bounds.
    pub(crate) fn canonical_file_hashes(
        &self,
        path: &std::path::Path,
    ) -> Result<crate::analyses::borrow_ownership::cache_contract::StreamHashes, String> {
        use std::io::{Read, Write};

        use crate::analyses::borrow_ownership::cache_contract::{
            HashWriter, StreamHashes, file_sha256,
        };
        self.validate_meta()?;
        struct Match<'a> {
            input: &'a mut std::io::BufReader<std::fs::File>,
            count: u64,
        }
        impl Write for Match<'_> {
            fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
                let mut buffer = [0u8; 8192];
                for chunk in bytes.chunks(buffer.len()) {
                    self.input.read_exact(&mut buffer[..chunk.len()])?;
                    if buffer[..chunk.len()] != *chunk {
                        return Err(std::io::Error::new(
                            std::io::ErrorKind::InvalidData,
                            "noncanonical cache header/footer",
                        ));
                    }
                }
                self.count += bytes.len() as u64;
                Ok(bytes.len())
            }

            fn flush(&mut self) -> std::io::Result<()> {
                Ok(())
            }
        }
        struct Count(u64);
        impl Write for Count {
            fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
                self.0 += bytes.len() as u64;
                Ok(bytes.len())
            }

            fn flush(&mut self) -> std::io::Result<()> {
                Ok(())
            }
        }
        let mut input =
            std::io::BufReader::new(std::fs::File::open(path).map_err(|e| e.to_string())?);
        let length = input.get_ref().metadata().map_err(|e| e.to_string())?.len();
        let mut functions = self.functions.clone();
        functions.sort();
        let mut universe = self.universe.clone();
        universe.sort();
        let prefix_length = {
            let mut output = Match {
                input: &mut input,
                count: 0,
            };
            macro_rules! field {
                ($prefix:literal,$value:expr) => {{
                    output.write_all($prefix).map_err(|e| e.to_string())?;
                    serde_json::to_writer(&mut output, $value).map_err(|e| e.to_string())?;
                }};
            }
            field!(b"{\"schema\":", &self.schema);
            field!(b",\"key\":", &self.key);
            field!(b",\"inputs\":", &self.inputs);
            field!(b",\"functions\":", &functions);
            field!(b",\"universe\":", &universe);
            field!(b",\"model\":", &self.model);
            field!(b",\"baseline\":", &self.baseline);
            field!(b",\"receipt\":", &self.receipt);
            output
                .write_all(b",\"exports\":")
                .map_err(|e| e.to_string())?;
            output.count
        };
        let mut suffix = Count(0);
        suffix
            .write_all(b",\"origin\":")
            .map_err(|e| e.to_string())?;
        serde_json::to_writer(&mut suffix, &self.origin).map_err(|e| e.to_string())?;
        suffix.write_all(b"}").map_err(|e| e.to_string())?;
        let exported = length
            .checked_sub(prefix_length)
            .and_then(|n| n.checked_sub(suffix.0))
            .ok_or("truncated canonical entry")?;
        let mut payload = HashWriter::new();
        serde_json::to_writer(&mut payload, &(&self.model, &self.baseline, &self.receipt))
            .map_err(|e| e.to_string())?;
        let mut exports = HashWriter::new();
        exports.write_all(b"[").map_err(|e| e.to_string())?;
        if std::io::copy(&mut input.by_ref().take(exported), &mut exports)
            .map_err(|e| e.to_string())?
            != exported
        {
            return Err("truncated exports".into());
        }
        exports.write_all(b",").map_err(|e| e.to_string())?;
        serde_json::to_writer(&mut exports, &self.origin).map_err(|e| e.to_string())?;
        exports.write_all(b"]").map_err(|e| e.to_string())?;
        {
            let mut output = Match {
                input: &mut input,
                count: 0,
            };
            output
                .write_all(b",\"origin\":")
                .map_err(|e| e.to_string())?;
            serde_json::to_writer(&mut output, &self.origin).map_err(|e| e.to_string())?;
            output.write_all(b"}").map_err(|e| e.to_string())?;
        }
        if input.read(&mut [0u8; 1]).map_err(|e| e.to_string())? != 0 {
            return Err("trailing canonical entry bytes".into());
        }
        Ok(StreamHashes {
            entry: file_sha256(path)?,
            payload: payload.finish(),
            exports: exports.finish(),
        })
    }
}

impl From<CompleteEntry> for Metadata {
    fn from(entry: CompleteEntry) -> Self {
        Self {
            schema: entry.schema,
            key: entry.key,
            inputs: entry.inputs,
            functions: entry.functions,
            universe: entry.universe,
            model: entry.model,
            baseline: entry.baseline,
            receipt: entry.receipt,
            origin: entry.origin,
        }
    }
}

/// Validate the complete entry while discarding large portable review bodies.
pub(crate) fn validate_reader<R: Read>(reader: R) -> Result<Metadata, String> {
    validate_reader_streaming(reader)
}

fn validate_reader_streaming<R: Read>(reader: R) -> Result<Metadata, String> {
    let mut deserializer = serde_json::Deserializer::from_reader(reader);
    let metadata = deserializer
        .deserialize_map(MetadataVisitor)
        .map_err(|error| error.to_string())?;
    deserializer.end().map_err(|error| error.to_string())?;
    metadata.validate_meta()?;
    Ok(metadata)
}

fn required<T, E: de::Error>(value: Option<T>, name: &'static str) -> Result<T, E> {
    value.ok_or_else(|| E::missing_field(name))
}

fn unique<E: de::Error>(seen: &mut BTreeSet<String>, key: &str) -> Result<(), E> {
    if !seen.insert(key.to_owned()) {
        return Err(E::custom(format!("duplicate JSON object key: {key:?}")));
    }
    Ok(())
}

fn next<'de, T: DeserializeOwned, A: MapAccess<'de>>(map: &mut A) -> Result<T, A::Error> {
    let value = map.next_value::<UniqueValue>()?;
    serde_json::from_value(value.0).map_err(de::Error::custom)
}

struct MetadataVisitor;
impl<'de> Visitor<'de> for MetadataVisitor {
    type Value = Metadata;

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("a complete cache entry")
    }

    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Metadata, A::Error> {
        let (mut schema, mut key, mut inputs, mut functions, mut universe) =
            (None, None, None, None, None);
        let (mut model, mut baseline, mut receipt, mut origin, mut exports) =
            (None, None, None, None, None);
        let mut seen = BTreeSet::new();
        while let Some(name) = map.next_key::<String>()? {
            unique(&mut seen, &name)?;
            match name.as_str() {
                "schema" => schema = Some(next(&mut map)?),
                "key" => key = Some(next(&mut map)?),
                "inputs" => inputs = Some(next(&mut map)?),
                "functions" => functions = Some(next(&mut map)?),
                "universe" => universe = Some(next(&mut map)?),
                "model" => model = Some(next(&mut map)?),
                "baseline" => baseline = Some(next(&mut map)?),
                "receipt" => receipt = Some(next(&mut map)?),
                "origin" => origin = Some(next(&mut map)?),
                "exports" => exports = Some(map.next_value_seed(Exports)?),
                _ => return Err(de::Error::custom(format!("unknown cache field: {name}"))),
            }
        }
        required(exports, "exports")?;
        Ok(Metadata {
            schema: required(schema, "schema")?,
            key: required(key, "key")?,
            inputs: required(inputs, "inputs")?,
            functions: required(functions, "functions")?,
            universe: required(universe, "universe")?,
            model: required(model, "model")?,
            baseline: required(baseline, "baseline")?,
            receipt: required(receipt, "receipt")?,
            origin: required(origin, "origin")?,
        })
    }
}

#[derive(Default)]
struct ExportSummary {
    referenced: BTreeSet<String>,
    diagnostic_families: BTreeSet<ExportFamily>,
}

struct Exports;
impl<'de> DeserializeSeed<'de> for Exports {
    type Value = ();

    fn deserialize<D: de::Deserializer<'de>>(self, d: D) -> Result<(), D::Error> {
        d.deserialize_map(self)
    }
}
impl<'de> Visitor<'de> for Exports {
    type Value = ();

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("portable exports")
    }

    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<(), A::Error> {
        let (mut schema, mut licensing, mut identities, mut gaps, mut families, mut diagnostics) =
            (None, None, None, None, None, None);
        let mut summary = ExportSummary::default();
        let mut seen = BTreeSet::new();
        while let Some(name) = map.next_key::<String>()? {
            unique(&mut seen, &name)?;
            match name.as_str() {
                "schema" => schema = Some(next::<String, _>(&mut map)?),
                "licensing_deferred" => licensing = Some(next::<bool, _>(&mut map)?),
                "identities" => identities = Some(next::<BTreeSet<String>, _>(&mut map)?),
                "scope_gaps" => gaps = Some(next::<BTreeSet<ScopeGap>, _>(&mut map)?),
                "families" => families = Some(map.next_value_seed(Families(&mut summary))?),
                "diagnostics" => {
                    diagnostics = Some(map.next_value_seed(Diagnostics(&mut summary))?)
                }
                _ => return Err(de::Error::custom(format!("unknown export field: {name}"))),
            }
        }
        if required(schema, "schema")? != portable_export::SCHEMA
            || !required(licensing, "licensing_deferred")?
        {
            return Err(de::Error::custom(
                "portable export schema/licensing mismatch",
            ));
        }
        let identities = required(identities, "identities")?;
        let gaps = required(gaps, "scope_gaps")?;
        let families = required(families, "families")?;
        required(diagnostics, "diagnostics")?;
        if !gaps.contains(&ScopeGap::OwnershipOccurrenceConstructionNotRecorded)
            || !gaps.contains(&ScopeGap::OwnershipValuesAreLatestSuppliedValuation)
        {
            return Err(de::Error::custom(
                "ownership occurrence/valuation scope gap erased",
            ));
        }
        if !summary.referenced.is_subset(&identities)
            || !summary.diagnostic_families.is_subset(&families)
        {
            return Err(de::Error::custom("unresolved portable identity"));
        }
        Ok(())
    }
}

struct Families<'a>(&'a mut ExportSummary);
impl<'de> DeserializeSeed<'de> for Families<'_> {
    type Value = BTreeSet<ExportFamily>;

    fn deserialize<D: de::Deserializer<'de>>(self, d: D) -> Result<Self::Value, D::Error> {
        d.deserialize_map(self)
    }
}
impl<'de> Visitor<'de> for Families<'_> {
    type Value = BTreeSet<ExportFamily>;

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("twenty export families")
    }

    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Self::Value, A::Error> {
        let mut seen = BTreeSet::new();
        let mut families = BTreeSet::new();
        while let Some(name) = map.next_key::<String>()? {
            unique(&mut seen, &name)?;
            let family = serde_json::from_value(Value::String(name)).map_err(de::Error::custom)?;
            families.insert(family);
            map.next_value_seed(Family {
                family,
                summary: self.0,
            })?;
        }
        if families != REQUIRED_FAMILIES.into_iter().collect() {
            return Err(de::Error::custom("missing or extra portable export family"));
        }
        Ok(families)
    }
}

struct Family<'a> {
    family: ExportFamily,
    summary: &'a mut ExportSummary,
}
impl<'de> DeserializeSeed<'de> for Family<'_> {
    type Value = ();

    fn deserialize<D: de::Deserializer<'de>>(self, d: D) -> Result<(), D::Error> {
        d.deserialize_map(self)
    }
}
impl<'de> Visitor<'de> for Family<'_> {
    type Value = ();

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("an export family")
    }

    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<(), A::Error> {
        let (mut availability, mut source_rows, mut records) = (None, None, None);
        let mut seen = BTreeSet::new();
        while let Some(name) = map.next_key::<String>()? {
            unique(&mut seen, &name)?;
            match name.as_str() {
                "availability" => availability = Some(next::<CaptureAvailability, _>(&mut map)?),
                "source_rows" => source_rows = Some(next::<usize, _>(&mut map)?),
                "records" => {
                    records = Some(map.next_value_seed(Records {
                        family: self.family,
                        summary: self.summary,
                    })?)
                }
                _ => return Err(de::Error::custom(format!("unknown family field: {name}"))),
            }
        }
        let source_rows = required(source_rows, "source_rows")?;
        let records = required(records, "records")?;
        match required(availability, "availability")? {
            CaptureAvailability::Captured => {}
            CaptureAvailability::NotRecorded { reason }
                if self.family == ExportFamily::ResidualConflicts
                    && !reason.is_empty()
                    && source_rows == 0
                    && records == 0 => {}
            _ => return Err(de::Error::custom("required capture unavailable")),
        }
        if source_rows != records {
            return Err(de::Error::custom("incomplete portable family"));
        }
        if matches!(
            self.family,
            ExportFamily::RetirementFinal
                | ExportFamily::DemandEvidence
                | ExportFamily::ProofEvidence
        ) && records != 1
        {
            return Err(de::Error::custom("missing singleton portable capture"));
        }
        Ok(())
    }
}

struct Records<'a> {
    family: ExportFamily,
    summary: &'a mut ExportSummary,
}
impl<'de> DeserializeSeed<'de> for Records<'_> {
    type Value = usize;

    fn deserialize<D: de::Deserializer<'de>>(self, d: D) -> Result<usize, D::Error> {
        d.deserialize_seq(self)
    }
}
impl<'de> Visitor<'de> for Records<'_> {
    type Value = usize;

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("export records")
    }

    fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<usize, A::Error> {
        let mut count = 0usize;
        while seq
            .next_element_seed(Record {
                family: self.family,
                summary: self.summary,
            })?
            .is_some()
        {
            count = count
                .checked_add(1)
                .ok_or_else(|| de::Error::custom("record count overflow"))?;
        }
        Ok(count)
    }
}

struct Record<'a> {
    family: ExportFamily,
    summary: &'a mut ExportSummary,
}
impl<'de> DeserializeSeed<'de> for Record<'_> {
    type Value = ();

    fn deserialize<D: de::Deserializer<'de>>(self, d: D) -> Result<(), D::Error> {
        d.deserialize_map(self)
    }
}
impl<'de> Visitor<'de> for Record<'_> {
    type Value = ();

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("an export record")
    }

    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<(), A::Error> {
        let (mut key, mut references, mut fields) = (None, None, None);
        let mut seen = BTreeSet::new();
        while let Some(name) = map.next_key::<String>()? {
            unique(&mut seen, &name)?;
            match name.as_str() {
                "key" => key = Some(next::<String, _>(&mut map)?),
                "references" => references = Some(next::<Vec<String>, _>(&mut map)?),
                "fields" => fields = Some(map.next_value_seed(Fields(self.family))?),
                _ => return Err(de::Error::custom(format!("unknown record field: {name}"))),
            }
        }
        let key = required(key, "key")?;
        let fields = required(fields, "fields")?;
        let expected = portable_export::stream::expected_key(self.family, &fields)
            .map_err(de::Error::custom)?;
        if key.is_empty() || key != expected {
            return Err(de::Error::custom("portable source identity mismatch"));
        }
        self.summary.referenced.insert(key);
        self.summary
            .referenced
            .extend(required(references, "references")?);
        Ok(())
    }
}

struct Fields(ExportFamily);
impl<'de> DeserializeSeed<'de> for Fields {
    type Value = BTreeMap<String, Value>;

    fn deserialize<D: de::Deserializer<'de>>(self, d: D) -> Result<Self::Value, D::Error> {
        d.deserialize_map(self)
    }
}
impl<'de> Visitor<'de> for Fields {
    type Value = BTreeMap<String, Value>;

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("record fields")
    }

    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<Self::Value, A::Error> {
        let sparse = matches!(
            self.0,
            ExportFamily::RetirementFinal
                | ExportFamily::RetirementRounds
                | ExportFamily::DemandEvidence
                | ExportFamily::ProofEvidence
        );
        let mut seen = BTreeSet::new();
        let mut fields = BTreeMap::new();
        while let Some(name) = map.next_key::<String>()? {
            unique(&mut seen, &name)?;
            if !sparse || (self.0 == ExportFamily::RetirementRounds && name == "round") {
                fields.insert(name, map.next_value::<UniqueValue>()?.0);
            } else {
                map.next_value::<Discard>()?;
            }
        }
        Ok(fields)
    }
}

struct Diagnostics<'a>(&'a mut ExportSummary);
impl<'de> DeserializeSeed<'de> for Diagnostics<'_> {
    type Value = ();

    fn deserialize<D: de::Deserializer<'de>>(self, d: D) -> Result<(), D::Error> {
        d.deserialize_seq(self)
    }
}
impl<'de> Visitor<'de> for Diagnostics<'_> {
    type Value = ();

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("export diagnostics")
    }

    fn visit_seq<A: SeqAccess<'de>>(self, mut seq: A) -> Result<(), A::Error> {
        while seq.next_element_seed(Diagnostic(self.0))?.is_some() {}
        Ok(())
    }
}

struct Diagnostic<'a>(&'a mut ExportSummary);
impl<'de> DeserializeSeed<'de> for Diagnostic<'_> {
    type Value = ();

    fn deserialize<D: de::Deserializer<'de>>(self, d: D) -> Result<(), D::Error> {
        d.deserialize_map(self)
    }
}
impl<'de> Visitor<'de> for Diagnostic<'_> {
    type Value = ();

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("a diagnostic record")
    }

    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<(), A::Error> {
        let (mut family, mut source_key, mut labels) = (None, None, None);
        let mut seen = BTreeSet::new();
        while let Some(name) = map.next_key::<String>()? {
            unique(&mut seen, &name)?;
            match name.as_str() {
                "family" => family = Some(next::<ExportFamily, _>(&mut map)?),
                "source_key" => source_key = Some(next::<String, _>(&mut map)?),
                "labels" => labels = Some(map.next_value_seed(DiscardObject)?),
                _ => {
                    return Err(de::Error::custom(format!(
                        "unknown diagnostic field: {name}"
                    )));
                }
            }
        }
        required(labels, "labels")?;
        self.0
            .diagnostic_families
            .insert(required(family, "family")?);
        self.0
            .referenced
            .insert(required(source_key, "source_key")?);
        Ok(())
    }
}

struct DiscardObject;
impl<'de> DeserializeSeed<'de> for DiscardObject {
    type Value = ();

    fn deserialize<D: de::Deserializer<'de>>(self, d: D) -> Result<(), D::Error> {
        d.deserialize_map(self)
    }
}
impl<'de> Visitor<'de> for DiscardObject {
    type Value = ();

    fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("diagnostic labels object")
    }

    fn visit_map<A: MapAccess<'de>>(self, mut map: A) -> Result<(), A::Error> {
        let mut seen = BTreeSet::new();
        while let Some(name) = map.next_key::<String>()? {
            unique(&mut seen, &name)?;
            map.next_value::<Discard>()?;
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "stream_tests.rs"]
mod tests;
