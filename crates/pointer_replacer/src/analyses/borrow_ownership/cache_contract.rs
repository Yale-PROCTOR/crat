//! Era5a complete-entry and portable semantic identity contract.
use std::{
    collections::BTreeMap,
    path::{Path, PathBuf},
};

use serde::{Deserialize, Serialize};
pub(crate) const SCHEMA: &str = "era5a-model-cache-v1";
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct SemanticInputs {
    pub(crate) program: String,
    pub(crate) files: BTreeMap<String, String>,
    pub(crate) analysis: String,
    pub(crate) toolchain: String,
    pub(crate) dependencies: String,
    pub(crate) configuration: String,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct CompleteEntry {
    pub(crate) schema: String,
    pub(crate) key: String,
    pub(crate) inputs: SemanticInputs,
    pub(crate) functions: Vec<String>,
    pub(crate) universe: Vec<String>,
    pub(crate) model: BTreeMap<String, String>,
    pub(crate) baseline: BTreeMap<String, String>,
    pub(crate) receipt: String,
    pub(crate) exports: serde_json::Value,
    pub(crate) origin: serde_json::Value,
}
fn digest(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|b| b.is_ascii_hexdigit())
}
fn logical(value: &str) -> bool {
    !value.is_empty()
        && !value.starts_with('/')
        && !value.contains('\\')
        && value
            .split('/')
            .all(|part| !matches!(part, "" | "." | ".."))
}
pub(crate) fn semantic_key(inputs: &SemanticInputs) -> Result<String, String> {
    use sha2::{Digest, Sha256};
    if inputs.program.is_empty()
        || inputs.files.is_empty()
        || inputs.files.iter().any(|(p, h)| !logical(p) || !digest(h))
        || [
            &inputs.analysis,
            &inputs.toolchain,
            &inputs.dependencies,
            &inputs.configuration,
        ]
        .iter()
        .any(|h| !digest(h))
    {
        return Err("missing or noncanonical semantic input".into());
    }
    let bytes = serde_json::to_vec(inputs).map_err(|e| e.to_string())?;
    let mut hash = Sha256::new();
    hash.update(SCHEMA.as_bytes());
    hash.update([0]);
    hash.update(bytes);
    Ok(format!("{:x}", hash.finalize()))
}
pub(crate) fn logical_files(
    root: &Path,
    files: &[(PathBuf, String)],
) -> Result<BTreeMap<String, String>, String> {
    use std::path::Component;
    fn normalize(path: &Path) -> Result<PathBuf, String> {
        let mut out = PathBuf::new();
        for part in path.components() {
            match part {
                Component::CurDir => {}
                Component::ParentDir => {
                    if !out.pop() {
                        return Err("path escapes root".into());
                    }
                }
                other => out.push(other.as_os_str()),
            }
        }
        Ok(out)
    }
    let root = normalize(root)?;
    if !root.is_absolute() {
        return Err("source manifest root must be absolute".into());
    }
    let mut out = BTreeMap::new();
    for (path, hash) in files {
        let path = normalize(&if path.is_absolute() {
            path.clone()
        } else {
            root.join(path)
        })?;
        let relative = path
            .strip_prefix(&root)
            .map_err(|_| "source outside manifest root")?;
        let relative = relative
            .to_str()
            .ok_or("non-UTF8 logical source path")?
            .to_owned();
        if !logical(&relative) || !digest(hash) {
            return Err("invalid logical source input".into());
        }
        if out.insert(relative, hash.clone()).is_some() {
            return Err("duplicate logical source input".into());
        }
    }
    if out.is_empty() {
        return Err("missing source inputs".into());
    }
    Ok(out)
}
impl CompleteEntry {
    pub(crate) fn validate(&self) -> Result<(), String> {
        use std::collections::BTreeSet;
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
                .any(|k| !matches!(k.as_str(), "raw" | "ref" | "owning"))
        {
            return Err("incomplete or invalid model universe".into());
        }
        if !self.receipt.lines().any(|l| l == "status=ok")
            || !self.receipt.lines().any(|l| l == "data=true")
        {
            return Err("cache requires a complete accepted receipt".into());
        }
        let exports: super::portable_export::PortableExport =
            serde_json::from_value(self.exports.clone())
                .map_err(|e| format!("required exports: {e}"))?;
        exports.validate()?;
        let origin: super::origin_evidence::OriginEvidence =
            serde_json::from_value(self.origin.clone())
                .map_err(|e| format!("required origin evidence: {e}"))?;
        let functions: BTreeSet<_> = self.functions.iter().cloned().collect();
        if functions.len() != self.functions.len()
            || functions.iter().any(String::is_empty)
            || origin.functions.len() != functions.len()
            || origin
                .functions
                .iter()
                .map(|f| f.function.clone())
                .collect::<BTreeSet<_>>()
                != functions
        {
            return Err("incomplete origin function universe".into());
        }
        for function in &origin.functions {
            use super::origin_evidence::{OriginAvailability, OriginMissing};
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

    pub(crate) fn canonical_json(&self) -> Result<Vec<u8>, String> {
        self.validate()?;
        let mut value = self.clone();
        value.functions.sort();
        value.universe.sort();
        serde_json::to_vec(&value).map_err(|e| e.to_string())
    }
}
pub(crate) fn decode(bytes: &[u8]) -> Result<CompleteEntry, String> {
    let value = super::strict_json::parse(bytes)?;
    let entry: CompleteEntry = serde_json::from_value(value).map_err(|e| e.to_string())?;
    entry.validate()?;
    Ok(entry)
}

pub(crate) fn publish(directory: &Path, entry: &CompleteEntry) -> Result<PathBuf, String> {
    use std::{
        io::Write,
        sync::atomic::{AtomicU64, Ordering},
    };
    static NEXT: AtomicU64 = AtomicU64::new(0);
    let bytes = entry.canonical_json()?;
    std::fs::create_dir_all(directory).map_err(|e| e.to_string())?;
    let destination = directory.join(format!("{}.json", entry.key));
    if destination.exists() {
        return if std::fs::read(&destination).map_err(|e| e.to_string())? == bytes {
            Ok(destination)
        } else {
            Err("completed semantic address already has a different body".into())
        };
    }
    let temporary = directory.join(format!(
        ".{}.{}-{}.staged",
        entry.key,
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    struct Remove(PathBuf);
    impl Drop for Remove {
        fn drop(&mut self) {
            let _ = std::fs::remove_file(&self.0);
        }
    }
    let _remove = Remove(temporary.clone());
    let mut file = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&temporary)
        .map_err(|e| e.to_string())?;
    file.write_all(&bytes).map_err(|e| e.to_string())?;
    file.sync_all().map_err(|e| e.to_string())?;
    let staged = std::fs::read(&temporary).map_err(|e| e.to_string())?;
    let _decoded = decode(&staged)?;
    if staged != bytes {
        return Err("staged complete body changed".into());
    }
    // Linking a complete same-directory file publishes atomically and cannot
    // overwrite a concurrent writer's completed content address.
    match std::fs::hard_link(&temporary, &destination) {
        Ok(()) => {}
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
            if std::fs::read(&destination).map_err(|e| e.to_string())? != bytes {
                return Err("concurrent semantic-address collision".into());
            }
        }
        Err(error) => return Err(error.to_string()),
    }
    std::fs::File::open(directory)
        .and_then(|file| file.sync_all())
        .map_err(|e| e.to_string())?;
    Ok(destination)
}

/// A validated canonical entry kept on disk. Cloning the prepared cache shares
/// this handle; it never duplicates the portable history's JSON tree.
pub(crate) struct StreamedEntry {
    pub(crate) path: PathBuf,
    pub(crate) metadata: stream::Metadata,
    pub(crate) hashes: Option<StreamHashes>,
    remove_on_drop: bool,
}
#[derive(Clone, Debug)]
pub(crate) struct StreamHashes {
    pub(crate) entry: String,
    pub(crate) payload: String,
    pub(crate) exports: String,
}
impl Drop for StreamedEntry {
    fn drop(&mut self) {
        if self.remove_on_drop {
            let _ = std::fs::remove_file(&self.path);
        }
    }
}

struct HashWriter(sha2::Sha256);
impl HashWriter {
    fn new() -> Self {
        use sha2::Digest;
        Self(sha2::Sha256::new())
    }

    fn finish(self) -> String {
        use sha2::Digest;
        format!("{:x}", self.0.finalize())
    }
}
impl std::io::Write for HashWriter {
    fn write(&mut self, bytes: &[u8]) -> std::io::Result<usize> {
        use sha2::Digest;
        self.0.update(bytes);
        Ok(bytes.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

pub(crate) fn file_sha256(path: &Path) -> Result<String, String> {
    let mut input = std::io::BufReader::new(std::fs::File::open(path).map_err(|e| e.to_string())?);
    let mut output = HashWriter::new();
    std::io::copy(&mut input, &mut output).map_err(|e| e.to_string())?;
    Ok(output.finish())
}

pub(crate) fn validate_file(path: &Path) -> Result<stream::Metadata, String> {
    let input = std::io::BufReader::new(std::fs::File::open(path).map_err(|e| e.to_string())?);
    stream::validate_reader(input)
}

pub(crate) fn equal_files(left: &Path, right: &Path) -> Result<bool, String> {
    use std::io::Read;
    let mut left = std::fs::File::open(left).map_err(|e| e.to_string())?;
    let mut right = std::fs::File::open(right).map_err(|e| e.to_string())?;
    if left.metadata().map_err(|e| e.to_string())?.len()
        != right.metadata().map_err(|e| e.to_string())?.len()
    {
        return Ok(false);
    }
    let mut a = [0u8; 64 * 1024];
    let mut b = [0u8; 64 * 1024];
    loop {
        let count = left.read(&mut a).map_err(|e| e.to_string())?;
        if count == 0 {
            return Ok(true);
        }
        right
            .read_exact(&mut b[..count])
            .map_err(|e| e.to_string())?;
        if a[..count] != b[..count] {
            return Ok(false);
        }
    }
}

/// Exports must come from the canonical Value-order spool, not the typed
/// PortableExport-order proof file. The full validator is run on staged bytes.
pub(crate) fn stage_streamed(
    directory: &Path,
    metadata: &stream::Metadata,
    exports: &Path,
) -> Result<StreamedEntry, String> {
    use std::{
        io::{Read, Seek, SeekFrom, Write},
        sync::atomic::{AtomicU64, Ordering},
    };
    static NEXT_STREAM: AtomicU64 = AtomicU64::new(0);
    metadata.validate_meta()?;
    std::fs::create_dir_all(directory).map_err(|e| e.to_string())?;
    let path = directory.join(format!(
        ".{}.{}-{}.streamed",
        metadata.key,
        std::process::id(),
        NEXT_STREAM.fetch_add(1, Ordering::Relaxed),
    ));
    let file = std::fs::OpenOptions::new()
        .create_new(true)
        .write(true)
        .open(&path)
        .map_err(|e| e.to_string())?;
    let mut staged = StreamedEntry {
        path,
        metadata: metadata.clone(),
        hashes: None,
        remove_on_drop: true,
    };
    staged.metadata.functions.sort();
    staged.metadata.universe.sort();
    let meta = &staged.metadata;
    let mut writer = std::io::BufWriter::new(file);
    macro_rules! field {
        ($prefix:literal, $value:expr) => {{
            writer.write_all($prefix).map_err(|e| e.to_string())?;
            serde_json::to_writer(&mut writer, $value).map_err(|e| e.to_string())?;
        }};
    }
    field!(b"{\"schema\":", &meta.schema);
    field!(b",\"key\":", &meta.key);
    field!(b",\"inputs\":", &meta.inputs);
    field!(b",\"functions\":", &meta.functions);
    field!(b",\"universe\":", &meta.universe);
    field!(b",\"model\":", &meta.model);
    field!(b",\"baseline\":", &meta.baseline);
    field!(b",\"receipt\":", &meta.receipt);
    writer
        .write_all(b",\"exports\":")
        .map_err(|e| e.to_string())?;
    let export_start = writer.stream_position().map_err(|e| e.to_string())?;
    let mut export_input =
        std::io::BufReader::new(std::fs::File::open(exports).map_err(|e| e.to_string())?);
    let export_length = std::io::copy(&mut export_input, &mut writer).map_err(|e| e.to_string())?;
    field!(b",\"origin\":", &meta.origin);
    writer.write_all(b"}").map_err(|e| e.to_string())?;
    writer.flush().map_err(|e| e.to_string())?;
    writer.get_ref().sync_all().map_err(|e| e.to_string())?;
    drop(writer);
    let validated = validate_file(&staged.path)?;
    if validated.inputs != meta.inputs || validated.key != meta.key {
        return Err("staged stream semantic identity changed".into());
    }
    let mut payload = HashWriter::new();
    serde_json::to_writer(&mut payload, &(&meta.model, &meta.baseline, &meta.receipt))
        .map_err(|e| e.to_string())?;
    let mut export_hash = HashWriter::new();
    export_hash.write_all(b"[").map_err(|e| e.to_string())?;
    let mut input = std::fs::File::open(&staged.path).map_err(|e| e.to_string())?;
    input
        .seek(SeekFrom::Start(export_start))
        .map_err(|e| e.to_string())?;
    std::io::copy(&mut input.take(export_length), &mut export_hash).map_err(|e| e.to_string())?;
    export_hash.write_all(b",").map_err(|e| e.to_string())?;
    serde_json::to_writer(&mut export_hash, &meta.origin).map_err(|e| e.to_string())?;
    export_hash.write_all(b"]").map_err(|e| e.to_string())?;
    staged.hashes = Some(StreamHashes {
        entry: file_sha256(&staged.path)?,
        payload: payload.finish(),
        exports: export_hash.finish(),
    });
    Ok(staged)
}

pub(crate) fn existing_streamed(path: PathBuf, metadata: stream::Metadata) -> StreamedEntry {
    StreamedEntry {
        path,
        metadata,
        hashes: None,
        remove_on_drop: false,
    }
}

pub(crate) fn publish_streamed(directory: &Path, entry: &StreamedEntry) -> Result<PathBuf, String> {
    std::fs::create_dir_all(directory).map_err(|e| e.to_string())?;
    let checked = validate_file(&entry.path)?;
    if checked.key != entry.metadata.key || checked.inputs != entry.metadata.inputs {
        return Err("staged stream metadata changed before publication".into());
    }
    if let Some(hashes) = &entry.hashes {
        if file_sha256(&entry.path)? != hashes.entry {
            return Err("staged stream bytes changed before publication".into());
        }
    }
    let destination = directory.join(format!("{}.json", entry.metadata.key));
    if destination.exists() {
        return if equal_files(&entry.path, &destination)? {
            Ok(destination)
        } else {
            Err("completed semantic address already has a different body".into())
        };
    }
    match std::fs::hard_link(&entry.path, &destination) {
        Ok(()) => {}
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
            if !equal_files(&entry.path, &destination)? {
                return Err("concurrent semantic-address collision".into());
            }
        }
        Err(error) => return Err(error.to_string()),
    }
    std::fs::File::open(directory)
        .and_then(|file| file.sync_all())
        .map_err(|e| e.to_string())?;
    Ok(destination)
}

pub(crate) mod stream;

#[cfg(test)]
mod tests;
