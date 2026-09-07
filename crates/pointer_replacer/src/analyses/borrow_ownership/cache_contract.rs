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
#[cfg(test)]
mod tests;
