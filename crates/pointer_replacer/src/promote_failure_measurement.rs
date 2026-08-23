//! Analysis-phase measurement harness for the 27-key promote-failure census.
//!
//! This module joins existing measurement artifacts. It does not add an
//! analysis query and nothing in the production rewriter reads its output.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
    time::{Duration, Instant},
};

const REASON_KEYS: &[&str] = &[
    "arg-stays-raw",
    "arg-unadaptable-shape",
    "borrowed-into-raw-param",
    "call-site-not-adapted",
    "class-blocked",
    "copy-source-coupled",
    "duplicate-place-root",
    "escapes-via-field-store",
    "escapes-via-foreign-arg",
    "escapes-via-return",
    "flows-into-other-form",
    "flows-into-raw-param",
    "freed-slot",
    "kind-owning",
    "kind-raw",
    "nested-use-edits",
    "null-init",
    "opt-local-construction",
    "opt-use-unsupported",
    "place-read-pointee",
    "ptr-comparison",
    "raw-pointer-operation",
    "return-not-adapted",
    "slice-local-construction",
    "slice-neg-or-unknown-offset",
    "slice-use-unsupported",
    "unsupported-decl-shape",
];

const EXPECTED_REASON_COUNTS: &[(&str, usize)] = &[
    ("kind-raw", 867),
    ("class-blocked", 698),
    ("call-site-not-adapted", 684),
    ("raw-pointer-operation", 461),
    ("flows-into-raw-param", 264),
    ("arg-stays-raw", 252),
    ("duplicate-place-root", 252),
    ("slice-use-unsupported", 237),
    ("unsupported-decl-shape", 191),
    ("slice-local-construction", 190),
    ("escapes-via-return", 103),
    ("escapes-via-foreign-arg", 94),
    ("ptr-comparison", 93),
    ("return-not-adapted", 80),
    ("opt-use-unsupported", 68),
    ("flows-into-other-form", 55),
    ("arg-unadaptable-shape", 54),
    ("kind-owning", 48),
    ("null-init", 47),
    ("escapes-via-field-store", 45),
    ("opt-local-construction", 38),
    ("copy-source-coupled", 25),
    ("slice-neg-or-unknown-offset", 20),
    ("borrowed-into-raw-param", 12),
    ("nested-use-edits", 9),
    ("place-read-pointee", 7),
    ("freed-slot", 1),
];

#[derive(Clone, Copy)]
struct MechanismSpec {
    key: &'static str,
    family: &'static str,
    necessary: &'static str,
}

const MECHANISMS: &[MechanismSpec] = &[
    MechanismSpec {
        key: "kind-raw",
        family: "analysis-verdict",
        necessary: "BO licenses a non-Raw form without violating ownership or borrow constraints",
    },
    MechanismSpec {
        key: "class-blocked",
        family: "co-conversion-closure",
        necessary: "every concrete blocker in the connected class is discharged; the class converts atomically",
    },
    MechanismSpec {
        key: "call-site-not-adapted",
        family: "signature-call-web",
        necessary: "every non-adapted use of the function signature is rewritten or proved outside the licensed web",
    },
    MechanismSpec {
        key: "raw-pointer-operation",
        family: "raw-operation-semantics",
        necessary: "every recorded raw-only operation has a behavior-preserving safe-form image",
    },
    MechanismSpec {
        key: "flows-into-raw-param",
        family: "co-conversion-boundary",
        necessary: "the destination parameter and its closure convert compatibly, or a proved boundary prevents escape",
    },
    MechanismSpec {
        key: "arg-stays-raw",
        family: "co-conversion-boundary",
        necessary: "the supplying caller binding joins the compatible converted form, or a sound adapter is inserted",
    },
    MechanismSpec {
        key: "duplicate-place-root",
        family: "alias-disjointness",
        necessary: "overlapping mutable arguments are proved disjoint or represented without simultaneous conflicting borrows",
    },
    MechanismSpec {
        key: "slice-use-unsupported",
        family: "slice-use-rewrite",
        necessary: "every use of the binding has a semantics-preserving slice-form rewrite",
    },
    MechanismSpec {
        key: "unsupported-decl-shape",
        family: "declaration-ownership",
        necessary: "the actual type-owning declaration or alias is rewritten instead of a non-owning use site",
    },
    MechanismSpec {
        key: "slice-local-construction",
        family: "local-construction",
        necessary: "a sound extent is recovered and the raw initializer is rewritten into a slice value",
    },
    MechanismSpec {
        key: "escapes-via-return",
        family: "escape-signature",
        necessary: "the return contract and its callers are rewritten with valid lifetime and ownership flow",
    },
    MechanismSpec {
        key: "escapes-via-foreign-arg",
        family: "external-boundary",
        necessary: "a no-escape and lifetime contract is established, or an explicit raw boundary is retained",
    },
    MechanismSpec {
        key: "ptr-comparison",
        family: "pointer-semantics",
        necessary: "address-comparison semantics are preserved explicitly or the comparison has a proved safe equivalent",
    },
    MechanismSpec {
        key: "return-not-adapted",
        family: "return-typing",
        necessary: "the callee return signature and every dependent call site convert",
    },
    MechanismSpec {
        key: "opt-use-unsupported",
        family: "optional-use-rewrite",
        necessary: "every use has a semantics-preserving Option image",
    },
    MechanismSpec {
        key: "flows-into-other-form",
        family: "form-compatibility",
        necessary: "the class selects one compatible form or gains a proved adapter",
    },
    MechanismSpec {
        key: "arg-unadaptable-shape",
        family: "call-argument-rewrite",
        necessary: "the exact cast, call, index, or arithmetic argument adaptation is built and proved",
    },
    MechanismSpec {
        key: "kind-owning",
        family: "ownership-form",
        necessary: "a sound Box or Option-Box move, drop, and boundary policy exists for the owning slot",
    },
    MechanismSpec {
        key: "null-init",
        family: "nullable-construction",
        necessary: "an optional form is selected and null and non-null construction are rewritten consistently",
    },
    MechanismSpec {
        key: "escapes-via-field-store",
        family: "field-lifetime-flow",
        necessary: "the destination field and every store and alias promote with a valid lifetime or ownership contract",
    },
    MechanismSpec {
        key: "opt-local-construction",
        family: "local-construction",
        necessary: "the raw initializer is rewritten into Some or None with preserved null semantics",
    },
    MechanismSpec {
        key: "copy-source-coupled",
        family: "source-coupling",
        necessary: "initializer or co-conversion flow makes source and destination take one compatible form",
    },
    MechanismSpec {
        key: "slice-neg-or-unknown-offset",
        family: "offset-semantics",
        necessary: "non-negativity is proved or a cursor form preserves negative and unknown offset behavior",
    },
    MechanismSpec {
        key: "borrowed-into-raw-param",
        family: "reborrow-boundary",
        necessary: "the callee boundary adapts and the raw recipient is proved not to outlive the reborrow",
    },
    MechanismSpec {
        key: "nested-use-edits",
        family: "structured-emission",
        necessary: "nested expression rewrites compose structurally instead of as overlapping byte splices",
    },
    MechanismSpec {
        key: "place-read-pointee",
        family: "field-place-flow",
        necessary: "the promoted type and value propagate from the pointee, field, or array-decay source",
    },
    MechanismSpec {
        key: "freed-slot",
        family: "deallocation-semantics",
        necessary: "an owning form places destruction exactly, or the explicit free is proved unreachable",
    },
];

#[derive(Clone, Debug, PartialEq, Eq)]
struct JoinedRow {
    program: String,
    fn_path: String,
    mir_local: u32,
    degrade_reason: Option<String>,
    kind: String,
    raw_op: String,
    ref_class: String,
    ctor: String,
    len_class: String,
    arg_shapes: String,
    class_id: String,
    class_size: String,
    class_block: String,
    node_block: String,
    escapes: String,
}

fn join_payload(
    program: &str,
    artifact_jsonl: &str,
    facts_tsv: &str,
    coconv_tsv: &str,
) -> Result<Vec<JoinedRow>, String> {
    type Key = (String, u32);

    fn parse_tsv(
        label: &str,
        text: &str,
        required: &[&str],
    ) -> Result<BTreeMap<Key, BTreeMap<String, String>>, String> {
        let mut lines = text.lines();
        let header = lines
            .next()
            .ok_or_else(|| format!("{label}: missing header"))?;
        let columns = header.split('\t').collect::<Vec<_>>();
        let unique = columns.iter().copied().collect::<BTreeSet<_>>();
        if unique.len() != columns.len() {
            return Err(format!("{label}: duplicate header column"));
        }
        for column in required {
            if !unique.contains(column) {
                return Err(format!("{label}: missing required column {column}"));
            }
        }
        let path_col = columns
            .iter()
            .position(|column| *column == "fn_path")
            .expect("required fn_path");
        let local_col = columns
            .iter()
            .position(|column| *column == "mir_local")
            .expect("required mir_local");
        let mut rows = BTreeMap::new();
        for (index, line) in lines.enumerate() {
            let cells = line.split('\t').collect::<Vec<_>>();
            if cells.len() != columns.len() {
                return Err(format!(
                    "{label}: row {} has {} columns, expected {}",
                    index + 2,
                    cells.len(),
                    columns.len()
                ));
            }
            let local = cells[local_col].parse::<u32>().map_err(|error| {
                format!(
                    "{label}: row {} has invalid mir_local {:?}: {error}",
                    index + 2,
                    cells[local_col]
                )
            })?;
            let key = (cells[path_col].to_owned(), local);
            let payload = columns
                .iter()
                .zip(cells)
                .map(|(column, value)| ((*column).to_owned(), value.to_owned()))
                .collect();
            if rows.insert(key.clone(), payload).is_some() {
                return Err(format!("{label}: duplicate identity {}::_{}", key.0, key.1));
            }
        }
        Ok(rows)
    }

    let artifact_rows = crate::coverage_recon::schema::decode(artifact_jsonl)
        .map_err(|error| format!("artifact: {error}"))?;
    let mut artifacts = BTreeMap::new();
    for row in artifact_rows {
        let key = (row.fn_path.clone(), row.mir_local);
        if row.outcome == Some(crate::coverage_recon::schema::Outcome::Degraded)
            && row.degrade_reason.is_none()
        {
            return Err(format!(
                "artifact: degraded identity {}::_{} lacks a reason",
                key.0, key.1
            ));
        }
        if row.outcome != Some(crate::coverage_recon::schema::Outcome::Degraded)
            && row.degrade_reason.is_some()
        {
            return Err(format!(
                "artifact: non-degraded identity {}::_{} carries a reason",
                key.0, key.1
            ));
        }
        if artifacts.insert(key.clone(), row).is_some() {
            return Err(format!(
                "artifact: duplicate identity {}::_{}",
                key.0, key.1
            ));
        }
    }
    let facts = parse_tsv(
        "facts",
        facts_tsv,
        &[
            "fn_path",
            "mir_local",
            "kind",
            "raw_op",
            "ref_class",
            "ctor",
            "len_class",
            "arg_shapes",
        ],
    )?;
    let coconv = parse_tsv(
        "coconv",
        coconv_tsv,
        &[
            "fn_path",
            "mir_local",
            "class_id",
            "class_size",
            "class_block",
            "node_block",
            "escapes",
        ],
    )?;

    let artifact_keys = artifacts.keys().cloned().collect::<BTreeSet<_>>();
    for (label, keys) in [
        ("facts", facts.keys().cloned().collect::<BTreeSet<_>>()),
        ("coconv", coconv.keys().cloned().collect::<BTreeSet<_>>()),
    ] {
        if keys != artifact_keys {
            let missing = artifact_keys
                .difference(&keys)
                .next()
                .map(|(path, local)| format!("{path}::_{local}"));
            let extra = keys
                .difference(&artifact_keys)
                .next()
                .map(|(path, local)| format!("{path}::_{local}"));
            return Err(format!(
                "{label}: identity set differs from artifact; missing={missing:?} extra={extra:?}"
            ));
        }
    }

    fn field<'a>(
        label: &str,
        row: &'a BTreeMap<String, String>,
        name: &str,
    ) -> Result<&'a str, String> {
        row.get(name)
            .map(String::as_str)
            .ok_or_else(|| format!("{label}: joined row lacks {name}"))
    }

    let mut joined = Vec::with_capacity(artifacts.len());
    for ((fn_path, mir_local), artifact) in artifacts {
        let key = (fn_path.clone(), mir_local);
        let fact = &facts[&key];
        let class = &coconv[&key];
        joined.push(JoinedRow {
            program: program.to_owned(),
            fn_path,
            mir_local,
            degrade_reason: artifact.degrade_reason,
            kind: field("facts", fact, "kind")?.to_owned(),
            raw_op: field("facts", fact, "raw_op")?.to_owned(),
            ref_class: field("facts", fact, "ref_class")?.to_owned(),
            ctor: field("facts", fact, "ctor")?.to_owned(),
            len_class: field("facts", fact, "len_class")?.to_owned(),
            arg_shapes: field("facts", fact, "arg_shapes")?.to_owned(),
            class_id: field("coconv", class, "class_id")?.to_owned(),
            class_size: field("coconv", class, "class_size")?.to_owned(),
            class_block: field("coconv", class, "class_block")?.to_owned(),
            node_block: field("coconv", class, "node_block")?.to_owned(),
            escapes: field("coconv", class, "escapes")?.to_owned(),
        });
    }
    Ok(joined)
}

fn observed_counts(rows: &[JoinedRow]) -> Result<BTreeMap<String, usize>, String> {
    let registry = REASON_KEYS.iter().copied().collect::<BTreeSet<_>>();
    let mut counts = BTreeMap::new();
    for row in rows {
        let Some(reason) = row.degrade_reason.as_deref() else {
            continue;
        };
        if !registry.contains(reason) {
            return Err(format!(
                "unknown degradation reason {reason:?} at {}:{}::_{}",
                row.program, row.fn_path, row.mir_local
            ));
        }
        *counts.entry(reason.to_owned()).or_default() += 1;
    }
    Ok(counts)
}

fn render_counts(counts: &BTreeMap<String, usize>) -> String {
    let mut out = String::from("key\tcount\n");
    for (key, count) in counts {
        out.push_str(&format!("{key}\t{count}\n"));
    }
    out
}

fn select_deep_keys(
    counts: &BTreeMap<String, usize>,
    required: &BTreeSet<String>,
) -> Result<Vec<String>, String> {
    let registry = REASON_KEYS.iter().copied().collect::<BTreeSet<_>>();
    for key in counts.keys().chain(required.iter()) {
        if !registry.contains(key.as_str()) {
            return Err(format!(
                "deep-set key is outside the closed registry: {key}"
            ));
        }
    }
    let total = counts.values().sum::<usize>();
    if total == 0 {
        return Err("deep-set population is empty".to_owned());
    }
    let mut ranked = counts.iter().collect::<Vec<_>>();
    ranked.sort_by(|(key_a, count_a), (key_b, count_b)| {
        count_b.cmp(count_a).then_with(|| key_a.cmp(key_b))
    });
    let mut selected = Vec::new();
    let mut cumulative = 0usize;
    for (key, count) in ranked {
        if cumulative.saturating_mul(100) >= total.saturating_mul(80) {
            break;
        }
        selected.push(key.clone());
        cumulative += count;
    }
    for key in required {
        if !selected.contains(key) {
            selected.push(key.clone());
        }
    }
    Ok(selected)
}

fn validate_completed_shard(receipt: &str) -> Result<(), String> {
    let mut fields = BTreeMap::new();
    for (index, line) in receipt.lines().enumerate() {
        let (key, value) = line
            .split_once('=')
            .ok_or_else(|| format!("receipt line {} is not key=value", index + 1))?;
        if fields.insert(key, value).is_some() {
            return Err(format!("receipt repeats {key}"));
        }
    }
    for (key, expected) in [("status", "ok"), ("completed", "true"), ("data", "true")] {
        if fields.get(key).copied() != Some(expected) {
            return Err(format!(
                "receipt {key}={:?}, expected {expected}",
                fields.get(key)
            ));
        }
    }
    match fields.get("manifest_sha256").copied() {
        Some(value) if !value.is_empty() && value != "none" => Ok(()),
        other => Err(format!(
            "receipt manifest_sha256={other:?}, expected a digest"
        )),
    }
}

fn expected_counts() -> BTreeMap<String, usize> {
    EXPECTED_REASON_COUNTS
        .iter()
        .map(|(key, count)| ((*key).to_owned(), *count))
        .collect()
}

fn verify_expected_counts(counts: &BTreeMap<String, usize>) -> Result<(), String> {
    let expected = expected_counts();
    if counts == &expected {
        return Ok(());
    }
    let keys = counts
        .keys()
        .chain(expected.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    let differences = keys
        .into_iter()
        .filter_map(|key| {
            let got = counts.get(&key).copied().unwrap_or(0);
            let want = expected.get(&key).copied().unwrap_or(0);
            (got != want).then_some(format!("{key}: got {got}, expected {want}"))
        })
        .collect::<Vec<_>>();
    Err(format!(
        "frozen 27-key count oracle mismatch: {}",
        differences.join("; ")
    ))
}

const JOINED_HEADER: &str = "program\tfn_path\tmir_local\tdegrade_reason\tkind\traw_op\tref_class\tctor\tlen_class\targ_shapes\tclass_id\tclass_size\tclass_block\tnode_block\tescapes\n";

fn render_joined_rows(rows: &[JoinedRow]) -> String {
    let mut out = String::from(JOINED_HEADER);
    for row in rows {
        out.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            row.program,
            row.fn_path,
            row.mir_local,
            row.degrade_reason.as_deref().unwrap_or("-"),
            row.kind,
            row.raw_op,
            row.ref_class,
            row.ctor,
            row.len_class,
            row.arg_shapes,
            row.class_id,
            row.class_size,
            row.class_block,
            row.node_block,
            row.escapes,
        ));
    }
    out
}

fn parse_joined_rows(text: &str) -> Result<Vec<JoinedRow>, String> {
    let mut lines = text.lines();
    if lines.next() != Some(JOINED_HEADER.trim_end()) {
        return Err("joined rows have an unexpected header".to_owned());
    }
    let mut rows = Vec::new();
    let mut identities = BTreeSet::new();
    for (index, line) in lines.enumerate() {
        let fields = line.split('\t').collect::<Vec<_>>();
        if fields.len() != 15 {
            return Err(format!(
                "joined row {} has {} columns, expected 15",
                index + 2,
                fields.len()
            ));
        }
        let mir_local = fields[2].parse::<u32>().map_err(|error| {
            format!(
                "joined row {} has invalid mir_local {:?}: {error}",
                index + 2,
                fields[2]
            )
        })?;
        let identity = (fields[0].to_owned(), fields[1].to_owned(), mir_local);
        if !identities.insert(identity.clone()) {
            return Err(format!(
                "joined rows repeat {}:{}::_{}",
                identity.0, identity.1, identity.2
            ));
        }
        rows.push(JoinedRow {
            program: fields[0].to_owned(),
            fn_path: fields[1].to_owned(),
            mir_local,
            degrade_reason: (fields[3] != "-").then(|| fields[3].to_owned()),
            kind: fields[4].to_owned(),
            raw_op: fields[5].to_owned(),
            ref_class: fields[6].to_owned(),
            ctor: fields[7].to_owned(),
            len_class: fields[8].to_owned(),
            arg_shapes: fields[9].to_owned(),
            class_id: fields[10].to_owned(),
            class_size: fields[11].to_owned(),
            class_block: fields[12].to_owned(),
            node_block: fields[13].to_owned(),
            escapes: fields[14].to_owned(),
        });
    }
    Ok(rows)
}

fn write_atomic(path: &Path, contents: &str) -> Result<(), String> {
    let name = path
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(|| format!("non-UTF-8 output path: {}", path.display()))?;
    let temporary = path.with_file_name(format!(".{name}.tmp"));
    fs::write(&temporary, contents)
        .map_err(|error| format!("write {}: {error}", temporary.display()))?;
    fs::rename(&temporary, path).map_err(|error| {
        format!(
            "publish {} from {}: {error}",
            path.display(),
            temporary.display()
        )
    })
}

fn sha256(path: &Path) -> Result<String, String> {
    let output = std::process::Command::new("sha256sum")
        .arg(path)
        .output()
        .map_err(|error| format!("spawn sha256sum for {}: {error}", path.display()))?;
    if !output.status.success() {
        return Err(format!(
            "sha256sum failed for {}: {}",
            path.display(),
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    String::from_utf8_lossy(&output.stdout)
        .split_whitespace()
        .next()
        .map(str::to_owned)
        .ok_or_else(|| format!("sha256sum produced no digest for {}", path.display()))
}

fn write_manifest(dir: &Path, files: &[&str], name: &str) -> Result<String, String> {
    let mut files = files.to_vec();
    files.sort_unstable();
    let mut contents = String::new();
    for file in files {
        let path = dir.join(file);
        if !path.is_file() {
            return Err(format!("manifest input missing: {}", path.display()));
        }
        contents.push_str(&format!("{}  ./{}\n", sha256(&path)?, file));
    }
    let path = dir.join(name);
    write_atomic(&path, &contents)?;
    sha256(&path)
}

fn verify_manifest(dir: &Path, name: &str) -> Result<(), String> {
    let text = fs::read_to_string(dir.join(name))
        .map_err(|error| format!("read {name} in {}: {error}", dir.display()))?;
    for (index, line) in text.lines().enumerate() {
        let (expected, relative) = line
            .split_once("  ./")
            .ok_or_else(|| format!("{name} line {} is malformed", index + 1))?;
        let path = dir.join(relative);
        let actual = sha256(&path)?;
        if actual != expected {
            return Err(format!(
                "{name} hash mismatch for {}: {actual} != {expected}",
                path.display()
            ));
        }
    }
    Ok(())
}

fn audit_text(text: impl AsRef<str>) -> String {
    text.as_ref().replace(['\t', '\n', '\r'], " ")
}

fn write_partial(
    root: &Path,
    program: &str,
    phase: &str,
    status: &str,
    wall_s: f64,
    peak_rss_kb: u64,
    detail: &str,
) -> Result<(), String> {
    let dir = root.join("partials").join(program);
    fs::create_dir_all(&dir)
        .map_err(|error| format!("create partial directory {}: {error}", dir.display()))?;
    let receipt = format!(
        "machine_id=lambda7\nplatform=linux-x86_64\nphase={phase}\nprogram={program}\nstatus={status}\ncompleted=false\ndata=false\nmeasurement_started=true\nwall_s={wall_s:.3}\npeak_rss_kb={peak_rss_kb}\ndetail={}\n",
        audit_text(detail)
    );
    write_atomic(&dir.join("receipt.txt"), &receipt)?;
    write_manifest(&dir, &["receipt.txt"], "artifact-manifest.sha256")?;
    Ok(())
}

fn write_shard(
    root: &Path,
    program: &str,
    head: &str,
    rows: &[JoinedRow],
    sources: &[(&str, &Path)],
    wall_s: f64,
    peak_rss_kb: u64,
) -> Result<String, String> {
    let dir = root.join("shards").join(program);
    if dir.exists() {
        return Err(format!(
            "fresh-run shard directory already exists: {}",
            dir.display()
        ));
    }
    fs::create_dir_all(&dir)
        .map_err(|error| format!("create shard directory {}: {error}", dir.display()))?;
    write_atomic(&dir.join("rows.tsv"), &render_joined_rows(rows))?;
    let mut source_digests = String::from("artifact\tsha256\n");
    for (label, path) in sources {
        source_digests.push_str(&format!("{label}\t{}\n", sha256(path)?));
    }
    write_atomic(&dir.join("source-digests.tsv"), &source_digests)?;
    let data_manifest = write_manifest(
        &dir,
        &["rows.tsv", "source-digests.tsv"],
        "data-manifest.sha256",
    )?;
    let receipt = format!(
        "machine_id=lambda7\nplatform=linux-x86_64\nphase=program-complete\nprogram={program}\nstatus=ok\ncompleted=true\ndata=true\nmeasurement_started=true\nanalysis_head={head}\nwall_bound_kind=liveness\nwall_cap_s=14400\nmemory_policy=uncapped\nwall_s={wall_s:.3}\npeak_rss_kb={peak_rss_kb}\nrows={}\nmanifest_sha256={data_manifest}\n",
        rows.len()
    );
    validate_completed_shard(&receipt)?;
    write_atomic(&dir.join("receipt.txt"), &receipt)?;
    let artifact_manifest = write_manifest(
        &dir,
        &[
            "data-manifest.sha256",
            "receipt.txt",
            "rows.tsv",
            "source-digests.tsv",
        ],
        "artifact-manifest.sha256",
    )?;
    verify_manifest(&dir, "data-manifest.sha256")?;
    verify_manifest(&dir, "artifact-manifest.sha256")?;
    Ok(artifact_manifest)
}

fn read_completed_shard(root: &Path, program: &str) -> Result<Vec<JoinedRow>, String> {
    let dir = root.join("shards").join(program);
    verify_manifest(&dir, "data-manifest.sha256")?;
    verify_manifest(&dir, "artifact-manifest.sha256")?;
    let receipt = fs::read_to_string(dir.join("receipt.txt"))
        .map_err(|error| format!("read {program} receipt: {error}"))?;
    validate_completed_shard(&receipt)?;
    let rows = fs::read_to_string(dir.join("rows.tsv"))
        .map_err(|error| format!("read {program} joined rows: {error}"))?;
    let parsed = parse_joined_rows(&rows)?;
    if parsed.iter().any(|row| row.program != program) {
        return Err(format!("{program}: joined shard carries another program"));
    }
    Ok(parsed)
}

fn render_reason_rows(rows: &[JoinedRow]) -> String {
    let degraded = rows
        .iter()
        .filter(|row| row.degrade_reason.is_some())
        .cloned()
        .collect::<Vec<_>>();
    render_joined_rows(&degraded)
}

fn render_per_program(rows: &[JoinedRow]) -> Result<String, String> {
    let programs = rows
        .iter()
        .map(|row| row.program.clone())
        .collect::<BTreeSet<_>>();
    let mut out = String::from("program\tkey\tcount\n");
    for program in programs {
        let program_rows = rows
            .iter()
            .filter(|row| row.program == program)
            .cloned()
            .collect::<Vec<_>>();
        let counts = observed_counts(&program_rows)?;
        for key in REASON_KEYS {
            out.push_str(&format!(
                "{program}\t{key}\t{}\n",
                counts.get(*key).copied().unwrap_or(0)
            ));
        }
    }
    Ok(out)
}

fn witnesses<'a>(rows: &'a [JoinedRow]) -> BTreeMap<&'a str, &'a JoinedRow> {
    let mut witnesses = BTreeMap::new();
    for row in rows {
        let Some(reason) = row.degrade_reason.as_deref() else {
            continue;
        };
        let replace = witnesses.get(reason).is_none_or(|old: &&JoinedRow| {
            (&row.program, &row.fn_path, row.mir_local)
                < (&old.program, &old.fn_path, old.mir_local)
        });
        if replace {
            witnesses.insert(reason, row);
        }
    }
    witnesses
}

fn render_mechanisms(
    rows: &[JoinedRow],
    counts: &BTreeMap<String, usize>,
) -> Result<String, String> {
    let witness = witnesses(rows);
    let mut out = String::from(
        "key\tcount\tmechanism_family\tnecessary_promotion_condition\twitness_program\twitness_fn_path\twitness_mir_local\twitness_kind\twitness_raw_op\twitness_ref_class\twitness_ctor\twitness_len_class\twitness_arg_shapes\twitness_class_id\twitness_class_size\twitness_class_block\twitness_node_block\twitness_escapes\n",
    );
    for spec in MECHANISMS {
        let row = witness
            .get(spec.key)
            .ok_or_else(|| format!("reason {} has no witness", spec.key))?;
        out.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            spec.key,
            counts.get(spec.key).copied().unwrap_or(0),
            spec.family,
            spec.necessary,
            row.program,
            row.fn_path,
            row.mir_local,
            row.kind,
            row.raw_op,
            row.ref_class,
            row.ctor,
            row.len_class,
            row.arg_shapes,
            row.class_id,
            row.class_size,
            row.class_block,
            row.node_block,
            row.escapes,
        ));
    }
    Ok(out)
}

fn render_deep_specimens(rows: &[JoinedRow], keys: &[String]) -> Result<String, String> {
    let witness = witnesses(rows);
    let selected = keys
        .iter()
        .map(|key| {
            witness
                .get(key.as_str())
                .copied()
                .cloned()
                .ok_or_else(|| format!("deep-set key {key} has no witness"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(render_joined_rows(&selected))
}

fn current_branch(workspace: &Path) -> Result<String, String> {
    let output = std::process::Command::new("git")
        .args(["branch", "--show-current"])
        .current_dir(workspace)
        .output()
        .map_err(|error| format!("read current branch: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "read current branch: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    let branch = String::from_utf8_lossy(&output.stdout).trim().to_owned();
    if branch.is_empty() {
        Err("measurement worktree is detached".to_owned())
    } else {
        Ok(branch)
    }
}

fn run_measurement() -> Result<PathBuf, String> {
    use super::{CORPUS, a4_source_census, orchestrate};

    const WALL_CAP_S: u64 = 14_400;
    let root = PathBuf::from(
        std::env::var_os("CRAT_PROMOTE_FAILURE_OUT")
            .ok_or_else(|| "CRAT_PROMOTE_FAILURE_OUT is required".to_owned())?,
    );
    if root.exists() {
        return Err(format!(
            "fresh measurement directory already exists: {}",
            root.display()
        ));
    }
    if std::env::var("CRAT_BOC1_MEM_MB").as_deref() != Ok("uncapped") {
        return Err("CRAT_BOC1_MEM_MB must be exactly uncapped".to_owned());
    }
    if std::env::var_os("CRAT_BOC1_PROGRAMS").is_some() {
        return Err("CRAT_BOC1_PROGRAMS must be unset for the 20-program census".to_owned());
    }
    if CORPUS.len() != 20 {
        return Err(format!(
            "corpus cardinality is {}, expected 20",
            CORPUS.len()
        ));
    }
    let workspace = orchestrate::workspace_root();
    let head = orchestrate::git_sha();
    let expected_head = std::env::var("CRAT_PROMOTE_FAILURE_HEAD")
        .map_err(|_| "CRAT_PROMOTE_FAILURE_HEAD is required".to_owned())?;
    if head != expected_head {
        return Err(format!("analysis head {head} != pinned {expected_head}"));
    }
    if orchestrate::git_dirty() {
        return Err("measurement worktree is dirty".to_owned());
    }
    let branch = current_branch(&workspace)?;
    let substrate_digest = a4_source_census::registered_substrate_digest(&workspace)
        .map_err(|error| format!("substrate-preflight: {error}"))?;
    let boc1_out = std::env::var_os("CRAT_BOC1_OUT")
        .map(PathBuf::from)
        .ok_or_else(|| "CRAT_BOC1_OUT is required".to_owned())?;
    if boc1_out != root {
        return Err(format!(
            "CRAT_BOC1_OUT {} != measurement root {}",
            boc1_out.display(),
            root.display()
        ));
    }
    fs::create_dir_all(root.join("worker-artifacts"))
        .map_err(|error| format!("create measurement root {}: {error}", root.display()))?;
    let preflight = format!(
        "machine_id=lambda7\nplatform=linux-x86_64\nphase=preflight\nstatus=ok\nmeasurement_started=false\nanalysis_branch={branch}\nanalysis_head={head}\nderived_substrate_digest={substrate_digest}\nprograms=20\nwall_bound_kind=liveness\nwall_cap_s={WALL_CAP_S}\nmemory_policy=uncapped\n",
    );
    write_atomic(&root.join("preflight.txt"), &preflight)?;
    write_manifest(&root, &["preflight.txt"], "preflight-manifest.sha256")?;

    let artifact_dir = root.join("worker-artifacts");
    let mut checkpoints = String::from(
        "program\tstatus\tcompleted\tdata\twall_s\tpeak_rss_kb\tshard_manifest_sha256\n",
    );
    let mut wall_sum = 0.0f64;
    let mut peak_rss_kb = 0u64;
    let started = Instant::now();
    for program in CORPUS {
        eprintln!(
            "BOC1PHASE promote-failure phase=worker candidate={} completed={}",
            program.name,
            checkpoints.lines().count().saturating_sub(1)
        );
        let input = program.input_path(&workspace);
        let outcome = orchestrate::run_child_env(
            program.name,
            &input,
            "m1-recon",
            Duration::from_secs(WALL_CAP_S),
            &[("CRAT_BOC1_ARTIFACT_DIR", artifact_dir.display().to_string())],
        );
        wall_sum += outcome.wall_s;
        peak_rss_kb = peak_rss_kb.max(outcome.peak_rss_kb);
        if outcome.status != "ok" {
            write_partial(
                &root,
                program.name,
                "worker",
                &outcome.status,
                outcome.wall_s,
                outcome.peak_rss_kb,
                &outcome.note,
            )?;
            return Err(format!(
                "STOP phase=worker program={} status={} detail={}",
                program.name, outcome.status, outcome.note
            ));
        }
        eprintln!(
            "BOC1PHASE promote-failure phase=payload-join candidate={} completed={}",
            program.name,
            checkpoints.lines().count().saturating_sub(1)
        );
        let a_path = artifact_dir.join(format!("{}.a.jsonl", program.name));
        let facts_path = artifact_dir.join(format!("{}.facts.tsv", program.name));
        let coconv_path = artifact_dir.join(format!("{}.coconv.tsv", program.name));
        let joined = (|| {
            let artifact = fs::read_to_string(&a_path)
                .map_err(|error| format!("read {}: {error}", a_path.display()))?;
            let facts = fs::read_to_string(&facts_path)
                .map_err(|error| format!("read {}: {error}", facts_path.display()))?;
            let coconv = fs::read_to_string(&coconv_path)
                .map_err(|error| format!("read {}: {error}", coconv_path.display()))?;
            let rows = join_payload(program.name, &artifact, &facts, &coconv)?;
            observed_counts(&rows)?;
            Ok::<_, String>(rows)
        })();
        let joined = match joined {
            Ok(rows) => rows,
            Err(error) => {
                write_partial(
                    &root,
                    program.name,
                    "payload-join",
                    "schema-error",
                    outcome.wall_s,
                    outcome.peak_rss_kb,
                    &error,
                )?;
                return Err(format!(
                    "STOP phase=payload-join program={} status=schema-error detail={error}",
                    program.name
                ));
            }
        };
        let manifest = match write_shard(
            &root,
            program.name,
            &head,
            &joined,
            &[
                ("producer-a", &a_path),
                ("facts", &facts_path),
                ("coconv", &coconv_path),
            ],
            outcome.wall_s,
            outcome.peak_rss_kb,
        ) {
            Ok(manifest) => manifest,
            Err(error) => {
                write_partial(
                    &root,
                    program.name,
                    "shard-finalize",
                    "schema-error",
                    outcome.wall_s,
                    outcome.peak_rss_kb,
                    &error,
                )?;
                return Err(format!(
                    "STOP phase=shard-finalize program={} status=schema-error detail={error}",
                    program.name
                ));
            }
        };
        checkpoints.push_str(&format!(
            "{}\tok\ttrue\ttrue\t{:.3}\t{}\t{}\n",
            program.name, outcome.wall_s, outcome.peak_rss_kb, manifest
        ));
        write_atomic(&root.join("checkpoints.tsv"), &checkpoints)?;
    }

    eprintln!("BOC1PHASE promote-failure phase=aggregate candidate=none completed=20");
    let aggregate_stop = |error: String| {
        let _ = write_partial(
            &root,
            "none",
            "aggregate",
            "schema-error",
            wall_sum,
            peak_rss_kb,
            &error,
        );
        format!("STOP phase=aggregate program=none status=schema-error detail={error}")
    };
    let mut all_rows = Vec::new();
    for program in CORPUS {
        all_rows.extend(read_completed_shard(&root, program.name).map_err(&aggregate_stop)?);
    }
    if all_rows.len() != 6_015 {
        return Err(aggregate_stop(format!(
            "identity_rows={} expected=6015",
            all_rows.len()
        )));
    }
    let counts = observed_counts(&all_rows).map_err(&aggregate_stop)?;
    verify_expected_counts(&counts).map_err(&aggregate_stop)?;
    let required = std::env::var("CRAT_PROMOTE_FAILURE_REQUIRED_KEYS")
        .unwrap_or_default()
        .split(',')
        .filter(|key| !key.is_empty())
        .map(str::to_owned)
        .collect::<BTreeSet<_>>();
    let deep = select_deep_keys(&counts, &required).map_err(&aggregate_stop)?;
    let aggregate = root.join("aggregate");
    fs::create_dir_all(&aggregate)
        .map_err(|error| format!("create aggregate {}: {error}", aggregate.display()))
        .map_err(&aggregate_stop)?;
    write_atomic(
        &aggregate.join("reason-rows.tsv"),
        &render_reason_rows(&all_rows),
    )
    .map_err(&aggregate_stop)?;
    write_atomic(
        &aggregate.join("reason-counts.tsv"),
        &render_counts(&counts),
    )
    .map_err(&aggregate_stop)?;
    let per_program = render_per_program(&all_rows).map_err(&aggregate_stop)?;
    write_atomic(&aggregate.join("per-program.tsv"), &per_program).map_err(&aggregate_stop)?;
    let mechanisms = render_mechanisms(&all_rows, &counts).map_err(&aggregate_stop)?;
    write_atomic(&aggregate.join("mechanisms.tsv"), &mechanisms).map_err(&aggregate_stop)?;
    let specimens = render_deep_specimens(&all_rows, &deep).map_err(&aggregate_stop)?;
    write_atomic(&aggregate.join("deep-specimens.tsv"), &specimens).map_err(&aggregate_stop)?;
    let provenance = format!(
        "machine_id=lambda7\nplatform=linux-x86_64\nmeasurement_class=promote-failure-mechanism\nanalysis_branch={branch}\nanalysis_head={head}\nderived_substrate_digest={substrate_digest}\nsource_reference_manifest_sha256=b6e652d588e28587399a4c81b892967e6cb18cb6f3e29ee82f71228f6a21afb1\ncrown_reference_join_manifest_sha256=6e839c8d2af4dc3312a634173490484a32d10d9743df4d4ce8e6c8407a59a385\nprograms=20\nidentity_rows=6015\ndegraded_rows=4895\ndecided_rows=1120\nreason_keys=27\ndeep_keys={}\nrequired_keys={}\nwall_bound_kind=liveness\nwall_cap_s={WALL_CAP_S}\nmemory_policy=uncapped\nwall_sum_s={wall_sum:.3}\nelapsed_s={:.3}\npeak_rss_kb={peak_rss_kb}\ntiming_comparison=forbidden-across-machines\n",
        deep.join(","),
        required.into_iter().collect::<Vec<_>>().join(","),
        started.elapsed().as_secs_f64(),
    );
    write_atomic(&aggregate.join("provenance.txt"), &provenance).map_err(&aggregate_stop)?;
    let report = format!(
        "# Promote-failure mechanism census\n\n- exact subjects: 6,015\n- degraded: 4,895\n- decided: 1,120\n- reason keys: 27\n- frozen count oracle: byte-identical\n- deep-set rule: 80% prefix plus exact frontier/gap keys\n- deep keys: {}\n- programs: 20/20 completed\n- data=false partials aggregated: 0\n- wall sum on lambda7: {wall_sum:.3} s\n- peak worker RSS on lambda7: {peak_rss_kb} KiB\n",
        deep.join(", ")
    );
    write_atomic(&aggregate.join("report.md"), &report).map_err(&aggregate_stop)?;
    let data_files = [
        "deep-specimens.tsv",
        "mechanisms.tsv",
        "per-program.tsv",
        "provenance.txt",
        "reason-counts.tsv",
        "reason-rows.tsv",
        "report.md",
    ];
    let data_manifest =
        write_manifest(&aggregate, &data_files, "data-manifest.sha256").map_err(&aggregate_stop)?;
    let receipt = format!(
        "machine_id=lambda7\nplatform=linux-x86_64\nphase=aggregate\nstatus=ok\ncompleted=true\ndata=true\nmeasurement_started=true\nanalysis_head={head}\nprograms=20\nidentity_rows=6015\ndegraded_rows=4895\nreason_keys=27\nmanifest_sha256={data_manifest}\n",
    );
    validate_completed_shard(&receipt).map_err(&aggregate_stop)?;
    write_atomic(&aggregate.join("receipt.txt"), &receipt).map_err(&aggregate_stop)?;
    let artifact_files = [
        "data-manifest.sha256",
        "deep-specimens.tsv",
        "mechanisms.tsv",
        "per-program.tsv",
        "provenance.txt",
        "reason-counts.tsv",
        "reason-rows.tsv",
        "receipt.txt",
        "report.md",
    ];
    let manifest = write_manifest(&aggregate, &artifact_files, "artifact-manifest.sha256")
        .map_err(&aggregate_stop)?;
    verify_manifest(&aggregate, "data-manifest.sha256").map_err(&aggregate_stop)?;
    verify_manifest(&aggregate, "artifact-manifest.sha256").map_err(&aggregate_stop)?;
    println!(
        "PROMOTE-FAILURE complete programs=20 rows=6015 degraded=4895 keys=27 manifest={manifest}"
    );
    Ok(aggregate)
}

#[test]
#[ignore = "analysis-phase corpus measurement: sequential 20-program m1-recon workers"]
fn promote_failure_mechanism_corpus() {
    run_measurement().unwrap_or_else(|error| panic!("PROMOTE-FAILURE {error}"));
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::coverage_recon::schema::{self, DeclShape, Outcome, PairingConfidence, Row};

    const FACTS_HEADER: &str = "fn_path\tmir_local\tis_param\tannotated\tslot\tkind\traw_op\tptr_cmp\treferenced\tref_kinds\tref_class\tctor\tlen_class\tsize_expr\targ_shapes\targ_sites\n";
    const COCONV_HEADER: &str = "fn_path\tmir_local\tis_param\tclass_id\tclass_size\tadmissible\tclass_block\tnode_block\tsites\tescapes\tp2_blind_only\tp2_all_pairs\n";

    fn artifact(reason: &str) -> String {
        schema::encode(&[Row {
            fn_path: "m::f".to_owned(),
            mir_local: 1,
            param_name: Some("p".to_owned()),
            arg_index: Some(1),
            ptr_depth: 1,
            pairing_confidence: PairingConfidence::High,
            decl_span: Some("<fixture>:1:1".to_owned()),
            decl_span_lo: Some(0),
            decl_span_hi: Some(6),
            binding_span_lo: None,
            binding_span_hi: None,
            decl_shape: Some(DeclShape::RawPtr),
            outcome: Some(Outcome::Degraded),
            degrade_reason: Some(reason.to_owned()),
            freed: Some(false),
            approx_len: None,
        }])
    }

    fn facts() -> String {
        format!(
            "{FACTS_HEADER}m::f\t1\t1\t1\t1\traw\toffset\t0\t1\tfn-ptr-cast\tpinned\tparam\tparam-no-site\t\tbare-local\t2\n"
        )
    }

    fn coconv() -> String {
        format!(
            "{COCONV_HEADER}m::f\t1\t1\t7\t3\t0\targ-stays-raw\targ-stays-raw\t2\tfield-store\t0\t0\n"
        )
    }

    #[test]
    fn promote_failure_complete_payload_join_preserves_exact_fields() {
        let rows = join_payload("fixture", &artifact("kind-raw"), &facts(), &coconv())
            .expect("complete fixture joins");
        assert_eq!(rows.len(), 1);
        assert_eq!(
            rows[0],
            JoinedRow {
                program: "fixture".to_owned(),
                fn_path: "m::f".to_owned(),
                mir_local: 1,
                degrade_reason: Some("kind-raw".to_owned()),
                kind: "raw".to_owned(),
                raw_op: "offset".to_owned(),
                ref_class: "pinned".to_owned(),
                ctor: "param".to_owned(),
                len_class: "param-no-site".to_owned(),
                arg_shapes: "bare-local".to_owned(),
                class_id: "7".to_owned(),
                class_size: "3".to_owned(),
                class_block: "arg-stays-raw".to_owned(),
                node_block: "arg-stays-raw".to_owned(),
                escapes: "field-store".to_owned(),
            }
        );
    }

    #[test]
    fn promote_failure_join_rejects_missing_facts_row() {
        let error = join_payload("fixture", &artifact("kind-raw"), FACTS_HEADER, &coconv())
            .expect_err("missing facts identity must fail");
        assert!(error.contains("facts") && error.contains("m::f::_1"));
    }

    #[test]
    fn promote_failure_join_rejects_duplicate_coconv_row() {
        let duplicate = format!("{}{}", coconv(), coconv().lines().nth(1).unwrap());
        let error = join_payload("fixture", &artifact("kind-raw"), &facts(), &duplicate)
            .expect_err("duplicate co-conversion identity must fail");
        assert!(error.contains("duplicate") && error.contains("coconv"));
    }

    #[test]
    fn promote_failure_registry_rejects_an_unknown_reason() {
        let rows = join_payload("fixture", &artifact("invented-reason"), &facts(), &coconv())
            .expect("identity join itself is independent of the registry");
        let error = observed_counts(&rows).expect_err("unknown reason must fail closed");
        assert!(error.contains("invented-reason"));
    }

    #[test]
    fn promote_failure_completed_data_gate_is_two_sided() {
        let complete = "status=ok\ncompleted=true\ndata=true\nmanifest_sha256=abc\n";
        assert!(validate_completed_shard(complete).is_ok());
        for partial in [
            "status=ok\ncompleted=false\ndata=false\nmanifest_sha256=abc\n",
            "status=timeout\ncompleted=false\ndata=false\nmanifest_sha256=abc\n",
            "status=ok\ncompleted=true\ndata=true\n",
        ] {
            assert!(
                validate_completed_shard(partial).is_err(),
                "partial receipt passed: {partial:?}"
            );
        }
    }

    #[test]
    fn promote_failure_deep_set_is_80_percent_plus_required() {
        let counts = [
            ("kind-raw", 867),
            ("class-blocked", 698),
            ("call-site-not-adapted", 684),
            ("raw-pointer-operation", 461),
            ("flows-into-raw-param", 264),
            ("arg-stays-raw", 252),
            ("duplicate-place-root", 252),
            ("slice-use-unsupported", 237),
            ("unsupported-decl-shape", 191),
            ("slice-local-construction", 190),
            ("escapes-via-return", 103),
            ("escapes-via-foreign-arg", 94),
            ("ptr-comparison", 93),
            ("return-not-adapted", 80),
            ("opt-use-unsupported", 68),
            ("flows-into-other-form", 55),
            ("arg-unadaptable-shape", 54),
            ("kind-owning", 48),
            ("null-init", 47),
            ("escapes-via-field-store", 45),
            ("opt-local-construction", 38),
            ("copy-source-coupled", 25),
            ("slice-neg-or-unknown-offset", 20),
            ("borrowed-into-raw-param", 12),
            ("nested-use-edits", 9),
            ("place-read-pointee", 7),
            ("freed-slot", 1),
        ]
        .into_iter()
        .map(|(key, count)| (key.to_owned(), count))
        .collect();
        let required = ["freed-slot".to_owned()].into_iter().collect();
        let selected = select_deep_keys(&counts, &required).expect("closed keys");
        assert_eq!(selected.len(), 11);
        assert_eq!(
            &selected[..10],
            &[
                "kind-raw",
                "class-blocked",
                "call-site-not-adapted",
                "raw-pointer-operation",
                "flows-into-raw-param",
                "arg-stays-raw",
                "duplicate-place-root",
                "slice-use-unsupported",
                "unsupported-decl-shape",
                "slice-local-construction",
            ]
        );
        assert_eq!(selected[10], "freed-slot");
    }

    #[test]
    fn promote_failure_payload_keeps_reason_counts_byte_identical() {
        let rows = join_payload("fixture", &artifact("kind-raw"), &facts(), &coconv())
            .expect("complete fixture joins");
        let counts = observed_counts(&rows).expect("registered reason");
        assert_eq!(render_counts(&counts), "key\tcount\nkind-raw\t1\n");
    }

    #[test]
    fn promote_failure_mechanism_registry_is_closed_over_all_27_keys() {
        let keys = REASON_KEYS.iter().copied().collect::<BTreeSet<_>>();
        let expected = EXPECTED_REASON_COUNTS
            .iter()
            .map(|(key, _)| *key)
            .collect::<BTreeSet<_>>();
        let mechanisms = MECHANISMS
            .iter()
            .map(|spec| spec.key)
            .collect::<BTreeSet<_>>();
        assert_eq!(keys.len(), 27);
        assert_eq!(keys, expected);
        assert_eq!(keys, mechanisms);
        assert_eq!(
            EXPECTED_REASON_COUNTS.iter().map(|(_, n)| n).sum::<usize>(),
            4_895
        );
    }
}
