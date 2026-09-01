//! Test-only frozen P-b identity oracle for E2-FN.
//!
//! Production derives its web from the frozen analysis facts. This module is
//! the independent comparison side and consumes only the dated docs artifact;
//! no legacy rewriter module is imported or called.

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
};

use sha2::{Digest, Sha256};

const ROOTS_SHA256: &str = "ed99358a3f197dd318d2ca3a7bc15147c655494c0466ab84bec700900ecdfd33";
const REACHABLE_SHA256: &str = "b8a036acfb920460e02f95cc419d6fd32dbf76337dab95ef0838ff4c6416f041";

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct FrozenPbControl {
    roots: BTreeMap<String, BTreeSet<String>>,
    members: BTreeMap<String, BTreeSet<String>>,
}

impl FrozenPbControl {
    pub(crate) fn for_program(&self, program: &str) -> (BTreeSet<String>, BTreeSet<String>) {
        (
            self.roots.get(program).cloned().unwrap_or_default(),
            self.members.get(program).cloned().unwrap_or_default(),
        )
    }

    fn total_roots(&self) -> usize {
        self.roots.values().map(BTreeSet::len).sum()
    }

    fn total_members(&self) -> usize {
        self.members.values().map(BTreeSet::len).sum()
    }
}

fn control_dir() -> PathBuf {
    std::env::var_os("CRAT_E2_PB_CONTROL_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../..")
                .join("docs/agents/artifacts/2026-09-01-e2-fn-pb-control")
        })
}

fn checked_text(path: &Path, expected_sha256: &str) -> Result<String, String> {
    let bytes = std::fs::read(path)
        .map_err(|error| format!("P-b control {} unreadable: {error}", path.display()))?;
    let observed = format!("{:x}", Sha256::digest(&bytes));
    if observed != expected_sha256 {
        return Err(format!(
            "P-b control {} digest mismatch: expected {expected_sha256}, got {observed}",
            path.display()
        ));
    }
    String::from_utf8(bytes)
        .map_err(|error| format!("P-b control {} is not UTF-8: {error}", path.display()))
}

fn parse(
    text: &str,
    expected_header: &str,
    identity: &str,
) -> Result<BTreeMap<String, BTreeSet<String>>, String> {
    let mut lines = text.lines();
    let header = lines.next().unwrap_or_default();
    if header != expected_header {
        return Err(format!("P-b {identity} header mismatch: {header:?}"));
    }
    let mut rows = BTreeMap::<String, BTreeSet<String>>::new();
    for (index, line) in lines.enumerate() {
        let fields = line.split('\t').collect::<Vec<_>>();
        if fields.len() != 5 {
            return Err(format!(
                "P-b {identity} row {} has {} fields",
                index + 2,
                fields.len()
            ));
        }
        if fields[0] != "linux-x86_64" || fields[1] != "lambda7" {
            return Err(format!(
                "P-b {identity} row {} has wrong machine identity",
                index + 2
            ));
        }
        if !rows
            .entry(fields[2].to_owned())
            .or_default()
            .insert(fields[3].to_owned())
        {
            return Err(format!(
                "P-b {identity} duplicate at row {}: {} / {}",
                index + 2,
                fields[2],
                fields[3]
            ));
        }
    }
    Ok(rows)
}

pub(crate) fn load_frozen_pb_control() -> Result<FrozenPbControl, String> {
    let dir = control_dir();
    let roots = checked_text(&dir.join("roots.tsv"), ROOTS_SHA256)?;
    let members = checked_text(&dir.join("reachable.tsv"), REACHABLE_SHA256)?;
    let control = FrozenPbControl {
        roots: parse(
            &roots,
            "platform\tmachine_id\tprogram\tfunction\tis_public",
            "roots",
        )?,
        members: parse(
            &members,
            "platform\tmachine_id\tprogram\tfunction\tis_root",
            "members",
        )?,
    };
    if control.total_roots() != 93 || control.total_members() != 164 {
        return Err(format!(
            "P-b control count mismatch: roots={} members={}",
            control.total_roots(),
            control.total_members()
        ));
    }
    Ok(control)
}

#[test]
fn frozen_pb_control_has_exact_93_root_164_member_identity_sets() {
    let control = load_frozen_pb_control().expect("frozen P-b identity control");
    assert_eq!(control.total_roots(), 93);
    assert_eq!(control.total_members(), 164);
    for (program, roots) in &control.roots {
        let members = control.members.get(program).cloned().unwrap_or_default();
        assert!(
            roots.is_subset(&members),
            "{program} has a root outside its closure: {:?}",
            roots.difference(&members).collect::<Vec<_>>()
        );
    }
}
