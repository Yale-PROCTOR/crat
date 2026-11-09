//! R1500-2 / R1502-2 (main 330 (f); the user's words "1" on addendum 1499's option (1) and "1" on
//! addendum 1501's option (1), the instruments only): three log-only instruments in the verify's
//! rounds, written only under the phase log's sub-marks (the baseline and the precise verify run
//! inside `with_sub_marks`):
//! - at each replay's end, the conflict functions: the count, and the def paths when there are few;
//!   every path, sorted, to `<CRAT_BO_CONFLICT_DUMP_DIR>/round-conflicts-<pid>.tsv` when that switch
//!   is set (its own explicit path, so nothing lands in the artifact directory the identities
//!   compare; one file per process, so two processes never share one);
//! - one line per commit: a guarded-repair action's kind, target, issuer and the planner's own
//!   label; a count line for the retirement pins, the field-own forbids and the plain repair;
//! - at each re-solve, the model's distance from the round's model: the slots changed in total and
//!   within the round's conflict functions, and the ten functions that changed most.
//!
//! With the sub-marks off, nothing here computes anything.

use std::{
    io::Write,
    path::PathBuf,
    sync::atomic::{AtomicUsize, Ordering},
};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_span::def_id::{DefIndex, LocalDefId};

use super::{
    SlotKind,
    crate_slots::CrateSlots,
    guarded_repair::{CommitAction, CommitActionKind, SlotKey},
    slots::SlotId,
    solver::SlotRef,
};
use crate::utils::rustc::RustProgram;

/// The stderr line lists the conflict functions' paths only up to this many.
pub(crate) const LISTED: usize = 8;

/// The per-round file's name under `CRAT_BO_CONFLICT_DUMP_DIR`: this prefix, the process id, `.tsv`.
/// One writer per file, so rows of two processes never interleave nor share verify numbers.
pub(crate) const CONFLICTS_FILE_PREFIX: &str = "round-conflicts-";

/// A commit line's label is cut at this many bytes (at a char boundary), the rest counted.
pub(crate) const LABEL_BYTES: usize = 600;

fn conflicts_file_name() -> String {
    format!("{CONFLICTS_FILE_PREFIX}{}.tsv", std::process::id())
}

static VERIFIES: AtomicUsize = AtomicUsize::new(0);

fn on() -> bool {
    crate::phase_log::sub_marks_on()
}

/// The verify's sequence number in this process (1, 2, ...), counted only while the sub-marks are
/// on; 0 when they are off.
pub(crate) fn begin_verify() -> usize {
    if !on() {
        return 0;
    }
    VERIFIES.fetch_add(1, Ordering::Relaxed) + 1
}

/// R1502-2 item 2: `CRAT_BO_CONFLICT_DUMP_DIR=<dir>`, the per-round file's own directory -- a log-only
/// switch for a run the user's word names; never in a gate or an identity run, off by default, not
/// in the model cache's key nor the checkpoint's identity. Unset or empty: no file. Read once.
fn dump_dir() -> Option<PathBuf> {
    static DIR: std::sync::OnceLock<Option<PathBuf>> = std::sync::OnceLock::new();
    DIR.get_or_init(|| dump_dir_from(std::env::var_os("CRAT_BO_CONFLICT_DUMP_DIR")))
        .clone()
}

/// [`dump_dir`]'s reading of the value: a path, an empty value unset.
fn dump_dir_from(value: Option<std::ffi::OsString>) -> Option<PathBuf> {
    value.filter(|dir| !dir.is_empty()).map(PathBuf::from)
}

fn function_path(program: &RustProgram<'_>, did: LocalDefId) -> String {
    program.tcx.def_path_str(did.to_def_id())
}

/// The replay's conflict functions: one line, and every path to the per-round file. Returns them
/// for [`drift`], or `None` with the sub-marks off.
pub(crate) fn conflicts<T>(
    program: &RustProgram<'_>,
    verify: usize,
    round: usize,
    conflicts: &FxHashMap<LocalDefId, T>,
) -> Option<FxHashSet<LocalDefId>> {
    if !on() {
        return None;
    }
    let mut paths = conflicts
        .keys()
        .map(|did| function_path(program, *did))
        .collect::<Vec<_>>();
    paths.sort();
    let file = match dump_dir() {
        Some(dir) => match append_rows(&dir, verify, round, &paths) {
            Ok(()) => conflicts_file_name(),
            // A failed write may have left a partial row behind.
            Err(error) => format!("unwritten({error})"),
        },
        None => "none".to_owned(),
    };
    crate::phase_log::sub("verify:conflicts", "end", || {
        let listed = if paths.len() <= LISTED {
            paths.join(",")
        } else {
            format!(
                "{},…(+{} in the file)",
                paths[..LISTED].join(","),
                paths.len() - LISTED
            )
        };
        format!(
            "verify={verify} round={round} count={} file={file} fns={listed}",
            paths.len()
        )
    });
    Some(conflicts.keys().copied().collect())
}

fn append_rows(
    dir: &std::path::Path,
    verify: usize,
    round: usize,
    paths: &[String],
) -> std::io::Result<()> {
    std::fs::create_dir_all(dir)?;
    let path = dir.join(conflicts_file_name());
    let mut file = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(&path)?;
    let mut text = String::new();
    if file.metadata()?.len() == 0 {
        text.push_str("verify\tround\tfunction\n");
    }
    for function in paths {
        text.push_str(&format!("{verify}\t{round}\t{function}\n"));
    }
    file.write_all(text.as_bytes())
}

/// A slot's key (`<def path>::_<local>@d<depth>`, or the field's), only for a slot inside its
/// universe; otherwise the planner's numeric form. Never panics on an index.
fn render(program: &RustProgram<'_>, slots: &CrateSlots, slot: SlotRef) -> String {
    let inside = match slot {
        SlotRef::Field(id) => id.index() < slots.field_slots.len(),
        SlotRef::Local(did, id) => slots
            .fn_local_slots
            .get(&did)
            .is_some_and(|universe| id.index() < universe.len()),
    };
    inside
        .then(|| super::model_cache::render_key(program.tcx, slots, slot))
        .flatten()
        .unwrap_or_else(|| {
            format!(
                "unrendered:{}",
                super::guarded_repair::slotref_diagnostic(slot)
            )
        })
}

/// `SlotKey::of`'s inverse for its two variants (0 field, 1 local); `None` for any other.
fn slot_of_key(key: SlotKey) -> Option<SlotRef> {
    match key.variant {
        0 => Some(SlotRef::Field(SlotId::from_usize(key.slot))),
        1 => Some(SlotRef::Local(
            LocalDefId {
                local_def_index: DefIndex::from_u32(key.owner),
            },
            SlotId::from_usize(key.slot),
        )),
        _ => None,
    }
}

/// `label` cut at [`LABEL_BYTES`] at a char boundary, with the number of bytes left out.
fn bounded(label: &str) -> String {
    if label.len() <= LABEL_BYTES {
        return label.to_owned();
    }
    let mut end = LABEL_BYTES;
    while !label.is_char_boundary(end) {
        end -= 1;
    }
    format!("{}…(+{} bytes)", &label[..end], label.len() - end)
}

/// One guarded-repair commit: its kind, target, issuer (the spawning edge's) and label.
pub(crate) fn commit(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    verify: usize,
    round: usize,
    action: &CommitAction,
) {
    crate::phase_log::sub("verify:commit", "end", || {
        let kind = match action.kind {
            CommitActionKind::GuardedCommit => "guarded",
            CommitActionKind::UnconditionalCommit => "unconditional",
            CommitActionKind::RecurrenceEscalation => "escalation",
        };
        let issuer = match action.edge.issuer {
            None => "none".to_owned(),
            Some(key) => slot_of_key(key).map_or_else(
                || format!("unrendered:variant{}", key.variant),
                |slot| render(program, slots, slot),
            ),
        };
        format!(
            "verify={verify} round={round} kind={kind} target={} issuer={issuer} label={}",
            render(program, slots, action.target),
            bounded(&action.diagnostic_label)
        )
    });
}

/// A round's commits that are not the planner's actions, counted: the retirement pins
/// (`retirement-raw`), the field-own forbids (`field-own`), the plain repair (`plain`).
pub(crate) fn commits_counted(verify: usize, round: usize, kind: &str, count: usize) {
    crate::phase_log::sub("verify:commit", "end", || {
        format!("verify={verify} round={round} kind={kind} count={count}")
    });
}

/// The re-solve after round `round`'s commits: how far its model is from the round's model.
pub(crate) fn drift(
    program: &RustProgram<'_>,
    verify: usize,
    round: usize,
    previous: &FxHashMap<SlotRef, SlotKind>,
    next: &FxHashMap<SlotRef, SlotKind>,
    conflict_functions: Option<&FxHashSet<LocalDefId>>,
) {
    if !on() {
        return;
    }
    let mut changed = 0usize;
    let mut within = 0usize;
    let mut by_function: FxHashMap<Option<LocalDefId>, usize> = FxHashMap::default();
    for (slot, kind) in next {
        if previous.get(slot) == Some(kind) {
            continue;
        }
        changed += 1;
        let function = match slot {
            SlotRef::Local(did, _) => Some(*did),
            SlotRef::Field(_) => None,
        };
        if let Some(did) = function
            && conflict_functions.is_some_and(|functions| functions.contains(&did))
        {
            within += 1;
        }
        *by_function.entry(function).or_default() += 1;
    }
    let gone = previous
        .keys()
        .filter(|slot| !next.contains_key(slot))
        .count();
    let mut top = by_function
        .into_iter()
        .map(|(function, count)| {
            let name =
                function.map_or_else(|| "<fields>".to_owned(), |did| function_path(program, did));
            (count, name)
        })
        .collect::<Vec<_>>();
    top.sort_by(|a, b| b.0.cmp(&a.0).then_with(|| a.1.cmp(&b.1)));
    top.truncate(10);
    crate::phase_log::sub("verify:drift", "end", || {
        format!(
            "verify={verify} round={round} slots={} changed={changed} gone={gone} in_conflict_fns={within} conflict_fns={} top={}",
            next.len(),
            conflict_functions.map_or(0, FxHashSet::len),
            top.iter()
                .map(|(count, name)| format!("{name}:{count}"))
                .collect::<Vec<_>>()
                .join(",")
        )
    });
}

#[cfg(test)]
#[path = "round_log_tests.rs"]
mod tests;
