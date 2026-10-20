//! **Read-only market probe for R470-5 STOP 1 = (b).**
//!
//! The plain slice twin refuses a subject whose offset sign cannot be bounded
//! (`SliceNegOrUnknownOffset`). R464-3 admits the optional twin when every
//! offset that moves the read window takes a non-negative literal; the plain
//! twin was withheld (report 028 §4). This probe answers ONE question without
//! building that admission: of the corpus rows the plain twin currently
//! refuses, how many would the same predicate admit?
//!
//! It changes no decision. It compiles the substrate program, resolves each
//! named row to its `(function, local)` pair and evaluates
//! `every_advancing_offset_is_a_non_negative_literal` on it.
//!
//!   CRAT_W5C_PROBE_ROWS  TSV `program<TAB>subject_key`, no header
//!   CRAT_W5C_PROBE_OUT   TSV written with the verdict per row
use std::{collections::BTreeMap, fs, path::PathBuf};

use rustc_middle::{
    mir::{Local, VarDebugInfoContents},
    ty::TyCtxt,
};

use super::compare_only_offset;

/// `src::binn::IsValidBinnHeader::pbuf#1` -> (`…::IsValidBinnHeader`, `pbuf`, 1).
fn split_key(key: &str) -> Option<(String, String, u32)> {
    let (head, index) = key.rsplit_once('#')?;
    let (owner, name) = head.rsplit_once("::")?;
    Some((owner.to_owned(), name.to_owned(), index.parse().ok()?))
}

/// The census owner path and `def_path_str` need not share a crate prefix, so
/// a row matches on the longest common tail.
fn same_owner(census: &str, compiled: &str) -> bool {
    census == compiled
        || census.ends_with(&format!("::{compiled}"))
        || compiled.ends_with(&format!("::{census}"))
}

fn verdict(tcx: TyCtxt<'_>, owner: &str, name: &str, index: u32) -> String {
    for did in tcx.hir_body_owners() {
        if !matches!(tcx.def_kind(did), rustc_hir::def::DefKind::Fn) {
            continue;
        }
        if !same_owner(owner, &tcx.def_path_str(did.to_def_id())) {
            continue;
        }
        if !tcx.is_mir_available(did.to_def_id()) {
            return "unresolved:mir-unavailable".to_owned();
        }
        let local = Local::from_u32(index);
        // The SAME body the predicate reads (`optimized_mir` would steal it);
        // the borrow is dropped before the call.
        let debug_name = {
            let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
            if local.as_u32() as usize >= body.local_decls.len() {
                return format!("unresolved:local-out-of-range:{}", body.local_decls.len());
            }
            body.var_debug_info
                .iter()
                .find(|info| match &info.value {
                    VarDebugInfoContents::Place(place) => {
                        place.local == local && place.projection.is_empty()
                    }
                    _ => false,
                })
                .map(|info| info.name.to_string())
        };
        if debug_name.as_deref() != Some(name) {
            return format!("unresolved:name-mismatch:{debug_name:?}");
        }
        // Read-only: print the body a refusal is read from, when asked for it.
        if std::env::var("CRAT_W5C_PROBE_DUMP_MIR").is_ok_and(|want| owner.ends_with(&want)) {
            let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
            eprintln!("W5C-MIR {owner}\n{:#?}", *body);
        }
        return match compare_only_offset::every_advancing_offset_is_a_non_negative_literal(
            tcx, did, local,
        ) {
            Ok(()) => "admit".to_owned(),
            Err(refusal) => format!("refuse:{refusal:?}"),
        };
    }
    "unresolved:no-such-function".to_owned()
}

#[test]
#[ignore = "wave-5c R470-5(b): read-only plain-twin market probe over named corpus rows"]
fn wave5c_plain_twin_market_probe() {
    let rows_file = PathBuf::from(
        std::env::var_os("CRAT_W5C_PROBE_ROWS").expect("probe needs CRAT_W5C_PROBE_ROWS"),
    );
    let out_file = PathBuf::from(
        std::env::var_os("CRAT_W5C_PROBE_OUT").expect("probe needs CRAT_W5C_PROBE_OUT"),
    );
    let text = fs::read_to_string(&rows_file).expect("read probe rows");
    let mut by_program: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for line in text.lines().filter(|line| !line.trim().is_empty()) {
        let (program, key) = line.split_once('\t').expect("program<TAB>subject_key");
        by_program
            .entry(program.to_owned())
            .or_default()
            .push(key.to_owned());
    }

    // The substrate of record (`benchmarks/rs-crown-derived`), relative to this
    // crate, so the probe needs none of the census harness.
    let substrate = match std::env::var_os("CRAT_W5C_PROBE_SUBSTRATE") {
        Some(dir) => PathBuf::from(dir),
        None => PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .join("benchmarks/rs-crown-derived"),
    };
    let mut out = String::from("program\tsubject_key\tverdict\n");
    for (program, keys) in &by_program {
        let dir = substrate.join(program);
        let lib_root = ["lib.rs", "c2rust-lib.rs", "main.rs"]
            .into_iter()
            .map(|name| dir.join(name))
            .find(|path| path.exists())
            .unwrap_or_else(|| panic!("no lib root for {program}"));
        let verdicts = utils::compilation::run_compiler_on_path(&lib_root, |tcx| {
            keys.iter()
                .map(|key| {
                    let Some((owner, name, index)) = split_key(key) else {
                        return (key.clone(), "unresolved:unparsable-key".to_owned());
                    };
                    (key.clone(), verdict(tcx, &owner, &name, index))
                })
                .collect::<Vec<_>>()
        })
        .expect("compile substrate program");
        for (key, verdict) in verdicts {
            out.push_str(&format!("{program}\t{key}\t{verdict}\n"));
        }
        eprintln!("W5C-PROBE program={program} rows={}", keys.len());
    }
    fs::write(&out_file, out).expect("write probe verdicts");
}
