//! Wave-6o relay 134 (R767-1, USER): the exported-entry premise (W4, R462)
//! assumes a C caller never passes one object to two pointer parameters of an
//! exported entry. Where the program's OWN provided test does exactly that, and
//! a member writes the pointed-to object, the premise is false for that pair:
//! under Tree Borrows a reference formal is protected for the call and the
//! other member's access to the same object is UB (libzahl's `zsub(a, a, _1)`,
//! wave-6o 095 STOP 2).
//!
//! The evidence is a declared table extracted from the provided tests
//! (`exported_entry_aliased_by_test.tsv`: the scan of wave-6o 096, clang's AST
//! of the staged tests, plus the write facts), not an analysis input: the
//! analysis still decides these formals safe. The decision stage holds each
//! formal of the table's hold set raw, per FORMAL, receipted
//! `held:exported-entry-aliased-by-test` with the pair and the test's call site.
//! The formal stays an ordinary raw formal of its class, so its in-crate
//! callers are bridged at the call like any raw formal's.

use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::TyCtxt;

use super::{Subject, SubjectKind};

/// The declared table of record (the docs copy is
/// `agents/tools/runtime/r672/exported-entry-aliased-by-test.tsv`).
const TABLE: &str = include_str!("exported_entry_aliased_by_test.tsv");

/// The fixture rows: matched only where no census program is set (a unit test).
#[cfg(test)]
const FIXTURE_TABLE: &str = "\
-\tcrat_w6o_zsub\ta\tb\t0\t1\tW\tr\tUB\ta,b\tfixture:zsub(a,a,c)\t1
-\tcrat_w6o_zsub\ta\tc\t0\t2\tW\tr\tUB\ta,c\tfixture:zsub(a,b,a)\t1
-\tcrat_w6o_zcmp\ta\tb\t0\t1\tr\tr\tclean\t-\tfixture:zcmp(a,a)\t1
";

/// `CRAT_EXPORTED_ENTRY_ALIASED_BY_TEST=<path>` replaces the table (an empty
/// file is the fault: no formal held).
const OVERRIDE: &str = "CRAT_EXPORTED_ENTRY_ALIASED_BY_TEST";

/// One row: program, entry, the pair's formals and positions (0-based), which
/// members write the pointed-to object, the verdict (`UB` / `clean`), the held
/// formals, and one witness call site in the provided test.
struct Row<'a> {
    program: &'a str,
    entry: &'a str,
    formals: [(&'a str, usize); 2],
    verdict: &'a str,
    hold: Vec<&'a str>,
    site: &'a str,
}

fn rows(text: &str) -> impl Iterator<Item = Row<'_>> {
    text.lines()
        .filter(|l| !l.starts_with('#') && !l.starts_with("program\t") && !l.trim().is_empty())
        .filter_map(|l| {
            let f: Vec<&str> = l.split('\t').collect();
            (f.len() >= 11).then(|| Row {
                program: f[0],
                entry: f[1],
                formals: [
                    (f[2], f[4].parse().unwrap_or(usize::MAX)),
                    (f[3], f[5].parse().unwrap_or(usize::MAX)),
                ],
                verdict: f[8],
                hold: f[9].split(',').filter(|h| *h != "-").collect(),
                site: f[10],
            })
        })
}

/// The receipt detail when `subject` is a formal the table holds, else `None`.
pub(crate) fn held(tcx: TyCtxt<'_>, subject: &Subject) -> Option<String> {
    let SubjectKind::Param { hir_index } = subject.kind else {
        return None;
    };
    let program = std::env::var("CRAT_ERA5_PROGRAM").ok();
    let owned;
    let text: &str = match std::env::var(OVERRIDE) {
        Ok(path) => {
            owned = std::fs::read_to_string(&path).unwrap_or_default();
            &owned
        }
        Err(_) => table_for(program.is_some()),
    };
    let program = program.as_deref().unwrap_or("-");
    if !super::exported_pair::exported(tcx, subject.fn_did) {
        return None;
    }
    let entry = tcx.item_name(subject.fn_did.to_def_id());
    let name = subject.param_name.as_deref()?;
    let pairs: Vec<String> = rows(text)
        .filter(|r| r.program == program && r.entry == entry.as_str() && r.verdict == "UB")
        .filter(|r| {
            r.hold.contains(&name) && r.formals.iter().any(|&(f, i)| f == name && i == hir_index)
        })
        .map(|r| {
            format!(
                "{}({},{})@{}",
                r.entry, r.formals[0].0, r.formals[1].0, r.site
            )
        })
        .collect();
    (!pairs.is_empty()).then(|| pairs.join(";"))
}

/// R819-1 item 2 (wave-5d): the formal position pairs of `entry` that the
/// provided test passes one object to, whatever the members do. The scope's
/// separate-object certificate does not hold for them.
pub(crate) fn aliased_pairs(tcx: TyCtxt<'_>, entry: LocalDefId) -> Vec<(usize, usize)> {
    let program = std::env::var("CRAT_ERA5_PROGRAM").ok();
    let owned;
    let text: &str = match std::env::var(OVERRIDE) {
        Ok(path) => {
            owned = std::fs::read_to_string(&path).unwrap_or_default();
            &owned
        }
        Err(_) => table_for(program.is_some()),
    };
    let program = program.as_deref().unwrap_or("-");
    let name = tcx.item_name(entry.to_def_id());
    rows(text)
        .filter(|r| r.program == program && r.entry == name.as_str())
        .map(|r| (r.formals[0].1, r.formals[1].1))
        .collect()
}

#[cfg(test)]
fn table_for(census: bool) -> &'static str {
    if census { TABLE } else { FIXTURE_TABLE }
}

#[cfg(not(test))]
fn table_for(_census: bool) -> &'static str {
    TABLE
}
