//! Relay main/388 stage 1 (R1347-1), 270 §④: the out-parameter escape. A subject whose address is
//! given to a libc out-parameter (`strtol`'s `endptr`) is written by the callee and kept by nobody,
//! so its escaped loan ends at the call's return (a). And a call into an `extern "C"` callee does not
//! unwind (b): the MIR the review reads already says so -- rustc marks a call into a non-unwinding
//! ABI `unwind unreachable` before drop elaboration -- so (b) needs no code and is pinned here. (a)
//! fails closed: a callee outside the table, a local callee, a fn-pointer call.

use rustc_middle::mir::{Location, StatementKind, TerminatorKind};

use super::{
    inner_loan,
    tests_return_origin::{named_function, with_program},
};
use crate::analyses::borrow_ownership::{
    crate_slots::CrateSlots,
    source_events::{self, SourcePhase, SourceRole},
};

/// The `B01_synthetic` / `parse_number` shape, as c2rust writes it: a local end pointer handed to
/// `strtol` and compared with the input by address afterwards. Its storage is released by its own
/// `StorageDead` (270 row 5) and by the unwind exit of the later Rust-ABI call (row 4).
const STRTOL: &str = r#"
use core::ffi::{c_char, c_int, c_long};
unsafe extern "C" {
    fn strtol(s: *const c_char, endptr: *mut *mut c_char, base: c_int) -> c_long;
}
unsafe fn report(value: c_long) -> c_long {
    value + 1
}
#[no_mangle]
pub unsafe extern "C" fn parse(mut s: *mut c_char) -> c_long {
    let mut end: *mut c_char = 0 as *mut c_char;
    let mut value: c_long = strtol(s, &mut end, 10 as c_int);
    value = report(value);
    if end == s {
        return 0 as c_long;
    }
    return value;
}
"#;

/// The negatives, in the same shape: a local callee that keeps the end pointer's address, a
/// foreign callee outside the table, and `strtol` itself reached through a function pointer.
const NEGATIVES: &str = r#"
use core::ffi::{c_char, c_int, c_long};
unsafe extern "C" {
    fn strtol(s: *const c_char, endptr: *mut *mut c_char, base: c_int) -> c_long;
    fn strtoimax_like(s: *const c_char, endptr: *mut *mut c_char, base: c_int) -> c_long;
}
static mut KEPT: *mut *mut c_char = 0 as *mut *mut c_char;
#[no_mangle]
pub unsafe extern "C" fn keep(mut s: *const c_char, mut endptr: *mut *mut c_char, mut base: c_int) -> c_long {
    KEPT = endptr;
    *endptr = s as *mut c_char;
    return base as c_long;
}
unsafe fn report(value: c_long) -> c_long {
    value + 1
}
#[no_mangle]
pub unsafe extern "C" fn local_keeps(mut s: *mut c_char) -> c_long {
    let mut end: *mut c_char = 0 as *mut c_char;
    let mut value: c_long = keep(s, &mut end, 10 as c_int);
    value = report(value);
    if end == s {
        return 0 as c_long;
    }
    return value;
}
#[no_mangle]
pub unsafe extern "C" fn table_miss(mut s: *mut c_char) -> c_long {
    let mut end: *mut c_char = 0 as *mut c_char;
    let mut value: c_long = strtoimax_like(s, &mut end, 10 as c_int);
    value = report(value);
    if end == s {
        return 0 as c_long;
    }
    return value;
}
#[no_mangle]
pub unsafe extern "C" fn through_pointer(mut s: *mut c_char) -> c_long {
    let mut parse: Option<unsafe extern "C" fn(*const c_char, *mut *mut c_char, c_int) -> c_long> =
        Some(strtol);
    let mut end: *mut c_char = 0 as *mut c_char;
    let mut value: c_long = parse.unwrap()(s, &mut end, 10 as c_int);
    value = report(value);
    if end == s {
        return 0 as c_long;
    }
    return value;
}
"#;

/// The location of the one call to the item named `name`, or with `None` the one call through a
/// function pointer.
fn call_to<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    name: Option<&str>,
) -> Location {
    let rows: Vec<_> = body
        .basic_blocks
        .iter_enumerated()
        .filter(|(_, data)| {
            let TerminatorKind::Call { func, .. } = &data.terminator().kind else { return false };
            match (func.const_fn_def(), name) {
                (Some((did, _)), Some(name)) => tcx.item_name(did).as_str() == name,
                (None, None) => true,
                _ => false,
            }
        })
        .map(|(block, data)| Location {
            block,
            statement_index: data.statements.len(),
        })
        .collect();
    assert_eq!(rows.len(), 1, "one exact call to {name:?}");
    rows[0]
}

/// Every `StorageDead` of the named local.
fn storage_dead_of(body: &rustc_middle::mir::Body<'_>, name: &str) -> Vec<Location> {
    let local = super::tests_call_reach::named_local(body, name);
    let rows: Vec<_> = body
        .basic_blocks
        .iter_enumerated()
        .flat_map(|(block, data)| {
            data.statements
                .iter()
                .enumerate()
                .filter(move |(_, statement)| statement.kind == StatementKind::StorageDead(local))
                .map(move |(statement_index, _)| Location {
                    block,
                    statement_index,
                })
        })
        .collect();
    assert!(!rows.is_empty(), "a StorageDead of {name}");
    rows
}

/// The dispositions, at each of the end pointer's own `StorageDead`s, of every inner holder of
/// `function`.
fn holders_at_storage_dead(code: &str, function: &str) -> Vec<inner_loan::Disposition> {
    let mut answer = Vec::new();
    with_program(code, |program| {
        let slots = CrateSlots::build(program);
        let loans = inner_loan::analyze(program, &slots, |_| true);
        let wanted = named_function(program, function);
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(wanted)
            .borrow();
        for at in storage_dead_of(&body, "end") {
            for row in inner_loan::obligations(program, &slots, |_| true)
                .into_iter()
                .filter(|row| row.key.function == wanted)
            {
                answer.push(loans.disposition(wanted, row.key.local, row.key.depth, at));
            }
        }
    });
    assert!(
        !answer.is_empty(),
        "the fixture must have an inner holder of the end pointer"
    );
    answer
}

/// (a): `strtol` writes `*endptr` and keeps nothing, so the holder `&mut end` does not escape into
/// it, and at the end pointer's own `StorageDead` -- after the call returned -- no holder is
/// unrepresented.
#[test]
fn r388_a_strtol_endptr_is_not_an_escape() {
    for disposition in holders_at_storage_dead(STRTOL, "parse") {
        assert_ne!(
            disposition,
            inner_loan::Disposition::Unrepresented(inner_loan::Missing::Escaped),
            "the endptr argument is written, not retained: the loan ends at the return"
        );
    }
}

/// (a), fail closed: a local callee (it may keep the address -- this one does), a foreign callee
/// outside the table, and the table's own callee through a function pointer all still escape.
#[test]
fn r388_a_outside_the_table_the_holder_still_escapes() {
    for function in ["local_keeps", "table_miss", "through_pointer"] {
        assert!(
            holders_at_storage_dead(NEGATIVES, function).contains(
                &inner_loan::Disposition::Unrepresented(inner_loan::Missing::Escaped)
            ),
            "{function}: no contract row covers this call, so the holder escapes as today"
        );
    }
}

/// The unwind events on the call edge of the one call to `callee` in `function` (`None`: the one
/// fn-pointer call).
fn unwind_events_at(code: &str, function: &str, callee: Option<&str>) -> usize {
    let mut count = 0;
    with_program(code, |program| {
        let events = source_events::collect(program);
        let wanted = named_function(program, function);
        let path = program.tcx.def_path_str(wanted.to_def_id());
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(wanted)
            .borrow();
        let call = call_to(program.tcx, &body, callee);
        count = events
            .retirements
            .keys()
            .filter(|key| {
                key.function == path
                    && key.role == SourceRole::UnwindStorage
                    && key.phase == SourcePhase::Unwind
                    && key.block == call.block.as_u32()
                    && key.statement == call.statement_index
            })
            .count();
    });
    count
}

/// (b): an `extern "C"` callee does not unwind. The review's MIR carries no unwind edge for the
/// call, so no storage is released on it -- the 270 row-4 events are the later Rust-ABI calls'
/// unwind exits, which demoted the end pointer only because its holder had escaped into `strtol`.
#[test]
fn r388_a_an_extern_c_call_has_no_unwind_release() {
    assert_eq!(
        unwind_events_at(STRTOL, "parse", Some("strtol")),
        0,
        "strtol is extern \"C\": its call has no unwind edge in the MIR the review reads"
    );
}

/// (b), the Rust ABI keeps it: `report` may unwind, so its call edge still releases the frame's
/// storage -- the end pointer's among it (270 row 4's events).
#[test]
fn r388_a_a_rust_abi_call_keeps_its_unwind_release() {
    assert!(
        unwind_events_at(STRTOL, "parse", Some("report")) > 0,
        "a Rust-ABI callee may unwind: its edge still releases the frame's storage"
    );
}

/// The fixtures' settled kinds, solved in a child with every `CRAT_` switch unset -- the defaults
/// the 376 runs and the gate run under.
fn kinds_by_default(shape: &str) -> std::collections::BTreeMap<String, String> {
    let exe = std::env::current_exe().expect("current_exe");
    let mut command = std::process::Command::new(exe);
    command.args([
        "analyses::borrow_ownership::retirement::tests_out_params::r388_child_kinds",
        "--exact",
        "--ignored",
        "--nocapture",
        "--test-threads=1",
    ]);
    for (key, _) in std::env::vars().filter(|(key, _)| key.starts_with("CRAT_")) {
        command.env_remove(key);
    }
    command.env("R388_SHAPE", shape);
    let output = command.output().expect("child test");
    let text = format!(
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.status.success(), "child {shape} failed:\n{text}");
    text.lines()
        .filter_map(|line| line.split_once("R388_KIND ").map(|(_, rest)| rest))
        .filter_map(|line| line.rsplit_once(' '))
        .map(|(key, kind)| (key.to_owned(), kind.trim().to_owned()))
        .collect()
}

#[test]
#[ignore = "runs in a child of the r388_a / r388_b witnesses"]
fn r388_child_kinds() {
    let code = match std::env::var("R388_SHAPE").as_deref() {
        Ok("STRTOL") => STRTOL,
        Ok("NEGATIVES") => NEGATIVES,
        other => panic!("unknown shape {other:?}"),
    };
    for (key, kind) in super::super::copy_relax_tests::kinds(code) {
        println!("R388_KIND {key} {kind}");
    }
}

/// End to end, the 270 shapes in one fixture (row 5: the end pointer's own `StorageDead`; row 4:
/// the unwind exits after the call): with (a) the end pointer is a reference; each negative stays
/// raw.
#[test]
fn r388_a_the_end_pointer_is_a_reference_and_the_negatives_stay_raw() {
    let kinds = kinds_by_default("STRTOL");
    assert_eq!(
        kinds.get("parse::end").map(String::as_str),
        Some("ref"),
        "{kinds:?}"
    );
    let negatives = kinds_by_default("NEGATIVES");
    for function in ["local_keeps", "table_miss", "through_pointer"] {
        assert_eq!(
            negatives
                .get(&format!("{function}::end"))
                .map(String::as_str),
            Some("raw"),
            "{function}: {negatives:?}"
        );
    }
}
