//! wave-6l A8 (relay 026, R480-4) — **the missing return adapters**: shape (c)
//! of the ceiling row, "an Option returned as null-or-pointer".
//!
//! The row is `return-not-adapted`, and at the landed frame it is the residue
//! of ONE gate: an UNANNOTATED local whose initializer is a call
//! (`Construction::CallResult`) reaches [`super::decision::residual_reason`]
//! because no declaration channel can type it — the inferred-local channel
//! needs the callee's own return to be converted, and here the callee's return
//! interface stays `Raw` (`lil::add_func`, `binn::binn_alloc_item`,
//! `buffer::buffer_new_with_size`, `urlparser::url_get_protocol` — 11 of the
//! 15 readable rows at batch 18 have exactly this shape).
//!
//! The adapter this module witnesses is the receiver-side one: the RAW result
//! is adapted where it lands, `let mut cmd: Option<&mut lil_func> =
//! add_func(l, name).as_mut();`, and the null test that the C code already
//! writes becomes the Option's own discriminant. The callee keeps its raw
//! interface, so nothing about the callee's class moves.
//!
//! Fixtures are reductions of real corpus functions: lil `add_func` /
//! `lil_register` (subject `lil_register::cmd#5`, batch 18) and the same shape
//! with a CONVERTED callee return, which the existing receiver path already
//! serves and this arm must not touch.

use super::{A5Mode, RewriteOutcome, WholeProgramAttestation, decision::lifetime::LifetimeFailure};

/// lil `add_func` + `lil_register`: the callee returns a nullable pointer out
/// of the program's own storage and its return interface stays raw; the
/// receiver null-tests and then writes one field.
const LIL_REGISTER: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct lil_func {
    pub proc_0: usize,
    pub name: *mut i8,
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct lil {
    pub cmds: usize,
    pub cmd: *mut *mut lil_func,
}
#[no_mangle]
pub unsafe extern "C" fn add_func(mut l: *mut lil, mut name: *mut i8) -> *mut lil_func {
    if (*l).cmds == 0 as usize {
        return 0 as *mut lil_func;
    }
    return *((*l).cmd).offset(0 as isize);
}
#[no_mangle]
pub unsafe extern "C" fn lil_register(mut l: *mut lil, mut name: *mut i8, mut proc_0: usize) -> i32 {
    let mut cmd = add_func(l, name);
    if cmd.is_null() {
        return 0 as i32;
    }
    (*cmd).proc_0 = proc_0;
    return 1 as i32;
}
"#;

/// The control: the same receiver shape over a callee whose return the
/// EXISTING path converts (the return is a borrow of the callee's own
/// parameter, which rule W6L-1 ties). The receiver must take the callee's
/// delivered form through the inferred-local channel — this arm must not
/// re-adapt a converted return with `as_mut()`.
const CONVERTED_CALLEE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct slot {
    pub value: usize,
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct holder {
    pub only: slot,
}
#[no_mangle]
pub unsafe extern "C" fn holder_slot(mut h: *mut holder) -> *mut slot {
    return &mut (*h).only as *mut slot;
}
#[no_mangle]
pub unsafe extern "C" fn holder_set(mut h: *mut holder, mut v: usize) -> i32 {
    let mut s = holder_slot(h);
    (*s).value = v;
    return 1 as i32;
}
"#;

/// The second control: the same null-tested call result, but the local is
/// RETURNED. An untied view may not leave the frame that manufactured it
/// (R401-8), and the closed use vocabulary is what refuses it — buffer
/// `buffer_new_with_copy::self_0#6` and binn `binn_value::item#7` are this
/// shape at batch 18, and they stay held.
const ESCAPING_RECEIVER: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct item {
    pub kind: usize,
}
#[no_mangle]
pub unsafe extern "C" fn alloc_item(mut n: usize) -> *mut item {
    if n == 0 as usize {
        return 0 as *mut item;
    }
    return 0 as *mut item;
}
#[no_mangle]
pub unsafe extern "C" fn make_item(mut n: usize, mut kind: usize) -> *mut item {
    let mut it = alloc_item(n);
    if it.is_null() {
        return 0 as *mut item;
    }
    (*it).kind = kind;
    return it;
}
"#;

/// The third control: a FOREIGN callee's null-tested result (libtree
/// `parse_ld_config_file::comment#83`, `strchr`). A foreign return carries no
/// body to reason about and belongs to the contract families, so this arm
/// refuses it and the row stays held.
const FOREIGN_CALLEE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
unsafe extern "C" {
    fn strchr(s: *mut i8, c: i32) -> *mut i8;
}
#[no_mangle]
pub unsafe extern "C" fn strip_comment(mut line: *mut i8) -> i32 {
    let mut comment = strchr(line, '#' as i32);
    if comment.is_null() {
        return 0 as i32;
    }
    *comment = 0 as i8;
    return 1 as i32;
}
"#;

fn emitted(name: &str, source: &str, exposed: &[&str]) -> RewriteOutcome {
    use sha2::{Digest, Sha256};
    let dir = std::env::temp_dir().join(format!("crat-wave6l-a8-{name}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let root = dir.join("lib.rs");
    std::fs::write(&root, source).unwrap();
    let mut names = exposed
        .iter()
        .map(|name| (*name).to_owned())
        .collect::<Vec<_>>();
    names.sort();
    let digest = format!("{:x}", Sha256::digest(names.join("\n").as_bytes()));
    let configured_exposure = super::decision::exposure::ConfiguredExposureInput::checked(
        "wave6l-a8-fixture",
        names,
        digest,
    )
    .unwrap();
    super::rewrite_m1_path_with_emission_config(
        &root,
        A5Mode::PreciseReplay,
        Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        &super::EmissionRunConfig {
            configured_exposure,
        },
    )
}

fn compact(source: &str) -> String {
    source
        .chars()
        .filter(|c| !c.is_whitespace())
        .collect::<String>()
}

/// **W6L-A8-1 (RED first).** The null-tested receiver of a raw-returning local
/// callee takes `Option<&mut T>` from `as_mut()`, its null test becomes
/// `is_none()`, and the field write goes through the Option. The callee keeps
/// its raw return.
#[test]
fn w6l_null_tested_call_result_takes_an_option_receiver() {
    let RewriteOutcome::Emitted {
        source,
        reverted_count,
        degradations,
        ..
    } = emitted("lil-register", LIL_REGISTER, &["add_func", "lil_register"])
    else {
        panic!("lil_register fixture degraded to a non-emitting outcome");
    };
    println!("W6L-A8-1-EMITTED\n{source}\nW6L-A8-1-END\n{degradations:?}");
    assert_eq!(reverted_count, 0, "{degradations:?}");
    let text = compact(&source);
    assert!(
        text.contains("letmutcmd:Option<&mutcrate::lil_func>="),
        "the receiver did not take the adapted Option declaration: {text}"
    );
    assert!(
        text.contains(").as_mut();"),
        "the declaration's value is not the raw pointer's own null-to-Option API: {text}"
    );
    assert!(
        text.contains("cmd.is_none()"),
        "the null test was not adapted: {text}"
    );
    assert!(
        !text.contains("(*cmd).proc_0=proc_0;") && text.contains("cmd.unwrap()"),
        "the field write still goes through a raw deref: {text}"
    );
}

/// **The control.** A converted callee return is served by the existing
/// receiver path, not by this arm: the receiver's declaration names the
/// callee's delivered form and carries no `as_mut()` adapter.
#[test]
fn w6l_converted_callee_return_is_not_re_adapted() {
    let RewriteOutcome::Emitted {
        source,
        reverted_count,
        degradations,
        ..
    } = emitted(
        "converted-callee",
        CONVERTED_CALLEE,
        &["holder_slot", "holder_set"],
    )
    else {
        panic!("converted-callee fixture degraded to a non-emitting outcome");
    };
    println!("W6L-A8-CONTROL-EMITTED\n{source}\nW6L-A8-CONTROL-END\n{degradations:?}");
    assert_eq!(reverted_count, 0, "{degradations:?}");
    let text = compact(&source);
    assert!(
        !text.contains("holder_slot(h).as_mut()"),
        "a converted return was re-adapted by the A8 arm: {text}"
    );
}

/// Diagnostic probe (kept: it is the measurement this arm is built against).
#[test]
fn w6l_a8_probe_the_receiver_and_its_callee() {
    let observed = ::utils::compilation::run_compiler_on_str(LIL_REGISTER, |tcx| {
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let mut rows = Vec::new();
        for (subject, decision) in &table.entries {
            let failure: Option<LifetimeFailure> = ctx
                .lifetime_eligibility
                .failure((subject.fn_did, subject.hir_id));
            let value = super::decision::call_result_option::value(tcx, subject).is_some();
            let node = (subject.fn_did, subject.hir_id);
            let raw_uses = ctx
                .facts
                .raw_only_uses
                .get(&node)
                .map(|uses| uses.iter().map(|(op, _)| op.clone()).collect::<Vec<_>>());
            rows.push(format!(
                "{} :: {decision:?} :: lifetime_failure={failure:?} :: ty_span={} :: ctor={:?} :: a8_value={value} :: raw_uses={raw_uses:?} :: decl_shape={:?} :: null_init={} :: mutable={}",
                subject.label,
                subject.ty_span.is_some(),
                subject.ctor,
                subject.decl_shape,
                subject.null_init,
                subject.mutable,
            ));
        }
        let interfaces = table
            .return_interfaces
            .functions
            .iter()
            .map(|(did, interface)| {
                format!("{} -> {:?}", tcx.def_path_str(did.to_def_id()), interface.form)
            })
            .collect::<Vec<_>>();
        (rows, interfaces)
    })
    .unwrap();
    println!("W6L-A8-PROBE-ROWS");
    for row in &observed.0 {
        println!("  {row}");
    }
    println!("W6L-A8-PROBE-INTERFACES");
    for row in &observed.1 {
        println!("  {row}");
    }
}

/// **The escape control.** A returned receiver keeps its raw form: the untied
/// `as_mut()` view has no lifetime to hand to the caller, so the closed use
/// vocabulary refuses it and the row stays `return-not-adapted`.
#[test]
fn w6l_a8_escaping_receiver_stays_held() {
    let RewriteOutcome::Emitted {
        source,
        reverted_count,
        degradations,
        ..
    } = emitted(
        "escaping-receiver",
        ESCAPING_RECEIVER,
        &["alloc_item", "make_item"],
    )
    else {
        panic!("escaping-receiver fixture degraded to a non-emitting outcome");
    };
    println!("W6L-A8-ESCAPE-EMITTED\n{source}\nW6L-A8-ESCAPE-END\n{degradations:?}");
    assert_eq!(reverted_count, 0, "{degradations:?}");
    let text = compact(&source);
    assert!(
        !text.contains("letmutit:Option<"),
        "an escaping receiver was typed by the A8 arm: {text}"
    );
    assert!(
        degradations.iter().any(|d| d.subject == "make_item::it"
            && format!("{:?}", d.reason).contains("ReturnNotAdapted")),
        "{degradations:?}"
    );
}

/// **The foreign control.** `strchr`'s result is not this arm's value: the
/// callee has no body in the crate, so the row stays raw and held.
#[test]
fn w6l_a8_foreign_callee_result_is_refused() {
    let RewriteOutcome::Emitted {
        source,
        reverted_count,
        degradations,
        ..
    } = emitted("foreign-callee", FOREIGN_CALLEE, &["strip_comment"])
    else {
        panic!("foreign-callee fixture degraded to a non-emitting outcome");
    };
    println!("W6L-A8-FOREIGN-EMITTED\n{source}\nW6L-A8-FOREIGN-END\n{degradations:?}");
    assert_eq!(reverted_count, 0, "{degradations:?}");
    let text = compact(&source);
    assert!(
        !text.contains("letmutcomment:Option<"),
        "a foreign callee's result was typed by the A8 arm: {text}"
    );
}

/// **Review r1 (R785), the base arm's own hazard.** `as_mut()` makes the
/// `&mut T` at the declaration; the input had no reference until each deref.
/// A write to the pointee through ANOTHER pointer in between (here `(*l).cmd`'s
/// element, which is the same object when `add_func` returns it) disables
/// that reference under Tree Borrows, and the later write through it is UB.
const WRITE_BETWEEN: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct lil_func {
    pub proc_0: usize,
    pub name: *mut i8,
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct lil {
    pub cmds: usize,
    pub cmd: *mut *mut lil_func,
}
#[no_mangle]
pub unsafe extern "C" fn add_func(mut l: *mut lil, mut name: *mut i8) -> *mut lil_func {
    if (*l).cmds == 0 as usize {
        return 0 as *mut lil_func;
    }
    return *((*l).cmd).offset(0 as isize);
}
#[no_mangle]
pub unsafe extern "C" fn lil_register(mut l: *mut lil, mut name: *mut i8, mut proc_0: usize) -> i32 {
    let mut cmd = add_func(l, name);
    if cmd.is_null() {
        return 0 as i32;
    }
    (**((*l).cmd).offset(0 as isize)).proc_0 = 0 as usize;
    (*cmd).proc_0 = proc_0;
    return 1 as i32;
}
"#;

/// **Review r1 (R785), the second Tree Borrows case.** A write through the
/// view makes it Active; a read of the same object through another pointer
/// then freezes it, and the next write through the view is UB.
const READ_BETWEEN_WRITES: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct lil_func {
    pub proc_0: usize,
    pub name: *mut i8,
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct lil {
    pub cmds: usize,
    pub cmd: *mut *mut lil_func,
}
#[no_mangle]
pub unsafe extern "C" fn add_func(mut l: *mut lil, mut name: *mut i8) -> *mut lil_func {
    if (*l).cmds == 0 as usize {
        return 0 as *mut lil_func;
    }
    return *((*l).cmd).offset(0 as isize);
}
#[no_mangle]
pub unsafe extern "C" fn lil_register(mut l: *mut lil, mut name: *mut i8, mut proc_0: usize) -> usize {
    let mut cmd = add_func(l, name);
    if cmd.is_null() {
        return 0 as usize;
    }
    (*cmd).proc_0 = proc_0;
    let mut seen = (**((*l).cmd).offset(0 as isize)).proc_0;
    (*cmd).proc_0 = seen.wrapping_add(1 as usize);
    return seen;
}
"#;

fn receiver_stays_held(name: &str, source: &str, subject: &str, local: &str) {
    let RewriteOutcome::Emitted {
        source,
        reverted_count,
        degradations,
        ..
    } = emitted(name, source, &["add_func", "lil_register"])
    else {
        panic!("{name} degraded to a non-emitting outcome");
    };
    println!("W6L-WINDOW-{name}\n{source}\nW6L-WINDOW-END\n{degradations:?}");
    assert_eq!(reverted_count, 0, "{degradations:?}");
    let text = compact(&source);
    assert!(
        !text.contains(&format!("letmut{local}:Option<")),
        "{name}: the receiver was typed across a foreign access: {text}"
    );
    assert!(
        degradations.iter().any(|d| d.subject == subject
            && format!("{:?}", d.reason).contains("ReturnNotAdapted")),
        "{degradations:?}"
    );
}

/// **RED (review r1):** a foreign write between the declaration and a deref
/// keeps the receiver raw.
#[test]
fn w6l_window_foreign_write_before_the_deref_keeps_the_receiver_raw() {
    receiver_stays_held("write-between", WRITE_BETWEEN, "lil_register::cmd", "cmd");
}

/// **RED (review r1):** a foreign read between two writes through the view
/// keeps the receiver raw.
#[test]
fn w6l_window_foreign_read_between_writes_keeps_the_receiver_raw() {
    receiver_stays_held(
        "read-between-writes",
        READ_BETWEEN_WRITES,
        "lil_register::cmd",
        "cmd",
    );
}

/// lil `lil_find_var` + `lil_get_var_or` (subject `lil_get_var_or::var#5`,
/// delivered `optional` at batch 54): the view is only read, and the call
/// through the callback runs after its last use.
const GET_VAR_OR: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct var_t {
    pub v: usize,
    pub env: usize,
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct lil {
    pub rootenv: usize,
    pub vars: *mut *mut var_t,
    pub callback: [Option<unsafe extern "C" fn(*mut lil, *mut usize) -> i32>; 8],
}
#[no_mangle]
pub unsafe extern "C" fn lil_find_var(mut l: *mut lil) -> *mut var_t {
    if (*l).rootenv == 0 as usize {
        return 0 as *mut var_t;
    }
    return *((*l).vars).offset(0 as isize);
}
#[no_mangle]
pub unsafe extern "C" fn lil_get_var_or(mut l: *mut lil, mut defvalue: usize) -> usize {
    let mut var = lil_find_var(l);
    let mut retval = if !var.is_null() { (*var).v } else { defvalue };
    if ((*l).callback[7 as usize]).is_some() && (var.is_null() || (*var).env == (*l).rootenv) {
        let mut proc_0 = (*l).callback[7 as usize];
        let mut newretval = retval;
        if proc_0.expect("non-null function pointer")(l, &mut newretval) != 0 {
            retval = newretval;
        }
    }
    return retval;
}
"#;

/// **Precision (review r1 of R785), from the corpus row:** what runs after the
/// view's last use cannot reach it, so the window ends there; a read-only
/// view beside foreign reads stays typed.
#[test]
fn w6l_window_ends_at_the_last_use() {
    let RewriteOutcome::Emitted {
        source,
        reverted_count,
        degradations,
        ..
    } = emitted(
        "get-var-or",
        GET_VAR_OR,
        &["lil_find_var", "lil_get_var_or"],
    )
    else {
        panic!("get-var-or degraded to a non-emitting outcome");
    };
    println!("W6L-WINDOW-GETVAR\n{source}\nW6L-WINDOW-END\n{degradations:?}");
    assert_eq!(reverted_count, 0, "{degradations:?}");
    let text = compact(&source);
    assert!(
        text.contains("letmutvar:Option<&mutcrate::var_t>=")
            || text.contains("letmutvar:Option<&crate::var_t>="),
        "the read-only view was not typed: {text}"
    );
}

/// **Review of the quiet window, finding 1:** a local ARRAY decayed with
/// `as_mut_ptr()` (c2rust's form) is never `&`-borrowed in HIR, yet the view
/// points into it: `buf[0] = 1` in the window is a foreign write.
const ARRAY_DECAY_WRITE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct holder {
    pub n: i32,
    pub p: *mut i32,
}
#[no_mangle]
pub unsafe extern "C" fn get(mut h: *mut holder) -> *mut i32 {
    if (*h).n == 0 as i32 {
        return 0 as *mut i32;
    }
    return (*h).p;
}
#[no_mangle]
pub unsafe extern "C" fn fill(mut n: i32) -> i32 {
    let mut buf: [i32; 4] = [0 as i32; 4];
    let mut h = holder { n: n, p: buf.as_mut_ptr() };
    let mut q = get(&mut h);
    if q.is_null() {
        return 0 as i32;
    }
    buf[0 as usize] = 1 as i32;
    *q = 2 as i32;
    return buf[0 as usize];
}
"#;

/// **Finding 2:** a STATIC read between two writes through the view freezes
/// it when the view points into the static.
const STATIC_READ_BETWEEN_WRITES: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments, static_mut_refs)]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct entry {
    pub a: i32,
}
pub static mut TABLE: [entry; 4] = [entry { a: 0 }; 4];
#[no_mangle]
pub unsafe extern "C" fn get(mut i: i32) -> *mut entry {
    if i < 0 as i32 {
        return 0 as *mut entry;
    }
    return TABLE.as_mut_ptr().offset(i as isize);
}
#[no_mangle]
pub unsafe extern "C" fn bump(mut i: i32) -> i32 {
    let mut q = get(i);
    if q.is_null() {
        return 0 as i32;
    }
    (*q).a = 1 as i32;
    let mut n = TABLE[i as usize].a;
    (*q).a = n + 1 as i32;
    return n;
}
"#;

/// **Finding 3:** a raw pointer taken from the view (`addr_of_mut!`) outlives
/// the cut and carries the view's tag; a foreign write after the last use
/// disables it and the later write through the raw pointer is UB.
const RAW_ADDRESS_OF_VIEW: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct holder {
    pub n: i32,
    pub p: *mut holder,
}
#[no_mangle]
pub unsafe extern "C" fn get(mut h: *mut holder) -> *mut holder {
    if (*h).n == 0 as i32 {
        return 0 as *mut holder;
    }
    return (*h).p;
}
#[no_mangle]
pub unsafe extern "C" fn poke(mut target: *mut holder) -> i32 {
    let mut h = holder { n: 1 as i32, p: target };
    let mut q = get(&mut h);
    if q.is_null() {
        return 0 as i32;
    }
    let mut r = core::ptr::addr_of_mut!((*q).n);
    (*target).n = 5 as i32;
    *r = 7 as i32;
    return (*target).n;
}
"#;

fn view_not_typed(name: &str, source: &str, exposed: &[&str], local: &str) {
    let RewriteOutcome::Emitted {
        source,
        reverted_count,
        degradations,
        ..
    } = emitted(name, source, exposed)
    else {
        panic!("{name} degraded to a non-emitting outcome");
    };
    println!("W6L-WINDOW2-{name}\n{source}\nW6L-WINDOW2-END\n{degradations:?}");
    assert_eq!(reverted_count, 0, "{degradations:?}");
    let text = compact(&source);
    assert!(
        !text.contains(&format!("letmut{local}:Option<")),
        "{name}: the view was typed: {text}"
    );
}

/// **RED (review of the quiet window, finding 1).**
#[test]
fn w6l_window_a_write_to_a_decayed_local_array_keeps_the_receiver_raw() {
    view_not_typed(
        "array-decay-write",
        ARRAY_DECAY_WRITE,
        &["get", "fill"],
        "q",
    );
}

/// **RED (finding 2).**
#[test]
fn w6l_window_a_static_read_between_writes_keeps_the_receiver_raw() {
    view_not_typed(
        "static-read-between-writes",
        STATIC_READ_BETWEEN_WRITES,
        &["get", "bump"],
        "q",
    );
}

/// **RED (finding 3).**
#[test]
fn w6l_window_a_raw_address_of_the_view_keeps_the_receiver_raw() {
    view_not_typed(
        "raw-address-of-view",
        RAW_ADDRESS_OF_VIEW,
        &["get", "poke"],
        "q",
    );
}

/// **R791-4 (b):** the view is dereferenced on SOME non-null paths only
/// (`if n > 2 { *q = 2 }`), so `as_mut()` at the declaration would assert a
/// dereferenceability the input does not rely on where `n <= 2`. (buffer's
/// `test_buffer_slice__range_error::a`, never dereferenced at all, is the
/// corpus row of this class.)
const PARTIAL_DEREFERENCE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct holder {
    pub n: i32,
    pub p: *mut i32,
}
#[no_mangle]
pub unsafe extern "C" fn get(mut h: *mut holder) -> *mut i32 {
    if (*h).n == 0 as i32 {
        return 0 as *mut i32;
    }
    return (*h).p;
}
#[no_mangle]
pub unsafe extern "C" fn probe(mut n: i32) -> i32 {
    let mut buf: [i32; 4] = [0 as i32; 4];
    let mut h = holder { n: n, p: buf.as_mut_ptr() };
    let mut q = get(&mut h);
    if q.is_null() {
        return 1 as i32;
    }
    if n > 2 as i32 {
        *q = 2 as i32;
    }
    return 0 as i32;
}
"#;

/// **R791-4 (a), lil `lil_get_var_or`'s shape:** a `char` pointer (the type
/// rule's wildcard: it may point into the view's pointee) is live across the
/// declaration — used after it — so the declaration's whole-`T` retag may
/// freeze what it points through.
const LIVE_CHAR_POINTER: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct var_t {
    pub v: usize,
    pub env: usize,
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct lil {
    pub rootenv: usize,
    pub vars: *mut *mut var_t,
}
#[no_mangle]
pub unsafe extern "C" fn lil_find_var(mut l: *mut lil) -> *mut var_t {
    if (*l).rootenv == 0 as usize {
        return 0 as *mut var_t;
    }
    return *((*l).vars).offset(0 as isize);
}
#[no_mangle]
pub unsafe extern "C" fn first_byte(mut s: *const i8) -> usize {
    return *s as usize;
}
#[no_mangle]
pub unsafe extern "C" fn lil_get_var_or(mut l: *mut lil, mut name: *const i8, mut defvalue: usize) -> usize {
    let mut var = lil_find_var(l);
    let mut retval = if !var.is_null() { (*var).v } else { defvalue };
    return retval + first_byte(name);
}
"#;

/// **RED (R801-2, USER: P7 extended).** Rule (b) of R791-4 is no longer a
/// refusal: a view that a non-null path does not dereference is delivered,
/// and its declaration carries the premise's receipt
/// (`premise=bridge-dereferenceable`, site kind `declaration-view`).
#[test]
fn w6l_window_a_view_not_dereferenced_on_every_non_null_path_rides_p7() {
    let RewriteOutcome::Emitted {
        source,
        reverted_count,
        degradations,
        raw_boundary_artifacts,
        ..
    } = emitted(
        "partial-dereference",
        PARTIAL_DEREFERENCE,
        &["get", "probe"],
    )
    else {
        panic!("partial-dereference degraded to a non-emitting outcome");
    };
    assert_eq!(reverted_count, 0, "{degradations:?}");
    let text = compact(&source);
    assert!(
        text.contains("letmutq:Option<&muti32>="),
        "the view was not delivered: {text}"
    );
    let receipts = &raw_boundary_artifacts.premise_receipts;
    assert!(
        receipts.lines().any(|row| row.contains("probe::q")
            && row.contains("premise=bridge-dereferenceable")
            && row.contains("declaration-view")),
        "no P7 receipt for the view: {receipts}"
    );
}

/// **Control (R801-2):** a view every non-null path dereferences carries no
/// receipt (lil `lil_register::cmd`'s shape).
#[test]
fn w6l_window_a_dereferenced_view_carries_no_p7_receipt() {
    let RewriteOutcome::Emitted {
        raw_boundary_artifacts,
        ..
    } = emitted(
        "lil-register-p7",
        LIL_REGISTER,
        &["add_func", "lil_register"],
    )
    else {
        panic!("lil_register fixture degraded to a non-emitting outcome");
    };
    assert!(
        !raw_boundary_artifacts
            .premise_receipts
            .contains("premise=bridge-dereferenceable"),
        "{}",
        raw_boundary_artifacts.premise_receipts
    );
}

/// **RED (R791-4 (a)).**
#[test]
fn w6l_window_a_live_char_pointer_keeps_the_receiver_raw() {
    view_not_typed(
        "live-char-pointer",
        LIVE_CHAR_POINTER,
        &["lil_find_var", "first_byte", "lil_get_var_or"],
        "var",
    );
}
