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
