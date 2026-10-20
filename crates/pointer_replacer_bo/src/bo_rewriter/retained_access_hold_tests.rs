//! **R864-3 (relay 299; era-5c 154 / 154a) — the retained-access check of record as
//! the joint fixpoint's fourth predicate.** The positive control (a self-reference
//! the check names is held on the settled table) and one witness per filter (era-5c
//! 154's fixtures). The filters' faults are measured by disabling each in a build of
//! its own (main 194), not by markers in the production code.

use rustc_hash::FxHashMap;

use super::{A5Mode, WholeProgramAttestation};

const ALLOW: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments, unused_variables, non_snake_case, non_camel_case_types)]\n";

/// Every subject's settled decision, `label => Debug`.
fn decisions(source: &str) -> FxHashMap<String, String> {
    ::utils::compilation::run_compiler_on_str(source, |tcx| {
        let (table, _) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("decision table");
        table
            .entries
            .iter()
            .map(|(subject, decision)| (subject.label.clone(), format!("{decision:?}")))
            .collect()
    })
    .expect("fixture compiles")
}

fn held(decisions: &FxHashMap<String, String>, subject: &str) -> bool {
    decisions
        .get(subject)
        .unwrap_or_else(|| panic!("no {subject}: {decisions:#?}"))
        .contains("RetainedAlias")
}

/// The positive control: libtree's shape, a self-reference stored by `init` and used
/// by `append` within one call from outside, is held on the settled table (155 §4:
/// the hook-free line left `append::v` `Ref { mutable: true }`). The field carries raw
/// evidence here (a byte write through it), as libtree's does; the shape without it is
/// pinned below.
const SELF_REFERENCE: &str = r#"
#[repr(C)] pub struct small_vec { pub p: *mut u64, pub n: usize, pub buf: [u64; 16] }
pub unsafe fn init(v: *mut small_vec) { (*v).p = (*v).buf.as_mut_ptr(); (*v).n = 0; }
pub unsafe fn append(v: *mut small_vec, x: u64) {
    *(*v).p.offset((*v).n as isize) = x;
    *((*v).p as *mut u8) = 0;
    (*v).n += 1;
}
pub unsafe fn run(v: *mut small_vec) { init(v); append(v, 1); }
"#;

#[test]
fn r864_3_a_self_reference_is_held_on_the_settled_table() {
    let d = decisions(&format!("{ALLOW}{SELF_REFERENCE}"));
    assert!(held(&d, "append::v"), "{d:#?}");
    assert!(d["append::v"].contains("evident:self-reference"), "{d:#?}");
}

/// era-5c's own `W2_RUN` (main 194a §3; R878-1; era-5c 158 / 158a): with no raw evidence
/// on `small_vec.p` the model decides it `Ref`, and the check of record used to clear
/// `append::v` on that reading while the rewriter keeps the field raw. The check's guard
/// now reads the applied field transactions (`after_deliveries`, relay 305), and no
/// transaction delivers `small_vec.p`: held.
const SELF_REFERENCE_UNMARKED: &str = r#"
#[repr(C)] pub struct small_vec { pub p: *mut u64, pub n: usize, pub buf: [u64; 16] }
pub unsafe fn init(v: *mut small_vec) { (*v).p = (*v).buf.as_mut_ptr(); (*v).n = 0; }
pub unsafe fn append(v: *mut small_vec, x: u64) {
    *(*v).p.offset((*v).n as isize) = x;
    (*v).n += 1;
}
pub unsafe fn run(v: *mut small_vec) { init(v); append(v, 1); }
"#;

#[test]
fn r864_3_libtrees_self_reference_is_held_whatever_the_model_decides_the_field() {
    let d = decisions(&format!("{ALLOW}{SELF_REFERENCE_UNMARKED}"));
    assert!(held(&d, "append::v"), "{d:#?}");
    assert!(d["append::v"].contains("evident:self-reference"), "{d:#?}");
}

/// Filter 1: a formal moved into the program's storage as an owner (wave-6a's C2
/// store sink) is a move, not an alias.
const STORE_CHAIN: &str = r#"
extern "C" { fn calloc(n: usize, size: usize) -> *mut core::ffi::c_void; }
#[repr(C)]
pub struct slot { pub key: *mut i8, pub value: i32 }
unsafe extern "C" fn slot_set(mut slots: *mut slot, mut index: usize, mut key: *mut i8, mut value: i32) {
    *key.offset(0 as isize) = 0 as i8;
    (*slots.offset(index as isize)).value = value;
    (*slots.offset(index as isize)).key = key;
}
pub unsafe extern "C" fn table_put(mut slots: *mut slot, mut index: usize) {
    let mut key = calloc(8 as usize, ::std::mem::size_of::<i8>()) as *mut i8;
    *key.offset(1 as isize) = 65 as i8;
    slot_set(slots, index, key, 7 as i32);
}
"#;

#[test]
fn r864_3_filter1_an_owning_decision_is_not_held() {
    let d = decisions(&format!("{ALLOW}{STORE_CHAIN}"));
    assert!(!held(&d, "slot_set::key"), "{d:#?}");
}

/// Filter 3: a formal stored into a field the rewriter delivers as a reference (ht's
/// iterator).
const HT: &str = include_str!("wave6f_fixture_ht.rs");

#[test]
fn r864_3_filter3_a_store_into_a_delivered_field_is_not_held() {
    let d = decisions(HT);
    assert!(!held(&d, "ht_iterator::table"), "{d:#?}");
}

/// Filter 2 at a block with no bridge (binn's `GetValue` shape). Restated (relay 305;
/// the stand-in review's round 3, R3-2; main 197 / 198): `caller`'s site into `GetValue`
/// is `Blocked{PositiveRetention}` at a target that converts, so nothing renders there and
/// it reads no retention; `GetValue` keeps `buf` in `Blob.ptr`, raw, and `caller::buf` is
/// held. The positive witness is the waived foreign site below.
const RETAINED: &str = r#"
#[repr(C)]
pub struct Blob { pub ptr: *mut u8, pub len: i32 }
unsafe fn GetValue(mut p: *mut u8, mut value: *mut Blob) -> i32 {
    if value.is_null() { return 0; }
    (*value).ptr = p;
    (*value).len = *p.offset(0 as isize) as i32;
    return 1;
}
pub unsafe fn caller(mut buf: *mut u8, mut value: *mut Blob) -> i32 {
    if buf.is_null() { return 0; }
    *buf.offset(0 as isize) = 1 as u8;
    return GetValue(buf, value);
}
"#;

#[test]
fn r864_3_filter2_a_block_with_no_bridge_reads_no_retention() {
    let d = decisions(&format!("{ALLOW}{RETAINED}"));
    assert!(held(&d, "caller::buf"), "{d:#?}");
}

/// Filter 2's positive witness: a foreign call the check reads as keeping its argument,
/// at the subject's own site, where the tier spends the tier-2 waiver on a bridge: the
/// tier's reading stands for that store, receipted at that site.
const STASHED: &str = r#"
extern "C" { fn stash(p: *mut u8); }
pub unsafe fn caller(mut buf: *mut u8) -> u8 {
    *buf = 1;
    stash(buf);
    *buf
}
"#;

#[test]
fn r864_3_filter2_a_waived_bridge_reads_its_own_call() {
    let d = decisions(&format!("{ALLOW}{STASHED}"));
    assert!(!held(&d, "caller::buf"), "{d:#?}");
    assert!(
        d["caller::buf"].starts_with("Ref") || d["caller::buf"].starts_with("Slice"),
        "{d:#?}"
    );
}

/// The stand-in review's round 2, R2-1 (relay 304, R878-1: E2 / E3 are never exempt):
/// filter 2 is a reading of one site's retention, not of the subject. A foreign call at
/// the subject's own site that the tier waives (`trace`: retention unknown, the tier-2
/// waiver) must not exempt the self-reference the check names (the positive control
/// plus that one call).
const SELF_REFERENCE_TRACED: &str = r#"
extern "C" { fn trace(p: *mut core::ffi::c_void); }
#[repr(C)] pub struct small_vec { pub p: *mut u64, pub n: usize, pub buf: [u64; 16] }
pub unsafe fn init(v: *mut small_vec) { (*v).p = (*v).buf.as_mut_ptr(); (*v).n = 0; }
pub unsafe fn append(v: *mut small_vec, x: u64) {
    trace(v as *mut core::ffi::c_void);
    *(*v).p.offset((*v).n as isize) = x;
    *((*v).p as *mut u8) = 0;
    (*v).n += 1;
}
pub unsafe fn run(v: *mut small_vec) { init(v); append(v, 1); }
"#;

#[test]
fn r864_3_round2_a_waived_site_does_not_exempt_a_self_reference() {
    let d = decisions(&format!("{ALLOW}{SELF_REFERENCE_TRACED}"));
    assert!(held(&d, "append::v"), "{d:#?}");
    assert!(d["append::v"].contains("evident:self-reference"), "{d:#?}");
}

/// R2-1's second shape: the subject's own derived store into a field the rewriter keeps
/// raw (a place expression's address: wave-6f's `store-source-raw-expression`) is a
/// retained raw pointer whatever the tier read at another of the subject's calls.
const OWN_STORE_TRACED: &str = r#"
extern "C" { fn trace(p: *mut core::ffi::c_void); }
#[repr(C)] pub struct S { pub x: i32, pub y: i32 }
#[repr(C)] pub struct H { pub f: *mut i32 }
pub unsafe fn bind(h: *mut H, s: *mut S) {
    trace(s as *mut core::ffi::c_void);
    (*h).f = &mut (*s).x;
}
pub unsafe fn bump(h: *mut H) { *(*h).f += 1; }
pub unsafe fn run(h: *mut H, s: *mut S) { bind(h, s); (*s).x = 0; bump(h); }
"#;

#[test]
fn r864_3_round2_a_waived_site_does_not_exempt_an_own_store() {
    let d = decisions(&format!("{ALLOW}{OWN_STORE_TRACED}"));
    assert!(
        !d["bind::s"].starts_with("Ref") && !d["bind::s"].starts_with("InferredRef"),
        "{d:#?}"
    );
}

/// The stand-in review's round 3, R3-1: the tier's reading at one of the subject's
/// calls (`note`, T2 with a bridge) is no reading of a callee store at another call that
/// has no tier site (`keep` takes the subject inside an aggregate). `H.f` keeps the
/// pointer and `run` writes through `o` before reading through it.
const CALLEE_STORE_UNSITED: &str = r#"
#[repr(C)] pub struct S { pub x: i32 }
#[repr(C)] #[derive(Copy, Clone)] pub struct Pair { pub a: *mut S, pub n: i32 }
#[repr(C)] pub struct H { pub f: *mut S }
static mut LAST: *mut S = 0 as *mut S;
unsafe fn note(p: *mut S) { LAST = p; }
unsafe fn keep(p: Pair, h: *mut H) { (*h).f = p.a; }
pub unsafe fn f(s: *mut S, h: *mut H) { note(s); keep(Pair { a: s, n: 0 }, h); }
pub unsafe fn run(o: *mut S, h: *mut H) { f(o, h); (*o).x = 2; let _y = (*(*h).f).x; }
"#;

#[test]
fn r864_3_round3_a_reading_at_one_call_is_none_at_an_unsited_one() {
    let d = decisions(&format!("{ALLOW}{CALLEE_STORE_UNSITED}"));
    assert!(
        !d["f::s"].starts_with("Ref") && !d["f::s"].starts_with("InferredRef"),
        "{d:#?}"
    );
}

/// The review's round 3, R3-2: a protected formal released on its callee's receipt. `g`
/// hands `p` to `keep` (stored into a static, the tier-2 waiver at `g`'s site), and `f`
/// then frees what the static holds while its own `s` would be a protected `&mut S`.
const RELEASED_THEN_FREED: &str = r#"
extern "C" { fn free(p: *mut core::ffi::c_void); }
#[repr(C)] pub struct S { pub x: i32 }
static mut LIST: [*mut S; 8] = [0 as *mut S; 8];
static mut N: usize = 0;
unsafe fn keep(q: *mut S) { LIST[N] = q; N += 1; }
unsafe fn g(p: *mut S) { (*p).x += 1; keep(p); }
unsafe fn free_all() { while N > 0 { N -= 1; free(LIST[N] as *mut core::ffi::c_void); } }
pub unsafe fn f(s: *mut S) { g(s); free_all(); }
"#;

#[test]
fn r864_3_round3_a_formal_is_not_released_on_its_callees_receipt() {
    let d = decisions(&format!("{ALLOW}{RELEASED_THEN_FREED}"));
    assert!(
        !d["f::s"].starts_with("Ref") && !d["f::s"].starts_with("InferredRef"),
        "{d:#?}"
    );
}

/// The stand-in review's round 4, R4-1: the check emits a formal's callee store only when
/// the formal stores nothing itself; here its own store is a foreign `stash` the tier
/// waives at its own bridged site, and the in-program `keep` takes the subject inside an
/// aggregate (no tier site) and keeps it in `H.f`.
const OWN_STORE_HIDES_CALLEE_STORE: &str = r#"
#[repr(C)] pub struct S { pub x: i32 }
#[repr(C)] #[derive(Copy, Clone)] pub struct Pair { pub a: *mut S, pub n: i32 }
#[repr(C)] pub struct H { pub f: *mut S }
extern "C" { fn stash(p: *mut S); }
unsafe fn keep(p: Pair, h: *mut H) { (*h).f = p.a; }
pub unsafe fn f(s: *mut S, h: *mut H) { stash(s); keep(Pair { a: s, n: 0 }, h); }
pub unsafe fn run(o: *mut S, h: *mut H) { f(o, h); (*o).x = 2; let _y = (*(*h).f).x; }
"#;

#[test]
fn r864_3_round4_an_own_store_does_not_hide_a_callee_store() {
    let d = decisions(&format!("{ALLOW}{OWN_STORE_HIDES_CALLEE_STORE}"));
    assert!(
        !d["f::s"].starts_with("Ref") && !d["f::s"].starts_with("InferredRef"),
        "{d:#?}"
    );
}

/// The review's round 4, R4-2 (ruling-level): binn's KEEP shape with its derived-global
/// store (`KEPT = p`, a known retention the tier waives at `probe`'s site: the tier-2
/// retention waiver, R481-2) and a caller that writes through its parent after `probe`
/// returns, then reads through the kept pointer. The retention waiver's text excludes a
/// use while the reference is live, not this one: R889-1 (relay 307) rules closure (i),
/// filter 2 reads a T2 only where its waiver is the c-aliasing one.
const KEPT_AFTER_THE_REFERENCE: &str = r#"
#[repr(C)]
pub struct binn { pub header: i32, pub type_0: i32, pub size: i32, pub ptr: *mut core::ffi::c_void }
static mut KEPT: *mut u8 = 0 as *mut u8;
unsafe fn keep(mut p: *mut u8, mut out: *mut binn) -> i32 {
    (*out).type_0 = *p as i32;
    (*out).ptr = p as *mut core::ffi::c_void;
    KEPT = p.cast::<i8>() as *mut u8;
    return 1 as i32;
}
pub unsafe fn probe(mut s: *mut u8) -> i32 {
    let mut out = binn { header: 0, type_0: 0, size: 0, ptr: 0 as *mut core::ffi::c_void };
    if keep(s, &mut out) == 0 as i32 { return 0 as i32; }
    return out.type_0;
}
pub unsafe fn run(b: *mut u8) -> u8 { probe(b); *b = 5; *KEPT }
"#;

#[test]
fn r864_3_round4_a_retention_waiver_does_not_cover_a_later_use() {
    let d = decisions(&format!("{ALLOW}{KEPT_AFTER_THE_REFERENCE}"));
    assert!(
        !d["probe::s"].starts_with("Ref") && !d["probe::s"].starts_with("Slice"),
        "{d:#?}"
    );
}

/// The stand-in review's round 5, R5-1 (filter 2's scope: the seat's, main 198a): the
/// check's family carries a program call's integer result whose return derives from the
/// argument (`addr`), so `x as *mut S` reaches `keep2`'s argument 1, which keeps it in
/// `H.f`; the host's carriers stop at the integer call result, so the per-(call, argument)
/// coverage reads only `keep2`'s argument 0 (a c-aliasing T2) and exempts the unsited
/// callee store. Constructed by the review; on this fixture `f::s` is held at bdb28f335
/// (pinned, not red), so the shape stays the seat's question (MAX-3 on filter 2's scope).
const INTEGER_ROUND_TRIP_KEPT: &str = r#"
#[repr(C)] pub struct S { pub x: i32 }
#[repr(C)] pub struct H { pub f: *mut S }
unsafe fn addr(p: *mut S) -> usize { p as usize }
unsafe fn keep2(p: *mut S, q: *mut S, h: *mut H) { let _a = p as usize; (*h).f = q; }
pub unsafe fn f(s: *mut S, h: *mut H) { let x = addr(s); keep2(s, x as *mut S, h); }
pub unsafe fn run(o: *mut S, h: *mut H) { f(o, h); (*o).x = 2; let _y = (*(*h).f).x; }
"#;

#[test]
fn r864_3_round5_an_integer_round_trip_to_a_keeper_is_not_covered() {
    let d = decisions(&format!("{ALLOW}{INTEGER_ROUND_TRIP_KEPT}"));
    assert!(
        !d["f::s"].starts_with("Ref") && !d["f::s"].starts_with("InferredRef"),
        "{d:#?}"
    );
}

/// **Relay 315 item 1 (main 207 / 208): a retained-access hold does not hold its
/// class.** `append::v` is held (`held:retained-alias`: the self-reference `init`
/// stores and `append` uses), and `out` / `y` are ordinary formals of the same
/// function. The hold decides `v` raw on the settled table, in the input's raw form,
/// after co-conversion set the class's arm requirements — D5 (c)'s reading of every
/// settled-table hold (relay 297) — so it neither requires an arm of its class nor
/// blocks it: `out` and `y` deliver (at 57's census the class was held,
/// `blocked-subject:held:retained-alias`: brotli's 62, quadtree's `split_node_` /
/// `insert_` and the Box rows behind them). The controls: `v` stays raw end to end,
/// and `other`'s `w`, handed whole to the held formal, stays held
/// (`into_held_formals` reads the retained holds).
const RETAINED_BESIDE_NEIGHBOURS: &str = r#"
#[repr(C)] pub struct small_vec { pub p: *mut u64, pub n: usize, pub buf: [u64; 16] }
pub unsafe fn init(v: *mut small_vec) { (*v).p = (*v).buf.as_mut_ptr(); (*v).n = 0; }
pub unsafe fn append(v: *mut small_vec, x: u64, out: *mut u64, y: *const u64) -> u64 {
    *(*v).p.offset((*v).n as isize) = x;
    (*v).n += 1;
    *out = x;
    *y
}
pub unsafe fn run(v: *mut small_vec) -> u64 {
    let mut last: u64 = 0;
    let k: u64 = 3;
    init(v);
    append(v, 1, &mut last, &k) + last
}
pub unsafe fn other(w: *mut small_vec) -> u64 {
    let mut z: u64 = 0;
    let k: u64 = 4;
    append(w, 2, &mut z, &k) + z
}
"#;

#[test]
fn r315_1_a_retained_access_hold_does_not_hold_its_class() {
    let source = format!("{ALLOW}{RETAINED_BESIDE_NEIGHBOURS}");
    let dir = std::env::temp_dir().join(format!("crat-r315-1-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("lib.rs"), &source).unwrap();
    let result = super::rewrite_m1_path(&dir.join("lib.rs"));
    let _ = std::fs::remove_dir_all(&dir);
    let super::RewriteOutcome::Emitted {
        source: out,
        degradations,
        ..
    } = result
    else {
        panic!("the fixture must emit")
    };
    println!("SOURCE\n{out}");
    for d in &degradations {
        println!("DEGRADED {} {}", d.subject, d.reason.key());
    }
    assert!(super::verify::type_checks_str(&out), "{out}");
    let reason = |subject: &str| {
        degradations
            .iter()
            .find(|d| d.subject == subject || d.subject.starts_with(&format!("{subject}#")))
            .map(|d| d.reason.key().to_owned())
    };
    let signature = |function: &str| {
        out.lines()
            .find(|line| line.contains(&format!("fn {function}(")))
            .unwrap_or_default()
            .split_whitespace()
            .collect::<String>()
    };
    // The control: the held subject stays raw end to end.
    assert_eq!(reason("append::v").as_deref(), Some("held:retained-alias"));
    assert!(signature("append").contains("v:*mutsmall_vec"), "{out}");
    // The control: a caller's binding handed whole to the held formal stays held,
    // by the cascade (`run::v` is held by the check itself: `init` stores into it).
    assert_eq!(reason("other::w").as_deref(), Some("held:into-held-formal"));
    assert_eq!(reason("run::v").as_deref(), Some("held:retained-alias"));
    assert!(signature("other").contains("w:*mutsmall_vec"), "{out}");
    // The neighbours deliver: the hold does not hold its class.
    assert_eq!(reason("append::out"), None, "{degradations:#?}");
    assert_eq!(reason("append::y"), None, "{degradations:#?}");
    assert!(signature("append").contains("out:&mutu64"), "{out}");
    assert!(signature("append").contains("y:&u64"), "{out}");
}

/// The negative controls (the stand-in review of item 1, LOW-2): a neighbour that
/// reaches the retained memory stays raw without the class block — a formal handed
/// the held object's own buffer, and a local taken from the held object, live across
/// the write through `(*v).p`. The decision-level holds own them now: the class
/// block was never their backstop.
const NEIGHBOURS_INSIDE_THE_HELD_OBJECT: &str = r#"
#[repr(C)] pub struct small_vec { pub p: *mut u64, pub n: usize, pub buf: [u64; 16] }
pub unsafe fn init(v: *mut small_vec) { (*v).p = (*v).buf.as_mut_ptr(); (*v).n = 0; }
pub unsafe fn append(v: *mut small_vec, x: u64, out: *mut u64) -> usize {
    let mut q: *mut usize = &mut (*v).n;
    *(*v).p.offset((*v).n as isize) = x;
    *out = x;
    *q += 1;
    *q
}
pub unsafe fn run(v: *mut small_vec) -> usize {
    init(v);
    append(v, 1, (*v).buf.as_mut_ptr())
}
"#;

#[test]
fn r315_1_neighbours_inside_the_held_object_stay_raw() {
    let source = format!("{ALLOW}{NEIGHBOURS_INSIDE_THE_HELD_OBJECT}");
    let dir = std::env::temp_dir().join(format!("crat-r315-1n-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("lib.rs"), &source).unwrap();
    let result = super::rewrite_m1_path(&dir.join("lib.rs"));
    let _ = std::fs::remove_dir_all(&dir);
    let super::RewriteOutcome::Emitted {
        source: out,
        degradations,
        ..
    } = result
    else {
        panic!("the fixture must emit")
    };
    println!("SOURCE\n{out}");
    for d in &degradations {
        println!("DEGRADED {} {}", d.subject, d.reason.key());
    }
    assert!(super::verify::type_checks_str(&out), "{out}");
    let signature: String = out
        .lines()
        .find(|line| line.contains("fn append("))
        .unwrap_or_default()
        .split_whitespace()
        .collect();
    assert!(signature.contains("v:*mutsmall_vec"), "{out}");
    assert!(signature.contains("out:*mutu64"), "out stays raw: {out}");
    let flat: String = out.split_whitespace().collect();
    assert!(flat.contains("letmutq:*mutusize"), "q stays raw: {out}");
}
