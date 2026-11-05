//! **R1130-1 (relay wave-6a/164): the read-modify-write temporary, restored**
//! (`rmw_relet`). Every fixture defines `__crat_rmw_relet_test`, the test-only
//! opt-in (the switch `CRAT_RMW_RELET` is process-global); the witnesses and the
//! faults run in ONE test because the fault knob is global too.

use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT: AtomicUsize = AtomicUsize::new(0);

fn emitted(text: &str) -> String {
    let dir = std::env::temp_dir().join(format!(
        "crat-w6a-164-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&dir).expect("fixture dir");
    let root = dir.join("lib.rs");
    std::fs::write(&root, text).expect("fixture root");
    let result = super::rewrite_m1_path(&root);
    let _ = std::fs::remove_dir_all(&dir);
    match result {
        super::RewriteOutcome::Emitted { source, .. } => {
            assert!(super::verify::type_checks_str(&source), "{source}");
            source
        }
        other => panic!("the fixture must emit: {other:?}"),
    }
}

/// As [`emitted`], but `None` where the fixture does not emit well-typed text
/// (a fault that breaks typing is then observed, not a panic).
fn emitted_or_none(text: &str) -> Option<String> {
    let dir = std::env::temp_dir().join(format!(
        "crat-w6a-164-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&dir).expect("fixture dir");
    let root = dir.join("lib.rs");
    std::fs::write(&root, text).expect("fixture root");
    let result = super::rewrite_m1_path(&root);
    let _ = std::fs::remove_dir_all(&dir);
    match result {
        super::RewriteOutcome::Emitted { source, .. }
            if super::verify::type_checks_str(&source) =>
        {
            Some(source)
        }
        _ => None,
    }
}

fn compact(s: &str) -> String {
    s.split_whitespace().collect()
}

const PRELUDE: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_camel_case_types)]\n\
    pub fn __crat_rmw_relet_test() {}\n\
    #[repr(C)]\n\
    pub struct z_t { pub used: usize, pub chars: *mut u32 }\n";

/// (a) libzahl: `(*a).used = ((*a).used).wrapping_sub(1)` on a raw formal (it
/// is stepped by an index of unknown sign, so it stays raw; the function's
/// class is kept — a fully withheld crate keeps its input bytes, R216).
const A: &str = "pub unsafe fn dec(mut a: *mut z_t, mut i: i32) -> usize {\n\
        let seen = a.offset(i as isize) as usize;\n\
        (*a).used = ((*a).used).wrapping_sub(1);\n\
        seen\n\
    }\n";

/// (b) a compound assignment through a step: `*p.offset(i) += 1`.
const B: &str = "pub unsafe fn bump(mut p: *mut i32, mut i: i32) -> usize {\n\
        let seen = p as usize;\n\
        *p.offset(i as isize) += 1;\n\
        seen\n\
    }\n";

/// (c) a safe root: `a` is delivered `&mut z_t`; untouched.
const C: &str = "pub unsafe fn dec_safe(mut a: *mut z_t) {\n\
        (*a).used = ((*a).used).wrapping_sub(1);\n\
    }\n";

/// (d) the RHS does not mention the place: untouched.
const D: &str = "pub unsafe fn clear(mut a: *mut z_t, mut i: i32) -> usize {\n\
        let seen = a.offset(i as isize) as usize;\n\
        (*a).used = 0;\n\
        seen\n\
    }\n";

/// (e) an index with a call: skipped (c2rust hoisted those itself).
const E: &str = "fn idx(i: i32) -> isize { i as isize }\n\
    pub unsafe fn bump_at(mut a: *mut z_t, mut i: i32) -> usize {\n\
        let seen = a.offset(i as isize) as usize;\n\
        *(*a).chars.offset(idx(i)) += 1;\n\
        seen\n\
    }\n";

/// (f) report 165b / R1160-1: the RHS reads another raw place, `*s.offset(i)`,
/// which may alias the place; under Tree Borrows the foreign read keeps the
/// temporary Reserved (Miri TB clean), so it is re-let. `n` is delivered, so the crate is not the
/// all-withheld round R216 leaves alone (the rule is reached, then refused); `s`
/// is kept raw like `a`, so no other edit claims the statement.
const F: &str = "pub unsafe fn sub_from(mut a: *mut z_t, mut s: *mut u32, mut i: i32, mut n: *mut i32) -> usize {\n\
        let seen = a.offset(i as isize) as usize;\n\
        let seen_s = s.offset(i as isize) as usize;\n\
        *(*a).chars.offset(i as isize) = (*(*a).chars.offset(i as isize)).wrapping_sub(*s.offset(i as isize));\n\
        *n = 0;\n\
        seen.wrapping_add(seen_s)\n\
    }\n";

/// (g) relay 166: the RHS calls a function, which may read the place; not re-let.
const G: &str = "fn peek(i: i32) -> u32 { i as u32 }\n\
    pub unsafe fn sub_peek(mut a: *mut z_t, mut i: i32, mut n: *mut i32) -> usize {\n\
        let seen = a.offset(i as isize) as usize;\n\
        *(*a).chars.offset(i as isize) = (*(*a).chars.offset(i as isize)).wrapping_sub(peek(i));\n\
        *n = 0;\n\
        seen\n\
    }\n";

/// (h) report 165d / R1160-1: the RHS reads a `static mut` the place may alias
/// (`p = &raw mut G`); a read, so re-let (Miri TB clean).
const H: &str = "pub static mut G: u32 = 0;\n\
    pub unsafe fn add_g(mut p: *mut u32, mut i: i32, mut n: *mut i32) -> usize {\n\
        let seen = p.offset(i as isize) as usize;\n\
        *p = (*p).wrapping_add(G);\n\
        *n = 0;\n\
        seen\n\
    }\n";

/// (i) report 165d / R1160-1: the RHS reads a local whose address is taken
/// (`q = &mut x` may be the place); a read, so re-let (Miri TB clean).
const I: &str = "pub unsafe fn add_x(mut p: *mut u32, mut i: i32, mut n: *mut i32) -> usize {\n\
        let mut x: u32 = 3;\n\
        let mut q: *mut u32 = &mut x;\n\
        let seen = p.offset(i as isize) as usize;\n\
        *p = (*p).wrapping_add(x);\n\
        *n = 0;\n\
        seen.wrapping_add(q as usize)\n\
    }\n";

/// (j) a field of a `packed` struct: `&mut (*v).x` would be E0793; not re-let.
const J: &str = "#[repr(C, packed)]\n\
    pub struct pk { pub x: f32 }\n\
    pub unsafe fn scale(mut v: *mut pk, mut i: i32, mut s: f32, mut n: *mut i32) -> usize {\n\
        let seen = v.offset(i as isize) as usize;\n\
        (*v).x *= s;\n\
        *n = 0;\n\
        seen\n\
    }\n";

/// (l) R1160-1: a side effect in the RHS (a block with an assignment); not re-let.
const L: &str = "pub unsafe fn bump_then(mut p: *mut u32, mut i: i32) -> usize {\n\
        let seen = p.offset(i as isize) as usize;\n\
        *p = { i += 1; (*p).wrapping_add(i as u32) };\n\
        seen\n\
    }\n";

/// (k) the RHS reads a scalar formal: re-let.
const K: &str = "pub unsafe fn add_k(mut p: *mut u32, mut i: i32, mut k: u32) -> usize {\n\
        let seen = p.offset(i as isize) as usize;\n\
        *p = (*p).wrapping_add(k);\n\
        seen\n\
    }\n";

struct Seen {
    text: String,
    a: bool,
    b: bool,
    c_untouched: bool,
    d_untouched: bool,
    e_untouched: bool,
    f: bool,
    g_untouched: bool,
    h: bool,
    i: bool,
    /// `Some(untouched)` where (j) emitted well-typed text.
    j_untouched: Option<bool>,
    k: bool,
    l_untouched: bool,
}

fn observe() -> Seen {
    let a = compact(&emitted(&format!("{PRELUDE}{A}")));
    let b = compact(&emitted(&format!("{PRELUDE}{B}")));
    let c = compact(&emitted(&format!("{PRELUDE}{C}")));
    let d = compact(&emitted(&format!("{PRELUDE}{D}")));
    let e = compact(&emitted(&format!("{PRELUDE}{E}")));
    let f = compact(&emitted(&format!("{PRELUDE}{F}")));
    let g = compact(&emitted(&format!("{PRELUDE}{G}")));
    let h = compact(&emitted(&format!("{PRELUDE}{H}")));
    let i = compact(&emitted(&format!("{PRELUDE}{I}")));
    let j = emitted_or_none(&format!("{PRELUDE}{J}")).map(|j| compact(&j));
    let k = compact(&emitted(&format!("{PRELUDE}{K}")));
    let l = compact(&emitted(&format!("{PRELUDE}{L}")));
    let relet = |text: &str, rhs: &str| {
        text.contains(&format!(
            "{{let__crat_fresh_0=&mut*p;*__crat_fresh_0=(*__crat_fresh_0).wrapping_add({rhs});}}"
        ))
    };
    Seen {
        text: format!(
            "A: {a}\nB: {b}\nC: {c}\nD: {d}\nE: {e}\nF: {f}\nG: {g}\nH: {h}\nI: {i}\nJ: {j:?}\nK: {k}\nL: {l}"
        ),
        a: a.contains(
            "{let__crat_fresh_0=&mut(*a).used;*__crat_fresh_0=(*__crat_fresh_0).wrapping_sub(1);}",
        ),
        b: b.contains("{let__crat_fresh_0=&mut*p.offset(iasisize);*__crat_fresh_0+=1;}"),
        c_untouched: !c.contains("__crat_fresh"),
        d_untouched: !d.contains("__crat_fresh"),
        e_untouched: !e.contains("__crat_fresh"),
        f: f.contains(
            "{let__crat_fresh_0=&mut*(*a).chars.offset(iasisize);*__crat_fresh_0=(*__crat_fresh_0).wrapping_sub(*s.offset(iasisize));}",
        ),
        g_untouched: !g.contains("__crat_fresh"),
        h: relet(&h, "G"),
        i: relet(&i, "x"),
        j_untouched: j.map(|j| !j.contains("__crat_fresh")),
        k: relet(&k, "k"),
        l_untouched: !l.contains("__crat_fresh"),
    }
}

#[test]
fn w6a_164_the_rmw_temporary_on_a_raw_root_is_restored_and_nothing_else_moves() {
    use super::rmw_relet::FAULT;
    FAULT.store(0, Ordering::SeqCst);
    let seen = observe();
    let t = &seen.text;
    assert!(
        seen.a,
        "(a) libzahl's (*a).used = ((*a).used).wrapping_sub(1) is re-let\n{t}"
    );
    assert!(seen.b, "(b) *p.offset(i) += 1 is re-let\n{t}");
    assert!(seen.c_untouched, "(c) a safe root is untouched\n{t}");
    assert!(
        seen.d_untouched,
        "(d) an RHS without the place is untouched\n{t}"
    );
    assert!(seen.e_untouched, "(e) an index with a call is skipped\n{t}");
    assert!(
        seen.f,
        "(f) an RHS reading another raw place is re-let (R1160-1)\n{t}"
    );
    assert!(
        seen.g_untouched,
        "(g) an RHS with a call is left as written\n{t}"
    );
    assert!(
        seen.h,
        "(h) an RHS reading a static is re-let (R1160-1)\n{t}"
    );
    assert!(
        seen.i,
        "(i) an RHS reading an address-taken local is re-let (R1160-1)\n{t}"
    );
    assert_eq!(
        seen.j_untouched,
        Some(true),
        "(j) a packed field is left as written\n{t}"
    );
    assert!(seen.k, "(k) an RHS reading a scalar formal is re-let\n{t}");
    assert!(
        seen.l_untouched,
        "(l) an RHS with a side effect is left as written\n{t}"
    );
    // Seven faults, each caught by its witness; the RHS fault by (g) and (l) together.
    let mut caught = Vec::new();
    let mut last = String::new();
    for fault in 1..=7u8 {
        FAULT.store(fault, Ordering::SeqCst);
        let seen = observe();
        last = seen.text.clone();
        caught.push(match fault {
            1 => !seen.c_untouched, // the raw-root check off: the safe root is re-let
            2 => !seen.d_untouched, // the mention check off: (d) is re-let
            3 => !seen.e_untouched, // the call skip off: (e) is re-let
            4 => !seen.b,           // compound assignments dropped: (b) is not re-let
            5 => !seen.a,           // the switch off: (a) is not re-let
            6 => !seen.g_untouched && !seen.l_untouched, // the RHS check off: (g) and (l) are re-let
            _ => seen.j_untouched != Some(true), // the packed check off: (j) is re-let or ill-typed
        });
    }
    FAULT.store(0, Ordering::SeqCst);
    assert_eq!(caught, vec![true; 7], "every fault is caught\n{last}");
}
