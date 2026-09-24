//! **R556-4 joint (c) — a Box owner's element address at a raw formal takes the owner's raw
//! view at its BASE** (wave-5d 075 R-A, relay 099).
//!
//! brotli's `BrotliClusterHistograms*` pass `&mut *clusters.offset(num_clusters as isize)` to
//! `BrotliHistogramCombine*`'s raw `clusters` formal, `BrotliCompressBufferQuality10` passes
//! `&mut *nodes.offset(0)` and `BrotliCreateHqZopfliBackwardReferences` passes
//! `&mut *matches.offset(..)`, each owner an optional `Box<[T]>`. The C arm chose the
//! whole-owner view (`optional-box-borrow-view-to-raw`) for an argument that is not the owner,
//! and the owner's own `box-expression` for `*X.offset(k)` sat inside it: one class, two edits,
//! `intra-class-interval-overlap` — and composing them would render
//! `(&mut X.as_deref_mut().unwrap()[k]).as_deref_mut()..` (E0599). The hold was load-bearing.
//!
//! R-A renders the owner's raw view over the base path and keeps the input's arithmetic and its
//! `&mut *` verbatim: `&mut *X.as_deref_mut().map_or(core::ptr::null_mut(), |s| s.as_mut_ptr())
//! .offset(k)`. The element edit is retired (`box-expression:retired-under-base-view`): its
//! product, a one-element place, is exactly what must not reach a formal that writes a range.

use super::wave6a_allocation_tests::{compact, emitted, reason_of};

const PRELUDE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, unused_assignments, non_camel_case_types, non_snake_case)]
extern "C" {
    fn exit(code: i32) -> !;
}
#[repr(C)]
pub struct MemoryManager {
    pub alloc_func: Option<unsafe extern "C" fn(*mut std::os::raw::c_void, usize) -> *mut std::os::raw::c_void>,
    pub free_func: Option<unsafe extern "C" fn(*mut std::os::raw::c_void, *mut std::os::raw::c_void)>,
    pub opaque: *mut std::os::raw::c_void,
}
pub unsafe extern "C" fn BrotliAllocate(mut m: *mut MemoryManager, mut n: usize) -> *mut std::os::raw::c_void {
    let mut result = ((*m).alloc_func).expect("non-null function pointer")((*m).opaque, n);
    if result.is_null() { exit(1 as i32); }
    return result;
}
pub unsafe extern "C" fn BrotliFree(mut m: *mut MemoryManager, mut p: *mut std::os::raw::c_void) {
    ((*m).free_func).expect("non-null function pointer")((*m).opaque, p);
}
/// A range writer whose formal the analysis keeps raw (the address escapes as an integer).
pub unsafe extern "C" fn Combine(mut clusters: *mut u32, n: usize) -> usize {
    let mut i = 0 as usize;
    while i < n {
        *clusters.offset(i as isize) = i as u32;
        i = i.wrapping_add(1);
    }
    return clusters as usize;
}
"#;

/// brotli's shape: the conditional allocation (an OPTIONAL owner), an element write, the element
/// address passed to the raw range writer, the `BrotliFree` pair.
const ELEMENT_AT_RAW: &str = r#"
pub unsafe extern "C" fn Cluster(mut m: *mut MemoryManager, n: usize, k: usize) -> usize {
    let mut clusters = if n > 0 as usize {
        BrotliAllocate(m, n.wrapping_mul(::core::mem::size_of::<u32>())) as *mut u32
    } else { 0 as *mut u32 };
    if n > 0 as usize { *clusters.offset(0 as isize) = 1 as u32; }
    let r = Combine(&mut *clusters.offset(k as isize), n.wrapping_sub(k));
    BrotliFree(m, clusters as *mut std::os::raw::c_void);
    return r;
}
"#;

/// **Witness (075 §4 fixture 1).** The owner delivers `Option<Box<[u32]>>`, the element address
/// renders over the base's raw view with the input's arithmetic and `&mut *` kept, and the tree
/// type-checks.
#[test]
fn r556_4_an_element_address_at_a_raw_formal_takes_the_base_view() {
    let out = emitted("r556-base-view", &format!("{PRELUDE}{ELEMENT_AT_RAW}"));
    let text = compact(&out.source);
    assert_eq!(
        reason_of(&out.degradations, "Cluster::clusters"),
        None,
        "{:#?}\n{}",
        out.degradations,
        out.source
    );
    assert!(
        text.contains("letmutclusters:Option<Box<[u32]>>="),
        "{}",
        out.source
    );
    assert!(
        text.contains(
            "Combine(&mut*clusters.as_deref_mut().map_or(core::ptr::null_mut(),|s|s.as_mut_ptr()).offset(kasisize),"
        ),
        "{}",
        out.source
    );
    assert!(
        text.contains("fnCombine(mutclusters:*mutu32,"),
        "{}",
        out.source
    );
    assert_eq!(out.reverted, 0, "{}", out.source);
    assert!(
        super::verify::type_checks_str(&out.source),
        "{}",
        out.source
    );
    // The class's one edit at that argument is the view over the base path; the
    // owner's element edit there is gone (not applied, not dropped: retired).
    let (argument, base, element) = spans(ELEMENT_AT_RAW, "&mut *clusters.offset(k as isize)");
    let events = &out.artifacts.bridge_events;
    assert!(
        events.iter().any(
            |event| event.site.bridge_kind == "optional-box-borrow-view-to-raw"
                && event.state == super::bridge_receipt::BridgeReceiptState::Applied
                && (event.site.lo, event.site.hi) == base
        ),
        "the view is anchored at the base path {base:?} of {argument:?}: {events:#?}"
    );
    assert!(
        !events
            .iter()
            .any(|event| event.site.bridge_kind == "box-expression"
                && (event.site.lo, event.site.hi) == element),
        "the element edit {element:?} is retired: {events:#?}"
    );
}

/// `(argument, base, element)` byte intervals of `argument` (spelled
/// `&mut *X.offset(..)`) in `{PRELUDE}{program}`.
fn spans(program: &str, argument: &str) -> ((u32, u32), (u32, u32), (u32, u32)) {
    let source = format!("{PRELUDE}{program}");
    let lo = u32::try_from(source.find(argument).expect("argument spelled")).unwrap();
    let hi = lo + u32::try_from(argument.len()).unwrap();
    let name = argument["&mut *".len()..].split('.').next().unwrap();
    let base_lo = lo + u32::try_from("&mut *".len()).unwrap();
    (
        (lo, hi),
        (base_lo, base_lo + u32::try_from(name.len()).unwrap()),
        (lo + u32::try_from("&mut ".len()).unwrap(), hi),
    )
}

/// The Box plan's receipts for `subject` (`fn::binding`) in the precise-replay decision table.
fn box_receipts(program: &str, subject: &str) -> Vec<String> {
    ::utils::compilation::run_compiler_on_str(&format!("{PRELUDE}{program}"), |tcx| {
        let (table, _) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("one decision pipeline");
        table
            .entries
            .iter()
            .find_map(|(key, decision)| match decision {
                super::decision::Decision::Box(plan)
                    if format!(
                        "{}::{}",
                        tcx.def_path_str(key.fn_did.to_def_id()),
                        tcx.hir_name(key.hir_id)
                    )
                    .ends_with(subject) =>
                {
                    Some(plan.receipts.clone())
                }
                _ => None,
            })
            .unwrap_or_else(|| panic!("{subject} is decided Box"))
    })
    .expect("fixture compiles")
}

/// The Box plan's own receipt names the retirement (`box-expression:retired-under-base-view`),
/// so the census can count it.
#[test]
fn r556_4_the_retired_element_edit_is_receipted() {
    let receipts = box_receipts(ELEMENT_AT_RAW, "Cluster::clusters");
    assert!(
        receipts
            .iter()
            .any(|receipt| receipt == "box-expression:retired-under-base-view"),
        "{receipts:#?}"
    );
}

/// **Control (075 §4, 3).** The base view is for an owner's ELEMENT ADDRESS only. The
/// classifier accepts exactly `&mut *X.offset(k)` / `&*X.offset(k)` with `X` a binding, and
/// refuses the owner passed bare (whose whole-owner view wave-6a's `w6a_r551_*` witness), a
/// deref without arithmetic, chained arithmetic, a field projection and a cast.
#[test]
fn r556_4_the_classifier_takes_only_an_element_address() {
    const SHAPES: &str = r#"
#![allow(unused_unsafe, unused_mut, dead_code)]
pub struct S { pub f: u32 }
pub unsafe fn sink(p: *mut u32) {}
pub unsafe fn csink(p: *const u32) {}
pub unsafe fn shapes(mut x: *mut u32, mut s: *mut S, k: isize) {
    sink(&mut *x.offset(k));
    csink(&*x.offset(k));
    sink(x);
    sink(&mut *x);
    sink(&mut *x.offset(k).offset(1));
    sink(&mut (*s.offset(k)).f);
    sink(&mut *(x.offset(k) as *mut u32));
}
"#;
    let verdicts = ::utils::compilation::run_compiler_on_str(SHAPES, |tcx| {
        use rustc_hir::intravisit::{self, Visitor};
        struct V<'tcx> {
            tcx: rustc_middle::ty::TyCtxt<'tcx>,
            out: Vec<(String, Option<bool>)>,
        }
        impl<'tcx> Visitor<'tcx> for V<'tcx> {
            fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
                if let rustc_hir::ExprKind::Call(_, [argument]) = &expr.kind {
                    let text = self
                        .tcx
                        .sess
                        .source_map()
                        .span_to_snippet(argument.span)
                        .unwrap();
                    let verdict = super::decision::emitability::owner_element_address(argument)
                        .map(|address| address.mutable);
                    self.out.push((text, verdict));
                }
                intravisit::walk_expr(self, expr);
            }
        }
        let owner = tcx
            .hir_body_owners()
            .find(|owner| tcx.def_path_str(owner.to_def_id()) == "shapes")
            .expect("shapes");
        let mut v = V {
            tcx,
            out: Vec::new(),
        };
        v.visit_body(tcx.hir_body_owned_by(owner));
        v.out
    })
    .expect("fixture compiles");
    assert_eq!(
        verdicts,
        vec![
            ("&mut *x.offset(k)".to_owned(), Some(true)),
            ("&*x.offset(k)".to_owned(), Some(false)),
            ("x".to_owned(), None),
            ("&mut *x".to_owned(), None),
            ("&mut *x.offset(k).offset(1)".to_owned(), None),
            ("&mut (*s.offset(k)).f".to_owned(), None),
            ("&mut *(x.offset(k) as *mut u32)".to_owned(), None),
        ]
    );
}

/// **Relay-042 row's fate (R556-4 STOP 3).** The NON-optional twin — an unconditional
/// allocation, `Box<[u32]>` — takes the base view too (`&mut *clusters.as_mut_ptr()
/// .offset(k)`), so the shape the relay-042 row was admitted for no longer produces the
/// pair, and the row is withdrawn.
#[test]
fn r556_4_the_non_optional_twin_takes_the_base_view() {
    let twin = ELEMENT_AT_RAW
        .replace(
            "let mut clusters = if n > 0 as usize {\n        BrotliAllocate(m, n.wrapping_mul(::core::mem::size_of::<u32>())) as *mut u32\n    } else { 0 as *mut u32 };",
            "let mut clusters = BrotliAllocate(m, n.wrapping_mul(::core::mem::size_of::<u32>())) as *mut u32;",
        )
        .replace("if n > 0 as usize { *clusters.offset(0 as isize) = 1 as u32; }", "*clusters.offset(0 as isize) = 1 as u32;");
    assert_ne!(twin, ELEMENT_AT_RAW, "the twin is a different program");
    let out = emitted("r556-twin", &format!("{PRELUDE}{twin}"));
    let text = compact(&out.source);
    assert!(
        text.contains("letmutclusters:Box<[u32]>="),
        "{}",
        out.source
    );
    assert!(
        text.contains("Combine(&mut*clusters.as_mut_ptr().offset(kasisize),"),
        "{}",
        out.source
    );
    assert_eq!(out.reverted, 0, "{}", out.source);
    assert!(
        super::verify::type_checks_str(&out.source),
        "{}",
        out.source
    );
}

/// **Control — mutability must agree.** `&mut *X.offset(k)` at a `*const` formal: the view
/// would be `*const` and `&mut *` over it does not type, so the base view declines and the
/// argument keeps its pre-R556-4 path (the class holds; the tree is the input's there).
#[test]
fn r556_4_a_mutable_element_address_at_a_const_formal_declines_the_base_view() {
    let program = format!(
        "{}{}",
        ELEMENT_AT_RAW.replace("Combine(&mut *clusters", "Peek(&mut *clusters"),
        r#"
pub unsafe extern "C" fn Peek(mut clusters: *const u32, n: usize) -> usize {
    let mut i = 0 as usize;
    let mut total = 0 as usize;
    while i < n {
        total = total.wrapping_add(*clusters.offset(i as isize) as usize);
        i = i.wrapping_add(1);
    }
    return total.wrapping_add(clusters as usize);
}
"#
    );
    let out = emitted("r556-const", &format!("{PRELUDE}{program}"));
    let text = compact(&out.source);
    assert!(!text.contains("&mut*clusters.as_deref"), "{}", out.source);
    assert!(
        super::verify::type_checks_str(&out.source),
        "{}",
        out.source
    );
    // Read on the PLAN, not the verified text: an ill-typed base view would be caught by the
    // per-function gate and reverted, leaving the same final text. The view stays on the whole
    // argument (the pre-R556-4 path) and nothing reverts.
    let (argument, _, _) = spans(&program, "&mut *clusters.offset(k as isize)");
    assert!(
        out.artifacts
            .bridge_events
            .iter()
            .any(
                |event| event.site.bridge_kind == "optional-box-borrow-view-to-raw"
                    && (event.site.lo, event.site.hi) == argument
            ),
        "{:#?}",
        out.artifacts.bridge_events
    );
    assert_eq!(out.reverted, 0, "{}", out.source);
}

/// **(i) — the composed geometry at brotli's `BrotliHistogramCombine*` calls.** The callee
/// writes a range through `clusters` beside a `symbols` formal of the same pointee type; their
/// disjointness is not provable (the caller's `symbols` and an opaque allocation), so the
/// callee's A5 T2 fallback selects the element address's argument as a raw view — exactly the
/// argument the caller's base-view bridge sits INSIDE. Before (i) the two were a cross-class
/// collision holding both classes; (α) over containment lets the wrapper take the argument's
/// grafted text, `&mut *clusters.as_deref_mut()….offset(k)`, as its raw value.
const COMPOSED: &str = r#"
pub unsafe extern "C" fn CombineCounted(mut symbols: *mut u32, mut clusters: *mut u32, n: usize) -> usize {
    *symbols.offset(0 as isize) = 7 as u32;
    let mut i = 0 as usize;
    while i < n {
        *clusters.offset(i as isize) = *symbols.offset(0 as isize);
        i = i.wrapping_add(1);
    }
    return n;
}
pub unsafe extern "C" fn ClusterCounted(mut m: *mut MemoryManager, mut symbols: *mut u32, n: usize, k: usize) -> usize {
    let mut clusters = if n > 0 as usize {
        BrotliAllocate(m, n.wrapping_mul(::core::mem::size_of::<u32>())) as *mut u32
    } else { 0 as *mut u32 };
    if n > 0 as usize { *clusters.offset(0 as isize) = 1 as u32; }
    let _raw_symbols = symbols as usize;
    let r = CombineCounted(symbols, &mut *clusters.offset(k as isize), n.wrapping_sub(k));
    BrotliFree(m, clusters as *mut std::os::raw::c_void);
    return r;
}
"#;

/// **Witness (i).** The wrapper and the base view compose: no class collides, the wrapper's
/// raw value for the element address is the argument's grafted text, and the tree type-checks.
#[test]
fn r556_4_i_the_a5_wrapper_takes_the_base_view_argument() {
    let out = emitted("r556-composed", &format!("{PRELUDE}{COMPOSED}"));
    let text = compact(&out.source);
    let events = &out.artifacts.bridge_events;
    assert!(
        !events.iter().any(|event| event
            .drop_reason
            .as_deref()
            .is_some_and(|reason| reason.contains("cross-class-interval-collision"))),
        "{events:#?}\n{}",
        out.source
    );
    assert!(
        events.iter().any(
            |event| event.site.bridge_kind == "a5-site-proof-t2-fallback"
                && event.state == super::bridge_receipt::BridgeReceiptState::Applied
        ),
        "the fallback is the composed geometry's premise: {events:#?}"
    );
    assert!(
        text.contains(
            ":*mutu32=&mut*clusters.as_deref_mut().map_or(core::ptr::null_mut(),|s|s.as_mut_ptr()).offset(kasisize);"
        ),
        "{}",
        out.source
    );
    assert_eq!(out.reverted, 0, "{}", out.source);
    assert!(
        super::verify::type_checks_str(&out.source),
        "{}",
        out.source
    );
}
