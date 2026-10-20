//! Relay wave-5d/026 §2 (wave-6s 012 §2): a thin `Ref` local whose initializer
//! stays a raw-pointer VALUE after the rewrite — a depth-2 slice's element
//! `inputs[k]` (the element of `&[*const f64]` is `*const f64`), the deref of a
//! reference-to-raw `*p`, raw arithmetic `p.offset(k)` — was declared `&T` and
//! initialized from the raw value: `let input: &f64 = inputs[(k) as usize];`,
//! E0308 at verify and the program degraded. Outside wave 2's eight pinned
//! functions no body adapter existed for the shape; inside them a `RawExpr`
//! initializer was refused as `body-unnameable-rhs`. The reborrow bridge
//! `&*(<initializer>)` / `&mut *(<initializer>)` is the `c` arm's own
//! `GlueCore::Reborrow` at the declaration.
use super::{A5Mode, RewriteOutcome, WholeProgramAttestation};

fn rewrite(input: &str) -> RewriteOutcome {
    super::rewrite_core_injected(
        ::utils::compilation::str_to_input(input),
        None,
        super::MAX_REVERT_ROUNDS,
        &|_| {},
        false,
        false,
        false,
        Some((
            A5Mode::PreciseReplay,
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        )),
    )
}

fn emitted(input: &str) -> (String, String) {
    match rewrite(input) {
        RewriteOutcome::Emitted {
            source,
            reverted_count,
            degradations,
            ..
        } => {
            assert_eq!(reverted_count, 0, "{source}\n{degradations:#?}");
            (source.split_whitespace().collect(), source)
        }
        other => panic!("the program degraded: {other:?}"),
    }
}

const PRE: &str = "#![allow(dead_code, unused_mut, unused_unsafe)]\n";

/// wave-6s's shape: the element of a delivered outer slice, read into a thin
/// local (tulip's `let input = *inputs.offset(0)` when `input` is thin).
#[test]
fn depth2_element_read_into_a_thin_local_is_reborrowed() {
    let (text, source) = emitted(&format!(
        "{PRE}pub unsafe fn first(inputs: *const *const f64, k: i32) -> f64 {{
    let input: *const f64 = *inputs.offset(k as isize);
    return *input;
}}
pub unsafe fn caller(arr: *const *const f64) -> f64 {{ return first(arr, 1); }}
"
    ));
    assert!(
        text.contains("fnfirst(inputs:&[*constf64],k:i32)"),
        "{source}"
    );
    assert!(
        text.contains("letinput:&f64=&*(inputs[(k)asusize]);")
            || text.contains("letinput:&f64=&*inputs[(k)asusize];"),
        "{source}"
    );
}

/// The deref of a reference-to-raw parameter: `*p` is `*const f64` when `p`
/// is `&*const f64`.
#[test]
fn deref_of_a_reference_to_raw_is_reborrowed() {
    let (text, source) = emitted(&format!(
        "{PRE}pub unsafe fn g(p: *const *const f64) -> f64 {{
    let q: *const f64 = *p;
    return *q;
}}
"
    ));
    assert!(text.contains("fng(p:&*constf64)"), "{source}");
    assert!(
        text.contains("letq:&f64=&*(*p);") || text.contains("letq:&f64=&**p;"),
        "{source}"
    );
}

/// Raw arithmetic on a parameter that stays raw; the mutable twin writes
/// through the local.
#[test]
fn raw_arithmetic_into_a_thin_local_is_reborrowed_at_both_mutabilities() {
    let (text, source) = emitted(&format!(
        "{PRE}pub unsafe fn m(p: *const f64, k: i32) -> f64 {{
    let q: *const f64 = p.offset(k as isize);
    return *q;
}}
pub unsafe fn w(p: *mut f64, k: i32) {{
    let q: *mut f64 = p.offset(k as isize);
    *q = 1.0;
}}
"
    ));
    assert!(
        text.contains("letq:&f64=&*(p.offset(kasisize));")
            || text.contains("letq:&f64=&*p.offset(kasisize);"),
        "{source}"
    );
    assert!(
        text.contains("letq:&mutf64=&mut*(p.offset(kasisize));")
            || text.contains("letq:&mutf64=&mut*p.offset(kasisize);"),
        "{source}"
    );
}

/// A call into a LOCAL function is not this bridge's: its return may be
/// delivered in a safe form by the return family, and the declaration then
/// needs no reborrow. No body edit is planned for the call-initialized local.
#[test]
fn a_local_call_initializer_is_left_to_the_return_family() {
    let input = format!(
        "{PRE}pub unsafe fn mk(x: *mut i32) -> *mut i32 {{ x }}
pub unsafe fn c(x: *mut i32) {{
    let q: *mut i32 = mk(x);
    *q = 1;
}}
"
    );
    ::utils::compilation::run_compiler_on_str(&input, |tcx| {
        let (table, _) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        assert!(
            table
                .entries
                .iter()
                .any(|(s, d)| s.label == "c::q"
                    && matches!(d, super::decision::Decision::Ref { .. })),
            "{:?}",
            table
                .entries
                .iter()
                .map(|(s, d)| (s.label.clone(), format!("{d:?}")))
                .collect::<Vec<_>>()
        );
        assert!(
            !table.seams.body_edits.iter().any(|edit| {
                edit.bridge.bridge_kind == super::decision::raw_initializer::BRIDGE_KIND
            }),
            "{:#?}",
            table.seams.body_edits
        );
    })
    .unwrap();
}

/// The same handoff across two classes: the callee's `c` reborrow at exactly
/// the caller's element read. Before, `cross-class-interval-collision` held
/// both classes (`f::x`, `g::inputs`) and their dependent.
#[test]
fn a_callee_reborrow_at_exactly_the_callers_element_read_composes() {
    let (text, source) = emitted(&format!(
        "{PRE}pub unsafe fn f(x: *const f64) -> f64 {{ return *x; }}
pub unsafe fn g(inputs: *const *const f64, k: i32) -> f64 {{
    return f(*inputs.offset(k as isize));
}}
pub unsafe fn caller(arr: *const *const f64) -> f64 {{ return g(arr, 1); }}
"
    ));
    assert!(text.contains("fnf(x:&f64)"), "{source}");
    assert!(text.contains("fng(inputs:&[*constf64],k:i32)"), "{source}");
    assert!(text.contains("returnf(&*inputs[(k)asusize]);"), "{source}");
}

/// **The refusal that keeps this bridge from doubling another family's.**
///
/// The bridge's premise is that the initializer's VALUE stays raw after the
/// rewrite. When the place it reads through is DELIVERED at depth 1, the
/// slice/reference family rewrites the initializer into a REFERENCE — wave-6s's
/// rebind arm renders g18's `p.offset(1)` as `&(p)[1]`, wave-6f's array of
/// references renders `points[i].unwrap()` — and `&*` over that is a second
/// bridge on a value that needs none. Measured on the batch-9 composition
/// (`445f55be`, where both arms are in): without this refusal g18 emits
/// `&*&(p)[1]` and wave-6f's local `&*points[i].unwrap()`.
///
/// Two arms over one fixture, so the discriminator is load-bearing: the rule
/// plans the bridge for the raw root this base decides, and refuses when the
/// same root is delivered at depth 1. The delivered arm is set on the table
/// because no family on THIS base delivers such a root for this shape — that
/// is the composition's state, not the hook's.
#[test]
fn a_delivered_root_at_depth_one_is_not_bridged_again() {
    let input = format!(
        "{PRE}pub unsafe fn sum_and_first(values: *const f64, n: i32) -> f64 {{
    let mut s = 0.0;
    let mut i = 0;
    while i < n {{ s += *values.offset(i as isize); i += 1; }}
    let q: *const f64 = values.offset(1);
    return s + *q;
}}
pub unsafe fn caller(values: *const f64, n: i32) -> f64 {{ return sum_and_first(values, n); }}
"
    );
    ::utils::compilation::run_compiler_on_str(&input, |tcx| {
        let (table, _) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        // BOTH arms are constructed, so the discriminator is witnessed on any
        // base: a tree where another family already delivers this root (the
        // composition) would otherwise make the raw arm vacuous.
        let with_root = |form: super::decision::Decision| {
            let mut table = table.clone();
            for (subject, decision) in &mut table.entries {
                if subject.label == "sum_and_first::values" {
                    *decision = form.clone();
                }
            }
            table
        };
        let planned = |table: &super::decision::DecisionTable| {
            let mut plan = super::decision::seam::SeamPlan::default();
            super::decision::raw_initializer::complete(tcx, table, &mut plan);
            plan.body_edits.iter().any(|edit| {
                edit.bridge.bridge_kind == super::decision::raw_initializer::BRIDGE_KIND
            })
        };
        assert!(
            planned(&with_root(super::decision::Decision::Degraded(
                super::decision::Degradation {
                    subject: "sum_and_first::values".to_owned(),
                    site: "<w5d>".to_owned(),
                    reason: super::decision::DegradeReason::KindRaw,
                }
            ))),
            "a raw root keeps the bridge"
        );
        assert!(
            !planned(&with_root(super::decision::Decision::Slice {
                mutable: false,
                uses: Vec::new(),
            })),
            "a delivered root at depth 1 must not be bridged again"
        );
    })
    .unwrap();
}
