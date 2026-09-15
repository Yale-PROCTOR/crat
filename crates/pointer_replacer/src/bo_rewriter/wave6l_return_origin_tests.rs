//! wave-6l — returned references whose origin is reached THROUGH RAW STORAGE
//! of one input parameter (`return-not-adapted`, charter relay wave-6l/001).
//!
//! Shape: a local callee returns `(*p).field…` (a pointer read out of, or
//! arithmetic over, a raw field of `*p`). The NB5-O origin summary records the
//! return's only source as `Arg(p)/deref≥1/field`. Rule W6L-1 ties the safe
//! variant's return to the parameter's own borrow (`p: &'a T -> &'a U`),
//! bridging the raw return expression with a receipted T2 reborrow, and the
//! caller's unannotated local receives it through the existing inferred-local
//! path. SHARED views only in this wave: a mutable view would extend the
//! parameter's exclusive borrow across the caller's other live views, which no
//! existing gate examines, so it is a typed hold.
//!
//! Fixtures are reductions of real corpus functions: heman
//! `heman_image_texel` / `copy_row` (subject `copy_row::srcp#17`), and lil
//! `lil_to_string` / `lil_to_boolean` (subject `lil_to_boolean::s#3`).

use std::sync::OnceLock;

use super::{
    A5Mode, RewriteOutcome, WholeProgramAttestation,
    decision::{DegradeReason, lifetime::LifetimeFailure},
};

/// heman `heman_image_texel` + `copy_row` (the `nbands == 1` branch).
const HEMAN: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
pub struct heman_image { pub width: i32, pub height: i32, pub nbands: i32, pub data: *mut f32 }
#[no_mangle]
pub unsafe extern "C" fn heman_image_texel(mut img: *mut heman_image, mut x: i32, mut y: i32) -> *mut f32 {
    return ((*img).data).offset(((y * (*img).width * (*img).nbands) as isize) + ((x * (*img).nbands) as isize));
}
#[no_mangle]
pub unsafe extern "C" fn copy_row(mut src: *mut heman_image, mut dst: *mut heman_image, mut dstx: i32, mut y: i32) {
    let mut width = (*src).width;
    let mut x = 0;
    while x < width {
        let mut srcp = heman_image_texel(src, x, y);
        let mut dstp = heman_image_texel(dst, dstx + x, y);
        *dstp = *srcp;
        x += 1;
    }
}
"#;

/// lil `lil_to_string` (a raw field OR a static literal) + `lil_to_boolean`.
/// The literal branch has no trackable origin: the callee never earns a
/// permit and the caller stays typed-held.
const LIL: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
pub struct Value { pub l: usize, pub d: *mut u8 }
#[no_mangle]
pub unsafe extern "C" fn lil_to_string(mut val: *mut Value) -> *const u8 {
    if !val.is_null() && !((*val).d).is_null() { (*val).d as *const u8 } else { b"\0" as *const u8 }
}
#[no_mangle]
pub unsafe extern "C" fn lil_to_boolean(mut val: *mut Value) -> i32 {
    let mut s = lil_to_string(val);
    let mut i: usize = 0;
    if *s.offset(0) == 0 { return 0; }
    while *s.offset(i as isize) != 0 {
        if *s.offset(i as isize) != b'0' { return 1; }
        i = i.wrapping_add(1);
    }
    0
}
"#;

/// The ambiguity control: two parameters feed the return through raw fields.
const AMBIGUOUS: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
pub struct heman_image { pub nbands: i32, pub data: *mut f32 }
pub unsafe fn pick(mut a: *mut heman_image, mut b: *mut heman_image, which: i32) -> *mut f32 {
    if which != 0 { (*a).data } else { (*b).data }
}
pub unsafe fn read(mut a: *mut heman_image, mut b: *mut heman_image, which: i32) -> f32 {
    let mut t = pick(a, b, which);
    *t
}
"#;

struct Observed {
    decisions: Vec<(String, String)>,
    failures: Vec<(String, Option<LifetimeFailure>)>,
    plans: Vec<(String, String)>,
}

fn observe(source: &str) -> Observed {
    ::utils::compilation::run_compiler_on_str(source, |tcx| {
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let mut decisions = Vec::new();
        let mut failures = Vec::new();
        for (subject, decision) in &table.entries {
            decisions.push((subject.label.clone(), format!("{decision:?}")));
            failures.push((
                subject.label.clone(),
                ctx.lifetime_eligibility
                    .failure((subject.fn_did, subject.hir_id)),
            ));
        }
        let plans = table
            .lifetime_plan
            .functions()
            .map(|(did, plan)| (tcx.def_path_str(did.to_def_id()), plan.receipt()))
            .collect();
        Observed {
            decisions,
            failures,
            plans,
        }
    })
    .unwrap()
}

fn decision_of<'a>(observed: &'a Observed, label: &str) -> &'a str {
    &observed
        .decisions
        .iter()
        .find(|(candidate, _)| candidate == label)
        .unwrap_or_else(|| panic!("subject {label}: {:?}", observed.decisions))
        .1
}

fn failure_of(observed: &Observed, label: &str) -> Option<LifetimeFailure> {
    observed
        .failures
        .iter()
        .find(|(candidate, _)| candidate == label)
        .unwrap_or_else(|| panic!("subject {label}"))
        .1
}

/// The corpus exposes its `#[no_mangle]` functions by name (the C ABI
/// surface), which is what splits a `__crat_safe_` variant from its wrapper.
fn emitted(name: &str, source: &str, exposed: &[&str]) -> RewriteOutcome {
    use sha2::{Digest, Sha256};
    let dir = std::env::temp_dir().join(format!("crat-wave6l-{name}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let root = dir.join("lib.rs");
    std::fs::write(&root, source).unwrap();
    let names = exposed
        .iter()
        .map(|name| (*name).to_owned())
        .collect::<Vec<_>>();
    let digest = format!("{:x}", Sha256::digest(names.join("\n").as_bytes()));
    let configured_exposure = super::decision::exposure::ConfiguredExposureInput::checked(
        "wave6l-fixture",
        names,
        digest,
    )
    .unwrap();
    let outcome = super::rewrite_m1_path_with_emission_config(
        &root,
        A5Mode::PreciseReplay,
        Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        &super::EmissionRunConfig {
            configured_exposure,
        },
    );
    std::fs::remove_dir_all(dir).unwrap();
    outcome
}

fn heman_emitted() -> &'static RewriteOutcome {
    static AFTER: OnceLock<RewriteOutcome> = OnceLock::new();
    AFTER.get_or_init(|| emitted("heman", HEMAN, &["copy_row", "heman_image_texel"]))
}

fn compact(source: &str) -> String {
    source.split_whitespace().collect()
}

/// RED 1 — the callee earns a parameter-tied return plan from its raw-field
/// origin, and the shared caller local is inferred safe.
#[test]
fn w6l_heman_texel_shared_view_is_inferred_from_the_raw_field_origin() {
    let observed = observe(HEMAN);
    let srcp = decision_of(&observed, "copy_row::srcp");
    assert!(
        srcp.starts_with("InferredRef { mutable: false"),
        "srcp={srcp}; failures={:?}",
        observed.failures
    );
    let (_, plan) = observed
        .plans
        .iter()
        .find(|(function, _)| function == "heman_image_texel")
        .unwrap_or_else(|| panic!("texel lifetime plan; plans={:?}", observed.plans));
    assert!(plan.contains("arg1/deref0/depth0"), "{plan}");
    assert!(plan.contains("return_lifetime_reused=true"), "{plan}");
    assert!(
        plan.contains("through_raw_field=arg1/deref1/field"),
        "the plan names the raw traversal it collapsed: {plan}"
    );
}

/// RED 2 — the mutable view is a typed hold, not a compile-gate revert.
#[test]
fn w6l_heman_texel_mutable_view_is_held_typed() {
    let observed = observe(HEMAN);
    let dstp = decision_of(&observed, "copy_row::dstp");
    assert!(
        dstp.contains("ReturnNotAdapted"),
        "dstp keeps its residual reason: {dstp}"
    );
    assert_eq!(
        failure_of(&observed, "copy_row::dstp"),
        Some(LifetimeFailure::ViewPairHeld),
        "{:?}",
        observed.failures
    );
}

/// RED 3 — the emitted tree: the safe variant returns `&'a mut f32` tied to
/// `img` (the view's mutability follows the raw return type, the lifetime
/// follows the parameter), the C-ABI wrapper bridges it back to the raw
/// return, the caller binds the shared view; nothing reverts.
#[test]
fn w6l_heman_emits_a_parameter_tied_shared_return_and_the_caller_binding() {
    let RewriteOutcome::Emitted {
        source,
        reverted_count,
        raw_boundary_artifacts,
        ..
    } = heman_emitted()
    else {
        panic!("heman emission degraded");
    };
    println!("W6L-HEMAN-EMITTED\n{source}\nW6L-HEMAN-END");
    assert_eq!(*reverted_count, 0);
    let text = compact(source);
    // The safe variant: the return borrows `img`'s own lifetime; the raw
    // return expression is reborrowed in place.
    assert!(
        text.contains("fn__crat_safe_heman_image_texel<'a>(mutimg:&'amutheman_image,mutx:i32,muty:i32)->&'amutf32"),
        "{text}"
    );
    assert!(text.contains("return&mut*((*img).data).offset("), "{text}");
    // The C-ABI wrapper bridges the safe return back to the raw return type.
    assert!(
        text.contains("let__crat_result:&mutf32=__crat_safe_heman_image_texel(&mut*img,x,y);core::ptr::from_mut(__crat_result)"),
        "{text}"
    );
    // The caller binds the shared view; the held mutable receiver keeps its
    // raw form through the existing receive-raw twin.
    assert!(
        text.contains("letmutsrcp:&f32=__crat_safe_heman_image_texel(src,x,y);"),
        "{text}"
    );
    assert!(
        text.contains("__crat_safe_heman_image_texel(dst,dstx+x,y));(core::ptr::from_mut("),
        "{text}"
    );
    assert!(text.contains("*dstp=*srcp;"), "{text}");
    let returns = raw_boundary_artifacts
        .bridge_events
        .iter()
        .filter(|event| {
            event.site.bridge_kind == "return-raw-to-ref"
                && event.stage == super::bridge_receipt::BridgeReceiptStage::Terminal
        })
        .collect::<Vec<_>>();
    let [event] = returns.as_slice() else {
        panic!("one terminal return bridge: {returns:#?}");
    };
    assert_eq!(
        event.state,
        super::bridge_receipt::BridgeReceiptState::Applied
    );
    assert_eq!(
        event.retention,
        super::bridge_receipt::BridgeRetentionTier::T2
    );
    assert_eq!(
        event.waiver_id.as_deref(),
        Some(super::bridge_receipt::RAW_BOUNDARY_T2_WAIVER_ID)
    );
    assert!(
        event.site.position.contains("through_raw_field"),
        "the receipt names the raw traversal: {}",
        event.site.position
    );
    let rows = raw_boundary_artifacts
        .outbound_return_rows
        .iter()
        .filter(|row| {
            row.boundary_kind == "return-raw-to-ref"
                && row.terminal.stage == super::mechanical_receipt::MechanicalStage::Terminal
        })
        .collect::<Vec<_>>();
    let [row] = rows.as_slice() else {
        panic!("one terminal outbound return row: {rows:#?}");
    };
    assert_eq!(
        row.retention,
        super::mechanical_receipt::MechanicalRetention::T2 {
            waiver_id: super::bridge_receipt::RAW_BOUNDARY_T2_WAIVER_ID.to_owned()
        }
    );
    assert_eq!(row.lifetime_origin.len(), 1, "{row:#?}");
    assert_eq!(row.terminal_interface, "ref-mut");
    assert!(
        raw_boundary_artifacts.outbound_return_error.is_none(),
        "{:?}",
        raw_boundary_artifacts.outbound_return_error
    );
}

/// RED 4 — lil: the literal branch has no trackable origin (the summary marks
/// the return `unknown`); no permit, the caller local stays
/// `return-not-adapted` with the typed origin failure.
#[test]
fn w6l_lil_to_string_literal_branch_is_held_typed() {
    let observed = observe(LIL);
    let s = decision_of(&observed, "lil_to_boolean::s");
    assert!(s.contains("ReturnNotAdapted"), "{s}");
    assert_eq!(
        failure_of(&observed, "lil_to_boolean::s"),
        Some(LifetimeFailure::OriginUnknown),
        "{:?}",
        observed.failures
    );
    assert!(
        !observed
            .plans
            .iter()
            .any(|(function, _)| function == "lil_to_string"),
        "{:?}",
        observed.plans
    );
}

/// RED 5 — two parameters feed the return through raw fields: no guessed
/// lifetime, a typed ambiguity hold.
#[test]
fn w6l_two_parameter_origins_are_held_ambiguous() {
    let observed = observe(AMBIGUOUS);
    let t = decision_of(&observed, "read::t");
    assert!(t.contains("ReturnNotAdapted"), "{t}");
    assert_eq!(
        failure_of(&observed, "read::t"),
        Some(LifetimeFailure::OriginAmbiguous),
        "{:?}",
        observed.failures
    );
    assert!(observed.plans.is_empty(), "{:?}", observed.plans);
}

/// The degradation vocabulary stays: a held caller local still reports
/// `return-not-adapted` in the census, never a silent skip.
#[test]
fn w6l_held_locals_keep_the_return_not_adapted_reason() {
    let RewriteOutcome::Emitted { degradations, .. } = heman_emitted() else {
        panic!("heman emission degraded");
    };
    let dstp = degradations
        .iter()
        .find(|degradation| degradation.subject == "copy_row::dstp")
        .expect("dstp degradation");
    assert_eq!(dstp.reason, DegradeReason::ReturnNotAdapted);
}

/// heman `heman_image_texel` + `heman_image_sample`: the caller WALKS the
/// returned pointer (`data = data.offset(1)` in a loop). A thin inferred view
/// cannot serve that use; the local must stay a typed hold, and the owner
/// must not revert because of it.
const HEMAN_WALK: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
pub struct heman_image { pub width: i32, pub height: i32, pub nbands: i32, pub data: *mut f32 }
#[no_mangle]
pub unsafe extern "C" fn heman_image_texel(mut img: *mut heman_image, mut x: i32, mut y: i32) -> *mut f32 {
    return ((*img).data).offset(((y * (*img).width * (*img).nbands) as isize) + ((x * (*img).nbands) as isize));
}
#[no_mangle]
pub unsafe extern "C" fn heman_image_sample(mut img: *mut heman_image, mut x: i32, mut y: i32, mut result: *mut f32) {
    let mut data = heman_image_texel(img, x, y);
    let mut b = 0;
    while b < (*img).nbands {
        let fresh1 = *data;
        data = data.offset(1);
        *result.offset(b as isize) = fresh1;
        b += 1;
    }
}
"#;

/// Witness 7 — the walking caller keeps its raw local (the receiver form the
/// walk needs is a slice, which the thin return interface cannot supply), the
/// census reason stays `return-not-adapted`, and the owner does NOT revert:
/// the raw local receives the safe return through the existing receive-raw
/// twin. The callee itself still earns its plan.
#[test]
fn w6l_cursor_walk_caller_is_held_without_reverting_the_owner() {
    let observed = observe(HEMAN_WALK);
    let data = decision_of(&observed, "heman_image_sample::data");
    assert!(data.contains("ReturnNotAdapted"), "{data}");
    assert!(
        observed
            .plans
            .iter()
            .any(|(function, plan)| function == "heman_image_texel"
                && plan.contains("through_raw_field=arg1/deref1/field")),
        "{:?}",
        observed.plans
    );
    let RewriteOutcome::Emitted {
        source,
        reverted_count,
        ..
    } = emitted(
        "heman-walk",
        HEMAN_WALK,
        &["heman_image_sample", "heman_image_texel"],
    )
    else {
        panic!("heman walk emission degraded");
    };
    println!("W6L-WALK-EMITTED\n{source}\nW6L-WALK-END");
    assert_eq!(reverted_count, 0);
    let text = compact(&source);
    assert!(
        text.contains("fn__crat_safe_heman_image_texel<'a>(mutimg:&'aheman_image,mutx:i32,muty:i32)->&'amutf32"),
        "{text}"
    );
    assert!(
        text.contains("__crat_safe_heman_image_texel(img,x,y));(core::ptr::from_mut("),
        "{text}"
    );
    assert!(text.contains("data=data.offset(1);"), "{text}");
}
