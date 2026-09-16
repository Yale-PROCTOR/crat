//! wave-6l — returned references whose origin is reached THROUGH RAW STORAGE
//! of one input parameter (`return-not-adapted`, charter relay wave-6l/001).
//!
//! Shape: a local callee returns `(*p).field…` (a pointer read out of, or
//! arithmetic over, a raw field of `*p`). The NB5-O origin summary records the
//! return's only source as `Arg(p)/deref≥1/field`. Rule W6L-1 ties the safe
//! variant's return to the parameter's own borrow (`p: &'a T -> &'a U`),
//! bridging the raw return expression with a receipted T2 reborrow, and the
//! caller's unannotated local receives it through the existing inferred-local
//! path. The parameter must be a SHARED reference: the returned memory is not
//! its pointee, so an exclusive tie would forbid the caller every read of the
//! parameter while the view lives (heman's walkers read `(*img).nbands` in the
//! walking loop — E0503, a revert taking the owner's other deliveries down);
//! a write through the view makes the parameter mutable in the model, so the
//! parameter-borrow hold also covers every mutable view.
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
    let mut names = exposed
        .iter()
        .map(|name| (*name).to_owned())
        .collect::<Vec<_>>();
    names.sort();
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
    match &outcome {
        RewriteOutcome::Degraded {
            reason,
            degradations,
            ..
        } => {
            println!("W6L-DEGRADED {name}: {reason}\n{degradations:?}");
        }
        RewriteOutcome::Emitted {
            emitted_count,
            reverted_count,
            degradations,
            excluded,
            first_diags,
            raw_boundary_artifacts,
            ..
        } => {
            println!(
                "W6L-OUTCOME {name}: emitted={emitted_count} reverted={reverted_count} degradations={degradations:?} excluded={excluded:?} diags={first_diags:?}\nW6L-FAMILY {name}: {:?}",
                raw_boundary_artifacts.additive_family_receipts
            );
        }
    }
    outcome
}

fn heman_emitted() -> &'static RewriteOutcome {
    static AFTER: OnceLock<RewriteOutcome> = OnceLock::new();
    AFTER.get_or_init(|| emitted("heman", HEMAN, &["copy_row", "heman_image_texel"]))
}

fn compact(source: &str) -> String {
    source.split_whitespace().collect()
}

/// The shared-parameter twin of `HEMAN`: the same callee, read-only callers
/// (`copy_row` reading both texels), so the callee's parameter stays shared.
const HEMAN_READ: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
pub struct heman_image { pub width: i32, pub height: i32, pub nbands: i32, pub data: *mut f32 }
#[no_mangle]
pub unsafe extern "C" fn heman_image_texel(mut img: *mut heman_image, mut x: i32, mut y: i32) -> *mut f32 {
    return ((*img).data).offset(((y * (*img).width * (*img).nbands) as isize) + ((x * (*img).nbands) as isize));
}
#[no_mangle]
pub unsafe extern "C" fn row_sum(mut src: *mut heman_image, mut dst: *mut heman_image, mut dstx: i32, mut y: i32) -> f32 {
    let mut width = (*src).width;
    let mut x = 0;
    let mut sum = 0.0f32;
    while x < width {
        let mut srcp = heman_image_texel(src, x, y);
        let mut dstp = heman_image_texel(dst, dstx + x, y);
        sum += *dstp + *srcp;
        x += 1;
    }
    sum
}
"#;

fn heman_read_emitted() -> &'static RewriteOutcome {
    static AFTER: OnceLock<RewriteOutcome> = OnceLock::new();
    AFTER.get_or_init(|| emitted("heman-read", HEMAN_READ, &["row_sum", "heman_image_texel"]))
}

/// RED 1 — the callee earns a parameter-tied return plan from its raw-field
/// origin, and both shared caller locals are inferred safe (two shared views
/// may alias each other).
#[test]
fn w6l_heman_texel_shared_views_are_inferred_from_the_raw_field_origin() {
    let observed = observe(HEMAN_READ);
    for label in ["row_sum::srcp", "row_sum::dstp"] {
        let decision = decision_of(&observed, label);
        assert!(
            decision.starts_with("InferredRef { mutable: false"),
            "{label}={decision}; failures={:?}",
            observed.failures
        );
    }
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
    assert!(plan.contains("form=thin"), "{plan}");
}

/// RED 2 (R401-8, the relay's RED on `copy_row`) — a write through the view
/// makes the parameter mutable in the model; the view is then UNTIED
/// (`&'static mut f32`): `srcp` (shared view) delivers, `dstp` (a mutable
/// view beside another safe `f32` view) is view-pair-held; the emitted tree
/// carries `'static` on the callee's return with no generic parameter, the
/// receipt `untied-return-view`, and nothing reverts.
#[test]
fn w6l_mutable_parameter_yields_an_untied_view() {
    let observed = observe(HEMAN);
    let srcp = decision_of(&observed, "copy_row::srcp");
    assert!(
        srcp.starts_with("InferredRef { mutable: false"),
        "srcp={srcp}; failures={:?}",
        observed.failures
    );
    let dstp = decision_of(&observed, "copy_row::dstp");
    assert!(dstp.contains("ReturnNotAdapted"), "{dstp}");
    assert_eq!(
        failure_of(&observed, "copy_row::dstp"),
        Some(LifetimeFailure::ViewPairHeld),
        "{:?}",
        observed.failures
    );
    let (_, plan) = observed
        .plans
        .iter()
        .find(|(function, _)| function == "heman_image_texel")
        .unwrap_or_else(|| panic!("texel plan; {:?}", observed.plans));
    assert!(
        plan.contains("slot\treturn/deref0/depth0\tstatic"),
        "{plan}"
    );
    assert!(plan.contains("tie=untied-return-view"), "{plan}");
    assert!(!plan.contains("return_tie"), "no tie: {plan}");
    let RewriteOutcome::Emitted {
        source,
        reverted_count,
        raw_boundary_artifacts,
        ..
    } = heman_emitted()
    else {
        panic!("heman emission degraded");
    };
    println!("W6L-UNTIED-EMITTED\n{source}\nW6L-UNTIED-END");
    assert_eq!(*reverted_count, 0);
    let text = compact(source);
    assert!(
        text.contains("fn__crat_safe_heman_image_texel(mutimg:&mutheman_image,mutx:i32,muty:i32)->&'staticmutf32"),
        "{text}"
    );
    assert!(
        text.contains("letmutsrcp:&f32=__crat_safe_heman_image_texel(src,x,y);"),
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
        event.retention,
        super::bridge_receipt::BridgeRetentionTier::T2
    );
    assert_eq!(
        event.waiver_id.as_deref(),
        Some(super::bridge_receipt::RAW_BOUNDARY_T2_WAIVER_ID)
    );
    assert!(
        event.site.position.contains(":untied-return-view"),
        "the per-site receipt: {}",
        event.site.position
    );
    assert!(
        raw_boundary_artifacts.outbound_return_error.is_none(),
        "{:?}",
        raw_boundary_artifacts.outbound_return_error
    );
}

/// R401-8 — a single mutable untied view delivers (`fill`), and the untied
/// SLICE form serves a writing walker: `&'static mut [f32]` over the fallback
/// extent, the walk rewritten, `(*img).nbands` still readable in the loop.
#[test]
fn w6l_single_mutable_untied_view_and_untied_slice_deliver() {
    let observed = observe(HEMAN_FILL);
    let t = decision_of(&observed, "fill::t");
    assert!(
        t.starts_with("InferredRef { mutable: true"),
        "t={t}; failures={:?}",
        observed.failures
    );
    let RewriteOutcome::Emitted {
        source,
        reverted_count,
        ..
    } = emitted("heman-fill", HEMAN_FILL, &["fill", "heman_image_texel"])
    else {
        panic!("heman fill emission degraded");
    };
    assert_eq!(reverted_count, 0);
    let text = compact(&source);
    assert!(text.contains("->&'staticmutf32"), "{text}");
    assert!(
        text.contains("letmutt:&mutf32=__crat_safe_heman_image_texel(img,x,y);*t=v;"),
        "{text}"
    );

    let observed = observe(HEMAN_WRITE_WALK);
    let texel = decision_of(&observed, "heman_draw_points::texel");
    assert!(
        texel.starts_with("Slice { mutable: true"),
        "texel={texel}; failures={:?}",
        observed.failures
    );
    let mine = observed
        .plans
        .iter()
        .any(|(function, _)| function == "heman_image_texel");
    let RewriteOutcome::Emitted {
        source,
        reverted_count,
        ..
    } = emitted(
        "heman-write-walk",
        HEMAN_WRITE_WALK,
        &["heman_draw_points", "heman_image_texel"],
    )
    else {
        panic!("heman write-walk emission degraded");
    };
    println!("W6L-WRITE-WALK-EMITTED\n{source}\nW6L-WRITE-WALK-END");
    assert_eq!(reverted_count, 0);
    let text = compact(&source);
    assert!(text.contains("whilec<(*target).nbands"), "{text}");
    assert!(text.contains("texel[0]=val;"), "{text}");
    if mine {
        assert!(text.contains("->&'staticmut[f32]"), "{text}");
        assert!(
            text.contains("returncore::slice::from_raw_parts_mut("),
            "{text}"
        );
    } else {
        // R217-2(a) re-pin (batch-8 composition): the walker is wave-6a's
        // raw-call delivery; the callee keeps its raw interface.
        assert!(text.contains("->*mutf32"), "{text}");
    }
}

/// R401-8 guard — an untied view that leaves its caller (returned further)
/// is a typed hold, never a `'static` that outlives what Rust can see.
#[test]
fn w6l_untied_view_that_escapes_its_caller_is_held() {
    let observed = observe(HEMAN_ESCAPE);
    let t = decision_of(&observed, "first_texel::t");
    assert!(!t.starts_with("InferredRef"), "t={t}");
    assert!(
        t.contains("Degraded"),
        "the escaping view is not delivered: {t}; failures={:?}",
        observed.failures
    );
    assert_eq!(
        failure_of(&observed, "first_texel::t"),
        Some(LifetimeFailure::UntiedViewEscapes),
        "{:?}",
        observed.failures
    );
    let RewriteOutcome::Emitted { reverted_count, .. } = emitted(
        "heman-escape",
        HEMAN_ESCAPE,
        &["first_texel", "heman_image_texel"],
    ) else {
        panic!("heman escape emission degraded");
    };
    assert_eq!(reverted_count, 0);
}

/// heman `heman_draw_points`: a WRITING walker (`*texel = val; texel = texel.offset(1)`).
const HEMAN_WRITE_WALK: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
pub struct heman_image { pub width: i32, pub height: i32, pub nbands: i32, pub data: *mut f32 }
#[no_mangle]
pub unsafe extern "C" fn heman_image_texel(mut img: *mut heman_image, mut x: i32, mut y: i32) -> *mut f32 {
    return ((*img).data).offset(((y * (*img).width * (*img).nbands) as isize) + ((x * (*img).nbands) as isize));
}
#[no_mangle]
pub unsafe extern "C" fn heman_draw_points(mut target: *mut heman_image, mut i: i32, mut j: i32, val: f32) {
    if !(i < 0 || i >= (*target).width || j < 0 || j >= (*target).height) {
        let mut texel = heman_image_texel(target, i, j);
        let mut c = 0;
        while c < (*target).nbands {
            *texel = val;
            let fresh0 = *texel;
            texel = texel.offset(1);
            c += 1;
        }
    }
}
"#;

/// The escape control: the caller returns the view further.
const HEMAN_ESCAPE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
pub struct heman_image { pub width: i32, pub height: i32, pub nbands: i32, pub data: *mut f32 }
#[no_mangle]
pub unsafe extern "C" fn heman_image_texel(mut img: *mut heman_image, mut x: i32, mut y: i32) -> *mut f32 {
    return ((*img).data).offset(((y * (*img).width * (*img).nbands) as isize) + ((x * (*img).nbands) as isize));
}
#[no_mangle]
pub unsafe extern "C" fn first_texel(mut img: *mut heman_image, v: f32) -> *mut f32 {
    let mut t = heman_image_texel(img, 0, 0);
    *t = v;
    return t;
}
"#;

/// RED 3 — the emitted tree: the safe variant returns `&'a mut f32` tied to
/// the shared `img` (the view's mutability follows the raw return type, the
/// lifetime follows the parameter), the C-ABI wrapper bridges it back to the
/// raw return, both callers bind shared views; nothing reverts.
#[test]
fn w6l_heman_emits_a_parameter_tied_return_and_the_caller_bindings() {
    let RewriteOutcome::Emitted {
        source,
        reverted_count,
        raw_boundary_artifacts,
        ..
    } = heman_read_emitted()
    else {
        panic!("heman read emission degraded");
    };
    println!("W6L-HEMAN-EMITTED\n{source}\nW6L-HEMAN-END");
    assert_eq!(*reverted_count, 0);
    let text = compact(source);
    assert!(
        text.contains("fn__crat_safe_heman_image_texel<'a>(mutimg:&'aheman_image,mutx:i32,muty:i32)->&'amutf32"),
        "{text}"
    );
    assert!(text.contains("return&mut*((*img).data).offset("), "{text}");
    assert!(
        text.contains("let__crat_result:&mutf32=__crat_safe_heman_image_texel(&*img,x,y);core::ptr::from_mut(__crat_result)"),
        "{text}"
    );
    assert!(
        text.contains("letmutsrcp:&f32=__crat_safe_heman_image_texel(src,x,y);"),
        "{text}"
    );
    assert!(
        text.contains("letmutdstp:&f32=__crat_safe_heman_image_texel(dst,dstx+x,y);"),
        "{text}"
    );
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
    // R217-2(a) re-pin (batch-8 composition): wave-6a's sealed slice
    // constructor now examines the walked call result first and names its
    // own residue (`slice-local-construction`); on this lane's base the
    // residue stays `return-not-adapted` with the origin failure. Either way
    // the row is a typed hold and the callee earns no plan.
    assert!(
        s.contains("ReturnNotAdapted") || s.contains("SliceLocalConstruction"),
        "{s}"
    );
    if s.contains("ReturnNotAdapted") {
        assert_eq!(
            failure_of(&observed, "lil_to_boolean::s"),
            Some(LifetimeFailure::OriginUnknown),
            "{:?}",
            observed.failures
        );
    }
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

/// Witness 7 (wave 2, slice form) — the walking caller receives a slice:
/// on this lane's base the callee returns `&'a mut [f32]` over the fallback
/// extent with the addendum-77 receipt and the caller local is a delivered
/// `Slice` whose walk the slice-use machinery rewrites; on the batch-8
/// composition wave-6a's sealed slice constructor delivers the same local
/// FROM THE RAW CALL first, and this rule yields the callee (its raw
/// interface is consumed by that delivery). Both are deliveries; nothing
/// reverts in either.
#[test]
fn w6l_walking_caller_receives_a_fallback_extent_slice() {
    let observed = observe(HEMAN_WALK);
    let data = decision_of(&observed, "heman_image_sample::data");
    assert!(
        data.starts_with("Slice {"),
        "data={data}; failures={:?}",
        observed.failures
    );
    let mine = observed
        .plans
        .iter()
        .find(|(function, _)| function == "heman_image_texel")
        .map(|(_, plan)| plan.clone());
    if let Some(plan) = &mine {
        assert!(
            plan.contains("through_raw_field=arg1/deref1/field"),
            "{plan}"
        );
        assert!(plan.contains("form=slice"), "{plan}");
    }
    let RewriteOutcome::Emitted {
        source,
        reverted_count,
        raw_boundary_artifacts,
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
        !text.contains("data=data.offset(1);"),
        "the walk is rewritten: {text}"
    );
    if mine.is_none() {
        // The composition: the callee keeps its raw interface.
        assert!(
            text.contains(
                "fn__crat_safe_heman_image_texel(mutimg:&heman_image,mutx:i32,muty:i32)->*mutf32"
            ),
            "{text}"
        );
        return;
    }
    assert!(
        text.contains("fn__crat_safe_heman_image_texel<'a>(mutimg:&'aheman_image,mutx:i32,muty:i32)->&'amut[f32]"),
        "{text}"
    );
    assert!(
        text.contains("returncore::slice::from_raw_parts_mut(((*img).data).offset("),
        "{text}"
    );
    assert!(text.contains(",crate::FALLBACK_SLICE_EXTENT)"), "{text}");
    assert!(text.contains("__crat_result.as_mut_ptr()"), "{text}");
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
        event.extent,
        super::bridge_receipt::BridgeExtentKind::Fallback
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
    assert_eq!(row.terminal_interface, "slice-mut");
    assert!(
        raw_boundary_artifacts.outbound_return_error.is_none(),
        "{:?}",
        raw_boundary_artifacts.outbound_return_error
    );
}

/// heman `heman_image_texel` with BOTH caller shapes (the corpus reality: 10
/// walking callers, 3 thin ones). One return form serves every caller: the
/// walker decides it (slice); the thin caller is held typed, never mis-typed,
/// and its owner does not revert.
const HEMAN_MIXED: &str = r#"
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
#[no_mangle]
pub unsafe extern "C" fn row_sum(mut src: *mut heman_image, mut dst: *mut heman_image, mut dstx: i32, mut y: i32) -> f32 {
    let mut width = (*src).width;
    let mut x = 0;
    let mut sum = 0.0f32;
    while x < width {
        let mut srcp = heman_image_texel(src, x, y);
        let mut dstp = heman_image_texel(dst, dstx + x, y);
        sum += *dstp + *srcp;
        x += 1;
    }
    sum
}
"#;

#[test]
fn w6l_mixed_callers_deliver_thin_and_the_walker_is_constructed_over_the_view() {
    let observed = observe(HEMAN_MIXED);
    let data = decision_of(&observed, "heman_image_sample::data");
    assert!(
        data.starts_with("Slice {"),
        "data={data}; failures={:?}",
        observed.failures
    );
    let RewriteOutcome::Emitted {
        source,
        reverted_count,
        degradations,
        ..
    } = emitted(
        "heman-mixed",
        HEMAN_MIXED,
        &["row_sum", "heman_image_sample", "heman_image_texel"],
    )
    else {
        panic!("heman mixed emission degraded");
    };
    println!("W6L-MIXED-EMITTED\n{source}\nW6L-MIXED-END\n{degradations:?}");
    assert_eq!(reverted_count, 0);
    let text = compact(&source);
    // Wave 6 (the initializer-channel composition): one thin caller makes
    // the return THIN and the thin callers deliver as inferred references;
    // the walking caller is typed by its sealed slice constructor rendered
    // over this lane's view of the adapted call — both deliver, nothing is
    // held on the form any more.
    for label in ["row_sum::srcp", "row_sum::dstp"] {
        let decision = decision_of(&observed, label);
        assert!(decision.contains("InferredRef"), "{label}={decision}");
    }
    assert!(text.contains("->&'amutf32"), "{text}");
    assert!(
        text.contains("letmutsrcp:&f32=__crat_safe_heman_image_texel(src,x,y);"),
        "{text}"
    );
    assert!(text.contains("sum+=*dstp+*srcp;"), "{text}");
    assert!(
        text.contains("letmutdata:&[f32]=core::slice::from_raw_parts({let__crat_native_result_9_11:&mutf32=(__crat_safe_heman_image_texel(img,x,y));(core::ptr::from_mut(&mut*__crat_native_result_9_11))as*mutf32},crate::FALLBACK_SLICE_EXTENT);"),
        "{text}"
    );
    assert!(
        text.contains("letfresh1=data[0];data=&data[1..];"),
        "{text}"
    );
    assert!(degradations.is_empty(), "{degradations:?}");
}

/// brotli `StartPosQueueAt` / `UpdateNodes` (subjects `UpdateNodes::posdata#54`,
/// `posdata_0#85`): the return points INTO an inline array field of the
/// parameter's pointee — not a pointer stored in a field.
const BROTLI_QUEUE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
pub struct PosData { pub pos: usize, pub distance_cache: [i32; 4], pub costdiff: f32, pub cost: f32 }
pub struct StartPosQueue { pub q_: [PosData; 8], pub idx_: usize }
unsafe extern "C" fn StartPosQueueAt(mut self_0: *const StartPosQueue, mut k: usize) -> *const PosData {
    return &*((*self_0).q_).as_ptr().offset((k.wrapping_sub((*self_0).idx_) & 7) as isize) as *const PosData;
}
unsafe extern "C" fn StartPosQueueSize(mut self_0: *const StartPosQueue) -> usize {
    if (*self_0).idx_ < 8 { (*self_0).idx_ } else { 8 }
}
unsafe extern "C" fn UpdateNodes(mut queue: *const StartPosQueue, max_iters: usize, pos: usize) -> f32 {
    let mut posdata = StartPosQueueAt(queue, 0);
    let mut min_cost = (*posdata).cost + (*posdata).pos as f32;
    let mut k: usize = 0;
    while k < max_iters && k < StartPosQueueSize(queue) {
        let mut posdata_0 = StartPosQueueAt(queue, k);
        let start = (*posdata_0).pos;
        min_cost += (*posdata_0).costdiff + start as f32;
        k = k.wrapping_add(1);
    }
    min_cost
}
"#;

/// Witness 9 (wave 2, the pointee class) — the return points into the
/// parameter's own pointee; NB5-O carries `Arg/deref0 → Return` directly; the
/// bridge is the existing T1 reborrow with no waiver; the thin callers are
/// inferred safe.
#[test]
fn w6l_return_into_the_parameter_pointee_is_a_t1_permit() {
    let observed = observe(BROTLI_QUEUE);
    let posdata = decision_of(&observed, "UpdateNodes::posdata");
    assert!(
        posdata.starts_with("InferredRef { mutable: false"),
        "posdata={posdata}; failures={:?}",
        observed.failures
    );
    let posdata_0 = decision_of(&observed, "UpdateNodes::posdata_0");
    assert!(
        posdata_0.starts_with("InferredRef { mutable: false"),
        "{posdata_0}"
    );
    let (_, plan) = observed
        .plans
        .iter()
        .find(|(function, _)| function == "StartPosQueueAt")
        .unwrap_or_else(|| panic!("queue plan; {:?}", observed.plans));
    assert!(plan.contains("return_lifetime_reused=true"), "{plan}");
    assert!(
        !plan.contains("through_raw_field"),
        "no collapse for the pointee class: {plan}"
    );
    let RewriteOutcome::Emitted {
        source,
        reverted_count,
        raw_boundary_artifacts,
        ..
    } = emitted("brotli-queue", BROTLI_QUEUE, &[])
    else {
        panic!("brotli queue emission degraded");
    };
    println!("W6L-QUEUE-EMITTED\n{source}\nW6L-QUEUE-END");
    assert_eq!(reverted_count, 0);
    let text = compact(&source);
    assert!(
        text.contains("fnStartPosQueueAt<'a>(mutself_0:&'aStartPosQueue,mutk:usize)->&'aPosData"),
        "{text}"
    );
    assert!(
        text.contains("letmutposdata:&crate::PosData=StartPosQueueAt(queue,0);"),
        "{text}"
    );
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
        event.retention,
        super::bridge_receipt::BridgeRetentionTier::T1
    );
    assert!(event.waiver_id.is_none());
    assert!(
        raw_boundary_artifacts.outbound_return_error.is_none(),
        "{:?}",
        raw_boundary_artifacts.outbound_return_error
    );
}

const HEMAN_FILL: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
pub struct heman_image { pub width: i32, pub height: i32, pub nbands: i32, pub data: *mut f32 }
#[no_mangle]
pub unsafe extern "C" fn heman_image_texel(mut img: *mut heman_image, mut x: i32, mut y: i32) -> *mut f32 {
    return ((*img).data).offset(((y * (*img).width * (*img).nbands) as isize) + ((x * (*img).nbands) as isize));
}
#[no_mangle]
pub unsafe extern "C" fn fill(mut img: *mut heman_image, mut x: i32, mut y: i32, v: f32) {
    let mut t = heman_image_texel(img, x, y);
    *t = v;
}
"#;

/// lil `find_cmd` / `lil_parse` (subject `lil_parse::cmd#63`): the callee
/// returns a pointer VALUE read out of an array field of the parameter's
/// pointee, or null; the caller tests it and reads through it.
const LIL_FIND: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
pub struct Func { pub name: *const u8, pub argc: i32 }
pub struct Lil { pub cmds: usize, pub cmd: *mut *mut Func }
unsafe extern "C" fn find_cmd(mut lil: *mut Lil, mut argc: i32) -> *mut Func {
    if (*lil).cmds > 0 {
        let mut i = (*lil).cmds.wrapping_sub(1);
        loop {
            if (**((*lil).cmd).offset(i as isize)).argc == argc {
                return *((*lil).cmd).offset(i as isize);
            }
            if i == 0 { break; }
            i = i.wrapping_sub(1);
        }
    }
    return 0 as *mut Func;
}
unsafe extern "C" fn lil_parse(mut lil: *mut Lil, mut argc: i32) -> i32 {
    let mut cmd = find_cmd(lil, argc);
    if cmd.is_null() { return 0; }
    return (*cmd).argc;
}
"#;

/// Pin (wave 2, an export gap, not a rule): the pointer VALUE read out of a
/// pointer-array field (`*((*lil).cmd).offset(i)`) has no origin edge into
/// the return in the NB5-O summary (the field slot is carried at depth 0
/// only), so the callee earns nothing and the caller stays typed-held with
/// `lifetime-origin-absent`. The owner keeps its other deliveries.
#[test]
fn w6l_pointer_value_read_from_a_pointer_array_field_is_held_origin_absent() {
    let observed = observe(LIL_FIND);
    let cmd = decision_of(&observed, "lil_parse::cmd");
    assert!(cmd.contains("ReturnNotAdapted"), "{cmd}");
    assert_eq!(
        failure_of(&observed, "lil_parse::cmd"),
        Some(LifetimeFailure::OriginAbsent),
        "{:?}",
        observed.failures
    );
    assert!(observed.plans.is_empty(), "{:?}", observed.plans);
    let RewriteOutcome::Emitted {
        reverted_count,
        emitted_count,
        ..
    } = emitted("lil-find", LIL_FIND, &[])
    else {
        panic!("lil find emission degraded");
    };
    assert_eq!(reverted_count, 0);
    assert_eq!(emitted_count, 2, "the two `lil` parameters still deliver");
}

/// heman `kmAABB3Scale` (subject `kmAABB3Scale::pOut#1`, `escapes-via-return`):
/// an unimplemented stub — `__assert_fail(..)` then `return pOut`.
const KM_AABB3_SCALE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
pub struct kmAABB3 { pub min: [f32; 3], pub max: [f32; 3] }
unsafe extern "C" { fn __assert_fail(assertion: *const u8, file: *const u8, line: u32, function: *const u8) -> !; }
#[no_mangle]
pub unsafe extern "C" fn kmAABB3Scale(mut pOut: *mut kmAABB3, mut pIn: *const kmAABB3, mut s: f32) -> *mut kmAABB3 {
    {
        __assert_fail(b"0 && \"Not implemented\"\0" as *const u8, b"../kazmath/aabb3.c\0" as *const u8, 81, b"kmAABB3Scale\0" as *const u8);
    }
    return pOut;
}
#[no_mangle]
pub unsafe extern "C" fn use_scale(mut a: *mut kmAABB3, mut b: *const kmAABB3) -> f32 {
    let mut r = kmAABB3Scale(a, b, 2.0);
    (*r).min[0]
}
"#;

/// Wave 4 — the dead return: `kmAABB3Scale` never reaches its `return pOut`
/// (a diverging `__assert_fail` precedes it), so NB5-O carries no origin
/// edge; the bare-parameter tie is granted on the derived overlay (vacuously
/// sound) and the caller's local is inferred safe. What still holds the
/// emission is the existing `seam-shared-to-mut` gate: `pOut` is decided
/// SHARED (its only use is the dead return) while the `*mut` ABI asks for a
/// mutable view — a typed class hold, no revert.
#[test]
fn w6l_dead_return_of_a_bare_parameter_ties_to_that_parameter() {
    let observed = observe(KM_AABB3_SCALE);
    let p_out = decision_of(&observed, "kmAABB3Scale::pOut");
    assert!(
        p_out.starts_with("Ref { mutable: false"),
        "pOut={p_out}; failures={:?}",
        observed.failures
    );
    let r = decision_of(&observed, "use_scale::r");
    assert!(
        r.starts_with("InferredRef {"),
        "r={r}; failures={:?}",
        observed.failures
    );
    let (_, plan) = observed
        .plans
        .iter()
        .find(|(function, _)| function == "kmAABB3Scale")
        .unwrap_or_else(|| panic!("scale plan; {:?}", observed.plans));
    assert!(plan.contains("return_lifetime_reused=true"), "{plan}");
    assert!(!plan.contains("through_raw_field"), "{plan}");
    let RewriteOutcome::Emitted {
        reverted_count,
        degradations,
        ..
    } = emitted("km-scale", KM_AABB3_SCALE, &["kmAABB3Scale", "use_scale"])
    else {
        panic!("km scale emission degraded");
    };
    assert_eq!(reverted_count, 0);
    let p_out = degradations
        .iter()
        .find(|degradation| degradation.subject == "kmAABB3Scale::pOut#1")
        .expect("pOut class hold");
    assert!(
        format!("{:?}", p_out.reason).contains("seam-shared-to-mut"),
        "{:?}",
        p_out.reason
    );
}

/// The dead-return control: a LIVE return of the same shape is the existing
/// bare-parameter permit (no overlay), and a dead return that hands back
/// something other than a bare parameter stays held.
#[test]
fn w6l_dead_return_needs_a_bare_parameter() {
    let source = KM_AABB3_SCALE.replace(
        "    return pOut;\n",
        "    return (*pOut).min.as_mut_ptr() as *mut kmAABB3;\n",
    );
    let observed = observe(&source);
    let r = decision_of(&observed, "use_scale::r");
    assert!(r.contains("ReturnNotAdapted"), "{r}");
    assert_eq!(
        failure_of(&observed, "use_scale::r"),
        Some(LifetimeFailure::OriginAbsent),
        "{:?}",
        observed.failures
    );
    assert!(observed.plans.is_empty(), "{:?}", observed.plans);
}

/// heman `heman_image_texel` with the receivers the raw-receiver twin does
/// not serve: a cast initializer (`heman_lighting_apply`), an immediate
/// deref read into a field (`heman_lighting_compute_normals`), a compound
/// assignment through the call (`heman_ops_accumulate`), an assignment to an
/// existing raw local (`heman_ops_warp_core`), and a walker that fixes the
/// slice form. One unadaptable site drops the callee's class today.
const HEMAN_EXPRESSION_RECEIVERS: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments)]
pub struct heman_image { pub width: i32, pub height: i32, pub nbands: i32, pub data: *mut f32 }
pub struct kmVec3 { pub x: f32, pub y: f32, pub z: f32 }
#[no_mangle]
pub unsafe extern "C" fn heman_image_texel(mut img: *mut heman_image, mut x: i32, mut y: i32) -> *mut f32 {
    return ((*img).data).offset(((y * (*img).width * (*img).nbands) as isize) + ((x * (*img).nbands) as isize));
}
#[no_mangle]
pub unsafe extern "C" fn heman_draw_points(mut target: *mut heman_image, mut i: i32, mut j: i32, val: f32) {
    let mut texel = heman_image_texel(target, i, j);
    let mut c = 0;
    while c < (*target).nbands {
        *texel = val;
        texel = texel.offset(1);
        c += 1;
    }
}
#[no_mangle]
pub unsafe extern "C" fn heman_lighting_apply(mut normals: *mut heman_image, mut x: i32, mut y: i32) -> f32 {
    let mut N = heman_image_texel(normals, x, y) as *mut kmVec3;
    (*N).x + (*N).y
}
#[no_mangle]
pub unsafe extern "C" fn heman_lighting_compute_normals(mut heightmap: *mut heman_image, mut x: i32, mut y: i32) -> f32 {
    let mut p = kmVec3 { x: 0.0, y: 0.0, z: 0.0 };
    p.z = *heman_image_texel(heightmap, x, y);
    p.z
}
#[no_mangle]
pub unsafe extern "C" fn heman_ops_accumulate(mut result: *mut heman_image, mut i: i32, mut j: i32, v: f32) {
    *heman_image_texel(result, i, j) += v;
}
#[no_mangle]
pub unsafe extern "C" fn heman_ops_warp_core(mut secondary: *mut heman_image, mut x: i32, mut y: i32) -> f32 {
    let mut src = 0 as *mut f32;
    src = heman_image_texel(secondary, x, y);
    *src
}
"#;

/// Wave 5 — every one of these callers keeps its delivery: the changed
/// return interface is restored to the call's original raw type at the cast
/// initializer, the immediate derefs, the compound assignment and the
/// assignment receiver (the receiving-local twin's own shape), and the
/// callee's class is placed. Each site is a receipted T2 view.
#[test]
fn w6l_expression_position_receivers_keep_the_callee_class_placed() {
    let RewriteOutcome::Emitted {
        source,
        reverted_count,
        degradations,
        raw_boundary_artifacts,
        ..
    } = emitted(
        "heman-expression-receivers",
        HEMAN_EXPRESSION_RECEIVERS,
        &[
            "heman_draw_points",
            "heman_image_texel",
            "heman_lighting_apply",
            "heman_lighting_compute_normals",
            "heman_ops_accumulate",
            "heman_ops_warp_core",
        ],
    )
    else {
        panic!("heman expression receivers emission degraded");
    };
    println!("W6L-EXPR-EMITTED\n{source}\nW6L-EXPR-END\n{degradations:?}");
    assert_eq!(reverted_count, 0);
    let text = compact(&source);
    assert!(
        !degradations
            .iter()
            .any(|d| format!("{:?}", d.reason).contains("raw-receiver-result-unavailable")),
        "{degradations:?}"
    );
    // Wave 6 (the initializer-channel composition): a walker beside thin
    // receivers makes the return THIN; the walker is typed by its sealed
    // slice constructor rendered over this lane's view of the adapted call,
    // the cast and the store take their views, the immediate derefs read the
    // reference natively — every receiver of one callee delivers.
    let view = |temporary: &str, args: &str| {
        format!(
            "{{let{temporary}:&mutf32=(__crat_safe_heman_image_texel({args}));(core::ptr::from_mut(&mut*{temporary}))as*mutf32}}"
        )
    };
    assert!(text.contains("->&'staticmutf32"), "{text}");
    assert!(
        text.contains(&format!(
            "letmuttexel:&mut[f32]=core::slice::from_raw_parts_mut({},crate::FALLBACK_SLICE_EXTENT);",
            view("__crat_native_result_13_11", "target,i,j")
        )),
        "{text}"
    );
    assert!(
        text.contains("texel[0]=val;texel=&muttexel[1..];"),
        "{text}"
    );
    // (a) the cast receiver (wave 6): the local is an inferred reference of
    // the CAST's pointee, initialised by a typed reborrow of the view cast —
    // `let mut N: &kmVec3 = &*({view} as *mut kmVec3)` — under the view's
    // own T2 receipt; its field reads are untouched.
    assert!(
        text.contains(&format!(
            "letmutN:&crate::kmVec3=&*({}as*mutkmVec3);(*N).x+(*N).y",
            view("__crat_native_result_14_10", "normals,x,y")
        )),
        "{text}"
    );
    assert!(
        !degradations
            .iter()
            .any(|d| d.subject == "heman_lighting_apply::N"),
        "{degradations:?}"
    );
    // (b) the immediate deref read and the compound assignment, natively.
    assert!(
        text.contains("p.z=*__crat_safe_heman_image_texel(heightmap,x,y);"),
        "{text}"
    );
    assert!(
        text.contains("*__crat_safe_heman_image_texel(result,i,j)+=v;"),
        "{text}"
    );
    // (c) the store into the null-initialised local: the raw view, or the
    // optional store composed OVER it where another family delivers `src`.
    let store = view("__crat_native_result_17_19", "secondary,x,y");
    assert!(
        text.contains(&format!("src={store};"))
            || (text.contains("letmutsrc:Option<&f32>=None;")
                && text.contains(&format!("src=({store}as*constf32).as_ref();"))),
        "{text}"
    );
    let views = raw_boundary_artifacts
        .bridge_events
        .iter()
        .filter(|event| {
            event.site.bridge_kind == "native-result-expression-raw"
                && event.stage == super::bridge_receipt::BridgeReceiptStage::Terminal
        })
        .collect::<Vec<_>>();
    assert_eq!(views.len(), 3, "{views:#?}");
    for event in &views {
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
    }
    assert!(
        raw_boundary_artifacts.outbound_return_error.is_none(),
        "{:?}",
        raw_boundary_artifacts.outbound_return_error
    );
}

/// Wave 5 — a result position outside the served shapes (the receiver of a
/// method call) holds the callee's class typed; nothing reverts and no site
/// is passed over silently.
#[test]
fn w6l_unserved_result_position_holds_the_callee_class_typed() {
    let source = HEMAN_EXPRESSION_RECEIVERS.replace(
        "    *heman_image_texel(result, i, j) += v;\n",
        "    if heman_image_texel(result, i, j).is_null() { return; }\n",
    );
    let RewriteOutcome::Emitted {
        reverted_count,
        degradations,
        ..
    } = emitted(
        "heman-unserved-position",
        &source,
        &[
            "heman_draw_points",
            "heman_image_texel",
            "heman_lighting_apply",
            "heman_lighting_compute_normals",
            "heman_ops_accumulate",
            "heman_ops_warp_core",
        ],
    )
    else {
        panic!("heman unserved position emission degraded");
    };
    assert_eq!(reverted_count, 0);
    if !observe(&source)
        .plans
        .iter()
        .any(|(function, _)| function == "heman_image_texel")
    {
        // R217-2(a) re-pin (batch-8 composition): the callee is not this
        // rule's (see above); nothing is held for an unserved position
        // because no native result is planned. The thin variant below keeps
        // the hold witnessed on every head.
        assert!(
            !degradations
                .iter()
                .any(|d| d.subject == "heman_image_texel::img#1"),
            "{degradations:?}"
        );
        return;
    }
    let img = degradations
        .iter()
        .find(|d| d.subject == "heman_image_texel::img#1")
        .expect("the callee's class hold");
    let reason = format!("{:?}", img.reason);
    assert!(
        reason.contains(
            "native-result-expression-unavailable:native-result-expression:PositionUnbuilt("
        ) && reason.contains("method-receiver"),
        "{:?}",
        img.reason
    );
}

/// The thin-form twin of `HEMAN_EXPRESSION_RECEIVERS`: no walker (so no
/// other family constructs a slice over the raw call on any head) and no
/// cast receiver; the callee returns `&'static mut f32` (R401-8 untied view
/// for the exclusive parameter). Immediate derefs of a thin result read the
/// reference as it stands; only the assignment into an existing raw local
/// needs the expression carrier.
fn heman_thin_expression_receivers() -> String {
    HEMAN_EXPRESSION_RECEIVERS
        .replace(
            "    let mut texel = heman_image_texel(target, i, j);\n    let mut c = 0;\n    while c < (*target).nbands {\n        *texel = val;\n        texel = texel.offset(1);\n        c += 1;\n    }\n",
            "    let mut texel = heman_image_texel(target, i, j);\n    *texel = val;\n",
        )
        .replace(
            "    let mut N = heman_image_texel(normals, x, y) as *mut kmVec3;\n    (*N).x + (*N).y\n",
            "    let mut N = heman_image_texel(normals, x, y);\n    *N\n",
        )
}

const HEMAN_THIN_EXPOSED: &[&str] = &[
    "heman_draw_points",
    "heman_image_texel",
    "heman_lighting_apply",
    "heman_lighting_compute_normals",
    "heman_ops_accumulate",
    "heman_ops_warp_core",
];

/// Wave 5 (thin form) — the callee's class is placed with every receiver
/// served: the bound locals as `&mut f32` / `&f32`, the immediate derefs
/// natively, the raw-local assignment through one receipted T2 view.
#[test]
fn w6l_thin_expression_position_receivers_keep_the_callee_class_placed() {
    let fixture = heman_thin_expression_receivers();
    let RewriteOutcome::Emitted {
        source,
        reverted_count,
        degradations,
        raw_boundary_artifacts,
        ..
    } = emitted(
        "heman-thin-expression-receivers",
        &fixture,
        HEMAN_THIN_EXPOSED,
    )
    else {
        panic!("heman thin expression receivers emission degraded");
    };
    println!("W6L-THIN-EMITTED\n{source}\nW6L-THIN-END\n{degradations:?}");
    assert_eq!(reverted_count, 0);
    let text = compact(&source);
    assert!(text.contains("->&'staticmutf32"), "{text}");
    assert!(
        !degradations
            .iter()
            .any(|d| d.subject == "heman_image_texel::img#1"),
        "{degradations:?}"
    );
    assert!(
        text.contains("letmuttexel:&mutf32=__crat_safe_heman_image_texel(target,i,j);*texel=val;"),
        "{text}"
    );
    assert!(
        text.contains("letmutN:&f32=__crat_safe_heman_image_texel(normals,x,y);*N"),
        "{text}"
    );
    assert!(
        text.contains("p.z=*__crat_safe_heman_image_texel(heightmap,x,y);"),
        "{text}"
    );
    assert!(
        text.contains("*__crat_safe_heman_image_texel(result,i,j)+=v;"),
        "{text}"
    );
    let views = raw_boundary_artifacts
        .bridge_events
        .iter()
        .filter(|event| {
            event.site.bridge_kind == "native-result-expression-raw"
                && event.stage == super::bridge_receipt::BridgeReceiptStage::Terminal
        })
        .collect::<Vec<_>>();
    // The raw-local assignment takes the view; where another family
    // delivers that null-initialised local as an optional view (the batch-8
    // composition), its store is composed OVER the view by the nested-edit
    // composition (wave 6) and both deliver.
    let view = "{let__crat_native_result_17_19:&mutf32=(__crat_safe_heman_image_texel(secondary,x,y));(core::ptr::from_mut(&mut*__crat_native_result_17_19))as*mutf32}";
    assert!(
        text.contains(&format!("src={view};"))
            || (text.contains("letmutsrc:Option<&f32>=None;")
                && text.contains(&format!("src=({view}as*constf32).as_ref();"))),
        "{text}"
    );
    let [event] = views.as_slice() else {
        panic!("one terminal expression view: {views:#?}");
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
        raw_boundary_artifacts.outbound_return_error.is_none(),
        "{:?}",
        raw_boundary_artifacts.outbound_return_error
    );
}

/// Wave 5 (thin form) — the method-receiver position holds the callee's
/// class typed on every head where the callee is this rule's.
#[test]
fn w6l_thin_unserved_result_position_holds_the_callee_class_typed() {
    let fixture = heman_thin_expression_receivers().replace(
        "    *heman_image_texel(result, i, j) += v;\n",
        "    if heman_image_texel(result, i, j).is_null() { return; }\n",
    );
    let RewriteOutcome::Emitted {
        reverted_count,
        degradations,
        ..
    } = emitted("heman-thin-unserved-position", &fixture, HEMAN_THIN_EXPOSED)
    else {
        panic!("heman thin unserved position emission degraded");
    };
    assert_eq!(reverted_count, 0);
    if !observe(&fixture)
        .plans
        .iter()
        .any(|(function, _)| function == "heman_image_texel")
    {
        // R217-2(a) re-pin (batch-8 composition, dry3): another family
        // delivers the null-initialised receiving local (`src`) from the raw
        // call at its own stage and, the callee's class being held at this
        // rule's stage anyway, the callee yields to it (no plan, no class
        // hold of this rule's); the other receivers are typed holds.
        assert!(
            !degradations
                .iter()
                .any(|d| d.subject == "heman_image_texel::img#1"),
            "{degradations:?}"
        );
        assert!(
            degradations
                .iter()
                .any(|d| d.subject == "heman_draw_points::texel"
                    && format!("{:?}", d.reason) == "ReturnNotAdapted"),
            "{degradations:?}"
        );
        return;
    }
    let img = degradations
        .iter()
        .find(|d| d.subject == "heman_image_texel::img#1")
        .expect("the callee's class hold");
    let reason = format!("{:?}", img.reason);
    assert!(
        reason.contains(
            "native-result-expression-unavailable:native-result-expression:PositionUnbuilt("
        ) && reason.contains("method-receiver"),
        "{reason}"
    );
}
