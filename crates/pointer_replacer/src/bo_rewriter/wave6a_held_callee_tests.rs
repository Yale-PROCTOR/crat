//! R575-5 — the held-callee disposition.
//!
//! `callee_parameter_input`'s alternative for a caller KEPT beside a HELD
//! callee renders the caller's argument against the callee's raw input formal.
//! The raw boundary computed the site's disposition for the kept callee, whose
//! formal is decided safe (`target_stays_raw = 0`), and there R481-2's tier-2
//! retention waiver declines: no raw view exists. In the held world the formal
//! IS raw and the waiver applies. brotli's `BrotliCompressBufferQuality10` →
//! `InitOrStitchToPreviousBlock(m, &mut hasher, ..)` is the shape: the callee
//! stores `&mut (*hasher).common` into the `Hasher` itself (a real retention
//! that outlives the call), so nothing discharges it and the waiver is the
//! instrument.

use std::collections::BTreeSet;

use super::{
    bridge_receipt::{BridgeRetentionTier, SignatureClassId},
    decision::seam::SeamInputRendering,
};

struct Run {
    /// The raw boundary's public dispositions TSV.
    dispositions: String,
    /// `(current_source rendering, bridge (tier, waiver))` of every held-callee
    /// input at a call of `callee` from `caller`.
    inputs: Vec<(String, Option<(BridgeRetentionTier, Option<String>)>)>,
    /// The root file emitted with `callee`'s class held.
    held_source: String,
}

fn run(input: &str, caller: &str, callee: &str) -> Run {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("ast");
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("decide");
        let callee_did = table
            .entries
            .iter()
            .map(|(subject, _)| subject.fn_did)
            .find(|did| tcx.def_path_str(did.to_def_id()).ends_with(callee))
            .expect("callee has subjects");
        let emission = super::emit_files(
            tcx,
            &table,
            &rustc_hash::FxHashSet::default(),
            &ctx.retained_c9_plans,
        )
        .expect("emit");
        let inputs = emission
            .plan
            .terminal_call_plans
            .callee_parameter_inputs
            .iter()
            .filter(|(key, input)| {
                key.0 == SignatureClassId::of(callee_did)
                    && tcx.def_path_str(input.caller.to_def_id()).ends_with(caller)
            })
            .map(|(_, input)| match &input.current_source {
                Ok(alternative) => (
                    match &alternative.rendering {
                        SeamInputRendering::ZeroSyntax { .. } => "zero-syntax".to_owned(),
                        SeamInputRendering::Adapter { replacement, .. } => {
                            format!("adapter:{replacement}")
                        }
                    },
                    alternative
                        .bridge
                        .as_ref()
                        .map(|bridge| (bridge.retention, bridge.waiver_id.clone())),
                ),
                Err(reason) => ((*reason).to_owned(), None),
            })
            .collect();
        let mut held = emission.plan.held_classes();
        held.insert(SignatureClassId::of(callee_did));
        let (files, ..) = super::round_files(
            tcx,
            &capture,
            &emission.plan,
            &emission.texts,
            &held,
            &BTreeSet::new(),
            emission.plan.root_file.as_ref(),
            &table,
        )
        .expect("round");
        Run {
            dispositions: ctx.raw_boundary_artifacts.dispositions.clone(),
            inputs,
            held_source: files.into_values().next().expect("root file"),
        }
    })
    .expect("fixture compiles")
}

/// The disposition rows whose `callee` column ends with `callee`.
fn rows<'a>(dispositions: &'a str, callee: &str) -> Vec<&'a str> {
    dispositions
        .lines()
        .skip(1)
        .filter(|line| line.split('\t').nth(3).is_some_and(|c| c.ends_with(callee)))
        .collect()
}

fn compact(text: &str) -> String {
    text.chars().filter(|c| !c.is_whitespace()).collect()
}

/// brotli's `BrotliCompressBufferQuality10` → `InitOrStitchToPreviousBlock`,
/// reduced: `hasher` is a value local of the caller; the callee's setup stores
/// `&mut (*hasher).common` into the `Hasher` itself, and the caller reads the
/// stored pointer after the call.
const QUALITY10: &str = "#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]\n\
    #[derive(Copy, Clone)]\n\
    #[repr(C)]\n\
    pub struct Common { pub n: u32 }\n\
    #[derive(Copy, Clone)]\n\
    #[repr(C)]\n\
    pub struct H2 { pub common: *mut Common, pub k: u32 }\n\
    #[derive(Copy, Clone)]\n\
    #[repr(C)]\n\
    pub struct Hasher { pub common: Common, pub h2: H2 }\n\
    unsafe fn initialize_h2(common: *mut Common, self_0: *mut H2) { (*self_0).common = common; (*self_0).k = 0; }\n\
    unsafe fn hasher_setup(hasher: *mut Hasher) { initialize_h2(&mut (*hasher).common, &mut (*hasher).h2); }\n\
    unsafe fn init_or_stitch(hasher: *mut Hasher, x: u32) { hasher_setup(hasher); (*hasher).h2.k = x; }\n\
    pub unsafe fn quality10(out: *mut u32, x: u32) {\n\
        let mut hasher = Hasher { common: Common { n: 0 }, h2: H2 { common: 0 as *mut Common, k: 0 } };\n\
        init_or_stitch(&mut hasher, x);\n\
        *out = (*hasher.h2.common).n + hasher.h2.k;\n\
    }\n";

/// The witness: the held-callee input of `&mut hasher` is admitted as written,
/// spending the tier-2 retention waiver (receipted), and the caller stays
/// converted beside the held callee instead of closing.
#[test]
fn w6a_r575_a_value_local_address_at_a_held_callee_takes_the_retention_waiver() {
    // Restated under R878-1 (B) (relay 304; main 196): the retained-access check of
    // record holds `hasher_setup::hasher` (`initialize_h2` keeps `&mut (*hasher).common`
    // in `(*hasher).h2`, a self-reference through a callee; the tier's positive-retention
    // row is at that address, a pointer into the subject, not its own value), and
    // `init_or_stitch::hasher` follows it raw (`held:into-held-formal`). The callee's
    // formal is then raw by decision, not a converted formal of a held class: no input
    // is admitted and no waiver is spent, and `&mut hasher` is the input's own coercion.
    // The receipt moves; the emitted text below is unchanged.
    let run = run(QUALITY10, "quality10", "init_or_stitch");
    assert_eq!(
        run.inputs,
        Vec::new(),
        "{}\n{}",
        rows(&run.dispositions, "init_or_stitch").join("\n"),
        run.held_source
    );
    let src = compact(&run.held_source);
    assert!(
        src.contains("fninit_or_stitch(hasher:*mutHasher,x:u32)"),
        "the callee is held:\n{}",
        run.held_source
    );
    assert!(
        src.contains("fnquality10(out:&mutu32,x:u32)"),
        "the caller stays converted beside the held callee:\n{}",
        run.held_source
    );
    assert!(
        src.contains("init_or_stitch(&muthasher,x);"),
        "the argument is rendered as written:\n{}",
        run.held_source
    );
}

/// Control: the KEPT callee's site is unchanged — its public disposition is
/// still refused by positive retention, and the held-callee admission never
/// shows there.
#[test]
fn w6a_r575_a_kept_callee_keeps_its_positive_retention_refusal() {
    let run = run(QUALITY10, "quality10", "init_or_stitch");
    let init = rows(&run.dispositions, "init_or_stitch");
    assert!(
        init.iter()
            .any(|row| row.contains("raw-boundary-positive-retention")),
        "{}",
        init.join("\n")
    );
    assert!(
        init.iter().all(|row| !row.contains("held-callee")),
        "{}",
        init.join("\n")
    );
}

/// Control: a retention the analysis cannot resolve (the callee hands the
/// address to a foreign function with no contract row) is not the held-callee
/// disposition's business. Its kept disposition already carries the v1 bridge
/// waiver; no tier-2 retention-waiver (`held-callee`) receipt appears.
#[test]
fn w6a_r575_an_unknown_retention_takes_no_held_callee_receipt() {
    let input = "#![allow(dead_code, unused_unsafe, unused_mut)]\n\
        #[derive(Copy, Clone)]\n\
        #[repr(C)]\n\
        pub struct Rec { pub a: u32 }\n\
        extern \"C\" { fn opaque_keep(r: *mut Rec); }\n\
        unsafe fn pass(r: *mut Rec, x: u32) { (*r).a = x; opaque_keep(r); }\n\
        pub unsafe fn entry(out: *mut u32, x: u32) {\n\
            let mut rec = Rec { a: 0 };\n\
            pass(&mut rec, x);\n\
            *out = rec.a;\n\
        }\n";
    let run = run(input, "entry", "pass");
    println!(
        "R575 unknown-retention control: {:?}\n{}",
        run.inputs,
        rows(&run.dispositions, "pass").join("\n")
    );
    assert_eq!(
        run.inputs,
        vec![("zero-syntax".to_owned(), None)],
        "R473-2's own admission, unreceipted and unchanged:\n{}",
        rows(&run.dispositions, "pass").join("\n")
    );
}

/// brotli's `EncodeData` → `HasherReset(&mut (*s).hasher_)`, reduced (R583-4):
/// the caller's `s` is `kind-raw` (batch 42: model `raw`, `degraded kind-raw`;
/// stated here by the frame override), and the argument is the address of a
/// field reached through that raw formal. The callee is held, so its formal
/// is its raw input form.
const RAW_ROOTED: &str = "#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types)]\n\
    // w6a-r583-raw-rooted-frame\n\
    #[derive(Copy, Clone)]\n\
    #[repr(C)]\n\
    pub struct Hasher { pub n: u32 }\n\
    #[derive(Copy, Clone)]\n\
    #[repr(C)]\n\
    pub struct State { pub k: u32, pub hasher_: Hasher }\n\
    unsafe fn hasher_reset(hasher: *mut Hasher) { (*hasher).n = 0; }\n\
    pub unsafe fn encode_data(s: *mut State, out: *mut u32) {\n\
        hasher_reset(&mut (*s).hasher_);\n\
        *out = (*s).k;\n\
    }\n";

/// The frame: `encode_data::s` is `Raw`, as the model has it on the corpus.
fn raw_rooted(input: &str) -> Run {
    use crate::analyses::borrow_ownership::SlotKind;
    let _frame = super::test_model_override::frame_lock();
    super::test_model_override::set(
        "w6a-r583-raw-rooted-frame",
        Vec::new(),
        vec![("encode_data::s".to_owned(), SlotKind::Raw)],
    );
    let out = run(input, "encode_data", "hasher_reset");
    super::test_model_override::clear();
    out
}

/// **R583-4 — the raw-rooted arm.** An address rooted in a raw formal through
/// undelivered fields, into a held callee's raw formal, crosses no boundary:
/// admitted as written, no bridge and no retention reading, receipted
/// `held-callee-input:raw-rooted`.
#[test]
fn w6a_r583_a_raw_rooted_address_at_a_held_callee_is_admitted_as_written() {
    let run = raw_rooted(RAW_ROOTED);
    assert_eq!(
        run.inputs,
        vec![(
            "zero-syntax".to_owned(),
            Some((BridgeRetentionTier::None, None))
        )],
        "{}\n{}",
        rows(&run.dispositions, "hasher_reset").join("\n"),
        run.held_source
    );
    let src = compact(&run.held_source);
    assert!(
        src.contains("fnhasher_reset(hasher:*mutHasher)"),
        "the callee is held:\n{}",
        run.held_source
    );
    assert!(
        src.contains("fnencode_data(s:*mutState,out:&mutu32)"),
        "the caller stays converted beside the held callee:\n{}",
        run.held_source
    );
    assert!(
        src.contains("hasher_reset(&mut(*s).hasher_);"),
        "the argument is rendered as written:\n{}",
        run.held_source
    );
}

/// The `found_form` of every held-callee input's receipt (`-` for none).
fn receipts(run: &Run) -> Vec<String> {
    run.inputs
        .iter()
        .map(|(rendering, _)| rendering.clone())
        .collect()
}

/// Control (R583-4): a raw LOCAL root is not the ruled shape — the arm reads
/// a formal only, so `let t = s; hasher_reset(&mut (*t).hasher_)` keeps the
/// existing refusal.
#[test]
fn w6a_r583_a_raw_local_root_is_not_the_raw_rooted_arm() {
    use crate::analyses::borrow_ownership::SlotKind;
    let input = RAW_ROOTED.replace(
        "hasher_reset(&mut (*s).hasher_);",
        "let mut t = s; hasher_reset(&mut (*t).hasher_);",
    );
    assert_ne!(input, RAW_ROOTED);
    let _frame = super::test_model_override::frame_lock();
    super::test_model_override::set(
        "w6a-r583-raw-rooted-frame",
        Vec::new(),
        vec![
            ("encode_data::s".to_owned(), SlotKind::Raw),
            ("encode_data::t".to_owned(), SlotKind::Raw),
        ],
    );
    let run = run(&input, "encode_data", "hasher_reset");
    super::test_model_override::clear();
    assert_eq!(
        receipts(&run),
        vec!["callee-parameter-input-raw-boundary-held".to_owned()],
        "{}\n{}",
        rows(&run.dispositions, "hasher_reset").join("\n"),
        run.held_source
    );
}

/// Control (R583-4): the address of the raw formal's own slot (`&mut s`) is
/// not rooted THROUGH it — that is R473-2's value-local question — so it is
/// not the raw-rooted arm.
#[test]
fn w6a_r583_the_formals_own_slot_is_not_raw_rooted() {
    let input = RAW_ROOTED
        .replace(
            "unsafe fn hasher_reset(hasher: *mut Hasher) { (*hasher).n = 0; }",
            "unsafe fn hasher_reset(slot: *mut *mut State) { (**slot).k = 0; }",
        )
        .replace("hasher_reset(&mut (*s).hasher_);", "hasher_reset(&mut s);")
        .replace("encode_data(s: *mut State", "encode_data(mut s: *mut State");
    assert_ne!(input, RAW_ROOTED);
    let run = raw_rooted(&input);
    assert!(
        !run.inputs
            .iter()
            .any(|(_, bridge)| bridge == &Some((BridgeRetentionTier::None, None))),
        "{:?}\n{}\n{}",
        run.inputs,
        rows(&run.dispositions, "hasher_reset").join("\n"),
        run.held_source
    );
}

/// bst's `node` with its two children delivered as owned fields (era-5c's
/// frame), and a caller whose raw formal reaches a key THROUGH a delivered
/// child: `&mut (*(*s).left).key` crosses the field transaction, so it is not
/// raw-rooted.
const THROUGH_DELIVERED: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, non_snake_case)]
// w6a-r583-through-delivered-frame
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}
#[repr(C)]
pub struct node {
    pub key: i32,
    pub left: *mut node,
    pub right: *mut node,
}
#[no_mangle]
pub unsafe extern "C" fn newNode(mut item: i32) -> *mut node {
    let mut temp = malloc(::std::mem::size_of::<node>()) as *mut node;
    (*temp).key = item;
    (*temp).left = 0 as *mut node;
    (*temp).right = 0 as *mut node;
    return temp;
}
#[no_mangle]
pub unsafe extern "C" fn freeTree(mut root: *mut node) {
    if root.is_null() { return; }
    freeTree((*root).left);
    freeTree((*root).right);
    free(root as *mut core::ffi::c_void);
}
unsafe fn reset_key(k: *mut i32) { *k = 0; }
pub unsafe fn touch(s: *mut node, out: *mut i32) {
    reset_key(&mut (*(*s).left).key);
    *out = (*s).key;
}
"#;

/// Control (R583-4): an argument whose path crosses a DELIVERED field
/// transaction is not raw-rooted; the existing rules decide it.
#[test]
fn w6a_r583_a_path_through_a_delivered_field_is_not_raw_rooted() {
    use crate::analyses::borrow_ownership::SlotKind;
    let _frame = super::test_model_override::frame_lock();
    super::test_model_override::set(
        "w6a-r583-through-delivered-frame",
        vec![
            ("node".to_owned(), 1, SlotKind::Owning),
            ("node".to_owned(), 2, SlotKind::Owning),
        ],
        vec![
            ("newNode::temp".to_owned(), SlotKind::Owning),
            ("freeTree::root".to_owned(), SlotKind::Owning),
            ("touch::s".to_owned(), SlotKind::Raw),
        ],
    );
    let run = run(THROUGH_DELIVERED, "touch", "reset_key");
    super::test_model_override::clear();
    println!(
        "R583 delivered control: {:?}\n{}\n{}",
        run.inputs,
        rows(&run.dispositions, "reset_key").join("\n"),
        run.held_source
    );
    assert!(
        run.held_source.contains("pub left: Option<Box<node>>"),
        "the field is delivered:\n{}",
        run.held_source
    );
    assert!(
        !run.inputs
            .iter()
            .any(|(_, bridge)| bridge == &Some((BridgeRetentionTier::None, None))),
        "{:?}\n{}",
        run.inputs,
        run.held_source
    );
}

/// Control (R583-4, the arm's premise): the same address shape rooted in a
/// SAFE formal. `quality(p, ..)` passes `&mut (*p).hasher` to the held
/// `init_or_stitch`, which retains `&mut (*hasher).common` inside the hasher
/// itself — §130's channel IS present (the caller's `p` is a reference), so
/// the retention reading is owed and the raw-rooted arm must not admit it.
#[test]
fn w6a_r583_a_safe_root_is_not_raw_rooted() {
    let cut = QUALITY10
        .find("pub unsafe fn quality10")
        .expect("the Quality10 caller");
    let input = format!(
        "{}{}",
        &QUALITY10[..cut],
        "#[derive(Copy, Clone)]\n\
        #[repr(C)]\n\
        pub struct Outer { pub hasher: Hasher }\n\
        pub unsafe fn quality(p: *mut Outer, out: *mut u32, x: u32) {\n\
            init_or_stitch(&mut (*p).hasher, x);\n\
            *out = (*(*p).hasher.h2.common).n + (*p).hasher.h2.k;\n\
        }\n"
    );
    assert_ne!(
        input, QUALITY10,
        "the control must root the address in a formal"
    );
    let run = run(&input, "quality", "init_or_stitch");
    println!(
        "R583 safe-root control: {:?}\n{}\n{}",
        run.inputs,
        rows(&run.dispositions, "init_or_stitch").join("\n"),
        run.held_source
    );
    // The premise: the root is a SAFE subject whose address the callee
    // retains — the raw boundary reads a positive retention, not
    // `raw-boundary-subject-not-safe`.
    let init = rows(&run.dispositions, "init_or_stitch");
    assert!(
        init.iter()
            .any(|row| row.contains("quality::p#1")
                && row.contains("raw-boundary-positive-retention")),
        "{}",
        init.join("\n")
    );
    assert!(
        !run.inputs
            .iter()
            .any(|(_, bridge)| bridge == &Some((BridgeRetentionTier::None, None))),
        "{:?}\n{}",
        run.inputs,
        run.held_source
    );
}
