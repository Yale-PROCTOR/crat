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
    decision::{raw_boundary::RAW_BOUNDARY_RETENTION_WAIVER_ID, seam::SeamInputRendering},
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
    let run = run(QUALITY10, "quality10", "init_or_stitch");
    assert_eq!(
        run.inputs,
        vec![(
            "zero-syntax".to_owned(),
            Some((
                BridgeRetentionTier::T2,
                Some(RAW_BOUNDARY_RETENTION_WAIVER_ID.to_owned())
            ))
        )],
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
