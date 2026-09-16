//! Offset-derived copy initializers from the frozen heman corpus: unannotated
//! slice locals delivered with an explicit declaration and item 2's constructor.

use super::decision::Decision;

fn compact(source: &str) -> String {
    source.chars().filter(|c| !c.is_whitespace()).collect()
}

fn emitted(input: &str, binding: &str) -> (String, Decision) {
    emitted_reverting(input, binding, false)
}

fn emitted_reverting(input: &str, binding: &str, withdraw: bool) -> (String, Decision) {
    let (source, decision) = ::utils::compilation::run_compiler_on_str(input, move |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("original AST");
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("native decisions");
        for (subject, decision) in &table.entries {
            println!("DECISION {} {decision:?}", subject.label);
        }
        let emission = super::emit_files(tcx, &table, &Default::default(), &ctx.retained_c9_plans)
            .expect("emission plan");
        let mut held = emission.plan.held_classes();
        if withdraw {
            let owner = table
                .entries
                .iter()
                .find(|(s, _)| s.param_name.as_deref() == Some(binding))
                .unwrap()
                .0
                .fn_did;
            held.insert(super::bridge_receipt::SignatureClassId::of(owner));
        }
        let reverts = super::ast_transform::revert_set_from_classes_and_atoms(
            &held,
            &Default::default(),
            &table,
        )
        .expect("held classes");
        let source = super::ast_transform::ast_emitted_files_from(
            tcx,
            &capture,
            &reverts,
            emission.plan.root_file.as_ref(),
            &table,
            Some(&emission.plan.terminal_call_plans),
        )
        .expect("AST emission")
        .0
        .into_values()
        .next()
        .expect("one source");
        println!("EMITTED\n{source}");
        let (subject, decision) = table
            .entries
            .iter()
            .find(|(s, _)| s.param_name.as_deref() == Some(binding))
            .expect("copy subject");
        assert!(
            withdraw
                || !held.contains(&super::bridge_receipt::SignatureClassId::of(subject.fn_did)),
            "the owner must be placed: {:?}",
            emission
                .plan
                .class_finalization
                .classes
                .get(&super::bridge_receipt::SignatureClassId::of(subject.fn_did))
        );
        (source, decision.clone())
    })
    .expect("input compiles");
    assert!(super::verify::type_checks_str(&source), "{source}");
    (source, decision)
}

/// heman `_match`: a raw-field base offset by a computed pixel index, read at
/// three constant offsets.
const MATCH: &str = r#"
    #[repr(C)]
    pub struct heman_image { pub width: i32, pub height: i32, pub nbands: i32, pub data: *mut f32 }
    pub unsafe fn _match(mask: *mut heman_image, mask_color: u32, pixel_index: i32) -> i32 {
        let mut mcolor = ((*mask).data).offset((pixel_index * 3) as isize);
        let r1 = (*mcolor.offset(0) * 255.0) as u8;
        let g1 = (*mcolor.offset(1) * 255.0) as u8;
        let b1 = (*mcolor.offset(2) * 255.0) as u8;
        let r2 = (mask_color >> 16) as u8;
        (r1 == r2 && g1 == b1) as i32
    }
"#;

/// heman `heman_ops_emboss`: a per-row destination pointer written through a
/// counted inner loop.
const EMBOSS: &str = r#"
    #[repr(C)]
    pub struct heman_image { pub width: i32, pub height: i32, pub nbands: i32, pub data: *mut f32 }
    pub unsafe fn emboss(result: *mut heman_image, width: i32, height: i32) {
        let mut y = 0;
        while y < height {
            let mut dst = ((*result).data).offset((y * width) as isize);
            let mut x = 0;
            while x < width {
                *dst.offset(x as isize) = (x + y) as f32;
                x += 1;
            }
            y += 1;
        }
    }
"#;

#[test]
fn wave6k_heman_match_offset_copy_is_a_declared_slice() {
    let (source, decision) = emitted(MATCH, "mcolor");
    assert!(matches!(decision, Decision::Slice { .. }), "{decision:?}");
    let compact_source = compact(&source);
    assert!(compact_source.contains("mcolor:&[f32]="), "{source}");
    assert!(compact_source.contains("from_raw_parts("), "{source}");
    assert!(compact_source.contains("mcolor[0"), "{source}");
}

#[test]
fn wave6k_heman_emboss_row_offset_copy_is_a_declared_slice() {
    let (source, decision) = emitted(EMBOSS, "dst");
    assert!(
        matches!(decision, Decision::Slice { mutable: true, .. }),
        "{decision:?}"
    );
    let compact_source = compact(&source);
    assert!(compact_source.contains("dst:&mut[f32]="), "{source}");
    assert!(compact_source.contains("from_raw_parts_mut("), "{source}");
    assert!(compact_source.contains("dst[(x)asusize]="), "{source}");
}

/// genann `load_data`: the base is itself a delivered slice parameter; the
/// constructor composes the base's own use rewrite.
#[test]
fn wave6k_genann_load_data_offset_copy_of_a_slice_parameter() {
    let (source, decision) = emitted(
        r#"
        pub unsafe fn load_data(input: *mut f64, class: *mut f64, n: i32) {
            let mut i = 0;
            while i < n {
                let mut p = input.offset((i * 4) as isize);
                let mut c = class.offset((i * 3) as isize);
                *p.offset(0) = 1.0;
                *c.offset(0) = 0.0;
                *c.offset(1) = 1.0;
                i += 1;
            }
        }
    "#,
        "c",
    );
    assert!(
        matches!(decision, Decision::Slice { mutable: true, .. }),
        "{decision:?}"
    );
    let compact_source = compact(&source);
    assert!(compact_source.contains("c:&mut[f64]="), "{source}");
    assert!(compact_source.contains("c[0]=0.0"), "{source}");
}

/// Owner withdrawal restores the untyped copy and its raw uses.
#[test]
fn wave6k_withdrawn_owner_restores_the_untyped_offset_copy() {
    let (source, _) = emitted_reverting(EMBOSS, "dst", true);
    assert!(source.contains("result: *mut heman_image"), "{source}");
    assert!(
        source.contains("let mut dst = ((*result).data).offset("),
        "{source}"
    );
    assert!(!source.contains("from_raw_parts_mut"), "{source}");
    assert!(!source.contains("dst: &mut [f32]"), "{source}");
}

/// heman `transform_to_distance` → `edt`: the caller's offset copies `f` / `z`
/// are arguments of a LOCAL callee whose own parameters were delivered before.
/// A candidate on a shared interface must be declined up front (R397-6(b)):
/// attempting it withdraws the callee's prior delivery (R398-1).
const TRANSFORM_EDT: &str = r#"
    pub unsafe fn edt(f: *mut f32, z: *mut f32, n: i32) {
        *z.offset(0) = -1.0;
        *z.offset(1) = 1.0;
        let mut q = 1;
        while q < n {
            *z.offset(q as isize) = *f.offset(q as isize) - *z.offset((q - 1) as isize);
            q += 1;
        }
    }
    pub unsafe fn transform(ff: *mut f32, zz: *mut f32, width: i32, height: i32) {
        let mut x = 0;
        while x < width {
            let mut f = ff.offset((height * x) as isize);
            let mut z = zz.offset(((height + 1) * x) as isize);
            let mut y = 0;
            while y < height {
                *f.offset(y as isize) = (x + y) as f32;
                y += 1;
            }
            edt(f, z, height);
            x += 1;
        }
    }
"#;

#[test]
fn wave6k_copy_passed_to_a_local_callee_is_declined_and_the_callee_keeps_its_delivery() {
    ::utils::compilation::run_compiler_on_str(TRANSFORM_EDT, |tcx| {
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("native decisions");
        for (subject, decision) in &table.entries {
            println!("DECISION {} {decision:?}", subject.label);
        }
        for receipt in &ctx.raw_boundary_artifacts.additive_family_receipts {
            println!(
                "WITHDRAWAL {:?}",
                (
                    &receipt.family,
                    &receipt.owner_path,
                    &receipt.cause,
                    &receipt.subjects
                )
            );
        }
        let decision_of = |label: &str| {
            table
                .entries
                .iter()
                .find(|(s, _)| s.label == label)
                .map(|(_, d)| d.clone())
                .unwrap_or_else(|| panic!("no subject {label}"))
        };
        assert!(
            matches!(decision_of("edt::f"), Decision::Slice { .. }),
            "the callee keeps its delivered slice: {:?}",
            decision_of("edt::f")
        );
        assert!(
            matches!(decision_of("transform::f"), Decision::Degraded(_)),
            "a copy on a shared interface is declined up front: {:?}",
            decision_of("transform::f")
        );
        assert!(
            !ctx.raw_boundary_artifacts
                .additive_family_receipts
                .iter()
                .any(|r| r.owner_path == "edt"),
            "no withdrawal may touch the callee"
        );
    })
    .expect("input compiles");
}

/// wave-6s2's pin (relay wave-6k/011 §2): a local initialised by a call to a
/// LOCAL callee whose return the return family converts is the return
/// receiver's; this rule must not plan a `from_raw_parts` over it.
const BARE_RESLICE_RETURN: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables)]
 pub unsafe fn chunk_data(mut chunk: *mut u8) -> *mut u8 { return chunk.offset(8); }
 pub unsafe fn use_it(mut chunk: *mut u8) -> u8 { let a = *chunk.offset(2); let d = chunk_data(chunk); a.wrapping_add(*d.offset(1)) }
"#;

#[test]
fn wave6k_call_initialised_slice_local_yields_to_the_return_receiver() {
    let (source, _) = emitted(BARE_RESLICE_RETURN, "d");
    let text = compact(&source);
    assert!(
        text.contains("fnchunk_data<'a>(mutchunk:&'a[u8])->&'a[u8]{return&chunk[8..];}"),
        "{source}"
    );
    assert!(text.contains("letd:&[u8]=chunk_data(chunk);"), "{source}");
    assert!(!text.contains("from_raw_parts(chunk_data("), "{source}");
}

/// R395-2 fix-2 (relay wave-6k/012 §1, wave-6a 005 claim 2(ii)): a copy of a
/// THIN reference parameter must not become a slice constructed over it —
/// `from_raw_parts(a, …)` with `a: &i32` widens a one-element claim.
#[test]
fn wave6k_thin_reference_root_is_never_widened() {
    ::utils::compilation::run_compiler_on_str(
        r#"
        pub unsafe fn f(a: *const i32) -> i32 { let p = a; *p.offset(1) }
    "#,
        |tcx| {
            let (table, _) = super::decide_table_with_ctx_config(
                tcx,
                Some((
                    super::A5Mode::PreciseReplay,
                    Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
                )),
            )
            .expect("native decisions");
            for (subject, decision) in &table.entries {
                println!("DECISION {} {decision:?}", subject.label);
            }
            let (subject, decision) = table
                .entries
                .iter()
                .find(|(s, _)| s.param_name.as_deref() == Some("p"))
                .expect("subject");
            assert!(
                matches!(decision, Decision::Degraded(_)),
                "{} must keep its hold, never a slice over a thin root: {decision:?}",
                subject.label
            );
        },
    )
    .expect("input compiles");
}
