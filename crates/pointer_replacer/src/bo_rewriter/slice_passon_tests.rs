//! wave-6s2 — bare slice pass-ons classified by the callee's parameter
//! (report 001).
//!
//! The pass-on sub-family has no unbuilt emission mechanism: a delivered
//! slice passed as-is into a local callee takes the callee parameter's own
//! form — the same-form zero-syntax carrier (W-C1), the thin `&T` first
//! element, or the raw bridge under the site's T1 / T2 tier when the
//! parameter settles raw — and a positively-retaining callee holds it. The
//! pins below fix those five outcomes; the two `#[ignore]`d witnesses
//! reproduce the two class-level walls the corpus rows wait on, each named
//! for the lane that owns it.

fn emit_with_receipts(input: &str) -> (String, String) {
    let receipts = std::sync::Arc::new(std::sync::Mutex::new(String::new()));
    let sink = receipts.clone();
    let output = ::utils::compilation::run_compiler_on_str(input, move |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("capture original AST");
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("native corpus-mode decisions");
        for (subject, decision) in &table.entries {
            println!(
                "DECISION {} arms={:?} {decision:?}",
                subject.label,
                table.arm_requirements.get(&(subject.fn_did, subject.hir_id))
            );
        }
        let mut plans = String::new();
        for plan in &table.slice_use_receipts {
            println!("SLICE-USE-RECEIPT {plan:#?}");
            plans.push_str(&format!(
                "PLAN owner={} adapter={} target={} retention={:?} state={:?} reason={:?} evidence={}\n",
                plan.obligation.planned.owner_path,
                plan.adapter,
                plan.target_form,
                plan.retention,
                plan.obligation.intended_terminal_state,
                plan.obligation.intended_terminal_reason,
                plan.boundary_evidence
            ));
        }
        for edit in &table.seams.edits {
            println!(
                "SEAM owner={:?} src={:?} repl={} zero={} shape={} found={:?} expected={:?}",
                edit.owner_class,
                edit.source_node,
                edit.replacement,
                edit.zero_syntax,
                edit.source_shape,
                edit.found,
                edit.expected
            );
        }
        for block in &table.seams.blocked {
            println!("SEAM-BLOCK {block:?}");
        }
        *sink.lock().unwrap() = format!(
            "{plans}{:#?}",
            ctx.raw_boundary_artifacts.additive_family_receipts
        );
        let emission = super::emit_files(tcx, &table, &Default::default(), &ctx.retained_c9_plans)
            .expect("native emission plan");
        for (id, class) in &emission.plan.class_finalization.classes {
            println!(
                "CLASS {} ready={} holds={:?}",
                tcx.def_path_str(id.local_def_id().to_def_id()),
                class.is_ready(),
                class.hold_reasons()
            );
        }
        for collision in &emission.plan.class_finalization.collisions {
            println!("COLLISION {collision:?}");
        }
        let held = emission.plan.held_classes();
        let reverts = super::ast_transform::revert_set_from_classes_and_atoms(
            &held,
            &Default::default(),
            &table,
        )
        .expect("planned held classes");
        super::ast_transform::ast_emitted_files_from(
            tcx,
            &capture,
            &reverts,
            emission.plan.root_file.as_ref(),
            &table,
            Some(&emission.plan.terminal_call_plans),
        )
        .expect("native AST emission")
        .0
        .into_iter()
        .map(|(path, text)| format!("// FILE {path:?}\n{text}"))
        .collect::<Vec<_>>()
        .join("\n")
    })
    .expect("input type-checks");
    let receipts = receipts.lock().unwrap().clone();
    println!("EMITTED {output}");
    println!("RECEIPTS {receipts}");
    (output, receipts)
}

fn joined(source: &str) -> String {
    source.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// **Witness A (for wave-5d2).** The callee's READ/WRITE parameter pair is
/// held `pair-raw-view` by a caller that passes two views of ONE root
/// (`overlap(x, x.offset(n), n)`). A second caller whose own arguments are
/// two distinct delivered slices already plans its pass-ons as the raw seams
/// (`p` same-form, `q.as_mut_ptr()` T2) — and both classes are then held by
/// a cross-class interval collision: the A5 pair arm renders a
/// `a5-site-proof-t2-fallback` edit over the WHOLE call, on top of the
/// caller's own raw-view edit. Measured at `8e84dc6d`; the collision is the
/// pair-charged partner coupling wave-5d2 owns.
const CALLEE_PAIR_HELD: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables)]
 unsafe fn pair(mut a: *const u8, mut b: *mut u8, n: usize) {
    let mut i: usize = 0;
    while i < n { *b.offset(i as isize) = *a.offset(i as isize); i = i.wrapping_add(1); }
 }
 pub unsafe fn overlap(mut x: *mut u8, n: usize) { pair(x, x.offset(n as isize), n); }
 pub unsafe fn caller(mut p: *const u8, mut q: *mut u8, n: usize) -> u8 {
    let a = *p.offset(1);
    *q.offset(1) = a;
    pair(p, q, n);
    a
 }
"#;

#[test]
#[ignore = "RED by design (wave-5d2): the A5 pair-arm `a5-site-proof-t2-fallback` edit over the whole call collides with the caller's own `q.as_mut_ptr()` raw-view edit (cross-class-interval-collision) — the pair-charged partner coupling of R403-4"]
fn wave6s2_pass_on_beside_an_a5_pair_fallback_edit_bridges() {
    let (source, receipts) = emit_with_receipts(CALLEE_PAIR_HELD);
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(source.contains("mut p: &[u8]"), "{source}");
    assert!(source.contains("mut q: &mut [u8]"), "{source}");
    assert!(
        source.contains("mut a: *const u8, mut b: *mut u8"),
        "the callee keeps its raw parameters: {source}"
    );
    assert!(
        joined(&source).contains("pair(p.as_ptr(), q.as_mut_ptr(), n)"),
        "the pass-ons are the sites' raw bridges: {source}"
    );
    assert!(
        receipts.contains("adapter=slice-to-raw-const")
            && receipts.contains("adapter=slice-mut-to-raw-mut"),
        "the receipts name the boundary templates: {receipts}"
    );
    assert!(
        receipts.contains("callee-parameter-degraded:pair-raw-view"),
        "the receipt names why the callee settles raw: {receipts}"
    );
}

/// **Witness B (brotli `BrotliBuildAndStoreHuffmanTreeFast::bits#6` /
/// `depth#5`, batch-6 rows, reduced).** In the reduction the callee's
/// parameters both deliver and the caller's `depth` pass-on is a MUTABLE
/// slice into a SHARED slice parameter — W-C1's `Hold::Form`
/// (`slice-use-existing-c-interface-carrier-unmapped:candidates=0`), which
/// withdraws the caller with `bits` (`new-family-dependency`). That is the
/// coercion arm wave-6s built in `b56f95a1` (report 006); at the corpus the
/// callee's `bits` additionally holds `pair-raw-view` (wave-6p / wave-5d2).
const HUFFMAN_TREE_FAST: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
 unsafe fn BrotliReverseBits(num_bits: usize, bits: u16) -> u16 {
    let mut retval: usize = 0; let mut i: usize = 0;
    while i < num_bits { retval = (retval << 1) | (((bits as usize) >> i) & 1); i = i.wrapping_add(1); }
    retval as u16
 }
 unsafe fn BrotliConvertBitDepthsToSymbols(mut depth: *const u8, mut len: usize, mut bits: *mut u16) {
    let mut bl_count: [u16; 16] = [0; 16];
    let mut next_code: [u16; 16] = [0; 16];
    let mut i: usize = 0;
    let mut code: i32 = 0;
    i = 0;
    while i < len { bl_count[*depth.offset(i as isize) as usize] = bl_count[*depth.offset(i as isize) as usize].wrapping_add(1); i = i.wrapping_add(1); }
    bl_count[0] = 0;
    next_code[0] = 0;
    i = 1;
    while i < 16 { code = (code + bl_count[i.wrapping_sub(1)] as i32) << 1; next_code[i] = code as u16; i = i.wrapping_add(1); }
    i = 0;
    while i < len {
        if *depth.offset(i as isize) != 0 {
            let fresh2 = next_code[*depth.offset(i as isize) as usize];
            next_code[*depth.offset(i as isize) as usize] = next_code[*depth.offset(i as isize) as usize].wrapping_add(1);
            *bits.offset(i as isize) = BrotliReverseBits(*depth.offset(i as isize) as usize, fresh2);
        }
        i = i.wrapping_add(1);
    }
 }
 pub unsafe fn BrotliBuildAndStoreHuffmanTreeFast(mut histogram: *const u32, mut histogram_total: usize, mut depth: *mut u8, mut bits: *mut u16) {
    let mut count: usize = 0;
    let mut symbols: [usize; 4] = [0; 4];
    let mut length: usize = 0;
    while histogram_total != 0 {
        if *histogram.offset(length as isize) != 0 {
            if count < 4 { symbols[count] = length; }
            count = count.wrapping_add(1);
            histogram_total = histogram_total.wrapping_sub(*histogram.offset(length as isize) as usize);
        }
        length = length.wrapping_add(1);
    }
    if count <= 1 {
        *depth.offset(symbols[0] as isize) = 0;
        *bits.offset(symbols[0] as isize) = 0;
        return;
    }
    let mut k: usize = 0;
    while k < length { *depth.offset(k as isize) = (k & 7) as u8; k = k.wrapping_add(1); }
    BrotliConvertBitDepthsToSymbols(depth, length, bits);
 }
"#;

#[test]
#[ignore = "RED by design: the mutable `depth: &mut [u8]` into the shared `depth: &[u8]` parameter is W-C1's `Hold::Form` until wave-6s's coercion arm (`b56f95a1`) lands, and under it the caller is still withdrawn by the R220 restoration walk (`new-family-dependency` / `restore-prior-family-disposition`) that wave-5d's primitive replaces; un-ignore when both are on the head"]
fn wave6s2_huffman_tree_fast_mutable_into_shared_pass_on_is_zero_syntax() {
    let (source, receipts) = emit_with_receipts(HUFFMAN_TREE_FAST);
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(source.contains("mut bits: &mut [u16]"), "{source}");
    assert!(source.contains("mut depth: &mut [u8]"), "{source}");
    assert!(
        joined(&source).contains("bits[symbols[0]] = 0;"),
        "the caller's own element write: {source}"
    );
    assert!(
        joined(&source).contains("BrotliConvertBitDepthsToSymbols(depth, length, bits)"),
        "both pass-ons are zero-syntax same-form positions: {source}"
    );
    assert!(
        receipts.contains("owned-existing-c-same-slice"),
        "{receipts}"
    );
}

/// **Pins 1–3.** A callee parameter the analysis itself keeps raw (a
/// pointer-to-integer observation: `kind-raw`), a thin callee, and a
/// positively-retaining callee. The first two deliver the caller; the third
/// must stay held — the site's own disposition blocks it and nothing raises a
/// tier.
const PASS_ON_TO_RAW_MODEL: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables)]
 unsafe fn back(mut p: *const u8, n: usize) -> u8 { let a = p as usize; return *p.offset((a % 2 + n) as isize); }
 pub unsafe fn caller(mut buf: *const u8, n: usize) -> u8 {
    let a = *buf.offset(1);
    let b = back(buf, n);
    a.wrapping_add(b)
 }
"#;

#[test]
fn wave6s2_pin_pass_on_into_a_model_raw_callee_bridges() {
    let (source, receipts) = emit_with_receipts(PASS_ON_TO_RAW_MODEL);
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(source.contains("mut buf: &[u8]"), "{source}");
    assert!(
        source.contains("mut p: *const u8"),
        "the callee keeps its raw parameter: {source}"
    );
    assert!(
        joined(&source).contains("back(buf.as_ptr(), n)"),
        "{source}"
    );
    assert!(
        receipts.contains("template=SliceToRawConst"),
        "the site's own boundary template: {receipts}"
    );
}

const PASS_ON_TO_THIN: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables)]
 unsafe fn one(mut p: *const u8) -> u8 { return *p; }
 pub unsafe fn caller(mut buf: *const u8, n: usize) -> u8 {
    let a = *buf.offset(n as isize);
    let b = one(buf);
    a.wrapping_add(b)
 }
"#;

#[test]
fn wave6s2_pin_pass_on_into_a_thin_callee_takes_the_first_element() {
    let (source, _) = emit_with_receipts(PASS_ON_TO_THIN);
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(source.contains("mut p: &u8"), "{source}");
    assert!(
        joined(&source).contains("one(buf.first().unwrap())"),
        "{source}"
    );
}

const PASS_ON_TO_RETAINING: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables, non_upper_case_globals)]
 static mut KEEP: *const u8 = 0 as *const u8;
 unsafe fn sink(mut p: *const u8, n: usize) -> u8 { KEEP = p; return *p.offset(n as isize); }
 pub unsafe fn caller(mut buf: *const u8, n: usize) -> u8 {
    let a = *buf.offset(1);
    let b = sink(buf, n);
    a.wrapping_add(b)
 }
"#;

#[test]
fn wave6s2_pin_pass_on_into_a_positively_retaining_callee_stays_held() {
    let (source, receipts) = emit_with_receipts(PASS_ON_TO_RETAINING);
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(source.contains("mut buf: *const u8"), "{source}");
    assert!(!source.contains("as_ptr()"), "{source}");
    assert!(
        receipts.contains("positive-retention") || receipts.contains("PositiveRetention"),
        "{receipts}"
    );
}

/// **Pin 4.** The callee's parameter is withdrawn in the SAME family
/// transaction (it hands the pointer to a foreign `*mut` position with no
/// negative-write evidence); the family loop re-derives the caller with the
/// callee raw and the pass-on takes the raw bridge under the site's tier.
const CALLEE_WRITER: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables)]
 unsafe extern "C" { fn consume(q: *mut u8, n: usize); }
 unsafe fn sink(mut p: *const u8, n: usize) -> u8 { consume(p as *mut u8, n); return *p.offset(1); }
 pub unsafe fn caller(mut buf: *const u8, n: usize) -> u8 {
    let a = *buf.offset(1);
    let b = sink(buf, n);
    a.wrapping_add(b)
 }
"#;

#[test]
fn wave6s2_pin_pass_on_into_a_callee_withdrawn_in_the_same_transaction_bridges() {
    let (source, receipts) = emit_with_receipts(CALLEE_WRITER);
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(source.contains("mut buf: &[u8]"), "{source}");
    assert!(
        source.contains("mut p: *const u8"),
        "the callee keeps its raw parameter: {source}"
    );
    assert!(
        joined(&source).contains("sink(buf.as_ptr(), n)"),
        "{source}"
    );
    assert!(
        receipts.contains("negative-write-absent"),
        "the callee's own withdrawal is receipted: {receipts}"
    );
}

/// **Pin 5.** A callee pinned by a function-pointer reference keeps its raw
/// signature behind a shim; the caller's pass-on is zero syntax into the shim.
const CALLEE_PINNED: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables)]
 unsafe fn sink(mut p: *const u8, n: usize) -> u8 { return *p.offset(n as isize); }
 pub unsafe fn table() -> unsafe fn(*const u8, usize) -> u8 { sink as unsafe fn(*const u8, usize) -> u8 }
 pub unsafe fn caller(mut buf: *const u8, n: usize) -> u8 {
    let a = *buf.offset(1);
    let b = sink(buf, n);
    a.wrapping_add(b)
 }
"#;

#[test]
fn wave6s2_pin_pass_on_into_a_fn_pointer_pinned_callee_goes_through_its_shim() {
    let (source, _) = emit_with_receipts(CALLEE_PINNED);
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(source.contains("mut buf: &[u8]"), "{source}");
    assert!(
        source.contains("unsafe fn __crat_safe_sink(mut p: &[u8], n: usize)"),
        "{source}"
    );
    assert!(joined(&source).contains("sink(buf, n)"), "{source}");
}

// ---------------------------------------------------------------------------
// W6S2-2 — the C2Rust constant-reslice return (`decision/slice_passon.rs`).
// ---------------------------------------------------------------------------

/// **Witness (lodepng `lodepng_chunk_data` / `lodepng_chunk_data_const`,
/// batch-6 rows, sole).** C2Rust spells the reslice return as
/// `&mut *chunk.offset(8 as i32 as isize) as *mut u8`; the return family
/// already delivers `return chunk.offset(8)` as the tied `&chunk[8..]`, and
/// the spine is the same value. RED at `8e84dc6d` (`slice-cursor-use` on both
/// parameters), GREEN with the recogniser.
const LODEPNG_CHUNK_DATA: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables)]
 pub unsafe fn lodepng_chunk_data(mut chunk: *mut u8) -> *mut u8 { return &mut *chunk.offset(8 as i32 as isize) as *mut u8; }
 pub unsafe fn lodepng_chunk_data_const(mut chunk: *const u8) -> *const u8 { return &*chunk.offset(8 as i32 as isize) as *const u8; }
 pub unsafe fn use_it(mut chunk: *mut u8) -> u8 { let a = *chunk.offset(2); let d = lodepng_chunk_data(chunk); let c = lodepng_chunk_data_const(chunk); a.wrapping_add(*d.offset(1)).wrapping_add(*c.offset(2)) }
"#;

#[test]
fn wave6s2_c2rust_constant_reslice_return_delivers_the_tied_suffix() {
    let (source, _) = emit_with_receipts(LODEPNG_CHUNK_DATA);
    assert!(super::verify::type_checks_str(&source), "{source}");
    let text = joined(&source);
    assert!(
        text.contains(
            "fn lodepng_chunk_data<'a>(mut chunk: &'a [u8]) -> &'a [u8] { return &chunk[8..]; }"
        ),
        "{source}"
    );
    assert!(
        text.contains("fn lodepng_chunk_data_const<'a>(mut chunk: &'a [u8]) -> &'a [u8] { return &chunk[8..]; }"),
        "{source}"
    );
    assert!(
        text.contains("let d: &[u8] = lodepng_chunk_data(chunk);"),
        "{source}"
    );
    assert!(
        text.contains("a.wrapping_add(d[1]).wrapping_add(c[2])"),
        "{source}"
    );
}

/// **Witness (the bare spelling is unchanged).** `return chunk.offset(8)`
/// delivered before this rule and delivers identically with it.
const BARE_RESLICE_RETURN: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables)]
 pub unsafe fn chunk_data(mut chunk: *mut u8) -> *mut u8 { return chunk.offset(8); }
 pub unsafe fn use_it(mut chunk: *mut u8) -> u8 { let a = *chunk.offset(2); let d = chunk_data(chunk); a.wrapping_add(*d.offset(1)) }
"#;

#[test]
fn wave6s2_pin_bare_constant_reslice_return_still_delivers() {
    let (source, _) = emit_with_receipts(BARE_RESLICE_RETURN);
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(
        joined(&source)
            .contains("fn chunk_data<'a>(mut chunk: &'a [u8]) -> &'a [u8] { return &chunk[8..]; }"),
        "{source}"
    );
}

/// **Controls.** A cast that CHANGES the pointee (`… as *const u16` on a
/// `*const u8` receiver) is a reinterpretation, not a reslice, and stays
/// held; a NEGATIVE literal is the bidirectional family's (slicecursor) and
/// stays held. Both functions keep their raw signatures.
const RESLICE_RETURN_CONTROLS: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables)]
 pub unsafe fn reinterpret(mut chunk: *const u8) -> *const u16 { return &*chunk.offset(8 as i32 as isize) as *const u8 as *const u16; }
 pub unsafe fn backward(mut chunk: *const u8) -> *const u8 { return &*chunk.offset(-8 as i32 as isize) as *const u8; }
 pub unsafe fn use_it(mut chunk: *mut u8) -> u16 { let a = *chunk.offset(2); let d = reinterpret(chunk); let c = backward(chunk.offset(16)); (a as u16).wrapping_add(*d).wrapping_add(*c as u16) }
"#;

#[test]
fn wave6s2_reslice_return_controls_stay_held() {
    let (source, _) = emit_with_receipts(RESLICE_RETURN_CONTROLS);
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(
        source.contains("fn reinterpret(mut chunk: *const u8) -> *const u16"),
        "a pointee-changing cast is not a reslice: {source}"
    );
    assert!(
        source.contains("fn backward(mut chunk: *const u8) -> *const u8"),
        "a negative literal is the bidirectional family's: {source}"
    );
}
