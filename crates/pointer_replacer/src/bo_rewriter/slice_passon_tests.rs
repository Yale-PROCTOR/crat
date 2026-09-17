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
//!
//! Model gate (relay 002 §4): a caller-side form never outruns the model's
//! kind of the callee it forwards to — every pass-on here takes the callee
//! parameter's OWN settled form (same-form zero syntax, the thin element, or
//! the raw bridge exactly because the callee's parameter stays raw); no pin
//! and no rule of this lane converts a callee on the caller's behalf.

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
        // A compact, assertable decision line per subject: the emitted form, or
        // `degraded:<reason>`. A witness of a wall that MOVES (one family's
        // blocker replaced by another's) needs the reason, not only the text.
        for (subject, decision) in &table.entries {
            let state = match decision {
                super::decision::Decision::Degraded(record) => {
                    format!("degraded:{}", record.reason.key())
                }
                other => super::decision::seam::form_of(other).key().to_owned(),
            };
            plans.push_str(&format!("DECISION-KV {} {state}\n", subject.label));
        }
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
fn wave6s2_pass_on_beside_an_a5_pair_fallback_edit_bridges() {
    let (source, receipts) = emit_with_receipts(CALLEE_PAIR_HELD);
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(source.contains("mut p: &[u8]"), "{source}");
    assert!(source.contains("mut q: &mut [u8]"), "{source}");
    // R217-2(a): the expectation MOVED with wave-5d's exclusion re-derivation
    // and the A5 pair arm (batch-9 candidate frame). The collision that held
    // both classes is gone: the callee's READ parameter converts with the
    // caller's `p` (zero syntax), and only the WRITE parameter stays raw,
    // taking the caller's `q` through the A5 arm's temporary.
    assert!(
        source.contains("mut a: &[u8], mut b: *mut u8"),
        "the callee's read parameter converts, the write parameter stays raw: {source}"
    );
    let text = joined(&source);
    assert!(
        text.contains("let __crat_a5_raw_") && text.contains(": *mut u8 = q.as_mut_ptr();"),
        "the write pass-on is the A5 arm's raw view of the caller's slice: {source}"
    );
    assert!(
        text.contains("pair(p, __crat_a5_raw_"),
        "the read pass-on is zero syntax into the converted parameter: {source}"
    );
    assert!(
        receipts.contains("adapter=slice-mut-to-raw-mut"),
        "the write bridge's template: {receipts}"
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
#[ignore = "RED by design, CALLER side only (batch-9 candidate frame df982371): the callee's `depth: &[u8]` / `bits: &mut [u16]` now deliver, and the caller `BrotliBuildAndStoreHuffmanTreeFast` is withdrawn by the restoration walk (`exclusion-rederivation:anchor=4:restore-family-interface-path:[4, 9]`, then `restore-prior-family-disposition`) — wave-5d's R220 layer; un-ignore when that walk stops withdrawing the caller"]
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

// ---------------------------------------------------------------------------
// Pins of wave-6f's W6F-2 on the Slice family (R407-8): a delivered slice at
// an argument of a call THROUGH A FUNCTION POINTER is an inventoried
// `<indirect>` raw-boundary site — the raw view under the T2 waiver, the
// callee keeping the pointer type its signature names. Model gate: the
// caller's form never outruns the callee it forwards to — the bridge exists
// exactly because the indirect callee's parameter stays raw. RED until W6F-2
// with its return-type refinement is on the head (the lane's own W6S2-3 was
// withdrawn in its favour, report 004 / relay 002).
// ---------------------------------------------------------------------------

/// **Witness (tulipindicators `fuzzer::check_output::options#4`, batch-6 row,
/// sole).** `(*info).start.expect(..)(options)` is a call through a function
/// pointer, which the boundary planner does not inventory; the bare argument
/// was refused and the whole subject held. It is the raw view under the T2
/// waiver: `(..)(options.as_ptr())`, while the counted read `options[k]`
/// delivers.
const CHECK_OUTPUT: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables, non_camel_case_types)]
 #[repr(C)] pub struct ti_indicator_info { pub start: Option<unsafe extern "C" fn(*const f64) -> i32>, pub options: i32 }
 pub unsafe extern "C" fn check_output(mut info: *const ti_indicator_info, mut size: i32, mut options: *const f64) -> i32 {
    let mut s: i32 = 0;
    s = (*info).start.expect("non-null function pointer")(options);
    let mut k: i32 = 0;
    let mut acc: f64 = 0.0;
    while k < (*info).options { acc += *options.offset(k as isize); k += 1; }
    s + acc as i32
 }
"#;

#[test]
fn wave6s2_fn_pointer_call_argument_takes_the_t2_raw_view() {
    let (source, receipts) = emit_with_receipts(CHECK_OUTPUT);
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(source.contains("mut options: &[f64]"), "{source}");
    let text = joined(&source);
    assert!(
        text.contains("(*info).start.expect(\"non-null function pointer\")(options.as_ptr());"),
        "{source}"
    );
    assert!(text.contains("acc += options[(k) as usize];"), "{source}");
    assert!(receipts.contains("retention=T2"), "{receipts}");
}

/// **Controls.** A SHARED slice at a `*mut` function-pointer parameter has
/// no negative-write evidence and holds; a function pointer that returns a
/// raw pointer may hand a child of the argument back and holds. Both keep the
/// raw parameter.
const FN_POINTER_CONTROLS: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables)]
 pub unsafe fn writer(mut f: unsafe extern "C" fn(*mut u8) -> i32, mut buf: *const u8, n: usize) -> i32 {
    let a = *buf.offset(n as isize);
    f(buf as *mut u8) + a as i32
 }
 pub unsafe fn child(mut g: unsafe extern "C" fn(*const u8) -> *mut u8, mut buf: *const u8, n: usize) -> u8 {
    let a = *buf.offset(n as isize);
    let r = g(buf);
    a.wrapping_add(*r)
 }
"#;

#[test]
fn wave6s2_fn_pointer_call_controls_stay_held() {
    let (source, receipts) = emit_with_receipts(FN_POINTER_CONTROLS);
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(!source.contains("as_ptr()"), "{source}");
    assert!(
        source.contains("mut buf: *const u8, n: usize) -> i32"),
        "{source}"
    );
    assert!(
        source.contains("mut buf: *const u8, n: usize) -> u8"),
        "{source}"
    );
    assert!(
        receipts.contains("returned-child") || receipts.contains("negative-write-absent"),
        "{receipts}"
    );
}

// ---------------------------------------------------------------------------
// W6S2-4 — a COMPUTED VIEW of a delivered slice at an argument of a call
// through a function pointer: the composition of wave-6s's computed
// sub-view spine with wave-6f's `<indirect>` raw-boundary site (relay 005 §1).
// ---------------------------------------------------------------------------

/// **Witness (brotli `SortHuffmanTreeItems::items#1`, the batch-6 market's
/// last two `slice-cursor-use` rows — the same function in
/// `enc::brotli_bit_stream` and in `enc::entropy_encode`, both sole).** The
/// subject is walked by `*items.offset(i)` reads and writes (the deref-index
/// arm) and handed to the comparator as `&mut *items.offset(j as isize)` — a
/// computed view at an argument of a call through a function pointer. Neither
/// end existed at batch 6: the spine refused the position (unregistered
/// callee) and the position had no boundary site.
const SORT_HUFFMAN_TREE_ITEMS: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables, non_snake_case, non_upper_case_globals)]
 #[repr(C)] #[derive(Copy, Clone)] pub struct HuffmanTree { pub total_count_: u32, pub index_left_: i16, pub index_right_or_value_: i16 }
 pub type HuffmanTreeComparator = Option<unsafe extern "C" fn(*const HuffmanTree, *const HuffmanTree) -> i32>;
 unsafe extern "C" fn SortHuffmanTreeItemsCmp(v0: *const HuffmanTree, v1: *const HuffmanTree) -> i32 {
    ((*v0).total_count_ < (*v1).total_count_) as i32
 }
 pub unsafe fn BrotliCreateHuffmanTree(mut tree: *mut HuffmanTree, n: usize) {
    SortHuffmanTreeItems(tree, n, Some(SortHuffmanTreeItemsCmp));
 }
 unsafe fn SortHuffmanTreeItems(mut items: *mut HuffmanTree, n: usize, mut comparator: HuffmanTreeComparator) {
    let mut i: usize = 1;
    while i < n {
        let mut tmp = *items.offset(i as isize);
        let mut k = i;
        let mut j = i.wrapping_sub(1);
        while comparator.expect("non-null function pointer")(&mut tmp, &mut *items.offset(j as isize)) != 0 {
            *items.offset(k as isize) = *items.offset(j as isize);
            k = j;
            let fresh0 = j;
            j = j.wrapping_sub(1);
            if fresh0 == 0 { break; }
        }
        *items.offset(k as isize) = tmp;
        i = i.wrapping_add(1);
    }
 }
"#;

#[test]
#[ignore = "RED by design, ANALYSIS frame (batch-9 candidate df982371): the reduction's model settles `items` Raw (`kind-raw`) however it is spelled — measured with and without a concrete comparator target, with a direct call in place of the indirect one, without the struct copy, and with a forward-only walk (report 007, MAX-3). The corpus rows are `slice-cursor-use`, i.e. model-Ref, so the emission question this witness asks is only reachable on an analysis-faithful reduction or on the corpus row itself"]
fn wave6s2_computed_view_at_a_fn_pointer_argument_delivers_the_slice() {
    let (source, receipts) = emit_with_receipts(SORT_HUFFMAN_TREE_ITEMS);
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(
        source.contains("mut items: &mut [HuffmanTree]"),
        "the subject delivers: {source}"
    );
    let text = joined(&source);
    assert!(text.contains("items[i]"), "the deref-index arm: {source}");
    assert!(
        text.contains("(&mut (items)[j..]).as_mut_ptr()")
            || text.contains("(&mut items[j..]).as_mut_ptr()")
            || text.contains("&mut (items)[j]")
            || text.contains("&mut items[j]"),
        "the computed view at the indirect argument: {source}"
    );
    assert!(receipts.contains("retention=T2"), "{receipts}");
}

// ---------------------------------------------------------------------------
// W6S2-5 — the destination of a computed view copied by ASSIGNMENT
// (`decision/slice_passon.rs`).
// ---------------------------------------------------------------------------

/// **Witness (brotli `BrotliFindAllStaticDictionaryMatches::s#61`, `s_0`,
/// `s_1`, `s_2` — four sole rows ENABLED at the batch-9 frame, and lodepng
/// `addChunk_IHDR::data#9`).** The source `data` delivers and its edit is the
/// checked suffix; the DESTINATION saw the assignment as an unsupported use
/// and stayed raw.
const ASSIGN_COMPUTED_VIEW_DESTINATION: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
 pub unsafe fn FindMatches(mut data: *const u8, max_length: usize, mut out: *mut u32) -> i32 {
    let mut s = 0 as *const u8;
    let mut l: usize = 0;
    let mut found = 0;
    while l < max_length {
        if *data.offset(l as isize) as i32 == ' ' as i32 { l = l.wrapping_add(1); continue; }
        s = &*data.offset(l as isize) as *const u8;
        if *s.offset(0 as isize) as i32 == 'a' as i32 { *out.offset(found as isize) = l as u32; found += 1; }
        if *s.offset(1 as isize) as i32 == 'b' as i32 { found += 1; }
        l = l.wrapping_add(1);
    }
    found
 }
"#;

#[test]
fn wave6s2_assignment_destination_of_a_computed_view_is_in_scope() {
    let (source, receipts) = emit_with_receipts(ASSIGN_COMPUTED_VIEW_DESTINATION);
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(
        source.contains("mut data: &[u8]"),
        "the source delivers: {source}"
    );
    // The wall MOVES: the assignment target is in scope, so the destination is
    // no longer held by the slice-use wall; what remains is its
    // null-initialised declaration — wave-6o's Option family — and until that
    // lands the source keeps rendering its raw view for the raw destination.
    assert!(
        receipts.contains("DECISION-KV FindMatches::s degraded:null-init"),
        "the destination's blocker is now the null-init declaration: {receipts}"
    );
    assert!(
        !receipts.contains("DECISION-KV FindMatches::s degraded:slice-use-unsupported"),
        "{receipts}"
    );
    assert!(
        joined(&source).contains("s = (&(data)[l..]).as_ptr()"),
        "the source's view is still rendered for the raw destination: {source}"
    );
}

/// **Control.** A BACKWARD assignment (`p = q.offset(-k)`) is the
/// bidirectional family's (R394-2) and stays out of scope; a self-advance
/// stays the classifier's own arm.
const ASSIGN_BACKWARD_DESTINATION: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
 pub unsafe fn Walk(mut data: *const u8, n: usize) -> u8 {
    let mut s = 0 as *const u8;
    let mut acc = 0u8;
    let mut l: usize = 1;
    while l < n {
        acc = acc.wrapping_add(*data.offset(l as isize));
        s = &*data.offset((l as isize) + (-1 as isize)) as *const u8;
        acc = acc.wrapping_add(*s.offset(0 as isize));
        l = l.wrapping_add(1);
    }
    acc
 }
"#;

#[test]
fn wave6s2_backward_assignment_destination_stays_out_of_scope() {
    let (source, receipts) = emit_with_receipts(ASSIGN_BACKWARD_DESTINATION);
    assert!(super::verify::type_checks_str(&source), "{source}");
    // R217-2(a), measured on batch-10 dry8: what this control fixes is that
    // W6S2-5 does NOT admit a backward assignment. On this lane's own frame
    // that shows as the use wall standing; on a composed frame the row is
    // taken by the BIDIRECTIONAL family instead (R394-2) — the source becomes
    // a cursor and the destination its element view — which is the routing
    // this control asserts, not a widening of my rule. Both outcomes are
    // spelled; no third one passes.
    if receipts.contains("DECISION-KV Walk::data cursor-shared") {
        assert!(
            receipts.contains("DECISION-KV Walk::s opt-slice-shared")
                || receipts.contains("DECISION-KV Walk::s slice-shared")
                || receipts.contains("DECISION-KV Walk::s degraded:"),
            "the bidirectional family owns the row: {receipts}"
        );
        assert!(
            !joined(&source).contains("s = &(data)[l..]"),
            "never my forward suffix for a backward delta: {source}"
        );
    } else {
        assert!(source.contains("mut s = 0 as *const u8"), "{source}");
        assert!(
            receipts.contains("DECISION-KV Walk::s degraded:slice-use-unsupported"),
            "a backward assignment keeps the use wall: {receipts}"
        );
    }
}

/// **The delivery witness (report 010).** The same destination shape with a
/// TYPED (non-null) initialiser: both ends deliver and the assignment is the
/// checked suffix — so W6S2-5 is a delivery rule, and the corpus rows whose
/// declaration is null-initialised (brotli `static_dict::s*`, lodepng
/// `addChunk_IHDR::data`) wait on exactly one thing: wave-6o's Option
/// declaration for that local. Measured without composing the two lines.
const ASSIGN_DESTINATION_NON_NULL_INIT: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
 pub unsafe fn FindMatches(mut data: *const u8, max_length: usize, mut out: *mut u32) -> i32 {
    let mut s: *const u8 = data;
    let mut l: usize = 0;
    let mut found = 0;
    while l < max_length {
        if *data.offset(l as isize) as i32 == ' ' as i32 { l = l.wrapping_add(1); continue; }
        s = &*data.offset(l as isize) as *const u8;
        if *s.offset(0 as isize) as i32 == 'a' as i32 { *out.offset(found as isize) = l as u32; found += 1; }
        if *s.offset(1 as isize) as i32 == 'b' as i32 { found += 1; }
        l = l.wrapping_add(1);
    }
    found
 }
"#;

#[test]
fn wave6s2_assignment_destination_delivers_once_its_declaration_is_typed() {
    let (source, receipts) = emit_with_receipts(ASSIGN_DESTINATION_NON_NULL_INIT);
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(
        receipts.contains("DECISION-KV FindMatches::s slice-shared"),
        "the destination carries the view: {receipts}"
    );
    let text = joined(&source);
    assert!(text.contains("let mut s: &[u8] = data;"), "{source}");
    assert!(
        text.contains("s = &(data)[l..];"),
        "the assignment is the checked suffix: {source}"
    );
    assert!(text.contains("s[0]") && text.contains("s[1]"), "{source}");
    assert!(
        !text.contains("as_ptr()"),
        "neither end needs a raw view: {source}"
    );
}

// ---------------------------------------------------------------------------
// W6S2-5b (R451-4) — the same assignment with an ARRAY-LOCAL source.
// ---------------------------------------------------------------------------

/// **Witness (heman `kazmath::quaternion::kmQuaternionRotationMatrix::pMatrix#8`,
/// an ENABLED `slice-use-unsupported` row of the batch-10 frame, `sole = 0`).**
/// `pMatrix = &mut *m4x4.as_mut_ptr().offset(0) as *mut c_float` on a
/// `[c_float; 16]` local, then `*pMatrix.offset(k)` reads. Were the arm built,
/// the extent would be the array type's own length — no evidence invented
/// (`sealed-contract:array-length`, the key `decision/construction.rs` already
/// mints for `arr.as_ptr()`), and the destination is null-initialised so the
/// Option family, not this lane, would render the right-hand side. The
/// reduction does not reach that stage; see the STOP on the test below.
const ARRAY_LOCAL_SOURCE: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
 #[derive(Copy, Clone)]
 #[repr(C)]
 pub struct kmMat3 { pub mat: [f32; 9], }
 pub unsafe fn kmQuaternionRotationMatrix(mut pIn: *const kmMat3) -> f32 {
    let mut pMatrix = 0 as *mut f32;
    let mut m4x4: [f32; 16] = [0.; 16];
    if pIn.is_null() { return 0.; }
    m4x4[0 as usize] = (*pIn).mat[0 as usize];
    m4x4[5 as usize] = (*pIn).mat[4 as usize];
    m4x4[10 as usize] = (*pIn).mat[8 as usize];
    m4x4[15 as usize] = 1 as i32 as f32;
    pMatrix = &mut *m4x4.as_mut_ptr().offset(0 as i32 as isize) as *mut f32;
    let mut diagonal = *pMatrix.offset(0 as i32 as isize)
        + *pMatrix.offset(5 as i32 as isize)
        + *pMatrix.offset(10 as i32 as isize);
    diagonal
 }
"#;

/// **STOP (MAX-3, report 015).** The rule this witness asks for is NOT built:
/// the reduction cannot exhibit the corpus row's wall. In the corpus
/// (`batch10/heman.*subjects.tsv`) `pMatrix#8` is model kind **`ref`**, family
/// `slice`, degraded `slice-use-unsupported` — a USE-stage wall. In three
/// spellings of the reduction (raw `*const f32` input; no pointer return;
/// struct-pointer input reproducing `pIn`'s `optional`/`ref` exactly) the model
/// settles `pMatrix` at **`Raw`** (`degraded:kind-raw`) whenever its value is an
/// array-local decay, with or without a null-initialised declaration — so the
/// SliceUse stage never runs on it and no use rule is observable. Admitting the
/// array-local arm without a witness would be an unwitnessed rule; the arm is
/// withdrawn and preserved at
/// `/home/p51lee/dev/.crat-scratch/wave-6s2/w6s2-5b-arm.patch`.
#[test]
#[ignore = "W6S2-5b STOP: the reduction settles the array-local destination at \
            kind-raw in three spellings where the corpus row is model-ref \
            (analysis-frame divergence, report 015)"]
fn wave6s2_array_local_source_moves_the_wall_to_the_option_family() {
    let (source, receipts) = emit_with_receipts(ARRAY_LOCAL_SOURCE);
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(
        receipts.contains("DECISION-KV kmQuaternionRotationMatrix::pMatrix degraded:null-init"),
        "the array-local assignment is in scope; what remains is the null-init \
         declaration (the Option family's): {receipts}"
    );
    assert!(
        !receipts.contains(
            "DECISION-KV kmQuaternionRotationMatrix::pMatrix degraded:slice-use-unsupported"
        ),
        "{receipts}"
    );
}

/// **Control 1.** The same array-local source with a TYPED destination stays
/// out of scope: no family owns the right-hand side for an array source, so
/// admitting it could only produce an ill-typed assignment.
const ARRAY_LOCAL_SOURCE_TYPED_DESTINATION: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
 pub unsafe fn Typed(mut pIn: *const f32) -> f32 {
    let mut m4x4: [f32; 16] = [0.; 16];
    let mut pMatrix: *mut f32 = m4x4.as_mut_ptr();
    m4x4[5] = *pIn.offset(4);
    pMatrix = &mut *m4x4.as_mut_ptr().offset(0 as isize) as *mut f32;
    *pMatrix.offset(0) + *pMatrix.offset(5)
 }
"#;

#[test]
fn wave6s2_array_local_source_with_a_typed_destination_stays_out_of_scope() {
    let (source, receipts) = emit_with_receipts(ARRAY_LOCAL_SOURCE_TYPED_DESTINATION);
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(
        !receipts.contains("DECISION-KV Typed::pMatrix slice-shared")
            && !receipts.contains("DECISION-KV Typed::pMatrix slice-mut"),
        "a typed destination is not admitted by this arm: {receipts}"
    );
}

/// **Control 2.** A source whose extent is NOT in its type — a pointer handed
/// back by a call — is refused by the array arm (and by the pointer arm, whose
/// receiver must be a local path).
const CALL_RESULT_SOURCE: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
 unsafe extern "C" { fn get_buf() -> *mut f32; }
 pub unsafe fn FromCall(n: usize) -> f32 {
    let mut p = 0 as *mut f32;
    p = &mut *get_buf().offset(1 as isize) as *mut f32;
    *p.offset(0) + *p.offset(1)
 }
"#;

#[test]
fn wave6s2_call_result_source_is_refused() {
    let (source, receipts) = emit_with_receipts(CALL_RESULT_SOURCE);
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(
        !receipts.contains("DECISION-KV FromCall::p slice-shared")
            && !receipts.contains("DECISION-KV FromCall::p slice-mut"),
        "{receipts}"
    );
}
