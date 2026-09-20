//! Forward parameter fixtures derived from rs-crown urlparser::strff.

#[test]
fn wave6s_strff_forward_parameter_pass_on() {
    let source = emit(STRFF);
    println!("EMITTED {source}");
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(
        source.contains("ptr: &[i8]"),
        "forward parameter must deliver: {source}"
    );
    // The rendering is the arm that fires: the indexed forward parameter when
    // the pass-on target stays a raw position (`strdup::input` on its
    // `strlen` / `strcpy` C arms), the S3.2′-2b reslice (`ptr = &ptr[1..]`)
    // when it is a slice. wave-4's contract extent (batch-7 probe P2) makes
    // `strdup::input` a slice through its `strlen` contract, so THIS fixture
    // may render either way (R217-2(a): the expectation moves where wave-4
    // intentionally delivers); the index form stays pinned by the revert,
    // incoming-extent and raw-local-caller witnesses below.
    assert!(
        source.contains("let mut __crat_wave6s_pos_") || source.contains("ptr = &ptr[1..];"),
        "forward parameter renders by one of its two arms: {source}"
    );
}

fn emit(input: &str) -> String {
    emit_reverting(input, None)
}

fn emit_reverting(input: &str, revert: Option<&str>) -> String {
    let output = ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("capture original AST");
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("native corpus-mode decisions");
        println!("SLICE RECEIPTS {:#?}", table.slice_use_receipts);
        for (subject, decision) in &table.entries {
            println!("DECISION {} {decision:?}", subject.label);
        }
        let emission = super::emit_files(tcx, &table, &Default::default(), &ctx.retained_c9_plans)
            .expect("native emission plan");
        let mut held = emission.plan.held_classes();
        if let Some(name) = revert {
            let owner = tcx
                .hir_body_owners()
                .find(|owner| tcx.def_path_str(owner.to_def_id()) == name)
                .expect("the reverted fixture function exists");
            held.insert(super::bridge_receipt::SignatureClassId::of(owner));
        }
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
        .into_values()
        .next()
        .expect("one source file")
    })
    .expect("input type-checks");
    println!(
        "WAVE6S_RUNTIME {}",
        serde_json::json!({"input": input, "output": output})
    );
    output
}

#[test]
fn wave6s_brotli_forward_word_and_byte_walk() {
    let source = emit(BROTLI);
    println!("EMITTED {source}");
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(
        source.contains("s2: &[u8]"),
        "forward byte parameter must deliver: {source}"
    );
    assert!(
        source.contains("let mut __crat_wave6s_pos_"),
        "forward byte parameter needs its index: {source}"
    );
    // The computed sub-view argument of the word loop (report 004): `s1` is a
    // sole-blocker row in all six corpus copies.
    assert!(source.contains("s1: &[u8]"), "{source}");
    let joined = source.split_whitespace().collect::<Vec<_>>().join(" ");
    // Composed with wave-6b's width-reader hook the reader takes `&[u8]` and
    // the argument is the checked prefix of the suffix view (no raw pointer);
    // alone, the suffix view is bridged raw into the raw reader.
    assert!(
        joined.contains(
            "BrotliUnalignedRead64((&(s1)[(matched) as usize..]).as_ptr().cast::<core::ffi::c_void>())"
        ) || joined.contains("BrotliUnalignedRead64(&((&(s1)[(matched) as usize..]))[..8])"),
        "the word read takes the suffix view: {source}"
    );
}

const STRFF: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables)]
 unsafe extern "C" {
    fn strlen(p: *const i8) -> usize;
    fn malloc(n: usize) -> *mut core::ffi::c_void;
    fn strcpy(out: *mut i8, input: *const i8) -> *mut i8;
 }
 unsafe extern "C" fn strdup(input: *const i8) -> *mut i8 {
    let n = strlen(input) + 1;
    let dup = malloc(n) as *mut i8;
    if !dup.is_null() { strcpy(dup, input); }
    return dup;
 }
 pub unsafe fn strff(mut ptr: *mut i8, n: i32) -> *mut i8 {
  let mut y = 0; let mut i = 0;
  while i < n { let fresh11 = *ptr; ptr = ptr.offset(1); y = fresh11 as i32; i += 1; }
  strdup(ptr)
 }
 "#;

const BROTLI: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
 unsafe fn BrotliUnalignedRead64(p: *const core::ffi::c_void) -> u64 {
   *(p as *const u64)
 }
pub unsafe fn FindMatchLengthWithLimit(mut s1:
                    *const u8, mut s2: *const u8, mut limit: u64)
                -> u64 {
                let mut matched = 0 as i32 as u64;
                let mut limit2 =
                    (limit >>
                                3 as
                                    i32).wrapping_add(1 as i32 as
                            u64);
                loop {
                    limit2 = limit2.wrapping_sub(1);
                    if !((limit2 != 0) as i32 as i64 != 0) {
                        break;
                    }
                    if (BrotliUnalignedRead64(s2 as *const core::ffi::c_void) ==
                                            BrotliUnalignedRead64(s1.offset(matched as isize) as
                                                    *const core::ffi::c_void)) as i32 as i64 != 0 {
                        s2 = s2.offset(8 as i32 as isize);
                        matched =
                            (matched as
                                                u64).wrapping_add(8 as i32 as
                                            u64) as u64 as u64;
                    } else {
                        let mut x =
                            BrotliUnalignedRead64(s2 as *const core::ffi::c_void) ^
                                BrotliUnalignedRead64(s1.offset(matched as isize) as
                                        *const core::ffi::c_void);
                        let mut matching_bits =
                            (x as u64).trailing_zeros() as i32 as u64;
                        matched =
                            (matched as
                                                u64).wrapping_add(matching_bits >>
                                            3 as i32) as u64 as u64;
                        return matched;
                    }
                }
                limit =
                    (limit &
                                7 as i32 as
                                    u64).wrapping_add(1 as i32 as
                            u64);
                loop {
                    limit = limit.wrapping_sub(1);
                    if !(limit != 0) { break; }
                    if (*s1.offset(matched as isize) as i32 ==
                                            *s2 as i32) as i32 as i64 != 0 {
                        s2 = s2.offset(1);
                        matched = matched.wrapping_add(1);
                    } else { return matched }
                }
                return matched;
            }

"#;

#[test]
fn wave6s_strff_revert_withdraws_index_and_tail_view() {
    let source = emit_reverting(STRFF, Some("strff"));
    assert!(super::verify::type_checks_str(&source));
    assert!(source.contains("ptr: *mut i8"), "{source}");
    assert!(!source.contains("__crat_wave6s_pos_"), "{source}");
}

#[test]
fn wave6s_strff_mixed_return_preserves_shared_permission_hold() {
    let input = STRFF.replace(
        "return dup;",
        "if n == 5 { return input as *mut i8; } return dup;",
    );
    let source = emit(&input);
    assert!(super::verify::type_checks_str(&source));
    assert!(source.contains("ptr: *mut i8"), "{source}");
    assert!(!source.contains("__crat_wave6s_pos_"), "{source}");
}

#[test]
fn wave6s_backward_parameter_keeps_its_separate_hold() {
    let source = emit(&STRFF.replace("ptr.offset(1)", "ptr.offset(-1)"));
    assert!(super::verify::type_checks_str(&source));
    assert!(!source.contains("__crat_wave6s_pos_"), "{source}");
}

#[test]
fn wave6s_strff_incoming_preserves_tail_extent() {
    let input =
        format!("{STRFF}\npub unsafe fn drive(p: *mut i8, n: i32) -> *mut i8 {{ strff(p, n) }}");
    let source = emit(&input);
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(source.contains("ptr: &[i8]"), "{source}");
    assert!(
        source.contains("p: *mut i8"),
        "thin incoming source stays raw: {source}"
    );
    assert!(
        source.contains("FALLBACK_SLICE_EXTENT"),
        "prefix count does not prove the NUL tail: {source}"
    );
}

/// urlparser `url_get_port` → `strff`, reduced with the real caller: the argument
/// `hostname` is an analysis-Raw local (allocated by a local callee, freed
/// here) and the caller already delivers `url`. Report 002's census recorded
/// this owner withdrawn at `restore-family-interface-path:[38, 58, 57, 55, 43]`
/// from `url_get_port`'s `unwitnessed-family-refusal:blocked-subject:kind-raw`.
const STRFF_WITH_URL_GET_PORT: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables)]
 unsafe extern "C" {
    fn strlen(p: *const i8) -> usize;
    fn malloc(n: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
    fn strcpy(out: *mut i8, input: *const i8) -> *mut i8;
 }
 unsafe extern "C" fn strdup(input: *const i8) -> *mut i8 {
    let n = strlen(input) + 1;
    let dup = malloc(n) as *mut i8;
    if !dup.is_null() { strcpy(dup, input); }
    return dup;
 }
 unsafe fn strff(mut ptr: *mut i8, n: i32) -> *mut i8 {
  let mut y = 0; let mut i = 0;
  while i < n { let fresh11 = *ptr; ptr = ptr.offset(1); y = fresh11 as i32; i += 1; }
  strdup(ptr)
 }
 unsafe fn url_get_hostname() -> *mut i8 { malloc(64) as *mut i8 }
 pub unsafe fn url_get_port(url: *mut i8, n: i32) -> *mut i8 {
    let hostname = url_get_hostname();
    let first = *url;
    let tmp_hostname = strff(hostname, n);
    free(hostname as *mut core::ffi::c_void);
    tmp_hostname
 }
 "#;

fn emit_with_family_receipts(input: &str) -> (String, String) {
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
        for edit in &table.seams.edits {
            println!("SEAM owner={:?} src={:?} repl={} zero={} shape={} found={:?} expected={:?} spec={:?} outbound={}", edit.owner_class, edit.source_node, edit.replacement, edit.zero_syntax, edit.source_shape, edit.found, edit.expected, edit.spec, edit.raw_outbound.is_some());
        }
        for block in &table.seams.blocked {
            println!("SEAM-BLOCK {block:?}");
        }
        *sink.lock().unwrap() = format!(
            "{:#?}",
            ctx.raw_boundary_artifacts.additive_family_receipts
        );
        let emission = super::emit_files(tcx, &table, &Default::default(), &ctx.retained_c9_plans)
            .expect("native emission plan");
        for edits in emission.plan.by_file.values() {
            for edit in edits {
                println!(
                    "EDIT {}..{} {:?} owner={:?} kind={:?}",
                    edit.lo,
                    edit.hi,
                    edit.replacement,
                    edit.owner_path,
                    edit.bridge.as_ref().map(|b| b.bridge_kind.clone())
                );
            }
        }
        for (id, class) in &emission.plan.class_finalization.classes {
            println!(
                "CLASS {} ready={} holds={:?}",
                tcx.def_path_str(id.local_def_id().to_def_id()),
                class.is_ready(),
                class.hold_reasons()
            );
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
        .into_values()
        .next()
        .expect("one source file")
    })
    .expect("input type-checks");
    let receipts = receipts.lock().unwrap().clone();
    println!(
        "WAVE6S_RUNTIME {}",
        serde_json::json!({"input": input, "output": output})
    );
    (output, receipts)
}

/// **Caller-bearing witness (report 004; R401-4 lands the fix).**
/// The callee-only fixture delivers `ptr: &[i8]`; adding the real caller
/// must not withdraw it. Today the caller's class is charged the C arm for
/// its raw argument `hostname` while the adapter site is owned by the callee
/// class, so the caller holds (`blocked-subject:kind-raw`,
/// `missing-required-arm:c`), its previously applied `url` is "lost", and the
/// restoration walk withdraws `strff` through the interface graph.
#[test]
fn wave6s_strff_survives_its_raw_local_caller() {
    let (source, receipts) = emit_with_family_receipts(STRFF_WITH_URL_GET_PORT);
    println!("EMITTED {source}");
    println!("FAMILY RECEIPTS {receipts}");
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(
        source.contains("ptr: &[i8]"),
        "the forward parameter is withdrawn by its caller: {receipts}\n{source}"
    );
    assert!(source.contains("url: &i8"), "{source}");
    assert!(
        !receipts.contains("restore-family-interface-path"),
        "interface restoration withdrew a caller-side family: {receipts}"
    );
}

/// brotli `StoreRangeH2` → `StoreH2` → `HashBytesH2`: the caller passes a thin
/// raw `data` (held `local-callee-access-extent`), the callee now delivers.
const STOREH2_WITH_STORE_RANGE: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables, non_snake_case, non_upper_case_globals)]
 #[repr(C)] pub struct H2 { pub buckets_: [u32; 65536] }
 static kHashMul64: u64 = 0x1E35A7BD1E35A7BD;
 unsafe fn BrotliUnalignedRead64(p: *const core::ffi::c_void) -> u64 { *(p as *const u64) }
 unsafe fn HashBytesH2(mut data: *const u8) -> u32 {
    let h = (BrotliUnalignedRead64(data as *const core::ffi::c_void) << (64 - 8 * 5)).wrapping_mul(kHashMul64);
    return (h >> (64 - 16)) as u32;
 }
 pub unsafe fn StoreH2(mut self_0: *mut H2, mut data: *const u8, mask: usize, ix: usize) {
    let key = HashBytesH2(&*data.offset((ix & mask) as isize));
    (*self_0).buckets_[key as usize] = ix as u32;
 }
 pub unsafe fn StoreRangeH2(mut self_0: *mut H2, mut data: *const u8, mask: usize, ix_start: usize, ix_end: usize) {
    let mut i = ix_start;
    while i < ix_end { StoreH2(self_0, data, mask, i); i = i.wrapping_add(1); }
 }
"#;

/// **Second caller-bearing witness (report 004; R401-4) — the `unrestored` form before the fix.**
/// `StoreRangeH2` (caller) and `StoreH2` (callee) depend on each other in the
/// class graph (`interface-call-zero-syntax` one way, the raw→slice adapter
/// the other); when the caller's class holds for the mis-charged C arm, both
/// `self_0` deliveries are "lost", the restoration walk finds each owner held
/// only through the other and requests nothing, and the pipeline fails with
/// `additive-family-preservation-invariant:unrestored:[(9, 1), (10, 1)]` —
/// wave-5d's binn `binn_get_bool` MAX-3 shape.
#[test]
fn wave6s_storeh2_survives_its_thin_raw_caller() {
    let (source, receipts) = emit_with_family_receipts(STOREH2_WITH_STORE_RANGE);
    println!("EMITTED {source}");
    println!("FAMILY RECEIPTS {receipts}");
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(source.contains("data: &[u8]"), "{source}");
    assert!(source.contains("self_0: &mut H2"), "{source}");
    // The caller's thin raw `data` is adapted at the call. Under the arm-C
    // charge probe (report 004) the adjacency arm licensed the FOLLOWING
    // argument `mask` as the length — a bit mask, not an extent. Wave-4
    // R408-1 (report 024) licenses a sibling only on a count position of the
    // callee's own contract, so the construction takes the fallback extent.
    let compact = source.split_whitespace().collect::<String>();
    assert!(
        compact.contains(
            "StoreH2(self_0,core::slice::from_raw_parts(data,crate::FALLBACK_SLICE_EXTENT),"
        ),
        "{source}"
    );
    assert!(!compact.contains("(mask)asusize"), "{source}");
}

/// Negative controls: the arithmetic consumed by anything other than the
/// call-argument spine is not a view and keeps the collector's verdict.
#[test]
fn wave6s_computed_view_refuses_non_argument_consumers() {
    // A copy of the arithmetic.
    let copied = STOREH2.replace(
        "let key = HashBytesH2(&*data.offset((ix & mask) as isize));",
        "let q = data.offset((ix & mask) as isize); let key = HashBytesH2(q);",
    );
    let source = emit(&copied);
    assert!(super::verify::type_checks_str(&source), "{source}");
    // **Re-premised by wave-4's W4-LIFT (R475-2), disclosed in wave-4 report
    // 038.** The callee is lifted to the slice form by its own callee's exact
    // licensed width, and `StoreH2`'s parameter follows it, so the old
    // `data: *const u8` no longer states this control's claim. The claim
    // itself is unchanged and is asserted directly: the arithmetic copied into
    // a local is NOT a view, so it does not reach the argument as
    // `&(data)[..]` — it goes through the local, and the bridge at the call is
    // the §77 fallback with its receipt.
    assert!(!source.contains("HashBytesH2((&(data)["), "{source}");
    assert!(
        source.contains("let q = (&(data)[(ix & mask)..]).as_ptr();"),
        "{source}"
    );
    // A borrowed element bound to a local, not passed on.
    let bound = STOREH2.replace(
        "let key = HashBytesH2(&*data.offset((ix & mask) as isize));",
        "let r = &*data.offset((ix & mask) as isize); let key = HashBytesH2(r);",
    );
    let source = emit(&bound);
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(!source.contains("HashBytesH2((&(data)["), "{source}");
}

/// A signed delta is the bidirectional family's (R394-2): no view.
#[test]
fn wave6s_computed_view_refuses_signed_delta() {
    let signed = STOREH2
        .replace(
            "mask: usize, ix: usize",
            "mask: usize, ix: usize, back: i32",
        )
        .replace(
            "&*data.offset((ix & mask) as isize)",
            "&*data.offset(back as isize)",
        );
    let source = emit(&signed);
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(source.contains("data: *const u8"), "{source}");
}

const STOREH2: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables, non_snake_case, non_upper_case_globals)]
 #[repr(C)] pub struct H2 { pub buckets_: [u32; 65536] }
 static kHashMul64: u64 = 0x1E35A7BD1E35A7BD;
 unsafe fn BrotliUnalignedRead64(p: *const core::ffi::c_void) -> u64 { *(p as *const u64) }
 unsafe fn HashBytesH2(mut data: *const u8) -> u32 {
    let h = (BrotliUnalignedRead64(data as *const core::ffi::c_void) << (64 - 8 * 5)).wrapping_mul(kHashMul64);
    return (h >> (64 - 16)) as u32;
 }
 pub unsafe fn StoreH2(mut self_0: *mut H2, mut data: *const u8, mask: usize, ix: usize) {
    let key = HashBytesH2(&*data.offset((ix & mask) as isize));
    (*self_0).buckets_[key as usize] = ix as u32;
 }
"#;

#[test]
fn wave6s_storeh2_computed_subview_argument() {
    let source = emit(STOREH2);
    println!("EMITTED {source}");
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(source.contains("data: &[u8]"), "{source}");
    // **Re-premised by wave-4's W4-LIFT (R475-2), disclosed in wave-4 report
    // 038.** `HashBytesH2` hands its own parameter to `BrotliUnalignedRead64`,
    // whose region contract carries an exact eight-byte width, so that callee
    // is no longer raw: it takes the slice form and the suffix view is passed
    // WHOLE, with no `as_ptr()` downgrade in between. The view itself is
    // unchanged — this is the same computed sub-view, one raw bridge shorter.
    assert!(
        source.contains("HashBytesH2((&(data)[(ix & mask)..]))"),
        "the suffix view is passed whole to a lifted callee: {source}"
    );
    assert!(
        !source.contains(".as_ptr())"),
        "and the raw downgrade is gone: {source}"
    );
}

/// brotli `ClearHistogramsLiteral` → `HistogramClearLiteral`: the arithmetic
/// itself is the argument, no borrow.
const CLEAR_HISTOGRAMS: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
 unsafe extern "C" { fn memset(s: *mut core::ffi::c_void, c: i32, n: usize) -> *mut core::ffi::c_void; }
 #[repr(C)] pub struct HistogramLiteral { pub data_: [u32; 256], pub total_count_: usize, pub bit_cost_: f64 }
 unsafe fn HistogramClearLiteral(mut self_0: *mut HistogramLiteral) {
    memset(((*self_0).data_).as_mut_ptr() as *mut core::ffi::c_void, 0, core::mem::size_of::<[u32; 256]>());
    (*self_0).total_count_ = 0;
    (*self_0).bit_cost_ = f64::INFINITY;
 }
 pub unsafe fn ClearHistogramsLiteral(mut array: *mut HistogramLiteral, mut length: usize) {
    let mut i: usize = 0;
    while i < length { HistogramClearLiteral(array.offset(i as isize)); i = i.wrapping_add(1); }
 }
"#;

#[test]
fn wave6s_clear_histograms_direct_offset_argument() {
    let (source, receipts) = emit_with_family_receipts(CLEAR_HISTOGRAMS);
    println!("EMITTED {source}");
    println!("FAMILY RECEIPTS {receipts}");
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(
        source.contains("array: &mut [HistogramLiteral]"),
        "{source}"
    );
}

/// brotli `BrotliCreateHuffmanTree` → `InitHuffmanTree`: a mutable computed
/// sub-view argument.
const CREATE_HUFFMAN_TREE: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
 #[repr(C)] #[derive(Clone, Copy)] pub struct HuffmanTree { pub total_count_: u32, pub index_left_: i16, pub index_right_or_value_: i16 }
 unsafe fn InitHuffmanTree(mut self_0: *mut HuffmanTree, mut count: u32, mut left: i16, mut right: i16) {
    (*self_0).total_count_ = count;
    (*self_0).index_left_ = left;
    (*self_0).index_right_or_value_ = right;
 }
 pub unsafe fn BrotliCreateHuffmanTree(mut data: *const u32, length: usize, mut tree: *mut HuffmanTree) {
    let mut n: usize = 0;
    let mut i: usize = 0;
    while i < length {
        let count = *data.offset(i as isize);
        if count != 0 {
            let fresh1 = n;
            n = n.wrapping_add(1);
            InitHuffmanTree(&mut *tree.offset(fresh1 as isize), count, -1, -1);
        }
        i = i.wrapping_add(1);
    }
 }
"#;

#[test]
fn wave6s_create_huffman_tree_mutable_subview_argument() {
    let (source, receipts) = emit_with_family_receipts(CREATE_HUFFMAN_TREE);
    println!("EMITTED {source}");
    println!("FAMILY RECEIPTS {receipts}");
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(source.contains("tree: &mut [HuffmanTree]"), "{source}");
}

/// The E-ADAPT-W4 shape with a forward delta: the base now delivers and the
/// scalar-reference callee receives the checked element of the suffix.
#[test]
fn wave6s_forward_computed_view_delivers_the_scalar_reference_base() {
    let source = emit(
        "#![allow(dead_code, unused_unsafe, unused_mut)]\n\
         pub unsafe fn scalar(p: *const i32) -> i32 { *p }\n\
         pub unsafe fn caller(base: *const i32) -> i32 { scalar(base.offset(1)) }\n",
    );
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(source.contains("base: &[i32]"), "{source}");
    assert!(source.contains("scalar(&(&(base)[1..])[0])"), "{source}");
}

/// brotli `ComputeDistanceCost`: a computed sub-view bound to a local
/// (`let cmd: *const Command = &*cmds.offset(i) as *const Command`) that a
/// local callee and field reads consume.
const COMPUTE_DISTANCE_COST: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
 #[repr(C)] #[derive(Clone, Copy)] pub struct Command { pub insert_len_: u32, pub copy_len_: u32, pub dist_extra_: u32, pub cmd_prefix_: u16, pub dist_prefix_: u16 }
 unsafe fn CommandCopyLen(mut self_0: *const Command) -> u32 { return (*self_0).copy_len_ & 0x1ffffff; }
 pub unsafe fn ComputeDistanceCost(mut cmds: *const Command, mut num_commands: usize) -> i32 {
    let mut i: usize = 0;
    let mut total: u32 = 0;
    while i < num_commands {
        let mut cmd: *const Command = &*cmds.offset(i as isize) as *const Command;
        if CommandCopyLen(cmd) != 0 && (*cmd).cmd_prefix_ as i32 >= 128 {
            total = total.wrapping_add((*cmd).dist_prefix_ as u32);
        }
        i = i.wrapping_add(1);
    }
    return total as i32;
 }
"#;

#[test]
fn wave6s_compute_distance_cost_computed_view_bound_to_local() {
    let (source, receipts) = emit_with_family_receipts(COMPUTE_DISTANCE_COST);
    println!("EMITTED {source}");
    println!("FAMILY RECEIPTS {receipts}");
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(source.contains("cmds: &[Command]"), "{source}");
    assert!(
        source.contains("let mut cmd: &Command = &(cmds)[i];"),
        "the bound view composes with the destination's identity-cast peel: {source}"
    );
    assert!(source.contains("self_0: &Command"), "{source}");
}

/// heman `kmVec4TransformArray`: derived pointers bound to locals and passed
/// on (`let in_0 = pV.offset(i * vStride); … kmVec4Transform(out, in_0, pM)`).
const KM_VEC4_TRANSFORM_ARRAY: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
 #[repr(C)] #[derive(Clone, Copy)] pub struct kmVec4 { pub x: f32, pub y: f32, pub z: f32, pub w: f32 }
 #[repr(C)] #[derive(Clone, Copy)] pub struct kmMat4 { pub mat: [f32; 16] }
 unsafe fn kmVec4Transform(mut pOut: *mut kmVec4, mut pV: *const kmVec4, mut pM: *const kmMat4) {
    (*pOut).x = (*pV).x * (*pM).mat[0] + (*pV).y * (*pM).mat[4] + (*pV).z * (*pM).mat[8] + (*pV).w * (*pM).mat[12];
    (*pOut).y = (*pV).x * (*pM).mat[1] + (*pV).y * (*pM).mat[5] + (*pV).z * (*pM).mat[9] + (*pV).w * (*pM).mat[13];
    (*pOut).z = (*pV).x * (*pM).mat[2] + (*pV).y * (*pM).mat[6] + (*pV).z * (*pM).mat[10] + (*pV).w * (*pM).mat[14];
    (*pOut).w = (*pV).x * (*pM).mat[3] + (*pV).y * (*pM).mat[7] + (*pV).z * (*pM).mat[11] + (*pV).w * (*pM).mat[15];
 }
 pub unsafe fn kmVec4TransformArray(mut pOut: *mut kmVec4, mut outStride: u32, mut pV: *const kmVec4, mut vStride: u32, mut pM: *const kmMat4, mut count: u32) {
    let mut i = 0u32;
    while i < count {
        let mut in_0 = pV.offset(i.wrapping_mul(vStride) as isize);
        let mut out = pOut.offset(i.wrapping_mul(outStride) as isize);
        kmVec4Transform(out, in_0, pM);
        i = i.wrapping_add(1);
    }
 }
"#;

/// **Third caller-side witness (report 005; R401-4) — same-function form.** The
/// derived local `out` (degraded `copy-source-coupled`) is the raw source of
/// the converted `kmVec4Transform::pOut: &mut kmVec4`, so the arm-C charge
/// lands on it and holds its own class (`blocked-subject:copy-source-coupled`)
/// although `pV` / `pOut` both plan their suffix raw views.
#[test]
fn wave6s_km_vec4_transform_array_derived_pointers_bound_to_locals() {
    let (source, receipts) = emit_with_family_receipts(KM_VEC4_TRANSFORM_ARRAY);
    println!("EMITTED {source}");
    println!("FAMILY RECEIPTS {receipts}");
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(source.contains("pV: &[kmVec4]"), "{source}");
    assert!(source.contains("pOut: &mut [kmVec4]"), "{source}");
    assert!(
        source.contains("let mut in_0 = (&(pV)[(i.wrapping_mul(vStride)) as usize..]).as_ptr();"),
        "{source}"
    );
}

/// brotli `EvaluateNode` → `ComputeDistanceShortcut`: a MUTABLE slice base
/// passed as-is into a parameter that settles as a SHARED slice — the
/// `&mut [T] → &[T]` coercion is zero syntax; wave-5c's same-slice carrier
/// (W-C1) completes it through its coercion arm (report 006).
const EVALUATE_NODE: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
 #[repr(C)] #[derive(Clone, Copy)] pub struct U { pub cost: f32, pub shortcut: u32 }
 #[repr(C)] #[derive(Clone, Copy)] pub struct ZopfliNode { pub length: u32, pub distance: u32, pub dcode_insert_length: u32, pub u: U }
 unsafe fn ZopfliNodeCopyLength(mut self_0: *const ZopfliNode) -> u32 { return (*self_0).length & 0x1ffffff; }
 unsafe fn ComputeDistanceShortcut(block_start: usize, pos: usize, gap: usize, mut nodes: *const ZopfliNode) -> u32 {
    let clen = ZopfliNodeCopyLength(&*nodes.offset(pos as isize)) as usize;
    if pos == 0 { return 0; }
    if pos.wrapping_sub(clen) == block_start { return 0; }
    return (*nodes.offset(pos.wrapping_sub(clen) as isize)).u.shortcut;
 }
 pub unsafe fn EvaluateNode(block_start: usize, pos: usize, gap: usize, mut nodes: *mut ZopfliNode) {
    let mut node_cost = (*nodes.offset(pos as isize)).u.cost;
    (*nodes.offset(pos as isize)).u.shortcut = ComputeDistanceShortcut(block_start, pos, gap, nodes);
    if node_cost <= 1.0 { (*nodes.offset(pos as isize)).u.cost = 0.0; }
 }
"#;

#[test]
fn wave6s_evaluate_node_bare_pass_on_into_same_form_parameter() {
    let (source, receipts) = emit_with_family_receipts(EVALUATE_NODE);
    println!("EMITTED {source}");
    println!("FAMILY RECEIPTS {receipts}");
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(source.contains("mut nodes: &mut [ZopfliNode]"), "{source}");
    assert!(source.contains("mut nodes: &[ZopfliNode]"), "{source}");
    let joined = source.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(
        joined.contains("ComputeDistanceShortcut(block_start, pos, gap, nodes)"),
        "the same-form pass-on stays zero-syntax: {source}"
    );
    assert!(joined.contains("nodes[pos].u.shortcut ="), "{source}");
}

/// brotli `FindBlocksLiteral::cost`: a delivered slice base cast to `*mut
/// c_void` at a foreign counted callee (`memset`).
const FIND_BLOCKS_COST: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
 unsafe extern "C" { fn memset(s: *mut core::ffi::c_void, c: i32, n: usize) -> *mut core::ffi::c_void; }
 pub unsafe fn FindBlocks(mut cost: *mut f64, num_histograms: usize, mut insert: *const f64) -> usize {
    let mut best: usize = 0;
    memset(cost as *mut core::ffi::c_void, 0, core::mem::size_of::<f64>().wrapping_mul(num_histograms));
    let mut k: usize = 0;
    let mut min_cost = 1e99f64;
    while k < num_histograms {
        *cost.offset(k as isize) += *insert.offset(k as isize);
        if *cost.offset(k as isize) < min_cost { min_cost = *cost.offset(k as isize); best = k; }
        k = k.wrapping_add(1);
    }
    best
 }
"#;

/// Relay 004 §1's first ask: the cast-argument bridge. It already exists —
/// this pins it (`VoidFromSliceMut`, T2 at the foreign counted callee).
#[test]
fn wave6s_cast_argument_bridge_already_exists() {
    let (source, receipts) = emit_with_family_receipts(FIND_BLOCKS_COST);
    println!("EMITTED {source}");
    println!("FAMILY RECEIPTS {receipts}");
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(source.contains("cost: &mut [f64]"), "{source}");
    assert!(
        source.contains("memset(cost.as_mut_ptr().cast::<core::ffi::c_void>(), 0,"),
        "{source}"
    );
}

/// tulipindicators `smoke::get_array` (corpus regression of the partial
/// census, report 006): the Option value composition snapshots the seam's
/// text, so the computed-view rendering must be on the seam set before it —
/// `strtok((&mut (line)[1..]).as_mut_ptr(), …)` composed into `.as_ref()`.
#[test]
fn wave6s_computed_view_composes_into_option_value() {
    let src = r#"
 #![allow(dead_code, unused_mut, unused_variables, non_snake_case, static_mut_refs)]
 unsafe extern "C" {
    fn strtok(s: *mut i8, delim: *const i8) -> *mut i8;
    fn atof(s: *const i8) -> f64;
 }
 static mut BUF: [i8; 64] = [0; 64];
 unsafe fn next_line() -> *mut i8 { BUF.as_mut_ptr() }
 pub unsafe fn get_array(mut s: *mut f64) -> i32 {
    let mut line: *mut i8 = next_line();
    if *line.offset(0 as i32 as isize) as i32 != '{' as i32 { return 0; }
    let mut num: *mut i8 = strtok(line.offset(1 as i32 as isize), b",}\r\n\0" as *const u8 as *const i8);
    if num.is_null() { return 0; }
    let mut inp: *mut f64 = s;
    loop {
        *inp = atof(num);
        inp = inp.offset(1);
        num = strtok(0 as *mut i8, b",}\r\n\0" as *const u8 as *const i8);
        if num.is_null() { break; }
    }
    return 1;
 }
"#;
    let (source, receipts) = emit_with_family_receipts(src);
    println!("EMITTED {source}");
    println!("FAMILY RECEIPTS {receipts}");
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(source.contains("line: &mut [i8]"), "{source}");
    let joined = source.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(
        joined.contains("strtok((&mut (line)[(1 as i32) as usize..]).as_mut_ptr(),"),
        "{source}"
    );
}

/// **Sum of forward deltas (report 007 §5a).** lodepng
/// `lodepng_chunk_generate_crc`: `chunk.offset((8 as isize) + (length as
/// isize))` — the delta is a `+` of a non-negative literal and an unsigned
/// value under casts. Conditional on a UB-free input each summand is
/// non-negative and a sum leaving the object would already be the input's
/// UB, so the sum is forward and the argument is the suffix view.
#[test]
fn wave6s_generate_crc_sum_of_forward_deltas() {
    let (source, receipts) = emit_with_family_receipts(GENERATE_CRC_LENGTH_GIVEN);
    println!("EMITTED {source}");
    println!("FAMILY RECEIPTS {receipts}");
    assert!(super::verify::type_checks_str(&source), "{source}");
    let flat: String = source.chars().filter(|c| !c.is_whitespace()).collect();
    assert!(
        flat.contains("fnlodepng_chunk_generate_crc(mutchunk:&mut[libc::c_uchar]"),
        "{source}"
    );
    assert!(
        flat.contains("lodepng_set32bitInt((&mut(chunk)[((8aslibc::c_intasisize)+(lengthasisize))asusize..]),CRC)"),
        "{source}"
    );
}

/// A `+` with a signed summand keeps the cursor verdict (R394-2).
#[test]
fn wave6s_sum_with_signed_summand_keeps_the_cursor_verdict() {
    let signed = GENERATE_CRC_LENGTH_GIVEN.replace(
        "(8 as libc::c_int as isize) + (length as isize)",
        "(8 as libc::c_int as isize) + (length as libc::c_int as isize)",
    );
    assert_ne!(signed, GENERATE_CRC_LENGTH_GIVEN);
    let rows = super::emit_tests::decisions_of(&signed);
    let reason = rows
        .iter()
        .rev()
        .find(|(n, p, _)| n == "chunk" && *p)
        .map(|(_, _, r)| r.clone())
        .expect("generate_crc::chunk");
    assert_eq!(reason, "slice-cursor-use", "{rows:?}");
}

/// The faithful lodepng shape (`lodepng_chunk_generate_crc::chunk`,
/// `slice-cursor-use` at `60f52cff`): with the sum forward and the bare
/// `from_raw_parts` seam of a slice callee taking the suffix view, the
/// subject delivers, its `lodepng_chunk_length(chunk)` pass-on through the
/// existing thin-element carrier.
#[test]
fn wave6s_generate_crc_faithful_delivers() {
    let (source, receipts) = emit_with_family_receipts(GENERATE_CRC);
    println!("EMITTED {source}");
    println!("FAMILY RECEIPTS {receipts}");
    assert!(super::verify::type_checks_str(&source), "{source}");
    let flat: String = source.chars().filter(|c| !c.is_whitespace()).collect();
    assert!(
        flat.contains("fnlodepng_chunk_generate_crc(mutchunk:&mut[libc::c_uchar])"),
        "{source}"
    );
    assert!(
        flat.contains("lodepng_chunk_length(chunk.first().unwrap())"),
        "{source}"
    );
    assert_eq!(receipts.trim(), "[]", "no family withdrawal: {receipts}");
}

const GENERATE_CRC: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables, non_snake_case, non_upper_case_globals)]
 mod libc { pub type c_uchar = u8; pub type c_uint = u32; pub type c_int = i32; pub type c_ulong = u64; }
 pub type size_t = libc::c_ulong;
 static lodepng_crc32_table: [libc::c_uint; 256] = [0; 256];
 unsafe extern "C" fn lodepng_read32bitInt(mut buffer: *const libc::c_uchar) -> libc::c_uint {
    return (*buffer.offset(0 as libc::c_int as isize) as libc::c_uint) << 24 as libc::c_uint
        | (*buffer.offset(1 as libc::c_int as isize) as libc::c_uint) << 16 as libc::c_uint
        | (*buffer.offset(2 as libc::c_int as isize) as libc::c_uint) << 8 as libc::c_uint
        | *buffer.offset(3 as libc::c_int as isize) as libc::c_uint;
 }
 unsafe extern "C" fn lodepng_set32bitInt(mut buffer: *mut libc::c_uchar, mut value: libc::c_uint) {
    *buffer.offset(0 as libc::c_int as isize) = (value >> 24 as libc::c_int & 0xff as libc::c_int as libc::c_uint) as libc::c_uchar;
    *buffer.offset(1 as libc::c_int as isize) = (value >> 16 as libc::c_int & 0xff as libc::c_int as libc::c_uint) as libc::c_uchar;
    *buffer.offset(2 as libc::c_int as isize) = (value >> 8 as libc::c_int & 0xff as libc::c_int as libc::c_uint) as libc::c_uchar;
    *buffer.offset(3 as libc::c_int as isize) = (value & 0xff as libc::c_int as libc::c_uint) as libc::c_uchar;
 }
 pub unsafe extern "C" fn lodepng_chunk_length(mut chunk: *const libc::c_uchar) -> libc::c_uint {
    return lodepng_read32bitInt(chunk);
 }
 pub unsafe extern "C" fn lodepng_crc32(mut data: *const libc::c_uchar, mut length: size_t) -> libc::c_uint {
    let mut r = 0xffffffff as libc::c_uint;
    let mut i: size_t = 0;
    i = 0 as libc::c_int as size_t;
    while i < length {
        r = lodepng_crc32_table[((r ^ *data.offset(i as isize) as libc::c_uint) & 0xff as libc::c_uint) as usize] ^ r >> 8 as libc::c_uint;
        i = i.wrapping_add(1);
    }
    return r ^ 0xffffffff as libc::c_uint;
 }
 pub unsafe extern "C" fn lodepng_chunk_generate_crc(mut chunk: *mut libc::c_uchar) {
    let mut length = lodepng_chunk_length(chunk);
    let mut CRC = lodepng_crc32(&mut *chunk.offset(4 as libc::c_int as isize), length.wrapping_add(4 as libc::c_int as libc::c_uint) as size_t);
    lodepng_set32bitInt(chunk.offset((8 as libc::c_int as isize) + (length as isize)), CRC);
 }
"#;

const GENERATE_CRC_LENGTH_GIVEN: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables, non_snake_case, non_upper_case_globals)]
 mod libc { pub type c_uchar = u8; pub type c_uint = u32; pub type c_int = i32; pub type c_ulong = u64; }
 pub type size_t = libc::c_ulong;
 static lodepng_crc32_table: [libc::c_uint; 256] = [0; 256];
 unsafe extern "C" fn lodepng_read32bitInt(mut buffer: *const libc::c_uchar) -> libc::c_uint {
    return (*buffer.offset(0 as libc::c_int as isize) as libc::c_uint) << 24 as libc::c_uint
        | (*buffer.offset(1 as libc::c_int as isize) as libc::c_uint) << 16 as libc::c_uint
        | (*buffer.offset(2 as libc::c_int as isize) as libc::c_uint) << 8 as libc::c_uint
        | *buffer.offset(3 as libc::c_int as isize) as libc::c_uint;
 }
 unsafe extern "C" fn lodepng_set32bitInt(mut buffer: *mut libc::c_uchar, mut value: libc::c_uint) {
    *buffer.offset(0 as libc::c_int as isize) = (value >> 24 as libc::c_int & 0xff as libc::c_int as libc::c_uint) as libc::c_uchar;
    *buffer.offset(1 as libc::c_int as isize) = (value >> 16 as libc::c_int & 0xff as libc::c_int as libc::c_uint) as libc::c_uchar;
    *buffer.offset(2 as libc::c_int as isize) = (value >> 8 as libc::c_int & 0xff as libc::c_int as libc::c_uint) as libc::c_uchar;
    *buffer.offset(3 as libc::c_int as isize) = (value & 0xff as libc::c_int as libc::c_uint) as libc::c_uchar;
 }
 pub unsafe extern "C" fn lodepng_chunk_length(mut chunk: *const libc::c_uchar) -> libc::c_uint {
    return lodepng_read32bitInt(chunk);
 }
 pub unsafe extern "C" fn lodepng_crc32(mut data: *const libc::c_uchar, mut length: size_t) -> libc::c_uint {
    let mut r = 0xffffffff as libc::c_uint;
    let mut i: size_t = 0;
    i = 0 as libc::c_int as size_t;
    while i < length {
        r = lodepng_crc32_table[((r ^ *data.offset(i as isize) as libc::c_uint) & 0xff as libc::c_uint) as usize] ^ r >> 8 as libc::c_uint;
        i = i.wrapping_add(1);
    }
    return r ^ 0xffffffff as libc::c_uint;
 }
 pub unsafe extern "C" fn lodepng_chunk_generate_crc(mut chunk: *mut libc::c_uchar, mut length: libc::c_uint) {
    let mut CRC = lodepng_crc32(&mut *chunk.offset(4 as libc::c_int as isize), length.wrapping_add(4 as libc::c_int as libc::c_uint) as size_t);
    lodepng_set32bitInt(chunk.offset((8 as libc::c_int as isize) + (length as isize)), CRC);
 }
"#;

/// **Borrow-deref-double-cast view at a foreign position (relay 008 §3,
/// routed from wave-6s2).** brotli `MakeUncompressedStream`:
/// `memcpy(&mut *output.offset(result) as *mut u8 as *mut c_void, …)`. The
/// spine already walks the casts; what was missing is the foreign call fact's
/// ROOT — `AddrOfCast` carried none, so the site was never a raw-boundary
/// argument of `output` and the collector's cursor verdict took it
/// (`slice-cursor-use` at `60f52cff`). Rooted, the site is the subject's own
/// C-arm seam and the view renders `(&mut (output)[result..]).as_mut_ptr()`.
#[test]
fn wave6s_borrow_deref_double_cast_view_at_a_foreign_position() {
    let (source, receipts) = emit_with_family_receipts(MEMSET_DOUBLE_CAST);
    println!("EMITTED {source}");
    println!("FAMILY RECEIPTS {receipts}");
    assert!(super::verify::type_checks_str(&source), "{source}");
    let flat: String = source.chars().filter(|c| !c.is_whitespace()).collect();
    assert!(flat.contains("fnfill(mutoutput:&mut[uint8_t]"), "{source}");
    assert!(
        flat.contains(
            "memset((&mut(output)[(result)asusize..]).as_mut_ptr().cast::<core::ffi::c_void>(),"
        ),
        "{source}"
    );
    assert_eq!(receipts.trim(), "[]", "no family withdrawal: {receipts}");
}

/// The faithful brotli shape: `output` (the `memcpy` destination, a T2
/// open-boundary void bridge) is admitted by the root; `input` (the source,
/// a SHARED view at a pointer-returning foreign callee) holds under the
/// returned-child permission rule `write-through-shared-view` — wave-6r's
/// family. Alone (this lane's tree) the hold withdraws the function's
/// SliceUse stage and both stay raw; composed with wave-6r's libc
/// negative-write contract at `memcpy`'s source (relay 009 §2, batch 8)
/// both deliver, `input` through the suffix view. Either outcome is the
/// rule that owns it (R217-2(a)); this lane's own claim is the rooted view.
#[test]
fn wave6s_make_uncompressed_stream_source_is_wave6r_s_rule() {
    let (source, receipts) = emit_with_family_receipts(MAKE_UNCOMPRESSED_STREAM);
    println!("EMITTED {source}");
    println!("FAMILY RECEIPTS {receipts}");
    assert!(super::verify::type_checks_str(&source), "{source}");
    let flat: String = source.chars().filter(|c| !c.is_whitespace()).collect();
    let delivered = flat.contains("mutinput:&[uint8_t]")
        && flat.contains("mutoutput:&mut[uint8_t]")
        && flat.contains("memcpy((&mut(output)[(result)asusize..]).as_mut_ptr().cast::<core::ffi::c_void>(),(&(input)[(offset)asusize..]).as_ptr().cast::<core::ffi::c_void>(),");
    let held = receipts.contains("write-through-shared-view") || receipts.contains("memcpy:arg=1");
    assert!(delivered || held, "{source}\n{receipts}");
}

const MEMSET_DOUBLE_CAST: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables, non_snake_case, non_upper_case_globals)]
 mod libc { pub type c_void = core::ffi::c_void; pub type c_int = i32; pub type c_ulong = u64; }
 pub type uint8_t = u8;
 pub type size_t = libc::c_ulong;
 unsafe extern "C" { fn memset(d: *mut libc::c_void, c: libc::c_int, n: libc::c_ulong) -> *mut libc::c_void; }
 unsafe extern "C" fn fill(mut output: *mut uint8_t, mut result: size_t, mut n: size_t) {
    *output.offset(0 as libc::c_int as isize) = 1 as libc::c_int as uint8_t;
    memset(&mut *output.offset(result as isize) as *mut uint8_t as *mut libc::c_void, 0 as libc::c_int, n);
 }
"#;

const MAKE_UNCOMPRESSED_STREAM: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables, non_snake_case, non_upper_case_globals)]
 mod libc { pub type c_void = core::ffi::c_void; pub type c_int = i32; pub type c_ulong = u64; pub type c_uint = u32; }
 pub type uint8_t = u8;
 pub type size_t = libc::c_ulong;
 unsafe extern "C" { fn memcpy(d: *mut libc::c_void, s: *const libc::c_void, n: libc::c_ulong) -> *mut libc::c_void; }
 unsafe extern "C" fn MakeUncompressedStream(mut input: *const uint8_t, mut input_size: size_t, mut output: *mut uint8_t) -> size_t {
    let mut size = input_size;
    let mut result = 0 as libc::c_int as size_t;
    let mut offset = 0 as libc::c_int as size_t;
    if input_size == 0 as libc::c_int as libc::c_ulong {
        *output.offset(0 as libc::c_int as isize) = 6 as libc::c_int as uint8_t;
        return 1 as libc::c_int as size_t;
    }
    let fresh95 = result;
    result = result.wrapping_add(1);
    *output.offset(fresh95 as isize) = 0x21 as libc::c_int as uint8_t;
    while size > 0 as libc::c_int as libc::c_ulong {
        let mut chunk_size = if size > (1 as libc::c_int as size_t) << 24 { (1 as libc::c_int as size_t) << 24 } else { size };
        let fresh96 = result;
        result = result.wrapping_add(1);
        *output.offset(fresh96 as isize) = (chunk_size >> 8 as libc::c_int) as uint8_t;
        memcpy(&mut *output.offset(result as isize) as *mut uint8_t as *mut libc::c_void,
            &*input.offset(offset as isize) as *const uint8_t as *const libc::c_void, chunk_size as libc::c_ulong);
        result = (result as libc::c_ulong).wrapping_add(chunk_size as libc::c_ulong) as size_t as size_t;
        offset = (offset as libc::c_ulong).wrapping_add(chunk_size as libc::c_ulong) as size_t as size_t;
        size = (size as libc::c_ulong).wrapping_sub(chunk_size as libc::c_ulong) as size_t as size_t;
    }
    let fresh97 = result;
    result = result.wrapping_add(1);
    *output.offset(fresh97 as isize) = 3 as libc::c_int as uint8_t;
    return result;
 }
"#;

/// **Relay 013 — the slice-use receipt drift that aborted batch 8's census
/// (lodepng class 563, brotli class 1276).** A slice-use candidate retired by
/// R220 keeps its candidate form beside the restored source form
/// (`source_form=raw`, `candidate_form=opt-slice-mut`, adapter
/// `prior-family-rendering:<stage>`), licensed at reconciliation by its
/// terminal partner (`Reclassified`, `additive-family-fallback:…`). When the
/// whole program then degrades (`RewriteOutcome::degraded`: lodepng's and
/// brotli's revert loops exhausted on wave-6v's missing raw twins), every
/// terminal is rewritten to `Dropped` / `ProgramDegradedUnmodifiedInput` — the
/// license vanishes while the row still carries both forms, and the census
/// worker aborts on `slice-use specialized/common drift … :plan`. The retired
/// identity is the row's, not the partner's state: a degraded partner
/// licenses it too.
#[test]
fn wave6s_retired_slice_use_row_survives_program_degradation() {
    use super::mechanical_receipt::{MechanicalStage, MechanicalState, MechanicalTerminalReason};
    let input = "#![allow(dead_code, unused_unsafe)]\n\
        pub unsafe fn target(p: *const i32) -> i32 {\n\
            let q: *const i32 = p; *p.offset(1) + *q\n\
        }\n";
    let table = ::utils::compilation::run_compiler_on_str(input, |tcx| {
        super::decide_table(tcx).expect("retired-candidate table")
    })
    .expect("fixture compiles");
    let retired = table
        .slice_use_receipts
        .iter()
        .find(|plan| plan.obligation.intended_terminal_state == MechanicalState::Reclassified)
        .expect("an R220-retired slice-use candidate");
    assert_ne!(retired.source_form, retired.candidate_form, "{retired:?}");
    let (mut events, mut rows) = retired.materialize(false, false);
    super::mechanical_receipt::reconcile_slice_use_rows(&rows, &events)
        .expect("the retired partner licenses the row");
    // `RewriteOutcome::degraded` (bo_rewriter/mod.rs): every terminal event
    // and row drops with the program.
    for event in &mut events {
        if event.stage == MechanicalStage::Terminal {
            event.state = MechanicalState::Dropped;
            event.terminal_reason = Some(MechanicalTerminalReason::ProgramDegradedUnmodifiedInput);
        }
    }
    for row in &mut rows {
        row.terminal_class_state = MechanicalState::Dropped;
        if row.terminal.stage == MechanicalStage::Terminal {
            row.terminal.state = MechanicalState::Dropped;
            row.terminal.reason = Some(MechanicalTerminalReason::ProgramDegradedUnmodifiedInput);
        }
    }
    super::mechanical_receipt::reconcile_slice_use_rows(&rows, &events)
        .expect("a degraded partner still licenses the retired row");
}

/// The lodepng shape verbatim (`addChunk_IHDR` with `lodepng_chunk_init`,
/// `ucvector_resize`/`reserve`, `lodepng_memcpy`, `lodepng_set32bitInt`,
/// `lodepng_chunk_generate_crc`; `benchmarks/rs-crown-derived/lodepng`):
/// `data = chunk.offset(8)` then `lodepng_set32bitInt(data.offset(0), w)` —
/// the census's `class=563:subject=local:563:9:…:callee=def-id:0:329:arg=0`
/// is this reduction's `subject=local:9 … arg=0` (the HIR item-local id 114
/// coincides). The program degrades in the reduction as in the corpus, and
/// the census's reconciliation must then hold rather than abort the worker.
#[test]
fn wave6s_lodepng_addchunk_ihdr_reduction_reconciles_after_degradation() {
    let input = include_str!("testdata/wave6s-drift/lodepng-addchunk-ihdr.rs");
    let outcome = super::rewrite_core_injected(
        ::utils::compilation::str_to_input(input),
        None,
        super::MAX_REVERT_ROUNDS,
        &|_| {},
        false,
        true,
        true,
        Some((
            super::A5Mode::PreciseReplay,
            Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
        )),
    );
    let artifacts = match &outcome {
        super::RewriteOutcome::Emitted {
            raw_boundary_artifacts,
            ..
        }
        | super::RewriteOutcome::Degraded {
            raw_boundary_artifacts,
            ..
        } => raw_boundary_artifacts,
    };
    // **Restated for both frames (R217-2(a), under R465-5).** What this test
    // is about is the invariant after it: a retired row of a DEGRADED program
    // still reconciles. Which retirement produced the row is frame-dependent
    // and was never the point:
    //
    // * **before R465-5** — `addChunk_IHDR::data`'s carrier was built from the
    //   base's raw form, the Option presentation at that class was dropped
    //   `option-evidence-held`, and the slice-use family fell back behind it,
    //   so the row carried a `prior-family-rendering:` adapter and a candidate
    //   form that differed from its source.
    // * **after R465-5** — the carrier takes the base's decided form, the
    //   class is not dropped, and the same two sites (`hir:…:96`, `…:114`)
    //   carry `source_form == candidate_form == "opt-slice-mut"` with the
    //   program's own degradation as the only retirement.
    let retired_after_degradation = artifacts.slice_use_rows.iter().any(|row| {
        row.terminal.reason
            == Some(
                super::mechanical_receipt::MechanicalTerminalReason::ProgramDegradedUnmodifiedInput,
            )
            && (
                // the pre-R465-5 rendering
                (row.adapter.starts_with("prior-family-rendering:")
                    && row.source_form != row.candidate_form)
                // the R465-5 rendering: the option-presented base on both sides
                || (row.source_form == "opt-slice-mut" && row.candidate_form == "opt-slice-mut")
            )
    });
    assert!(
        retired_after_degradation,
        "the reduction must carry a retired row of a degraded program: {:?}",
        artifacts.slice_use_rows
    );
    super::mechanical_receipt::reconcile_slice_use_rows(
        &artifacts.slice_use_rows,
        &artifacts.mechanical_events,
    )
    .expect("slice-use receipt reconciliation");
}

/// **Relay 013 §3 — tulipindicators `ti_trima::inputs` → `ti_sma::inputs`.**
/// The bare pass-on of a depth-2 parameter's OUTER slot (`inputs: &[*const
/// f64]`, same form on both sides, raw element on both sides) had no carrier
/// (`slice-use-existing-c-interface-carrier-unmapped:candidates=0`): the
/// same-slice carrier (wave-5c W-C1) looked for the source and the parameter
/// at `ptr_depth == 1` only, the site dropped `slice-use-evidence-held`, and
/// the exclusion re-derivation withdrew `ti_sma`'s family with it (its
/// cursor `input` among the losses — slicecursor 015). The carrier now reads
/// the plan's own slot depth and requires every deeper slot to agree. Verbatim
/// `ti_sma` / `ti_trima` (+ their `_start`) from `benchmarks/rs-crown-derived/
/// tulipindicators`.
#[test]
fn wave6s_ti_trima_outer_slot_pass_on_delivers_and_returns_ti_sma_s_cursor() {
    let input = include_str!("testdata/wave6s-drift/tulip-trima-sma.rs");
    let (source, receipts) = emit_with_family_receipts(input);
    println!("EMITTED {source}");
    println!("FAMILY RECEIPTS {receipts}");
    assert!(super::verify::type_checks_str(&source), "{source}");
    let flat: String = source.chars().filter(|c| !c.is_whitespace()).collect();
    assert!(
        flat.contains("fnti_trima(mutsize:std::os::raw::c_int,mutinputs:&[*conststd::os::raw::c_double],mutoptions:&[std::os::raw::c_double],"),
        "{source}"
    );
    assert!(
        flat.contains("fnti_sma(mutsize:std::os::raw::c_int,mutinputs:&[*conststd::os::raw::c_double],mutoptions:&[std::os::raw::c_double],"),
        "{source}"
    );
    assert!(
        flat.contains("returnti_sma(size,inputs,options,outputs)"),
        "{source}"
    );
    assert_eq!(receipts.trim(), "[]", "no family withdrawal: {receipts}");
}

/// **The deref-rooted computed view has no base yet (relay 023).** lodepng
/// `lodepng_chunk_append` assigns `chunk_start = &mut *(*out).offset(e) as
/// *mut c_uchar` — this family's computed-view shape whose BASE is a deref of
/// a depth-2 parameter. Two walls stand before the view rule, and this control
/// pins both so the ordering is visible when either moves: the base `out` is
/// `kind-raw` (an inner slot delivers only once the nested family promotes it)
/// and the destination `chunk_start` is THIS family's `slice-use-unsupported`
/// (R217-2(a): the batch-8 frame read `null-init` here; at the landed batch-10
/// frame wave-6o's declaration family types the null-initialized destination,
/// so the only wall left at this row is the view — and W6S-7's admission does
/// not reach it, because a deref of a depth-2 parameter is not a binding and
/// carries no subject to render the view).
/// Where the base is raw the construction family already delivers a
/// destination of this shape with the §77 fallback extent
/// (`from_raw_parts_mut(&mut *(*out).offset(2) as *mut u8,
/// crate::FALLBACK_SLICE_EXTENT)`), so this lane's arm would change the
/// EXTENT, not the delivery — and only with a delivered base.
#[test]
fn wave6s_deref_rooted_view_base_and_destination_are_other_families() {
    let input = include_str!("testdata/wave6s-drift/lodepng-chunk-append.rs");
    let rows = super::emit_tests::decisions_of(input);
    let reason = |name: &str| {
        rows.iter()
            .rev()
            .find(|(row, _, _)| row == name)
            .map(|(_, _, reason)| reason.clone())
            .unwrap_or_else(|| panic!("{name}: {rows:?}"))
    };
    assert_eq!(reason("out"), "kind-raw", "{rows:?}");
    assert_eq!(reason("chunk_start"), "slice-use-unsupported", "{rows:?}");
    // The same shape with a raw base: the construction family delivers it with
    // the named fallback extent, which is what an evidence-backed base would
    // replace. **R217-2(a) — the spelling of that delivery is frame-dependent
    // and the assertion below is not.** At `046482b8e` the base kept the
    // C2Rust reborrow (`from_raw_parts_mut(&mut *(*out).offset(2) as *mut u8,
    // crate::FALLBACK_SLICE_EXTENT)`); on the composed frame
    // (`batch-14-dry17d`) the reborrow is gone and the base is passed bare
    // (`from_raw_parts_mut((*out).offset(2 as i32 as isize),
    // crate::FALLBACK_SLICE_EXTENT)`). What both frames say — and what this
    // control exists to pin — is that the destination of the deref-rooted
    // shape is delivered by the CONSTRUCTION family, off this same base, at
    // the named fallback extent, and never by this lane's view.
    let fabricated = emit(
        r#"
 #![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
 pub unsafe fn copy(mut out: *mut *mut u8, mut src: *const u8, mut n: usize) {
    let mut start: *mut u8 = &mut *(*out).offset(2 as i32 as isize) as *mut u8;
    let mut i: usize = 0;
    while i < n { *start.offset(i as isize) = *src.offset(i as isize); i = i.wrapping_add(1); }
 }
"#,
    );
    assert!(super::verify::type_checks_str(&fabricated), "{fabricated}");
    let flat: String = fabricated.chars().filter(|c| !c.is_whitespace()).collect();
    assert!(flat.contains("from_raw_parts_mut("), "{fabricated}");
    assert!(
        flat.contains("(*out).offset(2asi32asisize)"),
        "{fabricated}"
    );
    assert!(
        flat.contains("crate::FALLBACK_SLICE_EXTENT"),
        "{fabricated}"
    );
}

// ---------------------------------------------------------------------------
// W6S-7 — the Option-slice destination of a forward computed view
//
// `let mut p = 0 as *mut T; … p = &mut *src.offset(e) as *mut T;` is this
// lane's computed view landing in a null-initialized destination, whose form
// is `Option<&[T]>`. Two pieces:
//
//   (i)  the destination's own use walk admits the assignment — the right-hand
//        side is the view's to render, not the destination's. The structural
//        walk is wave-6s2's (W6S2-5); the DELTA authority is this lane's
//        width-aware `forward_delta`, which admits the C2Rust double-cast
//        literal (`2 as i32 as isize`) their narrower rule refuses.
//   (ii) the `Decision::Opt { slice: true }` destination renders the same
//        suffix the `Decision::Slice` destination already renders; the
//        `Some(..)` belongs to the Option family's value planner.
//
// Measured state after (i) and (ii): the wall MOVES from this family to the
// Option family. The destination's reason becomes `null-init`, the Option
// family's candidate for it is `raw -> opt-slice-shared`, and the stage is
// withdrawn by ONE named hold — wave-6o's R410-7 STOP 1(b)
// `option-slice-value:one-element-carrier`, which refuses the one-element
// `from_ref` carrier "until the base delivers a real view". This lane now
// delivers that view; what the hold still does not see is the composition —
// `construction::collect_composable_edits` at the value planner's view span
// returns empty for this edit. That last link is wave-6o's (report 021 STOP 1).
// ---------------------------------------------------------------------------

/// **W6S-7 (i)+(ii) — the destination leaves this family.** Before the arm it
/// was this family's `slice-use-unsupported`; after it, the assignment is
/// admitted and the row belongs to the Option family.
///
/// **R217-2(a) — what the Option family then does with it is frame-dependent,
/// and this witness asserts only the part that is not.** At `046482b8e` the
/// row stopped at ONE named hold — candidate `raw -> opt-slice-shared`,
/// withdrawn on `option-presentation:
/// EvidenceMissing("option-slice-value:one-element-carrier")` (wave-6o's
/// R410-7 STOP 1(b), which holds "until the base delivers a real view"). On
/// the composed frame (`batch-14-dry17d`, with wave-6o's option 1) the hold is
/// discharged by exactly this lane's view and the row DELIVERS:
///
/// ```text
/// let mut p: Option<&[f32]> = None;
/// p = Some(&src[2..]);
/// return p.unwrap()[(0 as i32) as usize] + p.unwrap()[(1 as i32) as usize];
/// ```
///
/// The shared property is the arm's own claim: the destination is never left
/// with this family's refusal, and whichever frame it is read on, the outcome
/// is one of those two — the named hold, or the optional suffix view.
#[test]
fn wave6s_forward_view_into_a_null_initialized_destination_moves_to_the_option_family() {
    const INPUT: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
 pub unsafe extern "C" fn diag(mut src: *mut f32, mut n: i32) -> f32 {
    let mut p: *mut f32 = 0 as *mut f32;
    p = &mut *src.offset(2 as i32 as isize) as *mut f32;
    return *p.offset(0 as i32 as isize) + *p.offset(1 as i32 as isize);
 }
"#;
    let rows = super::emit_tests::decisions_of(INPUT);
    let reason = rows
        .iter()
        .rev()
        .find(|(name, is_param, _)| name == "p" && !is_param)
        .map(|(_, _, reason)| reason.clone())
        .unwrap_or_else(|| panic!("{rows:?}"));
    assert_ne!(reason, "slice-use-unsupported", "{rows:?}");
    if reason == "<emitted>" {
        // The composed frame: the hold is discharged and the view is placed.
        let source = emit(INPUT);
        assert!(super::verify::type_checks_str(&source), "{source}");
        let flat: String = source.chars().filter(|c| !c.is_whitespace()).collect();
        assert!(flat.contains("letmutp:Option<&[f32]>=None"), "{source}");
        assert!(flat.contains("p=Some(&src[2..])"), "{source}");
        return;
    }
    assert_eq!(reason, "null-init", "{rows:?}");
    let (_, receipts) = emit_with_family_receipts(INPUT);
    assert!(
        receipts.contains("opt-slice-shared"),
        "the Option family must carry this destination as an optional slice candidate: {receipts}"
    );
    assert!(
        receipts.contains("option-presentation") && receipts.contains("option-evidence-held"),
        "and its withdrawal must be the named presentation hold: {receipts}"
    );
}

/// **The bare copy is unchanged.** The same destination whose value is the
/// root itself still delivers `Option<&[f32]>` — the admission is additive.
#[test]
fn wave6s_bare_copy_into_a_null_initialized_destination_still_delivers() {
    let source = emit(
        r#"
 #![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
 pub unsafe extern "C" fn diag(mut src: *mut f32, mut n: i32) -> f32 {
    let mut p: *mut f32 = 0 as *mut f32;
    p = src;
    return *p.offset(0 as i32 as isize) + *p.offset(1 as i32 as isize);
 }
"#,
    );
    assert!(super::verify::type_checks_str(&source), "{source}");
    let flat: String = source.chars().filter(|c| !c.is_whitespace()).collect();
    assert!(flat.contains("letmutp:Option<&[f32]>=None"), "{source}");
}

/// **FAULT — a BACKWARD delta is never this arm's.** The sign authority is one
/// and the same; a view that can move the root backwards belongs to the
/// bidirectional family, and the destination keeps the cursor rendering.
///
/// The emission of this shape does NOT type-check at this frame
/// (`E0596: cannot borrow data in a *const pointer as mutable`, from the
/// cursor's `&mut *src.offset_by(..).addr()` inside the optional value) —
/// measured identical with and without this arm, so it is pinned as
/// pre-existing and reported rather than asserted away (report 021 STOP 2).
#[test]
fn wave6s_option_slice_destination_refuses_a_backward_view() {
    let source = emit(
        r#"
 #![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
 pub unsafe extern "C" fn diag(mut src: *mut f32, mut n: i32) -> f32 {
    let mut p: *mut f32 = 0 as *mut f32;
    p = &mut *src.offset(-(2 as i32) as isize) as *mut f32;
    return *p.offset(0 as i32 as isize) + *p.offset(1 as i32 as isize);
 }
"#,
    );
    assert!(source.contains("SliceCursor::new"), "{source}");
    let flat: String = source.chars().filter(|c| !c.is_whitespace()).collect();
    assert!(!flat.contains("Some(&(src)["), "{source}");
    assert!(!flat.contains("Some(&mut(src)["), "{source}");
}

/// **FAULT — a different pointee keeps the wall.** The view's element type is
/// the destination's; a cast that changes it is a reinterpretation, which is
/// the void-region family's evidence to supply, not this arm's.
#[test]
fn wave6s_option_slice_destination_refuses_a_retyped_view() {
    let rows = super::emit_tests::decisions_of(
        r#"
 #![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
 pub unsafe extern "C" fn diag(mut src: *mut u32, mut n: i32) -> u8 {
    let mut p: *mut u8 = 0 as *mut u8;
    p = src.offset(2 as i32 as isize) as *mut u8;
    return *p.offset(0 as i32 as isize);
 }
"#,
    );
    let p = rows
        .iter()
        .rev()
        .find(|(name, is_param, _)| name == "p" && !is_param)
        .unwrap_or_else(|| panic!("{rows:?}"));
    assert_ne!(p.2, "<emitted>", "{rows:?}");
}

/// **CONTROL — an ARRAY LOCAL as the view's root is not admitted.** heman
/// `kazmath::quaternion::kmQuaternionRotationMatrix`'s `pMatrix` takes its
/// view off the function's own `[f32; 16]` (`&mut *m4x4.as_mut_ptr().offset(0)
/// as *mut c_float`), which is not a pointer binding, so it carries no subject
/// and no view: the row stays this family's. The boundary is pinned here so it
/// is visible when the array-local root is built (report 021 §3).
#[test]
fn wave6s_array_local_root_is_not_yet_a_view_root() {
    let input = include_str!("testdata/wave6s-drift/heman-quaternion-rotation-matrix.rs");
    let rows = super::emit_tests::decisions_of(input);
    let reason = rows
        .iter()
        .rev()
        .find(|(name, is_param, _)| name == "pMatrix" && !is_param)
        .map(|(_, _, reason)| reason.clone())
        .unwrap_or_else(|| panic!("{rows:?}"));
    assert_eq!(reason, "slice-use-unsupported", "{rows:?}");
}

/// **The doubled view (R475-3), as a REPRODUCTION rather than a guess.**
///
/// brotli emits `(histograms[(i) as usize].data_).as_ptr().as_ptr()` for the input
/// `&*((*histograms.offset(i)).data_).as_ptr().offset(0)` — `data_` is a fixed array, so
/// the FIRST `as_ptr()` is c2rust's own decay and is correct; a second one lands on the
/// `*const u32` it produced. This is the smallest shape that carries all three features:
/// a delivered slice parameter, indexed; a fixed-array field on the element; and the
/// W-C6 `&*….as_ptr().offset(0)` idiom over that field.
#[test]
fn r475_3_the_doubled_view_reproduced() {
    let source = emit(DOUBLED_VIEW);
    println!("EMITTED {source}");
    // The defect is not one spelling: brotli renders `.as_ptr().as_ptr()` and this
    // fixture `.as_ptr().as_mut_ptr().cast::<u32>().cast_const()`. The PROPERTY is a
    // raw-producing view applied to a receiver that already produced a raw pointer --
    // the W-C6 operand `(place).as_ptr()` is `*const u32` before anything is appended.
    for doubled in [
        ".as_ptr().as_ptr()",
        ".as_ptr().as_mut_ptr()",
        ".as_mut_ptr().as_ptr()",
        ".as_mut_ptr().as_mut_ptr()",
    ] {
        assert!(
            !source.contains(doubled),
            "a view was emitted over a receiver that had already produced one \
             ({doubled}):\n{source}"
        );
    }
}

const DOUBLED_VIEW: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables)]
 #[derive(Copy, Clone)]
 #[repr(C)]
 pub struct Histogram { pub data_: [u32; 4], pub total_: usize }
 unsafe extern "C" {
    // FOREIGN: the position can never be delivered, so `expected` stays Raw and the
    // bridge must go slice -> raw. That is brotli's direction; a local callee converts
    // and the bridge goes the other way, which is why the first fixture missed.
    fn consume(counts: *const u32, n: usize) -> u32;
 }
 pub unsafe fn drive(mut histograms: *mut Histogram, n: usize) -> u32 {
    let mut total: u32 = 0;
    let mut i: usize = 0;
    while i < n {
        total = total.wrapping_add(consume(
            &*((*histograms.offset(i as isize)).data_).as_ptr().offset(0 as isize),
            4,
        ));
        i = i.wrapping_add(1);
    }
    return total;
 }
"#;

/// **`offset_from` (R475-3)** — brotli's `EmitUncompressedMetaBlock` delivers
/// `end: &uint8_t` and keeps `end.offset_from(begin)` verbatim in the body, which is
/// `E0599`: `offset_from` is a raw-pointer method. Every other arithmetic use in the
/// corpus is `offset`/`add`, which the use-rewrite carries; `offset_from` reads a PAIR of
/// pointers and is the one shape it does not.
#[test]
fn r475_3_offset_from_on_delivered_references() {
    let source = emit(OFFSET_FROM);
    println!("EMITTED {source}");
    // The R130 bridge at a use: a delivered reference reaches `offset_from` through
    // `core::ptr::from_ref`. The defect is a use left BARE on a delivered receiver, not
    // the presence of `offset_from` -- the bridged form contains it too.
    for bad in ["end.offset_from(", "begin.offset_from("] {
        assert!(
            !source.contains(bad),
            "a delivered reference kept a bare raw-pointer `offset_from` use ({bad}):\n{source}"
        );
    }
    assert!(
        source.contains("core::ptr::from_ref(end).offset_from("),
        "the use must bridge through from_ref:\n{source}"
    );
}

/// The ASYMMETRIC shape, which is brotli's: one end delivered, the other kept raw by a
/// second caller that does arithmetic on it. If the bridge only fires when BOTH sides
/// convert, this is the one that stays bare.
/// **RED-first, preserved and `#[ignore]`d until the fix is built** — this is the shape
/// brotli has, and it fails today. It is ignored rather than deleted so the fix has its
/// witness already written, and ignored rather than left red so it adds nothing to the
/// standing set.
#[test]
#[ignore = "R475-3: the receiver bridge does not fire when only one side is delivered; fix owed"]
fn r475_3_offset_from_with_one_side_still_raw() {
    let source = emit(OFFSET_FROM_ASYMMETRIC);
    println!("EMITTED {source}");
    for bad in ["end.offset_from(", "begin.offset_from("] {
        assert!(
            !source.contains(bad),
            "a delivered reference kept a bare `offset_from` ({bad}):\n{source}"
        );
    }
}

const OFFSET_FROM_ASYMMETRIC: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables)]
 unsafe extern "C" {
    fn sink(p: *const u8, n: usize);
 }
 pub unsafe fn span_len2(mut begin: *const u8, mut end: *const u8) -> usize {
    let len = end.offset_from(begin) as usize;
    sink(begin.offset(1), len);
    return len;
 }
"#;

const OFFSET_FROM: &str = r#"
 #![allow(dead_code, unused_mut, unused_variables)]
 unsafe extern "C" {
    fn sink(p: *const u8, n: usize);
 }
 pub unsafe fn span_len(mut begin: *const u8, mut end: *const u8) -> usize {
    let len = end.offset_from(begin) as usize;
    sink(begin, len);
    return len;
 }
"#;
