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
    assert!(
        source.contains("let mut __crat_wave6s_pos_"),
        "forward parameter needs its index: {source}"
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
    // argument `mask` as the length — a bit mask, not an extent — which is
    // ruling B's pre-existing selection, recorded there as an observation.
    assert!(
        source.contains("StoreH2(self_0, core::slice::from_raw_parts(data, "),
        "{source}"
    );
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
    assert!(source.contains("data: *const u8"), "{source}");
    // A borrowed element bound to a local, not passed on.
    let bound = STOREH2.replace(
        "let key = HashBytesH2(&*data.offset((ix & mask) as isize));",
        "let r = &*data.offset((ix & mask) as isize); let key = HashBytesH2(r);",
    );
    let source = emit(&bound);
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(source.contains("data: *const u8"), "{source}");
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
    assert!(
        source.contains("HashBytesH2((&(data)[(ix & mask)..]).as_ptr())"),
        "the suffix view bridges at the raw callee: {source}"
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

#[test]
fn wave6s_strff_forward_parameter_pass_on() {
    let source = emit(STRFF);
    println!("EMITTED {source}");
    assert!(super::verify::type_checks_str(&source), "{source}");
    assert!(
        source.contains("ptr: &[i8]"),
        "forward parameter must deliver: {source}"
    );
    assert!(
        source.contains("let mut __crat_wave6s_pos_"),
        "forward parameter needs its index: {source}"
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
