//! **R738-1 (brotli at L01¹²) — a call routed to the raw twin takes the input's
//! arguments at every position.** brotli's `SafeReadSymbolCodeLengths` calls
//! `ProcessSingleCodeLength(code_len, &mut (*h).symbol, …, (*h).symbol_lists,
//! ((*h).code_length_histo).as_mut_ptr(), ((*h).next_symbol).as_mut_ptr())`: a
//! converted position shares the root `h` with a raw argument, so the seam routes
//! the call to the pristine raw twin and renders zero syntax at every position.
//! The interface-inventory arm (R466-6) then bridged the two slice-formal
//! positions anyway, and the twin received `from_raw_parts_mut(..)` where its
//! formal is `*mut u16` (E0308 ×2, the class reverted: 296 rows at L01¹²).
//! Driven from a file, as the census is.

const SHAPE: &str = "#![allow(dead_code, non_snake_case, unused_mut, unused_assignments)]\n\
pub mod decode {\n\
    #[repr(C)]\n\
    pub struct Arena {\n\
        pub symbol: u32,\n\
        pub repeat: u32,\n\
        pub space: u32,\n\
        pub prev_code_len: u32,\n\
        pub symbol_lists: *mut u16,\n\
        pub next_symbol: [i32; 32],\n\
        pub code_length_histo: [u16; 16],\n\
    }\n\
    #[repr(C)]\n\
    pub struct State {\n\
        pub header: Arena,\n\
    }\n\
    #[inline(always)]\n\
    unsafe extern \"C\" fn ProcessSingleCodeLength(mut code_len: u32, mut symbol: *mut u32,\n\
        mut repeat: *mut u32, mut space: *mut u32, mut prev_code_len: *mut u32,\n\
        mut symbol_lists: *mut u16, mut code_length_histo: *mut u16, mut next_symbol: *mut i32) {\n\
        *repeat = 0 as u32;\n\
        if code_len != 0 as u32 {\n\
            *symbol_lists.offset(*next_symbol.offset(code_len as isize) as isize) = *symbol as u16;\n\
            *next_symbol.offset(code_len as isize) = *symbol as i32;\n\
            *prev_code_len = code_len;\n\
            *space = (*space).wrapping_sub(32768 as u32 >> code_len);\n\
            *code_length_histo.offset(code_len as isize) =\n\
                (*code_length_histo.offset(code_len as isize)).wrapping_add(1);\n\
        }\n\
        *symbol = (*symbol).wrapping_add(1);\n\
    }\n\
    unsafe extern \"C\" fn ReadSymbolCodeLengths(mut s: *mut State, mut code_len: u32) -> i32 {\n\
        let mut h: *mut Arena = &mut (*s).header;\n\
        let mut symbol = (*h).symbol;\n\
        let mut repeat = (*h).repeat;\n\
        let mut space = (*h).space;\n\
        let mut prev_code_len = (*h).prev_code_len;\n\
        let mut symbol_lists = (*h).symbol_lists;\n\
        let mut code_length_histo = ((*h).code_length_histo).as_mut_ptr();\n\
        let mut next_symbol = ((*h).next_symbol).as_mut_ptr();\n\
        ProcessSingleCodeLength(code_len, &mut symbol, &mut repeat, &mut space,\n\
            &mut prev_code_len, symbol_lists, code_length_histo, next_symbol);\n\
        (*h).symbol = symbol;\n\
        (*h).repeat = repeat;\n\
        (*h).space = space;\n\
        (*h).prev_code_len = prev_code_len;\n\
        0\n\
    }\n\
    unsafe extern \"C\" fn SafeReadSymbolCodeLengths(mut s: *mut State, mut code_len: u32) -> i32 {\n\
        let mut h: *mut Arena = &mut (*s).header;\n\
        ProcessSingleCodeLength(code_len, &mut (*h).symbol, &mut (*h).repeat,\n\
            &mut (*h).space, &mut (*h).prev_code_len, (*h).symbol_lists,\n\
            ((*h).code_length_histo).as_mut_ptr(), ((*h).next_symbol).as_mut_ptr());\n\
        0\n\
    }\n\
    #[no_mangle]\n\
    pub unsafe extern \"C\" fn entry(mut s: *mut State, mut c: u32) -> i32 {\n\
        ReadSymbolCodeLengths(s, c) + SafeReadSymbolCodeLengths(s, c)\n\
    }\n\
}\n";

fn emitted(source: &str, tag: &str) -> (String, usize) {
    let dir = std::env::temp_dir().join(format!("crat-r738-{tag}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let root = dir.join("lib.rs");
    std::fs::write(&root, source).unwrap();
    // The census's A5 configuration (precise replay over the frozen graph).
    let outcome = super::rewrite_m1_path_a5_injected(
        &root,
        super::A5Mode::PreciseReplay,
        Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
        &|_| {},
    );
    std::fs::remove_dir_all(dir).unwrap();
    match outcome {
        super::RewriteOutcome::Emitted {
            source,
            reverted_count,
            ..
        } => (source, reverted_count),
        super::RewriteOutcome::Degraded { reason, .. } => panic!("degraded: {reason}"),
    }
}

#[test]
fn r738_1_a_raw_twin_call_takes_the_original_arguments() {
    let (source, reverted) = emitted(SHAPE, "twin");
    let flat = source.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(
        flat.contains("__crat_raw_ProcessSingleCodeLength("),
        "the aliased call is routed to the raw twin:\n{source}"
    );
    assert!(
        flat.contains("((*h).code_length_histo).as_mut_ptr(), ((*h).next_symbol).as_mut_ptr())"),
        "the twin takes the input's arguments:\n{source}"
    );
    assert_eq!(reverted, 0, "{source}");
    // Control: the other caller's call to the same callee is not the twin's,
    // so its slice positions keep their bridges.
    assert!(
        flat.contains("ProcessSingleCodeLength(code_len, &mut symbol,")
            && flat.contains("core::slice::from_raw_parts_mut(code_length_histo,"),
        "a call not routed to the twin keeps its bridges:\n{source}"
    );
}

/// **R738-1 (ii) — a computed view borrowed mutably stays mutable when its
/// raw-boundary bridge reads it mutably.** brotli's `SortHuffmanTreeItems`
/// passes `&mut *items.offset(j)` (items a delivered `&mut [HuffmanTree]`) to a
/// comparator taking `*const HuffmanTree`. The computed sub-view took the
/// TARGET's mutability (`&(items)[j..]`) while the terminal sealing picked the
/// writable view `{view}.as_mut_ptr().cast::<T>().cast_const()`: E0596 ×4 at
/// L01¹². The view follows the input's borrow when the base is mutable.
const SORT: &str = "#![allow(dead_code, non_snake_case, unused_mut, unused_assignments)]\n\
pub mod entropy_encode {\n\
    #[derive(Copy, Clone)]\n\
    #[repr(C)]\n\
    pub struct HuffmanTree {\n\
        pub total_count_: u32,\n\
        pub index_left_: i16,\n\
        pub index_right_or_value_: i16,\n\
    }\n\
    pub type HuffmanTreeComparator =\n\
        Option<unsafe extern \"C\" fn(*const HuffmanTree, *const HuffmanTree) -> i32>;\n\
    #[inline]\n\
    unsafe extern \"C\" fn SortHuffmanTreeItems(mut items: *mut HuffmanTree, n: usize,\n\
        mut comparator: HuffmanTreeComparator) {\n\
        let mut i: usize = 1;\n\
        while i < n {\n\
            let mut tmp = *items.offset(i as isize);\n\
            let mut k = i;\n\
            let mut j = i.wrapping_sub(1);\n\
            while comparator.expect(\"non-null function pointer\")(&mut tmp,\n\
                    &mut *items.offset(j as isize)) != 0 {\n\
                *items.offset(k as isize) = *items.offset(j as isize);\n\
                k = j;\n\
                let fresh0 = j;\n\
                j = j.wrapping_sub(1);\n\
                if fresh0 == 0 { break; }\n\
            }\n\
            *items.offset(k as isize) = tmp;\n\
            i = i.wrapping_add(1);\n\
        }\n\
    }\n\
    unsafe extern \"C\" fn SortHuffmanTree(mut v0: *const HuffmanTree, mut v1: *const HuffmanTree) -> i32 {\n\
        ((*v0).total_count_ < (*v1).total_count_) as i32\n\
    }\n\
    #[no_mangle]\n\
    pub unsafe extern \"C\" fn BrotliCreateHuffmanTree(mut tree: *mut HuffmanTree, n: usize) {\n\
        let cmp = Some(SortHuffmanTree as unsafe extern \"C\" fn(*const HuffmanTree, *const HuffmanTree) -> i32);\n\
        SortHuffmanTreeItems(tree, n, cmp);\n\
    }\n\
}\n";

#[test]
fn r738_1_a_mutably_borrowed_computed_view_stays_mutable_under_a_writable_bridge() {
    let (source, reverted) = emitted(SORT, "sort");
    let flat = source.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(
        flat.contains("fn SortHuffmanTreeItems(mut items: &mut [HuffmanTree],"),
        "the sorted items are delivered as a mutable slice:\n{source}"
    );
    assert!(
        flat.contains("(&mut (items)[j..])") && !flat.contains("(&(items)[j..]).as_mut_ptr()"),
        "the input's `&mut *items.offset(j)` keeps a mutable view:\n{source}"
    );
    assert_eq!(reverted, 0, "{source}");
}

/// **R761-2 (main 146 STOP 2 (ii)) — the receipt follows the call that is
/// emitted.** heman's `kmVec3Add(pOut, pOut, &mut uuv)`: the callee's `pOut`
/// is delivered `&mut`, the caller's stays raw, so the second `pOut` aliases
/// the first and the call is routed to the raw twin with the input's own
/// arguments. R499-1 discharged the A5 pair's T2 fallback at `arg1` as
/// zero-syntax, and it was receipted `applied`, but nothing bridges there:
/// raw `pOut` into a raw formal (`outbound-input-form`). Two such receipts were
/// over-issued at frame 13 (`459:322`, `460:263`). They are withdrawn.
const HEMAN_TWIN: &str = "#![allow(dead_code, mutable_transmutes, non_camel_case_types, non_snake_case, non_upper_case_globals, unused_assignments, unused_mut)]\n\
pub mod src {\n\
    pub mod kazmath {\n\
        pub mod vec3 {\n\
            #[derive(Copy, Clone)]\n\
            #[repr(C)]\n\
            pub struct kmVec3 {\n\
                pub x: f32,\n\
                pub y: f32,\n\
                pub z: f32,\n\
            }\n\
            #[no_mangle]\n\
            pub unsafe extern \"C\" fn kmVec3Add(mut pOut: *mut kmVec3, mut pV1: *const kmVec3,\n\
                mut pV2: *const kmVec3) -> *mut kmVec3 {\n\
                let mut v = kmVec3 { x: 0., y: 0., z: 0. };\n\
                v.x = (*pV1).x + (*pV2).x;\n\
                v.y = (*pV1).y + (*pV2).y;\n\
                v.z = (*pV1).z + (*pV2).z;\n\
                (*pOut).x = v.x;\n\
                (*pOut).y = v.y;\n\
                (*pOut).z = v.z;\n\
                return pOut;\n\
            }\n\
        }\n\
        pub mod quaternion {\n\
            #[no_mangle]\n\
            pub unsafe extern \"C\" fn kmQuaternionMultiplyVec3(\n\
                mut pOut: *mut crate::src::kazmath::vec3::kmVec3,\n\
                mut v: *const crate::src::kazmath::vec3::kmVec3,\n\
            ) -> *mut crate::src::kazmath::vec3::kmVec3 {\n\
                let mut uv = crate::src::kazmath::vec3::kmVec3 { x: 0., y: 0., z: 0. };\n\
                let mut uuv = crate::src::kazmath::vec3::kmVec3 { x: 1., y: 1., z: 1. };\n\
                crate::src::kazmath::vec3::kmVec3Add(pOut, v, &mut uv);\n\
                crate::src::kazmath::vec3::kmVec3Add(pOut, pOut, &mut uuv);\n\
                return pOut;\n\
            }\n\
        }\n\
    }\n\
}\n\
";

#[test]
fn r761_2_a_raw_twin_position_with_nothing_to_bridge_issues_no_a5_receipt() {
    let dir = std::env::temp_dir().join(format!("crat-r761-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let root = dir.join("lib.rs");
    std::fs::write(&root, HEMAN_TWIN).unwrap();
    let config = super::EmissionRunConfig {
        configured_exposure: super::decision::exposure::ConfiguredExposureInput::checked(
            "standing-raw-boundary-launch:Config::default.c_exposed_fns",
            Vec::new(),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        )
        .unwrap(),
    };
    let capture = super::rewrite_core_injected_with_config(
        ::utils::compilation::path_to_input(&root),
        Some(&root),
        super::MAX_REVERT_ROUNDS,
        &|_| {},
        false,
        true,
        false,
        Some((
            super::A5Mode::PreciseReplay,
            Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
        )),
        &config,
    )
    .into_e1_capture()
    .expect("the one-iteration capture");
    std::fs::remove_dir_all(dir).unwrap();
    let call = "kmVec3Add(pOut, pOut, &mut uuv)";
    let lo = HEMAN_TWIN.find(call).expect("the twin call") as u32;
    let hi = lo + call.len() as u32;
    let rows = capture
        .raw_boundary_artifacts
        .bridge_events
        .iter()
        .filter(|e| lo <= e.site.lo && e.site.hi <= hi)
        .map(|e| {
            format!(
                "{}:{}:{}:{:?}",
                e.site.arm, e.site.bridge_kind, e.site.position, e.state
            )
        })
        .collect::<Vec<_>>();
    assert!(
        rows.iter()
            .any(|r| r.starts_with("c:outbound-input-form:arg1:")),
        "the twin call passes the input's raw pOut at arg1: {rows:?}"
    );
    assert!(
        !rows
            .iter()
            .any(|r| r.starts_with("pair:a5-site-proof-t2-fallback:")),
        "nothing bridges at the twin's arg1, so no A5 receipt is issued: {rows:?}"
    );
}

/// **R761-2 — the keep / withdraw predicate, on frame 13's own rows.** brotli's
/// twin call (`556:559`) keeps its T2 receipts: each has a `c` conversion at
/// the same interval (`ref-mut-to-raw-mut`, `typed-raw-temporary`). heman's
/// (`459:322`) has only the input's own form beside it and is withdrawn, as is
/// a receipt with no sibling at all.
#[test]
fn r761_2_a_twin_position_keeps_its_receipt_only_where_the_call_still_bridges() {
    use super::bridge_receipt::{BridgeCalleeId, BridgeSiteKey, SignatureClassId};
    let did = |n: u32| rustc_span::def_id::LocalDefId {
        local_def_index: rustc_span::def_id::DefIndex::from_u32(n),
    };
    let key = |arm: &str, kind: &str, lo: u32, hi: u32| BridgeSiteKey {
        owner_class: SignatureClassId::of(did(559)),
        caller: did(556),
        callee: BridgeCalleeId::Local(did(559)),
        arm: arm.to_owned(),
        position: "arg2".to_owned(),
        file: "<program>/lib.rs".to_owned(),
        lo,
        hi,
        bridge_kind: kind.to_owned(),
    };
    let t2 = key("pair", "a5-site-proof-t2-fallback", 6925755, 6925771);
    let still = |siblings: Vec<BridgeSiteKey>| {
        let mut all = siblings;
        all.push(t2.clone());
        super::plan::twin_position_still_bridges(all.iter(), &t2)
    };
    // brotli: a conversion at the same interval keeps the receipt.
    assert!(still(vec![key(
        "c",
        "ref-mut-to-raw-mut",
        6925755,
        6925771
    )]));
    assert!(still(vec![key(
        "c",
        "typed-raw-temporary",
        6925755,
        6925771
    )]));
    // heman: the input's own raw argument, nothing bridges.
    assert!(!still(vec![key(
        "c",
        "outbound-input-form",
        6925755,
        6925771
    )]));
    // No sibling at all; a conversion at another interval does not count.
    assert!(!still(vec![]));
    assert!(!still(vec![key(
        "c",
        "ref-mut-to-raw-mut",
        6925773,
        6925788
    )]));
}
