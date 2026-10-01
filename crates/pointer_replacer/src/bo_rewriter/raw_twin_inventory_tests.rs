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
