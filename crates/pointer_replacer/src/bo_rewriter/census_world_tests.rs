//! R805-7 (relay 272): the census-world test entry. A reduced A5 shape that the
//! open world (`rewrite_m1`) cannot emit — `unowned A5 proof-site receipt
//! identities` — emits in the world every census runs in.

const ALLOW: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments, unused_variables, non_snake_case, non_camel_case_types)]\n";

/// brotli `BrotliClusterHistogramsCommand → BrotliHistogramCombineCommand`'s
/// call, reduced (main 164 §4): three pointer arguments of one element type,
/// two of them element addresses.
const CLUSTER: &str = r#"
extern "C" {
    fn malloc(n: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
pub unsafe fn combine(cluster_size: *mut u32, symbols: *mut u32, clusters: *mut u32, n: usize) -> usize {
    let mut i = 0usize;
    while i < n {
        *symbols.offset(i as isize) = *clusters.offset(i as isize);
        *cluster_size.offset(i as isize) = 1;
        i = i.wrapping_add(1);
    }
    n
}
pub unsafe fn cluster(in_size: usize, histogram_symbols: *mut u32) -> usize {
    let mut cluster_size = malloc(in_size.wrapping_mul(4)) as *mut u32;
    let mut clusters = malloc(in_size.wrapping_mul(4)) as *mut u32;
    let mut i = 0usize;
    while i < in_size {
        *histogram_symbols.offset(i as isize) = i as u32;
        *clusters.offset(i as isize) = i as u32;
        i = i.wrapping_add(1);
    }
    let mut total = 0usize;
    i = 0;
    while i < in_size {
        total = total.wrapping_add(combine(
            cluster_size,
            &mut *histogram_symbols.offset(i as isize),
            &mut *clusters.offset(i as isize),
            64,
        ));
        i = i.wrapping_add(64);
    }
    free(cluster_size as *mut core::ffi::c_void);
    free(clusters as *mut core::ffi::c_void);
    total
}
"#;

#[test]
fn r805_7_an_a5_shape_emits_in_the_census_world() {
    let input = format!("{ALLOW}{CLUSTER}");
    match super::rewrite_m1_census_world(&input) {
        super::RewriteOutcome::Emitted { source, .. } => {
            assert!(source.contains("pub unsafe fn combine("), "{source}");
        }
        other => panic!("the census world emits: {other:#?}"),
    }
}

// ---- era-5c 148 / relay 190 item 1: the census world's A5 reading of pairs loaded from
// ---- memory, executed (wave-5d 133 §3). A probe: it prints the pair table and the
// ---- callee's emitted signature for each shape; wave-5d takes it as its RED's
// ---- expectation. Run: `census_world_tests::e5c_148_ --ignored --nocapture`.

const E5C_148_ADD: &str = "unsafe fn add(a: *mut i32, b: *mut i32) { *a += *b; }\n";

fn e5c_148_probe(name: &str, body: &str) {
    let input = format!("{ALLOW}{E5C_148_ADD}{body}");
    match super::rewrite_m1_census_world(&input) {
        super::RewriteOutcome::Emitted {
            source,
            raw_boundary_artifacts,
            ..
        } => {
            let flat = source.split_whitespace().collect::<Vec<_>>().join(" ");
            let signature = flat
                .split("fn add(")
                .nth(1)
                .and_then(|rest| rest.split(')').next())
                .unwrap_or("<no add>");
            eprintln!("E5C148 {name} signature: add({signature})");
            for line in raw_boundary_artifacts.pairs.lines() {
                if line.starts_with("caller") || line.contains("add") {
                    eprintln!("E5C148 {name} pair: {line}");
                }
            }
        }
        other => eprintln!("E5C148 {name} outcome: {other:#?}"),
    }
}

#[test]
#[ignore = "era-5c 148 probe (relay 190 item 1)"]
fn e5c_148_one_static_passed_twice() {
    e5c_148_probe(
        "G1G1",
        "static mut G1: *mut i32 = 0 as *mut i32;\n\
         pub unsafe fn entry(p: *mut i32) { G1 = p; add(G1, G1); }\n",
    );
}

#[test]
#[ignore = "era-5c 148 probe (relay 190 item 1)"]
fn e5c_148_two_statics_one_stored_from_the_other() {
    e5c_148_probe(
        "G1G2",
        "static mut G1: *mut i32 = 0 as *mut i32;\n\
         static mut G2: *mut i32 = 0 as *mut i32;\n\
         pub unsafe fn set(p: *mut i32) { G1 = p; G2 = G1; }\n\
         pub unsafe fn entry() { add(G1, G2); }\n",
    );
}

#[test]
#[ignore = "era-5c 148 probe (relay 190 item 1)"]
fn e5c_148_two_pointees_of_one_pointer() {
    e5c_148_probe(
        "PQ",
        "unsafe fn pair(p: *mut *mut i32, q: *mut *mut i32) { add(*p, *q); }\n\
         pub unsafe fn entry(x: *mut *mut i32) { pair(x, x); }\n",
    );
}

#[test]
#[ignore = "era-5c 148 probe (relay 190 item 1)"]
fn e5c_148_two_fields_one_stored_from_the_other() {
    e5c_148_probe(
        "FIELDS",
        "#[repr(C)] pub struct S { a: *mut i32, b: *mut i32 }\n\
         pub unsafe fn entry(s: *mut S) { (*s).b = (*s).a; add((*s).a, (*s).b); }\n",
    );
}

#[test]
#[ignore = "era-5c 148 probe (relay 190 item 1)"]
fn e5c_148_control_two_locals() {
    e5c_148_probe(
        "CONTROL",
        "pub unsafe fn entry() { let mut x = 1i32; let mut y = 2i32; add(&mut x, &mut y); }\n",
    );
}

/// **R808-5 (wave-6o 110a, brotli's decoder) — a pair PROVEN to overlap is
/// not two references.** The driver takes `br = &mut (*s).br` and hands `s`
/// and `br` to callees that write through both. At the record (54′) both
/// formals converted: `DecodeMetaBlockLength(&mut *s, &mut *br)` into
/// `(s: &mut State, br: &mut BrotliBitReader)`, two protected references over
/// the reader's bytes. A raw view of `br` beside `s: &mut` is not a remedy:
/// a write through the view is a foreign write to `s`'s protected range. With
/// one argument a place inside the other's referent, both stay raw.
#[test]
fn r808_5_a_reader_inside_its_state_is_not_handed_beside_the_state_as_mut() {
    let input = include_str!("testdata/r808_decoder_reader_in_state.rs");
    match super::rewrite_m1_census_world(input) {
        super::RewriteOutcome::Emitted { source, .. } => {
            let flat = source.split_whitespace().collect::<Vec<_>>().join(" ");
            // `ReadDistanceInternal` is the `…Internal` shape (relay 164 item 2):
            // it receives both one call down, from `ReadDistance`'s formals.
            for callee in [
                "DecodeWindowBits",
                "DecodeMetaBlockLength",
                "ReadDistance",
                "ReadDistanceInternal",
                // relay 165 item 2: the table inside the state, through `h`.
                "ReadHuffmanCode",
            ] {
                let signature = flat
                    .split(&format!("fn {callee}("))
                    .nth(1)
                    .and_then(|rest| rest.split(')').next())
                    .unwrap_or_else(|| panic!("no {callee}:\n{source}"));
                // Both positions of a proven overlap stay raw (R810-2): neither
                // the state nor the object inside it is a protected `&mut`.
                assert!(
                    !signature.contains("&mut"),
                    "{callee} takes a protected `&mut` beside an argument that lies \
                     inside another: ({signature})\n{source}"
                );
            }
        }
        other => panic!("the census world emits: {other:#?}"),
    }
}

/// R808-5's control: the same proven overlap at a callee that only READS
/// through both keeps its references (two shared references may overlap).
#[test]
fn r808_5_control_a_read_only_overlap_keeps_its_references() {
    let input = include_str!("testdata/r808_decoder_reader_in_state.rs").replace(
        "#[no_mangle]\npub unsafe extern \"C\" fn BrotliDecoderDecompressStream(",
        "unsafe fn Peek(mut s: *const BrotliDecoderStateInternal, mut br: *const BrotliBitReader) -> u32 {\n    (*br).bit_pos_.wrapping_add((*s).state as u32)\n}\n#[no_mangle]\npub unsafe extern \"C\" fn BrotliDecoderPeek(mut s: *const BrotliDecoderStateInternal) -> u32 {\n    let mut br: *const BrotliBitReader = &(*s).br;\n    Peek(s, br)\n}\n#[no_mangle]\npub unsafe extern \"C\" fn BrotliDecoderDecompressStream(",
    );
    assert!(input.contains("fn Peek("), "the control edit applied");
    match super::rewrite_m1_census_world(&input) {
        super::RewriteOutcome::Emitted { source, .. } => {
            let flat = source.split_whitespace().collect::<Vec<_>>().join(" ");
            assert!(
                flat.contains(
                    "fn Peek(mut s: &BrotliDecoderStateInternal, mut br: &BrotliBitReader)"
                ),
                "a read-only overlap keeps both shared references:\n{source}"
            );
        }
        other => panic!("the census world emits: {other:#?}"),
    }
}

/// R815-6 (P8 `OutsideByteViewDiscipline`, R814-2): binn's `binn_object_blob`
/// hands on, bare, its byte formal `key` beside its typed formal `psize`. It is
/// an exported entry with no caller in the program, so the two are views of
/// different outside objects: the pair is disjoint under P8, `psize` is no raw
/// view, and the callee keeps both its slice `key` and its optional `psize`.
#[test]
fn r815_6_an_entry_byte_formal_beside_its_typed_formal_is_disjoint_under_p8() {
    let input = include_str!("testdata/r815_entry_byte_view_beside_typed.rs");
    match super::rewrite_m1_census_world(input) {
        super::RewriteOutcome::Emitted { source, .. } => {
            let flat = source.split_whitespace().collect::<Vec<_>>().join(" ");
            let signature = flat
                .split("fn binn_object_get(")
                .nth(1)
                .and_then(|rest| rest.split(')').next())
                .unwrap_or_else(|| panic!("no binn_object_get:\n{source}"));
            assert!(
                signature.contains("key: Option<&[i8]>") || signature.contains("key: &[i8]"),
                "the callee's key keeps its slice beside the entry's typed formal: ({signature})\n{source}"
            );
            assert!(
                signature.contains("psize: Option<&mut i32>"),
                "psize is not a raw view of the entry's pair: ({signature})\n{source}"
            );
        }
        other => panic!("the census world emits: {other:#?}"),
    }
}
