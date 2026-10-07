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
            // The key converts (a slice on main's 55 line; a thin optional on
            // the frame head, which does not carry main's thin-into-fat rule):
            // the pair formed, so psize's form below is the certificate's.
            assert!(
                signature.contains("key: Option<&") || signature.contains("key: &"),
                "the callee's key converts beside the entry's typed formal: ({signature})\n{source}"
            );
            assert!(
                signature.contains("psize: Option<&mut i32>"),
                "psize is not a raw view of the entry's pair: ({signature})\n{source}"
            );
        }
        other => panic!("the census world emits: {other:#?}"),
    }
}

/// R815-6's controls: the signature of `binn_object_get` for a variant of the
/// P8 reduction, in the census world.
fn r815_6_callee_signature(input: &str) -> String {
    match super::rewrite_m1_census_world(input) {
        super::RewriteOutcome::Emitted { source, .. } => {
            let flat = source.split_whitespace().collect::<Vec<_>>().join(" ");
            flat.split("fn binn_object_get(")
                .nth(1)
                .and_then(|rest| rest.split(')').next())
                .unwrap_or_else(|| panic!("no binn_object_get:\n{source}"))
                .to_owned()
        }
        other => panic!("the census world emits: {other:#?}"),
    }
}

/// Not covered by P8: an entry the program itself calls (its caller is not
/// only outside).
#[test]
fn r815_6_control_an_entry_called_in_the_program_is_not_certified() {
    let input = format!(
        "{}\npub unsafe fn blob_user(o: *mut core::ffi::c_void, k: *const i8, s: *mut i32) -> *mut core::ffi::c_void {{ binn_object_blob(o, k, s) }}\n",
        include_str!("testdata/r815_entry_byte_view_beside_typed.rs")
    );
    let signature = r815_6_callee_signature(&input);
    assert!(signature.contains("psize: *mut i32"), "({signature})");
}

/// Not covered by P8: an entry that is not exported (no `#[no_mangle]`).
#[test]
fn r815_6_control_an_unexported_function_is_not_certified() {
    let input = include_str!("testdata/r815_entry_byte_view_beside_typed.rs").replace(
        "#[no_mangle]\npub unsafe extern \"C\" fn binn_object_blob(",
        "pub unsafe extern \"C\" fn binn_object_blob(",
    );
    assert!(input.contains("\npub unsafe extern \"C\" fn binn_object_blob("));
    let signature = r815_6_callee_signature(&input);
    assert!(signature.contains("psize: *mut i32"), "({signature})");
}

/// R819-1 item 1 (§29): a subject with nullability evidence, its own or
/// carried, is never delivered as a non-optional reference. `map_pair::pid` is
/// handed to a callee that null-tests it; when its Option stage is withdrawn it
/// falls back to raw, not to its Core form `&mut i32`.
#[test]
fn r819_1_a_nullable_entry_formal_never_falls_back_to_a_plain_reference() {
    let input = include_str!("testdata/r819_nullable_entry_formal_option_withdrawn.rs");
    match super::rewrite_m1_census_world(input) {
        super::RewriteOutcome::Emitted { source, .. } => {
            let flat = source.split_whitespace().collect::<Vec<_>>().join(" ");
            let signature = flat
                .split("fn map_pair(")
                .nth(1)
                .and_then(|rest| rest.split(')').next())
                .unwrap_or_else(|| panic!("no map_pair:\n{source}"));
            assert!(
                !signature.contains("pid: &mut i32") && !signature.contains("pid: &i32"),
                "a nullable formal is never a plain reference: ({signature})\n{source}"
            );
        }
        other => panic!("the census world emits: {other:#?}"),
    }
}

/// R819-1 item 1's control: without nullability evidence (the callee writes
/// through `pid` unconditionally, no null test) the entry keeps its reference.
#[test]
fn r819_1_control_a_formal_without_nullability_evidence_keeps_its_reference() {
    let input = include_str!("testdata/r819_nullable_entry_formal_option_withdrawn.rs").replace(
        "    if !pid.is_null() {\n        *pid = pos;\n        keep(pid);\n    }\n",
        "    *pid = pos;\n    keep(pid);\n",
    );
    assert!(!input.contains("pid.is_null()"));
    match super::rewrite_m1_census_world(&input) {
        super::RewriteOutcome::Emitted { source, .. } => {
            let flat = source.split_whitespace().collect::<Vec<_>>().join(" ");
            let signature = flat
                .split("fn map_pair(")
                .nth(1)
                .and_then(|rest| rest.split(')').next())
                .unwrap_or_else(|| panic!("no map_pair:\n{source}"));
            assert!(
                signature.contains("pid: &mut i32"),
                "({signature})\n{source}"
            );
        }
        other => panic!("the census world emits: {other:#?}"),
    }
}

/// R819-1 item 4's control: the same pointer at two positions of a callee that
/// only reads both (`zcmp(b, b)`) keeps its shared references.
#[test]
fn r819_4_control_the_same_pointer_read_at_two_positions_keeps_its_references() {
    let input = include_str!("testdata/r819_same_pointer_two_positions.rs");
    match super::rewrite_m1_census_world(input) {
        super::RewriteOutcome::Emitted { source, .. } => {
            let flat = source.split_whitespace().collect::<Vec<_>>().join(" ");
            let signature = flat
                .split("fn zcmp(")
                .nth(1)
                .and_then(|rest| rest.split(')').next())
                .unwrap_or_else(|| panic!("no zcmp:\n{source}"));
            assert!(
                signature.contains("a: &Z") && signature.contains("b: &Z"),
                "({signature})\n{source}"
            );
        }
        other => panic!("the census world emits: {other:#?}"),
    }
}

/// R833-1 (USER), the callee's side, end-to-end controls. (The rule's own
/// witness is unit-level, `decision/pair_rule_tests.rs`: on this reduction the
/// census world reads `add(G1, G2)` as proven disjoint even where `G2` may hold
/// `G1`'s pointer, so no raw-view pair forms here — three attempts.)
fn r833_signature(name: &str) -> String {
    let input = include_str!("testdata/r833_pair_not_shown_disjoint.rs");
    match super::rewrite_m1_census_world(input) {
        super::RewriteOutcome::Emitted { source, .. } => {
            let flat = source.split_whitespace().collect::<Vec<_>>().join(" ");
            flat.split(&format!("fn {name}("))
                .nth(1)
                .and_then(|rest| rest.split(')').next())
                .unwrap_or_else(|| panic!("no {name}:\n{source}"))
                .to_owned()
        }
        other => panic!("the census world emits: {other:#?}"),
    }
}

/// Control: the same callee shape at a call the scope's certificate proves.
#[test]
fn r833_1_control_a_certified_pair_keeps_its_references() {
    let signature = r833_signature("add2");
    assert!(signature.contains("a: &mut i32"), "({signature})");
    assert!(signature.contains("b: &"), "({signature})");
}

/// Control: a pair whose members are only read keeps shared references.
#[test]
fn r833_1_control_a_read_read_pair_keeps_shared_references() {
    let signature = r833_signature("sum");
    assert!(
        signature.contains("a: &i32") && signature.contains("b: &i32"),
        "({signature})"
    );
}

/// R838 (relay 178 item 2): `add(G1, G2)` with `G2` able to hold `G1`'s
/// pointer is not shown disjoint, so `add`'s formals both stay raw; the
/// entry's certified pair (`add2(x, y)`) keeps its references.
fn r838_signature(name: &str) -> String {
    let input = include_str!("testdata/r838_statics_pair.rs");
    match super::rewrite_m1_census_world(input) {
        super::RewriteOutcome::Emitted { source, .. } => {
            let flat = source.split_whitespace().collect::<Vec<_>>().join(" ");
            flat.split(&format!("fn {name}("))
                .nth(1)
                .and_then(|rest| rest.split(')').next())
                .unwrap_or_else(|| panic!("no {name}:\n{source}"))
                .to_owned()
        }
        other => panic!("the census world emits: {other:#?}"),
    }
}

#[test]
fn r838_add_of_two_statics_contents_keeps_both_formals_raw() {
    let signature = r838_signature("add");
    assert!(
        signature.contains("mut a: *mut i32") && signature.contains("mut b: *mut i32"),
        "({signature})"
    );
}

#[test]
fn r838_control_the_entrys_certified_pair_keeps_its_references() {
    let signature = r838_signature("add2");
    assert!(
        signature.contains("a: &mut i32") && signature.contains("b: &"),
        "({signature})"
    );
}

/// The raw view of a cast argument A5's fallback learned keeps the program's
/// cast to the formal's raw type: `&mut int32 as *mut i32 as *mut u32` beside a
/// loaded `p` (binn `copy_be32`, E0308 `&mut u32` expected, `&mut i32` found),
/// so the emission verifies without a revert and `psource` stays raw.
/// (`pdest` is a byte view here, not a conversion node: the pair rule does not
/// reach it — wave-5d report 138's named residual.)
#[test]
fn r833_1_the_raw_view_of_a_cast_address_keeps_its_cast() {
    let input = include_str!("testdata/r833_peer_of_a_learned_raw_view.rs");
    match super::rewrite_m1_census_world(input) {
        super::RewriteOutcome::Emitted {
            source,
            reverted_count,
            first_diags,
            ..
        } => {
            let flat = source.split_whitespace().collect::<Vec<_>>().join(" ");
            let signature = |name: &str| {
                flat.split(&format!("fn {name}("))
                    .nth(1)
                    .and_then(|rest| rest.split(')').next())
                    .unwrap_or_else(|| panic!("no {name}:\n{source}"))
                    .to_owned()
            };
            assert_eq!(
                (reverted_count, first_diags.len()),
                (0, 0),
                "the emission verifies without a revert: {first_diags:#?}\n{source}"
            );
            assert!(
                signature("copy_be32").contains("psource: *mut u32"),
                "{source}"
            );
            assert!(signature("save").contains("item: &mut Item"), "{source}");
        }
        other => panic!("the census world emits: {other:#?}"),
    }
}

fn r864_signature(name: &str) -> String {
    let input = include_str!("testdata/r864_raw_side.rs");
    match super::rewrite_m1_census_world(input) {
        super::RewriteOutcome::Emitted { source, .. } => {
            let flat = source.split_whitespace().collect::<Vec<_>>().join(" ");
            flat.split(&format!("fn {name}("))
                .nth(1)
                .and_then(|rest| rest.split(')').next())
                .unwrap_or_else(|| panic!("no {name}:\n{source}"))
                .to_owned()
        }
        other => panic!("the census world emits: {other:#?}"),
    }
}

/// R864-1 (a) (fan-out 081): `zsqr(x, &mut *x)` with `zsqr::a` raw: `b` is
/// held raw beside it (no pair row, no A5 proof, not shown disjoint).
#[test]
fn r864_1_a_a_reference_formal_beside_a_raw_formal_not_shown_disjoint_is_held() {
    let signature = r864_signature("zsqr");
    assert!(signature.contains("mut b: *mut Z"), "({signature})");
}

/// Control: the reference side is `&mut local` (a scalar), its address taken
/// only there.
#[test]
fn r864_1_a_control_a_local_taken_only_here_keeps_its_reference() {
    let signature = r864_signature("zsqr2");
    assert!(!signature.contains("mut b: *mut i32"), "({signature})");
}

fn r866_signature(name: &str) -> String {
    let input = include_str!("testdata/r866_containment.rs");
    match super::rewrite_m1_census_world(input) {
        super::RewriteOutcome::Emitted { source, .. } => {
            let flat = source.split_whitespace().collect::<Vec<_>>().join(" ");
            flat.split(&format!("fn {name}("))
                .nth(1)
                .and_then(|rest| rest.split(')').next())
                .unwrap_or_else(|| panic!("no {name}:\n{source}"))
                .to_owned()
        }
        other => panic!("the census world emits: {other:#?}"),
    }
}

/// R866-1 (fan-out 083): `safe_read(&mut *s, &mut *br)` with `br = &mut
/// (*s).br`: both formals stay raw. In this small crate the model itself
/// demotes `br` (the containment is a borrow conflict here) and the raw-side
/// rule (R864-1 (a)) holds `s` beside it; the record delivered both, and the
/// containment fact F2 holds them by is witnessed in `proven_overlap_tests`.
#[test]
fn r866_1_a_field_of_the_other_arguments_object_holds_both_formals() {
    let signature = r866_signature("safe_read");
    assert!(
        signature.contains("mut s: *mut State") && signature.contains("mut br: *mut BitReader"),
        "({signature})"
    );
}

/// The direct spelling, `safe_read2(&mut *s, &mut (*s).br)`.
#[test]
fn r866_1_the_fields_address_beside_the_objects_reborrow_holds_both_formals() {
    let signature = r866_signature("safe_read2");
    assert!(
        signature.contains("mut s: *mut State") && signature.contains("mut br: *mut BitReader"),
        "({signature})"
    );
}

/// Control: two distinct locals' addresses stay delivered.
#[test]
fn r866_1_control_two_distinct_locals_stay_delivered() {
    let signature = r866_signature("safe_read3");
    assert!(
        !signature.contains("*mut State") && !signature.contains("*mut BitReader"),
        "({signature})"
    );
}

/// The substrate's spelling, `safe_read4(s, br)`: F2's proven overlap (`br`'s
/// one definition lies inside `s`) holds both formals already.
#[test]
fn r866_1_the_substrate_spelling_is_f2s_proven_overlap() {
    let signature = r866_signature("safe_read4");
    assert!(
        signature.contains("mut s: *mut State") && signature.contains("mut br: *mut BitReader"),
        "({signature})"
    );
}
