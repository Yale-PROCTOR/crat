//! W-C9 witnesses: brotli's `BrotliSplitBlock → SplitByteVectorLiteral →
//! {InitialEntropyCodesLiteral, RefineEntropyCodesLiteral → RandomSampleLiteral}
//! chain, reduced — a slice root that is a caller LOCAL (the `literals`
//! allocation), not a parameter; and the transitive extent hold that keeps a
//! thin source out of the chain.

const CHAIN: &str = r###"
extern "C" {
    fn xalloc(n: usize) -> *mut u8;
    fn xfree(p: *mut u8);
    fn rnd() -> u32;
}
// The corpus leaves write into a histogram handed down beside `data`; that
// second converting pointer is the PAIR of report 016 (wave-6p's), so the
// reduction returns its sums instead and isolates the supply.
unsafe fn HistogramAddVector(data: *const u8, n: usize) -> u32 {
    let mut acc = 0u32;
    let mut i = 0usize;
    while i < n { acc = acc.wrapping_add(*data.offset(i as isize) as u32); i = i.wrapping_add(1); }
    acc
}
unsafe fn InitialEntropyCodes(data: *const u8, length: usize, stride: usize, num: usize) -> u32 {
    let block_length = length / num;
    let mut acc = 0u32;
    let mut i = 0usize;
    while i < num {
        let mut pos = length.wrapping_mul(i) / num;
        if i != 0 { pos = pos.wrapping_add((rnd() as usize) % block_length); }
        if pos.wrapping_add(stride) >= length { pos = length.wrapping_sub(stride).wrapping_sub(1); }
        let mut j = 0usize;
        while j < stride { acc = acc.wrapping_add(*data.offset((pos + j) as isize) as u32); j = j.wrapping_add(1); }
        i = i.wrapping_add(1);
    }
    acc
}
unsafe fn RandomSample(seed: u32, data: *const u8, length: usize, mut stride: usize) -> u32 {
    let mut pos = 0usize;
    if stride >= length { stride = length; } else { pos = (seed as usize) % (length.wrapping_sub(stride).wrapping_add(1)); }
    let mut acc = 0u32;
    let mut j = 0usize;
    while j < stride { acc = acc.wrapping_add(*data.offset((pos + j) as isize) as u32); j = j.wrapping_add(1); }
    acc
}
unsafe fn RefineEntropyCodes(data: *const u8, length: usize, stride: usize) -> u32 {
    let mut seed = 7u32;
    let mut acc = 0u32;
    let mut iter = 0usize;
    while iter < 8 {
        seed = seed.wrapping_mul(16807);
        acc = acc.wrapping_add(RandomSample(seed, data, length, stride));
        iter = iter.wrapping_add(1);
    }
    acc
}
unsafe fn SplitByteVector(data: *const u8, length: usize, stride: usize, num: usize) -> u32 {
    if length == 0 { return 0; }
    InitialEntropyCodes(data, length, stride, num).wrapping_add(RefineEntropyCodes(data, length, stride))
}
unsafe fn fill(p: *mut u8, n: usize) {
    let mut i = 0usize;
    while i < n { *p.offset(i as isize) = (i & 255) as u8; i = i.wrapping_add(1); }
}
pub unsafe fn entry(n: usize) -> u32 {
    let literals = xalloc(n);
    fill(literals, n);
    let r = SplitByteVector(literals, n, 3, 2);
    xfree(literals);
    r
}
"###;

fn fixture() -> String {
    format!(
        "#![allow(dead_code,unused_unsafe,unused_mut,unused_assignments,unused_variables,non_snake_case,non_camel_case_types)]\n{CHAIN}"
    )
}

/// The same chain with no companion integer beside `SplitByteVector::data`
/// (a pointer sits between it and `length`), so the fresh-root supply is
/// what decides it (R418-1 gives a companion forwarder the slice on its own).
fn fixture_no_companion() -> String {
    fixture()
        .replace(
            "unsafe fn SplitByteVector(data: *const u8, length: usize,",
            "unsafe fn SplitByteVector(data: *const u8, _tail: *const u8, length: usize,",
        )
        .replace(
            "SplitByteVector(literals, n, 3, 2)",
            "SplitByteVector(literals, literals, n, 3, 2)",
        )
}


/// **The adapter's extent arm, in both frames.** Ruling item 4a licensed the
/// adjacent integer by adjacency; R408-1 (wave-6f, batch 8) requires evidence
/// that it is a COUNT — a pinned contract's count position, wave-5c's
/// thin-count proof, or wave-6f's field transaction. These reductions carry
/// none, so on the composed frame the same site takes the receipted
/// `FALLBACK_SLICE_EXTENT` (addendum 77) where this lane's own line still
/// spells `(n) as usize`. The witness pins the SHAPE of the adapter and
/// accepts either extent; which one it is belongs to R408-1's evidence, not
/// to this rule. (Report 020 §2 asks whether the chain proof of R418-1 is
/// count evidence for that arm.)
fn extent_arm(flat: &str, prefix: &str) -> String {
    let at = flat
        .find(prefix)
        .unwrap_or_else(|| panic!("{prefix} not in {flat}"));
    // The prefix ends inside the constructor's argument list, so the extent
    // runs to the `)` that closes it — depth-aware, because the licensed
    // spelling is itself parenthesised (`(n) as usize`).
    let rest = &flat[at + prefix.len()..];
    let mut depth = 1usize;
    let mut end = rest.len();
    for (i, c) in rest.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    end = i;
                    break;
                }
            }
            _ => {}
        }
    }
    rest[..end].trim().trim_end_matches(',').to_owned()
}
fn licensed_extent(extent: &str, companion: &str) -> bool {
    extent == companion || extent == "crate::FALLBACK_SLICE_EXTENT"
}

/// `SplitByteVector::data` and `RefineEntropyCodes::data` are the corpus's
/// thin forwarders; their root is the caller's allocation LOCAL, which W-C7
/// refused (`caller-not-supplied`: a supplier had to be a parameter).
#[test]
fn w5c_slice_input_root_local_supplies_the_forwarders() {
    let proofs = super::slice_input_tests::proofs(&fixture());
    assert_eq!(
        super::slice_input_tests::proof_of(&proofs, "SplitByteVector::data"),
        &Ok(1)
    );
    assert_eq!(
        super::slice_input_tests::proof_of(&proofs, "RefineEntropyCodes::data"),
        &Ok(2)
    );
}

/// Under the corpus attestation both forwarders take the shared slice, the
/// root call adapts the raw allocation with the companion length
/// (evidence-backed, ruling item 4a), and the emitted program type-checks.
#[test]
fn w5c_slice_input_root_local_forwarders_deliver() {
    let input = fixture();
    let table = super::slice_input_tests::decisions(&input);
    for label in ["SplitByteVector::data", "RefineEntropyCodes::data"] {
        assert!(
            matches!(
                super::slice_input_tests::decision(&table, label),
                super::Decision::Slice { mutable: false, .. }
            ),
            "{label}: {:?}\n{table:#?}",
            super::slice_input_tests::decision(&table, label)
        );
    }
    let emitted = crate::bo_rewriter::emit_tests::ast_emitted_source_of(&input).unwrap();
    let flat = emitted.split_whitespace().collect::<Vec<_>>().join(" ");
    assert!(flat.contains("unsafe fn SplitByteVector(data: &[u8]"), "{flat}");
    let extent = extent_arm(
        &flat,
        "SplitByteVector(core::slice::from_raw_parts(literals,",
    );
    assert!(licensed_extent(&extent, "(n) as usize"), "{extent}: {flat}");
    assert!(crate::bo_rewriter::verify::type_checks_str(&emitted));
}

/// A THIN source at a forwarder's position is held on the forwarder's
/// account when the forwarder hands it, bare, to a RAW reader (a callee whose
/// arithmetic is no slice candidate): fix-2 one call deeper. Before W-C9 the
/// `&u8` bridged into the raw forwarder and the reader read wide through a
/// one-element claim.
#[test]
fn w5c_slice_input_thin_source_is_held_through_the_forwarder() {
    let input = format!(
        "#![allow(dead_code,unused_unsafe,unused_mut,unused_assignments,unused_variables,non_snake_case)]\n{}",
        r###"
unsafe fn raw_reader(data: *const u8, n: usize) -> u32 {
    let mut i = 0usize;
    let mut acc = 0u32;
    while i < n { acc = acc.wrapping_add(data.offset(i as isize).read() as u32); i = i.wrapping_add(1); }
    acc
}
unsafe fn forwarder(data: *const u8, n: usize) -> u32 { raw_reader(data, n) }
unsafe fn thin_entry(thin: *const u8) -> u32 { let x = *thin; forwarder(thin, 1).wrapping_add(x as u32) }
pub unsafe fn entry() -> u32 { let one: u8 = 7; thin_entry(&one) }
"###
    );
    let table = super::slice_input_tests::decisions(&input);
    let thin = super::slice_input_tests::decision(&table, "thin_entry::thin");
    assert!(
        matches!(
            thin,
            super::Decision::Degraded(super::Degradation {
                reason: super::DegradeReason::LocalCalleeAccessExtent { access, .. },
                ..
            }) if access.detail() == "forwarder:data:read:forwarded-into:raw_reader:data:read:pointer-arithmetic:offset"
        ),
        "{thin:?}"
    );
}

/// The root must be FRESH: a local whose value is a borrow of something else
/// (`&buf[0]`, a field's pointer) is not this rule's; a null-tested root is
/// the thin Option's.
#[test]
fn w5c_slice_input_root_local_must_be_fresh() {
    use super::slice_input::Hold;
    let borrowed = fixture_no_companion().replace(
        "    let literals = xalloc(n);",
        "    let mut arr = [0u8; 16];\n    let literals: *mut u8 = &mut arr[0];",
    );
    let proofs = super::slice_input_tests::proofs(&borrowed);
    assert_eq!(
        super::slice_input_tests::proof_of(&proofs, "SplitByteVector::data"),
        &Err(Hold::CallerNotSupplied)
    );
    // A call that takes a pointer may hand it back: not fresh.
    let handed_back = fixture_no_companion().replace(
        "    let literals = xalloc(n);",
        "    let mut arr = [0u8; 16];\n    let literals = pass_through(arr.as_mut_ptr());",
    ) + "unsafe fn pass_through(p: *mut u8) -> *mut u8 { p }\n";
    let proofs = super::slice_input_tests::proofs(&handed_back);
    assert_eq!(
        super::slice_input_tests::proof_of(&proofs, "SplitByteVector::data"),
        &Err(Hold::CallerNotSupplied)
    );
    // A root redefined from something else is not fresh past that point.
    let reassigned = fixture_no_companion()
        .replace("    let literals = xalloc(n);", "    let mut literals = xalloc(n);")
        .replace(
            "    fill(literals, n);",
            "    let mut arr = [0u8; 16];\n    fill(literals, n);\n    literals = arr.as_mut_ptr();",
        );
    let proofs = super::slice_input_tests::proofs(&reassigned);
    assert_eq!(
        super::slice_input_tests::proof_of(&proofs, "SplitByteVector::data"),
        &Err(Hold::CallerNotSupplied)
    );
    let tested = fixture_no_companion().replace(
        "    fill(literals, n);",
        "    if literals.is_null() { return 0; }\n    fill(literals, n);",
    );
    let proofs = super::slice_input_tests::proofs(&tested);
    assert_eq!(
        super::slice_input_tests::proof_of(&proofs, "SplitByteVector::data"),
        &Err(Hold::CallerNullable)
    );
}
