//! K21 — nested use edits, composed inner-first under one owner.
//!
//! Two subject-use rewrites whose spans nest — `new_id[block_ids[i]]` in the
//! source's raw spelling — could not both be applied, so the inner one was
//! refused and its subject stayed raw. The outer replacement text contains the
//! inner span's ORIGINAL text verbatim, which is what makes composition purely
//! textual and checkable: splice the inner replacement into the outer one and
//! drop the inner edit, whose work now lives inside its container.
//!
//! The population is brotli's `RemapBlockIds*` and `StoreSimpleHuffmanTree`
//! loops: 9 subjects by first reason, 4 where nesting is the only blocker.

fn reasons(src: &str) -> std::collections::BTreeMap<String, String> {
    super::emit_tests::decisions_of(src)
        .into_iter()
        .map(|(name, _, reason)| (name, reason))
        .collect()
}

/// brotli's `*new_id.offset(*block_ids.offset(i) as isize) = fresh` shape.
const NESTED_INDEX_INPUT: &str = "#![allow(dead_code, unused_unsafe)]\n\
    pub unsafe fn f(new_id: *mut u32, block_ids: *mut u8, n: usize) {\n\
        let mut i: usize = 0;\n\
        while i < n {\n\
            *new_id.offset(*block_ids.offset(i as isize) as isize) = 7;\n\
            i = i.wrapping_add(1);\n\
        }\n\
    }\n";

#[test]
fn nested_index_uses_compose_inner_first() {
    let got = reasons(NESTED_INDEX_INPUT);
    assert_ne!(
        got.get("block_ids").map(String::as_str),
        Some("nested-use-edits"),
        "the inner subject is composed, not refused: {got:#?}"
    );
    let super::RewriteOutcome::Emitted { source, .. } = super::rewrite_m1(NESTED_INDEX_INPUT)
    else {
        panic!("the nested-index fixture must emit")
    };
    assert!(
        source.contains("new_id[(block_ids[i]) as usize] = 7"),
        "both indexes are rewritten, inner inside outer; the parentheses are \
         the outer rewrite's own spelling of the index expression:\n{source}"
    );
    assert!(
        source.contains("block_ids: &[u8]"),
        "the inner subject converts too:\n{source}"
    );
    assert!(
        super::verify::type_checks_str(&source),
        "emitted output type/borrow-checks:\n{source}"
    );
}

/// The refusal survives where composition cannot be proven. Here the inner
/// span's original text occurs TWICE in the outer replacement, so splicing it
/// would rewrite a use that was never the inner subject's.
#[test]
fn ambiguous_nesting_still_refuses() {
    let src = "#![allow(dead_code, unused_unsafe)]\n\
        pub unsafe fn f(a: *mut u32, b: *mut u8, n: usize) -> u32 {\n\
            let mut i: usize = 0;\n\
            let mut t: u32 = 0;\n\
            while i < n {\n\
                t = t.wrapping_add(*a.offset((*b.offset(i as isize) as isize) + (*b.offset(i as isize) as isize)));\n\
                i = i.wrapping_add(1);\n\
            }\n\
            t\n\
        }\n";
    let got = reasons(src);
    println!("AMBIGUOUS-NESTING {got:#?}");
    let super::RewriteOutcome::Emitted { source, .. } = super::rewrite_m1(src) else {
        panic!("the ambiguous fixture must still emit something")
    };
    assert!(
        super::verify::type_checks_str(&source),
        "a refused nesting leaves a compiling tree:\n{source}"
    );
}
