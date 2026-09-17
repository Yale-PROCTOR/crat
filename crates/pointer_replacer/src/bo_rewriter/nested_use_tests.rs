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

// ---------------------------------------------------------------------------
// Relay 037 — the same composition where the CONTAINER is a Box owner.
//
// brotli `BrotliHistogramReindex{Command,Distance,Literal}` writes
// `*new_index.offset(*symbols.offset(i as isize) as isize)`: the container is
// the contract-allocated owner's element access (a `Box` decision's
// `expr_edits`), the inner is another subject's `subject-use`. K21's scan only
// ever looked at `Slice` / `NestedSlice` / `Opt` uses, so a `Box` container was
// invisible to it — the two edits reached the class layer as two sites over one
// interval and the class held `intra-class-interval-overlap` (12 rows of the
// census of record, 4 in each of the three Reindex classes).

const CONTRACT_PRELUDE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, unused_assignments, non_camel_case_types, non_snake_case)]
extern "C" {
    fn exit(code: i32) -> !;
}
#[repr(C)]
pub struct MemoryManager {
    pub alloc_func: Option<unsafe extern "C" fn(*mut std::os::raw::c_void, usize) -> *mut std::os::raw::c_void>,
    pub free_func: Option<unsafe extern "C" fn(*mut std::os::raw::c_void, *mut std::os::raw::c_void)>,
    pub opaque: *mut std::os::raw::c_void,
}
pub unsafe extern "C" fn BrotliAllocate(mut m: *mut MemoryManager, mut n: usize) -> *mut std::os::raw::c_void {
    let mut result = ((*m).alloc_func).expect("non-null function pointer")((*m).opaque, n);
    if result.is_null() { exit(1 as i32); }
    return result;
}
pub unsafe extern "C" fn BrotliFree(mut m: *mut MemoryManager, mut p: *mut std::os::raw::c_void) {
    ((*m).free_func).expect("non-null function pointer")((*m).opaque, p);
}
"#;

/// The census shape, reduced: the owner's element access CONTAINS the
/// parameter's element access, inside one signature class.
const REINDEX: &str = r#"
pub unsafe extern "C" fn HistogramReindex(mut m: *mut MemoryManager, mut symbols: *mut u32, length: usize) -> u32 {
    let mut new_index = if length > 0 as usize {
        BrotliAllocate(m, length.wrapping_mul(::core::mem::size_of::<u32>())) as *mut u32
    } else { 0 as *mut u32 };
    let mut next_index = 0 as u32;
    let mut i = 0 as usize;
    while i < length {
        *new_index.offset(i as isize) = 0 as u32;
        i = i.wrapping_add(1);
    }
    i = 0 as usize;
    while i < length {
        if *new_index.offset(*symbols.offset(i as isize) as isize) == 0 as u32 {
            *new_index.offset(*symbols.offset(i as isize) as isize) = next_index;
            next_index = next_index.wrapping_add(1);
        }
        i = i.wrapping_add(1);
    }
    BrotliFree(m, new_index as *mut std::os::raw::c_void);
    new_index = 0 as *mut u32;
    return next_index;
}
"#;

#[test]
fn a_box_container_composes_over_the_inner_subject_use() {
    let out =
        super::wave6a_allocation_tests::emitted("reindex", &format!("{CONTRACT_PRELUDE}{REINDEX}"));
    let text = super::wave6a_allocation_tests::compact(&out.source);
    println!("REINDEX-EMITTED\n{}", out.source);
    println!("REINDEX-DEGRADED {:#?}", out.degradations);
    println!("REINDEX-COLLISIONS\n{}", out.artifacts.class_collisions);
    assert!(
        text.contains("new_index.as_deref_mut().unwrap()[(symbols[i])asusize]=next_index;"),
        "the owner's index composes over the inner subject's product:\n{}",
        out.source
    );
    assert!(
        text.contains("symbols:&[u32]"),
        "the inner subject converts too:\n{}",
        out.source
    );
    assert!(
        super::verify::type_checks_str(&out.source),
        "emitted output type/borrow-checks:\n{}",
        out.source
    );
}

/// The refusal survives on the Box side too: the inner span's original text
/// occurs TWICE in the owner's replacement, so splicing it would rewrite a use
/// that was never the inner subject's. The container keeps its own rewrite and
/// the inner subject stays raw — a hold, and a compiling tree.
#[test]
fn an_ambiguous_box_container_still_refuses() {
    const AMBIGUOUS: &str = r#"
pub unsafe extern "C" fn HistogramReindexTwice(mut m: *mut MemoryManager, mut symbols: *mut u32, length: usize) -> u32 {
    let mut new_index = if length > 0 as usize {
        BrotliAllocate(m, length.wrapping_mul(::core::mem::size_of::<u32>())) as *mut u32
    } else { 0 as *mut u32 };
    let mut next_index = 0 as u32;
    let mut i = 0 as usize;
    while i < length {
        *new_index.offset(((*symbols.offset(i as isize)) + (*symbols.offset(i as isize))) as isize) = next_index;
        i = i.wrapping_add(1);
    }
    BrotliFree(m, new_index as *mut std::os::raw::c_void);
    new_index = 0 as *mut u32;
    return next_index;
}
"#;
    let out = super::wave6a_allocation_tests::emitted(
        "reindex-ambiguous",
        &format!("{CONTRACT_PRELUDE}{AMBIGUOUS}"),
    );
    println!("AMBIGUOUS-BOX-DEGRADED {:#?}", out.degradations);
    assert_eq!(
        super::wave6a_allocation_tests::reason_of(
            &out.degradations,
            "HistogramReindexTwice::symbols"
        )
        .as_deref(),
        Some("nested-use-edits"),
        "the inner subject is refused, not spliced twice:\n{}",
        out.source
    );
    assert!(
        super::verify::type_checks_str(&out.source),
        "a refused nesting leaves a compiling tree:\n{}",
        out.source
    );
}

/// **The upstream refusal is load-bearing, not redundant.** A container whose
/// inner access is its OWN (`*p.offset(*p.offset(i) as isize)`) would compose
/// into `p[(p[i]) as usize]`, which Rust rejects (`p` borrowed mutably and
/// immutably at once). Both owner collectors refuse such a subject before it
/// can reach a plan (`return_certificate::owner_uses`'s `nested-owner-access`,
/// `box_param::slice_uses_of`'s `nested-element-access`), so the table-level
/// composition never sees it — which is why making a Box container visible to
/// the scan cannot manufacture that shape.
#[test]
fn a_self_nesting_owner_is_refused_upstream_and_leaves_a_compiling_tree() {
    const SELF_NESTED: &str = r#"
pub unsafe extern "C" fn HistogramReindexSelf(mut m: *mut MemoryManager, length: usize) -> u32 {
    let mut new_index = if length > 0 as usize {
        BrotliAllocate(m, length.wrapping_mul(::core::mem::size_of::<u32>())) as *mut u32
    } else { 0 as *mut u32 };
    let mut next_index = 0 as u32;
    let mut i = 0 as usize;
    while i < length {
        *new_index.offset(*new_index.offset(i as isize) as isize) = next_index;
        i = i.wrapping_add(1);
    }
    BrotliFree(m, new_index as *mut std::os::raw::c_void);
    new_index = 0 as *mut u32;
    return next_index;
}
"#;
    let out = super::wave6a_allocation_tests::emitted(
        "reindex-self",
        &format!("{CONTRACT_PRELUDE}{SELF_NESTED}"),
    );
    println!("SELF-NESTED-DEGRADED {:#?}", out.degradations);
    assert!(
        !super::wave6a_allocation_tests::compact(&out.source).contains("new_index.as_deref"),
        "the self-nesting owner must not be planned:\n{}",
        out.source
    );
    assert!(
        super::verify::type_checks_str(&out.source),
        "the refusal leaves a compiling tree:\n{}",
        out.source
    );
}
