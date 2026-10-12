//! wave-5d relay 207 (R785-6, report 119; analysis-fanout 118): the twin check
//! (`counted_void::aliased_storage_twin`) decides by ROOT — a converted position
//! whose place root is also a raw argument's root sends the call to the callee's
//! raw twin (or, for a non-leaf callee, refuses it `SiteOverlap`). The A5 site
//! proof is per PAIR: brotli's `InitializeHx(&mut (*hasher).common,
//! &mut (*hasher).privat._Hx, params)` and the block splitters'
//! `(.., &mut (*mb).literal_split, &mut (*mb).literal_histograms, ..)` are one
//! root and disjoint fields, every pair `a5-site-proof-clear`. A raw argument
//! proven disjoint from the converted one is not its alias.

const ONE_ROOT_DISJOINT_FIELDS: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut)]
#[repr(C)]
pub struct Common { pub x: i32, pub y: i32 }
#[repr(C)]
pub struct Priv { pub n: usize }
#[repr(C)]
pub struct Hasher { pub common: Common, pub privat: Priv }
unsafe fn init(common: *mut Common, p: *mut Priv, params: *const i32) {
    (*common).x = *params;
    (*common).y = 0;
    (*p).n = p as usize;
}
pub unsafe fn reset(hasher: *mut Hasher, params: *const i32) {
    init(&mut (*hasher).common, &mut (*hasher).privat, params);
}
"#;

fn flat(source: &str) -> String {
    source.split_whitespace().collect::<Vec<_>>().join(" ")
}

#[test]
fn w5d_207_a_proven_disjoint_field_is_not_the_converted_views_alias() {
    let source = super::emitted(ONE_ROOT_DISJOINT_FIELDS);
    let text = flat(&source);
    assert!(
        !text.contains("__crat_raw_init"),
        "a pair proven disjoint does not send the call to the raw twin:\n{source}"
    );
    assert!(
        text.contains("fn init(common: &mut Common"),
        "the converted formal delivers:\n{source}"
    );
}
