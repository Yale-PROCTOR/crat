//! wave-6p R477-6: the seam's alias-twin gate asks whether a converting
//! position shares a PLACE ROOT with a non-converting argument, which holds the
//! whole call when the two are distinct FIELDS of one struct — memory that
//! cannot overlap. The rule lets the pair-disjointness certificate answer, so
//! the shared root alone no longer blocks.
//!
//! The controls are the three shapes the certificate must keep refusing: a
//! whole place beside a projection of itself, an index projection with a
//! runtime index, and the same local twice.

use super::counted_void_tests::compact;

/// The certificate's verdict on one recorded pair of a fixture.
fn verdict_of(
    src: &str,
    caller: &str,
    callee: &str,
    left: usize,
    right: usize,
) -> Result<
    super::decision::pair_disjointness::CertificateKind,
    super::decision::pair_disjointness::Unproved,
> {
    let mut out = None;
    ::utils::compilation::run_compiler_on_str(src, |tcx| {
        let program = super::collect_program(tcx);
        let mut_facts =
            crate::analyses::borrow_ownership::mutability_facts::MutFacts::from_program(&program);
        let index = super::decision::pair_disjointness::PairDisjointnessIndex::derive(
            &program, &mut_facts, None,
        );
        let function = |name: &str| {
            *program
                .functions
                .iter()
                .find(|did| tcx.item_name(did.to_def_id()).as_str() == name)
                .unwrap_or_else(|| panic!("no fn {name}"))
        };
        out = Some(index.certify_recorded(function(caller), function(callee), left, right));
    })
    .expect("fixture compilation");
    out.expect("the compiler callback ran")
}

/// brotli's `BrotliBuildHistogramsWithContext` shape: three `&mut (*mb).<field>`
/// arguments beside a raw `(*mb).command_histograms` peer, all rooted at `mb`.
const DISJOINT_FIELD_PEER: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct Split { pub num_types: i32, pub alphabet_size: i32 }
#[repr(C)]
pub struct MetaBlock {
    pub literal_split: Split,
    pub command_split: Split,
    pub distance_split: Split,
    pub command_histograms: *mut u32,
}
pub unsafe fn BuildHistograms(
    mut cmds: *const u32,
    mut n: i32,
    mut literal_split: *mut Split,
    mut command_split: *mut Split,
    mut dist_split: *mut Split,
    mut histograms: *mut u32,
) {
    (*literal_split).num_types = n;
    (*command_split).num_types = n;
    (*dist_split).num_types = n;
    *histograms.offset(1) = *cmds;
}
pub unsafe fn BuildMetaBlock(mut mb: *mut MetaBlock, mut cmds: *const u32, mut n: i32) {
    BuildHistograms(
        cmds,
        n,
        &mut (*mb).literal_split,
        &mut (*mb).command_split,
        &mut (*mb).distance_split,
        (*mb).command_histograms,
    );
}
"#;

/// The three field-address arguments certify pairwise, and the certificate is
/// `DisjointFields` by name — the rule R477-6 priced is already built and
/// already fires on this exact shape. What still holds the call is the pair
/// each of them forms with argument 5, the pointer VALUE loaded out of a
/// sibling field: `pointer_value_provenance` gives a loaded pointer no place
/// (its pointee is not the field slot), so no projection argument reaches it,
/// and the type rule refuses it `MemberType` because `u32` may lawfully alias
/// `Split`'s `i32` members by signedness. Both refusals are correct.
#[test]
fn w6p_field_addresses_certify_and_the_loaded_sibling_does_not() {
    ::utils::compilation::run_compiler_on_str(DISJOINT_FIELD_PEER, |tcx| {
        let program = super::collect_program(tcx);
        let mut_facts =
            crate::analyses::borrow_ownership::mutability_facts::MutFacts::from_program(&program);
        let index = super::decision::pair_disjointness::PairDisjointnessIndex::derive(
            &program, &mut_facts, None,
        );
        let function = |name: &str| {
            *program
                .functions
                .iter()
                .find(|did| tcx.item_name(did.to_def_id()).as_str() == name)
                .unwrap_or_else(|| panic!("no fn {name}"))
        };
        let (caller, callee) = (function("BuildMetaBlock"), function("BuildHistograms"));
        for (left, right) in [(2, 3), (2, 4), (3, 4)] {
            assert_eq!(
                index.certify_recorded(caller, callee, left, right),
                Ok(super::decision::pair_disjointness::CertificateKind::DisjointFields),
                "distinct field projections of one root are disjoint ({left}, {right})"
            );
        }
        for (left, right) in [(2, 5), (3, 5), (4, 5)] {
            assert!(
                index.certify_recorded(caller, callee, left, right).is_err(),
                "a field ADDRESS and a pointer VALUE loaded from a sibling field \
                 share no projection argument ({left}, {right})"
            );
        }
    })
    .expect("fixture compilation");
}

/// The consequence at the seam, pinned so the day the loaded sibling gets a
/// root this witness moves: the call still holds and the callee's field
/// parameters keep their raw form.
#[test]
fn w6p_the_loaded_sibling_still_holds_the_seam() {
    let source = super::emit_tests::ast_emitted_source_of(DISJOINT_FIELD_PEER).unwrap();
    let c = compact(&source);
    assert!(
        !c.contains("__crat_raw_BuildHistograms"),
        "the alias twin is not what holds this call: {source}"
    );
    assert!(
        !c.contains("literal_split:&mutSplit"),
        "argument 5's unknown pointee still holds the field parameters: {source}"
    );
}

/// Control (i), whole-vs-part: `EncodeData(s, …, &mut (*s).available_out_, …)`
/// passes the container itself beside a projection of it. A whole place and any
/// projection of it DO overlap.
const WHOLE_AND_PART: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
#[repr(C)]
pub struct State { pub available_out_: usize, pub buf: *mut u8 }
pub unsafe fn WriteBits(mut s: *mut State, mut avail: *mut usize, mut n: i32) {
    *avail = (*avail).wrapping_add(1);
    *(*s).buf.offset(n as isize) = 0;
}
pub unsafe fn EncodeData(mut s: *mut State, mut n: i32) {
    WriteBits(s, &mut (*s).available_out_, n);
}
"#;

#[test]
fn w6p_whole_place_beside_its_own_projection_stays_held() {
    assert_ne!(
        verdict_of(WHOLE_AND_PART, "EncodeData", "WriteBits", 0, 1),
        Ok(super::decision::pair_disjointness::CertificateKind::DisjointFields),
        "a projection of the very place passed whole is not disjoint from it"
    );
}

/// Control (ii), a runtime index: `&mut *(*s).block_length.offset(i)` names no
/// field of `s` that a certificate can separate from `s`'s other uses.
const RUNTIME_INDEX: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
#[repr(C)]
pub struct Reader { pub block_length: *mut u32, pub pos: usize }
pub unsafe fn ReadLength(mut r: *mut Reader, mut slot: *mut u32) {
    *slot = (*slot).wrapping_add(1);
    (*r).pos = (*r).pos.wrapping_add(1);
}
pub unsafe fn SafeReadBlockLength(mut s: *mut Reader, mut i: isize) {
    ReadLength(s, &mut *(*s).block_length.offset(i));
}
"#;

#[test]
fn w6p_runtime_index_projection_stays_held() {
    assert_ne!(
        verdict_of(RUNTIME_INDEX, "SafeReadBlockLength", "ReadLength", 0, 1),
        Ok(super::decision::pair_disjointness::CertificateKind::DisjointFields),
        "an index projection with a runtime index proves no field separation \
         (this pair is separated by the TYPE rule instead, which is the point: \
         no projection argument reaches it)"
    );
}

/// Control (iii), the same local twice: heman's `kmXNormalize(pOut, pOut)`.
const SAME_LOCAL_TWICE: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
#[derive(Copy, Clone)]
#[repr(C)]
pub struct kmVec3 { pub x: f32, pub y: f32, pub z: f32 }
pub unsafe fn kmVec3Normalize(mut pOut: *mut kmVec3, mut pIn: *const kmVec3) {
    (*pOut).x = (*pIn).x;
    (*pOut).y = (*pIn).y;
    (*pOut).z = (*pIn).z;
}
pub unsafe fn kmXNormalize(mut pOut: *mut kmVec3) {
    kmVec3Normalize(pOut, pOut);
}
"#;

#[test]
fn w6p_same_local_on_both_sides_stays_held() {
    assert_eq!(
        verdict_of(SAME_LOCAL_TWICE, "kmXNormalize", "kmVec3Normalize", 0, 1),
        Err(super::decision::pair_disjointness::Unproved::SamePlace),
        "the same place is never disjoint from itself"
    );
}

#[test]
#[ignore = "diagnostic: the certificate's own verdict on the fixture's pairs"]
fn w6p_probe_disjoint_field_certificates() {
    ::utils::compilation::run_compiler_on_str(DISJOINT_FIELD_PEER, |tcx| {
        let program = super::collect_program(tcx);
        let mut_facts =
            crate::analyses::borrow_ownership::mutability_facts::MutFacts::from_program(&program);
        let index = super::decision::pair_disjointness::PairDisjointnessIndex::derive(
            &program, &mut_facts, None,
        );
        let function = |name: &str| {
            *program
                .functions
                .iter()
                .find(|did| tcx.item_name(did.to_def_id()).as_str() == name)
                .unwrap_or_else(|| panic!("no fn {name}"))
        };
        let (caller, callee) = (function("BuildMetaBlock"), function("BuildHistograms"));
        for (l, r) in [
            (2, 3),
            (2, 4),
            (3, 4),
            (2, 5),
            (3, 5),
            (4, 5),
            (0, 2),
            (0, 5),
        ] {
            println!(
                "W6P_CERT\t{l}\t{r}\t{:?}",
                index.certify_recorded(caller, callee, l, r)
            );
        }
    })
    .expect("fixture compilation");
}

#[test]
#[ignore = "diagnostic: the certificate's verdict on the two control fixtures"]
fn w6p_probe_control_certificates() {
    for (label, src, caller, callee, pairs) in [
        (
            "whole-part",
            WHOLE_AND_PART,
            "EncodeData",
            "WriteBits",
            vec![(0usize, 1usize)],
        ),
        (
            "index",
            RUNTIME_INDEX,
            "SafeReadBlockLength",
            "ReadLength",
            vec![(0, 1)],
        ),
        (
            "same-local",
            SAME_LOCAL_TWICE,
            "kmXNormalize",
            "kmVec3Normalize",
            vec![(0, 1)],
        ),
    ] {
        ::utils::compilation::run_compiler_on_str(src, |tcx| {
            let program = super::collect_program(tcx);
            let mut_facts =
                crate::analyses::borrow_ownership::mutability_facts::MutFacts::from_program(
                    &program,
                );
            let index = super::decision::pair_disjointness::PairDisjointnessIndex::derive(
                &program, &mut_facts, None,
            );
            let function = |name: &str| {
                *program
                    .functions
                    .iter()
                    .find(|did| tcx.item_name(did.to_def_id()).as_str() == name)
                    .unwrap_or_else(|| panic!("no fn {name}"))
            };
            for (l, r) in &pairs {
                println!(
                    "W6P_CTRL\t{label}\t{l}\t{r}\t{:?}",
                    index.certify_recorded(function(caller), function(callee), *l, *r)
                );
            }
        })
        .expect("control fixture compilation");
    }
}

/// R478-5, mechanized: the probe column is a READ, not a rule. `ArgRecord.why`
/// and `LocalFacts.other_shapes` are written at derive time and may be read
/// only from `#[cfg(test)]` code — `pair_disjointness.rs`'s rule half must
/// never consult them, or the column would move a decision. The ban is checked
/// on the source text because there is no type that can express it.
#[test]
fn w6p_the_probe_column_is_never_read_by_a_rule() {
    let source = include_str!("decision/pair_disjointness.rs");
    let rules = source
        .split_once("#[cfg(test)]\nimpl PairDisjointnessIndex {")
        .expect("the probe half starts at the cfg(test) impl")
        .0;
    for (line_no, line) in rules.lines().enumerate() {
        let code = line.split("//").next().unwrap_or(line);
        // Writing the column is what derive does; reading it is the ban.
        let writes = code.contains("why,")
            || code.contains("why:")
            || code.contains("other_shapes:")
            || code.contains("other_shapes.push");
        assert!(
            writes || !(code.contains(".why") || code.contains(".other_shapes")),
            "pair_disjointness.rs:{} reads the probe column from a rule: {line}",
            line_no + 1
        );
    }
}
