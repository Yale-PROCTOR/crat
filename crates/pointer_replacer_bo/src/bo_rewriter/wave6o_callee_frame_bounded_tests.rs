//! **R572-3 (relay 085): frame-bounded retention with the container inside the
//! callee.**
//!
//! brotli's `BrotliBuildHistogramsWithContext` opens with a `BlockSplitIterator`
//! on its own stack and `InitBlockSplitIterator(&mut literal_it, literal_split)`
//! stores the formal into `literal_it.split_`; the iterator is advanced by
//! `BlockSplitIteratorNext(&mut literal_it)` and read by field, never returned
//! and never stored elsewhere. The pointer dies with the callee's frame.

/// brotli's shape, reduced: the metablock caller, the histogram builder with its
/// iterator local, and the two iterator functions verbatim in structure.
const ITERATOR: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case, non_camel_case_types)]
#[repr(C)]
pub struct BlockSplit { pub num_types: usize, pub num_blocks: usize, pub types: *mut u8, pub lengths: *mut u32 }
#[repr(C)]
#[derive(Copy, Clone)]
pub struct BlockSplitIterator { pub split_: *const BlockSplit, pub idx_: usize, pub type_: usize, pub length_: usize }
unsafe fn InitBlockSplitIterator(mut self_0: *mut BlockSplitIterator, mut split: *const BlockSplit) {
    (*self_0).split_ = split;
    (*self_0).idx_ = 0 as usize;
    (*self_0).type_ = 0 as usize;
    (*self_0).length_ = (if !((*split).lengths).is_null() { *((*split).lengths).offset(0 as isize) } else { 0 as u32 }) as usize;
}
unsafe fn BlockSplitIteratorNext(mut self_0: *mut BlockSplitIterator) {
    if (*self_0).length_ == 0 as usize {
        (*self_0).idx_ = ((*self_0).idx_).wrapping_add(1);
        (*self_0).type_ = *((*(*self_0).split_).types).offset((*self_0).idx_ as isize) as usize;
        (*self_0).length_ = *((*(*self_0).split_).lengths).offset((*self_0).idx_ as isize) as usize;
    }
    (*self_0).length_ = ((*self_0).length_).wrapping_sub(1);
}
pub unsafe fn BuildHistograms(mut n: usize, mut literal_split: *const BlockSplit, mut histo: *mut u32) {
    let mut literal_it = BlockSplitIterator { split_: 0 as *const BlockSplit, idx_: 0, type_: 0, length_: 0 };
    let mut i: usize = 0;
    InitBlockSplitIterator(&mut literal_it, literal_split);
    while i < n {
        BlockSplitIteratorNext(&mut literal_it);
        *histo.offset(literal_it.type_ as isize) = (*histo.offset(literal_it.type_ as isize)).wrapping_add(1);
        i = i.wrapping_add(1);
    }
}
#[repr(C)]
pub struct MetaBlockSplit { pub literal_split: BlockSplit, pub histo: *mut u32 }
pub unsafe fn BuildMetaBlock(mut mb: *mut MetaBlockSplit, mut n: usize) {
    BuildHistograms(n, &mut (*mb).literal_split, (*mb).histo);
}
"#;

/// `(verdict, reason)` of the retention row for `function` at `argument`.
fn retention_row(input: &str, function: &str, argument: usize) -> (String, String) {
    let tsv = retention_tsv(input);
    let header = tsv.lines().next().expect("retention header");
    let ix = |name: &str| {
        header
            .split('\t')
            .position(|c| c == name)
            .unwrap_or_else(|| panic!("column {name} in {header}"))
    };
    let (f, a, v, r) = (
        ix("function"),
        ix("argument_index"),
        ix("verdict"),
        ix("reason"),
    );
    let row = tsv
        .lines()
        .skip(1)
        .map(|line| line.split('\t').collect::<Vec<_>>())
        .find(|c| c[f].ends_with(function) && c[a] == argument.to_string())
        .unwrap_or_else(|| panic!("no retention row for {function} arg{argument}:\n{tsv}"));
    (row[v].to_owned(), row[r].to_owned())
}

fn retention_tsv(input: &str) -> String {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (_, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("decision table");
        ctx.raw_boundary_artifacts.retention.clone()
    })
    .expect("fixture compiler context")
}

/// **The witness.** The histogram builder's split is stored into its own
/// iterator, which never leaves the frame; the iterator's callees are
/// certified. The row is `no-retain` with the typed receipt, tagged
/// `callee-local` and naming the storing call, and the metablock caller's
/// parameter — which reached the hold only through this row — is freed too.
#[test]
fn wave6o_a_callee_local_container_bounds_the_retention() {
    let (verdict, reason) = retention_row(ITERATOR, "BuildHistograms", 1);
    assert_eq!(verdict, "no-retain", "reason={reason}");
    assert!(
        reason.starts_with("retention-discharged:frame-bounded(subject=arg1, container=_")
            && reason.contains(", via=")
            && reason.ends_with(", callee-local)"),
        "{reason}"
    );
    let (caller, reason) = retention_row(ITERATOR, "BuildMetaBlock", 0);
    assert_eq!(caller, "no-retain", "reason={reason}");
}

/// Control (relay 085): the container escapes BY VALUE — the builder returns
/// its iterator — so clause (2) fails and the hold stands.
#[test]
fn wave6o_a_returned_callee_container_keeps_the_retention() {
    let input = ITERATOR
        .replace(
            "pub unsafe fn BuildHistograms(mut n: usize, mut literal_split: *const BlockSplit, mut histo: *mut u32) {",
            "pub unsafe fn BuildHistograms(mut n: usize, mut literal_split: *const BlockSplit, mut histo: *mut u32) -> BlockSplitIterator {",
        )
        .replace("        i = i.wrapping_add(1);\n    }\n}", "        i = i.wrapping_add(1);\n    }\n    return literal_it;\n}")
        .replace(
            "    BuildHistograms(n, &mut (*mb).literal_split, (*mb).histo);",
            "    let _ = BuildHistograms(n, &mut (*mb).literal_split, (*mb).histo);",
        );
    assert!(input.contains("return literal_it;"), "fixture edit applied");
    assert_eq!(retention_row(&input, "BuildHistograms", 1).0, "retains");
    assert_eq!(retention_row(&input, "BuildMetaBlock", 0).0, "retains");
}

/// Control (relay 085): the container is stored into a formal's pointee, so it
/// outlives the frame — clause (2) fails.
#[test]
fn wave6o_a_callee_container_stored_through_a_formal_keeps_the_retention() {
    let input = ITERATOR
        .replace(
            "mut histo: *mut u32) {",
            "mut histo: *mut u32, mut keep: *mut BlockSplitIterator) {",
        )
        .replace(
            "        i = i.wrapping_add(1);\n    }\n}",
            "        i = i.wrapping_add(1);\n    }\n    *keep = literal_it;\n}",
        )
        .replace(
            "(*mb).histo);",
            "(*mb).histo, 0 as *mut BlockSplitIterator);",
        );
    assert!(
        input.contains("*keep = literal_it;"),
        "fixture edit applied"
    );
    assert_eq!(retention_row(&input, "BuildHistograms", 1).0, "retains");
}

/// Control, clause (3): a callee receiving the container's address keeps it.
#[test]
fn wave6o_a_retaining_container_callee_keeps_the_callee_side_hold() {
    let input = ITERATOR
        .replace(
            "unsafe fn BlockSplitIteratorNext(mut self_0: *mut BlockSplitIterator) {",
            "static mut KEPT: *mut BlockSplitIterator = 0 as *mut BlockSplitIterator;\nunsafe fn BlockSplitIteratorNext(mut self_0: *mut BlockSplitIterator) {\n    KEPT = self_0;",
        );
    assert!(input.contains("KEPT = self_0;"), "fixture edit applied");
    assert_eq!(retention_row(&input, "BuildHistograms", 1).0, "retains");
}

/// Control, clause (3) through the field: a container callee copies the STORED
/// pointer out of the container into a static.
#[test]
fn wave6o_a_container_callee_copying_the_stored_pointer_out_keeps_the_hold() {
    let input = ITERATOR
        .replace(
            "unsafe fn BlockSplitIteratorNext(mut self_0: *mut BlockSplitIterator) {",
            "static mut KEPT_SPLIT: *const BlockSplit = 0 as *const BlockSplit;\nunsafe fn BlockSplitIteratorNext(mut self_0: *mut BlockSplitIterator) {\n    KEPT_SPLIT = (*self_0).split_;",
        );
    assert!(
        input.contains("KEPT_SPLIT = (*self_0).split_;"),
        "fixture edit applied"
    );
    assert_eq!(retention_row(&input, "BuildHistograms", 1).0, "retains");
}

/// Control, the walk continues from a field read: the body itself copies the
/// stored pointer out of its container into a static.
#[test]
fn wave6o_a_field_read_of_the_callee_container_is_followed() {
    let input = ITERATOR
        .replace(
            "pub unsafe fn BuildHistograms(",
            "static mut KEPT_SPLIT: *const BlockSplit = 0 as *const BlockSplit;\npub unsafe fn BuildHistograms(",
        )
        .replace(
            "    InitBlockSplitIterator(&mut literal_it, literal_split);\n",
            "    InitBlockSplitIterator(&mut literal_it, literal_split);\n    KEPT_SPLIT = literal_it.split_;\n",
        );
    assert!(
        input.contains("KEPT_SPLIT = literal_it.split_;"),
        "fixture edit applied"
    );
    assert_ne!(retention_row(&input, "BuildHistograms", 1).0, "no-retain");
}

/// Control, clause (1): the argument is read again after the storing call.
#[test]
fn wave6o_an_argument_live_after_the_storing_call_keeps_the_hold() {
    let input = ITERATOR.replace(
        "    InitBlockSplitIterator(&mut literal_it, literal_split);\n",
        "    InitBlockSplitIterator(&mut literal_it, literal_split);\n    let mut k = (*literal_split).num_types;\n    i = k.wrapping_sub(k);\n",
    );
    assert!(
        input.contains("(*literal_split).num_types"),
        "fixture edit applied"
    );
    assert_eq!(retention_row(&input, "BuildHistograms", 1).0, "retains");
}

/// Control, the residual: the argument ALSO reaches a foreign callee the walk
/// cannot see into, so the bounded store alone does not certify the row.
#[test]
fn wave6o_an_open_residual_keeps_the_callee_side_hold() {
    let input = ITERATOR
        .replace(
            "pub unsafe fn BuildHistograms(",
            "extern \"C\" { fn keep_split(_: *const BlockSplit); }\npub unsafe fn BuildHistograms(",
        )
        .replace(
            "    let mut i: usize = 0;\n    InitBlockSplitIterator(",
            "    let mut i: usize = 0;\n    keep_split(literal_split);\n    InitBlockSplitIterator(",
        );
    assert!(
        input.contains("keep_split(literal_split);"),
        "fixture edit applied"
    );
    assert_ne!(retention_row(&input, "BuildHistograms", 1).0, "no-retain");
}
