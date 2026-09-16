//! Reduced from brotli InitBlockSplitIterator / BlockSplitIteratorNext (report
//! 014 claim 7, relay 013 §2): a callee stores its shared argument into the
//! caller's frame-local iterator (`(*self_0).split_ = split`), and the only
//! later use of that local is a second address-of into a reader that loads
//! the stored pointer and reads through it. The two scan entries wave-6v2's
//! `frame_confined` certificate needs: the callee position modulo its
//! certified output storage, and the reader's loaded field.
const ITERATOR: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, static_mut_refs)]
pub struct Split { types: *const u8, lengths: *const u32, num: usize }
pub struct It { split_: *const Split, idx_: usize, type_: usize, length_: usize }
pub static mut KEEP: *const Split = core::ptr::null();
unsafe fn init(self_0: *mut It, split: *const Split) {
    (*self_0).split_ = split;
    (*self_0).idx_ = 0;
    (*self_0).type_ = 0;
    (*self_0).length_ = if !((*split).lengths).is_null() { *((*split).lengths).offset(0) } else { 0 } as usize;
}
unsafe fn init_and_keep(self_0: *mut It, split: *const Split) {
    (*self_0).split_ = split;
    KEEP = split;
}
unsafe fn init_via_local(self_0: *mut It, split: *const Split) {
    let mut it = It { split_: split, idx_: 0, type_: 0, length_: 0 };
    *self_0 = it;
}
unsafe fn next(self_0: *mut It) {
    if (*self_0).length_ == 0 {
        (*self_0).idx_ += 1;
        (*self_0).type_ = *((*(*self_0).split_).types).offset((*self_0).idx_ as isize) as usize;
        (*self_0).length_ = *((*(*self_0).split_).lengths).offset((*self_0).idx_ as isize) as usize;
    }
    (*self_0).length_ -= 1;
}
unsafe fn next_and_keep(self_0: *mut It) {
    KEEP = (*self_0).split_;
    (*self_0).length_ -= 1;
}
unsafe fn next_and_return(self_0: *mut It) -> *const Split {
    (*self_0).length_ -= 1;
    (*self_0).split_
}
unsafe fn next_and_forward(self_0: *mut It) {
    let s = (*self_0).split_;
    count(s);
}
unsafe fn count(s: *const Split) -> usize { (*s).num }
unsafe fn next_and_stash(self_0: *mut It, other: *mut It) {
    (*other).split_ = (*self_0).split_;
}
pub unsafe fn build(split: *const Split, n: usize) -> usize {
    let mut it = It { split_: core::ptr::null(), idx_: 0, type_: 0, length_: 0 };
    init(&mut it, split);
    let mut acc = 0usize;
    let mut i = 0usize;
    while i < n {
        next(&mut it);
        acc += it.type_;
        i += 1;
    }
    acc
}
"#;

fn with_functions<R: Send + 'static>(
    input: &str,
    f: impl FnOnce(
        rustc_middle::ty::TyCtxt<'_>,
        &[rustc_hir::def_id::LocalDefId],
        &dyn Fn(&str) -> rustc_hir::def_id::LocalDefId,
    ) -> R
    + Send,
) -> R {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let functions = tcx.hir_body_owners().collect::<Vec<_>>();
        let find = |name: &str| {
            functions
                .iter()
                .copied()
                .find(|owner| tcx.def_path_str(owner.to_def_id()) == name)
                .expect("the scanned function exists")
        };
        f(tcx, &functions, &find)
    })
    .expect("input type-checks")
}

fn callee_modulo_output(function: &str) -> (bool, bool) {
    with_functions(ITERATOR, |tcx, functions, find| {
        let target = find(function);
        (
            super::super::wave6r_child_access::position_is_descendant_free(
                tcx, functions, target, 1,
            ),
            super::super::wave6r_child_access::position_is_descendant_free_modulo_output(
                tcx, functions, target, 1, 0,
            ),
        )
    })
}

fn reader_field(function: &str) -> bool {
    with_functions(ITERATOR, |tcx, functions, find| {
        let target = find(function);
        super::super::wave6r_child_access::loaded_field_is_descendant_free(
            tcx,
            functions,
            target,
            0,
            rustc_abi::FieldIdx::from_usize(0),
        )
    })
}

#[test]
fn wave6r_iterator_init_stores_only_through_its_output() {
    let (plain, modulo) = callee_modulo_output("init");
    assert!(
        !plain,
        "the store through `self_0` is a hand-out for the plain scan"
    );
    assert!(
        modulo,
        "modulo the certified output storage the position is descendant-free"
    );
}

#[test]
fn wave6r_iterator_init_with_a_second_sink_stays_refused() {
    let (_, modulo) = callee_modulo_output("init_and_keep");
    assert!(
        !modulo,
        "a global store beside the output storage is not the certified sink"
    );
    let (_, modulo) = callee_modulo_output("init_via_local");
    assert!(
        !modulo,
        "an aggregate carrying the alias is not a store through the output"
    );
}

#[test]
fn wave6r_iterator_reader_only_reads_through_the_loaded_field() {
    assert!(
        reader_field("next"),
        "loads of `split_` are read through only"
    );
}

#[test]
fn wave6r_iterator_readers_hand_out_or_forward_the_loaded_field() {
    assert!(!reader_field("next_and_keep"), "global store");
    assert!(!reader_field("next_and_return"), "returned");
    assert!(
        reader_field("next_and_forward"),
        "forwarded to a local callee that only reads"
    );
    assert!(
        !reader_field("next_and_stash"),
        "stored through another pointer"
    );
}
