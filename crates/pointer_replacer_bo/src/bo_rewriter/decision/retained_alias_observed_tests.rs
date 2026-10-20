//! Wave-6o relay 146 (R796-1, USER): the retained-alias STOP-GAP for batch 55.
//! Exactly the formals whose Tree Borrows report the Miri runs have shown are
//! held raw (`held:retained-alias`, detail `observed:<run>`): bzip2's stream
//! (`handle_compress`, `BZ2_bzCompress`, `BZ2_bzDecompress::strm`) and libtree's
//! small vector (`small_vec_u64_init`, `small_vec_u64_append::v`,
//! `apply_exclude_list::needed_buf_offsets`). It is not the rule (relay 140's
//! R787-1); it holds what was observed, until the refined rule replaces it.
//! The fixtures carry the corpus names with an `obs_` prefix: the fixture table
//! must match no other lane's fixture (libtree's `small_vec_u64_init` is CE-M06's).

fn fixture(body: &str) -> String {
    format!(
        "#![allow(dead_code,unused_unsafe,unused_mut,unused_assignments,unused_variables,non_snake_case,non_camel_case_types)]\n{body}"
    )
}

/// bzip2's shape (`bzlib.c`): the state keeps a pointer back to the stream.
const BZIP2: &str = r###"
pub struct bz_stream {
    pub state: *mut EState,
    pub avail_in: u32,
    pub total_in_lo32: u32,
}
pub struct EState {
    pub strm: *mut bz_stream,
    pub mode: i32,
}
unsafe fn obs_copy_input_until_stop(mut s: *mut EState) {
    (*(*s).strm).avail_in = (*(*s).strm).avail_in.wrapping_sub(1);
    (*(*s).strm).total_in_lo32 = (*(*s).strm).total_in_lo32.wrapping_add(1);
}
unsafe fn obs_handle_compress(mut strm: *mut bz_stream) -> u8 {
    let mut s = (*strm).state;
    obs_copy_input_until_stop(s);
    (*strm).total_in_lo32 = (*strm).total_in_lo32.wrapping_add(0);
    1
}
pub unsafe fn obs_BZ2_bzCompress(mut strm: *mut bz_stream, mut action: i32) -> i32 {
    if strm.is_null() {
        return -2;
    }
    obs_handle_compress(strm) as i32
}
pub unsafe fn bump(mut c: *mut u32) {
    *c = (*c).wrapping_add(1);
}
pub unsafe fn caller(mut strm: *mut bz_stream, mut k: *mut u32) -> i32 {
    bump(k);
    obs_BZ2_bzCompress(strm, 0)
}
"###;

/// libtree's shape (`libtree.c`): a small vector whose pointer points into its
/// own buffer.
const LIBTREE: &str = r###"
pub struct small_vec_u64_t {
    pub buf: [u64; 16],
    pub p: *mut u64,
    pub n: usize,
}
unsafe fn obs_small_vec_u64_init(mut v: *mut small_vec_u64_t) {
    (*v).n = 0;
    (*v).p = ((*v).buf).as_mut_ptr();
}
unsafe fn obs_small_vec_u64_append(mut v: *mut small_vec_u64_t, mut x: u64) {
    *(*v).p.offset((*v).n as isize) = x;
    (*v).n = (*v).n.wrapping_add(1);
}
pub unsafe fn obs_use_vec() -> usize {
    let mut v = small_vec_u64_t { buf: [0; 16], p: 0 as *mut u64, n: 0 };
    obs_small_vec_u64_init(&mut v);
    obs_small_vec_u64_append(&mut v, 1);
    v.n
}
"###;

fn reasons(src: &str, fn_name: &str) -> Vec<(String, String)> {
    crate::bo_rewriter::emit_tests::artifact_rows_of(&fixture(src))
        .into_iter()
        .filter(|r| r.fn_path.ends_with(fn_name) && r.arg_index.is_some())
        .map(|r| {
            (
                r.param_name.clone().unwrap_or_default(),
                r.degrade_reason
                    .clone()
                    .unwrap_or_else(|| "<emitted>".to_owned()),
            )
        })
        .collect()
}

fn reason(rows: &[(String, String)], name: &str) -> String {
    rows.iter()
        .find(|(n, _)| n == name)
        .map(|(_, r)| r.clone())
        .unwrap_or_else(|| panic!("no formal {name}: {rows:?}"))
}

const HELD: &str = "held:retained-alias";

/// W1 — bzip2: the stream formals of the observed functions are held.
#[test]
fn w6o_r796_w1_bzip2_observed_stream_formals_are_held() {
    for f in ["obs_handle_compress", "obs_BZ2_bzCompress"] {
        let rows = reasons(BZIP2, f);
        assert_eq!(reason(&rows, "strm"), HELD, "{f}: {rows:?}");
    }
}

/// W2 — libtree: the observed small-vector formals are held.
#[test]
fn w6o_r796_w2_libtree_observed_vector_formals_are_held() {
    for f in ["obs_small_vec_u64_init", "obs_small_vec_u64_append"] {
        let rows = reasons(LIBTREE, f);
        assert_eq!(reason(&rows, "v"), HELD, "{f}: {rows:?}");
    }
}

/// C1 — nothing else: a formal not on the list keeps its reference.
#[test]
fn w6o_r796_c1_an_unlisted_formal_keeps_its_reference() {
    let rows = reasons(BZIP2, "bump");
    assert_eq!(reason(&rows, "c"), "<emitted>", "{rows:?}");
}
