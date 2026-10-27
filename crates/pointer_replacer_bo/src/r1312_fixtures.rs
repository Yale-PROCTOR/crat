//! **R1312-1 (relay main/370) — the design notes' fixtures.** Reduced from the real inputs of 364's kept
//! trees (06-enum): the P01 address setters and buffer formals (A1 / A2), the cross-class collisions
//! (A5: P01's `SPX_set_tree_addr` → `SPX_ull_to_bytes`, `compress_bc5_lib`), and
//! `underhanded_c_nuke_lib` verbatim (B). Each fixture runs the step-7 entry
//! (`rewrite_bo_with_artifacts`) with the per-subject writer on; the probes print the rows and the emitted
//! source (copied under `R370_OUT` when set); the `w_*` witnesses assert the forms the notes propose and
//! are RED on the base by design.

use std::path::{Path, PathBuf};

const PRE: &str = "#![allow(dead_code, unused_mut, unused_unsafe, unused_assignments, unused_variables, \
                   non_camel_case_types, non_snake_case, non_upper_case_globals)]\n";

/// P01 `address.c` + `wots.c` / `sign.c` callers, reduced. `CAST` is the leaf caller's argument:
/// `leaf_addr as *mut uint32_t` (the input) or `leaf_addr`.
fn setters(leaf_arg: &str) -> String {
    format!(
        "{PRE}pub type uint32_t = core::ffi::c_uint;
pub type uint64_t = core::ffi::c_ulong;
pub const SPX_OFFSET_TREE: core::ffi::c_int = 8 as core::ffi::c_int;
pub const SPX_OFFSET_CHAIN_ADDR: core::ffi::c_int = 27 as core::ffi::c_int;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct leaf_info_x1 {{
    pub wots_sig: *mut core::ffi::c_uchar,
    pub wots_sign_leaf: uint32_t,
    pub leaf_addr: [uint32_t; 8],
    pub pk_addr: [uint32_t; 8],
}}
#[no_mangle]
pub unsafe extern \"C\" fn SPX_ull_to_bytes(mut out: *mut core::ffi::c_uchar,
    mut outlen: core::ffi::c_uint, mut in_0: core::ffi::c_ulonglong) {{
    let mut i: core::ffi::c_int = 0;
    i = outlen as core::ffi::c_int - 1 as core::ffi::c_int;
    while i >= 0 as core::ffi::c_int {{
        *out.offset(i as isize) = (in_0 & 0xff as core::ffi::c_ulonglong) as core::ffi::c_uchar;
        in_0 = in_0 >> 8 as core::ffi::c_int;
        i -= 1;
    }}
}}
#[no_mangle]
pub unsafe extern \"C\" fn SPX_set_tree_addr(mut addr: *mut uint32_t, mut tree: uint64_t) {{
    SPX_ull_to_bytes(&mut *(addr as *mut core::ffi::c_uchar).offset(SPX_OFFSET_TREE as isize),
        8 as core::ffi::c_uint, tree as core::ffi::c_ulonglong);
}}
#[no_mangle]
pub unsafe extern \"C\" fn SPX_set_chain_addr(mut addr: *mut uint32_t, mut chain: uint32_t) {{
    *(addr as *mut core::ffi::c_uchar).offset(SPX_OFFSET_CHAIN_ADDR as isize) =
        chain as core::ffi::c_uchar;
}}
#[no_mangle]
pub unsafe extern \"C\" fn SPX_wots_gen_leafx1(mut leaf_idx: uint32_t, mut v_info: *mut leaf_info_x1) {{
    let mut info: *mut leaf_info_x1 = v_info as *mut leaf_info_x1;
    let mut leaf_addr: *mut uint32_t = ((*info).leaf_addr).as_mut_ptr();
    SPX_set_chain_addr({leaf_arg}, leaf_idx);
}}
#[no_mangle]
pub unsafe extern \"C\" fn crypto_sign_signature(mut i: uint32_t) -> uint32_t {{
    let mut tree_addr: [uint32_t; 8] = [0 as core::ffi::c_int as uint32_t, 0, 0, 0, 0, 0, 0, 0];
    SPX_set_tree_addr(tree_addr.as_mut_ptr(), 7 as core::ffi::c_int as uint64_t);
    SPX_set_chain_addr(tree_addr.as_mut_ptr(), i);
    return tree_addr[6 as core::ffi::c_int as usize];
}}
"
    )
}

/// P01 blake `kat_tr_init` (A2's thin struct case) and shake `SPX_gen_message_random`'s `R` (A2's slice
/// case): an identity cast (a typedef) of a converting binding into a converting formal.
const A2: &str = "pub type uint8_t = core::ffi::c_uchar;
pub type uint32_t = core::ffi::c_uint;
pub type uint64_t = core::ffi::c_ulong;
pub type size_t = usize;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct blakestate256 {
    pub h: [uint32_t; 8],
    pub s: [uint32_t; 4],
    pub t: [uint32_t; 2],
    pub buflen: core::ffi::c_int,
    pub nullt: core::ffi::c_int,
    pub buf: [uint8_t; 64],
}
pub type kat_tr_ctx = blakestate256;
#[no_mangle]
pub unsafe extern \"C\" fn blake256_init(mut S: *mut blakestate256) {
    (*S).h[0 as core::ffi::c_int as usize] = 0x6a09e667 as core::ffi::c_uint;
    (*S).t[1 as core::ffi::c_int as usize] = 0 as core::ffi::c_int as uint32_t;
    (*S).t[0 as core::ffi::c_int as usize] = (*S).t[1 as core::ffi::c_int as usize];
    (*S).buflen = 0 as core::ffi::c_int;
    (*S).nullt = 0 as core::ffi::c_int;
}
unsafe extern \"C\" fn kat_tr_init(mut ctx: *mut kat_tr_ctx) {
    blake256_init(ctx as *mut blakestate256);
}
#[no_mangle]
pub unsafe extern \"C\" fn kat_tr_run() -> uint32_t {
    let mut ctx: kat_tr_ctx = blakestate256 { h: [0; 8], s: [0; 4], t: [0; 2], buflen: 0, nullt: 0, buf: [0; 64] };
    kat_tr_init(&mut ctx);
    return ctx.h[0 as core::ffi::c_int as usize];
}
unsafe extern \"C\" fn shake256_inc_squeeze(mut output: *mut uint8_t, mut outlen: size_t,
    mut s_inc: *mut uint64_t) {
    let mut i: size_t = 0;
    i = 0 as size_t;
    while i < outlen {
        *output.offset(i as isize) = (*s_inc.offset((i / 8) as isize) >> 8 * (i % 8)) as uint8_t;
        i = i.wrapping_add(1);
    }
}
#[no_mangle]
pub unsafe extern \"C\" fn SPX_gen_message_random(mut R: *mut core::ffi::c_uchar,
    mut sk_prf: *const core::ffi::c_uchar) {
    let mut s_inc: [uint64_t; 26] = [0; 26];
    s_inc[0 as core::ffi::c_int as usize] = *sk_prf.offset(0 as core::ffi::c_int as isize) as uint64_t;
    shake256_inc_squeeze(R as *mut uint8_t, 16 as core::ffi::c_int as size_t, s_inc.as_mut_ptr());
}
";

/// `compress_bc5_lib` (stb_dxt), the two functions of A5's four rows, verbatim but for the loop body.
const BC5: &str = "#[no_mangle]
pub unsafe extern \"C\" fn stb__CompressAlphaBlock(mut dest: *mut core::ffi::c_uchar,
    mut src: *mut core::ffi::c_uchar, mut stride: core::ffi::c_int) {
    let mut i: core::ffi::c_int = 0;
    let mut mn: core::ffi::c_int = 0;
    let mut mx: core::ffi::c_int = 0;
    mx = *src.offset(0 as core::ffi::c_int as isize) as core::ffi::c_int;
    mn = mx;
    i = 1 as core::ffi::c_int;
    while i < 16 as core::ffi::c_int {
        if (*src.offset((i * stride) as isize) as core::ffi::c_int) < mn {
            mn = *src.offset((i * stride) as isize) as core::ffi::c_int;
        } else if *src.offset((i * stride) as isize) as core::ffi::c_int > mx {
            mx = *src.offset((i * stride) as isize) as core::ffi::c_int;
        }
        i += 1;
    }
    *dest.offset(0 as core::ffi::c_int as isize) = mx as core::ffi::c_uchar;
    *dest.offset(1 as core::ffi::c_int as isize) = mn as core::ffi::c_uchar;
    dest = dest.offset(2 as core::ffi::c_int as isize);
    i = 0 as core::ffi::c_int;
    while i < 6 as core::ffi::c_int {
        *dest.offset(i as isize) = (mx - mn) as core::ffi::c_uchar;
        i += 1;
    }
}
#[no_mangle]
pub unsafe extern \"C\" fn compress_bc5(mut dest: *mut core::ffi::c_uchar,
    mut src: *const core::ffi::c_uchar) {
    stb__CompressAlphaBlock(dest, src as *mut core::ffi::c_uchar, 2 as core::ffi::c_int);
    stb__CompressAlphaBlock(dest.offset(8 as core::ffi::c_int as isize),
        (src as *mut core::ffi::c_uchar).offset(1 as core::ffi::c_int as isize), 2 as core::ffi::c_int);
}
";

/// `binary_heap` (`scheduler_print_task`) and `filesystem_example_lib` (`driver`), reduced: the other
/// five collision rows.
const HEAP_FS: &str = "extern \"C\" {
    fn printf(_: *const core::ffi::c_char, _: ...) -> core::ffi::c_int;
    fn strcmp(_: *const core::ffi::c_char, _: *const core::ffi::c_char) -> core::ffi::c_int;
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct SchedTask {
    pub priority: core::ffi::c_int,
    pub pid: core::ffi::c_int,
    pub class_name: [core::ffi::c_char; 16],
    pub command: [core::ffi::c_char; 32],
}
#[no_mangle]
pub unsafe extern \"C\" fn scheduler_print_task(mut task: *const SchedTask,
    mut prefix: *const core::ffi::c_char) {
    if task.is_null() {
        printf(b\"%s idle\\n\\0\" as *const u8 as *const core::ffi::c_char, prefix);
        return;
    }
    printf(b\"%s prio=%d pid=%d class=%s cmd=%s\\n\\0\" as *const u8 as *const core::ffi::c_char, prefix,
        (*task).priority, (*task).pid, ((*task).class_name).as_ptr(), ((*task).command).as_ptr());
}
unsafe extern \"C\" fn do_read(mut file_name: *const core::ffi::c_char) -> core::ffi::c_int {
    return *file_name.offset(0 as core::ffi::c_int as isize) as core::ffi::c_int;
}
#[no_mangle]
pub unsafe extern \"C\" fn driver(mut operation: *const core::ffi::c_char,
    mut file_name: *const core::ffi::c_char) -> core::ffi::c_int {
    if operation.is_null() {
        return 1 as core::ffi::c_int;
    }
    if strcmp(operation, b\"read\\0\" as *const u8 as *const core::ffi::c_char) == 0 as core::ffi::c_int {
        if file_name.is_null() {
            return 1 as core::ffi::c_int;
        }
        return do_read(file_name);
    }
    return 0 as core::ffi::c_int;
}
";

/// P01 shake (029): `shake256` → `shake256_absorb` / `shake256_squeezeblocks` → `keccak_*`, reduced
/// (A4's `call-site-not-adapted` rows `shake256_absorb::input`, `shake256_squeezeblocks::output`).
const SHAKE: &str = "pub type uint8_t = core::ffi::c_uchar;
pub type uint32_t = core::ffi::c_uint;
pub type uint64_t = core::ffi::c_ulong;
pub type size_t = usize;
pub const SHAKE256_RATE: core::ffi::c_int = 136 as core::ffi::c_int;
unsafe extern \"C\" fn load64(mut x: *const uint8_t) -> uint64_t {
    let mut r: uint64_t = 0 as uint64_t;
    let mut i: size_t = 0 as size_t;
    while i < 8 as size_t {
        r |= (*x.offset(i as isize) as uint64_t) << (8 as size_t).wrapping_mul(i);
        i = i.wrapping_add(1);
    }
    return r;
}
unsafe extern \"C\" fn store64(mut x: *mut uint8_t, mut u: uint64_t) {
    let mut i: size_t = 0 as size_t;
    while i < 8 as size_t {
        *x.offset(i as isize) = (u >> (8 as size_t).wrapping_mul(i)) as uint8_t;
        i = i.wrapping_add(1);
    }
}
unsafe extern \"C\" fn keccak_absorb(mut s: *mut uint64_t, mut r: uint32_t, mut m: *const uint8_t,
    mut mlen: size_t, mut p: uint8_t) {
    let mut i: size_t = 0;
    i = 0 as size_t;
    while i < 25 as size_t {
        *s.offset(i as isize) = 0 as uint64_t;
        i = i.wrapping_add(1);
    }
    while mlen >= r as size_t {
        i = 0 as size_t;
        while i < r.wrapping_div(8 as uint32_t) as size_t {
            *s.offset(i as isize) ^= load64(m.offset((8 as size_t).wrapping_mul(i) as isize));
            i = i.wrapping_add(1);
        }
        mlen = mlen.wrapping_sub(r as size_t);
        m = m.offset(r as isize);
    }
    *s.offset(0 as core::ffi::c_int as isize) ^= p as uint64_t;
}
unsafe extern \"C\" fn keccak_squeezeblocks(mut h: *mut uint8_t, mut nblocks: size_t,
    mut s: *mut uint64_t, mut r: uint32_t) {
    while nblocks > 0 as size_t {
        let mut i: size_t = 0 as size_t;
        while i < (r >> 3 as core::ffi::c_int) as size_t {
            store64(h.offset((8 as size_t).wrapping_mul(i) as isize), *s.offset(i as isize));
            i = i.wrapping_add(1);
        }
        h = h.offset(r as isize);
        nblocks = nblocks.wrapping_sub(1);
    }
}
#[no_mangle]
pub unsafe extern \"C\" fn shake256_absorb(mut s: *mut uint64_t, mut input: *const uint8_t,
    mut inlen: size_t) {
    keccak_absorb(s, SHAKE256_RATE as uint32_t, input, inlen, 0x1f as uint8_t);
}
#[no_mangle]
pub unsafe extern \"C\" fn shake256_squeezeblocks(mut output: *mut uint8_t, mut nblocks: size_t,
    mut s: *mut uint64_t) {
    keccak_squeezeblocks(output, nblocks, s, SHAKE256_RATE as uint32_t);
}
#[no_mangle]
pub unsafe extern \"C\" fn shake256(mut output: *mut uint8_t, mut outlen: size_t,
    mut input: *const uint8_t, mut inlen: size_t) {
    let mut nblocks: size_t = outlen.wrapping_div(SHAKE256_RATE as size_t);
    let mut t: [uint8_t; 136] = [0; 136];
    let mut s: [uint64_t; 25] = [0; 25];
    shake256_absorb(s.as_mut_ptr(), input, inlen);
    shake256_squeezeblocks(output, nblocks, s.as_mut_ptr());
    output = output.offset(nblocks.wrapping_mul(SHAKE256_RATE as size_t) as isize);
    outlen = outlen.wrapping_sub(nblocks.wrapping_mul(SHAKE256_RATE as size_t));
    if outlen != 0 {
        shake256_squeezeblocks(t.as_mut_ptr(), 1 as size_t, s.as_mut_ptr());
        let mut i: size_t = 0 as size_t;
        while i < outlen {
            *output.offset(i as isize) = t[i as usize];
            i = i.wrapping_add(1);
        }
    }
}
#[no_mangle]
pub unsafe extern \"C\" fn thash(mut out: *mut core::ffi::c_uchar, mut inp: *const core::ffi::c_uchar) {
    let mut buf: [uint8_t; 64] = [0; 64];
    buf[0 as core::ffi::c_int as usize] = *inp.offset(0 as core::ffi::c_int as isize);
    shake256(out as *mut uint8_t, 16 as core::ffi::c_int as size_t, buf.as_ptr(), 64 as core::ffi::c_int as size_t);
}
";

/// A3 (`slice-cursor-use`), reduced from the real inputs: P01 `randombytes` (an offset argument into a foreign
/// `memcpy`), `merge_sort_lib` (offset arguments into thin formals), P01 `blake256_update` (a self-advance) and
/// `load_png_mem_lib`'s `cp_get_chunk_byte_length` (a negative offset argument).
const A3: &str = "extern \"C\" {
    fn memcpy(_: *mut core::ffi::c_void, _: *const core::ffi::c_void, _: usize) -> *mut core::ffi::c_void;
}
#[no_mangle]
pub unsafe extern \"C\" fn randombytes(mut x: *mut core::ffi::c_uchar, mut xlen: core::ffi::c_ulonglong)
    -> core::ffi::c_int {
    let mut block: [core::ffi::c_uchar; 16] = [0; 16];
    let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
    while xlen > 0 as core::ffi::c_ulonglong {
        block[0 as core::ffi::c_int as usize] = (block[0 as core::ffi::c_int as usize]).wrapping_add(1);
        if xlen > 15 as core::ffi::c_ulonglong {
            memcpy(x.offset(i as isize) as *mut core::ffi::c_void,
                block.as_mut_ptr() as *const core::ffi::c_void, 16 as usize);
            i += 16 as core::ffi::c_int;
            xlen = xlen.wrapping_sub(16 as core::ffi::c_ulonglong);
        } else {
            memcpy(x.offset(i as isize) as *mut core::ffi::c_void,
                block.as_mut_ptr() as *const core::ffi::c_void, xlen as usize);
            xlen = 0 as core::ffi::c_ulonglong;
        }
    }
    return 0 as core::ffi::c_int;
}
#[derive(Copy, Clone)]
#[repr(C)]
pub struct spritebatch_sprite_t {
    pub sort_bits: core::ffi::c_ulonglong,
    pub w: core::ffi::c_int,
}
unsafe extern \"C\" fn sprite_less_than_or_equal(mut a: *const spritebatch_sprite_t,
    mut b: *const spritebatch_sprite_t) -> core::ffi::c_int {
    return ((*a).sort_bits <= (*b).sort_bits) as core::ffi::c_int;
}
#[no_mangle]
pub unsafe extern \"C\" fn merge_sort_iteration(mut a: *mut spritebatch_sprite_t, mut n: core::ffi::c_int)
    -> core::ffi::c_int {
    let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
    let mut j: core::ffi::c_int = n - 1 as core::ffi::c_int;
    let mut count: core::ffi::c_int = 0 as core::ffi::c_int;
    while i < j {
        if sprite_less_than_or_equal(a.offset(i as isize), a.offset(j as isize)) != 0 {
            count += 1;
        }
        i += 1;
    }
    return count;
}
#[no_mangle]
pub unsafe extern \"C\" fn blake_absorb(mut data: *const core::ffi::c_uchar, mut datalen: core::ffi::c_ulonglong)
    -> core::ffi::c_uint {
    let mut acc: core::ffi::c_uint = 0 as core::ffi::c_uint;
    while datalen >= 64 as core::ffi::c_ulonglong {
        acc = acc.wrapping_add(*data.offset(0 as core::ffi::c_int as isize) as core::ffi::c_uint);
        data = data.offset(64 as core::ffi::c_int as isize);
        datalen = datalen.wrapping_sub(64 as core::ffi::c_ulonglong);
    }
    let mut k: core::ffi::c_ulonglong = 0 as core::ffi::c_ulonglong;
    while k < datalen {
        acc = acc.wrapping_add(*data.offset(k as isize) as core::ffi::c_uint);
        k = k.wrapping_add(1);
    }
    return acc;
}
unsafe extern \"C\" fn cp_make32(mut b: *const core::ffi::c_uchar) -> core::ffi::c_uint {
    return (*b.offset(0 as core::ffi::c_int as isize) as core::ffi::c_uint) << 24 as core::ffi::c_int
        | *b.offset(3 as core::ffi::c_int as isize) as core::ffi::c_uint;
}
#[no_mangle]
pub unsafe extern \"C\" fn cp_get_chunk_byte_length(mut chunk: *const core::ffi::c_uchar) -> core::ffi::c_uint {
    return cp_make32(chunk.offset(-(8 as core::ffi::c_int as isize)));
}
";

/// A4 (`slice-use-unsupported`), reduced from P01 `kat_tr_absorb_label`: a NUL-walked local cast (an identity
/// under the typedef) into a slice formal.
const A4: &str = "pub type uint8_t = core::ffi::c_uchar;
pub type size_t = usize;
unsafe extern \"C\" fn absorb_bytes(mut data: *const core::ffi::c_uchar, mut datalen: core::ffi::c_ulonglong)
    -> core::ffi::c_uint {
    let mut acc: core::ffi::c_uint = 0 as core::ffi::c_uint;
    let mut k: core::ffi::c_ulonglong = 0 as core::ffi::c_ulonglong;
    while k < datalen {
        acc = acc.wrapping_add(*data.offset(k as isize) as core::ffi::c_uint);
        k = k.wrapping_add(1);
    }
    return acc;
}
#[no_mangle]
pub unsafe extern \"C\" fn kat_tr_absorb_label(mut label: *const core::ffi::c_char) -> core::ffi::c_uint {
    let mut p: *const uint8_t = label as *const uint8_t;
    let mut n: size_t = 0 as size_t;
    while *p.offset(n as isize) != 0 {
        n = n.wrapping_add(1);
    }
    return absorb_bytes(p as *const core::ffi::c_uchar, n as core::ffi::c_ulonglong);
}
";

fn nuke() -> String {
    std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("src/r1312_fixtures/underhanded_c_nuke_lib.rs"),
    )
    .unwrap()
}

/// One step-7 run of `source` with the writer on: (emitted lib.rs, subjects.tsv, class_collisions.tsv).
fn run(tag: &str, source: &str) -> (String, String, String) {
    let dir = std::env::temp_dir().join(format!("crat-r1312-{tag}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("lib.rs"), source).unwrap();
    let artifacts = dir.join("artifacts");
    let receipt =
        crate::bo_pipeline::rewrite_bo_with_artifacts(&dir.join("lib.rs"), [], Some(&artifacts));
    let emitted = std::fs::read_to_string(dir.join("lib.rs")).unwrap();
    let read = |name: &str| std::fs::read_to_string(artifacts.join(name)).unwrap_or_default();
    let (subjects, collisions) = (read("subjects.tsv"), read("class_collisions.tsv"));
    if let Some(out) = std::env::var_os("R370_OUT") {
        let out = PathBuf::from(out).join(tag);
        let _ = std::fs::remove_dir_all(&out);
        std::fs::create_dir_all(&out).unwrap();
        std::fs::write(out.join("input.rs"), source).unwrap();
        std::fs::write(out.join("emitted.rs"), &emitted).unwrap();
        std::fs::write(
            out.join("receipt.txt"),
            match &receipt {
                Ok(r) => format!(
                    "outcome {} status {} verify_rounds {} reverted {} files {}/{}\n",
                    r.outcome,
                    r.status,
                    r.verify_rounds,
                    r.reverted_count,
                    r.files_changed,
                    r.files_total
                ),
                Err(e) => format!("error {e}\n"),
            },
        )
        .unwrap();
        for entry in std::fs::read_dir(&artifacts)
            .into_iter()
            .flatten()
            .flatten()
        {
            std::fs::copy(entry.path(), out.join(entry.file_name())).unwrap();
        }
    }
    std::fs::remove_dir_all(&dir).unwrap();
    (emitted, subjects, collisions)
}

/// `label → (decision, reason, exclusion, outcome, first_hold_reason)` from subjects.tsv.
fn rows(subjects: &str) -> std::collections::BTreeMap<String, Vec<String>> {
    let mut lines = subjects.lines();
    let header: Vec<&str> = lines.next().unwrap_or_default().split('\t').collect();
    let at = |name: &str| header.iter().position(|h| *h == name).unwrap();
    lines
        .map(|line| {
            let cells: Vec<&str> = line.split('\t').collect();
            let get = |name: &str| cells[at(name)].to_owned();
            (
                get("label"),
                vec![
                    get("decision"),
                    get("reason"),
                    get("exclusion"),
                    get("outcome"),
                    get("first_hold_reason"),
                ],
            )
        })
        .collect()
}

fn flat(source: &str) -> String {
    source.split_whitespace().collect::<Vec<_>>().join(" ")
}

#[test]
fn r1312_probe_all() {
    for (tag, source) in [
        ("a1-setters-cast", setters("leaf_addr as *mut uint32_t")),
        ("a1-setters-nocast", setters("leaf_addr")),
        ("a2", format!("{PRE}{A2}")),
        ("a5-bc5", format!("{PRE}{BC5}")),
        ("a5-heap-fs", format!("{PRE}{HEAP_FS}")),
        ("a3", format!("{PRE}{A3}")),
        ("a4", format!("{PRE}{A4}")),
        ("a4-shake", format!("{PRE}{SHAKE}")),
        (
            "a4-shake-fat-caller",
            format!("{PRE}{SHAKE}").replace(
                "    let mut nblocks: size_t = outlen",
                "    let mut first: uint8_t = *input.offset(1 as core::ffi::c_int as isize);\n    let mut nblocks: size_t = outlen",
            ),
        ),
        ("b-nuke", nuke()),
    ] {
        let (_, subjects, collisions) = run(tag, &source);
        eprintln!("==== {tag}");
        for (label, cells) in rows(&subjects) {
            eprintln!("  {label}\t{}", cells.join("\t"));
        }
        eprintln!("  collisions:\n{collisions}");
    }
}

/// A1 (cast strip): the leaf caller's identity cast no longer holds the setter's formal.
#[test]
#[ignore = "relay 371 step 3 (the strip): RED until that step"]
fn r1312_w_a1_identity_cast_does_not_hold_the_formal() {
    let (emitted, subjects, _) = run("w-a1", &setters("leaf_addr as *mut uint32_t"));
    let r = rows(&subjects);
    assert_ne!(
        r["SPX_set_chain_addr::addr"][1], "arg-cast-form-unbuilt",
        "{r:#?}"
    );
    assert!(
        !flat(&emitted).contains("SPX_set_chain_addr(leaf_addr as *mut uint32_t"),
        "{emitted}"
    );
}

/// A1 (byte view): the setter's formal reaches byte 27 of the caller's `[u32; 8]`; it must carry the
/// caller's extent (a slice), never a thin `&mut u32` whose four bytes the write leaves.
#[test]
#[ignore = "relay 371 step 2 (the cast-offset need): RED until that step"]
fn r1312_w_a1_byte_offset_formal_is_a_slice() {
    let (emitted, _, _) = run("w-a1b", &setters("leaf_addr"));
    let text = flat(&emitted);
    assert!(
        !text.contains("fn SPX_set_chain_addr(mut addr: &mut uint32_t"),
        "{emitted}"
    );
    assert!(
        !text.contains("fn __crat_safe_SPX_set_chain_addr(mut addr: &mut uint32_t"),
        "{emitted}"
    );
}

/// A2: a typedef-identity cast of a converting binding into a converting formal is stripped.
#[test]
#[ignore = "relay 371 step 3 (the strip): RED until that step"]
fn r1312_w_a2_typedef_identity_cast_is_stripped() {
    let (_, subjects, _) = run("w-a2", &format!("{PRE}{A2}"));
    let r = rows(&subjects);
    for label in ["kat_tr_init::ctx", "SPX_gen_message_random::R"] {
        assert_ne!(r[label][1], "cast-of-converting-local", "{label}: {r:#?}");
    }
}

/// A5: the two classes of one argument interval compose; neither is held for the collision.
#[test]
#[ignore = "relay 371 step 2 (the cast-offset need): RED until that step"]
fn r1312_w_a5_collision_composes() {
    let (_, subjects, _) = run("w-a5", &setters("leaf_addr"));
    let r = rows(&subjects);
    for label in ["SPX_set_tree_addr::addr", "SPX_ull_to_bytes::out"] {
        assert!(
            !r[label][2].contains("cross-class-interval-collision"),
            "{label}: {r:#?}"
        );
    }
}

/// B2: no one-element view (`core::slice::from_mut` / `from_ref`) reaches a slice-decided formal.
#[test]
fn r1312_w_b_no_one_element_view_into_a_slice_formal() {
    let (emitted, _, _) = run("w-b2", &nuke());
    assert!(
        !emitted.contains("core::slice::from_mut(") && !emitted.contains("core::slice::from_ref("),
        "{emitted}"
    );
}

/// B: the test vector's call (`match` over 1024 bins, the input's own sizes) runs on the emitted program:
/// `normalize` and `dot_product` index `length` elements of what `spectral_contrast` passes them.
#[test]
fn r1312_w_b_test_vector_runs() {
    let (emitted, _, _) = run("w-b", &nuke());
    let program = format!(
        "{emitted}\nfn main() {{ let mut t = vec![0.0f64; 1024]; let mut r = vec![0.0f64; 1024];\n\
         for i in 0..1024 {{ t[i] = (i % 7) as f64 + 1.0; r[i] = (i % 5) as f64 + 1.0; }}\n\
         let m = unsafe {{ crate::src::r#match::match_0(t.as_mut_ptr(), r.as_mut_ptr(), 1024, 0.5) }};\n\
         println!(\"{{m}}\"); }}\n"
    );
    let dir = std::env::temp_dir().join(format!("crat-r1312-run-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("main.rs"), &program).unwrap();
    let built = std::process::Command::new("rustc")
        .args(["--edition=2021", "-Awarnings", "--crate-type=bin"])
        .arg(dir.join("main.rs"))
        .arg("-o")
        .arg(dir.join("main"))
        .output()
        .unwrap();
    assert!(
        built.status.success(),
        "build: {}",
        String::from_utf8_lossy(&built.stderr)
    );
    let ran = std::process::Command::new(dir.join("main"))
        .output()
        .unwrap();
    std::fs::remove_dir_all(&dir).unwrap();
    assert!(
        ran.status.success(),
        "run: {}",
        String::from_utf8_lossy(&ran.stderr)
    );
}

/// A3: an offset argument takes the element / sub-slice form, the negative offset a cursor. None of the three
/// is held `slice-cursor-use`.
#[test]
#[ignore = "relay 371 step 4 (A3): RED until that step"]
fn r1312_w_a3_offset_arguments_deliver() {
    let (_, subjects, _) = run("w-a3", &format!("{PRE}{A3}"));
    let r = rows(&subjects);
    for label in [
        "randombytes::x",
        "merge_sort_iteration::a",
        "cp_get_chunk_byte_length::chunk",
    ] {
        assert_eq!(r[label][3], "delivered", "{label}: {r:#?}");
    }
}

/// A3's control (GREEN on the base): a plain non-negative self-advance of a shared slice already delivers as
/// `data = &data[64..]`; the real `blake256_update::data` is held by its cast arguments, not by the advance.
#[test]
fn r1312_c_a3_self_advance_already_delivers() {
    let (emitted, subjects, _) = run("c-a3", &format!("{PRE}{A3}"));
    assert_eq!(rows(&subjects)["blake_absorb::data"][3], "delivered");
    assert!(
        flat(&emitted).contains("data = &data[(64 as core::ffi::c_int) as usize..];"),
        "{emitted}"
    );
}

/// A4: the identity cast of a delivered slice into a slice formal is stripped (the NUL-walked label).
#[test]
#[ignore = "relay 371 step 5 (A4): RED until that step"]
fn r1312_w_a4_identity_cast_of_a_slice_into_a_slice_formal_delivers() {
    let (_, subjects, _) = run("w-a4", &format!("{PRE}{A4}"));
    let r = rows(&subjects);
    assert_eq!(r["kat_tr_absorb_label::p"][3], "delivered", "{r:#?}");
}
