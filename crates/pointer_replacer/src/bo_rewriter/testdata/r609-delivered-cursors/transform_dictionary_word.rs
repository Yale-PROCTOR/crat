#![allow(dead_code, unused_mut, unused_variables, unused_assignments, non_snake_case, non_camel_case_types, non_upper_case_globals, unused_unsafe)]
pub mod libc { pub type c_int = i32; pub type c_uint = u32; pub type c_long = i64; pub type c_ulong = u64; pub type c_char = i8; pub type c_short = i16; pub use core::ffi::c_void; }
pub type uint8_t = u8; pub type uint16_t = u16; pub type uint32_t = u32; pub type uint64_t = u64; pub type size_t = libc::c_ulong;
pub type __int16_t = libc::c_short;
pub type int16_t = __int16_t;
pub type BrotliWordTransformType = libc::c_uint;
pub const BROTLI_NUM_TRANSFORM_TYPES: BrotliWordTransformType =
    23;
pub const BROTLI_TRANSFORM_SHIFT_ALL: BrotliWordTransformType =
    22;
pub const BROTLI_TRANSFORM_SHIFT_FIRST: BrotliWordTransformType =
    21;
pub const BROTLI_TRANSFORM_OMIT_FIRST_9: BrotliWordTransformType =
    20;
pub const BROTLI_TRANSFORM_OMIT_FIRST_8: BrotliWordTransformType =
    19;
pub const BROTLI_TRANSFORM_OMIT_FIRST_7: BrotliWordTransformType =
    18;
pub const BROTLI_TRANSFORM_OMIT_FIRST_6: BrotliWordTransformType =
    17;
pub const BROTLI_TRANSFORM_OMIT_FIRST_5: BrotliWordTransformType =
    16;
pub const BROTLI_TRANSFORM_OMIT_FIRST_4: BrotliWordTransformType =
    15;
pub const BROTLI_TRANSFORM_OMIT_FIRST_3: BrotliWordTransformType =
    14;
pub const BROTLI_TRANSFORM_OMIT_FIRST_2: BrotliWordTransformType =
    13;
pub const BROTLI_TRANSFORM_OMIT_FIRST_1: BrotliWordTransformType =
    12;
pub const BROTLI_TRANSFORM_UPPERCASE_ALL: BrotliWordTransformType
    =
    11;
pub const BROTLI_TRANSFORM_UPPERCASE_FIRST:
    BrotliWordTransformType =
    10;
pub const BROTLI_TRANSFORM_OMIT_LAST_9: BrotliWordTransformType =
    9;
pub const BROTLI_TRANSFORM_OMIT_LAST_8: BrotliWordTransformType =
    8;
pub const BROTLI_TRANSFORM_OMIT_LAST_7: BrotliWordTransformType =
    7;
pub const BROTLI_TRANSFORM_OMIT_LAST_6: BrotliWordTransformType =
    6;
pub const BROTLI_TRANSFORM_OMIT_LAST_5: BrotliWordTransformType =
    5;
pub const BROTLI_TRANSFORM_OMIT_LAST_4: BrotliWordTransformType =
    4;
pub const BROTLI_TRANSFORM_OMIT_LAST_3: BrotliWordTransformType =
    3;
pub const BROTLI_TRANSFORM_OMIT_LAST_2: BrotliWordTransformType =
    2;
pub const BROTLI_TRANSFORM_OMIT_LAST_1: BrotliWordTransformType =
    1;
pub const BROTLI_TRANSFORM_IDENTITY: BrotliWordTransformType = 0;
#[repr(C)]
#[repr(C)]
pub struct BrotliTransforms {
    pub prefix_suffix_size: uint16_t,
    pub prefix_suffix: *const uint8_t,
    pub prefix_suffix_map: *const uint16_t,
    pub num_transforms: uint32_t,
    pub transforms: *const uint8_t,
    pub params: *const uint8_t,
    pub cutOffTransforms: [int16_t; 10],
}
unsafe extern "C" fn ToUpperCase(mut p: *mut uint8_t)
    -> libc::c_int {
    if (*p.offset(0 as libc::c_int as isize) as libc::c_int) <
            0xc0 as libc::c_int {
        if *p.offset(0 as libc::c_int as isize) as libc::c_int >=
                    'a' as i32 &&
                *p.offset(0 as libc::c_int as isize) as libc::c_int <=
                    'z' as i32 {
            *p.offset(0 as libc::c_int as isize) =
                (*p.offset(0 as libc::c_int as isize) as libc::c_int ^
                            32 as libc::c_int) as uint8_t;
        }
        return 1 as libc::c_int;
    }
    if (*p.offset(0 as libc::c_int as isize) as libc::c_int) <
            0xe0 as libc::c_int {
        *p.offset(1 as libc::c_int as isize) =
            (*p.offset(1 as libc::c_int as isize) as libc::c_int ^
                        32 as libc::c_int) as uint8_t;
        return 2 as libc::c_int;
    }
    *p.offset(2 as libc::c_int as isize) =
        (*p.offset(2 as libc::c_int as isize) as libc::c_int ^
                    5 as libc::c_int) as uint8_t;
    return 3 as libc::c_int;
}
unsafe extern "C" fn Shift(mut word: *mut uint8_t,
    mut word_len: libc::c_int, mut parameter: uint16_t)
    -> libc::c_int {
    let mut scalar =
        (parameter as libc::c_uint &
                    0x7fff as
                        libc::c_uint).wrapping_add((0x1000000 as
                        libc::c_uint).wrapping_sub(parameter as libc::c_uint &
                    0x8000 as libc::c_uint));
    if (*word.offset(0 as libc::c_int as isize) as libc::c_int) <
            0x80 as libc::c_int {
        scalar =
            (scalar as
                                libc::c_uint).wrapping_add(*word.offset(0 as libc::c_int as
                                        isize) as uint32_t) as uint32_t as uint32_t;
        *word.offset(0 as libc::c_int as isize) =
            (scalar & 0x7f as libc::c_uint) as uint8_t;
        return 1 as libc::c_int;
    } else {
        if (*word.offset(0 as libc::c_int as isize) as libc::c_int)
                < 0xc0 as libc::c_int {
            return 1 as libc::c_int
        } else {
            if (*word.offset(0 as libc::c_int as isize) as libc::c_int)
                    < 0xe0 as libc::c_int {
                if word_len < 2 as libc::c_int { return 1 as libc::c_int; }
                scalar =
                    (scalar as
                                        libc::c_uint).wrapping_add(*word.offset(1 as libc::c_int as
                                                        isize) as libc::c_uint & 0x3f as libc::c_uint |
                                    (*word.offset(0 as libc::c_int as isize) as libc::c_uint &
                                                0x1f as libc::c_uint) << 6 as libc::c_uint) as uint32_t as
                        uint32_t;
                *word.offset(0 as libc::c_int as isize) =
                    (0xc0 as libc::c_int as libc::c_uint |
                                scalar >> 6 as libc::c_uint &
                                    0x1f as libc::c_int as libc::c_uint) as uint8_t;
                *word.offset(1 as libc::c_int as isize) =
                    ((*word.offset(1 as libc::c_int as isize) as libc::c_int &
                                            0xc0 as libc::c_int) as libc::c_uint |
                                scalar & 0x3f as libc::c_int as libc::c_uint) as uint8_t;
                return 2 as libc::c_int;
            } else {
                if (*word.offset(0 as libc::c_int as isize) as libc::c_int)
                        < 0xf0 as libc::c_int {
                    if word_len < 3 as libc::c_int { return word_len; }
                    scalar =
                        (scalar as
                                            libc::c_uint).wrapping_add(*word.offset(2 as libc::c_int as
                                                                isize) as libc::c_uint & 0x3f as libc::c_uint |
                                            (*word.offset(1 as libc::c_int as isize) as libc::c_uint &
                                                        0x3f as libc::c_uint) << 6 as libc::c_uint |
                                        (*word.offset(0 as libc::c_int as isize) as libc::c_uint &
                                                    0xf as libc::c_uint) << 12 as libc::c_uint) as uint32_t as
                            uint32_t;
                    *word.offset(0 as libc::c_int as isize) =
                        (0xe0 as libc::c_int as libc::c_uint |
                                    scalar >> 12 as libc::c_uint &
                                        0xf as libc::c_int as libc::c_uint) as uint8_t;
                    *word.offset(1 as libc::c_int as isize) =
                        ((*word.offset(1 as libc::c_int as isize) as libc::c_int &
                                                0xc0 as libc::c_int) as libc::c_uint |
                                    scalar >> 6 as libc::c_uint &
                                        0x3f as libc::c_int as libc::c_uint) as uint8_t;
                    *word.offset(2 as libc::c_int as isize) =
                        ((*word.offset(2 as libc::c_int as isize) as libc::c_int &
                                                0xc0 as libc::c_int) as libc::c_uint |
                                    scalar & 0x3f as libc::c_int as libc::c_uint) as uint8_t;
                    return 3 as libc::c_int;
                } else {
                    if (*word.offset(0 as libc::c_int as isize) as libc::c_int)
                            < 0xf8 as libc::c_int {
                        if word_len < 4 as libc::c_int { return word_len; }
                        scalar =
                            (scalar as
                                                libc::c_uint).wrapping_add(*word.offset(3 as libc::c_int as
                                                                        isize) as libc::c_uint & 0x3f as libc::c_uint |
                                                    (*word.offset(2 as libc::c_int as isize) as libc::c_uint &
                                                                0x3f as libc::c_uint) << 6 as libc::c_uint |
                                                (*word.offset(1 as libc::c_int as isize) as libc::c_uint &
                                                            0x3f as libc::c_uint) << 12 as libc::c_uint |
                                            (*word.offset(0 as libc::c_int as isize) as libc::c_uint &
                                                        0x7 as libc::c_uint) << 18 as libc::c_uint) as uint32_t as
                                uint32_t;
                        *word.offset(0 as libc::c_int as isize) =
                            (0xf0 as libc::c_int as libc::c_uint |
                                        scalar >> 18 as libc::c_uint &
                                            0x7 as libc::c_int as libc::c_uint) as uint8_t;
                        *word.offset(1 as libc::c_int as isize) =
                            ((*word.offset(1 as libc::c_int as isize) as libc::c_int &
                                                    0xc0 as libc::c_int) as libc::c_uint |
                                        scalar >> 12 as libc::c_uint &
                                            0x3f as libc::c_int as libc::c_uint) as uint8_t;
                        *word.offset(2 as libc::c_int as isize) =
                            ((*word.offset(2 as libc::c_int as isize) as libc::c_int &
                                                    0xc0 as libc::c_int) as libc::c_uint |
                                        scalar >> 6 as libc::c_uint &
                                            0x3f as libc::c_int as libc::c_uint) as uint8_t;
                        *word.offset(3 as libc::c_int as isize) =
                            ((*word.offset(3 as libc::c_int as isize) as libc::c_int &
                                                    0xc0 as libc::c_int) as libc::c_uint |
                                        scalar & 0x3f as libc::c_int as libc::c_uint) as uint8_t;
                        return 4 as libc::c_int;
                    }
                }
            }
        }
    }
    return 1 as libc::c_int;
}
#[no_mangle]
pub unsafe extern "C" fn BrotliTransformDictionaryWord(mut dst:
        *mut uint8_t, mut word: *const uint8_t,
    mut len: libc::c_int, mut transforms: *const BrotliTransforms,
    mut transform_idx: libc::c_int) -> libc::c_int {
    let mut idx = 0 as libc::c_int;
    let mut prefix: *const uint8_t =
        &*((*transforms).prefix_suffix).offset(*((*transforms).prefix_suffix_map).offset(*((*transforms).transforms).offset((transform_idx
                                                                * 3 as libc::c_int + 0 as libc::c_int) as isize) as isize)
                            as isize) as *const uint8_t;
    let mut type_0 =
        *((*transforms).transforms).offset((transform_idx *
                                3 as libc::c_int + 1 as libc::c_int) as isize);
    let mut suffix: *const uint8_t =
        &*((*transforms).prefix_suffix).offset(*((*transforms).prefix_suffix_map).offset(*((*transforms).transforms).offset((transform_idx
                                                                * 3 as libc::c_int + 2 as libc::c_int) as isize) as isize)
                            as isize) as *const uint8_t;
    let fresh3 = *prefix;
    prefix = prefix.offset(1);
    let mut prefix_len = fresh3 as libc::c_int;
    loop {
        let fresh4 = prefix_len;
        prefix_len = prefix_len - 1;
        if !(fresh4 != 0) { break; }
        let fresh5 = *prefix;
        prefix = prefix.offset(1);
        let fresh6 = idx;
        idx = idx + 1;
        *dst.offset(fresh6 as isize) = fresh5;
    }
    let t = type_0 as libc::c_int;
    let mut i = 0 as libc::c_int;
    if t <= BROTLI_TRANSFORM_OMIT_LAST_9 as libc::c_int {
        len -= t;
    } else if t >= BROTLI_TRANSFORM_OMIT_FIRST_1 as libc::c_int &&
            t <= BROTLI_TRANSFORM_OMIT_FIRST_9 as libc::c_int {
        let mut skip =
            t -
                (BROTLI_TRANSFORM_OMIT_FIRST_1 as libc::c_int -
                        1 as libc::c_int);
        word = word.offset(skip as isize);
        len -= skip;
    }
    while i < len {
        let fresh7 = i;
        i = i + 1;
        let fresh8 = idx;
        idx = idx + 1;
        *dst.offset(fresh8 as isize) =
            *word.offset(fresh7 as isize);
    }
    if t == BROTLI_TRANSFORM_UPPERCASE_FIRST as libc::c_int {
        ToUpperCase(&mut *dst.offset((idx - len) as isize));
    } else if t == BROTLI_TRANSFORM_UPPERCASE_ALL as libc::c_int {
        let mut uppercase: *mut uint8_t =
            &mut *dst.offset((idx - len) as isize) as *mut uint8_t;
        while len > 0 as libc::c_int {
            let mut step = ToUpperCase(uppercase);
            uppercase = uppercase.offset(step as isize);
            len -= step;
        }
    } else if t == BROTLI_TRANSFORM_SHIFT_FIRST as libc::c_int {
        let mut param =
            (*((*transforms).params).offset((transform_idx *
                                                2 as libc::c_int) as isize) as libc::c_int +
                        ((*((*transforms).params).offset((transform_idx *
                                                                2 as libc::c_int + 1 as libc::c_int) as isize) as
                                        libc::c_int) << 8 as libc::c_uint)) as uint16_t;
        Shift(&mut *dst.offset((idx - len) as isize), len, param);
    } else if t == BROTLI_TRANSFORM_SHIFT_ALL as libc::c_int {
        let mut param_0 =
            (*((*transforms).params).offset((transform_idx *
                                                2 as libc::c_int) as isize) as libc::c_int +
                        ((*((*transforms).params).offset((transform_idx *
                                                                2 as libc::c_int + 1 as libc::c_int) as isize) as
                                        libc::c_int) << 8 as libc::c_uint)) as uint16_t;
        let mut shift: *mut uint8_t =
            &mut *dst.offset((idx - len) as isize) as *mut uint8_t;
        while len > 0 as libc::c_int {
            let mut step_0 = Shift(shift, len, param_0);
            shift = shift.offset(step_0 as isize);
            len -= step_0;
        }
    }
    let fresh9 = *suffix;
    suffix = suffix.offset(1);
    let mut suffix_len = fresh9 as libc::c_int;
    loop {
        let fresh10 = suffix_len;
        suffix_len = suffix_len - 1;
        if !(fresh10 != 0) { break; }
        let fresh11 = *suffix;
        suffix = suffix.offset(1);
        let fresh12 = idx;
        idx = idx + 1;
        *dst.offset(fresh12 as isize) = fresh11;
    }
    return idx;
}
