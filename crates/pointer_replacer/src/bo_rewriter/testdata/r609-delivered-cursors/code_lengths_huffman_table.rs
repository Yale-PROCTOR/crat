#![allow(dead_code, unused_mut, unused_variables, unused_assignments, non_snake_case, non_camel_case_types, non_upper_case_globals, unused_unsafe)]
pub mod libc { pub type c_int = i32; pub type c_uint = u32; pub type c_long = i64; pub type c_ulong = u64; pub type c_char = i8; pub type c_short = i16; pub use core::ffi::c_void; }
pub type uint8_t = u8; pub type uint16_t = u16; pub type uint32_t = u32; pub type uint64_t = u64; pub type size_t = libc::c_ulong;
#[derive(Copy, Clone)]
#[repr(C)]
pub struct HuffmanCode {
    pub bits: uint8_t,
    pub value: uint16_t,
}
#[inline(always)]
unsafe extern "C" fn ConstructHuffmanCode(bits: uint8_t,
    value: uint16_t) -> HuffmanCode {
    let mut h = HuffmanCode { bits: 0, value: 0 };
    h.bits = bits;
    h.value = value;
    return h;
}
static mut kReverseBits: [uint8_t; 256] =
    [0 as libc::c_int as uint8_t, 0x80 as libc::c_int as uint8_t,
            0x40 as libc::c_int as uint8_t,
            0xc0 as libc::c_int as uint8_t,
            0x20 as libc::c_int as uint8_t,
            0xa0 as libc::c_int as uint8_t,
            0x60 as libc::c_int as uint8_t,
            0xe0 as libc::c_int as uint8_t,
            0x10 as libc::c_int as uint8_t,
            0x90 as libc::c_int as uint8_t,
            0x50 as libc::c_int as uint8_t,
            0xd0 as libc::c_int as uint8_t,
            0x30 as libc::c_int as uint8_t,
            0xb0 as libc::c_int as uint8_t,
            0x70 as libc::c_int as uint8_t,
            0xf0 as libc::c_int as uint8_t,
            0x8 as libc::c_int as uint8_t,
            0x88 as libc::c_int as uint8_t,
            0x48 as libc::c_int as uint8_t,
            0xc8 as libc::c_int as uint8_t,
            0x28 as libc::c_int as uint8_t,
            0xa8 as libc::c_int as uint8_t,
            0x68 as libc::c_int as uint8_t,
            0xe8 as libc::c_int as uint8_t,
            0x18 as libc::c_int as uint8_t,
            0x98 as libc::c_int as uint8_t,
            0x58 as libc::c_int as uint8_t,
            0xd8 as libc::c_int as uint8_t,
            0x38 as libc::c_int as uint8_t,
            0xb8 as libc::c_int as uint8_t,
            0x78 as libc::c_int as uint8_t,
            0xf8 as libc::c_int as uint8_t,
            0x4 as libc::c_int as uint8_t,
            0x84 as libc::c_int as uint8_t,
            0x44 as libc::c_int as uint8_t,
            0xc4 as libc::c_int as uint8_t,
            0x24 as libc::c_int as uint8_t,
            0xa4 as libc::c_int as uint8_t,
            0x64 as libc::c_int as uint8_t,
            0xe4 as libc::c_int as uint8_t,
            0x14 as libc::c_int as uint8_t,
            0x94 as libc::c_int as uint8_t,
            0x54 as libc::c_int as uint8_t,
            0xd4 as libc::c_int as uint8_t,
            0x34 as libc::c_int as uint8_t,
            0xb4 as libc::c_int as uint8_t,
            0x74 as libc::c_int as uint8_t,
            0xf4 as libc::c_int as uint8_t,
            0xc as libc::c_int as uint8_t,
            0x8c as libc::c_int as uint8_t,
            0x4c as libc::c_int as uint8_t,
            0xcc as libc::c_int as uint8_t,
            0x2c as libc::c_int as uint8_t,
            0xac as libc::c_int as uint8_t,
            0x6c as libc::c_int as uint8_t,
            0xec as libc::c_int as uint8_t,
            0x1c as libc::c_int as uint8_t,
            0x9c as libc::c_int as uint8_t,
            0x5c as libc::c_int as uint8_t,
            0xdc as libc::c_int as uint8_t,
            0x3c as libc::c_int as uint8_t,
            0xbc as libc::c_int as uint8_t,
            0x7c as libc::c_int as uint8_t,
            0xfc as libc::c_int as uint8_t,
            0x2 as libc::c_int as uint8_t,
            0x82 as libc::c_int as uint8_t,
            0x42 as libc::c_int as uint8_t,
            0xc2 as libc::c_int as uint8_t,
            0x22 as libc::c_int as uint8_t,
            0xa2 as libc::c_int as uint8_t,
            0x62 as libc::c_int as uint8_t,
            0xe2 as libc::c_int as uint8_t,
            0x12 as libc::c_int as uint8_t,
            0x92 as libc::c_int as uint8_t,
            0x52 as libc::c_int as uint8_t,
            0xd2 as libc::c_int as uint8_t,
            0x32 as libc::c_int as uint8_t,
            0xb2 as libc::c_int as uint8_t,
            0x72 as libc::c_int as uint8_t,
            0xf2 as libc::c_int as uint8_t,
            0xa as libc::c_int as uint8_t,
            0x8a as libc::c_int as uint8_t,
            0x4a as libc::c_int as uint8_t,
            0xca as libc::c_int as uint8_t,
            0x2a as libc::c_int as uint8_t,
            0xaa as libc::c_int as uint8_t,
            0x6a as libc::c_int as uint8_t,
            0xea as libc::c_int as uint8_t,
            0x1a as libc::c_int as uint8_t,
            0x9a as libc::c_int as uint8_t,
            0x5a as libc::c_int as uint8_t,
            0xda as libc::c_int as uint8_t,
            0x3a as libc::c_int as uint8_t,
            0xba as libc::c_int as uint8_t,
            0x7a as libc::c_int as uint8_t,
            0xfa as libc::c_int as uint8_t,
            0x6 as libc::c_int as uint8_t,
            0x86 as libc::c_int as uint8_t,
            0x46 as libc::c_int as uint8_t,
            0xc6 as libc::c_int as uint8_t,
            0x26 as libc::c_int as uint8_t,
            0xa6 as libc::c_int as uint8_t,
            0x66 as libc::c_int as uint8_t,
            0xe6 as libc::c_int as uint8_t,
            0x16 as libc::c_int as uint8_t,
            0x96 as libc::c_int as uint8_t,
            0x56 as libc::c_int as uint8_t,
            0xd6 as libc::c_int as uint8_t,
            0x36 as libc::c_int as uint8_t,
            0xb6 as libc::c_int as uint8_t,
            0x76 as libc::c_int as uint8_t,
            0xf6 as libc::c_int as uint8_t,
            0xe as libc::c_int as uint8_t,
            0x8e as libc::c_int as uint8_t,
            0x4e as libc::c_int as uint8_t,
            0xce as libc::c_int as uint8_t,
            0x2e as libc::c_int as uint8_t,
            0xae as libc::c_int as uint8_t,
            0x6e as libc::c_int as uint8_t,
            0xee as libc::c_int as uint8_t,
            0x1e as libc::c_int as uint8_t,
            0x9e as libc::c_int as uint8_t,
            0x5e as libc::c_int as uint8_t,
            0xde as libc::c_int as uint8_t,
            0x3e as libc::c_int as uint8_t,
            0xbe as libc::c_int as uint8_t,
            0x7e as libc::c_int as uint8_t,
            0xfe as libc::c_int as uint8_t,
            0x1 as libc::c_int as uint8_t,
            0x81 as libc::c_int as uint8_t,
            0x41 as libc::c_int as uint8_t,
            0xc1 as libc::c_int as uint8_t,
            0x21 as libc::c_int as uint8_t,
            0xa1 as libc::c_int as uint8_t,
            0x61 as libc::c_int as uint8_t,
            0xe1 as libc::c_int as uint8_t,
            0x11 as libc::c_int as uint8_t,
            0x91 as libc::c_int as uint8_t,
            0x51 as libc::c_int as uint8_t,
            0xd1 as libc::c_int as uint8_t,
            0x31 as libc::c_int as uint8_t,
            0xb1 as libc::c_int as uint8_t,
            0x71 as libc::c_int as uint8_t,
            0xf1 as libc::c_int as uint8_t,
            0x9 as libc::c_int as uint8_t,
            0x89 as libc::c_int as uint8_t,
            0x49 as libc::c_int as uint8_t,
            0xc9 as libc::c_int as uint8_t,
            0x29 as libc::c_int as uint8_t,
            0xa9 as libc::c_int as uint8_t,
            0x69 as libc::c_int as uint8_t,
            0xe9 as libc::c_int as uint8_t,
            0x19 as libc::c_int as uint8_t,
            0x99 as libc::c_int as uint8_t,
            0x59 as libc::c_int as uint8_t,
            0xd9 as libc::c_int as uint8_t,
            0x39 as libc::c_int as uint8_t,
            0xb9 as libc::c_int as uint8_t,
            0x79 as libc::c_int as uint8_t,
            0xf9 as libc::c_int as uint8_t,
            0x5 as libc::c_int as uint8_t,
            0x85 as libc::c_int as uint8_t,
            0x45 as libc::c_int as uint8_t,
            0xc5 as libc::c_int as uint8_t,
            0x25 as libc::c_int as uint8_t,
            0xa5 as libc::c_int as uint8_t,
            0x65 as libc::c_int as uint8_t,
            0xe5 as libc::c_int as uint8_t,
            0x15 as libc::c_int as uint8_t,
            0x95 as libc::c_int as uint8_t,
            0x55 as libc::c_int as uint8_t,
            0xd5 as libc::c_int as uint8_t,
            0x35 as libc::c_int as uint8_t,
            0xb5 as libc::c_int as uint8_t,
            0x75 as libc::c_int as uint8_t,
            0xf5 as libc::c_int as uint8_t,
            0xd as libc::c_int as uint8_t,
            0x8d as libc::c_int as uint8_t,
            0x4d as libc::c_int as uint8_t,
            0xcd as libc::c_int as uint8_t,
            0x2d as libc::c_int as uint8_t,
            0xad as libc::c_int as uint8_t,
            0x6d as libc::c_int as uint8_t,
            0xed as libc::c_int as uint8_t,
            0x1d as libc::c_int as uint8_t,
            0x9d as libc::c_int as uint8_t,
            0x5d as libc::c_int as uint8_t,
            0xdd as libc::c_int as uint8_t,
            0x3d as libc::c_int as uint8_t,
            0xbd as libc::c_int as uint8_t,
            0x7d as libc::c_int as uint8_t,
            0xfd as libc::c_int as uint8_t,
            0x3 as libc::c_int as uint8_t,
            0x83 as libc::c_int as uint8_t,
            0x43 as libc::c_int as uint8_t,
            0xc3 as libc::c_int as uint8_t,
            0x23 as libc::c_int as uint8_t,
            0xa3 as libc::c_int as uint8_t,
            0x63 as libc::c_int as uint8_t,
            0xe3 as libc::c_int as uint8_t,
            0x13 as libc::c_int as uint8_t,
            0x93 as libc::c_int as uint8_t,
            0x53 as libc::c_int as uint8_t,
            0xd3 as libc::c_int as uint8_t,
            0x33 as libc::c_int as uint8_t,
            0xb3 as libc::c_int as uint8_t,
            0x73 as libc::c_int as uint8_t,
            0xf3 as libc::c_int as uint8_t,
            0xb as libc::c_int as uint8_t,
            0x8b as libc::c_int as uint8_t,
            0x4b as libc::c_int as uint8_t,
            0xcb as libc::c_int as uint8_t,
            0x2b as libc::c_int as uint8_t,
            0xab as libc::c_int as uint8_t,
            0x6b as libc::c_int as uint8_t,
            0xeb as libc::c_int as uint8_t,
            0x1b as libc::c_int as uint8_t,
            0x9b as libc::c_int as uint8_t,
            0x5b as libc::c_int as uint8_t,
            0xdb as libc::c_int as uint8_t,
            0x3b as libc::c_int as uint8_t,
            0xbb as libc::c_int as uint8_t,
            0x7b as libc::c_int as uint8_t,
            0xfb as libc::c_int as uint8_t,
            0x7 as libc::c_int as uint8_t,
            0x87 as libc::c_int as uint8_t,
            0x47 as libc::c_int as uint8_t,
            0xc7 as libc::c_int as uint8_t,
            0x27 as libc::c_int as uint8_t,
            0xa7 as libc::c_int as uint8_t,
            0x67 as libc::c_int as uint8_t,
            0xe7 as libc::c_int as uint8_t,
            0x17 as libc::c_int as uint8_t,
            0x97 as libc::c_int as uint8_t,
            0x57 as libc::c_int as uint8_t,
            0xd7 as libc::c_int as uint8_t,
            0x37 as libc::c_int as uint8_t,
            0xb7 as libc::c_int as uint8_t,
            0x77 as libc::c_int as uint8_t,
            0xf7 as libc::c_int as uint8_t,
            0xf as libc::c_int as uint8_t,
            0x8f as libc::c_int as uint8_t,
            0x4f as libc::c_int as uint8_t,
            0xcf as libc::c_int as uint8_t,
            0x2f as libc::c_int as uint8_t,
            0xaf as libc::c_int as uint8_t,
            0x6f as libc::c_int as uint8_t,
            0xef as libc::c_int as uint8_t,
            0x1f as libc::c_int as uint8_t,
            0x9f as libc::c_int as uint8_t,
            0x5f as libc::c_int as uint8_t,
            0xdf as libc::c_int as uint8_t,
            0x3f as libc::c_int as uint8_t,
            0xbf as libc::c_int as uint8_t,
            0x7f as libc::c_int as uint8_t,
            0xff as libc::c_int as uint8_t];
#[inline(always)]
unsafe extern "C" fn BrotliReverseBits(mut num: uint64_t)
    -> uint64_t {
    return kReverseBits[num as usize] as uint64_t;
}
#[inline(always)]
unsafe extern "C" fn ReplicateValue(mut table: *mut HuffmanCode,
    mut step: libc::c_int, mut end: libc::c_int,
    mut code: HuffmanCode) {
    loop {
        end -= step;
        *table.offset(end as isize) = code;
        if !(end > 0 as libc::c_int) { break; }
    };
}
#[no_mangle]
pub unsafe extern "C" fn BrotliBuildCodeLengthsHuffmanTable(mut table:
        *mut HuffmanCode, code_lengths: *const uint8_t,
    mut count: *mut uint16_t) {
    let mut code = HuffmanCode { bits: 0, value: 0 };
    let mut symbol: libc::c_int = 0;
    let mut key: uint64_t = 0;
    let mut key_step: uint64_t = 0;
    let mut step: libc::c_int = 0;
    let mut table_size: libc::c_int = 0;
    let mut sorted: [libc::c_int; 18] = [0; 18];
    let mut offset: [libc::c_int; 6] = [0; 6];
    let mut bits: libc::c_int = 0;
    let mut bits_count: libc::c_int = 0;
    symbol = -(1 as libc::c_int);
    bits = 1 as libc::c_int;
    {
        symbol += *count.offset(bits as isize) as libc::c_int;
        offset[bits as usize] = symbol;
        bits += 1;
    }
    {}
    {
        symbol += *count.offset(bits as isize) as libc::c_int;
        offset[bits as usize] = symbol;
        bits += 1;
        symbol += *count.offset(bits as isize) as libc::c_int;
        offset[bits as usize] = symbol;
        bits += 1;
        symbol += *count.offset(bits as isize) as libc::c_int;
        offset[bits as usize] = symbol;
        bits += 1;
        symbol += *count.offset(bits as isize) as libc::c_int;
        offset[bits as usize] = symbol;
        bits += 1;
    }
    offset[0 as libc::c_int as usize] =
        17 as libc::c_int + 1 as libc::c_int - 1 as libc::c_int;
    symbol = 17 as libc::c_int + 1 as libc::c_int;
    loop {
        {}
        {
            symbol -= 1;
            let fresh1 =
                offset[*code_lengths.offset(symbol as isize) as usize];
            offset[*code_lengths.offset(symbol as isize) as usize] =
                offset[*code_lengths.offset(symbol as isize) as usize] - 1;
            sorted[fresh1 as usize] = symbol;
            symbol -= 1;
            let fresh2 =
                offset[*code_lengths.offset(symbol as isize) as usize];
            offset[*code_lengths.offset(symbol as isize) as usize] =
                offset[*code_lengths.offset(symbol as isize) as usize] - 1;
            sorted[fresh2 as usize] = symbol;
        }
        {
            symbol -= 1;
            let fresh3 =
                offset[*code_lengths.offset(symbol as isize) as usize];
            offset[*code_lengths.offset(symbol as isize) as usize] =
                offset[*code_lengths.offset(symbol as isize) as usize] - 1;
            sorted[fresh3 as usize] = symbol;
            symbol -= 1;
            let fresh4 =
                offset[*code_lengths.offset(symbol as isize) as usize];
            offset[*code_lengths.offset(symbol as isize) as usize] =
                offset[*code_lengths.offset(symbol as isize) as usize] - 1;
            sorted[fresh4 as usize] = symbol;
            symbol -= 1;
            let fresh5 =
                offset[*code_lengths.offset(symbol as isize) as usize];
            offset[*code_lengths.offset(symbol as isize) as usize] =
                offset[*code_lengths.offset(symbol as isize) as usize] - 1;
            sorted[fresh5 as usize] = symbol;
            symbol -= 1;
            let fresh6 =
                offset[*code_lengths.offset(symbol as isize) as usize];
            offset[*code_lengths.offset(symbol as isize) as usize] =
                offset[*code_lengths.offset(symbol as isize) as usize] - 1;
            sorted[fresh6 as usize] = symbol;
        }
        if !(symbol != 0 as libc::c_int) { break; }
    }
    table_size = (1 as libc::c_int) << 5 as libc::c_int;
    if offset[0 as libc::c_int as usize] == 0 as libc::c_int {
        code =
            ConstructHuffmanCode(0 as libc::c_int as uint8_t,
                sorted[0 as libc::c_int as usize] as uint16_t);
        key = 0 as libc::c_int as uint64_t;
        while key < table_size as uint64_t {
            *table.offset(key as isize) = code;
            key = key.wrapping_add(1);
        }
        return;
    }
    key = 0 as libc::c_int as uint64_t;
    key_step =
        (1 as libc::c_int as uint64_t) <<
            8 as libc::c_int - 1 as libc::c_int + 0 as libc::c_int;
    symbol = 0 as libc::c_int;
    bits = 1 as libc::c_int;
    step = 2 as libc::c_int;
    loop {
        bits_count = *count.offset(bits as isize) as libc::c_int;
        while bits_count != 0 as libc::c_int {
            let fresh7 = symbol;
            symbol = symbol + 1;
            code =
                ConstructHuffmanCode(bits as uint8_t,
                    sorted[fresh7 as usize] as uint16_t);
            ReplicateValue(&mut *table.offset((BrotliReverseBits as
                                            unsafe extern "C" fn(uint64_t) -> uint64_t)(key) as isize),
                step, table_size, code);
            key =
                (key as libc::c_ulong).wrapping_add(key_step) as uint64_t as
                    uint64_t;
            bits_count -= 1;
        }
        step <<= 1 as libc::c_int;
        key_step >>= 1 as libc::c_int;
        bits += 1;
        if !(bits <= 5 as libc::c_int) { break; }
    };
}
