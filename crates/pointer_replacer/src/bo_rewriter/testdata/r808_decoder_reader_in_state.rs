#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments, unused_variables, non_snake_case, non_camel_case_types)]
// R808-5: brotli's decoder, reduced. The bit reader is a field of the state;
// the stream driver takes `br = &mut (*s).br` and hands both to callees that
// write through each.
#[repr(C)]
pub struct BrotliBitReader {
    pub val_: u64,
    pub bit_pos_: u32,
    pub next_in: *const u8,
    pub avail_in: usize,
}
#[repr(C)]
pub struct HuffmanCode {
    pub bits: u8,
    pub value: u16,
}
#[repr(C)]
pub struct BrotliMetablockHeaderArena {
    pub context_map_table: [HuffmanCode; 8],
}
#[repr(C)]
pub struct BrotliMetablockBodyArena {
    pub header: BrotliMetablockHeaderArena,
}
#[repr(C)]
pub struct BrotliDecoderStateInternal {
    pub arena: BrotliMetablockBodyArena,
    pub state: i32,
    pub br: BrotliBitReader,
    pub window_bits: u32,
    pub large_window: i32,
    pub meta_block_remaining_len: i32,
    pub distance_code: i32,
}
unsafe fn BrotliSafeReadBits(mut br: *mut BrotliBitReader, mut n_bits: u32, mut val: *mut u32) -> i32 {
    if (*br).avail_in == 0 {
        return 0;
    }
    *val = ((*br).val_ & ((1u64 << n_bits) - 1)) as u32;
    (*br).val_ >>= n_bits;
    (*br).bit_pos_ = (*br).bit_pos_.wrapping_add(n_bits);
    1
}
unsafe fn DecodeWindowBits(mut s: *mut BrotliDecoderStateInternal, mut br: *mut BrotliBitReader) -> i32 {
    let mut n: u32 = 0;
    let mut large_window = (*s).large_window;
    (*s).large_window = 0;
    BrotliSafeReadBits(br, 1, &mut n);
    if n == 0 {
        (*s).window_bits = 16;
        return 1;
    }
    (*s).window_bits = n.wrapping_add(17);
    (*s).large_window = large_window;
    1
}
unsafe fn DecodeMetaBlockLength(mut s: *mut BrotliDecoderStateInternal, mut br: *mut BrotliBitReader) -> i32 {
    let mut bits: u32 = 0;
    if BrotliSafeReadBits(br, 2, &mut bits) == 0 {
        return 0;
    }
    (*s).meta_block_remaining_len = bits as i32;
    (*s).state = 2;
    1
}
unsafe fn ReadDistanceInternal(mut safe: i32, mut s: *mut BrotliDecoderStateInternal, mut br: *mut BrotliBitReader) -> i32 {
    let mut bits: u32 = 0;
    if safe != 0 {
        if BrotliSafeReadBits(br, 3, &mut bits) == 0 {
            return 0;
        }
    } else {
        BrotliSafeReadBits(br, 3, &mut bits);
    }
    (*s).distance_code = bits as i32;
    1
}
unsafe fn ReadDistance(mut s: *mut BrotliDecoderStateInternal, mut br: *mut BrotliBitReader) {
    ReadDistanceInternal(0, s, br);
}
// relay 165 item 2: the table is an array inside the state (through the
// header local), and the callee reborrows the whole state.
unsafe fn ReadCodeLengthCodeLengths(mut s: *mut BrotliDecoderStateInternal) -> i32 {
    (*s).state += 1;
    1
}
unsafe fn ReadHuffmanCode(mut alphabet_size: u32, mut table: *mut HuffmanCode, mut s: *mut BrotliDecoderStateInternal) -> i32 {
    let mut result = ReadCodeLengthCodeLengths(s);
    (*table.offset(0)).bits = alphabet_size as u8;
    (*table.offset(1)).value = 2;
    result
}
#[no_mangle]
pub unsafe extern "C" fn BrotliDecoderDecompressStream(mut s: *mut BrotliDecoderStateInternal) -> i32 {
    let mut result = 0;
    let mut br: *mut BrotliBitReader = &mut (*s).br;
    if (*s).state == 0 {
        result = DecodeWindowBits(s, br);
        (*s).state = 1;
    }
    if (*s).state == 1 {
        result = DecodeMetaBlockLength(s, br);
    }
    if (*s).state == 2 {
        ReadDistance(s, br);
    }
    if (*s).state == 3 {
        let mut h: *mut BrotliMetablockHeaderArena = &mut (*s).arena.header;
        result = ReadHuffmanCode(4, ((*h).context_map_table).as_mut_ptr(), s);
    }
    result
}
