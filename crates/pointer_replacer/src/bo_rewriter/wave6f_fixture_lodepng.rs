#![feature(derive_clone_copy)]
#![allow(dead_code, unused_unsafe, unused_mut, unused_assignments, non_camel_case_types, non_snake_case)]
pub type size_t = u64;
pub struct LodePNGBitReader {
    pub data: *const u8,
    pub size: size_t,
    pub bitsize: size_t,
    pub bp: size_t,
    pub buffer: u32,
}
#[automatically_derived]
impl ::core::marker::Copy for LodePNGBitReader { }
#[automatically_derived]
impl ::core::clone::Clone for LodePNGBitReader {
    #[inline]
    fn clone(&self) -> LodePNGBitReader {
        let _: ::core::clone::AssertParamIsClone<*const u8>;
        let _: ::core::clone::AssertParamIsClone<size_t>;
        let _: ::core::clone::AssertParamIsClone<u32>;
        *self
    }
}
unsafe extern "C" fn lodepng_memcpy(mut dst: *mut ::std::ffi::c_void, mut src: *const ::std::ffi::c_void, mut size: size_t) {
    let mut i: size_t = 0;
    i = 0 as i32 as size_t;
    while i < size {
        *(dst as *mut i8).offset(i as isize) = *(src as *const i8).offset(i as isize);
        i = i.wrapping_add(1);
    }
}
unsafe extern "C" fn LodePNGBitReader_init(mut reader: *mut LodePNGBitReader, mut data: *const u8, mut size: size_t) -> u32 {
    (*reader).data = data;
    (*reader).size = size;
    if size > (u64::MAX >> 3) { return 105 as i32 as u32; }
    (*reader).bitsize = size << 3;
    (*reader).bp = 0 as i32 as size_t;
    (*reader).buffer = 0 as i32 as u32;
    return 0 as i32 as u32;
}
unsafe extern "C" fn ensureBits9(mut reader: *mut LodePNGBitReader, mut nbits: size_t) {
    let mut start = (*reader).bp >> 3 as u32;
    let mut size = (*reader).size;
    if start.wrapping_add(1 as u32 as u64) < size {
        (*reader).buffer =
            *((*reader).data).offset(start.wrapping_add(0 as i32 as u64) as isize) as u32
                | (*((*reader).data).offset(start.wrapping_add(1 as i32 as u64) as isize) as u32) << 8 as u32;
        (*reader).buffer >>= ((*reader).bp & 7 as i32 as u64) as u32;
    } else {
        (*reader).buffer = 0 as i32 as u32;
        if start.wrapping_add(0 as i32 as u64) < size {
            (*reader).buffer |= *((*reader).data).offset(start.wrapping_add(0 as i32 as u64) as isize) as u32;
        }
        (*reader).buffer >>= ((*reader).bp & 7 as i32 as u64) as u32;
    }
}
unsafe extern "C" fn peekBits(mut reader: *const LodePNGBitReader, mut nbits: size_t) -> u32 {
    return (*reader).buffer & ((1 as u32) << nbits).wrapping_sub(1 as u32);
}
unsafe extern "C" fn advanceBits(mut reader: *mut LodePNGBitReader, mut nbits: size_t) {
    (*reader).buffer >>= nbits;
    (*reader).bp = ((*reader).bp).wrapping_add(nbits);
}
unsafe extern "C" fn readBits(mut reader: *mut LodePNGBitReader, mut nbits: size_t) -> u32 {
    let mut result = peekBits(reader, nbits);
    advanceBits(reader, nbits);
    return result;
}
unsafe extern "C" fn inflateNoCompression(mut out: *mut u8, mut reader: *mut LodePNGBitReader) -> u32 {
    let mut size = (*reader).size;
    let mut bytepos = ((*reader).bp).wrapping_add(7 as u32 as u64) >> 3 as u32;
    if bytepos.wrapping_add(4 as i32 as u64) >= size { return 52 as i32 as u32; }
    let mut LEN = (*((*reader).data).offset(bytepos as isize) as u32)
        .wrapping_add((*((*reader).data).offset(bytepos.wrapping_add(1 as i32 as u64) as isize) as u32) << 8 as u32);
    bytepos = bytepos.wrapping_add(4 as i32 as u64);
    if LEN != 0 {
        lodepng_memcpy(out as *mut ::std::ffi::c_void, ((*reader).data).offset(bytepos as isize) as *const ::std::ffi::c_void, LEN as size_t);
    }
    return 0 as i32 as u32;
}
pub struct LodePNGDecompressSettings {
    pub ignore_adler32: u32,
    pub custom_inflate: Option<unsafe extern "C" fn(*mut u8, *const u8, size_t) -> u32>,
}
unsafe extern "C" fn inflatev(mut out: *mut u8, mut in_0: *const u8, mut insize: size_t, mut settings: *const LodePNGDecompressSettings) -> u32 {
    if ((*settings).custom_inflate).is_some() {
        let mut error = ((*settings).custom_inflate).expect("non-null function pointer")(out, in_0, insize);
        if error != 0 { error = 110 as i32 as u32; }
        return error;
    } else { return lodepng_inflatev(out, in_0, insize) };
}
#[no_mangle]
pub unsafe extern "C" fn lodepng_inflatev(mut out: *mut u8, mut in_0: *const u8, mut insize: size_t) -> u32 {
    let mut BFINAL = 0 as i32 as u32;
    let mut align = in_0 as usize & 3;
    let mut reader =
        LodePNGBitReader {
            data: 0 as *const u8,
            size: 0,
            bitsize: 0,
            bp: 0,
            buffer: 0,
        };
    let mut error = LodePNGBitReader_init(&mut reader, in_0, insize);
    if error != 0 { return error; }
    while BFINAL == 0 {
        if (reader.bitsize).wrapping_sub(reader.bp) < 3 as i32 as u64 { return 52 as i32 as u32; }
        ensureBits9(&mut reader, 3 as i32 as size_t);
        BFINAL = readBits(&mut reader, 1 as i32 as size_t);
        let mut BTYPE = readBits(&mut reader, 2 as i32 as size_t);
        if BTYPE == 0 as u32 {
            error = inflateNoCompression(out, &mut reader);
        } else {
            return 20 as i32 as u32;
        }
        if error != 0 { return error; }
    }
    return error;
}
