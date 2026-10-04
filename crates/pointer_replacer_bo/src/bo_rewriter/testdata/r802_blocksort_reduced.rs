// R802-6 / R805-7 (main 168): bzip2's derived blocksort, reduced for the census-world entry: mainGtU,
// mainSimpleSort, mmed3 and mainQSort3 verbatim; mainSort cut to its mainQSort3 call and BZ2_blockSort to
// quadrant cast from block's tail (the overlap behind mainQSort3's a5-raw-view-template-unavailable).
#![warn(mutable_transmutes)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
#![feature(c_variadic)]
#![feature(extern_types)]
#![feature(linkage)]
#![feature(rustc_private)]
#![feature(thread_local)]
#![feature(builtin_syntax)]
#![feature(core_intrinsics)]
#![feature(derive_clone_copy)]
#![feature(hint_must_use)]
#![feature(panic_internals)]
#![feature(rt)]
#![feature(libstd_sys_internals)]
#![feature(structural_match)]
#![allow(dead_code, unused_mut, unused_assignments, unused_variables, unused_unsafe, unused_imports)]
pub mod blocksort {
    use crate::bzlib::BZ2_bz__AssertH__fail;
    extern "C" {
        pub type __sFILEX;
        #[no_mangle]
        static mut __stderrp: *mut FILE;
        #[no_mangle]
        fn fprintf(_: *mut FILE, _: *const std::os::raw::c_char, _: ...)
        -> std::os::raw::c_int;
    }
    pub type __int64_t = std::os::raw::c_longlong;
    pub type __darwin_off_t = __int64_t;
    pub type fpos_t = __darwin_off_t;
    #[repr(C)]
    pub struct __sbuf {
        pub _base: *mut std::os::raw::c_uchar,
        pub _size: std::os::raw::c_int,
    }
    #[automatically_derived]
    impl ::core::marker::Copy for __sbuf { }
    #[automatically_derived]
    impl ::core::clone::Clone for __sbuf {
        #[inline]
        fn clone(&self) -> __sbuf {
            let _:
                    ::core::clone::AssertParamIsClone<*mut std::os::raw::c_uchar>;
            let _: ::core::clone::AssertParamIsClone<std::os::raw::c_int>;
            *self
        }
    }
    #[repr(C)]
    pub struct __sFILE {
        pub _p: *mut std::os::raw::c_uchar,
        pub _r: std::os::raw::c_int,
        pub _w: std::os::raw::c_int,
        pub _flags: std::os::raw::c_short,
        pub _file: std::os::raw::c_short,
        pub _bf: __sbuf,
        pub _lbfsize: std::os::raw::c_int,
        pub _cookie: *mut std::os::raw::c_void,
        pub _close: Option<unsafe extern "C" fn(_: *mut std::os::raw::c_void)
            -> std::os::raw::c_int>,
        pub _read: Option<unsafe extern "C" fn(_: *mut std::os::raw::c_void,
            _: *mut std::os::raw::c_char, _: std::os::raw::c_int)
            -> std::os::raw::c_int>,
        pub _seek: Option<unsafe extern "C" fn(_: *mut std::os::raw::c_void,
            _: fpos_t, _: std::os::raw::c_int) -> fpos_t>,
        pub _write: Option<unsafe extern "C" fn(_: *mut std::os::raw::c_void,
            _: *const std::os::raw::c_char, _: std::os::raw::c_int)
            -> std::os::raw::c_int>,
        pub _ub: __sbuf,
        pub _extra: *mut __sFILEX,
        pub _ur: std::os::raw::c_int,
        pub _ubuf: [std::os::raw::c_uchar; 3],
        pub _nbuf: [std::os::raw::c_uchar; 1],
        pub _lb: __sbuf,
        pub _blksize: std::os::raw::c_int,
        pub _offset: fpos_t,
    }
    #[automatically_derived]
    impl ::core::marker::Copy for __sFILE { }
    #[automatically_derived]
    impl ::core::clone::Clone for __sFILE {
        #[inline]
        fn clone(&self) -> __sFILE {
            let _:
                    ::core::clone::AssertParamIsClone<*mut std::os::raw::c_uchar>;
            let _: ::core::clone::AssertParamIsClone<std::os::raw::c_int>;
            let _: ::core::clone::AssertParamIsClone<std::os::raw::c_int>;
            let _: ::core::clone::AssertParamIsClone<std::os::raw::c_short>;
            let _: ::core::clone::AssertParamIsClone<std::os::raw::c_short>;
            let _: ::core::clone::AssertParamIsClone<__sbuf>;
            let _: ::core::clone::AssertParamIsClone<std::os::raw::c_int>;
            let _:
                    ::core::clone::AssertParamIsClone<*mut std::os::raw::c_void>;
            let _:
                    ::core::clone::AssertParamIsClone<Option<unsafe extern "C" fn(_:
                            *mut std::os::raw::c_void) -> std::os::raw::c_int>>;
            let _:
                    ::core::clone::AssertParamIsClone<Option<unsafe extern "C" fn(_:
                            *mut std::os::raw::c_void, _: *mut std::os::raw::c_char,
                        _: std::os::raw::c_int) -> std::os::raw::c_int>>;
            let _:
                    ::core::clone::AssertParamIsClone<Option<unsafe extern "C" fn(_:
                            *mut std::os::raw::c_void, _: fpos_t,
                        _: std::os::raw::c_int) -> fpos_t>>;
            let _:
                    ::core::clone::AssertParamIsClone<Option<unsafe extern "C" fn(_:
                            *mut std::os::raw::c_void, _: *const std::os::raw::c_char,
                        _: std::os::raw::c_int) -> std::os::raw::c_int>>;
            let _: ::core::clone::AssertParamIsClone<*mut __sFILEX>;
            let _: ::core::clone::AssertParamIsClone<std::os::raw::c_int>;
            let _:
                    ::core::clone::AssertParamIsClone<[std::os::raw::c_uchar; 3]>;
            let _:
                    ::core::clone::AssertParamIsClone<[std::os::raw::c_uchar; 1]>;
            let _: ::core::clone::AssertParamIsClone<std::os::raw::c_int>;
            let _: ::core::clone::AssertParamIsClone<fpos_t>;
            *self
        }
    }
    pub type FILE = __sFILE;
    #[repr(C)]
    pub struct bz_stream {
        pub next_in: *mut std::os::raw::c_char,
        pub avail_in: std::os::raw::c_uint,
        pub total_in_lo32: std::os::raw::c_uint,
        pub total_in_hi32: std::os::raw::c_uint,
        pub next_out: *mut std::os::raw::c_char,
        pub avail_out: std::os::raw::c_uint,
        pub total_out_lo32: std::os::raw::c_uint,
        pub total_out_hi32: std::os::raw::c_uint,
        pub state: *mut std::os::raw::c_void,
        pub bzalloc: Option<unsafe extern "C" fn(_: *mut std::os::raw::c_void,
            _: std::os::raw::c_int, _: std::os::raw::c_int)
            -> *mut std::os::raw::c_void>,
        pub bzfree: Option<unsafe extern "C" fn(_: *mut std::os::raw::c_void,
            _: *mut std::os::raw::c_void) -> ()>,
        pub opaque: *mut std::os::raw::c_void,
    }
    #[automatically_derived]
    impl ::core::marker::Copy for bz_stream { }
    #[automatically_derived]
    impl ::core::clone::Clone for bz_stream {
        #[inline]
        fn clone(&self) -> bz_stream {
            let _:
                    ::core::clone::AssertParamIsClone<*mut std::os::raw::c_char>;
            let _: ::core::clone::AssertParamIsClone<std::os::raw::c_uint>;
            let _: ::core::clone::AssertParamIsClone<std::os::raw::c_uint>;
            let _: ::core::clone::AssertParamIsClone<std::os::raw::c_uint>;
            let _:
                    ::core::clone::AssertParamIsClone<*mut std::os::raw::c_char>;
            let _: ::core::clone::AssertParamIsClone<std::os::raw::c_uint>;
            let _: ::core::clone::AssertParamIsClone<std::os::raw::c_uint>;
            let _: ::core::clone::AssertParamIsClone<std::os::raw::c_uint>;
            let _:
                    ::core::clone::AssertParamIsClone<*mut std::os::raw::c_void>;
            let _:
                    ::core::clone::AssertParamIsClone<Option<unsafe extern "C" fn(_:
                            *mut std::os::raw::c_void, _: std::os::raw::c_int,
                        _: std::os::raw::c_int) -> *mut std::os::raw::c_void>>;
            let _:
                    ::core::clone::AssertParamIsClone<Option<unsafe extern "C" fn(_:
                            *mut std::os::raw::c_void, _: *mut std::os::raw::c_void)
                        -> ()>>;
            let _:
                    ::core::clone::AssertParamIsClone<*mut std::os::raw::c_void>;
            *self
        }
    }
    pub type Bool = std::os::raw::c_uchar;
    pub type UChar = std::os::raw::c_uchar;
    pub type Int32 = std::os::raw::c_int;
    pub type UInt32 = std::os::raw::c_uint;
    pub type UInt16 = std::os::raw::c_ushort;
    #[repr(C)]
    pub struct EState {
        pub strm: *mut bz_stream,
        pub mode: Int32,
        pub state: Int32,
        pub avail_in_expect: UInt32,
        pub arr1: *mut UInt32,
        pub arr2: *mut UInt32,
        pub ftab: *mut UInt32,
        pub origPtr: Int32,
        pub ptr: *mut UInt32,
        pub block: *mut UChar,
        pub mtfv: *mut UInt16,
        pub zbits: *mut UChar,
        pub workFactor: Int32,
        pub state_in_ch: UInt32,
        pub state_in_len: Int32,
        pub rNToGo: Int32,
        pub rTPos: Int32,
        pub nblock: Int32,
        pub nblockMAX: Int32,
        pub numZ: Int32,
        pub state_out_pos: Int32,
        pub nInUse: Int32,
        pub inUse: [Bool; 256],
        pub unseqToSeq: [UChar; 256],
        pub bsBuff: UInt32,
        pub bsLive: Int32,
        pub blockCRC: UInt32,
        pub combinedCRC: UInt32,
        pub verbosity: Int32,
        pub blockNo: Int32,
        pub blockSize100k: Int32,
        pub nMTF: Int32,
        pub mtfFreq: [Int32; 258],
        pub selector: [UChar; 18002],
        pub selectorMtf: [UChar; 18002],
        pub len: [[UChar; 258]; 6],
        pub code: [[Int32; 258]; 6],
        pub rfreq: [[Int32; 258]; 6],
        pub len_pack: [[UInt32; 4]; 258],
    }
    #[automatically_derived]
    impl ::core::marker::Copy for EState { }
    #[automatically_derived]
    impl ::core::clone::Clone for EState {
        #[inline]
        fn clone(&self) -> EState {
            let _: ::core::clone::AssertParamIsClone<*mut bz_stream>;
            let _: ::core::clone::AssertParamIsClone<Int32>;
            let _: ::core::clone::AssertParamIsClone<UInt32>;
            let _: ::core::clone::AssertParamIsClone<*mut UInt32>;
            let _: ::core::clone::AssertParamIsClone<*mut UInt32>;
            let _: ::core::clone::AssertParamIsClone<*mut UInt32>;
            let _: ::core::clone::AssertParamIsClone<*mut UInt32>;
            let _: ::core::clone::AssertParamIsClone<*mut UChar>;
            let _: ::core::clone::AssertParamIsClone<*mut UInt16>;
            let _: ::core::clone::AssertParamIsClone<*mut UChar>;
            let _: ::core::clone::AssertParamIsClone<[Bool; 256]>;
            let _: ::core::clone::AssertParamIsClone<[UChar; 256]>;
            let _: ::core::clone::AssertParamIsClone<[Int32; 258]>;
            let _: ::core::clone::AssertParamIsClone<[UChar; 18002]>;
            let _: ::core::clone::AssertParamIsClone<[UChar; 18002]>;
            let _: ::core::clone::AssertParamIsClone<[[UChar; 258]; 6]>;
            let _: ::core::clone::AssertParamIsClone<[[Int32; 258]; 6]>;
            let _: ::core::clone::AssertParamIsClone<[[Int32; 258]; 6]>;
            let _: ::core::clone::AssertParamIsClone<[[UInt32; 4]; 258]>;
            *self
        }
    }
    #[inline]
    unsafe extern "C" fn mainGtU(mut i1: UInt32, mut i2: UInt32,
        mut block: *mut UChar, mut quadrant: *mut UInt16, mut nblock: UInt32,
        mut budget: *mut Int32) -> Bool {
        let mut k: Int32 = 0;
        let mut c1: UChar = 0;
        let mut c2: UChar = 0;
        let mut s1: UInt16 = 0;
        let mut s2: UInt16 = 0;
        c1 = *block.offset(i1 as isize);
        c2 = *block.offset(i2 as isize);
        if c1 as std::os::raw::c_int != c2 as std::os::raw::c_int {
            return (c1 as std::os::raw::c_int > c2 as std::os::raw::c_int) as
                        std::os::raw::c_int as Bool
        }
        i1 = i1.wrapping_add(1);
        i2 = i2.wrapping_add(1);
        c1 = *block.offset(i1 as isize);
        c2 = *block.offset(i2 as isize);
        if c1 as std::os::raw::c_int != c2 as std::os::raw::c_int {
            return (c1 as std::os::raw::c_int > c2 as std::os::raw::c_int) as
                        std::os::raw::c_int as Bool
        }
        i1 = i1.wrapping_add(1);
        i2 = i2.wrapping_add(1);
        c1 = *block.offset(i1 as isize);
        c2 = *block.offset(i2 as isize);
        if c1 as std::os::raw::c_int != c2 as std::os::raw::c_int {
            return (c1 as std::os::raw::c_int > c2 as std::os::raw::c_int) as
                        std::os::raw::c_int as Bool
        }
        i1 = i1.wrapping_add(1);
        i2 = i2.wrapping_add(1);
        c1 = *block.offset(i1 as isize);
        c2 = *block.offset(i2 as isize);
        if c1 as std::os::raw::c_int != c2 as std::os::raw::c_int {
            return (c1 as std::os::raw::c_int > c2 as std::os::raw::c_int) as
                        std::os::raw::c_int as Bool
        }
        i1 = i1.wrapping_add(1);
        i2 = i2.wrapping_add(1);
        c1 = *block.offset(i1 as isize);
        c2 = *block.offset(i2 as isize);
        if c1 as std::os::raw::c_int != c2 as std::os::raw::c_int {
            return (c1 as std::os::raw::c_int > c2 as std::os::raw::c_int) as
                        std::os::raw::c_int as Bool
        }
        i1 = i1.wrapping_add(1);
        i2 = i2.wrapping_add(1);
        c1 = *block.offset(i1 as isize);
        c2 = *block.offset(i2 as isize);
        if c1 as std::os::raw::c_int != c2 as std::os::raw::c_int {
            return (c1 as std::os::raw::c_int > c2 as std::os::raw::c_int) as
                        std::os::raw::c_int as Bool
        }
        i1 = i1.wrapping_add(1);
        i2 = i2.wrapping_add(1);
        c1 = *block.offset(i1 as isize);
        c2 = *block.offset(i2 as isize);
        if c1 as std::os::raw::c_int != c2 as std::os::raw::c_int {
            return (c1 as std::os::raw::c_int > c2 as std::os::raw::c_int) as
                        std::os::raw::c_int as Bool
        }
        i1 = i1.wrapping_add(1);
        i2 = i2.wrapping_add(1);
        c1 = *block.offset(i1 as isize);
        c2 = *block.offset(i2 as isize);
        if c1 as std::os::raw::c_int != c2 as std::os::raw::c_int {
            return (c1 as std::os::raw::c_int > c2 as std::os::raw::c_int) as
                        std::os::raw::c_int as Bool
        }
        i1 = i1.wrapping_add(1);
        i2 = i2.wrapping_add(1);
        c1 = *block.offset(i1 as isize);
        c2 = *block.offset(i2 as isize);
        if c1 as std::os::raw::c_int != c2 as std::os::raw::c_int {
            return (c1 as std::os::raw::c_int > c2 as std::os::raw::c_int) as
                        std::os::raw::c_int as Bool
        }
        i1 = i1.wrapping_add(1);
        i2 = i2.wrapping_add(1);
        c1 = *block.offset(i1 as isize);
        c2 = *block.offset(i2 as isize);
        if c1 as std::os::raw::c_int != c2 as std::os::raw::c_int {
            return (c1 as std::os::raw::c_int > c2 as std::os::raw::c_int) as
                        std::os::raw::c_int as Bool
        }
        i1 = i1.wrapping_add(1);
        i2 = i2.wrapping_add(1);
        c1 = *block.offset(i1 as isize);
        c2 = *block.offset(i2 as isize);
        if c1 as std::os::raw::c_int != c2 as std::os::raw::c_int {
            return (c1 as std::os::raw::c_int > c2 as std::os::raw::c_int) as
                        std::os::raw::c_int as Bool
        }
        i1 = i1.wrapping_add(1);
        i2 = i2.wrapping_add(1);
        c1 = *block.offset(i1 as isize);
        c2 = *block.offset(i2 as isize);
        if c1 as std::os::raw::c_int != c2 as std::os::raw::c_int {
            return (c1 as std::os::raw::c_int > c2 as std::os::raw::c_int) as
                        std::os::raw::c_int as Bool
        }
        i1 = i1.wrapping_add(1);
        i2 = i2.wrapping_add(1);
        k =
            nblock.wrapping_add(8 as std::os::raw::c_int as
                        std::os::raw::c_uint) as Int32;
        loop {
            c1 = *block.offset(i1 as isize);
            c2 = *block.offset(i2 as isize);
            if c1 as std::os::raw::c_int != c2 as std::os::raw::c_int {
                return (c1 as std::os::raw::c_int > c2 as std::os::raw::c_int)
                            as std::os::raw::c_int as Bool
            }
            s1 = *quadrant.offset(i1 as isize);
            s2 = *quadrant.offset(i2 as isize);
            if s1 as std::os::raw::c_int != s2 as std::os::raw::c_int {
                return (s1 as std::os::raw::c_int > s2 as std::os::raw::c_int)
                            as std::os::raw::c_int as Bool
            }
            i1 = i1.wrapping_add(1);
            i2 = i2.wrapping_add(1);
            c1 = *block.offset(i1 as isize);
            c2 = *block.offset(i2 as isize);
            if c1 as std::os::raw::c_int != c2 as std::os::raw::c_int {
                return (c1 as std::os::raw::c_int > c2 as std::os::raw::c_int)
                            as std::os::raw::c_int as Bool
            }
            s1 = *quadrant.offset(i1 as isize);
            s2 = *quadrant.offset(i2 as isize);
            if s1 as std::os::raw::c_int != s2 as std::os::raw::c_int {
                return (s1 as std::os::raw::c_int > s2 as std::os::raw::c_int)
                            as std::os::raw::c_int as Bool
            }
            i1 = i1.wrapping_add(1);
            i2 = i2.wrapping_add(1);
            c1 = *block.offset(i1 as isize);
            c2 = *block.offset(i2 as isize);
            if c1 as std::os::raw::c_int != c2 as std::os::raw::c_int {
                return (c1 as std::os::raw::c_int > c2 as std::os::raw::c_int)
                            as std::os::raw::c_int as Bool
            }
            s1 = *quadrant.offset(i1 as isize);
            s2 = *quadrant.offset(i2 as isize);
            if s1 as std::os::raw::c_int != s2 as std::os::raw::c_int {
                return (s1 as std::os::raw::c_int > s2 as std::os::raw::c_int)
                            as std::os::raw::c_int as Bool
            }
            i1 = i1.wrapping_add(1);
            i2 = i2.wrapping_add(1);
            c1 = *block.offset(i1 as isize);
            c2 = *block.offset(i2 as isize);
            if c1 as std::os::raw::c_int != c2 as std::os::raw::c_int {
                return (c1 as std::os::raw::c_int > c2 as std::os::raw::c_int)
                            as std::os::raw::c_int as Bool
            }
            s1 = *quadrant.offset(i1 as isize);
            s2 = *quadrant.offset(i2 as isize);
            if s1 as std::os::raw::c_int != s2 as std::os::raw::c_int {
                return (s1 as std::os::raw::c_int > s2 as std::os::raw::c_int)
                            as std::os::raw::c_int as Bool
            }
            i1 = i1.wrapping_add(1);
            i2 = i2.wrapping_add(1);
            c1 = *block.offset(i1 as isize);
            c2 = *block.offset(i2 as isize);
            if c1 as std::os::raw::c_int != c2 as std::os::raw::c_int {
                return (c1 as std::os::raw::c_int > c2 as std::os::raw::c_int)
                            as std::os::raw::c_int as Bool
            }
            s1 = *quadrant.offset(i1 as isize);
            s2 = *quadrant.offset(i2 as isize);
            if s1 as std::os::raw::c_int != s2 as std::os::raw::c_int {
                return (s1 as std::os::raw::c_int > s2 as std::os::raw::c_int)
                            as std::os::raw::c_int as Bool
            }
            i1 = i1.wrapping_add(1);
            i2 = i2.wrapping_add(1);
            c1 = *block.offset(i1 as isize);
            c2 = *block.offset(i2 as isize);
            if c1 as std::os::raw::c_int != c2 as std::os::raw::c_int {
                return (c1 as std::os::raw::c_int > c2 as std::os::raw::c_int)
                            as std::os::raw::c_int as Bool
            }
            s1 = *quadrant.offset(i1 as isize);
            s2 = *quadrant.offset(i2 as isize);
            if s1 as std::os::raw::c_int != s2 as std::os::raw::c_int {
                return (s1 as std::os::raw::c_int > s2 as std::os::raw::c_int)
                            as std::os::raw::c_int as Bool
            }
            i1 = i1.wrapping_add(1);
            i2 = i2.wrapping_add(1);
            c1 = *block.offset(i1 as isize);
            c2 = *block.offset(i2 as isize);
            if c1 as std::os::raw::c_int != c2 as std::os::raw::c_int {
                return (c1 as std::os::raw::c_int > c2 as std::os::raw::c_int)
                            as std::os::raw::c_int as Bool
            }
            s1 = *quadrant.offset(i1 as isize);
            s2 = *quadrant.offset(i2 as isize);
            if s1 as std::os::raw::c_int != s2 as std::os::raw::c_int {
                return (s1 as std::os::raw::c_int > s2 as std::os::raw::c_int)
                            as std::os::raw::c_int as Bool
            }
            i1 = i1.wrapping_add(1);
            i2 = i2.wrapping_add(1);
            c1 = *block.offset(i1 as isize);
            c2 = *block.offset(i2 as isize);
            if c1 as std::os::raw::c_int != c2 as std::os::raw::c_int {
                return (c1 as std::os::raw::c_int > c2 as std::os::raw::c_int)
                            as std::os::raw::c_int as Bool
            }
            s1 = *quadrant.offset(i1 as isize);
            s2 = *quadrant.offset(i2 as isize);
            if s1 as std::os::raw::c_int != s2 as std::os::raw::c_int {
                return (s1 as std::os::raw::c_int > s2 as std::os::raw::c_int)
                            as std::os::raw::c_int as Bool
            }
            i1 = i1.wrapping_add(1);
            i2 = i2.wrapping_add(1);
            if i1 >= nblock {
                i1 =
                    (i1 as std::os::raw::c_uint).wrapping_sub(nblock) as UInt32
                        as UInt32
            }
            if i2 >= nblock {
                i2 =
                    (i2 as std::os::raw::c_uint).wrapping_sub(nblock) as UInt32
                        as UInt32
            }
            k -= 8 as std::os::raw::c_int;
            *budget -= 1;
            if !(k >= 0 as std::os::raw::c_int) { break; }
        }
        return 0 as std::os::raw::c_int as Bool;
    }
    static mut incs: [Int32; 14] =
        [1 as std::os::raw::c_int, 4 as std::os::raw::c_int,
                13 as std::os::raw::c_int, 40 as std::os::raw::c_int,
                121 as std::os::raw::c_int, 364 as std::os::raw::c_int,
                1093 as std::os::raw::c_int, 3280 as std::os::raw::c_int,
                9841 as std::os::raw::c_int, 29524 as std::os::raw::c_int,
                88573 as std::os::raw::c_int, 265720 as std::os::raw::c_int,
                797161 as std::os::raw::c_int,
                2391484 as std::os::raw::c_int];
    unsafe extern "C" fn mainSimpleSort(mut ptr: *mut UInt32,
        mut block: *mut UChar, mut quadrant: *mut UInt16, mut nblock: Int32,
        mut lo: Int32, mut hi: Int32, mut d: Int32, mut budget: *mut Int32) {
        let mut i: Int32 = 0;
        let mut j: Int32 = 0;
        let mut h: Int32 = 0;
        let mut bigN: Int32 = 0;
        let mut hp: Int32 = 0;
        let mut v: UInt32 = 0;
        bigN = hi - lo + 1 as std::os::raw::c_int;
        if bigN < 2 as std::os::raw::c_int { return }
        hp = 0 as std::os::raw::c_int;
        while incs[hp as usize] < bigN { hp += 1 }
        hp -= 1;
        while hp >= 0 as std::os::raw::c_int {
            h = incs[hp as usize];
            i = lo + h;
            while 1 as std::os::raw::c_int as Bool != 0 {
                if i > hi { break; }
                v = *ptr.offset(i as isize);
                j = i;
                while mainGtU((*ptr.offset((j - h) as
                                                isize)).wrapping_add(d as std::os::raw::c_uint),
                            v.wrapping_add(d as std::os::raw::c_uint), block, quadrant,
                            nblock as UInt32, budget) != 0 {
                    *ptr.offset(j as isize) = *ptr.offset((j - h) as isize);
                    j = j - h;
                    if j <= lo + h - 1 as std::os::raw::c_int { break; }
                }
                *ptr.offset(j as isize) = v;
                i += 1;
                if i > hi { break; }
                v = *ptr.offset(i as isize);
                j = i;
                while mainGtU((*ptr.offset((j - h) as
                                                isize)).wrapping_add(d as std::os::raw::c_uint),
                            v.wrapping_add(d as std::os::raw::c_uint), block, quadrant,
                            nblock as UInt32, budget) != 0 {
                    *ptr.offset(j as isize) = *ptr.offset((j - h) as isize);
                    j = j - h;
                    if j <= lo + h - 1 as std::os::raw::c_int { break; }
                }
                *ptr.offset(j as isize) = v;
                i += 1;
                if i > hi { break; }
                v = *ptr.offset(i as isize);
                j = i;
                while mainGtU((*ptr.offset((j - h) as
                                                isize)).wrapping_add(d as std::os::raw::c_uint),
                            v.wrapping_add(d as std::os::raw::c_uint), block, quadrant,
                            nblock as UInt32, budget) != 0 {
                    *ptr.offset(j as isize) = *ptr.offset((j - h) as isize);
                    j = j - h;
                    if j <= lo + h - 1 as std::os::raw::c_int { break; }
                }
                *ptr.offset(j as isize) = v;
                i += 1;
                if *budget < 0 as std::os::raw::c_int { return }
            }
            hp -= 1
        };
    }
    #[inline]
    unsafe extern "C" fn mmed3(mut a: UChar, mut b: UChar, mut c: UChar)
        -> UChar {
        let mut t: UChar = 0;
        if a as std::os::raw::c_int > b as std::os::raw::c_int {
            t = a;
            a = b;
            b = t
        }
        if b as std::os::raw::c_int > c as std::os::raw::c_int {
            b = c;
            if a as std::os::raw::c_int > b as std::os::raw::c_int { b = a }
        }
        return b;
    }
    unsafe extern "C" fn mainQSort3(mut ptr: *mut UInt32,
        mut block: *mut UChar, mut quadrant: *mut UInt16, mut nblock: Int32,
        mut loSt: Int32, mut hiSt: Int32, mut dSt: Int32,
        mut budget: *mut Int32) {
        let mut unLo: Int32 = 0;
        let mut unHi: Int32 = 0;
        let mut ltLo: Int32 = 0;
        let mut gtHi: Int32 = 0;
        let mut n: Int32 = 0;
        let mut m: Int32 = 0;
        let mut med: Int32 = 0;
        let mut sp: Int32 = 0;
        let mut lo: Int32 = 0;
        let mut hi: Int32 = 0;
        let mut d: Int32 = 0;
        let mut stackLo: [Int32; 100] = [0; 100];
        let mut stackHi: [Int32; 100] = [0; 100];
        let mut stackD: [Int32; 100] = [0; 100];
        let mut nextLo: [Int32; 3] = [0; 3];
        let mut nextHi: [Int32; 3] = [0; 3];
        let mut nextD: [Int32; 3] = [0; 3];
        sp = 0 as std::os::raw::c_int;
        stackLo[sp as usize] = loSt;
        stackHi[sp as usize] = hiSt;
        stackD[sp as usize] = dSt;
        sp += 1;
        while sp > 0 as std::os::raw::c_int {
            if !(sp < 100 as std::os::raw::c_int - 2 as std::os::raw::c_int) {
                BZ2_bz__AssertH__fail(1001 as std::os::raw::c_int);
            }
            sp -= 1;
            lo = stackLo[sp as usize];
            hi = stackHi[sp as usize];
            d = stackD[sp as usize];
            if hi - lo < 20 as std::os::raw::c_int ||
                    d > 2 as std::os::raw::c_int + 12 as std::os::raw::c_int {
                mainSimpleSort(ptr, block, quadrant, nblock, lo, hi, d,
                    budget);
                if *budget < 0 as std::os::raw::c_int { return }
            } else {
                med =
                    mmed3(*block.offset((*ptr.offset(lo as
                                                            isize)).wrapping_add(d as std::os::raw::c_uint) as isize),
                            *block.offset((*ptr.offset(hi as
                                                            isize)).wrapping_add(d as std::os::raw::c_uint) as isize),
                            *block.offset((*ptr.offset((lo + hi >>
                                                                    1 as std::os::raw::c_int) as
                                                            isize)).wrapping_add(d as std::os::raw::c_uint) as isize))
                        as Int32;
                ltLo = lo;
                unLo = ltLo;
                gtHi = hi;
                unHi = gtHi;
                while 1 as std::os::raw::c_int as Bool != 0 {
                    while 1 as std::os::raw::c_int as Bool != 0 {
                        if unLo > unHi { break; }
                        n =
                            *block.offset((*ptr.offset(unLo as
                                                                    isize)).wrapping_add(d as std::os::raw::c_uint) as isize) as
                                    Int32 - med;
                        if n == 0 as std::os::raw::c_int {
                            let mut zztmp: Int32 = *ptr.offset(unLo as isize) as Int32;
                            *ptr.offset(unLo as isize) = *ptr.offset(ltLo as isize);
                            *ptr.offset(ltLo as isize) = zztmp as UInt32;
                            ltLo += 1;
                            unLo += 1
                        } else {
                            if n > 0 as std::os::raw::c_int { break; }
                            unLo += 1
                        }
                    }
                    while 1 as std::os::raw::c_int as Bool != 0 {
                        if unLo > unHi { break; }
                        n =
                            *block.offset((*ptr.offset(unHi as
                                                                    isize)).wrapping_add(d as std::os::raw::c_uint) as isize) as
                                    Int32 - med;
                        if n == 0 as std::os::raw::c_int {
                            let mut zztmp_0: Int32 =
                                *ptr.offset(unHi as isize) as Int32;
                            *ptr.offset(unHi as isize) = *ptr.offset(gtHi as isize);
                            *ptr.offset(gtHi as isize) = zztmp_0 as UInt32;
                            gtHi -= 1;
                            unHi -= 1
                        } else {
                            if n < 0 as std::os::raw::c_int { break; }
                            unHi -= 1
                        }
                    }
                    if unLo > unHi { break; }
                    let mut zztmp_1: Int32 =
                        *ptr.offset(unLo as isize) as Int32;
                    *ptr.offset(unLo as isize) = *ptr.offset(unHi as isize);
                    *ptr.offset(unHi as isize) = zztmp_1 as UInt32;
                    unLo += 1;
                    unHi -= 1
                }
                if gtHi < ltLo {
                    stackLo[sp as usize] = lo;
                    stackHi[sp as usize] = hi;
                    stackD[sp as usize] = d + 1 as std::os::raw::c_int;
                    sp += 1
                } else {
                    n =
                        if ltLo - lo < unLo - ltLo {
                            (ltLo) - lo
                        } else { (unLo) - ltLo };
                    let mut yyp1: Int32 = lo;
                    let mut yyp2: Int32 = unLo - n;
                    let mut yyn: Int32 = n;
                    while yyn > 0 as std::os::raw::c_int {
                        let mut zztmp_2: Int32 =
                            *ptr.offset(yyp1 as isize) as Int32;
                        *ptr.offset(yyp1 as isize) = *ptr.offset(yyp2 as isize);
                        *ptr.offset(yyp2 as isize) = zztmp_2 as UInt32;
                        yyp1 += 1;
                        yyp2 += 1;
                        yyn -= 1
                    }
                    m =
                        if hi - gtHi < gtHi - unHi {
                            (hi) - gtHi
                        } else { (gtHi) - unHi };
                    let mut yyp1_0: Int32 = unLo;
                    let mut yyp2_0: Int32 = hi - m + 1 as std::os::raw::c_int;
                    let mut yyn_0: Int32 = m;
                    while yyn_0 > 0 as std::os::raw::c_int {
                        let mut zztmp_3: Int32 =
                            *ptr.offset(yyp1_0 as isize) as Int32;
                        *ptr.offset(yyp1_0 as isize) = *ptr.offset(yyp2_0 as isize);
                        *ptr.offset(yyp2_0 as isize) = zztmp_3 as UInt32;
                        yyp1_0 += 1;
                        yyp2_0 += 1;
                        yyn_0 -= 1
                    }
                    n = lo + unLo - ltLo - 1 as std::os::raw::c_int;
                    m = hi - (gtHi - unHi) + 1 as std::os::raw::c_int;
                    nextLo[0 as std::os::raw::c_int as usize] = lo;
                    nextHi[0 as std::os::raw::c_int as usize] = n;
                    nextD[0 as std::os::raw::c_int as usize] = d;
                    nextLo[1 as std::os::raw::c_int as usize] = m;
                    nextHi[1 as std::os::raw::c_int as usize] = hi;
                    nextD[1 as std::os::raw::c_int as usize] = d;
                    nextLo[2 as std::os::raw::c_int as usize] =
                        n + 1 as std::os::raw::c_int;
                    nextHi[2 as std::os::raw::c_int as usize] =
                        m - 1 as std::os::raw::c_int;
                    nextD[2 as std::os::raw::c_int as usize] =
                        d + 1 as std::os::raw::c_int;
                    if nextHi[0 as std::os::raw::c_int as usize] -
                                nextLo[0 as std::os::raw::c_int as usize] <
                            nextHi[1 as std::os::raw::c_int as usize] -
                                nextLo[1 as std::os::raw::c_int as usize] {
                        let mut tz: Int32 = 0;
                        tz = nextLo[0 as std::os::raw::c_int as usize];
                        nextLo[0 as std::os::raw::c_int as usize] =
                            nextLo[1 as std::os::raw::c_int as usize];
                        nextLo[1 as std::os::raw::c_int as usize] = tz;
                        tz = nextHi[0 as std::os::raw::c_int as usize];
                        nextHi[0 as std::os::raw::c_int as usize] =
                            nextHi[1 as std::os::raw::c_int as usize];
                        nextHi[1 as std::os::raw::c_int as usize] = tz;
                        tz = nextD[0 as std::os::raw::c_int as usize];
                        nextD[0 as std::os::raw::c_int as usize] =
                            nextD[1 as std::os::raw::c_int as usize];
                        nextD[1 as std::os::raw::c_int as usize] = tz
                    }
                    if nextHi[1 as std::os::raw::c_int as usize] -
                                nextLo[1 as std::os::raw::c_int as usize] <
                            nextHi[2 as std::os::raw::c_int as usize] -
                                nextLo[2 as std::os::raw::c_int as usize] {
                        let mut tz_0: Int32 = 0;
                        tz_0 = nextLo[1 as std::os::raw::c_int as usize];
                        nextLo[1 as std::os::raw::c_int as usize] =
                            nextLo[2 as std::os::raw::c_int as usize];
                        nextLo[2 as std::os::raw::c_int as usize] = tz_0;
                        tz_0 = nextHi[1 as std::os::raw::c_int as usize];
                        nextHi[1 as std::os::raw::c_int as usize] =
                            nextHi[2 as std::os::raw::c_int as usize];
                        nextHi[2 as std::os::raw::c_int as usize] = tz_0;
                        tz_0 = nextD[1 as std::os::raw::c_int as usize];
                        nextD[1 as std::os::raw::c_int as usize] =
                            nextD[2 as std::os::raw::c_int as usize];
                        nextD[2 as std::os::raw::c_int as usize] = tz_0
                    }
                    if nextHi[0 as std::os::raw::c_int as usize] -
                                nextLo[0 as std::os::raw::c_int as usize] <
                            nextHi[1 as std::os::raw::c_int as usize] -
                                nextLo[1 as std::os::raw::c_int as usize] {
                        let mut tz_1: Int32 = 0;
                        tz_1 = nextLo[0 as std::os::raw::c_int as usize];
                        nextLo[0 as std::os::raw::c_int as usize] =
                            nextLo[1 as std::os::raw::c_int as usize];
                        nextLo[1 as std::os::raw::c_int as usize] = tz_1;
                        tz_1 = nextHi[0 as std::os::raw::c_int as usize];
                        nextHi[0 as std::os::raw::c_int as usize] =
                            nextHi[1 as std::os::raw::c_int as usize];
                        nextHi[1 as std::os::raw::c_int as usize] = tz_1;
                        tz_1 = nextD[0 as std::os::raw::c_int as usize];
                        nextD[0 as std::os::raw::c_int as usize] =
                            nextD[1 as std::os::raw::c_int as usize];
                        nextD[1 as std::os::raw::c_int as usize] = tz_1
                    }
                    stackLo[sp as usize] =
                        nextLo[0 as std::os::raw::c_int as usize];
                    stackHi[sp as usize] =
                        nextHi[0 as std::os::raw::c_int as usize];
                    stackD[sp as usize] =
                        nextD[0 as std::os::raw::c_int as usize];
                    sp += 1;
                    stackLo[sp as usize] =
                        nextLo[1 as std::os::raw::c_int as usize];
                    stackHi[sp as usize] =
                        nextHi[1 as std::os::raw::c_int as usize];
                    stackD[sp as usize] =
                        nextD[1 as std::os::raw::c_int as usize];
                    sp += 1;
                    stackLo[sp as usize] =
                        nextLo[2 as std::os::raw::c_int as usize];
                    stackHi[sp as usize] =
                        nextHi[2 as std::os::raw::c_int as usize];
                    stackD[sp as usize] =
                        nextD[2 as std::os::raw::c_int as usize];
                    sp += 1
                }
            }
        };
    }
    unsafe extern "C" fn mainSort(mut ptr: *mut UInt32, mut block: *mut UChar,
        mut quadrant: *mut UInt16, mut nblock: Int32, mut budget: *mut Int32) {
        let mut i: Int32 = 0;
        while i < nblock + 34 {
            *block.offset(i as isize) = 0 as UChar;
            *quadrant.offset(i as isize) = 0 as UInt16;
            *ptr.offset(i as isize) = i as UInt32;
            i += 1;
        }
        mainQSort3(ptr, block, quadrant, nblock, 0 as Int32, nblock - 1, 2 as Int32, budget);
    }
    #[no_mangle]
    pub unsafe extern "C" fn BZ2_blockSort(mut arr1: *mut UInt32, mut arr2: *mut UInt32, mut nblock: Int32) {
        let mut budget: Int32 = nblock * 30;
        let mut block = arr2 as *mut UChar;
        let mut i = nblock + 34;
        if i & 1 as Int32 != 0 { i += 1; }
        let mut quadrant = &mut *block.offset(i as isize) as *mut UChar as *mut UInt16;
        mainSort(arr1, block, quadrant, nblock, &mut budget);
    }
}
pub mod bzlib {
    #[no_mangle]
    pub unsafe extern "C" fn BZ2_bz__AssertH__fail(errcode: std::os::raw::c_int) { let _ = errcode; }
}
