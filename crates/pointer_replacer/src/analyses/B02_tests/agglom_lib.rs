use super::run_ownership_case_with_box_candidates;

const SOURCE: &str = r####"
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
pub mod src {
    pub mod lib {
        extern "C" {
            fn fabsf(__x: core::ffi::c_float) -> core::ffi::c_float;
            fn floorf(__x: core::ffi::c_float) -> core::ffi::c_float;
            fn fmodf(__x: core::ffi::c_float, __y: core::ffi::c_float) -> core::ffi::c_float;
        }
        pub type __uint16_t = u16;
        pub type __uint32_t = u32;
        pub type __uint64_t = u64;
        pub type uint16_t = __uint16_t;
        pub type uint32_t = __uint32_t;
        pub type uint64_t = __uint64_t;
        pub type tflac_u32 = uint32_t;
        #[repr(C)]
        pub union C2RustUnnamed {
            pub flt: core::ffi::c_float,
            pub num: uint32_t,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for C2RustUnnamed {}
        #[automatically_derived]
        impl ::core::clone::Clone for C2RustUnnamed {
            #[inline]
            fn clone(&self) -> C2RustUnnamed {
                let _: ::core::clone::AssertParamIsCopy<Self>;
                *self
            }
        }
        #[repr(C)]
        pub struct lm_vec2 {
            pub x: core::ffi::c_float,
            pub y: core::ffi::c_float,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for lm_vec2 {}
        #[automatically_derived]
        impl ::core::clone::Clone for lm_vec2 {
            #[inline]
            fn clone(&self) -> lm_vec2 {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_float>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_float>;
                *self
            }
        }
        #[repr(C)]
        pub struct cn_rnd_t {
            pub state: [uint64_t; 2],
        }
        #[automatically_derived]
        impl ::core::marker::Copy for cn_rnd_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for cn_rnd_t {
            #[inline]
            fn clone(&self) -> cn_rnd_t {
                let _: ::core::clone::AssertParamIsClone<[uint64_t; 2]>;
                *self
            }
        }
        pub type C2_TYPE = core::ffi::c_uint;
        pub const C2_TYPE_AABB: C2_TYPE = 1;
        pub const C2_TYPE_CIRCLE: C2_TYPE = 0;
        #[repr(C)]
        pub struct c2AABB {
            pub min: c2v,
            pub max: c2v,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for c2AABB {}
        #[automatically_derived]
        impl ::core::clone::Clone for c2AABB {
            #[inline]
            fn clone(&self) -> c2AABB {
                let _: ::core::clone::AssertParamIsClone<c2v>;
                *self
            }
        }
        #[repr(C)]
        pub struct c2v {
            pub x: core::ffi::c_float,
            pub y: core::ffi::c_float,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for c2v {}
        #[automatically_derived]
        impl ::core::clone::Clone for c2v {
            #[inline]
            fn clone(&self) -> c2v {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_float>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_float>;
                *self
            }
        }
        #[repr(C)]
        pub struct c2Circle {
            pub p: c2v,
            pub r: core::ffi::c_float,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for c2Circle {}
        #[automatically_derived]
        impl ::core::clone::Clone for c2Circle {
            #[inline]
            fn clone(&self) -> c2Circle {
                let _: ::core::clone::AssertParamIsClone<c2v>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_float>;
                *self
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2V(x: core::ffi::c_float, y: core::ffi::c_float) -> c2v {
            let mut a: c2v = c2v { x: 0., y: 0. };
            a.x = x;
            a.y = y;
            a
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Maxv(a: c2v, b: c2v) -> c2v {
            c2V(
                if a.x > b.x { a.x } else { b.x },
                if a.y > b.y { a.y } else { b.y },
            )
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Minv(a: c2v, b: c2v) -> c2v {
            c2V(
                if a.x < b.x { a.x } else { b.x },
                if a.y < b.y { a.y } else { b.y },
            )
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Clampv(a: c2v, lo: c2v, hi: c2v) -> c2v {
            c2Maxv(lo, c2Minv(a, hi))
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Sub(mut a: c2v, b: c2v) -> c2v {
            a.x -= b.x;
            a.y -= b.y;
            a
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Dot(a: c2v, b: c2v) -> core::ffi::c_float {
            a.x * b.x + a.y * b.y
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2CircletoCircle(A: c2Circle, B: c2Circle) -> core::ffi::c_int {
            let c: c2v = c2Sub(B.p, A.p);
            let d2: core::ffi::c_float = c2Dot(c, c);
            let mut r2: core::ffi::c_float = A.r + B.r;
            r2 = r2 * r2;
            (d2 < r2) as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2CircletoAABB(A: c2Circle, B: c2AABB) -> core::ffi::c_int {
            let L: c2v = c2Clampv(A.p, B.min, B.max);
            let ab: c2v = c2Sub(A.p, L);
            let d2: core::ffi::c_float = c2Dot(ab, ab);
            let r2: core::ffi::c_float = A.r * A.r;
            (d2 < r2) as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2AABBtoAABB(A: c2AABB, B: c2AABB) -> core::ffi::c_int {
            let d0: core::ffi::c_int = (B.max.x < A.min.x) as core::ffi::c_int;
            let d1: core::ffi::c_int = (A.max.x < B.min.x) as core::ffi::c_int;
            let d2: core::ffi::c_int = (B.max.y < A.min.y) as core::ffi::c_int;
            let d3: core::ffi::c_int = (A.max.y < B.min.y) as core::ffi::c_int;
            (d0 | d1 | d2 | d3 == 0) as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn f2(
            A: *const core::ffi::c_void,
            typeA: C2_TYPE,
            B: *const core::ffi::c_void,
            typeB: C2_TYPE,
        ) -> core::ffi::c_int {
            match typeA as core::ffi::c_uint {
                0 => match typeB as core::ffi::c_uint {
                    0 => c2CircletoCircle(*(A as *mut c2Circle), *(B as *mut c2Circle)),
                    1 => c2CircletoAABB(*(A as *mut c2Circle), *(B as *mut c2AABB)),
                    _ => 0 as core::ffi::c_int,
                },
                1 => match typeB as core::ffi::c_uint {
                    0 => c2CircletoAABB(*(B as *mut c2Circle), *(A as *mut c2AABB)),
                    1 => c2AABBtoAABB(*(A as *mut c2AABB), *(B as *mut c2AABB)),
                    _ => 0 as core::ffi::c_int,
                },
                _ => 0 as core::ffi::c_int,
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn f3(
            v1: core::ffi::c_int,
            v2: core::ffi::c_int,
        ) -> core::ffi::c_int {
            if v2 == 0 as core::ffi::c_int {
                return 0 as core::ffi::c_int;
            }
            let mut q: core::ffi::c_int = 0;
            let mut r: core::ffi::c_int = 0;
            if v1 >= 0 as core::ffi::c_int {
                if v2 >= 0 as core::ffi::c_int {
                    return v1 / v2;
                } else if v2 != -(0x7fffffff as core::ffi::c_int) - 1 as core::ffi::c_int {
                    q = -(v1 / -v2);
                    r = v1 % -v2;
                } else {
                    q = 0 as core::ffi::c_int;
                    r = v1;
                }
            } else if v1 != -(0x7fffffff as core::ffi::c_int) - 1 as core::ffi::c_int {
                if v2 >= 0 as core::ffi::c_int {
                    q = -(-v1 / v2);
                    r = -(-v1 % v2);
                } else if v2 != -(0x7fffffff as core::ffi::c_int) - 1 as core::ffi::c_int {
                    q = -v1 / -v2;
                    r = -(-v1 % -v2);
                } else {
                    q = 1 as core::ffi::c_int;
                    r = v1 - q * v2;
                }
            } else if v2 >= 0 as core::ffi::c_int {
                q = -(-(v1 + v2) / v2) - 1 as core::ffi::c_int;
                r = -(-(v1 + v2) % v2);
            } else if v2 != -(0x7fffffff as core::ffi::c_int) - 1 as core::ffi::c_int {
                q = -(v1 - v2) / -v2 + 1 as core::ffi::c_int;
                r = -(-(v1 - v2) % -v2);
            } else {
                q = 1 as core::ffi::c_int;
                r = 0 as core::ffi::c_int;
            }
            if r >= 0 as core::ffi::c_int {
                q
            } else {
                q + (if v2 > 0 as core::ffi::c_int {
                    -(1 as core::ffi::c_int)
                } else {
                    1 as core::ffi::c_int
                })
            }
        }
        unsafe extern "C" fn cn_rnd_next(rnd: *mut cn_rnd_t) -> uint64_t {
            let mut x: uint64_t = (*rnd).state[0 as core::ffi::c_int as usize];
            let y: uint64_t = (*rnd).state[1 as core::ffi::c_int as usize];
            (*rnd).state[0 as core::ffi::c_int as usize] = y;
            x = (x as core::ffi::c_ulong ^ (x << 23 as core::ffi::c_int) as core::ffi::c_ulong)
                as uint64_t;
            x = (x as core::ffi::c_ulong ^ (x >> 17 as core::ffi::c_int) as core::ffi::c_ulong)
                as uint64_t;
            x = (x as core::ffi::c_ulong ^ (y ^ y >> 26 as core::ffi::c_int) as core::ffi::c_ulong)
                as uint64_t;
            (*rnd).state[1 as core::ffi::c_int as usize] = x;
            x.wrapping_add(y)
        }
        #[no_mangle]
        pub unsafe extern "C" fn f4(rnd: *mut cn_rnd_t) -> core::ffi::c_double {
            let value: uint64_t = cn_rnd_next(rnd);
            let exponent: uint64_t = 1023 as uint64_t;
            let mantissa: uint64_t = value >> 12 as core::ffi::c_int;
            let mut result: uint64_t = exponent << 52 as core::ffi::c_int | mantissa;
            *(&mut result as *mut uint64_t as *mut core::ffi::c_double) - 1.0f64
        }
        #[no_mangle]
        pub unsafe extern "C" fn f5(mut a: uint32_t) -> uint32_t {
            a = (a & 0xaaaa as uint32_t) >> 1 as core::ffi::c_int
                | (a & 0x5555 as uint32_t) << 1 as core::ffi::c_int;
            a = (a & 0xcccc as uint32_t) >> 2 as core::ffi::c_int
                | (a & 0x3333 as uint32_t) << 2 as core::ffi::c_int;
            a = (a & 0xf0f0 as uint32_t) >> 4 as core::ffi::c_int
                | (a & 0xf0f as uint32_t) << 4 as core::ffi::c_int;
            a = (a & 0xff00 as uint32_t) >> 8 as core::ffi::c_int
                | (a & 0xff as uint32_t) << 8 as core::ffi::c_int;
            a
        }
        #[no_mangle]
        pub unsafe extern "C" fn f7(
            blocksize: tflac_u32,
            channels: tflac_u32,
            bitdepth: tflac_u32,
        ) -> tflac_u32 {
            (18 as tflac_u32).wrapping_add(channels).wrapping_add(
                blocksize
                    .wrapping_mul(bitdepth)
                    .wrapping_mul(channels.wrapping_mul(
                        (channels != 2 as tflac_u32) as core::ffi::c_int as tflac_u32,
                    ))
                    .wrapping_add(blocksize.wrapping_mul(bitdepth).wrapping_mul(
                        (channels == 2 as tflac_u32) as core::ffi::c_int as tflac_u32,
                    ))
                    .wrapping_add(
                        blocksize
                            .wrapping_mul(bitdepth.wrapping_add(
                                (bitdepth != 32 as tflac_u32) as core::ffi::c_int as tflac_u32,
                            ))
                            .wrapping_mul(
                                (channels == 2 as tflac_u32) as core::ffi::c_int as tflac_u32,
                            ),
                    )
                    .wrapping_add(7 as core::ffi::c_int as tflac_u32)
                    .wrapping_div(8 as tflac_u32),
            )
        }
        unsafe extern "C" fn lm_v2(x: core::ffi::c_float, y: core::ffi::c_float) -> lm_vec2 {
            let v: lm_vec2 = { lm_vec2 { x, y } };
            v
        }
        unsafe extern "C" fn lm_sub2(a: lm_vec2, b: lm_vec2) -> lm_vec2 {
            lm_v2(a.x - b.x, a.y - b.y)
        }
        unsafe extern "C" fn lm_dot2(a: lm_vec2, b: lm_vec2) -> core::ffi::c_float {
            a.x * b.x + a.y * b.y
        }
        #[no_mangle]
        pub unsafe extern "C" fn f9(p1: lm_vec2, p2: lm_vec2, p3: lm_vec2, p: lm_vec2) -> lm_vec2 {
            let v0: lm_vec2 = lm_sub2(p3, p1);
            let v1: lm_vec2 = lm_sub2(p2, p1);
            let v2: lm_vec2 = lm_sub2(p, p1);
            let dot00: core::ffi::c_float = lm_dot2(v0, v0);
            let dot01: core::ffi::c_float = lm_dot2(v0, v1);
            let dot02: core::ffi::c_float = lm_dot2(v0, v2);
            let dot11: core::ffi::c_float = lm_dot2(v1, v1);
            let dot12: core::ffi::c_float = lm_dot2(v1, v2);
            let invDenom: core::ffi::c_float = 1.0f32 / (dot00 * dot11 - dot01 * dot01);
            let u: core::ffi::c_float = (dot11 * dot02 - dot01 * dot12) * invDenom;
            let v: core::ffi::c_float = (dot00 * dot12 - dot01 * dot02) * invDenom;
            lm_v2(u, v)
        }
        static mut m__mantissa: [uint32_t; 2048] = [
            0 as core::ffi::c_int as uint32_t,
            0x33800000 as core::ffi::c_int as uint32_t,
            0x34000000 as core::ffi::c_int as uint32_t,
            0x34400000 as core::ffi::c_int as uint32_t,
            0x34800000 as core::ffi::c_int as uint32_t,
            0x34a00000 as core::ffi::c_int as uint32_t,
            0x34c00000 as core::ffi::c_int as uint32_t,
            0x34e00000 as core::ffi::c_int as uint32_t,
            0x35000000 as core::ffi::c_int as uint32_t,
            0x35100000 as core::ffi::c_int as uint32_t,
            0x35200000 as core::ffi::c_int as uint32_t,
            0x35300000 as core::ffi::c_int as uint32_t,
            0x35400000 as core::ffi::c_int as uint32_t,
            0x35500000 as core::ffi::c_int as uint32_t,
            0x35600000 as core::ffi::c_int as uint32_t,
            0x35700000 as core::ffi::c_int as uint32_t,
            0x35800000 as core::ffi::c_int as uint32_t,
            0x35880000 as core::ffi::c_int as uint32_t,
            0x35900000 as core::ffi::c_int as uint32_t,
            0x35980000 as core::ffi::c_int as uint32_t,
            0x35a00000 as core::ffi::c_int as uint32_t,
            0x35a80000 as core::ffi::c_int as uint32_t,
            0x35b00000 as core::ffi::c_int as uint32_t,
            0x35b80000 as core::ffi::c_int as uint32_t,
            0x35c00000 as core::ffi::c_int as uint32_t,
            0x35c80000 as core::ffi::c_int as uint32_t,
            0x35d00000 as core::ffi::c_int as uint32_t,
            0x35d80000 as core::ffi::c_int as uint32_t,
            0x35e00000 as core::ffi::c_int as uint32_t,
            0x35e80000 as core::ffi::c_int as uint32_t,
            0x35f00000 as core::ffi::c_int as uint32_t,
            0x35f80000 as core::ffi::c_int as uint32_t,
            0x36000000 as core::ffi::c_int as uint32_t,
            0x36040000 as core::ffi::c_int as uint32_t,
            0x36080000 as core::ffi::c_int as uint32_t,
            0x360c0000 as core::ffi::c_int as uint32_t,
            0x36100000 as core::ffi::c_int as uint32_t,
            0x36140000 as core::ffi::c_int as uint32_t,
            0x36180000 as core::ffi::c_int as uint32_t,
            0x361c0000 as core::ffi::c_int as uint32_t,
            0x36200000 as core::ffi::c_int as uint32_t,
            0x36240000 as core::ffi::c_int as uint32_t,
            0x36280000 as core::ffi::c_int as uint32_t,
            0x362c0000 as core::ffi::c_int as uint32_t,
            0x36300000 as core::ffi::c_int as uint32_t,
            0x36340000 as core::ffi::c_int as uint32_t,
            0x36380000 as core::ffi::c_int as uint32_t,
            0x363c0000 as core::ffi::c_int as uint32_t,
            0x36400000 as core::ffi::c_int as uint32_t,
            0x36440000 as core::ffi::c_int as uint32_t,
            0x36480000 as core::ffi::c_int as uint32_t,
            0x364c0000 as core::ffi::c_int as uint32_t,
            0x36500000 as core::ffi::c_int as uint32_t,
            0x36540000 as core::ffi::c_int as uint32_t,
            0x36580000 as core::ffi::c_int as uint32_t,
            0x365c0000 as core::ffi::c_int as uint32_t,
            0x36600000 as core::ffi::c_int as uint32_t,
            0x36640000 as core::ffi::c_int as uint32_t,
            0x36680000 as core::ffi::c_int as uint32_t,
            0x366c0000 as core::ffi::c_int as uint32_t,
            0x36700000 as core::ffi::c_int as uint32_t,
            0x36740000 as core::ffi::c_int as uint32_t,
            0x36780000 as core::ffi::c_int as uint32_t,
            0x367c0000 as core::ffi::c_int as uint32_t,
            0x36800000 as core::ffi::c_int as uint32_t,
            0x36820000 as core::ffi::c_int as uint32_t,
            0x36840000 as core::ffi::c_int as uint32_t,
            0x36860000 as core::ffi::c_int as uint32_t,
            0x36880000 as core::ffi::c_int as uint32_t,
            0x368a0000 as core::ffi::c_int as uint32_t,
            0x368c0000 as core::ffi::c_int as uint32_t,
            0x368e0000 as core::ffi::c_int as uint32_t,
            0x36900000 as core::ffi::c_int as uint32_t,
            0x36920000 as core::ffi::c_int as uint32_t,
            0x36940000 as core::ffi::c_int as uint32_t,
            0x36960000 as core::ffi::c_int as uint32_t,
            0x36980000 as core::ffi::c_int as uint32_t,
            0x369a0000 as core::ffi::c_int as uint32_t,
            0x369c0000 as core::ffi::c_int as uint32_t,
            0x369e0000 as core::ffi::c_int as uint32_t,
            0x36a00000 as core::ffi::c_int as uint32_t,
            0x36a20000 as core::ffi::c_int as uint32_t,
            0x36a40000 as core::ffi::c_int as uint32_t,
            0x36a60000 as core::ffi::c_int as uint32_t,
            0x36a80000 as core::ffi::c_int as uint32_t,
            0x36aa0000 as core::ffi::c_int as uint32_t,
            0x36ac0000 as core::ffi::c_int as uint32_t,
            0x36ae0000 as core::ffi::c_int as uint32_t,
            0x36b00000 as core::ffi::c_int as uint32_t,
            0x36b20000 as core::ffi::c_int as uint32_t,
            0x36b40000 as core::ffi::c_int as uint32_t,
            0x36b60000 as core::ffi::c_int as uint32_t,
            0x36b80000 as core::ffi::c_int as uint32_t,
            0x36ba0000 as core::ffi::c_int as uint32_t,
            0x36bc0000 as core::ffi::c_int as uint32_t,
            0x36be0000 as core::ffi::c_int as uint32_t,
            0x36c00000 as core::ffi::c_int as uint32_t,
            0x36c20000 as core::ffi::c_int as uint32_t,
            0x36c40000 as core::ffi::c_int as uint32_t,
            0x36c60000 as core::ffi::c_int as uint32_t,
            0x36c80000 as core::ffi::c_int as uint32_t,
            0x36ca0000 as core::ffi::c_int as uint32_t,
            0x36cc0000 as core::ffi::c_int as uint32_t,
            0x36ce0000 as core::ffi::c_int as uint32_t,
            0x36d00000 as core::ffi::c_int as uint32_t,
            0x36d20000 as core::ffi::c_int as uint32_t,
            0x36d40000 as core::ffi::c_int as uint32_t,
            0x36d60000 as core::ffi::c_int as uint32_t,
            0x36d80000 as core::ffi::c_int as uint32_t,
            0x36da0000 as core::ffi::c_int as uint32_t,
            0x36dc0000 as core::ffi::c_int as uint32_t,
            0x36de0000 as core::ffi::c_int as uint32_t,
            0x36e00000 as core::ffi::c_int as uint32_t,
            0x36e20000 as core::ffi::c_int as uint32_t,
            0x36e40000 as core::ffi::c_int as uint32_t,
            0x36e60000 as core::ffi::c_int as uint32_t,
            0x36e80000 as core::ffi::c_int as uint32_t,
            0x36ea0000 as core::ffi::c_int as uint32_t,
            0x36ec0000 as core::ffi::c_int as uint32_t,
            0x36ee0000 as core::ffi::c_int as uint32_t,
            0x36f00000 as core::ffi::c_int as uint32_t,
            0x36f20000 as core::ffi::c_int as uint32_t,
            0x36f40000 as core::ffi::c_int as uint32_t,
            0x36f60000 as core::ffi::c_int as uint32_t,
            0x36f80000 as core::ffi::c_int as uint32_t,
            0x36fa0000 as core::ffi::c_int as uint32_t,
            0x36fc0000 as core::ffi::c_int as uint32_t,
            0x36fe0000 as core::ffi::c_int as uint32_t,
            0x37000000 as core::ffi::c_int as uint32_t,
            0x37010000 as core::ffi::c_int as uint32_t,
            0x37020000 as core::ffi::c_int as uint32_t,
            0x37030000 as core::ffi::c_int as uint32_t,
            0x37040000 as core::ffi::c_int as uint32_t,
            0x37050000 as core::ffi::c_int as uint32_t,
            0x37060000 as core::ffi::c_int as uint32_t,
            0x37070000 as core::ffi::c_int as uint32_t,
            0x37080000 as core::ffi::c_int as uint32_t,
            0x37090000 as core::ffi::c_int as uint32_t,
            0x370a0000 as core::ffi::c_int as uint32_t,
            0x370b0000 as core::ffi::c_int as uint32_t,
            0x370c0000 as core::ffi::c_int as uint32_t,
            0x370d0000 as core::ffi::c_int as uint32_t,
            0x370e0000 as core::ffi::c_int as uint32_t,
            0x370f0000 as core::ffi::c_int as uint32_t,
            0x37100000 as core::ffi::c_int as uint32_t,
            0x37110000 as core::ffi::c_int as uint32_t,
            0x37120000 as core::ffi::c_int as uint32_t,
            0x37130000 as core::ffi::c_int as uint32_t,
            0x37140000 as core::ffi::c_int as uint32_t,
            0x37150000 as core::ffi::c_int as uint32_t,
            0x37160000 as core::ffi::c_int as uint32_t,
            0x37170000 as core::ffi::c_int as uint32_t,
            0x37180000 as core::ffi::c_int as uint32_t,
            0x37190000 as core::ffi::c_int as uint32_t,
            0x371a0000 as core::ffi::c_int as uint32_t,
            0x371b0000 as core::ffi::c_int as uint32_t,
            0x371c0000 as core::ffi::c_int as uint32_t,
            0x371d0000 as core::ffi::c_int as uint32_t,
            0x371e0000 as core::ffi::c_int as uint32_t,
            0x371f0000 as core::ffi::c_int as uint32_t,
            0x37200000 as core::ffi::c_int as uint32_t,
            0x37210000 as core::ffi::c_int as uint32_t,
            0x37220000 as core::ffi::c_int as uint32_t,
            0x37230000 as core::ffi::c_int as uint32_t,
            0x37240000 as core::ffi::c_int as uint32_t,
            0x37250000 as core::ffi::c_int as uint32_t,
            0x37260000 as core::ffi::c_int as uint32_t,
            0x37270000 as core::ffi::c_int as uint32_t,
            0x37280000 as core::ffi::c_int as uint32_t,
            0x37290000 as core::ffi::c_int as uint32_t,
            0x372a0000 as core::ffi::c_int as uint32_t,
            0x372b0000 as core::ffi::c_int as uint32_t,
            0x372c0000 as core::ffi::c_int as uint32_t,
            0x372d0000 as core::ffi::c_int as uint32_t,
            0x372e0000 as core::ffi::c_int as uint32_t,
            0x372f0000 as core::ffi::c_int as uint32_t,
            0x37300000 as core::ffi::c_int as uint32_t,
            0x37310000 as core::ffi::c_int as uint32_t,
            0x37320000 as core::ffi::c_int as uint32_t,
            0x37330000 as core::ffi::c_int as uint32_t,
            0x37340000 as core::ffi::c_int as uint32_t,
            0x37350000 as core::ffi::c_int as uint32_t,
            0x37360000 as core::ffi::c_int as uint32_t,
            0x37370000 as core::ffi::c_int as uint32_t,
            0x37380000 as core::ffi::c_int as uint32_t,
            0x37390000 as core::ffi::c_int as uint32_t,
            0x373a0000 as core::ffi::c_int as uint32_t,
            0x373b0000 as core::ffi::c_int as uint32_t,
            0x373c0000 as core::ffi::c_int as uint32_t,
            0x373d0000 as core::ffi::c_int as uint32_t,
            0x373e0000 as core::ffi::c_int as uint32_t,
            0x373f0000 as core::ffi::c_int as uint32_t,
            0x37400000 as core::ffi::c_int as uint32_t,
            0x37410000 as core::ffi::c_int as uint32_t,
            0x37420000 as core::ffi::c_int as uint32_t,
            0x37430000 as core::ffi::c_int as uint32_t,
            0x37440000 as core::ffi::c_int as uint32_t,
            0x37450000 as core::ffi::c_int as uint32_t,
            0x37460000 as core::ffi::c_int as uint32_t,
            0x37470000 as core::ffi::c_int as uint32_t,
            0x37480000 as core::ffi::c_int as uint32_t,
            0x37490000 as core::ffi::c_int as uint32_t,
            0x374a0000 as core::ffi::c_int as uint32_t,
            0x374b0000 as core::ffi::c_int as uint32_t,
            0x374c0000 as core::ffi::c_int as uint32_t,
            0x374d0000 as core::ffi::c_int as uint32_t,
            0x374e0000 as core::ffi::c_int as uint32_t,
            0x374f0000 as core::ffi::c_int as uint32_t,
            0x37500000 as core::ffi::c_int as uint32_t,
            0x37510000 as core::ffi::c_int as uint32_t,
            0x37520000 as core::ffi::c_int as uint32_t,
            0x37530000 as core::ffi::c_int as uint32_t,
            0x37540000 as core::ffi::c_int as uint32_t,
            0x37550000 as core::ffi::c_int as uint32_t,
            0x37560000 as core::ffi::c_int as uint32_t,
            0x37570000 as core::ffi::c_int as uint32_t,
            0x37580000 as core::ffi::c_int as uint32_t,
            0x37590000 as core::ffi::c_int as uint32_t,
            0x375a0000 as core::ffi::c_int as uint32_t,
            0x375b0000 as core::ffi::c_int as uint32_t,
            0x375c0000 as core::ffi::c_int as uint32_t,
            0x375d0000 as core::ffi::c_int as uint32_t,
            0x375e0000 as core::ffi::c_int as uint32_t,
            0x375f0000 as core::ffi::c_int as uint32_t,
            0x37600000 as core::ffi::c_int as uint32_t,
            0x37610000 as core::ffi::c_int as uint32_t,
            0x37620000 as core::ffi::c_int as uint32_t,
            0x37630000 as core::ffi::c_int as uint32_t,
            0x37640000 as core::ffi::c_int as uint32_t,
            0x37650000 as core::ffi::c_int as uint32_t,
            0x37660000 as core::ffi::c_int as uint32_t,
            0x37670000 as core::ffi::c_int as uint32_t,
            0x37680000 as core::ffi::c_int as uint32_t,
            0x37690000 as core::ffi::c_int as uint32_t,
            0x376a0000 as core::ffi::c_int as uint32_t,
            0x376b0000 as core::ffi::c_int as uint32_t,
            0x376c0000 as core::ffi::c_int as uint32_t,
            0x376d0000 as core::ffi::c_int as uint32_t,
            0x376e0000 as core::ffi::c_int as uint32_t,
            0x376f0000 as core::ffi::c_int as uint32_t,
            0x37700000 as core::ffi::c_int as uint32_t,
            0x37710000 as core::ffi::c_int as uint32_t,
            0x37720000 as core::ffi::c_int as uint32_t,
            0x37730000 as core::ffi::c_int as uint32_t,
            0x37740000 as core::ffi::c_int as uint32_t,
            0x37750000 as core::ffi::c_int as uint32_t,
            0x37760000 as core::ffi::c_int as uint32_t,
            0x37770000 as core::ffi::c_int as uint32_t,
            0x37780000 as core::ffi::c_int as uint32_t,
            0x37790000 as core::ffi::c_int as uint32_t,
            0x377a0000 as core::ffi::c_int as uint32_t,
            0x377b0000 as core::ffi::c_int as uint32_t,
            0x377c0000 as core::ffi::c_int as uint32_t,
            0x377d0000 as core::ffi::c_int as uint32_t,
            0x377e0000 as core::ffi::c_int as uint32_t,
            0x377f0000 as core::ffi::c_int as uint32_t,
            0x37800000 as core::ffi::c_int as uint32_t,
            0x37808000 as core::ffi::c_int as uint32_t,
            0x37810000 as core::ffi::c_int as uint32_t,
            0x37818000 as core::ffi::c_int as uint32_t,
            0x37820000 as core::ffi::c_int as uint32_t,
            0x37828000 as core::ffi::c_int as uint32_t,
            0x37830000 as core::ffi::c_int as uint32_t,
            0x37838000 as core::ffi::c_int as uint32_t,
            0x37840000 as core::ffi::c_int as uint32_t,
            0x37848000 as core::ffi::c_int as uint32_t,
            0x37850000 as core::ffi::c_int as uint32_t,
            0x37858000 as core::ffi::c_int as uint32_t,
            0x37860000 as core::ffi::c_int as uint32_t,
            0x37868000 as core::ffi::c_int as uint32_t,
            0x37870000 as core::ffi::c_int as uint32_t,
            0x37878000 as core::ffi::c_int as uint32_t,
            0x37880000 as core::ffi::c_int as uint32_t,
            0x37888000 as core::ffi::c_int as uint32_t,
            0x37890000 as core::ffi::c_int as uint32_t,
            0x37898000 as core::ffi::c_int as uint32_t,
            0x378a0000 as core::ffi::c_int as uint32_t,
            0x378a8000 as core::ffi::c_int as uint32_t,
            0x378b0000 as core::ffi::c_int as uint32_t,
            0x378b8000 as core::ffi::c_int as uint32_t,
            0x378c0000 as core::ffi::c_int as uint32_t,
            0x378c8000 as core::ffi::c_int as uint32_t,
            0x378d0000 as core::ffi::c_int as uint32_t,
            0x378d8000 as core::ffi::c_int as uint32_t,
            0x378e0000 as core::ffi::c_int as uint32_t,
            0x378e8000 as core::ffi::c_int as uint32_t,
            0x378f0000 as core::ffi::c_int as uint32_t,
            0x378f8000 as core::ffi::c_int as uint32_t,
            0x37900000 as core::ffi::c_int as uint32_t,
            0x37908000 as core::ffi::c_int as uint32_t,
            0x37910000 as core::ffi::c_int as uint32_t,
            0x37918000 as core::ffi::c_int as uint32_t,
            0x37920000 as core::ffi::c_int as uint32_t,
            0x37928000 as core::ffi::c_int as uint32_t,
            0x37930000 as core::ffi::c_int as uint32_t,
            0x37938000 as core::ffi::c_int as uint32_t,
            0x37940000 as core::ffi::c_int as uint32_t,
            0x37948000 as core::ffi::c_int as uint32_t,
            0x37950000 as core::ffi::c_int as uint32_t,
            0x37958000 as core::ffi::c_int as uint32_t,
            0x37960000 as core::ffi::c_int as uint32_t,
            0x37968000 as core::ffi::c_int as uint32_t,
            0x37970000 as core::ffi::c_int as uint32_t,
            0x37978000 as core::ffi::c_int as uint32_t,
            0x37980000 as core::ffi::c_int as uint32_t,
            0x37988000 as core::ffi::c_int as uint32_t,
            0x37990000 as core::ffi::c_int as uint32_t,
            0x37998000 as core::ffi::c_int as uint32_t,
            0x379a0000 as core::ffi::c_int as uint32_t,
            0x379a8000 as core::ffi::c_int as uint32_t,
            0x379b0000 as core::ffi::c_int as uint32_t,
            0x379b8000 as core::ffi::c_int as uint32_t,
            0x379c0000 as core::ffi::c_int as uint32_t,
            0x379c8000 as core::ffi::c_int as uint32_t,
            0x379d0000 as core::ffi::c_int as uint32_t,
            0x379d8000 as core::ffi::c_int as uint32_t,
            0x379e0000 as core::ffi::c_int as uint32_t,
            0x379e8000 as core::ffi::c_int as uint32_t,
            0x379f0000 as core::ffi::c_int as uint32_t,
            0x379f8000 as core::ffi::c_int as uint32_t,
            0x37a00000 as core::ffi::c_int as uint32_t,
            0x37a08000 as core::ffi::c_int as uint32_t,
            0x37a10000 as core::ffi::c_int as uint32_t,
            0x37a18000 as core::ffi::c_int as uint32_t,
            0x37a20000 as core::ffi::c_int as uint32_t,
            0x37a28000 as core::ffi::c_int as uint32_t,
            0x37a30000 as core::ffi::c_int as uint32_t,
            0x37a38000 as core::ffi::c_int as uint32_t,
            0x37a40000 as core::ffi::c_int as uint32_t,
            0x37a48000 as core::ffi::c_int as uint32_t,
            0x37a50000 as core::ffi::c_int as uint32_t,
            0x37a58000 as core::ffi::c_int as uint32_t,
            0x37a60000 as core::ffi::c_int as uint32_t,
            0x37a68000 as core::ffi::c_int as uint32_t,
            0x37a70000 as core::ffi::c_int as uint32_t,
            0x37a78000 as core::ffi::c_int as uint32_t,
            0x37a80000 as core::ffi::c_int as uint32_t,
            0x37a88000 as core::ffi::c_int as uint32_t,
            0x37a90000 as core::ffi::c_int as uint32_t,
            0x37a98000 as core::ffi::c_int as uint32_t,
            0x37aa0000 as core::ffi::c_int as uint32_t,
            0x37aa8000 as core::ffi::c_int as uint32_t,
            0x37ab0000 as core::ffi::c_int as uint32_t,
            0x37ab8000 as core::ffi::c_int as uint32_t,
            0x37ac0000 as core::ffi::c_int as uint32_t,
            0x37ac8000 as core::ffi::c_int as uint32_t,
            0x37ad0000 as core::ffi::c_int as uint32_t,
            0x37ad8000 as core::ffi::c_int as uint32_t,
            0x37ae0000 as core::ffi::c_int as uint32_t,
            0x37ae8000 as core::ffi::c_int as uint32_t,
            0x37af0000 as core::ffi::c_int as uint32_t,
            0x37af8000 as core::ffi::c_int as uint32_t,
            0x37b00000 as core::ffi::c_int as uint32_t,
            0x37b08000 as core::ffi::c_int as uint32_t,
            0x37b10000 as core::ffi::c_int as uint32_t,
            0x37b18000 as core::ffi::c_int as uint32_t,
            0x37b20000 as core::ffi::c_int as uint32_t,
            0x37b28000 as core::ffi::c_int as uint32_t,
            0x37b30000 as core::ffi::c_int as uint32_t,
            0x37b38000 as core::ffi::c_int as uint32_t,
            0x37b40000 as core::ffi::c_int as uint32_t,
            0x37b48000 as core::ffi::c_int as uint32_t,
            0x37b50000 as core::ffi::c_int as uint32_t,
            0x37b58000 as core::ffi::c_int as uint32_t,
            0x37b60000 as core::ffi::c_int as uint32_t,
            0x37b68000 as core::ffi::c_int as uint32_t,
            0x37b70000 as core::ffi::c_int as uint32_t,
            0x37b78000 as core::ffi::c_int as uint32_t,
            0x37b80000 as core::ffi::c_int as uint32_t,
            0x37b88000 as core::ffi::c_int as uint32_t,
            0x37b90000 as core::ffi::c_int as uint32_t,
            0x37b98000 as core::ffi::c_int as uint32_t,
            0x37ba0000 as core::ffi::c_int as uint32_t,
            0x37ba8000 as core::ffi::c_int as uint32_t,
            0x37bb0000 as core::ffi::c_int as uint32_t,
            0x37bb8000 as core::ffi::c_int as uint32_t,
            0x37bc0000 as core::ffi::c_int as uint32_t,
            0x37bc8000 as core::ffi::c_int as uint32_t,
            0x37bd0000 as core::ffi::c_int as uint32_t,
            0x37bd8000 as core::ffi::c_int as uint32_t,
            0x37be0000 as core::ffi::c_int as uint32_t,
            0x37be8000 as core::ffi::c_int as uint32_t,
            0x37bf0000 as core::ffi::c_int as uint32_t,
            0x37bf8000 as core::ffi::c_int as uint32_t,
            0x37c00000 as core::ffi::c_int as uint32_t,
            0x37c08000 as core::ffi::c_int as uint32_t,
            0x37c10000 as core::ffi::c_int as uint32_t,
            0x37c18000 as core::ffi::c_int as uint32_t,
            0x37c20000 as core::ffi::c_int as uint32_t,
            0x37c28000 as core::ffi::c_int as uint32_t,
            0x37c30000 as core::ffi::c_int as uint32_t,
            0x37c38000 as core::ffi::c_int as uint32_t,
            0x37c40000 as core::ffi::c_int as uint32_t,
            0x37c48000 as core::ffi::c_int as uint32_t,
            0x37c50000 as core::ffi::c_int as uint32_t,
            0x37c58000 as core::ffi::c_int as uint32_t,
            0x37c60000 as core::ffi::c_int as uint32_t,
            0x37c68000 as core::ffi::c_int as uint32_t,
            0x37c70000 as core::ffi::c_int as uint32_t,
            0x37c78000 as core::ffi::c_int as uint32_t,
            0x37c80000 as core::ffi::c_int as uint32_t,
            0x37c88000 as core::ffi::c_int as uint32_t,
            0x37c90000 as core::ffi::c_int as uint32_t,
            0x37c98000 as core::ffi::c_int as uint32_t,
            0x37ca0000 as core::ffi::c_int as uint32_t,
            0x37ca8000 as core::ffi::c_int as uint32_t,
            0x37cb0000 as core::ffi::c_int as uint32_t,
            0x37cb8000 as core::ffi::c_int as uint32_t,
            0x37cc0000 as core::ffi::c_int as uint32_t,
            0x37cc8000 as core::ffi::c_int as uint32_t,
            0x37cd0000 as core::ffi::c_int as uint32_t,
            0x37cd8000 as core::ffi::c_int as uint32_t,
            0x37ce0000 as core::ffi::c_int as uint32_t,
            0x37ce8000 as core::ffi::c_int as uint32_t,
            0x37cf0000 as core::ffi::c_int as uint32_t,
            0x37cf8000 as core::ffi::c_int as uint32_t,
            0x37d00000 as core::ffi::c_int as uint32_t,
            0x37d08000 as core::ffi::c_int as uint32_t,
            0x37d10000 as core::ffi::c_int as uint32_t,
            0x37d18000 as core::ffi::c_int as uint32_t,
            0x37d20000 as core::ffi::c_int as uint32_t,
            0x37d28000 as core::ffi::c_int as uint32_t,
            0x37d30000 as core::ffi::c_int as uint32_t,
            0x37d38000 as core::ffi::c_int as uint32_t,
            0x37d40000 as core::ffi::c_int as uint32_t,
            0x37d48000 as core::ffi::c_int as uint32_t,
            0x37d50000 as core::ffi::c_int as uint32_t,
            0x37d58000 as core::ffi::c_int as uint32_t,
            0x37d60000 as core::ffi::c_int as uint32_t,
            0x37d68000 as core::ffi::c_int as uint32_t,
            0x37d70000 as core::ffi::c_int as uint32_t,
            0x37d78000 as core::ffi::c_int as uint32_t,
            0x37d80000 as core::ffi::c_int as uint32_t,
            0x37d88000 as core::ffi::c_int as uint32_t,
            0x37d90000 as core::ffi::c_int as uint32_t,
            0x37d98000 as core::ffi::c_int as uint32_t,
            0x37da0000 as core::ffi::c_int as uint32_t,
            0x37da8000 as core::ffi::c_int as uint32_t,
            0x37db0000 as core::ffi::c_int as uint32_t,
            0x37db8000 as core::ffi::c_int as uint32_t,
            0x37dc0000 as core::ffi::c_int as uint32_t,
            0x37dc8000 as core::ffi::c_int as uint32_t,
            0x37dd0000 as core::ffi::c_int as uint32_t,
            0x37dd8000 as core::ffi::c_int as uint32_t,
            0x37de0000 as core::ffi::c_int as uint32_t,
            0x37de8000 as core::ffi::c_int as uint32_t,
            0x37df0000 as core::ffi::c_int as uint32_t,
            0x37df8000 as core::ffi::c_int as uint32_t,
            0x37e00000 as core::ffi::c_int as uint32_t,
            0x37e08000 as core::ffi::c_int as uint32_t,
            0x37e10000 as core::ffi::c_int as uint32_t,
            0x37e18000 as core::ffi::c_int as uint32_t,
            0x37e20000 as core::ffi::c_int as uint32_t,
            0x37e28000 as core::ffi::c_int as uint32_t,
            0x37e30000 as core::ffi::c_int as uint32_t,
            0x37e38000 as core::ffi::c_int as uint32_t,
            0x37e40000 as core::ffi::c_int as uint32_t,
            0x37e48000 as core::ffi::c_int as uint32_t,
            0x37e50000 as core::ffi::c_int as uint32_t,
            0x37e58000 as core::ffi::c_int as uint32_t,
            0x37e60000 as core::ffi::c_int as uint32_t,
            0x37e68000 as core::ffi::c_int as uint32_t,
            0x37e70000 as core::ffi::c_int as uint32_t,
            0x37e78000 as core::ffi::c_int as uint32_t,
            0x37e80000 as core::ffi::c_int as uint32_t,
            0x37e88000 as core::ffi::c_int as uint32_t,
            0x37e90000 as core::ffi::c_int as uint32_t,
            0x37e98000 as core::ffi::c_int as uint32_t,
            0x37ea0000 as core::ffi::c_int as uint32_t,
            0x37ea8000 as core::ffi::c_int as uint32_t,
            0x37eb0000 as core::ffi::c_int as uint32_t,
            0x37eb8000 as core::ffi::c_int as uint32_t,
            0x37ec0000 as core::ffi::c_int as uint32_t,
            0x37ec8000 as core::ffi::c_int as uint32_t,
            0x37ed0000 as core::ffi::c_int as uint32_t,
            0x37ed8000 as core::ffi::c_int as uint32_t,
            0x37ee0000 as core::ffi::c_int as uint32_t,
            0x37ee8000 as core::ffi::c_int as uint32_t,
            0x37ef0000 as core::ffi::c_int as uint32_t,
            0x37ef8000 as core::ffi::c_int as uint32_t,
            0x37f00000 as core::ffi::c_int as uint32_t,
            0x37f08000 as core::ffi::c_int as uint32_t,
            0x37f10000 as core::ffi::c_int as uint32_t,
            0x37f18000 as core::ffi::c_int as uint32_t,
            0x37f20000 as core::ffi::c_int as uint32_t,
            0x37f28000 as core::ffi::c_int as uint32_t,
            0x37f30000 as core::ffi::c_int as uint32_t,
            0x37f38000 as core::ffi::c_int as uint32_t,
            0x37f40000 as core::ffi::c_int as uint32_t,
            0x37f48000 as core::ffi::c_int as uint32_t,
            0x37f50000 as core::ffi::c_int as uint32_t,
            0x37f58000 as core::ffi::c_int as uint32_t,
            0x37f60000 as core::ffi::c_int as uint32_t,
            0x37f68000 as core::ffi::c_int as uint32_t,
            0x37f70000 as core::ffi::c_int as uint32_t,
            0x37f78000 as core::ffi::c_int as uint32_t,
            0x37f80000 as core::ffi::c_int as uint32_t,
            0x37f88000 as core::ffi::c_int as uint32_t,
            0x37f90000 as core::ffi::c_int as uint32_t,
            0x37f98000 as core::ffi::c_int as uint32_t,
            0x37fa0000 as core::ffi::c_int as uint32_t,
            0x37fa8000 as core::ffi::c_int as uint32_t,
            0x37fb0000 as core::ffi::c_int as uint32_t,
            0x37fb8000 as core::ffi::c_int as uint32_t,
            0x37fc0000 as core::ffi::c_int as uint32_t,
            0x37fc8000 as core::ffi::c_int as uint32_t,
            0x37fd0000 as core::ffi::c_int as uint32_t,
            0x37fd8000 as core::ffi::c_int as uint32_t,
            0x37fe0000 as core::ffi::c_int as uint32_t,
            0x37fe8000 as core::ffi::c_int as uint32_t,
            0x37ff0000 as core::ffi::c_int as uint32_t,
            0x37ff8000 as core::ffi::c_int as uint32_t,
            0x38000000 as core::ffi::c_int as uint32_t,
            0x38004000 as core::ffi::c_int as uint32_t,
            0x38008000 as core::ffi::c_int as uint32_t,
            0x3800c000 as core::ffi::c_int as uint32_t,
            0x38010000 as core::ffi::c_int as uint32_t,
            0x38014000 as core::ffi::c_int as uint32_t,
            0x38018000 as core::ffi::c_int as uint32_t,
            0x3801c000 as core::ffi::c_int as uint32_t,
            0x38020000 as core::ffi::c_int as uint32_t,
            0x38024000 as core::ffi::c_int as uint32_t,
            0x38028000 as core::ffi::c_int as uint32_t,
            0x3802c000 as core::ffi::c_int as uint32_t,
            0x38030000 as core::ffi::c_int as uint32_t,
            0x38034000 as core::ffi::c_int as uint32_t,
            0x38038000 as core::ffi::c_int as uint32_t,
            0x3803c000 as core::ffi::c_int as uint32_t,
            0x38040000 as core::ffi::c_int as uint32_t,
            0x38044000 as core::ffi::c_int as uint32_t,
            0x38048000 as core::ffi::c_int as uint32_t,
            0x3804c000 as core::ffi::c_int as uint32_t,
            0x38050000 as core::ffi::c_int as uint32_t,
            0x38054000 as core::ffi::c_int as uint32_t,
            0x38058000 as core::ffi::c_int as uint32_t,
            0x3805c000 as core::ffi::c_int as uint32_t,
            0x38060000 as core::ffi::c_int as uint32_t,
            0x38064000 as core::ffi::c_int as uint32_t,
            0x38068000 as core::ffi::c_int as uint32_t,
            0x3806c000 as core::ffi::c_int as uint32_t,
            0x38070000 as core::ffi::c_int as uint32_t,
            0x38074000 as core::ffi::c_int as uint32_t,
            0x38078000 as core::ffi::c_int as uint32_t,
            0x3807c000 as core::ffi::c_int as uint32_t,
            0x38080000 as core::ffi::c_int as uint32_t,
            0x38084000 as core::ffi::c_int as uint32_t,
            0x38088000 as core::ffi::c_int as uint32_t,
            0x3808c000 as core::ffi::c_int as uint32_t,
            0x38090000 as core::ffi::c_int as uint32_t,
            0x38094000 as core::ffi::c_int as uint32_t,
            0x38098000 as core::ffi::c_int as uint32_t,
            0x3809c000 as core::ffi::c_int as uint32_t,
            0x380a0000 as core::ffi::c_int as uint32_t,
            0x380a4000 as core::ffi::c_int as uint32_t,
            0x380a8000 as core::ffi::c_int as uint32_t,
            0x380ac000 as core::ffi::c_int as uint32_t,
            0x380b0000 as core::ffi::c_int as uint32_t,
            0x380b4000 as core::ffi::c_int as uint32_t,
            0x380b8000 as core::ffi::c_int as uint32_t,
            0x380bc000 as core::ffi::c_int as uint32_t,
            0x380c0000 as core::ffi::c_int as uint32_t,
            0x380c4000 as core::ffi::c_int as uint32_t,
            0x380c8000 as core::ffi::c_int as uint32_t,
            0x380cc000 as core::ffi::c_int as uint32_t,
            0x380d0000 as core::ffi::c_int as uint32_t,
            0x380d4000 as core::ffi::c_int as uint32_t,
            0x380d8000 as core::ffi::c_int as uint32_t,
            0x380dc000 as core::ffi::c_int as uint32_t,
            0x380e0000 as core::ffi::c_int as uint32_t,
            0x380e4000 as core::ffi::c_int as uint32_t,
            0x380e8000 as core::ffi::c_int as uint32_t,
            0x380ec000 as core::ffi::c_int as uint32_t,
            0x380f0000 as core::ffi::c_int as uint32_t,
            0x380f4000 as core::ffi::c_int as uint32_t,
            0x380f8000 as core::ffi::c_int as uint32_t,
            0x380fc000 as core::ffi::c_int as uint32_t,
            0x38100000 as core::ffi::c_int as uint32_t,
            0x38104000 as core::ffi::c_int as uint32_t,
            0x38108000 as core::ffi::c_int as uint32_t,
            0x3810c000 as core::ffi::c_int as uint32_t,
            0x38110000 as core::ffi::c_int as uint32_t,
            0x38114000 as core::ffi::c_int as uint32_t,
            0x38118000 as core::ffi::c_int as uint32_t,
            0x3811c000 as core::ffi::c_int as uint32_t,
            0x38120000 as core::ffi::c_int as uint32_t,
            0x38124000 as core::ffi::c_int as uint32_t,
            0x38128000 as core::ffi::c_int as uint32_t,
            0x3812c000 as core::ffi::c_int as uint32_t,
            0x38130000 as core::ffi::c_int as uint32_t,
            0x38134000 as core::ffi::c_int as uint32_t,
            0x38138000 as core::ffi::c_int as uint32_t,
            0x3813c000 as core::ffi::c_int as uint32_t,
            0x38140000 as core::ffi::c_int as uint32_t,
            0x38144000 as core::ffi::c_int as uint32_t,
            0x38148000 as core::ffi::c_int as uint32_t,
            0x3814c000 as core::ffi::c_int as uint32_t,
            0x38150000 as core::ffi::c_int as uint32_t,
            0x38154000 as core::ffi::c_int as uint32_t,
            0x38158000 as core::ffi::c_int as uint32_t,
            0x3815c000 as core::ffi::c_int as uint32_t,
            0x38160000 as core::ffi::c_int as uint32_t,
            0x38164000 as core::ffi::c_int as uint32_t,
            0x38168000 as core::ffi::c_int as uint32_t,
            0x3816c000 as core::ffi::c_int as uint32_t,
            0x38170000 as core::ffi::c_int as uint32_t,
            0x38174000 as core::ffi::c_int as uint32_t,
            0x38178000 as core::ffi::c_int as uint32_t,
            0x3817c000 as core::ffi::c_int as uint32_t,
            0x38180000 as core::ffi::c_int as uint32_t,
            0x38184000 as core::ffi::c_int as uint32_t,
            0x38188000 as core::ffi::c_int as uint32_t,
            0x3818c000 as core::ffi::c_int as uint32_t,
            0x38190000 as core::ffi::c_int as uint32_t,
            0x38194000 as core::ffi::c_int as uint32_t,
            0x38198000 as core::ffi::c_int as uint32_t,
            0x3819c000 as core::ffi::c_int as uint32_t,
            0x381a0000 as core::ffi::c_int as uint32_t,
            0x381a4000 as core::ffi::c_int as uint32_t,
            0x381a8000 as core::ffi::c_int as uint32_t,
            0x381ac000 as core::ffi::c_int as uint32_t,
            0x381b0000 as core::ffi::c_int as uint32_t,
            0x381b4000 as core::ffi::c_int as uint32_t,
            0x381b8000 as core::ffi::c_int as uint32_t,
            0x381bc000 as core::ffi::c_int as uint32_t,
            0x381c0000 as core::ffi::c_int as uint32_t,
            0x381c4000 as core::ffi::c_int as uint32_t,
            0x381c8000 as core::ffi::c_int as uint32_t,
            0x381cc000 as core::ffi::c_int as uint32_t,
            0x381d0000 as core::ffi::c_int as uint32_t,
            0x381d4000 as core::ffi::c_int as uint32_t,
            0x381d8000 as core::ffi::c_int as uint32_t,
            0x381dc000 as core::ffi::c_int as uint32_t,
            0x381e0000 as core::ffi::c_int as uint32_t,
            0x381e4000 as core::ffi::c_int as uint32_t,
            0x381e8000 as core::ffi::c_int as uint32_t,
            0x381ec000 as core::ffi::c_int as uint32_t,
            0x381f0000 as core::ffi::c_int as uint32_t,
            0x381f4000 as core::ffi::c_int as uint32_t,
            0x381f8000 as core::ffi::c_int as uint32_t,
            0x381fc000 as core::ffi::c_int as uint32_t,
            0x38200000 as core::ffi::c_int as uint32_t,
            0x38204000 as core::ffi::c_int as uint32_t,
            0x38208000 as core::ffi::c_int as uint32_t,
            0x3820c000 as core::ffi::c_int as uint32_t,
            0x38210000 as core::ffi::c_int as uint32_t,
            0x38214000 as core::ffi::c_int as uint32_t,
            0x38218000 as core::ffi::c_int as uint32_t,
            0x3821c000 as core::ffi::c_int as uint32_t,
            0x38220000 as core::ffi::c_int as uint32_t,
            0x38224000 as core::ffi::c_int as uint32_t,
            0x38228000 as core::ffi::c_int as uint32_t,
            0x3822c000 as core::ffi::c_int as uint32_t,
            0x38230000 as core::ffi::c_int as uint32_t,
            0x38234000 as core::ffi::c_int as uint32_t,
            0x38238000 as core::ffi::c_int as uint32_t,
            0x3823c000 as core::ffi::c_int as uint32_t,
            0x38240000 as core::ffi::c_int as uint32_t,
            0x38244000 as core::ffi::c_int as uint32_t,
            0x38248000 as core::ffi::c_int as uint32_t,
            0x3824c000 as core::ffi::c_int as uint32_t,
            0x38250000 as core::ffi::c_int as uint32_t,
            0x38254000 as core::ffi::c_int as uint32_t,
            0x38258000 as core::ffi::c_int as uint32_t,
            0x3825c000 as core::ffi::c_int as uint32_t,
            0x38260000 as core::ffi::c_int as uint32_t,
            0x38264000 as core::ffi::c_int as uint32_t,
            0x38268000 as core::ffi::c_int as uint32_t,
            0x3826c000 as core::ffi::c_int as uint32_t,
            0x38270000 as core::ffi::c_int as uint32_t,
            0x38274000 as core::ffi::c_int as uint32_t,
            0x38278000 as core::ffi::c_int as uint32_t,
            0x3827c000 as core::ffi::c_int as uint32_t,
            0x38280000 as core::ffi::c_int as uint32_t,
            0x38284000 as core::ffi::c_int as uint32_t,
            0x38288000 as core::ffi::c_int as uint32_t,
            0x3828c000 as core::ffi::c_int as uint32_t,
            0x38290000 as core::ffi::c_int as uint32_t,
            0x38294000 as core::ffi::c_int as uint32_t,
            0x38298000 as core::ffi::c_int as uint32_t,
            0x3829c000 as core::ffi::c_int as uint32_t,
            0x382a0000 as core::ffi::c_int as uint32_t,
            0x382a4000 as core::ffi::c_int as uint32_t,
            0x382a8000 as core::ffi::c_int as uint32_t,
            0x382ac000 as core::ffi::c_int as uint32_t,
            0x382b0000 as core::ffi::c_int as uint32_t,
            0x382b4000 as core::ffi::c_int as uint32_t,
            0x382b8000 as core::ffi::c_int as uint32_t,
            0x382bc000 as core::ffi::c_int as uint32_t,
            0x382c0000 as core::ffi::c_int as uint32_t,
            0x382c4000 as core::ffi::c_int as uint32_t,
            0x382c8000 as core::ffi::c_int as uint32_t,
            0x382cc000 as core::ffi::c_int as uint32_t,
            0x382d0000 as core::ffi::c_int as uint32_t,
            0x382d4000 as core::ffi::c_int as uint32_t,
            0x382d8000 as core::ffi::c_int as uint32_t,
            0x382dc000 as core::ffi::c_int as uint32_t,
            0x382e0000 as core::ffi::c_int as uint32_t,
            0x382e4000 as core::ffi::c_int as uint32_t,
            0x382e8000 as core::ffi::c_int as uint32_t,
            0x382ec000 as core::ffi::c_int as uint32_t,
            0x382f0000 as core::ffi::c_int as uint32_t,
            0x382f4000 as core::ffi::c_int as uint32_t,
            0x382f8000 as core::ffi::c_int as uint32_t,
            0x382fc000 as core::ffi::c_int as uint32_t,
            0x38300000 as core::ffi::c_int as uint32_t,
            0x38304000 as core::ffi::c_int as uint32_t,
            0x38308000 as core::ffi::c_int as uint32_t,
            0x3830c000 as core::ffi::c_int as uint32_t,
            0x38310000 as core::ffi::c_int as uint32_t,
            0x38314000 as core::ffi::c_int as uint32_t,
            0x38318000 as core::ffi::c_int as uint32_t,
            0x3831c000 as core::ffi::c_int as uint32_t,
            0x38320000 as core::ffi::c_int as uint32_t,
            0x38324000 as core::ffi::c_int as uint32_t,
            0x38328000 as core::ffi::c_int as uint32_t,
            0x3832c000 as core::ffi::c_int as uint32_t,
            0x38330000 as core::ffi::c_int as uint32_t,
            0x38334000 as core::ffi::c_int as uint32_t,
            0x38338000 as core::ffi::c_int as uint32_t,
            0x3833c000 as core::ffi::c_int as uint32_t,
            0x38340000 as core::ffi::c_int as uint32_t,
            0x38344000 as core::ffi::c_int as uint32_t,
            0x38348000 as core::ffi::c_int as uint32_t,
            0x3834c000 as core::ffi::c_int as uint32_t,
            0x38350000 as core::ffi::c_int as uint32_t,
            0x38354000 as core::ffi::c_int as uint32_t,
            0x38358000 as core::ffi::c_int as uint32_t,
            0x3835c000 as core::ffi::c_int as uint32_t,
            0x38360000 as core::ffi::c_int as uint32_t,
            0x38364000 as core::ffi::c_int as uint32_t,
            0x38368000 as core::ffi::c_int as uint32_t,
            0x3836c000 as core::ffi::c_int as uint32_t,
            0x38370000 as core::ffi::c_int as uint32_t,
            0x38374000 as core::ffi::c_int as uint32_t,
            0x38378000 as core::ffi::c_int as uint32_t,
            0x3837c000 as core::ffi::c_int as uint32_t,
            0x38380000 as core::ffi::c_int as uint32_t,
            0x38384000 as core::ffi::c_int as uint32_t,
            0x38388000 as core::ffi::c_int as uint32_t,
            0x3838c000 as core::ffi::c_int as uint32_t,
            0x38390000 as core::ffi::c_int as uint32_t,
            0x38394000 as core::ffi::c_int as uint32_t,
            0x38398000 as core::ffi::c_int as uint32_t,
            0x3839c000 as core::ffi::c_int as uint32_t,
            0x383a0000 as core::ffi::c_int as uint32_t,
            0x383a4000 as core::ffi::c_int as uint32_t,
            0x383a8000 as core::ffi::c_int as uint32_t,
            0x383ac000 as core::ffi::c_int as uint32_t,
            0x383b0000 as core::ffi::c_int as uint32_t,
            0x383b4000 as core::ffi::c_int as uint32_t,
            0x383b8000 as core::ffi::c_int as uint32_t,
            0x383bc000 as core::ffi::c_int as uint32_t,
            0x383c0000 as core::ffi::c_int as uint32_t,
            0x383c4000 as core::ffi::c_int as uint32_t,
            0x383c8000 as core::ffi::c_int as uint32_t,
            0x383cc000 as core::ffi::c_int as uint32_t,
            0x383d0000 as core::ffi::c_int as uint32_t,
            0x383d4000 as core::ffi::c_int as uint32_t,
            0x383d8000 as core::ffi::c_int as uint32_t,
            0x383dc000 as core::ffi::c_int as uint32_t,
            0x383e0000 as core::ffi::c_int as uint32_t,
            0x383e4000 as core::ffi::c_int as uint32_t,
            0x383e8000 as core::ffi::c_int as uint32_t,
            0x383ec000 as core::ffi::c_int as uint32_t,
            0x383f0000 as core::ffi::c_int as uint32_t,
            0x383f4000 as core::ffi::c_int as uint32_t,
            0x383f8000 as core::ffi::c_int as uint32_t,
            0x383fc000 as core::ffi::c_int as uint32_t,
            0x38400000 as core::ffi::c_int as uint32_t,
            0x38404000 as core::ffi::c_int as uint32_t,
            0x38408000 as core::ffi::c_int as uint32_t,
            0x3840c000 as core::ffi::c_int as uint32_t,
            0x38410000 as core::ffi::c_int as uint32_t,
            0x38414000 as core::ffi::c_int as uint32_t,
            0x38418000 as core::ffi::c_int as uint32_t,
            0x3841c000 as core::ffi::c_int as uint32_t,
            0x38420000 as core::ffi::c_int as uint32_t,
            0x38424000 as core::ffi::c_int as uint32_t,
            0x38428000 as core::ffi::c_int as uint32_t,
            0x3842c000 as core::ffi::c_int as uint32_t,
            0x38430000 as core::ffi::c_int as uint32_t,
            0x38434000 as core::ffi::c_int as uint32_t,
            0x38438000 as core::ffi::c_int as uint32_t,
            0x3843c000 as core::ffi::c_int as uint32_t,
            0x38440000 as core::ffi::c_int as uint32_t,
            0x38444000 as core::ffi::c_int as uint32_t,
            0x38448000 as core::ffi::c_int as uint32_t,
            0x3844c000 as core::ffi::c_int as uint32_t,
            0x38450000 as core::ffi::c_int as uint32_t,
            0x38454000 as core::ffi::c_int as uint32_t,
            0x38458000 as core::ffi::c_int as uint32_t,
            0x3845c000 as core::ffi::c_int as uint32_t,
            0x38460000 as core::ffi::c_int as uint32_t,
            0x38464000 as core::ffi::c_int as uint32_t,
            0x38468000 as core::ffi::c_int as uint32_t,
            0x3846c000 as core::ffi::c_int as uint32_t,
            0x38470000 as core::ffi::c_int as uint32_t,
            0x38474000 as core::ffi::c_int as uint32_t,
            0x38478000 as core::ffi::c_int as uint32_t,
            0x3847c000 as core::ffi::c_int as uint32_t,
            0x38480000 as core::ffi::c_int as uint32_t,
            0x38484000 as core::ffi::c_int as uint32_t,
            0x38488000 as core::ffi::c_int as uint32_t,
            0x3848c000 as core::ffi::c_int as uint32_t,
            0x38490000 as core::ffi::c_int as uint32_t,
            0x38494000 as core::ffi::c_int as uint32_t,
            0x38498000 as core::ffi::c_int as uint32_t,
            0x3849c000 as core::ffi::c_int as uint32_t,
            0x384a0000 as core::ffi::c_int as uint32_t,
            0x384a4000 as core::ffi::c_int as uint32_t,
            0x384a8000 as core::ffi::c_int as uint32_t,
            0x384ac000 as core::ffi::c_int as uint32_t,
            0x384b0000 as core::ffi::c_int as uint32_t,
            0x384b4000 as core::ffi::c_int as uint32_t,
            0x384b8000 as core::ffi::c_int as uint32_t,
            0x384bc000 as core::ffi::c_int as uint32_t,
            0x384c0000 as core::ffi::c_int as uint32_t,
            0x384c4000 as core::ffi::c_int as uint32_t,
            0x384c8000 as core::ffi::c_int as uint32_t,
            0x384cc000 as core::ffi::c_int as uint32_t,
            0x384d0000 as core::ffi::c_int as uint32_t,
            0x384d4000 as core::ffi::c_int as uint32_t,
            0x384d8000 as core::ffi::c_int as uint32_t,
            0x384dc000 as core::ffi::c_int as uint32_t,
            0x384e0000 as core::ffi::c_int as uint32_t,
            0x384e4000 as core::ffi::c_int as uint32_t,
            0x384e8000 as core::ffi::c_int as uint32_t,
            0x384ec000 as core::ffi::c_int as uint32_t,
            0x384f0000 as core::ffi::c_int as uint32_t,
            0x384f4000 as core::ffi::c_int as uint32_t,
            0x384f8000 as core::ffi::c_int as uint32_t,
            0x384fc000 as core::ffi::c_int as uint32_t,
            0x38500000 as core::ffi::c_int as uint32_t,
            0x38504000 as core::ffi::c_int as uint32_t,
            0x38508000 as core::ffi::c_int as uint32_t,
            0x3850c000 as core::ffi::c_int as uint32_t,
            0x38510000 as core::ffi::c_int as uint32_t,
            0x38514000 as core::ffi::c_int as uint32_t,
            0x38518000 as core::ffi::c_int as uint32_t,
            0x3851c000 as core::ffi::c_int as uint32_t,
            0x38520000 as core::ffi::c_int as uint32_t,
            0x38524000 as core::ffi::c_int as uint32_t,
            0x38528000 as core::ffi::c_int as uint32_t,
            0x3852c000 as core::ffi::c_int as uint32_t,
            0x38530000 as core::ffi::c_int as uint32_t,
            0x38534000 as core::ffi::c_int as uint32_t,
            0x38538000 as core::ffi::c_int as uint32_t,
            0x3853c000 as core::ffi::c_int as uint32_t,
            0x38540000 as core::ffi::c_int as uint32_t,
            0x38544000 as core::ffi::c_int as uint32_t,
            0x38548000 as core::ffi::c_int as uint32_t,
            0x3854c000 as core::ffi::c_int as uint32_t,
            0x38550000 as core::ffi::c_int as uint32_t,
            0x38554000 as core::ffi::c_int as uint32_t,
            0x38558000 as core::ffi::c_int as uint32_t,
            0x3855c000 as core::ffi::c_int as uint32_t,
            0x38560000 as core::ffi::c_int as uint32_t,
            0x38564000 as core::ffi::c_int as uint32_t,
            0x38568000 as core::ffi::c_int as uint32_t,
            0x3856c000 as core::ffi::c_int as uint32_t,
            0x38570000 as core::ffi::c_int as uint32_t,
            0x38574000 as core::ffi::c_int as uint32_t,
            0x38578000 as core::ffi::c_int as uint32_t,
            0x3857c000 as core::ffi::c_int as uint32_t,
            0x38580000 as core::ffi::c_int as uint32_t,
            0x38584000 as core::ffi::c_int as uint32_t,
            0x38588000 as core::ffi::c_int as uint32_t,
            0x3858c000 as core::ffi::c_int as uint32_t,
            0x38590000 as core::ffi::c_int as uint32_t,
            0x38594000 as core::ffi::c_int as uint32_t,
            0x38598000 as core::ffi::c_int as uint32_t,
            0x3859c000 as core::ffi::c_int as uint32_t,
            0x385a0000 as core::ffi::c_int as uint32_t,
            0x385a4000 as core::ffi::c_int as uint32_t,
            0x385a8000 as core::ffi::c_int as uint32_t,
            0x385ac000 as core::ffi::c_int as uint32_t,
            0x385b0000 as core::ffi::c_int as uint32_t,
            0x385b4000 as core::ffi::c_int as uint32_t,
            0x385b8000 as core::ffi::c_int as uint32_t,
            0x385bc000 as core::ffi::c_int as uint32_t,
            0x385c0000 as core::ffi::c_int as uint32_t,
            0x385c4000 as core::ffi::c_int as uint32_t,
            0x385c8000 as core::ffi::c_int as uint32_t,
            0x385cc000 as core::ffi::c_int as uint32_t,
            0x385d0000 as core::ffi::c_int as uint32_t,
            0x385d4000 as core::ffi::c_int as uint32_t,
            0x385d8000 as core::ffi::c_int as uint32_t,
            0x385dc000 as core::ffi::c_int as uint32_t,
            0x385e0000 as core::ffi::c_int as uint32_t,
            0x385e4000 as core::ffi::c_int as uint32_t,
            0x385e8000 as core::ffi::c_int as uint32_t,
            0x385ec000 as core::ffi::c_int as uint32_t,
            0x385f0000 as core::ffi::c_int as uint32_t,
            0x385f4000 as core::ffi::c_int as uint32_t,
            0x385f8000 as core::ffi::c_int as uint32_t,
            0x385fc000 as core::ffi::c_int as uint32_t,
            0x38600000 as core::ffi::c_int as uint32_t,
            0x38604000 as core::ffi::c_int as uint32_t,
            0x38608000 as core::ffi::c_int as uint32_t,
            0x3860c000 as core::ffi::c_int as uint32_t,
            0x38610000 as core::ffi::c_int as uint32_t,
            0x38614000 as core::ffi::c_int as uint32_t,
            0x38618000 as core::ffi::c_int as uint32_t,
            0x3861c000 as core::ffi::c_int as uint32_t,
            0x38620000 as core::ffi::c_int as uint32_t,
            0x38624000 as core::ffi::c_int as uint32_t,
            0x38628000 as core::ffi::c_int as uint32_t,
            0x3862c000 as core::ffi::c_int as uint32_t,
            0x38630000 as core::ffi::c_int as uint32_t,
            0x38634000 as core::ffi::c_int as uint32_t,
            0x38638000 as core::ffi::c_int as uint32_t,
            0x3863c000 as core::ffi::c_int as uint32_t,
            0x38640000 as core::ffi::c_int as uint32_t,
            0x38644000 as core::ffi::c_int as uint32_t,
            0x38648000 as core::ffi::c_int as uint32_t,
            0x3864c000 as core::ffi::c_int as uint32_t,
            0x38650000 as core::ffi::c_int as uint32_t,
            0x38654000 as core::ffi::c_int as uint32_t,
            0x38658000 as core::ffi::c_int as uint32_t,
            0x3865c000 as core::ffi::c_int as uint32_t,
            0x38660000 as core::ffi::c_int as uint32_t,
            0x38664000 as core::ffi::c_int as uint32_t,
            0x38668000 as core::ffi::c_int as uint32_t,
            0x3866c000 as core::ffi::c_int as uint32_t,
            0x38670000 as core::ffi::c_int as uint32_t,
            0x38674000 as core::ffi::c_int as uint32_t,
            0x38678000 as core::ffi::c_int as uint32_t,
            0x3867c000 as core::ffi::c_int as uint32_t,
            0x38680000 as core::ffi::c_int as uint32_t,
            0x38684000 as core::ffi::c_int as uint32_t,
            0x38688000 as core::ffi::c_int as uint32_t,
            0x3868c000 as core::ffi::c_int as uint32_t,
            0x38690000 as core::ffi::c_int as uint32_t,
            0x38694000 as core::ffi::c_int as uint32_t,
            0x38698000 as core::ffi::c_int as uint32_t,
            0x3869c000 as core::ffi::c_int as uint32_t,
            0x386a0000 as core::ffi::c_int as uint32_t,
            0x386a4000 as core::ffi::c_int as uint32_t,
            0x386a8000 as core::ffi::c_int as uint32_t,
            0x386ac000 as core::ffi::c_int as uint32_t,
            0x386b0000 as core::ffi::c_int as uint32_t,
            0x386b4000 as core::ffi::c_int as uint32_t,
            0x386b8000 as core::ffi::c_int as uint32_t,
            0x386bc000 as core::ffi::c_int as uint32_t,
            0x386c0000 as core::ffi::c_int as uint32_t,
            0x386c4000 as core::ffi::c_int as uint32_t,
            0x386c8000 as core::ffi::c_int as uint32_t,
            0x386cc000 as core::ffi::c_int as uint32_t,
            0x386d0000 as core::ffi::c_int as uint32_t,
            0x386d4000 as core::ffi::c_int as uint32_t,
            0x386d8000 as core::ffi::c_int as uint32_t,
            0x386dc000 as core::ffi::c_int as uint32_t,
            0x386e0000 as core::ffi::c_int as uint32_t,
            0x386e4000 as core::ffi::c_int as uint32_t,
            0x386e8000 as core::ffi::c_int as uint32_t,
            0x386ec000 as core::ffi::c_int as uint32_t,
            0x386f0000 as core::ffi::c_int as uint32_t,
            0x386f4000 as core::ffi::c_int as uint32_t,
            0x386f8000 as core::ffi::c_int as uint32_t,
            0x386fc000 as core::ffi::c_int as uint32_t,
            0x38700000 as core::ffi::c_int as uint32_t,
            0x38704000 as core::ffi::c_int as uint32_t,
            0x38708000 as core::ffi::c_int as uint32_t,
            0x3870c000 as core::ffi::c_int as uint32_t,
            0x38710000 as core::ffi::c_int as uint32_t,
            0x38714000 as core::ffi::c_int as uint32_t,
            0x38718000 as core::ffi::c_int as uint32_t,
            0x3871c000 as core::ffi::c_int as uint32_t,
            0x38720000 as core::ffi::c_int as uint32_t,
            0x38724000 as core::ffi::c_int as uint32_t,
            0x38728000 as core::ffi::c_int as uint32_t,
            0x3872c000 as core::ffi::c_int as uint32_t,
            0x38730000 as core::ffi::c_int as uint32_t,
            0x38734000 as core::ffi::c_int as uint32_t,
            0x38738000 as core::ffi::c_int as uint32_t,
            0x3873c000 as core::ffi::c_int as uint32_t,
            0x38740000 as core::ffi::c_int as uint32_t,
            0x38744000 as core::ffi::c_int as uint32_t,
            0x38748000 as core::ffi::c_int as uint32_t,
            0x3874c000 as core::ffi::c_int as uint32_t,
            0x38750000 as core::ffi::c_int as uint32_t,
            0x38754000 as core::ffi::c_int as uint32_t,
            0x38758000 as core::ffi::c_int as uint32_t,
            0x3875c000 as core::ffi::c_int as uint32_t,
            0x38760000 as core::ffi::c_int as uint32_t,
            0x38764000 as core::ffi::c_int as uint32_t,
            0x38768000 as core::ffi::c_int as uint32_t,
            0x3876c000 as core::ffi::c_int as uint32_t,
            0x38770000 as core::ffi::c_int as uint32_t,
            0x38774000 as core::ffi::c_int as uint32_t,
            0x38778000 as core::ffi::c_int as uint32_t,
            0x3877c000 as core::ffi::c_int as uint32_t,
            0x38780000 as core::ffi::c_int as uint32_t,
            0x38784000 as core::ffi::c_int as uint32_t,
            0x38788000 as core::ffi::c_int as uint32_t,
            0x3878c000 as core::ffi::c_int as uint32_t,
            0x38790000 as core::ffi::c_int as uint32_t,
            0x38794000 as core::ffi::c_int as uint32_t,
            0x38798000 as core::ffi::c_int as uint32_t,
            0x3879c000 as core::ffi::c_int as uint32_t,
            0x387a0000 as core::ffi::c_int as uint32_t,
            0x387a4000 as core::ffi::c_int as uint32_t,
            0x387a8000 as core::ffi::c_int as uint32_t,
            0x387ac000 as core::ffi::c_int as uint32_t,
            0x387b0000 as core::ffi::c_int as uint32_t,
            0x387b4000 as core::ffi::c_int as uint32_t,
            0x387b8000 as core::ffi::c_int as uint32_t,
            0x387bc000 as core::ffi::c_int as uint32_t,
            0x387c0000 as core::ffi::c_int as uint32_t,
            0x387c4000 as core::ffi::c_int as uint32_t,
            0x387c8000 as core::ffi::c_int as uint32_t,
            0x387cc000 as core::ffi::c_int as uint32_t,
            0x387d0000 as core::ffi::c_int as uint32_t,
            0x387d4000 as core::ffi::c_int as uint32_t,
            0x387d8000 as core::ffi::c_int as uint32_t,
            0x387dc000 as core::ffi::c_int as uint32_t,
            0x387e0000 as core::ffi::c_int as uint32_t,
            0x387e4000 as core::ffi::c_int as uint32_t,
            0x387e8000 as core::ffi::c_int as uint32_t,
            0x387ec000 as core::ffi::c_int as uint32_t,
            0x387f0000 as core::ffi::c_int as uint32_t,
            0x387f4000 as core::ffi::c_int as uint32_t,
            0x387f8000 as core::ffi::c_int as uint32_t,
            0x387fc000 as core::ffi::c_int as uint32_t,
            0x38000000 as core::ffi::c_int as uint32_t,
            0x38002000 as core::ffi::c_int as uint32_t,
            0x38004000 as core::ffi::c_int as uint32_t,
            0x38006000 as core::ffi::c_int as uint32_t,
            0x38008000 as core::ffi::c_int as uint32_t,
            0x3800a000 as core::ffi::c_int as uint32_t,
            0x3800c000 as core::ffi::c_int as uint32_t,
            0x3800e000 as core::ffi::c_int as uint32_t,
            0x38010000 as core::ffi::c_int as uint32_t,
            0x38012000 as core::ffi::c_int as uint32_t,
            0x38014000 as core::ffi::c_int as uint32_t,
            0x38016000 as core::ffi::c_int as uint32_t,
            0x38018000 as core::ffi::c_int as uint32_t,
            0x3801a000 as core::ffi::c_int as uint32_t,
            0x3801c000 as core::ffi::c_int as uint32_t,
            0x3801e000 as core::ffi::c_int as uint32_t,
            0x38020000 as core::ffi::c_int as uint32_t,
            0x38022000 as core::ffi::c_int as uint32_t,
            0x38024000 as core::ffi::c_int as uint32_t,
            0x38026000 as core::ffi::c_int as uint32_t,
            0x38028000 as core::ffi::c_int as uint32_t,
            0x3802a000 as core::ffi::c_int as uint32_t,
            0x3802c000 as core::ffi::c_int as uint32_t,
            0x3802e000 as core::ffi::c_int as uint32_t,
            0x38030000 as core::ffi::c_int as uint32_t,
            0x38032000 as core::ffi::c_int as uint32_t,
            0x38034000 as core::ffi::c_int as uint32_t,
            0x38036000 as core::ffi::c_int as uint32_t,
            0x38038000 as core::ffi::c_int as uint32_t,
            0x3803a000 as core::ffi::c_int as uint32_t,
            0x3803c000 as core::ffi::c_int as uint32_t,
            0x3803e000 as core::ffi::c_int as uint32_t,
            0x38040000 as core::ffi::c_int as uint32_t,
            0x38042000 as core::ffi::c_int as uint32_t,
            0x38044000 as core::ffi::c_int as uint32_t,
            0x38046000 as core::ffi::c_int as uint32_t,
            0x38048000 as core::ffi::c_int as uint32_t,
            0x3804a000 as core::ffi::c_int as uint32_t,
            0x3804c000 as core::ffi::c_int as uint32_t,
            0x3804e000 as core::ffi::c_int as uint32_t,
            0x38050000 as core::ffi::c_int as uint32_t,
            0x38052000 as core::ffi::c_int as uint32_t,
            0x38054000 as core::ffi::c_int as uint32_t,
            0x38056000 as core::ffi::c_int as uint32_t,
            0x38058000 as core::ffi::c_int as uint32_t,
            0x3805a000 as core::ffi::c_int as uint32_t,
            0x3805c000 as core::ffi::c_int as uint32_t,
            0x3805e000 as core::ffi::c_int as uint32_t,
            0x38060000 as core::ffi::c_int as uint32_t,
            0x38062000 as core::ffi::c_int as uint32_t,
            0x38064000 as core::ffi::c_int as uint32_t,
            0x38066000 as core::ffi::c_int as uint32_t,
            0x38068000 as core::ffi::c_int as uint32_t,
            0x3806a000 as core::ffi::c_int as uint32_t,
            0x3806c000 as core::ffi::c_int as uint32_t,
            0x3806e000 as core::ffi::c_int as uint32_t,
            0x38070000 as core::ffi::c_int as uint32_t,
            0x38072000 as core::ffi::c_int as uint32_t,
            0x38074000 as core::ffi::c_int as uint32_t,
            0x38076000 as core::ffi::c_int as uint32_t,
            0x38078000 as core::ffi::c_int as uint32_t,
            0x3807a000 as core::ffi::c_int as uint32_t,
            0x3807c000 as core::ffi::c_int as uint32_t,
            0x3807e000 as core::ffi::c_int as uint32_t,
            0x38080000 as core::ffi::c_int as uint32_t,
            0x38082000 as core::ffi::c_int as uint32_t,
            0x38084000 as core::ffi::c_int as uint32_t,
            0x38086000 as core::ffi::c_int as uint32_t,
            0x38088000 as core::ffi::c_int as uint32_t,
            0x3808a000 as core::ffi::c_int as uint32_t,
            0x3808c000 as core::ffi::c_int as uint32_t,
            0x3808e000 as core::ffi::c_int as uint32_t,
            0x38090000 as core::ffi::c_int as uint32_t,
            0x38092000 as core::ffi::c_int as uint32_t,
            0x38094000 as core::ffi::c_int as uint32_t,
            0x38096000 as core::ffi::c_int as uint32_t,
            0x38098000 as core::ffi::c_int as uint32_t,
            0x3809a000 as core::ffi::c_int as uint32_t,
            0x3809c000 as core::ffi::c_int as uint32_t,
            0x3809e000 as core::ffi::c_int as uint32_t,
            0x380a0000 as core::ffi::c_int as uint32_t,
            0x380a2000 as core::ffi::c_int as uint32_t,
            0x380a4000 as core::ffi::c_int as uint32_t,
            0x380a6000 as core::ffi::c_int as uint32_t,
            0x380a8000 as core::ffi::c_int as uint32_t,
            0x380aa000 as core::ffi::c_int as uint32_t,
            0x380ac000 as core::ffi::c_int as uint32_t,
            0x380ae000 as core::ffi::c_int as uint32_t,
            0x380b0000 as core::ffi::c_int as uint32_t,
            0x380b2000 as core::ffi::c_int as uint32_t,
            0x380b4000 as core::ffi::c_int as uint32_t,
            0x380b6000 as core::ffi::c_int as uint32_t,
            0x380b8000 as core::ffi::c_int as uint32_t,
            0x380ba000 as core::ffi::c_int as uint32_t,
            0x380bc000 as core::ffi::c_int as uint32_t,
            0x380be000 as core::ffi::c_int as uint32_t,
            0x380c0000 as core::ffi::c_int as uint32_t,
            0x380c2000 as core::ffi::c_int as uint32_t,
            0x380c4000 as core::ffi::c_int as uint32_t,
            0x380c6000 as core::ffi::c_int as uint32_t,
            0x380c8000 as core::ffi::c_int as uint32_t,
            0x380ca000 as core::ffi::c_int as uint32_t,
            0x380cc000 as core::ffi::c_int as uint32_t,
            0x380ce000 as core::ffi::c_int as uint32_t,
            0x380d0000 as core::ffi::c_int as uint32_t,
            0x380d2000 as core::ffi::c_int as uint32_t,
            0x380d4000 as core::ffi::c_int as uint32_t,
            0x380d6000 as core::ffi::c_int as uint32_t,
            0x380d8000 as core::ffi::c_int as uint32_t,
            0x380da000 as core::ffi::c_int as uint32_t,
            0x380dc000 as core::ffi::c_int as uint32_t,
            0x380de000 as core::ffi::c_int as uint32_t,
            0x380e0000 as core::ffi::c_int as uint32_t,
            0x380e2000 as core::ffi::c_int as uint32_t,
            0x380e4000 as core::ffi::c_int as uint32_t,
            0x380e6000 as core::ffi::c_int as uint32_t,
            0x380e8000 as core::ffi::c_int as uint32_t,
            0x380ea000 as core::ffi::c_int as uint32_t,
            0x380ec000 as core::ffi::c_int as uint32_t,
            0x380ee000 as core::ffi::c_int as uint32_t,
            0x380f0000 as core::ffi::c_int as uint32_t,
            0x380f2000 as core::ffi::c_int as uint32_t,
            0x380f4000 as core::ffi::c_int as uint32_t,
            0x380f6000 as core::ffi::c_int as uint32_t,
            0x380f8000 as core::ffi::c_int as uint32_t,
            0x380fa000 as core::ffi::c_int as uint32_t,
            0x380fc000 as core::ffi::c_int as uint32_t,
            0x380fe000 as core::ffi::c_int as uint32_t,
            0x38100000 as core::ffi::c_int as uint32_t,
            0x38102000 as core::ffi::c_int as uint32_t,
            0x38104000 as core::ffi::c_int as uint32_t,
            0x38106000 as core::ffi::c_int as uint32_t,
            0x38108000 as core::ffi::c_int as uint32_t,
            0x3810a000 as core::ffi::c_int as uint32_t,
            0x3810c000 as core::ffi::c_int as uint32_t,
            0x3810e000 as core::ffi::c_int as uint32_t,
            0x38110000 as core::ffi::c_int as uint32_t,
            0x38112000 as core::ffi::c_int as uint32_t,
            0x38114000 as core::ffi::c_int as uint32_t,
            0x38116000 as core::ffi::c_int as uint32_t,
            0x38118000 as core::ffi::c_int as uint32_t,
            0x3811a000 as core::ffi::c_int as uint32_t,
            0x3811c000 as core::ffi::c_int as uint32_t,
            0x3811e000 as core::ffi::c_int as uint32_t,
            0x38120000 as core::ffi::c_int as uint32_t,
            0x38122000 as core::ffi::c_int as uint32_t,
            0x38124000 as core::ffi::c_int as uint32_t,
            0x38126000 as core::ffi::c_int as uint32_t,
            0x38128000 as core::ffi::c_int as uint32_t,
            0x3812a000 as core::ffi::c_int as uint32_t,
            0x3812c000 as core::ffi::c_int as uint32_t,
            0x3812e000 as core::ffi::c_int as uint32_t,
            0x38130000 as core::ffi::c_int as uint32_t,
            0x38132000 as core::ffi::c_int as uint32_t,
            0x38134000 as core::ffi::c_int as uint32_t,
            0x38136000 as core::ffi::c_int as uint32_t,
            0x38138000 as core::ffi::c_int as uint32_t,
            0x3813a000 as core::ffi::c_int as uint32_t,
            0x3813c000 as core::ffi::c_int as uint32_t,
            0x3813e000 as core::ffi::c_int as uint32_t,
            0x38140000 as core::ffi::c_int as uint32_t,
            0x38142000 as core::ffi::c_int as uint32_t,
            0x38144000 as core::ffi::c_int as uint32_t,
            0x38146000 as core::ffi::c_int as uint32_t,
            0x38148000 as core::ffi::c_int as uint32_t,
            0x3814a000 as core::ffi::c_int as uint32_t,
            0x3814c000 as core::ffi::c_int as uint32_t,
            0x3814e000 as core::ffi::c_int as uint32_t,
            0x38150000 as core::ffi::c_int as uint32_t,
            0x38152000 as core::ffi::c_int as uint32_t,
            0x38154000 as core::ffi::c_int as uint32_t,
            0x38156000 as core::ffi::c_int as uint32_t,
            0x38158000 as core::ffi::c_int as uint32_t,
            0x3815a000 as core::ffi::c_int as uint32_t,
            0x3815c000 as core::ffi::c_int as uint32_t,
            0x3815e000 as core::ffi::c_int as uint32_t,
            0x38160000 as core::ffi::c_int as uint32_t,
            0x38162000 as core::ffi::c_int as uint32_t,
            0x38164000 as core::ffi::c_int as uint32_t,
            0x38166000 as core::ffi::c_int as uint32_t,
            0x38168000 as core::ffi::c_int as uint32_t,
            0x3816a000 as core::ffi::c_int as uint32_t,
            0x3816c000 as core::ffi::c_int as uint32_t,
            0x3816e000 as core::ffi::c_int as uint32_t,
            0x38170000 as core::ffi::c_int as uint32_t,
            0x38172000 as core::ffi::c_int as uint32_t,
            0x38174000 as core::ffi::c_int as uint32_t,
            0x38176000 as core::ffi::c_int as uint32_t,
            0x38178000 as core::ffi::c_int as uint32_t,
            0x3817a000 as core::ffi::c_int as uint32_t,
            0x3817c000 as core::ffi::c_int as uint32_t,
            0x3817e000 as core::ffi::c_int as uint32_t,
            0x38180000 as core::ffi::c_int as uint32_t,
            0x38182000 as core::ffi::c_int as uint32_t,
            0x38184000 as core::ffi::c_int as uint32_t,
            0x38186000 as core::ffi::c_int as uint32_t,
            0x38188000 as core::ffi::c_int as uint32_t,
            0x3818a000 as core::ffi::c_int as uint32_t,
            0x3818c000 as core::ffi::c_int as uint32_t,
            0x3818e000 as core::ffi::c_int as uint32_t,
            0x38190000 as core::ffi::c_int as uint32_t,
            0x38192000 as core::ffi::c_int as uint32_t,
            0x38194000 as core::ffi::c_int as uint32_t,
            0x38196000 as core::ffi::c_int as uint32_t,
            0x38198000 as core::ffi::c_int as uint32_t,
            0x3819a000 as core::ffi::c_int as uint32_t,
            0x3819c000 as core::ffi::c_int as uint32_t,
            0x3819e000 as core::ffi::c_int as uint32_t,
            0x381a0000 as core::ffi::c_int as uint32_t,
            0x381a2000 as core::ffi::c_int as uint32_t,
            0x381a4000 as core::ffi::c_int as uint32_t,
            0x381a6000 as core::ffi::c_int as uint32_t,
            0x381a8000 as core::ffi::c_int as uint32_t,
            0x381aa000 as core::ffi::c_int as uint32_t,
            0x381ac000 as core::ffi::c_int as uint32_t,
            0x381ae000 as core::ffi::c_int as uint32_t,
            0x381b0000 as core::ffi::c_int as uint32_t,
            0x381b2000 as core::ffi::c_int as uint32_t,
            0x381b4000 as core::ffi::c_int as uint32_t,
            0x381b6000 as core::ffi::c_int as uint32_t,
            0x381b8000 as core::ffi::c_int as uint32_t,
            0x381ba000 as core::ffi::c_int as uint32_t,
            0x381bc000 as core::ffi::c_int as uint32_t,
            0x381be000 as core::ffi::c_int as uint32_t,
            0x381c0000 as core::ffi::c_int as uint32_t,
            0x381c2000 as core::ffi::c_int as uint32_t,
            0x381c4000 as core::ffi::c_int as uint32_t,
            0x381c6000 as core::ffi::c_int as uint32_t,
            0x381c8000 as core::ffi::c_int as uint32_t,
            0x381ca000 as core::ffi::c_int as uint32_t,
            0x381cc000 as core::ffi::c_int as uint32_t,
            0x381ce000 as core::ffi::c_int as uint32_t,
            0x381d0000 as core::ffi::c_int as uint32_t,
            0x381d2000 as core::ffi::c_int as uint32_t,
            0x381d4000 as core::ffi::c_int as uint32_t,
            0x381d6000 as core::ffi::c_int as uint32_t,
            0x381d8000 as core::ffi::c_int as uint32_t,
            0x381da000 as core::ffi::c_int as uint32_t,
            0x381dc000 as core::ffi::c_int as uint32_t,
            0x381de000 as core::ffi::c_int as uint32_t,
            0x381e0000 as core::ffi::c_int as uint32_t,
            0x381e2000 as core::ffi::c_int as uint32_t,
            0x381e4000 as core::ffi::c_int as uint32_t,
            0x381e6000 as core::ffi::c_int as uint32_t,
            0x381e8000 as core::ffi::c_int as uint32_t,
            0x381ea000 as core::ffi::c_int as uint32_t,
            0x381ec000 as core::ffi::c_int as uint32_t,
            0x381ee000 as core::ffi::c_int as uint32_t,
            0x381f0000 as core::ffi::c_int as uint32_t,
            0x381f2000 as core::ffi::c_int as uint32_t,
            0x381f4000 as core::ffi::c_int as uint32_t,
            0x381f6000 as core::ffi::c_int as uint32_t,
            0x381f8000 as core::ffi::c_int as uint32_t,
            0x381fa000 as core::ffi::c_int as uint32_t,
            0x381fc000 as core::ffi::c_int as uint32_t,
            0x381fe000 as core::ffi::c_int as uint32_t,
            0x38200000 as core::ffi::c_int as uint32_t,
            0x38202000 as core::ffi::c_int as uint32_t,
            0x38204000 as core::ffi::c_int as uint32_t,
            0x38206000 as core::ffi::c_int as uint32_t,
            0x38208000 as core::ffi::c_int as uint32_t,
            0x3820a000 as core::ffi::c_int as uint32_t,
            0x3820c000 as core::ffi::c_int as uint32_t,
            0x3820e000 as core::ffi::c_int as uint32_t,
            0x38210000 as core::ffi::c_int as uint32_t,
            0x38212000 as core::ffi::c_int as uint32_t,
            0x38214000 as core::ffi::c_int as uint32_t,
            0x38216000 as core::ffi::c_int as uint32_t,
            0x38218000 as core::ffi::c_int as uint32_t,
            0x3821a000 as core::ffi::c_int as uint32_t,
            0x3821c000 as core::ffi::c_int as uint32_t,
            0x3821e000 as core::ffi::c_int as uint32_t,
            0x38220000 as core::ffi::c_int as uint32_t,
            0x38222000 as core::ffi::c_int as uint32_t,
            0x38224000 as core::ffi::c_int as uint32_t,
            0x38226000 as core::ffi::c_int as uint32_t,
            0x38228000 as core::ffi::c_int as uint32_t,
            0x3822a000 as core::ffi::c_int as uint32_t,
            0x3822c000 as core::ffi::c_int as uint32_t,
            0x3822e000 as core::ffi::c_int as uint32_t,
            0x38230000 as core::ffi::c_int as uint32_t,
            0x38232000 as core::ffi::c_int as uint32_t,
            0x38234000 as core::ffi::c_int as uint32_t,
            0x38236000 as core::ffi::c_int as uint32_t,
            0x38238000 as core::ffi::c_int as uint32_t,
            0x3823a000 as core::ffi::c_int as uint32_t,
            0x3823c000 as core::ffi::c_int as uint32_t,
            0x3823e000 as core::ffi::c_int as uint32_t,
            0x38240000 as core::ffi::c_int as uint32_t,
            0x38242000 as core::ffi::c_int as uint32_t,
            0x38244000 as core::ffi::c_int as uint32_t,
            0x38246000 as core::ffi::c_int as uint32_t,
            0x38248000 as core::ffi::c_int as uint32_t,
            0x3824a000 as core::ffi::c_int as uint32_t,
            0x3824c000 as core::ffi::c_int as uint32_t,
            0x3824e000 as core::ffi::c_int as uint32_t,
            0x38250000 as core::ffi::c_int as uint32_t,
            0x38252000 as core::ffi::c_int as uint32_t,
            0x38254000 as core::ffi::c_int as uint32_t,
            0x38256000 as core::ffi::c_int as uint32_t,
            0x38258000 as core::ffi::c_int as uint32_t,
            0x3825a000 as core::ffi::c_int as uint32_t,
            0x3825c000 as core::ffi::c_int as uint32_t,
            0x3825e000 as core::ffi::c_int as uint32_t,
            0x38260000 as core::ffi::c_int as uint32_t,
            0x38262000 as core::ffi::c_int as uint32_t,
            0x38264000 as core::ffi::c_int as uint32_t,
            0x38266000 as core::ffi::c_int as uint32_t,
            0x38268000 as core::ffi::c_int as uint32_t,
            0x3826a000 as core::ffi::c_int as uint32_t,
            0x3826c000 as core::ffi::c_int as uint32_t,
            0x3826e000 as core::ffi::c_int as uint32_t,
            0x38270000 as core::ffi::c_int as uint32_t,
            0x38272000 as core::ffi::c_int as uint32_t,
            0x38274000 as core::ffi::c_int as uint32_t,
            0x38276000 as core::ffi::c_int as uint32_t,
            0x38278000 as core::ffi::c_int as uint32_t,
            0x3827a000 as core::ffi::c_int as uint32_t,
            0x3827c000 as core::ffi::c_int as uint32_t,
            0x3827e000 as core::ffi::c_int as uint32_t,
            0x38280000 as core::ffi::c_int as uint32_t,
            0x38282000 as core::ffi::c_int as uint32_t,
            0x38284000 as core::ffi::c_int as uint32_t,
            0x38286000 as core::ffi::c_int as uint32_t,
            0x38288000 as core::ffi::c_int as uint32_t,
            0x3828a000 as core::ffi::c_int as uint32_t,
            0x3828c000 as core::ffi::c_int as uint32_t,
            0x3828e000 as core::ffi::c_int as uint32_t,
            0x38290000 as core::ffi::c_int as uint32_t,
            0x38292000 as core::ffi::c_int as uint32_t,
            0x38294000 as core::ffi::c_int as uint32_t,
            0x38296000 as core::ffi::c_int as uint32_t,
            0x38298000 as core::ffi::c_int as uint32_t,
            0x3829a000 as core::ffi::c_int as uint32_t,
            0x3829c000 as core::ffi::c_int as uint32_t,
            0x3829e000 as core::ffi::c_int as uint32_t,
            0x382a0000 as core::ffi::c_int as uint32_t,
            0x382a2000 as core::ffi::c_int as uint32_t,
            0x382a4000 as core::ffi::c_int as uint32_t,
            0x382a6000 as core::ffi::c_int as uint32_t,
            0x382a8000 as core::ffi::c_int as uint32_t,
            0x382aa000 as core::ffi::c_int as uint32_t,
            0x382ac000 as core::ffi::c_int as uint32_t,
            0x382ae000 as core::ffi::c_int as uint32_t,
            0x382b0000 as core::ffi::c_int as uint32_t,
            0x382b2000 as core::ffi::c_int as uint32_t,
            0x382b4000 as core::ffi::c_int as uint32_t,
            0x382b6000 as core::ffi::c_int as uint32_t,
            0x382b8000 as core::ffi::c_int as uint32_t,
            0x382ba000 as core::ffi::c_int as uint32_t,
            0x382bc000 as core::ffi::c_int as uint32_t,
            0x382be000 as core::ffi::c_int as uint32_t,
            0x382c0000 as core::ffi::c_int as uint32_t,
            0x382c2000 as core::ffi::c_int as uint32_t,
            0x382c4000 as core::ffi::c_int as uint32_t,
            0x382c6000 as core::ffi::c_int as uint32_t,
            0x382c8000 as core::ffi::c_int as uint32_t,
            0x382ca000 as core::ffi::c_int as uint32_t,
            0x382cc000 as core::ffi::c_int as uint32_t,
            0x382ce000 as core::ffi::c_int as uint32_t,
            0x382d0000 as core::ffi::c_int as uint32_t,
            0x382d2000 as core::ffi::c_int as uint32_t,
            0x382d4000 as core::ffi::c_int as uint32_t,
            0x382d6000 as core::ffi::c_int as uint32_t,
            0x382d8000 as core::ffi::c_int as uint32_t,
            0x382da000 as core::ffi::c_int as uint32_t,
            0x382dc000 as core::ffi::c_int as uint32_t,
            0x382de000 as core::ffi::c_int as uint32_t,
            0x382e0000 as core::ffi::c_int as uint32_t,
            0x382e2000 as core::ffi::c_int as uint32_t,
            0x382e4000 as core::ffi::c_int as uint32_t,
            0x382e6000 as core::ffi::c_int as uint32_t,
            0x382e8000 as core::ffi::c_int as uint32_t,
            0x382ea000 as core::ffi::c_int as uint32_t,
            0x382ec000 as core::ffi::c_int as uint32_t,
            0x382ee000 as core::ffi::c_int as uint32_t,
            0x382f0000 as core::ffi::c_int as uint32_t,
            0x382f2000 as core::ffi::c_int as uint32_t,
            0x382f4000 as core::ffi::c_int as uint32_t,
            0x382f6000 as core::ffi::c_int as uint32_t,
            0x382f8000 as core::ffi::c_int as uint32_t,
            0x382fa000 as core::ffi::c_int as uint32_t,
            0x382fc000 as core::ffi::c_int as uint32_t,
            0x382fe000 as core::ffi::c_int as uint32_t,
            0x38300000 as core::ffi::c_int as uint32_t,
            0x38302000 as core::ffi::c_int as uint32_t,
            0x38304000 as core::ffi::c_int as uint32_t,
            0x38306000 as core::ffi::c_int as uint32_t,
            0x38308000 as core::ffi::c_int as uint32_t,
            0x3830a000 as core::ffi::c_int as uint32_t,
            0x3830c000 as core::ffi::c_int as uint32_t,
            0x3830e000 as core::ffi::c_int as uint32_t,
            0x38310000 as core::ffi::c_int as uint32_t,
            0x38312000 as core::ffi::c_int as uint32_t,
            0x38314000 as core::ffi::c_int as uint32_t,
            0x38316000 as core::ffi::c_int as uint32_t,
            0x38318000 as core::ffi::c_int as uint32_t,
            0x3831a000 as core::ffi::c_int as uint32_t,
            0x3831c000 as core::ffi::c_int as uint32_t,
            0x3831e000 as core::ffi::c_int as uint32_t,
            0x38320000 as core::ffi::c_int as uint32_t,
            0x38322000 as core::ffi::c_int as uint32_t,
            0x38324000 as core::ffi::c_int as uint32_t,
            0x38326000 as core::ffi::c_int as uint32_t,
            0x38328000 as core::ffi::c_int as uint32_t,
            0x3832a000 as core::ffi::c_int as uint32_t,
            0x3832c000 as core::ffi::c_int as uint32_t,
            0x3832e000 as core::ffi::c_int as uint32_t,
            0x38330000 as core::ffi::c_int as uint32_t,
            0x38332000 as core::ffi::c_int as uint32_t,
            0x38334000 as core::ffi::c_int as uint32_t,
            0x38336000 as core::ffi::c_int as uint32_t,
            0x38338000 as core::ffi::c_int as uint32_t,
            0x3833a000 as core::ffi::c_int as uint32_t,
            0x3833c000 as core::ffi::c_int as uint32_t,
            0x3833e000 as core::ffi::c_int as uint32_t,
            0x38340000 as core::ffi::c_int as uint32_t,
            0x38342000 as core::ffi::c_int as uint32_t,
            0x38344000 as core::ffi::c_int as uint32_t,
            0x38346000 as core::ffi::c_int as uint32_t,
            0x38348000 as core::ffi::c_int as uint32_t,
            0x3834a000 as core::ffi::c_int as uint32_t,
            0x3834c000 as core::ffi::c_int as uint32_t,
            0x3834e000 as core::ffi::c_int as uint32_t,
            0x38350000 as core::ffi::c_int as uint32_t,
            0x38352000 as core::ffi::c_int as uint32_t,
            0x38354000 as core::ffi::c_int as uint32_t,
            0x38356000 as core::ffi::c_int as uint32_t,
            0x38358000 as core::ffi::c_int as uint32_t,
            0x3835a000 as core::ffi::c_int as uint32_t,
            0x3835c000 as core::ffi::c_int as uint32_t,
            0x3835e000 as core::ffi::c_int as uint32_t,
            0x38360000 as core::ffi::c_int as uint32_t,
            0x38362000 as core::ffi::c_int as uint32_t,
            0x38364000 as core::ffi::c_int as uint32_t,
            0x38366000 as core::ffi::c_int as uint32_t,
            0x38368000 as core::ffi::c_int as uint32_t,
            0x3836a000 as core::ffi::c_int as uint32_t,
            0x3836c000 as core::ffi::c_int as uint32_t,
            0x3836e000 as core::ffi::c_int as uint32_t,
            0x38370000 as core::ffi::c_int as uint32_t,
            0x38372000 as core::ffi::c_int as uint32_t,
            0x38374000 as core::ffi::c_int as uint32_t,
            0x38376000 as core::ffi::c_int as uint32_t,
            0x38378000 as core::ffi::c_int as uint32_t,
            0x3837a000 as core::ffi::c_int as uint32_t,
            0x3837c000 as core::ffi::c_int as uint32_t,
            0x3837e000 as core::ffi::c_int as uint32_t,
            0x38380000 as core::ffi::c_int as uint32_t,
            0x38382000 as core::ffi::c_int as uint32_t,
            0x38384000 as core::ffi::c_int as uint32_t,
            0x38386000 as core::ffi::c_int as uint32_t,
            0x38388000 as core::ffi::c_int as uint32_t,
            0x3838a000 as core::ffi::c_int as uint32_t,
            0x3838c000 as core::ffi::c_int as uint32_t,
            0x3838e000 as core::ffi::c_int as uint32_t,
            0x38390000 as core::ffi::c_int as uint32_t,
            0x38392000 as core::ffi::c_int as uint32_t,
            0x38394000 as core::ffi::c_int as uint32_t,
            0x38396000 as core::ffi::c_int as uint32_t,
            0x38398000 as core::ffi::c_int as uint32_t,
            0x3839a000 as core::ffi::c_int as uint32_t,
            0x3839c000 as core::ffi::c_int as uint32_t,
            0x3839e000 as core::ffi::c_int as uint32_t,
            0x383a0000 as core::ffi::c_int as uint32_t,
            0x383a2000 as core::ffi::c_int as uint32_t,
            0x383a4000 as core::ffi::c_int as uint32_t,
            0x383a6000 as core::ffi::c_int as uint32_t,
            0x383a8000 as core::ffi::c_int as uint32_t,
            0x383aa000 as core::ffi::c_int as uint32_t,
            0x383ac000 as core::ffi::c_int as uint32_t,
            0x383ae000 as core::ffi::c_int as uint32_t,
            0x383b0000 as core::ffi::c_int as uint32_t,
            0x383b2000 as core::ffi::c_int as uint32_t,
            0x383b4000 as core::ffi::c_int as uint32_t,
            0x383b6000 as core::ffi::c_int as uint32_t,
            0x383b8000 as core::ffi::c_int as uint32_t,
            0x383ba000 as core::ffi::c_int as uint32_t,
            0x383bc000 as core::ffi::c_int as uint32_t,
            0x383be000 as core::ffi::c_int as uint32_t,
            0x383c0000 as core::ffi::c_int as uint32_t,
            0x383c2000 as core::ffi::c_int as uint32_t,
            0x383c4000 as core::ffi::c_int as uint32_t,
            0x383c6000 as core::ffi::c_int as uint32_t,
            0x383c8000 as core::ffi::c_int as uint32_t,
            0x383ca000 as core::ffi::c_int as uint32_t,
            0x383cc000 as core::ffi::c_int as uint32_t,
            0x383ce000 as core::ffi::c_int as uint32_t,
            0x383d0000 as core::ffi::c_int as uint32_t,
            0x383d2000 as core::ffi::c_int as uint32_t,
            0x383d4000 as core::ffi::c_int as uint32_t,
            0x383d6000 as core::ffi::c_int as uint32_t,
            0x383d8000 as core::ffi::c_int as uint32_t,
            0x383da000 as core::ffi::c_int as uint32_t,
            0x383dc000 as core::ffi::c_int as uint32_t,
            0x383de000 as core::ffi::c_int as uint32_t,
            0x383e0000 as core::ffi::c_int as uint32_t,
            0x383e2000 as core::ffi::c_int as uint32_t,
            0x383e4000 as core::ffi::c_int as uint32_t,
            0x383e6000 as core::ffi::c_int as uint32_t,
            0x383e8000 as core::ffi::c_int as uint32_t,
            0x383ea000 as core::ffi::c_int as uint32_t,
            0x383ec000 as core::ffi::c_int as uint32_t,
            0x383ee000 as core::ffi::c_int as uint32_t,
            0x383f0000 as core::ffi::c_int as uint32_t,
            0x383f2000 as core::ffi::c_int as uint32_t,
            0x383f4000 as core::ffi::c_int as uint32_t,
            0x383f6000 as core::ffi::c_int as uint32_t,
            0x383f8000 as core::ffi::c_int as uint32_t,
            0x383fa000 as core::ffi::c_int as uint32_t,
            0x383fc000 as core::ffi::c_int as uint32_t,
            0x383fe000 as core::ffi::c_int as uint32_t,
            0x38400000 as core::ffi::c_int as uint32_t,
            0x38402000 as core::ffi::c_int as uint32_t,
            0x38404000 as core::ffi::c_int as uint32_t,
            0x38406000 as core::ffi::c_int as uint32_t,
            0x38408000 as core::ffi::c_int as uint32_t,
            0x3840a000 as core::ffi::c_int as uint32_t,
            0x3840c000 as core::ffi::c_int as uint32_t,
            0x3840e000 as core::ffi::c_int as uint32_t,
            0x38410000 as core::ffi::c_int as uint32_t,
            0x38412000 as core::ffi::c_int as uint32_t,
            0x38414000 as core::ffi::c_int as uint32_t,
            0x38416000 as core::ffi::c_int as uint32_t,
            0x38418000 as core::ffi::c_int as uint32_t,
            0x3841a000 as core::ffi::c_int as uint32_t,
            0x3841c000 as core::ffi::c_int as uint32_t,
            0x3841e000 as core::ffi::c_int as uint32_t,
            0x38420000 as core::ffi::c_int as uint32_t,
            0x38422000 as core::ffi::c_int as uint32_t,
            0x38424000 as core::ffi::c_int as uint32_t,
            0x38426000 as core::ffi::c_int as uint32_t,
            0x38428000 as core::ffi::c_int as uint32_t,
            0x3842a000 as core::ffi::c_int as uint32_t,
            0x3842c000 as core::ffi::c_int as uint32_t,
            0x3842e000 as core::ffi::c_int as uint32_t,
            0x38430000 as core::ffi::c_int as uint32_t,
            0x38432000 as core::ffi::c_int as uint32_t,
            0x38434000 as core::ffi::c_int as uint32_t,
            0x38436000 as core::ffi::c_int as uint32_t,
            0x38438000 as core::ffi::c_int as uint32_t,
            0x3843a000 as core::ffi::c_int as uint32_t,
            0x3843c000 as core::ffi::c_int as uint32_t,
            0x3843e000 as core::ffi::c_int as uint32_t,
            0x38440000 as core::ffi::c_int as uint32_t,
            0x38442000 as core::ffi::c_int as uint32_t,
            0x38444000 as core::ffi::c_int as uint32_t,
            0x38446000 as core::ffi::c_int as uint32_t,
            0x38448000 as core::ffi::c_int as uint32_t,
            0x3844a000 as core::ffi::c_int as uint32_t,
            0x3844c000 as core::ffi::c_int as uint32_t,
            0x3844e000 as core::ffi::c_int as uint32_t,
            0x38450000 as core::ffi::c_int as uint32_t,
            0x38452000 as core::ffi::c_int as uint32_t,
            0x38454000 as core::ffi::c_int as uint32_t,
            0x38456000 as core::ffi::c_int as uint32_t,
            0x38458000 as core::ffi::c_int as uint32_t,
            0x3845a000 as core::ffi::c_int as uint32_t,
            0x3845c000 as core::ffi::c_int as uint32_t,
            0x3845e000 as core::ffi::c_int as uint32_t,
            0x38460000 as core::ffi::c_int as uint32_t,
            0x38462000 as core::ffi::c_int as uint32_t,
            0x38464000 as core::ffi::c_int as uint32_t,
            0x38466000 as core::ffi::c_int as uint32_t,
            0x38468000 as core::ffi::c_int as uint32_t,
            0x3846a000 as core::ffi::c_int as uint32_t,
            0x3846c000 as core::ffi::c_int as uint32_t,
            0x3846e000 as core::ffi::c_int as uint32_t,
            0x38470000 as core::ffi::c_int as uint32_t,
            0x38472000 as core::ffi::c_int as uint32_t,
            0x38474000 as core::ffi::c_int as uint32_t,
            0x38476000 as core::ffi::c_int as uint32_t,
            0x38478000 as core::ffi::c_int as uint32_t,
            0x3847a000 as core::ffi::c_int as uint32_t,
            0x3847c000 as core::ffi::c_int as uint32_t,
            0x3847e000 as core::ffi::c_int as uint32_t,
            0x38480000 as core::ffi::c_int as uint32_t,
            0x38482000 as core::ffi::c_int as uint32_t,
            0x38484000 as core::ffi::c_int as uint32_t,
            0x38486000 as core::ffi::c_int as uint32_t,
            0x38488000 as core::ffi::c_int as uint32_t,
            0x3848a000 as core::ffi::c_int as uint32_t,
            0x3848c000 as core::ffi::c_int as uint32_t,
            0x3848e000 as core::ffi::c_int as uint32_t,
            0x38490000 as core::ffi::c_int as uint32_t,
            0x38492000 as core::ffi::c_int as uint32_t,
            0x38494000 as core::ffi::c_int as uint32_t,
            0x38496000 as core::ffi::c_int as uint32_t,
            0x38498000 as core::ffi::c_int as uint32_t,
            0x3849a000 as core::ffi::c_int as uint32_t,
            0x3849c000 as core::ffi::c_int as uint32_t,
            0x3849e000 as core::ffi::c_int as uint32_t,
            0x384a0000 as core::ffi::c_int as uint32_t,
            0x384a2000 as core::ffi::c_int as uint32_t,
            0x384a4000 as core::ffi::c_int as uint32_t,
            0x384a6000 as core::ffi::c_int as uint32_t,
            0x384a8000 as core::ffi::c_int as uint32_t,
            0x384aa000 as core::ffi::c_int as uint32_t,
            0x384ac000 as core::ffi::c_int as uint32_t,
            0x384ae000 as core::ffi::c_int as uint32_t,
            0x384b0000 as core::ffi::c_int as uint32_t,
            0x384b2000 as core::ffi::c_int as uint32_t,
            0x384b4000 as core::ffi::c_int as uint32_t,
            0x384b6000 as core::ffi::c_int as uint32_t,
            0x384b8000 as core::ffi::c_int as uint32_t,
            0x384ba000 as core::ffi::c_int as uint32_t,
            0x384bc000 as core::ffi::c_int as uint32_t,
            0x384be000 as core::ffi::c_int as uint32_t,
            0x384c0000 as core::ffi::c_int as uint32_t,
            0x384c2000 as core::ffi::c_int as uint32_t,
            0x384c4000 as core::ffi::c_int as uint32_t,
            0x384c6000 as core::ffi::c_int as uint32_t,
            0x384c8000 as core::ffi::c_int as uint32_t,
            0x384ca000 as core::ffi::c_int as uint32_t,
            0x384cc000 as core::ffi::c_int as uint32_t,
            0x384ce000 as core::ffi::c_int as uint32_t,
            0x384d0000 as core::ffi::c_int as uint32_t,
            0x384d2000 as core::ffi::c_int as uint32_t,
            0x384d4000 as core::ffi::c_int as uint32_t,
            0x384d6000 as core::ffi::c_int as uint32_t,
            0x384d8000 as core::ffi::c_int as uint32_t,
            0x384da000 as core::ffi::c_int as uint32_t,
            0x384dc000 as core::ffi::c_int as uint32_t,
            0x384de000 as core::ffi::c_int as uint32_t,
            0x384e0000 as core::ffi::c_int as uint32_t,
            0x384e2000 as core::ffi::c_int as uint32_t,
            0x384e4000 as core::ffi::c_int as uint32_t,
            0x384e6000 as core::ffi::c_int as uint32_t,
            0x384e8000 as core::ffi::c_int as uint32_t,
            0x384ea000 as core::ffi::c_int as uint32_t,
            0x384ec000 as core::ffi::c_int as uint32_t,
            0x384ee000 as core::ffi::c_int as uint32_t,
            0x384f0000 as core::ffi::c_int as uint32_t,
            0x384f2000 as core::ffi::c_int as uint32_t,
            0x384f4000 as core::ffi::c_int as uint32_t,
            0x384f6000 as core::ffi::c_int as uint32_t,
            0x384f8000 as core::ffi::c_int as uint32_t,
            0x384fa000 as core::ffi::c_int as uint32_t,
            0x384fc000 as core::ffi::c_int as uint32_t,
            0x384fe000 as core::ffi::c_int as uint32_t,
            0x38500000 as core::ffi::c_int as uint32_t,
            0x38502000 as core::ffi::c_int as uint32_t,
            0x38504000 as core::ffi::c_int as uint32_t,
            0x38506000 as core::ffi::c_int as uint32_t,
            0x38508000 as core::ffi::c_int as uint32_t,
            0x3850a000 as core::ffi::c_int as uint32_t,
            0x3850c000 as core::ffi::c_int as uint32_t,
            0x3850e000 as core::ffi::c_int as uint32_t,
            0x38510000 as core::ffi::c_int as uint32_t,
            0x38512000 as core::ffi::c_int as uint32_t,
            0x38514000 as core::ffi::c_int as uint32_t,
            0x38516000 as core::ffi::c_int as uint32_t,
            0x38518000 as core::ffi::c_int as uint32_t,
            0x3851a000 as core::ffi::c_int as uint32_t,
            0x3851c000 as core::ffi::c_int as uint32_t,
            0x3851e000 as core::ffi::c_int as uint32_t,
            0x38520000 as core::ffi::c_int as uint32_t,
            0x38522000 as core::ffi::c_int as uint32_t,
            0x38524000 as core::ffi::c_int as uint32_t,
            0x38526000 as core::ffi::c_int as uint32_t,
            0x38528000 as core::ffi::c_int as uint32_t,
            0x3852a000 as core::ffi::c_int as uint32_t,
            0x3852c000 as core::ffi::c_int as uint32_t,
            0x3852e000 as core::ffi::c_int as uint32_t,
            0x38530000 as core::ffi::c_int as uint32_t,
            0x38532000 as core::ffi::c_int as uint32_t,
            0x38534000 as core::ffi::c_int as uint32_t,
            0x38536000 as core::ffi::c_int as uint32_t,
            0x38538000 as core::ffi::c_int as uint32_t,
            0x3853a000 as core::ffi::c_int as uint32_t,
            0x3853c000 as core::ffi::c_int as uint32_t,
            0x3853e000 as core::ffi::c_int as uint32_t,
            0x38540000 as core::ffi::c_int as uint32_t,
            0x38542000 as core::ffi::c_int as uint32_t,
            0x38544000 as core::ffi::c_int as uint32_t,
            0x38546000 as core::ffi::c_int as uint32_t,
            0x38548000 as core::ffi::c_int as uint32_t,
            0x3854a000 as core::ffi::c_int as uint32_t,
            0x3854c000 as core::ffi::c_int as uint32_t,
            0x3854e000 as core::ffi::c_int as uint32_t,
            0x38550000 as core::ffi::c_int as uint32_t,
            0x38552000 as core::ffi::c_int as uint32_t,
            0x38554000 as core::ffi::c_int as uint32_t,
            0x38556000 as core::ffi::c_int as uint32_t,
            0x38558000 as core::ffi::c_int as uint32_t,
            0x3855a000 as core::ffi::c_int as uint32_t,
            0x3855c000 as core::ffi::c_int as uint32_t,
            0x3855e000 as core::ffi::c_int as uint32_t,
            0x38560000 as core::ffi::c_int as uint32_t,
            0x38562000 as core::ffi::c_int as uint32_t,
            0x38564000 as core::ffi::c_int as uint32_t,
            0x38566000 as core::ffi::c_int as uint32_t,
            0x38568000 as core::ffi::c_int as uint32_t,
            0x3856a000 as core::ffi::c_int as uint32_t,
            0x3856c000 as core::ffi::c_int as uint32_t,
            0x3856e000 as core::ffi::c_int as uint32_t,
            0x38570000 as core::ffi::c_int as uint32_t,
            0x38572000 as core::ffi::c_int as uint32_t,
            0x38574000 as core::ffi::c_int as uint32_t,
            0x38576000 as core::ffi::c_int as uint32_t,
            0x38578000 as core::ffi::c_int as uint32_t,
            0x3857a000 as core::ffi::c_int as uint32_t,
            0x3857c000 as core::ffi::c_int as uint32_t,
            0x3857e000 as core::ffi::c_int as uint32_t,
            0x38580000 as core::ffi::c_int as uint32_t,
            0x38582000 as core::ffi::c_int as uint32_t,
            0x38584000 as core::ffi::c_int as uint32_t,
            0x38586000 as core::ffi::c_int as uint32_t,
            0x38588000 as core::ffi::c_int as uint32_t,
            0x3858a000 as core::ffi::c_int as uint32_t,
            0x3858c000 as core::ffi::c_int as uint32_t,
            0x3858e000 as core::ffi::c_int as uint32_t,
            0x38590000 as core::ffi::c_int as uint32_t,
            0x38592000 as core::ffi::c_int as uint32_t,
            0x38594000 as core::ffi::c_int as uint32_t,
            0x38596000 as core::ffi::c_int as uint32_t,
            0x38598000 as core::ffi::c_int as uint32_t,
            0x3859a000 as core::ffi::c_int as uint32_t,
            0x3859c000 as core::ffi::c_int as uint32_t,
            0x3859e000 as core::ffi::c_int as uint32_t,
            0x385a0000 as core::ffi::c_int as uint32_t,
            0x385a2000 as core::ffi::c_int as uint32_t,
            0x385a4000 as core::ffi::c_int as uint32_t,
            0x385a6000 as core::ffi::c_int as uint32_t,
            0x385a8000 as core::ffi::c_int as uint32_t,
            0x385aa000 as core::ffi::c_int as uint32_t,
            0x385ac000 as core::ffi::c_int as uint32_t,
            0x385ae000 as core::ffi::c_int as uint32_t,
            0x385b0000 as core::ffi::c_int as uint32_t,
            0x385b2000 as core::ffi::c_int as uint32_t,
            0x385b4000 as core::ffi::c_int as uint32_t,
            0x385b6000 as core::ffi::c_int as uint32_t,
            0x385b8000 as core::ffi::c_int as uint32_t,
            0x385ba000 as core::ffi::c_int as uint32_t,
            0x385bc000 as core::ffi::c_int as uint32_t,
            0x385be000 as core::ffi::c_int as uint32_t,
            0x385c0000 as core::ffi::c_int as uint32_t,
            0x385c2000 as core::ffi::c_int as uint32_t,
            0x385c4000 as core::ffi::c_int as uint32_t,
            0x385c6000 as core::ffi::c_int as uint32_t,
            0x385c8000 as core::ffi::c_int as uint32_t,
            0x385ca000 as core::ffi::c_int as uint32_t,
            0x385cc000 as core::ffi::c_int as uint32_t,
            0x385ce000 as core::ffi::c_int as uint32_t,
            0x385d0000 as core::ffi::c_int as uint32_t,
            0x385d2000 as core::ffi::c_int as uint32_t,
            0x385d4000 as core::ffi::c_int as uint32_t,
            0x385d6000 as core::ffi::c_int as uint32_t,
            0x385d8000 as core::ffi::c_int as uint32_t,
            0x385da000 as core::ffi::c_int as uint32_t,
            0x385dc000 as core::ffi::c_int as uint32_t,
            0x385de000 as core::ffi::c_int as uint32_t,
            0x385e0000 as core::ffi::c_int as uint32_t,
            0x385e2000 as core::ffi::c_int as uint32_t,
            0x385e4000 as core::ffi::c_int as uint32_t,
            0x385e6000 as core::ffi::c_int as uint32_t,
            0x385e8000 as core::ffi::c_int as uint32_t,
            0x385ea000 as core::ffi::c_int as uint32_t,
            0x385ec000 as core::ffi::c_int as uint32_t,
            0x385ee000 as core::ffi::c_int as uint32_t,
            0x385f0000 as core::ffi::c_int as uint32_t,
            0x385f2000 as core::ffi::c_int as uint32_t,
            0x385f4000 as core::ffi::c_int as uint32_t,
            0x385f6000 as core::ffi::c_int as uint32_t,
            0x385f8000 as core::ffi::c_int as uint32_t,
            0x385fa000 as core::ffi::c_int as uint32_t,
            0x385fc000 as core::ffi::c_int as uint32_t,
            0x385fe000 as core::ffi::c_int as uint32_t,
            0x38600000 as core::ffi::c_int as uint32_t,
            0x38602000 as core::ffi::c_int as uint32_t,
            0x38604000 as core::ffi::c_int as uint32_t,
            0x38606000 as core::ffi::c_int as uint32_t,
            0x38608000 as core::ffi::c_int as uint32_t,
            0x3860a000 as core::ffi::c_int as uint32_t,
            0x3860c000 as core::ffi::c_int as uint32_t,
            0x3860e000 as core::ffi::c_int as uint32_t,
            0x38610000 as core::ffi::c_int as uint32_t,
            0x38612000 as core::ffi::c_int as uint32_t,
            0x38614000 as core::ffi::c_int as uint32_t,
            0x38616000 as core::ffi::c_int as uint32_t,
            0x38618000 as core::ffi::c_int as uint32_t,
            0x3861a000 as core::ffi::c_int as uint32_t,
            0x3861c000 as core::ffi::c_int as uint32_t,
            0x3861e000 as core::ffi::c_int as uint32_t,
            0x38620000 as core::ffi::c_int as uint32_t,
            0x38622000 as core::ffi::c_int as uint32_t,
            0x38624000 as core::ffi::c_int as uint32_t,
            0x38626000 as core::ffi::c_int as uint32_t,
            0x38628000 as core::ffi::c_int as uint32_t,
            0x3862a000 as core::ffi::c_int as uint32_t,
            0x3862c000 as core::ffi::c_int as uint32_t,
            0x3862e000 as core::ffi::c_int as uint32_t,
            0x38630000 as core::ffi::c_int as uint32_t,
            0x38632000 as core::ffi::c_int as uint32_t,
            0x38634000 as core::ffi::c_int as uint32_t,
            0x38636000 as core::ffi::c_int as uint32_t,
            0x38638000 as core::ffi::c_int as uint32_t,
            0x3863a000 as core::ffi::c_int as uint32_t,
            0x3863c000 as core::ffi::c_int as uint32_t,
            0x3863e000 as core::ffi::c_int as uint32_t,
            0x38640000 as core::ffi::c_int as uint32_t,
            0x38642000 as core::ffi::c_int as uint32_t,
            0x38644000 as core::ffi::c_int as uint32_t,
            0x38646000 as core::ffi::c_int as uint32_t,
            0x38648000 as core::ffi::c_int as uint32_t,
            0x3864a000 as core::ffi::c_int as uint32_t,
            0x3864c000 as core::ffi::c_int as uint32_t,
            0x3864e000 as core::ffi::c_int as uint32_t,
            0x38650000 as core::ffi::c_int as uint32_t,
            0x38652000 as core::ffi::c_int as uint32_t,
            0x38654000 as core::ffi::c_int as uint32_t,
            0x38656000 as core::ffi::c_int as uint32_t,
            0x38658000 as core::ffi::c_int as uint32_t,
            0x3865a000 as core::ffi::c_int as uint32_t,
            0x3865c000 as core::ffi::c_int as uint32_t,
            0x3865e000 as core::ffi::c_int as uint32_t,
            0x38660000 as core::ffi::c_int as uint32_t,
            0x38662000 as core::ffi::c_int as uint32_t,
            0x38664000 as core::ffi::c_int as uint32_t,
            0x38666000 as core::ffi::c_int as uint32_t,
            0x38668000 as core::ffi::c_int as uint32_t,
            0x3866a000 as core::ffi::c_int as uint32_t,
            0x3866c000 as core::ffi::c_int as uint32_t,
            0x3866e000 as core::ffi::c_int as uint32_t,
            0x38670000 as core::ffi::c_int as uint32_t,
            0x38672000 as core::ffi::c_int as uint32_t,
            0x38674000 as core::ffi::c_int as uint32_t,
            0x38676000 as core::ffi::c_int as uint32_t,
            0x38678000 as core::ffi::c_int as uint32_t,
            0x3867a000 as core::ffi::c_int as uint32_t,
            0x3867c000 as core::ffi::c_int as uint32_t,
            0x3867e000 as core::ffi::c_int as uint32_t,
            0x38680000 as core::ffi::c_int as uint32_t,
            0x38682000 as core::ffi::c_int as uint32_t,
            0x38684000 as core::ffi::c_int as uint32_t,
            0x38686000 as core::ffi::c_int as uint32_t,
            0x38688000 as core::ffi::c_int as uint32_t,
            0x3868a000 as core::ffi::c_int as uint32_t,
            0x3868c000 as core::ffi::c_int as uint32_t,
            0x3868e000 as core::ffi::c_int as uint32_t,
            0x38690000 as core::ffi::c_int as uint32_t,
            0x38692000 as core::ffi::c_int as uint32_t,
            0x38694000 as core::ffi::c_int as uint32_t,
            0x38696000 as core::ffi::c_int as uint32_t,
            0x38698000 as core::ffi::c_int as uint32_t,
            0x3869a000 as core::ffi::c_int as uint32_t,
            0x3869c000 as core::ffi::c_int as uint32_t,
            0x3869e000 as core::ffi::c_int as uint32_t,
            0x386a0000 as core::ffi::c_int as uint32_t,
            0x386a2000 as core::ffi::c_int as uint32_t,
            0x386a4000 as core::ffi::c_int as uint32_t,
            0x386a6000 as core::ffi::c_int as uint32_t,
            0x386a8000 as core::ffi::c_int as uint32_t,
            0x386aa000 as core::ffi::c_int as uint32_t,
            0x386ac000 as core::ffi::c_int as uint32_t,
            0x386ae000 as core::ffi::c_int as uint32_t,
            0x386b0000 as core::ffi::c_int as uint32_t,
            0x386b2000 as core::ffi::c_int as uint32_t,
            0x386b4000 as core::ffi::c_int as uint32_t,
            0x386b6000 as core::ffi::c_int as uint32_t,
            0x386b8000 as core::ffi::c_int as uint32_t,
            0x386ba000 as core::ffi::c_int as uint32_t,
            0x386bc000 as core::ffi::c_int as uint32_t,
            0x386be000 as core::ffi::c_int as uint32_t,
            0x386c0000 as core::ffi::c_int as uint32_t,
            0x386c2000 as core::ffi::c_int as uint32_t,
            0x386c4000 as core::ffi::c_int as uint32_t,
            0x386c6000 as core::ffi::c_int as uint32_t,
            0x386c8000 as core::ffi::c_int as uint32_t,
            0x386ca000 as core::ffi::c_int as uint32_t,
            0x386cc000 as core::ffi::c_int as uint32_t,
            0x386ce000 as core::ffi::c_int as uint32_t,
            0x386d0000 as core::ffi::c_int as uint32_t,
            0x386d2000 as core::ffi::c_int as uint32_t,
            0x386d4000 as core::ffi::c_int as uint32_t,
            0x386d6000 as core::ffi::c_int as uint32_t,
            0x386d8000 as core::ffi::c_int as uint32_t,
            0x386da000 as core::ffi::c_int as uint32_t,
            0x386dc000 as core::ffi::c_int as uint32_t,
            0x386de000 as core::ffi::c_int as uint32_t,
            0x386e0000 as core::ffi::c_int as uint32_t,
            0x386e2000 as core::ffi::c_int as uint32_t,
            0x386e4000 as core::ffi::c_int as uint32_t,
            0x386e6000 as core::ffi::c_int as uint32_t,
            0x386e8000 as core::ffi::c_int as uint32_t,
            0x386ea000 as core::ffi::c_int as uint32_t,
            0x386ec000 as core::ffi::c_int as uint32_t,
            0x386ee000 as core::ffi::c_int as uint32_t,
            0x386f0000 as core::ffi::c_int as uint32_t,
            0x386f2000 as core::ffi::c_int as uint32_t,
            0x386f4000 as core::ffi::c_int as uint32_t,
            0x386f6000 as core::ffi::c_int as uint32_t,
            0x386f8000 as core::ffi::c_int as uint32_t,
            0x386fa000 as core::ffi::c_int as uint32_t,
            0x386fc000 as core::ffi::c_int as uint32_t,
            0x386fe000 as core::ffi::c_int as uint32_t,
            0x38700000 as core::ffi::c_int as uint32_t,
            0x38702000 as core::ffi::c_int as uint32_t,
            0x38704000 as core::ffi::c_int as uint32_t,
            0x38706000 as core::ffi::c_int as uint32_t,
            0x38708000 as core::ffi::c_int as uint32_t,
            0x3870a000 as core::ffi::c_int as uint32_t,
            0x3870c000 as core::ffi::c_int as uint32_t,
            0x3870e000 as core::ffi::c_int as uint32_t,
            0x38710000 as core::ffi::c_int as uint32_t,
            0x38712000 as core::ffi::c_int as uint32_t,
            0x38714000 as core::ffi::c_int as uint32_t,
            0x38716000 as core::ffi::c_int as uint32_t,
            0x38718000 as core::ffi::c_int as uint32_t,
            0x3871a000 as core::ffi::c_int as uint32_t,
            0x3871c000 as core::ffi::c_int as uint32_t,
            0x3871e000 as core::ffi::c_int as uint32_t,
            0x38720000 as core::ffi::c_int as uint32_t,
            0x38722000 as core::ffi::c_int as uint32_t,
            0x38724000 as core::ffi::c_int as uint32_t,
            0x38726000 as core::ffi::c_int as uint32_t,
            0x38728000 as core::ffi::c_int as uint32_t,
            0x3872a000 as core::ffi::c_int as uint32_t,
            0x3872c000 as core::ffi::c_int as uint32_t,
            0x3872e000 as core::ffi::c_int as uint32_t,
            0x38730000 as core::ffi::c_int as uint32_t,
            0x38732000 as core::ffi::c_int as uint32_t,
            0x38734000 as core::ffi::c_int as uint32_t,
            0x38736000 as core::ffi::c_int as uint32_t,
            0x38738000 as core::ffi::c_int as uint32_t,
            0x3873a000 as core::ffi::c_int as uint32_t,
            0x3873c000 as core::ffi::c_int as uint32_t,
            0x3873e000 as core::ffi::c_int as uint32_t,
            0x38740000 as core::ffi::c_int as uint32_t,
            0x38742000 as core::ffi::c_int as uint32_t,
            0x38744000 as core::ffi::c_int as uint32_t,
            0x38746000 as core::ffi::c_int as uint32_t,
            0x38748000 as core::ffi::c_int as uint32_t,
            0x3874a000 as core::ffi::c_int as uint32_t,
            0x3874c000 as core::ffi::c_int as uint32_t,
            0x3874e000 as core::ffi::c_int as uint32_t,
            0x38750000 as core::ffi::c_int as uint32_t,
            0x38752000 as core::ffi::c_int as uint32_t,
            0x38754000 as core::ffi::c_int as uint32_t,
            0x38756000 as core::ffi::c_int as uint32_t,
            0x38758000 as core::ffi::c_int as uint32_t,
            0x3875a000 as core::ffi::c_int as uint32_t,
            0x3875c000 as core::ffi::c_int as uint32_t,
            0x3875e000 as core::ffi::c_int as uint32_t,
            0x38760000 as core::ffi::c_int as uint32_t,
            0x38762000 as core::ffi::c_int as uint32_t,
            0x38764000 as core::ffi::c_int as uint32_t,
            0x38766000 as core::ffi::c_int as uint32_t,
            0x38768000 as core::ffi::c_int as uint32_t,
            0x3876a000 as core::ffi::c_int as uint32_t,
            0x3876c000 as core::ffi::c_int as uint32_t,
            0x3876e000 as core::ffi::c_int as uint32_t,
            0x38770000 as core::ffi::c_int as uint32_t,
            0x38772000 as core::ffi::c_int as uint32_t,
            0x38774000 as core::ffi::c_int as uint32_t,
            0x38776000 as core::ffi::c_int as uint32_t,
            0x38778000 as core::ffi::c_int as uint32_t,
            0x3877a000 as core::ffi::c_int as uint32_t,
            0x3877c000 as core::ffi::c_int as uint32_t,
            0x3877e000 as core::ffi::c_int as uint32_t,
            0x38780000 as core::ffi::c_int as uint32_t,
            0x38782000 as core::ffi::c_int as uint32_t,
            0x38784000 as core::ffi::c_int as uint32_t,
            0x38786000 as core::ffi::c_int as uint32_t,
            0x38788000 as core::ffi::c_int as uint32_t,
            0x3878a000 as core::ffi::c_int as uint32_t,
            0x3878c000 as core::ffi::c_int as uint32_t,
            0x3878e000 as core::ffi::c_int as uint32_t,
            0x38790000 as core::ffi::c_int as uint32_t,
            0x38792000 as core::ffi::c_int as uint32_t,
            0x38794000 as core::ffi::c_int as uint32_t,
            0x38796000 as core::ffi::c_int as uint32_t,
            0x38798000 as core::ffi::c_int as uint32_t,
            0x3879a000 as core::ffi::c_int as uint32_t,
            0x3879c000 as core::ffi::c_int as uint32_t,
            0x3879e000 as core::ffi::c_int as uint32_t,
            0x387a0000 as core::ffi::c_int as uint32_t,
            0x387a2000 as core::ffi::c_int as uint32_t,
            0x387a4000 as core::ffi::c_int as uint32_t,
            0x387a6000 as core::ffi::c_int as uint32_t,
            0x387a8000 as core::ffi::c_int as uint32_t,
            0x387aa000 as core::ffi::c_int as uint32_t,
            0x387ac000 as core::ffi::c_int as uint32_t,
            0x387ae000 as core::ffi::c_int as uint32_t,
            0x387b0000 as core::ffi::c_int as uint32_t,
            0x387b2000 as core::ffi::c_int as uint32_t,
            0x387b4000 as core::ffi::c_int as uint32_t,
            0x387b6000 as core::ffi::c_int as uint32_t,
            0x387b8000 as core::ffi::c_int as uint32_t,
            0x387ba000 as core::ffi::c_int as uint32_t,
            0x387bc000 as core::ffi::c_int as uint32_t,
            0x387be000 as core::ffi::c_int as uint32_t,
            0x387c0000 as core::ffi::c_int as uint32_t,
            0x387c2000 as core::ffi::c_int as uint32_t,
            0x387c4000 as core::ffi::c_int as uint32_t,
            0x387c6000 as core::ffi::c_int as uint32_t,
            0x387c8000 as core::ffi::c_int as uint32_t,
            0x387ca000 as core::ffi::c_int as uint32_t,
            0x387cc000 as core::ffi::c_int as uint32_t,
            0x387ce000 as core::ffi::c_int as uint32_t,
            0x387d0000 as core::ffi::c_int as uint32_t,
            0x387d2000 as core::ffi::c_int as uint32_t,
            0x387d4000 as core::ffi::c_int as uint32_t,
            0x387d6000 as core::ffi::c_int as uint32_t,
            0x387d8000 as core::ffi::c_int as uint32_t,
            0x387da000 as core::ffi::c_int as uint32_t,
            0x387dc000 as core::ffi::c_int as uint32_t,
            0x387de000 as core::ffi::c_int as uint32_t,
            0x387e0000 as core::ffi::c_int as uint32_t,
            0x387e2000 as core::ffi::c_int as uint32_t,
            0x387e4000 as core::ffi::c_int as uint32_t,
            0x387e6000 as core::ffi::c_int as uint32_t,
            0x387e8000 as core::ffi::c_int as uint32_t,
            0x387ea000 as core::ffi::c_int as uint32_t,
            0x387ec000 as core::ffi::c_int as uint32_t,
            0x387ee000 as core::ffi::c_int as uint32_t,
            0x387f0000 as core::ffi::c_int as uint32_t,
            0x387f2000 as core::ffi::c_int as uint32_t,
            0x387f4000 as core::ffi::c_int as uint32_t,
            0x387f6000 as core::ffi::c_int as uint32_t,
            0x387f8000 as core::ffi::c_int as uint32_t,
            0x387fa000 as core::ffi::c_int as uint32_t,
            0x387fc000 as core::ffi::c_int as uint32_t,
            0x387fe000 as core::ffi::c_int as uint32_t,
        ];
        static mut m__offset: [uint16_t; 64] = [
            0 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
            0x400 as core::ffi::c_int as uint16_t,
        ];
        static mut m__exponent: [uint32_t; 64] = [
            0 as core::ffi::c_int as uint32_t,
            0x800000 as core::ffi::c_int as uint32_t,
            0x1000000 as core::ffi::c_int as uint32_t,
            0x1800000 as core::ffi::c_int as uint32_t,
            0x2000000 as core::ffi::c_int as uint32_t,
            0x2800000 as core::ffi::c_int as uint32_t,
            0x3000000 as core::ffi::c_int as uint32_t,
            0x3800000 as core::ffi::c_int as uint32_t,
            0x4000000 as core::ffi::c_int as uint32_t,
            0x4800000 as core::ffi::c_int as uint32_t,
            0x5000000 as core::ffi::c_int as uint32_t,
            0x5800000 as core::ffi::c_int as uint32_t,
            0x6000000 as core::ffi::c_int as uint32_t,
            0x6800000 as core::ffi::c_int as uint32_t,
            0x7000000 as core::ffi::c_int as uint32_t,
            0x7800000 as core::ffi::c_int as uint32_t,
            0x8000000 as core::ffi::c_int as uint32_t,
            0x8800000 as core::ffi::c_int as uint32_t,
            0x9000000 as core::ffi::c_int as uint32_t,
            0x9800000 as core::ffi::c_int as uint32_t,
            0xa000000 as core::ffi::c_int as uint32_t,
            0xa800000 as core::ffi::c_int as uint32_t,
            0xb000000 as core::ffi::c_int as uint32_t,
            0xb800000 as core::ffi::c_int as uint32_t,
            0xc000000 as core::ffi::c_int as uint32_t,
            0xc800000 as core::ffi::c_int as uint32_t,
            0xd000000 as core::ffi::c_int as uint32_t,
            0xd800000 as core::ffi::c_int as uint32_t,
            0xe000000 as core::ffi::c_int as uint32_t,
            0xe800000 as core::ffi::c_int as uint32_t,
            0xf000000 as core::ffi::c_int as uint32_t,
            0x47800000 as core::ffi::c_int as uint32_t,
            0x80000000 as core::ffi::c_uint,
            0x80800000 as core::ffi::c_uint,
            0x81000000 as core::ffi::c_uint,
            0x81800000 as core::ffi::c_uint,
            0x82000000 as core::ffi::c_uint,
            0x82800000 as core::ffi::c_uint,
            0x83000000 as core::ffi::c_uint,
            0x83800000 as core::ffi::c_uint,
            0x84000000 as core::ffi::c_uint,
            0x84800000 as core::ffi::c_uint,
            0x85000000 as core::ffi::c_uint,
            0x85800000 as core::ffi::c_uint,
            0x86000000 as core::ffi::c_uint,
            0x86800000 as core::ffi::c_uint,
            0x87000000 as core::ffi::c_uint,
            0x87800000 as core::ffi::c_uint,
            0x88000000 as core::ffi::c_uint,
            0x88800000 as core::ffi::c_uint,
            0x89000000 as core::ffi::c_uint,
            0x89800000 as core::ffi::c_uint,
            0x8a000000 as core::ffi::c_uint,
            0x8a800000 as core::ffi::c_uint,
            0x8b000000 as core::ffi::c_uint,
            0x8b800000 as core::ffi::c_uint,
            0x8c000000 as core::ffi::c_uint,
            0x8c800000 as core::ffi::c_uint,
            0x8d000000 as core::ffi::c_uint,
            0x8d800000 as core::ffi::c_uint,
            0x8e000000 as core::ffi::c_uint,
            0x8e800000 as core::ffi::c_uint,
            0x8f000000 as core::ffi::c_uint,
            0xc7800000 as core::ffi::c_uint,
        ];
        #[no_mangle]
        pub unsafe extern "C" fn f10(h: uint16_t) -> core::ffi::c_float {
            let mut out: C2RustUnnamed = C2RustUnnamed { flt: 0. };
            let n: core::ffi::c_int = h as core::ffi::c_int >> 10 as core::ffi::c_int;
            out.num = (m__mantissa[((h as core::ffi::c_int & 0x3ff as core::ffi::c_int)
                + m__offset[n as usize] as core::ffi::c_int)
                as usize])
                .wrapping_add(m__exponent[n as usize]);
            out.flt
        }
        #[no_mangle]
        pub unsafe extern "C" fn f11(
            dest: *mut core::ffi::c_float,
            src: *const core::ffi::c_float,
        ) {
            let h: core::ffi::c_float = *src.offset(0 as core::ffi::c_int as isize);
            let s: core::ffi::c_float = *src.offset(1 as core::ffi::c_int as isize);
            let l: core::ffi::c_float = *src.offset(2 as core::ffi::c_int as isize);
            let mut c: core::ffi::c_float = 0.;
            let mut m: core::ffi::c_float = 0.;
            let mut x: core::ffi::c_float = 0.;
            if s == 0 as core::ffi::c_int as core::ffi::c_float {
                *dest.offset(0 as core::ffi::c_int as isize) = l;
                *dest.offset(1 as core::ffi::c_int as isize) = l;
                *dest.offset(2 as core::ffi::c_int as isize) = l;
                return;
            }
            c = (1.0f32 - fabsf(2.0f32 * l - 1.0f32)) * s;
            m = 1.0f32 * (l - 0.5f32 * c);
            x = c
                * (1.0f32
                    - fabsf(
                        fmodf(h / 60.0f32, 2 as core::ffi::c_int as core::ffi::c_float) - 1.0f32,
                    ));
            if (0.0f32..60.0f32).contains(&h) {
                *dest.offset(0 as core::ffi::c_int as isize) = c + m;
                *dest.offset(1 as core::ffi::c_int as isize) = x + m;
                *dest.offset(2 as core::ffi::c_int as isize) = m;
            } else if (60.0f32..120.0f32).contains(&h) {
                *dest.offset(0 as core::ffi::c_int as isize) = x + m;
                *dest.offset(1 as core::ffi::c_int as isize) = c + m;
                *dest.offset(2 as core::ffi::c_int as isize) = m;
            } else if h < 120.0f32 && h < 180.0f32 {
                *dest.offset(0 as core::ffi::c_int as isize) = m;
                *dest.offset(1 as core::ffi::c_int as isize) = c + m;
                *dest.offset(2 as core::ffi::c_int as isize) = x + m;
            } else if (180.0f32..240.0f32).contains(&h) {
                *dest.offset(0 as core::ffi::c_int as isize) = m;
                *dest.offset(1 as core::ffi::c_int as isize) = x + m;
                *dest.offset(2 as core::ffi::c_int as isize) = c + m;
            } else if (240.0f32..300.0f32).contains(&h) {
                *dest.offset(0 as core::ffi::c_int as isize) = x + m;
                *dest.offset(1 as core::ffi::c_int as isize) = m;
                *dest.offset(2 as core::ffi::c_int as isize) = c + m;
            } else if (300.0f32..360.0f32).contains(&h) {
                *dest.offset(0 as core::ffi::c_int as isize) = c + m;
                *dest.offset(1 as core::ffi::c_int as isize) = m;
                *dest.offset(2 as core::ffi::c_int as isize) = x + m;
            } else {
                *dest.offset(0 as core::ffi::c_int as isize) = m;
                *dest.offset(1 as core::ffi::c_int as isize) = m;
                *dest.offset(2 as core::ffi::c_int as isize) = m;
            };
        }
        #[no_mangle]
        pub unsafe extern "C" fn f12(
            dest: *mut core::ffi::c_float,
            src: *const core::ffi::c_float,
        ) {
            let mut r: core::ffi::c_float = 0.;
            let mut g: core::ffi::c_float = 0.;
            let mut b: core::ffi::c_float = 0.;
            let mut f: core::ffi::c_float = 0.;
            let mut p: core::ffi::c_float = 0.;
            let mut q: core::ffi::c_float = 0.;
            let mut t: core::ffi::c_float = 0.;
            let mut h: core::ffi::c_float = *src.offset(0 as core::ffi::c_int as isize);
            let s: core::ffi::c_float = *src.offset(1 as core::ffi::c_int as isize);
            let v: core::ffi::c_float = *src.offset(2 as core::ffi::c_int as isize);
            let mut i: core::ffi::c_int = 0;
            if s == 0 as core::ffi::c_int as core::ffi::c_float {
                *dest.offset(0 as core::ffi::c_int as isize) = v;
                *dest.offset(1 as core::ffi::c_int as isize) = v;
                *dest.offset(2 as core::ffi::c_int as isize) = v;
                return;
            }
            h /= 60.0f32;
            i = floorf(h) as core::ffi::c_int;
            f = h - i as core::ffi::c_float;
            p = v * (1 as core::ffi::c_int as core::ffi::c_float - s);
            q = v * (1 as core::ffi::c_int as core::ffi::c_float - s * f);
            t = v
                * (1 as core::ffi::c_int as core::ffi::c_float
                    - s * (1 as core::ffi::c_int as core::ffi::c_float - f));
            match i {
                0 => {
                    r = v;
                    g = t;
                    b = p;
                }
                1 => {
                    r = q;
                    g = v;
                    b = p;
                }
                2 => {
                    r = p;
                    g = v;
                    b = t;
                }
                3 => {
                    r = p;
                    g = q;
                    b = v;
                }
                4 => {
                    r = t;
                    g = p;
                    b = v;
                }
                _ => {
                    r = v;
                    g = p;
                    b = q;
                }
            }
            *dest.offset(0 as core::ffi::c_int as isize) = r;
            *dest.offset(1 as core::ffi::c_int as isize) = g;
            *dest.offset(2 as core::ffi::c_int as isize) = b;
        }
        #[no_mangle]
        pub unsafe extern "C" fn f13(
            dest: *mut core::ffi::c_float,
            src: *const core::ffi::c_float,
        ) {
            let r: core::ffi::c_float = *src.offset(0 as core::ffi::c_int as isize);
            let g: core::ffi::c_float = *src.offset(1 as core::ffi::c_int as isize);
            let b: core::ffi::c_float = *src.offset(2 as core::ffi::c_int as isize);
            let mut h: core::ffi::c_float = 0 as core::ffi::c_int as core::ffi::c_float;
            let mut s: core::ffi::c_float = 0 as core::ffi::c_int as core::ffi::c_float;
            let mut v: core::ffi::c_float = 0 as core::ffi::c_int as core::ffi::c_float;
            let mut min: core::ffi::c_float = r;
            let mut max: core::ffi::c_float = r;
            let mut delta: core::ffi::c_float = 0.;
            min = if min < g { min } else { g };
            min = if min < b { min } else { b };
            max = if max > g { max } else { g };
            max = if max > b { max } else { b };
            delta = max - min;
            v = max;
            if delta == 0 as core::ffi::c_int as core::ffi::c_float
                || max == 0 as core::ffi::c_int as core::ffi::c_float
            {
                *dest.offset(0 as core::ffi::c_int as isize) = h;
                *dest.offset(1 as core::ffi::c_int as isize) = s;
                *dest.offset(2 as core::ffi::c_int as isize) = v;
                return;
            }
            s = delta / max;
            if r == max {
                h = (g - b) / delta;
            } else if g == max {
                h = 2 as core::ffi::c_int as core::ffi::c_float + (b - r) / delta;
            } else {
                h = 4 as core::ffi::c_int as core::ffi::c_float + (r - g) / delta;
            }
            h *= 60 as core::ffi::c_int as core::ffi::c_float;
            if h < 0 as core::ffi::c_int as core::ffi::c_float {
                h += 360 as core::ffi::c_int as core::ffi::c_float;
            }
            *dest.offset(0 as core::ffi::c_int as isize) = h;
            *dest.offset(1 as core::ffi::c_int as isize) = s;
            *dest.offset(2 as core::ffi::c_int as isize) = v;
        }
        #[no_mangle]
        pub unsafe extern "C" fn agglom(
            f2_1: core::ffi::c_float,
            f2_2: core::ffi::c_float,
            f2_3: core::ffi::c_float,
            f2_7: core::ffi::c_float,
            f2_8: core::ffi::c_float,
            f2_9: core::ffi::c_float,
            f2_10: core::ffi::c_float,
            f3_1: core::ffi::c_int,
            f3_2: core::ffi::c_int,
            f4_1: uint64_t,
            f4_2: uint64_t,
            f5_1: uint32_t,
            f7_1: tflac_u32,
            f7_2: tflac_u32,
            f7_3: tflac_u32,
            f9_1: core::ffi::c_float,
            f9_2: core::ffi::c_float,
            f9_4: core::ffi::c_float,
            f9_5: core::ffi::c_float,
            f9_7: core::ffi::c_float,
            f9_8: core::ffi::c_float,
            f9_10: core::ffi::c_float,
            f9_11: core::ffi::c_float,
            f10_1: uint16_t,
            f11_2: core::ffi::c_float,
            f11_3: core::ffi::c_float,
            f11_4: core::ffi::c_float,
            f12_2: core::ffi::c_float,
            f12_3: core::ffi::c_float,
            f12_4: core::ffi::c_float,
            f13_2: core::ffi::c_float,
            f13_3: core::ffi::c_float,
            f13_4: core::ffi::c_float,
        ) -> core::ffi::c_double {
            let mut ret: core::ffi::c_double = 0.0f64;
            let mut f2_5: c2Circle = {
                c2Circle {
                    p: { c2v { x: f2_1, y: f2_2 } },
                    r: f2_3,
                }
            };
            let f2_6: C2_TYPE = C2_TYPE_CIRCLE;
            let mut f2_11: c2AABB = {
                c2AABB {
                    min: { c2v { x: f2_7, y: f2_8 } },
                    max: { c2v { x: f2_9, y: f2_10 } },
                }
            };
            let f2_12: C2_TYPE = C2_TYPE_AABB;
            let f2_r: core::ffi::c_int = f2(
                &mut f2_5 as *mut c2Circle as *mut core::ffi::c_void,
                f2_6,
                &mut f2_11 as *mut c2AABB as *mut core::ffi::c_void,
                f2_12,
            );
            ret += f2_r as core::ffi::c_double;
            let f3_r: core::ffi::c_int = f3(f3_1, f3_2);
            ret += f3_r as core::ffi::c_double;
            let mut f4_3: cn_rnd_t = {
                cn_rnd_t {
                    state: [f4_1, f4_2],
                }
            };
            let f4_r: core::ffi::c_double = f4(&mut f4_3);
            if f4_r.is_nan() as i32 == 0 {
                ret += f4_r;
            }
            let f5_r: uint32_t = f5(f5_1);
            ret += f5_r as core::ffi::c_double;
            let f7_r: tflac_u32 = f7(f7_1, f7_2, f7_3);
            ret += f7_r as core::ffi::c_double;
            let f9_3: lm_vec2 = { lm_vec2 { x: f9_1, y: f9_2 } };
            let f9_6: lm_vec2 = { lm_vec2 { x: f9_4, y: f9_5 } };
            let f9_9: lm_vec2 = { lm_vec2 { x: f9_7, y: f9_8 } };
            let f9_12: lm_vec2 = { lm_vec2 { x: f9_10, y: f9_11 } };
            let f9_r: lm_vec2 = f9(f9_3, f9_6, f9_9, f9_12);
            if (f9_r.x).is_nan() as i32 == 0 {
                ret += f9_r.x as core::ffi::c_double;
            }
            if (f9_r.y).is_nan() as i32 == 0 {
                ret += f9_r.y as core::ffi::c_double;
            }
            let f10_r: core::ffi::c_float = f10(f10_1);
            if f10_r.is_nan() as i32 == 0 {
                ret += f10_r as core::ffi::c_double;
            }
            let mut f11_r: [core::ffi::c_float; 3] = [
                0 as core::ffi::c_int as core::ffi::c_float,
                0 as core::ffi::c_int as core::ffi::c_float,
                0 as core::ffi::c_int as core::ffi::c_float,
            ];
            let f11_5: [core::ffi::c_float; 3] = [f11_2, f11_3, f11_4];
            f11(f11_r.as_mut_ptr(), f11_5.as_ptr());
            if (f11_r[0 as core::ffi::c_int as usize]).is_nan() as i32 == 0 {
                ret += f11_r[0 as core::ffi::c_int as usize] as core::ffi::c_double;
            }
            if (f11_r[1 as core::ffi::c_int as usize]).is_nan() as i32 == 0 {
                ret += f11_r[1 as core::ffi::c_int as usize] as core::ffi::c_double;
            }
            if (f11_r[2 as core::ffi::c_int as usize]).is_nan() as i32 == 0 {
                ret += f11_r[2 as core::ffi::c_int as usize] as core::ffi::c_double;
            }
            let mut f12_r: [core::ffi::c_float; 3] = [
                0 as core::ffi::c_int as core::ffi::c_float,
                0 as core::ffi::c_int as core::ffi::c_float,
                0 as core::ffi::c_int as core::ffi::c_float,
            ];
            let f12_5: [core::ffi::c_float; 3] = [f12_2, f12_3, f12_4];
            f12(f12_r.as_mut_ptr(), f12_5.as_ptr());
            if (f12_r[0 as core::ffi::c_int as usize]).is_nan() as i32 == 0 {
                ret += f12_r[0 as core::ffi::c_int as usize] as core::ffi::c_double;
            }
            if (f12_r[1 as core::ffi::c_int as usize]).is_nan() as i32 == 0 {
                ret += f12_r[1 as core::ffi::c_int as usize] as core::ffi::c_double;
            }
            if (f12_r[2 as core::ffi::c_int as usize]).is_nan() as i32 == 0 {
                ret += f12_r[2 as core::ffi::c_int as usize] as core::ffi::c_double;
            }
            let mut f13_r: [core::ffi::c_float; 3] = [
                0 as core::ffi::c_int as core::ffi::c_float,
                0 as core::ffi::c_int as core::ffi::c_float,
                0 as core::ffi::c_int as core::ffi::c_float,
            ];
            let f13_5: [core::ffi::c_float; 3] = [f13_2, f13_3, f13_4];
            f13(f13_r.as_mut_ptr(), f13_5.as_ptr());
            if (f13_r[0 as core::ffi::c_int as usize]).is_nan() as i32 == 0 {
                ret += f13_r[0 as core::ffi::c_int as usize] as core::ffi::c_double;
            }
            if (f13_r[1 as core::ffi::c_int as usize]).is_nan() as i32 == 0 {
                ret += f13_r[1 as core::ffi::c_int as usize] as core::ffi::c_double;
            }
            if (f13_r[2 as core::ffi::c_int as usize]).is_nan() as i32 == 0 {
                ret += f13_r[2 as core::ffi::c_int as usize] as core::ffi::c_double;
            }
            ret
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates("agglom_lib", SOURCE, &[], &[]);
}
