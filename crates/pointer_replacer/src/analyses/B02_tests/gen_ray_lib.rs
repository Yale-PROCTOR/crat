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
            fn sqrtf(__x: core::ffi::c_float)
            -> core::ffi::c_float;
        }
        #[repr(C)]
        pub struct c2v {
            pub x: core::ffi::c_float,
            pub y: core::ffi::c_float,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for c2v { }
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
        pub struct c2Raycast {
            pub t: core::ffi::c_float,
            pub n: c2v,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for c2Raycast { }
        #[automatically_derived]
        impl ::core::clone::Clone for c2Raycast {
            #[inline]
            fn clone(&self) -> c2Raycast {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_float>;
                let _: ::core::clone::AssertParamIsClone<c2v>;
                *self
            }
        }
        pub type C2_TYPE = core::ffi::c_uint;
        pub const C2_TYPE_CAPSULE: C2_TYPE = 2;
        pub const C2_TYPE_AABB: C2_TYPE = 1;
        pub const C2_TYPE_CIRCLE: C2_TYPE = 0;
        #[repr(C)]
        pub struct c2AABB {
            pub min: c2v,
            pub max: c2v,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for c2AABB { }
        #[automatically_derived]
        impl ::core::clone::Clone for c2AABB {
            #[inline]
            fn clone(&self) -> c2AABB {
                let _: ::core::clone::AssertParamIsClone<c2v>;
                *self
            }
        }
        #[repr(C)]
        pub struct c2Ray {
            pub p: c2v,
            pub d: c2v,
            pub t: core::ffi::c_float,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for c2Ray { }
        #[automatically_derived]
        impl ::core::clone::Clone for c2Ray {
            #[inline]
            fn clone(&self) -> c2Ray {
                let _: ::core::clone::AssertParamIsClone<c2v>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_float>;
                *self
            }
        }
        #[repr(C)]
        pub struct c2Capsule {
            pub a: c2v,
            pub b: c2v,
            pub r: core::ffi::c_float,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for c2Capsule { }
        #[automatically_derived]
        impl ::core::clone::Clone for c2Capsule {
            #[inline]
            fn clone(&self) -> c2Capsule {
                let _: ::core::clone::AssertParamIsClone<c2v>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_float>;
                *self
            }
        }
        #[repr(C)]
        pub struct c2m {
            pub x: c2v,
            pub y: c2v,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for c2m { }
        #[automatically_derived]
        impl ::core::clone::Clone for c2m {
            #[inline]
            fn clone(&self) -> c2m {
                let _: ::core::clone::AssertParamIsClone<c2v>;
                *self
            }
        }
        #[repr(C)]
        pub struct c2Circle {
            pub p: c2v,
            pub r: core::ffi::c_float,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for c2Circle { }
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
        pub unsafe extern "C" fn c2V(mut x: core::ffi::c_float,
            mut y: core::ffi::c_float) -> c2v {
            let mut a: c2v = c2v { x: 0., y: 0. };
            a.x = x;
            a.y = y;
            return a;
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Dot(mut a: c2v, mut b: c2v)
            -> core::ffi::c_float {
            return a.x * b.x + a.y * b.y;
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Len(mut a: c2v) -> core::ffi::c_float {
            return sqrtf(c2Dot(a, a));
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Add(mut a: c2v, mut b: c2v) -> c2v {
            a.x += b.x;
            a.y += b.y;
            return a;
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Sub(mut a: c2v, mut b: c2v) -> c2v {
            a.x -= b.x;
            a.y -= b.y;
            return a;
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Mulvs(mut a: c2v,
            mut b: core::ffi::c_float) -> c2v {
            a.x *= b;
            a.y *= b;
            return a;
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Div(mut a: c2v, mut b: core::ffi::c_float)
            -> c2v {
            return c2Mulvs(a, 1.0f32 / b);
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Norm(mut a: c2v) -> c2v {
            return c2Div(a, c2Len(a));
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Minv(mut a: c2v, mut b: c2v) -> c2v {
            return c2V(if a.x < b.x { a.x } else { b.x },
                    if a.y < b.y { a.y } else { b.y });
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Maxv(mut a: c2v, mut b: c2v) -> c2v {
            return c2V(if a.x > b.x { a.x } else { b.x },
                    if a.y > b.y { a.y } else { b.y });
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Skew(mut a: c2v) -> c2v {
            let mut b: c2v = c2v { x: 0., y: 0. };
            b.x = -a.y;
            b.y = a.x;
            return b;
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Absv(mut a: c2v) -> c2v {
            return c2V(if a.x < 0 as core::ffi::c_int as core::ffi::c_float {
                        -a.x
                    } else { a.x },
                    if a.y < 0 as core::ffi::c_int as core::ffi::c_float {
                        -a.y
                    } else { a.y });
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2RaytoCircle(mut A: c2Ray, mut B: c2Circle,
            mut out: *mut c2Raycast) -> core::ffi::c_int {
            let mut p: c2v = B.p;
            let mut m: c2v = c2Sub(A.p, p);
            let mut c: core::ffi::c_float = c2Dot(m, m) - B.r * B.r;
            let mut b: core::ffi::c_float = c2Dot(m, A.d);
            let mut disc: core::ffi::c_float = b * b - c;
            if disc < 0 as core::ffi::c_int as core::ffi::c_float {
                return 0 as core::ffi::c_int;
            }
            let mut t: core::ffi::c_float = -b - sqrtf(disc);
            if t >= 0 as core::ffi::c_int as core::ffi::c_float && t <= A.t {
                (*out).t = t;
                let mut impact: c2v = c2Add(A.p, c2Mulvs(A.d, t));
                (*out).n = c2Norm(c2Sub(impact, p));
                return 1 as core::ffi::c_int;
            }
            return 0 as core::ffi::c_int;
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2AABBtoAABB(mut A: c2AABB, mut B: c2AABB)
            -> core::ffi::c_int {
            let mut d0: core::ffi::c_int =
                (B.max.x < A.min.x) as core::ffi::c_int;
            let mut d1: core::ffi::c_int =
                (A.max.x < B.min.x) as core::ffi::c_int;
            let mut d2: core::ffi::c_int =
                (B.max.y < A.min.y) as core::ffi::c_int;
            let mut d3: core::ffi::c_int =
                (A.max.y < B.min.y) as core::ffi::c_int;
            return (d0 | d1 | d2 | d3 == 0) as core::ffi::c_int;
        }
        #[inline]
        unsafe extern "C" fn c2SignedDistPointToPlane_OneDimensional(mut p:
                core::ffi::c_float, mut n: core::ffi::c_float,
            mut d: core::ffi::c_float) -> core::ffi::c_float {
            return p * n - d * n;
        }
        #[inline]
        unsafe extern "C" fn c2RayToPlane_OneDimensional(mut da:
                core::ffi::c_float, mut db: core::ffi::c_float)
            -> core::ffi::c_float {
            if da < 0 as core::ffi::c_int as core::ffi::c_float {
                return 0 as core::ffi::c_int as core::ffi::c_float
            } else if da * db > 0 as core::ffi::c_int as core::ffi::c_float {
                return 1.0f32
            } else {
                let mut d: core::ffi::c_float = da - db;
                if d != 0 as core::ffi::c_int as core::ffi::c_float {
                    return da / d
                } else { return 0 as core::ffi::c_int as core::ffi::c_float }
            };
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2RaytoAABB(mut A: c2Ray, mut B: c2AABB,
            mut out: *mut c2Raycast) -> core::ffi::c_int {
            let mut p0: c2v = A.p;
            let mut p1: c2v = c2Add(A.p, c2Mulvs(A.d, A.t));
            let mut a_box: c2AABB =
                c2AABB {
                    min: c2v { x: 0., y: 0. },
                    max: c2v { x: 0., y: 0. },
                };
            a_box.min = c2Minv(p0, p1);
            a_box.max = c2Maxv(p0, p1);
            if c2AABBtoAABB(a_box, B) == 0 { return 0 as core::ffi::c_int; }
            let mut ab: c2v = c2Sub(p1, p0);
            let mut n: c2v = c2Skew(ab);
            let mut abs_n: c2v = c2Absv(n);
            let mut half_extents: c2v = c2Mulvs(c2Sub(B.max, B.min), 0.5f32);
            let mut center_of_b_box: c2v =
                c2Mulvs(c2Add(B.min, B.max), 0.5f32);
            let mut d: core::ffi::c_float =
                (if c2Dot(n, c2Sub(p0, center_of_b_box)) <
                                0 as core::ffi::c_int as core::ffi::c_float {
                            -c2Dot(n, c2Sub(p0, center_of_b_box))
                        } else { c2Dot(n, c2Sub(p0, center_of_b_box)) }) -
                    c2Dot(abs_n, half_extents);
            if d > 0 as core::ffi::c_int as core::ffi::c_float {
                return 0 as core::ffi::c_int;
            }
            let mut da0: core::ffi::c_float =
                c2SignedDistPointToPlane_OneDimensional(p0.x, -1.0f32,
                    B.min.x);
            let mut db0: core::ffi::c_float =
                c2SignedDistPointToPlane_OneDimensional(p1.x, -1.0f32,
                    B.min.x);
            let mut da1: core::ffi::c_float =
                c2SignedDistPointToPlane_OneDimensional(p0.x, 1.0f32,
                    B.max.x);
            let mut db1: core::ffi::c_float =
                c2SignedDistPointToPlane_OneDimensional(p1.x, 1.0f32,
                    B.max.x);
            let mut da2: core::ffi::c_float =
                c2SignedDistPointToPlane_OneDimensional(p0.y, -1.0f32,
                    B.min.y);
            let mut db2: core::ffi::c_float =
                c2SignedDistPointToPlane_OneDimensional(p1.y, -1.0f32,
                    B.min.y);
            let mut da3: core::ffi::c_float =
                c2SignedDistPointToPlane_OneDimensional(p0.y, 1.0f32,
                    B.max.y);
            let mut db3: core::ffi::c_float =
                c2SignedDistPointToPlane_OneDimensional(p1.y, 1.0f32,
                    B.max.y);
            let mut t0: core::ffi::c_float =
                c2RayToPlane_OneDimensional(da0, db0);
            let mut t1: core::ffi::c_float =
                c2RayToPlane_OneDimensional(da1, db1);
            let mut t2: core::ffi::c_float =
                c2RayToPlane_OneDimensional(da2, db2);
            let mut t3: core::ffi::c_float =
                c2RayToPlane_OneDimensional(da3, db3);
            let mut hit0: core::ffi::c_int =
                (t0 <= 1.0f32) as core::ffi::c_int;
            let mut hit1: core::ffi::c_int =
                (t1 <= 1.0f32) as core::ffi::c_int;
            let mut hit2: core::ffi::c_int =
                (t2 <= 1.0f32) as core::ffi::c_int;
            let mut hit3: core::ffi::c_int =
                (t3 <= 1.0f32) as core::ffi::c_int;
            let mut hit: core::ffi::c_int = hit0 | hit1 | hit2 | hit3;
            if hit != 0 {
                t0 = hit0 as core::ffi::c_float * t0;
                t1 = hit1 as core::ffi::c_float * t1;
                t2 = hit2 as core::ffi::c_float * t2;
                t3 = hit3 as core::ffi::c_float * t3;
                if t0 >= t1 && t0 >= t2 && t0 >= t3 {
                    (*out).t = t0 * A.t;
                    (*out).n =
                        c2V(-(1 as core::ffi::c_int) as core::ffi::c_float,
                            0 as core::ffi::c_int as core::ffi::c_float);
                } else if t1 >= t0 && t1 >= t2 && t1 >= t3 {
                    (*out).t = t1 * A.t;
                    (*out).n =
                        c2V(1 as core::ffi::c_int as core::ffi::c_float,
                            0 as core::ffi::c_int as core::ffi::c_float);
                } else if t2 >= t0 && t2 >= t1 && t2 >= t3 {
                    (*out).t = t2 * A.t;
                    (*out).n =
                        c2V(0 as core::ffi::c_int as core::ffi::c_float,
                            -(1 as core::ffi::c_int) as core::ffi::c_float);
                } else {
                    (*out).t = t3 * A.t;
                    (*out).n =
                        c2V(0 as core::ffi::c_int as core::ffi::c_float,
                            1 as core::ffi::c_int as core::ffi::c_float);
                }
                return 1 as core::ffi::c_int;
            } else { return 0 as core::ffi::c_int };
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2CCW90(mut a: c2v) -> c2v {
            let mut b: c2v = c2v { x: 0., y: 0. };
            b.x = a.y;
            b.y = -a.x;
            return b;
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2MulmvT(mut a: c2m, mut b: c2v) -> c2v {
            let mut c: c2v = c2v { x: 0., y: 0. };
            c.x = a.x.x * b.x + a.x.y * b.y;
            c.y = a.y.x * b.x + a.y.y * b.y;
            return c;
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2AABBtoPoint(mut A: c2AABB, mut B: c2v)
            -> core::ffi::c_int {
            let mut d0: core::ffi::c_int =
                (B.x < A.min.x) as core::ffi::c_int;
            let mut d1: core::ffi::c_int =
                (B.y < A.min.y) as core::ffi::c_int;
            let mut d2: core::ffi::c_int =
                (B.x > A.max.x) as core::ffi::c_int;
            let mut d3: core::ffi::c_int =
                (B.y > A.max.y) as core::ffi::c_int;
            return (d0 | d1 | d2 | d3 == 0) as core::ffi::c_int;
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2CircleToPoint(mut A: c2Circle, mut B: c2v)
            -> core::ffi::c_int {
            let mut n: c2v = c2Sub(A.p, B);
            let mut d2: core::ffi::c_float = c2Dot(n, n);
            return (d2 < A.r * A.r) as core::ffi::c_int;
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2RaytoCapsule(mut A: c2Ray,
            mut B: c2Capsule, mut out: *mut c2Raycast) -> core::ffi::c_int {
            let mut M: c2m =
                c2m { x: c2v { x: 0., y: 0. }, y: c2v { x: 0., y: 0. } };
            M.y = c2Norm(c2Sub(B.b, B.a));
            M.x = c2CCW90(M.y);
            let mut cap_n: c2v = c2Sub(B.b, B.a);
            let mut yBb: c2v = c2MulmvT(M, cap_n);
            let mut yAp: c2v = c2MulmvT(M, c2Sub(A.p, B.a));
            let mut yAd: c2v = c2MulmvT(M, A.d);
            let mut yAe: c2v = c2Add(yAp, c2Mulvs(yAd, A.t));
            let mut capsule_bb: c2AABB =
                c2AABB {
                    min: c2v { x: 0., y: 0. },
                    max: c2v { x: 0., y: 0. },
                };
            capsule_bb.min =
                c2V(-B.r, 0 as core::ffi::c_int as core::ffi::c_float);
            capsule_bb.max = c2V(B.r, yBb.y);
            (*out).n = c2Norm(cap_n);
            (*out).t = 0 as core::ffi::c_int as core::ffi::c_float;
            if c2AABBtoPoint(capsule_bb, yAp) != 0 {
                return 1 as core::ffi::c_int
            } else {
                let mut capsule_a: c2Circle =
                    c2Circle { p: c2v { x: 0., y: 0. }, r: 0. };
                let mut capsule_b: c2Circle =
                    c2Circle { p: c2v { x: 0., y: 0. }, r: 0. };
                capsule_a.p = B.a;
                capsule_a.r = B.r;
                capsule_b.p = B.b;
                capsule_b.r = B.r;
                if c2CircleToPoint(capsule_a, A.p) != 0 {
                    return 1 as core::ffi::c_int
                } else if c2CircleToPoint(capsule_b, A.p) != 0 {
                    return 1 as core::ffi::c_int
                }
            }
            if yAe.x * yAp.x < 0 as core::ffi::c_int as core::ffi::c_float ||
                    (if (if yAe.x < 0 as core::ffi::c_int as core::ffi::c_float
                                            {
                                            -yAe.x
                                        } else { yAe.x }) <
                                    (if yAp.x < 0 as core::ffi::c_int as core::ffi::c_float {
                                            -yAp.x
                                        } else { yAp.x }) {
                                (if yAe.x < 0 as core::ffi::c_int as core::ffi::c_float {
                                        -yAe.x
                                    } else { yAe.x })
                            } else {
                                (if yAp.x < 0 as core::ffi::c_int as core::ffi::c_float {
                                        -yAp.x
                                    } else { yAp.x })
                            }) < B.r {
                let mut Ca: c2Circle =
                    c2Circle { p: c2v { x: 0., y: 0. }, r: 0. };
                let mut Cb: c2Circle =
                    c2Circle { p: c2v { x: 0., y: 0. }, r: 0. };
                Ca.p = B.a;
                Ca.r = B.r;
                Cb.p = B.b;
                Cb.r = B.r;
                if (if yAp.x < 0 as core::ffi::c_int as core::ffi::c_float {
                                -yAp.x
                            } else { yAp.x }) < B.r {
                    if yAp.y < 0 as core::ffi::c_int as core::ffi::c_float {
                        return c2RaytoCircle(A, Ca, out)
                    } else { return c2RaytoCircle(A, Cb, out) }
                } else {
                    let mut c: core::ffi::c_float =
                        if yAp.x > 0 as core::ffi::c_int as core::ffi::c_float {
                            B.r
                        } else { -B.r };
                    let mut d: core::ffi::c_float = yAe.x - yAp.x;
                    let mut t: core::ffi::c_float = (c - yAp.x) / d;
                    let mut y: core::ffi::c_float = yAp.y + (yAe.y - yAp.y) * t;
                    if y <= 0 as core::ffi::c_int as core::ffi::c_float {
                        return c2RaytoCircle(A, Ca, out);
                    }
                    if y >= yBb.y {
                        return c2RaytoCircle(A, Cb, out)
                    } else {
                        (*out).n =
                            if c > 0 as core::ffi::c_int as core::ffi::c_float {
                                M.x
                            } else { c2Skew(M.y) };
                        (*out).t = t * A.t;
                        return 1 as core::ffi::c_int;
                    }
                }
            }
            return 0 as core::ffi::c_int;
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2CastRay(mut A: c2Ray,
            mut B: *const core::ffi::c_void, mut typeB: C2_TYPE,
            mut out: *mut c2Raycast) -> core::ffi::c_int {
            match typeB as core::ffi::c_uint {
                0 => return c2RaytoCircle(A, *(B as *mut c2Circle), out),
                1 => return c2RaytoAABB(A, *(B as *mut c2AABB), out),
                2 => return c2RaytoCapsule(A, *(B as *mut c2Capsule), out),
                _ => {}
            }
            {
                ::core::panicking::panic_fmt(format_args!("Reached end of non-void function without returning"));
            };
        }
        #[no_mangle]
        pub unsafe extern "C" fn gen_ray(mut cast1: *mut c2Raycast,
            mut cast2: *mut c2Raycast, mut cast3: *mut c2Raycast,
            mut mp_x: core::ffi::c_float, mut mp_y: core::ffi::c_float,
            mut r_p_x: core::ffi::c_float, mut r_p_y: core::ffi::c_float,
            mut c_p_x: core::ffi::c_float, mut c_p_y: core::ffi::c_float,
            mut c_r: core::ffi::c_float, mut cap_a_x: core::ffi::c_float,
            mut cap_a_y: core::ffi::c_float, mut cap_b_x: core::ffi::c_float,
            mut cap_b_y: core::ffi::c_float, mut cap_r: core::ffi::c_float,
            mut bb_min_x: core::ffi::c_float,
            mut bb_min_y: core::ffi::c_float,
            mut bb_max_x: core::ffi::c_float,
            mut bb_max_y: core::ffi::c_float) -> core::ffi::c_int {
            let mut hit: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut mp: c2v = c2V(mp_x, mp_y);
            let mut ray: c2Ray =
                c2Ray {
                    p: c2v { x: 0., y: 0. },
                    d: c2v { x: 0., y: 0. },
                    t: 0.,
                };
            ray.p = c2V(r_p_x, r_p_y);
            ray.d = c2Norm(c2Sub(mp, ray.p));
            ray.t = c2Dot(mp, ray.d) - c2Dot(ray.p, ray.d);
            let mut c: c2Circle = c2Circle { p: c2v { x: 0., y: 0. }, r: 0. };
            c.p = c2V(c_p_x, c_p_y);
            c.r = c_r;
            hit +=
                c2CastRay(ray,
                    &mut c as *mut c2Circle as *const core::ffi::c_void,
                    C2_TYPE_CIRCLE, cast1);
            let mut cap: c2Capsule =
                c2Capsule {
                    a: c2v { x: 0., y: 0. },
                    b: c2v { x: 0., y: 0. },
                    r: 0.,
                };
            cap.a = c2V(cap_a_x, cap_a_y);
            cap.b = c2V(cap_b_x, cap_b_y);
            cap.r = cap_r;
            hit +=
                c2CastRay(ray,
                        &mut cap as *mut c2Capsule as *const core::ffi::c_void,
                        C2_TYPE_CAPSULE, cast2) << 1 as core::ffi::c_int;
            let mut bb: c2AABB =
                c2AABB {
                    min: c2v { x: 0., y: 0. },
                    max: c2v { x: 0., y: 0. },
                };
            bb.min = c2V(bb_min_x, bb_min_y);
            bb.max = c2V(bb_max_x, bb_max_y);
            hit +=
                c2CastRay(ray,
                        &mut bb as *mut c2AABB as *const core::ffi::c_void,
                        C2_TYPE_AABB, cast3) << 2 as core::ffi::c_int;
            return hit;
        }
    }
}"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates("gen_ray_lib", SOURCE, &[], &[]);
}
