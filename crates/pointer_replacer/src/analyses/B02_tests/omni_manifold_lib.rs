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
            fn sqrtf(__x: core::ffi::c_float) -> core::ffi::c_float;
            fn malloc(__size: size_t) -> *mut core::ffi::c_void;
        }
        pub type C2_TYPE = core::ffi::c_uint;
        pub const C2_TYPE_POLY: C2_TYPE = 3;
        pub const C2_TYPE_AABB: C2_TYPE = 2;
        pub const C2_TYPE_CIRCLE: C2_TYPE = 1;
        pub const C2_TYPE_CAPSULE: C2_TYPE = 0;
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
        pub struct c2Manifold {
            pub count: core::ffi::c_int,
            pub depths: [core::ffi::c_float; 2],
            pub contact_points: [c2v; 2],
            pub n: c2v,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for c2Manifold {}
        #[automatically_derived]
        impl ::core::clone::Clone for c2Manifold {
            #[inline]
            fn clone(&self) -> c2Manifold {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_float; 2]>;
                let _: ::core::clone::AssertParamIsClone<[c2v; 2]>;
                let _: ::core::clone::AssertParamIsClone<c2v>;
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
        impl ::core::marker::Copy for c2Capsule {}
        #[automatically_derived]
        impl ::core::clone::Clone for c2Capsule {
            #[inline]
            fn clone(&self) -> c2Capsule {
                let _: ::core::clone::AssertParamIsClone<c2v>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_float>;
                *self
            }
        }
        pub type size_t = usize;
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
        #[repr(C)]
        pub struct c2GJKCache {
            pub metric: core::ffi::c_float,
            pub count: core::ffi::c_int,
            pub iA: [core::ffi::c_int; 3],
            pub iB: [core::ffi::c_int; 3],
            pub div: core::ffi::c_float,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for c2GJKCache {}
        #[automatically_derived]
        impl ::core::clone::Clone for c2GJKCache {
            #[inline]
            fn clone(&self) -> c2GJKCache {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_float>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_int; 3]>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_int; 3]>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_float>;
                *self
            }
        }
        #[repr(C)]
        pub struct c2x {
            pub p: c2v,
            pub r: c2r,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for c2x {}
        #[automatically_derived]
        impl ::core::clone::Clone for c2x {
            #[inline]
            fn clone(&self) -> c2x {
                let _: ::core::clone::AssertParamIsClone<c2v>;
                let _: ::core::clone::AssertParamIsClone<c2r>;
                *self
            }
        }
        #[repr(C)]
        pub struct c2r {
            pub c: core::ffi::c_float,
            pub s: core::ffi::c_float,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for c2r {}
        #[automatically_derived]
        impl ::core::clone::Clone for c2r {
            #[inline]
            fn clone(&self) -> c2r {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_float>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_float>;
                *self
            }
        }
        #[repr(C)]
        pub struct c2Simplex {
            pub a: c2sv,
            pub b: c2sv,
            pub c: c2sv,
            pub d: c2sv,
            pub div: core::ffi::c_float,
            pub count: core::ffi::c_int,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for c2Simplex {}
        #[automatically_derived]
        impl ::core::clone::Clone for c2Simplex {
            #[inline]
            fn clone(&self) -> c2Simplex {
                let _: ::core::clone::AssertParamIsClone<c2sv>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_float>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                *self
            }
        }
        #[repr(C)]
        pub struct c2sv {
            pub sA: c2v,
            pub sB: c2v,
            pub p: c2v,
            pub u: core::ffi::c_float,
            pub iA: core::ffi::c_int,
            pub iB: core::ffi::c_int,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for c2sv {}
        #[automatically_derived]
        impl ::core::clone::Clone for c2sv {
            #[inline]
            fn clone(&self) -> c2sv {
                let _: ::core::clone::AssertParamIsClone<c2v>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_float>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                *self
            }
        }
        #[repr(C)]
        pub struct c2Proxy {
            pub radius: core::ffi::c_float,
            pub count: core::ffi::c_int,
            pub verts: [c2v; 8],
        }
        #[automatically_derived]
        impl ::core::marker::Copy for c2Proxy {}
        #[automatically_derived]
        impl ::core::clone::Clone for c2Proxy {
            #[inline]
            fn clone(&self) -> c2Proxy {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_float>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<[c2v; 8]>;
                *self
            }
        }
        #[repr(C)]
        pub struct c2Poly {
            pub count: core::ffi::c_int,
            pub verts: [c2v; 8],
            pub norms: [c2v; 8],
        }
        #[automatically_derived]
        impl ::core::marker::Copy for c2Poly {}
        #[automatically_derived]
        impl ::core::clone::Clone for c2Poly {
            #[inline]
            fn clone(&self) -> c2Poly {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<[c2v; 8]>;
                let _: ::core::clone::AssertParamIsClone<[c2v; 8]>;
                *self
            }
        }
        #[repr(C)]
        pub struct c2h {
            pub n: c2v,
            pub d: core::ffi::c_float,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for c2h {}
        #[automatically_derived]
        impl ::core::clone::Clone for c2h {
            #[inline]
            fn clone(&self) -> c2h {
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
        pub unsafe extern "C" fn c2Mulvs(mut a: c2v, b: core::ffi::c_float) -> c2v {
            a.x *= b;
            a.y *= b;
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
        pub unsafe extern "C" fn c2Dist(h: c2h, p: c2v) -> core::ffi::c_float {
            c2Dot(h.n, p) - h.d
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2PlaneAt(p: *const c2Poly, i: core::ffi::c_int) -> c2h {
            let mut h: c2h = c2h {
                n: c2v { x: 0., y: 0. },
                d: 0.,
            };
            h.n = (*p).norms[i as usize];
            h.d = c2Dot((*p).norms[i as usize], (*p).verts[i as usize]);
            h
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2RotIdentity() -> c2r {
            let mut r: c2r = c2r { c: 0., s: 0. };
            r.c = 1.0f32;
            r.s = 0 as core::ffi::c_int as core::ffi::c_float;
            r
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2xIdentity() -> c2x {
            let mut x: c2x = c2x {
                p: c2v { x: 0., y: 0. },
                r: c2r { c: 0., s: 0. },
            };
            x.p = c2V(
                0 as core::ffi::c_int as core::ffi::c_float,
                0 as core::ffi::c_int as core::ffi::c_float,
            );
            x.r = c2RotIdentity();
            x
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2BBVerts(out: *mut c2v, bb: *mut c2AABB) {
            *out.offset(0 as core::ffi::c_int as isize) = (*bb).min;
            *out.offset(1 as core::ffi::c_int as isize) = c2V((*bb).max.x, (*bb).min.y);
            *out.offset(2 as core::ffi::c_int as isize) = (*bb).max;
            *out.offset(3 as core::ffi::c_int as isize) = c2V((*bb).min.x, (*bb).max.y);
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2MakeProxy(
            shape: *const core::ffi::c_void,
            type_0: C2_TYPE,
            p: *mut c2Proxy,
        ) {
            match type_0 as core::ffi::c_uint {
                1 => {
                    let c: *mut c2Circle = shape as *mut c2Circle;
                    (*p).radius = (*c).r;
                    (*p).count = 1 as core::ffi::c_int;
                    (*p).verts[0 as core::ffi::c_int as usize] = (*c).p;
                }
                2 => {
                    let bb: *mut c2AABB = shape as *mut c2AABB;
                    (*p).radius = 0 as core::ffi::c_int as core::ffi::c_float;
                    (*p).count = 4 as core::ffi::c_int;
                    c2BBVerts(((*p).verts).as_mut_ptr(), bb);
                }
                0 => {
                    let c_0: *mut c2Capsule = shape as *mut c2Capsule;
                    (*p).radius = (*c_0).r;
                    (*p).count = 2 as core::ffi::c_int;
                    (*p).verts[0 as core::ffi::c_int as usize] = (*c_0).a;
                    (*p).verts[1 as core::ffi::c_int as usize] = (*c_0).b;
                }
                _ => {}
            };
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Len(a: c2v) -> core::ffi::c_float {
            sqrtf(c2Dot(a, a))
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Det2(a: c2v, b: c2v) -> core::ffi::c_float {
            a.x * b.y - a.y * b.x
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2GJKSimplexMetric(s: *mut c2Simplex) -> core::ffi::c_float {
            match (*s).count {
                2 => c2Len(c2Sub((*s).b.p, (*s).a.p)),
                3 => c2Det2(c2Sub((*s).b.p, (*s).a.p), c2Sub((*s).c.p, (*s).a.p)),
                1 | _ => 0 as core::ffi::c_int as core::ffi::c_float,
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Mulrv(a: c2r, b: c2v) -> c2v {
            c2V(a.c * b.x - a.s * b.y, a.s * b.x + a.c * b.y)
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2MulrvT(a: c2r, b: c2v) -> c2v {
            c2V(a.c * b.x + a.s * b.y, -a.s * b.x + a.c * b.y)
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Add(mut a: c2v, b: c2v) -> c2v {
            a.x += b.x;
            a.y += b.y;
            a
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Mulxv(a: c2x, b: c2v) -> c2v {
            c2Add(c2Mulrv(a.r, b), a.p)
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2MulxvT(a: c2x, b: c2v) -> c2v {
            c2MulrvT(a.r, c2Sub(b, a.p))
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Intersect(
            a: c2v,
            b: c2v,
            da: core::ffi::c_float,
            db: core::ffi::c_float,
        ) -> c2v {
            c2Add(a, c2Mulvs(c2Sub(b, a), da / (da - db)))
        }
        unsafe extern "C" fn c2Clip(seg: *mut c2v, h: c2h) -> core::ffi::c_int {
            let mut out: [c2v; 2] = [c2v { x: 0., y: 0. }; 2];
            let mut sp: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut d0: core::ffi::c_float = 0.;
            let mut d1: core::ffi::c_float = 0.;
            d0 = c2Dist(h, *seg.offset(0 as core::ffi::c_int as isize));
            if d0 < 0 as core::ffi::c_int as core::ffi::c_float {
                let fresh0 = sp;
                sp += 1;
                out[fresh0 as usize] = *seg.offset(0 as core::ffi::c_int as isize);
            }
            d1 = c2Dist(h, *seg.offset(1 as core::ffi::c_int as isize));
            if d1 < 0 as core::ffi::c_int as core::ffi::c_float {
                let fresh1 = sp;
                sp += 1;
                out[fresh1 as usize] = *seg.offset(1 as core::ffi::c_int as isize);
            }
            if d0 == 0 as core::ffi::c_int as core::ffi::c_float
                && d1 == 0 as core::ffi::c_int as core::ffi::c_float
            {
                let fresh2 = sp;
                sp += 1;
                out[fresh2 as usize] = *seg.offset(0 as core::ffi::c_int as isize);
                let fresh3 = sp;
                sp += 1;
                out[fresh3 as usize] = *seg.offset(1 as core::ffi::c_int as isize);
            } else if d0 * d1 <= 0 as core::ffi::c_int as core::ffi::c_float {
                let fresh4 = sp;
                sp += 1;
                out[fresh4 as usize] = c2Intersect(
                    *seg.offset(0 as core::ffi::c_int as isize),
                    *seg.offset(1 as core::ffi::c_int as isize),
                    d0,
                    d1,
                );
            }
            *seg.offset(0 as core::ffi::c_int as isize) = out[0 as core::ffi::c_int as usize];
            *seg.offset(1 as core::ffi::c_int as isize) = out[1 as core::ffi::c_int as usize];
            sp
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Div(a: c2v, b: core::ffi::c_float) -> c2v {
            c2Mulvs(a, 1.0f32 / b)
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Norm(a: c2v) -> c2v {
            c2Div(a, c2Len(a))
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Neg(a: c2v) -> c2v {
            c2V(-a.x, -a.y)
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2CCW90(a: c2v) -> c2v {
            let mut b: c2v = c2v { x: 0., y: 0. };
            b.x = a.y;
            b.y = -a.x;
            b
        }
        unsafe extern "C" fn c2SidePlanes(
            seg: *mut c2v,
            ra: c2v,
            rb: c2v,
            h: *mut c2h,
        ) -> core::ffi::c_int {
            let in_0: c2v = c2Norm(c2Sub(rb, ra));
            let left: c2h = {
                c2h {
                    n: c2Neg(in_0),
                    d: c2Dot(c2Neg(in_0), ra),
                }
            };
            let right: c2h = {
                c2h {
                    n: in_0,
                    d: c2Dot(in_0, rb),
                }
            };
            if c2Clip(seg, left) < 2 as core::ffi::c_int {
                return 0 as core::ffi::c_int;
            }
            if c2Clip(seg, right) < 2 as core::ffi::c_int {
                return 0 as core::ffi::c_int;
            }
            if !h.is_null() {
                (*h).n = c2CCW90(in_0);
                (*h).d = c2Dot(c2CCW90(in_0), ra);
            }
            1 as core::ffi::c_int
        }
        unsafe extern "C" fn c2SidePlanesFromPoly(
            seg: *mut c2v,
            x: c2x,
            p: *const c2Poly,
            e: core::ffi::c_int,
            h: *mut c2h,
        ) -> core::ffi::c_int {
            let ra: c2v = c2Mulxv(x, (*p).verts[e as usize]);
            let rb: c2v = c2Mulxv(
                x,
                (*p).verts[(if e + 1 as core::ffi::c_int == (*p).count {
                    0 as core::ffi::c_int
                } else {
                    e + 1 as core::ffi::c_int
                }) as usize],
            );
            c2SidePlanes(seg, ra, rb, h)
        }
        #[no_mangle]
        pub unsafe extern "C" fn c22(s: *mut c2Simplex) {
            let a: c2v = (*s).a.p;
            let b: c2v = (*s).b.p;
            let u: core::ffi::c_float = c2Dot(b, c2Sub(b, a));
            let v: core::ffi::c_float = c2Dot(a, c2Sub(a, b));
            if v <= 0 as core::ffi::c_int as core::ffi::c_float {
                (*s).a.u = 1.0f32;
                (*s).div = 1.0f32;
                (*s).count = 1 as core::ffi::c_int;
            } else if u <= 0 as core::ffi::c_int as core::ffi::c_float {
                (*s).a = (*s).b;
                (*s).a.u = 1.0f32;
                (*s).div = 1.0f32;
                (*s).count = 1 as core::ffi::c_int;
            } else {
                (*s).a.u = u;
                (*s).b.u = v;
                (*s).div = u + v;
                (*s).count = 2 as core::ffi::c_int;
            };
        }
        #[no_mangle]
        pub unsafe extern "C" fn c23(s: *mut c2Simplex) {
            let a: c2v = (*s).a.p;
            let b: c2v = (*s).b.p;
            let c: c2v = (*s).c.p;
            let uAB: core::ffi::c_float = c2Dot(b, c2Sub(b, a));
            let vAB: core::ffi::c_float = c2Dot(a, c2Sub(a, b));
            let uBC: core::ffi::c_float = c2Dot(c, c2Sub(c, b));
            let vBC: core::ffi::c_float = c2Dot(b, c2Sub(b, c));
            let uCA: core::ffi::c_float = c2Dot(a, c2Sub(a, c));
            let vCA: core::ffi::c_float = c2Dot(c, c2Sub(c, a));
            let area: core::ffi::c_float = c2Det2(c2Sub(b, a), c2Sub(c, a));
            let uABC: core::ffi::c_float = c2Det2(b, c) * area;
            let vABC: core::ffi::c_float = c2Det2(c, a) * area;
            let wABC: core::ffi::c_float = c2Det2(a, b) * area;
            if vAB <= 0 as core::ffi::c_int as core::ffi::c_float
                && uCA <= 0 as core::ffi::c_int as core::ffi::c_float
            {
                (*s).a.u = 1.0f32;
                (*s).div = 1.0f32;
                (*s).count = 1 as core::ffi::c_int;
            } else if uAB <= 0 as core::ffi::c_int as core::ffi::c_float
                && vBC <= 0 as core::ffi::c_int as core::ffi::c_float
            {
                (*s).a = (*s).b;
                (*s).a.u = 1.0f32;
                (*s).div = 1.0f32;
                (*s).count = 1 as core::ffi::c_int;
            } else if uBC <= 0 as core::ffi::c_int as core::ffi::c_float
                && vCA <= 0 as core::ffi::c_int as core::ffi::c_float
            {
                (*s).a = (*s).c;
                (*s).a.u = 1.0f32;
                (*s).div = 1.0f32;
                (*s).count = 1 as core::ffi::c_int;
            } else if uAB > 0 as core::ffi::c_int as core::ffi::c_float
                && vAB > 0 as core::ffi::c_int as core::ffi::c_float
                && wABC <= 0 as core::ffi::c_int as core::ffi::c_float
            {
                (*s).a.u = uAB;
                (*s).b.u = vAB;
                (*s).div = uAB + vAB;
                (*s).count = 2 as core::ffi::c_int;
            } else if uBC > 0 as core::ffi::c_int as core::ffi::c_float
                && vBC > 0 as core::ffi::c_int as core::ffi::c_float
                && uABC <= 0 as core::ffi::c_int as core::ffi::c_float
            {
                (*s).a = (*s).b;
                (*s).b = (*s).c;
                (*s).a.u = uBC;
                (*s).b.u = vBC;
                (*s).div = uBC + vBC;
                (*s).count = 2 as core::ffi::c_int;
            } else if uCA > 0 as core::ffi::c_int as core::ffi::c_float
                && vCA > 0 as core::ffi::c_int as core::ffi::c_float
                && vABC <= 0 as core::ffi::c_int as core::ffi::c_float
            {
                (*s).b = (*s).a;
                (*s).a = (*s).c;
                (*s).a.u = uCA;
                (*s).b.u = vCA;
                (*s).div = uCA + vCA;
                (*s).count = 2 as core::ffi::c_int;
            } else {
                (*s).a.u = uABC;
                (*s).b.u = vABC;
                (*s).c.u = wABC;
                (*s).div = uABC + vABC + wABC;
                (*s).count = 3 as core::ffi::c_int;
            };
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Skew(a: c2v) -> c2v {
            let mut b: c2v = c2v { x: 0., y: 0. };
            b.x = -a.y;
            b.y = a.x;
            b
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2D(s: *mut c2Simplex) -> c2v {
            match (*s).count {
                1 => c2Neg((*s).a.p),
                2 => {
                    let ab: c2v = c2Sub((*s).b.p, (*s).a.p);
                    if c2Det2(ab, c2Neg((*s).a.p)) > 0 as core::ffi::c_int as core::ffi::c_float {
                        return c2Skew(ab);
                    }
                    c2CCW90(ab)
                }
                3 | _ => c2V(
                    0 as core::ffi::c_int as core::ffi::c_float,
                    0 as core::ffi::c_int as core::ffi::c_float,
                ),
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Support(
            verts: *const c2v,
            count: core::ffi::c_int,
            d: c2v,
        ) -> core::ffi::c_int {
            let mut imax: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut dmax: core::ffi::c_float =
                c2Dot(*verts.offset(0 as core::ffi::c_int as isize), d);
            let mut i: core::ffi::c_int = 1 as core::ffi::c_int;
            while i < count {
                let dot: core::ffi::c_float = c2Dot(*verts.offset(i as isize), d);
                if dot > dmax {
                    imax = i;
                    dmax = dot;
                }
                i += 1;
            }
            imax
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Witness(s: *mut c2Simplex, a: *mut c2v, b: *mut c2v) {
            let den: core::ffi::c_float = 1.0f32 / (*s).div;
            match (*s).count {
                1 => {
                    *a = (*s).a.sA;
                    *b = (*s).a.sB;
                }
                2 => {
                    *a = c2Add(
                        c2Mulvs((*s).a.sA, den * (*s).a.u),
                        c2Mulvs((*s).b.sA, den * (*s).b.u),
                    );
                    *b = c2Add(
                        c2Mulvs((*s).a.sB, den * (*s).a.u),
                        c2Mulvs((*s).b.sB, den * (*s).b.u),
                    );
                }
                3 => {
                    *a = c2Add(
                        c2Add(
                            c2Mulvs((*s).a.sA, den * (*s).a.u),
                            c2Mulvs((*s).b.sA, den * (*s).b.u),
                        ),
                        c2Mulvs((*s).c.sA, den * (*s).c.u),
                    );
                    *b = c2Add(
                        c2Add(
                            c2Mulvs((*s).a.sB, den * (*s).a.u),
                            c2Mulvs((*s).b.sB, den * (*s).b.u),
                        ),
                        c2Mulvs((*s).c.sB, den * (*s).c.u),
                    );
                }
                _ => {
                    *a = c2V(
                        0 as core::ffi::c_int as core::ffi::c_float,
                        0 as core::ffi::c_int as core::ffi::c_float,
                    );
                    *b = c2V(
                        0 as core::ffi::c_int as core::ffi::c_float,
                        0 as core::ffi::c_int as core::ffi::c_float,
                    );
                }
            };
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2L(s: *mut c2Simplex) -> c2v {
            let den: core::ffi::c_float = 1.0f32 / (*s).div;
            match (*s).count {
                1 => (*s).a.p,
                2 => c2Add(
                    c2Mulvs((*s).a.p, den * (*s).a.u),
                    c2Mulvs((*s).b.p, den * (*s).b.u),
                ),
                _ => c2V(
                    0 as core::ffi::c_int as core::ffi::c_float,
                    0 as core::ffi::c_int as core::ffi::c_float,
                ),
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2GJK(
            A: *const core::ffi::c_void,
            typeA: C2_TYPE,
            ax_ptr: *const c2x,
            B: *const core::ffi::c_void,
            typeB: C2_TYPE,
            bx_ptr: *const c2x,
            outA: *mut c2v,
            outB: *mut c2v,
            use_radius: core::ffi::c_int,
            iterations: *mut core::ffi::c_int,
            cache: *mut c2GJKCache,
        ) -> core::ffi::c_float {
            let mut ax: c2x = c2x {
                p: c2v { x: 0., y: 0. },
                r: c2r { c: 0., s: 0. },
            };
            let mut bx: c2x = c2x {
                p: c2v { x: 0., y: 0. },
                r: c2r { c: 0., s: 0. },
            };
            if ax_ptr.is_null() {
                ax = c2xIdentity();
            } else {
                ax = *ax_ptr;
            }
            if bx_ptr.is_null() {
                bx = c2xIdentity();
            } else {
                bx = *bx_ptr;
            }
            let mut pA: c2Proxy = c2Proxy {
                radius: 0.,
                count: 0,
                verts: [c2v { x: 0., y: 0. }; 8],
            };
            let mut pB: c2Proxy = c2Proxy {
                radius: 0.,
                count: 0,
                verts: [c2v { x: 0., y: 0. }; 8],
            };
            c2MakeProxy(A, typeA, &mut pA);
            c2MakeProxy(B, typeB, &mut pB);
            let mut s: c2Simplex = c2Simplex {
                a: c2sv {
                    sA: c2v { x: 0., y: 0. },
                    sB: c2v { x: 0., y: 0. },
                    p: c2v { x: 0., y: 0. },
                    u: 0.,
                    iA: 0,
                    iB: 0,
                },
                b: c2sv {
                    sA: c2v { x: 0., y: 0. },
                    sB: c2v { x: 0., y: 0. },
                    p: c2v { x: 0., y: 0. },
                    u: 0.,
                    iA: 0,
                    iB: 0,
                },
                c: c2sv {
                    sA: c2v { x: 0., y: 0. },
                    sB: c2v { x: 0., y: 0. },
                    p: c2v { x: 0., y: 0. },
                    u: 0.,
                    iA: 0,
                    iB: 0,
                },
                d: c2sv {
                    sA: c2v { x: 0., y: 0. },
                    sB: c2v { x: 0., y: 0. },
                    p: c2v { x: 0., y: 0. },
                    u: 0.,
                    iA: 0,
                    iB: 0,
                },
                div: 0.,
                count: 0,
            };
            let verts: *mut c2sv = &mut s.a;
            let mut cache_was_read: core::ffi::c_int = 0 as core::ffi::c_int;
            if !cache.is_null() {
                let cache_was_good: core::ffi::c_int = ((*cache).count != 0) as core::ffi::c_int;
                if cache_was_good != 0 {
                    let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
                    while i < (*cache).count {
                        let iA: core::ffi::c_int = (*cache).iA[i as usize];
                        let iB: core::ffi::c_int = (*cache).iB[i as usize];
                        let sA: c2v = c2Mulxv(ax, pA.verts[iA as usize]);
                        let sB: c2v = c2Mulxv(bx, pB.verts[iB as usize]);
                        let v: *mut c2sv = verts.offset(i as isize);
                        (*v).iA = iA;
                        (*v).sA = sA;
                        (*v).iB = iB;
                        (*v).sB = sB;
                        (*v).p = c2Sub((*v).sB, (*v).sA);
                        (*v).u = 0 as core::ffi::c_int as core::ffi::c_float;
                        i += 1;
                    }
                    s.count = (*cache).count;
                    s.div = (*cache).div;
                    let metric_old: core::ffi::c_float = (*cache).metric;
                    let metric: core::ffi::c_float = c2GJKSimplexMetric(&mut s);
                    let min_metric: core::ffi::c_float = if metric < metric_old {
                        metric
                    } else {
                        metric_old
                    };
                    let max_metric: core::ffi::c_float = if metric > metric_old {
                        metric
                    } else {
                        metric_old
                    };
                    if !(min_metric < max_metric * 2.0f32 && metric < -1.0e8f32) {
                        cache_was_read = 1 as core::ffi::c_int;
                    }
                }
            }
            if cache_was_read == 0 {
                s.a.iA = 0 as core::ffi::c_int;
                s.a.iB = 0 as core::ffi::c_int;
                s.a.sA = c2Mulxv(ax, pA.verts[0 as core::ffi::c_int as usize]);
                s.a.sB = c2Mulxv(bx, pB.verts[0 as core::ffi::c_int as usize]);
                s.a.p = c2Sub(s.a.sB, s.a.sA);
                s.a.u = 1.0f32;
                s.div = 1.0f32;
                s.count = 1 as core::ffi::c_int;
            }
            let mut saveA: [core::ffi::c_int; 3] = [0; 3];
            let mut saveB: [core::ffi::c_int; 3] = [0; 3];
            let mut save_count: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut d0: core::ffi::c_float = 3.402_823_5e38_f32;
            let mut d1: core::ffi::c_float = 3.402_823_5e38_f32;
            let mut iter: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut hit: core::ffi::c_int = 0 as core::ffi::c_int;
            while iter < 20 as core::ffi::c_int {
                save_count = s.count;
                let mut i_0: core::ffi::c_int = 0 as core::ffi::c_int;
                while i_0 < save_count {
                    saveA[i_0 as usize] = (*verts.offset(i_0 as isize)).iA;
                    saveB[i_0 as usize] = (*verts.offset(i_0 as isize)).iB;
                    i_0 += 1;
                }
                match s.count {
                    2 => {
                        c22(&mut s);
                    }
                    3 => {
                        c23(&mut s);
                    }
                    1 | _ => {}
                }
                if s.count == 3 as core::ffi::c_int {
                    hit = 1 as core::ffi::c_int;
                    break;
                } else {
                    let p: c2v = c2L(&mut s);
                    d1 = c2Dot(p, p);
                    if d1 > d0 {
                        break;
                    }
                    d0 = d1;
                    let d: c2v = c2D(&mut s);
                    if c2Dot(d, d) < 1.192_092_9e-7_f32 * 1.192_092_9e-7_f32 {
                        break;
                    }
                    let iA_0: core::ffi::c_int =
                        c2Support((pA.verts).as_ptr(), pA.count, c2MulrvT(ax.r, c2Neg(d)));
                    let sA_0: c2v = c2Mulxv(ax, pA.verts[iA_0 as usize]);
                    let iB_0: core::ffi::c_int =
                        c2Support((pB.verts).as_ptr(), pB.count, c2MulrvT(bx.r, d));
                    let sB_0: c2v = c2Mulxv(bx, pB.verts[iB_0 as usize]);
                    let v_0: *mut c2sv = verts.offset(s.count as isize);
                    (*v_0).iA = iA_0;
                    (*v_0).sA = sA_0;
                    (*v_0).iB = iB_0;
                    (*v_0).sB = sB_0;
                    (*v_0).p = c2Sub((*v_0).sB, (*v_0).sA);
                    let mut dup: core::ffi::c_int = 0 as core::ffi::c_int;
                    let mut i_1: core::ffi::c_int = 0 as core::ffi::c_int;
                    while i_1 < save_count {
                        if iA_0 == saveA[i_1 as usize] && iB_0 == saveB[i_1 as usize] {
                            dup = 1 as core::ffi::c_int;
                            break;
                        } else {
                            i_1 += 1;
                        }
                    }
                    if dup != 0 {
                        break;
                    }
                    s.count += 1;
                    iter += 1;
                }
            }
            let mut a: c2v = c2v { x: 0., y: 0. };
            let mut b: c2v = c2v { x: 0., y: 0. };
            c2Witness(&mut s, &mut a, &mut b);
            let mut dist: core::ffi::c_float = c2Len(c2Sub(a, b));
            if hit != 0 {
                a = b;
                dist = 0 as core::ffi::c_int as core::ffi::c_float;
            } else if use_radius != 0 {
                let rA: core::ffi::c_float = pA.radius;
                let rB: core::ffi::c_float = pB.radius;
                if dist > rA + rB && dist > 1.192_092_9e-7_f32 {
                    dist -= rA + rB;
                    let n: c2v = c2Norm(c2Sub(b, a));
                    a = c2Add(a, c2Mulvs(n, rA));
                    b = c2Sub(b, c2Mulvs(n, rB));
                    if a.x == b.x && a.y == b.y {
                        dist = 0 as core::ffi::c_int as core::ffi::c_float;
                    }
                } else {
                    let p_0: c2v = c2Mulvs(c2Add(a, b), 0.5f32);
                    a = p_0;
                    b = p_0;
                    dist = 0 as core::ffi::c_int as core::ffi::c_float;
                }
            }
            if !cache.is_null() {
                (*cache).metric = c2GJKSimplexMetric(&mut s);
                (*cache).count = s.count;
                let mut i_2: core::ffi::c_int = 0 as core::ffi::c_int;
                while i_2 < s.count {
                    let v_1: *mut c2sv = verts.offset(i_2 as isize);
                    (*cache).iA[i_2 as usize] = (*v_1).iA;
                    (*cache).iB[i_2 as usize] = (*v_1).iB;
                    i_2 += 1;
                }
                (*cache).div = s.div;
            }
            if !outA.is_null() {
                *outA = a;
            }
            if !outB.is_null() {
                *outB = b;
            }
            if !iterations.is_null() {
                *iterations = iter;
            }
            dist
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Absv(a: c2v) -> c2v {
            c2V(
                if a.x < 0 as core::ffi::c_int as core::ffi::c_float {
                    -a.x
                } else {
                    a.x
                },
                if a.y < 0 as core::ffi::c_int as core::ffi::c_float {
                    -a.y
                } else {
                    a.y
                },
            )
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2CircletoCircleManifold(
            A: c2Circle,
            B: c2Circle,
            m: *mut c2Manifold,
        ) {
            (*m).count = 0 as core::ffi::c_int;
            let d: c2v = c2Sub(B.p, A.p);
            let d2: core::ffi::c_float = c2Dot(d, d);
            let r: core::ffi::c_float = A.r + B.r;
            if d2 < r * r {
                let l: core::ffi::c_float = sqrtf(d2);
                let n: c2v = if l != 0 as core::ffi::c_int as core::ffi::c_float {
                    c2Mulvs(d, 1.0f32 / l)
                } else {
                    c2V(0 as core::ffi::c_int as core::ffi::c_float, 1.0f32)
                };
                (*m).count = 1 as core::ffi::c_int;
                (*m).depths[0 as core::ffi::c_int as usize] = r - l;
                (*m).contact_points[0 as core::ffi::c_int as usize] = c2Sub(B.p, c2Mulvs(n, B.r));
                (*m).n = n;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2CircletoAABBManifold(
            A: c2Circle,
            B: c2AABB,
            m: *mut c2Manifold,
        ) {
            (*m).count = 0 as core::ffi::c_int;
            let L: c2v = c2Clampv(A.p, B.min, B.max);
            let ab: c2v = c2Sub(L, A.p);
            let d2: core::ffi::c_float = c2Dot(ab, ab);
            let r2: core::ffi::c_float = A.r * A.r;
            if d2 < r2 {
                if d2 != 0 as core::ffi::c_int as core::ffi::c_float {
                    let d: core::ffi::c_float = sqrtf(d2);
                    let n: c2v = c2Norm(ab);
                    (*m).count = 1 as core::ffi::c_int;
                    (*m).depths[0 as core::ffi::c_int as usize] = A.r - d;
                    (*m).contact_points[0 as core::ffi::c_int as usize] = c2Add(A.p, c2Mulvs(n, d));
                    (*m).n = n;
                } else {
                    let mid: c2v = c2Mulvs(c2Add(B.min, B.max), 0.5f32);
                    let e: c2v = c2Mulvs(c2Sub(B.max, B.min), 0.5f32);
                    let d_0: c2v = c2Sub(A.p, mid);
                    let abs_d: c2v = c2Absv(d_0);
                    let x_overlap: core::ffi::c_float = e.x - abs_d.x;
                    let y_overlap: core::ffi::c_float = e.y - abs_d.y;
                    let mut depth: core::ffi::c_float = 0.;
                    let mut n_0: c2v = c2v { x: 0., y: 0. };
                    if x_overlap < y_overlap {
                        depth = x_overlap;
                        n_0 = c2V(1.0f32, 0 as core::ffi::c_int as core::ffi::c_float);
                        n_0 = c2Mulvs(
                            n_0,
                            if d_0.x < 0 as core::ffi::c_int as core::ffi::c_float {
                                1.0f32
                            } else {
                                -1.0f32
                            },
                        );
                    } else {
                        depth = y_overlap;
                        n_0 = c2V(0 as core::ffi::c_int as core::ffi::c_float, 1.0f32);
                        n_0 = c2Mulvs(
                            n_0,
                            if d_0.y < 0 as core::ffi::c_int as core::ffi::c_float {
                                1.0f32
                            } else {
                                -1.0f32
                            },
                        );
                    }
                    (*m).count = 1 as core::ffi::c_int;
                    (*m).depths[0 as core::ffi::c_int as usize] = A.r + depth;
                    (*m).contact_points[0 as core::ffi::c_int as usize] =
                        c2Sub(A.p, c2Mulvs(n_0, depth));
                    (*m).n = n_0;
                }
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2CircletoCapsuleManifold(
            mut A: c2Circle,
            mut B: c2Capsule,
            m: *mut c2Manifold,
        ) {
            (*m).count = 0 as core::ffi::c_int;
            let mut a: c2v = c2v { x: 0., y: 0. };
            let mut b: c2v = c2v { x: 0., y: 0. };
            let r: core::ffi::c_float = A.r + B.r;
            let d: core::ffi::c_float = c2GJK(
                &mut A as *mut c2Circle as *const core::ffi::c_void,
                C2_TYPE_CIRCLE,
                std::ptr::null::<c2x>(),
                &mut B as *mut c2Capsule as *const core::ffi::c_void,
                C2_TYPE_CAPSULE,
                std::ptr::null::<c2x>(),
                &mut a,
                &mut b,
                0 as core::ffi::c_int,
                std::ptr::null_mut::<core::ffi::c_int>(),
                std::ptr::null_mut::<c2GJKCache>(),
            );
            if d < r {
                let mut n: c2v = c2v { x: 0., y: 0. };
                if d == 0 as core::ffi::c_int as core::ffi::c_float {
                    n = c2Norm(c2Skew(c2Sub(B.b, B.a)));
                } else {
                    n = c2Norm(c2Sub(b, a));
                }
                (*m).count = 1 as core::ffi::c_int;
                (*m).depths[0 as core::ffi::c_int as usize] = r - d;
                (*m).contact_points[0 as core::ffi::c_int as usize] = c2Sub(b, c2Mulvs(n, B.r));
                (*m).n = n;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2AABBtoAABBManifold(A: c2AABB, B: c2AABB, m: *mut c2Manifold) {
            (*m).count = 0 as core::ffi::c_int;
            let mid_a: c2v = c2Mulvs(c2Add(A.min, A.max), 0.5f32);
            let mid_b: c2v = c2Mulvs(c2Add(B.min, B.max), 0.5f32);
            let eA: c2v = c2Absv(c2Mulvs(c2Sub(A.max, A.min), 0.5f32));
            let eB: c2v = c2Absv(c2Mulvs(c2Sub(B.max, B.min), 0.5f32));
            let d: c2v = c2Sub(mid_b, mid_a);
            let dx: core::ffi::c_float = eA.x + eB.x
                - (if d.x < 0 as core::ffi::c_int as core::ffi::c_float {
                    -d.x
                } else {
                    d.x
                });
            if dx < 0 as core::ffi::c_int as core::ffi::c_float {
                return;
            }
            let dy: core::ffi::c_float = eA.y + eB.y
                - (if d.y < 0 as core::ffi::c_int as core::ffi::c_float {
                    -d.y
                } else {
                    d.y
                });
            if dy < 0 as core::ffi::c_int as core::ffi::c_float {
                return;
            }
            let mut n: c2v = c2v { x: 0., y: 0. };
            let mut depth: core::ffi::c_float = 0.;
            let mut p: c2v = c2v { x: 0., y: 0. };
            if dx < dy {
                depth = dx;
                if d.x < 0 as core::ffi::c_int as core::ffi::c_float {
                    n = c2V(-1.0f32, 0 as core::ffi::c_int as core::ffi::c_float);
                    p = c2Sub(
                        mid_a,
                        c2V(eA.x, 0 as core::ffi::c_int as core::ffi::c_float),
                    );
                } else {
                    n = c2V(1.0f32, 0 as core::ffi::c_int as core::ffi::c_float);
                    p = c2Add(
                        mid_a,
                        c2V(eA.x, 0 as core::ffi::c_int as core::ffi::c_float),
                    );
                }
            } else {
                depth = dy;
                if d.y < 0 as core::ffi::c_int as core::ffi::c_float {
                    n = c2V(0 as core::ffi::c_int as core::ffi::c_float, -1.0f32);
                    p = c2Sub(
                        mid_a,
                        c2V(0 as core::ffi::c_int as core::ffi::c_float, eA.y),
                    );
                } else {
                    n = c2V(0 as core::ffi::c_int as core::ffi::c_float, 1.0f32);
                    p = c2Add(
                        mid_a,
                        c2V(0 as core::ffi::c_int as core::ffi::c_float, eA.y),
                    );
                }
            }
            (*m).count = 1 as core::ffi::c_int;
            (*m).contact_points[0 as core::ffi::c_int as usize] = p;
            (*m).depths[0 as core::ffi::c_int as usize] = depth;
            (*m).n = n;
        }
        unsafe extern "C" fn c2KeepDeep(seg: *mut c2v, h: c2h, m: *mut c2Manifold) {
            let mut cp: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < 2 as core::ffi::c_int {
                let p: c2v = *seg.offset(i as isize);
                let d: core::ffi::c_float = c2Dist(h, p);
                if d <= 0 as core::ffi::c_int as core::ffi::c_float {
                    (*m).contact_points[cp as usize] = p;
                    (*m).depths[cp as usize] = -d;
                    cp += 1;
                }
                i += 1;
            }
            (*m).count = cp;
            (*m).n = h.n;
        }
        unsafe extern "C" fn c2Incident(
            incident: *mut c2v,
            ip: *const c2Poly,
            ix: c2x,
            rn_in_incident_space: c2v,
        ) {
            let mut index: core::ffi::c_int = !(0 as core::ffi::c_int);
            let mut min_dot: core::ffi::c_float = 3.402_823_5e38_f32;
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < (*ip).count {
                let dot: core::ffi::c_float = c2Dot(rn_in_incident_space, (*ip).norms[i as usize]);
                if dot < min_dot {
                    min_dot = dot;
                    index = i;
                }
                i += 1;
            }
            *incident.offset(0 as core::ffi::c_int as isize) =
                c2Mulxv(ix, (*ip).verts[index as usize]);
            *incident.offset(1 as core::ffi::c_int as isize) = c2Mulxv(
                ix,
                (*ip).verts[(if index + 1 as core::ffi::c_int == (*ip).count {
                    0 as core::ffi::c_int
                } else {
                    index + 1 as core::ffi::c_int
                }) as usize],
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2CapsuletoPolyManifold(
            mut A: c2Capsule,
            B: *const c2Poly,
            bx_ptr: *const c2x,
            m: *mut c2Manifold,
        ) {
            (*m).count = 0 as core::ffi::c_int;
            let mut a: c2v = c2v { x: 0., y: 0. };
            let mut b: c2v = c2v { x: 0., y: 0. };
            let d: core::ffi::c_float = c2GJK(
                &mut A as *mut c2Capsule as *const core::ffi::c_void,
                C2_TYPE_CAPSULE,
                std::ptr::null::<c2x>(),
                B as *const core::ffi::c_void,
                C2_TYPE_POLY,
                bx_ptr,
                &mut a,
                &mut b,
                0 as core::ffi::c_int,
                std::ptr::null_mut::<core::ffi::c_int>(),
                std::ptr::null_mut::<c2GJKCache>(),
            );
            if d < 1.0e-6f32 {
                let bx: c2x = if !bx_ptr.is_null() {
                    *bx_ptr
                } else {
                    c2xIdentity()
                };
                let mut A_in_B: c2Capsule = c2Capsule {
                    a: c2v { x: 0., y: 0. },
                    b: c2v { x: 0., y: 0. },
                    r: 0.,
                };
                A_in_B.a = c2MulxvT(bx, A.a);
                A_in_B.b = c2MulxvT(bx, A.b);
                let ab: c2v = c2Norm(c2Sub(A_in_B.a, A_in_B.b));
                let mut ab_h0: c2h = c2h {
                    n: c2v { x: 0., y: 0. },
                    d: 0.,
                };
                ab_h0.n = c2CCW90(ab);
                ab_h0.d = c2Dot(A_in_B.a, ab_h0.n);
                let v0: core::ffi::c_int =
                    c2Support(((*B).verts).as_ptr(), (*B).count, c2Neg(ab_h0.n));
                let s0: core::ffi::c_float = c2Dist(ab_h0, (*B).verts[v0 as usize]);
                let mut ab_h1: c2h = c2h {
                    n: c2v { x: 0., y: 0. },
                    d: 0.,
                };
                ab_h1.n = c2Skew(ab);
                ab_h1.d = c2Dot(A_in_B.a, ab_h1.n);
                let v1: core::ffi::c_int =
                    c2Support(((*B).verts).as_ptr(), (*B).count, c2Neg(ab_h1.n));
                let s1: core::ffi::c_float = c2Dist(ab_h1, (*B).verts[v1 as usize]);
                let mut index: core::ffi::c_int = !(0 as core::ffi::c_int);
                let mut sep: core::ffi::c_float = -3.402_823_5e38_f32;
                let mut code: core::ffi::c_int = 0 as core::ffi::c_int;
                let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
                while i < (*B).count {
                    let h: c2h = c2PlaneAt(B, i);
                    let da: core::ffi::c_float = c2Dot(A_in_B.a, c2Neg(h.n));
                    let db: core::ffi::c_float = c2Dot(A_in_B.b, c2Neg(h.n));
                    let mut d_0: core::ffi::c_float = 0.;
                    if da > db {
                        d_0 = c2Dist(h, A_in_B.a);
                    } else {
                        d_0 = c2Dist(h, A_in_B.b);
                    }
                    if d_0 > sep {
                        sep = d_0;
                        index = i;
                    }
                    i += 1;
                }
                if s0 > sep {
                    sep = s0;
                    index = v0;
                    code = 1 as core::ffi::c_int;
                }
                if s1 > sep {
                    sep = s1;
                    index = v1;
                    code = 2 as core::ffi::c_int;
                }
                match code {
                    0 => {
                        let mut seg: [c2v; 2] = [A.a, A.b];
                        let mut h_0: c2h = c2h {
                            n: c2v { x: 0., y: 0. },
                            d: 0.,
                        };
                        if c2SidePlanesFromPoly(seg.as_mut_ptr(), bx, B, index, &mut h_0) == 0 {
                            return;
                        }
                        c2KeepDeep(seg.as_mut_ptr(), h_0, m);
                        (*m).n = c2Neg((*m).n);
                    }
                    1 => {
                        let mut incident: [c2v; 2] = [c2v { x: 0., y: 0. }; 2];
                        c2Incident(incident.as_mut_ptr(), B, bx, ab_h0.n);
                        let mut h_1: c2h = c2h {
                            n: c2v { x: 0., y: 0. },
                            d: 0.,
                        };
                        if c2SidePlanes(incident.as_mut_ptr(), A_in_B.b, A_in_B.a, &mut h_1) == 0 {
                            return;
                        }
                        c2KeepDeep(incident.as_mut_ptr(), h_1, m);
                    }
                    2 => {
                        let mut incident_0: [c2v; 2] = [c2v { x: 0., y: 0. }; 2];
                        c2Incident(incident_0.as_mut_ptr(), B, bx, ab_h1.n);
                        let mut h_2: c2h = c2h {
                            n: c2v { x: 0., y: 0. },
                            d: 0.,
                        };
                        if c2SidePlanes(incident_0.as_mut_ptr(), A_in_B.a, A_in_B.b, &mut h_2) == 0
                        {
                            return;
                        }
                        c2KeepDeep(incident_0.as_mut_ptr(), h_2, m);
                    }
                    _ => return,
                }
                let mut i_0: core::ffi::c_int = 0 as core::ffi::c_int;
                while i_0 < (*m).count {
                    (*m).depths[i_0 as usize] += A.r;
                    i_0 += 1;
                }
            } else if d < A.r {
                (*m).count = 1 as core::ffi::c_int;
                (*m).n = c2Norm(c2Sub(b, a));
                (*m).contact_points[0 as core::ffi::c_int as usize] =
                    c2Add(a, c2Mulvs((*m).n, A.r));
                (*m).depths[0 as core::ffi::c_int as usize] = A.r - d;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Norms(
            verts: *mut c2v,
            norms: *mut c2v,
            count: core::ffi::c_int,
        ) {
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < count {
                let a: core::ffi::c_int = i;
                let b: core::ffi::c_int = if (i + 1 as core::ffi::c_int) < count {
                    i + 1 as core::ffi::c_int
                } else {
                    0 as core::ffi::c_int
                };
                let e: c2v = c2Sub(*verts.offset(b as isize), *verts.offset(a as isize));
                *norms.offset(i as isize) = c2Norm(c2CCW90(e));
                i += 1;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2AABBtoCapsuleManifold(
            mut A: c2AABB,
            B: c2Capsule,
            m: *mut c2Manifold,
        ) {
            (*m).count = 0 as core::ffi::c_int;
            let mut p: c2Poly = c2Poly {
                count: 0,
                verts: [c2v { x: 0., y: 0. }; 8],
                norms: [c2v { x: 0., y: 0. }; 8],
            };
            c2BBVerts((p.verts).as_mut_ptr(), &mut A);
            p.count = 4 as core::ffi::c_int;
            c2Norms(
                (p.verts).as_mut_ptr(),
                (p.norms).as_mut_ptr(),
                4 as core::ffi::c_int,
            );
            c2CapsuletoPolyManifold(B, &mut p, std::ptr::null::<c2x>(), m);
            (*m).n = c2Neg((*m).n);
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2CapsuletoCapsuleManifold(
            mut A: c2Capsule,
            mut B: c2Capsule,
            m: *mut c2Manifold,
        ) {
            (*m).count = 0 as core::ffi::c_int;
            let mut a: c2v = c2v { x: 0., y: 0. };
            let mut b: c2v = c2v { x: 0., y: 0. };
            let r: core::ffi::c_float = A.r + B.r;
            let d: core::ffi::c_float = c2GJK(
                &mut A as *mut c2Capsule as *const core::ffi::c_void,
                C2_TYPE_CAPSULE,
                std::ptr::null::<c2x>(),
                &mut B as *mut c2Capsule as *const core::ffi::c_void,
                C2_TYPE_CAPSULE,
                std::ptr::null::<c2x>(),
                &mut a,
                &mut b,
                0 as core::ffi::c_int,
                std::ptr::null_mut::<core::ffi::c_int>(),
                std::ptr::null_mut::<c2GJKCache>(),
            );
            if d < r {
                let mut n: c2v = c2v { x: 0., y: 0. };
                if d == 0 as core::ffi::c_int as core::ffi::c_float {
                    n = c2Norm(c2Skew(c2Sub(A.b, A.a)));
                } else {
                    n = c2Norm(c2Sub(b, a));
                }
                (*m).count = 1 as core::ffi::c_int;
                (*m).depths[0 as core::ffi::c_int as usize] = r - d;
                (*m).contact_points[0 as core::ffi::c_int as usize] = c2Sub(b, c2Mulvs(n, B.r));
                (*m).n = n;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Collide(
            A: *const core::ffi::c_void,
            typeA: C2_TYPE,
            B: *const core::ffi::c_void,
            typeB: C2_TYPE,
            m: *mut c2Manifold,
        ) {
            (*m).count = 0 as core::ffi::c_int;
            match typeA as core::ffi::c_uint {
                1 => match typeB as core::ffi::c_uint {
                    1 => {
                        c2CircletoCircleManifold(*(A as *mut c2Circle), *(B as *mut c2Circle), m);
                    }
                    2 => {
                        c2CircletoAABBManifold(*(A as *mut c2Circle), *(B as *mut c2AABB), m);
                    }
                    0 => {
                        c2CircletoCapsuleManifold(*(A as *mut c2Circle), *(B as *mut c2Capsule), m);
                    }
                    _ => {}
                },
                2 => match typeB as core::ffi::c_uint {
                    1 => {
                        c2CircletoAABBManifold(*(B as *mut c2Circle), *(A as *mut c2AABB), m);
                        (*m).n = c2Neg((*m).n);
                    }
                    2 => {
                        c2AABBtoAABBManifold(*(A as *mut c2AABB), *(B as *mut c2AABB), m);
                    }
                    0 => {
                        c2AABBtoCapsuleManifold(*(A as *mut c2AABB), *(B as *mut c2Capsule), m);
                    }
                    _ => {}
                },
                0 => match typeB as core::ffi::c_uint {
                    1 => {
                        c2CircletoCapsuleManifold(*(B as *mut c2Circle), *(A as *mut c2Capsule), m);
                        (*m).n = c2Neg((*m).n);
                    }
                    2 => {
                        c2AABBtoCapsuleManifold(*(B as *mut c2AABB), *(A as *mut c2Capsule), m);
                        (*m).n = c2Neg((*m).n);
                    }
                    0 => {
                        c2CapsuletoCapsuleManifold(
                            *(A as *mut c2Capsule),
                            *(B as *mut c2Capsule),
                            m,
                        );
                    }
                    _ => {}
                },
                _ => {}
            };
        }
        #[no_mangle]
        pub unsafe extern "C" fn ptr_from_parts(
            typ: C2_TYPE,
            a: core::ffi::c_float,
            b: core::ffi::c_float,
            c: core::ffi::c_float,
            d: core::ffi::c_float,
            e: core::ffi::c_float,
        ) -> *mut core::ffi::c_void {
            let mut circle: *mut c2Circle = std::ptr::null_mut::<c2Circle>();
            let mut aabb: *mut c2AABB = std::ptr::null_mut::<c2AABB>();
            let mut capsule: *mut c2Capsule = std::ptr::null_mut::<c2Capsule>();
            match typ as core::ffi::c_uint {
                1 => {
                    circle = malloc(::core::mem::size_of::<c2Circle>() as size_t) as *mut c2Circle;
                    (*circle).p = c2V(a, b);
                    (*circle).r = c;
                    return circle as *mut core::ffi::c_void;
                }
                2 => {
                    aabb = malloc(::core::mem::size_of::<c2AABB>() as size_t) as *mut c2AABB;
                    (*aabb).min = c2V(a, b);
                    (*aabb).max = c2V(c, d);
                    return aabb as *mut core::ffi::c_void;
                }
                0 => {
                    capsule =
                        malloc(::core::mem::size_of::<c2Capsule>() as size_t) as *mut c2Capsule;
                    (*capsule).a = c2V(a, b);
                    (*capsule).b = c2V(c, d);
                    (*capsule).r = e;
                    return capsule as *mut core::ffi::c_void;
                }
                _ => {}
            }
            {
                ::core::panicking::panic_fmt(format_args!(
                    "Reached end of non-void function without returning"
                ));
            };
        }
        #[no_mangle]
        pub unsafe extern "C" fn omni_manifold(
            m: *mut c2Manifold,
            type_a: C2_TYPE,
            a1: core::ffi::c_float,
            a2: core::ffi::c_float,
            a3: core::ffi::c_float,
            a4: core::ffi::c_float,
            a5: core::ffi::c_float,
            type_b: C2_TYPE,
            b1: core::ffi::c_float,
            b2: core::ffi::c_float,
            b3: core::ffi::c_float,
            b4: core::ffi::c_float,
            b5: core::ffi::c_float,
        ) {
            let A: *mut core::ffi::c_void = ptr_from_parts(type_a, a1, a2, a3, a4, a5);
            let B: *mut core::ffi::c_void = ptr_from_parts(type_b, b1, b2, b3, b4, b5);
            c2Collide(A, type_a, B, type_b, m);
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates("omni_manifold_lib", SOURCE, &[], &[]);
}
