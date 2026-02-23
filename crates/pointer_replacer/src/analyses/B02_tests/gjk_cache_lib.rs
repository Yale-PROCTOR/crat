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
        }
        pub type C2_TYPE = core::ffi::c_uint;
        pub const C2_TYPE_CAPSULE: C2_TYPE = 2;
        pub const C2_TYPE_AABB: C2_TYPE = 1;
        pub const C2_TYPE_CIRCLE: C2_TYPE = 0;
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
                0 => {
                    let c: *mut c2Circle = shape as *mut c2Circle;
                    (*p).radius = (*c).r;
                    (*p).count = 1 as core::ffi::c_int;
                    (*p).verts[0 as core::ffi::c_int as usize] = (*c).p;
                }
                1 => {
                    let bb: *mut c2AABB = shape as *mut c2AABB;
                    (*p).radius = 0 as core::ffi::c_int as core::ffi::c_float;
                    (*p).count = 4 as core::ffi::c_int;
                    c2BBVerts(((*p).verts).as_mut_ptr(), bb);
                }
                2 => {
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
        pub unsafe extern "C" fn c2Neg(a: c2v) -> c2v {
            c2V(-a.x, -a.y)
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Skew(a: c2v) -> c2v {
            let mut b: c2v = c2v { x: 0., y: 0. };
            b.x = -a.y;
            b.y = a.x;
            b
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2CCW90(a: c2v) -> c2v {
            let mut b: c2v = c2v { x: 0., y: 0. };
            b.x = a.y;
            b.y = -a.x;
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
        pub unsafe extern "C" fn c2Div(a: c2v, b: core::ffi::c_float) -> c2v {
            c2Mulvs(a, 1.0f32 / b)
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Norm(a: c2v) -> c2v {
            c2Div(a, c2Len(a))
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
        pub unsafe extern "C" fn c2MulrvT(a: c2r, b: c2v) -> c2v {
            c2V(a.c * b.x + a.s * b.y, -a.s * b.x + a.c * b.y)
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
        pub unsafe extern "C" fn gjk_cache(
            reverse: core::ffi::c_char,
            a9: *mut c2v,
            b9: *mut c2v,
            a1: core::ffi::c_float,
            a2: core::ffi::c_float,
            a3: core::ffi::c_float,
            a4: core::ffi::c_float,
            b1: core::ffi::c_float,
            b2: core::ffi::c_float,
            b3: core::ffi::c_float,
            b4: core::ffi::c_float,
            b5: core::ffi::c_float,
        ) {
            let mut cache: c2GJKCache = c2GJKCache {
                metric: 0.,
                count: 0,
                iA: [0; 3],
                iB: [0; 3],
                div: 0.,
            };
            cache.count = 0 as core::ffi::c_int;
            let mut A: c2Circle = {
                c2Circle {
                    p: {
                        c2v {
                            x: 0 as core::ffi::c_int as core::ffi::c_float,
                            y: 0 as core::ffi::c_int as core::ffi::c_float,
                        }
                    },
                    r: 15.0f32,
                }
            };
            let mut B: c2Capsule = {
                c2Capsule {
                    a: {
                        c2v {
                            x: 100 as core::ffi::c_int as core::ffi::c_float,
                            y: -(25 as core::ffi::c_int) as core::ffi::c_float,
                        }
                    },
                    b: {
                        c2v {
                            x: 75 as core::ffi::c_int as core::ffi::c_float,
                            y: 100 as core::ffi::c_int as core::ffi::c_float,
                        }
                    },
                    r: 10 as core::ffi::c_int as core::ffi::c_float,
                }
            };
            let mut a0: c2v = c2v { x: 0., y: 0. };
            let mut b0: c2v = c2v { x: 0., y: 0. };
            let mut a: c2v = c2v { x: 0., y: 0. };
            let mut b: c2v = c2v { x: 0., y: 0. };
            let mut iterations: core::ffi::c_int = -(1 as core::ffi::c_int);
            let mut cached_iterations: core::ffi::c_int = -(1 as core::ffi::c_int);
            let d0: core::ffi::c_float = c2GJK(
                &mut A as *mut c2Circle as *const core::ffi::c_void,
                C2_TYPE_CIRCLE,
                std::ptr::null::<c2x>(),
                &mut B as *mut c2Capsule as *const core::ffi::c_void,
                C2_TYPE_CAPSULE,
                std::ptr::null::<c2x>(),
                &mut a0,
                &mut b0,
                1 as core::ffi::c_int,
                &mut iterations,
                &mut cache,
            );
            let d1: core::ffi::c_float = c2GJK(
                &mut A as *mut c2Circle as *const core::ffi::c_void,
                C2_TYPE_CIRCLE,
                std::ptr::null::<c2x>(),
                &mut B as *mut c2Capsule as *const core::ffi::c_void,
                C2_TYPE_CAPSULE,
                std::ptr::null::<c2x>(),
                &mut a,
                &mut b,
                1 as core::ffi::c_int,
                &mut cached_iterations,
                &mut cache,
            );
            let mut bb: c2AABB = c2AABB {
                min: c2v { x: 0., y: 0. },
                max: c2v { x: 0., y: 0. },
            };
            bb.min = c2V(a1, a2);
            bb.max = c2V(a3, a4);
            let mut cap: c2Capsule = c2Capsule {
                a: c2v { x: 0., y: 0. },
                b: c2v { x: 0., y: 0. },
                r: 0.,
            };
            cap.a = c2V(b1, b2);
            cap.b = c2V(b3, b4);
            cap.r = b5;
            if reverse != 0 {
                c2GJK(
                    &mut cap as *mut c2Capsule as *const core::ffi::c_void,
                    C2_TYPE_CAPSULE,
                    std::ptr::null::<c2x>(),
                    &mut bb as *mut c2AABB as *const core::ffi::c_void,
                    C2_TYPE_AABB,
                    std::ptr::null::<c2x>(),
                    &mut a,
                    &mut b,
                    1 as core::ffi::c_int,
                    std::ptr::null_mut::<core::ffi::c_int>(),
                    std::ptr::null_mut::<c2GJKCache>(),
                );
            } else {
                c2GJK(
                    &mut bb as *mut c2AABB as *const core::ffi::c_void,
                    C2_TYPE_AABB,
                    std::ptr::null::<c2x>(),
                    &mut cap as *mut c2Capsule as *const core::ffi::c_void,
                    C2_TYPE_CAPSULE,
                    std::ptr::null::<c2x>(),
                    &mut a,
                    &mut b,
                    1 as core::ffi::c_int,
                    std::ptr::null_mut::<core::ffi::c_int>(),
                    std::ptr::null_mut::<c2GJKCache>(),
                );
            };
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates("gjk_cache_lib", SOURCE, &[], &[]);
}
