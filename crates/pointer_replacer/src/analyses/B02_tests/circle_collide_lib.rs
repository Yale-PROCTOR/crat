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
        pub type C2_TYPE = core::ffi::c_uint;
        pub const C2_TYPE_CAPSULE: C2_TYPE = 2;
        pub const C2_TYPE_AABB: C2_TYPE = 1;
        pub const C2_TYPE_CIRCLE: C2_TYPE = 0;
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
        pub unsafe extern "C" fn c2CircletoCapsule(A: c2Circle, B: c2Capsule) -> core::ffi::c_int {
            let n: c2v = c2Sub(B.b, B.a);
            let ap: c2v = c2Sub(A.p, B.a);
            let da: core::ffi::c_float = c2Dot(ap, n);
            let mut d2: core::ffi::c_float = 0.;
            if da < 0 as core::ffi::c_int as core::ffi::c_float {
                d2 = c2Dot(ap, ap);
            } else {
                let db: core::ffi::c_float = c2Dot(c2Sub(A.p, B.b), n);
                if db < 0 as core::ffi::c_int as core::ffi::c_float {
                    let e: c2v = c2Sub(ap, c2Mulvs(n, da / c2Dot(n, n)));
                    d2 = c2Dot(e, e);
                } else {
                    let bp: c2v = c2Sub(A.p, B.b);
                    d2 = c2Dot(bp, bp);
                }
            }
            let r: core::ffi::c_float = A.r + B.r;
            (d2 < r * r) as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn c2Collided(
            A: *const core::ffi::c_void,
            B: *const core::ffi::c_void,
            typeB: C2_TYPE,
        ) -> core::ffi::c_int {
            match typeB as core::ffi::c_uint {
                0 => c2CircletoCircle(*(A as *mut c2Circle), *(B as *mut c2Circle)),
                1 => c2CircletoAABB(*(A as *mut c2Circle), *(B as *mut c2AABB)),
                2 => c2CircletoCapsule(*(A as *mut c2Circle), *(B as *mut c2Capsule)),
                _ => 0 as core::ffi::c_int,
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn circle_collide(
            x: core::ffi::c_float,
            y: core::ffi::c_float,
            r: core::ffi::c_float,
        ) -> core::ffi::c_int {
            let mut result: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut circle_in: c2Circle = c2Circle {
                p: c2v { x: 0., y: 0. },
                r: 0.,
            };
            circle_in.p = c2V(x, y);
            circle_in.r = r;
            let mut circle: c2Circle = c2Circle {
                p: c2v { x: 0., y: 0. },
                r: 0.,
            };
            circle.p = c2V(-70.0f32, 0 as core::ffi::c_int as core::ffi::c_float);
            circle.r = 20.0f32;
            let mut aabb: c2AABB = c2AABB {
                min: c2v { x: 0., y: 0. },
                max: c2v { x: 0., y: 0. },
            };
            aabb.min = c2V(-40.0f32, -40.0f32);
            aabb.max = c2V(-15.0f32, -15.0f32);
            let mut capsule: c2Capsule = c2Capsule {
                a: c2v { x: 0., y: 0. },
                b: c2v { x: 0., y: 0. },
                r: 0.,
            };
            capsule.a = c2V(-40.0f32, 40.0f32);
            capsule.b = c2V(-20.0f32, 100.0f32);
            capsule.r = 10.0f32;
            result += c2Collided(
                &mut circle_in as *mut c2Circle as *const core::ffi::c_void,
                &mut circle as *mut c2Circle as *const core::ffi::c_void,
                C2_TYPE_CIRCLE,
            );
            result += c2Collided(
                &mut circle_in as *mut c2Circle as *const core::ffi::c_void,
                &mut aabb as *mut c2AABB as *const core::ffi::c_void,
                C2_TYPE_AABB,
            ) << 1 as core::ffi::c_int;
            result += c2Collided(
                &mut circle_in as *mut c2Circle as *const core::ffi::c_void,
                &mut capsule as *mut c2Capsule as *const core::ffi::c_void,
                C2_TYPE_CAPSULE,
            ) << 2 as core::ffi::c_int;
            result
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates("circle_collide_lib", SOURCE, &[], &[]);
}
