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
    pub mod r#match {
        extern "C" {
            fn memcpy(__dest: *mut core::ffi::c_void,
            __src: *const core::ffi::c_void, __n: size_t)
            -> *mut core::ffi::c_void;
            fn spectral_contrast(a: *mut float_t, b: *mut float_t,
            length: core::ffi::c_int)
            -> core::ffi::c_double;
        }
        pub type size_t = usize;
        pub type float_t = core::ffi::c_double;
        pub const N_SMOOTH: core::ffi::c_int = 16 as core::ffi::c_int;
        unsafe extern "C" fn total(mut v: *mut float_t,
            mut length: core::ffi::c_int) -> core::ffi::c_double {
            let mut sum: core::ffi::c_double =
                0 as core::ffi::c_int as core::ffi::c_double;
            let mut i: core::ffi::c_int = 0;
            i = 0 as core::ffi::c_int;
            while i < length {
                sum += *v.offset(i as isize) as core::ffi::c_double;
                i += 1;
            }
            return sum;
        }
        unsafe extern "C" fn smoothen(mut v: *mut float_t,
            mut length: core::ffi::c_int) {
            let mut sum: core::ffi::c_double = 0.;
            let mut i: core::ffi::c_int = 0;
            let mut j: core::ffi::c_int = 0;
            i = 0 as core::ffi::c_int;
            while i < length {
                sum = 0 as core::ffi::c_int as core::ffi::c_double;
                j = 0 as core::ffi::c_int;
                while j < N_SMOOTH && i + j < length {
                    sum += *v.offset((i + j) as isize) as core::ffi::c_double;
                    j += 1;
                }
                *v.offset(i as isize) =
                    (sum / N_SMOOTH as core::ffi::c_double) as float_t;
                i += 1;
            }
        }
        unsafe extern "C" fn differentiate(mut v: *mut float_t,
            mut length: core::ffi::c_int) {
            let mut i: core::ffi::c_int = 0;
            i = 0 as core::ffi::c_int;
            while i < length - 1 as core::ffi::c_int {
                *v.offset(i as isize) =
                    *v.offset((i + 1 as core::ffi::c_int) as isize) -
                        *v.offset(i as isize);
                i += 1;
            }
            *v.offset((length - 1 as core::ffi::c_int) as isize) =
                0 as core::ffi::c_int as float_t;
        }
        unsafe extern "C" fn preprocess(mut v: *mut float_t,
            mut source: *mut float_t, mut length: core::ffi::c_int) {
            memcpy(v as *mut core::ffi::c_void,
                source as *const core::ffi::c_void,
                (length as
                            size_t).wrapping_mul(::core::mem::size_of::<float_t>() as
                        size_t));
            smoothen(v, length);
            differentiate(v, length);
            smoothen(v, length);
        }
        #[export_name = "match"]
        pub unsafe extern "C" fn match_0(mut test: *mut float_t,
            mut reference: *mut float_t, mut bins: core::ffi::c_int,
            mut threshold: core::ffi::c_double) -> core::ffi::c_int {
            let vla = bins as usize;
            let mut t: Vec<float_t> = ::std::vec::from_elem(0., vla);
            let vla_0 = bins as usize;
            let mut r: Vec<float_t> = ::std::vec::from_elem(0., vla_0);
            if total(test, bins) < threshold * total(reference, bins) {
                return 0 as core::ffi::c_int;
            }
            preprocess(t.as_mut_ptr(), test, bins);
            preprocess(r.as_mut_ptr(), reference, bins);
            return (spectral_contrast(t.as_mut_ptr(), r.as_mut_ptr(), bins) >=
                            threshold) as core::ffi::c_int;
        }
    }
    pub mod spectral_contrast {
        extern "C" {
            fn sqrt(__x: core::ffi::c_double)
            -> core::ffi::c_double;
        }
        pub type float_t = core::ffi::c_float;
        unsafe extern "C" fn dot_product(mut a: *mut float_t,
            mut b: *mut float_t, mut length: core::ffi::c_int)
            -> core::ffi::c_double {
            let mut sum: core::ffi::c_double =
                0 as core::ffi::c_int as core::ffi::c_double;
            let mut i: core::ffi::c_int = 0;
            i = 0 as core::ffi::c_int;
            while i < length {
                sum +=
                    (*a.offset(i as isize) * *b.offset(i as isize)) as
                        core::ffi::c_double;
                i += 1;
            }
            return sum;
        }
        unsafe extern "C" fn normalize(mut v: *mut float_t,
            mut length: core::ffi::c_int) {
            let mut magnitude: core::ffi::c_double =
                sqrt(dot_product(v, v, length));
            let mut i: core::ffi::c_int = 0;
            i = 0 as core::ffi::c_int;
            while i < length {
                *v.offset(i as isize) =
                    (*v.offset(i as isize) as core::ffi::c_double / magnitude)
                        as float_t;
                i += 1;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn spectral_contrast(mut a: *mut float_t,
            mut b: *mut float_t, mut length: core::ffi::c_int)
            -> core::ffi::c_double {
            normalize(a, length);
            normalize(b, length);
            return dot_product(a, b, length);
        }
    }
}"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates("underhanded-c-nuke_lib", SOURCE, &[], &[]);
}
