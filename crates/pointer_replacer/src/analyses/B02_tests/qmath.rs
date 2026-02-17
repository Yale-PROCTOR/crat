use super::run_ownership_case;

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
    pub mod main {
        use crate::src::q_math::Q_rsqrt;
        extern "C" {
            pub type _IO_wide_data;
            pub type _IO_codecvt;
            pub type _IO_marker;
            static mut stderr: *mut FILE;
            fn fprintf(
                __stream: *mut FILE,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn printf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
            fn atof(__nptr: *const core::ffi::c_char) -> core::ffi::c_double;
            fn exit(__status: core::ffi::c_int) -> !;
        }
        pub type __off_t = core::ffi::c_long;
        pub type __off64_t = core::ffi::c_long;
        pub type size_t = usize;
        #[repr(C)]
        pub struct _IO_FILE {
            pub _flags: core::ffi::c_int,
            pub _IO_read_ptr: *mut core::ffi::c_char,
            pub _IO_read_end: *mut core::ffi::c_char,
            pub _IO_read_base: *mut core::ffi::c_char,
            pub _IO_write_base: *mut core::ffi::c_char,
            pub _IO_write_ptr: *mut core::ffi::c_char,
            pub _IO_write_end: *mut core::ffi::c_char,
            pub _IO_buf_base: *mut core::ffi::c_char,
            pub _IO_buf_end: *mut core::ffi::c_char,
            pub _IO_save_base: *mut core::ffi::c_char,
            pub _IO_backup_base: *mut core::ffi::c_char,
            pub _IO_save_end: *mut core::ffi::c_char,
            pub _markers: *mut _IO_marker,
            pub _chain: *mut _IO_FILE,
            pub _fileno: core::ffi::c_int,
            pub _flags2: core::ffi::c_int,
            pub _old_offset: __off_t,
            pub _cur_column: core::ffi::c_ushort,
            pub _vtable_offset: core::ffi::c_schar,
            pub _shortbuf: [core::ffi::c_char; 1],
            pub _lock: *mut core::ffi::c_void,
            pub _offset: __off64_t,
            pub _codecvt: *mut _IO_codecvt,
            pub _wide_data: *mut _IO_wide_data,
            pub _freeres_list: *mut _IO_FILE,
            pub _freeres_buf: *mut core::ffi::c_void,
            pub __pad5: size_t,
            pub _mode: core::ffi::c_int,
            pub _unused2: [core::ffi::c_char; 20],
        }
        #[automatically_derived]
        impl ::core::marker::Copy for _IO_FILE {}
        #[automatically_derived]
        impl ::core::clone::Clone for _IO_FILE {
            #[inline]
            fn clone(&self) -> _IO_FILE {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*mut _IO_marker>;
                let _: ::core::clone::AssertParamIsClone<*mut _IO_FILE>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<__off_t>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_ushort>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_schar>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 1]>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_void>;
                let _: ::core::clone::AssertParamIsClone<__off64_t>;
                let _: ::core::clone::AssertParamIsClone<*mut _IO_codecvt>;
                let _: ::core::clone::AssertParamIsClone<*mut _IO_wide_data>;
                let _: ::core::clone::AssertParamIsClone<*mut _IO_FILE>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_void>;
                let _: ::core::clone::AssertParamIsClone<size_t>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 20]>;
                *self
            }
        }
        pub type _IO_lock_t = ();
        pub type FILE = _IO_FILE;
        pub type vec_t = core::ffi::c_float;
        pub type vec3_t = [vec_t; 3];
        #[inline]
        unsafe extern "C" fn VectorNormalizeFast(v: *mut vec_t) {
            let mut ilength: core::ffi::c_float = 0.;
            ilength = Q_rsqrt(
                *v.offset(0 as core::ffi::c_int as isize) as core::ffi::c_float
                    * *v.offset(0 as core::ffi::c_int as isize) as core::ffi::c_float
                    + *v.offset(1 as core::ffi::c_int as isize) as core::ffi::c_float
                        * *v.offset(1 as core::ffi::c_int as isize) as core::ffi::c_float
                    + *v.offset(2 as core::ffi::c_int as isize) as core::ffi::c_float
                        * *v.offset(2 as core::ffi::c_int as isize) as core::ffi::c_float,
            );
            *v.offset(0 as core::ffi::c_int as isize) *= ilength;
            *v.offset(1 as core::ffi::c_int as isize) *= ilength;
            *v.offset(2 as core::ffi::c_int as isize) *= ilength;
        }
        unsafe fn main_0(
            argc: core::ffi::c_int,
            argv: *mut *mut core::ffi::c_char,
        ) -> core::ffi::c_int {
            let mut Inputs: vec3_t = [0.; 3];
            if argc != 4 as core::ffi::c_int {
                fprintf(
                    stderr,
                    b"%s requires 4 inputs\n\0" as *const u8 as *const core::ffi::c_char,
                    *argv.offset(0 as core::ffi::c_int as isize),
                );
                exit(1 as core::ffi::c_int);
            }
            Inputs[0 as core::ffi::c_int as usize] =
                atof(*argv.offset(1 as core::ffi::c_int as isize)) as vec_t;
            Inputs[1 as core::ffi::c_int as usize] =
                atof(*argv.offset(2 as core::ffi::c_int as isize)) as vec_t;
            Inputs[2 as core::ffi::c_int as usize] =
                atof(*argv.offset(3 as core::ffi::c_int as isize)) as vec_t;
            VectorNormalizeFast(Inputs.as_mut_ptr());
            printf(
                b"%f %f %f\n\0" as *const u8 as *const core::ffi::c_char,
                Inputs[0 as core::ffi::c_int as usize] as core::ffi::c_double,
                Inputs[1 as core::ffi::c_int as usize] as core::ffi::c_double,
                Inputs[2 as core::ffi::c_int as usize] as core::ffi::c_double,
            );
            0 as core::ffi::c_int
        }
        pub fn main() {
            let mut args: Vec<*mut core::ffi::c_char> = Vec::new();
            for arg in ::std::env::args() {
                args.push(
                    (::std::ffi::CString::new(arg))
                        .expect("Failed to convert argument into CString.")
                        .into_raw(),
                );
            }
            args.push(::core::ptr::null_mut());
            unsafe {
                ::std::process::exit(main_0(
                    (args.len() - 1) as core::ffi::c_int,
                    args.as_mut_ptr() as *mut *mut core::ffi::c_char,
                ) as i32)
            }
        }
    }
    pub mod q_math {
        use crate::src::main::size_t;
        use crate::src::main::vec3_t;
        use crate::src::main::vec_t;
        extern "C" {
            fn atan2(__y: core::ffi::c_double, __x: core::ffi::c_double) -> core::ffi::c_double;
            fn cos(__x: core::ffi::c_double) -> core::ffi::c_double;
            fn sin(__x: core::ffi::c_double) -> core::ffi::c_double;
            fn sqrt(__x: core::ffi::c_double) -> core::ffi::c_double;
            fn fabs(__x: core::ffi::c_double) -> core::ffi::c_double;
            fn memcpy(
                __dest: *mut core::ffi::c_void,
                __src: *const core::ffi::c_void,
                __n: size_t,
            ) -> *mut core::ffi::c_void;
            fn memset(
                __s: *mut core::ffi::c_void,
                __c: core::ffi::c_int,
                __n: size_t,
            ) -> *mut core::ffi::c_void;
        }
        pub type __uint32_t = u32;
        pub type byte = core::ffi::c_uchar;
        pub type qboolean = core::ffi::c_uint;
        pub const qtrue: qboolean = 1;
        pub const qfalse: qboolean = 0;
        pub type vec4_t = [vec_t; 4];
        #[repr(C)]
        pub struct cplane_s {
            pub normal: vec3_t,
            pub dist: core::ffi::c_float,
            pub type_0: byte,
            pub signbits: byte,
            pub pad: [byte; 2],
        }
        #[automatically_derived]
        impl ::core::marker::Copy for cplane_s {}
        #[automatically_derived]
        impl ::core::clone::Clone for cplane_s {
            #[inline]
            fn clone(&self) -> cplane_s {
                let _: ::core::clone::AssertParamIsClone<vec3_t>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_float>;
                let _: ::core::clone::AssertParamIsClone<byte>;
                let _: ::core::clone::AssertParamIsClone<[byte; 2]>;
                *self
            }
        }
        pub type uint32_t = __uint32_t;
        pub type cplane_t = cplane_s;
        pub const M_PI: core::ffi::c_double = 3.141_592_653_589_793_f64;
        pub const PITCH: core::ffi::c_int = 0 as core::ffi::c_int;
        pub const YAW: core::ffi::c_int = 1 as core::ffi::c_int;
        pub const ROLL: core::ffi::c_int = 2 as core::ffi::c_int;
        pub const NUMVERTEXNORMALS: core::ffi::c_int = 162 as core::ffi::c_int;
        #[inline]
        unsafe extern "C" fn VectorLength(v: *const vec_t) -> vec_t {
            sqrt(
                (*v.offset(0 as core::ffi::c_int as isize)
                    * *v.offset(0 as core::ffi::c_int as isize)
                    + *v.offset(1 as core::ffi::c_int as isize)
                        * *v.offset(1 as core::ffi::c_int as isize)
                    + *v.offset(2 as core::ffi::c_int as isize)
                        * *v.offset(2 as core::ffi::c_int as isize))
                    as core::ffi::c_double,
            ) as vec_t
        }
        #[inline]
        unsafe extern "C" fn CrossProduct(v1: *const vec_t, v2: *const vec_t, cross: *mut vec_t) {
            *cross.offset(0 as core::ffi::c_int as isize) = *v1
                .offset(1 as core::ffi::c_int as isize)
                * *v2.offset(2 as core::ffi::c_int as isize)
                - *v1.offset(2 as core::ffi::c_int as isize)
                    * *v2.offset(1 as core::ffi::c_int as isize);
            *cross.offset(1 as core::ffi::c_int as isize) = *v1
                .offset(2 as core::ffi::c_int as isize)
                * *v2.offset(0 as core::ffi::c_int as isize)
                - *v1.offset(0 as core::ffi::c_int as isize)
                    * *v2.offset(2 as core::ffi::c_int as isize);
            *cross.offset(2 as core::ffi::c_int as isize) = *v1
                .offset(0 as core::ffi::c_int as isize)
                * *v2.offset(1 as core::ffi::c_int as isize)
                - *v1.offset(1 as core::ffi::c_int as isize)
                    * *v2.offset(0 as core::ffi::c_int as isize);
        }
        #[no_mangle]
        pub static mut vec3_origin: vec3_t = [
            0 as core::ffi::c_int as vec_t,
            0 as core::ffi::c_int as vec_t,
            0 as core::ffi::c_int as vec_t,
        ];
        #[no_mangle]
        pub static mut axisDefault: [vec3_t; 3] = [
            [
                1 as core::ffi::c_int as vec_t,
                0 as core::ffi::c_int as vec_t,
                0 as core::ffi::c_int as vec_t,
            ],
            [
                0 as core::ffi::c_int as vec_t,
                1 as core::ffi::c_int as vec_t,
                0 as core::ffi::c_int as vec_t,
            ],
            [
                0 as core::ffi::c_int as vec_t,
                0 as core::ffi::c_int as vec_t,
                1 as core::ffi::c_int as vec_t,
            ],
        ];
        #[no_mangle]
        pub static mut colorBlack: vec4_t = [
            0 as core::ffi::c_int as vec_t,
            0 as core::ffi::c_int as vec_t,
            0 as core::ffi::c_int as vec_t,
            1 as core::ffi::c_int as vec_t,
        ];
        #[no_mangle]
        pub static mut colorRed: vec4_t = [
            1 as core::ffi::c_int as vec_t,
            0 as core::ffi::c_int as vec_t,
            0 as core::ffi::c_int as vec_t,
            1 as core::ffi::c_int as vec_t,
        ];
        #[no_mangle]
        pub static mut colorGreen: vec4_t = [
            0 as core::ffi::c_int as vec_t,
            1 as core::ffi::c_int as vec_t,
            0 as core::ffi::c_int as vec_t,
            1 as core::ffi::c_int as vec_t,
        ];
        #[no_mangle]
        pub static mut colorBlue: vec4_t = [
            0 as core::ffi::c_int as vec_t,
            0 as core::ffi::c_int as vec_t,
            1 as core::ffi::c_int as vec_t,
            1 as core::ffi::c_int as vec_t,
        ];
        #[no_mangle]
        pub static mut colorYellow: vec4_t = [
            1 as core::ffi::c_int as vec_t,
            1 as core::ffi::c_int as vec_t,
            0 as core::ffi::c_int as vec_t,
            1 as core::ffi::c_int as vec_t,
        ];
        #[no_mangle]
        pub static mut colorMagenta: vec4_t = [
            1 as core::ffi::c_int as vec_t,
            0 as core::ffi::c_int as vec_t,
            1 as core::ffi::c_int as vec_t,
            1 as core::ffi::c_int as vec_t,
        ];
        #[no_mangle]
        pub static mut colorCyan: vec4_t = [
            0 as core::ffi::c_int as vec_t,
            1 as core::ffi::c_int as vec_t,
            1 as core::ffi::c_int as vec_t,
            1 as core::ffi::c_int as vec_t,
        ];
        #[no_mangle]
        pub static mut colorWhite: vec4_t = [
            1 as core::ffi::c_int as vec_t,
            1 as core::ffi::c_int as vec_t,
            1 as core::ffi::c_int as vec_t,
            1 as core::ffi::c_int as vec_t,
        ];
        #[no_mangle]
        pub static mut colorLtGrey: vec4_t = [
            0.75f64 as vec_t,
            0.75f64 as vec_t,
            0.75f64 as vec_t,
            1 as core::ffi::c_int as vec_t,
        ];
        #[no_mangle]
        pub static mut colorMdGrey: vec4_t = [
            0.5f64 as vec_t,
            0.5f64 as vec_t,
            0.5f64 as vec_t,
            1 as core::ffi::c_int as vec_t,
        ];
        #[no_mangle]
        pub static mut colorDkGrey: vec4_t = [
            0.25f64 as vec_t,
            0.25f64 as vec_t,
            0.25f64 as vec_t,
            1 as core::ffi::c_int as vec_t,
        ];
        #[no_mangle]
        pub static mut g_color_table: [vec4_t; 8] = [
            [
                0.0f64 as vec_t,
                0.0f64 as vec_t,
                0.0f64 as vec_t,
                1.0f64 as vec_t,
            ],
            [
                1.0f64 as vec_t,
                0.0f64 as vec_t,
                0.0f64 as vec_t,
                1.0f64 as vec_t,
            ],
            [
                0.0f64 as vec_t,
                1.0f64 as vec_t,
                0.0f64 as vec_t,
                1.0f64 as vec_t,
            ],
            [
                1.0f64 as vec_t,
                1.0f64 as vec_t,
                0.0f64 as vec_t,
                1.0f64 as vec_t,
            ],
            [
                0.0f64 as vec_t,
                0.0f64 as vec_t,
                1.0f64 as vec_t,
                1.0f64 as vec_t,
            ],
            [
                0.0f64 as vec_t,
                1.0f64 as vec_t,
                1.0f64 as vec_t,
                1.0f64 as vec_t,
            ],
            [
                1.0f64 as vec_t,
                0.0f64 as vec_t,
                1.0f64 as vec_t,
                1.0f64 as vec_t,
            ],
            [
                1.0f64 as vec_t,
                1.0f64 as vec_t,
                1.0f64 as vec_t,
                1.0f64 as vec_t,
            ],
        ];
        #[no_mangle]
        pub static mut bytedirs: [vec3_t; 162] = [
            [-0.525731f32, 0.000000f32, 0.850651f32],
            [-0.442863f32, 0.238856f32, 0.864188f32],
            [-0.295242f32, 0.000000f32, 0.955423f32],
            [-0.309017f32, 0.500000f32, 0.809017f32],
            [-0.162460f32, 0.262866f32, 0.951056f32],
            [0.000000f32, 0.000000f32, 1.000000f32],
            [0.000000f32, 0.850651f32, 0.525731f32],
            [-0.147621f32, 0.716567f32, 0.681718f32],
            [0.147621f32, 0.716567f32, 0.681718f32],
            [0.000000f32, 0.525731f32, 0.850651f32],
            [0.309017f32, 0.500000f32, 0.809017f32],
            [0.525731f32, 0.000000f32, 0.850651f32],
            [0.295242f32, 0.000000f32, 0.955423f32],
            [0.442863f32, 0.238856f32, 0.864188f32],
            [0.162460f32, 0.262866f32, 0.951056f32],
            [-0.681718f32, 0.147621f32, 0.716567f32],
            [-0.809017f32, 0.309017f32, 0.500000f32],
            [-0.587785f32, 0.425325f32, 0.688191f32],
            [-0.850651f32, 0.525731f32, 0.000000f32],
            [-0.864188f32, 0.442863f32, 0.238856f32],
            [-0.716567f32, 0.681718f32, 0.147621f32],
            [-0.688191f32, 0.587785f32, 0.425325f32],
            [-0.500000f32, 0.809017f32, 0.309017f32],
            [-0.238856f32, 0.864188f32, 0.442863f32],
            [-0.425325f32, 0.688191f32, 0.587785f32],
            [-0.716567f32, 0.681718f32, -0.147621f32],
            [-0.500000f32, 0.809017f32, -0.309017f32],
            [-0.525731f32, 0.850651f32, 0.000000f32],
            [0.000000f32, 0.850651f32, -0.525731f32],
            [-0.238856f32, 0.864188f32, -0.442863f32],
            [0.000000f32, 0.955423f32, -0.295242f32],
            [-0.262866f32, 0.951056f32, -0.162460f32],
            [0.000000f32, 1.000000f32, 0.000000f32],
            [0.000000f32, 0.955423f32, 0.295242f32],
            [-0.262866f32, 0.951056f32, 0.162460f32],
            [0.238856f32, 0.864188f32, 0.442863f32],
            [0.262866f32, 0.951056f32, 0.162460f32],
            [0.500000f32, 0.809017f32, 0.309017f32],
            [0.238856f32, 0.864188f32, -0.442863f32],
            [0.262866f32, 0.951056f32, -0.162460f32],
            [0.500000f32, 0.809017f32, -0.309017f32],
            [0.850651f32, 0.525731f32, 0.000000f32],
            [0.716567f32, 0.681718f32, 0.147621f32],
            [0.716567f32, 0.681718f32, -0.147621f32],
            [0.525731f32, 0.850651f32, 0.000000f32],
            [0.425325f32, 0.688191f32, 0.587785f32],
            [0.864188f32, 0.442863f32, 0.238856f32],
            [0.688191f32, 0.587785f32, 0.425325f32],
            [0.809017f32, 0.309017f32, 0.500000f32],
            [0.681718f32, 0.147621f32, 0.716567f32],
            [0.587785f32, 0.425325f32, 0.688191f32],
            [0.955423f32, 0.295242f32, 0.000000f32],
            [1.000000f32, 0.000000f32, 0.000000f32],
            [0.951056f32, 0.162460f32, 0.262866f32],
            [0.850651f32, -0.525731f32, 0.000000f32],
            [0.955423f32, -0.295242f32, 0.000000f32],
            [0.864188f32, -0.442863f32, 0.238856f32],
            [0.951056f32, -0.162460f32, 0.262866f32],
            [0.809017f32, -0.309017f32, 0.500000f32],
            [0.681718f32, -0.147621f32, 0.716567f32],
            [0.850651f32, 0.000000f32, 0.525731f32],
            [0.864188f32, 0.442863f32, -0.238856f32],
            [0.809017f32, 0.309017f32, -0.500000f32],
            [0.951056f32, 0.162460f32, -0.262866f32],
            [0.525731f32, 0.000000f32, -0.850651f32],
            [0.681718f32, 0.147621f32, -0.716567f32],
            [0.681718f32, -0.147621f32, -0.716567f32],
            [0.850651f32, 0.000000f32, -0.525731f32],
            [0.809017f32, -0.309017f32, -0.500000f32],
            [0.864188f32, -0.442863f32, -0.238856f32],
            [0.951056f32, -0.162460f32, -0.262866f32],
            [0.147621f32, 0.716567f32, -0.681718f32],
            [0.309017f32, 0.500000f32, -0.809017f32],
            [0.425325f32, 0.688191f32, -0.587785f32],
            [0.442863f32, 0.238856f32, -0.864188f32],
            [0.587785f32, 0.425325f32, -0.688191f32],
            [0.688191f32, 0.587785f32, -0.425325f32],
            [-0.147621f32, 0.716567f32, -0.681718f32],
            [-0.309017f32, 0.500000f32, -0.809017f32],
            [0.000000f32, 0.525731f32, -0.850651f32],
            [-0.525731f32, 0.000000f32, -0.850651f32],
            [-0.442863f32, 0.238856f32, -0.864188f32],
            [-0.295242f32, 0.000000f32, -0.955423f32],
            [-0.162460f32, 0.262866f32, -0.951056f32],
            [0.000000f32, 0.000000f32, -1.000000f32],
            [0.295242f32, 0.000000f32, -0.955423f32],
            [0.162460f32, 0.262866f32, -0.951056f32],
            [-0.442863f32, -0.238856f32, -0.864188f32],
            [-0.309017f32, -0.500000f32, -0.809017f32],
            [-0.162460f32, -0.262866f32, -0.951056f32],
            [0.000000f32, -0.850651f32, -0.525731f32],
            [-0.147621f32, -0.716567f32, -0.681718f32],
            [0.147621f32, -0.716567f32, -0.681718f32],
            [0.000000f32, -0.525731f32, -0.850651f32],
            [0.309017f32, -0.500000f32, -0.809017f32],
            [0.442863f32, -0.238856f32, -0.864188f32],
            [0.162460f32, -0.262866f32, -0.951056f32],
            [0.238856f32, -0.864188f32, -0.442863f32],
            [0.500000f32, -0.809017f32, -0.309017f32],
            [0.425325f32, -0.688191f32, -0.587785f32],
            [0.716567f32, -0.681718f32, -0.147621f32],
            [0.688191f32, -0.587785f32, -0.425325f32],
            [0.587785f32, -0.425325f32, -0.688191f32],
            [0.000000f32, -0.955423f32, -0.295242f32],
            [0.000000f32, -1.000000f32, 0.000000f32],
            [0.262866f32, -0.951056f32, -0.162460f32],
            [0.000000f32, -0.850651f32, 0.525731f32],
            [0.000000f32, -0.955423f32, 0.295242f32],
            [0.238856f32, -0.864188f32, 0.442863f32],
            [0.262866f32, -0.951056f32, 0.162460f32],
            [0.500000f32, -0.809017f32, 0.309017f32],
            [0.716567f32, -0.681718f32, 0.147621f32],
            [0.525731f32, -0.850651f32, 0.000000f32],
            [-0.238856f32, -0.864188f32, -0.442863f32],
            [-0.500000f32, -0.809017f32, -0.309017f32],
            [-0.262866f32, -0.951056f32, -0.162460f32],
            [-0.850651f32, -0.525731f32, 0.000000f32],
            [-0.716567f32, -0.681718f32, -0.147621f32],
            [-0.716567f32, -0.681718f32, 0.147621f32],
            [-0.525731f32, -0.850651f32, 0.000000f32],
            [-0.500000f32, -0.809017f32, 0.309017f32],
            [-0.238856f32, -0.864188f32, 0.442863f32],
            [-0.262866f32, -0.951056f32, 0.162460f32],
            [-0.864188f32, -0.442863f32, 0.238856f32],
            [-0.809017f32, -0.309017f32, 0.500000f32],
            [-0.688191f32, -0.587785f32, 0.425325f32],
            [-0.681718f32, -0.147621f32, 0.716567f32],
            [-0.442863f32, -0.238856f32, 0.864188f32],
            [-0.587785f32, -0.425325f32, 0.688191f32],
            [-0.309017f32, -0.500000f32, 0.809017f32],
            [-0.147621f32, -0.716567f32, 0.681718f32],
            [-0.425325f32, -0.688191f32, 0.587785f32],
            [-0.162460f32, -0.262866f32, 0.951056f32],
            [0.442863f32, -0.238856f32, 0.864188f32],
            [0.162460f32, -0.262866f32, 0.951056f32],
            [0.309017f32, -0.500000f32, 0.809017f32],
            [0.147621f32, -0.716567f32, 0.681718f32],
            [0.000000f32, -0.525731f32, 0.850651f32],
            [0.425325f32, -0.688191f32, 0.587785f32],
            [0.587785f32, -0.425325f32, 0.688191f32],
            [0.688191f32, -0.587785f32, 0.425325f32],
            [-0.955423f32, 0.295242f32, 0.000000f32],
            [-0.951056f32, 0.162460f32, 0.262866f32],
            [-1.000000f32, 0.000000f32, 0.000000f32],
            [-0.850651f32, 0.000000f32, 0.525731f32],
            [-0.955423f32, -0.295242f32, 0.000000f32],
            [-0.951056f32, -0.162460f32, 0.262866f32],
            [-0.864188f32, 0.442863f32, -0.238856f32],
            [-0.951056f32, 0.162460f32, -0.262866f32],
            [-0.809017f32, 0.309017f32, -0.500000f32],
            [-0.864188f32, -0.442863f32, -0.238856f32],
            [-0.951056f32, -0.162460f32, -0.262866f32],
            [-0.809017f32, -0.309017f32, -0.500000f32],
            [-0.681718f32, 0.147621f32, -0.716567f32],
            [-0.681718f32, -0.147621f32, -0.716567f32],
            [-0.850651f32, 0.000000f32, -0.525731f32],
            [-0.688191f32, 0.587785f32, -0.425325f32],
            [-0.587785f32, 0.425325f32, -0.688191f32],
            [-0.425325f32, 0.688191f32, -0.587785f32],
            [-0.425325f32, -0.688191f32, -0.587785f32],
            [-0.587785f32, -0.425325f32, -0.688191f32],
            [-0.688191f32, -0.587785f32, -0.425325f32],
        ];
        #[no_mangle]
        pub unsafe extern "C" fn Q_rand(seed: *mut core::ffi::c_int) -> core::ffi::c_int {
            *seed = 69069 as core::ffi::c_int * *seed + 1 as core::ffi::c_int;
            *seed
        }
        #[no_mangle]
        pub unsafe extern "C" fn Q_random(seed: *mut core::ffi::c_int) -> core::ffi::c_float {
            (Q_rand(seed) & 0xffff as core::ffi::c_int) as core::ffi::c_float
                / 0x10000 as core::ffi::c_int as core::ffi::c_float
        }
        #[no_mangle]
        pub unsafe extern "C" fn Q_crandom(seed: *mut core::ffi::c_int) -> core::ffi::c_float {
            (2.0f64 * (Q_random(seed) as core::ffi::c_double - 0.5f64)) as core::ffi::c_float
        }
        #[no_mangle]
        pub unsafe extern "C" fn ClampChar(i: core::ffi::c_int) -> core::ffi::c_schar {
            if i < -(128 as core::ffi::c_int) {
                return -(128 as core::ffi::c_int) as core::ffi::c_schar;
            }
            if i > 127 as core::ffi::c_int {
                return 127 as core::ffi::c_schar;
            }
            i as core::ffi::c_schar
        }
        #[no_mangle]
        pub unsafe extern "C" fn ClampShort(i: core::ffi::c_int) -> core::ffi::c_short {
            if i < -(32768 as core::ffi::c_int) {
                return -(32768 as core::ffi::c_int) as core::ffi::c_short;
            }
            if i > 0x7fff as core::ffi::c_int {
                return 0x7fff as core::ffi::c_short;
            }
            i as core::ffi::c_short
        }
        #[no_mangle]
        pub unsafe extern "C" fn DirToByte(dir: *mut vec_t) -> core::ffi::c_int {
            let mut i: core::ffi::c_int = 0;
            let mut best: core::ffi::c_int = 0;
            let mut d: core::ffi::c_float = 0.;
            let mut bestd: core::ffi::c_float = 0.;
            if dir.is_null() {
                return 0 as core::ffi::c_int;
            }
            bestd = 0 as core::ffi::c_int as core::ffi::c_float;
            best = 0 as core::ffi::c_int;
            i = 0 as core::ffi::c_int;
            while i < NUMVERTEXNORMALS {
                d = (*dir.offset(0 as core::ffi::c_int as isize)
                    * bytedirs[i as usize][0 as core::ffi::c_int as usize]
                    + *dir.offset(1 as core::ffi::c_int as isize)
                        * bytedirs[i as usize][1 as core::ffi::c_int as usize]
                    + *dir.offset(2 as core::ffi::c_int as isize)
                        * bytedirs[i as usize][2 as core::ffi::c_int as usize])
                    as core::ffi::c_float;
                if d > bestd {
                    bestd = d;
                    best = i;
                }
                i += 1;
            }
            best
        }
        #[no_mangle]
        pub unsafe extern "C" fn ByteToDir(b: core::ffi::c_int, dir: *mut vec_t) {
            if b < 0 as core::ffi::c_int || b >= NUMVERTEXNORMALS {
                *dir.offset(0 as core::ffi::c_int as isize) =
                    vec3_origin[0 as core::ffi::c_int as usize];
                *dir.offset(1 as core::ffi::c_int as isize) =
                    vec3_origin[1 as core::ffi::c_int as usize];
                *dir.offset(2 as core::ffi::c_int as isize) =
                    vec3_origin[2 as core::ffi::c_int as usize];
                return;
            }
            *dir.offset(0 as core::ffi::c_int as isize) =
                bytedirs[b as usize][0 as core::ffi::c_int as usize];
            *dir.offset(1 as core::ffi::c_int as isize) =
                bytedirs[b as usize][1 as core::ffi::c_int as usize];
            *dir.offset(2 as core::ffi::c_int as isize) =
                bytedirs[b as usize][2 as core::ffi::c_int as usize];
        }
        #[no_mangle]
        pub unsafe extern "C" fn ColorBytes3(
            r: core::ffi::c_float,
            g: core::ffi::c_float,
            b: core::ffi::c_float,
        ) -> core::ffi::c_uint {
            let mut i: core::ffi::c_uint = 0;
            *(&mut i as *mut core::ffi::c_uint as *mut byte)
                .offset(0 as core::ffi::c_int as isize) =
                (r * 255 as core::ffi::c_int as core::ffi::c_float) as byte;
            *(&mut i as *mut core::ffi::c_uint as *mut byte)
                .offset(1 as core::ffi::c_int as isize) =
                (g * 255 as core::ffi::c_int as core::ffi::c_float) as byte;
            *(&mut i as *mut core::ffi::c_uint as *mut byte)
                .offset(2 as core::ffi::c_int as isize) =
                (b * 255 as core::ffi::c_int as core::ffi::c_float) as byte;
            i
        }
        #[no_mangle]
        pub unsafe extern "C" fn ColorBytes4(
            r: core::ffi::c_float,
            g: core::ffi::c_float,
            b: core::ffi::c_float,
            a: core::ffi::c_float,
        ) -> core::ffi::c_uint {
            let mut i: core::ffi::c_uint = 0;
            *(&mut i as *mut core::ffi::c_uint as *mut byte)
                .offset(0 as core::ffi::c_int as isize) =
                (r * 255 as core::ffi::c_int as core::ffi::c_float) as byte;
            *(&mut i as *mut core::ffi::c_uint as *mut byte)
                .offset(1 as core::ffi::c_int as isize) =
                (g * 255 as core::ffi::c_int as core::ffi::c_float) as byte;
            *(&mut i as *mut core::ffi::c_uint as *mut byte)
                .offset(2 as core::ffi::c_int as isize) =
                (b * 255 as core::ffi::c_int as core::ffi::c_float) as byte;
            *(&mut i as *mut core::ffi::c_uint as *mut byte)
                .offset(3 as core::ffi::c_int as isize) =
                (a * 255 as core::ffi::c_int as core::ffi::c_float) as byte;
            i
        }
        #[no_mangle]
        pub unsafe extern "C" fn NormalizeColor(
            in_0: *const vec_t,
            out: *mut vec_t,
        ) -> core::ffi::c_float {
            let mut max: core::ffi::c_float = 0.;
            max = *in_0.offset(0 as core::ffi::c_int as isize) as core::ffi::c_float;
            if *in_0.offset(1 as core::ffi::c_int as isize) > max {
                max = *in_0.offset(1 as core::ffi::c_int as isize) as core::ffi::c_float;
            }
            if *in_0.offset(2 as core::ffi::c_int as isize) > max {
                max = *in_0.offset(2 as core::ffi::c_int as isize) as core::ffi::c_float;
            }
            if max == 0. {
                *out.offset(2 as core::ffi::c_int as isize) = 0 as core::ffi::c_int as vec_t;
                *out.offset(1 as core::ffi::c_int as isize) =
                    *out.offset(2 as core::ffi::c_int as isize);
                *out.offset(0 as core::ffi::c_int as isize) =
                    *out.offset(1 as core::ffi::c_int as isize);
            } else {
                *out.offset(0 as core::ffi::c_int as isize) =
                    (*in_0.offset(0 as core::ffi::c_int as isize) as core::ffi::c_float / max)
                        as vec_t;
                *out.offset(1 as core::ffi::c_int as isize) =
                    (*in_0.offset(1 as core::ffi::c_int as isize) as core::ffi::c_float / max)
                        as vec_t;
                *out.offset(2 as core::ffi::c_int as isize) =
                    (*in_0.offset(2 as core::ffi::c_int as isize) as core::ffi::c_float / max)
                        as vec_t;
            }
            max
        }
        #[no_mangle]
        pub unsafe extern "C" fn PlaneFromPoints(
            plane: *mut vec_t,
            a: *const vec_t,
            b: *const vec_t,
            c: *const vec_t,
        ) -> qboolean {
            let mut d1: vec3_t = [0.; 3];
            let mut d2: vec3_t = [0.; 3];
            d1[0 as core::ffi::c_int as usize] = *b.offset(0 as core::ffi::c_int as isize)
                - *a.offset(0 as core::ffi::c_int as isize);
            d1[1 as core::ffi::c_int as usize] = *b.offset(1 as core::ffi::c_int as isize)
                - *a.offset(1 as core::ffi::c_int as isize);
            d1[2 as core::ffi::c_int as usize] = *b.offset(2 as core::ffi::c_int as isize)
                - *a.offset(2 as core::ffi::c_int as isize);
            d2[0 as core::ffi::c_int as usize] = *c.offset(0 as core::ffi::c_int as isize)
                - *a.offset(0 as core::ffi::c_int as isize);
            d2[1 as core::ffi::c_int as usize] = *c.offset(1 as core::ffi::c_int as isize)
                - *a.offset(1 as core::ffi::c_int as isize);
            d2[2 as core::ffi::c_int as usize] = *c.offset(2 as core::ffi::c_int as isize)
                - *a.offset(2 as core::ffi::c_int as isize);
            CrossProduct(
                d2.as_ptr() as *const vec_t,
                d1.as_ptr() as *const vec_t,
                plane as *mut vec_t,
            );
            if VectorNormalize(plane as *mut vec_t) == 0 as core::ffi::c_int as core::ffi::c_float {
                return qfalse;
            }
            *plane.offset(3 as core::ffi::c_int as isize) = *a
                .offset(0 as core::ffi::c_int as isize)
                * *plane.offset(0 as core::ffi::c_int as isize)
                + *a.offset(1 as core::ffi::c_int as isize)
                    * *plane.offset(1 as core::ffi::c_int as isize)
                + *a.offset(2 as core::ffi::c_int as isize)
                    * *plane.offset(2 as core::ffi::c_int as isize);
            qtrue
        }
        #[no_mangle]
        pub unsafe extern "C" fn RotatePointAroundVector(
            dst: *mut vec_t,
            dir: *const vec_t,
            point: *const vec_t,
            degrees: core::ffi::c_float,
        ) {
            let mut m: [[core::ffi::c_float; 3]; 3] = [[0.; 3]; 3];
            let mut im: [[core::ffi::c_float; 3]; 3] = [[0.; 3]; 3];
            let mut zrot: [[core::ffi::c_float; 3]; 3] = [[0.; 3]; 3];
            let mut tmpmat: [[core::ffi::c_float; 3]; 3] = [[0.; 3]; 3];
            let mut rot: [[core::ffi::c_float; 3]; 3] = [[0.; 3]; 3];
            let mut i: core::ffi::c_int = 0;
            let mut vr: vec3_t = [0.; 3];
            let mut vup: vec3_t = [0.; 3];
            let mut vf: vec3_t = [0.; 3];
            let mut rad: core::ffi::c_float = 0.;
            vf[0 as core::ffi::c_int as usize] = *dir.offset(0 as core::ffi::c_int as isize);
            vf[1 as core::ffi::c_int as usize] = *dir.offset(1 as core::ffi::c_int as isize);
            vf[2 as core::ffi::c_int as usize] = *dir.offset(2 as core::ffi::c_int as isize);
            PerpendicularVector(vr.as_mut_ptr(), dir);
            CrossProduct(
                vr.as_ptr() as *const vec_t,
                vf.as_ptr() as *const vec_t,
                vup.as_mut_ptr(),
            );
            m[0 as core::ffi::c_int as usize][0 as core::ffi::c_int as usize] =
                vr[0 as core::ffi::c_int as usize] as core::ffi::c_float;
            m[1 as core::ffi::c_int as usize][0 as core::ffi::c_int as usize] =
                vr[1 as core::ffi::c_int as usize] as core::ffi::c_float;
            m[2 as core::ffi::c_int as usize][0 as core::ffi::c_int as usize] =
                vr[2 as core::ffi::c_int as usize] as core::ffi::c_float;
            m[0 as core::ffi::c_int as usize][1 as core::ffi::c_int as usize] =
                vup[0 as core::ffi::c_int as usize] as core::ffi::c_float;
            m[1 as core::ffi::c_int as usize][1 as core::ffi::c_int as usize] =
                vup[1 as core::ffi::c_int as usize] as core::ffi::c_float;
            m[2 as core::ffi::c_int as usize][1 as core::ffi::c_int as usize] =
                vup[2 as core::ffi::c_int as usize] as core::ffi::c_float;
            m[0 as core::ffi::c_int as usize][2 as core::ffi::c_int as usize] =
                vf[0 as core::ffi::c_int as usize] as core::ffi::c_float;
            m[1 as core::ffi::c_int as usize][2 as core::ffi::c_int as usize] =
                vf[1 as core::ffi::c_int as usize] as core::ffi::c_float;
            m[2 as core::ffi::c_int as usize][2 as core::ffi::c_int as usize] =
                vf[2 as core::ffi::c_int as usize] as core::ffi::c_float;
            memcpy(
                im.as_mut_ptr() as *mut core::ffi::c_void,
                m.as_mut_ptr() as *const core::ffi::c_void,
                ::core::mem::size_of::<[[core::ffi::c_float; 3]; 3]>() as size_t,
            );
            im[0 as core::ffi::c_int as usize][1 as core::ffi::c_int as usize] =
                m[1 as core::ffi::c_int as usize][0 as core::ffi::c_int as usize];
            im[0 as core::ffi::c_int as usize][2 as core::ffi::c_int as usize] =
                m[2 as core::ffi::c_int as usize][0 as core::ffi::c_int as usize];
            im[1 as core::ffi::c_int as usize][0 as core::ffi::c_int as usize] =
                m[0 as core::ffi::c_int as usize][1 as core::ffi::c_int as usize];
            im[1 as core::ffi::c_int as usize][2 as core::ffi::c_int as usize] =
                m[2 as core::ffi::c_int as usize][1 as core::ffi::c_int as usize];
            im[2 as core::ffi::c_int as usize][0 as core::ffi::c_int as usize] =
                m[0 as core::ffi::c_int as usize][2 as core::ffi::c_int as usize];
            im[2 as core::ffi::c_int as usize][1 as core::ffi::c_int as usize] =
                m[1 as core::ffi::c_int as usize][2 as core::ffi::c_int as usize];
            memset(
                zrot.as_mut_ptr() as *mut core::ffi::c_void,
                0 as core::ffi::c_int,
                ::core::mem::size_of::<[[core::ffi::c_float; 3]; 3]>() as size_t,
            );
            zrot[2 as core::ffi::c_int as usize][2 as core::ffi::c_int as usize] = 1.0f32;
            zrot[1 as core::ffi::c_int as usize][1 as core::ffi::c_int as usize] =
                zrot[2 as core::ffi::c_int as usize][2 as core::ffi::c_int as usize];
            zrot[0 as core::ffi::c_int as usize][0 as core::ffi::c_int as usize] =
                zrot[1 as core::ffi::c_int as usize][1 as core::ffi::c_int as usize];
            rad = (degrees as core::ffi::c_double * M_PI / 180.0f64) as core::ffi::c_float;
            zrot[0 as core::ffi::c_int as usize][0 as core::ffi::c_int as usize] =
                cos(rad as core::ffi::c_double) as core::ffi::c_float;
            zrot[0 as core::ffi::c_int as usize][1 as core::ffi::c_int as usize] =
                sin(rad as core::ffi::c_double) as core::ffi::c_float;
            zrot[1 as core::ffi::c_int as usize][0 as core::ffi::c_int as usize] =
                -sin(rad as core::ffi::c_double) as core::ffi::c_float;
            zrot[1 as core::ffi::c_int as usize][1 as core::ffi::c_int as usize] =
                cos(rad as core::ffi::c_double) as core::ffi::c_float;
            MatrixMultiply(m.as_mut_ptr(), zrot.as_mut_ptr(), tmpmat.as_mut_ptr());
            MatrixMultiply(tmpmat.as_mut_ptr(), im.as_mut_ptr(), rot.as_mut_ptr());
            i = 0 as core::ffi::c_int;
            while i < 3 as core::ffi::c_int {
                *dst.offset(i as isize) = rot[i as usize][0 as core::ffi::c_int as usize]
                    * *point.offset(0 as core::ffi::c_int as isize)
                    + rot[i as usize][1 as core::ffi::c_int as usize]
                        * *point.offset(1 as core::ffi::c_int as isize)
                    + rot[i as usize][2 as core::ffi::c_int as usize]
                        * *point.offset(2 as core::ffi::c_int as isize);
                i += 1;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn RotateAroundDirection(axis: *mut vec3_t, yaw: core::ffi::c_float) {
            PerpendicularVector(
                (*axis.offset(1 as core::ffi::c_int as isize)).as_mut_ptr(),
                (*axis.offset(0 as core::ffi::c_int as isize)).as_ptr() as *const vec_t,
            );
            if yaw != 0. {
                let mut temp: vec3_t = [0.; 3];
                temp[0 as core::ffi::c_int as usize] =
                    (*axis.offset(1 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize];
                temp[1 as core::ffi::c_int as usize] =
                    (*axis.offset(1 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize];
                temp[2 as core::ffi::c_int as usize] =
                    (*axis.offset(1 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize];
                RotatePointAroundVector(
                    (*axis.offset(1 as core::ffi::c_int as isize)).as_mut_ptr(),
                    (*axis.offset(0 as core::ffi::c_int as isize)).as_ptr() as *const vec_t,
                    temp.as_ptr() as *const vec_t,
                    yaw,
                );
            }
            CrossProduct(
                (*axis.offset(0 as core::ffi::c_int as isize)).as_ptr() as *const vec_t,
                (*axis.offset(1 as core::ffi::c_int as isize)).as_ptr() as *const vec_t,
                (*axis.offset(2 as core::ffi::c_int as isize)).as_mut_ptr(),
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn vectoangles(value1: *const vec_t, angles: *mut vec_t) {
            let mut forward: core::ffi::c_float = 0.;
            let mut yaw: core::ffi::c_float = 0.;
            let mut pitch: core::ffi::c_float = 0.;
            if *value1.offset(1 as core::ffi::c_int as isize)
                == 0 as core::ffi::c_int as core::ffi::c_float
                && *value1.offset(0 as core::ffi::c_int as isize)
                    == 0 as core::ffi::c_int as core::ffi::c_float
            {
                yaw = 0 as core::ffi::c_int as core::ffi::c_float;
                if *value1.offset(2 as core::ffi::c_int as isize)
                    > 0 as core::ffi::c_int as core::ffi::c_float
                {
                    pitch = 90 as core::ffi::c_int as core::ffi::c_float;
                } else {
                    pitch = 270 as core::ffi::c_int as core::ffi::c_float;
                }
            } else {
                if *value1.offset(0 as core::ffi::c_int as isize) != 0. {
                    yaw = (atan2(
                        *value1.offset(1 as core::ffi::c_int as isize) as core::ffi::c_double,
                        *value1.offset(0 as core::ffi::c_int as isize) as core::ffi::c_double,
                    ) * 180 as core::ffi::c_int as core::ffi::c_double
                        / M_PI) as core::ffi::c_float;
                } else if *value1.offset(1 as core::ffi::c_int as isize)
                    > 0 as core::ffi::c_int as core::ffi::c_float
                {
                    yaw = 90 as core::ffi::c_int as core::ffi::c_float;
                } else {
                    yaw = 270 as core::ffi::c_int as core::ffi::c_float;
                }
                if yaw < 0 as core::ffi::c_int as core::ffi::c_float {
                    yaw += 360 as core::ffi::c_int as core::ffi::c_float;
                }
                forward = sqrt(
                    (*value1.offset(0 as core::ffi::c_int as isize)
                        * *value1.offset(0 as core::ffi::c_int as isize)
                        + *value1.offset(1 as core::ffi::c_int as isize)
                            * *value1.offset(1 as core::ffi::c_int as isize))
                        as core::ffi::c_double,
                ) as core::ffi::c_float;
                pitch = (atan2(
                    *value1.offset(2 as core::ffi::c_int as isize) as core::ffi::c_double,
                    forward as core::ffi::c_double,
                ) * 180 as core::ffi::c_int as core::ffi::c_double
                    / M_PI) as core::ffi::c_float;
                if pitch < 0 as core::ffi::c_int as core::ffi::c_float {
                    pitch += 360 as core::ffi::c_int as core::ffi::c_float;
                }
            }
            *angles.offset(PITCH as isize) = -pitch as vec_t;
            *angles.offset(YAW as isize) = yaw as vec_t;
            *angles.offset(ROLL as isize) = 0 as core::ffi::c_int as vec_t;
        }
        #[no_mangle]
        pub unsafe extern "C" fn AnglesToAxis(angles: *const vec_t, axis: *mut vec3_t) {
            let mut right: vec3_t = [0.; 3];
            AngleVectors(
                angles,
                (*axis.offset(0 as core::ffi::c_int as isize)).as_mut_ptr(),
                right.as_mut_ptr(),
                (*axis.offset(2 as core::ffi::c_int as isize)).as_mut_ptr(),
            );
            (*axis.offset(1 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize] =
                vec3_origin[0 as core::ffi::c_int as usize] - right[0 as core::ffi::c_int as usize];
            (*axis.offset(1 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize] =
                vec3_origin[1 as core::ffi::c_int as usize] - right[1 as core::ffi::c_int as usize];
            (*axis.offset(1 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize] =
                vec3_origin[2 as core::ffi::c_int as usize] - right[2 as core::ffi::c_int as usize];
        }
        #[no_mangle]
        pub unsafe extern "C" fn AxisClear(axis: *mut vec3_t) {
            (*axis.offset(0 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize] =
                1 as core::ffi::c_int as vec_t;
            (*axis.offset(0 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize] =
                0 as core::ffi::c_int as vec_t;
            (*axis.offset(0 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize] =
                0 as core::ffi::c_int as vec_t;
            (*axis.offset(1 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize] =
                0 as core::ffi::c_int as vec_t;
            (*axis.offset(1 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize] =
                1 as core::ffi::c_int as vec_t;
            (*axis.offset(1 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize] =
                0 as core::ffi::c_int as vec_t;
            (*axis.offset(2 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize] =
                0 as core::ffi::c_int as vec_t;
            (*axis.offset(2 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize] =
                0 as core::ffi::c_int as vec_t;
            (*axis.offset(2 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize] =
                1 as core::ffi::c_int as vec_t;
        }
        #[no_mangle]
        pub unsafe extern "C" fn AxisCopy(in_0: *mut vec3_t, out: *mut vec3_t) {
            (*out.offset(0 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize] =
                (*in_0.offset(0 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize];
            (*out.offset(0 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize] =
                (*in_0.offset(0 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize];
            (*out.offset(0 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize] =
                (*in_0.offset(0 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize];
            (*out.offset(1 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize] =
                (*in_0.offset(1 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize];
            (*out.offset(1 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize] =
                (*in_0.offset(1 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize];
            (*out.offset(1 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize] =
                (*in_0.offset(1 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize];
            (*out.offset(2 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize] =
                (*in_0.offset(2 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize];
            (*out.offset(2 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize] =
                (*in_0.offset(2 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize];
            (*out.offset(2 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize] =
                (*in_0.offset(2 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize];
        }
        #[no_mangle]
        pub unsafe extern "C" fn ProjectPointOnPlane(
            dst: *mut vec_t,
            p: *const vec_t,
            normal: *const vec_t,
        ) {
            let mut d: core::ffi::c_float = 0.;
            let mut n: vec3_t = [0.; 3];
            let mut inv_denom: core::ffi::c_float = 0.;
            inv_denom = (*normal.offset(0 as core::ffi::c_int as isize)
                * *normal.offset(0 as core::ffi::c_int as isize)
                + *normal.offset(1 as core::ffi::c_int as isize)
                    * *normal.offset(1 as core::ffi::c_int as isize)
                + *normal.offset(2 as core::ffi::c_int as isize)
                    * *normal.offset(2 as core::ffi::c_int as isize))
                as core::ffi::c_float;
            inv_denom = 1.0f32 / inv_denom;
            d = (*normal.offset(0 as core::ffi::c_int as isize) as core::ffi::c_float
                * *p.offset(0 as core::ffi::c_int as isize) as core::ffi::c_float
                + *normal.offset(1 as core::ffi::c_int as isize) as core::ffi::c_float
                    * *p.offset(1 as core::ffi::c_int as isize) as core::ffi::c_float
                + *normal.offset(2 as core::ffi::c_int as isize) as core::ffi::c_float
                    * *p.offset(2 as core::ffi::c_int as isize) as core::ffi::c_float)
                * inv_denom;
            n[0 as core::ffi::c_int as usize] = (*normal.offset(0 as core::ffi::c_int as isize)
                as core::ffi::c_float
                * inv_denom) as vec_t;
            n[1 as core::ffi::c_int as usize] = (*normal.offset(1 as core::ffi::c_int as isize)
                as core::ffi::c_float
                * inv_denom) as vec_t;
            n[2 as core::ffi::c_int as usize] = (*normal.offset(2 as core::ffi::c_int as isize)
                as core::ffi::c_float
                * inv_denom) as vec_t;
            *dst.offset(0 as core::ffi::c_int as isize) = *p.offset(0 as core::ffi::c_int as isize)
                - d as vec_t * n[0 as core::ffi::c_int as usize];
            *dst.offset(1 as core::ffi::c_int as isize) = *p.offset(1 as core::ffi::c_int as isize)
                - d as vec_t * n[1 as core::ffi::c_int as usize];
            *dst.offset(2 as core::ffi::c_int as isize) = *p.offset(2 as core::ffi::c_int as isize)
                - d as vec_t * n[2 as core::ffi::c_int as usize];
        }
        #[no_mangle]
        pub unsafe extern "C" fn MakeNormalVectors(
            forward: *const vec_t,
            right: *mut vec_t,
            up: *mut vec_t,
        ) {
            let mut d: core::ffi::c_float = 0.;
            *right.offset(1 as core::ffi::c_int as isize) =
                -*forward.offset(0 as core::ffi::c_int as isize);
            *right.offset(2 as core::ffi::c_int as isize) =
                *forward.offset(1 as core::ffi::c_int as isize);
            *right.offset(0 as core::ffi::c_int as isize) =
                *forward.offset(2 as core::ffi::c_int as isize);
            d = (*right.offset(0 as core::ffi::c_int as isize)
                * *forward.offset(0 as core::ffi::c_int as isize)
                + *right.offset(1 as core::ffi::c_int as isize)
                    * *forward.offset(1 as core::ffi::c_int as isize)
                + *right.offset(2 as core::ffi::c_int as isize)
                    * *forward.offset(2 as core::ffi::c_int as isize))
                as core::ffi::c_float;
            *right.offset(0 as core::ffi::c_int as isize) =
                (*right.offset(0 as core::ffi::c_int as isize) as core::ffi::c_float
                    + *forward.offset(0 as core::ffi::c_int as isize) as core::ffi::c_float * -d)
                    as vec_t;
            *right.offset(1 as core::ffi::c_int as isize) =
                (*right.offset(1 as core::ffi::c_int as isize) as core::ffi::c_float
                    + *forward.offset(1 as core::ffi::c_int as isize) as core::ffi::c_float * -d)
                    as vec_t;
            *right.offset(2 as core::ffi::c_int as isize) =
                (*right.offset(2 as core::ffi::c_int as isize) as core::ffi::c_float
                    + *forward.offset(2 as core::ffi::c_int as isize) as core::ffi::c_float * -d)
                    as vec_t;
            VectorNormalize(right);
            CrossProduct(right as *const vec_t, forward, up);
        }
        #[no_mangle]
        pub unsafe extern "C" fn VectorRotate(
            in_0: *mut vec_t,
            matrix: *mut vec3_t,
            out: *mut vec_t,
        ) {
            *out.offset(0 as core::ffi::c_int as isize) = *in_0
                .offset(0 as core::ffi::c_int as isize)
                * (*matrix.offset(0 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize]
                + *in_0.offset(1 as core::ffi::c_int as isize)
                    * (*matrix.offset(0 as core::ffi::c_int as isize))
                        [1 as core::ffi::c_int as usize]
                + *in_0.offset(2 as core::ffi::c_int as isize)
                    * (*matrix.offset(0 as core::ffi::c_int as isize))
                        [2 as core::ffi::c_int as usize];
            *out.offset(1 as core::ffi::c_int as isize) = *in_0
                .offset(0 as core::ffi::c_int as isize)
                * (*matrix.offset(1 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize]
                + *in_0.offset(1 as core::ffi::c_int as isize)
                    * (*matrix.offset(1 as core::ffi::c_int as isize))
                        [1 as core::ffi::c_int as usize]
                + *in_0.offset(2 as core::ffi::c_int as isize)
                    * (*matrix.offset(1 as core::ffi::c_int as isize))
                        [2 as core::ffi::c_int as usize];
            *out.offset(2 as core::ffi::c_int as isize) = *in_0
                .offset(0 as core::ffi::c_int as isize)
                * (*matrix.offset(2 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize]
                + *in_0.offset(1 as core::ffi::c_int as isize)
                    * (*matrix.offset(2 as core::ffi::c_int as isize))
                        [1 as core::ffi::c_int as usize]
                + *in_0.offset(2 as core::ffi::c_int as isize)
                    * (*matrix.offset(2 as core::ffi::c_int as isize))
                        [2 as core::ffi::c_int as usize];
        }
        #[no_mangle]
        pub unsafe extern "C" fn Q_rsqrt(number: core::ffi::c_float) -> core::ffi::c_float {
            let mut i: uint32_t = 0;
            let mut x2: core::ffi::c_float = 0.;
            let mut y: core::ffi::c_float = 0.;
            let threehalfs: core::ffi::c_float = 1.5f32;
            x2 = number * 0.5f32;
            y = number;
            memcpy(
                &mut i as *mut uint32_t as *mut core::ffi::c_void,
                &mut y as *mut core::ffi::c_float as *const core::ffi::c_void,
                ::core::mem::size_of::<core::ffi::c_float>() as size_t,
            );
            i = (0x5f3759df as uint32_t).wrapping_sub(i >> 1 as core::ffi::c_int);
            memcpy(
                &mut y as *mut core::ffi::c_float as *mut core::ffi::c_void,
                &mut i as *mut uint32_t as *const core::ffi::c_void,
                ::core::mem::size_of::<core::ffi::c_float>() as size_t,
            );
            y = y * (threehalfs - x2 * y * y);
            y
        }
        #[no_mangle]
        pub unsafe extern "C" fn Q_fabs(mut f: core::ffi::c_float) -> core::ffi::c_float {
            let mut tmp: core::ffi::c_int =
                *(&mut f as *mut core::ffi::c_float as *mut core::ffi::c_int);
            tmp &= 0x7fffffff as core::ffi::c_int;
            *(&mut tmp as *mut core::ffi::c_int as *mut core::ffi::c_float)
        }
        #[no_mangle]
        pub unsafe extern "C" fn LerpAngle(
            from: core::ffi::c_float,
            mut to: core::ffi::c_float,
            frac: core::ffi::c_float,
        ) -> core::ffi::c_float {
            let mut a: core::ffi::c_float = 0.;
            if to - from > 180 as core::ffi::c_int as core::ffi::c_float {
                to -= 360 as core::ffi::c_int as core::ffi::c_float;
            }
            if to - from < -(180 as core::ffi::c_int) as core::ffi::c_float {
                to += 360 as core::ffi::c_int as core::ffi::c_float;
            }
            a = from + frac * (to - from);
            a
        }
        #[no_mangle]
        pub unsafe extern "C" fn AngleSubtract(
            a1: core::ffi::c_float,
            a2: core::ffi::c_float,
        ) -> core::ffi::c_float {
            let mut a: core::ffi::c_float = 0.;
            a = a1 - a2;
            while a > 180 as core::ffi::c_int as core::ffi::c_float {
                a -= 360 as core::ffi::c_int as core::ffi::c_float;
            }
            while a < -(180 as core::ffi::c_int) as core::ffi::c_float {
                a += 360 as core::ffi::c_int as core::ffi::c_float;
            }
            a
        }
        #[no_mangle]
        pub unsafe extern "C" fn AnglesSubtract(v1: *mut vec_t, v2: *mut vec_t, v3: *mut vec_t) {
            *v3.offset(0 as core::ffi::c_int as isize) = AngleSubtract(
                *v1.offset(0 as core::ffi::c_int as isize) as core::ffi::c_float,
                *v2.offset(0 as core::ffi::c_int as isize) as core::ffi::c_float,
            ) as vec_t;
            *v3.offset(1 as core::ffi::c_int as isize) = AngleSubtract(
                *v1.offset(1 as core::ffi::c_int as isize) as core::ffi::c_float,
                *v2.offset(1 as core::ffi::c_int as isize) as core::ffi::c_float,
            ) as vec_t;
            *v3.offset(2 as core::ffi::c_int as isize) = AngleSubtract(
                *v1.offset(2 as core::ffi::c_int as isize) as core::ffi::c_float,
                *v2.offset(2 as core::ffi::c_int as isize) as core::ffi::c_float,
            ) as vec_t;
        }
        #[no_mangle]
        pub unsafe extern "C" fn AngleMod(mut a: core::ffi::c_float) -> core::ffi::c_float {
            a = (360.0f64 / 65536 as core::ffi::c_int as core::ffi::c_double
                * ((a as core::ffi::c_double
                    * (65536 as core::ffi::c_int as core::ffi::c_double / 360.0f64))
                    as core::ffi::c_int
                    & 65535 as core::ffi::c_int) as core::ffi::c_double)
                as core::ffi::c_float;
            a
        }
        #[no_mangle]
        pub unsafe extern "C" fn AngleNormalize360(
            angle: core::ffi::c_float,
        ) -> core::ffi::c_float {
            (360.0f64 / 65536 as core::ffi::c_int as core::ffi::c_double
                * ((angle as core::ffi::c_double
                    * (65536 as core::ffi::c_int as core::ffi::c_double / 360.0f64))
                    as core::ffi::c_int
                    & 65535 as core::ffi::c_int) as core::ffi::c_double)
                as core::ffi::c_float
        }
        #[no_mangle]
        pub unsafe extern "C" fn AngleNormalize180(
            mut angle: core::ffi::c_float,
        ) -> core::ffi::c_float {
            angle = AngleNormalize360(angle);
            if angle as core::ffi::c_double > 180.0f64 {
                angle = (angle as core::ffi::c_double - 360.0f64) as core::ffi::c_float;
            }
            angle
        }
        #[no_mangle]
        pub unsafe extern "C" fn AngleDelta(
            angle1: core::ffi::c_float,
            angle2: core::ffi::c_float,
        ) -> core::ffi::c_float {
            AngleNormalize180(angle1 - angle2)
        }
        #[no_mangle]
        pub unsafe extern "C" fn SetPlaneSignbits(out: *mut cplane_t) {
            let mut bits: core::ffi::c_int = 0;
            let mut j: core::ffi::c_int = 0;
            bits = 0 as core::ffi::c_int;
            j = 0 as core::ffi::c_int;
            while j < 3 as core::ffi::c_int {
                if (*out).normal[j as usize] < 0 as core::ffi::c_int as core::ffi::c_float {
                    bits |= (1 as core::ffi::c_int) << j;
                }
                j += 1;
            }
            (*out).signbits = bits as byte;
        }
        #[no_mangle]
        pub unsafe extern "C" fn BoxOnPlaneSide(
            emins: *mut vec_t,
            emaxs: *mut vec_t,
            p: *mut cplane_s,
        ) -> core::ffi::c_int {
            let mut dist1: core::ffi::c_float = 0.;
            let mut dist2: core::ffi::c_float = 0.;
            let mut sides: core::ffi::c_int = 0;
            if ((*p).type_0 as core::ffi::c_int) < 3 as core::ffi::c_int {
                if (*p).dist <= *emins.offset((*p).type_0 as isize) {
                    return 1 as core::ffi::c_int;
                }
                if (*p).dist >= *emaxs.offset((*p).type_0 as isize) {
                    return 2 as core::ffi::c_int;
                }
                return 3 as core::ffi::c_int;
            }
            match (*p).signbits as core::ffi::c_int {
                0 => {
                    dist1 = ((*p).normal[0 as core::ffi::c_int as usize]
                        * *emaxs.offset(0 as core::ffi::c_int as isize)
                        + (*p).normal[1 as core::ffi::c_int as usize]
                            * *emaxs.offset(1 as core::ffi::c_int as isize)
                        + (*p).normal[2 as core::ffi::c_int as usize]
                            * *emaxs.offset(2 as core::ffi::c_int as isize))
                        as core::ffi::c_float;
                    dist2 = ((*p).normal[0 as core::ffi::c_int as usize]
                        * *emins.offset(0 as core::ffi::c_int as isize)
                        + (*p).normal[1 as core::ffi::c_int as usize]
                            * *emins.offset(1 as core::ffi::c_int as isize)
                        + (*p).normal[2 as core::ffi::c_int as usize]
                            * *emins.offset(2 as core::ffi::c_int as isize))
                        as core::ffi::c_float;
                }
                1 => {
                    dist1 = ((*p).normal[0 as core::ffi::c_int as usize]
                        * *emins.offset(0 as core::ffi::c_int as isize)
                        + (*p).normal[1 as core::ffi::c_int as usize]
                            * *emaxs.offset(1 as core::ffi::c_int as isize)
                        + (*p).normal[2 as core::ffi::c_int as usize]
                            * *emaxs.offset(2 as core::ffi::c_int as isize))
                        as core::ffi::c_float;
                    dist2 = ((*p).normal[0 as core::ffi::c_int as usize]
                        * *emaxs.offset(0 as core::ffi::c_int as isize)
                        + (*p).normal[1 as core::ffi::c_int as usize]
                            * *emins.offset(1 as core::ffi::c_int as isize)
                        + (*p).normal[2 as core::ffi::c_int as usize]
                            * *emins.offset(2 as core::ffi::c_int as isize))
                        as core::ffi::c_float;
                }
                2 => {
                    dist1 = ((*p).normal[0 as core::ffi::c_int as usize]
                        * *emaxs.offset(0 as core::ffi::c_int as isize)
                        + (*p).normal[1 as core::ffi::c_int as usize]
                            * *emins.offset(1 as core::ffi::c_int as isize)
                        + (*p).normal[2 as core::ffi::c_int as usize]
                            * *emaxs.offset(2 as core::ffi::c_int as isize))
                        as core::ffi::c_float;
                    dist2 = ((*p).normal[0 as core::ffi::c_int as usize]
                        * *emins.offset(0 as core::ffi::c_int as isize)
                        + (*p).normal[1 as core::ffi::c_int as usize]
                            * *emaxs.offset(1 as core::ffi::c_int as isize)
                        + (*p).normal[2 as core::ffi::c_int as usize]
                            * *emins.offset(2 as core::ffi::c_int as isize))
                        as core::ffi::c_float;
                }
                3 => {
                    dist1 = ((*p).normal[0 as core::ffi::c_int as usize]
                        * *emins.offset(0 as core::ffi::c_int as isize)
                        + (*p).normal[1 as core::ffi::c_int as usize]
                            * *emins.offset(1 as core::ffi::c_int as isize)
                        + (*p).normal[2 as core::ffi::c_int as usize]
                            * *emaxs.offset(2 as core::ffi::c_int as isize))
                        as core::ffi::c_float;
                    dist2 = ((*p).normal[0 as core::ffi::c_int as usize]
                        * *emaxs.offset(0 as core::ffi::c_int as isize)
                        + (*p).normal[1 as core::ffi::c_int as usize]
                            * *emaxs.offset(1 as core::ffi::c_int as isize)
                        + (*p).normal[2 as core::ffi::c_int as usize]
                            * *emins.offset(2 as core::ffi::c_int as isize))
                        as core::ffi::c_float;
                }
                4 => {
                    dist1 = ((*p).normal[0 as core::ffi::c_int as usize]
                        * *emaxs.offset(0 as core::ffi::c_int as isize)
                        + (*p).normal[1 as core::ffi::c_int as usize]
                            * *emaxs.offset(1 as core::ffi::c_int as isize)
                        + (*p).normal[2 as core::ffi::c_int as usize]
                            * *emins.offset(2 as core::ffi::c_int as isize))
                        as core::ffi::c_float;
                    dist2 = ((*p).normal[0 as core::ffi::c_int as usize]
                        * *emins.offset(0 as core::ffi::c_int as isize)
                        + (*p).normal[1 as core::ffi::c_int as usize]
                            * *emins.offset(1 as core::ffi::c_int as isize)
                        + (*p).normal[2 as core::ffi::c_int as usize]
                            * *emaxs.offset(2 as core::ffi::c_int as isize))
                        as core::ffi::c_float;
                }
                5 => {
                    dist1 = ((*p).normal[0 as core::ffi::c_int as usize]
                        * *emins.offset(0 as core::ffi::c_int as isize)
                        + (*p).normal[1 as core::ffi::c_int as usize]
                            * *emaxs.offset(1 as core::ffi::c_int as isize)
                        + (*p).normal[2 as core::ffi::c_int as usize]
                            * *emins.offset(2 as core::ffi::c_int as isize))
                        as core::ffi::c_float;
                    dist2 = ((*p).normal[0 as core::ffi::c_int as usize]
                        * *emaxs.offset(0 as core::ffi::c_int as isize)
                        + (*p).normal[1 as core::ffi::c_int as usize]
                            * *emins.offset(1 as core::ffi::c_int as isize)
                        + (*p).normal[2 as core::ffi::c_int as usize]
                            * *emaxs.offset(2 as core::ffi::c_int as isize))
                        as core::ffi::c_float;
                }
                6 => {
                    dist1 = ((*p).normal[0 as core::ffi::c_int as usize]
                        * *emaxs.offset(0 as core::ffi::c_int as isize)
                        + (*p).normal[1 as core::ffi::c_int as usize]
                            * *emins.offset(1 as core::ffi::c_int as isize)
                        + (*p).normal[2 as core::ffi::c_int as usize]
                            * *emins.offset(2 as core::ffi::c_int as isize))
                        as core::ffi::c_float;
                    dist2 = ((*p).normal[0 as core::ffi::c_int as usize]
                        * *emins.offset(0 as core::ffi::c_int as isize)
                        + (*p).normal[1 as core::ffi::c_int as usize]
                            * *emaxs.offset(1 as core::ffi::c_int as isize)
                        + (*p).normal[2 as core::ffi::c_int as usize]
                            * *emaxs.offset(2 as core::ffi::c_int as isize))
                        as core::ffi::c_float;
                }
                7 => {
                    dist1 = ((*p).normal[0 as core::ffi::c_int as usize]
                        * *emins.offset(0 as core::ffi::c_int as isize)
                        + (*p).normal[1 as core::ffi::c_int as usize]
                            * *emins.offset(1 as core::ffi::c_int as isize)
                        + (*p).normal[2 as core::ffi::c_int as usize]
                            * *emins.offset(2 as core::ffi::c_int as isize))
                        as core::ffi::c_float;
                    dist2 = ((*p).normal[0 as core::ffi::c_int as usize]
                        * *emaxs.offset(0 as core::ffi::c_int as isize)
                        + (*p).normal[1 as core::ffi::c_int as usize]
                            * *emaxs.offset(1 as core::ffi::c_int as isize)
                        + (*p).normal[2 as core::ffi::c_int as usize]
                            * *emaxs.offset(2 as core::ffi::c_int as isize))
                        as core::ffi::c_float;
                }
                _ => {
                    dist2 = 0 as core::ffi::c_int as core::ffi::c_float;
                    dist1 = dist2;
                }
            }
            sides = 0 as core::ffi::c_int;
            if dist1 >= (*p).dist {
                sides = 1 as core::ffi::c_int;
            }
            if dist2 < (*p).dist {
                sides |= 2 as core::ffi::c_int;
            }
            sides
        }
        #[no_mangle]
        pub unsafe extern "C" fn RadiusFromBounds(
            mins: *const vec_t,
            maxs: *const vec_t,
        ) -> core::ffi::c_float {
            let mut i: core::ffi::c_int = 0;
            let mut corner: vec3_t = [0.; 3];
            let mut a: core::ffi::c_float = 0.;
            let mut b: core::ffi::c_float = 0.;
            i = 0 as core::ffi::c_int;
            while i < 3 as core::ffi::c_int {
                a = fabs(*mins.offset(i as isize) as core::ffi::c_double) as core::ffi::c_float;
                b = fabs(*maxs.offset(i as isize) as core::ffi::c_double) as core::ffi::c_float;
                corner[i as usize] = (if a > b { a } else { b }) as vec_t;
                i += 1;
            }
            VectorLength(corner.as_ptr() as *const vec_t) as core::ffi::c_float
        }
        #[no_mangle]
        pub unsafe extern "C" fn ClearBounds(mins: *mut vec_t, maxs: *mut vec_t) {
            *mins.offset(2 as core::ffi::c_int as isize) = 99999 as core::ffi::c_int as vec_t;
            *mins.offset(1 as core::ffi::c_int as isize) =
                *mins.offset(2 as core::ffi::c_int as isize);
            *mins.offset(0 as core::ffi::c_int as isize) =
                *mins.offset(1 as core::ffi::c_int as isize);
            *maxs.offset(2 as core::ffi::c_int as isize) = -(99999 as core::ffi::c_int) as vec_t;
            *maxs.offset(1 as core::ffi::c_int as isize) =
                *maxs.offset(2 as core::ffi::c_int as isize);
            *maxs.offset(0 as core::ffi::c_int as isize) =
                *maxs.offset(1 as core::ffi::c_int as isize);
        }
        #[no_mangle]
        pub unsafe extern "C" fn AddPointToBounds(
            v: *const vec_t,
            mins: *mut vec_t,
            maxs: *mut vec_t,
        ) {
            if *v.offset(0 as core::ffi::c_int as isize)
                < *mins.offset(0 as core::ffi::c_int as isize)
            {
                *mins.offset(0 as core::ffi::c_int as isize) =
                    *v.offset(0 as core::ffi::c_int as isize);
            }
            if *v.offset(0 as core::ffi::c_int as isize)
                > *maxs.offset(0 as core::ffi::c_int as isize)
            {
                *maxs.offset(0 as core::ffi::c_int as isize) =
                    *v.offset(0 as core::ffi::c_int as isize);
            }
            if *v.offset(1 as core::ffi::c_int as isize)
                < *mins.offset(1 as core::ffi::c_int as isize)
            {
                *mins.offset(1 as core::ffi::c_int as isize) =
                    *v.offset(1 as core::ffi::c_int as isize);
            }
            if *v.offset(1 as core::ffi::c_int as isize)
                > *maxs.offset(1 as core::ffi::c_int as isize)
            {
                *maxs.offset(1 as core::ffi::c_int as isize) =
                    *v.offset(1 as core::ffi::c_int as isize);
            }
            if *v.offset(2 as core::ffi::c_int as isize)
                < *mins.offset(2 as core::ffi::c_int as isize)
            {
                *mins.offset(2 as core::ffi::c_int as isize) =
                    *v.offset(2 as core::ffi::c_int as isize);
            }
            if *v.offset(2 as core::ffi::c_int as isize)
                > *maxs.offset(2 as core::ffi::c_int as isize)
            {
                *maxs.offset(2 as core::ffi::c_int as isize) =
                    *v.offset(2 as core::ffi::c_int as isize);
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn VectorNormalize(v: *mut vec_t) -> vec_t {
            let mut length: core::ffi::c_float = 0.;
            let mut ilength: core::ffi::c_float = 0.;
            length = (*v.offset(0 as core::ffi::c_int as isize)
                * *v.offset(0 as core::ffi::c_int as isize)
                + *v.offset(1 as core::ffi::c_int as isize)
                    * *v.offset(1 as core::ffi::c_int as isize)
                + *v.offset(2 as core::ffi::c_int as isize)
                    * *v.offset(2 as core::ffi::c_int as isize))
                as core::ffi::c_float;
            length = sqrt(length as core::ffi::c_double) as core::ffi::c_float;
            if length != 0. {
                ilength = 1 as core::ffi::c_int as core::ffi::c_float / length;
                *v.offset(0 as core::ffi::c_int as isize) *= ilength;
                *v.offset(1 as core::ffi::c_int as isize) *= ilength;
                *v.offset(2 as core::ffi::c_int as isize) *= ilength;
            }
            length as vec_t
        }
        #[no_mangle]
        pub unsafe extern "C" fn VectorNormalize2(v: *const vec_t, out: *mut vec_t) -> vec_t {
            let mut length: core::ffi::c_float = 0.;
            let mut ilength: core::ffi::c_float = 0.;
            length = (*v.offset(0 as core::ffi::c_int as isize)
                * *v.offset(0 as core::ffi::c_int as isize)
                + *v.offset(1 as core::ffi::c_int as isize)
                    * *v.offset(1 as core::ffi::c_int as isize)
                + *v.offset(2 as core::ffi::c_int as isize)
                    * *v.offset(2 as core::ffi::c_int as isize))
                as core::ffi::c_float;
            length = sqrt(length as core::ffi::c_double) as core::ffi::c_float;
            if length != 0. {
                ilength = 1 as core::ffi::c_int as core::ffi::c_float / length;
                *out.offset(0 as core::ffi::c_int as isize) =
                    (*v.offset(0 as core::ffi::c_int as isize) as core::ffi::c_float * ilength)
                        as vec_t;
                *out.offset(1 as core::ffi::c_int as isize) =
                    (*v.offset(1 as core::ffi::c_int as isize) as core::ffi::c_float * ilength)
                        as vec_t;
                *out.offset(2 as core::ffi::c_int as isize) =
                    (*v.offset(2 as core::ffi::c_int as isize) as core::ffi::c_float * ilength)
                        as vec_t;
            } else {
                *out.offset(2 as core::ffi::c_int as isize) = 0 as core::ffi::c_int as vec_t;
                *out.offset(1 as core::ffi::c_int as isize) =
                    *out.offset(2 as core::ffi::c_int as isize);
                *out.offset(0 as core::ffi::c_int as isize) =
                    *out.offset(1 as core::ffi::c_int as isize);
            }
            length as vec_t
        }
        #[no_mangle]
        pub unsafe extern "C" fn _VectorMA(
            veca: *const vec_t,
            scale: core::ffi::c_float,
            vecb: *const vec_t,
            vecc: *mut vec_t,
        ) {
            *vecc.offset(0 as core::ffi::c_int as isize) = *veca
                .offset(0 as core::ffi::c_int as isize)
                + scale as vec_t * *vecb.offset(0 as core::ffi::c_int as isize);
            *vecc.offset(1 as core::ffi::c_int as isize) = *veca
                .offset(1 as core::ffi::c_int as isize)
                + scale as vec_t * *vecb.offset(1 as core::ffi::c_int as isize);
            *vecc.offset(2 as core::ffi::c_int as isize) = *veca
                .offset(2 as core::ffi::c_int as isize)
                + scale as vec_t * *vecb.offset(2 as core::ffi::c_int as isize);
        }
        #[no_mangle]
        pub unsafe extern "C" fn _DotProduct(v1: *const vec_t, v2: *const vec_t) -> vec_t {
            *v1.offset(0 as core::ffi::c_int as isize) * *v2.offset(0 as core::ffi::c_int as isize)
                + *v1.offset(1 as core::ffi::c_int as isize)
                    * *v2.offset(1 as core::ffi::c_int as isize)
                + *v1.offset(2 as core::ffi::c_int as isize)
                    * *v2.offset(2 as core::ffi::c_int as isize)
        }
        #[no_mangle]
        pub unsafe extern "C" fn _VectorSubtract(
            veca: *const vec_t,
            vecb: *const vec_t,
            out: *mut vec_t,
        ) {
            *out.offset(0 as core::ffi::c_int as isize) = *veca
                .offset(0 as core::ffi::c_int as isize)
                - *vecb.offset(0 as core::ffi::c_int as isize);
            *out.offset(1 as core::ffi::c_int as isize) = *veca
                .offset(1 as core::ffi::c_int as isize)
                - *vecb.offset(1 as core::ffi::c_int as isize);
            *out.offset(2 as core::ffi::c_int as isize) = *veca
                .offset(2 as core::ffi::c_int as isize)
                - *vecb.offset(2 as core::ffi::c_int as isize);
        }
        #[no_mangle]
        pub unsafe extern "C" fn _VectorAdd(
            veca: *const vec_t,
            vecb: *const vec_t,
            out: *mut vec_t,
        ) {
            *out.offset(0 as core::ffi::c_int as isize) = *veca
                .offset(0 as core::ffi::c_int as isize)
                + *vecb.offset(0 as core::ffi::c_int as isize);
            *out.offset(1 as core::ffi::c_int as isize) = *veca
                .offset(1 as core::ffi::c_int as isize)
                + *vecb.offset(1 as core::ffi::c_int as isize);
            *out.offset(2 as core::ffi::c_int as isize) = *veca
                .offset(2 as core::ffi::c_int as isize)
                + *vecb.offset(2 as core::ffi::c_int as isize);
        }
        #[no_mangle]
        pub unsafe extern "C" fn _VectorCopy(in_0: *const vec_t, out: *mut vec_t) {
            *out.offset(0 as core::ffi::c_int as isize) =
                *in_0.offset(0 as core::ffi::c_int as isize);
            *out.offset(1 as core::ffi::c_int as isize) =
                *in_0.offset(1 as core::ffi::c_int as isize);
            *out.offset(2 as core::ffi::c_int as isize) =
                *in_0.offset(2 as core::ffi::c_int as isize);
        }
        #[no_mangle]
        pub unsafe extern "C" fn _VectorScale(in_0: *const vec_t, scale: vec_t, out: *mut vec_t) {
            *out.offset(0 as core::ffi::c_int as isize) =
                *in_0.offset(0 as core::ffi::c_int as isize) * scale;
            *out.offset(1 as core::ffi::c_int as isize) =
                *in_0.offset(1 as core::ffi::c_int as isize) * scale;
            *out.offset(2 as core::ffi::c_int as isize) =
                *in_0.offset(2 as core::ffi::c_int as isize) * scale;
        }
        #[no_mangle]
        pub unsafe extern "C" fn Vector4Scale(in_0: *const vec_t, scale: vec_t, out: *mut vec_t) {
            *out.offset(0 as core::ffi::c_int as isize) =
                *in_0.offset(0 as core::ffi::c_int as isize) * scale;
            *out.offset(1 as core::ffi::c_int as isize) =
                *in_0.offset(1 as core::ffi::c_int as isize) * scale;
            *out.offset(2 as core::ffi::c_int as isize) =
                *in_0.offset(2 as core::ffi::c_int as isize) * scale;
            *out.offset(3 as core::ffi::c_int as isize) =
                *in_0.offset(3 as core::ffi::c_int as isize) * scale;
        }
        #[no_mangle]
        pub unsafe extern "C" fn Q_log2(mut val: core::ffi::c_int) -> core::ffi::c_int {
            let mut answer: core::ffi::c_int = 0;
            answer = 0 as core::ffi::c_int;
            loop {
                val >>= 1 as core::ffi::c_int;
                if val == 0 as core::ffi::c_int {
                    break;
                }
                answer += 1;
            }
            answer
        }
        #[no_mangle]
        pub unsafe extern "C" fn MatrixMultiply(
            in1: *mut [core::ffi::c_float; 3],
            in2: *mut [core::ffi::c_float; 3],
            out: *mut [core::ffi::c_float; 3],
        ) {
            (*out.offset(0 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize] = (*in1
                .offset(0 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize]
                * (*in2.offset(0 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize]
                + (*in1.offset(0 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize]
                    * (*in2.offset(1 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize]
                + (*in1.offset(0 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize]
                    * (*in2.offset(2 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize];
            (*out.offset(0 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize] = (*in1
                .offset(0 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize]
                * (*in2.offset(0 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize]
                + (*in1.offset(0 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize]
                    * (*in2.offset(1 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize]
                + (*in1.offset(0 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize]
                    * (*in2.offset(2 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize];
            (*out.offset(0 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize] = (*in1
                .offset(0 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize]
                * (*in2.offset(0 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize]
                + (*in1.offset(0 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize]
                    * (*in2.offset(1 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize]
                + (*in1.offset(0 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize]
                    * (*in2.offset(2 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize];
            (*out.offset(1 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize] = (*in1
                .offset(1 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize]
                * (*in2.offset(0 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize]
                + (*in1.offset(1 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize]
                    * (*in2.offset(1 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize]
                + (*in1.offset(1 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize]
                    * (*in2.offset(2 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize];
            (*out.offset(1 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize] = (*in1
                .offset(1 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize]
                * (*in2.offset(0 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize]
                + (*in1.offset(1 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize]
                    * (*in2.offset(1 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize]
                + (*in1.offset(1 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize]
                    * (*in2.offset(2 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize];
            (*out.offset(1 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize] = (*in1
                .offset(1 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize]
                * (*in2.offset(0 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize]
                + (*in1.offset(1 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize]
                    * (*in2.offset(1 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize]
                + (*in1.offset(1 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize]
                    * (*in2.offset(2 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize];
            (*out.offset(2 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize] = (*in1
                .offset(2 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize]
                * (*in2.offset(0 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize]
                + (*in1.offset(2 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize]
                    * (*in2.offset(1 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize]
                + (*in1.offset(2 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize]
                    * (*in2.offset(2 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize];
            (*out.offset(2 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize] = (*in1
                .offset(2 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize]
                * (*in2.offset(0 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize]
                + (*in1.offset(2 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize]
                    * (*in2.offset(1 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize]
                + (*in1.offset(2 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize]
                    * (*in2.offset(2 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize];
            (*out.offset(2 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize] = (*in1
                .offset(2 as core::ffi::c_int as isize))[0 as core::ffi::c_int as usize]
                * (*in2.offset(0 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize]
                + (*in1.offset(2 as core::ffi::c_int as isize))[1 as core::ffi::c_int as usize]
                    * (*in2.offset(1 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize]
                + (*in1.offset(2 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize]
                    * (*in2.offset(2 as core::ffi::c_int as isize))[2 as core::ffi::c_int as usize];
        }
        #[no_mangle]
        pub unsafe extern "C" fn AngleVectors(
            angles: *const vec_t,
            forward: *mut vec_t,
            right: *mut vec_t,
            up: *mut vec_t,
        ) {
            let mut angle: core::ffi::c_float = 0.;
            static mut sr: core::ffi::c_float = 0.;
            static mut sp: core::ffi::c_float = 0.;
            static mut sy: core::ffi::c_float = 0.;
            static mut cr: core::ffi::c_float = 0.;
            static mut cp: core::ffi::c_float = 0.;
            static mut cy: core::ffi::c_float = 0.;
            angle = (*angles.offset(YAW as isize) as core::ffi::c_double
                * (M_PI * 2 as core::ffi::c_int as core::ffi::c_double
                    / 360 as core::ffi::c_int as core::ffi::c_double))
                as core::ffi::c_float;
            sy = sin(angle as core::ffi::c_double) as core::ffi::c_float;
            cy = cos(angle as core::ffi::c_double) as core::ffi::c_float;
            angle = (*angles.offset(PITCH as isize) as core::ffi::c_double
                * (M_PI * 2 as core::ffi::c_int as core::ffi::c_double
                    / 360 as core::ffi::c_int as core::ffi::c_double))
                as core::ffi::c_float;
            sp = sin(angle as core::ffi::c_double) as core::ffi::c_float;
            cp = cos(angle as core::ffi::c_double) as core::ffi::c_float;
            angle = (*angles.offset(ROLL as isize) as core::ffi::c_double
                * (M_PI * 2 as core::ffi::c_int as core::ffi::c_double
                    / 360 as core::ffi::c_int as core::ffi::c_double))
                as core::ffi::c_float;
            sr = sin(angle as core::ffi::c_double) as core::ffi::c_float;
            cr = cos(angle as core::ffi::c_double) as core::ffi::c_float;
            if !forward.is_null() {
                *forward.offset(0 as core::ffi::c_int as isize) = (cp * cy) as vec_t;
                *forward.offset(1 as core::ffi::c_int as isize) = (cp * sy) as vec_t;
                *forward.offset(2 as core::ffi::c_int as isize) = -sp as vec_t;
            }
            if !right.is_null() {
                *right.offset(0 as core::ffi::c_int as isize) =
                    (-(1 as core::ffi::c_int) as core::ffi::c_float * sr * sp * cy
                        + -(1 as core::ffi::c_int) as core::ffi::c_float * cr * -sy)
                        as vec_t;
                *right.offset(1 as core::ffi::c_int as isize) =
                    (-(1 as core::ffi::c_int) as core::ffi::c_float * sr * sp * sy
                        + -(1 as core::ffi::c_int) as core::ffi::c_float * cr * cy)
                        as vec_t;
                *right.offset(2 as core::ffi::c_int as isize) =
                    (-(1 as core::ffi::c_int) as core::ffi::c_float * sr * cp) as vec_t;
            }
            if !up.is_null() {
                *up.offset(0 as core::ffi::c_int as isize) = (cr * sp * cy + -sr * -sy) as vec_t;
                *up.offset(1 as core::ffi::c_int as isize) = (cr * sp * sy + -sr * cy) as vec_t;
                *up.offset(2 as core::ffi::c_int as isize) = (cr * cp) as vec_t;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn PerpendicularVector(dst: *mut vec_t, src: *const vec_t) {
            let mut pos: core::ffi::c_int = 0;
            let mut i: core::ffi::c_int = 0;
            let mut minelem: core::ffi::c_float = 1.0f32;
            let mut tempvec: vec3_t = [0.; 3];
            pos = 0 as core::ffi::c_int;
            i = 0 as core::ffi::c_int;
            while i < 3 as core::ffi::c_int {
                if fabs(*src.offset(i as isize) as core::ffi::c_double)
                    < minelem as core::ffi::c_double
                {
                    pos = i;
                    minelem =
                        fabs(*src.offset(i as isize) as core::ffi::c_double) as core::ffi::c_float;
                }
                i += 1;
            }
            tempvec[2 as core::ffi::c_int as usize] = 0.0f32 as vec_t;
            tempvec[1 as core::ffi::c_int as usize] = tempvec[2 as core::ffi::c_int as usize];
            tempvec[0 as core::ffi::c_int as usize] = tempvec[1 as core::ffi::c_int as usize];
            tempvec[pos as usize] = 1.0f32 as vec_t;
            ProjectPointOnPlane(dst, tempvec.as_ptr() as *const vec_t, src);
            VectorNormalize(dst);
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case("qmath", SOURCE);
}
