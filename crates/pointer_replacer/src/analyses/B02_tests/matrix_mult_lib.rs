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
    pub mod driver {
        use crate::src::matrix::free_matrix;
        use crate::src::matrix::initialize_matrix_from_string;
        use crate::src::matrix::matrix_to_string;
        use crate::src::matrix::multiply_matrices;
        use crate::src::write::write_to_file;
        extern "C" {
            fn free(__ptr: *mut core::ffi::c_void);
        }
        #[repr(C)]
        pub struct matrix_t {
            pub matrix: *mut *mut core::ffi::c_int,
            pub width: core::ffi::c_int,
            pub height: core::ffi::c_int,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for matrix_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for matrix_t {
            #[inline]
            fn clone(&self) -> matrix_t {
                let _: ::core::clone::AssertParamIsClone<*mut *mut core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                *self
            }
        }
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const EXIT_FAILURE: core::ffi::c_int = 1 as core::ffi::c_int;
        pub const EXIT_SUCCESS: core::ffi::c_int = 0 as core::ffi::c_int;
        pub const OUT_FILE: [core::ffi::c_char; 11] = [
            b'm' as i8,
            b'a' as i8,
            b't' as i8,
            b'r' as i8,
            b'i' as i8,
            b'x' as i8,
            b'.' as i8,
            b't' as i8,
            b'x' as i8,
            b't' as i8,
            b'\0' as i8,
        ];
        #[no_mangle]
        pub unsafe extern "C" fn driver(
            width_a: core::ffi::c_int,
            height_a: core::ffi::c_int,
            matrix_a: *const core::ffi::c_char,
            width_b: core::ffi::c_int,
            height_b: core::ffi::c_int,
            matrix_b: *const core::ffi::c_char,
        ) -> core::ffi::c_int {
            let mat_a: *mut matrix_t = initialize_matrix_from_string(matrix_a, width_a, height_a);
            if mat_a.is_null() {
                return EXIT_FAILURE;
            }
            let mat_b: *mut matrix_t = initialize_matrix_from_string(matrix_b, width_b, height_b);
            if mat_b.is_null() {
                free_matrix(mat_a);
                return EXIT_FAILURE;
            }
            let res: *mut matrix_t = multiply_matrices(mat_a, mat_b);
            if res.is_null() {
                free_matrix(mat_a);
                free_matrix(mat_b);
                return EXIT_FAILURE;
            }
            let res_str: *mut core::ffi::c_char = matrix_to_string(res);
            if res_str.is_null() {
                free_matrix(mat_a);
                free_matrix(mat_b);
                free(res as *mut core::ffi::c_void);
                return EXIT_FAILURE;
            }
            let res_write: core::ffi::c_int = write_to_file(OUT_FILE.as_ptr(), res_str);
            free_matrix(mat_a);
            free_matrix(mat_b);
            free_matrix(res);
            free(res_str as *mut core::ffi::c_void);
            if res_write != 0 as core::ffi::c_int {
                return EXIT_FAILURE;
            }
            EXIT_SUCCESS
        }
    }
    pub mod matrix {
        use crate::src::driver::matrix_t;
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
            fn snprintf(
                __s: *mut core::ffi::c_char,
                __maxlen: size_t,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn perror(__s: *const core::ffi::c_char);
            fn atoi(__nptr: *const core::ffi::c_char) -> core::ffi::c_int;
            fn malloc(__size: size_t) -> *mut core::ffi::c_void;
            fn free(__ptr: *mut core::ffi::c_void);
            fn strcat(
                __dest: *mut core::ffi::c_char,
                __src: *const core::ffi::c_char,
            ) -> *mut core::ffi::c_char;
            fn strdup(__s: *const core::ffi::c_char) -> *mut core::ffi::c_char;
            fn strtok_r(
                __s: *mut core::ffi::c_char,
                __delim: *const core::ffi::c_char,
                __save_ptr: *mut *mut core::ffi::c_char,
            ) -> *mut core::ffi::c_char;
        }
        pub type size_t = usize;
        pub type __off_t = core::ffi::c_long;
        pub type __off64_t = core::ffi::c_long;
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
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        #[no_mangle]
        pub unsafe extern "C" fn allocate_matrix(
            width: core::ffi::c_int,
            height: core::ffi::c_int,
        ) -> *mut matrix_t {
            let mat: *mut matrix_t =
                malloc(::core::mem::size_of::<matrix_t>() as size_t) as *mut matrix_t;
            if mat.is_null() {
                perror(
                    b"Failed to allocate memory for matrix struct\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return std::ptr::null_mut::<matrix_t>();
            }
            (*mat).width = width;
            (*mat).height = height;
            (*mat).matrix = malloc(
                (height as size_t)
                    .wrapping_mul(::core::mem::size_of::<*mut core::ffi::c_int>() as size_t),
            ) as *mut *mut core::ffi::c_int;
            if ((*mat).matrix).is_null() {
                perror(
                    b"Failed to allocate memory for matrix rows\0" as *const u8
                        as *const core::ffi::c_char,
                );
                free(mat as *mut core::ffi::c_void);
                return std::ptr::null_mut::<matrix_t>();
            }
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < height {
                *((*mat).matrix).offset(i as isize) = malloc(
                    (width as size_t)
                        .wrapping_mul(::core::mem::size_of::<core::ffi::c_int>() as size_t),
                ) as *mut core::ffi::c_int;
                if (*((*mat).matrix).offset(i as isize)).is_null() {
                    perror(
                        b"Failed to allocate memory for matrix columns\0" as *const u8
                            as *const core::ffi::c_char,
                    );
                    let mut j: core::ffi::c_int = 0 as core::ffi::c_int;
                    while j <= i {
                        free(*((*mat).matrix).offset(j as isize) as *mut core::ffi::c_void);
                        j += 1;
                    }
                    free((*mat).matrix as *mut core::ffi::c_void);
                    free(mat as *mut core::ffi::c_void);
                    return std::ptr::null_mut::<matrix_t>();
                }
                i += 1;
            }
            mat
        }
        #[no_mangle]
        pub unsafe extern "C" fn free_matrix(mat: *mut matrix_t) {
            if mat.is_null() {
                return;
            }
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < (*mat).height {
                free(*((*mat).matrix).offset(i as isize) as *mut core::ffi::c_void);
                i += 1;
            }
            free((*mat).matrix as *mut core::ffi::c_void);
            free(mat as *mut core::ffi::c_void);
        }
        #[no_mangle]
        pub unsafe extern "C" fn initialize_matrix_from_string(
            input: *const core::ffi::c_char,
            width: core::ffi::c_int,
            height: core::ffi::c_int,
        ) -> *mut matrix_t {
            let mat: *mut matrix_t = allocate_matrix(width, height);
            let input_copy: *mut core::ffi::c_char = strdup(input);
            if input_copy.is_null() {
                perror(
                    b"Failed to duplicate input string\0" as *const u8 as *const core::ffi::c_char,
                );
                free_matrix(mat);
                return std::ptr::null_mut::<matrix_t>();
            }
            let mut saveptr_row: *mut core::ffi::c_char = std::ptr::null_mut::<core::ffi::c_char>();
            let mut row_token: *mut core::ffi::c_char = strtok_r(
                input_copy,
                b"\n\0" as *const u8 as *const core::ffi::c_char,
                &mut saveptr_row,
            );
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < height {
                if row_token.is_null() {
                    fprintf(
                        stderr,
                        b"Insufficient rows in input string.\n\0" as *const u8
                            as *const core::ffi::c_char,
                    );
                    free(input_copy as *mut core::ffi::c_void);
                    free_matrix(mat);
                    return std::ptr::null_mut::<matrix_t>();
                }
                let mut saveptr_col: *mut core::ffi::c_char =
                    std::ptr::null_mut::<core::ffi::c_char>();
                let mut col_token: *mut core::ffi::c_char = strtok_r(
                    row_token,
                    b" \0" as *const u8 as *const core::ffi::c_char,
                    &mut saveptr_col,
                );
                let mut j: core::ffi::c_int = 0 as core::ffi::c_int;
                while j < width {
                    if col_token.is_null() {
                        fprintf(
                            stderr,
                            b"Insufficient columns in row %d.\n\0" as *const u8
                                as *const core::ffi::c_char,
                            i + 1 as core::ffi::c_int,
                        );
                        free(input_copy as *mut core::ffi::c_void);
                        free_matrix(mat);
                        return std::ptr::null_mut::<matrix_t>();
                    }
                    *(*((*mat).matrix).offset(i as isize)).offset(j as isize) = atoi(col_token);
                    col_token = strtok_r(
                        std::ptr::null_mut::<core::ffi::c_char>(),
                        b" \0" as *const u8 as *const core::ffi::c_char,
                        &mut saveptr_col,
                    );
                    j += 1;
                }
                row_token = strtok_r(
                    std::ptr::null_mut::<core::ffi::c_char>(),
                    b"\n\0" as *const u8 as *const core::ffi::c_char,
                    &mut saveptr_row,
                );
                i += 1;
            }
            free(input_copy as *mut core::ffi::c_void);
            mat
        }
        #[no_mangle]
        pub unsafe extern "C" fn multiply_matrices(
            mat_a: *mut matrix_t,
            mat_b: *mut matrix_t,
        ) -> *mut matrix_t {
            if (*mat_a).width != (*mat_b).height {
                fprintf(
                    stderr,
                    b"Matrix dimensions do not allow multiplication.\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return std::ptr::null_mut::<matrix_t>();
            }
            let result: *mut matrix_t = allocate_matrix((*mat_b).width, (*mat_a).height);
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < (*mat_a).height {
                let mut j: core::ffi::c_int = 0 as core::ffi::c_int;
                while j < (*mat_b).width {
                    *(*((*result).matrix).offset(i as isize)).offset(j as isize) =
                        0 as core::ffi::c_int;
                    let mut k: core::ffi::c_int = 0 as core::ffi::c_int;
                    while k < (*mat_a).width {
                        *(*((*result).matrix).offset(i as isize)).offset(j as isize) +=
                            *(*((*mat_a).matrix).offset(i as isize)).offset(k as isize)
                                * *(*((*mat_b).matrix).offset(k as isize)).offset(j as isize);
                        k += 1;
                    }
                    j += 1;
                }
                i += 1;
            }
            result
        }
        #[no_mangle]
        pub unsafe extern "C" fn matrix_to_string(mat: *mut matrix_t) -> *mut core::ffi::c_char {
            if mat.is_null() {
                fprintf(
                    stderr,
                    b"Error: Matrix is NULL.\n\0" as *const u8 as *const core::ffi::c_char,
                );
                return std::ptr::null_mut::<core::ffi::c_char>();
            }
            let buffer_size: core::ffi::c_int = (*mat).height
                * ((*mat).width * 10 as core::ffi::c_int + (*mat).width)
                + (*mat).height
                + 1 as core::ffi::c_int;
            let result: *mut core::ffi::c_char =
                malloc(buffer_size as size_t) as *mut core::ffi::c_char;
            if result.is_null() {
                perror(
                    b"Failed to allocate memory for matrix string\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return std::ptr::null_mut::<core::ffi::c_char>();
            }
            *result.offset(0 as core::ffi::c_int as isize) = '\0' as i32 as core::ffi::c_char;
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < (*mat).height {
                let mut j: core::ffi::c_int = 0 as core::ffi::c_int;
                while j < (*mat).width {
                    let mut buffer: [core::ffi::c_char; 12] = [0; 12];
                    snprintf(
                        buffer.as_mut_ptr(),
                        ::core::mem::size_of::<[core::ffi::c_char; 12]>() as size_t,
                        b"%d\0" as *const u8 as *const core::ffi::c_char,
                        *(*((*mat).matrix).offset(i as isize)).offset(j as isize),
                    );
                    strcat(result, buffer.as_ptr());
                    if j < (*mat).width - 1 as core::ffi::c_int {
                        strcat(result, b" \0" as *const u8 as *const core::ffi::c_char);
                    }
                    j += 1;
                }
                strcat(result, b"\n\0" as *const u8 as *const core::ffi::c_char);
                i += 1;
            }
            result
        }
    }
    pub mod write {
        use crate::src::matrix::FILE;
        extern "C" {
            static mut stderr: *mut FILE;
            fn fclose(__stream: *mut FILE) -> core::ffi::c_int;
            fn fopen(
                __filename: *const core::ffi::c_char,
                __modes: *const core::ffi::c_char,
            ) -> *mut FILE;
            fn fprintf(
                __stream: *mut FILE,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn __errno_location() -> *mut core::ffi::c_int;
            fn strerror(__errnum: core::ffi::c_int) -> *mut core::ffi::c_char;
        }
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const EINVAL: core::ffi::c_int = 22 as core::ffi::c_int;
        #[no_mangle]
        pub unsafe extern "C" fn write_to_file(
            filename: *const core::ffi::c_char,
            content: *const core::ffi::c_char,
        ) -> core::ffi::c_int {
            if content.is_null() {
                fprintf(
                    stderr,
                    b"Error: Content is NULL.\n\0" as *const u8 as *const core::ffi::c_char,
                );
                return EINVAL;
            }
            let file: *mut FILE = fopen(filename, b"w\0" as *const u8 as *const core::ffi::c_char);
            if file.is_null() {
                fprintf(
                    stderr,
                    b"Error opening file '%s': %s\n\0" as *const u8 as *const core::ffi::c_char,
                    filename,
                    strerror(*__errno_location()),
                );
                return *__errno_location();
            }
            if fprintf(
                file,
                b"%s\0" as *const u8 as *const core::ffi::c_char,
                content,
            ) < 0 as core::ffi::c_int
            {
                fprintf(
                    stderr,
                    b"Error writing to file '%s': %s\n\0" as *const u8 as *const core::ffi::c_char,
                    filename,
                    strerror(*__errno_location()),
                );
                fclose(file);
                return *__errno_location();
            }
            if fclose(file) != 0 as core::ffi::c_int {
                fprintf(
                    stderr,
                    b"Error closing file '%s': %s\n\0" as *const u8 as *const core::ffi::c_char,
                    filename,
                    strerror(*__errno_location()),
                );
                return *__errno_location();
            }
            0 as core::ffi::c_int
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates(
        "matrix_mult_lib",
        SOURCE,
        &["initialize_matrix_from_string#input_copy", "allocate_matrix#mat"],
        &[],
    );
}
