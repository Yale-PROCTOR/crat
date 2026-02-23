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
    pub mod luggage {
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
            fn scanf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
            fn calloc(__nmemb: size_t, __size: size_t) -> *mut core::ffi::c_void;
            fn exit(__status: core::ffi::c_int) -> !;
            fn strcpy(
                __dest: *mut core::ffi::c_char,
                __src: *const core::ffi::c_char,
            ) -> *mut core::ffi::c_char;
            fn strcmp(
                __s1: *const core::ffi::c_char,
                __s2: *const core::ffi::c_char,
            ) -> core::ffi::c_int;
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
        #[repr(C)]
        pub struct RoutingDirective {
            pub time_stamp: core::ffi::c_uint,
            pub luggage_id: [core::ffi::c_char; 9],
            pub flight_id: [core::ffi::c_char; 7],
            pub departure: [core::ffi::c_char; 4],
            pub arrival: [core::ffi::c_char; 4],
            pub comments: [core::ffi::c_char; 81],
            pub next_directive: *mut RoutingDirective,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for RoutingDirective {}
        #[automatically_derived]
        impl ::core::clone::Clone for RoutingDirective {
            #[inline]
            fn clone(&self) -> RoutingDirective {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_uint>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 9]>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 7]>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 4]>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 4]>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 81]>;
                let _: ::core::clone::AssertParamIsClone<*mut RoutingDirective>;
                *self
            }
        }
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const EOF: core::ffi::c_int = -(1 as core::ffi::c_int);
        #[no_mangle]
        pub unsafe extern "C" fn addRoutingDirectiveToList(
            previous_directive: *mut RoutingDirective,
            new_directive: *mut RoutingDirective,
        ) {
            let next_directive: *mut RoutingDirective =
                (*previous_directive).next_directive as *mut RoutingDirective;
            if next_directive.is_null()
                || (*next_directive).time_stamp > (*new_directive).time_stamp
            {
                (*new_directive).next_directive = next_directive as *mut RoutingDirective;
                (*previous_directive).next_directive = new_directive as *mut RoutingDirective;
            } else {
                addRoutingDirectiveToList(next_directive, new_directive);
            };
        }
        #[no_mangle]
        pub unsafe extern "C" fn supersedes(
            directive: *mut RoutingDirective,
            luggage_id: *mut core::ffi::c_char,
            departure: *mut core::ffi::c_char,
        ) -> core::ffi::c_int {
            if directive.is_null() {
                return 0 as core::ffi::c_int;
            }
            if strcmp(((*directive).luggage_id).as_ptr(), luggage_id) != 0 as core::ffi::c_int {
                return supersedes(
                    (*directive).next_directive as *mut RoutingDirective,
                    luggage_id,
                    departure,
                );
            }
            if strcmp(((*directive).departure).as_ptr(), departure) == 0 as core::ffi::c_int {
                return 1 as core::ffi::c_int;
            }
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn superseded(directive: *mut RoutingDirective) -> core::ffi::c_int {
            supersedes(
                (*directive).next_directive as *mut RoutingDirective,
                ((*directive).luggage_id).as_mut_ptr(),
                ((*directive).departure).as_mut_ptr(),
            )
        }
        #[no_mangle]
        pub unsafe extern "C" fn matches(
            expected: *mut core::ffi::c_char,
            actual: *mut core::ffi::c_char,
        ) -> core::ffi::c_int {
            (*expected.offset(0 as core::ffi::c_int as isize) as core::ffi::c_int == '-' as i32
                || strcmp(expected, actual) == 0 as core::ffi::c_int)
                as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn printMatchingDirectives(
            first_directive: *mut RoutingDirective,
            expected_luggage_id: *mut core::ffi::c_char,
            expected_flight_id: *mut core::ffi::c_char,
            expected_departure: *mut core::ffi::c_char,
            expected_arrival: *mut core::ffi::c_char,
        ) {
            let mut directive: *mut RoutingDirective = std::ptr::null_mut::<RoutingDirective>();
            directive = first_directive;
            while !directive.is_null() {
                if superseded(directive) == 0
                    && matches(expected_luggage_id, ((*directive).luggage_id).as_mut_ptr()) != 0
                    && matches(expected_flight_id, ((*directive).flight_id).as_mut_ptr()) != 0
                    && matches(expected_departure, ((*directive).departure).as_mut_ptr()) != 0
                    && matches(expected_arrival, ((*directive).arrival).as_mut_ptr()) != 0
                {
                    printf(
                        b"%010u %s %s %s %s %s\n\0" as *const u8 as *const core::ffi::c_char,
                        (*directive).time_stamp,
                        ((*directive).luggage_id).as_ptr(),
                        ((*directive).flight_id).as_ptr(),
                        ((*directive).departure).as_ptr(),
                        ((*directive).arrival).as_ptr(),
                        ((*directive).comments).as_ptr(),
                    );
                }
                directive = (*directive).next_directive as *mut RoutingDirective;
            }
        }
        unsafe fn main_0(
            argc: core::ffi::c_int,
            argv: *mut *mut core::ffi::c_char,
        ) -> core::ffi::c_int {
            if argc != 5 as core::ffi::c_int {
                fprintf(
                    stderr,
                    b"Command line error: 4 arguments expected\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                exit(1 as core::ffi::c_int);
            }
            let mut directive_list_head: RoutingDirective = RoutingDirective {
                time_stamp: 0,
                luggage_id: [0; 9],
                flight_id: [0; 7],
                departure: [0; 4],
                arrival: [0; 4],
                comments: [0; 81],
                next_directive: std::ptr::null_mut::<RoutingDirective>(),
            };
            directive_list_head.time_stamp = 0 as core::ffi::c_uint;
            directive_list_head.next_directive = std::ptr::null_mut::<RoutingDirective>();
            loop {
                let mut time_stamp: core::ffi::c_uint = 0;
                let mut luggage_id: [core::ffi::c_char; 9] = [0; 9];
                let mut flight_id: [core::ffi::c_char; 7] = [0; 7];
                let mut departure: [core::ffi::c_char; 4] = [0; 4];
                let mut arrival: [core::ffi::c_char; 4] = [0; 4];
                let mut comments: [core::ffi::c_char; 81] = [0; 81];
                comments[0 as core::ffi::c_int as usize] = 0 as core::ffi::c_char;
                if scanf(
                    b"%d \0" as *const u8 as *const core::ffi::c_char,
                    &mut time_stamp as *mut core::ffi::c_uint,
                ) == EOF
                {
                    break;
                }
                if scanf(
                    b"%8[A-Z0-9] %6[A-Z0-9] \0" as *const u8 as *const core::ffi::c_char,
                    luggage_id.as_mut_ptr(),
                    flight_id.as_mut_ptr(),
                ) == EOF
                {
                    break;
                }
                if scanf(
                    b"%3[A-Z] %3[A-Z]\0" as *const u8 as *const core::ffi::c_char,
                    departure.as_mut_ptr(),
                    arrival.as_mut_ptr(),
                ) == EOF
                {
                    break;
                }
                if scanf(
                    b"%80[^\n]\0" as *const u8 as *const core::ffi::c_char,
                    comments.as_mut_ptr(),
                ) == EOF
                {
                    break;
                }
                let new_directive: *mut RoutingDirective = calloc(
                    1 as size_t,
                    ::core::mem::size_of::<RoutingDirective>() as size_t,
                )
                    as *mut RoutingDirective;
                (*new_directive).time_stamp = time_stamp;
                strcpy(
                    ((*new_directive).luggage_id).as_mut_ptr(),
                    luggage_id.as_ptr(),
                );
                strcpy(
                    ((*new_directive).flight_id).as_mut_ptr(),
                    flight_id.as_ptr(),
                );
                strcpy(
                    ((*new_directive).departure).as_mut_ptr(),
                    departure.as_ptr(),
                );
                strcpy(((*new_directive).arrival).as_mut_ptr(), arrival.as_ptr());
                strcpy(((*new_directive).comments).as_mut_ptr(), comments.as_ptr());
                (*new_directive).next_directive = std::ptr::null_mut::<RoutingDirective>();
                addRoutingDirectiveToList(&mut directive_list_head, new_directive);
            }
            printMatchingDirectives(
                directive_list_head.next_directive as *mut RoutingDirective,
                *argv.offset(1 as core::ffi::c_int as isize),
                *argv.offset(2 as core::ffi::c_int as isize),
                *argv.offset(3 as core::ffi::c_int as isize),
                *argv.offset(4 as core::ffi::c_int as isize),
            );
            exit(0 as core::ffi::c_int);
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
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates("underhanded-c-luggage", SOURCE, &[], &[]);
}
