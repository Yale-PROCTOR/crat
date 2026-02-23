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
            fn printf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
            fn strcmp(
                __s1: *const core::ffi::c_char,
                __s2: *const core::ffi::c_char,
            ) -> core::ffi::c_int;
            fn time(__timer: *mut time_t) -> time_t;
        }
        pub type size_t = usize;
        pub type __time_t = core::ffi::c_long;
        pub type time_t = __time_t;
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        #[no_mangle]
        pub unsafe extern "C" fn classify_mode(mode: *const core::ffi::c_char) -> core::ffi::c_int {
            if strcmp(mode, b"standard\0" as *const u8 as *const core::ffi::c_char)
                == 0 as core::ffi::c_int
            {
                return 0x10 as core::ffi::c_int;
            } else if strcmp(mode, b"enhanced\0" as *const u8 as *const core::ffi::c_char)
                == 0 as core::ffi::c_int
            {
                return 0x20 as core::ffi::c_int;
            } else if strcmp(mode, b"turbo\0" as *const u8 as *const core::ffi::c_char)
                == 0 as core::ffi::c_int
            {
                return 0x30 as core::ffi::c_int;
            } else if strcmp(mode, b"extreme\0" as *const u8 as *const core::ffi::c_char)
                == 0 as core::ffi::c_int
            {
                return 0x40 as core::ffi::c_int;
            }
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn apply_multiplier(
            mut base: core::ffi::c_int,
            level: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let mut current_block_5: u64;
            match level {
                4 => {
                    base += 0xff as core::ffi::c_int;
                    current_block_5 = 17978390595819632496;
                }
                3 => {
                    current_block_5 = 17978390595819632496;
                }
                2 => {
                    current_block_5 = 16013381478083460001;
                }
                1 => {
                    current_block_5 = 10344925754825801646;
                }
                0 => {
                    current_block_5 = 6995965253482708452;
                }
                _ => {
                    base = 0xdead as core::ffi::c_int;
                    current_block_5 = 6937071982253665452;
                }
            }
            if current_block_5 == 17978390595819632496 {
                base += 0xab as core::ffi::c_int;
                current_block_5 = 16013381478083460001;
            }
            if current_block_5 == 16013381478083460001 {
                base += 0x7e as core::ffi::c_int;
                current_block_5 = 10344925754825801646;
            }
            if current_block_5 == 10344925754825801646 {
                base += 0x1c as core::ffi::c_int;
                current_block_5 = 6995965253482708452;
            }
            if current_block_5 == 6995965253482708452 {
                base += 0x5 as core::ffi::c_int;
            }
            base
        }
        #[no_mangle]
        pub unsafe extern "C" fn convert_time_factor(
            factor: core::ffi::c_double,
        ) -> core::ffi::c_int {
            let scaled: core::ffi::c_double = factor * 1e12f64;
            let result: core::ffi::c_int = scaled as core::ffi::c_int;
            result
        }
        #[no_mangle]
        pub unsafe extern "C" fn convert_negative_overflow(
            value: core::ffi::c_double,
        ) -> core::ffi::c_int {
            let extreme: core::ffi::c_double = value * -1e15f64;
            let result: core::ffi::c_int = extreme as core::ffi::c_int;
            result
        }
        #[no_mangle]
        pub unsafe extern "C" fn get_modified_time(
            offset_days: core::ffi::c_int,
            offset_hours: core::ffi::c_int,
        ) -> time_t {
            let mut current: time_t = time(std::ptr::null_mut::<time_t>());
            current >>= 22 as core::ffi::c_int;
            let offset: time_t = (offset_days * 86400 as core::ffi::c_int
                + offset_hours * 3600 as core::ffi::c_int)
                as time_t;
            current + offset
        }
        #[no_mangle]
        pub unsafe extern "C" fn hash_time_value(mut t: time_t) -> core::ffi::c_int {
            let mut hash: core::ffi::c_int = 0x5a5a5a5a as core::ffi::c_int;
            let bytes: *mut core::ffi::c_uchar = &mut t as *mut time_t as *mut core::ffi::c_uchar;
            let mut i: size_t = 0 as size_t;
            while i < ::core::mem::size_of::<time_t>() {
                hash ^= (*bytes.add(i) as core::ffi::c_int)
                    << i.wrapping_rem(4 as size_t).wrapping_mul(8 as size_t);
                hash *= 0x1f as core::ffi::c_int;
                i = i.wrapping_add(1);
            }
            hash & 0x7fffffff as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn modeselect(
            mode_selector: core::ffi::c_int,
            time_offset: core::ffi::c_int,
            complexity: core::ffi::c_int,
            seed: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let mut result: core::ffi::c_int = 0 as core::ffi::c_int;
            let modes: [*const core::ffi::c_char; 4] = [
                b"standard\0" as *const u8 as *const core::ffi::c_char,
                b"enhanced\0" as *const u8 as *const core::ffi::c_char,
                b"turbo\0" as *const u8 as *const core::ffi::c_char,
                b"extreme\0" as *const u8 as *const core::ffi::c_char,
            ];
            let mode_index: core::ffi::c_int = mode_selector % 4 as core::ffi::c_int;
            let selected_mode: *const core::ffi::c_char = modes[mode_index as usize];
            let mode_value: core::ffi::c_int = classify_mode(selected_mode);
            printf(
                b"Selected mode: %s (0x%X)\n\0" as *const u8 as *const core::ffi::c_char,
                selected_mode,
                mode_value,
            );
            result += mode_value;
            let complexity_level: core::ffi::c_int = complexity % 5 as core::ffi::c_int;
            let multiplier: core::ffi::c_int =
                apply_multiplier(0xa0 as core::ffi::c_int, complexity_level);
            printf(
                b"Complexity level: %d, Multiplier: 0x%X\n\0" as *const u8
                    as *const core::ffi::c_char,
                complexity_level,
                multiplier,
            );
            result += multiplier;
            let modified_time: time_t =
                get_modified_time(time_offset, seed % 24 as core::ffi::c_int);
            let time_hash: core::ffi::c_int = hash_time_value(modified_time);
            printf(
                b"Modified time: %ld, Hash: 0x%X\n\0" as *const u8 as *const core::ffi::c_char,
                modified_time,
                time_hash,
            );
            result += time_hash % 0x1000 as core::ffi::c_int;
            let factor1: core::ffi::c_double = seed as core::ffi::c_double * 1e8f64;
            let factor2: core::ffi::c_double = time_offset as core::ffi::c_double * -1e7f64;
            printf(
                b"Converting double %.2e to int (may overflow)...\n\0" as *const u8
                    as *const core::ffi::c_char,
                factor1,
            );
            let result1: core::ffi::c_int = convert_time_factor(factor1);
            printf(
                b"Result 1: %d (0x%X)\n\0" as *const u8 as *const core::ffi::c_char,
                result1,
                result1,
            );
            printf(
                b"Converting double %.2e to int (may underflow)...\n\0" as *const u8
                    as *const core::ffi::c_char,
                factor2,
            );
            let result2: core::ffi::c_int = convert_negative_overflow(factor2);
            printf(
                b"Result 2: %d (0x%X)\n\0" as *const u8 as *const core::ffi::c_char,
                result2,
                result2,
            );
            result ^= result1 & 0xff as core::ffi::c_int;
            result ^= result2 & 0xff00 as core::ffi::c_int;
            result = result * 0x10 as core::ffi::c_int + 0xbeef as core::ffi::c_int;
            printf(
                b"\nFinal result: %d (0x%X)\n\0" as *const u8 as *const core::ffi::c_char,
                result,
                result,
            );
            result
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates("modeselect_lib", SOURCE, &[], &[]);
}
