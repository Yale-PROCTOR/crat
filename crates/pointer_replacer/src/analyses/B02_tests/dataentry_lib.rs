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
            fn sprintf(
                __s: *mut core::ffi::c_char,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn malloc(__size: size_t) -> *mut core::ffi::c_void;
            fn free(__ptr: *mut core::ffi::c_void);
            fn strcpy(
                __dest: *mut core::ffi::c_char,
                __src: *const core::ffi::c_char,
            ) -> *mut core::ffi::c_char;
            fn strlen(__s: *const core::ffi::c_char) -> size_t;
        }
        pub type size_t = usize;
        #[repr(C)]
        pub struct DataEntry {
            pub id: core::ffi::c_int,
            pub value: core::ffi::c_int,
            pub name: [core::ffi::c_char; 32],
        }
        #[automatically_derived]
        impl ::core::marker::Copy for DataEntry {}
        #[automatically_derived]
        impl ::core::clone::Clone for DataEntry {
            #[inline]
            fn clone(&self) -> DataEntry {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 32]>;
                *self
            }
        }
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const NAME_LENGTH: core::ffi::c_int = 32 as core::ffi::c_int;
        static mut lookup_table: [[core::ffi::c_int; 3]; 4] = [
            [
                10 as core::ffi::c_int,
                20 as core::ffi::c_int,
                30 as core::ffi::c_int,
            ],
            [
                40 as core::ffi::c_int,
                50 as core::ffi::c_int,
                60 as core::ffi::c_int,
            ],
            [
                70 as core::ffi::c_int,
                80 as core::ffi::c_int,
                90 as core::ffi::c_int,
            ],
            [
                100 as core::ffi::c_int,
                110 as core::ffi::c_int,
                120 as core::ffi::c_int,
            ],
        ];
        unsafe extern "C" fn find_entry(
            entries: *mut DataEntry,
            count: core::ffi::c_int,
            target_id: core::ffi::c_int,
        ) -> *mut DataEntry {
            let mut ptr: *mut DataEntry = entries;
            let end: *mut DataEntry = entries.offset(count as isize);
            while ptr < end {
                if (*ptr).id == target_id {
                    return ptr;
                }
                ptr = ptr.offset(1);
            }
            std::ptr::null_mut::<DataEntry>()
        }
        unsafe extern "C" fn process_name(
            dest: *mut core::ffi::c_char,
            src: *const core::ffi::c_char,
            max_len: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let mut len: core::ffi::c_int = 0;
            if dest.is_null() || *dest as core::ffi::c_int == '\0' as i32 {
                return -(1 as core::ffi::c_int);
            }
            strcpy(dest, src);
            len = strlen(dest) as core::ffi::c_int;
            len
        }
        unsafe extern "C" fn calculate_lookup(
            row: core::ffi::c_int,
            col: core::ffi::c_int,
            result: *mut core::ffi::c_int,
        ) -> core::ffi::c_int {
            let mut temp: core::ffi::c_int = 0;
            temp = lookup_table[row as usize][col as usize];
            if temp != 0 {
                *result = temp * 2 as core::ffi::c_int;
                return 1 as core::ffi::c_int;
            }
            0 as core::ffi::c_int
        }
        unsafe extern "C" fn create_entries(
            count: core::ffi::c_int,
            base_id: core::ffi::c_int,
        ) -> *mut DataEntry {
            let mut entries: *mut DataEntry = std::ptr::null_mut::<DataEntry>();
            let mut i: core::ffi::c_int = 0;
            let mut temp_name: [core::ffi::c_char; 32] = [0; 32];
            entries = malloc(
                (count as size_t).wrapping_mul(::core::mem::size_of::<DataEntry>() as size_t),
            ) as *mut DataEntry;
            if entries.is_null() || count <= 0 as core::ffi::c_int {
                return std::ptr::null_mut::<DataEntry>();
            }
            i = 0 as core::ffi::c_int;
            while i < count {
                (*entries.offset(i as isize)).id = base_id + i;
                (*entries.offset(i as isize)).value = (base_id + i) * 10 as core::ffi::c_int;
                sprintf(
                    temp_name.as_mut_ptr(),
                    b"Entry_%d\0" as *const u8 as *const core::ffi::c_char,
                    base_id + i,
                );
                strcpy(
                    ((*entries.offset(i as isize)).name).as_mut_ptr(),
                    temp_name.as_ptr(),
                );
                i += 1;
            }
            entries
        }
        unsafe extern "C" fn modify_entries(
            entries: *mut DataEntry,
            count: core::ffi::c_int,
            multiplier: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let mut current: *mut DataEntry = std::ptr::null_mut::<DataEntry>();
            let mut last: *mut DataEntry = std::ptr::null_mut::<DataEntry>();
            let mut total: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut temp_value: core::ffi::c_int = 0;
            if entries.is_null() {
                return -(1 as core::ffi::c_int);
            }
            current = entries;
            last = entries.offset(count as isize);
            while current < last {
                temp_value = (*current).value;
                if temp_value != 0 {
                    (*current).value = temp_value * multiplier;
                    total += (*current).value;
                }
                current = current.offset(1);
            }
            total
        }
        #[no_mangle]
        pub unsafe extern "C" fn dataentry(
            mode: core::ffi::c_int,
            param1: core::ffi::c_int,
            param2: core::ffi::c_int,
            param3: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let mut entries: *mut DataEntry = std::ptr::null_mut::<DataEntry>();
            let mut found: *mut DataEntry = std::ptr::null_mut::<DataEntry>();
            let mut result: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut count: core::ffi::c_int = 0;
            let mut lookup_result: core::ffi::c_int = 0;
            let mut buffer: [core::ffi::c_char; 32] = [0; 32];
            let i: core::ffi::c_int = 0;
            buffer[0 as core::ffi::c_int as usize] = 'T' as i32 as core::ffi::c_char;
            buffer[1 as core::ffi::c_int as usize] = '\0' as i32 as core::ffi::c_char;
            match mode {
                1 => {
                    count = if param1 > 0 as core::ffi::c_int {
                        param1
                    } else {
                        5 as core::ffi::c_int
                    };
                    entries = create_entries(count, 100 as core::ffi::c_int);
                    if entries.is_null() || count == 0 as core::ffi::c_int {
                        result = -(1 as core::ffi::c_int);
                    } else {
                        found = find_entry(entries, count, 100 as core::ffi::c_int + param2);
                        if found.is_null() || (*found).id == 0 as core::ffi::c_int {
                            result = -(2 as core::ffi::c_int);
                        } else {
                            result = (*found).value;
                            strcpy(buffer.as_mut_ptr(), ((*found).name).as_ptr());
                        }
                        free(entries as *mut core::ffi::c_void);
                    }
                }
                2 => {
                    count = if param1 > 0 as core::ffi::c_int {
                        param1
                    } else {
                        3 as core::ffi::c_int
                    };
                    entries = create_entries(count, 200 as core::ffi::c_int);
                    if entries.is_null() {
                        result = -(1 as core::ffi::c_int);
                    } else {
                        result = modify_entries(entries, count, param2);
                        if result != 0 {
                            result += param3;
                        }
                        free(entries as *mut core::ffi::c_void);
                    }
                }
                3 => {
                    if param1 >= 0 as core::ffi::c_int
                        && param1 < 4 as core::ffi::c_int
                        && param2 >= 0 as core::ffi::c_int
                        && param2 < 3 as core::ffi::c_int
                    {
                        result = calculate_lookup(param1, param2, &mut lookup_result);
                        if result != 0 {
                            result = lookup_result + param3;
                        }
                    }
                }
                _ => {
                    strcpy(
                        buffer.as_mut_ptr(),
                        b"Default\0" as *const u8 as *const core::ffi::c_char,
                    );
                    result = process_name(
                        buffer.as_mut_ptr(),
                        b"TestName\0" as *const u8 as *const core::ffi::c_char,
                        NAME_LENGTH,
                    );
                    count = strlen(buffer.as_ptr()) as core::ffi::c_int;
                    if count != 0 {
                        result = count * param1;
                    }
                }
            }
            result
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates("dataentry_lib", SOURCE, &["create_entries#entries"], &[]);
}
