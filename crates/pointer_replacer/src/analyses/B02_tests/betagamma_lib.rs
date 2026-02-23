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
            fn malloc(__size: size_t) -> *mut core::ffi::c_void;
            fn calloc(__nmemb: size_t, __size: size_t) -> *mut core::ffi::c_void;
            fn free(__ptr: *mut core::ffi::c_void);
            fn strcpy(
                __dest: *mut core::ffi::c_char,
                __src: *const core::ffi::c_char,
            ) -> *mut core::ffi::c_char;
        }
        pub type size_t = usize;
        pub type __uint8_t = u8;
        pub type uint8_t = __uint8_t;
        #[repr(C)]
        pub struct DataBlock {
            pub id: core::ffi::c_int,
            pub name: [core::ffi::c_char; 32],
            pub flags: uint8_t,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for DataBlock {}
        #[automatically_derived]
        impl ::core::clone::Clone for DataBlock {
            #[inline]
            fn clone(&self) -> DataBlock {
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 32]>;
                let _: ::core::clone::AssertParamIsClone<uint8_t>;
                *self
            }
        }
        #[repr(C)]
        pub struct MemoryBlock {
            pub data: *mut core::ffi::c_int,
            pub size: size_t,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for MemoryBlock {}
        #[automatically_derived]
        impl ::core::clone::Clone for MemoryBlock {
            #[inline]
            fn clone(&self) -> MemoryBlock {
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<size_t>;
                *self
            }
        }
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        #[no_mangle]
        pub unsafe extern "C" fn create_block(
            id: core::ffi::c_int,
            name: *const core::ffi::c_char,
            flags: uint8_t,
        ) -> DataBlock {
            let mut block: DataBlock = DataBlock {
                id: 0,
                name: [0; 32],
                flags: 0,
            };
            block.id = id;
            strcpy((block.name).as_mut_ptr(), name);
            block.flags = flags;
            block
        }
        #[no_mangle]
        pub unsafe extern "C" fn allocate_block(
            count: size_t,
            init_value: core::ffi::c_int,
        ) -> *mut MemoryBlock {
            let mb: *mut MemoryBlock =
                malloc(::core::mem::size_of::<MemoryBlock>() as size_t) as *mut MemoryBlock;
            if mb.is_null() {
                return std::ptr::null_mut::<MemoryBlock>();
            }
            (*mb).data = calloc(count, ::core::mem::size_of::<core::ffi::c_int>() as size_t)
                as *mut core::ffi::c_int;
            if ((*mb).data).is_null() {
                free(mb as *mut core::ffi::c_void);
                return std::ptr::null_mut::<MemoryBlock>();
            }
            (*mb).size = count;
            let mut i: size_t = 0 as size_t;
            while i < count {
                *((*mb).data).add(i) = (init_value as size_t).wrapping_add(i) as core::ffi::c_int;
                i = i.wrapping_add(1);
            }
            mb
        }
        #[no_mangle]
        pub unsafe extern "C" fn free_block(mb: *mut MemoryBlock) {
            if !mb.is_null() {
                if !((*mb).data).is_null() {
                    free((*mb).data as *mut core::ffi::c_void);
                }
                free(mb as *mut core::ffi::c_void);
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn compute_hash(
            mb1: *mut MemoryBlock,
            mb2: *mut MemoryBlock,
        ) -> core::ffi::c_int {
            let mut hash: core::ffi::c_int = 0 as core::ffi::c_int;
            if (*mb1).data < (*mb2).data {
                hash += 100 as core::ffi::c_int;
            } else if (*mb1).data > (*mb2).data {
                hash += 200 as core::ffi::c_int;
            }
            if mb1 < mb2 {
                hash += 10 as core::ffi::c_int;
            } else if mb1 > mb2 {
                hash += 20 as core::ffi::c_int;
            }
            hash
        }
        #[no_mangle]
        pub unsafe extern "C" fn betagamma(
            param1: core::ffi::c_int,
            param2: core::ffi::c_int,
            param3: core::ffi::c_int,
            param4: core::ffi::c_int,
        ) -> core::ffi::c_int {
            let mut result: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut blocks: [DataBlock; 3] = [
                {
                    DataBlock {
                        id: 1 as core::ffi::c_int,
                        name: [
                            b'B' as i8,
                            b'l' as i8,
                            b'o' as i8,
                            b'c' as i8,
                            b'k' as i8,
                            b'_' as i8,
                            b'A' as i8,
                            b'l' as i8,
                            b'p' as i8,
                            b'h' as i8,
                            b'a' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                        ],
                        flags: 0o252 as uint8_t,
                    }
                },
                {
                    DataBlock {
                        id: 2 as core::ffi::c_int,
                        name: [
                            b'B' as i8,
                            b'l' as i8,
                            b'o' as i8,
                            b'c' as i8,
                            b'k' as i8,
                            b'_' as i8,
                            b'B' as i8,
                            b'e' as i8,
                            b't' as i8,
                            b'a' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                        ],
                        flags: 0o314 as uint8_t,
                    }
                },
                {
                    DataBlock {
                        id: 3 as core::ffi::c_int,
                        name: [
                            b'B' as i8,
                            b'l' as i8,
                            b'o' as i8,
                            b'c' as i8,
                            b'k' as i8,
                            b'_' as i8,
                            b'G' as i8,
                            b'a' as i8,
                            b'm' as i8,
                            b'm' as i8,
                            b'a' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                            b'\0' as i8,
                        ],
                        flags: 0o360 as uint8_t,
                    }
                },
            ];
            let num_blocks: core::ffi::c_int = ::core::mem::size_of::<[DataBlock; 3]>()
                .wrapping_div(::core::mem::size_of::<DataBlock>())
                as core::ffi::c_int;
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < num_blocks {
                let current: *mut DataBlock =
                    &mut *blocks.as_mut_ptr().offset(i as isize) as *mut DataBlock;
                let mut temp_name: [core::ffi::c_char; 32] = [0; 32];
                strcpy(temp_name.as_mut_ptr(), ((*current).name).as_ptr());
                let mut flag_contribution: core::ffi::c_int = 0 as core::ffi::c_int;
                if (*current).flags as core::ffi::c_int & 0o17 as core::ffi::c_int != 0 {
                    flag_contribution += param1;
                }
                if (*current).flags as core::ffi::c_int & 0o360 as core::ffi::c_int != 0 {
                    flag_contribution += param2;
                }
                if (*current).flags as core::ffi::c_int & 0o252 as core::ffi::c_int != 0 {
                    flag_contribution += param3;
                }
                if (*current).flags as core::ffi::c_int & 0o125 as core::ffi::c_int != 0 {
                    flag_contribution += param4;
                }
                result += flag_contribution * (*current).id;
                i += 1;
            }
            let block_size: size_t =
                (param1 % 10 as core::ffi::c_int + 5 as core::ffi::c_int) as size_t;
            let mem1: *mut MemoryBlock = allocate_block(block_size, param1);
            let mem2: *mut MemoryBlock = allocate_block(block_size, param2);
            if mem1.is_null() || mem2.is_null() {
                free_block(mem1);
                free_block(mem2);
                return -(1 as core::ffi::c_int);
            }
            let hash: core::ffi::c_int = compute_hash(mem1, mem2);
            result += hash;
            let mut sum1: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut sum2: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut i_0: size_t = 0 as size_t;
            while i_0 < (*mem1).size {
                sum1 += *((*mem1).data).add(i_0);
                i_0 = i_0.wrapping_add(1);
            }
            let mut i_1: size_t = 0 as size_t;
            while i_1 < (*mem2).size {
                sum2 += *((*mem2).data).add(i_1);
                i_1 = i_1.wrapping_add(1);
            }
            result += (sum1 - sum2) / 10 as core::ffi::c_int;
            let mut special: DataBlock = {
                DataBlock {
                    id: 99 as core::ffi::c_int,
                    name: [
                        b'S' as i8,
                        b'p' as i8,
                        b'e' as i8,
                        b'c' as i8,
                        b'i' as i8,
                        b'a' as i8,
                        b'l' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                        b'\0' as i8,
                    ],
                    flags: 0o377 as uint8_t,
                }
            };
            strcpy(
                (special.name).as_mut_ptr(),
                b"Modified\0" as *const u8 as *const core::ffi::c_char,
            );
            if (*mem1).data != (*mem2).data {
                result += special.id;
            }
            if (*mem1).data > NULL as *mut core::ffi::c_int
                && (*mem2).data > NULL as *mut core::ffi::c_int
            {
                result += special.flags as core::ffi::c_int;
            }
            free_block(mem1);
            free_block(mem2);
            result
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates("betagamma_lib", SOURCE, &["allocate_block#mb"], &[]);
}
