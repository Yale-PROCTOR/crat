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
    pub mod cJSON {
        extern "C" {
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
            fn strcpy(
                __dest: *mut core::ffi::c_char,
                __src: *const core::ffi::c_char,
            ) -> *mut core::ffi::c_char;
            fn strcmp(
                __s1: *const core::ffi::c_char,
                __s2: *const core::ffi::c_char,
            ) -> core::ffi::c_int;
            fn strncmp(
                __s1: *const core::ffi::c_char,
                __s2: *const core::ffi::c_char,
                __n: size_t,
            ) -> core::ffi::c_int;
            fn strlen(__s: *const core::ffi::c_char) -> size_t;
            fn sprintf(
                __s: *mut core::ffi::c_char,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn sscanf(
                __s: *const core::ffi::c_char,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn fabs(__x: core::ffi::c_double) -> core::ffi::c_double;
            fn strtod(
                __nptr: *const core::ffi::c_char,
                __endptr: *mut *mut core::ffi::c_char,
            ) -> core::ffi::c_double;
            fn malloc(__size: size_t) -> *mut core::ffi::c_void;
            fn realloc(__ptr: *mut core::ffi::c_void, __size: size_t) -> *mut core::ffi::c_void;
            fn free(__ptr: *mut core::ffi::c_void);
            fn tolower(__c: core::ffi::c_int) -> core::ffi::c_int;
            fn localeconv() -> *mut lconv;
        }
        pub type size_t = usize;
        #[repr(C)]
        pub struct lconv {
            pub decimal_point: *mut core::ffi::c_char,
            pub thousands_sep: *mut core::ffi::c_char,
            pub grouping: *mut core::ffi::c_char,
            pub int_curr_symbol: *mut core::ffi::c_char,
            pub currency_symbol: *mut core::ffi::c_char,
            pub mon_decimal_point: *mut core::ffi::c_char,
            pub mon_thousands_sep: *mut core::ffi::c_char,
            pub mon_grouping: *mut core::ffi::c_char,
            pub positive_sign: *mut core::ffi::c_char,
            pub negative_sign: *mut core::ffi::c_char,
            pub int_frac_digits: core::ffi::c_char,
            pub frac_digits: core::ffi::c_char,
            pub p_cs_precedes: core::ffi::c_char,
            pub p_sep_by_space: core::ffi::c_char,
            pub n_cs_precedes: core::ffi::c_char,
            pub n_sep_by_space: core::ffi::c_char,
            pub p_sign_posn: core::ffi::c_char,
            pub n_sign_posn: core::ffi::c_char,
            pub __int_p_cs_precedes: core::ffi::c_char,
            pub __int_p_sep_by_space: core::ffi::c_char,
            pub __int_n_cs_precedes: core::ffi::c_char,
            pub __int_n_sep_by_space: core::ffi::c_char,
            pub __int_p_sign_posn: core::ffi::c_char,
            pub __int_n_sign_posn: core::ffi::c_char,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for lconv {}
        #[automatically_derived]
        impl ::core::clone::Clone for lconv {
            #[inline]
            fn clone(&self) -> lconv {
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
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_char>;
                *self
            }
        }
        #[repr(C)]
        pub struct cJSON {
            pub next: *mut cJSON,
            pub prev: *mut cJSON,
            pub child: *mut cJSON,
            pub type_0: core::ffi::c_int,
            pub valuestring: *mut core::ffi::c_char,
            pub valueint: core::ffi::c_int,
            pub valuedouble: core::ffi::c_double,
            pub string: *mut core::ffi::c_char,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for cJSON {}
        #[automatically_derived]
        impl ::core::clone::Clone for cJSON {
            #[inline]
            fn clone(&self) -> cJSON {
                let _: ::core::clone::AssertParamIsClone<*mut cJSON>;
                let _: ::core::clone::AssertParamIsClone<*mut cJSON>;
                let _: ::core::clone::AssertParamIsClone<*mut cJSON>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_double>;
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_char>;
                *self
            }
        }
        #[repr(C)]
        pub struct cJSON_Hooks {
            pub malloc_fn: Option<unsafe extern "C" fn(size_t) -> *mut core::ffi::c_void>,
            pub free_fn: Option<unsafe extern "C" fn(*mut core::ffi::c_void) -> ()>,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for cJSON_Hooks {}
        #[automatically_derived]
        impl ::core::clone::Clone for cJSON_Hooks {
            #[inline]
            fn clone(&self) -> cJSON_Hooks {
                let _: ::core::clone::AssertParamIsClone<
                    Option<unsafe extern "C" fn(size_t) -> *mut core::ffi::c_void>,
                >;
                let _: ::core::clone::AssertParamIsClone<
                    Option<unsafe extern "C" fn(*mut core::ffi::c_void) -> ()>,
                >;
                *self
            }
        }
        pub type cJSON_bool = core::ffi::c_int;
        #[repr(C)]
        pub struct internal_hooks {
            pub allocate: Option<unsafe extern "C" fn(size_t) -> *mut core::ffi::c_void>,
            pub deallocate: Option<unsafe extern "C" fn(*mut core::ffi::c_void) -> ()>,
            pub reallocate: Option<
                unsafe extern "C" fn(*mut core::ffi::c_void, size_t) -> *mut core::ffi::c_void,
            >,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for internal_hooks {}
        #[automatically_derived]
        impl ::core::clone::Clone for internal_hooks {
            #[inline]
            fn clone(&self) -> internal_hooks {
                let _: ::core::clone::AssertParamIsClone<
                    Option<unsafe extern "C" fn(size_t) -> *mut core::ffi::c_void>,
                >;
                let _: ::core::clone::AssertParamIsClone<
                    Option<unsafe extern "C" fn(*mut core::ffi::c_void) -> ()>,
                >;
                let _: ::core::clone::AssertParamIsClone<
                    Option<
                        unsafe extern "C" fn(
                            *mut core::ffi::c_void,
                            size_t,
                        ) -> *mut core::ffi::c_void,
                    >,
                >;
                *self
            }
        }
        #[repr(C)]
        pub struct error {
            pub json: *const core::ffi::c_uchar,
            pub position: size_t,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for error {}
        #[automatically_derived]
        impl ::core::clone::Clone for error {
            #[inline]
            fn clone(&self) -> error {
                let _: ::core::clone::AssertParamIsClone<*const core::ffi::c_uchar>;
                let _: ::core::clone::AssertParamIsClone<size_t>;
                *self
            }
        }
        #[repr(C)]
        pub struct parse_buffer {
            pub content: *const core::ffi::c_uchar,
            pub length: size_t,
            pub offset: size_t,
            pub depth: size_t,
            pub hooks: internal_hooks,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for parse_buffer {}
        #[automatically_derived]
        impl ::core::clone::Clone for parse_buffer {
            #[inline]
            fn clone(&self) -> parse_buffer {
                let _: ::core::clone::AssertParamIsClone<*const core::ffi::c_uchar>;
                let _: ::core::clone::AssertParamIsClone<size_t>;
                let _: ::core::clone::AssertParamIsClone<internal_hooks>;
                *self
            }
        }
        #[repr(C)]
        pub struct printbuffer {
            pub buffer: *mut core::ffi::c_uchar,
            pub length: size_t,
            pub offset: size_t,
            pub depth: size_t,
            pub noalloc: cJSON_bool,
            pub format: cJSON_bool,
            pub hooks: internal_hooks,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for printbuffer {}
        #[automatically_derived]
        impl ::core::clone::Clone for printbuffer {
            #[inline]
            fn clone(&self) -> printbuffer {
                let _: ::core::clone::AssertParamIsClone<*mut core::ffi::c_uchar>;
                let _: ::core::clone::AssertParamIsClone<size_t>;
                let _: ::core::clone::AssertParamIsClone<cJSON_bool>;
                let _: ::core::clone::AssertParamIsClone<internal_hooks>;
                *self
            }
        }
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const __INT_MAX__: core::ffi::c_int = 2147483647 as core::ffi::c_int;
        pub const CJSON_VERSION_MAJOR: core::ffi::c_int = 1 as core::ffi::c_int;
        pub const CJSON_VERSION_MINOR: core::ffi::c_int = 7 as core::ffi::c_int;
        pub const CJSON_VERSION_PATCH: core::ffi::c_int = 19 as core::ffi::c_int;
        pub const cJSON_Invalid: core::ffi::c_int = 0 as core::ffi::c_int;
        pub const cJSON_False: core::ffi::c_int = (1 as core::ffi::c_int) << 0 as core::ffi::c_int;
        pub const cJSON_True: core::ffi::c_int = (1 as core::ffi::c_int) << 1 as core::ffi::c_int;
        pub const cJSON_NULL: core::ffi::c_int = (1 as core::ffi::c_int) << 2 as core::ffi::c_int;
        pub const cJSON_Number: core::ffi::c_int = (1 as core::ffi::c_int) << 3 as core::ffi::c_int;
        pub const cJSON_String: core::ffi::c_int = (1 as core::ffi::c_int) << 4 as core::ffi::c_int;
        pub const cJSON_Array: core::ffi::c_int = (1 as core::ffi::c_int) << 5 as core::ffi::c_int;
        pub const cJSON_Object: core::ffi::c_int = (1 as core::ffi::c_int) << 6 as core::ffi::c_int;
        pub const cJSON_Raw: core::ffi::c_int = 128;
        pub const cJSON_IsReference: core::ffi::c_int = 256 as core::ffi::c_int;
        pub const cJSON_StringIsConst: core::ffi::c_int = 512 as core::ffi::c_int;
        pub const CJSON_NESTING_LIMIT: core::ffi::c_int = 1000 as core::ffi::c_int;
        pub const CJSON_CIRCULAR_LIMIT: core::ffi::c_int = 10000 as core::ffi::c_int;
        pub const true_0: cJSON_bool = 1 as core::ffi::c_int;
        pub const false_0: cJSON_bool = 0 as core::ffi::c_int;
        static mut global_error: error = {
            error {
                json: 0 as *const core::ffi::c_uchar,
                position: 0 as size_t,
            }
        };
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_GetErrorPtr() -> *const core::ffi::c_char {
            (global_error.json).add(global_error.position) as *const core::ffi::c_char
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_GetStringValue(
            item: *const cJSON,
        ) -> *mut core::ffi::c_char {
            if cJSON_IsString(item) == 0 {
                return std::ptr::null_mut::<core::ffi::c_char>();
            }
            (*item).valuestring
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_GetNumberValue(item: *const cJSON) -> core::ffi::c_double {
            if cJSON_IsNumber(item) == 0 {
                return 0.0f64 / 0.0f64;
            }
            (*item).valuedouble
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_Version() -> *const core::ffi::c_char {
            static mut version: [core::ffi::c_char; 15] = [0; 15];
            sprintf(
                version.as_mut_ptr(),
                b"%i.%i.%i\0" as *const u8 as *const core::ffi::c_char,
                CJSON_VERSION_MAJOR,
                CJSON_VERSION_MINOR,
                CJSON_VERSION_PATCH,
            );
            version.as_ptr()
        }
        unsafe extern "C" fn case_insensitive_strcmp(
            mut string1: *const core::ffi::c_uchar,
            mut string2: *const core::ffi::c_uchar,
        ) -> core::ffi::c_int {
            if string1.is_null() || string2.is_null() {
                return 1 as core::ffi::c_int;
            }
            if string1 == string2 {
                return 0 as core::ffi::c_int;
            }
            while tolower(*string1 as core::ffi::c_int) == tolower(*string2 as core::ffi::c_int) {
                if *string1 as core::ffi::c_int == '\0' as i32 {
                    return 0 as core::ffi::c_int;
                }
                string1 = string1.offset(1);
                string2 = string2.offset(1);
            }
            tolower(*string1 as core::ffi::c_int) - tolower(*string2 as core::ffi::c_int)
        }
        static mut global_hooks: internal_hooks = unsafe {
            {
                internal_hooks {
                    allocate: Some(
                        malloc as unsafe extern "C" fn(size_t) -> *mut core::ffi::c_void,
                    ),
                    deallocate: Some(free as unsafe extern "C" fn(*mut core::ffi::c_void) -> ()),
                    reallocate: Some(
                        realloc
                            as unsafe extern "C" fn(
                                *mut core::ffi::c_void,
                                size_t,
                            )
                                -> *mut core::ffi::c_void,
                    ),
                }
            }
        };
        unsafe extern "C" fn cJSON_strdup(
            string: *const core::ffi::c_uchar,
            hooks: *const internal_hooks,
        ) -> *mut core::ffi::c_uchar {
            let mut length: size_t = 0 as size_t;
            let mut copy: *mut core::ffi::c_uchar = std::ptr::null_mut::<core::ffi::c_uchar>();
            if string.is_null() {
                return std::ptr::null_mut::<core::ffi::c_uchar>();
            }
            length = (strlen(string as *const core::ffi::c_char))
                .wrapping_add(::core::mem::size_of::<[core::ffi::c_char; 1]>() as size_t);
            copy = ((*hooks).allocate).expect("non-null function pointer")(length)
                as *mut core::ffi::c_uchar;
            if copy.is_null() {
                return std::ptr::null_mut::<core::ffi::c_uchar>();
            }
            memcpy(
                copy as *mut core::ffi::c_void,
                string as *const core::ffi::c_void,
                length,
            );
            copy
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_InitHooks(hooks: *mut cJSON_Hooks) {
            if hooks.is_null() {
                global_hooks.allocate =
                    Some(malloc as unsafe extern "C" fn(size_t) -> *mut core::ffi::c_void)
                        as Option<unsafe extern "C" fn(size_t) -> *mut core::ffi::c_void>;
                global_hooks.deallocate =
                    Some(free as unsafe extern "C" fn(*mut core::ffi::c_void) -> ())
                        as Option<unsafe extern "C" fn(*mut core::ffi::c_void) -> ()>;
                global_hooks.reallocate = Some(
                    realloc
                        as unsafe extern "C" fn(
                            *mut core::ffi::c_void,
                            size_t,
                        ) -> *mut core::ffi::c_void,
                )
                    as Option<
                        unsafe extern "C" fn(
                            *mut core::ffi::c_void,
                            size_t,
                        ) -> *mut core::ffi::c_void,
                    >;
                return;
            }
            global_hooks.allocate =
                Some(malloc as unsafe extern "C" fn(size_t) -> *mut core::ffi::c_void)
                    as Option<unsafe extern "C" fn(size_t) -> *mut core::ffi::c_void>;
            if ((*hooks).malloc_fn).is_some() {
                global_hooks.allocate = (*hooks).malloc_fn;
            }
            global_hooks.deallocate =
                Some(free as unsafe extern "C" fn(*mut core::ffi::c_void) -> ())
                    as Option<unsafe extern "C" fn(*mut core::ffi::c_void) -> ()>;
            if ((*hooks).free_fn).is_some() {
                global_hooks.deallocate = (*hooks).free_fn;
            }
            global_hooks.reallocate = None;
            if global_hooks.allocate
                == Some(malloc as unsafe extern "C" fn(size_t) -> *mut core::ffi::c_void)
                && global_hooks.deallocate
                    == Some(free as unsafe extern "C" fn(*mut core::ffi::c_void) -> ())
            {
                global_hooks.reallocate = Some(
                    realloc
                        as unsafe extern "C" fn(
                            *mut core::ffi::c_void,
                            size_t,
                        ) -> *mut core::ffi::c_void,
                )
                    as Option<
                        unsafe extern "C" fn(
                            *mut core::ffi::c_void,
                            size_t,
                        ) -> *mut core::ffi::c_void,
                    >;
            }
        }
        unsafe extern "C" fn cJSON_New_Item(hooks: *const internal_hooks) -> *mut cJSON {
            let node: *mut cJSON = ((*hooks).allocate).expect("non-null function pointer")(
                ::core::mem::size_of::<cJSON>() as size_t,
            ) as *mut cJSON;
            if !node.is_null() {
                memset(
                    node as *mut core::ffi::c_void,
                    '\0' as i32,
                    ::core::mem::size_of::<cJSON>() as size_t,
                );
            }
            node
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_Delete(mut item: *mut cJSON) {
            let mut next: *mut cJSON = std::ptr::null_mut::<cJSON>();
            while !item.is_null() {
                next = (*item).next as *mut cJSON;
                if (*item).type_0 & cJSON_IsReference == 0 && !((*item).child).is_null() {
                    cJSON_Delete((*item).child as *mut cJSON);
                }
                if (*item).type_0 & cJSON_IsReference == 0 && !((*item).valuestring).is_null() {
                    (global_hooks.deallocate).expect("non-null function pointer")(
                        (*item).valuestring as *mut core::ffi::c_void,
                    );
                    (*item).valuestring = std::ptr::null_mut::<core::ffi::c_char>();
                }
                if (*item).type_0 & cJSON_StringIsConst == 0 && !((*item).string).is_null() {
                    (global_hooks.deallocate).expect("non-null function pointer")(
                        (*item).string as *mut core::ffi::c_void,
                    );
                    (*item).string = std::ptr::null_mut::<core::ffi::c_char>();
                }
                (global_hooks.deallocate).expect("non-null function pointer")(
                    item as *mut core::ffi::c_void,
                );
                item = next;
            }
        }
        unsafe extern "C" fn get_decimal_point() -> core::ffi::c_uchar {
            let lconv: *mut lconv = localeconv();
            *((*lconv).decimal_point).offset(0 as core::ffi::c_int as isize) as core::ffi::c_uchar
        }
        unsafe extern "C" fn parse_number(
            item: *mut cJSON,
            input_buffer: *mut parse_buffer,
        ) -> cJSON_bool {
            let mut number: core::ffi::c_double = 0 as core::ffi::c_int as core::ffi::c_double;
            let mut after_end: *mut core::ffi::c_uchar = std::ptr::null_mut::<core::ffi::c_uchar>();
            let mut number_c_string: *mut core::ffi::c_uchar =
                std::ptr::null_mut::<core::ffi::c_uchar>();
            let decimal_point: core::ffi::c_uchar = get_decimal_point();
            let mut i: size_t = 0 as size_t;
            let mut number_string_length: size_t = 0 as size_t;
            let mut has_decimal_point: cJSON_bool = false_0;
            if input_buffer.is_null() || ((*input_buffer).content).is_null() {
                return false_0;
            }
            i = 0 as size_t;
            while !input_buffer.is_null()
                && ((*input_buffer).offset).wrapping_add(i) < (*input_buffer).length
            {
                match *((*input_buffer).content).add((*input_buffer).offset).add(i)
                    as core::ffi::c_int
                {
                    48 | 49 | 50 | 51 | 52 | 53 | 54 | 55 | 56 | 57 | 43 | 45 | 101 | 69 => {
                        number_string_length = number_string_length.wrapping_add(1);
                    }
                    46 => {
                        number_string_length = number_string_length.wrapping_add(1);
                        has_decimal_point = true_0;
                    }
                    _ => {
                        break;
                    }
                }
                i = i.wrapping_add(1);
            }
            number_c_string = ((*input_buffer).hooks.allocate).expect("non-null function pointer")(
                number_string_length.wrapping_add(1 as size_t),
            ) as *mut core::ffi::c_uchar;
            if number_c_string.is_null() {
                return false_0;
            }
            memcpy(
                number_c_string as *mut core::ffi::c_void,
                ((*input_buffer).content).add((*input_buffer).offset) as *const core::ffi::c_void,
                number_string_length,
            );
            *number_c_string.add(number_string_length) = '\0' as i32 as core::ffi::c_uchar;
            if has_decimal_point != 0 {
                i = 0 as size_t;
                while i < number_string_length {
                    if *number_c_string.add(i) as core::ffi::c_int == '.' as i32 {
                        *number_c_string.add(i) = decimal_point;
                    }
                    i = i.wrapping_add(1);
                }
            }
            number = strtod(
                number_c_string as *const core::ffi::c_char,
                &mut after_end as *mut *mut core::ffi::c_uchar as *mut *mut core::ffi::c_char,
            );
            if number_c_string == after_end {
                ((*input_buffer).hooks.deallocate).expect("non-null function pointer")(
                    number_c_string as *mut core::ffi::c_void,
                );
                return false_0;
            }
            (*item).valuedouble = number;
            if number >= INT_MAX as core::ffi::c_double {
                (*item).valueint = INT_MAX;
            } else if number <= INT_MIN as core::ffi::c_double {
                (*item).valueint = INT_MIN;
            } else {
                (*item).valueint = number as core::ffi::c_int;
            }
            (*item).type_0 = cJSON_Number;
            (*input_buffer).offset =
                ((*input_buffer).offset as core::ffi::c_ulong)
                    .wrapping_add(after_end.offset_from(number_c_string) as core::ffi::c_long
                        as size_t as core::ffi::c_ulong) as size_t as size_t;
            ((*input_buffer).hooks.deallocate).expect("non-null function pointer")(
                number_c_string as *mut core::ffi::c_void,
            );
            true_0
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_SetNumberHelper(
            object: *mut cJSON,
            number: core::ffi::c_double,
        ) -> core::ffi::c_double {
            if number >= INT_MAX as core::ffi::c_double {
                (*object).valueint = INT_MAX;
            } else if number <= INT_MIN as core::ffi::c_double {
                (*object).valueint = INT_MIN;
            } else {
                (*object).valueint = number as core::ffi::c_int;
            }
            (*object).valuedouble = number;
            (*object).valuedouble
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_SetValuestring(
            object: *mut cJSON,
            valuestring: *const core::ffi::c_char,
        ) -> *mut core::ffi::c_char {
            let mut copy: *mut core::ffi::c_char = std::ptr::null_mut::<core::ffi::c_char>();
            let mut v1_len: size_t = 0;
            let mut v2_len: size_t = 0;
            if object.is_null()
                || (*object).type_0 & cJSON_String == 0
                || (*object).type_0 & cJSON_IsReference != 0
            {
                return std::ptr::null_mut::<core::ffi::c_char>();
            }
            if ((*object).valuestring).is_null() || valuestring.is_null() {
                return std::ptr::null_mut::<core::ffi::c_char>();
            }
            v1_len = strlen(valuestring);
            v2_len = strlen((*object).valuestring);
            if v1_len <= v2_len {
                if !(valuestring.add(v1_len) < (*object).valuestring as *const core::ffi::c_char
                    || ((*object).valuestring).add(v2_len) < valuestring as *mut core::ffi::c_char)
                {
                    return std::ptr::null_mut::<core::ffi::c_char>();
                }
                strcpy((*object).valuestring, valuestring);
                return (*object).valuestring;
            }
            copy = cJSON_strdup(valuestring as *const core::ffi::c_uchar, &mut global_hooks)
                as *mut core::ffi::c_char;
            if copy.is_null() {
                return std::ptr::null_mut::<core::ffi::c_char>();
            }
            if !((*object).valuestring).is_null() {
                cJSON_free((*object).valuestring as *mut core::ffi::c_void);
            }
            (*object).valuestring = copy;
            copy
        }
        unsafe extern "C" fn ensure(
            p: *mut printbuffer,
            mut needed: size_t,
        ) -> *mut core::ffi::c_uchar {
            let mut newbuffer: *mut core::ffi::c_uchar = std::ptr::null_mut::<core::ffi::c_uchar>();
            let mut newsize: size_t = 0 as size_t;
            if p.is_null() || ((*p).buffer).is_null() {
                return std::ptr::null_mut::<core::ffi::c_uchar>();
            }
            if (*p).length > 0 as size_t && (*p).offset >= (*p).length {
                return std::ptr::null_mut::<core::ffi::c_uchar>();
            }
            if needed > INT_MAX as size_t {
                return std::ptr::null_mut::<core::ffi::c_uchar>();
            }
            needed = (needed as core::ffi::c_ulong)
                .wrapping_add(((*p).offset).wrapping_add(1 as size_t) as core::ffi::c_ulong)
                as size_t as size_t;
            if needed <= (*p).length {
                return ((*p).buffer).add((*p).offset);
            }
            if (*p).noalloc != 0 {
                return std::ptr::null_mut::<core::ffi::c_uchar>();
            }
            if needed > (INT_MAX / 2 as core::ffi::c_int) as size_t {
                if needed <= INT_MAX as size_t {
                    newsize = INT_MAX as size_t;
                } else {
                    return std::ptr::null_mut::<core::ffi::c_uchar>();
                }
            } else {
                newsize = needed.wrapping_mul(2 as size_t);
            }
            if ((*p).hooks.reallocate).is_some() {
                newbuffer = ((*p).hooks.reallocate).expect("non-null function pointer")(
                    (*p).buffer as *mut core::ffi::c_void,
                    newsize,
                ) as *mut core::ffi::c_uchar;
                if newbuffer.is_null() {
                    ((*p).hooks.deallocate).expect("non-null function pointer")(
                        (*p).buffer as *mut core::ffi::c_void,
                    );
                    (*p).length = 0 as size_t;
                    (*p).buffer = std::ptr::null_mut::<core::ffi::c_uchar>();
                    return std::ptr::null_mut::<core::ffi::c_uchar>();
                }
            } else {
                newbuffer = ((*p).hooks.allocate).expect("non-null function pointer")(newsize)
                    as *mut core::ffi::c_uchar;
                if newbuffer.is_null() {
                    ((*p).hooks.deallocate).expect("non-null function pointer")(
                        (*p).buffer as *mut core::ffi::c_void,
                    );
                    (*p).length = 0 as size_t;
                    (*p).buffer = std::ptr::null_mut::<core::ffi::c_uchar>();
                    return std::ptr::null_mut::<core::ffi::c_uchar>();
                }
                memcpy(
                    newbuffer as *mut core::ffi::c_void,
                    (*p).buffer as *const core::ffi::c_void,
                    ((*p).offset).wrapping_add(1 as size_t),
                );
                ((*p).hooks.deallocate).expect("non-null function pointer")(
                    (*p).buffer as *mut core::ffi::c_void,
                );
            }
            (*p).length = newsize;
            (*p).buffer = newbuffer;
            newbuffer.add((*p).offset)
        }
        unsafe extern "C" fn update_offset(buffer: *mut printbuffer) {
            let mut buffer_pointer: *const core::ffi::c_uchar =
                std::ptr::null::<core::ffi::c_uchar>();
            if buffer.is_null() || ((*buffer).buffer).is_null() {
                return;
            }
            buffer_pointer = ((*buffer).buffer).add((*buffer).offset);
            (*buffer).offset = ((*buffer).offset as core::ffi::c_ulong)
                .wrapping_add(
                    strlen(buffer_pointer as *const core::ffi::c_char) as core::ffi::c_ulong
                ) as size_t as size_t;
        }
        unsafe extern "C" fn compare_double(
            a: core::ffi::c_double,
            b: core::ffi::c_double,
        ) -> cJSON_bool {
            let maxVal: core::ffi::c_double = if fabs(a) > fabs(b) { fabs(a) } else { fabs(b) };
            (fabs(a - b) <= maxVal * DBL_EPSILON) as core::ffi::c_int
        }
        unsafe extern "C" fn print_number(
            item: *const cJSON,
            output_buffer: *mut printbuffer,
        ) -> cJSON_bool {
            let mut output_pointer: *mut core::ffi::c_uchar =
                std::ptr::null_mut::<core::ffi::c_uchar>();
            let d: core::ffi::c_double = (*item).valuedouble;
            let mut length: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut i: size_t = 0 as size_t;
            let mut number_buffer: [core::ffi::c_uchar; 26] = [
                0 as core::ffi::c_int as core::ffi::c_uchar,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
                0,
            ];
            let decimal_point: core::ffi::c_uchar = get_decimal_point();
            let mut test: core::ffi::c_double = 0.0f64;
            if output_buffer.is_null() {
                return false_0;
            }
            if d != d || d - d != d - d && !(d != d) {
                length = sprintf(
                    number_buffer.as_mut_ptr() as *mut core::ffi::c_char,
                    b"null\0" as *const u8 as *const core::ffi::c_char,
                );
            } else if d == (*item).valueint as core::ffi::c_double {
                length = sprintf(
                    number_buffer.as_mut_ptr() as *mut core::ffi::c_char,
                    b"%d\0" as *const u8 as *const core::ffi::c_char,
                    (*item).valueint,
                );
            } else {
                length = sprintf(
                    number_buffer.as_mut_ptr() as *mut core::ffi::c_char,
                    b"%1.15g\0" as *const u8 as *const core::ffi::c_char,
                    d,
                );
                if sscanf(
                    number_buffer.as_mut_ptr() as *mut core::ffi::c_char,
                    b"%lg\0" as *const u8 as *const core::ffi::c_char,
                    &mut test as *mut core::ffi::c_double,
                ) != 1 as core::ffi::c_int
                    || compare_double(test, d) == 0
                {
                    length = sprintf(
                        number_buffer.as_mut_ptr() as *mut core::ffi::c_char,
                        b"%1.17g\0" as *const u8 as *const core::ffi::c_char,
                        d,
                    );
                }
            }
            if length < 0 as core::ffi::c_int
                || length
                    > ::core::mem::size_of::<[core::ffi::c_uchar; 26]>().wrapping_sub(1_usize)
                        as core::ffi::c_int
            {
                return false_0;
            }
            output_pointer = ensure(
                output_buffer,
                (length as size_t)
                    .wrapping_add(::core::mem::size_of::<[core::ffi::c_char; 1]>() as size_t),
            );
            if output_pointer.is_null() {
                return false_0;
            }
            i = 0 as size_t;
            while i < length as size_t {
                if number_buffer[i as usize] as core::ffi::c_int
                    == decimal_point as core::ffi::c_int
                {
                    *output_pointer.add(i) = '.' as i32 as core::ffi::c_uchar;
                } else {
                    *output_pointer.add(i) = number_buffer[i as usize];
                }
                i = i.wrapping_add(1);
            }
            *output_pointer.add(i) = '\0' as i32 as core::ffi::c_uchar;
            (*output_buffer).offset = ((*output_buffer).offset as core::ffi::c_ulong)
                .wrapping_add(length as size_t as core::ffi::c_ulong)
                as size_t as size_t;
            true_0
        }
        unsafe extern "C" fn parse_hex4(input: *const core::ffi::c_uchar) -> core::ffi::c_uint {
            let mut h: core::ffi::c_uint = 0 as core::ffi::c_uint;
            let mut i: size_t = 0 as size_t;
            i = 0 as size_t;
            while i < 4 as size_t {
                if *input.add(i) as core::ffi::c_int >= '0' as i32
                    && *input.add(i) as core::ffi::c_int <= '9' as i32
                {
                    h = h.wrapping_add(
                        (*input.add(i) as core::ffi::c_uint)
                            .wrapping_sub('0' as i32 as core::ffi::c_uint),
                    );
                } else if *input.add(i) as core::ffi::c_int >= 'A' as i32
                    && *input.add(i) as core::ffi::c_int <= 'F' as i32
                {
                    h = h.wrapping_add(
                        (10 as core::ffi::c_int as core::ffi::c_uint)
                            .wrapping_add(*input.add(i) as core::ffi::c_uint)
                            .wrapping_sub('A' as i32 as core::ffi::c_uint),
                    );
                } else if *input.add(i) as core::ffi::c_int >= 'a' as i32
                    && *input.add(i) as core::ffi::c_int <= 'f' as i32
                {
                    h = h.wrapping_add(
                        (10 as core::ffi::c_int as core::ffi::c_uint)
                            .wrapping_add(*input.add(i) as core::ffi::c_uint)
                            .wrapping_sub('a' as i32 as core::ffi::c_uint),
                    );
                } else {
                    return 0 as core::ffi::c_uint;
                }
                if i < 3 as size_t {
                    h <<= 4 as core::ffi::c_int;
                }
                i = i.wrapping_add(1);
            }
            h
        }
        unsafe extern "C" fn utf16_literal_to_utf8(
            input_pointer: *const core::ffi::c_uchar,
            input_end: *const core::ffi::c_uchar,
            output_pointer: *mut *mut core::ffi::c_uchar,
        ) -> core::ffi::c_uchar {
            let mut current_block: u64;
            let mut codepoint: core::ffi::c_ulong = 0 as core::ffi::c_ulong;
            let mut first_code: core::ffi::c_uint = 0 as core::ffi::c_uint;
            let mut utf8_length: core::ffi::c_uchar = 0 as core::ffi::c_uchar;
            let mut utf8_position: core::ffi::c_uchar = 0 as core::ffi::c_uchar;
            let mut sequence_length: core::ffi::c_uchar = 0 as core::ffi::c_uchar;
            let mut first_byte_mark: core::ffi::c_uchar = 0 as core::ffi::c_uchar;
            if (input_end.offset_from(input_pointer) as core::ffi::c_long) >= 6 as core::ffi::c_long
            {
                first_code = parse_hex4(input_pointer.offset(2 as core::ffi::c_int as isize));
                if !(first_code >= 0xdc00 as core::ffi::c_uint
                    && first_code <= 0xdfff as core::ffi::c_uint)
                {
                    if first_code >= 0xd800 as core::ffi::c_uint
                        && first_code <= 0xdbff as core::ffi::c_uint
                    {
                        let second_sequence: *const core::ffi::c_uchar =
                            input_pointer.offset(6 as core::ffi::c_int as isize);
                        let mut second_code: core::ffi::c_uint = 0 as core::ffi::c_uint;
                        sequence_length = 12 as core::ffi::c_uchar;
                        if (input_end.offset_from(second_sequence) as core::ffi::c_long)
                            < 6 as core::ffi::c_long
                        {
                            current_block = 2375782389372945117;
                        } else if *second_sequence.offset(0 as core::ffi::c_int as isize)
                            as core::ffi::c_int
                            != '\\' as i32
                            || *second_sequence.offset(1 as core::ffi::c_int as isize)
                                as core::ffi::c_int
                                != 'u' as i32
                        {
                            current_block = 2375782389372945117;
                        } else {
                            second_code =
                                parse_hex4(second_sequence.offset(2 as core::ffi::c_int as isize));
                            if second_code < 0xdc00 as core::ffi::c_uint
                                || second_code > 0xdfff as core::ffi::c_uint
                            {
                                current_block = 2375782389372945117;
                            } else {
                                codepoint = (0x10000 as core::ffi::c_uint).wrapping_add(
                                    (first_code & 0x3ff as core::ffi::c_uint)
                                        << 10 as core::ffi::c_int
                                        | second_code & 0x3ff as core::ffi::c_uint,
                                ) as core::ffi::c_ulong;
                                current_block = 12039483399334584727;
                            }
                        }
                    } else {
                        sequence_length = 6 as core::ffi::c_uchar;
                        codepoint = first_code as core::ffi::c_ulong;
                        current_block = 12039483399334584727;
                    }
                    match current_block {
                        2375782389372945117 => {}
                        _ => {
                            if codepoint < 0x80 as core::ffi::c_ulong {
                                utf8_length = 1 as core::ffi::c_uchar;
                                current_block = 3437258052017859086;
                            } else if codepoint < 0x800 as core::ffi::c_ulong {
                                utf8_length = 2 as core::ffi::c_uchar;
                                first_byte_mark = 0xc0 as core::ffi::c_uchar;
                                current_block = 3437258052017859086;
                            } else if codepoint < 0x10000 as core::ffi::c_ulong {
                                utf8_length = 3 as core::ffi::c_uchar;
                                first_byte_mark = 0xe0 as core::ffi::c_uchar;
                                current_block = 3437258052017859086;
                            } else if codepoint <= 0x10ffff as core::ffi::c_ulong {
                                utf8_length = 4 as core::ffi::c_uchar;
                                first_byte_mark = 0xf0 as core::ffi::c_uchar;
                                current_block = 3437258052017859086;
                            } else {
                                current_block = 2375782389372945117;
                            }
                            match current_block {
                                2375782389372945117 => {}
                                _ => {
                                    utf8_position = (utf8_length as core::ffi::c_int
                                        - 1 as core::ffi::c_int)
                                        as core::ffi::c_uchar;
                                    while utf8_position as core::ffi::c_int > 0 as core::ffi::c_int
                                    {
                                        *(*output_pointer).offset(utf8_position as isize) =
                                            ((codepoint | 0x80 as core::ffi::c_ulong)
                                                & 0xbf as core::ffi::c_ulong)
                                                as core::ffi::c_uchar;
                                        codepoint >>= 6 as core::ffi::c_int;
                                        utf8_position = utf8_position.wrapping_sub(1);
                                    }
                                    if utf8_length as core::ffi::c_int > 1 as core::ffi::c_int {
                                        *(*output_pointer).offset(0 as core::ffi::c_int as isize) =
                                            ((codepoint | first_byte_mark as core::ffi::c_ulong)
                                                & 0xff as core::ffi::c_ulong)
                                                as core::ffi::c_uchar;
                                    } else {
                                        *(*output_pointer).offset(0 as core::ffi::c_int as isize) =
                                            (codepoint & 0x7f as core::ffi::c_ulong)
                                                as core::ffi::c_uchar;
                                    }
                                    *output_pointer = (*output_pointer)
                                        .offset(utf8_length as core::ffi::c_int as isize);
                                    return sequence_length;
                                }
                            }
                        }
                    }
                }
            }
            0 as core::ffi::c_uchar
        }
        unsafe extern "C" fn parse_string(
            item: *mut cJSON,
            input_buffer: *mut parse_buffer,
        ) -> cJSON_bool {
            let mut current_block: u64;
            let mut input_pointer: *const core::ffi::c_uchar = ((*input_buffer).content)
                .add((*input_buffer).offset)
                .offset(1 as core::ffi::c_int as isize);
            let mut input_end: *const core::ffi::c_uchar = ((*input_buffer).content)
                .add((*input_buffer).offset)
                .offset(1 as core::ffi::c_int as isize);
            let mut output_pointer: *mut core::ffi::c_uchar =
                std::ptr::null_mut::<core::ffi::c_uchar>();
            let mut output: *mut core::ffi::c_uchar = std::ptr::null_mut::<core::ffi::c_uchar>();
            if *((*input_buffer).content)
                .add((*input_buffer).offset)
                .offset(0 as core::ffi::c_int as isize) as core::ffi::c_int
                == '"' as i32
            {
                let mut allocation_length: size_t = 0 as size_t;
                let mut skipped_bytes: size_t = 0 as size_t;
                loop {
                    if !((input_end.offset_from((*input_buffer).content) as core::ffi::c_long
                        as size_t)
                        < (*input_buffer).length
                        && *input_end as core::ffi::c_int != '"' as i32)
                    {
                        current_block = 11812396948646013369;
                        break;
                    }
                    if *input_end.offset(0 as core::ffi::c_int as isize) as core::ffi::c_int
                        == '\\' as i32
                    {
                        if input_end
                            .offset(1 as core::ffi::c_int as isize)
                            .offset_from((*input_buffer).content)
                            as core::ffi::c_long as size_t
                            >= (*input_buffer).length
                        {
                            current_block = 10063478961057336850;
                            break;
                        }
                        skipped_bytes = skipped_bytes.wrapping_add(1);
                        input_end = input_end.offset(1);
                    }
                    input_end = input_end.offset(1);
                }
                match current_block {
                    10063478961057336850 => {}
                    _ => {
                        if !(input_end.offset_from((*input_buffer).content) as core::ffi::c_long
                            as size_t
                            >= (*input_buffer).length
                            || *input_end as core::ffi::c_int != '"' as i32)
                        {
                            allocation_length = (input_end
                                .offset_from(((*input_buffer).content).add((*input_buffer).offset))
                                as core::ffi::c_long
                                as size_t)
                                .wrapping_sub(skipped_bytes);
                            output = ((*input_buffer).hooks.allocate)
                                .expect("non-null function pointer")(
                                allocation_length
                                    .wrapping_add(
                                        ::core::mem::size_of::<[core::ffi::c_char; 1]>() as size_t
                                    ),
                            ) as *mut core::ffi::c_uchar;
                            if !output.is_null() {
                                output_pointer = output;
                                loop {
                                    if input_pointer >= input_end {
                                        current_block = 7828949454673616476;
                                        break;
                                    }
                                    if *input_pointer as core::ffi::c_int != '\\' as i32 {
                                        let fresh0 = *input_pointer;
                                        input_pointer = input_pointer.offset(1);
                                        *output_pointer = fresh0;
                                        let fresh1 = *output_pointer;
                                        output_pointer = output_pointer.offset(1);
                                    } else {
                                        let mut sequence_length: core::ffi::c_uchar =
                                            2 as core::ffi::c_uchar;
                                        if (input_end.offset_from(input_pointer)
                                            as core::ffi::c_long)
                                            < 1 as core::ffi::c_long
                                        {
                                            current_block = 10063478961057336850;
                                            break;
                                        }
                                        match *input_pointer.offset(1 as core::ffi::c_int as isize)
                                            as core::ffi::c_int
                                        {
                                            98 => {
                                                *output_pointer =
                                                    '\u{8}' as i32 as core::ffi::c_uchar;
                                                let fresh2 = *output_pointer;
                                                output_pointer = output_pointer.offset(1);
                                            }
                                            102 => {
                                                *output_pointer =
                                                    '\u{c}' as i32 as core::ffi::c_uchar;
                                                let fresh3 = *output_pointer;
                                                output_pointer = output_pointer.offset(1);
                                            }
                                            110 => {
                                                *output_pointer = '\n' as i32 as core::ffi::c_uchar;
                                                let fresh4 = *output_pointer;
                                                output_pointer = output_pointer.offset(1);
                                            }
                                            114 => {
                                                *output_pointer = '\r' as i32 as core::ffi::c_uchar;
                                                let fresh5 = *output_pointer;
                                                output_pointer = output_pointer.offset(1);
                                            }
                                            116 => {
                                                *output_pointer = '\t' as i32 as core::ffi::c_uchar;
                                                let fresh6 = *output_pointer;
                                                output_pointer = output_pointer.offset(1);
                                            }
                                            34 | 92 | 47 => {
                                                *output_pointer = *input_pointer
                                                    .offset(1 as core::ffi::c_int as isize);
                                                let fresh7 = *output_pointer;
                                                output_pointer = output_pointer.offset(1);
                                            }
                                            117 => {
                                                sequence_length = utf16_literal_to_utf8(
                                                    input_pointer,
                                                    input_end,
                                                    &mut output_pointer,
                                                );
                                                if sequence_length as core::ffi::c_int
                                                    == 0 as core::ffi::c_int
                                                {
                                                    current_block = 10063478961057336850;
                                                    break;
                                                }
                                            }
                                            _ => {
                                                current_block = 10063478961057336850;
                                                break;
                                            }
                                        }
                                        input_pointer = input_pointer
                                            .offset(sequence_length as core::ffi::c_int as isize);
                                    }
                                }
                                match current_block {
                                    10063478961057336850 => {}
                                    _ => {
                                        *output_pointer = '\0' as i32 as core::ffi::c_uchar;
                                        (*item).type_0 = cJSON_String;
                                        (*item).valuestring = output as *mut core::ffi::c_char;
                                        (*input_buffer).offset = input_end
                                            .offset_from((*input_buffer).content)
                                            as core::ffi::c_long
                                            as size_t;
                                        (*input_buffer).offset =
                                            ((*input_buffer).offset).wrapping_add(1);
                                        return true_0;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            if !output.is_null() {
                ((*input_buffer).hooks.deallocate).expect("non-null function pointer")(
                    output as *mut core::ffi::c_void,
                );
                output = std::ptr::null_mut::<core::ffi::c_uchar>();
            }
            if !input_pointer.is_null() {
                (*input_buffer).offset = input_pointer.offset_from((*input_buffer).content)
                    as core::ffi::c_long as size_t;
            }
            false_0
        }
        unsafe extern "C" fn print_string_ptr(
            input: *const core::ffi::c_uchar,
            output_buffer: *mut printbuffer,
        ) -> cJSON_bool {
            let mut input_pointer: *const core::ffi::c_uchar =
                std::ptr::null::<core::ffi::c_uchar>();
            let mut output: *mut core::ffi::c_uchar = std::ptr::null_mut::<core::ffi::c_uchar>();
            let mut output_pointer: *mut core::ffi::c_uchar =
                std::ptr::null_mut::<core::ffi::c_uchar>();
            let mut output_length: size_t = 0 as size_t;
            let mut escape_characters: size_t = 0 as size_t;
            if output_buffer.is_null() {
                return false_0;
            }
            if input.is_null() {
                output = ensure(
                    output_buffer,
                    ::core::mem::size_of::<[core::ffi::c_char; 3]>() as size_t,
                );
                if output.is_null() {
                    return false_0;
                }
                strcpy(
                    output as *mut core::ffi::c_char,
                    b"\"\"\0" as *const u8 as *const core::ffi::c_char,
                );
                return true_0;
            }
            input_pointer = input;
            while *input_pointer != 0 {
                match *input_pointer as core::ffi::c_int {
                    34 | 92 | 8 | 12 | 10 | 13 | 9 => {
                        escape_characters = escape_characters.wrapping_add(1);
                    }
                    _ => {
                        if (*input_pointer as core::ffi::c_int) < 32 as core::ffi::c_int {
                            escape_characters = (escape_characters as core::ffi::c_ulong)
                                .wrapping_add(5 as core::ffi::c_ulong)
                                as size_t as size_t;
                        }
                    }
                }
                input_pointer = input_pointer.offset(1);
            }
            output_length = (input_pointer.offset_from(input) as core::ffi::c_long as size_t)
                .wrapping_add(escape_characters);
            output = ensure(
                output_buffer,
                output_length
                    .wrapping_add(::core::mem::size_of::<[core::ffi::c_char; 3]>() as size_t),
            );
            if output.is_null() {
                return false_0;
            }
            if escape_characters == 0 as size_t {
                *output.offset(0 as core::ffi::c_int as isize) = '"' as i32 as core::ffi::c_uchar;
                memcpy(
                    output.offset(1 as core::ffi::c_int as isize) as *mut core::ffi::c_void,
                    input as *const core::ffi::c_void,
                    output_length,
                );
                *output.add(output_length.wrapping_add(1 as size_t)) =
                    '"' as i32 as core::ffi::c_uchar;
                *output.add(output_length.wrapping_add(2 as size_t)) =
                    '\0' as i32 as core::ffi::c_uchar;
                return true_0;
            }
            *output.offset(0 as core::ffi::c_int as isize) = '"' as i32 as core::ffi::c_uchar;
            output_pointer = output.offset(1 as core::ffi::c_int as isize);
            input_pointer = input;
            while *input_pointer as core::ffi::c_int != '\0' as i32 {
                if *input_pointer as core::ffi::c_int > 31 as core::ffi::c_int
                    && *input_pointer as core::ffi::c_int != '"' as i32
                    && *input_pointer as core::ffi::c_int != '\\' as i32
                {
                    *output_pointer = *input_pointer;
                } else {
                    *output_pointer = '\\' as i32 as core::ffi::c_uchar;
                    let fresh21 = *output_pointer;
                    output_pointer = output_pointer.offset(1);
                    match *input_pointer as core::ffi::c_int {
                        92 => {
                            *output_pointer = '\\' as i32 as core::ffi::c_uchar;
                        }
                        34 => {
                            *output_pointer = '"' as i32 as core::ffi::c_uchar;
                        }
                        8 => {
                            *output_pointer = 'b' as i32 as core::ffi::c_uchar;
                        }
                        12 => {
                            *output_pointer = 'f' as i32 as core::ffi::c_uchar;
                        }
                        10 => {
                            *output_pointer = 'n' as i32 as core::ffi::c_uchar;
                        }
                        13 => {
                            *output_pointer = 'r' as i32 as core::ffi::c_uchar;
                        }
                        9 => {
                            *output_pointer = 't' as i32 as core::ffi::c_uchar;
                        }
                        _ => {
                            sprintf(
                                output_pointer as *mut core::ffi::c_char,
                                b"u%04x\0" as *const u8 as *const core::ffi::c_char,
                                *input_pointer as core::ffi::c_int,
                            );
                            output_pointer = output_pointer.offset(4 as core::ffi::c_int as isize);
                        }
                    }
                }
                input_pointer = input_pointer.offset(1);
                output_pointer = output_pointer.offset(1);
            }
            *output.add(output_length.wrapping_add(1 as size_t)) = '"' as i32 as core::ffi::c_uchar;
            *output.add(output_length.wrapping_add(2 as size_t)) =
                '\0' as i32 as core::ffi::c_uchar;
            true_0
        }
        unsafe extern "C" fn print_string(item: *const cJSON, p: *mut printbuffer) -> cJSON_bool {
            print_string_ptr((*item).valuestring as *mut core::ffi::c_uchar, p)
        }
        unsafe extern "C" fn buffer_skip_whitespace(
            buffer: *mut parse_buffer,
        ) -> *mut parse_buffer {
            if buffer.is_null() || ((*buffer).content).is_null() {
                return std::ptr::null_mut::<parse_buffer>();
            }
            if !(!buffer.is_null()
                && ((*buffer).offset).wrapping_add(0 as size_t) < (*buffer).length)
            {
                return buffer;
            }
            while !buffer.is_null()
                && ((*buffer).offset).wrapping_add(0 as size_t) < (*buffer).length
                && *((*buffer).content)
                    .add((*buffer).offset)
                    .offset(0 as core::ffi::c_int as isize) as core::ffi::c_int
                    <= 32 as core::ffi::c_int
            {
                (*buffer).offset = ((*buffer).offset).wrapping_add(1);
            }
            if (*buffer).offset == (*buffer).length {
                (*buffer).offset = ((*buffer).offset).wrapping_sub(1);
            }
            buffer
        }
        unsafe extern "C" fn skip_utf8_bom(buffer: *mut parse_buffer) -> *mut parse_buffer {
            if buffer.is_null() || ((*buffer).content).is_null() || (*buffer).offset != 0 as size_t
            {
                return std::ptr::null_mut::<parse_buffer>();
            }
            if !buffer.is_null()
                && ((*buffer).offset).wrapping_add(4 as size_t) < (*buffer).length
                && strncmp(
                    ((*buffer).content).add((*buffer).offset) as *const core::ffi::c_char,
                    b"\xEF\xBB\xBF\0" as *const u8 as *const core::ffi::c_char,
                    3 as size_t,
                ) == 0 as core::ffi::c_int
            {
                (*buffer).offset = ((*buffer).offset as core::ffi::c_ulong)
                    .wrapping_add(3 as core::ffi::c_ulong)
                    as size_t as size_t;
            }
            buffer
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_ParseWithOpts(
            value: *const core::ffi::c_char,
            return_parse_end: *mut *const core::ffi::c_char,
            require_null_terminated: cJSON_bool,
        ) -> *mut cJSON {
            let mut buffer_length: size_t = 0;
            if value.is_null() {
                return std::ptr::null_mut::<cJSON>();
            }
            buffer_length = (strlen(value))
                .wrapping_add(::core::mem::size_of::<[core::ffi::c_char; 1]>() as size_t);
            cJSON_ParseWithLengthOpts(
                value,
                buffer_length,
                return_parse_end,
                require_null_terminated,
            )
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_ParseWithLengthOpts(
            value: *const core::ffi::c_char,
            buffer_length: size_t,
            return_parse_end: *mut *const core::ffi::c_char,
            require_null_terminated: cJSON_bool,
        ) -> *mut cJSON {
            let current_block: u64;
            let mut buffer: parse_buffer = {
                parse_buffer {
                    content: std::ptr::null::<core::ffi::c_uchar>(),
                    length: 0 as size_t,
                    offset: 0 as size_t,
                    depth: 0 as size_t,
                    hooks: {
                        internal_hooks {
                            allocate: None,
                            deallocate: None,
                            reallocate: None,
                        }
                    },
                }
            };
            let mut item: *mut cJSON = std::ptr::null_mut::<cJSON>();
            global_error.json = std::ptr::null::<core::ffi::c_uchar>();
            global_error.position = 0 as size_t;
            if !(value.is_null() || 0 as size_t == buffer_length) {
                buffer.content = value as *const core::ffi::c_uchar;
                buffer.length = buffer_length;
                buffer.offset = 0 as size_t;
                buffer.hooks = global_hooks;
                item = cJSON_New_Item(&mut global_hooks);
                if !item.is_null()
                    && (parse_value(item, buffer_skip_whitespace(skip_utf8_bom(&mut buffer))) != 0)
                {
                    if require_null_terminated != 0 {
                        buffer_skip_whitespace(&mut buffer);
                        if buffer.offset >= buffer.length
                            || *(buffer.content)
                                .add(buffer.offset)
                                .offset(0 as core::ffi::c_int as isize)
                                as core::ffi::c_int
                                != '\0' as i32
                        {
                            current_block = 9251897605611739088;
                        } else {
                            current_block = 1841672684692190573;
                        }
                    } else {
                        current_block = 1841672684692190573;
                    }
                    match current_block {
                        9251897605611739088 => {}
                        _ => {
                            if !return_parse_end.is_null() {
                                *return_parse_end =
                                    (buffer.content).add(buffer.offset) as *const core::ffi::c_char;
                            }
                            return item;
                        }
                    }
                }
            }
            if !item.is_null() {
                cJSON_Delete(item);
            }
            if !value.is_null() {
                let mut local_error: error = error {
                    json: std::ptr::null::<core::ffi::c_uchar>(),
                    position: 0,
                };
                local_error.json = value as *const core::ffi::c_uchar;
                local_error.position = 0 as size_t;
                if buffer.offset < buffer.length {
                    local_error.position = buffer.offset;
                } else if buffer.length > 0 as size_t {
                    local_error.position = (buffer.length).wrapping_sub(1 as size_t);
                }
                if !return_parse_end.is_null() {
                    *return_parse_end =
                        (local_error.json as *const core::ffi::c_char).add(local_error.position);
                }
                global_error = local_error;
            }
            std::ptr::null_mut::<cJSON>()
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_Parse(value: *const core::ffi::c_char) -> *mut cJSON {
            cJSON_ParseWithOpts(
                value,
                std::ptr::null_mut::<*const core::ffi::c_char>(),
                0 as cJSON_bool,
            )
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_ParseWithLength(
            value: *const core::ffi::c_char,
            buffer_length: size_t,
        ) -> *mut cJSON {
            cJSON_ParseWithLengthOpts(
                value,
                buffer_length,
                std::ptr::null_mut::<*const core::ffi::c_char>(),
                0 as cJSON_bool,
            )
        }
        unsafe extern "C" fn print(
            item: *const cJSON,
            format: cJSON_bool,
            hooks: *const internal_hooks,
        ) -> *mut core::ffi::c_uchar {
            let current_block: u64;
            static mut default_buffer_size: size_t = 256 as size_t;
            let mut buffer: [printbuffer; 1] = [printbuffer {
                buffer: std::ptr::null_mut::<core::ffi::c_uchar>(),
                length: 0,
                offset: 0,
                depth: 0,
                noalloc: 0,
                format: 0,
                hooks: internal_hooks {
                    allocate: None,
                    deallocate: None,
                    reallocate: None,
                },
            }; 1];
            let mut printed: *mut core::ffi::c_uchar = std::ptr::null_mut::<core::ffi::c_uchar>();
            memset(
                buffer.as_mut_ptr() as *mut core::ffi::c_void,
                0 as core::ffi::c_int,
                ::core::mem::size_of::<[printbuffer; 1]>() as size_t,
            );
            (*buffer.as_mut_ptr()).buffer =
                ((*hooks).allocate).expect("non-null function pointer")(default_buffer_size)
                    as *mut core::ffi::c_uchar;
            (*buffer.as_mut_ptr()).length = default_buffer_size;
            (*buffer.as_mut_ptr()).format = format;
            (*buffer.as_mut_ptr()).hooks = *hooks;
            if !((*buffer.as_mut_ptr()).buffer).is_null()
                && (print_value(item, buffer.as_mut_ptr()) != 0)
            {
                update_offset(buffer.as_mut_ptr());
                if ((*hooks).reallocate).is_some() {
                    printed = ((*hooks).reallocate).expect("non-null function pointer")(
                        (*buffer.as_mut_ptr()).buffer as *mut core::ffi::c_void,
                        ((*buffer.as_mut_ptr()).offset).wrapping_add(1 as size_t),
                    ) as *mut core::ffi::c_uchar;
                    if printed.is_null() {
                        current_block = 3502048593697126715;
                    } else {
                        (*buffer.as_mut_ptr()).buffer = std::ptr::null_mut::<core::ffi::c_uchar>();
                        current_block = 7149356873433890176;
                    }
                } else {
                    printed = ((*hooks).allocate).expect("non-null function pointer")(
                        ((*buffer.as_mut_ptr()).offset).wrapping_add(1 as size_t),
                    ) as *mut core::ffi::c_uchar;
                    if printed.is_null() {
                        current_block = 3502048593697126715;
                    } else {
                        memcpy(
                            printed as *mut core::ffi::c_void,
                            (*buffer.as_mut_ptr()).buffer as *const core::ffi::c_void,
                            if (*buffer.as_mut_ptr()).length
                                < ((*buffer.as_mut_ptr()).offset).wrapping_add(1 as size_t)
                            {
                                (*buffer.as_mut_ptr()).length
                            } else {
                                ((*buffer.as_mut_ptr()).offset).wrapping_add(1 as size_t)
                            },
                        );
                        *printed.add((*buffer.as_mut_ptr()).offset) =
                            '\0' as i32 as core::ffi::c_uchar;
                        ((*hooks).deallocate).expect("non-null function pointer")(
                            (*buffer.as_mut_ptr()).buffer as *mut core::ffi::c_void,
                        );
                        (*buffer.as_mut_ptr()).buffer = std::ptr::null_mut::<core::ffi::c_uchar>();
                        current_block = 7149356873433890176;
                    }
                }
                match current_block {
                    3502048593697126715 => {}
                    _ => return printed,
                }
            }
            if !((*buffer.as_mut_ptr()).buffer).is_null() {
                ((*hooks).deallocate).expect("non-null function pointer")(
                    (*buffer.as_mut_ptr()).buffer as *mut core::ffi::c_void,
                );
                (*buffer.as_mut_ptr()).buffer = std::ptr::null_mut::<core::ffi::c_uchar>();
            }
            if !printed.is_null() {
                ((*hooks).deallocate).expect("non-null function pointer")(
                    printed as *mut core::ffi::c_void,
                );
                printed = std::ptr::null_mut::<core::ffi::c_uchar>();
            }
            std::ptr::null_mut::<core::ffi::c_uchar>()
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_Print(item: *const cJSON) -> *mut core::ffi::c_char {
            print(item, true_0, &mut global_hooks) as *mut core::ffi::c_char
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_PrintUnformatted(
            item: *const cJSON,
        ) -> *mut core::ffi::c_char {
            print(item, false_0, &mut global_hooks) as *mut core::ffi::c_char
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_PrintBuffered(
            item: *const cJSON,
            prebuffer: core::ffi::c_int,
            fmt: cJSON_bool,
        ) -> *mut core::ffi::c_char {
            let mut p: printbuffer = {
                printbuffer {
                    buffer: std::ptr::null_mut::<core::ffi::c_uchar>(),
                    length: 0 as size_t,
                    offset: 0 as size_t,
                    depth: 0 as size_t,
                    noalloc: 0 as cJSON_bool,
                    format: 0 as cJSON_bool,
                    hooks: {
                        internal_hooks {
                            allocate: None,
                            deallocate: None,
                            reallocate: None,
                        }
                    },
                }
            };
            if prebuffer < 0 as core::ffi::c_int {
                return std::ptr::null_mut::<core::ffi::c_char>();
            }
            p.buffer =
                (global_hooks.allocate).expect("non-null function pointer")(prebuffer as size_t)
                    as *mut core::ffi::c_uchar;
            if (p.buffer).is_null() {
                return std::ptr::null_mut::<core::ffi::c_char>();
            }
            p.length = prebuffer as size_t;
            p.offset = 0 as size_t;
            p.noalloc = false_0;
            p.format = fmt;
            p.hooks = global_hooks;
            if print_value(item, &mut p) == 0 {
                (global_hooks.deallocate).expect("non-null function pointer")(
                    p.buffer as *mut core::ffi::c_void,
                );
                p.buffer = std::ptr::null_mut::<core::ffi::c_uchar>();
                return std::ptr::null_mut::<core::ffi::c_char>();
            }
            p.buffer as *mut core::ffi::c_char
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_PrintPreallocated(
            item: *mut cJSON,
            buffer: *mut core::ffi::c_char,
            length: core::ffi::c_int,
            format: cJSON_bool,
        ) -> cJSON_bool {
            let mut p: printbuffer = {
                printbuffer {
                    buffer: std::ptr::null_mut::<core::ffi::c_uchar>(),
                    length: 0 as size_t,
                    offset: 0 as size_t,
                    depth: 0 as size_t,
                    noalloc: 0 as cJSON_bool,
                    format: 0 as cJSON_bool,
                    hooks: {
                        internal_hooks {
                            allocate: None,
                            deallocate: None,
                            reallocate: None,
                        }
                    },
                }
            };
            if length < 0 as core::ffi::c_int || buffer.is_null() {
                return false_0;
            }
            p.buffer = buffer as *mut core::ffi::c_uchar;
            p.length = length as size_t;
            p.offset = 0 as size_t;
            p.noalloc = true_0;
            p.format = format;
            p.hooks = global_hooks;
            print_value(item, &mut p)
        }
        unsafe extern "C" fn parse_value(
            item: *mut cJSON,
            input_buffer: *mut parse_buffer,
        ) -> cJSON_bool {
            if input_buffer.is_null() || ((*input_buffer).content).is_null() {
                return false_0;
            }
            if !input_buffer.is_null()
                && ((*input_buffer).offset).wrapping_add(4 as size_t) <= (*input_buffer).length
                && strncmp(
                    ((*input_buffer).content).add((*input_buffer).offset)
                        as *const core::ffi::c_char,
                    b"null\0" as *const u8 as *const core::ffi::c_char,
                    4 as size_t,
                ) == 0 as core::ffi::c_int
            {
                (*item).type_0 = cJSON_NULL;
                (*input_buffer).offset = ((*input_buffer).offset as core::ffi::c_ulong)
                    .wrapping_add(4 as core::ffi::c_ulong)
                    as size_t as size_t;
                return true_0;
            }
            if !input_buffer.is_null()
                && ((*input_buffer).offset).wrapping_add(5 as size_t) <= (*input_buffer).length
                && strncmp(
                    ((*input_buffer).content).add((*input_buffer).offset)
                        as *const core::ffi::c_char,
                    b"false\0" as *const u8 as *const core::ffi::c_char,
                    5 as size_t,
                ) == 0 as core::ffi::c_int
            {
                (*item).type_0 = cJSON_False;
                (*input_buffer).offset = ((*input_buffer).offset as core::ffi::c_ulong)
                    .wrapping_add(5 as core::ffi::c_ulong)
                    as size_t as size_t;
                return true_0;
            }
            if !input_buffer.is_null()
                && ((*input_buffer).offset).wrapping_add(4 as size_t) <= (*input_buffer).length
                && strncmp(
                    ((*input_buffer).content).add((*input_buffer).offset)
                        as *const core::ffi::c_char,
                    b"true\0" as *const u8 as *const core::ffi::c_char,
                    4 as size_t,
                ) == 0 as core::ffi::c_int
            {
                (*item).type_0 = cJSON_True;
                (*item).valueint = 1 as core::ffi::c_int;
                (*input_buffer).offset = ((*input_buffer).offset as core::ffi::c_ulong)
                    .wrapping_add(4 as core::ffi::c_ulong)
                    as size_t as size_t;
                return true_0;
            }
            if !input_buffer.is_null()
                && ((*input_buffer).offset).wrapping_add(0 as size_t) < (*input_buffer).length
                && *((*input_buffer).content)
                    .add((*input_buffer).offset)
                    .offset(0 as core::ffi::c_int as isize) as core::ffi::c_int
                    == '"' as i32
            {
                return parse_string(item, input_buffer);
            }
            if !input_buffer.is_null()
                && ((*input_buffer).offset).wrapping_add(0 as size_t) < (*input_buffer).length
                && (*((*input_buffer).content)
                    .add((*input_buffer).offset)
                    .offset(0 as core::ffi::c_int as isize) as core::ffi::c_int
                    == '-' as i32
                    || *((*input_buffer).content)
                        .add((*input_buffer).offset)
                        .offset(0 as core::ffi::c_int as isize)
                        as core::ffi::c_int
                        >= '0' as i32
                        && *((*input_buffer).content)
                            .add((*input_buffer).offset)
                            .offset(0 as core::ffi::c_int as isize)
                            as core::ffi::c_int
                            <= '9' as i32)
            {
                return parse_number(item, input_buffer);
            }
            if !input_buffer.is_null()
                && ((*input_buffer).offset).wrapping_add(0 as size_t) < (*input_buffer).length
                && *((*input_buffer).content)
                    .add((*input_buffer).offset)
                    .offset(0 as core::ffi::c_int as isize) as core::ffi::c_int
                    == '[' as i32
            {
                return parse_array(item, input_buffer);
            }
            if !input_buffer.is_null()
                && ((*input_buffer).offset).wrapping_add(0 as size_t) < (*input_buffer).length
                && *((*input_buffer).content)
                    .add((*input_buffer).offset)
                    .offset(0 as core::ffi::c_int as isize) as core::ffi::c_int
                    == '{' as i32
            {
                return parse_object(item, input_buffer);
            }
            false_0
        }
        unsafe extern "C" fn print_value(
            item: *const cJSON,
            output_buffer: *mut printbuffer,
        ) -> cJSON_bool {
            let mut output: *mut core::ffi::c_uchar = std::ptr::null_mut::<core::ffi::c_uchar>();
            if item.is_null() || output_buffer.is_null() {
                return false_0;
            }
            match (*item).type_0 & 0xff as core::ffi::c_int {
                cJSON_NULL => {
                    output = ensure(output_buffer, 5 as size_t);
                    if output.is_null() {
                        return false_0;
                    }
                    strcpy(
                        output as *mut core::ffi::c_char,
                        b"null\0" as *const u8 as *const core::ffi::c_char,
                    );
                    true_0
                }
                cJSON_False => {
                    output = ensure(output_buffer, 6 as size_t);
                    if output.is_null() {
                        return false_0;
                    }
                    strcpy(
                        output as *mut core::ffi::c_char,
                        b"false\0" as *const u8 as *const core::ffi::c_char,
                    );
                    true_0
                }
                cJSON_True => {
                    output = ensure(output_buffer, 5 as size_t);
                    if output.is_null() {
                        return false_0;
                    }
                    strcpy(
                        output as *mut core::ffi::c_char,
                        b"true\0" as *const u8 as *const core::ffi::c_char,
                    );
                    true_0
                }
                cJSON_Number => print_number(item, output_buffer),
                cJSON_Raw => {
                    let mut raw_length: size_t = 0 as size_t;
                    if ((*item).valuestring).is_null() {
                        return false_0;
                    }
                    raw_length = (strlen((*item).valuestring))
                        .wrapping_add(::core::mem::size_of::<[core::ffi::c_char; 1]>() as size_t);
                    output = ensure(output_buffer, raw_length);
                    if output.is_null() {
                        return false_0;
                    }
                    memcpy(
                        output as *mut core::ffi::c_void,
                        (*item).valuestring as *const core::ffi::c_void,
                        raw_length,
                    );
                    true_0
                }
                cJSON_String => print_string(item, output_buffer),
                cJSON_Array => print_array(item, output_buffer),
                cJSON_Object => print_object(item, output_buffer),
                _ => false_0,
            }
        }
        unsafe extern "C" fn parse_array(
            item: *mut cJSON,
            input_buffer: *mut parse_buffer,
        ) -> cJSON_bool {
            let mut current_block: u64;
            let mut head: *mut cJSON = std::ptr::null_mut::<cJSON>();
            let mut current_item: *mut cJSON = std::ptr::null_mut::<cJSON>();
            if (*input_buffer).depth >= CJSON_NESTING_LIMIT as size_t {
                return false_0;
            }
            (*input_buffer).depth = ((*input_buffer).depth).wrapping_add(1);
            if *((*input_buffer).content)
                .add((*input_buffer).offset)
                .offset(0 as core::ffi::c_int as isize) as core::ffi::c_int
                == '[' as i32
            {
                (*input_buffer).offset = ((*input_buffer).offset).wrapping_add(1);
                buffer_skip_whitespace(input_buffer);
                if !input_buffer.is_null()
                    && ((*input_buffer).offset).wrapping_add(0 as size_t) < (*input_buffer).length
                    && *((*input_buffer).content)
                        .add((*input_buffer).offset)
                        .offset(0 as core::ffi::c_int as isize)
                        as core::ffi::c_int
                        == ']' as i32
                {
                    current_block = 10437877545879587800;
                } else if !(!input_buffer.is_null()
                    && ((*input_buffer).offset).wrapping_add(0 as size_t) < (*input_buffer).length)
                {
                    (*input_buffer).offset = ((*input_buffer).offset).wrapping_sub(1);
                    current_block = 9392365638336364342;
                } else {
                    (*input_buffer).offset = ((*input_buffer).offset).wrapping_sub(1);
                    loop {
                        let new_item: *mut cJSON = cJSON_New_Item(&mut (*input_buffer).hooks);
                        if new_item.is_null() {
                            current_block = 9392365638336364342;
                            break;
                        }
                        if head.is_null() {
                            head = new_item;
                            current_item = head;
                        } else {
                            (*current_item).next = new_item as *mut cJSON;
                            (*new_item).prev = current_item as *mut cJSON;
                            current_item = new_item;
                        }
                        (*input_buffer).offset = ((*input_buffer).offset).wrapping_add(1);
                        buffer_skip_whitespace(input_buffer);
                        if parse_value(current_item, input_buffer) == 0 {
                            current_block = 9392365638336364342;
                            break;
                        }
                        buffer_skip_whitespace(input_buffer);
                        if !(!input_buffer.is_null()
                            && ((*input_buffer).offset).wrapping_add(0 as size_t)
                                < (*input_buffer).length
                            && *((*input_buffer).content)
                                .add((*input_buffer).offset)
                                .offset(0 as core::ffi::c_int as isize)
                                as core::ffi::c_int
                                == ',' as i32)
                        {
                            current_block = 15089075282327824602;
                            break;
                        }
                    }
                    match current_block {
                        9392365638336364342 => {}
                        _ => {
                            if !(!input_buffer.is_null()
                                && ((*input_buffer).offset).wrapping_add(0 as size_t)
                                    < (*input_buffer).length)
                                || *((*input_buffer).content)
                                    .add((*input_buffer).offset)
                                    .offset(0 as core::ffi::c_int as isize)
                                    as core::ffi::c_int
                                    != ']' as i32
                            {
                                current_block = 9392365638336364342;
                            } else {
                                current_block = 10437877545879587800;
                            }
                        }
                    }
                }
                match current_block {
                    9392365638336364342 => {}
                    _ => {
                        (*input_buffer).depth = ((*input_buffer).depth).wrapping_sub(1);
                        if !head.is_null() {
                            (*head).prev = current_item as *mut cJSON;
                        }
                        (*item).type_0 = cJSON_Array;
                        (*item).child = head as *mut cJSON;
                        (*input_buffer).offset = ((*input_buffer).offset).wrapping_add(1);
                        return true_0;
                    }
                }
            }
            if !head.is_null() {
                cJSON_Delete(head);
            }
            false_0
        }
        unsafe extern "C" fn print_array(
            item: *const cJSON,
            output_buffer: *mut printbuffer,
        ) -> cJSON_bool {
            let mut output_pointer: *mut core::ffi::c_uchar =
                std::ptr::null_mut::<core::ffi::c_uchar>();
            let mut length: size_t = 0 as size_t;
            let mut current_element: *mut cJSON = (*item).child as *mut cJSON;
            if output_buffer.is_null() {
                return false_0;
            }
            output_pointer = ensure(output_buffer, 1 as size_t);
            if output_pointer.is_null() {
                return false_0;
            }
            *output_pointer = '[' as i32 as core::ffi::c_uchar;
            (*output_buffer).offset = ((*output_buffer).offset).wrapping_add(1);
            (*output_buffer).depth = ((*output_buffer).depth).wrapping_add(1);
            while !current_element.is_null() {
                if print_value(current_element, output_buffer) == 0 {
                    return false_0;
                }
                update_offset(output_buffer);
                if !((*current_element).next).is_null() {
                    length = (if (*output_buffer).format != 0 {
                        2 as core::ffi::c_int
                    } else {
                        1 as core::ffi::c_int
                    }) as size_t;
                    output_pointer = ensure(output_buffer, length.wrapping_add(1 as size_t));
                    if output_pointer.is_null() {
                        return false_0;
                    }
                    *output_pointer = ',' as i32 as core::ffi::c_uchar;
                    let fresh22 = *output_pointer;
                    output_pointer = output_pointer.offset(1);
                    if (*output_buffer).format != 0 {
                        *output_pointer = ' ' as i32 as core::ffi::c_uchar;
                        let fresh23 = *output_pointer;
                        output_pointer = output_pointer.offset(1);
                    }
                    *output_pointer = '\0' as i32 as core::ffi::c_uchar;
                    (*output_buffer).offset = ((*output_buffer).offset as core::ffi::c_ulong)
                        .wrapping_add(length as core::ffi::c_ulong)
                        as size_t as size_t;
                }
                current_element = (*current_element).next as *mut cJSON;
            }
            output_pointer = ensure(output_buffer, 2 as size_t);
            if output_pointer.is_null() {
                return false_0;
            }
            *output_pointer = ']' as i32 as core::ffi::c_uchar;
            let fresh24 = *output_pointer;
            output_pointer = output_pointer.offset(1);
            *output_pointer = '\0' as i32 as core::ffi::c_uchar;
            (*output_buffer).depth = ((*output_buffer).depth).wrapping_sub(1);
            true_0
        }
        unsafe extern "C" fn parse_object(
            item: *mut cJSON,
            input_buffer: *mut parse_buffer,
        ) -> cJSON_bool {
            let mut current_block: u64;
            let mut head: *mut cJSON = std::ptr::null_mut::<cJSON>();
            let mut current_item: *mut cJSON = std::ptr::null_mut::<cJSON>();
            if (*input_buffer).depth >= CJSON_NESTING_LIMIT as size_t {
                return false_0;
            }
            (*input_buffer).depth = ((*input_buffer).depth).wrapping_add(1);
            if !(!(!input_buffer.is_null()
                && ((*input_buffer).offset).wrapping_add(0 as size_t) < (*input_buffer).length)
                || *((*input_buffer).content)
                    .add((*input_buffer).offset)
                    .offset(0 as core::ffi::c_int as isize) as core::ffi::c_int
                    != '{' as i32)
            {
                (*input_buffer).offset = ((*input_buffer).offset).wrapping_add(1);
                buffer_skip_whitespace(input_buffer);
                if !input_buffer.is_null()
                    && ((*input_buffer).offset).wrapping_add(0 as size_t) < (*input_buffer).length
                    && *((*input_buffer).content)
                        .add((*input_buffer).offset)
                        .offset(0 as core::ffi::c_int as isize)
                        as core::ffi::c_int
                        == '}' as i32
                {
                    current_block = 1266867152802447262;
                } else if !(!input_buffer.is_null()
                    && ((*input_buffer).offset).wrapping_add(0 as size_t) < (*input_buffer).length)
                {
                    (*input_buffer).offset = ((*input_buffer).offset).wrapping_sub(1);
                    current_block = 6321287469578562981;
                } else {
                    (*input_buffer).offset = ((*input_buffer).offset).wrapping_sub(1);
                    loop {
                        let new_item: *mut cJSON = cJSON_New_Item(&mut (*input_buffer).hooks);
                        if new_item.is_null() {
                            current_block = 6321287469578562981;
                            break;
                        } else {
                            if head.is_null() {
                                head = new_item;
                                current_item = head;
                            } else {
                                (*current_item).next = new_item as *mut cJSON;
                                (*new_item).prev = current_item as *mut cJSON;
                                current_item = new_item;
                            }
                            if !(!input_buffer.is_null()
                                && ((*input_buffer).offset).wrapping_add(1 as size_t)
                                    < (*input_buffer).length)
                            {
                                current_block = 6321287469578562981;
                                break;
                            } else {
                                (*input_buffer).offset = ((*input_buffer).offset).wrapping_add(1);
                                buffer_skip_whitespace(input_buffer);
                                if parse_string(current_item, input_buffer) == 0 {
                                    current_block = 6321287469578562981;
                                    break;
                                } else {
                                    buffer_skip_whitespace(input_buffer);
                                    (*current_item).string = (*current_item).valuestring;
                                    (*current_item).valuestring =
                                        std::ptr::null_mut::<core::ffi::c_char>();
                                    if !(!input_buffer.is_null()
                                        && ((*input_buffer).offset).wrapping_add(0 as size_t)
                                            < (*input_buffer).length)
                                        || *((*input_buffer).content)
                                            .add((*input_buffer).offset)
                                            .offset(0 as core::ffi::c_int as isize)
                                            as core::ffi::c_int
                                            != ':' as i32
                                    {
                                        current_block = 6321287469578562981;
                                        break;
                                    } else {
                                        (*input_buffer).offset =
                                            ((*input_buffer).offset).wrapping_add(1);
                                        buffer_skip_whitespace(input_buffer);
                                        if parse_value(current_item, input_buffer) == 0 {
                                            current_block = 6321287469578562981;
                                            break;
                                        } else {
                                            buffer_skip_whitespace(input_buffer);
                                            if !(!input_buffer.is_null()
                                                && ((*input_buffer).offset)
                                                    .wrapping_add(0 as size_t)
                                                    < (*input_buffer).length
                                                && *((*input_buffer).content)
                                                    .add((*input_buffer).offset)
                                                    .offset(0 as core::ffi::c_int as isize)
                                                    as core::ffi::c_int
                                                    == ',' as i32)
                                            {
                                                current_block = 14359455889292382949;
                                                break;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    match current_block {
                        6321287469578562981 => {}
                        _ => {
                            if !(!input_buffer.is_null()
                                && ((*input_buffer).offset).wrapping_add(0 as size_t)
                                    < (*input_buffer).length)
                                || *((*input_buffer).content)
                                    .add((*input_buffer).offset)
                                    .offset(0 as core::ffi::c_int as isize)
                                    as core::ffi::c_int
                                    != '}' as i32
                            {
                                current_block = 6321287469578562981;
                            } else {
                                current_block = 1266867152802447262;
                            }
                        }
                    }
                }
                match current_block {
                    6321287469578562981 => {}
                    _ => {
                        (*input_buffer).depth = ((*input_buffer).depth).wrapping_sub(1);
                        if !head.is_null() {
                            (*head).prev = current_item as *mut cJSON;
                        }
                        (*item).type_0 = cJSON_Object;
                        (*item).child = head as *mut cJSON;
                        (*input_buffer).offset = ((*input_buffer).offset).wrapping_add(1);
                        return true_0;
                    }
                }
            }
            if !head.is_null() {
                cJSON_Delete(head);
            }
            false_0
        }
        unsafe extern "C" fn print_object(
            item: *const cJSON,
            output_buffer: *mut printbuffer,
        ) -> cJSON_bool {
            let mut output_pointer: *mut core::ffi::c_uchar =
                std::ptr::null_mut::<core::ffi::c_uchar>();
            let mut length: size_t = 0 as size_t;
            let mut current_item: *mut cJSON = (*item).child as *mut cJSON;
            if output_buffer.is_null() {
                return false_0;
            }
            length = (if (*output_buffer).format != 0 {
                2 as core::ffi::c_int
            } else {
                1 as core::ffi::c_int
            }) as size_t;
            output_pointer = ensure(output_buffer, length.wrapping_add(1 as size_t));
            if output_pointer.is_null() {
                return false_0;
            }
            *output_pointer = '{' as i32 as core::ffi::c_uchar;
            let fresh12 = *output_pointer;
            output_pointer = output_pointer.offset(1);
            (*output_buffer).depth = ((*output_buffer).depth).wrapping_add(1);
            if (*output_buffer).format != 0 {
                *output_pointer = '\n' as i32 as core::ffi::c_uchar;
                let fresh13 = *output_pointer;
                output_pointer = output_pointer.offset(1);
            }
            (*output_buffer).offset = ((*output_buffer).offset as core::ffi::c_ulong)
                .wrapping_add(length as core::ffi::c_ulong)
                as size_t as size_t;
            while !current_item.is_null() {
                if (*output_buffer).format != 0 {
                    let mut i: size_t = 0;
                    output_pointer = ensure(output_buffer, (*output_buffer).depth);
                    if output_pointer.is_null() {
                        return false_0;
                    }
                    i = 0 as size_t;
                    while i < (*output_buffer).depth {
                        *output_pointer = '\t' as i32 as core::ffi::c_uchar;
                        let fresh14 = *output_pointer;
                        output_pointer = output_pointer.offset(1);
                        i = i.wrapping_add(1);
                    }
                    (*output_buffer).offset = ((*output_buffer).offset as core::ffi::c_ulong)
                        .wrapping_add((*output_buffer).depth as core::ffi::c_ulong)
                        as size_t as size_t;
                }
                if print_string_ptr(
                    (*current_item).string as *mut core::ffi::c_uchar,
                    output_buffer,
                ) == 0
                {
                    return false_0;
                }
                update_offset(output_buffer);
                length = (if (*output_buffer).format != 0 {
                    2 as core::ffi::c_int
                } else {
                    1 as core::ffi::c_int
                }) as size_t;
                output_pointer = ensure(output_buffer, length);
                if output_pointer.is_null() {
                    return false_0;
                }
                *output_pointer = ':' as i32 as core::ffi::c_uchar;
                let fresh15 = *output_pointer;
                output_pointer = output_pointer.offset(1);
                if (*output_buffer).format != 0 {
                    *output_pointer = '\t' as i32 as core::ffi::c_uchar;
                    let fresh16 = *output_pointer;
                    output_pointer = output_pointer.offset(1);
                }
                (*output_buffer).offset = ((*output_buffer).offset as core::ffi::c_ulong)
                    .wrapping_add(length as core::ffi::c_ulong)
                    as size_t as size_t;
                if print_value(current_item, output_buffer) == 0 {
                    return false_0;
                }
                update_offset(output_buffer);
                length = ((if (*output_buffer).format != 0 {
                    1 as core::ffi::c_int
                } else {
                    0 as core::ffi::c_int
                }) as size_t)
                    .wrapping_add(
                        (if !((*current_item).next).is_null() {
                            1 as core::ffi::c_int
                        } else {
                            0 as core::ffi::c_int
                        }) as size_t,
                    );
                output_pointer = ensure(output_buffer, length.wrapping_add(1 as size_t));
                if output_pointer.is_null() {
                    return false_0;
                }
                if !((*current_item).next).is_null() {
                    *output_pointer = ',' as i32 as core::ffi::c_uchar;
                    let fresh17 = *output_pointer;
                    output_pointer = output_pointer.offset(1);
                }
                if (*output_buffer).format != 0 {
                    *output_pointer = '\n' as i32 as core::ffi::c_uchar;
                    let fresh18 = *output_pointer;
                    output_pointer = output_pointer.offset(1);
                }
                *output_pointer = '\0' as i32 as core::ffi::c_uchar;
                (*output_buffer).offset = ((*output_buffer).offset as core::ffi::c_ulong)
                    .wrapping_add(length as core::ffi::c_ulong)
                    as size_t as size_t;
                current_item = (*current_item).next as *mut cJSON;
            }
            output_pointer = ensure(
                output_buffer,
                if (*output_buffer).format != 0 {
                    ((*output_buffer).depth).wrapping_add(1 as size_t)
                } else {
                    2 as size_t
                },
            );
            if output_pointer.is_null() {
                return false_0;
            }
            if (*output_buffer).format != 0 {
                let mut i_0: size_t = 0;
                i_0 = 0 as size_t;
                while i_0 < ((*output_buffer).depth).wrapping_sub(1 as size_t) {
                    *output_pointer = '\t' as i32 as core::ffi::c_uchar;
                    let fresh19 = *output_pointer;
                    output_pointer = output_pointer.offset(1);
                    i_0 = i_0.wrapping_add(1);
                }
            }
            *output_pointer = '}' as i32 as core::ffi::c_uchar;
            let fresh20 = *output_pointer;
            output_pointer = output_pointer.offset(1);
            *output_pointer = '\0' as i32 as core::ffi::c_uchar;
            (*output_buffer).depth = ((*output_buffer).depth).wrapping_sub(1);
            true_0
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_GetArraySize(array: *const cJSON) -> core::ffi::c_int {
            let mut child: *mut cJSON = std::ptr::null_mut::<cJSON>();
            let mut size: size_t = 0 as size_t;
            if array.is_null() {
                return 0 as core::ffi::c_int;
            }
            child = (*array).child as *mut cJSON;
            while !child.is_null() {
                size = size.wrapping_add(1);
                child = (*child).next as *mut cJSON;
            }
            size as core::ffi::c_int
        }
        unsafe extern "C" fn get_array_item(array: *const cJSON, mut index: size_t) -> *mut cJSON {
            let mut current_child: *mut cJSON = std::ptr::null_mut::<cJSON>();
            if array.is_null() {
                return std::ptr::null_mut::<cJSON>();
            }
            current_child = (*array).child as *mut cJSON;
            while !current_child.is_null() && index > 0 as size_t {
                index = index.wrapping_sub(1);
                current_child = (*current_child).next as *mut cJSON;
            }
            current_child
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_GetArrayItem(
            array: *const cJSON,
            index: core::ffi::c_int,
        ) -> *mut cJSON {
            if index < 0 as core::ffi::c_int {
                return std::ptr::null_mut::<cJSON>();
            }
            get_array_item(array, index as size_t)
        }
        unsafe extern "C" fn get_object_item(
            object: *const cJSON,
            name: *const core::ffi::c_char,
            case_sensitive: cJSON_bool,
        ) -> *mut cJSON {
            let mut current_element: *mut cJSON = std::ptr::null_mut::<cJSON>();
            if object.is_null() || name.is_null() {
                return std::ptr::null_mut::<cJSON>();
            }
            current_element = (*object).child as *mut cJSON;
            if case_sensitive != 0 {
                while !current_element.is_null()
                    && !((*current_element).string).is_null()
                    && strcmp(name, (*current_element).string) != 0 as core::ffi::c_int
                {
                    current_element = (*current_element).next as *mut cJSON;
                }
            } else {
                while !current_element.is_null()
                    && case_insensitive_strcmp(
                        name as *const core::ffi::c_uchar,
                        (*current_element).string as *const core::ffi::c_uchar,
                    ) != 0 as core::ffi::c_int
                {
                    current_element = (*current_element).next as *mut cJSON;
                }
            }
            if current_element.is_null() || ((*current_element).string).is_null() {
                return std::ptr::null_mut::<cJSON>();
            }
            current_element
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_GetObjectItem(
            object: *const cJSON,
            string: *const core::ffi::c_char,
        ) -> *mut cJSON {
            get_object_item(object, string, false_0)
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_GetObjectItemCaseSensitive(
            object: *const cJSON,
            string: *const core::ffi::c_char,
        ) -> *mut cJSON {
            get_object_item(object, string, true_0)
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_HasObjectItem(
            object: *const cJSON,
            string: *const core::ffi::c_char,
        ) -> cJSON_bool {
            if !(cJSON_GetObjectItem(object, string)).is_null() {
                1 as cJSON_bool
            } else {
                0 as cJSON_bool
            }
        }
        unsafe extern "C" fn suffix_object(prev: *mut cJSON, item: *mut cJSON) {
            (*prev).next = item as *mut cJSON;
            (*item).prev = prev as *mut cJSON;
        }
        unsafe extern "C" fn create_reference(
            item: *const cJSON,
            hooks: *const internal_hooks,
        ) -> *mut cJSON {
            let mut reference: *mut cJSON = std::ptr::null_mut::<cJSON>();
            if item.is_null() {
                return std::ptr::null_mut::<cJSON>();
            }
            reference = cJSON_New_Item(hooks);
            if reference.is_null() {
                return std::ptr::null_mut::<cJSON>();
            }
            memcpy(
                reference as *mut core::ffi::c_void,
                item as *const core::ffi::c_void,
                ::core::mem::size_of::<cJSON>() as size_t,
            );
            (*reference).string = std::ptr::null_mut::<core::ffi::c_char>();
            (*reference).type_0 |= cJSON_IsReference;
            (*reference).prev = std::ptr::null_mut::<cJSON>();
            (*reference).next = (*reference).prev;
            reference
        }
        unsafe extern "C" fn add_item_to_array(array: *mut cJSON, item: *mut cJSON) -> cJSON_bool {
            let mut child: *mut cJSON = std::ptr::null_mut::<cJSON>();
            if item.is_null() || array.is_null() || array == item {
                return false_0;
            }
            child = (*array).child as *mut cJSON;
            if child.is_null() {
                (*array).child = item as *mut cJSON;
                (*item).prev = item as *mut cJSON;
                (*item).next = std::ptr::null_mut::<cJSON>();
            } else if !((*child).prev).is_null() {
                suffix_object((*child).prev as *mut cJSON, item);
                (*(*array).child).prev = item as *mut cJSON;
            }
            true_0
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_AddItemToArray(
            array: *mut cJSON,
            item: *mut cJSON,
        ) -> cJSON_bool {
            add_item_to_array(array, item)
        }
        unsafe extern "C" fn cast_away_const(
            string: *const core::ffi::c_void,
        ) -> *mut core::ffi::c_void {
            string as *mut core::ffi::c_void
        }
        unsafe extern "C" fn add_item_to_object(
            object: *mut cJSON,
            string: *const core::ffi::c_char,
            item: *mut cJSON,
            hooks: *const internal_hooks,
            constant_key: cJSON_bool,
        ) -> cJSON_bool {
            let mut new_key: *mut core::ffi::c_char = std::ptr::null_mut::<core::ffi::c_char>();
            let mut new_type: core::ffi::c_int = cJSON_Invalid;
            if object.is_null() || string.is_null() || item.is_null() || object == item {
                return false_0;
            }
            if constant_key != 0 {
                new_key =
                    cast_away_const(string as *const core::ffi::c_void) as *mut core::ffi::c_char;
                new_type = (*item).type_0 | cJSON_StringIsConst;
            } else {
                new_key = cJSON_strdup(string as *const core::ffi::c_uchar, hooks)
                    as *mut core::ffi::c_char;
                if new_key.is_null() {
                    return false_0;
                }
                new_type = (*item).type_0 & !cJSON_StringIsConst;
            }
            if (*item).type_0 & cJSON_StringIsConst == 0 && !((*item).string).is_null() {
                ((*hooks).deallocate).expect("non-null function pointer")(
                    (*item).string as *mut core::ffi::c_void,
                );
            }
            (*item).string = new_key;
            (*item).type_0 = new_type;
            add_item_to_array(object, item)
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_AddItemToObject(
            object: *mut cJSON,
            string: *const core::ffi::c_char,
            item: *mut cJSON,
        ) -> cJSON_bool {
            add_item_to_object(object, string, item, &mut global_hooks, false_0)
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_AddItemToObjectCS(
            object: *mut cJSON,
            string: *const core::ffi::c_char,
            item: *mut cJSON,
        ) -> cJSON_bool {
            add_item_to_object(object, string, item, &mut global_hooks, true_0)
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_AddItemReferenceToArray(
            array: *mut cJSON,
            item: *mut cJSON,
        ) -> cJSON_bool {
            if array.is_null() {
                return false_0;
            }
            add_item_to_array(array, create_reference(item, &mut global_hooks))
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_AddItemReferenceToObject(
            object: *mut cJSON,
            string: *const core::ffi::c_char,
            item: *mut cJSON,
        ) -> cJSON_bool {
            if object.is_null() || string.is_null() {
                return false_0;
            }
            add_item_to_object(
                object,
                string,
                create_reference(item, &mut global_hooks),
                &mut global_hooks,
                false_0,
            )
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_AddNullToObject(
            object: *mut cJSON,
            name: *const core::ffi::c_char,
        ) -> *mut cJSON {
            let null: *mut cJSON = cJSON_CreateNull();
            if add_item_to_object(object, name, null, &mut global_hooks, false_0) != 0 {
                return null;
            }
            cJSON_Delete(null);
            std::ptr::null_mut::<cJSON>()
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_AddTrueToObject(
            object: *mut cJSON,
            name: *const core::ffi::c_char,
        ) -> *mut cJSON {
            let true_item: *mut cJSON = cJSON_CreateTrue();
            if add_item_to_object(object, name, true_item, &mut global_hooks, false_0) != 0 {
                return true_item;
            }
            cJSON_Delete(true_item);
            std::ptr::null_mut::<cJSON>()
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_AddFalseToObject(
            object: *mut cJSON,
            name: *const core::ffi::c_char,
        ) -> *mut cJSON {
            let false_item: *mut cJSON = cJSON_CreateFalse();
            if add_item_to_object(object, name, false_item, &mut global_hooks, false_0) != 0 {
                return false_item;
            }
            cJSON_Delete(false_item);
            std::ptr::null_mut::<cJSON>()
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_AddBoolToObject(
            object: *mut cJSON,
            name: *const core::ffi::c_char,
            boolean: cJSON_bool,
        ) -> *mut cJSON {
            let bool_item: *mut cJSON = cJSON_CreateBool(boolean);
            if add_item_to_object(object, name, bool_item, &mut global_hooks, false_0) != 0 {
                return bool_item;
            }
            cJSON_Delete(bool_item);
            std::ptr::null_mut::<cJSON>()
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_AddNumberToObject(
            object: *mut cJSON,
            name: *const core::ffi::c_char,
            number: core::ffi::c_double,
        ) -> *mut cJSON {
            let number_item: *mut cJSON = cJSON_CreateNumber(number);
            if add_item_to_object(object, name, number_item, &mut global_hooks, false_0) != 0 {
                return number_item;
            }
            cJSON_Delete(number_item);
            std::ptr::null_mut::<cJSON>()
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_AddStringToObject(
            object: *mut cJSON,
            name: *const core::ffi::c_char,
            string: *const core::ffi::c_char,
        ) -> *mut cJSON {
            let string_item: *mut cJSON = cJSON_CreateString(string);
            if add_item_to_object(object, name, string_item, &mut global_hooks, false_0) != 0 {
                return string_item;
            }
            cJSON_Delete(string_item);
            std::ptr::null_mut::<cJSON>()
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_AddRawToObject(
            object: *mut cJSON,
            name: *const core::ffi::c_char,
            raw: *const core::ffi::c_char,
        ) -> *mut cJSON {
            let raw_item: *mut cJSON = cJSON_CreateRaw(raw);
            if add_item_to_object(object, name, raw_item, &mut global_hooks, false_0) != 0 {
                return raw_item;
            }
            cJSON_Delete(raw_item);
            std::ptr::null_mut::<cJSON>()
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_AddObjectToObject(
            object: *mut cJSON,
            name: *const core::ffi::c_char,
        ) -> *mut cJSON {
            let object_item: *mut cJSON = cJSON_CreateObject();
            if add_item_to_object(object, name, object_item, &mut global_hooks, false_0) != 0 {
                return object_item;
            }
            cJSON_Delete(object_item);
            std::ptr::null_mut::<cJSON>()
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_AddArrayToObject(
            object: *mut cJSON,
            name: *const core::ffi::c_char,
        ) -> *mut cJSON {
            let array: *mut cJSON = cJSON_CreateArray();
            if add_item_to_object(object, name, array, &mut global_hooks, false_0) != 0 {
                return array;
            }
            cJSON_Delete(array);
            std::ptr::null_mut::<cJSON>()
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_DetachItemViaPointer(
            parent: *mut cJSON,
            item: *mut cJSON,
        ) -> *mut cJSON {
            if parent.is_null()
                || item.is_null()
                || item != (*parent).child && ((*item).prev).is_null()
            {
                return std::ptr::null_mut::<cJSON>();
            }
            if item != (*parent).child {
                (*(*item).prev).next = (*item).next;
            }
            if !((*item).next).is_null() {
                (*(*item).next).prev = (*item).prev;
            }
            if item == (*parent).child {
                (*parent).child = (*item).next;
            } else if ((*item).next).is_null() {
                (*(*parent).child).prev = (*item).prev;
            }
            (*item).prev = std::ptr::null_mut::<cJSON>();
            (*item).next = std::ptr::null_mut::<cJSON>();
            item
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_DetachItemFromArray(
            array: *mut cJSON,
            which: core::ffi::c_int,
        ) -> *mut cJSON {
            if which < 0 as core::ffi::c_int {
                return std::ptr::null_mut::<cJSON>();
            }
            {
                let __arg_1 = get_array_item(array, which as size_t);
                cJSON_DetachItemViaPointer(array, __arg_1)
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_DeleteItemFromArray(
            array: *mut cJSON,
            which: core::ffi::c_int,
        ) {
            cJSON_Delete(cJSON_DetachItemFromArray(array, which));
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_DetachItemFromObject(
            object: *mut cJSON,
            string: *const core::ffi::c_char,
        ) -> *mut cJSON {
            let to_detach: *mut cJSON = cJSON_GetObjectItem(object, string);
            cJSON_DetachItemViaPointer(object, to_detach)
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_DetachItemFromObjectCaseSensitive(
            object: *mut cJSON,
            string: *const core::ffi::c_char,
        ) -> *mut cJSON {
            let to_detach: *mut cJSON = cJSON_GetObjectItemCaseSensitive(object, string);
            cJSON_DetachItemViaPointer(object, to_detach)
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_DeleteItemFromObject(
            object: *mut cJSON,
            string: *const core::ffi::c_char,
        ) {
            cJSON_Delete(cJSON_DetachItemFromObject(object, string));
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_DeleteItemFromObjectCaseSensitive(
            object: *mut cJSON,
            string: *const core::ffi::c_char,
        ) {
            cJSON_Delete(cJSON_DetachItemFromObjectCaseSensitive(object, string));
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_InsertItemInArray(
            array: *mut cJSON,
            which: core::ffi::c_int,
            newitem: *mut cJSON,
        ) -> cJSON_bool {
            let mut after_inserted: *mut cJSON = std::ptr::null_mut::<cJSON>();
            if which < 0 as core::ffi::c_int || newitem.is_null() {
                return false_0;
            }
            after_inserted = get_array_item(array, which as size_t);
            if after_inserted.is_null() {
                return add_item_to_array(array, newitem);
            }
            if after_inserted != (*array).child && ((*after_inserted).prev).is_null() {
                return false_0;
            }
            (*newitem).next = after_inserted as *mut cJSON;
            (*newitem).prev = (*after_inserted).prev;
            (*after_inserted).prev = newitem as *mut cJSON;
            if after_inserted == (*array).child {
                (*array).child = newitem as *mut cJSON;
            } else {
                (*(*newitem).prev).next = newitem as *mut cJSON;
            }
            true_0
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_ReplaceItemViaPointer(
            parent: *mut cJSON,
            item: *mut cJSON,
            replacement: *mut cJSON,
        ) -> cJSON_bool {
            if parent.is_null()
                || ((*parent).child).is_null()
                || replacement.is_null()
                || item.is_null()
            {
                return false_0;
            }
            if replacement == item {
                return true_0;
            }
            (*replacement).next = (*item).next;
            (*replacement).prev = (*item).prev;
            if !((*replacement).next).is_null() {
                (*(*replacement).next).prev = replacement as *mut cJSON;
            }
            if (*parent).child == item {
                if (*(*parent).child).prev == (*parent).child {
                    (*replacement).prev = replacement as *mut cJSON;
                }
                (*parent).child = replacement as *mut cJSON;
            } else {
                if !((*replacement).prev).is_null() {
                    (*(*replacement).prev).next = replacement as *mut cJSON;
                }
                if ((*replacement).next).is_null() {
                    (*(*parent).child).prev = replacement as *mut cJSON;
                }
            }
            (*item).next = std::ptr::null_mut::<cJSON>();
            (*item).prev = std::ptr::null_mut::<cJSON>();
            cJSON_Delete(item);
            true_0
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_ReplaceItemInArray(
            array: *mut cJSON,
            which: core::ffi::c_int,
            newitem: *mut cJSON,
        ) -> cJSON_bool {
            if which < 0 as core::ffi::c_int {
                return false_0;
            }
            {
                let __arg_1 = get_array_item(array, which as size_t);
                cJSON_ReplaceItemViaPointer(array, __arg_1, newitem)
            }
        }
        unsafe extern "C" fn replace_item_in_object(
            object: *mut cJSON,
            string: *const core::ffi::c_char,
            replacement: *mut cJSON,
            case_sensitive: cJSON_bool,
        ) -> cJSON_bool {
            if replacement.is_null() || string.is_null() {
                return false_0;
            }
            if (*replacement).type_0 & cJSON_StringIsConst == 0
                && !((*replacement).string).is_null()
            {
                cJSON_free((*replacement).string as *mut core::ffi::c_void);
            }
            (*replacement).string =
                cJSON_strdup(string as *const core::ffi::c_uchar, &mut global_hooks)
                    as *mut core::ffi::c_char;
            if ((*replacement).string).is_null() {
                return false_0;
            }
            (*replacement).type_0 &= !cJSON_StringIsConst;
            {
                let __arg_1 = get_object_item(object, string, case_sensitive);
                cJSON_ReplaceItemViaPointer(object, __arg_1, replacement)
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_ReplaceItemInObject(
            object: *mut cJSON,
            string: *const core::ffi::c_char,
            newitem: *mut cJSON,
        ) -> cJSON_bool {
            replace_item_in_object(object, string, newitem, false_0)
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_ReplaceItemInObjectCaseSensitive(
            object: *mut cJSON,
            string: *const core::ffi::c_char,
            newitem: *mut cJSON,
        ) -> cJSON_bool {
            replace_item_in_object(object, string, newitem, true_0)
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_CreateNull() -> *mut cJSON {
            let item: *mut cJSON = cJSON_New_Item(&mut global_hooks);
            if !item.is_null() {
                (*item).type_0 = cJSON_NULL;
            }
            item
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_CreateTrue() -> *mut cJSON {
            let item: *mut cJSON = cJSON_New_Item(&mut global_hooks);
            if !item.is_null() {
                (*item).type_0 = cJSON_True;
            }
            item
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_CreateFalse() -> *mut cJSON {
            let item: *mut cJSON = cJSON_New_Item(&mut global_hooks);
            if !item.is_null() {
                (*item).type_0 = cJSON_False;
            }
            item
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_CreateBool(boolean: cJSON_bool) -> *mut cJSON {
            let item: *mut cJSON = cJSON_New_Item(&mut global_hooks);
            if !item.is_null() {
                (*item).type_0 = if boolean != 0 {
                    cJSON_True
                } else {
                    cJSON_False
                };
            }
            item
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_CreateNumber(num: core::ffi::c_double) -> *mut cJSON {
            let item: *mut cJSON = cJSON_New_Item(&mut global_hooks);
            if !item.is_null() {
                (*item).type_0 = cJSON_Number;
                (*item).valuedouble = num;
                if num >= INT_MAX as core::ffi::c_double {
                    (*item).valueint = INT_MAX;
                } else if num <= INT_MIN as core::ffi::c_double {
                    (*item).valueint = INT_MIN;
                } else {
                    (*item).valueint = num as core::ffi::c_int;
                }
            }
            item
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_CreateString(
            string: *const core::ffi::c_char,
        ) -> *mut cJSON {
            let item: *mut cJSON = cJSON_New_Item(&mut global_hooks);
            if !item.is_null() {
                (*item).type_0 = cJSON_String;
                (*item).valuestring =
                    cJSON_strdup(string as *const core::ffi::c_uchar, &mut global_hooks)
                        as *mut core::ffi::c_char;
                if ((*item).valuestring).is_null() {
                    cJSON_Delete(item);
                    return std::ptr::null_mut::<cJSON>();
                }
            }
            item
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_CreateStringReference(
            string: *const core::ffi::c_char,
        ) -> *mut cJSON {
            let item: *mut cJSON = cJSON_New_Item(&mut global_hooks);
            if !item.is_null() {
                (*item).type_0 = cJSON_String | cJSON_IsReference;
                (*item).valuestring =
                    cast_away_const(string as *const core::ffi::c_void) as *mut core::ffi::c_char;
            }
            item
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_CreateObjectReference(child: *const cJSON) -> *mut cJSON {
            let item: *mut cJSON = cJSON_New_Item(&mut global_hooks);
            if !item.is_null() {
                (*item).type_0 = cJSON_Object | cJSON_IsReference;
                (*item).child =
                    cast_away_const(child as *const core::ffi::c_void) as *mut cJSON as *mut cJSON;
            }
            item
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_CreateArrayReference(child: *const cJSON) -> *mut cJSON {
            let item: *mut cJSON = cJSON_New_Item(&mut global_hooks);
            if !item.is_null() {
                (*item).type_0 = cJSON_Array | cJSON_IsReference;
                (*item).child =
                    cast_away_const(child as *const core::ffi::c_void) as *mut cJSON as *mut cJSON;
            }
            item
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_CreateRaw(raw: *const core::ffi::c_char) -> *mut cJSON {
            let item: *mut cJSON = cJSON_New_Item(&mut global_hooks);
            if !item.is_null() {
                (*item).type_0 = cJSON_Raw;
                (*item).valuestring =
                    cJSON_strdup(raw as *const core::ffi::c_uchar, &mut global_hooks)
                        as *mut core::ffi::c_char;
                if ((*item).valuestring).is_null() {
                    cJSON_Delete(item);
                    return std::ptr::null_mut::<cJSON>();
                }
            }
            item
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_CreateArray() -> *mut cJSON {
            let item: *mut cJSON = cJSON_New_Item(&mut global_hooks);
            if !item.is_null() {
                (*item).type_0 = cJSON_Array;
            }
            item
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_CreateObject() -> *mut cJSON {
            let item: *mut cJSON = cJSON_New_Item(&mut global_hooks);
            if !item.is_null() {
                (*item).type_0 = cJSON_Object;
            }
            item
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_CreateIntArray(
            numbers: *const core::ffi::c_int,
            count: core::ffi::c_int,
        ) -> *mut cJSON {
            let mut i: size_t = 0 as size_t;
            let mut n: *mut cJSON = std::ptr::null_mut::<cJSON>();
            let mut p: *mut cJSON = std::ptr::null_mut::<cJSON>();
            let mut a: *mut cJSON = std::ptr::null_mut::<cJSON>();
            if count < 0 as core::ffi::c_int || numbers.is_null() {
                return std::ptr::null_mut::<cJSON>();
            }
            a = cJSON_CreateArray();
            i = 0 as size_t;
            while !a.is_null() && i < count as size_t {
                n = cJSON_CreateNumber(*numbers.add(i) as core::ffi::c_double);
                if n.is_null() {
                    cJSON_Delete(a);
                    return std::ptr::null_mut::<cJSON>();
                }
                if i == 0 {
                    (*a).child = n as *mut cJSON;
                } else {
                    suffix_object(p, n);
                }
                p = n;
                i = i.wrapping_add(1);
            }
            if !a.is_null() && !((*a).child).is_null() {
                (*(*a).child).prev = n as *mut cJSON;
            }
            a
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_CreateFloatArray(
            numbers: *const core::ffi::c_float,
            count: core::ffi::c_int,
        ) -> *mut cJSON {
            let mut i: size_t = 0 as size_t;
            let mut n: *mut cJSON = std::ptr::null_mut::<cJSON>();
            let mut p: *mut cJSON = std::ptr::null_mut::<cJSON>();
            let mut a: *mut cJSON = std::ptr::null_mut::<cJSON>();
            if count < 0 as core::ffi::c_int || numbers.is_null() {
                return std::ptr::null_mut::<cJSON>();
            }
            a = cJSON_CreateArray();
            i = 0 as size_t;
            while !a.is_null() && i < count as size_t {
                n = cJSON_CreateNumber(*numbers.add(i) as core::ffi::c_double);
                if n.is_null() {
                    cJSON_Delete(a);
                    return std::ptr::null_mut::<cJSON>();
                }
                if i == 0 {
                    (*a).child = n as *mut cJSON;
                } else {
                    suffix_object(p, n);
                }
                p = n;
                i = i.wrapping_add(1);
            }
            if !a.is_null() && !((*a).child).is_null() {
                (*(*a).child).prev = n as *mut cJSON;
            }
            a
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_CreateDoubleArray(
            numbers: *const core::ffi::c_double,
            count: core::ffi::c_int,
        ) -> *mut cJSON {
            let mut i: size_t = 0 as size_t;
            let mut n: *mut cJSON = std::ptr::null_mut::<cJSON>();
            let mut p: *mut cJSON = std::ptr::null_mut::<cJSON>();
            let mut a: *mut cJSON = std::ptr::null_mut::<cJSON>();
            if count < 0 as core::ffi::c_int || numbers.is_null() {
                return std::ptr::null_mut::<cJSON>();
            }
            a = cJSON_CreateArray();
            i = 0 as size_t;
            while !a.is_null() && i < count as size_t {
                n = cJSON_CreateNumber(*numbers.add(i));
                if n.is_null() {
                    cJSON_Delete(a);
                    return std::ptr::null_mut::<cJSON>();
                }
                if i == 0 {
                    (*a).child = n as *mut cJSON;
                } else {
                    suffix_object(p, n);
                }
                p = n;
                i = i.wrapping_add(1);
            }
            if !a.is_null() && !((*a).child).is_null() {
                (*(*a).child).prev = n as *mut cJSON;
            }
            a
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_CreateStringArray(
            strings: *const *const core::ffi::c_char,
            count: core::ffi::c_int,
        ) -> *mut cJSON {
            let mut i: size_t = 0 as size_t;
            let mut n: *mut cJSON = std::ptr::null_mut::<cJSON>();
            let mut p: *mut cJSON = std::ptr::null_mut::<cJSON>();
            let mut a: *mut cJSON = std::ptr::null_mut::<cJSON>();
            if count < 0 as core::ffi::c_int || strings.is_null() {
                return std::ptr::null_mut::<cJSON>();
            }
            a = cJSON_CreateArray();
            i = 0 as size_t;
            while !a.is_null() && i < count as size_t {
                n = cJSON_CreateString(*strings.add(i));
                if n.is_null() {
                    cJSON_Delete(a);
                    return std::ptr::null_mut::<cJSON>();
                }
                if i == 0 {
                    (*a).child = n as *mut cJSON;
                } else {
                    suffix_object(p, n);
                }
                p = n;
                i = i.wrapping_add(1);
            }
            if !a.is_null() && !((*a).child).is_null() {
                (*(*a).child).prev = n as *mut cJSON;
            }
            a
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_Duplicate(
            item: *const cJSON,
            recurse: cJSON_bool,
        ) -> *mut cJSON {
            cJSON_Duplicate_rec(item, 0 as size_t, recurse)
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_Duplicate_rec(
            item: *const cJSON,
            depth: size_t,
            recurse: cJSON_bool,
        ) -> *mut cJSON {
            let mut current_block: u64;
            let mut newitem: *mut cJSON = std::ptr::null_mut::<cJSON>();
            let mut child: *mut cJSON = std::ptr::null_mut::<cJSON>();
            let mut next: *mut cJSON = std::ptr::null_mut::<cJSON>();
            let mut newchild: *mut cJSON = std::ptr::null_mut::<cJSON>();
            if !item.is_null() {
                newitem = cJSON_New_Item(&mut global_hooks);
                if !newitem.is_null() {
                    (*newitem).type_0 = (*item).type_0 & !cJSON_IsReference;
                    (*newitem).valueint = (*item).valueint;
                    (*newitem).valuedouble = (*item).valuedouble;
                    if !((*item).valuestring).is_null() {
                        (*newitem).valuestring = cJSON_strdup(
                            (*item).valuestring as *mut core::ffi::c_uchar,
                            &mut global_hooks,
                        )
                            as *mut core::ffi::c_char;
                        if ((*newitem).valuestring).is_null() {
                            current_block = 3569157825637638140;
                        } else {
                            current_block = 11812396948646013369;
                        }
                    } else {
                        current_block = 11812396948646013369;
                    }
                    match current_block {
                        3569157825637638140 => {}
                        _ => {
                            if !((*item).string).is_null() {
                                (*newitem).string = if (*item).type_0 & cJSON_StringIsConst != 0 {
                                    (*item).string
                                } else {
                                    cJSON_strdup(
                                        (*item).string as *mut core::ffi::c_uchar,
                                        &mut global_hooks,
                                    ) as *mut core::ffi::c_char
                                };
                                if ((*newitem).string).is_null() {
                                    current_block = 3569157825637638140;
                                } else {
                                    current_block = 12800627514080957624;
                                }
                            } else {
                                current_block = 12800627514080957624;
                            }
                            match current_block {
                                3569157825637638140 => {}
                                _ => {
                                    if recurse == 0 {
                                        return newitem;
                                    }
                                    child = (*item).child as *mut cJSON;
                                    loop {
                                        if child.is_null() {
                                            current_block = 14763689060501151050;
                                            break;
                                        }
                                        if depth >= CJSON_CIRCULAR_LIMIT as size_t {
                                            current_block = 3569157825637638140;
                                            break;
                                        }
                                        newchild = cJSON_Duplicate_rec(
                                            child,
                                            depth.wrapping_add(1 as size_t),
                                            true_0,
                                        );
                                        if newchild.is_null() {
                                            current_block = 3569157825637638140;
                                            break;
                                        }
                                        if !next.is_null() {
                                            (*next).next = newchild as *mut cJSON;
                                            (*newchild).prev = next as *mut cJSON;
                                            next = newchild;
                                        } else {
                                            (*newitem).child = newchild as *mut cJSON;
                                            next = newchild;
                                        }
                                        child = (*child).next as *mut cJSON;
                                    }
                                    match current_block {
                                        3569157825637638140 => {}
                                        _ => {
                                            if !newitem.is_null() && !((*newitem).child).is_null() {
                                                (*(*newitem).child).prev = newchild as *mut cJSON;
                                            }
                                            return newitem;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            if !newitem.is_null() {
                cJSON_Delete(newitem);
            }
            std::ptr::null_mut::<cJSON>()
        }
        unsafe extern "C" fn skip_oneline_comment(input: *mut *mut core::ffi::c_char) {
            *input = (*input).add(
                ::core::mem::size_of::<[core::ffi::c_char; 3]>()
                    .wrapping_sub(::core::mem::size_of::<[core::ffi::c_char; 1]>()),
            );
            while *(*input).offset(0 as core::ffi::c_int as isize) as core::ffi::c_int
                != '\0' as i32
            {
                if *(*input).offset(0 as core::ffi::c_int as isize) as core::ffi::c_int
                    == '\n' as i32
                {
                    *input = (*input).add(
                        ::core::mem::size_of::<[core::ffi::c_char; 2]>()
                            .wrapping_sub(::core::mem::size_of::<[core::ffi::c_char; 1]>()),
                    );
                    return;
                }
                *input = (*input).offset(1);
            }
        }
        unsafe extern "C" fn skip_multiline_comment(input: *mut *mut core::ffi::c_char) {
            *input = (*input).add(
                ::core::mem::size_of::<[core::ffi::c_char; 3]>()
                    .wrapping_sub(::core::mem::size_of::<[core::ffi::c_char; 1]>()),
            );
            while *(*input).offset(0 as core::ffi::c_int as isize) as core::ffi::c_int
                != '\0' as i32
            {
                if *(*input).offset(0 as core::ffi::c_int as isize) as core::ffi::c_int
                    == '*' as i32
                    && *(*input).offset(1 as core::ffi::c_int as isize) as core::ffi::c_int
                        == '/' as i32
                {
                    *input = (*input).add(
                        ::core::mem::size_of::<[core::ffi::c_char; 3]>()
                            .wrapping_sub(::core::mem::size_of::<[core::ffi::c_char; 1]>()),
                    );
                    return;
                }
                *input = (*input).offset(1);
            }
        }
        unsafe extern "C" fn minify_string(
            input: *mut *mut core::ffi::c_char,
            output: *mut *mut core::ffi::c_char,
        ) {
            *(*output).offset(0 as core::ffi::c_int as isize) =
                *(*input).offset(0 as core::ffi::c_int as isize);
            *input = (*input).add(
                ::core::mem::size_of::<[core::ffi::c_char; 2]>()
                    .wrapping_sub(::core::mem::size_of::<[core::ffi::c_char; 1]>()),
            );
            *output = (*output).add(
                ::core::mem::size_of::<[core::ffi::c_char; 2]>()
                    .wrapping_sub(::core::mem::size_of::<[core::ffi::c_char; 1]>()),
            );
            while *(*input).offset(0 as core::ffi::c_int as isize) as core::ffi::c_int
                != '\0' as i32
            {
                *(*output).offset(0 as core::ffi::c_int as isize) =
                    *(*input).offset(0 as core::ffi::c_int as isize);
                if *(*input).offset(0 as core::ffi::c_int as isize) as core::ffi::c_int
                    == '"' as i32
                {
                    *(*output).offset(0 as core::ffi::c_int as isize) =
                        '"' as i32 as core::ffi::c_char;
                    *input = (*input).add(
                        ::core::mem::size_of::<[core::ffi::c_char; 2]>()
                            .wrapping_sub(::core::mem::size_of::<[core::ffi::c_char; 1]>()),
                    );
                    *output = (*output).add(
                        ::core::mem::size_of::<[core::ffi::c_char; 2]>()
                            .wrapping_sub(::core::mem::size_of::<[core::ffi::c_char; 1]>()),
                    );
                    return;
                } else if *(*input).offset(0 as core::ffi::c_int as isize) as core::ffi::c_int
                    == '\\' as i32
                    && *(*input).offset(1 as core::ffi::c_int as isize) as core::ffi::c_int
                        == '"' as i32
                {
                    *(*output).offset(1 as core::ffi::c_int as isize) =
                        *(*input).offset(1 as core::ffi::c_int as isize);
                    *input = (*input).add(
                        ::core::mem::size_of::<[core::ffi::c_char; 2]>()
                            .wrapping_sub(::core::mem::size_of::<[core::ffi::c_char; 1]>()),
                    );
                    *output = (*output).add(
                        ::core::mem::size_of::<[core::ffi::c_char; 2]>()
                            .wrapping_sub(::core::mem::size_of::<[core::ffi::c_char; 1]>()),
                    );
                }
                *input = (*input).offset(1);
                *output = (*output).offset(1);
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_Minify(mut json: *mut core::ffi::c_char) {
            let mut into: *mut core::ffi::c_char = json;
            if json.is_null() {
                return;
            }
            while *json.offset(0 as core::ffi::c_int as isize) as core::ffi::c_int != '\0' as i32 {
                match *json.offset(0 as core::ffi::c_int as isize) as core::ffi::c_int {
                    32 | 9 | 13 | 10 => {
                        json = json.offset(1);
                    }
                    47 => {
                        if *json.offset(1 as core::ffi::c_int as isize) as core::ffi::c_int
                            == '/' as i32
                        {
                            skip_oneline_comment(&mut json);
                        } else if *json.offset(1 as core::ffi::c_int as isize) as core::ffi::c_int
                            == '*' as i32
                        {
                            skip_multiline_comment(&mut json);
                        } else {
                            json = json.offset(1);
                        }
                    }
                    34 => {
                        minify_string(&mut json, &mut into as *mut *mut core::ffi::c_char);
                    }
                    _ => {
                        *into.offset(0 as core::ffi::c_int as isize) =
                            *json.offset(0 as core::ffi::c_int as isize);
                        json = json.offset(1);
                        into = into.offset(1);
                    }
                }
            }
            *into = '\0' as i32 as core::ffi::c_char;
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_IsInvalid(item: *const cJSON) -> cJSON_bool {
            if item.is_null() {
                return false_0;
            }
            ((*item).type_0 & 0xff as core::ffi::c_int == cJSON_Invalid) as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_IsFalse(item: *const cJSON) -> cJSON_bool {
            if item.is_null() {
                return false_0;
            }
            ((*item).type_0 & 0xff as core::ffi::c_int == cJSON_False) as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_IsTrue(item: *const cJSON) -> cJSON_bool {
            if item.is_null() {
                return false_0;
            }
            ((*item).type_0 & 0xff as core::ffi::c_int == cJSON_True) as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_IsBool(item: *const cJSON) -> cJSON_bool {
            if item.is_null() {
                return false_0;
            }
            ((*item).type_0 & (cJSON_True | cJSON_False) != 0 as core::ffi::c_int)
                as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_IsNull(item: *const cJSON) -> cJSON_bool {
            if item.is_null() {
                return false_0;
            }
            ((*item).type_0 & 0xff as core::ffi::c_int == cJSON_NULL) as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_IsNumber(item: *const cJSON) -> cJSON_bool {
            if item.is_null() {
                return false_0;
            }
            ((*item).type_0 & 0xff as core::ffi::c_int == cJSON_Number) as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_IsString(item: *const cJSON) -> cJSON_bool {
            if item.is_null() {
                return false_0;
            }
            ((*item).type_0 & 0xff as core::ffi::c_int == cJSON_String) as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_IsArray(item: *const cJSON) -> cJSON_bool {
            if item.is_null() {
                return false_0;
            }
            ((*item).type_0 & 0xff as core::ffi::c_int == cJSON_Array) as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_IsObject(item: *const cJSON) -> cJSON_bool {
            if item.is_null() {
                return false_0;
            }
            ((*item).type_0 & 0xff as core::ffi::c_int == cJSON_Object) as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_IsRaw(item: *const cJSON) -> cJSON_bool {
            if item.is_null() {
                return false_0;
            }
            ((*item).type_0 & 0xff as core::ffi::c_int == cJSON_Raw) as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_Compare(
            a: *const cJSON,
            b: *const cJSON,
            case_sensitive: cJSON_bool,
        ) -> cJSON_bool {
            if a.is_null()
                || b.is_null()
                || (*a).type_0 & 0xff as core::ffi::c_int != (*b).type_0 & 0xff as core::ffi::c_int
            {
                return false_0;
            }
            match (*a).type_0 & 0xff as core::ffi::c_int {
                cJSON_False | cJSON_True | cJSON_NULL | cJSON_Number | cJSON_String | cJSON_Raw
                | cJSON_Array | cJSON_Object => {}
                _ => return false_0,
            }
            if a == b {
                return true_0;
            }
            match (*a).type_0 & 0xff as core::ffi::c_int {
                cJSON_False | cJSON_True | cJSON_NULL => true_0,
                cJSON_Number => {
                    if compare_double((*a).valuedouble, (*b).valuedouble) != 0 {
                        return true_0;
                    }
                    false_0
                }
                cJSON_String | cJSON_Raw => {
                    if ((*a).valuestring).is_null() || ((*b).valuestring).is_null() {
                        return false_0;
                    }
                    if strcmp((*a).valuestring, (*b).valuestring) == 0 as core::ffi::c_int {
                        return true_0;
                    }
                    false_0
                }
                cJSON_Array => {
                    let mut a_element: *mut cJSON = (*a).child as *mut cJSON;
                    let mut b_element: *mut cJSON = (*b).child as *mut cJSON;
                    while !a_element.is_null() && !b_element.is_null() {
                        if cJSON_Compare(a_element, b_element, case_sensitive) == 0 {
                            return false_0;
                        }
                        a_element = (*a_element).next as *mut cJSON;
                        b_element = (*b_element).next as *mut cJSON;
                    }
                    if a_element != b_element {
                        return false_0;
                    }
                    true_0
                }
                cJSON_Object => {
                    let mut a_element_0: *mut cJSON = std::ptr::null_mut::<cJSON>();
                    let mut b_element_0: *mut cJSON = std::ptr::null_mut::<cJSON>();
                    a_element_0 = (if !a.is_null() {
                        (*a).child
                    } else {
                        std::ptr::null_mut::<cJSON>()
                    }) as *mut cJSON;
                    while !a_element_0.is_null() {
                        b_element_0 = get_object_item(b, (*a_element_0).string, case_sensitive);
                        if b_element_0.is_null() {
                            return false_0;
                        }
                        if cJSON_Compare(a_element_0, b_element_0, case_sensitive) == 0 {
                            return false_0;
                        }
                        a_element_0 = (*a_element_0).next as *mut cJSON;
                    }
                    b_element_0 = (if !b.is_null() {
                        (*b).child
                    } else {
                        std::ptr::null_mut::<cJSON>()
                    }) as *mut cJSON;
                    while !b_element_0.is_null() {
                        a_element_0 = get_object_item(a, (*b_element_0).string, case_sensitive);
                        if a_element_0.is_null() {
                            return false_0;
                        }
                        if cJSON_Compare(b_element_0, a_element_0, case_sensitive) == 0 {
                            return false_0;
                        }
                        b_element_0 = (*b_element_0).next as *mut cJSON;
                    }
                    true_0
                }
                _ => false_0,
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_malloc(size: size_t) -> *mut core::ffi::c_void {
            (global_hooks.allocate).expect("non-null function pointer")(size)
        }
        #[no_mangle]
        pub unsafe extern "C" fn cJSON_free(mut object: *mut core::ffi::c_void) {
            (global_hooks.deallocate).expect("non-null function pointer")(object);
            object = NULL;
        }
        pub const INT_MAX: core::ffi::c_int = __INT_MAX__;
        pub const INT_MIN: core::ffi::c_int = -__INT_MAX__ - 1 as core::ffi::c_int;
        pub const __DBL_EPSILON__: core::ffi::c_double = 2.220_446_049_250_313e-16_f64;
        pub const DBL_EPSILON: core::ffi::c_double = __DBL_EPSILON__;
    }
    pub mod test {
        use crate::src::cJSON::cJSON;
        use crate::src::cJSON::cJSON_AddFalseToObject;
        use crate::src::cJSON::cJSON_AddItemToArray;
        use crate::src::cJSON::cJSON_AddItemToObject;
        use crate::src::cJSON::cJSON_AddNumberToObject;
        use crate::src::cJSON::cJSON_AddStringToObject;
        use crate::src::cJSON::cJSON_CreateArray;
        use crate::src::cJSON::cJSON_CreateIntArray;
        use crate::src::cJSON::cJSON_CreateObject;
        use crate::src::cJSON::cJSON_CreateString;
        use crate::src::cJSON::cJSON_CreateStringArray;
        use crate::src::cJSON::cJSON_Delete;
        use crate::src::cJSON::cJSON_Print;
        use crate::src::cJSON::cJSON_PrintPreallocated;
        use crate::src::cJSON::cJSON_Version;
        use crate::src::cJSON::cJSON_bool;
        use crate::src::cJSON::size_t;
        extern "C" {
            fn printf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
            fn malloc(__size: size_t) -> *mut core::ffi::c_void;
            fn free(__ptr: *mut core::ffi::c_void);
            fn exit(__status: core::ffi::c_int) -> !;
            fn strcmp(
                __s1: *const core::ffi::c_char,
                __s2: *const core::ffi::c_char,
            ) -> core::ffi::c_int;
            fn strlen(__s: *const core::ffi::c_char) -> size_t;
        }
        #[repr(C)]
        pub struct record {
            pub precision: *const core::ffi::c_char,
            pub lat: core::ffi::c_double,
            pub lon: core::ffi::c_double,
            pub address: *const core::ffi::c_char,
            pub city: *const core::ffi::c_char,
            pub state: *const core::ffi::c_char,
            pub zip: *const core::ffi::c_char,
            pub country: *const core::ffi::c_char,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for record {}
        #[automatically_derived]
        impl ::core::clone::Clone for record {
            #[inline]
            fn clone(&self) -> record {
                let _: ::core::clone::AssertParamIsClone<*const core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_double>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_double>;
                let _: ::core::clone::AssertParamIsClone<*const core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*const core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*const core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*const core::ffi::c_char>;
                let _: ::core::clone::AssertParamIsClone<*const core::ffi::c_char>;
                *self
            }
        }
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const EXIT_FAILURE: core::ffi::c_int = 1 as core::ffi::c_int;
        unsafe extern "C" fn print_preallocated(root: *mut cJSON) -> core::ffi::c_int {
            let mut out: *mut core::ffi::c_char = std::ptr::null_mut::<core::ffi::c_char>();
            let mut buf: *mut core::ffi::c_char = std::ptr::null_mut::<core::ffi::c_char>();
            let mut buf_fail: *mut core::ffi::c_char = std::ptr::null_mut::<core::ffi::c_char>();
            let mut len: size_t = 0 as size_t;
            let mut len_fail: size_t = 0 as size_t;
            out = cJSON_Print(root);
            len = (strlen(out)).wrapping_add(5 as size_t);
            buf = malloc(len) as *mut core::ffi::c_char;
            if buf.is_null() {
                printf(b"Failed to allocate memory.\n\0" as *const u8 as *const core::ffi::c_char);
                exit(1 as core::ffi::c_int);
            }
            len_fail = strlen(out);
            buf_fail = malloc(len_fail) as *mut core::ffi::c_char;
            if buf_fail.is_null() {
                printf(b"Failed to allocate memory.\n\0" as *const u8 as *const core::ffi::c_char);
                exit(1 as core::ffi::c_int);
            }
            if cJSON_PrintPreallocated(root, buf, len as core::ffi::c_int, 1 as cJSON_bool) == 0 {
                printf(
                    b"cJSON_PrintPreallocated failed!\n\0" as *const u8 as *const core::ffi::c_char,
                );
                if strcmp(out, buf) != 0 as core::ffi::c_int {
                    printf(
                        b"cJSON_PrintPreallocated not the same as cJSON_Print!\n\0" as *const u8
                            as *const core::ffi::c_char,
                    );
                    printf(
                        b"cJSON_Print result:\n%s\n\0" as *const u8 as *const core::ffi::c_char,
                        out,
                    );
                    printf(
                        b"cJSON_PrintPreallocated result:\n%s\n\0" as *const u8
                            as *const core::ffi::c_char,
                        buf,
                    );
                }
                free(out as *mut core::ffi::c_void);
                free(buf_fail as *mut core::ffi::c_void);
                free(buf as *mut core::ffi::c_void);
                return -(1 as core::ffi::c_int);
            }
            printf(b"%s\n\0" as *const u8 as *const core::ffi::c_char, buf);
            if cJSON_PrintPreallocated(
                root,
                buf_fail,
                len_fail as core::ffi::c_int,
                1 as cJSON_bool,
            ) != 0
            {
                printf(
                    b"cJSON_PrintPreallocated failed to show error with insufficient memory!\n\0"
                        as *const u8 as *const core::ffi::c_char,
                );
                printf(
                    b"cJSON_Print result:\n%s\n\0" as *const u8 as *const core::ffi::c_char,
                    out,
                );
                printf(
                    b"cJSON_PrintPreallocated result:\n%s\n\0" as *const u8
                        as *const core::ffi::c_char,
                    buf_fail,
                );
                free(out as *mut core::ffi::c_void);
                free(buf_fail as *mut core::ffi::c_void);
                free(buf as *mut core::ffi::c_void);
                return -(1 as core::ffi::c_int);
            }
            free(out as *mut core::ffi::c_void);
            free(buf_fail as *mut core::ffi::c_void);
            free(buf as *mut core::ffi::c_void);
            0 as core::ffi::c_int
        }
        unsafe extern "C" fn create_objects(
            strings: *mut *const core::ffi::c_char,
            numbers: *mut [core::ffi::c_int; 3],
            ids: *mut core::ffi::c_int,
            fields: *mut record,
        ) {
            let mut root: *mut cJSON = std::ptr::null_mut::<cJSON>();
            let mut fmt: *mut cJSON = std::ptr::null_mut::<cJSON>();
            let mut img: *mut cJSON = std::ptr::null_mut::<cJSON>();
            let mut thm: *mut cJSON = std::ptr::null_mut::<cJSON>();
            let mut fld: *mut cJSON = std::ptr::null_mut::<cJSON>();
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            let zero: core::ffi::c_double = 0.0f64;
            root = cJSON_CreateObject();
            cJSON_AddItemToObject(
                root,
                b"name\0" as *const u8 as *const core::ffi::c_char,
                cJSON_CreateString(
                    b"Jack (\"Bee\") Nimble\0" as *const u8 as *const core::ffi::c_char,
                ),
            );
            fmt = cJSON_CreateObject();
            cJSON_AddItemToObject(
                root,
                b"format\0" as *const u8 as *const core::ffi::c_char,
                fmt,
            );
            cJSON_AddStringToObject(
                fmt,
                b"type\0" as *const u8 as *const core::ffi::c_char,
                b"rect\0" as *const u8 as *const core::ffi::c_char,
            );
            cJSON_AddNumberToObject(
                fmt,
                b"width\0" as *const u8 as *const core::ffi::c_char,
                1920 as core::ffi::c_int as core::ffi::c_double,
            );
            cJSON_AddNumberToObject(
                fmt,
                b"height\0" as *const u8 as *const core::ffi::c_char,
                1080 as core::ffi::c_int as core::ffi::c_double,
            );
            cJSON_AddFalseToObject(fmt, b"interlace\0" as *const u8 as *const core::ffi::c_char);
            cJSON_AddNumberToObject(
                fmt,
                b"frame rate\0" as *const u8 as *const core::ffi::c_char,
                24 as core::ffi::c_int as core::ffi::c_double,
            );
            if print_preallocated(root) != 0 as core::ffi::c_int {
                cJSON_Delete(root);
                exit(EXIT_FAILURE);
            }
            cJSON_Delete(root);
            root = cJSON_CreateStringArray(
                strings as *const *const core::ffi::c_char,
                7 as core::ffi::c_int,
            );
            if print_preallocated(root) != 0 as core::ffi::c_int {
                cJSON_Delete(root);
                exit(EXIT_FAILURE);
            }
            cJSON_Delete(root);
            root = cJSON_CreateArray();
            i = 0 as core::ffi::c_int;
            while i < 3 as core::ffi::c_int {
                cJSON_AddItemToArray(
                    root,
                    cJSON_CreateIntArray(
                        (*numbers.offset(i as isize)).as_ptr(),
                        3 as core::ffi::c_int,
                    ),
                );
                i += 1;
            }
            if print_preallocated(root) != 0 as core::ffi::c_int {
                cJSON_Delete(root);
                exit(EXIT_FAILURE);
            }
            cJSON_Delete(root);
            root = cJSON_CreateObject();
            img = cJSON_CreateObject();
            cJSON_AddItemToObject(
                root,
                b"Image\0" as *const u8 as *const core::ffi::c_char,
                img,
            );
            cJSON_AddNumberToObject(
                img,
                b"Width\0" as *const u8 as *const core::ffi::c_char,
                800 as core::ffi::c_int as core::ffi::c_double,
            );
            cJSON_AddNumberToObject(
                img,
                b"Height\0" as *const u8 as *const core::ffi::c_char,
                600 as core::ffi::c_int as core::ffi::c_double,
            );
            cJSON_AddStringToObject(
                img,
                b"Title\0" as *const u8 as *const core::ffi::c_char,
                b"View from 15th Floor\0" as *const u8 as *const core::ffi::c_char,
            );
            thm = cJSON_CreateObject();
            cJSON_AddItemToObject(
                img,
                b"Thumbnail\0" as *const u8 as *const core::ffi::c_char,
                thm,
            );
            cJSON_AddStringToObject(
                thm,
                b"Url\0" as *const u8 as *const core::ffi::c_char,
                b"http:/*www.example.com/image/481989943\0" as *const u8
                    as *const core::ffi::c_char,
            );
            cJSON_AddNumberToObject(
                thm,
                b"Height\0" as *const u8 as *const core::ffi::c_char,
                125 as core::ffi::c_int as core::ffi::c_double,
            );
            cJSON_AddStringToObject(
                thm,
                b"Width\0" as *const u8 as *const core::ffi::c_char,
                b"100\0" as *const u8 as *const core::ffi::c_char,
            );
            cJSON_AddItemToObject(
                img,
                b"IDs\0" as *const u8 as *const core::ffi::c_char,
                cJSON_CreateIntArray(ids as *const core::ffi::c_int, 4 as core::ffi::c_int),
            );
            if print_preallocated(root) != 0 as core::ffi::c_int {
                cJSON_Delete(root);
                exit(EXIT_FAILURE);
            }
            cJSON_Delete(root);
            root = cJSON_CreateArray();
            i = 0 as core::ffi::c_int;
            while i < 2 as core::ffi::c_int {
                fld = cJSON_CreateObject();
                cJSON_AddItemToArray(root, fld);
                cJSON_AddStringToObject(
                    fld,
                    b"precision\0" as *const u8 as *const core::ffi::c_char,
                    (*fields.offset(i as isize)).precision,
                );
                cJSON_AddNumberToObject(
                    fld,
                    b"Latitude\0" as *const u8 as *const core::ffi::c_char,
                    (*fields.offset(i as isize)).lat,
                );
                cJSON_AddNumberToObject(
                    fld,
                    b"Longitude\0" as *const u8 as *const core::ffi::c_char,
                    (*fields.offset(i as isize)).lon,
                );
                cJSON_AddStringToObject(
                    fld,
                    b"Address\0" as *const u8 as *const core::ffi::c_char,
                    (*fields.offset(i as isize)).address,
                );
                cJSON_AddStringToObject(
                    fld,
                    b"City\0" as *const u8 as *const core::ffi::c_char,
                    (*fields.offset(i as isize)).city,
                );
                cJSON_AddStringToObject(
                    fld,
                    b"State\0" as *const u8 as *const core::ffi::c_char,
                    (*fields.offset(i as isize)).state,
                );
                cJSON_AddStringToObject(
                    fld,
                    b"Zip\0" as *const u8 as *const core::ffi::c_char,
                    (*fields.offset(i as isize)).zip,
                );
                cJSON_AddStringToObject(
                    fld,
                    b"Country\0" as *const u8 as *const core::ffi::c_char,
                    (*fields.offset(i as isize)).country,
                );
                i += 1;
            }
            if print_preallocated(root) != 0 as core::ffi::c_int {
                cJSON_Delete(root);
                exit(EXIT_FAILURE);
            }
            cJSON_Delete(root);
            root = cJSON_CreateObject();
            cJSON_AddNumberToObject(
                root,
                b"number\0" as *const u8 as *const core::ffi::c_char,
                1.0f64 / zero,
            );
            if print_preallocated(root) != 0 as core::ffi::c_int {
                cJSON_Delete(root);
                exit(EXIT_FAILURE);
            }
            cJSON_Delete(root);
        }
        #[no_mangle]
        pub unsafe extern "C" fn driver(
            strings: *mut *const core::ffi::c_char,
            numbers: *mut [core::ffi::c_int; 3],
            ids: *mut core::ffi::c_int,
            fields: *mut record,
        ) -> core::ffi::c_int {
            printf(
                b"Version: %s\n\0" as *const u8 as *const core::ffi::c_char,
                cJSON_Version(),
            );
            create_objects(strings, numbers, ids, fields);
            0 as core::ffi::c_int
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case("cJSON_lib", SOURCE);
}
