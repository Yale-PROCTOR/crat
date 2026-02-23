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
    pub mod analyzer {
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
            fn memset(
                __s: *mut core::ffi::c_void,
                __c: core::ffi::c_int,
                __n: size_t,
            ) -> *mut core::ffi::c_void;
            fn strcpy(
                __dest: *mut core::ffi::c_char,
                __src: *const core::ffi::c_char,
            ) -> *mut core::ffi::c_char;
            fn strncpy(
                __dest: *mut core::ffi::c_char,
                __src: *const core::ffi::c_char,
                __n: size_t,
            ) -> *mut core::ffi::c_char;
            fn strcmp(
                __s1: *const core::ffi::c_char,
                __s2: *const core::ffi::c_char,
            ) -> core::ffi::c_int;
            fn strstr(
                __haystack: *const core::ffi::c_char,
                __needle: *const core::ffi::c_char,
            ) -> *mut core::ffi::c_char;
        }
        pub type size_t = usize;
        pub type token_type_t = core::ffi::c_uint;
        pub const TOKEN_ERROR: token_type_t = 11;
        pub const TOKEN_COMMENT: token_type_t = 10;
        pub const TOKEN_STRING: token_type_t = 9;
        pub const TOKEN_OPERATOR: token_type_t = 8;
        pub const TOKEN_KEYWORD: token_type_t = 7;
        pub const TOKEN_IDENTIFIER: token_type_t = 6;
        pub const TOKEN_NEWLINE: token_type_t = 5;
        pub const TOKEN_WHITESPACE: token_type_t = 4;
        pub const TOKEN_PUNCTUATION: token_type_t = 3;
        pub const TOKEN_NUMBER: token_type_t = 2;
        pub const TOKEN_WORD: token_type_t = 1;
        pub const TOKEN_EOF: token_type_t = 0;
        #[repr(C)]
        pub struct token_t {
            pub type_0: token_type_t,
            pub value: [core::ffi::c_char; 256],
            pub length: size_t,
            pub line: core::ffi::c_int,
            pub column: core::ffi::c_int,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for token_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for token_t {
            #[inline]
            fn clone(&self) -> token_t {
                let _: ::core::clone::AssertParamIsClone<token_type_t>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 256]>;
                let _: ::core::clone::AssertParamIsClone<size_t>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                *self
            }
        }
        pub type tokenizer_next_fn = Option<unsafe extern "C" fn() -> token_t>;
        pub type tokenizer_peek_fn = Option<unsafe extern "C" fn() -> token_t>;
        pub type tokenizer_reset_fn = Option<unsafe extern "C" fn() -> ()>;
        pub type tokenizer_load_fn =
            Option<unsafe extern "C" fn(*const core::ffi::c_char) -> core::ffi::c_int>;
        pub type tokenizer_get_stats_fn =
            Option<unsafe extern "C" fn(*mut size_t, *mut size_t, *mut size_t) -> ()>;
        #[repr(C)]
        pub struct tokenizer_ops_t {
            pub next_token: tokenizer_next_fn,
            pub peek_token: tokenizer_peek_fn,
            pub reset: tokenizer_reset_fn,
            pub load_text: tokenizer_load_fn,
            pub get_stats: tokenizer_get_stats_fn,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for tokenizer_ops_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for tokenizer_ops_t {
            #[inline]
            fn clone(&self) -> tokenizer_ops_t {
                let _: ::core::clone::AssertParamIsClone<tokenizer_next_fn>;
                let _: ::core::clone::AssertParamIsClone<tokenizer_peek_fn>;
                let _: ::core::clone::AssertParamIsClone<tokenizer_reset_fn>;
                let _: ::core::clone::AssertParamIsClone<tokenizer_load_fn>;
                let _: ::core::clone::AssertParamIsClone<tokenizer_get_stats_fn>;
                *self
            }
        }
        #[repr(C)]
        pub struct analysis_result_t {
            pub word_count: size_t,
            pub number_count: size_t,
            pub keyword_count: size_t,
            pub operator_count: size_t,
            pub comment_count: size_t,
            pub string_count: size_t,
            pub line_count: size_t,
            pub char_count: size_t,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for analysis_result_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for analysis_result_t {
            #[inline]
            fn clone(&self) -> analysis_result_t {
                let _: ::core::clone::AssertParamIsClone<size_t>;
                *self
            }
        }
        pub type FILE = _IO_FILE;
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
        pub type __off64_t = core::ffi::c_long;
        pub type _IO_lock_t = ();
        pub type __off_t = core::ffi::c_long;
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const MAX_TOKEN_LENGTH: core::ffi::c_int = 256 as core::ffi::c_int;
        static mut tokenizer_ops: tokenizer_ops_t = tokenizer_ops_t {
            next_token: None,
            peek_token: None,
            reset: None,
            load_text: None,
            get_stats: None,
        };
        static mut initialized: core::ffi::c_int = 0 as core::ffi::c_int;
        static mut token_type_counts: [core::ffi::c_int; 20] = [0; 20];
        static mut common_words: [[core::ffi::c_char; 256]; 100] = [[0; 256]; 100];
        static mut common_word_counts: [core::ffi::c_int; 100] = [0; 100];
        static mut num_common_words: core::ffi::c_int = 0 as core::ffi::c_int;
        #[no_mangle]
        pub unsafe extern "C" fn analyzer_init(ops: tokenizer_ops_t) {
            tokenizer_ops = ops;
            initialized = 1 as core::ffi::c_int;
            memset(
                token_type_counts.as_mut_ptr() as *mut core::ffi::c_void,
                0 as core::ffi::c_int,
                ::core::mem::size_of::<[core::ffi::c_int; 20]>() as size_t,
            );
            memset(
                common_word_counts.as_mut_ptr() as *mut core::ffi::c_void,
                0 as core::ffi::c_int,
                ::core::mem::size_of::<[core::ffi::c_int; 100]>() as size_t,
            );
            num_common_words = 0 as core::ffi::c_int;
        }
        unsafe extern "C" fn track_word(word: *const core::ffi::c_char) {
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < num_common_words {
                if strcmp((common_words[i as usize]).as_ptr(), word) == 0 as core::ffi::c_int {
                    common_word_counts[i as usize] += 1;
                    return;
                }
                i += 1;
            }
            if num_common_words < 100 as core::ffi::c_int {
                strncpy(
                    (common_words[num_common_words as usize]).as_mut_ptr(),
                    word,
                    (MAX_TOKEN_LENGTH - 1 as core::ffi::c_int) as size_t,
                );
                common_words[num_common_words as usize]
                    [(MAX_TOKEN_LENGTH - 1 as core::ffi::c_int) as usize] =
                    '\0' as i32 as core::ffi::c_char;
                common_word_counts[num_common_words as usize] = 1 as core::ffi::c_int;
                num_common_words += 1;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn analyze_text(text: *const core::ffi::c_char) -> analysis_result_t {
            let mut result: analysis_result_t = {
                analysis_result_t {
                    word_count: 0 as size_t,
                    number_count: 0,
                    keyword_count: 0,
                    operator_count: 0,
                    comment_count: 0,
                    string_count: 0,
                    line_count: 0,
                    char_count: 0,
                }
            };
            if initialized == 0 {
                fprintf(
                    stderr,
                    b"Error: Analyzer not initialized\n\0" as *const u8 as *const core::ffi::c_char,
                );
                return result;
            }
            if (tokenizer_ops.load_text).expect("non-null function pointer")(text)
                != 0 as core::ffi::c_int
            {
                fprintf(
                    stderr,
                    b"Error: Failed to load text\n\0" as *const u8 as *const core::ffi::c_char,
                );
                return result;
            }
            let mut token: token_t = token_t {
                type_0: TOKEN_EOF,
                value: [0; 256],
                length: 0,
                line: 0,
                column: 0,
            };
            loop {
                token = (tokenizer_ops.next_token).expect("non-null function pointer")();
                if token.type_0 as core::ffi::c_uint
                    == TOKEN_EOF as core::ffi::c_int as core::ffi::c_uint
                {
                    break;
                }
                token_type_counts[token.type_0 as usize] += 1;
                match token.type_0 as core::ffi::c_uint {
                    1 | 6 => {
                        result.word_count = (result.word_count).wrapping_add(1);
                        track_word((token.value).as_ptr());
                    }
                    2 => {
                        result.number_count = (result.number_count).wrapping_add(1);
                    }
                    7 => {
                        result.keyword_count = (result.keyword_count).wrapping_add(1);
                    }
                    8 => {
                        result.operator_count = (result.operator_count).wrapping_add(1);
                    }
                    10 => {
                        result.comment_count = (result.comment_count).wrapping_add(1);
                    }
                    9 => {
                        result.string_count = (result.string_count).wrapping_add(1);
                    }
                    5 => {
                        result.line_count = (result.line_count).wrapping_add(1);
                    }
                    _ => {}
                }
            }
            let mut lines: size_t = 0;
            let mut tokens: size_t = 0;
            let mut chars: size_t = 0;
            (tokenizer_ops.get_stats).expect("non-null function pointer")(
                &mut lines,
                &mut tokens,
                &mut chars,
            );
            result.line_count = lines;
            result.char_count = chars;
            result
        }
        #[no_mangle]
        pub unsafe extern "C" fn print_token_distribution() {
            printf(b"\n=== Token Distribution ===\n\0" as *const u8 as *const core::ffi::c_char);
            let token_names: [*const core::ffi::c_char; 12] = [
                b"EOF\0" as *const u8 as *const core::ffi::c_char,
                b"WORD\0" as *const u8 as *const core::ffi::c_char,
                b"NUMBER\0" as *const u8 as *const core::ffi::c_char,
                b"PUNCTUATION\0" as *const u8 as *const core::ffi::c_char,
                b"WHITESPACE\0" as *const u8 as *const core::ffi::c_char,
                b"NEWLINE\0" as *const u8 as *const core::ffi::c_char,
                b"IDENTIFIER\0" as *const u8 as *const core::ffi::c_char,
                b"KEYWORD\0" as *const u8 as *const core::ffi::c_char,
                b"OPERATOR\0" as *const u8 as *const core::ffi::c_char,
                b"STRING\0" as *const u8 as *const core::ffi::c_char,
                b"COMMENT\0" as *const u8 as *const core::ffi::c_char,
                b"ERROR\0" as *const u8 as *const core::ffi::c_char,
            ];
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < 12 as core::ffi::c_int {
                if token_type_counts[i as usize] > 0 as core::ffi::c_int {
                    printf(
                        b"%s: %d\n\0" as *const u8 as *const core::ffi::c_char,
                        token_names[i as usize],
                        token_type_counts[i as usize],
                    );
                }
                i += 1;
            }
            printf(b"\n=== Most Common Words ===\n\0" as *const u8 as *const core::ffi::c_char);
            let mut i_0: core::ffi::c_int = 0 as core::ffi::c_int;
            while i_0 < num_common_words - 1 as core::ffi::c_int {
                let mut j: core::ffi::c_int = 0 as core::ffi::c_int;
                while j < num_common_words - i_0 - 1 as core::ffi::c_int {
                    if common_word_counts[j as usize]
                        < common_word_counts[(j + 1 as core::ffi::c_int) as usize]
                    {
                        common_word_counts.swap(j as usize, (j + 1 as core::ffi::c_int) as usize);
                        let mut temp_word: [core::ffi::c_char; 256] = [0; 256];
                        strcpy(temp_word.as_mut_ptr(), (common_words[j as usize]).as_ptr());
                        strcpy(
                            (common_words[j as usize]).as_mut_ptr(),
                            (common_words[(j + 1 as core::ffi::c_int) as usize]).as_ptr(),
                        );
                        strcpy(
                            (common_words[(j + 1 as core::ffi::c_int) as usize]).as_mut_ptr(),
                            temp_word.as_ptr(),
                        );
                    }
                    j += 1;
                }
                i_0 += 1;
            }
            let limit: core::ffi::c_int = if num_common_words < 10 as core::ffi::c_int {
                num_common_words
            } else {
                10 as core::ffi::c_int
            };
            let mut i_1: core::ffi::c_int = 0 as core::ffi::c_int;
            while i_1 < limit {
                printf(
                    b"%d. %s: %d times\n\0" as *const u8 as *const core::ffi::c_char,
                    i_1 + 1 as core::ffi::c_int,
                    (common_words[i_1 as usize]).as_ptr(),
                    common_word_counts[i_1 as usize],
                );
                i_1 += 1;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn calculate_complexity_score() -> core::ffi::c_int {
            let mut score: core::ffi::c_int = 0 as core::ffi::c_int;
            score += token_type_counts[TOKEN_KEYWORD as core::ffi::c_int as usize]
                * 2 as core::ffi::c_int;
            score += token_type_counts[TOKEN_OPERATOR as core::ffi::c_int as usize];
            score += token_type_counts[TOKEN_PUNCTUATION as core::ffi::c_int as usize]
                / 10 as core::ffi::c_int;
            score -= token_type_counts[TOKEN_COMMENT as core::ffi::c_int as usize];
            if score < 0 as core::ffi::c_int {
                score = 0 as core::ffi::c_int;
            }
            score
        }
        #[no_mangle]
        pub unsafe extern "C" fn find_patterns(pattern: *const core::ffi::c_char) {
            if initialized == 0 || pattern.is_null() {
                return;
            }
            printf(
                b"\n=== Searching for pattern: '%s' ===\n\0" as *const u8
                    as *const core::ffi::c_char,
                pattern,
            );
            (tokenizer_ops.reset).expect("non-null function pointer")();
            let mut count: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut token: token_t = token_t {
                type_0: TOKEN_EOF,
                value: [0; 256],
                length: 0,
                line: 0,
                column: 0,
            };
            loop {
                token = (tokenizer_ops.next_token).expect("non-null function pointer")();
                if token.type_0 as core::ffi::c_uint
                    == TOKEN_EOF as core::ffi::c_int as core::ffi::c_uint
                {
                    break;
                }
                if !(strstr((token.value).as_ptr(), pattern)).is_null() {
                    printf(
                        b"Line %d, Column %d: %s\n\0" as *const u8 as *const core::ffi::c_char,
                        token.line,
                        token.column,
                        (token.value).as_ptr(),
                    );
                    count += 1;
                }
            }
            printf(
                b"Found %d occurrences\n\0" as *const u8 as *const core::ffi::c_char,
                count,
            );
        }
    }
    pub mod main {
        use crate::src::analyzer::analysis_result_t;
        use crate::src::analyzer::analyze_text;
        use crate::src::analyzer::analyzer_init;
        use crate::src::analyzer::calculate_complexity_score;
        use crate::src::analyzer::find_patterns;
        use crate::src::analyzer::print_token_distribution;
        use crate::src::analyzer::size_t;
        use crate::src::analyzer::token_t;
        use crate::src::analyzer::token_type_t;
        use crate::src::analyzer::tokenizer_ops_t;
        use crate::src::analyzer::FILE;
        use crate::src::tokenizer::get_tokenizer_ops;
        extern "C" {
            static mut stdin: *mut FILE;
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
            fn printf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
            fn sscanf(
                __s: *const core::ffi::c_char,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn fgets(
                __s: *mut core::ffi::c_char,
                __n: core::ffi::c_int,
                __stream: *mut FILE,
            ) -> *mut core::ffi::c_char;
            fn fread(
                __ptr: *mut core::ffi::c_void,
                __size: size_t,
                __n: size_t,
                __stream: *mut FILE,
            ) -> core::ffi::c_ulong;
            fn fseek(
                __stream: *mut FILE,
                __off: core::ffi::c_long,
                __whence: core::ffi::c_int,
            ) -> core::ffi::c_int;
            fn ftell(__stream: *mut FILE) -> core::ffi::c_long;
            fn malloc(__size: size_t) -> *mut core::ffi::c_void;
            fn free(__ptr: *mut core::ffi::c_void);
            fn strncat(
                __dest: *mut core::ffi::c_char,
                __src: *const core::ffi::c_char,
                __n: size_t,
            ) -> *mut core::ffi::c_char;
            fn strcspn(
                __s: *const core::ffi::c_char,
                __reject: *const core::ffi::c_char,
            ) -> core::ffi::c_ulong;
            fn strlen(__s: *const core::ffi::c_char) -> size_t;
        }
        pub const TOKEN_ERROR: token_type_t = 11;
        pub const TOKEN_COMMENT: token_type_t = 10;
        pub const TOKEN_STRING: token_type_t = 9;
        pub const TOKEN_OPERATOR: token_type_t = 8;
        pub const TOKEN_KEYWORD: token_type_t = 7;
        pub const TOKEN_IDENTIFIER: token_type_t = 6;
        pub const TOKEN_NEWLINE: token_type_t = 5;
        pub const TOKEN_WHITESPACE: token_type_t = 4;
        pub const TOKEN_PUNCTUATION: token_type_t = 3;
        pub const TOKEN_NUMBER: token_type_t = 2;
        pub const TOKEN_WORD: token_type_t = 1;
        pub const TOKEN_EOF: token_type_t = 0;
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const SEEK_SET: core::ffi::c_int = 0 as core::ffi::c_int;
        pub const SEEK_END: core::ffi::c_int = 2 as core::ffi::c_int;
        pub const MAX_BUFFER_SIZE: core::ffi::c_int = 8192 as core::ffi::c_int;
        pub const MAX_INPUT_SIZE: core::ffi::c_int = 4096 as core::ffi::c_int;
        #[no_mangle]
        pub unsafe extern "C" fn print_menu() {
            printf(b"\n=== Text Analyzer ===\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"1. Analyze text\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"2. Load text from file\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"3. Show token distribution\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"4. Calculate complexity score\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"5. Find pattern\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"6. Interactive tokenizer\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"7. Exit\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"Choice: \0" as *const u8 as *const core::ffi::c_char);
        }
        #[no_mangle]
        pub unsafe extern "C" fn print_analysis_result(result: analysis_result_t) {
            printf(b"\n=== Analysis Results ===\n\0" as *const u8 as *const core::ffi::c_char);
            printf(
                b"Words/Identifiers: %zu\n\0" as *const u8 as *const core::ffi::c_char,
                result.word_count,
            );
            printf(
                b"Numbers: %zu\n\0" as *const u8 as *const core::ffi::c_char,
                result.number_count,
            );
            printf(
                b"Keywords: %zu\n\0" as *const u8 as *const core::ffi::c_char,
                result.keyword_count,
            );
            printf(
                b"Operators: %zu\n\0" as *const u8 as *const core::ffi::c_char,
                result.operator_count,
            );
            printf(
                b"Comments: %zu\n\0" as *const u8 as *const core::ffi::c_char,
                result.comment_count,
            );
            printf(
                b"Strings: %zu\n\0" as *const u8 as *const core::ffi::c_char,
                result.string_count,
            );
            printf(
                b"Lines: %zu\n\0" as *const u8 as *const core::ffi::c_char,
                result.line_count,
            );
            printf(
                b"Characters: %zu\n\0" as *const u8 as *const core::ffi::c_char,
                result.char_count,
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn interactive_tokenizer(ops: tokenizer_ops_t) {
            printf(
                b"\nEnter text (empty line to stop):\n\0" as *const u8 as *const core::ffi::c_char,
            );
            let mut input: [core::ffi::c_char; 4096] = [b'\0' as i8; 4096];
            let mut line: [core::ffi::c_char; 256] = [0; 256];
            while !(fgets(
                line.as_mut_ptr(),
                ::core::mem::size_of::<[core::ffi::c_char; 256]>() as core::ffi::c_int,
                stdin,
            ))
            .is_null()
            {
                if line[0 as core::ffi::c_int as usize] as core::ffi::c_int == '\n' as i32 {
                    break;
                }
                strncat(
                    input.as_mut_ptr(),
                    line.as_ptr(),
                    (MAX_INPUT_SIZE as size_t)
                        .wrapping_sub(strlen(input.as_ptr()))
                        .wrapping_sub(1 as size_t),
                );
            }
            if (ops.load_text).expect("non-null function pointer")(input.as_ptr())
                != 0 as core::ffi::c_int
            {
                printf(b"Failed to load text\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            printf(b"\n=== Tokens ===\n\0" as *const u8 as *const core::ffi::c_char);
            let token_type_names: [*const core::ffi::c_char; 12] = [
                b"EOF\0" as *const u8 as *const core::ffi::c_char,
                b"WORD\0" as *const u8 as *const core::ffi::c_char,
                b"NUMBER\0" as *const u8 as *const core::ffi::c_char,
                b"PUNCT\0" as *const u8 as *const core::ffi::c_char,
                b"SPACE\0" as *const u8 as *const core::ffi::c_char,
                b"NEWLINE\0" as *const u8 as *const core::ffi::c_char,
                b"IDENT\0" as *const u8 as *const core::ffi::c_char,
                b"KEYWORD\0" as *const u8 as *const core::ffi::c_char,
                b"OPERATOR\0" as *const u8 as *const core::ffi::c_char,
                b"STRING\0" as *const u8 as *const core::ffi::c_char,
                b"COMMENT\0" as *const u8 as *const core::ffi::c_char,
                b"ERROR\0" as *const u8 as *const core::ffi::c_char,
            ];
            let mut token: token_t = token_t {
                type_0: TOKEN_EOF,
                value: [0; 256],
                length: 0,
                line: 0,
                column: 0,
            };
            let mut count: core::ffi::c_int = 0 as core::ffi::c_int;
            loop {
                token = (ops.next_token).expect("non-null function pointer")();
                if token.type_0 as core::ffi::c_uint
                    == TOKEN_EOF as core::ffi::c_int as core::ffi::c_uint
                {
                    break;
                }
                printf(
                    b"[%s] '%s' (L%d:C%d)\n\0" as *const u8 as *const core::ffi::c_char,
                    token_type_names[token.type_0 as usize],
                    (token.value).as_ptr(),
                    token.line,
                    token.column,
                );
                count += 1;
                if count <= 100 as core::ffi::c_int {
                    continue;
                }
                printf(
                    b"... (truncated, too many tokens)\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                break;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn read_file(
            filename: *const core::ffi::c_char,
        ) -> *mut core::ffi::c_char {
            let file: *mut FILE = fopen(filename, b"r\0" as *const u8 as *const core::ffi::c_char);
            if file.is_null() {
                fprintf(
                    stderr,
                    b"Error: Could not open file '%s'\n\0" as *const u8 as *const core::ffi::c_char,
                    filename,
                );
                return std::ptr::null_mut::<core::ffi::c_char>();
            }
            fseek(file, 0 as core::ffi::c_long, SEEK_END);
            let size: core::ffi::c_long = ftell(file);
            fseek(file, 0 as core::ffi::c_long, SEEK_SET);
            if size > MAX_BUFFER_SIZE as core::ffi::c_long {
                fprintf(
                    stderr,
                    b"Error: File too large\n\0" as *const u8 as *const core::ffi::c_char,
                );
                fclose(file);
                return std::ptr::null_mut::<core::ffi::c_char>();
            }
            let content: *mut core::ffi::c_char =
                malloc((size + 1 as core::ffi::c_long) as size_t) as *mut core::ffi::c_char;
            if content.is_null() {
                fprintf(
                    stderr,
                    b"Error: Memory allocation failed\n\0" as *const u8 as *const core::ffi::c_char,
                );
                fclose(file);
                return std::ptr::null_mut::<core::ffi::c_char>();
            }
            let read_size: size_t = fread(
                content as *mut core::ffi::c_void,
                1 as size_t,
                size as size_t,
                file,
            ) as size_t;
            *content.add(read_size) = '\0' as i32 as core::ffi::c_char;
            fclose(file);
            content
        }
        unsafe fn main_0() -> core::ffi::c_int {
            let ops: tokenizer_ops_t = get_tokenizer_ops();
            analyzer_init(ops);
            printf(
                b"Text Analysis and Tokenization System\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(
                b"This system demonstrates function pointers and static globals\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            let mut input: [core::ffi::c_char; 256] = [0; 256];
            let mut choice: core::ffi::c_int = 0;
            loop {
                print_menu();
                if (fgets(
                    input.as_mut_ptr(),
                    ::core::mem::size_of::<[core::ffi::c_char; 256]>() as core::ffi::c_int,
                    stdin,
                ))
                .is_null()
                {
                    break;
                }
                if sscanf(
                    input.as_ptr(),
                    b"%d\0" as *const u8 as *const core::ffi::c_char,
                    &mut choice as *mut core::ffi::c_int,
                ) != 1 as core::ffi::c_int
                {
                    printf(b"Invalid input\n\0" as *const u8 as *const core::ffi::c_char);
                } else {
                    match choice {
                        1 => {
                            printf(
                                b"Enter text to analyze (empty line to stop):\n\0" as *const u8
                                    as *const core::ffi::c_char,
                            );
                            let mut text: [core::ffi::c_char; 4096] = [b'\0' as i8; 4096];
                            let mut line: [core::ffi::c_char; 256] = [0; 256];
                            while !(fgets(
                                line.as_mut_ptr(),
                                ::core::mem::size_of::<[core::ffi::c_char; 256]>()
                                    as core::ffi::c_int,
                                stdin,
                            ))
                            .is_null()
                            {
                                if line[0 as core::ffi::c_int as usize] as core::ffi::c_int
                                    == '\n' as i32
                                {
                                    break;
                                }
                                strncat(
                                    text.as_mut_ptr(),
                                    line.as_ptr(),
                                    (MAX_INPUT_SIZE as size_t)
                                        .wrapping_sub(strlen(text.as_ptr()))
                                        .wrapping_sub(1 as size_t),
                                );
                            }
                            let result: analysis_result_t = analyze_text(text.as_ptr());
                            print_analysis_result(result);
                        }
                        2 => {
                            printf(b"Enter filename: \0" as *const u8 as *const core::ffi::c_char);
                            if !(fgets(
                                input.as_mut_ptr(),
                                ::core::mem::size_of::<[core::ffi::c_char; 256]>()
                                    as core::ffi::c_int,
                                stdin,
                            ))
                            .is_null()
                            {
                                input[strcspn(
                                    input.as_ptr(),
                                    b"\n\0" as *const u8 as *const core::ffi::c_char,
                                ) as usize] = 0 as core::ffi::c_char;
                                let content: *mut core::ffi::c_char = read_file(input.as_ptr());
                                if !content.is_null() {
                                    let result_0: analysis_result_t = analyze_text(content);
                                    print_analysis_result(result_0);
                                    free(content as *mut core::ffi::c_void);
                                }
                            }
                        }
                        3 => {
                            print_token_distribution();
                        }
                        4 => {
                            let score: core::ffi::c_int = calculate_complexity_score();
                            printf(
                                b"\nComplexity Score: %d\n\0" as *const u8
                                    as *const core::ffi::c_char,
                                score,
                            );
                            if score < 10 as core::ffi::c_int {
                                printf(
                                    b"Complexity: Low\n\0" as *const u8 as *const core::ffi::c_char,
                                );
                            } else if score < 50 as core::ffi::c_int {
                                printf(
                                    b"Complexity: Medium\n\0" as *const u8
                                        as *const core::ffi::c_char,
                                );
                            } else {
                                printf(
                                    b"Complexity: High\n\0" as *const u8
                                        as *const core::ffi::c_char,
                                );
                            }
                        }
                        5 => {
                            printf(
                                b"Enter pattern to search: \0" as *const u8
                                    as *const core::ffi::c_char,
                            );
                            if !(fgets(
                                input.as_mut_ptr(),
                                ::core::mem::size_of::<[core::ffi::c_char; 256]>()
                                    as core::ffi::c_int,
                                stdin,
                            ))
                            .is_null()
                            {
                                input[strcspn(
                                    input.as_ptr(),
                                    b"\n\0" as *const u8 as *const core::ffi::c_char,
                                ) as usize] = 0 as core::ffi::c_char;
                                find_patterns(input.as_ptr());
                            }
                        }
                        6 => {
                            interactive_tokenizer(ops);
                        }
                        7 => {
                            printf(b"Goodbye!\n\0" as *const u8 as *const core::ffi::c_char);
                            return 0 as core::ffi::c_int;
                        }
                        _ => {
                            printf(b"Invalid choice\n\0" as *const u8 as *const core::ffi::c_char);
                        }
                    }
                }
            }
            0 as core::ffi::c_int
        }
        pub fn main() {
            unsafe { ::std::process::exit(main_0() as i32) }
        }
    }
    pub mod tokenizer {
        use crate::src::analyzer::size_t;
        use crate::src::analyzer::token_t;
        use crate::src::analyzer::token_type_t;
        use crate::src::analyzer::tokenizer_get_stats_fn;
        use crate::src::analyzer::tokenizer_load_fn;
        use crate::src::analyzer::tokenizer_next_fn;
        use crate::src::analyzer::tokenizer_ops_t;
        use crate::src::analyzer::tokenizer_peek_fn;
        use crate::src::analyzer::tokenizer_reset_fn;
        use crate::src::analyzer::FILE;
        extern "C" {
            static mut stderr: *mut FILE;
            fn fprintf(
                __stream: *mut FILE,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn strncpy(
                __dest: *mut core::ffi::c_char,
                __src: *const core::ffi::c_char,
                __n: size_t,
            ) -> *mut core::ffi::c_char;
            fn strcmp(
                __s1: *const core::ffi::c_char,
                __s2: *const core::ffi::c_char,
            ) -> core::ffi::c_int;
            fn strchr(
                __s: *const core::ffi::c_char,
                __c: core::ffi::c_int,
            ) -> *mut core::ffi::c_char;
            fn strlen(__s: *const core::ffi::c_char) -> size_t;
            fn __ctype_b_loc() -> *mut *const core::ffi::c_ushort;
        }
        pub const TOKEN_ERROR: token_type_t = 11;
        pub const TOKEN_COMMENT: token_type_t = 10;
        pub const TOKEN_STRING: token_type_t = 9;
        pub const TOKEN_OPERATOR: token_type_t = 8;
        pub const TOKEN_KEYWORD: token_type_t = 7;
        pub const TOKEN_IDENTIFIER: token_type_t = 6;
        pub const TOKEN_NEWLINE: token_type_t = 5;
        pub const TOKEN_WHITESPACE: token_type_t = 4;
        pub const TOKEN_PUNCTUATION: token_type_t = 3;
        pub const TOKEN_NUMBER: token_type_t = 2;
        pub const TOKEN_WORD: token_type_t = 1;
        pub const TOKEN_EOF: token_type_t = 0;
        pub const _ISdigit: C2RustUnnamed = 2048;
        pub const _ISalnum: C2RustUnnamed = 8;
        pub const _ISalpha: C2RustUnnamed = 1024;
        pub const _ISspace: C2RustUnnamed = 8192;
        pub type C2RustUnnamed = core::ffi::c_uint;
        pub const _ISpunct: C2RustUnnamed = 4;
        pub const _IScntrl: C2RustUnnamed = 2;
        pub const _ISblank: C2RustUnnamed = 1;
        pub const _ISgraph: C2RustUnnamed = 32768;
        pub const _ISprint: C2RustUnnamed = 16384;
        pub const _ISxdigit: C2RustUnnamed = 4096;
        pub const _ISlower: C2RustUnnamed = 512;
        pub const _ISupper: C2RustUnnamed = 256;
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const MAX_TOKEN_LENGTH: core::ffi::c_int = 256 as core::ffi::c_int;
        pub const MAX_BUFFER_SIZE: core::ffi::c_int = 8192 as core::ffi::c_int;
        static mut input_buffer: [core::ffi::c_char; 8192] = [0; 8192];
        static mut buffer_length: size_t = 0 as size_t;
        static mut current_position: size_t = 0 as size_t;
        static mut current_line: core::ffi::c_int = 1 as core::ffi::c_int;
        static mut current_column: core::ffi::c_int = 1 as core::ffi::c_int;
        static mut total_tokens_processed: size_t = 0 as size_t;
        static mut total_lines_processed: size_t = 0 as size_t;
        static mut total_chars_processed: size_t = 0 as size_t;
        static mut lookahead_token: token_t = token_t {
            type_0: TOKEN_EOF,
            value: [0; 256],
            length: 0,
            line: 0,
            column: 0,
        };
        static mut lookahead_valid: core::ffi::c_int = 0 as core::ffi::c_int;
        static mut keywords: [*const core::ffi::c_char; 31] = [
            b"if\0" as *const u8 as *const core::ffi::c_char,
            b"else\0" as *const u8 as *const core::ffi::c_char,
            b"while\0" as *const u8 as *const core::ffi::c_char,
            b"for\0" as *const u8 as *const core::ffi::c_char,
            b"return\0" as *const u8 as *const core::ffi::c_char,
            b"int\0" as *const u8 as *const core::ffi::c_char,
            b"char\0" as *const u8 as *const core::ffi::c_char,
            b"float\0" as *const u8 as *const core::ffi::c_char,
            b"double\0" as *const u8 as *const core::ffi::c_char,
            b"void\0" as *const u8 as *const core::ffi::c_char,
            b"struct\0" as *const u8 as *const core::ffi::c_char,
            b"typedef\0" as *const u8 as *const core::ffi::c_char,
            b"const\0" as *const u8 as *const core::ffi::c_char,
            b"static\0" as *const u8 as *const core::ffi::c_char,
            b"extern\0" as *const u8 as *const core::ffi::c_char,
            b"auto\0" as *const u8 as *const core::ffi::c_char,
            b"register\0" as *const u8 as *const core::ffi::c_char,
            b"sizeof\0" as *const u8 as *const core::ffi::c_char,
            b"break\0" as *const u8 as *const core::ffi::c_char,
            b"continue\0" as *const u8 as *const core::ffi::c_char,
            b"switch\0" as *const u8 as *const core::ffi::c_char,
            b"case\0" as *const u8 as *const core::ffi::c_char,
            b"default\0" as *const u8 as *const core::ffi::c_char,
            b"do\0" as *const u8 as *const core::ffi::c_char,
            b"goto\0" as *const u8 as *const core::ffi::c_char,
            b"enum\0" as *const u8 as *const core::ffi::c_char,
            b"union\0" as *const u8 as *const core::ffi::c_char,
            b"signed\0" as *const u8 as *const core::ffi::c_char,
            b"unsigned\0" as *const u8 as *const core::ffi::c_char,
            b"long\0" as *const u8 as *const core::ffi::c_char,
            b"short\0" as *const u8 as *const core::ffi::c_char,
        ];
        static mut num_keywords: core::ffi::c_int = 0;
        unsafe extern "C" fn is_keyword(str: *const core::ffi::c_char) -> core::ffi::c_int {
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < num_keywords {
                if strcmp(str, keywords[i as usize]) == 0 as core::ffi::c_int {
                    return 1 as core::ffi::c_int;
                }
                i += 1;
            }
            0 as core::ffi::c_int
        }
        unsafe extern "C" fn peek_char() -> core::ffi::c_char {
            if current_position >= buffer_length {
                return '\0' as i32 as core::ffi::c_char;
            }
            input_buffer[current_position]
        }
        unsafe extern "C" fn advance_char() -> core::ffi::c_char {
            if current_position >= buffer_length {
                return '\0' as i32 as core::ffi::c_char;
            }
            let fresh0 = current_position;
            current_position = current_position.wrapping_add(1);
            let c: core::ffi::c_char = input_buffer[fresh0];
            total_chars_processed = total_chars_processed.wrapping_add(1);
            if c as core::ffi::c_int == '\n' as i32 {
                current_line += 1;
                current_column = 1 as core::ffi::c_int;
                total_lines_processed = total_lines_processed.wrapping_add(1);
            } else {
                current_column += 1;
            }
            c
        }
        unsafe extern "C" fn skip_whitespace() {
            while peek_char() as core::ffi::c_int != '\0' as i32
                && *(*__ctype_b_loc()).offset(peek_char() as core::ffi::c_int as isize)
                    as core::ffi::c_int
                    & _ISspace as core::ffi::c_int as core::ffi::c_ushort as core::ffi::c_int
                    != 0
                && peek_char() as core::ffi::c_int != '\n' as i32
            {
                advance_char();
            }
        }
        unsafe extern "C" fn create_token(
            type_0: token_type_t,
            value: *const core::ffi::c_char,
            length: size_t,
        ) -> token_t {
            let mut token: token_t = token_t {
                type_0: TOKEN_EOF,
                value: [0; 256],
                length: 0,
                line: 0,
                column: 0,
            };
            token.type_0 = type_0;
            token.length = if length < MAX_TOKEN_LENGTH as size_t {
                length
            } else {
                (MAX_TOKEN_LENGTH - 1 as core::ffi::c_int) as size_t
            };
            strncpy((token.value).as_mut_ptr(), value, token.length);
            token.value[token.length] = '\0' as i32 as core::ffi::c_char;
            token.line = current_line;
            token.column =
                (current_column as size_t).wrapping_sub(token.length) as core::ffi::c_int;
            total_tokens_processed = total_tokens_processed.wrapping_add(1);
            token
        }
        unsafe extern "C" fn scan_word() -> token_t {
            let mut buffer: [core::ffi::c_char; 256] = [0; 256];
            let mut length: size_t = 0 as size_t;
            while peek_char() as core::ffi::c_int != '\0' as i32
                && (*(*__ctype_b_loc()).offset(peek_char() as core::ffi::c_int as isize)
                    as core::ffi::c_int
                    & _ISalnum as core::ffi::c_int as core::ffi::c_ushort as core::ffi::c_int
                    != 0
                    || peek_char() as core::ffi::c_int == '_' as i32)
                && length < (MAX_TOKEN_LENGTH - 1 as core::ffi::c_int) as size_t
            {
                let fresh16 = length;
                length = length.wrapping_add(1);
                buffer[fresh16 as usize] = advance_char();
            }
            buffer[length as usize] = '\0' as i32 as core::ffi::c_char;
            if is_keyword(buffer.as_ptr()) != 0 {
                return create_token(TOKEN_KEYWORD, buffer.as_ptr(), length);
            }
            create_token(TOKEN_IDENTIFIER, buffer.as_ptr(), length)
        }
        unsafe extern "C" fn scan_number() -> token_t {
            let mut buffer: [core::ffi::c_char; 256] = [0; 256];
            let mut length: size_t = 0 as size_t;
            let mut has_decimal: core::ffi::c_int = 0 as core::ffi::c_int;
            while peek_char() as core::ffi::c_int != '\0' as i32
                && (*(*__ctype_b_loc()).offset(peek_char() as core::ffi::c_int as isize)
                    as core::ffi::c_int
                    & _ISdigit as core::ffi::c_int as core::ffi::c_ushort as core::ffi::c_int
                    != 0
                    || peek_char() as core::ffi::c_int == '.' as i32)
                && length < (MAX_TOKEN_LENGTH - 1 as core::ffi::c_int) as size_t
            {
                if peek_char() as core::ffi::c_int == '.' as i32 {
                    if has_decimal != 0 {
                        break;
                    }
                    has_decimal = 1 as core::ffi::c_int;
                }
                let fresh15 = length;
                length = length.wrapping_add(1);
                buffer[fresh15 as usize] = advance_char();
            }
            buffer[length as usize] = '\0' as i32 as core::ffi::c_char;
            create_token(TOKEN_NUMBER, buffer.as_ptr(), length)
        }
        unsafe extern "C" fn scan_string() -> token_t {
            let mut buffer: [core::ffi::c_char; 256] = [0; 256];
            let mut length: size_t = 0 as size_t;
            let quote: core::ffi::c_char = advance_char();
            let fresh10 = length;
            length = length.wrapping_add(1);
            buffer[fresh10 as usize] = quote;
            while peek_char() as core::ffi::c_int != '\0' as i32
                && peek_char() as core::ffi::c_int != quote as core::ffi::c_int
                && peek_char() as core::ffi::c_int != '\n' as i32
                && length < (MAX_TOKEN_LENGTH - 2 as core::ffi::c_int) as size_t
            {
                if peek_char() as core::ffi::c_int == '\\' as i32 {
                    let fresh11 = length;
                    length = length.wrapping_add(1);
                    buffer[fresh11 as usize] = advance_char();
                    if peek_char() as core::ffi::c_int != '\0' as i32 {
                        let fresh12 = length;
                        length = length.wrapping_add(1);
                        buffer[fresh12 as usize] = advance_char();
                    }
                } else {
                    let fresh13 = length;
                    length = length.wrapping_add(1);
                    buffer[fresh13 as usize] = advance_char();
                }
            }
            if peek_char() as core::ffi::c_int == quote as core::ffi::c_int {
                let fresh14 = length;
                length = length.wrapping_add(1);
                buffer[fresh14 as usize] = advance_char();
            }
            buffer[length as usize] = '\0' as i32 as core::ffi::c_char;
            create_token(TOKEN_STRING, buffer.as_ptr(), length)
        }
        unsafe extern "C" fn scan_comment() -> token_t {
            let mut buffer: [core::ffi::c_char; 256] = [0; 256];
            let mut length: size_t = 0 as size_t;
            let fresh3 = length;
            length = length.wrapping_add(1);
            buffer[fresh3 as usize] = advance_char();
            if peek_char() as core::ffi::c_int == '/' as i32 {
                let fresh4 = length;
                length = length.wrapping_add(1);
                buffer[fresh4 as usize] = advance_char();
                while peek_char() as core::ffi::c_int != '\0' as i32
                    && peek_char() as core::ffi::c_int != '\n' as i32
                    && length < (MAX_TOKEN_LENGTH - 1 as core::ffi::c_int) as size_t
                {
                    let fresh5 = length;
                    length = length.wrapping_add(1);
                    buffer[fresh5 as usize] = advance_char();
                }
            } else if peek_char() as core::ffi::c_int == '*' as i32 {
                let fresh6 = length;
                length = length.wrapping_add(1);
                buffer[fresh6 as usize] = advance_char();
                while peek_char() as core::ffi::c_int != '\0' as i32
                    && length < (MAX_TOKEN_LENGTH - 2 as core::ffi::c_int) as size_t
                {
                    if peek_char() as core::ffi::c_int == '*' as i32 {
                        let fresh7 = length;
                        length = length.wrapping_add(1);
                        buffer[fresh7 as usize] = advance_char();
                        if peek_char() as core::ffi::c_int != '/' as i32 {
                            continue;
                        }
                        let fresh8 = length;
                        length = length.wrapping_add(1);
                        buffer[fresh8 as usize] = advance_char();
                        break;
                    } else {
                        let fresh9 = length;
                        length = length.wrapping_add(1);
                        buffer[fresh9 as usize] = advance_char();
                    }
                }
            }
            buffer[length as usize] = '\0' as i32 as core::ffi::c_char;
            create_token(TOKEN_COMMENT, buffer.as_ptr(), length)
        }
        unsafe extern "C" fn scan_operator() -> token_t {
            let mut buffer: [core::ffi::c_char; 256] = [0; 256];
            let mut length: size_t = 0 as size_t;
            let c: core::ffi::c_char = peek_char();
            let fresh1 = length;
            length = length.wrapping_add(1);
            buffer[fresh1 as usize] = advance_char();
            let next: core::ffi::c_char = peek_char();
            if c as core::ffi::c_int == '=' as i32 && next as core::ffi::c_int == '=' as i32
                || c as core::ffi::c_int == '!' as i32 && next as core::ffi::c_int == '=' as i32
                || c as core::ffi::c_int == '<' as i32 && next as core::ffi::c_int == '=' as i32
                || c as core::ffi::c_int == '>' as i32 && next as core::ffi::c_int == '=' as i32
                || c as core::ffi::c_int == '&' as i32 && next as core::ffi::c_int == '&' as i32
                || c as core::ffi::c_int == '|' as i32 && next as core::ffi::c_int == '|' as i32
                || c as core::ffi::c_int == '+' as i32 && next as core::ffi::c_int == '+' as i32
                || c as core::ffi::c_int == '-' as i32 && next as core::ffi::c_int == '-' as i32
                || c as core::ffi::c_int == '-' as i32 && next as core::ffi::c_int == '>' as i32
                || c as core::ffi::c_int == '<' as i32 && next as core::ffi::c_int == '<' as i32
                || c as core::ffi::c_int == '>' as i32 && next as core::ffi::c_int == '>' as i32
            {
                let fresh2 = length;
                length = length.wrapping_add(1);
                buffer[fresh2 as usize] = advance_char();
            }
            buffer[length as usize] = '\0' as i32 as core::ffi::c_char;
            create_token(TOKEN_OPERATOR, buffer.as_ptr(), length)
        }
        #[no_mangle]
        pub unsafe extern "C" fn tokenizer_next_token() -> token_t {
            if lookahead_valid != 0 {
                lookahead_valid = 0 as core::ffi::c_int;
                return lookahead_token;
            }
            skip_whitespace();
            if current_position >= buffer_length {
                return create_token(
                    TOKEN_EOF,
                    b"\0" as *const u8 as *const core::ffi::c_char,
                    0 as size_t,
                );
            }
            let c: core::ffi::c_char = peek_char();
            if c as core::ffi::c_int == '\n' as i32 {
                let newline: [core::ffi::c_char; 2] =
                    [advance_char(), '\0' as i32 as core::ffi::c_char];
                return create_token(TOKEN_NEWLINE, newline.as_ptr(), 1 as size_t);
            }
            if *(*__ctype_b_loc()).offset(c as core::ffi::c_int as isize) as core::ffi::c_int
                & _ISalpha as core::ffi::c_int as core::ffi::c_ushort as core::ffi::c_int
                != 0
                || c as core::ffi::c_int == '_' as i32
            {
                return scan_word();
            }
            if *(*__ctype_b_loc()).offset(c as core::ffi::c_int as isize) as core::ffi::c_int
                & _ISdigit as core::ffi::c_int as core::ffi::c_ushort as core::ffi::c_int
                != 0
            {
                return scan_number();
            }
            if c as core::ffi::c_int == '"' as i32 || c as core::ffi::c_int == '\'' as i32 {
                return scan_string();
            }
            if c as core::ffi::c_int == '/' as i32
                && (peek_char() as core::ffi::c_int == '/' as i32
                    || peek_char() as core::ffi::c_int == '*' as i32)
            {
                return scan_comment();
            }
            if !(strchr(
                b"+-*/%=<>!&|^~?:\0" as *const u8 as *const core::ffi::c_char,
                c as core::ffi::c_int,
            ))
            .is_null()
            {
                return scan_operator();
            }
            if !(strchr(
                b"(){}[];,.\0" as *const u8 as *const core::ffi::c_char,
                c as core::ffi::c_int,
            ))
            .is_null()
            {
                let punct: [core::ffi::c_char; 2] =
                    [advance_char(), '\0' as i32 as core::ffi::c_char];
                return create_token(TOKEN_PUNCTUATION, punct.as_ptr(), 1 as size_t);
            }
            let unknown: [core::ffi::c_char; 2] =
                [advance_char(), '\0' as i32 as core::ffi::c_char];
            create_token(TOKEN_ERROR, unknown.as_ptr(), 1 as size_t)
        }
        #[no_mangle]
        pub unsafe extern "C" fn tokenizer_peek_token() -> token_t {
            if lookahead_valid == 0 {
                lookahead_token = tokenizer_next_token();
                lookahead_valid = 1 as core::ffi::c_int;
            }
            lookahead_token
        }
        #[no_mangle]
        pub unsafe extern "C" fn tokenizer_reset() {
            current_position = 0 as size_t;
            current_line = 1 as core::ffi::c_int;
            current_column = 1 as core::ffi::c_int;
            lookahead_valid = 0 as core::ffi::c_int;
        }
        #[no_mangle]
        pub unsafe extern "C" fn tokenizer_load_text(
            text: *const core::ffi::c_char,
        ) -> core::ffi::c_int {
            if text.is_null() {
                return -(1 as core::ffi::c_int);
            }
            let length: size_t = strlen(text);
            if length >= MAX_BUFFER_SIZE as size_t {
                fprintf(
                    stderr,
                    b"Error: Input text too large\n\0" as *const u8 as *const core::ffi::c_char,
                );
                return -(1 as core::ffi::c_int);
            }
            strncpy(
                input_buffer.as_mut_ptr(),
                text,
                (MAX_BUFFER_SIZE - 1 as core::ffi::c_int) as size_t,
            );
            input_buffer[(MAX_BUFFER_SIZE - 1 as core::ffi::c_int) as usize] =
                '\0' as i32 as core::ffi::c_char;
            buffer_length = length;
            tokenizer_reset();
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn tokenizer_get_stats(
            lines: *mut size_t,
            tokens: *mut size_t,
            chars: *mut size_t,
        ) {
            if !lines.is_null() {
                *lines = total_lines_processed;
            }
            if !tokens.is_null() {
                *tokens = total_tokens_processed;
            }
            if !chars.is_null() {
                *chars = total_chars_processed;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn get_tokenizer_ops() -> tokenizer_ops_t {
            let mut ops: tokenizer_ops_t = tokenizer_ops_t {
                next_token: None,
                peek_token: None,
                reset: None,
                load_text: None,
                get_stats: None,
            };
            ops.next_token = Some(tokenizer_next_token as unsafe extern "C" fn() -> token_t)
                as tokenizer_next_fn;
            ops.peek_token = Some(tokenizer_peek_token as unsafe extern "C" fn() -> token_t)
                as tokenizer_peek_fn;
            ops.reset = Some(tokenizer_reset as unsafe extern "C" fn() -> ()) as tokenizer_reset_fn;
            ops.load_text = Some(
                tokenizer_load_text
                    as unsafe extern "C" fn(*const core::ffi::c_char) -> core::ffi::c_int,
            ) as tokenizer_load_fn;
            ops.get_stats = Some(
                tokenizer_get_stats
                    as unsafe extern "C" fn(*mut size_t, *mut size_t, *mut size_t) -> (),
            ) as tokenizer_get_stats_fn;
            ops
        }
        unsafe extern "C" fn run_static_initializers() {
            num_keywords = ::core::mem::size_of::<[*const core::ffi::c_char; 31]>()
                .wrapping_div(::core::mem::size_of::<*const core::ffi::c_char>())
                as core::ffi::c_int;
        }
        #[used]
        #[link_section = ".init_array"]
        static INIT_ARRAY: [unsafe extern "C" fn(); 1] = [run_static_initializers];
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates("static-vars-fpts", SOURCE, &["read_file#content"], &[]);
}
