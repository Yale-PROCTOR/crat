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
        extern "C" {
            pub type _IO_wide_data;
            pub type _IO_codecvt;
            pub type _IO_marker;
            static mut stdin: *mut FILE;
            fn printf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
            fn fgets(
                __s: *mut core::ffi::c_char,
                __n: core::ffi::c_int,
                __stream: *mut FILE,
            ) -> *mut core::ffi::c_char;
            fn atoi(__nptr: *const core::ffi::c_char) -> core::ffi::c_int;
            fn exit(__status: core::ffi::c_int) -> !;
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
            fn strncmp(
                __s1: *const core::ffi::c_char,
                __s2: *const core::ffi::c_char,
                __n: size_t,
            ) -> core::ffi::c_int;
            fn strcspn(
                __s: *const core::ffi::c_char,
                __reject: *const core::ffi::c_char,
            ) -> core::ffi::c_ulong;
            fn strstr(
                __haystack: *const core::ffi::c_char,
                __needle: *const core::ffi::c_char,
            ) -> *mut core::ffi::c_char;
            fn strtok(
                __s: *mut core::ffi::c_char,
                __delim: *const core::ffi::c_char,
            ) -> *mut core::ffi::c_char;
            fn strlen(__s: *const core::ffi::c_char) -> size_t;
            fn time(__timer: *mut time_t) -> time_t;
            fn ctime(__timer: *const time_t) -> *mut core::ffi::c_char;
        }
        pub type size_t = usize;
        pub type __off_t = core::ffi::c_long;
        pub type __off64_t = core::ffi::c_long;
        pub type __time_t = core::ffi::c_long;
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
        pub type time_t = __time_t;
        #[repr(C)]
        pub struct user_t {
            pub name: [core::ffi::c_char; 32],
            pub password: [core::ffi::c_char; 32],
            pub permission_level: core::ffi::c_int,
            pub logged_in: core::ffi::c_int,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for user_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for user_t {
            #[inline]
            fn clone(&self) -> user_t {
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 32]>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 32]>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                *self
            }
        }
        #[repr(C)]
        pub struct file_t {
            pub filename: [core::ffi::c_char; 64],
            pub content: [core::ffi::c_char; 512],
            pub owner: [core::ffi::c_char; 32],
            pub permissions: core::ffi::c_int,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for file_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for file_t {
            #[inline]
            fn clone(&self) -> file_t {
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 64]>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 512]>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 32]>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                *self
            }
        }
        #[repr(C)]
        pub struct variable_t {
            pub name: [core::ffi::c_char; 32],
            pub value: [core::ffi::c_char; 128],
        }
        #[automatically_derived]
        impl ::core::marker::Copy for variable_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for variable_t {
            #[inline]
            fn clone(&self) -> variable_t {
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 32]>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 128]>;
                *self
            }
        }
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const MAX_INPUT: core::ffi::c_int = 256 as core::ffi::c_int;
        pub const MAX_COMMAND: core::ffi::c_int = 64 as core::ffi::c_int;
        pub const MAX_ARGS: core::ffi::c_int = 10 as core::ffi::c_int;
        pub const MAX_FILES: core::ffi::c_int = 20 as core::ffi::c_int;
        pub const MAX_USERS: core::ffi::c_int = 10 as core::ffi::c_int;
        pub const MAX_VARIABLES: core::ffi::c_int = 20 as core::ffi::c_int;
        static mut users: [user_t; 10] = [user_t {
            name: [0; 32],
            password: [0; 32],
            permission_level: 0,
            logged_in: 0,
        }; 10];
        static mut user_count: core::ffi::c_int = 0 as core::ffi::c_int;
        static mut current_user: *mut user_t = 0 as *const user_t as *mut user_t;
        static mut files: [file_t; 20] = [file_t {
            filename: [0; 64],
            content: [0; 512],
            owner: [0; 32],
            permissions: 0,
        }; 20];
        static mut file_count: core::ffi::c_int = 0 as core::ffi::c_int;
        static mut variables: [variable_t; 20] = [variable_t {
            name: [0; 32],
            value: [0; 128],
        }; 20];
        static mut variable_count: core::ffi::c_int = 0 as core::ffi::c_int;
        static mut debug_mode: core::ffi::c_int = 0 as core::ffi::c_int;
        static mut verbose_mode: core::ffi::c_int = 0 as core::ffi::c_int;
        #[no_mangle]
        pub unsafe extern "C" fn parse_command(
            input: *const core::ffi::c_char,
            cmd: *mut core::ffi::c_char,
            args: *mut [core::ffi::c_char; 64],
            arg_count: *mut core::ffi::c_int,
        ) {
            let mut temp: [core::ffi::c_char; 256] = [0; 256];
            strncpy(
                temp.as_mut_ptr(),
                input,
                (MAX_INPUT - 1 as core::ffi::c_int) as size_t,
            );
            temp[(MAX_INPUT - 1 as core::ffi::c_int) as usize] = '\0' as i32 as core::ffi::c_char;
            *arg_count = 0 as core::ffi::c_int;
            let mut token: *mut core::ffi::c_char = strtok(
                temp.as_mut_ptr(),
                b" \t\0" as *const u8 as *const core::ffi::c_char,
            );
            if !token.is_null() {
                strncpy(cmd, token, (MAX_COMMAND - 1 as core::ffi::c_int) as size_t);
                *cmd.offset((MAX_COMMAND - 1 as core::ffi::c_int) as isize) =
                    '\0' as i32 as core::ffi::c_char;
                loop {
                    token = strtok(
                        std::ptr::null_mut::<core::ffi::c_char>(),
                        b" \t\0" as *const u8 as *const core::ffi::c_char,
                    );
                    if !(!token.is_null() && *arg_count < MAX_ARGS) {
                        break;
                    }
                    strncpy(
                        (*args.offset(*arg_count as isize)).as_mut_ptr(),
                        token,
                        (MAX_COMMAND - 1 as core::ffi::c_int) as size_t,
                    );
                    (*args.offset(*arg_count as isize))
                        [(MAX_COMMAND - 1 as core::ffi::c_int) as usize] =
                        '\0' as i32 as core::ffi::c_char;
                    *arg_count += 1;
                }
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn cmd_adduser(
            args: *mut [core::ffi::c_char; 64],
            arg_count: core::ffi::c_int,
        ) {
            if arg_count < 2 as core::ffi::c_int {
                printf(
                    b"Usage: adduser <username> <password> [permission_level]\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return;
            }
            if user_count >= MAX_USERS {
                printf(
                    b"Error: Maximum users reached\n\0" as *const u8 as *const core::ffi::c_char,
                );
                return;
            }
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < user_count {
                if strcmp(
                    (users[i as usize].name).as_ptr(),
                    (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                ) == 0 as core::ffi::c_int
                {
                    printf(
                        b"Error: User '%s' already exists\n\0" as *const u8
                            as *const core::ffi::c_char,
                        (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                    );
                    return;
                }
                i += 1;
            }
            strcpy(
                (users[user_count as usize].name).as_mut_ptr(),
                (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
            );
            strcpy(
                (users[user_count as usize].password).as_mut_ptr(),
                (*args.offset(1 as core::ffi::c_int as isize)).as_ptr(),
            );
            users[user_count as usize].permission_level = if arg_count >= 3 as core::ffi::c_int {
                atoi((*args.offset(2 as core::ffi::c_int as isize)).as_ptr())
            } else {
                1 as core::ffi::c_int
            };
            users[user_count as usize].logged_in = 0 as core::ffi::c_int;
            user_count += 1;
            printf(
                b"User '%s' added with permission level %d\n\0" as *const u8
                    as *const core::ffi::c_char,
                (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                users[(user_count - 1 as core::ffi::c_int) as usize].permission_level,
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn cmd_login(
            args: *mut [core::ffi::c_char; 64],
            arg_count: core::ffi::c_int,
        ) {
            if arg_count < 2 as core::ffi::c_int {
                printf(
                    b"Usage: login <username> <password>\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return;
            }
            if !current_user.is_null() && (*current_user).logged_in != 0 {
                printf(
                    b"Error: User '%s' already logged in. Use 'logout' first.\n\0" as *const u8
                        as *const core::ffi::c_char,
                    ((*current_user).name).as_ptr(),
                );
                return;
            }
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < user_count {
                if strcmp(
                    (users[i as usize].name).as_ptr(),
                    (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                ) == 0 as core::ffi::c_int
                {
                    if strcmp(
                        (users[i as usize].password).as_ptr(),
                        (*args.offset(1 as core::ffi::c_int as isize)).as_ptr(),
                    ) == 0 as core::ffi::c_int
                    {
                        users[i as usize].logged_in = 1 as core::ffi::c_int;
                        current_user = &mut *users.as_mut_ptr().offset(i as isize) as *mut user_t;
                        printf(
                            b"Login successful. Welcome, %s!\n\0" as *const u8
                                as *const core::ffi::c_char,
                            ((*current_user).name).as_ptr(),
                        );
                        return;
                    } else {
                        printf(
                            b"Error: Incorrect password\n\0" as *const u8
                                as *const core::ffi::c_char,
                        );
                        return;
                    }
                }
                i += 1;
            }
            printf(b"Error: User not found\n\0" as *const u8 as *const core::ffi::c_char);
        }
        #[no_mangle]
        pub unsafe extern "C" fn cmd_logout() {
            if current_user.is_null() || (*current_user).logged_in == 0 {
                printf(b"Error: No user logged in\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            printf(
                b"Goodbye, %s!\n\0" as *const u8 as *const core::ffi::c_char,
                ((*current_user).name).as_ptr(),
            );
            (*current_user).logged_in = 0 as core::ffi::c_int;
            current_user = std::ptr::null_mut::<user_t>();
        }
        #[no_mangle]
        pub unsafe extern "C" fn cmd_whoami() {
            if current_user.is_null() || (*current_user).logged_in == 0 {
                printf(b"Not logged in\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            printf(
                b"Current user: %s\n\0" as *const u8 as *const core::ffi::c_char,
                ((*current_user).name).as_ptr(),
            );
            printf(
                b"Permission level: %d\n\0" as *const u8 as *const core::ffi::c_char,
                (*current_user).permission_level,
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn cmd_listusers() {
            if user_count == 0 as core::ffi::c_int {
                printf(b"No users registered\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            printf(b"Registered users:\n\0" as *const u8 as *const core::ffi::c_char);
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < user_count {
                printf(
                    b"  %s (level %d) %s\n\0" as *const u8 as *const core::ffi::c_char,
                    (users[i as usize].name).as_ptr(),
                    users[i as usize].permission_level,
                    if users[i as usize].logged_in != 0 {
                        b"[logged in]\0" as *const u8 as *const core::ffi::c_char
                    } else {
                        b"\0" as *const u8 as *const core::ffi::c_char
                    },
                );
                i += 1;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn cmd_createfile(
            args: *mut [core::ffi::c_char; 64],
            arg_count: core::ffi::c_int,
        ) {
            if current_user.is_null() || (*current_user).logged_in == 0 {
                printf(b"Error: Must be logged in\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            if arg_count < 1 as core::ffi::c_int {
                printf(
                    b"Usage: createfile <filename> [content]\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return;
            }
            if file_count >= MAX_FILES {
                printf(
                    b"Error: Maximum files reached\n\0" as *const u8 as *const core::ffi::c_char,
                );
                return;
            }
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < file_count {
                if strcmp(
                    (files[i as usize].filename).as_ptr(),
                    (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                ) == 0 as core::ffi::c_int
                {
                    printf(
                        b"Error: File '%s' already exists\n\0" as *const u8
                            as *const core::ffi::c_char,
                        (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                    );
                    return;
                }
                i += 1;
            }
            strcpy(
                (files[file_count as usize].filename).as_mut_ptr(),
                (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
            );
            strcpy(
                (files[file_count as usize].owner).as_mut_ptr(),
                ((*current_user).name).as_ptr(),
            );
            files[file_count as usize].permissions = 755 as core::ffi::c_int;
            if arg_count >= 2 as core::ffi::c_int {
                strcpy(
                    (files[file_count as usize].content).as_mut_ptr(),
                    (*args.offset(1 as core::ffi::c_int as isize)).as_ptr(),
                );
            } else {
                files[file_count as usize].content[0 as core::ffi::c_int as usize] =
                    '\0' as i32 as core::ffi::c_char;
            }
            file_count += 1;
            printf(
                b"File '%s' created\n\0" as *const u8 as *const core::ffi::c_char,
                (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn cmd_readfile(
            args: *mut [core::ffi::c_char; 64],
            arg_count: core::ffi::c_int,
        ) {
            if arg_count < 1 as core::ffi::c_int {
                printf(b"Usage: readfile <filename>\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < file_count {
                if strcmp(
                    (files[i as usize].filename).as_ptr(),
                    (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                ) == 0 as core::ffi::c_int
                {
                    printf(
                        b"=== %s ===\n\0" as *const u8 as *const core::ffi::c_char,
                        (files[i as usize].filename).as_ptr(),
                    );
                    printf(
                        b"Owner: %s\n\0" as *const u8 as *const core::ffi::c_char,
                        (files[i as usize].owner).as_ptr(),
                    );
                    printf(
                        b"Permissions: %d\n\0" as *const u8 as *const core::ffi::c_char,
                        files[i as usize].permissions,
                    );
                    printf(
                        b"Content: %s\n\0" as *const u8 as *const core::ffi::c_char,
                        (files[i as usize].content).as_ptr(),
                    );
                    return;
                }
                i += 1;
            }
            printf(
                b"Error: File '%s' not found\n\0" as *const u8 as *const core::ffi::c_char,
                (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn cmd_writefile(
            args: *mut [core::ffi::c_char; 64],
            arg_count: core::ffi::c_int,
        ) {
            if current_user.is_null() || (*current_user).logged_in == 0 {
                printf(b"Error: Must be logged in\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            if arg_count < 2 as core::ffi::c_int {
                printf(
                    b"Usage: writefile <filename> <content>\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return;
            }
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < file_count {
                if strcmp(
                    (files[i as usize].filename).as_ptr(),
                    (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                ) == 0 as core::ffi::c_int
                {
                    if strcmp(
                        (files[i as usize].owner).as_ptr(),
                        ((*current_user).name).as_ptr(),
                    ) == 0 as core::ffi::c_int
                        || (*current_user).permission_level >= 5 as core::ffi::c_int
                    {
                        strcpy(
                            (files[i as usize].content).as_mut_ptr(),
                            (*args.offset(1 as core::ffi::c_int as isize)).as_ptr(),
                        );
                        printf(
                            b"File '%s' updated\n\0" as *const u8 as *const core::ffi::c_char,
                            (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                        );
                        return;
                    } else {
                        printf(
                            b"Error: Permission denied\n\0" as *const u8
                                as *const core::ffi::c_char,
                        );
                        return;
                    }
                }
                i += 1;
            }
            printf(
                b"Error: File '%s' not found\n\0" as *const u8 as *const core::ffi::c_char,
                (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn cmd_deletefile(
            args: *mut [core::ffi::c_char; 64],
            arg_count: core::ffi::c_int,
        ) {
            if current_user.is_null() || (*current_user).logged_in == 0 {
                printf(b"Error: Must be logged in\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            if arg_count < 1 as core::ffi::c_int {
                printf(
                    b"Usage: deletefile <filename>\n\0" as *const u8 as *const core::ffi::c_char,
                );
                return;
            }
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < file_count {
                if strcmp(
                    (files[i as usize].filename).as_ptr(),
                    (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                ) == 0 as core::ffi::c_int
                {
                    if strcmp(
                        (files[i as usize].owner).as_ptr(),
                        ((*current_user).name).as_ptr(),
                    ) == 0 as core::ffi::c_int
                        || (*current_user).permission_level >= 9 as core::ffi::c_int
                    {
                        let mut j: core::ffi::c_int = i;
                        while j < file_count - 1 as core::ffi::c_int {
                            files[j as usize] = files[(j + 1 as core::ffi::c_int) as usize];
                            j += 1;
                        }
                        file_count -= 1;
                        printf(
                            b"File '%s' deleted\n\0" as *const u8 as *const core::ffi::c_char,
                            (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                        );
                        return;
                    } else {
                        printf(
                            b"Error: Permission denied\n\0" as *const u8
                                as *const core::ffi::c_char,
                        );
                        return;
                    }
                }
                i += 1;
            }
            printf(
                b"Error: File '%s' not found\n\0" as *const u8 as *const core::ffi::c_char,
                (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn cmd_listfiles() {
            if file_count == 0 as core::ffi::c_int {
                printf(b"No files\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            printf(b"Files:\n\0" as *const u8 as *const core::ffi::c_char);
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < file_count {
                printf(
                    b"  %s (owner: %s, perm: %d)\n\0" as *const u8 as *const core::ffi::c_char,
                    (files[i as usize].filename).as_ptr(),
                    (files[i as usize].owner).as_ptr(),
                    files[i as usize].permissions,
                );
                i += 1;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn cmd_set(
            args: *mut [core::ffi::c_char; 64],
            arg_count: core::ffi::c_int,
        ) {
            if arg_count < 2 as core::ffi::c_int {
                printf(b"Usage: set <name> <value>\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < variable_count {
                if strcmp(
                    (variables[i as usize].name).as_ptr(),
                    (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                ) == 0 as core::ffi::c_int
                {
                    strcpy(
                        (variables[i as usize].value).as_mut_ptr(),
                        (*args.offset(1 as core::ffi::c_int as isize)).as_ptr(),
                    );
                    printf(
                        b"Variable '%s' updated\n\0" as *const u8 as *const core::ffi::c_char,
                        (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                    );
                    return;
                }
                i += 1;
            }
            if variable_count >= MAX_VARIABLES {
                printf(
                    b"Error: Maximum variables reached\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return;
            }
            strcpy(
                (variables[variable_count as usize].name).as_mut_ptr(),
                (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
            );
            strcpy(
                (variables[variable_count as usize].value).as_mut_ptr(),
                (*args.offset(1 as core::ffi::c_int as isize)).as_ptr(),
            );
            variable_count += 1;
            printf(
                b"Variable '%s' set\n\0" as *const u8 as *const core::ffi::c_char,
                (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn cmd_get(
            args: *mut [core::ffi::c_char; 64],
            arg_count: core::ffi::c_int,
        ) {
            if arg_count < 1 as core::ffi::c_int {
                printf(b"Usage: get <name>\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < variable_count {
                if strcmp(
                    (variables[i as usize].name).as_ptr(),
                    (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                ) == 0 as core::ffi::c_int
                {
                    printf(
                        b"%s = %s\n\0" as *const u8 as *const core::ffi::c_char,
                        (variables[i as usize].name).as_ptr(),
                        (variables[i as usize].value).as_ptr(),
                    );
                    return;
                }
                i += 1;
            }
            printf(
                b"Error: Variable '%s' not found\n\0" as *const u8 as *const core::ffi::c_char,
                (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn cmd_unset(
            args: *mut [core::ffi::c_char; 64],
            arg_count: core::ffi::c_int,
        ) {
            if arg_count < 1 as core::ffi::c_int {
                printf(b"Usage: unset <name>\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < variable_count {
                if strcmp(
                    (variables[i as usize].name).as_ptr(),
                    (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                ) == 0 as core::ffi::c_int
                {
                    let mut j: core::ffi::c_int = i;
                    while j < variable_count - 1 as core::ffi::c_int {
                        variables[j as usize] = variables[(j + 1 as core::ffi::c_int) as usize];
                        j += 1;
                    }
                    variable_count -= 1;
                    printf(
                        b"Variable '%s' unset\n\0" as *const u8 as *const core::ffi::c_char,
                        (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                    );
                    return;
                }
                i += 1;
            }
            printf(
                b"Error: Variable '%s' not found\n\0" as *const u8 as *const core::ffi::c_char,
                (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn cmd_listvars() {
            if variable_count == 0 as core::ffi::c_int {
                printf(b"No variables set\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            printf(b"Variables:\n\0" as *const u8 as *const core::ffi::c_char);
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < variable_count {
                printf(
                    b"  %s = %s\n\0" as *const u8 as *const core::ffi::c_char,
                    (variables[i as usize].name).as_ptr(),
                    (variables[i as usize].value).as_ptr(),
                );
                i += 1;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn cmd_compare(
            args: *mut [core::ffi::c_char; 64],
            arg_count: core::ffi::c_int,
        ) {
            if arg_count < 2 as core::ffi::c_int {
                printf(
                    b"Usage: compare <string1> <string2>\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return;
            }
            let result: core::ffi::c_int = strcmp(
                (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                (*args.offset(1 as core::ffi::c_int as isize)).as_ptr(),
            );
            printf(
                b"strcmp('%s', '%s') = %d\n\0" as *const u8 as *const core::ffi::c_char,
                (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                (*args.offset(1 as core::ffi::c_int as isize)).as_ptr(),
                result,
            );
            if result == 0 as core::ffi::c_int {
                printf(b"Strings are equal\n\0" as *const u8 as *const core::ffi::c_char);
            } else if result < 0 as core::ffi::c_int {
                printf(
                    b"'%s' < '%s'\n\0" as *const u8 as *const core::ffi::c_char,
                    (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                    (*args.offset(1 as core::ffi::c_int as isize)).as_ptr(),
                );
            } else {
                printf(
                    b"'%s' > '%s'\n\0" as *const u8 as *const core::ffi::c_char,
                    (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                    (*args.offset(1 as core::ffi::c_int as isize)).as_ptr(),
                );
            };
        }
        #[no_mangle]
        pub unsafe extern "C" fn cmd_compareN(
            args: *mut [core::ffi::c_char; 64],
            arg_count: core::ffi::c_int,
        ) {
            if arg_count < 3 as core::ffi::c_int {
                printf(
                    b"Usage: compareN <string1> <string2> <n>\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return;
            }
            let n: core::ffi::c_int = atoi((*args.offset(2 as core::ffi::c_int as isize)).as_ptr());
            let result: core::ffi::c_int = strncmp(
                (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                (*args.offset(1 as core::ffi::c_int as isize)).as_ptr(),
                n as size_t,
            );
            printf(
                b"strncmp('%s', '%s', %d) = %d\n\0" as *const u8 as *const core::ffi::c_char,
                (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                (*args.offset(1 as core::ffi::c_int as isize)).as_ptr(),
                n,
                result,
            );
            if result == 0 as core::ffi::c_int {
                printf(
                    b"First %d characters are equal\n\0" as *const u8 as *const core::ffi::c_char,
                    n,
                );
            } else if result < 0 as core::ffi::c_int {
                printf(
                    b"'%s' < '%s' (first %d chars)\n\0" as *const u8 as *const core::ffi::c_char,
                    (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                    (*args.offset(1 as core::ffi::c_int as isize)).as_ptr(),
                    n,
                );
            } else {
                printf(
                    b"'%s' > '%s' (first %d chars)\n\0" as *const u8 as *const core::ffi::c_char,
                    (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                    (*args.offset(1 as core::ffi::c_int as isize)).as_ptr(),
                    n,
                );
            };
        }
        #[no_mangle]
        pub unsafe extern "C" fn cmd_startswith(
            args: *mut [core::ffi::c_char; 64],
            arg_count: core::ffi::c_int,
        ) {
            if arg_count < 2 as core::ffi::c_int {
                printf(
                    b"Usage: startswith <string> <prefix>\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return;
            }
            let prefix_len: size_t =
                strlen((*args.offset(1 as core::ffi::c_int as isize)).as_ptr());
            if strncmp(
                (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                (*args.offset(1 as core::ffi::c_int as isize)).as_ptr(),
                prefix_len,
            ) == 0 as core::ffi::c_int
            {
                printf(
                    b"'%s' starts with '%s'\n\0" as *const u8 as *const core::ffi::c_char,
                    (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                    (*args.offset(1 as core::ffi::c_int as isize)).as_ptr(),
                );
            } else {
                printf(
                    b"'%s' does not start with '%s'\n\0" as *const u8 as *const core::ffi::c_char,
                    (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                    (*args.offset(1 as core::ffi::c_int as isize)).as_ptr(),
                );
            };
        }
        #[no_mangle]
        pub unsafe extern "C" fn cmd_match(
            args: *mut [core::ffi::c_char; 64],
            arg_count: core::ffi::c_int,
        ) {
            if arg_count < 2 as core::ffi::c_int {
                printf(
                    b"Usage: match <pattern> <string1> [string2] ...\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return;
            }
            printf(
                b"Matching pattern '%s':\n\0" as *const u8 as *const core::ffi::c_char,
                (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
            );
            let mut matches: core::ffi::c_int = 0 as core::ffi::c_int;
            let mut i: core::ffi::c_int = 1 as core::ffi::c_int;
            while i < arg_count {
                if strcmp(
                    (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                    (*args.offset(i as isize)).as_ptr(),
                ) == 0 as core::ffi::c_int
                {
                    printf(
                        b"  '%s' - EXACT MATCH\n\0" as *const u8 as *const core::ffi::c_char,
                        (*args.offset(i as isize)).as_ptr(),
                    );
                    matches += 1;
                } else if !(strstr(
                    (*args.offset(i as isize)).as_ptr(),
                    (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                ))
                .is_null()
                {
                    printf(
                        b"  '%s' - contains pattern\n\0" as *const u8 as *const core::ffi::c_char,
                        (*args.offset(i as isize)).as_ptr(),
                    );
                    matches += 1;
                } else {
                    printf(
                        b"  '%s' - no match\n\0" as *const u8 as *const core::ffi::c_char,
                        (*args.offset(i as isize)).as_ptr(),
                    );
                }
                i += 1;
            }
            printf(
                b"Total matches: %d\n\0" as *const u8 as *const core::ffi::c_char,
                matches,
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn cmd_help() {
            printf(
                b"\n=== Command Interpreter Help ===\n\0" as *const u8 as *const core::ffi::c_char,
            );
            printf(b"User Management:\n\0" as *const u8 as *const core::ffi::c_char);
            printf(
                b"  adduser <user> <pass> [level] - Add new user\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(
                b"  login <user> <pass>            - Login as user\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(
                b"  logout                         - Logout current user\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(
                b"  whoami                         - Show current user\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(
                b"  listusers                      - List all users\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(b"\nFile Management:\n\0" as *const u8 as *const core::ffi::c_char);
            printf(
                b"  createfile <name> [content]    - Create file\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(
                b"  readfile <name>                - Read file\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(
                b"  writefile <name> <content>     - Write to file\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(
                b"  deletefile <name>              - Delete file\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(
                b"  listfiles                      - List all files\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(b"\nVariable Management:\n\0" as *const u8 as *const core::ffi::c_char);
            printf(
                b"  set <name> <value>             - Set variable\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(
                b"  get <name>                     - Get variable\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(
                b"  unset <name>                   - Unset variable\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(
                b"  listvars                       - List all variables\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(b"\nString Operations:\n\0" as *const u8 as *const core::ffi::c_char);
            printf(
                b"  compare <str1> <str2>          - Compare strings\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(
                b"  compareN <str1> <str2> <n>     - Compare first N chars\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(
                b"  startswith <str> <prefix>      - Check if starts with\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(
                b"  match <pattern> <str> ...      - Match pattern\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(b"\nSystem:\n\0" as *const u8 as *const core::ffi::c_char);
            printf(
                b"  debug [on|off]                 - Toggle debug mode\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(
                b"  verbose [on|off]               - Toggle verbose mode\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(
                b"  status                         - Show system status\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(
                b"  time                           - Show current time\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(
                b"  help                           - Show this help\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(
                b"  exit                           - Exit program\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn cmd_debug(
            args: *mut [core::ffi::c_char; 64],
            arg_count: core::ffi::c_int,
        ) {
            if arg_count < 1 as core::ffi::c_int {
                printf(
                    b"Debug mode: %s\n\0" as *const u8 as *const core::ffi::c_char,
                    if debug_mode != 0 {
                        b"ON\0" as *const u8 as *const core::ffi::c_char
                    } else {
                        b"OFF\0" as *const u8 as *const core::ffi::c_char
                    },
                );
                return;
            }
            if strcmp(
                (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                b"on\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
                debug_mode = 1 as core::ffi::c_int;
                printf(b"Debug mode enabled\n\0" as *const u8 as *const core::ffi::c_char);
            } else if strcmp(
                (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                b"off\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
                debug_mode = 0 as core::ffi::c_int;
                printf(b"Debug mode disabled\n\0" as *const u8 as *const core::ffi::c_char);
            } else {
                printf(b"Usage: debug [on|off]\n\0" as *const u8 as *const core::ffi::c_char);
            };
        }
        #[no_mangle]
        pub unsafe extern "C" fn cmd_verbose(
            args: *mut [core::ffi::c_char; 64],
            arg_count: core::ffi::c_int,
        ) {
            if arg_count < 1 as core::ffi::c_int {
                printf(
                    b"Verbose mode: %s\n\0" as *const u8 as *const core::ffi::c_char,
                    if verbose_mode != 0 {
                        b"ON\0" as *const u8 as *const core::ffi::c_char
                    } else {
                        b"OFF\0" as *const u8 as *const core::ffi::c_char
                    },
                );
                return;
            }
            if strcmp(
                (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                b"on\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
                verbose_mode = 1 as core::ffi::c_int;
                printf(b"Verbose mode enabled\n\0" as *const u8 as *const core::ffi::c_char);
            } else if strcmp(
                (*args.offset(0 as core::ffi::c_int as isize)).as_ptr(),
                b"off\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
                verbose_mode = 0 as core::ffi::c_int;
                printf(b"Verbose mode disabled\n\0" as *const u8 as *const core::ffi::c_char);
            } else {
                printf(b"Usage: verbose [on|off]\n\0" as *const u8 as *const core::ffi::c_char);
            };
        }
        #[no_mangle]
        pub unsafe extern "C" fn cmd_status() {
            printf(b"\n=== System Status ===\n\0" as *const u8 as *const core::ffi::c_char);
            printf(
                b"Users: %d/%d\n\0" as *const u8 as *const core::ffi::c_char,
                user_count,
                MAX_USERS,
            );
            printf(
                b"Files: %d/%d\n\0" as *const u8 as *const core::ffi::c_char,
                file_count,
                MAX_FILES,
            );
            printf(
                b"Variables: %d/%d\n\0" as *const u8 as *const core::ffi::c_char,
                variable_count,
                MAX_VARIABLES,
            );
            printf(
                b"Current user: %s\n\0" as *const u8 as *const core::ffi::c_char,
                if !current_user.is_null() && (*current_user).logged_in != 0 {
                    ((*current_user).name).as_ptr() as *const core::ffi::c_char
                } else {
                    b"none\0" as *const u8 as *const core::ffi::c_char
                },
            );
            printf(
                b"Debug mode: %s\n\0" as *const u8 as *const core::ffi::c_char,
                if debug_mode != 0 {
                    b"ON\0" as *const u8 as *const core::ffi::c_char
                } else {
                    b"OFF\0" as *const u8 as *const core::ffi::c_char
                },
            );
            printf(
                b"Verbose mode: %s\n\0" as *const u8 as *const core::ffi::c_char,
                if verbose_mode != 0 {
                    b"ON\0" as *const u8 as *const core::ffi::c_char
                } else {
                    b"OFF\0" as *const u8 as *const core::ffi::c_char
                },
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn cmd_time() {
            let mut now: time_t = time(std::ptr::null_mut::<time_t>());
            printf(
                b"Current time: %s\0" as *const u8 as *const core::ffi::c_char,
                ctime(&mut now),
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn process_command(input: *const core::ffi::c_char) {
            let mut command: [core::ffi::c_char; 64] = [0; 64];
            let mut args: [[core::ffi::c_char; 64]; 10] = [[0; 64]; 10];
            let mut arg_count: core::ffi::c_int = 0 as core::ffi::c_int;
            parse_command(
                input,
                command.as_mut_ptr(),
                args.as_mut_ptr(),
                &mut arg_count,
            );
            if strlen(command.as_ptr()) == 0 as size_t {
                return;
            }
            if debug_mode != 0 {
                printf(
                    b"[DEBUG] Command: '%s', Args: %d\n\0" as *const u8 as *const core::ffi::c_char,
                    command.as_ptr(),
                    arg_count,
                );
            }
            if strcmp(
                command.as_ptr(),
                b"adduser\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
                cmd_adduser(args.as_mut_ptr(), arg_count);
            } else if strcmp(
                command.as_ptr(),
                b"login\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
                cmd_login(args.as_mut_ptr(), arg_count);
            } else if strcmp(
                command.as_ptr(),
                b"logout\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
                cmd_logout();
            } else if strcmp(
                command.as_ptr(),
                b"whoami\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
                cmd_whoami();
            } else if strcmp(
                command.as_ptr(),
                b"listusers\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
                || strcmp(
                    command.as_ptr(),
                    b"users\0" as *const u8 as *const core::ffi::c_char,
                ) == 0 as core::ffi::c_int
            {
                cmd_listusers();
            } else if strcmp(
                command.as_ptr(),
                b"createfile\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
                || strcmp(
                    command.as_ptr(),
                    b"touch\0" as *const u8 as *const core::ffi::c_char,
                ) == 0 as core::ffi::c_int
            {
                cmd_createfile(args.as_mut_ptr(), arg_count);
            } else if strcmp(
                command.as_ptr(),
                b"readfile\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
                || strcmp(
                    command.as_ptr(),
                    b"cat\0" as *const u8 as *const core::ffi::c_char,
                ) == 0 as core::ffi::c_int
            {
                cmd_readfile(args.as_mut_ptr(), arg_count);
            } else if strcmp(
                command.as_ptr(),
                b"writefile\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
                || strcmp(
                    command.as_ptr(),
                    b"write\0" as *const u8 as *const core::ffi::c_char,
                ) == 0 as core::ffi::c_int
            {
                cmd_writefile(args.as_mut_ptr(), arg_count);
            } else if strcmp(
                command.as_ptr(),
                b"deletefile\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
                || strcmp(
                    command.as_ptr(),
                    b"rm\0" as *const u8 as *const core::ffi::c_char,
                ) == 0 as core::ffi::c_int
            {
                cmd_deletefile(args.as_mut_ptr(), arg_count);
            } else if strcmp(
                command.as_ptr(),
                b"listfiles\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
                || strcmp(
                    command.as_ptr(),
                    b"ls\0" as *const u8 as *const core::ffi::c_char,
                ) == 0 as core::ffi::c_int
            {
                cmd_listfiles();
            } else if strcmp(
                command.as_ptr(),
                b"set\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
                cmd_set(args.as_mut_ptr(), arg_count);
            } else if strcmp(
                command.as_ptr(),
                b"get\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
                cmd_get(args.as_mut_ptr(), arg_count);
            } else if strcmp(
                command.as_ptr(),
                b"unset\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
                cmd_unset(args.as_mut_ptr(), arg_count);
            } else if strcmp(
                command.as_ptr(),
                b"listvars\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
                || strcmp(
                    command.as_ptr(),
                    b"vars\0" as *const u8 as *const core::ffi::c_char,
                ) == 0 as core::ffi::c_int
            {
                cmd_listvars();
            } else if strcmp(
                command.as_ptr(),
                b"compare\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
                || strcmp(
                    command.as_ptr(),
                    b"cmp\0" as *const u8 as *const core::ffi::c_char,
                ) == 0 as core::ffi::c_int
            {
                cmd_compare(args.as_mut_ptr(), arg_count);
            } else if strcmp(
                command.as_ptr(),
                b"compareN\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
                || strcmp(
                    command.as_ptr(),
                    b"cmpn\0" as *const u8 as *const core::ffi::c_char,
                ) == 0 as core::ffi::c_int
            {
                cmd_compareN(args.as_mut_ptr(), arg_count);
            } else if strcmp(
                command.as_ptr(),
                b"startswith\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
                cmd_startswith(args.as_mut_ptr(), arg_count);
            } else if strcmp(
                command.as_ptr(),
                b"match\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
                cmd_match(args.as_mut_ptr(), arg_count);
            } else if strcmp(
                command.as_ptr(),
                b"debug\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
                cmd_debug(args.as_mut_ptr(), arg_count);
            } else if strcmp(
                command.as_ptr(),
                b"verbose\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
                cmd_verbose(args.as_mut_ptr(), arg_count);
            } else if strcmp(
                command.as_ptr(),
                b"status\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
                cmd_status();
            } else if strcmp(
                command.as_ptr(),
                b"time\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
            {
                cmd_time();
            } else if strcmp(
                command.as_ptr(),
                b"help\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
                || strcmp(
                    command.as_ptr(),
                    b"?\0" as *const u8 as *const core::ffi::c_char,
                ) == 0 as core::ffi::c_int
            {
                cmd_help();
            } else if strcmp(
                command.as_ptr(),
                b"exit\0" as *const u8 as *const core::ffi::c_char,
            ) == 0 as core::ffi::c_int
                || strcmp(
                    command.as_ptr(),
                    b"quit\0" as *const u8 as *const core::ffi::c_char,
                ) == 0 as core::ffi::c_int
            {
                printf(b"Goodbye!\n\0" as *const u8 as *const core::ffi::c_char);
                exit(0 as core::ffi::c_int);
            } else if strncmp(
                command.as_ptr(),
                b"add\0" as *const u8 as *const core::ffi::c_char,
                3 as size_t,
            ) == 0 as core::ffi::c_int
            {
                printf(b"Did you mean 'adduser'?\n\0" as *const u8 as *const core::ffi::c_char);
            } else if strncmp(
                command.as_ptr(),
                b"log\0" as *const u8 as *const core::ffi::c_char,
                3 as size_t,
            ) == 0 as core::ffi::c_int
            {
                printf(
                    b"Did you mean 'login' or 'logout'?\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
            } else if strncmp(
                command.as_ptr(),
                b"list\0" as *const u8 as *const core::ffi::c_char,
                4 as size_t,
            ) == 0 as core::ffi::c_int
            {
                printf(
                    b"Did you mean 'listusers', 'listfiles', or 'listvars'?\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
            } else if strncmp(
                command.as_ptr(),
                b"create\0" as *const u8 as *const core::ffi::c_char,
                6 as size_t,
            ) == 0 as core::ffi::c_int
            {
                printf(b"Did you mean 'createfile'?\n\0" as *const u8 as *const core::ffi::c_char);
            } else if strncmp(
                command.as_ptr(),
                b"read\0" as *const u8 as *const core::ffi::c_char,
                4 as size_t,
            ) == 0 as core::ffi::c_int
            {
                printf(b"Did you mean 'readfile'?\n\0" as *const u8 as *const core::ffi::c_char);
            } else if strncmp(
                command.as_ptr(),
                b"write\0" as *const u8 as *const core::ffi::c_char,
                5 as size_t,
            ) == 0 as core::ffi::c_int
            {
                printf(b"Did you mean 'writefile'?\n\0" as *const u8 as *const core::ffi::c_char);
            } else if strncmp(
                command.as_ptr(),
                b"delete\0" as *const u8 as *const core::ffi::c_char,
                6 as size_t,
            ) == 0 as core::ffi::c_int
            {
                printf(b"Did you mean 'deletefile'?\n\0" as *const u8 as *const core::ffi::c_char);
            } else {
                printf(
                    b"Unknown command: '%s'. Type 'help' for available commands.\n\0" as *const u8
                        as *const core::ffi::c_char,
                    command.as_ptr(),
                );
            };
        }
        unsafe fn main_0() -> core::ffi::c_int {
            printf(
                b"|----------------------------------------|\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(
                b"|   COMMAND INTERPRETER                  |\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(
                b"|   strcmp/strncmp demonstration         |\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(
                b"|----------------------------------------|\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(
                b"Type 'help' for available commands\n\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            let mut input: [core::ffi::c_char; 256] = [0; 256];
            loop {
                printf(b"> \0" as *const u8 as *const core::ffi::c_char);
                if (fgets(input.as_mut_ptr(), MAX_INPUT, stdin)).is_null() {
                    break;
                }
                input[strcspn(
                    input.as_ptr(),
                    b"\n\0" as *const u8 as *const core::ffi::c_char,
                ) as usize] = 0 as core::ffi::c_char;
                if verbose_mode != 0 {
                    printf(
                        b"[VERBOSE] Processing: '%s'\n\0" as *const u8 as *const core::ffi::c_char,
                        input.as_ptr(),
                    );
                }
                process_command(input.as_ptr());
            }
            0 as core::ffi::c_int
        }
        pub fn main() {
            unsafe { ::std::process::exit(main_0() as i32) }
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case("strcmp", SOURCE);
}
