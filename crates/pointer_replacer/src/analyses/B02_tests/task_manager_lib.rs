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
        use crate::src::logger::finalize_logger;
        use crate::src::logger::initialize_logger;
        use crate::src::task_manager::add_task;
        use crate::src::task_manager::create_task_manager;
        use crate::src::task_manager::destroy_task_manager;
        use crate::src::task_manager::print_tasks;
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
            fn malloc(__size: size_t) -> *mut core::ffi::c_void;
            fn free(__ptr: *mut core::ffi::c_void);
            fn strncpy(
                __dest: *mut core::ffi::c_char,
                __src: *const core::ffi::c_char,
                __n: size_t,
            ) -> *mut core::ffi::c_char;
            fn strchr(
                __s: *const core::ffi::c_char,
                __c: core::ffi::c_int,
            ) -> *mut core::ffi::c_char;
            fn strlen(__s: *const core::ffi::c_char) -> size_t;
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
        pub struct Task {
            pub description: [core::ffi::c_char; 256],
            pub priority: core::ffi::c_int,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for Task {}
        #[automatically_derived]
        impl ::core::clone::Clone for Task {
            #[inline]
            fn clone(&self) -> Task {
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 256]>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                *self
            }
        }
        #[repr(C)]
        pub struct TaskManager {
            pub tasks: *mut Task,
            pub max_tasks: core::ffi::c_int,
            pub task_count: core::ffi::c_int,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for TaskManager {}
        #[automatically_derived]
        impl ::core::clone::Clone for TaskManager {
            #[inline]
            fn clone(&self) -> TaskManager {
                let _: ::core::clone::AssertParamIsClone<*mut Task>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                *self
            }
        }
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const EXIT_FAILURE: core::ffi::c_int = 1 as core::ffi::c_int;
        #[no_mangle]
        pub unsafe extern "C" fn driver(mut tasks: *const core::ffi::c_char) -> core::ffi::c_int {
            let res: core::ffi::c_int = initialize_logger();
            if res != 0 as core::ffi::c_int {
                return EXIT_FAILURE;
            }
            let manager: *mut TaskManager = create_task_manager();
            if manager.is_null() {
                return EXIT_FAILURE;
            }
            let mut priority: core::ffi::c_int = 1 as core::ffi::c_int;
            while *tasks as core::ffi::c_int != '\0' as i32 {
                let mut end: *const core::ffi::c_char = strchr(tasks, '\n' as i32);
                if end.is_null() {
                    end = tasks.add(strlen(tasks));
                }
                let length: size_t = end.offset_from(tasks) as core::ffi::c_long as size_t;
                let task: *mut core::ffi::c_char =
                    malloc(length.wrapping_add(1 as size_t)) as *mut core::ffi::c_char;
                if task.is_null() {
                    fprintf(
                        stderr,
                        b"Error: Failed to allocate memory for task.\n\0" as *const u8
                            as *const core::ffi::c_char,
                    );
                    destroy_task_manager(manager);
                    finalize_logger();
                    return EXIT_FAILURE;
                }
                strncpy(task, tasks, length);
                *task.add(length) = '\0' as i32 as core::ffi::c_char;
                let fresh0 = priority;
                priority += 1;
                add_task(manager, task, fresh0);
                free(task as *mut core::ffi::c_void);
                tasks = if *end as core::ffi::c_int == '\n' as i32 {
                    end.offset(1 as core::ffi::c_int as isize)
                } else {
                    end
                };
            }
            print_tasks(manager);
            destroy_task_manager(manager);
            finalize_logger();
            0 as core::ffi::c_int
        }
    }
    pub mod logger {
        use crate::src::driver::FILE;
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
            fn getenv(__name: *const core::ffi::c_char) -> *mut core::ffi::c_char;
        }
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        static mut log_file: *mut FILE = 0 as *const FILE as *mut FILE;
        #[no_mangle]
        pub unsafe extern "C" fn initialize_logger() -> core::ffi::c_int {
            let log_file_env: *const core::ffi::c_char =
                getenv(b"LOG_FILE\0" as *const u8 as *const core::ffi::c_char);
            let log_file_path: *const core::ffi::c_char = if !log_file_env.is_null() {
                log_file_env
            } else {
                b"default.log\0" as *const u8 as *const core::ffi::c_char
            };
            log_file = fopen(
                log_file_path,
                b"a\0" as *const u8 as *const core::ffi::c_char,
            );
            if log_file.is_null() {
                fprintf(
                    stderr,
                    b"Failed to open log file: %s\n\0" as *const u8 as *const core::ffi::c_char,
                    log_file_path,
                );
                return -(1 as core::ffi::c_int);
            }
            log_info(b"Logger initialized.\0" as *const u8 as *const core::ffi::c_char);
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn log_info(message: *const core::ffi::c_char) {
            if !log_file.is_null() {
                fprintf(
                    log_file,
                    b"[INFO] %s\n\0" as *const u8 as *const core::ffi::c_char,
                    message,
                );
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn log_warning(message: *const core::ffi::c_char) {
            if !log_file.is_null() {
                fprintf(
                    log_file,
                    b"[WARNING] %s\n\0" as *const u8 as *const core::ffi::c_char,
                    message,
                );
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn log_error(message: *const core::ffi::c_char) {
            if !log_file.is_null() {
                fprintf(
                    log_file,
                    b"[ERROR] %s\n\0" as *const u8 as *const core::ffi::c_char,
                    message,
                );
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn finalize_logger() {
            if !log_file.is_null() {
                log_info(b"Logger finalized.\0" as *const u8 as *const core::ffi::c_char);
                fclose(log_file);
            }
        }
    }
    pub mod task_manager {
        use crate::src::driver::size_t;
        use crate::src::driver::Task;
        use crate::src::driver::TaskManager;
        use crate::src::logger::log_error;
        use crate::src::logger::log_info;
        use crate::src::logger::log_warning;
        extern "C" {
            fn printf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
            fn atoi(__nptr: *const core::ffi::c_char) -> core::ffi::c_int;
            fn malloc(__size: size_t) -> *mut core::ffi::c_void;
            fn free(__ptr: *mut core::ffi::c_void);
            fn getenv(__name: *const core::ffi::c_char) -> *mut core::ffi::c_char;
            fn strncpy(
                __dest: *mut core::ffi::c_char,
                __src: *const core::ffi::c_char,
                __n: size_t,
            ) -> *mut core::ffi::c_char;
        }
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        #[no_mangle]
        pub unsafe extern "C" fn create_task_manager() -> *mut TaskManager {
            let manager: *mut TaskManager =
                malloc(::core::mem::size_of::<TaskManager>() as size_t) as *mut TaskManager;
            if manager.is_null() {
                log_error(
                    b"Failed to allocate memory for TaskManager.\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return std::ptr::null_mut::<TaskManager>();
            }
            let max_tasks_env: *const core::ffi::c_char =
                getenv(b"MAX_TASKS\0" as *const u8 as *const core::ffi::c_char);
            (*manager).max_tasks = if !max_tasks_env.is_null() {
                atoi(max_tasks_env)
            } else {
                10 as core::ffi::c_int
            };
            (*manager).task_count = 0 as core::ffi::c_int;
            (*manager).tasks = malloc(
                ((*manager).max_tasks as size_t)
                    .wrapping_mul(::core::mem::size_of::<Task>() as size_t),
            ) as *mut Task;
            if ((*manager).tasks).is_null() {
                log_error(
                    b"Failed to allocate memory for tasks.\0" as *const u8
                        as *const core::ffi::c_char,
                );
                free(manager as *mut core::ffi::c_void);
                return std::ptr::null_mut::<TaskManager>();
            }
            log_info(
                b"TaskManager created successfully.\0" as *const u8 as *const core::ffi::c_char,
            );
            manager
        }
        #[no_mangle]
        pub unsafe extern "C" fn add_task(
            manager: *mut TaskManager,
            description: *const core::ffi::c_char,
            priority: core::ffi::c_int,
        ) {
            if (*manager).task_count >= (*manager).max_tasks {
                log_warning(
                    b"Cannot add task: Maximum task limit reached.\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return;
            }
            let fresh0 = (*manager).task_count;
            (*manager).task_count += 1;
            let task: *mut Task = &mut *((*manager).tasks).offset(fresh0 as isize) as *mut Task;
            strncpy(
                ((*task).description).as_mut_ptr(),
                description,
                (::core::mem::size_of::<[core::ffi::c_char; 256]>() as size_t)
                    .wrapping_sub(1 as size_t),
            );
            (*task).description
                [::core::mem::size_of::<[core::ffi::c_char; 256]>().wrapping_sub(1_usize)] =
                '\0' as i32 as core::ffi::c_char;
            (*task).priority = priority;
            log_info(b"Task added successfully.\0" as *const u8 as *const core::ffi::c_char);
        }
        #[no_mangle]
        pub unsafe extern "C" fn print_tasks(manager: *const TaskManager) {
            printf(b"Tasks:\n\0" as *const u8 as *const core::ffi::c_char);
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < (*manager).task_count {
                printf(
                    b"  [%d] %s (Priority: %d)\n\0" as *const u8 as *const core::ffi::c_char,
                    i + 1 as core::ffi::c_int,
                    ((*((*manager).tasks).offset(i as isize)).description).as_ptr(),
                    (*((*manager).tasks).offset(i as isize)).priority,
                );
                i += 1;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn destroy_task_manager(manager: *mut TaskManager) {
            free((*manager).tasks as *mut core::ffi::c_void);
            free(manager as *mut core::ffi::c_void);
            log_info(
                b"TaskManager destroyed successfully.\0" as *const u8 as *const core::ffi::c_char,
            );
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates(
        "task_manager_lib",
        SOURCE,
        &["create_task_manager#manager"],
        &["add_task#task"],
    );
}
