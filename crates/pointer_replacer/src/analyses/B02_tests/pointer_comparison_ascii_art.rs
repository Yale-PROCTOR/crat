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
    pub mod main {
        use crate::src::scene::scene_add_shape;
        use crate::src::scene::scene_create;
        use crate::src::scene::scene_destroy;
        use crate::src::scene::scene_equals;
        use crate::src::scene::scene_list_shapes;
        use crate::src::scene::scene_load;
        use crate::src::scene::scene_print;
        use crate::src::scene::scene_remove_shape;
        use crate::src::scene::scene_save;
        use crate::src::shape::shape_equals;
        use crate::src::shape::shape_get;
        use crate::src::shape::shape_manager_cleanup;
        use crate::src::shape::shape_manager_init;
        use crate::src::shape::shape_print;
        use crate::src::shape::shape_type_name;
        extern "C" {
            pub type _IO_wide_data;
            pub type _IO_codecvt;
            pub type _IO_marker;
            static mut stdin: *mut FILE;
            fn printf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
            fn scanf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
            fn sscanf(
                __s: *const core::ffi::c_char,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn getchar() -> core::ffi::c_int;
            fn fgets(
                __s: *mut core::ffi::c_char,
                __n: core::ffi::c_int,
                __stream: *mut FILE,
            ) -> *mut core::ffi::c_char;
            fn strcspn(
                __s: *const core::ffi::c_char,
                __reject: *const core::ffi::c_char,
            ) -> core::ffi::c_ulong;
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
        pub type shape_type_t = core::ffi::c_uint;
        pub const SHAPE_COUNT: shape_type_t = 10;
        pub const SHAPE_RAINBOW: shape_type_t = 9;
        pub const SHAPE_HEART: shape_type_t = 8;
        pub const SHAPE_STAR: shape_type_t = 7;
        pub const SHAPE_CAR: shape_type_t = 6;
        pub const SHAPE_FLOWER: shape_type_t = 5;
        pub const SHAPE_CLOUD: shape_type_t = 4;
        pub const SHAPE_SUN: shape_type_t = 3;
        pub const SHAPE_HOUSE: shape_type_t = 2;
        pub const SHAPE_TRACTOR: shape_type_t = 1;
        pub const SHAPE_TREE: shape_type_t = 0;
        #[repr(C)]
        pub struct shape_t {
            pub type_0: shape_type_t,
            pub name: [core::ffi::c_char; 32],
            pub art: [[core::ffi::c_char; 80]; 30],
            pub width: core::ffi::c_int,
            pub height: core::ffi::c_int,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for shape_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for shape_t {
            #[inline]
            fn clone(&self) -> shape_t {
                let _: ::core::clone::AssertParamIsClone<shape_type_t>;
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 32]>;
                let _: ::core::clone::AssertParamIsClone<[[core::ffi::c_char; 80]; 30]>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                *self
            }
        }
        #[repr(C)]
        pub struct scene_t {
            pub name: [core::ffi::c_char; 64],
            pub shapes: [*mut shape_t; 50],
            pub shape_count: core::ffi::c_int,
        }
        #[automatically_derived]
        impl ::core::marker::Copy for scene_t {}
        #[automatically_derived]
        impl ::core::clone::Clone for scene_t {
            #[inline]
            fn clone(&self) -> scene_t {
                let _: ::core::clone::AssertParamIsClone<[core::ffi::c_char; 64]>;
                let _: ::core::clone::AssertParamIsClone<[*mut shape_t; 50]>;
                let _: ::core::clone::AssertParamIsClone<core::ffi::c_int>;
                *self
            }
        }
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const MAX_SCENE_NAME: core::ffi::c_int = 64 as core::ffi::c_int;
        pub const MAX_SCENES: core::ffi::c_int = 10 as core::ffi::c_int;
        static mut scenes: [*mut scene_t; 10] = [
            0 as *const scene_t as *mut scene_t,
            0 as *const scene_t as *mut scene_t,
            0 as *const scene_t as *mut scene_t,
            0 as *const scene_t as *mut scene_t,
            0 as *const scene_t as *mut scene_t,
            0 as *const scene_t as *mut scene_t,
            0 as *const scene_t as *mut scene_t,
            0 as *const scene_t as *mut scene_t,
            0 as *const scene_t as *mut scene_t,
            0 as *const scene_t as *mut scene_t,
        ];
        static mut scene_count: core::ffi::c_int = 0 as core::ffi::c_int;
        #[no_mangle]
        pub unsafe extern "C" fn print_menu() {
            printf(b"\n\0" as *const u8 as *const core::ffi::c_char);
            printf(
                b"=========================================\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(b"  ASCII ART DRAWING APPLICATION\n\0" as *const u8 as *const core::ffi::c_char);
            printf(
                b"=========================================\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(b"1. View all available shapes\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"2. Create new scene\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"3. Add shape to scene\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"4. Remove shape from scene\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"5. View scene\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"6. List all scenes\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"7. Save scene\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"8. Load scene\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"9. Compare two shapes\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"10. Compare two scenes\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"11. Delete scene\n\0" as *const u8 as *const core::ffi::c_char);
            printf(b"12. Exit\n\0" as *const u8 as *const core::ffi::c_char);
            printf(
                b"=========================================\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(b"Choice: \0" as *const u8 as *const core::ffi::c_char);
        }
        #[no_mangle]
        pub unsafe extern "C" fn view_all_shapes() {
            printf(b"\n=== Available Shapes ===\n\0" as *const u8 as *const core::ffi::c_char);
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < SHAPE_COUNT as core::ffi::c_int {
                printf(
                    b"\n%d. \0" as *const u8 as *const core::ffi::c_char,
                    i + 1 as core::ffi::c_int,
                );
                shape_print(shape_get(i as shape_type_t));
                i += 1;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn create_new_scene() {
            if scene_count >= MAX_SCENES {
                printf(
                    b"Error: Maximum scenes reached\n\0" as *const u8 as *const core::ffi::c_char,
                );
                return;
            }
            let mut name: [core::ffi::c_char; 64] = [0; 64];
            printf(b"Enter scene name: \0" as *const u8 as *const core::ffi::c_char);
            if (fgets(name.as_mut_ptr(), MAX_SCENE_NAME, stdin)).is_null() {
                return;
            }
            name[strcspn(
                name.as_ptr(),
                b"\n\0" as *const u8 as *const core::ffi::c_char,
            ) as usize] = 0 as core::ffi::c_char;
            scenes[scene_count as usize] = scene_create(name.as_ptr());
            if !(scenes[scene_count as usize]).is_null() {
                printf(
                    b"Scene '%s' created (index %d)\n\0" as *const u8 as *const core::ffi::c_char,
                    name.as_ptr(),
                    scene_count,
                );
                scene_count += 1;
            } else {
                printf(b"Error creating scene\n\0" as *const u8 as *const core::ffi::c_char);
            };
        }
        #[no_mangle]
        pub unsafe extern "C" fn add_shape_to_scene() {
            if scene_count == 0 as core::ffi::c_int {
                printf(
                    b"No scenes available. Create a scene first.\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return;
            }
            printf(
                b"Select scene (0-%d): \0" as *const u8 as *const core::ffi::c_char,
                scene_count - 1 as core::ffi::c_int,
            );
            let mut scene_idx: core::ffi::c_int = 0;
            if scanf(
                b"%d\0" as *const u8 as *const core::ffi::c_char,
                &mut scene_idx as *mut core::ffi::c_int,
            ) != 1 as core::ffi::c_int
            {
                printf(b"Invalid input\n\0" as *const u8 as *const core::ffi::c_char);
                while getchar() != '\n' as i32 {}
                return;
            }
            while getchar() != '\n' as i32 {}
            if scene_idx < 0 as core::ffi::c_int || scene_idx >= scene_count {
                printf(b"Invalid scene index\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            printf(b"\nSelect shape to add:\n\0" as *const u8 as *const core::ffi::c_char);
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < SHAPE_COUNT as core::ffi::c_int {
                printf(
                    b"%d. %s\n\0" as *const u8 as *const core::ffi::c_char,
                    i,
                    shape_type_name(i as shape_type_t),
                );
                i += 1;
            }
            printf(b"Choice: \0" as *const u8 as *const core::ffi::c_char);
            let mut shape_type: core::ffi::c_int = 0;
            if scanf(
                b"%d\0" as *const u8 as *const core::ffi::c_char,
                &mut shape_type as *mut core::ffi::c_int,
            ) != 1 as core::ffi::c_int
            {
                printf(b"Invalid input\n\0" as *const u8 as *const core::ffi::c_char);
                while getchar() != '\n' as i32 {}
                return;
            }
            while getchar() != '\n' as i32 {}
            if shape_type < 0 as core::ffi::c_int || shape_type >= SHAPE_COUNT as core::ffi::c_int {
                printf(b"Invalid shape type\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            let shape: *mut shape_t = shape_get(shape_type as shape_type_t);
            if scene_add_shape(scenes[scene_idx as usize], shape) == 0 as core::ffi::c_int {
                printf(
                    b"Shape '%s' added to scene (reusing singleton at %p)\n\0" as *const u8
                        as *const core::ffi::c_char,
                    ((*shape).name).as_ptr(),
                    shape as *mut core::ffi::c_void,
                );
            } else {
                printf(b"Error adding shape\n\0" as *const u8 as *const core::ffi::c_char);
            };
        }
        #[no_mangle]
        pub unsafe extern "C" fn remove_shape_from_scene() {
            if scene_count == 0 as core::ffi::c_int {
                printf(b"No scenes available\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            printf(
                b"Select scene (0-%d): \0" as *const u8 as *const core::ffi::c_char,
                scene_count - 1 as core::ffi::c_int,
            );
            let mut scene_idx: core::ffi::c_int = 0;
            if scanf(
                b"%d\0" as *const u8 as *const core::ffi::c_char,
                &mut scene_idx as *mut core::ffi::c_int,
            ) != 1 as core::ffi::c_int
            {
                printf(b"Invalid input\n\0" as *const u8 as *const core::ffi::c_char);
                while getchar() != '\n' as i32 {}
                return;
            }
            while getchar() != '\n' as i32 {}
            if scene_idx < 0 as core::ffi::c_int || scene_idx >= scene_count {
                printf(b"Invalid scene index\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            scene_list_shapes(scenes[scene_idx as usize]);
            if (*scenes[scene_idx as usize]).shape_count == 0 as core::ffi::c_int {
                printf(b"Scene is empty\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            printf(
                b"Select shape to remove (1-%d): \0" as *const u8 as *const core::ffi::c_char,
                (*scenes[scene_idx as usize]).shape_count,
            );
            let mut shape_idx: core::ffi::c_int = 0;
            if scanf(
                b"%d\0" as *const u8 as *const core::ffi::c_char,
                &mut shape_idx as *mut core::ffi::c_int,
            ) != 1 as core::ffi::c_int
            {
                printf(b"Invalid input\n\0" as *const u8 as *const core::ffi::c_char);
                while getchar() != '\n' as i32 {}
                return;
            }
            while getchar() != '\n' as i32 {}
            if scene_remove_shape(
                scenes[scene_idx as usize],
                shape_idx - 1 as core::ffi::c_int,
            ) == 0 as core::ffi::c_int
            {
                printf(b"Shape removed\n\0" as *const u8 as *const core::ffi::c_char);
            } else {
                printf(b"Error removing shape\n\0" as *const u8 as *const core::ffi::c_char);
            };
        }
        #[no_mangle]
        pub unsafe extern "C" fn view_scene() {
            if scene_count == 0 as core::ffi::c_int {
                printf(b"No scenes available\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            printf(
                b"Select scene (0-%d): \0" as *const u8 as *const core::ffi::c_char,
                scene_count - 1 as core::ffi::c_int,
            );
            let mut scene_idx: core::ffi::c_int = 0;
            if scanf(
                b"%d\0" as *const u8 as *const core::ffi::c_char,
                &mut scene_idx as *mut core::ffi::c_int,
            ) != 1 as core::ffi::c_int
            {
                printf(b"Invalid input\n\0" as *const u8 as *const core::ffi::c_char);
                while getchar() != '\n' as i32 {}
                return;
            }
            while getchar() != '\n' as i32 {}
            if scene_idx < 0 as core::ffi::c_int || scene_idx >= scene_count {
                printf(b"Invalid scene index\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            scene_print(scenes[scene_idx as usize]);
        }
        #[no_mangle]
        pub unsafe extern "C" fn list_all_scenes() {
            printf(b"\n=== All Scenes ===\n\0" as *const u8 as *const core::ffi::c_char);
            if scene_count == 0 as core::ffi::c_int {
                printf(b"No scenes created yet\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < scene_count {
                printf(
                    b"%d. %s (%d shapes)\n\0" as *const u8 as *const core::ffi::c_char,
                    i,
                    ((*scenes[i as usize]).name).as_ptr(),
                    (*scenes[i as usize]).shape_count,
                );
                i += 1;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn save_scene_to_file() {
            if scene_count == 0 as core::ffi::c_int {
                printf(b"No scenes available\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            printf(
                b"Select scene (0-%d): \0" as *const u8 as *const core::ffi::c_char,
                scene_count - 1 as core::ffi::c_int,
            );
            let mut scene_idx: core::ffi::c_int = 0;
            if scanf(
                b"%d\0" as *const u8 as *const core::ffi::c_char,
                &mut scene_idx as *mut core::ffi::c_int,
            ) != 1 as core::ffi::c_int
            {
                printf(b"Invalid input\n\0" as *const u8 as *const core::ffi::c_char);
                while getchar() != '\n' as i32 {}
                return;
            }
            while getchar() != '\n' as i32 {}
            if scene_idx < 0 as core::ffi::c_int || scene_idx >= scene_count {
                printf(b"Invalid scene index\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            let mut filename: [core::ffi::c_char; 256] = [0; 256];
            printf(b"Enter filename: \0" as *const u8 as *const core::ffi::c_char);
            if (fgets(
                filename.as_mut_ptr(),
                ::core::mem::size_of::<[core::ffi::c_char; 256]>() as core::ffi::c_int,
                stdin,
            ))
            .is_null()
            {
                return;
            }
            filename[strcspn(
                filename.as_ptr(),
                b"\n\0" as *const u8 as *const core::ffi::c_char,
            ) as usize] = 0 as core::ffi::c_char;
            scene_save(scenes[scene_idx as usize], filename.as_ptr());
        }
        #[no_mangle]
        pub unsafe extern "C" fn load_scene_from_file() {
            if scene_count >= MAX_SCENES {
                printf(
                    b"Error: Maximum scenes reached\n\0" as *const u8 as *const core::ffi::c_char,
                );
                return;
            }
            let mut filename: [core::ffi::c_char; 256] = [0; 256];
            printf(b"Enter filename: \0" as *const u8 as *const core::ffi::c_char);
            if (fgets(
                filename.as_mut_ptr(),
                ::core::mem::size_of::<[core::ffi::c_char; 256]>() as core::ffi::c_int,
                stdin,
            ))
            .is_null()
            {
                return;
            }
            filename[strcspn(
                filename.as_ptr(),
                b"\n\0" as *const u8 as *const core::ffi::c_char,
            ) as usize] = 0 as core::ffi::c_char;
            let scene: *mut scene_t = scene_load(filename.as_ptr());
            if !scene.is_null() {
                let fresh0 = scene_count;
                scene_count += 1;
                scenes[fresh0 as usize] = scene;
                printf(
                    b"Scene loaded (index %d)\n\0" as *const u8 as *const core::ffi::c_char,
                    scene_count - 1 as core::ffi::c_int,
                );
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn compare_shapes() {
            printf(
                b"\nSelect first shape (0-%d):\n\0" as *const u8 as *const core::ffi::c_char,
                SHAPE_COUNT as core::ffi::c_int - 1 as core::ffi::c_int,
            );
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < SHAPE_COUNT as core::ffi::c_int {
                printf(
                    b"%d. %s\n\0" as *const u8 as *const core::ffi::c_char,
                    i,
                    shape_type_name(i as shape_type_t),
                );
                i += 1;
            }
            printf(b"Choice: \0" as *const u8 as *const core::ffi::c_char);
            let mut type1: core::ffi::c_int = 0;
            if scanf(
                b"%d\0" as *const u8 as *const core::ffi::c_char,
                &mut type1 as *mut core::ffi::c_int,
            ) != 1 as core::ffi::c_int
            {
                printf(b"Invalid input\n\0" as *const u8 as *const core::ffi::c_char);
                while getchar() != '\n' as i32 {}
                return;
            }
            while getchar() != '\n' as i32 {}
            printf(
                b"\nSelect second shape (0-%d): \0" as *const u8 as *const core::ffi::c_char,
                SHAPE_COUNT as core::ffi::c_int - 1 as core::ffi::c_int,
            );
            let mut type2: core::ffi::c_int = 0;
            if scanf(
                b"%d\0" as *const u8 as *const core::ffi::c_char,
                &mut type2 as *mut core::ffi::c_int,
            ) != 1 as core::ffi::c_int
            {
                printf(b"Invalid input\n\0" as *const u8 as *const core::ffi::c_char);
                while getchar() != '\n' as i32 {}
                return;
            }
            while getchar() != '\n' as i32 {}
            if type1 < 0 as core::ffi::c_int
                || type1 >= SHAPE_COUNT as core::ffi::c_int
                || type2 < 0 as core::ffi::c_int
                || type2 >= SHAPE_COUNT as core::ffi::c_int
            {
                printf(b"Invalid shape type\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            let s1: *mut shape_t = shape_get(type1 as shape_type_t);
            let s2: *mut shape_t = shape_get(type2 as shape_type_t);
            printf(
                b"\nShape 1: %s (ptr: %p)\n\0" as *const u8 as *const core::ffi::c_char,
                ((*s1).name).as_ptr(),
                s1 as *mut core::ffi::c_void,
            );
            printf(
                b"Shape 2: %s (ptr: %p)\n\0" as *const u8 as *const core::ffi::c_char,
                ((*s2).name).as_ptr(),
                s2 as *mut core::ffi::c_void,
            );
            printf(
                b"Comparison of pointers: %d\n\0" as *const u8 as *const core::ffi::c_char,
                (s1 == s2) as core::ffi::c_int,
            );
            if shape_equals(s1, s2) != 0 {
                printf(
                    b"Result: Shapes are EQUAL (same instance)\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
            } else {
                printf(
                    b"Result: Shapes are NOT EQUAL (different instances)\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
            };
        }
        #[no_mangle]
        pub unsafe extern "C" fn compare_scenes() {
            if scene_count < 2 as core::ffi::c_int {
                printf(
                    b"Need at least 2 scenes to compare\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
                return;
            }
            printf(
                b"Select first scene (0-%d): \0" as *const u8 as *const core::ffi::c_char,
                scene_count - 1 as core::ffi::c_int,
            );
            let mut idx1: core::ffi::c_int = 0;
            if scanf(
                b"%d\0" as *const u8 as *const core::ffi::c_char,
                &mut idx1 as *mut core::ffi::c_int,
            ) != 1 as core::ffi::c_int
            {
                printf(b"Invalid input\n\0" as *const u8 as *const core::ffi::c_char);
                while getchar() != '\n' as i32 {}
                return;
            }
            while getchar() != '\n' as i32 {}
            printf(
                b"Select second scene (0-%d): \0" as *const u8 as *const core::ffi::c_char,
                scene_count - 1 as core::ffi::c_int,
            );
            let mut idx2: core::ffi::c_int = 0;
            if scanf(
                b"%d\0" as *const u8 as *const core::ffi::c_char,
                &mut idx2 as *mut core::ffi::c_int,
            ) != 1 as core::ffi::c_int
            {
                printf(b"Invalid input\n\0" as *const u8 as *const core::ffi::c_char);
                while getchar() != '\n' as i32 {}
                return;
            }
            while getchar() != '\n' as i32 {}
            if idx1 < 0 as core::ffi::c_int
                || idx1 >= scene_count
                || idx2 < 0 as core::ffi::c_int
                || idx2 >= scene_count
            {
                printf(b"Invalid scene index\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            let sc1: *mut scene_t = scenes[idx1 as usize];
            let sc2: *mut scene_t = scenes[idx2 as usize];
            printf(
                b"\nScene 1: %s (%d shapes)\n\0" as *const u8 as *const core::ffi::c_char,
                ((*sc1).name).as_ptr(),
                (*sc1).shape_count,
            );
            scene_list_shapes(sc1);
            printf(
                b"\nScene 2: %s (%d shapes)\n\0" as *const u8 as *const core::ffi::c_char,
                ((*sc2).name).as_ptr(),
                (*sc2).shape_count,
            );
            scene_list_shapes(sc2);
            if scene_equals(sc1, sc2) != 0 {
                printf(
                    b"\nResult: Scenes are EQUAL (1:1 correspondence)\n\0" as *const u8
                        as *const core::ffi::c_char,
                );
            } else {
                printf(
                    b"\nResult: Scenes are NOT EQUAL\n\0" as *const u8 as *const core::ffi::c_char,
                );
            };
        }
        #[no_mangle]
        pub unsafe extern "C" fn delete_scene() {
            if scene_count == 0 as core::ffi::c_int {
                printf(b"No scenes available\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            printf(
                b"Select scene to delete (0-%d): \0" as *const u8 as *const core::ffi::c_char,
                scene_count - 1 as core::ffi::c_int,
            );
            let mut scene_idx: core::ffi::c_int = 0;
            if scanf(
                b"%d\0" as *const u8 as *const core::ffi::c_char,
                &mut scene_idx as *mut core::ffi::c_int,
            ) != 1 as core::ffi::c_int
            {
                printf(b"Invalid input\n\0" as *const u8 as *const core::ffi::c_char);
                while getchar() != '\n' as i32 {}
                return;
            }
            while getchar() != '\n' as i32 {}
            if scene_idx < 0 as core::ffi::c_int || scene_idx >= scene_count {
                printf(b"Invalid scene index\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            scene_destroy(scenes[scene_idx as usize]);
            let mut i: core::ffi::c_int = scene_idx;
            while i < scene_count - 1 as core::ffi::c_int {
                scenes[i as usize] = scenes[(i + 1 as core::ffi::c_int) as usize];
                i += 1;
            }
            scene_count -= 1;
            printf(b"Scene deleted\n\0" as *const u8 as *const core::ffi::c_char);
        }
        unsafe fn main_0() -> core::ffi::c_int {
            printf(b"\xE2\x95\x94\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x97\n\0"
                        as *const u8 as *const core::ffi::c_char);
            printf(
                b"\xE2\x95\x91  ASCII ART DRAWING APPLICATION        \xE2\x95\x91\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(
                b"\xE2\x95\x91  Child-Friendly Shape Editor           \xE2\x95\x91\n\0" as *const u8
                    as *const core::ffi::c_char,
            );
            printf(b"\xE2\x95\x9A\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x90\xE2\x95\x9D\n\0"
                        as *const u8 as *const core::ffi::c_char);
            shape_manager_init();
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
                            view_all_shapes();
                        }
                        2 => {
                            create_new_scene();
                        }
                        3 => {
                            add_shape_to_scene();
                        }
                        4 => {
                            remove_shape_from_scene();
                        }
                        5 => {
                            view_scene();
                        }
                        6 => {
                            list_all_scenes();
                        }
                        7 => {
                            save_scene_to_file();
                        }
                        8 => {
                            load_scene_from_file();
                        }
                        9 => {
                            compare_shapes();
                        }
                        10 => {
                            compare_scenes();
                        }
                        11 => {
                            delete_scene();
                        }
                        12 => {
                            printf(
                                b"\nCleaning up and exiting...\n\0" as *const u8
                                    as *const core::ffi::c_char,
                            );
                            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
                            while i < scene_count {
                                scene_destroy(scenes[i as usize]);
                                i += 1;
                            }
                            shape_manager_cleanup();
                            printf(b"Goodbye!\n\0" as *const u8 as *const core::ffi::c_char);
                            return 0 as core::ffi::c_int;
                        }
                        _ => {
                            printf(b"Invalid choice\n\0" as *const u8 as *const core::ffi::c_char);
                        }
                    }
                }
            }
            let mut i_0: core::ffi::c_int = 0 as core::ffi::c_int;
            while i_0 < scene_count {
                scene_destroy(scenes[i_0 as usize]);
                i_0 += 1;
            }
            shape_manager_cleanup();
            0 as core::ffi::c_int
        }
        pub fn main() {
            unsafe { ::std::process::exit(main_0() as i32) }
        }
    }
    pub mod scene {
        use crate::src::main::scene_t;
        use crate::src::main::shape_t;
        use crate::src::main::shape_type_t;
        use crate::src::main::size_t;
        use crate::src::main::FILE;
        use crate::src::shape::shape_equals;
        use crate::src::shape::shape_get;
        use crate::src::shape::shape_print;
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
            fn printf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
            fn fscanf(
                __stream: *mut FILE,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn fgets(
                __s: *mut core::ffi::c_char,
                __n: core::ffi::c_int,
                __stream: *mut FILE,
            ) -> *mut core::ffi::c_char;
            fn malloc(__size: size_t) -> *mut core::ffi::c_void;
            fn free(__ptr: *mut core::ffi::c_void);
            fn strcpy(
                __dest: *mut core::ffi::c_char,
                __src: *const core::ffi::c_char,
            ) -> *mut core::ffi::c_char;
            fn strncpy(
                __dest: *mut core::ffi::c_char,
                __src: *const core::ffi::c_char,
                __n: size_t,
            ) -> *mut core::ffi::c_char;
            fn strcspn(
                __s: *const core::ffi::c_char,
                __reject: *const core::ffi::c_char,
            ) -> core::ffi::c_ulong;
        }
        pub const SHAPE_COUNT: shape_type_t = 10;
        pub const SHAPE_RAINBOW: shape_type_t = 9;
        pub const SHAPE_HEART: shape_type_t = 8;
        pub const SHAPE_STAR: shape_type_t = 7;
        pub const SHAPE_CAR: shape_type_t = 6;
        pub const SHAPE_FLOWER: shape_type_t = 5;
        pub const SHAPE_CLOUD: shape_type_t = 4;
        pub const SHAPE_SUN: shape_type_t = 3;
        pub const SHAPE_HOUSE: shape_type_t = 2;
        pub const SHAPE_TRACTOR: shape_type_t = 1;
        pub const SHAPE_TREE: shape_type_t = 0;
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        pub const MAX_SHAPES_IN_SCENE: core::ffi::c_int = 50 as core::ffi::c_int;
        pub const MAX_SCENE_NAME: core::ffi::c_int = 64 as core::ffi::c_int;
        #[no_mangle]
        pub unsafe extern "C" fn scene_create(name: *const core::ffi::c_char) -> *mut scene_t {
            let scene: *mut scene_t =
                malloc(::core::mem::size_of::<scene_t>() as size_t) as *mut scene_t;
            if scene.is_null() {
                return std::ptr::null_mut::<scene_t>();
            }
            if !name.is_null() {
                strncpy(
                    ((*scene).name).as_mut_ptr(),
                    name,
                    (MAX_SCENE_NAME - 1 as core::ffi::c_int) as size_t,
                );
                (*scene).name[(MAX_SCENE_NAME - 1 as core::ffi::c_int) as usize] =
                    '\0' as i32 as core::ffi::c_char;
            } else {
                strcpy(
                    ((*scene).name).as_mut_ptr(),
                    b"Untitled Scene\0" as *const u8 as *const core::ffi::c_char,
                );
            }
            (*scene).shape_count = 0 as core::ffi::c_int;
            scene
        }
        #[no_mangle]
        pub unsafe extern "C" fn scene_destroy(scene: *mut scene_t) {
            if !scene.is_null() {
                free(scene as *mut core::ffi::c_void);
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn scene_add_shape(
            scene: *mut scene_t,
            shape: *mut shape_t,
        ) -> core::ffi::c_int {
            if scene.is_null() || shape.is_null() {
                return -(1 as core::ffi::c_int);
            }
            if (*scene).shape_count >= MAX_SHAPES_IN_SCENE {
                fprintf(
                    stderr,
                    b"Error: Scene is full\n\0" as *const u8 as *const core::ffi::c_char,
                );
                return -(1 as core::ffi::c_int);
            }
            let fresh0 = (*scene).shape_count;
            (*scene).shape_count += 1;
            (*scene).shapes[fresh0 as usize] = shape;
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn scene_remove_shape(
            scene: *mut scene_t,
            index: core::ffi::c_int,
        ) -> core::ffi::c_int {
            if scene.is_null() || index < 0 as core::ffi::c_int || index >= (*scene).shape_count {
                return -(1 as core::ffi::c_int);
            }
            let mut i: core::ffi::c_int = index;
            while i < (*scene).shape_count - 1 as core::ffi::c_int {
                (*scene).shapes[i as usize] = (*scene).shapes[(i + 1 as core::ffi::c_int) as usize];
                i += 1;
            }
            (*scene).shape_count -= 1;
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn scene_print(scene: *const scene_t) {
            if scene.is_null() {
                printf(b"(null scene)\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            printf(
                b"\n=== Scene: %s ===\n\0" as *const u8 as *const core::ffi::c_char,
                ((*scene).name).as_ptr(),
            );
            printf(
                b"Contains %d shape(s)\n\n\0" as *const u8 as *const core::ffi::c_char,
                (*scene).shape_count,
            );
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < (*scene).shape_count {
                printf(
                    b"Shape #%d:\n\0" as *const u8 as *const core::ffi::c_char,
                    i + 1 as core::ffi::c_int,
                );
                shape_print((*scene).shapes[i as usize]);
                printf(b"\n\0" as *const u8 as *const core::ffi::c_char);
                i += 1;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn scene_equals(
            s1: *const scene_t,
            s2: *const scene_t,
        ) -> core::ffi::c_int {
            if s1.is_null() || s2.is_null() {
                return 0 as core::ffi::c_int;
            }
            if (*s1).shape_count != (*s2).shape_count {
                return 0 as core::ffi::c_int;
            }
            let mut matched: [core::ffi::c_int; 50] = [0 as core::ffi::c_int; 50];
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < (*s1).shape_count {
                let mut found: core::ffi::c_int = 0 as core::ffi::c_int;
                let mut j: core::ffi::c_int = 0 as core::ffi::c_int;
                while j < (*s2).shape_count {
                    if matched[j as usize] == 0
                        && shape_equals((*s1).shapes[i as usize], (*s2).shapes[j as usize]) != 0
                    {
                        matched[j as usize] = 1 as core::ffi::c_int;
                        found = 1 as core::ffi::c_int;
                        break;
                    } else {
                        j += 1;
                    }
                }
                if found == 0 {
                    return 0 as core::ffi::c_int;
                }
                i += 1;
            }
            1 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn scene_save(
            scene: *const scene_t,
            filename: *const core::ffi::c_char,
        ) -> core::ffi::c_int {
            if scene.is_null() || filename.is_null() {
                return -(1 as core::ffi::c_int);
            }
            let file: *mut FILE = fopen(filename, b"w\0" as *const u8 as *const core::ffi::c_char);
            if file.is_null() {
                fprintf(
                    stderr,
                    b"Error: Could not open file '%s' for writing\n\0" as *const u8
                        as *const core::ffi::c_char,
                    filename,
                );
                return -(1 as core::ffi::c_int);
            }
            fprintf(
                file,
                b"%s\n\0" as *const u8 as *const core::ffi::c_char,
                ((*scene).name).as_ptr(),
            );
            fprintf(
                file,
                b"%d\n\0" as *const u8 as *const core::ffi::c_char,
                (*scene).shape_count,
            );
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < (*scene).shape_count {
                fprintf(
                    file,
                    b"%d\n\0" as *const u8 as *const core::ffi::c_char,
                    (*(*scene).shapes[i as usize]).type_0 as core::ffi::c_uint,
                );
                i += 1;
            }
            fclose(file);
            printf(
                b"Scene saved to '%s'\n\0" as *const u8 as *const core::ffi::c_char,
                filename,
            );
            0 as core::ffi::c_int
        }
        #[no_mangle]
        pub unsafe extern "C" fn scene_load(filename: *const core::ffi::c_char) -> *mut scene_t {
            if filename.is_null() {
                return std::ptr::null_mut::<scene_t>();
            }
            let file: *mut FILE = fopen(filename, b"r\0" as *const u8 as *const core::ffi::c_char);
            if file.is_null() {
                fprintf(
                    stderr,
                    b"Error: Could not open file '%s' for reading\n\0" as *const u8
                        as *const core::ffi::c_char,
                    filename,
                );
                return std::ptr::null_mut::<scene_t>();
            }
            let mut name: [core::ffi::c_char; 64] = [0; 64];
            if (fgets(name.as_mut_ptr(), MAX_SCENE_NAME, file)).is_null() {
                fclose(file);
                return std::ptr::null_mut::<scene_t>();
            }
            name[strcspn(
                name.as_ptr(),
                b"\n\0" as *const u8 as *const core::ffi::c_char,
            ) as usize] = 0 as core::ffi::c_char;
            let scene: *mut scene_t = scene_create(name.as_ptr());
            if scene.is_null() {
                fclose(file);
                return std::ptr::null_mut::<scene_t>();
            }
            let mut shape_count: core::ffi::c_int = 0;
            if fscanf(
                file,
                b"%d\n\0" as *const u8 as *const core::ffi::c_char,
                &mut shape_count as *mut core::ffi::c_int,
            ) != 1 as core::ffi::c_int
            {
                scene_destroy(scene);
                fclose(file);
                return std::ptr::null_mut::<scene_t>();
            }
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < shape_count {
                let mut type_0: core::ffi::c_int = 0;
                if fscanf(
                    file,
                    b"%d\n\0" as *const u8 as *const core::ffi::c_char,
                    &mut type_0 as *mut core::ffi::c_int,
                ) != 1 as core::ffi::c_int
                {
                    scene_destroy(scene);
                    fclose(file);
                    return std::ptr::null_mut::<scene_t>();
                }
                let shape: *mut shape_t = shape_get(type_0 as shape_type_t);
                if !shape.is_null() {
                    scene_add_shape(scene, shape);
                }
                i += 1;
            }
            fclose(file);
            printf(
                b"Scene loaded from '%s'\n\0" as *const u8 as *const core::ffi::c_char,
                filename,
            );
            scene
        }
        #[no_mangle]
        pub unsafe extern "C" fn scene_list_shapes(scene: *const scene_t) {
            if scene.is_null() {
                printf(b"(null scene)\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            printf(
                b"\nScene: %s\n\0" as *const u8 as *const core::ffi::c_char,
                ((*scene).name).as_ptr(),
            );
            printf(
                b"Shapes (%d):\n\0" as *const u8 as *const core::ffi::c_char,
                (*scene).shape_count,
            );
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < (*scene).shape_count {
                printf(
                    b"  %d. %s (ptr: %p)\n\0" as *const u8 as *const core::ffi::c_char,
                    i + 1 as core::ffi::c_int,
                    ((*(*scene).shapes[i as usize]).name).as_ptr(),
                    (*scene).shapes[i as usize] as *mut core::ffi::c_void,
                );
                i += 1;
            }
        }
    }
    pub mod shape {
        use crate::src::main::shape_t;
        use crate::src::main::shape_type_t;
        use crate::src::main::size_t;
        use crate::src::main::FILE;
        extern "C" {
            static mut stderr: *mut FILE;
            fn fprintf(
                __stream: *mut FILE,
                __format: *const core::ffi::c_char,
                ...
            ) -> core::ffi::c_int;
            fn printf(__format: *const core::ffi::c_char, ...) -> core::ffi::c_int;
            fn strcpy(
                __dest: *mut core::ffi::c_char,
                __src: *const core::ffi::c_char,
            ) -> *mut core::ffi::c_char;
            fn malloc(__size: size_t) -> *mut core::ffi::c_void;
            fn free(__ptr: *mut core::ffi::c_void);
            fn exit(__status: core::ffi::c_int) -> !;
        }
        pub const SHAPE_COUNT: shape_type_t = 10;
        pub const SHAPE_RAINBOW: shape_type_t = 9;
        pub const SHAPE_HEART: shape_type_t = 8;
        pub const SHAPE_STAR: shape_type_t = 7;
        pub const SHAPE_CAR: shape_type_t = 6;
        pub const SHAPE_FLOWER: shape_type_t = 5;
        pub const SHAPE_CLOUD: shape_type_t = 4;
        pub const SHAPE_SUN: shape_type_t = 3;
        pub const SHAPE_HOUSE: shape_type_t = 2;
        pub const SHAPE_TRACTOR: shape_type_t = 1;
        pub const SHAPE_TREE: shape_type_t = 0;
        pub const NULL: *mut core::ffi::c_void = 0 as *mut core::ffi::c_void;
        static mut shapes: [*mut shape_t; 10] = [
            0 as *const shape_t as *mut shape_t,
            0 as *const shape_t as *mut shape_t,
            0 as *const shape_t as *mut shape_t,
            0 as *const shape_t as *mut shape_t,
            0 as *const shape_t as *mut shape_t,
            0 as *const shape_t as *mut shape_t,
            0 as *const shape_t as *mut shape_t,
            0 as *const shape_t as *mut shape_t,
            0 as *const shape_t as *mut shape_t,
            0 as *const shape_t as *mut shape_t,
        ];
        unsafe extern "C" fn init_tree(shape: *mut shape_t) {
            (*shape).type_0 = SHAPE_TREE;
            strcpy(
                ((*shape).name).as_mut_ptr(),
                b"Tree\0" as *const u8 as *const core::ffi::c_char,
            );
            (*shape).height = 7 as core::ffi::c_int;
            (*shape).width = 11 as core::ffi::c_int;
            strcpy(
                ((*shape).art[0 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"    /\\    \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[1 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"   /  \\   \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[2 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"  /____\\  \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[3 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"  /    \\  \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[4 as core::ffi::c_int as usize]).as_mut_ptr(),
                b" /______\\ \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[5 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"    ||    \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[6 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"    ||    \0" as *const u8 as *const core::ffi::c_char,
            );
        }
        unsafe extern "C" fn init_tractor(shape: *mut shape_t) {
            (*shape).type_0 = SHAPE_TRACTOR;
            strcpy(
                ((*shape).name).as_mut_ptr(),
                b"Tractor\0" as *const u8 as *const core::ffi::c_char,
            );
            (*shape).height = 6 as core::ffi::c_int;
            (*shape).width = 20 as core::ffi::c_int;
            strcpy(
                ((*shape).art[0 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"      ________     \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[1 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"     |        |___ \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[2 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"     |  []  []|   |\0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[3 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"  ___|________|___|\0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[4 as core::ffi::c_int as usize]).as_mut_ptr(),
                b" /  o        o   \\\0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[5 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"|___|        |___| \0" as *const u8 as *const core::ffi::c_char,
            );
        }
        unsafe extern "C" fn init_house(shape: *mut shape_t) {
            (*shape).type_0 = SHAPE_HOUSE;
            strcpy(
                ((*shape).name).as_mut_ptr(),
                b"House\0" as *const u8 as *const core::ffi::c_char,
            );
            (*shape).height = 7 as core::ffi::c_int;
            (*shape).width = 13 as core::ffi::c_int;
            strcpy(
                ((*shape).art[0 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"     /\\     \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[1 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"    /  \\    \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[2 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"   /____\\   \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[3 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"   |    |   \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[4 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"   | [] |   \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[5 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"   |    |   \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[6 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"   |____|   \0" as *const u8 as *const core::ffi::c_char,
            );
        }
        unsafe extern "C" fn init_sun(shape: *mut shape_t) {
            (*shape).type_0 = SHAPE_SUN;
            strcpy(
                ((*shape).name).as_mut_ptr(),
                b"Sun\0" as *const u8 as *const core::ffi::c_char,
            );
            (*shape).height = 7 as core::ffi::c_int;
            (*shape).width = 11 as core::ffi::c_int;
            strcpy(
                ((*shape).art[0 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"  \\  |  / \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[1 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"   \\ | /  \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[2 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"--- (@) ---\0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[3 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"   / | \\  \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[4 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"  /  |  \\ \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[5 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"          \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[6 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"          \0" as *const u8 as *const core::ffi::c_char,
            );
        }
        unsafe extern "C" fn init_cloud(shape: *mut shape_t) {
            (*shape).type_0 = SHAPE_CLOUD;
            strcpy(
                ((*shape).name).as_mut_ptr(),
                b"Cloud\0" as *const u8 as *const core::ffi::c_char,
            );
            (*shape).height = 4 as core::ffi::c_int;
            (*shape).width = 16 as core::ffi::c_int;
            strcpy(
                ((*shape).art[0 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"   _____       \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[1 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"  /     \\_    \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[2 as core::ffi::c_int as usize]).as_mut_ptr(),
                b" /  ___  _\\  \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[3 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"(__/   \\_)   \0" as *const u8 as *const core::ffi::c_char,
            );
        }
        unsafe extern "C" fn init_flower(shape: *mut shape_t) {
            (*shape).type_0 = SHAPE_FLOWER;
            strcpy(
                ((*shape).name).as_mut_ptr(),
                b"Flower\0" as *const u8 as *const core::ffi::c_char,
            );
            (*shape).height = 7 as core::ffi::c_int;
            (*shape).width = 9 as core::ffi::c_int;
            strcpy(
                ((*shape).art[0 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"  \\|/  \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[1 as core::ffi::c_int as usize]).as_mut_ptr(),
                b" -(@)- \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[2 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"  /|\\  \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[3 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"   |   \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[4 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"   |   \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[5 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"  / \\  \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[6 as core::ffi::c_int as usize]).as_mut_ptr(),
                b" /   \\ \0" as *const u8 as *const core::ffi::c_char,
            );
        }
        unsafe extern "C" fn init_car(shape: *mut shape_t) {
            (*shape).type_0 = SHAPE_CAR;
            strcpy(
                ((*shape).name).as_mut_ptr(),
                b"Car\0" as *const u8 as *const core::ffi::c_char,
            );
            (*shape).height = 4 as core::ffi::c_int;
            (*shape).width = 16 as core::ffi::c_int;
            strcpy(
                ((*shape).art[0 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"  ____       \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[1 as core::ffi::c_int as usize]).as_mut_ptr(),
                b" /|_||_\\____ \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[2 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"( o     o  ) \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[3 as core::ffi::c_int as usize]).as_mut_ptr(),
                b" -----------  \0" as *const u8 as *const core::ffi::c_char,
            );
        }
        unsafe extern "C" fn init_star(shape: *mut shape_t) {
            (*shape).type_0 = SHAPE_STAR;
            strcpy(
                ((*shape).name).as_mut_ptr(),
                b"Star\0" as *const u8 as *const core::ffi::c_char,
            );
            (*shape).height = 5 as core::ffi::c_int;
            (*shape).width = 9 as core::ffi::c_int;
            strcpy(
                ((*shape).art[0 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"    *    \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[1 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"   ***   \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[2 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"  *****  \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[3 as core::ffi::c_int as usize]).as_mut_ptr(),
                b" ******* \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[4 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"*********\0" as *const u8 as *const core::ffi::c_char,
            );
        }
        unsafe extern "C" fn init_heart(shape: *mut shape_t) {
            (*shape).type_0 = SHAPE_HEART;
            strcpy(
                ((*shape).name).as_mut_ptr(),
                b"Heart\0" as *const u8 as *const core::ffi::c_char,
            );
            (*shape).height = 6 as core::ffi::c_int;
            (*shape).width = 11 as core::ffi::c_int;
            strcpy(
                ((*shape).art[0 as core::ffi::c_int as usize]).as_mut_ptr(),
                b" *** ***  \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[1 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"*********  \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[2 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"*********  \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[3 as core::ffi::c_int as usize]).as_mut_ptr(),
                b" ******* \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[4 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"  *****  \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[5 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"   ***   \0" as *const u8 as *const core::ffi::c_char,
            );
        }
        unsafe extern "C" fn init_rainbow(shape: *mut shape_t) {
            (*shape).type_0 = SHAPE_RAINBOW;
            strcpy(
                ((*shape).name).as_mut_ptr(),
                b"Rainbow\0" as *const u8 as *const core::ffi::c_char,
            );
            (*shape).height = 5 as core::ffi::c_int;
            (*shape).width = 21 as core::ffi::c_int;
            strcpy(
                ((*shape).art[0 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"      _______      \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[1 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"    /         \\    \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[2 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"   /           \\   \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[3 as core::ffi::c_int as usize]).as_mut_ptr(),
                b"  /             \\  \0" as *const u8 as *const core::ffi::c_char,
            );
            strcpy(
                ((*shape).art[4 as core::ffi::c_int as usize]).as_mut_ptr(),
                b" /               \\ \0" as *const u8 as *const core::ffi::c_char,
            );
        }
        #[no_mangle]
        pub unsafe extern "C" fn shape_manager_init() {
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < SHAPE_COUNT as core::ffi::c_int {
                shapes[i as usize] =
                    malloc(::core::mem::size_of::<shape_t>() as size_t) as *mut shape_t;
                if (shapes[i as usize]).is_null() {
                    fprintf(
                        stderr,
                        b"Error: Failed to allocate shape\n\0" as *const u8
                            as *const core::ffi::c_char,
                    );
                    exit(1 as core::ffi::c_int);
                }
                i += 1;
            }
            init_tree(shapes[SHAPE_TREE as core::ffi::c_int as usize]);
            init_tractor(shapes[SHAPE_TRACTOR as core::ffi::c_int as usize]);
            init_house(shapes[SHAPE_HOUSE as core::ffi::c_int as usize]);
            init_sun(shapes[SHAPE_SUN as core::ffi::c_int as usize]);
            init_cloud(shapes[SHAPE_CLOUD as core::ffi::c_int as usize]);
            init_flower(shapes[SHAPE_FLOWER as core::ffi::c_int as usize]);
            init_car(shapes[SHAPE_CAR as core::ffi::c_int as usize]);
            init_star(shapes[SHAPE_STAR as core::ffi::c_int as usize]);
            init_heart(shapes[SHAPE_HEART as core::ffi::c_int as usize]);
            init_rainbow(shapes[SHAPE_RAINBOW as core::ffi::c_int as usize]);
        }
        #[no_mangle]
        pub unsafe extern "C" fn shape_manager_cleanup() {
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < SHAPE_COUNT as core::ffi::c_int {
                free(shapes[i as usize] as *mut core::ffi::c_void);
                shapes[i as usize] = std::ptr::null_mut::<shape_t>();
                i += 1;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn shape_get(type_0: shape_type_t) -> *mut shape_t {
            if (type_0 as core::ffi::c_uint) < 0 as core::ffi::c_uint
                || type_0 as core::ffi::c_uint
                    >= SHAPE_COUNT as core::ffi::c_int as core::ffi::c_uint
            {
                return std::ptr::null_mut::<shape_t>();
            }
            shapes[type_0 as usize]
        }
        #[no_mangle]
        pub unsafe extern "C" fn shape_print(shape: *const shape_t) {
            if shape.is_null() {
                printf(b"(null shape)\n\0" as *const u8 as *const core::ffi::c_char);
                return;
            }
            printf(
                b"%s:\n\0" as *const u8 as *const core::ffi::c_char,
                ((*shape).name).as_ptr(),
            );
            let mut i: core::ffi::c_int = 0 as core::ffi::c_int;
            while i < (*shape).height {
                printf(
                    b"%s\n\0" as *const u8 as *const core::ffi::c_char,
                    ((*shape).art[i as usize]).as_ptr(),
                );
                i += 1;
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn shape_equals(
            s1: *const shape_t,
            s2: *const shape_t,
        ) -> core::ffi::c_int {
            if s1 == s2 {
                1 as core::ffi::c_int
            } else {
                0 as core::ffi::c_int
            }
        }
        #[no_mangle]
        pub unsafe extern "C" fn shape_type_name(type_0: shape_type_t) -> *const core::ffi::c_char {
            match type_0 as core::ffi::c_uint {
                0 => b"Tree\0" as *const u8 as *const core::ffi::c_char,
                1 => b"Tractor\0" as *const u8 as *const core::ffi::c_char,
                2 => b"House\0" as *const u8 as *const core::ffi::c_char,
                3 => b"Sun\0" as *const u8 as *const core::ffi::c_char,
                4 => b"Cloud\0" as *const u8 as *const core::ffi::c_char,
                5 => b"Flower\0" as *const u8 as *const core::ffi::c_char,
                6 => b"Car\0" as *const u8 as *const core::ffi::c_char,
                7 => b"Star\0" as *const u8 as *const core::ffi::c_char,
                8 => b"Heart\0" as *const u8 as *const core::ffi::c_char,
                9 => b"Rainbow\0" as *const u8 as *const core::ffi::c_char,
                _ => b"Unknown\0" as *const u8 as *const core::ffi::c_char,
            }
        }
    }
}
"####;

#[test]
fn ownership_analysis_runs() {
    run_ownership_case_with_box_candidates(
        "pointer-comparison-ascii-art",
        SOURCE,
        &["scene_create#scene"],
        &[],
    );
}
