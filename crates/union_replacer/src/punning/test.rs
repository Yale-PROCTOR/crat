#[cfg(test)]
mod tests {
    fn run_test(code: &str, expected_stats: (usize, usize, usize)) {
        let s = utils::compilation::run_compiler_on_str(code, |tcx| {
            super::super::replace_unions(tcx, true)
        })
        .unwrap();
        utils::compilation::run_compiler_on_str(&s.code, utils::type_check).expect(&s.code);
        assert_eq!(s.union_use_stats, expected_stats, "{}", s.code);
    }

    // TODO: bytemuck trait impl을 현재는 manual하게 달았는데, 이게 자동으로 derive되도록 구현해야 함
    const BASE: &str = r#"
        #![feature(derive_clone_copy)]
        #[repr(transparent)]
        #[derive(Copy, Clone)]
        pub struct NonPrimitive32(pub u32);

        unsafe impl bytemuck::Zeroable for NonPrimitive32 {}
        unsafe impl bytemuck::Pod for NonPrimitive32 {}

        #[derive(Copy, Clone)]
        pub union U {
            pub a: u32,
            pub b: f32,
            pub c: NonPrimitive32,
        }

        pub fn use_a(x: u32) -> u32 {
            x
        }

        pub fn use_b(x: f32) -> f32 {
            x
        }

        pub fn use_c(x: NonPrimitive32) -> NonPrimitive32 {
            x
        }

        pub fn cond() -> bool {
            true
        }

        pub fn nop() -> u8 {
            0
        }
    "#;

    #[test]
    fn basic_direct_read_after_write() {
        let code = r#"
        pub extern "C" fn basic() {
            let u: U = U { a: 1 };
            unsafe {
                use_b(u.b);
            }
        }
        "#;

        let code = format!("{BASE}\n{code}");
        run_test(&code, (1, 1, 1));
    }

    #[test]
    fn basic_overwrite_then_read() {
        let code = r#"
        pub extern "C" fn basic2() {
            let mut u: U = U { a: 1 };
            u.b = 2.0;
            unsafe {
                use_a(u.a);
            }
        }
        "#;

        let code = format!("{BASE}\n{code}");
        run_test(&code, (1, 1, 1));
    }

    #[test]
    fn basic_same_field_union_filtered() {
        let code = r#"
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union SameTypeU {
            pub x: u32,
            pub y: u32,
        }

        pub extern "C" fn non_punning() {
            let mut u = SameTypeU { x: 0 };
            unsafe {
                u.y = 42;
                use_a(u.x);
            }
        }
        "#;

        let code = format!("{BASE}\n{code}");
        run_test(&code, (2, 2, 0));
    }

    #[test]
    fn overlap_parent_direct() {
        let code = r#"
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union OverlapU {
            pub a: u32,
            pub b: [u8; 4],
        }

        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct ParentOverlap {
            pub d: u32,
            pub u: OverlapU,
            pub i: i32,
        }

        pub extern "C" fn overlap_parent_direct() {
            let mut s = ParentOverlap { d: 0, u: OverlapU { a: 0 }, i: 1 };
            unsafe {
                s.u.b = [1, 2, 3, 4];
                use_a(s.u.a);
            }
        }
        "#;

        let code = format!("{BASE}\n{code}");
        run_test(&code, (2, 2, 1));
    }

    #[test]
    fn overlap_parent_helper_write() {
        let code = r#"
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union OverlapU {
            pub a: u32,
            pub b: [u8; 4],
        }

        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct ParentOverlap {
            pub u: OverlapU,
            pub i: i32,
        }

        fn touch_overlap(p: *mut ParentOverlap) {
            unsafe {
                (*p).u.b = [5, 6, 7, 8];
            }
        }

        pub extern "C" fn overlap_parent_helper_write() {
            let mut s = ParentOverlap { u: OverlapU { a: 0 }, i: 1 };
            touch_overlap(&mut s as *mut ParentOverlap);
            unsafe {
                use_a(s.u.a);
            }
        }
        "#;

        let code = format!("{BASE}\n{code}");
        run_test(&code, (2, 2, 1));
    }

    #[test]
    fn overlap_parent_index() {
        let code = r#"
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union OverlapU {
            pub a: u32,
            pub b: [u8; 4],
        }

        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct ParentOverlap {
            pub u: OverlapU,
        }

        pub extern "C" fn overlap_parent_index() {
            let mut s = ParentOverlap { u: OverlapU { a: 0 } };
            unsafe {
                s.u.a = 0x11223344;
                use_a(s.u.b[2] as u32);
            }
        }
        "#;

        let code = format!("{BASE}\n{code}");
        run_test(&code, (2, 2, 1));
    }

    #[test]
    fn overlap_nested_parent() {
        let code = r#"
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union OverlapU {
            pub a: u32,
            pub b: [u8; 4],
        }

        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct ParentOverlap {
            pub u: OverlapU,
        }

        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct NestedOverlap {
            pub inner: ParentOverlap,
        }

        pub extern "C" fn overlap_nested_parent() {
            let mut n = NestedOverlap { inner: ParentOverlap { u: OverlapU { a: 0 } } };
            unsafe {
                n.inner.u.b = [9, 8, 7, 6];
                use_a(n.inner.u.a);
            }
        }
        "#;

        let code = format!("{BASE}\n{code}");
        run_test(&code, (2, 2, 1));
    }

    #[test]
    fn overlap_nested_index() {
        let code = r#"
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union OverlapU {
            pub a: u32,
            pub b: [u8; 4],
        }

        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct ParentOverlap {
            pub u: OverlapU,
        }

        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct NestedOverlap {
            pub inner: ParentOverlap,
        }

        pub extern "C" fn overlap_nested_index() {
            let mut n = NestedOverlap { inner: ParentOverlap { u: OverlapU { a: 0 } } };
            unsafe {
                n.inner.u.a = 0xAABBCCDD;
                use_a(n.inner.u.b[1] as u32);
            }
        }
        "#;

        let code = format!("{BASE}\n{code}");
        run_test(&code, (2, 2, 1));
    }

    #[test]
    fn overlap_helper_read() {
        let code = r#"
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union OverlapU {
            pub a: u32,
            pub b: [u8; 4],
        }

        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct ParentOverlap {
            pub u: OverlapU,
        }

        fn write_and_read(p: *mut ParentOverlap) -> u32 {
            unsafe {
                (*p).u.b = [3, 4, 5, 6];
                (*p).u.a
            }
        }

        pub extern "C" fn overlap_helper_read() {
            let mut s = ParentOverlap { u: OverlapU { a: 0 } };
            unsafe {
                use_a(write_and_read(&mut s as *mut ParentOverlap));
            }
        }
        "#;

        let code = format!("{BASE}\n{code}");
        run_test(&code, (2, 2, 1));
    }

    #[test]
    fn overlap_partial_byte_write() {
        // unsafe union use case -> no transform
        let code = r#"
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union OverlapU {
            pub a: u32,
            pub b: [u8; 4],
        }

        pub extern "C" fn overlap_partial_byte_write() {
            let mut u = OverlapU { a: 0 };
            unsafe {
                let byte_ptr = (&mut u as *mut OverlapU).cast::<u8>();
                *byte_ptr.add(0) = 0xAA;
                *byte_ptr.add(1) = 0xBB;
                use_a(u.a);
            }
        }
        "#;

        let code = format!("{BASE}\n{code}");
        run_test(&code, (2, 2, 0));
    }

    #[test]
    fn overlap_copy_into_parent_union() {
        let code = r#"
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union OverlapU {
            pub a: u32,
            pub b: [u8; 4],
        }

        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct ParentOverlap {
            pub u: OverlapU,
        }

        pub extern "C" fn overlap_copy_into_parent_union() {
            let mut s = ParentOverlap { u: OverlapU { a: 0 } };
            let v = OverlapU { b: [1, 1, 1, 1] };
            unsafe {
                s.u = v;
                use_a(s.u.a);
            }
        }
        "#;

        let code = format!("{BASE}\n{code}");
        run_test(&code, (2, 2, 1));
    }

    #[test]
    fn overlap_branch_parent() {
        let code = r#"
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union OverlapU {
            pub a: u32,
            pub b: [u8; 4],
        }

        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct ParentOverlap {
            pub u: OverlapU,
        }

        pub extern "C" fn overlap_branch_parent() {
            let mut s = ParentOverlap { u: OverlapU { a: 0 } };
            if cond() {
                unsafe { s.u.b = [7, 7, 7, 7]; }
            } else {
                unsafe { s.u.b = [8, 8, 8, 8]; }
            }
            unsafe {
                use_a(s.u.a);
            }
        }
        "#;

        let code = format!("{BASE}\n{code}");
        run_test(&code, (2, 2, 1));
    }

    #[test]
    fn false_positive_branch() {
        let code = r#"
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union OverlapU {
            pub a: u32,
            pub b: [u8; 4],
        }

        pub extern "C" fn false_positive_branch() {
            let mut u = OverlapU { a: 0 };
            let c = cond();
            if c {
                unsafe { u.b = [1, 2, 3, 4]; }
            } else {
                nop();
            }
            if c {
                nop();
            } else {
                unsafe { use_a(u.a); }
            }
        }
        "#;

        let code = format!("{BASE}\n{code}");
        run_test(&code, (2, 2, 1));
    }
}
