#[cfg(test)]
mod tests {
    fn run_test(code: &str, expected_stats: (usize, usize, usize)) {
        let config = super::super::Config {
            c_exposed_fns: Default::default(),
        };
        let s = utils::compilation::run_compiler_on_str(code, |tcx| {
            super::super::replace_unions(tcx, true, &config)
        })
        .unwrap();
        utils::compilation::run_compiler_on_str(&s.code, utils::type_check).expect(&s.code);
        assert_eq!(s.union_use_stats, expected_stats, "{}", s.code);
    }

    const BASE: &str = r#"
        #![feature(derive_clone_copy)]
        #[repr(transparent)]
        #[derive(Copy, Clone)]
        pub struct NonPrimitive32(pub u32);

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
    fn basic_pod() {
        let code = r#"
        pub extern "C" fn basic_pod() {
            let u = U { a: 1 };
            unsafe {
                use_b(u.b);
            }
        }
        "#;

        run_test(&format!("{BASE}\n{code}"), (1, 1, 1));
    }

    #[test]
    fn basic_nouninit() {
        let code = r#"
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union PtrU {
            pub a: *mut u8,
            pub b: usize,
        }

        pub extern "C" fn basic_nouninit() {
            let u = PtrU { a: 1usize as *mut u8 };
            unsafe {
                use_a(u.b as u32);
            }
        }
        "#;

        run_test(&format!("{BASE}\n{code}"), (2, 2, 1));
    }

    #[test]
    fn basic_anybitpattern() {
        let code = r#"
        #[derive(Copy, Clone)]
        pub struct Padded {
            pub tag: u8,
            pub value: u32,
        }

        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union AnyBitsU {
            pub a: u64,
            pub b: Padded,
        }

        fn use_padded(x: Padded) -> u32 {
            x.value
        }

        pub extern "C" fn basic_anybitpattern() {
            let u = AnyBitsU { a: 7 };
            unsafe {
                use_a(use_padded(u.b));
            }
        }
        "#;

        run_test(&format!("{BASE}\n{code}"), (2, 2, 1));
    }

    #[test]
    fn parent_pod() {
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

        pub extern "C" fn parent_pod() {
            let mut s = ParentOverlap { d: 0, u: OverlapU { a: 0 }, i: 1 };
            unsafe {
                s.u.b = [1, 2, 3, 4];
                use_a(s.u.a);
            }
        }
        "#;

        run_test(&format!("{BASE}\n{code}"), (2, 2, 1));
    }

    #[test]
    fn parent_nouninit() {
        let code = r#"
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union PtrU {
            pub a: *mut u8,
            pub b: usize,
        }

        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct ParentPtr {
            pub u: PtrU,
        }

        pub extern "C" fn parent_nouninit() {
            let mut s = ParentPtr { u: PtrU { a: core::ptr::null_mut() } };
            unsafe { s.u.a = 1usize as *mut u8; use_a(s.u.b as u32); }
        }
        "#;

        run_test(&format!("{BASE}\n{code}"), (2, 2, 1));
    }

    #[test]
    fn parent_anybitpattern() {
        let code = r#"
        #[derive(Copy, Clone)]
        pub struct Padded {
            pub tag: u8,
            pub value: u32,
        }

        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union AnyBitsU {
            pub a: u64,
            pub b: Padded,
        }

        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct ParentBits {
            pub u: AnyBitsU,
        }

        pub extern "C" fn parent_anybitpattern() {
            let s = ParentBits { u: AnyBitsU { a: 9 } };
            unsafe {
                use_a(s.u.b.value);
            }
        }
        "#;

        run_test(&format!("{BASE}\n{code}"), (2, 2, 1));
    }

    #[test]
    fn nested_parent_bytes_to_u32() {
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

        pub extern "C" fn nested_parent_bytes_to_u32() {
            let mut n = NestedOverlap { inner: ParentOverlap { u: OverlapU { a: 0 } } };
            unsafe {
                n.inner.u.b = [9, 8, 7, 6];
                use_a(n.inner.u.a);
            }
        }
        "#;

        run_test(&format!("{BASE}\n{code}"), (2, 2, 1));
    }

    #[test]
    fn call_by_value_read() {
        let code = r#"
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union OverlapU {
            pub a: u32,
            pub b: [u8; 4],
        }

        fn read_u(u: OverlapU) -> u32 {
            unsafe { u.a }
        }

        pub extern "C" fn call_by_value_read() {
            let mut u = OverlapU { a: 0 };
            unsafe {
                u.b = [1, 2, 3, 4];
            }
            use_a(read_u(u));
        }
        "#;

        run_test(&format!("{BASE}\n{code}"), (2, 2, 1));
    }

    #[test]
    fn call_by_value_parent_read() {
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

        fn read_parent(p: ParentOverlap) -> u32 {
            unsafe { p.u.a }
        }

        pub extern "C" fn call_by_value_parent_read() {
            let mut p = ParentOverlap { u: OverlapU { a: 0 }, i: 1 };
            unsafe {
                p.u.b = [1, 2, 3, 4];
            }
            use_a(read_parent(p));
        }
        "#;

        run_test(&format!("{BASE}\n{code}"), (2, 2, 1));
    }

    #[test]
    fn return_by_value_read() {
        let code = r#"
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union OverlapU {
            pub a: u32,
            pub b: [u8; 4],
        }

        fn make_u() -> OverlapU {
            let mut u = OverlapU { a: 0 };
            unsafe {
                u.b = [9, 8, 7, 6];
            }
            u
        }

        pub extern "C" fn return_by_value_read() {
            let u = make_u();
            unsafe {
                use_a(u.a);
            }
        }
        "#;

        run_test(&format!("{BASE}\n{code}"), (2, 2, 1));
    }

    #[test]
    fn return_parent_by_value_read() {
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

        fn make_parent() -> ParentOverlap {
            let mut p = ParentOverlap { u: OverlapU { a: 0 }, i: 1 };
            unsafe {
                p.u.b = [4, 3, 2, 1];
            }
            p
        }

        pub extern "C" fn return_parent_by_value_read() {
            let p = make_parent();
            unsafe {
                use_a(p.u.a);
            }
        }
        "#;

        run_test(&format!("{BASE}\n{code}"), (2, 2, 1));
    }

    #[test]
    fn call_parent_write() {
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

        pub extern "C" fn call_parent_write() {
            let mut s = ParentOverlap { u: OverlapU { a: 0 }, i: 1 };
            touch_overlap(&mut s as *mut ParentOverlap);
            unsafe {
                use_a(s.u.a);
            }
        }
        "#;

        run_test(&format!("{BASE}\n{code}"), (2, 2, 1));
    }

    #[test]
    fn call_padded_read() {
        let code = r#"
        #[derive(Copy, Clone)]
        pub struct Padded {
            pub tag: u8,
            pub value: u32,
        }

        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union AnyBitsU {
            pub a: u64,
            pub b: Padded,
        }

        fn read_padded(u: AnyBitsU) -> Padded {
            unsafe { u.b }
        }

        pub extern "C" fn call_padded_read() {
            let u = AnyBitsU { a: 11 };
            use_a(read_padded(u).value);
        }
        "#;

        run_test(&format!("{BASE}\n{code}"), (2, 2, 1));
    }

    #[test]
    fn pointer_write_then_read() {
        let code = r#"
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union OverlapU {
            pub a: u32,
            pub b: [u8; 4],
        }

        pub extern "C" fn pointer_write_then_read() {
            let mut u = OverlapU { a: 0 };
            unsafe {
                let p = &mut u as *mut OverlapU;
                (*p).b = [1, 3, 5, 7];
                use_a((*p).a);
            }
        }
        "#;

        run_test(&format!("{BASE}\n{code}"), (2, 2, 1));
    }

    #[test]
    fn pointer_read_ptr_bits() {
        let code = r#"
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union PtrU {
            pub a: *mut u8,
            pub b: usize,
        }

        pub extern "C" fn pointer_read_ptr_bits() {
            let mut u = PtrU { a: core::ptr::null_mut() };
            unsafe {
                let p = &mut u as *mut PtrU;
                (*p).a = 1usize as *mut u8;
                use_a((*p).b as u32);
            }
        }
        "#;

        run_test(&format!("{BASE}\n{code}"), (2, 2, 1));
    }

    #[test]
    fn pointer_parent_union_field() {
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

        pub extern "C" fn pointer_parent_union_field() {
            let mut s = ParentOverlap { u: OverlapU { a: 0 } };
            unsafe {
                let p = &mut s.u as *mut OverlapU;
                (*p).b = [2, 4, 6, 8];
                use_a(s.u.a);
            }
        }
        "#;

        run_test(&format!("{BASE}\n{code}"), (2, 2, 1));
    }

    #[test]
    fn pointer_read_padded_field() {
        let code = r#"
        #[derive(Copy, Clone)]
        pub struct Padded {
            pub tag: u8,
            pub value: u32,
        }

        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union AnyBitsU {
            pub a: u64,
            pub b: Padded,
        }

        pub extern "C" fn pointer_read_padded_field() {
            let mut u = AnyBitsU { a: 21 };
            unsafe {
                let p = &mut u as *mut AnyBitsU;
                use_a((*p).b.value);
            }
        }
        "#;

        run_test(&format!("{BASE}\n{code}"), (2, 2, 1));
    }

    #[test]
    fn pointer_call_chain() {
        let code = r#"
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union OverlapU {
            pub a: u32,
            pub b: [u8; 4],
        }

        fn read_from_ptr(p: *const OverlapU) -> u32 {
            unsafe { (*p).a }
        }

        pub extern "C" fn pointer_call_chain() {
            let mut u = OverlapU { a: 0 };
            unsafe {
                let p = &mut u as *mut OverlapU;
                (*p).b = [8, 6, 4, 2];
                use_a(read_from_ptr(p));
            }
        }
        "#;

        run_test(&format!("{BASE}\n{code}"), (2, 2, 1));
    }

    #[test]
    fn ip() {
        let code = r#"
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union Ipv4 {
            pub as_int: u32,
            pub octet: [u8; 4],
        }

        unsafe fn local_host(p: &mut [u8; 4]) {
            *p = [127, 0, 0, 1];
        }

        pub extern "C" fn ip() {
            let mut ip = Ipv4 { as_int: 0 };
            unsafe { local_host(&mut ip.octet); }
            unsafe { use_a(ip.as_int); }
        }
        "#;

        run_test(
            &format!(
                "{BASE}
{code}"
            ),
            (2, 2, 1),
        );
    }

    #[test]
    fn ip2() {
        let code = r#"
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union Ipv4 {
            pub octet: [u8; 4],
            pub as_int: u32,
        }

        unsafe fn local_host(p: &mut [u8; 4]) {
            *p = [127, 0, 0, 1];
        }

        pub extern "C" fn ip2() {
            let mut ip = Ipv4 { as_int: 0 };
            unsafe { local_host(&mut ip.octet); }
            unsafe { use_a(ip.as_int); }
        }
        "#;

        run_test(
            &format!(
                "{BASE}
{code}"
            ),
            (2, 2, 1),
        );
    }

    #[test]
    fn tagged_ii() {
        let code = r#"
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union Value {
            pub i: i32,
            pub i2: i32,
        }

        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct Parent {
            pub u: Value,
        }

        unsafe fn to_field_ptr(value: *mut Parent) -> *mut i32 {
            &mut (*value).u.i as *mut i32
        }

        pub extern "C" fn tagged_ii() {
            let mut value = Parent {
                u: Value { i: 0 },
            };
            unsafe {
                value.u.i = 42;
                let p = to_field_ptr(&mut value as *mut Parent);
                *p;
            }
        }
        "#;

        run_test(
            &format!(
                "{BASE}
{code}"
            ),
            (2, 2, 0),
        );
    }


    #[test]
    fn tagged_if() {
        let code = r#"
        #[derive(Copy, Clone)]
        #[repr(C)]
        pub union Value {
            pub i: i32,
            pub f: f32,
        }

        #[derive(Copy, Clone)]
        #[repr(C)]
        pub struct Parent {
            pub u: Value,
        }

        unsafe fn to_field_ptr(value: *mut Parent) -> *mut i32 {
            &mut (*value).u.i as *mut i32
        }

        pub extern "C" fn tagged_if() {
            let mut value = Parent {
                u: Value { i: 0 },
            };
            unsafe {
                value.u.i = 42;
                let p = to_field_ptr(&mut value as *mut Parent);
                *p;
            }
        }
        "#;

        run_test(
            &format!(
                "{BASE}
{code}"
            ),
            (2, 2, 0),
        );
    }

//     #[test]
//     fn tagged_iif() {
//         let code = r#"
//         #[derive(Copy, Clone)]
//         #[repr(C)]
//         pub union Value {
//             pub i: i32,
//             pub i2: i32,
//             pub f: f32,
//         }

//         #[derive(Copy, Clone)]
//         #[repr(C)]
//         pub struct Parent {
//             pub u: Value,
//         }

//         unsafe fn to_field_ptr(value: *mut Parent) -> *mut i32 {
//             &mut (*value).u.i as *mut i32
//         }

//         pub extern "C" fn tagged_iif() {
//             let mut value = Parent {
//                 u: Value { i: 0 },
//             };
//             unsafe {
//                 value.u.i = 42;
//                 let p = to_field_ptr(&mut value as *mut Parent);
//                 *p;
//             }
//         }
//         "#;

//         run_test(
//             &format!(
//                 "{BASE}
// {code}"
//             ),
//             (2, 2, 0),
//         );
//     }
}
