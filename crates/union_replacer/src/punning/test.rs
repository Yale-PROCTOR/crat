#[cfg(test)]
mod tests {
    fn run_test(code: &str) {
        let s = utils::compilation::run_compiler_on_str(code, |tcx| {
            super::super::replace_unions(tcx, true)
        })
        .unwrap();
        utils::compilation::run_compiler_on_str(&s, utils::type_check).expect(&s);
    }

    const BASE: &str = r#"
        #![feature(derive_clone_copy)]
        #[derive(Copy, Clone)]
        pub struct NonPrimitive32(pub u32);

        #[derive(Copy, Clone)]
        pub union U {
            pub a: u32,
            pub b: f32,
            pub c: NonPrimitive32,
        }

        pub fn use_a(x: u32) {
            ()
        }

        pub fn use_b(x: f32) {
            ()
        }

        pub fn use_c(x: NonPrimitive32) {
            ()
        }

        pub fn cond() -> bool {
            true
        }

        pub fn nop() {
            ()
        }
    "#;

    #[test]
    fn trivial() {
        let code = r#"
        pub extern "C" fn trivial() {
            let u: U = U { a: 1 }; // Write A
            unsafe {
                use_b(u.b); // Read B
            }
        }
        "#;
        let code = format!("{BASE}\n{code}");
        run_test(&code);
    }

    #[test]
    fn wwr() {
        let code = r#"
        pub extern "C" fn wwr() {
            let mut u: U = U { a: 1 }; // Write A
            u.b = 2.0; // Write B
            unsafe {
                use_a(u.a); // Read A
            }
        }
        "#;

        let code = format!("{BASE}\n{code}");
        run_test(&code);
    }

    #[test]
    fn no_transform() {
        let code = r#"
        pub extern "C" fn no_transform() {
            let mut u: U = U { c: NonPrimitive32(1) }; // Write C
            unsafe {
                use_a(u.a); // Read A
            }
        }
        "#;

        let code = format!("{BASE}\n{code}");
        run_test(&code);
    }

    #[test]
    fn extra_write() {
        let code = r#"
        pub extern "C" fn extra_write() {
            let mut u: U = U { a: 1 }; // Write A
            u.b = 2.0; // Write B, extra write will be added {e; e};
            if cond() {
                unsafe {
                    use_c(u.c); // Read C, non-replacable
                }
            } else {
                unsafe {
                    use_a(u.a); // Read A, replacable
                }
            }
        }
        "#;

        let code = format!("{BASE}\n{code}");
        run_test(&code);
    }

    #[test]
    fn loop1() {
        let code = r#"
        pub extern "C" fn loop1() {
            let mut u: U = U {
                c: NonPrimitive32(0),
            }; // Write C

            loop {
                u.a = 1; // Write A
                unsafe {
                    use_a(u.a); // Read A
                }
                u.b = 2.0; // Write B
            }
        }
        "#;

        let code = format!("{BASE}\n{code}");
        run_test(&code);
    }

    #[test]
    fn loop2() {
        let code = r#"
        pub extern "C" fn loop2() {
            let mut u: U = U { a: 1 }; // Write A

            loop {
                unsafe {
                    use_a(u.a); // Read A
                }
                u.b = 2.0; // Write B
            }
        }
        "#;

        let code = format!("{BASE}\n{code}");
        run_test(&code);
    }

    #[test]
    fn branch1() {
        let code = r#"
        pub extern "C" fn branch1() {
            let mut u: U = U { a: 1 }; // Write A

            if cond() {
                u.a = 2; // Write A
            } else {
                u.b = 3.0; // Write B
            }
            unsafe {
                use_a(u.a); // Read A
            }
        }
        "#;

        let code = format!("{BASE}\n{code}");
        run_test(&code);
    }

    #[test]
    fn branch2() {
        let code = r#"
        pub extern "C" fn branch2() {
            let u: U = U { a: 1 }; // Write A

            if cond() {
                nop();
            } else {
                unsafe {
                    use_b(u.b); // Read B
                }
            }
            nop();
        }
        "#;

        let code = format!("{BASE}\n{code}");
        run_test(&code);
    }

    #[test]
    fn branch3() {
        let code = r#"
        pub extern "C" fn branch3() {
            let mut u: U = U { a: 1 }; // Write A

            if cond() {
                u.b = 2.0; // Write B
            } else {
                unsafe {
                    use_b(u.b); // Read B
                }
            }
            unsafe {
                use_a(u.a); // Read A
            }
        }
        "#;

        let code = format!("{BASE}\n{code}");
        run_test(&code);
    }

    #[test]
    fn branch4() {
        let code = r#"
        pub extern "C" fn branch4() {
            let mut u: U = U { a: 1 }; // Write A

            if cond() {
                u.a = 2; // Write A
            } else {
                unsafe {
                    use_b(u.b); // Read B
                }
            }
            unsafe {
                use_a(u.a); // Read A
            }
        }
        "#;

        let code = format!("{BASE}\n{code}");
        run_test(&code);
    }

    #[test]
    fn branch5() {
        let code = r#"
        pub extern "C" fn branch5() {
            let mut u: U = U {
                c: NonPrimitive32(1),
            }; // Write C

            if cond() {
                u.a = 2; // Write A
            } else {
                u.b = 3.0; // Write B
            }
            unsafe {
                use_a(u.a); // Read A
            }
        }
        "#;

        let code = format!("{BASE}\n{code}");
        run_test(&code);
    }

    #[test]
    fn if_inside_loop() {
        let code = r#"
        pub extern "C" fn if_inside_loop() {
            let mut u: U = U { a: 1 }; // Write A
            unsafe {
                use_c(u.c); // Read C
            }

            loop {
                if cond() {
                    u.a = 2; // Write A
                }

                u.b = 3.0; // Write B
                unsafe {
                    use_a(u.a); // Read A
                }
            }
        }
        "#;

        let code = format!("{BASE}\n{code}");
        run_test(&code);
    }

    // #[test]
    // fn temp() {
    //     let code = r#"
    //     "#;

    //     let code = format!("{BASE}\n{code}");
    //     run_test(&code);
    // }
}
