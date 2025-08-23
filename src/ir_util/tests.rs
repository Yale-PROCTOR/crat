use rustc_ast::{visit::Visitor, *};
use rustc_hir::{self as hir, def_id::LocalModDefId};
use rustc_span::FileName;

use super::*;
use crate::{ast_util, compile_util};

fn run_test(code: &str) {
    let code = format!(
        "
        #![feature(associated_type_defaults)]
        #![feature(extern_types)]
        #![feature(trait_alias)]
        #![feature(c_variadic)]
        #![feature(default_field_values)]
        #![feature(closure_lifetime_binder)]
        #![feature(more_qualified_paths)]
        #![feature(box_patterns)]
        #![feature(unsafe_binders)]
        mod a {{ {code} }}"
    );
    compile_util::run_compiler_on_str(&code, |tcx| {
        let borrowed = tcx.resolver_for_lowering().borrow();
        let mut expanded_crate = borrowed.1.as_ref().clone();
        drop(borrowed);

        let parse_sess = ast_util::new_parse_sess();
        let mut parser = rustc_parse::new_parser_from_source_str(
            &parse_sess,
            FileName::Custom("test.rs".to_string()),
            code.clone(),
        )
        .unwrap();
        let mut krate = parser.parse_crate_mod().unwrap();
        let items = krate
            .items
            .iter_mut()
            .find_map(|item| {
                if let ItemKind::Mod(_, ident, ModKind::Loaded(items, _, _, _)) = &mut item.kind
                    && ident.as_str() == "a"
                {
                    Some(items)
                } else {
                    None
                }
            })
            .unwrap();
        let (module, _, _) = tcx.hir_get_module(LocalModDefId::CRATE_DEF_ID);
        let hitems = module
            .item_ids
            .iter()
            .find_map(|item_id| {
                let item = tcx.hir_item(*item_id);
                if let hir::ItemKind::Mod(ident, module) = &item.kind
                    && ident.as_str() == "a"
                {
                    Some(module.item_ids)
                } else {
                    None
                }
            })
            .unwrap();
        let mut mapper = AstToHirMapper::new(tcx);
        mapper.map_items_to_items(items, hitems, false);
        let mut checker = AstToHirChecker {
            tcx,
            ast_to_hir: mapper.ast_to_hir,
        };
        for item in items {
            checker.visit_item(item);
        }

        let mut mapper = AstToHirMapper::new(tcx);
        let module = tcx.hir_root_module();
        mapper.map_crate_to_mod(&mut expanded_crate, module, true);
        let mut checker = AstToHirChecker {
            tcx,
            ast_to_hir: mapper.ast_to_hir,
        };
        for item in &expanded_crate.items {
            checker.visit_item(item);
        }

        let hir_to_thir = map_hir_to_thir(tcx);
        let mut checker = HirToThirChecker { tcx, hir_to_thir };
        tcx.hir_visit_all_item_likes_in_crate(&mut checker);
    })
    .unwrap();
}

#[test]
fn test_item_use() {
    run_test("use std::path::Path;")
}

#[test]
fn test_item_static() {
    run_test("static X: i32 = 0;")
}

#[test]
fn test_item_const() {
    run_test("const X: i32 = 0;")
}

#[test]
fn test_item_fn() {
    run_test("fn f<T>(x: T) -> T { x }")
}

#[test]
fn test_item_fn_variadic() {
    run_test("unsafe extern \"C\" fn f(x: i32, ...) -> i32 { x }")
}

#[test]
fn test_item_foreign_mod_static() {
    run_test("extern \"C\" { static mut X: i32; }")
}

#[test]
fn test_item_foreign_fn() {
    run_test("extern \"C\" { fn f() -> i32; }")
}

#[test]
fn test_item_foreign_fn_vararg() {
    run_test("extern \"C\" { fn f(...) -> i32; }")
}

#[test]
fn test_item_foreign_mod_ty_alias() {
    run_test("extern \"C\" { type T; }")
}

#[test]
fn test_item_ty_alias() {
    run_test("type X<T> = T;")
}

#[test]
fn test_item_enum() {
    run_test("enum X<T: Clone> { A = 0, B(T), C { x: T } }")
}

#[test]
fn test_item_struct() {
    run_test("struct X<T: Clone> { x: T, y: i32, z: i32 = 0 }")
}

#[test]
fn test_item_struct_tuple() {
    run_test("struct X<T: Clone>(T, i32);")
}

#[test]
fn test_item_union() {
    run_test("union X<T: Clone> { x: T, y: i32 }")
}

#[test]
fn test_item_trait() {
    run_test(
        "
        trait X<T: Clone>: Clone {
            type Y: Clone;
            type Z = i32;
            const N: i32;
            fn new() -> Self;
            fn f<A>(self, x: A) -> A { x }
        }",
    )
}

#[test]
fn test_item_trait_alias() {
    run_test("trait X<T: Clone> = Clone + Send;")
}

#[test]
fn test_item_impl() {
    run_test(
        "
        struct S<T>;
        trait X<T: Clone>: Clone {
            type Y: Clone;
            type Z = i32;
            const N: i32;
            fn new() -> Self;
            fn f<A>(self, x: A) -> A { x }
        }
        impl<T: Clone> X<T> for S<T> {
            type Y = i32;
            const N: i32 = 0;
            fn new() -> Self { Self }
            fn f<A>(self, x: A) -> A { x }
        }",
    )
}

#[test]
fn test_expr_array() {
    run_test(
        "
        fn f() {
            [1, 2, 3][0];
        }",
    )
}

#[test]
fn test_expr_const_block() {
    run_test(
        "
        fn f() {
            const { 1 + 2 };
        }",
    )
}

#[test]
fn test_expr_call() {
    run_test(
        "
        fn g(x: i32, y: i32) -> i32 {
            x + y
        }
        fn f() {
            g(1, 2);
        }",
    )
}

#[test]
fn test_expr_method_call() {
    run_test(
        "
        struct A;
        impl A {
            fn f(self, x: i32) -> i32 {
                -x + 1
            }
        }
        fn f() {
            A.f(1);
        }",
    )
}

#[test]
fn test_expr_tup() {
    run_test(
        "
        fn f() {
            (1, 2, 3);
        }",
    )
}

#[test]
fn test_expr_cast() {
    run_test(
        "
        fn f() {
            1.0 as i32;
        }",
    )
}

#[test]
fn test_expr_let() {
    run_test(
        "
        fn f() {
            if let 0 = 0 {}
        }",
    )
}

#[test]
fn test_expr_if() {
    run_test(
        "
        fn f() {
            if true {
                1;
            } else if true {
                2;
            } else {
                3;
            }
        }",
    )
}

#[test]
fn test_expr_while() {
    run_test(
        "
        fn f() {
            'l: while true {
                1;
            }
        }",
    )
}

#[test]
fn test_expr_for_loop() {
    run_test(
        "
        fn f() {
            'l: for x in 0..10 {
                x;
            }
        }",
    )
}

#[test]
fn test_expr_loop() {
    run_test(
        "
        fn f() {
            'l: loop {
                1;
                break 'l 1;
                continue 'l;
            };
        }",
    )
}

#[test]
fn test_expr_match() {
    run_test(
        "
        fn f() {
            match true {
                true if true => 1,
                true => 2,
                false => 3,
            };
        }",
    )
}

#[test]
fn test_expr_closure() {
    run_test(
        "
        fn f() {
            |x: i32| x;
            for<'a> |_: &'a (), x: i32| -> i32 {
                x
            };
        }",
    )
}

#[test]
fn test_expr_assign() {
    run_test(
        "
        fn f() {
            let x;
            x = 0;
        }",
    )
}

#[test]
fn test_expr_assign_op() {
    run_test(
        "
        fn f() {
            let mut x = 0;
            x += 1;
        }",
    )
}

#[test]
fn test_expr_field() {
    run_test(
        "
        struct S { x: i32 }
        fn f() {
            S { x: 1 }.x;
        }",
    )
}

#[test]
fn test_expr_range() {
    run_test(
        "
        fn f() {
            0..10;
            0..=10;
            ..10;
            ..=10;
            0..;
            ..;
        }",
    )
}

#[test]
fn test_expr_addr_of() {
    run_test(
        "
        fn f() {
            let x = 0;
            &x;
        }",
    )
}

#[test]
fn test_expr_return() {
    run_test(
        "
        fn f() -> i32 {
            return 0;
        }",
    )
}

#[test]
fn test_expr_struct() {
    run_test(
        "
        struct S { x: i32, y: i32 }
        fn f() {
            let s = S { x: 1, y: 2 };
            S { x: 3, ..s };
        }",
    )
}

#[test]
fn test_expr_repeat() {
    run_test(
        "
        fn f() {
            [1; 10];
        }",
    )
}

#[test]
fn test_expr_paren() {
    run_test(
        "
        fn f() {
            (1);
        }",
    )
}

#[test]
fn test_expr_binary() {
    run_test(
        "
        fn f() {
            ((1 + 2) < (3 - 4)) && ((5 * 6) < (7 / 8)) ||
                ((1 << 2) < (3 >> 4)) && ((5 | 6) < (7 & 8));
        }",
    )
}

#[test]
fn test_stmt_let() {
    run_test(
        "
        fn f() {
            let Some(x) = Some(0) else { return };
        }",
    )
}

#[test]
fn test_stmt_item() {
    run_test(
        "
        fn f() {
            static mut X: i32 = 0;
        }",
    )
}

#[test]
fn test_stmt_expr() {
    run_test(
        "
        fn f() {
            if true {} else {}
            0;
        }",
    )
}

#[test]
fn test_qpath() {
    run_test(
        "
        trait T<V> {
            type A;
        }
        struct S;
        impl<V> T<V> for S {
            type A = X<V>;
        }
        struct X<V> { x: V }
        fn f() {
            <S as T<i32>>::A { x: 0 };
            X::<i32> { x: 0 };
        }",
    )
}

#[test]
fn test_pat_binding() {
    run_test(
        "
        fn f() {
            match Some(0) {
                x @ Some(y) => {}
                _ => {}
            }
        }",
    )
}

#[test]
fn test_pat_binding_expr() {
    run_test(
        "
        struct S;
        fn f() {
            match S {
                S => {}
            }
        }",
    )
}

#[test]
fn test_pat_struct() {
    run_test(
        "
        fn f() {
            struct S { x: i32, y: i32, z: i32 }
            match (S { x: 0, y: 1, z: 2 }) {
                S { x, y: yy, .. } => {}
            }
        }",
    )
}

#[test]
fn test_pat_tuple_struct() {
    run_test(
        "
        fn f() {
            struct S(i32, i32, i32);
            match S(0, 1, 2) {
                S(0, 0, 0) => {}
                S(0, .., 1) => {}
                S(.., 0, 2) => {}
                S(.., 3) => {}
                S(1, 0, ..) => {}
                S(2, ..) => {}
                S(..) => {}
            }
        }",
    )
}

#[test]
fn test_pat_or() {
    run_test(
        "
        fn f() {
            match 0 {
                -1 | 0 | 1 => {}
                _ => {}
            }
        }",
    )
}

#[test]
fn test_pat_path() {
    run_test(
        "
        trait T<V> {
            type A;
        }
        struct S;
        impl<V> T<V> for S {
            type A = X<V>;
        }
        struct X<V> { x: V }
        fn f() {
            match (X::<i32> { x: 0 }) {
                <S as T<i32>>::A { x: 0 } => {}
            }
        }",
    )
}

#[test]
fn test_pat_tuple() {
    run_test(
        "
        fn f() {
            match (0, 1, 2) {
                (0, 0, 0) => {}
                (0, .., 1) => {}
                (.., 0, 2) => {}
                (.., 3) => {}
                (1, 0, ..) => {}
                (2, ..) => {}
                (..) => {}
            }
        }",
    )
}

#[test]
fn test_pat_box() {
    run_test(
        "
        fn f() {
            match Box::new(0) {
                box x => {}
            }
        }",
    )
}

#[test]
fn test_pat_ref() {
    run_test(
        "
        fn f() {
            match 0 {
                ref x => {}
            }
        }",
    )
}

#[test]
fn test_pat_range() {
    run_test(
        "
        fn f() {
            match 0 {
                0..10 => {}
                10.. => {}
                ..0 => {}
            }
        }",
    )
}

#[test]
fn test_pat_slice() {
    run_test(
        "
        fn f() {
            match [1, 2, 3].as_slice() {
                [0, 0, 0] => {}
                [0, .., 1] => {}
                [0, x @ .., 2] => {}
                [.., 3] => {}
                [x @ .., 4] => {}
                [1, ..] => {}
                [2, x @ ..] => {}
                [..] => {}
                [x @ ..] => {}
            }
        }",
    )
}

#[test]
fn test_pat_paren() {
    run_test(
        "
        fn f() {
            match 0 {
                (x) => {}
            }
        }",
    )
}

#[test]
fn test_ty_slice() {
    run_test(
        "
        fn f<'a>(x: &'a [i32]) {}
        ",
    )
}

#[test]
fn test_ty_array() {
    run_test(
        "
        fn f(x: [i32; 3]) {}
        ",
    )
}

#[test]
fn test_ty_ptr() {
    run_test(
        "
        fn f(x: *mut i32, y: *const i32) {}
        ",
    )
}

#[test]
fn test_ty_ref() {
    run_test(
        "
        fn f<'a>(x: &'a mut i32, y: &'a i32) {}
        ",
    )
}

#[test]
fn test_ty_bare_fn() {
    run_test(
        "
        struct S<'a>(&'a i32);
        fn f(x: fn (i32, i32, S) -> i32) {}
        ",
    )
}

#[test]
fn test_ty_unsafe_binder() {
    run_test(
        "
        fn f(x: unsafe<'a> &'a ()) {}
        ",
    )
}

#[test]
fn test_ty_never() {
    run_test(
        "
        fn f() -> ! { loop {} }
        ",
    )
}

#[test]
fn test_ty_tup() {
    run_test(
        "
        fn f(x: (i32, i32, i32)) {}
        ",
    )
}

#[test]
fn test_ty_path() {
    run_test(
        "
        struct S<T>(T);
        fn f(x: S<i32>) {}
        ",
    )
}

#[test]
fn test_ty_trait_object() {
    run_test(
        "
        trait A {}
        fn f(x: Box<dyn A + Send + 'static>) {}
        ",
    )
}

#[test]
fn test_ty_impl_trait() {
    run_test(
        "
        fn f() -> impl Send + 'static { 1 }
        ",
    )
}

#[test]
fn test_ty_impl_trait_param() {
    run_test(
        "
        trait A {}
        fn f(x: impl A + Send + 'static) {}
        ",
    )
}

#[test]
fn test_generics() {
    run_test(
        "
        fn f<'a, 'b: 'a, T: Copy, const A: bool>(x: &'a &'b T) where T: Send, 'b: 'static {}
        ",
    )
}

#[test]
fn test_generic_args_parenthesized() {
    run_test(
        "
        fn f<F: Fn(), G: Fn(u32), H: Fn(u32) -> u32>(f: F, g: G, h: H) {}
        ",
    )
}

#[test]
fn test_assoc_item_constraint_kind_equality() {
    run_test(
        "
        trait T<A> {
            type X;
        }
        fn f<A: T<i32, X = i32>>(a: A) {}
        ",
    )
}

#[test]
fn test_stmt_mac_call_asm() {
    run_test(
        r#"
        fn f(a: i32, b: i32) -> i32 {
            let mut sum = a;
            unsafe {
                std::arch::asm!(
                    "add {sum}, {b}",
                    sum = inout(reg) sum,
                    b   = in(reg) b,
                    options(pure, nomem, nostack),
                );
            }
            sum
        }"#,
    )
}

#[test]
fn test_expr_mac_call_format_0() {
    run_test(
        r#"
        fn f(x: i32) {
            format!("");
        }"#,
    )
}

#[test]
fn test_expr_mac_call_format_0_lit() {
    run_test(
        r#"
        fn f(x: i32) {
            format!("{}", 1);
        }"#,
    )
}

#[test]
fn test_expr_mac_call_format_1() {
    run_test(
        r#"
        fn f(x: i32) {
            format!("{}", x);
        }"#,
    )
}

#[test]
fn test_expr_mac_call_format_1_lit() {
    run_test(
        r#"
        fn f(x: i32) {
            format!("{} {}", x + x, 1);
        }"#,
    )
}

#[test]
fn test_expr_mac_call_format_2() {
    run_test(
        r#"
        fn f(x: i32) {
            format!("{} {}", x + x, x);
        }"#,
    )
}

#[test]
fn test_expr_mac_call_format_2_lit() {
    run_test(
        r#"
        fn f(x: i32) {
            format!("{} {} {} {}", x + x, 1, x, 1);
        }"#,
    )
}

#[test]
fn test_expr_mac_call_format_3() {
    run_test(
        r#"
        fn f(x: i32) {
            format!("{} {} {}", x + x, x, x);
        }"#,
    )
}

#[test]
fn test_expr_mac_call_format_3_lit() {
    run_test(
        r#"
        fn f(x: i32) {
            format!("{} {} {} {} {} {}", x, 1, x, 1, x, 1);
        }"#,
    )
}

#[test]
fn test_expr_mac_call() {
    run_test(
        r#"
        fn f() {
            let _ = panic!();
            let _ = unreachable!();
        }
        "#,
    )
}

#[test]
fn test_stmt_mac_call() {
    run_test(
        r#"
        fn f() {
            1;
            panic!();
            1;
            unreachable!();
            1;
        }
        "#,
    )
}

#[test]
fn test_generic_arg_infer() {
    run_test(
        "
        fn g<T>(x: T) {}
        fn f() {
            g::<_>(0);
        }
        ",
    )
}

#[test]
fn test_adjustment_deref_some() {
    run_test(
        "
        struct S(i32);
        impl std::ops::Deref for S {
            type Target = i32;
            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }
        fn f() {
            S(0).overflowing_add(1);
        }
        ",
    )
}

#[test]
fn test_adjustment_borrow_raw_ptr() {
    run_test(
        "
        fn f() {
            let p: *mut i32 = &mut 0;
        }
        ",
    )
}

#[test]
fn test_adjustment_pointer() {
    run_test(
        "
        trait T {}
        struct S;
        impl T for S {}
        fn f() {
            let x: &dyn T = &S;
        }
        ",
    )
}
