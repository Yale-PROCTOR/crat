use super::*;

fn analyze(code: &str) -> EnumAnalysis {
    let code = format!(
        r#"
            #![allow(dead_code)]
            #![allow(non_camel_case_types)]
            #![allow(non_snake_case)]
            #![allow(non_upper_case_globals)]

            {code}
            "#
    );
    utils::compilation::run_compiler_on_str(&code, analyze_enums).unwrap()
}

fn transform(code: &str) -> String {
    let code = format!(
        r#"
            #![allow(dead_code)]
            #![allow(non_camel_case_types)]
            #![allow(non_snake_case)]
            #![allow(non_upper_case_globals)]

            {code}
            "#
    );
    utils::compilation::run_compiler_on_str(&code, replace_enums).unwrap()
}

fn transform_and_compile(code: &str) -> String {
    let code = transform(code);
    utils::compilation::run_compiler_on_str(&code, utils::type_check).unwrap();
    code
}

fn enum_by_name<'a>(analysis: &'a EnumAnalysis, tcx: TyCtxt<'_>, name: &str) -> &'a EnumInfo {
    analysis
        .enums
        .iter()
        .find_map(|(alias, info)| {
            (tcx.item_name(alias.to_def_id()).as_str() == name).then_some(info)
        })
        .unwrap()
}

fn analyze_with_tcx<R: Send>(
    code: &str,
    f: impl FnOnce(TyCtxt<'_>, EnumAnalysis) -> R + Send,
) -> R {
    let code = format!(
        r#"
            #![allow(dead_code)]
            #![allow(non_camel_case_types)]
            #![allow(non_snake_case)]
            #![allow(non_upper_case_globals)]

            {code}
            "#
    );
    utils::compilation::run_compiler_on_str(&code, |tcx| f(tcx, analyze_enums(tcx))).unwrap()
}

fn has_reject(info: &EnumInfo, kind: RejectReasonKind) -> bool {
    info.reject_reasons.iter().any(|reason| reason.kind == kind)
}

#[test]
fn detect_simple_c_enum() {
    analyze_with_tcx(
        r#"
            pub type E = core::ffi::c_uint;
            pub const C: E = 2;
            pub const B: E = 1;
            pub const A: E = 0;

            pub unsafe extern "C" fn f() -> E {
                A
            }
            "#,
        |tcx, analysis| {
            let info = enum_by_name(&analysis, tcx, "E");
            assert!(info.transformable);
            assert_eq!(
                info.variants
                    .iter()
                    .map(|v| (v.name.as_str().to_string(), v.value))
                    .collect::<Vec<_>>(),
                vec![
                    ("A".to_string(), DiscriminantValue::Unsigned(0)),
                    ("B".to_string(), DiscriminantValue::Unsigned(1)),
                    ("C".to_string(), DiscriminantValue::Unsigned(2)),
                ]
            );
            assert!(info.reject_reasons.is_empty());
            assert!(info.enum_to_int_cast_sites.is_empty());
        },
    );
}

#[test]
fn sort_variants_by_discriminant() {
    analyze_with_tcx(
        r#"
            pub type E = core::ffi::c_uint;
            pub const C: E = 10;
            pub const A: E = 0;
            pub const B: E = 3;

            pub unsafe extern "C" fn f() -> E {
                B
            }
            "#,
        |tcx, analysis| {
            let info = enum_by_name(&analysis, tcx, "E");
            assert!(info.transformable);
            assert_eq!(
                info.variants
                    .iter()
                    .map(|v| v.name.as_str().to_string())
                    .collect::<Vec<_>>(),
                vec!["A", "B", "C"]
            );
        },
    );
}

#[test]
fn reject_duplicate_discriminants() {
    analyze_with_tcx(
        r#"
            pub type E = core::ffi::c_uint;
            pub const A: E = 0;
            pub const ALSO_A: E = 0;

            pub unsafe extern "C" fn f() -> E {
                A
            }
            "#,
        |tcx, analysis| {
            let info = enum_by_name(&analysis, tcx, "E");
            assert!(!info.transformable);
            assert!(has_reject(info, RejectReasonKind::DuplicateDiscriminant));
            assert!(info.enum_to_int_cast_sites.is_empty());
        },
    );
}

#[test]
fn reject_integer_literal_assigned_to_enum() {
    analyze_with_tcx(
        r#"
            pub type E = core::ffi::c_uint;
            pub const A: E = 0;
            pub const B: E = 1;

            pub unsafe extern "C" fn f() -> E {
                let mut e: E = 0 as core::ffi::c_uint;
                e = B;
                e
            }
            "#,
        |tcx, analysis| {
            let info = enum_by_name(&analysis, tcx, "E");
            assert!(!info.transformable);
            assert!(
                has_reject(info, RejectReasonKind::CastAssignedToEnum)
                    || has_reject(info, RejectReasonKind::IntegerLiteralAssignedToEnum)
            );
        },
    );
}

#[test]
fn reject_arithmetic_assigned_to_enum() {
    analyze_with_tcx(
        r#"
            pub type E = core::ffi::c_uint;
            pub const A: E = 0;
            pub const B: E = 1;

            pub unsafe extern "C" fn f() -> E {
                let mut e: E = A;
                e = A + B;
                e
            }
            "#,
        |tcx, analysis| {
            let info = enum_by_name(&analysis, tcx, "E");
            assert!(!info.transformable);
            assert!(has_reject(info, RejectReasonKind::ArithmeticAssignedToEnum));
        },
    );
}

#[test]
fn accept_enum_flow_through_locals_params_returns_fields() {
    analyze_with_tcx(
        r#"
            pub type E = core::ffi::c_uint;
            pub const A: E = 0;
            pub const B: E = 1;

            pub struct S {
                pub tag: E,
            }

            pub unsafe extern "C" fn id(mut x: E) -> E {
                let mut y: E = x;
                y = B;
                y
            }

            pub unsafe extern "C" fn f() -> E {
                let s: S = S { tag: A };
                id(s.tag)
            }
            "#,
        |tcx, analysis| {
            let info = enum_by_name(&analysis, tcx, "E");
            assert!(info.transformable);
            assert!(info.reject_reasons.is_empty());
            assert!(info.enum_to_int_cast_sites.is_empty());
        },
    );
}

#[test]
fn accept_pointer_dereference_as_enum_source() {
    analyze_with_tcx(
        r#"
            pub type E = core::ffi::c_uint;
            pub const A: E = 0;
            pub const B: E = 1;

            pub unsafe extern "C" fn f(mut p: *mut E) -> E {
                *p = A;
                let x: E = *p;
                x
            }
            "#,
        |tcx, analysis| {
            let info = enum_by_name(&analysis, tcx, "E");
            assert!(info.transformable);
            assert!(info.reject_reasons.is_empty());
            assert!(info.enum_to_int_cast_sites.is_empty());
        },
    );
}

#[test]
fn reject_wrong_argument_for_enum_parameter() {
    analyze_with_tcx(
        r#"
            pub type E = core::ffi::c_uint;
            pub const A: E = 0;
            pub const B: E = 1;

            pub unsafe extern "C" fn takes_e(mut x: E) -> E {
                x
            }

            pub unsafe extern "C" fn f() -> E {
                takes_e(1 as core::ffi::c_uint)
            }
            "#,
        |tcx, analysis| {
            let info = enum_by_name(&analysis, tcx, "E");
            assert!(!info.transformable);
            assert!(
                has_reject(info, RejectReasonKind::FunctionArgumentRequiresEnum)
                    || has_reject(info, RejectReasonKind::CastAssignedToEnum)
            );
        },
    );
}

#[test]
fn reject_wrong_return_expression() {
    analyze_with_tcx(
        r#"
            pub type E = core::ffi::c_uint;
            pub const A: E = 0;
            pub const B: E = 1;

            pub unsafe extern "C" fn f() -> E {
                return 1 as core::ffi::c_uint;
            }
            "#,
        |tcx, analysis| {
            let info = enum_by_name(&analysis, tcx, "E");
            assert!(!info.transformable);
            assert!(
                has_reject(info, RejectReasonKind::ReturnRequiresEnum)
                    || has_reject(info, RejectReasonKind::CastAssignedToEnum)
            );
        },
    );
}

#[test]
fn accept_explicit_return_variants_without_tail_expr() {
    analyze_with_tcx(
        r#"
            pub type E = core::ffi::c_uint;
            pub const A: E = 0;
            pub const B: E = 1;

            pub unsafe extern "C" fn f(mut cond: core::ffi::c_int) -> E {
                if cond != 0 as core::ffi::c_int {
                    return A;
                }
                return B;
            }
            "#,
        |tcx, analysis| {
            let info = enum_by_name(&analysis, tcx, "E");
            assert!(info.transformable);
            assert!(info.reject_reasons.is_empty());
        },
    );
}

#[test]
fn accept_c_bool_style_flag_with_explicit_returns() {
    analyze_with_tcx(
        r#"
            pub type c_bool = core::ffi::c_int;
            pub const true_0: c_bool = 1 as core::ffi::c_int;
            pub const false_0: c_bool = 0 as core::ffi::c_int;

            pub unsafe extern "C" fn f(mut cond: core::ffi::c_int) -> c_bool {
                let mut seen: c_bool = false_0;
                if cond != 0 as core::ffi::c_int {
                    seen = true_0;
                }
                if seen != 0 as core::ffi::c_int {
                    return true_0;
                }
                return false_0;
            }
            "#,
        |tcx, analysis| {
            let info = enum_by_name(&analysis, tcx, "c_bool");
            assert!(info.transformable);
            assert!(info.reject_reasons.is_empty());
            assert!(info.enum_to_int_cast_sites.is_empty());
        },
    );
}

#[test]
fn record_enum_to_integer_assignment_cast() {
    analyze_with_tcx(
        r#"
            pub type E = core::ffi::c_uint;
            pub const A: E = 0;
            pub const B: E = 1;

            pub unsafe extern "C" fn f() -> core::ffi::c_uint {
                let e: E = B;
                let i: core::ffi::c_uint = e;
                i
            }
            "#,
        |tcx, analysis| {
            let info = enum_by_name(&analysis, tcx, "E");
            assert!(info.transformable);
            assert_eq!(info.enum_to_int_cast_sites.len(), 1);
        },
    );
}

#[test]
fn record_enum_operands_in_integer_arithmetic() {
    analyze_with_tcx(
        r#"
            pub type E = core::ffi::c_uint;
            pub const A: E = 0;
            pub const B: E = 1;

            pub unsafe extern "C" fn f() -> core::ffi::c_uint {
                let e: E = B;
                e + A + 3 as core::ffi::c_uint
            }
            "#,
        |tcx, analysis| {
            let info = enum_by_name(&analysis, tcx, "E");
            assert!(info.transformable);
            assert_eq!(info.enum_to_int_cast_sites.len(), 2);
        },
    );
}

#[test]
fn same_enum_comparisons_need_no_casts() {
    analyze_with_tcx(
        r#"
            pub type E = core::ffi::c_uint;
            pub const A: E = 0;
            pub const B: E = 1;

            pub unsafe extern "C" fn f(mut x: E, mut y: E) -> core::ffi::c_int {
                if x < y && x != A {
                    1
                } else {
                    0
                }
            }
            "#,
        |tcx, analysis| {
            let info = enum_by_name(&analysis, tcx, "E");
            assert!(info.transformable);
            assert!(info.enum_to_int_cast_sites.is_empty());
        },
    );
}

#[test]
fn enum_integer_comparison_rewrites_directly() {
    analyze_with_tcx(
        r#"
            pub type E = core::ffi::c_uint;
            pub const A: E = 0;
            pub const B: E = 1;

            pub unsafe extern "C" fn f(mut x: E) -> core::ffi::c_int {
                if x == 1 as core::ffi::c_uint {
                    1
                } else {
                    0
                }
            }
            "#,
        |tcx, analysis| {
            let info = enum_by_name(&analysis, tcx, "E");
            assert!(info.transformable);
            assert!(info.enum_to_int_cast_sites.is_empty());
        },
    );
}

#[test]
fn function_call_returning_enum_is_accepted() {
    analyze_with_tcx(
        r#"
            pub type E = core::ffi::c_uint;
            pub const A: E = 0;
            pub const B: E = 1;

            pub unsafe extern "C" fn g() -> E {
                A
            }

            pub unsafe extern "C" fn f() -> E {
                let x: E = g();
                x
            }
            "#,
        |tcx, analysis| {
            let info = enum_by_name(&analysis, tcx, "E");
            assert!(info.transformable);
            assert!(info.reject_reasons.is_empty());
            assert!(info.enum_to_int_cast_sites.is_empty());
        },
    );
}

#[test]
fn signed_repr_sorting() {
    analyze_with_tcx(
        r#"
            pub type E = core::ffi::c_int;
            pub const NEG: E = -1;
            pub const ZERO: E = 0;
            pub const POS: E = 1;

            pub unsafe extern "C" fn f() -> E {
                NEG
            }
            "#,
        |tcx, analysis| {
            let info = enum_by_name(&analysis, tcx, "E");
            assert!(matches!(info.repr, IntegerRepr::Signed(_)));
            assert_eq!(
                info.variants
                    .iter()
                    .map(|v| v.name.as_str().to_string())
                    .collect::<Vec<_>>(),
                vec!["NEG", "ZERO", "POS"]
            );
            assert!(info.transformable);
        },
    );
}

#[test]
fn non_enum_integer_alias_is_not_detected() {
    let analysis = analyze(
        r#"
            pub type Count = core::ffi::c_uint;
            pub static mut LIMIT: Count = 10;

            pub unsafe extern "C" fn f(mut x: Count) -> Count {
                x
            }
            "#,
    );
    assert!(analysis.enums.is_empty());
}

#[test]
fn alias_through_pointer_type() {
    analyze_with_tcx(
        r#"
            pub type E = core::ffi::c_uint;
            pub type EP = *mut E;
            pub const A: E = 0;
            pub const B: E = 1;

            pub unsafe extern "C" fn f(mut p: EP) -> E {
                *p = B;
                *p
            }
            "#,
        |tcx, analysis| {
            let info = enum_by_name(&analysis, tcx, "E");
            assert!(info.transformable);
            assert!(info.reject_reasons.is_empty());
            assert!(info.enum_to_int_cast_sites.is_empty());
        },
    );
}

#[test]
fn two_independent_enums() {
    analyze_with_tcx(
        r#"
            pub type E1 = core::ffi::c_uint;
            pub const E1_A: E1 = 0;
            pub const E1_B: E1 = 1;

            pub type E2 = core::ffi::c_uint;
            pub const E2_A: E2 = 0;
            pub const E2_B: E2 = 1;

            pub unsafe extern "C" fn f(mut x: E1, mut y: E2) -> E1 {
                x = E1_A;
                y = E2_B;
                x
            }
            "#,
        |tcx, analysis| {
            let e1 = enum_by_name(&analysis, tcx, "E1");
            let e2 = enum_by_name(&analysis, tcx, "E2");
            assert!(e1.transformable);
            assert!(e2.transformable);
            assert!(e1.enum_to_int_cast_sites.is_empty());
            assert!(e2.enum_to_int_cast_sites.is_empty());
        },
    );
}

#[test]
fn reject_assigning_wrong_enum() {
    analyze_with_tcx(
        r#"
            pub type E1 = core::ffi::c_uint;
            pub const E1_A: E1 = 0;
            pub const E1_B: E1 = 1;

            pub type E2 = core::ffi::c_uint;
            pub const E2_A: E2 = 0;
            pub const E2_B: E2 = 1;

            pub unsafe extern "C" fn f(mut y: E2) -> E1 {
                let x: E1 = y;
                x
            }
            "#,
        |tcx, analysis| {
            let e1 = enum_by_name(&analysis, tcx, "E1");
            assert!(!e1.transformable);
            assert!(has_reject(e1, RejectReasonKind::WrongEnumAssignedToEnum));
        },
    );
}

#[test]
fn unknown_enum_required_source_rejects() {
    analyze_with_tcx(
        r#"
            pub type E = core::ffi::c_uint;
            pub const A: E = 0;
            pub const B: E = 1;

            unsafe extern "C" {
                fn unknown() -> core::ffi::c_uint;
            }

            pub unsafe extern "C" fn f() -> E {
                return unknown();
            }
            "#,
        |tcx, analysis| {
            let info = enum_by_name(&analysis, tcx, "E");
            assert!(!info.transformable);
            assert!(
                has_reject(info, RejectReasonKind::ReturnRequiresEnum)
                    || has_reject(info, RejectReasonKind::UnknownExpressionAssignedToEnum)
            );
        },
    );
}

#[test]
fn transform_simple_c_enum() {
    let code = transform_and_compile(
        r#"
            pub type E = core::ffi::c_uint;
            pub const C: E = 2;
            pub const A: E = 0;
            pub const B: E = 1;

            pub unsafe extern "C" fn f() -> E {
                A
            }
            "#,
    );

    assert!(code.contains("#[repr(u32)]"));
    assert!(code.contains("#![feature(coverage_attribute)]"));
    assert!(code.contains("#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]"));
    assert!(code.contains("pub enum E"));
    assert!(code.contains("A = 0u32"));
    assert!(code.contains("B = 1u32"));
    assert!(code.contains("C = 2u32"));
    assert!(code.find("A = 0u32").unwrap() < code.find("B = 1u32").unwrap());
    assert!(code.find("B = 1u32").unwrap() < code.find("C = 2u32").unwrap());
    assert!(code.contains("pub use E::A;"));
    assert!(code.contains("pub use E::B;"));
    assert!(code.contains("pub use E::C;"));
    assert!(!code.contains("type E ="));
    assert!(!code.contains("pub const A"));
    assert!(!code.contains("pub const B"));
    assert!(!code.contains("pub const C"));
}

#[test]
fn transform_signed_repr() {
    let code = transform_and_compile(
        r#"
            pub type E = core::ffi::c_int;
            pub const POS: E = 1;
            pub const NEG: E = -1;
            pub const ZERO: E = 0;

            pub unsafe extern "C" fn f() -> E {
                NEG
            }
            "#,
    );

    assert!(code.contains("#[repr(i32)]"));
    assert!(code.contains("NEG = -1i32"));
    assert!(code.contains("ZERO = 0i32"));
    assert!(code.contains("POS = 1i32"));
    assert!(code.find("NEG = -1i32").unwrap() < code.find("ZERO = 0i32").unwrap());
    assert!(code.find("ZERO = 0i32").unwrap() < code.find("POS = 1i32").unwrap());
}

#[test]
fn transform_inserts_enum_to_integer_casts() {
    let code = transform_and_compile(
        r#"
            pub type E = core::ffi::c_uint;
            pub const A: E = 0;
            pub const B: E = 1;

            pub unsafe extern "C" fn takes_int(x: core::ffi::c_uint) -> core::ffi::c_uint {
                x
            }

            pub unsafe extern "C" fn f() -> core::ffi::c_uint {
                let e: E = B;
                let mut i: core::ffi::c_uint = e;
                i = i + A + e;
                if e == 1 as core::ffi::c_uint {
                    i = i + takes_int(e);
                }
                return e;
            }
            "#,
    );

    assert!(code.contains("as u32"));
    assert!(code.contains("takes_int((e) as u32)"));
    assert!(code.contains("return (e) as u32;"));
    assert!(code.contains("if e == crate::E::B"));
    assert!(!code.contains("if (e) as u32 == 1"));
}

#[test]
fn transform_rewrites_cast_targets_to_repr() {
    let code = transform_and_compile(
        r#"
            pub type E = core::ffi::c_uint;
            pub const A: E = 0;
            pub const B: E = 1;

            pub unsafe extern "C" fn f(x: u8) -> core::ffi::c_uint {
                x as E as core::ffi::c_uint
            }
            "#,
    );

    assert!(code.contains("x as u32 as core::ffi::c_uint"));
    assert!(!code.contains("x as E as core::ffi::c_uint"));
}

#[test]
fn transform_avoids_unnecessary_casts() {
    let code = transform_and_compile(
        r#"
            pub type E = core::ffi::c_uint;
            pub const A: E = 0;
            pub const B: E = 1;

            pub unsafe extern "C" fn f(x: E) -> E {
                let y: E = x;
                if y == A {
                    y
                } else {
                    B
                }
            }
            "#,
    );

    assert!(!code.contains(" as u32"));
}

#[test]
fn transform_rewrites_casted_enum_variant_comparison() {
    let code = transform_and_compile(
        r#"
            pub type Token = core::ffi::c_uint;
            pub const TOKEN_EOF: Token = 0;
            pub const TOKEN_WORD: Token = 1;

            pub struct TokenState {
                pub type_0: Token,
            }

            pub unsafe extern "C" fn f(token: TokenState) -> core::ffi::c_int {
                if token.type_0 as core::ffi::c_uint !=
                    TOKEN_EOF as core::ffi::c_int as core::ffi::c_uint
                {
                    1
                } else {
                    0
                }
            }
            "#,
    );

    assert!(code.contains("token.type_0 != TOKEN_EOF"));
    assert!(!code.contains("token.type_0 as core::ffi::c_uint !="));
    assert!(!code.contains("TOKEN_EOF as core::ffi::c_int as core::ffi::c_uint"));
}

#[test]
fn transform_rewrites_enum_literal_comparison() {
    let code = transform_and_compile(
        r#"
            pub type c_bool = core::ffi::c_int;
            pub const false_0: c_bool = 0 as core::ffi::c_int;
            pub const true_0: c_bool = 1 as core::ffi::c_int;

            pub unsafe extern "C" fn f(has_decimal_point: c_bool) -> core::ffi::c_int {
                if (has_decimal_point) as i32 != 0 {
                    1
                } else {
                    0
                }
            }
            "#,
    );

    assert!(code.contains("has_decimal_point != crate::c_bool::false_0"));
    assert!(!code.contains("(has_decimal_point) as i32 != 0"));
}

#[test]
fn transform_rewrites_uncast_enum_literal_comparison() {
    let code = transform_and_compile(
        r#"
            pub type E = core::ffi::c_uint;
            pub const A: E = 0;
            pub const B: E = 1;

            pub unsafe extern "C" fn f(x: E) -> core::ffi::c_int {
                if x == 1 as core::ffi::c_uint {
                    1
                } else {
                    0
                }
            }
            "#,
    );

    assert!(code.contains("if x == crate::E::B"));
    assert!(!code.contains("x == 1 as core::ffi::c_uint"));
    assert!(!code.contains("(x) as u32"));
}

#[test]
fn transform_rewrites_literal_on_left() {
    let code = transform_and_compile(
        r#"
            pub type E = core::ffi::c_uint;
            pub const A: E = 0;
            pub const B: E = 1;

            pub unsafe extern "C" fn f(x: E) -> core::ffi::c_int {
                if 0 as core::ffi::c_uint == x as core::ffi::c_uint {
                    1
                } else {
                    0
                }
            }
            "#,
    );

    assert!(code.contains("if crate::E::A == x"));
    assert!(!code.contains("0 as core::ffi::c_uint == x as core::ffi::c_uint"));
}

#[test]
fn transform_rewrites_lowercase_literal_variant() {
    let code = transform_and_compile(
        r#"
            pub type c_bool = core::ffi::c_int;
            pub const false_0: c_bool = 0 as core::ffi::c_int;
            pub const true_0: c_bool = 1 as core::ffi::c_int;

            pub unsafe extern "C" fn f(x: c_bool) -> core::ffi::c_int {
                if x == 0 as core::ffi::c_int {
                    1
                } else {
                    0
                }
            }
            "#,
    );

    assert!(code.contains("x == crate::c_bool::false_0"));
    assert!(!code.contains("if x == false_0"));
}

#[test]
fn skip_enum_literal_comparison_unknown_value() {
    let code = transform_and_compile(
        r#"
            pub type E = core::ffi::c_uint;
            pub const A: E = 0;
            pub const B: E = 1;

            pub unsafe extern "C" fn f(x: E) -> core::ffi::c_int {
                if x == 2 as core::ffi::c_uint {
                    1
                } else {
                    0
                }
            }
            "#,
    );

    assert!(code.contains("if (x) as u32 == 2 as core::ffi::c_uint"));
    assert!(!code.contains("x == crate::E::"));
}

#[test]
fn skip_enum_literal_comparison_colliding_cast() {
    let code = transform_and_compile(
        r#"
            pub type E = u16;
            pub const A: E = 0;
            pub const B: E = 256;

            pub unsafe extern "C" fn f(x: E) -> core::ffi::c_int {
                if x as u8 == 0 as u8 {
                    1
                } else {
                    0
                }
            }
            "#,
    );

    assert!(code.contains("if x as u8 == 0 as u8"));
    assert!(!code.contains("x == crate::E::A"));
}

#[test]
fn skip_casted_enum_comparison_different_cast_semantics() {
    let code = transform_and_compile(
        r#"
            pub type E = u32;
            pub const A: E = 0;
            pub const B: E = 2147483648;

            pub unsafe extern "C" fn f(x: E, y: E) -> core::ffi::c_int {
                if x as i32 as i64 == y as u32 as i64 {
                    1
                } else {
                    0
                }
            }
            "#,
    );

    assert!(code.contains("if x as i32 as i64 == y as u32 as i64"));
    assert!(!code.contains("if x == y"));
}

#[test]
fn skip_casted_enum_relational_when_order_changes() {
    let code = transform_and_compile(
        r#"
            pub type E = u32;
            pub const A: E = 0;
            pub const B: E = 2147483648;

            pub unsafe extern "C" fn f(x: E, y: E) -> core::ffi::c_int {
                if (x as i32) < (y as i32) {
                    1
                } else {
                    0
                }
            }
            "#,
    );

    assert!(code.contains("if (x as i32) < (y as i32)"));
    assert!(!code.contains("if x < y"));
}

#[test]
fn skip_different_enum_comparison() {
    let code = transform_and_compile(
        r#"
            pub type E1 = u32;
            pub const E1_A: E1 = 0;
            pub const E1_B: E1 = 1;

            pub type E2 = u32;
            pub const E2_A: E2 = 0;
            pub const E2_B: E2 = 1;

            pub unsafe extern "C" fn f(x: E1, y: E2) -> core::ffi::c_int {
                if x as u32 == y as u32 {
                    1
                } else {
                    0
                }
            }
            "#,
    );

    assert!(code.contains("if x as u32 == y as u32"));
    assert!(!code.contains("if x == y"));
}

#[test]
fn skip_non_enum_cast_chain_comparison() {
    let code = transform_and_compile(
        r#"
            pub type E = core::ffi::c_uint;
            pub const A: E = 0;
            pub const B: E = 1;

            pub unsafe extern "C" fn f(mode: u8) -> core::ffi::c_int {
                if mode as u32 as core::ffi::c_uint != 0 {
                    1
                } else {
                    0
                }
            }
            "#,
    );

    assert!(code.contains("if mode as u32 as core::ffi::c_uint != 0"));
}

#[test]
fn transform_preserves_rejected_aliases() {
    let code = transform_and_compile(
        r#"
            pub type E = core::ffi::c_uint;
            pub const A: E = 0;
            pub const ALSO_A: E = 0;

            pub unsafe extern "C" fn f() -> E {
                A
            }
            "#,
    );

    assert!(code.contains("type E ="));
    assert!(code.contains("pub const A"));
    assert!(code.contains("pub const ALSO_A"));
    assert!(!code.contains("enum E"));
}

#[test]
fn transform_exports_variants_inside_module() {
    let mut code = transform(
        r#"
            pub mod m {
                pub type E = core::ffi::c_uint;
                pub const A: E = 0;
                pub const B: E = 1;
            }
            "#,
    );

    assert!(code.contains("pub enum E"));
    assert!(code.contains("pub use E::A;"));
    assert!(code.contains("pub use E::B;"));
    code.push_str(
        r#"
            pub fn use_exported_variants() {
                let _ = m::E::A;
                let _ = m::A;
            }
            "#,
    );
    utils::compilation::run_compiler_on_str(&code, utils::type_check).unwrap();
}

#[test]
fn transform_preserves_visibility() {
    let code = transform_and_compile(
        r#"
            type Private = core::ffi::c_uint;
            const PRIVATE_A: Private = 0;

            pub(crate) type CrateVisible = core::ffi::c_uint;
            pub(crate) const CRATE_A: CrateVisible = 0;

            pub type Public = core::ffi::c_uint;
            pub const PUBLIC_A: Public = 0;
            "#,
    );

    assert!(code.contains("enum Private"));
    assert!(code.contains("use Private::PRIVATE_A;"));
    assert!(code.contains("pub(crate) enum CrateVisible"));
    assert!(code.contains("pub(crate) use CrateVisible::CRATE_A;"));
    assert!(code.contains("pub enum Public"));
    assert!(code.contains("pub use Public::PUBLIC_A;"));
}

#[test]
fn transform_alias_through_pointer_compiles() {
    let code = transform_and_compile(
        r#"
            pub type E = core::ffi::c_uint;
            pub type EP = *mut E;
            pub const A: E = 0;
            pub const B: E = 1;

            pub unsafe extern "C" fn f(p: EP) -> E {
                *p = B;
                *p
            }
            "#,
    );

    assert!(code.contains("pub enum E"));
    assert!(code.contains("pub type EP = *mut E;"));
}

#[test]
fn transform_rewrites_enum_match() {
    let code = transform_and_compile(
        r#"
            pub type E = core::ffi::c_uint;
            pub const A: E = 0;
            pub const B: E = 1;

            pub unsafe extern "C" fn f(e: E) -> core::ffi::c_int {
                match e as core::ffi::c_uint {
                    0 => 10,
                    1 => 20,
                    _ => 0,
                }
            }
            "#,
    );

    assert!(code.contains("match e {"));
    assert!(code.contains("crate::E::A => 10"));
    assert!(code.contains("crate::E::B => 20"));
    assert!(!code.contains("match e as core::ffi::c_uint"));
}

#[test]
fn transform_removes_exhaustive_final_wildcard() {
    let code = transform_and_compile(
        r#"
            pub type E = u32;
            pub const A: E = 0;
            pub const B: E = 1;

            pub unsafe extern "C" fn f(e: E) -> u32 {
                match e as u32 {
                    0 => 10,
                    1 => 20,
                    _ => 30,
                }
            }
            "#,
    );

    assert!(code.contains("match e {"));
    assert!(!code.contains("_ => 30"));
}

#[test]
fn transform_keeps_partial_final_wildcard() {
    let code = transform_and_compile(
        r#"
            pub type E = u32;
            pub const A: E = 0;
            pub const B: E = 1;
            pub const C: E = 2;

            pub unsafe extern "C" fn f(e: E) -> u32 {
                match e as u32 {
                    0 => 10,
                    1 => 20,
                    _ => 30,
                }
            }
            "#,
    );

    assert!(code.contains("match e {"));
    assert!(code.contains("_ => 30"));
}

#[test]
fn transform_rewrites_or_pattern() {
    let code = transform_and_compile(
        r#"
            pub type Token = u32;
            pub const WORD: Token = 1;
            pub const IDENT: Token = 6;
            pub const OTHER: Token = 9;

            pub unsafe extern "C" fn f(token: Token) -> u32 {
                match token as u32 {
                    1 | 6 => 10,
                    9 => 20,
                    _ => 0,
                }
            }
            "#,
    );

    assert!(code.contains("crate::Token::WORD | crate::Token::IDENT => 10"));
}

#[test]
fn transform_uses_qualified_paths_for_lowercase_variants() {
    let code = transform_and_compile(
        r#"
            pub type c_bool = core::ffi::c_int;
            pub const false_0: c_bool = 0 as core::ffi::c_int;
            pub const true_0: c_bool = 1 as core::ffi::c_int;

            pub unsafe extern "C" fn f(b: c_bool) -> core::ffi::c_int {
                match b as core::ffi::c_int {
                    0 => 10,
                    1 => 20,
                    _ => 0,
                }
            }
            "#,
    );

    assert!(code.contains("crate::c_bool::false_0 => 10"));
    assert!(code.contains("crate::c_bool::true_0 => 20"));
    assert!(!code.contains("{ false_0 => 10"));
}

#[test]
fn transform_rewrites_enum_field_match() {
    let code = transform_and_compile(
        r#"
            pub type E = core::ffi::c_uint;
            pub const A: E = 0;
            pub const B: E = 1;

            pub struct S {
                pub tag: E,
            }

            pub unsafe extern "C" fn f(s: S) -> core::ffi::c_int {
                match s.tag as core::ffi::c_uint {
                    0 => 10,
                    1 => 20,
                    _ => 0,
                }
            }
            "#,
    );

    assert!(code.contains("match s.tag {"));
    assert!(code.contains("crate::E::A => 10"));
    assert!(code.contains("crate::E::B => 20"));
}

#[test]
fn transform_rewrites_signed_cast_target() {
    let code = transform_and_compile(
        r#"
            pub type Operation = core::ffi::c_uint;
            pub const OP_ADD: Operation = 1;
            pub const OP_SUB: Operation = 2;

            pub unsafe extern "C" fn f(op: Operation) -> core::ffi::c_int {
                match op as core::ffi::c_int {
                    1 => 10,
                    2 => 20,
                    _ => 0,
                }
            }
            "#,
    );

    assert!(code.contains("match op {"));
    assert!(code.contains("crate::Operation::OP_ADD => 10"));
    assert!(code.contains("crate::Operation::OP_SUB => 20"));
}

#[test]
fn skip_non_enum_cast_chain_match() {
    let code = transform_and_compile(
        r#"
            pub type E = core::ffi::c_uint;
            pub const A: E = 0;
            pub const B: E = 1;

            pub unsafe extern "C" fn f(mode: u8) -> E {
                match mode as u32 as core::ffi::c_uint {
                    0 => A,
                    _ => B,
                }
            }
            "#,
    );

    assert!(code.contains("match mode as u32 as core::ffi::c_uint"));
}

#[test]
fn skip_unknown_numeric_arm() {
    let code = transform_and_compile(
        r#"
            pub type E = u32;
            pub const A: E = 0;
            pub const B: E = 1;

            pub unsafe extern "C" fn f(e: E) -> u32 {
                match e as u32 {
                    0 => 10,
                    2 => 20,
                    _ => 30,
                }
            }
            "#,
    );

    assert!(code.contains("match e as u32"));
    assert!(code.contains("2 => 20"));
}

#[test]
fn skip_colliding_casted_discriminants() {
    let code = transform_and_compile(
        r#"
            pub type E = u16;
            pub const A: E = 0;
            pub const B: E = 256;

            pub unsafe extern "C" fn f(e: E) -> u8 {
                match e as u8 {
                    0 => 10,
                    _ => 20,
                }
            }
            "#,
    );

    assert!(code.contains("match e as u8"));
}

#[test]
fn keep_wildcard_with_guard() {
    let code = transform_and_compile(
        r#"
            pub type E = u32;
            pub const A: E = 0;
            pub const B: E = 1;

            pub unsafe extern "C" fn f(e: E, cond: bool) -> u32 {
                match e as u32 {
                    0 if cond => 10,
                    1 => 20,
                    _ => 30,
                }
            }
            "#,
    );

    assert!(code.contains("crate::E::A if cond => 10"));
    assert!(code.contains("_ => 30"));
}
