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
                1 as core::ffi::c_uint
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
fn enum_integer_comparison_records_cast() {
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
            assert_eq!(info.enum_to_int_cast_sites.len(), 1);
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
                unknown()
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
