use points_to::andersen;
use rustc_hash::FxHashSet;
use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::{mir::VarDebugInfoContents, ty::TyCtxt};

use super::analyze;
use crate::utils::rustc::RustProgram;

fn build_rust_program(tcx: TyCtxt<'_>) -> RustProgram<'_> {
    let mut functions = vec![];
    for maybe_owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        if matches!(item.kind, ItemKind::Fn { .. }) {
            functions.push(item.owner_id.def_id);
        }
    }
    RustProgram {
        tcx,
        functions,
        structs: vec![],
    }
}

#[derive(Default)]
struct AnalysisNames {
    params: FxHashSet<(String, String)>,
    locals: FxHashSet<(String, String)>,
}

fn run_analysis(code: &str) -> AnalysisNames {
    let code = format!(
        "
        #![allow(dead_code)]
        #![allow(improper_ctypes)]
        #![allow(unconditional_recursion)]
        #![allow(unreachable_code)]
        #![allow(unused_mut)]
        #![allow(unused_variables)]
        {code}
        "
    );

    ::utils::compilation::run_compiler_on_str(&code, |tcx| {
        let rust_program = build_rust_program(tcx);
        let arena = typed_arena::Arena::new();
        let tss = utils::ty_shape::get_ty_shapes(&arena, tcx, false);
        let andersen_config = andersen::Config {
            use_optimized_mir: false,
            c_exposed_fns: FxHashSet::default(),
        };
        let pre_points_to = andersen::pre_analyze(&andersen_config, &tss, tcx);
        let points_to_solutions = andersen::analyze(&andersen_config, &pre_points_to, &tss, tcx);
        let points_to = andersen::post_analyze(
            &andersen_config,
            pre_points_to,
            points_to_solutions,
            &tss,
            tcx,
        );
        let result = analyze(&rust_program, &points_to);
        let mut names = AnalysisNames::default();

        for (&did, non_null_params) in &result.non_null_params {
            let fn_name = tcx.item_name(did.to_def_id()).to_string();
            let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
            for var_debug_info in body.var_debug_info.iter() {
                let VarDebugInfoContents::Place(place) = &var_debug_info.value else {
                    continue;
                };
                let Some(local) = place.as_local() else {
                    continue;
                };
                if var_debug_info.argument_index.is_some() && non_null_params.contains(local) {
                    names
                        .params
                        .insert((fn_name.clone(), var_debug_info.name.as_str().to_string()));
                }
            }
        }

        for (&did, non_null_locals) in &result.non_null_locals {
            let fn_name = tcx.item_name(did.to_def_id()).to_string();
            let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
            for var_debug_info in body.var_debug_info.iter() {
                let VarDebugInfoContents::Place(place) = &var_debug_info.value else {
                    continue;
                };
                let Some(local) = place.as_local() else {
                    continue;
                };
                if non_null_locals.contains(local) {
                    names
                        .locals
                        .insert((fn_name.clone(), var_debug_info.name.as_str().to_string()));
                }
            }
        }

        names
    })
    .unwrap()
}

fn expect_non_null(code: &str, expected: &[(&str, &str)]) {
    let expected = expected
        .iter()
        .map(|(function, param)| ((*function).to_string(), (*param).to_string()))
        .collect::<FxHashSet<_>>();
    assert_eq!(run_analysis(code).params, expected);
}

fn expect_non_null_local_facts(
    code: &str,
    expected_present: &[(&str, &str)],
    expected_absent: &[(&str, &str)],
) {
    let locals = run_analysis(code).locals;
    for (function, local) in expected_present {
        assert!(
            locals.contains(&((*function).to_string(), (*local).to_string())),
            "expected {function}::{local} to be non-null; got {locals:?}",
        );
    }
    for (function, local) in expected_absent {
        assert!(
            !locals.contains(&((*function).to_string(), (*local).to_string())),
            "expected {function}::{local} to be nullable; got {locals:?}",
        );
    }
}

#[test]
fn direct_deref_before_return_is_non_null() {
    expect_non_null(
        "
        pub unsafe fn f(p: *const i32) -> i32 {
            *p
        }
        ",
        &[("f", "p")],
    );
}

#[test]
fn is_null_before_deref_is_nullable() {
    expect_non_null(
        "
        pub unsafe fn f(p: *const i32) -> i32 {
            if p.is_null() {
                return 0;
            }
            *p
        }
        ",
        &[],
    );
}

#[test]
fn one_branch_returns_before_proof_is_nullable() {
    expect_non_null(
        "
        pub unsafe fn f(p: *const i32, flag: bool) -> i32 {
            if flag {
                *p
            } else {
                0
            }
        }
        ",
        &[],
    );
}

#[test]
fn both_branches_deref_is_non_null() {
    expect_non_null(
        "
        pub unsafe fn f(p: *const i32, flag: bool) -> i32 {
            if flag {
                *p
            } else {
                *p
            }
        }
        ",
        &[("f", "p")],
    );
}

#[test]
fn alias_copy_deref_is_non_null() {
    expect_non_null(
        "
        pub unsafe fn f(p: *const i32) -> i32 {
            let q = p;
            *q
        }
        ",
        &[("f", "p")],
    );
}

#[test]
fn alias_cast_deref_is_non_null() {
    expect_non_null(
        "
        pub unsafe fn f(p: *mut i32) -> i32 {
            let q = p as *const i32;
            *q
        }
        ",
        &[("f", "p")],
    );
}

#[test]
fn is_null_on_alias_is_nullable() {
    expect_non_null(
        "
        pub unsafe fn f(p: *const i32) -> i32 {
            let q = p;
            if q.is_null() {
                return 0;
            }
            *p
        }
        ",
        &[],
    );
}

#[test]
fn alias_reassignment_noop_is_non_null() {
    expect_non_null(
        "
        pub unsafe fn f(mut p: *const i32) -> i32 {
            let q = p;
            p = q;
            *p
        }
        ",
        &[("f", "p")],
    );
}

#[test]
fn alias_reassigned_from_non_alias_loses_original_proof() {
    expect_non_null(
        "
        pub unsafe fn f(mut p: *const i32, r: *const i32) -> i32 {
            p = r;
            *p
        }
        ",
        &[("f", "r")],
    );
}

#[test]
fn storing_alias_through_pointer_is_nullable_for_stored_alias() {
    expect_non_null(
        "
        pub unsafe fn f(p: *const i32, out: *mut *const i32) -> i32 {
            *out = p;
            *p
        }
        ",
        &[("f", "out")],
    );
}

#[test]
fn pointer_arithmetic_assignment_is_nullable() {
    expect_non_null(
        "
        pub unsafe fn f(mut p: *const i32) -> i32 {
            p = p.offset(1);
            *p
        }
        ",
        &[],
    );
}

#[test]
fn address_take_of_pointer_variable_is_nullable() {
    expect_non_null(
        "
        pub unsafe fn f(p: *const i32) -> i32 {
            let _addr = &p;
            *p
        }
        ",
        &[],
    );
}

#[test]
fn local_callee_non_null_param_proves_caller_param() {
    expect_non_null(
        "
        pub unsafe fn callee(x: *const i32) -> i32 {
            *x
        }

        pub unsafe fn caller(p: *const i32) -> i32 {
            callee(p)
        }
        ",
        &[("callee", "x"), ("caller", "p")],
    );
}

#[test]
fn local_callee_nullable_param_keeps_caller_nullable() {
    expect_non_null(
        "
        pub unsafe fn callee(x: *const i32) -> i32 {
            if x.is_null() {
                return 0;
            }
            *x
        }

        pub unsafe fn caller(p: *const i32) -> i32 {
            callee(p)
        }
        ",
        &[],
    );
}

#[test]
fn same_alias_passed_to_nullable_formal_keeps_caller_nullable() {
    expect_non_null(
        "
        pub unsafe fn callee(a: *const i32, b: *const i32) -> i32 {
            let v = *a;
            if b.is_null() {
                return v;
            }
            v + *b
        }

        pub unsafe fn caller(p: *const i32) -> i32 {
            callee(p, p)
        }
        ",
        &[("callee", "a")],
    );
}

#[test]
fn recursive_deref_before_call_is_non_null() {
    expect_non_null(
        "
        pub unsafe fn f(p: *const i32) -> i32 {
            let v = *p;
            f(p);
            v
        }
        ",
        &[("f", "p")],
    );
}

#[test]
fn recursive_call_before_deref_is_nullable() {
    expect_non_null(
        "
        pub unsafe fn f(p: *const i32) -> i32 {
            f(p);
            *p
        }
        ",
        &[],
    );
}

#[test]
fn mutual_recursion_with_deref_before_calls_is_non_null() {
    expect_non_null(
        "
        pub unsafe fn a(p: *const i32) -> i32 {
            let v = *p;
            b(p);
            v
        }

        pub unsafe fn b(p: *const i32) -> i32 {
            let v = *p;
            a(p);
            v
        }
        ",
        &[("a", "p"), ("b", "p")],
    );
}

#[test]
fn loop_before_deref_is_nullable() {
    expect_non_null(
        "
        pub unsafe fn f(p: *const i32, mut n: i32) -> i32 {
            while n > 0 {
                n -= 1;
            }
            *p
        }
        ",
        &[],
    );
}

#[test]
fn loop_body_deref_before_revisit_is_non_null() {
    expect_non_null(
        "
        pub unsafe fn f(p: *const i32) -> i32 {
            loop {
                let v = *p;
                if v == 0 {
                    return v;
                }
            }
        }
        ",
        &[("f", "p")],
    );
}

#[test]
fn function_pointer_call_with_alias_is_nullable() {
    expect_non_null(
        "
        pub unsafe fn f(p: *const i32, fp: unsafe fn(*const i32) -> i32) -> i32 {
            fp(p)
        }
        ",
        &[],
    );
}

#[test]
fn modeled_libc_strlen_proves_non_null() {
    expect_non_null(
        "
        extern \"C\" {
            fn strlen(s: *const i8) -> usize;
        }

        pub unsafe fn f(p: *const i8) {
            let _ = strlen(p);
        }
        ",
        &[("f", "p")],
    );
}

#[test]
fn free_accepts_null_and_is_nullable() {
    expect_non_null(
        "
        extern \"C\" {
            fn free(p: *mut core::ffi::c_void);
        }

        pub unsafe fn f(p: *mut core::ffi::c_void) {
            free(p);
        }
        ",
        &[],
    );
}

#[test]
fn unmodeled_libc_call_is_nullable() {
    expect_non_null(
        "
        extern \"C\" {
            fn maybe_accepts_null(p: *const i8);
        }

        pub unsafe fn f(p: *const i8) {
            maybe_accepts_null(p);
        }
        ",
        &[],
    );
}

#[test]
fn local_address_assignment_is_non_null() {
    expect_non_null_local_facts(
        "
        pub unsafe fn f() {
            let mut x = 0;
            let p: *mut i32 = &mut x;
            let _ = p;
        }
        ",
        &[("f", "p")],
        &[],
    );
}

#[test]
fn local_malloc_assignment_is_non_null() {
    expect_non_null_local_facts(
        "
        extern \"C\" {
            fn malloc(size: usize) -> *mut i32;
        }

        pub unsafe fn f() {
            let p: *mut i32 = malloc(std::mem::size_of::<i32>());
            let _ = p;
        }
        ",
        &[("f", "p")],
        &[],
    );
}

#[test]
fn local_null_then_address_stays_nullable_for_now() {
    expect_non_null_local_facts(
        "
        pub unsafe fn f() {
            let mut x = 0;
            let mut p: *mut i32 = std::ptr::null_mut();
            p = &mut x;
            let _ = p;
        }
        ",
        &[],
        &[("f", "p")],
    );
}

#[test]
fn nullable_param_copy_makes_local_nullable() {
    expect_non_null_local_facts(
        "
        pub unsafe fn f(p: *mut i32) {
            let q = p;
            let _ = q;
        }
        ",
        &[],
        &[("f", "q")],
    );
}

#[test]
fn non_null_param_copy_keeps_local_non_null() {
    expect_non_null_local_facts(
        "
        pub unsafe fn f(p: *mut i32) -> i32 {
            let v = *p;
            let q = p;
            let _ = q;
            v
        }
        ",
        &[("f", "q")],
        &[],
    );
}

#[test]
fn integer_to_pointer_cast_is_nullable() {
    expect_non_null_local_facts(
        "
        pub unsafe fn f(n: usize) {
            let p = n as *mut i32;
            let _ = p;
        }
        ",
        &[],
        &[("f", "p")],
    );
}

#[test]
fn pointer_to_pointer_cast_preserves_nullity() {
    expect_non_null_local_facts(
        "
        pub unsafe fn nullable(p: *mut i32) {
            let q = p as *const i32;
            let _ = q;
        }

        pub unsafe fn non_null() {
            let mut x = 0;
            let p = &mut x as *mut i32;
            let q = p as *const i32;
            let _ = q;
        }
        ",
        &[("non_null", "q")],
        &[("nullable", "q")],
    );
}

#[test]
fn load_through_pointer_is_nullable() {
    expect_non_null_local_facts(
        "
        pub unsafe fn f(out: *mut *mut i32) {
            let p = *out;
            let _ = p;
        }
        ",
        &[],
        &[("f", "p")],
    );
}

#[test]
fn field_projection_pointer_is_nullable() {
    expect_non_null_local_facts(
        "
        #[repr(C)]
        pub struct Holder {
            ptr: *mut i32,
        }

        pub unsafe fn f(holder: Holder) {
            let p = holder.ptr;
            let _ = p;
        }
        ",
        &[],
        &[("f", "p")],
    );
}

#[test]
fn indirect_null_write_marks_target_nullable() {
    expect_non_null_local_facts(
        "
        pub unsafe fn f() {
            let mut x = 0;
            let mut p = &mut x as *mut i32;
            let out = &mut p as *mut *mut i32;
            *out = std::ptr::null_mut();
            let _ = p;
        }
        ",
        &[],
        &[("f", "p")],
    );
}

#[test]
fn indirect_non_null_write_does_not_mark_target_nullable() {
    expect_non_null_local_facts(
        "
        pub unsafe fn f() {
            let mut x = 0;
            let mut y = 0;
            let mut p = &mut x as *mut i32;
            let out = &mut p as *mut *mut i32;
            *out = &mut y;
            let _ = p;
        }
        ",
        &[("f", "p")],
        &[],
    );
}

#[test]
fn callee_indirect_null_write_side_effect_marks_caller_local_nullable() {
    expect_non_null_local_facts(
        "
        pub unsafe fn set_null(out: *mut *mut i32) {
            *out = std::ptr::null_mut();
        }

        pub unsafe fn caller() {
            let mut x = 0;
            let mut p = &mut x as *mut i32;
            set_null(&mut p);
            let _ = p;
        }
        ",
        &[],
        &[("caller", "p")],
    );
}

#[test]
fn function_pointer_null_write_side_effect_marks_caller_local_nullable() {
    expect_non_null_local_facts(
        "
        pub unsafe fn set_null(out: *mut *mut i32) {
            *out = std::ptr::null_mut();
        }

        pub unsafe fn caller() {
            let mut x = 0;
            let mut p = &mut x as *mut i32;
            let fp: unsafe fn(*mut *mut i32) = set_null;
            fp(&mut p);
            let _ = p;
        }
        ",
        &[],
        &[("caller", "p")],
    );
}

#[test]
fn direct_non_null_return_summary_keeps_call_result_non_null() {
    expect_non_null_local_facts(
        "
        pub unsafe fn callee() -> *mut i32 {
            let mut x = 0;
            &mut x as *mut i32
        }

        pub unsafe fn caller() {
            let q = callee();
            let _ = q;
        }
        ",
        &[("caller", "q")],
        &[],
    );
}

#[test]
fn direct_nullable_return_summary_marks_call_result_nullable() {
    expect_non_null_local_facts(
        "
        pub unsafe fn callee(flag: bool) -> *mut i32 {
            if flag {
                return std::ptr::null_mut();
            }
            let mut x = 0;
            &mut x as *mut i32
        }

        pub unsafe fn caller(flag: bool) {
            let q = callee(flag);
            let _ = q;
        }
        ",
        &[],
        &[("caller", "q")],
    );
}
