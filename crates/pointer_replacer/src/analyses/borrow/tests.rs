use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::mir::VarDebugInfoContents;

use super::*;

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

fn all_mutable_ctxt(program: &RustProgram) -> GBorrowInferCtxt {
    GBorrowInferCtxt::new(program, |_| |_| true, |_| |_| true)
}

fn user_var_names(tcx: TyCtxt, def_id: LocalDefId, locals: &DenseBitSet<Local>) -> Vec<String> {
    let body = &*tcx.mir_drops_elaborated_and_const_checked(def_id).borrow();
    let mut names = vec![];
    for var_debug_info in body.var_debug_info.iter() {
        if let VarDebugInfoContents::Place(place) = &var_debug_info.value {
            if let Some(local) = place.as_local()
                && locals.contains(local)
            {
                names.push(var_debug_info.name.as_str().to_string());
            }
        }
    }
    names.sort();
    names
}

fn fn_name(tcx: TyCtxt, def_id: LocalDefId) -> String {
    tcx.item_name(def_id.to_def_id()).to_string()
}

fn run_demote(code: &str) -> Vec<String> {
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let program = build_rust_program(tcx);
        let mut ctxt = all_mutable_ctxt(&program);
        let demoted = demote_pointers_iterative(&program, &mut ctxt);
        let mut all_demoted: Vec<String> = Vec::new();
        for (&did, locals) in &demoted {
            all_demoted.extend(user_var_names(tcx, did, locals));
        }
        all_demoted.sort();
        all_demoted
    })
    .unwrap()
}

fn get_return_provenance_params(code: &str) -> FxHashMap<String, Vec<String>> {
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let program = build_rust_program(tcx);
        let ctxt = all_mutable_ctxt(&program);
        let mut result: FxHashMap<String, Vec<String>> = FxHashMap::default();

        for &f in &program.functions {
            let body = &*tcx.mir_drops_elaborated_and_const_checked(f).borrow();
            let provenance_set = &ctxt.provenances[&f];
            let Some(return_provenance) = provenance_set.local_data[RETURN_PLACE] else {
                continue;
            };
            let BorrowInferenceResults { subset_closure, .. } = borrow_inference(tcx, f, &ctxt);
            let mut bounds = vec![];
            for arg in body.args_iter() {
                if let Some(arg_provenance) = provenance_set.local_data[arg]
                    && subset_closure.contains(arg_provenance, return_provenance)
                {
                    for var_debug_info in body.var_debug_info.iter() {
                        if var_debug_info
                            .argument_index
                            .is_some_and(|arg_index| arg_index == arg.as_u32() as u16)
                        {
                            bounds.push(var_debug_info.name.as_str().to_string());
                        }
                    }
                }
            }
            if !bounds.is_empty() {
                bounds.sort();
                result.insert(fn_name(tcx, f), bounds);
            }
        }
        result
    })
    .unwrap()
}

#[test]
fn test_proof_of_concept() {
    let demoted = run_demote(
        "
        unsafe fn f(mut p: *mut i32) -> i32 {
            let mut r1 = p;
            let mut r2 = r1;
            let mut q = r1;
            *q = 1;
            *r1 = 2;
            *r2 = 3;
            *p = 4;
            *p
        }",
    );
    assert_eq!(demoted, vec!["r2"], "only r2 should be demoted");
}

#[test]
fn test_inferred_bounds() {
    let params = get_return_provenance_params(
        "
        unsafe fn f(mut p: *mut i32, mut q: *mut i32) -> *mut i32 {
            *p = 3;
            return &raw mut *q;
        }

        unsafe fn g() {
            let mut local1 = 0;
            let mut local2 = 1;
            let mut r = f(&raw mut local1, &raw mut local2);
            *r = 2;
            println!(\"{}\", *r);
        }
        ",
    );
    assert_eq!(
        params["f"],
        vec!["q"],
        "only q's provenance flows to f's return value"
    );
    assert!(!params.contains_key("g"), "g has no pointer return type");
}

#[test]
fn test_demote_strategy_no_ub() {
    let demoted = run_demote(
        "
        unsafe fn f() {
            let mut local = 0i32;
            let x = &mut local as *mut _;
            let y = &mut local as *mut _;
            *x = 1;
            *y = 2;
        }
        ",
    );
    assert_eq!(demoted, vec!["x", "y"], "both x and y should be demoted");
}

#[test]
fn test_demote_strategy_optimality() {
    let demoted = run_demote(
        "
        unsafe fn f() {
            let mut local = 0i32;
            let x = &raw mut local;
            let y = &raw mut local;
            *y = 2;
            *x = 1;
        }
        ",
    );
    assert_eq!(
        demoted,
        vec!["x"],
        "only x should be demoted (its write invalidates y's loan)"
    );
}

#[test]
#[should_panic]
fn struct_field_collapsed() {
    // p borrows s.a, q borrows s.b — disjoint fields, no real conflict.

    let demoted = run_demote(
        "
        struct Pair { a: i32, b: i32 }
        unsafe fn f() {
            let mut s = Pair { a: 0, b: 0 };
            let p = &raw mut s.a;
            let q = &raw mut s.b;
            *p = 1;
            *q = 2;
        }
        ",
    );
    assert_eq!(
        demoted,
        Vec::<String>::new(),
        "s.a and s.b are disjoint — nothing should be demoted; got: {demoted:?}"
    );
}

#[test]
#[should_panic]
fn return_value_lifetime() {
    // make_ref returns its input — p aliases a through the call.

    let demoted = run_demote(
        "
        unsafe fn make_ref(x: *mut i32) -> *mut i32 { x }
        unsafe fn f() {
            let mut a = 0i32;
            let p = make_ref(&raw mut a);
            a = 1;
            *p = 2;
        }
        ",
    );
    assert_eq!(
        demoted,
        vec!["p"],
        "p aliases a through make_ref — p should be demoted due to conflict with a = 1"
    );
}

#[test]
#[should_panic]
fn null_ptr_no_provenance() {
    // p is initialized from a null constant — no provenance is created for it.
    // When *pp = &raw mut x later stores a real borrow into p, there's no
    // provenance to attach the loan to. The conflict is missed.
    let demoted = run_demote(
        "
        unsafe fn f() {
            let mut x = 0i32;
            let mut p: *mut i32 = core::ptr::null_mut();
            let pp: *mut *mut i32 = &raw mut p;
            *pp = &raw mut x;
            *p = 1;
            x = 2;
        }
        ",
    );
    assert_eq!(
        demoted,
        vec!["p"],
        "p borrows x via indirect store — p should be demoted due to conflict with x = 2"
    );
}
