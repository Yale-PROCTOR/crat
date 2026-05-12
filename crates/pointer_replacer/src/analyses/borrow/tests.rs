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

fn get_lifetime_flow_edges(code: &str) -> FxHashMap<String, Vec<(String, String)>> {
    get_lifetime_flow_facts(code)
        .into_iter()
        .map(|(name, facts)| (name, facts.value_flows))
        .collect()
}

#[derive(Debug)]
struct LifetimeFlowFacts {
    value_flows: Vec<(String, String)>,
    storage_aliases: Vec<(String, String)>,
    unknown_targets: Vec<String>,
}

fn get_lifetime_flow_facts(code: &str) -> FxHashMap<String, LifetimeFlowFacts> {
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let program = build_rust_program(tcx);
        let results = lifetime_flow::analyze_program_lifetime_flow(&program);
        let mut all_facts = FxHashMap::default();

        for &f in &program.functions {
            let result = &results[&f];
            let mut unknown_targets: Vec<_> = result
                .summary
                .unknown_targets
                .iter()
                .map(|target| format_signature_slot(result.summary.slots[target]))
                .collect();
            unknown_targets.sort();
            all_facts.insert(
                fn_name(tcx, f),
                LifetimeFlowFacts {
                    value_flows: collect_lifetime_flow_edges(&result.summary, false),
                    storage_aliases: collect_lifetime_flow_edges(&result.summary, true),
                    unknown_targets,
                },
            );
        }

        all_facts
    })
    .unwrap()
}

fn collect_lifetime_flow_edges(
    summary: &lifetime_flow::LifetimeFlowSummary,
    storage_aliases: bool,
) -> Vec<(String, String)> {
    let matrix = if storage_aliases {
        &summary.storage_aliases
    } else {
        &summary.value_flows
    };
    let mut edges = vec![];
    for source in matrix.rows() {
        let Some(targets) = matrix.row(source) else {
            continue;
        };
        let source = format_signature_slot(summary.slots[source]);
        for target in targets.iter() {
            edges.push((source.clone(), format_signature_slot(summary.slots[target])));
        }
    }
    edges.sort();
    edges
}

fn format_signature_slot(slot: lifetime_flow::SignatureSlot) -> String {
    let root = match slot.root {
        lifetime_flow::SignatureRoot::Return => "return".to_string(),
        lifetime_flow::SignatureRoot::Arg(local) => format!("arg{}", local.index()),
    };
    format!("{root}@{}", slot.depth)
}

fn assert_lifetime_flow_edge(
    facts: &FxHashMap<String, LifetimeFlowFacts>,
    function: &str,
    source: &str,
    target: &str,
) {
    assert!(
        facts[function]
            .value_flows
            .contains(&(source.to_string(), target.to_string())),
        "{function} should contain value flow {source} -> {target}; got {:?}",
        facts[function].value_flows
    );
}

fn assert_lifetime_storage_alias(
    facts: &FxHashMap<String, LifetimeFlowFacts>,
    function: &str,
    left: &str,
    right: &str,
) {
    assert!(
        facts[function]
            .storage_aliases
            .contains(&(left.to_string(), right.to_string())),
        "{function} should contain storage alias {left} -> {right}; got {:?}",
        facts[function].storage_aliases
    );
}

fn assert_lifetime_unknown_target(
    facts: &FxHashMap<String, LifetimeFlowFacts>,
    function: &str,
    target: &str,
) {
    assert!(
        facts[function]
            .unknown_targets
            .contains(&target.to_string()),
        "{function} should mark {target} unknown; got {:?}",
        facts[function].unknown_targets
    );
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
fn lifetime_flow_identity_return() {
    let edges = get_lifetime_flow_edges(
        "
        unsafe fn make_ref(x: *mut i32) -> *mut i32 { x }
        ",
    );
    assert!(
        edges["make_ref"].contains(&("arg1@0".to_string(), "return@0".to_string())),
        "identity return should flow arg1@0 to return@0; got {:?}",
        edges["make_ref"]
    );
}

#[test]
fn lifetime_flow_stored_output() {
    let edges = get_lifetime_flow_edges(
        "
        unsafe fn write_out(out: *mut *const i32, value: *const i32) {
            *out = value;
        }
        ",
    );
    assert!(
        edges["write_out"].contains(&("arg2@0".to_string(), "arg1@1".to_string())),
        "stored output should flow value arg2@0 to out arg1@1; got {:?}",
        edges["write_out"]
    );
    assert!(
        !edges["write_out"].contains(&("arg2@0".to_string(), "arg1@0".to_string())),
        "stored output must not flow value into out arg1@0"
    );
}

#[test]
fn lifetime_flow_conditional_return() {
    let edges = get_lifetime_flow_edges(
        "
        unsafe fn pick(x: *mut i32, y: *mut i32, pick_x: bool) -> *mut i32 {
            if pick_x { x } else { y }
        }
        ",
    );
    assert!(
        edges["pick"].contains(&("arg1@0".to_string(), "return@0".to_string())),
        "x should flow to return; got {:?}",
        edges["pick"]
    );
    assert!(
        edges["pick"].contains(&("arg2@0".to_string(), "return@0".to_string())),
        "y should flow to return; got {:?}",
        edges["pick"]
    );
}

#[test]
fn lifetime_flow_read_output() {
    let edges = get_lifetime_flow_edges(
        "
        unsafe fn read_out(out: *const *const i32) -> *const i32 {
            *out
        }
        ",
    );
    assert!(
        edges["read_out"].contains(&("arg1@1".to_string(), "return@0".to_string())),
        "read output should flow out arg1@1 to return@0; got {:?}",
        edges["read_out"]
    );
}

#[test]
fn lifetime_flow_forwarded_output_reference_aliases_storage() {
    let facts = get_lifetime_flow_facts(
        "
        unsafe fn forward(out: *mut *mut i32) -> *mut *mut i32 {
            out
        }
        ",
    );
    assert_lifetime_flow_edge(&facts, "forward", "arg1@0", "return@0");
    assert_lifetime_storage_alias(&facts, "forward", "arg1@1", "return@1");
    assert_lifetime_storage_alias(&facts, "forward", "return@1", "arg1@1");
}

#[test]
fn lifetime_flow_copy_between_output_slots() {
    let facts = get_lifetime_flow_facts(
        "
        unsafe fn copy_out(src: *mut *mut i32, dst: *mut *mut i32) {
            *dst = *src;
        }
        ",
    );
    assert_lifetime_flow_edge(&facts, "copy_out", "arg1@1", "arg2@1");
    assert!(
        !facts["copy_out"]
            .value_flows
            .contains(&("arg1@0".to_string(), "arg2@1".to_string())),
        "copy_out should copy the value behind src, not src itself; got {:?}",
        facts["copy_out"].value_flows
    );
}

#[test]
fn lifetime_flow_instantiates_callee_return_summary() {
    let facts = get_lifetime_flow_facts(
        "
        unsafe fn id(x: *mut i32) -> *mut i32 { x }

        unsafe fn wrap(y: *mut i32) -> *mut i32 {
            id(y)
        }
        ",
    );
    assert_lifetime_flow_edge(&facts, "id", "arg1@0", "return@0");
    assert_lifetime_flow_edge(&facts, "wrap", "arg1@0", "return@0");
}

#[test]
fn lifetime_flow_instantiates_callee_output_store_summary() {
    let facts = get_lifetime_flow_facts(
        "
        unsafe fn write_out(out: *mut *mut i32, value: *mut i32) {
            *out = value;
        }

        unsafe fn wrap(out: *mut *mut i32, value: *mut i32) {
            write_out(out, value);
        }
        ",
    );
    assert_lifetime_flow_edge(&facts, "write_out", "arg2@0", "arg1@1");
    assert_lifetime_flow_edge(&facts, "wrap", "arg2@0", "arg1@1");
}

#[test]
fn lifetime_flow_external_call_marks_unknown_return_and_nested_arg() {
    let facts = get_lifetime_flow_facts(
        "
        unsafe extern \"C\" {
            fn external(out: *mut *mut i32) -> *mut i32;
        }

        unsafe fn call_external(out: *mut *mut i32) -> *mut i32 {
            external(out)
        }
        ",
    );
    assert_lifetime_unknown_target(&facts, "call_external", "return@0");
    assert_lifetime_unknown_target(&facts, "call_external", "arg1@1");
    assert!(
        !facts["call_external"]
            .unknown_targets
            .contains(&"arg1@0".to_string()),
        "plain arg@0 reassignment is not caller-visible unknown output; got {:?}",
        facts["call_external"].unknown_targets
    );
}

#[test]
fn lifetime_flow_mutually_recursive_scc_converges() {
    let facts = get_lifetime_flow_facts(
        "
        unsafe fn a(x: *mut i32, pick_x: bool) -> *mut i32 {
            if pick_x { x } else { b(x, pick_x) }
        }

        unsafe fn b(y: *mut i32, pick_y: bool) -> *mut i32 {
            a(y, pick_y)
        }
        ",
    );
    assert_lifetime_flow_edge(&facts, "a", "arg1@0", "return@0");
    assert_lifetime_flow_edge(&facts, "b", "arg1@0", "return@0");
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
fn tb_union_find_over_demotion() {
    // Miri TB: OK. q as &mut s.1 survives s.0 = 1 (sibling field write).
    // p gets demoted (s.0 = 1 invalidates its loan, then *p = 3 uses it).
    // Our analysis: union(p, s) when demoting p. Since q's loan has
    // borrowed.local == s, and s is now in p's group, q gets spuriously
    // affected in subsequent iterations.
    //
    // The correct post-transformation (verified with Miri -Zmiri-tree-borrows):
    //   unsafe {
    //       let mut s = (0i32, 1i32);
    //       let p = &raw mut s.0;       // stays raw
    //       let q: &mut i32 = &mut s.1; // promoted
    //       s.0 = 1;
    //       *p = 3;
    //       *q = 4;
    //       assert_eq!(s, (3, 4));
    //   }
    // is NOT UB — writing to s.0 is not a foreign write to q's tag
    // because they cover disjoint memory offsets.
    let demoted = run_demote(
        "
        unsafe fn f() {
            let mut s = (0i32, 1i32);
            let p = &raw mut s.0;
            let q = &raw mut s.1;
            s.0 = 1;
            *p = 3;
            *q = 4;
        }
        ",
    );
    assert_eq!(
        demoted,
        vec!["p"],
        "only p should be demoted — q borrows s.1 which is unaffected; got: {demoted:?}"
    );
}

#[test]
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
fn stored_output_lifetime() {
    let demoted = run_demote(
        "
        unsafe fn write_out(out: *mut *mut i32, value: *mut i32) {
            *out = value;
        }

        unsafe fn f() {
            let mut x = 0i32;
            let mut r: *mut i32 = core::ptr::null_mut();
            write_out(&raw mut r, &raw mut x);
            x = 1;
            *r = 2;
        }
        ",
    );
    assert_eq!(
        demoted,
        vec!["r"],
        "r receives x's borrow through write_out and should be demoted"
    );
}

#[test]
fn wrapped_return_value_lifetime() {
    let demoted = run_demote(
        "
        unsafe fn id(x: *mut i32) -> *mut i32 { x }
        unsafe fn wrap(y: *mut i32) -> *mut i32 { id(y) }

        unsafe fn f() {
            let mut x = 0i32;
            let p = wrap(&raw mut x);
            x = 1;
            *p = 2;
        }
        ",
    );
    assert_eq!(
        demoted,
        vec!["p"],
        "p receives x's borrow through two user-defined calls and should be demoted"
    );
}

#[test]
fn wrapped_stored_output_lifetime() {
    let demoted = run_demote(
        "
        unsafe fn write_out(out: *mut *mut i32, value: *mut i32) {
            *out = value;
        }

        unsafe fn wrap(out: *mut *mut i32, value: *mut i32) {
            write_out(out, value);
        }

        unsafe fn f() {
            let mut x = 0i32;
            let mut r: *mut i32 = core::ptr::null_mut();
            wrap(&raw mut r, &raw mut x);
            x = 1;
            *r = 2;
        }
        ",
    );
    assert_eq!(
        demoted,
        vec!["r"],
        "r receives x's borrow through a wrapped output store and should be demoted"
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
