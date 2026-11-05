use super::*;

fn indirections(ty: &Ty) -> String {
    match &ty.kind {
        TyKind::Ref(_, inner) => format!("&{}", indirections(&inner.ty)),
        TyKind::Ptr(inner) => format!("*{}", indirections(&inner.ty)),
        _ => String::new(),
    }
}

fn signature_indirections(signature: &str) -> String {
    run_compiler_on_str("pub fn context() {}", |_| {
        let parsed = utils::ast::parse_crate(format!("{signature} {{ todo!() }}"));
        let ItemKind::Fn(function) = &parsed.items[0].kind else { unreachable!() };
        indirections(&function.sig.decl.inputs[0].ty)
    })
    .unwrap()
}

fn assert_stub_signatures_compile(records: &[ItemRecord], context: &str) {
    let mut source = context.to_owned();
    for record in records {
        if let ItemRecord::Function(function) = record {
            source.push_str(&function.target_signature);
            source.push_str(" { todo!() }\n");
        }
    }
    run_compiler_on_str(&source, utils::type_check).expect(&source);
}

#[test]
fn nested_model_references_reach_signatures_locals_rules_and_metadata() {
    let source = r#"
pub unsafe fn read(p: *const *const i32) -> i32 {
    let q: *const *const i32 = p;
    **q
}
pub unsafe fn third(p: *const *const *const i32) -> i32 { ***p }
"#;
    run_compiler_on_str(source, |tcx| {
        let decisions = tools_pointer_decisions(tcx);
        let read = local_def("read", tcx);
        assert_eq!(
            decisions.signatures.data[&read].input_decs[0],
            Some(PtrKind::Ref(false))
        );
        assert_eq!(
            decisions.nested(PointerTarget::Input(read, 0))[0].kind,
            PtrKind::Ref(false)
        );
        let mut surface = utils::ast::parse_crate(source.to_owned());
        let mut mapper = utils::ir::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
        let catalog =
            rule_binding_catalog(&surface.items[0], read, &decisions, &mapper.ast_to_hir, tcx);
        let binding = local_binding_hir_id(read, "p", tcx);
        let TypeTree::Reference { pointee, .. } = &catalog[&binding] else {
            panic!("missing outer reference")
        };
        assert!(matches!(pointee.as_ref(), TypeTree::Reference { .. }));
    })
    .unwrap();
    let records = generate(source);
    let read = function(&records, "read");
    assert!(
        read.baseline.skeleton.contains("let mut q: &&i32"),
        "{}",
        read.baseline.skeleton
    );
    let row = read
        .baseline
        .statement_pair_metadata
        .iter()
        .flat_map(|pair| &pair.pointer_variables)
        .find(|row| row.name == "q")
        .unwrap();
    assert_eq!(
        signature_indirections(&format!("fn q(value: {})", row.selected_target_type)),
        "&&"
    );
    let third = function(&records, "third");
    assert_eq!(signature_indirections(&third.target_signature), "&&&");
    assert_stub_signatures_compile(&records, "");
}

#[test]
fn raw_outer_decision_does_not_hide_promoted_inner_layer() {
    let source = "pub unsafe fn read(p: *const *const i32) -> i32 { **p }";
    run_compiler_on_str(source, |tcx| {
        let mut decisions = tools_pointer_decisions(tcx);
        let read = local_def("read", tcx);
        decisions.signatures.data.get_mut(&read).unwrap().input_decs[0] = Some(PtrKind::Raw(false));
        let mut surface = utils::ast::parse_crate(source.to_owned());
        let mut mapper = utils::ir::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
        let speller = TypeSpeller::new(read, &mapper.ast_to_hir, tcx);
        apply_target_signature(
            &mut surface.items[0],
            read,
            &decisions,
            &speller,
            "read",
            tcx,
        )
        .unwrap();
        let ItemKind::Fn(function) = &surface.items[0].kind else { unreachable!() };
        assert_eq!(indirections(&function.sig.decl.inputs[0].ty), "*&");
        assert!(nested_changes_type(
            decisions.nested(PointerTarget::Input(read, 0)),
            tcx.fn_sig(read)
                .instantiate_identity()
                .skip_binder()
                .inputs()[0]
        ));
    })
    .unwrap();
}

#[test]
fn existing_reference_outer_layers_and_pointer_aliases_keep_nested_promotions() {
    let source = r#"
type Pointer = *const *const i32;
pub unsafe fn alias(p: Pointer) -> i32 { **p }
pub unsafe fn reference(p: &*const i32) -> i32 { **p }
pub unsafe fn deep(p: *const *const *const *const i32) -> i32 { ****p }
"#;
    let records = generate(source);
    for (name, expected) in [("alias", "&&"), ("reference", "&&"), ("deep", "&&&*")] {
        let signature = &function(&records, name).target_signature;
        assert_eq!(signature_indirections(signature), expected, "{signature}");
    }
    assert_stub_signatures_compile(&records, "type Pointer = *const *const i32;");
}

#[test]
fn nested_return_lifetimes_support_direct_transformed_bodies() {
    let source = "pub unsafe fn id<'a>(p: *const *const i32) -> *const *const i32 { p }";
    let records = generate(source);
    let signature = &function(&records, "id").target_signature;
    assert!(signature.contains("'b"), "{signature}");
    assert!(signature.contains("'c"), "{signature}");
    let transformed = format!("{signature} {{ p }}");
    run_compiler_on_str(&transformed, utils::type_check).expect(&transformed);
}

#[test]
fn unmodeled_reference_suffix_retains_its_original_lifetime_relationship() {
    let source =
        "pub unsafe fn id(p: *const *const *const &i32) -> *const *const *const &i32 { p }";
    let records = generate(source);
    let signature = &function(&records, "id").target_signature;
    let transformed = format!("{signature} {{ p }}");
    run_compiler_on_str(&transformed, utils::type_check).expect(&transformed);
}

#[test]
fn existing_static_and_named_return_lifetimes_remain_usable() {
    for source in [
        "static GLOBAL: i32 = 1; pub unsafe fn get() -> &'static i32 { &GLOBAL }",
        "pub unsafe fn get<'a>(p: *const i32) -> &'a i32 { &*p }",
        "pub unsafe fn get(p: &'static *const i32) -> i32 { **p }",
        "type P = &'static *const i32; pub unsafe fn get(p: P) -> i32 { **p }",
    ] {
        let records = generate(source);
        let signature = &function(&records, "get").target_signature;
        if source.contains("'static") {
            assert!(signature.contains("'static"), "{signature}");
        }
        let body = if source.contains("GLOBAL") {
            "&GLOBAL"
        } else if source.contains("-> &'a") {
            "p"
        } else {
            "**p"
        };
        let transformed = format!("static GLOBAL: i32 = 1; {signature} {{ {body} }}");
        run_compiler_on_str(&transformed, utils::type_check).expect(&transformed);
    }
}

#[test]
fn preserved_fields_and_globals_keep_original_types() {
    let source = r#"
pub struct Holder { pub pointer: *const *const i32 }
static mut GLOBAL: *const *const i32 = core::ptr::null();
pub unsafe fn read(holder: *const Holder) -> i32 { **(*holder).pointer }
"#;
    let records = generate(source);
    assert!(
        type_record(&records, "Holder")
            .definition
            .contains("pointer: *const *const i32")
    );
    assert!(
        value(&records, "GLOBAL")
            .declaration
            .contains("*const *const i32")
    );
    assert_stub_signatures_compile(
        &records,
        "pub struct Holder { pub pointer: *const *const i32 }\n",
    );
}

#[test]
fn nullable_actuals_and_returns_choose_optional_reference_types() {
    let source = r#"
pub unsafe fn consume(p: *const i32) { let _ = p; }
pub unsafe fn caller() { consume(core::ptr::null()); }
pub unsafe fn none() -> *const i32 { core::ptr::null() }
pub unsafe fn none_with_statements() -> *const i32 { let _x = 1; core::ptr::null() }
pub unsafe fn none_with_branches(flag: bool) -> *const i32 { if flag { core::ptr::null() } else { core::ptr::null() } }
pub unsafe fn none_local() -> *const i32 { let p = core::ptr::null(); p }
"#;
    let records = generate(source);
    assert!(
        function(&records, "consume")
            .target_signature
            .contains("Option<&i32>")
    );
    for name in [
        "none",
        "none_with_statements",
        "none_with_branches",
        "none_local",
    ] {
        let signature = &function(&records, name).target_signature;
        assert!(signature.contains("Option<&"), "{signature}");
        let transformed = format!("{signature} {{ None }}");
        run_compiler_on_str(&transformed, utils::type_check).expect(&transformed);
    }
    assert_stub_signatures_compile(&records, "");
}

#[test]
fn null_comparisons_and_nullable_arrays_select_optional_forms() {
    let records = generate(
        "pub unsafe fn maybe(p: *const i32) -> i32 { if p == 0 as *const i32 { 0 } else { *p } } pub unsafe fn array(p: *const i32) -> i32 { if p.is_null() { 0 } else { *p.offset(1) } }",
    );
    assert!(
        function(&records, "maybe")
            .target_signature
            .contains("Option<&i32>")
    );
    assert!(
        function(&records, "array")
            .target_signature
            .contains("Option<&[i32]>")
    );
    assert_stub_signatures_compile(&records, "");
}

#[test]
fn owning_allocation_size_controls_slice_shape_without_indexing() {
    for (size, expected) in [
        ("core::mem::size_of::<i32>()", "Box<i32>"),
        ("4 * core::mem::size_of::<i32>()", "Box<[i32]>"),
        ("count * core::mem::size_of::<i32>()", "Box<[i32]>"),
    ] {
        let source = format!(
            "unsafe extern \"C\" {{ fn malloc(size: usize) -> *mut core::ffi::c_void; }} pub unsafe fn allocate(count: usize) -> *mut i32 {{ let p = malloc({size}) as *mut i32; *p = 7; p }}"
        );
        let records = generate(&source);
        let signature = &function(&records, "allocate").target_signature;
        assert!(signature.ends_with(expected), "{signature}");
        assert_stub_signatures_compile(&records, "");
    }
}

#[test]
fn owning_void_allocations_and_nullable_returns_stay_raw() {
    use pointer_replacer_bo::analyses::borrow_ownership::{SlotKind, solver::SlotRef};

    let source = r#"
unsafe extern "C" { fn malloc(size: usize) -> *mut core::ffi::c_void; }
pub unsafe fn allocate(size: usize) -> *mut core::ffi::c_void { let p = malloc(size); p }
pub unsafe fn nullable(size: usize) -> *mut core::ffi::c_void {
    let p = malloc(size);
    if p.is_null() { core::ptr::null_mut() } else { p }
}
"#;
    run_compiler_on_str(source, |tcx| {
        let analysis = pointer_replacer_bo::analyze_pointers(tcx).unwrap();
        let allocate = local_def("allocate", tcx);
        let slot = analysis.slots.fn_local_slots[&allocate]
            .slot_for_local_depth(rustc_middle::mir::RETURN_PLACE, 0)
            .unwrap();
        assert_eq!(
            analysis.kinds[&SlotRef::Local(allocate, slot)],
            SlotKind::Owning
        );
    })
    .unwrap();
    let records = generate(source);
    for name in ["allocate", "nullable"] {
        let record = function(&records, name);
        assert_eq!(
            record.target_signature,
            format!("pub unsafe fn {name}(mut size: usize) -> *mut core::ffi::c_void")
        );
        assert!(
            record
                .baseline
                .skeleton
                .contains("let mut p: *mut ::core::ffi::c_void"),
            "{}",
            record.baseline.skeleton
        );
    }
    assert_stub_signatures_compile(&records, "");
}

#[test]
fn borrowed_void_pointers_keep_mutability_nulls_and_existing_references() {
    use pointer_replacer_bo::analyses::borrow_ownership::{SlotKind, solver::SlotRef};

    let source = r#"
use core::ffi::c_void as Void;
pub unsafe fn shared(p: *const Void) -> *const Void {
    let q = p;
    if q.is_null() { core::ptr::null() } else { q }
}
pub unsafe fn mutable(p: *mut Void) -> *mut Void {
    let q = p;
    if q.is_null() { core::ptr::null_mut() } else { q }
}
pub unsafe fn array(p: *mut Void) -> *mut Void { let q = p.add(1); q }
pub unsafe fn none() -> *const Void { core::ptr::null() }
pub unsafe fn none_mut() -> *mut Void { core::ptr::null_mut() }
pub unsafe fn reference(p: &Void) -> &Void { p }
pub unsafe fn reference_mut(p: &mut Void) -> &mut Void { p }
pub struct c_void { value: i32 }
pub unsafe fn lookalike(p: *const c_void) -> i32 { (*p).value }
"#;
    run_compiler_on_str(source, |tcx| {
        let analysis = pointer_replacer_bo::analyze_pointers(tcx).unwrap();
        for name in ["shared", "mutable"] {
            let function = local_def(name, tcx);
            let slot = analysis.slots.fn_local_slots[&function]
                .slot_for_local_depth(rustc_middle::mir::Local::from_usize(1), 0)
                .unwrap();
            assert_eq!(
                analysis.kinds[&SlotRef::Local(function, slot)],
                SlotKind::Ref
            );
        }
    })
    .unwrap();
    let records = generate(source);
    for (name, raw) in [
        ("shared", "*const Void"),
        ("mutable", "*mut Void"),
        ("array", "*mut Void"),
    ] {
        let record = function(&records, name);
        assert_eq!(
            record.target_signature,
            format!("pub unsafe fn {name}(mut p: {raw}) -> {raw}")
        );
        assert!(
            record
                .baseline
                .skeleton
                .contains(&format!("let mut q: {raw}"))
        );
    }
    for (name, raw) in [("none", "*const Void"), ("none_mut", "*mut Void")] {
        let signature = &function(&records, name).target_signature;
        assert!(signature.ends_with(raw), "{signature}");
        let transformed = format!(
            "use core::ffi::c_void as Void; {signature} {{ core::ptr::{name}() }}",
            name = if name == "none" { "null" } else { "null_mut" }
        );
        run_compiler_on_str(&transformed, utils::type_check).expect(&transformed);
    }
    for name in ["reference", "reference_mut", "lookalike"] {
        assert_eq!(
            signature_indirections(&function(&records, name).target_signature),
            "&"
        );
    }
    assert_stub_signatures_compile(
        &records,
        "use core::ffi::c_void as Void; pub struct c_void { value: i32 }",
    );
}

#[test]
fn nested_void_pointers_keep_raw_inner_layers_in_rules_and_metadata() {
    let source = r#"
use core::ffi::c_void as Void;
pub unsafe fn read(p: *const *mut Void) -> *mut Void {
    let q = *p;
    if q.is_null() { core::ptr::null_mut() } else { q }
}
pub unsafe fn store(p: *mut *mut Void, q: *mut Void) { *p = q; }
pub unsafe fn deep(p: *const *const *mut Void) -> *mut Void { **p }
"#;
    run_compiler_on_str(source, |tcx| {
        let decisions = tools_pointer_decisions(tcx);
        let read = local_def("read", tcx);
        assert_eq!(
            decisions.signatures.data[&read].input_decs[0],
            Some(PtrKind::Ref(false))
        );
        assert_eq!(
            decisions.nested(PointerTarget::Input(read, 0))[0].kind,
            PtrKind::Raw(true)
        );
        let mut surface = utils::ast::parse_crate(source.to_owned());
        let mut mapper = utils::ir::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
        let catalog =
            rule_binding_catalog(&surface.items[1], read, &decisions, &mapper.ast_to_hir, tcx);
        let binding = local_binding_hir_id(read, "p", tcx);
        let TypeTree::Reference { pointee, .. } = &catalog[&binding] else {
            panic!("missing reference")
        };
        let TypeTree::RawPointer {
            mutability,
            pointee,
        } = pointee.as_ref()
        else {
            panic!("missing raw void pointer")
        };
        assert_eq!(*mutability, RawMutability::Mut);
        let void = match tcx
            .fn_sig(read)
            .instantiate_identity()
            .skip_binder()
            .inputs()[0]
            .kind()
        {
            ty::TyKind::RawPtr(inner, _) => match inner.kind() {
                ty::TyKind::RawPtr(void, _) => *void,
                _ => unreachable!(),
            },
            _ => unreachable!(),
        };
        assert_eq!(
            pointee.as_ref(),
            &semantic_type_tree(void, &mapper.ast_to_hir, tcx).unwrap()
        );
    })
    .unwrap();
    let records = generate(source);
    for (name, expected) in [("read", "&*"), ("store", "&*"), ("deep", "&&*")] {
        let record = function(&records, name);
        assert_eq!(signature_indirections(&record.target_signature), expected);
    }
    let read = function(&records, "read");
    let row = read
        .baseline
        .statement_pair_metadata
        .iter()
        .flat_map(|pair| &pair.pointer_variables)
        .find(|row| row.name == "q")
        .unwrap();
    assert_eq!(row.selected_target_type, "*mut Void");
    assert_stub_signatures_compile(&records, "use core::ffi::c_void as Void;");
}

#[test]
fn typed_borrow_returns_from_raw_void_parameters_keep_the_lifetime_error() {
    let source =
        "pub unsafe fn cast(p: *const core::ffi::c_void) -> *const i32 { p as *const i32 }";
    let error =
        run_compiler_on_str(source, |tcx| make_skeletons(source, tcx).unwrap_err()).unwrap();
    assert_eq!(error.kind, GenerationErrorKind::PointerAnalysis);
    assert!(
        error
            .message
            .contains("cannot determine the lifetime of cast return pointer at depth 0")
    );
}

#[test]
fn allocation_extent_survives_preserved_struct_field_initializers() {
    let source = "unsafe extern \"C\" { fn malloc(size: usize) -> *mut i32; } pub struct Holder { p: *mut i32 } pub unsafe fn allocate() -> *mut i32 { let holder = Holder { p: malloc(4 * core::mem::size_of::<i32>()) }; let p = holder.p; *p = 7; p }";
    let records = generate(source);
    let signature = &function(&records, "allocate").target_signature;
    assert!(signature.ends_with("Box<[i32]>"), "{signature}");
    assert!(
        type_record(&records, "Holder")
            .definition
            .contains("p: *mut i32")
    );
    assert_stub_signatures_compile(&records, "pub struct Holder { p: *mut i32 }");
}

#[test]
fn existing_shared_lifetime_parameters_do_not_create_undeclared_bounds() {
    let records = generate("pub unsafe fn sum<'a>(x: &'a i32, y: &'a i32) -> i32 { *x + *y }");
    let signature = &function(&records, "sum").target_signature;
    assert!(!signature.contains("'b"), "{signature}");
    let transformed = format!("{signature} {{ *x + *y }}");
    run_compiler_on_str(&transformed, utils::type_check).expect(&transformed);
}

#[test]
fn null_tests_of_loaded_pointers_make_the_inner_layer_optional() {
    let records = generate(
        "pub unsafe fn read(p: *const *const i32) -> i32 { let q = *p; if q.is_null() { 0 } else { *q } }",
    );
    let read = function(&records, "read");
    assert!(
        read.target_signature.contains("p: &Option<&i32>"),
        "{}",
        read.target_signature
    );
    assert!(read.baseline.skeleton.contains("let mut q: Option<&i32>"));
    let transformed = format!(
        "{} {{ let q = *p; q.map_or(0, |q| *q) }}",
        read.target_signature
    );
    run_compiler_on_str(&transformed, utils::type_check).expect(&transformed);
}

#[test]
fn diverging_bodies_admit_reference_return_types_without_input_origins() {
    for body in ["loop {}", "std::process::abort()"] {
        let records = generate(&format!("pub unsafe fn stop() -> *const i32 {{ {body} }}"));
        let signature = &function(&records, "stop").target_signature;
        assert!(signature.contains("-> &"), "{signature}");
        let transformed = format!("{signature} {{ {body} }}");
        run_compiler_on_str(&transformed, utils::type_check).expect(&transformed);
    }
}
