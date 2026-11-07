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
fn struct_fields_change_while_globals_keep_original_types() {
    let source = r#"
pub struct Holder { pub pointer: *const *const i32 }
static mut GLOBAL: *const *const i32 = core::ptr::null();
pub unsafe fn read(holder: *const Holder) -> i32 { **(*holder).pointer }
"#;
    let records = generate(source);
    assert!(
        type_record(&records, "Holder")
            .source_definition
            .contains("pointer: *const *const i32")
    );
    assert!(
        value(&records, "GLOBAL")
            .declaration
            .contains("*const *const i32")
    );
    let holder = type_record(&records, "Holder");
    assert!(
        holder.target_definition.contains("pointer: &'"),
        "{}",
        holder.target_definition
    );
    assert_stub_signatures_compile(&records, &holder.target_definition);
}

fn compile_target_bodies(source: &str, bodies: &[(&str, &str)]) -> Vec<ItemRecord> {
    let records = generate(source);
    let definitions = records
        .iter()
        .filter_map(|record| match record {
            ItemRecord::Type(record) => Some(record.target_definition.as_str()),
            _ => None,
        })
        .collect::<Vec<_>>()
        .join("\n");
    let functions = bodies
        .iter()
        .map(|(name, body)| format!("{} {{ {body} }}", function(&records, name).target_signature))
        .collect::<Vec<_>>()
        .join("\n");
    let target = format!("{definitions}\n{functions}");
    run_compiler_on_str(&target, utils::type_check).expect(&target);
    records
}

#[test]
fn nested_field_returns_keep_the_terminal_reference_lifetime() {
    let source = r#"
pub struct Entry { pub value: *const i32 }
pub struct Map { pub entries: *const Entry }
pub struct Tree { pub map: *const Map }
pub unsafe fn lookup(map: *const Map, i: isize) -> *const i32 {
    let entries = (*map).entries;
    let item = entries.offset(i);
    (*item).value
}
pub unsafe fn get(tree: *const Tree, i: isize) -> *const i32 { lookup((*tree).map, i) }
"#;
    let records = compile_target_bodies(
        source,
        &[
            ("lookup", "map.entries[i as usize].value"),
            ("get", "lookup(tree.map, i)"),
        ],
    );
    for name in ["lookup", "get"] {
        let signature = &function(&records, name).target_signature;
        assert!(signature.contains("-> &'"), "{signature}");
        assert!(signature.ends_with("i32"), "{signature}");
    }
}

#[test]
fn projected_struct_fields_and_value_copies_preserve_borrowed_returns() {
    let source = r#"
pub struct Entry { pub value: *const i32 }
pub struct Pair { pub left: Entry, pub right: Entry }
pub unsafe fn read(entry: *const Entry) -> *const i32 { (*entry).value }
pub unsafe fn left(pair: *const Pair) -> *const i32 { read(&raw const (*pair).left) }
pub unsafe fn copied(pair: Pair) -> *const i32 { let entry = pair.left; read(&entry) }
"#;
    let records = compile_target_bodies(
        source,
        &[
            ("read", "entry.value"),
            ("left", "read(&pair.left)"),
            ("copied", "let entry = pair.left; read(&entry)"),
        ],
    );
    for name in ["read", "left", "copied"] {
        let signature = &function(&records, name).target_signature;
        assert!(signature.contains("-> &'"), "{signature}");
    }
}

#[test]
fn nested_void_values_and_unsupported_paths_retain_raw_returns() {
    let source = r#"
use core::ffi::c_void;
pub struct Node { pub number: i32 }
pub struct Entry { pub value: *mut c_void }
pub struct Map { pub entries: *const Entry }
pub struct Tree { pub map: *const Map }
pub struct Outer { pub tree: *const Tree }
pub unsafe fn lookup(map: *const Map, i: isize) -> *mut c_void { (*(*map).entries.offset(i)).value }
pub unsafe fn get(tree: *const Tree, i: isize) -> *mut Node { lookup((*tree).map, i) as *mut Node }
pub unsafe fn deeper(outer: *const Outer) -> *mut Node { get((*outer).tree, 0) }
"#;
    let frozen = run_compiler_on_str(source, |tcx| {
        let records = make_skeletons(source, tcx).unwrap();
        for name in ["get", "deeper"] {
            let signature = &function(&records, name).target_signature;
            assert!(signature.ends_with("*mut Node"), "{signature}");
        }
        assert!(
            type_record(&records, "Entry")
                .target_definition
                .contains("value: *mut c_void")
        );
        crate::freeze_project(source, &records, tcx).unwrap()
    })
    .unwrap();
    run_compiler_on_str(&frozen.target_source, utils::type_check).expect(&frozen.target_source);
}

#[test]
fn raw_container_links_cannot_supply_owned_field_borrow_lifetimes() {
    let source = r#"
unsafe extern "C" { fn malloc(size: usize) -> *mut i32; fn free(p: *mut i32); }
#[repr(C)] pub struct Entry { pub value: *mut i32 }
#[repr(C)] pub struct Map { pub entries: *const Entry }
pub unsafe fn allocate() -> Entry { let value = malloc(core::mem::size_of::<i32>()); *value = 7; Entry { value } }
pub unsafe fn release(entry: Entry) { free(entry.value); }
pub unsafe fn get(map: *const Map, i: isize) -> *const i32 { &*(*(*map).entries.offset(i)).value as *const i32 }
pub unsafe extern "C" fn api(_map: *const Map) {}
"#;
    let frozen = run_compiler_on_str(source, |tcx| {
        let records =
            make_skeletons_with_api(source, None, &FxHashSet::from_iter(["api".to_owned()]), tcx)
                .unwrap();
        let entry = &type_record(&records, "Entry").target_definition;
        assert!(entry.contains("Box<i32>"), "{entry}");
        let map = &type_record(&records, "Map").target_definition;
        assert!(map.contains("entries: *const Entry"), "{map}");
        let signature = &function(&records, "get").target_signature;
        assert!(signature.ends_with("*const i32"), "{signature}");
        crate::freeze_project(source, &records, tcx).unwrap()
    })
    .unwrap();
    run_compiler_on_str(&frozen.target_source, utils::type_check).expect(&frozen.target_source);
    compile_target_bodies(source, &[("get", "&*map.entries[i as usize].value")]);
}

#[test]
fn raw_outer_field_layers_cannot_supply_mutable_inner_borrow_lifetimes() {
    let source = r#"
#[repr(C)] pub struct Holder { pub cells: *const *mut i32 }
pub unsafe fn get(holder: *const Holder, i: isize) -> *mut i32 { *(*holder).cells.offset(i) }
pub unsafe fn write(holder: *const Holder, i: isize) { *get(holder, i) = 9; }
pub unsafe extern "C" fn api(_holder: *const Holder) {}
"#;
    let frozen = run_compiler_on_str(source, |tcx| {
        let records =
            make_skeletons_with_api(source, None, &FxHashSet::from_iter(["api".to_owned()]), tcx)
                .unwrap();
        let definition = &type_record(&records, "Holder").target_definition;
        assert!(definition.contains("cells: *const &'"), "{definition}");
        assert!(definition.contains("mut i32"), "{definition}");
        let signature = &function(&records, "get").target_signature;
        assert!(signature.ends_with("*mut i32"), "{signature}");
        crate::freeze_project(source, &records, tcx).unwrap()
    })
    .unwrap();
    run_compiler_on_str(&frozen.target_source, utils::type_check).expect(&frozen.target_source);
}

#[test]
fn recursive_traversals_outside_the_origin_domain_retain_raw_returns() {
    let source = r#"
pub struct Link { pub next: *mut Link }
pub unsafe fn walk(mut head: *mut Link) -> *mut Link {
    while !(*head).next.is_null() { head = (*head).next; }
    head
}
"#;
    let frozen = run_compiler_on_str(source, |tcx| {
        let records = make_skeletons(source, tcx).unwrap();
        let signature = &function(&records, "walk").target_signature;
        assert!(signature.ends_with("*mut Link"), "{signature}");
        crate::freeze_project(source, &records, tcx).unwrap()
    })
    .unwrap();
    run_compiler_on_str(&frozen.target_source, utils::type_check).expect(&frozen.target_source);
}

#[test]
fn unresolved_allocated_field_contents_do_not_block_owning_returns() {
    let source = r#"
unsafe extern "C" { fn malloc(size: usize) -> *mut core::ffi::c_void; fn free(p: *mut core::ffi::c_void); }
pub struct Holder { pub value: *const i32 }
pub unsafe fn make(p: *const i32) -> *mut Holder {
    let holder = malloc(core::mem::size_of::<Holder>()) as *mut Holder;
    (*holder).value = p;
    holder
}
pub unsafe fn release(holder: *mut Holder) { free(holder as *mut core::ffi::c_void); }
"#;
    let records = compile_target_bodies(
        source,
        &[
            ("make", "Box::new(Holder { value: p as *const i32 })"),
            ("release", "drop(holder);"),
        ],
    );
    let signature = &function(&records, "make").target_signature;
    assert!(signature.ends_with("Box<Holder>"), "{signature}");
    let definition = &type_record(&records, "Holder").target_definition;
    assert!(definition.contains("value: *const i32"), "{definition}");
}

#[test]
fn memchr_void_casts_produce_slice_inputs_and_nullable_borrowed_returns() {
    let source = r#"
use core::ffi::c_void;
unsafe extern "C" {
    fn memchr(p: *const c_void, c: i32, n: usize) -> *mut c_void;
    #[link_name = "memchr"] fn malloc(p: *const c_void, c: i32, n: usize) -> *mut c_void;
}
pub unsafe fn read(p: *const u8, n: usize) -> *mut u8 {
    let erased = p as *const c_void;
    let found = memchr(erased, 7, n);
    found as *mut u8
}
pub unsafe fn alias(p: *const u8, n: usize) -> *mut u8 { malloc(p as *const c_void, 7, n) as *mut u8 }
pub unsafe fn external(p: *const u8, n: usize) -> *mut u8 { libc::memchr(p as *const c_void, 7, n) as *mut u8 }
pub unsafe fn write(p: *mut u8, n: usize) -> *mut u8 {
    let found = memchr(p as *const c_void, 7, n) as *mut u8;
    if !found.is_null() { *found = 8; }
    found
}
pub unsafe fn mutate(p: *mut u8, n: usize) {
    let found = write(p, n);
    if !found.is_null() { *found = 9; }
}
"#;
    let records = compile_target_bodies(
        source,
        &[
            ("read", "p[..n].iter().find(|byte| **byte == 7)"),
            ("alias", "p[..n].iter().find(|byte| **byte == 7)"),
            ("external", "p[..n].iter().find(|byte| **byte == 7)"),
            (
                "write",
                "let index = p[..n].iter().position(|byte| *byte == 7)?; let found = &mut p[index]; *found = 8; Some(found)",
            ),
            ("mutate", "if let Some(found) = write(p, n) { *found = 9; }"),
        ],
    );
    for name in ["read", "alias", "external", "write"] {
        let signature = &function(&records, name).target_signature;
        assert!(signature.contains("-> Option<&'"), "{signature}");
        assert!(signature.ends_with("u8>"), "{signature}");
        assert_eq!(
            signature.contains("mut [u8]"),
            name == "write",
            "{signature}"
        );
        assert!(!signature.contains("Box"), "{signature}");
        assert_eq!(
            signature.ends_with("mut u8>"),
            name == "write",
            "{signature}"
        );
    }
    let skeleton = &function(&records, "read").baseline.skeleton;
    assert!(skeleton.contains("erased: *const c_void"), "{skeleton}");
    assert!(skeleton.contains("found: *mut c_void"), "{skeleton}");
}

#[test]
fn allocator_extent_uses_the_foreign_symbol_for_aliases_and_external_declarations() {
    let source = r#"
unsafe extern "C" {
    #[link_name = "malloc"] fn memchr(n: usize) -> *mut core::ffi::c_void;
}
pub unsafe fn alias() -> *mut i32 {
    let p = memchr(4 * core::mem::size_of::<i32>()) as *mut i32;
    *p = 7;
    p
}
pub unsafe fn external() -> *mut i32 {
    let p = libc::malloc(4 * core::mem::size_of::<i32>()) as *mut i32;
    *p = 7;
    p
}
"#;
    let records = compile_target_bodies(
        source,
        &[
            ("alias", "vec![7, 0, 0, 0].into_boxed_slice()"),
            ("external", "vec![7, 0, 0, 0].into_boxed_slice()"),
        ],
    );
    for name in ["alias", "external"] {
        let signature = &function(&records, name).target_signature;
        assert!(signature.ends_with("Box<[i32]>"), "{signature}");
    }
}

#[test]
fn memchr_writes_promote_const_pointer_sources_to_mutable_borrows() {
    let source = r#"
unsafe extern "C" {
    fn memchr(p: *const core::ffi::c_void, c: i32, n: usize) -> *mut core::ffi::c_void;
}
pub struct Holder { pub p: *const u8 }
pub unsafe fn make(p: *const u8) -> Holder { Holder { p } }
pub unsafe fn write(p: *const u8, n: usize) -> *mut u8 {
    let found = memchr(p as *const core::ffi::c_void, 7, n) as *mut u8;
    if !found.is_null() { *found = 8; }
    found
}
pub unsafe fn caller(p: *const u8, n: usize) -> *mut u8 { write(p, n) }
pub unsafe fn field(h: *mut Holder, n: usize) -> *mut u8 { write((*h).p, n) }
"#;
    let records = compile_target_bodies(
        source,
        &[
            ("make", "Holder { p }"),
            (
                "write",
                "let index = p[..n].iter().position(|byte| *byte == 7)?; let found = &mut p[index]; *found = 8; Some(found)",
            ),
            ("caller", "write(p, n)"),
            ("field", "write(h.p, n)"),
        ],
    );
    for name in ["write", "caller"] {
        let signature = &function(&records, name).target_signature;
        assert!(signature.contains("mut [u8]"), "{signature}");
        assert!(signature.contains("-> Option<&'"), "{signature}");
    }
    let definition = &type_record(&records, "Holder").target_definition;
    assert!(definition.contains("mut [u8]"), "{definition}");
}

#[test]
fn field_borrow_lifetimes_support_construction_setters_and_getters() {
    let source = r#"
pub struct Holder { pub pointer: *const i32 }
pub unsafe fn make(pointer: *const i32) -> Holder { Holder { pointer } }
pub unsafe fn set(holder: *mut Holder, pointer: *const i32) { (*holder).pointer = pointer; }
pub unsafe fn get(holder: *const Holder) -> *const i32 { (*holder).pointer }
"#;
    let records = compile_target_bodies(
        source,
        &[
            ("make", "Holder { pointer }"),
            ("set", "holder.pointer = pointer;"),
            ("get", "holder.pointer"),
        ],
    );
    let holder = type_record(&records, "Holder");
    assert!(holder.source_definition.contains("*const i32"));
    assert!(
        holder.target_definition.contains("&'"),
        "{}",
        holder.target_definition
    );
    assert!(function(&records, "set").target_signature.contains(":"));
}

#[test]
fn field_lifetimes_propagate_through_aliases_containers_and_enums() {
    let source = r#"
#[derive(Clone, Copy)] pub struct Holder { pub pointer: *const i32 }
pub type Alias = Holder;
#[derive(Clone, Copy)] pub struct Container { pub holder: Alias }
#[derive(Clone, Copy)] pub enum Choice { Value(Container), Empty }
pub unsafe fn make(pointer: *const i32) -> Choice { Choice::Value(Container { holder: Holder { pointer } }) }
pub unsafe fn read(holder: *const Holder) -> i32 { *(*holder).pointer }
"#;
    let records = compile_target_bodies(
        source,
        &[
            (
                "make",
                "Choice::Value(Container { holder: Holder { pointer } })",
            ),
            ("read", "*holder.pointer"),
        ],
    );
    for name in ["Holder", "Alias", "Container", "Choice"] {
        let record = type_record(&records, name);
        assert_ne!(record.source_definition, record.target_definition, "{name}");
        assert!(
            record.target_definition.contains("<'"),
            "{}",
            record.target_definition
        );
    }
}

#[test]
fn mutable_fields_remove_incompatible_derives_from_containers() {
    let source = r#"
#[derive(Clone, Copy, Debug)] pub struct Holder { pub pointer: *mut i32 }
#[derive(Clone, Copy, Debug)] pub struct Container { pub holder: Holder }
#[derive(Clone, Copy, Debug)] pub enum Choice { Value(Container), Empty }
pub unsafe fn make(pointer: *mut i32) -> Holder { Holder { pointer } }
pub unsafe fn write(holder: *mut Holder) { *(*holder).pointer = 7; }
"#;
    let records = compile_target_bodies(
        source,
        &[
            ("make", "Holder { pointer }"),
            ("write", "*holder.pointer = 7;"),
        ],
    );
    for name in ["Holder", "Container", "Choice"] {
        let target = &type_record(&records, name).target_definition;
        assert!(!target.contains("Copy"), "{target}");
        assert!(!target.contains("Clone"), "{target}");
        assert!(target.contains("Debug"), "{target}");
    }
}

#[test]
fn field_lifetimes_keep_multiple_structs_and_module_identities_distinct() {
    let source = r#"
pub mod left { pub struct Holder { pub pointer: *const i32 } }
pub mod right { pub struct Holder { pub pointer: *const i64 } }
pub unsafe fn make(p: *const i32, q: *const i64) -> (left::Holder, right::Holder) {
    (left::Holder { pointer: p }, right::Holder { pointer: q })
}
pub unsafe fn read(a: *const left::Holder, b: *const right::Holder) -> i64 { *(*a).pointer as i64 + *(*b).pointer }
"#;
    let frozen = run_compiler_on_str(source, |tcx| {
        let records = make_skeletons(source, tcx).unwrap();
        crate::freeze_project(source, &records, tcx).unwrap()
    })
    .unwrap();
    run_compiler_on_str(&frozen.target_source, utils::type_check).expect(&frozen.target_source);
    assert!(
        !frozen.target_source.contains("*const"),
        "{}",
        frozen.target_source
    );
}

#[test]
fn configured_api_exposure_preserves_transitive_array_fields_and_promotes_thin_fields() {
    let source = r#"
#[repr(C)] pub struct Inner { pub pointer: *const i32, pub buffer: *const u8 }
pub type Alias = Inner;
pub enum Outer { Value(Alias), Empty }
pub struct Private { pub pointer: *const i32 }
pub struct Foreign { pub pointer: *const i32 }
#[export_name = "external_api"] pub unsafe extern "C" fn exported(value: *const Outer) -> *const Outer { value }
pub unsafe fn private_read(value: *const Private) -> i32 { *(*value).pointer }
pub unsafe fn public_read(value: *const Inner) -> i32 { if (*value).pointer.is_null() { 0 } else { *(*value).pointer + *(*value).buffer.offset(1) as i32 } }
extern "C" { fn foreign(value: *const Foreign); }
pub unsafe fn invoke(value: *const Foreign) { foreign(value); }
"#;
    let (records, frozen) = run_compiler_on_str(source, |tcx| {
        let records = make_skeletons_with_api(
            source,
            None,
            &FxHashSet::from_iter(["external_api".to_owned()]),
            tcx,
        )
        .unwrap();
        let frozen = crate::freeze_project(source, &records, tcx).unwrap();
        (records, frozen)
    })
    .unwrap();
    for name in ["Inner", "Alias", "Outer"] {
        let record = type_record(&records, name);
        assert_ne!(record.source_definition, record.target_definition, "{name}");
    }
    let inner = &type_record(&records, "Inner").target_definition;
    assert!(inner.contains("pointer: Option<&'"), "{inner}");
    assert!(inner.contains("buffer: *const u8"), "{inner}");
    let private = type_record(&records, "Private");
    assert_ne!(private.source_definition, private.target_definition);
    let foreign = type_record(&records, "Foreign");
    assert_eq!(foreign.source_definition, foreign.target_definition);
    run_compiler_on_str(&frozen.target_source, utils::type_check).expect(&frozen.target_source);

    let unprotected = generate(source);
    assert!(
        type_record(&unprotected, "Inner")
            .target_definition
            .contains("[u8]")
    );
}

#[test]
fn foreign_statics_preserve_recursive_definitions_aliases_derives_and_pointer_layers() {
    let source = r#"
#[repr(C)] #[derive(Clone, Copy, Debug)] pub struct Stream {
    pub buffer: *mut u8,
    pub next: *mut Stream,
    pub indirect: *const *const i32,
}
pub type FILE = Stream;
extern "C" { static mut stdin: *mut FILE; }
pub unsafe fn write(stream: *mut FILE) { *(*stream).buffer = 7; }
pub unsafe fn read(stream: *const FILE) -> i32 { **(*stream).indirect }
"#;
    let frozen = run_compiler_on_str(source, |tcx| {
        let records = make_skeletons(source, tcx).unwrap();
        for name in ["Stream", "FILE"] {
            let record = type_record(&records, name);
            assert_eq!(record.source_definition, record.target_definition, "{name}");
        }
        assert!(
            function(&records, "write")
                .target_signature
                .contains("*mut FILE")
        );
        crate::freeze_project(source, &records, tcx).unwrap()
    })
    .unwrap();
    let reloaded =
        crate::frozen_project_from_json(&serde_json::to_string(&frozen).unwrap()).unwrap();
    assert_eq!(reloaded, frozen);
    run_compiler_on_str(&frozen.target_source, utils::type_check).expect(&frozen.target_source);
}

#[test]
fn file_pointer_aliases_keep_raw_layers_mutability_and_existing_references() {
    let source = r#"
pub struct Stream { pub value: i32 }
pub type FILE = Stream;
pub type Alias = FILE;
pub type Handle = *mut Alias;
pub unsafe fn shared(pointer: *const FILE) -> *const FILE { let q: *const FILE = pointer; q }
pub unsafe fn mutable(pointer: *mut FILE) -> *mut FILE { let q: *mut FILE = pointer; q }
pub unsafe fn nullable(pointer: *mut FILE) -> *mut FILE {
    let q: *mut FILE = pointer;
    if q.is_null() { core::ptr::null_mut() } else { q }
}
pub unsafe fn nested(pointer: *mut *const Alias) -> *mut *const Alias { let q: *mut *const Alias = pointer; q }
pub unsafe fn deep(pointer: *const *const *mut FILE) -> *const *const *mut FILE { pointer }
pub unsafe fn array(pointer: *const [*mut FILE; 2]) -> *const [*mut FILE; 2] { pointer }
pub unsafe fn alias(pointer: Handle) -> Handle { pointer }
pub unsafe fn existing<'a>(pointer: &'a mut FILE) -> &'a mut FILE { pointer }
pub unsafe fn ordinary(pointer: *const i32) -> i32 { *pointer }
"#;
    run_compiler_on_str(source, |tcx| {
        let analysis = pointer_replacer_bo::analyze_pointers(tcx).unwrap();
        let shared = local_def("shared", tcx);
        let slot = analysis.slots.fn_local_slots[&shared]
            .slot_for_local_depth(rustc_middle::mir::Local::from_usize(1), 0)
            .unwrap();
        assert_eq!(
            analysis.kinds
                [&pointer_replacer_bo::analyses::borrow_ownership::solver::SlotRef::Local(
                    shared, slot
                )],
            pointer_replacer_bo::analyses::borrow_ownership::SlotKind::Ref
        );
    })
    .unwrap();
    let records = generate(source);
    for name in [
        "shared", "mutable", "nullable", "nested", "deep", "array", "existing",
    ] {
        let record = function(&records, name);
        assert_eq!(record.source_signature, record.target_signature, "{name}");
    }
    let alias = &function(&records, "alias").target_signature;
    assert_eq!(signature_indirections(alias), "*");
    assert!(alias.contains("-> *mut"), "{alias}");
    let handle = type_record(&records, "Handle");
    assert_eq!(handle.source_definition, handle.target_definition);
    for (name, pointer) in [
        ("shared", "*const FILE"),
        ("mutable", "*mut FILE"),
        ("nullable", "*mut FILE"),
        ("nested", "*mut *const Alias"),
    ] {
        let record = function(&records, name);
        assert!(
            record
                .baseline
                .skeleton
                .contains(&format!("let mut q: {pointer}")),
            "{}",
            record.baseline.skeleton
        );
    }
    assert!(
        function(&records, "ordinary")
            .target_signature
            .contains("&i32")
    );
    assert_stub_signatures_compile(
        &records,
        "pub struct Stream { pub value: i32 } pub type FILE = Stream; pub type Alias = FILE; pub type Handle = *mut Alias;",
    );
}

#[test]
fn file_definitions_stay_fixed_without_freezing_unrelated_wrapper_fields() {
    let template = r#"
pub struct Support { pub pointer: *const i32 }
#[repr(C)] #[derive(Clone, Copy, Debug)] pub struct StreamType {
    pub buffer: *mut u8,
    pub support: *const Support,
}
pub type Alias = StreamType;
pub struct Wrapper { pub handle: *mut Alias, pub indirect: *const *mut Alias, pub values: *const i32 }
pub unsafe fn read_stream(stream: *const StreamType) -> i32 { *(*(*stream).support).pointer }
pub unsafe fn read_wrapper(wrapper: *const Wrapper) -> i32 { *(*wrapper).values }
"#;
    for name in ["FILE", "_IO_FILE", "__sFILE", "_IO_FILE_plus"] {
        let source = template.replace("StreamType", name);
        let records = compile_target_bodies(
            &source,
            &[
                ("read_stream", "*(*(*stream).support).pointer"),
                ("read_wrapper", "*wrapper.values"),
            ],
        );
        for protected in [name, "Support", "Alias"] {
            let record = type_record(&records, protected);
            assert_eq!(
                record.source_definition, record.target_definition,
                "{protected}"
            );
        }
        let wrapper = &type_record(&records, "Wrapper").target_definition;
        assert!(wrapper.contains("handle: *mut Alias"), "{wrapper}");
        assert!(wrapper.contains("indirect: *const *mut Alias"), "{wrapper}");
        assert!(wrapper.contains("values: &'"), "{wrapper}");
        assert!(
            function(&records, "read_wrapper")
                .target_signature
                .contains("&'")
        );
    }
}

#[test]
fn file_ownership_and_array_inference_cannot_promote_handles_or_fields() {
    use pointer_replacer_bo::analyses::borrow_ownership::{SlotKind, solver::SlotRef};

    for size in [
        "core::mem::size_of::<FILE>()",
        "4 * core::mem::size_of::<FILE>()",
    ] {
        let template = r#"
pub struct FILE { pub value: i32 }
#[derive(Clone, Copy)] pub struct Holder { pub handle: *mut FILE }
unsafe extern "C" { fn malloc(size: usize) -> *mut core::ffi::c_void; fn free(pointer: *mut core::ffi::c_void); }
pub unsafe fn allocate() -> *mut FILE {
    let pointer: *mut FILE = malloc(ALLOCATION_SIZE) as *mut FILE;
    (*pointer).value = 7;
    pointer
}
pub unsafe fn nullable() -> *mut FILE {
    let pointer: *mut FILE = allocate();
    if pointer.is_null() { core::ptr::null_mut() } else { pointer }
}
pub unsafe fn holder() -> Holder { Holder { handle: allocate() } }
pub unsafe fn release(value: Holder) { free(value.handle as *mut core::ffi::c_void); }
"#;
        let source = template.replace("ALLOCATION_SIZE", size);
        run_compiler_on_str(&source, |tcx| {
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
        let frozen = run_compiler_on_str(&source, |tcx| {
            let records = make_skeletons(&source, tcx).unwrap();
            for name in ["allocate", "nullable"] {
                let record = function(&records, name);
                assert_eq!(record.source_signature, record.target_signature, "{name}");
                assert!(
                    record
                        .baseline
                        .skeleton
                        .contains("let mut pointer: *mut FILE")
                );
            }
            let holder = type_record(&records, "Holder");
            assert_eq!(holder.source_definition, holder.target_definition);
            crate::freeze_project(&source, &records, tcx).unwrap()
        })
        .unwrap();
        run_compiler_on_str(&frozen.target_source, utils::type_check).expect(&frozen.target_source);
    }
}

#[test]
fn opaque_file_aliases_keep_the_original_pointer_chain() {
    let source = r#"
#![feature(extern_types)]
unsafe extern "C" { pub type Stream; }
pub type FILE = Stream;
pub type Alias = FILE;
pub unsafe fn direct(pointer: *mut Alias) -> *mut Alias { pointer }
pub unsafe fn nested(pointer: *const *mut Alias) -> *const *mut Alias { pointer }
"#;
    let frozen = run_compiler_on_str(source, |tcx| {
        let records = make_skeletons(source, tcx).unwrap();
        for name in ["direct", "nested"] {
            let record = function(&records, name);
            assert_eq!(record.source_signature, record.target_signature, "{name}");
        }
        crate::freeze_project(source, &records, tcx).unwrap()
    })
    .unwrap();
    run_compiler_on_str(&frozen.target_source, utils::type_check).expect(&frozen.target_source);
}

#[test]
fn file_policy_holds_do_not_create_unknown_return_origins() {
    let source = r#"
pub struct FILE { pub value: i32 }
pub unsafe fn stop() -> *const FILE { loop {} }
pub unsafe fn typed(pointer: *const i32, flag: bool) -> *const i32 {
    if flag { pointer } else { stop() as *const i32 }
}
"#;
    let records = compile_target_bodies(
        source,
        &[
            ("stop", "loop {}"),
            (
                "typed",
                "if flag { pointer } else { &*(stop() as *const i32) }",
            ),
        ],
    );
    assert!(
        function(&records, "stop")
            .target_signature
            .ends_with("*const FILE")
    );
    assert!(
        function(&records, "typed")
            .target_signature
            .contains("-> &'")
    );
}

#[test]
fn foreign_signatures_preserve_nested_types_and_callback_aliases_without_calls() {
    let definitions = r#"
#[repr(C)] #[derive(Clone, Copy, Debug)] pub struct Leaf { pub pointer: *mut i32 }
pub type Alias = Leaf;
pub struct EnumLeaf { pub pointer: *const i32 }
pub struct ArrayLeaf { pub pointer: *const i32 }
pub struct TupleLeaf { pub pointer: *const i32 }
pub struct GenericLeaf { pub pointer: *const i32 }
pub enum Choice { Value(EnumLeaf), Empty }
#[derive(Clone, Copy)] pub union Storage { pub leaf: Leaf, pub bits: usize }
pub struct Wrapper<T> { pub value: T }
pub struct Input { pub pointer: *const i32 }
pub struct Output { pub pointer: *const i32 }
pub type Callback = unsafe extern "C" fn(*const Input) -> *mut Output;
pub struct Envelope {
    pub choice: Choice,
    pub storage: Storage,
    pub callback: Callback,
    pub nested: *const *const Leaf,
    pub alias: Alias,
    pub array: [ArrayLeaf; 2],
    pub tuple: (TupleLeaf, i32),
    pub generic: Wrapper<GenericLeaf>,
}
pub type EnvelopeAlias = Envelope;
pub unsafe fn write(value: *mut Leaf) { *(*value).pointer = 7; }
pub unsafe fn read_input(value: *const Input) -> i32 { *(*value).pointer }
pub unsafe fn read_output(value: *const Output) -> i32 { *(*value).pointer }
"#;
    let unprotected = generate(definitions);
    for name in [
        "EnumLeaf",
        "ArrayLeaf",
        "TupleLeaf",
        "GenericLeaf",
        "Input",
        "Output",
    ] {
        let record = type_record(&unprotected, name);
        assert_ne!(record.source_definition, record.target_definition, "{name}");
    }
    for declaration in [
        "fn consume(value: *const EnvelopeAlias);",
        "fn produce() -> *mut EnvelopeAlias;",
    ] {
        let source = format!("{definitions}\nextern \"C\" {{ {declaration} }}");
        let frozen = run_compiler_on_str(&source, |tcx| {
            let records = make_skeletons(&source, tcx).unwrap();
            for record in &records {
                if let ItemRecord::Type(record) = record {
                    assert_eq!(
                        record.source_definition, record.target_definition,
                        "{}: {declaration}",
                        record.path
                    );
                }
            }
            crate::freeze_project(&source, &records, tcx).unwrap()
        })
        .unwrap();
        run_compiler_on_str(&frozen.target_source, utils::type_check).expect(&frozen.target_source);
    }
}

#[test]
fn foreign_type_identity_overrides_api_promotion_without_freezing_unrelated_structs() {
    let source = r#"
pub mod system { #[repr(C)] #[derive(Clone, Copy)] pub struct Holder { pub pointer: *mut i32 } }
pub mod local { #[repr(C)] #[derive(Clone, Copy)] pub struct Holder { pub pointer: *mut i32 } }
extern "C" { fn unused(value: *const system::Holder); }
pub unsafe fn api(system: *mut system::Holder, local: *mut local::Holder) {
    *(*system).pointer = 1;
    *(*local).pointer = 2;
}
"#;
    let frozen = run_compiler_on_str(source, |tcx| {
        let records =
            make_skeletons_with_api(source, None, &FxHashSet::from_iter(["api".to_owned()]), tcx)
                .unwrap();
        let system = type_record(&records, "system::Holder");
        assert_eq!(system.source_definition, system.target_definition);
        let local = type_record(&records, "local::Holder");
        assert_ne!(local.source_definition, local.target_definition);
        assert!(
            !local.target_definition.contains("Copy"),
            "{}",
            local.target_definition
        );
        crate::freeze_project(source, &records, tcx).unwrap()
    })
    .unwrap();
    run_compiler_on_str(&frozen.target_source, utils::type_check).expect(&frozen.target_source);
}

#[test]
fn api_exposed_thin_fields_preserve_layout_and_support_transformed_bodies() {
    let source = r#"
extern "C" { fn malloc(size: usize) -> *mut i32; fn free(pointer: *mut i32); }
#[repr(C)] pub struct Data { pub tag: u8, pub pointer: *const i32, pub mutable: *mut i32, pub optional: *const i32, pub optional_mutable: *mut i32, pub owned: *mut i32, pub optional_owned: *mut i32 }
pub unsafe fn make(pointer: *const i32, mutable: *mut i32, optional: *const i32, optional_mutable: *mut i32) -> Data {
    Data { tag: 1, pointer, mutable, optional, optional_mutable, owned: malloc(core::mem::size_of::<i32>()), optional_owned: malloc(core::mem::size_of::<i32>()) }
}
pub unsafe fn read(value: *mut Data) -> i32 {
    *(*value).mutable = 3;
    if !(*value).optional_mutable.is_null() { *(*value).optional_mutable = 5; }
    let extra = if (*value).optional.is_null() { 0 } else { *(*value).optional };
    *(*value).pointer + extra
}
pub unsafe fn release(value: Data) { free(value.owned); if !value.optional_owned.is_null() { free(value.optional_owned); } }
"#;
    let layout = |tcx: ty::TyCtxt<'_>| {
        let did = local_def("Data", tcx);
        let layout = tcx
            .layout_of(
                ty::TypingEnv::post_analysis(tcx, did)
                    .as_query_input(tcx.type_of(did).instantiate_identity()),
            )
            .unwrap();
        (
            layout.size.bytes(),
            layout.align.abi.bytes(),
            (0..7)
                .map(|index| layout.fields.offset(index).bytes())
                .collect::<Vec<_>>(),
        )
    };
    let (records, original_layout) = run_compiler_on_str(source, |tcx| {
        (
            make_skeletons_with_api(
                source,
                None,
                &FxHashSet::from_iter(["make".to_owned()]),
                tcx,
            )
            .unwrap(),
            layout(tcx),
        )
    })
    .unwrap();
    let definition = &type_record(&records, "Data").target_definition;
    for expected in [
        "pointer: &'",
        "mut i32",
        "optional: Option<&'",
        "optional_mutable: Option<&'",
        "owned: Box<i32>",
        "optional_owned: Option<Box<i32>>",
    ] {
        assert!(definition.contains(expected), "{definition}");
    }
    assert!(!definition.contains("*const"), "{definition}");
    assert!(!definition.contains("*mut"), "{definition}");
    let target = format!(
        "{definition}\n{} {{ Data {{ tag: 1, pointer, mutable, optional, optional_mutable, owned: Box::new(0), optional_owned: Some(Box::new(0)) }} }}\n{} {{ *value.mutable = 3; if let Some(pointer) = value.optional_mutable.as_deref_mut() {{ *pointer = 5; }} *value.pointer + value.optional.map_or(0, |pointer| *pointer) }}\n{} {{ drop(value.owned); drop(value.optional_owned); }}",
        function(&records, "make").target_signature,
        function(&records, "read").target_signature,
        function(&records, "release").target_signature,
    );
    run_compiler_on_str(&target, |tcx| {
        utils::type_check(tcx);
        assert_eq!(original_layout, layout(tcx));
    })
    .expect(&target);
}

#[test]
fn api_exposure_blocks_array_layers_without_blocking_nested_thin_layers() {
    for (body, expected) in [
        ("**(*value).pointer", "&&"),
        ("*(*(*value).pointer).offset(1)", "&*"),
        ("**(*value).pointer.offset(1)", "*&"),
    ] {
        let source = format!(
            "#[repr(C)] pub struct Holder {{ pub pointer: *const *const i32 }} pub unsafe fn api(value: *const Holder) -> i32 {{ {body} }}"
        );
        let (records, frozen) = run_compiler_on_str(&source, |tcx| {
            let records = make_skeletons_with_api(
                &source,
                None,
                &FxHashSet::from_iter(["api".to_owned()]),
                tcx,
            )
            .unwrap();
            let frozen = crate::freeze_project(&source, &records, tcx).unwrap();
            (records, frozen)
        })
        .unwrap();
        let definition = &type_record(&records, "Holder").target_definition;
        run_compiler_on_str(definition, |_| {
            let parsed = utils::ast::parse_crate(definition.clone());
            let ItemKind::Struct(_, _, fields) = &parsed.items[0].kind else { unreachable!() };
            assert_eq!(
                indirections(&fields.fields()[0].ty),
                expected,
                "{definition}"
            );
        })
        .unwrap();
        assert!(!definition.contains("[i32]"), "{definition}");
        run_compiler_on_str(&frozen.target_source, utils::type_check).expect(&frozen.target_source);
    }
}

#[test]
fn api_exposure_preserves_optional_and_owned_array_fields() {
    let source = r#"
extern "C" { fn malloc(size: usize) -> *mut i32; fn free(pointer: *mut i32); }
#[repr(C)] pub struct Data { pub optional: *const i32, pub owned: *mut i32, pub optional_owned: *mut i32 }
pub unsafe fn make() -> Data { Data { optional: core::ptr::null(), owned: malloc(4 * core::mem::size_of::<i32>()), optional_owned: malloc(4 * core::mem::size_of::<i32>()) } }
pub unsafe fn read(value: *const Data) -> i32 { if (*value).optional.is_null() { 0 } else { *(*value).optional.offset(1) } }
pub unsafe fn release(value: Data) { free(value.owned); if !value.optional_owned.is_null() { free(value.optional_owned); } }
"#;
    let records = run_compiler_on_str(source, |tcx| {
        make_skeletons_with_api(
            source,
            None,
            &FxHashSet::from_iter(["make".to_owned()]),
            tcx,
        )
        .unwrap()
    })
    .unwrap();
    let data = type_record(&records, "Data");
    assert_eq!(data.source_definition, data.target_definition);
    let unprotected = generate(source);
    let target = &type_record(&unprotected, "Data").target_definition;
    assert!(target.contains("Option<&'"), "{target}");
    assert!(target.contains("[i32]"), "{target}");
    assert!(target.contains("Box<[i32]>"), "{target}");
    assert!(target.contains("Option<Box<[i32]>>"), "{target}");
}

#[test]
fn api_exposure_preserves_layout_of_enums_and_rust_struct_containers() {
    for container in [
        "pub enum Container { Value(Inner), Empty }",
        "pub type Container = Option<Inner>;",
        "pub struct Container { pub value: usize, pub inner: Inner }",
    ] {
        let source = format!(
            "#[repr(C)] pub struct Inner {{ pub pointer: *const i32 }} {container} pub unsafe fn api(value: *const Container) {{ let _ = value; }} pub unsafe fn read(value: *const Inner) -> i32 {{ *(*value).pointer }}"
        );
        let records = run_compiler_on_str(&source, |tcx| {
            make_skeletons_with_api(
                &source,
                None,
                &FxHashSet::from_iter(["api".to_owned()]),
                tcx,
            )
            .unwrap()
        })
        .unwrap();
        let inner = type_record(&records, "Inner");
        assert_eq!(
            inner.source_definition, inner.target_definition,
            "{container}"
        );
        assert!(
            type_record(&generate(&source), "Inner")
                .target_definition
                .contains("pointer: &'")
        );
    }
}

#[test]
fn pointer_arrays_and_union_fields_remain_raw() {
    let source = r#"
#[derive(Clone, Copy)] pub struct Holder { pub pointer: *mut i32 }
pub union Storage { pub holder: Holder, pub bits: usize }
pub struct Array { pub pointers: [*const i32; 2] }
pub unsafe fn write(holder: *mut Holder) { *(*holder).pointer = 7; }
pub unsafe fn read(array: *const Array) -> i32 { *(*array).pointers[0] }
pub unsafe fn local(pointer: *const i32) -> i32 { let values: [*const i32; 1] = [pointer]; *values[0] }
"#;
    let records = generate(source);
    for name in ["Holder", "Storage", "Array"] {
        let record = type_record(&records, name);
        assert_eq!(record.source_definition, record.target_definition, "{name}");
    }
    assert!(
        function(&records, "local")
            .baseline
            .skeleton
            .contains("[*const i32; 1]")
    );
}

#[test]
fn field_lifetimes_follow_aggregate_values_and_nested_field_returns() {
    let source = r#"
pub struct Holder { pub pointer: *const *const i32 }
pub struct Container { pub holder: Holder }
pub enum Choice { Value(Container), Empty }
pub unsafe fn identity(value: Holder) -> Holder { value }
pub unsafe fn forward(value: Holder) -> Holder { identity(value) }
pub unsafe fn container(value: Container) -> Container { value }
pub unsafe fn choice(value: Choice) -> Choice { value }
pub unsafe fn pair(value: (Holder, Holder)) -> (Holder, Holder) { value }
pub unsafe fn get(value: *const Holder) -> *const *const i32 { (*value).pointer }
pub unsafe fn read(value: *const Holder) -> i32 { **(*value).pointer }
"#;
    compile_target_bodies(
        source,
        &[
            ("identity", "value"),
            ("forward", "identity(value)"),
            ("container", "value"),
            ("choice", "value"),
            ("pair", "value"),
            ("get", "value.pointer"),
            ("read", "**value.pointer"),
        ],
    );
}

#[test]
fn pointer_fields_preserve_lifetimes_of_aliases_to_compound_types() {
    let source = r#"
pub struct Holder { pub pointer: *const i32 }
pub type Pair = (Holder, Holder);
pub type Array = [Holder; 2];
pub type Pointer = *const Pair;
pub struct Outer { pub pair: *const Pair, pub array: *const Array, pub pointer: Pointer }
pub unsafe fn read(value: *const Outer) -> bool { (*value).pair.is_null() }
pub unsafe fn read_holder(value: *const Holder) -> i32 { *(*value).pointer }
"#;
    let records = generate(source);
    let target = records
        .iter()
        .map(|record| match record {
            ItemRecord::Type(record) => record.target_definition.clone(),
            ItemRecord::Function(record) => format!("{} {{ todo!() }}", record.target_signature),
            _ => String::new(),
        })
        .collect::<Vec<_>>()
        .join("\n");
    run_compiler_on_str(&target, utils::type_check).expect(&target);
    assert!(
        type_record(&records, "Outer")
            .target_definition
            .contains("Pair<'")
    );
}

#[test]
fn incompatible_comparison_and_debug_derives_are_removed() {
    let source = r#"
#[derive(PartialEq, Eq)] pub struct Float { pub pointer: *const f32 }
pub struct Plain { pub value: i32 }
#[derive(Debug)] pub struct Holder { pub pointer: *const Plain }
#[derive(Debug)] pub enum Container { Value(Holder), Empty }
pub unsafe fn read_float(value: *const Float) -> f32 { *(*value).pointer }
pub unsafe fn read(value: *const Holder) -> i32 { (*(*value).pointer).value }
"#;
    let records = compile_target_bodies(
        source,
        &[
            ("read_float", "*value.pointer"),
            ("read", "value.pointer.value"),
        ],
    );
    let float = &type_record(&records, "Float").target_definition;
    assert!(float.contains("derive(PartialEq)"), "{float}");
    for name in ["Holder", "Container"] {
        assert!(
            !type_record(&records, name)
                .target_definition
                .contains("derive(Debug)")
        );
    }
}

#[test]
fn union_copy_requirements_follow_optional_structs_with_owning_fields() {
    let source = r#"
extern "C" { fn malloc(size: usize) -> *mut i32; fn free(pointer: *mut i32); }
#[derive(Clone, Copy)] pub struct Holder { pub pointer: *mut i32 }
pub union Storage { pub holder: Option<Holder>, pub bits: usize }
pub unsafe fn allocate() -> Holder { Holder { pointer: malloc(core::mem::size_of::<i32>()) } }
pub unsafe fn release(value: Holder) { free(value.pointer); }
"#;
    let records = generate(source);
    let holder = type_record(&records, "Holder");
    assert_eq!(holder.source_definition, holder.target_definition);
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
            Some(PtrKind::Ref(true))
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
fn typed_returns_without_a_lifetime_from_raw_void_parameters_stay_raw() {
    let source = r#"
pub unsafe fn shared(p: *const core::ffi::c_void) -> *const i32 { p as *const i32 }
pub unsafe fn mutable(p: *const core::ffi::c_void) -> *mut i32 { p as *mut i32 }
pub unsafe fn reference_suffix<'a>(p: *const core::ffi::c_void) -> *const &'a i32 { p as *const &'a i32 }
"#;
    let records = compile_target_bodies(
        source,
        &[
            ("shared", "p as *const i32"),
            ("mutable", "p as *mut i32"),
            ("reference_suffix", "p as *const &'a i32"),
        ],
    );
    for (name, expected) in [
        ("shared", "*const i32"),
        ("mutable", "*mut i32"),
        ("reference_suffix", "*const &'a i32"),
    ] {
        let signature = &function(&records, name).target_signature;
        assert!(signature.ends_with(expected), "{signature}");
        if name != "reference_suffix" {
            assert!(!signature.contains('\''), "{signature}");
        }
    }
}

#[test]
fn borrowed_returns_from_globals_and_opaque_calls_stay_raw() {
    let source = r#"
unsafe extern "C" { fn opaque() -> *mut i32; }
static mut VALUES: [i32; 2] = [0, 1];
static mut POINTERS: [*mut i32; 2] = [core::ptr::null_mut(); 2];
pub unsafe fn global(index: usize) -> *mut i32 {
    if index >= 2 { core::ptr::null_mut() } else { VALUES.as_mut_ptr().add(index) }
}
pub unsafe fn lookup(index: usize) -> *mut i32 { POINTERS[index] }
pub unsafe fn foreign() -> *mut i32 {
    let pointer = opaque();
    if pointer.is_null() { core::ptr::null_mut() } else { pointer }
}
pub unsafe fn read() -> i32 { *foreign().add(1) }
"#;
    let frozen = run_compiler_on_str(source, |tcx| {
        let records = make_skeletons(source, tcx).unwrap();
        for name in ["global", "lookup", "foreign"] {
            let record = function(&records, name);
            assert!(
                record.target_signature.ends_with("*mut i32"),
                "{}",
                record.target_signature
            );
            assert!(
                !record.target_signature.contains('\''),
                "{}",
                record.target_signature
            );
        }
        crate::freeze_project(source, &records, tcx).unwrap()
    })
    .unwrap();
    run_compiler_on_str(&frozen.target_source, utils::type_check).expect(&frozen.target_source);
}

#[test]
fn unknown_return_alternatives_prevent_borrowing_from_a_known_input() {
    let source = r#"
unsafe extern "C" { fn opaque() -> *const i32; }
pub unsafe fn mixed(pointer: *const i32, flag: bool) -> *const i32 {
    if flag { pointer } else {
        let other = opaque();
        if other.is_null() { core::ptr::null() } else { other }
    }
}
"#;
    let records = generate(source);
    let signature = &function(&records, "mixed").target_signature;
    assert!(signature.ends_with("*const i32"), "{signature}");
    assert!(
        signature.contains("pointer: Option<&mut i32>"),
        "{signature}"
    );
    assert!(!signature.contains('\''), "{signature}");
    assert_stub_signatures_compile(&records, "");
}

#[test]
fn unusable_input_origins_do_not_hide_behind_a_borrowable_input() {
    let source = r#"
pub unsafe fn cast(pointer: *const core::ffi::c_void) -> *const i32 { pointer as *const i32 }
pub unsafe fn typed(pointer: *const i32) -> *const i32 { cast(pointer as *const core::ffi::c_void) }
pub unsafe fn mixed(pointer: *const i32, raw: *const core::ffi::c_void, flag: bool) -> *const i32 {
    if flag { pointer } else { raw as *const i32 }
}
pub unsafe fn mixed_call(pointer: *const i32, raw: *const core::ffi::c_void, flag: bool) -> *const i32 {
    if flag { pointer } else { cast(raw) }
}
"#;
    let records = generate(source);
    for name in ["cast", "mixed", "mixed_call"] {
        let signature = &function(&records, name).target_signature;
        assert!(signature.ends_with("*const i32"), "{signature}");
        assert!(!signature.contains('\''), "{signature}");
    }
    let typed = &function(&records, "typed").target_signature;
    assert!(typed.contains("-> &'"), "{typed}");
    assert_stub_signatures_compile(&records, "");
}

#[test]
fn nested_return_fallback_retains_the_borrow_with_a_usable_lifetime() {
    let source = r#"
pub unsafe fn cast(pointer: *const *const core::ffi::c_void) -> *const *const i32 {
    pointer as *const *const i32
}
"#;
    run_compiler_on_str(source, |tcx| {
        let decisions = tools_pointer_decisions(tcx);
        let cast = local_def("cast", tcx);
        assert_eq!(
            decisions.signatures.data[&cast].output_dec,
            Some(PtrKind::Ref(false))
        );
        assert_eq!(
            decisions.nested(PointerTarget::Output(cast))[0].kind,
            PtrKind::Raw(false)
        );
        assert_eq!(
            decisions.nested(PointerTarget::Output(cast))[0].lifetime,
            None
        );
        assert!(decisions.bounds[&cast].is_empty());
    })
    .unwrap();
    let records = compile_target_bodies(
        source,
        &[(
            "cast",
            "&*(pointer as *const *const core::ffi::c_void as *const *const i32)",
        )],
    );
    let signature = &function(&records, "cast").target_signature;
    assert!(signature.ends_with("*const i32"), "{signature}");
}

#[test]
fn raw_return_dependencies_propagate_without_changing_unrelated_input_borrows() {
    let source = r#"
pub struct Cell { pub value: *const i32 }
pub struct Holder { pub cell: *const Cell }
unsafe extern "C" { fn unused(value: *const Holder); }
pub unsafe fn nested(value: *const Holder) -> *const i32 { (*(*value).cell).value }
pub unsafe fn identity(pointer: *const i32) -> *const i32 { pointer }
pub unsafe fn mixed(pointer: *const i32, value: *const Holder, flag: bool) -> *const i32 {
    if flag { pointer } else { nested(value) }
}
pub unsafe fn inline(pointer: *const i32, value: *const Holder, flag: bool) -> *const i32 {
    if flag { pointer } else { (*(*value).cell).value }
}
pub unsafe fn reborrow(pointer: *const i32, value: *const Holder, flag: bool) -> *const i32 {
    if flag { pointer } else { &*nested(value) as *const i32 }
}
pub unsafe fn offset(pointer: *const i32, value: *const Holder, flag: bool) -> *const i32 {
    if flag { pointer } else { nested(value).offset(1) }
}
pub unsafe fn forward(pointer: *const i32, value: *const Holder, flag: bool) -> *const i32 {
    if flag { pointer } else { identity(mixed(pointer, value, flag)) }
}
pub unsafe fn recursive(pointer: *const i32, value: *const Holder, count: i32) -> *const i32 {
    if count == 0 { nested(value) } else { recursive(pointer, value, count - 1) }
}
"#;
    let frozen = run_compiler_on_str(source, |tcx| {
        let records = make_skeletons(source, tcx).unwrap();
        for name in [
            "nested",
            "mixed",
            "inline",
            "reborrow",
            "offset",
            "forward",
            "recursive",
        ] {
            let signature = &function(&records, name).target_signature;
            assert!(signature.ends_with("*const i32"), "{signature}");
            assert!(!signature.contains('\''), "{signature}");
        }
        let identity = &function(&records, "identity").target_signature;
        assert!(identity.contains("-> &'"), "{identity}");
        crate::freeze_project(source, &records, tcx).unwrap()
    })
    .unwrap();
    run_compiler_on_str(&frozen.target_source, utils::type_check).expect(&frozen.target_source);
}

#[test]
fn owning_return_layers_survive_fallback_of_a_borrowed_inner_layer() {
    let source = r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn opaque() -> *mut i32;
}
pub unsafe fn borrowed(pointer: *const i32) -> *mut *const i32 {
    let cell = malloc(core::mem::size_of::<*const i32>()) as *mut *const i32;
    *cell = pointer;
    cell
}
pub unsafe fn unknown() -> *mut *mut i32 {
    let cell = malloc(core::mem::size_of::<*mut i32>()) as *mut *mut i32;
    let pointer = opaque();
    *cell = if pointer.is_null() { core::ptr::null_mut() } else { pointer };
    cell
}
"#;
    let records = generate(source);
    let borrowed = &function(&records, "borrowed").target_signature;
    assert!(borrowed.contains("Box<&'"), "{borrowed}");
    let unknown = &function(&records, "unknown").target_signature;
    assert!(unknown.ends_with("Box<*mut i32>"), "{unknown}");
    assert!(!unknown.contains('\''), "{unknown}");
    assert_stub_signatures_compile(&records, "");
}

#[test]
fn nullable_owning_returns_do_not_require_borrow_origins() {
    for (size, expected) in [
        ("core::mem::size_of::<i32>()", "Option<Box<i32>>"),
        ("4 * core::mem::size_of::<i32>()", "Option<Box<[i32]>>"),
    ] {
        let source = format!(
            "unsafe extern \"C\" {{ fn malloc(size: usize) -> *mut core::ffi::c_void; }} pub unsafe fn allocate() -> *mut i32 {{ let pointer = malloc({size}) as *mut i32; if pointer.is_null() {{ core::ptr::null_mut() }} else {{ *pointer = 7; pointer }} }}"
        );
        let records = generate(&source);
        let signature = &function(&records, "allocate").target_signature;
        assert!(signature.ends_with(expected), "{signature}");
        assert_stub_signatures_compile(&records, "");
    }
}

#[test]
fn allocation_extent_survives_preserved_struct_field_initializers() {
    let source = "unsafe extern \"C\" { fn malloc(size: usize) -> *mut i32; } pub struct Holder { p: *mut i32 } pub unsafe fn allocate() -> *mut i32 { let holder = Holder { p: malloc(4 * core::mem::size_of::<i32>()) }; let p = holder.p; *p = 7; p }";
    let records = generate(source);
    let signature = &function(&records, "allocate").target_signature;
    assert!(signature.ends_with("Box<[i32]>"), "{signature}");
    assert!(
        type_record(&records, "Holder")
            .source_definition
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

#[test]
fn mutable_field_getters_reborrow_for_the_container_lifetime() {
    let source = r#"
pub struct Holder { pub pointer: *mut i32 }
pub unsafe fn get(holder: *mut Holder) -> *mut i32 { (*holder).pointer }
pub unsafe fn write(holder: *mut Holder) { *get(holder) = 7; }
pub unsafe fn read(holder: *const Holder) -> i32 { *(*holder).pointer }
"#;
    compile_target_bodies(
        source,
        &[
            ("get", "&mut *holder.pointer"),
            ("write", "*get(holder) = 7;"),
            ("read", "*holder.pointer"),
        ],
    );
    let source = r#"
pub struct Holder { pub pointer: *mut *mut i32 }
pub unsafe fn make(pointer: *mut *mut i32) -> Holder { Holder { pointer } }
pub unsafe fn get(holder: *mut Holder) -> *mut *mut i32 { (*holder).pointer }
pub unsafe fn write(holder: *mut Holder) { **get(holder) = 7; }
"#;
    compile_target_bodies(
        source,
        &[
            ("make", "Holder { pointer }"),
            ("get", "&mut *holder.pointer"),
            ("write", "**get(holder) = 7;"),
        ],
    );
}

#[test]
fn compatible_default_and_marker_derives_are_preserved() {
    let source = r#"
pub struct Plain { pub value: i32 }
#[derive(Clone, Copy)] pub struct Unchanged { pub marker: core::marker::PhantomData<Plain> }
#[derive(Default)] pub enum UnchangedChoice { #[default] Empty, Value(Plain) }
pub struct Holder { pub pointer: *mut i32 }
#[derive(Clone, Copy, Debug, Default)] pub struct Marker { pub marker: core::marker::PhantomData<Holder> }
#[derive(Default)] pub enum Choice { #[default] Empty, Value(Holder) }
pub unsafe fn write(holder: *mut Holder) { *(*holder).pointer = 7; }
"#;
    let records = compile_target_bodies(source, &[("write", "*holder.pointer = 7;")]);
    for name in ["Unchanged", "UnchangedChoice"] {
        let record = type_record(&records, name);
        assert_eq!(record.source_definition, record.target_definition);
    }
    assert!(
        type_record(&records, "Marker")
            .target_definition
            .contains("derive(Clone, Copy, Debug, Default)")
    );
    assert!(
        type_record(&records, "Choice")
            .target_definition
            .contains("derive(Default)")
    );
}

#[test]
fn existing_nominal_lifetimes_remain_distinct_and_keep_argument_order() {
    let source = r#"
pub struct Holder<'a> { pub original: &'a i32, pub pointer: *const i32 }
pub unsafe fn identity<'a>(value: Holder<'a>) -> Holder<'a> { value }
pub unsafe fn read(value: *const Holder<'static>) -> i32 { *(*value).pointer }
"#;
    let records =
        compile_target_bodies(source, &[("identity", "value"), ("read", "*value.pointer")]);
    let holder = &type_record(&records, "Holder").target_definition;
    assert!(holder.contains("Holder<'b, 'a>"), "{holder}");
}

#[test]
fn zeroable_derives_follow_the_selected_reference_form() {
    let source = r#"
#[derive(bytemuck::Zeroable)] pub struct Holder { pub pointer: *const i32 }
#[derive(bytemuck::Zeroable)] pub struct Nullable { pub pointer: *const i32 }
pub unsafe fn read(value: *const Holder) -> i32 { *(*value).pointer }
pub unsafe fn optional(value: *const Nullable) -> i32 { if (*value).pointer.is_null() { 0 } else { *(*value).pointer } }
"#;
    let records = compile_target_bodies(
        source,
        &[
            ("read", "*value.pointer"),
            ("optional", "value.pointer.map_or(0, |pointer| *pointer)"),
        ],
    );
    assert!(
        !type_record(&records, "Holder")
            .target_definition
            .contains("Zeroable")
    );
    assert!(
        type_record(&records, "Nullable")
            .target_definition
            .contains("Zeroable")
    );
}

#[test]
fn copy_union_manually_drop_fields_retain_raw_owners() {
    let source = r#"
extern "C" { fn malloc(size: usize) -> *mut i32; fn free(pointer: *mut i32); }
#[derive(Clone, Copy)] pub struct Holder { pub pointer: *mut i32 }
#[derive(Clone, Copy)] pub union Storage { pub holder: core::mem::ManuallyDrop<Holder>, pub bits: usize }
pub unsafe fn allocate() -> Holder { Holder { pointer: malloc(core::mem::size_of::<i32>()) } }
pub unsafe fn release(value: Holder) { free(value.pointer); }
"#;
    let records = generate(source);
    let record = type_record(&records, "Holder");
    assert_eq!(record.source_definition, record.target_definition);
}

#[test]
fn struct_field_representations_include_optional_slice_and_owned_forms() {
    let source = r#"
extern "C" { fn malloc(size: usize) -> *mut i32; fn free(pointer: *mut i32); }
pub struct Data { pub pointer: *const i32, pub optional: *const i32, pub bytes: *const u8, pub optional_bytes: *const u8, pub owned: *mut i32, pub owned_array: *mut i32 }
pub unsafe fn make(pointer: *const i32, optional: *const i32, bytes: *const u8, optional_bytes: *const u8) -> Data {
    Data { pointer, optional, bytes, optional_bytes, owned: malloc(core::mem::size_of::<i32>()), owned_array: malloc(4 * core::mem::size_of::<i32>()) }
}
pub unsafe fn read(value: *const Data) -> i32 { let number = if (*value).optional.is_null() { 0 } else { *(*value).optional }; let byte = if (*value).optional_bytes.is_null() { 0 } else { *(*value).optional_bytes.offset(1) as i32 }; number + byte + *(*value).pointer + *(*value).bytes.offset(1) as i32 }
pub unsafe fn release(value: Data) { free(value.owned); free(value.owned_array); }
"#;
    let records = generate(source);
    let target = &type_record(&records, "Data").target_definition;
    assert!(target.contains("Option<&'"), "{target}");
    assert!(target.contains("[u8]"), "{target}");
    assert!(target.contains("Box<i32>"), "{target}");
    assert!(target.contains("Box<[i32]>"), "{target}");
    assert_stub_signatures_compile(&records, target);
}

#[test]
fn owned_fields_support_allocation_reads_and_release() {
    let source = r#"
extern "C" { fn malloc(size: usize) -> *mut i32; fn free(pointer: *mut i32); }
pub struct Holder { pub pointer: *mut i32 }
pub unsafe fn allocate() -> Holder { let pointer = malloc(core::mem::size_of::<i32>()); *pointer = 7; Holder { pointer } }
pub unsafe fn get(holder: *const Holder) -> i32 { *(*holder).pointer }
pub unsafe fn release(holder: Holder) { free(holder.pointer); }
"#;
    let records = compile_target_bodies(
        source,
        &[
            ("allocate", "Holder { pointer: Box::new(7) }"),
            ("get", "*holder.pointer"),
            ("release", "drop(holder.pointer);"),
        ],
    );
    assert!(
        type_record(&records, "Holder")
            .target_definition
            .contains("Box<i32>")
    );
}

#[test]
fn readonly_aliases_of_mutable_field_containers_keep_shared_views() {
    let source = r#"
pub struct Holder { pub pointer: *mut i32 }
pub unsafe fn write(holder: *mut Holder) { *(*holder).pointer = 7; }
pub unsafe fn read(left: *mut Holder, right: *mut Holder) -> i32 { *(*left).pointer + *(*right).pointer }
pub unsafe fn repeated(holder: *mut Holder) -> i32 { read(holder, holder) }
"#;
    compile_target_bodies(
        source,
        &[
            ("write", "*holder.pointer = 7;"),
            ("read", "*left.pointer + *right.pointer"),
            ("repeated", "read(holder, holder)"),
        ],
    );
}
