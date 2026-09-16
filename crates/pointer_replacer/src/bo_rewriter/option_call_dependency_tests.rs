//! Wave-6o (relay 015 / R415-6): an optional argument matched to an optional
//! formal is zero-syntax at the seam, but the caller's declaration only types
//! against the CONVERTED formal — if the callee's class is held (its formal
//! stays raw) the caller must be `dependency-class-held` by it, from the Core
//! stage on, not first at the Option stage's call receipts.
use rustc_span::def_id::LocalDefId;

use super::{bridge_receipt::SignatureClassId, emit_tests::ast_emitted_source_of, verify};

/// wave-5d's `accessors-null-tested-fixture.rs` (relay 020): `GetValue` is
/// held by the retention hold on `p`; `get_value` passes its optional `value`
/// to `GetValue`'s optional formal.
const ACCESSORS: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case, unused_variables)]
#[repr(C)]
pub struct binn { pub header: i32, pub type_0: i32, pub size: i32, pub ptr: *mut core::ffi::c_void }
unsafe fn GetValue(mut p: *mut u8, mut value: *mut binn) -> i32 {
    if value.is_null() { return 0 as i32; }
    (*value).type_0 = *p as i32;
    (*value).ptr = p as *mut core::ffi::c_void;
    return 1 as i32;
}
pub unsafe fn get_value(mut ptr: *mut core::ffi::c_void, mut pos: i32, mut value: *mut binn) -> i32 {
    if ptr.is_null() || value.is_null() { return 0 as i32; }
    let mut p = ptr as *mut u8;
    return GetValue(p, value);
}
unsafe fn copy_raw_value(mut psource: *mut core::ffi::c_void, mut pdest: *mut core::ffi::c_void, mut data_store: i32) -> i32 {
    match data_store {
        96 => { *(pdest as *mut i32) = *(psource as *mut i32); }
        160 => { *(pdest as *mut *mut i8) = psource as *mut i8; }
        _ => return 0 as i32,
    }
    return 1 as i32;
}
unsafe fn copy_value(mut psource: *mut core::ffi::c_void, mut pdest: *mut core::ffi::c_void, mut data_store: i32) -> i32 {
    return copy_raw_value(psource, pdest, data_store);
}
pub unsafe fn binn_list_get(mut ptr: *mut core::ffi::c_void, mut pos: i32, mut type_0: i32, mut pvalue: *mut core::ffi::c_void) -> i32 {
    let mut value = binn { header: 0, type_0: 0, size: 0, ptr: 0 as *mut core::ffi::c_void };
    if get_value(ptr, pos, &mut value) == 0 as i32 { return 0 as i32; }
    if copy_value(value.ptr, pvalue, type_0) == 0 as i32 { return 0 as i32; }
    return 1 as i32;
}
pub unsafe fn binn_list_int32(mut list: *mut core::ffi::c_void, mut pos: i32) -> i32 {
    let mut value: i32 = 0;
    binn_list_get(list, pos, 96 as i32, &mut value as *mut i32 as *mut core::ffi::c_void);
    return value;
}
pub unsafe fn binn_list_str(mut list: *mut core::ffi::c_void, mut pos: i32) -> *mut i8 {
    let mut value: *mut i8 = 0 as *mut i8;
    binn_list_get(list, pos, 160 as i32, &mut value as *mut *mut i8 as *mut core::ffi::c_void);
    return value;
}
"#;

/// A reference argument at a reference formal needs no such edge: `&mut T`
/// coerces to `*mut T` at the call whether or not the callee converts.
const REFERENCE_ONLY: &str = r#"
#![allow(dead_code, unused_mut)]
unsafe fn store(mut p: *mut i32) { *p = 1 as i32; }
pub unsafe fn caller(mut p: *mut i32) { *p = 0 as i32; store(p); }
"#;

fn function(tcx: rustc_middle::ty::TyCtxt<'_>, name: &str) -> LocalDefId {
    tcx.hir_body_owners()
        .find(|owner| tcx.item_name(owner.to_def_id()).as_str() == name)
        .unwrap_or_else(|| panic!("fixture function {name}"))
}

/// (caller, callee) interface dependencies recorded by the seam layer, and the
/// caller class's finalized `depends_on`.
fn dependency_edges(
    input: &str,
    caller: &str,
    callee: &str,
) -> (bool, bool, Vec<SignatureClassId>) {
    assert!(verify::type_checks_str(input));
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (table, ctx) = super::decide_table_with_ctx(tcx).expect("native decisions");
        let caller = SignatureClassId::of(function(tcx, caller));
        let callee = SignatureClassId::of(function(tcx, callee));
        let emission = super::emit_files(
            tcx,
            &table,
            &rustc_hash::FxHashSet::default(),
            &ctx.retained_c9_plans,
        )
        .expect("emission plan");
        let depends_on = emission
            .plan
            .class_finalization
            .classes
            .get(&caller)
            .map(|class| class.depends_on.clone())
            .unwrap_or_default();
        (
            table
                .seams
                .interface_dependencies
                .contains(&(caller, callee)),
            depends_on.contains(&callee),
            depends_on,
        )
    })
    .expect("fixture compiler context")
}

#[test]
fn wave6o_optional_argument_at_optional_formal_depends_on_the_callee_class() {
    let (edge, depends, depends_on) = dependency_edges(ACCESSORS, "get_value", "GetValue");
    assert!(
        edge,
        "the seam must record get_value -> GetValue for the optional `value` at the optional formal"
    );
    assert!(
        depends,
        "get_value's class must depend on GetValue's from the Core stage: {depends_on:?}"
    );
    let output = ast_emitted_source_of(ACCESSORS).expect("native emission");
    eprintln!("WAVE6O_CALLDEP_OUTPUT_BEGIN\n{output}\nWAVE6O_CALLDEP_OUTPUT_END");
    assert!(verify::type_checks_str(&output), "{output}");
}

#[test]
fn wave6o_reference_argument_at_reference_formal_records_no_dependency() {
    let (edge, depends, depends_on) = dependency_edges(REFERENCE_ONLY, "caller", "store");
    assert!(
        !edge && !depends,
        "a coercing reference needs no edge: {depends_on:?}"
    );
}
