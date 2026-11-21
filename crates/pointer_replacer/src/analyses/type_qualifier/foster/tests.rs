use super::{fatness::fatness_analysis, mutability::mutability_analysis};

#[test]
fn generic_calls_with_different_pointer_shapes_constrain_inputs_and_results() {
    utils::compilation::run_compiler_on_str(
        r#"
pub fn pass<T>(value: T) -> T { value }
pub fn returned(value: *mut i32) -> *mut i32 { pass(value) }
pub unsafe fn accept<T>(pointer: *mut i32, value: T) { *pointer = 1; }
pub unsafe fn arguments(left: *mut i32, right: *mut i32) { accept(left, right); }
"#,
        |tcx| {
            let program = crate::rewriter::collect_input(tcx);
            let mutable = mutability_analysis(&program);
            let fatness = fatness_analysis(&program);
            for &function in &program.functions {
                let name = tcx.item_name(function.to_def_id());
                if !matches!(name.as_str(), "returned" | "arguments") {
                    continue;
                }
                for facts in mutable.function_facts(function, tcx) {
                    assert!(facts.iter().all(|value| value.is_mutable()), "{name}");
                }
                for facts in fatness.function_facts(function, tcx) {
                    assert!(facts.iter().all(|value| value.is_arr()), "{name}");
                }
            }
        },
    )
    .unwrap();
}

#[test]
fn slice_rest_patterns_keep_mutability_and_array_requirements() {
    utils::compilation::run_compiler_on_str(
        r#"
pub unsafe fn tail(values: &mut [*mut i32], offset: isize) {
    if let [_, rest @ ..] = values { *rest[0].offset(offset) = 1; }
}
pub unsafe fn head(values: &mut [*mut i32; 3], offset: isize) {
    let [ref mut rest @ .., _] = *values;
    *rest[0].offset(offset) = 1;
}
"#,
        |tcx| {
            let program = crate::rewriter::collect_input(tcx);
            let mutable = mutability_analysis(&program);
            let fatness = fatness_analysis(&program);
            for &function in &program.functions {
                assert!(mutable.function_facts(function, tcx).nth(1).unwrap()[1].is_mutable());
                assert!(fatness.function_facts(function, tcx).nth(1).unwrap()[1].is_arr());
            }
        },
    )
    .unwrap();
}

#[test]
fn constant_index_patterns_preserve_pointer_qualifiers() {
    use rustc_middle::mir::{ProjectionElem, Rvalue, StatementKind};

    let source = r#"
pub unsafe fn prefix(values: &mut [*mut i32; 2], offset: isize) {
    let [first, _] = *values;
    *first.offset(offset) = 1;
}
pub unsafe fn suffix(values: &mut [*mut i32], offset: isize) {
    if let [.., last] = *values { *last.offset(offset) = 1; }
}
pub unsafe fn dynamic(values: &mut [*mut i32], index: usize, offset: isize) {
    *values[index].offset(offset) = 1;
}
pub struct Entry { pointer: *mut i32 }
pub unsafe fn nested(values: &mut [[Entry; 2]; 2], offset: isize) {
    let [_, [_, Entry { pointer }]] = *values;
    *pointer.offset(offset) = 1;
}
"#;
    utils::compilation::run_compiler_on_str(source, |tcx| {
        let program = crate::rewriter::collect_input(tcx);
        let mutable = mutability_analysis(&program);
        let fatness = fatness_analysis(&program);
        let mut start = false;
        let mut end = false;
        let mut nested = false;
        for &function in &program.functions {
            let body = tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            for statement in body.basic_blocks.iter().flat_map(|block| &block.statements) {
                let StatementKind::Assign(box (_, Rvalue::Use(operand))) = &statement.kind else {
                    continue;
                };
                let Some(place) = operand.place() else { continue };
                let mut indices = 0;
                for element in place.projection {
                    if let ProjectionElem::ConstantIndex { from_end, .. } = element {
                        start |= !from_end;
                        end |= from_end;
                        indices += 1;
                    }
                }
                nested |= indices == 2;
            }
            if tcx.item_name(function.to_def_id()).as_str() != "nested" {
                let pointer_shape = fatness.function_facts(function, tcx).nth(1).unwrap();
                assert_eq!(pointer_shape.len(), 2);
                assert!(pointer_shape[0].is_ptr());
                assert!(pointer_shape[1].is_arr());
                assert!(mutable.function_facts(function, tcx).nth(1).unwrap()[1].is_mutable());
            }
        }
        assert!(
            start && end && nested,
            "fixtures must exercise real constant-index projections"
        );
        let entry = program.structs[0];
        assert!(fatness.struct_field_fact(entry, 0, 0).unwrap().is_arr());
        assert!(mutable.struct_field_fact(entry, 0, 0).unwrap().is_mutable());
    })
    .unwrap();
}

#[test]
fn memchr_tracks_buffer_shape_and_read_or_write_uses_through_void_casts() {
    use crate::analyses::mir::{CallKind, TerminatorExt};

    let source = r#"
use core::ffi::c_void;
unsafe extern "C" {
    fn memchr(p: *const c_void, c: i32, n: usize) -> *mut c_void;
    #[link_name = "memchr"] fn renamed(p: *const c_void, c: i32, n: usize) -> *mut c_void;
    #[link_name = "opaque"] fn hidden(p: *const c_void, c: i32, n: usize) -> *mut c_void;
}
pub unsafe fn read(p: *mut u8, n: usize) -> *mut u8 { memchr(p as *const c_void, 7, n) as *mut u8 }
pub unsafe fn alias(p: *mut u8, n: usize) -> *mut u8 { renamed(p as *const c_void, 7, n) as *mut u8 }
pub unsafe fn external(p: *mut u8, n: usize) -> *mut u8 { libc::memchr(p as *const c_void, 7, n) as *mut u8 }
pub unsafe fn write(p: *mut u8, n: usize) -> *mut u8 {
    let result = memchr(p as *const c_void, 7, n) as *mut u8;
    if !result.is_null() { *result = 8; }
    result
}
pub unsafe fn unknown(p: *mut u8, n: usize) -> *mut u8 { hidden(p as *const c_void, 7, n) as *mut u8 }
"#;
    utils::compilation::run_compiler_on_str(source, |tcx| {
        let program = crate::rewriter::collect_input(tcx);
        let mutability = mutability_analysis(&program);
        let fatness = fatness_analysis(&program);
        for &function in &program.functions {
            let name = tcx.item_name(function.to_def_id());
            let input_mutable =
                mutability.function_facts(function, tcx).nth(1).unwrap()[0].is_mutable();
            let output_mutable =
                mutability.function_facts(function, tcx).next().unwrap()[0].is_mutable();
            if name.as_str() == "unknown" {
                assert!(input_mutable);
                assert!(fatness.function_facts(function, tcx).nth(1).unwrap()[0].is_ptr());
            } else {
                assert_eq!(input_mutable, name.as_str() == "write", "{name}");
                assert!(!output_mutable, "{name}");
                assert!(
                    fatness.function_facts(function, tcx).nth(1).unwrap()[0].is_arr(),
                    "{name}"
                );
                let body = tcx
                    .mir_drops_elaborated_and_const_checked(function)
                    .borrow();
                let destination = body
                    .basic_blocks
                    .iter()
                    .find_map(|block| {
                        let call = block.terminator().as_call(tcx)?;
                        matches!(call.func, CallKind::LibC(symbol) if symbol.as_str() == "memchr")
                            .then_some(call.destination.local)
                    })
                    .unwrap();
                assert!(
                    fatness
                        .function_body_fact(function, destination.index(), 0)
                        .unwrap()
                        .is_arr(),
                    "{name}"
                );
                assert_eq!(
                    mutability
                        .function_body_fact(function, destination.index(), 0)
                        .unwrap()
                        .is_mutable(),
                    name.as_str() == "write",
                    "{name}"
                );
            }
        }
    })
    .unwrap();
}

#[test]
fn boxed_pointer_projections_propagate_nested_qualifiers() {
    let source = r#"
pub unsafe fn boxed(value: Box<*mut i32>, index: isize) {
    *(*value).offset(index) = 1;
}
pub unsafe fn nested(value: Box<Box<*mut i32>>, index: isize) {
    *(**value).offset(index) = 1;
}
pub unsafe fn nonnull(value: std::ptr::NonNull<*mut i32>, index: isize) {
    let raw: *const *mut i32 = std::mem::transmute(value);
    *(*raw).offset(index) = 1;
}
"#;
    utils::compilation::run_compiler_on_str(source, |tcx| {
        let program = crate::rewriter::collect_input(tcx);
        let mutability = mutability_analysis(&program);
        let fatness = fatness_analysis(&program);
        for &function in &program.functions {
            let mutable = mutability.function_facts(function, tcx).nth(1).unwrap();
            let array = fatness.function_facts(function, tcx).nth(1).unwrap();
            let layers = if tcx.item_name(function.to_def_id()).as_str() == "nested" {
                3
            } else {
                2
            };
            assert_eq!(mutable.len(), layers);
            assert_eq!(array.len(), layers);
            assert!(mutable.last().unwrap().is_mutable());
            assert!(array.last().unwrap().is_arr());
            assert!(array[..layers - 1].iter().all(|value| value.is_ptr()));
        }
    })
    .unwrap();
}
