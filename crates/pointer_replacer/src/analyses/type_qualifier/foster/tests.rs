use super::{fatness::fatness_analysis, mutability::mutability_analysis};

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
