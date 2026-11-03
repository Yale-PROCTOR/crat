use super::{fatness::fatness_analysis, mutability::mutability_analysis};

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
