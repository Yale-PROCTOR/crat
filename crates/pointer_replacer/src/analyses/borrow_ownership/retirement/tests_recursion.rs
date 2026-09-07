//! A recursive argument permutation must retain uncertainty in outer frames.

#[test]
fn e5_p_recursive_raw_wrapper_cannot_hide_retirement_of_caller_entry() {
    const CODE: &str = r#"
unsafe extern "C" {
    fn malloc(n: usize) -> *mut u8;
    fn free(p: *mut u8);
}
unsafe fn release_pair(p: *mut u8, q: *mut u8, remaining: u8) {
    if remaining == 0 {
        free(p);
    } else {
        release_pair(q, p, remaining - 1);
    }
}
pub unsafe fn caller(entry: *const u8) -> u8 {
    let value = *entry;
    let fresh = malloc(1);
    release_pair(fresh, entry as *mut u8, 1);
    value
}
"#;
    assert!(
        !super::tests::accepts(CODE, &[("caller", 1, 0)]),
        "the recursive swap retires the caller's protected input; the outer route cannot keep only the disjoint fresh argument"
    );
}
