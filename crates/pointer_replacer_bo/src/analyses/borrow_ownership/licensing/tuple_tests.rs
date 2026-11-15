use super::{super::SlotKind, tests::inspect};

#[test]
fn tuple_raw_payloads_keep_hidden_aliases_raw_across_calls_and_storage() {
    let fixture = inspect(
        r#"
pub struct Store { value: (usize, *mut i32) }
pub unsafe fn identity(value: (usize, *mut i32)) -> (usize, *mut i32) { value }
pub unsafe fn explicit(p: *mut i32) -> i32 {
    let pair = identity((0, p));
    let q = pair.1;
    *p = 1; *q = 2; *p
}
pub unsafe fn hidden(p: *mut i32, pair: (usize, *mut i32)) -> i32 {
    let q = pair.1;
    *p = 1; *q = 2; *p
}
pub unsafe fn stored(p: *mut i32, store: *mut Store) -> i32 {
    let q = (*store).value.1;
    *p = 1; *q = 2; *p
}
pub unsafe fn nested_native(slot: &mut *mut i32, pair: (usize, *mut i32)) -> i32 {
    let q = pair.1;
    let p = *slot;
    *p = 1; *q = 2; *p
}
pub enum EnumStore { Pair((usize, *mut i32)) }
pub unsafe fn enum_store(p: *mut i32, value: EnumStore) -> i32 {
    let EnumStore::Pair((_, q)) = value;
    *p = 1; *q = 2; *p
}
pub union UnionStore { pair: (usize, *mut i32), other: usize }
pub unsafe fn union_store(p: *mut i32, value: UnionStore) -> i32 {
    let q = value.pair.1;
    *p = 1; *q = 2; *p
}
pub unsafe fn nonnull(p: *mut i32, pair: (usize, core::ptr::NonNull<i32>)) -> i32 {
    let q = pair.1.as_ptr();
    *p = 1; *q = 2; *p
}
pub unsafe fn control(p: *const i32, metadata: (usize, usize), values: &Vec<(usize, usize)>) -> i32 {
    *p + metadata.0 as i32 + values.len() as i32
}
pub unsafe fn native(p: *const i32, pair: (&i32, &i32)) -> i32 { *p + *pair.0 + *pair.1 }
pub struct Separate { raw: *const i32, metadata: (usize, usize) }
pub unsafe fn separate(value: Separate) -> i32 { *value.raw + value.metadata.0 as i32 }
pub struct Recursive<T> { payload: T, next: *mut Recursive<Vec<T>> }
pub unsafe fn recursive(p: *const i32, node: &Recursive<i32>) -> i32 { *p + node.payload }
pub struct Wrapper<T> { value: (usize, T) }
pub struct Siblings { first: Wrapper<i32>, second: Wrapper<*mut i32> }
pub unsafe fn siblings(p: *mut i32, value: Siblings) -> i32 {
    let q = value.second.value.1;
    *p = 1; *q = 2; *p
}
pub struct Changed<T> { payload: (T, usize), next: *mut Changed<*mut i32> }
pub unsafe fn changed(p: *mut i32, value: &Changed<i32>) -> i32 {
    let q = (*value.next).payload.0;
    *p = 1; *q = 2; *p
}
pub struct Opaque<T> { value: T, tail: *mut i32 }
pub unsafe fn opaque(p: *mut i32, value: &Opaque<*mut i32>) -> i32 {
    let q = value.value;
    *p = 1; *q = 2; *p
}
"#,
    );
    for key in [
        "explicit::p",
        "explicit::q",
        "hidden::p",
        "hidden::q",
        "stored::p",
        "stored::q",
        "stored::store",
        "nested_native::p",
        "nested_native::q",
        "nested_native::_1@d1",
        "enum_store::p",
        "enum_store::q",
        "union_store::p",
        "union_store::q",
        "nonnull::p",
        "nonnull::q",
        "siblings::p",
        "siblings::q",
        "changed::p",
        "changed::q",
        "opaque::p",
        "opaque::q",
    ] {
        fixture.assert_kind(key, SlotKind::Raw);
    }
    fixture.assert_kind("nested_native::_1@d0", SlotKind::Ref);
    fixture.assert_kind("control::p", SlotKind::Ref);
    fixture.assert_kind("native::p", SlotKind::Ref);
    fixture.assert_kind("Separate.raw", SlotKind::Ref);
    fixture.assert_kind("recursive::p", SlotKind::Ref);
}
