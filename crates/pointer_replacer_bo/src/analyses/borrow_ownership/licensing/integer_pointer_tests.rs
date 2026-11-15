use super::{super::SlotKind, tests::inspect};

#[test]
fn tagged_parent_fields_preserve_raw_aliases_across_functions() {
    let fixture = inspect(
        r#"
#[repr(C)] pub struct Node { parent: usize, left: *mut Node, value: i32 }
pub unsafe fn set_parent(node: *mut Node, parent: *mut Node) {
    (*node).parent = parent as usize | ((*node).parent & 3);
    (*node).left = parent;
}
pub unsafe fn get_parent(node: *const Node) -> *mut Node {
    let bits = (*node).parent & !3usize;
    bits as *mut Node
}
pub unsafe fn set_factor(node: *mut Node, factor: i32) {
    (*node).parent = get_parent(node) as usize | (factor + 1) as usize;
}
pub unsafe fn update(node: *mut Node) -> i32 {
    let parent = get_parent(node);
    let alias = parent;
    (*node).value = 1;
    (*parent).value = 2;
    (*alias).value
}
pub unsafe fn read(pointer: *const i32) -> i32 { *pointer }
"#,
    );
    for key in [
        "set_parent::node",
        "set_parent::parent",
        "get_parent::node",
        "get_parent::_0",
        "set_factor::node",
        "update::node",
        "update::parent",
        "update::alias",
        "Node.left",
    ] {
        fixture.assert_kind(key, SlotKind::Raw);
    }
    fixture.assert_kind("read::pointer", SlotKind::Ref);
}

#[test]
fn reconstruction_keeps_unconnected_aliases_and_nested_raw_layers_raw() {
    let fixture = inspect(
        r#"
pub unsafe fn write(slot: &mut *mut i32, bits: usize) -> i32 {
    let q = bits as *mut i32;
    let p = *slot;
    let r = &raw mut *q;
    *p = 1; *r = 2; *p
}
pub unsafe fn constant(p: *mut i32) -> i32 {
    let q = 1usize as *mut i32;
    *p = 1; *q = 2; *p
}
pub fn null() -> *mut i32 { 0usize as *mut i32 }
"#,
    );
    for key in [
        "write::_1@d1",
        "write::p",
        "write::q",
        "write::r",
        "constant::p",
        "constant::q",
    ] {
        fixture.assert_kind(key, SlotKind::Raw);
    }
    fixture.assert_kind("write::_1@d0", SlotKind::Ref);
    fixture.assert_kind("null::_0", SlotKind::Ref);
}

#[test]
fn encoded_addresses_escape_through_aggregate_fields_without_reconstruction() {
    let fixture = inspect(
        r#"
#[repr(C)] pub struct Holder { bits: usize, pointer: *mut i32, array: [*mut i32; 1] }
pub unsafe fn encode(p: *mut i32) -> Holder {
    let bits = (p as usize).wrapping_add(3) & !1usize;
    Holder { bits, pointer: p, array: [p] }
}
pub unsafe fn decode(holder: Holder) -> *mut i32 {
    let bits = holder.bits;
    (bits & !3usize) as *mut i32
}
pub unsafe fn read(p: *const i32) -> i32 { *p }
"#,
    );
    for key in ["encode::p", "decode::_0", "Holder.pointer", "Holder.array"] {
        fixture.assert_kind(key, SlotKind::Raw);
    }
    fixture.assert_kind("read::p", SlotKind::Ref);
    let encoded_only = inspect(
        r#"
pub struct Encoded { bits: f64 }
pub unsafe fn encode(p: *mut i32) -> Encoded {
    let address = p as usize;
    Encoded { bits: address as f64 }
}
"#,
    );
    encoded_only.assert_kind("encode::p", SlotKind::Raw);
}

#[test]
fn reconstruction_protects_callers_callees_and_static_aliases() {
    let fixture = inspect(
        r#"
static mut SAVED: *mut i32 = 0 as *mut i32;
unsafe fn consume(q: *mut i32) -> i32 {
    let p = SAVED;
    *p = 1; *q = 2; *p
}
unsafe fn decode(bits: usize) -> i32 { consume(bits as *mut i32) }
pub unsafe fn caller(p: *mut i32, bits: usize) -> i32 {
    SAVED = p;
    *p = 3;
    let result = decode(bits);
    *p + result
}
pub unsafe fn reader(p: *const i32) -> i32 { *p }
"#,
    );
    for key in ["consume::q", "consume::p", "caller::p"] {
        fixture.assert_kind(key, SlotKind::Raw);
    }
    fixture.assert_kind("reader::p", SlotKind::Ref);
}

#[test]
fn reconstructed_addresses_propagate_through_static_storage_between_functions() {
    let fixture = inspect(
        r#"
static mut SAVED: *mut i32 = 0 as *mut i32;
pub unsafe fn save(bits: usize) { SAVED = bits as *mut i32; }
pub unsafe fn fetch(other: *mut i32) -> i32 {
    let p = SAVED;
    *other = 1; *p = 2; *other
}
pub unsafe fn read(p: *const i32) -> i32 { *p }
"#,
    );
    fixture.assert_kind("fetch::other", SlotKind::Raw);
    fixture.assert_kind("fetch::p", SlotKind::Raw);
    fixture.assert_kind("read::p", SlotKind::Ref);
}

#[test]
fn local_address_observations_do_not_create_raw_boundaries() {
    let fixture = inspect(
        r#"
pub unsafe fn read(p: *const i32) -> i32 {
    let address = p as usize;
    let _comparison = address == 0;
    *p
}
pub unsafe fn expose(p: *mut i32) -> usize { (p as usize) | 3 }
"#,
    );
    fixture.assert_kind("read::p", SlotKind::Ref);
    fixture.assert_kind("expose::p", SlotKind::Raw);
}
