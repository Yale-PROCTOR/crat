//! wave-6a rule **W6A-A1** (`decision/return_certificate.rs`): allocation-
//! returning callees under a per-callee source-proved certificate (relay
//! wave-6a/005 §1). Fixtures: quadtree `quadtree_node_new` + `test_node`
//! (null-init + `malloc` overwrite, null check, field stores; the receiver
//! lent to Ref callees), buffer `buffer_new_with_size` + `buffer_slice` +
//! its test (a chained return; receivers freed), and controls.

use super::wave6a_allocation_tests::{QUADTREE_NODE_NEW, compact, emitted, reason_of};

fn record(name: &str, source: &str) {
    if let Ok(dir) = std::env::var("CRAT_W6A_EMIT_DIR") {
        std::fs::write(format!("{dir}/{name}-emitted.rs"), source).unwrap();
    }
}

/// buffer `buffer_new_with_size` (malloc struct, null check, field stores,
/// return), `buffer_slice` (a receiver returned — the chain; a real null
/// return, so its output is `Option<Box<T>>`), and the two test shapes (a
/// receiver freed; a receiver null-checked and freed), each test owning its
/// own source buffer (the corpus tests take theirs as a raw parameter, whose
/// class the base already holds on the caller side).
const BUFFER_CHAIN: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_camel_case_types)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn calloc(count: usize, size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
    fn memcpy(dst: *mut core::ffi::c_void, src: *const core::ffi::c_void, n: usize) -> *mut core::ffi::c_void;
}
#[repr(C)]
pub struct buffer_t {
    pub len: usize,
    pub alloc: *mut std::os::raw::c_char,
    pub data: *mut std::os::raw::c_char,
}
pub unsafe extern "C" fn buffer_new_with_size(mut n: usize) -> *mut buffer_t {
    let mut self_0 = malloc(::std::mem::size_of::<buffer_t>()) as *mut buffer_t;
    if self_0.is_null() {
        return 0 as *mut buffer_t;
    }
    (*self_0).len = n;
    (*self_0).alloc = calloc(n.wrapping_add(1), 1) as *mut std::os::raw::c_char;
    (*self_0).data = (*self_0).alloc;
    return self_0;
}
pub unsafe extern "C" fn buffer_slice(mut buf: *mut buffer_t, mut from: usize, mut to: usize) -> *mut buffer_t {
    let mut len = (*buf).len;
    if to > len {
        return 0 as *mut buffer_t;
    }
    let mut n = to - from;
    let mut self_0 = buffer_new_with_size(n);
    memcpy((*self_0).data as *mut core::ffi::c_void, ((*buf).data).offset(from as isize) as *const core::ffi::c_void, n);
    return self_0;
}
pub unsafe extern "C" fn test_buffer_slice() -> usize {
    let mut buf = buffer_new_with_size(4);
    let mut a = buffer_slice(buf, 0, 2);
    let mut n = (*a).len;
    free((*a).alloc as *mut core::ffi::c_void);
    free(a as *mut core::ffi::c_void);
    free((*buf).alloc as *mut core::ffi::c_void);
    free(buf as *mut core::ffi::c_void);
    return n;
}
pub unsafe extern "C" fn test_buffer_slice__range_error() -> i32 {
    let mut buf = buffer_new_with_size(4);
    let mut a = buffer_slice(buf, 0, 100);
    if a.is_null() {
        free((*buf).alloc as *mut core::ffi::c_void);
        free(buf as *mut core::ffi::c_void);
        return 1 as i32;
    }
    free(a as *mut core::ffi::c_void);
    free(buf as *mut core::ffi::c_void);
    return 0 as i32;
}
"#;

/// quadtree: `let mut node = 0 as *mut T; node = malloc(sizeof T) as *mut T;
/// if node.is_null() { return null; } (*node).f = ..; return node;` — the
/// null-init overwrite IS the initializer, the malloc guard is dead (a `Box`
/// cannot be null), the output is `Box<T>`, and the receiver owns it and is
/// lent to the Ref callees through the ordinary `&*node` bridge.
#[test]
fn w6a_a1_quadtree_node_new_returns_a_box_and_the_receiver_owns_it() {
    let out = emitted("cert-quadtree", QUADTREE_NODE_NEW);
    record("quadtree-chain", &out.source);
    let src = compact(&out.source);
    assert_eq!(out.reverted, 0, "{}", out.source);
    assert!(
        src.contains("fnquadtree_node_new()->Box<quadtree_node_t>{"),
        "{}\n{:#?}\n{}",
        out.source,
        out.degradations,
        out.artifacts.return_certificate_receipts
    );
    assert!(
        src.contains("letmutnode:Box<crate::quadtree_node>=Box::new(crate::quadtree_node{ne:0as*mutcrate::quadtree_node,nw:0as*mutcrate::quadtree_node,point:0as*muti32,});{}(*node).ne=0as*mutquadtree_node;"),
        "{}",
        out.source
    );
    assert!(!src.contains("node.is_null()"), "{}", out.source);
    assert!(!src.contains("=malloc("), "{}", out.source);
    assert!(src.contains("returnnode;}"), "{}", out.source);
    assert!(
        src.contains("letmutnode:Box<crate::quadtree_node>=quadtree_node_new();"),
        "{}",
        out.source
    );
    assert!(
        src.contains("quadtree_node_isleaf(&*node)==0"),
        "{}",
        out.source
    );
    for subject in ["quadtree_node_new::node", "test_node::node"] {
        assert_eq!(
            reason_of(&out.degradations, subject),
            None,
            "{subject}: {:#?}",
            out.degradations
        );
    }
    assert!(
        out.artifacts.return_certificate_receipts.contains(
            "quadtree_node_new\tadmitted\treturn-certificate callee=quadtree_node_new output=Box<quadtree_node_t> source=struct-fill model=Some(Raw) null_returns=0 receivers=1 [test_node::node] returned_receivers=0"
        ),
        "{}",
        out.artifacts.return_certificate_receipts
    );
    let declarations =
        super::delivery_custody::inventory_source("lib.rs", &out.source).expect("inventory");
    for (owner, binding) in [("quadtree_node_new", "node"), ("test_node", "node")] {
        let row = declarations
            .iter()
            .find(|row| row.owner == owner && row.binding == binding)
            .unwrap_or_else(|| panic!("{owner}::{binding}: {declarations:#?}"));
        assert!(row.type_is_fully_explicit, "{row:#?}");
    }
}

#[test]
fn w6a_a1_buffer_chain_returns_through_buffer_slice_and_the_tests_free() {
    let out = emitted("cert-buffer", BUFFER_CHAIN);
    record("buffer-chain", &out.source);
    let src = compact(&out.source);
    assert_eq!(
        out.reverted, 0,
        "{}\n{:#?}\n{}",
        out.source, out.degradations, out.artifacts.return_certificate_receipts
    );
    assert!(
        src.contains("fnbuffer_new_with_size(mutn:usize)->Box<buffer_t>{"),
        "{}\n{:#?}\n{}",
        out.source,
        out.degradations,
        out.artifacts.return_certificate_receipts
    );
    assert!(
        src.contains("letmutself_0:Box<crate::buffer_t>=Box::new(crate::buffer_t{len:0asusize,alloc:0as*muti8,data:0as*muti8,});{}(*self_0).len=n;"),
        "{}",
        out.source
    );
    assert!(
        src.contains("(*self_0).data=(*self_0).alloc;returnself_0;}"),
        "{}",
        out.source
    );
    assert!(
        src.contains(
            "fnbuffer_slice(mutbuf:&buffer_t,mutfrom:usize,mutto:usize)->Option<Box<buffer_t>>{"
        ),
        "{}",
        out.source
    );
    assert!(src.contains("ifto>len{returnNone;}"), "{}", out.source);
    assert!(
        src.contains("letmutself_0:Box<crate::buffer_t>=buffer_new_with_size(n);"),
        "{}",
        out.source
    );
    assert!(src.contains("returnSome(self_0);}"), "{}", out.source);
    assert!(
        src.contains("letmutbuf:Box<crate::buffer_t>=buffer_new_with_size(4);letmuta:Option<Box<crate::buffer_t>>=buffer_slice(&*buf,0,2);letmutn=(*a.as_deref_mut().unwrap()).len;free((*a.as_deref_mut().unwrap()).allocas*mutcore::ffi::c_void);drop(a);free((*buf).allocas*mutcore::ffi::c_void);drop(buf);returnn;}"),
        "{}",
        out.source
    );
    assert!(
        src.contains("ifa.is_none(){free((*buf).allocas*mutcore::ffi::c_void);drop(buf);return1asi32;}drop(a);drop(buf);return0asi32;}"),
        "{}",
        out.source
    );
    assert!(!src.contains("*mutbuffer_t"), "{}", out.source);
    for subject in [
        "buffer_new_with_size::self_0",
        "buffer_slice::self_0",
        "buffer_slice::buf",
        "test_buffer_slice::a",
        "test_buffer_slice::buf",
        "test_buffer_slice__range_error::a",
        "test_buffer_slice__range_error::buf",
    ] {
        assert_eq!(
            reason_of(&out.degradations, subject),
            None,
            "{subject}: {:#?}",
            out.degradations
        );
    }
}

const CONTROL_PRELUDE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_camel_case_types)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn calloc(count: usize, size: usize) -> *mut core::ffi::c_void;
    fn realloc(ptr: *mut core::ffi::c_void, size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}
#[repr(C)]
pub struct item {
    pub id: i32,
    pub next: *mut item,
}
"#;

/// lil `add_func`: the returned local is first a lookup result, then a fresh
/// `calloc`, and it is ALSO stored into an array the registry owns — not an
/// owning return.
const LIL_ADD_FUNC: &str = r#"
#[repr(C)]
pub struct registry {
    pub cmd: *mut *mut item,
    pub cmds: usize,
}
unsafe extern "C" fn find_cmd(mut r: *mut registry, mut id: i32) -> *mut item {
    let mut i = 0 as usize;
    while i < (*r).cmds {
        if (**((*r).cmd).offset(i as isize)).id == id {
            return *((*r).cmd).offset(i as isize);
        }
        i = i.wrapping_add(1);
    }
    return 0 as *mut item;
}
unsafe extern "C" fn add_func(mut r: *mut registry, mut id: i32) -> *mut item {
    let mut cmd = 0 as *mut item;
    let mut ncmd = 0 as *mut *mut item;
    cmd = find_cmd(r, id);
    if !cmd.is_null() {
        return cmd;
    }
    cmd = calloc(1, ::std::mem::size_of::<item>()) as *mut item;
    (*cmd).id = id;
    ncmd = realloc((*r).cmd as *mut core::ffi::c_void, ::std::mem::size_of::<*mut item>().wrapping_mul(((*r).cmds).wrapping_add(1))) as *mut *mut item;
    if ncmd.is_null() {
        free(cmd as *mut core::ffi::c_void);
        return 0 as *mut item;
    }
    (*r).cmd = ncmd;
    let fresh = (*r).cmds;
    (*r).cmds = ((*r).cmds).wrapping_add(1);
    *ncmd.offset(fresh as isize) = cmd;
    return cmd;
}
pub unsafe extern "C" fn register(mut r: *mut registry, mut id: i32) -> i32 {
    let mut cmd = add_func(r, id);
    if cmd.is_null() {
        return -(1 as i32);
    }
    return (*cmd).id;
}
"#;

/// Control: the receiver is handed to a raw callee that frees it — a Box in
/// the caller would drop it a second time at scope exit.
const RECEIVER_CONSUMED_RAW: &str = r#"
pub unsafe extern "C" fn item_new(mut id: i32) -> *mut item {
    let mut it = malloc(::std::mem::size_of::<item>()) as *mut item;
    if it.is_null() {
        return 0 as *mut item;
    }
    (*it).id = id;
    (*it).next = 0 as *mut item;
    return it;
}
pub unsafe extern "C" fn item_release(mut it: *mut item, mut flag: i32) {
    if flag != 0 {
        free(it as *mut core::ffi::c_void);
    }
}
pub unsafe extern "C" fn use_item() -> i32 {
    let mut it = item_new(3 as i32);
    let mut id = (*it).id;
    item_release(it, 1 as i32);
    return id;
}
"#;

/// Control: the allocating callee's address is taken — a caller the graph
/// cannot show.
const CALLEE_ADDRESS_TAKEN: &str = r#"
pub unsafe extern "C" fn item_new(mut id: i32) -> *mut item {
    let mut it = malloc(::std::mem::size_of::<item>()) as *mut item;
    if it.is_null() {
        return 0 as *mut item;
    }
    (*it).id = id;
    (*it).next = 0 as *mut item;
    return it;
}
pub static mut MAKER: Option<unsafe extern "C" fn(i32) -> *mut item> = Some(item_new as unsafe extern "C" fn(i32) -> *mut item);
pub unsafe extern "C" fn use_item() -> i32 {
    let mut it = item_new(3 as i32);
    let mut id = (*it).id;
    free(it as *mut core::ffi::c_void);
    return id;
}
"#;

#[test]
fn w6a_a1_lil_add_func_is_not_an_owning_return() {
    let out = emitted("cert-lil", &format!("{CONTROL_PRELUDE}{LIL_ADD_FUNC}"));
    let src = compact(&out.source);
    assert!(!src.contains("Box<"), "{}", out.source);
    assert!(
        out.artifacts
            .return_certificate_receipts
            .contains("add_func::cmd\theld\treturn-certificate-allocation:add_func:"),
        "{}",
        out.artifacts.return_certificate_receipts
    );
    assert_ne!(
        reason_of(&out.degradations, "register::cmd"),
        None,
        "{:#?}",
        out.degradations
    );
}

#[test]
fn w6a_a1_receiver_handed_to_a_freeing_raw_callee_holds() {
    let out = emitted(
        "cert-consumed",
        &format!("{CONTROL_PRELUDE}{RECEIVER_CONSUMED_RAW}"),
    );
    let src = compact(&out.source);
    assert!(!src.contains("Box<"), "{}", out.source);
    assert!(
        out.artifacts.return_certificate_receipts.contains(
            "use_item::it\theld\treturn-certificate-receiver-use:call-argument-not-a-lend:item_release(it, 1 as i32)"
        ),
        "{}",
        out.artifacts.return_certificate_receipts
    );
}

#[test]
fn w6a_a1_callee_with_its_address_taken_holds() {
    let out = emitted(
        "cert-address",
        &format!("{CONTROL_PRELUDE}{CALLEE_ADDRESS_TAKEN}"),
    );
    let src = compact(&out.source);
    assert!(!src.contains("Box<"), "{}", out.source);
    assert!(
        out.artifacts
            .return_certificate_receipts
            .contains("item_new::it\theld\treturn-certificate-indirect-callers:item_new"),
        "{}",
        out.artifacts.return_certificate_receipts
    );
}

/// The same `item_new` with a plain owner: the receiver reads a field and
/// frees — the sized chain with the dead malloc guard.
#[test]
fn w6a_a1_sized_receiver_reads_and_frees() {
    let src_text = format!("{CONTROL_PRELUDE}{}", CALLEE_ADDRESS_TAKEN.replace(
        "pub static mut MAKER: Option<unsafe extern \"C\" fn(i32) -> *mut item> = Some(item_new as unsafe extern \"C\" fn(i32) -> *mut item);\n",
        "",
    ));
    let out = emitted("cert-sized", &src_text);
    record("item-chain", &out.source);
    let src = compact(&out.source);
    assert_eq!(out.reverted, 0, "{}", out.source);
    assert!(
        src.contains("fnitem_new(mutid:i32)->Box<item>{"),
        "{}",
        out.source
    );
    assert!(
        src.contains(
            "letmutit:Box<crate::item>=item_new(3asi32);letmutid=(*it).id;drop(it);returnid;}"
        ),
        "{}",
        out.source
    );
    assert_eq!(
        reason_of(&out.degradations, "use_item::it"),
        None,
        "{:#?}",
        out.degradations
    );
    assert_eq!(
        reason_of(&out.degradations, "item_new::it"),
        None,
        "{:#?}",
        out.degradations
    );
}

/// urlparser `url_get_protocol`: the byte buffer is handed to `sscanf` — a
/// foreign lend this build does not bridge (the raw-boundary retention
/// certificate is the next step); the row holds typed.
const URLPARSER_PROTOCOL: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_camel_case_types)]
extern "C" {
    fn malloc(size: std::os::raw::c_ulong) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
    fn sscanf(s: *const std::os::raw::c_char, fmt: *const std::os::raw::c_char, ...) -> i32;
    fn strcmp(a: *const std::os::raw::c_char, b: *const std::os::raw::c_char) -> i32;
}
pub unsafe extern "C" fn url_is_protocol(mut s: *mut std::os::raw::c_char) -> bool {
    return 0 as i32 == strcmp(b"http\0" as *const u8 as *const std::os::raw::c_char, s);
}
pub unsafe extern "C" fn url_get_protocol(mut url: *mut std::os::raw::c_char) -> *mut std::os::raw::c_char {
    let mut protocol = malloc((16 as std::os::raw::c_ulong) * (::std::mem::size_of::<std::os::raw::c_char>() as std::os::raw::c_ulong)) as *mut std::os::raw::c_char;
    if protocol.is_null() {
        return 0 as *mut std::os::raw::c_char;
    }
    sscanf(url, b"%[^://]\0" as *const u8 as *const std::os::raw::c_char, protocol);
    if url_is_protocol(protocol) {
        return protocol;
    }
    return 0 as *mut std::os::raw::c_char;
}
pub unsafe extern "C" fn url_get_auth(mut url: *mut std::os::raw::c_char) -> i32 {
    let mut protocol = url_get_protocol(url);
    if protocol.is_null() {
        return 0 as i32;
    }
    free(protocol as *mut core::ffi::c_void);
    return 1 as i32;
}
"#;

#[test]
fn w6a_a1_urlparser_protocol_buffer_lent_to_sscanf_holds_typed() {
    let out = emitted("cert-urlparser", URLPARSER_PROTOCOL);
    let src = compact(&out.source);
    assert!(!src.contains("Box<"), "{}", out.source);
    assert!(
        out.artifacts.return_certificate_receipts.contains(
            "url_get_protocol::protocol\theld\treturn-certificate-owner-use:url_get_protocol:call-argument-not-a-lend:sscanf("
        ),
        "{}",
        out.artifacts.return_certificate_receipts
    );
}

/// Control: a receiver is returned by a function whose other return is a
/// parameter — that function has no certificate, so the callee's chain
/// stays open and the callee holds with it (nothing half-typed).
const CHAIN_OPEN: &str = r#"
pub unsafe extern "C" fn item_new(mut id: i32) -> *mut item {
    let mut it = malloc(::std::mem::size_of::<item>()) as *mut item;
    if it.is_null() {
        return 0 as *mut item;
    }
    (*it).id = id;
    (*it).next = 0 as *mut item;
    return it;
}
pub unsafe extern "C" fn pick(mut fresh: i32, mut fallback: *mut item) -> *mut item {
    let mut it = item_new(1 as i32);
    if fresh != 0 {
        return it;
    }
    free(it as *mut core::ffi::c_void);
    return fallback;
}
"#;

#[test]
fn w6a_a1_receiver_returned_by_an_uncertified_function_holds_the_chain() {
    let out = emitted("cert-chain-open", &format!("{CONTROL_PRELUDE}{CHAIN_OPEN}"));
    let src = compact(&out.source);
    assert!(!src.contains("Box<"), "{}", out.source);
    assert!(
        out.artifacts
            .return_certificate_receipts
            .contains("item_new::it\theld\treturn-certificate-chain-open:item_new:pick"),
        "{}",
        out.artifacts.return_certificate_receipts
    );
    assert!(
        out.artifacts
            .return_certificate_receipts
            .contains("pick\theld\treturn-certificate-return-locals:pick:2"),
        "{}",
        out.artifacts.return_certificate_receipts
    );
}

/// Control: a call whose result is stored straight into a field (quadtree's
/// `(*root).nw = quadtree_node_with_bounds(..)` shape) is not a receiver —
/// the callee holds rather than meet that store untyped.
const CALL_INTO_FIELD: &str = r#"
pub unsafe extern "C" fn item_new(mut id: i32) -> *mut item {
    let mut it = malloc(::std::mem::size_of::<item>()) as *mut item;
    if it.is_null() {
        return 0 as *mut item;
    }
    (*it).id = id;
    (*it).next = 0 as *mut item;
    return it;
}
pub unsafe extern "C" fn chain(mut head: *mut item) -> i32 {
    let mut it = item_new(1 as i32);
    (*head).next = item_new(2 as i32);
    let mut id = (*it).id;
    free(it as *mut core::ffi::c_void);
    return id;
}
"#;

#[test]
fn w6a_a1_call_result_stored_into_a_field_holds_the_callee() {
    let out = emitted(
        "cert-field-store",
        &format!("{CONTROL_PRELUDE}{CALL_INTO_FIELD}"),
    );
    let src = compact(&out.source);
    assert!(!src.contains("Box<"), "{}", out.source);
    assert!(
        out.artifacts.return_certificate_receipts.contains(
            "item_new::it\theld\treturn-certificate-call-site-not-a-receiver:item_new:chain:item_new(2 as i32)"
        ),
        "{}",
        out.artifacts.return_certificate_receipts
    );
}
