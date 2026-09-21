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
    // R410-5 §2: the removed malloc guard is receipted per site.
    assert!(
        out.artifacts
            .return_certificate_receipts
            .contains("quadtree_node_new\tadmitted\tdead-alloc-guard site="),
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

/// **A1-c** (the C1 composition): the receiver is handed to a callee that
/// FREES its formal — a consuming formal the Box-parameter chain plans, so
/// the transfer is a move (`item_release(it, 1)`), the formal `Box<item>`,
/// its free `drop(it)`; nothing drops twice.
const RECEIVER_CONSUMED: &str = r#"
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

/// Control: the receiver is handed to a raw callee that KEEPS it (stores
/// it through a raw slot) — not a lend, not a consuming formal: the owner
/// holds.
const RECEIVER_KEPT_RAW: &str = r#"
pub unsafe extern "C" fn item_new(mut id: i32) -> *mut item {
    let mut it = malloc(::std::mem::size_of::<item>()) as *mut item;
    if it.is_null() {
        return 0 as *mut item;
    }
    (*it).id = id;
    (*it).next = 0 as *mut item;
    return it;
}
pub unsafe extern "C" fn item_stash(mut it: *mut item, mut slot: *mut *mut item) {
    *slot = it;
}
pub unsafe extern "C" fn use_item(mut slot: *mut *mut item) -> i32 {
    let mut it = item_new(3 as i32);
    let mut id = (*it).id;
    item_stash(it, slot);
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
    // **Amended by wave-6l W6L-A8-1** (relay 026, wave-6l report 024): this
    // line read `assert_ne!(reason_of(.., "register::cmd"), None)` — the
    // receiver earned nothing, because the certificate family declines it and
    // nothing else could type it. The A8 arm now types it from its own null
    // test, `Option<&mut lil_func>` through the raw pointer's `as_mut()`, so
    // the receiver IS delivered — by the Option form, never an owning one,
    // which is what this witness is about. The `Box<` assertion above is the
    // unchanged pin; this one records the new, non-owning delivery. Revert if
    // wave-6a reads the intent differently.
    assert_eq!(
        reason_of(&out.degradations, "register::cmd"),
        None,
        "{:#?}",
        out.degradations
    );
    assert!(
        src.contains(
            "letmutcmd:Option<&crate::item>=(add_func(r,id)as*constcrate::item).as_ref();"
        ),
        "{}",
        out.source
    );
}

#[test]
fn w6a_a1c_receiver_moved_into_a_consuming_formal_composes_with_the_chain() {
    let out = emitted(
        "cert-consumed",
        &format!("{CONTROL_PRELUDE}{RECEIVER_CONSUMED}"),
    );
    record("item-consumed", &out.source);
    let src = compact(&out.source);
    assert_eq!(out.reverted, 0, "{}", out.source);
    assert!(
        src.contains("fnitem_release(mutit:Box<item>,mutflag:i32){ifflag!=0{drop(it);}}"),
        "{}\n{}\n{}",
        out.source,
        out.artifacts.return_certificate_receipts,
        out.artifacts.box_param_receipts
    );
    assert!(
        src.contains("letmutit:Box<crate::item>=item_new(3asi32);letmutid=(*it).id;item_release(it,1asi32);returnid;}"),
        "{}",
        out.source
    );
    assert!(
        out.artifacts.box_param_receipts.contains(
            "box-param-chain callee=item_release index=0 sink=free pointee=item shape=sized callers=1 members=use_item::it formal_model=Some(Raw)"
        ),
        "{}",
        out.artifacts.box_param_receipts
    );
    for subject in ["item_new::it", "use_item::it", "item_release::it"] {
        assert_eq!(
            reason_of(&out.degradations, subject),
            None,
            "{subject}: {:#?}",
            out.degradations
        );
    }
}

#[test]
fn w6a_a1_receiver_handed_to_a_keeping_raw_callee_holds() {
    let out = emitted(
        "cert-kept",
        &format!("{CONTROL_PRELUDE}{RECEIVER_KEPT_RAW}"),
    );
    let src = compact(&out.source);
    assert!(!src.contains("Box<"), "{}", out.source);
    // W6A-C2 reads `item_stash`'s formal as a syntactic store sink, so the
    // certificate admits the transfer and the CHAIN then refuses it (the
    // destination is a field a C free releases / not an admitted store), and
    // `confirm_transfers` withdraws the certificate: the same hold, reached
    // through the A1-c confirmation rather than the lend refusal.
    assert!(
        out.artifacts.return_certificate_receipts.contains(
            "item_new::it\theld\treturn-certificate-transfer-unconfirmed:item_new:item_stash#0"
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

/// R419-3 / R423-7 (relays 011, 013): `use_item` is a fn-pointer-web ROOT
/// (its address sits in a static table), so `item_new` and `item_release`
/// are web MEMBERS — `item_release`'s converted signature gets the exposure
/// family's raw wrapper, which re-enters ownership (`Box::from_raw(it)`)
/// because the formal is SIZED; `item_new`'s owning return crosses as the
/// raw allocation; every in-crate caller binds to the safe inner name. The
/// certificate and the chain deliver whole.
#[test]
fn w6a_a1_web_member_callee_delivers_through_the_wrapper_bridge() {
    const TABLE: &str = r#"
pub static mut HOOKS: [Option<unsafe extern "C" fn() -> i32>; 1] = [Some(use_item as unsafe extern "C" fn() -> i32)];
"#;
    let out = emitted(
        "cert-web",
        &format!("{CONTROL_PRELUDE}{RECEIVER_CONSUMED}{TABLE}"),
    );
    let src = compact(&out.source);
    assert_eq!(out.reverted, 0, "{}\n{:#?}", out.source, out.degradations);
    assert!(
        src.contains("fnitem_release(mutit:*mutitem,mutflag:i32){__crat_safe_item_release(Box::from_raw(it),flag)}"),
        "{}",
        out.source
    );
    assert!(
        src.contains(
            "fn__crat_safe_item_release(mutit:Box<item>,mutflag:i32){ifflag!=0{drop(it);}}"
        ),
        "{}",
        out.source
    );
    assert!(
        src.contains("fnitem_new(mutid:i32)->Box<item>{"),
        "{}",
        out.source
    );
    assert!(
        src.contains("letmutit:Box<crate::item>=item_new(3asi32);"),
        "{}",
        out.source
    );
    assert!(
        src.contains("__crat_safe_item_release(it,1asi32);"),
        "{}",
        out.source
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

/// **A1-d** urlparser `url_get_protocol`: the byte buffer is handed to
/// `sscanf` and, through `url_is_protocol`, to `strcmp` — foreign lends the
/// pinned libc contract table calls `NoRetain` / `BorrowView`; the owner is
/// bridged at those seams by the ordinary raw-boundary glue. (The corpus
/// callers pass their own raw `url` parameter along, which the base holds
/// `flows-into-raw-param` on the caller's class — kept out of this fixture.)
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
pub unsafe extern "C" fn url_get_protocol() -> *mut std::os::raw::c_char {
    let mut protocol = malloc((16 as std::os::raw::c_ulong) * (::std::mem::size_of::<std::os::raw::c_char>() as std::os::raw::c_ulong)) as *mut std::os::raw::c_char;
    if protocol.is_null() {
        return 0 as *mut std::os::raw::c_char;
    }
    sscanf(b"http://x\0" as *const u8 as *const std::os::raw::c_char, b"%[^://]\0" as *const u8 as *const std::os::raw::c_char, protocol);
    if url_is_protocol(protocol) {
        return protocol;
    }
    return 0 as *mut std::os::raw::c_char;
}
pub unsafe extern "C" fn url_get_auth() -> i32 {
    let mut protocol = url_get_protocol();
    if protocol.is_null() {
        return 0 as i32;
    }
    free(protocol as *mut core::ffi::c_void);
    return 1 as i32;
}
"#;

#[test]
fn w6a_a1d_urlparser_protocol_buffer_lent_to_sscanf_delivers() {
    let out = emitted("cert-urlparser", URLPARSER_PROTOCOL);
    record("urlparser-protocol", &out.source);
    let src = compact(&out.source);
    assert_eq!(
        out.reverted, 0,
        "{}\n{:#?}\n{}",
        out.source, out.degradations, out.artifacts.return_certificate_receipts
    );
    assert!(
        src.contains("Box<[std::os::raw::c_char]>"),
        "{}\n{:#?}\n{}",
        out.source,
        out.degradations,
        out.artifacts.return_certificate_receipts
    );
    // `url_get_protocol` returns null while its buffer is live — the same
    // waiver site, in the shape that landed in batch 9.
    assert_eq!(
        out.artifacts
            .return_certificate_receipts
            .matches("waiver-drop(scope-exit) site=")
            .count(),
        1,
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
            .contains("pick::it\theld\treturn-certificate-return-locals:pick:2"),
        "{}",
        out.artifacts.return_certificate_receipts
    );
}

/// A1-b: a call whose result is stored straight into a raw field
/// (quadtree's `(*root).nw = quadtree_node_with_bounds(..)` shape) is a
/// transfer into C's storage: `Box::into_raw(callee(..))` at the store.
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
    let mut tail = item_new(3 as i32);
    (*(*head).next).next = tail;
    return id;
}
"#;

#[test]
fn w6a_a1_call_result_stored_into_a_raw_field_transfers_through_into_raw() {
    let out = emitted(
        "cert-field-store",
        &format!("{CONTROL_PRELUDE}{CALL_INTO_FIELD}"),
    );
    let src = compact(&out.source);
    assert_eq!(out.reverted, 0, "{}", out.source);
    assert!(
        src.contains("(*head).next=Box::into_raw(item_new(2asi32));"),
        "{}",
        out.source
    );
    assert!(
        src.contains("letmutit:Box<crate::item>=item_new(1asi32);"),
        "{}",
        out.source
    );
    // A non-optional OWNER stored into a raw field: `Box::into_raw(tail)`.
    assert!(
        src.contains(
            "letmuttail:Box<crate::item>=item_new(3asi32);(*(*head).next).next=Box::into_raw(tail);"
        ),
        "{}",
        out.source
    );
    assert!(
        out.artifacts
            .return_certificate_receipts
            .contains("store_sites=1"),
        "{}",
        out.artifacts.return_certificate_receipts
    );
}

/// **A1-b, the quadtree corpus chain reduced**: `quadtree_node_new` (the
/// allocation) → `quadtree_node_with_bounds` (an ASSIGNMENT receiver
/// `node = quadtree_node_new()` with its dead guard, a real null return on
/// the bounds path, `return node`) → `split_node_` (four assignment receivers
/// null-checked and STORED into the parent's fields) and `quadtree_new`
/// (the call stored straight into `(*tree).root`).
const QUADTREE_CHAIN: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_camel_case_types)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}
#[repr(C)]
pub struct quadtree_bounds { pub w: f64, pub h: f64 }
#[repr(C)]
pub struct quadtree_node {
    pub ne: *mut quadtree_node,
    pub nw: *mut quadtree_node,
    pub bounds: *mut quadtree_bounds,
    pub key: *mut core::ffi::c_void,
}
#[repr(C)]
pub struct quadtree { pub root: *mut quadtree_node, pub length: u32 }
pub unsafe extern "C" fn quadtree_bounds_new() -> *mut quadtree_bounds {
    let mut b = malloc(::std::mem::size_of::<quadtree_bounds>()) as *mut quadtree_bounds;
    if b.is_null() {
        return 0 as *mut quadtree_bounds;
    }
    (*b).w = 0.0;
    (*b).h = 0.0;
    return b;
}
pub unsafe extern "C" fn quadtree_bounds_extend(mut b: *mut quadtree_bounds, mut x: f64, mut y: f64) {
    (*b).w = if x > (*b).w { x } else { (*b).w };
    (*b).h = if y > (*b).h { y } else { (*b).h };
}
pub unsafe extern "C" fn quadtree_node_new() -> *mut quadtree_node {
    let mut node = 0 as *mut quadtree_node;
    node = malloc(::std::mem::size_of::<quadtree_node>()) as *mut quadtree_node;
    if node.is_null() {
        return 0 as *mut quadtree_node;
    }
    (*node).ne = 0 as *mut quadtree_node;
    (*node).nw = 0 as *mut quadtree_node;
    (*node).bounds = 0 as *mut quadtree_bounds;
    (*node).key = 0 as *mut core::ffi::c_void;
    return node;
}
pub unsafe extern "C" fn quadtree_node_with_bounds(mut maxx: f64, mut maxy: f64) -> *mut quadtree_node {
    let mut node = 0 as *mut quadtree_node;
    node = quadtree_node_new();
    if node.is_null() {
        return 0 as *mut quadtree_node;
    }
    (*node).bounds = quadtree_bounds_new();
    if ((*node).bounds).is_null() {
        return 0 as *mut quadtree_node;
    }
    quadtree_bounds_extend((*node).bounds, maxx, maxy);
    return node;
}
pub unsafe extern "C" fn split_node_(mut node: *mut quadtree_node) -> i32 {
    let mut nw = 0 as *mut quadtree_node;
    let mut ne = 0 as *mut quadtree_node;
    let mut hw = (*(*node).bounds).w / 2 as i32 as f64;
    nw = quadtree_node_with_bounds(hw, hw);
    if nw.is_null() {
        return 0 as i32;
    }
    ne = quadtree_node_with_bounds(hw * 2 as i32 as f64, hw);
    if ne.is_null() {
        return 0 as i32;
    }
    (*node).nw = nw;
    (*node).ne = ne;
    return 1 as i32;
}
pub unsafe extern "C" fn quadtree_new(mut maxx: f64, mut maxy: f64) -> *mut quadtree {
    let mut tree = 0 as *mut quadtree;
    tree = malloc(::std::mem::size_of::<quadtree>()) as *mut quadtree;
    if tree.is_null() {
        return 0 as *mut quadtree;
    }
    (*tree).root = quadtree_node_with_bounds(maxx, maxy);
    if ((*tree).root).is_null() {
        free(tree as *mut core::ffi::c_void);
        return 0 as *mut quadtree;
    }
    (*tree).length = 0 as u32;
    return tree;
}
pub unsafe extern "C" fn driver() -> i32 {
    let mut tree = quadtree_new(8.0, 8.0);
    if tree.is_null() {
        return -(1 as i32);
    }
    return (*tree).length as i32;
}
"#;

#[test]
fn w6a_a1b_quadtree_assignment_receivers_stores_and_the_stored_call_deliver() {
    let out = emitted("cert-quadtree-chain", QUADTREE_CHAIN);
    record("quadtree-full-chain", &out.source);
    let src = compact(&out.source);
    assert_eq!(
        out.reverted, 0,
        "{}\n{:#?}\n{}",
        out.source, out.degradations, out.artifacts.return_certificate_receipts
    );
    // The allocation: null-init folded, dead guard, `Box<quadtree_node>`.
    assert!(
        src.contains("fnquadtree_node_new()->Box<quadtree_node>{"),
        "{}\n{:#?}\n{}\nCOLLISIONS\n{}",
        out.source,
        out.degradations,
        out.artifacts.return_certificate_receipts,
        out.artifacts.class_collisions
    );
    // The assignment receiver returned, FOLDED (its one assignment is the
    // binding's first use): `let mut node: Box<..> = quadtree_node_new();`,
    // the assignment statement gone, its guard dead, the bounds call stored
    // through `Box::into_raw`, the real null return `None`, `return Some(node)`.
    assert!(
        src.contains("fnquadtree_node_with_bounds(mutmaxx:f64,mutmaxy:f64)->Option<Box<quadtree_node>>{letmutnode:Box<crate::quadtree_node>=quadtree_node_new();{}(*node).bounds=Box::into_raw(quadtree_bounds_new());"),
        "{}",
        out.source
    );
    assert!(
        src.contains("if((*node).bounds).is_null(){returnNone;}"),
        "{}",
        out.source
    );
    assert!(
        src.contains("quadtree_bounds_extend(&mut*(*node).bounds,maxx,maxy);returnSome(node);}"),
        "{}",
        out.source
    );
    // split_node_: two assignment receivers of an optional callee, null-tested,
    // stored into the parent's raw fields.
    assert!(
        src.contains("letmutnw:Option<Box<crate::quadtree_node>>=None;"),
        "{}",
        out.source
    );
    assert!(
        src.contains("nw=quadtree_node_with_bounds(hw,hw);ifnw.is_none(){return0asi32;}"),
        "{}",
        out.source
    );
    assert!(src.contains("(*node).nw=nw.map_or(core::ptr::null_mut(),Box::into_raw);(*node).ne=ne.map_or(core::ptr::null_mut(),Box::into_raw);"), "{}", out.source);
    // quadtree_new: the call stored straight into the raw field.
    assert!(src.contains("(*tree).root=quadtree_node_with_bounds(maxx,maxy).map_or(core::ptr::null_mut(),Box::into_raw);"), "{}", out.source);
    for subject in [
        "quadtree_node_new::node",
        "quadtree_node_with_bounds::node",
        "split_node_::nw",
        "split_node_::ne",
    ] {
        assert_eq!(
            reason_of(&out.degradations, subject),
            None,
            "{subject}: {:#?}",
            out.degradations
        );
    }
}

/// **A1-b, buffer's direct return**: `buffer_new() { return buffer_new_with_size(64) }`
/// chains without a local; its receiver frees.
const BUFFER_DIRECT_RETURN: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_camel_case_types)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}
#[repr(C)]
pub struct buffer_t { pub len: usize, pub data: *mut u8 }
pub unsafe extern "C" fn buffer_new_with_size(mut n: usize) -> *mut buffer_t {
    let mut self_0 = malloc(::std::mem::size_of::<buffer_t>()) as *mut buffer_t;
    if self_0.is_null() {
        return 0 as *mut buffer_t;
    }
    (*self_0).len = n;
    (*self_0).data = 0 as *mut u8;
    return self_0;
}
pub unsafe extern "C" fn buffer_new() -> *mut buffer_t {
    return buffer_new_with_size(64 as usize);
}
pub unsafe extern "C" fn test_buffer_new() -> usize {
    let mut buf = buffer_new();
    let mut n = (*buf).len;
    free(buf as *mut core::ffi::c_void);
    return n;
}
"#;

#[test]
fn w6a_a1b_direct_return_of_a_certified_call_chains() {
    let out = emitted("cert-direct-return", BUFFER_DIRECT_RETURN);
    record("buffer-direct-return", &out.source);
    let src = compact(&out.source);
    assert_eq!(
        out.reverted, 0,
        "{}\n{:#?}\n{}",
        out.source, out.degradations, out.artifacts.return_certificate_receipts
    );
    assert!(
        src.contains("fnbuffer_new()->Box<buffer_t>{returnbuffer_new_with_size(64asusize);}"),
        "{}",
        out.source
    );
    assert!(
        src.contains("letmutbuf:Box<crate::buffer_t>=buffer_new();letmutn=(*buf).len;drop(buf);"),
        "{}",
        out.source
    );
    assert!(
        out.artifacts
            .return_certificate_receipts
            .contains("return-certificate callee=buffer_new output=Box<buffer_t> source=calls"),
        "{}",
        out.artifacts.return_certificate_receipts
    );
}

/// **The conditional return** (relay wave-6a/021; urlparser's `get_part`): the
/// owner leaves through `return if has { ret } else { null }`, not through two
/// `return` statements. It is the same certificate either way — one owner
/// return and one null return, so the output is `Option<Box<T>>` — and the
/// `Some` / `None` edits land on the arms. The census rows read
/// `return-certificate-return-shape` on the whole conditional (report 016 §2).
///
/// The `has == 0` arm abandons a generation the input leaked: Rust closes it
/// at scope exit under the leak-parity waiver, which carries its receipt.
const CONDITIONAL_RETURN: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_camel_case_types)]
extern "C" {
    fn malloc(size: std::os::raw::c_ulong) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}
pub unsafe extern "C" fn get_part(mut has: i32) -> *mut std::os::raw::c_char {
    let mut ret = malloc(::std::mem::size_of::<std::os::raw::c_char>() as std::os::raw::c_ulong) as *mut std::os::raw::c_char;
    if ret.is_null() {
        return 0 as *mut std::os::raw::c_char;
    }
    *ret = 7 as std::os::raw::c_char;
    return if has != 0 as i32 { ret } else { 0 as *mut std::os::raw::c_char };
}
pub unsafe extern "C" fn use_part(mut has: i32) -> i32 {
    let mut p = get_part(has);
    if p.is_null() {
        return 0 as i32;
    }
    let mut v = *p as i32;
    free(p as *mut core::ffi::c_void);
    return v;
}
pub unsafe extern "C" fn get_part_working_arm(mut has: i32) -> *mut std::os::raw::c_char {
    let mut ret = malloc(::std::mem::size_of::<std::os::raw::c_char>() as std::os::raw::c_ulong) as *mut std::os::raw::c_char;
    if ret.is_null() {
        return 0 as *mut std::os::raw::c_char;
    }
    return if has != 0 as i32 { *ret = 1 as std::os::raw::c_char; ret } else { 0 as *mut std::os::raw::c_char };
}
pub unsafe extern "C" fn use_working_arm(mut has: i32) -> i32 {
    let mut q = get_part_working_arm(has);
    if q.is_null() {
        return 0 as i32;
    }
    free(q as *mut core::ffi::c_void);
    return 1 as i32;
}
"#;

#[test]
fn w6a_a1_a_conditional_return_carries_the_option_on_its_arms() {
    let out = emitted("cert-conditional-return", CONDITIONAL_RETURN);
    record("conditional-return", &out.source);
    let src = compact(&out.source);
    let receipts = &out.artifacts.return_certificate_receipts;
    assert_eq!(
        out.reverted, 0,
        "{}\n{:#?}\n{receipts}",
        out.source, out.degradations
    );
    for expected in [
        "fnget_part(muthas:i32)->Option<Box<std::os::raw::c_char>>",
        "returnifhas!=0asi32{Some(ret)}else{None};",
        "letmutp:Option<Box<i8>>=get_part(has);",
        "drop(p);",
    ] {
        assert!(
            src.contains(expected),
            "missing `{expected}`\n{}\n{:#?}\n{receipts}",
            out.source,
            out.degradations
        );
    }
    assert_eq!(
        reason_of(&out.degradations, "get_part::ret"),
        None,
        "{:#?}",
        out.degradations
    );
    assert_eq!(
        receipts.matches("waiver-drop(scope-exit) site=").count(),
        1,
        "{receipts}"
    );
    // CONTROL: an arm that does work before yielding the owner is not read —
    // what those statements do to the generation is exactly what this rule
    // would have to prove, so the shape holds fail-closed.
    assert!(
        receipts.contains("get_part_working_arm\theld\treturn-certificate-return-shape"),
        "{receipts}"
    );
    assert!(
        !src.contains("fnget_part_working_arm(muthas:i32)->Option<"),
        "{}",
        out.source
    );
}
