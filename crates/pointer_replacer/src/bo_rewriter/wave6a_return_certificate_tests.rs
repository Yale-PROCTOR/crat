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
        src.contains("letmutnode:Box<crate::quadtree_node>=::std::boxed::Box::new(crate::quadtree_node{ne:::core::ptr::null_mut(),nw:::core::ptr::null_mut(),point:::core::ptr::null_mut(),});{}(*node).ne=0as*mutquadtree_node;"),
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
        src.contains("letmutself_0:Box<crate::buffer_t>=::std::boxed::Box::new(crate::buffer_t{len:0usize,alloc:::core::ptr::null_mut(),data:::core::ptr::null_mut(),});{}(*self_0).len=n;"),
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

/// **R619-3 (2) — a receiver live at an early exit is receipted** (wave-6o
/// 081 STOP 2). In the chain, `nw` still owns at `ne`'s null return: C leaked
/// it there, and the emitted `Option<Box>` drops it at scope exit. The stores
/// that make both receivers `retained_sink` do not reach that exit. `ne` is
/// stored before every exit its owner reaches (its own null edge holds
/// `None`), so exactly one row, under `split_node_`, names `nw`.
#[test]
fn r619_3_a_receiver_live_at_an_early_exit_is_receipted() {
    let out = emitted("cert-quadtree-exit-close", QUADTREE_CHAIN);
    let receipts = &out.artifacts.return_certificate_receipts;
    let exit_rows = receipts
        .lines()
        .filter(|line| line.contains("exit-path"))
        .collect::<Vec<_>>();
    assert_eq!(
        exit_rows,
        ["split_node_\treceiver\twaiver-drop(scope-exit) exit-path receiver=nw"],
        "{receipts}"
    );
}

/// **R619-3 (2), a loop body's scope exit.** `it` is a `let` receiver inside a
/// loop: on the odd-id `continue` its scope ends before the store, so the
/// emitted owner is dropped there with no `return` anywhere on the path. Its
/// null `continue` holds `None` and is not a close.
const LOOP_EXIT: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_camel_case_types)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
}
#[repr(C)]
pub struct item { pub id: i32 }
#[repr(C)]
pub struct slot { pub it: *mut item }
pub unsafe extern "C" fn item_new(mut id: i32) -> *mut item {
    let mut it = malloc(::std::mem::size_of::<item>()) as *mut item;
    if it.is_null() {
        return 0 as *mut item;
    }
    (*it).id = id;
    return it;
}
pub unsafe extern "C" fn fill(mut s: *mut slot, mut n: i32) {
    let mut i = 0 as i32;
    while i < n {
        let mut it = item_new(i);
        i += 1;
        if it.is_null() {
            continue;
        }
        if (*it).id % 2 as i32 != 0 as i32 {
            continue;
        }
        (*s).it = it;
    }
}
"#;

#[test]
fn r619_3_a_receiver_live_at_a_loop_scope_exit_is_receipted() {
    let out = emitted("cert-loop-exit-close", LOOP_EXIT);
    let receipts = &out.artifacts.return_certificate_receipts;
    let exit_rows = receipts
        .lines()
        .filter(|line| line.contains("exit-path"))
        .collect::<Vec<_>>();
    assert_eq!(
        exit_rows,
        ["fill\treceiver\twaiver-drop(scope-exit) exit-path receiver=it"],
        "{receipts}\n{}",
        out.source
    );
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

/// **The heman cascade's shape** (relay wave-6a/049; main 063 §3's routing
/// table names `heman_lighting_compute_normals` as the seed of 26 of the 69
/// cascade members). `heman_image_create` mallocs a struct, stores a SECOND
/// allocation into one of its fields and returns it; `compute` receives that
/// allocation, reads the field back through a CAST to a different pointee
/// (`(*result).data as *mut Vec3`), walks it, and returns the owner.
const HEMAN_IMAGE_CHAIN: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_camel_case_types, non_snake_case)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}
#[repr(C)]
pub struct Vec3 { pub x: f32, pub y: f32, pub z: f32 }
#[repr(C)]
pub struct Image {
    pub width: i32,
    pub height: i32,
    pub nbands: i32,
    pub data: *mut f32,
}
pub unsafe extern "C" fn image_create(mut width: i32, mut height: i32, mut nbands: i32) -> *mut Image {
    let mut img = malloc(::std::mem::size_of::<Image>()) as *mut Image;
    (*img).width = width;
    (*img).height = height;
    (*img).nbands = nbands;
    (*img).data = malloc(((width * height * nbands) as usize)
        .wrapping_mul(::std::mem::size_of::<f32>())) as *mut f32;
    return img;
}
pub unsafe extern "C" fn compute(mut heightmap: *mut Image) -> *mut Image {
    let mut width = (*heightmap).width;
    let mut height = (*heightmap).height;
    let mut result = image_create(width, height, 3 as i32);
    let mut normals = (*result).data as *mut Vec3;
    let mut y = 0 as i32;
    while y < height {
        let mut n = normals.offset((y * width) as isize);
        let mut x = 0 as i32;
        while x < width {
            (*n).x = x as f32;
            n = n.offset(1 as i32 as isize);
            x += 1;
        }
        y += 1;
    }
    return result;
}
pub unsafe extern "C" fn run() -> i32 {
    let mut base = image_create(2 as i32, 2 as i32, 1 as i32);
    let mut out = compute(base);
    let mut w = (*out).width;
    free((*out).data as *mut core::ffi::c_void);
    free(out as *mut core::ffi::c_void);
    free((*base).data as *mut core::ffi::c_void);
    free(base as *mut core::ffi::c_void);
    return w;
}
"#;

#[test]
fn w6a_a1e_the_heman_cascade_root_is_one_lend() {
    // R528-2: the crate-wide frame lock (wave-6f `3adb662ad`) — this test and
    // wave-6f's lodepng witness share model-cache state, and without the one
    // lock thread order decides which of them loses.
    let _frame = super::test_model_override::frame_lock();
    // **W6A-A1-e** (relay wave-6a/049). The whole shape turns on ONE hold.
    // Bisected on this fixture: dropping the nested field allocation changes
    // nothing, and dropping the call `compute(base)` changes both holds — so
    // `run::base`'s `call-argument-not-a-lend` is the root, it withdraws
    // `image_create`'s certificate, and that leaves `compute::result` with an
    // `uncertified-source`. The callee's formal is `box-param-callee-lends`:
    // the model calls it `Owning`, which the lend oracle refused.
    let out = emitted("a1-heman-chain", HEMAN_IMAGE_CHAIN);
    let text = compact(&out.source);
    let certificates = &out.artifacts.return_certificate_receipts;
    assert!(
        !certificates.contains("call-argument-not-a-lend"),
        "a body-proved lend must not read as a consuming argument\n{certificates}"
    );
    assert!(
        text.contains("mutnbands:i32)->Box<Image>"),
        "the producer's output type is the certificate\n{}",
        out.source
    );
    // The chain continues through compute's own certificate. The FORMAL's
    // form is not this rule's business — it is the parameter family's, and
    // W6A-A9 moves it — so the assertion is a dichotomy over the two frames:
    // without A9 the formal stays raw and the owner is bridged at the call,
    // with A9 it is a reference and the owner is borrowed. Both deliver.
    let raw_formal = text.contains("fncompute(mutheightmap:*mutImage)->Box<Image>")
        && text.contains("compute(core::ptr::from_mut(base.as_mut()))");
    let reference_formal = text.contains("fncompute(mutheightmap:&Image)->Box<Image>")
        && text.contains("compute(&*base)");
    assert!(
        raw_formal != reference_formal,
        "exactly one of the two frames, and the owner crosses the call either way\n{}",
        out.source
    );
    assert!(
        text.contains("free((*out).data") && text.contains("drop(out);"),
        "the struct's C free becomes a drop AT that site; the field's stays a C free\n{}",
        out.source
    );
    assert_eq!(
        reason_of(&out.degradations, "compute::result"),
        None,
        "the receiver of a certified producer is an owner\n{:?}",
        out.degradations
            .iter()
            .map(|d| (d.subject.clone(), d.reason.key().to_owned()))
            .collect::<Vec<_>>()
    );
    assert_eq!(
        reason_of(&out.degradations, "run::base"),
        None,
        "the owner lent across the call keeps its certificate\n{:?}",
        out.degradations
            .iter()
            .map(|d| (d.subject.clone(), d.reason.key().to_owned()))
            .collect::<Vec<_>>()
    );
}

/// Control: the same chain where the lent callee COPIES its formal into a
/// local (`let mut alias = heightmap;`). Nothing frees it and nothing stores
/// it, so neither the transfer path nor any plan diverts the question: the
/// LEND WALK alone must refuse it, on an `Owning`-modeled formal. This is the
/// control that measures the walk, and the fault that skips the walk for
/// `Owning` turns it red.
#[test]
fn w6a_a1e_a_copying_callee_is_not_a_lend() {
    let source = HEMAN_IMAGE_CHAIN.replace(
        "    let mut width = (*heightmap).width;",
        "    let mut alias = heightmap;\n    let mut width = (*alias).width;",
    );
    assert!(
        source.contains("let mut alias = heightmap;"),
        "the control must add the copy"
    );
    let out = emitted("a1-heman-copying", &source);
    assert!(
        out.artifacts
            .return_certificate_receipts
            .contains("call-argument-not-a-lend:compute(base)"),
        "a formal the body copies is not a proven lend\n{}",
        out.artifacts.return_certificate_receipts
    );
    // Measured, and the reason fault 1 (skipping the walk for `Owning`) is
    // INERT: the copy also removes the model's `Owning` verdict — the whole
    // chain reads `kind-raw` here and `compute::heightmap` has no lend hold at
    // all. On every fixture in reach the conjunction `Owning AND !walk.ok` is
    // empty, so no fixture can separate the walk from the kind gate.
    //
    // Read on the producer's own allocation, which nothing masks.
    assert_eq!(
        reason_of(&out.degradations, "image_create::img").as_deref(),
        Some("kind-raw"),
        "{:?}",
        out.degradations
            .iter()
            .map(|d| (d.subject.clone(), d.reason.key().to_owned()))
            .collect::<Vec<_>>()
    );
    // Restated for R528-3: the pass-through is no longer narrowed to A1-e's
    // companion gate (R497-3(b)), so `compute::result` carries the
    // certificate's own refusal instead of the generic model reason — its
    // source is the producer the receiver's refusal withdrew.
    assert_eq!(
        reason_of(&out.degradations, "compute::result").as_deref(),
        Some("return-certificate-return-locals"),
        "{:?}",
        out.degradations
            .iter()
            .map(|d| (d.subject.clone(), d.reason.key().to_owned()))
            .collect::<Vec<_>>()
    );
}

/// **R528-3 — every certificate refusal is its subject's reason.** The copying
/// control's receiver `run::base` is refused by the receiver-use rule
/// (`call-argument-not-a-lend:compute(base)`), and until now only A1-e's
/// companion gate reached the census, so the subject read the model's generic
/// reason and the certificate's refusal lived only in a receipt no census
/// writes. The key is the refusal's own family and the detail is the whole
/// hold, so the wall can be read per subject.
#[test]
fn w6a_r528_a_certificate_refusal_is_the_subjects_reason() {
    let source = HEMAN_IMAGE_CHAIN.replace(
        "    let mut width = (*heightmap).width;",
        "    let mut alias = heightmap;\n    let mut width = (*alias).width;",
    );
    let out = emitted("r528-refusal-is-the-reason", &source);
    let rows: Vec<(String, String, String)> = out
        .degradations
        .iter()
        .map(|d| {
            (
                d.subject.clone(),
                d.reason.key().to_owned(),
                d.reason.detail(),
            )
        })
        .collect();
    let base = rows
        .iter()
        .find(|(subject, ..)| subject == "run::base")
        .unwrap_or_else(|| panic!("the refused receiver is degraded\n{rows:#?}"));
    assert_eq!(base.1, "return-certificate-receiver-use", "{rows:#?}");
    assert!(
        base.2.contains("call-argument-not-a-lend:compute(base)"),
        "the detail is the whole hold\n{rows:#?}"
    );
}

/// quadtree's `insert_` / `split_node_` reduced: a recursive pair that hands
/// the tree to each other and otherwise only reads and writes through it.
const RECURSIVE_LEND: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_camel_case_types)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}
#[repr(C)]
pub struct tree_t {
    pub length: u32,
    pub depth: i32,
}
pub unsafe extern "C" fn tree_new() -> *mut tree_t {
    let mut tree = malloc(::std::mem::size_of::<tree_t>()) as *mut tree_t;
    (*tree).length = 0 as u32;
    (*tree).depth = 0 as i32;
    return tree;
}
unsafe extern "C" fn split_(mut tree: *mut tree_t, mut level: i32) -> i32 {
    (*tree).depth += 1 as i32;
    return insert_(tree, level - 1 as i32);
}
unsafe extern "C" fn insert_(mut tree: *mut tree_t, mut level: i32) -> i32 {
    if level <= 0 as i32 {
        return 1 as i32;
    }
    if (*tree).depth < level {
        return split_(tree, level);
    }
    return insert_(tree, level - 1 as i32);
}
pub unsafe extern "C" fn tree_insert(mut tree: *mut tree_t, mut level: i32) -> i32 {
    if insert_(tree, level) == 0 as i32 {
        return 0 as i32;
    }
    (*tree).length = ((*tree).length).wrapping_add(1 as u32);
    return 1 as i32;
}
pub unsafe extern "C" fn run() -> u32 {
    let mut tree = tree_new();
    tree_insert(tree, 3 as i32);
    let mut n = (*tree).length;
    free(tree as *mut core::ffi::c_void);
    return n;
}
"#;

/// **R528-3 — the receiver-use rule.** `tree_insert(tree, ..)` is a lend:
/// the formal is passed on only into a recursive pair that never frees,
/// stores, returns or copies it. The lend oracle used to answer a cycle
/// "not a lend", so the receiver held `call-argument-not-a-lend` and the
/// producer's certificate withdrew (quadtree's `test_tree::tree`,
/// ownership-fields 058). The pairs admitted through the recursion are
/// receipted one each.
#[test]
fn w6a_r528_a_recursive_pass_on_is_a_lend() {
    let out = emitted("r528-recursive-lend", RECURSIVE_LEND);
    let receipts = &out.artifacts.return_certificate_receipts;
    let text = compact(&out.source);
    assert!(
        !receipts.contains("call-argument-not-a-lend"),
        "a recursive pass-on is a lend\n{receipts}"
    );
    assert!(
        text.contains("fntree_new()->Box<tree_t>"),
        "the producer's certificate stands\n{}",
        out.source
    );
    assert_eq!(
        reason_of(&out.degradations, "run::tree"),
        None,
        "the receiver owns the tree\n{receipts}"
    );
    assert!(
        text.contains("drop(tree);"),
        "the C free is the owner's drop\n{}",
        out.source
    );
    for formal in ["insert_#0", "split_#0", "tree_insert#0"] {
        assert!(
            receipts.contains(&format!("lend\tlend-by-recursion:{formal}")),
            "one receipt per pair admitted through the recursion: {formal}\n{receipts}"
        );
    }
}

/// Control: the same recursion where one member FREES the formal. The walk
/// records `free` as a foreign pass-on and the contract table refuses it, so
/// this measures a refused SUCCESSOR removing every member that reaches it.
#[test]
fn w6a_r528_a_recursion_that_frees_is_not_a_lend() {
    let source = RECURSIVE_LEND.replace(
        "    (*tree).depth += 1 as i32;\n",
        "    (*tree).depth += 1 as i32;\n    if level > 9 as i32 {\n        free(tree as *mut core::ffi::c_void);\n    }\n",
    );
    assert_ne!(source, RECURSIVE_LEND, "the control must add the free");
    let out = emitted("r528-recursive-free", &source);
    let receipts = &out.artifacts.return_certificate_receipts;
    assert!(
        receipts.contains("call-argument-not-a-lend:tree_insert(tree, 3 as i32)"),
        "a member that frees refuses the whole recursion\n{receipts}"
    );
    assert!(!receipts.contains("lend-by-recursion"), "{receipts}");
}

/// Control: the same recursion where one member COPIES the formal. That is a
/// refusal on the member's OWN body, which the greatest fixpoint must keep:
/// the pair starts out of the fixpoint, and its callers fall with it.
#[test]
fn w6a_r528_a_recursion_that_copies_is_not_a_lend() {
    let source = RECURSIVE_LEND.replace(
        "    (*tree).depth += 1 as i32;\n",
        "    let mut alias = tree;\n    (*alias).depth += 1 as i32;\n",
    );
    assert_ne!(source, RECURSIVE_LEND, "the control must add the copy");
    let out = emitted("r528-recursive-copy", &source);
    let receipts = &out.artifacts.return_certificate_receipts;
    assert!(
        receipts.contains("call-argument-not-a-lend:tree_insert(tree, 3 as i32)"),
        "a member whose own body copies refuses the whole recursion\n{receipts}"
    );
    assert!(!receipts.contains("lend-by-recursion"), "{receipts}");
}

/// ht's `ht_create` reduced: the producer stores a second allocation into
/// a field the model calls `Owning` (set by the override below), then returns
/// the owner; the test frees both.
const OWNED_FIELD_TABLE: &str = r#"
// w6a-r528-owned-field-table
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_camel_case_types)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn calloc(count: usize, size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}
#[repr(C)]
pub struct entry_t {
    pub key: i32,
}
#[repr(C)]
pub struct table_t {
    pub cap: usize,
    pub entries: *mut entry_t,
}
pub unsafe extern "C" fn table_new(mut cap: usize) -> *mut table_t {
    let mut t = malloc(::std::mem::size_of::<table_t>()) as *mut table_t;
    (*t).cap = cap;
    (*t).entries = calloc(cap, ::std::mem::size_of::<entry_t>()) as *mut entry_t;
    return t;
}
pub unsafe extern "C" fn run() -> usize {
    let mut t = table_new(4 as usize);
    (*(*t).entries.offset(1 as isize)).key = 3 as i32;
    let mut n = (*t).cap;
    free((*t).entries as *mut core::ffi::c_void);
    free(t as *mut core::ffi::c_void);
    return n;
}
"#;

fn owned_field_table(name: &str, source: &str) -> super::wave6a_allocation_tests::Emitted {
    use crate::analyses::borrow_ownership::SlotKind;
    let _frame = super::test_model_override::frame_lock();
    super::test_model_override::set_with_contract(
        "w6a-r528-owned-field-table",
        vec![("table_t".to_owned(), 1, SlotKind::Owning)],
        Vec::new(),
        Vec::new(),
    );
    let out = emitted(name, source);
    super::test_model_override::clear();
    out
}

/// **R528-3 — A1-e's companion gate admits a HELD owned field** (ht's
/// `ht_create::table`). `entries` is model-`Owning`, but it is indexed and
/// its store carries no length, so its transaction is held and the field
/// stays `*mut entry_t`: the raw zero the certificate spells is exactly the
/// field's type, and the certificate stands.
#[test]
fn w6a_r528_a_held_owned_field_admits_the_certificate() {
    let out = owned_field_table("r528-owned-field-held", OWNED_FIELD_TABLE);
    let receipts = &out.artifacts.return_certificate_receipts;
    let text = compact(&out.source);
    assert!(!receipts.contains(":owned-field"), "{receipts}");
    assert!(
        text.contains("fntable_new(mutcap:usize)->Box<table_t>"),
        "the certificate stands\n{receipts}\n{}",
        out.source
    );
    assert!(
        text.contains("pubentries:*mutentry_t"),
        "the held field stays raw\n{}",
        out.source
    );
}

/// The same producer where the owned field's transaction is DELIVERED
/// (`entries` is only read through, not indexed, so no length is needed and
/// the field becomes `Option<Box<entry_t>>`). R528-3 withdrew the certificate
/// here, because its raw zero would be an `E0308`.
///
/// **Restated for R579-4 R1 — the gate re-renders.** The certificate spells
/// its literal again with the delivered form (`entries: None`, ownership-
/// fields' own spelling) and stands: `table_new` returns `Box<table_t>`, its
/// receiver is a `Box`, and the delivered field's store and C free are the
/// field transaction's. (A WRITE through the delivered field renders
/// `.as_deref()` and does not compile — wave-6f's rendering, routed in report
/// 077 — so the fixture reads.)
#[test]
fn w6a_r579_a_delivered_owned_field_re_renders_the_certificate() {
    let source = OWNED_FIELD_TABLE.replace(
        "    (*(*t).entries.offset(1 as isize)).key = 3 as i32;\n",
        "    let mut k = (*(*t).entries).key;\n",
    );
    assert_ne!(source, OWNED_FIELD_TABLE, "the control must drop the index");
    let out = owned_field_table("r528-owned-field-delivered", &source);
    let receipts = &out.artifacts.return_certificate_receipts;
    let text = compact(&out.source);
    assert_eq!(out.reverted, 0, "{receipts}\n{}", out.source);
    assert!(
        !receipts.contains(":owned-field"),
        "{receipts}\n{}",
        out.source
    );
    assert!(
        text.contains("fntable_new(mutcap:usize)->Box<table_t>"),
        "{receipts}\n{}",
        out.source
    );
    assert!(
        text.contains("Box::new(crate::table_t{cap:0usize,entries:None})"),
        "{}",
        out.source
    );
    assert!(
        text.contains("letmutt:Box<crate::table_t>=table_new(4asusize);"),
        "{}",
        out.source
    );
    assert_eq!(
        reason_of(&out.degradations, "table_new::t"),
        None,
        "{receipts}"
    );
}

/// **R531-4 (i), main's guard (a).** The widening is reason-only because it
/// never runs where a family could still deliver: no in-ladder consultation
/// (`held` / `held_final`) exists any more, and the one rename runs exactly
/// once, on the settled table right after `retired.append`, with no decision
/// made after it in `finish_decide`. Its body rewrites only a degraded
/// record's reason — never a decision. A later edit that adds a call site in
/// the ladder, moves the call ahead of a decide, or lets the rename touch a
/// decision turns this red.
#[test]
fn w6a_r531_the_rename_runs_once_on_the_settled_table() {
    let pipeline = include_str!("mod.rs");
    let ladder = include_str!("decision/mod.rs");
    let certificate = include_str!("decision/return_certificate.rs");
    let code = |text: &'static str| {
        text.lines()
            .map(str::trim)
            .filter(|line| !line.is_empty() && !line.starts_with("//"))
            .collect::<Vec<_>>()
    };
    for (name, text) in [
        ("mod.rs", pipeline),
        ("decision/mod.rs", ladder),
        ("return_certificate.rs", certificate),
    ] {
        for line in code(text) {
            assert!(
                !line.contains("return_certificate::held(")
                    && !line.contains("return_certificate::held_final(")
                    && !line.contains("fn held(")
                    && !line.contains("fn held_final("),
                "{name}: an in-ladder consultation is back: {line}"
            );
        }
    }
    let lines = code(pipeline);
    let calls = lines
        .iter()
        .enumerate()
        .filter(|(_, line)| line.contains("relabel_refused("))
        .map(|(at, _)| at)
        .collect::<Vec<_>>();
    assert_eq!(calls.len(), 1, "exactly one rename");
    assert!(
        code(ladder)
            .iter()
            .all(|line| !line.contains("relabel_refused(")),
        "never inside the ladder"
    );
    let at = calls[0];
    assert_eq!(
        lines[at - 1],
        "retired.append(&mut table, &prepared.plan);",
        "the rename sits on the settled table, after the stage loop's last stage"
    );
    let rest = lines[at..]
        .iter()
        .take_while(|line| !line.starts_with("return Ok((table, context));"))
        .collect::<Vec<_>>();
    assert!(
        rest.iter().all(|line| !line.contains("decision::decide(")),
        "no decision is made after the rename"
    );
    let body = certificate
        .split("pub(crate) fn relabel_refused(")
        .nth(1)
        .and_then(|rest| rest.split("\n}\n").next())
        .expect("the rename's body");
    let writes = body
        .lines()
        .map(str::trim)
        .filter(|line| !line.starts_with("//") && line.contains(" = ") && !line.starts_with("let "))
        .collect::<Vec<_>>();
    assert_eq!(
        writes,
        ["record.reason = super::DegradeReason::BoxFailure {"],
        "{body}"
    );
}

/// R528-3's key table is total: every hold family `certify` writes (a
/// `"return-certificate-<family>:` literal outside a receipt) has its own key,
/// so no refusal collapses into the root key at census.
#[test]
fn w6a_r528_every_hold_family_has_a_key() {
    let source = include_str!("decision/return_certificate.rs");
    let mut families = std::collections::BTreeSet::new();
    for line in source.lines() {
        let code = line.trim_start();
        if code.starts_with("//") || line.contains("receipt") {
            continue;
        }
        for (at, _) in line.match_indices("\"return-certificate-") {
            let rest = &line[at + 1..];
            let end = rest
                .find(|c: char| !(c.is_ascii_lowercase() || c == '-'))
                .unwrap_or(rest.len());
            if rest[end..].starts_with(':') {
                families.insert(&rest[..end]);
            }
        }
    }
    let keys = super::decision::return_certificate::HOLD_KEYS
        .iter()
        .copied()
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(families, keys);
}

/// Control: the same chain where the lent callee STORES its formal into a raw
/// place. Nothing frees it, so the transfer path does not divert the question
/// — the LEND WALK itself must refuse, and the caller's certificate must not
/// stand. This is the control that measures the walk on an `Owning` formal.
#[test]
fn w6a_a1e_a_storing_callee_is_not_a_lend() {
    let source = HEMAN_IMAGE_CHAIN.replace(
        "    let mut normals = (*result).data as *mut Vec3;",
        "    (*result).data = heightmap as *mut f32;\n    let mut normals = (*result).data as *mut Vec3;",
    );
    assert!(
        source.contains("(*result).data = heightmap"),
        "the control must add the store"
    );
    let out = emitted("a1-heman-storing", &source);
    let text = compact(&out.source);
    assert!(
        !text.contains("letmutbase:Box<"),
        "an owner the callee stores away is not the caller's to keep\n{}",
        out.source
    );
    assert!(
        reason_of(&out.degradations, "run::base").is_some(),
        "run::base must stay degraded\n{:?}",
        out.degradations
            .iter()
            .map(|d| (d.subject.clone(), d.reason.key().to_owned()))
            .collect::<Vec<_>>()
    );
}

/// The admitted kinds, stated exactly: `Ref` (the model's own lend verdict),
/// `Raw` (an absence the body may fill) and — W6A-A1-e — `Owning` (a claim
/// about the FORMAL that the caller's question does not touch). A formal with
/// no slot answers nothing.
#[test]
fn w6a_a1e_the_admitted_kinds_are_exactly_three() {
    use crate::analyses::borrow_ownership::SlotKind;
    assert!(super::decision::return_certificate::model_admits_lend(
        Some(SlotKind::Ref)
    ));
    assert!(super::decision::return_certificate::model_admits_lend(
        Some(SlotKind::Raw)
    ));
    assert!(super::decision::return_certificate::model_admits_lend(
        Some(SlotKind::Owning)
    ));
    assert!(!super::decision::return_certificate::model_admits_lend(
        None
    ));
}

/// Control: the same chain where the lent callee FREES its formal. The body
/// walk refuses it, the argument is a consuming one again, and the caller's
/// certificate must not stand — a Box moved into a raw free is the
/// double-free path A1 exists to avoid.
#[test]
fn w6a_a1e_a_freeing_callee_is_not_a_lend_however_the_model_reads_it() {
    let source = HEMAN_IMAGE_CHAIN.replace(
        "    return result;\n}",
        "    free(heightmap as *mut core::ffi::c_void);\n    return result;\n}",
    );
    assert!(
        source.contains("free(heightmap"),
        "the control must add the free"
    );
    let out = emitted("a1-heman-freeing", &source);
    let text = compact(&out.source);
    assert!(
        !text.contains("letmutbase:Box<") && !text.contains("letmutbase:::std::boxed::Box<"),
        "an owner the callee frees is not the caller's to keep\n{}",
        out.source
    );
    assert!(
        reason_of(&out.degradations, "run::base").is_some(),
        "run::base must stay degraded\n{:?}",
        out.degradations
            .iter()
            .map(|d| (d.subject.clone(), d.reason.key().to_owned()))
            .collect::<Vec<_>>()
    );
}

/// **W6A-A1-f — a chain-through callee does not open the chain** (relay
/// wave-6a/068, R515-4). avl's and bst's shape, reduced: `newNode` allocates
/// and returns; `insert` returns either its own PARAMETER or `newNode(..)` —
/// never a third thing. `insert` cannot be certified (its returned local is a
/// parameter, not an allocation), and until this rule that refusal
/// (`return-certificate-return-locals:insert:not-a-subject`) withdrew
/// `newNode`'s certificate as `chain-open` collateral, costing the allocation
/// its Box. The callee's own return statements are the proof: it hands the
/// value onward and originates nothing.
const INSERT_CHAIN: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_camel_case_types, non_snake_case)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}
#[repr(C)]
pub struct Node {
    pub key: i32,
    pub left: *mut Node,
    pub right: *mut Node,
}
unsafe extern "C" fn newNode(mut key: i32) -> *mut Node {
    let mut node = malloc(::std::mem::size_of::<Node>()) as *mut Node;
    (*node).key = key;
    (*node).left = 0 as *mut Node;
    (*node).right = 0 as *mut Node;
    return node;
}
unsafe extern "C" fn insert(mut node: *mut Node, mut key: i32) -> *mut Node {
    if node.is_null() {
        return newNode(key);
    }
    if key < (*node).key {
        (*node).left = insert((*node).left, key);
    } else {
        (*node).right = insert((*node).right, key);
    }
    return node;
}
pub unsafe extern "C" fn run() -> i32 {
    let mut root = newNode(5 as i32);
    root = insert(root, 3 as i32);
    let mut k = (*root).key;
    free(root as *mut core::ffi::c_void);
    return k;
}
"#;

#[test]
fn w6a_a1f_a_chain_through_callee_does_not_open_the_chain() {
    let out = emitted("a1f-insert-chain", INSERT_CHAIN);
    let certificates = &out.artifacts.return_certificate_receipts;
    assert!(
        certificates.contains("chain-through:insert:returns-parameter-or-certified"),
        "the pass-over is receipted by name\n{certificates}"
    );
    assert!(
        !certificates.contains("return-certificate-chain-open"),
        "a chain-through callee does not open the chain\n{certificates}"
    );
    assert!(
        !certificates.contains("return-locals:insert:not-a-subject"),
        "and it is no longer a refusal\n{certificates}"
    );
    // What the ruling bought stops here. `newNode::node` still does not emit,
    // and the rule is what makes the reason legible: the receiver `run::root`
    // is passed BACK INTO the chain-through callee (`root = insert(root, 3)`),
    // which the lend oracle refuses because `insert` returns the formal rather
    // than only borrowing it. That is a second wall, named, not this one.
    assert!(
        certificates.contains("call-argument-not-a-lend:insert(root"),
        "the next wall is the receiver's own use\n{certificates}"
    );
}

/// The same rule where the receiver is NOT handed back to the chain-through
/// callee: the certificate then stands and the allocation is a `Box`.
const INSERT_CHAIN_PLAIN_RECEIVER: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_camel_case_types, non_snake_case)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}
#[repr(C)]
pub struct Node {
    pub key: i32,
    pub left: *mut Node,
    pub right: *mut Node,
}
unsafe extern "C" fn newNode(mut key: i32) -> *mut Node {
    let mut node = malloc(::std::mem::size_of::<Node>()) as *mut Node;
    (*node).key = key;
    (*node).left = 0 as *mut Node;
    (*node).right = 0 as *mut Node;
    return node;
}
unsafe extern "C" fn pick(mut node: *mut Node, mut key: i32) -> *mut Node {
    if node.is_null() {
        return newNode(key);
    }
    return node;
}
pub unsafe extern "C" fn run() -> i32 {
    let mut root = newNode(5 as i32);
    let mut k = (*root).key;
    free(root as *mut core::ffi::c_void);
    return k;
}
"#;

#[test]
fn w6a_a1f_the_pass_through_delivers_through_the_return_position() {
    // **R517-9, the return-position arm.** The pass-through keeps its raw
    // return type, so `return newNode(key)` inside it is bridged back raw —
    // and the bridge is what makes the enclosing return the call's RECEIVER.
    // Until that was said, the certificate refused its own bridged site as
    // `call-site-not-a-receiver` and the constructor stopped one wall short
    // (report 062).
    let out = emitted("a1f-plain-receiver", INSERT_CHAIN_PLAIN_RECEIVER);
    let certificates = &out.artifacts.return_certificate_receipts;
    assert!(
        certificates.contains("chain-through:pick:returns-parameter-or-certified"),
        "{certificates}"
    );
    assert!(
        !certificates.contains("call-site-not-a-receiver"),
        "the enclosing return IS the receiver\n{certificates}"
    );
    assert!(
        certificates.contains("return-certificate callee=newNode output=Box<Node>"),
        "the constructor is certified\n{certificates}"
    );
    assert_eq!(
        reason_of(&out.degradations, "newNode::node"),
        None,
        "and its allocation is an owner\nRECEIPTS:\n{certificates}\n{:?}",
        out.degradations
            .iter()
            .map(|d| (d.subject.clone(), d.reason.key().to_owned()))
            .collect::<Vec<_>>()
    );
    let text = compact(&out.source);
    assert!(
        text.contains("fnnewNode(mutkey:i32)->Box<Node>")
            && text.contains("Box::into_raw(newNode(key))"),
        "{}",
        out.source
    );
}

/// Control (relay 068's "a third value"): the middle callee returns its
/// parameter, a certified constructor's result AND a third local. The proof
/// the pass-over rests on — that the callee originates nothing — does not
/// hold, so the chain stays open.
const THIRD_VALUE_MIDDLE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_camel_case_types, non_snake_case)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}
#[repr(C)]
pub struct Node {
    pub key: i32,
    pub left: *mut Node,
    pub right: *mut Node,
}
unsafe extern "C" fn newNode(mut key: i32) -> *mut Node {
    let mut node = malloc(::std::mem::size_of::<Node>()) as *mut Node;
    (*node).key = key;
    return node;
}
unsafe extern "C" fn pick3(mut node: *mut Node, mut key: i32) -> *mut Node {
    if node.is_null() {
        return newNode(key);
    }
    if key < 0 as i32 {
        let mut other = (*node).left;
        return other;
    }
    return node;
}
pub unsafe extern "C" fn run() -> i32 {
    let mut root = newNode(5 as i32);
    let mut k = (*root).key;
    free(root as *mut core::ffi::c_void);
    return k;
}
"#;

#[test]
fn w6a_a1f_a_third_returned_value_keeps_the_chain_open() {
    let out = emitted("a1f-third-value", THIRD_VALUE_MIDDLE);
    let certificates = &out.artifacts.return_certificate_receipts;
    assert!(
        !certificates.contains("chain-through:pick3:"),
        "a callee that returns a third value originates something\n{certificates}"
    );
}

/// Control: the middle callee STORES its parameter away instead of handing it
/// onward, so it is not a chain-through and the chain stays open.
const STORING_MIDDLE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_camel_case_types, non_snake_case)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}
#[repr(C)]
pub struct Node {
    pub key: i32,
    pub left: *mut Node,
    pub right: *mut Node,
}
static mut STASH: *mut Node = 0 as *mut Node;
unsafe extern "C" fn newNode(mut key: i32) -> *mut Node {
    let mut node = malloc(::std::mem::size_of::<Node>()) as *mut Node;
    (*node).key = key;
    return node;
}
unsafe extern "C" fn keep(mut node: *mut Node, mut key: i32) -> *mut Node {
    if node.is_null() {
        return newNode(key);
    }
    STASH = node;
    return node;
}
pub unsafe extern "C" fn run() -> i32 {
    let mut root = newNode(5 as i32);
    let mut k = (*root).key;
    free(root as *mut core::ffi::c_void);
    return k;
}
"#;

#[test]
fn w6a_a1f_a_storing_middle_is_not_a_chain_through() {
    let out = emitted("a1f-storing-middle", STORING_MIDDLE);
    let certificates = &out.artifacts.return_certificate_receipts;
    assert!(
        !certificates.contains("chain-through:keep:"),
        "a callee that stores its parameter is not passed over\n{certificates}"
    );
}

/// **W6A-A1-g — a returned block whose statements cannot touch the owner**
/// (relay wave-6a/072 (e)). buffer's shape, reduced: c2rust hoists an argument
/// into a `let` and returns the block —
/// `return { let __arg_1 = strlen(str); buffer_new_with_string_length(str, __arg_1) };`
/// — so the certificate read `return-shape:{ .. }` for the wrapper and
/// `call-site-not-a-receiver` for the constructor inside it, and both stopped.
///
/// The block is descended into when every statement is a `let` binding a
/// NON-POINTER local: such a statement cannot hold, alter or alias the owner,
/// which does not exist until the tail call returns. A statement binding a
/// pointer, or any other statement, keeps the old refusal — that is precisely
/// the thing the rule would otherwise have to prove.
const BLOCK_RETURN: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_camel_case_types, non_snake_case)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
    fn strlen(s: *const i8) -> usize;
}
#[repr(C)]
pub struct buffer_t {
    pub len: usize,
    pub data: *mut i8,
}
unsafe extern "C" fn buffer_new_with_size(mut n: usize) -> *mut buffer_t {
    let mut self_0 = malloc(::std::mem::size_of::<buffer_t>()) as *mut buffer_t;
    (*self_0).len = n;
    (*self_0).data = 0 as *mut i8;
    return self_0;
}
unsafe extern "C" fn buffer_new_with_string_length(mut str: *mut i8, mut len: usize)
    -> *mut buffer_t {
    return buffer_new_with_size(len);
}
pub unsafe extern "C" fn buffer_new_with_string(mut str: *mut i8) -> *mut buffer_t {
    return {
        let __arg_1 = strlen(str);
        buffer_new_with_string_length(str, __arg_1)
    };
}
pub unsafe extern "C" fn run(mut s: *mut i8) -> usize {
    let mut b = buffer_new_with_string(s);
    let mut n = (*b).len;
    free(b as *mut core::ffi::c_void);
    return n;
}
"#;

#[test]
fn w6a_a1g_a_returned_block_of_scalar_lets_is_descended_into() {
    let out = emitted("a1g-block-return", BLOCK_RETURN);
    let certificates = &out.artifacts.return_certificate_receipts;
    assert!(
        !certificates.contains("return-certificate-return-shape:"),
        "the block is read through, not refused\n{certificates}"
    );
    assert!(
        !certificates.contains("call-site-not-a-receiver"),
        "and the call inside it has the enclosing return as its receiver\n{certificates}"
    );
    assert_eq!(
        reason_of(&out.degradations, "buffer_new_with_size::self_0"),
        None,
        "the allocation at the bottom of the chain is an owner\nRECEIPTS:\n{certificates}\n{:?}",
        out.degradations
            .iter()
            .map(|d| (d.subject.clone(), d.reason.key().to_owned()))
            .collect::<Vec<_>>()
    );
}

/// Control: the block binds a POINTER local, which this rule cannot read
/// through — the refusal stands.
#[test]
fn w6a_a1g_a_block_binding_a_pointer_keeps_its_refusal() {
    let source = BLOCK_RETURN.replace(
        "        let __arg_1 = strlen(str);",
        "        let __arg_1 = strlen(str);\n        let mut alias = str;",
    );
    assert!(
        source.contains("let mut alias = str;"),
        "the control must bind a pointer"
    );
    let out = emitted("a1g-block-pointer", &source);
    assert!(
        out.artifacts
            .return_certificate_receipts
            .contains("return-certificate-return-shape:"),
        "a pointer binding keeps the block opaque\n{}",
        out.artifacts.return_certificate_receipts
    );
}

/// **R561-4 W1 — a re-seated `let` receiver.** buffer's `test_buffer_trim`:
/// `let mut buf = f(..); …; <consume buf>; buf = f(..); …` — each re-seat by
/// the same callee after the previous generation was consumed is one more
/// generation of the same Box local (`buf = f(..)` after the move is plain
/// Rust). The certificate admitted only `let` receivers and null-initialised
/// assignment receivers, so the re-seat was a call with nowhere to go
/// (`call-site-not-a-receiver`), and every certificate chained through the
/// callee closed with it (buffer: the three constructors and the 22 locals).
fn reseat_fixture(driver: &str) -> String {
    let head = &BUFFER_CHAIN[..BUFFER_CHAIN
        .find("pub unsafe extern \"C\" fn buffer_slice")
        .expect("the fixture's head")];
    format!("{head}{driver}")
}

const RESEAT_AFTER_FREE: &str = r#"
pub unsafe extern "C" fn test_buffer_trim() -> usize {
    let mut buf = buffer_new_with_size(3);
    let mut n = (*buf).len;
    free((*buf).alloc as *mut core::ffi::c_void);
    free(buf as *mut core::ffi::c_void);
    buf = buffer_new_with_size(4);
    n = n.wrapping_add((*buf).len);
    free((*buf).alloc as *mut core::ffi::c_void);
    free(buf as *mut core::ffi::c_void);
    buf = buffer_new_with_size(5);
    n = n.wrapping_add((*buf).len);
    free((*buf).alloc as *mut core::ffi::c_void);
    free(buf as *mut core::ffi::c_void);
    return n;
}
"#;

#[test]
fn w6a_r561_a_let_receiver_reseated_after_its_free_is_one_box_local() {
    let out = emitted("r561-reseat", &reseat_fixture(RESEAT_AFTER_FREE));
    let src = compact(&out.source);
    assert_eq!(
        out.reverted, 0,
        "{}\n{:#?}\n{}",
        out.source, out.degradations, out.artifacts.return_certificate_receipts
    );
    for subject in ["buffer_new_with_size::self_0", "test_buffer_trim::buf"] {
        assert_eq!(
            reason_of(&out.degradations, subject),
            None,
            "{subject}\n{:#?}\n{}\n{}",
            out.degradations,
            out.artifacts.return_certificate_receipts,
            out.source
        );
    }
    assert!(
        src.contains("letmutbuf:Box<crate::buffer_t>=buffer_new_with_size(3);"),
        "{}",
        out.source
    );
    assert!(
        src.contains("drop(buf);buf=buffer_new_with_size(4);"),
        "{}",
        out.source
    );
    assert!(
        src.contains("drop(buf);buf=buffer_new_with_size(5);"),
        "{}",
        out.source
    );
}

/// Control: a first generation freed only inside a branch is still live on
/// the other path when the re-seat overwrites it — refused like the plain
/// overwrite. The consume must be a statement of the re-seat's own block.
#[test]
fn w6a_r561_a_reseat_after_a_branch_free_stays_refused() {
    let branch = RESEAT_AFTER_FREE.replacen(
        "    free(buf as *mut core::ffi::c_void);\n    buf = buffer_new_with_size(4);",
        "    if n > 0 {\n        free(buf as *mut core::ffi::c_void);\n    }\n    buf = buffer_new_with_size(4);",
        1,
    );
    assert_ne!(
        branch, RESEAT_AFTER_FREE,
        "the control moves the first generation's free into a branch"
    );
    let out = emitted("r561-reseat-branch", &reseat_fixture(&branch));
    assert!(
        !compact(&out.source).contains("letmutbuf:Box<crate::buffer_t>="),
        "{}\n{}",
        out.artifacts.return_certificate_receipts,
        out.source
    );
}

/// Control: a re-seat over a LIVE owner (the first generation never freed) is
/// an overwrite, the leak-parity line — it stays refused.
#[test]
fn w6a_r561_a_reseat_over_a_live_owner_stays_refused() {
    let live = RESEAT_AFTER_FREE.replacen(
        "    free(buf as *mut core::ffi::c_void);\n    buf = buffer_new_with_size(4);",
        "    buf = buffer_new_with_size(4);",
        1,
    );
    assert_ne!(
        live, RESEAT_AFTER_FREE,
        "the control removes the first generation's free"
    );
    let out = emitted("r561-reseat-live", &reseat_fixture(&live));
    assert!(
        out.artifacts.return_certificate_receipts.contains(
            "return-certificate-receiver-use:reseat-over-live-owner:test_buffer_trim::buf"
        ),
        "{}\n{:#?}\n{}",
        out.artifacts.return_certificate_receipts,
        out.degradations,
        out.source
    );
    assert!(
        !compact(&out.source).contains("letmutbuf:Box<crate::buffer_t>="),
        "{}",
        out.source
    );
}

/// bst, reduced from the corpus: `newNode` mallocs and fills a node,
/// `insert` / `deleteNode` recurse and store the recursive result into the
/// node's own `left` / `right`.
const BST: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, non_snake_case)]
// w6a-r578-bst-frame
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}
#[repr(C)]
pub struct node {
    pub key: i32,
    pub left: *mut node,
    pub right: *mut node,
}
#[no_mangle]
pub unsafe extern "C" fn newNode(mut item: i32) -> *mut node {
    let mut temp = malloc(::std::mem::size_of::<node>()) as *mut node;
    (*temp).key = item;
    (*temp).left = 0 as *mut node;
    (*temp).right = 0 as *mut node;
    return temp;
}
#[no_mangle]
pub unsafe extern "C" fn insert(mut node: *mut node, mut key: i32) -> *mut node {
    if node.is_null() { return newNode(key); }
    if key < (*node).key {
        (*node).left = insert((*node).left, key);
    } else { (*node).right = insert((*node).right, key); }
    return node;
}
#[no_mangle]
pub unsafe extern "C" fn minValueNode(mut node: *mut node) -> *mut node {
    while !node.is_null() && !((*node).left).is_null() {
        node = (*node).left;
    }
    return node;
}
#[no_mangle]
pub unsafe extern "C" fn deleteNode(mut root: *mut node, mut key: i32) -> *mut node {
    if root.is_null() { return root; }
    if key < (*root).key {
        (*root).left = deleteNode((*root).left, key);
    } else if key > (*root).key {
        (*root).right = deleteNode((*root).right, key);
    } else {
        if ((*root).left).is_null() {
            let mut temp = (*root).right;
            free(root as *mut core::ffi::c_void);
            return temp;
        } else {
            if ((*root).right).is_null() {
                let mut temp_0 = (*root).left;
                free(root as *mut core::ffi::c_void);
                return temp_0;
            }
        }
        let mut temp_1 = minValueNode((*root).right);
        (*root).key = (*temp_1).key;
        (*root).right = deleteNode((*root).right, (*temp_1).key);
    }
    return root;
}
"#;

/// era-5c's bst frame (the solve's 0 raw / 13 ref / 31 owning), as wave-6f
/// states it for its own witnesses: both `node` fields and every node owner
/// Owning, the traversal subjects Ref.
fn bst_frame() {
    use crate::analyses::borrow_ownership::SlotKind;
    super::test_model_override::set(
        "w6a-r578-bst-frame",
        vec![
            ("node".to_owned(), 1, SlotKind::Owning),
            ("node".to_owned(), 2, SlotKind::Owning),
        ],
        vec![
            ("insert::node".to_owned(), SlotKind::Owning),
            ("deleteNode::root".to_owned(), SlotKind::Owning),
            ("newNode::temp".to_owned(), SlotKind::Owning),
            ("deleteNode::temp".to_owned(), SlotKind::Owning),
            ("deleteNode::temp_0".to_owned(), SlotKind::Owning),
            ("minValueNode::node".to_owned(), SlotKind::Ref),
            ("deleteNode::temp_1".to_owned(), SlotKind::Ref),
        ],
    );
}

/// Both frame locks, in one order: the crate-wide one every frame-state test
/// holds, then ownership-fields' (three of whose tests set the same global
/// model override under it alone).
fn frame_locks() -> (
    std::sync::MutexGuard<'static, ()>,
    std::sync::MutexGuard<'static, ()>,
) {
    let frame = super::test_model_override::frame_lock();
    let fields = super::decision::ownership_fields_native::field_form_override::LOCK
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    (frame, fields)
}

fn bst_emitted(name: &str, source: &str) -> super::wave6a_allocation_tests::Emitted {
    let _frame = frame_locks();
    bst_frame();
    let out = emitted(name, source);
    super::test_model_override::clear();
    out
}

/// The degradations of a run, by subject and reason key, sorted.
fn degraded(out: &super::wave6a_allocation_tests::Emitted) -> Vec<(String, String)> {
    let mut rows: Vec<(String, String)> = out
        .degradations
        .iter()
        .map(|d| (d.subject.clone(), d.reason.key().to_owned()))
        .collect();
    rows.sort();
    rows
}

/// **R579-4 — the recursive return certificate, six edits in one
/// transaction** (relay wave-6a/106). Under era-5c's frame bst's recursive
/// returns certify: `newNode` re-renders its literal with the delivered field
/// forms (R1), `insert` / `deleteNode` return their own re-seated formal
/// (R2, C1) and `deleteNode` the owners it moves out of a field (R3, C3), and
/// every store of a recursive result into the owned field is a plain move
/// (C2) — no `from_raw` and no `into_raw` left anywhere.
#[test]
fn w6a_r579_the_recursive_certificate_moves_bst_whole() {
    let out = bst_emitted("r579-bst", BST);
    record(
        "r579-bst",
        &format!(
            "{}\n{}",
            out.artifacts.return_certificate_receipts, out.source
        ),
    );
    let text = compact(&out.source);
    let receipts = &out.artifacts.return_certificate_receipts;
    let context = format!("{receipts}\n{}", out.source);
    assert_eq!(out.reverted, 0, "{context}");
    // R1: the producer stands, its literal spelling the delivered fields.
    assert!(
        text.contains("fnnewNode(mutitem:i32)->Box<node>") && text.contains("left:None,right:None"),
        "{context}"
    );
    // R2 + C1: the re-seated formal is the owner the callee hands back.
    assert!(
        text.contains("fninsert(mutnode:Option<Box<node>>,mutkey:i32)->Option<Box<node>>"),
        "{context}"
    );
    assert!(text.contains("returnSome(newNode(key));"), "{context}");
    assert!(text.contains("returnnode;"), "{context}");
    // R2 + R3 + C3: the formal on two paths, the moved-out owners on two.
    assert!(
        text.contains("fndeleteNode(mutroot:Option<Box<node>>,mutkey:i32)->Option<Box<node>>"),
        "{context}"
    );
    assert!(
        text.contains("returnroot;")
            && text.contains("returntemp;")
            && text.contains("returntemp_0;"),
        "{context}"
    );
    // C2: the five stores are plain moves.
    assert_eq!(
        text.matches("=insert(").count() + text.matches("=deleteNode(").count(),
        5,
        "{context}"
    );
    assert!(
        !text.contains("from_raw") && !text.contains("into_raw"),
        "{context}"
    );
    // The control: the borrowed-child return stays uncertified and held.
    assert!(
        text.contains("fnminValueNode(mutnode:*mutnode)->*mutnode"),
        "{context}"
    );
    assert!(
        receipts.contains(
            "minValueNode\theld\treturn-certificate-return-locals:minValueNode:not-a-subject"
        ),
        "{context}"
    );
    // Nothing else moves: the two rows batch 39 holds stay held.
    assert_eq!(
        degraded(&out),
        vec![
            (
                "deleteNode::temp_1".to_owned(),
                "return-not-adapted".to_owned()
            ),
            (
                "minValueNode::node".to_owned(),
                "opt-use-unsupported".to_owned()
            ),
        ],
        "{context}"
    );
}

/// Control (R579-4, `fn_values` unchanged): `insert`'s address is taken, so
/// the re-seat refuses its formal (`box-param-indirect-callers`) and R2 has
/// no owner to read — `insert` keeps its raw return and its stores their
/// `from_raw`, exactly as before; `deleteNode` still certifies.
#[test]
fn w6a_r579_an_address_taken_recursion_is_not_certified() {
    let source = BST.replace(
        "#[no_mangle]\npub unsafe extern \"C\" fn minValueNode",
        "pub unsafe fn pick() -> unsafe extern \"C\" fn(*mut node, i32) -> *mut node { insert }\n#[no_mangle]\npub unsafe extern \"C\" fn minValueNode",
    );
    assert_ne!(source, BST, "the control must take insert's address");
    let out = bst_emitted("r579-bst-fn-value", &source);
    let text = compact(&out.source);
    let receipts = &out.artifacts.return_certificate_receipts;
    let context = format!("{receipts}\n{}", out.source);
    assert!(!receipts.contains("callee=insert output"), "{context}");
    assert!(
        text.contains("fninsert(mutnode:*mutnode,mutkey:i32)->*mutnode")
            || text.contains("fninsert(mutnode:Option<Box<node>>,mutkey:i32)->*mutnode"),
        "{context}"
    );
    assert!(
        receipts.contains("return-certificate callee=deleteNode output=Option<Box<node>>"),
        "{context}"
    );
}

/// Control (R579-4 R2's fallback): the same program with the fields NOT
/// owned. The re-seat plans the formals at derive time, but no transaction
/// delivers `left` / `right`, so the re-seats withdraw after the fields
/// finalize; the certificates re-derive without them and `insert` is passed
/// over, `deleteNode` held, exactly as before R2.
#[test]
fn w6a_r579_an_undelivered_field_unseats_the_owner_parameter() {
    use crate::analyses::borrow_ownership::SlotKind;
    let _frame = frame_locks();
    super::test_model_override::set(
        "w6a-r578-bst-frame",
        Vec::new(),
        vec![
            ("insert::node".to_owned(), SlotKind::Owning),
            ("deleteNode::root".to_owned(), SlotKind::Owning),
            ("newNode::temp".to_owned(), SlotKind::Owning),
        ],
    );
    let out = emitted("r579-bst-fields-raw", BST);
    super::test_model_override::clear();
    let text = compact(&out.source);
    let receipts = &out.artifacts.return_certificate_receipts;
    let context = format!("{receipts}\n{}", out.source);
    assert!(!receipts.contains("source=owner-parameter"), "{context}");
    assert!(
        receipts.contains("chain-through:insert:returns-parameter-or-certified"),
        "{context}"
    );
    assert!(
        receipts.contains("return-certificate-return-locals:deleteNode:2"),
        "{context}"
    );
    assert!(!text.contains("->Option<Box<node>>"), "{context}");
    assert_eq!(out.reverted, 0, "{context}");
}

/// **R583-8 wall 3 — a moved-out owner alone.** R579-4's R3 lifted
/// `return-locals:2` only beside a primary owner, and this fixture was its
/// scope control (`detachLeft` kept `return-certificate-allocation:…:
/// construction`). Wall 3 admits the lone owner — the shape of avl's
/// rotations: `detachLeft`'s one returned local is a load moved out of an
/// owned field, adopted and confirmed by ownership-fields' certified return,
/// so the callee certifies `Option<Box<node>>` and returns the owner as itself.
#[test]
fn w6a_r583_a_lone_moved_out_owner_is_certified() {
    let source = BST.replace(
        "#[no_mangle]\npub unsafe extern \"C\" fn minValueNode",
        "#[no_mangle]\npub unsafe extern \"C\" fn detachLeft(mut root: *mut node) -> *mut node {\n    let mut t = (*root).left;\n    (*root).left = 0 as *mut node;\n    return t;\n}\n#[no_mangle]\npub unsafe extern \"C\" fn minValueNode",
    );
    assert_ne!(source, BST, "the control must add the detaching callee");
    use crate::analyses::borrow_ownership::SlotKind;
    let _frame = frame_locks();
    super::test_model_override::set(
        "w6a-r578-bst-frame",
        vec![
            ("node".to_owned(), 1, SlotKind::Owning),
            ("node".to_owned(), 2, SlotKind::Owning),
        ],
        vec![
            ("insert::node".to_owned(), SlotKind::Owning),
            ("deleteNode::root".to_owned(), SlotKind::Owning),
            ("newNode::temp".to_owned(), SlotKind::Owning),
            ("deleteNode::temp".to_owned(), SlotKind::Owning),
            ("deleteNode::temp_0".to_owned(), SlotKind::Owning),
            ("minValueNode::node".to_owned(), SlotKind::Ref),
            ("deleteNode::temp_1".to_owned(), SlotKind::Ref),
            ("detachLeft::t".to_owned(), SlotKind::Owning),
        ],
    );
    let out = emitted("r579-bst-detach", &source);
    super::test_model_override::clear();
    let receipts = &out.artifacts.return_certificate_receipts;
    let context = format!("{receipts}\n{}", out.source);
    let text = compact(&out.source);
    assert_eq!(out.reverted, 0, "{context}");
    assert!(
        receipts.contains("return-certificate-adopted owners=detachLeft::t"),
        "{context}"
    );
    assert!(
        text.contains("fndetachLeft(mutroot:&mutnode)->Option<Box<node>>")
            && text.contains("(*root).left.take();")
            && text.contains("returnt;"),
        "{context}"
    );
    // The rest of the transaction is unmoved by the extra callee.
    assert!(
        receipts.contains("return-certificate callee=deleteNode output=Option<Box<node>>"),
        "{context}"
    );
}

/// **R583-7 (wave-6f 071's residual)** — the certified stores a field
/// transaction moves follow the CURRENT delivery. After the stage that
/// delivered `left` / `right`, `insert`'s two stores are field moves and its
/// raw-place transfers are gone; if a later stage iteration no longer
/// delivers the fields, the transfers come back and the moves go — they are
/// recomputed from `store_fields`, not accumulated.
#[test]
fn w6a_r583_field_moves_follow_the_current_delivery() {
    let _frame = frame_locks();
    bst_frame();
    let observed = ::utils::compilation::run_compiler_on_str(BST, |tcx| {
        let (table, _ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("decide");
        let subjects: Vec<_> = table.entries.iter().map(|(s, _)| s.clone()).collect();
        let mut certificates = table.return_certificates.clone();
        let state = |certificates: &super::decision::return_certificate::Certificates| {
            let insert = certificates
                .callees
                .values()
                .find(|c| c.callee_path == "insert")
                .expect("insert is certified");
            (
                insert.field_moves.len(),
                insert
                    .site_edits
                    .iter()
                    .filter(|(_, edit)| edit.receipt == "return-certificate-store-transfer")
                    .count(),
            )
        };
        let delivered = state(&certificates);
        let changed = super::decision::return_certificate::withdraw_delivered_owned_fields(
            &mut certificates,
            tcx,
            &subjects,
            &|_, _| false,
            &|_, _| None,
        );
        (delivered, changed, state(&certificates))
    })
    .expect("fixture compiles");
    super::test_model_override::clear();
    assert_eq!(observed, ((2, 0), true, (0, 2)));
}

/// wave-6f 072's shape (their `wave6f_fixture_certified_store.rs`, my copy):
/// `make_item` certifies `Box<item>`, `attach`'s ONLY site of the owned field
/// `holder.item` is the certified-call store, and `make_item` owns no site
/// of the field.
const CERTIFIED_STORE: &str = r#"// w6a-r584-certified-store-frame
#![allow(dead_code, unused_mut, unused_unsafe, non_camel_case_types, unused_variables, unused_assignments)]
extern "C" {
    fn malloc(_: u64) -> *mut ::std::ffi::c_void;
    fn free(_: *mut ::std::ffi::c_void);
}
#[repr(C)]
pub struct item {
    pub v: i32,
}
#[repr(C)]
pub struct holder {
    pub item: *mut item,
}
pub unsafe extern "C" fn make_item(mut v: i32) -> *mut item {
    let mut p: *mut item = malloc(::std::mem::size_of::<item>() as u64) as *mut item;
    (*p).v = v;
    return p;
}
pub unsafe extern "C" fn attach(mut h: *mut holder, mut v: i32) {
    (*h).item = make_item(v);
}
pub unsafe extern "C" fn value(mut h: *mut holder) -> i32 {
    return (*(*h).item).v;
}
pub unsafe extern "C" fn release(mut h: *mut holder) {
    free((*h).item as *mut ::std::ffi::c_void);
    (*h).item = 0 as *mut item;
}
"#;

/// **R584-4 (wave-6f 072 §4)** — a certificate reverts WHOLE in the round
/// one of its owners reverts. `attach` (the certified storer) is reverted for
/// a reason of its own; `Certificates::owners` then withholds the
/// certificate's signature, and its callee's LOCAL plan (`make_item::p` →
/// `Box::new(..)`) must go in the same round — the certificate's owner set is
/// closed in the round's withheld set, as a field transaction's is. Before,
/// round 1 shipped `return p;` as a `Box<item>` against the withheld
/// `*mut item` (E0308) and the loop converged one revert later.
#[test]
fn w6a_r584_a_certificate_reverts_whole_in_its_owners_round() {
    use crate::analyses::borrow_ownership::SlotKind;
    let _frame = frame_locks();
    super::test_model_override::set(
        "w6a-r584-certified-store-frame",
        vec![("holder".to_owned(), 0, SlotKind::Owning)],
        Vec::new(),
    );
    let dir = std::env::temp_dir().join(format!("w6a-r584-first-failing-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    // SAFETY: the frame locks serialize the witnesses that set these.
    unsafe {
        std::env::set_var("CRAT_W6F_FORCE_REVERT", "attach");
        std::env::set_var("CRAT_RAW_BOUNDARY_FIRST_FAILING_VERIFY_TREE", &dir);
    }
    let out = emitted("r584-certified-store", CERTIFIED_STORE);
    unsafe {
        std::env::remove_var("CRAT_W6F_FORCE_REVERT");
        std::env::remove_var("CRAT_RAW_BOUNDARY_FIRST_FAILING_VERIFY_TREE");
    }
    super::test_model_override::clear();
    let _ = std::fs::remove_dir_all(&dir);
    let text = compact(&out.source);
    assert_eq!(
        out.artifacts.first_failing_verify_tree, "",
        "no verify round fails: the callee reverts with its storer in round 1\n{}",
        out.source
    );
    assert_eq!(out.reverted, 2, "attach and make_item\n{}", out.source);
    assert!(
        text.contains("pubitem:*mutitem,")
            && text.contains("fnmake_item(mutv:i32)->*mutitem{")
            && text.contains("(*h).item=make_item(v);"),
        "{}",
        out.source
    );
}

/// avl, reduced from the corpus in its substrate form (the `ref mut fresh`
/// stores already plain): `newNode`, the two rotations, `insert`.
const AVL: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, non_camel_case_types, non_snake_case)]
// w6a-r579-avl-frame
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}
#[repr(C)]
pub struct Node {
    pub key: i32,
    pub left: *mut Node,
    pub right: *mut Node,
    pub height: i32,
}
#[no_mangle]
pub unsafe extern "C" fn height(mut N: *mut Node) -> i32 {
    if N.is_null() { return 0 as i32; }
    return (*N).height;
}
#[no_mangle]
pub unsafe extern "C" fn max(mut a: i32, mut b: i32) -> i32 {
    return if a > b { a } else { b };
}
#[no_mangle]
pub unsafe extern "C" fn newNode(mut key: i32) -> *mut Node {
    let mut node = malloc(::std::mem::size_of::<Node>()) as *mut Node;
    (*node).key = key;
    (*node).left = 0 as *mut Node;
    (*node).right = 0 as *mut Node;
    (*node).height = 1 as i32;
    return node;
}
#[no_mangle]
pub unsafe extern "C" fn rightRotate(mut y: *mut Node) -> *mut Node {
    let mut x = (*y).left;
    let mut T2 = (*x).right;
    (*y).left = T2;
    (*y).height = max(height((*y).left), height((*y).right)) + 1 as i32;
    (*x).right = y;
    (*x).height = max(height((*x).left), height((*x).right)) + 1 as i32;
    return x;
}
#[no_mangle]
pub unsafe extern "C" fn leftRotate(mut x: *mut Node) -> *mut Node {
    let mut y = (*x).right;
    let mut T2 = (*y).left;
    (*x).right = T2;
    (*x).height = max(height((*x).left), height((*x).right)) + 1 as i32;
    (*y).left = x;
    (*y).height = max(height((*y).left), height((*y).right)) + 1 as i32;
    return y;
}
#[no_mangle]
pub unsafe extern "C" fn getBalance(mut N: *mut Node) -> i32 {
    if N.is_null() { return 0 as i32; }
    return height((*N).left) - height((*N).right);
}
#[no_mangle]
pub unsafe extern "C" fn insert(mut node: *mut Node, mut key: i32) -> *mut Node {
    if node.is_null() { return newNode(key); }
    if key < (*node).key {
        (*node).left = insert((*node).left, key);
    } else if key > (*node).key {
        (*node).right = insert((*node).right, key);
    } else { return node }
    (*node).height = 1 as i32 + max(height((*node).left), height((*node).right));
    let mut balance = getBalance(node);
    if balance > 1 as i32 && key < (*(*node).left).key {
        return rightRotate(node);
    }
    if balance < -(1 as i32) && key > (*(*node).right).key {
        return leftRotate(node);
    }
    if balance > 1 as i32 && key > (*(*node).left).key {
        (*node).left = leftRotate((*node).left);
        return rightRotate(node);
    }
    if balance < -(1 as i32) && key < (*(*node).right).key {
        (*node).right = rightRotate((*node).right);
        return leftRotate(node);
    }
    return node;
}
"#;

/// era-5c's L01⁹ avl frame (report 067: avl's ten CROWN units Owning —
/// `Node::field1` / `field2`, `insert::node`, `newNode::node`, the rotations'
/// `x` / `y` / `T2`), the readers Ref.
fn avl_emitted(name: &str, source: &str) -> super::wave6a_allocation_tests::Emitted {
    let _frame = frame_locks();
    avl_frame();
    let out = emitted(name, source);
    super::test_model_override::clear();
    out
}

/// report 067's ten Owning units, the readers `Ref`. The caller holds the
/// frame locks.
fn avl_frame() {
    use crate::analyses::borrow_ownership::SlotKind;
    super::test_model_override::set(
        "w6a-r579-avl-frame",
        vec![
            ("Node".to_owned(), 1, SlotKind::Owning),
            ("Node".to_owned(), 2, SlotKind::Owning),
        ],
        vec![
            ("insert::node".to_owned(), SlotKind::Owning),
            ("newNode::node".to_owned(), SlotKind::Owning),
            ("rightRotate::y".to_owned(), SlotKind::Owning),
            ("rightRotate::x".to_owned(), SlotKind::Owning),
            ("rightRotate::T2".to_owned(), SlotKind::Owning),
            ("leftRotate::x".to_owned(), SlotKind::Owning),
            ("leftRotate::y".to_owned(), SlotKind::Owning),
            ("leftRotate::T2".to_owned(), SlotKind::Owning),
            ("height::N".to_owned(), SlotKind::Ref),
            ("getBalance::N".to_owned(), SlotKind::Ref),
        ],
    );
}

/// avl's round-1 tree: the first failing verify tree when a round fails,
/// else the emitted tree (no round failed). Every planned rendering is in it
/// either way, whatever a later round reverts.
fn avl_round1(name: &str, source: &str) -> (super::wave6a_allocation_tests::Emitted, String) {
    let dir = std::env::temp_dir().join(format!("w6a-r583-avl-{}-{name}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    // The locks FIRST: another frame witness brackets the same variable, and
    // setting it while waiting for them lets that witness's removal land
    // inside this emission (measured at 4 threads: no capture).
    let _frame = frame_locks();
    avl_frame();
    // SAFETY: the frame locks serialize every writer of this variable.
    unsafe { std::env::set_var("CRAT_RAW_BOUNDARY_FIRST_FAILING_VERIFY_TREE", &dir) };
    let out = emitted(name, source);
    unsafe { std::env::remove_var("CRAT_RAW_BOUNDARY_FIRST_FAILING_VERIFY_TREE") };
    super::test_model_override::clear();
    let _ = std::fs::remove_dir_all(&dir);
    let round1 = if out.artifacts.first_failing_verify_tree.is_empty() {
        out.source.clone()
    } else {
        out.artifacts.first_failing_verify_tree.clone()
    };
    (out, round1)
}

/// **R583-8 — avl on L01⁹, walls 1–3.** Under report 067's ten Owning units
/// the recursive certificate reaches avl: `insert` hands its re-seated formal
/// back or ON (`return rightRotate(node)`, wall 1), the rotations consume a
/// formal from `insert` (the re-seated `node`, wall 2(a)) or an owned child
/// (`leftRotate((*node).left)`, 2(b)), store it into an owned field (2(c)),
/// and return the owner they move out of a field alone (wall 3). The round-1
/// tree carries it whole: every signature certified, every store a plain
/// move, the lend of the optional owner its own view, no `from_raw` /
/// `into_raw`. With ownership-fields' moved-load projection on the line
/// (`eb24609de`, report 112 §1) no round fails, so it is the emitted tree and
/// nothing reverts (R586-3).
#[test]
fn w6a_r583_the_recursive_certificate_moves_avl_whole() {
    let (out, round1) = avl_round1("r583-avl", AVL);
    record(
        "r583-avl",
        &format!("{}\n{}", out.artifacts.return_certificate_receipts, round1),
    );
    let text = compact(&round1);
    let receipts = &out.artifacts.return_certificate_receipts;
    let chains = &out.artifacts.box_param_receipts;
    let context = format!("{receipts}\n{chains}\n{round1}");
    assert!(
        receipts.contains(
            "return-certificate callee=insert output=Option<Box<Node>> source=owner-parameter"
        ) && receipts.contains("return-certificate-adopted owners=rightRotate::x")
            && receipts.contains("return-certificate-adopted owners=leftRotate::y"),
        "{context}"
    );
    assert!(
        chains.contains("box-param-reseat callee=insert index=0 fields=2 transfers-at-return=4")
            && chains.contains("box-param-chain callee=rightRotate index=0 sink=store")
            && chains.contains("box-param-chain callee=leftRotate index=0 sink=store"),
        "{context}"
    );
    assert!(
        text.contains("fnnewNode(mutkey:i32)->Box<Node>"),
        "{context}"
    );
    assert!(
        text.contains("fnrightRotate(muty:Option<Box<Node>>)->Option<Box<Node>>")
            && text.contains("fnleftRotate(mutx:Option<Box<Node>>)->Option<Box<Node>>"),
        "{context}"
    );
    assert!(
        text.contains("fninsert(mutnode:Option<Box<Node>>,mutkey:i32)->Option<Box<Node>>"),
        "{context}"
    );
    assert!(
        text.contains("returnrightRotate(node);")
            && text.contains("returnleftRotate(node);")
            && text.contains("returnSome(newNode(key));")
            && text.contains("getBalance(node.as_deref())")
            && text.contains("=leftRotate((*node.as_deref_mut().unwrap()).left.take());")
            && text.contains("(*x.as_deref_mut().unwrap()).right=y;")
            && text.contains("(*y.as_deref_mut().unwrap()).left=x;"),
        "{context}"
    );
    assert!(
        !text.contains("from_raw") && !text.contains("into_raw"),
        "{context}"
    );
    assert!(
        out.artifacts.first_failing_verify_tree.is_empty(),
        "{context}"
    );
    assert_eq!(out.reverted, 0, "{context}");
    assert!(
        text.contains("publeft:Option<Box<Node>>,") && text.contains("pubright:Option<Box<Node>>,"),
        "{context}"
    );
}

/// The avl frame's holds on the Box-parameter family, one line per hold.
fn chain_holds(out: &super::wave6a_allocation_tests::Emitted) -> Vec<String> {
    out.artifacts
        .box_param_receipts
        .lines()
        .filter(|line| line.contains("\theld\t"))
        .map(str::to_owned)
        .collect()
}

/// Control (R583-8 walls 1 / 2(b)): a rotation whose owned child is handed
/// in and the result DISCARDED (`rightRotate((*node).right);`) would leave
/// the field `None` where C left it intact, so the chain refuses that
/// caller; the re-seat that hands `node` on at `return rightRotate(node)` then
/// has no chain to hand into and withdraws, and the chain that took the
/// re-seated `node` as its member withdraws with it.
#[test]
fn w6a_r583_a_discarded_child_hand_on_holds_the_hand_ons() {
    let source = AVL.replace(
        "    let mut balance = getBalance(node);\n",
        "    let mut balance = getBalance(node);\n    rightRotate((*node).right);\n",
    );
    assert_ne!(source, AVL, "the control must discard a rotation's result");
    let (out, _) = avl_round1("r583-avl-discarded", &source);
    let holds = chain_holds(&out);
    let context = format!("{holds:#?}\n{}", out.artifacts.box_param_receipts);
    assert!(
        holds.iter().any(|h| h.starts_with("rightRotate::y")
            && h.contains("box-param-caller-retains:insert:not-a-local")),
        "{context}"
    );
    assert!(
        holds.iter().any(|h| h.starts_with("insert::node")
            && h.contains("box-param-reseat-transfer-unplanned:insert")),
        "{context}"
    );
    assert!(
        holds.iter().any(|h| h.starts_with("leftRotate::x")
            && h.contains("box-param-chain-member-withdrawn:leftRotate")),
        "{context}"
    );
}

/// Control (R583-8 wall 1): a hand-on that is NOT the `return` operand
/// (`let r = rightRotate(node); return r;`) leaves a path on which the owner
/// has moved, so the re-seat still refuses it (`box-param-reseat-escapes`).
#[test]
fn w6a_r583_a_hand_on_off_the_return_is_not_a_reseat() {
    let source = AVL.replacen(
        "        return rightRotate(node);\n    }\n    if balance < -(1 as i32) && key > (*(*node).right).key {",
        "        let mut r = rightRotate(node);\n        return r;\n    }\n    if balance < -(1 as i32) && key > (*(*node).right).key {",
        1,
    );
    assert_ne!(source, AVL, "the control must bind the rotation's result");
    let (out, _) = avl_round1("r583-avl-bound", &source);
    let holds = chain_holds(&out);
    assert!(
        holds.iter().any(|h| h.starts_with("insert::node")
            && h.contains("box-param-reseat-escapes:insert")),
        "{holds:#?}\n{}",
        out.artifacts.box_param_receipts
    );
}

/// Control (R583-8 wall 2(c)): an optional formal whose store goes into a
/// field the model does NOT own (`Node.right` not `Owning` here) is a raw
/// transfer, not the field's move, so the optional chain refuses its sink.
/// `rightRotate`'s only member is the re-seated `node` (optional).
#[test]
fn w6a_r583_an_optional_formal_stored_into_a_raw_field_holds() {
    use crate::analyses::borrow_ownership::SlotKind;
    let _frame = frame_locks();
    super::test_model_override::set(
        "w6a-r579-avl-frame",
        vec![("Node".to_owned(), 1, SlotKind::Owning)],
        vec![
            ("insert::node".to_owned(), SlotKind::Owning),
            ("newNode::node".to_owned(), SlotKind::Owning),
            ("rightRotate::y".to_owned(), SlotKind::Owning),
            ("rightRotate::x".to_owned(), SlotKind::Owning),
            ("rightRotate::T2".to_owned(), SlotKind::Owning),
            ("leftRotate::x".to_owned(), SlotKind::Owning),
            ("leftRotate::y".to_owned(), SlotKind::Owning),
            ("leftRotate::T2".to_owned(), SlotKind::Owning),
            ("height::N".to_owned(), SlotKind::Ref),
            ("getBalance::N".to_owned(), SlotKind::Ref),
        ],
    );
    // Only the re-seated `node` is a member (the double rotations, whose
    // owned-child members would refuse first, are cut).
    let start = AVL
        .find("    if balance > 1 as i32 && key > (*(*node).left).key {")
        .expect("double rotations");
    let end = AVL[start..].find("    return node;\n}").expect("the tail") + start;
    let source = format!("{}{}", &AVL[..start], &AVL[end..]);
    let out = emitted("r583-avl-raw-right", &source);
    super::test_model_override::clear();
    let holds = chain_holds(&out);
    assert!(
        holds.iter().any(|h| h.starts_with("rightRotate::y")
            && h.contains("box-param-shape:rightRotate:optional-owner-sink")),
        "{holds:#?}\n{}",
        out.artifacts.box_param_receipts
    );
}

/// Control (R583-8 wall 2): a chain's owned field that no transaction
/// delivers (`Node.left` is indexed below, so its transaction holds) withdraws
/// the chain after the fields finalize, with its own hold.
#[test]
fn w6a_r583_an_undelivered_chain_field_withdraws_the_chain() {
    let source = format!(
        "{AVL}#[no_mangle]\npub unsafe extern \"C\" fn peekSecond(mut n: *mut Node) -> i32 {{\n    return (*(*n).left.offset(1 as isize)).key;\n}}\n"
    );
    let (out, _) = avl_round1("r583-avl-left-held", &source);
    let holds = chain_holds(&out);
    assert!(
        holds.iter().any(|h| h.starts_with("leftRotate::x")
            && h.contains("box-param-chain-field-not-delivered:leftRotate")),
        "{holds:#?}\n{}",
        out.artifacts.box_param_receipts
    );
}

/// lil's `alloc_value` and `lil_new`, reduced: a `calloc(1, size_of::<T>())`
/// block filled in place (field stores, one reading another, a nested
/// allocation freed with the owner on its own failure path, a lend before the
/// return) and returned; each with a receiver that frees it.
const FILLED_IN_PLACE: &str = r#"
// w6a-r615-filled-in-place
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, unused_assignments, non_camel_case_types, non_snake_case)]
extern "C" {
    fn calloc(n: usize, size: usize) -> *mut core::ffi::c_void;
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
#[repr(C)]
pub struct value {
    pub l: usize,
    pub d: *mut u8,
}
#[repr(C)]
pub struct env {
    pub depth: i32,
}
#[repr(C)]
pub struct interp {
    pub env: *mut env,
    pub rootenv: *mut env,
    pub callbacks: [Option<unsafe extern "C" fn(*mut interp) -> i32>; 4],
    pub count: usize,
}
unsafe extern "C" fn alloc_value(mut n: usize) -> *mut value {
    let mut val = calloc(1 as i32 as usize, ::core::mem::size_of::<value>()) as *mut value;
    if val.is_null() {
        return 0 as *mut value;
    }
    if n > 0 as usize {
        (*val).l = n;
        (*val).d = malloc(n.wrapping_add(1 as usize)) as *mut u8;
        if ((*val).d).is_null() {
            free(val as *mut core::ffi::c_void);
            return 0 as *mut value;
        }
    } else {
        (*val).l = 0 as usize;
        (*val).d = 0 as *mut u8;
    }
    return val;
}
unsafe extern "C" fn short_value(mut n: usize) -> *mut value {
    let mut val = calloc(1 as i32 as usize, ::core::mem::size_of::<value>()) as *mut value;
    if val.is_null() {
        return 0 as *mut value;
    }
    if n > 8 as usize {
        free(val as *mut core::ffi::c_void);
        return 0 as *mut value;
    }
    if n == 0 as usize {
        return 0 as *mut value;
    }
    (*val).l = n;
    return val;
}
unsafe extern "C" fn use_short(mut n: usize) -> usize {
    let mut v = short_value(n);
    if v.is_null() {
        return 0 as usize;
    }
    let mut l = (*v).l;
    free(v as *mut core::ffi::c_void);
    return l;
}
unsafe extern "C" fn use_value(mut n: usize) -> usize {
    let mut v = alloc_value(n);
    if v.is_null() {
        return 0 as usize;
    }
    let mut l = (*v).l;
    free((*v).d as *mut core::ffi::c_void);
    free(v as *mut core::ffi::c_void);
    return l;
}
unsafe extern "C" fn alloc_env() -> *mut env {
    let mut e = malloc(::core::mem::size_of::<env>()) as *mut env;
    (*e).depth = 0 as i32;
    return e;
}
unsafe extern "C" fn register_all(mut it: *mut interp) {
    (*it).count = 4 as usize;
}
#[no_mangle]
pub unsafe extern "C" fn lil_new() -> *mut interp {
    let mut lil = calloc(1 as i32 as usize, ::core::mem::size_of::<interp>()) as *mut interp;
    (*lil).env = alloc_env();
    (*lil).rootenv = (*lil).env;
    register_all(lil);
    return lil;
}
unsafe extern "C" fn two_values() -> *mut value {
    let mut pair = calloc(2 as i32 as usize, ::core::mem::size_of::<value>()) as *mut value;
    (*pair).l = 1 as usize;
    return pair;
}
unsafe extern "C" fn env_sized_value() -> *mut value {
    let mut small = calloc(1 as i32 as usize, ::core::mem::size_of::<env>()) as *mut value;
    (*small).l = 1 as usize;
    return small;
}
unsafe extern "C" fn take_two() -> usize {
    let mut p = two_values();
    let mut q = env_sized_value();
    let mut n = (*p).l.wrapping_add((*q).l);
    free(p as *mut core::ffi::c_void);
    free(q as *mut core::ffi::c_void);
    return n;
}
unsafe extern "C" fn repl() -> usize {
    let mut lil = lil_new();
    let mut count = (*lil).count;
    free((*lil).env as *mut core::ffi::c_void);
    free(lil as *mut core::ffi::c_void);
    return count;
}
"#;

fn filled_in_place_frame() {
    use crate::analyses::borrow_ownership::SlotKind;
    super::test_model_override::set(
        "w6a-r615-filled-in-place",
        vec![
            ("value".to_owned(), 1, SlotKind::Raw),
            ("interp".to_owned(), 0, SlotKind::Raw),
            ("interp".to_owned(), 1, SlotKind::Raw),
        ],
        vec![
            ("alloc_value::val".to_owned(), SlotKind::Owning),
            ("lil_new::lil".to_owned(), SlotKind::Owning),
            ("use_value::v".to_owned(), SlotKind::Owning),
            ("repl::lil".to_owned(), SlotKind::Owning),
            ("short_value::val".to_owned(), SlotKind::Owning),
            ("use_short::v".to_owned(), SlotKind::Owning),
            ("two_values::pair".to_owned(), SlotKind::Owning),
            ("env_sized_value::small".to_owned(), SlotKind::Owning),
            ("take_two::p".to_owned(), SlotKind::Owning),
            ("take_two::q".to_owned(), SlotKind::Owning),
        ],
    );
}

fn filled_in_place_emitted(name: &str) -> super::wave6a_allocation_tests::Emitted {
    let _frame = frame_locks();
    filled_in_place_frame();
    let out = emitted(name, FILLED_IN_PLACE);
    super::test_model_override::clear();
    out
}

/// **R615-4 (1)** — a contract allocation FILLED IN PLACE is a certificate
/// source: `calloc(1, size_of::<T>())` is one zero-filled `T`, so the owner is
/// `Box::from_raw(..)` around the allocation itself, its fields written
/// through the Box. Before, `alloc_value` held `…:shape` (the literal path
/// takes `malloc` only) and `lil_new` `struct-literal:ConstructorShape` (no
/// literal spells a callback array).
#[test]
fn w6a_r615_a_block_filled_in_place_is_a_certificate_source() {
    let out = filled_in_place_emitted("r615-filled");
    let receipts = &out.artifacts.return_certificate_receipts;
    let text = compact(&out.source);
    let context = format!("{receipts}\n{:#?}\n{}", out.degradations, out.source);
    for callee in ["alloc_value", "lil_new"] {
        assert!(
            receipts.contains(&format!("return-certificate callee={callee} "))
                && receipts.contains("source=filled-in-place"),
            "{callee}\n{context}"
        );
    }
    assert!(
        text.contains("letmutval:Box<crate::value>=::std::boxed::Box::from_raw(calloc("),
        "{context}"
    );
    assert!(
        text.contains("letmutlil:Box<crate::interp>=::std::boxed::Box::from_raw(calloc("),
        "{context}"
    );
    assert!(
        !text.contains("into_raw(val") && !text.contains("into_raw(lil"),
        "{context}"
    );
    for receiver in ["use_value::v", "repl::lil"] {
        assert_eq!(
            reason_of(&out.degradations, receiver),
            None,
            "{receiver}\n{context}"
        );
    }
}

/// Controls: a block of TWO elements (`calloc(2, ..)`) and a block measured
/// by ANOTHER type (`calloc(1, size_of::<env>()) as *mut value`, smaller than
/// a `value`) are not one zero-filled `T`, and keep their holds.
#[test]
fn w6a_r615_two_elements_or_another_types_size_keep_their_holds() {
    let out = filled_in_place_emitted("r615-filled-controls");
    let receipts = &out.artifacts.return_certificate_receipts;
    for owner in ["two_values::pair", "env_sized_value::small"] {
        assert!(
            receipts.lines().any(|line| line.starts_with(owner)
                && line.contains("\theld\treturn-certificate-allocation:")
                && line.ends_with(":shape")),
            "{owner}\n{receipts}"
        );
    }
    assert!(
        !compact(&out.source).contains("from_raw(calloc(2"),
        "{}",
        out.source
    );
}

/// bst's `newNode` allocated by `calloc(1, size_of::<node>())`, under
/// era-5c's frame, where the node's two fields are delivered: a zero-filled
/// block is a `node` only while its fields keep a zero-valid form, so the
/// filled-in-place certificate withdraws (`struct-field:..:owned-field`).
#[test]
fn w6a_r615_a_delivered_field_withdraws_the_filled_in_place_certificate() {
    let source = BST.replace(
        "malloc(::std::mem::size_of::<node>()) as *mut node",
        "calloc(1 as i32 as usize, ::std::mem::size_of::<node>()) as *mut node",
    );
    let source = source.replace(
        "    fn malloc(size: usize) -> *mut core::ffi::c_void;",
        "    fn malloc(size: usize) -> *mut core::ffi::c_void;\n    fn calloc(n: usize, size: usize) -> *mut core::ffi::c_void;",
    );
    let out = bst_emitted("r615-bst-calloc", &source);
    let receipts = &out.artifacts.return_certificate_receipts;
    assert!(
        receipts.contains("return-certificate-struct-field:newNode:owned-field"),
        "{receipts}\n{}",
        out.source
    );
    assert!(
        !compact(&out.source).contains("Box::from_raw(calloc("),
        "{}",
        out.source
    );
}

/// The watched set reaches every field a zero-filled block holds BY VALUE:
/// its own, a nested struct's, and an array element struct's; a pointer's
/// target is not held by value.
#[test]
fn w6a_r615_the_watched_fields_are_every_field_held_by_value() {
    let src = r#"
#[repr(C)] pub struct link { pub next: *mut item, pub tag: i32 }
#[repr(C)] pub struct item { pub key: i32, pub inner: link, pub pair: [link; 2], pub far: *mut link }
pub fn keep(_: item) {}
"#;
    ::utils::compilation::run_compiler_on_str(src, |tcx| {
        let named = |name: &str| {
            tcx.hir_crate_items(())
                .definitions()
                .find(|did| {
                    tcx.opt_item_name(did.to_def_id())
                        .is_some_and(|n| n.as_str() == name)
                })
                .expect(name)
        };
        let (item, link) = (named("item"), named("link"));
        let ty = tcx.type_of(item.to_def_id()).instantiate_identity();
        let mut fields =
            super::decision::return_certificate::fields_held_by_value_for_test(tcx, ty);
        fields.sort_by_key(|(did, index)| (tcx.item_name(did.to_def_id()).to_string(), *index));
        assert_eq!(
            fields,
            vec![
                (item, 0),
                (item, 1),
                (item, 2),
                (item, 3),
                (link, 0),
                (link, 1)
            ]
        );
    })
    .unwrap();
}

/// The watch reaches INTO a struct held by value: a zero-filled `holder`
/// carries a whole `node`, whose delivered fields (era-5c's bst frame) make
/// the zero a `node` no longer is — withdrawn, where the model-Owning fields
/// of `holder` itself (none) would have watched nothing.
#[test]
fn w6a_r615_a_field_delivered_inside_a_by_value_struct_withdraws() {
    use crate::analyses::borrow_ownership::SlotKind;
    let source = BST.replace(
        "    fn malloc(size: usize) -> *mut core::ffi::c_void;",
        "    fn malloc(size: usize) -> *mut core::ffi::c_void;\n    fn calloc(n: usize, size: usize) -> *mut core::ffi::c_void;",
    ) + r#"
#[repr(C)]
pub struct holder {
    pub n: node,
    pub count: i32,
}
#[no_mangle]
pub unsafe extern "C" fn newHolder() -> *mut holder {
    let mut h = calloc(1 as i32 as usize, ::std::mem::size_of::<holder>()) as *mut holder;
    (*h).count = 1 as i32;
    return h;
}
"#;
    let _frame = frame_locks();
    super::test_model_override::set(
        "w6a-r578-bst-frame",
        vec![
            ("node".to_owned(), 1, SlotKind::Owning),
            ("node".to_owned(), 2, SlotKind::Owning),
        ],
        vec![
            ("insert::node".to_owned(), SlotKind::Owning),
            ("deleteNode::root".to_owned(), SlotKind::Owning),
            ("newNode::temp".to_owned(), SlotKind::Owning),
            ("deleteNode::temp".to_owned(), SlotKind::Owning),
            ("deleteNode::temp_0".to_owned(), SlotKind::Owning),
            ("minValueNode::node".to_owned(), SlotKind::Ref),
            ("deleteNode::temp_1".to_owned(), SlotKind::Ref),
            ("newHolder::h".to_owned(), SlotKind::Owning),
        ],
    );
    let out = emitted("r615-holder", &source);
    super::test_model_override::clear();
    let receipts = &out.artifacts.return_certificate_receipts;
    let context = format!("{receipts}\n{}", out.source);
    assert!(
        compact(&out.source).contains("publeft:Option<Box<node>>,"),
        "{context}"
    );
    assert!(
        receipts.contains("return-certificate-struct-field:newHolder:owned-field"),
        "{context}"
    );
}

/// **R619-5 (1)** — a null return right after the owner's C `free` in its
/// block (`free(val); return 0`) closes nothing: the free already dropped the
/// owner, so it takes no `waiver-drop(scope-exit)` receipt. A LIVE null
/// return (the generation still held, leaked by the input) keeps its receipt,
/// even when another branch frees before its own return.
#[test]
fn w6a_r619_a_null_return_after_the_free_is_not_an_implicit_close() {
    let out = filled_in_place_emitted("r619-receipts");
    let receipts = &out.artifacts.return_certificate_receipts;
    let scope_exits = |callee: &str| {
        receipts
            .lines()
            .filter(|line| {
                line.starts_with(&format!("{callee}\t")) && line.contains("waiver-drop(scope-exit)")
            })
            .count()
    };
    assert_eq!(scope_exits("alloc_value"), 0, "{receipts}");
    assert_eq!(scope_exits("short_value"), 1, "{receipts}");
}

/// lil's `lil_new` and its three receivers on lil's own shapes (relay
/// wave-6a/123, ownership-fields 081 wall 4b): the `lil_t` alias, `_lil_t`'s
/// 22 fields verbatim (the `[Option<fn>; 8]` callback array among them), the
/// `1 as c_int as c_ulong` count, the lend before the return; and the ONE
/// consumer every receiver ends in, `lil_free`, which tests its formal for
/// null before freeing it (`if lil.is_null() { return; }`).
const LIL_NEW: &str = r#"
// w6a-r623-lil-new
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, unused_assignments, non_camel_case_types, non_snake_case)]
extern "C" {
    fn calloc(_: u64, _: u64) -> *mut core::ffi::c_void;
    fn malloc(_: u64) -> *mut core::ffi::c_void;
    fn free(_: *mut core::ffi::c_void);
}
pub type size_t = u64;
#[repr(C)]
pub struct _lil_value_t {
    pub l: size_t,
    pub d: *mut i8,
}
pub type lil_value_t = *mut _lil_value_t;
#[repr(C)]
pub struct _lil_env_t {
    pub parent: *mut _lil_env_t,
    pub vars: size_t,
}
pub type lil_env_t = *mut _lil_env_t;
pub type lil_callback_proc_t = Option<unsafe extern "C" fn() -> ()>;
#[repr(C)]
pub struct _lil_t {
    pub code: *const i8,
    pub rootcode: *const i8,
    pub clen: size_t,
    pub head: size_t,
    pub ignoreeol: i32,
    pub cmd: *mut *mut i8,
    pub cmds: size_t,
    pub syscmds: size_t,
    pub catcher: *mut i8,
    pub in_catcher: i32,
    pub dollarprefix: *mut i8,
    pub env: lil_env_t,
    pub rootenv: lil_env_t,
    pub downenv: lil_env_t,
    pub empty: lil_value_t,
    pub error: i32,
    pub err_head: size_t,
    pub err_msg: *mut i8,
    pub callback: [lil_callback_proc_t; 8],
    pub parse_depth: size_t,
    pub data: *mut core::ffi::c_void,
}
pub type lil_t = *mut _lil_t;
unsafe extern "C" fn lil_alloc_env(mut parent: lil_env_t) -> lil_env_t {
    let mut env = calloc(1 as i32 as u64, ::std::mem::size_of::<_lil_env_t>() as u64) as lil_env_t;
    (*env).parent = parent;
    return env;
}
unsafe extern "C" fn lil_free_env(mut env: lil_env_t) {
    free(env as *mut core::ffi::c_void);
}
unsafe extern "C" fn register_stdcmds(mut lil: lil_t) {
    (*lil).cmds = 0 as size_t;
    (*lil).syscmds = (*lil).cmds;
}
#[no_mangle]
pub unsafe extern "C" fn lil_new() -> lil_t {
    let mut lil = calloc(
        1 as i32 as u64,
        ::std::mem::size_of::<_lil_t>() as u64,
    ) as lil_t;
    (*lil).env = lil_alloc_env(0 as lil_env_t);
    (*lil).rootenv = (*lil).env;
    register_stdcmds(lil);
    return lil;
}
#[no_mangle]
pub unsafe extern "C" fn lil_free(mut lil: lil_t) {
    if lil.is_null() {
        return;
    }
    free((*lil).err_msg as *mut core::ffi::c_void);
    while !((*lil).env).is_null() {
        let mut next = (*(*lil).env).parent;
        lil_free_env((*lil).env);
        (*lil).env = next;
    }
    free((*lil).dollarprefix as *mut core::ffi::c_void);
    free(lil as *mut core::ffi::c_void);
}
unsafe extern "C" fn repl() -> size_t {
    let mut lil = lil_new();
    let mut n = (*lil).cmds;
    lil_free(lil);
    return n;
}
unsafe extern "C" fn nonint() -> i32 {
    let mut lil = lil_new();
    let mut e = (*lil).error;
    lil_free(lil);
    return e;
}
unsafe extern "C" fn fnc_jaileval(mut lil: lil_t) -> size_t {
    let mut sublil = lil_new();
    let mut r = (*sublil).syscmds;
    lil_free(sublil);
    return r;
}
"#;

fn lil_new_emitted(name: &str, source: &str) -> super::wave6a_allocation_tests::Emitted {
    use crate::analyses::borrow_ownership::SlotKind;
    let _frame = frame_locks();
    super::test_model_override::set(
        "w6a-r623-lil-new",
        vec![
            ("_lil_t".to_owned(), 11, SlotKind::Raw),
            ("_lil_t".to_owned(), 12, SlotKind::Raw),
        ],
        vec![
            ("lil_new::lil".to_owned(), SlotKind::Owning),
            ("lil_free::lil".to_owned(), SlotKind::Owning),
            ("repl::lil".to_owned(), SlotKind::Owning),
            ("nonint::lil".to_owned(), SlotKind::Owning),
            ("fnc_jaileval::sublil".to_owned(), SlotKind::Owning),
            ("release::l".to_owned(), SlotKind::Owning),
            ("drop_one::lil".to_owned(), SlotKind::Owning),
        ],
    );
    let out = emitted(name, source);
    super::test_model_override::clear();
    out
}

/// `lil_free` spelled with the raw pointer instead of the `lil_t` alias.
fn lil_new_raw_consumer() -> String {
    let source = LIL_NEW.replace(
        "pub unsafe extern \"C\" fn lil_free(mut lil: lil_t)",
        "pub unsafe extern \"C\" fn lil_free(mut lil: *mut _lil_t)",
    );
    assert_ne!(source, LIL_NEW);
    source
}

fn lil_new_context(out: &super::wave6a_allocation_tests::Emitted) -> (String, String) {
    let receipts = format!(
        "{}\n{}",
        out.artifacts.return_certificate_receipts, out.artifacts.box_param_receipts
    );
    let context = format!(
        "{receipts}\nREVERTS\n{}\n{:#?}\n{}",
        out.artifacts.final_reverts, out.degradations, out.source
    );
    (receipts, context)
}

/// **Relay wave-6a/123 (R636-4).** `lil_new`'s own wall, the struct literal,
/// is `9479cf3fd`'s (a `calloc(1, size_of::<_lil_t>())` block filled in place
/// needs no literal). What held its three receivers is their one consumer:
/// `lil_free` tests its formal for null first, a use C1's collector had no
/// form for. A `Box` is never null, so the owner walk renders the test
/// `false`, and the receivers move into `lil_free`. Here `lil_free` is spelled
/// with the raw pointer; the corpus spelling is the next test.
#[test]
fn w6a_r623_lil_new_and_its_three_receivers_move_into_a_null_testing_lil_free() {
    let out = lil_new_emitted("r623-lil-new-raw", &lil_new_raw_consumer());
    let (receipts, context) = lil_new_context(&out);
    let text = compact(&out.source);
    assert!(
        receipts.contains("return-certificate callee=lil_new ")
            && receipts.contains("source=filled-in-place")
            && receipts.contains("receivers=3 [repl::lil,nonint::lil,fnc_jaileval::sublil]"),
        "{context}"
    );
    assert!(
        receipts.contains("box-param-chain callee=lil_free index=0 sink=free"),
        "{context}"
    );
    assert!(
        text.contains("letmutlil:Box<crate::_lil_t>=::std::boxed::Box::from_raw(calloc("),
        "{context}"
    );
    assert!(
        text.contains("fnlil_free(mutlil:Box<_lil_t>){iffalse{return;}"),
        "{context}"
    );
    assert!(text.contains("drop(lil);}"), "{context}");
    for subject in [
        "lil_new::lil",
        "lil_free::lil",
        "repl::lil",
        "nonint::lil",
        "fnc_jaileval::sublil",
    ] {
        assert_eq!(
            reason_of(&out.degradations, subject),
            None,
            "{subject}\n{context}"
        );
    }
    assert_eq!(out.reverted, 0, "{context}");
}

/// The corpus spelling: `lil_free(mut lil: lil_t)`. The surface has no pointee
/// span to put `Box<..>` on and no alias spelling for a Box, so the chain
/// holds typed (`box-param-alias-formal`), the certificate withdraws on the
/// transfer it cannot confirm, and nothing reverts — `lil_alloc_env`,
/// certified on its own, still delivers.
#[test]
fn w6a_r623_lils_alias_spelled_consumer_holds_typed_and_reverts_nothing() {
    let out = lil_new_emitted("r623-lil-new-alias", LIL_NEW);
    let (receipts, context) = lil_new_context(&out);
    assert!(
        receipts.contains("lil_free::lil\theld\tbox-param-alias-formal:lil_free"),
        "{context}"
    );
    // The receivers' transfer into `lil_free` is a consumer's now, so the
    // certificate asks the chain to confirm it, and withdraws when it cannot.
    assert!(
        receipts.contains(
            "lil_new::lil\theld\treturn-certificate-transfer-unconfirmed:lil_new:lil_free#0"
        ),
        "{context}"
    );
    assert!(
        reason_of(&out.degradations, "repl::lil").is_some(),
        "{context}"
    );
    assert!(
        receipts.contains("return-certificate callee=lil_alloc_env ")
            && !receipts.contains("return-certificate callee=lil_new "),
        "{context}"
    );
    assert!(
        !compact(&out.source).contains("from_mut(lil.as_mut())"),
        "{context}"
    );
    assert_eq!(out.reverted, 0, "{context}");
}

/// Relay 123's controls on the delivering spelling, one violation each: a
/// `malloc`'d `_lil_t` (no zero to discharge the literal with) and a `calloc`
/// measured by another type keep `lil_new` held; a consumer that lends its
/// formal away before the free is not a null-tested consumer (the walk admits
/// no lend), and neither is one that re-seats it (`lil = 0 as *mut _lil_t;`
/// — the certificate's walk passes an assignment TO its owner, which C1 does
/// not render; only a null test is what the rule admits), so the receivers
/// keep theirs. A field whose delivered form has no
/// zero is `w6a_r615_a_delivered_field_withdraws_the_filled_in_place_certificate`.
#[test]
fn w6a_r623_lil_new_controls_hold() {
    let raw = lil_new_raw_consumer();
    let calloc_head = "let mut lil = calloc(\n        1 as i32 as u64,\n        ::std::mem::size_of::<_lil_t>() as u64,\n    ) as lil_t;";
    assert!(raw.contains(calloc_head));
    let malloced = raw.replace(
        calloc_head,
        "let mut lil = malloc(::std::mem::size_of::<_lil_t>() as u64) as lil_t;",
    );
    let resized = raw.replace(
        "::std::mem::size_of::<_lil_t>() as u64,\n    ) as lil_t;",
        "::std::mem::size_of::<_lil_env_t>() as u64,\n    ) as lil_t;",
    );
    let lent = raw.replace(
        "    free((*lil).err_msg as *mut core::ffi::c_void);\n",
        "    keep(lil);\n    free((*lil).err_msg as *mut core::ffi::c_void);\n",
    ) + "static mut KEPT: *mut _lil_t = 0 as *mut _lil_t;\nunsafe extern \"C\" fn keep(mut p: *mut _lil_t) {\n    KEPT = p;\n}\n";
    let reseated = raw.replace(
        "    if lil.is_null() {\n        return;\n    }\n",
        "    if (*lil).error != 0 as i32 {\n        lil = 0 as *mut _lil_t;\n    }\n",
    );
    assert_ne!(reseated, raw);
    for (name, source, expected) in [
        ("r623-malloced", malloced, "lil_new::lil\theld\t"),
        ("r623-resized", resized, "lil_new::lil\theld\t"),
        (
            "r623-reseated",
            reseated,
            "lil_free::lil\theld\tbox-param-callee-use:lil_free:",
        ),
        (
            "r623-lent",
            lent,
            "lil_free::lil\theld\tbox-param-callee-use:lil_free:unsupported:lil",
        ),
    ] {
        let out = lil_new_emitted(name, &source);
        let (receipts, context) = lil_new_context(&out);
        assert!(receipts.contains(expected), "{name}\n{context}");
        assert!(
            !receipts.contains("box-param-chain callee=lil_free "),
            "{name}\n{context}"
        );
        assert!(
            reason_of(&out.degradations, "repl::lil").is_some(),
            "{name}\n{context}"
        );
    }
}

/// A formal that hands its owner on to `lil_free` (R450-8 rung 2's move on),
/// and a caller that hands it a fresh `lil_new` — `lil_new`'s ONLY receiver, so
/// its certificate stands on the chain through `release` alone.
const RELEASE: &str = r#"
unsafe extern "C" fn release(mut l: *mut _lil_t) {
    lil_free(l);
}
unsafe extern "C" fn drop_one() -> i32 {
    let mut lil = lil_new();
    let mut e = (*lil).error;
    release(lil);
    return e;
}
"#;

/// **R636-4, from the review of `ef7aa6579`: a hand-on stands with the
/// formal it hands into.** `release(l)`'s only sink is the move on into
/// `lil_free`, so it is planned as a `Box` formal on the consumer set's word.
/// Where `lil_free` then holds (its alias spelling), `release`'s `Box` would
/// meet a raw formal, bridged as a lend and freed twice; so the hand-on
/// withdraws with its transferee (`box-param-hand-on-unplanned`). Where
/// `lil_free` is planned, `release` delivers.
#[test]
fn w6a_r623_a_formal_handed_on_stands_with_the_formal_it_hands_into() {
    let base = &LIL_NEW[..LIL_NEW.find("unsafe extern \"C\" fn repl()").expect("repl")];
    let out = lil_new_emitted("r623-hand-on-held", &format!("{base}{RELEASE}"));
    let (receipts, context) = lil_new_context(&out);
    let text = compact(&out.source);
    assert!(
        receipts.contains("lil_free::lil\theld\tbox-param-alias-formal:lil_free"),
        "{context}"
    );
    assert!(
        receipts.contains("release::l\theld\tbox-param-hand-on-unplanned:release"),
        "{context}"
    );
    assert!(!text.contains("fnrelease(mutl:Box<"), "{context}");
    assert!(!text.contains(".as_mut())"), "{context}");
    assert_eq!(out.reverted, 0, "{context}");

    let raw = lil_new_raw_consumer();
    let raw_base = &raw[..raw.find("unsafe extern \"C\" fn repl()").expect("repl")];
    let out = lil_new_emitted("r623-hand-on-planned", &format!("{raw_base}{RELEASE}"));
    let (_, context) = lil_new_context(&out);
    let text = compact(&out.source);
    assert!(
        text.contains("fnrelease(mutl:Box<_lil_t>){lil_free(l);}"),
        "{context}"
    );
    for subject in ["release::l", "drop_one::lil", "lil_free::lil"] {
        assert_eq!(
            reason_of(&out.degradations, subject),
            None,
            "{subject}\n{context}"
        );
    }
    assert_eq!(out.reverted, 0, "{context}");
}
