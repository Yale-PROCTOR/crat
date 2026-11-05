//! wave-6a — allocation-rooted forms (seat addendum 400, R400-3).
//!
//! Rule **W6A-B1** (`decision/slice_local_construction.rs`): an unannotated
//! slice local is typed by its sealed constructor, so the dissolution's veto
//! keeps its `Slice` decision and the planner places no declaration splice;
//! a safe slice handed to a settled slice parameter is a zero-syntax pass.
//!
//! Corpus-derived fixtures: heman `transform_to_distance` + `edt` and
//! `transform_to_coordfield` + `edt_with_payload` (shape (b),
//! `slice-local-construction`), quadtree `quadtree_node_new` + `test_node`
//! (shape (a): a callee returning a fresh allocation — the frame read).

/// quadtree `src::src::node::quadtree_node_new` and `src::test::test_node`,
/// reduced: the struct keeps three pointer fields, the three predicate callees
/// keep their real bodies.
pub(super) const QUADTREE_NODE_NEW: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_camel_case_types)]
extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(ptr: *mut core::ffi::c_void);
}
#[repr(C)]
pub struct quadtree_node {
    pub ne: *mut quadtree_node,
    pub nw: *mut quadtree_node,
    pub point: *mut i32,
}
pub type quadtree_node_t = quadtree_node;
pub unsafe extern "C" fn quadtree_node_isleaf(mut node: *mut quadtree_node_t) -> i32 {
    return ((*node).point != 0 as *mut core::ffi::c_void as *mut i32) as i32;
}
pub unsafe extern "C" fn quadtree_node_isempty(mut node: *mut quadtree_node_t) -> i32 {
    return (((*node).nw).is_null() && ((*node).ne).is_null()
        && quadtree_node_isleaf(node) == 0) as i32;
}
pub unsafe extern "C" fn quadtree_node_new() -> *mut quadtree_node_t {
    let mut node = 0 as *mut quadtree_node_t;
    node = malloc(::std::mem::size_of::<quadtree_node_t>()) as *mut quadtree_node_t;
    if node.is_null() {
        return 0 as *mut quadtree_node_t;
    }
    (*node).ne = 0 as *mut quadtree_node;
    (*node).nw = 0 as *mut quadtree_node;
    (*node).point = 0 as *mut i32;
    return node;
}
pub unsafe extern "C" fn test_node() -> i32 {
    let mut node = quadtree_node_new();
    let mut ok = 0;
    if quadtree_node_isleaf(node) == 0 {
        ok += 1;
    }
    if quadtree_node_isempty(node) != 0 {
        ok += 1;
    }
    ok
}
"#;

/// The corpus census runs A5 in precise-replay mode over the frozen benchmark
/// graph; the fixtures run the same configuration so site proofs resolve.
pub(super) fn rewrite_precise(name: &str, src: &str) -> super::RewriteOutcome {
    use super::{OverlapMode, WholeProgramAttestation};
    let dir = std::env::temp_dir().join(format!("crat-wave6a-{name}-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let root = dir.join("lib.rs");
    std::fs::write(&root, src).unwrap();
    let result = super::rewrite_m1_path_a5_injected(
        &root,
        OverlapMode::PreciseReplay,
        Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        &|_| {},
    );
    std::fs::remove_dir_all(dir).unwrap();
    result
}

pub(super) struct Emitted {
    pub(super) source: String,
    pub(super) reverted: usize,
    pub(super) degradations: Vec<super::decision::Degradation>,
    pub(super) artifacts: super::RawBoundaryArtifacts,
}

pub(super) fn emitted(name: &str, src: &str) -> Emitted {
    match rewrite_precise(name, src) {
        super::RewriteOutcome::Emitted {
            source,
            degradations,
            reverted_count,
            raw_boundary_artifacts,
            ..
        } => Emitted {
            source,
            reverted: reverted_count,
            degradations,
            artifacts: raw_boundary_artifacts,
        },
        super::RewriteOutcome::Degraded {
            reason,
            degradations,
            first_diags,
            ..
        } => panic!("{name} must emit: {reason}\n{degradations:#?}\n{first_diags:#?}"),
    }
}

pub(super) fn compact(text: &str) -> String {
    text.chars().filter(|c| !c.is_whitespace()).collect()
}

pub(super) fn reason_of(
    degradations: &[super::decision::Degradation],
    subject: &str,
) -> Option<String> {
    degradations
        .iter()
        .find(|d| d.subject == subject)
        .map(|d| d.reason.key().to_owned())
}

// The quadtree frame-read witness (report 001, STOP 4) moved under W6A-A1:
// `wave6a_return_certificate_tests::w6a_a1_quadtree_node_new_returns_a_box_and_the_receiver_owns_it`
// asserts the delivery the certificate route was ruled to give (relay 005).

/// **The rule's soundness control.** An unannotated copy of a parameter the
/// model calls `Ref` (`let p = a;` then `p[1]`) stays exactly where the base
/// leaves it — `copy-source-coupled` — because constructing a slice over a
/// binding that becomes a thin reference would widen that reference
/// (R395-2, fix-2). The annotated twin of this shape widens at the base
/// today (`let p: *mut i32 = a;` → `p: &[i32] = from_raw_parts(a, 1024)` with
/// `a: &i32`); that is reported, not repaired, here.
#[test]
fn w6a_b1_copy_of_a_reference_root_is_refused() {
    let src = "#![allow(dead_code, unused_unsafe, unused_variables)]\n\
               pub unsafe fn f(a: *mut i32) -> i32 { let p = a; *p.offset(1) }\n";
    let decisions = super::emit_tests::decisions_of(src);
    let reason = decisions
        .iter()
        .find(|(name, is_param, _)| name == "p" && !is_param)
        .map(|(_, _, reason)| reason.clone());
    assert_eq!(
        reason.as_deref(),
        Some("copy-source-coupled"),
        "{decisions:#?}"
    );
}

/// brotli `ZopfliCostModelSetFromLiteralCosts`, reduced: two unannotated
/// locals rooted in FIELD places of a delivered `&mut` parameter — an inline
/// array decay (`(*self_0).cost_cmd_.as_mut_ptr()`, exact length 704) and a
/// raw pointer field load (`(*self_0).literal_costs_`, fallback extent).
/// Neither widens `self_0`: the constructed slice is over the field's own
/// pointer value, so the reference-root refusal does not apply.
pub(super) const BROTLI_COST_MODEL: &str = r#"
#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, non_camel_case_types, non_snake_case)]
#[repr(C)]
pub struct ZopfliCostModel {
    pub cost_cmd_: [f32; 704],
    pub literal_costs_: *mut f32,
    pub num_bytes_: usize,
}
unsafe extern "C" fn ZopfliCostModelSetFromLiteralCosts(mut self_0: *mut ZopfliCostModel, mut position: usize) {
    let mut literal_costs = (*self_0).literal_costs_;
    let mut literal_carry = 0.0f64 as f32;
    let mut cost_cmd = ((*self_0).cost_cmd_).as_mut_ptr();
    let mut num_bytes = (*self_0).num_bytes_;
    let mut i: usize = 0;
    *literal_costs.offset(0 as i32 as isize) = 0.0f64 as f32;
    i = 0 as i32 as usize;
    while i < num_bytes {
        literal_carry += *literal_costs.offset(i.wrapping_add(1 as i32 as usize) as isize);
        *literal_costs.offset(i.wrapping_add(1 as i32 as usize) as isize) =
            *literal_costs.offset(i as isize) + literal_carry;
        literal_carry -= *literal_costs.offset(i.wrapping_add(1 as i32 as usize) as isize)
            - *literal_costs.offset(i as isize);
        i = i.wrapping_add(1);
    }
    i = 0 as i32 as usize;
    while i < 704 as i32 as usize {
        *cost_cmd.offset(i as isize) = 0.0f64 as f32;
        i = i.wrapping_add(1);
    }
}
"#;

/// `literal_costs` (a raw pointer value loaded from a field of `self_0`)
/// delivers with the fallback extent: the slice covers that pointer's pointee,
/// never `self_0`'s memory. `cost_cmd` (the inline array field's decay) never
/// takes this rule's constructor: `self_0` becomes `&mut ZopfliCostModel` and
/// a `from_raw_parts_mut` over its own field would be a second live safe view
/// the compiler cannot relate to `self_0`.
///
/// What happens to it instead is a **dichotomy over the frame**, because the
/// sound form this refusal was protecting — the reborrow `&mut
/// (*self_0).cost_cmd_[..]` — is wave-6f's W6F-5′ and exists only where their
/// rule is composed (R456-6). With it, `cost_cmd` delivers that reborrow and
/// indexes; without it, the subject is held `place-read-pointee` and keeps
/// its input text. Neither frame may emit a constructor over the field, and
/// the assertion that matters holds in both.
#[test]
fn w6a_b1_field_rooted_locals_split_by_what_memory_the_slice_covers() {
    let out = emitted("brotli-cost-model", BROTLI_COST_MODEL);
    let src = compact(&out.source);
    assert_eq!(out.reverted, 0, "{}", out.source);
    assert!(
        src.contains("mutself_0:&mutZopfliCostModel"),
        "{}",
        out.source
    );
    assert!(
        src.contains("letmutliteral_costs:&mut[f32]=core::slice::from_raw_parts_mut((*self_0).literal_costs_,crate::FALLBACK_SLICE_EXTENT);"),
        "{}",
        out.source
    );
    assert!(src.contains("literal_costs[i]"), "{}", out.source);
    assert_eq!(
        reason_of(
            &out.degradations,
            "ZopfliCostModelSetFromLiteralCosts::literal_costs"
        ),
        None,
        "{:#?}",
        out.degradations
    );
    // Never, on either frame: a constructor over the field's own memory.
    assert!(
        !src.contains("from_raw_parts_mut(((*self_0).cost_cmd_)"),
        "no constructor over the field\n{}",
        out.source
    );
    let reborrowed = src.contains("letmutcost_cmd:&mut[f32]=&mut((*self_0).cost_cmd_)[..];");
    if reborrowed {
        // The composed frame: wave-6f's W6F-5′ renders the view and this
        // rule's refusal stands aside for exactly that subject (R456-6).
        assert!(src.contains("cost_cmd[i]="), "{}", out.source);
        assert_eq!(
            reason_of(
                &out.degradations,
                "ZopfliCostModelSetFromLiteralCosts::cost_cmd"
            ),
            None,
            "{:#?}",
            out.degradations
        );
    } else {
        // The lane's own frame: no reborrow rule, so the subject is held and
        // its text is kept exactly.
        assert!(
            src.contains("letmutcost_cmd=((*self_0).cost_cmd_).as_mut_ptr();"),
            "{}",
            out.source
        );
        assert!(
            src.contains("*cost_cmd.offset(iasisize)="),
            "{}",
            out.source
        );
        assert_eq!(
            reason_of(
                &out.degradations,
                "ZopfliCostModelSetFromLiteralCosts::cost_cmd"
            )
            .as_deref(),
            Some("place-read-pointee"),
            "{:#?}",
            out.degradations
        );
    }
}

/// The tulip indicator table: `ti_cci` is a fn-pointer web ROOT, so
/// `ti_buffer_new` / `ti_buffer_free` (called from it) are web MEMBERS and
/// the exposure family gives each a raw outer wrapper when its signature
/// converts (`ti_buffer_free(buffer: *mut)` → `__crat_safe_ti_buffer_free(buffer)`).
pub(super) const TULIP_INDICATOR_TABLE: &str = r#"
#[repr(C)]
pub struct ti_indicator_info {
    pub name: *const std::os::raw::c_char,
    pub indicator: Option<unsafe extern "C" fn(std::os::raw::c_int, *const *const std::os::raw::c_double, std::os::raw::c_int, *const *mut std::os::raw::c_double) -> std::os::raw::c_int>,
}
#[no_mangle]
pub static mut ti_indicators: [ti_indicator_info; 1] = [ti_indicator_info {
    name: b"cci\0" as *const u8 as *const std::os::raw::c_char,
    indicator: Some(ti_cci as unsafe extern "C" fn(std::os::raw::c_int, *const *const std::os::raw::c_double, std::os::raw::c_int, *const *mut std::os::raw::c_double) -> std::os::raw::c_int),
}];
"#;

/// **Relays 011 / 013 (R419-3, R423-7): the wrapper bridges the sized owning
/// positions, so the transaction rides its raw-surfaced endpoints.** With
/// `ti_cci` in the indicator table, `ti_buffer_new` and `ti_buffer_free` are
/// fn-pointer-web members: a converted signature of theirs gets the exposure
/// family's raw outer wrapper. The wrapper re-enters ownership at the owning
/// FORMAL (`ti_buffer_free(buffer: *mut ti_buffer) {
/// __crat_safe_ti_buffer_free(Box::from_raw(buffer)) }`) and hands the owning
/// RETURN back as the raw allocation it always was; every in-crate caller
/// binds to the safe inner name. Before the bridge this was tulip's 216 E0308
/// on census-1 (`3d28008a`).
#[test]
fn w6a_t1_web_member_endpoints_deliver_through_the_wrapper_bridges() {
    let out = emitted(
        "tulip-cci-web",
        &format!(
            "{}{}",
            super::wave6a_fixture_tulip::TULIP_BUFFER,
            TULIP_INDICATOR_TABLE
        ),
    );
    let src = compact(&out.source);
    assert_eq!(out.reverted, 0, "{}\n{:#?}", out.source, out.degradations);
    assert!(src.contains("pubvals:Box<[f64]>,}"), "{}", out.source);
    assert!(
        src.contains("fnti_buffer_free(mutbuffer:*mutti_buffer){__crat_safe_ti_buffer_free(Box::from_raw(buffer))}"),
        "{}",
        out.source
    );
    assert!(
        src.contains("fn__crat_safe_ti_buffer_free(mutbuffer:Box<ti_buffer>){drop(buffer);}"),
        "{}",
        out.source
    );
    assert!(
        src.contains("fnti_buffer_new(mutsize:std::os::raw::c_int)->Box<ti_buffer>{"),
        "{}",
        out.source
    );
    assert!(
        src.contains("letmutsum:Box<ti_buffer>=ti_buffer_new(period);"),
        "{}",
        out.source
    );
    assert!(
        src.contains("__crat_safe_ti_buffer_free(sum);"),
        "{}",
        out.source
    );
    assert!(
        out.artifacts
            .flexible_tail_receipts
            .contains("wrapper-bridged-endpoint "),
        "{}",
        out.artifacts.flexible_tail_receipts
    );
    assert_eq!(
        reason_of(&out.degradations, "ti_cci::sum"),
        None,
        "{:#?}",
        out.degradations
    );
}

/// Control: a foreign consumer takes the struct by pointer — the layout may
/// not change; the transaction holds typed and every row keeps
/// `box-flexible-tail-held`.
#[test]
fn w6a_t1_struct_crossing_a_foreign_boundary_is_held() {
    let src_text = format!(
        "{}{}",
        super::wave6a_fixture_tulip::TULIP_HEADER,
        super::wave6a_fixture_tulip::TULIP_CROSSING_BODY
    );
    let out = emitted("tulip-crossing", &src_text);
    let src = compact(&out.source);
    assert!(
        src.contains("pubvals:[std::os::raw::c_double;1],"),
        "{}",
        out.source
    );
    assert!(!src.contains("Box<ti_buffer>"), "{}", out.source);
    assert_eq!(
        reason_of(&out.degradations, "crossing::b").as_deref(),
        Some("box-flexible-tail-held"),
        "{:#?}",
        out.degradations
    );
    assert_eq!(
        reason_of(&out.degradations, "ti_buffer_new::ret").as_deref(),
        Some("box-flexible-tail-held")
    );
    assert!(
        out.artifacts
            .flexible_tail_receipts
            .contains("ti_buffer\theld\tflexible-tail-crosses-boundary:extern:ti_buffer_dump"),
        "{}",
        out.artifacts.flexible_tail_receipts
    );
}

/// Control: a caller reads the buffer after handing it to the freeing callee,
/// so the callee's parameter is not an owning transfer at every caller — the
/// transaction holds typed (`param-caller-retains`) and nothing moves.
#[test]
fn w6a_t1_caller_using_the_buffer_after_transfer_is_held() {
    let src_text = format!(
        "{}{}",
        super::wave6a_fixture_tulip::TULIP_HEADER,
        super::wave6a_fixture_tulip::TULIP_RETAINED_BODY
    );
    let out = emitted("tulip-retained", &src_text);
    let src = compact(&out.source);
    assert!(!src.contains("Box<ti_buffer>"), "{}", out.source);
    assert_eq!(
        reason_of(&out.degradations, "retained::b").as_deref(),
        Some("box-flexible-tail-held"),
        "{:#?}",
        out.degradations
    );
    assert!(
        out.artifacts.flexible_tail_receipts.contains(
            "ti_buffer\theld\tflexible-tail-param-caller-retains:retained:used-after-transfer"
        ),
        "{}",
        out.artifacts.flexible_tail_receipts
    );
}

/// **Relay 007 §3a (wave-6s2 006).** A receiver of a LOCAL callee is the
/// return-receiver family's where that family converts the callee's return:
/// on batch 8's composition it converted `chunk_data`'s return to `&'a [u8]`,
/// and a `from_raw_parts` over it is E0308.
///
/// **Re-pinned by R615-7 (wave-6l 055, rule (b′) with the bracket).** Here NO
/// family converts `chunk_data`'s return (no permit, no receiver plan, no Box
/// certificate): the call is the raw pointer C returned, so the sealed
/// constructor is WRAPPED around it (the call's own text and edits untouched)
/// and takes §77's receipted fallback. The E0308 premise is pinned where it
/// holds by wave-6l's `w6l_nul_c3`.
#[test]
fn w6a_b1_receiver_of_a_local_callee_is_not_typed_by_its_constructor() {
    let src = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
               pub unsafe fn chunk_data(mut chunk: *mut u8) -> *mut u8 { return chunk.offset(8 as i32 as isize); }\n\
               pub unsafe fn reader(mut chunk: *mut u8) -> u8 { let mut d = chunk_data(chunk); return *d.offset(0 as i32 as isize); }\n";
    let out = emitted("receiver-of-local-callee", src);
    let text = compact(&out.source);
    assert!(
        text.contains("fnchunk_data(mutchunk:*mutu8)->*mutu8"),
        "the callee's return is not converted: {}",
        out.source
    );
    assert!(
        text.contains(
            "core::slice::from_raw_parts(chunk_data(chunk),crate::FALLBACK_SLICE_EXTENT)"
        ),
        "{}",
        out.source
    );
    assert!(
        reason_of(&out.degradations, "reader::d").is_none(),
        "{:#?}",
        out.degradations
    );
}

/// **Relay 009 §1 (wave-4 026 C3).** A libc callee declared in the crate's
/// own `extern "C"` block is a local `DefId` but not a local callee: the
/// shared-interface clause of the refusal must not fire on `strlen(p)`, so
/// the unannotated slice local keeps its constructor typing; an argument of
/// a callee the crate owns (a body) is still refused.
/// **The root is itself a delivered slice.** Over a formal another rule
/// delivers fat (`a: &mut [i8]`), wave-6s's computed-suffix-copy already
/// renders the initializer as the reslice (`&mut (a)[1..]`); the constructor
/// planner takes that value bare — wrapping it in `from_raw_parts_mut` is
/// E0308 and reverts the whole class, the root with it. The root delivers on
/// the batch-8 composition only (on this branch `a` degrades
/// `slice-cursor-use`, so the witness is load-bearing there: the reslice
/// text and no class revert; here it pins the constructor form).
#[test]
fn w6a_b1_suffix_copy_of_a_delivered_root_is_the_reslice() {
    let src = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
               pub unsafe fn measure(mut a: *mut std::os::raw::c_char, mut n: usize) -> usize {\n\
                   let mut p = a.offset(1 as i32 as isize);\n\
                   *p.offset(0 as i32 as isize) = 0 as std::os::raw::c_char;\n\
                   return n;\n\
               }\n";
    let out = emitted("suffix-copy-root", src);
    let text = compact(&out.source);
    let root_delivered = text.contains("muta:&mut[std::os::raw::c_char]");
    assert!(
        if root_delivered {
            text.contains("letmutp:&mut[i8]=&mut(a)[(1asi32)asusize..];")
        } else {
            text.contains("letmutp:&mut[i8]=core::slice::from_raw_parts_mut(a.offset(1asi32asisize),crate::FALLBACK_SLICE_EXTENT);")
        },
        "root_delivered={root_delivered}\n{}\n{:#?}",
        out.source,
        out.degradations
    );
    assert!(
        !text.contains("from_raw_parts_mut(&mut(a)"),
        "{}\n{:#?}",
        out.source,
        out.degradations
    );
    assert_eq!(
        reason_of(&out.degradations, "measure::p"),
        None,
        "{:#?}",
        out.degradations
    );
    assert_ne!(
        reason_of(&out.degradations, "measure::a").as_deref(),
        Some("reverted-after-verify-failure"),
        "{:#?}",
        out.degradations
    );
}

/// **Clause (b), the assignment form** (lil `fnc_charat::str`: null-init,
/// then `str = lil_to_string(..)`, then `strlen(str)`): an unannotated local
/// ASSIGNED from a local callee's call is the receiver shape clause (b)
/// refuses at a `let` — the return family reads the callee's settled return,
/// a nullable-slice constructor over the assignment is E0308 once it
/// converts. Before the libc fix the `strlen` bug held it by accident.
#[test]
fn w6a_b1_assigned_call_of_a_local_callee_is_refused() {
    let src = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables, unused_assignments)]\n\
               extern \"C\" { fn strlen(s: *const std::os::raw::c_char) -> usize; }\n\
               pub unsafe fn to_string(mut v: *mut std::os::raw::c_char) -> *const std::os::raw::c_char { return v; }\n\
               pub unsafe fn charat(mut v: *mut std::os::raw::c_char, mut index: usize) -> std::os::raw::c_char {\n\
                   let mut s = 0 as *const std::os::raw::c_char;\n\
                   s = to_string(v);\n\
                   if index >= strlen(s) { return 0; }\n\
                   return *s.offset(index as isize);\n\
               }\n";
    let out = emitted("assigned-call", src);
    let text = compact(&out.source);
    assert!(
        !text.contains("from_raw_parts("),
        "{}\n{:#?}",
        out.source,
        out.degradations
    );
    assert!(
        reason_of(&out.degradations, "charat::s").is_some(),
        "{}\n{:#?}",
        out.source,
        out.degradations
    );
}

#[test]
fn w6a_b1_libc_argument_is_not_a_shared_interface() {
    let src = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
               extern \"C\" { fn strlen(s: *const std::os::raw::c_char) -> usize; }\n\
               pub unsafe fn measure(mut a: *mut std::os::raw::c_char, mut n: usize) -> usize {\n\
                   let mut p = a.offset(1 as i32 as isize);\n\
                   *p.offset(0 as i32 as isize) = 0 as std::os::raw::c_char;\n\
                   return strlen(p);\n\
               }\n\
               pub unsafe fn own_len(mut s: *const std::os::raw::c_char) -> usize { let mut i = 0 as usize; while *s.offset(i as isize) != 0 { i = i.wrapping_add(1); } return i; }\n\
               pub unsafe fn measure_own(mut a: *mut std::os::raw::c_char, mut n: usize) -> usize {\n\
                   let mut p = a.offset(1 as i32 as isize);\n\
                   *p.offset(0 as i32 as isize) = 0 as std::os::raw::c_char;\n\
                   return own_len(p);\n\
               }\n";
    let out = emitted("libc-argument", src);
    let text = compact(&out.source);
    // The libc lend keeps the constructor typing: over a raw root the
    // fallback-extent view, over a root another rule delivers fat (the
    // batch-8 composition) the reslice of it.
    assert!(
        text.contains("letmutp:&mut[i8]=core::slice::from_raw_parts_mut(a.offset(1asi32asisize),crate::FALLBACK_SLICE_EXTENT);")
            || text.contains("letmutp:&mut[i8]=&mut(a)[(1asi32)asusize..];"),
        "{}\n{:#?}",
        out.source,
        out.degradations
    );
    assert_eq!(
        reason_of(&out.degradations, "measure::p"),
        None,
        "{:#?}",
        out.degradations
    );
    // The argument of a callee the crate owns is still refused (clause (b)).
    assert!(
        reason_of(&out.degradations, "measure_own::p").is_some(),
        "{:#?}",
        out.degradations
    );
}

/// **R470-4 — the exposure wrapper casts a `c_void` base to the parameter's
/// own element type.** The wrapper keeps the C ABI's signature, so its
/// parameter is whatever C declared — for brotli's hasher accessors,
/// `extra: *mut libc::c_void`. The inner function's parameter is delivered
/// `&mut [u8]` / `&mut [u32]`, and the slice the wrapper builds for it has no
/// element type to infer from a `c_void` base: `from_raw_parts_mut(extra, N)`
/// is `expected *mut u8, found *mut libc::c_void`. main 056 read brotli's
/// first failing verify tree and **21 of its 26 rows are this one shape**, at
/// nine sites in `Addr/Head/TinyHash H40-H42` and their twins.
///
/// The extent is untouched: this is a typing fix over the base, not a length
/// claim, so no receipt and no waiver moves (§77). Two controls ride with it —
/// a base that is already the element type takes no cast, and a parameter the
/// run does not deliver is passed by name — and the fault is the cast removed.
///
/// These are consumer controls over explicitly constructed signatures, as
/// `return_terminal_tests`' wrapper controls are: they claim no model
/// admission and no execution, only what the production wrapper builder emits.
#[test]
fn w6a_the_exposure_wrapper_casts_a_void_base_to_its_element_type() {
    let cases = [
        // (outer C signature, inner delivered signature, expected text)
        (
            "*mut libc::c_void",
            "&mut [u8]",
            "core::slice::from_raw_parts_mut(p.cast::<u8>(), crate::FALLBACK_SLICE_EXTENT)",
        ),
        (
            "*const libc::c_void",
            "&[u32]",
            "core::slice::from_raw_parts(p.cast::<u32>(), crate::FALLBACK_SLICE_EXTENT)",
        ),
        (
            "*mut core::ffi::c_void",
            "Option<&mut [u16]>",
            "if p.is_null() { None } else { Some(core::slice::from_raw_parts_mut(p.cast::<u16>(), crate::FALLBACK_SLICE_EXTENT)) }",
        ),
        // Controls: a base that is ALREADY the element type takes no cast …
        (
            "*mut u8",
            "&mut [u8]",
            "core::slice::from_raw_parts_mut(p, crate::FALLBACK_SLICE_EXTENT)",
        ),
        // … and a parameter this run does not deliver is passed by name.
        ("*mut libc::c_void", "*mut libc::c_void", "inner(p)"),
    ];
    for (outer_ty, inner_ty, expected) in cases {
        let rendered = wrapper_body(outer_ty, inner_ty);
        // The pretty printer line-wraps; the text is compared without
        // whitespace, as every emitted-text assertion in this file is.
        let rendered = compact(&rendered);
        let expected = compact(expected);
        assert!(
            rendered.contains(&expected),
            "outer {outer_ty} / inner {inner_ty}\n  expected: {expected}\n  rendered: {rendered}"
        );
        if !outer_ty.contains("c_void") || !inner_ty.contains('[') {
            assert!(
                !rendered.contains(".cast::<"),
                "no cast for outer {outer_ty} / inner {inner_ty}: {rendered}"
            );
        }
    }
}

/// The production wrapper builder, over two explicitly constructed signatures.
fn wrapper_body(outer_ty: &str, inner_ty: &str) -> String {
    rustc_span::create_session_globals_then(
        rustc_span::edition::Edition::Edition2018,
        &[],
        None,
        || {
            let session = rustc_session::parse::ParseSess::new(
                rustc_driver::DEFAULT_LOCALE_RESOURCES.to_vec(),
            );
            let inner_crate = super::slice_use_inventory_tests::parse_crate(
                &session,
                "constructed-inner.rs",
                &format!("unsafe fn inner(p: {inner_ty}) -> u32 {{ 0 }}"),
            )
            .expect("the delivered signature parses");
            let rustc_ast::ItemKind::Fn(inner) = &inner_crate.items[0].kind else {
                panic!("constructed inner item must be a function");
            };
            let outer_crate = super::slice_use_inventory_tests::parse_crate(
                &session,
                "constructed-outer.rs",
                &format!("pub unsafe extern \"C\" fn outer(p: {outer_ty}) -> u32 {{ loop {{}} }}"),
            )
            .expect("the C signature parses");
            let mut outer_crate = outer_crate;
            let rustc_ast::ItemKind::Fn(outer) = &mut outer_crate.items[0].kind else {
                panic!("constructed outer item must be a function");
            };
            let block = super::ast_transform::surface_wrapper_block_with_outer(
                "inner",
                inner,
                None,
                &outer.sig.decl,
            )
            .expect("actual production wrapper builder");
            outer.body = Some(block);
            rustc_ast_pretty::pprust::item_to_string(&outer_crate.items[0])
        },
    )
}

/// **R473-3 — the WRAPPER BODY's base is cast, not just the call site's.**
/// Report 030 put this cast in `ast_transform::surface_argument`, the builder
/// that writes a wrapper's arguments when no plan supplies them. brotli's
/// wrappers come from the other path: `decision::surface_argument::plan`
/// renders the glue itself and `apply_surface_plans` takes that text verbatim,
/// so the cast never reached them. The corpus shape is
/// `batch16-verify-trees/brotli.first-failing-verify-tree.rs`:
///
/// ```text
/// unsafe extern "C" fn AddrH40(mut extra: *mut libc::c_void) -> *mut uint32_t {
///     __crat_safe_AddrH40(core::slice::from_raw_parts_mut(extra,
///             crate::FALLBACK_SLICE_EXTENT))
/// }
/// unsafe extern "C" fn __crat_safe_AddrH40(mut extra: &mut [u8]) -> *mut uint32_t
/// ```
///
/// nine wrappers (`{Addr,Head,TinyHash}H{40,41,42}`), E0308 at each, and the
/// class then reverts — which is why the post-revert emitted tree carries none
/// of them and report 032 read the cast as inert.
///
/// The element type is the void region's own (`Region::element`), the string
/// the converted signature was written from; the extent is untouched.
#[test]
fn w6a_the_wrapper_bodys_void_base_takes_the_delivered_element_type() {
    use super::decision::{seam::Form, surface_argument::wrapper_base};

    // The corpus rows: a `c_void` parameter delivered as a typed slice.
    assert_eq!(
        wrapper_base(
            "extra",
            Form::Slice { mutable: true },
            true,
            Some("uint32_t")
        ),
        "extra.cast::<uint32_t>()"
    );
    assert_eq!(
        wrapper_base("extra", Form::Slice { mutable: false }, true, Some("u8")),
        "extra.cast::<u8>()"
    );
    assert_eq!(
        wrapper_base(
            "extra",
            Form::Opt {
                mutable: true,
                slice: true
            },
            true,
            Some("uint16_t")
        ),
        "extra.cast::<uint16_t>()"
    );
    // Controls: a base that is not `c_void` keeps the parameter …
    assert_eq!(
        wrapper_base("data", Form::Slice { mutable: true }, false, Some("u8")),
        "data"
    );
    // … a thin form has no constructor to feed …
    assert_eq!(
        wrapper_base("extra", Form::Ref { mutable: true }, true, Some("u8")),
        "extra"
    );
    // … and a region that delivers no element for a parameter is left alone.
    assert_eq!(
        wrapper_base("extra", Form::Slice { mutable: true }, true, None),
        "extra"
    );
}

/// **R477-3 — the element is the CONVERTED parameter's, not the region's.**
/// batch 20 measured the difference: the six `TinyHashH4x` wrappers verified
/// (their access width IS `u8`, so both readings agree) while `AddrH4{0,1,2}`
/// stayed `expected *mut u8, found *mut u32` and `HeadH42` `found *mut u16` —
/// the width the BODY reinterprets at, cast onto a parameter that is a byte
/// slice. The `Addr` shape is the case the two readings disagree on.
#[test]
fn w6a_the_wrapper_cast_takes_the_converted_parameters_element_not_the_regions() {
    use super::decision::{
        seam::Form,
        surface_argument::{delivered_element, wrapper_base_for_region},
        void_region::{Region, Shape},
    };

    let region = |shape: Shape, element: &str, size: u64| Region {
        shape,
        offset_bytes: 0,
        len_bytes: None,
        element: element.to_owned(),
        element_size: size,
        mutable: true,
        uses: Vec::new(),
        replaced: rustc_span::DUMMY_SP,
        inner: None,
    };

    // The `Addr` shape: the body reinterprets at `u32`, the parameter carries
    // bytes, and the cast must follow the parameter.
    assert_eq!(
        delivered_element(&region(Shape::Accessor, "uint32_t", 4)),
        Some("u8")
    );
    // `HeadH42`'s width, same answer.
    assert_eq!(
        delivered_element(&region(Shape::Accessor, "uint16_t", 2)),
        Some("u8")
    );
    // `TinyHash`, where the two readings agree — which is why only those six
    // verified in batch 20.
    assert_eq!(
        delivered_element(&region(Shape::Accessor, "uint8_t", 1)),
        Some("u8")
    );
    // A width read delivers a byte slice too …
    assert_eq!(
        delivered_element(&region(Shape::WidthRead, "uint32_t", 4)),
        Some("u8")
    );
    // … and so does its MIRROR, the width WRITE (R478-3): wave-6b gives the
    // pair one length rule and one parameter form, so the converted parameter
    // carries bytes for a writer exactly as for a reader.
    assert_eq!(
        delivered_element(&region(Shape::WidthWrite, "uint64_t", 8)),
        Some("u8")
    );
    // … and a byte view is a LOCAL's region, so no wrapper argument is built
    // from it.
    assert_eq!(
        delivered_element(&region(Shape::ByteView, "uint8_t", 1)),
        None
    );

    // The WIRING, not only the pieces: the planner asks this one function, so
    // a base wired back to the region's own element is red here.
    assert_eq!(
        wrapper_base_for_region(
            "extra",
            Form::Slice { mutable: true },
            true,
            Some(&region(Shape::Accessor, "uint32_t", 4)),
        ),
        "extra.cast::<u8>()"
    );
    assert_eq!(
        wrapper_base_for_region("extra", Form::Slice { mutable: true }, true, None),
        "extra"
    );
}
