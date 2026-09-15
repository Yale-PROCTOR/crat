//! Wave-6o reductions of binn::binn_copy, quadtree::quadtree_node_with_bounds
//! and lil::get_bracketpart: an UNANNOTATED null-initialized local that the
//! analysis decides `Opt` receives its inserted declaration type.
use super::{decision::Decision, emit_tests::ast_emitted_source_of, verify};

const PRELUDE: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case)]
unsafe extern "C" { fn myMalloc(size: usize) -> *mut core::ffi::c_void; }
#[repr(C)] struct Binn { header: i32, used_size: i32, count: i32 }
unsafe fn binn_new(count: i32) -> *mut Binn {
    let mut item: *mut Binn = 0 as *mut Binn;
    item = myMalloc(core::mem::size_of::<Binn>()) as *mut Binn;
    if !item.is_null() { (*item).header = 0x1f22b11f; (*item).count = count; }
    return item;
}
"#;

fn decisions_and_receipts(
    input: &str,
    function: &str,
    binding: &str,
) -> (Decision, Vec<(String, String, String)>) {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let table = super::decide_table(tcx).expect("native decisions");
        let (subject, decision) = table
            .entries
            .iter()
            .find(|(subject, _)| {
                tcx.item_name(subject.fn_did.to_def_id()).as_str() == function
                    && subject.param_name.as_deref() == Some(binding)
            })
            .expect("corpus-derived local");
        assert!(
            subject.ty_span.is_none(),
            "the fixture local must be unannotated"
        );
        let receipts = table
            .option_receipts
            .iter()
            .filter(|receipt| {
                receipt.obligation.planned.key.subject
                    == super::mechanical_receipt::MechanicalSubjectKey::Local {
                        owner: subject.fn_did,
                        mir_local: subject.local.as_u32(),
                        slot_depth: 0,
                    }
            })
            .map(|receipt| {
                (
                    receipt.operation.clone(),
                    format!("{:?}", receipt.obligation.intended_terminal_state),
                    format!("{:?}", receipt.obligation.intended_terminal_reason),
                )
            })
            .collect();
        (decision.clone(), receipts)
    })
    .expect("fixture compiler context")
}

fn admitted_declaration(input: &str, function: &str, binding: &str, declaration: &str) {
    assert!(verify::type_checks_str(input));
    let (decision, receipts) = decisions_and_receipts(input, function, binding);
    eprintln!("WAVE6O_DECL_RECEIPTS {function}::{binding} {receipts:#?}");
    assert!(
        matches!(decision, Decision::Opt { slice: false, .. }),
        "the unannotated null-initialized local must stay optional for {function}::{binding}: {decision:?}"
    );
    assert!(
        receipts
            .iter()
            .any(|(operation, state, _)| operation == "null-initialization" && state == "Applied"),
        "the null initializer must be planned as `None`: {receipts:?}"
    );
    let output = ast_emitted_source_of(input).expect("native emission");
    assert!(
        output.contains(declaration),
        "the declaration type must be inserted: expected `{declaration}` in\n{output}"
    );
    eprintln!("WAVE6O_DECL_OUTPUT_BEGIN {function}\n{output}\nWAVE6O_DECL_OUTPUT_END");
    assert!(
        verify::type_checks_str(&output),
        "emitted declaration must compile: {output}"
    );
}

/// binn::binn_copy — a local callee's raw result, null-tested, written
/// through, returned bare.
#[test]
fn wave6o_binn_copy_unannotated_null_init_local_receives_its_type() {
    let input = format!(
        r#"{PRELUDE}
unsafe fn binn_copy(count: i32, size: i32) -> *mut Binn {{
    let mut item = 0 as *mut Binn;
    if size < 0 {{ return 0 as *mut Binn; }}
    item = binn_new(count);
    if !item.is_null() {{
        (*item).used_size = 9 + size;
        (*item).count = count;
    }}
    return item;
}}
"#
    );
    admitted_declaration(
        &input,
        "binn_copy",
        "item",
        "let mut item: Option<&mut crate::Binn> = None;",
    );
}

/// quadtree::quadtree_node_with_bounds — the same shape with an early null
/// return and a field store through the local.
#[test]
fn wave6o_quadtree_node_unannotated_null_init_local_receives_its_type() {
    let input = format!(
        r#"{PRELUDE}
unsafe fn quadtree_node_with_bounds(minx: i32) -> *mut Binn {{
    let mut node = 0 as *mut Binn;
    node = binn_new(0);
    if node.is_null() {{ return 0 as *mut Binn; }}
    (*node).count = minx;
    return node;
}}
"#
    );
    admitted_declaration(
        &input,
        "quadtree_node_with_bounds",
        "node",
        "let mut node: Option<&mut crate::Binn> = None;",
    );
}

/// lil::get_bracketpart — a pass-through: the local is never written through
/// in its function and is returned at a `*mut` position. The declaration
/// admits it into the Option family (its first-site reason is no longer the
/// declaration); the return then keeps the typed shared-to-mutable hold.
#[test]
fn wave6o_get_bracketpart_pass_through_moves_to_the_typed_return_hold() {
    let input = format!(
        r#"{PRELUDE}
unsafe fn get_bracketpart(count: i32) -> *mut Binn {{
    let mut val = 0 as *mut Binn;
    let mut cmd = binn_new(count);
    val = binn_new((*cmd).count);
    (*cmd).count = 0;
    return val;
}}
"#
    );
    assert!(verify::type_checks_str(&input));
    let (decision, receipts) = decisions_and_receipts(&input, "get_bracketpart", "val");
    assert!(
        receipts
            .iter()
            .any(|(operation, _, _)| operation == "null-initialization"),
        "the declaration must admit the local into the Option family: {decision:?} {receipts:?}"
    );
    assert!(
        receipts
            .iter()
            .any(|(operation, _, reason)| operation == "return-raw"
                && reason.contains("option-raw-return:shared-to-mut-held")),
        "the pass-through must hold at its return, not at its declaration: {decision:?} {receipts:?}"
    );
    let output = ast_emitted_source_of(&input).expect("hold emission");
    assert!(verify::type_checks_str(&output), "{output}");
}

/// Relay 010 — brotli `BrotliFindAllStaticDictionaryMatches::{s,s_0,s_1,s_2}`:
/// an unannotated null-initialized local whose form is an optional SLICE
/// (`s = &*data.offset(l) as *const u8; *s.offset(k)`) receives
/// `Option<&[u8]>`. The VALUE is the existing nullable-slice plan (here, with
/// `data` still raw in the reduction, the one-element `from_ref` carrier;
/// with wave-6s's computed view, `Some(&data[l..])`).
#[test]
fn wave6o_unannotated_null_init_optional_slice_receives_its_type() {
    let input = r#"
#![allow(dead_code, unused_mut, non_snake_case)]
unsafe fn FindAllStaticDictionaryMatches(data: *const u8, l: usize, k: usize, n: usize) -> u32 {
    let mut s = 0 as *const u8;
    let mut sum = 0u32;
    if l < n {
        s = &*data.offset(l as isize) as *const u8;
        sum = sum.wrapping_add(*s.offset(k as isize) as u32);
    }
    return sum;
}
"#;
    assert!(verify::type_checks_str(input));
    let (decision, receipts) = decisions_and_receipts(input, "FindAllStaticDictionaryMatches", "s");
    assert!(
        matches!(decision, Decision::Opt { slice: true, .. }),
        "the unannotated null-initialized optional slice must be admitted: {decision:?}"
    );
    assert!(
        receipts
            .iter()
            .any(|(operation, state, _)| operation == "null-initialization" && state == "Applied"),
        "{receipts:?}"
    );
    let output = ast_emitted_source_of(input).expect("native emission");
    assert!(
        output.contains("let mut s: Option<&[u8]> = None;"),
        "{output}"
    );
    assert!(verify::type_checks_str(&output), "{output}");
}
