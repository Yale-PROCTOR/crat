//! Wave-6o reductions of binn::binn_alloc_item and bzip2::mkCell.
use super::{decision::Decision, emit_tests::ast_emitted_source_of, verify};

const ALLOCATOR: &str = r#"
#![allow(dead_code, unused_mut, non_snake_case)]
unsafe extern "C" { fn myMalloc(size: usize) -> *mut core::ffi::c_void; }
"#;

fn admitted_raw_return(input: &str, function: &str, binding: &str, null: &str) {
    assert!(verify::type_checks_str(input));
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (table, ctx) = super::decide_table_with_ctx(tcx).expect("native decisions");
        let (subject, decision) = table
            .entries
            .iter()
            .find(|(subject, _)| {
                tcx.item_name(subject.fn_did.to_def_id()).as_str() == function
                    && subject.param_name.as_deref() == Some(binding)
            })
            .expect("corpus-derived local");
        assert!(
            matches!(decision, Decision::Opt { slice: false, .. }),
            "raw return must admit {function}::{binding}: {decision:?}"
        );
        assert!(
            table.option_receipts.iter().any(|receipt| {
                receipt.operation == "return-raw"
                    && receipt.obligation.intended_terminal_state
                        == super::mechanical_receipt::MechanicalState::Applied
                    && receipt.retention == super::mechanical_receipt::MechanicalRetention::None
                    && receipt.target_form == "raw"
                    && receipt.obligation.planned.key.subject
                        == super::mechanical_receipt::MechanicalSubjectKey::Local {
                            owner: subject.fn_did,
                            mir_local: subject.local.as_u32(),
                            slot_depth: 0,
                        }
            }),
            "raw return needs its applied terminal-move receipt"
        );
        let emission = super::emit_files(
            tcx,
            &table,
            &rustc_hash::FxHashSet::default(),
            &ctx.retained_c9_plans,
        )
        .expect("prepared class");
        assert!(
            emission.plan.class_finalization.classes
                [&super::bridge_receipt::SignatureClassId::of(subject.fn_did)]
                .is_ready(),
            "raw return class must be ready"
        );
    })
    .expect("fixture compiler context");
    let output = ast_emitted_source_of(input).expect("native emission");
    assert!(output.contains(&format!("{binding}: Option<")), "{output}");
    assert!(
        output
            .split_whitespace()
            .collect::<String>()
            .contains(&format!("return{binding}.map_or(core::ptr::{null}::<")),
        "return bridge must preserve None: {output}"
    );
    eprintln!("WAVE6O_OUTPUT_BEGIN {function}\n{output}\nWAVE6O_OUTPUT_END");
    assert!(
        verify::type_checks_str(&output),
        "emitted raw return must compile: {output}"
    );
}

#[test]
fn wave6o_binn_alloc_item_raw_return() {
    let input = format!(
        r#"{ALLOCATOR}
#[repr(C)] struct Binn {{ header: i32, allocated: i32 }}
unsafe fn binn_alloc_item() -> *mut Binn {{
    let mut item: *mut Binn = 0 as *mut Binn;
    item = myMalloc(core::mem::size_of::<Binn>()) as *mut Binn;
    if !item.is_null() {{ (*item).header = 0x1f22b11f; (*item).allocated = 1; }}
    return item;
}}
"#
    );
    admitted_raw_return(&input, "binn_alloc_item", "item", "null_mut");
}

#[test]
fn wave6o_bzip2_mkcell_raw_return() {
    let input = format!(
        r#"{ALLOCATOR}
#[repr(C)] struct Cell {{ name: *mut i8, link: *mut Cell }}
unsafe fn mkCell() -> *mut Cell {{
    let mut c: *mut Cell = 0 as *mut Cell;
    c = myMalloc(core::mem::size_of::<Cell>()) as *mut Cell;
    (*c).name = 0 as *mut i8;
    (*c).link = 0 as *mut Cell;
    return c;
}}
"#
    );
    admitted_raw_return(&input, "mkCell", "c", "null_mut");
}

#[test]
fn wave6o_shared_local_const_raw_return() {
    let input = format!(
        r#"{ALLOCATOR}
unsafe fn shared_return() -> *const i32 {{
    let mut p: *const i32 = 0 as *const i32;
    p = myMalloc(core::mem::size_of::<i32>()) as *const i32;
    if p.is_null() {{ return p; }}
    let value = *p;
    return p;
}}
"#
    );
    admitted_raw_return(&input, "shared_return", "p", "null");
}

#[test]
fn wave6o_mutable_local_const_raw_return() {
    let input = format!(
        r#"{ALLOCATOR}
unsafe fn const_return() -> *const i32 {{
    let mut p: *mut i32 = 0 as *mut i32;
    p = myMalloc(core::mem::size_of::<i32>()) as *mut i32;
    if !p.is_null() {{ *p = 42; }}
    return p;
}}
"#
    );
    admitted_raw_return(&input, "const_return", "p", "null");
}

#[test]
fn wave6o_shared_to_mutable_raw_return_keeps_typed_hold() {
    let input = format!(
        r#"{ALLOCATOR}
unsafe fn held_return() -> *mut i32 {{
    let mut p: *mut i32 = 0 as *mut i32;
    p = myMalloc(core::mem::size_of::<i32>()) as *mut i32;
    if !p.is_null() {{ let value = *p; }}
    return p;
}}
"#
    );
    ::utils::compilation::run_compiler_on_str(&input, |tcx| {
        let table = super::decide_table(tcx).expect("typed refusal decisions");
        assert!(
            table.option_receipts.iter().any(|receipt| {
                format!("{:?}", receipt.obligation.intended_terminal_reason)
                    .contains("option-raw-return:shared-to-mut-held")
            }),
            "shared-to-mutable refusal must remain receipted: {:?}",
            table.option_receipts
        );
        assert!(
            !table
                .option_receipts
                .iter()
                .any(|receipt| receipt.operation == "return-raw"
                    && receipt.obligation.intended_terminal_state
                        == super::mechanical_receipt::MechanicalState::Applied)
        );
    })
    .expect("refusal compiler context");
    let output = ast_emitted_source_of(&input).expect("refusal emission");
    assert!(verify::type_checks_str(&output), "{output}");
}
