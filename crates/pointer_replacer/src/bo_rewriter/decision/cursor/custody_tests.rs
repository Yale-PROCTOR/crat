//! Native admission first, then corrupt only the delivered-base evidence.
//! These controls exercise class withdrawal, final AST, and terminal receipts.

use std::collections::BTreeSet;

use rustc_hir::{HirId, PatKind};

use super::Decision;
use crate::bo_rewriter::{
    ast_transform,
    bridge_receipt::SignatureClassId,
    mechanical_receipt::{MechanicalFamily, MechanicalStage, MechanicalState},
};

const INPUT: &str = r#"
pub unsafe fn witness(output: &mut [i32], other: &mut [i32], raw: *mut i32) {
    let n = output.len();
    let mut p: *mut i32 = output.as_mut_ptr();
    let mut i: usize = 0;
    while i < n {
        *p = 7;
        p = p.add(1);
        i += 1;
    }
}
"#;

#[derive(Clone, Copy, Debug)]
enum Corruption {
    RawBase,
    WrongWindow,
    NonExpressionInitializer,
    WrongExpressionInitializer,
    DifferentDeliveredBase,
}

fn assert_withdrawn(corruption: Corruption) {
    let source = utils::compilation::run_compiler_on_str(INPUT, |tcx| {
        let capture = ast_transform::capture_ast(tcx).unwrap();
        let (mut table, ctx) = crate::bo_rewriter::decide_table_with_ctx(tcx).unwrap();
        let index = table
            .entries
            .iter()
            .position(|(subject, _)| subject.param_name.as_deref() == Some("p"))
            .expect("native cursor inventoried");
        let owner_did = table.entries[index].0.fn_did;
        let owner = SignatureClassId::of(owner_did);
        assert!(
            matches!(&table.entries[index].1, Decision::Cursor { plan, .. }
            if plan.delivered_base.is_some()),
            "fixture must earn production Cursor admission"
        );
        let baseline = crate::bo_rewriter::emit_files(
            tcx,
            &table,
            &Default::default(),
            &ctx.retained_c9_plans,
        )
        .unwrap();
        assert!(
            !baseline.plan.held_classes().contains(&owner),
            "control fixture must place before corruption: {:?}",
            baseline.plan.class_finalization
        );
        let baseline_events = baseline.plan.mechanical_receipts(&BTreeSet::new()).0;
        assert!(
            baseline_events
                .iter()
                .any(|event| event.key.owner_class == owner
                    && event.key.family == MechanicalFamily::Cursor
                    && event.stage == MechanicalStage::Terminal
                    && event.state == MechanicalState::Applied),
            "control fixture must have applied Cursor receipts"
        );

        let parameter = |name: &str| -> HirId {
            tcx.hir_body_owned_by(owner_did)
                .params
                .iter()
                .find_map(|param| match param.pat.kind {
                    PatKind::Binding(_, hir, ident, None) if ident.name.as_str() == name => {
                        Some(hir)
                    }
                    _ => None,
                })
                .expect("real parameter binding")
        };
        let Decision::Cursor { plan, .. } = &mut table.entries[index].1 else { unreachable!() };
        let base = plan.delivered_base.as_mut().unwrap();
        match corruption {
            Corruption::RawBase => {
                base.binding = parameter("raw");
                base.window_binding = base.binding;
            }
            Corruption::WrongWindow => base.window_binding = parameter("other"),
            Corruption::DifferentDeliveredBase => {
                base.binding = parameter("other");
                base.window_binding = base.binding;
            }
            Corruption::NonExpressionInitializer => base.initializer = Some(parameter("other")),
            Corruption::WrongExpressionInitializer => {
                base.initializer = Some(tcx.hir_body_owned_by(owner_did).value.hir_id)
            }
        }
        let emission = crate::bo_rewriter::emit_files(
            tcx,
            &table,
            &Default::default(),
            &ctx.retained_c9_plans,
        )
        .unwrap();
        let held = emission.plan.held_classes();
        assert!(
            held.contains(&owner),
            "{corruption:?}: malformed base did not hold Cursor owner: {:?}",
            emission.plan.class_finalization
        );
        let events = emission.plan.mechanical_receipts(&held).0;
        assert!(
            !events.iter().any(|event| event.key.owner_class == owner
                && event.key.family == MechanicalFamily::Cursor
                && event.stage == MechanicalStage::Terminal
                && event.state == MechanicalState::Applied),
            "{corruption:?}: withdrawn Cursor still reports Applied"
        );
        let reverts =
            ast_transform::revert_set_from_classes_and_atoms(&held, &BTreeSet::new(), &table)
                .unwrap();
        let (files, _, _, _) = ast_transform::ast_emitted_files_from(
            tcx,
            &capture,
            &reverts,
            emission.plan.root_file.as_ref(),
            &table,
            Some(&emission.plan.terminal_call_plans),
        )
        .unwrap();
        let source = files.into_values().next().unwrap();
        assert!(
            source.contains("p: *mut i32"),
            "{corruption:?}: raw declaration not restored: {source}"
        );
        assert!(
            source.contains("p = p.add(1)"),
            "{corruption:?}: original increment not restored: {source}"
        );
        assert!(
            !source.contains("::core::primitive::usize") && !source.contains("checked_add"),
            "{corruption:?}: Cursor syntax survived owner withdrawal: {source}"
        );
        source
    })
    .unwrap();
    super::tests::compile(&source, None);
}

#[test]
fn custody_native_cursor_raw_base_corruption_withdraws_owner_and_receipts() {
    assert_withdrawn(Corruption::RawBase);
}

#[test]
fn custody_native_cursor_wrong_window_withdraws_owner_and_receipts() {
    assert_withdrawn(Corruption::WrongWindow);
}

#[test]
fn custody_native_cursor_invalid_initializer_withdraws_owner_and_receipts() {
    assert_withdrawn(Corruption::NonExpressionInitializer);
}

#[test]
fn delivered_cursor_requires_its_exact_original_initializer() {
    assert_withdrawn(Corruption::WrongExpressionInitializer);
}

#[test]
fn custody_native_cursor_initializer_must_derive_from_the_claimed_base() {
    assert_withdrawn(Corruption::DifferentDeliveredBase);
}
