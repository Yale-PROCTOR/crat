//! R216 recovery-base controls. The original source bytes are the oracle;
//! successful compilation alone cannot establish that all edits were removed.

use std::collections::{BTreeMap, BTreeSet};

use rustc_hash::FxHashSet;

use super::{
    ast_transform,
    bridge_receipt::SignatureClassId,
    decision::{Decision, emitability::UseEdit},
    plan::FileKey,
};

struct RevertProbe {
    input: BTreeMap<FileKey, String>,
    restored: Result<(BTreeMap<FileKey, String>, usize), String>,
}

fn revert_probe(input: &str, inject_unowned_use: bool) -> RevertProbe {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        // Capture precedes every HIR/MIR query, exactly as in production.
        let capture = ast_transform::capture_ast(tcx)?;
        let (mut table, ctx) = super::decide_table_with_ctx(tcx)?;
        let emission =
            super::emit_files(tcx, &table, &FxHashSet::default(), &ctx.retained_c9_plans)?;
        let ready = super::ready_classes(&emission.plan);
        assert!(!ready.is_empty(), "revert-all control needs a ready class");
        let root = emission.plan.root_file.as_ref().expect("fixture root key");
        let original = BTreeMap::from([(root.clone(), input.to_owned())]);
        let (candidate, rollbacks, edited, _) = super::round_files(
            tcx,
            &capture,
            &emission.plan,
            &emission.texts,
            &BTreeSet::new(),
            &BTreeSet::new(),
            Some(root),
            &table,
        )?;
        assert!(
            rollbacks.is_empty(),
            "initial control has a structural rollback"
        );
        assert!(edited > 0, "initial control did not place an edit");
        assert_ne!(
            candidate, original,
            "initial control did not change input bytes"
        );

        if inject_unowned_use {
            let mut orphan = table
                .entries
                .iter()
                .find_map(|(subject, decision)| match decision {
                    Decision::Ref { .. } => Some(subject.clone()),
                    Decision::InferredRef { .. }
                    | Decision::Slice { .. }
                    | Decision::Opt { .. }
                    | Decision::Box(_)
                    | Decision::Degraded(_) => None,
                })
                .expect("deliberate-fault control needs its ordinary Ref subject");
            let body_id = tcx
                .hir_node_by_def_id(orphan.fn_did)
                .body_id()
                .expect("control function body");
            let rustc_hir::ExprKind::Block(block, _) = tcx.hir_body(body_id).value.kind else {
                panic!("control function has a block body");
            };
            let tail = block.expr.expect("control's pointer-read tail");
            assert!(matches!(
                tail.kind,
                rustc_hir::ExprKind::Unary(rustc_hir::UnOp::Deref, _)
            ));
            let absent_owner = rustc_hir::def_id::CRATE_DEF_ID;
            assert!(
                !emission
                    .plan
                    .class_finalization
                    .classes
                    .contains_key(&SignatureClassId::of(absent_owner)),
                "fault owner must be outside the ready/held class universe"
            );
            // Deliberate fault: the original HIR use is attributed to an owner
            // absent from the sealed plan. The use graft has no later owner
            // check, so a missing recovery-base guard lets this edit survive.
            // No analysis result or production plan is modified on disk.
            orphan.fn_did = absent_owner;
            table.entries.push((
                orphan,
                Decision::Opt {
                    mutable: false,
                    slice: false,
                    uses: vec![UseEdit {
                        span: tail.span,
                        replacement: "73".to_owned(),
                        bridge_kind: "subject-use",
                    }],
                },
            ));
        }

        let restored = super::round_files(
            tcx,
            &capture,
            &emission.plan,
            &emission.texts,
            &ready,
            &BTreeSet::new(),
            Some(root),
            &table,
        )
        .map(|(files, rollbacks, edited, _)| {
            assert!(
                rollbacks.is_empty(),
                "revert-all produced a structural rollback"
            );
            (files, edited)
        });
        Ok::<_, String>(RevertProbe {
            input: original,
            restored,
        })
    })
    .expect("revert-all input fixture compiles")
    .expect("revert-all control reaches its recovery candidate")
}

#[test]
fn r216_revert_all_ready_classes_restores_exact_input_bytes() {
    for input in [
        "#![allow(dead_code, unused_unsafe)]\n\
         pub unsafe fn read(p:   *const i32) -> i32 {\n\
         \x20   // This comment and spacing must survive recovery.\n\
         \x20   *p\n\
         }\n",
        "#![allow(dead_code, unused_unsafe)]\n\
         pub struct Node { pub left: *const Node, pub right: *const Node, pub value: i32 }\n\
         pub unsafe fn inorder(root:   *const Node) -> i32 {\n\
         \x20   // BST-shaped recursive nullable arguments.\n\
         \x20   if root.is_null() { 0 } else {\n\
         \x20       inorder((*root).left) + (*root).value + inorder((*root).right)\n\
         \x20   }\n\
         }\n",
        "#![allow(dead_code, unused_unsafe)]\n\
         pub struct Node { pub left: *const Node, pub right: *const Node, pub height: i32 }\n\
         pub unsafe fn height(node: *const Node) -> i32 {\n\
         \x20   // AVL-shaped nullable field and call uses.\n\
         \x20   if node.is_null() { 0 } else { (*node).height }\n\
         }\n\
         pub unsafe fn balance(node: *const Node) -> i32 {\n\
         \x20   if node.is_null() { 0 } else { height((*node).left) - height((*node).right) }\n\
         }\n",
    ] {
        let probe = revert_probe(input, false);
        let (restored, edited) = probe.restored.expect("ordinary revert-all candidate");
        assert_eq!(
            restored, probe.input,
            "revert-all must restore every original byte"
        );
        assert_eq!(edited, 0, "revert-all must leave no claimed function edit");
    }
}

#[test]
fn r216_revert_all_rejects_an_injected_unowned_use() {
    let probe = revert_probe(
        "#![allow(dead_code, unused_unsafe)]\n\
         pub unsafe fn read(p:   *const i32) -> i32 {\n\
         \x20   // The injected 73 must never survive the recovery base.\n\
         \x20   *p\n\
         }\n",
        true,
    );
    match probe.restored {
        Err(reason) => assert!(
            reason.starts_with("revert-all-input-mismatch:"),
            "the deliberate fault must be caught by the input-identity guard: {reason}"
        ),
        Ok((candidate, _)) => panic!(
            "unowned edit escaped the recovery-base identity guard; input={:?}; candidate={candidate:?}",
            probe.input
        ),
    }
}
