use super::{
    super::{Decision, cursor_native::CursorPlan, seam::GlueSpec},
    *,
};

fn cursor(mutable: bool) -> Decision {
    Decision::Cursor {
        mutable,
        plan: CursorPlan {
            use_hirs: vec![],
            extent: 4,
            bridges: vec![],
            uses: Vec::new(),
            base: Local::from_u32(1),
            component: Vec::new(),
        },
    }
}

fn target(mutability: RawMutability) -> RawTargetType {
    RawTargetType {
        rendered: format!(
            "*{} i32",
            if mutability == RawMutability::Mut {
                "mut"
            } else {
                "const"
            }
        ),
        pointee: "i32".into(),
        mutability,
        depth2: None,
    }
}

#[test]
fn cursor_raw_templates_keep_current_index_and_one_operand_evaluation() {
    for (mutable, target_mutability, expected, method) in [
        (
            false,
            RawMutability::Const,
            BridgeTemplate::CursorSharedToRawConst,
            "as_ptr",
        ),
        (
            true,
            RawMutability::Mut,
            BridgeTemplate::CursorMutToRawMut,
            "as_mut_ptr",
        ),
        (
            true,
            RawMutability::Const,
            BridgeTemplate::CursorMutToRawConst,
            "as_mut_ptr",
        ),
    ] {
        let template =
            template_for(&cursor(mutable), &target(target_mutability), None, false).unwrap();
        assert_eq!(template, expected);
        let BridgeRender::Edit(text) = template
            .render("source_cursor", target_mutability, false, Some("i32"))
            .unwrap()
        else {
            panic!("cursor boundary must emit an explicit current-index view")
        };
        assert_eq!(text.matches("source_cursor").count(), 1);
        assert!(
            text.contains(&format!(".0.{method}().add(__crat_cursor.1)")),
            "{text}"
        );
        assert!(text.contains(".cast::<i32>()"), "{text}");
        assert_eq!(
            text.contains(".cast_const()"),
            mutable && target_mutability == RawMutability::Const
        );
        assert!(template.key().starts_with("cursor-"));
    }
}

#[test]
fn cursor_raw_glue_preserves_unsafe_context() {
    let spec = GlueSpec::raw_boundary_target(
        BridgeTemplate::CursorSharedToRawConst,
        &target(RawMutability::Const),
        false,
        true,
    );
    assert!(spec.requires_unsafe());
    let safe = spec.render_in_context("p", false).unwrap();
    let unsafe_fn = spec.render_in_context("p", true).unwrap();
    assert_eq!(safe, format!("unsafe {{ {unsafe_fn} }}"));
    assert!(unsafe_fn.contains(".add(__crat_cursor.1)"));
}

#[test]
fn cursor_raw_rejects_unlicensed_target_and_ownership_forms() {
    assert_eq!(
        template_for(&cursor(false), &target(RawMutability::Mut), None, true),
        Err(RawBoundaryBlockReason::SharedToMut)
    );
    let mut void = target(RawMutability::Const);
    void.pointee = "core::ffi::c_void".into();
    assert_eq!(
        template_for(&cursor(false), &void, None, false),
        Err(RawBoundaryBlockReason::TemplateUnavailable)
    );
    let mut depth2 = target(RawMutability::Mut);
    depth2.depth2 = Some(Depth2Target {
        inner_pointee: "i32".into(),
        inner_mutability: RawMutability::Mut,
        thin: true,
    });
    assert_eq!(
        template_for(&cursor(true), &depth2, None, false),
        Err(RawBoundaryBlockReason::TemplateUnavailable)
    );
    assert_eq!(
        template_for(
            &cursor(true),
            &target(RawMutability::Mut),
            Some(super::super::raw_boundary_contracts::OwnershipContract::Consume),
            false
        ),
        Err(RawBoundaryBlockReason::OwnershipTransfer)
    );
}

#[test]
fn cursor_unknown_retention_cannot_enter_legacy_t2_waiver() {
    let unknown = RetentionVerdict::Unknown {
        reason: RetentionUnknownReason::LocalSummaryUnknown,
        frontier: Vec::new(),
    };
    assert_eq!(
        cursor_retention_permit(&cursor(true), &unknown),
        Err(RawBoundaryBlockReason::TemplateUnavailable)
    );
    assert_eq!(
        cursor_retention_permit(&cursor(false), &unknown),
        Err(RawBoundaryBlockReason::TemplateUnavailable)
    );
    assert_eq!(
        cursor_retention_permit(&Decision::Ref { mutable: true }, &unknown),
        Ok(())
    );
    let no_retain = RetentionVerdict::NoRetain {
        certificate: RetentionCertificate {
            function: "callee".into(),
            argument_index: 0,
            steps: Vec::new(),
            attestation: "test-only",
        },
    };
    assert_eq!(cursor_retention_permit(&cursor(true), &no_retain), Ok(()));
}
