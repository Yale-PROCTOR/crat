//! Returned-child controls over actual MIR, without a model or rewriter run.

use rustc_middle::{
    mir::{Location, TerminatorKind},
    ty::TyKind,
};

use super::decision::{
    raw_boundary::{raw_target_type, symbol_key},
    raw_boundary_contracts::classify_contract,
    return_alias,
    returned_child::{
        self, ChildAccess, ChildEdgeKind, ChildRoot, ChildSinkKind, ChildUnknownReason,
        ChildUseKind, ChildWriteKind, ReturnedChildEvidence,
    },
};

fn evidence(body_source: &str, expected_calls: usize) -> ReturnedChildEvidence {
    evidence_with_mir_premise(body_source, expected_calls, |_, _| {})
}

fn evidence_with_mir_premise(
    body_source: &str,
    expected_calls: usize,
    premise: for<'tcx> fn(rustc_middle::ty::TyCtxt<'tcx>, &rustc_middle::mir::Body<'tcx>),
) -> ReturnedChildEvidence {
    let input = format!(
        "#![allow(dead_code, unused_variables, unused_assignments, unused_mut, unused_unsafe)]\n\
        extern \"C\" {{\n\
            fn strchr(s: *const i8, c: i32) -> *mut i8;\n\
            fn opaque(p: *mut i8);\n\
        }}\n\
        pub struct Holder {{ saved: *mut i8 }}\n\
        static mut SAVED: *mut i8 = 0 as *mut i8;\n\
        {body_source}\n"
    );
    ::utils::compilation::run_compiler_on_str(&input, |tcx| {
        let caller = tcx.hir_body_owners().find(|owner| tcx.def_path_str(owner.to_def_id()) == "target")
            .expect("actual target body");
        let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
        premise(tcx, &body);
        let mut calls = body.basic_blocks.iter_enumerated().filter_map(|(block, data)| {
            let TerminatorKind::Call { func, args, destination, .. } = &data.terminator().kind else {
                return None;
            };
            let constant = func.constant()?;
            let TyKind::FnDef(callee, _) = *constant.ty().kind() else { return None };
            if tcx.item_name(callee).as_str() != "strchr" { return None; }
            assert!(matches!(tcx.hir_node_by_def_id(callee.expect_local()), rustc_hir::Node::ForeignItem(_)),
                "the selected symbol must be the actual foreign declaration");
            Some((data.terminator().source_info.span.lo().0,
                Location { block, statement_index: data.statements.len() }, callee, args, destination))
        }).collect::<Vec<_>>();
        assert_eq!(calls.len(), expected_calls, "actual resolved strchr call inventory: {body:?}");
        calls.sort_by_key(|call| call.0);
        let (_, call, callee, arguments, destination) = calls[0];
        let key = symbol_key(tcx, callee, &[caller]);
        let target = raw_target_type(tcx, arguments[0].node.ty(&*body, tcx))
            .expect("actual raw-pointer parent argument");
        let contract = classify_contract(&key, 0, &target).expect("sealed strchr parent contract");
        assert_eq!(contract.returns_alias_of, Some(0));
        let initial = return_alias::observe(&body, call);
        println!("RB-RETALIAS child READ premise: caller={caller:?}, callee={callee:?}, call={call:?}, initial={initial:#?}");
        let mut records = returned_child::derive(tcx, caller, call);
        assert_eq!(records.len(), 1, "one exact sealed parent-argument evidence record: {records:#?}");
        let record = records.remove(0);
        assert_eq!(record.key.caller, caller);
        assert_eq!(record.key.call, call);
        assert_eq!(record.key.callee, callee);
        assert_eq!(record.key.parent_argument_index, 0);
        assert_eq!(record.contract_provenance, contract.provenance);
        assert_eq!(record.initial, initial, "the existing observe API is preserved verbatim");
        assert!(matches!(record.parent, ChildRoot::Local(_)), "these controls have plain-local parents: {record:?}");
        assert_eq!(record.destination, ChildRoot::Local(destination.as_local().expect("plain-local initial result")));
        record
    }).expect("returned-child real-MIR fixture compiles")
}

#[test]
fn returned_child_discarded_and_named_unused_results_are_unused() {
    for source in [
        "pub unsafe fn target(p: *const i8) { strchr(p, 0); }",
        "pub unsafe fn target(p: *const i8) { let child = strchr(p, 0); }",
    ] {
        let record = evidence(source, 1);
        assert_eq!(
            record.access,
            ChildAccess::Unused,
            "bookkeeping is not pointer consumption: {record:?}"
        );
        assert!(record.outward_sinks.is_empty());
    }
}

#[test]
fn returned_child_copied_read_only_result_checks_its_value_and_pointee_uses() {
    let record = evidence(
        "pub unsafe fn target(p: *const i8) -> i8 {\n\
        let child = strchr(p, 0); let copied = child;\n\
        if copied.is_null() { 0 } else { *copied }\n\
    }",
        1,
    );
    assert!(
        record
            .edges
            .iter()
            .any(|edge| edge.kind == ChildEdgeKind::Copy),
        "{record:?}"
    );
    let ChildAccess::ReadOnly { checked_uses } = &record.access else {
        panic!("complete copied read-only child evidence required: {record:#?}");
    };
    assert!(
        checked_uses
            .iter()
            .any(|site| site.kind == ChildUseKind::PointerCopy)
    );
    assert!(
        checked_uses
            .iter()
            .any(|site| site.kind == ChildUseKind::PointerComparison)
    );
    assert!(
        checked_uses
            .iter()
            .any(|site| site.kind == ChildUseKind::PointeeRead)
    );
    assert!(record.outward_sinks.is_empty());
}

#[test]
fn returned_child_pointer_cast_and_returned_alias_edges_preserve_read_only_lineage() {
    let record = evidence(
        "pub unsafe fn target(p: *const i8) -> i8 {\n\
        let child = strchr(p, 0); let copied = child as *const i8;\n\
        if copied.is_null() { return 0; }\n\
        let nested = strchr(copied, 0);\n\
        if nested.is_null() { 0 } else { *nested }\n\
    }",
        2,
    );
    assert!(
        record
            .edges
            .iter()
            .any(|edge| edge.kind == ChildEdgeKind::PointerCast),
        "{record:?}"
    );
    assert!(
        record.edges.iter().any(|edge| matches!(
            edge.kind,
            ChildEdgeKind::ReturnedAlias {
                parent_argument_index: 0,
                ..
            }
        )),
        "{record:?}"
    );
    let ChildAccess::ReadOnly { checked_uses } = &record.access else {
        panic!("complete nested returned-child access evidence required: {record:#?}");
    };
    assert!(
        checked_uses
            .iter()
            .any(|site| site.kind == ChildUseKind::PointeeRead)
    );
    assert!(
        checked_uses
            .iter()
            .any(|site| site.kind == ChildUseKind::PointerCast)
    );
    assert!(
        checked_uses
            .iter()
            .any(|site| matches!(site.kind, ChildUseKind::ReturnedAliasArgument { .. }))
    );
    assert!(record.outward_sinks.is_empty());
}

#[test]
fn returned_child_copied_guarded_pointee_write_is_positive_write_evidence() {
    let record = evidence(
        "pub unsafe fn target(p: *const i8) {\n\
        let child = strchr(p, 0); let copied = child;\n\
        if !copied.is_null() { *copied = 7; }\n\
    }",
        1,
    );
    assert!(
        record
            .edges
            .iter()
            .any(|edge| edge.kind == ChildEdgeKind::Copy),
        "{record:?}"
    );
    assert!(
        matches!(&record.access, ChildAccess::Writes { sites, .. }
        if sites.iter().any(|site| site.kind == ChildWriteKind::PointeeStore)),
        "a copied descendant write cannot become parent-argument Read evidence: {record:#?}"
    );
}

#[test]
fn returned_child_copied_field_global_and_return_sinks_stay_positive() {
    for (source, expected_sink) in [
        (
            "pub unsafe fn target(p: *const i8, out: *mut Holder) { let child = strchr(p, 0); let copied = child; (*out).saved = copied; }",
            ChildSinkKind::FieldStore,
        ),
        (
            "pub unsafe fn target(p: *const i8) { let child = strchr(p, 0); let copied = child; SAVED = copied; }",
            ChildSinkKind::GlobalStore,
        ),
        (
            "pub unsafe fn target(p: *const i8) -> *mut i8 { let child = strchr(p, 0); let copied = child; copied }",
            ChildSinkKind::Return,
        ),
    ] {
        let record = evidence(source, 1);
        assert!(
            record
                .edges
                .iter()
                .any(|edge| edge.kind == ChildEdgeKind::Copy),
            "{record:?}"
        );
        assert!(
            record
                .outward_sinks
                .iter()
                .any(|sink| sink.kind == expected_sink),
            "the descendant's positive outward sink must survive access uncertainty: expected={expected_sink:?}, {record:#?}"
        );
        assert!(!matches!(record.access, ChildAccess::Unused));
    }
}

#[test]
fn returned_child_redefined_pointer_local_has_an_explicit_unknown_frontier() {
    let record = evidence(
        "pub unsafe fn target(p: *const i8, other: *mut i8) -> i8 {\n\
        let mut child = strchr(p, 0); child = other;\n\
        if child.is_null() { 0 } else { *child }\n\
    }",
        1,
    );
    assert!(
        matches!(&record.access, ChildAccess::Unknown { frontiers }
        if frontiers.iter().any(|site| site.reason == ChildUnknownReason::RedefinedLocal)),
        "redefinition cannot prove complete read-only lineage: {record:#?}"
    );
}

#[test]
fn returned_child_opaque_call_has_an_explicit_unknown_frontier() {
    let record = evidence(
        "pub unsafe fn target(p: *const i8) {\n\
        let child = strchr(p, 0); let copied = child; opaque(copied);\n\
    }",
        1,
    );
    assert!(
        matches!(&record.access, ChildAccess::Unknown { frontiers }
        if frontiers.iter().any(|site| site.reason == ChildUnknownReason::OpaqueCall)),
        "an unsealed call is not absence-of-write evidence: {record:#?}"
    );
}

#[test]
fn returned_child_positive_write_and_sink_survive_an_opaque_frontier() {
    let record = evidence(
        "pub unsafe fn target(p: *const i8) {\n\
        let child = strchr(p, 0); let copied = child; opaque(copied);\n\
        if !copied.is_null() { *copied = 7; } SAVED = copied;\n\
    }",
        1,
    );
    assert!(
        matches!(&record.access, ChildAccess::Writes { sites, unknown_frontiers }
        if !sites.is_empty() && unknown_frontiers.iter().any(|site| site.reason == ChildUnknownReason::OpaqueCall)),
        "positive write evidence and the opaque frontier are independently retained: {record:#?}"
    );
    assert!(
        record
            .outward_sinks
            .iter()
            .any(|sink| sink.kind == ChildSinkKind::GlobalStore)
    );
}

#[test]
fn returned_child_pointer_bearing_aggregate_load_is_an_unknown_frontier() {
    let source = "#[repr(C, packed)]\n\
        #[derive(Copy, Clone)]\n\
        pub struct ChildHeader { tag: i8, link: *mut i8 }\n\
        pub unsafe fn target(p: *const i8) {\n\
            let child = strchr(p, 0);\n\
            if child.is_null() { return; }\n\
            let header_ptr = child as *const ChildHeader;\n\
            let snapshot = *header_ptr;\n\
            let link = snapshot.link;\n\
            if !link.is_null() { *link = 7; }\n\
        }\n\
        pub unsafe fn entry() {\n\
            let mut header = ChildHeader { tag: 0, link: core::ptr::null_mut() };\n\
            header.link = &raw mut header.tag;\n\
            target((&raw const header).cast::<i8>());\n\
        }\n";
    // The concrete setup has a NUL first byte and an initialized self-link.
    // strchr returns the header's allocation start; packed alignment is one.
    // The fixture is inspected, never executed.
    let record = evidence_with_mir_premise(source, 1, |tcx, body| {
        use rustc_middle::mir::{Operand, ProjectionElem, Rvalue, StatementKind};
        let mut aggregate_locals = std::collections::BTreeSet::new();
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(assignment) = &statement.kind else { continue };
                let Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) = &assignment.1 else {
                    continue;
                };
                if !matches!(&place.projection[..], [ProjectionElem::Deref]) {
                    continue;
                }
                let ty = place.ty(body, tcx).ty;
                let TyKind::Adt(definition, arguments) = ty.kind() else { continue };
                if tcx.item_name(definition.did()).as_str() != "ChildHeader" {
                    continue;
                }
                assert!(
                    definition
                        .all_fields()
                        .any(|field| matches!(field.ty(tcx, arguments).kind(), TyKind::RawPtr(..))),
                    "the actual loaded aggregate must contain a raw pointer field"
                );
                aggregate_locals.insert(
                    assignment
                        .0
                        .as_local()
                        .expect("plain local whole-header copy"),
                );
            }
        }
        assert!(
            !aggregate_locals.is_empty(),
            "the actual MIR must load the whole pointer-bearing aggregate: {body:?}"
        );
        let mut pointer_field_locals = std::collections::BTreeSet::new();
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(assignment) = &statement.kind else { continue };
                let Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) = &assignment.1 else {
                    continue;
                };
                if aggregate_locals.contains(&place.local)
                    && place
                        .projection
                        .iter()
                        .any(|element| matches!(element, ProjectionElem::Field(..)))
                    && matches!(place.ty(body, tcx).ty.kind(), TyKind::RawPtr(..))
                {
                    pointer_field_locals
                        .insert(assignment.0.as_local().expect("copied pointer field local"));
                }
            }
        }
        assert!(
            !pointer_field_locals.is_empty(),
            "the copied aggregate's pointer field must actually be used: {body:?}"
        );
        assert!(
            body.basic_blocks
                .iter()
                .flat_map(|data| &data.statements)
                .any(|statement| {
                    matches!(&statement.kind, StatementKind::Assign(assignment)
                if pointer_field_locals.contains(&assignment.0.local)
                    && matches!(assignment.0.projection.first(), Some(ProjectionElem::Deref)))
                }),
            "the field-value pointer has an actual guarded pointee store"
        );
        println!(
            "RB-RETALIAS aggregate READ premise: aggregate_locals={aggregate_locals:?}, pointer_field_locals={pointer_field_locals:?}"
        );
    });
    assert!(
        matches!(&record.access, ChildAccess::Unknown { frontiers }
        if frontiers.iter().any(|site| site.reason == ChildUnknownReason::ProjectedPointerValue)),
        "without deep field provenance this aggregate load cannot prove complete ReadOnly access: {record:#?}"
    );
}
