use rustc_ast::{ExprKind, ItemKind, visit::Visitor as _};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LocalDefId;
use serde_json::json;
use utils::compilation::run_compiler_on_str;

use super::*;
use crate::{
    OBSERVATION_SCHEMA_VERSION, ObservationDocument, RuleDocument, StatementDisposition,
    StatementDispositionKind,
};

#[derive(Clone, Copy)]
enum RuleTarget {
    KeepSource,
    BoolFalse,
    IntegerSeven,
}

fn local_def(name: &str, tcx: TyCtxt<'_>) -> LocalDefId {
    tcx.hir_free_items()
        .find_map(|item_id| {
            let item = tcx.hir_item(item_id);
            item.kind
                .ident()
                .is_some_and(|ident| ident.name.as_str() == name)
                .then_some(item_id.owner_id.def_id)
        })
        .unwrap_or_else(|| panic!("missing function {name}"))
}

fn rule_for_region(
    source: &str,
    function_name: &str,
    label: u32,
    select: impl Fn(&crate::observation::RuleRegion) -> bool,
    target: RuleTarget,
    tcx: TyCtxt<'_>,
) -> RuleDocument {
    let mut surface = utils::ast::parse_crate(source.to_owned());
    let mut mapper = utils::ir::AstToHirMapper::new(tcx);
    mapper.map_crate_to_mod(&mut surface, tcx.hir_root_module(), false);
    let ast_to_hir = mapper.ast_to_hir;
    let function = local_def(function_name, tcx);
    let mut item = surface
        .items
        .iter()
        .find(|item| {
            item.kind
                .ident()
                .is_some_and(|ident| ident.name.as_str() == function_name)
        })
        .unwrap()
        .clone();
    annotate_function(&mut item, &FxHashSet::default());
    let decisions = initial_pointer_decisions(
        &pointer_replacer::Config::default(),
        PointerDecisionOptions {
            assume_nonnegative_offsets: true,
        },
        tcx,
    );
    let catalog = rule_binding_catalog(&item, function, &decisions, &ast_to_hir, tcx);
    let ItemKind::Fn(box function_item) = &item.kind else { unreachable!() };
    let mut statements = FxHashMap::default();
    StatementByLabelCollector {
        statements: &mut statements,
    }
    .visit_block(function_item.body.as_ref().unwrap());
    let statement = statements
        .get(&label)
        .unwrap_or_else(|| panic!("missing statement label {label}"));
    let regions = select_rule_regions(statement, &catalog, &ast_to_hir, tcx)
        .unwrap_or_else(|| panic!("label {label} has invalid selected regions"));
    let region = regions
        .iter()
        .find(|region| select(region))
        .unwrap_or_else(|| panic!("label {label} has no requested selected region"));
    let mut observation = region.observation.clone();
    observation.target_expression = match target {
        RuleTarget::KeepSource => observation.source_expression.clone(),
        RuleTarget::BoolFalse => serde_json::from_value(json!({
            "kind": "literal",
            "value": {"kind": "bool", "value": false}
        }))
        .unwrap(),
        RuleTarget::IntegerSeven => serde_json::from_value(json!({
            "kind": "literal",
            "value": {"kind": "integer", "value": "7", "type": "i32"}
        }))
        .unwrap(),
    };
    crate::synthesize_rules(&[ObservationDocument {
        schema_version: OBSERVATION_SCHEMA_VERSION,
        observations: vec![observation.clone(), observation],
    }])
    .unwrap()
}

fn merge_rules(documents: impl IntoIterator<Item = RuleDocument>) -> RuleDocument {
    let mut merged = RuleDocument::default();
    for document in documents {
        merged.rules.extend(document.rules);
    }
    merged
}

fn function_record<'a>(records: &'a [ItemRecord], name: &str) -> &'a FunctionRecord {
    records
        .iter()
        .find_map(|record| match record {
            ItemRecord::Function(record) if record.name == name => Some(record.as_ref()),
            _ => None,
        })
        .unwrap_or_else(|| panic!("missing generated function {name}"))
}

fn metadata_labels(view: &SkeletonView) -> Vec<u32> {
    view.statement_pair_metadata
        .iter()
        .map(|metadata| metadata.label)
        .collect()
}

fn assert_node(
    node: &StatementDisposition,
    label: u32,
    disposition: StatementDispositionKind,
    children: &[(u32, StatementDispositionKind)],
) {
    assert_eq!(node.label, label);
    assert_eq!(node.disposition, disposition);
    assert_eq!(node.children.len(), children.len());
    for (child, (child_label, child_disposition)) in node.children.iter().zip(children) {
        assert_eq!(child.label, *child_label);
        assert_eq!(child.disposition, *child_disposition);
        assert!(child.children.is_empty());
    }
}

fn outer_if_condition(skeleton: &str) -> String {
    let parsed = utils::ast::parse_crate(skeleton.to_owned());
    let ItemKind::Fn(box function) = &parsed.items[0].kind else { unreachable!() };
    let statement = &function.body.as_ref().unwrap().stmts[0];
    let expression = crate::observation::statement_expression(statement).unwrap();
    let ExprKind::If(condition, _, _) = &expression.kind else { unreachable!() };
    pprust::expr_to_string(condition)
}

#[test]
fn compiler_emits_one_rule_complete_statement_view() {
    let source = "pub unsafe fn read(p: *mut i32) -> i32 { *p }";
    run_compiler_on_str(source, |tcx| {
        let rules = rule_for_region(source, "read", 0, |_| true, RuleTarget::IntegerSeven, tcx);
        let records = make_skeletons_with_rules(source, Some(&rules), tcx).unwrap();
        let record = function_record(&records, "read");
        assert_node(
            &record.baseline.statement_dispositions[0],
            0,
            StatementDispositionKind::Transform,
            &[],
        );
        assert_node(
            &record.applied.statement_dispositions[0],
            0,
            StatementDispositionKind::RuleApplied,
            &[],
        );
        assert!(record.baseline.needs_transformation);
        assert!(!record.applied.needs_transformation);
        assert_eq!(metadata_labels(&record.baseline), vec![0]);
        assert!(record.applied.statement_pair_metadata.is_empty());
        assert_ne!(record.baseline.skeleton, record.applied.skeleton);
        assert!(
            record.applied.skeleton.contains("7i32"),
            "{}",
            record.applied.skeleton
        );
    })
    .unwrap();
}

#[test]
fn compiler_emits_rule_applied_outer_with_open_child() {
    let source = r#"
pub unsafe fn inspect(p: *mut i32) {
    if p.is_null() {
        *p = 1;
    }
}
"#;
    run_compiler_on_str(source, |tcx| {
        let rules = rule_for_region(
            source,
            "inspect",
            0,
            |region| {
                serde_json::to_string(&region.observation.source_expression)
                    .unwrap()
                    .contains("is_null")
            },
            RuleTarget::BoolFalse,
            tcx,
        );
        let records = make_skeletons_with_rules(source, Some(&rules), tcx).unwrap();
        let record = function_record(&records, "inspect");
        assert_node(
            &record.baseline.statement_dispositions[0],
            0,
            StatementDispositionKind::Transform,
            &[(1, StatementDispositionKind::Transform)],
        );
        assert_node(
            &record.applied.statement_dispositions[0],
            0,
            StatementDispositionKind::RuleApplied,
            &[(1, StatementDispositionKind::Transform)],
        );
        assert!(record.baseline.needs_transformation);
        assert!(record.applied.needs_transformation);
        assert_eq!(metadata_labels(&record.baseline), vec![0, 1]);
        assert_eq!(metadata_labels(&record.applied), vec![1]);
        assert_ne!(
            outer_if_condition(&record.baseline.skeleton),
            outer_if_condition(&record.applied.skeleton)
        );
        assert_eq!(outer_if_condition(&record.applied.skeleton), "false");
    })
    .unwrap();
}

#[test]
fn compiler_emits_transform_outer_with_rule_applied_child() {
    let source = r#"
pub unsafe fn update(p: *mut i32) {
    if p.is_null() {
        *p = 1;
    }
}
"#;
    run_compiler_on_str(source, |tcx| {
        let rules = rule_for_region(
            source,
            "update",
            1,
            |region| region.observation.lhs,
            RuleTarget::KeepSource,
            tcx,
        );
        let records = make_skeletons_with_rules(source, Some(&rules), tcx).unwrap();
        let record = function_record(&records, "update");
        assert_node(
            &record.baseline.statement_dispositions[0],
            0,
            StatementDispositionKind::Transform,
            &[(1, StatementDispositionKind::Transform)],
        );
        assert_node(
            &record.applied.statement_dispositions[0],
            0,
            StatementDispositionKind::Transform,
            &[(1, StatementDispositionKind::RuleApplied)],
        );
        assert!(record.baseline.needs_transformation);
        assert!(record.applied.needs_transformation);
        assert_eq!(metadata_labels(&record.baseline), vec![0, 1]);
        assert_eq!(metadata_labels(&record.applied), vec![0]);
        assert_eq!(
            outer_if_condition(&record.baseline.skeleton),
            outer_if_condition(&record.applied.skeleton)
        );
        assert_ne!(record.baseline.skeleton, record.applied.skeleton);
    })
    .unwrap();
}

#[test]
fn partial_parent_coverage_keeps_its_baseline_payload_while_child_applies() {
    let source = r#"
pub unsafe fn update(p: *mut i32, q: *mut i32, r: *mut i32) {
    if p.is_null() && *q == 0 {
        *r = 1;
    }
}
"#;
    run_compiler_on_str(source, |tcx| {
        let condition = rule_for_region(
            source,
            "update",
            0,
            |region| {
                serde_json::to_string(&region.observation.source_expression)
                    .unwrap()
                    .contains("is_null")
            },
            RuleTarget::BoolFalse,
            tcx,
        );
        let child = rule_for_region(
            source,
            "update",
            1,
            |region| region.observation.lhs,
            RuleTarget::KeepSource,
            tcx,
        );
        let rules = merge_rules([condition, child]);
        let records = make_skeletons_with_rules(source, Some(&rules), tcx).unwrap();
        let record = function_record(&records, "update");
        assert_node(
            &record.baseline.statement_dispositions[0],
            0,
            StatementDispositionKind::Transform,
            &[(1, StatementDispositionKind::Transform)],
        );
        assert_node(
            &record.applied.statement_dispositions[0],
            0,
            StatementDispositionKind::Transform,
            &[(1, StatementDispositionKind::RuleApplied)],
        );
        assert!(record.baseline.needs_transformation);
        assert!(record.applied.needs_transformation);
        assert_eq!(metadata_labels(&record.baseline), vec![0, 1]);
        assert_eq!(metadata_labels(&record.applied), vec![0]);
        assert_eq!(
            outer_if_condition(&record.baseline.skeleton),
            outer_if_condition(&record.applied.skeleton),
            "one uncovered condition region must discard the tentative parent rewrite"
        );
        assert_ne!(
            record.baseline.skeleton, record.applied.skeleton,
            "the independently complete nested label should still apply"
        );
    })
    .unwrap();
}
