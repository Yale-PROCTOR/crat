use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SkeletonView {
    pub skeleton: String,
    pub needs_transformation: bool,
    pub statement_dispositions: Vec<StatementDisposition>,
    pub statement_pair_metadata: Vec<StatementPairMetadata>,
}

impl SkeletonView {
    pub fn transform_labels(&self) -> Vec<u32> {
        fn visit(nodes: &[StatementDisposition], labels: &mut Vec<u32>) {
            for node in nodes {
                if node.disposition == StatementDispositionKind::Transform {
                    labels.push(node.label);
                }
                visit(&node.children, labels);
            }
        }
        let mut labels = vec![];
        visit(&self.statement_dispositions, &mut labels);
        labels
    }

    pub fn has_rule_application(&self) -> bool {
        fn visit(nodes: &[StatementDisposition]) -> bool {
            nodes.iter().any(|node| {
                node.disposition == StatementDispositionKind::RuleApplied || visit(&node.children)
            })
        }
        visit(&self.statement_dispositions)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct StatementDisposition {
    pub label: u32,
    pub disposition: StatementDispositionKind,
    pub children: Vec<StatementDisposition>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum StatementDispositionKind {
    Preserve,
    Transform,
    RuleApplied,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct StatementPairMetadata {
    pub label: u32,
    pub before_statement: String,
    pub pointer_variables_complete: bool,
    pub pointer_variables: Vec<PointerVariableMetadata>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PointerVariableMetadata {
    pub name: String,
    pub origin: PointerVariableOrigin,
    pub before_type: String,
    pub selected_target_type: String,
    pub before_type_is_inferred: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum PointerVariableOrigin {
    Parameter { index: u32 },
    Local { declaration_label: u32 },
}
