//! J07 exact seat-129 Read-B inventory. No model, worker, filesystem or solver API.
//! Authority TSV SHA256: 60869d0e423f4e0fd65a74ca55df025e3fbd4968cc76ecaa0f1490f0e924cdca.
//! Coverage alone never means measured-kind, analysis, or delivery acceptance.
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct Unit {
    pub(crate) record_key: String,
    pub(crate) program: String,
    pub(crate) unit_kind: String,
    pub(crate) crown_unit: String,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Error {
    Missing(String),
    Duplicate(String),
    Unexpected(String),
    IdentityMismatch(String),
}
const UNITS: &[(&str, &str, &str, &str)] = &[
    (
        "src::avl::Node::field1@d0",
        "avl",
        "field",
        "src::avl::Node::field1@d0",
    ),
    (
        "src::avl::Node::field2@d0",
        "avl",
        "field",
        "src::avl::Node::field2@d0",
    ),
    (
        "src::avl::insert::node",
        "avl",
        "variable",
        "src::avl::insert::node",
    ),
    (
        "src::avl::leftRotate::T2",
        "avl",
        "variable",
        "src::avl::leftRotate::T2",
    ),
    (
        "src::avl::leftRotate::x",
        "avl",
        "variable",
        "src::avl::leftRotate::x",
    ),
    (
        "src::avl::leftRotate::y",
        "avl",
        "variable",
        "src::avl::leftRotate::y",
    ),
    (
        "src::avl::newNode::node",
        "avl",
        "variable",
        "src::avl::newNode::node",
    ),
    (
        "src::avl::rightRotate::T2",
        "avl",
        "variable",
        "src::avl::rightRotate::T2",
    ),
    (
        "src::avl::rightRotate::x",
        "avl",
        "variable",
        "src::avl::rightRotate::x",
    ),
    (
        "src::avl::rightRotate::y",
        "avl",
        "variable",
        "src::avl::rightRotate::y",
    ),
    (
        "src::bst::node::field1@d0",
        "bst",
        "field",
        "src::bst::node::field1@d0",
    ),
    (
        "src::bst::node::field2@d0",
        "bst",
        "field",
        "src::bst::node::field2@d0",
    ),
    (
        "src::bst::deleteNode::root",
        "bst",
        "variable",
        "src::bst::deleteNode::root",
    ),
    (
        "src::bst::deleteNode::temp",
        "bst",
        "variable",
        "src::bst::deleteNode::temp",
    ),
    (
        "src::bst::deleteNode::temp_0",
        "bst",
        "variable",
        "src::bst::deleteNode::temp_0",
    ),
    (
        "src::bst::insert::node",
        "bst",
        "variable",
        "src::bst::insert::node",
    ),
    (
        "src::bst::newNode::temp",
        "bst",
        "variable",
        "src::bst::newNode::temp",
    ),
    (
        "src::buffer::buffer_free::self_0",
        "buffer",
        "variable",
        "src::buffer::buffer_free::self_0",
    ),
    (
        "src::buffer::buffer_new_with_copy::self_0",
        "buffer",
        "variable",
        "src::buffer::buffer_new_with_copy::self_0",
    ),
    (
        "src::buffer::buffer_new_with_size::self_0",
        "buffer",
        "variable",
        "src::buffer::buffer_new_with_size::self_0",
    ),
    (
        "src::buffer::buffer_new_with_string_length::self_0",
        "buffer",
        "variable",
        "src::buffer::buffer_new_with_string_length::self_0",
    ),
    (
        "src::buffer::buffer_slice::self_0",
        "buffer",
        "variable",
        "src::buffer::buffer_slice::self_0",
    ),
    (
        "src::test::test_buffer_append::buf",
        "buffer",
        "variable",
        "src::test::test_buffer_append::buf",
    ),
    (
        "src::test::test_buffer_append__grow::buf",
        "buffer",
        "variable",
        "src::test::test_buffer_append__grow::buf",
    ),
    (
        "src::test::test_buffer_append_n::buf",
        "buffer",
        "variable",
        "src::test::test_buffer_append_n::buf",
    ),
    (
        "src::test::test_buffer_clear::buf",
        "buffer",
        "variable",
        "src::test::test_buffer_clear::buf",
    ),
    (
        "src::test::test_buffer_compact::buf",
        "buffer",
        "variable",
        "src::test::test_buffer_compact::buf",
    ),
    (
        "src::test::test_buffer_equals::a",
        "buffer",
        "variable",
        "src::test::test_buffer_equals::a",
    ),
    (
        "src::test::test_buffer_equals::b",
        "buffer",
        "variable",
        "src::test::test_buffer_equals::b",
    ),
    (
        "src::test::test_buffer_fill::buf",
        "buffer",
        "variable",
        "src::test::test_buffer_fill::buf",
    ),
    (
        "src::test::test_buffer_indexof::buf",
        "buffer",
        "variable",
        "src::test::test_buffer_indexof::buf",
    ),
    (
        "src::test::test_buffer_new::buf",
        "buffer",
        "variable",
        "src::test::test_buffer_new::buf",
    ),
    (
        "src::test::test_buffer_new_with_size::buf",
        "buffer",
        "variable",
        "src::test::test_buffer_new_with_size::buf",
    ),
    (
        "src::test::test_buffer_prepend::buf",
        "buffer",
        "variable",
        "src::test::test_buffer_prepend::buf",
    ),
    (
        "src::test::test_buffer_slice::a",
        "buffer",
        "variable",
        "src::test::test_buffer_slice::a",
    ),
    (
        "src::test::test_buffer_slice::buf",
        "buffer",
        "variable",
        "src::test::test_buffer_slice::buf",
    ),
    (
        "src::test::test_buffer_slice__end::a",
        "buffer",
        "variable",
        "src::test::test_buffer_slice__end::a",
    ),
    (
        "src::test::test_buffer_slice__end::b",
        "buffer",
        "variable",
        "src::test::test_buffer_slice__end::b",
    ),
    (
        "src::test::test_buffer_slice__end::buf",
        "buffer",
        "variable",
        "src::test::test_buffer_slice__end::buf",
    ),
    (
        "src::test::test_buffer_slice__end::c",
        "buffer",
        "variable",
        "src::test::test_buffer_slice__end::c",
    ),
    (
        "src::test::test_buffer_slice__end_overflow::a",
        "buffer",
        "variable",
        "src::test::test_buffer_slice__end_overflow::a",
    ),
    (
        "src::test::test_buffer_slice__end_overflow::buf",
        "buffer",
        "variable",
        "src::test::test_buffer_slice__end_overflow::buf",
    ),
    (
        "src::test::test_buffer_slice__range_error::a",
        "buffer",
        "variable",
        "src::test::test_buffer_slice__range_error::a",
    ),
    (
        "src::test::test_buffer_slice__range_error::buf",
        "buffer",
        "variable",
        "src::test::test_buffer_slice__range_error::buf",
    ),
    (
        "src::test::test_buffer_trim::buf",
        "buffer",
        "variable",
        "src::test::test_buffer_trim::buf",
    ),
    (
        "src::ht::ht_create::table",
        "ht",
        "variable",
        "src::ht::ht_create::table",
    ),
    (
        "src::ht::ht_destroy::table",
        "ht",
        "variable",
        "src::ht::ht_destroy::table",
    ),
    (
        "src::src::bounds::quadtree_bounds::field0@d0",
        "quadtree",
        "field",
        "src::src::bounds::quadtree_bounds::field0@d0",
    ),
    (
        "src::src::bounds::quadtree_bounds::field1@d0",
        "quadtree",
        "field",
        "src::src::bounds::quadtree_bounds::field1@d0",
    ),
    (
        "src::src::quadtree::quadtree::field0@d0",
        "quadtree",
        "field",
        "src::src::quadtree::quadtree::field0@d0",
    ),
    (
        "src::src::bounds::quadtree_bounds_free::bounds",
        "quadtree",
        "variable",
        "src::src::bounds::quadtree_bounds_free::bounds",
    ),
    (
        "src::src::bounds::quadtree_bounds_new::bounds",
        "quadtree",
        "variable",
        "src::src::bounds::quadtree_bounds_new::bounds",
    ),
    (
        "src::src::node::quadtree_node_free::node",
        "quadtree",
        "variable",
        "src::src::node::quadtree_node_free::node",
    ),
    (
        "src::src::node::quadtree_node_new::node",
        "quadtree",
        "variable",
        "src::src::node::quadtree_node_new::node",
    ),
    (
        "src::src::point::quadtree_point_free::point",
        "quadtree",
        "variable",
        "src::src::point::quadtree_point_free::point",
    ),
    (
        "src::src::point::quadtree_point_new::point",
        "quadtree",
        "variable",
        "src::src::point::quadtree_point_new::point",
    ),
    (
        "src::src::quadtree::quadtree_free::tree",
        "quadtree",
        "variable",
        "src::src::quadtree::quadtree_free::tree",
    ),
    (
        "src::src::quadtree::quadtree_new::tree",
        "quadtree",
        "variable",
        "src::src::quadtree::quadtree_new::tree",
    ),
    (
        "src::test::test_bounds::bounds",
        "quadtree",
        "variable",
        "src::test::test_bounds::bounds",
    ),
    (
        "src::test::test_points::point",
        "quadtree",
        "variable",
        "src::test::test_points::point",
    ),
    (
        "src::test::test_tree::tree",
        "quadtree",
        "variable",
        "src::test::test_tree::tree",
    ),
];
pub(crate) fn expected() -> Vec<Unit> {
    UNITS
        .iter()
        .map(|&(record_key, program, unit_kind, crown_unit)| Unit {
            record_key: record_key.into(),
            program: program.into(),
            unit_kind: unit_kind.into(),
            crown_unit: crown_unit.into(),
        })
        .collect()
}
pub(crate) fn validate(rows: &[Unit]) -> Result<(), Vec<Error>> {
    let inventory = expected();
    let expected: BTreeMap<_, _> = inventory
        .iter()
        .map(|row| (row.record_key.as_str(), row))
        .collect();
    let mut seen = BTreeMap::new();
    let mut errors = Vec::new();
    for row in rows {
        if seen.insert(row.record_key.as_str(), ()).is_some() {
            errors.push(Error::Duplicate(row.record_key.clone()));
            continue;
        }
        match expected.get(row.record_key.as_str()) {
            None => errors.push(Error::Unexpected(row.record_key.clone())),
            Some(expected) if **expected != *row => {
                errors.push(Error::IdentityMismatch(row.record_key.clone()))
            }
            Some(_) => {}
        }
    }
    for key in expected.keys() {
        if !seen.contains_key(key) {
            errors.push(Error::Missing((*key).into()));
        }
    }
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn j07_read_b_complete_original_keys_are_order_independent() {
        let mut rows = expected();
        assert_eq!(rows.len(), 61);
        let mut counts = BTreeMap::new();
        for r in &rows {
            *counts.entry(r.program.as_str()).or_insert(0) += 1;
        }
        assert_eq!(
            counts,
            BTreeMap::from([
                ("avl", 10),
                ("bst", 7),
                ("buffer", 28),
                ("ht", 2),
                ("quadtree", 14)
            ])
        );
        assert_eq!(rows.iter().filter(|r| r.unit_kind == "field").count(), 7);
        assert_eq!(validate(&rows), Ok(()));
        rows.reverse();
        assert_eq!(validate(&rows), Ok(()));
    }
    #[test]
    fn j07_read_b_missing_and_duplicate_are_exact_identities() {
        let mut rows = expected();
        let removed = rows.pop().unwrap();
        assert_eq!(
            validate(&rows),
            Err(vec![Error::Missing(removed.record_key)])
        );
        let mut rows = expected();
        let duplicate = rows[0].clone();
        rows.push(duplicate.clone());
        assert_eq!(
            validate(&rows),
            Err(vec![Error::Duplicate(duplicate.record_key)])
        );
    }
    #[test]
    fn j07_read_b_same_count_substitution_and_program_change_fail() {
        let mut rows = expected();
        let old = rows[0].record_key.clone();
        rows[0].record_key = "invented replacement".into();
        let errors = validate(&rows).expect_err("count equality cannot replace a unit");
        assert!(errors.contains(&Error::Missing(old)));
        assert!(errors.contains(&Error::Unexpected("invented replacement".into())));
        for field in ["program", "unit_kind", "crown_unit"] {
            let mut rows = expected();
            let key = rows[0].record_key.clone();
            match field {
                "program" => rows[0].program = "buffer".into(),
                "unit_kind" => rows[0].unit_kind = "variable".into(),
                _ => rows[0].crown_unit = "different unit".into(),
            }
            assert_eq!(
                validate(&rows),
                Err(vec![Error::IdentityMismatch(key)]),
                "{field}"
            );
        }
    }
    #[test]
    fn j07_read_b_missing_program_cannot_shrink_the_denominator() {
        let rows: Vec<_> = expected()
            .into_iter()
            .filter(|r| r.program != "bst")
            .collect();
        let errors = validate(&rows).expect_err("missing bst units");
        assert_eq!(errors.len(), 7);
        assert!(errors.iter().all(|e| matches!(e, Error::Missing(_))));
    }
}
