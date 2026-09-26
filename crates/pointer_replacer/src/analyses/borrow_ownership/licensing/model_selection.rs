//! Same-model original-cell selections. This carrier is independent of
//! optional exports; facts identity is transient and never serialized.
use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet},
    rc::Rc,
};

use super::facts::{EquationId, Facts};

#[derive(Clone, Debug)]
pub(crate) struct Selection {
    facts: Rc<Facts>,
    values: BTreeMap<EquationId, bool>,
    traversal_owns: BTreeMap<super::transport::Node, bool>,
    fold_values: Option<super::fold_custody::Values>,
}
impl Selection {
    /// Evaluate actual original-cell predicates in the existing live Model.
    /// Missing/ambiguous bindings remain missing, never selected by default.
    pub(crate) fn from_model(
        facts: Rc<Facts>,
        mut evaluate: impl FnMut(&z3::ast::Bool) -> Option<bool>,
    ) -> Self {
        let expected: BTreeSet<_> = facts
            .equations
            .iter()
            .filter(|row| {
                matches!(
                    row.operation.as_str(),
                    "guarded-original-cell-frame" | "guarded-traversal-call" | "guarded-fold-call"
                )
            })
            .map(|row| EquationId {
                construction: row.point.construction,
                ordinal: row.ordinal,
            })
            .collect();
        let mut values = BTreeMap::new();
        for key in expected {
            let mut rows = facts.guards.iter().filter(|row| row.equation == key);
            if let Some(row) = rows.next()
                && rows.next().is_none()
                && let Some(value) = evaluate(&row.predicate)
            {
                values.insert(key, value);
            }
        }
        let required = facts
            .licensing
            .as_ref()
            .and_then(|f| super::traversal_call::valuation_nodes(&facts, &f.traversal_calls).ok())
            .unwrap_or_default();
        let traversal_owns = required
            .into_iter()
            .filter_map(|node| {
                facts
                    .ownership_asts
                    .get(super::super::ssa::constraint::Var::from_u32(node.var))
                    .and_then(|ast| evaluate(ast))
                    .map(|value| (node, value))
            })
            .collect();
        Self {
            fold_values: super::fold_custody::capture(&facts, &mut evaluate),
            facts,
            values,
            traversal_owns,
        }
    }

    pub(crate) fn fold_values(&self, facts: &Rc<Facts>) -> Option<super::fold_custody::Values> {
        Rc::ptr_eq(facts, &self.facts)
            .then(|| self.fold_values.clone())
            .flatten()
    }

    pub(crate) fn traversal_ownership(
        &self,
        facts: &Rc<Facts>,
    ) -> Option<Vec<(super::transport::Node, bool)>> {
        Rc::ptr_eq(facts, &self.facts)
            .then(|| self.traversal_owns.iter().map(|(n, v)| (*n, *v)).collect())
    }

    pub(crate) fn values(&self, facts: &Rc<Facts>) -> Option<BTreeMap<EquationId, bool>> {
        Rc::ptr_eq(facts, &self.facts).then(|| self.values.clone())
    }

    pub(crate) fn value(&self, facts: &Rc<Facts>, guard: EquationId) -> Option<bool> {
        Rc::ptr_eq(facts, &self.facts)
            .then(|| self.values.get(&guard).copied())
            .flatten()
    }
}
thread_local! {static CURRENT:RefCell<Option<Rc<Selection>>>=const {RefCell::new(None)};}
pub(crate) struct Scope(Option<Rc<Selection>>);
impl Drop for Scope {
    fn drop(&mut self) {
        CURRENT.with(|current| *current.borrow_mut() = self.0.take());
    }
}
pub(crate) fn enter(selection: Option<Rc<Selection>>) -> Scope {
    Scope(CURRENT.with(|current| current.replace(selection)))
}
pub(crate) fn current(facts: &Rc<Facts>) -> Option<Rc<Selection>> {
    CURRENT.with(|current| {
        current
            .borrow()
            .as_ref()
            .filter(|s| Rc::ptr_eq(facts, &s.facts))
            .cloned()
    })
}

#[cfg(test)]
mod tests {
    use rustc_hir::{ItemKind, OwnerNode};

    use super::{
        super::super::{
            SlotKind, a5_overlap::WholeProgramAttestation, coherence,
            construction::construct_bo_into_a16_refined, crate_slots::CrateSlots, export,
            mutability_facts::MutFacts, origins::compute_origins, solver::KindSolver,
        },
        *,
    };
    const CODE: &str = r#"
unsafe extern "C"{fn calloc(n:usize,size:usize)->*mut core::ffi::c_void;fn free(p:*mut core::ffi::c_void);}
pub struct Cell{ptr:*mut i32}
pub unsafe fn put(cell:*mut Cell,value:*mut i32){(*cell).ptr=value;}
pub unsafe fn f(){let owner=calloc(1,4) as *mut i32;let mut cell=Cell{ptr:0 as *mut i32};put(&mut cell,owner);free(cell.ptr as *mut core::ffi::c_void);}
"#;

    fn with_models(check: impl FnOnce(Rc<Facts>, EquationId, Rc<Selection>, Rc<Selection>) + Send) {
        ::utils::compilation::run_compiler_on_str(CODE, move |tcx| {
            let mut functions = Vec::new();
            let mut structs = Vec::new();
            for owner in tcx.hir_crate(()).owners.iter() {
                let Some(owner) = owner.as_owner() else { continue };
                let OwnerNode::Item(item) = owner.node() else { continue };
                match item.kind {
                    ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
                    ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
                    _ => {}
                }
            }
            let program = crate::utils::rustc::RustProgram {
                tcx,
                functions,
                structs,
            };
            let slots = CrateSlots::build(&program);
            let origins = compute_origins(&program);
            let mutability = MutFacts::from_program(&program);
            let _world = super::super::stack_entry::enter_world(Some(
                WholeProgramAttestation::FrozenBenchmarkGraph,
            ));
            assert!(!export::capturing(), "selection must not need BoExport");
            let solver = KindSolver::new(&slots);
            let (construction, _) =
                construct_bo_into_a16_refined(&program, &slots, &origins, &mutability, &solver)
                    .unwrap();
            coherence::constrain_field_ownership(&solver, &slots, &program);
            let facts = solver.ownership_facts().unwrap();
            let guard = facts
                .licensing
                .as_ref()
                .unwrap()
                .first_permissions
                .iter()
                .find(|p| p.proof.is_some())
                .unwrap()
                .guard;
            let field = facts.slot_refs["Cell::field0@d0"];
            let (positive, _) = solver
                .model_kinds_relaxing_reporting(&construction.selectors)
                .expect("source/free hard-admissible model");
            assert_eq!(positive[&field], SlotKind::Owning);
            let selected = solver
                .original_cell_selection()
                .expect("actual guard snapshot without optional export");
            assert_eq!(selected.value(&facts, guard), Some(true));
            solver.assume(field, SlotKind::Raw);
            let (negative, _) = solver
                .model_kinds_relaxing_reporting(&construction.selectors)
                .expect("retracted endpoint model");
            assert_eq!(negative[&field], SlotKind::Raw);
            let unselected = solver
                .original_cell_selection()
                .expect("replacement snapshot from the same Facts and new Model");
            assert_eq!(unselected.value(&facts, guard), Some(false));
            assert_eq!(
                selected.value(&facts, guard),
                Some(true),
                "an older model snapshot remains immutable"
            );
            assert!(!export::capturing());
            check(facts, guard, selected, unselected);
        })
        .unwrap_or_else(|error| error.raise());
    }

    #[test]
    fn c04_model_selection_reads_true_false_with_export_disabled_and_exact_facts() {
        with_models(|facts, guard, selected, unselected| {
            let wrong = Rc::new((*facts).clone());
            assert_eq!(
                selected.value(&wrong, guard),
                None,
                "equal metadata does not establish Facts identity: {guard:?}"
            );
            assert_eq!(unselected.value(&wrong, guard), None);
            assert!(!Rc::ptr_eq(&selected, &unselected));
            let unavailable = Selection::from_model(facts.clone(), |_| None);
            assert_eq!(
                unavailable.value(&facts, guard),
                None,
                "missing valuation is not a selected or false predicate: {guard:?}"
            );
            let mut duplicate = (*facts).clone();
            let binding = duplicate
                .guards
                .iter()
                .find(|g| g.equation == guard)
                .unwrap()
                .clone();
            duplicate.guards.push(binding);
            let duplicate = Rc::new(duplicate);
            let ambiguous = Selection::from_model(duplicate.clone(), |_| Some(true));
            assert_eq!(
                ambiguous.value(&duplicate, guard),
                None,
                "duplicate predicate binding cannot select: {guard:?}"
            );
        });
    }

    #[test]
    fn c04_model_selection_scope_restores_nested_models_none_and_unwind() {
        with_models(|facts, guard, selected, unselected| {
            assert!(current(&facts).is_none());
            {
                let _outer = enter(Some(selected.clone()));
                assert_eq!(current(&facts).unwrap().value(&facts, guard), Some(true));
                {
                    let _none = enter(None);
                    assert!(current(&facts).is_none());
                }
                assert_eq!(current(&facts).unwrap().value(&facts, guard), Some(true));
                {
                    let _inner = enter(Some(unselected.clone()));
                    assert_eq!(current(&facts).unwrap().value(&facts, guard), Some(false));
                    let wrong = Rc::new((*facts).clone());
                    assert!(current(&wrong).is_none());
                }
                let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    let _inner = enter(Some(unselected.clone()));
                    panic!("selection scope unwind witness");
                }));
                assert!(result.is_err());
                assert_eq!(current(&facts).unwrap().value(&facts, guard), Some(true));
            }
            assert!(current(&facts).is_none());
        });
    }
}
