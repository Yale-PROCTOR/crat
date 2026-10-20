//! Compiler-backed licensing witnesses; fixture programs are never executed.

use std::collections::BTreeMap;

use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::mir::VarDebugInfoContents;

use super::super::{
    SlotKind,
    construction::{CopyLendMode, construct_bo_into, verify_bo_construction_counting},
    crate_slots::CrateSlots,
    export::{self, BoExport},
    mutability_facts::MutFacts,
    origins::compute_origins,
    slots::SlotOwner,
    solver::KindSolver,
};
use crate::utils::rustc::RustProgram;

pub(super) struct Fixture {
    pub(super) kinds: BTreeMap<String, SlotKind>,
    pub(super) accepted: bool,
    pub(super) export: BoExport,
    pub(super) origin_json: serde_json::Value,
    pub(super) construction_error: Option<String>,
    pub(super) commit_trace: Vec<String>,
}

impl Fixture {
    pub(super) fn assert_kind(&self, key: &str, expected: SlotKind) {
        assert!(
            self.accepted,
            "fixture declined before kind selection: {:?}",
            self.construction_error
        );
        assert_eq!(
            self.kinds.get(key),
            Some(&expected),
            "{key}: {:?}",
            self.kinds
        );
    }

    pub(super) fn assert_not_owning(&self, key: &str) {
        if self.accepted {
            let kind = self
                .kinds
                .get(key)
                .unwrap_or_else(|| panic!("missing {key}"));
            assert_ne!(*kind, SlotKind::Owning, "{key}");
        }
    }
}

pub(super) fn inspect(code: &str) -> Fixture {
    inspect_profile(code, false)
}

pub(super) fn inspect_era5_frame(code: &str) -> Fixture {
    inspect_profile(code, true)
}

fn inspect_profile(code: &str, attested_frame: bool) -> Fixture {
    ::utils::compilation::run_compiler_on_str(code, move |tcx| {
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
        let program = RustProgram {
            tcx,
            functions,
            structs,
        };
        let slots = CrateSlots::build(&program);
        let origins = compute_origins(&program);
        let facts = MutFacts::from_program(&program);
        let ((model, construction_error, commit_trace), export) = export::with_bo_export(|| {
            if attested_frame {
                use super::super::a5_overlap::{A5Mode, WholeProgramAttestation};
                let (result, trace) = super::super::borrow_verify::with_mode_a_commit_trace(|| {
                    super::super::construction::solve_bo_a5_config_reporting(
                        &program,
                        &slots,
                        &origins,
                        &facts,
                        A5Mode::PreciseReplay,
                        Some(WholeProgramAttestation::FrozenBenchmarkGraph),
                    )
                });
                let trace = trace.iter().map(|row| format!("{row:?}")).collect();
                return match result {
                    Ok(verified) => (Some(verified.model), None, trace),
                    Err(error) => (None, Some(format!("{error:?}")), trace),
                };
            }
            let solver = KindSolver::new(&slots);
            let construction = match construct_bo_into(
                &program,
                &slots,
                &origins,
                &facts,
                &solver,
                CopyLendMode::Baseline,
            ) {
                Ok(construction) => construction,
                Err(error) => return (None, Some(error.to_string()), Vec::new()),
            };
            let ((model, _), trace) = super::super::borrow_verify::with_mode_a_commit_trace(|| {
                verify_bo_construction_counting(
                    &program,
                    &slots,
                    &origins,
                    &solver,
                    &construction,
                    &facts,
                )
            });
            (
                model,
                None,
                trace.iter().map(|row| format!("{row:?}")).collect(),
            )
        });
        let mut kinds = BTreeMap::new();
        if let Some(model) = &model {
            for (&slot, &kind) in model {
                match slot {
                    super::super::solver::SlotRef::Local(function, id) => {
                        let slot = slots.fn_local_slots[&function].slot(id);
                        let SlotOwner::Local(local) = slot.owner else { panic!("local owner") };
                        let name = tcx.item_name(function.to_def_id());
                        kinds.insert(
                            format!("{name}::_{}@d{}", local.as_usize(), slot.depth),
                            kind,
                        );
                        if slot.depth != 0 {
                            continue;
                        }
                        if local.as_usize() == 0 {
                            kinds.insert(format!("{name}::_0"), kind);
                        }
                        let body = tcx
                            .mir_drops_elaborated_and_const_checked(function)
                            .borrow();
                        for info in &body.var_debug_info {
                            if let VarDebugInfoContents::Place(place) = info.value
                                && place.local == local
                                && place.projection.is_empty()
                            {
                                let key = format!("{name}::{}", info.name);
                                if let Some(previous) = kinds.insert(key.clone(), kind) {
                                    assert_eq!(previous, kind, "ambiguous named fixture key {key}");
                                }
                            }
                        }
                    }
                    super::super::solver::SlotRef::Field(id) => {
                        let slot = slots.field_slots.slot(id);
                        let SlotOwner::Field(field) = slot.owner else { panic!("field owner") };
                        let adt = tcx.adt_def(field.struct_did);
                        let definition = adt
                            .all_fields()
                            .nth(field.field_index)
                            .expect("field ordinal");
                        let key = format!(
                            "{}.{}",
                            tcx.item_name(field.struct_did.to_def_id()),
                            definition.name
                        );
                        kinds.insert(format!("{key}@d{}", slot.depth), kind);
                        if slot.depth == 0 {
                            kinds.insert(key, kind);
                        }
                    }
                }
            }
        }
        let origin_json = serde_json::from_str(
            &super::super::origin_evidence::collect(&program, &slots, &origins, Some(&export))
                .canonical_json(),
        )
        .expect("origin evidence JSON");
        Fixture {
            kinds,
            accepted: model.is_some(),
            export,
            origin_json,
            construction_error,
            commit_trace,
        }
    })
    .unwrap_or_else(|error| error.raise())
}

#[test]
fn ol13_endpoint_identity_and_selected_responsibility_control() {
    let fixture = inspect(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub unsafe fn f() { let p = malloc(4); *p = 1; free(p); }
"#,
    );
    fixture.assert_kind("f::p", SlotKind::Owning);
    assert_eq!(fixture.export.source_sites.len(), 1);
    assert_eq!(fixture.export.sink_sites.len(), 1);
    let owns = fixture
        .export
        .version_owns
        .as_ref()
        .expect("accepted ownership valuation");
    assert!(owns[fixture.export.source_sites[0].var]);
    assert!(owns[fixture.export.sink_sites[0].var]);
    let call = fixture.export.sink_sites[0]
        .call
        .as_ref()
        .expect("free identity");
    assert_eq!(call.callee, "free");
    assert!(call.function_path.ends_with("::f") || call.function_path == "f");
    let demand = fixture
        .export
        .demand_evidence
        .as_ref()
        .expect("T2 evidence");
    assert!(!demand.constructions.is_empty());
    assert!(
        demand
            .constructions
            .iter()
            .all(|c| !c.final_selections.is_empty())
    );
}

#[test]
fn ol14_source_dead_parameter_stays_protected_at_free() {
    let fixture = inspect(
        r#"
unsafe extern "C" { fn free(p: *mut i32); }
pub unsafe fn releases(a: *mut i32) -> i32 {
    let p = &raw mut *a;
    let value = *a;
    free(p);
    value
}
"#,
    );
    fixture.assert_kind("releases::a", SlotKind::Raw);
    assert!(!fixture.export.retirement_rounds.is_empty());
    assert!(
        fixture
            .export
            .source_events
            .as_ref()
            .expect("source inventory")
            .retirements
            .keys()
            .any(|k| k.role == super::super::source_events::SourceRole::Free)
    );
}

#[test]
fn ol15_realloc_outcomes_remain_distinct() {
    let fixture = inspect(
        r#"
unsafe extern "C" { fn realloc(p: *mut i32, n: usize) -> *mut i32; }
pub unsafe fn resize(p: *mut i32) -> *mut i32 {
    let q = realloc(p, 8);
    if q.is_null() { return p; }
    *q = 1;
    q
}
"#,
    );
    let events = fixture
        .export
        .source_events
        .as_ref()
        .expect("realloc inventory");
    assert_eq!(events.reallocations.len(), 1);
    let outcomes: std::collections::BTreeSet<_> = fixture
        .export
        .realloc_version_sites
        .iter()
        .map(|site| site.outcome)
        .collect();
    assert!(outcomes.contains(&super::super::realloc::ReallocOutcome::Success));
    assert!(outcomes.contains(&super::super::realloc::ReallocOutcome::Failure));
    if fixture.accepted {
        assert_ne!(fixture.kinds.get("resize::q"), Some(&SlotKind::Ref));
    }
}

#[test]
fn ol16_borrowed_call_does_not_take_the_callers_owner() {
    let fixture = inspect(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; fn free(p: *mut i32); }
pub unsafe fn read(p: *mut i32) -> i32 { *p }
pub unsafe fn release(p: *mut i32) { free(p); }
pub unsafe fn f() -> i32 {
    let p = malloc(4); *p = 5;
    let value = read(p);
    release(p);
    value
}
"#,
    );
    fixture.assert_kind("f::p", SlotKind::Owning);
    fixture.assert_kind("read::p", SlotKind::Ref);
    fixture.assert_kind("release::p", SlotKind::Owning);
}

#[test]
fn ol17_non_null_constant_is_not_an_owned_or_empty_store() {
    let fixture = inspect(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; }
pub struct H { pub p: *mut i32 }
pub unsafe fn choose(heap: bool) -> H {
    if heap { H { p: malloc(4) } } else { H { p: 4096usize as *mut i32 } }
}
"#,
    );
    fixture.assert_not_owning("H.p");
    let nullable = inspect(
        r#"
pub struct H { pub p: *mut i32 }
pub fn empty() -> H { H { p: 0 as *mut i32 } }
"#,
    );
    nullable.assert_kind("H.p", SlotKind::Ref);
}

#[test]
fn ol18_unproved_root_wrapper_is_not_licensed_by_nullable_shape() {
    // The two CROWN null-from-raw counter-witnesses remain G-JUST evidence.
    // This analysis control isolates their unresolved wrapper/cast inflow;
    // it does not treat null itself as a reason to make an owning field Raw.
    let fixture = inspect(
        r#"
unsafe extern "C" { fn opaque() -> *mut core::ffi::c_void; }
pub struct Node { pub child: *mut Node }
pub struct Tree { pub root: *mut Node }
pub unsafe fn wrapper() -> Tree { Tree { root: opaque() as *mut Node } }
"#,
    );
    fixture.assert_not_owning("Tree.root");
}

#[test]
fn ol19_return_transfers_but_live_local_finalization_is_not_relaxed() {
    let moved = inspect(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; }
pub unsafe fn make() -> *mut i32 { let p = malloc(4); *p = 1; p }
"#,
    );
    moved.assert_kind("make::p", SlotKind::Owning);
    moved.assert_kind("make::_0", SlotKind::Owning);
    let leaked = inspect(
        r#"
unsafe extern "C" { fn malloc(n: usize) -> *mut i32; }
pub unsafe fn leak() { let p = malloc(4); *p = 1; }
"#,
    );
    leaked.assert_kind("leak::p", SlotKind::Raw);
}

#[test]
fn ol20_recorded_ownership_equations_are_available_with_occurrences() {
    let fixture = inspect("pub unsafe fn relay(p: *mut i32) -> *mut i32 { let q = p; q }");
    assert!(fixture.accepted);
    assert!(
        !fixture.export.version_sites.is_empty(),
        "the baseline occurrence producer ran"
    );
    let functions = fixture.origin_json["functions"]
        .as_array()
        .expect("functions");
    let function = functions
        .iter()
        .find(|f| {
            f["function"]
                .as_str()
                .is_some_and(|name| name == "relay" || name.ends_with("::relay"))
        })
        .expect("relay");
    assert_eq!(
        function["ownership"]["equations"]["state"], "present",
        "ownership occurrences alone do not export transfer equations"
    );
    let equations = function["ownership"]["equations"]["value"]
        .as_array()
        .expect("equations");
    assert!(equations.iter().any(|eq| eq["operation"] == "linear"));
    assert!(
        equations
            .iter()
            .all(|eq| eq["point"].is_object() && eq["variables"].is_array())
    );
}

#[test]
fn e_equation_phi_rows_have_their_actual_join_block() {
    let fixture = inspect(
        "pub unsafe fn choose(p:*mut i32,q:*mut i32,c:bool)->*mut i32 { let mut out=p; if c {out=q;} out }",
    );
    let equations = fixture
        .export
        .ownership_equations
        .as_ref()
        .expect("recorded equations");
    assert!(
        equations.iter().any(|eq| eq.operation == "equal"
            && eq.point.phase == "phi"
            && eq.point.block.is_some()),
        "phi equalities need their actual join site"
    );
}

#[test]
fn e_equation_nested_capture_does_not_inherit_another_recording_point() {
    use super::super::{ownership_evidence, ssa::constraint::Var};
    let (_, outer) = with_fact_recording(|| {
        let _scope = ownership_evidence::construction();
        let variables = [Var::from_u32(1), Var::from_u32(2)];
        ownership_evidence::record("equal", &variables, None, None);
        let (_, inner) = export::with_bo_export(|| {
            ownership_evidence::record("equal", &variables, None, None);
        });
        assert!(
            inner.ownership_equations.is_none(),
            "inner capture has no construction"
        );
        ownership_evidence::record("equal", &variables, None, None);
    });
    // Optional observation cannot interrupt the normative constructor. The
    // inner observer has no completed construction; all three actual producer
    // calls remain in the outer constructor's completed snapshot.
    assert_eq!(outer.ownership_equations.as_ref().unwrap().len(), 3);
}

fn with_fact_recording<T>(run: impl FnOnce() -> T) -> (T, BoExport) {
    use super::facts;
    export::with_bo_export(|| {
        let builder = std::rc::Rc::new(std::cell::RefCell::new(facts::Facts::default()));
        let scope = facts::activate(&builder);
        let output = run();
        drop(scope);
        let facts = facts::freeze(builder, Default::default());
        export::record_ownership_facts(&facts);
        output
    })
}

#[test]
fn e_equation_missing_guard_and_invalid_phase_are_rejected() {
    use super::super::{ownership_evidence, ssa::constraint::Var};
    let (_, output) = with_fact_recording(|| {
        let _scope = ownership_evidence::construction();
        ownership_evidence::record(
            "linear",
            &[Var::from_u32(1), Var::from_u32(2), Var::from_u32(3)],
            None,
            None,
        );
    });
    let equation = &output.ownership_equations.as_ref().unwrap()[0];
    let mut bad = equation.clone();
    bad.operation = "guarded-copy".into();
    assert!(
        bad.validate().is_err(),
        "a guarded equation needs its predicate"
    );
    let mut bad = equation.clone();
    bad.point.phase = "invented".into();
    assert!(
        bad.validate().is_err(),
        "point phases are a closed vocabulary"
    );
    let mut bad = equation.clone();
    bad.assumption_class = Some("return-zero".into());
    assert!(
        bad.validate().is_err(),
        "non-assumptions cannot acquire an assumption class"
    );
    assert!(
        ownership_evidence::validate_function(&[equation.clone(), equation.clone()], "read")
            .is_err(),
        "equation IDs are unique in each function recording"
    );
    let mut bad = equation.clone();
    bad.point.phase = "function".into();
    bad.point.function = Some("other".into());
    assert!(
        ownership_evidence::validate_function(&[bad], "read").is_err(),
        "foreign functions are not correspondence"
    );
}

#[test]
fn e_equation_realloc_endpoints_keep_the_existing_outcome_and_operand_key() {
    let fixture = inspect(
        r#"
        unsafe extern "C" { fn realloc(p:*mut i32,n:usize)->*mut i32; fn free(p:*mut i32); }
        pub unsafe fn grow(p:*mut i32) { let q=realloc(p,8); if q.is_null() { free(p); } else { *q=1; free(q); } }
    "#,
    );
    let equations = fixture
        .export
        .ownership_equations
        .as_ref()
        .expect("captured");
    let endpoints: Vec<_> = equations
        .iter()
        .filter_map(|eq| eq.endpoint.as_ref())
        .filter(|ep| ep.callee == "realloc")
        .collect();
    assert!(
        !endpoints.is_empty(),
        "actual split assertions were recorded"
    );
    assert!(
        endpoints.iter().all(|ep| ep.outcome
            == Some(super::super::realloc::ReallocOutcome::Success)
            && ep.operand.is_some()),
        "realloc source/sink endpoint assertions belong to the exact success operand"
    );
    assert!(
        equations.iter().any(|eq| eq.point.phase == "realloc-edge"),
        "edge equations are not phi equations"
    );
}

#[test]
fn e_equation_ordinary_endpoint_cannot_move_to_another_emission_point() {
    let fixture = inspect(
        r#"
        unsafe extern "C" { fn malloc(n:usize)->*mut i32; fn free(p:*mut i32); }
        pub unsafe fn fresh() { let p=malloc(4); free(p); }
    "#,
    );
    let equations = fixture
        .export
        .ownership_equations
        .as_ref()
        .expect("captured");
    let source = equations
        .iter()
        .find(|eq| eq.operation == "source")
        .expect("source");
    assert!(source.validate().is_ok());
    let mut misplaced = source.clone();
    misplaced.endpoint.as_mut().unwrap().statement += 1;
    assert!(
        misplaced.validate().is_err(),
        "ordinary endpoint statement must match emission"
    );
    let mut misplaced = source.clone();
    misplaced.endpoint.as_mut().unwrap().block += 1;
    assert!(
        misplaced.validate().is_err(),
        "ordinary endpoint block must match emission"
    );
    let mut misplaced = source.clone();
    misplaced.point.phase = "phi".into();
    misplaced.point.statement = None;
    assert!(
        misplaced.validate().is_err(),
        "an ordinary endpoint is not a phi"
    );
}

#[test]
fn e_occurrence_transfer_assumptions_bind_exact_places_and_pointer_paths() {
    let fixture = inspect(
        r#"
        pub struct Node { left:*mut Node, right:*mut Node }
        pub unsafe fn replace(mut node:*mut Node, incoming:*mut Node)->*mut Node {
            node=incoming; node
        }
    "#,
    );
    let function = fixture.origin_json["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["function"] == "replace")
        .unwrap();
    assert_eq!(
        function["ownership"]["consumes"]["state"], "present",
        "actual consume windows must be exported"
    );
    let equations = function["ownership"]["equations"]["value"]
        .as_array()
        .unwrap();
    let transfers: Vec<_> = equations
        .iter()
        .filter(|row| row["assumption_class"] == "ssa-transfer")
        .collect();
    assert!(!transfers.is_empty());
    for equation in transfers {
        let transfer = &equation["transfer"];
        assert!(
            transfer.is_object(),
            "a transfer assumption carries its matched def/use pair"
        );
        assert_eq!(transfer["destination"]["state"], "present");
        assert_eq!(transfer["source"]["state"], "present");
        assert!(transfer["destination"]["value"]["path"].is_array());
        assert!(transfer["source"]["value"]["path"].is_array());
    }
}

#[test]
fn e_occurrence_final_zero_keeps_exact_local_ssa_and_path_keys() {
    let fixture = inspect(
        r#"
        unsafe extern "C" { fn malloc(n:usize)->*mut i32; }
        pub unsafe fn held() { let p=malloc(4); *p=7; }
    "#,
    );
    let function = fixture.origin_json["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|f| f["function"] == "held")
        .unwrap();
    assert_eq!(
        function["ownership"]["terminals"]["state"], "present",
        "return/finalization values need exact occurrences"
    );
    let rows = function["ownership"]["terminals"]["value"]
        .as_array()
        .unwrap();
    let equations = function["ownership"]["equations"]["value"]
        .as_array()
        .unwrap();
    let finals: Vec<_> = equations
        .iter()
        .filter(|e| e["assumption_class"] == "temporary-finalization")
        .collect();
    assert!(!finals.is_empty());
    for equation in finals {
        let var = equation["variables"][0].as_u64().unwrap();
        let found: Vec<_> = rows
            .iter()
            .filter(|row| {
                row["point"] == equation["point"]
                    && row["role"] == "local-final-zero"
                    && row["values"]["state"] == "present"
                    && row["values"]["value"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .any(|value| value["var"] == var)
            })
            .collect();
        assert_eq!(
            found.len(),
            1,
            "one exact final-value occurrence for each zero assumption"
        );
        assert!(found[0]["ssa"].is_number());
        assert!(
            found[0]["values"]["value"]
                .as_array()
                .unwrap()
                .iter()
                .all(|value| value["path"]["state"] == "present")
        );
    }
}

#[test]
fn e04_field_accesses_keep_distinct_bases_and_ordered_aggregate_operands() {
    let fixture = inspect(
        r#"
        pub struct Holder { ptr:*mut i32 }
        pub unsafe fn cells(p:*mut i32,q:*mut i32)->*mut i32 {
            let a=Holder {ptr:p}; let mut b=Holder {ptr:q}; b.ptr=a.ptr; b.ptr
        }
    "#,
    );
    let function = fixture.origin_json["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|f| f["function"] == "cells")
        .unwrap();
    let rows = function["occurrences"].as_array().unwrap();
    let aggregates: Vec<_> = rows
        .iter()
        .filter(|r| r["syntax"]["expression"]["kind"] == "aggregate")
        .collect();
    assert_eq!(aggregates.len(), 2, "both object constructions retained");
    assert_ne!(
        aggregates[0]["syntax"]["destination"]["local"],
        aggregates[1]["syntax"]["destination"]["local"]
    );
    for row in aggregates {
        let operands = row["syntax"]["expression"]["operands"].as_array().unwrap();
        assert_eq!(operands.len(), 1);
        assert_eq!(operands[0]["kind"], "move", "{row}");
    }
    assert!(
        rows.iter().any(|r| r["syntax"]["destination"]["projection"]
            .as_array()
            .is_some_and(|p| !p.is_empty())),
        "ordinary field stores keep their base and projection"
    );
}

#[test]
fn e10_immediate_origin_seeds_distinguish_borrow_null_and_unknown() {
    let fixture = inspect(
        r#"
        pub unsafe fn seeds()->*mut i32 {
            let mut x=1; let borrowed=&mut x as *mut i32;
            let empty=0 as *mut i32; let opaque=1 as *mut i32;
            if borrowed==empty { borrowed } else { opaque }
        }
    "#,
    );
    let function = fixture.origin_json["functions"]
        .as_array()
        .unwrap()
        .iter()
        .find(|f| f["function"] == "seeds")
        .unwrap();
    let rows = function["occurrences"].as_array().unwrap();
    for kind in ["borrow", "null", "unknown"] {
        assert!(
            rows.iter()
                .any(|row| row["syntax"]["immediate_origin"] == kind),
            "missing immediate {kind} origin evidence"
        );
    }
    assert_eq!(
        function["ownership"]["origin_closure"], "origin-closure-not-computed",
        "immediate syntax is not a closed origin proof"
    );
}
