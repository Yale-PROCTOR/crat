//! E03 recording contracts. Embedded programs are analyzed, never executed.

use serde_json::{Value, json};

use super::tests::inspect;

fn function<'a>(evidence: &'a Value, name: &str) -> &'a Value {
    evidence["functions"]
        .as_array()
        .expect("function evidence")
        .iter()
        .find(|row| row["function"] == name)
        .unwrap_or_else(|| panic!("missing function {name}"))
}

fn substitutions(function: &Value) -> &[Value] {
    let recording = &function["ownership"]["boundary_substitutions"];
    assert_eq!(
        recording["state"], "present",
        "E03 must record actual boundary substitutions, including missing positions"
    );
    recording["value"].as_array().expect("boundary rows")
}

fn present(value: &Value) -> &Value {
    assert_eq!(value["state"], "present", "{value}");
    &value["value"]
}

fn number(value: &Value) -> u64 {
    value
        .as_u64()
        .unwrap_or_else(|| panic!("expected Var/offset: {value}"))
}

fn in_window(variable: &Value, window: &Value, start: &str, end: &str) {
    let variable = number(variable);
    assert!(
        number(&window[start]) <= variable && variable < number(&window[end]),
        "matched Var {variable} lies outside {window}"
    );
}

fn has_equation(
    function: &Value,
    point: &Value,
    operation: &str,
    variables: &[u64],
    value: Value,
) -> bool {
    function["ownership"]["equations"]["value"]
        .as_array()
        .expect("actual ownership equations")
        .iter()
        .any(|equation| {
            equation["point"] == *point
                && equation["operation"] == operation
                && equation["variables"] == json!(variables)
                && equation["value"] == value
        })
}

#[test]
fn e03_return_receiver_and_exit_return_match_the_emitted_equations() {
    let fixture = inspect(
        r#"
pub unsafe fn identity(p: *mut i32) -> *mut i32 { p }
pub unsafe fn caller(p: *mut i32) -> *mut i32 {
    let result = identity(p);
    result
}
"#,
    );
    let caller = function(&fixture.origin_json, "caller");
    let rows: Vec<_> = substitutions(caller)
        .iter()
        .filter(|row| row["role"] == "return-receiver" && row["callee"] == "identity")
        .collect();
    assert_eq!(rows.len(), 1, "one actual return-receiver event");
    let row = rows[0];
    let actual = present(&row["actual"]);
    let formal = present(&row["formal"]);
    assert_eq!(actual["kind"], "use-def");
    assert_eq!(formal["kind"], "single");
    let pairs = row["matched"].as_array().expect("actual matcher pairs");
    assert!(!pairs.is_empty());
    for pair in pairs {
        let a = &pair["actual"];
        let f = &pair["formal"];
        assert_eq!(a["kind"], "use-def");
        assert_eq!(f["kind"], "single");
        in_window(&a["use_var"], actual, "use_start", "use_end");
        in_window(&a["def_var"], actual, "def_start", "def_end");
        in_window(&f["var"], formal, "start", "end");
        assert!(has_equation(
            caller,
            &row["point"],
            "assume",
            &[number(&a["use_var"])],
            json!(false),
        ));
        assert!(has_equation(
            caller,
            &row["point"],
            "equal",
            &[number(&a["def_var"]), number(&f["var"])],
            Value::Null,
        ));
    }

    let callee = function(&fixture.origin_json, "identity");
    let exits: Vec<_> = substitutions(callee)
        .iter()
        .filter(|row| row["role"] == "exit-return")
        .collect();
    assert_eq!(exits.len(), 1);
    let exit = exits[0];
    assert_eq!(present(&exit["actual"])["kind"], "single");
    assert_eq!(present(&exit["formal"]), formal);
    for pair in exit["matched"].as_array().expect("exit pairs") {
        assert!(has_equation(
            callee,
            &exit["point"],
            "equal",
            &[
                number(&pair["actual"]["var"]),
                number(&pair["formal"]["var"])
            ],
            Value::Null,
        ));
    }
}

#[test]
fn e03_reference_field_output_preserves_the_formal_peel_and_exact_matches() {
    let fixture = inspect(
        r#"
pub struct Holder { ptr: *mut i32 }
pub unsafe fn put(out: &mut Holder, incoming: *mut i32) {
    out.ptr = incoming;
}
pub unsafe fn caller(incoming: *mut i32) {
    let mut holder = Holder { ptr: 0 as *mut i32 };
    put(&mut holder, incoming);
}
"#,
    );
    let caller = function(&fixture.origin_json, "caller");
    let rows: Vec<_> = substitutions(caller)
        .iter()
        .filter(|row| {
            row["role"] == "call-argument" && row["callee"] == "put" && row["argument_index"] == 0
        })
        .collect();
    assert_eq!(rows.len(), 1);
    let row = rows[0];
    let actual = present(&row["actual"]);
    let formal = present(&row["formal"]);
    let peel = &row["reference_peel"];
    assert!(
        peel.is_object(),
        "the actual reference-proxy peel must be recorded"
    );
    let original = &peel["original_formal"];
    let effective = &peel["effective_formal"];
    let skipped = &peel["skipped"];
    assert_eq!(formal, effective);
    for prefix in ["use", "def"] {
        let start = format!("{prefix}_start");
        let end = format!("{prefix}_end");
        let variable = format!("{prefix}_var");
        assert_eq!(number(&original[&start]), number(&skipped[&variable]));
        assert_eq!(number(&effective[&start]), number(&original[&start]) + 1);
        assert_eq!(effective[&end], original[&end]);
    }
    let pairs = row["matched"].as_array().expect("actual matcher pairs");
    assert!(
        !pairs.is_empty(),
        "the payload field must have a matched window"
    );
    for pair in pairs {
        let a = &pair["actual"];
        let f = &pair["formal"];
        assert_eq!(a["kind"], "use-def");
        assert_eq!(f["kind"], "use-def");
        for prefix in ["use", "def"] {
            let start = format!("{prefix}_start");
            let end = format!("{prefix}_end");
            let variable = format!("{prefix}_var");
            in_window(&a[&variable], actual, &start, &end);
            in_window(&f[&variable], effective, &start, &end);
            assert_ne!(
                f[&variable], skipped[&variable],
                "peeled outer pair was not matched"
            );
            assert!(has_equation(
                caller,
                &row["point"],
                "equal",
                &[number(&f[&variable]), number(&a[&variable])],
                Value::Null,
            ));
        }
    }
}

#[test]
fn e03_scalar_and_constant_argument_positions_remain_explicit() {
    let fixture = inspect(
        r#"
pub unsafe fn target(before: i32, pointer: *mut i32, after: i32) {
    let _ = (before, pointer, after);
}
pub unsafe fn caller() { target(11, 0 as *mut i32, 22); }
"#,
    );
    let caller = function(&fixture.origin_json, "caller");
    let mut rows: Vec<_> = substitutions(caller)
        .iter()
        .filter(|row| row["role"] == "call-argument" && row["callee"] == "target")
        .collect();
    rows.sort_by_key(|row| number(&row["argument_index"]));
    assert_eq!(rows.len(), 3, "unrepresented positions must not disappear");
    for (index, row) in rows.into_iter().enumerate() {
        assert_eq!(row["argument_index"], index);
        assert_eq!(row["actual"]["state"], "missing");
        assert!(
            row["actual"]["value"]
                .as_str()
                .is_some_and(|reason| !reason.is_empty()),
            "missing correspondence needs its reason"
        );
        assert!(
            row["matched"]
                .as_array()
                .expect("recorded empty match list")
                .is_empty()
        );
    }
}

fn consume(function: &Value, ordinal: u64) -> &Value {
    present(&function["ownership"]["consumes"])
        .as_array()
        .expect("consume records")
        .iter()
        .find(|row| row["ordinal"] == ordinal)
        .unwrap_or_else(|| panic!("missing consume {ordinal}"))
}

fn source_call<'a>(function: &'a Value, point: &Value) -> &'a Value {
    function["occurrences"]
        .as_array()
        .expect("original source occurrences")
        .iter()
        .find(|row| {
            row["kind"] == "call"
                && row["site"]["block"] == point["block"]
                && row["site"]["statement"] == point["statement"]
        })
        .expect("original MIR call at the recorded boundary point")
}

fn same_consume_window(window: &Value, occurrence: &Value) {
    let projected = present(&occurrence["projected"]);
    for key in ["use_start", "use_end", "def_start", "def_end"] {
        assert_eq!(
            window[key], projected[key],
            "{key}: boundary/consume mismatch"
        );
    }
    assert!(occurrence["ssa_use"].is_u64());
    assert!(occurrence["ssa_def"].is_u64());
}

#[test]
fn e03_return_receiver_has_the_exact_current_site_consume() {
    let fixture = inspect(
        r#"
pub unsafe fn identity(p: *mut i32) -> *mut i32 { p }
pub unsafe fn caller(p: *mut i32) -> *mut i32 {
    let result = identity(p);
    result
}
"#,
    );
    let caller = function(&fixture.origin_json, "caller");
    let row = substitutions(caller)
        .iter()
        .find(|row| row["role"] == "return-receiver" && row["callee"] == "identity")
        .expect("return-receiver substitution");
    let ordinal = number(present(&row["actual_occurrence"]));
    let actual = consume(caller, ordinal);
    assert_eq!(
        actual["point"], row["point"],
        "receiver uses this call's consume"
    );
    same_consume_window(present(&row["actual"]), actual);
    assert_eq!(actual["projection"], json!([]));
    let original = source_call(caller, &row["point"]);
    assert_eq!(
        present(&original["destination"]),
        &json!(format!("caller::_{}@d0", number(&actual["local"]))),
        "the recorded consume belongs to the original MIR destination"
    );
}

#[test]
fn e03_call_arguments_name_their_exact_prior_proxy_registrations() {
    let fixture = inspect(
        r#"
pub struct Holder { ptr: *mut i32 }
pub unsafe fn visit(left: &mut Holder, right: &mut Holder) -> bool {
    left.ptr == right.ptr
}
pub unsafe fn caller(p: *mut i32, q: *mut i32) {
    let mut left = Holder { ptr: p };
    let mut right = Holder { ptr: q };
    let _ = visit(&mut left, &mut right);
    let _ = visit(&mut right, &mut left);
}
"#,
    );
    let caller = function(&fixture.origin_json, "caller");
    let rows: Vec<_> = substitutions(caller)
        .iter()
        .filter(|row| row["role"] == "call-argument" && row["callee"] == "visit")
        .collect();
    assert_eq!(rows.len(), 4, "two ordered arguments at each of two calls");
    let registrations = present(&caller["ownership"]["call_arg_registrations"])
        .as_array()
        .expect("actual call_arg registration events");
    let mut used = std::collections::BTreeSet::new();
    let mut selected_earlier_registration = false;
    for row in rows {
        let registration_id = number(present(&row["call_arg_registration"]));
        assert!(
            used.insert(registration_id),
            "different proxies/calls reused one registration"
        );
        let registration = registrations
            .iter()
            .find(|registration| registration["ordinal"] == registration_id)
            .expect("exact selected registration identity");
        assert_eq!(registration["point"]["function"], row["point"]["function"]);
        assert_eq!(
            registration["point"]["construction"],
            row["point"]["construction"]
        );
        assert_eq!(registration["point"]["block"], row["point"]["block"]);
        assert!(number(&registration["point"]["statement"]) < number(&row["point"]["statement"]));
        assert_eq!(registration["window"], *present(&row["actual"]));
        assert_eq!(registration["by_reference"], true);
        assert!(row["reference_peel"].is_object());

        let original = source_call(caller, &row["point"]);
        let index = number(&row["argument_index"]) as usize;
        assert_eq!(
            present(&original["arguments"][index]),
            &json!(format!(
                "caller::_{}@d0",
                number(&registration["proxy_local"])
            )),
            "registration must belong to this original argument proxy"
        );
        let occurrence_id = number(present(&registration["source_occurrence"]));
        assert_eq!(number(present(&row["actual_occurrence"])), occurrence_id);
        let actual = consume(caller, occurrence_id);
        assert_eq!(actual["point"], registration["point"]);
        same_consume_window(&registration["window"], actual);

        // This fixture has two reference registrations before each call. One
        // argument must retain the earlier registration rather than using the
        // most recently observed unrelated proxy.
        selected_earlier_registration |= registrations.iter().any(|other| {
            other["point"]["block"] == row["point"]["block"]
                && number(&other["point"]["statement"]) < number(&row["point"]["statement"])
                && number(&other["ordinal"]) > registration_id
        });
    }
    assert!(
        selected_earlier_registration,
        "the control must distinguish prior proxies"
    );
}

fn c02_borrowed_window(code: &str, minimum_components: usize) {
    super::graph_tests::with_facts(code, move |facts| {
        let snapshot =
            super::snapshot::Snapshot::capture(facts, 0).expect("real construction snapshot");
        let document = serde_json::to_value(&snapshot).unwrap();
        let metadata = &document["metadata"];
        let boundaries = metadata["boundaries"].as_array().expect("boundary records");
        let equations = metadata["equations"].as_array().expect("equation records");
        let rows: Vec<_> = boundaries
            .iter()
            .filter(|row| {
                row["role"] == "call-argument"
                    && row["callee"] == "read"
                    && row["point"]["function"] == "run"
                    && row["argument_index"] == 0
            })
            .collect();
        assert_eq!(rows.len(), 1, "one exact readonly call argument");
        let row = rows[0];
        assert_eq!(
            row["licensing_role"], "borrowed",
            "C01 must classify this static readonly parameter"
        );
        let actual = present(&row["actual"]);
        let formal = present(&row["formal"]);
        let width = number(&formal["use_end"]) - number(&formal["use_start"]);
        assert!(
            width >= minimum_components as u64,
            "fixture must exercise its complete represented window"
        );
        assert_eq!(
            number(&actual["use_end"]) - number(&actual["use_start"]),
            width
        );
        let is_zero = |var| {
            equations.iter().any(|equation| {
                equation["point"] == row["point"]
                    && equation["operation"] == "assume"
                    && equation["value"] == false
                    && equation["variables"] == json!([var])
            })
        };
        for prefix in ["use", "def"] {
            let start = number(&formal[format!("{prefix}_start")]);
            let end = number(&formal[format!("{prefix}_end")]);
            assert_eq!(end - start, width);
            for var in start..end {
                assert!(
                    is_zero(var),
                    "callee input/output component {var} is not zero at its borrowed call"
                );
            }
        }
        for offset in 0..width {
            let before = number(&actual["use_start"]) + offset;
            let after = number(&actual["def_start"]) + offset;
            assert!(
                equations.iter().any(|equation| {
                    equation["point"] == row["point"]
                        && equation["operation"] == "equal"
                        && (equation["variables"] == json!([before, after])
                            || equation["variables"] == json!([after, before]))
                }),
                "caller component {before}->{after} must retain its ownership responsibility"
            );
        }
        let entries: Vec<_> = boundaries
            .iter()
            .filter(|entry| {
                entry["point"]["function"] == "read"
                    && entry["role"] == "entry"
                    && entry["argument_index"] == 0
            })
            .collect();
        assert_eq!(entries.len(), 1);
        assert_eq!(
            entries[0]["matched"].as_array().unwrap().len() as u64,
            width,
            "existing body/formal entry equality covers every represented component"
        );
        for pair in entries[0]["matched"].as_array().unwrap() {
            let body_var = number(&pair["actual"]["var"]);
            let formal_var = number(&pair["formal"]["var"]);
            assert!(is_zero(formal_var));
            assert!(
                equations.iter().any(|equation| {
                    equation["point"] == entries[0]["point"]
                        && equation["operation"] == "equal"
                        && equation["variables"] == json!([body_var, formal_var])
                }),
                "borrowed body window retains its existing formal equality"
            );
        }
    });
}

#[test]
fn c01_c02_readonly_scalar_parameter_zeros_callee_and_frames_caller() {
    c02_borrowed_window(
        r#"
pub unsafe fn read(p: *mut i32) -> i32 { *p }
pub unsafe fn run(p: *mut i32) -> i32 { read(p) }
"#,
        1,
    );
}

#[test]
fn c02_readonly_node_parameter_zeroes_descendants_with_the_outer_window() {
    c02_borrowed_window(
        r#"
pub struct Node { key: i32, left: *mut Node, right: *mut Node }
pub unsafe fn read(p: *mut Node) -> i32 { (*p).key }
pub unsafe fn run(p: *mut Node) -> i32 { read(p) }
"#,
        3,
    );
}

#[test]
fn c01_unknown_and_consuming_parameters_keep_legacy_linkage_in_initial_slice() {
    super::graph_tests::with_facts(
        r#"
unsafe extern "C" { fn opaque(p: *mut i32); fn free(p: *mut i32); }
pub unsafe fn unknown(p: *mut i32) { opaque(p); }
pub unsafe fn consume(p: *mut i32) { free(p); }
pub unsafe fn run(p: *mut i32) { unknown(p); consume(p); }
"#,
        |facts| {
            let snapshot =
                super::snapshot::Snapshot::capture(facts, 0).expect("real construction snapshot");
            let document = serde_json::to_value(&snapshot).unwrap();
            let metadata = &document["metadata"];
            let boundaries = metadata["boundaries"].as_array().unwrap();
            let equations = metadata["equations"].as_array().unwrap();
            for callee in ["unknown", "consume"] {
                let rows: Vec<_> = boundaries
                    .iter()
                    .filter(|row| {
                        row["role"] == "call-argument"
                            && row["callee"] == callee
                            && row["point"]["function"] == "run"
                            && row["argument_index"] == 0
                    })
                    .collect();
                assert_eq!(rows.len(), 1);
                let row = rows[0];
                assert_eq!(
                    row["licensing_role"], "legacy",
                    "uncertified role must retain legacy linkage"
                );
                let pairs = row["matched"].as_array().unwrap();
                assert!(!pairs.is_empty());
                for pair in pairs {
                    for component in ["use_var", "def_var"] {
                        assert!(
                            equations.iter().any(|equation| {
                                equation["point"] == row["point"]
                                    && equation["operation"] == "equal"
                                    && equation["variables"]
                                        == json!([
                                            number(&pair["formal"][component]),
                                            number(&pair["actual"][component]),
                                        ])
                            }),
                            "legacy {callee} must keep actual/formal {component} equality"
                        );
                    }
                }
            }
        },
    );
}

#[test]
fn c02_omitted_entry_view_zero_is_not_a_valid_export() {
    super::graph_tests::with_facts(
        r#"
pub unsafe fn read(p: *mut i32) -> i32 { *p }
pub unsafe fn run(p: *mut i32) -> i32 { read(p) }
"#,
        |facts| {
            let mut snapshot = super::snapshot::Snapshot::capture(facts, 0).unwrap();
            snapshot.validate().unwrap();
            let entry = facts
                .boundary_substitutions
                .iter()
                .find(|row| {
                    row.point.function.as_deref() == Some("read")
                        && row.role == super::super::ownership_boundary::Role::Entry
                })
                .unwrap();
            let super::super::ownership_boundary::Variables::Single { var } =
                entry.matched[0].formal
            else {
                panic!("entry signature")
            };
            let before = snapshot.metadata.equations.len();
            let call = facts
                .boundary_substitutions
                .iter()
                .find(|row| {
                    row.point.function.as_deref() == Some("run")
                        && row.role == super::super::ownership_boundary::Role::CallArgument
                })
                .unwrap();
            snapshot.metadata.equations.retain(|row| {
                !(row.point == call.point
                    && row.operation == "assume"
                    && row.value == Some(false)
                    && row.variables == [var])
            });
            assert!(snapshot.metadata.equations.len() < before);
            assert!(
                snapshot.validate().is_err(),
                "borrowed entry needs its actual zero-view law"
            );
        },
    );
}

#[test]
fn c02_omitted_reference_peel_zero_is_not_a_valid_export() {
    super::graph_tests::with_facts(
        r#"
pub struct H { ptr: *mut i32 }
pub unsafe fn read(h: &mut H) -> i32 { *h.ptr }
pub unsafe fn run(p: *mut i32) -> i32 { let mut holder = H { ptr: p }; read(&mut holder) }
"#,
        |facts| {
            let mut snapshot = super::snapshot::Snapshot::capture(facts, 0).unwrap();
            snapshot.validate().unwrap();
            let call = facts
                .boundary_substitutions
                .iter()
                .find(|row| {
                    row.point.function.as_deref() == Some("run")
                        && row.role == super::super::ownership_boundary::Role::CallArgument
                })
                .unwrap();
            let skipped = &call
                .reference_peel
                .as_ref()
                .expect("actual reference peel")
                .skipped;
            let super::super::ownership_boundary::Variables::UseDef { use_var, .. } = skipped
            else {
                panic!("peeled input/output")
            };
            let before = snapshot.metadata.equations.len();
            snapshot.metadata.equations.retain(|row| {
                !(row.point == call.point
                    && row.operation == "assume"
                    && row.value == Some(false)
                    && row.variables == [*use_var])
            });
            assert!(snapshot.metadata.equations.len() < before);
            assert!(
                snapshot.validate().is_err(),
                "the peeled outer view needs its actual zero law too"
            );
        },
    );
}

#[test]
fn c05_ifl3_construction_keeps_struct_and_payload_occurrences_distinct() {
    // The OL07 compiler input, captured without an ownership query. The
    // supervisor retains the nocapture output as a durable diagnostic receipt.
    super::graph_tests::with_facts(
        r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
pub struct H { ptr: *mut i32 }
pub unsafe fn release(h: *mut H) { free((*h).ptr as *mut core::ffi::c_void); }
pub unsafe fn f() -> i32 {
    let owner = malloc(core::mem::size_of::<i32>()) as *mut i32;
    *owner = 1;
    let mut h = H { ptr: owner };
    let before = *h.ptr;
    release(&mut h);
    before
}
"#,
        |facts| {
            let snapshot = super::snapshot::Snapshot::capture(facts, 0).unwrap();
            snapshot.validate().unwrap();
            assert_eq!(
                facts
                    .equations
                    .iter()
                    .filter(|row| row.operation == "source")
                    .count(),
                1
            );
            assert_eq!(
                facts
                    .equations
                    .iter()
                    .filter(|row| row.operation == "sink")
                    .count(),
                1
            );
            assert!(
                !facts.reader_plan.borrows_parameter("release", 0),
                "payload consumption is not a readonly full-window contract"
            );
            let release = facts
                .boundary_substitutions
                .iter()
                .find(|row| {
                    row.point.function.as_deref() == Some("f")
                        && row.callee.as_deref() == Some("release")
                        && row.role == super::super::ownership_boundary::Role::CallArgument
                })
                .unwrap();
            assert_eq!(release.formal_local, Some(1));
            assert!(
                !release.matched.is_empty(),
                "actual callee linkage must be represented"
            );
            println!(
                "C05_IFL3_FACTS={}",
                serde_json::to_string(&snapshot).unwrap()
            );
        },
    );
}
