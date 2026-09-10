use std::{
    cell::Cell,
    io::{self, Cursor, Read},
    rc::Rc,
};

use serde_json::json;

use crate::analyses::borrow_ownership::cache_contract::stream::*;

fn fixture() -> Value {
    let inputs = SemanticInputs {
        program: "stream-fixture".into(),
        files: BTreeMap::from([("lib.rs".into(), "1".repeat(64))]),
        analysis: "2".repeat(64),
        toolchain: "3".repeat(64),
        dependencies: "4".repeat(64),
        configuration: "5".repeat(64),
    };
    let mut families = serde_json::Map::new();
    let mut identities = Vec::new();
    for family in REQUIRED_FAMILIES {
        let name = serde_json::to_value(family)
            .unwrap()
            .as_str()
            .unwrap()
            .to_owned();
        let records = if matches!(
            family,
            ExportFamily::RetirementFinal
                | ExportFamily::DemandEvidence
                | ExportFamily::ProofEvidence
        ) {
            let key = portable_export::stream::expected_key(family, &BTreeMap::new()).unwrap();
            identities.push(key.clone());
            vec![json!({"key":key,"references":[],"fields":{"body":[{"x":1},[true,null,"text"]]}})]
        } else {
            vec![]
        };
        families.insert(name, json!({"availability":{"state":"captured"},"source_rows":records.len(),"records":records}));
    }
    json!({
        "schema":SCHEMA,"key":semantic_key(&inputs).unwrap(),"inputs":inputs,
        "functions":[],"universe":[],"model":{},"baseline":{},
        "receipt":"status=ok\ndata=true\n", "origin":{"functions":[]},
        "exports":{"schema":portable_export::SCHEMA,"licensing_deferred":true,
            "identities":identities,"scope_gaps":["ownership-occurrence-construction-not-recorded","ownership-values-are-latest-supplied-valuation"],
            "families":families,"diagnostics":[]}
    })
}

fn parity(value: &Value) -> bool {
    let bytes = serde_json::to_vec(value).unwrap();
    let expected = crate::analyses::borrow_ownership::cache_contract::decode(&bytes).is_ok();
    assert_eq!(
        validate_reader(bytes.as_slice()).is_ok(),
        expected,
        "{value}"
    );
    expected
}

struct PoisonTail {
    prefix: Cursor<Vec<u8>>,
    tail_reads: Rc<Cell<usize>>,
}
impl Read for PoisonTail {
    fn read(&mut self, bytes: &mut [u8]) -> io::Result<usize> {
        let count = self.prefix.read(bytes)?;
        if count != 0 || bytes.is_empty() {
            return Ok(count);
        }
        self.tail_reads.set(self.tail_reads.get() + 1);
        Err(io::Error::other("unbounded tail was requested"))
    }
}

#[test]
fn r281_cache_stream_rejects_duplicate_before_reading_unbounded_tail() {
    let reads = Rc::new(Cell::new(0));
    let input = PoisonTail {
        prefix: Cursor::new(br#"{"schema":"era5a-model-cache-v1","\u0073chema":"#.to_vec()),
        tail_reads: reads.clone(),
    };
    let error = validate_reader(input).unwrap_err();
    assert_eq!(
        reads.get(),
        0,
        "validation must reject the duplicate before reading its body"
    );
    assert!(error.contains("duplicate JSON object key"), "{error}");
}

#[test]
fn r281_cache_stream_metadata_and_field_order_match_old_validator() {
    let value = fixture();
    let bytes = serde_json::to_vec(&value).unwrap();
    let expected = crate::analyses::borrow_ownership::cache_contract::decode(&bytes).unwrap();
    let actual = validate_reader(bytes.as_slice()).unwrap();
    assert_eq!(actual.schema, expected.schema);
    assert_eq!(actual.key, expected.key);
    assert_eq!(actual.inputs, expected.inputs);
    assert_eq!(actual.functions, expected.functions);
    assert_eq!(actual.universe, expected.universe);
    assert_eq!(actual.model, expected.model);
    assert_eq!(actual.baseline, expected.baseline);
    assert_eq!(actual.receipt, expected.receipt);
    assert_eq!(actual.origin, expected.origin);
    let reversed = reverse_objects(&value);
    assert!(validate_reader(reversed.as_bytes()).is_ok());
    assert!(crate::analyses::borrow_ownership::cache_contract::decode(reversed.as_bytes()).is_ok());
}

fn reverse_objects(value: &Value) -> String {
    match value {
        Value::Object(map) => format!(
            "{{{}}}",
            map.iter()
                .rev()
                .map(|(key, value)| format!(
                    "{}:{}",
                    serde_json::to_string(key).unwrap(),
                    reverse_objects(value)
                ))
                .collect::<Vec<_>>()
                .join(",")
        ),
        Value::Array(values) => format!(
            "[{}]",
            values
                .iter()
                .map(reverse_objects)
                .collect::<Vec<_>>()
                .join(",")
        ),
        _ => serde_json::to_string(value).unwrap(),
    }
}

#[test]
fn r281_cache_stream_retains_arbitrary_round_identity_and_record_multiplicity() {
    for round in [
        Value::Null,
        json!(-1),
        json!("untyped"),
        json!({"nested":[false,2]}),
    ] {
        let mut value = fixture();
        let fields = BTreeMap::from([("round".into(), round)]);
        let key =
            portable_export::stream::expected_key(ExportFamily::RetirementRounds, &fields).unwrap();
        value["exports"]["identities"]
            .as_array_mut()
            .unwrap()
            .push(json!(key));
        let record = json!({"key":key,"references":[],"fields":fields});
        value["exports"]["families"]["retirement-rounds"]["records"] =
            json!([record.clone(), record]);
        value["exports"]["families"]["retirement-rounds"]["source_rows"] = json!(2);
        assert!(parity(&value));
        value["exports"]["families"]["retirement-rounds"]["records"][0]["fields"]
            .as_object_mut()
            .unwrap()
            .remove("round");
        assert!(!parity(&value));
    }
}

#[test]
fn r281_cache_stream_preserves_scope_sets_and_availability_enum_semantics() {
    let mut value = fixture();
    let identity = value["exports"]["identities"][0].clone();
    value["exports"]["identities"]
        .as_array_mut()
        .unwrap()
        .push(identity);
    let gap = value["exports"]["scope_gaps"][0].clone();
    value["exports"]["scope_gaps"]
        .as_array_mut()
        .unwrap()
        .push(gap);
    value["exports"]["families"]["loans"]["availability"]["extra"] = json!([1, 2]);
    assert!(parity(&value));
    value["exports"]["families"]["residual-conflicts"]["availability"] =
        json!({"state":"not-recorded","reason":"absent","extra":true});
    assert!(parity(&value));
    value["exports"]["families"]["loans"]["availability"] =
        json!({"state":"not-recorded","reason":"absent"});
    assert!(!parity(&value));

    // W04: preserve the old decoder's availability/type boundary exactly.
    for availability in [
        json!({"state":"not-recorded","reason":""}),
        json!({"state":"not-recorded"}),
        json!({"state":"not-recorded","reason":null}),
        json!({"state":"not-recorded","reason":7}),
        json!({"state":"unknown"}),
        json!({"reason":"absent"}),
        json!({"state":null}),
        json!({"state":false}),
    ] {
        let mut case = fixture();
        case["exports"]["families"]["residual-conflicts"]["availability"] = availability;
        assert!(!parity(&case));
    }
    for count in [json!(null), json!("0"), json!(-1), json!(0.5), json!(false)] {
        let mut case = fixture();
        case["exports"]["families"]["loans"]["source_rows"] = count;
        assert!(!parity(&case));
    }
    let mut case = fixture();
    let fields = BTreeMap::from([("probe".into(), json!(true))]);
    let key =
        portable_export::stream::expected_key(ExportFamily::ResidualConflicts, &fields).unwrap();
    case["exports"]["identities"]
        .as_array_mut()
        .unwrap()
        .push(json!(key));
    case["exports"]["families"]["residual-conflicts"] = json!({
        "availability":{"state":"not-recorded","reason":"absent"},
        "source_rows":1,"records":[{"key":key,"references":[],"fields":fields}]
    });
    assert!(
        !parity(&case),
        "nonempty unavailable residual capture remains invalid"
    );
}

#[test]
fn r281_cache_stream_rejects_corrupt_envelopes_references_and_metadata() {
    let valid = fixture();
    let mut cases = Vec::new();
    let mut case = valid.clone();
    case["unexpected"] = json!(0);
    cases.push(case);
    let mut case = valid.clone();
    case["exports"]["extra"] = json!(0);
    cases.push(case);
    let mut case = valid.clone();
    case["exports"]["families"]["loans"]["extra"] = json!(0);
    cases.push(case);
    let mut case = valid.clone();
    case["exports"]["families"]["retirement-final"]["records"][0]["extra"] = json!(0);
    cases.push(case);
    let mut case = valid.clone();
    case["exports"]["families"]
        .as_object_mut()
        .unwrap()
        .remove("loans");
    cases.push(case);
    let mut case = valid.clone();
    case["exports"]["families"]["loans"]["source_rows"] = json!(1);
    cases.push(case);
    let mut case = valid.clone();
    case["exports"]["families"]["retirement-final"]["records"][0]["references"] =
        json!(["missing"]);
    cases.push(case);
    let mut case = valid.clone();
    case["exports"]["families"]["retirement-final"]["records"][0]["key"] = json!("wrong");
    cases.push(case);
    let mut case = valid.clone();
    case["exports"]["families"]["proof-evidence"]["records"] = json!([]);
    case["exports"]["families"]["proof-evidence"]["source_rows"] = json!(0);
    cases.push(case);
    let mut case = valid.clone();
    case["exports"]["scope_gaps"] = json!([]);
    cases.push(case);
    let mut case = valid.clone();
    case["exports"]["licensing_deferred"] = json!(false);
    cases.push(case);
    let mut case = valid.clone();
    case["key"] = json!("0".repeat(64));
    cases.push(case);
    let mut case = valid.clone();
    case["universe"] = json!(["x", "x"]);
    cases.push(case);
    let mut case = valid.clone();
    case["model"] = json!({"x":"raw"});
    cases.push(case);
    let mut case = valid.clone();
    case["receipt"] = json!("status=ok\n");
    cases.push(case);
    let mut case = valid.clone();
    case["functions"] = json!(["f"]);
    cases.push(case);
    for case in cases {
        assert!(!parity(&case));
    }
    let bytes = serde_json::to_string(&valid).unwrap() + " null";
    assert!(validate_reader(bytes.as_bytes()).is_err());
}

#[test]
fn r281_cache_stream_strict_discard_rejects_nested_duplicates_everywhere() {
    let mut valid = fixture();
    let source = valid["exports"]["identities"][0].clone();
    valid["exports"]["diagnostics"] =
        json!([{"family":"loans","source_key":source,"labels":{"probe":"DUPLICATE_SENTINEL"}}]);
    assert!(parity(&valid));
    for pointer in [
        "/exports/families/retirement-final/records/0/fields/body",
        "/exports/families/demand-evidence/records/0/fields/body",
        "/exports/families/proof-evidence/records/0/fields/body",
        "/exports/diagnostics/0/labels/probe",
        "/origin/ignored",
    ] {
        let mut case = valid.clone();
        if pointer == "/origin/ignored" {
            case["origin"]["ignored"] = json!("NESTED_SENTINEL");
        } else {
            *case.pointer_mut(pointer).unwrap() = json!("NESTED_SENTINEL");
        }
        let text = serde_json::to_string(&case)
            .unwrap()
            .replace("\"NESTED_SENTINEL\"", r#"[{"x":1,"\u0078":2}]"#);
        assert!(
            crate::analyses::borrow_ownership::cache_contract::decode(text.as_bytes()).is_err()
        );
        assert!(validate_reader(text.as_bytes()).is_err(), "{pointer}");
    }
}

#[test]
fn r281_cache_stream_discarded_review_body_need_not_have_typed_review_shape() {
    let mut valid = fixture();
    valid["exports"]["families"]["retirement-final"]["records"][0]["fields"] =
        json!({"arbitrary":[null, {"array":[1,2,3]}]});
    valid["exports"]["families"]["demand-evidence"]["records"][0]["fields"] = json!({});
    assert!(parity(&valid));

    // These are raw JSON spellings, so the old decoder decides numeric range
    // and syntax acceptance before any Value normalization can erase it.
    for scalar in [
        "null",
        "true",
        "false",
        "-9223372036854775808",
        "18446744073709551615",
        "18446744073709551616",
        "-9223372036854775809",
        "-0",
        "-0.0",
        "1e0",
        "1.25e-200",
        "1.7976931348623157e308",
        "1e309",
        "-1e309",
        "01",
        "+1",
        r#""\u0000\n\t\"\\\u03bb\ud83d\ude00""#,
    ] {
        let mut case = fixture();
        case["exports"]["families"]["retirement-final"]["records"][0]["fields"] =
            json!({"probe":"SCALAR_SENTINEL"});
        let bytes = serde_json::to_string(&case)
            .unwrap()
            .replace("\"SCALAR_SENTINEL\"", scalar);
        let old =
            crate::analyses::borrow_ownership::cache_contract::decode(bytes.as_bytes()).is_ok();
        assert_eq!(
            validate_reader(bytes.as_bytes()).is_ok(),
            old,
            "scalar spelling {scalar}"
        );
    }
}
