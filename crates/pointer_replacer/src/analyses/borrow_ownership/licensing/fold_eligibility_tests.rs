//! Eligibility custody precedes any selected-fold activation.
use super::{fold_chain_tests::CODE, snapshot::Snapshot};

#[test]
fn gf08_eligibility_freeze_keeps_the_exact_caller_proof_and_rebuilds() {
    super::graph_tests::with_facts(CODE, |facts| {
        let snapshot = Snapshot::capture(facts, 0).unwrap();
        let encoded = serde_json::to_value(&snapshot).unwrap();
        let rows = encoded["fold_callers"]
            .as_array()
            .expect("new frame eligibility inventory");
        assert_eq!(rows.len(), facts.fold_declarations.as_ref().unwrap().len());
        let declaration = &facts.fold_declarations.as_ref().unwrap()[0];
        let fold = super::fold_call::certify(
            facts,
            &declaration.call,
            declaration.argument,
            &Default::default(),
        )
        .unwrap();
        let proof = super::fold_caller::certify(facts, declaration, &fold).unwrap();
        assert_eq!(
            rows[0]["declaration"],
            serde_json::to_value(declaration).unwrap()
        );
        assert_eq!(
            rows[0]["outcome"]["Ok"],
            serde_json::to_value(proof).unwrap()
        );
        snapshot
            .validate()
            .expect("AST-free reconstruction matches eligibility");
        let decoded: Snapshot = serde_json::from_value(encoded).unwrap();
        assert_eq!(decoded, snapshot);
    });
}

#[test]
fn gf08_eligibility_freeze_keeps_typed_holds_in_the_denominator() {
    let code = CODE.replace(
        " free(result as *mut core::ffi::c_void);",
        " free(node as *mut core::ffi::c_void);\n free(result as *mut core::ffi::c_void);",
    );
    super::graph_tests::with_facts(&code, |facts| {
        let snapshot = Snapshot::capture(facts, 0).unwrap();
        let encoded = serde_json::to_value(&snapshot).unwrap();
        let rows = encoded["fold_callers"]
            .as_array()
            .expect("held declaration remains exported");
        assert_eq!(rows.len(), 1);
        assert_eq!(
            rows[0]["outcome"]["Err"]["Caller"],
            "CompetingResponsibility"
        );
        snapshot.validate().expect("typed hold reconstructs");
    });
}

#[test]
fn gf08_eligibility_validator_rejects_omission_and_changed_requirements() {
    super::graph_tests::with_facts(CODE, |facts| {
        let snapshot = Snapshot::capture(facts, 0).unwrap();
        let encoded = serde_json::to_value(&snapshot).unwrap();
        assert_eq!(
            encoded["fold_callers"]
                .as_array()
                .expect("eligibility exists")
                .len(),
            1
        );
        for mode in 0..4 {
            let mut changed = encoded.clone();
            match mode {
                0 => {
                    changed.as_object_mut().unwrap().remove("fold_callers");
                }
                1 => changed["fold_callers"] = serde_json::json!([]),
                2 => {
                    changed["fold_callers"][0]["outcome"]["Ok"]["requirements"]["zero"] =
                        serde_json::json!([])
                }
                _ => {
                    let duplicate = changed["fold_callers"][0].clone();
                    changed["fold_callers"]
                        .as_array_mut()
                        .unwrap()
                        .push(duplicate);
                }
            }
            let changed: Snapshot = serde_json::from_value(changed).unwrap();
            assert_eq!(
                changed.validate(),
                Err("fold caller eligibility differs from current metadata".into()),
                "omission/mutation {mode}"
            );
        }
    });
}

#[test]
fn gf08_eligibility_distinguishes_observed_empty_from_legacy_unavailable() {
    super::graph_tests::with_facts("pub fn identity(value:i32)->i32{value}", |facts| {
        let snapshot = Snapshot::capture(facts, 0).unwrap();
        assert_eq!(snapshot.fold_callers, Some(Vec::new()));
        // The appended member family observes the same emptiness separately.
        assert_eq!(snapshot.fold_members, Some(Vec::new()));
        snapshot.validate().unwrap();
        let mut legacy = snapshot;
        legacy.metadata.fold_declarations = None;
        legacy.fold_callers = None;
        legacy.fold_members = None;
        let encoded = serde_json::to_value(&legacy).unwrap();
        assert!(encoded.get("fold_callers").is_none());
        assert!(encoded.get("fold_members").is_none());
        let decoded: Snapshot = serde_json::from_value(encoded).unwrap();
        assert_eq!(decoded, legacy);
        decoded.validate().unwrap();
        // Either family observed where the declarations are unavailable is a
        // difference, and each is reported by its own name.
        legacy.fold_callers = Some(Vec::new());
        assert_eq!(
            legacy.validate(),
            Err("fold caller eligibility differs from current metadata".into())
        );
        legacy.fold_callers = None;
        legacy.fold_members = Some(Vec::new());
        assert_eq!(
            legacy.validate(),
            Err("fold member eligibility differs from current metadata".into())
        );
    });
}
