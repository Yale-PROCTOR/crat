use super::*;
fn inputs() -> SemanticInputs {
    SemanticInputs {
        program: "fixture".into(),
        files: BTreeMap::from([("src/lib.rs".into(), "1".repeat(64))]),
        analysis: "2".repeat(64),
        toolchain: "3".repeat(64),
        dependencies: "4".repeat(64),
        configuration: "5".repeat(64),
    }
}
#[test]
fn e5_i_cache_key_is_portable_and_every_semantic_input_is_keyed() {
    let left = logical_files(
        Path::new("/sender/tree"),
        &[(PathBuf::from("/sender/tree/src/lib.rs"), "1".repeat(64))],
    )
    .unwrap();
    let right = logical_files(
        Path::new("/receiver/other"),
        &[(PathBuf::from("/receiver/other/src/lib.rs"), "1".repeat(64))],
    )
    .unwrap();
    assert_eq!(left, right);
    assert_eq!(left.keys().cloned().collect::<Vec<_>>(), vec!["src/lib.rs"]);
    let base = inputs();
    let key = semantic_key(&base).unwrap();
    assert_eq!(key.len(), 64);
    for index in 0..6 {
        let mut changed = base.clone();
        match index {
            0 => changed.program = "other".into(),
            1 => {
                changed.files.insert("src/lib.rs".into(), "6".repeat(64));
            }
            2 => changed.analysis = "6".repeat(64),
            3 => changed.toolchain = "6".repeat(64),
            4 => changed.dependencies = "6".repeat(64),
            _ => changed.configuration = "6".repeat(64),
        }
        assert_ne!(semantic_key(&changed).unwrap(), key);
    }
}
#[test]
fn e5_i_cache_logical_paths_reject_escape_duplicate_and_missing_inputs() {
    let root = Path::new("/sender/tree");
    assert!(
        logical_files(
            root,
            &[(PathBuf::from("/sender/outside.rs"), "1".repeat(64))]
        )
        .is_err()
    );
    assert!(
        logical_files(
            root,
            &[
                (root.join("x.rs"), "1".repeat(64)),
                (root.join("x.rs"), "1".repeat(64))
            ]
        )
        .is_err()
    );
    let mut missing = inputs();
    missing.toolchain.clear();
    assert!(semantic_key(&missing).is_err());
}
#[test]
fn e5_i_cache_old_schema_and_missing_required_exports_never_validate() {
    let mut entry = CompleteEntry {
        schema: "bo-model-cache-v2".into(),
        key: "a".repeat(64),
        inputs: inputs(),
        functions: vec!["f".into()],
        universe: vec!["f::_1@d0".into()],
        model: BTreeMap::from([("f::_1@d0".into(), "raw".into())]),
        baseline: BTreeMap::from([("f::_1@d0".into(), "raw".into())]),
        receipt: "status=ok\n".into(),
        exports: serde_json::json!({}),
        origin: serde_json::json!({}),
    };
    assert!(
        entry.validate().is_err(),
        "old payload cannot be relabelled"
    );
    entry.schema = SCHEMA.into();
    assert!(
        entry.validate().is_err(),
        "all required exports must actually exist"
    );
}

#[test]
fn e5_i_actual_cache_requires_complete_payload_and_cache_only_never_falls_back() {
    use super::super::{
        execution_guard::{self, ExecutionRole},
        model_cache,
    };
    struct Directory(PathBuf);
    impl Drop for Directory {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
    let directory = Directory(
        std::env::temp_dir().join(format!("era5a-cache-contract-{}", std::process::id())),
    );
    let _ = std::fs::remove_dir_all(&directory.0);
    std::fs::create_dir_all(&directory.0).unwrap();
    ::utils::compilation::run_compiler_on_str("pub unsafe fn read(p:*const i32)->i32{*p}", |tcx| {
        model_cache::reset_for_test();
        let first = model_cache::with_test_config(false, &directory.0, || {
            crate::bo_rewriter::cache_decide_receipt_for_test(tcx)
        })
        .expect("fresh accepted model");
        let provenance = model_cache::last_solve().unwrap();
        let path = PathBuf::from(provenance.cache_entry.expect("complete fresh entry"));
        let body = std::fs::read(&path).unwrap();
        let mut document: serde_json::Value =
            serde_json::from_slice(&body).expect("new era5a complete JSON envelope");
        assert_eq!(document["schema"], SCHEMA);
        assert!(document.get("exports").is_some());
        assert!(document.get("origin").is_some());
        model_cache::reset_for_test();
        let before = execution_guard::model_entries();
        let loaded = execution_guard::with_role(ExecutionRole::CacheOnly, || {
            model_cache::with_test_config(true, &directory.0, || {
                crate::bo_rewriter::cache_decide_receipt_for_test(tcx)
            })
        })
        .expect("cache-only complete readback");
        assert_eq!(loaded, first);
        assert_eq!(execution_guard::model_entries(), before);
        assert_eq!(model_cache::last_solve().unwrap().source, "cache");
        document.as_object_mut().unwrap().remove("exports");
        let incomplete = serde_json::to_vec(&document).unwrap();
        std::fs::write(&path, &incomplete).unwrap();
        model_cache::reset_for_test();
        let before = execution_guard::model_entries();
        let refused = execution_guard::with_role(ExecutionRole::CacheOnly, || {
            model_cache::with_test_config(true, &directory.0, || {
                crate::bo_rewriter::cache_decide_receipt_for_test(tcx)
            })
        });
        assert!(
            refused.is_err(),
            "missing required export must refuse without a solver fallback"
        );
        assert_eq!(execution_guard::model_entries(), before);
        assert_eq!(
            std::fs::read(&path).unwrap(),
            incomplete,
            "refusal must not overwrite the entry"
        );
        // Coordinated deletion must not make two incomplete lists validate
        // each other while losing the compiler's actual function evidence.
        let mut missing_functions: serde_json::Value = serde_json::from_slice(&body).unwrap();
        missing_functions["functions"] = serde_json::json!([]);
        missing_functions["origin"]["functions"] = serde_json::json!([]);
        std::fs::write(&path, serde_json::to_vec(&missing_functions).unwrap()).unwrap();
        model_cache::reset_for_test();
        let before = execution_guard::model_entries();
        let refused = execution_guard::with_role(ExecutionRole::CacheOnly, || {
            model_cache::with_test_config(true, &directory.0, || {
                crate::bo_rewriter::cache_decide_receipt_for_test(tcx)
            })
        });
        assert!(
            refused.is_err(),
            "actual compiler function evidence cannot be co-deleted"
        );
        assert_eq!(execution_guard::model_entries(), before);
        model_cache::reset_for_test();
    })
    .unwrap_or_else(|error| error.raise());
}

#[test]
fn e5_i_cache_publish_is_atomic_idempotent_and_never_overwrites() {
    use super::super::portable_export::{
        self, CaptureAvailability, PortableExport, PortableFamily, ScopeGap,
    };
    // Integrity-only synthetic empty model; no claim that a model was solved.
    let mut exports = PortableExport {
        schema: portable_export::SCHEMA.into(),
        licensing_deferred: true,
        identities: Default::default(),
        scope_gaps: [
            ScopeGap::OwnershipOccurrenceConstructionNotRecorded,
            ScopeGap::OwnershipValuesAreLatestSuppliedValuation,
        ]
        .into_iter()
        .collect(),
        families: portable_export::REQUIRED_FAMILIES
            .into_iter()
            .map(|f| {
                (
                    f,
                    PortableFamily {
                        availability: CaptureAvailability::Captured,
                        source_rows: 0,
                        records: vec![],
                    },
                )
            })
            .collect(),
        diagnostics: vec![],
    };
    use portable_export::{ExportFamily, PortableRecord};
    for (family, value) in [
        (
            ExportFamily::RetirementFinal,
            serde_json::json!({"conflicts":[],"unresolved":[],"coverage":[],"ordinary_error_points":0,"terminal":[]}),
        ),
        (
            ExportFamily::DemandEvidence,
            serde_json::from_str(
                &super::super::demand_evidence::DemandEvidence::default()
                    .canonical_json()
                    .unwrap(),
            )
            .unwrap(),
        ),
        (
            ExportFamily::ProofEvidence,
            serde_json::to_value(super::super::proof_evidence::ProofEvidence::default()).unwrap(),
        ),
    ] {
        let key = format!("{family:?}/{{}}");
        exports.identities.insert(key.clone());
        let row = PortableRecord {
            key,
            references: vec![],
            fields: value
                .as_object()
                .unwrap()
                .iter()
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect(),
        };
        exports.families.insert(
            family,
            PortableFamily {
                availability: CaptureAvailability::Captured,
                source_rows: 1,
                records: vec![row],
            },
        );
    }
    let inputs = inputs();
    let key = semantic_key(&inputs).unwrap();
    let entry = CompleteEntry {
        schema: SCHEMA.into(),
        key,
        inputs,
        functions: vec![],
        universe: vec![],
        model: BTreeMap::new(),
        baseline: BTreeMap::new(),
        receipt: "status=ok\ndata=true\n".into(),
        exports: serde_json::to_value(exports).unwrap(),
        origin: serde_json::json!({"functions":[]}),
    };
    entry
        .validate()
        .expect("well-formed synthetic integrity envelope");
    struct Directory(PathBuf);
    impl Drop for Directory {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
    let directory = Directory(
        std::env::temp_dir().join(format!("era5a-atomic-contract-{}", std::process::id())),
    );
    let _ = std::fs::remove_dir_all(&directory.0);
    let path = publish(&directory.0, &entry).expect("atomic complete publication");
    let original = std::fs::read(&path).unwrap();
    assert_eq!(
        publish(&directory.0, &entry).unwrap(),
        path,
        "identical repeated publication is idempotent"
    );
    let mut collision = entry.clone();
    collision.receipt.push_str("different-receipt=true\n");
    assert!(
        publish(&directory.0, &collision).is_err(),
        "same semantic address cannot overwrite a different completed body"
    );
    assert_eq!(std::fs::read(&path).unwrap(), original);
    let decoded: CompleteEntry = serde_json::from_slice(&original).unwrap();
    decoded.validate().unwrap();
    assert_eq!(decoded, entry);
}

#[test]
fn e5_i_actual_cache_transports_between_distinct_source_roots_without_solving() {
    use super::super::{
        execution_guard::{self, ExecutionRole},
        model_cache,
    };
    struct Directory(PathBuf);
    impl Drop for Directory {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
    let root =
        Directory(std::env::temp_dir().join(format!("era5a-cross-root-{}", std::process::id())));
    let _ = std::fs::remove_dir_all(&root.0);
    let source =
        "pub struct Holder{pub items:[*mut u8;2]} pub unsafe fn read(p:*const i32)->i32{*p}";
    let left = root.0.join("sender/src/lib.rs");
    let right = root.0.join("receiver/src/lib.rs");
    for path in [&left, &right] {
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, source).unwrap();
    }
    let cache = root.0.join("cache");
    let first = ::utils::compilation::run_compiler_on_path(&left, |tcx| {
        model_cache::reset_for_test();
        let receipt = model_cache::with_test_config(false, &cache, || {
            crate::bo_rewriter::cache_decide_receipt_for_test(tcx)
        })
        .expect("sender model");
        let provenance = model_cache::last_solve().unwrap();
        assert!(
            provenance.cache_entry.is_some(),
            "sender complete entry: {:?}",
            model_cache::prepare_error()
        );
        (receipt, provenance.fingerprint, provenance.model_sha256)
    })
    .unwrap_or_else(|error| error.raise());
    ::utils::compilation::run_compiler_on_path(&right, |tcx| {
        model_cache::reset_for_test();
        let before = execution_guard::model_entries();
        let receipt = execution_guard::with_role(ExecutionRole::CacheOnly, || {
            model_cache::with_test_config(true, &cache, || {
                crate::bo_rewriter::cache_decide_receipt_for_test(tcx)
            })
        })
        .expect("receiver cache-only readback");
        let provenance = model_cache::last_solve().unwrap();
        assert_eq!(receipt, first.0);
        assert_eq!(provenance.fingerprint, first.1);
        assert_eq!(provenance.model_sha256, first.2);
        assert_eq!(provenance.source, "cache");
        assert_eq!(execution_guard::model_entries(), before);
        model_cache::reset_for_test();
    })
    .unwrap_or_else(|error| error.raise());
}
