//! R231 instrument controls. These do not invoke analysis or a corpus worker.

use super::bridge_custody_syntax::{self as syntax, ArgumentForm, GeneratedKind};

fn targets(source: &str) -> Vec<syntax::Call> {
    syntax::inventory_source("bridge-control.rs", source)
        .expect("valid pinned syntax")
        .calls
        .into_iter()
        .filter(|call| call.callee_path.as_deref() == Some("target"))
        .collect()
}

#[test]
fn bridge_custody_syntax_raw_view_links_the_actual_earlier_binding() {
    let source = "fn caller(p: &i32) { let __crat_pair_raw_42_1: *const i32 = core::ptr::from_ref(p); target(__crat_pair_raw_42_1); }";
    let calls = targets(source);
    assert_eq!(calls.len(), 1);
    let call = &calls[0];
    assert_eq!(call.owner, "caller");
    let arg = &call.arguments[0];
    assert_eq!(arg.form, ArgumentForm::Path);
    let binding = arg.binding.as_ref().expect("actual binding provenance");
    assert_eq!(binding.generated, Some(GeneratedKind::RawTemporary));
    assert_eq!(binding.name, "__crat_pair_raw_42_1");
    assert_eq!(binding.type_text.as_deref(), Some("*const i32"));
    assert!(binding.declaration_span.hi <= call.span.lo);
    let init = binding.init_span.expect("initializer span");
    assert_eq!(
        &source[init.lo as usize..init.hi as usize],
        "core::ptr::from_ref(p)"
    );
}

#[test]
fn bridge_custody_syntax_snapshot_links_the_borrowed_value_temporary() {
    let calls = targets(
        "fn caller(p: *const i32) { let __crat_c9_0_5: i32 = *p; target(&__crat_c9_0_5); }",
    );
    assert_eq!(calls.len(), 1);
    let arg = &calls[0].arguments[0];
    assert_eq!(arg.form, ArgumentForm::AddrOfPath);
    let binding = arg.binding.as_ref().expect("exact snapshot binding");
    assert_eq!(binding.generated, Some(GeneratedKind::C9Temporary));
    assert_eq!(binding.type_text.as_deref(), Some("i32"));
    assert_eq!(binding.init_text.as_deref(), Some("*p"));
}

#[test]
fn bridge_custody_syntax_shadow_and_sibling_scope_cannot_supply_a_view() {
    let calls = targets(
        "fn caller(p: &i32) { let __crat_pair_raw_42_1: *const i32 = core::ptr::from_ref(p); { let __crat_pair_raw_42_1 = 7; target(__crat_pair_raw_42_1); } target(__crat_pair_raw_42_1); } fn other() { { let __crat_pair_raw_9_0: *const i32 = 0 as *const i32; } target(__crat_pair_raw_9_0); }",
    );
    assert_eq!(calls.len(), 3);
    let inner = calls[0].arguments[0]
        .binding
        .as_ref()
        .expect("shadow observed");
    let outer = calls[1].arguments[0]
        .binding
        .as_ref()
        .expect("outer binding restored");
    assert_ne!(inner.id, outer.id);
    assert_eq!(inner.generated, None);
    assert_eq!(outer.generated, Some(GeneratedKind::RawTemporary));
    assert!(calls[2].arguments[0].binding.is_none());
}

#[test]
fn bridge_custody_syntax_later_binding_and_fake_text_do_not_match() {
    let calls = targets(
        "fn caller() { let text = \"let __crat_pair_raw_42_1: *const i32 = p;\"; /* let __crat_pair_raw_42_1: *const i32 = p; */ target(__crat_pair_raw_42_1); let __crat_pair_raw_42_1: *const i32 = 0 as *const i32; }",
    );
    assert_eq!(calls.len(), 1);
    assert!(calls[0].arguments[0].binding.is_none());
}

#[test]
fn bridge_custody_syntax_invalid_rust_fails_closed() {
    assert!(syntax::inventory_source("bad.rs", "fn caller( {").is_err());
}

#[test]
fn bridge_custody_syntax_uses_the_pinned_nightly_grammar_and_original_offsets() {
    let source = "\u{feff}#![feature(extern_types)]\r\nextern \"C\" { pub type Opaque; }\r\nfn caller(a: u32, b: u64) { if a as u64 <= b { target(a); } }\r\n";
    let calls = targets(source);
    assert_eq!(calls.len(), 1);
    assert_eq!(
        &source[calls[0].span.lo as usize..calls[0].span.hi as usize],
        "target(a)"
    );
}

#[test]
fn bridge_custody_syntax_records_borrow_kind_and_mutability() {
    let calls = targets(
        "fn caller() { let mut __crat_c9_0_1: i32 = 7; target(&__crat_c9_0_1); target(&raw const __crat_c9_0_1); target(&mut __crat_c9_0_1); }",
    );
    assert_eq!(calls.len(), 3);
    let observed = calls
        .iter()
        .map(|call| {
            let arg = &call.arguments[0];
            (arg.address_kind.as_deref(), arg.address_mutable)
        })
        .collect::<Vec<_>>();
    assert_eq!(
        observed,
        vec![
            (Some("ref"), Some(false)),
            (Some("raw"), Some(false)),
            (Some("ref"), Some(true))
        ]
    );
}

#[test]
fn bridge_custody_syntax_records_uses_without_claiming_liveness() {
    let inventory = syntax::inventory_source(
        "uses.rs",
        "fn caller(p: &i32) { let before = *p; target(p); let after = *p; }",
    )
    .unwrap();
    let parameter = inventory
        .bindings
        .iter()
        .find(|binding| binding.owner == "caller" && binding.name == "p")
        .unwrap();
    let call = inventory
        .calls
        .iter()
        .find(|call| call.callee_path.as_deref() == Some("target"))
        .unwrap();
    let uses = inventory
        .uses
        .iter()
        .filter(|site| site.binding_id == parameter.id)
        .collect::<Vec<_>>();
    assert_eq!(uses.len(), 3);
    assert!(uses.iter().any(|site| site.span.hi < call.span.lo));
    assert!(uses.iter().any(|site| site.span.lo > call.span.hi));
    assert!(uses.iter().all(|site| site.owner == "caller"));
    // These are syntax positions only: no loop/branch execution or MIR-live
    // conclusion is inferred from their order or from absent rows.
}

#[test]
fn bridge_custody_manifest_inventory() {
    use sha2::{Digest, Sha256};
    let Some(input) = std::env::var_os("CRAT_BRIDGE_CUSTODY_INPUT") else { return };
    let output = std::env::var_os("CRAT_BRIDGE_CUSTODY_OUTPUT").expect("bridge inventory output");
    assert!(
        !std::path::Path::new(&output).exists(),
        "do not overwrite a sealed inventory"
    );
    #[derive(serde::Deserialize)]
    struct Input {
        path: String,
        sha256: String,
    }
    let inputs: Vec<Input> =
        serde_json::from_slice(&std::fs::read(input).expect("bridge inventory manifest"))
            .expect("bridge manifest schema");
    assert!(!inputs.is_empty());
    let mut seen = std::collections::BTreeSet::new();
    let mut observed = Vec::new();
    for input in &inputs {
        assert!(seen.insert(input.path.clone()), "unique source paths");
        let bytes = std::fs::read(&input.path).expect("pinned source");
        assert_eq!(format!("{:x}", Sha256::digest(&bytes)), input.sha256);
        let source = std::str::from_utf8(&bytes).expect("Rust source UTF-8");
        let inventory = syntax::inventory_source(&input.path, source)
            .unwrap_or_else(|error| panic!("bridge parse gate {}: {error}", input.path));
        observed.push(serde_json::json!({"path":input.path,"sha256":input.sha256,"parse_errors":0,"inventory":inventory}));
    }
    for input in &inputs {
        assert_eq!(
            format!(
                "{:x}",
                Sha256::digest(std::fs::read(&input.path).expect("post-parser source"))
            ),
            input.sha256
        );
    }
    std::fs::write(
        output,
        serde_json::to_vec(&observed).expect("bridge inventory JSON"),
    )
    .expect("publish complete inventory only");
}

#[test]
fn bridge_custody_manifest_compare() {
    use sha2::{Digest, Sha256};

    use crate::bo_rewriter::bridge_custody_match::{
        self as custody, BridgeCustodyContext, BridgeExpectation,
    };
    let Some(requests) = std::env::var_os("CRAT_BRIDGE_MATCH_INPUT") else { return };
    let inventory_path =
        std::env::var_os("CRAT_BRIDGE_MATCH_INVENTORY").expect("closed inventory path");
    let inventory_sha =
        std::env::var("CRAT_BRIDGE_MATCH_INVENTORY_SHA256").expect("closed inventory digest");
    let output = std::env::var_os("CRAT_BRIDGE_MATCH_OUTPUT").expect("bridge comparison output");
    assert!(
        !std::path::Path::new(&output).exists(),
        "do not overwrite a sealed comparison"
    );
    #[derive(serde::Deserialize)]
    struct InventoryRow {
        sha256: String,
        parse_errors: usize,
        inventory: syntax::Inventory,
    }
    #[derive(serde::Deserialize)]
    struct Request {
        frame: String,
        program: String,
        file: String,
        original_path: String,
        original_sha256: String,
        emitted_path: String,
        emitted_sha256: String,
        expectations: Vec<BridgeExpectation>,
        context: BridgeCustodyContext,
    }
    let bytes = std::fs::read(inventory_path).expect("bridge inventory bytes");
    assert_eq!(format!("{:x}", Sha256::digest(&bytes)), inventory_sha);
    let inventory: Vec<InventoryRow> =
        serde_json::from_slice(&bytes).expect("bridge inventory schema");
    let mut by_sha = std::collections::BTreeMap::new();
    for row in inventory {
        assert_eq!(row.parse_errors, 0);
        assert!(
            by_sha.insert(row.sha256, row.inventory).is_none(),
            "unique parsed source hashes"
        );
    }
    let requests: Vec<Request> =
        serde_json::from_slice(&std::fs::read(requests).expect("bridge requests"))
            .expect("bridge request schema");
    assert!(!requests.is_empty());
    let mut seen = std::collections::BTreeSet::new();
    let mut reports = Vec::new();
    for request in requests {
        assert!(
            seen.insert((
                request.frame.clone(),
                request.program.clone(),
                request.file.clone()
            )),
            "unique frame file request"
        );
        let original_source =
            std::fs::read_to_string(&request.original_path).expect("original source");
        let emitted_source =
            std::fs::read_to_string(&request.emitted_path).expect("emitted source");
        assert_eq!(
            format!("{:x}", Sha256::digest(original_source.as_bytes())),
            request.original_sha256
        );
        assert_eq!(
            format!("{:x}", Sha256::digest(emitted_source.as_bytes())),
            request.emitted_sha256
        );
        let report = custody::compare(custody::BridgeCustodyInput {
            original: by_sha
                .get(&request.original_sha256)
                .expect("parsed original"),
            emitted: by_sha.get(&request.emitted_sha256).expect("parsed emitted"),
            original_source: &original_source,
            emitted_source: &emitted_source,
            expectations: &request.expectations,
            context: &request.context,
        });
        // A false custody verdict is evidence to report, not a parser failure
        // and not a reason to skip the remaining sealed frame files.
        reports.push(serde_json::json!({"frame":request.frame,"program":request.program,"file":request.file,
            "original_sha256":request.original_sha256,"emitted_sha256":request.emitted_sha256,"report":report}));
        assert_eq!(
            format!(
                "{:x}",
                Sha256::digest(std::fs::read(&request.original_path).unwrap())
            ),
            request.original_sha256
        );
        assert_eq!(
            format!(
                "{:x}",
                Sha256::digest(std::fs::read(&request.emitted_path).unwrap())
            ),
            request.emitted_sha256
        );
    }
    std::fs::write(output, serde_json::to_vec_pretty(&reports).unwrap())
        .expect("complete bridge report");
}

mod matcher {
    use syntax::ByteSpan;

    use super::syntax;
    use crate::bo_rewriter::bridge_custody_match::*;

    const INPUT: &str = "fn target(w: *mut i32, r: *const i32) {} fn caller(w: *mut i32, r: *const i32) { target(w, r); }";

    fn expectation(kind: BridgeKind) -> BridgeExpectation {
        let lo = INPUT.find("target(w, r)").unwrap() as u32;
        BridgeExpectation {
            identity: "site:caller:target:arg1".into(),
            kind,
            caller: "caller".into(),
            callee: "target".into(),
            anchor: SiteAnchor::Call {
                span: ByteSpan {
                    lo,
                    hi: lo + "target(w, r)".len() as u32,
                },
                argument_indices: vec![1],
            },
            c9_stamp: None,
            pending_source: None,
            tier: "T2".into(),
            waiver_id: Some(crate::bo_rewriter::bridge_receipt::RAW_BOUNDARY_T2_WAIVER_ID.into()),
        }
    }

    fn raw_output() -> String {
        let lo = INPUT.find("target(w, r)").unwrap();
        format!(
            "fn target(w: &mut i32, r: *const i32) {{}} fn caller(w: &mut i32, r: &i32) {{ {{ let __crat_pair_raw_{lo}_1: *const i32 = core::ptr::from_ref(r); target(w, __crat_pair_raw_{lo}_1); }} }}"
        )
    }

    fn check(output: &str, rows: &[BridgeExpectation]) -> BridgeCustodyReport {
        check_sources(INPUT, output, rows)
    }

    fn check_sources(input: &str, output: &str, rows: &[BridgeExpectation]) -> BridgeCustodyReport {
        let original = syntax::inventory_source("original.rs", input).unwrap();
        let emitted = syntax::inventory_source("emitted.rs", output).unwrap();
        compare(BridgeCustodyInput {
            original: &original,
            emitted: &emitted,
            original_source: input,
            emitted_source: output,
            expectations: rows,
            context: &BridgeCustodyContext::default(),
        })
    }

    #[test]
    fn bridge_custody_match_links_the_site_stamped_raw_view_and_its_call_use() {
        let report = check(&raw_output(), &[expectation(BridgeKind::PairT2RawView)]);
        assert!(report.data, "{report:#?}");
        assert_eq!(report.rows[0].status, ReceiptStatus::MatchedRaw);
        assert_eq!(report.rows[0].bindings.len(), 1);
        assert!(report.tree_only.is_empty());
    }

    #[test]
    fn bridge_custody_match_receipt_without_render_is_missing() {
        let report = check(
            "fn target(w: &mut i32, r: &i32) {} fn caller(w: &mut i32, r: &i32) { target(w, r); }",
            &[expectation(BridgeKind::A5SiteProofT2Fallback)],
        );
        assert!(!report.data);
        assert_eq!(report.rows[0].status, ReceiptStatus::Missing, "{report:#?}");
    }

    #[test]
    fn bridge_custody_match_snapshot_requires_the_exact_private_read() {
        let mut expected = expectation(BridgeKind::PairCopySnapshot);
        expected.c9_stamp = Some(C9Stamp {
            basic_block: 0,
            statement_index: 5,
        });
        expected.tier = "T1".into();
        expected.waiver_id = None;
        let report = check(
            "fn target(w: &mut i32, r: &i32) {} fn caller(w: &mut i32, r: &i32) { { let __crat_c9_0_5: i32 = *r; target(w, &__crat_c9_0_5); } }",
            &[expected],
        );
        assert!(report.data, "{report:#?}");
        assert_eq!(report.rows[0].status, ReceiptStatus::MatchedC9);
    }

    #[test]
    fn bridge_custody_match_unrelated_initializer_cannot_discharge_a_receipt() {
        let output = raw_output().replace("core::ptr::from_ref(r)", "0 as *const i32");
        let report = check(&output, &[expectation(BridgeKind::PairT2RawView)]);
        assert!(!report.data);
        assert!(
            report
                .rows
                .iter()
                .all(|row| row.status != ReceiptStatus::MatchedRaw)
        );
    }

    #[test]
    fn bridge_custody_match_reverse_census_finds_an_unreceipted_view() {
        let report = check(&raw_output(), &[]);
        assert!(!report.data);
        assert!(
            !report.tree_only.is_empty(),
            "the actual unowned bridge must remain visible: {report:#?}"
        );
    }

    #[test]
    fn bridge_custody_match_duplicate_ledger_identity_fails_closed() {
        let expected = expectation(BridgeKind::PairT2RawView);
        let report = check(&raw_output(), &[expected.clone(), expected]);
        assert!(!report.data);
        assert!(
            report
                .issues
                .iter()
                .any(|issue| issue.contains("duplicate")),
            "{report:#?}"
        );
    }

    #[test]
    fn bridge_custody_match_zero_syntax_pending_receipt_is_waived_not_sound() {
        let mut expected = expectation(BridgeKind::SiblingOverlapPending);
        expected.tier = "T2-pending".into();
        expected.waiver_id = Some("c-aliasing-semantics-at-unsafe-bridges/v2-pending".into());
        let report = check(
            "fn target(w: *mut i32, r: *const i32) {} fn caller(w: *mut i32, r: &i32) { target(w, r); }",
            &[expected],
        );
        assert!(report.data, "{report:#?}");
        assert_eq!(report.rows[0].status, ReceiptStatus::WaivedPending);
        assert!(
            report.rows[0].bindings.is_empty(),
            "pending law does not change emission"
        );
    }

    fn pending_expectation() -> BridgeExpectation {
        let mut expected = expectation(BridgeKind::SiblingOverlapPending);
        expected.identity.push_str(":pending");
        expected.tier = "T2-pending".into();
        expected.waiver_id = Some("c-aliasing-semantics-at-unsafe-bridges/v2-pending".into());
        expected
    }

    fn pending_materialized_view(a5: bool) {
        let kind = if a5 {
            BridgeKind::A5SiteProofT2Fallback
        } else {
            BridgeKind::PairT2RawView
        };
        let output = if a5 {
            raw_output().replace("__crat_pair_raw_", "__crat_a5_raw_")
        } else {
            raw_output()
        };
        let report = check(&output, &[expectation(kind), pending_expectation()]);
        assert_eq!(
            report.rows[0].status,
            ReceiptStatus::MatchedRaw,
            "{report:#?}"
        );
        assert_eq!(
            report.rows[1].status,
            ReceiptStatus::WaivedPending,
            "the exact raw-view carrier does not remove the protected caller source: {report:#?}"
        );
        assert_eq!(report.rows[0].emitted_call, report.rows[1].emitted_call);
        assert!(report.data && report.tree_only.is_empty(), "{report:#?}");
    }

    #[test]
    fn bridge_custody_match_pending_accepts_the_receipted_pair_raw_view() {
        pending_materialized_view(false);
    }

    #[test]
    fn bridge_custody_match_pending_accepts_the_receipted_a5_raw_view() {
        pending_materialized_view(true);
    }

    #[test]
    fn bridge_custody_match_pending_accepts_an_exact_inline_from_ref() {
        let report = check(
            "fn target(w: &mut i32, r: *const i32) {} fn caller(w: &mut i32, r: &i32) { target(w, core::ptr::from_ref(r)); }",
            &[pending_expectation()],
        );
        assert_eq!(
            report.rows[0].status,
            ReceiptStatus::WaivedPending,
            "{report:#?}"
        );
        assert!(report.data, "{report:#?}");
    }

    const LOCAL_PENDING_INPUT: &str = "fn target(w: *mut i32, r: *const i32) {} fn caller(w: *mut i32, seed: *const i32) { let r: *const i32 = seed; target(w, r); }";

    fn local_pending_expectation(kind: BridgeKind) -> BridgeExpectation {
        let mut expected = if kind == BridgeKind::SiblingOverlapPending {
            pending_expectation()
        } else {
            expectation(kind)
        };
        let lo = LOCAL_PENDING_INPUT.find("target(w, r)").unwrap() as u32;
        expected.anchor = SiteAnchor::Call {
            span: ByteSpan {
                lo,
                hi: lo + "target(w, r)".len() as u32,
            },
            argument_indices: vec![1],
        };
        expected
    }

    #[test]
    fn bridge_custody_match_pending_accepts_the_corresponding_converted_local() {
        let output = "fn target(w: &mut i32, r: *const i32) {} fn caller(w: &mut i32, seed: &i32) { let r: &i32 = seed; target(w, r); }";
        let report = check_sources(
            LOCAL_PENDING_INPUT,
            output,
            &[local_pending_expectation(BridgeKind::SiblingOverlapPending)],
        );
        assert_eq!(
            report.rows[0].status,
            ReceiptStatus::WaivedPending,
            "{report:#?}"
        );
        assert!(report.data, "{report:#?}");
    }

    #[test]
    fn bridge_custody_match_pending_local_raw_view_shares_the_ordinary_receipt() {
        let lo = LOCAL_PENDING_INPUT.find("target(w, r)").unwrap();
        let output = format!(
            "fn target(w: &mut i32, r: *const i32) {{}} fn caller(w: &mut i32, seed: &i32) {{ let r: &i32 = seed; {{ let __crat_a5_raw_{lo}_1: *const i32 = core::ptr::from_ref(r); target(w, __crat_a5_raw_{lo}_1); }} }}"
        );
        let report = check_sources(
            LOCAL_PENDING_INPUT,
            &output,
            &[
                local_pending_expectation(BridgeKind::A5SiteProofT2Fallback),
                local_pending_expectation(BridgeKind::SiblingOverlapPending),
            ],
        );
        assert_eq!(
            report.rows[0].status,
            ReceiptStatus::MatchedRaw,
            "{report:#?}"
        );
        assert_eq!(
            report.rows[1].status,
            ReceiptStatus::WaivedPending,
            "{report:#?}"
        );
        assert_eq!(report.rows[0].emitted_call, report.rows[1].emitted_call);
        assert!(report.data && report.tree_only.is_empty(), "{report:#?}");
    }

    #[test]
    fn bridge_custody_match_pending_rejects_a_different_local_initializer() {
        let output = "fn target(w: &mut i32, r: *const i32) {} fn caller(w: &mut i32, seed: &i32) { let other = 9; let r: &i32 = &other; target(w, r); }";
        let report = check_sources(
            LOCAL_PENDING_INPUT,
            output,
            &[local_pending_expectation(BridgeKind::SiblingOverlapPending)],
        );
        assert!(!report.data, "{report:#?}");
        assert_ne!(report.rows[0].status, ReceiptStatus::WaivedPending);
    }

    #[test]
    fn bridge_custody_match_pending_rejects_an_unmapped_local_alias() {
        let output = "fn target(w: &mut i32, r: *const i32) {} fn caller(w: &mut i32, seed: &i32) { let r: &i32 = seed; let alias: &i32 = r; target(w, core::ptr::from_ref(alias)); }";
        let report = check_sources(
            LOCAL_PENDING_INPUT,
            output,
            &[local_pending_expectation(BridgeKind::SiblingOverlapPending)],
        );
        assert!(!report.data, "{report:#?}");
        assert_ne!(report.rows[0].status, ReceiptStatus::WaivedPending);
    }

    #[test]
    fn bridge_custody_match_pending_inner_c9_does_not_discharge_the_caller_source() {
        let output = "fn target(w: &mut i32, r: *const i32) {} fn caller(w: &mut i32, r: &i32) { let __crat_c9_0_5: i32 = *r; target(w, &__crat_c9_0_5); let _after = *r; }";
        let stamp = C9Stamp {
            basic_block: 0,
            statement_index: 5,
        };
        let mut snapshot = expectation(BridgeKind::PairCopySnapshot);
        snapshot.tier = "T1".into();
        snapshot.waiver_id = None;
        snapshot.c9_stamp = Some(stamp);
        let mut pending = pending_expectation();
        pending.c9_stamp = Some(stamp);
        let report = check(output, &[snapshot, pending]);
        assert_eq!(
            report.rows[0].status,
            ReceiptStatus::MatchedC9,
            "{report:#?}"
        );
        assert_eq!(
            report.rows[1].status,
            ReceiptStatus::WaivedPending,
            "an inner snapshot changes the carrier, not the original caller protection: {report:#?}"
        );
        assert_eq!(report.rows[0].emitted_call, report.rows[1].emitted_call);
        assert!(report.data && report.tree_only.is_empty(), "{report:#?}");
    }

    fn pending_optional_parameter(mutable: bool) {
        let input = if mutable {
            INPUT.replace("*const i32", "*mut i32")
        } else {
            INPUT.to_owned()
        };
        let lo = input.find("target(w, r)").unwrap() as u32;
        let pointer = if mutable { "*mut i32" } else { "*const i32" };
        let source = if mutable {
            "mut r: Option<&mut i32>"
        } else {
            "r: Option<&i32>"
        };
        let view = if mutable {
            "r.as_deref_mut().map_or(core::ptr::null_mut::<i32>(), core::ptr::from_mut)"
        } else {
            "r.as_deref().map_or(core::ptr::null::<i32>(), core::ptr::from_ref)"
        };
        let output = format!(
            "fn target(w: &mut i32, r: {pointer}) {{}} fn caller(w: &mut i32, {source}) {{ {{ let __crat_a5_raw_{lo}_1: {pointer} = {view}; target(w, __crat_a5_raw_{lo}_1); }} }}"
        );
        let mut raw = expectation(BridgeKind::A5SiteProofT2Fallback);
        let mut pending = pending_expectation();
        for row in [&mut raw, &mut pending] {
            row.anchor = SiteAnchor::Call {
                span: ByteSpan {
                    lo,
                    hi: lo + "target(w, r)".len() as u32,
                },
                argument_indices: vec![1],
            };
        }
        let report = check_sources(&input, &output, &[raw, pending]);
        assert_eq!(
            report.rows[0].status,
            ReceiptStatus::MatchedRaw,
            "{report:#?}"
        );
        assert_eq!(
            report.rows[1].status,
            ReceiptStatus::WaivedPending,
            "nullable reference presentation preserves the pending source obligation: {report:#?}"
        );
        assert_eq!(report.rows[0].emitted_call, report.rows[1].emitted_call);
        assert!(report.data && report.tree_only.is_empty(), "{report:#?}");
    }

    #[test]
    fn r233_pending_option_shared_parameter_null_map() {
        pending_optional_parameter(false);
    }

    #[test]
    fn r233_pending_option_mutable_parameter_null_map() {
        pending_optional_parameter(true);
    }

    // Exact bytes from the one-shot r233-shape-emission-confirmation.json.
    const PROJECTED_INPUT: &str = r##"#![allow(dead_code, unused_unsafe)]
pub struct Holder { data: *mut i32, scalar: i32 }
pub unsafe fn update(dst: *mut i32, src: *const i32) { *dst = *src + 1; }
pub unsafe fn caller(holder: *const Holder) {
update((*holder).data, &(*holder).scalar);
}
pub unsafe fn entry() {
let mut value = 1; let holder = Holder { data: &mut value, scalar: 2 }; caller(&holder);
}
"##;
    const PROJECTED_OUTPUT: &str = r##"#![allow(dead_code, unused_unsafe)]
pub struct Holder { data: *mut i32, scalar: i32 }
pub unsafe fn update(dst: &mut i32, src: *const i32) { *dst = *src + 1; }
pub unsafe fn caller(holder: &Holder) {
    {
        let __crat_a5_raw_206_1: *const i32 =
            core::ptr::from_ref(&(*holder).scalar);
        update(&mut *(*holder).data, __crat_a5_raw_206_1)
    };
}
pub unsafe fn entry() {
let mut value = 1; let holder = Holder { data: &mut value, scalar: 2 }; caller(&holder);
}
"##;

    fn projected_source_start(input: &str) -> u32 {
        // Source-map-only confirmation: this callback never enters decide or
        // any Crat analysis. The start is not inferred from a generated name.
        ::utils::compilation::run_compiler_on_str(input, |tcx| {
            let files = tcx.sess.source_map().files();
            let exact = files
                .iter()
                .filter(|file| {
                    file.src
                        .as_ref()
                        .is_some_and(|source| source.as_str() == input)
                })
                .collect::<Vec<_>>();
            assert_eq!(exact.len(), 1, "exact single-input source-map file");
            let start = exact[0].start_pos.0;
            println!("R233 projected matcher source-map-only start: {start}");
            start
        })
        .expect("source-map-only fixture callback")
    }

    fn projected_pending_case(fault: &str) -> BridgeCustodyReport {
        use sha2::{Digest, Sha256};
        assert_eq!(
            format!("{:x}", Sha256::digest(PROJECTED_INPUT.as_bytes())),
            "0413edb5661ee3709bace5962056e37a0bf0ddbf2cf75f063fddec6468657866"
        );
        assert_eq!(
            format!("{:x}", Sha256::digest(PROJECTED_OUTPUT.as_bytes())),
            "7ea13cb5cf0c92d1a82a39e99ac508f6dad3e1a849b8fdc118d239a23d0a943d"
        );
        let source_global_start = projected_source_start(PROJECTED_INPUT);
        // Only this negative replaces the referent borrow with a loaded raw
        // field value; it is not a new emitted fixture or a model observation.
        let input = if fault == "raw-field" {
            PROJECTED_INPUT.replace("&(*holder).scalar", "(*holder).data")
        } else {
            PROJECTED_INPUT.to_owned()
        };
        let output = if fault == "raw-field" {
            PROJECTED_OUTPUT.replace(
                "core::ptr::from_ref(&(*holder).scalar)",
                "(*holder).data as *const i32",
            )
        } else {
            PROJECTED_OUTPUT.to_owned()
        };
        let original = syntax::inventory_source("projected-original.rs", &input).unwrap();
        let emitted = syntax::inventory_source("projected-emitted.rs", &output).unwrap();
        let calls = original
            .calls
            .iter()
            .filter(|call| call.owner == "caller" && call.callee_path.as_deref() == Some("update"))
            .collect::<Vec<_>>();
        let [call] = calls.as_slice() else { panic!("exact original projected call") };
        let owner = if fault == "wrong-root" {
            "entry"
        } else {
            "caller"
        };
        let bindings = original
            .bindings
            .iter()
            .filter(|binding| binding.owner == owner && binding.name == "holder")
            .collect::<Vec<_>>();
        let [binding] = bindings.as_slice() else { panic!("exact protected-binding declaration") };
        let mut raw = expectation(BridgeKind::A5SiteProofT2Fallback);
        raw.callee = "update".into();
        raw.anchor = SiteAnchor::Call {
            span: call.span,
            argument_indices: vec![1],
        };
        let mut pending = pending_expectation();
        pending.callee = "update".into();
        pending.anchor = SiteAnchor::Argument {
            span: call.arguments[1].span,
            argument_index: 1,
        };
        pending.pending_source = (fault != "missing-metadata").then(|| PendingSource {
            binding: "holder".into(),
            binding_span: binding.binding_span,
            shape: PendingSourceShape::ProjectedReferent,
        });
        compare(BridgeCustodyInput {
            original: &original,
            emitted: &emitted,
            original_source: &input,
            emitted_source: &output,
            expectations: &[raw, pending],
            context: &BridgeCustodyContext {
                source_global_start,
                ..Default::default()
            },
        })
    }

    #[test]
    fn r233_projected_source_matches_the_sealed_emitted_pending_site() {
        let report = projected_pending_case("none");
        assert_eq!(
            report.rows[0].status,
            ReceiptStatus::MatchedRaw,
            "{report:#?}"
        );
        assert_eq!(
            report.rows[1].status,
            ReceiptStatus::WaivedPending,
            "{report:#?}"
        );
        assert_eq!(report.rows[0].emitted_call, report.rows[1].emitted_call);
        assert!(report.data && report.tree_only.is_empty(), "{report:#?}");
    }

    #[test]
    fn r233_projected_source_requires_its_typed_metadata() {
        let report = projected_pending_case("missing-metadata");
        assert_eq!(
            report.rows[0].status,
            ReceiptStatus::MatchedRaw,
            "{report:#?}"
        );
        assert!(
            !report.data && report.rows[1].status != ReceiptStatus::WaivedPending,
            "{report:#?}"
        );
    }

    #[test]
    fn r233_projected_source_rejects_a_different_protected_binding() {
        let report = projected_pending_case("wrong-root");
        assert_eq!(
            report.rows[0].status,
            ReceiptStatus::MatchedRaw,
            "{report:#?}"
        );
        assert!(
            !report.data && report.rows[1].status != ReceiptStatus::WaivedPending,
            "{report:#?}"
        );
    }

    #[test]
    fn r233_projected_source_rejects_a_loaded_raw_field_value() {
        let report = projected_pending_case("raw-field");
        assert_eq!(
            report.rows[0].status,
            ReceiptStatus::MatchedRaw,
            "{report:#?}"
        );
        assert!(
            !report.data && report.rows[1].status != ReceiptStatus::WaivedPending,
            "{report:#?}"
        );
    }

    fn reflowed_local_case(changed: bool) -> BridgeCustodyReport {
        let input = "struct Info { a: i32, b: i32 } fn target(w: *mut Info, r: *mut Info) {} fn caller() { let mut info = Info {\n a: 1,\n b: 2,\n}; target(&mut info, &mut info); }";
        let text = "target(&mut info, &mut info)";
        let lo = input.find(text).unwrap() as u32;
        let mut expected = expectation(BridgeKind::PairT2RawView);
        expected.anchor = SiteAnchor::Call {
            span: ByteSpan {
                lo,
                hi: lo + text.len() as u32,
            },
            argument_indices: vec![1],
        };
        let value = if changed { 9 } else { 2 };
        let output = format!(
            "struct Info {{ a: i32, b: i32 }} fn target(w: &mut Info, r: *mut Info) {{}} fn caller() {{ let mut info = Info {{ a: 1, b: {value}, }}; {{ let __crat_pair_raw_{lo}_1: *mut Info = core::ptr::from_mut(&mut info); target(&mut info, __crat_pair_raw_{lo}_1); }} }}"
        );
        check_sources(input, &output, &[expected])
    }

    #[test]
    fn bridge_custody_match_local_initializer_reflow_keeps_exact_binding_correspondence() {
        let report = reflowed_local_case(false);
        assert!(report.data, "{report:#?}");
        assert_eq!(report.rows[0].status, ReceiptStatus::MatchedRaw);
    }

    #[test]
    fn bridge_custody_match_changed_local_initializer_is_not_formatting() {
        assert!(!reflowed_local_case(true).data);
    }

    fn reconstructed_safe_target(target: &str, use_text: &str, mutable: bool) {
        let lo = INPUT.find("target(w, r)").unwrap();
        let temp = format!("__crat_pair_raw_{lo}_1");
        let pointer = if mutable { "*mut i32" } else { "*const i32" };
        let source = if mutable { "&mut i32" } else { "&i32" };
        let view = if mutable {
            "core::ptr::from_mut(r)"
        } else {
            "core::ptr::from_ref(r)"
        };
        let use_text = use_text.replace("TEMP", &temp);
        let output = format!(
            "fn target(w: &mut i32, r: {target}) {{}} fn caller(w: &mut i32, r: {source}) {{ {{ let {temp}: {pointer} = {view}; target(w, {use_text}); }} }}"
        );
        let report = check(&output, &[expectation(BridgeKind::A5SiteProofT2Fallback)]);
        assert!(!report.data);
        assert_eq!(
            report.rows[0].status,
            ReceiptStatus::InvalidRenderedRole,
            "{report:#?}"
        );
        assert!(report.rows[0].emitted_call.is_some());
        assert_eq!(
            report.rows[0].bindings.len(),
            1,
            "retain the actual temporary evidence"
        );
    }

    #[test]
    fn bridge_custody_match_raw_temp_back_to_shared_ref_is_invalid_role() {
        reconstructed_safe_target("&i32", "&*TEMP", false);
    }

    #[test]
    fn bridge_custody_match_raw_temp_back_to_mutable_ref_is_invalid_role() {
        reconstructed_safe_target("&mut i32", "&mut *TEMP", true);
    }

    #[test]
    fn bridge_custody_match_raw_temp_back_to_slice_is_invalid_role() {
        reconstructed_safe_target("&[i32]", "core::slice::from_raw_parts(TEMP, 1)", false);
    }

    #[test]
    fn bridge_custody_match_raw_temp_back_to_option_ref_is_invalid_role() {
        reconstructed_safe_target("Option<&i32>", "TEMP.as_ref()", false);
    }

    fn pending_with_native_scalar_read(changed_index: bool) -> BridgeCustodyReport {
        let input = "fn target(n: usize, w: *mut i32, r: *const i32) {} fn caller(w: *mut i32, r: *const i32, table: *const i32, index: usize) { target(*table.offset(index as isize) as usize, w, r); }";
        let call = "target(*table.offset(index as isize) as usize, w, r)";
        let lo = input.find(call).unwrap() as u32;
        let mut expected = expectation(BridgeKind::SiblingOverlapPending);
        expected.anchor = SiteAnchor::Call {
            span: ByteSpan {
                lo,
                hi: lo + call.len() as u32,
            },
            argument_indices: vec![2],
        };
        expected.tier = "T2-pending".into();
        expected.waiver_id = Some("c-aliasing-semantics-at-unsafe-bridges/v2-pending".into());
        let index = if changed_index { "index + 1" } else { "index" };
        let output = format!(
            "fn target(n: usize, w: *mut i32, r: *const i32) {{}} fn caller(w: *mut i32, r: &i32, table: &[i32], index: usize) {{ target(table[({index}) as usize] as usize, w, r); }}"
        );
        check_sources(input, &output, &[expected])
    }

    #[test]
    fn bridge_custody_match_pending_preserves_unrelated_native_slice_read_correspondence() {
        let report = pending_with_native_scalar_read(false);
        assert!(report.data, "{report:#?}");
        assert_eq!(report.rows[0].status, ReceiptStatus::WaivedPending);
    }

    #[test]
    fn bridge_custody_match_pending_rejects_a_changed_native_slice_index() {
        assert!(!pending_with_native_scalar_read(true).data);
    }

    fn pending_with_local_native_index(changed_index: bool) -> BridgeCustodyReport {
        let input = "fn target(n: usize, r: *const i32) {} fn caller(r: *const i32, table: *const i32, indices: *const usize) { let i: usize = 0; let index: usize = *indices.offset(i as isize); target(*table.offset(index as isize) as usize, r); }";
        let call = "target(*table.offset(index as isize) as usize, r)";
        let lo = input.find(call).unwrap() as u32;
        let mut expected = expectation(BridgeKind::SiblingOverlapPending);
        expected.anchor = SiteAnchor::Call {
            span: ByteSpan {
                lo,
                hi: lo + call.len() as u32,
            },
            argument_indices: vec![1],
        };
        expected.tier = "T2-pending".into();
        expected.waiver_id = Some("c-aliasing-semantics-at-unsafe-bridges/v2-pending".into());
        let index = if changed_index { "i + 1" } else { "i" };
        let output = format!(
            "fn target(n: usize, r: *const i32) {{}} fn caller(r: &i32, table: &[i32], indices: &[usize]) {{ let i: usize = 0; let index: usize = indices[({index}) as usize]; target(table[(index) as usize] as usize, r); }}"
        );
        check_sources(input, &output, &[expected])
    }

    #[test]
    fn bridge_custody_match_pending_tracks_the_local_index_initializer() {
        let report = pending_with_local_native_index(false);
        assert!(report.data, "{report:#?}");
        assert_eq!(report.rows[0].status, ReceiptStatus::WaivedPending);
    }

    #[test]
    fn bridge_custody_match_pending_rejects_a_changed_local_index_initializer() {
        assert!(!pending_with_local_native_index(true).data);
    }
}
