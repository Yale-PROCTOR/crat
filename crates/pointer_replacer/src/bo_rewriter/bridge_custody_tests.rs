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

    fn pending_native_return_expression_consumer_case(fault: &str) -> BridgeCustodyReport {
        // Consumer-only pinned syntax: this exercises no decision pipeline,
        // native lifetime proof, alias verdict, solver, or corpus worker.
        let input = "unsafe fn identity(p: *const i32) -> *const i32 { p } unsafe fn target(r: *const i32, peer: *const i32) {} unsafe fn caller(p: *const i32, peer: *const i32) { target(identity(p), peer); }";
        let output = "unsafe fn identity<'a>(p: &'a i32) -> &'a i32 { p } unsafe fn target(r: *const i32, peer: *const i32) {} unsafe fn caller(p: &i32, peer: *const i32) { target({ let __crat_outbound_return_3_17: &i32 = (identity(p)); (core::ptr::from_ref(__crat_outbound_return_3_17)) as *const i32 }, peer); }";
        let original = syntax::inventory_source("native-expression-original.rs", input).unwrap();
        let emitted = syntax::inventory_source("native-expression-emitted.rs", output).unwrap();
        let original_calls = original
            .calls
            .iter()
            .filter(|call| call.owner == "caller" && call.callee_path.as_deref() == Some("target"))
            .collect::<Vec<_>>();
        let [original_call] = original_calls.as_slice() else { panic!("one original outer call") };
        let argument = &original_call.arguments[0];
        assert!(
            argument.binding.is_none(),
            "the original source is a native call expression, not a declaration root"
        );
        let source_calls = original
            .calls
            .iter()
            .filter(|call| {
                call.owner == "caller"
                    && call.span == argument.span
                    && call.callee_path.as_deref() == Some("identity")
            })
            .collect::<Vec<_>>();
        let [source_call] = source_calls.as_slice() else {
            panic!("the exact original source call occupies argument zero")
        };
        let emitted_calls = emitted
            .calls
            .iter()
            .filter(|call| call.owner == "caller" && call.callee_path.as_deref() == Some("target"))
            .collect::<Vec<_>>();
        let [emitted_call] = emitted_calls.as_slice() else { panic!("one emitted outer call") };
        let emitted_argument = &emitted_call.arguments[0];
        let temporaries = emitted
            .bindings
            .iter()
            .filter(|binding| {
                binding.owner == "caller"
                    && binding.name == "__crat_outbound_return_3_17"
                    && emitted_argument.span.lo <= binding.declaration_span.lo
                    && binding.declaration_span.hi <= emitted_argument.span.hi
            })
            .collect::<Vec<_>>();
        let [temporary] = temporaries.as_slice() else {
            panic!("one actual temporary inside the selected emitted argument")
        };
        assert_eq!(temporary.type_text.as_deref(), Some("&i32"));
        assert_eq!(temporary.init_text.as_deref(), Some("(identity(p))"));
        let views = emitted
            .calls
            .iter()
            .filter(|call| {
                call.owner == "caller"
                    && call.callee_path.as_deref() == Some("core::ptr::from_ref")
                    && emitted_argument.span.lo <= call.span.lo
                    && call.span.hi <= emitted_argument.span.hi
            })
            .collect::<Vec<_>>();
        let [view] = views.as_slice() else {
            panic!("one exact raw view of the returned temporary")
        };
        assert_eq!(
            view.arguments[0].binding.as_ref().map(|binding| binding.id),
            Some(temporary.id)
        );
        let mut expected = BridgeExpectation {
            identity: "consumer-only:native-return-expression:arg0".into(),
            kind: BridgeKind::SiblingOverlapPending,
            caller: "caller".into(),
            callee: "target".into(),
            anchor: SiteAnchor::Argument {
                span: argument.span,
                argument_index: 0,
            },
            c9_stamp: None,
            pending_source: Some(PendingSource {
                binding: None,
                binding_span: None,
                shape: PendingSourceShape::NativeReturnExpression {
                    argument_span: argument.span,
                    source_call_span: source_call.span,
                    // Opaque consumer fixture identity; this parser control
                    // makes no claim about a compiler-assigned definition ID.
                    source_owner: 1,
                    source_function: "identity".into(),
                    source_form: "ref-shared".into(),
                    source_type: "&i32".into(),
                    temporary: temporary.name.clone(),
                    template: "ref-shared-to-raw-const".into(),
                },
            }),
            tier: "T2-pending".into(),
            waiver_id: Some("c-aliasing-semantics-at-unsafe-bridges/v2-pending".into()),
        };
        let altered = match fault {
            "wrong-temporary" => output.replace("__crat_outbound_return_3_17", "__crat_outbound_return_3_18"),
            "wrong-source-callee" => output.replace("(identity(p))", "(another(p))"),
            "missing-view" => output.replace("(core::ptr::from_ref(__crat_outbound_return_3_17)) as *const i32", "core::ptr::null::<i32>()"),
            "receipt-without-carrier" => output.replace("{ let __crat_outbound_return_3_17: &i32 = (identity(p)); (core::ptr::from_ref(__crat_outbound_return_3_17)) as *const i32 }", "identity(p) as *const i32"),
            "wrong-native-type" => output.replace("__crat_outbound_return_3_17: &i32", "__crat_outbound_return_3_17: *const i32"),
            "changed-sibling" => output.replace("}, peer);", "}, p as *const i32);"),
            "source-rename" => output.replace("identity", "__crat_safe_identity"),
            _ => output.to_owned(),
        };
        if fault == "wrong-source-descriptor"
            && let Some(PendingSource {
                shape:
                    PendingSourceShape::NativeReturnExpression {
                        source_function, ..
                    },
                ..
            }) = &mut expected.pending_source
        {
            *source_function = "target".into();
        }
        let context = if fault == "source-rename" {
            BridgeCustodyContext {
                owner_renames: vec![OwnerRename {
                    original_owner: "identity".into(),
                    emitted_owner: "__crat_safe_identity".into(),
                    evidence: "consumer-only:explicit-native-source-rename".into(),
                }],
                callee_renames: vec![CalleeRename {
                    original_caller: "caller".into(),
                    original_callee_text: "identity".into(),
                    emitted_callee_text: "__crat_safe_identity".into(),
                    evidence: "consumer-only:explicit-native-call-rename".into(),
                }],
                ..Default::default()
            }
        } else {
            BridgeCustodyContext::default()
        };
        let emitted = syntax::inventory_source("native-expression-control.rs", &altered).unwrap();
        let report = compare(BridgeCustodyInput {
            original: &original,
            emitted: &emitted,
            original_source: input,
            emitted_source: &altered,
            expectations: &[expected],
            context: &context,
        });
        println!("R236 native-expression parser consumer control {fault}: {report:#?}");
        report
    }

    #[test]
    fn r236_pending_native_return_expression_parser_consumer_control() {
        let report = pending_native_return_expression_consumer_case("none");
        assert_eq!(
            report.rows[0].status,
            ReceiptStatus::WaivedPending,
            "the selected native-result temporary/raw view must have custody without an invented declaration source: {report:#?}"
        );
        assert!(report.data && report.tree_only.is_empty(), "{report:#?}");
    }

    #[test]
    fn r236_pending_native_return_expression_parser_consumer_faults() {
        for fault in [
            "wrong-temporary",
            "wrong-source-callee",
            "wrong-source-descriptor",
            "missing-view",
            "receipt-without-carrier",
            "wrong-native-type",
            "changed-sibling",
        ] {
            let report = pending_native_return_expression_consumer_case(fault);
            assert!(
                !report.data && report.rows[0].status != ReceiptStatus::WaivedPending,
                "consumer-only native carrier fault {fault} must be rejected: {report:#?}"
            );
        }
    }

    #[test]
    fn r236_pending_native_return_expression_parser_consumer_source_rename() {
        let report = pending_native_return_expression_consumer_case("source-rename");
        assert!(
            report.data && report.rows[0].status == ReceiptStatus::WaivedPending,
            "consumer-only explicit source-function/call rename receipts preserve custody: {report:#?}"
        );
    }

    fn native_slice_source_consumer_case(fault: &str) -> BridgeCustodyReport {
        // Consumer-only version of the banked target(p) ->
        // target(from_raw_parts_mut(p, FALLBACK_SLICE_EXTENT)) shape.
        // The length waiver and native proof come from production receipts;
        // this parser control creates neither of those facts.
        let input = "unsafe fn raw_pair(q: *const i32, dst: *mut i32) -> i32 { dst.write(8); q.read() } unsafe fn target(p: *mut i32) -> *mut i32 { *p.offset(1) += 1; p } unsafe fn caller(p: *mut i32) -> i32 { raw_pair(target(p), p) }";
        let output = "unsafe fn raw_pair(q: *const i32, dst: *mut i32) -> i32 { dst.write(8); q.read() } unsafe fn target<'a>(p: &'a mut [i32]) -> &'a mut [i32] { p[1] += 1; p } unsafe fn caller(p: *mut i32) -> i32 { raw_pair({ let __crat_outbound_return_5_7: &mut [i32] = (target(core::slice::from_raw_parts_mut(p, crate::FALLBACK_SLICE_EXTENT))); (__crat_outbound_return_5_7.as_ptr()) as *const i32 }, p) } const FALLBACK_SLICE_EXTENT: usize = 1024;";
        let output = match fault {
            "wrong-operand" => {
                output.replace("from_raw_parts_mut(p,", "from_raw_parts_mut(p.add(1),")
            }
            "wrong-constructor" => output.replace(
                "core::slice::from_raw_parts_mut",
                "custom::from_raw_parts_mut",
            ),
            "wrong-mutability" => output.replace("from_raw_parts_mut", "from_raw_parts"),
            "wrong-arity" => output.replace(
                "p, crate::FALLBACK_SLICE_EXTENT",
                "p, crate::FALLBACK_SLICE_EXTENT, 0",
            ),
            "wrong-extent" => output.replace("p, crate::FALLBACK_SLICE_EXTENT", "p, 0"),
            "wrong-element-type" => output.replace("p: &'a mut [i32]", "p: &'a mut [u32]"),
            _ => output.to_owned(),
        };
        let original = syntax::inventory_source("native-slice-source-original.rs", input).unwrap();
        let emitted = syntax::inventory_source("native-slice-source-emitted.rs", &output).unwrap();
        let outer = original
            .calls
            .iter()
            .filter(|call| {
                call.owner == "caller" && call.callee_path.as_deref() == Some("raw_pair")
            })
            .collect::<Vec<_>>();
        let [outer] = outer.as_slice() else { panic!("one original raw sink") };
        let argument = &outer.arguments[0];
        assert_eq!(argument.text, "target(p)");
        assert!(argument.binding.is_none());
        let source = original
            .calls
            .iter()
            .filter(|call| {
                call.owner == "caller"
                    && call.span == argument.span
                    && call.callee_path.as_deref() == Some("target")
            })
            .collect::<Vec<_>>();
        let [source] = source.as_slice() else { panic!("one original native source call") };
        assert_eq!(source.arguments[0].text, "p");
        let expected = BridgeExpectation {
            identity: "consumer-only:native-slice-source-adapter:arg0".into(),
            kind: BridgeKind::SiblingOverlapPending,
            caller: "caller".into(),
            callee: "raw_pair".into(),
            anchor: SiteAnchor::Argument {
                span: argument.span,
                argument_index: 0,
            },
            c9_stamp: None,
            pending_source: Some(PendingSource {
                binding: None,
                binding_span: None,
                shape: PendingSourceShape::NativeReturnExpression {
                    argument_span: argument.span,
                    source_call_span: source.span,
                    source_owner: 4,
                    source_function: "target".into(),
                    source_form: "slice-mut".into(),
                    source_type: "&mut [i32]".into(),
                    temporary: "__crat_outbound_return_5_7".into(),
                    template: "slice-to-raw-const".into(),
                },
            }),
            tier: "T2-pending".into(),
            waiver_id: Some("c-aliasing-semantics-at-unsafe-bridges/v2-pending".into()),
        };
        let report = compare(BridgeCustodyInput {
            original: &original,
            emitted: &emitted,
            original_source: input,
            emitted_source: &output,
            expectations: &[expected],
            context: &BridgeCustodyContext::default(),
        });
        println!("R236 native source-call slice adapter consumer control {fault}: {report:#?}");
        report
    }

    #[test]
    fn r236_pending_native_slice_source_adapter_parser_consumer_control() {
        let report = native_slice_source_consumer_case("none");
        assert!(
            report.data && report.rows[0].status == ReceiptStatus::WaivedPending,
            "the banked inner source-call slice adapter preserves operand custody: {report:#?}"
        );
    }

    #[test]
    fn r236_pending_native_slice_source_adapter_parser_consumer_faults() {
        for fault in [
            "wrong-operand",
            "wrong-constructor",
            "wrong-mutability",
            "wrong-arity",
            "wrong-extent",
            "wrong-element-type",
        ] {
            let report = native_slice_source_consumer_case(fault);
            assert!(
                !report.data && report.rows[0].status != ReceiptStatus::WaivedPending,
                "consumer-only native source adapter fault {fault} must be rejected: {report:#?}"
            );
        }
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
            binding: Some("holder".into()),
            binding_span: Some(binding.binding_span),
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

/// Q-J20-CARRIER custody witnesses (seat addendum 259(5)). The nested carrier
/// got its own `PendingSourceShape` variant rather than a loosened rule on the
/// existing one, so what has to be shown is that neither arm accepts what the
/// other describes.
mod native_expression_interval {
    use super::super::{
        bridge_custody_match::native_expression_interval_ok, delivery_custody::ByteSpan,
    };

    fn span(lo: u32, hi: u32) -> ByteSpan {
        ByteSpan { lo, hi }
    }

    /// The existing arm still rejects drift: an edit strictly inside the
    /// argument is exactly what the bare carrier may not claim, and this is
    /// the rule that would have had to be loosened to admit the nested shape
    /// without its own variant.
    #[test]
    fn bare_carrier_rejects_a_strictly_nested_edit() {
        assert!(!native_expression_interval_ok(
            &span(100, 140),
            &span(100, 120),
            false
        ));
        assert!(native_expression_interval_ok(
            &span(100, 140),
            &span(100, 140),
            false
        ));
    }

    /// A nested carrier claiming the whole argument is a mismatched receipt:
    /// it describes an edit the emitter did not make.
    #[test]
    fn nested_carrier_rejects_an_edit_equal_to_the_argument() {
        assert!(!native_expression_interval_ok(
            &span(100, 140),
            &span(100, 140),
            true
        ));
    }

    /// A nested carrier whose edit escapes the argument is caught on either
    /// side, which is the deliberate fault this rule exists to kill.
    #[test]
    fn nested_carrier_rejects_an_edit_outside_the_argument() {
        assert!(!native_expression_interval_ok(
            &span(100, 140),
            &span(90, 120),
            true
        ));
        assert!(!native_expression_interval_ok(
            &span(100, 140),
            &span(120, 150),
            true
        ));
        assert!(!native_expression_interval_ok(
            &span(100, 140),
            &span(200, 210),
            true
        ));
    }

    /// What it does accept: strict containment at either end and in the middle.
    #[test]
    fn nested_carrier_accepts_strict_containment() {
        for (lo, hi) in [(100, 120), (120, 140), (110, 130)] {
            assert!(
                native_expression_interval_ok(&span(100, 140), &span(lo, hi), true),
                "{lo}..{hi} sits inside 100..140"
            );
        }
    }
}

#[cfg(test)]
mod r304_local_type_correspondence {
    use super::super::bridge_custody_match::local_types_correspond_for_test;

    /// The predicate parses types, so it needs session globals like every
    /// other parser-backed check in this file.
    fn correspond(raw: &str, safe: &str) -> bool {
        rustc_span::create_session_globals_then(
            rustc_span::edition::Edition::Edition2018,
            &[],
            None,
            || local_types_correspond_for_test(Some(raw), Some(safe)).unwrap(),
        )
    }

    /// **Witness.** Every safe form the emitter produces for a raw local
    /// corresponds, and the pointee identity is what carries it.
    #[test]
    fn r304_the_emitted_safe_forms_correspond_to_their_raw_local() {
        for (raw, safe) in [
            ("*mut i32", "&mut i32"),
            ("*const i32", "&i32"),
            ("*mut i32", "Option<&mut i32>"),
            ("*const i32", "Option<&i32>"),
            ("*mut i32", "&mut [i32]"),
            (
                "*mut std::os::raw::c_char",
                "Option<&mut [std::os::raw::c_char]>",
            ),
        ] {
            assert!(correspond(raw, safe), "{raw} -> {safe}");
        }
    }

    /// **Fault.** The identity requirement is unchanged: a different pointee
    /// never corresponds, and a shared raw pointer never yields a mutable
    /// reference.
    #[test]
    fn r304_a_different_pointee_or_a_widened_mutability_still_refuses() {
        for (raw, safe) in [
            ("*mut i32", "&mut u8"),
            ("*const i32", "&mut i32"),
            ("*const i32", "Option<&mut i32>"),
            ("*mut i32", "Option<&mut [u8]>"),
            ("*mut i32", "Option<i32>"),
        ] {
            assert!(!correspond(raw, safe), "{raw} -> {safe}");
        }
    }
}

#[cfg(test)]
mod r306_void_carrier {
    use super::super::bridge_custody_match::whole_subject_uses_for_test;

    fn uses(expression: &str, binding: &str) -> bool {
        rustc_span::create_session_globals_then(
            rustc_span::edition::Edition::Edition2018,
            &[],
            None,
            || whole_subject_uses_for_test(expression, binding),
        )
    }

    /// **Witness.** The K19′ void carrier is the whole subject wearing a
    /// raw-pointer cast, and the bare path still is too.
    #[test]
    fn r306_the_void_carrier_is_the_whole_subject() {
        for text in [
            "p",
            "p as *const libc::c_void",
            "p as *mut libc::c_void",
            "(p) as *const core::ffi::c_void",
            "p as *const u8 as *const libc::c_void",
        ] {
            assert!(uses(text, "p"), "{text}");
        }
    }

    /// **Fault.** Only raw-pointer casts are peeled, and only the binding's own
    /// path survives them.
    #[test]
    fn r306_a_non_pointer_cast_or_another_binding_is_not_the_whole_subject() {
        for (text, binding) in [
            ("q as *const libc::c_void", "p"),
            ("p as usize", "p"),
            ("p as usize as *const libc::c_void", "p"),
            ("(*p).field as *const libc::c_void", "p"),
            ("p.offset(1) as *const libc::c_void", "p"),
        ] {
            assert!(!uses(text, binding), "{text} / {binding}");
        }
    }
}
