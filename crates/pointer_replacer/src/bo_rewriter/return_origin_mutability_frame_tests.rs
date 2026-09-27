//! **R586-2 (main 118) — the sole-origin mutability rule, read on avl's own frame.**
//!
//! The corpus hold is gate 2 of avl's `minValueNode` wall
//! (`dropped-site:seam-shared-to-mut`), and only the L01⁹ model reaches it:
//! `node` decides `ref`, the return keeps the exported `*mut`. A fixture stops at
//! gate 1 (`escapes-via-return`), so the witness reads avl's substrate under the
//! frame's accepted model through the census's one-iteration instrument, with no
//! solve. Run by hand, never by the suite: `CRAT_R586_PROGRAM=<…/rs-crown-derived/
//! avl/lib.rs>` with the L01⁹ frame's env (`l01p9-extra-env.sh`) on a head
//! carrying the L01⁹ analyses.

/// The census's own one-iteration capture (`diagnose_raw_boundary_census_with_config`)
/// of the program whose substrate `lib.rs` the variable names.
fn frame_of(var: &str) -> super::E1Capture {
    let root = std::path::PathBuf::from(
        std::env::var(var).unwrap_or_else(|_| panic!("{var}: the program's substrate lib.rs")),
    );
    assert_eq!(
        std::env::var("CRAT_ERA5_EXECUTION_ROLE").as_deref(),
        Ok("cache-only"),
        "the frame is read from its accepted cache, never solved"
    );
    let config = super::EmissionRunConfig {
        configured_exposure: super::decision::exposure::ConfiguredExposureInput::checked(
            "standing-raw-boundary-launch:Config::default.c_exposed_fns",
            Vec::new(),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        )
        .expect("the configured exposure row"),
    };
    super::diagnose_raw_boundary_census_with_config(&root, &config)
        .expect("the one-iteration capture")
}

/// `key -> (decision, reason, exclusion)` from the census subject receipt.
fn decisions(receipt: &str) -> std::collections::BTreeMap<String, (String, String, String)> {
    receipt
        .lines()
        .skip(1)
        .filter_map(|line| {
            let f = line.split('\t').collect::<Vec<_>>();
            (f.len() == 14).then(|| {
                (
                    f[0].to_owned(),
                    (f[7].to_owned(), f[8].to_owned(), f[12].to_owned()),
                )
            })
        })
        .collect()
}

/// Writes the receipt, the emitted tree and the verify record next to
/// `CRAT_R586_OUT`, when set.
fn record(capture: &super::E1Capture) {
    let Ok(out) = std::env::var("CRAT_R586_OUT") else {
        return;
    };
    std::fs::write(&out, &capture.subject_receipt).expect("write the receipt");
    let tree = capture
        .emitted_files
        .iter()
        .flat_map(|files| files.values())
        .cloned()
        .collect::<Vec<_>>()
        .join("\n");
    std::fs::write(format!("{out}.emitted.rs"), tree).expect("write the emitted tree");
    std::fs::write(
        format!("{out}.verify.txt"),
        format!(
            "outcome={:?} reverted={} rounds={}\nreverts={:#?}\nfirst_diags={:#?}\n",
            capture.outcome_kind,
            capture.reverted_count,
            capture.verify_rounds,
            capture.reverts,
            capture.first_diags
        ),
    )
    .expect("write the verify record");
}

/// **R586-2 witness (the hold).** avl's `#[no_mangle] minValueNode(node: *mut
/// Node) -> *mut Node` returns its one formal: the formal is the sole origin of a
/// mutable scalar return, so it is decided mutable, the return seam no longer
/// refuses a shared source, and its own emission type-checks (the loop's read of
/// the owning `left` renders `as_deref_mut()`). RED without the rule: `node#1`
/// decides shared `ref` and reads
/// `terminal-not-applied:dropped-site:seam-shared-to-mut`.
#[test]
#[ignore = "R586-2: avl's L01^9 frame; run by hand with CRAT_R586_PROGRAM and the frame's env"]
fn r586_2_avl_min_value_node_takes_its_mutable_origin() {
    let capture = frame_of("CRAT_R586_PROGRAM");
    record(&capture);
    let decisions = decisions(&capture.subject_receipt);
    let (decision, reason, exclusion) = decisions
        .get("src::avl::minValueNode::node#1")
        .unwrap_or_else(|| panic!("minValueNode::node#1 in\n{}", capture.subject_receipt));
    assert!(
        !exclusion.contains("seam-shared-to-mut"),
        "the return seam still refuses the shared formal: decision={decision} reason={reason} exclusion={exclusion}"
    );
    let own = capture
        .reverts
        .iter()
        .filter(|revert| revert.function == "src::avl::minValueNode")
        .map(|revert| revert.diagnostic.message.clone())
        .collect::<Vec<_>>();
    assert!(
        own.is_empty(),
        "minValueNode's own emission does not type-check: {own:?}"
    );
}

/// **R586-2 witness (the delivery), on the avl line** (the rotations' walls
/// fixed): `minValueNode<'a>(mut node: &'a mut Node) -> &'a mut Node`. On a head
/// without the line, avl's rotation classes revert and take `minValueNode` with
/// them (`closure:partition`), so this reads the composed line only.
#[test]
#[ignore = "R586-2: avl's L01^9 frame on the avl line; run by hand like the hold witness"]
fn r586_2_avl_line_delivers_min_value_node_mutable() {
    let capture = frame_of("CRAT_R586_PROGRAM");
    record(&capture);
    let text = capture
        .emitted_files
        .iter()
        .flat_map(|files| files.values())
        .find(|text| text.contains("fn minValueNode"))
        .unwrap_or_else(|| {
            panic!(
                "no emitted minValueNode ({:?}: {})",
                capture.outcome_kind, capture.escalation
            )
        });
    let at = text.find("fn minValueNode").expect("found above");
    let signature = text[at..]
        .split('{')
        .next()
        .expect("a body")
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    assert_eq!(
        signature, "fn minValueNode<'a>(mut node: &'a mut Node) -> &'a mut Node",
        "the sole-origin formal and the return are mutable references"
    );
}

/// The rule's shape in a one-file crate: an exported function that reads
/// through its one formal and returns it.
const R586_SHAPE: &str = r#"
#[repr(C)]
pub struct Node {
    pub key: i32,
}
#[no_mangle]
pub unsafe extern "C" fn first(mut node: *mut Node) -> *mut Node {
    let _k = (*node).key;
    return node;
}
"#;

/// An in-program caller whose argument is only read: it decides shared.
const R586_CALLER: &str = r#"
pub unsafe fn peek(mut n: *mut Node) -> i32 {
    let mut m = first(n);
    return (*m).key;
}
"#;

/// Two formals, one returned: `a` is the sole origin, `b` is only read.
const R586_TWO_FORMALS: &str = r#"
#[repr(C)]
pub struct Node {
    pub key: i32,
}
#[no_mangle]
pub unsafe extern "C" fn pick(mut a: *mut Node, mut b: *mut Node) -> *mut Node {
    let _k = (*a).key + (*b).key;
    return a;
}
"#;

/// The fixture's receipts, under the crate-wide frame lock (no model override
/// may leak in from a concurrent test).
fn fixture(src: &str) -> super::plan::class_split::fixture::Receipts {
    let _frame = super::test_model_override::frame_lock();
    super::plan::class_split::fixture::run(src)
}

fn exclusion<'a>(receipts: &'a super::plan::class_split::fixture::Receipts, key: &str) -> &'a str {
    super::plan::class_split::fixture::column(&receipts.subjects, key, "exclusion")
}

/// **R586-2 witness (the shape).** The exported formal that is the sole origin
/// of the mutable scalar return is decided mutable: the function delivers
/// `&'a mut Node -> &'a mut Node`. RED without the rule: `first::node#1` is
/// held on the return seam (`dropped-site:seam-shared-to-mut`).
#[test]
fn r586_2_an_exported_sole_origin_formal_takes_the_return_mutability() {
    let out = fixture(R586_SHAPE);
    assert_eq!(exclusion(&out, "first::node#1"), "-", "{}", out.subjects);
    assert!(
        super::wave6a_allocation_tests::compact(out.tree())
            .contains("fnfirst<'a>(mutnode:&'amutNode)->&'amutNode{"),
        "{}",
        out.tree()
    );
}

/// **R586-2 control.** An in-program caller passing a shared argument into the
/// upgraded formal meets the existing call-site shared-to-mut gate (`peek` →
/// `first`, argument 0): the callee's signature class holds and the caller with
/// it, so nothing hands a shared reference to a `&mut` formal. Both functions
/// stay raw.
#[test]
fn r586_2_a_caller_holding_a_shared_argument_keeps_its_hold() {
    let out = fixture(&format!("{R586_SHAPE}{R586_CALLER}"));
    assert!(
        exclusion(&out, "first::node#1").contains("seam-shared-to-mut"),
        "{}",
        out.subjects
    );
    assert!(
        exclusion(&out, "peek::n#1").contains("dependency-class-held"),
        "{}",
        out.subjects
    );
    let tree = super::wave6a_allocation_tests::compact(out.tree());
    assert!(
        tree.contains("fnfirst(mutnode:*mutNode)->*mutNode{")
            && tree.contains("fnpeek(mutn:*mutNode)->i32{"),
        "{}",
        out.tree()
    );
}

/// **R586-2 witness (the sole-subject guard).** `pick` returns its origin `a`
/// but also reads a second pointer formal `b`, which C may pass aliased with `a`
/// (`pick(p, p)`): `a` stays shared and `pick` holds on the return seam, as
/// before the rule. The fault (the guard removed) upgrades `a` and delivers
/// `pick<'a>(a: &'a mut Node, b: &Node)`, a `&mut` beside a possibly aliased `&`.
#[test]
fn r586_2_a_second_pointer_subject_keeps_the_rule_out() {
    let out = fixture(R586_TWO_FORMALS);
    assert!(
        exclusion(&out, "pick::a#1").contains("seam-shared-to-mut"),
        "{}",
        out.subjects
    );
    assert!(
        super::wave6a_allocation_tests::compact(out.tree())
            .contains("fnpick(muta:*mutNode,mutb:*mutNode)->*mutNode{"),
        "{}",
        out.tree()
    );
}
