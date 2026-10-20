//! **R585-4 — the sealed-source-input edge rule, read on a program's own frame.**
//!
//! `plan::class_split::keeps_interface_dependency` no longer keeps a zero-syntax
//! interface edge whose callee position seals the caller's input-form rendering.
//! These witnesses read a program's substrate under its frame's accepted model,
//! through the census's one-iteration instrument (one decision, one emission,
//! one baseline-subtracted verify), with no solve. Run by hand, never by the
//! suite: `CRAT_R585_PROGRAM=<…/rs-crown-derived/<program>/lib.rs>` with the
//! frame's env; `CRAT_R585_OUT` names a file for the record.

/// The one-iteration capture of the program whose substrate `lib.rs` the
/// variable names (every corpus program's configured exposure row is the
/// explicit-empty one).
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
    super::rewrite_core_injected_with_config(
        ::utils::compilation::path_to_input(&root),
        Some(&root),
        super::MAX_REVERT_ROUNDS,
        &|_| {},
        false,
        true,
        false,
        None,
        &config,
    )
    .into_e1_capture()
    .expect("the one-iteration capture")
}

/// `key -> (decision, reason, exclusion)` from the census subject receipt
/// (`key owner local arg depth family model decision reason detail site placed
/// exclusion sole_blocker`).
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

/// `owner -> [terminal blocking_reason]` from the plan's arm outcomes, read by
/// column name (rows carry one column more than the header names).
fn holds(outcomes: &str) -> std::collections::BTreeMap<String, Vec<String>> {
    let mut lines = outcomes.lines();
    let header = lines
        .next()
        .unwrap_or_default()
        .split('\t')
        .collect::<Vec<_>>();
    let at = |name: &str| {
        header
            .iter()
            .position(|c| *c == name)
            .expect("arm outcome column")
    };
    let (owner, terminal, reason) = (at("owner"), at("terminal"), at("blocking_reason"));
    let mut out = std::collections::BTreeMap::<String, Vec<String>>::new();
    for f in lines.map(|l| l.split('\t').collect::<Vec<_>>()) {
        if f.len() >= header.len() {
            out.entry(f[owner].to_owned())
                .or_default()
                .push(format!("{} {}", f[terminal], f[reason]));
        }
    }
    out
}

/// The family withdrawals on `new-family-dependency:` (R397-6(a)'s arm) and
/// every subject's decision, for a RED / GREEN comparison of any program.
#[test]
#[ignore = "R585-4: a program's frame; run by hand with CRAT_R585_PROGRAM and the frame's env"]
fn r585_4_frame_record() {
    let capture = frame_of("CRAT_R585_PROGRAM");
    let mut record = vec!["== new-family-dependency withdrawals".to_owned()];
    for receipt in &capture.raw_boundary_artifacts.additive_family_receipts {
        if receipt.cause.contains("new-family-dependency:") {
            record.push(format!(
                "{}\t{}\t{}\t{}",
                receipt.family, receipt.owner_path, receipt.scope, receipt.cause
            ));
        }
    }
    record.push("== decisions".to_owned());
    for (key, (decision, reason, exclusion)) in decisions(&capture.subject_receipt) {
        record.push(format!("{key}\t{decision}\t{reason}\t{exclusion}"));
    }
    std::fs::write(
        std::env::var("CRAT_R585_OUT").expect("CRAT_R585_OUT"),
        record.join("\n") + "\n",
    )
    .expect("write the record");
}

const PREPARE_H2: &str = "src::enc::encode::PrepareH2";
const PREPARE_H2_DATA: &str = "src::enc::encode::PrepareH2::data#4";
const HASHER_SETUP: &str = "src::enc::encode::HasherSetup";

/// batch 42's shape (with the field-origin rule in): `HasherSetup::data#4` is
/// decided `slice` but held with its class (`seam-positive-retention`), and
/// `HasherSetup` passes it bare to `PrepareH2`. The callee position seals the
/// caller's input form (`source-input:c-raw-slice-shared`, batch 39's rendering),
/// so `PrepareH2` is not tied to the held class and its `SliceUse` family stays.
#[test]
#[ignore = "R585-4: brotli's frame; run by hand with CRAT_R585_PROGRAM and the frame's env"]
fn r585_4_brotli_prepare_h2_is_not_tied_to_the_held_hasher_setup() {
    let capture = frame_of("CRAT_R585_PROGRAM");
    let decisions = decisions(&capture.subject_receipt);
    let holds = holds(&capture.raw_boundary_artifacts.arm_outcomes);
    let withdrawals = capture
        .raw_boundary_artifacts
        .additive_family_receipts
        .iter()
        .filter(|r| r.owner_path == PREPARE_H2 && r.cause.contains("new-family-dependency:"))
        .map(|r| format!("{} {}", r.family, r.cause))
        .collect::<Vec<_>>();
    let data = decisions.get(PREPARE_H2_DATA).cloned();
    let hasher_setup = holds.get(HASHER_SETUP).cloned().unwrap_or_default();
    let record = [
        format!("== {PREPARE_H2_DATA}: {data:?}"),
        format!("== {PREPARE_H2} withdrawals: {withdrawals:?}"),
        format!("== {PREPARE_H2} holds: {:?}", holds.get(PREPARE_H2)),
        format!("== {HASHER_SETUP} holds: {hasher_setup:?}"),
    ];
    if let Ok(out) = std::env::var("CRAT_R585_OUT") {
        std::fs::write(out, record.join("\n") + "\n").expect("write the record");
    }
    let mut failures = Vec::new();
    // Witness: the family stays and the formal is decided a slice …
    if !withdrawals.is_empty() {
        failures.push(format!("witness: {PREPARE_H2} withdrawn: {withdrawals:?}"));
    }
    if data.as_ref().map(|(decision, ..)| decision.as_str()) != Some("slice") {
        failures.push(format!("witness: {PREPARE_H2_DATA} is {data:?}"));
    }
    // … while the caller is still held on its own wall.
    if !hasher_setup
        .iter()
        .any(|h| h.contains("seam-positive-retention"))
    {
        failures.push(format!(
            "precondition: {HASHER_SETUP} is not held: {hasher_setup:?}"
        ));
    }
    assert!(failures.is_empty(), "{failures:#?}");
}
