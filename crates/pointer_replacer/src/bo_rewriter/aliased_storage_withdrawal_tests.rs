//! **R575-6 — the aliased-storage withdrawal, witnessed on brotli's own frame.**
//!
//! brotli's `EncodeData` is held by its two callers' `EncodeData(s, …, &mut
//! (*s).available_out_, …)`: the converted `out_size` is a place inside `*s` while
//! `s` itself is a raw position, and `EncodeData` is no leaf, so
//! `counted_void::aliased_storage_twin` cannot take the pristine twin and refuses
//! the call. `out_size` is the class's only safe subject. Three hand reductions of
//! the shape decide `out_size` raw in the model (wave-5d 083), so the witness reads
//! brotli's own substrate under the landed frame's accepted model, through the
//! census's one-iteration instrument (one decision, one emission, one
//! baseline-subtracted verify), with no solve.
//!
//! Run by hand, never by the suite: `CRAT_R575_BROTLI=<…/rs-crown-derived/brotli/lib.rs>`
//! with the landed frame's env (`2026-09-23-lane-brotli-probe/landed-frame-env.sh`);
//! `CRAT_R575_OUT` names a file for the rows the report quotes.

use std::collections::{BTreeMap, BTreeSet};

const ENCODE_DATA: &str = "src::enc::encode::EncodeData";
/// `EncodeData`'s signature class on this substrate (its `LocalDefIndex`, as the
/// census tables name it: `dependency-class-held:2437`).
const ENCODE_DATA_CLASS: u32 = 2437;
const OUT_SIZE: &str = "src::enc::encode::EncodeData::out_size#4";
/// Refused callees whose class has more than one safe subject: they keep the
/// subject and the hold.
const CONTROLS: [&str; 3] = [
    "src::enc::histogram::BrotliBuildHistogramsWithContext::literal_split#3",
    "src::dec::decode::SafeReadBlockLength::s#1",
    "src::dec::decode::SafeReadBlockLength::br#4",
];
/// Delivered on the settled table, where A5's raw-view role at `header` makes
/// `WriteMetadataHeader(s, n, (*s).next_out_)` a PAIR-owned call that never
/// reaches the twin's gate: a withdrawal read before the roles converge would
/// take it (the second control).
const PAIR_OWNED: &str = "src::enc::encode::WriteMetadataHeader::s#1";
/// Read, not judged: the class the forced cover makes depend on `EncodeData`.
const STITCH: &str = "src::enc::encode::InitOrStitchToPreviousBlock";

struct Row {
    owner: String,
    model: String,
    decision: String,
    reason: String,
    detail: String,
    exclusion: String,
}

/// The census subject receipt: `key owner local arg depth family model decision
/// reason detail site placed exclusion sole_blocker`.
fn rows(receipt: &str) -> BTreeMap<String, Row> {
    receipt
        .lines()
        .skip(1)
        .filter_map(|line| {
            let f = line.split('\t').collect::<Vec<_>>();
            (f.len() == 14).then(|| {
                (
                    f[0].to_owned(),
                    Row {
                        owner: f[1].to_owned(),
                        model: f[6].to_owned(),
                        decision: f[7].to_owned(),
                        reason: f[8].to_owned(),
                        detail: f[9].to_owned(),
                        exclusion: f[12].to_owned(),
                    },
                )
            })
        })
        .collect()
}

fn line(key: &str, row: &Row) -> String {
    format!(
        "{key}\tmodel={}\tdecision={}\treason={}\tdetail={}\texclusion={}",
        row.model, row.decision, row.reason, row.detail, row.exclusion
    )
}

fn frame() -> super::E1Capture {
    let root = std::path::PathBuf::from(
        std::env::var("CRAT_R575_BROTLI").expect("CRAT_R575_BROTLI: brotli's substrate lib.rs"),
    );
    assert_eq!(
        std::env::var("CRAT_ERA5_EXECUTION_ROLE").as_deref(),
        Ok("cache-only"),
        "the frame is read from its accepted cache, never solved"
    );
    // The census's configured exposure row for brotli (explicit-empty).
    let config = super::EmissionRunConfig {
        configured_exposure: super::decision::exposure::ConfiguredExposureInput::checked(
            "standing-raw-boundary-launch:Config::default.c_exposed_fns",
            Vec::new(),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        )
        .expect("brotli's configured exposure row"),
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

#[test]
#[ignore = "R575-6: brotli's frame; run by hand with CRAT_R575_BROTLI and the landed frame's env"]
fn r575_6_brotli_out_size_is_withdrawn_and_encode_data_is_ready() {
    let capture = frame();
    let rows = rows(&capture.subject_receipt);
    // The class is ready when nothing is held on it: no subject of the frame
    // waits on `dependency-class-held:<EncodeData>`.
    let held_on_encode_data = rows
        .iter()
        .filter(|(_, row)| {
            row.exclusion
                .split([':', ';', ','])
                .collect::<Vec<_>>()
                .windows(2)
                .any(|w| w[0] == "dependency-class-held" && w[1] == ENCODE_DATA_CLASS.to_string())
        })
        .map(|(key, row)| line(key, row))
        .collect::<Vec<_>>();
    let encode_data_bridges = capture
        .raw_boundary_artifacts
        .bridge_events
        .iter()
        .filter(|e| e.site.owner_class.order_key() == ENCODE_DATA_CLASS)
        .map(|e| {
            format!(
                "{}\t{}\t{}\t{}..{}\t{:?}\t{}",
                e.site.arm,
                e.site.bridge_kind,
                e.site.position,
                e.site.lo,
                e.site.hi,
                e.state,
                e.drop_reason.as_deref().unwrap_or("-")
            )
        })
        .collect::<Vec<_>>();
    let refused_into = |callee: &str| {
        capture
            .adapter_receipt
            .lines()
            .filter(|l| {
                let f = l.split('\t').collect::<Vec<_>>();
                f.contains(&"blocked") && f.contains(&callee) && f.contains(&"seam-site-overlap")
            })
            .map(str::to_owned)
            .collect::<Vec<_>>()
    };
    let withdrawn = rows
        .iter()
        .filter(|(_, row)| row.reason == "aliased-storage-withdrawn")
        .collect::<Vec<_>>();
    // The withdrawal's footprint: each withdrawn subject's function and the
    // callers of its refused calls (`caller@site;…`).
    let footprint = withdrawn
        .iter()
        .flat_map(|(_, row)| {
            std::iter::once(row.owner.clone()).chain(
                row.detail
                    .split(';')
                    .filter_map(|seam| seam.split_once('@').map(|(caller, _)| caller.to_owned())),
            )
        })
        .collect::<BTreeSet<_>>();
    let reverts = capture
        .reverts
        .iter()
        .map(|r| {
            format!(
                "{}\t{}\t{}",
                r.function, r.attribution, r.diagnostic.message
            )
        })
        .collect::<Vec<_>>();

    let mut record = vec![format!("== {OUT_SIZE}")];
    record.extend(rows.get(OUT_SIZE).map(|row| line(OUT_SIZE, row)));
    record.push(format!(
        "== subjects held on {ENCODE_DATA}'s class {ENCODE_DATA_CLASS}"
    ));
    record.extend(held_on_encode_data.iter().cloned());
    record.push(format!("== {ENCODE_DATA}'s bridge events"));
    record.extend(encode_data_bridges.iter().cloned());
    record.push(format!(
        "== blocked seam-site-overlap rows into {ENCODE_DATA}"
    ));
    record.extend(refused_into(ENCODE_DATA));
    record.push("== withdrawn (aliased-storage-withdrawn)".to_owned());
    record.extend(withdrawn.iter().map(|(key, row)| line(key, row)));
    record.push("== controls".to_owned());
    record.extend(
        CONTROLS
            .iter()
            .chain([&PAIR_OWNED])
            .filter_map(|key| rows.get(*key).map(|row| line(key, row))),
    );
    record.push(format!("== {STITCH} (read)"));
    record.extend(
        rows.iter()
            .filter(|(_, row)| row.owner == STITCH)
            .map(|(key, row)| line(key, row)),
    );
    record.push(format!(
        "== first verify: novel_errors={} reverts={}",
        capture.novel_error_count,
        reverts.len()
    ));
    record.extend(reverts.iter().cloned());
    if let Ok(out) = std::env::var("CRAT_R575_OUT") {
        std::fs::write(out, record.join("\n") + "\n").expect("write the witness record");
    }

    let mut failures = Vec::new();
    // Witness.
    match rows.get(OUT_SIZE) {
        None => failures.push(format!("witness: no row for {OUT_SIZE}")),
        Some(row) => {
            if row.model != "ref" {
                failures.push(format!(
                    "witness: the frame's model is not ref: {}",
                    line(OUT_SIZE, row)
                ));
            }
            if (row.decision.as_str(), row.reason.as_str())
                != ("degraded", "aliased-storage-withdrawn")
                || !row.detail.contains("::ProcessMetadata@")
                || !row.detail.contains("::BrotliEncoderCompressStream@")
            {
                failures.push(format!(
                    "witness: not withdrawn with its receipt: {}",
                    line(OUT_SIZE, row)
                ));
            }
        }
    }
    if !held_on_encode_data.is_empty() {
        failures.push(format!(
            "witness: {ENCODE_DATA}'s class is held: {held_on_encode_data:?}"
        ));
    }
    let refused = refused_into(ENCODE_DATA);
    if !refused.is_empty() {
        failures.push(format!(
            "witness: blocked calls into {ENCODE_DATA}: {refused:?}"
        ));
    }
    let reverted = capture
        .reverts
        .iter()
        .filter(|r| footprint.contains(&r.function))
        .map(|r| format!("{}: {}", r.function, r.diagnostic.message))
        .collect::<Vec<_>>();
    if !reverted.is_empty() {
        failures.push(format!(
            "witness: the first verify reverts the footprint: {reverted:?}"
        ));
    }
    // Control: another safe subject in the class keeps the subject and its hold.
    for key in CONTROLS {
        match rows.get(key) {
            Some(row) if row.decision == "ref" && row.exclusion.contains("seam-site-overlap") => {}
            Some(row) => failures.push(format!("control: {}", line(key, row))),
            None => failures.push(format!("control: no row for {key}")),
        }
    }
    // Control: a subject whose call the settled PAIR row owns stays delivered.
    match rows.get(PAIR_OWNED) {
        Some(row) if row.decision == "ref" && row.exclusion == "-" => {}
        Some(row) => failures.push(format!("control: {}", line(PAIR_OWNED, row))),
        None => failures.push(format!("control: no row for {PAIR_OWNED}")),
    }
    assert!(failures.is_empty(), "{failures:#?}");
}
