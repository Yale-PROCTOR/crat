//! **R481-2 / R486-1 (USER ruling, 2026-09-21): the tier-2 retention waiver.**
//!
//! After every proof has been tried, a bridging site whose ONLY remaining hold
//! is the callee's retention emits the bridge it would have had under tier 1,
//! with a per-site receipt. A site that a proof discharges carries its PROOF
//! receipt and never the waiver; a site with any other hold stays held; and a
//! site where the callee's own parameter is rewritten safe has no bridge to
//! license, so it holds exactly as it did before the waiver.
use super::verify;

/// **The delivering shape — binn's `GetValue` reduced.** A caller hands its own
/// buffer parameter to a local callee that stores it through an out-parameter
/// (`(*value).ptr = p`): retention is known positive, no proof discharges it,
/// nothing else holds the site, and the callee's parameter stays raw. This is
/// the class of binn's nine `target_stays_raw = 1` retention-blocked rows.
const RETAINED: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
#[repr(C)]
pub struct Blob { pub ptr: *mut u8, pub len: i32 }
unsafe fn GetValue(mut p: *mut u8, mut value: *mut Blob) -> i32 {
    if value.is_null() { return 0; }
    (*value).ptr = p;
    (*value).len = *p.offset(0 as isize) as i32;
    return 1;
}
pub unsafe fn caller(mut buf: *mut u8, mut value: *mut Blob) -> i32 {
    if buf.is_null() { return 0; }
    *buf.offset(0 as isize) = 1 as u8;
    return GetValue(buf, value);
}
"#;

/// `(callee, argument_index, target_stays_raw, tier, waiver_id, evidence,
/// reason, atom_group)` of every disposition row for `function`.
pub(super) struct Row {
    callee: String,
    argument_index: String,
    target_stays_raw: String,
    tier: String,
    waiver_id: String,
    evidence: String,
    reason: String,
    atom_group: String,
}

impl std::fmt::Debug for Row {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}#{} stays_raw={} {} {} [{}] {} atom={}",
            self.callee,
            self.argument_index,
            self.target_stays_raw,
            self.tier,
            self.waiver_id,
            self.evidence,
            self.reason,
            self.atom_group
        )
    }
}

pub(super) fn dispositions(input: &str, function: &str) -> Vec<Row> {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (_, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("decision table");
        let tsv = &ctx.raw_boundary_artifacts.dispositions;
        let header = tsv.lines().next().expect("header");
        let ix = |name: &str| {
            header
                .split('\t')
                .position(|c| c == name)
                .unwrap_or_else(|| panic!("column {name} in {header}"))
        };
        let (caller, callee, argument_index, target_stays_raw) = (
            ix("caller"),
            ix("callee"),
            ix("argument_index"),
            ix("target_stays_raw"),
        );
        let (tier, waiver_id, evidence, reason, atom_group) = (
            ix("tier"),
            ix("waiver_id"),
            ix("evidence"),
            ix("reason"),
            ix("atom_group"),
        );
        tsv.lines()
            .skip(1)
            .map(|line| line.split('\t').collect::<Vec<_>>())
            .filter(|row| row[caller].ends_with(function))
            .map(|row| Row {
                callee: row[callee].to_owned(),
                argument_index: row[argument_index].to_owned(),
                target_stays_raw: row[target_stays_raw].to_owned(),
                tier: row[tier].to_owned(),
                waiver_id: row[waiver_id].to_owned(),
                evidence: row[evidence].to_owned(),
                reason: row[reason].to_owned(),
                atom_group: row[atom_group].to_owned(),
            })
            .collect()
    })
    .expect("fixture compiler context")
}

fn waived(rows: &[Row]) -> Option<&Row> {
    rows.iter()
        .find(|row| row.waiver_id.contains("retention-waiver:tier-2"))
}

/// The tier-2 receipt at `function`'s waived site, for the controls in other
/// modules that the waiver re-premises (R481-2, R495-2).
pub(super) fn waived_receipt(input: &str, function: &str) -> Option<String> {
    let rows = dispositions(input, function);
    waived(&rows).map(|row| row.evidence.clone())
}

/// **W6O-T2-1 — the delivering witness.** The retaining site is bridged under
/// the retention waiver, with the per-site receipt naming the subject and the
/// callee, the site carries an atom, and the emitted program type-checks.
#[test]
fn wave6o_a_known_retaining_site_is_bridged_under_the_waiver() {
    assert!(verify::type_checks_str(RETAINED));
    let rows = dispositions(RETAINED, "caller");
    let waived = waived(&rows).unwrap_or_else(|| panic!("no waived row: {rows:?}"));
    assert_eq!(waived.tier, "T2", "the waiver is a tier-2 bridge: {rows:?}");
    assert_eq!(waived.reason, "retention-positive-waived", "{rows:?}");
    assert!(
        waived
            .evidence
            .contains("retention-waiver(tier-2, kind=known, subject=caller::buf, callee=")
            && waived.evidence.contains("GetValue"),
        "the receipt names the subject and the callee: {}",
        waived.evidence
    );
    assert_eq!(waived.target_stays_raw, "1", "{rows:?}");
    assert!(
        waived.atom_group.starts_with("raw-boundary-site:"),
        "the waived site carries the atom that renders the bridge: {rows:?}"
    );
    let output = super::emit_tests::ast_emitted_source_of(RETAINED).expect("native emission");
    assert!(verify::type_checks_str(&output), "{output}");
    assert!(
        output.contains("GetValue("),
        "the call survives the bridge: {output}"
    );
}

/// **Control 1 — a site a PROOF discharges carries the proof receipt, never
/// the waiver.** json.h's shape: the container is a frame-bounded stack local
/// whose callees are certified, so R476-1 answers `no-retain` before this arm
/// is reached.
#[test]
fn wave6o_a_proof_discharged_site_does_not_spend_the_waiver() {
    const PROVED: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
#[repr(C)]
pub struct State { pub src: *const u8, pub size: usize, pub offset: usize }
unsafe fn read_one(mut st: *mut State) -> i32 {
    let mut b = *((*st).src).offset((*st).offset as isize);
    (*st).offset = ((*st).offset).wrapping_add(1);
    return b as i32;
}
pub unsafe fn parse(mut src: *const u8, mut size: usize) -> i32 {
    let mut state = State { src: 0 as *const u8, size: 0, offset: 0 };
    if src.is_null() { return 0; }
    state.src = src;
    state.size = size;
    return read_one(&mut state);
}
"#;
    let rows = dispositions(PROVED, "parse");
    assert!(
        waived(&rows).is_none(),
        "a proved site spends no waiver: {rows:?}"
    );
}

/// **Control 2 — a site with a SECOND hold stays held.** The waiver lifts
/// retention and nothing else: here the callee takes a mutable raw pointer
/// from a subject whose only evidence is shared, so the shared-to-mut refusal
/// stands whatever retention says.
#[test]
fn wave6o_a_second_hold_survives_the_waiver() {
    const SHARED_TO_MUT: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
static mut KEPT: *mut u8 = 0 as *mut u8;
unsafe fn keep_mut(mut p: *mut u8) { KEPT = p; }
pub unsafe fn reader(mut buf: *const u8, mut n: usize) -> i32 {
    if buf.is_null() { return 0; }
    let mut total = *buf.offset(0 as isize) as i32 + *buf.offset(1 as isize) as i32;
    keep_mut(buf as *mut u8);
    return total;
}
"#;
    let rows = dispositions(SHARED_TO_MUT, "reader");
    assert!(
        waived(&rows).is_none(),
        "a shared-to-mut site is not waived into a bridge: {rows:?}"
    );
}

/// **Control 3 — where the callee's own parameter is rewritten safe there is
/// no bridge to license, so the site holds.** Same retaining store as the
/// delivering witness, but the callee reads its buffer parameter as a shared
/// reference, so `target_stays_raw = 0`: waiving here would leave the safe
/// argument facing a safe parameter with no atom to render, and the emitted
/// program would not type-check. It stays `positive-retention` blocked.
#[test]
fn wave6o_a_site_whose_callee_parameter_goes_safe_is_not_waived() {
    const CALLEE_GOES_SAFE: &str = r#"
#![allow(dead_code, unused_mut, unused_variables, non_snake_case)]
#[repr(C)]
pub struct Reg { pub ptr: *mut u8, pub n: i32 }
unsafe fn attach(mut p: *mut u8, mut r: *mut Reg) {
    (*r).ptr = p;
    (*r).n = ((*r).n) + 1;
}
pub unsafe fn caller(mut buf: *mut u8, mut r: *mut Reg) -> i32 {
    if buf.is_null() { return 0; }
    *buf.offset(0 as isize) = 1 as u8;
    attach(buf, r);
    return *buf.offset(1 as isize) as i32;
}
"#;
    let rows = dispositions(CALLEE_GOES_SAFE, "caller");
    let held = rows
        .iter()
        .find(|row| row.callee.ends_with("attach") && row.argument_index == "0")
        .unwrap_or_else(|| panic!("the attach site: {rows:?}"));
    assert_eq!(held.target_stays_raw, "0", "{rows:?}");
    assert_eq!(held.tier, "blocked", "{rows:?}");
    assert_eq!(held.reason, "raw-boundary-positive-retention", "{rows:?}");
    // The site is not bridged and not broken: the argument is adapted by the
    // arm that owns it, so the emitted call carries NO `E0308` mismatch. (This
    // shape has a PRE-EXISTING `E0499` from two `as_mut()` borrows of the same
    // subject, which the waiver neither causes nor repairs; asserting the whole
    // program type-checks would assert something this shape has never done.)
    let output =
        super::emit_tests::ast_emitted_source_of(CALLEE_GOES_SAFE).expect("native emission");
    let mismatches = verify::diagnose_str(&output)
        .diags
        .into_iter()
        .filter(|diag| diag.code.as_deref() == Some("E0308"))
        .collect::<Vec<_>>();
    assert!(
        mismatches.is_empty(),
        "an unwaived site leaves no unadapted argument: {mismatches:?}\n{output}"
    );
}

/// **W6O-T2-6 (R523-1) — the BRIDGE receipts of a waived site reconcile.**
///
/// One comparator over from the transport: `BridgeReceiptEvent::validate`
/// knew only the v1 bridge waiver, so at batch 28 binn, lil, bzip2 and brotli
/// read `reconciliation-drift:bridge /
/// T2_bridge_receipt_lacks_the_exact_waiver_ID` and the census was
/// `data=false` — nothing could land while the arm was in.
#[test]
fn wave6o_a_waived_sites_bridge_receipts_reconcile() {
    let outcome = ::utils::compilation::run_compiler_on_input(
        ::utils::compilation::str_to_input(RETAINED),
        |tcx| {
            let (table, ctx) = super::decide_table_with_ctx(tcx)?;
            let emission = super::emit_files(
                tcx,
                &table,
                &rustc_hash::FxHashSet::default(),
                &ctx.retained_c9_plans,
            )?;
            let events = emission
                .plan
                .bridge_events(&std::collections::BTreeSet::new());
            let waived = events
                .iter()
                .filter(|event| {
                    event.waiver_id.as_deref()
                        == Some(super::decision::raw_boundary::RAW_BOUNDARY_RETENTION_WAIVER_ID)
                })
                .count();
            Ok::<_, String>((
                waived,
                super::bridge_receipt::reconcile_bridge_events(&events).map(|_| ()),
            ))
        },
    )
    .expect("fixture compiler context")
    .expect("emission");
    assert!(
        outcome.0 > 0,
        "the fixture carries a tier-2 waived bridge receipt"
    );
    assert_eq!(outcome.1, Ok(()), "and the bridge events reconcile");
}
