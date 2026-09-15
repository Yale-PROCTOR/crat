//! **wave-5d2 — the class split for raw-discharged partners.**
//!
//! # The coupling this removes
//!
//! A signature class is one function. [`super::finalize_signature_classes`]
//! holds the whole class (`blocked-subject:<reason>`) whenever one of its
//! subjects is `Degraded` and carries a required arm: a subject that owes an
//! arm it cannot pay would leave the class's atomic Surface / D4 / C / PAIR /
//! GLUE / ADDR application incomplete. Every safe sibling in that function is
//! withdrawn with it — the batch-6 table's 119 `kind-raw` rows.
//!
//! The hold is right when the arm is one the partner would have to CHANGE FORM
//! to pay (Surface, D4, Glue, Addr). It is a construction artefact when the arm
//! is paid exactly by the partner staying raw:
//!
//! - **`Pair` on a raw parameter.** An A5 raw-view call at that argument
//!   presents the caller's argument as a hoisted raw value whose
//!   `expected_form` is `Raw` — the callee already takes a raw pointer there,
//!   so the view is the call's own presentation and the parameter's form does
//!   not move. The site itself stays owned by the callee's class and is
//!   applied, dropped, or held on its own receipts
//!   (`a5-fallback-unrenderable`, `seam-positive-retention`, …); only the
//!   partner's veto over its siblings is removed.
//! - **`C` on the raw SOURCE of a Raw→safe edge** is the same artefact from the
//!   other end and is retired by R401-4 (`co_conversion::required_arms`
//!   charges the adapter to the converted target only); it is not re-derived
//!   here — the C adapter is the callee class's seam edit, and the fixture
//!   below documents the dependency.
//!
//! # Soundness
//!
//! Nothing new is emitted: the A5 raw view was planned with the partner's raw
//! form as its target, under the T2 waiver receipt every A5 fallback carries.
//! The rule only stops a degraded subject that pays its arm in raw form from
//! withdrawing siblings whose own forms are settled. A partner owing any other
//! arm, or a view that expects a non-raw form at its argument, keeps the hold.

use super::super::{
    bridge_receipt::SignatureClassId,
    decision::{Arm, Decision, DecisionTable, RequiredArmSet, Subject, SubjectKind, seam::Form},
};

/// Whether every arm `required` of the degraded `subject` is paid by the
/// subject keeping its raw form, so the subject does not hold its class.
///
/// Empty requirements are not this rule's question (the caller already skips
/// them); the answer is `false` so the hook composes as a pure narrowing.
pub(crate) fn raw_form_discharges(
    table: &DecisionTable,
    subject: &Subject,
    required: RequiredArmSet,
) -> bool {
    if required.is_empty() {
        return false;
    }
    Arm::ALL
        .into_iter()
        .filter(|&arm| required.contains(arm))
        .all(|arm| match arm {
            Arm::Pair => pair_views_expect_raw(table, subject),
            Arm::Surface | Arm::D4 | Arm::C | Arm::Glue | Arm::Addr => false,
        })
}

/// The `Pair` arm on a parameter comes from the A5 raw-view calls into it
/// (`derive_arm_requirements`). It is paid in raw form exactly when at least
/// one such view exists and every one of them expects the raw form there.
fn pair_views_expect_raw(table: &DecisionTable, subject: &Subject) -> bool {
    let SubjectKind::Param { hir_index } = subject.kind else {
        return false;
    };
    let mut views = table
        .seams
        .a5_raw_calls
        .iter()
        .filter(|call| call.callee == subject.fn_did)
        .flat_map(|call| call.views.iter())
        .filter(|view| view.argument_index == hir_index)
        .peekable();
    views.peek().is_some() && views.all(|view| view.expected_form == Form::Raw)
}

/// **The second half of the split — the interface dependency an A5 raw view
/// induces.** The seam records `(callee, caller)` for every A5 raw-view call
/// so the callee's class waits for the caller's: a view rendered against the
/// caller's DECIDED argument form would be wrong if the caller's class were
/// then held and its bindings reverted to raw. That is exactly the guard the
/// zero-syntax producer applies itself (`found != Raw` on a bare / cast
/// local) — and it is what a raw view of a raw-stable argument does not need:
/// a place projection through a root that is degraded (raw in both worlds)
/// renders the same text whether or not the caller's class applies.
///
/// A pair is kept whenever anything else explains it: a zero-syntax
/// interface call on a converting local between the same two classes, or an
/// A5 view whose argument is a bare / cast local of a converting source.
pub(crate) fn keeps_interface_dependency(
    table: &DecisionTable,
    (dependent, dependency): (SignatureClassId, SignatureClassId),
) -> bool {
    let explained_by_zero_syntax = table.seams.zero_bridges.iter().any(|site| {
        site.owner_class == dependent
            && SignatureClassId::of(site.caller) == dependency
            && site.bridge_kind == "interface-call-zero-syntax"
            && matches!(site.argument_kind, "bare-local" | "cast-of-local")
            && site.found_form != Form::Raw.key()
    });
    if explained_by_zero_syntax {
        return true;
    }
    let mut views = table
        .seams
        .a5_raw_calls
        .iter()
        .filter(|call| {
            call.owner_class == dependent && SignatureClassId::of(call.caller) == dependency
        })
        .flat_map(|call| call.views.iter())
        .peekable();
    if views.peek().is_none() {
        // Not an A5-induced pair; whoever produced it keeps it.
        return true;
    }
    views.any(|view| {
        let converting_source = view.source_node.is_some_and(|(owner, hir_id)| {
            table.entries.iter().any(|(subject, decision)| {
                subject.fn_did == owner
                    && subject.hir_id == hir_id
                    && match decision {
                        Decision::Ref { .. }
                        | Decision::InferredRef { .. }
                        | Decision::Cursor { .. }
                        | Decision::NestedSlice { .. }
                        | Decision::Slice { .. }
                        | Decision::Opt { .. }
                        | Decision::Box(_) => true,
                        Decision::Degraded(_) => false,
                    }
            })
        });
        matches!(view.argument_shape, "bare-local" | "cast-of-local") && converting_source
    })
}

#[cfg(test)]
pub(crate) mod fixture {
    use std::sync::atomic::{AtomicUsize, Ordering};

    static NEXT: AtomicUsize = AtomicUsize::new(0);

    pub(crate) struct Receipts {
        pub(crate) subjects: String,
        pub(crate) arm_outcomes: String,
        pub(crate) class_collisions: String,
        pub(crate) emitted: String,
    }

    /// A one-file crate on disk, driven through the corpus's own path: precise
    /// A5 replay under the frozen-graph attestation, the census-once capture with
    /// the production verifier converging (`diagnose_raw_boundary_census`'s
    /// flags).
    /// Returns the E1 subject receipt (with its `exclusion` column), the arm
    /// outcomes and the emitted root text.
    pub(crate) fn run(src: &str) -> Receipts {
        let dir = std::env::temp_dir().join(format!(
            "crat-class-split-fixture-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&dir).expect("fixture dir");
        let root = dir.join("lib.rs");
        std::fs::write(&root, src).expect("fixture file");
        let outcome = crate::bo_rewriter::rewrite_core_injected(
            ::utils::compilation::path_to_input(&root),
            Some(&root),
            crate::bo_rewriter::MAX_REVERT_ROUNDS,
            &|_| {},
            false,
            true,
            true,
            Some((
                crate::bo_rewriter::A5Mode::PreciseReplay,
                Some(crate::bo_rewriter::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        );
        let capture = outcome.into_e1_capture().expect("fixture emits");
        // The census-once outcome hands back the unmodified input; the emitted
        // tree is the capture's file map (one file here).
        let emitted = capture
            .emitted_files
            .as_ref()
            .and_then(|files| files.values().next().cloned())
            .unwrap_or_else(|| {
                panic!(
                    "fixture delivers no tree: {}\nsubjects:\n{}\narms:\n{}\nbridge events: {:#?}\nreverts: {:#?}",
                    capture.escalation,
                    capture.subject_receipt,
                    capture.raw_boundary_artifacts.arm_outcomes,
                    capture.raw_boundary_artifacts.bridge_events,
                    capture.reverts
                )
            });
        Receipts {
            subjects: capture.subject_receipt,
            arm_outcomes: capture.raw_boundary_artifacts.arm_outcomes,
            class_collisions: capture.raw_boundary_artifacts.class_collisions,
            emitted,
        }
    }

    /// One column of the E1 subject receipt for one subject key.
    pub(crate) fn column<'a>(receipt: &'a str, subject_key: &str, column: &str) -> &'a str {
        let mut lines = receipt.lines();
        let header = lines
            .next()
            .expect("receipt header")
            .split('\t')
            .collect::<Vec<_>>();
        let index = header
            .iter()
            .position(|name| *name == column)
            .unwrap_or_else(|| panic!("no column {column} in {header:?}"));
        lines
            .map(|line| line.split('\t').collect::<Vec<_>>())
            .find(|fields| fields.first() == Some(&subject_key))
            .unwrap_or_else(|| panic!("no subject {subject_key} in\n{receipt}"))[index]
    }
}

#[cfg(test)]
mod tests {
    use super::fixture::{column, run};

    /// brotli `PrefixEncodeCopyDistance(…, code, extra_bits)` called from
    /// `InitCommand` with `&mut (*self_0).dist_prefix_, &mut
    /// (*self_0).dist_extra_`: `code` settles `&mut u16`; `extra_bits` is
    /// model-Raw (written through a narrower cast here, as the corpus's slot
    /// is), and the two field addresses through the raw `self_0` are blind to
    /// borrowck, so the A5 machinery presents `extra_bits`'s argument as a
    /// hoisted raw view. Batch 6: `code#4` = `blocked-subject:kind-raw`.
    const BROTLI_PAIR_SHAPE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_assignments, unused_mut)]
#[repr(C)]
pub struct Command { pub insert_len_: u32, pub dist_prefix_: u16, pub dist_extra_: u32 }
pub unsafe fn prefix_encode(distance_code: u64, code: *mut u16, extra_bits: *mut u32) {
    if distance_code < 16 {
        *code = distance_code as u16;
        *(extra_bits as *mut u8) = 0;
        return;
    }
    *code = (distance_code >> 1) as u16;
    *(extra_bits as *mut u8) = (distance_code & 1) as u8;
}
pub unsafe fn init_command(self_0: *mut Command, distance_code: u64) {
    (*self_0).insert_len_ = 1;
    prefix_encode(distance_code, &mut (*self_0).dist_prefix_, &mut (*self_0).dist_extra_);
}
"#;

    /// The pair-charged raw partner no longer vetoes its class: `code` places
    /// as `&mut u16`, `extra_bits` keeps `*mut u32`, and the call site carries
    /// the A5 raw view that was already planned for it.
    #[test]
    fn pair_charged_raw_partner_does_not_hold_its_class() {
        let got = run(BROTLI_PAIR_SHAPE);
        assert_eq!(
            column(&got.subjects, "prefix_encode::extra_bits#3", "reason"),
            "kind-raw",
            "the fixture's partner must be the corpus's model-Raw shape:\n{}",
            got.subjects
        );
        assert_eq!(
            column(
                &got.arm_outcomes,
                "prefix_encode::extra_bits#3",
                "required_arms"
            ),
            "pair",
            "the partner's only required arm is the A5 pair arm:\n{}",
            got.arm_outcomes
        );
        assert_eq!(
            column(&got.subjects, "prefix_encode::code#2", "exclusion"),
            "-",
            "the safe sibling is no longer withdrawn:\n{}",
            got.subjects
        );
        assert_eq!(
            column(&got.subjects, "prefix_encode::code#2", "placed"),
            "1"
        );
        let signature = got.emitted.split_whitespace().collect::<Vec<_>>().join(" ");
        assert!(
            signature.contains("code: &mut u16, extra_bits: *mut u32"),
            "the sibling places and the partner stays raw:\n{}",
            got.emitted
        );
        assert!(
            got.emitted.contains("__crat_a5_raw_"),
            "the call site carries the planned A5 raw view:\n{}",
            got.emitted
        );
    }

    /// The control on the same fixture: `init_command::self_0` is a degraded
    /// NODE (borrowed into a raw parameter) whose required arm is `d4` — a
    /// form-changing arm — so its class stays held exactly as before.
    #[test]
    fn form_changing_arm_on_a_degraded_partner_still_holds() {
        let got = run(BROTLI_PAIR_SHAPE);
        assert_eq!(
            column(&got.arm_outcomes, "init_command::self_0#1", "required_arms"),
            "d4"
        );
        assert_eq!(
            column(
                &got.arm_outcomes,
                "init_command::self_0#1",
                "blocking_reason"
            ),
            "blocked-subject:borrowed-into-raw-param"
        );
    }

    /// The dependency control: `caller::q` converts and is passed BARE into
    /// `callee::p` (zero syntax, `found = ref-mut`), while `caller`'s class is
    /// held by its degraded node `r` (stored into a `static mut`, `d4`). If
    /// `callee` applied alone, `callee(q)` would hand a raw `q` to `&mut i32`
    /// (`E0308`), so the `(callee, caller)` dependency is real and is kept:
    /// `p` reads `dependency-class-held`.
    const ZERO_SYNTAX_DEPENDENCY_SHAPE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_assignments, unused_mut)]
pub static mut KEPT: *mut i32 = 0 as *mut i32;
pub unsafe fn callee(p: *mut i32) { *p += 1; }
pub unsafe fn caller(q: *mut i32, r: *mut i32) {
    callee(q);
    *r = 2;
    KEPT = r;
}
"#;

    #[test]
    fn zero_syntax_dependency_on_a_held_caller_is_kept() {
        let got = run(ZERO_SYNTAX_DEPENDENCY_SHAPE);
        let exclusion = column(&got.subjects, "callee::p#1", "exclusion");
        assert!(
            exclusion.starts_with("terminal-not-applied:dependency-class-held:"),
            "{exclusion}\n{}",
            got.subjects
        );
        assert_eq!(column(&got.subjects, "callee::p#1", "placed"), "0");
        assert!(
            column(&got.subjects, "caller::q#1", "exclusion")
                .starts_with("terminal-not-applied:blocked-subject:"),
            "{}",
            got.subjects
        );
    }

    /// **Bucket (b).** brotli `BrotliFree(m, p)` called from
    /// `CleanupZopfliCostModel` as `BrotliFree(m, (*self_0).literal_costs_ as
    /// *mut c_void)`: `m` settles `&mut MemoryManager`; `p` is a void pointee
    /// (raw); the cast argument through the raw `self_0` is blind to borrowck,
    /// so the A5 machinery gives `p`'s position the raw-view role — and
    /// refused it because the argument is a `raw-expr`, holding the class
    /// (`dropped-site:a5-raw-view-template-unavailable`; batch 6
    /// `BrotliFree::m#1`). The caller's `m` is model-Raw and `self_0` a
    /// reference, as the corpus's `CleanupZopfliCostModel` has them. The
    /// view of a pure raw expression is the expression itself, hoisted.
    const BROTLI_FREE_SHAPE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_assignments, unused_mut)]
#[repr(C)]
pub struct MemoryManager {
    pub opaque: *mut core::ffi::c_void,
    pub free_func: Option<unsafe extern "C" fn(*mut core::ffi::c_void, *mut core::ffi::c_void)>,
}
#[repr(C)]
pub struct CostModel { pub literal_costs_: *mut f32 }
pub unsafe fn brotli_free(m: *mut MemoryManager, p: *mut core::ffi::c_void) {
    ((*m).free_func).expect("non-null function pointer")((*m).opaque, p);
}
pub unsafe fn cleanup(m: *mut MemoryManager, self_0: *mut CostModel) {
    *(m as *mut u8) = 0;
    brotli_free(m, (*self_0).literal_costs_ as *mut core::ffi::c_void);
    (*self_0).literal_costs_ = 0 as *mut f32;
}
"#;

    /// The A5 seam path now renders the view; the row's NEXT wall is the
    /// cross-class interval collision between the callee-owned raw-view call
    /// rewrite and the caller class's own edit inside the same call (the
    /// caller's `self_0` converts) — wave-5d's collision composition. Asserted
    /// as measured: the template hold is gone, the collision hold is what
    /// remains. (Rule inert → the exclusion is the template hold again; that
    /// is fault F5.)
    #[test]
    fn a_pure_raw_expression_argument_takes_the_a5_passthrough_view() {
        let got = run(BROTLI_FREE_SHAPE);
        let exclusion = column(&got.subjects, "brotli_free::m#1", "exclusion");
        assert!(
            !exclusion.contains("a5-raw-view-template-unavailable"),
            "the raw-expression view renders:\n{}",
            got.subjects
        );
        assert_eq!(
            exclusion, "terminal-not-applied:cross-class-interval-collision",
            "the next wall is the collision composition (wave-5d):\n{}",
            got.subjects
        );
    }

    /// **Bucket (b), the delivering shape — a CONTROL of the pair path.** lodepng `lodepng_info_copy(dest,
    /// source)` calls `lodepng_assign_icc(dest, (*source).iccp_name,
    /// (*source).iccp_profile, size)`: `dest` and `source` are model-Raw in
    /// the caller (`kind-raw`), `info` settles `&mut Info` in the callee, and
    /// the `(*source).…` field reads at the raw positions are raw
    /// expressions whose roots may alias `dest` — the A5 machinery makes
    /// `info` the primary and the field reads raw views, and refused them as
    /// `raw-expr`. Batch 6: `lodepng_assign_icc::info#1` = `dropped-site:
    /// a5-raw-view-template-unavailable`. With a raw caller there is no
    /// caller-class edit inside the call, so the hoisted views compose and
    /// `info` delivers. In the small crate `name` is a co-conversion NODE, so the
    /// view goes through the PAIR path (`pair_raw_view_expression`, which
    /// already passes a raw expression through) rather than the A5 seam path
    /// the corpus row took — measured: this test is GREEN with the admission
    /// inert. It is kept as the rendering control for the hoisted-field-read
    /// shape; the corpus row's own path is witnessed by the BrotliFree shape.
    /// (The corpus's third pointer, `profile`, is left out:
    /// it is degraded early there — `held:local-callee-access-extent` — while
    /// in a small crate it settles `&u8` and the LATE A5 reclassification to
    /// a raw view leaves its planned body adapter `core::ptr::from_ref(profile)`
    /// in place, `E0308`, function revert — a pre-existing defect of the late
    /// reclassification path, recorded in report 002, not this rule's.)
    const LODEPNG_ASSIGN_ICC_SHAPE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_assignments, unused_mut)]
#[repr(C)]
pub struct Info {
    pub iccp_defined: u32,
    pub iccp_name: *mut i8,
    pub iccp_profile: *mut u8,
    pub iccp_profile_size: u32,
}
extern "C" {
    fn lodepng_malloc(n: usize) -> *mut core::ffi::c_void;
    fn alloc_string(s: *const i8) -> *mut i8;
}
pub unsafe fn assign_icc(info: *mut Info, name: *const i8, size: u32) -> u32 {
    if size == 0 { return 100; }
    (*info).iccp_name = alloc_string(name);
    (*info).iccp_profile = lodepng_malloc(size as usize) as *mut u8;
    if (*info).iccp_name.is_null() || (*info).iccp_profile.is_null() { return 83; }
    (*info).iccp_profile_size = size;
    0
}
pub unsafe fn info_copy(dest: *mut Info, source: *mut Info) -> u32 {
    *(dest as *mut u8) = 0;
    *(source as *mut u8) = 0;
    if (*source).iccp_defined != 0 {
        let e = assign_icc(dest, (*source).iccp_name, (*source).iccp_profile_size);
        if e != 0 { return e; }
    }
    0
}
"#;

    #[test]
    fn a_hoisted_field_read_view_with_a_raw_caller_delivers_the_primary() {
        let got = run(LODEPNG_ASSIGN_ICC_SHAPE);
        assert_eq!(
            column(&got.subjects, "assign_icc::info#1", "exclusion"),
            "-",
            "{}",
            got.subjects
        );
        assert_eq!(column(&got.subjects, "assign_icc::info#1", "placed"), "1");
        let text = got.emitted.split_whitespace().collect::<Vec<_>>().join(" ");
        assert!(text.contains("info: &mut Info"), "{}", got.emitted);
        assert!(
            text.contains("= (*source).iccp_name;")
                && (text.contains("__crat_a5_raw_") || text.contains("__crat_pair_raw_")),
            "the raw field read is hoisted verbatim into the call snapshot:\n{}",
            got.emitted
        );
    }

    /// **Bucket (c), `body-unnameable-rhs`.** json.h
    /// `json_extract_get_array_size(array)`: `let mut element: *const Element
    /// = (*array).start;` then `element = (*element).next;` in the loop —
    /// `array` and `element` settle shared references, but every RHS is a raw
    /// field read (`raw-expr`), which the body seam refused as unnameable.
    /// Batch 6: `json_extract_get_array_size::{array#1, element#5}` ×2 owners.
    /// The body-adapter producer (Item E wave 2) is gated by a def-path
    /// allowlist of eight corpus functions (`emitability::WAVE2_BODY_FUNCTIONS`),
    /// so the fixture carries the corpus path `src::json::json_extract_get_array_size`.
    const JSON_ARRAY_SIZE_SHAPE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_assignments, unused_mut)]
pub mod src {
    pub mod json {
        #[repr(C)]
        pub struct Element { pub value: u64, pub next: *const Element }
        #[repr(C)]
        pub struct Array { pub start: *const Element, pub length: usize }
        pub unsafe fn json_extract_get_array_size(array: *const Array) -> u64 {
            let mut total: u64 = 0;
            let mut i: usize = 0;
            let mut element: *const Element = (*array).start;
            while i < (*array).length {
                total = total.wrapping_add((*element).value);
                element = (*element).next;
                i = i.wrapping_add(1);
            }
            total
        }
    }
}
"#;

    #[test]
    fn a_pure_raw_field_read_rhs_takes_the_reference_glue() {
        let got = run(JSON_ARRAY_SIZE_SHAPE);
        for key in [
            "src::json::json_extract_get_array_size::array#1",
            "src::json::json_extract_get_array_size::element#4",
        ] {
            assert_eq!(
                column(&got.subjects, key, "exclusion"),
                "-",
                "{key}\n{}",
                got.subjects
            );
            assert_eq!(column(&got.subjects, key, "placed"), "1", "{key}");
        }
        let text = got.emitted.split_whitespace().collect::<Vec<_>>().join(" ");
        assert!(text.contains("array: &Array"), "{}", got.emitted);
        assert!(
            text.contains("element: &Element = &*(*array).start;")
                && text.contains("element = &*(*element).next;"),
            "the initializer and the assignment are the raw field reads under the reference glue:\n{}",
            got.emitted
        );
    }

    /// binn `binn_is_valid_ex(ptr, ptype, …)`: `plimit = p.offset(size)` is
    /// passed raw into `AdvanceDataPos(p, plimit)` whose `plimit` is
    /// hypothetically `ref`, so the edge routes `arm-c` and the raw SOURCE is
    /// charged `C`; the caller's class holds (`blocked-subject:<partner>` +
    /// `missing-required-arm:c`) and `ptype` (`Option<&mut i32>`) is withdrawn.
    /// Batch 6: `ptype#2` = `blocked-subject:kind-raw`. (The small crate's
    /// fresh solve calls `plimit` `copy-source-coupled` instead of `kind-raw`;
    /// the class mechanism is identical. `buf` is a void pointer as binn's
    /// `ptr` is, so it stays raw — `held:void-pointee` — and the body's copy
    /// `p = buf as *mut u8` needs no adapter once the class is released.)
    const BINN_C_SOURCE_SHAPE: &str = r#"
#![allow(dead_code, unused_unsafe, unused_assignments, unused_mut)]
pub unsafe fn advance(mut p: *mut u8, plimit: *mut u8) -> *mut u8 {
    if p > plimit { return 0 as *mut u8; }
    p = p.offset(1);
    p
}
pub unsafe fn is_valid(buf: *mut core::ffi::c_void, size: i32, ptype: *mut i32) -> i32 {
    let mut p = buf as *mut u8;
    let plimit = p.offset(size as isize);
    if !ptype.is_null() && *ptype != 0 { return 0; }
    p = advance(p, plimit);
    if p.is_null() { return 0; }
    if !ptype.is_null() { *ptype = 3; }
    1
}
"#;

    /// The C-charged coupling is NOT this module's: it is released by R401-4
    /// (wave-6s `bc46254e`, "charge the C adapter arm to the converted target
    /// only"), measured GREEN on this fixture with that change applied and RED
    /// without it. Ignored until that hook is on the head; un-ignore then.
    #[test]
    #[ignore = "RED by design: released by wave-6s bc46254e (R401-4), not by the class split"]
    fn c_charged_raw_source_partner_is_released_by_the_target_only_charge() {
        let got = run(BINN_C_SOURCE_SHAPE);
        assert_eq!(column(&got.subjects, "is_valid::ptype#3", "exclusion"), "-");
        assert_eq!(column(&got.subjects, "is_valid::ptype#3", "placed"), "1");
        assert!(
            got.emitted.contains("ptype: Option<&mut i32>"),
            "{}",
            got.emitted
        );
    }

    /// What the C-charged shape looks like at this head, so the dependency is
    /// measured rather than asserted: the partner owes `c` as a raw source and
    /// the class reports `missing-required-arm:c`.
    #[test]
    fn c_charged_raw_source_partner_holds_its_class_at_this_head() {
        let got = run(BINN_C_SOURCE_SHAPE);
        let exclusion = column(&got.subjects, "is_valid::ptype#3", "exclusion");
        assert!(
            exclusion.starts_with("terminal-not-applied:blocked-subject:")
                && exclusion.contains("missing-required-arm:c"),
            "{exclusion}\n{}",
            got.subjects
        );
        assert_eq!(
            column(&got.arm_outcomes, "is_valid::plimit#6", "required_arms"),
            "c"
        );
    }
}
