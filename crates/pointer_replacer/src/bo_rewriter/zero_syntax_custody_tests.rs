//! Logical receipt custody for real zero-syntax seams.
//! Independent control sites are constructed receipt inputs, not model facts.
//!
//! **R285-3 / R217-2 — why the source moved from `strchr` to `utime`.**
//!
//! These fixtures reached their zero-syntax carrier through a RETURNED-PARENT
//! source: `strchr(p, 65)` with `p: &i8`. Route (A)'s `held:thin-extent` now
//! holds exactly that shape, and correctly — `strchr` reads to the NUL while
//! `&i8` grants one byte — so `target::p` degrades before any seam is planned.
//!
//! The shape is not recoverable by editing the fixture. Every returned-parent
//! row in the pinned contract table carries a many-element extent
//! (`NulTerminated`, `ByteCount`, `UnboundedWrite`); there is no
//! returned-parent position that fits one element, and a fat source cannot
//! produce a zero-syntax carrier because a slice needs `.as_ptr()`. Returned
//! parent and zero syntax are now mutually exclusive.
//!
//! So the route changed and the property did not. The source is a one-element
//! position (`utime` argument 1, `Read`/`OneElement`), whose `&Times` still
//! coerces with no syntax, and every custody assertion below — the
//! `ZeroSyntaxReady` state, the logical atom dependency without a text edit,
//! the atom-fate split against an independent same-class site, and the
//! explicit-to-zero replacement — is unchanged and still driven by a real
//! model fact. What is lost is coverage of the returned-parent ROUTE to a
//! zero-syntax carrier, which route (A) removed on purpose;
//! `thin_extent_holds_the_returned_parent_zero_syntax_source` below keeps that
//! removal witnessed rather than silent.

use std::collections::{BTreeMap, BTreeSet};

use super::{
    bridge_receipt::{BridgeReceiptStage, BridgeReceiptState, BridgeSiteKey, SignatureClassId},
    decision::{Arm, Decision, RequiredArmSet, seam::SeamEdit},
    plan::{ClassInput, ClassSite, ClassSiteState, Edit, FileKey, Justification, Plan},
};

fn fixture(readonly: bool) -> (Plan, SeamEdit, FileKey, usize, usize) {
    let body = if readonly {
        "let code = utime(b\"f\\0\" as *const u8 as *const i8, p);\n\
         if code == 0 { (*p).actime } else { (*p).modtime }"
    } else {
        "utime(b\"f\\0\" as *const u8 as *const i8, p); (*p).actime"
    };
    let source = format!(
        "#![allow(dead_code, unused_variables, unused_unsafe)]\n\
         #[repr(C)] pub struct Times {{ pub actime: i64, pub modtime: i64 }}\n\
         extern \"C\" {{ fn utime(path: *const i8, times: *const Times) -> i32; }}\n\
         unsafe fn target(p: *const Times) -> i64 {{ {body} }}\n\
         pub unsafe fn entry() -> i64 {{\n\
             let storage = Times {{ actime: 65, modtime: 0 }};\n\
             target(&storage)\n\
         }}\n"
    );
    let (plan, seam, file, lo, hi, baseline, reverted_source) = ::utils::compilation::run_compiler_on_str(&source, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("original fixture AST");
        let (table, ctx) = super::decide_table_with_ctx_config(tcx, Some((
            crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
            Some(crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph),
        ))).expect("actual fixture decisions");
        let solve = super::model_cache::solve_receipt();
        println!("zero-syntax custody readonly={readonly} solve receipt: {solve:#?}");
        assert!(solve.is_some(), "R232 fixture solve receipt is required");
        let (subject, decision) = table.entries.iter().find(|(subject, _)| subject.label == "target::p").unwrap();
        let slot = ctx.slots.fn_local_slots[&subject.fn_did].slot_for_local_depth(subject.local, 0).unwrap();
        assert_eq!(ctx.model.get(&super::SlotRef::Local(subject.fn_did, slot)), Some(&super::SlotKind::Ref));
        let shared = match decision {
            Decision::Ref { mutable } | Decision::InferredRef { mutable, .. }
            | Decision::Slice { mutable, .. } | Decision::Opt { mutable, .. } => !*mutable,
            Decision::Box(_) | Decision::Degraded(_) => false,
        };
        assert!(shared, "actual shared source required: {decision:?}");
        let emission = super::emit_files(tcx, &table, &rustc_hash::FxHashSet::default(), &ctx.retained_c9_plans).unwrap();
        let owner = SignatureClassId::of(subject.fn_did);
        assert!(emission.plan.class_finalization.classes[&owner].is_ready());
        let seams = emission.plan.terminal_call_plans.seam_edits.iter().filter(|seam| {
            seam.source_node == Some((subject.fn_did, subject.hir_id))
                && seam.zero_syntax
        }).collect::<Vec<_>>();
        let [seam] = seams.as_slice() else { panic!("one real zero-syntax seam required: {seams:?}") };
        let seam = (**seam).clone();
        assert!(seam.zero_syntax, "fixture must exercise the actual zero-syntax carrier");
        assert!(!seam.atom_ids.is_empty(), "actual source atom dependency required");
        let source_file = tcx.sess.source_map().lookup_source_file(seam.span.lo());
        let file = super::file_key(&source_file.name).unwrap();
        let lo = (seam.span.lo().0 - source_file.start_pos.0) as usize;
        let hi = (seam.span.hi().0 - source_file.start_pos.0) as usize;
        let held = emission.plan.held_classes();
        let render = |atoms: BTreeSet<String>| {
            let reverts = super::ast_transform::revert_set_from_classes_and_atoms(&held, &atoms, &table).unwrap();
            let (files, _, _, _) = super::ast_transform::ast_emitted_files_from(tcx, &capture, &reverts,
                emission.plan.root_file.as_ref(), &table, Some(&emission.plan.terminal_call_plans)).unwrap();
            assert_eq!(files.len(), 1);
            files.into_values().next().unwrap()
        };
        let baseline = render(BTreeSet::new());
        let reverted_source = render(BTreeSet::from([seam.atom_ids[0].clone()]));
        (emission.plan, seam, file, lo, hi, baseline, reverted_source)
    }).expect("accepted returned-parent input compiles");
    assert!(super::verify::type_checks_str(&baseline), "{baseline}");
    assert!(
        super::verify::type_checks_str(&reverted_source),
        "{reverted_source}"
    );
    (plan, seam, file, lo, hi)
}

fn exact_key(seam: &SeamEdit, file: &FileKey, lo: usize, hi: usize) -> BridgeSiteKey {
    seam.bridge.materialize(
        seam.owner_class,
        super::bridge_custody_export::file_label(file),
        lo as u32,
        hi as u32,
    )
}

fn add_independent_site(plan: &mut Plan, owner: SignatureClassId) -> BridgeSiteKey {
    let site = ClassSite::zero(owner, owner, Arm::C, "constructed-independent-zero-control");
    assert!(site.atom_ids.is_empty());
    let key = site.key.clone();
    let class = plan.class_finalization.classes.get_mut(&owner).unwrap();
    assert!(class.is_ready());
    class.site_keys.push(key.clone());
    class.sites.push(site);
    key
}

fn require_atom_fate(
    plan: &Plan,
    selected: &BridgeSiteKey,
    independent: &BridgeSiteKey,
    atom: &str,
) {
    let held = plan.held_classes();
    let events = plan.bridge_events_with_atoms(&held, &BTreeSet::from([atom.to_owned()]));
    let terminal = |key: &BridgeSiteKey| {
        let found = events
            .iter()
            .filter(|event| &event.site == key && event.stage == BridgeReceiptStage::Terminal)
            .collect::<Vec<_>>();
        assert_eq!(found.len(), 1, "exact terminal identity: {key:?}");
        found[0]
    };
    assert_eq!(
        terminal(independent).state,
        BridgeReceiptState::Applied,
        "independent same-class receipt survives"
    );
    assert_eq!(
        terminal(selected).state,
        BridgeReceiptState::Dropped,
        "zero-syntax receipt outlived its actual source atom: {:?}",
        terminal(selected)
    );
    assert_eq!(
        terminal(selected).drop_reason.as_deref(),
        Some("atom-reverted-after-verify")
    );
}

fn check_real_zero(readonly: bool) {
    let (mut plan, seam, file, lo, hi) = fixture(readonly);
    let key = exact_key(&seam, &file, lo, hi);
    let sites = plan.class_finalization.classes[&seam.owner_class]
        .sites
        .iter()
        .filter(|site| site.key == key)
        .collect::<Vec<_>>();
    let [site] = sites.as_slice() else { panic!("one actual class site required") };
    assert_eq!(site.state, ClassSiteState::ZeroSyntaxReady);
    assert_eq!(site.edit_key, "-");
    assert_eq!(
        site.atom_ids, seam.atom_ids,
        "producer carries logical dependencies without a text edit"
    );
    let before = plan.bridge_events(&plan.held_classes());
    assert!(before.iter().any(|event| event.site == key
        && event.stage == BridgeReceiptStage::Terminal
        && event.state == BridgeReceiptState::Applied));
    let independent = add_independent_site(&mut plan, seam.owner_class);
    require_atom_fate(&plan, &key, &independent, &seam.atom_ids[0]);
}

#[test]
fn zero_syntax_custody_discarded_one_element_source_drops_with_source_atom() {
    check_real_zero(false);
}

#[test]
fn zero_syntax_custody_readonly_one_element_source_drops_with_source_atom() {
    check_real_zero(true);
}

#[test]
fn zero_syntax_custody_explicit_to_zero_replacement_preserves_atom_dependency() {
    let (_, new, file, lo, hi) = fixture(false);
    let mut old = new.clone();
    old.zero_syntax = false;
    old.replacement = "core::ptr::from_ref(p)".into();
    let key = exact_key(&old, &file, lo, hi);
    let mut site = ClassSite::edit(
        old.owner_class,
        old.owner_class,
        Arm::C,
        &super::bridge_custody_export::file_label(&file),
        lo as u32,
        hi as u32,
        &old.bridge.bridge_kind,
    );
    site.key = key.clone();
    site.atom_ids = old.atom_ids.clone();
    let mut input = ClassInput::new(old.owner_class, RequiredArmSet::default());
    input.sites.push(site);
    let edit = Edit {
        lo,
        hi,
        replacement: old.replacement.clone(),
        justification: Justification::SeamAdapter {
            family: "safe",
            fabricated: false,
        },
        owner_class: Some(old.owner_class),
        owner_path: old.owner_fn.clone(),
        bridge: Some(old.bridge.clone()),
        atom_ids: old.atom_ids.clone(),
        subject_id: "constructed-replacement-control".into(),
        required_arms: "c".into(),
        edit_kind: "seam-adapter",
    };
    let mut plan = Plan {
        by_file: BTreeMap::from([(file.clone(), vec![edit])]),
        class_finalization: super::plan::finalize_class_inputs(vec![input]),
        ..Default::default()
    };
    plan.replace_terminal_seam(&old, &new, (file, lo, hi))
        .unwrap();
    assert!(
        plan.by_file.values().all(Vec::is_empty),
        "replacement removes the physical carrier"
    );
    let site = &plan.class_finalization.classes[&new.owner_class].sites[0];
    assert_eq!(site.state, ClassSiteState::ZeroSyntaxReady);
    assert_eq!(site.atom_ids, new.atom_ids);
    let independent = add_independent_site(&mut plan, new.owner_class);
    require_atom_fate(&plan, &key, &independent, &new.atom_ids[0]);
}

/// **R285-3's receipt, as a live witness.** The shape these fixtures used to
/// take is held, not quietly absent: the returned-parent source degrades with
/// `ThinExtent` before a seam exists, which is why the route above changed.
#[test]
fn thin_extent_holds_the_returned_parent_zero_syntax_source() {
    let source = "#![allow(dead_code, unused_variables, unused_unsafe)]\n\
         extern \"C\" { fn strchr(s: *const i8, c: i32) -> *mut i8; }\n\
         unsafe fn target(p: *const i8) -> i8 { strchr(p, 65); let parent_read = *p; parent_read }\n\
         pub unsafe fn entry() -> i8 {\n\
             let mut storage: [i8; 2] = [65, 0];\n\
             target(storage.as_mut_ptr() as *const i8)\n\
         }\n";
    ::utils::compilation::run_compiler_on_str(source, |tcx| {
        let (table, _) = super::decide_table_with_ctx_config(tcx, Some((
            crate::analyses::borrow_ownership::a5_overlap::A5Mode::PreciseReplay,
            Some(crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph),
        ))).expect("actual fixture decisions");
        let (_, decision) = table
            .entries
            .iter()
            .find(|(subject, _)| subject.label == "target::p")
            .expect("the fixture's source subject");
        assert!(
            matches!(
                decision,
                Decision::Degraded(degraded)
                    if degraded.reason == super::decision::DegradeReason::ThinExtent
            ),
            "the returned-parent NUL-terminated source must be held, not delivered thin: {decision:?}"
        );
    })
    .expect("held-source fixture compiles");
}
