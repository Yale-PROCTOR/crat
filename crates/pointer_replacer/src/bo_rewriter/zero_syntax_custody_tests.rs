//! Logical receipt custody for real returned-parent zero-syntax seams.
//! Independent control sites are constructed receipt inputs, not model facts.

use std::collections::{BTreeMap, BTreeSet};

use super::{
    bridge_receipt::{BridgeReceiptStage, BridgeReceiptState, BridgeSiteKey, SignatureClassId},
    decision::{Arm, Decision, RequiredArmSet, seam::SeamEdit},
    plan::{ClassInput, ClassSite, ClassSiteState, Edit, FileKey, Justification, Plan},
};

fn fixture(readonly: bool) -> (Plan, SeamEdit, FileKey, usize, usize) {
    let body = if readonly {
        "let child = strchr(p, 65); let copied = child;\n\
         let parent_read = *p;\n\
         if copied.is_null() { parent_read } else { parent_read ^ *copied }"
    } else {
        "strchr(p, 65); let parent_read = *p; parent_read"
    };
    // Exact accepted discarded/readonly inputs from retalias_semantics_tests.
    let source = format!(
        "#![allow(dead_code, unused_variables, unused_unsafe)]\n\
         extern \"C\" {{ fn strchr(s: *const i8, c: i32) -> *mut i8; }}\n\
         unsafe fn target(p: *const i8) -> i8 {{ {body} }}\n\
         pub unsafe fn entry() -> i8 {{\n\
             let mut storage: [i8; 2] = [65, 0];\n\
             target(storage.as_mut_ptr() as *const i8)\n\
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
                && seam.raw_outbound.as_ref().is_some_and(|endpoint| endpoint.returned_child.is_some())
        }).collect::<Vec<_>>();
        let [seam] = seams.as_slice() else { panic!("one real returned-parent seam required: {seams:?}") };
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
            let (files, _, _) = super::ast_transform::ast_emitted_files_from(tcx, &capture, &reverts,
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
fn zero_syntax_custody_discarded_return_parent_drops_with_source_atom() {
    check_real_zero(false);
}

#[test]
fn zero_syntax_custody_readonly_return_parent_drops_with_source_atom() {
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
