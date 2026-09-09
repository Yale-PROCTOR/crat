//! Standalone R244 witnesses. This does not register production emission.
#![allow(dead_code)]
#[path = "../src/bo_rewriter/ownership_fields.rs"]
mod ownership_fields;

use std::collections::{BTreeMap, BTreeSet};

use ownership_fields::{FieldClassId, OwnerId, SiteId, transaction::*};

fn field(n: u32) -> FieldClassId {
    FieldClassId {
        owner: OwnerId(1),
        field: n,
    }
}
fn site(n: u32) -> SiteId {
    SiteId {
        owner: OwnerId(1),
        occurrence: n,
    }
}
fn transaction(n: u32) -> Transaction {
    Transaction {
        id: ClassId::Field(field(n)),
        prerequisites: BTreeSet::new(),
        sites: BTreeMap::from([(site(n), SiteState::Ready)]),
    }
}

#[test]
fn field_transaction_removes_dependents_but_preserves_independent_sibling() {
    let mut failed = transaction(0);
    failed
        .sites
        .insert(site(0), SiteState::Held("constructor missing".into()));
    let mut dependent = transaction(1);
    dependent.prerequisites.insert(failed.id);
    let independent = transaction(2);
    let result = finalize(&[failed.clone(), dependent.clone(), independent.clone()]).unwrap();
    assert_eq!(result.live, BTreeSet::from([independent.id]));
    assert_eq!(result.held[&dependent.id], Hold::Prerequisite(failed.id));
}

#[test]
fn complete_interface_cycle_survives_but_missing_site_does_not() {
    let mut a = transaction(0);
    let mut b = transaction(1);
    a.prerequisites.insert(b.id);
    b.prerequisites.insert(a.id);
    assert_eq!(finalize(&[a.clone(), b.clone()]).unwrap().live.len(), 2);
    b.sites.clear();
    assert!(finalize(&[a, b]).unwrap().live.is_empty());
}

#[test]
fn field_lifetimes_are_stable_under_independent_recovery() {
    let fields: Vec<_> = (0..2)
        .map(|n| Field {
            id: field(n),
            name: format!("f{n}"),
            input_type: "*const i32".into(),
            candidate: FieldForm::Borrow {
                pointee: "i32".into(),
                mutable: false,
                optional: true,
            },
        })
        .collect();
    let tx = vec![transaction(0), transaction(1)];
    let full = struct_interface(
        OwnerId(1),
        &fields,
        &BTreeSet::from(["__crat_f0".into()]),
        &CopyContract::Absent,
        &tx,
        &finalize(&tx).unwrap(),
    )
    .unwrap();
    assert_eq!(full.field_types[&field(0)], "Option<&'__crat_f0_1 i32>");
    let mut partial = tx.clone();
    partial[0].sites.clear();
    let recovered = struct_interface(
        OwnerId(1),
        &fields,
        &BTreeSet::from(["__crat_f0".into()]),
        &CopyContract::Absent,
        &partial,
        &finalize(&partial).unwrap(),
    )
    .unwrap();
    assert_eq!(recovered.field_types[&field(0)], "*const i32");
    assert_eq!(
        recovered.field_types[&field(1)],
        full.field_types[&field(1)]
    );
    assert_eq!(recovered.lifetimes, vec!["__crat_f1"]);
}

#[test]
fn owning_field_requires_every_source_struct_copy_site() {
    let fields = vec![Field {
        id: field(0),
        name: "child".into(),
        input_type: "*mut Node".into(),
        candidate: FieldForm::Owning {
            pointee: "Node".into(),
            optional: true,
        },
    }];
    let mut tx = vec![transaction(0)];
    let copy = CopyContract::Removable {
        sites: BTreeSet::from([site(8)]),
    };
    assert_eq!(
        struct_interface(
            OwnerId(1),
            &fields,
            &BTreeSet::new(),
            &copy,
            &tx,
            &finalize(&tx).unwrap()
        ),
        Err(Error::CopySiteMissing(site(8)))
    );
    tx[0].sites.insert(site(8), SiteState::Ready);
    let interface = struct_interface(
        OwnerId(1),
        &fields,
        &BTreeSet::new(),
        &copy,
        &tx,
        &finalize(&tx).unwrap(),
    )
    .unwrap();
    assert!(interface.remove_copy_clone);
    assert_eq!(interface.field_types[&field(0)], "Option<Box<Node>>");
    assert!(interface.lifetimes.is_empty());
}

use ownership_fields::{EvidenceKey, lifecycle::*};
fn key(n: u32) -> EvidenceKey {
    EvidenceKey {
        model: [1; 32],
        configuration: [2; 32],
        site: site(n),
        generation: 3,
    }
}
fn proofs(k: EvidenceKey) -> CloseProofs {
    CloseProofs {
        event: Some((k, CloseKind::ScopeExit)),
        all_roots: Some(k),
        continuation: Some(k),
        no_live_reference: Some(k),
        no_protector: Some(k),
        allocator_layout: Some(k),
        target_permission: Some(k),
    }
}
fn recursive_graph() -> BTreeMap<OwnerId, DropShape> {
    BTreeMap::from([(OwnerId(1), DropShape::Fields(vec![OwnerId(1)]))])
}
#[test]
fn deep_recursive_payload_leaks_at_each_unwitnessed_implicit_close() {
    for kind in [
        CloseKind::ScopeExit,
        CloseKind::Overwrite,
        CloseKind::Unwind,
    ] {
        let plan = implicit_close(
            key(0),
            kind,
            OwnerId(1),
            &recursive_graph(),
            [3; 32],
            None,
            &proofs_for(key(0), kind),
        )
        .unwrap();
        assert_eq!(plan, ClosePlan::LeakRecursive { key: key(0), kind });
        assert_eq!(plan.receipt(), "waiver-leak(recursive-drop)");
    }
}
#[test]
fn shallow_recursive_payload_drops_only_with_exact_depth_witness() {
    let depth = DepthWitness {
        kind: CloseKind::ScopeExit,
        key: key(0),
        payload: OwnerId(1),
        graph_revision: [3; 32],
        maximum_depth: 2,
        admitted_depth: 2,
    };
    let result = implicit_close(
        key(0),
        CloseKind::ScopeExit,
        OwnerId(1),
        &recursive_graph(),
        [3; 32],
        Some(&depth),
        &proofs(key(0)),
    )
    .unwrap();
    assert_eq!(result.receipt(), "waiver-drop(scope-exit)");
    assert!(matches!(result, ClosePlan::Drop { .. }));
    assert_eq!(
        implicit_close(
            key(1),
            CloseKind::ScopeExit,
            OwnerId(1),
            &recursive_graph(),
            [3; 32],
            Some(&depth),
            &proofs(key(1))
        ),
        Err(CloseHold::DepthWitnessMismatch)
    );
}
#[test]
fn recursion_leak_does_not_hide_missing_all_roots_or_unknown_shape() {
    let mut evidence = proofs(key(0));
    evidence.all_roots = None;
    assert_eq!(
        implicit_close(
            key(0),
            CloseKind::ScopeExit,
            OwnerId(1),
            &recursive_graph(),
            [3; 32],
            None,
            &evidence
        ),
        Err(CloseHold::MissingProof("all-roots"))
    );
    let graph = BTreeMap::from([(OwnerId(1), DropShape::Fields(vec![OwnerId(2)]))]);
    assert_eq!(
        implicit_close(
            key(0),
            CloseKind::ScopeExit,
            OwnerId(1),
            &graph,
            [3; 32],
            None,
            &proofs(key(0))
        ),
        Err(CloseHold::UnknownShape(OwnerId(2)))
    );
}

use ownership_fields::hoist::*;
fn hoist_fixture() -> (Vec<Argument>, HoistWitness) {
    let args = vec![
        Argument::Consume {
            key: key(0),
            expression: "root.right.take()".into(),
        },
        Argument::ScalarRead {
            key: key(1),
            expression: "temp_1.key".into(),
        },
    ];
    let witness = HoistWitness {
        call: site(5),
        read: key(1),
        consume: key(0),
        original_order: vec![site(0), site(1)],
        scalar_effect_free_nontrapping: true,
        callee_commutes: true,
        commutes_with: BTreeSet::from([site(0)]),
        no_independent_protector: true,
    };
    (args, witness)
}
#[test]
fn bst_scalar_read_hoists_before_same_call_take_with_hygienic_name() {
    let (args, witness) = hoist_fixture();
    let plan = plan_scalar_hoist(
        site(5),
        &args,
        &witness,
        &BTreeSet::from(["__crat_scalar".into()]),
    )
    .unwrap();
    assert_eq!(plan.binding, "let __crat_scalar_1 = temp_1.key;");
    assert_eq!(plan.arguments, ["root.right.take()", "__crat_scalar_1"]);
}
#[test]
fn hoist_refuses_effectful_read_intervening_write_and_active_protector() {
    let (args, mut witness) = hoist_fixture();
    witness.scalar_effect_free_nontrapping = false;
    assert_eq!(
        plan_scalar_hoist(site(5), &args, &witness, &BTreeSet::new()),
        Err(HoistHold::EffectfulRead)
    );
    witness.scalar_effect_free_nontrapping = true;
    witness.commutes_with.clear();
    assert_eq!(
        plan_scalar_hoist(site(5), &args, &witness, &BTreeSet::new()),
        Err(HoistHold::InterveningEffect(site(0)))
    );
    witness.commutes_with.insert(site(0));
    witness.no_independent_protector = false;
    assert_eq!(
        plan_scalar_hoist(site(5), &args, &witness, &BTreeSet::new()),
        Err(HoistHold::Protector)
    );
}
#[test]
fn hoist_requires_same_generation_model_configuration_and_exact_order() {
    let (mut args, witness) = hoist_fixture();
    args.swap(0, 1);
    assert_eq!(
        plan_scalar_hoist(site(5), &args, &witness, &BTreeSet::new()),
        Err(HoistHold::StaleOrder)
    );
}

use ownership_fields::emission::*;
fn grant(k: EvidenceKey) -> Grant {
    Grant {
        key: k,
        kind: Kind::Owning,
        status: GrantStatus::Selected,
        transport: Some(k),
    }
}
fn call_facts(k: EvidenceKey) -> OwnCallFacts {
    OwnCallFacts {
        key: k,
        call: Span { start: 10, end: 20 },
        protector: Span { start: 10, end: 20 },
        whole_payload: true,
        references: vec![],
        reference_inventory: Some(k),
        helper_lowering: Some(k),
        permission: Some(k),
        transfer_cleanup: Some(k),
    }
}
#[test]
fn owning_call_checks_whole_payload_and_full_protector_with_dead_named_reference() {
    let k = key(0);
    let g = grant(k);
    let mut facts = call_facts(k);
    assert!(admit_call(&g, &facts).is_ok());
    facts.protector.end = 15;
    assert!(matches!(admit_call(&g, &facts), Err(EmitHold::CallSpan)));
    facts.protector.end = 20;
    facts.references.push(ReferenceInterval {
        generation: k.generation,
        live: Span { start: 0, end: 4 },
        protected: Some(Span { start: 0, end: 30 }),
    });
    assert!(matches!(admit_call(&g, &facts), Err(EmitHold::Protector)));
}
#[test]
fn fresh_return_receiver_does_not_request_borrow_origin_or_initializer() {
    let k = key(0);
    let permit = admit_call(&grant(k), &call_facts(k)).unwrap();
    let ty = OwnerType {
        pointee: "Node".into(),
        optional: false,
    };
    assert_eq!(
        receiver(
            &permit,
            "buf",
            &ty,
            &OwnerInput::Transfer {
                expression: "make()".into()
            }
        )
        .unwrap()
        .code,
        "let mut buf: Box<Node> = make();"
    );
    assert_eq!(consume_argument(&permit, "buf", false).code, "buf");
    assert_eq!(
        consume_argument(&permit, "s.child", true).code,
        "(s.child).take()"
    );
}
#[test]
fn explicit_free_joins_exact_sink_and_requires_allocator_contract() {
    let k = key(0);
    let permit = admit_call(&grant(k), &call_facts(k)).unwrap();
    assert_eq!(
        explicit_free(&permit, k, "s.child", true, Some(k))
            .unwrap()
            .code,
        "drop((s.child).take());"
    );
    assert_eq!(
        explicit_free(&permit, key(1), "s.child", true, Some(k)),
        Err(EmitHold::SinkIdentity)
    );
}
#[test]
fn recursive_leak_local_wraps_before_any_unwind_and_suppresses_overwrite() {
    let k = key(0);
    let (mut local, init) = leak_local(
        &leak_coverage(k),
        "owner",
        OwnerType {
            pointee: "Node".into(),
            optional: true,
        },
        "make()",
    )
    .unwrap();
    assert_eq!(
        init.code,
        "let mut owner: std::mem::ManuallyDrop<Option<Box<Node>>> = std::mem::ManuallyDrop::new(make());"
    );
    let overwrite = ClosePlan::LeakRecursive {
        key: k,
        kind: CloseKind::Overwrite,
    };
    let mut next_key = k;
    next_key.generation = 4;
    assert_eq!(
        local
            .overwrite(&overwrite, &leak_coverage(next_key), "make()")
            .unwrap()
            .code,
        "owner = std::mem::ManuallyDrop::new(make());"
    );
    let permit = admit_call(&grant(next_key), &call_facts(next_key)).unwrap();
    assert_eq!(
        local.free(&permit, next_key, Some(next_key)).unwrap().code,
        "drop((owner).take());"
    );
}
#[test]
fn missing_transfer_cleanup_cannot_expose_an_unprotected_box_temporary() {
    let k = key(0);
    let mut facts = call_facts(k);
    facts.transfer_cleanup = None;
    assert!(matches!(
        admit_call(&grant(k), &facts),
        Err(EmitHold::MissingEvidence("transfer-cleanup"))
    ));
}

/// These execute only newly emitted safe Rust witnesses, never raw C input.
/// Each rustc invocation type/borrow-checks the emitted text, not just parsing.
fn compile_source(source: &str, run: bool) -> std::process::Output {
    use std::{
        io::Write,
        process::{Command, Stdio},
        sync::atomic::{AtomicUsize, Ordering},
    };
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "crat-owner-fixture-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::SeqCst)
    ));
    std::fs::create_dir(&dir).unwrap();
    let executable = dir.join("fixture");
    let mut compiler = Command::new("rustc")
        .args(["--edition=2024", "--crate-name", "ownership_fixture", "-"])
        .arg("-o")
        .arg(&executable)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    compiler
        .stdin
        .take()
        .unwrap()
        .write_all(source.as_bytes())
        .unwrap();
    let compiled = compiler.wait_with_output().unwrap();
    if run {
        assert!(
            compiled.status.success(),
            "{}",
            String::from_utf8_lossy(&compiled.stderr)
        );
    }
    let output = if run {
        Command::new(&executable).output().unwrap()
    } else {
        compiled
    };
    std::fs::remove_dir_all(dir).unwrap();
    output
}

#[test]
fn bst_hoisted_emission_passes_borrow_check_where_read_after_take_fails() {
    let prefix = "struct Node { key:i32, right:Option<Box<Node>> }\nfn deleteNode(_:Option<Box<Node>>, _:i32)->Option<Box<Node>> {None}\n";
    let original = format!(
        "{prefix} fn witness(mut root:Node) {{ let temp_1=root.right.as_ref().unwrap(); root.right=deleteNode(root.right.take(),temp_1.key); }} fn main(){{}}"
    );
    let red = compile_source(&original, false);
    assert!(!red.status.success());
    assert!(String::from_utf8_lossy(&red.stderr).contains("E0502"));
    let (args, witness) = hoist_fixture();
    let plan = plan_scalar_hoist(site(5), &args, &witness, &BTreeSet::new()).unwrap();
    let emitted = format!(
        "{prefix} fn witness(mut root:Node) {{ let temp_1=root.right.as_ref().unwrap(); {} root.right=deleteNode({}); }} fn main(){{}}",
        plan.binding,
        plan.arguments.join(", ")
    );
    let result = compile_source(&emitted, false);
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
}

#[test]
fn emitted_deep_scope_and_overwrite_unwind_carrier_performs_no_payload_drop() {
    let k = key(0);
    let graph = recursive_graph();
    let (mut local, init) = leak_local(
        &leak_coverage(k),
        "owner",
        OwnerType {
            pointee: "Node".into(),
            optional: true,
        },
        "make(20000)",
    )
    .unwrap();
    let old = implicit_close(
        k,
        CloseKind::Overwrite,
        OwnerId(1),
        &graph,
        [3; 32],
        None,
        &proofs_for(k, CloseKind::Overwrite),
    )
    .unwrap();
    let mut next = k;
    next.generation = 4;
    let assign = local
        .overwrite(&old, &leak_coverage(next), "make(2)")
        .unwrap();
    let source = format!(
        r#"
        use std::sync::atomic::{{AtomicUsize,Ordering}};
        static DROPS:AtomicUsize=AtomicUsize::new(0);
        struct Node{{ next:Option<Box<Node>> }}
        impl Drop for Node{{fn drop(&mut self){{DROPS.fetch_add(1,Ordering::SeqCst);}}}}
        fn make(n:usize)->Option<Box<Node>>{{let mut p=None;for _ in 0..n{{p=Some(Box::new(Node{{next:p}}));}}p}}
        fn main(){{
            {{ {} {} }}
            assert_eq!(DROPS.load(Ordering::SeqCst),0);
            let _=std::panic::catch_unwind(||{{ {} panic!("fixture cleanup"); }});
            assert_eq!(DROPS.load(Ordering::SeqCst),0);
            let _=std::panic::catch_unwind(||{{ {} owner=std::mem::ManuallyDrop::new(panic_rhs()); }});
            assert_eq!(DROPS.load(Ordering::SeqCst),0);
        }}
        fn panic_rhs()->Option<Box<Node>>{{panic!("fixture rhs")}}
    "#,
        init.code, assign.code, init.code, init.code
    );
    let result = compile_source(&source, true);
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
}

#[test]
fn emitted_struct_copy_adaptation_and_explicit_free_drop_exactly_once() {
    let fields = vec![Field {
        id: field(0),
        name: "child".into(),
        input_type: "*mut i32".into(),
        candidate: FieldForm::Owning {
            pointee: "i32".into(),
            optional: true,
        },
    }];
    let tx = vec![transaction(0)];
    let form = struct_interface(
        OwnerId(1),
        &fields,
        &BTreeSet::new(),
        &CopyContract::Removable {
            sites: BTreeSet::from([site(0)]),
        },
        &tx,
        &finalize(&tx).unwrap(),
    )
    .unwrap();
    assert!(form.remove_copy_clone);
    let k = key(0);
    let permit = admit_call(&grant(k), &call_facts(k)).unwrap();
    let drop = explicit_free(&permit, k, "moved.child", true, Some(k)).unwrap();
    let source = format!(
        "struct Holder {{ child:{} }} fn main() {{ let original=Holder {{child:Some(Box::new(3))}}; let mut moved=original; assert_eq!(**moved.child.as_ref().unwrap(),3); {} assert!(moved.child.is_none()); }}",
        form.field_types[&field(0)],
        drop.code
    );
    assert!(compile_source(&source, true).status.success());
    let forbidden = format!("#[derive(Copy,Clone)] {source}");
    let bad = compile_source(&forbidden, false);
    assert!(!bad.status.success());
    assert!(String::from_utf8_lossy(&bad.stderr).contains("E0204"));
}

#[test]
fn permitted_shallow_close_and_explicit_free_are_not_suppressed() {
    let k = key(0);
    let depth = DepthWitness {
        kind: CloseKind::ScopeExit,
        key: k,
        payload: OwnerId(1),
        graph_revision: [3; 32],
        maximum_depth: 2,
        admitted_depth: 2,
    };
    let close = implicit_close(
        k,
        CloseKind::ScopeExit,
        OwnerId(1),
        &recursive_graph(),
        [3; 32],
        Some(&depth),
        &proofs(k),
    )
    .unwrap();
    assert!(matches!(close, ClosePlan::Drop { .. }));
    let (local, init) = leak_local(
        &leak_coverage(k),
        "owner",
        OwnerType {
            pointee: "Node".into(),
            optional: true,
        },
        "Some(Box::new(Node))",
    )
    .unwrap();
    let permit = admit_call(&grant(k), &call_facts(k)).unwrap();
    let free = local.free(&permit, k, Some(k)).unwrap();
    let source = format!(
        "use std::sync::atomic::{{AtomicUsize,Ordering}}; static N:AtomicUsize=AtomicUsize::new(0);struct Node;impl Drop for Node{{fn drop(&mut self){{N.fetch_add(1,Ordering::SeqCst);}}}}fn main(){{ {} {} assert_eq!(N.load(Ordering::SeqCst),1); }}",
        init.code, free.code
    );
    assert!(compile_source(&source, true).status.success());
}

use ownership_fields::declaration::*;
fn captured(source: &str, text: &str) -> CapturedSpan {
    let lo = source.find(text).unwrap();
    CapturedSpan {
        lo,
        hi: lo + text.len(),
        text: text.into(),
    }
}
#[test]
fn structural_renderer_composes_copy_removal_owning_field_and_borrow_lifetime() {
    let source =
        "#[derive(Copy, Clone, Debug)]\nstruct Holder { child: *mut i32, view: *const i32 }";
    let before_brace = source.find(" {").unwrap();
    let declaration = Declaration {
        owner: OwnerId(1),
        fields: BTreeMap::from([
            (field(0), captured(source, "*mut i32")),
            (field(1), captured(source, "*const i32")),
        ]),
        generics: GenericSite {
            span: CapturedSpan {
                lo: before_brace,
                hi: before_brace,
                text: String::new(),
            },
            parameters: vec![],
        },
        derives: vec![DeriveSite {
            span: captured(source, "#[derive(Copy, Clone, Debug)]"),
            traits: vec![
                DeriveTrait::BuiltinCopy,
                DeriveTrait::BuiltinClone,
                DeriveTrait::Other("Debug".into()),
            ],
        }],
    };
    let interface = StructInterface {
        terminal_fields: BTreeSet::from([field(0)]),
        field_types: BTreeMap::from([
            (field(0), "Option<Box<i32>>".into()),
            (field(1), "&'__crat_f1 i32".into()),
        ]),
        lifetimes: vec!["__crat_f1".into()],
        remove_copy_clone: true,
    };
    let rendered = render_declaration(source, &declaration, &interface).unwrap();
    assert_eq!(
        rendered,
        "#[derive(Debug)]\nstruct Holder<'__crat_f1> { child: Option<Box<i32>>, view: &'__crat_f1 i32 }"
    );
    let program = format!(
        "{rendered}\nfn main() {{ let value=7; let original=Holder{{child:Some(Box::new(3)),view:&value}}; let moved=original; assert_eq!(*moved.view,7); }}"
    );
    assert!(compile_source(&program, true).status.success());
    assert_eq!(
        render_declaration(
            &source.replace("*mut i32", "*mut u32"),
            &declaration,
            &interface
        ),
        Err(DeclarationHold::StaleSpan)
    );
}

#[test]
fn unrelated_ready_site_cannot_pay_an_owning_field_copy_obligation() {
    let fields = vec![Field {
        id: field(0),
        name: "child".into(),
        input_type: "*mut i32".into(),
        candidate: FieldForm::Owning {
            pointee: "i32".into(),
            optional: true,
        },
    }];
    let mut unrelated = transaction(9);
    unrelated.sites.insert(site(8), SiteState::Ready);
    let tx = vec![transaction(0), unrelated];
    assert_eq!(
        struct_interface(
            OwnerId(1),
            &fields,
            &BTreeSet::new(),
            &CopyContract::Removable {
                sites: BTreeSet::from([site(8)])
            },
            &tx,
            &finalize(&tx).unwrap()
        ),
        Err(Error::CopySiteMissing(site(8)))
    );
}

#[test]
fn scope_depth_witness_cannot_authorize_unwind_drop() {
    let k = key(0);
    let witness = DepthWitness {
        kind: CloseKind::ScopeExit,
        key: k,
        payload: OwnerId(1),
        graph_revision: [3; 32],
        maximum_depth: 2,
        admitted_depth: 2,
    };
    assert_eq!(
        implicit_close(
            k,
            CloseKind::Unwind,
            OwnerId(1),
            &recursive_graph(),
            [3; 32],
            Some(&witness),
            &proofs(k)
        ),
        Err(CloseHold::StaleProof("close-event"))
    );
}
#[test]
fn local_carrier_requires_unwind_coverage_before_suppressing_all_exits() {
    let plan = ClosePlan::LeakRecursive {
        key: key(0),
        kind: CloseKind::ScopeExit,
    };
    assert!(matches!(
        leak_local(
            &LeakCoverage {
                local: key(0),
                completeness: Some(key(0)),
                closes: vec![plan]
            },
            "owner",
            OwnerType {
                pointee: "Node".into(),
                optional: true
            },
            "make()"
        ),
        Err(EmitHold::MissingEvidence("leak-unwind-coverage"))
    ));
}
#[test]
fn empty_reference_interval_does_not_overlap_owning_call() {
    let k = key(0);
    let mut facts = call_facts(k);
    facts.references.push(ReferenceInterval {
        generation: k.generation,
        live: Span { start: 15, end: 15 },
        protected: None,
    });
    assert!(admit_call(&grant(k), &facts).is_ok());
}
#[test]
fn optional_leak_carrier_free_preserves_empty_shell() {
    let k = key(0);
    let (local, init) = leak_local(
        &leak_coverage(k),
        "owner",
        OwnerType {
            pointee: "i32".into(),
            optional: true,
        },
        "Some(Box::new(3))",
    )
    .unwrap();
    let permit = admit_call(&grant(k), &call_facts(k)).unwrap();
    let free = local.free(&permit, k, Some(k)).unwrap();
    let result = compile_source(
        &format!(
            "fn main(){{{} {} assert!(owner.is_none());}}",
            init.code, free.code
        ),
        false,
    );
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
}

fn proofs_for(k: EvidenceKey, kind: CloseKind) -> CloseProofs {
    let mut p = proofs(k);
    p.event = Some((k, kind));
    p
}
fn leak_coverage(k: EvidenceKey) -> LeakCoverage {
    let closes = [CloseKind::ScopeExit, CloseKind::Unwind]
        .into_iter()
        .map(|kind| {
            implicit_close(
                k,
                kind,
                OwnerId(1),
                &recursive_graph(),
                [3; 32],
                None,
                &proofs_for(k, kind),
            )
            .unwrap()
        })
        .collect();
    LeakCoverage {
        local: k,
        completeness: Some(k),
        closes,
    }
}

use ownership_fields::custody::*;
#[test]
fn custody_rejects_equal_count_identity_swaps_and_planned_but_raw_fields() {
    let interface = StructInterface {
        terminal_fields: BTreeSet::from([field(0)]),
        field_types: BTreeMap::from([(field(0), "Option<Box<i32>>".into())]),
        lifetimes: vec![],
        remove_copy_clone: true,
    };
    let terminal = finalize(&[transaction(0)]).unwrap();
    let mut observation = Observation {
        source_hash: [7; 32],
        field_types: interface.field_types.clone(),
        lifetimes: vec![],
        has_copy_clone: false,
    };
    assert_eq!(
        check_fields(
            &[],
            [7; 32],
            &interface,
            &terminal,
            &BTreeSet::from([field(1)]),
            &observation
        ),
        Err(CustodyError::DeliveredIdentity)
    );
    observation.field_types.insert(field(0), "*mut i32".into());
    assert_eq!(
        check_fields(
            &[],
            [7; 32],
            &interface,
            &terminal,
            &BTreeSet::from([field(0)]),
            &observation
        ),
        Err(CustodyError::FieldType(field(0)))
    );
}

#[test]
fn each_r101_obligation_is_required_even_on_recursive_leak_path() {
    for field in 0..6 {
        let k = key(0);
        let mut p = proofs(k);
        let slots = [
            &mut p.all_roots,
            &mut p.continuation,
            &mut p.no_live_reference,
            &mut p.no_protector,
            &mut p.allocator_layout,
            &mut p.target_permission,
        ];
        *slots.into_iter().nth(field).unwrap() = None;
        assert!(matches!(
            implicit_close(
                k,
                CloseKind::ScopeExit,
                OwnerId(1),
                &recursive_graph(),
                [3; 32],
                None,
                &p
            ),
            Err(CloseHold::MissingProof(_))
        ));
    }
}
#[test]
fn raw_candidate_retracted_and_stale_grants_never_enter_emission() {
    let k = key(0);
    for kind in [Kind::Raw, Kind::Ref] {
        let mut g = grant(k);
        g.kind = kind;
        assert!(matches!(
            admit_call(&g, &call_facts(k)),
            Err(EmitHold::Grant)
        ));
    }
    for status in [GrantStatus::Candidate, GrantStatus::Retracted] {
        let mut g = grant(k);
        g.status = status;
        assert!(matches!(
            admit_call(&g, &call_facts(k)),
            Err(EmitHold::Grant)
        ));
    }
    let mut facts = call_facts(k);
    facts.whole_payload = false;
    assert!(matches!(
        admit_call(&grant(k), &facts),
        Err(EmitHold::Payload)
    ));
    facts.whole_payload = true;
    facts.key.model = [9; 32];
    assert!(matches!(
        admit_call(&grant(k), &facts),
        Err(EmitHold::CallIdentity)
    ));
}
#[test]
fn typed_constructor_preserves_null_and_requires_layout_and_initialization() {
    let k = key(0);
    let permit = admit_call(&grant(k), &call_facts(k)).unwrap();
    let ty = OwnerType {
        pointee: "i32".into(),
        optional: true,
    };
    assert_eq!(
        receiver(&permit, "p", &ty, &OwnerInput::Null).unwrap().code,
        "let mut p: Option<Box<i32>> = None;"
    );
    let input = OwnerInput::Construct {
        value: "3".into(),
        layout: Some(k),
        initialization: None,
    };
    assert_eq!(
        receiver(&permit, "p", &ty, &input),
        Err(EmitHold::Construction)
    );
    let input = OwnerInput::Construct {
        value: "3".into(),
        layout: Some(k),
        initialization: Some(k),
    };
    let code = receiver(&permit, "p", &ty, &input).unwrap().code;
    assert!(
        compile_source(
            &format!("fn main(){{{code} assert_eq!(p.as_deref(),Some(&3));}}"),
            true
        )
        .status
        .success()
    );
}
#[test]
fn hoist_checks_arguments_before_consume_and_not_only_between_read_and_consume() {
    let (mut args, mut witness) = hoist_fixture();
    args.insert(
        0,
        Argument::Other {
            site: site(9),
            expression: "mutate_alias()".into(),
        },
    );
    witness.original_order.insert(0, site(9));
    assert_eq!(
        plan_scalar_hoist(site(5), &args, &witness, &BTreeSet::new()),
        Err(HoistHold::InterveningEffect(site(9)))
    );
    witness.commutes_with.insert(site(9));
    witness.callee_commutes = false;
    assert_eq!(
        plan_scalar_hoist(site(5), &args, &witness, &BTreeSet::new()),
        Err(HoistHold::CalleeOrder)
    );
}
#[test]
fn close_graph_unknown_branch_is_not_hidden_by_an_earlier_cycle() {
    let graph = BTreeMap::from([(OwnerId(1), DropShape::Fields(vec![OwnerId(1), OwnerId(2)]))]);
    assert_eq!(
        implicit_close(
            key(0),
            CloseKind::ScopeExit,
            OwnerId(1),
            &graph,
            [3; 32],
            None,
            &proofs(key(0))
        ),
        Err(CloseHold::UnknownShape(OwnerId(2)))
    );
}
#[test]
fn deep_type_graph_inspection_uses_no_recursive_host_stack() {
    let mut graph = BTreeMap::new();
    for n in 0..20000 {
        graph.insert(OwnerId(n), DropShape::Fields(vec![OwnerId(n + 1)]));
    }
    graph.insert(OwnerId(20000), DropShape::Leaf);
    assert!(matches!(
        implicit_close(
            key(0),
            CloseKind::ScopeExit,
            OwnerId(0),
            &graph,
            [3; 32],
            None,
            &proofs(key(0))
        ),
        Ok(ClosePlan::Drop { .. })
    ));
}
#[test]
fn duplicated_class_and_stale_finalization_are_rejected() {
    assert_eq!(
        finalize(&[transaction(0), transaction(0)]),
        Err(Error::DuplicateClass(ClassId::Field(field(0))))
    );
    let mut tx = transaction(0);
    let old = finalize(&[tx.clone()]).unwrap();
    tx.sites.clear();
    assert_eq!(
        struct_interface(
            OwnerId(1),
            &[],
            &BTreeSet::new(),
            &CopyContract::Absent,
            &[tx],
            &old
        ),
        Err(Error::StaleFinalization)
    );
}
#[test]
fn bounded_recursive_ordinary_scope_close_executes_destructors() {
    let k = key(0);
    let depth = DepthWitness {
        kind: CloseKind::ScopeExit,
        key: k,
        payload: OwnerId(1),
        graph_revision: [3; 32],
        maximum_depth: 2,
        admitted_depth: 2,
    };
    assert!(matches!(
        implicit_close(
            k,
            CloseKind::ScopeExit,
            OwnerId(1),
            &recursive_graph(),
            [3; 32],
            Some(&depth),
            &proofs(k)
        ),
        Ok(ClosePlan::Drop { .. })
    ));
    let permit = admit_call(&grant(k), &call_facts(k)).unwrap();
    let emitted = receiver(
        &permit,
        "owner",
        &OwnerType {
            pointee: "Node".into(),
            optional: true,
        },
        &OwnerInput::Transfer {
            expression: "make()".into(),
        },
    )
    .unwrap();
    let source = format!(
        "use std::sync::atomic::{{AtomicUsize,Ordering}};static N:AtomicUsize=AtomicUsize::new(0);struct Node{{child:Option<Box<Node>>}}impl Drop for Node{{fn drop(&mut self){{N.fetch_add(1,Ordering::SeqCst);}}}}fn make()->Option<Box<Node>>{{Some(Box::new(Node{{child:Some(Box::new(Node{{child:None}}))}}))}}fn main(){{{{{}}}assert_eq!(N.load(Ordering::SeqCst),2);}}",
        emitted.code
    );
    assert!(compile_source(&source, true).status.success());
}
#[test]
fn custody_checks_source_hash_type_lifetimes_and_copy_traits_together() {
    let interface = StructInterface {
        terminal_fields: BTreeSet::from([field(0)]),
        field_types: BTreeMap::from([(field(0), "Option<Box<i32>>".into())]),
        lifetimes: vec![],
        remove_copy_clone: true,
    };
    let terminal = finalize(&[transaction(0)]).unwrap();
    let ledger = BTreeSet::from([field(0)]);
    let mut observed = Observation {
        source_hash: [7; 32],
        field_types: interface.field_types.clone(),
        lifetimes: vec![],
        has_copy_clone: false,
    };
    assert_eq!(
        check_fields(&[], [7; 32], &interface, &terminal, &ledger, &observed),
        Ok(())
    );
    assert_eq!(
        check_fields(&[], [8; 32], &interface, &terminal, &ledger, &observed),
        Err(CustodyError::SourceHash)
    );
    observed.has_copy_clone = true;
    assert_eq!(
        check_fields(&[], [7; 32], &interface, &terminal, &ledger, &observed),
        Err(CustodyError::CopyClone)
    );
    observed.has_copy_clone = false;
    observed.lifetimes.push("orphan".into());
    assert_eq!(
        check_fields(&[], [7; 32], &interface, &terminal, &ledger, &observed),
        Err(CustodyError::Lifetimes)
    );
}

#[test]
fn custody_cannot_pair_old_raw_interface_with_new_live_transaction() {
    let fields = vec![Field {
        id: field(0),
        name: "p".into(),
        input_type: "*mut i32".into(),
        candidate: FieldForm::Owning {
            pointee: "i32".into(),
            optional: true,
        },
    }];
    let mut held = transaction(0);
    held.sites.clear();
    let interface = struct_interface(
        OwnerId(1),
        &fields,
        &BTreeSet::new(),
        &CopyContract::Absent,
        &[held.clone()],
        &finalize(&[held]).unwrap(),
    )
    .unwrap();
    let observed = Observation {
        source_hash: [7; 32],
        field_types: interface.field_types.clone(),
        lifetimes: vec![],
        has_copy_clone: false,
    };
    assert!(
        check_fields(
            &[],
            [7; 32],
            &interface,
            &finalize(&[transaction(0)]).unwrap(),
            &BTreeSet::from([field(0)]),
            &observed
        )
        .is_err()
    );
}

#[test]
fn qualified_builtin_clone_is_removed_with_copy() {
    let source = "#[derive(Copy, std::clone::Clone, Debug)] struct Holder { p: *mut i32 }";
    let at = source.find(" {").unwrap();
    let declaration = Declaration {
        owner: OwnerId(1),
        fields: BTreeMap::from([(field(0), captured(source, "*mut i32"))]),
        generics: GenericSite {
            span: CapturedSpan {
                lo: at,
                hi: at,
                text: String::new(),
            },
            parameters: vec![],
        },
        derives: vec![DeriveSite {
            span: captured(source, "#[derive(Copy, std::clone::Clone, Debug)]"),
            traits: vec![
                DeriveTrait::BuiltinCopy,
                DeriveTrait::BuiltinClone,
                DeriveTrait::Other("Debug".into()),
            ],
        }],
    };
    let interface = StructInterface {
        terminal_fields: BTreeSet::from([field(0)]),
        field_types: BTreeMap::from([(field(0), "Option<Box<i32>>".into())]),
        lifetimes: vec![],
        remove_copy_clone: true,
    };
    let output = render_declaration(source, &declaration, &interface).unwrap();
    assert!(output.starts_with("#[derive(Debug)]"), "{output}");
}

#[test]
fn custody_preserves_existing_and_introduced_lifetimes() {
    let fields = vec![Field {
        id: field(0),
        name: "p".into(),
        input_type: "*const &'a i32".into(),
        candidate: FieldForm::Borrow {
            pointee: "&'a i32".into(),
            mutable: false,
            optional: false,
        },
    }];
    let tx = vec![transaction(0)];
    let terminal = finalize(&tx).unwrap();
    let interface = struct_interface(
        OwnerId(1),
        &fields,
        &BTreeSet::from(["a".into()]),
        &CopyContract::Absent,
        &tx,
        &terminal,
    )
    .unwrap();
    let observed = Observation {
        source_hash: [7; 32],
        field_types: interface.field_types.clone(),
        lifetimes: vec!["__crat_f0".into(), "a".into()],
        has_copy_clone: false,
    };
    assert!(
        check_fields(
            &["a".into()],
            [7; 32],
            &interface,
            &terminal,
            &BTreeSet::from([field(0)]),
            &observed
        )
        .is_ok()
    );
}
