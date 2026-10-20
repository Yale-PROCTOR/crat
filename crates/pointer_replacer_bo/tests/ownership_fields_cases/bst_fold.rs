//! Relay 001: complete synthetic BST vocabulary, not a corpus translation or
//! native export decoder. The per-fold sets mimic report 024; global field
//! grants, site roles, P1'-E and close evidence are explicit fixture assumptions.
use ownership_fields::{boundary::*, field_uses::*, free_sites::*};

use super::*;

const NODE: OwnerId = OwnerId(10);
const NEW: OwnerId = OwnerId(11);
const INSERT: OwnerId = OwnerId(12);
const DELETE: OwnerId = OwnerId(13);
const MIN: OwnerId = OwnerId(14);
const DRIVER: OwnerId = OwnerId(15);
fn fld(index: u32) -> FieldClassId {
    FieldClassId {
        owner: NODE,
        field: index,
    }
}
fn at(owner: OwnerId, occurrence: u32) -> SiteId {
    SiteId { owner, occurrence }
}
fn evidence(owner: OwnerId, occurrence: u32, generation: u64) -> EvidenceKey {
    EvidenceKey {
        model: [11; 32],
        configuration: [12; 32],
        site: at(owner, occurrence),
        generation,
    }
}
fn owner_type() -> BoundaryType {
    BoundaryType::Owner(OwnerType {
        pointee: "Node".into(),
        optional: true,
    })
}
fn slot(owner: OwnerId, occurrence: u32, ty: BoundaryType) -> SignatureSlot {
    let key = evidence(owner, occurrence, 100);
    let borrowed = matches!(ty, BoundaryType::Borrow { .. });
    let scalar = matches!(ty, BoundaryType::Scalar(_));
    let mut g = grant(key);
    if borrowed {
        g.kind = Kind::Ref;
    }
    SignatureSlot {
        key,
        ty,
        grant: (!scalar).then_some(g),
        borrow_origin: borrowed.then_some(key),
    }
}
fn signature(owner: OwnerId) -> Signature {
    let scalar = |occurrence| slot(owner, occurrence, BoundaryType::Scalar("i32".into()));
    let borrow = BoundaryType::Borrow {
        pointee: "Node".into(),
        mutable: false,
        optional: true,
        lifetime: "tree".into(),
    };
    match owner {
        NEW => Signature {
            owner,
            parameters: vec![Parameter {
                index: 0,
                name: "key".into(),
                slot: scalar(1),
            }],
            result: slot(owner, 0, owner_type()),
        },
        MIN => Signature {
            owner,
            parameters: vec![Parameter {
                index: 0,
                name: "node".into(),
                slot: slot(owner, 1, borrow.clone()),
            }],
            result: slot(owner, 0, borrow),
        },
        INSERT | DELETE => Signature {
            owner,
            parameters: vec![
                Parameter {
                    index: 0,
                    name: "root".into(),
                    slot: slot(owner, 1, owner_type()),
                },
                Parameter {
                    index: 1,
                    name: "key".into(),
                    slot: scalar(2),
                },
            ],
            result: slot(owner, 0, owner_type()),
        },
        _ => unreachable!("synthetic function inventory"),
    }
}
fn header(owner: OwnerId, name: &str) -> String {
    let plan = plan_signature(&signature(owner)).unwrap();
    let generics = if plan.lifetimes.is_empty() {
        String::new()
    } else {
        format!(
            "<{}>",
            plan.lifetimes
                .iter()
                .map(|name| format!("'{name}"))
                .collect::<Vec<_>>()
                .join(", ")
        )
    };
    format!(
        "fn {name}{generics}({}) -> {}",
        plan.parameters.join(", "),
        plan.result
    )
}
fn returned(owner: OwnerId, expression: &str, borrow: bool) -> Result<String, BoundaryHold> {
    let sig = signature(owner);
    let source = if borrow {
        sig.parameters[0].slot.clone()
    } else {
        slot(owner, 90, owner_type())
    };
    let transport = Some((source.key, sig.result.key));
    plan_return(&ReturnEdge {
        source,
        result: sig.result,
        expression: expression.into(),
        take_optional_storage: false,
        exclusive_storage: false,
        transport,
    })
}

#[derive(Clone)]
struct FixtureGrants {
    /// Required fields of the sampled identity/member attempts, not a global scheme.
    insert_required: BTreeSet<FieldClassId>,
    delete_required: BTreeSet<FieldClassId>,
    global_fields: BTreeSet<FieldClassId>,
    caller_selected: bool,
}
fn fixture_grants() -> FixtureGrants {
    FixtureGrants {
        insert_required: BTreeSet::from([fld(1)]),
        delete_required: BTreeSet::from([fld(1), fld(2)]),
        global_fields: BTreeSet::from([fld(1), fld(2)]),
        caller_selected: true,
    }
}
#[derive(Debug, PartialEq, Eq)]
enum BuildHold {
    CallerHeld,
    GlobalFieldScheme,
    BorrowReturn(BoundaryHold),
}
struct Built {
    source: String,
    frees: BTreeMap<EvidenceKey, Emitted>,
    extra_closes: Vec<ClosePlan>,
}

fn field_code(
    interface: &StructInterface,
    owner: OwnerId,
    occurrence: u32,
    index: u32,
    operation: FieldOperation,
) -> String {
    let key = evidence(owner, occurrence, 100);
    let name = if index == 1 { "left" } else { "right" };
    let mutable = !matches!(operation, FieldOperation::ReadShared);
    plan_field_use(
        &FieldSite {
            field: fld(index),
            key,
            terminal_type: "Option<Box<Node>>".into(),
            form: FieldForm::Owning {
                pointee: "Node".into(),
                optional: true,
            },
            lifetime: None,
            place: format!(
                "root.{}().unwrap().{name}",
                if mutable { "as_mut" } else { "as_ref" }
            ),
            access: if mutable {
                StorageAccess::Exclusive
            } else {
                StorageAccess::Shared
            },
            operation,
            role_proof: Some(key),
            view_proof: Some(key),
            transfer_proof: Some(key),
        },
        interface,
    )
    .unwrap()
    .code
}

fn recursive_call(
    owner: OwnerId,
    occurrence: u32,
    field: &str,
    scalar: &str,
    hoist: bool,
) -> (String, String) {
    let target = signature(owner);
    let call_site = at(owner, occurrence);
    let actual = evidence(owner, occurrence + 1, 100);
    let scalar_actual = evidence(owner, occurrence + 2, 100);
    let contract = CallContract {
        site: call_site,
        required_targets: BTreeSet::from([owner]),
        targets: vec![target.clone()],
        arguments: vec![
            ArgumentEdge {
                call_site,
                index: 0,
                actual,
                formal: target.parameters[0].slot.key,
                expression: format!("root.as_mut().unwrap().{field}"),
                source_type: owner_type(),
                actual_grant: Some(grant(actual)),
                mode: PassingMode::TakeOptionalStorage,
                transport: Some((actual, target.parameters[0].slot.key)),
                borrow_proof: None,
                exclusive_storage: true,
                call_facts: Some(call_facts(actual)),
            },
            ArgumentEdge {
                call_site,
                index: 1,
                actual: scalar_actual,
                formal: target.parameters[1].slot.key,
                expression: scalar.into(),
                source_type: BoundaryType::Scalar("i32".into()),
                actual_grant: None,
                mode: PassingMode::Scalar,
                transport: Some((scalar_actual, target.parameters[1].slot.key)),
                borrow_proof: None,
                exclusive_storage: false,
                call_facts: None,
            },
        ],
    };
    if hoist {
        let witness = HoistWitness {
            call: call_site,
            read: scalar_actual,
            consume: actual,
            original_order: vec![actual.site, scalar_actual.site],
            scalar_effect_free_nontrapping: true,
            callee_commutes: true,
            commutes_with: BTreeSet::from([actual.site]),
            no_independent_protector: true,
        };
        let plan = plan_hoisted_call(&contract, &witness, &BTreeSet::new()).unwrap();
        (plan.binding, plan.call.arguments.join(", "))
    } else {
        (
            String::new(),
            plan_call(&contract).unwrap().arguments.join(", "),
        )
    }
}

fn build(grants: &FixtureGrants) -> Result<Built, BuildHold> {
    if !grants.caller_selected {
        return Err(BuildHold::CallerHeld);
    }
    // The complete Node declaration needs both fields independently. A local
    // MemberDecision.fields set is deliberately not used to fabricate this set.
    if grants.global_fields != BTreeSet::from([fld(1), fld(2)])
        || !grants.insert_required.is_subset(&grants.global_fields)
        || !grants.delete_required.is_subset(&grants.global_fields)
    {
        return Err(BuildHold::GlobalFieldScheme);
    }
    let fields: Vec<_> = [1, 2]
        .into_iter()
        .map(|index| Field {
            id: fld(index),
            name: if index == 1 { "left" } else { "right" }.into(),
            input_type: "*mut Node".into(),
            candidate: FieldForm::Owning {
                pointee: "Node".into(),
                optional: true,
            },
        })
        .collect();
    let transactions: Vec<_> = fields
        .iter()
        .map(|field| Transaction {
            id: ClassId::Field(field.id),
            prerequisites: BTreeSet::new(),
            sites: BTreeMap::from([(at(NODE, field.id.field), SiteState::Ready)]),
        })
        .collect();
    let interface = struct_interface(
        NODE,
        &fields,
        &BTreeSet::new(),
        &CopyContract::Removable {
            sites: BTreeSet::new(),
        },
        &transactions,
        &finalize(&transactions).unwrap(),
    )
    .unwrap();
    let input =
        "#[derive(Copy, Clone, Debug)] struct Node { key: i32, left: *mut Node, right: *mut Node }";
    let span = |lo| CapturedSpan {
        lo,
        hi: lo + "*mut Node".len(),
        text: "*mut Node".into(),
    };
    let generic = input.find(" {").unwrap();
    let declaration = Declaration {
        owner: NODE,
        fields: BTreeMap::from([
            (fld(1), span(input.find("*mut Node").unwrap())),
            (fld(2), span(input.rfind("*mut Node").unwrap())),
        ]),
        generics: GenericSite {
            span: CapturedSpan {
                lo: generic,
                hi: generic,
                text: String::new(),
            },
            parameters: vec![],
        },
        derives: vec![DeriveSite {
            span: captured(input, "#[derive(Copy, Clone, Debug)]"),
            traits: vec![
                DeriveTrait::BuiltinCopy,
                DeriveTrait::BuiltinClone,
                DeriveTrait::Other("Debug".into()),
            ],
        }],
    };
    let node = render_declaration(input, &declaration, &interface).unwrap();
    let allocation = evidence(NEW, 10, 100);
    let new_value = receiver(
        &admit_call(&grant(allocation), &call_facts(allocation)).unwrap(),
        "fresh",
        &OwnerType {
            pointee: "Node".into(),
            optional: true,
        },
        &OwnerInput::Construct {
            value: "Node { key, left: None, right: None }".into(),
            layout: Some(allocation),
            initialization: Some(allocation),
        },
    )
    .unwrap()
    .code;
    let new_return = returned(NEW, "fresh", false).unwrap();
    let insert_return = returned(INSERT, "root", false).unwrap();
    let delete_return = returned(DELETE, "root", false).unwrap();
    let child_return = returned(DELETE, "survivor", false).unwrap();
    let min_return = returned(MIN, "node", true).map_err(BuildHold::BorrowReturn)?;
    let (_, insert_left) = recursive_call(INSERT, 20, "left", "key", false);
    let (_, insert_right) = recursive_call(INSERT, 30, "right", "key", false);
    let (_, delete_left) = recursive_call(DELETE, 20, "left", "key", false);
    let (_, delete_right) = recursive_call(DELETE, 30, "right", "key", false);
    let (hoist, delete_successor) = recursive_call(DELETE, 40, "right", "temp_1.key", true);
    let left = field_code(&interface, DELETE, 61, 1, FieldOperation::ReadShared);
    let right = field_code(&interface, DELETE, 62, 2, FieldOperation::ReadShared);
    let take_left = field_code(&interface, DELETE, 63, 1, FieldOperation::Take);
    let take_right = field_code(&interface, DELETE, 64, 2, FieldOperation::Take);
    let sites: Vec<_> = [70, 71]
        .into_iter()
        .map(|occurrence| {
            let sink = evidence(DELETE, occurrence, 100);
            let owner = evidence(DELETE, 1, 100);
            FreeSite {
                sink,
                owner,
                expression: "root".into(),
                optional_storage: true,
                casts: vec![CastKind::PointerToVoid],
                exact_owner_relation: Some((owner, sink)),
                allocation_base: Some(sink),
                allocator_layout: Some(sink),
                grant: grant(sink),
                call: call_facts(sink),
            }
        })
        .collect();
    let frees = plan_frees(&sites.iter().map(|s| s.sink).collect(), &sites).unwrap();
    let free_left = &frees[&evidence(DELETE, 70, 100)].code;
    let free_right = &frees[&evidence(DELETE, 71, 100)].code;
    // All function-owned values move out or close at the two explicit sinks.
    // The synthetic driver intentionally leaves its final tree to one extra
    // close. Both normal/unwind paths are bounded by seven fresh allocations.
    let graph = BTreeMap::from([(
        NODE,
        DropShape::OwnedFields(vec![
            DropEdge {
                payload: NODE,
                optional: true,
            },
            DropEdge {
                payload: NODE,
                optional: true,
            },
        ]),
    )]);
    let extra_closes: Vec<_> = [CloseKind::ScopeExit, CloseKind::Unwind]
        .into_iter()
        .map(|kind| {
            let k = evidence(DRIVER, 90, 200);
            let depth = DepthWitness {
                kind,
                key: k,
                payload: NODE,
                graph_revision: [13; 32],
                graph: graph.clone(),
                maximum_depth: 7,
                admitted_depth: 7,
            };
            implicit_close(
                k,
                kind,
                NODE,
                &graph,
                [13; 32],
                Some(&depth),
                &proofs_for(k, kind),
            )
            .unwrap()
        })
        .collect();
    let source = format!(
        r#"
#![allow(non_snake_case,unused_mut,dead_code)]
{node}
{new_header} {{ {new_value} {new_return} }}
{insert_header} {{
    if root.is_none() {{ return newNode(key); }}
    if key < root.as_ref().unwrap().key {{ let child = insert({insert_left}); root.as_mut().unwrap().left = child; }}
    else if key > root.as_ref().unwrap().key {{ let child = insert({insert_right}); root.as_mut().unwrap().right = child; }}
    {insert_return}
}}
{min_header} {{
    while let Some(current) = node {{
        if current.left.is_none() {{ return Some(current); }}
        node = current.left.as_deref();
    }}
    {min_return}
}}
{delete_header} {{
    if root.is_none() {{ {delete_return} }}
    if key < root.as_ref().unwrap().key {{ let child = deleteNode({delete_left}); root.as_mut().unwrap().left = child; }}
    else if key > root.as_ref().unwrap().key {{ let child = deleteNode({delete_right}); root.as_mut().unwrap().right = child; }}
    else {{
        if {left}.is_none() {{ let survivor = {take_right}; /* source-free:deleteNode:70 */ {free_left} {child_return} }}
        if {right}.is_none() {{ let survivor = {take_left}; /* source-free:deleteNode:71 */ {free_right} {child_return} }}
        let temp_1 = minValueNode({right}).unwrap();
        {hoist}
        root.as_mut().unwrap().key = __crat_scalar;
        let child = deleteNode({delete_successor}); root.as_mut().unwrap().right = child;
    }}
    {delete_return}
}}
fn values(node: Option<&Node>, out: &mut Vec<i32>) {{ if let Some(node)=node {{ values(node.left.as_deref(),out); out.push(node.key); values(node.right.as_deref(),out); }} }}
fn main() {{
    let mut tree = None;
    for key in [8,3,10,1,6,4,7] {{ tree = insert(tree,key); }}
    assert_eq!(minValueNode(tree.as_deref()).unwrap().key,1);
    tree=deleteNode(tree,8); tree=deleteNode(tree,1); tree=deleteNode(tree,3); tree=deleteNode(tree,99);
    let mut got=Vec::new(); values(tree.as_deref(),&mut got); assert_eq!(got,[4,6,7,10]);
    // waiver-drop(scope-exit); the bounded fixture's unwind counterpart is in its receipt.
}}
"#,
        new_header = header(NEW, "newNode"),
        insert_header = header(INSERT, "insert"),
        min_header = header(MIN, "minValueNode"),
        delete_header = header(DELETE, "deleteNode")
    );
    Ok(Built {
        source,
        frees,
        extra_closes,
    })
}

#[test]
fn relay001_bst_four_functions_compile_from_explicit_synthetic_grants() {
    let built = build(&fixture_grants()).expect("four-function synthetic emission");
    assert_eq!(built.frees.len(), 2);
    assert!(
        built
            .frees
            .values()
            .all(|f| f.receipt == "c-free-site-drop")
    );
    assert_eq!(
        built
            .extra_closes
            .iter()
            .map(ClosePlan::receipt)
            .collect::<Vec<_>>(),
        ["waiver-drop(scope-exit)", "waiver-drop(unwind)"]
    );
    for occurrence in [70, 71] {
        let emitted = &built.frees[&evidence(DELETE, occurrence, 100)];
        let marker = format!("/* source-free:deleteNode:{occurrence} */ {}", emitted.code);
        assert_eq!(
            built.source.matches(&marker).count(),
            1,
            "source free lost its exact expansion"
        );
    }
    assert_eq!(built.source.matches("drop((root).take());").count(), 2);
    assert!(!built.source.contains("*mut ") && !built.source.contains("*const "));
    let result = compile_source(&built.source, true);
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    if let Ok(directory) = std::env::var("CRAT_OWNERSHIP_FIXTURE_OUTPUT") {
        std::fs::write(
            std::path::Path::new(&directory).join("synthetic-bst.rs"),
            &built.source,
        )
        .unwrap();
        let mut receipts =
            String::from("function\toccurrence\tkind\tsource_generation\temission\n");
        for (key, free) in &built.frees {
            receipts.push_str(&format!(
                "deleteNode\t{}\t{}\t{}\t{}\n",
                key.site.occurrence, free.receipt, key.generation, free.code
            ));
        }
        for close in &built.extra_closes {
            receipts.push_str(&format!(
                "synthetic-driver\t90\t{}\t200\tordinary bounded cleanup\n",
                close.receipt()
            ));
        }
        std::fs::write(
            std::path::Path::new(&directory).join("synthetic-bst-receipts.tsv"),
            receipts,
        )
        .unwrap();
    }
}
#[test]
fn relay001_held_caller_and_missing_global_scheme_remain_typed_holds() {
    let mut facts = fixture_grants();
    facts.caller_selected = false;
    assert_eq!(build(&facts).err(), Some(BuildHold::CallerHeld));
    facts.caller_selected = true;
    facts.global_fields = facts.insert_required.clone();
    assert_eq!(build(&facts).err(), Some(BuildHold::GlobalFieldScheme));
}

#[test]
fn relay001_lending_return_cannot_take_ownership_or_invent_an_origin() {
    let sig = signature(MIN);
    let mut edge = ReturnEdge {
        source: sig.parameters[0].slot.clone(),
        result: sig.result,
        expression: "node".into(),
        take_optional_storage: false,
        exclusive_storage: true,
        transport: Some((sig.parameters[0].slot.key, evidence(MIN, 0, 100))),
    };
    assert!(plan_return(&edge).is_ok());
    edge.take_optional_storage = true;
    assert_eq!(plan_return(&edge), Err(BoundaryHold::Type));
    edge.take_optional_storage = false;
    edge.result.borrow_origin = None;
    assert_eq!(plan_return(&edge), Err(BoundaryHold::BorrowOrigin));
}
