//! R288 owned-child source identities. These fixtures are never executed.
use super::{
    graph_tests::with_facts,
    matched::{MatchedTransport, TerminalTarget},
    transport::CandidateGraph,
};

pub(super) const CODE: &str = r#"
unsafe extern "C"{fn malloc(n:usize)->*mut core::ffi::c_void;fn free(p:*mut core::ffi::c_void);}
pub struct Node{child:*mut Node}
pub struct Holder{ptr:*mut Node}
pub unsafe fn detach(node:*mut Node)->*mut Node {
 let child=(*node).child;
 free(node as *mut core::ffi::c_void);
 child
}
pub unsafe fn run(){
 let leaf=malloc(core::mem::size_of::<Node>()) as *mut Node;
 (*leaf).child=0 as *mut Node;
 let parent=malloc(core::mem::size_of::<Node>()) as *mut Node;
 (*parent).child=leaf;
 let holder=malloc(core::mem::size_of::<Holder>()) as *mut Holder;
 (*holder).ptr=parent;
 let result=detach((*holder).ptr);
 (*holder).ptr=0 as *mut Node;
 free(result as *mut core::ffi::c_void);
 free(holder as *mut core::ffi::c_void);
}
"#;

#[test]
fn oc01_native_owned_child_capture_preserves_sources_widths_and_pending_activation() {
    with_facts(CODE, |facts| {
        let graph = CandidateGraph::build(facts);
        assert_eq!(graph.sources.len(), 3);
        assert_eq!(graph.sinks.len(), 3);
        let [declaration] = facts.fold_declarations.as_deref().unwrap() else {
            panic!("one exact folded detach call")
        };
        let field = "Node::field0@d0".to_owned();
        assert_eq!(
            super::fold_call::certify(facts, &declaration.call, 0, &Default::default()),
            Err(super::fold_call::Error::FieldScheme(field.clone()))
        );
        let proof =
            super::fold_call::certify(facts, &declaration.call, 0, &[field].into_iter().collect())
                .expect("conditional internal taking/freeing/returned-child certificate");
        assert_eq!(proof.internal.input_components.len(), 2);
        assert_eq!(proof.descendants.len(), 1);
        let conditional = MatchedTransport::build_with_conditional_folds(
            facts,
            &[(declaration.guard, proof.clone())],
        )
        .unwrap();
        let routes: Vec<_> = graph
            .sources
            .iter()
            .map(|source| {
                let meets = conditional.meets_for(source.node);
                let frees: Vec<_> = meets
                    .iter()
                    .filter(|m| matches!(m.terminal.target, TerminalTarget::Free(_)))
                    .cloned()
                    .collect();
                serde_json::json!({"source":source,"meets":meets,"frees":frees})
            })
            .collect();
        let snapshot = super::snapshot::Snapshot::capture(facts, 0).unwrap();
        assert!(
            snapshot.fold_callers.as_ref().unwrap()[0].outcome.is_err(),
            "used-child activation remains held"
        );
        eprintln!(
            "OC01_CAPTURE {}",
            serde_json::json!({"snapshot":snapshot,"conditional_fold":proof,"source_routes":routes,"conditional_transport":serde_json::from_slice::<serde_json::Value>(&conditional.encode_json().unwrap()).unwrap()})
        );
    });
}

#[test]
fn oc02_detach_transports_each_exact_allocation_to_its_original_free() {
    use std::collections::BTreeSet;

    use super::{
        super::ownership_occurrence::Availability::Present,
        facts::EquationId,
        field_support::StoredValue,
        matched::SourceLineage,
        transport::{Node, Rule},
        value_origins::{OriginAtom, ValueOrigins},
    };
    with_facts(CODE, |facts| {
        let declaration = &facts.fold_declarations.as_ref().unwrap()[0];
        let fold = super::fold_call::certify(
            facts,
            &declaration.call,
            0,
            &["Node::field0@d0".to_owned()].into_iter().collect(),
        )
        .unwrap();
        let graph = CandidateGraph::build(facts);
        let membership = super::fold_subtree::certify(facts, declaration, &fold).unwrap();
        let transport = MatchedTransport::build_with_subtree_folds(
            facts,
            &[(declaration.guard, fold.clone())],
            &[membership.clone()],
        )
        .unwrap();
        let origins = ValueOrigins::build(facts);
        let fresh = |node| {
            let atoms = origins.at(node);
            assert!(
                atoms
                    .iter()
                    .all(|a| matches!(a, OriginAtom::Fresh(_) | OriginAtom::Null)),
                "closed fixture origin {node:?}: {atoms:?}"
            );
            let values: BTreeSet<_> = atoms
                .iter()
                .filter_map(|a| {
                    if let OriginAtom::Fresh(key) = a {
                        Some(*key)
                    } else {
                        None
                    }
                })
                .collect();
            assert_eq!(values.len(), 1);
            *values.iter().next().unwrap()
        };
        let transfer = |field: &str| {
            let stores: Vec<_> = facts
                .field_support_inputs
                .stores
                .iter()
                .filter(|s| s.site.field_key == field && matches!(s.value, StoredValue::Value(_)))
                .collect();
            let [store] = stores.as_slice() else { panic!("one exact non-null store") };
            let equations:Vec<_>=facts.equations.iter().filter(|e|e.point.function.as_ref()==Some(&store.site.function) && e.point.block==Some(store.site.block) && e.point.statement==Some(store.site.statement) && e.operation=="equal" && e.transfer.as_ref().is_some_and(|t|matches!(&t.destination,Present(d) if d.projection==store.site.place.projection && d.local==store.site.place.local))).collect();
            let [equation] = equations.as_slice() else { panic!("one exact native moving store") };
            assert!(equation.transfer.as_ref().unwrap().by_move);
            (*equation).clone()
        };
        let child_store = transfer("Node::field0@d0");
        let pack_store = transfer("Holder::field0@d0");
        let node = |var| Node {
            construction: fold.call.construction,
            var,
        };
        let child = child_store.transfer.as_ref().unwrap();
        let pack = pack_store.transfer.as_ref().unwrap();
        let leaf_source = fresh(node(child.source_use));
        let base_source = |consume| {
            let row = facts
                .consumes
                .iter()
                .find(|c| c.ordinal == consume && c.point.construction == fold.call.construction)
                .unwrap();
            let Present(base) = &row.base else { panic!("native full base") };
            fresh(node(base.use_start))
        };
        let Present(child_destination) = &child.destination else { panic!("child destination") };
        let parent_source = base_source(child_destination.consume);
        assert_eq!(fresh(node(pack.source_use)), parent_source);
        let Present(pack_destination) = &pack.destination else { panic!("pack destination") };
        let holder_source = base_source(pack_destination.consume);
        assert_eq!(
            BTreeSet::from([leaf_source, parent_source, holder_source]).len(),
            3
        );
        let Present(pack_source) = &pack.source else { panic!("wide source") };
        let wide = facts
            .consumes
            .iter()
            .find(|c| {
                c.ordinal == pack_source.consume && c.point.construction == fold.call.construction
            })
            .unwrap();
        let (Present(base), Present(paths)) = (&wide.base, &wide.pointer_paths) else {
            panic!("native wide source paths")
        };
        let offset = paths
            .iter()
            .position(|p| p == &fold.descendants[0].path)
            .unwrap();
        let member = node(base.use_start + u32::try_from(offset).unwrap());
        assert_eq!(
            fresh(member),
            leaf_source,
            "the existing pre-narrow child component carries the leaf source"
        );
        assert_eq!(base.use_end - base.use_start, 2);
        assert_eq!(pack.destination_def, fold.actual_before.var);
        let parent_free = graph
            .sinks
            .iter()
            .find(|s| s.endpoint.function == fold.call.callee)
            .unwrap()
            .equation;
        let mut receiver_reaches = BTreeSet::from([fold.receiver]);
        loop {
            let before = receiver_reaches.len();
            for edge in &graph.edges {
                if edge.guard.is_none()
                    && matches!(edge.rule, Rule::Copy | Rule::Frame)
                    && receiver_reaches.contains(&edge.from)
                {
                    receiver_reaches.insert(edge.to);
                }
            }
            if receiver_reaches.len() == before {
                break;
            }
        }
        let child_frees: Vec<_> = graph
            .sinks
            .iter()
            .filter(|s| {
                s.endpoint.function == fold.call.caller && receiver_reaches.contains(&s.node)
            })
            .collect();
        let [child_free] = child_frees.as_slice() else {
            panic!("receiver reaches one original caller free")
        };
        let holder_frees: Vec<_> = graph
            .sinks
            .iter()
            .filter(|s| {
                s.endpoint.function == fold.call.caller && s.equation != child_free.equation
            })
            .collect();
        let [holder_free] = holder_frees.as_slice() else {
            panic!("remaining original container free")
        };
        let expected: [(&str, EquationId, EquationId, SourceLineage); 3] = [
            (
                "parent",
                parent_source,
                parent_free,
                SourceLineage::Exact(vec![fold.call.clone()]),
            ),
            (
                "holder",
                holder_source,
                holder_free.equation,
                SourceLineage::Exact(vec![]),
            ),
            (
                "leaf",
                leaf_source,
                child_free.equation,
                SourceLineage::Exact(vec![]),
            ),
        ];
        for (role, source, free, lineage) in expected {
            let source_node = graph
                .sources
                .iter()
                .find(|s| s.equation == source)
                .unwrap()
                .node;
            let meets = transport.meets_for(source_node);
            let frees: Vec<_> = meets
                .iter()
                .filter(|m| {
                    m.source.endpoint == source
                        && matches!(m.terminal.target, TerminalTarget::Free(_))
                })
                .collect();
            assert_eq!(
                frees.len(),
                1,
                "{role} allocation needs its exact original free; member {member:?}, meets {meets:?}"
            );
            assert_eq!(frees[0].terminal.target, TerminalTarget::Free(free));
            assert_eq!(frees[0].terminal.lineage, lineage);
            if role != "holder" {
                assert_eq!(frees[0].guards.get(&declaration.guard), Some(&true));
            }
            if role == "leaf" {
                for (key, value) in &membership.requirements.guards {
                    assert_eq!(
                        frees[0].guards.get(key),
                        Some(value),
                        "member requirement {key:?} is part of the returned leaf route"
                    );
                }
            }
        }
    });
}

#[test]
fn oc02_member_certificate_binds_real_component_and_exact_source_instances() {
    with_facts(CODE, |facts| {
        let declaration = &facts.fold_declarations.as_ref().unwrap()[0];
        let fold = super::fold_call::certify(
            facts,
            &declaration.call,
            0,
            &["Node::field0@d0".to_owned()].into_iter().collect(),
        )
        .unwrap();
        let member = super::fold_subtree::certify(facts, declaration, &fold)
            .expect("owned child membership before narrowing");
        assert_eq!(member.declaration, *declaration);
        assert_eq!(member.fold, fold);
        assert_ne!(member.parent, member.member);
        assert_eq!(member.field, "Node::field0@d0");
        assert_eq!(member.cell, fold.actual_before);
        assert_eq!(member.formal.var, fold.descendants[0].formal_use);
        assert!(member.requirements.owning.contains(&member.member_before));
        assert!(member.requirements.zero.contains(&member.member_after));
        assert!(member.requirements.kind_keys.contains(&member.field));
        let snapshot = super::snapshot::Snapshot::capture(facts, 0).unwrap();
        assert_eq!(
            super::fold_subtree::certify_metadata(
                &snapshot.metadata.facts(),
                declaration,
                &fold,
                &snapshot.metadata.guard_aliases.iter().copied().collect(),
                &snapshot.metadata.slot_keys.iter().cloned().collect()
            ),
            Ok(member)
        );
    });
}

#[test]
fn oc02_member_rejects_wrong_declaration_and_field_premises() {
    with_facts(CODE, |facts| {
        use super::fold_subtree::Hold;
        let declaration = &facts.fold_declarations.as_ref().unwrap()[0];
        let fold = super::fold_call::certify(
            facts,
            &declaration.call,
            0,
            &["Node::field0@d0".to_owned()].into_iter().collect(),
        )
        .unwrap();
        let mut wrong = declaration.clone();
        wrong.boundary = usize::MAX;
        assert_eq!(
            super::fold_subtree::certify(facts, &wrong, &fold),
            Err(Hold::Declaration)
        );
        let mut wrong = fold.clone();
        wrong.descendants[0].premise = super::fold_call::FieldPremise::Unused {
            field: "Node::field0@d0".into(),
        };
        assert_eq!(
            super::fold_subtree::certify(facts, declaration, &wrong),
            Err(Hold::FieldScheme)
        );
        let mut wrong = fold;
        wrong.descendants[0].path.clear();
        assert_eq!(
            super::fold_subtree::certify(facts, declaration, &wrong),
            Err(Hold::Call)
        );
    });
}

#[test]
fn oc02_member_rejects_self_containment_and_competing_leaf_free() {
    use super::fold_subtree::Hold;
    for (code, expected) in [
        (
            CODE.replace("(*parent).child=leaf;", "(*parent).child=parent;"),
            Hold::SourceIdentity,
        ),
        (
            CODE.replace(
                " let result=detach((*holder).ptr);",
                " free(leaf as *mut core::ffi::c_void);\n let result=detach((*holder).ptr);",
            ),
            Hold::PartnerFree,
        ),
    ] {
        assert_ne!(code, CODE);
        with_facts(&code, move |facts| {
            let declaration = &facts.fold_declarations.as_ref().unwrap()[0];
            let fold = super::fold_call::certify(
                facts,
                &declaration.call,
                0,
                &["Node::field0@d0".to_owned()].into_iter().collect(),
            )
            .unwrap();
            assert_eq!(
                super::fold_subtree::certify(facts, declaration, &fold),
                Err(expected)
            );
        });
    }
}

#[test]
fn oc02_member_rejects_intervening_store_and_reordered_cell_reset() {
    use super::fold_subtree::Hold;
    for (code, expected) in [
        (
            CODE.replace(
                " let result=detach((*holder).ptr);",
                " (*parent).child=0 as *mut Node;\n let result=detach((*holder).ptr);",
            ),
            Hold::StoreInventory,
        ),
        (
            CODE.replace(" (*holder).ptr=0 as *mut Node;\n", "")
                .replace(
                    " let result=detach((*holder).ptr);",
                    " (*holder).ptr=0 as *mut Node;\n let result=detach((*holder).ptr);",
                ),
            Hold::MemberPath,
        ),
    ] {
        assert_ne!(code, CODE);
        with_facts(&code, move |facts| {
            let declaration = &facts.fold_declarations.as_ref().unwrap()[0];
            let fold = super::fold_call::certify(
                facts,
                &declaration.call,
                0,
                &["Node::field0@d0".to_owned()].into_iter().collect(),
            )
            .unwrap();
            assert_eq!(
                super::fold_subtree::certify(facts, declaration, &fold),
                Err(expected)
            );
        });
    }
}

#[test]
fn oc03_member_transport_rebuilds_and_requires_explicit_membership() {
    with_facts(CODE, |facts| {
        let declaration = &facts.fold_declarations.as_ref().unwrap()[0];
        let fold = super::fold_call::certify(
            facts,
            &declaration.call,
            0,
            &["Node::field0@d0".to_owned()].into_iter().collect(),
        )
        .unwrap();
        let member = super::fold_subtree::certify(facts, declaration, &fold).unwrap();
        let folds = vec![(declaration.guard, fold.clone())];
        let transport =
            MatchedTransport::build_with_subtree_folds(facts, &folds, &[member.clone()]).unwrap();
        let graph = CandidateGraph::build(facts);
        let source = graph
            .sources
            .iter()
            .find(|s| s.equation == member.member.endpoint)
            .unwrap();
        let absent = MatchedTransport::build_with_subtree_folds(facts, &folds, &[]).unwrap();
        assert!(
            !absent
                .meets_for(source.node)
                .iter()
                .any(|m| matches!(m.terminal.target, TerminalTarget::Free(_)))
        );
        let meets = transport.meets_for(source.node);
        let free = meets
            .iter()
            .find(|m| matches!(m.terminal.target, TerminalTarget::Free(_)))
            .unwrap();
        let returned = fold.internal.packed_return.as_ref().unwrap().root;
        let output = meets
            .iter()
            .find(|m| matches!(m.terminal.target,TerminalTarget::Output{node,..} if node==returned))
            .unwrap();
        assert!(
            transport.forward_return(facts, output, free).is_none(),
            "ordinary scalar forwarding cannot authenticate a folded member"
        );
        let snapshot = super::snapshot::Snapshot::capture(facts, 0).unwrap();
        let rebuilt = MatchedTransport::build_with_subtree_folds_metadata(
            &snapshot.metadata.facts(),
            &folds,
            &[member],
            &snapshot.metadata.guard_aliases.iter().copied().collect(),
            &snapshot.metadata.slot_keys.iter().cloned().collect(),
        )
        .unwrap();
        let bytes = transport.encode_json().unwrap();
        assert_eq!(rebuilt.encode_json().unwrap(), bytes);
        assert_eq!(MatchedTransport::decode_json(&bytes).unwrap(), transport);
        assert!(
            String::from_utf8(bytes).unwrap().contains("folded_member"),
            "typed witness is exported"
        );
    });
}

#[test]
fn oc03_member_transport_rejects_forged_or_duplicate_membership() {
    with_facts(CODE, |facts| {
        let declaration = &facts.fold_declarations.as_ref().unwrap()[0];
        let fold = super::fold_call::certify(
            facts,
            &declaration.call,
            0,
            &["Node::field0@d0".to_owned()].into_iter().collect(),
        )
        .unwrap();
        let member = super::fold_subtree::certify(facts, declaration, &fold).unwrap();
        let folds = vec![(declaration.guard, fold)];
        for mode in 0..6 {
            let mut changed = member.clone();
            match mode {
                0 => changed.parent = changed.member.clone(),
                1 => changed.member = changed.parent.clone(),
                2 => changed.narrowing_transfer.ordinal += 1,
                3 => changed.cell.var += 1,
                4 => changed.requirements.zero.clear(),
                _ => changed.formal.var += 1,
            }
            assert_eq!(
                MatchedTransport::build_with_subtree_folds(facts, &folds, &[changed]),
                Err("folded member differs from current metadata".into()),
                "member mutation {mode}"
            );
        }
        let mut wrong_call = member.clone();
        wrong_call.declaration.guard.ordinal = usize::MAX;
        assert_eq!(
            MatchedTransport::build_with_subtree_folds(facts, &folds, &[wrong_call]),
            Err("folded member has no matching conditional fold".into())
        );
        assert_eq!(
            MatchedTransport::build_with_subtree_folds(facts, &folds, &[member.clone(), member]),
            Err("duplicate folded member".into())
        );
    });
}

/// R304-9 and R304-10 fixtures. Each differs from `CODE` by exactly one
/// construct, so a rejection can be attributed to that construct alone.
///
/// `ALIAS_STORE_CODE` writes the member's own child cell through a punned
/// pointer, which produces no named field store. `AGGREGATE_WRITE_CODE` writes
/// the whole struct through a literal. `COPY_DERIVE_CODE` carries the
/// substrate's own derived `Copy`/`Clone` impl and never calls it;
/// `DERIVED_CLONE_CALL_CODE` calls it.
const COPY_DERIVE_CODE: &str = r#"
unsafe extern "C"{fn malloc(n:usize)->*mut core::ffi::c_void;fn free(p:*mut core::ffi::c_void);}
pub struct Node{child:*mut Node}
#[automatically_derived]
impl ::core::marker::Copy for Node {}
#[automatically_derived]
impl ::core::clone::Clone for Node {
 #[inline]
 fn clone(&self)->Node{*self}
}
pub struct Holder{ptr:*mut Node}
pub unsafe fn detach(node:*mut Node)->*mut Node {
 let child=(*node).child;
 free(node as *mut core::ffi::c_void);
 child
}
pub unsafe fn run(){
 let leaf=malloc(core::mem::size_of::<Node>()) as *mut Node;
 (*leaf).child=0 as *mut Node;
 let parent=malloc(core::mem::size_of::<Node>()) as *mut Node;
 (*parent).child=leaf;
 let holder=malloc(core::mem::size_of::<Holder>()) as *mut Holder;
 (*holder).ptr=parent;
 let result=detach((*holder).ptr);
 (*holder).ptr=0 as *mut Node;
 free(result as *mut core::ffi::c_void);
 free(holder as *mut core::ffi::c_void);
}
"#;
const DERIVED_CLONE_CALL_CODE: &str = r#"
unsafe extern "C"{fn malloc(n:usize)->*mut core::ffi::c_void;fn free(p:*mut core::ffi::c_void);}
pub struct Node{child:*mut Node}
#[automatically_derived]
impl ::core::marker::Copy for Node {}
#[automatically_derived]
impl ::core::clone::Clone for Node {
 #[inline]
 fn clone(&self)->Node{*self}
}
pub struct Holder{ptr:*mut Node}
pub unsafe fn detach(node:*mut Node)->*mut Node {
 let child=(*node).child;
 free(node as *mut core::ffi::c_void);
 child
}
pub unsafe fn run(){
 let leaf=malloc(core::mem::size_of::<Node>()) as *mut Node;
 (*leaf).child=0 as *mut Node;
 let parent=malloc(core::mem::size_of::<Node>()) as *mut Node;
 (*parent).child=leaf;
 let dup=(*parent).clone();
 let holder=malloc(core::mem::size_of::<Holder>()) as *mut Holder;
 (*holder).ptr=parent;
 let result=detach((*holder).ptr);
 (*holder).ptr=0 as *mut Node;
 free(result as *mut core::ffi::c_void);
 free(holder as *mut core::ffi::c_void);
}
"#;
const ALIAS_STORE_CODE: &str = r#"
unsafe extern "C"{fn malloc(n:usize)->*mut core::ffi::c_void;fn free(p:*mut core::ffi::c_void);}
pub struct Node{child:*mut Node}
pub struct Holder{ptr:*mut Node}
pub unsafe fn detach(node:*mut Node)->*mut Node {
 let child=(*node).child;
 free(node as *mut core::ffi::c_void);
 child
}
pub unsafe fn run(){
 let leaf=malloc(core::mem::size_of::<Node>()) as *mut Node;
 (*leaf).child=0 as *mut Node;
 let parent=malloc(core::mem::size_of::<Node>()) as *mut Node;
 (*parent).child=leaf;
 let alias=leaf as *mut *mut Node;
 *alias=parent;
 let holder=malloc(core::mem::size_of::<Holder>()) as *mut Holder;
 (*holder).ptr=parent;
 let result=detach((*holder).ptr);
 (*holder).ptr=0 as *mut Node;
 free(result as *mut core::ffi::c_void);
 free(holder as *mut core::ffi::c_void);
}
"#;
const AGGREGATE_WRITE_CODE: &str = r#"
unsafe extern "C"{fn malloc(n:usize)->*mut core::ffi::c_void;fn free(p:*mut core::ffi::c_void);}
pub struct Node{child:*mut Node}
pub struct Holder{ptr:*mut Node}
pub unsafe fn detach(node:*mut Node)->*mut Node {
 let child=(*node).child;
 free(node as *mut core::ffi::c_void);
 child
}
pub unsafe fn run(){
 let leaf=malloc(core::mem::size_of::<Node>()) as *mut Node;
 (*leaf).child=0 as *mut Node;
 let parent=malloc(core::mem::size_of::<Node>()) as *mut Node;
 (*parent).child=leaf;
 *leaf=Node{child:parent};
 let holder=malloc(core::mem::size_of::<Holder>()) as *mut Holder;
 (*holder).ptr=parent;
 let result=detach((*holder).ptr);
 (*holder).ptr=0 as *mut Node;
 free(result as *mut core::ffi::c_void);
 free(holder as *mut core::ffi::c_void);
}
"#;

fn fold_of(
    facts: &super::facts::Facts,
) -> Result<super::fold_call::Proof, super::fold_call::Error> {
    let declaration = &facts.fold_declarations.as_ref().unwrap()[0];
    super::fold_call::certify(
        facts,
        &declaration.call,
        0,
        &["Node::field0@d0".to_owned()].into_iter().collect(),
    )
}

/// R336-4 positive: bst's `newNode` shape. A pointer-free field written through
/// a base cast from what an allocator returned.
const SCALAR_FIELD_CODE: &str = r#"
unsafe extern "C"{fn malloc(n:usize)->*mut core::ffi::c_void;}
pub struct Node{key:i32,child:*mut Node}
pub unsafe fn make(key:i32)->*mut Node{
 let temp=malloc(core::mem::size_of::<Node>()) as *mut Node;
 (*temp).key=key;
 (*temp).child=0 as *mut Node;
 temp
}
"#;

/// R336-4 N1: the base is cast from a pointer to a DIFFERENT struct, so the
/// field projection is type-directed on a type the base may not really have.
/// This is the prefix pun finding A exists for and stays denied.
const N1_CODE: &str = r#"
unsafe extern "C"{fn malloc(n:usize)->*mut core::ffi::c_void;}
pub struct Node{child:*mut Node}
pub struct Other{x:i32}
pub unsafe fn run(){
 let p=malloc(core::mem::size_of::<Node>()) as *mut Node;
 (*p).child=0 as *mut Node;
 let q=p as *mut Other;
 (*q).x=0;
}
"#;

/// R336-4 N2: the written field carries a pointer but is not a REGISTERED raw
/// pointer field, so `field()` does not resolve it and the narrowing is what
/// must refuse it. A raw-pointer field of a local struct is always registered
/// and never reaches here, which is why this is a function pointer.
const N2_CODE: &str = r#"
unsafe extern "C"{fn malloc(n:usize)->*mut core::ffi::c_void;}
pub struct Node{hook:fn(),child:*mut Node}
pub fn noop(){}
pub unsafe fn run(){
 let p=malloc(core::mem::size_of::<Node>()) as *mut Node;
 (*p).child=0 as *mut Node;
 (*p).hook=noop;
}
"#;

/// R336-4 N3: a pointer-free field written through a base made from an integer.
const N3_CODE: &str = r#"
pub struct Node{key:i32,child:*mut Node}
pub unsafe fn run(address:usize){
 let p=address as *mut Node;
 (*p).key=0;
}
"#;

/// R337-2(b) control: the caller gate admits a READ-ONLY intrinsic, and nothing
/// else from the library. `offset` moves a pointer and must keep holding.
const OFFSET_CALLER_CODE: &str = r#"
unsafe extern "C"{fn malloc(n:usize)->*mut core::ffi::c_void;fn free(p:*mut core::ffi::c_void);}
pub struct Node{child:*mut Node}
pub struct Holder{ptr:*mut Node}
pub unsafe fn identity(node:*mut Node)->*mut Node{node}
pub unsafe fn run(){
 let node=malloc(core::mem::size_of::<Node>()) as *mut Node;
 (*node).child=0 as *mut Node;
 let holder=malloc(core::mem::size_of::<Holder>()) as *mut Holder;
 (*holder).ptr=node;
 let moved=node.offset(1);
 (*holder).ptr=moved;
 let result=identity((*holder).ptr);
 (*holder).ptr=0 as *mut Node;
 free(result as *mut core::ffi::c_void);
 free(holder as *mut core::ffi::c_void);
}
"#;

#[test]
fn r337_2_the_caller_gate_admits_a_read_only_intrinsic_and_not_offset() {
    super::graph_tests::with_facts(OFFSET_CALLER_CODE, |facts| {
        let declarations = facts.fold_declarations.as_deref().unwrap_or_default();
        let [declaration, ..] = declarations else {
            panic!("one fold declaration: {declarations:?}")
        };
        let refused = super::fold_caller::unsupported_occurrences(
            facts,
            &declaration.call,
            &super::matched::guard_aliases(&facts.guards),
        )
        .unwrap_or_default();
        assert!(
            refused.iter().any(|occurrence| matches!(
                &occurrence.callee,
                Some(super::super::origin_evidence::SourceCallee::RustLibrary(name))
                    if name.contains("offset")
            )),
            "a pointer-moving library call is not a read-only intrinsic: {:?}",
            refused
                .iter()
                .map(|occurrence| occurrence.callee.clone())
                .collect::<Vec<_>>()
        );
    });
}

#[test]
fn r336_4_a_pointer_free_field_write_denies_nothing_and_is_still_counted() {
    with_facts(SCALAR_FIELD_CODE, |facts| {
        let [row] = facts.field_support_inputs.unsupported.as_slice() else {
            panic!(
                "one scalar field write: {:?}",
                facts.field_support_inputs.unsupported
            )
        };
        assert_eq!(row.function, "make");
        assert_eq!(row.reason, "scalar-field-write");
        assert!(
            row.field_keys.is_empty(),
            "a type-directed write to a pointer-free field may alias no pointer field"
        );
    });
}

#[test]
fn r336_4_the_three_prefix_and_field_puns_stay_denied() {
    for (name, code, reason) in [
        (
            "N1 base cast from another struct",
            N1_CODE,
            "punned-destination",
        ),
        (
            "N2 unregistered pointer field",
            N2_CODE,
            "punned-destination",
        ),
        (
            "N3 base made from an integer",
            N3_CODE,
            "punned-destination",
        ),
    ] {
        with_facts(code, move |facts| {
            let rows = &facts.field_support_inputs.unsupported;
            assert!(
                rows.iter()
                    .any(|row| row.reason == reason && !row.field_keys.is_empty()),
                "{name} must stay denied: {rows:?}"
            );
            assert!(
                rows.iter().all(|row| row.reason != "scalar-field-write"),
                "{name} must not narrow: {rows:?}"
            );
        });
    }
}

#[test]
fn r304_9_the_named_store_inventory_fails_closed_on_unresolved_destinations() {
    with_facts(CODE, |facts| {
        assert!(
            facts.field_support_inputs.unsupported.is_empty(),
            "every baseline store resolves to a named raw-pointer field"
        );
    });
    with_facts(ALIAS_STORE_CODE, |facts| {
        let [row] = facts.field_support_inputs.unsupported.as_slice() else {
            panic!(
                "one punned destination: {:?}",
                facts.field_support_inputs.unsupported
            )
        };
        assert_eq!(row.function, "run");
        assert_eq!(row.reason, "punned-destination");
        assert_eq!(
            row.field_keys,
            ["Holder::field0@d0".to_owned(), "Node::field0@d0".to_owned()],
            "a punned destination may alias every registered pointer field"
        );
    });
    with_facts(AGGREGATE_WRITE_CODE, |facts| {
        let [row] = facts.field_support_inputs.unsupported.as_slice() else {
            panic!(
                "one whole-struct destination: {:?}",
                facts.field_support_inputs.unsupported
            )
        };
        assert_eq!(row.reason, "whole-struct-write");
        assert_eq!(
            row.field_keys,
            ["Node::field0@d0".to_owned()],
            "a known struct pointee narrows the may-alias set to that struct"
        );
    });
}

#[test]
fn r304_9_an_unsupported_field_effect_holds_the_scheme_and_the_member() {
    use super::fold_call::Error;
    with_facts(ALIAS_STORE_CODE, |facts| {
        assert_eq!(
            fold_of(facts),
            Err(Error::FieldScheme("Node::field0@d0".to_owned())),
            "the punned write denies the owning field scheme"
        );
    });
    with_facts(AGGREGATE_WRITE_CODE, |facts| {
        assert_eq!(
            fold_of(facts),
            Err(Error::FieldScheme("Node::field0@d0".to_owned()))
        );
    });
}

#[test]
fn r304_9_membership_independently_refuses_an_affected_field() {
    with_facts(ALIAS_STORE_CODE, |facts| {
        // Build the fold against a copy with no recorded effect, so the scheme
        // gate is the only thing bypassed, then certify against the real facts.
        let mut clean = facts.clone();
        clean.field_support_inputs.unsupported.clear();
        let declaration = &clean.fold_declarations.as_ref().unwrap()[0].clone();
        let fold = super::fold_call::certify(
            &clean,
            &declaration.call,
            0,
            &["Node::field0@d0".to_owned()].into_iter().collect(),
        )
        .expect("the effect-free copy still folds");
        assert_eq!(
            super::fold_subtree::certify(facts, declaration, &fold),
            Err(super::fold_subtree::Hold::UnsupportedEffect),
            "membership does not rely on the scheme gate alone"
        );
    });
}

#[test]
fn r304_9_the_baseline_member_is_unaffected() {
    with_facts(CODE, |facts| {
        let declaration = &facts.fold_declarations.as_ref().unwrap()[0];
        let fold = fold_of(facts).expect("baseline fold");
        super::fold_subtree::certify(facts, declaration, &fold).expect("baseline membership");
    });
}

#[test]
fn r304_10_derived_impl_bodies_join_the_roster_with_their_role() {
    with_facts(CODE, |facts| {
        let coverage = facts.caller_coverage.as_ref().unwrap();
        assert!(coverage.derived_impl_bodies.is_empty());
        assert_eq!(
            super::caller_coverage::assess(facts),
            super::caller_coverage::Status::Complete
        );
    });
    with_facts(COPY_DERIVE_CODE, |facts| {
        let coverage = facts.caller_coverage.as_ref().unwrap();
        assert_eq!(
            coverage.derived_impl_bodies.iter().collect::<Vec<_>>(),
            ["<Node as std::clone::Clone>::clone"],
            "the derived body is admitted with its role, never filtered away"
        );
        assert!(
            coverage
                .compiler_bodies
                .iter()
                .all(|b| coverage.configured_functions.contains(b)
                    || coverage.derived_impl_bodies.contains(b)),
            "the roster accounts for every compiler body"
        );
        assert_eq!(
            super::caller_coverage::assess(facts),
            super::caller_coverage::Status::Complete
        );
    });
}

#[test]
fn r304_10_an_uncalled_derived_body_leaves_every_certificate_intact() {
    with_facts(COPY_DERIVE_CODE, |facts| {
        assert!(
            facts.field_support_inputs.unsupported.is_empty(),
            "a body that is never called records no effect"
        );
        let declaration = &facts.fold_declarations.as_ref().unwrap()[0];
        let fold = fold_of(facts).expect("fold is unaffected by an uncalled derived body");
        super::fold_subtree::certify(facts, declaration, &fold)
            .expect("membership is unaffected by an uncalled derived body");
    });
}

#[test]
fn r304_10_calling_a_derived_clone_holds_the_structs_pointer_fields() {
    with_facts(DERIVED_CLONE_CALL_CODE, |facts| {
        let [row] = facts.field_support_inputs.unsupported.as_slice() else {
            panic!(
                "one derived-impl call: {:?}",
                facts.field_support_inputs.unsupported
            )
        };
        assert_eq!(row.function, "run");
        assert_eq!(row.reason, "derived-impl-call");
        assert_eq!(
            row.field_keys,
            ["Node::field0@d0".to_owned()],
            "a derived clone copies exactly that struct's pointer fields"
        );
        assert_eq!(
            fold_of(facts),
            Err(super::fold_call::Error::FieldScheme(
                "Node::field0@d0".to_owned()
            ))
        );
    });
}

#[test]
fn r304_9_a_constant_address_is_a_known_base() {
    // `SAVED = result` writes a global pointer variable through a constant
    // address. That is a known base and can never alias a heap struct field, so
    // it records no row; the global escape stays held exactly where it was, by
    // the caller certificate rather than by the store inventory.
    let global = super::fold_chain_tests::CODE
        .replace(
            "pub struct Holder",
            "static mut SAVED:*mut Node=0 as *mut Node;\npub struct Holder",
        )
        .replace(
            " free(result as *mut core::ffi::c_void);",
            " SAVED=result;\n free(result as *mut core::ffi::c_void);",
        );
    with_facts(&global, |facts| {
        assert!(
            facts.field_support_inputs.unsupported.is_empty(),
            "a constant-address destination is resolved, not punned: {:?}",
            facts.field_support_inputs.unsupported
        );
        let declaration = &facts.fold_declarations.as_ref().unwrap()[0];
        let fold = super::fold_call::certify(
            facts,
            &declaration.call,
            declaration.argument,
            &Default::default(),
        )
        .expect("call correspondence still qualifies independently of caller closure");
        assert_eq!(
            super::fold_caller::certify(facts, declaration, &fold),
            Err(super::fold_caller::Hold::UnsupportedEffect),
            "the global escape is held by the caller certificate"
        );
    });
}
