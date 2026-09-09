use std::collections::BTreeMap;

use super::cursor::{
    adapters::*,
    carrier::ExtentOrigin,
    retention::{Node, Use, Verdict},
};

fn form(kind: Kind, mutable: bool, optional: bool) -> Form {
    Form {
        kind,
        mutable,
        optional,
    }
}

fn request(source: Form, target: Form) -> Request<u32> {
    let region = match target.kind {
        Kind::Cursor => Region::Base,
        Kind::Slice => Region::Tail,
        Kind::Thin => Region::Element,
        Kind::Raw | Kind::Owning => Region::RawUse,
    };
    Request {
        site: 50,
        source,
        target,
        destination: Destination::Call(20),
        entry: Entry::ForwardOnly,
        proofs: Proofs {
            origin: Some(Origin::BaseAndIndex(100)),
            extent: Some(ExtentProof {
                site: 50,
                origin: ExtentOrigin::Evidence(101),
            }),
            region: Some(RegionProof {
                site: 50,
                region,
                formation: 102,
                schedule: 103,
            }),
            evaluation_order: Some(104),
            current_index: Some(105),
            nonempty: Some(106),
            present: Some(107),
            same_base: Some(108),
            no_shared_write: Some(109),
        },
        t2: Some(Waiver {
            id: WaiverId::CAliasing20260901,
            site: 50,
            receipt: 110,
        }),
        pair: None,
        existing_hold: None,
    }
}

fn graph(uses: Vec<Use<u32>>) -> BTreeMap<u32, Node<u32>> {
    BTreeMap::from([(
        20,
        Node {
            complete: true,
            uses,
        },
    )])
}

fn reason(request: Request<u32>, uses: &BTreeMap<u32, Node<u32>>) -> Hold {
    let failure = plan(request, uses).unwrap_err();
    assert_eq!(
        (failure.site, failure.source, failure.target),
        (request.site, request.source, request.target)
    );
    failure.reason
}

#[test]
fn w10_cursor_safe_matrix_covers_mutability_and_optional_axes() {
    for source_mut in [false, true] {
        for target_mut in [false, true] {
            for source_opt in [false, true] {
                for target_opt in [false, true] {
                    for (kind, operation, index) in [
                        (Kind::Cursor, Operation::ReborrowCursor, IndexFlow::Preserve),
                        (Kind::Slice, Operation::CursorTail, IndexFlow::Tail),
                        (Kind::Thin, Operation::CursorElement, IndexFlow::Current),
                    ] {
                        let req = request(
                            form(Kind::Cursor, source_mut, source_opt),
                            form(kind, target_mut, target_opt),
                        );
                        if !source_mut && target_mut {
                            assert_eq!(reason(req, &BTreeMap::new()), Hold::SharedToMutable);
                            continue;
                        }
                        let result = plan(req, &BTreeMap::new()).unwrap();
                        assert_eq!((result.operation, result.index), (operation, index));
                        assert_eq!(result.tier, Tier::NotApplicable);
                        assert!(
                            result.retention.is_none(),
                            "safe destinations never enter raw alias classification"
                        );
                        let null = match (source_opt, target_opt) {
                            (false, false) => NullFlow::Direct,
                            (false, true) => NullFlow::WrapSome,
                            (true, false) => NullFlow::UnwrapReborrow,
                            (true, true) => NullFlow::MapOptionalReborrow,
                        };
                        assert_eq!(result.null, null);
                    }
                }
            }
        }
    }
}

#[test]
fn w10_inbound_slice_raw_and_wrapper_matrix() {
    for source_kind in [Kind::Slice, Kind::Raw] {
        for source_mut in [false, true] {
            for target_mut in [false, true] {
                for target_opt in [false, true] {
                    let mut req = request(
                        form(source_kind, source_mut, false),
                        form(Kind::Cursor, target_mut, target_opt),
                    );
                    req.proofs.origin = Some(Origin::ForwardWindow(100));
                    if !source_mut && target_mut {
                        assert_eq!(
                            reason(req, &graph(vec![Use::Observe])),
                            Hold::SharedToMutable
                        );
                        continue;
                    }
                    let result = plan(req, &graph(vec![Use::Observe])).unwrap();
                    assert_eq!(result.index, IndexFlow::Zero);
                    assert_eq!(
                        result.operation,
                        if source_kind == Kind::Raw {
                            Operation::RawCursor
                        } else {
                            Operation::SliceCursor
                        }
                    );
                    assert_eq!(
                        result.null,
                        if source_kind == Kind::Raw && target_opt {
                            NullFlow::GuardRawConstructor
                        } else if target_opt {
                            NullFlow::WrapSome
                        } else {
                            NullFlow::Direct
                        }
                    );
                    req.entry = Entry::NeedsPrefix;
                    assert_eq!(reason(req, &graph(vec![Use::Observe])), Hold::OriginPrefix);
                    req.proofs.origin = Some(Origin::BaseAndIndex(100));
                    assert_eq!(
                        plan(req, &graph(vec![Use::Observe])).unwrap().index,
                        IndexFlow::Decompose
                    );
                    if source_kind == Kind::Raw {
                        req.destination = Destination::RawWrapper(20);
                        assert_eq!(
                            plan(req, &graph(vec![Use::Observe])).unwrap().operation,
                            Operation::RawCursor
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn w10_prefix_endpoint_and_required_terminal_holds_are_independent() {
    let mut req = request(
        form(Kind::Cursor, true, true),
        form(Kind::Slice, true, false),
    );
    req.entry = Entry::NeedsPrefix;
    assert_eq!(reason(req, &BTreeMap::new()), Hold::PrefixLost);
    req.entry = Entry::ForwardOnly;
    req.proofs.present = None;
    assert_eq!(reason(req, &BTreeMap::new()), Hold::Present);
    req.target.optional = true;
    assert_eq!(
        plan(req, &BTreeMap::new()).unwrap().null,
        NullFlow::MapOptionalReborrow
    );
    req = request(
        form(Kind::Cursor, true, false),
        form(Kind::Thin, true, false),
    );
    req.proofs.nonempty = None;
    assert_eq!(reason(req, &BTreeMap::new()), Hold::Nonempty);
    req.target = form(Kind::Raw, true, false);
    req.proofs.region.as_mut().unwrap().region = Region::RawUse;
    assert_eq!(
        plan(req, &graph(vec![Use::Observe])).unwrap().operation,
        Operation::RawView
    );
}

#[test]
fn w10_full_base_schedule_and_extent_origin_are_required() {
    let mut req = request(
        form(Kind::Cursor, true, false),
        form(Kind::Cursor, true, false),
    );
    req.proofs.region.as_mut().unwrap().region = Region::Element;
    assert_eq!(reason(req, &BTreeMap::new()), Hold::FormationOrSchedule);
    req.proofs.region.as_mut().unwrap().region = Region::Base;
    req.proofs.region.as_mut().unwrap().site = 999;
    assert_eq!(reason(req, &BTreeMap::new()), Hold::FormationOrSchedule);
    req.proofs.region = None;
    assert_eq!(reason(req, &BTreeMap::new()), Hold::FormationOrSchedule);
    req = request(
        form(Kind::Cursor, true, false),
        form(Kind::Slice, true, false),
    );
    req.proofs.extent = Some(ExtentProof {
        site: 50,
        origin: ExtentOrigin::Fallback {
            origin_receipt: 7,
            site_receipt: 8,
        },
    });
    let tail = plan(req, &BTreeMap::new()).unwrap();
    assert_eq!(tail.proofs.extent, req.proofs.extent);
    req.proofs.origin = None;
    assert_eq!(reason(req, &BTreeMap::new()), Hold::OriginPrefix);
    req.proofs.origin = Some(Origin::BaseAndIndex(100));
    req.proofs.evaluation_order = None;
    assert_eq!(reason(req, &BTreeMap::new()), Hold::EvaluationOrder);
}

#[test]
fn w12_safe_local_copy_keeps_one_base_and_never_uses_raw_retention() {
    let mut req = request(
        form(Kind::Cursor, true, false),
        form(Kind::Cursor, true, true),
    );
    req.destination = Destination::Local(20);
    let result = plan(req, &graph(vec![Use::Retain])).unwrap();
    assert_eq!(result.operation, Operation::CopyIndex);
    assert_eq!(result.null, NullFlow::WrapSome);
    assert!(result.retention.is_none());
    req.proofs.same_base = None;
    assert_eq!(reason(req, &BTreeMap::new()), Hold::BaseTransfer);
    req.target.kind = Kind::Owning;
    assert_eq!(
        reason(req, &graph(vec![Use::Unknown])),
        Hold::DestinationUnbuilt
    );
}

#[test]
fn w12_raw_matrix_records_current_index_null_and_permission() {
    for source_mut in [false, true] {
        for target_mut in [false, true] {
            for source_opt in [false, true] {
                let req = request(
                    form(Kind::Cursor, source_mut, source_opt),
                    form(Kind::Raw, target_mut, false),
                );
                let result = plan(req, &graph(vec![Use::Observe])).unwrap();
                assert_eq!(result.index, IndexFlow::Current);
                assert_eq!(result.tier, Tier::T1);
                assert_eq!(
                    result.null,
                    if source_opt {
                        NullFlow::NullOrRawView
                    } else {
                        NullFlow::Direct
                    }
                );
            }
        }
    }
}

#[test]
fn w12_raw_local_queries_destination_chain_before_t2() {
    let mut req = request(
        form(Kind::Cursor, true, false),
        form(Kind::Raw, true, false),
    );
    req.destination = Destination::Local(20);
    let mut uses = graph(vec![Use::Copy(21)]);
    uses.insert(
        10,
        Node {
            complete: true,
            uses: vec![Use::Observe],
        },
    );
    uses.insert(
        21,
        Node {
            complete: true,
            uses: vec![Use::Copy(22)],
        },
    );
    uses.insert(
        22,
        Node {
            complete: true,
            uses: vec![Use::Retain],
        },
    );
    assert_eq!(reason(req, &uses), Hold::PositiveRetention);
    uses.insert(
        22,
        Node {
            complete: true,
            uses: vec![Use::Observe],
        },
    );
    let result = plan(req, &uses).unwrap();
    assert_eq!(result.retention.as_ref().unwrap().root, 20);
    assert_eq!(result.tier, Tier::T1);
    uses.remove(&22);
    let result = plan(req, &uses).unwrap();
    assert_eq!(result.tier, Tier::T2(req.t2.unwrap()));
    assert_eq!(result.retention.unwrap().verdict(), Verdict::Unknown);
}

#[test]
fn w12_unknown_needs_named_site_waiver_and_used_import_return_stays_t2() {
    let mut req = request(
        form(Kind::Cursor, true, false),
        form(Kind::Raw, true, false),
    );
    let uses = graph(vec![Use::Unknown]);
    let result = plan(req, &uses).unwrap();
    assert_eq!(result.tier, Tier::T2(req.t2.unwrap()));
    assert_eq!(
        req.t2.unwrap().id.key(),
        "c-aliasing-semantics-at-unsafe-bridges/v1@2026-09-01"
    );
    req.t2.as_mut().unwrap().site = 999;
    assert_eq!(reason(req, &uses), Hold::WaiverSite);
    req.t2 = None;
    assert_eq!(reason(req, &uses), Hold::WaiverMissing);
    req = request(
        form(Kind::Cursor, true, false),
        form(Kind::Raw, true, false),
    );
    let mut uses = graph(vec![Use::ImportedAliasReturn(21)]);
    uses.insert(
        21,
        Node {
            complete: true,
            uses: vec![Use::Observe],
        },
    );
    assert_eq!(plan(req, &uses).unwrap().tier, Tier::T2(req.t2.unwrap()));
    uses.insert(
        21,
        Node {
            complete: true,
            uses: vec![Use::Retain],
        },
    );
    assert_eq!(reason(req, &uses), Hold::PositiveRetention);
    assert_eq!(
        plan(req, &graph(vec![Use::UnusedImportedAliasReturn]))
            .unwrap()
            .tier,
        Tier::T1
    );
}

#[test]
fn w12_shared_derived_writes_and_direct_storage_hold_despite_waiver() {
    let mut req = request(
        form(Kind::Cursor, false, false),
        form(Kind::Raw, true, false),
    );
    assert_eq!(
        reason(req, &graph(vec![Use::Write])),
        Hold::SharedDerivedWrite
    );
    req.proofs.no_shared_write = None;
    assert_eq!(
        reason(req, &graph(vec![Use::Observe])),
        Hold::MissingWriteProof
    );
    req.source.mutable = true;
    for destination in [Destination::Field(20), Destination::Return(20)] {
        req.destination = destination;
        assert_eq!(
            reason(req, &graph(vec![Use::Unknown])),
            Hold::PositiveRetention
        );
        req.target.kind = Kind::Cursor;
        assert_eq!(reason(req, &BTreeMap::new()), Hold::DestinationUnbuilt);
        req.target.kind = Kind::Raw;
    }
}

#[test]
fn w10_pair_and_observation_have_distinct_obligations() {
    let mut req = request(
        form(Kind::Cursor, true, false),
        form(Kind::Raw, true, false),
    );
    req.destination = Destination::Observation(20);
    assert_eq!(
        plan(req, &graph(vec![Use::Observe])).unwrap().tier,
        Tier::NotApplicable
    );
    assert_eq!(
        reason(req, &graph(vec![Use::Unknown])),
        Hold::RetentionUnknown
    );
    req.destination = Destination::PairPeer(20);
    assert_eq!(reason(req, &graph(vec![Use::Unknown])), Hold::PairMissing);
    req.pair = Some(PairProof {
        site: 50,
        primary: 3,
        waiver_receipt: 120,
    });
    assert_eq!(
        reason(req, &graph(vec![Use::Unknown])),
        Hold::FormationOrSchedule
    );
    req.proofs.region.as_mut().unwrap().region = Region::Base;
    let result = plan(req, &graph(vec![Use::Unknown])).unwrap();
    assert_eq!(result.operation, Operation::PairRawView);
    assert_eq!(result.pair, req.pair);
}

#[test]
fn w10_existing_holds_and_non_cursor_pairs_never_fall_through() {
    let mut req = request(
        form(Kind::Cursor, true, false),
        form(Kind::Raw, true, false),
    );
    for hold in [
        ExistingHold::FreedSlot,
        ExistingHold::IoDomain,
        ExistingHold::ForeignAbiStruct,
        ExistingHold::AddressTaken,
        ExistingHold::Layout,
        ExistingHold::BaseAliasConflict,
    ] {
        req.existing_hold = Some(hold);
        assert_eq!(
            reason(req, &graph(vec![Use::Unknown])),
            Hold::Inherited(hold)
        );
    }
    req.existing_hold = None;
    req.target.optional = true;
    assert_eq!(reason(req, &BTreeMap::new()), Hold::InvalidForm);
    req.source.kind = Kind::Thin;
    req.target = form(Kind::Cursor, true, false);
    assert_eq!(reason(req, &BTreeMap::new()), Hold::DestinationUnbuilt);
    req.target.kind = Kind::Slice;
    assert_eq!(reason(req, &BTreeMap::new()), Hold::DestinationUnbuilt);
}

#[test]
fn w12_unknown_shared_boundary_requires_write_evidence_even_for_const_raw() {
    for (source, target) in [
        (
            form(Kind::Cursor, false, false),
            form(Kind::Raw, false, false),
        ),
        (
            form(Kind::Raw, true, false),
            form(Kind::Cursor, false, false),
        ),
    ] {
        let mut req = request(source, target);
        req.proofs.no_shared_write = None;
        for uses in [
            graph(vec![Use::Unknown]),
            BTreeMap::new(),
            BTreeMap::from([(
                20,
                Node {
                    complete: false,
                    uses: vec![],
                },
            )]),
        ] {
            assert_eq!(reason(req, &uses), Hold::MissingWriteProof);
        }
        assert_eq!(
            plan(req, &graph(vec![Use::Observe])).unwrap().tier,
            Tier::T1
        );
        req.proofs.no_shared_write = Some(109);
        assert_eq!(
            plan(req, &graph(vec![Use::Unknown])).unwrap().tier,
            Tier::T2(req.t2.unwrap())
        );
        assert_eq!(
            reason(req, &graph(vec![Use::Write])),
            Hold::SharedDerivedWrite
        );
    }
}

#[test]
fn w10_optional_slice_inbound_and_raw_null_map_use_terminal_contracts() {
    for target_optional in [false, true] {
        let mut req = request(
            form(Kind::Slice, true, true),
            form(Kind::Cursor, true, target_optional),
        );
        req.proofs.origin = Some(Origin::ForwardWindow(100));
        let result = plan(req, &BTreeMap::new()).unwrap();
        assert_eq!(result.index, IndexFlow::Zero);
        assert_eq!(
            result.null,
            if target_optional {
                NullFlow::MapOptionalReborrow
            } else {
                NullFlow::UnwrapReborrow
            }
        );
        req.proofs.present = None;
        if target_optional {
            assert!(plan(req, &BTreeMap::new()).is_ok());
        } else {
            assert_eq!(reason(req, &BTreeMap::new()), Hold::Present);
        }
    }
    let mut req = request(form(Kind::Cursor, true, true), form(Kind::Raw, true, false));
    req.proofs.present = None;
    assert_eq!(
        plan(req, &graph(vec![Use::Observe])).unwrap().null,
        NullFlow::NullOrRawView
    );
    req.proofs.current_index = None;
    assert_eq!(reason(req, &graph(vec![Use::Observe])), Hold::CurrentIndex);
    req.proofs.current_index = Some(105);
    req.proofs.extent = None;
    assert_eq!(reason(req, &graph(vec![Use::Observe])), Hold::Extent);
}

#[test]
fn w10_fallback_extent_requires_current_adapter_site_binding() {
    let mut req = request(
        form(Kind::Cursor, true, false),
        form(Kind::Slice, true, false),
    );
    let origin = ExtentOrigin::Fallback {
        origin_receipt: 7,
        site_receipt: 8,
    };
    req.proofs.extent = Some(ExtentProof { site: 49, origin });
    assert_eq!(reason(req, &BTreeMap::new()), Hold::Extent);
    req.proofs.extent = None;
    assert_eq!(reason(req, &BTreeMap::new()), Hold::Extent);
    req.proofs.extent = Some(ExtentProof { site: 50, origin });
    let result = plan(req, &BTreeMap::new()).unwrap();
    assert_eq!(result.proofs.extent, Some(ExtentProof { site: 50, origin }));
}
