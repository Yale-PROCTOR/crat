//! Standalone pure controls: `rustc --edition=2024 --test` this file.
mod slice_call_contract;
use slice_call_contract::*;

fn site(expected: InterfaceForm, found: InterfaceForm) -> CallSite {
    CallSite {
        owner: "callee-class".into(),
        caller: "caller".into(),
        callee: "callee".into(),
        argument_index: 1,
        argument_span: SourceSpan { lo: 40, hi: 44 },
        expected,
        found,
    }
}

fn zero(expected: InterfaceForm, found: InterfaceForm) -> Carrier {
    Carrier {
        site: site(expected, found),
        kind: CarrierKind::ZeroSyntax {
            bridge_kind: "interface-call-zero-syntax".into(),
            glue: GlueVerdict::NoEdit,
        },
        native_arm: "glue".into(),
        dependency_registered: true,
        held: false,
    }
}

#[test]
fn zc_w1_unique_zero_carrier_preserves_native_ownership() {
    let carrier = zero(InterfaceForm::SliceShared, InterfaceForm::SliceShared);
    let wanted = carrier.site.clone();
    let selected = select_carrier(&wanted, &[], &[carrier]).expect("unique zero carrier");
    assert_eq!(
        selected.kind,
        CarrierKind::ZeroSyntax {
            bridge_kind: "interface-call-zero-syntax".into(),
            glue: GlueVerdict::NoEdit,
        }
    );
    assert_eq!(selected.native_arm, "glue");
    assert!(selected.dependency_registered);
}

#[test]
fn zc_w2_edit_carrier_remains_supported() {
    let carrier = Carrier {
        site: site(InterfaceForm::RefShared, InterfaceForm::SliceShared),
        kind: CarrierKind::Edit,
        native_arm: "c".into(),
        dependency_registered: true,
        held: false,
    };
    let wanted = carrier.site.clone();
    let selected = select_carrier(&wanted, &[carrier], &[]).expect("unique edit");
    assert_eq!(selected.kind, CarrierKind::Edit);
    assert_eq!(selected.native_arm, "c");
}

#[test]
fn zc_w3_missing_ambiguous_and_held_fail_closed() {
    let wanted = site(InterfaceForm::SliceShared, InterfaceForm::SliceShared);
    assert_eq!(select_carrier(&wanted, &[], &[]), Err(CarrierHold::Missing));
    let carrier = zero(wanted.expected, wanted.found);
    assert_eq!(
        select_carrier(&wanted, &[carrier.clone()], &[carrier.clone()]),
        Err(CarrierHold::Ambiguous { candidates: 2 })
    );
    let mut held = carrier;
    held.held = true;
    assert_eq!(
        select_carrier(&wanted, &[], &[held]),
        Err(CarrierHold::Held)
    );
}

#[test]
fn zc_w4_zero_carrier_requires_kind_real_span_and_no_edit_glue() {
    let wanted = site(InterfaceForm::SliceShared, InterfaceForm::SliceShared);
    let mut wrong_kind = zero(wanted.expected, wanted.found);
    wrong_kind.kind = CarrierKind::ZeroSyntax {
        bridge_kind: "generated-zero-syntax".into(),
        glue: GlueVerdict::NoEdit,
    };
    assert_eq!(
        select_carrier(&wanted, &[], &[wrong_kind]),
        Err(CarrierHold::Incompatible)
    );
    let invalid_site = CallSite {
        argument_span: SourceSpan { lo: 0, hi: 0 },
        ..wanted.clone()
    };
    let invalid_span = Carrier {
        site: invalid_site.clone(),
        kind: CarrierKind::ZeroSyntax {
            bridge_kind: "interface-call-zero-syntax".into(),
            glue: GlueVerdict::NoEdit,
        },
        native_arm: "glue".into(),
        dependency_registered: true,
        held: false,
    };
    assert_eq!(
        select_carrier(&invalid_site, &[], &[invalid_span]),
        Err(CarrierHold::Incompatible)
    );
    let mut blocked = zero(wanted.expected, wanted.found);
    blocked.kind = CarrierKind::ZeroSyntax {
        bridge_kind: "interface-call-zero-syntax".into(),
        glue: GlueVerdict::Blocked,
    };
    assert_eq!(
        select_carrier(&wanted, &[], &[blocked]),
        Err(CarrierHold::Incompatible)
    );
    let mut adapter = zero(wanted.expected, wanted.found);
    adapter.kind = CarrierKind::ZeroSyntax {
        bridge_kind: "interface-call-zero-syntax".into(),
        glue: GlueVerdict::Adapter,
    };
    assert_eq!(
        select_carrier(&wanted, &[], &[adapter]),
        Err(CarrierHold::Incompatible)
    );
    let mut no_dependency = zero(wanted.expected, wanted.found);
    no_dependency.dependency_registered = false;
    assert_eq!(
        select_carrier(&wanted, &[], &[no_dependency]),
        Err(CarrierHold::Incompatible)
    );
    let mut recursive = zero(wanted.expected, wanted.found);
    recursive.site.callee = recursive.site.caller.clone();
    recursive.site.owner = "caller-class".into();
    recursive.dependency_registered = false;
    let recursive_site = recursive.site.clone();
    assert_eq!(
        select_carrier(&recursive_site, &[], &[recursive]),
        Ok(SelectedCarrier {
            kind: CarrierKind::ZeroSyntax {
                bridge_kind: "interface-call-zero-syntax".into(),
                glue: GlueVerdict::NoEdit,
            },
            native_arm: "glue".into(),
            dependency_registered: false,
        })
    );
}

#[test]
fn zc_w5_exact_identity_and_forms_are_required() {
    let wanted = site(InterfaceForm::SliceShared, InterfaceForm::SliceShared);
    for change in 0..7 {
        let mut carrier = zero(wanted.expected, wanted.found);
        match change {
            0 => carrier.site.owner = "other".into(),
            1 => carrier.site.caller = "other".into(),
            2 => carrier.site.callee = "other".into(),
            3 => carrier.site.argument_index = 2,
            4 => carrier.site.argument_span = SourceSpan { lo: 41, hi: 44 },
            5 => carrier.site.expected = InterfaceForm::RefShared,
            6 => carrier.site.found = InterfaceForm::SliceMut,
            _ => unreachable!(),
        }
        assert_eq!(
            select_carrier(&wanted, &[], &[carrier]),
            Err(CarrierHold::Missing)
        );
    }
}

#[test]
fn zc_w6_shared_to_mut_remains_incompatible() {
    let wanted = site(InterfaceForm::SliceMut, InterfaceForm::SliceShared);
    let carrier = zero(wanted.expected, wanted.found);
    assert_eq!(
        select_carrier(&wanted, &[], &[carrier]),
        Err(CarrierHold::Incompatible)
    );
}

fn reader(subject: &str, form: ReaderForm, array: Option<bool>, downstream: bool) -> ReaderHop {
    ReaderHop {
        subject: subject.into(),
        form,
        array,
        downstream_array_use: downstream,
    }
}

#[test]
fn reader_w6_arr_keeps_slices_at_every_hop() {
    let hops = [
        reader("entry", ReaderForm::Slice, Some(true), true),
        reader("middle", ReaderForm::ThinRef, Some(true), true),
        reader("leaf", ReaderForm::Slice, Some(true), true),
    ];
    assert_eq!(
        preserve_reader_chain(&hops).unwrap(),
        vec![
            ("entry".into(), ReaderForm::Slice),
            ("middle".into(), ReaderForm::Slice),
            ("leaf".into(), ReaderForm::Slice)
        ]
    );
}

#[test]
fn reader_w6n_missing_or_ptr_fact_holds_the_narrowing_hop() {
    for array in [None, Some(false)] {
        let hops = [
            reader("entry", ReaderForm::Slice, Some(true), true),
            reader("middle", ReaderForm::ThinRef, array, true),
            reader("leaf", ReaderForm::Slice, Some(true), true),
        ];
        assert_eq!(
            preserve_reader_chain(&hops),
            Err(ReaderHold::ReaderChainNarrowsRange {
                subject: "middle".into(),
                needs_array_fact: true
            })
        );
    }
}

#[test]
fn reader_non_array_use_keeps_thin_reference() {
    let hops = [reader("one", ReaderForm::ThinRef, None, false)];
    assert_eq!(
        preserve_reader_chain(&hops).unwrap(),
        vec![("one".into(), ReaderForm::ThinRef)]
    );
}
