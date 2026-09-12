//! Standalone pure witnesses: rustc --edition=2024 --test this file.
//! Imports the real SlotKind source; no compiler-fact stubs or corpus input.
//! This does not replace the gated production CE-W01..CE-W09 suite.

#[path = "../../analyses/borrow_ownership/domain.rs"]
pub mod slot_domain;
mod analyses {
    pub mod borrow_ownership {
        pub use crate::slot_domain as domain;
    }
}
mod contract_extent;

use contract_extent::*;
use slot_domain::SlotKind;

fn subject() -> SubjectFacts {
    SubjectFacts {
        key: "f::p#1".into(),
        construction: "entry:caller0:p".into(),
        model_kind: Some(SlotKind::Ref),
        depth: 1,
        form: CurrentForm::Ref {
            mutable: false,
            nullable: false,
        },
        array: Some(true),
        non_length: Ok(()),
    }
}

fn site(requirement: Requirement) -> ContractSite {
    ContractSite {
        subject: "f::p#1".into(),
        site: "f:bb0:s2:arg0".into(),
        contract: "fixture:canonical-matched-contract-v1".into(),
        requirement,
    }
}

fn count() -> CountOperand {
    CountOperand {
        site: "f:bb0:s2:arg0".into(),
        argument_index: 2,
        construction: "entry:caller0:p".into(),
        elements: Ok("n".into()),
    }
}

fn promotion(selection: Selection) -> Promotion {
    let Selection::Promote(p) = selection else { panic!("expected promotion, got {selection:?}") };
    p
}

#[test]
fn ce_p01_nul_fallback_retains_site_and_typed_waiver() {
    let input = site(Requirement::NulTerminated);
    let p = promotion(select(&subject(), &[input.clone()], None));
    assert_eq!(p.subject, subject().key);
    assert_eq!(p.construction, subject().construction);
    assert_eq!(
        p.length,
        LengthPlan::Fallback(FallbackReason::NulTerminated)
    );
    assert_eq!(p.length.waiver(), Some(Waiver::SliceExtent));
    assert_eq!(p.sites, [input]);
}

#[test]
fn ce_p02_exact_count_keeps_operand_identity_and_elements() {
    let p = promotion(select(
        &subject(),
        &[site(Requirement::ExactAccess(Some(count())))],
        None,
    ));
    assert_eq!(
        p.length,
        LengthPlan::Evidence {
            elements: "n".into(),
            source: LengthSource::ExactContract {
                site: count().site,
                argument_index: 2
            },
        }
    );
    assert_eq!(p.length.waiver(), None);
}

#[test]
fn ce_p03_one_element_lifecycle_and_no_contract_preserve_ladder() {
    for inputs in [
        vec![],
        vec![site(Requirement::OneElement)],
        vec![site(Requirement::Lifecycle)],
    ] {
        assert_eq!(
            select(&subject(), &inputs, None),
            Selection::Keep(KeepReason::NoContractOperation)
        );
    }
}

#[test]
fn ce_p04_existing_fat_and_other_forms_are_untouched() {
    for form in [CurrentForm::Slice, CurrentForm::Other] {
        let mut s = subject();
        s.form = form;
        assert_eq!(
            select(&s, &[site(Requirement::NulTerminated)], None),
            Selection::Keep(KeepReason::ExistingForm)
        );
    }
}

#[test]
fn ce_p05_fatness_is_a_required_independent_conjunct() {
    for (array, reason) in [
        (Some(false), KeepReason::FatnessPtr),
        (None, KeepReason::FatnessMissing),
    ] {
        let mut s = subject();
        s.array = array;
        assert_eq!(
            select(&s, &[site(Requirement::NulTerminated)], None),
            Selection::Keep(reason)
        );
    }
    assert_eq!(
        select(&subject(), &[], None),
        Selection::Keep(KeepReason::NoContractOperation)
    );
}

#[test]
fn ce_p06_model_and_depth_authority_are_unchanged() {
    for model in [Some(SlotKind::Raw), Some(SlotKind::Owning), None] {
        let mut s = subject();
        s.model_kind = model;
        assert_eq!(
            select(&s, &[site(Requirement::NulTerminated)], None),
            Selection::Keep(KeepReason::ModelNotRef)
        );
    }
    let mut s = subject();
    s.depth = 2;
    assert_eq!(
        select(&s, &[site(Requirement::NulTerminated)], None),
        Selection::Keep(KeepReason::Depth)
    );
}

#[test]
fn ce_p07_nullability_and_mutability_survive_promotion() {
    for mutable in [false, true] {
        for nullable in [false, true] {
            let mut s = subject();
            s.form = CurrentForm::Ref { mutable, nullable };
            let p = promotion(select(&s, &[site(Requirement::NulTerminated)], None));
            assert_eq!((p.mutable, p.nullable), (mutable, nullable));
        }
    }
}

#[test]
fn ce_p08_upper_read_limit_never_becomes_exact_evidence() {
    let p = promotion(select(
        &subject(),
        &[site(Requirement::UpperBound(Some(count())))],
        None,
    ));
    assert_eq!(p.length, LengthPlan::Fallback(FallbackReason::UpperBound));
    assert_eq!(p.length.waiver(), Some(Waiver::SliceExtent));
}

#[test]
fn ce_p09_non_length_holds_cannot_spend_length_waiver() {
    for hold in [
        NonLengthHold::Uninitialized,
        NonLengthHold::MissingRangeAlias,
        NonLengthHold::Evaluation,
        NonLengthHold::ReturnCustody,
        NonLengthHold::Existing("retained-alias".into()),
        NonLengthHold::Existing("held:void-pointee".into()),
    ] {
        let mut s = subject();
        s.non_length = Err(hold.clone());
        for requirement in [
            Requirement::NulTerminated,
            Requirement::ExactAccess(Some(count())),
        ] {
            for backing in [None, Some(backing())] {
                assert_eq!(
                    select(&s, &[site(requirement.clone())], backing.as_ref()),
                    Selection::Keep(KeepReason::NonLength(hold.clone()))
                );
            }
        }
    }
}

#[test]
fn ce_p10_backing_extent_precedes_contract_and_fallback() {
    let backing = backing();
    for requirement in [
        Requirement::NulTerminated,
        Requirement::UpperBound(Some(count())),
        Requirement::ExactAccess(Some(count())),
    ] {
        let p = promotion(select(&subject(), &[site(requirement)], Some(&backing)));
        assert_eq!(
            p.length,
            LengthPlan::Evidence {
                elements: backing.elements.clone(),
                source: LengthSource::Backing(backing.evidence.clone())
            }
        );
        assert_eq!(p.length.waiver(), None);
    }
}

#[test]
fn ce_p11_missing_units_or_transport_uses_attributed_fallback() {
    for gap in [CountGap::UnitsUnproved, CountGap::TransportMissing] {
        let mut operand = count();
        operand.elements = Err(gap.clone());
        let p = promotion(select(
            &subject(),
            &[site(Requirement::ExactAccess(Some(operand)))],
            None,
        ));
        assert_eq!(
            p.length,
            LengthPlan::Fallback(FallbackReason::CountGap(gap))
        );
    }
    let p = promotion(select(
        &subject(),
        &[site(Requirement::ExactAccess(None))],
        None,
    ));
    assert_eq!(p.length, LengthPlan::Fallback(FallbackReason::CountMissing));
}

#[test]
fn ce_p12_foreign_site_identity_is_not_an_expression_spelling() {
    let mut foreign_subject = site(Requirement::NulTerminated);
    foreign_subject.subject = "g::q#1".into();
    assert_eq!(
        select(&subject(), &[foreign_subject], None),
        Selection::Keep(KeepReason::WrongSubject)
    );
    let one = site(Requirement::NulTerminated);
    assert_eq!(
        select(&subject(), &[one.clone(), one], None),
        Selection::Keep(KeepReason::DuplicateSite)
    );
    let mut operand = count();
    operand.site = "g:bb0:s2:arg0".into();
    assert_eq!(
        select(
            &subject(),
            &[site(Requirement::ExactAccess(Some(operand)))],
            None
        ),
        Selection::Keep(KeepReason::WrongCountSite)
    );
}

#[test]
fn ce_p13_multiple_requirements_do_not_choose_first_count() {
    let a = site(Requirement::ExactAccess(Some(count())));
    let mut b = a.clone();
    b.site = "f:bb1:s2:arg0".into();
    let Requirement::ExactAccess(Some(ref mut c)) = b.requirement else { unreachable!() };
    c.site = b.site.clone();
    c.elements = Ok("m".into());
    let p = promotion(select(&subject(), &[a.clone(), b.clone()], None));
    assert_eq!(
        p.length,
        LengthPlan::Fallback(FallbackReason::MultipleRequirements)
    );
    assert_eq!(p.sites, [a, b]);
}

fn backing() -> BackingExtent {
    BackingExtent {
        subject: subject().key,
        construction: subject().construction,
        elements: "backing_len".into(),
        evidence: "allocation:17".into(),
    }
}

#[test]
fn ce_p14_length_evidence_belongs_to_this_construction() {
    let s = subject();
    let inputs = [site(Requirement::ExactAccess(Some(count())))];
    let mut b = backing();
    b.subject = "other::p#1".into();
    assert_eq!(
        select(&s, &inputs, Some(&b)),
        Selection::Keep(KeepReason::WrongSubject)
    );
    let mut b = backing();
    b.construction = "entry:caller1:p".into();
    assert_eq!(
        select(&s, &inputs, Some(&b)),
        Selection::Keep(KeepReason::WrongConstruction)
    );
    let mut c = count();
    c.construction = "entry:caller1:p".into();
    assert_eq!(
        select(&s, &[site(Requirement::ExactAccess(Some(c)))], None),
        Selection::Keep(KeepReason::WrongConstruction)
    );
    let mut wrong_site = inputs[0].clone();
    wrong_site.subject = "other::p#1".into();
    assert_eq!(
        select(&s, &[wrong_site], Some(&backing())),
        Selection::Keep(KeepReason::WrongSubject)
    );
    assert_eq!(
        select(
            &s,
            &[inputs[0].clone(), inputs[0].clone()],
            Some(&backing())
        ),
        Selection::Keep(KeepReason::DuplicateSite)
    );
}
