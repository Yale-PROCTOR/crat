//! Conditional field-output discharge controls. Embedded programs are analyzed
//! only; construction retains all raw meets and performs no model queries.

use super::{
    facts::Facts,
    field_support::{self, OutputDischarge},
    graph_tests::with_facts,
    matched::{Meet, SourceLineage, TerminalTarget},
    ref_effects::{self, Candidate, ConsumedOutput},
};

const IFL3: &str = r#"
unsafe extern "C" {
    fn malloc(size: usize) -> *mut core::ffi::c_void;
    fn free(p: *mut core::ffi::c_void);
}
pub struct H { ptr: *mut i32 }
pub unsafe fn release(h: *mut H) { free((*h).ptr as *mut core::ffi::c_void); }
pub unsafe fn f() -> i32 {
    let owner = malloc(core::mem::size_of::<i32>()) as *mut i32;
    *owner = 1;
    let mut h = H { ptr: owner };
    let before = *h.ptr;
    release(&mut h);
    before
}
"#;

fn context(facts: &Facts) -> (Candidate, ConsumedOutput, Meet, Meet) {
    let plan = ref_effects::Plan::build(facts);
    assert_eq!(plan.candidates.len(), 1, "{plan:#?}");
    let candidate = plan.candidates[0].clone();
    let matched = &facts.licensing.as_ref().unwrap().matched;
    let certificate =
        ref_effects::certify_consumed_output(facts, &candidate, matched.guard_aliases()).unwrap();
    let meets = matched.meets_for(candidate.scalar_before);
    let free = meets
        .iter()
        .find(|meet| meet.terminal == certificate.free)
        .expect("same-call free route")
        .clone();
    let output = meets
        .iter()
        .find(|meet| meet.terminal == certificate.output)
        .expect("retained raw projected-output route")
        .clone();
    assert_eq!(free.source, output.source);
    assert_eq!(
        free.guards.get(&certificate.required_free.binding),
        Some(&true)
    );
    (candidate, certificate, free, output)
}

#[test]
fn c05_ref_support_records_same_free_and_conditional_output_discharge() {
    with_facts(IFL3, |facts| {
        let (candidate, certificate, free, output) = context(facts);
        let frozen = facts.licensing.as_ref().unwrap();
        let before = frozen.matched.meets_for(candidate.scalar_before);
        let proofs = field_support::audit(
            facts,
            &facts.field_support_inputs,
            &frozen.matched,
            &frozen.value_origins,
        );
        let field = proofs
            .iter()
            .find(|field| field.field_key == candidate.field_key)
            .unwrap();
        assert!(field.supported(), "{field:#?}");
        assert_eq!(field.stores.len(), 1);
        let store = &field.stores[0];
        assert_eq!(store.meet, free);
        assert_eq!(
            store.meet.guards.get(&certificate.required_free.binding),
            Some(&true)
        );
        assert_eq!(
            store.discharged_outputs,
            vec![OutputDischarge {
                output: output.clone(),
                certificate: certificate.clone(),
            }]
        );
        assert_eq!(
            frozen.matched.meets_for(candidate.scalar_before),
            before,
            "conditional disposition never deletes raw transport meets"
        );
        assert_eq!(
            OutputDischarge::certify(&output, &free, &certificate),
            store.discharged_outputs.first().cloned()
        );
    });
}

#[test]
fn c05_ref_support_requires_positive_present_same_free_guard() {
    with_facts(IFL3, |facts| {
        let (_, certificate, free, output) = context(facts);
        assert!(OutputDischarge::certify(&output, &free, &certificate).is_some());
        let mut false_free = free.clone();
        false_free
            .guards
            .insert(certificate.required_free.binding, false);
        assert!(OutputDischarge::certify(&output, &false_free, &certificate).is_none());
        let mut absent_free = free.clone();
        absent_free
            .guards
            .remove(&certificate.required_free.binding);
        assert!(OutputDischarge::certify(&output, &absent_free, &certificate).is_none());
        let mut false_certificate = certificate.clone();
        false_certificate.required_free.required = false;
        assert!(OutputDischarge::certify(&output, &free, &false_certificate).is_none());
        let mut contradictory_output = output.clone();
        contradictory_output
            .guards
            .insert(certificate.required_free.binding, false);
        assert!(OutputDischarge::certify(&contradictory_output, &free, &certificate).is_none());
    });
}

#[test]
fn c05_ref_support_requires_same_source_and_call_lineage() {
    with_facts(IFL3, |facts| {
        let (_, certificate, free, output) = context(facts);
        assert!(OutputDischarge::certify(&output, &free, &certificate).is_some());
        let mut wrong_source = output.clone();
        wrong_source.source.endpoint = certificate.split;
        assert!(OutputDischarge::certify(&wrong_source, &free, &certificate).is_none());
        let mut wrong_lineage = output.clone();
        let SourceLineage::Exact(calls) = &mut wrong_lineage.terminal.lineage else {
            panic!("exact fixture lineage")
        };
        calls[0].statement += 1;
        assert!(OutputDischarge::certify(&wrong_lineage, &free, &certificate).is_none());
        let mut wrong_free = free.clone();
        wrong_free.terminal.target = TerminalTarget::Free(certificate.split);
        assert!(OutputDischarge::certify(&output, &wrong_free, &certificate).is_none());
        assert!(
            OutputDischarge::certify(&free, &free, &certificate).is_none(),
            "a free terminal can never be relabeled a discharged output"
        );
    });
}

#[test]
fn c05_ref_support_retained_partner_free_still_blocks() {
    let code = IFL3.replace(
        "release(&mut h);",
        "release(&mut h);\n    free(owner as *mut core::ffi::c_void);",
    );
    with_facts(&code, |facts| {
        let (candidate, certificate, free, _) = context(facts);
        let frozen = facts.licensing.as_ref().unwrap();
        let seeds =
            frozen
                .matched
                .source_nodes(candidate.construction, &candidate.function, &free.source);
        assert!(!seeds.is_empty());
        let partners: Vec<_> = seeds
            .into_iter()
            .flat_map(|seed| frozen.matched.meets_for(seed))
            .filter(|meet| {
                meet.source == free.source
                    && matches!(meet.terminal.target, TerminalTarget::Free(_))
                    && meet.terminal != certificate.free
            })
            .collect();
        assert!(
            !partners.is_empty(),
            "the retained partner has its own original free terminal"
        );
        assert!(
            partners.iter().any(|partner| partner.guards != free.guards),
            "selector identities differ"
        );
        let proofs = field_support::audit(
            facts,
            &facts.field_support_inputs,
            &frozen.matched,
            &frozen.value_origins,
        );
        let field = proofs
            .iter()
            .find(|field| field.field_key == candidate.field_key)
            .unwrap();
        assert!(!field.supported(), "{field:#?}");
        assert!(field.stores.is_empty());
        assert!(
            field
                .holds
                .iter()
                .any(|hold| hold.reason == field_support::Pending::CompetingTerminal),
            "partner free must be retained as the reason, even though its selector is independent: {field:#?}"
        );
    });
}
