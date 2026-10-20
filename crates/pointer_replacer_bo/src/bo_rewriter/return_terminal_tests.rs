//! J13 scalar-return controls over real model and lifetime evidence.
//! No model/decision injection; the held contrast uses the existing class
//! revert harness after proving that both original classes are Ready.

use std::collections::BTreeSet;

use rustc_middle::mir::RETURN_PLACE;
use sha2::{Digest, Sha256};

use super::{
    bridge_receipt::{
        BridgeReceiptEvent, BridgeReceiptStage, BridgeReceiptState, BridgeRetentionTier,
        SignatureClassId,
    },
    decision::{
        Decision,
        exposure::{ConfiguredExposureInput, ExposureSurfacePlan},
        lifetime::FnSignatureSlot,
    },
    delivery_custody::{TypeShape, inventory_source},
};

// Exact source bytes from BR-W13's scalar choose fixture.
const CHOOSE: &str = "#![allow(dead_code, unused_unsafe, unused_mut, unused_variables)]\n\
    pub unsafe fn choose(p: *const i32) -> *const i32 { p }\n";

// Exact source bytes from LIFE-W1's mutable parameter-origin return fixture.
const KAZMATH: &str = "#![allow(dead_code, unused_unsafe)]\n\
    pub unsafe fn kazmath(p_out: *mut i32, add: *const i32) -> *mut i32 {\n\
        *p_out += *add;\n\
        p_out\n\
    }\n";

#[derive(Clone, Copy)]
struct Function {
    name: &'static str,
    parameter: &'static str,
    mutable: bool,
}

const CHOOSE_FUNCTION: Function = Function {
    name: "choose",
    parameter: "p",
    mutable: false,
};
const KAZMATH_FUNCTION: Function = Function {
    name: "kazmath",
    parameter: "p_out",
    mutable: true,
};

fn configured_exposure(name: &str) -> ConfiguredExposureInput {
    // Same checked fixture-config mechanism as BR-W13. A singleton name's
    // canonical bytes contain no trailing newline.
    ConfiguredExposureInput::checked(
        "fixture-config",
        [name.to_owned()],
        format!("{:x}", Sha256::digest(name.as_bytes())),
    )
    .expect("checked configured exposure for the actual fixture function")
}

fn terminal_event<'a>(
    events: &'a [BridgeReceiptEvent],
    owner: SignatureClassId,
    kind: &str,
) -> &'a BridgeReceiptEvent {
    let sites = events
        .iter()
        .filter(|event| event.site.owner_class == owner && event.site.bridge_kind == kind)
        .collect::<Vec<_>>();
    let plans = sites
        .iter()
        .filter(|event| event.stage == BridgeReceiptStage::Plan)
        .collect::<Vec<_>>();
    let terminal = sites
        .iter()
        .filter(|event| event.stage == BridgeReceiptStage::Terminal)
        .collect::<Vec<_>>();
    assert_eq!(
        plans.len(),
        1,
        "one exact {kind} plan for {owner:?}: {sites:#?}"
    );
    assert_eq!(
        terminal.len(),
        1,
        "one exact {kind} terminal for {owner:?}: {sites:#?}"
    );
    assert_eq!(
        plans[0].site, terminal[0].site,
        "plan/terminal return identity must agree"
    );
    terminal[0]
}

struct Output {
    baseline: String,
    held: Option<String>,
    lifetimes: Vec<(Function, String)>,
}

fn emit(input: &str, functions: &[Function], exposed: &str, hold_exposed: bool) -> Output {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("one original return-fixture AST capture");
        let (table, ctx) = super::decide_table_with_emission_config(
            tcx,
            Some((super::A5Mode::PreciseReplay, Some(super::WholeProgramAttestation::FrozenBenchmarkGraph))),
            &super::EmissionRunConfig { configured_exposure: configured_exposure(exposed) },
        ).expect("one real return-fixture decision pipeline");
        let solve = super::model_cache::solve_receipt();
        println!("J13 return fixture exposed={exposed}, hold={hold_exposed}: solve={solve:#?}");
        assert!(solve.is_some(), "the actual decision call must carry its solve receipt");
        let mut witnesses = Vec::new();
        for &function in functions {
            let label = format!("{}::{}", function.name, function.parameter);
            let (subject, decision) = table.entries.iter().find(|(subject, _)| subject.label == label)
                .expect("the fixture's real returning parameter subject");
            assert!(matches!(decision, Decision::Ref { mutable } if *mutable == function.mutable),
                "AUTHORING PREMISE: actual scalar return parameter decision: {label}, {decision:?}");
            for local in [subject.local, RETURN_PLACE] {
                let kind = ctx.slots.fn_local_slots.get(&subject.fn_did)
                    .and_then(|slots| slots.slot_for_local_depth(local, 0))
                    .and_then(|slot| ctx.model.get(&super::SlotRef::Local(subject.fn_did, slot))).copied();
                assert_eq!(kind, Some(super::SlotKind::Ref),
                    "AUTHORING PREMISE: actual source and return model-Ref: {label}, {local:?}");
            }
            let permit = ctx.lifetime_eligibility.return_permit((subject.fn_did, subject.hir_id))
                .expect("AUTHORING PREMISE: native production return permit, never a fabricated permit");
            let flow = ctx.analysis.origins.as_ref().and_then(|origins| origins.try_native_flows())
                .and_then(|flows| flows.get(&subject.fn_did)).expect("native original-input return flow");
            use crate::analyses::borrow_ownership::slots::SlotOwner;
            assert!(flow.body.depth0_value_flows().contains(&(
                SlotOwner::Local(subject.local), SlotOwner::Local(RETURN_PLACE))),
                "the exact parameter must flow to the native return slot");
            let lifetime_plan = table.lifetime_plan.function(subject.fn_did).expect("real return lifetime plan");
            let parameter_lifetime = lifetime_plan.lifetime_for(FnSignatureSlot::arg(1, 0, 0))
                .expect("first parameter lifetime");
            assert_eq!(lifetime_plan.lifetime_for(FnSignatureSlot::RETURN), Some(parameter_lifetime),
                "the return must reuse its origin parameter lifetime");
            assert!(lifetime_plan.receipt().contains("return_lifetime_reused=true"));
            assert_eq!(table.input_interfaces.return_forms.get(&subject.fn_did),
                Some(&super::decision::seam::Form::Raw), "the observed original return interface is raw");
            println!("J13 {label}: permit={permit:?}, lifetime_plan={}", lifetime_plan.receipt());
            witnesses.push((function, subject.fn_did, parameter_lifetime.to_owned(), lifetime_plan.digest()));
        }
        let exposed_did = witnesses.iter().find(|(function, _, _, _)| function.name == exposed)
            .expect("exposed function has its own real lifetime witness").1;
        assert_eq!(table.exposure.as_ref().expect("actual exposure policy").plan(exposed_did),
            ExposureSurfacePlan::PositiveSeedShim);
        let emission = super::emit_files(tcx, &table, &rustc_hash::FxHashSet::default(),
            &ctx.retained_c9_plans).expect("actual terminal return plan");
        let held = emission.plan.held_classes();
        for (_, did, _, _) in &witnesses {
            let owner = SignatureClassId::of(*did);
            assert!(emission.plan.class_finalization.classes.get(&owner)
                .is_some_and(super::plan::SignatureClassPlan::is_ready),
                "each real fixture class must be Ready before the contrast: {:?}", emission.plan.class_finalization);
            assert!(!held.contains(&owner));
        }
        let render = |held: &BTreeSet<SignatureClassId>| {
            let reverts = super::ast_transform::revert_set_from_classes_and_atoms(
                held, &BTreeSet::new(), &table).expect("existing class revert harness");
            let (files, _, _, _) = super::ast_transform::ast_emitted_files_from(
                tcx, &capture, &reverts, emission.plan.root_file.as_ref(), &table,
                Some(&emission.plan.terminal_call_plans)).expect("AST uses the real terminal call plans");
            assert_eq!(files.len(), 1, "complete single-file fixture emission");
            files.into_values().next().unwrap()
        };
        let baseline = render(&held);
        let events = emission.plan.bridge_events(&held);
        println!("J13 baseline exposed={exposed}: events={events:#?}\n{baseline}");
        for (function, did, _, digest) in &witnesses {
            let event = terminal_event(&events, SignatureClassId::of(*did), "return-raw-to-ref");
            assert_eq!(event.state, BridgeReceiptState::Applied);
            assert_eq!(event.site.caller, *did);
            assert!(event.site.position.contains(digest.as_str()), "return receipt retains its exact lifetime-plan digest");
            assert_eq!(event.expected_form, if function.mutable { "ref-mut" } else { "ref-shared" });
            assert_eq!(event.retention, BridgeRetentionTier::T1);
            assert!(event.waiver_id.is_none());
        }
        let surface = terminal_event(&events, SignatureClassId::of(exposed_did), "return-ref-to-raw");
        assert_eq!(surface.state, BridgeReceiptState::Applied);
        assert_eq!(surface.site.arm, "surface");
        assert_eq!(surface.expected_form, "raw");
        assert_eq!(surface.retention, BridgeRetentionTier::T1);
        assert!(surface.waiver_id.is_none());
        assert!(baseline.contains(&format!("fn __crat_safe_{exposed}")),
            "the live contrast must actually materialize the inner definition");

        let reverted = hold_exposed.then(|| {
            let owner = SignatureClassId::of(exposed_did);
            let mut withheld = held.clone();
            withheld.insert(owner);
            let output = render(&withheld);
            let events = emission.plan.bridge_events(&withheld);
            println!("J13 held-inner exposed={exposed}: withheld={withheld:?}, events={events:#?}\n{output}");
            assert!(events.iter().filter(|event| event.site.owner_class == owner
                && event.stage == BridgeReceiptStage::Terminal).all(|event| event.state == BridgeReceiptState::Dropped),
                "a held inner must not leave any Applied signature/return/wrapper receipt");
            assert_eq!(terminal_event(&events, owner, "return-raw-to-ref").state, BridgeReceiptState::Dropped);
            assert_eq!(terminal_event(&events, owner, "return-ref-to-raw").state, BridgeReceiptState::Dropped);
            for (function, did, _, _) in &witnesses {
                if function.name == exposed { continue; }
                assert_eq!(terminal_event(&events, SignatureClassId::of(*did), "return-raw-to-ref").state,
                    BridgeReceiptState::Applied, "the independent return class must remain live");
            }
            output
        });
        Output { baseline, held: reverted,
            lifetimes: witnesses.into_iter().map(|(function, _, lifetime, _)| (function, lifetime)).collect() }
    }).expect("the original return fixture type-checks")
}

fn assert_parameter(source: &str, owner: &str, parameter: &str, mutable: bool, raw: bool) {
    let declarations = inventory_source("return-terminal.rs", source)
        .expect("independent emitted declaration inventory");
    let declaration = declarations
        .iter()
        .find(|declaration| {
            declaration.owner == owner
                && declaration.binding == parameter
                && declaration.parameter_index == Some(1)
        })
        .expect("exact first-parameter declaration in emitted source");
    assert!(
        matches!(&declaration.type_shape,
        TypeShape::RawPointer { mutable: found, .. } if raw && *found == mutable)
            || matches!(&declaration.type_shape,
            TypeShape::Reference { mutable: found, .. } if !raw && *found == mutable),
        "the actual delivered parameter has the required form: {declaration:?}"
    );
}

fn normalized_function_header(source: &str, owner: &str) -> String {
    let needle = format!("fn {owner}");
    let starts = source
        .match_indices(needle.as_str())
        .filter_map(|(start, _)| {
            let next = source[start + needle.len()..].chars().next();
            matches!(next, Some('<' | '(' | ' ' | '\n' | '\r' | '\t')).then_some(start)
        })
        .collect::<Vec<_>>();
    assert_eq!(
        starts.len(),
        1,
        "one exact named function header for {owner}"
    );
    let source = &source[starts[0]..];
    let end = source.find('{').expect("the fixture function has a body");
    source[..end]
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

fn assert_live(output: &Output, exposed: &str) {
    assert!(
        super::verify::type_checks_str(&output.baseline),
        "J13 emitted return/wrapper must type/borrow-check:\n{}",
        output.baseline
    );
    for (function, lifetime) in &output.lifetimes {
        let owner = if function.name == exposed {
            format!("__crat_safe_{exposed}")
        } else {
            function.name.to_owned()
        };
        assert_parameter(
            &output.baseline,
            &owner,
            function.parameter,
            function.mutable,
            false,
        );
        let header = normalized_function_header(&output.baseline, &owner);
        assert!(header.starts_with(&format!("fn {owner}<'{lifetime}>")));
        let mutability = if function.mutable { "mut " } else { "" };
        assert!(
            header.contains(&format!(
                "{}: &'{lifetime} {mutability}i32",
                function.parameter
            )),
            "the exact parameter retains its proved lifetime and mutability: {header}"
        );
        assert!(
            header.ends_with(&format!(") -> &'{lifetime} {mutability}i32")),
            "the exact output return uses the proved parameter lifetime: {header}"
        );
        if function.name == exposed {
            assert_parameter(
                &output.baseline,
                exposed,
                function.parameter,
                function.mutable,
                true,
            );
            let view = if function.mutable {
                "from_mut"
            } else {
                "from_ref"
            };
            assert!(
                output
                    .baseline
                    .contains(&format!("core::ptr::{view}(__crat_result)")),
                "the raw wrapper must preserve the actual inner return mutability: {}",
                output.baseline
            );
        }
    }
}

#[test]
fn return_terminal_scalar_choose_reuses_its_native_parameter_lifetime() {
    let output = emit(CHOOSE, &[CHOOSE_FUNCTION], "choose", false);
    assert_live(&output, "choose");
}

#[test]
fn return_terminal_mutable_kazmath_wrapper_preserves_its_native_return() {
    let output = emit(KAZMATH, &[KAZMATH_FUNCTION], "kazmath", false);
    assert_live(&output, "kazmath");
}

#[test]
fn return_terminal_held_inner_restores_its_source_and_keeps_independent_return_live() {
    // Compose the two existing function bodies without changing either; keep
    // CHOOSE's crate attributes and drop only KAZMATH's duplicate attribute.
    let input = format!("{CHOOSE}{}", KAZMATH.split_once('\n').unwrap().1);
    let output = emit(&input, &[CHOOSE_FUNCTION, KAZMATH_FUNCTION], "choose", true);
    assert_live(&output, "choose");
    let held = output.held.as_ref().expect("held-inner output");
    assert!(
        super::verify::type_checks_str(held),
        "held-inner final output must type/borrow-check:\n{held}"
    );
    assert_parameter(held, "choose", "p", false, true);
    assert!(
        !held.contains("__crat_safe_choose"),
        "no generated definition or call may survive the held inner:\n{held}"
    );
    assert!(
        held.contains("fn choose(p: *const i32) -> *const i32 { p }"),
        "the held return expression and raw signature must restore their original source:\n{held}"
    );
    assert_parameter(held, "kazmath", "p_out", true, false);
}

fn assert_named_lifetime_wrapper_consumer(borrowed_type: &str, mutable: bool) {
    // These are consumer controls over an explicitly constructed transformed
    // signature. They claim no model admission, origin permit, or execution.
    let emitted = rustc_span::create_session_globals_then(
        rustc_span::edition::Edition::Edition2018,
        &[],
        None,
        || {
            let session = rustc_session::parse::ParseSess::new(
                rustc_driver::DEFAULT_LOCALE_RESOURCES.to_vec(),
            );
            let inner_source =
                format!("unsafe fn inner<'view>(p: {borrowed_type}) -> {borrowed_type} {{ p }}");
            let inner_crate = super::slice_use_inventory_tests::parse_crate(
                &session,
                "constructed-inner.rs",
                &inner_source,
            )
            .expect("explicit transformed signature parses");
            assert_eq!(inner_crate.items.len(), 1);
            let rustc_ast::ItemKind::Fn(inner) = &inner_crate.items[0].kind else {
                panic!("constructed transformed item must be a function");
            };
            // The raw wrapper has no named lifetime. Its result temporary
            // elides the lifetime while preserving the entire borrowed form.
            let temporary_type = borrowed_type.replace("'view ", "");
            let block =
                super::ast_transform::surface_wrapper_block("inner", inner, Some(&temporary_type))
                    .expect("actual production wrapper builder");
            let raw_type = if mutable { "*mut i32" } else { "*const i32" };
            let wrapper_source =
                format!("pub unsafe fn wrapper(p: {raw_type}) -> {raw_type} {{ loop {{}} }}");
            let mut wrapper_crate = super::slice_use_inventory_tests::parse_crate(
                &session,
                "constructed-wrapper.rs",
                &wrapper_source,
            )
            .expect("raw wrapper signature parses");
            let rustc_ast::ItemKind::Fn(wrapper) = &mut wrapper_crate.items[0].kind else {
                panic!("raw wrapper item must be a function");
            };
            wrapper.body = Some(block);
            // Supply the production helper's named fallback for compilation;
            // this constant is not asserted to be observed length evidence.
            format!(
                "#![allow(dead_code, unused_unsafe)]\n\
                 const FALLBACK_SLICE_EXTENT: usize = 1024;\n\
                 {inner_source}\n{}\n",
                rustc_ast_pretty::pprust::item_to_string(&wrapper_crate.items[0]),
            )
        },
    );
    println!("J13 wrapper consumer borrowed_type={borrowed_type}, mutable={mutable}:\n{emitted}");
    assert!(
        super::verify::type_checks_str(&emitted),
        "named lifetime must not change borrowed parameter/return shape: {borrowed_type}\n{emitted}"
    );
}

#[test]
fn return_wrapper_consumer_named_lifetime_shared_slice() {
    assert_named_lifetime_wrapper_consumer("&'view [i32]", false);
}

#[test]
fn return_wrapper_consumer_named_lifetime_mutable_slice() {
    assert_named_lifetime_wrapper_consumer("&'view mut [i32]", true);
}

#[test]
fn return_wrapper_consumer_named_lifetime_shared_option_ref() {
    assert_named_lifetime_wrapper_consumer("Option<&'view i32>", false);
}

#[test]
fn return_wrapper_consumer_named_lifetime_mutable_option_ref() {
    assert_named_lifetime_wrapper_consumer("Option<&'view mut i32>", true);
}

#[test]
fn return_wrapper_consumer_named_lifetime_shared_option_slice() {
    assert_named_lifetime_wrapper_consumer("Option<&'view [i32]>", false);
}

#[test]
fn return_wrapper_consumer_named_lifetime_mutable_option_slice() {
    assert_named_lifetime_wrapper_consumer("Option<&'view mut [i32]>", true);
}
