//! Relay006 accumulator checkpoint: actual bodies, native model and emission.
use std::sync::OnceLock;

use super::{
    A5Mode, WholeProgramAttestation,
    decision::{Decision, nested_slice::Hold},
};

const SOURCE: &str = include_str!("wave5d_accumulator_fixture.rs");
#[allow(
    dead_code,
    unused_assignments,
    unused_variables,
    unused_mut,
    unsafe_op_in_unsafe_fn
)]
#[path = "wave5d_accumulator_fixture.rs"]
mod original;

fn with_table(source: &str, f: impl Fn(super::decision::DecisionTable) + Send + Sync) {
    ::utils::compilation::run_compiler_on_str(source, |tcx| {
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        for (s, _) in &table.entries {
            if source != SOURCE
                || tcx.def_path_str(s.fn_did.to_def_id()) != "indicators::ad::ti_ad"
                || s.ptr_depth != 2
            {
                continue;
            }
            for depth in 0..2 {
                let slot = ctx.slots.fn_local_slots[&s.fn_did]
                    .slot_for_local_depth(s.local, depth)
                    .unwrap();
                assert_eq!(
                    ctx.model.get(&super::SlotRef::Local(s.fn_did, slot)),
                    Some(&super::SlotKind::Ref)
                );
            }
        }
        f(table);
    })
    .unwrap();
}
fn emitted() -> &'static str {
    static AFTER: OnceLock<String> = OnceLock::new();
    AFTER.get_or_init(|| {
        let dir = std::env::temp_dir().join(format!("crat-wave5d-acc-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let root = dir.join("lib.rs");
        std::fs::write(&root, SOURCE).unwrap();
        let result = super::rewrite_m1_path_a5_injected(
            &root,
            A5Mode::PreciseReplay,
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            &|_| {},
        );
        std::fs::remove_dir_all(dir).unwrap();
        let super::RewriteOutcome::Emitted {
            source,
            reverted_count,
            ..
        } = result
        else {
            panic!("accumulator emission failed");
        };
        assert_eq!(reverted_count, 0);
        println!("W5D-ACC-EMITTED\n{source}\nW5D-ACC-END");
        source
    })
}
#[test]
fn w5d_acc_ad_native_inherits_five_existing_formations() {
    with_table(SOURCE, |table| {
        let plans = table
            .nested_receipts
            .iter()
            .filter_map(|r| r.result.as_ref().ok())
            .collect::<Vec<_>>();
        assert_eq!(plans.len(), 1, "ad positive; prefix functions stay held");
        assert_eq!(plans[0].rows.len(), 5);
        assert_eq!(plans[0].parameters.len(), 2);
        assert!(plans[0].accumulator.is_some());
        assert_eq!(plans[0].conditional_updates.len(), 1);
        for row in &plans[0].rows {
            let c = table
                .slice_constructions
                .iter()
                .find(|c| c.node == (plans[0].owner, row.local))
                .unwrap();
            assert_eq!(c.length.expression, "size");
            assert!(!c.length.is_fallback());
        }
        println!("W5D-ACC-PLAN {:?}", plans[0]);
        assert_eq!(
            table
                .entries
                .iter()
                .filter(|(_, d)| matches!(d, Decision::NestedSlice { .. }))
                .count(),
            2
        );
    });
}
#[test]
fn w5d_acc_ad_emits_nested_tables_and_evidence_lengths() {
    let source = emitted();
    let compact = source.split_whitespace().collect::<String>();
    let helper = compact
        .split("fn__crat_safe_ti_ad(")
        .nth(1)
        .unwrap()
        .split("pubmod")
        .next()
        .unwrap();
    assert!(helper.contains("inputs:&[&[std::os::raw::c_double]]"));
    assert!(helper.contains("outputs:&mut[&mut[std::os::raw::c_double]]"));
    assert!(!helper.contains("FALLBACK_SLICE_EXTENT"));
    assert!(helper.contains("ifhl!=0.0f64"));
    assert!(helper.contains("sum+="));
}
fn held(source: &str) {
    with_table(source, |table| {
        assert!(
            !table.nested_receipts.iter().any(|r| r.result.is_ok()),
            "no widened native admission"
        );
    });
}
#[test]
fn w5d_acc_nonzero_initial_accumulator_is_not_this_rule() {
    held(&SOURCE.replacen(
        "0 as std::os::raw::c_int as std::os::raw::c_double",
        "1 as std::os::raw::c_int as std::os::raw::c_double",
        1,
    ));
}
#[test]
fn w5d_acc_effectful_initializer_is_held() {
    held(&SOURCE.replacen(
        "0 as std::os::raw::c_int as std::os::raw::c_double",
        "{ size += 1; 0.0 }",
        1,
    ));
}
#[test]
fn w5d_acc_count_write_in_conditional_update_is_held() {
    held(&SOURCE.replacen("if hl != 0.0f64 {", "if hl != 0.0f64 { size += 1;", 1));
}
#[test]
fn w5d_acc_index_write_in_conditional_update_is_held() {
    held(&SOURCE.replacen("if hl != 0.0f64 {", "if hl != 0.0f64 { i += 1;", 1));
}
#[test]
fn w5d_acc_scalar_call_in_conditional_update_is_held() {
    let source = format!(
        "fn effect(v:f64)->f64{{v}}\n{}",
        SOURCE.replacen(
            "if hl != 0.0f64 {",
            "if hl != 0.0f64 { crate::effect(sum);",
            1
        )
    );
    held(&source);
}
#[test]
fn w5d_acc_pointer_write_in_conditional_update_is_held() {
    held(&SOURCE.replacen(
        "if hl != 0.0f64 {",
        "if hl != 0.0f64 { output = output.offset(1);",
        1,
    ));
}
#[test]
fn w5d_acc_reference_in_conditional_update_is_held() {
    held(&SOURCE.replacen(
        "if hl != 0.0f64 {",
        "if hl != 0.0f64 { let r = &mut sum; *r += 1.0;",
        1,
    ));
}
#[test]
fn w5d_acc_scalar_prelude_must_follow_every_table_load() {
    let declaration = regex::Regex::new(r"let mut sum:[^;]+;")
        .unwrap()
        .find(SOURCE)
        .unwrap()
        .as_str();
    let source = SOURCE.replacen(declaration, "", 1).replacen(
        "let mut low:",
        &format!("{declaration} let mut low:"),
        1,
    );
    held(&source);
}
#[test]
fn w5d_acc_prefix_sources_write_even_when_size_is_nonpositive() {
    let close = [7.0];
    let volume = [2.0];
    let options = [2.0];
    for size in [0, -1] {
        let mut output = [99.0];
        let inputs = [close.as_ptr(), volume.as_ptr()];
        let outputs = [output.as_mut_ptr()];
        // Safety: initialized table cells and one valid element at every
        // unconditional source prefix access; loop is not entered.
        unsafe {
            original::INDICATORS[1].unwrap()(
                size,
                inputs.as_ptr(),
                options.as_ptr(),
                outputs.as_ptr(),
            );
        }
        assert_eq!(output, [7.0]);
        output[0] = 99.0;
        // Safety: obv's initial output write and close[0] read are valid;
        // its size-one loop is not entered for these inputs.
        let outputs = [output.as_mut_ptr()];
        unsafe {
            original::INDICATORS[2].unwrap()(
                size,
                inputs.as_ptr(),
                options.as_ptr(),
                outputs.as_ptr(),
            );
        }
        assert_eq!(output, [0.0]);
    }
}
#[test]
fn w5d_acc_prefix_is_typed_held() {
    with_table(SOURCE, |table| {
        let owners = table
            .entries
            .iter()
            .filter(|(s, _)| s.label.starts_with("ti_edecay::") || s.label.starts_with("ti_obv::"))
            .map(|(s, _)| s.fn_did)
            .collect::<rustc_hash::FxHashSet<_>>();
        let prefix = table
            .nested_receipts
            .iter()
            .filter(|r| owners.contains(&r.owner))
            .filter_map(|r| r.result.as_ref().err())
            .collect::<Vec<_>>();
        assert_eq!(prefix.len(), 2);
        assert!(
            prefix.iter().all(|h| matches!(h, Hold::IntervalChanged)),
            "initial prefix hold"
        );
    });
}

fn function_body<'a>(source: &'a str, name: &str) -> &'a str {
    let begin = source.find(&format!("fn {name}(")).unwrap();
    let braces = source[begin..].find('{').unwrap() + begin;
    let mut depth = 0;
    for (i, c) in source[braces..].char_indices() {
        if c == '{' {
            depth += 1;
        } else if c == '}' {
            depth -= 1;
            if depth == 0 {
                return &source[begin..braces + i + 1];
            }
        }
    }
    panic!("function body must close")
}
#[test]
fn w5d_acc_prefix_emission_receives_no_new_nonpositive_guard() {
    for name in ["ti_edecay", "ti_obv"] {
        let outer = function_body(emitted(), name);
        let inner = function_body(emitted(), &format!("__crat_safe_{name}"));
        assert!(!outer.contains("__crat_nested_"));
        assert!(
            !inner
                .split_whitespace()
                .collect::<String>()
                .contains("size<=0")
        );
        assert!(inner.contains("output"));
    }
}
#[test]
fn w5d_acc_ad_nonpositive_guard_remains_before_all_new_views() {
    let outer = function_body(emitted(), "ti_ad");
    assert!(outer.find("return 0").unwrap() < outer.find("::core::slice::from_raw_parts").unwrap());
    assert_eq!(outer.matches(".add(").count(), 5);
    assert_eq!(outer.matches("__crat_nested_count =").count(), 1);
}
#[test]
fn w5d_acc_conditional_volume_use_is_not_claimed_as_unconditional() {
    let inner = function_body(emitted(), "__crat_safe_ti_ad")
        .split_whitespace()
        .collect::<String>();
    assert!(inner.contains("ifhl!=0.0f64{sum+="));
    assert!(inner.contains("volume[(i)asusize]"));
    assert_eq!(inner.matches("volume[(i)asusize]").count(), 1);
}
#[test]
fn w5d_acc_runtime_matches_original_for_zero_width_and_nan_rows() {
    let main = r#"
fn same(a:f64,b:f64)->bool { a==b || (a.is_nan()&&b.is_nan()) }
fn main() {
    let low=[0.0,5.0,4.0];let close=[10.0,7.0,4.0];let volume=[3.0,1.0,2.0];let option=0.0;
    for high in [[10.0,5.0,8.0],[f64::NAN,5.0,8.0],[0.0,5.0,4.0]] {
        let input=[high.as_ptr(),low.as_ptr(),close.as_ptr(),volume.as_ptr()];
        let mut before=[0.0;3];let before_ptrs=[before.as_mut_ptr()];
        let mut after=[0.0;3];let after_ptrs=[after.as_mut_ptr()];
        // Safety: four immutable initialized rows and one independent writable
        // row, each three elements, remain valid through each call.
        unsafe { original::INDICATORS[0].unwrap()(3,input.as_ptr(),&option,before_ptrs.as_ptr());
                 INDICATORS[0].unwrap()(3,input.as_ptr(),&option,after_ptrs.as_ptr()); }
        for i in 0..3 { assert!(same(before[i],after[i])); }
    }
    let empty_inputs=[std::ptr::null::<f64>();4];let empty_outputs=[std::ptr::null_mut::<f64>()];
    for n in [i32::MIN,-1,0] {
        // Safety: readable pointer-table cells; the original ad loop and the
        // emitted early return make no inner access for a nonpositive size.
        unsafe { assert_eq!(original::INDICATORS[0].unwrap()(n,empty_inputs.as_ptr(),std::ptr::null(),empty_outputs.as_ptr()),0);
                 assert_eq!(INDICATORS[0].unwrap()(n,empty_inputs.as_ptr(),std::ptr::null(),empty_outputs.as_ptr()),0); }
    }
}
"#;
    let source = format!(
        "#[allow(dead_code,unused_assignments,unused_mut,unused_variables,unsafe_op_in_unsafe_fn)] mod original {{ {SOURCE} }}\n{}\n{main}",
        emitted()
    );
    let dir = std::env::temp_dir().join(format!("crat-wave5d-ad-runtime-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let input = dir.join("main.rs");
    let binary = dir.join("run");
    std::fs::write(&input, source).unwrap();
    let compiled = std::process::Command::new("rustc")
        .arg("--edition=2021")
        .arg(&input)
        .arg("-o")
        .arg(&binary)
        .output()
        .unwrap();
    assert!(
        compiled.status.success(),
        "{}",
        String::from_utf8_lossy(&compiled.stderr)
    );
    let run = std::process::Command::new(&binary).output().unwrap();
    assert!(
        run.status.success(),
        "{}",
        String::from_utf8_lossy(&run.stderr)
    );
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn w5d_acc_other_scalar_binding_is_not_the_accumulator() {
    let source = SOURCE
        .replacen("let hl:", "let mut hl:", 1)
        .replacen("sum +=", "hl +=", 1);
    held(&source);
}
