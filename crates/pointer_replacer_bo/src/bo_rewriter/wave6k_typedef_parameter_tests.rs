//! lil's typedef parameters (relay wave-6k/021 §2): a declaration whose type is
//! a one-level C typedef of a raw pointer (`pub type lil_env_t = *mut
//! _lil_env_t;`) reads `unsupported-decl-shape:alias` at the census. The
//! declaration family can name the pointee from the binding's own compiler
//! type, so the alias is resolved at the declaration and the reference form is
//! emitted; the alias itself is left alone.

use super::decision::Decision;

/// The lil shape: `lil_find_local_var(lil: lil_t, env: lil_env_t, …)`.
const TYPEDEF_PARAMETERS: &str = r#"
    #[repr(C)]
    pub struct _lil_env_t { pub vars: u64 }
    #[repr(C)]
    pub struct _lil_t { pub depth: u64 }
    pub type lil_env_t = *mut _lil_env_t;
    pub type lil_t = *mut _lil_t;
    pub unsafe fn lil_find_local_var(mut lil: lil_t, mut env: lil_env_t) -> u64 {
        if (*env).vars > 0 { (*lil).depth } else { 0 }
    }
"#;

fn emitted_signature(input: &str) -> String {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let capture = super::ast_transform::capture_ast(tcx).expect("original AST");
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("native decisions");
        let emission = super::emit_files(tcx, &table, &Default::default(), &ctx.retained_c9_plans)
            .expect("emission plan");
        let reverts = super::ast_transform::revert_set_from_classes_and_atoms(
            &emission.plan.held_classes(),
            &Default::default(),
            &table,
        )
        .expect("held classes");
        let source = super::ast_transform::ast_emitted_files_from(
            tcx,
            &capture,
            &reverts,
            emission.plan.root_file.as_ref(),
            &table,
            Some(&emission.plan.terminal_call_plans),
        )
        .expect("AST emission")
        .0
        .into_values()
        .next()
        .expect("one source");
        println!("EMITTED\n{source}");
        source
    })
    .expect("input compiles")
}

fn decisions(input: &str) -> Vec<(String, Decision)> {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (table, _) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("native decisions");
        table
            .entries
            .iter()
            .map(|(subject, decision)| {
                println!("DECISION {} {decision:?}", subject.label);
                (
                    subject.param_name.clone().unwrap_or_default(),
                    decision.clone(),
                )
            })
            .collect()
    })
    .expect("input compiles")
}

#[test]
fn wave6k_a_typedef_parameter_is_resolved_at_its_declaration() {
    let decided = decisions(TYPEDEF_PARAMETERS);
    for name in ["env", "lil"] {
        let decision = decided
            .iter()
            .find(|(n, _)| n == name)
            .map(|(_, d)| d.clone())
            .unwrap_or_else(|| panic!("no subject for {name}"));
        assert!(
            !matches!(
                decision,
                Decision::Degraded(ref degraded)
                    if degraded.reason.key() == "unsupported-decl-shape"
            ),
            "{name} must not be refused for its alias declaration: {decision:?}"
        );
    }
    let source = emitted_signature(TYPEDEF_PARAMETERS);
    let compact: String = source.chars().filter(|c| !c.is_whitespace()).collect();
    assert!(
        compact.contains("env:&crate::_lil_env_t")
            || compact.contains("env:&mutcrate::_lil_env_t")
            || compact.contains("env:Option<&crate::_lil_env_t>")
            || compact.contains("env:Option<&mutcrate::_lil_env_t>"),
        "the alias is resolved to the reference form at the declaration: {source}"
    );
    assert!(
        !compact.contains("env:lil_env_t"),
        "the alias itself must not survive at the declaration: {source}"
    );
}
