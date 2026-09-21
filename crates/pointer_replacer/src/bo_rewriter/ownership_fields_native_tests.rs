//! Native pipeline coverage on tiny heman-shaped sources. These assert the
//! native grants/holds; none inject Owning model bits. R365's source bundle
//! supplies the proof obligations for the two positive caller-live reductions.

use super::decision::Decision;

/// R492-4 (relay 061): under wave-6a's A9 this fixture's callee formals
/// convert — `(input:*mut f32,output:*mut f32)` becomes `(input:&f32,output:
/// &mut f32)` — and then they emit as subjects of their own, so the emitted
/// count is the caller's two owning locals PLUS the callee's two. Which frame
/// produced a source is readable in its own signature, so the expectation
/// stays exact on both instead of becoming a range.
pub(super) fn expected_native_emitted(source: &str) -> usize {
    if source.contains("(input:*mut f32,output:*mut f32)") {
        2
    } else {
        4
    }
}

pub(super) fn native_fixture_source(callee: &str, body: &str) -> String {
    format!(
        r#"
        #![allow(dead_code,unused_unsafe,unused_mut)]
        extern "C" {{
            fn calloc(count:usize,size:usize)->*mut core::ffi::c_void;
            fn free(ptr:*mut core::ffi::c_void);
        }}
        unsafe fn {callee}(input:*mut f32,output:*mut f32) {{ *output=*input+1.0; }}
        pub unsafe fn transform_to_coordfield()->f32 {{
            let mut pl1=calloc(2,core::mem::size_of::<f32>()) as *mut f32;
            let mut pl2=calloc(2,core::mem::size_of::<f32>()) as *mut f32;
            *pl1=3.0;
            {body}
            let result=*pl1+*pl2;
            free(pl1 as *mut core::ffi::c_void);
            free(pl2 as *mut core::ffi::c_void);
            result
        }}
        "#,
    )
}

#[test]
fn r376_native_conditional_lend_bundle_is_admitted() {
    require_native_r365_bundle(
        "edt_with_payload",
        "if *pl1 > 0.0 { edt_with_payload(pl1,pl2); }",
        1,
    );
}

#[test]
fn r376_native_loop_repeated_caller_lend_bundle_is_admitted() {
    require_native_r365_bundle("edt", "while *pl1 > 0.0 { edt(pl1,pl2); *pl1=0.0; }", 1);
}

fn require_native_r365_bundle(callee_name: &str, calls: &str, expected_calls: usize) {
    use super::decision::{a5_site_proof::A5SiteProofVerdict, raw_boundary::RetentionVerdict};
    let source = native_fixture_source(callee_name, calls);
    ::utils::compilation::run_compiler_on_str(&source, |tcx| {
        let (table, ctx) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .unwrap();
        let program = super::collect_program(tcx);
        let effects = super::decision::ownership_fields_effects::NativeEffects::derive(&program);
        let callee = *program
            .functions
            .iter()
            .find(|id| tcx.def_path_str(id.to_def_id()) == callee_name)
            .unwrap();
        let caller = *program
            .functions
            .iter()
            .find(|id| tcx.def_path_str(id.to_def_id()) == "transform_to_coordfield")
            .unwrap();
        let mut grouped = std::collections::BTreeMap::<_, Vec<_>>::new();
        for site in &ctx.raw_boundary_sites.sites {
            if site.callee_local != Some(callee) {
                continue;
            }
            let retention = ctx.retention.get(callee, site.key.argument_index);
            let no_consume = effects.certify(callee, site.key.argument_index);
            println!(
                "R365_NATIVE_EDGE {:?} retention={retention:?} nonconsuming={:?}",
                site.key,
                no_consume.as_ref().map(|_| "proved")
            );
            let Some(RetentionVerdict::NoRetain { certificate }) = retention else {
                panic!("native T1 premise is absent: {retention:?}");
            };
            ctx.retention
                .verify_certificate(callee, site.key.argument_index, certificate)
                .unwrap();
            assert!(no_consume.is_ok());
            grouped
                .entry((site.key.block, site.key.statement_index))
                .or_default()
                .push(site);
        }
        assert_eq!(grouped.len(), expected_calls);
        for (location, mut sites) in grouped {
            sites.sort_by_key(|s| s.key.argument_index);
            assert_eq!(sites.len(), 2);
            let proof = ctx.a5_site_proofs.lookup(
                caller.local_def_index.as_u32(),
                callee.local_def_index.as_u32(),
                0,
                1,
                sites[0].source_span,
                sites[1].source_span,
            );
            println!("R365_NATIVE_PAIR {location:?} {proof:?}");
            assert_eq!(
                proof.verdict,
                A5SiteProofVerdict::Clear,
                "native disjointness premise"
            );
        }
        println!(
            "R365_NATIVE_CALLER_MIR {:#?}",
            tcx.mir_drops_elaborated_and_const_checked(caller)
                .borrow()
                .basic_blocks
        );
        for (subject, decision) in &table.entries {
            if subject.fn_did == callee || subject.fn_did == caller {
                println!("R365_NATIVE_SUBJECT {} {decision:?}", subject.label);
            }
        }
        let owners: Vec<_> = table
            .entries
            .iter()
            .filter(|(s, _)| {
                s.fn_did == caller && matches!(s.param_name.as_deref(), Some("pl1" | "pl2"))
            })
            .collect();
        assert_eq!(owners.len(), 2);
        assert!(
            owners.iter().all(|(_, d)| matches!(d, Decision::Box(_))),
            "R365 first native bundle must admit both actual Owning locals"
        );
    })
    .unwrap();
}

#[test]
fn r365_native_two_buffer_bundle_is_admitted() {
    require_native_r365_bundle("edt_with_payload", "edt_with_payload(pl1,pl2);", 1);
}

#[test]
fn r365_native_repeated_call_bundle_is_admitted() {
    require_native_r365_bundle("edt", "edt(pl1,pl2);*pl1=*pl2;edt(pl1,pl2);", 2);
}

fn check_r365_emitted(callee: &str, calls: &str) {
    let input = native_fixture_source(callee, calls);
    // The normal pipeline, no injected decisions, no census/probe invocation.
    let outcome = super::rewrite_core_injected(
        ::utils::compilation::str_to_input(&input),
        None,
        super::MAX_REVERT_ROUNDS,
        &|_| {},
        false,
        false,
        false,
        Some((
            super::A5Mode::PreciseReplay,
            Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
        )),
    );
    let super::RewriteOutcome::Emitted {
        source,
        emitted_count,
        reverted_count,
        unplaceable,
        ..
    } = outcome
    else {
        panic!("native emission refused: {outcome:?}");
    };
    println!("R365_EMITTED_BEGIN {callee}\n{source}\nR365_EMITTED_END {callee}");
    assert_eq!(
        emitted_count,
        expected_native_emitted(&source),
        "both native owning locals survive (plus the callee's formals where A9 converts them)"
    );
    assert_eq!(reverted_count, 0);
    assert!(unplaceable.is_empty());
    assert!(super::verify::type_checks_str(&source));
    for name in ["pl1", "pl2"] {
        assert_eq!(
            source.matches(&format!("drop({name})")).count(),
            1,
            "one exact C free -> drop"
        );
    }
    // Read actual inferred types from the final compiled output, not type
    // strings proposed by BoxPlan or a count of intended declarations.
    ::utils::compilation::run_compiler_on_str(&source, |tcx| {
        let program = super::collect_program(tcx);
        let caller = *program
            .functions
            .iter()
            .find(|id| tcx.def_path_str(id.to_def_id()) == "transform_to_coordfield")
            .unwrap();
        let target = *program
            .functions
            .iter()
            .find(|id| tcx.def_path_str(id.to_def_id()) == callee)
            .unwrap();
        let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
        for name in ["pl1", "pl2"] {
            let roots: Vec<_> = body
                .var_debug_info
                .iter()
                .filter(|info| info.name.as_str() == name)
                .filter_map(|info| match info.value {
                    rustc_middle::mir::VarDebugInfoContents::Place(place) => Some(place),
                    _ => None,
                })
                .collect();
            assert_eq!(roots.len(), 1, "unique final native owner identity");
            let ty = roots[0].ty(&body.local_decls, tcx).ty;
            assert!(ty.is_box(), "final {name} is {ty}");
            println!(
                "R365_CUSTODY {name} local={} type={ty}",
                roots[0].local.as_u32()
            );
        }
        let sig = tcx.fn_sig(target.to_def_id()).skip_binder().skip_binder();
        assert_eq!(sig.inputs().len(), 2);
        // R492-4 (relay 061): whether the callee's formals stay raw is the
        // FRAME's answer — here they do, and under wave-6a's A9 they are
        // `&f32` / `&mut f32`. Either way the caller's owners keep their Box
        // custody (asserted above) and the formals are uniform: a lend never
        // leaves one of a pair converted and the other raw.
        let raw: Vec<_> = sig
            .inputs()
            .iter()
            .map(|ty| matches!(ty.kind(), rustc_middle::ty::TyKind::RawPtr(..)))
            .collect();
        assert!(
            raw.iter().all(|r| *r) || raw.iter().all(|r| !*r),
            "the pair's formals are converted together: {sig:?}"
        );
    })
    .unwrap();
    let drops = super::verify::box_mir_drops_str(&source).unwrap();
    let policies: Vec<_> = ["pl1", "pl2"]
        .into_iter()
        .map(|name| super::verify::BoxMirDropPolicy {
            subject: format!("transform_to_coordfield::{name}"),
            function: "transform_to_coordfield".into(),
            local_name: Some(name.into()),
            overwrite_sites: Vec::new(),
            retained_sink: true,
            optional: false,
            implicit_scope_close: false,
        })
        .collect();
    // The native source/T1 proof supplied authorization before emission. This
    // separate emitted-MIR check accounts for every observed implicit close.
    let receipt = super::verify::reconcile_box_mir_drop_policies(&drops, &policies).unwrap();
    assert!(
        drops.iter().all(|drop| drop.cleanup),
        "no extra normal-path drop"
    );
    println!("R365_DROP_CUSTODY_BEGIN {callee}\n{receipt}R365_DROP_CUSTODY_END {callee}");
    let raw_callee =
        format!("unsafe fn {callee}(input:*mut f32,output:*mut f32) {{ *output=*input+1.0; }}");
    let moved_callee = format!(
        "unsafe fn {callee}(input: ::std::boxed::Box<[f32]>,mut output: ::std::boxed::Box<[f32]>) {{ output[0]=input[0]+1.0; }}"
    );
    // R492-4 (relay 061): the counterfactual is frame-independent — replacing
    // the lend with a CONSUMING formal must make the owner's later use
    // illegal — but the text it starts from is not. Under wave-6a's A9 the
    // callee reads `(input:&f32,output:&mut f32)` and the lend is the thin
    // reference arm, so the substitution takes whichever spelling this frame
    // emitted and the E0382 expectation below is unchanged.
    let reference_callee =
        format!("unsafe fn {callee}(input:&f32,output:&mut f32) {{ *output=*input+1.0; }}");
    let emitted_callee = if source.contains(&raw_callee) {
        raw_callee.clone()
    } else {
        reference_callee.clone()
    };
    assert_eq!(
        source.matches(&emitted_callee).count(),
        1,
        "exact emitted callee mutation"
    );
    let mut moved = source.replace(&emitted_callee, &moved_callee);
    for name in ["pl1", "pl2"] {
        let view = [
            format!("<[_]>::as_mut_ptr(&mut *({name}))"),
            format!("&mut (*({name}))[0]"),
            format!("&(*({name}))[0]"),
        ]
        .into_iter()
        .find(|view| moved.contains(view))
        .unwrap_or_else(|| panic!("no lend view for {name} in {moved}"));
        moved = moved.replace(&view, name);
    }
    let rejected = super::verify::diagnose_str(&moved);
    for name in ["pl1", "pl2"] {
        assert!(
            rejected.diags.iter().any(|diag| matches!(
                diag.code.as_deref(),
                Some("E0382" | "ErrCode(382)")
            ) && diag.message.contains(name)),
            "native move-for-lend must reject later use of {name}: {:?}",
            rejected.diags
        );
    }
    println!(
        "R365_NATIVE_MOVE_FAULT_BEGIN {callee}\n{moved}\nR365_NATIVE_MOVE_FAULT_END {callee}\nR365_NATIVE_MOVE_DIAGNOSTICS {callee} {:?}",
        rejected.diags
    );
}

#[test]
fn r365_native_two_buffer_emission_compiles_with_box_custody() {
    check_r365_emitted("edt_with_payload", "edt_with_payload(pl1,pl2);");
}

#[test]
fn r365_native_repeated_call_emission_compiles_with_box_custody() {
    check_r365_emitted("edt", "edt(pl1,pl2);*pl1=*pl2;edt(pl1,pl2);");
}

fn hygienic_output(prefix: &str) -> String {
    let input = native_fixture_source("edt_with_payload", "edt_with_payload(pl1,pl2);").replace(
        "#![allow(dead_code,unused_unsafe,unused_mut)]",
        &format!("#![allow(dead_code,unused_unsafe,unused_mut)]\n{prefix}"),
    );
    let outcome = super::rewrite_core_injected(
        ::utils::compilation::str_to_input(&input),
        None,
        super::MAX_REVERT_ROUNDS,
        &|_| {},
        false,
        false,
        false,
        Some((
            super::A5Mode::PreciseReplay,
            Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
        )),
    );
    let super::RewriteOutcome::Emitted {
        source,
        emitted_count,
        reverted_count,
        ..
    } = outcome
    else {
        panic!("{outcome:?}")
    };
    assert_eq!(
        (emitted_count, reverted_count),
        (expected_native_emitted(&source), 0)
    );
    source
}

#[test]
fn r365_native_hygiene_free_cannot_resolve_to_forget() {
    let source = hygienic_output("use ::std::mem::forget as drop;");
    let drops = ::utils::compilation::run_compiler_on_str(&source, |tcx| {
        let program = super::collect_program(tcx);
        let caller = *program
            .functions
            .iter()
            .find(|id| tcx.def_path_str(id.to_def_id()) == "transform_to_coordfield")
            .unwrap();
        let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
        body.basic_blocks
            .iter()
            .filter(|block| {
                let rustc_middle::mir::TerminatorKind::Call { func, .. } = &block.terminator().kind
                else {
                    return false;
                };
                let Some(constant) = func.constant() else { return false };
                matches!(constant.ty().kind(),rustc_middle::ty::TyKind::FnDef(did,args)
                if tcx.is_diagnostic_item(rustc_span::Symbol::intern("mem_drop"),*did)
                && args.types().any(|ty|ty.is_box()))
            })
            .count()
    })
    .unwrap();
    assert_eq!(
        drops, 2,
        "both exact source frees must resolve to standard Box drop: {source}"
    );
}

fn run_hygienic_program(prefix: &str) {
    let mut source = hygienic_output(prefix);
    // Only the emitted owned program is executed. The fault's empty vector
    // panics at safe indexing before either raw callee dereference is reached.
    source.push_str("\nfn main() { assert_eq!(unsafe { transform_to_coordfield() }, 7.0); }\n");
    static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let id = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("crat-r365-hygiene-{}-{id}", std::process::id()));
    std::fs::create_dir(&dir).unwrap();
    let path = dir.join("main.rs");
    let executable = dir.join("out");
    std::fs::write(&path, &source).unwrap();
    let compile = std::process::Command::new("rustc")
        .arg("--edition=2021")
        .arg(&path)
        .arg("-o")
        .arg(&executable)
        .output()
        .unwrap();
    let run = compile
        .status
        .success()
        .then(|| std::process::Command::new(&executable).output().unwrap());
    std::fs::remove_dir_all(&dir).unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );
    let run = run.unwrap();
    assert!(
        run.status.success(),
        "generated operation was captured by the input: {}\n{source}",
        String::from_utf8_lossy(&run.stderr)
    );
}

#[test]
fn r365_native_hygiene_constructor_cannot_invoke_input_vec_macro() {
    run_hygienic_program("macro_rules! vec { ($($t:tt)*) => { ::std::vec![0.0f32; 0] }; }");
}

#[test]
fn r365_native_hygiene_view_cannot_invoke_input_trait_method() {
    run_hygienic_program(
        "trait Trap { fn as_mut_ptr(&mut self) -> *mut f32; } impl Trap for ::std::boxed::Box<[f32]> { fn as_mut_ptr(&mut self) -> *mut f32 { panic!(\"captured view\") } }",
    );
}
