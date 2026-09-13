use crate::{
    analyses::borrow_ownership::a5_overlap::{A5Mode, WholeProgramAttestation},
    bo_rewriter::{
        self,
        decision::{Decision, DegradeReason},
    },
};

fn native_pair(input: &str) {
    ::utils::compilation::run_compiler_on_input(::utils::compilation::str_to_input(input), |tcx| {
        let (table, _) = bo_rewriter::decide_table_with_ctx_config(
            tcx,
            Some((A5Mode::PreciseReplay, Some(WholeProgramAttestation::FrozenBenchmarkGraph))),
        ).expect("native pair decision");
        for (subject, decision) in &table.entries {
            println!("{} {:?} {:?}", subject.label, subject.kind, decision);
        }
        for proof in &table.seams.overlap_proofs {
            println!("{} => {} #{} expected={:?} found={:?} fallback={:?}",
                tcx.def_path_str(proof.caller.to_def_id()), tcx.def_path_str(proof.callee.to_def_id()),
                proof.index, proof.expected_form, proof.found_form, proof.fallback);
        }
        let peers = table.entries.iter().filter(|(s, _)| tcx.item_name(s.fn_did.to_def_id()).as_str() == "read_pair").collect::<Vec<_>>();
        assert_eq!(peers.len(), 2);
        assert!(peers.iter().all(|(_, d)| !matches!(d, Decision::Degraded(g) if g.reason == DegradeReason::PairRawView)), "shared reader parameters must not acquire raw pair roles");
    }).expect("fixture compilation");
}

#[test]
fn w5p_native_shared_pair_baseline() {
    native_pair(
        r#"
        pub unsafe fn read_pair(a: *const i32, b: *const i32) -> bool { *a == *b }
        pub unsafe fn caller(p: *mut i32) -> bool { read_pair(p, p) }
    "#,
    );
}

#[test]
fn w5p_native_mutable_caller_shared_pair() {
    native_pair(
        r#"
        pub unsafe fn read_pair(a: *const i32, b: *const i32) -> bool { *a == *b }
        pub unsafe fn caller(p: *mut i32) -> bool { let sum = read_pair(p, p); *p = 7; sum }
    "#,
    );
}

#[test]
fn w5p_native_explicit_mutable_reborrow_shared_pair() {
    native_pair(
        r#"
        pub unsafe fn read_pair(a: *mut i32, b: *const i32) -> bool { *a == *b }
        pub unsafe fn caller(p: *mut i32) -> bool { let sum = read_pair(&mut *p, &*p); *p = 7; sum }
    "#,
    );
}

#[test]
fn w5p_diagnostic_carries_native_forms_and_mutability() {
    let input = r#"
        pub unsafe fn reader(a: *mut i32, b: *const i32) -> bool { *a == *b }
        pub unsafe fn entry(p: *mut i32) -> bool { let result = reader(&mut *p, &*p); *p = 7; result }
    "#;
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (mut table, ctx) = bo_rewriter::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("native writer-pair table");
        assert!(!table.seams.overlap_proofs.is_empty());
        let (positions, formals) = super::observer::snapshot(tcx, &table, &ctx);
        assert_eq!(
            positions.lines().count(),
            table.seams.overlap_proofs.len() + 1
        );
        assert!(formals.contains("reader\t0\timmutable\tfalse"), "{formals}");
        assert!(formals.contains("reader\t1\timmutable\tfalse"), "{formals}");
        assert!(formals.contains("entry\t0\tmutable\tfalse"), "{formals}");
        let rows = super::diagnose(&table, &ctx.mut_facts);
        assert_eq!(rows.len(), table.seams.overlap_proofs.len());
        for (row, proof) in rows.iter().zip(&table.seams.overlap_proofs) {
            assert_eq!(row.site, proof.proof_site_key);
            assert_eq!(row.argument_index, proof.index);
            assert_eq!(row.expected, proof.expected_form);
            assert_eq!(row.found, proof.found_form);
            assert_eq!(
                row.formal_mutability,
                super::NativeMutability::Present { mutable: false }
            );
            println!("native-position {row:?}");
        }
        table.seams.overlap_proofs[0].index = usize::MAX;
        assert_eq!(
            super::diagnose(&table, &ctx.mut_facts)[0].formal_mutability,
            super::NativeMutability::Missing
        );
    })
    .expect("diagnostic fixture");
}

fn discovery(input: &str, admitted: usize) {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let (table, ctx) = bo_rewriter::decide_table_with_ctx_config(
            tcx,
            Some((
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("native discovery table");
        let found = super::consumer::discover(
            tcx,
            &ctx.facts,
            &ctx.hypothetical,
            table.exposure.as_ref(),
            &ctx.a5_site_proofs,
            &ctx.lifetime_eligibility,
            &ctx.mut_facts,
        );
        assert_eq!(found.calls.len(), admitted, "{found:#?}");
    })
    .expect("discovery fixture");
}

#[test]
fn w5p_consumer_native_inventory() {
    discovery(
        r#"
        pub unsafe fn read_pair(a: *mut i32, b: *const i32) -> bool { *a == *b }
        pub unsafe fn caller(p: *mut i32) -> bool { let v = read_pair(&mut *p, &*p); *p = 7; v }
    "#,
        1,
    );
}

#[test]
fn w5p_consumer_one_uncovered_call_holds_subject() {
    discovery(
        r#"
        pub unsafe fn read_pair(a: *mut i32, b: *const i32) -> bool { *a == *b }
        pub unsafe fn caller(p: *mut i32) -> bool { let v = read_pair(&mut *p, &*p); *p = 7; v }
        pub unsafe fn unadaptable(p: *mut i32) -> bool { read_pair(p.offset(0), p) }
    "#,
        0,
    );
}

#[test]
fn w5p_consumer_mutable_peer_holds_component() {
    discovery(
        r#"
        pub unsafe fn read_pair(a: *mut i32, b: *const i32, writer: *mut i32) -> bool {
            let first = *a; *writer = 7; first == *b
        }
        pub unsafe fn caller(p: *mut i32) -> bool { read_pair(&mut *p, &*p, p) }
    "#,
        0,
    );
}

#[test]
fn w5p_consumer_distinct_roots_need_backing_source_evidence() {
    discovery(
        r#"
        pub unsafe fn read_pair(a: *mut i32, b: *const i32) -> bool { *a == *b }
        pub unsafe fn caller(p: *mut i32, q: *mut i32) -> bool { let v = read_pair(&mut *p, &*q); *p = 7; v }
    "#,
        0,
    );
}

#[test]
fn w5p_consumer_transitive_writer_is_held() {
    discovery(
        r#"
        static mut VALUE: i32 = 0;
        unsafe fn write_global() { VALUE = 7; }
        pub unsafe fn read_pair(a: *mut i32, b: *const i32) -> bool { write_global(); *a == *b }
        pub unsafe fn caller(p: *mut i32) -> bool { let v = read_pair(&mut *p, &*p); *p = 7; v }
    "#,
        0,
    );
}

#[test]
fn w5p_consumer_method_caller_is_not_lost_from_inventory() {
    discovery(
        r#"
        pub unsafe fn read_pair(a: *mut i32, b: *const i32) -> bool { *a == *b }
        pub unsafe fn caller(p: *mut i32) -> bool { let v = read_pair(&mut *p, &*p); *p = 7; v }
        pub struct Other;
        impl Other { pub unsafe fn hidden(p: *mut i32) -> bool { read_pair(p, p) } }
    "#,
        0,
    );
}

#[test]
fn w5p_consumer_unknown_and_exceptional_calls_are_held() {
    for code in [
        r#"
        unsafe extern "C" { fn external(); }
        pub unsafe fn read_pair(a: *mut i32, b: *const i32) -> bool { external(); *a == *b }
        pub unsafe fn caller(p: *mut i32) -> bool { let v = read_pair(&mut *p, &*p); *p = 7; v }
    "#,
        r#"
        pub unsafe fn read_pair(a: *mut i32, b: *const i32) -> i32 { *a / *b }
        pub unsafe fn caller(p: *mut i32) -> i32 { let v = read_pair(&mut *p, &*p); *p = 7; v }
    "#,
    ] {
        discovery(code, 0);
    }
}
