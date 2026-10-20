//! R243: real field-carried tests and a receipted, non-declining fallback.
use rustc_hir::{ItemKind, OwnerNode};

use super::*;
use crate::analyses::borrow_ownership::{
    a5_overlap::{A5Mode, WholeProgramAttestation},
    construction::solve_bo_a5_config_reporting,
    crate_slots::CrateSlots,
    export,
    mutability_facts::MutFacts,
    origins::compute_origins,
    portable_export,
};
const LABEL: &str = "realloc-result-test:fallback-both-outcomes";
const BUFFER: &str = r#"
unsafe extern "C" { fn realloc(p:*mut libc::c_void,n:libc::c_ulong)->*mut libc::c_void; }
type size_t=libc::c_ulong;
#[repr(C)] #[derive(Copy,Clone)] pub struct buffer_t {pub len:size_t,pub alloc:*mut libc::c_char,pub data:*mut libc::c_char}
#[no_mangle]
pub unsafe extern "C" fn buffer_resize(mut self_0:*mut buffer_t,mut n:size_t)->libc::c_int {
 n=n.wrapping_add((1024 as libc::c_int-1 as libc::c_int) as libc::c_ulong)&!(1024 as libc::c_int-1 as libc::c_int) as libc::c_ulong;
 (*self_0).len=n;
 (*self_0).data=realloc((*self_0).alloc as *mut libc::c_void,n.wrapping_add(1 as libc::c_int as libc::c_ulong)) as *mut libc::c_char;
 (*self_0).alloc=(*self_0).data;
 if ((*self_0).alloc).is_null(){return -(1 as libc::c_int);}
 *((*self_0).alloc).offset(n as isize)='\0' as i32 as libc::c_char;
 return 0 as libc::c_int;
}
"#;
fn inspect(code: &str, check: impl FnOnce(&ReallocSite, serde_json::Value) + Send + Sync) {
    inspect_many(code, 1, |sites, value| check(&sites[0], value));
}
fn inspect_many(
    code: &str,
    expected: usize,
    check: impl FnOnce(&[ReallocSite], serde_json::Value) + Send + Sync,
) {
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let mut functions = Vec::new();
        let mut structs = Vec::new();
        for owner in tcx.hir_crate(()).owners.iter() {
            let Some(owner) = owner.as_owner() else { continue };
            let OwnerNode::Item(item) = owner.node() else { continue };
            match item.kind {
                ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
                ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
                _ => {}
            }
        }
        let program = RustProgram {
            tcx,
            functions,
            structs,
        };
        let sites = collect_sites(&program);
        assert_eq!(sites.len(), expected);
        let slots = CrateSlots::build(&program);
        let origins = compute_origins(&program);
        let mutability = MutFacts::from_program(&program);
        let (solved, captured) = export::with_bo_export(|| {
            solve_bo_a5_config_reporting(
                &program,
                &slots,
                &origins,
                &mutability,
                A5Mode::PreciseReplay,
                Some(WholeProgramAttestation::FrozenBenchmarkGraph),
            )
        });
        assert!(
            solved.is_ok(),
            "R243 result-test coverage must keep the program model: {solved:?}"
        );
        let encoded = portable_export::collect(&program, &slots, &captured)
            .unwrap()
            .canonical_json()
            .unwrap();
        let value = serde_json::from_str(&encoded).unwrap();
        check(&sites, value);
    })
    .unwrap_or_else(|error| error.raise());
}
fn source_result(value: &serde_json::Value) -> &serde_json::Value {
    let rows = value["families"]["source-inventory"]["records"]
        .as_array()
        .unwrap();
    let rows: Vec<_> = rows
        .iter()
        .filter(|r| r["fields"]["kind"] == "realloc")
        .collect();
    assert_eq!(rows.len(), 1);
    &rows[0]["fields"]["site"]["result"]
}
#[test]
fn e5_r243_buffer_exact_field_chain_keeps_test_and_model() {
    inspect(BUFFER, |site, value| {
        let result = source_result(&value);
        assert_eq!(result["kind"], "field-branch");
        assert_ne!(result["branch"]["success"], result["branch"]["failure"]);
        assert!(result["field_transports"].as_array().unwrap().len() >= 3);
        assert!(
            classify(site)
                .unwrap()
                .iter()
                .any(|c| c.outcome == ReallocOutcome::Failure)
        );
        assert!(
            !value.to_string().contains(LABEL),
            "recognized field test is not an opaque fallback"
        );
    });
}
#[test]
fn e5_r243_opaque_result_keeps_both_outcomes_and_receipt() {
    inspect(
        "unsafe extern \"C\" {fn realloc(p:*mut u8,n:usize)->*mut u8;fn opaque(q:*mut u8)->bool;} pub unsafe fn f(p:*mut u8)->bool{let q=realloc(p,16);opaque(q)}",
        |site, value| {
            let result = source_result(&value);
            assert_eq!(result["kind"], "fallback-both-outcomes");
            assert_eq!(result["receipt"], LABEL);
            let cases = classify(site).unwrap();
            assert_eq!(cases.len(), 2);
            assert!(cases.iter().any(|c| c.outcome == ReallocOutcome::Success
                && c.old == OldResponsibility::RetireIfPresent
                && c.result == ResultResponsibility::FreshGeneration));
            assert!(cases.iter().any(|c| c.outcome == ReallocOutcome::Failure
                && c.old == OldResponsibility::LoseClaimIfPresent
                && c.result == ResultResponsibility::None));
        },
    );
}

const FIELD_DECL: &str = "unsafe extern \"C\" {fn realloc(p:*mut u8,n:usize)->*mut u8;fn opaque_store(p:*mut Holder);} pub struct Holder { pub old:*mut u8,pub data:*mut u8,pub alloc:*mut u8 }";
fn field_control(body: &str) {
    inspect(&format!("{FIELD_DECL}{body}"), |site, value| {
        assert_eq!(source_result(&value)["kind"], "fallback-both-outcomes");
        assert_eq!(source_result(&value)["receipt"], LABEL);
        assert_eq!(classify(site).unwrap().len(), 2);
    });
}
#[test]
fn e5_r243_overwritten_carrying_field_is_not_a_result_test() {
    inspect(
        &format!(
            "{FIELD_DECL}pub unsafe fn f(s:*mut Holder)->bool{{(*s).data=realloc((*s).old,16);(*s).data=core::ptr::null_mut();(*s).alloc=(*s).data;(*s).alloc.is_null()}}"
        ),
        |site, value| {
            assert_ne!(
                source_result(&value)["kind"],
                "field-branch",
                "the overwritten value is not the tested realloc result"
            );
            let cases = classify(site).unwrap();
            assert_eq!(cases.len(), 2);
            assert!(
                cases
                    .iter()
                    .any(|case| case.outcome == ReallocOutcome::Failure
                        && case.old == OldResponsibility::LoseClaimIfPresent)
            );
        },
    );
}
#[test]
fn e5_r243_distinct_base_field_copy_stays_receipted_fallback() {
    field_control(
        "pub unsafe fn f(s:*mut Holder,t:*mut Holder)->bool{(*s).data=realloc((*s).old,16);(*t).alloc=(*s).data;(*t).alloc.is_null()}",
    );
}
#[test]
fn e5_r243_opaque_call_between_field_store_and_test_stays_fallback() {
    field_control(
        "pub unsafe fn f(s:*mut Holder)->bool{(*s).data=realloc((*s).old,16);opaque_store(s);(*s).alloc=(*s).data;(*s).alloc.is_null()}",
    );
}
#[test]
fn e5_r243_fallback_and_direct_sites_share_a_body_without_decline() {
    inspect_many(
        "unsafe extern \"C\" {fn realloc(p:*mut u8,n:usize)->*mut u8;fn free(p:*mut u8);fn opaque(p:*mut u8)->bool;} pub unsafe fn f(p:*mut u8,other:*mut u8)->bool{let q=realloc(p,16);if q.is_null(){free(p);return false;} free(q);let r=realloc(other,16);opaque(r)}",
        2,
        |sites, value| {
            assert!(
                sites
                    .iter()
                    .any(|site| matches!(site.result, ReallocResult::DirectBranch(_)))
            );
            let rows = value["families"]["source-inventory"]["records"]
                .as_array()
                .unwrap();
            let labels: Vec<_> = rows
                .iter()
                .filter(|r| r["fields"]["kind"] == "realloc")
                .filter(|r| r["fields"]["site"]["result"]["receipt"] == LABEL)
                .collect();
            assert_eq!(
                labels.len(),
                1,
                "count once per original source site, not once per outcome/round"
            );
        },
    );
}

#[test]
fn e5_r243_overwritten_null_predicate_cannot_certify_field_test() {
    field_control(
        "pub unsafe fn f(s:*mut Holder)->i32{(*s).data=realloc((*s).old,16);let mut failed=(*s).data.is_null();failed=false;if failed{return -1;}0}",
    );
}

#[test]
fn e5_r243_field_null_predicate_negation_keeps_exact_test() {
    inspect(
        &format!(
            "{FIELD_DECL}pub unsafe fn f(s:*mut Holder)->i32{{(*s).data=realloc((*s).old,16);let failed=(*s).data.is_null();let ok=!failed;if ok{{1}}else{{0}}}}"
        ),
        |_, value| {
            assert_eq!(source_result(&value)["kind"], "field-branch");
            assert!(!value.to_string().contains(LABEL));
        },
    );
}
