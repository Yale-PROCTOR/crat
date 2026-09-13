use rustc_middle::{
    mir::TerminatorKind,
    ty::{TyCtxt, TyKind},
};

use super::{Hold, Request, prove, replay};
use crate::{
    analyses::borrow_ownership::l2::MirLocationKey,
    bo_rewriter::decision::a5_site_proof::{A5ProofSiteKey, ATTESTED_GUARD, ATTESTED_WORLD},
};

const READER: &str = r#"
    pub unsafe fn reader(a: *const i32, b: *const i32) -> bool { *a == *b }
    pub unsafe fn entry(p: *mut i32) -> bool { let value = reader(p, p); *p = 7; value }
"#;

fn with_request(input: &str, check: impl FnOnce(TyCtxt<'_>, Request) + Send) {
    ::utils::compilation::run_compiler_on_str(input, |tcx| {
        let program = crate::bo_rewriter::collect_program(tcx);
        // Foster consumes an earlier MIR query. Derive it before requesting
        // optimized MIR, just as the production pipeline does.
        let facts =
            crate::analyses::borrow_ownership::mutability_facts::MutFacts::from_program(&program);
        let reader = *program
            .functions
            .iter()
            .find(|did| tcx.item_name(did.to_def_id()).as_str() == "reader")
            .unwrap();
        for local in tcx
            .mir_drops_elaborated_and_const_checked(reader)
            .borrow()
            .args_iter()
            .take(2)
        {
            assert!(!facts.is_defaulted(reader, local));
            assert!(
                !facts.is_mutable(reader, local),
                "per-pointer read-only cannot certify the object"
            );
        }
        let caller = *program
            .functions
            .iter()
            .find(|did| tcx.item_name(did.to_def_id()).as_str() == "entry")
            .unwrap();
        let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
        let mut calls = body
            .basic_blocks
            .iter_enumerated()
            .filter_map(|(bb, data)| {
                let TerminatorKind::Call { func, .. } = &data.terminator().kind else {
                    return None;
                };
                let TyKind::FnDef(callee, _) = *func.ty(&body.local_decls, tcx).kind() else {
                    return None;
                };
                if tcx.item_name(callee).as_str() != "reader" {
                    return None;
                }
                Some((bb, data.statements.len(), callee))
            });
        let (bb, statement_index, callee) = calls.next().expect("reader call");
        assert!(calls.next().is_none());
        let key = |argument_index| A5ProofSiteKey {
            caller,
            callee,
            argument_index,
            slot_depth: 0,
            location: MirLocationKey {
                block: bb.as_u32(),
                statement_index,
            },
        };
        check(
            tcx,
            Request {
                left: key(0),
                right: key(1),
                world: ATTESTED_WORLD,
                guard: ATTESTED_GUARD,
            },
        );
    })
    .expect("reader fixture compilation");
}

#[test]
fn w5p_reader_no_write_interval_ends_before_caller_write() {
    with_request(READER, |tcx, request| {
        let proof = prove(tcx, &request).expect("object-wide reader certificate");
        assert_eq!(proof.functions.len(), 1);
        assert_eq!(replay(tcx, &request, Some(&proof)), Ok(()));
    });
}

#[test]
fn w5p_reader_transitive_closure() {
    with_request(
        r#"
        unsafe fn leaf(a: *const i32) -> i32 { *a }
        pub unsafe fn reader(a: *const i32, b: *const i32) -> bool { leaf(a) == leaf(b) }
        pub unsafe fn entry(p: *mut i32) -> bool { reader(p, p) }
    "#,
        |tcx, request| {
            let proof = prove(tcx, &request).expect("all local reader calls checked");
            assert_eq!(proof.functions.len(), 2);
        },
    );
}

#[test]
fn w5p_reader_third_alias_write_is_held() {
    with_request(
        r#"
        pub unsafe fn reader(a: *const i32, b: *const i32, writer: *mut i32) -> bool {
            let before = *a; *writer = 7; before == *b
        }
        pub unsafe fn entry(p: *mut i32) -> bool { reader(p, p, p) }
    "#,
        |tcx, request| {
            assert!(matches!(
                prove(tcx, &request),
                Err(Hold::MemoryWrite { .. })
            ));
        },
    );
}

#[test]
fn w5p_reader_transitive_writer_is_held() {
    with_request(
        r#"
        unsafe fn leaf(writer: *mut i32) { *writer = 7; }
        pub unsafe fn reader(a: *const i32, b: *const i32, writer: *mut i32) -> bool {
            let before = *a; leaf(writer); before == *b
        }
        pub unsafe fn entry(p: *mut i32) -> bool { reader(p, p, p) }
    "#,
        |tcx, request| {
            assert!(matches!(
                prove(tcx, &request),
                Err(Hold::MemoryWrite { .. })
            ));
        },
    );
}

#[test]
fn w5p_reader_unknown_effect_is_held() {
    with_request(
        r#"
        unsafe extern "C" { fn opaque(p: *mut i32); }
        pub unsafe fn reader(a: *const i32, b: *const i32, writer: *mut i32) -> bool {
            let before = *a; opaque(writer); before == *b
        }
        pub unsafe fn entry(p: *mut i32) -> bool { reader(p, p, p) }
    "#,
        |tcx, request| {
            assert!(matches!(prove(tcx, &request), Err(Hold::OpaqueCall { .. })));
        },
    );
}

#[test]
fn w5p_reader_defined_abort_is_opaque() {
    with_request(
        r#"
        pub unsafe fn reader(a: *const i32, b: *const i32) -> i32 { *a / *b }
        pub unsafe fn entry(p: *mut i32) -> i32 { reader(p, p) }
    "#,
        |tcx, request| {
            // Division by zero enters the Rust runtime even when the embedded
            // compiler disables overflow checks. A runtime hook may write a
            // global alias. It is not an
            // unreachable UB-free-input path like an invalid raw dereference.
            let result = prove(tcx, &request);
            assert!(
                matches!(result, Err(Hold::OpaqueEffect { .. })),
                "{result:?}"
            );
        },
    );
}

#[test]
fn w5p_reader_pointer_encoding_is_held() {
    for input in [
        r#"
        pub unsafe fn reader(a: *const i32, b: *const i32) -> usize { a as usize }
        pub unsafe fn entry(p: *mut i32) -> usize { reader(p, p) }
    "#,
        r#"
        unsafe fn leaf(a: *const i32) -> usize { a as usize }
        pub unsafe fn reader(a: *const i32, b: *const i32) -> usize { leaf(a) }
        pub unsafe fn entry(p: *mut i32) -> usize { reader(p, p) }
    "#,
    ] {
        with_request(input, |tcx, request| {
            let result = prove(tcx, &request);
            assert!(
                matches!(result, Err(Hold::OpaqueEffect { .. })),
                "{result:?}"
            );
        });
    }
}

#[test]
fn w5p_reader_missing_and_stale_evidence_is_held() {
    with_request(READER, |tcx, request| {
        assert_eq!(replay(tcx, &request, None), Err(Hold::MissingEvidence));
        let proof = prove(tcx, &request).expect("reader certificate");
        let mut stale = request.clone();
        stale.right.argument_index = 2;
        assert_eq!(replay(tcx, &stale, Some(&proof)), Err(Hold::StaleEvidence));
        stale = request.clone();
        stale.left.location.statement_index += 1;
        assert_eq!(replay(tcx, &stale, Some(&proof)), Err(Hold::StaleEvidence));
        stale = request.clone();
        stale.guard = "-";
        assert_eq!(replay(tcx, &stale, Some(&proof)), Err(Hold::StaleEvidence));
        let mut incomplete = proof.clone();
        incomplete.functions.clear();
        assert_eq!(
            replay(tcx, &request, Some(&incomplete)),
            Err(Hold::StaleEvidence)
        );
    });
}

#[test]
fn w5p_reader_unattested_or_invalid_site_is_held() {
    with_request(READER, |tcx, request| {
        let mut missing = request.clone();
        missing.world = "-";
        assert_eq!(prove(tcx, &missing), Err(Hold::UnattestedWorld));
        missing = request.clone();
        missing.right.argument_index = 2;
        assert_eq!(prove(tcx, &missing), Err(Hold::InvalidSite));
        missing = request.clone();
        missing.left.location.block = u32::MAX;
        missing.right.location.block = u32::MAX;
        assert_eq!(prove(tcx, &missing), Err(Hold::InvalidSite));
    });
}
