//! The revert closure (relay wave-6k/008): a class reverted by verification
//! must not close over its callers — a caller keeps its delivery and takes
//! the raw bridge against the reverted callee's raw signature.

use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT: AtomicUsize = AtomicUsize::new(0);

/// A single-file crate on disk for the real rewrite loop; removed on drop.
struct Fixture(std::path::PathBuf);

impl Fixture {
    fn new(text: &str) -> Self {
        let dir = std::env::temp_dir().join(format!(
            "crat-wave6k-closure-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&dir).expect("fixture dir");
        std::fs::write(dir.join("lib.rs"), text).expect("fixture root");
        Self(dir)
    }

    fn root(&self) -> std::path::PathBuf {
        self.0.join("lib.rs")
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// `callee`'s delivered body is a real borrow error (two live views of one
/// place); `caller` and `grand` only forward the pointer through it.
const CLOSURE: &str = "#![allow(dead_code, unused_unsafe, unused_assignments)]\n\
    #[repr(C)]\n\
    pub struct S { pub a: i32, pub b: i32 }\n\
    extern \"C\" { fn pick(p: *mut S) -> *mut S; }\n\
    #[no_mangle]\n\
    pub unsafe extern \"C\" fn leaf(x: *mut S) -> i32 {\n\
    \x20   (*x).b\n\
    }\n\
    #[no_mangle]\n\
    pub unsafe extern \"C\" fn callee(p: *mut S) -> i32 {\n\
    \x20   let r = pick(p);\n\
    \x20   (*p).a = 1;\n\
    \x20   leaf(r)\n\
    }\n\
    #[no_mangle]\n\
    pub unsafe extern \"C\" fn caller(mut p: *mut S) -> i32 {\n\
    \x20   if p.is_null() { return 0; }\n\
    \x20   (*p).b = 3;\n\
    \x20   callee(p)\n\
    }\n\
    #[no_mangle]\n\
    pub unsafe extern \"C\" fn grand(s: *mut S) -> i32 {\n\
    \x20   (*s).b = 0;\n\
    \x20   caller(s)\n\
    }\n";

fn outcome(
    text: &str,
) -> (
    String,
    Vec<super::decision::Degradation>,
    String,
    usize,
    usize,
) {
    let fixture = Fixture::new(text);
    match super::rewrite_m1_path(&fixture.root()) {
        super::RewriteOutcome::Emitted {
            source,
            degradations,
            raw_boundary_artifacts,
            reverted_count,
            verify_rounds,
            ..
        } => {
            println!(
                "REVERTED {reverted_count} ROUNDS {verify_rounds}\nFINAL_REVERTS\n{}\nSOURCE\n{source}",
                raw_boundary_artifacts.final_reverts
            );
            for d in &degradations {
                println!("DEGRADED {} {:?}", d.subject, d.reason);
            }
            (
                source,
                degradations,
                raw_boundary_artifacts.final_reverts,
                reverted_count,
                verify_rounds,
            )
        }
        other => panic!("unexpected outcome: {other:?}"),
    }
}

fn reason_of(degradations: &[super::decision::Degradation], subject: &str) -> Option<String> {
    degradations
        .iter()
        .find(|d| d.subject == subject)
        .map(|d| format!("{:?}", d.reason))
}

/// A held callee (`blocked-subject:return-not-adapted`) must not close over its
/// callers: the caller's adapter leaves with the callee's class and the
/// caller's argument renders in its own form against the raw signature.
#[test]
fn wave6k_held_callee_does_not_close_over_adapted_callers() {
    let (source, degradations, final_reverts, reverted_count, _) = outcome(CLOSURE);
    assert_eq!(reverted_count, 0, "no verify-loop revert: {final_reverts}");
    assert!(
        reason_of(&degradations, "callee::p#1")
            .is_some_and(|r| r.contains("blocked-subject:return-not-adapted")),
        "{degradations:?}"
    );
    assert!(
        reason_of(&degradations, "caller::p#1").is_none(),
        "{degradations:?}"
    );
    assert!(
        reason_of(&degradations, "grand::s#1").is_none(),
        "{degradations:?}"
    );
    assert_eq!(
        final_reverts.lines().count(),
        2,
        "only the callee: {final_reverts}"
    );
    assert!(
        source.contains("fn caller(mut p: Option<&mut S>)"),
        "{source}"
    );
    assert!(source.contains("fn grand(s: &mut S)"), "{source}");
    assert!(
        source.contains("callee(p.as_deref_mut().map_or(core::ptr::null_mut::<crate::S>()"),
        "{source}"
    );
}

/// Control of the classification: on the closure fixture the caller→callee
/// and grand→caller pairs are bare adapter edges; a pair that also carries a
/// structural dependency (given as `other_edges`) is never narrowed.
#[test]
fn wave6k_structural_pairs_are_never_narrowed() {
    ::utils::compilation::run_compiler_on_str(CLOSURE, |tcx| {
        use super::bridge_receipt::SignatureClassId;
        let (table, _) = super::decide_table_with_ctx_config(
            tcx,
            Some((
                super::A5Mode::PreciseReplay,
                Some(super::WholeProgramAttestation::FrozenBenchmarkGraph),
            )),
        )
        .expect("native decisions");
        let class_of = |name: &str| {
            SignatureClassId::of(
                table
                    .entries
                    .iter()
                    .find(|(s, _)| tcx.def_path_str(s.fn_did.to_def_id()) == name)
                    .unwrap_or_else(|| panic!("no subject in {name}"))
                    .0
                    .fn_did,
            )
        };
        let (caller, callee, grand) = (class_of("caller"), class_of("callee"), class_of("grand"));
        let bare = super::revert_closure::call_adapter_only_edges(&table, []);
        assert!(bare.contains(&(caller, callee)), "{bare:?}");
        assert!(bare.contains(&(grand, caller)), "{bare:?}");
        let with_structural =
            super::revert_closure::call_adapter_only_edges(&table, [(caller, callee)]);
        assert!(
            !with_structural.contains(&(caller, callee)),
            "{with_structural:?}"
        );
        assert!(
            with_structural.contains(&(grand, caller)),
            "{with_structural:?}"
        );
    })
    .expect("input compiles");
}
