//! R281 full-byte frozen-oracle and temporary resident-graph witnesses.
use rustc_hir::{ItemKind, OwnerNode};

use crate::analyses::borrow_ownership::{
    construction::{CopyLendMode, construct_bo_into, verify_bo_construction_counting},
    export,
    mutability_facts::MutFacts,
    origins::compute_origins,
    portable_export::*,
    solver::KindSolver,
};

fn captured(
    code: &str,
    check: impl FnOnce(&RustProgram<'_>, &CrateSlots, &BoExport) + Send + Sync,
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
        let slots = CrateSlots::build(&program);
        let origins = compute_origins(&program);
        let facts = MutFacts::from_program(&program);
        let (accepted, output) = export::with_bo_export(|| {
            let solver = KindSolver::new(&slots);
            let construction = construct_bo_into(
                &program,
                &slots,
                &origins,
                &facts,
                &solver,
                CopyLendMode::Baseline,
            )
            .expect("real construction");
            verify_bo_construction_counting(
                &program,
                &slots,
                &origins,
                &solver,
                &construction,
                &facts,
            )
            .0
            .is_some()
        });
        assert!(
            accepted,
            "portable fixture must have a real accepted capture"
        );
        assert!(output.version_owns.is_some());
        assert!(
            output.qualifier_facts.is_some()
                && output.array_fields.is_some()
                && output.demand_evidence.is_some()
        );
        check(&program, &slots, &output);
    })
    .unwrap_or_else(|error| error.raise());
}

const CODE: &str = r#"
unsafe extern "C" { fn realloc(p: *mut u8, n: usize) -> *mut u8; fn free(p: *mut u8); }
unsafe fn resize(p: *mut u8) { let q = realloc(p, 8); if q.is_null() { free(p); } else { free(q); } }
pub unsafe fn borrowed(p: *const u8, alias: *mut u8) -> u8 { let value = *p; free(alias); value }
"#;
struct Directory(std::path::PathBuf);
impl Directory {
    fn new() -> Self {
        static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
        let path = std::env::temp_dir().join(format!(
            "crat-r281-stream-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
        ));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }
}
impl Drop for Directory {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}
fn history(output: &BoExport, count: usize) -> BoExport {
    let mut result = output.clone();
    let review = output
        .retirement_rounds
        .iter()
        .find(|r| !r.conflicts.is_empty())
        .expect("real conflict review");
    result.retirement_rounds = (0..count)
        .map(|round| {
            let mut row = review.clone();
            row.ordinary_error_points = round;
            row.conflicts.push(row.conflicts[0].clone());
            row
        })
        .collect();
    result
}
#[test]
fn r281_w01_twelve_rounds_full_wire_bytes_match_frozen_oracle() {
    captured(CODE, |program, slots, output| {
        let output = history(output, 12);
        let oracle = collect(program, slots, &output)
            .unwrap()
            .canonical_json()
            .unwrap();
        let wire: Value = serde_json::from_str(&oracle).unwrap();
        let expected = serde_json::to_vec(&wire).unwrap();
        let directory = Directory::new();
        let spool = crate::analyses::borrow_ownership::portable_export::stream::collect_to_path(
            program,
            slots,
            &output,
            &directory.0,
        )
        .unwrap();
        assert_eq!(std::fs::read(&spool.path).unwrap(), expected);
        let mut typed = Vec::new();
        spool.write_portable_typed(&mut typed).unwrap();
        assert_eq!(typed, oracle.as_bytes(), "W01: old typed canonical bytes");
        let round_rows = wire["families"]["retirement-rounds"]["records"]
            .as_array()
            .unwrap();
        assert_eq!(
            round_rows
                .iter()
                .map(|row| row["fields"]["round"].as_u64().unwrap())
                .collect::<Vec<_>>(),
            vec![0, 10, 11, 1, 2, 3, 4, 5, 6, 7, 8, 9]
        );
        let path = spool.path.clone();
        drop(spool);
        assert!(!path.exists());
    });
}
#[test]
fn r281_w05_resident_json_graph_does_not_scale_with_retained_history() {
    captured(CODE, |program, slots, output| {
        let directory = Directory::new();
        let small = crate::analyses::borrow_ownership::portable_export::stream::collect_to_path(
            program,
            slots,
            &history(output, 12),
            &directory.0,
        )
        .unwrap();
        let large = crate::analyses::borrow_ownership::portable_export::stream::collect_to_path(
            program,
            slots,
            &history(output, 48),
            &directory.0,
        )
        .unwrap();
        assert!(
            std::fs::metadata(&large.path).unwrap().len()
                > std::fs::metadata(&small.path).unwrap().len()
        );
        assert_eq!(
            large.peak_materialized_nodes, small.peak_materialized_nodes,
            "W05: peak temporary JSON graph must not retain all retirement history"
        );
    });
}

#[test]
fn r281_w03_history_labels_routes_and_duplicates_keep_full_bytes() {
    captured(CODE, |program, slots, output| {
        let mut output = history(output, 12);
        let conflict = &mut output.retirement_rounds[0].conflicts[0];
        let first = rt::RouteStep {
            caller: program.functions[0],
            callee: program.functions[1],
            location: conflict.location,
        };
        let second = rt::RouteStep {
            caller: first.callee,
            callee: first.caller,
            location: first.location,
        };
        conflict.route = vec![first, second];
        conflict.loan = Some(rt::LoanIdentity {
            index: 42,
            reservation: conflict.location,
            borrowed: e::PlaceKey {
                local: rustc_middle::mir::Local::from_u32(1),
                proj: vec![],
            },
            owners: vec![],
        });
        let unresolved = rt::RetirementUnresolved {
            source: Some(conflict.source.clone()),
            function: Some(conflict.function),
            location: Some(conflict.location),
            phase: Some(conflict.phase),
            route: conflict.route.clone(),
            reason: rt::UnresolvedReason::MissingOwner {
                loan: 43,
                owner: None,
            },
        };
        output.retirement_rounds[0].unresolved.push(unresolved);
        let directory = Directory::new();
        let oracle = collect(program, slots, &output)
            .unwrap()
            .canonical_json()
            .unwrap();
        let expected: Value = serde_json::from_str(&oracle).unwrap();
        let spool = crate::analyses::borrow_ownership::portable_export::stream::collect_to_path(
            program,
            slots,
            &output,
            &directory.0,
        )
        .unwrap();
        assert_eq!(
            std::fs::read(&spool.path).unwrap(),
            serde_json::to_vec(&expected).unwrap()
        );
        let mut typed = Vec::new();
        spool.write_portable_typed(&mut typed).unwrap();
        assert_eq!(typed, oracle.as_bytes());
        let mut reordered = output.clone();
        reordered.retirement_rounds[0].conflicts[0].route.reverse();
        assert_ne!(
            collect(program, slots, &reordered)
                .unwrap()
                .canonical_json()
                .unwrap(),
            oracle,
            "ordered route is not a set"
        );
        let mut dropped = output.clone();
        dropped.retirement_rounds[0].conflicts.pop();
        assert_ne!(
            collect(program, slots, &dropped)
                .unwrap()
                .canonical_json()
                .unwrap(),
            oracle,
            "duplicate observations must remain"
        );
        let mut relabeled = output.clone();
        relabeled.retirement_rounds[0].conflicts[0]
            .loan
            .as_mut()
            .unwrap()
            .index += 1;
        assert_ne!(
            collect(program, slots, &relabeled)
                .unwrap()
                .canonical_json()
                .unwrap(),
            oracle,
            "diagnostic labels remain transported"
        );
    });
}
#[test]
fn r281_w04_corrupt_target_refuses_and_cleans_unpublished_fragments() {
    captured(CODE, |program, slots, output| {
        let mut output = history(output, 12);
        output.retirement_rounds[0].conflicts[0]
            .target_key
            .push_str("-corrupt");
        assert!(
            collect(program, slots, &output)
                .unwrap_err()
                .contains("retirement target canonical key mismatch")
        );
        let directory = Directory::new();
        let failure = crate::analyses::borrow_ownership::portable_export::stream::collect_to_path(
            program,
            slots,
            &output,
            &directory.0,
        )
        .err()
        .expect("stream must reject corrupt target");
        assert!(failure.contains("retirement target canonical key mismatch"));
        assert_eq!(
            std::fs::read_dir(&directory.0).unwrap().count(),
            0,
            "failed transport owns and removes every fragment"
        );
    });
}
#[test]
fn r281_w04_writer_failure_is_returned_without_truncating_owned_spool() {
    struct FailingWriter;
    impl std::io::Write for FailingWriter {
        fn write(&mut self, _: &[u8]) -> std::io::Result<usize> {
            Err(std::io::Error::other("injected write failure"))
        }

        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }
    captured(CODE, |program, slots, output| {
        let directory = Directory::new();
        let spool = crate::analyses::borrow_ownership::portable_export::stream::collect_to_path(
            program,
            slots,
            output,
            &directory.0,
        )
        .unwrap();
        let before = std::fs::read(&spool.path).unwrap();
        assert!(
            spool
                .write_portable_typed(&mut FailingWriter)
                .unwrap_err()
                .contains("injected write failure")
        );
        assert_eq!(std::fs::read(&spool.path).unwrap(), before);
        drop(spool);
        assert_eq!(std::fs::read_dir(&directory.0).unwrap().count(), 0);
    });
}
