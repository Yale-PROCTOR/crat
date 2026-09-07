//! Real-capture REDs for portable identity, multiplicity, and completeness.

use rustc_hir::{ItemKind, OwnerNode};

use super::*;
use crate::analyses::borrow_ownership::{
    construction::{CopyLendMode, construct_bo_into, verify_bo_construction_counting},
    export::{self, BorrowerKind, OwnerKey},
    mutability_facts::MutFacts,
    origins::compute_origins,
    solver::KindSolver,
};

const FIELD_CALL: &str = r#"
#[repr(C)] pub struct Holder { pub value: *mut i32 }
unsafe fn g(p: *mut i32) { *p = 9; }
pub unsafe fn f() -> i32 {
    let mut x = 1;
    let mut holder = Holder { value: 0 as *mut i32 };
    holder.value = &raw mut x;
    g(holder.value);
    x
}
"#;

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

fn packet(program: &RustProgram<'_>, slots: &CrateSlots, output: &BoExport) -> PortableExport {
    let packet = collect(program, slots, output).expect("complete portable export");
    packet.validate().expect("valid portable export");
    assert_eq!(packet.schema, SCHEMA);
    assert_eq!(packet.families.len(), REQUIRED_FAMILIES.len());
    assert_eq!(
        packet.families[&ExportFamily::OwnershipVersions]
            .records
            .len(),
        output.version_sites.len()
    );
    assert_eq!(
        packet.families[&ExportFamily::SourceSelectors]
            .records
            .len(),
        output.source_sites.len()
    );
    assert_eq!(
        packet.families[&ExportFamily::SinkSelectors].records.len(),
        output.sink_sites.len()
    );
    assert_eq!(
        packet.families[&ExportFamily::Loans].records.len(),
        output.loans.len()
    );
    assert_eq!(
        packet.families[&ExportFamily::RetirementRounds]
            .records
            .len(),
        output.retirement_rounds.len()
    );
    assert!(
        packet
            .scope_gaps
            .contains(&ScopeGap::OwnershipOccurrenceConstructionNotRecorded)
    );
    let encoded = packet.canonical_json().unwrap();
    let decoded: PortableExport = serde_json::from_str(&encoded).unwrap();
    decoded.validate().unwrap();
    assert_eq!(decoded.canonical_json().unwrap(), encoded);
    packet
}

#[test]
fn e5_i_portable_capture_preserves_fields_local_callees_and_all_families() {
    captured(FIELD_CALL, |program, slots, output| {
        assert!(!output.loans.is_empty(), "real loan identity population");
        assert!(
            output
                .loans
                .iter()
                .any(|loan| matches!(loan.key.borrower, BorrowerKind::CallArg { .. })),
            "actual local-callee borrower"
        );
        let packet = packet(program, slots, output);
        let loans = &packet.families[&ExportFamily::Loans].records;
        assert!(
            loans
                .iter()
                .any(|row| row
                    .fields
                    .get("borrower")
                    .is_some_and(
                        |borrower| borrower["kind"] == "call-arg" && borrower["callee"] == "g"
                    )),
            "erased callee index must resolve to the actual function path"
        );
        assert!(
            packet
                .identities
                .iter()
                .any(|key| key.contains("Holder::field0")),
            "actual canonical field identity"
        );
        let mut incomplete = packet.clone();
        incomplete.families.remove(&ExportFamily::QualifierFacts);
        assert!(incomplete.validate().is_err());
        let mut missing = output.clone();
        missing.qualifier_facts = None;
        assert!(
            collect(program, slots, &missing).is_err(),
            "missing required capture cannot be transported as empty"
        );
    });
}

#[test]
fn e5_i_portable_capture_keeps_realloc_and_every_retirement_round() {
    const CODE: &str = r#"
unsafe extern "C" { fn realloc(p: *mut u8, n: usize) -> *mut u8; fn free(p: *mut u8); }
unsafe fn resize(p: *mut u8) { let q = realloc(p, 8); if q.is_null() { free(p); } else { free(q); } }
pub unsafe fn borrowed(p: *const u8, alias: *mut u8) -> u8 { let value = *p; free(alias); value }
"#;
    captured(CODE, |program, slots, output| {
        assert!(
            !output.realloc_version_sites.is_empty(),
            "real conditional realloc values"
        );
        assert!(
            output
                .retirement_rounds
                .iter()
                .any(|round| !round.conflicts.is_empty()),
            "actual retirement repair history"
        );
        let packet = packet(program, slots, output);
        assert_eq!(
            packet.families[&ExportFamily::ReallocVersions]
                .records
                .len(),
            output.realloc_version_sites.len()
        );
        assert_eq!(
            packet.families[&ExportFamily::ReallocCases].records.len(),
            output.realloc_cases.len()
        );
        for (ordinal, round) in output.retirement_rounds.iter().enumerate() {
            let rows: Vec<_> = packet.families[&ExportFamily::RetirementRounds]
                .records
                .iter()
                .filter(|row| row.fields.get("round") == Some(&serde_json::json!(ordinal)))
                .collect();
            assert_eq!(rows.len(), 1);
            for (field, count) in [
                ("conflicts", round.conflicts.len()),
                ("unresolved", round.unresolved.len()),
                ("coverage", round.coverage.len()),
                ("terminal", round.terminal.len()),
            ] {
                assert_eq!(
                    rows[0].fields[field]
                        .as_array()
                        .expect("complete canonical round rows")
                        .len(),
                    count
                );
            }
        }
    });
}

#[test]
fn e5_i_portable_loan_handles_are_diagnostic_and_occurrences_are_not_deduplicated() {
    captured(FIELD_CALL, |program, slots, output| {
        assert!(!output.loans.is_empty());
        let baseline = packet(program, slots, output);
        let mut renumbered = output.clone();
        for loan in &mut renumbered.loans {
            loan.run_local_handle = loan.run_local_handle.checked_add(1000).unwrap();
        }
        let moved = packet(program, slots, &renumbered);
        assert_eq!(
            baseline.families, moved.families,
            "diagnostic loan numbering is not portable identity"
        );
        assert_ne!(
            baseline.diagnostics, moved.diagnostics,
            "numeric labels remain diagnostic evidence"
        );
        let mut repeated = output.clone();
        let row = repeated
            .version_sites
            .first()
            .expect("actual ownership occurrence")
            .clone();
        repeated.version_sites.push(row);
        let repeated = packet(program, slots, &repeated);
        assert_eq!(
            repeated.families[&ExportFamily::OwnershipVersions]
                .records
                .len(),
            baseline.families[&ExportFamily::OwnershipVersions]
                .records
                .len()
                + 1,
            "repeated stable sites may come from internal constructions and must not disappear"
        );
    });
}

#[test]
fn e5_i_portable_erased_owner_and_callee_indices_require_real_resolution() {
    captured(FIELD_CALL, |program, slots, output| {
        let _baseline = packet(program, slots, output);
        let mut bad_callee = output.clone();
        let loan = bad_callee
            .loans
            .iter_mut()
            .find(|loan| matches!(loan.key.borrower, BorrowerKind::CallArg { .. }))
            .expect("actual CallArg identity");
        let BorrowerKind::CallArg { arg_index, .. } = loan.key.borrower else { unreachable!() };
        loan.key.borrower = BorrowerKind::CallArg {
            callee: u32::MAX,
            arg_index,
        };
        assert!(
            collect(program, slots, &bad_callee).is_err(),
            "unknown erased callee cannot become a durable numeric key"
        );
        // Identity-validator seam only: this fixture does not produce a field
        // loan. Reuse one actual captured loan's site, and replace its owner
        // solely to exercise decoding against actual compiler field metadata.
        let structure = *program
            .structs
            .iter()
            .find(|did| program.tcx.def_path_str(did.to_def_id()) == "Holder")
            .expect("actual Holder definition");
        let ty = program.tcx.type_of(structure).skip_binder();
        let rustc_middle::ty::TyKind::Adt(adt, _) = ty.kind() else {
            panic!("Holder must be a compiler ADT");
        };
        let (field_index, field) = adt
            .all_fields()
            .enumerate()
            .find(|(_, field)| field.name.as_str() == "value")
            .expect("actual Holder::value field");
        let mut field_decoder_seam = output.clone();
        let loan = field_decoder_seam
            .loans
            .first_mut()
            .expect("actual loan site to clone");
        loan.key.borrower = BorrowerKind::Assign {
            owner: OwnerKey::Field {
                struct_did: structure.local_def_index.as_u32(),
                field_index,
            },
        };
        let valid = packet(program, slots, &field_decoder_seam);
        assert!(
            valid.families[&ExportFamily::Loans]
                .records
                .iter()
                .any(|row| {
                    let Some(borrower) = row.fields.get("borrower") else { return false };
                    borrower["kind"] == "assign"
                        && borrower["owner"]["kind"] == "field"
                        && borrower["owner"]["structure"]
                            == program.tcx.def_path_str(structure.to_def_id())
                        && borrower["owner"]["field"] == field.name.as_str()
                        && borrower["owner"]["field_index"] == serde_json::json!(field_index)
                }),
            "valid identity-validator seam must resolve the compiler-owned field"
        );
        let mut bad_owner = field_decoder_seam;
        bad_owner.loans.first_mut().unwrap().key.borrower = BorrowerKind::Assign {
            owner: OwnerKey::Field {
                struct_did: u32::MAX,
                field_index,
            },
        };
        assert!(
            collect(program, slots, &bad_owner).is_err(),
            "unknown erased field owner cannot become a durable numeric key"
        );
    });
}
