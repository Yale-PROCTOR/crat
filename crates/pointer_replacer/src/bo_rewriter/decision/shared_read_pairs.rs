//! Native immutable-formal evidence for the shared/shared PAIR consumer.

use rustc_hir::def_id::LocalDefId;
use rustc_middle::mir::Local;

use super::seam::Form;
use crate::analyses::borrow_ownership::mutability_facts::MutFacts;

/// R396-2: shared references impose no exclusivity against other read-only
/// views. The caller expression can still be `&mut field` on its way into an
/// immutable formal, so its surface spelling is not the read/write oracle.
/// This changes only the consumer role: the A5 overlap verdict stays intact.
pub(super) fn admits(
    facts: &MutFacts,
    callee: LocalDefId,
    index: usize,
    expected: Form,
    peers: impl Iterator<Item = (usize, Form)>,
) -> bool {
    let immutable = |index: usize| {
        let Some(local) = index.checked_add(1).filter(|n| *n < u32::MAX as usize) else {
            return false;
        };
        let local = Local::from_usize(local);
        !facts.is_defaulted(callee, local) && !facts.is_mutable(callee, local)
    };
    if expected != (Form::Ref { mutable: false }) || !immutable(index) {
        return false;
    }
    let mut has_peer = false;
    for (peer, form) in peers {
        has_peer = true;
        // Immutable effects cannot discharge Rust noalias for a peer whose
        // actual emitted signature still requests an exclusive reference.
        if !matches!(form, Form::Raw | Form::Ref { mutable: false }) || !immutable(peer) {
            return false;
        }
    }
    has_peer
}

#[cfg(test)]
mod tests {
    use super::{
        super::{
            Decision, a5_site_proof::A5SiteProofVerdict, co_conversion::PairRole,
            seam::A5ProofSiteFallback,
        },
        *,
    };

    const ROLLING: &str = r#"
#[repr(C)] pub struct HROLLING { pub state: u32 }
#[repr(C)] pub struct H65 { pub hb: HROLLING }
pub unsafe extern "C" fn PrepareDistanceCacheHROLLING(self_0: *mut HROLLING, distance_cache: *mut i32) {}
pub unsafe extern "C" fn PrepareDistanceCacheH65(self_0: *mut H65, distance_cache: *mut i32) {
    PrepareDistanceCacheHROLLING(&mut (*self_0).hb, distance_cache);
}
"#;
    const COMMAND: &str = r#"
#[repr(C)] pub struct Command { pub dist_prefix_: u16, pub dist_extra_: u32 }
#[repr(C)] pub struct BrotliDistanceParams { pub num_direct_distance_codes: u32, pub distance_postfix_bits: u32 }
#[repr(C)] pub struct State { pub dist: BrotliDistanceParams }
pub unsafe extern "C" fn CommandRestoreDistanceCode(self_0: *const Command, dist: *const BrotliDistanceParams) -> u32 {
    if ((*self_0).dist_prefix_ as u32 & 0x3ff) < 16u32.wrapping_add((*dist).num_direct_distance_codes) {
        (*self_0).dist_prefix_ as u32 & 0x3ff
    } else { (*self_0).dist_extra_.wrapping_add((*dist).distance_postfix_bits) }
}
pub unsafe extern "C" fn ExtendLastCommand(last_command: *mut Command, s: *mut State) -> u32 {
    let distance_code = CommandRestoreDistanceCode(last_command, &mut (*s).dist);
    (*last_command).dist_extra_ = distance_code;
    distance_code
}
"#;

    fn native_shared(source: &str, owner: &'static str, name: &'static str) {
        let output = ::utils::compilation::run_compiler_on_str(source, move |tcx| {
            use crate::bo_rewriter::{ast_transform, bridge_receipt::SignatureClassId, emit_files};
            let capture = ast_transform::capture_ast(tcx).expect("original AST");
            let (table, ctx) = crate::bo_rewriter::decide_table_with_ctx_config(
                tcx,
                Some((
                    crate::bo_rewriter::A5Mode::PreciseReplay,
                    Some(crate::bo_rewriter::WholeProgramAttestation::FrozenBenchmarkGraph),
                )),
            )
            .expect("native decisions");
            let (subject, decision) = table
                .entries
                .iter()
                .find(|(s, _)| {
                    tcx.def_path_str(s.fn_did.to_def_id()).ends_with(owner)
                        && s.param_name.as_deref() == Some(name)
                })
                .expect("corpus-derived subject");
            assert!(!ctx.mut_facts.is_defaulted(subject.fn_did, subject.local));
            assert!(!ctx.mut_facts.is_mutable(subject.fn_did, subject.local));
            let proof = table
                .seams
                .overlap_proofs
                .iter()
                .find(|p| p.callee == subject.fn_did && p.index == 1)
                .expect("native overlap receipt");
            assert_eq!(proof.verdict, A5SiteProofVerdict::Overlapping);
            assert!(proof.shared_permission.is_none(), "no synthetic permission");
            assert_eq!(proof.fallback, A5ProofSiteFallback::Primary);
            assert!(proof.reason.contains("native-shared-read-peers"));
            assert!(
                matches!(decision, Decision::Ref { mutable: false }),
                "{}: {decision:?}",
                subject.label
            );
            assert!(
                !ctx.coconv
                    .pair_sites()
                    .iter()
                    .any(|p| p.subject == (subject.fn_did, subject.hir_id)
                        && p.role == PairRole::RawView)
            );
            let emission = emit_files(tcx, &table, &Default::default(), &ctx.retained_c9_plans)
                .expect("emission plan");
            let held = emission.plan.held_classes();
            assert!(
                !held.contains(&SignatureClassId::of(subject.fn_did)),
                "shared subject placed"
            );
            let reverts = ast_transform::revert_set_from_classes_and_atoms(
                &held,
                &Default::default(),
                &table,
            )
            .expect("held classes");
            ast_transform::ast_emitted_files_from(
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
            .expect("source")
        })
        .expect("fixture compiles");
        assert!(
            crate::bo_rewriter::verify::type_checks_str(&output),
            "{output}"
        );
    }
    fn native_control(source: &str, check: impl FnOnce(&MutFacts, LocalDefId) + Send) {
        ::utils::compilation::run_compiler_on_str(source, |tcx| {
            let (_, ctx) = crate::bo_rewriter::decide_table_with_ctx_config(
                tcx,
                Some((
                    crate::bo_rewriter::A5Mode::PreciseReplay,
                    Some(crate::bo_rewriter::WholeProgramAttestation::FrozenBenchmarkGraph),
                )),
            )
            .expect("native control");
            let callee = ctx
                .subjects
                .iter()
                .find(|s| {
                    tcx.def_path_str(s.fn_did.to_def_id())
                        .ends_with("PrepareDistanceCacheHROLLING")
                })
                .unwrap()
                .fn_did;
            check(&ctx.mut_facts, callee);
        })
        .expect("control compiles");
    }
    #[test]
    fn wave6k_shared_pair_mutable_presentation_holds_with_immutable_native_facts() {
        native_control(ROLLING, |facts, callee| {
            assert!(!facts.is_defaulted(callee, Local::from_usize(1)));
            assert!(!facts.is_mutable(callee, Local::from_usize(1)));
            assert!(!admits(
                facts,
                callee,
                1,
                Form::Ref { mutable: false },
                [(0, Form::Ref { mutable: true })].into_iter()
            ));
        });
    }

    #[test]
    fn wave6k_shared_pair_missing_peer_holds() {
        native_control(ROLLING, |facts, callee| {
            assert!(!admits(
                facts,
                callee,
                1,
                Form::Ref { mutable: false },
                [0, 999]
                    .into_iter()
                    .map(|index| (index, Form::Ref { mutable: false }))
            ));
            assert!(!admits(
                facts,
                callee,
                999,
                Form::Ref { mutable: false },
                [0].into_iter()
                    .map(|index| (index, Form::Ref { mutable: false }))
            ));
            assert!(!admits(
                facts,
                callee,
                1,
                Form::Ref { mutable: false },
                [].into_iter()
                    .map(|index| (index, Form::Ref { mutable: false }))
            ));
            assert!(!admits(
                &MutFacts::all_mut(),
                callee,
                1,
                Form::Ref { mutable: false },
                [0].into_iter()
                    .map(|index| (index, Form::Ref { mutable: false }))
            ));
        });
    }
    #[test]
    fn wave6k_shared_pair_third_mutable_peer_holds() {
        let source = ROLLING
            .replace(
                "distance_cache: *mut i32) {}",
                "distance_cache: *mut i32, third: *mut i32) { *third = 1; }",
            )
            .replace(
                "hb, distance_cache);",
                "hb, distance_cache, distance_cache);",
            );
        native_control(&source, |facts, callee| {
            assert!(admits(
                facts,
                callee,
                1,
                Form::Ref { mutable: false },
                [0].into_iter()
                    .map(|index| (index, Form::Ref { mutable: false }))
            ));
            assert!(!admits(
                facts,
                callee,
                1,
                Form::Ref { mutable: false },
                [0, 2]
                    .into_iter()
                    .map(|index| (index, Form::Ref { mutable: false }))
            ));
        });
    }
    #[test]
    fn wave6k_shared_pair_mutable_peer_keeps_native_hold() {
        let source = ROLLING.replace(
            "distance_cache: *mut i32) {}",
            "distance_cache: *mut i32) { (*self_0).state = 1; }",
        );
        ::utils::compilation::run_compiler_on_str(&source, |tcx| {
            let (table, ctx) = crate::bo_rewriter::decide_table_with_ctx_config(
                tcx,
                Some((
                    crate::bo_rewriter::A5Mode::PreciseReplay,
                    Some(crate::bo_rewriter::WholeProgramAttestation::FrozenBenchmarkGraph),
                )),
            )
            .expect("mutable native control");
            let (subject, _) = table
                .entries
                .iter()
                .find(|(s, _)| {
                    tcx.def_path_str(s.fn_did.to_def_id())
                        .ends_with("PrepareDistanceCacheHROLLING")
                        && s.param_name.as_deref() == Some("distance_cache")
                })
                .unwrap();
            assert!(
                ctx.coconv
                    .pair_sites()
                    .iter()
                    .any(|p| p.subject == (subject.fn_did, subject.hir_id)
                        && matches!(p.role, PairRole::RawView | PairRole::Blocked))
            );
        })
        .expect("mutable fixture compiles");
    }
    #[test]
    fn wave6k_shared_pair_brotli_rolling_native() {
        native_shared(ROLLING, "PrepareDistanceCacheHROLLING", "distance_cache");
    }
    #[test]
    fn wave6k_shared_pair_brotli_command_native() {
        native_shared(COMMAND, "CommandRestoreDistanceCode", "dist");
    }
}
