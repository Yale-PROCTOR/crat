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

/// One exact address operator owed by a native read/read call. The place is
/// kept as an AST subtree; no expression is re-evaluated or reconstructed.
#[derive(Clone, Debug)]
pub(crate) struct SharedAddress {
    pub(crate) index: usize,
    pub(crate) argument: rustc_span::Span,
    pub(crate) place: rustc_span::Span,
}

#[derive(Clone, Debug)]
pub(crate) struct SharedCall {
    pub(crate) caller: LocalDefId,
    pub(crate) callee: LocalDefId,
    pub(crate) subjects: [rustc_hir::HirId; 2],
    pub(crate) addresses: Vec<SharedAddress>,
}

/// The initial read/read transaction is deliberately a two-argument call.
/// Even an otherwise unrelated scalar argument could mutate an earlier view.
/// Only local values and a field place under one dereference are admitted.
pub(super) fn prepare(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    table: &super::DecisionTable,
    callee: LocalDefId,
    site: &super::emitability::CallSite,
) -> Option<SharedCall> {
    use rustc_hir::{
        BorrowKind, Expr, ExprKind, Mutability, QPath, UnOp,
        def::Res,
        intravisit::{self, Visitor},
    };
    if site.args.len() != 2 {
        return None;
    }
    // Only a settled shared reference endpoint qualifies; every other
    // disposition (including a mutable reference) keeps the pair hold.
    let shared_endpoint = |d: &super::Decision| match d {
        super::Decision::Ref { mutable } => !mutable,
        super::Decision::InferredRef { .. }
        | super::Decision::Slice { .. }
        | super::Decision::NestedSlice { .. }
        | super::Decision::Opt { .. }
        | super::Decision::Box(_)
        | super::Decision::Cursor { .. }
        | super::Decision::Degraded(_) => false,
    };
    let subject = |index| {
        table.entries.iter().find_map(|(s, d)| {
            (s.fn_did == callee
                && matches!(s.kind, super::SubjectKind::Param { hir_index } if hir_index == index)
                && shared_endpoint(d))
            .then_some(s.hir_id)
        })
    };
    let subjects = [subject(0)?, subject(1)?];
    fn pure_place(
        tcx: rustc_middle::ty::TyCtxt<'_>,
        owner: LocalDefId,
        expr: &Expr<'_>,
        dereferenced: bool,
    ) -> bool {
        let typeck = tcx.typeck(owner);
        if !typeck.expr_adjustments(expr).is_empty() {
            return false;
        }
        match expr.kind {
            ExprKind::Field(base, _) => pure_place(tcx, owner, base, dereferenced),
            ExprKind::Unary(UnOp::Deref, base)
                if !dereferenced
                    && matches!(
                        typeck.expr_ty(base).kind(),
                        rustc_middle::ty::TyKind::RawPtr(..) | rustc_middle::ty::TyKind::Ref(..)
                    ) =>
            {
                pure_place(tcx, owner, base, true)
            }
            ExprKind::Path(QPath::Resolved(_, path)) => matches!(path.res, Res::Local(_)),
            _ => false,
        }
    }
    struct Find<'a, 'tcx> {
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
        site: &'a super::emitability::CallSite,
        matches: usize,
        addresses: Option<Vec<SharedAddress>>,
    }
    impl<'tcx> Visitor<'tcx> for Find<'_, 'tcx> {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            if expr.span == self.site.span
                && let ExprKind::Call(_, args) = expr.kind
            {
                self.matches += 1;
                let mut addresses = Vec::new();
                let pure = args.len() == 2
                    && args.iter().enumerate().all(|(index, arg)| match arg.kind {
                        ExprKind::Path(QPath::Resolved(_, path)) => {
                            matches!(path.res, Res::Local(_))
                        }
                        ExprKind::AddrOf(BorrowKind::Ref, mutable, place)
                            if matches!(place.kind, ExprKind::Field(..))
                                && pure_place(self.tcx, self.site.caller, place, false) =>
                        {
                            if mutable == Mutability::Mut {
                                addresses.push(SharedAddress {
                                    index,
                                    argument: arg.span,
                                    place: place.span,
                                });
                            }
                            true
                        }
                        _ => false,
                    });
                self.addresses = pure.then_some(addresses);
            }
            intravisit::walk_expr(self, expr);
        }
    }
    let mut find = Find {
        tcx,
        site,
        matches: 0,
        addresses: None,
    };
    let body = tcx.hir_node_by_def_id(site.caller).body_id()?;
    find.visit_body(tcx.hir_body(body));
    if find.matches != 1 {
        return None;
    }
    Some(SharedCall {
        caller: site.caller,
        callee,
        subjects,
        addresses: find.addresses?,
    })
}

/// Atom retirement closes the whole two-formal callee transaction, including
/// already materialized signature and argument edits.
pub(super) fn atom_owners(
    table: &super::DecisionTable,
) -> Vec<(String, crate::bo_rewriter::bridge_receipt::SignatureClassId)> {
    let mut owners = Vec::new();
    for call in &table.seams.shared_read_calls {
        for &subject in &call.subjects {
            if let Some(atoms) = table
                .seams
                .raw_boundary_atom_groups
                .get(&(call.callee, subject))
            {
                for atom in atoms {
                    owners.push((
                        atom.id.clone(),
                        crate::bo_rewriter::bridge_receipt::SignatureClassId::of(call.callee),
                    ));
                }
            }
        }
    }
    owners
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

    fn native_shared(source: &str, owner: &'static str, name: &'static str) -> String {
        native_shared_withdrawal(source, owner, name, None)
    }

    fn native_shared_withdrawal(
        source: &str,
        owner: &'static str,
        name: &'static str,
        withdraw: Option<&'static str>,
    ) -> String {
        let output = ::utils::compilation::run_compiler_on_str(source, move |tcx| {
            use crate::bo_rewriter::{ast_transform, bridge_receipt::SignatureClassId, emit_files};
            let capture = ast_transform::capture_ast(tcx).expect("original AST");
            let (mut table, ctx) = crate::bo_rewriter::decide_table_with_ctx_config(
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
            let owner_class = SignatureClassId::of(subject.fn_did);
            let mut atoms = std::collections::BTreeSet::new();
            if withdraw == Some("atom:dist") {
                let node = (subject.fn_did, subject.hir_id);
                let id = "shared-read-test-endpoint-retirement".to_owned();
                table
                    .seams
                    .raw_boundary_atom_groups
                    .entry(node)
                    .or_default()
                    .push(super::super::raw_boundary::SubjectAtomKey {
                        id: id.clone(),
                        node,
                        owner: owner.to_owned(),
                    });
                atoms.insert(id);
            }
            let emission = emit_files(tcx, &table, &Default::default(), &ctx.retained_c9_plans)
                .expect("emission plan");
            let mut held = emission.plan.held_classes();
            assert!(
                !held.contains(&owner_class),
                "shared subject placed: {:?}",
                emission.plan.class_finalization.classes.get(&owner_class)
            );
            if let Some(withdraw) = withdraw.filter(|value| *value != "atom:dist") {
                let function = table
                    .entries
                    .iter()
                    .find(|(s, _)| tcx.def_path_str(s.fn_did.to_def_id()).ends_with(withdraw))
                    .unwrap()
                    .0
                    .fn_did;
                held.insert(SignatureClassId::of(function));
            }
            let reverts = ast_transform::revert_set_from_classes_and_atoms(&held, &atoms, &table)
                .expect("held classes");
            if !atoms.is_empty() {
                assert!(
                    !reverts.keeps(owner_class),
                    "AST must close the callee class"
                );
                let effective = emission.plan.effective_reverted_classes(&held, &atoms);
                assert!(
                    effective.contains(&owner_class),
                    "planner must close same class"
                );
                let mut withdrawn_plan = emission.plan.clone();
                for edits in withdrawn_plan.by_file.values_mut() {
                    edits.retain(|edit| {
                        edit.owner_class
                            .is_none_or(|class| !effective.contains(&class))
                    });
                }
                let (text, rollbacks, _) =
                    crate::bo_rewriter::validate_plan(&withdrawn_plan, &emission.texts);
                assert!(rollbacks.is_empty(), "withdrawn text plan must compose");
                assert!(
                    text.values()
                        .any(|source| source.contains("&mut (*s).dist"))
                );
                assert!(
                    emission
                        .plan
                        .by_file
                        .values()
                        .flatten()
                        .any(|edit| edit.edit_kind == "native-shared-read-address"
                            && edit.owner_class == Some(owner_class))
                );
            }
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
        output
    }

    fn mutable_state_command() -> String {
        COMMAND
            .replace(
                "pub struct State { pub dist: BrotliDistanceParams }",
                "pub struct State { pub dist: BrotliDistanceParams, pub counter: u32 }",
            )
            .replace(
                "(*last_command).dist_extra_ = distance_code;",
                "(*last_command).dist_extra_ = distance_code; (*s).counter += 1;",
            )
    }

    #[test]
    fn wave6k_shared_pair_mutable_state_argument_is_shared() {
        let output = native_shared(
            &mutable_state_command(),
            "CommandRestoreDistanceCode",
            "dist",
        );
        assert!(!output.contains("&mut (*s).dist"), "{output}");
        assert!(output.contains("&(*s).dist"), "{output}");
    }

    #[test]
    fn wave6k_shared_pair_withdrawn_caller_keeps_shared_argument() {
        let output = native_shared_withdrawal(
            &mutable_state_command(),
            "CommandRestoreDistanceCode",
            "dist",
            Some("ExtendLastCommand"),
        );
        assert!(!output.contains("&mut (*s).dist"), "{output}");
        assert!(output.contains("&(*s).dist"), "{output}");
        assert!(output.contains("s: *mut State"), "{output}");
    }

    #[test]
    fn wave6k_shared_pair_withdrawn_callee_restores_address() {
        let output = native_shared_withdrawal(
            &mutable_state_command(),
            "CommandRestoreDistanceCode",
            "dist",
            Some("CommandRestoreDistanceCode"),
        );
        assert!(output.contains("&mut (*s).dist"), "{output}");
    }

    #[test]
    fn wave6k_shared_pair_partial_callee_withdrawal_closes_class() {
        let output = native_shared_withdrawal(
            &mutable_state_command(),
            "CommandRestoreDistanceCode",
            "dist",
            Some("atom:dist"),
        );
        assert!(output.contains("&mut (*s).dist"), "{output}");
        assert!(
            output.contains("dist: *const BrotliDistanceParams"),
            "{output}"
        );
    }

    fn unsupported_call(source: &str, owner: &'static str) {
        ::utils::compilation::run_compiler_on_str(source, move |tcx| {
            let (table, ctx) = crate::bo_rewriter::decide_table_with_ctx_config(
                tcx,
                Some((
                    crate::bo_rewriter::A5Mode::PreciseReplay,
                    Some(crate::bo_rewriter::WholeProgramAttestation::FrozenBenchmarkGraph),
                )),
            )
            .expect("native unsupported construction");
            let callee = table
                .entries
                .iter()
                .find(|(subject, _)| {
                    tcx.def_path_str(subject.fn_did.to_def_id())
                        .ends_with(owner)
                })
                .unwrap()
                .0
                .fn_did;
            assert!(
                !table
                    .seams
                    .shared_read_calls
                    .iter()
                    .any(|call| call.callee == callee)
            );
            let sites = ctx.facts.call_args.get(&callee).unwrap();
            let mut hypothetical = table.clone();
            for (subject, decision) in &mut hypothetical.entries {
                if subject.fn_did == callee {
                    *decision = Decision::Ref { mutable: false };
                }
            }
            assert!(
                sites
                    .iter()
                    .all(|site| prepare(tcx, &hypothetical, callee, site).is_none())
            );
        })
        .expect("unsupported input compiles");
    }

    #[test]
    fn wave6k_shared_pair_side_effecting_scalar_argument_holds() {
        let source = mutable_state_command()
            .replace(
                "dist: *const BrotliDistanceParams) -> u32",
                "dist: *const BrotliDistanceParams, effect: u32) -> u32",
            )
            .replace(
                "last_command, &mut (*s).dist);",
                "last_command, &mut (*s).dist, { (*s).counter += 1; 0 });",
            );
        unsupported_call(&source, "CommandRestoreDistanceCode");
    }

    #[test]
    fn wave6k_shared_pair_side_effecting_address_argument_holds() {
        let source = mutable_state_command()
            .replace("&mut (*s).dist);", "&mut (*advance(s)).dist);")
            + "pub unsafe fn advance(s: *mut State) -> *mut State { (*s).counter += 1; s }";
        unsupported_call(&source, "CommandRestoreDistanceCode");
    }

    /// The endpoint predicate is a second gate behind the native immutable
    /// facts: even on the supported shape, a mutable reference endpoint must
    /// refuse the whole two-argument transaction.
    #[test]
    fn wave6k_shared_pair_mutable_reference_endpoint_refuses_preparation() {
        let source = mutable_state_command();
        ::utils::compilation::run_compiler_on_str(&source, move |tcx| {
            let (table, ctx) = crate::bo_rewriter::decide_table_with_ctx_config(
                tcx,
                Some((
                    crate::bo_rewriter::A5Mode::PreciseReplay,
                    Some(crate::bo_rewriter::WholeProgramAttestation::FrozenBenchmarkGraph),
                )),
            )
            .expect("native shared construction");
            let callee = table
                .entries
                .iter()
                .find(|(subject, _)| {
                    tcx.def_path_str(subject.fn_did.to_def_id())
                        .ends_with("CommandRestoreDistanceCode")
                })
                .unwrap()
                .0
                .fn_did;
            let sites = ctx.facts.call_args.get(&callee).unwrap();
            assert!(
                sites
                    .iter()
                    .any(|site| prepare(tcx, &table, callee, site).is_some()),
                "control: the supported shape prepares"
            );
            let mut hypothetical = table.clone();
            for (subject, decision) in &mut hypothetical.entries {
                if subject.fn_did == callee
                    && matches!(
                        subject.kind,
                        super::super::SubjectKind::Param { hir_index: 1 }
                    )
                {
                    *decision = Decision::Ref { mutable: true };
                }
            }
            assert!(
                sites
                    .iter()
                    .all(|site| prepare(tcx, &hypothetical, callee, site).is_none()),
                "a mutable reference endpoint must not prepare"
            );
        })
        .expect("input compiles");
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
