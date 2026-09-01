//! Raw-boundary facts and decisions.
//!
//! This module is rewriter-side by design. It consumes the frozen model/MIR and
//! never contributes a solver constraint or cache field.

use rustc_hash::FxHashMap;
use rustc_hir::{HirId, def_id::LocalDefId};
use rustc_middle::{
    mir::{Operand, TerminatorKind},
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_span::{Span, def_id::DefId};

use crate::{
    analyses::borrow_ownership::{
        a5_overlap::WholeProgramAttestation, origin_summary::OriginSummaries,
    },
    utils::rustc::RustProgram,
};

/// A lifetime-free, artifact-stable call-site identity.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct RawBoundarySiteKey {
    pub caller: String,
    pub block: u32,
    pub statement_index: u32,
    pub callee: ForeignSymbolKey,
    pub argument_index: usize,
    pub subject: String,
}

/// Resolved callee identity. `foreign` is load-bearing: a same-spelled local
/// function is not a libc contract match.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct ForeignSymbolKey {
    pub symbol: String,
    pub path: String,
    pub abi: String,
    pub signature: String,
    pub foreign: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RawMutability {
    Const,
    Mut,
}

impl RawMutability {
    fn key(self) -> &'static str {
        match self {
            Self::Const => "const",
            Self::Mut => "mut",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RawTargetType {
    pub rendered: String,
    pub pointee: String,
    pub mutability: RawMutability,
}

pub(crate) fn raw_target_type(ty: Ty<'_>) -> Option<RawTargetType> {
    let TyKind::RawPtr(pointee, mutability) = ty.kind() else {
        return None;
    };
    Some(RawTargetType {
        rendered: format!("{ty:?}"),
        pointee: format!("{pointee:?}"),
        mutability: if mutability.is_mut() {
            RawMutability::Mut
        } else {
            RawMutability::Const
        },
    })
}

/// One resolved argument to a non-body callee. This is the fact the old
/// `EscapeKind::ForeignArg` could not express: callee, position and target type
/// are captured at the HIR visitor boundary rather than reconstructed later.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ForeignCallArgFact {
    pub caller: LocalDefId,
    pub callee: ForeignSymbolKey,
    pub call_span: Span,
    pub argument_index: usize,
    pub argument_span: Span,
    pub root: Option<HirId>,
    pub shape: &'static str,
    pub source_type: String,
    pub target: RawTargetType,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BoundaryDirection {
    OutgoingArgument,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RawBoundarySiteFact {
    pub key: RawBoundarySiteKey,
    pub direction: BoundaryDirection,
    pub source_span: Span,
    pub source_shape: &'static str,
    pub source_type: String,
    pub target: RawTargetType,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RawBoundarySiteFailure {
    pub caller: String,
    pub callee: ForeignSymbolKey,
    pub argument_index: usize,
    pub source_span: Span,
    pub reason: SiteMatchFailure,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct RawBoundarySiteFacts {
    pub sites: Vec<RawBoundarySiteFact>,
    pub failures: Vec<RawBoundarySiteFailure>,
}

pub(crate) fn symbol_key(
    tcx: TyCtxt<'_>,
    callee: DefId,
    body_functions: &[LocalDefId],
) -> ForeignSymbolKey {
    let sig = tcx.fn_sig(callee).skip_binder().skip_binder();
    let foreign = !callee
        .as_local()
        .is_some_and(|local| body_functions.contains(&local));
    ForeignSymbolKey {
        symbol: tcx.item_name(callee).to_string(),
        path: tcx.def_path_str(callee),
        abi: format!("{:?}", sig.abi),
        signature: format!("{sig:?}"),
        foreign,
    }
}

fn operand_callee(func: &Operand<'_>) -> Option<DefId> {
    let constant = func.constant()?;
    let TyKind::FnDef(callee, _) = *constant.ty().kind() else {
        return None;
    };
    Some(callee)
}

fn mir_candidates(
    tcx: TyCtxt<'_>,
    functions: &[LocalDefId],
    caller: LocalDefId,
    expected: &ForeignSymbolKey,
    argument_span: Span,
) -> Vec<MirCallCandidate> {
    let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
    let argument_span = argument_span.source_callsite();
    body.basic_blocks
        .iter_enumerated()
        .filter_map(|(block, data)| {
            let terminator = data.terminator();
            let func = match &terminator.kind {
                TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. } => func,
                _ => return None,
            };
            let callee = operand_callee(func)?;
            let key = symbol_key(tcx, callee, functions);
            let call_span = terminator.source_info.span.source_callsite();
            (key == *expected && call_span.contains(argument_span)).then_some(MirCallCandidate {
                block: block.as_u32(),
                statement_index: data.statements.len() as u32,
                callee: key,
            })
        })
        .collect()
}

impl RawBoundarySiteFacts {
    pub(crate) fn derive(
        program: &RustProgram<'_>,
        emitability: &super::emitability::EmitabilityFacts,
    ) -> Self {
        let tcx = program.tcx;
        let mut out = Self::default();
        for fact in &emitability.foreign_call_args {
            let candidates = mir_candidates(
                tcx,
                &program.functions,
                fact.caller,
                &fact.callee,
                fact.argument_span,
            );
            match select_unique_site(&fact.callee, &candidates) {
                Ok((block, statement_index)) => out.sites.push(RawBoundarySiteFact {
                    key: RawBoundarySiteKey {
                        caller: tcx.def_path_str(fact.caller.to_def_id()),
                        block,
                        statement_index,
                        callee: fact.callee.clone(),
                        argument_index: fact.argument_index,
                        subject: fact
                            .root
                            .map_or_else(|| "<unrooted>".to_owned(), |root| format!("{root:?}")),
                    },
                    direction: BoundaryDirection::OutgoingArgument,
                    source_span: fact.argument_span,
                    source_shape: fact.shape,
                    source_type: fact.source_type.clone(),
                    target: fact.target.clone(),
                }),
                Err(reason) => out.failures.push(RawBoundarySiteFailure {
                    caller: tcx.def_path_str(fact.caller.to_def_id()),
                    callee: fact.callee.clone(),
                    argument_index: fact.argument_index,
                    source_span: fact.argument_span,
                    reason,
                }),
            }
        }
        for (&callee, calls) in &emitability.call_args {
            let callee_key = symbol_key(tcx, callee.to_def_id(), &program.functions);
            for call in calls {
                for argument in &call.args {
                    let Some(target) = argument.target.clone() else {
                        continue;
                    };
                    let candidates = mir_candidates(
                        tcx,
                        &program.functions,
                        call.caller,
                        &callee_key,
                        argument.span,
                    );
                    match select_unique_site(&callee_key, &candidates) {
                        Ok((block, statement_index)) => out.sites.push(RawBoundarySiteFact {
                            key: RawBoundarySiteKey {
                                caller: tcx.def_path_str(call.caller.to_def_id()),
                                block,
                                statement_index,
                                callee: callee_key.clone(),
                                argument_index: argument.index,
                                subject: argument.shape.place_root().map_or_else(
                                    || "<unrooted>".to_owned(),
                                    |root| format!("{root:?}"),
                                ),
                            },
                            direction: BoundaryDirection::OutgoingArgument,
                            source_span: argument.span,
                            source_shape: argument.shape.key(),
                            source_type: argument.source_type.clone(),
                            target,
                        }),
                        Err(reason) => out.failures.push(RawBoundarySiteFailure {
                            caller: tcx.def_path_str(call.caller.to_def_id()),
                            callee: callee_key.clone(),
                            argument_index: argument.index,
                            source_span: argument.span,
                            reason,
                        }),
                    }
                }
            }
        }
        out.sites.sort_by(|left, right| left.key.cmp(&right.key));
        out.failures.sort_by(|left, right| {
            (&left.caller, &left.callee, left.argument_index).cmp(&(
                &right.caller,
                &right.callee,
                right.argument_index,
            ))
        });
        out
    }

    pub(crate) fn to_tsv(&self) -> String {
        let mut out = String::from(
            "status\tcaller\tblock\tstatement_index\tcallee_path\tcallee_symbol\tforeign\tabi\tsignature\targument_index\tsubject\tsource_lo\tsource_hi\tsource_shape\tsource_type\ttarget_type\ttarget_pointee\ttarget_mutability\treason\n",
        );
        for site in &self.sites {
            out.push_str(&format!(
                "site\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t-\n",
                site.key.caller,
                site.key.block,
                site.key.statement_index,
                site.key.callee.path,
                site.key.callee.symbol,
                u8::from(site.key.callee.foreign),
                site.key.callee.abi,
                site.key.callee.signature,
                site.key.argument_index,
                site.key.subject,
                site.source_span.lo().0,
                site.source_span.hi().0,
                site.source_shape,
                site.source_type,
                site.target.rendered,
                site.target.pointee,
                site.target.mutability.key(),
            ));
        }
        for failure in &self.failures {
            out.push_str(&format!(
                "failure\t{}\t-\t-\t{}\t{}\t{}\t{}\t{}\t{}\t-\t{}\t{}\t-\t-\t-\t-\t-\t{}\n",
                failure.caller,
                failure.callee.path,
                failure.callee.symbol,
                u8::from(failure.callee.foreign),
                failure.callee.abi,
                failure.callee.signature,
                failure.argument_index,
                failure.source_span.lo().0,
                failure.source_span.hi().0,
                failure.reason.key(),
            ));
        }
        out
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MirCallCandidate {
    pub block: u32,
    pub statement_index: u32,
    pub callee: ForeignSymbolKey,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SiteMatchFailure {
    Missing,
    Ambiguous,
    CalleeMismatch,
}

impl SiteMatchFailure {
    fn key(self) -> &'static str {
        match self {
            Self::Missing => "site-missing",
            Self::Ambiguous => "site-ambiguous",
            Self::CalleeMismatch => "callee-mismatch",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum RetentionUnknownReason {
    CalleeUnresolved,
    FnPtrWeb,
    OpenBoundary,
    MultiDef,
    NontransparentDef,
    ProjectionAmbiguous,
    OutputStorage,
    FieldOrGlobalStore,
    Return,
    LocalSummaryUnknown,
    AttestationAbsent,
    AnalysisIncomplete,
}

impl RetentionUnknownReason {
    pub(crate) const ALL: [Self; 12] = [
        Self::CalleeUnresolved,
        Self::FnPtrWeb,
        Self::OpenBoundary,
        Self::MultiDef,
        Self::NontransparentDef,
        Self::ProjectionAmbiguous,
        Self::OutputStorage,
        Self::FieldOrGlobalStore,
        Self::Return,
        Self::LocalSummaryUnknown,
        Self::AttestationAbsent,
        Self::AnalysisIncomplete,
    ];

    pub(crate) fn key(self) -> &'static str {
        match self {
            Self::CalleeUnresolved => "retention-callee-unresolved",
            Self::FnPtrWeb => "retention-fnptr-web",
            Self::OpenBoundary => "retention-open-boundary",
            Self::MultiDef => "retention-multi-def",
            Self::NontransparentDef => "retention-nontransparent-def",
            Self::ProjectionAmbiguous => "retention-projection-ambiguous",
            Self::OutputStorage => "retention-output-storage",
            Self::FieldOrGlobalStore => "retention-field-or-global-store",
            Self::Return => "retention-return",
            Self::LocalSummaryUnknown => "retention-local-summary-unknown",
            Self::AttestationAbsent => "retention-attestation-absent",
            Self::AnalysisIncomplete => "retention-analysis-incomplete",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum RetentionEventKind {
    Return,
    OutputStorage,
    FieldOrGlobalStore,
    UnknownCall,
    KnownNoRetainCall,
    LocalCall,
    DereferenceOnly,
    Free,
    MultiDef,
    Nontransparent,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct RetentionStep {
    pub location: String,
    pub kind: RetentionEventKind,
    pub detail: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RetentionCertificate {
    pub function: String,
    pub argument_index: usize,
    pub steps: Vec<RetentionStep>,
    pub attestation: &'static str,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum RetentionVerdict {
    NoRetain {
        certificate: RetentionCertificate,
    },
    Retains {
        sink: RetentionStep,
        path: Vec<RetentionStep>,
    },
    Unknown {
        reason: RetentionUnknownReason,
        frontier: Vec<RetentionStep>,
    },
}

#[derive(Clone, Debug, Default)]
pub(crate) struct RetentionSummaries {
    rows: FxHashMap<(LocalDefId, usize), RetentionVerdict>,
}

impl RetentionSummaries {
    pub(crate) fn derive(
        program: &RustProgram<'_>,
        _origins: Option<&OriginSummaries>,
        _attestation: Option<WholeProgramAttestation>,
    ) -> Self {
        let mut rows = FxHashMap::default();
        for &function in &program.functions {
            let body = program
                .tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            for argument_index in 0..body.arg_count {
                let local = rustc_middle::mir::Local::from_usize(argument_index + 1);
                if !matches!(body.local_decls[local].ty.kind(), TyKind::RawPtr(..)) {
                    continue;
                }
                rows.insert(
                    (function, argument_index),
                    RetentionVerdict::Unknown {
                        reason: RetentionUnknownReason::AnalysisIncomplete,
                        frontier: Vec::new(),
                    },
                );
            }
        }
        Self { rows }
    }

    pub(crate) fn get(
        &self,
        function: LocalDefId,
        argument_index: usize,
    ) -> Option<&RetentionVerdict> {
        self.rows.get(&(function, argument_index))
    }

    pub(crate) fn verify_certificate(
        &self,
        function: LocalDefId,
        argument_index: usize,
        certificate: &RetentionCertificate,
    ) -> Result<(), &'static str> {
        match self.get(function, argument_index) {
            Some(RetentionVerdict::NoRetain {
                certificate: expected,
            }) if expected == certificate => Ok(()),
            _ => Err("retention-certificate-invalid"),
        }
    }
}

/// Select the one MIR call which represents an already-resolved HIR call site.
/// Zero and multiple matches stay typed rather than choosing by traversal
/// order.
pub(crate) fn select_unique_site(
    expected: &ForeignSymbolKey,
    candidates: &[MirCallCandidate],
) -> Result<(u32, u32), SiteMatchFailure> {
    let mut matching = candidates.iter().filter(|site| site.callee == *expected);
    let Some(site) = matching.next() else {
        return Err(if candidates.is_empty() {
            SiteMatchFailure::Missing
        } else {
            SiteMatchFailure::CalleeMismatch
        });
    };
    if matching.next().is_some() {
        return Err(SiteMatchFailure::Ambiguous);
    }
    Ok((site.block, site.statement_index))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn retention_of(
        src: &str,
        function_suffix: &str,
        attestation: Option<WholeProgramAttestation>,
    ) -> (RetentionVerdict, Result<(), &'static str>) {
        ::utils::compilation::run_compiler_on_str(src, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let origins = crate::analyses::borrow_ownership::origins::compute_origins(&program);
            let function = program
                .functions
                .iter()
                .copied()
                .find(|function| {
                    tcx.def_path_str(function.to_def_id())
                        .ends_with(function_suffix)
                })
                .expect("fixture function");
            let summaries = RetentionSummaries::derive(&program, Some(&origins), attestation);
            let verdict = summaries
                .get(function, 0)
                .expect("argument summary")
                .clone();
            let verification = match &verdict {
                RetentionVerdict::NoRetain { certificate } => {
                    summaries.verify_certificate(function, 0, certificate)
                }
                _ => Err("not-a-certificate"),
            };
            (verdict, verification)
        })
        .expect("fixture compiles")
    }

    fn symbol(name: &str, foreign: bool) -> ForeignSymbolKey {
        ForeignSymbolKey {
            symbol: name.to_owned(),
            path: format!("fixture::{name}"),
            abi: "C".to_owned(),
            signature: "(*mut i32)->()".to_owned(),
            foreign,
        }
    }

    #[test]
    fn rb_x1_exact_single_call_candidate_builds_owned_key() {
        let expected = symbol("consume", true);
        let site = select_unique_site(
            &expected,
            &[MirCallCandidate {
                block: 7,
                statement_index: 3,
                callee: expected.clone(),
            }],
        );
        assert_eq!(site, Ok((7, 3)));
    }

    #[test]
    fn rb_x1_zero_or_multiple_candidates_fail_closed() {
        let expected = symbol("consume", true);
        assert_eq!(
            select_unique_site(&expected, &[]),
            Err(SiteMatchFailure::Missing)
        );
        let one = MirCallCandidate {
            block: 1,
            statement_index: 0,
            callee: expected.clone(),
        };
        assert_eq!(
            select_unique_site(&expected, &[one.clone(), one]),
            Err(SiteMatchFailure::Ambiguous)
        );
    }

    #[test]
    fn rb_x1_same_spelled_local_is_not_the_foreign_site() {
        let expected = symbol("consume", true);
        let local = symbol("consume", false);
        assert_eq!(
            select_unique_site(
                &expected,
                &[MirCallCandidate {
                    block: 2,
                    statement_index: 1,
                    callee: local,
                }],
            ),
            Err(SiteMatchFailure::CalleeMismatch)
        );
    }

    #[test]
    fn rb_x1_target_mutability_is_not_collapsed() {
        assert_ne!(RawMutability::Const, RawMutability::Mut);
    }

    #[test]
    fn rb_x1_foreign_argument_fact_carries_callee_position_and_target_type() {
        let src = r#"
            extern "C" { fn consume(p: *mut i32); }
            unsafe fn caller(p: *mut i32) { consume(p); }
        "#;
        let fact = ::utils::compilation::run_compiler_on_str(src, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let facts = super::super::emitability::collect(tcx, &program.functions);
            assert_eq!(
                facts.foreign_call_args.len(),
                1,
                "{:#?}",
                facts.foreign_call_args
            );
            facts.foreign_call_args[0].clone()
        })
        .expect("fixture compiles");
        assert_eq!(fact.callee.symbol, "consume");
        assert!(fact.callee.foreign);
        assert_eq!(fact.argument_index, 0);
        assert_eq!(fact.shape, "bare-local");
        assert_eq!(fact.target.mutability, RawMutability::Mut);
        assert!(fact.target.pointee.contains("i32"), "{fact:#?}");
    }

    #[test]
    fn rb_x1_derived_foreign_site_has_the_exact_mir_location() {
        let src = r#"
            extern "C" { fn consume(p: *mut i32); }
            unsafe fn caller(p: *mut i32) { consume(p); }
        "#;
        let sites = ::utils::compilation::run_compiler_on_str(src, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let facts = super::super::emitability::collect(tcx, &program.functions);
            RawBoundarySiteFacts::derive(&program, &facts)
        })
        .expect("fixture compiles");
        assert!(sites.failures.is_empty(), "{sites:#?}");
        assert_eq!(sites.sites.len(), 1, "{sites:#?}");
        let site = &sites.sites[0];
        assert_eq!(site.key.argument_index, 0);
        assert_eq!(site.key.callee.symbol, "consume");
        assert_eq!(site.target.mutability, RawMutability::Mut);
        assert_eq!(sites.to_tsv(), sites.clone().to_tsv());
    }

    #[test]
    fn rb_x1_direct_local_call_uses_the_same_owned_site_domain() {
        let src = r#"
            unsafe fn consume(p: *mut i32) { *p = 1; }
            unsafe fn caller(p: *mut i32) { consume(p); }
        "#;
        let sites = ::utils::compilation::run_compiler_on_str(src, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let facts = super::super::emitability::collect(tcx, &program.functions);
            RawBoundarySiteFacts::derive(&program, &facts)
        })
        .expect("fixture compiles");
        assert!(sites.failures.is_empty(), "{sites:#?}");
        assert_eq!(sites.sites.len(), 1, "{sites:#?}");
        assert!(!sites.sites[0].key.callee.foreign);
        assert_eq!(sites.sites[0].key.argument_index, 0);
    }

    #[test]
    fn rb_x1_variadic_raw_argument_keeps_its_position_and_contract() {
        let src = r#"
            extern "C" { fn printf(fmt: *const i8, ...) -> i32; }
            unsafe fn caller(fmt: *const i8, p: *const i8) { printf(fmt, p); }
        "#;
        let facts = ::utils::compilation::run_compiler_on_str(src, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            super::super::emitability::collect(tcx, &program.functions).foreign_call_args
        })
        .expect("fixture compiles");
        assert_eq!(facts.len(), 2, "{facts:#?}");
        assert_eq!(facts[1].argument_index, 1);
        assert_eq!(
            super::super::raw_boundary_contracts::classify_contract(
                &facts[1].callee,
                facts[1].argument_index,
                &facts[1].target,
            )
            .expect("printf vararg contract")
            .retention,
            super::super::raw_boundary_contracts::RetentionContract::NoRetain
        );
    }

    #[test]
    fn rb_w2_local_pointee_access_without_escape_has_a_verified_certificate() {
        let (verdict, verification) = retention_of(
            "unsafe fn no_retain(p: *mut i32) { let _ = *p; *p = 1; }",
            "no_retain",
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        );
        assert!(
            matches!(verdict, RetentionVerdict::NoRetain { .. }),
            "{verdict:#?}"
        );
        assert_eq!(verification, Ok(()));
    }

    #[test]
    fn rb_w3_returned_pointer_is_positive_retention() {
        let (verdict, _) = retention_of(
            "unsafe fn returns(p: *mut i32) -> *mut i32 { p }",
            "returns",
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        );
        assert!(
            matches!(
                verdict,
                RetentionVerdict::Retains {
                    sink: RetentionStep {
                        kind: RetentionEventKind::Return,
                        ..
                    },
                    ..
                }
            ),
            "{verdict:#?}"
        );
    }

    #[test]
    fn rb_w10_missing_attestation_is_typed_unknown() {
        let (verdict, _) = retention_of(
            "unsafe fn no_retain(p: *mut i32) { let _ = *p; }",
            "no_retain",
            None,
        );
        assert!(
            matches!(
                verdict,
                RetentionVerdict::Unknown {
                    reason: RetentionUnknownReason::AttestationAbsent,
                    ..
                }
            ),
            "{verdict:#?}"
        );
    }

    #[test]
    fn rb_n1_multi_definition_alias_is_typed_unknown() {
        let (verdict, _) = retention_of(
            "unsafe fn branch(p: *mut i32, q: *mut i32, flag: bool) { let mut x = p; if flag { x = q; } let _ = *x; }",
            "branch",
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        );
        assert!(
            matches!(
                verdict,
                RetentionVerdict::Unknown {
                    reason: RetentionUnknownReason::MultiDef,
                    ..
                }
            ),
            "{verdict:#?}"
        );
    }

    #[test]
    fn rb_n2_function_pointer_call_is_typed_unknown() {
        let (verdict, _) = retention_of(
            "unsafe fn indirect(p: *mut i32, cb: unsafe fn(*mut i32)) { cb(p); }",
            "indirect",
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        );
        assert!(
            matches!(
                verdict,
                RetentionVerdict::Unknown {
                    reason: RetentionUnknownReason::FnPtrWeb,
                    ..
                }
            ),
            "{verdict:#?}"
        );
    }

    #[test]
    fn rb_n3_positive_retention_never_collapses_to_unknown() {
        let (verdict, _) = retention_of(
            "unsafe fn returns(p: *mut i32) -> *mut i32 { p }",
            "returns",
            Some(WholeProgramAttestation::FrozenBenchmarkGraph),
        );
        assert!(
            matches!(verdict, RetentionVerdict::Retains { .. }),
            "{verdict:#?}"
        );
    }
}
