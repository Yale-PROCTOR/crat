use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::{mir::Local, ty::TyCtxt};
use rustc_span::def_id::LocalDefId;

pub use crate::analyses::borrow_ownership::origin_summary::{
    OriginSummary, SignatureRoot, SignatureSlot,
};
use crate::{
    analyses::{
        borrow_ownership::{
            SlotKind,
            construction::solve_bo_overlap_config,
            crate_slots::CrateSlots,
            mutability::mutability_analysis,
            mutability_facts::MutFacts,
            nullability,
            origins::compute_origins,
            param_overlap::{OverlapMode, WholeProgramAttestation},
            solver::SlotRef,
        },
        type_qualifier::foster::{
            fatness::{FatnessResult, fatness_analysis},
            mutability::MutabilityResult,
        },
    },
    utils::rustc::RustProgram,
};

/// Accepted inference and its source facts, before any symbolic rewrite decisions.
pub struct AcceptedPointerAnalysis {
    pub slots: CrateSlots,
    pub kinds: FxHashMap<SlotRef, SlotKind>,
    pub origins: FxHashMap<LocalDefId, OriginSummary>,
    pub mutability: MutabilityResult,
    pub fatness: FatnessResult,
    pub nullable: FxHashSet<SlotRef>,
    outer_mutability: FxHashMap<(LocalDefId, Local), bool>,
}

impl AcceptedPointerAnalysis {
    pub fn is_mutable(&self, function: LocalDefId, local: Local) -> bool {
        self.outer_mutability
            .get(&(function, local))
            .copied()
            .unwrap_or(true)
    }
}

pub fn analyze_pointers(tcx: TyCtxt<'_>) -> Result<AcceptedPointerAnalysis, String> {
    let mut program = RustProgram {
        tcx,
        functions: Vec::new(),
        structs: Vec::new(),
    };
    for owner in tcx
        .hir_crate(())
        .owners
        .iter()
        .filter_map(|owner| owner.as_owner())
    {
        let OwnerNode::Item(item) = owner.node() else { continue };
        match item.kind {
            ItemKind::Fn { .. } if !item.span.in_derive_expansion() => {
                program.functions.push(item.owner_id.def_id)
            }
            ItemKind::Struct(..) if !item.span.in_derive_expansion() => {
                program.structs.push(item.owner_id.def_id)
            }
            _ => {}
        }
    }
    let slots = CrateSlots::build(&program);
    let mutability = mutability_analysis(&program);
    let replay_mutability = MutFacts::from_program(&program);
    let origins = compute_origins(&program);
    let verified = solve_bo_overlap_config(
        &program,
        &slots,
        &origins,
        &replay_mutability,
        OverlapMode::PreciseReplay,
        Some(WholeProgramAttestation::FrozenBenchmarkGraph),
    )
    .ok_or_else(|| "BO analysis declined: no accepted pointer model".to_owned())?;
    let nullable = nullability::analyze(tcx, &program.functions, &slots).slots();
    let fatness = fatness_analysis(&program);
    let mut outer_mutability = FxHashMap::default();
    for &function in &program.functions {
        let body = tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        for local in body.local_decls.indices() {
            outer_mutability.insert(
                (function, local),
                replay_mutability.is_mutable(function, local),
            );
        }
    }
    Ok(AcceptedPointerAnalysis {
        slots,
        kinds: verified.model,
        origins: origins
            .iter()
            .map(|(&function, summary)| (function, summary.clone()))
            .collect(),
        mutability,
        fatness,
        nullable,
        outer_mutability,
    })
}
