//! **The AST application layer's bridge** — phases 1 and 2 of the migration.
//!
//! Standing decision 3 requires structure-preserving AST rewriting. The M1
//! application layer departed from it into byte splicing (departure recorded
//! 2026-08-12); this module is where the return begins.
//!
//! # The ordering constraint, and why it is not negotiable
//!
//! [`::utils::ast::expanded_ast`] **panics once the HIR is built** — it clones
//! the resolver's crate, and the resolver is consumed by lowering. Every
//! consumer of this module must therefore capture the AST as the FIRST action
//! inside the compiler callback, before `decide_table` or any other query
//! touches HIR or MIR.
//!
//! That is a constraint on call order, not a limitation: the AST is an input to
//! the pipeline exactly as the MIR is, and nothing about the decision layer
//! needs to run before it.
//!
//! # What the map is, and which direction it runs
//!
//! [`::utils::ast::make_ast_to_hir`] yields `AstToHir`, whose `local_map` sends
//! **AST `NodeId` → HIR `HirId`** and whose `global_map` sends
//! **AST `NodeId` → `LocalDefId`**. That is the FORWARD direction, and it is the
//! one a tree walk wants: the transform visitor walks the AST, reads each
//! node's own `NodeId`, resolves it to a `HirId`, and asks the decision table —
//! which is keyed by `(LocalDefId, HirId)` — what to do. No inversion is
//! needed, and none is built.
//!
//! `map_pat_to_pat` maps an AST `PatKind::Ident` onto `hir::PatKind::Binding`,
//! which is exactly the key M1 uses for both universes: a subject's `hir_id` is
//! its binding pattern's.
//!
//! # The mapper's failure mode is a PANIC, not a miss
//!
//! `ast_to_hir.rs` carries 161 assertions and asserts its way through every
//! structural correspondence it expects. A shape it does not expect aborts the
//! mapping rather than returning `None` for one node. So a resolution failure
//! can present as a panic over a whole crate, and the census below runs the
//! mapping inside `catch_unwind` for that reason — a program whose mapping
//! aborts is a REPORTED finding, not a dead sweep.

use rustc_data_structures::unord::UnordSet;
use rustc_hir::HirId;
use rustc_middle::ty::TyCtxt;

/// One subject's bridge status.
pub(crate) struct BridgeRow {
    pub fn_path: String,
    pub mir_local: u32,
    pub is_param: bool,
    /// `true` when the subject carries an emitting decision — the population
    /// the phase-2 bar is stated over.
    pub decided: bool,
    /// Is the subject's binding `HirId` in the image of the AST→HIR map?
    pub hir_resolved: bool,
    /// Is the subject's owning function in the image of the global map?
    pub fn_resolved: bool,
}

/// **PHASE 2's BAR.** For every subject, can the AST walk reach the node the
/// decision is keyed to?
///
/// Pre-stated bar (user ruling, 2026-08-12): **100 % resolution on decision
/// keys of the DECIDED population.** A miss there is blocking — a decided
/// subject whose node cannot be found is a subject the new layer cannot emit,
/// which is a silent ledger movement. Misses outside the decided population are
/// priced findings: they cost nothing today and price a future capability.
///
/// **Must be called before any HIR/MIR query** — see the module doc.
///
/// Returns `Err` with the panic's message if the mapper aborts, so that a
/// program whose correspondence the mapper rejects is reported rather than
/// crashing the sweep.
#[cfg(test)]
pub(crate) fn census(tcx: TyCtxt<'_>) -> Result<Vec<BridgeRow>, String> {
    // FIRST, before anything touches HIR. `catch_unwind` covers the mapping,
    // not the decision phase: a decision-phase panic is a real defect and must
    // not be swallowed here.
    let mapped = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let mut krate = ::utils::ast::expanded_ast(tcx);
        let map = ::utils::ast::make_ast_to_hir(&mut krate, tcx);
        // `NodeMap` is rustc's `UnordMap`, which hides `values()`/`iter()` on
        // purpose so nondeterministic iteration cannot leak into compiler
        // output. Membership is order-free, so `UnordSet` is the right
        // container and `From<UnordItems>` is the supported construction.
        let hir_image: UnordSet<HirId> = map.local_map.items().map(|(_, v)| *v).into();
        let fn_image: UnordSet<rustc_span::def_id::LocalDefId> =
            map.global_map.items().map(|(_, v)| *v).into();
        (hir_image, fn_image)
    }));
    let (hir_image, fn_image) = match mapped {
        Ok(pair) => pair,
        Err(payload) => {
            let msg = payload
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| payload.downcast_ref::<&str>().map(|s| (*s).to_owned()))
                .unwrap_or_else(|| "<non-string panic payload>".to_owned());
            return Err(msg);
        }
    };

    let (table, _ctx) = super::decide_table_with_ctx(tcx)?;
    Ok(table
        .entries
        .iter()
        .map(|(subject, decision)| BridgeRow {
            fn_path: tcx.def_path_str(subject.fn_did.to_def_id()),
            mir_local: subject.local.as_u32(),
            is_param: matches!(subject.kind, super::decision::SubjectKind::Param { .. }),
            // EXHAUSTIVE, not `matches!` — the import denylist rejects the
            // bypass shape, and it is right to: the bar is stated over the
            // DECIDED population, so a new emitting disposition that this
            // census silently counted as degraded would understate the very
            // number the phase gates on.
            decided: match decision {
                super::decision::Decision::Ref { .. }
                | super::decision::Decision::Slice { .. }
                | super::decision::Decision::Opt { .. } => true,
                super::decision::Decision::Degraded(_) => false,
            },
            hir_resolved: hir_image.contains(&subject.hir_id),
            fn_resolved: fn_image.contains(&subject.fn_did),
        })
        .collect())
}

/// The census as a TSV artifact, for the corpus sweep.
#[cfg(test)]
pub(crate) fn census_tsv(tcx: TyCtxt<'_>) -> String {
    let mut out =
        String::from("fn_path\tmir_local\tis_param\tdecided\thir_resolved\tfn_resolved\n");
    match census(tcx) {
        Ok(rows) => {
            for r in rows {
                out.push_str(&format!(
                    "{}\t{}\t{}\t{}\t{}\t{}\n",
                    r.fn_path,
                    r.mir_local,
                    u8::from(r.is_param),
                    u8::from(r.decided),
                    u8::from(r.hir_resolved),
                    u8::from(r.fn_resolved),
                ));
            }
        }
        // A declined census is REPORTED in the artifact, never an empty file:
        // an empty file and a total mapping failure are different facts, and
        // the bar must not read the second as the first.
        Err(why) => out.push_str(&format!(
            "<declined>\t0\t0\t0\t0\t0\t{}\n",
            why.replace(['\t', '\n', '\r'], " ")
        )),
    }
    out
}
