//! BO rewriter — GREENFIELD module (ruling 2026-07-27, Q2).
//!
//! This module consumes the borrow+ownership (BO) analysis results and emits
//! rewritten Rust. It is a clean-room implementation: the existing
//! [`crate::rewriter`] tree is a FROZEN production baseline and this module
//! **never imports from it**.
//!
//! Design of record:
//! - `docs/agents/plan/2026-07-27-bo-rewriter-scoping.md` (post-mortem + design)
//! - `docs/agents/plan/2026-07-28-m05-export-surface-spec.md` (E-R1..E-R4)
//! - `docs/agents/plan/2026-07-28-m05-decision-matrix.md` (kind mapping)
//!
//! # Isolation rule (Q2)
//!
//! A separate crate would have forced `mod analyses` public, so this is a
//! top-level module instead. That trades compile-time isolation for a
//! discipline that has to be enforced mechanically — see [`import_denylist`].
//!
//! | Target | Policy |
//! |---|---|
//! | `crate::rewriter::*` | **forbidden** — no import, path reference, or copied file |
//! | `crate::analyses::*` | allowed, read-only |
//! | `crate::utils::*`, `::utils::*` | allowed |
//!
//! # Phase separation (M1 architecture directive, binding from the first commit)
//!
//! The module is four phases with one-way data flow and no shared mutable
//! context (E1 state visibility):
//!
//! ```text
//!   analyses + BoExport ──▶ decision ──▶ plan ──▶ apply ──▶ verify
//!                           (reads)     (data)   (blind)   (gates)
//! ```
//!
//! Each phase hands the next a finished value. No phase holds a back-pointer to
//! another, and [`apply`] is *analysis-blind* by enforced rule, not convention —
//! see [`import_denylist`] for the per-phase checks.
//!
//! # Status
//!
//! M1/S0 lands the phase skeleton, the goldens as RED, and the per-phase
//! isolation checks. The decision table, edit plan and applier arrive in S1
//! (G01 walking skeleton) and S2–S3 (breadth).

use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::{
    mir::Local,
    ty::{Mutability, TyCtxt, TyKind},
};

use crate::{
    analyses::borrow_ownership::{
        CrateCtxt, borrow_verify::verify_to_fixpoint, coherence::add_coherence,
        crate_slots::{CrateSlots, ptr_chain_depth},
        emit_crate_ownership_constraints, export::with_bo_export, mutability_facts::MutFacts,
        origins::compute_origins, solver::KindSolver,
    },
    utils::rustc::RustProgram,
};

pub(crate) mod apply;
pub(crate) mod artifact;
pub(crate) mod decision;
pub(crate) mod plan;
pub(crate) mod verify;

#[cfg(test)]
mod emit_tests;
#[cfg(test)]
mod goldens;
#[cfg(test)]
mod import_denylist;

/// What one M1 rewrite attempt produced.
///
/// `Degraded` is a first-class outcome, not an error: §1.6 admits only
/// conflict-non-increasing re-routes, and **everything outside that envelope
/// degrades in the decision phase with a named reason**. Making that a variant
/// rather than a panic or a silent skip is what lets S2 count envelope
/// failures — the registered commitment that decides whether
/// emission-guided refinement is ever built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum RewriteOutcome {
    /// The emitted crate source, **with the degradations that accompanied it**.
    ///
    /// Degradations ride along with a successful emission on purpose: a crate
    /// can emit while most of its subjects were degraded, and an `Emitted` that
    /// did not say so would let a 100%-degraded program count as a success.
    /// `emitted_count` is how a caller tells a real rewrite from a no-op.
    Emitted {
        /// The crate **root's** final text. For a single-file crate this is the
        /// whole emitted crate; for a multi-file crate it is the root only, and
        /// [`Self::Emitted::files`] carries every file the rewrite changed.
        ///
        /// Read back from the materialized copy rather than reconstructed, so it
        /// is correct whether or not the root itself was edited.
        source: String,
        /// Every file the rewrite changed, keyed by file.
        files: std::collections::BTreeMap<plan::FileKey, String>,
        degradations: Vec<decision::Degradation>,
        emitted_count: usize,
        /// Pointer parameters on item kinds M1 does not rewrite. Carried out
        /// here so the exclusions reach a consumer **by construction** — the
        /// previous buckets were written and read by nothing outside one test,
        /// while the ledger claimed they "flow into S2b's counters".
        excluded: decision::universe::Excluded,
        /// Decisions that could not be turned into a placed edit — a
        /// macro-generated span, a span straddling two files, a file with no
        /// editable identity. Carried out for the same reason as `excluded`:
        /// counted and attributed, never silently dropped. Expected zero on the
        /// frozen corpus; a nonzero count is a finding to rule on.
        unplaceable: Vec<plan::Unplaceable>,
    },
    /// No emission, with whatever attribution was available.
    Degraded {
        reason: String,
        degradations: Vec<decision::Degradation>,
        excluded: decision::universe::Excluded,
    },
}

/// M1 entry point: source in, rewritten source out.
///
/// The four phases run in order, each handed the previous one's finished value:
/// `decision` (the only phase that reads analyses) → `plan` (edits as data) →
/// `apply` (analysis-blind splice) → `verify` (gates).
///
/// # Capture scope
///
/// The driver opens [`with_bo_export`] explicitly. The ambient `CRAT_BO_EXPORT`
/// flag is for corpus workers; the driver **is** the consumer, so it arms
/// unconditionally and pays the capture cost by design.
///
/// # S1 scope
///
/// Depth-0 pointer *parameters* decided `Ref`. Everything else degrades in the
/// decision phase with a named reason.
#[allow(
    dead_code,
    reason = "M1's only entry point, and it has no non-test caller until the \
              rewriter is wired into the pipeline. The allow is HERE, on one \
              item, rather than module-wide: seeding this as a live root keeps \
              dead_code active over everything reachable from it, which is what \
              the module-wide blanket switched off — it hid the two dead \
              universe fields the lint exists to catch."
)]
pub(crate) fn rewrite_m1(input: &str) -> RewriteOutcome {
    // **The single-file case of the general path — not a second path.** The
    // input is staged as a one-file crate and handed to `rewrite_m1_path`, so
    // the ten goldens exercise exactly the mechanism the corpus will. A parallel
    // string pipeline is the hazard class this milestone exists to remove: it
    // would be exercised by every test and by nothing real.
    rewrite_core(::utils::compilation::str_to_input(input), None)
}

/// M1's **general** entry point: a crate rooted at `root`, rewritten into a temp
/// copy and gated there.
#[allow(
    dead_code,
    reason = "no caller until 0a.4's corpus smoke; `rewrite_m1` reaches the same               core through the other entry. Targeted here rather than               module-wide so the lint stays live over everything reachable."
)]
pub(crate) fn rewrite_m1_path(root: &std::path::Path) -> RewriteOutcome {
    rewrite_core(::utils::compilation::path_to_input(root), Some(root))
}

/// **The one emission path.** Both entry points funnel here; they differ only in
/// the compiler input and in what the emitted files are materialized *onto*.
///
/// # Why the string entry is not staged to disk first
///
/// Staging it would make every span render against a temp directory — an
/// absolute, machine-specific path containing a pid and a counter. Sites would
/// stop being reproducible between runs, which is the D19 failure again: a
/// report whose values permute between runs is not comparable. Compiling the
/// string as `<main.rs>` keeps attribution stable, and the emission logic below
/// is shared regardless, which is what the one-path ruling is actually about.
fn rewrite_core(
    input: rustc_session::config::Input,
    tree_base: Option<&std::path::Path>,
) -> RewriteOutcome {
    let root_hint = tree_base;
    let result = ::utils::compilation::run_compiler_on_input(input, |tcx| {
        let table = decide_table(tcx)?;
        let emission = emit_files(tcx, &table)?;
        // Structural gate: rollbacks must be zero.
        if !emission.rollbacks.is_empty() {
            return Err(format!(
                "apply rolled back {} edit(s): {:?}",
                emission.rollbacks.len(),
                emission.rollbacks.iter().map(|r| r.reason).collect::<Vec<_>>()
            ));
        }
        let degradations: Vec<decision::Degradation> = table.degradations().cloned().collect();
        // The crate ROOT's final text: its emitted version if the root was
        // edited, otherwise its original source. Computed here because only the
        // compiler session can supply the unedited text.
        let source_map = tcx.sess.source_map();
        let root_text = source_map
            .files()
            .iter()
            .find_map(|sf| {
                let key = file_key(&sf.name)?;
                let is_root = match &key {
                    plan::FileKey::Virtual(_) => true,
                    plan::FileKey::Real(path) => Some(path.as_path()) == root_hint,
                };
                if !is_root {
                    return None;
                }
                emission
                    .files
                    .get(&key)
                    .cloned()
                    .or_else(|| sf.src.as_ref().map(|src| src.to_string()))
            })
            .unwrap_or_default();
        Ok((
            emission.files,
            emission.unplaceable,
            degradations,
            table.emitted_count(),
            decision::universe::classify(tcx).excluded,
            root_text,
        ))
    });

    match result {
        Ok(Ok((files, unplaceable, degradations, emitted_count, excluded, root_text))) => {
            // Materialize onto the original tree when there is one; otherwise
            // the emission is a single virtual file and becomes a one-file crate.
            let materialized = match tree_base {
                Some(root) => verify::materialize(root, &files),
                None => verify::materialize_single_file(&root_text),
            };
            let staged = match materialized {
                Ok(staged) => staged,
                Err(err) => {
                    return RewriteOutcome::Degraded {
                        reason: format!("could not materialize the emitted crate: {err}"),
                        degradations,
                        excluded,
                    };
                }
            };
            // Hard gate: the emitted crate type-checks, WHOLE-CRATE. S2b.1
            // replaces this verdict with per-function granularity, after the
            // S2b.0 measurement chooses its mechanism.
            if verify::type_checks_crate(staged.root()) {
                let source = match tree_base {
                    Some(_) => std::fs::read_to_string(staged.root()).unwrap_or_default(),
                    None => root_text,
                };
                RewriteOutcome::Emitted {
                    source,
                    files,
                    degradations,
                    emitted_count,
                    excluded,
                    unplaceable,
                }
            } else {
                RewriteOutcome::Degraded {
                    reason: "emitted crate failed the type-check gate".to_owned(),
                    degradations,
                    excluded,
                }
            }
        }
        Ok(Err(reason)) => RewriteOutcome::Degraded {
            reason,
            degradations: Vec::new(),
            excluded: decision::universe::Excluded::default(),
        },
        Err(_) => RewriteOutcome::Degraded {
            reason: "input crate did not compile".to_owned(),
            degradations: Vec::new(),
            excluded: decision::universe::Excluded::default(),
        },
    }
}


/// Every top-level fn/struct item, in HIR owner order (the `bo_c1` shape).
fn collect_program(tcx: TyCtxt<'_>) -> RustProgram<'_> {
    let mut functions = Vec::new();
    let mut structs = Vec::new();
    for maybe_owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        match item.kind {
            ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
            ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
            _ => {}
        }
    }
    RustProgram {
        tcx,
        functions,
        structs,
    }
}

/// M1 subjects: each pointer-typed parameter of each local function, decided on
/// the **resolved** type.
///
/// # Why resolved, not syntactic (R-A)
///
/// The previous collector matched `rustc_hir::TyKind::Ptr` on the syntactic HIR
/// type node. A C2Rust type alias — `pub type lil_value_t = *mut _lil_value_t`
/// — lowers to `TyKind::Path`, so a parameter declared `val: lil_value_t` was
/// not a subject at all: BO decided it (MIR types are resolved) and the
/// rewriter discarded that decision with no `Decision`, no `Degradation`, no
/// site and no reason. That is the "unrewritten and unattributed" class the
/// whole A1 layer exists to retire, and it is present in the evaluation corpus.
///
/// The predicate is now [`ptr_chain_depth`] over `tcx.fn_sig`'s inputs — the
/// same in-tree function `CrateSlots` builds the slot universe from. **HIR
/// supplies where, tcx supplies whether:** the plan edits source bytes, so the
/// declaration span and the pointee span still come from HIR.
///
/// R-A rules these subjects **collected, not excluded** — they are real C
/// pointer parameters. Whether each *emits* is A1's per-subject decision like
/// any other, and the alias-specific emission obstacle (the alias already
/// contains the `*mut`, so there is no pointee text to copy) degrades with its
/// own attributed reason in [`decision::decide_one`].
///
/// The MIR local of parameter `i` is `_{i+1}` — params occupy `_1 ..= arg_count`
/// — which is what lets a HIR-side span pair with a MIR-side slot lookup. That
/// mapping is what [`decision::coverage`]'s fail-loud arm guards.
fn collect_subjects(
    tcx: TyCtxt<'_>,
    program: &RustProgram<'_>,
    mut_facts: &MutFacts,
) -> Vec<decision::Subject> {
    let mut subjects = Vec::new();
    for &fn_did in &program.functions {
        let node = tcx.hir_node_by_def_id(fn_did);
        let (Some(decl), Some(body_id)) = (node.fn_decl(), node.body_id()) else {
            continue;
        };
        let body = tcx.hir_body(body_id);
        let fn_name = tcx.item_name(fn_did.to_def_id());
        let sig = tcx.fn_sig(fn_did).skip_binder().skip_binder();
        for (index, param_ty) in sig.inputs().iter().enumerate() {
            if ptr_chain_depth(*param_ty) == 0 {
                continue;
            }
            // F3: these used to `continue`, dropping the subject from BOTH the
            // table and the count it was checked against — a double-sided drop
            // no self-comparison could see. A mismatch here is a collector bug
            // rather than a degradation, so it fails loudly instead of
            // shrinking the work silently.
            let Some(input) = decl.inputs.get(index) else {
                panic!(
                    "resolved signature of {fn_did:?} has input {index} but the HIR \
                     declaration has only {} — parameter mapping broken",
                    decl.inputs.len()
                );
            };
            // The parameter's BINDING, so a use can be attributed to it without
            // relying on a name that might be shadowed in an inner scope.
            let Some(param) = body.params.get(index) else {
                panic!(
                    "HIR fn_decl has input {index} but the body has no matching \
                     param binding for {fn_did:?} — collector invariant broken"
                );
            };
            let (decl_shape, pointee_span) = match input.kind {
                rustc_hir::TyKind::Ptr(mut_ty) => {
                    (decision::DeclShape::RawPtr, Some(mut_ty.ty.span))
                }
                rustc_hir::TyKind::Ref(_, mut_ty) => {
                    (decision::DeclShape::Reference, Some(mut_ty.ty.span))
                }
                rustc_hir::TyKind::Path(_) => (decision::DeclShape::Alias, None),
                _ => (decision::DeclShape::Other, None),
            };
            let local = Local::from_usize(index + 1);
            let name = param_name(param);
            subjects.push(decision::Subject {
                fn_did,
                local,
                hir_id: param.pat.hir_id,
                param_name: name.clone(),
                hir_index: index,
                ptr_depth: ptr_chain_depth(*param_ty),
                label: format!("{fn_name}::{}", name.as_deref().unwrap_or("<pattern>")),
                ty_span: input.span,
                pointee_span,
                decl_shape,
                // The declared mutability is a ceiling, not the decision: BO's
                // mutability facts decide whether a `&mut` is warranted. Read
                // off the RESOLVED type so it sees through an alias exactly as
                // the pointer predicate above does.
                mutable: matches!(
                    param_ty.kind(),
                    TyKind::RawPtr(_, Mutability::Mut) | TyKind::Ref(_, _, Mutability::Mut)
                ) && mut_facts.is_mutable(fn_did, local),
            });
        }
    }
    subjects
}

/// **Census of the collector's own predicate** (§3, census discipline).
///
/// The ledger's `4171/0/0/2039` census came from an uncommitted scratchpad
/// `syn` walk applying the same syntactic `*mut`/`*const` test as the
/// classifier — so it inherited the alias blind spot and *could not have
/// detected it*. A number enters the ledger only via a committed, in-tree code
/// path; this is that path, and it runs the shipping collector.
///
/// `resolved - syntactic_ptr` is the population the retired predicate could not
/// see, broken down by declaration shape so the alias class is a datum rather
/// than a residual.
// `cfg(test)` rather than `allow(dead_code)`: the only consumer is `bo_c1`'s
// corpus harness, which is itself `cfg(test)`. Saying so is more honest than
// silencing the lint, and it keeps the lint working here.
#[cfg(test)]
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct CollectorCensus {
    /// Subjects the shipping (resolved-type) collector produces.
    pub resolved: usize,
    /// What the retired syntactic `TyKind::Ptr` predicate would have produced.
    pub syntactic_ptr: usize,
    /// Resolved-only, declared through a path — **the C2Rust alias class**.
    pub resolved_only_alias: usize,
    /// Resolved-only, already a reference in source.
    pub resolved_only_reference: usize,
    /// Resolved-only, some other declaration form.
    pub resolved_only_other: usize,
}

/// Run the shipping collector over `tcx` and count what it sees.
#[cfg(test)]
pub(crate) fn census(tcx: TyCtxt<'_>) -> CollectorCensus {
    let program = collect_program(tcx);
    let mut_facts = MutFacts::from_program(&program);
    let mut census = CollectorCensus::default();
    for subject in collect_subjects(tcx, &program, &mut_facts) {
        census.resolved += 1;
        match subject.decl_shape {
            decision::DeclShape::RawPtr => census.syntactic_ptr += 1,
            decision::DeclShape::Alias => census.resolved_only_alias += 1,
            decision::DeclShape::Reference => census.resolved_only_reference += 1,
            decision::DeclShape::Other => census.resolved_only_other += 1,
        }
    }
    census
}

/// Source name of a parameter binding.
///
/// `None` rather than a `"<pattern>"` placeholder: this feeds the artifact's
/// `param_name` pairing term, and a placeholder would compare *equal* between
/// two different pattern parameters — a pairing term that silently agrees is
/// the F1 failure mode in miniature. The placeholder is applied only where it
/// belongs, in the human-readable `label`.
fn param_name(param: &rustc_hir::Param<'_>) -> Option<String> {
    match param.pat.kind {
        rustc_hir::PatKind::Binding(_, _, ident, _) => Some(ident.name.to_string()),
        _ => None,
    }
}

/// The analysis front-end: everything from BO's model to a finished decision
/// table, with the structural self-check and the coverage gate applied.
///
/// Extracted so producer A's artifact is reachable without a second copy of the
/// pipeline — and, deliberately, **without moving any comparison into this
/// module**. `bo_rewriter` emits; `coverage_recon` compares.
fn decide_table<'tcx>(tcx: TyCtxt<'tcx>) -> Result<decision::DecisionTable, String> {
    decide_table_perturbed(tcx, |_| {})
}

/// The rewritten source of every file the plan touched, plus what could not be
/// placed. **This is the general emission path**; the string entry point is its
/// single-file case.
pub(crate) struct Emission {
    pub files: std::collections::BTreeMap<plan::FileKey, String>,
    pub rollbacks: Vec<apply::Rollback>,
    pub unplaceable: Vec<plan::Unplaceable>,
}

/// A source file's identity for editing. `None` for anything not written back
/// to a nameable file (macro-expansion contexts, synthetic inputs).
fn file_key(name: &rustc_span::FileName) -> Option<plan::FileKey> {
    match name {
        rustc_span::FileName::Real(real) => real
            .local_path()
            .map(|path| plan::FileKey::Real(path.to_path_buf())),
        rustc_span::FileName::Custom(name) => Some(plan::FileKey::Virtual(name.clone())),
        _ => None,
    }
}

/// Plan and apply, **grouped by file**.
///
/// Grouping is what makes the offsets meaningful: `lookup_byte_offset` yields
/// *file-relative* positions, so two edits in different files can carry
/// identical `(lo, hi)`. Applying them against one string would splice each into
/// whichever file happened to be passed — silently, and with a plausible result.
pub(crate) fn emit_files<'tcx>(
    tcx: TyCtxt<'tcx>,
    table: &decision::DecisionTable,
) -> Result<Emission, String> {
    let source_map = tcx.sess.source_map();
    let text_of = |key: &plan::FileKey| -> Option<String> {
        source_map
            .files()
            .iter()
            .find(|sf| file_key(&sf.name).as_ref() == Some(key))
            .and_then(|sf| sf.src.as_ref().map(|src| src.to_string()))
    };
    let span_to_loc =
        |span: rustc_span::Span| -> Result<(plan::FileKey, usize, usize), &'static str> {
            // A macro-generated span points into an expansion, not into source
            // anyone can edit. Splicing it would corrupt the file it nominally
            // resolves to.
            if span.from_expansion() {
                return Err("span is macro-generated and cannot be spliced into source");
            }
            let lo = source_map.lookup_byte_offset(span.lo());
            let hi = source_map.lookup_byte_offset(span.hi());
            let (Some(lo_key), Some(hi_key)) = (file_key(&lo.sf.name), file_key(&hi.sf.name))
            else {
                return Err("span resolves to a file with no editable identity");
            };
            if lo_key != hi_key {
                return Err("span straddles two source files");
            }
            let (lo, hi) = (lo.pos.0 as usize, hi.pos.0 as usize);
            if lo > hi {
                return Err("span bounds are inverted");
            }
            Ok((lo_key, lo, hi))
        };

    let planned = plan::plan(table, text_of, span_to_loc);

    let mut files = std::collections::BTreeMap::new();
    let mut rollbacks = Vec::new();
    for (key, edits) in &planned.by_file {
        let Some(source) = text_of(key) else {
            return Err(format!("no source text for planned file {key:?}"));
        };
        let applied = apply::apply(&source, edits);
        rollbacks.extend(applied.rollbacks);
        files.insert(key.clone(), applied.source);
    }
    Ok(Emission {
        files,
        rollbacks,
        unplaceable: planned.unplaceable,
    })
}

/// [`decide_table`] with a hook applied to the collector's real output at the
/// PHASE BOUNDARY, before `decide` runs.
///
/// The hook is a no-op in production (`decide_table` passes `|_| {}`) and exists
/// so a test can inject the exact defect this axis guards — a mis-associated
/// span on the collector's own `Subject` type — and then drive it through the
/// real `decide → artifact → encode → decode → compare` path.
///
/// **This is deliberately not a production fault seam.** A `CRAT_*`-gated seam
/// inside decision-phase code was considered and DENIED; a collector fault
/// manifests as exactly the mis-associated output a boundary hook injects, so
/// the verification power is the same at zero production-code cost. That is the
/// phase-separated architecture paying for itself.
fn decide_table_perturbed<'tcx>(
    tcx: TyCtxt<'tcx>,
    perturb: impl FnOnce(&mut Vec<decision::Subject>),
) -> Result<decision::DecisionTable, String> {
    let program = collect_program(tcx);
    let slots = CrateSlots::build(&program);
    let mut_facts = MutFacts::from_program(&program);

    // Phase 1 input: the BO run, under an explicit capture scope.
    let (model, _export) = with_bo_export(|| {
        let crate_ctxt = CrateCtxt::new(&program);
        let solver = KindSolver::new(&slots);
        let Ok((_stats, selectors)) = emit_crate_ownership_constraints(
            &crate_ctxt,
            &slots,
            &compute_origins(&program),
            &solver,
        ) else {
            return None;
        };
        for &g in &program.functions {
            let body = tcx.mir_drops_elaborated_and_const_checked(g).borrow();
            add_coherence(&solver, &slots, g, &body);
        }
        verify_to_fixpoint(&program, &slots, &solver, &selectors, &mut_facts)
    });
    let Some(model) = model else {
        return Err("BO declined — no accepted model".to_owned());
    };

    let mut subjects = collect_subjects(tcx, &program, &mut_facts);
    perturb(&mut subjects);
    let facts = decision::emitability::collect(tcx, &program.functions);
    let table = decision::decide(tcx, &subjects, &model, &slots, &facts);

    // Structural self-check: the table matches the subjects it was handed. NOT
    // the coverage gate — every comparison in it is against the collector's own
    // output.
    if let Err(why) = table.is_self_consistent_over(&subjects) {
        return Err(format!("decision table self-consistency: {why}"));
    }

    // C.2: the in-process coverage gate is GONE. Its replacement is the
    // harness reconciliation in `coverage_recon`, driven from outside this
    // module — see `recon_fixtures` (C.1) and the corpus mode (C.4).
    //
    // Deleted rather than demoted to a smoke check: a weakened gate that still
    // READS like a coverage gate is the hazard itself. Four rounds of this
    // milestone were spent on apparatus that claimed more than it checked, and
    // leaving a demoted version behind preserves the claim while removing the
    // substance.
    Ok(table)
}

/// **Producer A's artifact** for the crate in `tcx`.
///
/// The reconciliation's caller lives outside this module; this only emits.
#[allow(
    dead_code,
    reason = "producer A's artifact has no non-test consumer until the rewriter \
              is wired into the pipeline — the same standing as `rewrite_m1`. \
              Its test consumers are the C.1 reconciliation and C.4's corpus \
              mode. Targeted so dead_code stays live over everything reachable."
)]
pub(crate) fn artifact_rows(
    tcx: TyCtxt<'_>,
) -> Result<Vec<crate::coverage_recon::schema::Row>, String> {
    decide_table(tcx).map(|table| artifact::rows(tcx, &table))
}

/// The golden inputs, for the out-of-module reconciliation harness (C.1).
///
/// Exposed as `(name, source)` pairs rather than by making `goldens` public:
/// the harness needs the INPUTS, not the golden machinery, and a narrower
/// surface is a narrower coupling.
#[cfg(test)]
pub(crate) fn goldens_for_reconciliation() -> Vec<(&'static str, &'static str)> {
    goldens::GOLDENS.iter().map(|g| (g.name, g.input)).collect()
}

/// The item-axis census, for the corpus harness (C.6's owed exclusion numbers).
#[cfg(test)]
pub(crate) fn classify_universe(tcx: TyCtxt<'_>) -> decision::universe::UniverseReport {
    decision::universe::classify(tcx)
}

/// Producer A's artifact with the span association SWAPPED between the first two
/// subjects of the crate — injected at the phase boundary, on the collector's
/// real `Subject` type, then driven through the real pipeline.
#[cfg(test)]
pub(crate) fn artifact_rows_span_swapped(
    tcx: TyCtxt<'_>,
) -> Result<Vec<crate::coverage_recon::schema::Row>, String> {
    decide_table_perturbed(tcx, |subjects| {
        if subjects.len() >= 2 {
            let (lo, hi) = (subjects[0].ty_span, subjects[1].ty_span);
            subjects[0].ty_span = hi;
            subjects[1].ty_span = lo;
        }
    })
    .map(|table| artifact::rows(tcx, &table))
}
