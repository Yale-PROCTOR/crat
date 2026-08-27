//! ESC-GAP fix-candidate ② pricing census — READ-ONLY measurement.
//!
//! Sizes the population candidate ② ("escaped-loans-live-to-exit") would have to act on:
//! pointer-typed MIR **copies** whose source is `Ref`-modeled, still live after the copy, and
//! whose destination is caller-visible storage. It adds no analysis query, changes no analysis
//! behaviour, and nothing in the production rewriter reads its output. Every classification below
//! is either a direct MIR read or a lookup in an artifact the run already produces (the accepted
//! model, the `MutFacts` map).
//!
//! # The three definitions this census is required to record
//!
//! ## 1. Liveness seek (N2)
//!
//! The landed point-indexed liveness facts are
//! `borrow::provenance_liveness::compute_provenance_liveness`, which samples
//! [`MaybeLiveLocals`] with `seek_before_primary_effect` (`provenance_liveness.rs:41`).
//! `MaybeLiveLocals` is a **backward** analysis, so "before the primary effect" in dataflow order
//! is the state **on exit** of that location in program order. That is exactly N2's
//! "live AFTER the copy", and it is the seek this census uses as its primary. This is the same
//! off-by-one the HLZ port had to repair in the traversal (see
//! `docs/agents/tasks/2026-08-25-hlz-port-exploration.md` §4): there, gating on exit-liveness while
//! walking to successor points lost one point per loan. Because the choice is load-bearing and
//! easy to get backwards, the census records BOTH seeks per site — `live_after`
//! (`seek_before_primary_effect`, the primary) and `live_entry` (`seek_after_primary_effect`,
//! hlz's repaired sampling) — so the sensitivity is measured rather than asserted.
//!
//! This census reads **local** liveness rather than the provenance projection of it. The
//! projection is the image of exactly these bits under `provenance_set.local_data`
//! (`provenance_liveness.rs:43-53`); N2 is stated over the source *local*, so taking the bits at
//! their source is the same fact without a lossy re-keying.
//!
//! ## 2. Which local N2 is read on — the operand-temporary correction
//!
//! **Measured, not assumed: reading N2 on the *syntactic* source local makes the ESC-W1 witness
//! itself fall out of the population.** MIR builds `*out = x` as
//!
//! ```text
//! _3 = copy _2        // _2 is the parameter `x`
//! (*_1) = move _3
//! ```
//!
//! so the escaping store's syntactic source is `_3`, a temporary that is dead immediately after
//! the move — `live_after(_3) = false` — even though the pointer value in `x` remains usable and
//! is written through on the next line. A census keyed on `_3` reports the ESC-W1 shape as
//! non-live and therefore not in N2/N4, which is the opposite of the fact ② cares about.
//!
//! The census therefore resolves a bare-local source through
//! [`eliminable_temporaries`] — `output_params`' existing notion of a MIR local that is
//! "defined once and used once … trivially eliminable, and thus should not affect analysis
//! results" — to the place its unique defining copy read from, and reads liveness and mutability
//! **there**. No new analysis: the resolver walks that module's own bitset and the body's
//! assignments. Both readings are reported per site (`live_after` on the resolved origin,
//! `live_after_syn` on the syntactic local) so the size of the correction is visible, and
//! `resolved` marks the sites where they can differ.
//!
//! ## 3. Escape (N4)
//!
//! A copy is *escaping* iff its destination place is caller-visible storage in the sense of
//! `origin_summary::SignaturePlace`, i.e. under exactly the root/deref partition
//! `origin_flow::to_summary` uses to decide which internal origin slots become signature slots
//! (`origin_flow.rs:956-999`, `:1055-1090`):
//!
//! - base local is `RETURN_PLACE` → `return` (return-reachable), any projection; or
//! - base local is a parameter (`1..=body.arg_count`) **and** the projection contains at least one
//!   `Deref` → `deref-param` (deref-of-parameter at any depth).
//!
//! A parameter base with **no** `Deref` is deliberately excluded: MIR parameters are callee-local
//! copies of the argument values, and writing one is not visible to the caller. This is the same
//! exclusion `to_summary` encodes by reaching caller storage only through the return root or a
//! deref/field place rooted at an argument.
//!
//! **Recorded limitation, not silently absorbed.** A *transitive* escape ("the destination is a
//! temp that later flows to the return place") is NOT reported. `OriginSummary`'s slot universe
//! contains signature-rooted places only, so no existing origin/summary machinery can answer it
//! for an arbitrary temp; deriving it would mean inventing an analysis, which this census is
//! forbidden to do. N4 is therefore a LOWER bound on "escaping" under any transitive reading.

use std::{collections::BTreeMap, fs, path::Path};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::{
    mir::{Body, Local, Location, Operand, Place, PlaceElem, RETURN_PLACE, Rvalue, StatementKind},
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_mir_dataflow::Analysis;
use rustc_span::def_id::LocalDefId;

use crate::{
    analyses::{
        borrow_ownership::{
            SlotKind,
            crate_slots::CrateSlots,
            mutability_facts::MutFacts,
            slot_key::{field_key, local_key},
            slots::StructFieldSlot,
            solver::SlotRef,
        },
        liveness::MaybeLiveLocals,
        output_params::eliminable_temporaries::eliminable_temporaries,
    },
    utils::rustc::RustProgram,
};

/// Bound on the operand-temporary chase. MIR operand temps nest shallowly; the bound exists so a
/// malformed chain cannot loop, not because deep chains are expected.
const ORIGIN_CHASE_LIMIT: usize = 8;

// ---------------------------------------------------------------------------
// Rows
// ---------------------------------------------------------------------------

/// One site in the population: a pointer-typed MIR copy assignment.
#[derive(Clone, Debug)]
pub(crate) struct CopyRow {
    pub fn_key: String,
    pub block: usize,
    pub stmt: usize,
    /// `use-copy` | `use-move` | `cast-copy` | `cast-move` | `copy-for-deref`.
    pub form: &'static str,
    pub src: String,
    pub dst: String,
    /// Canonical BO slot key of the source place, or `None` when the place shape is outside the
    /// slot universe (indexing, downcast, a non-local struct base). Counted, never dropped.
    pub src_slot_key: Option<String>,
    pub src_kind: Option<SlotKind>,
    /// N1: the source slot is `Ref` in the accepted model.
    pub n1: bool,
    /// The source after the operand-temporary chase (§2 of the module docs); equals `src` when
    /// nothing was resolved.
    pub origin: String,
    pub origin_slot_key: Option<String>,
    pub origin_kind: Option<SlotKind>,
    /// The chase actually moved (`origin != src`).
    pub resolved: bool,
    /// N2 primary: the ORIGIN local is live on EXIT of the copy (`seek_before_primary_effect`).
    pub live_after: bool,
    /// The other seek, for sensitivity: origin local live on ENTRY (`seek_after_primary_effect`).
    pub live_entry: bool,
    /// N2 read on the SYNTACTIC source local — the uncorrected reading, kept so the size of the
    /// operand-temporary correction is a measured column rather than a claim.
    pub live_after_syn: bool,
    /// `MutFacts::is_mutable` for the origin local (the same readout `bo_c1` uses for the
    /// `n_ref_mut_d0` / `n_ref_shared_d0` split).
    pub src_mut: bool,
    /// The origin local had no fact and fell back to the `Mut` default (the sole unsound data
    /// direction; counted, per the `mut_default_fires` precedent).
    pub src_mut_defaulted: bool,
    /// N4 class: `return` | `deref-param` | `-`.
    pub escape: &'static str,
    /// The rvalue's own type is a pointer (the gate `borrow/mod.rs::borrow_set` applies).
    pub rv_ptr: bool,
    /// The destination is itself an eliminable temporary — i.e. this row is the *feeder* half of a
    /// source-level copy whose other half appears as its own row. Reported so N0 can be netted.
    pub dst_is_elim_temp: bool,
}

impl CopyRow {
    fn escaping(&self) -> bool {
        self.escape != "-"
    }
}

/// Per-function context columns.
#[derive(Clone, Debug)]
pub(crate) struct FnRow {
    pub fn_key: String,
    pub arg_count: usize,
    pub n0: usize,
    /// Structural proxy for "issued loans": assignments `BorrowSet::borrow_set`
    /// (`borrow/mod.rs:424-535`) turns into a loan, evaluated on the two gates that do not need a
    /// `ProvenanceSet` — the rvalue form (`Ref`/`RawPtr`/`CopyForDeref`/`Use(Copy|Move)`/
    /// `Cast(Copy|Move)`) and `rvalue.ty(..).is_any_ptr()` — with the third gate
    /// (`owner_for_place(lhs)`) approximated by "lhs resolves to a BO slot".
    ///
    /// It does NOT model the sibling-loan expansion over `tree_borrow_local.group(..)` (which only
    /// ever ADDS loans) nor the `is_borrowing_method` terminator loans, so it is a LOWER bound on
    /// the real per-function loan count. The authoritative count for the context column comes from
    /// the E-R4 export join, not from here; this is the standalone cross-check.
    pub loan_sites_structural: usize,
}

// ---------------------------------------------------------------------------
// Place → slot
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug)]
enum SlotPath {
    Local(Local, u8),
    Field(StructFieldSlot, u8),
}

fn pointee_ty<'tcx>(ty: Ty<'tcx>) -> Option<Ty<'tcx>> {
    match ty.kind() {
        TyKind::RawPtr(inner, _) => Some(*inner),
        TyKind::Ref(_, inner, _) => Some(*inner),
        _ => None,
    }
}

/// Resolve a MIR place onto the BO slot universe's own addressing scheme: a local plus a deref
/// depth, or a global struct-field slot plus a deref depth. This mirrors how `CrateSlots::build`
/// populates the universe (`crate_slots.rs:24-70`) — locals carry deref chains, struct fields are
/// registered globally — and resolves nothing else. Index/subslice/downcast/subtype projections and
/// fields of non-local structs return `None`, which the census counts as `src_slot_unresolved`.
fn resolve_place_slot<'tcx>(
    body: &Body<'tcx>,
    local_structs: &FxHashSet<LocalDefId>,
    place: Place<'tcx>,
) -> Option<SlotPath> {
    let mut cur = SlotPath::Local(place.local, 0);
    let mut ty = body.local_decls[place.local].ty;
    for elem in place.projection.iter() {
        match elem {
            PlaceElem::Deref => {
                ty = pointee_ty(ty)?;
                match &mut cur {
                    SlotPath::Local(_, depth) | SlotPath::Field(_, depth) => {
                        *depth = depth.checked_add(1)?;
                    }
                }
            }
            PlaceElem::Field(index, field_ty) => {
                let TyKind::Adt(adt_def, _) = ty.kind() else {
                    return None;
                };
                let struct_did = adt_def.did().as_local()?;
                if !local_structs.contains(&struct_did) {
                    return None;
                }
                cur = SlotPath::Field(
                    StructFieldSlot {
                        struct_did,
                        field_index: index.as_usize(),
                    },
                    0,
                );
                ty = field_ty;
            }
            _ => return None,
        }
    }
    Some(cur)
}

fn slot_ref_of(slots: &CrateSlots, f: LocalDefId, path: SlotPath) -> Option<SlotRef> {
    match path {
        SlotPath::Local(local, depth) => slots
            .fn_local_slots
            .get(&f)?
            .slot_for_local_depth(local, depth)
            .map(|id| SlotRef::Local(f, id)),
        SlotPath::Field(field, depth) => slots
            .field_slots
            .slot_for_field_depth(field, depth)
            .map(SlotRef::Field),
    }
}

fn slot_key_of(tcx: TyCtxt<'_>, f: LocalDefId, path: SlotPath) -> String {
    match path {
        SlotPath::Local(local, depth) => local_key(tcx, f, local.index(), depth),
        SlotPath::Field(field, depth) => field_key(tcx, field.struct_did, field.field_index, depth),
    }
}

// ---------------------------------------------------------------------------
// Classification
// ---------------------------------------------------------------------------

/// The population's rvalue forms, exactly as the task states them.
fn copy_form<'tcx>(rvalue: &Rvalue<'tcx>) -> Option<(&'static str, Place<'tcx>)> {
    match rvalue {
        Rvalue::Use(Operand::Copy(place)) => Some(("use-copy", *place)),
        Rvalue::Use(Operand::Move(place)) => Some(("use-move", *place)),
        Rvalue::Cast(_, Operand::Copy(place), _) => Some(("cast-copy", *place)),
        Rvalue::Cast(_, Operand::Move(place), _) => Some(("cast-move", *place)),
        Rvalue::CopyForDeref(place) => Some(("copy-for-deref", *place)),
        _ => None,
    }
}

/// N4's operational definition. See the module docs.
fn escape_class(body: &Body<'_>, dst: Place<'_>) -> &'static str {
    if dst.local == RETURN_PLACE {
        return "return";
    }
    let is_param = dst.local.index() >= 1 && dst.local.index() <= body.arg_count;
    let has_deref = dst
        .projection
        .iter()
        .any(|elem| matches!(elem, PlaceElem::Deref));
    if is_param && has_deref {
        "deref-param"
    } else {
        "-"
    }
}

fn is_loan_issuing_rvalue(rvalue: &Rvalue<'_>) -> bool {
    matches!(rvalue, Rvalue::Ref(..) | Rvalue::RawPtr(..)) || copy_form(rvalue).is_some()
}

/// The operand-temporary chase (§2 of the module docs): while the place is a bare local that
/// `eliminable_temporaries` marks and whose unique definition is a pointer copy, step to what that
/// copy read from.
fn chase_origin<'tcx>(
    mut place: Place<'tcx>,
    temp_defs: &FxHashMap<Local, Place<'tcx>>,
) -> Place<'tcx> {
    for _ in 0..ORIGIN_CHASE_LIMIT {
        if !place.projection.is_empty() {
            break;
        }
        let Some(&next) = temp_defs.get(&place.local) else {
            break;
        };
        if next == place {
            break;
        }
        place = next;
    }
    place
}

// ---------------------------------------------------------------------------
// The census
// ---------------------------------------------------------------------------

/// Walk one program and classify every pointer-typed copy. Read-only: no analysis is re-run and no
/// solver is invoked — the accepted `model` is consumed as given.
pub(crate) fn census<'tcx>(
    tcx: TyCtxt<'tcx>,
    program: &RustProgram<'tcx>,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
    mut_facts: &MutFacts,
) -> (Vec<CopyRow>, Vec<FnRow>) {
    let local_structs: FxHashSet<LocalDefId> = program.structs.iter().copied().collect();
    let mut rows = Vec::new();
    let mut fn_rows = Vec::new();

    for f in program.functions.iter().copied() {
        let body = tcx.mir_drops_elaborated_and_const_checked(f).borrow();
        let fn_key = tcx.def_path_str(f.to_def_id());
        let elim = eliminable_temporaries(&body);

        // The unique defining copy of each eliminable temporary, for the origin chase.
        let mut temp_defs: FxHashMap<Local, Place<'tcx>> = FxHashMap::default();
        for block_data in body.basic_blocks.iter() {
            for statement in &block_data.statements {
                let StatementKind::Assign(assign) = &statement.kind else {
                    continue;
                };
                let Some(dst_local) = assign.0.as_local() else {
                    continue;
                };
                if !elim.contains(dst_local) {
                    continue;
                }
                let Some((_, src)) = copy_form(&assign.1) else {
                    continue;
                };
                if src.ty(&body.local_decls, tcx).ty.is_any_ptr() {
                    temp_defs.insert(dst_local, src);
                }
            }
        }

        // Pass 1 — the sites, plus the structural loan-site count.
        let mut sites: Vec<(Location, CopyRow, Local, Local)> = Vec::new();
        let mut loan_sites_structural = 0usize;
        for (block, block_data) in body.basic_blocks.iter_enumerated() {
            for (stmt, statement) in block_data.statements.iter().enumerate() {
                let StatementKind::Assign(assign) = &statement.kind else {
                    continue;
                };
                let (dst, rvalue) = (assign.0, &assign.1);
                let rv_ptr = rvalue.ty(&body.local_decls, tcx).is_any_ptr();

                if rv_ptr
                    && is_loan_issuing_rvalue(rvalue)
                    && resolve_place_slot(&body, &local_structs, dst)
                        .and_then(|path| slot_ref_of(slots, f, path))
                        .is_some()
                {
                    loan_sites_structural += 1;
                }

                let Some((form, src)) = copy_form(rvalue) else {
                    continue;
                };
                // N0's gate: the SOURCE place is pointer-typed. (`rv_ptr` — the gate
                // `borrow_set` itself applies, which for a cast is the TARGET type — is carried as
                // its own column rather than folded in, so the two readings stay separable.)
                if !src.ty(&body.local_decls, tcx).ty.is_any_ptr() {
                    continue;
                }

                let src_path = resolve_place_slot(&body, &local_structs, src);
                let src_slot = src_path.and_then(|path| slot_ref_of(slots, f, path));
                let src_kind = src_slot.and_then(|slot| model.get(&slot).copied());

                let origin = chase_origin(src, &temp_defs);
                let origin_path = resolve_place_slot(&body, &local_structs, origin);
                let origin_slot = origin_path.and_then(|path| slot_ref_of(slots, f, path));
                let origin_kind = origin_slot.and_then(|slot| model.get(&slot).copied());

                let location = Location {
                    block,
                    statement_index: stmt,
                };
                sites.push((
                    location,
                    CopyRow {
                        fn_key: fn_key.clone(),
                        block: block.index(),
                        stmt,
                        form,
                        src: format!("{src:?}"),
                        dst: format!("{dst:?}"),
                        src_slot_key: src_path.map(|path| slot_key_of(tcx, f, path)),
                        src_kind,
                        n1: src_kind == Some(SlotKind::Ref),
                        origin: format!("{origin:?}"),
                        origin_slot_key: origin_path.map(|path| slot_key_of(tcx, f, path)),
                        origin_kind,
                        resolved: origin != src,
                        live_after: false,
                        live_entry: false,
                        live_after_syn: false,
                        src_mut: mut_facts.is_mutable(f, origin.local),
                        src_mut_defaulted: mut_facts.is_defaulted(f, origin.local),
                        escape: escape_class(&body, dst),
                        rv_ptr,
                        dst_is_elim_temp: dst.as_local().is_some_and(|l| elim.contains(l)),
                    },
                    origin.local,
                    src.local,
                ));
            }
        }

        fn_rows.push(FnRow {
            fn_key: fn_key.clone(),
            arg_count: body.arg_count,
            n0: sites.len(),
            loan_sites_structural,
        });

        if sites.is_empty() {
            continue;
        }

        // Pass 2 — liveness, sampled at BOTH seeks. Blocks are walked with `seek_to_block_end`
        // then positions in REVERSE, which is the direction a backward analysis's cursor advances
        // cheaply; this is the same loop shape `compute_provenance_liveness` uses.
        let mut by_block: FxHashMap<usize, Vec<usize>> = FxHashMap::default();
        for (index, (location, _, _, _)) in sites.iter().enumerate() {
            by_block
                .entry(location.block.index())
                .or_default()
                .push(index);
        }

        let mut exit_cursor = MaybeLiveLocals
            .iterate_to_fixpoint(tcx, &body, None)
            .into_results_cursor(&body);
        let mut entry_cursor = MaybeLiveLocals
            .iterate_to_fixpoint(tcx, &body, None)
            .into_results_cursor(&body);

        for (block, block_data) in body.basic_blocks.iter_enumerated() {
            let Some(indices) = by_block.get(&block.index()) else {
                continue;
            };
            let wanted: FxHashMap<usize, usize> = indices
                .iter()
                .map(|&index| (sites[index].0.statement_index, index))
                .collect();
            exit_cursor.seek_to_block_end(block);
            entry_cursor.seek_to_block_end(block);
            let len = block_data.statements.len() + block_data.terminator.is_some() as usize;
            for position in (0..len).rev() {
                let Some(&index) = wanted.get(&position) else {
                    continue;
                };
                let location = Location {
                    block,
                    statement_index: position,
                };
                let (origin_local, syntactic_local) = (sites[index].2, sites[index].3);
                exit_cursor.seek_before_primary_effect(location);
                let exit = exit_cursor.get();
                let (live_after, live_after_syn) =
                    (exit.contains(origin_local), exit.contains(syntactic_local));
                entry_cursor.seek_after_primary_effect(location);
                let live_entry = entry_cursor.get().contains(origin_local);
                sites[index].1.live_after = live_after;
                sites[index].1.live_after_syn = live_after_syn;
                sites[index].1.live_entry = live_entry;
            }
        }

        rows.extend(sites.into_iter().map(|(_, row, _, _)| row));
    }

    (rows, fn_rows)
}

// ---------------------------------------------------------------------------
// Reporting
// ---------------------------------------------------------------------------

fn kind_label(kind: Option<SlotKind>) -> &'static str {
    match kind {
        Some(SlotKind::Ref) => "ref",
        Some(SlotKind::Raw) => "raw",
        Some(SlotKind::Owning) => "own",
        None => "-",
    }
}

fn tsv_cell(value: &str) -> String {
    value.replace(['\t', '\n', '\r'], " ")
}

pub(crate) fn rows_tsv(rows: &[CopyRow]) -> String {
    let mut out = String::from(
        "fn\tblock\tstmt\tform\tsrc\tdst\tsrc_slot\tsrc_kind\tn1\torigin\torigin_slot\t\
         origin_kind\tresolved\tlive_after\tlive_entry\tlive_after_syn\tsrc_mut\t\
         src_mut_defaulted\tescape\trv_ptr\tdst_is_elim_temp\n",
    );
    for row in rows {
        out.push_str(&format!(
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            tsv_cell(&row.fn_key),
            row.block,
            row.stmt,
            row.form,
            tsv_cell(&row.src),
            tsv_cell(&row.dst),
            row.src_slot_key.as_deref().unwrap_or("-"),
            kind_label(row.src_kind),
            row.n1 as u8,
            tsv_cell(&row.origin),
            row.origin_slot_key.as_deref().unwrap_or("-"),
            kind_label(row.origin_kind),
            row.resolved as u8,
            row.live_after as u8,
            row.live_entry as u8,
            row.live_after_syn as u8,
            row.src_mut as u8,
            row.src_mut_defaulted as u8,
            row.escape,
            row.rv_ptr as u8,
            row.dst_is_elim_temp as u8,
        ));
    }
    out
}

pub(crate) fn fns_tsv(fn_rows: &[FnRow]) -> String {
    let mut out = String::from("fn\targ_count\tn0\tloan_sites_structural\n");
    for row in fn_rows {
        out.push_str(&format!(
            "{}\t{}\t{}\t{}\n",
            tsv_cell(&row.fn_key),
            row.arg_count,
            row.n0,
            row.loan_sites_structural,
        ));
    }
    out
}

/// The per-program roll-up. Kept as ordered key/value text so a shell join can read it without a
/// parser, and so the aggregate is recomputable from `rows_tsv` as a cross-check.
pub(crate) fn summary(rows: &[CopyRow], fn_rows: &[FnRow]) -> BTreeMap<&'static str, usize> {
    let mut out = BTreeMap::new();
    let n1: Vec<&CopyRow> = rows.iter().filter(|row| row.n1).collect();
    let n2: Vec<&&CopyRow> = n1.iter().filter(|row| row.live_after).collect();
    let n4: Vec<&&&CopyRow> = n2.iter().filter(|row| row.escaping()).collect();
    let zero_loan_fns: FxHashSet<&str> = fn_rows
        .iter()
        .filter(|row| row.loan_sites_structural == 0)
        .map(|row| row.fn_key.as_str())
        .collect();

    out.insert("n0", rows.len());
    out.insert("n0_rv_ptr", rows.iter().filter(|row| row.rv_ptr).count());
    out.insert(
        "n0_dst_elim_temp",
        rows.iter().filter(|row| row.dst_is_elim_temp).count(),
    );
    out.insert(
        "n0_resolved",
        rows.iter().filter(|row| row.resolved).count(),
    );
    out.insert(
        "src_slot_unresolved",
        rows.iter().filter(|row| row.src_slot_key.is_none()).count(),
    );
    out.insert("n1", n1.len());
    out.insert(
        "n1_origin",
        rows.iter()
            .filter(|row| row.origin_kind == Some(SlotKind::Ref))
            .count(),
    );
    out.insert("n2", n2.len());
    out.insert(
        "n2_syntactic_local",
        n1.iter().filter(|row| row.live_after_syn).count(),
    );
    out.insert(
        "n2_entry_seek",
        n1.iter().filter(|row| row.live_entry).count(),
    );
    out.insert("n2m", n2.iter().filter(|row| row.src_mut).count());
    out.insert("n2s", n2.iter().filter(|row| !row.src_mut).count());
    out.insert(
        "n2_mut_defaulted",
        n2.iter().filter(|row| row.src_mut_defaulted).count(),
    );
    out.insert("n4", n4.len());
    out.insert(
        "n4_return",
        n4.iter().filter(|row| row.escape == "return").count(),
    );
    out.insert(
        "n4_deref_param",
        n4.iter().filter(|row| row.escape == "deref-param").count(),
    );
    out.insert("n4m", n4.iter().filter(|row| row.src_mut).count());
    out.insert("n4s", n4.iter().filter(|row| !row.src_mut).count());
    out.insert(
        "n2_in_zero_loan_fn",
        n2.iter()
            .filter(|row| zero_loan_fns.contains(row.fn_key.as_str()))
            .count(),
    );
    out.insert(
        "n4_in_zero_loan_fn",
        n4.iter()
            .filter(|row| zero_loan_fns.contains(row.fn_key.as_str()))
            .count(),
    );
    out.insert("fns", fn_rows.len());
    out.insert("fns_zero_loan_structural", zero_loan_fns.len());
    out
}

/// Write the three artifacts for one program. Returns the row count.
pub(crate) fn write_program_census<'tcx>(
    dir: &Path,
    name: &str,
    tcx: TyCtxt<'tcx>,
    program: &RustProgram<'tcx>,
    slots: &CrateSlots,
    model: &FxHashMap<SlotRef, SlotKind>,
    mut_facts: &MutFacts,
) -> Result<usize, String> {
    let (rows, fn_rows) = census(tcx, program, slots, model, mut_facts);
    fs::create_dir_all(dir).map_err(|error| format!("escgap dir {}: {error}", dir.display()))?;
    let write = |suffix: &str, body: String| -> Result<(), String> {
        let path = dir.join(format!("{name}.{suffix}"));
        fs::write(&path, body).map_err(|error| format!("write {}: {error}", path.display()))
    };
    write("escgap.tsv", rows_tsv(&rows))?;
    write("escgap.fns", fns_tsv(&fn_rows))?;
    let summary = summary(&rows, &fn_rows);
    let mut text = format!("program\t{name}\n");
    for (key, value) in &summary {
        text.push_str(&format!("{key}\t{value}\n"));
    }
    write("escgap.summary", text)?;
    Ok(rows.len())
}

// ---------------------------------------------------------------------------
// Non-vacuity control
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::analyses::borrow_ownership::{
        construction::{CopyLendMode, construct_bo_into, verify_bo_construction},
        origins::compute_origins,
        solver::KindSolver,
    };

    /// The ESC-W1 pin fixture, verbatim from `tests.rs::escw1_escape_shape_x_stays_ref_known_gap`.
    const ESC_W1: &str = r#"
unsafe fn save(out: *mut *mut i32, x: *mut i32) { *out = x; *x = 1; }
unsafe fn caller() -> i32 {
    let mut cell = 0i32;
    let mut slot: *mut i32 = core::ptr::null_mut();
    save(&raw mut slot, &raw mut cell);
    *slot
}
"#;

    /// Same shape with the escape REMOVED — the discriminating control. If this also landed in N4
    /// the escape column would be measuring nothing.
    const NO_ESCAPE: &str = r#"
unsafe fn save(out: *mut *mut i32, x: *mut i32) { let _ = out; *x = 1; }
unsafe fn caller() -> i32 {
    let mut cell = 0i32;
    let mut slot: *mut i32 = core::ptr::null_mut();
    save(&raw mut slot, &raw mut cell);
    *slot
}
"#;

    /// Same shape with the post-store write removed, so the escaped pointer is genuinely dead
    /// after the store — the liveness column's discriminating control.
    const DEAD_AFTER: &str = r#"
unsafe fn save(out: *mut *mut i32, x: *mut i32) { *out = x; }
unsafe fn caller() -> i32 {
    let mut cell = 0i32;
    let mut slot: *mut i32 = core::ptr::null_mut();
    save(&raw mut slot, &raw mut cell);
    *slot
}
"#;

    /// Run the fixture's own accepted-model pipeline (the one
    /// `escw1_escape_shape_x_stays_ref_known_gap` pins) and hand the census the accepted model.
    fn census_of(code: &'static str) -> (Vec<CopyRow>, BTreeMap<&'static str, usize>) {
        let mut captured = None;
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = super::super::collect_program(tcx);
            let f = program
                .functions
                .iter()
                .copied()
                .find(|did| tcx.def_path_str(did.to_def_id()).rsplit("::").next() == Some("save"))
                .expect("fixture defines `save`");
            let _ = f;
            // Assembled through `construction.rs`'s shared helper — the phase-1b construction
            // ratchet forbids a fresh direct consumer of the legacy three-stage pipeline, and this
            // is also the path the corpus worker takes, so the fixture's model is built the same
            // way the measured programs' models are.
            let origins = compute_origins(&program);
            let slots = CrateSlots::build(&program);
            let facts = MutFacts::from_program(&program);
            let solver = KindSolver::new(&slots);
            let construction = construct_bo_into(
                &program,
                &slots,
                &origins,
                &facts,
                &solver,
                CopyLendMode::Baseline,
            )
            .expect("emission");
            let model =
                verify_bo_construction(&program, &slots, &origins, &solver, &construction, &facts)
                    .expect("the fixture accepts");
            let (rows, fn_rows) = census(tcx, &program, &slots, &model, &facts);
            let summary = summary(&rows, &fn_rows);
            captured = Some((rows, summary));
        })
        .unwrap_or_else(|error| error.raise());
        captured.expect("compiler callback ran")
    }

    fn escaping_save_rows(rows: &[CopyRow]) -> Vec<&CopyRow> {
        rows.iter()
            .filter(|row| row.fn_key.rsplit("::").next() == Some("save") && row.escaping())
            .collect()
    }

    /// **The census's non-vacuity control.** `*out = x` is the escaping copy the ESC-GAP witness
    /// turns on; if the census definitions are right it must be in N4, i.e. it must clear N0
    /// (pointer-typed copy), N1 (`x` is `Ref` in the accepted model — the pinned gap), N2 (`x` is
    /// live after the store, because `*x = 1` follows) and the escape test (`(*_1)` is a deref of
    /// a parameter). If this fails the census definition is wrong, not the analysis.
    ///
    /// It also pins the operand-temporary correction: MIR routes the store through a temp, so
    /// `live_after_syn` is FALSE at this very site while `live_after` is TRUE. Losing the
    /// correction would silently empty the population of exactly the shape ② targets.
    #[test]
    fn escgap_census_nonvacuity_escw1_copy_is_in_n4() {
        let (rows, summary) = census_of(ESC_W1);
        let escaping = escaping_save_rows(&rows);
        assert_eq!(
            escaping.len(),
            1,
            "ESC-W1's `save` has exactly one escaping copy (`*out = x`); got {escaping:#?}"
        );
        let row = escaping[0];
        assert_eq!(row.escape, "deref-param", "row: {row:#?}");
        assert!(row.n1, "N1: the pinned Ref-modeled source; row: {row:#?}");
        assert!(
            row.resolved && !row.live_after_syn,
            "the operand-temporary correction must be what carries this site; row: {row:#?}"
        );
        assert!(
            row.live_after,
            "N2: `x` is live after the store because `*x = 1` follows; row: {row:#?}"
        );
        assert!(
            row.src_mut,
            "`x` is written through, so the source is mut; row: {row:#?}"
        );
        assert!(
            summary["n4"] >= 1,
            "the ESC-W1 copy must reach N4; summary {summary:?}"
        );
    }

    /// The other half of the control: removing the escape must remove the N4 membership. Without
    /// this, `escape` could be a column that is true everywhere.
    #[test]
    fn escgap_census_escape_column_discriminates() {
        let (rows, _) = census_of(NO_ESCAPE);
        let escaping = escaping_save_rows(&rows);
        assert!(
            escaping.is_empty(),
            "no escape in the source ⇒ no escaping copy; got {escaping:#?}"
        );
    }

    /// And the liveness column: with nothing after the store the escaped pointer is dead, so the
    /// site must be escaping but NOT in N2.
    #[test]
    fn escgap_census_liveness_column_discriminates() {
        let (rows, summary) = census_of(DEAD_AFTER);
        let escaping = escaping_save_rows(&rows);
        assert_eq!(
            escaping.len(),
            1,
            "still one escaping copy; got {escaping:#?}"
        );
        assert!(
            !escaping[0].live_after,
            "nothing follows the store, so the source is dead after it; row: {:#?}",
            escaping[0]
        );
        assert_eq!(summary["n4"], 0, "…and it must not reach N4; {summary:?}");
    }
}
