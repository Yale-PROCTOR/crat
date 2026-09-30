//! era-5c R607-1 leg A: **the raw-cause ledger.** For every slot the accepted
//! model settles Raw, why:
//!
//! - `first_noref`: the `¬ref` commit in the tracked core of "can this slot be
//!   Ref?" -- a Mode-A commit (retirement conflict, retirement raw target,
//!   reader obligation, borrow exclusion) or an eager exclusion named by its
//!   emission context; on another slot, the constraint families that carry it
//!   here (`kind-equate`, `safe-mono`, ...);
//! - `own_refusal`: the family of the tracked core of "can it own?"
//!   (`own-assume[<class>]`, `link-own`, a selector, ...);
//! - `verdict_class`: `ref-excluded`, `own-refused`, `both`, or `objective`
//!   (neither: the optimum chose Raw for a joint reason).
//!
//! - `noref_clause` / `noref_ref_peers` / `noref_raw_invalidators` (L01¹¹,
//!   R668-4): for a Mode-A commit named as the first cause, the clause the
//!   guarded planner (R617-1) would assert there, `¬ref(t) ∨ ⋁¬ref(Ref peers) ∨
//!   ⋁ref(Raw invalidators)`, from the commit round's model.
//!
//! Observation only: two hard queries per Raw slot after the fixpoint, no
//! assertion added and no counter the entry records touched, so the model, the
//! entry's bytes and its identity are unchanged. `CRAT_ERA5C_RAW_CAUSE_LEDGER`
//! (`on|off`, default off) is not a model input and stays out of
//! `solver_identity`; the sidecar is `<program>.raw-cause-ledger.tsv` beside the
//! entry, keyed by the entry's own slot keys.

use std::cell::RefCell;

use rustc_hash::FxHashMap;
use rustc_middle::ty::TyCtxt;
use z3::ast::Bool;

use super::{
    SlotRef,
    crate_slots::CrateSlots,
    domain::SlotKind,
    solver::{HardLoopSolver, KindSolver, Selectors},
};

/// `CRAT_ERA5C_RAW_CAUSE_BUDGET_S`: the probes' wall budget per ledger; past
/// it a row keeps its direct commit and says `unprobed`. Unset: no budget.
fn budget() -> Option<std::time::Duration> {
    std::env::var("CRAT_ERA5C_RAW_CAUSE_BUDGET_S")
        .ok()
        .map(|value| {
            std::time::Duration::from_secs(value.parse().unwrap_or_else(|_| {
                panic!("CRAT_ERA5C_RAW_CAUSE_BUDGET_S must be seconds, got {value:?}")
            }))
        })
}

/// Whether Mode-A's replay records each conflict's invalidators (R668-4): with
/// the ledger. W74 fault (test builds only): they are not recorded.
pub(crate) fn records_invalidators() -> bool {
    #[cfg(test)]
    if std::env::var("CRAT_E5C_W74_FAULT").as_deref() == Ok("no-invalidators") {
        return false;
    }
    enabled()
}

pub(crate) fn enabled() -> bool {
    // W67 fault (test builds only): the ledger is silenced.
    #[cfg(test)]
    if std::env::var("CRAT_E5C_W67_FAULT").as_deref() == Ok("no-ledger") {
        return false;
    }
    match std::env::var("CRAT_ERA5C_RAW_CAUSE_LEDGER").as_deref() {
        Err(_) | Ok("off") => false,
        Ok("on") => true,
        Ok(other) => panic!("CRAT_ERA5C_RAW_CAUSE_LEDGER must be on|off, got {other:?}"),
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CommitKind {
    RetirementConflict,
    RetirementRaw,
    ReaderObligation,
    BorrowExclusion,
    /// R617-1: a guarded clause `¬ref(t) ∨ ⋁¬ref(n) ∨ ⋁ref(p)`.
    GuardedCommit,
    /// R617-1: a guarded hazard re-witnessed with no re-enabler, made permanent.
    RecurrenceEscalation,
}

impl CommitKind {
    fn label(self) -> &'static str {
        match self {
            CommitKind::RetirementConflict => "retirement-conflict",
            CommitKind::RetirementRaw => "retirement-raw",
            CommitKind::ReaderObligation => "reader-obligation",
            CommitKind::BorrowExclusion => "borrow-exclusion",
            CommitKind::GuardedCommit => "guarded-commit",
            CommitKind::RecurrenceEscalation => "recurrence-escalation",
        }
    }
}

/// One Mode-A commit, with the track literal it was asserted under.
#[derive(Clone, Debug)]
pub(crate) struct Commit {
    pub track: Bool,
    pub slot: SlotRef,
    pub round: usize,
    pub kind: CommitKind,
    pub issuer: Option<SlotRef>,
    /// The commit's witnessed clause (a `¬ref` commit; not a raw assumption).
    pub clause: Option<Clause>,
}

/// L01¹¹ (R668-4; analysis-fanout 014 STOP 1 (i)): the peers the guarded
/// planner (R617-1) witnesses for a Mode-A commit on `t`, read from the round's
/// model as `l2::Candidate::from_observation` reads them. Its clause is
/// `¬ref(t) ∨ ⋁¬ref(ref_peers) ∨ ⋁ref(raw_invalidators)`.
#[derive(Clone, Debug)]
pub(crate) struct Clause {
    /// `guarded`; or `self-issued` -- no issuer other than the target, which
    /// the planner commits unconditionally (its invalidators are still listed).
    pub shape: &'static str,
    /// The issuer, when it is not the target. Every residual conflict's slot is
    /// Ref at a Mode-A commit (`guard_slots_are_ref`), so it is witnessed Ref.
    pub ref_peers: Vec<SlotRef>,
    /// The conflict's invalidators, other than the target, that are Raw.
    pub raw_invalidators: Vec<SlotRef>,
}

impl Clause {
    pub(crate) fn witnessed(
        target: SlotRef,
        issuer: Option<SlotRef>,
        invalidators: &[SlotRef],
        model: &FxHashMap<SlotRef, SlotKind>,
    ) -> Self {
        let issuer = issuer.filter(|issuer| *issuer != target);
        Clause {
            shape: if issuer.is_some() {
                "guarded"
            } else {
                "self-issued"
            },
            ref_peers: issuer.into_iter().collect(),
            raw_invalidators: invalidators
                .iter()
                .copied()
                .filter(|slot| *slot != target && model.get(slot) == Some(&SlotKind::Raw))
                .collect(),
        }
    }
}

/// The sidecar's columns: keyed (program, function, MIR local, depth) as the
/// census keys its subjects (`owner_fn`, `mir_local`, `ptr_depth` less one), with
/// the entry's own slot key beside them. A field slot names its struct and
/// `field<N>` in place of the function and the local.
pub(crate) const HEADER: &str = "program\tfunction\tmir_local\tdepth\tslot_key\t\
verdict_class\tfirst_noref_kind\tnoref_slot\tnoref_round\tnoref_issuer\tnoref_partner\t\
noref_via\town_refusal\town_core\tnoref_clause\tnoref_ref_peers\tnoref_raw_invalidators";

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Row {
    pub function: String,
    pub mir_local: String,
    pub depth: u8,
    pub key: String,
    pub verdict: &'static str,
    pub first_noref: String,
    pub noref_slot: String,
    pub noref_round: String,
    pub noref_issuer: String,
    pub noref_via: String,
    pub own_refusal: String,
    pub own_core: String,
    pub noref_clause: String,
    pub noref_ref_peers: String,
    pub noref_raw_invalidators: String,
}

impl Row {
    /// The row without the program column.
    pub(crate) fn tsv(&self) -> String {
        [
            self.key.as_str(),
            self.verdict,
            &self.first_noref,
            &self.noref_slot,
            &self.noref_round,
            &self.noref_issuer,
            &self.noref_via,
            &self.own_refusal,
            &self.own_core,
            &self.noref_clause,
            &self.noref_ref_peers,
            &self.noref_raw_invalidators,
        ]
        .join("\t")
    }

    /// The sidecar row (`HEADER`'s columns after `program`).
    pub(crate) fn sidecar(&self) -> String {
        let partner = if self.noref_via == "direct" || self.noref_slot == "-" {
            "-"
        } else {
            self.noref_slot.as_str()
        };
        [
            self.function.as_str(),
            &self.mir_local,
            &self.depth.to_string(),
            &self.key,
            self.verdict,
            &self.first_noref,
            &self.noref_slot,
            &self.noref_round,
            &self.noref_issuer,
            partner,
            &self.noref_via,
            &self.own_refusal,
            &self.own_core,
            &self.noref_clause,
            &self.noref_ref_peers,
            &self.noref_raw_invalidators,
        ]
        .join("\t")
    }
}

thread_local! {
    /// The kind of each emission-time exclusion, by its track: the tracker's
    /// context is not reset between these loops, so its label cannot say.
    static EAGER: RefCell<FxHashMap<Bool, &'static str>> = RefCell::new(FxHashMap::default());
    /// One ledger per accepted fixpoint (the baseline and the A5 solves each
    /// accept one), keyed by the digest of the model it explains.
    static LEDGERS: RefCell<Vec<(String, Vec<Row>)>> = const { RefCell::new(Vec::new()) };
    /// The ledger the last `take_for` returned, for the witnesses.
    static LAST: RefCell<Option<Vec<Row>>> = const { RefCell::new(None) };
}

/// R645-2 (era-5c 088): `CRAT_ERA5C_EAGER_DUMP=on` prints every emission-time
/// `¬ref` with its kind (`E5C_EAGER kind slot`). Instrument only.
pub(crate) fn dump_eager(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    slots: &super::crate_slots::CrateSlots,
    slot: SlotRef,
    kind: &str,
) {
    if std::env::var_os("CRAT_ERA5C_EAGER_DUMP").is_some() {
        let key =
            super::model_cache::render_key(tcx, slots, slot).unwrap_or_else(|| format!("{slot:?}"));
        eprintln!("E5C_EAGER\t{kind}\t{key}");
    }
}

/// Name the exclusion `solver` asserted last (an emission-time `¬ref`).
pub(crate) fn note_eager(solver: &KindSolver, kind: &'static str) {
    if enabled()
        && let Some(track) = solver.last_track()
    {
        EAGER.with(|eager| eager.borrow_mut().insert(track, kind));
    }
}

/// The ledger that explains `model`; drains every pending ledger.
pub(crate) fn take_for(model: &FxHashMap<SlotRef, SlotKind>) -> Option<Vec<Row>> {
    let digest = super::construction::model_digest(model);
    EAGER.with(|eager| eager.borrow_mut().clear());
    let rows = LEDGERS
        .with(|ledgers| std::mem::take(&mut *ledgers.borrow_mut()))
        .into_iter()
        .rev()
        .find(|(d, _)| *d == digest)
        .map(|(_, rows)| rows);
    LAST.with(|last| *last.borrow_mut() = rows.clone());
    rows
}

pub(crate) fn last() -> Option<Vec<Row>> {
    LAST.with(|last| last.borrow().clone())
}

/// The family of one core label: its head, after the emission context and
/// before the arguments (`ctx::own-assume[temporary-finalization](7=false)` is
/// `own-assume[temporary-finalization]`).
fn family(label: &str) -> String {
    let head = label.split('(').next().unwrap_or(label);
    head.rsplit("::").next().unwrap_or(head).to_owned()
}

fn joined(mut families: Vec<String>) -> String {
    families.retain(|f| f != "one-hot");
    families.sort();
    families.dedup();
    if families.is_empty() {
        "-".to_owned()
    } else {
        families.join(",")
    }
}

/// Run the two queries on every Raw slot of the accepted `model` and keep the
/// ledger for the writer.
#[allow(clippy::too_many_arguments)]
pub(crate) fn publish(
    tcx: TyCtxt<'_>,
    slots: &CrateSlots,
    solver: &KindSolver,
    hard: Option<&HardLoopSolver>,
    selectors: &Selectors,
    dropped: &[Bool],
    model: &FxHashMap<SlotRef, SlotKind>,
    commits: &[Commit],
) {
    let owned;
    let hard = match hard {
        Some(hard) => {
            hard.sync_from(solver);
            hard
        }
        None => {
            owned = solver.hard_loop_solver();
            &owned
        }
    };
    let kept: Vec<Bool> = selectors
        .all()
        .iter()
        .filter(|s| !dropped.contains(s))
        .cloned()
        .collect();
    // (function, MIR local, depth) of a slot; a field names its struct.
    let parts = |slot: SlotRef| -> (String, String, u8) {
        match slot {
            SlotRef::Local(function, id) => {
                let s = slots.fn_local_slots[&function].slot(id);
                let local = match s.owner {
                    super::slots::SlotOwner::Local(local) => local.as_usize().to_string(),
                    _ => "?".to_owned(),
                };
                (tcx.def_path_str(function.to_def_id()), local, s.depth)
            }
            SlotRef::Field(id) => {
                let s = slots.field_slots.slot(id);
                match s.owner {
                    super::slots::SlotOwner::Field(field) => (
                        tcx.def_path_str(field.struct_did.to_def_id()),
                        format!("field{}", field.field_index),
                        s.depth,
                    ),
                    _ => ("?".to_owned(), "?".to_owned(), s.depth),
                }
            }
        }
    };
    let key = |slot: SlotRef| {
        super::model_cache::render_key(tcx, slots, slot).unwrap_or_else(|| format!("{slot:?}"))
    };
    // Emission order breaks every tie, so the ledger is deterministic.
    let ordered = solver.tracked_labels();
    let position: FxHashMap<Bool, usize> = ordered
        .iter()
        .enumerate()
        .map(|(index, (track, _))| (track.clone(), index))
        .collect();
    let labels: FxHashMap<Bool, String> = ordered.iter().cloned().collect();
    let selector_family: FxHashMap<Bool, &'static str> = selectors
        .all()
        .iter()
        .map(|s| {
            let family = if selectors.is_sink(s) {
                "sink-selector"
            } else {
                "source-selector"
            };
            (s.clone(), family)
        })
        .collect();
    let by_track: FxHashMap<Bool, &Commit> = commits.iter().map(|c| (c.track.clone(), c)).collect();
    // The exclusion a label asserts, by the exact text the solver formats.
    let mut excludes: FxHashMap<String, SlotRef> = FxHashMap::default();
    for &slot in model.keys() {
        excludes.insert(format!("borrow-exclusion(Some({slot:?}),[])"), slot);
        excludes.insert(format!("kind-pin({slot:?},Raw)"), slot);
    }
    let eager: FxHashMap<Bool, &'static str> = EAGER.with(|eager| eager.borrow().clone());
    // The exclusion a label asserts: an emission-time `¬ref` by its noted
    // kind, a `kind-pin(_, Raw)` as a raw pin, else by the label's context.
    let excluded = |track: &Bool, label: &str| -> Option<(SlotRef, String)> {
        let (at, pin) = match label.find("borrow-exclusion(") {
            Some(at) => (at, false),
            None => (label.find("kind-pin(")?, true),
        };
        let slot = *excludes.get(&label[at..])?;
        let kind = match eager.get(track) {
            Some(kind) => format!("eager:{kind}"),
            None if pin => "raw-pin".to_owned(),
            None => format!("eager:{}", label[..at].trim_end_matches("::")),
        };
        Some((slot, kind))
    };
    // A slot's own `¬ref` commit excludes Ref by itself: no probe is owed. The
    // earliest wins (emission-time exclusions are round 0).
    // (kind, round, issuer, the commit's index in `commits`).
    type Named = (String, usize, Option<SlotRef>, Option<usize>);
    let mut direct: FxHashMap<SlotRef, Named> = FxHashMap::default();
    let mut note = |slot: SlotRef, named: Named| {
        let entry = direct.entry(slot).or_insert(named.clone());
        if named.1 < entry.1 {
            *entry = named;
        }
    };
    for (track, label) in &ordered {
        if !by_track.contains_key(track)
            && let Some((slot, kind)) = excluded(track, label)
        {
            note(slot, (kind, 0, None, None));
        }
    }
    for (index, commit) in commits.iter().enumerate() {
        note(
            commit.slot,
            (
                commit.kind.label().to_owned(),
                commit.round,
                commit.issuer,
                Some(index),
            ),
        );
    }
    // The named commit's clause, rendered.
    let keys = |slots: &[SlotRef]| {
        if slots.is_empty() {
            "-".to_owned()
        } else {
            slots.iter().map(|s| key(*s)).collect::<Vec<_>>().join(",")
        }
    };
    let name_clause = |row: &mut Row, clause: Option<&Clause>| {
        if let Some(clause) = clause {
            row.noref_clause = clause.shape.to_owned();
            row.noref_ref_peers = keys(&clause.ref_peers);
            row.noref_raw_invalidators = keys(&clause.raw_invalidators);
        }
    };
    let started = std::time::Instant::now();
    let budget = budget();
    let (mut probes, mut unprobed) = (0usize, 0usize);
    // era-5c R701 (instrument, test builds): `CRAT_E5C_LEDGER_ALSO=<substring>` also
    // probes the non-Raw slots whose key contains it, and prints why each is not Raw
    // and not Ref (`E5C_ALSO`). The ledger's rows for Raw slots are unchanged.
    let also = if cfg!(test) {
        std::env::var("CRAT_E5C_LEDGER_ALSO").ok()
    } else {
        None
    };
    let mut raw: Vec<(String, SlotRef)> = model
        .iter()
        .filter(|(slot, kind)| {
            **kind == SlotKind::Raw
                || also
                    .as_deref()
                    .is_some_and(|filter| key(**slot).contains(filter))
        })
        .map(|(slot, _)| (key(*slot), *slot))
        .collect();
    raw.sort_by(|left, right| left.0.cmp(&right.0));
    let mut rows = Vec::with_capacity(raw.len());
    for (slot_key, slot) in raw {
        let direct_commit = direct.get(&slot).cloned();
        let (function, mir_local, depth) = parts(slot);
        let mut row = Row {
            function,
            mir_local,
            depth,
            key: slot_key,
            verdict: "objective",
            first_noref: "none".to_owned(),
            noref_slot: "-".to_owned(),
            noref_round: "-".to_owned(),
            noref_issuer: "-".to_owned(),
            noref_via: "-".to_owned(),
            own_refusal: "none".to_owned(),
            own_core: "-".to_owned(),
            noref_clause: "-".to_owned(),
            noref_ref_peers: "-".to_owned(),
            noref_raw_invalidators: "-".to_owned(),
        };
        if let Some((kind, round, issuer, clause)) = &direct_commit {
            row.first_noref = kind.clone();
            row.noref_slot = row.key.clone();
            row.noref_round = round.to_string();
            row.noref_issuer = issuer.map_or_else(|| "-".to_owned(), key);
            row.noref_via = "direct".to_owned();
            name_clause(&mut row, clause.and_then(|i| commits[i].clause.as_ref()));
        }
        if budget.is_some_and(|budget| started.elapsed() >= budget) {
            row.verdict = "unprobed";
            unprobed += 1;
            rows.push(row);
            continue;
        }
        let ref_probe = match &direct_commit {
            Some(_) => Ok(None),
            None => {
                probes += 1;
                solver.raw_cause_probe(hard, &kept, slot, SlotKind::Ref)
            }
        };
        probes += 1;
        let own_probe = solver.raw_cause_probe(hard, &kept, slot, SlotKind::Owning);
        if model[&slot] != SlotKind::Raw {
            let render = |core: &[Bool]| -> String {
                core.iter()
                    .map(|literal| {
                        selector_family
                            .get(literal)
                            .map(|f| format!("selector:{f}"))
                            .or_else(|| {
                                by_track
                                    .get(literal)
                                    .map(|c| format!("commit:{}({:?})", c.kind.label(), c.slot))
                            })
                            .or_else(|| labels.get(literal).cloned())
                            .unwrap_or_else(|| format!("{literal:?}"))
                    })
                    .collect::<Vec<_>>()
                    .join(" | ")
            };
            for (name, kind) in [
                ("raw", SlotKind::Raw),
                ("ref", SlotKind::Ref),
                ("own", SlotKind::Owning),
            ] {
                let verdict = match solver.raw_cause_probe(hard, &kept, slot, kind) {
                    Ok(None) => "sat".to_owned(),
                    Ok(Some(core)) => format!("unsat {}", render(&core)),
                    Err(reason) => format!("unknown {reason}"),
                };
                eprintln!(
                    "E5C_ALSO {} model={:?} {name}-probe={verdict}",
                    row.key, model[&slot]
                );
            }
        }
        // (slot, kind, round, issuer, position, clause) of every exclusion in the Ref core.
        let mut exclusions: Vec<(
            SlotRef,
            String,
            usize,
            Option<SlotRef>,
            usize,
            Option<&Clause>,
        )> = Vec::new();
        let mut via = Vec::new();
        let ref_excluded = direct_commit.is_some()
            || match &ref_probe {
                Ok(Some(core)) => {
                    for literal in core {
                        let at = position.get(literal).copied().unwrap_or(usize::MAX);
                        if let Some(commit) = by_track.get(literal) {
                            exclusions.push((
                                commit.slot,
                                commit.kind.label().to_owned(),
                                commit.round,
                                commit.issuer,
                                at,
                                commit.clause.as_ref(),
                            ));
                        } else if let Some(family) = selector_family.get(literal) {
                            via.push((*family).to_owned());
                        } else if let Some(label) = labels.get(literal) {
                            match excluded(literal, label) {
                                Some((slot, kind)) => {
                                    exclusions.push((slot, kind, 0, None, at, None))
                                }
                                None => via.push(family(label)),
                            }
                        }
                    }
                    true
                }
                Ok(None) => false,
                Err(reason) => {
                    row.first_noref = format!("unknown:{reason}");
                    false
                }
            };
        if ref_excluded && direct_commit.is_none() {
            // The slot's own commit first, then the earliest.
            exclusions.sort_by_key(|(s, _, round, _, at, _)| (*s != slot, *round, *at));
            match exclusions.first() {
                Some((excluded, kind, round, issuer, _, clause)) => {
                    row.first_noref = kind.clone();
                    row.noref_slot = key(*excluded);
                    row.noref_round = round.to_string();
                    row.noref_issuer = issuer.map_or_else(|| "-".to_owned(), key);
                    row.noref_via = if *excluded == slot {
                        "direct".to_owned()
                    } else {
                        joined(via)
                    };
                    name_clause(&mut row, *clause);
                }
                None => {
                    row.first_noref = "structural".to_owned();
                    row.noref_via = joined(via);
                }
            }
        }
        let own_refused = match &own_probe {
            Ok(Some(core)) => {
                // R0 (R645-3, group (a)): `CRAT_ERA5C_RAW_CAUSE_LABELS=<substring>` prints
                // the full label of every literal in the own core of a matching slot.
                // Instrument only: the ledger's rows are unchanged.
                if let Ok(filter) = std::env::var("CRAT_ERA5C_RAW_CAUSE_LABELS")
                    && row.key.contains(filter.as_str())
                {
                    for literal in core.iter() {
                        let label = selector_family
                            .get(literal)
                            .map(|f| format!("selector:{f}"))
                            .or_else(|| {
                                by_track
                                    .get(literal)
                                    .map(|c| format!("commit:{}({:?})", c.kind.label(), c.slot))
                            })
                            .or_else(|| labels.get(literal).cloned())
                            .unwrap_or_else(|| format!("{literal:?}"));
                        eprintln!("E5C_OWN_CORE {}\t{label}", row.key);
                    }
                }
                let families: Vec<String> = core
                    .iter()
                    .filter_map(|literal| {
                        selector_family
                            .get(literal)
                            .map(|f| (*f).to_owned())
                            .or_else(|| by_track.get(literal).map(|c| c.kind.label().to_owned()))
                            .or_else(|| labels.get(literal).map(|l| family(l)))
                    })
                    .collect();
                // Every `own-assume` class the core holds (a core is not
                // minimal, so all of them), else the first other family.
                let mut assumes: Vec<&String> = families
                    .iter()
                    .filter(|f| f.starts_with("own-assume["))
                    .collect();
                assumes.sort();
                assumes.dedup();
                row.own_core = joined(families.clone());
                row.own_refusal = if assumes.is_empty() {
                    ["link-own", "source-selector", "sink-selector"]
                        .iter()
                        .find(|head| families.iter().any(|f| f == *head))
                        .map(|head| (*head).to_owned())
                        .or_else(|| families.iter().find(|f| *f != "one-hot").cloned())
                        .unwrap_or_else(|| "structural".to_owned())
                } else {
                    assumes
                        .iter()
                        .map(|f| f.as_str())
                        .collect::<Vec<_>>()
                        .join("+")
                };
                true
            }
            Ok(None) => false,
            Err(reason) => {
                row.own_refusal = format!("unknown:{reason}");
                false
            }
        };
        row.verdict = if ref_probe.is_err() || own_probe.is_err() {
            "unknown"
        } else {
            match (ref_excluded, own_refused) {
                (true, true) => "both",
                (true, false) => "ref-excluded",
                (false, true) => "own-refused",
                (false, false) => "objective",
            }
        };
        rows.push(row);
    }
    eprintln!(
        "E5C_LEDGER_STATS rows={} direct={} probes={probes} unprobed={unprobed} secs={:.3}",
        rows.len(),
        rows.iter().filter(|row| row.noref_via == "direct").count(),
        started.elapsed().as_secs_f64()
    );
    let digest = super::construction::model_digest(model);
    LEDGERS.with(|ledgers| ledgers.borrow_mut().push((digest, rows)));
}
