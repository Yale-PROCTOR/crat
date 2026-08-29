//! ESC-GAP ②-minimal exact-site selector.

use std::{cell::RefCell, sync::OnceLock};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::{
    mir::{Body, Local, Location, Operand, Place, PlaceElem, RETURN_PLACE, Rvalue, StatementKind},
    ty::TyCtxt,
};
use rustc_mir_dataflow::Analysis;
use rustc_span::def_id::LocalDefId;

use super::{
    coherence::{SelectedCopyLendLoan, SelectedCopyLendLoans},
    crate_slots::CrateSlots,
    domain::SlotKind,
    export::{BorrowerKind, OwnerKey, PlaceKey},
    l2::MirLocationKey,
    resolve::{ResolvedSlot, resolve_place},
    slot_key::{field_key, local_key},
    slots::SlotOwner,
    solver::SlotRef,
};
use crate::{
    analyses::{
        borrow::{ProvenanceOwner, StructFieldSlot as BorrowFieldSlot},
        liveness::MaybeLiveLocals,
        output_params::eliminable_temporaries::eliminable_temporaries,
    },
    utils::rustc::RustProgram,
};

const ORIGIN_CHASE_LIMIT: usize = 8;
const ALLOWLIST: &str = include_str!("esc_minimal_allowlist.tsv");

#[derive(Clone, Debug, PartialEq, Eq)]
struct ArtifactKey {
    program: &'static str,
    function: &'static str,
    location: MirLocationKey,
    resolved_origin_slot: &'static str,
    destination_place: &'static str,
}

fn artifact_keys() -> &'static [ArtifactKey] {
    static KEYS: OnceLock<Vec<ArtifactKey>> = OnceLock::new();
    KEYS.get_or_init(|| {
        let mut lines = ALLOWLIST.lines();
        assert_eq!(
            lines.next(),
            Some(
                "program\tfunction\tblock\tstatement_index\tresolved_origin_slot\tdestination_place"
            )
        );
        let keys = lines
            .filter(|line| !line.is_empty())
            .map(|line| {
                let fields = line.split('\t').collect::<Vec<_>>();
                assert_eq!(fields.len(), 6, "short ESC allowlist row: {line}");
                ArtifactKey {
                    program: fields[0],
                    function: fields[1],
                    location: MirLocationKey::new(
                        fields[2].parse().expect("ESC allowlist block"),
                        fields[3].parse().expect("ESC allowlist statement"),
                    ),
                    resolved_origin_slot: fields[4],
                    destination_place: fields[5],
                }
            })
            .collect::<Vec<_>>();
        assert_eq!(keys.len(), 36, "②-minimal allowlist must contain 36 rows");
        keys
    })
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct EscCopySiteKey {
    pub(crate) program: String,
    pub(crate) function: String,
    pub(crate) location: MirLocationKey,
    pub(crate) resolved_origin_slot: String,
    pub(crate) destination_place: String,
}

#[derive(Clone, Debug)]
pub(crate) struct EscRuntimeSite {
    pub(crate) key: EscCopySiteKey,
    pub(crate) fn_did: LocalDefId,
    pub(crate) lhs: SlotRef,
    pub(crate) rhs: SlotRef,
    pub(crate) loan: SelectedCopyLendLoan,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum EscExclusionReason {
    FieldIssuerOutOfScope,
}

impl EscExclusionReason {
    pub(crate) const fn label(self) -> &'static str {
        match self {
            Self::FieldIssuerOutOfScope => "field-issuer-out-of-scope",
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct EscExcludedSite {
    pub(crate) key: EscCopySiteKey,
    pub(crate) fn_did: LocalDefId,
    pub(crate) lhs: SlotRef,
    pub(crate) rhs: SlotRef,
    pub(crate) reason: EscExclusionReason,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct EscMinimalSelection {
    pub(crate) sites: Vec<EscRuntimeSite>,
    pub(crate) excluded_sites: Vec<EscExcludedSite>,
    pub(crate) loans: SelectedCopyLendLoans,
    demotion_exemptions: FxHashMap<LocalDefId, FxHashSet<(Local, Local)>>,
    presentations: FxHashMap<(LocalDefId, SelectedCopyLendLoan), EscPresentation>,
}

impl EscMinimalSelection {
    pub(crate) fn cross_stage_counts(&self) -> (usize, usize, usize, usize) {
        let selected = self.sites.len();
        let exemptions = self
            .demotion_exemptions
            .values()
            .map(FxHashSet::len)
            .sum::<usize>();
        let extensions = self.loans.values().map(FxHashSet::len).sum::<usize>();
        let receipt_rows = self.sites.len();
        assert_eq!(
            (selected, selected, selected),
            (exemptions, extensions, receipt_rows),
            "② effective selection must feed every downstream consumer one-to-one"
        );
        (selected, exemptions, extensions, receipt_rows)
    }
}

#[derive(Clone, Copy, Debug)]
struct EscPresentation {
    source: SlotRef,
    source_owner: ProvenanceOwner,
    destination_owner: ProvenanceOwner,
}

#[derive(Clone, Debug)]
struct EscScope {
    presentations: FxHashMap<(LocalDefId, SelectedCopyLendLoan), EscPresentation>,
    demotion_exemptions: FxHashMap<LocalDefId, FxHashSet<(Local, Local)>>,
}

thread_local! {
    static EFFECTIVE_SELECTION: RefCell<Option<EscScope>> = const { RefCell::new(None) };
}

pub(crate) fn with_presentations<T>(selection: &EscMinimalSelection, f: impl FnOnce() -> T) -> T {
    struct Restore(Option<EscScope>);
    impl Drop for Restore {
        fn drop(&mut self) {
            EFFECTIVE_SELECTION.with(|selection| {
                *selection.borrow_mut() = self.0.take();
            });
        }
    }
    selection.cross_stage_counts();
    let scope = EscScope {
        presentations: selection.presentations.clone(),
        demotion_exemptions: selection.demotion_exemptions.clone(),
    };
    let previous = EFFECTIVE_SELECTION.with(|selection| selection.replace(Some(scope)));
    let _restore = Restore(previous);
    f()
}

pub(crate) fn presentation_for(
    fn_did: LocalDefId,
    loan: &SelectedCopyLendLoan,
) -> Option<(ProvenanceOwner, ProvenanceOwner)> {
    EFFECTIVE_SELECTION.with(|selection| {
        selection
            .borrow()
            .as_ref()
            .and_then(|selection| selection.presentations.get(&(fn_did, loan.clone())))
            .map(|presentation| (presentation.source_owner, presentation.destination_owner))
    })
}

pub(crate) fn demotion_exemption(loan: &SelectedCopyLendLoan) -> (Local, Local) {
    let BorrowerKind::Assign {
        owner: OwnerKey::Local(borrower),
    } = loan.borrower
    else {
        panic!(
            "② feeder borrower must be a local temp, got {:?}",
            loan.borrower
        )
    };
    (Local::from_u32(borrower), loan.borrowed.local)
}

pub(crate) fn demotion_exemptions_for(
    fn_did: LocalDefId,
    loans: &FxHashSet<SelectedCopyLendLoan>,
) -> FxHashSet<(Local, Local)> {
    if loans.is_empty() {
        return FxHashSet::default();
    }
    EFFECTIVE_SELECTION.with(|selection| {
        let selection = selection.borrow();
        let selection = selection
            .as_ref()
            .expect("② pruning exemptions require the effective-selection scope");
        let registered = selection
            .demotion_exemptions
            .get(&fn_did)
            .cloned()
            .unwrap_or_default();
        let active = loans
            .iter()
            .map(demotion_exemption)
            .collect::<FxHashSet<_>>();
        assert_eq!(
            active.len(),
            loans.len(),
            "② active loan identities must map one-to-one to pruning exemptions"
        );
        assert!(
            active.is_subset(&registered),
            "② active pruning exemption escaped the effective selection"
        );
        active
    })
}

/// Select exactly the escaped loans whose resolved source is still `Ref` in this validation
/// round. Addendum 61's source demotion is the ② class's kill switch; the allowlist identity stays
/// fixed, but a non-Ref source must not carry CopyLend invalidation or exit-liveness semantics into
/// the next replay.
pub(crate) fn active_loans_for_model(
    escaped: &SelectedCopyLendLoans,
    model: &FxHashMap<SlotRef, SlotKind>,
) -> SelectedCopyLendLoans {
    EFFECTIVE_SELECTION.with(|selection| {
        let selection = selection.borrow();
        let selection = selection
            .as_ref()
            .expect("② active-loan filtering requires the construction presentation scope");
        let mut active = SelectedCopyLendLoans::default();
        let mut visited = 0;
        for (&fn_did, loans) in escaped {
            for loan in loans {
                let presentation = selection
                    .presentations
                    .get(&(fn_did, loan.clone()))
                    .expect("escaped loan missing exact presentation row");
                visited += 1;
                if model.get(&presentation.source) == Some(&SlotKind::Ref) {
                    assert!(
                        active.entry(fn_did).or_default().insert(loan.clone()),
                        "duplicate active escaped loan"
                    );
                }
            }
        }
        assert_eq!(
            visited,
            escaped.values().map(FxHashSet::len).sum::<usize>(),
            "② active-loan filter must visit every escaped identity exactly once"
        );
        assert!(
            active.values().map(FxHashSet::len).sum::<usize>()
                <= selection
                    .demotion_exemptions
                    .values()
                    .map(FxHashSet::len)
                    .sum::<usize>(),
            "② active-loan class exceeded the effective selection"
        );
        active
    })
}

#[cfg(test)]
thread_local! {
    static FIXTURE_SELECTION: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

#[cfg(test)]
pub(crate) fn with_fixture_selection<T>(f: impl FnOnce() -> T) -> T {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            FIXTURE_SELECTION.with(|enabled| enabled.set(self.0));
        }
    }
    let previous = FIXTURE_SELECTION.with(|enabled| enabled.replace(true));
    let _restore = Restore(previous);
    f()
}

fn fixture_selection_enabled() -> bool {
    #[cfg(test)]
    {
        return FIXTURE_SELECTION.with(std::cell::Cell::get);
    }
    #[cfg(not(test))]
    false
}

#[derive(Clone, Debug)]
struct Site {
    function: String,
    fn_did: LocalDefId,
    location: MirLocationKey,
    loan_location: MirLocationKey,
    loan_borrowed: PlaceKey,
    lhs: SlotRef,
    rhs: SlotRef,
    borrower: BorrowerKind,
    resolved_origin_slot: String,
    destination_place: String,
    escaping: bool,
    resolved_origin: bool,
    live_after_syntactic: bool,
    live_after: bool,
    selected: bool,
}

fn copy_form<'tcx>(rvalue: &Rvalue<'tcx>) -> Option<Place<'tcx>> {
    match rvalue {
        Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
        | Rvalue::Cast(_, Operand::Copy(place) | Operand::Move(place), _)
        | Rvalue::CopyForDeref(place) => Some(*place),
        _ => None,
    }
}

fn chase_origin<'tcx>(
    mut place: Place<'tcx>,
    temp_defs: &FxHashMap<Local, TempDef<'tcx>>,
) -> Place<'tcx> {
    for _ in 0..ORIGIN_CHASE_LIMIT {
        if !place.projection.is_empty() {
            break;
        }
        let Some(next) = temp_defs
            .get(&place.local)
            .map(|definition| definition.source)
        else {
            break;
        };
        if next == place {
            break;
        }
        place = next;
    }
    place
}

#[derive(Clone, Copy)]
struct TempDef<'tcx> {
    source: Place<'tcx>,
    location: Location,
}

fn escaping(body: &Body<'_>, destination: Place<'_>) -> bool {
    destination.local == RETURN_PLACE
        || destination.local.index() >= 1
            && destination.local.index() <= body.arg_count
            && destination
                .projection
                .iter()
                .any(|projection| matches!(projection, PlaceElem::Deref))
}

fn slot_ref(fn_did: LocalDefId, resolved: ResolvedSlot) -> SlotRef {
    match resolved {
        ResolvedSlot::Local(slot) => SlotRef::Local(fn_did, slot),
        ResolvedSlot::Field(slot) => SlotRef::Field(slot),
    }
}

fn slot_key(tcx: TyCtxt<'_>, slots: &CrateSlots, slot: SlotRef) -> String {
    match slot {
        SlotRef::Local(fn_did, slot) => {
            let slot = slots.fn_local_slots[&fn_did].slot(slot);
            let SlotOwner::Local(local) = slot.owner else {
                unreachable!("function-local universe contains field owner")
            };
            local_key(tcx, fn_did, local.index(), slot.depth)
        }
        SlotRef::Field(slot) => {
            let slot = slots.field_slots.slot(slot);
            let SlotOwner::Field(field) = slot.owner else {
                unreachable!("field universe contains local owner")
            };
            field_key(tcx, field.struct_did, field.field_index, slot.depth)
        }
    }
}

fn owner_key(slots: &CrateSlots, slot: SlotRef) -> OwnerKey {
    let owner = match slot {
        SlotRef::Local(fn_did, slot) => slots.fn_local_slots[&fn_did].slot(slot).owner,
        SlotRef::Field(slot) => slots.field_slots.slot(slot).owner,
    };
    match owner {
        SlotOwner::Local(local) => OwnerKey::Local(local.as_u32()),
        SlotOwner::Field(field) => OwnerKey::Field {
            struct_did: field.struct_did.local_def_index.as_u32(),
            field_index: field.field_index,
        },
    }
}

fn presentation_owner(slots: &CrateSlots, slot: SlotRef) -> ProvenanceOwner {
    let owner = match slot {
        SlotRef::Local(fn_did, slot) => slots.fn_local_slots[&fn_did].slot(slot).owner,
        SlotRef::Field(slot) => slots.field_slots.slot(slot).owner,
    };
    match owner {
        SlotOwner::Local(local) => ProvenanceOwner::Local(local),
        SlotOwner::Field(field) => ProvenanceOwner::Field(BorrowFieldSlot {
            struct_did: field.struct_did,
            field_index: field.field_index,
        }),
    }
}

fn collect_sites(
    program: &RustProgram<'_>,
    slots: &CrateSlots,
    restrict_to_allowlist_functions: bool,
) -> Vec<Site> {
    let allowed_functions = artifact_keys()
        .iter()
        .map(|key| key.function)
        .collect::<FxHashSet<_>>();
    let mut sites = Vec::new();

    for &fn_did in &program.functions {
        let function = program.tcx.def_path_str(fn_did.to_def_id());
        if restrict_to_allowlist_functions && !allowed_functions.contains(function.as_str()) {
            continue;
        }
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(fn_did)
            .borrow();
        let eliminable = eliminable_temporaries(&body);
        let mut temp_defs = FxHashMap::default();
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for (statement_index, statement) in data.statements.iter().enumerate() {
                let StatementKind::Assign(assign) = &statement.kind else {
                    continue;
                };
                let Some(destination) = assign.0.as_local() else {
                    continue;
                };
                if eliminable.contains(destination)
                    && let Some(source) = copy_form(&assign.1)
                    && source.ty(&body.local_decls, program.tcx).ty.is_any_ptr()
                {
                    temp_defs.insert(
                        destination,
                        TempDef {
                            source,
                            location: Location {
                                block,
                                statement_index,
                            },
                        },
                    );
                }
            }
        }

        struct Pending<'tcx> {
            location: Location,
            source: Place<'tcx>,
            destination: Place<'tcx>,
            origin: Place<'tcx>,
            lhs: SlotRef,
            rhs: SlotRef,
            loan_location: Location,
            loan_source: Place<'tcx>,
            loan_borrower: BorrowerKind,
        }
        let mut pending = Vec::new();
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for (statement_index, statement) in data.statements.iter().enumerate() {
                let StatementKind::Assign(assign) = &statement.kind else {
                    continue;
                };
                let Some(source) = copy_form(&assign.1) else {
                    continue;
                };
                if !source.ty(&body.local_decls, program.tcx).ty.is_any_ptr() {
                    continue;
                }
                let origin = chase_origin(source, &temp_defs);
                let (Some(lhs), Some(rhs)) = (
                    resolve_place(slots, fn_did, &body, assign.0, 0, None),
                    resolve_place(slots, fn_did, &body, origin, 0, None),
                ) else {
                    continue;
                };
                let lhs = slot_ref(fn_did, lhs);
                let (loan_location, loan_source, loan_borrower) = source
                    .as_local()
                    .and_then(|local| temp_defs.get(&local).map(|definition| (local, *definition)))
                    .map(|(borrower, definition)| {
                        (
                            definition.location,
                            definition.source,
                            BorrowerKind::Assign {
                                owner: OwnerKey::Local(borrower.as_u32()),
                            },
                        )
                    })
                    .unwrap_or_else(|| {
                        (
                            Location {
                                block,
                                statement_index,
                            },
                            source,
                            BorrowerKind::Assign {
                                owner: owner_key(slots, lhs),
                            },
                        )
                    });
                pending.push(Pending {
                    location: Location {
                        block,
                        statement_index,
                    },
                    source,
                    destination: assign.0,
                    origin,
                    lhs,
                    rhs: slot_ref(fn_did, rhs),
                    loan_location,
                    loan_source,
                    loan_borrower,
                });
            }
        }
        if pending.is_empty() {
            continue;
        }

        let mut liveness = MaybeLiveLocals
            .iterate_to_fixpoint(program.tcx, &body, None)
            .into_results_cursor(&body);
        for row in pending {
            liveness.seek_before_primary_effect(row.location);
            let live = liveness.get();
            let live_after = live.contains(row.origin.local);
            let live_after_syntactic = live.contains(row.source.local);
            let is_escaping = escaping(&body, row.destination);
            let origin_key = slot_key(program.tcx, slots, row.rhs);
            let destination_place = format!("{:?}", row.destination);
            let artifact = artifact_keys().iter().find(|key| {
                key.function == function
                    && key.location
                        == MirLocationKey::new(
                            row.location.block.as_u32(),
                            row.location.statement_index,
                        )
                    && key.resolved_origin_slot == origin_key
                    && key.destination_place == destination_place
            });
            let selected = is_escaping
                && live_after
                && if restrict_to_allowlist_functions {
                    artifact.is_some()
                } else {
                    true
                };
            sites.push(Site {
                function: function.clone(),
                fn_did,
                location: MirLocationKey::new(
                    row.location.block.as_u32(),
                    row.location.statement_index,
                ),
                loan_location: MirLocationKey::new(
                    row.loan_location.block.as_u32(),
                    row.loan_location.statement_index,
                ),
                loan_borrowed: PlaceKey::from_place(
                    row.loan_source
                        .project_deeper(&[PlaceElem::Deref], program.tcx),
                ),
                lhs: row.lhs,
                rhs: row.rhs,
                borrower: row.loan_borrower,
                resolved_origin_slot: origin_key,
                destination_place,
                escaping: is_escaping,
                resolved_origin: row.origin != row.source,
                live_after_syntactic,
                live_after,
                selected,
            });
        }
    }
    sites
}

pub(crate) fn select(program: &RustProgram<'_>, slots: &CrateSlots) -> EscMinimalSelection {
    let fixture_selection = fixture_selection_enabled();
    let rows = collect_sites(program, slots, !fixture_selection);
    let present_functions = program
        .functions
        .iter()
        .map(|did| program.tcx.def_path_str(did.to_def_id()))
        .collect::<FxHashSet<_>>();
    let expected = if fixture_selection {
        Vec::new()
    } else {
        artifact_keys()
            .iter()
            .filter(|key| present_functions.contains(key.function))
            .collect::<Vec<_>>()
    };
    let selected = rows.iter().filter(|row| row.selected).collect::<Vec<_>>();
    if !fixture_selection {
        assert_eq!(
            selected.len(),
            expected.len(),
            "②-minimal exact allowlist did not join one-to-one in this crate"
        );
    }

    let mut answer = EscMinimalSelection::default();
    for row in selected {
        let artifact = (!fixture_selection).then(|| {
            artifact_keys()
                .iter()
                .find(|key| {
                    key.function == row.function
                        && key.location == row.location
                        && key.resolved_origin_slot == row.resolved_origin_slot
                        && key.destination_place == row.destination_place
                })
                .expect("selected row has artifact key")
        });
        let key = EscCopySiteKey {
            program: artifact.map_or("fixture", |key| key.program).to_owned(),
            function: row.function.clone(),
            location: row.location,
            resolved_origin_slot: row.resolved_origin_slot.clone(),
            destination_place: row.destination_place.clone(),
        };
        if matches!(row.rhs, SlotRef::Field(_)) {
            answer.excluded_sites.push(EscExcludedSite {
                key,
                fn_did: row.fn_did,
                lhs: row.lhs,
                rhs: row.rhs,
                reason: EscExclusionReason::FieldIssuerOutOfScope,
            });
            continue;
        }
        let loan = SelectedCopyLendLoan {
            location: row.loan_location,
            borrowed: row.loan_borrowed.clone(),
            borrower: row.borrower,
        };
        assert!(
            answer
                .loans
                .entry(row.fn_did)
                .or_default()
                .insert(loan.clone()),
            "duplicate ②-minimal selected loan"
        );
        assert!(
            answer
                .demotion_exemptions
                .entry(row.fn_did)
                .or_default()
                .insert(demotion_exemption(&loan)),
            "duplicate ②-minimal pruning exemption"
        );
        assert!(
            answer
                .presentations
                .insert(
                    (row.fn_did, loan.clone()),
                    EscPresentation {
                        source: row.rhs,
                        source_owner: presentation_owner(slots, row.rhs),
                        destination_owner: presentation_owner(slots, row.lhs),
                    },
                )
                .is_none(),
            "duplicate ②-minimal presentation identity"
        );
        answer.sites.push(EscRuntimeSite {
            key,
            fn_did: row.fn_did,
            lhs: row.lhs,
            rhs: row.rhs,
            loan,
        });
    }
    if !fixture_selection {
        let expected_field_issuers = expected
            .iter()
            .filter(|key| key.resolved_origin_slot.contains("::field"))
            .count();
        assert_eq!(
            answer.sites.len() + answer.excluded_sites.len(),
            expected.len(),
            "② allowlist keys must partition into selected plus typed-excluded"
        );
        assert_eq!(
            answer.excluded_sites.len(),
            expected_field_issuers,
            "② field-issuer exclusions must match the exact joined allowlist rows"
        );
    }
    answer.cross_stage_counts();
    answer
}

#[cfg(test)]
fn fixture_sites(code: &str) -> Vec<Site> {
    let mut answer = None;
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        use rustc_hir::{ItemKind, OwnerNode};
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
        let program = RustProgram {
            tcx,
            functions,
            structs,
        };
        let slots = CrateSlots::build(&program);
        answer = Some(collect_sites(&program, &slots, false));
    })
    .unwrap_or_else(|error| error.raise());
    answer.expect("fixture compiler callback")
}

#[cfg(test)]
mod tests {
    use rustc_middle::mir::Local;

    use super::{EscExclusionReason, artifact_keys, demotion_exemption, fixture_sites};
    use crate::analyses::borrow_ownership::{
        coherence::SelectedCopyLendLoan,
        export::{BorrowerKind, OwnerKey, PlaceKey},
        l2::MirLocationKey,
    };

    const ESC_W1: &str = r#"
unsafe fn save(out: *mut *mut i32, x: *mut i32) { *out = x; *x = 1; }
unsafe fn caller() -> i32 {
    let mut cell = 0i32;
    let mut slot: *mut i32 = core::ptr::null_mut();
    save(&raw mut slot, &raw mut cell);
    *slot
}
"#;

    const NO_ESCAPE: &str = r#"
unsafe fn save(out: *mut *mut i32, x: *mut i32) { let _ = out; *x = 1; }
unsafe fn caller() -> i32 {
    let mut cell = 0i32;
    let mut slot: *mut i32 = core::ptr::null_mut();
    save(&raw mut slot, &raw mut cell);
    *slot
}
"#;

    const DEAD_AFTER: &str = r#"
unsafe fn save(out: *mut *mut i32, x: *mut i32) { *out = x; }
unsafe fn caller() -> i32 {
    let mut cell = 0i32;
    let mut slot: *mut i32 = core::ptr::null_mut();
    save(&raw mut slot, &raw mut cell);
    *slot
}
"#;

    #[test]
    fn field_issuer_allowlist_residual_is_exact_and_typed() {
        let rows = artifact_keys()
            .iter()
            .filter(|key| key.program == "brotli" && key.resolved_origin_slot.contains("::field"))
            .collect::<Vec<_>>();
        assert_eq!(rows.len(), 3);
        assert_eq!(
            EscExclusionReason::FieldIssuerOutOfScope.label(),
            "field-issuer-out-of-scope"
        );
    }

    #[test]
    fn one_effective_loan_has_one_exact_pruning_exemption() {
        let loan = SelectedCopyLendLoan {
            location: MirLocationKey::new(3, 7),
            borrowed: PlaceKey {
                local: Local::from_u32(9),
                proj: Vec::new(),
            },
            borrower: BorrowerKind::Assign {
                owner: OwnerKey::Local(5),
            },
        };
        assert_eq!(
            demotion_exemption(&loan),
            (Local::from_u32(5), Local::from_u32(9))
        );
    }

    #[test]
    fn escgap_selector_nonvacuity_escw1_copy_is_selected() {
        let rows = fixture_sites(ESC_W1);
        let selected = rows.iter().filter(|row| row.selected).collect::<Vec<_>>();
        assert_eq!(selected.len(), 1);
        let row = selected[0];
        assert!(row.escaping);
        assert!(row.resolved_origin);
        assert!(!row.live_after_syntactic);
        assert!(row.live_after);
    }

    #[test]
    fn escgap_selector_escape_column_discriminates() {
        assert!(
            fixture_sites(NO_ESCAPE)
                .iter()
                .all(|row| !row.selected && !row.escaping)
        );
    }

    #[test]
    fn escgap_selector_liveness_column_discriminates() {
        let rows = fixture_sites(DEAD_AFTER);
        let escaping = rows.iter().filter(|row| row.escaping).collect::<Vec<_>>();
        assert_eq!(escaping.len(), 1);
        assert!(!escaping[0].live_after);
        assert!(!escaping[0].selected);
    }
}
