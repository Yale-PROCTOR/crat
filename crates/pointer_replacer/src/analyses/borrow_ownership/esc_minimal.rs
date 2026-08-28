//! ESC-GAP ②-minimal exact-site selector.

use std::sync::OnceLock;

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
    export::{BorrowerKind, OwnerKey, PlaceKey},
    l2::MirLocationKey,
    resolve::{ResolvedSlot, resolve_place},
    slot_key::{field_key, local_key},
    slots::SlotOwner,
    solver::SlotRef,
};
use crate::{
    analyses::{
        liveness::MaybeLiveLocals, output_params::eliminable_temporaries::eliminable_temporaries,
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

#[derive(Clone, Debug, Default)]
pub(crate) struct EscMinimalSelection {
    pub(crate) sites: Vec<EscRuntimeSite>,
    pub(crate) loans: SelectedCopyLendLoans,
}

#[derive(Clone, Debug)]
struct Site {
    function: String,
    fn_did: LocalDefId,
    location: MirLocationKey,
    syntactic_source: PlaceKey,
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
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
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
                    temp_defs.insert(destination, source);
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
                pending.push(Pending {
                    location: Location {
                        block,
                        statement_index,
                    },
                    source,
                    destination: assign.0,
                    origin,
                    lhs: slot_ref(fn_did, lhs),
                    rhs: slot_ref(fn_did, rhs),
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
                syntactic_source: PlaceKey::from_place(
                    row.source.project_deeper(&[PlaceElem::Deref], program.tcx),
                ),
                lhs: row.lhs,
                rhs: row.rhs,
                borrower: BorrowerKind::Assign {
                    owner: owner_key(slots, row.lhs),
                },
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
    let rows = collect_sites(program, slots, true);
    let present_functions = program
        .functions
        .iter()
        .map(|did| program.tcx.def_path_str(did.to_def_id()))
        .collect::<FxHashSet<_>>();
    let expected = artifact_keys()
        .iter()
        .filter(|key| present_functions.contains(key.function))
        .collect::<Vec<_>>();
    let selected = rows.iter().filter(|row| row.selected).collect::<Vec<_>>();
    assert_eq!(
        selected.len(),
        expected.len(),
        "②-minimal exact allowlist did not join one-to-one in this crate"
    );

    let mut answer = EscMinimalSelection::default();
    for row in selected {
        let artifact = artifact_keys()
            .iter()
            .find(|key| {
                key.function == row.function
                    && key.location == row.location
                    && key.resolved_origin_slot == row.resolved_origin_slot
                    && key.destination_place == row.destination_place
            })
            .expect("selected row has artifact key");
        let loan = SelectedCopyLendLoan {
            location: row.location,
            borrowed: row.syntactic_source.clone(),
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
        answer.sites.push(EscRuntimeSite {
            key: EscCopySiteKey {
                program: artifact.program.to_owned(),
                function: row.function.clone(),
                location: row.location,
                resolved_origin_slot: row.resolved_origin_slot.clone(),
                destination_place: row.destination_place.clone(),
            },
            fn_did: row.fn_did,
            lhs: row.lhs,
            rhs: row.rhs,
            loan,
        });
    }
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
    use super::fixture_sites;

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
