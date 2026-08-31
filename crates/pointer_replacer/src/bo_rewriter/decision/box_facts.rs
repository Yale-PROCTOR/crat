//! Derive-on-load ownership facts used by Box emission.
//!
//! The production implementation is intentionally RED-first.  These tests pin
//! the conservative concrete replay before the frozen ownership emitter is
//! connected to it.

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::IndexVec;
use rustc_middle::mir::{Body, Local, Location, Operand, Rvalue, StatementKind, TerminatorKind};
use rustc_span::{Span, def_id::LocalDefId};
use rustc_type_ir::TyKind::FnDef;
use sha2::{Digest, Sha256};

use crate::{
    analyses::{
        borrow_ownership::{
            SlotKind,
            boundary_table::{self, Matcher, Role},
            crate_slots::CrateSlots,
            solver::SlotRef,
            ssa::constraint::Var,
        },
        output_params::eliminable_temporaries::eliminable_temporaries,
    },
    utils::rustc::RustProgram,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FactValue {
    MustOwn,
    NotOwn,
    Unknown,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BoxScopeFailure {
    PointerDepth,
    ParameterHeld,
}

pub(crate) fn box_scope(is_parameter: bool, pointer_depth: u8) -> Result<(), BoxScopeFailure> {
    if pointer_depth != 1 {
        return Err(BoxScopeFailure::PointerDepth);
    }
    if is_parameter {
        return Err(BoxScopeFailure::ParameterHeld);
    }
    Ok(())
}

pub(crate) fn scalar_initializer_supported(normalized: &str) -> bool {
    matches!(
        normalized,
        "u8" | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "f32"
            | "f64"
    )
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum RecordedEquation {
    Linear { left: Var, right: Var, result: Var },
    Assume { var: Var, value: bool },
    Equal { left: Var, right: Var },
    LessEqual { left: Var, right: Var },
    EqMin { result: Var, left: Var, right: Var },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum EndpointStatus {
    Active,
    InactiveSlot,
    InactiveVar,
    Unknown,
}

impl EndpointStatus {
    pub(crate) fn key(self) -> &'static str {
        match self {
            EndpointStatus::Active => "active",
            EndpointStatus::InactiveSlot => "inactive-slot",
            EndpointStatus::InactiveVar => "inactive-var",
            EndpointStatus::Unknown => "unknown",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum EndpointRole {
    Source,
    Sink,
}

impl EndpointRole {
    fn key(self) -> &'static str {
        match self {
            EndpointRole::Source => "Source",
            EndpointRole::Sink => "Sink",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct VersionSite {
    function_path: String,
    local: Local,
    location: LocationKey,
    use_var: Option<Var>,
    def_var: Option<Var>,
    relation: &'static str,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct LocationKey {
    pub(crate) block: u32,
    pub(crate) statement: usize,
}

impl From<Location> for LocationKey {
    fn from(location: Location) -> Self {
        Self {
            block: location.block.as_u32(),
            statement: location.statement_index,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct EndpointFact {
    pub(crate) role: EndpointRole,
    pub(crate) function_path: String,
    pub(crate) location: LocationKey,
    pub(crate) callee: String,
    pub(crate) var: Var,
    pub(crate) slot: String,
    pub(crate) final_kind: Option<SlotKind>,
    pub(crate) value: FactValue,
    pub(crate) status: EndpointStatus,
    pub(crate) unknown_reason: Option<String>,
    slot_ref: Option<SlotRef>,
    span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SinkCarrierDef {
    Copy(Local),
    Multiple,
    NonCopy,
    Projected,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SinkCarrierReason {
    MultiDef,
    NonCopyDef,
    ProjectionBase,
    MissingDef,
    MissingVersionSite,
    Cycle,
}

impl SinkCarrierReason {
    fn key(self) -> &'static str {
        match self {
            SinkCarrierReason::MultiDef => "sink-carrier-multi-def",
            SinkCarrierReason::NonCopyDef => "sink-carrier-non-copy-def",
            SinkCarrierReason::ProjectionBase => "sink-carrier-projection-base",
            SinkCarrierReason::MissingDef => "sink-carrier-missing-def",
            SinkCarrierReason::MissingVersionSite => "sink-carrier-version-site-missing",
            SinkCarrierReason::Cycle => "sink-carrier-cycle",
        }
    }
}

fn resolve_sink_carrier(
    operand: Local,
    is_eliminable_temp: bool,
    definition: Option<SinkCarrierDef>,
) -> Result<Local, SinkCarrierReason> {
    if !is_eliminable_temp {
        return Ok(operand);
    }
    match definition {
        Some(SinkCarrierDef::Copy(carrier)) => Ok(carrier),
        Some(SinkCarrierDef::Multiple) => Err(SinkCarrierReason::MultiDef),
        Some(SinkCarrierDef::NonCopy) => Err(SinkCarrierReason::NonCopyDef),
        Some(SinkCarrierDef::Projected) => Err(SinkCarrierReason::ProjectionBase),
        None => Err(SinkCarrierReason::MissingDef),
    }
}

pub(crate) fn classify_endpoint(value: FactValue, slot: SlotKind) -> EndpointStatus {
    match (value, slot) {
        (FactValue::MustOwn, SlotKind::Owning) => EndpointStatus::Active,
        (FactValue::MustOwn, _) => EndpointStatus::InactiveSlot,
        (FactValue::NotOwn, _) => EndpointStatus::InactiveVar,
        (FactValue::Unknown, _) => EndpointStatus::Unknown,
    }
}

fn assign(
    values: &mut IndexVec<Var, FactValue>,
    var: Var,
    value: FactValue,
) -> Result<bool, String> {
    if value == FactValue::Unknown {
        return Ok(false);
    }
    match values[var] {
        FactValue::Unknown => {
            values[var] = value;
            Ok(true)
        }
        current if current == value => Ok(false),
        current => Err(format!(
            "contradictory ownership facts for {var:?}: {current:?} versus {value:?}"
        )),
    }
}

fn replay_one(
    values: &mut IndexVec<Var, FactValue>,
    equation: &RecordedEquation,
) -> Result<bool, String> {
    use FactValue::{MustOwn, NotOwn, Unknown};
    let mut changed = false;
    match *equation {
        RecordedEquation::Assume { var, value } => {
            changed |= assign(values, var, if value { MustOwn } else { NotOwn })?;
        }
        RecordedEquation::Equal { left, right } => match (values[left], values[right]) {
            (Unknown, value) => changed |= assign(values, left, value)?,
            (value, Unknown) => changed |= assign(values, right, value)?,
            (left_value, right_value) if left_value != right_value => {
                return Err(format!(
                    "equal equation disagrees for {left:?}/{right:?}: {left_value:?}/{right_value:?}"
                ));
            }
            _ => {}
        },
        RecordedEquation::LessEqual { left, right } => {
            if values[left] == MustOwn {
                changed |= assign(values, right, MustOwn)?;
            }
            if values[right] == NotOwn {
                changed |= assign(values, left, NotOwn)?;
            }
        }
        RecordedEquation::EqMin {
            result,
            left,
            right,
        } => {
            if values[result] == MustOwn {
                changed |= assign(values, left, MustOwn)?;
                changed |= assign(values, right, MustOwn)?;
            }
            if values[left] == NotOwn || values[right] == NotOwn {
                changed |= assign(values, result, NotOwn)?;
            }
            if values[left] == MustOwn && values[right] == MustOwn {
                changed |= assign(values, result, MustOwn)?;
            }
        }
        RecordedEquation::Linear {
            left,
            right,
            result,
        } => {
            if values[left] == MustOwn {
                changed |= assign(values, right, NotOwn)?;
                changed |= assign(values, result, MustOwn)?;
            }
            if values[right] == MustOwn {
                changed |= assign(values, left, NotOwn)?;
                changed |= assign(values, result, MustOwn)?;
            }
            if values[result] == NotOwn {
                changed |= assign(values, left, NotOwn)?;
                changed |= assign(values, right, NotOwn)?;
            }
            if values[left] == NotOwn && values[right] == NotOwn {
                changed |= assign(values, result, NotOwn)?;
            }
            if values[result] == MustOwn && values[left] == NotOwn {
                changed |= assign(values, right, MustOwn)?;
            }
            if values[result] == MustOwn && values[right] == NotOwn {
                changed |= assign(values, left, MustOwn)?;
            }
        }
    }
    Ok(changed)
}

pub(crate) fn replay_values(
    mut values: IndexVec<Var, FactValue>,
    equations: &[RecordedEquation],
) -> Result<IndexVec<Var, FactValue>, String> {
    loop {
        let mut changed = false;
        for equation in equations {
            changed |= replay_one(&mut values, equation)?;
        }
        if !changed {
            return Ok(values);
        }
    }
}

pub(crate) fn render_equations(equations: &[RecordedEquation]) -> String {
    let mut rows = equations
        .iter()
        .map(|equation| match *equation {
            RecordedEquation::Linear {
                left,
                right,
                result,
            } => format!(
                "linear\t{}\t{}\t{}",
                left.as_u32(),
                right.as_u32(),
                result.as_u32()
            ),
            RecordedEquation::Assume { var, value } => {
                format!("assume\t{}\t{}", var.as_u32(), u8::from(value))
            }
            RecordedEquation::Equal { left, right } => {
                format!("equal\t{}\t{}", left.as_u32(), right.as_u32())
            }
            RecordedEquation::LessEqual { left, right } => {
                format!("less-equal\t{}\t{}", left.as_u32(), right.as_u32())
            }
            RecordedEquation::EqMin {
                result,
                left,
                right,
            } => format!(
                "eq-min\t{}\t{}\t{}",
                result.as_u32(),
                left.as_u32(),
                right.as_u32()
            ),
        })
        .collect::<Vec<_>>();
    rows.sort();
    rows.join("\n") + "\n"
}

#[derive(Clone, Debug)]
struct EndpointCandidate {
    role: EndpointRole,
    function_path: String,
    location: LocationKey,
    callee: String,
    var: Var,
    slot: CandidateSlot,
    span: Span,
}

#[derive(Clone, Copy, Debug)]
enum CandidateSlot {
    Resolved(SlotRef),
    Undeterminable {
        direct: SlotRef,
        reason: SinkCarrierReason,
    },
}

#[derive(Clone, Copy, Debug)]
struct CarrierPresentation {
    carrier: Local,
    r#use: Var,
    def: Var,
    slot: SlotRef,
}

fn resolve_sink_presentation(
    operand: Local,
    direct: CarrierPresentation,
    eliminable: &rustc_index::bit_set::MixedBitSet<Local>,
    definitions: &IndexVec<Local, Option<SinkCarrierDef>>,
    presentations: &FxHashMap<Local, CarrierPresentation>,
) -> Result<CarrierPresentation, SinkCarrierReason> {
    let mut current = operand;
    let mut resolved = direct;
    let mut seen = FxHashSet::default();
    while eliminable.contains(current) {
        if !seen.insert(current) {
            return Err(SinkCarrierReason::Cycle);
        }
        let carrier = resolve_sink_carrier(current, true, definitions[current])?;
        let presentation = presentations
            .get(&current)
            .copied()
            .filter(|presentation| presentation.carrier == carrier)
            .ok_or(SinkCarrierReason::MissingVersionSite)?;
        resolved = presentation;
        current = carrier;
    }
    Ok(resolved)
}

fn record_sink_definition(
    definitions: &mut IndexVec<Local, Option<SinkCarrierDef>>,
    local: Local,
    definition: SinkCarrierDef,
) {
    definitions[local] = Some(match definitions[local] {
        None => definition,
        Some(_) => SinkCarrierDef::Multiple,
    });
}

fn sink_carrier_definitions(body: &Body<'_>) -> IndexVec<Local, Option<SinkCarrierDef>> {
    let mut definitions = IndexVec::from_elem_n(None, body.local_decls.len());
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let StatementKind::Assign(box (destination, rvalue)) = &statement.kind else {
                continue;
            };
            let definition = if destination.as_local().is_none() {
                SinkCarrierDef::Projected
            } else {
                match rvalue {
                    Rvalue::Use(Operand::Copy(source) | Operand::Move(source))
                    | Rvalue::Cast(_, Operand::Copy(source) | Operand::Move(source), _) => source
                        .as_local()
                        .map_or(SinkCarrierDef::Projected, SinkCarrierDef::Copy),
                    _ => SinkCarrierDef::NonCopy,
                }
            };
            record_sink_definition(&mut definitions, destination.local, definition);
        }
        if let Some(terminator) = &data.terminator
            && let TerminatorKind::Call { destination, .. } = &terminator.kind
        {
            let definition = if destination.as_local().is_some() {
                SinkCarrierDef::NonCopy
            } else {
                SinkCarrierDef::Projected
            };
            record_sink_definition(&mut definitions, destination.local, definition);
        }
    }
    definitions
}

struct MinimalWalk<'a, 'tcx> {
    program: &'a RustProgram<'tcx>,
    slots: &'a CrateSlots,
    model: &'a FxHashMap<SlotRef, SlotKind>,
    next_var: u32,
    equations: Vec<RecordedEquation>,
    version_sites: Vec<VersionSite>,
    candidates: Vec<EndpointCandidate>,
    var_slots: FxHashMap<Var, SlotRef>,
    move_edges: Vec<(SlotRef, SlotRef)>,
    field_held: FxHashSet<SlotRef>,
    boundary_held: FxHashSet<SlotRef>,
}

impl<'a, 'tcx> MinimalWalk<'a, 'tcx> {
    fn new(
        program: &'a RustProgram<'tcx>,
        slots: &'a CrateSlots,
        model: &'a FxHashMap<SlotRef, SlotKind>,
    ) -> Self {
        Self {
            program,
            slots,
            model,
            next_var: Var::MIN.as_u32(),
            equations: Vec::new(),
            version_sites: Vec::new(),
            candidates: Vec::new(),
            var_slots: FxHashMap::default(),
            move_edges: Vec::new(),
            field_held: FxHashSet::default(),
            boundary_held: FxHashSet::default(),
        }
    }

    fn new_var(&mut self, slot: SlotRef) -> Var {
        let var = Var::from_u32(self.next_var);
        self.next_var += 1;
        self.var_slots.insert(var, slot);
        var
    }

    fn slot_for_local(&self, fn_did: LocalDefId, local: Local) -> Option<SlotRef> {
        let slot = self
            .slots
            .fn_local_slots
            .get(&fn_did)?
            .slot_for_local_depth(local, 0)?;
        Some(SlotRef::Local(fn_did, slot))
    }

    fn consume(
        &mut self,
        fn_did: LocalDefId,
        function_path: &str,
        current: &mut FxHashMap<Local, Var>,
        local: Local,
        location: Location,
        relation: &'static str,
    ) -> Option<(Var, Var, SlotRef)> {
        let r#use = *current.get(&local)?;
        let slot = self.slot_for_local(fn_did, local)?;
        let def = self.new_var(slot);
        current.insert(local, def);
        self.version_sites.push(VersionSite {
            function_path: function_path.to_owned(),
            local,
            location: location.into(),
            use_var: Some(r#use),
            def_var: Some(def),
            relation,
        });
        Some((r#use, def, slot))
    }

    fn walk(mut self) -> Result<BoxOwnershipFacts, String> {
        let mut functions = self.program.functions.clone();
        functions.sort_unstable_by_key(|did| did.local_def_index.as_u32());
        for fn_did in functions {
            let body_ref = self
                .program
                .tcx
                .mir_drops_elaborated_and_const_checked(fn_did)
                .borrow();
            self.walk_body(fn_did, &body_ref)?;
        }
        self.finish()
    }

    fn walk_body(&mut self, fn_did: LocalDefId, body: &Body<'tcx>) -> Result<(), String> {
        let function_path = self.program.tcx.def_path_str(fn_did.to_def_id());
        let eliminable = eliminable_temporaries(body);
        let sink_definitions = sink_carrier_definitions(body);
        let mut transparent_argument_temps = FxHashSet::default();
        for data in body.basic_blocks.iter() {
            let Some(terminator) = data.terminator.as_ref() else {
                continue;
            };
            let TerminatorKind::Call { args, .. } = &terminator.kind else {
                continue;
            };
            for local in args
                .iter()
                .filter_map(|arg| arg.node.place())
                .filter_map(|place| place.as_local())
                .filter(|local| eliminable.contains(*local))
            {
                transparent_argument_temps.insert(local);
            }
        }
        let mut pending = transparent_argument_temps
            .iter()
            .copied()
            .collect::<Vec<_>>();
        while let Some(local) = pending.pop() {
            if let Some(SinkCarrierDef::Copy(carrier)) = sink_definitions[local]
                && eliminable.contains(carrier)
                && transparent_argument_temps.insert(carrier)
            {
                pending.push(carrier);
            }
        }
        let mut carrier_presentations = FxHashMap::<Local, CarrierPresentation>::default();
        let mut current = FxHashMap::<Local, Var>::default();
        for local in body.local_decls.indices() {
            if let Some(slot) = self.slot_for_local(fn_did, local) {
                let var = self.new_var(slot);
                current.insert(local, var);
            }
        }

        for (block, data) in body.basic_blocks.iter_enumerated() {
            for (statement_index, statement) in data.statements.iter().enumerate() {
                let location = Location {
                    block,
                    statement_index,
                };
                let StatementKind::Assign(box (lhs, rhs)) = &statement.kind else {
                    continue;
                };
                let rhs_operand = match rhs {
                    Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => Some(operand),
                    _ => None,
                };
                let rhs_local = rhs_operand
                    .and_then(Operand::place)
                    .and_then(|place| place.as_local());
                let Some(lhs_local) = lhs.as_local() else {
                    if let Some(rhs_local) = rhs_local
                        && let Some(slot) = self.slot_for_local(fn_did, rhs_local)
                    {
                        self.field_held.insert(slot);
                    }
                    continue;
                };
                if transparent_argument_temps.contains(&lhs_local) {
                    if let Some(rhs_local) = rhs_local
                        && let Some((rhs_use, rhs_def, rhs_slot)) = self.consume(
                            fn_did,
                            &function_path,
                            &mut current,
                            rhs_local,
                            location,
                            "sink-carrier-copy",
                        )
                    {
                        carrier_presentations.insert(
                            lhs_local,
                            CarrierPresentation {
                                carrier: rhs_local,
                                r#use: rhs_use,
                                def: rhs_def,
                                slot: rhs_slot,
                            },
                        );
                    }
                    continue;
                }
                let lhs_consume = self.consume(
                    fn_did,
                    &function_path,
                    &mut current,
                    lhs_local,
                    location,
                    "assignment-lhs",
                );
                let rhs_consume = rhs_local.and_then(|local| {
                    self.consume(
                        fn_did,
                        &function_path,
                        &mut current,
                        local,
                        location,
                        "assignment-rhs",
                    )
                });
                let Some((lhs_use, lhs_def, lhs_slot)) = lhs_consume else {
                    continue;
                };
                self.equations.push(RecordedEquation::Assume {
                    var: lhs_use,
                    value: false,
                });
                if let (Some(operand), Some((rhs_use, rhs_def, rhs_slot))) =
                    (rhs_operand, rhs_consume)
                {
                    self.move_edges.push((rhs_slot, lhs_slot));
                    if operand.is_move() {
                        self.equations.push(RecordedEquation::Equal {
                            left: lhs_def,
                            right: rhs_use,
                        });
                        self.equations.push(RecordedEquation::Assume {
                            var: rhs_def,
                            value: false,
                        });
                    } else {
                        self.equations.push(RecordedEquation::Linear {
                            left: lhs_def,
                            right: rhs_def,
                            result: rhs_use,
                        });
                    }
                }
            }

            let Some(terminator) = data.terminator.as_ref() else {
                continue;
            };
            let location = Location {
                block,
                statement_index: data.statements.len(),
            };
            let TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &terminator.kind
            else {
                continue;
            };
            let mut arg_consumes = Vec::with_capacity(args.len());
            for arg in args {
                let local = arg.node.place().and_then(|place| place.as_local());
                let consume = local.and_then(|local| {
                    self.consume(
                        fn_did,
                        &function_path,
                        &mut current,
                        local,
                        location,
                        "call-argument",
                    )
                });
                arg_consumes.push(local.zip(consume));
            }
            let destination = destination.as_local().and_then(|local| {
                self.consume(
                    fn_did,
                    &function_path,
                    &mut current,
                    local,
                    location,
                    "call-destination",
                )
            });

            let callee = foreign_callee_name(self.program, func);
            let roles = callee
                .as_deref()
                .and_then(|name| boundary_table::lookup(name, Matcher::ForeignC))
                .map(|entry| entry.roles)
                .unwrap_or(&[]);
            let is_source = roles.contains(&Role::Source);
            let is_sink = roles.contains(&Role::Sink);
            let is_flow_transfer = roles.contains(&Role::FlowTransfer);

            if is_flow_transfer
                && let Some((_, destination_def, _)) = destination
                && let Some(Some((arg_local, (arg_use, arg_def, _)))) = arg_consumes.first()
            {
                let (arg_use, arg_def) = carrier_presentations
                    .get(arg_local)
                    .map_or((*arg_use, *arg_def), |presentation| {
                        (presentation.r#use, presentation.def)
                    });
                self.equations.push(RecordedEquation::Linear {
                    left: destination_def,
                    right: arg_def,
                    result: arg_use,
                });
            }

            if let Some((destination_use, destination_def, slot)) = destination {
                self.equations.push(RecordedEquation::Assume {
                    var: destination_use,
                    value: false,
                });
                if is_source {
                    self.candidates.push(EndpointCandidate {
                        role: EndpointRole::Source,
                        function_path: function_path.clone(),
                        location: location.into(),
                        callee: callee.clone().expect("source callee"),
                        var: destination_def,
                        slot: CandidateSlot::Resolved(slot),
                        span: terminator.source_info.span,
                    });
                }
            }
            for (index, consume) in arg_consumes.into_iter().enumerate() {
                let Some((arg_local, (arg_use, arg_def, direct_slot))) = consume else {
                    continue;
                };
                if is_sink && index == 0 {
                    let direct = CarrierPresentation {
                        carrier: arg_local,
                        r#use: arg_use,
                        def: arg_def,
                        slot: direct_slot,
                    };
                    let (endpoint_var, endpoint_def, slot) = match resolve_sink_presentation(
                        arg_local,
                        direct,
                        &eliminable,
                        &sink_definitions,
                        &carrier_presentations,
                    ) {
                        Ok(presentation) => (
                            presentation.r#use,
                            presentation.def,
                            CandidateSlot::Resolved(presentation.slot),
                        ),
                        Err(reason) => (
                            arg_use,
                            arg_def,
                            CandidateSlot::Undeterminable {
                                direct: direct_slot,
                                reason,
                            },
                        ),
                    };
                    self.equations.push(RecordedEquation::Assume {
                        var: endpoint_def,
                        value: false,
                    });
                    self.candidates.push(EndpointCandidate {
                        role: EndpointRole::Sink,
                        function_path: function_path.clone(),
                        location: location.into(),
                        callee: callee.clone().expect("sink callee"),
                        var: endpoint_var,
                        slot,
                        span: terminator.source_info.span,
                    });
                } else if roles.is_empty() {
                    self.boundary_held.insert(
                        carrier_presentations
                            .get(&arg_local)
                            .map_or(direct_slot, |presentation| presentation.slot),
                    );
                    self.equations.push(RecordedEquation::LessEqual {
                        left: arg_def,
                        right: arg_use,
                    });
                }
            }
        }
        Ok(())
    }

    fn finish(mut self) -> Result<BoxOwnershipFacts, String> {
        let mut seeds = IndexVec::from_raw(vec![FactValue::Unknown; self.next_var as usize]);
        for (&var, &slot) in &self.var_slots {
            match self.model.get(&slot).copied() {
                Some(SlotKind::Raw | SlotKind::Ref) => {
                    assign(&mut seeds, var, FactValue::NotOwn)?;
                }
                Some(SlotKind::Owning) | None => {}
            }
        }
        for candidate in &self.candidates {
            let value = match candidate.slot {
                CandidateSlot::Resolved(slot) => match self.model.get(&slot) {
                    Some(SlotKind::Owning) => FactValue::MustOwn,
                    Some(SlotKind::Raw | SlotKind::Ref) => FactValue::NotOwn,
                    None => FactValue::Unknown,
                },
                CandidateSlot::Undeterminable { .. } => FactValue::Unknown,
            };
            assign(&mut seeds, candidate.var, value)?;
        }

        let direct_values = seeds.clone();
        let (values, replay_error) = match replay_values(seeds, &self.equations) {
            Ok(values) => (values, None),
            Err(error) => (direct_values, Some(error)),
        };
        let mut endpoints = Vec::with_capacity(self.candidates.len());
        for candidate in self.candidates {
            let (slot, slot_ref, final_kind, value, status, identity_reason) = match candidate.slot
            {
                CandidateSlot::Resolved(slot) => {
                    let final_kind = self
                        .model
                        .get(&slot)
                        .copied()
                        .ok_or_else(|| format!("Box endpoint model lacks slot {slot:?}"))?;
                    let value = values[candidate.var];
                    (
                        slot_label(slot),
                        Some(slot),
                        Some(final_kind),
                        value,
                        classify_endpoint(value, final_kind),
                        None,
                    )
                }
                CandidateSlot::Undeterminable { direct, reason } => (
                    format!("undeterminable:{}", slot_label(direct)),
                    None,
                    None,
                    FactValue::Unknown,
                    EndpointStatus::Unknown,
                    Some(reason.key().to_owned()),
                ),
            };
            endpoints.push(EndpointFact {
                role: candidate.role,
                function_path: candidate.function_path,
                location: candidate.location,
                callee: candidate.callee,
                var: candidate.var,
                slot,
                final_kind,
                value,
                status,
                unknown_reason: identity_reason.or_else(|| {
                    (status == EndpointStatus::Unknown).then(|| {
                        replay_error
                            .clone()
                            .unwrap_or_else(|| "constraint-underdetermined".to_owned())
                    })
                }),
                slot_ref,
                span: candidate.span,
            });
        }
        endpoints.sort_by(|left, right| {
            (
                &left.function_path,
                left.location,
                &left.callee,
                left.role,
                &left.slot,
            )
                .cmp(&(
                    &right.function_path,
                    right.location,
                    &right.callee,
                    right.role,
                    &right.slot,
                ))
        });
        self.version_sites.sort_by(|left, right| {
            (
                &left.function_path,
                left.location,
                left.local.as_u32(),
                left.relation,
            )
                .cmp(&(
                    &right.function_path,
                    right.location,
                    right.local.as_u32(),
                    right.relation,
                ))
        });
        let mut facts = BoxOwnershipFacts {
            equations: self.equations,
            version_sites: self.version_sites,
            endpoints,
            replay_error,
            canonical_sha256: String::new(),
            move_edges: self.move_edges,
            field_held: self.field_held,
            boundary_held: self.boundary_held,
        };
        facts
            .move_edges
            .sort_unstable_by_key(|(from, to)| (slot_order_key(*from), slot_order_key(*to)));
        facts.move_edges.dedup();
        facts.canonical_sha256 = format!("{:x}", Sha256::digest(facts.canonical_bytes()));
        Ok(facts)
    }
}

fn foreign_callee_name(program: &RustProgram<'_>, func: &Operand<'_>) -> Option<String> {
    let constant = func.constant()?;
    let &FnDef(callee, _) = constant.ty().kind() else {
        return None;
    };
    let local = callee.as_local()?;
    let rustc_hir::Node::ForeignItem(item) = program.tcx.hir_node_by_def_id(local) else {
        return None;
    };
    Some(item.ident.name.to_string())
}

fn slot_label(slot: SlotRef) -> String {
    match slot {
        SlotRef::Local(did, slot) => {
            format!("local:{}:{}", did.local_def_index.as_u32(), slot.index())
        }
        SlotRef::Field(slot) => format!("field:0:{}", slot.index()),
    }
}

fn slot_order_key(slot: SlotRef) -> (u8, u32, usize) {
    match slot {
        SlotRef::Field(slot) => (0, 0, slot.index()),
        SlotRef::Local(did, slot) => (1, did.local_def_index.as_u32(), slot.index()),
    }
}

fn exactly_one_sink_per_exit(body: &Body<'_>, source: LocationKey, sinks: &[LocationKey]) -> bool {
    exactly_one_sink_per_exit_graph(
        source.block,
        &sinks.iter().map(|sink| sink.block).collect::<Vec<_>>(),
        |block| {
            body.basic_blocks[rustc_middle::mir::BasicBlock::from_u32(block)]
                .terminator()
                .successors()
                .map(|next| next.as_u32())
                .collect()
        },
    )
}

fn exactly_one_sink_per_exit_graph(
    start: u32,
    sinks: &[u32],
    successors: impl Fn(u32) -> Vec<u32>,
) -> bool {
    let mut pending = vec![(start, 0usize)];
    let mut seen = FxHashSet::default();
    while let Some((block, count_before)) = pending.pop() {
        if !seen.insert((block, count_before)) {
            continue;
        }
        let count = count_before + sinks.iter().filter(|sink| **sink == block).count();
        if count > 1 {
            return false;
        }
        let next = successors(block);
        if next.is_empty() {
            if count != 1 {
                return false;
            }
        } else {
            pending.extend(next.into_iter().map(|next| (next, count)));
        }
    }
    true
}

#[derive(Clone, Debug)]
pub(crate) struct BoxOwnershipFacts {
    equations: Vec<RecordedEquation>,
    version_sites: Vec<VersionSite>,
    endpoints: Vec<EndpointFact>,
    replay_error: Option<String>,
    canonical_sha256: String,
    move_edges: Vec<(SlotRef, SlotRef)>,
    field_held: FxHashSet<SlotRef>,
    boundary_held: FxHashSet<SlotRef>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BoxShape {
    Sized,
    Slice,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ImplicitCloseKind {
    Overwrite,
    ScopeExit,
    Unwind,
}

impl ImplicitCloseKind {
    pub(crate) fn receipt(self) -> &'static str {
        match self {
            ImplicitCloseKind::Overwrite => "waiver-drop(overwrite)",
            ImplicitCloseKind::ScopeExit => "waiver-drop(scope-exit)",
            ImplicitCloseKind::Unwind => "waiver-drop(unwind)",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BoxExprEdit {
    pub(crate) span: Span,
    pub(crate) replacement: String,
    pub(crate) receipt: &'static str,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BoxPlan {
    pub(crate) shape: BoxShape,
    pub(crate) optional: bool,
    pub(crate) expr_edits: Vec<BoxExprEdit>,
    pub(crate) delete_statements: Vec<Span>,
    pub(crate) receipts: Vec<String>,
    pub(crate) fabricated_extent: bool,
    /// Exact source assignments whose old generation is closed by Rust's
    /// ordinary overwrite drop. The emitted-MIR postcheck maps only these
    /// lines to `waiver-drop(overwrite)`.
    pub(crate) overwrite_spans: Vec<Span>,
    /// A surviving C free consumes the final generation. Nullable plans still
    /// have an implicit drop of the now-empty `Option`; the postcheck maps that
    /// shell to this retained sink rather than inventing a waiver.
    pub(crate) retained_sink: bool,
    /// No retained sink survives for the final generation, so a normal exit
    /// may close it under the output-behavior waiver.
    pub(crate) implicit_scope_close: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BoxPlanFailure {
    PointerDepth,
    ParameterHeld,
    ConstructionUnmappable,
    EndpointInactive,
    EndpointUnjoined,
    MoveAmbiguous,
    FieldHeld,
    BoundaryHeld,
    InitializerUnsupported,
    ReallocUnsupported,
    FreeDuplicate,
    StoreFormUnknown,
    AstUnplaceable,
}

impl BoxPlanFailure {
    pub(crate) fn key(self) -> &'static str {
        match self {
            BoxPlanFailure::PointerDepth | BoxPlanFailure::ConstructionUnmappable => {
                "box-construction-unmappable"
            }
            BoxPlanFailure::ParameterHeld => "box-param-caller-unknown",
            BoxPlanFailure::EndpointInactive => "box-endpoint-inactive",
            BoxPlanFailure::EndpointUnjoined => "box-endpoint-unjoined",
            BoxPlanFailure::MoveAmbiguous => "box-move-ambiguous",
            BoxPlanFailure::FieldHeld => "box-field-held",
            BoxPlanFailure::BoundaryHeld => "box-param-caller-unknown",
            BoxPlanFailure::InitializerUnsupported => "box-initializer-unsupported",
            BoxPlanFailure::ReallocUnsupported => "box-realloc-transition-unsupported",
            BoxPlanFailure::FreeDuplicate => "box-free-duplicate",
            BoxPlanFailure::StoreFormUnknown => "box-store-form-unknown",
            BoxPlanFailure::AstUnplaceable => "box-ast-unplaceable",
        }
    }
}

impl BoxOwnershipFacts {
    pub(crate) fn derive(
        program: &RustProgram<'_>,
        slots: &CrateSlots,
        model: &FxHashMap<SlotRef, SlotKind>,
    ) -> Result<Self, String> {
        MinimalWalk::new(program, slots, model).walk()
    }

    pub(crate) fn endpoints(&self) -> &[EndpointFact] {
        &self.endpoints
    }

    pub(crate) fn canonical_sha256(&self) -> &str {
        &self.canonical_sha256
    }

    pub(crate) fn replay_error(&self) -> Option<&str> {
        self.replay_error.as_deref()
    }

    pub(crate) fn plan_for_subject(
        &self,
        tcx: rustc_middle::ty::TyCtxt<'_>,
        subject: &super::Subject,
        slot: SlotRef,
        constructions: &super::construction::ConstructionFacts,
        slots: &CrateSlots,
        subjects: &[super::Subject],
    ) -> Result<BoxPlan, BoxPlanFailure> {
        box_scope(
            matches!(subject.kind, super::SubjectKind::Param { .. }),
            subject.ptr_depth,
        )
        .map_err(|failure| match failure {
            BoxScopeFailure::PointerDepth => BoxPlanFailure::PointerDepth,
            BoxScopeFailure::ParameterHeld => BoxPlanFailure::ParameterHeld,
        })?;
        if subject.ty_span.is_none() || subject.pointee_span.is_none() {
            return Err(BoxPlanFailure::ConstructionUnmappable);
        }
        let body = tcx
            .mir_drops_elaborated_and_const_checked(subject.fn_did)
            .borrow();
        let ty = body.local_decls[subject.local].ty;
        let rustc_middle::ty::TyKind::RawPtr(pointee, _) = ty.kind() else {
            return Err(BoxPlanFailure::ConstructionUnmappable);
        };
        let normalized = format!("{pointee}");
        if !scalar_initializer_supported(&normalized) {
            return Err(BoxPlanFailure::InitializerUnsupported);
        }
        let subject_slot = |candidate: &super::Subject| {
            slots
                .fn_local_slots
                .get(&candidate.fn_did)
                .and_then(|universe| universe.slot_for_local_depth(candidate.local, 0))
                .map(|slot| SlotRef::Local(candidate.fn_did, slot))
        };

        let all_sources = self
            .endpoints
            .iter()
            .filter(|endpoint| {
                endpoint.role == EndpointRole::Source
                    && endpoint.status != EndpointStatus::Unknown
                    && endpoint
                        .slot_ref
                        .is_some_and(|source| self.move_reaches(source, slot))
            })
            .collect::<Vec<_>>();
        let active_sources = all_sources
            .iter()
            .copied()
            .filter(|endpoint| endpoint.status == EndpointStatus::Active)
            .collect::<Vec<_>>();
        if active_sources.is_empty() {
            return Err(BoxPlanFailure::EndpointInactive);
        }
        let key = (subject.fn_did, subject.hir_id);
        let construction = constructions
            .by_binding
            .get(&key)
            .ok_or(BoxPlanFailure::ConstructionUnmappable)?;
        let overwrite_count = constructions.owner_overwrites.get(&key).map_or(0, Vec::len);
        let expected_sources = match construction {
            super::construction::Construction::CopyOf => 1,
            super::construction::Construction::NullLit => overwrite_count,
            _ => 1 + overwrite_count,
        };
        if all_sources.len() != expected_sources {
            return Err(BoxPlanFailure::MoveAmbiguous);
        }
        let source_slot = all_sources[0].slot_ref.expect("source slot");
        if self
            .field_held
            .iter()
            .any(|held| *held == slot || self.move_reaches(slot, *held))
        {
            return Err(BoxPlanFailure::FieldHeld);
        }
        if self
            .boundary_held
            .iter()
            .any(|held| *held == slot || self.move_reaches(slot, *held))
        {
            return Err(BoxPlanFailure::BoundaryHeld);
        }
        if matches!(construction, super::construction::Construction::CopyOf) {
            if self.move_edges.iter().any(|(from, _)| {
                self.move_reaches(source_slot, *from)
                    && self
                        .move_edges
                        .iter()
                        .filter(|(candidate, _)| candidate == from)
                        .map(|(_, to)| *to)
                        .collect::<rustc_hash::FxHashSet<_>>()
                        .len()
                        > 1
            }) {
                return Err(BoxPlanFailure::MoveAmbiguous);
            }
            let upstream = subjects
                .iter()
                .filter(|candidate| candidate.fn_did == subject.fn_did)
                .filter_map(|candidate| {
                    let candidate_slot = subject_slot(candidate)?;
                    let construction = constructions
                        .by_binding
                        .get(&(candidate.fn_did, candidate.hir_id))?;
                    matches!(
                        construction,
                        super::construction::Construction::Alloc { .. }
                    )
                    .then_some((candidate, candidate_slot, construction))
                })
                .filter(|(_, candidate_slot, _)| {
                    self.move_reaches(source_slot, *candidate_slot)
                        && self.move_reaches(*candidate_slot, slot)
                })
                .collect::<Vec<_>>();
            let [(upstream, _, upstream_construction)] = upstream.as_slice() else {
                return Err(BoxPlanFailure::MoveAmbiguous);
            };
            let shape = match upstream_construction {
                super::construction::Construction::Alloc {
                    callee,
                    count: Some(count),
                    ..
                } if callee == "calloc" && count.trim() != "1" => BoxShape::Slice,
                _ => BoxShape::Sized,
            };
            let retained_sink = self.endpoints.iter().any(|endpoint| {
                endpoint.role == EndpointRole::Sink
                    && endpoint.status == EndpointStatus::Active
                    && endpoint
                        .slot_ref
                        .is_some_and(|sink| self.move_reaches(slot, sink))
            });
            return Ok(BoxPlan {
                shape,
                optional: false,
                expr_edits: Vec::new(),
                delete_statements: Vec::new(),
                receipts: vec![format!(
                    "box-move-companion source={} destination={}",
                    upstream.label, subject.label
                )],
                fabricated_extent: false,
                overwrite_spans: Vec::new(),
                retained_sink,
                implicit_scope_close: !retained_sink,
            });
        }
        let all_active_sinks = self
            .endpoints
            .iter()
            .filter(|endpoint| {
                endpoint.role == EndpointRole::Sink
                    && endpoint.status == EndpointStatus::Active
                    && endpoint
                        .slot_ref
                        .is_some_and(|sink| self.move_reaches(slot, sink))
            })
            .collect::<Vec<_>>();
        let realloc_sinks = all_active_sinks
            .iter()
            .copied()
            .filter(|sink| sink.callee == "realloc")
            .collect::<Vec<_>>();
        let active_sinks = all_active_sinks
            .iter()
            .copied()
            .filter(|sink| sink.callee != "realloc")
            .collect::<Vec<_>>();
        let realloc_overwrites = constructions
            .owner_overwrites
            .get(&key)
            .into_iter()
            .flatten()
            .filter(|overwrite| {
                matches!(
                    &overwrite.construction,
                    super::construction::Construction::Alloc { callee, .. }
                        if callee == "realloc"
                )
            })
            .count();
        if realloc_sinks.len() != realloc_overwrites {
            return Err(BoxPlanFailure::ReallocUnsupported);
        }
        if active_sinks.len() > 1
            && !exactly_one_sink_per_exit(
                &body,
                active_sources[0].location,
                &active_sinks
                    .iter()
                    .map(|sink| sink.location)
                    .collect::<Vec<_>>(),
            )
        {
            return Err(BoxPlanFailure::FreeDuplicate);
        }
        if subject.freed_at.is_some() && active_sinks.is_empty() {
            return Err(BoxPlanFailure::EndpointUnjoined);
        }
        if self.move_edges.iter().any(|(from, _)| {
            if !self.move_reaches(source_slot, *from) {
                return false;
            }
            self.move_edges
                .iter()
                .filter(|(candidate, _)| candidate == from)
                .map(|(_, to)| *to)
                .filter(|to| {
                    self.move_reaches(*to, slot)
                        || active_sinks.iter().any(|sink| {
                            sink.slot_ref
                                .is_some_and(|sink_slot| self.move_reaches(*to, sink_slot))
                        })
                })
                .collect::<rustc_hash::FxHashSet<_>>()
                .len()
                > 1
        }) {
            return Err(BoxPlanFailure::MoveAmbiguous);
        }

        let init_span = *constructions
            .init_spans
            .get(&key)
            .ok_or(BoxPlanFailure::AstUnplaceable)?;
        let mut delete_statements = Vec::new();
        let (initializer, initializer_arm, shape, fabricated_extent, optional) = match construction
        {
            super::construction::Construction::Alloc {
                callee,
                size,
                count: None,
            } if callee == "malloc" && size.contains(&format!("size_of::<{normalized}>")) => {
                if let Some(stores) = constructions.first_stores.get(&key)
                    && stores.len() == 1 + overwrite_count
                {
                    let store = &stores[0];
                    delete_statements.push(store.statement_span);
                    (
                        format!("Box::new({})", store.value),
                        "malloc-literal-first-store",
                        BoxShape::Sized,
                        false,
                        false,
                    )
                } else if overwrite_count == 0
                    && let Some(memsets) = constructions.zero_memsets.get(&key)
                    && let [memset] = memsets.as_slice()
                {
                    delete_statements.push(memset.statement_span);
                    (
                        format!(
                            "vec![0 as {normalized}; crate::FALLBACK_SLICE_EXTENT].into_boxed_slice()"
                        ),
                        "memset-zero-slice",
                        BoxShape::Slice,
                        true,
                        false,
                    )
                } else {
                    return Err(BoxPlanFailure::InitializerUnsupported);
                }
            }
            super::construction::Construction::Alloc {
                callee,
                size,
                count: Some(count),
            } if callee == "calloc" && size.contains(&format!("size_of::<{normalized}>")) => {
                if count.trim() == "1" {
                    (
                        format!("Box::new(0 as {normalized})"),
                        "calloc-zero-scalar",
                        BoxShape::Sized,
                        false,
                        false,
                    )
                } else {
                    (
                        format!("vec![0 as {normalized}; {count}].into_boxed_slice()"),
                        "calloc-zero-slice",
                        BoxShape::Slice,
                        false,
                        false,
                    )
                }
            }
            super::construction::Construction::NullLit if overwrite_count > 0 => {
                let overwrites = constructions
                    .owner_overwrites
                    .get(&key)
                    .ok_or(BoxPlanFailure::InitializerUnsupported)?;
                let shape = if overwrites.iter().any(|overwrite| {
                    matches!(
                        &overwrite.construction,
                        super::construction::Construction::Alloc {
                            callee,
                            count: Some(count),
                            ..
                        } if callee == "calloc" && count.trim() != "1"
                    )
                }) {
                    BoxShape::Slice
                } else {
                    BoxShape::Sized
                };
                ("None".to_owned(), "null-init", shape, false, true)
            }
            super::construction::Construction::Alloc { callee, .. } if callee == "realloc" => {
                return Err(BoxPlanFailure::ReallocUnsupported);
            }
            _ => return Err(BoxPlanFailure::InitializerUnsupported),
        };
        let expected_active_callee = constructions
            .owner_overwrites
            .get(&key)
            .and_then(|overwrites| overwrites.last())
            .and_then(|overwrite| match &overwrite.construction {
                super::construction::Construction::Alloc { callee, .. } => Some(callee.as_str()),
                _ => None,
            })
            .or_else(|| match construction {
                super::construction::Construction::Alloc { callee, .. } => Some(callee.as_str()),
                _ => None,
            })
            .ok_or(BoxPlanFailure::ConstructionUnmappable)?;
        if active_sources.last().expect("active source").callee != expected_active_callee {
            return Err(BoxPlanFailure::EndpointUnjoined);
        }

        let mut expr_edits = vec![BoxExprEdit {
            span: init_span,
            replacement: initializer,
            receipt: initializer_arm,
        }];
        let mut fabricated_extent = fabricated_extent;
        if overwrite_count > 0 {
            let overwrites = constructions
                .owner_overwrites
                .get(&key)
                .ok_or(BoxPlanFailure::StoreFormUnknown)?;
            let stores = constructions
                .first_stores
                .get(&key)
                .map(Vec::as_slice)
                .unwrap_or(&[]);
            let mut store_index = usize::from(matches!(
                construction,
                super::construction::Construction::Alloc { callee, .. } if callee == "malloc"
            ));
            let name = subject
                .param_name
                .as_deref()
                .ok_or(BoxPlanFailure::AstUnplaceable)?;
            for overwrite in overwrites {
                match &overwrite.construction {
                    super::construction::Construction::Alloc {
                        callee,
                        size,
                        count: None,
                    } if callee == "malloc"
                        && size.contains(&format!("size_of::<{normalized}>")) =>
                    {
                        let store = stores
                            .get(store_index)
                            .ok_or(BoxPlanFailure::InitializerUnsupported)?;
                        store_index += 1;
                        let replacement = format!("Box::new({})", store.value);
                        expr_edits.push(BoxExprEdit {
                            span: overwrite.value_span,
                            replacement: if optional {
                                format!("Some({replacement})")
                            } else {
                                replacement
                            },
                            receipt: "malloc-overwrite-literal-first-store",
                        });
                        delete_statements.push(store.statement_span);
                    }
                    super::construction::Construction::Alloc { callee, .. }
                        if callee == "realloc" && shape == BoxShape::Slice && !optional =>
                    {
                        fabricated_extent = true;
                        expr_edits.push(BoxExprEdit {
                            span: overwrite.value_span,
                            replacement: format!(
                                "{{ let mut __crat_box_vec = Vec::from({name}); \
                                 __crat_box_vec.resize(crate::FALLBACK_SLICE_EXTENT, \
                                 0 as {normalized}); __crat_box_vec.into_boxed_slice() }}"
                            ),
                            receipt: "realloc-atomic",
                        });
                    }
                    _ => return Err(BoxPlanFailure::StoreFormUnknown),
                }
            }
            if store_index != stores.len() {
                return Err(BoxPlanFailure::InitializerUnsupported);
            }
        }
        let mut receipts = vec![format!(
            "box-construction arm={initializer_arm} site={}",
            super::emitability::EmitabilityFacts::site(tcx, init_span)
        )];
        for store_span in &delete_statements {
            receipts.push(format!(
                "box-deleted-statement arm={initializer_arm} span={}",
                super::emitability::EmitabilityFacts::site(tcx, *store_span)
            ));
        }
        for overwrite in constructions
            .owner_overwrites
            .get(&key)
            .into_iter()
            .flatten()
        {
            let is_realloc = matches!(
                &overwrite.construction,
                super::construction::Construction::Alloc { callee, .. } if callee == "realloc"
            );
            receipts.push(format!(
                "{} site={}",
                if is_realloc {
                    "box-realloc-atomic"
                } else {
                    ImplicitCloseKind::Overwrite.receipt()
                },
                super::emitability::EmitabilityFacts::site(tcx, overwrite.statement_span)
            ));
        }
        if !active_sinks.is_empty() {
            let mut sink_subjects = active_sinks
                .iter()
                .map(|sink| {
                    let sink_slot = sink.slot_ref.ok_or(BoxPlanFailure::EndpointUnjoined)?;
                    let matched = subjects
                        .iter()
                        .filter(|candidate| subject_slot(candidate) == Some(sink_slot))
                        .collect::<Vec<_>>();
                    let [sink_subject] = matched.as_slice() else {
                        return Err(BoxPlanFailure::AstUnplaceable);
                    };
                    Ok(*sink_subject)
                })
                .collect::<Result<Vec<_>, BoxPlanFailure>>()?;
            sink_subjects.sort_unstable_by_key(|subject| subject.local.as_u32());
            sink_subjects.dedup_by_key(|subject| subject.local);
            let [sink_subject] = sink_subjects.as_slice() else {
                return Err(BoxPlanFailure::MoveAmbiguous);
            };
            let sink_key = (sink_subject.fn_did, sink_subject.hir_id);
            let name = sink_subject
                .param_name
                .as_deref()
                .ok_or(BoxPlanFailure::AstUnplaceable)?;
            let realloc_calls = constructions
                .realloc_calls
                .get(&sink_key)
                .into_iter()
                .flatten()
                .map(|span| (span.lo(), span.hi()))
                .collect::<FxHashSet<_>>();
            let mut calls = constructions
                .deallocator_calls
                .get(&sink_key)
                .ok_or(BoxPlanFailure::AstUnplaceable)?
                .iter()
                .copied()
                .filter(|span| !realloc_calls.contains(&(span.lo(), span.hi())))
                .collect::<Vec<_>>();
            if calls.len() != active_sinks.len() {
                return Err(BoxPlanFailure::FreeDuplicate);
            }
            calls.sort_unstable_by_key(|span| span.lo());
            for (sink, call_span) in active_sinks.iter().zip(calls) {
                expr_edits.push(BoxExprEdit {
                    span: call_span,
                    replacement: if optional {
                        format!("drop({name}.take())")
                    } else {
                        format!("drop({name})")
                    },
                    receipt: "c-free-site-drop",
                });
                receipts.push(format!(
                    "box-destruction callee={} site={}",
                    sink.callee,
                    super::emitability::EmitabilityFacts::site(tcx, call_span)
                ));
            }
        } else {
            receipts.push(format!(
                "{} site={}",
                ImplicitCloseKind::ScopeExit.receipt(),
                super::emitability::EmitabilityFacts::site(tcx, subject.binding_span)
            ));
        }
        let overwrite_spans = constructions
            .owner_overwrites
            .get(&key)
            .into_iter()
            .flatten()
            .filter_map(|overwrite| {
                (!matches!(
                    &overwrite.construction,
                    super::construction::Construction::Alloc { callee, .. }
                        if callee == "realloc"
                ))
                .then_some(overwrite.statement_span)
            })
            .collect();
        let retained_sink = !active_sinks.is_empty();
        Ok(BoxPlan {
            shape,
            optional,
            expr_edits,
            delete_statements,
            receipts,
            fabricated_extent,
            overwrite_spans,
            retained_sink,
            implicit_scope_close: !retained_sink,
        })
    }

    pub(crate) fn equations_tsv(&self) -> String {
        let mut rows = self
            .equations
            .iter()
            .map(|equation| match *equation {
                RecordedEquation::Linear {
                    left,
                    right,
                    result,
                } => format!(
                    "linear\t{}\t{}\t{}\t-",
                    left.as_u32(),
                    right.as_u32(),
                    result.as_u32()
                ),
                RecordedEquation::Assume { var, value } => {
                    format!("assume\t{}\t-\t-\t{}", var.as_u32(), u8::from(value))
                }
                RecordedEquation::Equal { left, right } => {
                    format!("equal\t{}\t{}\t-\t-", left.as_u32(), right.as_u32())
                }
                RecordedEquation::LessEqual { left, right } => {
                    format!("less-equal\t{}\t{}\t-\t-", left.as_u32(), right.as_u32())
                }
                RecordedEquation::EqMin {
                    result,
                    left,
                    right,
                } => format!(
                    "eq-min\t{}\t{}\t{}\t-",
                    result.as_u32(),
                    left.as_u32(),
                    right.as_u32()
                ),
            })
            .collect::<Vec<_>>();
        rows.sort();
        let mut output = String::from("relation\tx\ty\tz\tvalue\n");
        for row in rows {
            output.push_str(&row);
            output.push('\n');
        }
        output
    }

    fn canonical_bytes(&self) -> Vec<u8> {
        let mut bytes = render_equations(&self.equations).into_bytes();
        bytes.extend(self.version_sites_tsv().bytes());
        bytes.extend(self.endpoints_tsv().bytes());
        for &(from, to) in &self.move_edges {
            bytes.extend(format!("move\t{}\t{}\n", slot_label(from), slot_label(to)).bytes());
        }
        for (kind, slots) in [
            ("field-held", &self.field_held),
            ("boundary-held", &self.boundary_held),
        ] {
            let mut slots = slots.iter().copied().collect::<Vec<_>>();
            slots.sort_unstable_by_key(|slot| slot_order_key(*slot));
            for slot in slots {
                bytes.extend(format!("{kind}\t{}\n", slot_label(slot)).bytes());
            }
        }
        bytes
    }

    fn move_reaches(&self, start: SlotRef, target: SlotRef) -> bool {
        if start == target {
            return true;
        }
        let mut seen = rustc_hash::FxHashSet::default();
        let mut pending = vec![start];
        while let Some(current) = pending.pop() {
            if !seen.insert(current) {
                continue;
            }
            for &(_, next) in self.move_edges.iter().filter(|(from, _)| *from == current) {
                if next == target {
                    return true;
                }
                pending.push(next);
            }
        }
        false
    }

    pub(crate) fn version_sites_tsv(&self) -> String {
        let mut output = String::from(
            "function_path\tmir_local\tblock\tstatement\tuse_var\tdef_var\trelation\n",
        );
        for site in &self.version_sites {
            output.push_str(&format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
                site.function_path,
                site.local.as_u32(),
                site.location.block,
                site.location.statement,
                site.use_var
                    .map_or("-".to_owned(), |var| var.as_u32().to_string()),
                site.def_var
                    .map_or("-".to_owned(), |var| var.as_u32().to_string()),
                site.relation,
            ));
        }
        output
    }

    pub(crate) fn endpoints_tsv(&self) -> String {
        let mut output = String::from(
            "role\tfunction\tblock\tstatement\tcallee\tvar\tslot\tfinal_kind\tvalue\tstate\tunknown_reason\n",
        );
        for endpoint in &self.endpoints {
            let kind = match endpoint.final_kind {
                Some(SlotKind::Ref) => "Ref",
                Some(SlotKind::Raw) => "Raw",
                Some(SlotKind::Owning) => "Owning",
                None => "-",
            };
            let value = match endpoint.value {
                FactValue::MustOwn => "must-own",
                FactValue::NotOwn => "not-own",
                FactValue::Unknown => "unknown",
            };
            output.push_str(&format!(
                "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
                endpoint.role.key(),
                endpoint.function_path,
                endpoint.location.block,
                endpoint.location.statement,
                endpoint.callee,
                endpoint.var.as_u32(),
                endpoint.slot,
                kind,
                value,
                endpoint.status.key(),
                endpoint.unknown_reason.as_deref().unwrap_or("-"),
            ));
        }
        output
    }
}

#[cfg(test)]
mod tests {
    use rustc_index::IndexVec;

    use super::{
        BoxScopeFailure, EndpointStatus, FactValue, RecordedEquation, SinkCarrierDef,
        SinkCarrierReason, box_scope, classify_endpoint, exactly_one_sink_per_exit_graph,
        render_equations, replay_values, resolve_sink_carrier, scalar_initializer_supported,
    };
    use crate::analyses::borrow_ownership::{SlotKind, ssa::constraint::Var};

    fn var(index: u32) -> Var {
        Var::from_u32(index)
    }

    #[test]
    fn box_x1_equal_and_linear_replay_reaches_a_unique_model() {
        let mut seeds = IndexVec::from_raw(vec![FactValue::Unknown; 5]);
        seeds[var(1)] = FactValue::MustOwn;
        seeds[var(4)] = FactValue::NotOwn;
        let equations = [
            RecordedEquation::Equal {
                left: var(1),
                right: var(2),
            },
            RecordedEquation::Linear {
                left: var(2),
                right: var(3),
                result: var(1),
            },
        ];

        let values = replay_values(seeds, &equations).expect("consistent replay");
        assert_eq!(values[var(1)], FactValue::MustOwn);
        assert_eq!(values[var(2)], FactValue::MustOwn);
        assert_eq!(values[var(3)], FactValue::NotOwn);
        assert_eq!(values[var(4)], FactValue::NotOwn);
    }

    #[test]
    fn box_x1_underdetermined_linear_stays_unknown() {
        let mut seeds = IndexVec::from_raw(vec![FactValue::Unknown; 4]);
        seeds[var(3)] = FactValue::MustOwn;
        let equations = [RecordedEquation::Linear {
            left: var(1),
            right: var(2),
            result: var(3),
        }];

        let values = replay_values(seeds, &equations).expect("consistent replay");
        assert_eq!(values[var(1)], FactValue::Unknown);
        assert_eq!(values[var(2)], FactValue::Unknown);
        assert_eq!(values[var(3)], FactValue::MustOwn);
    }

    #[test]
    fn box_x1_contradictory_facts_fail_closed() {
        let mut seeds = IndexVec::from_raw(vec![FactValue::Unknown; 3]);
        seeds[var(1)] = FactValue::MustOwn;
        seeds[var(2)] = FactValue::NotOwn;
        let equations = [RecordedEquation::Equal {
            left: var(1),
            right: var(2),
        }];

        assert!(replay_values(seeds, &equations).is_err());
    }

    #[test]
    fn box_n7_endpoint_is_active_only_for_must_own_over_owning_slot() {
        assert_eq!(
            classify_endpoint(FactValue::MustOwn, SlotKind::Owning),
            EndpointStatus::Active,
        );
        assert_eq!(
            classify_endpoint(FactValue::MustOwn, SlotKind::Raw),
            EndpointStatus::InactiveSlot,
        );
        assert_eq!(
            classify_endpoint(FactValue::NotOwn, SlotKind::Owning),
            EndpointStatus::InactiveVar,
        );
        assert_eq!(
            classify_endpoint(FactValue::Unknown, SlotKind::Owning),
            EndpointStatus::Unknown,
        );
    }

    #[test]
    fn box_n8_equation_receipt_is_order_independent() {
        let left = RecordedEquation::Equal {
            left: var(1),
            right: var(2),
        };
        let right = RecordedEquation::Assume {
            var: var(3),
            value: false,
        };
        assert_eq!(
            render_equations(&[left.clone(), right.clone()]),
            render_equations(&[right, left]),
        );
    }

    #[test]
    fn box_n7_copy_temp_sink_resolves_to_its_carrier() {
        let temp = rustc_middle::mir::Local::from_usize(9);
        let carrier = rustc_middle::mir::Local::from_usize(4);
        assert_eq!(
            resolve_sink_carrier(temp, true, Some(SinkCarrierDef::Copy(carrier))),
            Ok(carrier),
            "mutation killer: deleting sink-carrier resolution returns the temp"
        );
    }

    #[test]
    fn box_n7_direct_sink_argument_keeps_its_identity() {
        let direct = rustc_middle::mir::Local::from_usize(4);
        assert_eq!(resolve_sink_carrier(direct, false, None), Ok(direct));
    }

    #[test]
    fn box_n7_ambiguous_sink_carriers_fail_closed_by_reason() {
        let temp = rustc_middle::mir::Local::from_usize(9);
        for (definition, expected) in [
            (Some(SinkCarrierDef::Multiple), SinkCarrierReason::MultiDef),
            (Some(SinkCarrierDef::NonCopy), SinkCarrierReason::NonCopyDef),
            (
                Some(SinkCarrierDef::Projected),
                SinkCarrierReason::ProjectionBase,
            ),
            (None, SinkCarrierReason::MissingDef),
        ] {
            assert_eq!(resolve_sink_carrier(temp, true, definition), Err(expected));
        }
    }

    #[test]
    fn box_n3_sink_paths_require_exactly_one_sink_each() {
        let diamond = |block| match block {
            0 => vec![1, 2],
            1 | 2 => vec![3],
            _ => Vec::new(),
        };
        assert!(exactly_one_sink_per_exit_graph(0, &[1, 2], diamond));
        assert!(
            !exactly_one_sink_per_exit_graph(0, &[1, 3], diamond),
            "one branch reaches two sinks and must fail box-free-duplicate"
        );
        assert!(
            !exactly_one_sink_per_exit_graph(0, &[1], diamond),
            "one branch reaches no sink and must fail closed"
        );
    }

    #[test]
    fn box_wave1_scope_is_local_depth_one_only() {
        assert_eq!(box_scope(false, 1), Ok(()));
        assert_eq!(box_scope(true, 1), Err(BoxScopeFailure::ParameterHeld));
        assert_eq!(box_scope(false, 2), Err(BoxScopeFailure::PointerDepth));
        assert_eq!(box_scope(true, 2), Err(BoxScopeFailure::PointerDepth));
    }

    #[test]
    fn box_w1_scalar_initializer_vocabulary_is_closed() {
        for admitted in ["u8", "u32", "usize", "i8", "i32", "isize", "f32", "f64"] {
            assert!(scalar_initializer_supported(admitted), "{admitted}");
        }
        for refused in ["bool", "char", "*mut i32", "S", "[u8; 4]", "()"] {
            assert!(!scalar_initializer_supported(refused), "{refused}");
        }
    }
}
