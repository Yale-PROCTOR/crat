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
}

impl SinkCarrierReason {
    fn key(self) -> &'static str {
        match self {
            SinkCarrierReason::MultiDef => "sink-carrier-multi-def",
            SinkCarrierReason::NonCopyDef => "sink-carrier-non-copy-def",
            SinkCarrierReason::ProjectionBase => "sink-carrier-projection-base",
            SinkCarrierReason::MissingDef => "sink-carrier-missing-def",
            SinkCarrierReason::MissingVersionSite => "sink-carrier-version-site-missing",
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

/// The r3-accepted endpoint-naming domain: exactly eliminable argument-0
/// temporaries of known ForeignC Sink calls. This type is intentionally not
/// interchangeable with [`BoxMoveTemps`].
#[derive(Default)]
struct SinkNamingTemps(FxHashSet<Local>);

impl SinkNamingTemps {
    fn from_seeds(seeds: impl IntoIterator<Item = Local>) -> Self {
        Self(seeds.into_iter().collect())
    }

    fn contains(&self, local: Local) -> bool {
        self.0.contains(&local)
    }
}

/// The widened copy-transparent domain used by Box responsibility/move
/// routing. It may recursively include a carrier that endpoint naming must not
/// inspect.
#[derive(Default)]
struct BoxMoveTemps(FxHashSet<Local>);

impl BoxMoveTemps {
    fn closed_from_seeds(
        seeds: impl IntoIterator<Item = Local>,
        definitions: &IndexVec<Local, Option<SinkCarrierDef>>,
        is_transparent: impl Fn(Local) -> bool,
    ) -> Self {
        let mut values = seeds.into_iter().collect::<FxHashSet<_>>();
        let mut pending = values.iter().copied().collect::<Vec<_>>();
        while let Some(local) = pending.pop() {
            if let Some(SinkCarrierDef::Copy(carrier)) = definitions[local]
                && is_transparent(carrier)
                && values.insert(carrier)
            {
                pending.push(carrier);
            }
        }
        Self(values)
    }

    fn contains(&self, local: Local) -> bool {
        self.0.contains(&local)
    }
}

#[derive(Default)]
struct SinkNamingPresentations(FxHashMap<Local, CarrierPresentation>);

impl SinkNamingPresentations {
    fn insert(&mut self, local: Local, presentation: CarrierPresentation) {
        self.0.insert(local, presentation);
    }

    fn get(&self, local: Local) -> Option<&CarrierPresentation> {
        self.0.get(&local)
    }
}

#[derive(Default)]
struct BoxMovePresentations(FxHashMap<Local, CarrierPresentation>);

impl BoxMovePresentations {
    fn insert(&mut self, local: Local, presentation: CarrierPresentation) {
        self.0.insert(local, presentation);
    }

    fn get(&self, local: Local) -> Option<&CarrierPresentation> {
        self.0.get(&local)
    }
}

/// The third sealed presentation domain. These rows project a ForeignC Source
/// call's compiler temporary onto the source binding whose construction is
/// being planned. They are deliberately not accepted by endpoint naming or
/// semantic move-routing APIs.
#[derive(Clone, Debug, PartialEq, Eq)]
struct ConstructionBridgeHop {
    source: Local,
    destination: Local,
    source_var: Var,
    destination_var: Var,
    location: LocationKey,
    transparent: bool,
    destination_single_def: bool,
    block_single_predecessor: bool,
}

#[derive(Clone, Debug, Default)]
struct ConstructionBridgeTemps(Vec<ConstructionBridgeHop>);

impl ConstructionBridgeTemps {
    fn from_hops(hops: impl IntoIterator<Item = ConstructionBridgeHop>) -> Self {
        Self(hops.into_iter().collect())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ConstructionBridgePresentation {
    source: Local,
    subject: Local,
    hops: Vec<ConstructionBridgeHop>,
}

impl ConstructionBridgePresentation {
    fn receipt(&self, endpoint: &EndpointFact, subject_slot: SlotRef) -> String {
        let hops = self
            .hops
            .iter()
            .map(|hop| {
                format!(
                    "{}:{}:{}>{}:{}>{}",
                    hop.location.block,
                    hop.location.statement,
                    hop.source.as_u32(),
                    hop.destination.as_u32(),
                    hop.source_var.as_u32(),
                    hop.destination_var.as_u32(),
                )
            })
            .collect::<Vec<_>>()
            .join(",");
        format!(
            "box-construction-bridge endpoint={}:{}:{}:{}:{}:{} subject_local={} subject_slot={} hops={}",
            endpoint.function_path,
            endpoint.location.block,
            endpoint.location.statement,
            endpoint.callee,
            endpoint.var.as_u32(),
            endpoint.slot,
            self.subject.as_u32(),
            slot_label(subject_slot),
            if hops.is_empty() { "direct" } else { &hops },
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ConstructionBridgeFailure {
    MissingVersionSite,
    MultipleDefinitions,
    BranchOrJoinFed,
    NonTransparentRvalue,
    ProjectedPlace,
    CrossFunctionHop,
    MultipleTerminals,
    DifferentSubject,
}

impl ConstructionBridgeFailure {
    fn key(self) -> &'static str {
        match self {
            Self::MissingVersionSite => "missing-version-site",
            Self::MultipleDefinitions => "multiple-definitions",
            Self::BranchOrJoinFed => "branch-or-join-fed",
            Self::NonTransparentRvalue => "nontransparent-rvalue",
            Self::ProjectedPlace => "projected-place",
            Self::CrossFunctionHop => "cross-function-hop",
            Self::MultipleTerminals => "multiple-terminals",
            Self::DifferentSubject => "different-subject",
        }
    }
}

fn resolve_construction_bridge(
    source: Local,
    source_var: Var,
    subject: Local,
    domain: &ConstructionBridgeTemps,
) -> Result<ConstructionBridgePresentation, ConstructionBridgeFailure> {
    if source == subject {
        return Ok(ConstructionBridgePresentation {
            source,
            subject,
            hops: Vec::new(),
        });
    }

    let mut current_local = source;
    let mut current_var = source_var;
    let mut seen = FxHashSet::default();
    let mut path = Vec::new();
    loop {
        if !seen.insert((current_local, current_var)) {
            return Err(ConstructionBridgeFailure::MultipleTerminals);
        }
        let candidates = domain
            .0
            .iter()
            .filter(|hop| hop.source == current_local && hop.source_var == current_var)
            .collect::<Vec<_>>();
        let [hop] = candidates.as_slice() else {
            return Err(if candidates.is_empty() {
                if path.is_empty() {
                    ConstructionBridgeFailure::MissingVersionSite
                } else {
                    ConstructionBridgeFailure::DifferentSubject
                }
            } else {
                ConstructionBridgeFailure::MultipleTerminals
            });
        };
        if !hop.destination_single_def {
            return Err(ConstructionBridgeFailure::MultipleDefinitions);
        }
        if !hop.block_single_predecessor {
            return Err(ConstructionBridgeFailure::BranchOrJoinFed);
        }
        if !hop.transparent {
            return Err(ConstructionBridgeFailure::NonTransparentRvalue);
        }
        path.push((*hop).clone());
        if hop.destination == subject {
            return Ok(ConstructionBridgePresentation {
                source,
                subject,
                hops: path,
            });
        }
        current_local = hop.destination;
        current_var = hop.destination_var;
    }
}

fn resolve_sink_naming_carrier(
    operand: Local,
    naming: &SinkNamingTemps,
    definitions: &IndexVec<Local, Option<SinkCarrierDef>>,
) -> Result<Local, SinkCarrierReason> {
    resolve_sink_carrier(operand, naming.contains(operand), definitions[operand])
}

fn resolve_sink_presentation(
    operand: Local,
    direct: CarrierPresentation,
    naming: &SinkNamingTemps,
    definitions: &IndexVec<Local, Option<SinkCarrierDef>>,
    presentations: &SinkNamingPresentations,
) -> Result<CarrierPresentation, SinkCarrierReason> {
    let carrier = resolve_sink_naming_carrier(operand, naming, definitions)?;
    if carrier == operand {
        return Ok(direct);
    }
    presentations
        .get(operand)
        .copied()
        .filter(|presentation| presentation.carrier == carrier)
        .ok_or(SinkCarrierReason::MissingVersionSite)
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
    /// Source-level ownership transfers; these alone participate in the
    /// branching/ambiguity guard.
    move_edges: Vec<(SlotRef, SlotRef)>,
    /// Eliminable argument-carrier projections. They extend reachability to
    /// the r3 endpoint name but never create a second ownership branch.
    transparent_move_edges: Vec<(SlotRef, SlotRef)>,
    construction_bridge_temps: ConstructionBridgeTemps,
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
            transparent_move_edges: Vec::new(),
            construction_bridge_temps: ConstructionBridgeTemps::default(),
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
        let mut sink_naming_seeds = FxHashSet::default();
        let mut box_move_seeds = FxHashSet::default();
        for data in body.basic_blocks.iter() {
            let Some(terminator) = data.terminator.as_ref() else {
                continue;
            };
            let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
                continue;
            };
            for local in args
                .iter()
                .filter_map(|arg| arg.node.place())
                .filter_map(|place| place.as_local())
                .filter(|local| eliminable.contains(*local))
            {
                box_move_seeds.insert(local);
            }
            let is_sink = foreign_callee_name(self.program, func)
                .as_deref()
                .and_then(|name| boundary_table::lookup(name, Matcher::ForeignC))
                .is_some_and(|entry| entry.roles.contains(&Role::Sink));
            if is_sink
                && let Some(local) = args
                    .first()
                    .and_then(|arg| arg.node.place())
                    .and_then(|place| place.as_local())
                && eliminable.contains(local)
            {
                sink_naming_seeds.insert(local);
            }
        }
        let sink_naming_temps = SinkNamingTemps::from_seeds(sink_naming_seeds);
        let box_move_temps =
            BoxMoveTemps::closed_from_seeds(box_move_seeds, &sink_definitions, |local| {
                eliminable.contains(local)
            });
        let mut sink_naming_presentations = SinkNamingPresentations::default();
        let mut box_move_presentations = BoxMovePresentations::default();
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
                if sink_naming_temps.contains(lhs_local) || box_move_temps.contains(lhs_local) {
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
                        let presentation = CarrierPresentation {
                            carrier: rhs_local,
                            r#use: rhs_use,
                            def: rhs_def,
                            slot: rhs_slot,
                        };
                        if sink_naming_temps.contains(lhs_local) {
                            sink_naming_presentations.insert(lhs_local, presentation);
                        }
                        if box_move_temps.contains(lhs_local) {
                            box_move_presentations.insert(lhs_local, presentation);
                            if let Some(lhs_slot) = self.slot_for_local(fn_did, lhs_local) {
                                self.transparent_move_edges.push((rhs_slot, lhs_slot));
                            }
                        }
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
                    let pointer_pair = matches!(
                        body.local_decls[rhs_local.expect("RHS local")].ty.kind(),
                        rustc_middle::ty::TyKind::RawPtr(..)
                    ) && matches!(
                        body.local_decls[lhs_local].ty.kind(),
                        rustc_middle::ty::TyKind::RawPtr(..)
                    );
                    let transparent = match rhs {
                        Rvalue::Use(_) => pointer_pair,
                        Rvalue::Cast(_, _, _) => pointer_pair,
                        _ => false,
                    };
                    self.construction_bridge_temps
                        .0
                        .push(ConstructionBridgeHop {
                            source: rhs_local.expect("RHS consume has a local"),
                            destination: lhs_local,
                            source_var: rhs_use,
                            destination_var: lhs_def,
                            location: location.into(),
                            transparent,
                            destination_single_def: !matches!(
                                sink_definitions[lhs_local],
                                Some(SinkCarrierDef::Multiple)
                            ),
                            block_single_predecessor: block.as_u32() == 0
                                || body.basic_blocks.predecessors()[block].len() == 1,
                        });
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
                let (arg_use, arg_def) = box_move_presentations
                    .get(*arg_local)
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
                        &sink_naming_temps,
                        &sink_definitions,
                        &sink_naming_presentations,
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
                        box_move_presentations
                            .get(arg_local)
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
            transparent_move_edges: self.transparent_move_edges,
            construction_bridge_temps: self.construction_bridge_temps,
            field_held: self.field_held,
            boundary_held: self.boundary_held,
        };
        facts
            .move_edges
            .sort_unstable_by_key(|(from, to)| (slot_order_key(*from), slot_order_key(*to)));
        facts.move_edges.dedup();
        facts
            .transparent_move_edges
            .sort_unstable_by_key(|(from, to)| (slot_order_key(*from), slot_order_key(*to)));
        facts.transparent_move_edges.dedup();
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

pub(crate) fn slot_label(slot: SlotRef) -> String {
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
    transparent_move_edges: Vec<(SlotRef, SlotRef)>,
    construction_bridge_temps: ConstructionBridgeTemps,
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
    /// The initializer carries the complete Box type for an unannotated source
    /// binding reached through the sealed construction-presentation domain.
    /// The AST planner therefore places value edits but no declaration splice.
    pub(crate) inferred_binding: bool,
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum BoxPlanFailure {
    PointerDepth,
    ParameterHeld,
    ConstructionUnmappable,
    ConstructionBridge(ConstructionBridgeFailure),
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
    pub(crate) fn key(&self) -> &'static str {
        match self {
            BoxPlanFailure::PointerDepth
            | BoxPlanFailure::ConstructionUnmappable
            | BoxPlanFailure::ConstructionBridge(_) => "box-construction-unmappable",
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

    pub(crate) fn detail(&self) -> String {
        match self {
            Self::ConstructionBridge(reason) => {
                format!("construction-bridge-{}", reason.key())
            }
            _ => "-".to_owned(),
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

    fn construction_bridge_for(
        &self,
        endpoint: &EndpointFact,
        subject: Local,
    ) -> Result<ConstructionBridgePresentation, ConstructionBridgeFailure> {
        let source_sites = self
            .version_sites
            .iter()
            .filter(|site| {
                site.function_path == endpoint.function_path
                    && site.relation == "call-destination"
                    && site.def_var == Some(endpoint.var)
            })
            .collect::<Vec<_>>();
        let [source_site] = source_sites.as_slice() else {
            return Err(if source_sites.is_empty() {
                ConstructionBridgeFailure::MissingVersionSite
            } else {
                ConstructionBridgeFailure::MultipleDefinitions
            });
        };
        resolve_construction_bridge(
            source_site.local,
            endpoint.var,
            subject,
            &self.construction_bridge_temps,
        )
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
        let construction_bridge = match (subject.ty_span, subject.pointee_span) {
            (Some(_), Some(_)) => None,
            (None, None) => {
                if active_sources.len() != 1 {
                    return Err(BoxPlanFailure::MoveAmbiguous);
                }
                Some(
                    self.construction_bridge_for(active_sources[0], subject.local)
                        .map_err(BoxPlanFailure::ConstructionBridge)?,
                )
            }
            _ => return Err(BoxPlanFailure::ConstructionUnmappable),
        };
        let construction_bridge_receipt = construction_bridge
            .as_ref()
            .map(|bridge| bridge.receipt(active_sources[0], slot));
        let inferred_binding = construction_bridge.is_some();
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
                receipts: construction_bridge_receipt
                    .into_iter()
                    .chain([format!(
                        "box-move-companion source={} destination={}",
                        upstream.label, subject.label
                    )])
                    .collect(),
                fabricated_extent: false,
                inferred_binding,
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
        if let Some(receipt) = construction_bridge_receipt {
            receipts.push(receipt);
        }
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
                    let reaching = subjects
                        .iter()
                        .filter_map(|candidate| {
                            let candidate_slot = subject_slot(candidate)?;
                            self.move_reaches(candidate_slot, sink_slot)
                                .then_some((candidate, candidate_slot))
                        })
                        .collect::<Vec<_>>();
                    let matched = reaching
                        .iter()
                        .filter(|(_, candidate_slot)| {
                            !reaching.iter().any(|(_, other_slot)| {
                                candidate_slot != other_slot
                                    && self.move_reaches(*candidate_slot, *other_slot)
                                    && self.move_reaches(*other_slot, sink_slot)
                            })
                        })
                        .map(|(candidate, _)| *candidate)
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
            inferred_binding,
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
        for &(from, to) in &self.transparent_move_edges {
            bytes.extend(
                format!(
                    "transparent-move\t{}\t{}\n",
                    slot_label(from),
                    slot_label(to)
                )
                .bytes(),
            );
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
            for &(_, next) in self
                .move_edges
                .iter()
                .chain(&self.transparent_move_edges)
                .filter(|(from, _)| *from == current)
            {
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
        BoxMoveTemps, BoxScopeFailure, ConstructionBridgeFailure, ConstructionBridgeHop,
        ConstructionBridgeTemps, EndpointStatus, FactValue, LocationKey, RecordedEquation,
        SinkCarrierDef, SinkCarrierReason, SinkNamingTemps, box_scope, classify_endpoint,
        exactly_one_sink_per_exit_graph, render_equations, replay_values,
        resolve_construction_bridge, resolve_sink_carrier, resolve_sink_naming_carrier,
        scalar_initializer_supported,
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
    fn box_n7_sink_naming_stops_before_move_domain_projection_base() {
        let sink_temp = rustc_middle::mir::Local::from_usize(10);
        let carrier = rustc_middle::mir::Local::from_usize(11);
        let mut definitions = IndexVec::from_elem_n(None, 12);
        definitions[sink_temp] = Some(SinkCarrierDef::Copy(carrier));
        definitions[carrier] = Some(SinkCarrierDef::Projected);

        let naming = SinkNamingTemps::from_seeds([sink_temp]);
        let moves = BoxMoveTemps::closed_from_seeds([sink_temp], &definitions, |_| true);
        assert!(naming.contains(sink_temp));
        assert!(!naming.contains(carrier));
        assert!(moves.contains(sink_temp));
        assert!(moves.contains(carrier));
        assert_eq!(
            resolve_sink_naming_carrier(sink_temp, &naming, &definitions),
            Ok(carrier),
            "the widened move domain must not drag endpoint naming into the carrier's projection-base definition"
        );
    }

    #[test]
    fn box2_w1_construction_bridge_follows_one_transparent_definition() {
        let source = rustc_middle::mir::Local::from_usize(9);
        let subject = rustc_middle::mir::Local::from_usize(8);
        let hops = ConstructionBridgeTemps::from_hops([ConstructionBridgeHop {
            source,
            destination: subject,
            source_var: var(1),
            destination_var: var(2),
            location: LocationKey {
                block: 2,
                statement: 2,
            },
            transparent: true,
            destination_single_def: true,
            block_single_predecessor: true,
        }]);

        let presentation = resolve_construction_bridge(source, var(1), subject, &hops)
            .expect("one transparent definition is an exact bridge");
        assert_eq!(presentation.source, source);
        assert_eq!(presentation.subject, subject);
        assert_eq!(presentation.hops.len(), 1);
    }

    #[test]
    fn box2_n1_nontransparent_construction_definition_fails_closed() {
        let source = rustc_middle::mir::Local::from_usize(9);
        let subject = rustc_middle::mir::Local::from_usize(8);
        let hops = ConstructionBridgeTemps::from_hops([ConstructionBridgeHop {
            source,
            destination: subject,
            source_var: var(1),
            destination_var: var(2),
            location: LocationKey {
                block: 2,
                statement: 2,
            },
            transparent: false,
            destination_single_def: true,
            block_single_predecessor: true,
        }]);
        assert_eq!(
            resolve_construction_bridge(source, var(1), subject, &hops),
            Err(ConstructionBridgeFailure::NonTransparentRvalue),
            "mutation killer: widening the bridge through a nontransparent definition must fail"
        );
    }

    #[test]
    fn box2_n2_multidef_and_join_fed_bridges_fail_closed() {
        let source = rustc_middle::mir::Local::from_usize(9);
        let subject = rustc_middle::mir::Local::from_usize(8);
        let hop = |destination_single_def, block_single_predecessor| ConstructionBridgeHop {
            source,
            destination: subject,
            source_var: var(1),
            destination_var: var(2),
            location: LocationKey {
                block: 2,
                statement: 2,
            },
            transparent: true,
            destination_single_def,
            block_single_predecessor,
        };
        assert_eq!(
            resolve_construction_bridge(
                source,
                var(1),
                subject,
                &ConstructionBridgeTemps::from_hops([hop(false, true)]),
            ),
            Err(ConstructionBridgeFailure::MultipleDefinitions),
        );
        assert_eq!(
            resolve_construction_bridge(
                source,
                var(1),
                subject,
                &ConstructionBridgeTemps::from_hops([hop(true, false)]),
            ),
            Err(ConstructionBridgeFailure::BranchOrJoinFed),
        );
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
