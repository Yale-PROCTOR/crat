//! Derive-on-load ownership facts used by Box emission.
//!
//! The production implementation is intentionally RED-first.  These tests pin
//! the conservative concrete replay before the frozen ownership emitter is
//! connected to it.

use rustc_hash::FxHashMap;
use rustc_index::IndexVec;
use rustc_middle::mir::{Body, Local, Location, Operand, Rvalue, StatementKind, TerminatorKind};
use rustc_span::def_id::LocalDefId;
use rustc_type_ir::TyKind::FnDef;
use sha2::{Digest, Sha256};

use crate::{
    analyses::borrow_ownership::{
        SlotKind,
        boundary_table::{self, Matcher, Role},
        crate_slots::CrateSlots,
        solver::SlotRef,
        ssa::constraint::Var,
    },
    utils::rustc::RustProgram,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FactValue {
    MustOwn,
    NotOwn,
    Unknown,
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
    pub(crate) final_kind: SlotKind,
    pub(crate) value: FactValue,
    pub(crate) status: EndpointStatus,
    pub(crate) unknown_reason: Option<String>,
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
}

impl SinkCarrierReason {
    fn key(self) -> &'static str {
        match self {
            SinkCarrierReason::MultiDef => "sink-carrier-multi-def",
            SinkCarrierReason::NonCopyDef => "sink-carrier-non-copy-def",
            SinkCarrierReason::ProjectionBase => "sink-carrier-projection-base",
            SinkCarrierReason::MissingDef => "sink-carrier-missing-def",
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
    slot: SlotRef,
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
                let Some(lhs_local) = lhs.as_local() else {
                    continue;
                };
                let rhs_operand = match rhs {
                    Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => Some(operand),
                    _ => None,
                };
                let rhs_local = rhs_operand
                    .and_then(Operand::place)
                    .and_then(|place| place.as_local());
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
                let Some((lhs_use, lhs_def, _)) = lhs_consume else {
                    continue;
                };
                self.equations.push(RecordedEquation::Assume {
                    var: lhs_use,
                    value: false,
                });
                if let (Some(operand), Some((rhs_use, rhs_def, _))) = (rhs_operand, rhs_consume) {
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
                let consume = arg
                    .node
                    .place()
                    .and_then(|place| place.as_local())
                    .and_then(|local| {
                        self.consume(
                            fn_did,
                            &function_path,
                            &mut current,
                            local,
                            location,
                            "call-argument",
                        )
                    });
                arg_consumes.push(consume);
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
                        slot,
                    });
                }
            }
            for (index, consume) in arg_consumes.into_iter().enumerate() {
                let Some((arg_use, arg_def, slot)) = consume else {
                    continue;
                };
                if is_sink && index == 0 {
                    self.equations.push(RecordedEquation::Assume {
                        var: arg_def,
                        value: false,
                    });
                    self.candidates.push(EndpointCandidate {
                        role: EndpointRole::Sink,
                        function_path: function_path.clone(),
                        location: location.into(),
                        callee: callee.clone().expect("sink callee"),
                        var: arg_use,
                        slot,
                    });
                } else if callee.is_none() {
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
            let value = match self.model.get(&candidate.slot) {
                Some(SlotKind::Owning) => FactValue::MustOwn,
                Some(SlotKind::Raw | SlotKind::Ref) => FactValue::NotOwn,
                None => FactValue::Unknown,
            };
            assign(&mut seeds, candidate.var, value)?;
        }

        let (values, replay_error) = match replay_values(seeds, &self.equations) {
            Ok(values) => (values, None),
            Err(error) => (
                IndexVec::from_raw(vec![FactValue::Unknown; self.next_var as usize]),
                Some(error),
            ),
        };
        let mut endpoints = Vec::with_capacity(self.candidates.len());
        for candidate in self.candidates {
            let final_kind = self
                .model
                .get(&candidate.slot)
                .copied()
                .ok_or_else(|| format!("Box endpoint model lacks slot {:?}", candidate.slot))?;
            let value = values[candidate.var];
            let status = classify_endpoint(value, final_kind);
            endpoints.push(EndpointFact {
                role: candidate.role,
                function_path: candidate.function_path,
                location: candidate.location,
                callee: candidate.callee,
                var: candidate.var,
                slot: slot_label(candidate.slot),
                final_kind,
                value,
                status,
                unknown_reason: (status == EndpointStatus::Unknown).then(|| {
                    replay_error
                        .clone()
                        .unwrap_or_else(|| "constraint-underdetermined".to_owned())
                }),
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
        };
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

#[derive(Clone, Debug)]
pub(crate) struct BoxOwnershipFacts {
    equations: Vec<RecordedEquation>,
    version_sites: Vec<VersionSite>,
    endpoints: Vec<EndpointFact>,
    replay_error: Option<String>,
    canonical_sha256: String,
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
        bytes
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
                SlotKind::Ref => "Ref",
                SlotKind::Raw => "Raw",
                SlotKind::Owning => "Owning",
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
        EndpointStatus, FactValue, RecordedEquation, SinkCarrierDef, SinkCarrierReason,
        classify_endpoint, render_equations, replay_values, resolve_sink_carrier,
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
}
