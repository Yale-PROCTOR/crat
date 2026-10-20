//! Retirement-only closed return evidence. R294 RED stub: no certificate is issued.
//!
//! The existing NB5-O may-relations are candidate/evidence links, never CLOSED
//! certificates. This module changes neither that analysis nor object factories.

use rustc_hash::FxHashMap;
use rustc_middle::mir::{Local, Location};
use rustc_span::def_id::LocalDefId;

use crate::{
    analyses::{
        borrow_ownership::origin_flow::OriginFlowResults,
        mir::{CallKind, MirFunctionCall},
    },
    utils::rustc::RustProgram,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ClosedOrigin {
    /// Every admitted non-null return was born during this invocation.
    /// This is not a claim that the allocation is still live at every later use.
    Fresh,
    /// The returned object's identity is that of this formal MIR local's value.
    /// MIR argument locals are one-based; Local(0) is not an input.
    Input(Local),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Certificate {
    pub(crate) origin: ClosedOrigin,
    /// The producer admits a null alternative. This flag is not a null origin,
    /// and false is not an independent non-null proof for a substituted input.
    pub(crate) nullable: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Rejection {
    MissingNativeFlow,
    MissingCertificate,
    UnsupportedReturnType,
    NoNormalReturn,
    NullOnly,
    UnknownDefinition,
    MayEvidence,
    MixedOrigins,
    RecursiveCall,
    UnsupportedProjection,
    AggregateOrGlobal,
    AddressOfLocal,
    Promoted,
    Arithmetic,
    UnsupportedCast,
    ForeignCall,
    IndirectCall,
    UnsupportedLocalCallee,
    InvalidInputParameter,
    MissingActualArgument,
    UnsupportedActual,
    EscapedOrWrittenCarrier,
}

pub(crate) type CertificateMap = FxHashMap<LocalDefId, Result<Certificate, Rejection>>;

mod producer {
    use std::collections::VecDeque;

    use rustc_hash::FxHashMap;
    use rustc_middle::{
        mir::{
            BasicBlock, Body, CastKind, Const, Local, Operand, Place, Rvalue, START_BLOCK,
            StatementKind, TerminatorKind,
        },
        ty::{Ty, TyKind},
    };
    use rustc_span::def_id::LocalDefId;

    use crate::{
        analyses::{
            borrow_ownership::{
                origin_flow::OriginFlowResults,
                origin_summary::SignatureRoot,
                retirement::return_origin::{
                    Certificate, CertificateMap, ClosedOrigin, Rejection, direct_callee,
                    input_argument_index,
                },
                source_events,
            },
            mir::{CallGraphPostOrder, CallKind, MirFunctionCall, TerminatorExt},
        },
        utils::rustc::RustProgram,
    };

    /// This finite abstract domain keeps no set of every possible origin. Two distinct
    /// non-null origins are already outside the admitted singleton contract.
    /// Null is an alternative, never an origin or the unreachable bottom.
    /// Rejection reasons are diagnostic: their merge need not be canonical;
    /// every rejected value denies the certificate regardless of that reason.
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Value {
        Null,
        Known(Certificate),
        Rejected(Rejection),
    }

    impl Value {
        fn known(origin: ClosedOrigin, nullable: bool) -> Self {
            Self::Known(Certificate { origin, nullable })
        }

        fn join(self, other: Self) -> Self {
            use Value::{Known, Null, Rejected};
            if self == other {
                return self;
            }
            match (self, other) {
                (Null, Known(mut value)) | (Known(mut value), Null) => {
                    value.nullable = true;
                    Known(value)
                }
                (Known(left), Known(right)) if left.origin == right.origin => {
                    Self::known(left.origin, left.nullable || right.nullable)
                }
                (Known(_), Known(_)) => Rejected(Rejection::MixedOrigins),
                (Rejected(Rejection::MixedOrigins), _) | (_, Rejected(Rejection::MixedOrigins)) => {
                    Rejected(Rejection::MixedOrigins)
                }
                (Rejected(reason), Null) | (Null, Rejected(reason)) => Rejected(reason),
                (Rejected(_), _) | (_, Rejected(_)) => Rejected(Rejection::MayEvidence),
                (Null, Null) => Null,
            }
        }

        fn nullable(self, nullable: bool) -> Self {
            if nullable {
                self.join(Self::Null)
            } else {
                self
            }
        }

        fn finish(self) -> Result<Certificate, Rejection> {
            match self {
                Self::Known(value) => Ok(value),
                Self::Null => Err(Rejection::NullOnly),
                Self::Rejected(reason) => Err(reason),
            }
        }
    }

    struct Layout {
        indices: Vec<Option<usize>>,
        locals: Vec<Local>,
    }

    fn pointer(ty: Ty<'_>) -> bool {
        matches!(ty.kind(), TyKind::RawPtr(..))
    }

    impl Layout {
        fn new(body: &Body<'_>) -> Self {
            let mut indices = vec![None; body.local_decls.len()];
            let mut locals = Vec::new();
            for local in body.local_decls.indices() {
                if pointer(body.local_decls[local].ty) {
                    indices[local.as_usize()] = Some(locals.len());
                    locals.push(local);
                }
            }
            Self { indices, locals }
        }

        fn index(&self, local: Local) -> Option<usize> {
            self.indices.get(local.as_usize()).copied().flatten()
        }
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct State {
        values: Vec<Value>,
        /// Exposure belongs to the carrier's storage, not its current value.
        /// Strong writes and StorageLive/Dead never clear this conservative bit.
        exposed: Vec<bool>,
    }

    impl State {
        fn initial(body: &Body<'_>, layout: &Layout) -> Self {
            let values = layout
                .locals
                .iter()
                .map(|&local| {
                    if local.as_usize() > 0 && local.as_usize() <= body.arg_count {
                        Value::known(ClosedOrigin::Input(local), false)
                    } else {
                        Value::Rejected(Rejection::UnknownDefinition)
                    }
                })
                .collect();
            Self {
                values,
                exposed: vec![false; layout.locals.len()],
            }
        }

        fn join(&mut self, other: &Self) -> bool {
            let mut changed = false;
            for (value, incoming) in self.values.iter_mut().zip(&other.values) {
                let merged = value.join(*incoming);
                changed |= merged != *value;
                *value = merged;
            }
            for (exposed, incoming) in self.exposed.iter_mut().zip(&other.exposed) {
                changed |= *incoming && !*exposed;
                *exposed |= *incoming;
            }
            changed
        }

        fn havoc_exposed(&mut self) {
            for (value, exposed) in self.values.iter_mut().zip(&self.exposed) {
                if *exposed {
                    *value = Value::Rejected(Rejection::EscapedOrWrittenCarrier);
                }
            }
        }

        fn read(&self, layout: &Layout, place: Place<'_>) -> Value {
            let Some(local) = place.as_local() else {
                return Value::Rejected(Rejection::UnsupportedProjection);
            };
            layout
                .index(local)
                .map(|index| self.values[index])
                .unwrap_or(Value::Rejected(Rejection::UnknownDefinition))
        }

        fn write(&mut self, layout: &Layout, place: Place<'_>, value: Value) {
            let Some(local) = place.as_local() else {
                // An indirect write may change any address-exposed local cell.
                // It does not change an unexposed local's pointer value merely
                // by writing the object that value addresses.
                self.havoc_exposed();
                return;
            };
            if let Some(index) = layout.index(local) {
                self.values[index] = value;
            }
        }
    }

    fn operand<'tcx>(
        program: &RustProgram<'tcx>,
        state: &State,
        layout: &Layout,
        value: &Operand<'tcx>,
    ) -> Value {
        match value {
            Operand::Copy(place) | Operand::Move(place) => state.read(layout, *place),
            Operand::Constant(constant) => {
                if source_events::operand_is_null(value, &[], program.tcx) {
                    Value::Null
                } else if matches!(&constant.const_, Const::Unevaluated(value, _) if value.promoted.is_some())
                {
                    Value::Rejected(Rejection::Promoted)
                } else {
                    Value::Rejected(Rejection::AggregateOrGlobal)
                }
            }
        }
    }

    fn statement<'tcx>(
        program: &RustProgram<'tcx>,
        layout: &Layout,
        state: &mut State,
        statement: &StatementKind<'tcx>,
    ) {
        match statement {
            StatementKind::Assign(box (destination, rvalue)) => {
                if let Rvalue::Ref(_, _, addressed) | Rvalue::RawPtr(_, addressed) = rvalue {
                    if let Some(local) = addressed.as_local()
                        && let Some(index) = layout.index(local)
                    {
                        state.exposed[index] = true;
                    }
                }
                let value = match rvalue {
                    Rvalue::Use(value) | Rvalue::Cast(CastKind::PtrToPtr, value, _) => {
                        operand(program, state, layout, value)
                    }
                    Rvalue::Cast(_, value @ Operand::Constant(_), _)
                        if source_events::operand_is_null(value, &[], program.tcx) =>
                    {
                        Value::Null
                    }
                    Rvalue::Cast(..) => Value::Rejected(Rejection::UnsupportedCast),
                    Rvalue::CopyForDeref(place) => state.read(layout, *place),
                    Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                        Value::Rejected(if place.projection.is_empty() {
                            Rejection::AddressOfLocal
                        } else {
                            Rejection::UnsupportedProjection
                        })
                    }
                    Rvalue::BinaryOp(..) | Rvalue::UnaryOp(..) => {
                        Value::Rejected(Rejection::Arithmetic)
                    }
                    Rvalue::Aggregate(..) | Rvalue::Repeat(..) | Rvalue::ThreadLocalRef(..) => {
                        Value::Rejected(Rejection::AggregateOrGlobal)
                    }
                    _ => Value::Rejected(Rejection::UnknownDefinition),
                };
                state.write(layout, *destination, value);
            }
            StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
                if let Some(index) = layout.index(*local) {
                    state.values[index] = Value::Rejected(Rejection::UnknownDefinition);
                }
            }
            StatementKind::Deinit(place) | StatementKind::SetDiscriminant { place, .. } => {
                state.write(
                    layout,
                    **place,
                    Value::Rejected(Rejection::UnknownDefinition),
                );
            }
            StatementKind::Intrinsic(..) => state.havoc_exposed(),
            _ => {}
        }
    }

    fn null_constructor(program: &RustProgram<'_>, call: &MirFunctionCall<'_, '_>) -> bool {
        matches!(&call.func, CallKind::RustLib(did)
            if program.tcx.crate_name(did.krate).as_str() == "core"
                && program.tcx.def_path_str(*did).contains("::ptr::")
                && matches!(program.tcx.item_name(*did).as_str(), "null" | "null_mut"))
    }

    fn call_value<'tcx>(
        program: &RustProgram<'tcx>,
        layout: &Layout,
        state: &State,
        call: &MirFunctionCall<'_, 'tcx>,
        certificates: &CertificateMap,
    ) -> Value {
        if matches!(&call.func, CallKind::LibC(name)
            if matches!(name.as_str(), "malloc" | "calloc" | "strdup"))
        {
            return Value::known(ClosedOrigin::Fresh, true);
        }
        if null_constructor(program, call) {
            return Value::Null;
        }
        let callee = match direct_callee(program, call) {
            Ok(callee) => callee,
            Err(reason) => return Value::Rejected(reason),
        };
        let certificate = match certificates.get(&callee).copied() {
            Some(Ok(certificate)) => certificate,
            Some(Err(reason)) => return Value::Rejected(reason),
            None => return Value::Rejected(Rejection::MissingCertificate),
        };
        match certificate.origin {
            ClosedOrigin::Fresh => Value::known(ClosedOrigin::Fresh, certificate.nullable),
            ClosedOrigin::Input(parameter) => {
                let index = match input_argument_index(parameter) {
                    Ok(index) => index,
                    Err(reason) => return Value::Rejected(reason),
                };
                let Some(actual) = call.args.get(index) else {
                    return Value::Rejected(Rejection::MissingActualArgument);
                };
                operand(program, state, layout, &actual.node).nullable(certificate.nullable)
            }
        }
    }

    fn self_call(program: &RustProgram<'_>, function: LocalDefId) -> bool {
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        body.basic_blocks.iter().any(|block| {
            block
                .terminator()
                .as_call(program.tcx)
                .and_then(|call| direct_callee(program, &call).ok())
                == Some(function)
        })
    }

    fn analyze<'tcx>(
        program: &RustProgram<'tcx>,
        function: LocalDefId,
        certificates: &CertificateMap,
        origin_flows: &OriginFlowResults,
    ) -> Result<Certificate, Rejection> {
        let body = program
            .tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        if !pointer(body.local_decls[rustc_middle::mir::RETURN_PLACE].ty) {
            return Err(Rejection::UnsupportedReturnType);
        }
        let layout = Layout::new(&body);
        let mut entries: Vec<Option<State>> = vec![None; body.basic_blocks.len()];
        entries[START_BLOCK.as_usize()] = Some(State::initial(&body, &layout));
        let mut queue = VecDeque::from([START_BLOCK]);
        let mut queued = vec![false; body.basic_blocks.len()];
        queued[START_BLOCK.as_usize()] = true;
        while let Some(block) = queue.pop_front() {
            queued[block.as_usize()] = false;
            let data = &body.basic_blocks[block];
            let mut state = entries[block.as_usize()]
                .clone()
                .expect("queued reachable state");
            for item in &data.statements {
                statement(program, &layout, &mut state, &item.kind);
            }
            let terminator = data.terminator();
            if matches!(
                &terminator.kind,
                TerminatorKind::InlineAsm { .. }
                    | TerminatorKind::Yield { .. }
                    | TerminatorKind::TailCall { .. }
            ) {
                // These can hide effects or a normal-return alternative outside
                // the admitted grammar. Do not ignore them beside another Return.
                return Err(Rejection::UnknownDefinition);
            }
            let call = terminator.as_call(program.tcx);
            if let Some(call) = &call
                && let Ok(callee) = direct_callee(program, call)
                && matches!(
                    certificates.get(&callee),
                    Some(Err(Rejection::RecursiveCall))
                )
            {
                return Err(Rejection::RecursiveCall);
            }
            // Snapshot the returned Input operand before ALL call effects,
            // including those of an already-certified direct local callee.
            let returned = call
                .as_ref()
                .map(|call| call_value(program, &layout, &state, call, certificates));
            for successor in terminator.successors() {
                let mut outgoing = state.clone();
                if call.is_some() || matches!(&terminator.kind, TerminatorKind::Drop { .. }) {
                    outgoing.havoc_exposed();
                }
                let normal = matches!(&terminator.kind,
                    TerminatorKind::Call { target: Some(target), .. } if *target == successor);
                if normal && let (Some(call), Some(value)) = (&call, returned) {
                    outgoing.write(&layout, call.destination, value);
                }
                let changed = match &mut entries[successor.as_usize()] {
                    Some(previous) => previous.join(&outgoing),
                    slot @ None => {
                        *slot = Some(outgoing);
                        true
                    }
                };
                if changed && !queued[successor.as_usize()] {
                    queued[successor.as_usize()] = true;
                    queue.push_back(successor);
                }
            }
        }
        // Inspect only converged reachable Return states: no first-path or
        // worklist-intermediate state can issue a CLOSED certificate.
        let mut returned: Option<Value> = None;
        for (block, data) in body.basic_blocks.iter_enumerated() {
            if !matches!(&data.terminator().kind, TerminatorKind::Return) {
                continue;
            }
            let Some(mut state) = entries[block.as_usize()].clone() else { continue };
            for item in &data.statements {
                statement(program, &layout, &mut state, &item.kind);
            }
            let value = state.read(&layout, Place::return_place());
            returned = Some(returned.map_or(value, |prior| prior.join(value)));
        }
        let certificate = returned.ok_or(Rejection::NoNormalReturn)?.finish()?;
        if let ClosedOrigin::Input(parameter) = certificate.origin {
            // Corroboration only. This MAY edge did not establish closure: the
            // explicit, exhaustive current-definition proof above already did.
            let summary = &origin_flows
                .get(&function)
                .ok_or(Rejection::MissingNativeFlow)?
                .summary;
            let returned = summary.slots.iter_enumerated().find_map(|(id, slot)| {
                (slot.place.root == SignatureRoot::Return
                    && slot.place.deref_depth == 0
                    && slot.place.field.is_none()
                    && slot.depth == 0)
                    .then_some(id)
            });
            let input = summary.slots.iter_enumerated().find_map(|(id, slot)| {
                (slot.place.root == SignatureRoot::Arg(parameter)
                    && slot.place.deref_depth == 0
                    && slot.place.field.is_none()
                    && slot.depth == 0)
                    .then_some(id)
            });
            if !matches!((input, returned), (Some(input), Some(returned))
                if summary.value_flows.contains(input, returned))
            {
                return Err(Rejection::MayEvidence);
            }
        }
        Ok(certificate)
    }

    pub(crate) fn derive(
        program: &RustProgram<'_>,
        origin_flows: &OriginFlowResults,
    ) -> CertificateMap {
        let mut certificates = FxHashMap::default();
        // Finite callee postorder; no recursive expansion and no NB5-O rerun.
        // Even apparently singleton/empty recursive MAY summaries remain closed
        // to this producer. Its certificate is not a termination proof.
        let order = CallGraphPostOrder::new(program);
        for component in order.sccs() {
            let recursive = component.len() > 1
                || component
                    .first()
                    .is_some_and(|function| self_call(program, function.expect_local()));
            for function in component {
                let function = function.expect_local();
                let result = if !origin_flows.contains_key(&function) {
                    Err(Rejection::MissingNativeFlow)
                } else if recursive {
                    Err(Rejection::RecursiveCall)
                } else {
                    analyze(program, function, &certificates, origin_flows)
                };
                certificates.insert(function, result);
            }
        }
        certificates
    }
}

pub(crate) fn derive(
    program: &RustProgram<'_>,
    origin_flows: &OriginFlowResults,
) -> CertificateMap {
    crate::analyses::borrow_ownership::retirement::return_origin::producer::derive(
        program,
        origin_flows,
    )
}

/// Resolve only an actual local body represented in the admitted program.
/// Foreign/library and unresolved calls do not inherit a similarly named body.
pub(crate) fn direct_callee(
    program: &RustProgram<'_>,
    call: &MirFunctionCall<'_, '_>,
) -> Result<LocalDefId, Rejection> {
    match &call.func {
        CallKind::FreeStanding(callee) | CallKind::Impl(callee)
            if program.functions.contains(callee) =>
        {
            Ok(*callee)
        }
        CallKind::FreeStanding(_) | CallKind::Impl(_) => Err(Rejection::UnsupportedLocalCallee),
        CallKind::LibC(_) | CallKind::RustLib(_) => Err(Rejection::ForeignCall),
        CallKind::Closure | CallKind::Dynamic => Err(Rejection::IndirectCall),
    }
}

pub(crate) fn for_call(
    program: &RustProgram<'_>,
    certificates: &CertificateMap,
    call: &MirFunctionCall<'_, '_>,
) -> Result<Certificate, Rejection> {
    let callee = direct_callee(program, call)?;
    certificates
        .get(&callee)
        .copied()
        .unwrap_or(Err(Rejection::MissingCertificate))
}

pub(crate) fn input_argument_index(parameter: Local) -> Result<usize, Rejection> {
    parameter
        .as_u32()
        .checked_sub(1)
        .map(|index| index as usize)
        .ok_or(Rejection::InvalidInputParameter)
}

#[cfg(test)]
use crate::analyses::borrow_ownership::retirement::objects::ObjectSet;

/// Test-only branch evidence. Object construction stays in objects::call_effect;
/// this receipt receives the actual selected destination set from that branch.
#[cfg(test)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct TransferReceipt {
    pub(crate) caller: LocalDefId,
    pub(crate) callee: Option<LocalDefId>,
    pub(crate) location: Location,
    pub(crate) normal: bool,
    pub(crate) certificate: Result<Certificate, Rejection>,
    pub(crate) argument_index: Option<usize>,
    pub(crate) destination_objects: ObjectSet,
}

#[cfg(test)]
std::thread_local! {
    static TRANSFER_RECEIPTS: std::cell::RefCell<Option<Vec<TransferReceipt>>> =
        const { std::cell::RefCell::new(None) };
}

/// Disabled by default, including in the cfg(test) corpus worker binary.
/// The closure avoids constructing/cloning a receipt unless a test opts in.
#[cfg(test)]
pub(crate) fn record_transfer(make: impl FnOnce() -> TransferReceipt) {
    TRANSFER_RECEIPTS.with(|current| {
        if let Some(rows) = current.borrow_mut().as_mut() {
            rows.push(make());
        }
    });
}

#[cfg(test)]
pub(crate) fn with_transfer_receipts<T>(f: impl FnOnce() -> T) -> (T, Vec<TransferReceipt>) {
    struct Restore(Option<Vec<TransferReceipt>>);
    impl Drop for Restore {
        fn drop(&mut self) {
            TRANSFER_RECEIPTS.with(|current| {
                current.replace(self.0.take());
            });
        }
    }
    let previous = TRANSFER_RECEIPTS.with(|current| current.replace(Some(Vec::new())));
    let restore = Restore(previous);
    let value = f();
    let receipts = TRANSFER_RECEIPTS
        .with(|current| current.replace(None))
        .unwrap_or_default();
    drop(restore);
    (value, receipts)
}
