//! Bounded whole-body transport, followed by a conservative full-object scan.
//! Unioning all definitions deliberately refuses ambiguous generations. It is
//! not a reaching-definition or loan-liveness replacement. Evidence is valid
//! only for the recorded one-base/index-only component and MIR body snapshot.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use rustc_hir::def_id::LocalDefId;
use rustc_middle::{
    mir::{
        self, Body, Local, Location, Operand, Place, Rvalue, StatementKind, TerminatorKind,
        visit::{PlaceContext, Visitor},
    },
    ty::{self, Ty, TyCtxt},
};

use super::{
    Admission, Candidate, Finding, ModelKind, Need, Outcome, Predicate, Shape, Site, Status,
    Unsupported,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Root {
    Array(Local),
    Slice(Local),
    Parameter(Local),
    Table(Local),
    Projection(Local),
    Opaque(Local),
}

#[derive(Clone, Default)]
struct Node {
    roots: BTreeSet<Root>,
    parents: BTreeSet<Local>,
    copies: BTreeSet<Local>,
    nullable: bool,
    layout_changed: bool,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Method {
    Pointer,
    Slice,
    Null,
    Observe,
    Wrapping,
    Unsupported,
}

fn element(ty: Ty<'_>) -> Option<Ty<'_>> {
    let pointee = match ty.kind() {
        ty::RawPtr(pointee, _) | ty::Ref(_, pointee, _) => *pointee,
        _ => return None,
    };
    Some(match pointee.kind() {
        ty::Array(t, _) | ty::Slice(t) => *t,
        _ => pointee,
    })
}

fn method<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    func: &Operand<'tcx>,
    receiver: Option<&Operand<'tcx>>,
) -> Method {
    let ty::FnDef(did, _) = *func.ty(&body.local_decls, tcx).kind() else {
        return Method::Unsupported;
    };
    let krate = tcx.crate_name(did.krate);
    if did.is_local() || !matches!(krate.as_str(), "core" | "std") {
        return Method::Unsupported;
    }
    let name = tcx.item_name(did);
    if matches!(name.as_str(), "null" | "null_mut") {
        return Method::Null;
    }
    let Some(receiver) = receiver else { return Method::Unsupported };
    let receiver_ty = receiver.ty(&body.local_decls, tcx);
    match (name.as_str(), receiver_ty.kind()) {
        (
            "wrapping_add"
            | "wrapping_sub"
            | "wrapping_offset"
            | "wrapping_byte_add"
            | "wrapping_byte_sub"
            | "wrapping_byte_offset",
            ty::RawPtr(..),
        ) => Method::Wrapping,
        ("add" | "sub" | "offset", ty::RawPtr(..)) => Method::Pointer,
        ("as_ptr" | "as_mut_ptr", ty::Ref(_, t, _))
            if matches!(t.kind(), ty::Array(..) | ty::Slice(..)) =>
        {
            Method::Slice
        }
        ("is_null", ty::RawPtr(..)) => Method::Observe,
        _ => Method::Unsupported,
    }
}

fn reject(finding: &mut Finding, outcome: Outcome, site: Location) {
    // Findings accumulate: a later missing fact must not erase an unsupported
    // storage/layout operation already observed elsewhere in the component.
    let rank = |outcome| match outcome {
        Outcome::Proven => 0,
        Outcome::Missing(_) => 1,
        Outcome::Unsupported(_) => 2,
    };
    if rank(outcome) > rank(finding.outcome) {
        finding.outcome = outcome;
        finding.site = Some(at(site));
    }
}

fn at(location: Location) -> Site {
    Site {
        block: location.block.index(),
        statement: location.statement_index,
    }
}

#[derive(Default)]
struct Places<'tcx> {
    rows: Vec<(Place<'tcx>, PlaceContext, Location)>,
}
impl<'tcx> Visitor<'tcx> for Places<'tcx> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        self.rows.push((*place, context, location));
        self.super_place(place, context, location);
    }
}

/// Graph reachability has at most one visit per MIR block. Same-block backwards
/// reachability requires a real CFG cycle, never statement-index wraparound.
fn reaches(body: &Body<'_>, from: Location, to: Location) -> bool {
    if from.block == to.block && from.statement_index < to.statement_index {
        return true;
    }
    let mut queue = VecDeque::from_iter(body.basic_blocks[from.block].terminator().successors());
    let mut seen = BTreeSet::new();
    while let Some(block) = queue.pop_front() {
        if block == to.block {
            return true;
        }
        if seen.insert(block) {
            queue.extend(body.basic_blocks[block].terminator().successors());
        }
    }
    false
}

fn dominates(body: &Body<'_>, definition: Location, use_site: Location) -> bool {
    if definition.block == use_site.block {
        return definition.statement_index <= use_site.statement_index;
    }
    let mut queue = VecDeque::from([mir::START_BLOCK]);
    let mut seen = BTreeSet::new();
    while let Some(block) = queue.pop_front() {
        if block == definition.block {
            continue;
        }
        if block == use_site.block {
            return false;
        }
        if seen.insert(block) {
            queue.extend(body.basic_blocks[block].terminator().successors());
        }
    }
    true
}

fn zero(operand: &Operand<'_>) -> bool {
    matches!(operand, Operand::Constant(value) if value.const_.try_to_scalar()
        .and_then(|scalar| scalar.try_to_scalar_int().ok())
        .is_some_and(|int| int.to_bits(int.size()) == 0))
}

fn operand_source(node: &mut Node, operand: &Operand<'_>, destination: Local, body: &Body<'_>) {
    match operand.place() {
        Some(place) if place.projection.is_empty() => {
            node.parents.insert(place.local);
        }
        Some(place) => {
            let table = place.projection.len() == 1
                && place.is_indirect()
                && matches!(body.local_decls[place.local].ty.kind(), ty::RawPtr(t, _) if matches!(t.kind(), ty::RawPtr(..)));
            node.roots.insert(if table {
                Root::Table(destination)
            } else {
                Root::Projection(destination)
            });
        }
        None => {
            node.roots.insert(Root::Opaque(destination));
        }
    }
}

pub(super) fn inspect<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    body: &Body<'tcx>,
    candidate: Candidate,
    kinds: &BTreeMap<Local, ModelKind>,
) -> Admission {
    let mut nodes = vec![Node::default(); body.local_decls.len()];
    let mut null_tests = Vec::new();
    let mut lends = BTreeMap::<Local, Vec<Location>>::new();
    let mut definitions = BTreeMap::<Local, Vec<(Location, bool)>>::new();
    for local in body.args_iter() {
        let root = match body.local_decls[local].ty.kind() {
            ty::RawPtr(..) => Root::Parameter(local),
            ty::Ref(_, t, _) if matches!(t.kind(), ty::Array(..) | ty::Slice(..)) => {
                Root::Slice(local)
            }
            _ => continue,
        };
        nodes[local.index()].roots.insert(root);
    }
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, statement) in data.statements.iter().enumerate() {
            let location = Location {
                block,
                statement_index,
            };
            let StatementKind::Assign(assignment) = &statement.kind else { continue };
            let (destination, value) = &**assignment;
            let Some(dest) = destination.as_local() else { continue };
            definitions.entry(dest).or_default().push((
                location,
                matches!(value, Rvalue::Aggregate(..) | Rvalue::Repeat(..)),
            ));
            if element(body.local_decls[dest].ty).is_none() {
                continue;
            }
            let node = &mut nodes[dest.index()];
            match value {
                Rvalue::Use(operand) | Rvalue::Cast(_, operand, _)
                    if matches!(body.local_decls[dest].ty.kind(), ty::RawPtr(..))
                        && zero(operand) =>
                {
                    node.nullable = true;
                }
                Rvalue::Use(operand) => {
                    if let Some(place) = operand.place()
                        && place.projection.is_empty()
                    {
                        node.copies.insert(place.local);
                    }
                    operand_source(node, operand, dest, body);
                }
                Rvalue::Cast(_, operand, target)
                    if element(operand.ty(&body.local_decls, tcx)).is_some() =>
                {
                    node.layout_changed |=
                        element(operand.ty(&body.local_decls, tcx)) != element(*target);
                    if let Some(place) = operand.place()
                        && place.projection.is_empty()
                    {
                        node.copies.insert(place.local);
                    }
                    operand_source(node, operand, dest, body);
                }
                Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                    if place.projection.is_empty()
                        && matches!(body.local_decls[place.local].ty.kind(), ty::Array(..))
                    {
                        node.roots.insert(Root::Array(place.local));
                        lends.entry(place.local).or_default().push(location);
                    } else if place.is_indirect()
                        && matches!(body.local_decls[place.local].ty.kind(), ty::Ref(..))
                    {
                        node.parents.insert(place.local);
                    } else {
                        node.roots.insert(Root::Opaque(dest));
                    }
                }
                _ => {
                    node.roots.insert(Root::Opaque(dest));
                }
            }
        }
        if let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &data.terminator().kind
        {
            let operation = method(tcx, body, func, args.first().map(|a| &a.node));
            if operation == Method::Observe
                && let Some(receiver) = args.first().and_then(|arg| arg.node.place())
                && receiver.projection.is_empty()
            {
                nodes[receiver.local.index()].nullable = true;
                null_tests.push(receiver.local);
            }
            let Some(dest) = destination.as_local() else { continue };
            if element(body.local_decls[dest].ty).is_none() {
                continue;
            }
            let node = &mut nodes[dest.index()];
            match operation {
                Method::Null => node.nullable = true,
                Method::Pointer | Method::Slice => operand_source(node, &args[0].node, dest, body),
                _ => {
                    node.roots.insert(Root::Opaque(dest));
                }
            }
        }
    }
    // A native is_null receiver is commonly a copy temporary. Attribute the
    // observation backwards through copies/casts, not through displacement or
    // memory-load edges; literal-null values still flow forwards below.
    let mut observed = BTreeSet::new();
    while let Some(local) = null_tests.pop() {
        if observed.insert(local) {
            nodes[local.index()].nullable = true;
            null_tests.extend(nodes[local.index()].copies.iter().copied());
        }
    }
    // Finite monotone transport: each root/flag enters each local at most once.
    // Worklist propagation cannot manufacture a root for an unseeded cycle.
    let mut children = vec![Vec::new(); nodes.len()];
    for (child, node) in nodes.iter().enumerate() {
        for parent in &node.parents {
            children[parent.index()].push(child);
        }
    }
    let mut queue = VecDeque::from_iter(0..nodes.len());
    while let Some(parent) = queue.pop_front() {
        for &child in &children[parent] {
            let prior = (
                nodes[child].roots.len(),
                nodes[child].nullable,
                nodes[child].layout_changed,
            );
            let roots = nodes[parent].roots.clone();
            nodes[child].roots.extend(roots);
            nodes[child].nullable |= nodes[parent].nullable;
            nodes[child].layout_changed |= nodes[parent].layout_changed;
            if prior
                != (
                    nodes[child].roots.len(),
                    nodes[child].nullable,
                    nodes[child].layout_changed,
                )
            {
                queue.push_back(child);
            }
        }
    }
    let node = &nodes[candidate.local.index()];
    let shape = if node.roots.len() > 1 {
        Shape::MultipleRoots
    } else {
        match node.roots.first() {
            Some(Root::Array(_)) => Shape::LocalArray,
            Some(Root::Slice(_)) => Shape::BorrowedSlice,
            Some(Root::Parameter(_)) => Shape::RawParameter,
            Some(Root::Table(_)) => Shape::PointerTableLoad,
            Some(Root::Projection(_)) => Shape::ProjectionLoad,
            _ if node.roots.is_empty() && node.nullable => Shape::NullOnly,
            _ => Shape::Opaque,
        }
    };
    let component: Vec<_> = body
        .local_decls
        .indices()
        .filter(|local| !nodes[local.index()].roots.is_disjoint(&node.roots))
        .collect();
    let mut report = Admission {
        owner,
        local: candidate.local,
        shape,
        status: Status::NeedsFact,
        nullable: node.nullable,
        component: component.clone(),
        base_elements: None,
        findings: [
            (Predicate::RetainedBase, Need::BaseOrigin),
            (Predicate::GenerationWindow, Need::Generation),
            (Predicate::RawEntryPrefix, Need::Prefix),
            (Predicate::FullRegionSchedule, Need::Schedule),
        ]
        .map(|(predicate, need)| Finding {
            predicate,
            outcome: Outcome::Missing(need),
            root: None,
            site: None,
        }),
    };
    if shape == Shape::BorrowedSlice {
        report.findings[1].outcome = Outcome::Missing(Need::WindowCoverage);
    }
    if candidate.slot_depth != 0
        || !matches!(body.local_decls[candidate.local].ty.kind(), ty::RawPtr(..))
    {
        report.findings[0].outcome = Outcome::Unsupported(Unsupported::PointerDepth);
    } else if candidate.model_kind != ModelKind::Ref
        || component.iter().any(|local| {
            matches!(body.local_decls[*local].ty.kind(), ty::RawPtr(..))
                && kinds.get(local) != Some(&ModelKind::Ref)
        })
    {
        report.findings[0].outcome = Outcome::Missing(Need::RefAdmission);
    } else if shape == Shape::LocalArray {
        let Root::Array(root) = *node.roots.first().unwrap() else { unreachable!() };
        derive_array(
            tcx,
            body,
            root,
            &component,
            &nodes,
            &lends,
            &definitions,
            &mut report,
        );
    }
    report.status = if report
        .findings
        .iter()
        .any(|f| matches!(f.outcome, Outcome::Unsupported(_)))
    {
        Status::OutOfScope
    } else if report.findings.iter().all(|f| f.outcome == Outcome::Proven) {
        Status::DecisionOnly
    } else {
        Status::NeedsFact
    };
    report
}

fn derive_array<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    root: Local,
    component: &[Local],
    nodes: &[Node],
    lends: &BTreeMap<Local, Vec<Location>>,
    definitions: &BTreeMap<Local, Vec<(Location, bool)>>,
    report: &mut Admission,
) {
    let origins = &lends[&root];
    let origin = origins[0];
    for finding in &mut report.findings {
        finding.root = Some(root);
        finding.site = Some(at(origin));
        finding.outcome = Outcome::Proven;
    }
    let ty::Array(elem, len) = *body.local_decls[root].ty.kind() else { unreachable!() };
    report.base_elements = len.try_to_target_usize(tcx);
    let typing_env = ty::TypingEnv::post_analysis(tcx, body.source.def_id());
    let layout_ok = tcx
        .layout_of(typing_env.as_query_input(elem))
        .is_ok_and(|layout| layout.size.bytes() != 0)
        && !matches!(elem.kind(), ty::RawPtr(..) | ty::Ref(..) | ty::Adt(..))
        && !component
            .iter()
            .any(|local| nodes[local.index()].layout_changed);
    if !layout_ok {
        report.findings[0].outcome = Outcome::Unsupported(Unsupported::Layout);
    }
    let initializations = definitions.get(&root).map(Vec::as_slice).unwrap_or(&[]);
    let mut places = Places::default();
    places.visit_body(body);
    let uses: Vec<_> = places
        .rows
        .iter()
        .filter(|(place, context, _)| {
            component.contains(&place.local) && !matches!(context, PlaceContext::NonUse(_))
        })
        .map(|(_, _, site)| *site)
        .collect();
    match initializations {
        [(initialization, true)]
            if origins
                .iter()
                .chain(&uses)
                .all(|site| dominates(body, *initialization, *site)) =>
        {
            // The proposed base is formed immediately after initialization,
            // before the statement at this boundary. Unlike origins[0], this
            // boundary dominates both branches of an if/else extraction.
            report.findings[3].site = Some(at(Location {
                block: initialization.block,
                statement_index: initialization.statement_index + 1,
            }));
            if reaches(body, *initialization, *initialization) {
                report.findings[1].outcome = Outcome::Missing(Need::Generation);
            }
        }
        [] => reject(
            &mut report.findings[0],
            Outcome::Missing(Need::Initialization),
            origin,
        ),
        _ => report.findings[1].outcome = Outcome::Missing(Need::Generation),
    }
    if component
        .iter()
        .any(|local| nodes[local.index()].roots != BTreeSet::from([Root::Array(root)]))
    {
        report.findings[1].outcome = Outcome::Missing(Need::Generation);
    }
    for (place, context, site) in &places.rows {
        if place.local == root
            && !matches!(context, PlaceContext::NonUse(_))
            && !origins.contains(site)
            && !initializations.iter().any(|(init, _)| init == site)
        {
            reject(
                &mut report.findings[3],
                Outcome::Missing(Need::Schedule),
                *site,
            );
        }
    }
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, statement) in data.statements.iter().enumerate() {
            let site = Location {
                block,
                statement_index,
            };
            if matches!(statement.kind, StatementKind::StorageDead(local) if local == root)
                && uses.iter().any(|use_site| reaches(body, site, *use_site))
            {
                report.findings[1].outcome = Outcome::Missing(Need::Generation);
                report.findings[1].site = Some(at(site));
            }
            if let StatementKind::Assign(assignment) = &statement.kind {
                let (destination, value) = &**assignment;
                if let Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) = value
                    && component.contains(&place.local)
                {
                    let outcome = if place.projection.is_empty() {
                        Outcome::Unsupported(Unsupported::EscapedStorage)
                    } else {
                        Outcome::Missing(Need::Schedule)
                    };
                    reject(&mut report.findings[3], outcome, site);
                }
                if matches!(value, Rvalue::Cast(_, operand, _) if operand.place().is_some_and(|p| component.contains(&p.local)) && element(destination.ty(&body.local_decls, tcx).ty).is_none())
                {
                    reject(
                        &mut report.findings[3],
                        Outcome::Unsupported(Unsupported::Operation),
                        site,
                    );
                }
                let mut operands = Places::default();
                operands.visit_rvalue(value, site);
                let uses_component = operands
                    .rows
                    .iter()
                    .any(|(place, _, _)| component.contains(&place.local));
                let supported = match value {
                    Rvalue::Use(operand) => operand.place().is_some_and(|place| {
                        place.is_indirect()
                            || (destination.as_local().is_some()
                                && element(destination.ty(&body.local_decls, tcx).ty).is_some())
                    }),
                    Rvalue::Cast(_, _, target) => element(*target).is_some(),
                    Rvalue::BinaryOp(op, _) => matches!(
                        op,
                        mir::BinOp::Eq
                            | mir::BinOp::Ne
                            | mir::BinOp::Lt
                            | mir::BinOp::Le
                            | mir::BinOp::Gt
                            | mir::BinOp::Ge
                    ),
                    Rvalue::Len(_) => true,
                    // Aggregates, Repeat, raw address formation, references to
                    // storage, and every unhandled transport fail closed at
                    // the source use, before a later hidden escape is lost.
                    _ => false,
                };
                if uses_component && !supported {
                    reject(
                        &mut report.findings[3],
                        Outcome::Missing(Need::Schedule),
                        site,
                    );
                }
            }
        }
        let site = Location {
            block,
            statement_index: data.statements.len(),
        };
        match &data.terminator().kind {
            TerminatorKind::Call { func, args, .. }
                if args.iter().any(|arg| {
                    arg.node
                        .place()
                        .is_some_and(|p| component.contains(&p.local))
                }) =>
            {
                match method(tcx, body, func, args.first().map(|a| &a.node)) {
                    Method::Wrapping => reject(
                        &mut report.findings[3],
                        Outcome::Unsupported(Unsupported::Operation),
                        site,
                    ),
                    Method::Unsupported => reject(
                        &mut report.findings[3],
                        Outcome::Missing(Need::Schedule),
                        site,
                    ),
                    _ => {}
                }
            }
            TerminatorKind::Return if component.contains(&mir::RETURN_PLACE) => {
                reject(
                    &mut report.findings[3],
                    Outcome::Missing(Need::Schedule),
                    site,
                );
            }
            TerminatorKind::InlineAsm { .. }
            | TerminatorKind::TailCall { .. }
            | TerminatorKind::Yield { .. } => {
                reject(
                    &mut report.findings[3],
                    Outcome::Unsupported(Unsupported::Operation),
                    site,
                );
            }
            _ => {}
        }
    }
}
