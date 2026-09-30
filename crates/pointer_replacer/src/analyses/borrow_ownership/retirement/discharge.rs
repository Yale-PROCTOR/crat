//! L01¹⁰ (R602-1 / R603-2; the record
//! `docs/agents/plan/2026-09-28-retirement-effective-type-discharge.md`): two
//! discharges of a retirement conflict raised by a `Free` / `ReallocOld` whose
//! object the overlap analysis cannot place.
//!
//! (α) the post-free use, unconditional: every path from the event reaches, in
//! the conflict's own frame, a load or store through the reference (or a
//! single-definition copy of it) before the frame returns. An overlapping free
//! would make that access a use-after-free of the input, which §28 excludes.
//!
//! (β) the effective type, behind `CRAT_ERA5C_TYPED_RELEASE` (the premise
//! `TypedReleaseDiscipline`, R603-1, the user's): the freed allocation's type P
//! (recovered from the freed operand backwards through pointer casts and
//! single-definition copies, and along the event's route from a routed
//! callee's parameter to the caller's actual) and the referent's type T are
//! object types other than `void` / character / union / zero-sized, and
//! neither contains the other by value under structural C compatibility.
//!
//! Everything here is computed from MIR when the scope begins; the review
//! only looks it up.

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::{
    mir::{
        BasicBlock, Body, CastKind, Local, Location, Operand, Place, ProjectionElem, Rvalue,
        StatementKind, TerminatorKind,
        visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor},
    },
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_span::def_id::LocalDefId;

use super::routes::{FrameEvent, RouteStep, RoutedEvents};
use crate::analyses::borrow_ownership::{
    export::{PlaceKey, ProjKey},
    source_events::{SourceObject, SourceRole},
};

/// `CRAT_ERA5C_TYPED_RELEASE` (on|off, fail-loud): (β), resting on the premise.
pub(crate) fn typed_release() -> bool {
    static ONCE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ONCE.get_or_init(|| match std::env::var("CRAT_ERA5C_TYPED_RELEASE") {
        Err(std::env::VarError::NotPresent) => false,
        Ok(value) => match value.as_str() {
            "on" => true,
            "off" => false,
            other => panic!("CRAT_ERA5C_TYPED_RELEASE must be on or off; got {other:?}"),
        },
        Err(error) => panic!("CRAT_ERA5C_TYPED_RELEASE is not valid Unicode: {error}"),
    })
}

fn switch(name: &'static str, cell: &'static std::sync::OnceLock<bool>) -> bool {
    *cell.get_or_init(|| match std::env::var(name) {
        Err(std::env::VarError::NotPresent) => false,
        Ok(value) => match value.as_str() {
            "on" => true,
            "off" => false,
            other => panic!("{name} must be on or off; got {other:?}"),
        },
        Err(error) => panic!("{name} is not valid Unicode: {error}"),
    })
}

/// `CRAT_ERA5C_RETIRE_FRESH` (on|off, fail-loud): **L01¹¹ (γ)** (R659-1, the
/// record `docs/agents/plan/2026-09-29-retirement-fresh-and-interior-release-discharge.md`
/// §2): the released block is an allocation made inside the route.
pub(crate) fn retire_fresh() -> bool {
    static ONCE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    switch("CRAT_ERA5C_RETIRE_FRESH", &ONCE)
}

/// `CRAT_ERA5C_RETIRE_ROUTE_USE` (on|off, fail-loud): **L01¹¹ (α⁺)** (the record
/// §3): the referent is used after the release, in a frame of the route.
pub(crate) fn retire_route_use() -> bool {
    static ONCE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    switch("CRAT_ERA5C_RETIRE_ROUTE_USE", &ONCE)
}

/// `CRAT_ERA5C_TYPED_SOLE` (on|off, fail-loud): **L01¹¹ (β′)** (the record §4),
/// with (β): pointer element types are typed, and the containment refusal fires
/// only when P contains T or T is P-only.
pub(crate) fn typed_sole() -> bool {
    static ONCE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    switch("CRAT_ERA5C_TYPED_SOLE", &ONCE)
}

/// `CRAT_ERA5C_ALPHA_RETURNS` (on|off, fail-loud): **L01¹¹, R666-1**. (α)
/// discharges only when every route frame below the conflict frame returns
/// normally (or uses the referent) on every path after the release: a callee that
/// releases and then diverges never reaches the conflict frame's later use.
pub(crate) fn alpha_returns() -> bool {
    static ONCE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    switch("CRAT_ERA5C_ALPHA_RETURNS", &ONCE)
}

/// W71's faults (test builds only): `no-fresh`, `no-route-use`, `no-sole`.
fn w71_fault(name: &str) -> bool {
    cfg!(test) && std::env::var("CRAT_E5C_W71_FAULT").ok().as_deref() == Some(name)
}

/// W66's fault: `no-discharge` gives today's conflicts back.
pub(crate) fn w66_fault(name: &str) -> bool {
    std::env::var("CRAT_E5C_W66_FAULT").ok().as_deref() == Some(name)
}

/// A lifetime-free C view of a type: enough for compatibility and containment.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum CTy {
    Void,
    Char,
    Scalar(String),
    Ptr(Box<CTy>),
    Array(Box<CTy>, u64),
    Tuple(Vec<CTy>),
    /// A struct or union, by its definition path (the table holds its shape).
    Adt(String),
    Other(String),
}

/// An integer scalar's name without its signedness (`i32` and `u32` are both
/// `32`); any other scalar keeps its name.
fn signedness_twin(name: &str) -> &str {
    match name.strip_prefix('i').or_else(|| name.strip_prefix('u')) {
        Some(width) if width == "size" || width.parse::<u32>().is_ok() => width,
        _ => name,
    }
}

/// R609-3 (the A5 type route, under R542): two pointees that are object types
/// (not `void`, character, a union, zero-sized or opaque) and of which neither
/// contains the other by value, under the same structural compatibility as (β)
/// (tag and members, never a definition identity), cannot overlap. Their names
/// when so; `None` otherwise.
pub(crate) fn disjoint_pointees<'tcx>(
    tcx: TyCtxt<'tcx>,
    left: Ty<'tcx>,
    right: Ty<'tcx>,
) -> Option<(String, String)> {
    let mut types = Types::default();
    let (a, b) = (types.of(tcx, left), types.of(tcx, right));
    (types.typed(&a) && types.typed(&b) && !types.contains(&a, &b, 0) && !types.contains(&b, &a, 0))
        .then(|| (types.name(&a), types.name(&b)))
}

#[derive(Clone, Debug)]
struct AdtShape {
    name: String,
    union: bool,
    fields: Vec<(String, CTy)>,
}

#[derive(Default)]
struct Types {
    adts: FxHashMap<String, AdtShape>,
    /// (β′): a pointer to anything but `void` / `char` is a typed element.
    pointers: bool,
}

impl Types {
    fn of<'tcx>(&mut self, tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> CTy {
        match ty.kind() {
            TyKind::RawPtr(pointee, _) | TyKind::Ref(_, pointee, _) => {
                CTy::Ptr(Box::new(self.of(tcx, *pointee)))
            }
            TyKind::Int(rustc_middle::ty::IntTy::I8)
            | TyKind::Uint(rustc_middle::ty::UintTy::U8) => CTy::Char,
            TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_) | TyKind::Bool => {
                CTy::Scalar(format!("{ty:?}"))
            }
            TyKind::Array(element, length) => CTy::Array(
                Box::new(self.of(tcx, *element)),
                length.try_to_target_usize(tcx).unwrap_or(u64::MAX),
            ),
            TyKind::Tuple(types) => CTy::Tuple(types.iter().map(|t| self.of(tcx, t)).collect()),
            TyKind::Adt(adt, args) if adt.is_struct() || adt.is_union() => {
                let name = tcx.item_name(adt.did()).to_string();
                if name == "c_void" {
                    return CTy::Void;
                }
                let key = format!("{}{:?}", tcx.def_path_str(adt.did()), args);
                if !self.adts.contains_key(&key) {
                    self.adts.insert(
                        key.clone(),
                        AdtShape {
                            name: name.clone(),
                            union: adt.is_union(),
                            fields: Vec::new(),
                        },
                    );
                    let fields = adt
                        .non_enum_variant()
                        .fields
                        .iter()
                        .map(|field| (field.name.to_string(), self.of(tcx, field.ty(tcx, args))))
                        .collect();
                    self.adts.get_mut(&key).expect("inserted").fields = fields;
                }
                CTy::Adt(key)
            }
            _ => CTy::Other(format!("{ty:?}")),
        }
    }

    fn name(&self, ty: &CTy) -> String {
        match ty {
            CTy::Void => "void".into(),
            CTy::Char => "char".into(),
            CTy::Scalar(s) | CTy::Other(s) => s.clone(),
            CTy::Ptr(p) => format!("*{}", self.name(p)),
            CTy::Array(e, n) => format!("[{}; {n}]", self.name(e)),
            CTy::Tuple(ts) => format!(
                "({})",
                ts.iter()
                    .map(|t| self.name(t))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            CTy::Adt(key) => self
                .adts
                .get(key)
                .map_or(key.clone(), |adt| adt.name.clone()),
        }
    }

    /// C compatibility, structurally: the same tag and members (never by
    /// definition identity), guarded for recursive pointer structure.
    fn compatible(&self, a: &CTy, b: &CTy, seen: &mut FxHashSet<(String, String)>) -> bool {
        match (a, b) {
            (CTy::Void, CTy::Void) | (CTy::Char, CTy::Char) => true,
            // §6.5p7: an object may be accessed through the signed or unsigned
            // type corresponding to its own, so those pairs are not disjoint.
            (CTy::Scalar(x), CTy::Scalar(y)) => x == y || signedness_twin(x) == signedness_twin(y),
            (CTy::Other(x), CTy::Other(y)) => x == y,
            (CTy::Ptr(x), CTy::Ptr(y)) => self.compatible(x, y, seen),
            (CTy::Array(x, n), CTy::Array(y, m)) => n == m && self.compatible(x, y, seen),
            (CTy::Tuple(xs), CTy::Tuple(ys)) => {
                xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| self.compatible(x, y, seen))
            }
            (CTy::Adt(x), CTy::Adt(y)) => {
                if x == y || !seen.insert((x.clone(), y.clone())) {
                    return true;
                }
                let (Some(p), Some(q)) = (self.adts.get(x), self.adts.get(y)) else {
                    return false;
                };
                p.name == q.name
                    && p.union == q.union
                    && p.fields.len() == q.fields.len()
                    && p.fields
                        .iter()
                        .zip(&q.fields)
                        .all(|((m, s), (n, t))| m == n && self.compatible(s, t, seen))
            }
            _ => false,
        }
    }

    /// `outer` contains `inner` by value: it is compatible with it, or a field
    /// or element of it does. A union contains anything (never discharges).
    fn contains(&self, outer: &CTy, inner: &CTy, depth: usize) -> bool {
        if depth > 64 || self.compatible(outer, inner, &mut FxHashSet::default()) {
            return true;
        }
        match outer {
            CTy::Adt(key) => match self.adts.get(key) {
                None => true,
                Some(adt) if adt.union => true,
                Some(adt) => adt
                    .fields
                    .iter()
                    .any(|(_, field)| self.contains(field, inner, depth + 1)),
            },
            CTy::Array(element, _) => self.contains(element, inner, depth + 1),
            CTy::Tuple(types) => types.iter().any(|t| self.contains(t, inner, depth + 1)),
            _ => false,
        }
    }

    /// An object type (β) may reason about: not `void` / character / union,
    /// not zero-sized, not an opaque type.
    fn typed(&self, ty: &CTy) -> bool {
        match ty {
            CTy::Ptr(pointee) => self.pointers && !matches!(**pointee, CTy::Void | CTy::Char),
            CTy::Void | CTy::Char | CTy::Other(_) => false,
            CTy::Array(element, length) => *length > 0 && self.typed_member(element),
            CTy::Adt(key) => self
                .adts
                .get(key)
                .is_some_and(|adt| !adt.union && !adt.fields.is_empty()),
            CTy::Scalar(_) | CTy::Tuple(_) => true,
        }
    }

    /// (β′): `outer` consists only of values compatible with `p`, so it could
    /// sit in a block holding only P values. A union or an opaque type is
    /// treated as P-only (never discharges).
    fn sole(&self, outer: &CTy, p: &CTy, depth: usize) -> bool {
        if depth > 64 || self.compatible(outer, p, &mut FxHashSet::default()) {
            return true;
        }
        match outer {
            CTy::Adt(key) => match self.adts.get(key) {
                None => true,
                Some(adt) if adt.union => true,
                Some(adt) => adt.fields.iter().all(|(_, f)| self.sole(f, p, depth + 1)),
            },
            CTy::Array(element, _) => self.sole(element, p, depth + 1),
            CTy::Tuple(types) => types.iter().all(|t| self.sole(t, p, depth + 1)),
            CTy::Other(_) => true,
            _ => false,
        }
    }

    fn typed_member(&self, ty: &CTy) -> bool {
        !matches!(ty, CTy::Void | CTy::Char | CTy::Other(_))
    }

    fn pointee(&self, ty: &CTy) -> Option<CTy> {
        match ty {
            CTy::Ptr(p) => Some((**p).clone()),
            _ => None,
        }
    }

    fn project(&self, ty: &CTy, proj: &ProjKey) -> Option<CTy> {
        match (ty, proj) {
            (CTy::Ptr(p), ProjKey::Deref) => Some((**p).clone()),
            (CTy::Adt(key), ProjKey::Field(index)) => self
                .adts
                .get(key)
                .and_then(|adt| adt.fields.get(*index as usize))
                .map(|(_, t)| t.clone()),
            (CTy::Tuple(ts), ProjKey::Field(index)) => ts.get(*index as usize).cloned(),
            (
                CTy::Array(e, _),
                ProjKey::Index(_) | ProjKey::ConstantIndex { .. } | ProjKey::Subslice { .. },
            ) => Some((**e).clone()),
            _ => None,
        }
    }
}

/// The referent of a conflict's target.
pub(crate) enum Target<'a> {
    /// A protected entry: the parameter local at its depth.
    Entry { parameter: Local, depth: u8 },
    /// A live loan: the borrowed place.
    Loan { borrowed: &'a PlaceKey },
    /// An inner holder: a local at its depth.
    Inner { local: Local, depth: u8 },
}

impl Target<'_> {
    fn base(&self) -> Option<Local> {
        match self {
            Target::Entry {
                parameter,
                depth: 0,
            } => Some(*parameter),
            Target::Loan { borrowed } => Some(borrowed.local),
            _ => None,
        }
    }
}

/// What the review needs, keyed by the event context.
pub(crate) type EventKey = super::ContextKey;

#[derive(Default)]
pub(crate) struct Discharges {
    types: Types,
    locals: FxHashMap<(LocalDefId, Local), CTy>,
    reassigned: FxHashSet<(LocalDefId, Local)>,
    freed: std::collections::BTreeMap<EventKey, Option<CTy>>,
    after: std::collections::BTreeMap<EventKey, FxHashSet<Local>>,
    /// (γ): the allocation a released value comes from, and the frame it was
    /// made in, when the walk reaches one.
    fresh: std::collections::BTreeMap<EventKey, Option<(String, LocalDefId)>>,
    /// (α⁺): the route's frames, bottom (the releasing function) to top (the
    /// conflict frame).
    chains: std::collections::BTreeMap<EventKey, Vec<RouteFrame>>,
}

/// One frame of a release's route, for (α⁺).
struct RouteFrame {
    function: LocalDefId,
    /// Locals accessed (`*local`) on every path from the release (or the
    /// routed call's return) before this frame returns.
    accessed: FxHashSet<Local>,
    /// Locals such that every path either accesses them or returns normally;
    /// `None` is every local (every path returns normally).
    accessed_or_returned: Option<FxHashSet<Local>>,
    /// Every path returns normally.
    returns: bool,
    /// For the step from this frame's caller: the caller's local behind each
    /// formal (`formal index -> caller local`), folded through copies, casts
    /// and reborrows. Empty for the conflict frame.
    formals_from_caller: FxHashMap<usize, Local>,
}

/// One discharged conflict, for the receipt.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Rule {
    PostFreeUse {
        local: u32,
    },
    /// `sole`: the discharge needed (β′) (a pointer element type, or a
    /// referent that contains P but is not P-only).
    EffectiveType {
        freed: String,
        referent: String,
        sole: bool,
    },
    /// (γ): the released value is `allocation`, made inside the route.
    FreshInRoute {
        allocation: String,
    },
    /// (α⁺): the referent is used through `_local` in `frame` after the release.
    PostReleaseUseRoute {
        frame: String,
        local: u32,
    },
}

impl Discharges {
    pub(crate) fn analyze<'tcx>(
        tcx: TyCtxt<'tcx>,
        routed: &RoutedEvents,
        functions: &std::collections::BTreeMap<String, LocalDefId>,
    ) -> Self {
        let mut out = Self::default();
        out.types.pointers = typed_sole() && !w71_fault("no-sole");
        let mut bodies = FxHashSet::default();
        for events in routed.frames.values() {
            for event in events {
                if !matches!(
                    event.source.key.role,
                    SourceRole::Free | SourceRole::ReallocOld
                ) {
                    continue;
                }
                let key = super::context_key(
                    &event.source.key,
                    event.frame,
                    event.location,
                    event.phase,
                    &event.route,
                );
                for function in std::iter::once(event.frame)
                    .chain(event.route.iter().flat_map(|s| [s.caller, s.callee]))
                    .chain(functions.get(&event.source.key.function).copied())
                {
                    if bodies.insert(function) {
                        out.index_body(tcx, function);
                    }
                }
                let freed = out.recover_freed(tcx, event, functions);
                out.freed.insert(key.clone(), freed);
                let body = tcx
                    .mir_drops_elaborated_and_const_checked(event.frame)
                    .borrow();
                let after = accessed_after(&body, event.location, event.frame, &out.reassigned);
                out.after.insert(key.clone(), after);
                if retire_fresh() && !w71_fault("no-fresh") {
                    let fresh = out.fresh_release(tcx, event, functions);
                    out.fresh.insert(key.clone(), fresh);
                }
                if (retire_route_use() && !w71_fault("no-route-use") || alpha_returns())
                    && let Some(chain) = out.route_chain(tcx, event, functions)
                {
                    out.chains.insert(key, chain);
                }
            }
        }
        out
    }

    fn index_body<'tcx>(&mut self, tcx: TyCtxt<'tcx>, function: LocalDefId) {
        let body = tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        for (local, decl) in body.local_decls.iter_enumerated() {
            let ty = self.types.of(tcx, decl.ty);
            self.locals.insert((function, local), ty);
        }
        let mut defs: FxHashMap<Local, usize> = FxHashMap::default();
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                if let StatementKind::Assign(assign) = &statement.kind
                    && assign.0.projection.is_empty()
                {
                    *defs.entry(assign.0.local).or_default() += 1;
                }
            }
            if let TerminatorKind::Call { destination, .. } = &data.terminator().kind
                && destination.projection.is_empty()
            {
                *defs.entry(destination.local).or_default() += 1;
            }
        }
        // A parameter is defined by the call alone; any other local by one
        // assignment. More than that is a reassignment.
        for (local, count) in defs {
            let parameter = local.as_usize() >= 1 && local.as_usize() <= body.arg_count;
            if count > usize::from(!parameter) {
                self.reassigned.insert((function, local));
            }
        }
    }

    /// P: the freed operand walked back to the first pointer to an object type.
    fn recover_freed<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        event: &FrameEvent,
        functions: &std::collections::BTreeMap<String, LocalDefId>,
    ) -> Option<CTy> {
        let SourceObject::HeapThrough(start) = &event.source.object else {
            return None;
        };
        let function = *functions.get(&event.source.key.function)?;
        self.recover(tcx, event.frame, function, start.clone(), &event.route)
    }

    /// The walk itself: from `place` in `function`, up `route` (inner to
    /// outer), never past `frame`'s own parameters.
    pub(crate) fn recover<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        frame: LocalDefId,
        mut function: LocalDefId,
        mut place: PlaceKey,
        route: &[RouteStep],
    ) -> Option<CTy> {
        for _ in 0..64 {
            let body = tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            let mut ty = self.types.of(tcx, body.local_decls[place.local].ty);
            for projection in &place.proj {
                ty = self.types.project(&ty, projection)?;
            }
            if let Some(pointee) = self.types.pointee(&ty)
                && self.types.typed(&pointee)
            {
                return Some(pointee);
            }
            // A `void *` / `char *` loaded from memory carries no type.
            if !place.proj.is_empty() {
                return None;
            }
            let local = place.local;
            if local.as_usize() >= 1 && local.as_usize() <= body.arg_count {
                // A parameter: up the route to the caller's actual, never past
                // the conflict's own frame (the route's head).
                if function == frame {
                    return None;
                }
                let step: &RouteStep = route.iter().find(|s| s.callee == function)?;
                let caller = tcx
                    .mir_drops_elaborated_and_const_checked(step.caller)
                    .borrow();
                let data = &caller.basic_blocks[step.location.block];
                let TerminatorKind::Call { args, .. } = &data.terminator().kind else {
                    return None;
                };
                let operand = &args.get(local.as_usize() - 1)?.node;
                let (Operand::Copy(p) | Operand::Move(p)) = operand else {
                    return None;
                };
                place = PlaceKey::from_place(*p);
                function = step.caller;
                continue;
            }
            // One definition: a copy, or a pointer-to-pointer cast.
            let mut found = None;
            let mut count = 0;
            for data in body.basic_blocks.iter() {
                for statement in &data.statements {
                    let StatementKind::Assign(assign) = &statement.kind else { continue };
                    if assign.0.local != local || !assign.0.projection.is_empty() {
                        continue;
                    }
                    count += 1;
                    found = match &assign.1 {
                        Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                        | Rvalue::Cast(
                            CastKind::PtrToPtr | CastKind::PointerCoercion(..),
                            Operand::Copy(p) | Operand::Move(p),
                            _,
                        ) => Some(*p),
                        _ => None,
                    };
                }
                if let TerminatorKind::Call { destination, .. } = &data.terminator().kind
                    && destination.local == local
                {
                    count += 1;
                    found = None;
                }
            }
            if count != 1 {
                return None;
            }
            place = PlaceKey::from_place(found?);
        }
        None
    }

    /// (γ): walk the released value back (copies, casts, up the route, as
    /// `recover` does) to its definition. An allocator's result, or a local
    /// producer's that returns only fresh blocks, is the allocation; the frame
    /// it was made in comes with it. A load from memory, a parameter of the
    /// conflict frame, or any other definition ends the walk with `None`.
    fn fresh_release<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        event: &FrameEvent,
        functions: &std::collections::BTreeMap<String, LocalDefId>,
    ) -> Option<(String, LocalDefId)> {
        let SourceObject::HeapThrough(start) = &event.source.object else {
            return None;
        };
        let mut function = *functions.get(&event.source.key.function)?;
        let mut place = start.clone();
        for _ in 0..64 {
            if !place.proj.is_empty() {
                return None;
            }
            let body = tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            let local = place.local;
            if local.as_usize() >= 1 && local.as_usize() <= body.arg_count {
                if function == event.frame {
                    return None;
                }
                let step: &RouteStep = event.route.iter().find(|s| s.callee == function)?;
                let caller = tcx
                    .mir_drops_elaborated_and_const_checked(step.caller)
                    .borrow();
                let TerminatorKind::Call { args, .. } =
                    &caller.basic_blocks[step.location.block].terminator().kind
                else {
                    return None;
                };
                let (Operand::Copy(p) | Operand::Move(p)) = &args.get(local.as_usize() - 1)?.node
                else {
                    return None;
                };
                place = PlaceKey::from_place(*p);
                function = step.caller;
                continue;
            }
            match single_definition(&body, local)? {
                Definition::Copy(p) => place = PlaceKey::from_place(p),
                Definition::Call(callee, first) => {
                    let name = tcx.item_name(callee).to_string();
                    let allocated = match name.as_str() {
                        "malloc" | "calloc" | "aligned_alloc" | "strdup" | "strndup" => true,
                        // `realloc` may return its old block: fresh only when
                        // the old block is (its first argument, walked the same way).
                        "realloc" => {
                            first.is_some_and(|old| fresh_value(tcx, function, &body, old, 0))
                        }
                        _ => callee.as_local().is_some_and(|f| returns_fresh(tcx, f, 0)),
                    };
                    return allocated
                        .then(|| (format!("{name}@{}", tcx.def_path_str(function)), function));
                }
            }
        }
        None
    }

    /// (α⁺): the route's frames with what each guarantees after the release.
    fn route_chain<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        event: &FrameEvent,
        functions: &std::collections::BTreeMap<String, LocalDefId>,
    ) -> Option<Vec<RouteFrame>> {
        let releasing = *functions.get(&event.source.key.function)?;
        let mut chain = Vec::new();
        // The bottom frame, from the release itself.
        let (mut function, mut start) = (
            releasing,
            Location {
                block: BasicBlock::from_usize(event.source.key.block as usize),
                statement_index: event.source.key.statement as usize,
            },
        );
        let mut steps = event.route.iter();
        loop {
            let body = tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            let (accessed, accessed_or_returned, returns) =
                after_frame(&body, start, function, &self.reassigned);
            let step = steps.next();
            let formals_from_caller = match step {
                Some(step) => formals_from(tcx, step)?,
                None => FxHashMap::default(),
            };
            chain.push(RouteFrame {
                function,
                accessed,
                accessed_or_returned,
                returns,
                formals_from_caller,
            });
            let Some(step) = step else { break };
            function = step.caller;
            start = step.location;
        }
        (chain.last().map(|f| f.function) == Some(event.frame)).then_some(chain)
    }

    /// T: the referent's type.
    fn referent(&self, frame: LocalDefId, target: &Target<'_>) -> Option<CTy> {
        match target {
            Target::Entry { parameter, depth }
            | Target::Inner {
                local: parameter,
                depth,
            } => {
                let mut ty = self.locals.get(&(frame, *parameter))?.clone();
                for _ in 0..=*depth {
                    ty = self.types.pointee(&ty)?;
                }
                Some(ty)
            }
            Target::Loan { borrowed } => {
                let mut ty = self.locals.get(&(frame, borrowed.local))?.clone();
                for projection in &borrowed.proj {
                    ty = self.types.project(&ty, projection)?;
                }
                Some(ty)
            }
        }
    }

    /// The discharge of one would-be conflict, (α) first, then (β) if enabled.
    pub(crate) fn discharge(&self, event: &FrameEvent, target: &Target<'_>) -> Option<Rule> {
        if w66_fault("no-discharge") {
            return None;
        }
        let key = super::context_key(
            &event.source.key,
            event.frame,
            event.location,
            event.phase,
            &event.route,
        );
        if let Some(base) = target.base()
            && !self.reassigned.contains(&(event.frame, base))
            && self.after.get(&key).is_some_and(|set| set.contains(&base))
            // R666-1: every route frame below returns (or uses the referent).
            && (!alpha_returns()
                || w71_fault("no-alpha-returns")
                || self.chains.get(&key).is_some_and(|chain| {
                    let pointer = pointers(chain, base);
                    below(chain, &pointer, chain.len() - 1)
                }))
        {
            return Some(Rule::PostFreeUse {
                local: base.as_u32(),
            });
        }
        if retire_route_use()
            && !w71_fault("no-route-use")
            && let Some(base) = target.base()
            && !self.reassigned.contains(&(event.frame, base))
            && let Some(chain) = self.chains.get(&key)
            && let Some((frame, local)) = route_use(chain, base)
        {
            return Some(Rule::PostReleaseUseRoute {
                frame: format!("{frame:?}"),
                local: local.as_u32(),
            });
        }
        if let Some(Some((allocation, made_in))) = self.fresh.get(&key)
            && (*made_in != event.frame || matches!(target, Target::Entry { .. }))
        {
            return Some(Rule::FreshInRoute {
                allocation: allocation.clone(),
            });
        }
        if !typed_release() {
            return None;
        }
        let freed = self.freed.get(&key)?.as_ref()?;
        let referent = self.referent(event.frame, target)?;
        let sole = self.types.pointers;
        if !self.types.typed(freed)
            || !self.types.typed(&referent)
            || self.types.contains(freed, &referent, 0)
            || if sole {
                self.types.sole(&referent, freed, 0)
            } else {
                self.types.contains(&referent, freed, 0)
            }
        {
            return None;
        }
        // The receipt names a discharge the unsharpened (β) would have refused.
        let needed_sole = sole
            && (matches!(freed, CTy::Ptr(_))
                || matches!(referent, CTy::Ptr(_))
                || self.types.contains(&referent, freed, 0));
        Some(Rule::EffectiveType {
            freed: self.types.name(freed),
            referent: self.types.name(&referent),
            sole: needed_sole,
        })
    }

    /// Why a would-be conflict is or is not discharged (the printer's column).
    pub(crate) fn explain(&self, event: &FrameEvent, target: &Target<'_>) -> String {
        let key = super::context_key(
            &event.source.key,
            event.frame,
            event.location,
            event.phase,
            &event.route,
        );
        let freed = self.freed.get(&key).and_then(Option::as_ref);
        let referent = self.referent(event.frame, target);
        let name = |t: Option<&CTy>| t.map_or("none".to_owned(), |t| self.types.name(t));
        let verdict = match (freed, referent.as_ref()) {
            (None, _) => "no-P",
            (_, None) => "no-T",
            (Some(p), Some(t)) if !self.types.typed(p) || !self.types.typed(t) => {
                "void/char/union/zst"
            }
            (Some(p), Some(t))
                if self.types.contains(p, t, 0)
                    || if self.types.pointers {
                        self.types.sole(t, p, 0)
                    } else {
                        self.types.contains(t, p, 0)
                    } =>
            {
                "contains"
            }
            _ if !typed_release() => "typed-release-off",
            _ => "disjoint",
        };
        format!(
            "P={} T={} verdict={verdict}",
            name(freed),
            name(referent.as_ref())
        )
    }

    /// The type table, for a census that walks without a routed event.
    pub(crate) fn name_of(&self, ty: &CTy) -> String {
        self.types.name(ty)
    }

    /// The freed type recovered for an event, for the printer.
    pub(crate) fn freed_name(&self, event: &FrameEvent) -> Option<String> {
        let key = super::context_key(
            &event.source.key,
            event.frame,
            event.location,
            event.phase,
            &event.route,
        );
        self.freed
            .get(&key)
            .map(|p| p.as_ref().map_or("none".into(), |t| self.types.name(t)))
    }
}

/// Loads and stores through `*local`, not address-taking.
struct Accesses {
    found: FxHashSet<Local>,
}

impl<'tcx> Visitor<'tcx> for Accesses {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, _location: Location) {
        let access = matches!(
            context,
            PlaceContext::NonMutatingUse(
                NonMutatingUseContext::Copy
                    | NonMutatingUseContext::Move
                    | NonMutatingUseContext::Inspect
            ) | PlaceContext::MutatingUse(
                MutatingUseContext::Store
                    | MutatingUseContext::Call
                    | MutatingUseContext::SetDiscriminant
            )
        );
        if access && place.projection.first() == Some(&ProjectionElem::Deref) {
            self.found.insert(place.local);
        }
    }
}

/// The locals accessed through (`*local`) on every path from `start` (after
/// it) to a normal return, a single-definition copy folded to its source. A
/// path that ends without returning (a diverging call, `unreachable`, a loop
/// that never leaves) contributes nothing (least fixpoint).
fn accessed_after(
    body: &Body<'_>,
    start: Location,
    function: LocalDefId,
    reassigned: &FxHashSet<(LocalDefId, Local)>,
) -> FxHashSet<Local> {
    // Single-definition copies of an unassigned local.
    let mut alias: FxHashMap<Local, Local> = FxHashMap::default();
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let StatementKind::Assign(assign) = &statement.kind else { continue };
            if !assign.0.projection.is_empty() || reassigned.contains(&(function, assign.0.local)) {
                continue;
            }
            if let Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
            | Rvalue::Cast(CastKind::PtrToPtr, Operand::Copy(p) | Operand::Move(p), _) =
                &assign.1
                && p.projection.is_empty()
                && !reassigned.contains(&(function, p.local))
            {
                alias.insert(assign.0.local, p.local);
            }
        }
    }
    let fold = |set: FxHashSet<Local>| -> FxHashSet<Local> {
        set.into_iter()
            .map(|l| alias.get(&l).copied().unwrap_or(l))
            .collect()
    };
    let gen_from = |block: BasicBlock, from: usize, with_terminator: bool| {
        let data = &body.basic_blocks[block];
        let mut visitor = Accesses {
            found: FxHashSet::default(),
        };
        for (index, statement) in data.statements.iter().enumerate().skip(from) {
            visitor.visit_statement(
                statement,
                Location {
                    block,
                    statement_index: index,
                },
            );
        }
        if with_terminator {
            visitor.visit_terminator(
                data.terminator(),
                Location {
                    block,
                    statement_index: data.statements.len(),
                },
            );
        }
        fold(visitor.found)
    };
    let successors = |block: BasicBlock| -> Vec<BasicBlock> {
        let terminator = body.basic_blocks[block].terminator();
        match &terminator.kind {
            TerminatorKind::Return
            | TerminatorKind::Unreachable
            | TerminatorKind::UnwindResume
            | TerminatorKind::UnwindTerminate(_)
            | TerminatorKind::CoroutineDrop => Vec::new(),
            TerminatorKind::Call { target, .. } => target.iter().copied().collect(),
            TerminatorKind::Drop { target, .. } | TerminatorKind::Assert { target, .. } => {
                vec![*target]
            }
            _ => terminator.successors().collect(),
        }
    };
    // Least fixpoint of IN[b] = GEN(b) ∪ ⋂ IN[succ], from ∅. A block with no
    // normal successor (a return, a diverging call, `unreachable`) has
    // IN = GEN(b): a path that ends there contributes nothing more.
    let blocks: Vec<BasicBlock> = body.basic_blocks.indices().collect();
    let gens: FxHashMap<BasicBlock, FxHashSet<Local>> =
        blocks.iter().map(|&b| (b, gen_from(b, 0, true))).collect();
    let mut inn: FxHashMap<BasicBlock, FxHashSet<Local>> =
        blocks.iter().map(|&b| (b, FxHashSet::default())).collect();
    let meet = |inn: &FxHashMap<BasicBlock, FxHashSet<Local>>, succ: &[BasicBlock]| {
        let mut acc: Option<FxHashSet<Local>> = None;
        for s in succ {
            acc = Some(match acc {
                None => inn[s].clone(),
                Some(a) => a.intersection(&inn[s]).copied().collect(),
            });
        }
        acc.unwrap_or_default()
    };
    loop {
        let mut changed = false;
        for &block in blocks.iter().rev() {
            let mut value = gens[&block].clone();
            value.extend(meet(&inn, &successors(block)));
            if inn[&block] != value {
                inn.insert(block, value);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    // From the event: the rest of its block (never the event's own terminator),
    // then every normal successor.
    let data = &body.basic_blocks[start.block];
    let is_terminator = start.statement_index >= data.statements.len();
    let mut set = if is_terminator {
        FxHashSet::default()
    } else {
        gen_from(start.block, start.statement_index + 1, true)
    };
    set.extend(meet(&inn, &successors(start.block)));
    set
}

/// A local's one definition: a copy or pointer cast of a place, or a call's
/// result (the callee and its first argument's place, if any).
enum Definition<'tcx> {
    Copy(Place<'tcx>),
    Call(rustc_span::def_id::DefId, Option<Place<'tcx>>),
}

fn single_definition<'tcx>(body: &Body<'tcx>, local: Local) -> Option<Definition<'tcx>> {
    let mut found = None;
    let mut count = 0;
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let StatementKind::Assign(assign) = &statement.kind else { continue };
            if assign.0.local != local || !assign.0.projection.is_empty() {
                continue;
            }
            count += 1;
            found = match &assign.1 {
                Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                | Rvalue::Cast(
                    CastKind::PtrToPtr | CastKind::PointerCoercion(..),
                    Operand::Copy(p) | Operand::Move(p),
                    _,
                ) => Some(Definition::Copy(*p)),
                _ => None,
            };
        }
        if let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &data.terminator().kind
            && destination.local == local
        {
            count += 1;
            found = func.const_fn_def().map(|(callee, _)| {
                let first = args.first().and_then(|a| match &a.node {
                    Operand::Copy(p) | Operand::Move(p) => Some(*p),
                    Operand::Constant(_) => None,
                });
                Definition::Call(callee, first)
            });
        }
    }
    if count == 1 { found } else { None }
}

/// (γ): `place` in `function` holds only fresh blocks: every definition of its
/// local is an allocator's result or a fresh producer's, through copies and
/// casts (bounded).
fn fresh_value<'tcx>(
    tcx: TyCtxt<'tcx>,
    function: LocalDefId,
    body: &Body<'tcx>,
    place: Place<'tcx>,
    depth: usize,
) -> bool {
    if depth > 8 || !place.projection.is_empty() {
        return false;
    }
    let local = place.local;
    if local.as_usize() >= 1 && local.as_usize() <= body.arg_count {
        return false;
    }
    match single_definition(body, local) {
        Some(Definition::Copy(p)) => fresh_value(tcx, function, body, p, depth + 1),
        Some(Definition::Call(callee, _)) => {
            matches!(
                tcx.item_name(callee).as_str(),
                "malloc" | "calloc" | "aligned_alloc" | "strdup" | "strndup"
            ) || callee
                .as_local()
                .is_some_and(|f| returns_fresh(tcx, f, depth + 1))
        }
        None => false,
    }
}

/// (γ): a local function whose return value is always a fresh block: `_0`'s
/// every definition is a fresh value (bounded; a null constant is allowed, as
/// releasing null releases nothing).
fn returns_fresh(tcx: TyCtxt<'_>, function: LocalDefId, depth: usize) -> bool {
    if depth > 4 || !tcx.def_kind(function).is_fn_like() {
        return false;
    }
    let body = tcx
        .mir_drops_elaborated_and_const_checked(function)
        .borrow();
    let mut any = false;
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let StatementKind::Assign(assign) = &statement.kind else { continue };
            if assign.0.local != rustc_middle::mir::RETURN_PLACE || !assign.0.projection.is_empty()
            {
                continue;
            }
            any = true;
            let fresh = match &assign.1 {
                Rvalue::Use(Operand::Copy(p) | Operand::Move(p))
                | Rvalue::Cast(
                    CastKind::PtrToPtr | CastKind::PointerCoercion(..),
                    Operand::Copy(p) | Operand::Move(p),
                    _,
                ) => fresh_value(tcx, function, &body, *p, depth + 1),
                Rvalue::Use(Operand::Constant(_)) | Rvalue::Cast(_, Operand::Constant(_), _) => {
                    true
                }
                _ => false,
            };
            if !fresh {
                return false;
            }
        }
        if let TerminatorKind::Call {
            func, destination, ..
        } = &data.terminator().kind
            && destination.local == rustc_middle::mir::RETURN_PLACE
        {
            any = true;
            let Some((callee, _)) = func.const_fn_def() else {
                return false;
            };
            let fresh = matches!(
                tcx.item_name(callee).as_str(),
                "malloc" | "calloc" | "aligned_alloc" | "strdup" | "strndup"
            ) || callee
                .as_local()
                .is_some_and(|f| returns_fresh(tcx, f, depth + 1));
            if !fresh {
                return false;
            }
        }
    }
    any
}

/// (α⁺): for the step `caller -> callee`, the caller's local behind each of
/// the callee's formals (the actual folded through single-definition copies,
/// casts and `&mut *x` / `&raw mut *x` reborrows).
fn formals_from<'tcx>(tcx: TyCtxt<'tcx>, step: &RouteStep) -> Option<FxHashMap<usize, Local>> {
    let caller = tcx
        .mir_drops_elaborated_and_const_checked(step.caller)
        .borrow();
    let TerminatorKind::Call { args, .. } =
        &caller.basic_blocks[step.location.block].terminator().kind
    else {
        return None;
    };
    let mut out = FxHashMap::default();
    for (index, arg) in args.iter().enumerate() {
        let (Operand::Copy(p) | Operand::Move(p)) = &arg.node else { continue };
        let mut place = *p;
        for _ in 0..16 {
            if !place.projection.is_empty() {
                break;
            }
            let mut next = None;
            let mut count = 0;
            for data in caller.basic_blocks.iter() {
                for statement in &data.statements {
                    let StatementKind::Assign(assign) = &statement.kind else { continue };
                    if assign.0.local != place.local || !assign.0.projection.is_empty() {
                        continue;
                    }
                    count += 1;
                    next = match &assign.1 {
                        Rvalue::Use(Operand::Copy(q) | Operand::Move(q))
                        | Rvalue::Cast(
                            CastKind::PtrToPtr | CastKind::PointerCoercion(..),
                            Operand::Copy(q) | Operand::Move(q),
                            _,
                        ) => Some(*q),
                        Rvalue::Ref(_, _, q) | Rvalue::RawPtr(_, q)
                            if q.projection.len() == 1
                                && q.projection[0] == ProjectionElem::Deref =>
                        {
                            Some(Place::from(q.local))
                        }
                        _ => None,
                    };
                }
            }
            match (count, next) {
                (1, Some(q)) => place = q,
                _ => break,
            }
        }
        if place.projection.is_empty() {
            out.insert(index + 1, place.local);
        }
    }
    Some(out)
}

/// (α⁺): the first frame, bottom up, where every path uses the referent after
/// the release, while every frame below it either uses the referent or
/// returns normally on every path. The referent's pointer is the conflict
/// target mapped down the route.
fn route_use(chain: &[RouteFrame], base: Local) -> Option<(LocalDefId, Local)> {
    let pointer = pointers(chain, base);
    for (index, frame) in chain.iter().enumerate() {
        if let Some(x) = pointer[index]
            && frame.accessed.contains(&x)
            && below(chain, &pointer, index)
        {
            return Some((frame.function, x));
        }
    }
    None
}

/// The pointer to the referent in each frame of the chain: the conflict target
/// at the top, mapped down through each step's formals. A frame's
/// `formals_from_caller` maps its own formals to its caller's (the frame above).
fn pointers(chain: &[RouteFrame], base: Local) -> Vec<Option<Local>> {
    let mut pointer: Vec<Option<Local>> = vec![None; chain.len()];
    let top = chain.len() - 1;
    pointer[top] = Some(base);
    for index in (0..top).rev() {
        let caller_local = pointer[index + 1];
        pointer[index] = caller_local.and_then(|x| {
            chain[index]
                .formals_from_caller
                .iter()
                .find(|(_, local)| **local == x)
                .map(|(formal, _)| Local::from_usize(*formal))
        });
    }
    pointer
}

/// Every frame below `index` either uses the referent or returns normally on
/// every path after the release.
fn below(chain: &[RouteFrame], pointer: &[Option<Local>], index: usize) -> bool {
    chain[..index]
        .iter()
        .zip(&pointer[..index])
        .all(|(f, x)| match x {
            Some(x) => f
                .accessed_or_returned
                .as_ref()
                .is_none_or(|set| set.contains(x)),
            None => f.returns,
        })
}

/// (α⁺): `accessed_after`'s set, the set where a normal return also counts
/// (`None`: every path returns), and whether every path returns normally.
fn after_frame(
    body: &Body<'_>,
    start: Location,
    function: LocalDefId,
    reassigned: &FxHashSet<(LocalDefId, Local)>,
) -> (FxHashSet<Local>, Option<FxHashSet<Local>>, bool) {
    let accessed = accessed_after(body, start, function, reassigned);
    // Every path returns normally: a least fixpoint over the blocks.
    let normal = |block: BasicBlock| -> (bool, Vec<BasicBlock>) {
        let terminator = body.basic_blocks[block].terminator();
        match &terminator.kind {
            TerminatorKind::Return => (true, Vec::new()),
            TerminatorKind::Unreachable
            | TerminatorKind::UnwindResume
            | TerminatorKind::UnwindTerminate(_)
            | TerminatorKind::CoroutineDrop => (false, Vec::new()),
            TerminatorKind::Call { target, .. } => (false, target.iter().copied().collect()),
            TerminatorKind::Drop { target, .. } | TerminatorKind::Assert { target, .. } => {
                (false, vec![*target])
            }
            _ => (false, terminator.successors().collect()),
        }
    };
    let blocks: Vec<BasicBlock> = body.basic_blocks.indices().collect();
    let mut returns: FxHashMap<BasicBlock, bool> = blocks.iter().map(|&b| (b, false)).collect();
    loop {
        let mut changed = false;
        for &block in blocks.iter().rev() {
            let (ret, succ) = normal(block);
            let value = ret || (!succ.is_empty() && succ.iter().all(|s| returns[s]));
            if returns[&block] != value {
                returns.insert(block, value);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    let (_, succ) = normal(start.block);
    let start_returns = if start.statement_index >= body.basic_blocks[start.block].statements.len()
    {
        !succ.is_empty() && succ.iter().all(|s| returns[s])
    } else {
        returns[&start.block]
    };
    // Accessed-or-returned: a local accessed on every path that does not
    // return. With every path returning, every local qualifies.
    let accessed_or_returned = if start_returns {
        None
    } else {
        Some(accessed.clone())
    };
    (accessed, accessed_or_returned, start_returns)
}
