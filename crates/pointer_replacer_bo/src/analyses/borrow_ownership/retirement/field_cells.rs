//! Relay main/388 stage 3 (B), 270's callee-unknown group: the pointer a caller stored in one field
//! of one known object, per program point, and whether a function has written any memory behind a
//! pointer since its entry.
//!
//! A release routed from a callee as `Field { Input { callee, k, d }, f }` -- the callee freed what
//! field `f` of its formal's object held at the load -- is resolved in the caller only when both hold:
//!
//!   * PRISTINE: on every path from the callee's entry to the release, nothing ran that may write
//!     memory behind a pointer: a store through a dereference, a call other than the allocators,
//!     `free` and `core::ptr::{null, null_mut, is_null}`, a `Drop`, `CopyNonOverlapping`, inline
//!     assembly, `Deinit` / `SetDiscriminant` through a dereference. The field's content at the
//!     release is then its content at the callee's entry, which is its content at the call;
//!   * STORED: at the call, the caller holds a cell for (the argument's single object, the formal's
//!     struct, `f`), set by a store `(*p).f = v` through that one object and not killed since.
//!
//! Kills: a store through the object to the same field, or to any field under another struct type
//! (no effective-type premise); a store through a parameter's object kills every parameter's cells
//! (two parameters may name one object); any other store through a dereference, every call above,
//! `Drop`, `CopyNonOverlapping` and inline assembly kill every cell; a write to a local's own storage
//! (its value, a field of it, its storage markers) kills that local's cells. `free` and the
//! allocators write no cell of a live object: a cell of the freed object is never read again on a
//! UB-free input (§28). An allocation site on a CFG cycle names many objects with one name and gets
//! no cell. A join keeps a cell only where every path holds the same content, and PRISTINE is the
//! paths' conjunction. Anything unresolved stays Unknown in the route, as before.
//!
//! One exception to "every call kills every cell" (the c2rust constructor stores
//! `(*o).f = text_duplicate(s)` field by field, a program call between the stores): a call cannot
//! write an object it cannot reach. A libc allocation's object is UNESCAPED until its pointer leaves
//! the frame's pointer locals: an argument of any call but `free` / the allocators /
//! `core::ptr::{null, null_mut, is_null}`, a value stored into memory or into a local's field, an
//! operand of an aggregate, of a cast other than pointer-to-pointer, of a non-comparison operator,
//! or any pointer-carrying operand whose objects are not all known (that escapes every object).
//! Across such a call, the cells of an unescaped object stay.

use std::collections::VecDeque;

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::{
    mir::{
        BinOp, Body, CastKind, Local, Location, NonDivergingIntrinsic, Operand, Place,
        ProjectionElem, Rvalue, START_BLOCK, StatementKind, TerminatorKind,
    },
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_span::def_id::{DefId, LocalDefId};

use super::objects::{ObjectFacts, ObjectRoot, ObjectSet};
use crate::{
    analyses::{
        borrow_ownership::{crate_slots::MAX_SLOT_DEPTH, export::PlaceKey, source_events},
        mir::{CallKind, TerminatorExt},
    },
    utils::rustc::RustProgram,
};

/// One pointer field of one known object, under the struct type it was stored through.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct CellKey {
    pub(crate) root: ObjectRoot,
    pub(crate) adt: DefId,
    pub(crate) field: u32,
}

pub(crate) type Cells = FxHashMap<CellKey, ObjectSet>;

#[derive(Clone, Debug, PartialEq)]
struct State {
    cells: Cells,
    pristine: bool,
    /// The libc allocations of this invocation whose pointer has not escaped on any path.
    fresh: FxHashSet<ObjectRoot>,
}

/// The one object a set names, when it names exactly one and nothing unknown.
pub(crate) fn single(objects: &ObjectSet) -> Option<ObjectRoot> {
    if objects.unknown {
        return None;
    }
    let mut roots = objects.roots.iter();
    match (roots.next(), roots.next()) {
        (Some(&root), None) => Some(root),
        _ => None,
    }
}

/// The non-generic struct `ty` points to through `depth + 1` dereferences.
pub(crate) fn pointee_struct<'tcx>(
    tcx: TyCtxt<'tcx>,
    mut ty: Ty<'tcx>,
    depth: u8,
) -> Option<DefId> {
    for _ in 0..=depth {
        ty = ty.builtin_deref(true)?;
    }
    let adt = ty.ty_adt_def()?;
    (adt.is_struct() && tcx.generics_of(adt.did()).count() == 0).then(|| adt.did())
}

fn kill_all(state: &mut State) {
    state.cells.clear();
    state.pristine = false;
    state.fresh.clear();
}

fn kill_local(state: &mut State, function: LocalDefId, local: Local) {
    let stack = ObjectRoot::Stack { function, local };
    state.cells.retain(|key, _| key.root != stack);
}

fn through_pointer(place: Place<'_>) -> bool {
    place
        .projection
        .iter()
        .any(|projection| matches!(projection, ProjectionElem::Deref))
}

fn joined(entry: &mut Option<State>, incoming: &State) -> bool {
    let Some(previous) = entry else {
        *entry = Some(incoming.clone());
        return true;
    };
    let before = (
        previous.cells.len(),
        previous.pristine,
        previous.fresh.len(),
    );
    previous
        .cells
        .retain(|key, value| incoming.cells.get(key) == Some(value));
    previous.pristine &= incoming.pristine;
    previous.fresh.retain(|root| incoming.fresh.contains(root));
    before
        != (
            previous.cells.len(),
            previous.pristine,
            previous.fresh.len(),
        )
}

struct Pass<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    function: LocalDefId,
    body: &'a Body<'tcx>,
    facts: &'a ObjectFacts,
    cyclic: FxHashSet<rustc_middle::mir::BasicBlock>,
}

impl<'tcx> Pass<'_, 'tcx> {
    /// An object a cell may name: one of this invocation, and not one name for many objects.
    fn eligible(&self, root: ObjectRoot) -> bool {
        match root {
            ObjectRoot::Field { .. } => false,
            ObjectRoot::Fresh { frame, site } => {
                frame == self.function && !self.cyclic.contains(&site.block)
            }
            ObjectRoot::Stack { function, .. } | ObjectRoot::Input { function, .. } => {
                function == self.function
            }
        }
    }

    /// A store's value at depth 0: a copied or cast pointer, or a null constant.
    fn value(&self, location: Location, rvalue: &Rvalue<'tcx>) -> Option<ObjectSet> {
        let (Rvalue::Use(operand) | Rvalue::Cast(CastKind::PtrToPtr, operand, _)) = rvalue else {
            return None;
        };
        match operand {
            Operand::Copy(place) | Operand::Move(place) => Some(self.facts.pointer_at(
                self.function,
                location,
                &PlaceKey::from_place(*place),
                0,
            )),
            Operand::Constant(_) if source_events::operand_is_null(operand, &[], self.tcx) => {
                Some(ObjectSet {
                    roots: FxHashSet::default(),
                    unknown: false,
                })
            }
            Operand::Constant(_) => None,
        }
    }

    /// The objects `operand` may carry leave the frame's pointer locals: they escape.
    fn escape(&self, location: Location, operand: &Operand<'tcx>, state: &mut State) {
        let mut level = operand.ty(&self.body.local_decls, self.tcx);
        // A value with no pointer in it (a C enum, a scalar, a function) carries no object.
        if matches!(level.kind(), TyKind::FnDef(..) | TyKind::FnPtr(..))
            || !crate::analyses::borrow_ownership::licensing::caller_coverage::carries_pointer(
                self.tcx,
                level,
                &mut FxHashSet::default(),
            )
        {
            return;
        }
        // A constant names no object of this invocation.
        let Some(place) = operand.place() else { return };
        let place = PlaceKey::from_place(place);
        for depth in 0..MAX_SLOT_DEPTH {
            if !level.is_raw_ptr() && !level.is_ref() {
                if depth == 0 {
                    // A non-scalar value may hold any pointer.
                    state.fresh.clear();
                }
                return;
            }
            let objects = self
                .facts
                .pointer_at(self.function, location, &place, depth);
            if objects.unknown {
                state.fresh.clear();
                return;
            }
            for root in &objects.roots {
                state.fresh.remove(root);
            }
            let Some(next) = level.builtin_deref(true) else { return };
            level = next;
        }
        if level.is_raw_ptr() || level.is_ref() {
            state.fresh.clear();
        }
    }

    fn rvalue_escapes(
        &self,
        location: Location,
        into_local: bool,
        rvalue: &Rvalue<'tcx>,
        state: &mut State,
    ) {
        match rvalue {
            Rvalue::Use(operand) | Rvalue::Cast(CastKind::PtrToPtr, operand, _) => {
                if !into_local {
                    self.escape(location, operand, state);
                }
            }
            Rvalue::Cast(_, operand, _)
            | Rvalue::Repeat(operand, _)
            | Rvalue::UnaryOp(_, operand) => {
                self.escape(location, operand, state);
            }
            Rvalue::BinaryOp(operator, box (left, right)) => {
                if !matches!(
                    operator,
                    BinOp::Eq
                        | BinOp::Ne
                        | BinOp::Lt
                        | BinOp::Le
                        | BinOp::Gt
                        | BinOp::Ge
                        | BinOp::Cmp
                ) {
                    self.escape(location, left, state);
                    self.escape(location, right, state);
                }
            }
            Rvalue::Aggregate(_, operands) => {
                for operand in operands {
                    self.escape(location, operand, state);
                }
            }
            _ => {}
        }
    }

    fn statement(&self, location: Location, kind: &StatementKind<'tcx>, state: &mut State) {
        match kind {
            StatementKind::Assign(box (place, rvalue)) => {
                self.rvalue_escapes(location, place.projection.is_empty(), rvalue, state);
                if !through_pointer(*place) {
                    kill_local(state, self.function, place.local);
                    return;
                }
                state.pristine = false;
                let stored = match place.projection.as_slice() {
                    [ProjectionElem::Deref, ProjectionElem::Field(field, _)] => {
                        let base = self.facts.pointer_at(
                            self.function,
                            location,
                            &PlaceKey::from_place(Place::from(place.local)),
                            0,
                        );
                        single(&base)
                            .filter(|&root| self.eligible(root))
                            .and_then(|root| {
                                pointee_struct(self.tcx, self.body.local_decls[place.local].ty, 0)
                                    .map(|adt| (root, adt, field.as_u32()))
                            })
                    }
                    _ => None,
                };
                let Some((root, adt, field)) = stored else {
                    state.cells.clear();
                    return;
                };
                let input = matches!(root, ObjectRoot::Input { .. });
                state.cells.retain(|key, _| {
                    if key.root == root {
                        key.adt == adt && key.field != field
                    } else {
                        !(input && matches!(key.root, ObjectRoot::Input { .. }))
                    }
                });
                if let Some(value) = self.value(location, rvalue).filter(|value| !value.unknown) {
                    state.cells.insert(CellKey { root, adt, field }, value);
                }
            }
            StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
                kill_local(state, self.function, *local);
            }
            StatementKind::Deinit(place) | StatementKind::SetDiscriminant { place, .. } => {
                if through_pointer(**place) {
                    kill_all(state);
                } else {
                    kill_local(state, self.function, place.local);
                }
            }
            StatementKind::Intrinsic(box NonDivergingIntrinsic::CopyNonOverlapping(_)) => {
                kill_all(state);
            }
            _ => {}
        }
    }

    fn terminator(&self, location: Location, state: &mut State) {
        let terminator = self.body.basic_blocks[location.block].terminator();
        let Some(call) = terminator.as_call(self.tcx) else {
            if matches!(
                terminator.kind,
                TerminatorKind::Drop { .. } | TerminatorKind::InlineAsm { .. }
            ) {
                kill_all(state);
            }
            return;
        };
        let tcx = self.tcx;
        let allocator = matches!(call.func, CallKind::LibC(name)
            if matches!(name.as_str(), "malloc" | "calloc" | "strdup" | "realloc"));
        let keeps = allocator
            || matches!(call.func, CallKind::LibC(name) if name.as_str() == "free")
            || matches!(call.func, CallKind::RustLib(did)
                if tcx.crate_name(did.krate).as_str() == "core"
                    && tcx.def_path_str(did).contains("::ptr::")
                    && matches!(tcx.item_name(did).as_str(), "null" | "null_mut" | "is_null"));
        if !keeps {
            for argument in call.args.iter() {
                self.escape(location, &argument.node, state);
            }
            let fresh = &state.fresh;
            state.cells.retain(|key, _| fresh.contains(&key.root));
            state.pristine = false;
        }
        match call.destination.as_local() {
            Some(local) => kill_local(state, self.function, local),
            None => kill_all(state),
        }
        if allocator && call.destination.as_local().is_some() {
            state.fresh.insert(ObjectRoot::Fresh {
                frame: self.function,
                site: location,
            });
        }
    }
}

/// The caller's cells at every point where it holds one, and the points reached with nothing
/// written behind a pointer since the function's entry.
pub(super) fn analyze<'tcx>(
    program: &RustProgram<'tcx>,
    function: LocalDefId,
    body: &Body<'tcx>,
    facts: &ObjectFacts,
) -> (FxHashMap<Location, Cells>, FxHashSet<Location>) {
    let pass = Pass {
        tcx: program.tcx,
        function,
        body,
        facts,
        cyclic: crate::analyses::borrow_ownership::index_ranges::cyclic_blocks(body),
    };
    let mut entries: Vec<Option<State>> = vec![None; body.basic_blocks.len()];
    entries[START_BLOCK.as_usize()] = Some(State {
        cells: Cells::default(),
        pristine: true,
        fresh: FxHashSet::default(),
    });
    let mut queue = VecDeque::from([START_BLOCK]);
    let mut queued = vec![false; body.basic_blocks.len()];
    queued[START_BLOCK.as_usize()] = true;
    while let Some(block) = queue.pop_front() {
        queued[block.as_usize()] = false;
        let data = &body.basic_blocks[block];
        let mut state = entries[block.as_usize()]
            .clone()
            .expect("a reachable cell state");
        for (statement_index, statement) in data.statements.iter().enumerate() {
            pass.statement(
                Location {
                    block,
                    statement_index,
                },
                &statement.kind,
                &mut state,
            );
        }
        pass.terminator(
            Location {
                block,
                statement_index: data.statements.len(),
            },
            &mut state,
        );
        for successor in data.terminator().successors() {
            if joined(&mut entries[successor.as_usize()], &state) && !queued[successor.as_usize()] {
                queued[successor.as_usize()] = true;
                queue.push_back(successor);
            }
        }
    }
    let mut cells = FxHashMap::default();
    let mut pristine = FxHashSet::default();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        let Some(mut state) = entries[block.as_usize()].clone() else { continue };
        for statement_index in 0..=data.statements.len() {
            let location = Location {
                block,
                statement_index,
            };
            if !state.cells.is_empty() {
                cells.insert(location, state.cells.clone());
            }
            if state.pristine {
                pristine.insert(location);
            }
            if let Some(statement) = data.statements.get(statement_index) {
                pass.statement(location, &statement.kind, &mut state);
            }
        }
    }
    (cells, pristine)
}
