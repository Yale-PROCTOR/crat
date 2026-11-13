use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::{
    mir::{
        Body, Local, Location, Operand, Place, ProjectionElem, RETURN_PLACE, Rvalue, StatementKind,
        TerminatorKind, UnwindAction, visit::Visitor,
    },
    ty::{Ty, TyCtxt, TyKind},
};

use super::local_outcome::is_pointer_copy_method;

/// Local carriers whose obligations end with this frame, rather than surviving its unwind.
#[derive(Default)]
pub(super) struct UnwindLiveness {
    exits: FxHashSet<Location>,
    escaping: FxHashSet<Local>,
}

struct ValueSources<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    locals: Vec<Local>,
    pointer_types: FxHashMap<Ty<'tcx>, bool>,
}

impl<'tcx> Visitor<'tcx> for ValueSources<'_, 'tcx> {
    fn visit_operand(&mut self, operand: &Operand<'tcx>, _: Location) {
        if let Some(place) = operand.place() {
            self.value(place);
        }
    }

    fn visit_rvalue(&mut self, value: &Rvalue<'tcx>, location: Location) {
        match value {
            // A carrier's address can expose its value through another pointer.
            Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => self.locals.push(place.local),
            Rvalue::CopyForDeref(place) => self.value(*place),
            _ => self.super_rvalue(value, location),
        }
    }
}

impl<'tcx> ValueSources<'_, 'tcx> {
    fn value(&mut self, place: Place<'tcx>) {
        let ty = place.ty(&self.body.local_decls, self.tcx).ty;
        // Reading pointer-free pointee data does not carry the pointer's value out of the frame.
        if !place.projection.contains(&ProjectionElem::Deref) || self.may_carry_pointer(ty) {
            self.locals.push(place.local);
        }
    }

    fn may_carry_pointer(&mut self, ty: Ty<'tcx>) -> bool {
        if let Some(&result) = self.pointer_types.get(&ty) {
            return result;
        }
        // Recursive or unresolved storage cannot establish the absence of pointer carriers.
        self.pointer_types.insert(ty, true);
        let result = match ty.kind() {
            TyKind::Array(inner, _) | TyKind::Slice(inner) => self.may_carry_pointer(*inner),
            TyKind::Tuple(fields) => fields.iter().any(|field| self.may_carry_pointer(field)),
            TyKind::Adt(definition, args) => definition
                .all_fields()
                .any(|field| self.may_carry_pointer(field.ty(self.tcx, args))),
            TyKind::Bool
            | TyKind::Char
            | TyKind::Int(_)
            | TyKind::Uint(_)
            | TyKind::Float(_)
            | TyKind::Str
            | TyKind::Never => false,
            _ => true,
        };
        self.pointer_types.insert(ty, result);
        result
    }
}

fn assign(
    dependencies: &mut FxHashMap<Local, Vec<Local>>,
    escaping: &mut FxHashSet<Local>,
    destination: Place<'_>,
    inputs: Vec<Local>,
) {
    if destination.local == RETURN_PLACE || destination.projection.contains(&ProjectionElem::Deref)
    {
        escaping.extend(inputs);
    } else {
        dependencies
            .entry(destination.local)
            .or_default()
            .extend(inputs);
    }
}

impl UnwindLiveness {
    pub(super) fn analyze<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Self {
        let exits = body
            .basic_blocks
            .iter_enumerated()
            .filter(|(_, data)| {
                matches!(data.terminator().kind, TerminatorKind::UnwindResume)
                    || data.terminator().unwind() == Some(&UnwindAction::Continue)
            })
            .map(|(block, data)| Location {
                block,
                statement_index: data.statements.len(),
            })
            .collect::<FxHashSet<_>>();
        if exits.is_empty() {
            return Self::default();
        }
        let mut escaping = FxHashSet::from_iter([RETURN_PLACE]);
        escaping.extend(body.args_iter());
        let mut dependencies = FxHashMap::<Local, Vec<Local>>::default();
        let mut sources = ValueSources {
            tcx,
            body,
            locals: Vec::new(),
            pointer_types: FxHashMap::default(),
        };
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for (statement_index, statement) in data.statements.iter().enumerate() {
                if matches!(statement.kind, StatementKind::Intrinsic(..)) {
                    escaping.extend(body.local_decls.indices());
                }
                let StatementKind::Assign(box (destination, value)) = &statement.kind else {
                    continue;
                };
                let location = Location {
                    block,
                    statement_index,
                };
                sources.visit_rvalue(value, location);
                // An alias of a carrier's storage can expose pointer bits through scalar loads.
                if let Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) = value
                    && !matches!(place.projection.first(), Some(ProjectionElem::Deref))
                    && let ty = body.local_decls[place.local].ty
                    && (!ty.is_scalar() || ty.is_any_ptr())
                {
                    escaping.insert(place.local);
                }
                // Erasing the pointer type can hide its address in a scalar representation.
                if matches!(value, Rvalue::Cast(_, operand, target)
                    if operand.ty(&body.local_decls, tcx).is_any_ptr() && !target.is_any_ptr())
                {
                    escaping.extend(sources.locals.iter().copied());
                }
                assign(
                    &mut dependencies,
                    &mut escaping,
                    *destination,
                    std::mem::take(&mut sources.locals),
                );
            }
            let location = Location {
                block,
                statement_index: data.statements.len(),
            };
            match &data.terminator().kind {
                TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    ..
                } => {
                    for argument in args {
                        sources.visit_operand(&argument.node, location);
                    }
                    if func
                        .const_fn_def()
                        .is_some_and(|(callee, _)| is_pointer_copy_method(tcx, callee))
                    {
                        if destination.ty(&body.local_decls, tcx).ty.is_integral() {
                            escaping.extend(sources.locals.iter().copied());
                        }
                        assign(
                            &mut dependencies,
                            &mut escaping,
                            *destination,
                            std::mem::take(&mut sources.locals),
                        );
                    } else {
                        sources.visit_operand(func, location);
                        escaping.extend(sources.locals.drain(..));
                    }
                }
                TerminatorKind::TailCall { func, args, .. } => {
                    sources.visit_operand(func, location);
                    for argument in args {
                        sources.visit_operand(&argument.node, location);
                    }
                    escaping.extend(sources.locals.drain(..));
                }
                TerminatorKind::Drop { place, .. } => {
                    escaping.insert(place.local);
                }
                TerminatorKind::InlineAsm { .. } | TerminatorKind::Yield { .. } => {
                    escaping.extend(body.local_decls.indices());
                }
                _ => {}
            }
        }
        let typing_env = body.typing_env(tcx);
        escaping.extend(
            body.local_decls
                .iter_enumerated()
                .filter_map(|(local, decl)| decl.ty.needs_drop(tcx, typing_env).then_some(local)),
        );
        let mut pending = escaping.iter().copied().collect::<Vec<_>>();
        while let Some(local) = pending.pop() {
            for &source in dependencies.get(&local).into_iter().flatten() {
                if escaping.insert(source) {
                    pending.push(source);
                }
            }
        }
        Self { exits, escaping }
    }

    pub(super) fn ends_at(&self, local: Local, location: Location) -> bool {
        self.exits.contains(&location) && !self.escaping.contains(&local)
    }
}
