#![allow(dead_code)]

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::bit_set::DenseBitSet;
use rustc_middle::{
    mir::{
        self, BasicBlock, Body, Local, Location, Operand, Place, Rvalue, Statement, StatementKind,
        Terminator, TerminatorKind,
    },
    ty::{self, Ty, TyCtxt},
};
use rustc_span::{Symbol, def_id::LocalDefId};

use crate::{
    analyses::mir::{CallGraphPostOrder, CallKind, MirFunctionCall, TerminatorExt},
    utils::rustc::RustProgram,
};

#[derive(Debug, Default)]
pub struct NullityResult {
    pub non_null_params: FxHashMap<LocalDefId, DenseBitSet<Local>>,
}

pub fn analyze(program: &RustProgram<'_>) -> NullityResult {
    let tcx = program.tcx;
    let function_set: FxHashSet<_> = program.functions.iter().copied().collect();
    let mut summaries = FxHashMap::default();
    summaries.reserve(program.functions.len());

    for &did in &program.functions {
        let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
        summaries.insert(did, DenseBitSet::new_empty(body.local_decls.len()));
    }

    let call_graph = CallGraphPostOrder::new(program);
    loop {
        let mut changed = false;

        for scc in call_graph.sccs() {
            loop {
                let mut scc_changed = false;

                for &did in scc {
                    let did = did.expect_local();
                    let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
                    let params_to_add = raw_pointer_params(&body)
                        .into_iter()
                        .filter(|param| !summaries[&did].contains(*param))
                        .filter(|param| {
                            SingleParamAnalyzer {
                                tcx,
                                body: &body,
                                summaries: &summaries,
                                function_set: &function_set,
                                positive_memo: FxHashSet::default(),
                            }
                            .proves_non_null(*param)
                        })
                        .collect::<Vec<_>>();

                    let summary = summaries.get_mut(&did).unwrap();
                    for param in params_to_add {
                        scc_changed |= summary.insert(param);
                    }
                }

                changed |= scc_changed;
                if !scc_changed {
                    break;
                }
            }
        }

        if !changed {
            break;
        }
    }

    NullityResult {
        non_null_params: summaries
            .into_iter()
            .filter(|(_, params)| !params.is_empty())
            .collect(),
    }
}

fn raw_pointer_params(body: &Body<'_>) -> Vec<Local> {
    body.args_iter()
        .filter(|&local| is_raw_pointer_ty(body.local_decls[local].ty))
        .collect()
}

fn is_raw_pointer_ty(ty: Ty<'_>) -> bool {
    matches!(ty.kind(), ty::TyKind::RawPtr(..))
}

struct SingleParamAnalyzer<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    summaries: &'a FxHashMap<LocalDefId, DenseBitSet<Local>>,
    function_set: &'a FxHashSet<LocalDefId>,
    positive_memo: FxHashSet<TraversalKey>,
}

impl<'a, 'tcx> SingleParamAnalyzer<'a, 'tcx> {
    fn proves_non_null(mut self, param: Local) -> bool {
        self.prove_from(
            Location::START,
            Aliases::new(param),
            &mut FxHashSet::default(),
        )
    }

    fn prove_from(
        &mut self,
        location: Location,
        aliases: Aliases,
        path: &mut FxHashSet<TraversalKey>,
    ) -> bool {
        let key = TraversalKey::new(location, &aliases);
        if self.positive_memo.contains(&key) {
            return true;
        }
        if !path.insert(key.clone()) {
            return false;
        }

        let proved = self.prove_from_uncached(location, aliases, path);

        path.remove(&key);
        if proved {
            self.positive_memo.insert(key);
        }
        proved
    }

    fn prove_from_uncached(
        &mut self,
        location: Location,
        aliases: Aliases,
        path: &mut FxHashSet<TraversalKey>,
    ) -> bool {
        let block = &self.body.basic_blocks[location.block];
        if location.statement_index < block.statements.len() {
            return match self
                .transfer_statement(&block.statements[location.statement_index], aliases)
            {
                Step::Proof => true,
                Step::Barrier => false,
                Step::Continue(aliases) => {
                    self.prove_from(location.successor_within_block(), aliases, path)
                }
            };
        }

        self.transfer_terminator(block.terminator(), aliases, path)
    }

    fn transfer_statement(&self, statement: &Statement<'tcx>, mut aliases: Aliases) -> Step {
        let StatementKind::Assign(box (lhs, rvalue)) = &statement.kind else {
            return Step::Continue(aliases);
        };

        if place_derefs_alias(lhs, &aliases) || rvalue_derefs_alias(rvalue, &aliases) {
            return Step::Proof;
        }

        if rvalue_takes_alias_address(rvalue, &aliases) {
            return Step::Barrier;
        }

        let rhs_direct_alias = rvalue_direct_alias_source(rvalue, &aliases)
            && is_raw_pointer_ty(self.body.local_decls[lhs.local].ty);
        let rhs_contains_alias = rvalue_contains_alias_value(rvalue, &aliases);

        if lhs.projection.is_empty() {
            if rhs_direct_alias {
                aliases.insert(lhs.local);
                return Step::Continue(aliases);
            }

            if aliases.contains(lhs.local) || rhs_contains_alias {
                return Step::Barrier;
            }
        } else if rhs_direct_alias || rhs_contains_alias {
            return Step::Barrier;
        }

        Step::Continue(aliases)
    }

    fn transfer_terminator(
        &mut self,
        terminator: &Terminator<'tcx>,
        aliases: Aliases,
        path: &mut FxHashSet<TraversalKey>,
    ) -> bool {
        if let Some(call) = terminator.as_call(self.tcx) {
            return self.transfer_call(terminator, call, aliases, path);
        }

        if terminator_derefs_alias(terminator, &aliases) {
            return true;
        }

        self.prove_successors(terminator.successors(), aliases, path)
    }

    fn transfer_call(
        &mut self,
        terminator: &Terminator<'tcx>,
        call: MirFunctionCall<'_, 'tcx>,
        aliases: Aliases,
        path: &mut FxHashSet<TraversalKey>,
    ) -> bool {
        let mut alias_arg_indices = vec![];

        for (idx, arg) in call.args.iter().enumerate() {
            if operand_derefs_alias(&arg.node, &aliases) {
                return true;
            }
            if operand_contains_alias_value(&arg.node, &aliases) {
                alias_arg_indices.push(idx);
            }
        }

        if place_derefs_alias(&call.destination, &aliases) {
            return true;
        }

        if !alias_arg_indices.is_empty() {
            return self.call_requires_non_null(&call.func, &alias_arg_indices);
        }

        if call.destination.projection.is_empty() && aliases.contains(call.destination.local) {
            return false;
        }

        self.prove_successors(terminator.successors(), aliases, path)
    }

    fn call_requires_non_null(&self, func: &CallKind, alias_arg_indices: &[usize]) -> bool {
        match func {
            CallKind::FreeStanding(callee) if self.function_set.contains(callee) => {
                let Some(summary) = self.summaries.get(callee) else {
                    return false;
                };
                alias_arg_indices
                    .iter()
                    .all(|idx| summary.contains(Local::from_usize(idx + 1)))
            }
            CallKind::LibC(name) => libc_requires_non_null(*name, alias_arg_indices),
            CallKind::RustLib(def_id) if is_raw_pointer_is_null(self.tcx, *def_id) => false,
            CallKind::FreeStanding(_)
            | CallKind::RustLib(_)
            | CallKind::Impl(_)
            | CallKind::Closure
            | CallKind::Dynamic => false,
        }
    }

    fn prove_successors(
        &mut self,
        successors: impl Iterator<Item = BasicBlock>,
        aliases: Aliases,
        path: &mut FxHashSet<TraversalKey>,
    ) -> bool {
        let successors = successors.collect::<Vec<_>>();
        if successors.is_empty() {
            return false;
        }

        successors.into_iter().all(|block| {
            self.prove_from(
                Location {
                    block,
                    statement_index: 0,
                },
                aliases.clone(),
                path,
            )
        })
    }
}

enum Step {
    Proof,
    Barrier,
    Continue(Aliases),
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Aliases(Vec<Local>);

impl Aliases {
    fn new(local: Local) -> Self {
        Self(vec![local])
    }

    fn contains(&self, local: Local) -> bool {
        self.0
            .binary_search_by_key(&local.index(), |local| local.index())
            .is_ok()
    }

    fn insert(&mut self, local: Local) {
        match self
            .0
            .binary_search_by_key(&local.index(), |local| local.index())
        {
            Ok(_) => {}
            Err(idx) => self.0.insert(idx, local),
        }
    }

    fn key(&self) -> Vec<usize> {
        self.0.iter().map(|local| local.index()).collect()
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct TraversalKey {
    block: usize,
    statement_index: usize,
    aliases: Vec<usize>,
}

impl TraversalKey {
    fn new(location: Location, aliases: &Aliases) -> Self {
        Self {
            block: location.block.as_usize(),
            statement_index: location.statement_index,
            aliases: aliases.key(),
        }
    }
}

fn libc_requires_non_null(name: Symbol, alias_arg_indices: &[usize]) -> bool {
    let non_null_args: &[usize] = match name.as_str() {
        "strlen" | "strchr" | "strrchr" | "atoi" | "atol" | "atof" | "puts" => &[0],
        "strcmp" | "strcasecmp" | "strcpy" | "strcat" | "strstr" => &[0, 1],
        "fputs" => &[0],
        _ => return false,
    };

    alias_arg_indices
        .iter()
        .all(|idx| non_null_args.contains(idx))
}

fn is_raw_pointer_is_null(tcx: TyCtxt<'_>, def_id: rustc_span::def_id::DefId) -> bool {
    let name = tcx.def_path(def_id).to_string_no_crate_verbose();
    let mut segs = name.rsplit("::");
    matches!(segs.next(), Some("is_null"))
        && segs.next().is_some()
        && matches!(segs.next(), Some("mut_ptr" | "const_ptr"))
        && matches!(segs.next(), Some("ptr"))
}

fn terminator_derefs_alias(terminator: &Terminator<'_>, aliases: &Aliases) -> bool {
    match &terminator.kind {
        TerminatorKind::SwitchInt { discr, .. } | TerminatorKind::Assert { cond: discr, .. } => {
            operand_derefs_alias(discr, aliases)
        }
        TerminatorKind::Drop { place, .. } => place_derefs_alias(place, aliases),
        TerminatorKind::Yield { value, .. } => operand_derefs_alias(value, aliases),
        _ => false,
    }
}

fn rvalue_direct_alias_source(rvalue: &Rvalue<'_>, aliases: &Aliases) -> bool {
    match rvalue {
        Rvalue::Use(operand) => operand_plain_alias(operand, aliases),
        Rvalue::Cast(_, operand, ty) if is_raw_pointer_ty(*ty) => {
            operand_plain_alias(operand, aliases)
        }
        _ => false,
    }
}

fn rvalue_takes_alias_address(rvalue: &Rvalue<'_>, aliases: &Aliases) -> bool {
    matches!(
        rvalue,
        Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place)
            if aliases.contains(place.local) && !place_has_deref(place)
    )
}

fn rvalue_derefs_alias(rvalue: &Rvalue<'_>, aliases: &Aliases) -> bool {
    match rvalue {
        Rvalue::Use(operand)
        | Rvalue::Repeat(operand, _)
        | Rvalue::UnaryOp(_, operand)
        | Rvalue::Cast(_, operand, _) => operand_derefs_alias(operand, aliases),
        Rvalue::BinaryOp(_, box (lhs, rhs)) => {
            operand_derefs_alias(lhs, aliases) || operand_derefs_alias(rhs, aliases)
        }
        Rvalue::Ref(_, _, place)
        | Rvalue::RawPtr(_, place)
        | Rvalue::Len(place)
        | Rvalue::Discriminant(place) => place_derefs_alias(place, aliases),
        Rvalue::CopyForDeref(place) => aliases.contains(place.local),
        Rvalue::Aggregate(_, operands) => operands
            .iter()
            .any(|operand| operand_derefs_alias(operand, aliases)),
        _ => false,
    }
}

fn rvalue_contains_alias_value(rvalue: &Rvalue<'_>, aliases: &Aliases) -> bool {
    match rvalue {
        Rvalue::Use(operand)
        | Rvalue::Repeat(operand, _)
        | Rvalue::UnaryOp(_, operand)
        | Rvalue::Cast(_, operand, _) => operand_contains_alias_value(operand, aliases),
        Rvalue::BinaryOp(_, box (lhs, rhs)) => {
            operand_contains_alias_value(lhs, aliases) || operand_contains_alias_value(rhs, aliases)
        }
        Rvalue::Aggregate(_, operands) => operands
            .iter()
            .any(|operand| operand_contains_alias_value(operand, aliases)),
        _ => false,
    }
}

fn operand_plain_alias(operand: &Operand<'_>, aliases: &Aliases) -> bool {
    matches!(
        operand,
        Operand::Copy(place) | Operand::Move(place)
            if place.projection.is_empty() && aliases.contains(place.local)
    )
}

fn operand_derefs_alias(operand: &Operand<'_>, aliases: &Aliases) -> bool {
    matches!(
        operand,
        Operand::Copy(place) | Operand::Move(place) if place_derefs_alias(place, aliases)
    )
}

fn operand_contains_alias_value(operand: &Operand<'_>, aliases: &Aliases) -> bool {
    matches!(
        operand,
        Operand::Copy(place) | Operand::Move(place)
            if aliases.contains(place.local) && !place_has_deref(place)
    )
}

fn place_derefs_alias(place: &Place<'_>, aliases: &Aliases) -> bool {
    aliases.contains(place.local) && place_has_deref(place)
}

fn place_has_deref(place: &Place<'_>) -> bool {
    place
        .projection
        .iter()
        .any(|elem| matches!(elem, mir::ProjectionElem::Deref))
}

#[cfg(test)]
mod tests;
