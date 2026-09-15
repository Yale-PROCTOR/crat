//! Conservative native no-retirement evidence for R350 Box lending.
//! This proves a whole local call closure, independently of no-retention and
//! model kind. Unsupported operations remain holds; no cached model is read.

// The closure module is also compiled verbatim by the bounded standalone test.
mod closure {
    use std::collections::{BTreeMap, BTreeSet};

    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
    pub(crate) struct Site {
        pub function: u32,
        pub block: u32,
        pub statement: usize,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub(crate) enum Effect {
        LocalCall { site: Site, callee: u32 },
        Retirement(Site),
        Opaque(Site),
    }

    #[derive(Clone, Debug)]
    pub(crate) struct FunctionFacts {
        pub pointer_parameters: BTreeSet<usize>,
        pub effects: Vec<Effect>,
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub(crate) enum Hold {
        MissingFunction(u32),
        Parameter {
            function: u32,
            argument: usize,
        },
        Retirement(Site),
        Opaque(Site),
        Cycle(u32),
        /// The traced formal is stored into memory or a call result of an
        /// aggregate place; a later load could reach it, so nothing is proved.
        Escape(Site),
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub(crate) struct Proof {
        pub function: u32,
        pub argument: usize,
        pub checked_functions: BTreeSet<u32>,
        pub checked_calls: BTreeSet<Site>,
    }

    pub(crate) fn certify(
        facts: &BTreeMap<u32, FunctionFacts>,
        function: u32,
        argument: usize,
    ) -> Result<Proof, Hold> {
        let root = facts
            .get(&function)
            .ok_or(Hold::MissingFunction(function))?;
        if !root.pointer_parameters.contains(&argument) {
            return Err(Hold::Parameter { function, argument });
        }
        let mut proof = Proof {
            function,
            argument,
            checked_functions: BTreeSet::new(),
            checked_calls: BTreeSet::new(),
        };
        let mut active = BTreeSet::new();
        let mut stack = vec![(function, false)];
        while let Some((current, exiting)) = stack.pop() {
            if exiting {
                active.remove(&current);
                proof.checked_functions.insert(current);
                continue;
            }
            if proof.checked_functions.contains(&current) {
                continue;
            }
            if !active.insert(current) {
                return Err(Hold::Cycle(current));
            }
            let body = facts.get(&current).ok_or(Hold::MissingFunction(current))?;
            stack.push((current, true));
            for effect in body.effects.iter().rev() {
                match *effect {
                    Effect::LocalCall { site, callee } => {
                        proof.checked_calls.insert(site);
                        stack.push((callee, false));
                    }
                    Effect::Retirement(site) => return Err(Hold::Retirement(site)),
                    Effect::Opaque(site) => return Err(Hold::Opaque(site)),
                }
            }
        }
        Ok(proof)
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        fn site(function: u32) -> Site {
            Site {
                function,
                block: 0,
                statement: 1,
            }
        }
        fn body(effects: Vec<Effect>) -> FunctionFacts {
            FunctionFacts {
                pointer_parameters: BTreeSet::from([0]),
                effects,
            }
        }
        #[test]
        fn direct_borrow_has_a_complete_nonconsuming_certificate() {
            let facts = BTreeMap::from([(1, body(vec![]))]);
            let proof = certify(&facts, 1, 0).unwrap();
            assert_eq!(proof.checked_functions, BTreeSet::from([1]));
            assert!(proof.checked_calls.is_empty());
        }
        #[test]
        fn direct_free_is_not_a_borrow_even_when_it_does_not_retain() {
            let facts = BTreeMap::from([(1, body(vec![Effect::Retirement(site(1))]))]);
            assert_eq!(certify(&facts, 1, 0), Err(Hold::Retirement(site(1))));
        }
        #[test]
        fn transitive_consumption_cannot_hide_behind_no_retention() {
            let facts = BTreeMap::from([
                (
                    1,
                    body(vec![Effect::LocalCall {
                        site: site(1),
                        callee: 2,
                    }]),
                ),
                (2, body(vec![Effect::Retirement(site(2))])),
            ]);
            assert_eq!(certify(&facts, 1, 0), Err(Hold::Retirement(site(2))));
        }
        #[test]
        fn complete_diamond_records_all_call_sites_once() {
            let second = Site {
                statement: 2,
                ..site(1)
            };
            let facts = BTreeMap::from([
                (
                    1,
                    body(vec![
                        Effect::LocalCall {
                            site: site(1),
                            callee: 2,
                        },
                        Effect::LocalCall {
                            site: second,
                            callee: 3,
                        },
                    ]),
                ),
                (
                    2,
                    body(vec![Effect::LocalCall {
                        site: site(2),
                        callee: 4,
                    }]),
                ),
                (
                    3,
                    body(vec![Effect::LocalCall {
                        site: site(3),
                        callee: 4,
                    }]),
                ),
                (4, body(vec![])),
            ]);
            let proof = certify(&facts, 1, 0).unwrap();
            assert_eq!(proof.checked_functions, BTreeSet::from([1, 2, 3, 4]));
            assert_eq!(
                proof.checked_calls,
                BTreeSet::from([site(1), second, site(2), site(3)])
            );
        }
        #[test]
        fn opaque_and_missing_dependencies_hold() {
            let mut facts = BTreeMap::from([(1, body(vec![Effect::Opaque(site(1))]))]);
            assert_eq!(certify(&facts, 1, 0), Err(Hold::Opaque(site(1))));
            facts.get_mut(&1).unwrap().effects = vec![Effect::LocalCall {
                site: site(1),
                callee: 2,
            }];
            assert_eq!(certify(&facts, 1, 0), Err(Hold::MissingFunction(2)));
        }
        #[test]
        fn self_and_mutual_cycles_do_not_default_to_positive() {
            let mut facts = BTreeMap::from([(
                1,
                body(vec![Effect::LocalCall {
                    site: site(1),
                    callee: 1,
                }]),
            )]);
            assert_eq!(certify(&facts, 1, 0), Err(Hold::Cycle(1)));
            facts.get_mut(&1).unwrap().effects = vec![Effect::LocalCall {
                site: site(1),
                callee: 2,
            }];
            facts.insert(
                2,
                body(vec![Effect::LocalCall {
                    site: site(2),
                    callee: 1,
                }]),
            );
            assert_eq!(certify(&facts, 1, 0), Err(Hold::Cycle(1)));
        }
        #[test]
        fn missing_root_and_wrong_parameter_hold() {
            assert_eq!(
                certify(&BTreeMap::new(), 1, 0),
                Err(Hold::MissingFunction(1))
            );
            let facts = BTreeMap::from([(1, body(vec![]))]);
            assert_eq!(
                certify(&facts, 1, 1),
                Err(Hold::Parameter {
                    function: 1,
                    argument: 1
                })
            );
        }
    }
}
// END STANDALONE CLOSURE

use std::collections::{BTreeMap, BTreeSet};

pub(crate) use closure::{Hold as EffectsHold, Site as EffectsSite};
use rustc_middle::{
    mir::{Body, Local, Operand, Place, ProjectionElem, Rvalue, StatementKind, TerminatorKind},
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_span::def_id::LocalDefId;

use crate::utils::rustc::RustProgram;

/// Complete bodies from one compiler session. The map is private so a caller
/// cannot manufacture completeness by omitting a consuming site or callee.
/// This deliberately proves more than one argument needs: no supported body in
/// the closure retires anything. A free of an unrelated object also holds.
pub(crate) struct NativeEffects<'tcx> {
    _tcx: TyCtxt<'tcx>,
    facts: BTreeMap<u32, closure::FunctionFacts>,
    /// Per-formal refinement of the whole-closure facts (see `ArgumentFacts`).
    arguments: BTreeMap<u32, ArgumentFacts>,
}

/// What each pointer parameter of one body may alias, and at every effect
/// site which parameters reach it. A parameter whose pointer value is stored
/// into memory (or into a call result that is not a plain local) records the
/// escape site instead of a set, and nothing is proved for it.
#[derive(Clone, Debug, Default)]
struct ArgumentFacts {
    escapes: BTreeMap<usize, closure::Site>,
    /// Parameters whose pointer value may reach the return place, and the
    /// first `Return` site: a returned alias is retention past the call.
    returned: BTreeSet<usize>,
    return_site: Option<closure::Site>,
    /// Drop terminators and C-free-contract calls: which parameters reach the
    /// retired operand.
    retirements: BTreeMap<closure::Site, BTreeSet<usize>>,
    /// Calls: the callee shape and, per parameter, the argument indices it reaches.
    calls: BTreeMap<closure::Site, CallFacts>,
    /// Sites that are opaque whatever the formal (intrinsics, inline assembly).
    unconditional_opaque: BTreeSet<closure::Site>,
}

#[derive(Clone, Debug)]
struct CallFacts {
    callee: CalleeKind,
    reaching: BTreeMap<usize, BTreeSet<usize>>,
}

#[derive(Clone, Debug)]
enum CalleeKind {
    Local(u32),
    /// A non-local callee with the argument indices carrying a C consume contract.
    Foreign {
        consumes: BTreeSet<usize>,
    },
    /// Core raw-pointer arithmetic (`offset`, `add`, `sub` and the wrapping
    /// forms): it derives a pointer from its receiver and neither frees nor
    /// stores it; the derived pointer is traced like the formal.
    PointerArithmetic,
    Indirect,
}

/// Tied to the deriving index and exact formal; never a model-kind certificate.
/// The caller must still prove no-retention, peer disjointness and lifetimes.
pub(crate) struct NonConsumingProof<'a, 'tcx> {
    index: &'a NativeEffects<'tcx>,
    callee: LocalDefId,
    proof: closure::Proof,
    scope: &'static str,
}

impl<'tcx> NativeEffects<'tcx> {
    pub(crate) fn derive(program: &RustProgram<'tcx>) -> Self {
        use closure::{Effect, FunctionFacts, Site};
        let mut functions = program.functions.clone();
        functions.sort_by_key(|function| function.local_def_index.as_u32());
        functions.dedup();
        let mut facts = BTreeMap::new();
        let mut arguments = BTreeMap::new();
        for &function in &functions {
            let body = program
                .tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            let pointer_parameters = (0..body.arg_count)
                .filter(|index| {
                    matches!(
                        body.local_decls[Local::from_usize(index + 1)].ty.kind(),
                        TyKind::RawPtr(..) | TyKind::Ref(..)
                    )
                })
                .collect();
            let mut effects = Vec::new();
            // Inspect every block, including cleanup and unreachable blocks.
            // Lack of reachability evidence never hides a retirement.
            for (block, data) in body.basic_blocks.iter_enumerated() {
                let at = |statement| Site {
                    function: function.local_def_index.as_u32(),
                    block: block.as_u32(),
                    statement,
                };
                for (index, statement) in data.statements.iter().enumerate() {
                    match statement.kind {
                        StatementKind::Assign(..)
                        | StatementKind::StorageLive(..)
                        | StatementKind::StorageDead(..)
                        | StatementKind::FakeRead(..)
                        | StatementKind::Retag(..)
                        | StatementKind::PlaceMention(..)
                        | StatementKind::AscribeUserType(..)
                        | StatementKind::SetDiscriminant { .. }
                        | StatementKind::Deinit(..)
                        | StatementKind::Nop => {}
                        _ => effects.push(Effect::Opaque(at(index))),
                    }
                }
                let site = at(data.statements.len());
                match &data.terminator().kind {
                    TerminatorKind::Drop { .. } => effects.push(Effect::Retirement(site)),
                    TerminatorKind::Call { func, args, .. }
                    | TerminatorKind::TailCall { func, args, .. } => {
                        let callee =
                            func.constant()
                                .and_then(|constant| match constant.ty().kind() {
                                    TyKind::FnDef(callee, _) => Some(*callee),
                                    _ => None,
                                });
                        if let Some(local) = callee.and_then(|callee| callee.as_local())
                            && functions.contains(&local)
                        {
                            effects.push(Effect::LocalCall {
                                site,
                                callee: local.local_def_index.as_u32(),
                            });
                        } else {
                            // Existing contracts are used only to name a negative
                            // consume. Per-argument BorrowView is not a proof that
                            // an opaque callee cannot retire a different alias.
                            let consumes = callee.is_some_and(|callee| {
                                let symbol = super::raw_boundary::symbol_key(
                                    program.tcx, callee, &program.functions,
                                );
                                args.iter().enumerate().any(|(index, argument)| {
                                    let Some(target) = super::raw_boundary::raw_target_type(
                                        program.tcx, argument.node.ty(&*body, program.tcx),
                                    ) else { return false };
                                    super::raw_boundary_contracts::classify_contract(
                                        &symbol, index, &target,
                                    ).is_ok_and(|contract| matches!(
                                        contract.ownership,
                                        super::raw_boundary_contracts::OwnershipContract::Consume
                                            | super::raw_boundary_contracts::OwnershipContract::AtomicSourceSink
                                    ))
                                })
                            });
                            effects.push(if consumes {
                                Effect::Retirement(site)
                            } else {
                                Effect::Opaque(site)
                            });
                        }
                    }
                    TerminatorKind::Goto { .. }
                    | TerminatorKind::SwitchInt { .. }
                    | TerminatorKind::Return
                    | TerminatorKind::Unreachable
                    | TerminatorKind::FalseEdge { .. }
                    | TerminatorKind::FalseUnwind { .. }
                    | TerminatorKind::UnwindResume
                    | TerminatorKind::UnwindTerminate(..) => {}
                    // Assert/panic, inline assembly and unknown library helpers
                    // need separate effects contracts, never a spelling allowlist.
                    _ => effects.push(Effect::Opaque(site)),
                }
            }
            let argument_facts =
                argument_facts(program, &functions, function, &body, &pointer_parameters);
            arguments.insert(function.local_def_index.as_u32(), argument_facts);
            facts.insert(
                function.local_def_index.as_u32(),
                FunctionFacts {
                    pointer_parameters,
                    effects,
                },
            );
        }
        Self {
            _tcx: program.tcx,
            facts,
            arguments,
        }
    }

    /// The per-formal walk: only a site the traced formal reaches can retire
    /// it. Cycles, escapes, opaque sites reached by the formal and missing
    /// bodies hold exactly as the whole-closure proof does.
    fn certify_argument(
        &self,
        function: u32,
        argument: usize,
    ) -> Result<closure::Proof, closure::Hold> {
        self.trace_formal(function, argument, false)
    }

    /// Native no-retention: the formal reaches no store into memory, no
    /// opaque or indirect callee, and no return place anywhere in the local
    /// closure it flows through (pointer arithmetic on it is traced, not
    /// trusted). It is an alternative to the raw-boundary T1 certificate for
    /// the lend arm only, and it is never a proof of non-consumption alone.
    pub(crate) fn certify_no_retention(
        &self,
        callee: LocalDefId,
        argument: usize,
    ) -> Result<NonConsumingProof<'_, 'tcx>, EffectsHold> {
        let function = callee.local_def_index.as_u32();
        Ok(NonConsumingProof {
            index: self,
            callee,
            proof: self.trace_formal(function, argument, true)?,
            scope: "native-per-argument-no-retention",
        })
    }

    fn trace_formal(
        &self,
        function: u32,
        argument: usize,
        retention: bool,
    ) -> Result<closure::Proof, closure::Hold> {
        use closure::{Hold, Proof};
        let root = self
            .facts
            .get(&function)
            .ok_or(Hold::MissingFunction(function))?;
        if !root.pointer_parameters.contains(&argument) {
            return Err(Hold::Parameter { function, argument });
        }
        let mut proof = Proof {
            function,
            argument,
            checked_functions: BTreeSet::new(),
            checked_calls: BTreeSet::new(),
        };
        let mut active = BTreeSet::new();
        let mut done = BTreeSet::new();
        self.walk(
            function,
            BTreeSet::from([argument]),
            retention,
            &mut active,
            &mut done,
            &mut proof,
        )?;
        Ok(proof)
    }

    fn walk(
        &self,
        function: u32,
        parameters: BTreeSet<usize>,
        retention: bool,
        active: &mut BTreeSet<(u32, BTreeSet<usize>)>,
        done: &mut BTreeSet<(u32, BTreeSet<usize>)>,
        proof: &mut closure::Proof,
    ) -> Result<(), closure::Hold> {
        use closure::Hold;
        let key = (function, parameters.clone());
        if done.contains(&key) {
            return Ok(());
        }
        if !active.insert(key.clone()) {
            return Err(Hold::Cycle(function));
        }
        let facts = self
            .arguments
            .get(&function)
            .ok_or(Hold::MissingFunction(function))?;
        if let Some(site) = facts.unconditional_opaque.iter().next() {
            return Err(Hold::Opaque(*site));
        }
        for (site, reaching) in &facts.retirements {
            if reaching
                .iter()
                .any(|parameter| parameters.contains(parameter))
            {
                return Err(Hold::Retirement(*site));
            }
        }
        for (site, call) in &facts.calls {
            let reached: BTreeSet<usize> = parameters
                .iter()
                .filter_map(|parameter| call.reaching.get(parameter))
                .flatten()
                .copied()
                .collect();
            if reached.is_empty() {
                continue;
            }
            match &call.callee {
                CalleeKind::Local(callee) => {
                    proof.checked_calls.insert(*site);
                    self.walk(*callee, reached, retention, active, done, proof)?;
                }
                CalleeKind::Foreign { consumes } => {
                    if reached.iter().any(|index| consumes.contains(index)) {
                        return Err(Hold::Retirement(*site));
                    }
                    return Err(Hold::Opaque(*site));
                }
                CalleeKind::PointerArithmetic => {}
                CalleeKind::Indirect => return Err(Hold::Opaque(*site)),
            }
        }
        // Sites the formal reaches are reported first; a store of the formal
        // into memory (or, for retention, a returned alias) holds after them.
        for parameter in &parameters {
            if let Some(site) = facts.escapes.get(parameter) {
                return Err(Hold::Escape(*site));
            }
            if retention && facts.returned.contains(parameter) {
                return Err(Hold::Escape(
                    facts.return_site.ok_or(Hold::MissingFunction(function))?,
                ));
            }
        }
        active.remove(&key);
        done.insert(key);
        proof.checked_functions.insert(function);
        Ok(())
    }

    pub(crate) fn certify(
        &self,
        callee: LocalDefId,
        argument: usize,
    ) -> Result<NonConsumingProof<'_, 'tcx>, EffectsHold> {
        let function = callee.local_def_index.as_u32();
        let (proof, scope) = match closure::certify(&self.facts, function, argument) {
            Ok(proof) => (proof, "whole-closure"),
            // The whole closure retires or hides something; prove instead that
            // this formal reaches none of it.
            Err(EffectsHold::Retirement(_) | EffectsHold::Opaque(_)) => {
                (self.certify_argument(function, argument)?, "per-argument")
            }
            Err(hold) => return Err(hold),
        };
        Ok(NonConsumingProof {
            index: self,
            callee,
            proof,
            scope,
        })
    }
}

fn is_pointer_arithmetic(tcx: TyCtxt<'_>, callee: rustc_span::def_id::DefId) -> bool {
    tcx.crate_name(callee.krate).as_str() == "core"
        && matches!(
            tcx.item_name(callee).as_str(),
            "offset" | "add" | "sub" | "wrapping_offset" | "wrapping_add" | "wrapping_sub"
        )
        && tcx.impl_of_method(callee).is_some_and(|imp| {
            tcx.trait_id_of_impl(imp).is_none() && tcx.type_of(imp).skip_binder().is_raw_ptr()
        })
}

fn is_scalar(ty: Ty<'_>) -> bool {
    matches!(
        ty.kind(),
        TyKind::Bool | TyKind::Char | TyKind::Int(_) | TyKind::Uint(_) | TyKind::Float(_)
    )
}

/// A read of `place` yields (part of) the traced pointer value when the place
/// is a tainted local or an aggregate projection of one, or a load through a
/// tainted pointer whose type could itself carry a pointer.
fn place_read_tainted<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    tainted: &BTreeSet<Local>,
    place: &Place<'tcx>,
) -> bool {
    tainted.contains(&place.local)
        && (!place
            .projection
            .iter()
            .any(|elem| matches!(elem, ProjectionElem::Deref))
            || !is_scalar(place.ty(body, tcx).ty))
}

fn operand_tainted<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    tainted: &BTreeSet<Local>,
    operand: &Operand<'tcx>,
) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            place_read_tainted(tcx, body, tainted, place)
        }
        Operand::Constant(_) => false,
    }
}

fn rvalue_tainted<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    tainted: &BTreeSet<Local>,
    rvalue: &Rvalue<'tcx>,
) -> bool {
    match rvalue {
        Rvalue::Use(operand)
        | Rvalue::Cast(_, operand, _)
        | Rvalue::UnaryOp(_, operand)
        | Rvalue::Repeat(operand, _)
        | Rvalue::ShallowInitBox(operand, _)
        | Rvalue::WrapUnsafeBinder(operand, _) => operand_tainted(tcx, body, tainted, operand),
        Rvalue::BinaryOp(_, operands) => {
            operand_tainted(tcx, body, tainted, &operands.0)
                || operand_tainted(tcx, body, tainted, &operands.1)
        }
        Rvalue::Aggregate(_, operands) => operands
            .iter()
            .any(|operand| operand_tainted(tcx, body, tainted, operand)),
        Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) | Rvalue::CopyForDeref(place) => {
            tainted.contains(&place.local)
        }
        Rvalue::Len(_)
        | Rvalue::Discriminant(_)
        | Rvalue::NullaryOp(..)
        | Rvalue::ThreadLocalRef(_) => false,
    }
}

/// Every local that may carry the pointer value of `parameter` (or a pointer
/// derived from it), or the site where that value is stored into memory.
/// Flow-insensitive and monotone: the set only grows, which is the safe side.
fn trace_parameter<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    parameter: usize,
    at: &dyn Fn(rustc_middle::mir::BasicBlock, usize) -> closure::Site,
) -> (BTreeSet<Local>, Option<closure::Site>) {
    let mut tainted = BTreeSet::from([Local::from_usize(parameter + 1)]);
    let mut escape = None;
    loop {
        let before = tainted.len();
        for (block, data) in body.basic_blocks.iter_enumerated() {
            for (index, statement) in data.statements.iter().enumerate() {
                let StatementKind::Assign(assignment) = &statement.kind else { continue };
                let (place, rvalue) = &**assignment;
                if !rvalue_tainted(tcx, body, &tainted, rvalue) {
                    continue;
                }
                if place
                    .projection
                    .iter()
                    .any(|elem| matches!(elem, ProjectionElem::Deref))
                {
                    escape.get_or_insert(at(block, index));
                    continue;
                }
                tainted.insert(place.local);
            }
            match &data.terminator().kind {
                TerminatorKind::Call {
                    args, destination, ..
                } if args
                    .iter()
                    .any(|argument| operand_tainted(tcx, body, &tainted, &argument.node)) =>
                {
                    if destination
                        .projection
                        .iter()
                        .any(|elem| matches!(elem, ProjectionElem::Deref))
                    {
                        escape.get_or_insert(at(block, data.statements.len()));
                    } else {
                        tainted.insert(destination.local);
                    }
                }
                // A tail call returns the callee's result directly; the
                // caller's own return place is not read again here.
                _ => {}
            }
        }
        if tainted.len() == before {
            return (tainted, escape);
        }
    }
}

fn argument_facts<'tcx>(
    program: &RustProgram<'tcx>,
    functions: &[LocalDefId],
    function: LocalDefId,
    body: &Body<'tcx>,
    pointer_parameters: &BTreeSet<usize>,
) -> ArgumentFacts {
    use closure::Site;
    let tcx = program.tcx;
    let at = |block: rustc_middle::mir::BasicBlock, statement: usize| Site {
        function: function.local_def_index.as_u32(),
        block: block.as_u32(),
        statement,
    };
    let mut facts = ArgumentFacts::default();
    let mut traced = BTreeMap::new();
    for &parameter in pointer_parameters {
        let (set, escape) = trace_parameter(tcx, body, parameter, &at);
        if set.contains(&rustc_middle::mir::RETURN_PLACE) {
            facts.returned.insert(parameter);
        }
        if let Some(site) = escape {
            facts.escapes.insert(parameter, site);
        }
        // The trace continues past an escape so every call and retirement
        // the formal reaches is still attributed; the escape holds afterwards.
        traced.insert(parameter, set);
    }
    let reaching_operand = |operand: &Operand<'tcx>| -> BTreeSet<usize> {
        traced
            .iter()
            .filter(|(_, set)| operand_tainted(tcx, body, set, operand))
            .map(|(parameter, _)| *parameter)
            .collect()
    };
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for (index, statement) in data.statements.iter().enumerate() {
            match statement.kind {
                StatementKind::Assign(..)
                | StatementKind::StorageLive(..)
                | StatementKind::StorageDead(..)
                | StatementKind::FakeRead(..)
                | StatementKind::Retag(..)
                | StatementKind::PlaceMention(..)
                | StatementKind::AscribeUserType(..)
                | StatementKind::SetDiscriminant { .. }
                | StatementKind::Deinit(..)
                | StatementKind::Nop => {}
                _ => {
                    facts.unconditional_opaque.insert(at(block, index));
                }
            }
        }
        let site = at(block, data.statements.len());
        match &data.terminator().kind {
            TerminatorKind::Drop { place, .. } => {
                let reaching = traced
                    .iter()
                    .filter(|(_, set)| set.contains(&place.local))
                    .map(|(parameter, _)| *parameter)
                    .collect();
                facts.retirements.insert(site, reaching);
            }
            TerminatorKind::Call { func, args, .. }
            | TerminatorKind::TailCall { func, args, .. } => {
                let callee = func
                    .constant()
                    .and_then(|constant| match constant.ty().kind() {
                        TyKind::FnDef(callee, _) => Some(*callee),
                        _ => None,
                    });
                let mut reaching: BTreeMap<usize, BTreeSet<usize>> = BTreeMap::new();
                for (index, argument) in args.iter().enumerate() {
                    for parameter in reaching_operand(&argument.node) {
                        reaching.entry(parameter).or_default().insert(index);
                    }
                }
                let callee = match callee {
                    Some(callee)
                        if callee
                            .as_local()
                            .is_some_and(|local| functions.contains(&local)) =>
                    {
                        CalleeKind::Local(callee.as_local().unwrap().local_def_index.as_u32())
                    }
                    Some(callee) if is_pointer_arithmetic(tcx, callee) => {
                        CalleeKind::PointerArithmetic
                    }
                    Some(callee) => {
                        let symbol =
                            super::raw_boundary::symbol_key(tcx, callee, &program.functions);
                        let consumes = args
                            .iter()
                            .enumerate()
                            .filter(|(index, argument)| {
                                super::raw_boundary::raw_target_type(tcx, argument.node.ty(body, tcx))
                                    .is_some_and(|target| {
                                        super::raw_boundary_contracts::classify_contract(&symbol, *index, &target)
                                            .is_ok_and(|contract| matches!(
                                                contract.ownership,
                                                super::raw_boundary_contracts::OwnershipContract::Consume
                                                    | super::raw_boundary_contracts::OwnershipContract::AtomicSourceSink
                                            ))
                                    })
                            })
                            .map(|(index, _)| index)
                            .collect();
                        CalleeKind::Foreign { consumes }
                    }
                    None => CalleeKind::Indirect,
                };
                facts.calls.insert(site, CallFacts { callee, reaching });
            }
            TerminatorKind::Return => {
                facts.return_site.get_or_insert(site);
            }
            // An assertion only unwinds or aborts; its cleanup drops are
            // inspected as their own sites.
            TerminatorKind::Assert { .. }
            | TerminatorKind::Goto { .. }
            | TerminatorKind::SwitchInt { .. }
            | TerminatorKind::Unreachable
            | TerminatorKind::FalseEdge { .. }
            | TerminatorKind::FalseUnwind { .. }
            | TerminatorKind::UnwindResume
            | TerminatorKind::UnwindTerminate(..) => {}
            _ => {
                facts.unconditional_opaque.insert(site);
            }
        }
    }
    facts
}

impl<'tcx> NonConsumingProof<'_, 'tcx> {
    pub(crate) fn matches(
        &self,
        index: &NativeEffects<'tcx>,
        callee: LocalDefId,
        argument: usize,
    ) -> bool {
        std::ptr::eq(self.index, index) && self.callee == callee && self.proof.argument == argument
    }

    pub(crate) fn checked_calls(&self) -> &BTreeSet<EffectsSite> {
        &self.proof.checked_calls
    }

    /// `whole-closure` (no supported body in the closure retires anything) or
    /// `per-argument` (this formal reaches no retiring or opaque site).
    pub(crate) fn scope(&self) -> &'static str {
        self.scope
    }

    pub(crate) fn checked_functions(&self) -> &BTreeSet<u32> {
        &self.proof.checked_functions
    }
}

#[cfg(test)]
mod native_tests {
    use super::*;

    fn verdict(source: &str, name: &str) -> Result<(usize, usize), EffectsHold> {
        let name = name.to_owned();
        ::utils::compilation::run_compiler_on_str(source, move |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let function = program
                .functions
                .iter()
                .copied()
                .find(|function| tcx.def_path_str(function.to_def_id()) == name)
                .expect("exact fixture definition");
            let effects = NativeEffects::derive(&program);
            let proof = effects.certify(function, 0)?;
            assert!(proof.matches(&effects, function, 0));
            assert!(!proof.matches(&effects, function, 1));
            let other = NativeEffects::derive(&program);
            assert!(!proof.matches(&other, function, 0));
            Ok((proof.checked_functions().len(), proof.checked_calls().len()))
        })
        .expect("effects fixture compiles")
    }

    #[test]
    fn native_direct_pointer_borrow_and_local_forwarding() {
        assert_eq!(
            verdict("pub unsafe fn touch(p: *mut i32) { *p = 7; }", "touch"),
            Ok((1, 0))
        );
        assert_eq!(
            verdict(
                "unsafe fn touch(p: *mut i32) { *p = 7; } pub unsafe fn forward(p: *mut i32) { touch(p); }",
                "forward"
            ),
            Ok((2, 1))
        );
    }

    #[test]
    fn native_direct_and_transitive_free_hold() {
        let prefix = r#"extern "C" { fn free(p: *mut core::ffi::c_void); }"#;
        let direct =
            format!("{prefix} pub unsafe fn sink(p: *mut core::ffi::c_void) {{ free(p); }}");
        assert!(matches!(
            verdict(&direct, "sink"),
            Err(EffectsHold::Retirement(_))
        ));
        let transitive =
            format!("{direct} pub unsafe fn forward(p: *mut core::ffi::c_void) {{ sink(p); }}");
        assert!(matches!(
            verdict(&transitive, "forward"),
            Err(EffectsHold::Retirement(_))
        ));
    }

    #[test]
    fn native_no_retention_does_not_discharge_transitive_free() {
        let source = r#"
            extern "C" { fn free(p: *mut core::ffi::c_void); }
            unsafe fn sink(p: *mut core::ffi::c_void) { free(p); }
            pub unsafe fn forward(p: *mut core::ffi::c_void) { sink(p); }
        "#;
        ::utils::compilation::run_compiler_on_str(source, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let function = program.functions.iter().copied()
                .find(|function| tcx.def_path_str(function.to_def_id()) == "forward")
                .expect("exact forward function");
            let origins = crate::analyses::borrow_ownership::origins::compute_origins(&program);
            let retention = super::super::raw_boundary::RetentionSummaries::derive(
                &program, Some(&origins),
                Some(crate::analyses::borrow_ownership::a5_overlap::WholeProgramAttestation::FrozenBenchmarkGraph),
            );
            let Some(super::super::raw_boundary::RetentionVerdict::NoRetain { certificate }) =
                retention.get(function, 0)
            else { panic!("the non-retaining consuming route must remain distinguished") };
            assert!(retention.verify_certificate(function, 0, certificate).is_ok());
            let effects = NativeEffects::derive(&program);
            assert!(matches!(effects.certify(function, 0), Err(EffectsHold::Retirement(_))));
        }).expect("non-retaining consuming fixture compiles");
    }

    const LIBC: &str = r#"extern "C" { fn malloc(n: usize) -> *mut core::ffi::c_void; fn free(p: *mut core::ffi::c_void); }"#;

    #[test]
    fn native_callee_freeing_only_its_own_allocation_certifies_the_formal() {
        // The corpus shape of heman `generate_gaussian_row`: the formal is read
        // and written through; the callee allocates and frees its own buffer.
        let source = format!(
            "{LIBC} pub unsafe fn row(target: *mut i32, n: usize) {{ let tmp = malloc(n * 4) as *mut i32; *tmp = 1; *target = *tmp; let mut i = 1; while i < n {{ *target.offset(i as isize) = *tmp.offset(i as isize); i += 1; }} free(tmp as *mut core::ffi::c_void); }}"
        );
        assert_eq!(verdict(&source, "row"), Ok((1, 0)));
        // The same with the formal forwarded to a local callee that frees only its own buffer.
        let forwarded = format!(
            "{source} unsafe fn own(p: *mut i32) {{ free(p as *mut core::ffi::c_void); }} pub unsafe fn forward(target: *mut i32) {{ let local = malloc(4) as *mut i32; row(target, 1); own(local); }}"
        );
        assert_eq!(verdict(&forwarded, "forward"), Ok((2, 1)));
    }

    #[test]
    fn native_formal_reaching_a_free_by_copy_cast_call_or_return_holds() {
        for body in [
            "let q = target as *mut core::ffi::c_void; free(q);",
            "let r = id(target); free(r as *mut core::ffi::c_void);",
            "own(target);",
            "let tmp = malloc(4) as *mut i32; let (a, b) = (tmp, target); free(b as *mut core::ffi::c_void); free(a as *mut core::ffi::c_void);",
        ] {
            let source = format!(
                "{LIBC} unsafe fn id(p: *mut i32) -> *mut i32 {{ p }} unsafe fn own(p: *mut i32) {{ free(p as *mut core::ffi::c_void); }} pub unsafe fn probe(target: *mut i32) {{ {body} }}"
            );
            assert!(
                matches!(verdict(&source, "probe"), Err(EffectsHold::Retirement(_))),
                "{body}"
            );
        }
    }

    #[test]
    fn native_formal_escaping_to_memory_or_an_opaque_callee_holds() {
        for (body, expected) in [
            ("*out = target; free(malloc(4));", "Escape"),
            ("(*out) = target.offset(1);", "Escape"),
            ("opaque(target);", "Opaque"),
            (
                "let p: *mut *mut i32 = out; *p = target; free(malloc(4));",
                "Escape",
            ),
        ] {
            let source = format!(
                "{LIBC} extern \"C\" {{ fn opaque(p: *mut i32); }} pub unsafe fn probe(target: *mut i32, out: *mut *mut i32) {{ {body} }}"
            );
            let result = verdict(&source, "probe");
            assert!(
                match expected {
                    "Escape" => matches!(result, Err(EffectsHold::Escape(_))),
                    _ => matches!(result, Err(EffectsHold::Opaque(_))),
                },
                "{body}: {result:?}"
            );
        }
    }

    fn no_retention(source: &str, name: &str) -> Result<&'static str, EffectsHold> {
        let name = name.to_owned();
        ::utils::compilation::run_compiler_on_str(source, move |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let function = program
                .functions
                .iter()
                .copied()
                .find(|function| tcx.def_path_str(function.to_def_id()) == name)
                .expect("exact fixture definition");
            let effects = NativeEffects::derive(&program);
            let proof = effects.certify_no_retention(function, 0)?;
            assert!(proof.matches(&effects, function, 0));
            Ok(proof.scope())
        })
        .expect("no-retention fixture compiles")
    }

    #[test]
    fn native_no_retention_certifies_written_through_and_offset_formals() {
        let source = format!(
            "{LIBC} pub unsafe fn row(target: *mut i32, n: usize) {{ let tmp = malloc(n * 4) as *mut i32; *tmp = 1; let mut i = 0; while i < n {{ *target.offset(i as isize) = *tmp.offset(i as isize); i += 1; }} free(tmp as *mut core::ffi::c_void); }} pub unsafe fn forward(target: *mut i32) {{ row(target.offset(1), 1); }}"
        );
        assert_eq!(
            no_retention(&source, "row"),
            Ok("native-per-argument-no-retention")
        );
        assert_eq!(
            no_retention(&source, "forward"),
            Ok("native-per-argument-no-retention")
        );
    }

    #[test]
    fn native_no_retention_holds_on_return_store_and_opaque_routes() {
        for body in [
            "target",
            "target.offset(1)",
            "id(target)",
            "{ *out = target; core::ptr::null_mut() }",
            "{ stash(target); core::ptr::null_mut() }",
            "{ let mut keep: *mut i32 = core::ptr::null_mut(); let cell: *mut *mut i32 = &mut keep; *cell = target; core::ptr::null_mut() }",
        ] {
            let source = format!(
                "{LIBC} extern \"C\" {{ fn stash(p: *mut i32); }} unsafe fn id(p: *mut i32) -> *mut i32 {{ p }} pub unsafe fn probe(target: *mut i32, out: *mut *mut i32) -> *mut i32 {{ {body} }}"
            );
            let result = no_retention(&source, "probe");
            assert!(
                matches!(result, Err(EffectsHold::Escape(_) | EffectsHold::Opaque(_))),
                "{body}: {result:?}"
            );
        }
    }

    #[test]
    fn native_opaque_and_recursive_calls_hold() {
        let source = r#"extern "C" { fn opaque(p: *mut i32); } pub unsafe fn probe(p: *mut i32) { opaque(p); }"#;
        assert!(matches!(
            verdict(&source, "probe"),
            Err(EffectsHold::Opaque(_))
        ));
        assert!(matches!(
            verdict("pub unsafe fn probe(p: *mut i32) { probe(p); }", "probe"),
            Err(EffectsHold::Cycle(_))
        ));
    }
}
