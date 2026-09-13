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
        Parameter { function: u32, argument: usize },
        Retirement(Site),
        Opaque(Site),
        Cycle(u32),
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
    mir::{Local, StatementKind, TerminatorKind},
    ty::{TyCtxt, TyKind},
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
}

/// Tied to the deriving index and exact formal; never a model-kind certificate.
/// The caller must still prove no-retention, peer disjointness and lifetimes.
pub(crate) struct NonConsumingProof<'a, 'tcx> {
    index: &'a NativeEffects<'tcx>,
    callee: LocalDefId,
    proof: closure::Proof,
}

impl<'tcx> NativeEffects<'tcx> {
    pub(crate) fn derive(program: &RustProgram<'tcx>) -> Self {
        use closure::{Effect, FunctionFacts, Site};
        let mut functions = program.functions.clone();
        functions.sort_by_key(|function| function.local_def_index.as_u32());
        functions.dedup();
        let mut facts = BTreeMap::new();
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
        }
    }

    pub(crate) fn certify(
        &self,
        callee: LocalDefId,
        argument: usize,
    ) -> Result<NonConsumingProof<'_, 'tcx>, EffectsHold> {
        Ok(NonConsumingProof {
            index: self,
            callee,
            proof: closure::certify(&self.facts, callee.local_def_index.as_u32(), argument)?,
        })
    }
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
