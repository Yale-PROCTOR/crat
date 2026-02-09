#![allow(dead_code)]
#![allow(unused_imports)]

use eliminable_temporaries::eliminable_temporaries;
use itertools::Itertools;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_index::bit_set::MixedBitSet;
use rustc_middle::{
    mir::{Body, Local},
    ty::TyCtxt,
};

use crate::{
    analyses::{
        mir::{CallGraphPostOrder, CallKind, MirFunctionCall, TerminatorExt},
        type_qualifier::foster::mutability::{Mutability, MutabilityResult},
    },
    utils::rustc::RustProgram,
};

mod eliminable_temporaries;

pub type OutputParams = FxHashMap<LocalDefId, MixedBitSet<Local>>;

pub fn show_output_params(
    program: &RustProgram,
    mutability_result: &MutabilityResult,
    aliases: &FxHashMap<LocalDefId, FxHashMap<Local, FxHashSet<Local>>>,
) {
    let output_params = compute_output_params(program, mutability_result, aliases);

    for (did, noalias_params) in output_params {
        let noalias_params_str = noalias_params
            .iter()
            .map(|param| format!("{:?}", param))
            .join(", ");
        println!("@{}: {noalias_params_str}", program.tcx.def_path_str(did));
    }
}

pub fn compute_output_params(
    program: &RustProgram,
    mutability_result: &MutabilityResult,
    aliases: &FxHashMap<LocalDefId, FxHashMap<Local, FxHashSet<Local>>>,
) -> OutputParams {
    let mut output_params = FxHashMap::default();
    output_params.reserve(program.functions.len());
    let mut copies = FxHashMap::default();
    copies.reserve(program.functions.len());

    for &did in program.functions.iter() {
        let body = &*program
            .tcx
            .mir_drops_elaborated_and_const_checked(did)
            .borrow();
        output_params.insert(
            did,
            conservative(program.tcx, body, aliases, mutability_result),
        );
        copies.insert(did, eliminable_temporaries(body));
    }

    let tcx = program.tcx;
    for scc in CallGraphPostOrder::new(program).sccs() {
        loop {
            let mut changed = false;
            for &def_id in scc {
                let def_id = def_id.expect_local();
                let body = &*tcx.mir_drops_elaborated_and_const_checked(def_id).borrow();
                changed = changed
                    || iterate(
                        body,
                        copies.get(&def_id).unwrap(),
                        aliases,
                        mutability_result,
                        &mut output_params,
                        tcx,
                    );
            }
            if !changed {
                break;
            }
        }
    }

    output_params
}

fn conservative<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    aliases: &FxHashMap<LocalDefId, FxHashMap<Local, FxHashSet<Local>>>,
    mutability_result: &MutabilityResult,
) -> MixedBitSet<Local> {
    let body_did = body.source.def_id();
    let function_facts = mutability_result.function_facts(body_did.expect_local(), tcx);
    let local_aliases = aliases.get(&body_did.expect_local());

    let mut output_params = MixedBitSet::new_empty(body.local_decls.len());
    for (local, _) in
        body.args_iter()
            .zip(function_facts.skip(1))
            .filter(|(_, mutability_qualifiers)| {
                matches!(mutability_qualifiers.first(),
                    Some(&mutability)
                    if mutability == Mutability::Mut
                )
            })
    {
        // let local_decl = &body.local_decls[local];
        // if !local_decl.is_user_variable() {
        //     continue
        // }
        output_params.insert(local);
    }

    if let Some(local_aliases) = local_aliases {
        for arg in body.args_iter() {
            if let Some(aliased_with) = local_aliases.get(&arg) {
                for &local in aliased_with {
                    if !body.args_iter().any(|a| a == local) {
                        let def_path_str = tcx.def_path_str(body_did);
                        #[cfg(debug_assertions)]
                        eprintln!("@{def_path_str}: {arg:?} removed because it aliases {local:?}");
                        output_params.remove(arg);
                        break;
                    }
                }
            }
        }
    }

    output_params
}

fn iterate<'tcx>(
    body: &Body<'tcx>,
    copies: &MixedBitSet<Local>,
    aliases: &FxHashMap<LocalDefId, FxHashMap<Local, FxHashSet<Local>>>,
    mutability_result: &MutabilityResult,
    known_facts: &mut OutputParams,
    tcx: TyCtxt<'tcx>,
) -> bool {
    let body_did = body.source.def_id();
    let function_facts = mutability_result.function_facts(body_did.expect_local(), tcx);
    let local_aliases = aliases.get(&body_did.expect_local());
    let transitive_output_position_temporaries =
        transitive_output_position_temporaries(known_facts, copies, body, tcx);
    let output_params = known_facts
        .get_mut(&body.source.def_id().expect_local())
        .unwrap();

    let mut changed = false;
    for (arg, _) in
        body.args_iter()
            .zip(function_facts.skip(1))
            .filter(|(_, mutability_qualifiers)| {
                matches!(mutability_qualifiers
                    .first(),
                    Some(&mutability)
                    if mutability == Mutability::Mut
                )
            })
    {
        let aliases_non_params = local_aliases
            .and_then(|la| la.get(&arg))
            .map(|aliased| {
                aliased.iter().any(|&local| {
                    !body.args_iter().any(|a| a == local)
                        && !transitive_output_position_temporaries.contains(local)
                })
            })
            .unwrap_or(false);

        if !aliases_non_params {
            let def_path_str = tcx.def_path_str(body_did);
            #[cfg(debug_assertions)]
            eprintln!(
                "@{def_path_str}: {arg:?} added because it aliases a transitive output position temporary"
            );
            changed = changed || output_params.insert(arg);
        }
    }

    changed
}

fn transitive_output_position_temporaries<'tcx>(
    known_facts: &OutputParams,
    copies: &MixedBitSet<Local>,
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> MixedBitSet<Local> {
    let mut transitive_output_temporaries = MixedBitSet::new_empty(body.local_decls.len());
    for bb_data in body.basic_blocks.iter() {
        let Some(terminator) = &bb_data.terminator else {
            continue;
        };

        let Some(MirFunctionCall { func, args, .. }) = terminator.as_call(tcx) else {
            continue;
        };

        let CallKind::FreeStanding(callee) = func else {
            continue;
        };

        for arg in known_facts
            .get(&callee)
            .unwrap()
            .iter()
            .map(|local| local.index() - 1)
            .map(|index| &args[index])
            .filter_map(|arg| arg.node.place().and_then(|place| place.as_local()))
            .filter(|&arg| copies.contains(arg))
        {
            transitive_output_temporaries.insert(arg);
        }
    }
    transitive_output_temporaries
}

// #[cfg(test)]
// mod tests {
//     use crate::type_qualifier::mutability_analysis;
//     use utils::test;

//     use super::*;

//     #[test]
//     fn regression_libtree_output_params() {
//         utils::rustc::run_compiler(utils::rustc::SourceCode::Libtree, |program| {
//             let mutability_result = mutability_analysis(&program);
//             show_output_params(&program, &mutability_result);
//         })
//     }
// }
