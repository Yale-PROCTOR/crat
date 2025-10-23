use etrace::some_or;
use points_to::andersen::{Loc, LocNode, PreAnalysisData, Solutions};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::{IndexVec, bit_set::ChunkedBitSet};
use rustc_middle::{
    mir::Local,
    ty::{Ty, TyCtxt, TyKind, TypingEnv},
};
use rustc_span::def_id::{DefId, LocalDefId};

/// Preprocess points-to analysis to use for the output parameter detection
#[derive(Debug)]
pub struct AliasResults {
    /// set of parameters that may alias each other
    pub aliases: FxHashMap<DefId, FxHashSet<Local>>,
    /// maps a location to the set of parameters that may point to it
    pub inv_params: FxHashMap<DefId, FxHashMap<Loc, FxHashSet<Local>>>,
    /// maps a Loc to its end Loc
    pub ends: IndexVec<Loc, Loc>,
    /// maps a static item to the corresponding Loc
    pub globals: FxHashMap<LocalDefId, Loc>,
    /// maps (function, local) to the corresponding node
    pub var_nodes: FxHashMap<(LocalDefId, Local), LocNode>,
    /// set of Locs of global variables
    pub non_fn_globals: ChunkedBitSet<Loc>,
    /// maps a Loc to the corresponding local
    pub index_locals: FxHashMap<DefId, FxHashMap<Loc, Local>>,
}

fn check_type_inner<'tcx>(
    pre: &PreAnalysisData<'tcx>,
    ty1: &Ty<'tcx>,
    ty2: &Ty<'tcx>,
    index1: Loc,
    index2: Loc,
    tcx: TyCtxt<'tcx>,
) -> bool {
    if ty1 == ty2 {
        return true;
    }
    let typing_env1 = TypingEnv::post_analysis(tcx, pre.index_info.get_owner(index1).to_def_id());
    let typing_env2 = TypingEnv::post_analysis(tcx, pre.index_info.get_owner(index2).to_def_id());
    let is_sized1 = ty1.is_sized(tcx, typing_env1);
    let is_sized2 = ty2.is_sized(tcx, typing_env2);
    if !is_sized1 || !is_sized2 {
        return true;
    }

    let layout1 = tcx.layout_of(typing_env1.as_query_input(*ty1)).unwrap();
    let layout2 = tcx.layout_of(typing_env2.as_query_input(*ty2)).unwrap();

    layout1.size.bytes() == layout2.size.bytes()
}

// Filter out the cases where the sizes of types of two global indices are not compatible
fn check_type_deref<'tcx>(
    pre: &PreAnalysisData<'tcx>,
    index1: Loc,
    index2: Loc,
    tcx: TyCtxt<'tcx>,
) -> bool {
    let ty1 = pre.index_info.get_ty(index1);
    let ty2 = pre.index_info.get_ty(index2);

    match (ty1.kind(), ty2.kind()) {
        (TyKind::RawPtr(ty1, _), TyKind::RawPtr(ty2, _))
        | (TyKind::RawPtr(ty1, _), TyKind::Ref(_, ty2, _)) => {
            check_type_inner(pre, ty1, ty2, index1, index2, tcx)
        }
        (_, _) => false,
    }
}

fn check_type<'tcx>(
    pre: &PreAnalysisData<'tcx>,
    index1: Loc,
    index2: Loc,
    tcx: TyCtxt<'tcx>,
) -> bool {
    let ty1 = pre.index_info.get_ty(index1);
    let ty2 = pre.index_info.get_ty(index2);

    if let TyKind::RawPtr(inner_ty1, _) = ty1.kind() {
        check_type_inner(pre, inner_ty1, &ty2, index1, index2, tcx)
    } else {
        false
    }
}

fn collect_param_alias<'tcx>(
    pre: &PreAnalysisData<'tcx>,
    solutions: &Solutions,
    locals: &ChunkedBitSet<Loc>,
    args: &[Option<Loc>],
    params: &[(Loc, Local)],
    fun_alias: &mut FxHashSet<Local>,
    tcx: TyCtxt<'tcx>,
) {
    for (skip, (_, i1)) in params.iter().enumerate() {
        for (_, i2) in params.iter().skip(skip + 1) {
            let index1 = args[i1.index() - 1].unwrap();
            let index2 = args[i2.index() - 1].unwrap();
            if (fun_alias.contains(i1) && fun_alias.contains(i2))
                || !check_type_deref(pre, index1, index2, tcx)
            {
                continue;
            }

            let mut sol1 = solutions[index1].clone();

            sol1.intersect(&solutions[index2]);
            sol1.subtract(locals);

            if !sol1.is_empty() {
                fun_alias.insert(*i1);
                fun_alias.insert(*i2);
            }
        }
    }
}

// Computes the aliasing information for the function parameters
pub fn compute_alias<'tcx>(
    pre: PreAnalysisData<'tcx>,
    solutions: &Solutions,
    inputs_map: &FxHashMap<DefId, usize>,
    tcx: TyCtxt<'tcx>,
    check_global_alias: bool,
    check_param_alias: bool,
) -> AliasResults {
    let mut aliases: FxHashMap<_, FxHashSet<Local>> = FxHashMap::default();
    let mut inv_params: FxHashMap<_, FxHashMap<_, FxHashSet<Local>>> = FxHashMap::default();
    let mut index_locals: FxHashMap<_, FxHashMap<Loc, Local>> = FxHashMap::default();
    let non_fn_globals = pre.non_fn_globals.iter().fold(
        ChunkedBitSet::new_empty(pre.index_info.len()),
        |mut acc, g| {
            acc.insert(*g);
            acc
        },
    );

    for (def_id, inputs) in inputs_map {
        let local_def_id = some_or!(def_id.as_local(), continue);
        let body = tcx
            .mir_drops_elaborated_and_const_checked(local_def_id)
            .borrow();
        let mut params = vec![];
        let mut locals = ChunkedBitSet::new_empty(pre.index_info.len());
        let mut index_local = FxHashMap::default();

        // Aliases of the function parameters
        let mut fun_alias = FxHashSet::default();
        // Map of location to set of parameters that may point to the location
        let mut inv_param: FxHashMap<_, FxHashSet<_>> = FxHashMap::default();

        for (local, decl) in body.local_decls.iter_enumerated() {
            let g_index = pre.var_nodes[&(local_def_id, local)].index;
            let g_index_end = pre.index_info.ends[g_index];
            index_local.extend((g_index..=g_index_end).map(|loc| (loc, local)));

            if (1..=*inputs).contains(&local.index()) {
                let ty = decl.ty;
                let TyKind::RawPtr(..) = ty.kind() else {
                    continue;
                };
                params.push((g_index, local));
            }
            locals.insert(g_index);
        }

        if check_param_alias && pre.call_args.contains_key(&local_def_id) {
            let call_args = pre.call_args.get(&local_def_id).unwrap();

            for args in call_args {
                if fun_alias.len() == params.len() {
                    break;
                }
                collect_param_alias(&pre, solutions, &locals, args, &params, &mut fun_alias, tcx)
            }
        }

        if check_global_alias {
            for (index, p) in params {
                let mut sol = solutions[index].clone();
                sol.subtract(&locals);
                sol.intersect(&non_fn_globals);

                for s in sol.iter() {
                    if check_type(&pre, index, s, tcx) {
                        inv_param.entry(s).or_default().insert(p);
                    }
                }
            }
        }

        aliases.insert(*def_id, fun_alias);
        inv_params.insert(*def_id, inv_param);
        index_locals.insert(*def_id, index_local);
    }

    AliasResults {
        aliases,
        inv_params,
        ends: pre.index_info.ends,
        globals: pre.globals,
        var_nodes: pre.var_nodes,
        non_fn_globals,
        index_locals,
    }
}

#[derive(Clone, Debug)]
pub struct PreAnalysisContext<'a> {
    /// the function being analyzed
    pub local_def_id: LocalDefId,
    /// set of parameters that may alias each other
    pub alias: &'a FxHashSet<Local>,
    /// a location to the set of parameters that may point to it
    pub inv_param: &'a FxHashMap<Loc, FxHashSet<Local>>,
    /// maps a Loc to its end Loc
    pub ends: &'a IndexVec<Loc, Loc>,
    // maps a Loc to the corresponding local in the function
    pub index_local_map: &'a FxHashMap<Loc, Local>,
    /// set of Locs of global variables
    pub globals: &'a ChunkedBitSet<Loc>,
    /// the solutions of the may-points-to analysis
    pub solutions: &'a Solutions,
    /// maps (function, local) to the corresponding node
    pub var_nodes: &'a FxHashMap<(LocalDefId, Local), LocNode>,
}

impl<'a> PreAnalysisContext<'a> {
    pub fn new(def_id: DefId, pre_data: &'a AliasResults, solutions: &'a Solutions) -> Self {
        Self {
            local_def_id: def_id.as_local().unwrap(),
            alias: pre_data.aliases.get(&def_id).unwrap(),
            inv_param: pre_data.inv_params.get(&def_id).unwrap(),
            ends: &pre_data.ends,
            index_local_map: pre_data.index_locals.get(&def_id).unwrap(),
            globals: &pre_data.non_fn_globals,
            var_nodes: &pre_data.var_nodes,
            solutions,
        }
    }

    pub fn check_index_global(&self, index: Loc) -> FxHashSet<Local> {
        if self.inv_param.contains_key(&index) {
            let params = self.inv_param.get(&index).unwrap();
            return params.clone();
        }
        FxHashSet::default()
    }
}
