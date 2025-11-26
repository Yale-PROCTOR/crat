use std::{
    collections::BTreeMap,
    fs::File,
    path::{Path, PathBuf},
};

use etrace::some_or;
use rustc_ast::{
    ast::*,
    mut_visit::{self, MutVisitor},
    ptr::P,
};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    Expr as HirExpr, ExprKind as HirExprKind, HirId, Item as HirItem, ItemKind as HirItemKind,
    Node as HirNode, PatKind, Path as HirPath, QPath, def::Res, definitions::DefPathData,
    intravisit,
};
use rustc_index::IndexVec;
use rustc_middle::{
    hir::nested_filter,
    mir::{BasicBlock, Local, Location, TerminatorKind},
    ty::{TyCtxt, TyKind as MirTyKind},
};
use rustc_span::{FileName, RealFileName, Span, def_id::LocalDefId};
use utils::{
    ast::transform_ast,
    expr,
    ir::{AstToHir, AstToHirMapper, HirToThir, ThirToMir, mir_ty_to_string},
    stmt, ty,
};

use crate::outparam_replacer::ai::analysis::*;

#[derive(Default, Clone, Copy, Debug)]
struct Counter {
    removed_value_defs: usize,
    removed_pointer_defs: usize,
    removed_pointer_uses: usize,
    direct_returns: usize,
    success_returns: usize,
    failure_returns: usize,
    removed_flag_sets: usize,
    removed_flag_defs: usize,
}

#[derive(Debug, Clone)]
struct Param {
    /// index of the parameter in the signature
    index: ParamIdx,
    /// name of the parameter
    name: String,
    /// whether the parameter is must output parameter
    must: bool,
    /// string representation of the type of the parameter
    ty_str: String,
    /// return value indicating success for may output parameter
    succ_value: Option<SuccValue>,

    /// if true, skip flag declaration
    simplify_flag_decl: bool,
    /// if true, skip value declaration
    simplify_value_decl: bool,
    /// if true, skip reference declaration
    simplify_ref_decl: bool,
    /// HirId of return and value written to param before return
    direct_returns: FxHashMap<HirId, String>,
}

impl Param {
    // convert param to return type item which does not use origin return type
    fn to_non_orig_ret_ty(&self) -> Option<ReturnTyItem> {
        if self.must {
            Some(ReturnTyItem::Type(self.clone()))
        } else if self.succ_value.is_none() {
            Some(ReturnTyItem::Option(self.clone()))
        } else {
            None
        }
    }
}

rustc_index::newtype_index! {
    #[orderable]
    #[debug_format = "p{}"]
    pub struct ParamIdx {}
}

rustc_index::newtype_index! {
    #[orderable]
    #[debug_format = "ret{}"]
    pub struct RetIdx {}
}

type WriteForReturn = FxHashMap<Location, (FxHashSet<ParamIdx>, FxHashSet<ParamIdx>)>;

struct Func {
    is_unit: bool,
    index_map: BTreeMap<ParamIdx, Param>,
    /// target return type after transformation
    return_tys: IndexVec<RetIdx, ReturnTyItem>,
    /// locations where the parameter is fully written. empty for must parameters
    write_locs: FxHashMap<ParamIdx, Vec<Location>>,

    /// HirIds where deref of the parameter can be simplified
    simpl_derefs: FxHashMap<HirId, ParamIdx>,
    /// Locations where assign to the parameter can be simplified
    simpl_assigns: FxHashSet<Location>,
    /// location where return value is written and params written at the point
    wfrs: Option<WriteForReturn>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum SuccValue {
    Int(i128),
    Uint(u128),
    Bool(bool),
}

impl SuccValue {
    fn from(param: &OutputParam) -> Option<Self> {
        if param.must {
            return None;
        }
        match &param.return_values {
            ReturnValues::Int(succ, fail) => {
                let succ = succ.gamma()?;
                if succ.len() != 1 {
                    return None;
                }
                let fail = fail.gamma()?;
                if !succ.is_disjoint(fail) {
                    return None;
                }
                Some(Self::Int(*succ.first().unwrap()))
            }
            ReturnValues::Uint(succ, fail) => {
                let succ = succ.gamma()?;
                if succ.len() != 1 {
                    return None;
                }
                let fail = fail.gamma()?;
                if !succ.is_disjoint(fail) {
                    return None;
                }
                Some(Self::Uint(*succ.first().unwrap()))
            }
            ReturnValues::Bool(succ, fail) => {
                let succ = succ.gamma();
                if succ.len() != 1 {
                    return None;
                }
                let succ = succ.first().unwrap();
                let fail = fail.gamma();
                if fail.len() != 1 {
                    return None;
                }
                let fail = fail.first().unwrap();
                if succ == fail {
                    return None;
                }
                Some(Self::Bool(*succ))
            }
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
enum ReturnTyItem {
    /// original return type
    Orig,
    /// must output parameter
    Type(Param),
    /// rewrite may parameter with original return to result type
    Result(Param),
    /// rewrite may parameter to option type
    Option(Param),
}

pub fn transform(
    tcx: TyCtxt<'_>,
    dir: &Path,
    lib_name: &str,
    config: &crate::outparam_replacer::Config,
) {
    let analysis_result: AnalysisResult = if let Some(file) = &config.analysis_file {
        let file = File::open(file).unwrap();
        serde_json::from_reader(file).unwrap()
    } else {
        analyze(config, false, tcx).0
    };

    let mut path_to_mod_id = FxHashMap::default();
    tcx.hir_for_each_module(|mod_id| {
        let def_path = tcx.def_path(mod_id.to_def_id());
        let mut path = dir.to_path_buf();
        for data in def_path.data {
            let DefPathData::TypeNs(name) = data.data else { panic!() };
            path.push(name.as_str());
        }
        path.set_extension("rs");
        path_to_mod_id.insert(path, mod_id);
    });

    let hir_to_thir = utils::ir::map_hir_to_thir(tcx);
    let mut thir_to_mir = FxHashMap::default();
    for def_id in tcx.hir_body_owners() {
        thir_to_mir.insert(def_id, utils::ir::map_thir_to_mir(def_id, false, tcx));
    }

    let mut hir_visitor = HirVisitor::new(tcx, &hir_to_thir, &thir_to_mir);
    tcx.hir_visit_all_item_likes_in_crate(&mut hir_visitor);
    hir_visitor
        .assigns
        .retain(|_, assign| !hir_visitor.call_in_assigns.contains(&assign.hir_id));

    let mut funcs = FxHashMap::default();
    let mut write_args: FxHashMap<_, FxHashMap<_, _>> = FxHashMap::default();
    let mut counter = Counter::default();

    for id in tcx.hir_free_items() {
        let item = tcx.hir_item(id);
        let HirItemKind::Fn { body, .. } = item.kind else {
            continue;
        };

        let local_def_id = id.owner_id.def_id;
        let def_id = local_def_id.to_def_id();
        let name = tcx.def_path_str(def_id);
        let fn_analysis_result = some_or!(analysis_result.get(&name), continue);
        let hir_body = tcx.hir_body(body);
        let mir_body = tcx
            .mir_drops_elaborated_and_const_checked(local_def_id)
            .borrow();

        let sig = tcx.fn_sig(def_id).skip_binder().skip_binder();
        let is_unit = sig.output().is_unit();

        let mut succ_param = None;
        let mut index_map: BTreeMap<_, _> = BTreeMap::new();
        let mut write_locs: FxHashMap<_, Vec<_>> = FxHashMap::default();
        let mut simpl_derefs: FxHashMap<_, _> = FxHashMap::default();
        let mut simpl_assigns: FxHashSet<_> = FxHashSet::default();

        // locations of write for return value
        let wfrs = if config.simplify && !is_unit && !fn_analysis_result.wfrs.is_empty() {
            Some(
                fn_analysis_result
                    .wfrs
                    .iter()
                    .map(|wfr| {
                        let loc = Location {
                            block: BasicBlock::from_usize(wfr.block),
                            statement_index: wfr.statement_index,
                        };
                        (
                            loc,
                            (
                                wfr.mays
                                    .iter()
                                    .map(|i| ParamIdx::from_usize(*i))
                                    .collect::<FxHashSet<_>>(),
                                wfr.musts
                                    .iter()
                                    .map(|i| ParamIdx::from_usize(*i))
                                    .collect::<FxHashSet<_>>(),
                            ),
                        )
                    })
                    .collect::<FxHashMap<_, _>>(),
            )
        } else {
            None
        };

        for p in &fn_analysis_result.output_params {
            let OutputParam {
                index,
                must,
                complete_writes,
                ..
            } = p;
            let param = &hir_body.params[*index];
            let param_index = ParamIdx::from_usize(*index);
            let mir_local = Local::from_usize(*index + 1);
            let PatKind::Binding(_, _hir_id, ident, _) = param.pat.kind else { unreachable!() };
            let name = ident.name.to_string();

            let mir_ty = mir_body.local_decls[mir_local].ty;
            let ty_str = match mir_ty.kind() {
                MirTyKind::RawPtr(ty, ..) => mir_ty_to_string(*ty, tcx),
                _ => unreachable!("{mir_ty:?}"),
            };

            // simplify 1: once may parameter is fully written, flag sets can be removed
            let rcfws = if config.simplify {
                fn_analysis_result
                    .rcfws
                    .get(&param_index.index())
                    .cloned()
                    .unwrap_or_default()
                    .into_iter()
                    .map(|(block, statement_index)| Location {
                        block: BasicBlock::from_usize(block),
                        statement_index,
                    })
                    .collect::<FxHashSet<_>>()
            } else {
                FxHashSet::default()
            };
            let mut simplify_flag_decl = config.simplify && !is_unit;
            complete_writes.iter().for_each(|cw| {
                let CompleteWrite {
                    block,
                    statement_index,
                    write_arg,
                } = cw;
                let block = BasicBlock::from_usize(*block);
                let bbd = &mir_body.basic_blocks[block];
                let loc = Location {
                    block,
                    statement_index: *statement_index,
                };
                if *statement_index == bbd.statements.len() {
                    let t = bbd.terminator();
                    assert!(matches!(t.kind, TerminatorKind::Call { .. }), "{t:?}");

                    if config.simplify && rcfws.contains(&loc) {
                        counter.removed_flag_sets += 1;
                    } else if let Some(arg) = write_arg {
                        write_args
                            .entry((local_def_id, loc))
                            .or_default()
                            .insert(ParamIdx::from_usize(*arg), name.clone());
                        simplify_flag_decl = false;
                    }
                } else if config.simplify && rcfws.contains(&loc) {
                    counter.removed_flag_sets += 1;
                } else {
                    write_locs.entry(param_index).or_default().push(loc);
                    simplify_flag_decl = false;
                }
            });

            // simplify 2: for assignments before return, return the value directly
            let mut direct_returns = FxHashMap::default();
            let deref_uses = if config.simplify
                && let Some(derefs) = hir_visitor.deref_uses.get(&(local_def_id, mir_local))
            {
                if is_unit {
                    derefs
                        .iter()
                        .map(|deref| (deref, param_index))
                        .collect::<FxHashSet<_>>()
                } else {
                    derefs
                        .iter()
                        .filter_map(|deref| {
                            if let Some(Assign { loc, span, rhs, .. }) =
                                hir_visitor.assigns.get(&deref.hir_id)
                                && let Some(returns) = hir_visitor.returns.get_mut(&local_def_id)
                            {
                                let source_map = tcx.sess.source_map();

                                let assigned_returns = returns
                                    .extract_if(|(ret_span, _)| {
                                        source_map
                                            .span_to_snippet(span.between(*ret_span))
                                            .unwrap()
                                            .chars()
                                            .all(|c| c.is_whitespace() || c == ';')
                                    })
                                    .collect::<Vec<_>>();

                                assert!(assigned_returns.len() <= 1);

                                if let Some((_, return_hir_id)) = assigned_returns.first() {
                                    // If there is an assignment before return, remove the assign and return the value
                                    direct_returns.insert(*return_hir_id, rhs.clone());
                                    simpl_assigns.insert(*loc);
                                    None
                                } else {
                                    Some((deref, param_index))
                                }
                            } else {
                                Some((deref, param_index))
                            }
                        })
                        .collect::<FxHashSet<_>>()
                }
            } else {
                FxHashSet::default()
            };
            // check if there are no uses of pointer and value
            let simplify_value_decl = config.simplify
                && !is_unit
                && deref_uses.is_empty()
                && !hir_visitor.ref_uses.contains(&(local_def_id, mir_local));

            // simplify 3: rewrite dereferenced ptr to direct value uses
            let mut simplify_ref_decl = false;
            if config.simplify {
                let deref_uses = if !hir_visitor.ref_uses.contains(&(local_def_id, mir_local)) {
                    simplify_ref_decl = true;
                    deref_uses
                        .into_iter()
                        .map(|(deref, param_index)| (deref.hir_id, param_index))
                        .collect::<FxHashMap<_, _>>()
                } else {
                    // if there are ref uses, only simplify derefs in call or return
                    deref_uses
                        .into_iter()
                        .filter_map(|(deref, param_index)| {
                            if deref.in_call_or_ret {
                                Some((deref.hir_id, param_index))
                            } else {
                                None
                            }
                        })
                        .collect::<FxHashMap<_, _>>()
                };

                simpl_derefs.extend(deref_uses);
            }

            // find the first may parameter which has a value indicating success
            let succ_value = if succ_param.is_none() {
                SuccValue::from(p)
            } else {
                None
            };
            if succ_value.is_some() {
                succ_param = Some(param_index);
            }

            index_map.insert(
                param_index,
                Param {
                    index: param_index,
                    name,
                    must: *must,
                    ty_str,
                    succ_value,
                    simplify_flag_decl,
                    simplify_value_decl,
                    simplify_ref_decl,
                    direct_returns,
                },
            );
        }

        // given the analysis result, decide how to transform the return type
        let mut return_tys: IndexVec<RetIdx, ReturnTyItem> = IndexVec::new();

        if let Some(index) = succ_param {
            // if there is a may parameter which has a value indicating success,
            // rewrite it to result type
            let param = index_map[&index].clone();
            return_tys.push(ReturnTyItem::Result(param));
        } else if !is_unit {
            // if not, keep the original return type
            return_tys.push(ReturnTyItem::Orig);
        }

        return_tys.extend(index_map.values().filter_map(|p| p.to_non_orig_ret_ty()));

        let func = Func {
            is_unit,
            index_map,
            return_tys,
            write_locs,
            simpl_derefs,
            simpl_assigns,
            wfrs,
        };
        funcs.insert(local_def_id, func);
    }

    let res = transform_ast(
        |krate| {
            let source_map = tcx.sess.source_map();
            let filename = source_map.span_to_filename(krate.spans.inner_span);
            let p = match filename {
                FileName::Real(RealFileName::LocalPath(p)) => p,
                FileName::Custom(p) => PathBuf::from(p),
                _ => unreachable!(),
            };

            if p.file_name().unwrap().to_str().unwrap() == lib_name {
                return false;
            }

            let mod_id: rustc_hir::def_id::LocalModDefId = path_to_mod_id[&p];
            let (module, _, _) = tcx.hir_get_module(mod_id);
            let mut mapper = AstToHirMapper::new(tcx);
            mapper.map_crate_to_mod(krate, module, false);

            let mut visitor = TransformVisitor {
                tcx,
                ast_to_hir: mapper.ast_to_hir,
                hir_to_thir: &hir_to_thir,
                thir_to_mir: &thir_to_mir,
                funcs: &funcs,
                current_fns: vec![],
                write_args: &write_args,
                bounds: &hir_visitor.bounds,
                call_in_ret: &hir_visitor.call_in_ret,
                updated: false,
                counter: &mut counter,
            };
            visitor.visit_crate(krate);
            visitor.updated
        },
        tcx,
    );

    if config.simplify {
        println!("{counter:#?}");
    }

    res.apply();
}

struct TransformVisitor<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    ast_to_hir: AstToHir,
    hir_to_thir: &'a HirToThir,
    thir_to_mir: &'a FxHashMap<LocalDefId, ThirToMir>,
    funcs: &'a FxHashMap<LocalDefId, Func>,
    current_fns: Vec<LocalDefId>,
    /// at location, caller param named 'String' is used 'ParamIdx'th argument of call
    write_args: &'a FxHashMap<(LocalDefId, Location), FxHashMap<ParamIdx, String>>,
    /// bound occurrence (ident) span to def_id
    bounds: &'a FxHashMap<Span, LocalDefId>,
    /// maps spans of returns to calls inside them
    call_in_ret: &'a FxHashMap<Span, LocalDefId>,
    /// is this file updated
    updated: bool,
    /// tracks simplification status
    counter: &'a mut Counter,
}

impl TransformVisitor<'_, '_> {
    #[inline]
    fn current_fn(&self) -> LocalDefId {
        *self.current_fns.last().unwrap()
    }

    #[inline]
    fn replace_expr(&mut self, old: &mut Expr, new: Expr) {
        self.updated = true;
        let span = old.span;
        *old = new;
        old.span = span;
    }

    fn get_assign(
        &self,
        expr: &Expr,
        must: bool,
        rhs: String,
        index: ParamIdx,
        loc: Location,
    ) -> String {
        let arg = pprust::expr_to_string(expr);
        let write_args = self.write_args.get(&(self.current_fn(), loc));
        let set_flag = if let Some(arg_to_param) = write_args
            && let Some(caller_param) = arg_to_param.get(&index)
        {
            format!("; {caller_param}___s = true")
        } else {
            String::new()
        };

        // TODO: enable more robust detection
        if arg.contains("&mut ") {
            if must {
                format!("*({arg}) = {rhs}{set_flag}")
            } else {
                format!("if let Some(v___) = {rhs} {{ *({arg}) = v___{set_flag} }}")
            }
        } else if must {
            format!("if !({arg}.is_null()) {{ *({arg}) = {rhs}{set_flag} }}")
        } else {
            format!(
                "if !(({arg}).is_null()) {{ if let Some(v___) = {rhs} {{ *({arg}) = v___{set_flag} }} }}"
            )
        }
    }

    fn get_simpl_name(&self, param: &Param, hir_id: Option<HirId>) -> Option<String> {
        let hir_id = hir_id?;
        let name = param.direct_returns.get(&hir_id)?;
        Some(name.clone())
    }

    fn get_name(&mut self, param: &Param, hir_id: Option<HirId>) -> String {
        if let Some(name) = self.get_simpl_name(param, hir_id) {
            self.counter.direct_returns += 1;
            name
        } else {
            format!("{}___v", param.name)
        }
    }

    fn get_return_value(
        &mut self,
        func: &Func,
        wfr: Option<&(FxHashSet<ParamIdx>, FxHashSet<ParamIdx>)>,
        orig_ret: Option<String>,
        hir_id: Option<HirId>,
    ) -> String {
        let mut ret_vals = vec![];
        let orig_ret = orig_ret.as_ref();
        for ret_ty in &func.return_tys {
            let ret_val = match ret_ty {
                ReturnTyItem::Orig => orig_ret.unwrap().clone(),
                ReturnTyItem::Type(param) => self.get_name(param, hir_id),
                ReturnTyItem::Result(param) => {
                    let name = self.get_name(param, hir_id);
                    if let Some((may, must)) = wfr {
                        if must.contains(&param.index) {
                            self.counter.success_returns += 1;
                            format!("Ok({name})")
                        } else if !may.contains(&param.index) {
                            self.counter.failure_returns += 1;
                            format!("Err({})", orig_ret.unwrap())
                        } else {
                            format!(
                                "if {}___s {{ Ok({}) }} else {{ Err({}) }}",
                                param.name,
                                name,
                                orig_ret.unwrap()
                            )
                        }
                    } else {
                        format!(
                            "if {}___s {{ Ok({}) }} else {{ Err({}) }}",
                            param.name,
                            name,
                            orig_ret.unwrap()
                        )
                    }
                }
                ReturnTyItem::Option(param) => {
                    let name = self.get_name(param, hir_id);
                    if let Some((may, must)) = wfr {
                        if must.contains(&param.index) {
                            self.counter.success_returns += 1;
                            format!("Some({name})")
                        } else if !may.contains(&param.index) {
                            self.counter.failure_returns += 1;
                            String::from("None")
                        } else {
                            format!("if {}___s {{ Some({}) }} else {{ None }}", param.name, name)
                        }
                    } else {
                        format!("if {}___s {{ Some({}) }} else {{ None }}", param.name, name)
                    }
                }
            };
            ret_vals.push(ret_val);
        }
        if ret_vals.len() == 1 {
            ret_vals.pop().unwrap()
        } else {
            format!("({})", ret_vals.join(", "))
        }
    }

    fn get_mir_locs_for_expr(&self, expr_id: NodeId) -> Option<Vec<Location>> {
        let hir_expr = self.ast_to_hir.get_expr(expr_id, self.tcx)?;

        let hir_id = hir_expr.hir_id;
        let owner_id = hir_id.owner.def_id;

        let thir_to_mir = self.thir_to_mir.get(&owner_id)?;

        let thir_expr_id = self.hir_to_thir.exprs.get(&hir_expr.hir_id)?;

        thir_to_mir
            .expr_to_locs
            .get(thir_expr_id)
            .cloned()
            .map(|locs| locs.to_vec())
    }

    fn get_mir_loc_for_expr(&self, expr_id: NodeId) -> Option<Location> {
        let mir_locs = self.get_mir_locs_for_expr(expr_id)?;

        if mir_locs.len() == 1 {
            Some(mir_locs[0])
        } else {
            // we expect only one mir location for expr (e.g., assignment, call)
            None
        }
    }
}

impl MutVisitor for TransformVisitor<'_, '_> {
    fn visit_item(&mut self, item: &mut Item) {
        if !matches!(item.kind, ItemKind::Fn(_)) {
            mut_visit::walk_item(self, item);
            return;
        };

        let node_id = item.id;
        let hir_item = self
            .ast_to_hir
            .get_item(node_id, self.tcx)
            .unwrap_or_else(|| panic!("Failed to find HIR item to node {node_id:?}"));
        let local_def_id = hir_item.owner_id.def_id;
        self.current_fns.push(local_def_id);
        mut_visit::walk_item(self, item);

        if let ItemKind::Fn(box fn_item) = &mut item.kind
            && let Some(func) = self.funcs.get(&local_def_id)
            && !func.index_map.is_empty()
        {
            // remove output parameters from input types
            fn_item.sig.decl.inputs = fn_item
                .sig
                .decl
                .inputs
                .iter()
                .cloned()
                .enumerate()
                .filter_map(|(i, p)| {
                    if func.index_map.contains_key(&ParamIdx::from_usize(i)) {
                        None
                    } else {
                        Some(p)
                    }
                })
                .collect();

            // rewrite return types
            let orig_return_ty = match &fn_item.sig.decl.output {
                FnRetTy::Ty(ty) => Some(ty),
                FnRetTy::Default(_) => None,
            };

            let mut ret_tys = vec![];
            for ret_ty in &func.return_tys {
                let ret_ty_str = match ret_ty {
                    ReturnTyItem::Orig => pprust::ty_to_string(orig_return_ty.unwrap()),
                    ReturnTyItem::Type(param) => param.ty_str.clone(),
                    ReturnTyItem::Result(param) => format!(
                        "Result<{}, {}>",
                        param.ty_str,
                        pprust::ty_to_string(orig_return_ty.unwrap())
                    ),
                    ReturnTyItem::Option(param) => format!("Option<{}>", param.ty_str),
                };
                ret_tys.push(ret_ty_str);
            }
            let new_return_ty = if ret_tys.len() == 1 {
                ty!("{}", ret_tys[0])
            } else {
                let str = ret_tys.join(", ");
                ty!("({})", str)
            };

            fn_item.sig.decl.output = FnRetTy::Ty(P(new_return_ty));

            // add value, ref, flag local declarations
            for param in func.index_map.values() {
                let value_decl = stmt!(
                    "let mut {0}___v: {1} = std::mem::transmute([0u8; std::mem::size_of::<{1}>()]);",
                    param.name,
                    param.ty_str
                );
                let ref_decl = stmt!(
                    "let mut {0}: *mut {1} = &mut {0}___v;",
                    param.name,
                    param.ty_str
                );
                let flag_decl = stmt!("let mut {}___s: bool = false;", param.name);

                let stmts = &mut fn_item.body.as_mut().unwrap().stmts;

                if param.simplify_ref_decl {
                    self.counter.removed_pointer_defs += 1;
                } else {
                    stmts.insert(0, ref_decl);
                }

                if param.simplify_value_decl {
                    self.counter.removed_value_defs += 1;
                } else {
                    stmts.insert(0, value_decl);
                }

                if !param.must {
                    if param.simplify_flag_decl {
                        self.counter.removed_flag_defs += 1;
                    } else {
                        stmts.insert(0, flag_decl);
                    }
                }
            }

            // for unit function without return statement, add a return
            if func.is_unit {
                let stmts = &mut fn_item.body.as_mut().unwrap().stmts;
                let ret = self.get_return_value(func, None, None, None);
                let ret_stmt = stmt!("return {};", ret);
                stmts.push(ret_stmt);
            }

            self.updated = true;
        }
        self.current_fns.pop();
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        mut_visit::walk_expr(self, expr);

        match &mut expr.kind {
            ExprKind::Assign(box _lhs, box _rhs, _) => {
                // Add flag updates for writes
                let curr_fn = self.current_fn();

                if let Some(func) = self.funcs.get(&curr_fn)
                    && !func.index_map.is_empty()
                {
                    let loc = self
                        .get_mir_loc_for_expr(expr.id)
                        .unwrap_or_else(|| panic!("Failed to find MIR location for assign expr"));

                    if func.simpl_assigns.contains(&loc) {
                        let new_expr = expr!("()");
                        self.replace_expr(expr, new_expr);
                    } else {
                        let mut flag_updates = vec![];
                        for (p, locs) in &func.write_locs {
                            let param = &func.index_map[p];
                            if !param.must && locs.contains(&loc) {
                                let update = format!("{}___s = true", param.name);
                                flag_updates.push(update);
                            }
                        }

                        if !flag_updates.is_empty() {
                            let new_expr = expr!(
                                "{{ {}; {} }}",
                                flag_updates.join("; "),
                                pprust::expr_to_string(expr),
                            );
                            self.replace_expr(expr, new_expr);
                        }
                    }
                }
            }
            ExprKind::Ret(opt_expr) => {
                // rewrite return values of functions
                let curr_fn = self.current_fn();

                if let Some(func) = self.funcs.get(&curr_fn)
                    && !func.index_map.is_empty()
                {
                    let orig_ret = opt_expr.as_ref().map(|e| pprust::expr_to_string(e));
                    let hir_expr = self
                        .ast_to_hir
                        .get_expr(expr.id, self.tcx)
                        .unwrap_or_else(|| panic!("Failed to find HIR expr for return expr"));
                    let hir_id = hir_expr.hir_id;

                    let wfr: Option<(FxHashSet<ParamIdx>, FxHashSet<ParamIdx>)> = if func.is_unit
                        || func.wfrs.is_none()
                    {
                        None
                    } else {
                        let wfrs = func.wfrs.as_ref().unwrap();
                        let mut expr_locs = self.get_mir_locs_for_expr(expr.id).unwrap_or_default();

                        // handle where return value has multiple MIR blocks
                        if let Some(opt_expr) = opt_expr.as_ref() {
                            let blocks = self
                                .get_mir_locs_for_expr(opt_expr.id)
                                .unwrap_or_default()
                                .into_iter()
                                .map(|loc| loc.block)
                                .collect::<FxHashSet<_>>();

                            for wfr in wfrs.keys() {
                                if blocks.contains(&wfr.block) && !expr_locs.contains(wfr) {
                                    expr_locs.push(*wfr);
                                }
                            }
                        }

                        Some(expr_locs.iter().fold(
                            (FxHashSet::default(), FxHashSet::default()),
                            |(mays, musts), loc| {
                                if let Some((loc_mays, loc_musts)) = wfrs.get(loc) {
                                    let mays = mays.union(loc_mays).cloned().collect();
                                    let musts = if musts.is_empty() {
                                        loc_musts.clone()
                                    } else {
                                        musts.intersection(loc_musts).cloned().collect()
                                    };
                                    (mays, musts)
                                } else {
                                    (mays, musts)
                                }
                            },
                        ))
                    };

                    if let Some(callee) = self.call_in_ret.get(&expr.span)
                        && let Some(callee) = self.funcs.get(callee)
                        && !callee.index_map.is_empty()
                    {
                        // if return contains a call to function being transformed
                        let ret_val = self.get_return_value(
                            func,
                            wfr.as_ref(),
                            Some("rv___".to_string()),
                            Some(hir_id),
                        );

                        let new_return = expr!(
                            "{{ let rv___ = {}; return {} }}",
                            orig_ret.unwrap(),
                            ret_val
                        );
                        self.replace_expr(expr, new_return);
                    } else {
                        let new_return = expr!(
                            "return {}",
                            self.get_return_value(func, wfr.as_ref(), orig_ret, Some(hir_id))
                        );
                        self.replace_expr(expr, new_return);
                    }
                }
            }
            ExprKind::Call(callee, args) => {
                if let Some(def_id) = self.bounds.get(&callee.span)
                    && let Some(func) = self.funcs.get(def_id)
                    && !func.index_map.is_empty()
                {
                    let loc = self
                        .get_mir_loc_for_expr(expr.id)
                        .unwrap_or_else(|| panic!("Failed to find MIR location for call expr"));

                    let ret_tys = &func.return_tys;
                    // binds return values of a call to rv___, rv___1, ...
                    let mut bindings = vec![];
                    // assign output parameter values to arguments
                    let mut assign_ret = vec![];
                    let mut mtch_assign = None;

                    for (ridx, ret_ty) in ret_tys.iter_enumerated() {
                        match ret_ty {
                            ReturnTyItem::Orig => {
                                assert!(ridx.index() == 0);
                                bindings.push(String::from("rv___"));
                            }
                            ReturnTyItem::Type(param) => {
                                let index = param.index;
                                let arg = args[index.index()].as_ref();
                                let rhs = if ridx.index() == 0 {
                                    String::from("rv___")
                                } else {
                                    format!("rv___{}", ridx.index())
                                };
                                let assign = self.get_assign(arg, true, rhs.clone(), index, loc);
                                assign_ret.push(assign);
                                bindings.push(rhs);
                            }
                            ReturnTyItem::Option(param) => {
                                let index = param.index;
                                let arg = args[index.index()].as_ref();
                                let rhs = if ridx.index() == 0 {
                                    String::from("rv___")
                                } else {
                                    format!("rv___{}", ridx.index())
                                };
                                let assign = self.get_assign(arg, false, rhs.clone(), index, loc);
                                assign_ret.push(assign);
                                bindings.push(rhs);
                            }
                            ReturnTyItem::Result(param) => {
                                assert!(ridx.index() == 0);
                                let index = param.index;
                                let arg = args[index.index()].as_ref();
                                bindings.push(String::from("rv___"));
                                mtch_assign = Some(self.get_assign(
                                    arg,
                                    true,
                                    "v___".to_string(),
                                    index,
                                    loc,
                                ));
                            }
                        }
                    }
                    // remove output parameters from arguments
                    *args = args
                        .iter()
                        .cloned()
                        .enumerate()
                        .filter_map(|(i, arg)| {
                            if func.index_map.contains_key(&ParamIdx::from_usize(i)) {
                                None
                            } else {
                                Some(arg)
                            }
                        })
                        .collect();

                    let binding = if bindings.len() == 1 {
                        format!("let {} = {}", bindings[0], pprust::expr_to_string(expr))
                    } else {
                        format!(
                            "let ({}) = {}",
                            bindings.join(", "),
                            pprust::expr_to_string(expr)
                        )
                    };

                    assign_ret.push(String::from("rv___"));

                    let new_expr = match &ret_tys[RetIdx::from_usize(0)] {
                        ReturnTyItem::Orig | ReturnTyItem::Type(_) | ReturnTyItem::Option(_) => {
                            let assign_ret = assign_ret.join("; ");
                            expr!("{{ {binding}; {assign_ret} }}")
                        }
                        ReturnTyItem::Result(param) => {
                            let mtch_assign = mtch_assign.unwrap();
                            let sv = param.succ_value.unwrap();
                            let v = match sv {
                                SuccValue::Int(v) => v.to_string(),
                                SuccValue::Uint(v) => v.to_string(),
                                SuccValue::Bool(v) => v.to_string(),
                            };
                            let assign_ret = assign_ret.join("; ");
                            expr!(
                                "(match {{ {binding}; {assign_ret} }} {{ Ok(v___) => {{ {mtch_assign}; {v} }} Err(v___) => v___ }})",
                            )
                        }
                    };
                    self.replace_expr(expr, new_expr);
                }
            }
            ExprKind::Unary(UnOp::Deref, _) => {
                if let Some(curr_fn) = self.current_fns.last()
                    && let Some(func) = self.funcs.get(curr_fn)
                    && !func.index_map.is_empty()
                    && let Some(hir_expr) = self.ast_to_hir.get_expr(expr.id, self.tcx)
                    && let Some(param_index) = func.simpl_derefs.get(&hir_expr.hir_id)
                {
                    let param = &func.index_map[param_index];
                    let new_expr = expr!("{}___v", param.name);
                    self.replace_expr(expr, new_expr);
                    self.counter.removed_pointer_uses += 1;
                }
            }
            _ => {}
        }
    }
}

#[derive(Debug, Clone)]
struct Assign {
    hir_id: HirId,
    loc: Location,
    span: Span,
    rhs: String,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
struct Deref {
    hir_id: HirId,
    in_call_or_ret: bool,
}

enum Parent<'tcx> {
    Deref(HirId),
    Ret(&'tcx HirExpr<'tcx>),
    Assign(HirId),
    Call,
}

struct HirVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    /// bound occurrence (ident) span to def_id
    bounds: FxHashMap<Span, LocalDefId>,
    /// spans of returns to function called inside them
    call_in_ret: FxHashMap<Span, LocalDefId>,
    /// HirId of assigns which has a call inside them
    call_in_assigns: FxHashSet<HirId>,
    /// in function, the set of deref hir ids of a local
    deref_uses: FxHashMap<(LocalDefId, Local), FxHashSet<Deref>>,
    /// in function, a local is used without deref
    ref_uses: FxHashSet<(LocalDefId, Local)>,
    /// maps HirId of lhs to assignment info
    assigns: FxHashMap<HirId, Assign>,
    /// span and HirId of return expressions
    returns: FxHashMap<LocalDefId, FxHashSet<(Span, HirId)>>,
    hir_to_thir: &'a HirToThir,
    thir_to_mir: &'a FxHashMap<LocalDefId, ThirToMir>,
}

impl<'a, 'tcx> HirVisitor<'a, 'tcx> {
    fn new(
        tcx: TyCtxt<'tcx>,
        hir_to_thir: &'a HirToThir,
        thir_to_mir: &'a FxHashMap<LocalDefId, ThirToMir>,
    ) -> Self {
        Self {
            tcx,
            bounds: FxHashMap::default(),
            call_in_ret: FxHashMap::default(),
            call_in_assigns: FxHashSet::default(),
            deref_uses: FxHashMap::default(),
            ref_uses: FxHashSet::default(),
            assigns: FxHashMap::default(),
            returns: FxHashMap::default(),
            hir_to_thir,
            thir_to_mir,
        }
    }

    fn add_bound(&mut self, span: Span, def_id: LocalDefId) {
        self.bounds.insert(span, def_id);
    }

    fn get_local_def_id(&self, expr: &HirExpr<'tcx>) -> Option<LocalDefId> {
        if let HirExprKind::Path(QPath::Resolved(_, path)) = expr.kind
            && let Res::Def(_, def_id) = path.res
            && let Some(def_id) = def_id.as_local()
        {
            Some(def_id)
        } else {
            None
        }
    }

    fn get_parent(&self, hir_id: HirId) -> Option<Parent<'tcx>> {
        for (_, parent) in self.tcx.hir_parent_iter(hir_id) {
            let HirNode::Expr(e) = parent else {
                return None;
            };

            match &e.kind {
                HirExprKind::Ret(_) => return Some(Parent::Ret(e)),
                HirExprKind::Unary(UnOp::Deref, _) => return Some(Parent::Deref(e.hir_id)),
                HirExprKind::Assign(_, _, _) => return Some(Parent::Assign(e.hir_id)),
                HirExprKind::Call(callee, _) => {
                    if self.get_local_def_id(callee).is_some() {
                        return Some(Parent::Call);
                    }
                }
                _ => {}
            }
        }
        None
    }

    fn get_mir_local(&self, hir_id: HirId, def_id: LocalDefId) -> Option<Local> {
        let thir_to_mir = self.thir_to_mir.get(&def_id)?;
        thir_to_mir.binding_to_local.get(&hir_id).cloned()
    }

    fn get_mir_loc(&self, hir_id: HirId, def_id: LocalDefId) -> Option<Location> {
        let thir_expr_id = self.hir_to_thir.exprs.get(&hir_id)?;
        let thir_to_mir = self.thir_to_mir.get(&def_id)?;
        let mir_locs = thir_to_mir.expr_to_locs.get(thir_expr_id)?;
        if mir_locs.len() == 1 {
            Some(mir_locs[0])
        } else {
            None
        }
    }
}

impl<'a, 'tcx> intravisit::Visitor<'tcx> for HirVisitor<'a, 'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_item(&mut self, item: &'tcx HirItem<'tcx>) {
        if let HirItemKind::Static(_, ident, _, _) = item.kind {
            self.add_bound(ident.span, item.owner_id.def_id);
        }
        intravisit::walk_item(self, item);
    }

    fn visit_path(&mut self, path: &HirPath<'tcx>, hir_id: HirId) {
        intravisit::walk_path(self, path);
        if let Res::Def(_, def_id) = path.res
            && let Some(def_id) = def_id.as_local()
        {
            self.add_bound(path.span, def_id);
        }

        if let Res::Local(id) = path.res {
            let def_id = id.owner.def_id;
            if let Some(Parent::Deref(parent_id)) = self.get_parent(hir_id) {
                if let Some(local) = self.get_mir_local(id, def_id) {
                    let parent = self.get_parent(parent_id);
                    let deref = Deref {
                        hir_id: parent_id,
                        in_call_or_ret: matches!(parent, Some(Parent::Call) | Some(Parent::Ret(_))),
                    };

                    self.deref_uses
                        .entry((def_id, local))
                        .or_default()
                        .insert(deref);
                }
            } else {
                let local = self.get_mir_local(id, def_id);
                if let Some(local) = local {
                    self.ref_uses.insert((def_id, local));
                }
            }
        }
    }

    fn visit_expr(&mut self, expr: &'tcx HirExpr<'tcx>) {
        match expr.kind {
            HirExprKind::Call(callee, _) => {
                let parent = self.get_parent(expr.hir_id);
                if let Some(def_id) = self.get_local_def_id(callee)
                    && let Some(Parent::Ret(parent)) = parent
                {
                    self.call_in_ret.insert(parent.span, def_id);
                }
                if let Some(Parent::Assign(hir_id)) = parent {
                    self.call_in_assigns.insert(hir_id);
                }
            }
            HirExprKind::Assign(lhs, rhs, _) => {
                let hir_id = expr.hir_id;
                let def_id = hir_id.owner.def_id;

                if let Some(loc) = self.get_mir_loc(hir_id, def_id) {
                    let source_map = self.tcx.sess.source_map();
                    let assign = Assign {
                        hir_id,
                        loc,
                        span: expr.span,
                        rhs: source_map.span_to_snippet(rhs.span).unwrap(),
                    };
                    self.assigns.insert(lhs.hir_id, assign);
                }
            }
            HirExprKind::Ret(_) => {
                let def_id = expr.hir_id.owner.def_id;
                self.returns
                    .entry(def_id)
                    .or_default()
                    .insert((expr.span, expr.hir_id));
            }
            _ => {}
        }
        intravisit::walk_expr(self, expr);
    }
}
