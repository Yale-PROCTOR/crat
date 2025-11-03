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
use rustc_hash::FxHashMap;
use rustc_hir::{
    Expr as HirExpr, ExprKind as HirExprKind, HirId, Item as HirItem, ItemKind as HirItemKind,
    MutTy, Node as HirNode, PatKind, Path as HirPath, QPath, TyKind as HirTyKind, def::Res,
    definitions::DefPathData, intravisit,
};
use rustc_index::IndexVec;
use rustc_middle::{
    hir::nested_filter,
    mir::{BasicBlock, TerminatorKind},
    ty::TyCtxt,
};
use rustc_span::{FileName, RealFileName, Span, def_id::LocalDefId};
use utils::{
    ast::transform_ast,
    expr,
    ir::{AstToHir, AstToHirMapper},
    stmt, ty,
};

use crate::outparam_replacer::ai::analysis::*;

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
}

impl Param {
    fn to_ret_ty(&self) -> Option<ReturnTyItem> {
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

struct Func {
    is_unit: bool,
    index_map: BTreeMap<ParamIdx, Param>,
    /// target return type after transformation
    return_tys: IndexVec<RetIdx, ReturnTyItem>,
    /// spans where the parameter is fully written. empty for must parameters
    write_spans: FxHashMap<ParamIdx, Vec<Span>>,
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
    Orig,          // original return type
    Type(Param),   // must output parameter
    Result(Param), // rewrite may parameter with original return to result type
    Option(Param), // rewrite may parameter to option type
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
        // TODO: run analysis here?
        panic!("no analysis result");
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

    let source_map = tcx.sess.source_map();
    let mut def_id_ty_map = FxHashMap::default();
    for id in tcx.hir_free_items() {
        let item = tcx.hir_item(id);
        let HirItemKind::TyAlias(_, _, ty) = item.kind else {
            continue;
        };
        let HirTyKind::Ptr(MutTy { ty, .. }) = ty.kind else {
            continue;
        };
        let def_id = item.owner_id.to_def_id();
        let ty = source_map.span_to_snippet(ty.span).unwrap();
        def_id_ty_map.insert(def_id, ty);
    }

    let mut hir_visitor = HirVisitor::new(tcx);
    tcx.hir_visit_all_item_likes_in_crate(&mut hir_visitor);

    let mut funcs = FxHashMap::default();
    let mut write_args: FxHashMap<_, FxHashMap<_, _>> = FxHashMap::default();

    for id in tcx.hir_free_items() {
        let item = tcx.hir_item(id);
        let HirItemKind::Fn { sig, body, .. } = item.kind else {
            continue;
        };

        let def_id = id.owner_id.to_def_id();
        let local_def_id = def_id.as_local().unwrap();
        let name = tcx.def_path_str(def_id);
        let fn_analysis_result = some_or!(analysis_result.get(&name), continue);
        let hir_body = tcx.hir_body(body);
        let mir_body = tcx
            .mir_drops_elaborated_and_const_checked(local_def_id)
            .borrow();

        let mut succ_param = None;
        let mut index_map: BTreeMap<_, _> = BTreeMap::new();
        let mut write_spans: FxHashMap<_, Vec<_>> = FxHashMap::default();

        for p in &fn_analysis_result.output_params {
            let OutputParam {
                index,
                must,
                complete_writes,
                ..
            } = p;
            let param = &hir_body.params[*index];
            let param_index = ParamIdx::from_usize(*index);
            let PatKind::Binding(_, _hir_id, ident, _) = param.pat.kind else { unreachable!() };
            let name = ident.name.to_string();

            let ty = &sig.decl.inputs[*index];
            let ty_str = match ty.kind {
                HirTyKind::Ptr(MutTy { ty, .. }) => source_map.span_to_snippet(ty.span).unwrap(),
                HirTyKind::Path(QPath::Resolved(_, path)) => {
                    let Res::Def(_, def_id) = path.res else {
                        unreachable!("{:?}", ty);
                    };
                    def_id_ty_map
                        .get(&def_id)
                        .unwrap_or_else(|| panic!("{ty:?}"))
                        .clone()
                }
                _ => unreachable!("{:?}", ty),
            };

            complete_writes.iter().for_each(|cw| {
                let CompleteWrite {
                    block,
                    statement_index,
                    write_arg,
                } = cw;
                let bbd = &mir_body.basic_blocks[BasicBlock::from_usize(*block)];
                if *statement_index == bbd.statements.len() {
                    let t = bbd.terminator();
                    assert!(matches!(t.kind, TerminatorKind::Call { .. }), "{t:?}");
                    let span = t.source_info.span;
                    if let Some(arg) = write_arg {
                        write_args
                            .entry(span)
                            .or_default()
                            .insert(ParamIdx::from_usize(*arg), name.clone());
                    }
                } else {
                    let write_span = bbd.statements[*statement_index].source_info.span;
                    write_spans.entry(param_index).or_default().push(write_span);
                }
            });

            let succ_value = if succ_param.is_none() {
                // find the first may parameter which has a value indicating success
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
                },
            );
        }

        // given the analysis result, decide how to transform the return type
        let sig = tcx.fn_sig(def_id).skip_binder().skip_binder();
        let is_unit = sig.output().is_unit();

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

        return_tys.extend(index_map.values().filter_map(|p| p.to_ret_ty()));

        let func = Func {
            is_unit,
            index_map,
            return_tys,
            write_spans,
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
                funcs: &funcs,
                current_fns: vec![],
                write_args: &write_args,
                bounds: &hir_visitor.bounds,
                call_in_ret: &hir_visitor.call_in_ret,
                updated: false,
            };
            visitor.visit_crate(krate);
            visitor.updated
        },
        tcx,
    );
    res.apply();
}

struct TransformVisitor<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    ast_to_hir: AstToHir,
    funcs: &'a FxHashMap<LocalDefId, Func>,
    current_fns: Vec<LocalDefId>,
    /// at span, caller param named string is used 'ParamIdx'th argument of call
    write_args: &'a FxHashMap<Span, FxHashMap<ParamIdx, String>>,
    /// bound occurrence (ident) span to def_id
    bounds: &'a FxHashMap<Span, LocalDefId>,
    // maps spans of returns to calls inside them
    call_in_ret: &'a FxHashMap<Span, LocalDefId>,
    /// is this file updated
    updated: bool,
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
        span: Span,
    ) -> String {
        let arg = pprust::expr_to_string(expr);
        let write_args = self.write_args.get(&span);
        let set_flag = if let Some(arg_to_param) = write_args
            && let Some(caller_param) = arg_to_param.get(&index)
        {
            format!(" {caller_param}___s = true")
        } else {
            String::new()
        };

        // TODO: enable more robust detection
        if arg.contains("&mut ") {
            if must {
                format!("*({arg}) = {rhs};{set_flag}")
            } else {
                format!("if let Some(v___) = {rhs} {{ *({arg}) = v___;{set_flag} }}")
            }
        } else if must {
            format!("if !({arg}.is_null()) {{ *({arg}) = {rhs};{set_flag} }}")
        } else {
            format!(
                "if !(({arg}).is_null()) {{ if let Some(v___) = {rhs} {{ *({arg}) = v___;{set_flag} }} }}"
            )
        }
    }

    fn get_return_value(&self, func: &Func, orig_ret: Option<String>) -> String {
        let mut ret_vals = vec![];
        for ret_ty in &func.return_tys {
            let ret_val = match ret_ty {
                ReturnTyItem::Orig => orig_ret.as_ref().unwrap().clone(),
                ReturnTyItem::Type(param) => format!("{}___v", param.name),
                ReturnTyItem::Result(param) => format!(
                    "if {}___s {{ Ok({}___v) }} else {{ Err({}) }}",
                    param.name,
                    param.name,
                    orig_ret.as_ref().unwrap()
                ),
                ReturnTyItem::Option(param) => format!(
                    "if {}___s {{ Some({}___v) }} else {{ None }}",
                    param.name, param.name
                ),
            };
            ret_vals.push(ret_val);
        }
        if ret_vals.len() == 1 {
            ret_vals.pop().unwrap()
        } else {
            format!("({})", ret_vals.join(", "))
        }
    }
}

impl MutVisitor for TransformVisitor<'_, '_> {
    fn visit_crate(&mut self, c: &mut Crate) {
        mut_visit::walk_crate(self, c);
    }

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
        println!("Visiting function item {local_def_id:?}");
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

                // TODO: simplify unnecessary declarations
                let stmts = &mut fn_item.body.as_mut().unwrap().stmts;
                stmts.insert(0, ref_decl);
                stmts.insert(0, value_decl);
                if !param.must {
                    stmts.insert(0, flag_decl);
                }
            }

            // for unit function without return statement, add a return
            if func.is_unit {
                let stmts = &mut fn_item.body.as_mut().unwrap().stmts;
                let ret = self.get_return_value(func, None);
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
                let expr_span = expr.span;
                let curr_fn = self.current_fn();

                if let Some(func) = self.funcs.get(&curr_fn)
                    && !func.index_map.is_empty()
                {
                    let mut flag_updates = vec![];
                    for (p, spans) in &func.write_spans {
                        let param = &func.index_map[p];
                        if !param.must && spans.contains(&expr_span) {
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
            ExprKind::Ret(opt_expr) => {
                // rewrite return values of functions
                let curr_fn = self.current_fn();

                if let Some(func) = self.funcs.get(&curr_fn)
                    && !func.index_map.is_empty()
                {
                    let orig_ret = opt_expr.as_ref().map(|e| pprust::expr_to_string(e));

                    if let Some(callee) = self.call_in_ret.get(&expr.span)
                        && let Some(callee) = self.funcs.get(callee)
                        && !callee.index_map.is_empty()
                    {
                        // if return contains a call to function being transformed
                        let ret_val = self.get_return_value(func, Some("rv___".to_string()));
                        let new_return = expr!(
                            "{{ let rv___ = {}; return {} }}",
                            orig_ret.unwrap(),
                            ret_val
                        );
                        self.replace_expr(expr, new_return);
                    } else {
                        let new_return = expr!("return {}", self.get_return_value(func, orig_ret));
                        self.replace_expr(expr, new_return);
                    }
                }
            }
            ExprKind::Call(callee, args) => {
                if let Some(def_id) = self.bounds.get(&callee.span)
                    && let Some(func) = self.funcs.get(def_id)
                    && !func.index_map.is_empty()
                {
                    println!("Transforming call to function {def_id:?}");
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
                                let assign =
                                    self.get_assign(arg, true, rhs.clone(), index, expr.span);
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
                                let assign =
                                    self.get_assign(arg, false, rhs.clone(), index, expr.span);
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
                                    expr.span,
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
                            expr!("{{ {binding}; {assign_ret}}}")
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
                                "(match ({{ {binding}; {assign_ret} }}) {{ Ok(v___) => {{ {mtch_assign} {v} }} Err(v___) => v___ }})",
                            )
                        }
                    };
                    self.replace_expr(expr, new_expr);
                }
            }
            _ => {}
        }
    }
}

struct HirVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    bounds: FxHashMap<Span, LocalDefId>,
    call_in_ret: FxHashMap<Span, LocalDefId>,
}

impl<'tcx> HirVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            bounds: FxHashMap::default(),
            call_in_ret: FxHashMap::default(),
        }
    }

    fn add_bound(&mut self, span: Span, def_id: LocalDefId) {
        self.bounds.insert(span, def_id);
    }

    fn get_parent(&self, hir_id: HirId) -> Option<&HirExpr<'_>> {
        let HirNode::Expr(e) = self.tcx.parent_hir_node(hir_id) else {
            return None;
        };
        match e.kind {
            HirExprKind::DropTemps(_) | HirExprKind::Cast(_, _) => self.get_parent(e.hir_id),
            _ => Some(e),
        }
    }

    fn get_parent_return(&self, hir_id: HirId) -> Option<&HirExpr<'_>> {
        let parent = self.get_parent(hir_id)?;
        if let HirExprKind::Ret(_) = parent.kind {
            Some(parent)
        } else {
            self.get_parent_return(parent.hir_id)
        }
    }
}

impl<'tcx> intravisit::Visitor<'tcx> for HirVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_item(&mut self, item: &'tcx HirItem<'tcx>) {
        intravisit::walk_item(self, item);

        if let HirItemKind::Static(_, ident, _, _body_id) = item.kind {
            self.add_bound(ident.span, item.owner_id.def_id);
        }
    }

    fn visit_path(&mut self, path: &HirPath<'tcx>, _: HirId) {
        intravisit::walk_path(self, path);
        if let Res::Def(_, def_id) = path.res
            && let Some(def_id) = def_id.as_local()
        {
            self.add_bound(path.span, def_id);
        }
    }

    fn visit_expr(&mut self, expr: &'tcx HirExpr<'tcx>) {
        if let HirExprKind::Call(callee, _) = expr.kind
            && let HirExprKind::Path(QPath::Resolved(_, path)) = callee.kind
            && let Res::Def(_, def_id) = path.res
            && let Some(def_id) = def_id.as_local()
            && let Some(parent) = self.get_parent_return(expr.hir_id)
        {
            self.call_in_ret.insert(parent.span, def_id);
        }
        intravisit::walk_expr(self, expr);
    }
}
