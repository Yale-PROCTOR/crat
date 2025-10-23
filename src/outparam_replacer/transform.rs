use std::{
    collections::BTreeMap,
    fs::File,
    path::{Path, PathBuf},
};

use etrace::some_or;
use regex::Regex;
use rustc_ast::{
    HasNodeId,
    ast::*,
    mut_visit::{self, MutVisitor},
    ptr::P,
};
use rustc_ast_pretty::pprust;
use rustc_hash::FxHashMap;
use rustc_hir::{
    intravisit, Expr as HirExpr, ExprKind as HirExprKind, ItemKind as HirItemKind, MutTy, PatKind, QPath,
    TyKind as HirTyKind, def::Res, definitions::DefPathData, Item as HirItem,
};
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{BasicBlock, TerminatorKind},
    ty::{Ty as MirTy, TyCtxt},
};
use rustc_span::{
    FileName, RealFileName, Span,
    def_id::{DefId, LocalDefId},
};
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
    _is_unit: bool,
    _input_len: usize,
    index_map: BTreeMap<ParamIdx, Param>,
    /// target return type after transformation
    return_tys: IndexVec<RetIdx, ReturnTyItem>,
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

enum ReturnTyItem {
    Orig,          // original return type
    Type(Param),   // must output parameter
    Result(Param), // rewrite may parameter with original return to result type
    Option(Param), // rewrite may parameter to option type
}

#[derive(Default, Clone, Copy)]
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

    let mut funcs = FxHashMap::default();
    let mut write_args: FxHashMap<_, FxHashMap<_, _>> = FxHashMap::default();

    for id in tcx.hir_free_items() {
        let item = tcx.hir_item(id);
        let HirItemKind::Fn { sig, body, .. } = item.kind else {
            continue;
        };

        let def_id = id.owner_id.to_def_id();
        let name = tcx.def_path_str(def_id);
        let fn_analysis_result = some_or!(analysis_result.get(&name), continue);
        let hir_body = tcx.hir_body(body);
        let mir_body = tcx
            .mir_drops_elaborated_and_const_checked(def_id.as_local().unwrap())
            .borrow();

        let mut succ_param = None;
        let mut index_map: BTreeMap<_, _> = BTreeMap::new();

        for p in &fn_analysis_result.output_params {
            let OutputParam {
                index,
                must,
                complete_writes,
                ..
            } = p;
            let param = &hir_body.params[*index];
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
                    assert!(matches!(t.kind, TerminatorKind::Call { .. }), "{:?}", t);
                    let span = t.source_info.span;
                    if let Some(arg) = write_arg {
                        write_args
                            .entry(span)
                            .or_default()
                            .insert(ParamIdx::from_usize(*arg), name.clone());
                    }
                }
            });

            let param_index = ParamIdx::from_usize(*index);
            let succ_value = if succ_param.is_none() {
                // find the first may parameter which has a value indicating success
                SuccValue::from(&p)
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

        let mut return_tys = IndexVec::new();

        if let Some(index) = succ_param {
            // if there is a may parameter which has a value indicating success,
            // rewrite it to result type
            let param = index_map[&index].clone();
            return_tys.push(ReturnTyItem::Result(param));
            return_tys.extend(index_map.values().filter_map(|p| p.to_ret_ty()));
        } else if !is_unit {
            // keep the original return type if not unit
            return_tys.push(ReturnTyItem::Orig);
            return_tys.extend(index_map.values().filter_map(|p| p.to_ret_ty()));
        }

        let func = Func {
            _is_unit: is_unit,
            _input_len: sig.inputs().len(),
            index_map,
            return_tys,
        };
        funcs.insert(def_id, func);
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
                println!("Skipping library file {:?}", p);
                return false;
            }

            println!("Transforming AST at {:?}", p);

            let mod_id = path_to_mod_id[&p];
            let (module, _, _) = tcx.hir_get_module(mod_id);
            let mut mapper = AstToHirMapper::new(tcx);
            mapper.map_crate_to_mod(krate, module, false);

            let mut visitor = TransformVisitor {
                tcx,
                ast_to_hir: &mapper.ast_to_hir,
                funcs: &funcs,
                current_fns: vec![],
                write_args: &write_args,
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
    ast_to_hir: &'a AstToHir,
    funcs: &'a FxHashMap<DefId, Func>,
    current_fns: Vec<LocalDefId>,
    /// param is used as 'usize'th call argument at span
    write_args: &'a FxHashMap<Span, FxHashMap<ParamIdx, String>>,
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

    fn expr_to_path<'a, 'tcx>(&self, expr: &'a HirExpr<'tcx>) -> Option<&'a rustc_hir::Path<'tcx>> {
        if let HirExprKind::Path(QPath::Resolved(_, path)) = expr.kind {
            Some(path)
        } else {
            None
        }
    }

    fn expr_ty(&self, expr: &Expr) -> Ty {
        let node_id = expr.node_id();
        let hir_expr = self
            .ast_to_hir
            .get_expr(node_id, self.tcx)
            .cloned()
            .unwrap_or_else(|| panic!("Failed to find HIR expr to node {:?}", node_id));
        let typeck = self.tcx.typeck(hir_expr.hir_id.owner);
        let mir_ty = typeck.expr_ty(&hir_expr);

        mir_ty_to_ty(&mir_ty)
    }

    fn get_set_flag(&self, i: ParamIdx, write_args: &FxHashMap<ParamIdx, String>) -> String {
        if let Some(name) = write_args.get(&i) {
            format!("{}___s = true", name)
        } else {
            String::new()
        }
    }

    fn get_assign(
        &self,
        expr: &Expr,
        must: bool,
        rhs: String,
        aidx: ParamIdx,
        write_args: &FxHashMap<ParamIdx, String>,
    ) -> String {
        let ty = self.expr_ty(expr);
        let arg = pprust::expr_to_string(expr);
        let set_flag = self.get_set_flag(aidx, write_args);
        match &ty.kind {
            TyKind::Ptr(_) => {
                if must {
                    format!("if !{arg}.is_null() {{ *({arg}) = {rhs}; {set_flag} }}")
                } else {
                    format!(
                        "if !({arg}).is_null() {{ if let Some(v___) = {rhs} {{ *({arg}) = v___; {set_flag} }} }}"
                    )
                }
            }
            TyKind::Ref(_, _) => {
                if must {
                    format!("*({arg}) = {rhs}; {set_flag}")
                } else {
                    format!("if let Some(v___) = {rhs} {{ *({arg}) = v___; {set_flag} }}")
                }
            }
            _ => panic!("expected pointer or reference type, found {:?}", ty),
        }
    }
}

impl MutVisitor for TransformVisitor<'_, '_> {
    fn visit_crate(&mut self, c: &mut Crate) {
        mut_visit::walk_crate(self, c);
    }

    fn visit_item(&mut self, item: &mut Item) {
        let node_id = item.id;
        let ItemKind::Fn(box fn_item) = &mut item.kind else {
            mut_visit::walk_item(self, item);
            return;
        };
        let hir_item = self
            .ast_to_hir
            .get_item(node_id, self.tcx)
            .unwrap_or_else(|| panic!("Failed to find HIR item to node {node_id:?}"));
        let local_def_id = hir_item.owner_id.def_id;
        let def_id = local_def_id.to_def_id();

        println!("Visiting function item {def_id:?}");
        self.current_fns.push(local_def_id);

        if let Some(func) = self.funcs.get(&def_id) {
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
                stmts.insert(0, flag_decl);
            }
            self.updated = true;
        }
        mut_visit::walk_item(self, item);
        self.current_fns.pop();
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        let node_id = expr.node_id();
        mut_visit::walk_expr(self, expr);
        match &mut expr.kind {
            ExprKind::Ret(opt_expr) => {
                // Rewrite return values of functions
                let curr_fn = self.current_fn();
                let def_id = curr_fn.to_def_id();

                let mut ret_vals = vec![];
                if let Some(func) = self.funcs.get(&def_id) {
                    for ret_ty in &func.return_tys {
                        let ret_val = match ret_ty {
                            ReturnTyItem::Orig => {
                                pprust::expr_to_string(opt_expr.as_ref().unwrap())
                            }
                            ReturnTyItem::Type(param) => format!("{}___v", param.name),
                            ReturnTyItem::Result(param) => format!(
                                "if {}___s {{ Ok({}___v) }} else {{ Err({}) }}",
                                param.name,
                                param.name,
                                pprust::expr_to_string(opt_expr.as_ref().unwrap())
                            ),
                            ReturnTyItem::Option(param) => format!(
                                "if {}___s {{ Some({}___v) }} else {{ None }}",
                                param.name, param.name
                            ),
                        };
                        ret_vals.push(ret_val);
                    }
                    let new_return = if ret_vals.len() == 1 {
                        expr!("return {}", ret_vals[0])
                    } else {
                        expr!("return ({})", ret_vals.join(", "))
                    };
                    self.replace_expr(expr, new_return);
                }
            }
            ExprKind::Call(callee, args) => {
                let hir_expr = self
                    .ast_to_hir
                    .get_expr(node_id, self.tcx)
                    .unwrap_or_else(|| panic!("Failed to find HIR expr to expr"));

                let HirExprKind::Call(hir_callee, _) = hir_expr.kind else {
                    return;
                };

                let path = some_or!(self.expr_to_path(hir_callee), return);
                let Res::Def(_, def_id) = path.res else {
                    return;
                };
                if !def_id.is_local() {
                    return;
                }

                if let Some(func) = self.funcs.get(&def_id) {
                    let ret_tys = &func.return_tys;
                    // bind return values
                    // e.g. let (rv___, rv___1) = call(...)
                    let mut bindings = vec![];
                    // assign output parameter values to arguments
                    let mut assigns = vec![];

                    let write_args = self
                        .write_args
                        .get(&expr.span)
                        .cloned() // TODO: avoid clone
                        .unwrap_or(FxHashMap::default());
                    let mut mtch_assign = None;

                    for (ridx, ret_ty) in ret_tys.iter_enumerated() {
                        match ret_ty {
                            ReturnTyItem::Orig => {
                                bindings.push(String::from("rv___"));
                            }
                            ReturnTyItem::Type(param) => {
                                let aidx = param.index;
                                let arg = args[aidx.index()].as_ref();
                                let rhs = format!("rv___{}", ridx.index());
                                let assign =
                                    self.get_assign(arg, true, rhs.clone(), aidx, &write_args);
                                assigns.push(assign);
                                bindings.push(rhs);
                            }
                            ReturnTyItem::Option(param) => {
                                let aidx = param.index;
                                let arg = args[aidx.index()].as_ref();
                                let rhs = format!("rv___{}", ridx.index());
                                let assign =
                                    self.get_assign(arg, false, rhs.clone(), aidx, &write_args);
                                assigns.push(assign);
                                bindings.push(rhs);
                            }
                            ReturnTyItem::Result(param) => {
                                let aidx = param.index;
                                let arg = args[aidx.index()].as_ref();
                                mtch_assign = Some(self.get_assign(
                                    arg,
                                    true,
                                    "v___".to_string(),
                                    aidx,
                                    &write_args,
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
                    let assign = assigns.join("; ");

                    let new_expr = match &ret_tys[RetIdx::from_usize(0)] {
                        ReturnTyItem::Orig => {
                            expr!("{{ {binding}; {assign}; rv___ }}")
                        }
                        ReturnTyItem::Result(param) => {
                            let mtch_assign = mtch_assign.unwrap();
                            let sv = param.succ_value.unwrap();
                            let v = match sv {
                                SuccValue::Int(v) => v.to_string(),
                                SuccValue::Uint(v) => v.to_string(),
                                SuccValue::Bool(v) => v.to_string(),
                            };
                            expr!(
                                "(match ({{ {binding}; {assign}; rv___ }}) {{ Ok(v___) => {{ {mtch_assign}; {v} }} Err(v___) => v___ }})"
                            )
                        }
                        _ => unreachable!(),
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
}

impl<'tcx> HirVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            bounds: FxHashMap::default(),
        }
    }

    fn add_bound(&mut self, span: Span, def_id: LocalDefId) {
        self.bounds.insert(span, def_id);
    }
}

impl<'tcx> intravisit::Visitor <'tcx> for HirVisitor<'tcx> {
    fn visit_item(&mut self, item: &'tcx HirItem<'tcx>) {
        intravisit::walk_item(self, item);

        match item.kind {
            HirItemKind::Static(_, ident, _, body_id) => {
                self.add_bound(ident.span, item.owner_id.def_id);
            }
            _ => {}
        }
    }

    fn visit_path()
}

fn mir_ty_to_ty(mir_ty: &MirTy) -> Ty {
    let mut ty_str = mir_ty.to_string();
    let re = Regex::new(r"(?P<prefix>(^|<|\s|,\s))([A-Za-z_][A-Za-z0-9_]*)::").unwrap();
    ty_str = re
        .replace_all(&ty_str, "${prefix}crate::${3}::")
        .to_string();
    ty!("{}", ty_str)
}
