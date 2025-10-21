use std::{
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
    FnRetTy as HirFnRetTy, HirId, ItemKind as HirItemKind, MutTy, PatKind, QPath, Ty as HirTy,
    TyKind as HirTyKind, def::Res, definitions::DefPathData,
};
use rustc_middle::ty::TyCtxt;
use rustc_span::{FileName, RealFileName, def_id::DefId};

use utils::{
    stmt, ty,
    ast::transform_ast,
    ir::{AstToHir, AstToHirMapper}
};
use crate::{outparam_replacer::ai::analysis::*};

#[derive(Debug, Clone)]
struct Param<'tcx> {
    index: usize,
    name: String,
    must: bool,
    hir_id: HirId,
    ty: &'tcx HirTy<'tcx>,
    ty_str: String,
    // span: Span,
    // writes: Vec<Span>,
    // write_args: BTreeMap<Span, usize>,
}

struct Func<'tcx> {
    is_unit: bool,
    input_len: usize,
    index_map: FxHashMap<usize, Param<'tcx>>,
    return_tys: Vec<ReturnTyItem<'tcx>>,
    // hir_id_map: BTreeMap<HirId, Param<'tcx>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum SuccValue {
    Int(i128),
    Uint(u128),
    Bool(bool),
}

impl SuccValue {
    fn from(rvs: &ReturnValues) -> Option<Self> {
        match rvs {
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

    fn find(params: &[OutputParam]) -> Option<(Self, usize)> {
        params.iter().find_map(|param| {
            if !param.must {
                Some((Self::from(&param.return_values)?, param.index))
            } else {
                None
            }
        })
    }
}

enum ReturnTyItem<'tcx> {
    Orig,                // original return type
    Type(Param<'tcx>),   // use type of parameter
    Result(Param<'tcx>), // rewrite parameter with original return to result type
    Option(Param<'tcx>), // rewrite parameter to option type
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

pub fn transform(tcx: TyCtxt<'_>, dir: &Path, lib_name: &str, config: &crate::outparam_replacer::Config) {
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

    for id in tcx.hir_free_items() {
        let item = tcx.hir_item(id);
        let HirItemKind::Fn { sig, body, .. } = item.kind else {
            continue;
        };

        let def_id = id.owner_id.to_def_id();
        let name = tcx.def_path_str(def_id);
        let fn_analysis_result = some_or!(analysis_result.get(&name), continue);
        let hir_body = tcx.hir_body(body);
        // let mir_body = tcx
        //     .mir_drops_elaborated_and_const_checked(def_id.as_local().unwrap())
        //     .borrow();

        let index_map: FxHashMap<_, _> = fn_analysis_result
            .output_params
            .iter()
            .map(|p| {
                let OutputParam { index, must, .. } = p;
                let param = &hir_body.params[*index];
                let PatKind::Binding(_, hir_id, ident, _) = param.pat.kind else { unreachable!() };
                let name = ident.name.to_string();

                let ty = &sig.decl.inputs[*index];
                let ty_str = match ty.kind {
                    HirTyKind::Ptr(MutTy { ty, .. }) => {
                        source_map.span_to_snippet(ty.span).unwrap()
                    }
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
                (
                    *index,
                    Param {
                        index: *index,
                        name,
                        must: *must,
                        hir_id,
                        ty,
                        ty_str,
                    },
                )
            })
            .collect();

        // given the analysis result, decide how to transform the return type
        let out_ty = match sig.decl.output {
            HirFnRetTy::Return(ty) => Some(ty),
            HirFnRetTy::DefaultReturn(_) => None,
        };
        let sig = tcx.fn_sig(def_id).skip_binder().skip_binder();
        let is_unit = sig.output().is_unit();

        let param_to_result = SuccValue::find(&fn_analysis_result.output_params);
        let mut return_tys = vec![];
        let out_param_tys = index_map.values().map(|p| {
            if p.must {
                ReturnTyItem::Type(p.clone())
            } else {
                ReturnTyItem::Option(p.clone())
            }
        });

        if let Some((_, index)) = param_to_result {
            // if there is a may parameter which has a value indicating success,
            // rewrite it to result type
            let param = &index_map[&index];
            return_tys.push(ReturnTyItem::Result(param.clone()));
            return_tys.extend(out_param_tys);
            return_tys.remove(index + 1);
        } else if !is_unit {
            // keep the original return type if not unit
            return_tys.push(ReturnTyItem::Orig);
            return_tys.extend(out_param_tys);
        }

        let func = Func {
            is_unit,
            input_len: sig.inputs().len(),
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
    // analysis_result: &'a AnalysisResult,
    ast_to_hir: &'a AstToHir,
    funcs: &'a FxHashMap<DefId, Func<'tcx>>,
    updated: bool,
}

impl MutVisitor for TransformVisitor<'_, '_> {
    fn visit_crate(&mut self, c: &mut Crate) {
        mut_visit::walk_crate(self, c);
    }

    fn visit_item(&mut self, item: &mut Item) {
        let node_id = item.id;
        if let ItemKind::Fn(box fn_item) = &mut item.kind {
            let hir_item = self
                .ast_to_hir
                .get_item(node_id, self.tcx)
                .unwrap_or_else(|| panic!("Failed to find HIR item to node {node_id:?}"));
            let local_def_id = hir_item.owner_id.def_id;
            let def_id = local_def_id.to_def_id();
            println!("Visiting function item {def_id:?}");

            if let Some(func) = self.funcs.get(&def_id) {
                // remove output parameters from input types
                let out_params: FxHashSet<_> = func.index_map.keys().collect();
                fn_item.sig.decl.inputs = fn_item
                    .sig
                    .decl
                    .inputs
                    .iter()
                    .cloned()
                    .enumerate()
                    .filter_map(|(i, p)| {
                        if out_params.contains(&i) {
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
                println!("updated function");
                self.updated = true;
            }
        }
        mut_visit::walk_item(self, item);
    }
}
