use etrace::some_or;
use rustc_hash::FxHashMap;
use rustc_hir::{
    HirId, ItemKind, Pat, PatKind, Path,
    def::Res,
    def_id::LocalDefId,
    intravisit::{self, Visitor as HVisitor},
};
use rustc_middle::{
    hir::nested_filter,
    mir::{BinOp, Const, LocalDecls, Location, Rvalue, TerminatorKind, visit::Visitor as MVisitor},
    ty::{TyCtxt, TyKind},
};
use rustc_span::Symbol;

pub fn run(tcx: TyCtxt<'_>) {
    for (arity, funcs) in collect_functions(tcx) {
        println!("{arity}-parameter functions:");
        for func in funcs {
            let name = tcx.def_path_str(func);
            println!("  {name}");
        }
    }
    println!();

    let bindings = collect_local_bindings(tcx);
    for (hir_id, name) in &bindings.int_bindings {
        let owner = tcx.def_path_str(hir_id.owner);
        let count = bindings.bound_occurrences.get(hir_id).copied().unwrap_or(0);
        println!("Integral binding {name} in {owner}, bound {count} times");
    }
    println!();

    for (def_id, count) in collect_calls(tcx) {
        let name = tcx.def_path_str(def_id);
        println!("Function {name} is called {count} times");
    }
    println!();

    for (def_id, count) in collect_int_adds(tcx) {
        let name = tcx.def_path_str(def_id);
        println!("Function {name} has {count} integral additions");
    }
}

fn collect_functions(tcx: TyCtxt<'_>) -> FxHashMap<usize, Vec<LocalDefId>> {
    let mut functions: FxHashMap<_, Vec<_>> = FxHashMap::default();
    for item_id in tcx.hir_free_items() {
        let item = tcx.hir_item(item_id);
        if let ItemKind::Fn { body, .. } = item.kind {
            let body = tcx.hir_body(body);
            let arity = body.params.len();
            let def_id = item_id.owner_id.def_id;
            functions.entry(arity).or_default().push(def_id);
        }
    }
    functions
}

fn collect_local_bindings(tcx: TyCtxt<'_>) -> Bindings {
    let mut visitor = BindingCollector::new(tcx);
    tcx.hir_visit_all_item_likes_in_crate(&mut visitor);
    visitor.ctx
}

#[derive(Default)]
struct Bindings {
    int_bindings: FxHashMap<HirId, Symbol>,
    bound_occurrences: FxHashMap<HirId, usize>,
}

struct BindingCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    ctx: Bindings,
}

impl<'tcx> BindingCollector<'tcx> {
    #[inline]
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        BindingCollector {
            tcx,
            ctx: Bindings::default(),
        }
    }
}

impl<'tcx> HVisitor<'tcx> for BindingCollector<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_pat(&mut self, pat: &'tcx Pat<'tcx>) {
        if let PatKind::Binding(_, hir_id, ident, _) = pat.kind {
            let typeck = self.tcx.typeck(pat.hir_id.owner);
            let ty = typeck.node_type(hir_id);
            if ty.is_integral() {
                self.ctx.int_bindings.insert(hir_id, ident.name);
            }
        }
        intravisit::walk_pat(self, pat);
    }

    fn visit_path(&mut self, path: &Path<'tcx>, _id: HirId) {
        if let Res::Local(hir_id) = path.res
            && self.ctx.int_bindings.contains_key(&hir_id)
        {
            *self.ctx.bound_occurrences.entry(hir_id).or_default() += 1;
        }
        intravisit::walk_path(self, path);
    }
}

fn collect_calls(tcx: TyCtxt<'_>) -> FxHashMap<LocalDefId, usize> {
    let mut calls: FxHashMap<_, usize> = FxHashMap::default();
    for def_id in tcx.hir_body_owners() {
        let dk = tcx.def_kind(def_id);
        let body = if dk.is_fn_like() {
            tcx.optimized_mir(def_id)
        } else {
            tcx.mir_for_ctfe(def_id)
        };
        for bbd in body.basic_blocks.iter() {
            let terminator = bbd.terminator();
            let TerminatorKind::Call { func, .. } = &terminator.kind else { continue };
            let constant = some_or!(func.constant(), continue);
            let Const::Val(_, ty) = constant.const_ else { unreachable!() };
            let TyKind::FnDef(def_id, _) = ty.kind() else { unreachable!() };
            let def_id = some_or!(def_id.as_local(), continue);
            *calls.entry(def_id).or_default() += 1;
        }
    }
    calls
}

fn collect_int_adds(tcx: TyCtxt<'_>) -> FxHashMap<LocalDefId, usize> {
    let mut adds: FxHashMap<_, usize> = FxHashMap::default();
    for def_id in tcx.hir_body_owners() {
        let dk = tcx.def_kind(def_id);
        let body = if dk.is_fn_like() {
            tcx.optimized_mir(def_id)
        } else {
            tcx.mir_for_ctfe(def_id)
        };
        let mut visitor = AddCollector {
            tcx,
            local_decls: &body.local_decls,
            count: 0,
        };
        visitor.visit_body(body);
        adds.insert(def_id, visitor.count);
    }
    adds
}

struct AddCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    local_decls: &'tcx LocalDecls<'tcx>,
    count: usize,
}

impl<'tcx> MVisitor<'tcx> for AddCollector<'tcx> {
    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        if let Rvalue::BinaryOp(BinOp::Add, box (l, _)) = rvalue {
            let ty = l.ty(self.local_decls, self.tcx);
            if ty.is_integral() {
                self.count += 1;
            }
        }
        self.super_rvalue(rvalue, location);
    }
}

#[cfg(test)]
mod tests {
    use utils::compilation;

    use super::*;
    use crate::ir_utils;

    #[test]
    fn test_collect_functions() {
        compilation::run_compiler_on_str(
            r#"
fn f() -> i32 { 0 }
fn g(x: i32) -> i32 { x }
fn h(x: i32) -> i32 { x + x }
"#,
            |tcx| {
                let functions = collect_functions(tcx);
                assert_eq!(functions.len(), 2);

                let nullary = functions.get(&0).unwrap();
                assert_eq!(nullary.len(), 1);
                assert_eq!(
                    ir_utils::def_id_to_symbol(nullary[0], tcx)
                        .unwrap()
                        .as_str(),
                    "f"
                );

                let unary = functions.get(&1).unwrap();
                assert_eq!(unary.len(), 2);
                assert_eq!(
                    ir_utils::def_id_to_symbol(unary[0], tcx).unwrap().as_str(),
                    "g"
                );
                assert_eq!(
                    ir_utils::def_id_to_symbol(unary[1], tcx).unwrap().as_str(),
                    "h"
                );
            },
        )
        .unwrap();
    }

    #[test]
    fn test_collect_local_bindings() {
        compilation::run_compiler_on_str(
            r#"
fn f(x: i32, b: bool) -> i32 {
    let y = if b {
        x
    } else {
        x + x
    };
    let z = if y > 0 {
        (y as f64).exp()
    } else {
        0.0
    };
    z as i32
}
"#,
            |tcx| {
                let bindings = collect_local_bindings(tcx);
                assert_eq!(bindings.int_bindings.len(), 2);

                let x = bindings
                    .int_bindings
                    .iter()
                    .find_map(|(hir_id, name)| {
                        if name.as_str() == "x" {
                            Some(*hir_id)
                        } else {
                            None
                        }
                    })
                    .unwrap();
                assert_eq!(*bindings.bound_occurrences.get(&x).unwrap(), 3);

                let y = bindings
                    .int_bindings
                    .iter()
                    .find_map(|(hir_id, name)| {
                        if name.as_str() == "y" {
                            Some(*hir_id)
                        } else {
                            None
                        }
                    })
                    .unwrap();
                assert_eq!(*bindings.bound_occurrences.get(&y).unwrap(), 2);
            },
        )
        .unwrap();
    }

    #[test]
    fn test_collect_calls() {
        compilation::run_compiler_on_str(
            r#"
fn f() {}
fn g() { f(); }
fn h() { g(); g(); }
"#,
            |tcx| {
                let calls = collect_calls(tcx);
                assert_eq!(calls.len(), 2);

                let f = calls
                    .iter()
                    .find_map(|(def_id, count)| {
                        if ir_utils::def_id_to_symbol(*def_id, tcx).unwrap().as_str() == "f" {
                            Some(*count)
                        } else {
                            None
                        }
                    })
                    .unwrap();
                assert_eq!(f, 1);

                let g = calls
                    .iter()
                    .find_map(|(def_id, count)| {
                        if ir_utils::def_id_to_symbol(*def_id, tcx).unwrap().as_str() == "g" {
                            Some(*count)
                        } else {
                            None
                        }
                    })
                    .unwrap();
                assert_eq!(g, 2);
            },
        )
        .unwrap();
    }

    #[test]
    fn test_collect_int_adds() {
        compilation::run_compiler_on_str(
            r#"
fn f(x: i32, y: i32, z: i32) -> i32 {
    x + y + z
}
fn g(x: i32, y: i32, f: f32) -> f32 {
    (x + y) as f32 + f
}
"#,
            |tcx| {
                let adds = collect_int_adds(tcx);
                assert_eq!(adds.len(), 2);

                let f = adds
                    .iter()
                    .find_map(|(def_id, count)| {
                        if ir_utils::def_id_to_symbol(*def_id, tcx).unwrap().as_str() == "f" {
                            Some(*count)
                        } else {
                            None
                        }
                    })
                    .unwrap();
                assert_eq!(f, 2);

                let g = adds
                    .iter()
                    .find_map(|(def_id, count)| {
                        if ir_utils::def_id_to_symbol(*def_id, tcx).unwrap().as_str() == "g" {
                            Some(*count)
                        } else {
                            None
                        }
                    })
                    .unwrap();
                assert_eq!(g, 1);
            },
        )
        .unwrap();
    }
}
