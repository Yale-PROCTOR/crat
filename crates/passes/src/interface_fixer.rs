use std::fmt::Write as _;

use rustc_ast::{mut_visit::MutVisitor as _, ptr::P, *};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir as hir;
use rustc_hir::{
    def::{DefKind, Res},
    def_id::LocalDefId,
    intravisit,
};
use rustc_middle::{hir::nested_filter, ty, ty::TyCtxt};
use rustc_span::{Symbol, sym};
use serde::Deserialize;
use utils::{FALLBACK_SLICE_LEN, ir::AstToHir};

#[derive(Debug, Default, Clone, Deserialize)]
pub struct Config {
    pub c_exposed_fns: FxHashSet<String>,
}

pub fn fix_interfaces(config: &Config, tcx: TyCtxt<'_>) -> String {
    let mut expanded_ast = utils::ast::expanded_ast(tcx);
    let ast_to_hir = utils::ast::make_ast_to_hir(&mut expanded_ast, tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut expanded_ast);

    let mut hir_visitor = HirVisitor {
        tcx,
        config,
        fixes: FxHashMap::default(),
    };
    tcx.hir_visit_all_item_likes_in_crate(&mut hir_visitor);

    let mut visitor = AstVisitor {
        tcx,
        ast_to_hir,
        fixes: hir_visitor.fixes,
    };
    visitor.visit_crate(&mut expanded_ast);

    pprust::crate_to_string_for_macros(&expanded_ast)
}

struct AstVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    ast_to_hir: AstToHir,
    fixes: FxHashMap<LocalDefId, (FxHashMap<usize, ParamFix>, Symbol)>,
}

impl mut_visit::MutVisitor for AstVisitor<'_> {
    fn flat_map_item(&mut self, item: P<Item>) -> smallvec::SmallVec<[P<Item>; 1]> {
        let id = item.id;
        let mut items = mut_visit::walk_flat_map_item(self, item);

        if let Some(def_id) = self.ast_to_hir.global_map.get(&id)
            && let Some((fixes, name)) = self.fixes.get(def_id)
        {
            let mut new_item = items[0].clone();
            let ItemKind::Fn(f) = &mut new_item.kind else { panic!() };
            let mut call = format!("{name}(");
            for (i, param) in f.sig.decl.inputs.iter_mut().enumerate() {
                let PatKind::Ident(_, ident, _) = &param.pat.kind else { panic!() };
                let x = ident.name;
                if let Some(fix) = fixes.get(&i) {
                    let raw_ty = raw_pointer_param_ty(&param.ty, *fix);
                    *param.ty = raw_ty;
                    match fix.kind {
                        ParamFixKind::Slice => {
                            write!(
                                call,
                                "if {x}.is_null() {{ &{}[] }} else {{ std::slice::from_raw_parts{}({x}, {FALLBACK_SLICE_LEN}) }}, ",
                                if fix.mutability.is_mut() { "mut " } else { "" },
                                if fix.mutability.is_mut() { "_mut" } else { "" },
                            )
                            .unwrap();
                        }
                        ParamFixKind::SliceCursor => {
                            if fix.mutability.is_mut() {
                                write!(
                                    call,
                                    "if {x}.is_null() {{ crate::slice_cursor::SliceCursorMut::empty() }} else {{ crate::slice_cursor::SliceCursorMut::new(std::slice::from_raw_parts_mut({x}, {FALLBACK_SLICE_LEN})) }}, ",
                                )
                                .unwrap();
                            } else {
                                write!(
                                    call,
                                    "if {x}.is_null() {{ crate::slice_cursor::SliceCursor::empty() }} else {{ crate::slice_cursor::SliceCursor::new(std::slice::from_raw_parts({x}, {FALLBACK_SLICE_LEN})) }}, ",
                                )
                                .unwrap();
                            }
                        }
                    }
                } else {
                    write!(call, "{x}, ").unwrap();
                }
            }
            call.push(')');
            let body = f.body.as_mut().unwrap();
            body.stmts.clear();
            let stmt = utils::stmt!("{call}");
            body.stmts.push(stmt);
            items.push(new_item);

            let ItemKind::Fn(f) = &mut items[0].kind else { panic!() };
            f.ident.name = *name;
            items[0]
                .attrs
                .retain(|attr| !attr.has_name(sym::export_name));
        }

        items
    }

    fn visit_item(&mut self, item: &mut Item) {
        mut_visit::walk_item(self, item);

        let id = item.id;
        if let ItemKind::Use(tree) = &mut item.kind
            && let Some(seg) = tree.prefix.segments.last_mut()
            && let Some(hir_item) = self.ast_to_hir.get_item(id, self.tcx)
            && let hir::ItemKind::Use(path, _) = &hir_item.kind
            && let Some(Res::Def(DefKind::Fn, def_id)) = path.res.value_ns
            && let Some(def_id) = def_id.as_local()
            && let Some((_, name)) = self.fixes.get(&def_id)
        {
            seg.ident.name = *name;
        }
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        mut_visit::walk_expr(self, expr);

        let id = expr.id;
        if let ExprKind::Path(_, path) = &mut expr.kind
            && let Some(hir_expr) = self.ast_to_hir.get_expr(id, self.tcx)
            && let hir::ExprKind::Path(hir::QPath::Resolved(_, hir_path)) = &hir_expr.kind
            && let Res::Def(DefKind::Fn, def_id) = hir_path.res
            && let Some(def_id) = def_id.as_local()
            && let Some((_, name)) = self.fixes.get(&def_id)
        {
            path.segments.last_mut().unwrap().ident.name = *name;
        }
    }
}

#[derive(Clone, Copy)]
struct ParamFix {
    kind: ParamFixKind,
    mutability: ty::Mutability,
}

#[derive(Clone, Copy)]
enum ParamFixKind {
    Slice,
    SliceCursor,
}

struct HirVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    config: &'a Config,
    fixes: FxHashMap<LocalDefId, (FxHashMap<usize, ParamFix>, Symbol)>,
}

impl<'tcx> intravisit::Visitor<'tcx> for HirVisitor<'_, 'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_item(&mut self, item: &'tcx hir::Item<'tcx>) {
        if let hir::ItemKind::Fn { ident, body, .. } = item.kind
            && let name = ident.name.as_str()
            && (self.config.c_exposed_fns.contains(name)
                || self
                    .tcx
                    .get_attrs(item.owner_id.def_id.to_def_id(), sym::export_name)
                    .any(|attr| {
                        attr.value_str()
                            .is_some_and(|s| self.config.c_exposed_fns.contains(s.as_str()))
                    }))
        {
            let body = self.tcx.hir_body(body);
            let typeck = self.tcx.typeck(item.owner_id.def_id);
            let mut fixes = FxHashMap::default();
            for (i, param) in body.params.iter().enumerate() {
                let ty = typeck.node_type(param.pat.hir_id);

                if let ty::TyKind::Ref(_, inner_ty, m) = ty.kind()
                    && let ty::TyKind::Slice(_) = inner_ty.kind()
                {
                    fixes.insert(
                        i,
                        ParamFix {
                            kind: ParamFixKind::Slice,
                            mutability: *m,
                        },
                    );
                    continue;
                }

                if let ty::TyKind::Adt(adt_def, generic_args) = ty.kind() {
                    let adt_name = adt_def
                        .did()
                        .as_local()
                        .map(|def_id| self.tcx.item_name(def_id.into()));
                    let Some(adt_name) = adt_name else { continue };

                    let (kind, mutability) = if adt_name.as_str() == "SliceCursorMut" {
                        (ParamFixKind::SliceCursor, ty::Mutability::Mut)
                    } else if adt_name.as_str() == "SliceCursor" {
                        (ParamFixKind::SliceCursor, ty::Mutability::Not)
                    } else {
                        continue;
                    };

                    if generic_args.types().next().is_none() {
                        continue;
                    }

                    fixes.insert(i, ParamFix { kind, mutability });
                }
            }
            if !fixes.is_empty() {
                let new_name = format!("{name}_internal__");
                let new_name = Symbol::intern(&new_name);
                self.fixes.insert(item.owner_id.def_id, (fixes, new_name));
            }
        }

        intravisit::walk_item(self, item);
    }
}

fn raw_pointer_param_ty(param_ty: &Ty, fix: ParamFix) -> Ty {
    let Some(inner_ty) = raw_pointer_inner_ty(param_ty, fix.kind) else {
        panic!(
            "failed to derive raw interface parameter type from `{}`",
            pprust::ty_to_string(param_ty)
        );
    };

    let m = if fix.mutability.is_mut() {
        "mut"
    } else {
        "const"
    };
    let mut raw_ty = utils::ty!("*{m} ()");
    let TyKind::Ptr(mut_ty) = &mut raw_ty.kind else { panic!() };
    mut_ty.ty = inner_ty;
    raw_ty
}

fn raw_pointer_inner_ty(param_ty: &Ty, kind: ParamFixKind) -> Option<P<Ty>> {
    match kind {
        ParamFixKind::Slice => slice_element_ty(param_ty),
        ParamFixKind::SliceCursor => slice_cursor_element_ty(param_ty),
    }
}

fn slice_element_ty(param_ty: &Ty) -> Option<P<Ty>> {
    let param_ty = peel_ty_parens(param_ty);
    let TyKind::Ref(_, mut_ty) = &param_ty.kind else { return None };
    let inner_ty = peel_ty_parens(&mut_ty.ty);
    let TyKind::Slice(element_ty) = &inner_ty.kind else { return None };
    Some(element_ty.clone())
}

fn slice_cursor_element_ty(param_ty: &Ty) -> Option<P<Ty>> {
    let param_ty = peel_ty_parens(param_ty);
    let TyKind::Path(_, path) = &param_ty.kind else { return None };
    let args = path.segments.last()?.args.as_ref()?;
    let GenericArgs::AngleBracketed(args) = &**args else { return None };

    let mut seen_cursor_lifetime = false;
    let mut element_ty = None;
    for arg in &args.args {
        let AngleBracketedArg::Arg(arg) = arg else { return None };
        match arg {
            GenericArg::Lifetime(_) if !seen_cursor_lifetime => {
                seen_cursor_lifetime = true;
            }
            GenericArg::Type(ty) if element_ty.is_none() => {
                element_ty = Some(ty.clone());
            }
            _ => return None,
        }
    }
    element_ty
}

fn peel_ty_parens(ty: &Ty) -> &Ty {
    if let TyKind::Paren(ty) = &ty.kind {
        peel_ty_parens(ty)
    } else {
        ty
    }
}

#[cfg(test)]
mod tests {
    use rustc_hash::FxHashSet;

    fn compact_source(s: &str) -> String {
        s.chars().filter(|c| !c.is_whitespace()).collect()
    }

    fn assert_fixed_interface_typechecks(code: &str, fn_name: &str, expected: &[&[&str]]) {
        let config = super::Config {
            c_exposed_fns: FxHashSet::from_iter([fn_name.to_string()]),
        };
        let transformed = utils::compilation::run_compiler_on_str(code, |tcx| {
            super::fix_interfaces(&config, tcx)
        })
        .unwrap();
        let compact_transformed = compact_source(&transformed);

        for alternatives in expected {
            assert!(
                alternatives
                    .iter()
                    .any(|expected| { compact_transformed.contains(&compact_source(expected)) }),
                "expected to find one of {alternatives:?} in transformed interface:\n{transformed}",
            );
        }

        utils::compilation::run_compiler_on_str(&transformed, utils::type_check)
            .expect(&transformed);
    }

    #[test]
    fn wraps_exposed_export_name_function() {
        let code = r#"
#[export_name = "match"]
pub unsafe extern "C" fn match_0(test: &[f64], reference: &[f64], bins: i32) -> i32 {
    (test[0] == reference[0]) as i32 + bins
}
"#;
        let config = super::Config {
            c_exposed_fns: FxHashSet::from_iter(["match".to_string()]),
        };
        let transformed = utils::compilation::run_compiler_on_str(code, |tcx| {
            super::fix_interfaces(&config, tcx)
        })
        .unwrap();
        utils::compilation::run_compiler_on_str(&transformed, utils::type_check)
            .expect(&transformed);

        assert!(transformed.contains("fn match_0_internal__"));
        assert!(transformed.contains("fn match_0(test: *const f64"));
        assert_eq!(transformed.matches("#[export_name = \"match\"]").count(), 1);
    }

    #[test]
    fn preserves_lifetimes_for_mutable_slice_params() {
        assert_fixed_interface_typechecks(
            r#"
#[repr(C)]
pub struct Push<'a> {
    pub marker: *mut &'a i32,
}

#[repr(C)]
pub struct Remote<'a> {
    pub peer: *mut Push<'a>,
}

pub unsafe extern "C" fn mutable_slices_share_lifetime<'a>(
    pushes: &mut [*mut Push<'a>],
    remotes: &mut [Remote<'a>],
) {
    let _ = pushes.len() + remotes.len();
}
"#,
            "mutable_slices_share_lifetime",
            &[
                &[
                    "fn mutable_slices_share_lifetime<'a>(pushes: *mut *mut Push<'a>",
                    "fn mutable_slices_share_lifetime<'a>(pushes: *mut *mut crate::Push<'a>",
                ],
                &[
                    "remotes: *mut Remote<'a>",
                    "remotes: *mut crate::Remote<'a>",
                ],
            ],
        );
    }

    #[test]
    fn preserves_lifetimes_for_immutable_slice_params_with_invariant_elements() {
        assert_fixed_interface_typechecks(
            r#"
#[repr(C)]
pub struct ReadLeft<'a> {
    pub marker: *mut &'a i32,
}

#[repr(C)]
pub struct ReadRight<'a> {
    pub marker: *mut &'a i32,
}

pub unsafe extern "C" fn immutable_slices_share_lifetime<'a>(
    left: &[ReadLeft<'a>],
    right: &[ReadRight<'a>],
) -> usize {
    left.len() + right.len()
}
"#,
            "immutable_slices_share_lifetime",
            &[
                &[
                    "fn immutable_slices_share_lifetime<'a>(left: *const ReadLeft<'a>",
                    "fn immutable_slices_share_lifetime<'a>(left: *const crate::ReadLeft<'a>",
                ],
                &[
                    "right: *const ReadRight<'a>",
                    "right: *const crate::ReadRight<'a>",
                ],
            ],
        );
    }

    #[test]
    fn preserves_lifetimes_across_fixed_slice_and_raw_pointer_params() {
        assert_fixed_interface_typechecks(
            r#"
#[repr(C)]
pub struct Node<'a> {
    pub marker: *mut &'a i32,
}

pub unsafe extern "C" fn mixed_fixed_and_raw_lifetime<'a>(
    nodes: &mut [Node<'a>],
    root: *mut Node<'a>,
    count: usize,
) -> *mut Node<'a> {
    let _ = nodes.len() + count;
    root
}
"#,
            "mixed_fixed_and_raw_lifetime",
            &[&[
                "fn mixed_fixed_and_raw_lifetime<'a>(nodes: *mut Node<'a>, root: *mut Node<'a>",
                "fn mixed_fixed_and_raw_lifetime<'a>(nodes: *mut crate::Node<'a>, root: *mut Node<'a>",
            ]],
        );
    }

    #[test]
    fn preserves_inner_lifetimes_for_slice_cursor_params() {
        assert_fixed_interface_typechecks(
            r#"
pub mod slice_cursor {
    pub struct SliceCursor<'a, T> {
        base: &'a [T],
    }

    pub struct SliceCursorMut<'a, T> {
        base: &'a mut [T],
    }

    impl<'a, T> SliceCursor<'a, T> {
        pub const fn new(base: &'a [T]) -> Self {
            Self { base }
        }

        pub const fn empty() -> Self {
            Self { base: &[] }
        }
    }

    impl<'a, T> SliceCursorMut<'a, T> {
        pub const fn new(base: &'a mut [T]) -> Self {
            Self { base }
        }

        pub const fn empty() -> Self {
            Self { base: &mut [] }
        }
    }
}

#[repr(C)]
pub struct CursorItem<'a> {
    pub marker: *mut &'a i32,
}

pub unsafe extern "C" fn cursor_params_preserve_inner_lifetimes<'a>(
    read: crate::slice_cursor::SliceCursor<'_, CursorItem<'a>>,
    write: crate::slice_cursor::SliceCursorMut<'_, CursorItem<'a>>,
) {
    let _ = read;
    let _ = write;
}
"#,
            "cursor_params_preserve_inner_lifetimes",
            &[&[
                "fn cursor_params_preserve_inner_lifetimes<'a>(read: *const CursorItem<'a>, write: *mut CursorItem<'a>)",
                "fn cursor_params_preserve_inner_lifetimes<'a>(read: *const crate::CursorItem<'a>, write: *mut crate::CursorItem<'a>)",
            ]],
        );
    }

    #[test]
    fn preserves_lifetimes_inside_nested_generic_slice_elements() {
        assert_fixed_interface_typechecks(
            r#"
#[repr(C)]
pub struct Node<'a> {
    pub marker: *mut &'a i32,
}

#[repr(C)]
pub struct Wrapper<T> {
    pub inner: *mut T,
}

pub unsafe extern "C" fn nested_generic_slice_lifetime<'a>(
    wrapped: &mut [Wrapper<Node<'a>>],
    nodes: &mut [Node<'a>],
) {
    let _ = wrapped.len() + nodes.len();
}
"#,
            "nested_generic_slice_lifetime",
            &[
                &[
                    "fn nested_generic_slice_lifetime<'a>(wrapped: *mut Wrapper<Node<'a>>",
                    "fn nested_generic_slice_lifetime<'a>(wrapped: *mut crate::Wrapper<crate::Node<'a>>",
                ],
                &["nodes: *mut Node<'a>", "nodes: *mut crate::Node<'a>"],
            ],
        );
    }

    #[test]
    fn preserves_lifetimes_through_parenthesized_param_types() {
        assert_fixed_interface_typechecks(
            r#"
pub mod slice_cursor {
    pub struct SliceCursor<'a, T> {
        base: &'a [T],
    }

    impl<'a, T> SliceCursor<'a, T> {
        pub const fn new(base: &'a [T]) -> Self {
            Self { base }
        }

        pub const fn empty() -> Self {
            Self { base: &[] }
        }
    }
}

#[repr(C)]
pub struct Node<'a> {
    pub marker: *mut &'a i32,
}

pub unsafe extern "C" fn parenthesized_interface_types<'a>(
    nodes: (&mut ([Node<'a>])),
    cursor: (crate::slice_cursor::SliceCursor<'_, Node<'a>>),
) {
    let _ = nodes.len();
    let _ = cursor;
}
"#,
            "parenthesized_interface_types",
            &[
                &[
                    "fn parenthesized_interface_types<'a>(nodes: *mut Node<'a>",
                    "fn parenthesized_interface_types<'a>(nodes: *mut crate::Node<'a>",
                ],
                &["cursor: *const Node<'a>", "cursor: *const crate::Node<'a>"],
            ],
        );
    }
}
