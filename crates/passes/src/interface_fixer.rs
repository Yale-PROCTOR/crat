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
use utils::{
    field_spec::{FieldSpecAttr, FieldSpecEntry, FieldSpecParam},
    ir::AstToHir,
};

#[derive(Debug, Default, Clone, Deserialize)]
pub struct Config {
    pub c_exposed_fns: FxHashSet<String>,
    // struct-param field specialization records produced by the pointer pass;
    // consumed by the interface pass to synthesize c-facing wrappers (task 3)
    #[serde(default)]
    pub field_spec: utils::field_spec::FieldSpecMap,
}

pub fn fix_interfaces(config: &Config, tcx: TyCtxt<'_>) -> String {
    let mut expanded_ast = utils::ast::expanded_ast(tcx);
    let ast_to_hir = utils::ast::make_ast_to_hir(&mut expanded_ast, tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut expanded_ast);

    // struct name/field -> declared field type, resolved once up front so
    // field-spec param shapes can be checked against the real (typeck'd)
    // field type regardless of visitor order
    let mut struct_visitor = StructFieldVisitor {
        tcx,
        fields: FxHashMap::default(),
    };
    tcx.hir_visit_all_item_likes_in_crate(&mut struct_visitor);

    let mut hir_visitor = HirVisitor {
        tcx,
        config,
        struct_fields: &struct_visitor.fields,
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

// one resolved wrapper-generation target: the per-param fixes to apply plus
// what to do with the fn's identity (see `FixAction`)
struct FixEntry<'tcx> {
    param_fixes: FxHashMap<usize, ParamFix<'tcx>>,
    action: FixAction,
}

enum FixAction {
    // the original c_exposed_fns/export_name-triggered flow: rename the
    // fn itself to `internal_name` and strip its export_name/no_mangle
    // attrs; the wrapper (cloned before the strip) keeps the original
    // ident and attrs and forwards into `internal_name`
    Rename {
        internal_name: Symbol,
    },
    // field specialization flow (task 3): the internal `_field` fn is left
    // completely untouched (already renamed and attr-stripped by the
    // pointer pass); a NEW wrapper item is synthesized under
    // `exported_name`, carrying `attr`, forwarding into the internal fn's
    // own (unchanged) name
    FieldSpec {
        exported_name: Symbol,
        attr: FieldSpecAttr,
    },
}

struct AstVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    ast_to_hir: AstToHir,
    fixes: FxHashMap<LocalDefId, FixEntry<'tcx>>,
}

impl mut_visit::MutVisitor for AstVisitor<'_> {
    fn flat_map_item(&mut self, item: P<Item>) -> smallvec::SmallVec<[P<Item>; 1]> {
        let id = item.id;
        let mut items = mut_visit::walk_flat_map_item(self, item);

        if let Some(def_id) = self.ast_to_hir.global_map.get(&id)
            && let Some(fix) = self.fixes.get(def_id)
        {
            let ItemKind::Fn(orig_f) = &items[0].kind else { panic!() };
            // the name the wrapper's forwarding call targets: the renamed
            // internal name for the Rename flow, or the (unchanged) internal
            // fn's own current name for the FieldSpec flow
            let call_target = match &fix.action {
                FixAction::Rename { internal_name } => *internal_name,
                FixAction::FieldSpec { .. } => orig_f.ident.name,
            };

            let mut new_item = items[0].clone();
            {
                let ItemKind::Fn(f) = &mut new_item.kind else { panic!() };
                let mut call = format!("{call_target}(");
                for (i, param) in f.sig.decl.inputs.iter_mut().enumerate() {
                    let PatKind::Ident(_, ident, _) = &param.pat.kind else { panic!() };
                    let x = ident.name;
                    if let Some(pfix) = fix.param_fixes.get(&i) {
                        let m = if pfix.mutability.is_mut() {
                            "mut"
                        } else {
                            "const"
                        };
                        match pfix.kind {
                            ParamFixKind::Slice => {
                                let ty = utils::ir::mir_ty_to_string(pfix.ty, self.tcx);
                                *param.ty = utils::ty!("*{m} {ty}");
                                write!(
                                    call,
                                    "if {x}.is_null() {{ &{}[] }} else {{ std::slice::from_raw_parts{}({x}, 1_000_000) }}, ",
                                    if pfix.mutability.is_mut() { "mut " } else { "" },
                                    if pfix.mutability.is_mut() { "_mut" } else { "" },
                                )
                                .unwrap();
                            }
                            ParamFixKind::SliceCursor => {
                                let ty = utils::ir::mir_ty_to_string(pfix.ty, self.tcx);
                                *param.ty = utils::ty!("*{m} {ty}");
                                if pfix.mutability.is_mut() {
                                    write!(
                                        call,
                                        "if {x}.is_null() {{ crate::slice_cursor::SliceCursorMut::empty() }} else {{ crate::slice_cursor::SliceCursorMut::new(std::slice::from_raw_parts_mut({x}, 1_000_000)) }}, ",
                                    )
                                    .unwrap();
                                } else {
                                    write!(
                                        call,
                                        "if {x}.is_null() {{ crate::slice_cursor::SliceCursor::empty() }} else {{ crate::slice_cursor::SliceCursor::new(std::slice::from_raw_parts({x}, 1_000_000)) }}, ",
                                    )
                                    .unwrap();
                                }
                            }
                            ParamFixKind::StructField {
                                struct_name,
                                field,
                                option_wrapped,
                            } => {
                                *param.ty = utils::ty!("*{m} {struct_name}");
                                if option_wrapped {
                                    let ctor = if pfix.mutability.is_mut() {
                                        format!("Some(&mut (*{x}).{field})")
                                    } else {
                                        format!("Some(&(*{x}).{field})")
                                    };
                                    write!(
                                        call,
                                        "if {x}.is_null() {{ None }} else {{ {ctor} }}, ",
                                    )
                                    .unwrap();
                                } else {
                                    let t = utils::ir::mir_ty_to_string(pfix.ty, self.tcx);
                                    let mm = if pfix.mutability.is_mut() { "mut " } else { "" };
                                    write!(
                                        call,
                                        "if {x}.is_null() {{ 0 as *{m} {t} }} else {{ &{mm}(*{x}).{field} as *{m} {t} }}, ",
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
            }

            match &fix.action {
                FixAction::Rename { internal_name } => {
                    items.push(new_item);

                    let ItemKind::Fn(orig_f) = &mut items[0].kind else { panic!() };
                    orig_f.ident.name = *internal_name;
                    items[0].attrs.retain(|attr| {
                        !attr.has_name(sym::export_name) && !attr.has_name(sym::no_mangle)
                    });
                }
                FixAction::FieldSpec {
                    exported_name,
                    attr,
                } => {
                    let ItemKind::Fn(f) = &mut new_item.kind else { panic!() };
                    f.ident.name = *exported_name;
                    // wholesale replace, not merge: the fresh wrapper is a new
                    // C-facing entry point and deliberately does not inherit
                    // the internal `_field` fn's attrs
                    new_item.attrs = match attr {
                        FieldSpecAttr::NoMangle => utils::attr!("#[no_mangle]"),
                        FieldSpecAttr::ExportName(s) => utils::attr!("#[export_name = {s:?}]"),
                    };
                    items.push(new_item);
                    // items[0] (the internal `_field` fn) stays untouched:
                    // no rename, no attr strip -- its attrs are already gone
                }
            }
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
            && let Some(fix) = self.fixes.get(&def_id)
            && let FixAction::Rename { internal_name } = &fix.action
        {
            seg.ident.name = *internal_name;
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
            && let Some(fix) = self.fixes.get(&def_id)
            && let FixAction::Rename { internal_name } = &fix.action
        {
            path.segments.last_mut().unwrap().ident.name = *internal_name;
        }
    }
}

#[derive(Clone, Copy)]
struct ParamFix<'tcx> {
    kind: ParamFixKind,
    mutability: ty::Mutability,
    ty: ty::Ty<'tcx>,
}

#[derive(Clone, Copy)]
enum ParamFixKind {
    Slice,
    SliceCursor,
    // a struct-pointer param specialized to one field (task 3); `ty` on the
    // enclosing `ParamFix` holds the observed field/pointee type, used for
    // the raw-pointer-target conversion arm's cast type
    StructField {
        struct_name: Symbol,
        field: Symbol,
        // true when the observed shape is `Option<&T>`/`Option<&mut T>`;
        // false when it's a raw `*const T`/`*mut T`
        option_wrapped: bool,
    },
}

struct HirVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    config: &'a Config,
    struct_fields: &'a FxHashMap<(String, String), ty::Ty<'tcx>>,
    fixes: FxHashMap<LocalDefId, FixEntry<'tcx>>,
}

impl<'tcx> intravisit::Visitor<'tcx> for HirVisitor<'_, 'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_item(&mut self, item: &'tcx hir::Item<'tcx>) {
        if let hir::ItemKind::Fn { ident, body, .. } = item.kind {
            let name = ident.name.as_str();
            if self.config.c_exposed_fns.contains(name)
                || self
                    .tcx
                    .get_attrs(item.owner_id.def_id.to_def_id(), sym::export_name)
                    .any(|attr| {
                        attr.value_str()
                            .is_some_and(|s| self.config.c_exposed_fns.contains(s.as_str()))
                    })
            {
                self.analyze_rename_target(item, name, body);
            } else if let Some((exported_symbol, entry)) =
                find_field_spec_entry(self.config, self.tcx, item.owner_id.def_id, name)
            {
                self.analyze_field_spec_target(item, name, body, exported_symbol, entry);
            }
        }

        intravisit::walk_item(self, item);
    }
}

impl<'tcx> HirVisitor<'_, 'tcx> {
    fn analyze_rename_target(&mut self, item: &hir::Item<'tcx>, name: &str, body: hir::BodyId) {
        let body = self.tcx.hir_body(body);
        let typeck = self.tcx.typeck(item.owner_id.def_id);
        let fixes = detect_slice_cursor_fixes(self.tcx, body, typeck);
        if !fixes.is_empty() {
            let new_name = Symbol::intern(&format!("{name}_internal"));
            self.fixes.insert(
                item.owner_id.def_id,
                FixEntry {
                    param_fixes: fixes,
                    action: FixAction::Rename {
                        internal_name: new_name,
                    },
                },
            );
        }
    }

    fn analyze_field_spec_target(
        &mut self,
        item: &hir::Item<'tcx>,
        name: &str,
        body: hir::BodyId,
        exported_symbol: &str,
        entry: &FieldSpecEntry,
    ) {
        let body = self.tcx.hir_body(body);
        let typeck = self.tcx.typeck(item.owner_id.def_id);
        let mut fixes = detect_slice_cursor_fixes(self.tcx, body, typeck);
        for p in &entry.params {
            match resolve_struct_field_fix(self.tcx, body, typeck, p, self.struct_fields) {
                Some(fix) => {
                    fixes.insert(p.index, fix);
                }
                None => {
                    // fail-closed: an unsupported observed shape for any one
                    // specialized param drops the whole entry, no wrapper
                    eprintln!(
                        "[interface-fixer] skipping field specialization wrapper for {exported_symbol:?}: {name:?} param {} (struct {:?} field {:?}) has an unsupported observed shape",
                        p.index, p.struct_name, p.field,
                    );
                    return;
                }
            }
        }
        let exported_name = Symbol::intern(exported_symbol);
        self.fixes.insert(
            item.owner_id.def_id,
            FixEntry {
                param_fixes: fixes,
                action: FixAction::FieldSpec {
                    exported_name,
                    attr: entry.attr.clone(),
                },
            },
        );
    }
}

// the existing slice/`SliceCursor`(`Mut`) param-shape detection, shared by
// both the rename flow and the field-spec flow
fn detect_slice_cursor_fixes<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &hir::Body<'tcx>,
    typeck: &ty::TypeckResults<'tcx>,
) -> FxHashMap<usize, ParamFix<'tcx>> {
    let mut fixes = FxHashMap::default();
    for (i, param) in body.params.iter().enumerate() {
        let ty = typeck.node_type(param.pat.hir_id);

        if let ty::TyKind::Ref(_, inner_ty, m) = ty.kind()
            && let ty::TyKind::Slice(inner_ty) = inner_ty.kind()
        {
            fixes.insert(
                i,
                ParamFix {
                    kind: ParamFixKind::Slice,
                    mutability: *m,
                    ty: *inner_ty,
                },
            );
            continue;
        }

        if let ty::TyKind::Adt(adt_def, generic_args) = ty.kind() {
            let adt_name = adt_def
                .did()
                .as_local()
                .map(|def_id| tcx.item_name(def_id.into()));
            let Some(adt_name) = adt_name else { continue };

            let (kind, mutability) = if adt_name.as_str() == "SliceCursorMut" {
                (ParamFixKind::SliceCursor, ty::Mutability::Mut)
            } else if adt_name.as_str() == "SliceCursor" {
                (ParamFixKind::SliceCursor, ty::Mutability::Not)
            } else {
                continue;
            };

            let Some(inner_ty) = generic_args.types().next() else { continue };

            fixes.insert(
                i,
                ParamFix {
                    kind,
                    mutability,
                    ty: inner_ty,
                },
            );
        }
    }
    fixes
}

// looks up the `field_spec` entry (if any) whose `internal` name matches
// `name`. names are guaranteed crate-unique by the pointer pass, so a single
// match is the normal case; if more than one entry happens to share the same
// internal name (only possible from hand-edited or otherwise corrupt sidecar
// data, since the pointer pass itself never emits this), `module` is used to
// disambiguate. a remaining ambiguity after that is fail-closed: skip (no
// wrapper for any of the colliding entries) with a diagnostic, consistent
// with every other "don't synthesize a wrapper from data we can't fully
// trust" case in this file — corrupt sidecar data must not panic the pass
fn find_field_spec_entry<'a>(
    config: &'a Config,
    tcx: TyCtxt<'_>,
    def_id: LocalDefId,
    name: &str,
) -> Option<(&'a str, &'a FieldSpecEntry)> {
    let mut matches: Vec<(&str, &FieldSpecEntry)> = config
        .field_spec
        .iter()
        .filter(|(_, e)| e.internal == name)
        .map(|(k, e)| (k.as_str(), e))
        .collect();
    if matches.len() > 1 {
        let module = field_module_path(tcx, def_id);
        matches.retain(|(_, e)| e.module == module);
        if matches.len() > 1 {
            eprintln!(
                "[interface-fixer] skipping field specialization wrapper(s) for internal fn {name:?}: \
                 ambiguous field_spec entries even after module disambiguation ({} candidates)",
                matches.len(),
            );
            return None;
        }
    }
    matches.into_iter().next()
}

// the fn's c2rust module path: `tcx.def_path_str` minus the fn's own
// trailing segment (mirrors the pointer pass's own `field_module_path`,
// which produced the `module` field in the first place)
fn field_module_path(tcx: TyCtxt<'_>, did: LocalDefId) -> String {
    let path = tcx.def_path_str(did.to_def_id());
    match path.rsplit_once("::") {
        Some((prefix, _)) => prefix.to_string(),
        None => String::new(),
    }
}

// checks the observed (post-promotion) type of the param at `param.index`
// against the supported shapes: `Option<&T>`, `Option<&mut T>`, or a raw
// `*const T`/`*mut T`, where `T` must equal the recorded struct field's own
// type (looked up by name via `struct_fields`). anything else (including a
// missing struct/field lookup) returns `None`, signaling the whole entry
// should be skipped
fn resolve_struct_field_fix<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &hir::Body<'tcx>,
    typeck: &ty::TypeckResults<'tcx>,
    param: &FieldSpecParam,
    struct_fields: &FxHashMap<(String, String), ty::Ty<'tcx>>,
) -> Option<ParamFix<'tcx>> {
    let hir_param = body.params.get(param.index)?;
    let ty = typeck.node_type(hir_param.pat.hir_id);
    let expected = *struct_fields.get(&(param.struct_name.clone(), param.field.clone()))?;
    // mutability below is derived from `ty.kind()`, the observed promoted
    // shape, which is authoritative; `param.mutbl` is not consulted here

    let (pointee, mutability, option_wrapped) = match ty.kind() {
        ty::TyKind::Adt(adt_def, generic_args) if utils::ir::is_option(adt_def.did(), tcx) => {
            let inner = generic_args.types().next()?;
            let ty::TyKind::Ref(_, pointee, m) = inner.kind() else {
                return None;
            };
            (*pointee, *m, true)
        }
        ty::TyKind::RawPtr(pointee, m) => (*pointee, *m, false),
        _ => return None,
    };

    if pointee != expected {
        return None;
    }

    Some(ParamFix {
        kind: ParamFixKind::StructField {
            struct_name: Symbol::intern(&param.struct_name),
            field: Symbol::intern(&param.field),
            option_wrapped,
        },
        mutability,
        ty: pointee,
    })
}

// one-shot crate scan resolving every struct's field types up front, keyed
// by (struct name, field name) text -- name-only, like the rest of this
// file's field-spec matching, since `FieldSpecParam` only carries names
struct StructFieldVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    fields: FxHashMap<(String, String), ty::Ty<'tcx>>,
}

impl<'tcx> intravisit::Visitor<'tcx> for StructFieldVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_item(&mut self, item: &'tcx hir::Item<'tcx>) {
        if let hir::ItemKind::Struct(ident, ..) = item.kind {
            let def_id = item.owner_id.def_id;
            let struct_ty = self.tcx.type_of(def_id).skip_binder();
            if let ty::TyKind::Adt(adt_def, args) = struct_ty.kind() {
                for field in &adt_def.non_enum_variant().fields {
                    self.fields.insert(
                        (ident.name.to_string(), field.name.to_string()),
                        field.ty(self.tcx, args),
                    );
                }
            }
        }
        intravisit::walk_item(self, item);
    }
}

#[cfg(test)]
mod tests {
    use rustc_hash::FxHashSet;
    use utils::field_spec::{FieldSpecAttr, FieldSpecEntry, FieldSpecMap, FieldSpecParam};

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
            ..Default::default()
        };
        let transformed = utils::compilation::run_compiler_on_str(code, |tcx| {
            super::fix_interfaces(&config, tcx)
        })
        .unwrap();
        utils::compilation::run_compiler_on_str(&transformed, utils::type_check)
            .expect(&transformed);

        assert!(transformed.contains("fn match_0_internal"));
        assert!(transformed.contains("fn match_0(test: *const f64"));
        assert_eq!(transformed.matches("#[export_name = \"match\"]").count(), 1);
    }

    // backward compat: config text written before field_spec existed still
    // deserializes, with field_spec defaulting to an empty map
    #[test]
    fn config_without_field_spec_deserializes_with_default() {
        let text = r#"{"c_exposed_fns": ["foo"]}"#;
        let config: super::Config = serde_json::from_str(text).unwrap();
        assert!(config.field_spec.is_empty());
        assert!(config.c_exposed_fns.contains("foo"));
    }

    #[test]
    fn wraps_field_specialized_fn_const() {
        let code = r#"
pub struct spx_ctx {
    pub tweaked512_rc64: [[u64; 8]; 10],
    pub pub_seed: [u8; 32],
}

pub unsafe extern "C" fn SPX_haraka_S_field(out: &mut [u8], ctx: Option<&[[u64; 8]; 10]>) {
    if let Some(c) = ctx {
        out[0] = c[0][0] as u8;
    }
}
"#;
        let mut field_spec = FieldSpecMap::new();
        field_spec.insert(
            "SPX_haraka_S".to_string(),
            FieldSpecEntry {
                internal: "SPX_haraka_S_field".to_string(),
                module: String::new(),
                attr: FieldSpecAttr::NoMangle,
                params: vec![FieldSpecParam {
                    index: 1,
                    struct_name: "spx_ctx".to_string(),
                    field: "tweaked512_rc64".to_string(),
                    mutbl: "const".to_string(),
                }],
            },
        );
        let config = super::Config {
            field_spec,
            ..Default::default()
        };
        let transformed = utils::compilation::run_compiler_on_str(code, |tcx| {
            super::fix_interfaces(&config, tcx)
        })
        .unwrap();
        utils::compilation::run_compiler_on_str(&transformed, utils::type_check)
            .expect(&transformed);

        assert!(transformed.contains("#[no_mangle]"));
        assert!(transformed.contains("fn SPX_haraka_S(out: *mut u8"));
        assert!(transformed.contains("ctx: *const spx_ctx"));
        assert!(transformed.contains("ctx.is_null()"));
        assert!(transformed.contains("Some(&(*ctx).tweaked512_rc64)"));
        // the existing slice fix still applies to `out`
        assert!(transformed.contains("std::slice::from_raw_parts_mut(out, 1_000_000)"));
        // the internal `_field` fn is unrenamed and un-attributed (pprust may
        // wrap the long param list, so check the pieces independently)
        assert!(transformed.contains("fn SPX_haraka_S_field(out: &mut [u8],"));
        assert!(transformed.contains("ctx: Option<&[[u64; 8]; 10]>)"));
        assert_eq!(transformed.matches("fn SPX_haraka_S_field").count(), 1);
    }

    #[test]
    fn wraps_field_specialized_fn_mut_and_export_name() {
        let code = r#"
pub struct st {
    pub lookup: [u16; 4],
}

pub unsafe extern "C" fn build_field(p: Option<&mut [u16; 4]>) {
    if let Some(p) = p {
        p[0] = 1;
    }
}
"#;
        let mut field_spec = FieldSpecMap::new();
        field_spec.insert(
            "build".to_string(),
            FieldSpecEntry {
                internal: "build_field".to_string(),
                module: String::new(),
                attr: FieldSpecAttr::ExportName("c_name".to_string()),
                params: vec![FieldSpecParam {
                    index: 0,
                    struct_name: "st".to_string(),
                    field: "lookup".to_string(),
                    mutbl: "mut".to_string(),
                }],
            },
        );
        let config = super::Config {
            field_spec,
            ..Default::default()
        };
        let transformed = utils::compilation::run_compiler_on_str(code, |tcx| {
            super::fix_interfaces(&config, tcx)
        })
        .unwrap();
        utils::compilation::run_compiler_on_str(&transformed, utils::type_check)
            .expect(&transformed);

        assert!(transformed.contains("#[export_name = \"c_name\"]"));
        assert!(transformed.contains("fn build(p: *mut st)"));
        assert!(transformed.contains("p.is_null()"));
        assert!(transformed.contains("Some(&mut (*p).lookup)"));
        assert!(transformed.contains("fn build_field(p: Option<&mut [u16; 4]>)"));
    }

    #[test]
    fn field_spec_missing_internal_fails_closed() {
        let code = r#"
pub struct st {
    pub lookup: [u16; 4],
}

pub fn other() -> i32 {
    0
}
"#;
        let mut field_spec = FieldSpecMap::new();
        field_spec.insert(
            "build".to_string(),
            FieldSpecEntry {
                internal: "build_field".to_string(), // no such fn in this crate
                module: String::new(),
                attr: FieldSpecAttr::NoMangle,
                params: vec![FieldSpecParam {
                    index: 0,
                    struct_name: "st".to_string(),
                    field: "lookup".to_string(),
                    mutbl: "mut".to_string(),
                }],
            },
        );
        let config = super::Config {
            field_spec,
            ..Default::default()
        };
        let transformed = utils::compilation::run_compiler_on_str(code, |tcx| {
            super::fix_interfaces(&config, tcx)
        })
        .unwrap();
        utils::compilation::run_compiler_on_str(&transformed, utils::type_check)
            .expect(&transformed);

        assert!(!transformed.contains("fn build("));
        assert_eq!(transformed.matches("fn other").count(), 1);
    }

    #[test]
    fn field_spec_unsupported_shape_fails_closed() {
        let code = r#"
pub struct st {
    pub lookup: [u16; 4],
}

pub unsafe extern "C" fn build_field(p: i32) -> i32 {
    p
}
"#;
        let mut field_spec = FieldSpecMap::new();
        field_spec.insert(
            "build".to_string(),
            FieldSpecEntry {
                internal: "build_field".to_string(),
                module: String::new(),
                attr: FieldSpecAttr::NoMangle,
                params: vec![FieldSpecParam {
                    index: 0,
                    struct_name: "st".to_string(),
                    field: "lookup".to_string(),
                    mutbl: "mut".to_string(),
                }],
            },
        );
        let config = super::Config {
            field_spec,
            ..Default::default()
        };
        let transformed = utils::compilation::run_compiler_on_str(code, |tcx| {
            super::fix_interfaces(&config, tcx)
        })
        .unwrap();
        utils::compilation::run_compiler_on_str(&transformed, utils::type_check)
            .expect(&transformed);

        // no wrapper synthesized; the internal fn is untouched and appears once
        assert_eq!(transformed.matches("fn build_field").count(), 1);
        assert!(!transformed.contains("fn build("));
    }

    #[test]
    fn field_spec_ambiguous_internal_after_module_disambiguation_fails_closed() {
        // two entries share the same `internal` name AND the same recorded
        // `module`, so module-based disambiguation can't tell them apart.
        // this can only arise from a corrupt/hand-edited sidecar (the
        // pointer pass itself never emits colliding internal names) -- it
        // must skip both, not panic
        let code = r#"
pub struct st {
    pub lookup: [u16; 4],
}

pub unsafe extern "C" fn build_field(p: Option<&mut [u16; 4]>) {
    if let Some(p) = p {
        p[0] = 1;
    }
}
"#;
        let mut field_spec = FieldSpecMap::new();
        field_spec.insert(
            "build_a".to_string(),
            FieldSpecEntry {
                internal: "build_field".to_string(),
                module: String::new(),
                attr: FieldSpecAttr::NoMangle,
                params: vec![FieldSpecParam {
                    index: 0,
                    struct_name: "st".to_string(),
                    field: "lookup".to_string(),
                    mutbl: "mut".to_string(),
                }],
            },
        );
        field_spec.insert(
            "build_b".to_string(),
            FieldSpecEntry {
                internal: "build_field".to_string(),
                module: String::new(),
                attr: FieldSpecAttr::NoMangle,
                params: vec![FieldSpecParam {
                    index: 0,
                    struct_name: "st".to_string(),
                    field: "lookup".to_string(),
                    mutbl: "mut".to_string(),
                }],
            },
        );
        let config = super::Config {
            field_spec,
            ..Default::default()
        };
        let transformed = utils::compilation::run_compiler_on_str(code, |tcx| {
            super::fix_interfaces(&config, tcx)
        })
        .unwrap();
        utils::compilation::run_compiler_on_str(&transformed, utils::type_check)
            .expect(&transformed);

        // no panic, and neither candidate wrapper is synthesized; the
        // internal fn is untouched and appears exactly once
        assert!(!transformed.contains("fn build_a("));
        assert!(!transformed.contains("fn build_b("));
        assert_eq!(transformed.matches("fn build_field").count(), 1);
    }

    #[test]
    fn field_spec_disambiguated_by_module_succeeds() {
        // two entries share the same `internal` name but record different
        // `module`s; only one module matches the fn's actual (crate-root,
        // i.e. empty) module path, so disambiguation should resolve to
        // exactly that entry and synthesize its wrapper (not the other
        // entry's)
        let code = r#"
pub struct st {
    pub lookup: [u16; 4],
}

pub unsafe extern "C" fn build_field(p: Option<&mut [u16; 4]>) {
    if let Some(p) = p {
        p[0] = 1;
    }
}
"#;
        let mut field_spec = FieldSpecMap::new();
        field_spec.insert(
            "correct_name".to_string(),
            FieldSpecEntry {
                internal: "build_field".to_string(),
                module: String::new(), // matches the fn's real (crate-root) module
                attr: FieldSpecAttr::NoMangle,
                params: vec![FieldSpecParam {
                    index: 0,
                    struct_name: "st".to_string(),
                    field: "lookup".to_string(),
                    mutbl: "mut".to_string(),
                }],
            },
        );
        field_spec.insert(
            "wrong_name".to_string(),
            FieldSpecEntry {
                internal: "build_field".to_string(),
                module: "some::other::mod".to_string(), // does not match
                attr: FieldSpecAttr::NoMangle,
                params: vec![FieldSpecParam {
                    index: 0,
                    struct_name: "st".to_string(),
                    field: "lookup".to_string(),
                    mutbl: "mut".to_string(),
                }],
            },
        );
        let config = super::Config {
            field_spec,
            ..Default::default()
        };
        let transformed = utils::compilation::run_compiler_on_str(code, |tcx| {
            super::fix_interfaces(&config, tcx)
        })
        .unwrap();
        utils::compilation::run_compiler_on_str(&transformed, utils::type_check)
            .expect(&transformed);

        assert!(transformed.contains("fn correct_name(p: *mut st)"));
        assert!(!transformed.contains("fn wrong_name("));
        assert!(transformed.contains("fn build_field(p: Option<&mut [u16; 4]>)"));
    }

    #[test]
    fn renamed_internal_loses_no_mangle() {
        let code = r#"
#[no_mangle]
pub unsafe extern "C" fn match_0(test: &[f64], reference: &[f64], bins: i32) -> i32 {
    (test[0] == reference[0]) as i32 + bins
}
"#;
        let config = super::Config {
            c_exposed_fns: FxHashSet::from_iter(["match_0".to_string()]),
            ..Default::default()
        };
        let transformed = utils::compilation::run_compiler_on_str(code, |tcx| {
            super::fix_interfaces(&config, tcx)
        })
        .unwrap();
        utils::compilation::run_compiler_on_str(&transformed, utils::type_check)
            .expect(&transformed);

        assert!(transformed.contains("fn match_0_internal"));
        assert!(transformed.contains("fn match_0(test: *const f64"));
        // `#[no_mangle]` survives only on the wrapper, not on the renamed internal
        assert_eq!(transformed.matches("#[no_mangle]").count(), 1);
        let idx = transformed.find("fn match_0_internal").unwrap();
        let preceding = &transformed[idx.saturating_sub(80)..idx];
        assert!(!preceding.contains("no_mangle"), "{preceding}");
    }
}
