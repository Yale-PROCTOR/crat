use std::ops::ControlFlow;

use rustc_hash::FxHashMap;
use rustc_hir::{
    self as hir, HirId,
    def::Res,
    def_id::DefId,
    intravisit::{self, Visitor},
};
use rustc_middle::{
    hir::nested_filter,
    ty::{self, Ty, TyCtxt, TyKind, TypeVisitor},
};
use rustc_span::{FileNameDisplayPreference, Pos, Span};
use rustc_type_ir::{TypeSuperVisitable as _, TypeVisitable as _};
use serde::Serialize;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub enum FindingKind {
    #[serde(rename = "local variable")]
    LocalVariable,
    #[serde(rename = "static")]
    Static,
    #[serde(rename = "const")]
    Const,
    #[serde(rename = "function return")]
    FunctionReturn,
    #[serde(rename = "field")]
    Field,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct Occurrence {
    pub file: String,
    pub line: usize,
    pub col: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Finding {
    pub name: String,
    #[serde(rename = "type")]
    pub ty: String,
    pub kind: FindingKind,
    pub file: String,
    pub line: usize,
    pub col: usize,
    pub uses: Vec<Occurrence>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Identifier {
    Local(HirId),
    Definition(DefId),
}

struct PendingFinding {
    finding: Finding,
    use_spans: Vec<Span>,
}

pub fn find_void(tcx: TyCtxt<'_>) -> Vec<Finding> {
    let mut definitions = DefinitionCollector {
        tcx,
        indices: FxHashMap::default(),
        findings: Vec::new(),
    };
    tcx.hir_visit_all_item_likes_in_crate(&mut definitions);

    let mut uses = UseCollector {
        tcx,
        indices: &definitions.indices,
        findings: &mut definitions.findings,
    };
    tcx.hir_visit_all_item_likes_in_crate(&mut uses);

    let mut findings = definitions
        .findings
        .into_iter()
        .map(|mut pending| {
            pending.finding.uses = pending
                .use_spans
                .into_iter()
                .map(|span| occurrence(span, tcx))
                .collect();
            pending.finding.uses.sort();
            pending.finding.uses.dedup();
            pending.finding
        })
        .collect::<Vec<_>>();
    findings.sort_by(|lhs, rhs| {
        (&lhs.file, lhs.line, lhs.col, lhs.kind, &lhs.name)
            .cmp(&(&rhs.file, rhs.line, rhs.col, rhs.kind, &rhs.name))
    });
    findings
}

struct DefinitionCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    indices: FxHashMap<Identifier, usize>,
    findings: Vec<PendingFinding>,
}

impl<'tcx> DefinitionCollector<'tcx> {
    fn add(
        &mut self,
        id: Identifier,
        name: rustc_span::Symbol,
        ty: Ty<'tcx>,
        kind: FindingKind,
        span: Span,
    ) {
        if self.indices.contains_key(&id) || !contains_c_void(ty, self.tcx) {
            return;
        }
        let definition = occurrence(span, self.tcx);
        self.indices.insert(id, self.findings.len());
        self.findings.push(PendingFinding {
            finding: Finding {
                name: name.to_string(),
                ty: mir_ty_to_string(ty, self.tcx),
                kind,
                file: definition.file,
                line: definition.line,
                col: definition.col,
                uses: Vec::new(),
            },
            use_spans: Vec::new(),
        });
    }

    fn add_fields(&mut self, fields: &'tcx [hir::FieldDef<'tcx>]) {
        for field in fields {
            let ty = self.tcx.type_of(field.def_id).instantiate_identity();
            self.add(
                Identifier::Definition(field.def_id.to_def_id()),
                field.ident.name,
                ty,
                FindingKind::Field,
                field.ident.span,
            );
        }
    }
}

impl<'tcx> Visitor<'tcx> for DefinitionCollector<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_item(&mut self, item: &'tcx hir::Item<'tcx>) {
        let def_id = item.owner_id.def_id;
        match item.kind {
            hir::ItemKind::Static(_, ident, _, _) => {
                let ty = self.tcx.type_of(def_id).instantiate_identity();
                self.add(
                    Identifier::Definition(def_id.to_def_id()),
                    ident.name,
                    ty,
                    FindingKind::Static,
                    ident.span,
                );
            }
            hir::ItemKind::Const(ident, _, _, _) => {
                let ty = self.tcx.type_of(def_id).instantiate_identity();
                self.add(
                    Identifier::Definition(def_id.to_def_id()),
                    ident.name,
                    ty,
                    FindingKind::Const,
                    ident.span,
                );
            }
            hir::ItemKind::Fn { ident, .. } => {
                let sig = self.tcx.fn_sig(def_id).instantiate_identity().skip_binder();
                self.add(
                    Identifier::Definition(def_id.to_def_id()),
                    ident.name,
                    sig.output(),
                    FindingKind::FunctionReturn,
                    ident.span,
                );
            }
            hir::ItemKind::Struct(_, _, data) | hir::ItemKind::Union(_, _, data) => {
                self.add_fields(data.fields());
            }
            hir::ItemKind::Enum(_, _, enum_def) => {
                for variant in enum_def.variants {
                    self.add_fields(variant.data.fields());
                }
            }
            _ => {}
        }
        intravisit::walk_item(self, item);
    }

    fn visit_pat(&mut self, pat: &'tcx hir::Pat<'tcx>) {
        if let hir::PatKind::Binding(_, hir_id, ident, _) = pat.kind {
            let ty = self.tcx.typeck(pat.hir_id.owner).node_type(hir_id);
            self.add(
                Identifier::Local(hir_id),
                ident.name,
                ty,
                FindingKind::LocalVariable,
                ident.span,
            );
        }
        intravisit::walk_pat(self, pat);
    }
}

struct UseCollector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    indices: &'a FxHashMap<Identifier, usize>,
    findings: &'a mut [PendingFinding],
}

impl UseCollector<'_, '_> {
    fn add(&mut self, id: Identifier, span: Span) {
        if let Some(&index) = self.indices.get(&id) {
            self.findings[index].use_spans.push(span);
        }
    }
}

impl<'tcx> Visitor<'tcx> for UseCollector<'_, 'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_item(&mut self, item: &'tcx hir::Item<'tcx>) {
        if let hir::ItemKind::Use(path, hir::UseKind::Single(alias)) = item.kind {
            for res in path.res.present_items() {
                if let Res::Def(_, def_id) = res {
                    self.add(Identifier::Definition(def_id), alias.span);
                }
            }
        }
        intravisit::walk_item(self, item);
    }

    fn visit_path(&mut self, path: &hir::Path<'tcx>, _hir_id: HirId) {
        let id = match path.res {
            Res::Local(hir_id) => Some(Identifier::Local(hir_id)),
            Res::Def(_, def_id) => Some(Identifier::Definition(def_id)),
            _ => None,
        };
        if let (Some(id), Some(segment)) = (id, path.segments.last()) {
            self.add(id, segment.ident.span);
        }
        intravisit::walk_path(self, path);
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        match expr.kind {
            hir::ExprKind::Field(base, ident) => {
                let typeck = self.tcx.typeck(expr.hir_id.owner);
                if let Some(field_index) = typeck.opt_field_index(expr.hir_id)
                    && let TyKind::Adt(adt, _) = typeck.expr_ty_adjusted(base).peel_refs().kind()
                {
                    let field = &adt.non_enum_variant().fields[field_index];
                    self.add(Identifier::Definition(field.did), ident.span);
                }
            }
            hir::ExprKind::Struct(qpath, fields, _) => {
                let typeck = self.tcx.typeck(expr.hir_id.owner);
                if let TyKind::Adt(adt, _) = typeck.expr_ty(expr).peel_refs().kind() {
                    let variant = adt.variant_of_res(typeck.qpath_res(qpath, expr.hir_id));
                    for field in fields {
                        if let Some(field_index) = typeck.opt_field_index(field.hir_id) {
                            let field_def = &variant.fields[field_index];
                            self.add(Identifier::Definition(field_def.did), field.ident.span);
                        }
                    }
                }
            }
            hir::ExprKind::OffsetOf(_, fields) => self.add_offset_of_uses(expr, fields),
            _ => {}
        }
        intravisit::walk_expr(self, expr);
    }

    fn visit_pat(&mut self, pat: &'tcx hir::Pat<'tcx>) {
        if let hir::PatKind::Struct(qpath, fields, _) = pat.kind {
            let typeck = self.tcx.typeck(pat.hir_id.owner);
            if let TyKind::Adt(adt, _) = typeck.node_type(pat.hir_id).peel_refs().kind() {
                let variant = adt.variant_of_res(typeck.qpath_res(&qpath, pat.hir_id));
                for field in fields {
                    if let Some(field_index) = typeck.opt_field_index(field.hir_id) {
                        let field_def = &variant.fields[field_index];
                        self.add(Identifier::Definition(field_def.did), field.ident.span);
                    }
                }
            }
        }
        intravisit::walk_pat(self, pat);
    }
}

impl<'tcx> UseCollector<'_, 'tcx> {
    fn add_offset_of_uses(&mut self, expr: &hir::Expr<'tcx>, fields: &[rustc_span::Ident]) {
        let typeck = self.tcx.typeck(expr.hir_id.owner);
        let Some((mut ty, field_indices)) = typeck.offset_of_data().get(expr.hir_id).cloned()
        else {
            return;
        };
        for (ident, (variant_index, field_index)) in fields.iter().zip(field_indices) {
            match ty.kind() {
                TyKind::Adt(adt, args) => {
                    let field = &adt.variant(variant_index).fields[field_index];
                    self.add(Identifier::Definition(field.did), ident.span);
                    ty = field.ty(self.tcx, args);
                }
                TyKind::Tuple(types) => {
                    ty = types[field_index.index()];
                }
                _ => return,
            }
        }
    }
}

fn contains_c_void<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    struct CVoidVisitor<'tcx> {
        tcx: TyCtxt<'tcx>,
    }

    impl<'tcx> TypeVisitor<TyCtxt<'tcx>> for CVoidVisitor<'tcx> {
        type Result = ControlFlow<()>;

        fn visit_ty(&mut self, ty: Ty<'tcx>) -> Self::Result {
            if let TyKind::Adt(adt, _) = ty.kind()
                && self.tcx.is_lang_item(adt.did(), hir::LangItem::CVoid)
            {
                return ControlFlow::Break(());
            }
            ty.super_visit_with(self)
        }
    }

    ty.visit_with(&mut CVoidVisitor { tcx }).is_break()
}

fn mir_ty_to_string(ty: Ty<'_>, tcx: TyCtxt<'_>) -> String {
    match ty.kind() {
        TyKind::Bool => "bool".to_string(),
        TyKind::Char => "char".to_string(),
        TyKind::Int(int) => int.name_str().to_string(),
        TyKind::Uint(int) => int.name_str().to_string(),
        TyKind::Float(float) => float.name_str().to_string(),
        TyKind::Adt(adt, args) => {
            let mut result = if adt.did().is_local() {
                format!("crate::{}", tcx.def_path_str(adt.did()))
            } else {
                tcx.def_path_str(adt.did())
            };
            if !args.is_empty() {
                let args = args
                    .iter()
                    .map(|arg| match arg.kind() {
                        ty::GenericArgKind::Lifetime(_) => "'_".to_string(),
                        ty::GenericArgKind::Type(ty) => mir_ty_to_string(ty, tcx),
                        ty::GenericArgKind::Const(value) => value.to_string(),
                    })
                    .collect::<Vec<_>>()
                    .join(", ");
                result.push('<');
                result.push_str(&args);
                result.push('>');
            }
            result
        }
        TyKind::Foreign(def_id) => {
            if def_id.is_local() {
                format!("crate::{}", tcx.def_path_str(*def_id))
            } else {
                tcx.def_path_str(*def_id)
            }
        }
        TyKind::Str => "str".to_string(),
        TyKind::Array(element, length) => {
            format!("[{}; {length}]", mir_ty_to_string(*element, tcx))
        }
        TyKind::Slice(element) => format!("[{}]", mir_ty_to_string(*element, tcx)),
        TyKind::RawPtr(element, mutability) => {
            let mutability = if mutability.is_mut() { "mut" } else { "const" };
            format!("*{mutability} {}", mir_ty_to_string(*element, tcx))
        }
        TyKind::Ref(_, element, mutability) => {
            let mutability = if mutability.is_mut() { "mut " } else { "" };
            format!("&{mutability}{}", mir_ty_to_string(*element, tcx))
        }
        TyKind::FnPtr(signature, header) => {
            let signature = signature.skip_binder();
            let mut result = String::new();
            if header.safety.is_unsafe() {
                result.push_str("unsafe ");
            }
            if !header.abi.is_rustic_abi() {
                result.push_str(&format!("extern \"{}\" ", header.abi.name()));
            }
            result.push_str("fn(");
            result.push_str(
                &signature
                    .inputs()
                    .iter()
                    .map(|ty| mir_ty_to_string(*ty, tcx))
                    .collect::<Vec<_>>()
                    .join(", "),
            );
            if header.c_variadic {
                if !signature.inputs().is_empty() {
                    result.push_str(", ");
                }
                result.push_str("...");
            }
            result.push_str(") -> ");
            result.push_str(&mir_ty_to_string(signature.output(), tcx));
            result
        }
        TyKind::Never => "!".to_string(),
        TyKind::Tuple(types) => {
            let mut result = types
                .iter()
                .map(|ty| mir_ty_to_string(ty, tcx))
                .collect::<Vec<_>>()
                .join(", ");
            if types.len() == 1 {
                result.push(',');
            }
            format!("({result})")
        }
        _ => ty.to_string(),
    }
}

fn occurrence(span: Span, tcx: TyCtxt<'_>) -> Occurrence {
    let location = tcx.sess.source_map().lookup_char_pos(span.lo());
    Occurrence {
        file: location
            .file
            .name
            .display(FileNameDisplayPreference::Local)
            .to_string(),
        line: location.line,
        col: location.col.to_usize() + 1,
    }
}

#[cfg(test)]
mod tests {
    use utils::compilation;

    use super::*;

    fn analyze(code: &str) -> Vec<Finding> {
        compilation::run_compiler_on_str(code, find_void).unwrap()
    }

    fn find<'a>(findings: &'a [Finding], kind: FindingKind, name: &str) -> &'a Finding {
        findings
            .iter()
            .find(|finding| finding.kind == kind && finding.name == name)
            .unwrap()
    }

    #[test]
    fn finds_definitions_and_bound_occurrences() {
        let findings = analyze(
            r#"
type VoidPtr = *mut core::ffi::c_void;

static mut GLOBAL: VoidPtr = core::ptr::null_mut();
const NULL: VoidPtr = core::ptr::null_mut();

struct Record {
    named: (*mut *mut core::ffi::c_void, i32),
    plain: i32,
}

struct Tuple(VoidPtr, i32);

enum Choice {
    Some { payload: VoidPtr },
    None,
}

union Either {
    pointer: VoidPtr,
    value: usize,
}

fn make(p: VoidPtr) -> VoidPtr {
    let local: (*mut *mut core::ffi::c_void, i32) = (core::ptr::null_mut(), 0);
    let record = Record { named: local, plain: 0 };
    let Record { named, .. } = record;
    let tuple = Tuple(p, 0);
    let _ = tuple.0;
    let _ = core::mem::offset_of!(Record, named);
    let choice = Choice::Some { payload: p };
    if let Choice::Some { payload } = choice {
        let _ = payload;
    }
    let either = Either { pointer: p };
    let _ = unsafe { either.pointer };
    unsafe { GLOBAL = p; }
    let _ = NULL;
    let _ = named.0;
    p
}

fn take_function() {
    let _ = make;
}
"#,
        );

        assert_eq!(find(&findings, FindingKind::Field, "named").uses.len(), 3);
        assert_eq!(find(&findings, FindingKind::Field, "0").uses.len(), 1);
        assert_eq!(find(&findings, FindingKind::Field, "payload").uses.len(), 2);
        assert_eq!(find(&findings, FindingKind::Field, "pointer").uses.len(), 2);
        assert_eq!(find(&findings, FindingKind::Static, "GLOBAL").uses.len(), 1);
        assert_eq!(find(&findings, FindingKind::Const, "NULL").uses.len(), 1);
        assert_eq!(
            find(&findings, FindingKind::FunctionReturn, "make")
                .uses
                .len(),
            1
        );
        assert_eq!(
            find(&findings, FindingKind::LocalVariable, "local")
                .uses
                .len(),
            1
        );
        assert_eq!(
            find(&findings, FindingKind::LocalVariable, "named")
                .uses
                .len(),
            1
        );
        assert!(!findings.iter().any(|finding| finding.name == "record"));
        assert!(!findings.iter().any(|finding| finding.name == "tuple"));
        assert!(
            findings.iter().all(|finding| {
                finding.file == "<main.rs>"
                    && finding.line > 0
                    && finding.col > 0
                    && finding
                        .uses
                        .iter()
                        .all(|use_| use_.file == "<main.rs>" && use_.line > 0 && use_.col > 0)
            }),
            "{findings:#?}"
        );
    }

    #[test]
    fn resolves_aliases_and_prints_generic_types() {
        let findings = analyze(
            r#"
type VoidPtr = *mut core::ffi::c_void;

struct Generic<T> {
    mixed: (T, VoidPtr),
}

fn generic<T>(value: (T, VoidPtr)) -> (T, VoidPtr) {
    value
}
"#,
        );

        for finding in [
            find(&findings, FindingKind::Field, "mixed"),
            find(&findings, FindingKind::FunctionReturn, "generic"),
            find(&findings, FindingKind::LocalVariable, "value"),
        ] {
            assert_eq!(finding.ty, "(T, *mut std::ffi::c_void)");
        }
    }

    #[test]
    fn excludes_foreign_items() {
        let findings = analyze(
            r#"
extern "C" {
    fn foreign() -> *mut core::ffi::c_void;
    static FOREIGN: *mut core::ffi::c_void;
}

fn use_foreign_items() {
    unsafe {
        let _ = foreign();
        let _ = FOREIGN;
    }
}
"#,
        );

        assert!(findings.is_empty());
    }

    #[test]
    fn finds_renamed_imports_and_closure_bindings() {
        let findings = analyze(
            r#"
fn returns_void() -> *mut core::ffi::c_void {
    core::ptr::null_mut()
}

mod nested {
    use super::returns_void as alias;

    fn use_alias() {
        let _ = alias;
    }
}

fn use_closure() {
    let closure = |parameter: *mut core::ffi::c_void| {
        let local = parameter;
        local
    };
    let _ = closure(core::ptr::null_mut());
}
"#,
        );

        assert_eq!(
            find(&findings, FindingKind::FunctionReturn, "returns_void")
                .uses
                .len(),
            3
        );
        assert_eq!(
            find(&findings, FindingKind::LocalVariable, "parameter")
                .uses
                .len(),
            1
        );
        assert_eq!(
            find(&findings, FindingKind::LocalVariable, "local")
                .uses
                .len(),
            1
        );
    }
}
