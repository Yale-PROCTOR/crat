//! R219 offline declaration custody. Syntax observations are independent of
//! worker placement bits; this module runs only in the test instrument.

use std::{collections::BTreeMap, fs};

use rustc_ast::{
    self as ast,
    visit::{self, Visitor},
};
use rustc_ast_pretty::pprust;
use rustc_session::parse::ParseSess;
use rustc_span::{Span, edition::Edition};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub(crate) struct ByteSpan {
    pub(crate) lo: u32,
    pub(crate) hi: u32,
}

/// Syntactic forms only: named aliases and wrapper paths remain explicit.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub(crate) enum TypeShape {
    RawPointer {
        mutable: bool,
        pointee: Box<TypeShape>,
    },
    Reference {
        mutable: bool,
        pointee: Box<TypeShape>,
    },
    Slice {
        element: Box<TypeShape>,
    },
    Option {
        path: String,
        payload: Box<TypeShape>,
    },
    #[serde(rename = "box")]
    OwningBox {
        path: String,
        payload: Box<TypeShape>,
    },
    Named {
        path: String,
    },
    Other {
        rendered: String,
    },
    Inferred,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub(crate) struct Declaration {
    pub(crate) owner: String,
    pub(crate) binding: String,
    pub(crate) parameter_index: Option<usize>,
    /// One-based occurrence of this binding name within its lexical function.
    pub(crate) local_ordinal: Option<usize>,
    pub(crate) declaration_span: ByteSpan,
    pub(crate) binding_span: ByteSpan,
    pub(crate) type_span: Option<ByteSpan>,
    pub(crate) explicit_type: Option<String>,
    pub(crate) rendered_type: Option<String>,
    pub(crate) type_shape: TypeShape,
    /// Whether the complete declared type is present without inference holes.
    pub(crate) type_is_fully_explicit: bool,
    /// Exact syntax connecting a by-value let-pattern component to an inline
    /// explicitly typed temporary. The binding's own type remains inferred.
    pub(crate) typed_component: Option<TypedComponentCustody>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub(crate) struct TypedComponentCustody {
    pub(crate) temporary: String,
    pub(crate) component_path: Vec<u32>,
    pub(crate) component_span: ByteSpan,
    pub(crate) pattern_span: ByteSpan,
    pub(crate) temporary_declaration_span: ByteSpan,
    pub(crate) temporary_binding_span: ByteSpan,
    pub(crate) returned_binding_span: ByteSpan,
    pub(crate) type_span: ByteSpan,
    pub(crate) explicit_type: String,
    pub(crate) rendered_type: String,
    pub(crate) type_shape: TypeShape,
    pub(crate) type_is_fully_explicit: bool,
}

impl Declaration {
    pub(crate) fn effective_type_shape(&self) -> Option<&TypeShape> {
        if self.type_is_fully_explicit {
            Some(&self.type_shape)
        } else {
            self.typed_component
                .as_ref()
                .filter(|carrier| carrier.type_is_fully_explicit)
                .map(|carrier| &carrier.type_shape)
        }
    }
}

fn observed_type(ty: &ast::Ty) -> TypeShape {
    match &ty.kind {
        ast::TyKind::Ptr(inner) => TypeShape::RawPointer {
            mutable: inner.mutbl.is_mut(),
            pointee: Box::new(observed_type(&inner.ty)),
        },
        ast::TyKind::Ref(_, inner) => TypeShape::Reference {
            mutable: inner.mutbl.is_mut(),
            pointee: Box::new(observed_type(&inner.ty)),
        },
        ast::TyKind::Slice(element) => TypeShape::Slice {
            element: Box::new(observed_type(element)),
        },
        ast::TyKind::Paren(inner) => observed_type(inner),
        ast::TyKind::Infer => TypeShape::Inferred,
        ast::TyKind::Path(None, path) => {
            if let Some(last) = path.segments.last()
                && matches!(last.ident.name.as_str(), "Option" | "Box")
                && let Some(ast::GenericArgs::AngleBracketed(arguments)) = last.args.as_deref()
                && let [ast::AngleBracketedArg::Arg(ast::GenericArg::Type(payload))] =
                    arguments.args.as_slice()
                && path
                    .segments
                    .iter()
                    .take(path.segments.len() - 1)
                    .all(|segment| segment.args.is_none())
            {
                let wrapper_path = path
                    .segments
                    .iter()
                    .filter(|segment| segment.ident.name != rustc_span::kw::PathRoot)
                    .map(|segment| segment.ident.name.to_string())
                    .collect::<Vec<_>>()
                    .join("::");
                let payload = Box::new(observed_type(payload));
                if last.ident.name.as_str() == "Option" {
                    TypeShape::Option {
                        path: wrapper_path,
                        payload,
                    }
                } else {
                    TypeShape::OwningBox {
                        path: wrapper_path,
                        payload,
                    }
                }
            } else {
                TypeShape::Named {
                    path: pprust::ty_to_string(ty),
                }
            }
        }
        _ => TypeShape::Other {
            rendered: pprust::ty_to_string(ty),
        },
    }
}

fn declared_type_is_fully_explicit(ty: &ast::Ty) -> bool {
    struct ExplicitType(bool);
    impl<'ast> Visitor<'ast> for ExplicitType {
        fn visit_ty(&mut self, ty: &'ast ast::Ty) {
            if matches!(ty.kind, ast::TyKind::Infer) {
                self.0 = false;
            }
            visit::walk_ty(self, ty);
        }
    }
    let mut visitor = ExplicitType(true);
    visitor.visit_ty(ty);
    visitor.0
}

struct Bindings(Vec<rustc_span::Ident>);

impl<'ast> Visitor<'ast> for Bindings {
    fn visit_pat(&mut self, pattern: &'ast ast::Pat) {
        if let ast::PatKind::Ident(_, ident, _) = &pattern.kind {
            self.0.push(*ident);
        }
        visit::walk_pat(self, pattern);
    }
}

struct DeclarationVisitor<'source> {
    source: &'source str,
    source_start: u32,
    original_offsets: Vec<u32>,
    path: Vec<String>,
    local_counts: Vec<BTreeMap<(String, String), usize>>,
    declarations: Vec<Declaration>,
    error: Option<String>,
}

impl DeclarationVisitor<'_> {
    fn range(&self, span: Span) -> Result<ByteSpan, String> {
        let lo = span
            .lo()
            .0
            .checked_sub(self.source_start)
            .and_then(|offset| self.original_offsets.get(offset as usize).copied());
        let hi = span
            .hi()
            .0
            .checked_sub(self.source_start)
            .and_then(|offset| self.original_offsets.get(offset as usize).copied());
        match (lo, hi) {
            (Some(lo), Some(hi))
                if lo <= hi && self.source.get(lo as usize..hi as usize).is_some() =>
            {
                Ok(ByteSpan { lo, hi })
            }
            _ => Err("declaration span is outside the original source".to_owned()),
        }
    }

    fn record(
        &mut self,
        pattern: &ast::Pat,
        ty: Option<&ast::Ty>,
        declaration_span: Span,
        parameter_index: Option<usize>,
    ) -> Result<(), String> {
        let mut bindings = Bindings(Vec::new());
        bindings.visit_pat(pattern);
        let declaration_span = self.range(declaration_span)?;
        let type_span = ty.map(|ty| self.range(ty.span)).transpose()?;
        let explicit_type =
            type_span.map(|span| self.source[span.lo as usize..span.hi as usize].to_owned());
        let rendered_type = ty.map(pprust::ty_to_string);
        let simple_binding = matches!(&pattern.kind,
            ast::PatKind::Ident(mode, _, None) if mode.0 == ast::ByRef::No);
        let type_shape = match ty {
            Some(ty) if simple_binding => observed_type(ty),
            Some(ty) => TypeShape::Other {
                rendered: pprust::ty_to_string(ty),
            },
            None => TypeShape::Inferred,
        };
        for ident in bindings.0 {
            let owner = self.path.join("::");
            let binding = ident.name.to_string();
            let binding_span = self.range(ident.span)?;
            let local_ordinal = if parameter_index.is_none() {
                let counts = self
                    .local_counts
                    .last_mut()
                    .ok_or_else(|| "local declaration lacks a lexical function".to_owned())?;
                let count = counts.entry((owner.clone(), binding.clone())).or_default();
                *count += 1;
                Some(*count)
            } else {
                None
            };
            self.declarations.push(Declaration {
                owner,
                binding,
                parameter_index,
                local_ordinal,
                declaration_span,
                binding_span,
                type_span,
                explicit_type: explicit_type.clone(),
                rendered_type: rendered_type.clone(),
                type_shape: type_shape.clone(),
                type_is_fully_explicit: ty.is_some_and(declared_type_is_fully_explicit),
                typed_component: None,
            });
        }
        Ok(())
    }

    fn typed_component(
        &self,
        pattern: &ast::Pat,
        expression: &ast::Expr,
        component_path: &[u32],
    ) -> Result<Option<TypedComponentCustody>, String> {
        let ast::PatKind::Ident(mode, _, None) = &pattern.kind else {
            return Ok(None);
        };
        if mode.0 != ast::ByRef::No || !expression.attrs.is_empty() {
            return Ok(None);
        }
        let ast::ExprKind::Block(block, None) = &expression.kind else {
            return Ok(None);
        };
        if block.rules != ast::BlockCheckMode::Default {
            return Ok(None);
        }
        let [binding, tail] = block.stmts.as_slice() else {
            return Ok(None);
        };
        let (ast::StmtKind::Let(local), ast::StmtKind::Expr(returned)) =
            (&binding.kind, &tail.kind)
        else {
            return Ok(None);
        };
        let ast::PatKind::Ident(mode, temporary, None) = &local.pat.kind else {
            return Ok(None);
        };
        if mode.0 != ast::ByRef::No
            || mode.1.is_mut()
            || local.super_.is_some()
            || !local.attrs.is_empty()
            || !returned.attrs.is_empty()
            || !matches!(&local.kind, ast::LocalKind::Init(_))
        {
            return Ok(None);
        }
        let Some(ty) = local.ty.as_deref() else {
            return Ok(None);
        };
        if !declared_type_is_fully_explicit(ty) {
            return Ok(None);
        }
        let ast::ExprKind::Path(None, path) = &returned.kind else {
            return Ok(None);
        };
        let [segment] = path.segments.as_slice() else {
            return Ok(None);
        };
        if segment.ident.name != temporary.name || segment.args.is_some() {
            return Ok(None);
        }
        let type_span = self.range(ty.span)?;
        Ok(Some(TypedComponentCustody {
            temporary: temporary.name.to_string(),
            component_path: component_path.to_vec(),
            component_span: self.range(expression.span)?,
            pattern_span: self.range(pattern.span)?,
            temporary_declaration_span: self.range(local.span)?,
            temporary_binding_span: self.range(temporary.span)?,
            returned_binding_span: self.range(segment.ident.span)?,
            type_span,
            explicit_type: self.source[type_span.lo as usize..type_span.hi as usize].to_owned(),
            rendered_type: pprust::ty_to_string(ty),
            type_shape: observed_type(ty),
            type_is_fully_explicit: true,
        }))
    }

    fn pair_typed_components(
        &self,
        pattern: &ast::Pat,
        expression: &ast::Expr,
        path: &mut Vec<u32>,
        carriers: &mut Vec<TypedComponentCustody>,
    ) -> Result<(), String> {
        let pattern_span = pattern.span;
        let component_span = expression.span;
        let mut pattern = pattern;
        while let ast::PatKind::Paren(inner) = &pattern.kind {
            pattern = inner;
        }
        let mut expression = expression;
        loop {
            if !expression.attrs.is_empty() {
                return Ok(());
            }
            let ast::ExprKind::Paren(inner) = &expression.kind else {
                break;
            };
            expression = inner;
        }
        match (&pattern.kind, &expression.kind) {
            (ast::PatKind::Tuple(patterns), ast::ExprKind::Tup(expressions))
                if patterns.len() == expressions.len()
                    && !patterns
                        .iter()
                        .any(|pattern| matches!(&pattern.kind, ast::PatKind::Rest)) =>
            {
                for (index, (pattern, expression)) in patterns.iter().zip(expressions).enumerate() {
                    path.push(u32::try_from(index).map_err(|_| "tuple component index overflow")?);
                    self.pair_typed_components(pattern, expression, path, carriers)?;
                    path.pop();
                }
            }
            (ast::PatKind::Ident(..), _) => {
                if let Some(mut carrier) = self.typed_component(pattern, expression, path)? {
                    // Pair through transparent parentheses while retaining the
                    // exact original component ranges. The block recognizer
                    // still requires its unparenthesized temporary-path tail.
                    carrier.pattern_span = self.range(pattern_span)?;
                    carrier.component_span = self.range(component_span)?;
                    carriers.push(carrier);
                }
            }
            _ => {}
        }
        Ok(())
    }

    fn record_let_expression(
        &mut self,
        pattern: &ast::Pat,
        expression: &ast::Expr,
        declaration_span: Span,
    ) -> Result<(), String> {
        let first = self.declarations.len();
        self.record(pattern, None, declaration_span, None)?;
        let mut carriers = Vec::new();
        self.pair_typed_components(pattern, expression, &mut Vec::new(), &mut carriers)?;
        for carrier in carriers {
            let matches = self.declarations[first..]
                .iter()
                .enumerate()
                .filter_map(|(index, row)| {
                    (row.binding_span.lo >= carrier.pattern_span.lo
                        && row.binding_span.hi <= carrier.pattern_span.hi)
                        .then_some(index)
                })
                .collect::<Vec<_>>();
            let [index] = matches.as_slice() else {
                return Err("typed component does not own exactly one pattern binding".to_owned());
            };
            let row = &mut self.declarations[first + *index];
            if row.typed_component.replace(carrier).is_some() {
                return Err("duplicate typed component for pattern binding".to_owned());
            }
        }
        Ok(())
    }

    fn parameters(&mut self, function: &ast::Fn) {
        for (index, parameter) in function.sig.decl.inputs.iter().enumerate() {
            if let Err(error) = self.record(
                &parameter.pat,
                Some(&parameter.ty),
                parameter.span,
                Some(index + 1),
            ) {
                self.error.get_or_insert(error);
            }
        }
    }
}

impl<'ast> Visitor<'ast> for DeclarationVisitor<'_> {
    fn visit_item(&mut self, item: &'ast ast::Item) {
        let component = item
            .kind
            .ident()
            .map(|ident| ident.name.to_string())
            .unwrap_or_else(|| format!("item@{}", item.span.lo().0 - self.source_start));
        self.path.push(component);
        let function = match &item.kind {
            ast::ItemKind::Fn(function) => Some(function),
            _ => None,
        };
        if let Some(function) = function {
            self.local_counts.push(BTreeMap::new());
            self.parameters(function);
        }
        visit::walk_item(self, item);
        if function.is_some() {
            self.local_counts.pop();
        }
        self.path.pop();
    }

    fn visit_assoc_item(&mut self, item: &'ast ast::AssocItem, context: visit::AssocCtxt) {
        let component = item
            .kind
            .ident()
            .map(|ident| ident.name.to_string())
            .unwrap_or_else(|| format!("associated@{}", item.span.lo().0 - self.source_start));
        self.path.push(component);
        let function = match &item.kind {
            ast::AssocItemKind::Fn(function) => Some(function),
            _ => None,
        };
        if let Some(function) = function {
            self.local_counts.push(BTreeMap::new());
            self.parameters(function);
        }
        visit::walk_assoc_item(self, item, context);
        if function.is_some() {
            self.local_counts.pop();
        }
        self.path.pop();
    }

    fn visit_local(&mut self, local: &'ast ast::Local) {
        if !self.local_counts.is_empty()
            && let Err(error) = self.record(&local.pat, local.ty.as_deref(), local.span, None)
        {
            self.error.get_or_insert(error);
        }
        visit::walk_local(self, local);
    }

    fn visit_expr(&mut self, expression: &'ast ast::Expr) {
        let anonymous = match expression.kind {
            ast::ExprKind::Closure(_) => Some("closure"),
            ast::ExprKind::ConstBlock(_) => Some("const"),
            _ => None,
        };
        if let Some(kind) = anonymous {
            self.path.push(format!(
                "{kind}@{}",
                expression.span.lo().0 - self.source_start
            ));
        }
        if !self.local_counts.is_empty()
            && let ast::ExprKind::Let(pattern, initializer, ..) = &expression.kind
            && let Err(error) = self.record_let_expression(pattern, initializer, expression.span)
        {
            self.error.get_or_insert(error);
        }
        visit::walk_expr(self, expression);
        if anonymous.is_some() {
            self.path.pop();
        }
    }
}

pub(crate) fn inventory_source(name: &str, source: &str) -> Result<Vec<Declaration>, String> {
    rustc_span::create_session_globals_then(Edition::Edition2018, &[], None, || {
        let psess = ParseSess::new(rustc_driver::DEFAULT_LOCALE_RESOURCES.to_vec());
        let krate = super::slice_use_inventory_tests::parse_crate(&psess, name, source)?;
        let files = psess.source_map().files();
        let file = files
            .first()
            .ok_or_else(|| "parser source file is absent".to_owned())?;
        // SourceMap removes a leading BOM and normalizes CRLF. Export offsets
        // in the original bytes whose digest the manifest pins.
        let bytes = source.as_bytes();
        let mut offset = if source.starts_with('\u{feff}') { 3 } else { 0 };
        let mut original_offsets = vec![offset as u32];
        while offset < bytes.len() {
            offset += if bytes[offset] == b'\r' && bytes.get(offset + 1) == Some(&b'\n') {
                2
            } else {
                1
            };
            original_offsets
                .push(u32::try_from(offset).map_err(|_| "source exceeds byte-span range")?);
        }
        if file
            .src
            .as_ref()
            .is_none_or(|normalized| normalized.len() + 1 != original_offsets.len())
        {
            return Err("unsupported parser source normalization".to_owned());
        }
        let mut visitor = DeclarationVisitor {
            source,
            source_start: file.start_pos.0,
            original_offsets,
            path: Vec::new(),
            local_counts: Vec::new(),
            declarations: Vec::new(),
            error: None,
        };
        visit::walk_crate(&mut visitor, &krate);
        if let Some(error) = visitor.error {
            return Err(error);
        }
        visitor
            .declarations
            .sort_by_key(|row| (row.binding_span.lo, row.binding_span.hi));
        Ok(visitor.declarations)
    })
}

#[derive(Deserialize)]
struct InventoryInput {
    path: String,
    sha256: String,
}

#[derive(Serialize)]
struct InventoryOutput {
    path: String,
    sha256: String,
    parse_errors: usize,
    declarations: Vec<Declaration>,
}

#[test]
fn custody_manifest_inventory() {
    let Some(input) = std::env::var_os("CRAT_DELIVERY_CUSTODY_INPUT") else { return };
    let output = std::env::var_os("CRAT_DELIVERY_CUSTODY_OUTPUT").expect("custody output path");
    let inputs: Vec<InventoryInput> =
        serde_json::from_slice(&fs::read(input).expect("custody manifest"))
            .expect("custody manifest schema");
    assert!(!inputs.is_empty(), "empty custody manifest");
    let mut outputs = Vec::new();
    for input in inputs {
        let source = fs::read_to_string(&input.path).expect("custody source");
        assert_eq!(
            format!("{:x}", Sha256::digest(source.as_bytes())),
            input.sha256,
            "source hash: {}",
            input.path
        );
        let declarations = inventory_source(&input.path, &source)
            .unwrap_or_else(|error| panic!("custody parse gate {}: {error}", input.path));
        outputs.push(InventoryOutput {
            path: input.path,
            sha256: input.sha256,
            parse_errors: 0,
            declarations,
        });
    }
    // Publish no partial inventory after any failed hash or parser gate.
    fs::write(
        output,
        serde_json::to_vec_pretty(&outputs).expect("custody output schema"),
    )
    .expect("custody output");
}

#[test]
fn custody_typed_component_preserves_inferred_binding_and_exact_provenance() {
    let source = "fn f() { if let (p, 0) = ({ let tmp: Option<&i32> = None; tmp }, 0) {} }";
    let rows = inventory_source("component.rs", source).expect("component syntax");
    let matches = rows
        .iter()
        .filter(|row| row.binding == "p")
        .collect::<Vec<_>>();
    assert_eq!(matches.len(), 1);
    let row = matches[0];
    assert_eq!(row.owner, "f");
    assert_eq!(row.local_ordinal, Some(1));
    assert_eq!(row.type_shape, TypeShape::Inferred);
    assert!(!row.type_is_fully_explicit);
    assert!(row.type_span.is_none());
    assert!(row.explicit_type.is_none());
    assert!(row.rendered_type.is_none());
    let carrier = row
        .typed_component
        .as_ref()
        .expect("exact component carrier");
    assert_eq!(carrier.temporary, "tmp");
    assert_eq!(carrier.component_path, vec![0]);
    assert_eq!(carrier.rendered_type, "Option<&i32>");
    assert!(
        matches!(row.effective_type_shape(), Some(TypeShape::Option { payload, .. })
        if matches!(payload.as_ref(), TypeShape::Reference { mutable: false, .. }))
    );
    for span in [
        carrier.temporary_binding_span,
        carrier.returned_binding_span,
    ] {
        assert_eq!(&source[span.lo as usize..span.hi as usize], "tmp");
    }
    assert_eq!(
        &source[carrier.type_span.lo as usize..carrier.type_span.hi as usize],
        "Option<&i32>"
    );
    assert_eq!(
        &source[carrier.pattern_span.lo as usize..carrier.pattern_span.hi as usize],
        "p"
    );
    assert_eq!(
        &source[carrier.component_span.lo as usize..carrier.component_span.hi as usize],
        "{ let tmp: Option<&i32> = None; tmp }"
    );
}

#[test]
fn custody_typed_component_pairs_nested_tuple_positions_exactly() {
    let source = "fn f() { if let ((p,), 0) = (({ let tmp: Option<&[i32]> = None; tmp },), 0) {} }";
    let rows = inventory_source("nested-component.rs", source).expect("nested component syntax");
    let row = rows.iter().find(|row| row.binding == "p").unwrap();
    assert_eq!(
        row.typed_component.as_ref().unwrap().component_path,
        vec![0, 0]
    );
    assert!(
        matches!(row.effective_type_shape(), Some(TypeShape::Option { payload, .. })
        if matches!(payload.as_ref(), TypeShape::Reference { pointee, .. }
            if matches!(pointee.as_ref(), TypeShape::Slice { .. })))
    );
}

#[test]
fn custody_typed_component_accepts_transparent_pattern_and_scrutinee_parentheses() {
    // HIR erases these parentheses around the source pattern/component. The
    // producer still emits a plain temporary path as the inline block's tail;
    // this witness does not license a different generated tail shape.
    let source = "fn f() { if let ((p), 0) = (({ let tmp: Option<&i32> = None; tmp }), 0) {} }";
    let rows = inventory_source("parenthesized-component.rs", source)
        .expect("transparent parenthesis syntax");
    let matching = rows
        .iter()
        .filter(|row| row.binding == "p")
        .collect::<Vec<_>>();
    assert_eq!(
        matching.len(),
        1,
        "the exact pattern binding must remain inventoried"
    );
    let row = matching[0];
    assert_eq!(row.owner, "f");
    assert_eq!(row.type_shape, TypeShape::Inferred);
    assert!(row.type_span.is_none());
    assert!(!row.type_is_fully_explicit);
    assert!(
        matches!(row.effective_type_shape(), Some(TypeShape::Option { payload, .. })
        if matches!(payload.as_ref(), TypeShape::Reference { mutable: false, .. })),
        "transparent source parentheses must preserve the exact typed-component proof: {row:?}"
    );
    let carrier = row
        .typed_component
        .as_ref()
        .expect("parenthesized component provenance");
    assert_eq!(carrier.component_path, vec![0]);
    assert_eq!(carrier.temporary, "tmp");
    assert_eq!(carrier.rendered_type, "Option<&i32>");
    assert!(carrier.type_is_fully_explicit);
    assert_eq!(
        &source[carrier.type_span.lo as usize..carrier.type_span.hi as usize],
        "Option<&i32>"
    );
    assert_eq!(
        &source[carrier.temporary_binding_span.lo as usize
            ..carrier.temporary_binding_span.hi as usize],
        "tmp"
    );
    assert_eq!(
        &source
            [carrier.returned_binding_span.lo as usize..carrier.returned_binding_span.hi as usize],
        "tmp"
    );
    let pattern = &source[carrier.pattern_span.lo as usize..carrier.pattern_span.hi as usize];
    assert_eq!(pattern.trim_matches(['(', ')', ' ']), "p");
    let component = &source[carrier.component_span.lo as usize..carrier.component_span.hi as usize];
    assert_eq!(
        component.trim_matches(['(', ')', ' ']),
        "{ let tmp: Option<&i32> = None; tmp }"
    );
}

#[test]
fn custody_typed_component_rejects_unproved_pattern_or_block_shapes() {
    for (label, pattern, component) in [
        ("wrong tail", "p", "{ let tmp: Option<&i32> = None; other }"),
        ("missing type", "p", "{ let tmp = None; tmp }"),
        (
            "extra statement",
            "p",
            "{ let tmp: Option<&i32> = None; touch(); tmp }",
        ),
        (
            "by-reference pattern",
            "ref p",
            "{ let tmp: Option<&i32> = None; tmp }",
        ),
        (
            "mutable temporary",
            "p",
            "{ let mut tmp: Option<&i32> = None; tmp }",
        ),
        (
            "nested inference",
            "p",
            "{ let tmp: Option<&_> = None; tmp }",
        ),
        (
            "changed tail view",
            "p",
            "{ let tmp: Option<&i32> = None; &tmp }",
        ),
    ] {
        let source = format!("fn f() {{ if let ({pattern}, 0) = ({component}, 0) {{}} }}");
        let rows = inventory_source("rejected-component.rs", &source)
            .expect("parser-only negative syntax");
        let row = rows.iter().find(|row| row.binding == "p").unwrap();
        assert!(row.typed_component.is_none(), "{label}: {row:?}");
        assert!(row.effective_type_shape().is_none(), "{label}: {row:?}");
    }
    for source in [
        "fn f() { if let (p, 0, _) = ({ let tmp: Option<&i32> = None; tmp }, 0) {} }",
        "fn f() { if let (p, ..) = ({ let tmp: Option<&i32> = None; tmp }, 0) {} }",
    ] {
        let rows =
            inventory_source("unpaired-component.rs", source).expect("unpaired tuple syntax");
        let row = rows.iter().find(|row| row.binding == "p").unwrap();
        assert!(
            row.effective_type_shape().is_none(),
            "tuple pairing must be exact: {row:?}"
        );
    }
}

#[test]
fn custody_typed_component_does_not_generalize_ordinary_local_inference() {
    let source = "fn f() { let p = { let tmp: Option<&i32> = None; tmp }; let q: &i32 = &1; }";
    let rows = inventory_source("ordinary-local.rs", source).expect("ordinary local syntax");
    let inferred = rows.iter().find(|row| row.binding == "p").unwrap();
    assert!(inferred.typed_component.is_none());
    assert!(inferred.effective_type_shape().is_none());
    let explicit = rows.iter().find(|row| row.binding == "q").unwrap();
    assert!(matches!(
        explicit.effective_type_shape(),
        Some(TypeShape::Reference { mutable: false, .. })
    ));
}

#[test]
fn custody_wrong_raw_declaration_cannot_stand_for_an_expected_reference() {
    let rows = inventory_source("forms.rs", "fn raw(p: *const i32) {} fn safe(p: &i32) {}")
        .expect("valid declaration syntax");
    assert_eq!(
        rows.len(),
        2,
        "both parameter declarations must be inventoried"
    );
    let raw = rows.iter().find(|row| row.owner == "raw").unwrap();
    let safe = rows.iter().find(|row| row.owner == "safe").unwrap();
    assert_eq!(raw.parameter_index, Some(1));
    assert_eq!(raw.rendered_type.as_deref(), Some("*const i32"));
    assert!(matches!(
        raw.type_shape,
        TypeShape::RawPointer { mutable: false, .. }
    ));
    assert!(matches!(
        safe.type_shape,
        TypeShape::Reference { mutable: false, .. }
    ));
    assert_ne!(
        raw.type_shape, safe.type_shape,
        "a raw declaration cannot prove safe delivery"
    );
}

#[test]
fn custody_option_slice_box_and_mutability_are_distinct_observations() {
    let rows = inventory_source(
        "shapes.rs",
        "fn f(a: &i32, b: &[i32], c: Option<&i32>, d: Option<&[i32]>, e: Box<i32>, f: *mut i32) {}",
    )
    .expect("valid nested type syntax");
    assert_eq!(
        rows.len(),
        6,
        "every declared parameter has an independent row"
    );
    assert_eq!(rows[2].rendered_type.as_deref(), Some("Option<&i32>"));
    assert_eq!(rows[3].rendered_type.as_deref(), Some("Option<&[i32]>"));
    assert_ne!(rows[0].type_shape, rows[1].type_shape);
    assert_ne!(rows[2].type_shape, rows[3].type_shape);
    assert!(
        matches!(&rows[3].type_shape, TypeShape::Option { payload, .. }
        if matches!(payload.as_ref(), TypeShape::Reference { pointee, mutable: false }
            if matches!(pointee.as_ref(), TypeShape::Slice { .. })))
    );
    assert!(matches!(rows[4].type_shape, TypeShape::OwningBox { .. }));
    assert!(matches!(
        rows[5].type_shape,
        TypeShape::RawPointer { mutable: true, .. }
    ));
}

#[test]
fn custody_nested_inference_is_not_fully_explicit() {
    let source = r#"fn f() {
        let array: &[_; 4] = unreachable!();
        let generic: qualified::Foo<_> = unreachable!();
        let direct: &_ = unreachable!();
        let concrete: &[i32; 4] = unreachable!();
        let unannotated = unreachable!();
    }"#;
    let rows =
        inventory_source("nested-inference.rs", source).expect("valid parser-only type syntax");
    let observed = rows
        .iter()
        .map(|row| (row.binding.as_str(), row.type_is_fully_explicit))
        .collect::<Vec<_>>();
    assert_eq!(
        observed,
        vec![
            ("array", false),
            ("generic", false),
            ("direct", false),
            ("concrete", true),
            ("unannotated", false),
        ],
        "opaque type shapes cannot conceal inference holes"
    );
}

#[test]
fn custody_duplicate_locals_and_generated_inner_keep_separate_lexical_keys() {
    let source = "mod src { mod tree { fn walk(p: *mut i32) { let value: *mut i32 = p; { let value: &i32 = &1; } } fn __crat_walk(p: &i32) {} } }";
    let rows = inventory_source("nested.rs", source).expect("nested declarations");
    assert_eq!(rows.len(), 4);
    let locals = rows
        .iter()
        .filter(|row| row.binding == "value")
        .collect::<Vec<_>>();
    assert_eq!(locals.len(), 2);
    assert!(locals.iter().all(|row| row.owner == "src::tree::walk"));
    assert_eq!(locals[0].local_ordinal, Some(1));
    assert_eq!(locals[1].local_ordinal, Some(2));
    assert!(locals[0].binding_span.lo < locals[1].binding_span.lo);
    assert!(rows.iter().any(|row| row.owner == "src::tree::__crat_walk"
        && row.parameter_index == Some(1)
        && matches!(row.type_shape, TypeShape::Reference { .. })));
    for row in &rows {
        assert_eq!(
            &source[row.binding_span.lo as usize..row.binding_span.hi as usize],
            row.binding
        );
        let span = row
            .type_span
            .expect("all fixture declarations have explicit types");
        assert_eq!(
            Some(&source[span.lo as usize..span.hi as usize]),
            row.explicit_type.as_deref()
        );
    }
}

#[test]
fn custody_pinned_parser_accepts_extern_types_without_expansion() {
    let source = "#![feature(extern_types)] extern \"C\" { pub type X; } mod nested { unsafe fn f(p: *const super::X) {} }";
    let rows = inventory_source("nightly.rs", source).expect("pinned extern_types syntax");
    assert_eq!(
        rows.len(),
        1,
        "valid nightly syntax cannot yield a vacuous inventory"
    );
    assert_eq!(rows[0].owner, "nested::f");
    assert_eq!(rows[0].binding, "p");
}

#[test]
fn custody_invalid_or_recovered_parse_never_yields_an_inventory() {
    for source in [
        "fn broken( {",
        "fn f() { let p = ; }",
        "fn f() { let p = 1 let q = 2; }",
    ] {
        assert!(
            inventory_source("invalid.rs", source).is_err(),
            "recovered AST admitted: {source}"
        );
    }
}
