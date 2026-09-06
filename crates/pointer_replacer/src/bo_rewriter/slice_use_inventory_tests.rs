//! F01 offline syntax instrument, authorized by loop-2 addendum 208 A.
//! Only the pinned parser runs: no expansion, type checking, analysis, model,
//! cache, or census-worker entry is called. All artifact I/O is test-only.

use std::{collections::BTreeSet, fs};

use rustc_ast::{
    self as ast,
    visit::{self, Visitor},
};
use rustc_session::parse::ParseSess;
use rustc_span::{FileName, Span, edition::Edition};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

#[derive(Clone, Debug, Deserialize)]
struct Site {
    identity: String,
    lo: u32,
    hi: u32,
}

#[derive(Deserialize)]
struct InputFile {
    program: String,
    file: String,
    path: String,
    input_sha256: String,
    sites: Vec<Site>,
}

#[derive(Debug, Serialize)]
struct Shape {
    identity: String,
    leaf_shape: String,
    use_shape: String,
    ancestors: Vec<String>,
    cursor_at_reported_use: bool,
    query_lo: u32,
    query_hi: u32,
    matched_lo: u32,
    matched_hi: u32,
    reported_source: String,
}

#[derive(Serialize)]
struct OutputFile {
    program: String,
    file: String,
    input_sha256: String,
    parse_errors: usize,
    shapes: Vec<Shape>,
}

fn parse_crate(psess: &ParseSess, name: &str, source: &str) -> Result<ast::Crate, String> {
    let mut parser = match rustc_parse::new_parser_from_source_str(
        psess,
        FileName::Custom(name.to_owned()),
        source.to_owned(),
    ) {
        Ok(parser) => parser,
        Err(errors) => {
            for error in errors {
                error.cancel();
            }
            return Err(format!("lexical error in {name}"));
        }
    };
    let krate = match parser.parse_crate_mod() {
        Ok(krate) => krate,
        Err(error) => {
            error.cancel();
            return Err(format!("parse error in {name}"));
        }
    };
    // A returned AST alone is insufficient: rustc can recover after reporting
    // an error. No recovered tree may supply even a site-local classification.
    if psess.dcx().has_errors().is_some() {
        return Err(format!("recovered parse error in {name}"));
    }
    Ok(krate)
}

fn expression_shape(expression: &ast::Expr) -> &'static str {
    use ast::ExprKind as E;
    match &expression.kind {
        E::Path(..) => "bare-local",
        E::Call(..) => "call",
        E::MethodCall(..) => "method-call",
        E::Cast(..) => "cast",
        E::AddrOf(_, mutability, _) => {
            if mutability.is_mut() {
                "address-of-mut"
            } else {
                "address-of-shared"
            }
        }
        E::Unary(ast::UnOp::Deref, _) => "deref",
        E::Unary(..) => "unary",
        E::Field(..) => "projection",
        E::Index(..) => "index",
        E::Assign(..) => "assignment",
        E::AssignOp(..) => "assignment-op",
        E::Ret(..) => "return",
        E::Paren(..) => "paren",
        E::Block(..) => "block",
        E::Binary(..) => "binary",
        E::If(..) => "if",
        E::While(..) => "while",
        E::ForLoop { .. } => "for",
        E::Loop(..) => "loop",
        E::Match(..) => "match",
        E::Closure(..) => "closure",
        E::Struct(..) => "struct-initializer",
        E::Array(..) => "array",
        E::Repeat(..) => "repeat",
        E::Tup(..) => "tuple",
        E::Lit(..) => "literal",
        E::Let(..) => "let-expression",
        E::ConstBlock(..) => "const-block",
        E::Gen(..) => "generator",
        E::Await(..) => "await",
        E::Use(..) => "use",
        E::TryBlock(..) => "try-block",
        E::Range(..) => "range",
        E::Underscore => "underscore",
        E::Break(..) => "break",
        E::Continue(..) => "continue",
        E::InlineAsm(..) => "inline-asm",
        E::OffsetOf(..) => "offset-of",
        E::MacCall(..) => "macro",
        E::Try(..) => "try",
        E::Yield(..) => "yield",
        E::Yeet(..) => "yeet",
        E::Become(..) => "tail-call",
        E::IncludedBytes(..) => "included-bytes",
        E::FormatArgs(..) => "format-args",
        E::Type(..) => "type-ascription",
        E::UnsafeBinderCast(..) => "unsafe-binder-cast",
        E::Err(..) | E::Dummy => "invalid-expression",
    }
}

struct ShapeVisitor<'a, 'ast> {
    source: &'a str,
    source_start: u32,
    sites: &'a [Site],
    found: Vec<Option<Shape>>,
    expressions: Vec<&'ast ast::Expr>,
    locals: Vec<Span>,
}

impl ShapeVisitor<'_, '_> {
    fn range(&self, span: Span) -> (u32, u32) {
        (
            span.lo().0 - self.source_start,
            span.hi().0 - self.source_start,
        )
    }

    fn contains(&self, span: Span, site: &Site) -> bool {
        let (lo, hi) = self.range(span);
        lo <= site.lo && site.hi <= hi
    }

    fn shape(&self, expression: &ast::Expr, site: &Site) -> Shape {
        let mut cursor = false;
        let mut ancestors = Vec::new();
        for parent in self.expressions.iter().rev() {
            let shape = match &parent.kind {
                ast::ExprKind::Call(callee, arguments) => {
                    if arguments.iter().any(|arg| self.contains(arg.span, site)) {
                        "call-argument".to_owned()
                    } else if self.contains(callee.span, site) {
                        "call-callee".to_owned()
                    } else {
                        "call".to_owned()
                    }
                }
                ast::ExprKind::MethodCall(call) => {
                    let receiver = self.contains(call.receiver.span, site);
                    let name = call.seg.ident.name.as_str();
                    if receiver
                        && matches!(
                            name,
                            "offset"
                                | "add"
                                | "sub"
                                | "wrapping_offset"
                                | "wrapping_add"
                                | "wrapping_sub"
                        )
                    {
                        cursor = true;
                    }
                    format!(
                        "method-{}:{name}",
                        if receiver { "receiver" } else { "argument" }
                    )
                }
                _ => expression_shape(parent).to_owned(),
            };
            ancestors.push(shape);
        }
        if self.locals.iter().any(|span| self.contains(*span, site)) {
            ancestors.push("local-initializer".to_owned());
        }
        let use_shape = if cursor {
            "cursor".to_owned()
        } else {
            ancestors
                .iter()
                .find(|kind| !matches!(kind.as_str(), "bare-local" | "paren" | "block"))
                .cloned()
                .unwrap_or_else(|| expression_shape(expression).to_owned())
        };
        let (matched_lo, matched_hi) = self.range(expression.span);
        Shape {
            identity: site.identity.clone(),
            leaf_shape: expression_shape(expression).to_owned(),
            use_shape,
            ancestors,
            cursor_at_reported_use: cursor,
            query_lo: site.lo,
            query_hi: site.hi,
            matched_lo,
            matched_hi,
            reported_source: self.source[site.lo as usize..site.hi as usize].to_owned(),
        }
    }
}

impl<'ast> Visitor<'ast> for ShapeVisitor<'_, 'ast> {
    fn visit_local(&mut self, local: &'ast ast::Local) {
        self.locals.push(local.span);
        visit::walk_local(self, local);
        self.locals.pop();
    }

    fn visit_expr(&mut self, expression: &'ast ast::Expr) {
        let (lo, hi) = self.range(expression.span);
        let first = self.sites.partition_point(|site| site.lo < lo);
        let last = self.sites.partition_point(|site| site.lo < hi);
        if first == last {
            return;
        }
        self.expressions.push(expression);
        for index in first..last {
            let site = &self.sites[index];
            if site.hi <= hi {
                let replace = self.found[index]
                    .as_ref()
                    .is_none_or(|found| hi - lo <= found.matched_hi - found.matched_lo);
                if replace {
                    self.found[index] = Some(self.shape(expression, site));
                }
            }
        }
        visit::walk_expr(self, expression);
        self.expressions.pop();
    }
}

fn classify(name: &str, source: &str, sites: &[Site]) -> Result<Vec<Shape>, String> {
    let psess = ParseSess::new(rustc_driver::DEFAULT_LOCALE_RESOURCES.to_vec());
    let krate = parse_crate(&psess, name, source)?;
    let source_start = psess.source_map().files()[0].start_pos.0;
    for site in sites {
        if site.lo >= site.hi || source.get(site.lo as usize..site.hi as usize).is_none() {
            return Err(format!("invalid input range for {}", site.identity));
        }
    }
    let mut sites = sites.to_vec();
    sites.sort_by_key(|site| (site.lo, site.hi));
    let mut visitor = ShapeVisitor {
        source,
        source_start,
        sites: &sites,
        found: std::iter::repeat_with(|| None).take(sites.len()).collect(),
        expressions: Vec::new(),
        locals: Vec::new(),
    };
    visit::walk_crate(&mut visitor, &krate);
    visitor
        .found
        .into_iter()
        .zip(sites)
        .map(|(found, site)| {
            found.ok_or_else(|| format!("no parsed expression for {}", site.identity))
        })
        .collect()
}

#[test]
fn f01_pinned_parser_inventory() {
    rustc_span::create_session_globals_then(Edition::Edition2018, &[], None, || {
        // RED evidence is the original F01 log: the auxiliary parser rejected
        // these valid nightly forms. Every ordinary suite run exercises them.
        let valid = "#![feature(extern_types)] extern \"C\" { pub type X; } fn f(p: *const i32) -> bool { unsafe { *p as i32 <= 7 } }";
        let lo = valid.find("*p as").expect("fixture use") as u32 + 1;
        let shapes = classify(
            "valid.rs",
            valid,
            &[Site {
                identity: "p".to_owned(),
                lo,
                hi: lo + 1,
            }],
        )
        .expect("pinned nightly syntax");
        assert_eq!(shapes.len(), 1);
        assert_eq!(shapes[0].leaf_shape, "bare-local");
        assert!(shapes[0].ancestors.iter().any(|shape| shape == "cast"));
        for invalid in [
            "fn broken( {",
            "fn f() { let x = ; }",
            "fn f() { let x = 1 let y = 2; }",
        ] {
            assert!(
                classify("invalid.rs", invalid, &[]).is_err(),
                "recovered AST admitted: {invalid}"
            );
        }

        let Some(input) = std::env::var_os("CRAT_F01_PARSER_INPUT") else {
            return;
        };
        let output = std::env::var_os("CRAT_F01_PARSER_OUTPUT").expect("F01 output path");
        let inputs: Vec<InputFile> = serde_json::from_slice(&fs::read(input).expect("F01 inputs"))
            .expect("F01 input schema");
        assert!(!inputs.is_empty(), "empty F01 input manifest");
        let mut identities = BTreeSet::new();
        let mut outputs = Vec::new();
        for input in inputs {
            let source = fs::read_to_string(&input.path).expect("reconstructed input");
            assert_eq!(
                format!("{:x}", Sha256::digest(source.as_bytes())),
                input.input_sha256,
                "input pin: {}",
                input.path
            );
            for site in &input.sites {
                assert!(
                    identities.insert((input.program.clone(), site.identity.clone())),
                    "duplicate first-use identity"
                );
            }
            let shapes = classify(&input.path, &source, &input.sites)
                .unwrap_or_else(|error| panic!("F01 parse gate: {error}"));
            outputs.push(OutputFile {
                program: input.program,
                file: input.file,
                input_sha256: input.input_sha256,
                parse_errors: 0,
                shapes,
            });
        }
        // No partial inventory is published if any file fails the parse gate.
        fs::write(
            output,
            serde_json::to_vec_pretty(&outputs).expect("F01 output schema"),
        )
        .expect("F01 output");
    });
}
