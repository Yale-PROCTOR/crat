use std::{env, fs, ops::Range};

use proc_macro2::{TokenStream, TokenTree};
use quote::ToTokens;
use syn::{
    visit::{self, Visit},
    Attribute, Expr, ForeignItem, ImplItem, Item, Meta, Stmt, TraitItem,
};

#[derive(PartialEq)]
enum Kind {
    Test,
    NotTest,
    Other,
}

fn classify(attr: &Attribute) -> Kind {
    if attr.path().is_ident("test") {
        return Kind::Test;
    }
    if attr.path().is_ident("cfg") {
        if let Meta::List(list) = &attr.meta {
            let s: String = list
                .tokens
                .to_string()
                .chars()
                .filter(|c| !c.is_whitespace())
                .collect();
            if s == "test" || s.starts_with("all(test,") || s == "all(test)" {
                return Kind::Test;
            }
            if s == "not(test)" {
                return Kind::NotTest;
            }
            if s.contains("test") {
                eprintln!("NOTE unusual cfg: {}", list.tokens);
            }
        }
    }
    Kind::Other
}

fn walk(ts: TokenStream, lo: &mut usize, hi: &mut usize) {
    for tt in ts {
        let r = tt.span().byte_range();
        if r.end > r.start || r.end > 0 {
            *lo = (*lo).min(r.start);
            *hi = (*hi).max(r.end);
        }
        if let TokenTree::Group(g) = tt {
            walk(g.stream(), lo, hi);
        }
    }
}

fn range_of<T: ToTokens>(node: &T) -> Range<usize> {
    let mut lo = usize::MAX;
    let mut hi = 0;
    walk(node.to_token_stream(), &mut lo, &mut hi);
    assert!(lo != usize::MAX, "empty token stream");
    lo..hi
}

struct Cutter<'a> {
    src: &'a str,
    cuts: Vec<Range<usize>>,
    attr_cuts: Vec<Range<usize>>,
}

impl<'a> Cutter<'a> {
    fn handle(
        &mut self,
        attrs: &[Attribute],
        node: &dyn Fn() -> Range<usize>,
        trailing_comma: bool,
    ) -> bool {
        if attrs.iter().any(|a| classify(a) == Kind::Test) {
            let mut r = node();
            if trailing_comma {
                let b = self.src.as_bytes();
                let mut e = r.end;
                while e < b.len()
                    && (b[e] == b' ' || b[e] == b'\t' || b[e] == b'\n' || b[e] == b'\r')
                {
                    e += 1;
                }
                if e < b.len() && b[e] == b',' {
                    r.end = e + 1;
                }
            }
            self.cuts.push(r);
            return true;
        }
        for a in attrs {
            if classify(a) == Kind::NotTest {
                self.attr_cuts.push(range_of(a));
            }
        }
        false
    }
}

fn item_attrs(i: &Item) -> Option<&Vec<Attribute>> {
    Some(match i {
        Item::Const(x) => &x.attrs,
        Item::Enum(x) => &x.attrs,
        Item::ExternCrate(x) => &x.attrs,
        Item::Fn(x) => &x.attrs,
        Item::ForeignMod(x) => &x.attrs,
        Item::Impl(x) => &x.attrs,
        Item::Macro(x) => &x.attrs,
        Item::Mod(x) => &x.attrs,
        Item::Static(x) => &x.attrs,
        Item::Struct(x) => &x.attrs,
        Item::Trait(x) => &x.attrs,
        Item::TraitAlias(x) => &x.attrs,
        Item::Type(x) => &x.attrs,
        Item::Union(x) => &x.attrs,
        Item::Use(x) => &x.attrs,
        _ => return None,
    })
}

fn expr_attrs(e: &Expr) -> Option<&Vec<Attribute>> {
    Some(match e {
        Expr::Array(x) => &x.attrs,
        Expr::Assign(x) => &x.attrs,
        Expr::Async(x) => &x.attrs,
        Expr::Await(x) => &x.attrs,
        Expr::Binary(x) => &x.attrs,
        Expr::Block(x) => &x.attrs,
        Expr::Break(x) => &x.attrs,
        Expr::Call(x) => &x.attrs,
        Expr::Cast(x) => &x.attrs,
        Expr::Closure(x) => &x.attrs,
        Expr::Const(x) => &x.attrs,
        Expr::Continue(x) => &x.attrs,
        Expr::Field(x) => &x.attrs,
        Expr::ForLoop(x) => &x.attrs,
        Expr::Group(x) => &x.attrs,
        Expr::If(x) => &x.attrs,
        Expr::Index(x) => &x.attrs,
        Expr::Infer(x) => &x.attrs,
        Expr::Let(x) => &x.attrs,
        Expr::Lit(x) => &x.attrs,
        Expr::Loop(x) => &x.attrs,
        Expr::Macro(x) => &x.attrs,
        Expr::Match(x) => &x.attrs,
        Expr::MethodCall(x) => &x.attrs,
        Expr::Paren(x) => &x.attrs,
        Expr::Path(x) => &x.attrs,
        Expr::Range(x) => &x.attrs,
        Expr::Reference(x) => &x.attrs,
        Expr::Repeat(x) => &x.attrs,
        Expr::Return(x) => &x.attrs,
        Expr::Struct(x) => &x.attrs,
        Expr::Try(x) => &x.attrs,
        Expr::TryBlock(x) => &x.attrs,
        Expr::Tuple(x) => &x.attrs,
        Expr::Unary(x) => &x.attrs,
        Expr::Unsafe(x) => &x.attrs,
        Expr::While(x) => &x.attrs,
        Expr::Yield(x) => &x.attrs,
        _ => return None,
    })
}

impl<'ast, 'a> Visit<'ast> for Cutter<'a> {
    fn visit_item(&mut self, i: &'ast Item) {
        if let Some(attrs) = item_attrs(i) {
            if self.handle(attrs, &|| range_of(i), false) {
                return;
            }
        }
        visit::visit_item(self, i);
    }

    fn visit_impl_item(&mut self, i: &'ast ImplItem) {
        let attrs = match i {
            ImplItem::Const(x) => Some(&x.attrs),
            ImplItem::Fn(x) => Some(&x.attrs),
            ImplItem::Type(x) => Some(&x.attrs),
            ImplItem::Macro(x) => Some(&x.attrs),
            _ => None,
        };
        if let Some(attrs) = attrs {
            if self.handle(attrs, &|| range_of(i), false) {
                return;
            }
        }
        visit::visit_impl_item(self, i);
    }

    fn visit_trait_item(&mut self, i: &'ast TraitItem) {
        let attrs = match i {
            TraitItem::Const(x) => Some(&x.attrs),
            TraitItem::Fn(x) => Some(&x.attrs),
            TraitItem::Type(x) => Some(&x.attrs),
            TraitItem::Macro(x) => Some(&x.attrs),
            _ => None,
        };
        if let Some(attrs) = attrs {
            if self.handle(attrs, &|| range_of(i), false) {
                return;
            }
        }
        visit::visit_trait_item(self, i);
    }

    fn visit_foreign_item(&mut self, i: &'ast ForeignItem) {
        let attrs = match i {
            ForeignItem::Fn(x) => Some(&x.attrs),
            ForeignItem::Static(x) => Some(&x.attrs),
            ForeignItem::Type(x) => Some(&x.attrs),
            ForeignItem::Macro(x) => Some(&x.attrs),
            _ => None,
        };
        if let Some(attrs) = attrs {
            if self.handle(attrs, &|| range_of(i), false) {
                return;
            }
        }
        visit::visit_foreign_item(self, i);
    }

    fn visit_field(&mut self, f: &'ast syn::Field) {
        if self.handle(&f.attrs, &|| range_of(f), true) {
            return;
        }
        visit::visit_field(self, f);
    }

    fn visit_variant(&mut self, v: &'ast syn::Variant) {
        if self.handle(&v.attrs, &|| range_of(v), true) {
            return;
        }
        visit::visit_variant(self, v);
    }

    fn visit_arm(&mut self, a: &'ast syn::Arm) {
        if self.handle(&a.attrs, &|| range_of(a), true) {
            return;
        }
        visit::visit_arm(self, a);
    }

    fn visit_field_value(&mut self, f: &'ast syn::FieldValue) {
        if self.handle(&f.attrs, &|| range_of(f), true) {
            return;
        }
        visit::visit_field_value(self, f);
    }

    fn visit_stmt(&mut self, s: &'ast Stmt) {
        let attrs: Option<&Vec<Attribute>> = match s {
            Stmt::Local(x) => Some(&x.attrs),
            Stmt::Item(_) => None,
            Stmt::Expr(e, _) => expr_attrs(e),
            Stmt::Macro(x) => Some(&x.attrs),
        };
        if let Some(attrs) = attrs {
            if self.handle(attrs, &|| range_of(s), false) {
                return;
            }
        }
        visit::visit_stmt(self, s);
    }
}

fn expand_lines(src: &[u8], r: &Range<usize>) -> Range<usize> {
    let mut s = r.start;
    while s > 0 && (src[s - 1] == b' ' || src[s - 1] == b'\t') {
        s -= 1;
    }
    let at_line_start = s == 0 || src[s - 1] == b'\n';
    let mut e = r.end;
    while e < src.len() && (src[e] == b' ' || src[e] == b'\t') {
        e += 1;
    }
    let at_line_end = e == src.len() || src[e] == b'\n';
    if at_line_start && at_line_end {
        if e < src.len() {
            e += 1;
        }
        s..e
    } else {
        r.clone()
    }
}

fn apply(src: &str, mut cuts: Vec<Range<usize>>) -> String {
    cuts.sort_by_key(|r| (r.start, std::cmp::Reverse(r.end)));
    let mut merged: Vec<Range<usize>> = Vec::new();
    for r in cuts {
        if let Some(last) = merged.last_mut() {
            if r.start < last.end {
                last.end = last.end.max(r.end);
                continue;
            }
        }
        merged.push(r);
    }
    let b = src.as_bytes();
    let expanded: Vec<Range<usize>> = merged.iter().map(|r| expand_lines(b, r)).collect();
    let mut merged2: Vec<Range<usize>> = Vec::new();
    for r in expanded {
        if let Some(last) = merged2.last_mut() {
            if r.start <= last.end {
                last.end = last.end.max(r.end);
                continue;
            }
        }
        merged2.push(r);
    }
    let mut out = String::with_capacity(src.len());
    let mut pos = 0;
    for r in merged2 {
        out.push_str(&src[pos..r.start]);
        pos = r.end;
        // avoid leaving two blank lines where one removal joined two gaps
        if out.ends_with("\n\n") {
            let rest = &src[pos..];
            let mut skip = 0;
            while rest[skip..].starts_with('\n') {
                skip += 1;
            }
            pos += skip;
        }
    }
    out.push_str(&src[pos..]);
    out
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let mut total_cuts = 0;
    let mut total_attr = 0;
    let mut failed = Vec::new();
    for path in &args[1..] {
        let src = fs::read_to_string(path).expect("read");
        let file = match syn::parse_file(&src) {
            Ok(f) => f,
            Err(e) => {
                eprintln!("PARSE-FAIL\t{}\t{}", path, e);
                failed.push(path.clone());
                continue;
            }
        };
        let mut c = Cutter {
            src: &src,
            cuts: Vec::new(),
            attr_cuts: Vec::new(),
        };
        c.visit_file(&file);
        // verify that every cut range starts at a '#' or an identifier (sanity)
        let n_cuts = c.cuts.len();
        let n_attr = c.attr_cuts.len();
        if n_cuts + n_attr == 0 {
            continue;
        }
        let mut all = c.cuts;
        all.extend(c.attr_cuts);
        let out = apply(&src, all);
        if let Err(e) = syn::parse_file(&out) {
            eprintln!("REPARSE-FAIL\t{}\t{}", path, e);
            failed.push(path.clone());
            continue;
        }
        fs::write(path, &out).expect("write");
        println!(
            "{}\t{}\t{}\t{}\t{}",
            path,
            n_cuts,
            n_attr,
            src.len(),
            out.len()
        );
        total_cuts += n_cuts;
        total_attr += n_attr;
    }
    eprintln!(
        "TOTAL\tcuts={}\tattr_cuts={}\tfailed={}",
        total_cuts,
        total_attr,
        failed.len()
    );
    if !failed.is_empty() {
        std::process::exit(2);
    }
}
