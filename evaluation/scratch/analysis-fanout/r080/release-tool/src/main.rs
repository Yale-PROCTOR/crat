// relay 080 item 2: syntax-tree release counter (syn 2).
// Usage: release-tool <side> <program> <file.rs>
// Prints one TSV row per occurrence:
//   side  program  fn_key  kind  name  line  first-arg-tokens (calls only, else -)
// kind: call | valpath | method | type | macro-tok | fndef
use quote::ToTokens;
use std::env;
use std::fs;
use syn::spanned::Spanned;
use syn::visit::{self, Visit};

struct V<'a> {
    side: &'a str,
    prog: &'a str,
    mods: Vec<String>,
    fns: Vec<String>, // stack of fn keys (nested fns get outer key prefix)
}

fn path_str(p: &syn::Path) -> String {
    let mut s = String::new();
    if p.leading_colon.is_some() {
        s.push_str("::");
    }
    let segs: Vec<String> = p.segments.iter().map(|s| s.ident.to_string()).collect();
    s.push_str(&segs.join("::"));
    s
}

fn is_release_name(last: &str) -> bool {
    let l = last.to_ascii_lowercase();
    last == "drop"
        || l.contains("free")
        || l.contains("dealloc")
        || l.contains("destroy")
        || l.contains("release")
        || l.contains("delete")
}

/// special paths: forget, ManuallyDrop, Box::leak/into_raw/from_raw
fn is_special(p: &syn::Path) -> bool {
    let segs: Vec<String> = p.segments.iter().map(|s| s.ident.to_string()).collect();
    let n = segs.len();
    if n == 0 {
        return false;
    }
    let last = segs[n - 1].as_str();
    if last == "forget" {
        return true;
    }
    if segs.iter().any(|s| s == "ManuallyDrop") {
        return true;
    }
    if n >= 2 && segs[n - 2] == "Box" && (last == "leak" || last == "into_raw" || last == "from_raw") {
        return true;
    }
    false
}

impl<'a> V<'a> {
    fn key(&self) -> String {
        if let Some(f) = self.fns.last() {
            f.clone()
        } else {
            format!("{}::<item-level>", self.mods.join("::"))
        }
    }
    fn emit(&self, kind: &str, name: &str, line: usize) {
        self.emit_arg(kind, name, line, "-");
    }
    fn emit_arg(&self, kind: &str, name: &str, line: usize, arg: &str) {
        println!("{}\t{}\t{}\t{}\t{}\t{}\t{}", self.side, self.prog, self.key(), kind, name, line, arg);
    }
    fn push_fn(&mut self, name: String, line: usize) {
        let k = match self.fns.last() {
            Some(outer) => format!("{}::{}", outer, name),
            None => {
                if self.mods.is_empty() {
                    name
                } else {
                    format!("{}::{}", self.mods.join("::"), name)
                }
            }
        };
        self.fns.push(k);
        self.emit("fndef", "-", line);
    }
}

impl<'a, 'ast> Visit<'ast> for V<'a> {
    fn visit_item_mod(&mut self, m: &'ast syn::ItemMod) {
        self.mods.push(m.ident.to_string());
        visit::visit_item_mod(self, m);
        self.mods.pop();
    }
    fn visit_item_fn(&mut self, f: &'ast syn::ItemFn) {
        self.push_fn(f.sig.ident.to_string(), f.sig.ident.span().start().line);
        visit::visit_item_fn(self, f);
        self.fns.pop();
    }
    fn visit_item_impl(&mut self, i: &'ast syn::ItemImpl) {
        let selfty = i.self_ty.to_token_stream().to_string().replace(' ', "");
        let prefix = match &i.trait_ {
            Some((_, p, _)) => format!("<{} as {}>", selfty, path_str(p)),
            None => selfty,
        };
        for it in &i.items {
            match it {
                syn::ImplItem::Fn(f) => {
                    self.push_fn(
                        format!("{}::{}", prefix, f.sig.ident),
                        f.sig.ident.span().start().line,
                    );
                    visit::visit_impl_item_fn(self, f);
                    self.fns.pop();
                }
                other => visit::visit_impl_item(self, other),
            }
        }
        // attrs / generics / self_ty / trait path
        for a in &i.attrs {
            self.visit_attribute(a);
        }
        self.visit_generics(&i.generics);
        self.visit_type(&i.self_ty);
    }
    fn visit_item_trait(&mut self, t: &'ast syn::ItemTrait) {
        for it in &t.items {
            match it {
                syn::TraitItem::Fn(f) => {
                    self.push_fn(
                        format!("<trait {}>::{}", t.ident, f.sig.ident),
                        f.sig.ident.span().start().line,
                    );
                    visit::visit_trait_item_fn(self, f);
                    self.fns.pop();
                }
                other => visit::visit_trait_item(self, other),
            }
        }
    }
    fn visit_expr_call(&mut self, c: &'ast syn::ExprCall) {
        if let syn::Expr::Path(ep) = &*c.func {
            let p = &ep.path;
            let last = p.segments.last().map(|s| s.ident.to_string()).unwrap_or_default();
            if is_release_name(&last) || is_special(p) {
                let arg = c
                    .args
                    .first()
                    .map(|a| a.to_token_stream().to_string().replace('\n', " ").replace('\t', " "))
                    .unwrap_or_else(|| "-".to_string());
                self.emit_arg("call", &path_str(p), ep.span().start().line, &arg);
            }
            // visit generic args / qself types inside the callee, but not the path as a value
            if let Some(q) = &ep.qself {
                self.visit_type(&q.ty);
            }
            for s in &p.segments {
                self.visit_path_arguments(&s.arguments);
            }
            for a in &c.attrs {
                self.visit_attribute(a);
            }
            for a in &c.args {
                self.visit_expr(a);
            }
        } else {
            visit::visit_expr_call(self, c);
        }
    }
    fn visit_expr_path(&mut self, ep: &'ast syn::ExprPath) {
        let p = &ep.path;
        let last = p.segments.last().map(|s| s.ident.to_string()).unwrap_or_default();
        if is_release_name(&last) || is_special(p) {
            self.emit("valpath", &path_str(p), ep.span().start().line);
        }
        visit::visit_expr_path(self, ep);
    }
    fn visit_expr_method_call(&mut self, m: &'ast syn::ExprMethodCall) {
        let n = m.method.to_string();
        if is_release_name(&n) || n == "forget" || n == "into_raw" || n == "leak" {
            self.emit("method", &n, m.method.span().start().line);
        }
        visit::visit_expr_method_call(self, m);
    }
    fn visit_type_path(&mut self, t: &'ast syn::TypePath) {
        if t.path.segments.iter().any(|s| s.ident == "ManuallyDrop") {
            self.emit("type", &path_str(&t.path), t.span().start().line);
        }
        visit::visit_type_path(self, t);
    }
    fn visit_macro(&mut self, m: &'ast syn::Macro) {
        // macro bodies are not parsed by syn; record any release-relevant ident token
        let mut stack = vec![m.tokens.clone()];
        while let Some(ts) = stack.pop() {
            for tt in ts {
                match tt {
                    proc_macro2::TokenTree::Group(g) => stack.push(g.stream()),
                    proc_macro2::TokenTree::Ident(id) => {
                        let s = id.to_string();
                        if is_release_name(&s)
                            || s == "forget"
                            || s == "ManuallyDrop"
                            || s == "into_raw"
                            || s == "from_raw"
                            || s == "leak"
                        {
                            self.emit("macro-tok", &s, id.span().start().line);
                        }
                    }
                    _ => {}
                }
            }
        }
        visit::visit_macro(self, m);
    }
    // foreign fn declarations (extern "C" { fn free(..); }) are not calls: skip bodies-less items
    fn visit_foreign_item_fn(&mut self, _f: &'ast syn::ForeignItemFn) {}
}

fn main() {
    let a: Vec<String> = env::args().collect();
    let (side, prog, file) = (&a[1], &a[2], &a[3]);
    let src = fs::read_to_string(file).expect("read");
    let ast = match syn::parse_file(&src) {
        Ok(f) => f,
        Err(e) => {
            let lc = e.span().start();
            eprintln!("PARSE-ERROR\t{}\t{}\t{}\t{}:{}\t{}", side, prog, file, lc.line, lc.column, e);
            std::process::exit(2);
        }
    };
    let mut v = V { side, prog, mods: vec![], fns: vec![] };
    v.visit_file(&ast);
}
