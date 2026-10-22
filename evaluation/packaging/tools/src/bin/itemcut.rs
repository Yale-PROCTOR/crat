//! Removes the items the compiler reports as never used: reads `file<TAB>line<TAB>name` lines on stdin (the line of
//! the item's name, 1-based) and cuts, from each file, the item (with its attributes) whose name is `name` on that line:
//! a function, constant, static, type alias, struct, enum, union, trait, macro, or an associated function, constant or
//! type of an inherent impl. Prints `CUT` or `MISS` per request; a file that does not parse again after the cuts is
//! left unchanged and reported (exit 2).
use std::{
    collections::BTreeMap,
    env, fs,
    io::{self, BufRead},
    ops::Range,
};

use proc_macro2::{TokenStream, TokenTree};
use quote::ToTokens;
use syn::{
    visit::{self, Visit},
    ImplItem, Item,
};

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

struct Finder<'a> {
    want: &'a [(usize, String)],
    found: Vec<(usize, String, &'static str, Range<usize>)>,
}

impl Finder<'_> {
    fn consider(&mut self, ident: &syn::Ident, kind: &'static str, range: Range<usize>) {
        let line = ident.span().start().line;
        let name = ident.to_string();
        if self.want.iter().any(|(l, n)| *l == line && *n == name) {
            self.found.push((line, name, kind, range));
        }
    }
}

impl<'ast> Visit<'ast> for Finder<'_> {
    fn visit_item(&mut self, i: &'ast Item) {
        let hit = match i {
            Item::Fn(x) => Some((&x.sig.ident, "fn")),
            Item::Const(x) => Some((&x.ident, "const")),
            Item::Static(x) => Some((&x.ident, "static")),
            Item::Type(x) => Some((&x.ident, "type")),
            Item::Struct(x) => Some((&x.ident, "struct")),
            Item::Enum(x) => Some((&x.ident, "enum")),
            Item::Union(x) => Some((&x.ident, "union")),
            Item::Trait(x) => Some((&x.ident, "trait")),
            Item::Macro(x) => x.ident.as_ref().map(|id| (id, "macro")),
            _ => None,
        };
        if let Some((ident, kind)) = hit {
            self.consider(ident, kind, range_of(i));
        }
        visit::visit_item(self, i);
    }

    fn visit_item_impl(&mut self, i: &'ast syn::ItemImpl) {
        // Only inherent impls: a trait impl's items are required by the trait.
        if i.trait_.is_none() {
            for it in &i.items {
                let hit = match it {
                    ImplItem::Fn(x) => Some((&x.sig.ident, "assoc fn")),
                    ImplItem::Const(x) => Some((&x.ident, "assoc const")),
                    ImplItem::Type(x) => Some((&x.ident, "assoc type")),
                    _ => None,
                };
                if let Some((ident, kind)) = hit {
                    self.consider(ident, kind, range_of(it));
                }
            }
        }
        visit::visit_item_impl(self, i);
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
        // an item sharing its line with another: the spaces between them go with it
        if at_line_end { s..e } else { r.start..e }
    }
}

fn apply(src: &str, mut cuts: Vec<Range<usize>>) -> String {
    cuts.sort_by_key(|r| (r.start, std::cmp::Reverse(r.end)));
    let b = src.as_bytes();
    let mut merged: Vec<Range<usize>> = Vec::new();
    for r in cuts.iter().map(|r| expand_lines(b, r)) {
        if let Some(last) = merged.last_mut() {
            if r.start <= last.end {
                last.end = last.end.max(r.end);
                continue;
            }
        }
        merged.push(r);
    }
    let mut out = String::with_capacity(src.len());
    let mut pos = 0;
    for r in merged {
        out.push_str(&src[pos..r.start]);
        pos = r.end;
        if out.ends_with("\n\n") {
            while src[pos..].starts_with('\n') {
                pos += 1;
            }
        }
    }
    out.push_str(&src[pos..]);
    out
}

fn main() {
    let root = env::args().nth(1).unwrap_or_default();
    let mut want: BTreeMap<String, Vec<(usize, String)>> = BTreeMap::new();
    for line in io::stdin().lock().lines() {
        let line = line.expect("stdin");
        let mut f = line.split('\t');
        let (Some(path), Some(l), Some(name)) = (f.next(), f.next(), f.next()) else {
            continue;
        };
        want.entry(path.to_string())
            .or_default()
            .push((l.parse().expect("line"), name.to_string()));
    }
    let mut failed = 0;
    for (path, items) in &want {
        let full = if root.is_empty() { path.clone() } else { format!("{root}/{path}") };
        let src = fs::read_to_string(&full).expect("read");
        let file = syn::parse_file(&src).expect("parse");
        let mut finder = Finder { want: items, found: Vec::new() };
        finder.visit_file(&file);
        for (l, n) in items {
            match finder.found.iter().find(|(fl, fname, _, _)| fl == l && fname == n) {
                Some((_, _, kind, _)) => println!("CUT\t{path}\t{l}\t{n}\t{kind}"),
                None => println!("MISS\t{path}\t{l}\t{n}"),
            }
        }
        if finder.found.is_empty() {
            continue;
        }
        let out = apply(&src, finder.found.iter().map(|f| f.3.clone()).collect());
        if let Err(e) = syn::parse_file(&out) {
            println!("REPARSE-FAIL\t{path}\t{e}");
            failed += 1;
            continue;
        }
        fs::write(&full, out).expect("write");
    }
    if failed > 0 {
        std::process::exit(2);
    }
}
