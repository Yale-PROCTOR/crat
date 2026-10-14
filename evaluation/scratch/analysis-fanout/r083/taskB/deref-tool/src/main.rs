// relay 083 items 1-2 (analysis-fanout, task B): classify every `&mut *X` / `&*X` in a Rust file by syntax.
// Usage: deref-tool <side> <program> <file.rs>
// Rows (TSV):
//   DEREF side prog fn line form ctx ctx_detail param_kind ancestry operand_kind operand_ty raw_place opt_derived operand_text
//   TYPE  side prog fn line form - - - - - type_text
//   MACRO side prog fn line form - - - - - macro_name
//   VIEW  side prog fn line method ctx ctx_detail param_kind ancestry recv_kind recv_ty - - recv_text
use quote::ToTokens;
use std::collections::HashMap;
use std::env;
use std::fs;
use syn::spanned::Spanned;
use syn::visit::{self, Visit};
use syn::{Expr, Type};

#[derive(Clone)]
struct Ctx {
    kind: &'static str,
    detail: String,
    param: String,
}

#[derive(Clone)]
struct Sig {
    params: Vec<Type>,
    ret: Option<Type>,
    key: String,
    module: String,
}

#[derive(Default)]
struct Globals {
    aliases: HashMap<String, Type>,
    structs: HashMap<String, Vec<(String, Type)>>,
    fns: HashMap<String, Vec<Sig>>,
    methods: HashMap<String, Vec<Sig>>,
    statics: HashMap<String, Type>,
}

fn ts(t: &impl ToTokens) -> String {
    t.to_token_stream().to_string().split_whitespace().collect::<Vec<_>>().join(" ")
}

fn last_ident(p: &syn::Path) -> String {
    p.segments.last().map(|s| s.ident.to_string()).unwrap_or_default()
}

struct Collect<'g> {
    g: &'g mut Globals,
    selfty: Vec<Type>,
    mods: Vec<String>,
}

fn sig_of(sig: &syn::Signature, selfty: Option<&Type>, module: String) -> Sig {
    let mut params = vec![];
    for a in &sig.inputs {
        match a {
            syn::FnArg::Typed(pt) => params.push((*pt.ty).clone()),
            syn::FnArg::Receiver(_) => {}
        }
    }
    let ret = match &sig.output {
        syn::ReturnType::Default => None,
        syn::ReturnType::Type(_, t) => {
            let t = (**t).clone();
            if let (Type::Path(tp), Some(st)) = (&t, selfty) {
                if tp.path.is_ident("Self") {
                    Some(st.clone())
                } else {
                    Some(t)
                }
            } else {
                Some(t)
            }
        }
    };
    Sig { params, ret, key: ts(&sig.inputs) + " -> " + &ts(&sig.output), module }
}

impl<'g, 'ast> Visit<'ast> for Collect<'g> {
    fn visit_item_mod(&mut self, m: &'ast syn::ItemMod) {
        self.mods.push(m.ident.to_string());
        visit::visit_item_mod(self, m);
        self.mods.pop();
    }
    fn visit_item_type(&mut self, t: &'ast syn::ItemType) {
        if t.generics.params.is_empty() {
            self.g.aliases.entry(t.ident.to_string()).or_insert((*t.ty).clone());
        }
    }
    fn visit_item_struct(&mut self, s: &'ast syn::ItemStruct) {
        let mut v = vec![];
        for (i, f) in s.fields.iter().enumerate() {
            let n = f.ident.as_ref().map(|x| x.to_string()).unwrap_or_else(|| i.to_string());
            v.push((n, f.ty.clone()));
        }
        self.g.structs.entry(s.ident.to_string()).or_insert(v);
        visit::visit_item_struct(self, s);
    }
    fn visit_item_union(&mut self, s: &'ast syn::ItemUnion) {
        let v = s
            .fields
            .named
            .iter()
            .map(|f| (f.ident.as_ref().unwrap().to_string(), f.ty.clone()))
            .collect();
        self.g.structs.entry(s.ident.to_string()).or_insert(v);
    }
    fn visit_item_static(&mut self, s: &'ast syn::ItemStatic) {
        self.g.statics.entry(s.ident.to_string()).or_insert((*s.ty).clone());
        visit::visit_item_static(self, s);
    }
    fn visit_item_const(&mut self, s: &'ast syn::ItemConst) {
        self.g.statics.entry(s.ident.to_string()).or_insert((*s.ty).clone());
        visit::visit_item_const(self, s);
    }
    fn visit_foreign_item_static(&mut self, s: &'ast syn::ForeignItemStatic) {
        self.g.statics.entry(s.ident.to_string()).or_insert((*s.ty).clone());
    }
    fn visit_item_fn(&mut self, f: &'ast syn::ItemFn) {
        self.g.fns.entry(f.sig.ident.to_string()).or_default().push(sig_of(&f.sig, None, self.mods.join("::")));
        visit::visit_item_fn(self, f);
    }
    fn visit_foreign_item_fn(&mut self, f: &'ast syn::ForeignItemFn) {
        self.g.fns.entry(f.sig.ident.to_string()).or_default().push(sig_of(&f.sig, None, self.mods.join("::")));
    }
    fn visit_item_impl(&mut self, i: &'ast syn::ItemImpl) {
        self.selfty.push((*i.self_ty).clone());
        visit::visit_item_impl(self, i);
        self.selfty.pop();
    }
    fn visit_impl_item_fn(&mut self, f: &'ast syn::ImplItemFn) {
        let st = self.selfty.last().cloned();
        self.g.methods.entry(f.sig.ident.to_string()).or_default().push(sig_of(&f.sig, st.as_ref(), self.mods.join("::")));
        visit::visit_impl_item_fn(self, f);
    }
}

fn unique(v: Option<&Vec<Sig>>) -> Option<&Sig> {
    let v = v?;
    let f = v.first()?;
    if v.iter().all(|s| s.key == f.key) {
        Some(f)
    } else {
        None
    }
}

struct V<'a> {
    g: &'a Globals,
    side: &'a str,
    prog: &'a str,
    fns: Vec<String>,
    selfty: Vec<Type>,
    env: Vec<HashMap<String, Option<Type>>>,
    ctx: Vec<Ctx>,
    mods: Vec<String>,
}

fn parse_ty(s: &str) -> Type {
    syn::parse_str::<Type>(s).unwrap()
}

impl<'a> V<'a> {
    /// module-aware pick: a unique same-module candidate wins; else all candidates must agree
    fn pick<'s>(&self, v: Option<&'s Vec<Sig>>) -> Option<&'s Sig> {
        let v = v?;
        let m = self.mods.join("::");
        let same: Vec<&Sig> = v.iter().filter(|s| s.module == m).collect();
        if same.len() == 1 {
            return Some(same[0]);
        }
        unique(Some(v))
    }
    fn resolve(&self, t: &Type) -> Type {
        let mut t = t.clone();
        for _ in 0..16 {
            match &t {
                Type::Paren(p) => t = (*p.elem).clone(),
                Type::Group(p) => t = (*p.elem).clone(),
                Type::Path(tp) if tp.qself.is_none() => {
                    let seg = tp.path.segments.last().unwrap();
                    if seg.arguments.is_empty() {
                        if let Some(a) = self.g.aliases.get(&seg.ident.to_string()) {
                            t = a.clone();
                            continue;
                        }
                    }
                    return t;
                }
                _ => return t,
            }
        }
        t
    }
    fn generic0(&self, t: &Type, name: &str) -> Option<Type> {
        if let Type::Path(tp) = self.resolve(t) {
            let seg = tp.path.segments.last()?;
            if seg.ident == name {
                if let syn::PathArguments::AngleBracketed(ab) = &seg.arguments {
                    for a in &ab.args {
                        if let syn::GenericArgument::Type(t) = a {
                            return Some(t.clone());
                        }
                    }
                }
            }
        }
        None
    }
    fn kind(&self, t: &Type) -> String {
        let r = self.resolve(t);
        match &r {
            Type::Ptr(p) => {
                if p.mutability.is_some() {
                    "raw-mut".into()
                } else {
                    "raw-const".into()
                }
            }
            Type::Reference(rf) => {
                let m = if rf.mutability.is_some() { "ref-mut" } else { "ref" };
                let inner = self.resolve(&rf.elem);
                if self.generic0(&inner, "Box").is_some() {
                    format!("{}-to-box", m)
                } else if let Type::Ptr(_) = inner {
                    format!("{}-to-raw", m)
                } else {
                    m.into()
                }
            }
            Type::Path(_) => {
                if let Some(b) = self.generic0(&r, "Box") {
                    if let Type::Slice(_) = self.resolve(&b) {
                        "box-slice".into()
                    } else {
                        "box".into()
                    }
                } else if let Some(o) = self.generic0(&r, "Option") {
                    let k = self.kind(&o);
                    format!("opt({})", k)
                } else if let Type::Path(tp) = &r {
                    format!("named:{}", last_ident(&tp.path))
                } else {
                    "other".into()
                }
            }
            Type::Slice(_) => "slice".into(),
            Type::Array(_) => "array".into(),
            Type::BareFn(_) => "fnptr".into(),
            Type::Tuple(_) => "tuple".into(),
            _ => "other".into(),
        }
    }
    fn deref_one(&self, t: &Type) -> Option<Type> {
        let r = self.resolve(t);
        match &r {
            Type::Ptr(p) => Some((*p.elem).clone()),
            Type::Reference(rf) => Some((*rf.elem).clone()),
            _ => self.generic0(&r, "Box"),
        }
    }
    fn autoderef(&self, t: &Type) -> Type {
        let mut t = self.resolve(t);
        for _ in 0..8 {
            match &t {
                Type::Reference(rf) => t = self.resolve(&rf.elem),
                _ => {
                    if let Some(b) = self.generic0(&t, "Box") {
                        t = self.resolve(&b);
                    } else {
                        return t;
                    }
                }
            }
        }
        t
    }
    fn field_ty(&self, base: &Type, m: &syn::Member) -> Option<Type> {
        let b = self.autoderef(base);
        let mname = match m {
            syn::Member::Named(i) => i.to_string(),
            syn::Member::Unnamed(i) => i.index.to_string(),
        };
        match &b {
            Type::Path(tp) => {
                let n = last_ident(&tp.path);
                let fs = self.g.structs.get(&n)?;
                fs.iter().find(|(f, _)| *f == mname).map(|(_, t)| t.clone())
            }
            Type::Tuple(tt) => {
                let i: usize = mname.parse().ok()?;
                tt.elems.iter().nth(i).cloned()
            }
            _ => None,
        }
    }
    fn lookup(&self, n: &str) -> Option<Type> {
        for s in self.env.iter().rev() {
            if let Some(t) = s.get(n) {
                return t.clone();
            }
        }
        self.g.statics.get(n).cloned()
    }
    fn elem_of(&self, t: &Type) -> Option<Type> {
        let b = self.autoderef(t);
        match &b {
            Type::Array(a) => Some((*a.elem).clone()),
            Type::Slice(s) => Some((*s.elem).clone()),
            _ => self.generic0(&b, "Vec"),
        }
    }
    fn infer(&self, e: &Expr) -> Option<Type> {
        match e {
            Expr::Path(p) => {
                if p.path.segments.len() == 1 {
                    let n = p.path.segments[0].ident.to_string();
                    if n == "self" {
                        return self.lookup("self");
                    }
                    self.lookup(&n)
                } else {
                    self.g.statics.get(&last_ident(&p.path)).cloned()
                }
            }
            Expr::Paren(p) => self.infer(&p.expr),
            Expr::Group(p) => self.infer(&p.expr),
            Expr::Field(f) => {
                let bt = self.infer(&f.base)?;
                self.field_ty(&bt, &f.member)
            }
            Expr::Unary(u) => match u.op {
                syn::UnOp::Deref(_) => self.deref_one(&self.infer(&u.expr)?),
                _ => self.infer(&u.expr),
            },
            Expr::Index(i) => self.elem_of(&self.infer(&i.expr)?),
            Expr::Reference(r) => {
                let inner = self.infer(&r.expr)?;
                let m = if r.mutability.is_some() { "&mut " } else { "&" };
                syn::parse_str::<Type>(&format!("{}{}", m, ts(&inner))).ok()
            }
            Expr::Cast(c) => Some((*c.ty).clone()),
            Expr::Call(c) => {
                if let Expr::Path(fp) = &*c.func {
                    let n = last_ident(&fp.path);
                    let a0 = c.args.first();
                    match n.as_str() {
                        "from_mut" => {
                            let t = self.infer(a0?)?;
                            let r = self.deref_one(&t)?;
                            return syn::parse_str::<Type>(&format!("*mut {}", ts(&r))).ok();
                        }
                        "from_ref" => {
                            let t = self.infer(a0?)?;
                            let r = self.deref_one(&t)?;
                            return syn::parse_str::<Type>(&format!("*const {}", ts(&r))).ok();
                        }
                        "null_mut" => return Some(parse_ty("*mut ()")),
                        "null" => return Some(parse_ty("*const ()")),
                        "into_raw" => {
                            let t = self.infer(a0?)?;
                            let b = self.generic0(&t, "Box")?;
                            return syn::parse_str::<Type>(&format!("*mut {}", ts(&b))).ok();
                        }
                        "Some" => {
                            let t = self.infer(a0?)?;
                            return syn::parse_str::<Type>(&format!("Option<{}>", ts(&t))).ok();
                        }
                        "from_raw_parts_mut" => {
                            let t = self.infer(a0?)?;
                            let el = self.deref_one(&t)?;
                            return syn::parse_str::<Type>(&format!("&mut [{}]", ts(&el))).ok();
                        }
                        "from_raw_parts" => {
                            let t = self.infer(a0?)?;
                            let el = self.deref_one(&t)?;
                            return syn::parse_str::<Type>(&format!("&[{}]", ts(&el))).ok();
                        }
                        _ => {}
                    }
                    if fp.path.segments.len() >= 2 {
                        if let Some(s) = self.pick(self.g.methods.get(&n)) {
                            return s.ret.clone();
                        }
                    }
                    self.pick(self.g.fns.get(&n)).and_then(|s| s.ret.clone())
                } else {
                    None
                }
            }
            Expr::MethodCall(m) => {
                let n = m.method.to_string();
                let rt = self.infer(&m.receiver);
                match n.as_str() {
                    "offset" | "add" | "sub" | "wrapping_offset" | "wrapping_add" | "wrapping_sub"
                    | "byte_add" | "byte_offset" => {
                        let r = rt?;
                        if let Type::Ptr(_) = self.resolve(&r) {
                            Some(r)
                        } else {
                            Some(r) // integer arithmetic keeps its type too
                        }
                    }
                    "cast" => {
                        let r = rt.map(|r| self.resolve(&r));
                        let mutp = matches!(&r, Some(Type::Ptr(p)) if p.mutability.is_some());
                        let tgt = m.turbofish.as_ref().and_then(|tf| {
                            tf.args.iter().find_map(|a| {
                                if let syn::GenericArgument::Type(t) = a {
                                    Some(ts(t))
                                } else {
                                    None
                                }
                            })
                        });
                        let tgt = tgt.unwrap_or_else(|| "()".into());
                        syn::parse_str::<Type>(&format!("*{} {}", if mutp { "mut" } else { "const" }, tgt)).ok()
                    }
                    "cast_mut" => {
                        let el = self.deref_one(&rt?)?;
                        syn::parse_str::<Type>(&format!("*mut {}", ts(&el))).ok()
                    }
                    "cast_const" => {
                        let el = self.deref_one(&rt?)?;
                        syn::parse_str::<Type>(&format!("*const {}", ts(&el))).ok()
                    }
                    "as_mut_ptr" | "as_ptr" => {
                        let mk = if n == "as_mut_ptr" { "mut" } else { "const" };
                        let r = rt?;
                        if let Type::Ptr(_) = self.resolve(&r) {
                            return Some(r);
                        }
                        let el = self.elem_of(&r).or_else(|| self.deref_one(&r))?;
                        syn::parse_str::<Type>(&format!("*{} {}", mk, ts(&el))).ok()
                    }
                    "unwrap" | "expect" | "unwrap_unchecked" | "unwrap_or_default" => self.generic0(&rt?, "Option"),
                    "as_deref_mut" | "as_deref" => {
                        let o = self.generic0(&rt?, "Option")?;
                        let inner = self.deref_one(&o)?;
                        let m = if n == "as_deref_mut" { "&mut " } else { "&" };
                        syn::parse_str::<Type>(&format!("Option<{}{}>", m, ts(&inner))).ok()
                    }
                    "as_mut" | "as_ref" => {
                        let m = if n == "as_mut" { "&mut " } else { "&" };
                        let r = rt?;
                        if let Some(o) = self.generic0(&r, "Option") {
                            return syn::parse_str::<Type>(&format!("Option<{}{}>", m, ts(&o))).ok();
                        }
                        let rr = self.resolve(&r);
                        if let Type::Ptr(p) = &rr {
                            return syn::parse_str::<Type>(&format!("Option<{}{}>", m, ts(&p.elem))).ok();
                        }
                        let inner = self.deref_one(&r)?;
                        syn::parse_str::<Type>(&format!("{}{}", m, ts(&inner))).ok()
                    }
                    "map_or" | "unwrap_or" => m.args.first().and_then(|a| self.infer(a)),
                    "clone" | "take" => rt,
                    _ => self.pick(self.g.methods.get(&n)).and_then(|s| s.ret.clone()),
                }
            }
            Expr::Block(b) => b.block.stmts.last().and_then(|s| match s {
                syn::Stmt::Expr(e, None) => self.infer(e),
                _ => None,
            }),
            Expr::Unsafe(b) => b.block.stmts.last().and_then(|s| match s {
                syn::Stmt::Expr(e, None) => self.infer(e),
                _ => None,
            }),
            Expr::If(i) => i.then_branch.stmts.last().and_then(|s| match s {
                syn::Stmt::Expr(e, None) => self.infer(e),
                _ => None,
            }),
            _ => None,
        }
    }
    fn bind_pat(&mut self, p: &syn::Pat, t: Option<Type>) {
        match p {
            syn::Pat::Ident(pi) => {
                let n = pi.ident.to_string();
                self.env.last_mut().unwrap().insert(n, t);
                if let Some((_, sub)) = &pi.subpat {
                    self.bind_pat(sub, None);
                }
            }
            syn::Pat::Type(pt) => self.bind_pat(&pt.pat, Some((*pt.ty).clone())),
            syn::Pat::TupleStruct(ts_) => {
                let inner = if last_ident(&ts_.path) == "Some" {
                    t.as_ref().and_then(|t| self.generic0(t, "Option"))
                } else {
                    None
                };
                for (i, e) in ts_.elems.iter().enumerate() {
                    self.bind_pat(e, if i == 0 { inner.clone() } else { None });
                }
            }
            syn::Pat::Reference(r) => {
                let inner = t.as_ref().and_then(|t| self.deref_one(t));
                self.bind_pat(&r.pat, inner)
            }
            syn::Pat::Paren(pp) => self.bind_pat(&pp.pat, t),
            syn::Pat::Tuple(tp) => {
                for e in &tp.elems {
                    self.bind_pat(e, None);
                }
            }
            syn::Pat::Struct(ps) => {
                for f in &ps.fields {
                    self.bind_pat(&f.pat, None);
                }
            }
            syn::Pat::Slice(ps) => {
                for e in &ps.elems {
                    self.bind_pat(e, None);
                }
            }
            syn::Pat::Or(po) => {
                for c in &po.cases {
                    self.bind_pat(c, t.clone());
                }
            }
            _ => {}
        }
    }
    fn fnkey(&self) -> String {
        self.fns.last().cloned().unwrap_or_else(|| "<item>".into())
    }
    fn with<F: FnOnce(&mut Self)>(&mut self, c: Ctx, f: F) {
        self.ctx.push(c);
        f(self);
        self.ctx.pop();
    }
    fn top(&self) -> Ctx {
        self.ctx.last().cloned().unwrap_or(Ctx { kind: "none", detail: "-".into(), param: "-".into() })
    }
    fn ancestry(&self) -> String {
        self.ctx
            .iter()
            .rev()
            .take(4)
            .map(|c| format!("{}:{}", c.kind, c.detail))
            .collect::<Vec<_>>()
            .join(" < ")
    }
    fn raw_place(&self, e: &Expr) -> bool {
        match e {
            Expr::Paren(p) => self.raw_place(&p.expr),
            Expr::Field(f) => self.raw_place(&f.base),
            Expr::Index(i) => self.raw_place(&i.expr),
            Expr::Unary(u) if matches!(u.op, syn::UnOp::Deref(_)) => {
                matches!(self.infer(&u.expr).map(|t| self.resolve(&t)), Some(Type::Ptr(_))) || self.raw_place(&u.expr)
            }
            _ => false,
        }
    }
    fn param_kind(&self, callee: &str, idx: usize, method: bool) -> String {
        let s = if method { self.pick(self.g.methods.get(callee)) } else { self.pick(self.g.fns.get(callee)) };
        match s {
            Some(s) => match s.params.get(idx) {
                Some(t) => self.kind(t),
                None => "variadic-or-none".into(),
            },
            None => {
                let has = if method { self.g.methods.get(callee) } else { self.g.fns.get(callee) };
                match has {
                    Some(v) => {
                        // several same-named fns with different signatures: agree on the formal's kind or say so
                        let mut ks: Vec<String> = v
                            .iter()
                            .map(|s| s.params.get(idx).map(|t| self.kind(t)).unwrap_or_else(|| "none".into()))
                            .collect();
                        ks.sort();
                        ks.dedup();
                        if ks.len() == 1 {
                            ks[0].clone()
                        } else {
                            format!("ambiguous({})", ks.join("/"))
                        }
                    }
                    None => "unknown-callee".into(),
                }
            }
        }
    }
    fn visit_body_block(&mut self, b: &syn::Block) {
        self.env.push(HashMap::new());
        let n = b.stmts.len();
        for (i, s) in b.stmts.iter().enumerate() {
            match s {
                syn::Stmt::Local(l) => {
                    if let Some(init) = &l.init {
                        self.with(Ctx { kind: "let-init", detail: ts(&l.pat).chars().take(40).collect(), param: "-".into() }, |v| {
                            v.visit_expr(&init.expr)
                        });
                        if let Some((_, d)) = &init.diverge {
                            self.with(Ctx { kind: "other", detail: "let-else".into(), param: "-".into() }, |v| v.visit_expr(d));
                        }
                    }
                    self.visit_pat(&l.pat);
                    let t = l.init.as_ref().and_then(|i| self.infer(&i.expr));
                    self.bind_pat(&l.pat, t);
                }
                syn::Stmt::Expr(e, semi) => {
                    if semi.is_none() && i + 1 == n {
                        self.visit_expr(e); // tail inherits the block's context
                    } else {
                        self.with(Ctx { kind: "stmt", detail: "-".into(), param: "-".into() }, |v| v.visit_expr(e));
                    }
                }
                syn::Stmt::Item(it) => self.visit_item(it),
                syn::Stmt::Macro(m) => self.visit_macro(&m.mac),
            }
        }
        self.env.pop();
    }
    fn enter_fn(&mut self, name: String, sig: &syn::Signature, body: &syn::Block) {
        let key = match self.fns.last() {
            Some(o) => format!("{}::{}", o, name),
            None => name,
        };
        self.fns.push(key);
        let mut sc = HashMap::new();
        for a in &sig.inputs {
            match a {
                syn::FnArg::Typed(pt) => {
                    if let syn::Pat::Ident(pi) = &*pt.pat {
                        sc.insert(pi.ident.to_string(), Some((*pt.ty).clone()));
                    }
                }
                syn::FnArg::Receiver(r) => {
                    sc.insert("self".into(), Some((*r.ty).clone()));
                }
            }
        }
        self.visit_signature(sig);
        let saved_env = std::mem::replace(&mut self.env, vec![sc]);
        let saved_ctx = std::mem::take(&mut self.ctx);
        self.with(Ctx { kind: "fn-tail", detail: "-".into(), param: "-".into() }, |v| v.visit_body_block(body));
        self.ctx = saved_ctx;
        self.env = saved_env;
        self.fns.pop();
    }
    fn record_deref(&self, r: &syn::ExprReference, u: &syn::ExprUnary) {
        let form = if r.mutability.is_some() { "mut" } else { "shared" };
        let c = self.top();
        let t = self.infer(&u.expr);
        let (k, tstr) = match &t {
            Some(t) => (self.kind(t), ts(&self.resolve(t))),
            None => ("untyped".to_string(), "-".to_string()),
        };
        let txt = ts(&*u.expr);
        let opt = txt.contains("as_deref_mut") || txt.contains("as_mut ()") || txt.contains("as_deref ()");
        println!(
            "DEREF\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            self.side,
            self.prog,
            self.fnkey(),
            r.and_token.span.start().line,
            form,
            c.kind,
            c.detail,
            c.param,
            self.ancestry(),
            k,
            tstr.chars().take(80).collect::<String>(),
            self.raw_place(&u.expr),
            opt,
            txt.chars().take(100).collect::<String>()
        );
    }
}

impl<'a, 'ast> Visit<'ast> for V<'a> {
    fn visit_item_mod(&mut self, m: &'ast syn::ItemMod) {
        self.mods.push(m.ident.to_string());
        visit::visit_item_mod(self, m);
        self.mods.pop();
    }
    fn visit_item_fn(&mut self, f: &'ast syn::ItemFn) {
        self.enter_fn(f.sig.ident.to_string(), &f.sig, &f.block);
    }
    fn visit_item_impl(&mut self, i: &'ast syn::ItemImpl) {
        self.selfty.push((*i.self_ty).clone());
        let st = ts(&*i.self_ty);
        for it in &i.items {
            if let syn::ImplItem::Fn(f) = it {
                self.enter_fn(format!("{}::{}", st, f.sig.ident), &f.sig, &f.block);
            }
        }
        self.selfty.pop();
    }
    fn visit_type_reference(&mut self, t: &'ast syn::TypeReference) {
        if let Type::Ptr(_) = &*t.elem {
            let form = if t.mutability.is_some() { "mut" } else { "shared" };
            println!("TYPE\t{}\t{}\t{}\t{}\t{}\t-\t-\t-\t-\t-\t-\t-\t-\t{}", self.side, self.prog, self.fnkey(), t.and_token.span.start().line, form, ts(t));
        }
        visit::visit_type_reference(self, t);
    }
    fn visit_macro(&mut self, m: &'ast syn::Macro) {
        let mut stack = vec![m.tokens.clone()];
        while let Some(s) = stack.pop() {
            let toks: Vec<proc_macro2::TokenTree> = s.into_iter().collect();
            for i in 0..toks.len() {
                if let proc_macro2::TokenTree::Group(g) = &toks[i] {
                    stack.push(g.stream());
                }
                if let proc_macro2::TokenTree::Punct(p) = &toks[i] {
                    if p.as_char() == '&' {
                        let is_mut = matches!(toks.get(i + 1), Some(proc_macro2::TokenTree::Ident(id)) if id == "mut");
                        let star_at = if is_mut { i + 2 } else { i + 1 };
                        if matches!(toks.get(star_at), Some(proc_macro2::TokenTree::Punct(q)) if q.as_char() == '*') {
                            println!(
                                "MACRO\t{}\t{}\t{}\t{}\t{}\t-\t-\t-\t-\t-\t-\t-\t-\t{}",
                                self.side,
                                self.prog,
                                self.fnkey(),
                                p.span().start().line,
                                if is_mut { "mut" } else { "shared" },
                                last_ident(&m.path)
                            );
                        }
                    }
                }
            }
        }
    }
    fn visit_expr(&mut self, e: &'ast Expr) {
        let o = |d: &str| Ctx { kind: "other", detail: d.to_string(), param: "-".into() };
        match e {
            Expr::Reference(r) => {
                if let Expr::Unary(u) = &*r.expr {
                    if matches!(u.op, syn::UnOp::Deref(_)) {
                        self.record_deref(r, u);
                    }
                }
                self.with(o("ref-operand"), |v| v.visit_expr(&r.expr));
            }
            Expr::MethodCall(m) => {
                let n = m.method.to_string();
                if n == "as_deref_mut" || n == "as_deref" || n == "as_mut" || n == "as_ref" {
                    let c = self.top();
                    let t = self.infer(&m.receiver);
                    let (k, tstr) = match &t {
                        Some(t) => (self.kind(t), ts(&self.resolve(t))),
                        None => ("untyped".to_string(), "-".to_string()),
                    };
                    println!(
                        "VIEW\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t-\t-\t{}",
                        self.side,
                        self.prog,
                        self.fnkey(),
                        m.method.span().start().line,
                        n,
                        c.kind,
                        c.detail,
                        c.param,
                        self.ancestry(),
                        k,
                        tstr.chars().take(80).collect::<String>(),
                        ts(&*m.receiver).chars().take(100).collect::<String>()
                    );
                }
                self.with(Ctx { kind: "method-recv", detail: n.clone(), param: "-".into() }, |v| v.visit_expr(&m.receiver));
                for (i, a) in m.args.iter().enumerate() {
                    let pk = self.param_kind(&n, i, true);
                    self.with(Ctx { kind: "method-arg", detail: format!("{}#{}", n, i), param: pk }, |v| v.visit_expr(a));
                }
            }
            Expr::Call(c) => {
                let callee = if let Expr::Path(p) = &*c.func { Some(last_ident(&p.path)) } else { None };
                self.with(o("callee"), |v| v.visit_expr(&c.func));
                let name = callee.clone().unwrap_or_else(|| "<expr>".into());
                let assoc = if let Expr::Path(p) = &*c.func { p.path.segments.len() >= 2 && self.g.methods.contains_key(&name) && !self.g.fns.contains_key(&name) } else { false };
                for (i, a) in c.args.iter().enumerate() {
                    let pk = if callee.is_some() { self.param_kind(&name, i, assoc) } else { "fnptr-call".into() };
                    self.with(Ctx { kind: "call-arg", detail: format!("{}#{}", name, i), param: pk }, |v| v.visit_expr(a));
                }
            }
            Expr::Cast(c) => {
                self.with(Ctx { kind: "cast", detail: ts(&*c.ty), param: "-".into() }, |v| v.visit_expr(&c.expr));
                self.visit_type(&c.ty);
            }
            Expr::Return(r) => {
                if let Some(x) = &r.expr {
                    self.with(Ctx { kind: "return", detail: "-".into(), param: "-".into() }, |v| v.visit_expr(x));
                }
            }
            Expr::Assign(a) => {
                self.with(Ctx { kind: "assign-lhs", detail: "-".into(), param: "-".into() }, |v| v.visit_expr(&a.left));
                let d = ts(&*a.left).chars().take(40).collect::<String>();
                self.with(Ctx { kind: "assign-rhs", detail: d, param: "-".into() }, |v| v.visit_expr(&a.right));
            }
            Expr::Struct(s) => {
                for f in &s.fields {
                    let d = match &f.member {
                        syn::Member::Named(i) => i.to_string(),
                        syn::Member::Unnamed(i) => i.index.to_string(),
                    };
                    self.with(Ctx { kind: "struct-field", detail: d, param: "-".into() }, |v| v.visit_expr(&f.expr));
                }
                if let Some(r) = &s.rest {
                    self.with(o("struct-rest"), |v| v.visit_expr(r));
                }
            }
            Expr::Paren(p) => self.visit_expr(&p.expr),
            Expr::Group(p) => self.visit_expr(&p.expr),
            Expr::Block(b) => self.visit_body_block(&b.block),
            Expr::Unsafe(b) => self.visit_body_block(&b.block),
            Expr::If(i) => {
                self.env.push(HashMap::new());
                self.with(o("if-cond"), |v| v.visit_expr(&i.cond));
                self.visit_body_block(&i.then_branch);
                self.env.pop();
                if let Some((_, el)) = &i.else_branch {
                    self.visit_expr(el);
                }
            }
            Expr::Let(l) => {
                self.with(o("let-scrutinee"), |v| v.visit_expr(&l.expr));
                let t = self.infer(&l.expr);
                self.bind_pat(&l.pat, t);
            }
            Expr::Match(m) => {
                self.with(o("match-scrutinee"), |v| v.visit_expr(&m.expr));
                let t = self.infer(&m.expr);
                for arm in &m.arms {
                    self.env.push(HashMap::new());
                    self.bind_pat(&arm.pat, t.clone());
                    if let Some((_, g)) = &arm.guard {
                        self.with(o("match-guard"), |v| v.visit_expr(g));
                    }
                    self.visit_expr(&arm.body);
                    self.env.pop();
                }
            }
            Expr::While(w) => {
                self.env.push(HashMap::new());
                self.with(o("while-cond"), |v| v.visit_expr(&w.cond));
                self.with(o("loop-body"), |v| v.visit_body_block(&w.body));
                self.env.pop();
            }
            Expr::Loop(l) => self.with(o("loop-body"), |v| v.visit_body_block(&l.body)),
            Expr::ForLoop(f) => {
                self.with(o("for-iter"), |v| v.visit_expr(&f.expr));
                self.env.push(HashMap::new());
                self.bind_pat(&f.pat, None);
                self.with(o("loop-body"), |v| v.visit_body_block(&f.body));
                self.env.pop();
            }
            Expr::Closure(c) => {
                self.env.push(HashMap::new());
                for p in &c.inputs {
                    self.visit_pat(p);
                    self.bind_pat(p, None);
                }
                self.with(Ctx { kind: "closure-tail", detail: "-".into(), param: "-".into() }, |v| v.visit_expr(&c.body));
                self.env.pop();
            }
            Expr::Macro(m) => self.visit_macro(&m.mac),
            _ => {
                let kind = match e {
                    Expr::Binary(_) => "binary",
                    Expr::Unary(_) => "unary",
                    Expr::Field(_) => "field-base",
                    Expr::Index(_) => "index",
                    Expr::Array(_) => "array-elem",
                    Expr::Tuple(_) => "tuple-elem",
                    Expr::Break(_) => "break",
                    Expr::Range(_) => "range",
                    Expr::Repeat(_) => "repeat",
                    _ => "misc",
                };
                self.with(o(kind), |v| visit::visit_expr(v, e));
            }
        }
    }
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
    let mut g = Globals::default();
    Collect { g: &mut g, selfty: vec![], mods: vec![] }.visit_file(&ast);
    let mut v = V { g: &g, side, prog, fns: vec![], selfty: vec![], env: vec![HashMap::new()], ctx: vec![], mods: vec![] };
    v.visit_file(&ast);
}
