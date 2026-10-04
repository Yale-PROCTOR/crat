//! **R801-2 (USER) — premise P7 `BridgedArgumentDereferenceable`, extended to the
//! declaration-site references (main 163, relay 270).** A census instrument: no
//! model fact, no emitted byte. It reads the FINAL emitted tree beside its input
//! and writes one row for each reference the code generator made from a raw
//! pointer where the input does not dereference that pointer right after —
//! rule (b) of R791-4 as wave-6l built it (`a902485a9`): the site rests on P7 and
//! is receipted, not held. Where (b) holds, P1 covers the site and no row is
//! written.
//!
//! The site kinds:
//! - `declaration-construction`: `let x: &[T] = from_raw_parts(p, n)`;
//! - `declaration-reborrow`: `let x: &T = &*p` / `&mut *p`;
//! - `declaration-view`: `let x = p.as_mut()` / `p.as_ref()`;
//!
//!   each where the input declares `x` a raw pointer (or `x` is the input's raw
//!   formal, re-bound by the generator); and
//! - `call-bridge`: a delivered thin `Ref` formal that its callers bridge from a
//!   raw pointer (a placed `c-raw-reborrow-{mut,shared}` adapter, R758-1 (β)),
//!   read at the callee's entry.
//!
//! Only the final tree counts: a site the verify rounds reverted keeps the
//! input's raw declaration and has no reference to receipt. The exposure
//! wrappers (`ti_*` handing whole views to `__crat_safe_ti_*`) hold (b) by their
//! shape and are counted apart. The `quiet_prefix` column is the dominance
//! reading the seat may prefer: a dereference reached before any call or exit.

use std::collections::{BTreeMap, BTreeSet};

use quote::ToTokens;
use syn::{BinOp, Block, Expr, FnArg, Item, ItemFn, Local, Pat, Stmt, Type, UnOp, visit::Visit};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum SiteKind {
    CallBridge,
    DeclarationView,
    DeclarationConstruction,
    DeclarationReborrow,
}

impl SiteKind {
    pub(crate) const ALL: [SiteKind; 4] = [
        SiteKind::CallBridge,
        SiteKind::DeclarationView,
        SiteKind::DeclarationConstruction,
        SiteKind::DeclarationReborrow,
    ];

    pub(crate) fn key(self) -> &'static str {
        match self {
            SiteKind::CallBridge => "call-bridge",
            SiteKind::DeclarationView => "declaration-view",
            SiteKind::DeclarationConstruction => "declaration-construction",
            SiteKind::DeclarationReborrow => "declaration-reborrow",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Row {
    pub(crate) kind: SiteKind,
    pub(crate) function: String,
    pub(crate) binding: String,
    pub(crate) ordinal: usize,
    pub(crate) pointer: String,
    /// The call site of a `call-bridge` row (`caller@site`); `-` at a declaration.
    pub(crate) site: String,
    /// Why (b) fails.
    pub(crate) rule_b: String,
    /// Whether the dominance reading clears it: the input dereferences the
    /// pointer before any call or exit.
    pub(crate) quiet_prefix: bool,
}

#[derive(Debug, Default, PartialEq, Eq)]
pub(crate) struct Reading {
    pub(crate) rows: Vec<Row>,
    /// Sites where (b) holds: P1 covers them, no row.
    pub(crate) held_b: BTreeMap<SiteKind, usize>,
    /// Constructions inside an exposure wrapper: (b) by the family's shape.
    pub(crate) exempt_exposure: usize,
    /// Constructions over a string literal: static storage nothing releases.
    pub(crate) exempt_literal: usize,
    /// References from raw pointers with no input binding to read (b) on.
    pub(crate) unread: usize,
    /// Distinct `call-bridge` formals behind the rows.
    pub(crate) call_bridge_formals: usize,
}

/// One placed raw-to-reference adapter at a call (the census's `adapters` row).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BridgedCall {
    pub(crate) callee: String,
    pub(crate) formal: usize,
    pub(crate) caller: String,
    pub(crate) site: String,
}

const SAFE_TWIN: &str = "__crat_safe_";

fn functions(file: &syn::File) -> BTreeMap<String, &ItemFn> {
    fn walk<'a>(items: &'a [Item], prefix: &str, out: &mut BTreeMap<String, &'a ItemFn>) {
        for item in items {
            match item {
                Item::Fn(function) => {
                    out.insert(format!("{prefix}{}", function.sig.ident), function);
                }
                Item::Mod(module) => {
                    if let Some((_, items)) = &module.content {
                        walk(items, &format!("{prefix}{}::", module.ident), out);
                    }
                }
                _ => {}
            }
        }
    }
    let mut out = BTreeMap::new();
    walk(&file.items, "", &mut out);
    out
}

fn function_names(file: &syn::File) -> BTreeSet<String> {
    functions(file)
        .keys()
        .map(|path| path.rsplit("::").next().unwrap_or(path).to_owned())
        .collect()
}

fn binding_of(pat: &Pat) -> Option<(&syn::Ident, Option<&Type>)> {
    match pat {
        Pat::Ident(ident) => Some((&ident.ident, None)),
        Pat::Type(typed) => match &*typed.pat {
            Pat::Ident(ident) => Some((&ident.ident, Some(&*typed.ty))),
            _ => None,
        },
        _ => None,
    }
}

/// Every `let` of a single binding, in source order, with the items of its
/// block after it.
struct Lets<'a> {
    found: Vec<(String, &'a Local, &'a [Stmt])>,
}

impl<'a> Visit<'a> for Lets<'a> {
    fn visit_block(&mut self, block: &'a Block) {
        for (position, stmt) in block.stmts.iter().enumerate() {
            if let Stmt::Local(local) = stmt
                && let Some((ident, _)) = binding_of(&local.pat)
            {
                self.found
                    .push((ident.to_string(), local, &block.stmts[position + 1..]));
            }
            self.visit_stmt(stmt);
        }
    }
}

fn lets(function: &ItemFn) -> Vec<(String, &Local, &[Stmt])> {
    let mut lets = Lets { found: Vec::new() };
    lets.visit_block(&function.block);
    lets.found
}

fn peel(mut expr: &Expr) -> &Expr {
    loop {
        expr = match expr {
            Expr::Paren(inner) => &inner.expr,
            Expr::Group(inner) => &inner.expr,
            _ => return expr,
        };
    }
}

fn is_the_local(expr: &Expr, name: &str) -> bool {
    matches!(peel(expr), Expr::Path(path)
        if path.qself.is_none() && path.path.is_ident(name))
}

/// `x`, or pointer arithmetic / a cast rooted at `x`.
fn rooted_at(expr: &Expr, name: &str) -> bool {
    match peel(expr) {
        Expr::MethodCall(call)
            if matches!(
                call.method.to_string().as_str(),
                "offset"
                    | "add"
                    | "sub"
                    | "wrapping_offset"
                    | "wrapping_add"
                    | "wrapping_sub"
                    | "cast"
                    | "cast_mut"
                    | "cast_const"
            ) =>
        {
            rooted_at(&call.receiver, name)
        }
        Expr::Cast(cast) => rooted_at(&cast.expr, name),
        other => is_the_local(other, name),
    }
}

fn is_null_test(expr: &Expr, name: &str) -> bool {
    matches!(peel(expr), Expr::MethodCall(call)
        if call.method == "is_null" && call.args.is_empty() && is_the_local(&call.receiver, name))
}

fn local_callee(expr: &Expr, local_fns: &BTreeSet<String>) -> bool {
    matches!(peel(expr), Expr::Path(path)
        if path.path.segments.last().is_some_and(|segment| local_fns.contains(&segment.ident.to_string())))
}

/// Whether `expr` can leave its block (`return`, `break`, `continue`, `?`).
fn may_exit(expr: &Expr) -> bool {
    struct Exits(bool);
    impl<'a> Visit<'a> for Exits {
        fn visit_expr(&mut self, expr: &'a Expr) {
            match expr {
                Expr::Return(_) | Expr::Break(_) | Expr::Continue(_) | Expr::Try(_) => {
                    self.0 = true
                }
                Expr::Closure(_) => {}
                _ => syn::visit::visit_expr(self, expr),
            }
        }
    }
    let mut exits = Exits(false);
    exits.visit_expr(expr);
    exits.0
}

/// A block that never falls through: its last item leaves.
fn diverges(block: &Block) -> bool {
    block.stmts.last().is_some_and(|stmt| {
        matches!(stmt, Stmt::Expr(expr, _)
            if matches!(peel(expr), Expr::Return(_) | Expr::Break(_) | Expr::Continue(_)))
    })
}

/// The item a block evaluates: a `let`'s initializer or an expression; a macro
/// statement is opaque (`None` in the vector, kept so it occupies its place).
fn items(stmts: &[Stmt]) -> Vec<Option<&Expr>> {
    stmts
        .iter()
        .filter_map(|stmt| match stmt {
            Stmt::Local(local) => Some(local.init.as_ref().map(|init| &*init.expr)),
            Stmt::Expr(expr, _) => Some(Some(expr)),
            Stmt::Macro(_) => Some(None),
            Stmt::Item(_) => None,
        })
        .collect()
}

/// **R791-4 (b): a dereference of `name` that `expr` evaluates on EVERY path
/// through it** — not under an `if` / `match` arm, the right side of `&&` /
/// `||`, a loop body or a closure, and not after an item that may leave. A
/// whole-argument hand-off to a local callee counts (R785). The conditions of
/// `while` and the iterator of `for` are evaluated, so they count.
struct Unconditional<'n> {
    name: &'n str,
    local_fns: &'n BTreeSet<String>,
    found: bool,
    stopped: bool,
}

impl<'a> Visit<'a> for Unconditional<'_> {
    fn visit_expr(&mut self, expr: &'a Expr) {
        if self.found || self.stopped {
            return;
        }
        match expr {
            Expr::Unary(unary)
                if matches!(unary.op, UnOp::Deref(_)) && rooted_at(&unary.expr, self.name) =>
            {
                self.found = true
            }
            Expr::Call(call)
                if local_callee(&call.func, self.local_fns)
                    && call.args.iter().any(|arg| is_the_local(arg, self.name)) =>
            {
                self.found = true
            }
            Expr::If(branch) => self.visit_expr(&branch.cond),
            Expr::Match(choice) => self.visit_expr(&choice.expr),
            Expr::Binary(binary) if matches!(binary.op, BinOp::And(_) | BinOp::Or(_)) => {
                self.visit_expr(&binary.left)
            }
            Expr::While(lp) => self.visit_expr(&lp.cond),
            Expr::ForLoop(lp) => self.visit_expr(&lp.expr),
            Expr::Loop(_) | Expr::Closure(_) => {}
            Expr::Block(block) => self.walk_block(&block.block),
            Expr::Unsafe(block) => self.walk_block(&block.block),
            _ => syn::visit::visit_expr(self, expr),
        }
    }
}

impl Unconditional<'_> {
    fn walk_block(&mut self, block: &Block) {
        for item in items(&block.stmts) {
            let Some(item) = item else {
                self.stopped = true;
                return;
            };
            self.visit_expr(item);
            if self.found || may_exit(item) {
                self.stopped = !self.found;
                return;
            }
        }
    }
}

fn block_dereferences(block: &Block, name: &str, local_fns: &BTreeSet<String>) -> bool {
    let mut walk = Unconditional {
        name,
        local_fns,
        found: false,
        stopped: false,
    };
    walk.walk_block(block);
    walk.found
}

fn dereferences_unconditionally(expr: &Expr, name: &str, local_fns: &BTreeSet<String>) -> bool {
    let mut walk = Unconditional {
        name,
        local_fns,
        found: false,
        stopped: false,
    };
    walk.visit_expr(expr);
    walk.found
}

/// R791-4 (b) on the items after the declaration. `Ok` names the shape that
/// holds; `Err` names why it fails.
fn rule_b(
    after: &[Option<&Expr>],
    name: &str,
    local_fns: &BTreeSet<String>,
) -> Result<&'static str, String> {
    let Some(first) = after.first() else {
        return Err("no item after the declaration".to_owned());
    };
    let Some(first) = first else {
        return Err("the next item is a macro".to_owned());
    };
    if dereferences_unconditionally(first, name, local_fns) {
        return Ok("the next item dereferences");
    }
    // The early-exiting null test, then a dereference.
    if let Expr::If(branch) = peel(first)
        && branch.else_branch.is_none()
        && is_null_test(&branch.cond, name)
    {
        if !diverges(&branch.then_branch) {
            return Err("a null test without an early exit".to_owned());
        }
        return match after.get(1) {
            Some(Some(next)) if dereferences_unconditionally(next, name, local_fns) => {
                Ok("an early-exit null test, then a dereference")
            }
            _ => Err("an early-exit null test, then no dereference".to_owned()),
        };
    }
    // An unconditionally evaluated `if` on the null test whose non-null arm
    // dereferences.
    struct GuardedIf<'n> {
        name: &'n str,
        local_fns: &'n BTreeSet<String>,
        verdict: Option<bool>,
    }
    impl<'a> Visit<'a> for GuardedIf<'_> {
        fn visit_expr(&mut self, expr: &'a Expr) {
            if self.verdict.is_some() {
                return;
            }
            match expr {
                Expr::If(branch) => {
                    let cond = peel(&branch.cond);
                    let non_null: Option<&Expr> = if is_null_test(cond, self.name) {
                        branch.else_branch.as_ref().map(|(_, arm)| &**arm)
                    } else if let Expr::Unary(unary) = cond
                        && matches!(unary.op, UnOp::Not(_))
                        && is_null_test(&unary.expr, self.name)
                    {
                        self.verdict = Some(block_dereferences(
                            &branch.then_branch,
                            self.name,
                            self.local_fns,
                        ));
                        return;
                    } else {
                        self.visit_expr(cond);
                        return;
                    };
                    self.verdict = Some(non_null.is_some_and(|arm| {
                        dereferences_unconditionally(arm, self.name, self.local_fns)
                    }));
                }
                Expr::Match(choice) => self.visit_expr(&choice.expr),
                Expr::Binary(binary) if matches!(binary.op, BinOp::And(_) | BinOp::Or(_)) => {
                    self.visit_expr(&binary.left)
                }
                Expr::Loop(_) | Expr::While(_) | Expr::ForLoop(_) | Expr::Closure(_) => {}
                _ => syn::visit::visit_expr(self, expr),
            }
        }
    }
    let mut guarded = GuardedIf {
        name,
        local_fns,
        verdict: None,
    };
    guarded.visit_expr(first);
    match guarded.verdict {
        Some(true) => Ok("the non-null arm dereferences"),
        Some(false) => Err("the non-null arm does not dereference".to_owned()),
        None => Err(format!(
            "the next item: {}",
            first
                .to_token_stream()
                .to_string()
                .chars()
                .take(80)
                .collect::<String>()
        )),
    }
}

/// Calls the dominance reading treats as unable to release: pointer
/// arithmetic, null tests and integer arithmetic.
fn releases_nothing(method: &str) -> bool {
    method == "is_null"
        || method == "offset"
        || method == "offset_from"
        || method == "add"
        || method == "sub"
        || method == "cast"
        || method == "cast_mut"
        || method == "cast_const"
        || method.starts_with("wrapping_")
}

fn may_release(expr: &Expr) -> bool {
    struct Calls(bool);
    impl<'a> Visit<'a> for Calls {
        fn visit_expr(&mut self, expr: &'a Expr) {
            match expr {
                Expr::Call(_) | Expr::Macro(_) => self.0 = true,
                Expr::MethodCall(call) if !releases_nothing(&call.method.to_string()) => {
                    self.0 = true
                }
                Expr::Closure(_) => {}
                _ => syn::visit::visit_expr(self, expr),
            }
        }
    }
    let mut calls = Calls(false);
    calls.visit_expr(expr);
    calls.0
}

/// The dominance reading: a dereference reached before any call, exit, loop or
/// branch other than an early-exit null test.
fn quiet_prefix(after: &[Option<&Expr>], name: &str, local_fns: &BTreeSet<String>) -> bool {
    for item in after {
        let Some(item) = item else { return false };
        if dereferences_unconditionally(item, name, local_fns) {
            return true;
        }
        if let Expr::If(branch) = peel(item)
            && branch.else_branch.is_none()
            && is_null_test(&branch.cond, name)
            && diverges(&branch.then_branch)
        {
            continue;
        }
        if may_exit(item)
            || may_release(item)
            || matches!(
                peel(item),
                Expr::If(_) | Expr::Match(_) | Expr::Loop(_) | Expr::While(_) | Expr::ForLoop(_)
            )
        {
            return false;
        }
    }
    false
}

fn tokens(expr: &Expr) -> String {
    expr.to_token_stream().to_string()
}

/// The reference an emitted declaration makes from a raw pointer, if any.
fn reference_from_raw(init: &Expr) -> Option<(SiteKind, String)> {
    let init = peel(init);
    match init {
        Expr::Reference(reference) => match peel(&reference.expr) {
            // `&mut *outputs[0]` reborrows an element of an already-safe
            // slice: a raw pointer is never indexed.
            Expr::Unary(unary)
                if matches!(unary.op, UnOp::Deref(_))
                    && !matches!(peel(&unary.expr), Expr::Index(_)) =>
            {
                Some((SiteKind::DeclarationReborrow, tokens(&unary.expr)))
            }
            _ => None,
        },
        Expr::MethodCall(call)
            if (call.method == "as_mut" || call.method == "as_ref") && call.args.is_empty() =>
        {
            Some((SiteKind::DeclarationView, tokens(&call.receiver)))
        }
        Expr::MethodCall(call) if call.method == "unwrap" && call.args.is_empty() => {
            match peel(&call.receiver) {
                Expr::MethodCall(view)
                    if (view.method == "as_mut" || view.method == "as_ref")
                        && view.args.is_empty() =>
                {
                    Some((SiteKind::DeclarationView, tokens(&view.receiver)))
                }
                _ => None,
            }
        }
        _ => {
            struct Construction(Option<String>);
            impl<'a> Visit<'a> for Construction {
                fn visit_expr(&mut self, expr: &'a Expr) {
                    if self.0.is_some() {
                        return;
                    }
                    if let Expr::Call(call) = expr
                        && let Expr::Path(path) = peel(&call.func)
                        && path.path.segments.last().is_some_and(|segment| {
                            segment.ident == "from_raw_parts"
                                || segment.ident == "from_raw_parts_mut"
                        })
                    {
                        self.0 = Some(call.args.first().map(tokens).unwrap_or_default());
                        return;
                    }
                    syn::visit::visit_expr(self, expr);
                }
            }
            let mut construction = Construction(None);
            construction.visit_expr(init);
            construction
                .0
                .map(|pointer| (SiteKind::DeclarationConstruction, pointer))
        }
    }
}

fn is_raw_pointer(ty: &Type) -> bool {
    matches!(ty, Type::Ptr(_))
        || matches!(ty, Type::Paren(inner) if is_raw_pointer(&inner.elem))
        || matches!(ty, Type::Group(inner) if is_raw_pointer(&inner.elem))
}

fn calls_safe_twin(function: &ItemFn) -> bool {
    struct Twin<'n>(&'n str, bool);
    impl<'a> Visit<'a> for Twin<'_> {
        fn visit_expr_call(&mut self, call: &'a syn::ExprCall) {
            if let Expr::Path(path) = peel(&call.func)
                && path
                    .path
                    .segments
                    .last()
                    .is_some_and(|segment| segment.ident == self.0)
            {
                self.1 = true;
            }
            syn::visit::visit_expr_call(self, call);
        }
    }
    let name = format!("{SAFE_TWIN}{}", function.sig.ident);
    let mut twin = Twin(&name, false);
    twin.visit_block(&function.block);
    twin.1
}

fn raw_formal(function: &ItemFn, name: &str) -> bool {
    function.sig.inputs.iter().any(|input| {
        matches!(input, FnArg::Typed(typed)
            if matches!(binding_of(&typed.pat), Some((ident, _)) if ident == name)
                && is_raw_pointer(&typed.ty))
    })
}

fn formal_name(function: &ItemFn, index: usize) -> Option<(String, &Type)> {
    match function.sig.inputs.iter().nth(index)? {
        FnArg::Typed(typed) => {
            binding_of(&typed.pat).map(|(ident, _)| (ident.to_string(), &*typed.ty))
        }
        FnArg::Receiver(_) => None,
    }
}

/// A delivered thin reference formal: `&T`, `&mut T` or `Option<&..>`, not a slice.
fn is_thin_reference(ty: &Type) -> bool {
    match ty {
        Type::Reference(reference) => !matches!(&*reference.elem, Type::Slice(_)),
        Type::Path(path) => path.path.segments.last().is_some_and(|segment| {
            segment.ident == "Option"
                && matches!(&segment.arguments, syn::PathArguments::AngleBracketed(args)
                    if args.args.iter().any(|arg| matches!(arg,
                        syn::GenericArgument::Type(Type::Reference(inner))
                            if !matches!(&*inner.elem, Type::Slice(_)))))
        }),
        Type::Paren(inner) => is_thin_reference(&inner.elem),
        Type::Group(inner) => is_thin_reference(&inner.elem),
        _ => false,
    }
}

/// The reading of one program: its input and its final emitted tree, and the
/// census's placed raw-to-reference adapters.
pub(crate) fn read_program(
    input: &syn::File,
    emitted: &syn::File,
    bridged: &[BridgedCall],
) -> Reading {
    let mut reading = Reading::default();
    let inputs = functions(input);
    let local_fns = function_names(input);
    for (path, function) in functions(emitted) {
        let input_path = match path.rsplit_once("::") {
            Some((prefix, name)) => {
                format!("{prefix}::{}", name.strip_prefix(SAFE_TWIN).unwrap_or(name))
            }
            None => path.strip_prefix(SAFE_TWIN).unwrap_or(&path).to_owned(),
        };
        let wrapper = calls_safe_twin(function);
        let input_fn = inputs.get(&input_path).copied();
        let input_lets = input_fn.map(lets).unwrap_or_default();
        let mut ordinals = BTreeMap::<String, usize>::new();
        for (name, local, _) in lets(function) {
            let ordinal = {
                let next = ordinals.entry(name.clone()).or_default();
                *next += 1;
                *next
            };
            let Some(init) = &local.init else { continue };
            let Some((kind, pointer)) = reference_from_raw(&init.expr) else {
                continue;
            };
            if wrapper && kind == SiteKind::DeclarationConstruction {
                reading.exempt_exposure += 1;
                continue;
            }
            let declared = input_lets
                .iter()
                .filter(|(other, ..)| *other == name)
                .nth(ordinal - 1);
            let after = match (declared, input_fn) {
                (Some((_, declared, after)), _) => {
                    match binding_of(&declared.pat).and_then(|(_, ty)| ty) {
                        Some(ty) if is_raw_pointer(ty) => items(after),
                        // The input's binding is not a raw pointer: the
                        // reference is not one the generator made from one.
                        Some(_) => continue,
                        // No type written (`let mut buckets = (*s).buckets_;`):
                        // the input's initializer is the pointer itself unless
                        // it already makes the reference.
                        None => match &declared.init {
                            Some(init)
                                if matches!(peel(&init.expr), Expr::Reference(_))
                                    || reference_from_raw(&init.expr).is_some() =>
                            {
                                continue;
                            }
                            Some(_) => items(after),
                            None => {
                                reading.unread += 1;
                                continue;
                            }
                        },
                    }
                }
                (None, Some(input_fn)) if raw_formal(input_fn, &name) => {
                    items(&input_fn.block.stmts)
                }
                _ => {
                    reading.unread += 1;
                    continue;
                }
            };
            match rule_b(&after, &name, &local_fns) {
                Ok(_) => *reading.held_b.entry(kind).or_default() += 1,
                Err(why) => reading.rows.push(Row {
                    kind,
                    function: input_path.clone(),
                    binding: name.clone(),
                    ordinal,
                    pointer,
                    site: "-".to_owned(),
                    rule_b: why,
                    quiet_prefix: quiet_prefix(&after, &name, &local_fns),
                }),
            }
        }
    }
    let emitted_fns = functions(emitted);
    let mut formals = BTreeSet::new();
    for call in bridged {
        let Some(input_fn) = inputs.get(&call.callee) else {
            reading.unread += 1;
            continue;
        };
        let emitted_fn = call.callee.rsplit_once("::").map_or_else(
            || emitted_fns.get(&format!("{SAFE_TWIN}{}", call.callee)),
            |(prefix, name)| emitted_fns.get(&format!("{prefix}::{SAFE_TWIN}{name}")),
        );
        let Some(emitted_fn) = emitted_fn.or_else(|| emitted_fns.get(&call.callee)) else {
            continue;
        };
        let Some((_, delivered)) = formal_name(emitted_fn, call.formal) else {
            continue;
        };
        if !is_thin_reference(delivered) {
            continue;
        }
        let Some((name, _)) = formal_name(input_fn, call.formal) else {
            continue;
        };
        let after = items(&input_fn.block.stmts);
        match rule_b(&after, &name, &local_fns) {
            Ok(_) => *reading.held_b.entry(SiteKind::CallBridge).or_default() += 1,
            Err(why) => {
                formals.insert((call.callee.clone(), call.formal));
                reading.rows.push(Row {
                    kind: SiteKind::CallBridge,
                    function: call.callee.clone(),
                    binding: name.clone(),
                    ordinal: call.formal,
                    pointer: "-".to_owned(),
                    site: format!("{}@{}", call.caller, call.site),
                    rule_b: why,
                    quiet_prefix: quiet_prefix(&after, &name, &local_fns),
                });
            }
        }
    }
    reading.call_bridge_formals = formals.len();
    reading
}

/// The placed raw-to-reference adapters of a census `adapters` table.
pub(crate) fn bridged_calls(adapters_tsv: &str) -> Vec<BridgedCall> {
    let mut lines = adapters_tsv.lines();
    let Some(header) = lines.next() else {
        return Vec::new();
    };
    let column = |name: &str| header.split('\t').position(|column| column == name);
    let (Some(kind), Some(callee), Some(caller), Some(index), Some(template), Some(site)) = (
        column("kind"),
        column("owner_fn"),
        column("caller"),
        column("param_index"),
        column("template"),
        column("site"),
    ) else {
        return Vec::new();
    };
    lines
        .filter_map(|line| {
            let fields = line.split('\t').collect::<Vec<_>>();
            let get = |at: usize| fields.get(at).copied().unwrap_or("");
            (get(kind) == "placed"
                && matches!(
                    get(template),
                    "c-raw-reborrow-mut" | "c-raw-reborrow-shared"
                ))
            .then(|| {
                Some(BridgedCall {
                    callee: get(callee).to_owned(),
                    formal: get(index).parse().ok()?,
                    caller: get(caller).to_owned(),
                    site: get(site).to_owned(),
                })
            })
            .flatten()
        })
        .collect()
}

pub(crate) const HEADER: &str =
    "program\tpremise\tsite_kind\tfunction\tbinding\tordinal\tpointer\tsite\trule_b\tquiet_prefix";

pub(crate) fn render(program: &str, reading: &Reading) -> String {
    let mut out = format!("{HEADER}\n");
    for row in &reading.rows {
        out += &format!(
            "{program}\tbridge-dereferenceable\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\n",
            row.kind.key(),
            row.function,
            row.binding,
            row.ordinal,
            row.pointer.replace(['\t', '\n'], " "),
            row.site,
            row.rule_b.replace(['\t', '\n'], " "),
            if row.quiet_prefix { "clears" } else { "fails" },
        );
    }
    out
}

/// The census receipt's P7 lines over the programs read.
pub(crate) fn census_lines(readings: &[(&str, Result<Reading, String>)]) -> String {
    let mut kinds = BTreeMap::<SiteKind, usize>::new();
    let mut held_kinds = BTreeMap::<SiteKind, usize>::new();
    let (mut total, mut clears, mut held, mut exempt, mut unread, mut formals) = (0, 0, 0, 0, 0, 0);
    let mut by_program = Vec::new();
    let mut unreadable = Vec::new();
    for (program, reading) in readings {
        let reading = match reading {
            Ok(reading) => reading,
            Err(why) => {
                unreadable.push(format!("{program}:{why}"));
                continue;
            }
        };
        for row in &reading.rows {
            *kinds.entry(row.kind).or_default() += 1;
            clears += usize::from(row.quiet_prefix);
        }
        total += reading.rows.len();
        held += reading.held_b.values().sum::<usize>();
        for (kind, count) in &reading.held_b {
            *held_kinds.entry(*kind).or_default() += count;
        }
        exempt += reading.exempt_exposure;
        unread += reading.unread;
        formals += reading.call_bridge_formals;
        if !reading.rows.is_empty() {
            by_program.push(format!("{program}:{}", reading.rows.len()));
        }
    }
    let mut out = format!("premise_bridge_dereferenceable={total}\n");
    out += &format!(
        "premise_bridge_dereferenceable_kinds={}\n",
        SiteKind::ALL
            .iter()
            .map(|kind| format!("{}:{}", kind.key(), kinds.get(kind).copied().unwrap_or(0)))
            .collect::<Vec<_>>()
            .join(",")
    );
    out += &format!(
        "premise_bridge_dereferenceable_by_program={}\n",
        if by_program.is_empty() {
            "-".to_owned()
        } else {
            by_program.join(",")
        }
    );
    out += &format!("premise_bridge_dereferenceable_call_bridge_formals={formals}\n");
    out += &format!("premise_bridge_dereferenceable_quiet_prefix_clears={clears}\n");
    out += &format!("premise_bridge_dereferenceable_held_b={held}\n");
    out += &format!(
        "premise_bridge_dereferenceable_held_b_kinds={}\n",
        SiteKind::ALL
            .iter()
            .map(|kind| format!(
                "{}:{}",
                kind.key(),
                held_kinds.get(kind).copied().unwrap_or(0)
            ))
            .collect::<Vec<_>>()
            .join(",")
    );
    out += &format!("premise_bridge_dereferenceable_exempt_exposure={exempt}\n");
    out += &format!("premise_bridge_dereferenceable_unread={unread}\n");
    if !unreadable.is_empty() {
        out += &format!(
            "premise_bridge_dereferenceable_unreadable={}\n",
            unreadable.join(",")
        );
    }
    out
}

/// Read one program from disk and write its rows beside the census's tables.
pub(crate) fn read_and_write(
    program: &str,
    input_path: &std::path::Path,
    emitted_path: &std::path::Path,
    ledger_dir: &std::path::Path,
) -> Result<Reading, String> {
    let read =
        |path: &std::path::Path| std::fs::read_to_string(path).map_err(|_| "missing".to_owned());
    let input = syn::parse_file(&read(input_path)?).map_err(|_| "input-parse".to_owned())?;
    let emitted = syn::parse_file(&read(emitted_path)?).map_err(|_| "emitted-parse".to_owned())?;
    let adapters =
        std::fs::read_to_string(ledger_dir.join(format!("{program}.raw-boundary-adapters.tsv")))
            .unwrap_or_default();
    let reading = read_program(&input, &emitted, &bridged_calls(&adapters));
    std::fs::write(
        ledger_dir.join(format!(
            "{program}.raw-boundary-premise-bridge-dereferenceable.tsv"
        )),
        render(program, &reading),
    )
    .map_err(|_| "write".to_owned())?;
    Ok(reading)
}
