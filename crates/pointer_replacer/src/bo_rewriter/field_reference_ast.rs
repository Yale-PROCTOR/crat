//! wave-6f — the declaration half of a field transaction, as node transforms:
//! the struct item (generated lifetime parameter, borrowed field type), the
//! struct's trait impls (the same parameter on the header and on every
//! signature mention), and the storing functions' signatures (the generated
//! lifetime on the stored parameter and on every mention of the struct).
//!
//! Expression edits (stores, literals, loads, element reads) travel the
//! ordinary use-graft channel from [`super::decision::DecisionTable`]; this
//! pass owns only what that channel cannot express — items and signatures.
//!
//! Runs after `RefDeclVisitor`, so a stored parameter's declaration is already
//! a reference and the lifetime can be placed on it; a lifetime an E2 plan
//! already placed there is reused rather than duplicated.

use rustc_ast::{
    AngleBracketedArg, AngleBracketedArgs, GenericArg, GenericArgs, GenericParamKind, Ty, TyKind,
    mut_visit::MutVisitor, ptr::P,
};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::ty::TyCtxt;
use rustc_span::{Symbol, def_id::LocalDefId};

use super::{
    ast_transform::{
        AstCapture, Composition, DeclForm, RevertSet, ast_lifetime, decl_ty_kind_with_lifetime,
        generated_lifetime_param,
    },
    decision::{DecisionTable, field_reference::FieldTransaction, seam::Form},
};

/// A struct's converting field: index, declared form, the struct's lifetime.
struct StructPlan {
    /// The converting fields: index and declared form. A reference struct
    /// carries exactly one; an owned struct may carry several.
    fields: Vec<(usize, DeclForm)>,
    /// W6F-3: owned fields — no lifetime; the derived `Copy` / `Clone`
    /// impls become empty inherent impls (a `Box` field is not `Copy`).
    owning: bool,
    lifetime: String,
    name: Symbol,
}

fn decl_form(form: Form) -> Option<DeclForm> {
    match form {
        Form::Ref { .. } => Some(DeclForm::Ref),
        Form::Slice { .. } => Some(DeclForm::Slice),
        Form::Opt { slice, .. } => Some(DeclForm::Opt { slice }),
        Form::Raw | Form::Cursor { .. } | Form::NestedSlice { .. } => None,
    }
}

/// The first lifetime name not already declared among `taken`.
fn fresh_lifetime(taken: &FxHashSet<String>) -> String {
    for letter in 'a'..='z' {
        let candidate = format!("'{letter}");
        if !taken.contains(&candidate) {
            return candidate;
        }
    }
    "'crat_field".to_owned()
}

fn declared_lifetimes(generics: &rustc_ast::Generics) -> FxHashSet<String> {
    generics
        .params
        .iter()
        .filter(|param| matches!(param.kind, GenericParamKind::Lifetime))
        .map(|param| param.ident.to_string())
        .collect()
}

fn insert_lifetime_param(generics: &mut rustc_ast::Generics, name: &str) {
    let at = generics
        .params
        .iter()
        .position(|param| !matches!(param.kind, GenericParamKind::Lifetime))
        .unwrap_or(generics.params.len());
    generics
        .params
        .insert(at, generated_lifetime_param(name, std::iter::empty()));
}

/// Instantiate every bare path to `name` inside `ty` with `<'lifetime>`.
/// Returns how many paths were instantiated.
fn instantiate_struct_paths(ty: &mut Ty, name: Symbol, lifetime: &str) -> usize {
    match &mut ty.kind {
        TyKind::Path(None, path) => {
            let Some(last) = path.segments.last_mut() else { return 0 };
            if last.ident.name == name && last.args.is_none() {
                last.args = Some(P(GenericArgs::AngleBracketed(AngleBracketedArgs {
                    span: rustc_span::DUMMY_SP,
                    args: thin_vec::ThinVec::from_iter([AngleBracketedArg::Arg(
                        GenericArg::Lifetime(ast_lifetime(lifetime)),
                    )]),
                })));
                return 1;
            }
            let mut count = 0;
            if let Some(args) = &mut last.args
                && let GenericArgs::AngleBracketed(args) = &mut **args
            {
                for arg in &mut args.args {
                    if let AngleBracketedArg::Arg(GenericArg::Type(inner)) = arg {
                        count += instantiate_struct_paths(inner, name, lifetime);
                    }
                }
            }
            count
        }
        TyKind::Ptr(mut_ty) | TyKind::Ref(_, mut_ty) => {
            instantiate_struct_paths(&mut mut_ty.ty, name, lifetime)
        }
        TyKind::Slice(inner) | TyKind::Array(inner, _) | TyKind::Paren(inner) => {
            instantiate_struct_paths(inner, name, lifetime)
        }
        TyKind::Tup(items) => items
            .iter_mut()
            .map(|item| instantiate_struct_paths(item, name, lifetime))
            .sum(),
        _ => 0,
    }
}

/// The outermost reference layer of a placed declaration: `&T`, `&[T]`,
/// `Option<&T>`, `Option<&[T]>`.
fn outer_reference(ty: &mut Ty) -> Option<&mut Option<rustc_ast::Lifetime>> {
    match &mut ty.kind {
        TyKind::Ref(lifetime, _) => Some(lifetime),
        TyKind::Path(None, path) => {
            let last = path.segments.last_mut()?;
            if last.ident.name.as_str() != "Option" {
                return None;
            }
            let args = last.args.as_mut()?;
            let GenericArgs::AngleBracketed(args) = &mut **args else { return None };
            match args.args.iter_mut().next()? {
                AngleBracketedArg::Arg(GenericArg::Type(inner)) => outer_reference(inner),
                _ => None,
            }
        }
        _ => None,
    }
}

struct Apply<'a> {
    global_map: &'a rustc_ast::node_id::NodeMap<LocalDefId>,
    structs: &'a FxHashMap<LocalDefId, StructPlan>,
    impls: &'a FxHashMap<LocalDefId, LocalDefId>,
    /// fn → (struct, parameter positions that carry the lifetime)
    signatures: &'a FxHashMap<LocalDefId, (LocalDefId, Vec<usize>)>,
    guard: &'a mut Composition,
    placed_structs: FxHashSet<LocalDefId>,
    placed_impls: FxHashSet<LocalDefId>,
    placed_signatures: FxHashSet<LocalDefId>,
    failures: Vec<String>,
}

impl MutVisitor for Apply<'_> {
    fn visit_item(&mut self, item: &mut rustc_ast::Item) {
        if let Some(&did) = self.global_map.get(&item.id) {
            if let Some(plan) = self.structs.get(&did)
                && let rustc_ast::ItemKind::Struct(_, generics, variant) = &mut item.kind
            {
                let rustc_ast::VariantData::Struct { fields, .. } = variant else {
                    self.failures.push(format!("struct-shape:{did:?}"));
                    return;
                };
                if !self.guard.claim(item.id, item.span, "field:struct") {
                    self.failures.push(format!("struct-claim-refused:{did:?}"));
                    return;
                }
                for &(field_index, form) in &plan.fields {
                    let Some(field) = fields.get_mut(field_index) else {
                        self.failures.push(format!("field-index:{did:?}"));
                        return;
                    };
                    let TyKind::Ptr(inner) = &field.ty.kind else {
                        self.failures.push(format!("field-not-raw:{did:?}"));
                        return;
                    };
                    let pointee = inner.ty.clone();
                    field.ty.kind = decl_ty_kind_with_lifetime(
                        form,
                        false,
                        pointee,
                        (!plan.owning).then_some(plan.lifetime.as_str()),
                    );
                }
                if !plan.owning {
                    insert_lifetime_param(generics, &plan.lifetime);
                }
                self.placed_structs.insert(did);
            } else if let Some(struct_did) = self.impls.get(&did)
                && let Some(plan) = self.structs.get(struct_did)
                && let rustc_ast::ItemKind::Impl(im) = &mut item.kind
            {
                if !self.guard.claim(item.id, item.span, "field:impl") {
                    self.failures.push(format!("impl-claim-refused:{did:?}"));
                    return;
                }
                if plan.owning {
                    // A derived `Copy` / `Clone` cannot hold a `Box` field:
                    // the impl becomes an empty inherent impl — the item keeps
                    // its span (and so its reprint), the trait is gone.
                    im.of_trait = None;
                    im.items.clear();
                    self.placed_impls.insert(did);
                    rustc_ast::mut_visit::walk_item(self, item);
                    return;
                }
                insert_lifetime_param(&mut im.generics, &plan.lifetime);
                instantiate_struct_paths(&mut im.self_ty, plan.name, &plan.lifetime);
                for assoc in &mut im.items {
                    if let rustc_ast::AssocItemKind::Fn(function) = &mut assoc.kind {
                        for input in &mut function.sig.decl.inputs {
                            instantiate_struct_paths(&mut input.ty, plan.name, &plan.lifetime);
                        }
                        if let rustc_ast::FnRetTy::Ty(output) = &mut function.sig.decl.output {
                            instantiate_struct_paths(output, plan.name, &plan.lifetime);
                        }
                    }
                }
                self.placed_impls.insert(did);
            } else if let Some((struct_did, params)) = self.signatures.get(&did)
                && let Some(plan) = self.structs.get(struct_did)
                && let rustc_ast::ItemKind::Fn(function) = &mut item.kind
            {
                // The lifetime: reuse one an earlier plan placed on a stored
                // parameter, else generate the first free name.
                let mut existing = None;
                for &index in params {
                    if let Some(input) = function.sig.decl.inputs.get_mut(index)
                        && let Some(Some(lifetime)) = outer_reference(&mut input.ty)
                    {
                        existing = Some(lifetime.ident.to_string());
                    }
                }
                let lifetime = match existing {
                    Some(name) => name,
                    None => {
                        let name = fresh_lifetime(&declared_lifetimes(&function.generics));
                        insert_lifetime_param(&mut function.generics, &name);
                        name
                    }
                };
                if !self.guard.claim(item.id, item.span, "field:signature") {
                    self.failures
                        .push(format!("signature-claim-refused:{did:?}"));
                    return;
                }
                for &index in params {
                    let Some(input) = function.sig.decl.inputs.get_mut(index) else {
                        self.failures
                            .push(format!("signature-param-index:{did:?}:{index}"));
                        return;
                    };
                    let Some(slot) = outer_reference(&mut input.ty) else {
                        self.failures
                            .push(format!("signature-param-not-borrowed:{did:?}:{index}"));
                        return;
                    };
                    if slot.is_none() {
                        *slot = Some(ast_lifetime(&lifetime));
                    }
                }
                let mut mentions = 0;
                for input in &mut function.sig.decl.inputs {
                    mentions += instantiate_struct_paths(&mut input.ty, plan.name, &lifetime);
                }
                if let rustc_ast::FnRetTy::Ty(output) = &mut function.sig.decl.output {
                    mentions += instantiate_struct_paths(output, plan.name, &lifetime);
                }
                if mentions == 0 {
                    self.failures
                        .push(format!("signature-mentions-none:{did:?}"));
                    return;
                }
                self.placed_signatures.insert(did);
            }
        }
        rustc_ast::mut_visit::walk_item(self, item);
    }
}

pub(super) fn apply(
    tcx: TyCtxt<'_>,
    capture: &AstCapture,
    table: &DecisionTable,
    reverts: &RevertSet,
    krate: &mut rustc_ast::Crate,
    guard: &mut Composition,
) -> Result<(), String> {
    let active: Vec<&FieldTransaction> = table.field_transactions.active(&reverts.fns).collect();
    if active.is_empty() {
        return Ok(());
    }
    let mut structs: FxHashMap<LocalDefId, StructPlan> = FxHashMap::default();
    let mut impls: FxHashMap<LocalDefId, LocalDefId> = FxHashMap::default();
    let mut signatures: FxHashMap<LocalDefId, (LocalDefId, Vec<usize>)> = FxHashMap::default();
    // G: array locals retype their declaration; no struct, impl or signature.
    let arrays: FxHashMap<(LocalDefId, rustc_hir::HirId), String> = active
        .iter()
        .filter_map(|t| {
            t.array.as_ref().map(|a| {
                (
                    (a.owner, a.binding),
                    if a.owning {
                        // G build 3: every element owns its allocation.
                        format!("[Option<Box<[{}]>>; {}]", a.pointee, a.len)
                    } else {
                        format!("[Option<&{}>; {}]", a.pointee, a.len)
                    },
                )
            })
        })
        .collect();
    if !arrays.is_empty() {
        let mut retype = ArrayLocalRetype {
            local_map: &capture.map.local_map,
            global_map: &capture.map.global_map,
            arrays: &arrays,
            current_fn: None,
            guard,
            placed: 0,
            failures: Vec::new(),
        };
        retype.visit_crate(krate);
        if !retype.failures.is_empty() {
            return Err(format!(
                "field-transaction-ast:array-local:{}",
                retype.failures.join(";")
            ));
        }
        if retype.placed != arrays.len() {
            return Err(format!(
                "field-transaction-ast:array-local:unplaced {}/{}",
                retype.placed,
                arrays.len()
            ));
        }
    }
    for transaction in active.iter().filter(|t| t.array.is_none()) {
        let struct_did = transaction.key.struct_did;
        let form = if transaction.owning {
            DeclForm::Box {
                slice: matches!(
                    transaction.form,
                    Form::Slice { .. } | Form::Opt { slice: true, .. }
                ),
                optional: true,
                pointee_override: None,
            }
        } else {
            let Some(form) = decl_form(transaction.form) else {
                return Err(format!(
                    "field-transaction-ast:form-unrenderable:{}",
                    transaction.struct_path
                ));
            };
            form
        };
        match structs.get_mut(&struct_did) {
            // Several fields of one struct: owned ones carry no lifetime,
            // reference ones share the struct's single generated lifetime.
            Some(plan) if plan.owning == transaction.owning => {
                plan.fields.push((transaction.key.field_index, form));
            }
            Some(_) => {
                return Err(format!(
                    "field-transaction-ast:mixed-owning-and-reference:{}",
                    transaction.struct_path
                ));
            }
            None => {
                structs.insert(
                    struct_did,
                    StructPlan {
                        fields: vec![(transaction.key.field_index, form)],
                        owning: transaction.owning,
                        lifetime: "'a".to_owned(),
                        name: tcx.item_name(struct_did.to_def_id()),
                    },
                );
            }
        }
        for im in &transaction.impls {
            impls.insert(*im, struct_did);
        }
        for plan in &transaction.signature_plans {
            let mut indices = Vec::new();
            for (owner, hir_id) in &plan.lifetime_params {
                let Some((subject, _)) = table
                    .entries
                    .iter()
                    .find(|(s, _)| s.fn_did == *owner && s.hir_id == *hir_id)
                else {
                    return Err("field-transaction-ast:stored-parameter-missing".to_owned());
                };
                let super::decision::SubjectKind::Param { hir_index } = subject.kind else {
                    return Err("field-transaction-ast:stored-source-not-a-parameter".to_owned());
                };
                indices.push(hir_index);
            }
            // A second field of the same struct stored by the same signature
            // adds its positions to the one plan.
            let entry = signatures
                .entry(plan.owner)
                .or_insert_with(|| (struct_did, Vec::new()));
            if entry.0 != struct_did {
                return Err(format!(
                    "field-transaction-ast:two-struct-signature:{}",
                    transaction.struct_path
                ));
            }
            for index in indices {
                if !entry.1.contains(&index) {
                    entry.1.push(index);
                }
            }
        }
    }
    let mut apply = Apply {
        global_map: &capture.map.global_map,
        structs: &structs,
        impls: &impls,
        signatures: &signatures,
        guard,
        placed_structs: FxHashSet::default(),
        placed_impls: FxHashSet::default(),
        placed_signatures: FxHashSet::default(),
        failures: Vec::new(),
    };
    apply.visit_crate(krate);
    if !apply.failures.is_empty() {
        return Err(format!(
            "field-transaction-ast:{}",
            apply.failures.join(";")
        ));
    }
    if apply.placed_structs.len() != structs.len()
        || apply.placed_impls.len() != impls.len()
        || apply.placed_signatures.len() != signatures.len()
    {
        return Err(format!(
            "field-transaction-ast:unplaced: structs {}/{} impls {}/{} signatures {}/{}",
            apply.placed_structs.len(),
            structs.len(),
            apply.placed_impls.len(),
            impls.len(),
            apply.placed_signatures.len(),
            signatures.len()
        ));
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// W6F-3: owned-field wraps
// ---------------------------------------------------------------------------

/// Replaces the one `__crat_inner` path in a parsed wrap template with the
/// wrapped node's current expression.
struct Substitute {
    inner: Option<rustc_ast::ExprKind>,
    place: Option<rustc_ast::ExprKind>,
    substituted: usize,
    placed: usize,
}

impl MutVisitor for Substitute {
    fn visit_expr(&mut self, e: &mut rustc_ast::Expr) {
        if let rustc_ast::ExprKind::Path(None, path) = &e.kind
            && path.segments.len() == 1
        {
            let name = path.segments[0].ident.name.as_str();
            if name == super::decision::field_reference::WRAP_PLACEHOLDER {
                if let Some(inner) = self.inner.take() {
                    e.kind = inner;
                }
                self.substituted += 1;
                return;
            }
            if name == super::decision::field_reference::WRAP_PLACE {
                if let Some(place) = self.place.take() {
                    e.kind = place;
                }
                self.placed += 1;
                return;
            }
        }
        rustc_ast::mut_visit::walk_expr(self, e);
    }
}

/// Post-order over the grafted tree: an owned-field wrap closes over the
/// node's CURRENT expression, so an inner use graft (a reborrowed parameter,
/// a nested wrap) is already in place.
struct Wraps<'a> {
    /// span → (template, edit kind)
    edits: &'a FxHashMap<(u32, u32), (&'a str, &'static str)>,
    guard: &'a mut Composition,
    placed: FxHashSet<(u32, u32)>,
    failures: Vec<String>,
}

impl MutVisitor for Wraps<'_> {
    fn visit_expr(&mut self, e: &mut rustc_ast::Expr) {
        rustc_ast::mut_visit::walk_expr(self, e);
        if e.span.is_dummy() {
            return;
        }
        let key = (e.span.lo().0, e.span.hi().0);
        let Some(&(template, kind)) = self.edits.get(&key) else { return };
        if !self.placed.insert(key) {
            self.failures.push(format!("wrap-multi-matched:{key:?}"));
            return;
        }
        if !self.guard.claim(e.id, e.span, "field:wrap") {
            self.failures.push(format!("wrap-claim-refused:{key:?}"));
            return;
        }
        let parsed = match super::ast_transform::graft_expr(template) {
            Ok(parsed) => parsed,
            Err(offending) => {
                self.failures.push(format!("wrap-parse:{offending}"));
                return;
            }
        };
        let mut wrapped = parsed;
        // A null test wraps its RECEIVER: `<field>.is_null()` becomes
        // `<field>.is_none()`, the raw method call itself is consumed.
        // A raw-base store wraps the whole assignment: the PLACE and the
        // value are substituted separately.
        let (inner, place) = match (kind, &mut e.kind) {
            ("owned-field-is-null", rustc_ast::ExprKind::MethodCall(call)) => (
                std::mem::replace(&mut call.receiver.kind, rustc_ast::ExprKind::Dummy),
                None,
            ),
            ("owned-field-raw-store", rustc_ast::ExprKind::Assign(lhs, rhs, _)) => (
                std::mem::replace(&mut rhs.kind, rustc_ast::ExprKind::Dummy),
                Some(std::mem::replace(&mut lhs.kind, rustc_ast::ExprKind::Dummy)),
            ),
            // A cast site wraps the cast's OPERAND (the field), keeping the
            // template's own `as <target>`.
            (
                "owned-field-dealloc-transfer" | "owned-field-dealloc-transfer-contract",
                rustc_ast::ExprKind::Cast(operand, _),
            ) => (
                std::mem::replace(&mut operand.kind, rustc_ast::ExprKind::Dummy),
                None,
            ),
            // A raw view of a cast site likewise; of an OFFSET the receiver
            // (the field) is the inner and the offset operand the second slot.
            ("owned-field-raw-view", rustc_ast::ExprKind::Cast(operand, _)) => (
                std::mem::replace(&mut operand.kind, rustc_ast::ExprKind::Dummy),
                None,
            ),
            ("owned-field-raw-view", rustc_ast::ExprKind::MethodCall(call)) => {
                let Some(operand) = call.args.first_mut() else {
                    self.failures.push(format!("wrap-shape:{kind}:{key:?}"));
                    return;
                };
                (
                    std::mem::replace(&mut call.receiver.kind, rustc_ast::ExprKind::Dummy),
                    Some(std::mem::replace(
                        &mut operand.kind,
                        rustc_ast::ExprKind::Dummy,
                    )),
                )
            }
            // `*(f).offset(k)`: the field is the receiver under the deref.
            ("owned-field-element", rustc_ast::ExprKind::Unary(rustc_ast::UnOp::Deref, under)) => {
                let rustc_ast::ExprKind::MethodCall(call) = &mut under.kind else {
                    self.failures.push(format!("wrap-shape:{kind}:{key:?}"));
                    return;
                };
                (
                    std::mem::replace(&mut call.receiver.kind, rustc_ast::ExprKind::Dummy),
                    None,
                )
            }
            (
                "owned-field-is-null"
                | "owned-field-raw-store"
                | "owned-field-dealloc-transfer"
                | "owned-field-dealloc-transfer-contract"
                | "owned-field-element",
                _,
            ) => {
                self.failures.push(format!("wrap-shape:{kind}:{key:?}"));
                return;
            }
            _ => (
                std::mem::replace(&mut e.kind, rustc_ast::ExprKind::Dummy),
                None,
            ),
        };
        let expects_place = place.is_some();
        let mut substitute = Substitute {
            inner: Some(inner),
            place,
            substituted: 0,
            placed: 0,
        };
        substitute.visit_expr(&mut wrapped);
        let expects_inner = template.contains(super::decision::field_reference::WRAP_PLACEHOLDER);
        if substitute.substituted != usize::from(expects_inner)
            || substitute.placed != usize::from(expects_place)
        {
            self.failures.push(format!(
                "wrap-placeholder-count:{key:?}:{}:{}",
                substitute.substituted, substitute.placed
            ));
        }
        e.kind = wrapped.kind;
    }
}

/// Applies the wrapping expression edits of every active owned-field
/// transaction. Runs after the use-graft pass and before the seam pass.
pub(crate) fn apply_wraps(
    table: &DecisionTable,
    reverts: &RevertSet,
    krate: &mut rustc_ast::Crate,
    guard: &mut Composition,
) -> Result<(), String> {
    let mut edits: FxHashMap<(u32, u32), (&str, &'static str)> = FxHashMap::default();
    for transaction in table.field_transactions.active(&reverts.fns) {
        for edit in transaction.expression_edits.iter().filter(|edit| edit.wrap) {
            if edits
                .insert(
                    (edit.span.lo().0, edit.span.hi().0),
                    (edit.replacement.as_str(), edit.kind),
                )
                .is_some()
            {
                return Err(format!(
                    "field-transaction-wrap:key-collision:{:?}",
                    edit.span
                ));
            }
        }
    }
    if edits.is_empty() {
        return Ok(());
    }
    let mut wraps = Wraps {
        edits: &edits,
        guard,
        placed: FxHashSet::default(),
        failures: Vec::new(),
    };
    wraps.visit_crate(krate);
    if !wraps.failures.is_empty() {
        return Err(format!(
            "field-transaction-wrap:{}",
            wraps.failures.join(";")
        ));
    }
    if wraps.placed.len() != edits.len() {
        return Err(format!(
            "field-transaction-wrap:unplaced {}/{}",
            wraps.placed.len(),
            edits.len()
        ));
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// E5C-3: hoisted reads
// ---------------------------------------------------------------------------

/// Takes the expression at `read` out of a statement, leaving a path to the
/// hoisted binding in its place.
struct TakeRead {
    read: (u32, u32),
    name: String,
    taken: Option<rustc_ast::Expr>,
}

impl MutVisitor for TakeRead {
    fn visit_expr(&mut self, e: &mut rustc_ast::Expr) {
        if !e.span.is_dummy() && (e.span.lo().0, e.span.hi().0) == self.read && self.taken.is_none()
        {
            let path = super::ast_transform::graft_expr(&self.name)
                .expect("a hoisted binding name parses as a path");
            // The moved node keeps its id (the claim) and its spans (the
            // edits nested in it); the path left behind is a fresh node.
            let moved = e.clone();
            e.id = rustc_ast::node_id::DUMMY_NODE_ID;
            e.kind = path.kind;
            e.span = rustc_span::DUMMY_SP;
            self.taken = Some(moved);
            return;
        }
        rustc_ast::mut_visit::walk_expr(self, e);
    }
}

/// Inserts `let <name> = <read>;` before the statement holding the store
/// whose value moves an owned field before that read is evaluated.
struct Hoists<'a> {
    /// assignment span → the reads to hoist, in argument order
    plans: &'a FxHashMap<(u32, u32), Vec<(u32, u32)>>,
    guard: &'a mut Composition,
    placed: usize,
    counter: usize,
    failures: Vec<String>,
}

impl MutVisitor for Hoists<'_> {
    fn flat_map_stmt(
        &mut self,
        mut statement: rustc_ast::Stmt,
    ) -> smallvec::SmallVec<[rustc_ast::Stmt; 1]> {
        // A field-store plan is keyed by the assignment expression, a
        // local-move plan by the statement itself.
        let assignment = match &statement.kind {
            rustc_ast::StmtKind::Expr(e) | rustc_ast::StmtKind::Semi(e) => {
                Some((e.span.lo().0, e.span.hi().0))
            }
            _ => None,
        };
        let by_statement = (statement.span.lo().0, statement.span.hi().0);
        let reads: Vec<(u32, u32)> = assignment
            .and_then(|key| self.plans.get(&key))
            .into_iter()
            .chain(self.plans.get(&by_statement))
            .flatten()
            .copied()
            .collect();
        if reads.is_empty() {
            return rustc_ast::mut_visit::walk_flat_map_stmt(self, statement);
        }
        let mut out = smallvec::SmallVec::new();
        for read in &reads {
            let name = format!("__crat_hoist{}", self.counter);
            self.counter += 1;
            let mut take = TakeRead {
                read: *read,
                name: name.clone(),
                taken: None,
            };
            match &mut statement.kind {
                rustc_ast::StmtKind::Expr(e) | rustc_ast::StmtKind::Semi(e) => take.visit_expr(e),
                rustc_ast::StmtKind::Let(local) => {
                    if let rustc_ast::LocalKind::Init(init)
                    | rustc_ast::LocalKind::InitElse(init, _) = &mut local.kind
                    {
                        take.visit_expr(init);
                    }
                }
                _ => {}
            }
            let Some(read_expr) = take.taken else {
                self.failures.push(format!("hoist-read-unplaced:{read:?}"));
                continue;
            };
            if !self
                .guard
                .claim(read_expr.id, read_expr.span, "field:hoist")
            {
                self.failures.push(format!("hoist-claim-refused:{read:?}"));
                continue;
            }
            let mut binding = ::utils::ast::parse_stmt(format!("let {name} = 0;"));
            let rustc_ast::StmtKind::Let(local) = &mut binding.kind else {
                self.failures.push("hoist-binding-shape".to_owned());
                continue;
            };
            let rustc_ast::LocalKind::Init(init) = &mut local.kind else {
                self.failures.push("hoist-binding-init".to_owned());
                continue;
            };
            **init = read_expr;
            out.push(binding);
            self.placed += 1;
        }
        out.extend(rustc_ast::mut_visit::walk_flat_map_stmt(self, statement));
        out
    }
}

/// EXHAUSTIVE: only a delivered `Box` moves at a call.
fn delivers_box(decision: &super::decision::Decision) -> bool {
    use super::decision::Decision;
    match decision {
        Decision::Box(_) => true,
        Decision::Cursor { .. }
        | Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::NestedSlice { .. }
        | Decision::Opt { .. }
        | Decision::Degraded(_) => false,
    }
}

/// Applies the E5C-3 hoists of every active owned-field transaction. Runs
/// before the use-graft pass: a moved read keeps its spans, so the edits
/// nested in it are grafted where it now stands.
pub(crate) fn apply_hoists(
    table: &DecisionTable,
    reverts: &RevertSet,
    krate: &mut rustc_ast::Crate,
    guard: &mut Composition,
) -> Result<(), String> {
    let mut plans: FxHashMap<(u32, u32), Vec<(u32, u32)>> = FxHashMap::default();
    let mut expected = 0;
    for transaction in table.field_transactions.active(&reverts.fns) {
        for (_, assignment, read) in &transaction.hoists {
            plans
                .entry((assignment.lo().0, assignment.hi().0))
                .or_default()
                .push((read.lo().0, read.hi().0));
            expected += 1;
        }
    }
    // A moving owned local: active while the local delivers as a Box (a raw
    // local moves nothing the checker sees) and is not reverted.
    for (_, local, statement, read) in &table.field_transactions.local_move_hoists {
        let delivered = table
            .entries
            .iter()
            .find(|(s, _)| (s.fn_did, s.hir_id) == *local)
            .is_some_and(|(_, decision)| delivers_box(decision));
        if !delivered || !reverts.keeps_subject(local.0, local.1) {
            continue;
        }
        plans
            .entry((statement.lo().0, statement.hi().0))
            .or_default()
            .push((read.lo().0, read.hi().0));
        expected += 1;
    }
    if plans.is_empty() {
        return Ok(());
    }
    let mut hoists = Hoists {
        plans: &plans,
        guard,
        placed: 0,
        counter: 0,
        failures: Vec::new(),
    };
    hoists.visit_crate(krate);
    if !hoists.failures.is_empty() {
        return Err(format!(
            "field-transaction-hoist:{}",
            hoists.failures.join(";")
        ));
    }
    if hoists.placed != expected {
        return Err(format!(
            "field-transaction-hoist:unplaced {}/{expected}",
            hoists.placed
        ));
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// G: array locals
// ---------------------------------------------------------------------------

/// `let mut points: [*const T; N] = ..` → `let mut points: [Option<&T>; N]`:
/// the annotated type is replaced in place (the explicit-declaration visitor
/// refuses annotated locals; this one exists for them).
struct ArrayLocalRetype<'a> {
    local_map: &'a rustc_ast::node_id::NodeMap<rustc_hir::HirId>,
    global_map: &'a rustc_ast::node_id::NodeMap<LocalDefId>,
    arrays: &'a FxHashMap<(LocalDefId, rustc_hir::HirId), String>,
    current_fn: Option<LocalDefId>,
    guard: &'a mut Composition,
    placed: usize,
    failures: Vec<String>,
}

impl MutVisitor for ArrayLocalRetype<'_> {
    fn visit_item(&mut self, item: &mut rustc_ast::Item) {
        let saved = self.current_fn;
        if matches!(item.kind, rustc_ast::ItemKind::Fn(_)) {
            self.current_fn = self.global_map.get(&item.id).copied();
        }
        rustc_ast::mut_visit::walk_item(self, item);
        self.current_fn = saved;
    }

    fn visit_local(&mut self, local: &mut rustc_ast::Local) {
        if let Some(fn_did) = self.current_fn
            && let Some(&hir_id) = self.local_map.get(&local.pat.id)
            && let Some(ty) = self.arrays.get(&(fn_did, hir_id))
        {
            if local.ty.is_none() {
                self.failures.push(format!("array-local-unannotated:{ty}"));
                return;
            }
            if !self.guard.claim(local.pat.id, local.pat.span, "array:decl") {
                self.failures
                    .push(format!("array-local-claim-refused:{ty}"));
                return;
            }
            local.ty = Some(P(::utils::ast::parse_ty(ty.clone())));
            self.placed += 1;
        }
        rustc_ast::mut_visit::walk_local(self, local);
    }
}
