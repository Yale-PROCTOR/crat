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
    field_index: usize,
    form: DeclForm,
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
                let Some(field) = fields.get_mut(plan.field_index) else {
                    self.failures.push(format!("field-index:{did:?}"));
                    return;
                };
                let TyKind::Ptr(inner) = &field.ty.kind else {
                    self.failures.push(format!("field-not-raw:{did:?}"));
                    return;
                };
                if !self.guard.claim(item.id, item.span, "field:struct") {
                    self.failures.push(format!("struct-claim-refused:{did:?}"));
                    return;
                }
                let pointee = inner.ty.clone();
                field.ty.kind =
                    decl_ty_kind_with_lifetime(plan.form, false, pointee, Some(&plan.lifetime));
                insert_lifetime_param(generics, &plan.lifetime);
                self.placed_structs.insert(did);
            } else if let Some(struct_did) = self.impls.get(&did)
                && let Some(plan) = self.structs.get(struct_did)
                && let rustc_ast::ItemKind::Impl(im) = &mut item.kind
            {
                if !self.guard.claim(item.id, item.span, "field:impl") {
                    self.failures.push(format!("impl-claim-refused:{did:?}"));
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
    for transaction in &active {
        let struct_did = transaction.key.struct_did;
        let Some(form) = decl_form(transaction.form) else {
            return Err(format!(
                "field-transaction-ast:form-unrenderable:{}",
                transaction.struct_path
            ));
        };
        if structs.contains_key(&struct_did) {
            return Err(format!(
                "field-transaction-ast:multi-field-struct:{}",
                transaction.struct_path
            ));
        }
        structs.insert(
            struct_did,
            StructPlan {
                field_index: transaction.key.field_index,
                form,
                lifetime: "'a".to_owned(),
                name: tcx.item_name(struct_did.to_def_id()),
            },
        );
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
            signatures.insert(plan.owner, (struct_did, indices));
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
