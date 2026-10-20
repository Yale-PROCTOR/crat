//! wave-6a W6A-T1 — the item half of a flexible-tail transaction, as node
//! transforms: the struct's tail field becomes `Box<[T]>` and its `Copy` /
//! `Clone` derives and impls go; the allocating callee's output becomes
//! `Box<S>`; the freeing callee's parameter becomes `Box<S>` where the
//! declaration pass left it raw. Tail-access expressions travel the ordinary
//! use-graft channel (`filtered_inputs`).
//!
//! A transaction is ACTIVE only while none of its owners is reverted: the
//! layout change is crate-wide, so it is applied whole or not at all.

use rustc_ast::{mut_visit::MutVisitor, ptr::P};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_span::{def_id::LocalDefId, sym};
use smallvec::{SmallVec, smallvec};

use super::{
    ast_transform::{AstCapture, Composition, RevertSet},
    decision::{DecisionTable, flexible_tail::StructTransaction},
};

/// Every function a transaction edits or plans a subject in.
pub(crate) fn owners(
    table: &DecisionTable,
    transaction: &StructTransaction,
) -> FxHashSet<LocalDefId> {
    let mut owners: FxHashSet<LocalDefId> = transaction.owning_returns.iter().copied().collect();
    owners.extend(transaction.owning_params.iter().map(|(f, _)| *f));
    owners.extend(
        table
            .flexible_tails
            .plans
            .keys()
            .filter(|(f, hir)| {
                table
                    .entries
                    .iter()
                    .any(|(s, _)| s.fn_did == *f && s.hir_id == *hir)
            })
            .map(|(f, _)| *f),
    );
    owners
}

pub(crate) fn active<'a>(
    table: &'a DecisionTable,
    reverts: &RevertSet,
) -> Vec<&'a StructTransaction> {
    table
        .flexible_tails
        .structs
        .values()
        .filter(|t| owners(table, t).iter().all(|f| !reverts.fns.contains(f)))
        .collect()
}

struct Apply<'a> {
    global_map: &'a rustc_ast::node_id::NodeMap<LocalDefId>,
    structs: &'a FxHashMap<LocalDefId, (String, usize)>,
    removed_impls: &'a FxHashSet<LocalDefId>,
    returns: &'a FxHashMap<LocalDefId, String>,
    guard: &'a mut Composition,
    placed_structs: FxHashSet<LocalDefId>,
    placed_impls: FxHashSet<LocalDefId>,
    placed_returns: FxHashSet<LocalDefId>,
    failures: Vec<String>,
}

fn strip_copy_clone_derives(attrs: &mut thin_vec::ThinVec<rustc_ast::Attribute>) {
    let mut rebuilt = thin_vec::ThinVec::new();
    for attr in attrs.drain(..) {
        if !attr.has_name(sym::derive) {
            rebuilt.push(attr);
            continue;
        }
        let Some(list) = attr.meta_item_list() else {
            rebuilt.push(attr);
            continue;
        };
        let kept: Vec<String> = list
            .iter()
            .filter_map(|item| item.meta_item())
            .filter(|meta| {
                !matches!(
                    meta.path.segments.last().map(|s| s.ident.name),
                    Some(sym::Copy | sym::Clone)
                )
            })
            .map(|meta| rustc_ast_pretty::pprust::path_to_string(&meta.path))
            .collect();
        if !kept.is_empty() {
            rebuilt.extend(::utils::ast::parse_attr(format!(
                "#[derive({})]",
                kept.join(", ")
            )));
        }
    }
    *attrs = rebuilt;
}

/// `*mut S` / `*const S` → `Box<S>` with `S` spelled as the source spells it.
fn boxed_pointee(ty: &rustc_ast::Ty) -> Option<String> {
    let rustc_ast::TyKind::Ptr(pointer) = &ty.kind else { return None };
    Some(format!(
        "Box<{}>",
        rustc_ast_pretty::pprust::ty_to_string(&pointer.ty)
    ))
}

impl MutVisitor for Apply<'_> {
    fn flat_map_item(&mut self, mut item: P<rustc_ast::Item>) -> SmallVec<[P<rustc_ast::Item>; 1]> {
        if let Some(&did) = self.global_map.get(&item.id) {
            if self.removed_impls.contains(&did)
                && let rustc_ast::ItemKind::Impl(im) = &mut item.kind
            {
                if !self.guard.claim(item.id, item.span, "flexible-tail:impl") {
                    self.failures.push(format!("impl-claim-refused:{did:?}"));
                    return smallvec![item];
                }
                // The `Copy` / `Clone` impl becomes an empty inherent impl at
                // the same span: the substrate splice replaces exactly it.
                im.of_trait = None;
                im.items.clear();
                self.placed_impls.insert(did);
                return smallvec![item];
            }
            if let Some((element, field_index)) = self.structs.get(&did)
                && let rustc_ast::ItemKind::Struct(_, _, variant) = &mut item.kind
            {
                let rustc_ast::VariantData::Struct { fields, .. } = variant else {
                    self.failures.push(format!("struct-shape:{did:?}"));
                    return smallvec![item];
                };
                let Some(field) = fields.get_mut(*field_index) else {
                    self.failures.push(format!("field-index:{did:?}"));
                    return smallvec![item];
                };
                if !self.guard.claim(item.id, item.span, "flexible-tail:struct") {
                    self.failures.push(format!("struct-claim-refused:{did:?}"));
                    return smallvec![item];
                }
                field.ty = P(::utils::ast::parse_ty(format!("Box<[{element}]>")));
                strip_copy_clone_derives(&mut item.attrs);
                self.placed_structs.insert(did);
            } else if let rustc_ast::ItemKind::Fn(function) = &mut item.kind {
                if let Some(output) = self.returns.get(&did) {
                    // The output type's own node: a parameter pass may hold
                    // the item, and the two edits do not overlap.
                    let (claim_id, claim_span) = match &function.sig.decl.output {
                        rustc_ast::FnRetTy::Ty(ty) => (ty.id, ty.span),
                        rustc_ast::FnRetTy::Default(_) => (item.id, item.span),
                    };
                    if !self
                        .guard
                        .claim(claim_id, claim_span, "flexible-tail:return")
                    {
                        self.failures.push(format!("return-claim-refused:{did:?}"));
                        return smallvec![item];
                    }
                    // The source's own pointee spelling, boxed — the same text
                    // the receivers' declarations carry.
                    let boxed = match &function.sig.decl.output {
                        rustc_ast::FnRetTy::Ty(ty) if !output.starts_with("Option<") => {
                            boxed_pointee(ty).unwrap_or_else(|| output.clone())
                        }
                        // W6A-A1: the certificate's own text (`Option<Box<T>>`).
                        _ => output.clone(),
                    };
                    function.sig.decl.output =
                        rustc_ast::FnRetTy::Ty(P(::utils::ast::parse_ty(boxed)));
                    self.placed_returns.insert(did);
                }
                // Owning parameters are subjects: the declaration pass boxes them.
            }
        }
        rustc_ast::mut_visit::walk_flat_map_item(self, item)
    }
}

pub(crate) fn apply(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    capture: &AstCapture,
    table: &DecisionTable,
    reverts: &RevertSet,
    krate: &mut rustc_ast::Crate,
    guard: &mut Composition,
) -> Result<(), String> {
    let active = active(table, reverts);
    // wave-6a W6A-A1: certified allocation returns, active while none of the
    // certificate's owners (the callee, its receivers' functions) reverted.
    let certified: Vec<&super::decision::return_certificate::Certificate> = table
        .return_certificates
        .callees
        .values()
        .filter(|c| {
            table
                .return_certificates
                .owners(c.callee)
                .iter()
                .all(|f| !reverts.fns.contains(f))
        })
        .collect();
    if active.is_empty() && certified.is_empty() {
        return Ok(());
    }
    let mut structs = FxHashMap::default();
    let mut removed_impls = FxHashSet::default();
    let mut returns = FxHashMap::default();
    for transaction in &active {
        let boxed = format!("Box<{}>", transaction.struct_path);
        structs.insert(
            transaction.struct_did,
            (
                transaction.element_type.clone(),
                transaction.tail_field_index,
            ),
        );
        removed_impls.extend(transaction.impls_to_remove.iter().copied());
        for &function in &transaction.owning_returns {
            returns.insert(function, boxed.clone());
        }
    }
    for certificate in &certified {
        returns.insert(certificate.callee, certificate.output_type.clone());
    }
    let _ = tcx;
    let mut apply = Apply {
        global_map: &capture.map.global_map,
        structs: &structs,
        removed_impls: &removed_impls,
        returns: &returns,
        guard,
        placed_structs: FxHashSet::default(),
        placed_impls: FxHashSet::default(),
        placed_returns: FxHashSet::default(),
        failures: Vec::new(),
    };
    apply.visit_crate(krate);
    if !apply.failures.is_empty() {
        return Err(format!("flexible-tail-ast:{}", apply.failures.join(";")));
    }
    if apply.placed_structs.len() != structs.len()
        || apply.placed_impls.len() != removed_impls.len()
        || apply.placed_returns.len() != returns.len()
    {
        return Err(format!(
            "flexible-tail-ast:unplaced: structs {}/{} impls {}/{} returns {}/{}",
            apply.placed_structs.len(),
            structs.len(),
            apply.placed_impls.len(),
            removed_impls.len(),
            apply.placed_returns.len(),
            returns.len()
        ));
    }
    Ok(())
}
