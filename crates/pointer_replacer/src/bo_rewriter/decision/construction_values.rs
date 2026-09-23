//! Inferred local copies of an existing reference stay compiler-visible reborrows.

use rustc_hir::{ExprKind, HirId, Node, PatKind, def::Res};
use rustc_middle::ty::{TyCtxt, TyKind};
use rustc_span::Span;

use super::{Ctx, Decision, DecisionTable, DeclShape, Subject, SubjectKind, declaration, seam};
use crate::bo_rewriter::{
    additive::FamilyStage,
    bridge_receipt::{BridgeSitePlan, SignatureClassId},
};

struct CopyValue {
    source: HirId,
    initializer: Span,
    pointee: String,
}

fn plain_reference(decision: &Decision) -> Option<&bool> {
    match decision {
        Decision::Ref { mutable } => Some(mutable),
        Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::Opt { .. }
        | Decision::Box(_)
        | Decision::Cursor { .. }
        | Decision::NestedSlice { .. }
        | Decision::Degraded(_) => None,
    }
}

fn copy_value(tcx: TyCtxt<'_>, subject: &Subject) -> Option<CopyValue> {
    if subject.kind != SubjectKind::Local
        || subject.ty_span.is_some()
        || subject.decl_shape != DeclShape::RawPtr
        || subject.ptr_depth != 1
        || subject.null_init
    {
        return None;
    }
    let Node::LetStmt(local) = tcx.parent_hir_node(subject.hir_id) else { return None };
    if !matches!(local.pat.kind, PatKind::Binding(_, hir, _, None) if hir == subject.hir_id)
        || local.ty.is_some()
    {
        return None;
    }
    let initializer = local.init?;
    let ExprKind::Path(path) = &initializer.kind else { return None };
    let typeck = tcx.typeck(subject.fn_did);
    let Res::Local(source) = typeck.qpath_res(path, initializer.hir_id) else { return None };
    let input = typeck.pat_ty(local.pat);
    let TyKind::RawPtr(pointee, _) = input.kind() else { return None };
    if typeck.expr_ty(initializer) != input
        || initializer.span.from_expansion()
        || subject.binding_span.from_expansion()
        || !declaration::pointee_is_nameable(tcx, subject.fn_did, *pointee)
    {
        return None;
    }
    Some(CopyValue {
        source,
        initializer: initializer.span,
        pointee: declaration::pointee_source(tcx, *pointee),
    })
}

/// Preserve zero-length address-only paths. This first slice copy shape is
/// followed immediately by a while guard whose first operand reads *source;
/// the input therefore already requires that element before any exit or call.
fn requires_first_element(tcx: TyCtxt<'_>, subject: &Subject, source: HirId) -> bool {
    use rustc_hir::{Expr, LoopSource, StmtKind, UnOp};
    fn peel<'a>(mut expression: &'a Expr<'a>) -> &'a Expr<'a> {
        while let ExprKind::DropTemps(inner) | ExprKind::Cast(inner, _) = expression.kind {
            expression = inner;
        }
        expression
    }
    let body = tcx.hir_body_owned_by(subject.fn_did);
    let ExprKind::Block(block, _) = body.value.kind else { return false };
    let Some(pair) = block.stmts.windows(2).find(
        |pair| matches!(pair[0].kind, StmtKind::Let(local) if local.pat.hir_id == subject.hir_id),
    ) else {
        return false;
    };
    let (StmtKind::Expr(next) | StmtKind::Semi(next)) = pair[1].kind else { return false };
    let ExprKind::Loop(guard_block, _, LoopSource::While, _) = next.kind else { return false };
    if !guard_block.stmts.is_empty() {
        return false;
    }
    let Some(guard) = guard_block.expr else { return false };
    let ExprKind::If(condition, _, _) = guard.kind else { return false };
    let ExprKind::Binary(_, left, _) = peel(condition).kind else { return false };
    let ExprKind::Unary(UnOp::Deref, pointer) = peel(left).kind else { return false };
    let ExprKind::Path(path) = &pointer.kind else { return false };
    tcx.typeck(subject.fn_did).qpath_res(path, pointer.hir_id) == Res::Local(source)
}

fn compatible(tcx: TyCtxt<'_>, subject: &Subject, value: &CopyValue, decision: &Decision) -> bool {
    match seam::form_of(decision) {
        seam::Form::Ref { mutable } => !subject.mutable || mutable,
        seam::Form::Slice { mutable } => {
            (!subject.mutable || mutable) && requires_first_element(tcx, subject, value.source)
        }
        _ => false,
    }
}

/// **A12 (relay 031) — a LOCAL source, one hop.** The rule admitted only
/// parameters, to keep the query acyclic and to guess no copying-local chain.
/// A local source keeps both properties when it is not ITSELF this shape:
/// `copy_value(source).is_none()` bounds the walk at one step, so `decide_one`
/// on the source returns without re-entering this rule. Measured at batch 16:
/// heman `heman_ops_sobel::fresh13#271` copies a local already decided `slice`;
/// brotli's four `base*` rows copy `ip`, whose own `ptr-comparison` refusal is
/// slicecursor's A5 and not this family's to lift (report 031).
fn admissible_source(tcx: TyCtxt<'_>, source: &Subject) -> bool {
    match source.kind {
        SubjectKind::Param { .. } => true,
        SubjectKind::Local => copy_value(tcx, source).is_none(),
        _ => false,
    }
}

/// Consult the ordinary ladder for the source. Sources are a parameter or a
/// non-copying local (`admissible_source`), which keeps this query acyclic.
pub(super) fn permits(ctx: &Ctx<'_, '_>, subject: &Subject) -> bool {
    if !ctx
        .family_policy
        .enabled(subject.fn_did, FamilyStage::Declaration)
    {
        return false;
    }
    let Some(value) = copy_value(ctx.tcx, subject) else { return false };
    ctx.subjects
        .iter()
        .find(|source| {
            source.fn_did == subject.fn_did
                && source.hir_id == value.source
                && admissible_source(ctx.tcx, source)
        })
        .is_some_and(|source| compatible(ctx.tcx, subject, &value, &super::decide_one(ctx, source)))
}

/// A raw fallback on the source cannot turn this rule into a raw-to-ref bridge.
pub(super) fn settle(ctx: &Ctx<'_, '_>, entries: &mut [(Subject, Decision)]) {
    let refused = entries
        .iter()
        .enumerate()
        .filter_map(|(index, (subject, decision))| {
            if subject.ty_span.is_some() || plain_reference(decision).is_none() {
                return None;
            }
            // wave-5d2: defensive — a local typed by its own literal initializer
            // (`source_typed_local`) is not a refusal of THIS rule. Today the two
            // recognizers are disjoint (path initializer vs literal initializer),
            // so this guard changes no outcome; it holds if `copy_value` widens.
            // (Confirmed by this file's owner, wave-6k report 020.)
            if super::source_typed_local::permits(ctx, subject) {
                return None;
            }
            let value = copy_value(ctx.tcx, subject)?;
            let source = entries
                .iter()
                .find(|(s, _)| s.fn_did == subject.fn_did && s.hir_id == value.source);
            (!source.is_some_and(|(_, d)| compatible(ctx.tcx, subject, &value, d))).then_some(index)
        })
        .collect::<Vec<_>>();
    for index in refused {
        let (subject, decision) = &mut entries[index];
        *decision = super::degrade(
            subject,
            super::emitability::EmitabilityFacts::site(ctx.tcx, subject.binding_span),
            super::DegradeReason::CopySourceCoupled,
        );
    }
}

pub(super) fn complete(tcx: TyCtxt<'_>, table: &DecisionTable, plan: &mut seam::SeamPlan) {
    for (subject, decision) in &table.entries {
        let Some(mutable) = plain_reference(decision) else { continue };
        let Some(value) = copy_value(tcx, subject) else { continue };
        let node = (subject.fn_did, subject.hir_id);
        let Some((source, found)) = table
            .entries
            .iter()
            .find(|(s, _)| s.fn_did == subject.fn_did && s.hir_id == value.source)
        else {
            continue;
        };
        if !compatible(tcx, subject, &value, found) || !admissible_source(tcx, source) {
            continue;
        }
        // Subject-only withdrawal could otherwise restore a raw parent under
        // this reborrow. Leave that composition to the existing typed hold.
        if plan
            .raw_boundary_atom_groups
            .contains_key(&(source.fn_did, source.hir_id))
            || plan.raw_boundary_atom_groups.contains_key(&node)
        {
            continue;
        }
        let Ok(text) = tcx.sess.source_map().span_to_snippet(value.initializer) else { continue };
        let core = match seam::form_of(found) {
            seam::Form::Slice { .. } => seam::GlueCore::Index0,
            _ => seam::GlueCore::Reborrow,
        };
        let spec = seam::GlueSpec::core(core, *mutable);
        let Some(replacement) = spec.render_in_context(&text, true) else { continue };
        let Some(emitted_type) = declaration::emitted_type(decision, &value.pointee, None) else {
            continue;
        };
        let owner_class = SignatureClassId::of(subject.fn_did);
        let found = seam::form_of(found);
        let expected = seam::form_of(decision);
        // A prior equal-form body site has no edit. Refuse a second owner.
        if plan
            .body_edits
            .iter()
            .any(|edit| edit.span == value.initializer)
            || plan
                .explicit_declarations
                .iter()
                .any(|site| site.node == Some(node))
        {
            continue;
        }
        let mut bridge = BridgeSitePlan::local(
            subject.fn_did,
            subject.fn_did,
            "glue",
            "body:local-initializer",
            "copy-local-reborrow",
        );
        bridge.expected_form = expected.key().to_owned();
        bridge.found_form = found.key().to_owned();
        bridge.argument_kind = "bare-local".to_owned();
        plan.body_edits.push(seam::BodyEdit {
            span: value.initializer,
            replacement,
            owner_class,
            bridge,
            owner_fn: tcx.def_path_str(subject.fn_did.to_def_id()),
            destination: subject.label.clone(),
            context: super::emitability::BodyAdapterContext::LocalInitializer,
            source_shape: "bare-local",
            family: seam::SeamFamily::Safe,
            spec,
            arg_span: value.initializer,
            expected,
            found,
            root_identity: source.label.clone(),
            blind: false,
        });
        plan.explicit_declarations
            .push(seam::ExplicitDeclarationSite {
                owner_class,
                caller: subject.fn_did,
                node: Some(node),
                span: Some(subject.binding_span.shrink_to_hi()),
                category: "local",
                replacement: Some(format!(": {emitted_type}")),
                emitted_type,
                arm: "surface",
            });
    }
}

pub(crate) fn has_declaration(table: &DecisionTable, subject: &Subject) -> bool {
    let node = (subject.fn_did, subject.hir_id);
    subject.ty_span.is_none()
        && table.seams.explicit_declarations.iter().any(|site| {
            site.node == Some(node)
                && site.category == "local"
                && site.owner_class == SignatureClassId::of(subject.fn_did)
        })
        && table.seams.body_edits.iter().any(|edit| {
            edit.destination == subject.label && edit.bridge.bridge_kind == "copy-local-reborrow"
        })
}

/// The value plan consumes this exact slice operand as a checked element
/// borrow. The slice-use producer must not also produce a raw pointer here.
pub(super) fn owns_initializer(
    tcx: TyCtxt<'_>,
    table: &DecisionTable,
    source: &Subject,
    destination: &Subject,
    rhs: &rustc_hir::Expr<'_>,
) -> bool {
    has_declaration(table, destination)
        && copy_value(tcx, destination).is_some_and(|value| {
            value.source == source.hir_id
                && source.fn_did == destination.fn_did
                && value.initializer == rhs.span
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wave6k_guarded_empty_slice_keeps_the_address_copy() {
        ::utils::compilation::run_compiler_on_str(
            r#"
            pub unsafe fn guarded(mut a: *const i8, n: usize) -> usize {
                let orig = a;
                if n == 0 { return a.offset_from(orig) as usize; }
                while *a != 0 { a = a.offset(1); }
                a.offset_from(orig) as usize
            }
        "#,
            |tcx| {
                let (table, _) = crate::bo_rewriter::decide_table_with_ctx_config(
                    tcx,
                    Some((
                        crate::bo_rewriter::A5Mode::PreciseReplay,
                        Some(crate::bo_rewriter::WholeProgramAttestation::FrozenBenchmarkGraph),
                    )),
                )
                .unwrap();
                let destination = &table
                    .entries
                    .iter()
                    .find(|(s, _)| s.param_name.as_deref() == Some("orig"))
                    .unwrap()
                    .0;
                assert!(
                    !has_declaration(&table, destination),
                    "an address-only zero-length path must not eagerly index the slice"
                );
            },
        )
        .unwrap();
    }

    fn fixture(check: impl FnOnce(TyCtxt<'_>, DecisionTable, Subject, Subject) + Send) {
        ::utils::compilation::run_compiler_on_str(
            "pub unsafe fn copy(p: *mut u8) -> u8 { let q = p; *q += 1; *q }",
            |tcx| {
                let (table, _) = crate::bo_rewriter::decide_table_with_ctx_config(
                    tcx,
                    Some((
                        crate::bo_rewriter::A5Mode::PreciseReplay,
                        Some(crate::bo_rewriter::WholeProgramAttestation::FrozenBenchmarkGraph),
                    )),
                )
                .expect("native decisions");
                let subject = |name| {
                    table
                        .entries
                        .iter()
                        .find(|(s, _)| s.param_name.as_deref() == Some(name))
                        .unwrap()
                        .0
                        .clone()
                };
                let source = subject("p");
                let destination = subject("q");
                assert!(has_declaration(&table, &destination));
                check(tcx, table, source, destination);
            },
        )
        .expect("fixture compiles");
    }

    fn rebuild(tcx: TyCtxt<'_>, table: &mut DecisionTable) {
        let mut plan = table.seams.clone();
        plan.body_edits
            .retain(|e| e.bridge.bridge_kind != "copy-local-reborrow");
        plan.explicit_declarations.retain(|s| s.category != "local");
        complete(tcx, table, &mut plan);
        table.seams = plan;
    }

    #[test]
    fn wave6k_mutable_copy_reborrows() {
        fixture(|_, table, _, destination| {
            let edit = table
                .seams
                .body_edits
                .iter()
                .find(|e| e.destination == destination.label)
                .expect("mutable value");
            assert_eq!(edit.replacement, "&mut *p");
            assert_eq!(edit.found, seam::Form::Ref { mutable: true });
        });
    }

    #[test]
    fn wave6k_shared_source_never_becomes_mutable() {
        fixture(|tcx, mut table, source, destination| {
            table
                .entries
                .iter_mut()
                .find(|(s, _)| s.hir_id == source.hir_id)
                .unwrap()
                .1 = Decision::Ref { mutable: false };
            rebuild(tcx, &mut table);
            assert!(!has_declaration(&table, &destination));
        });
    }

    #[test]
    fn wave6k_raw_source_never_becomes_a_reborrow() {
        fixture(|tcx, mut table, source, destination| {
            table
                .entries
                .iter_mut()
                .find(|(s, _)| s.hir_id == source.hir_id)
                .unwrap()
                .1 = super::super::degrade(
                &source,
                "fixture".into(),
                super::super::DegradeReason::KindRaw,
            );
            rebuild(tcx, &mut table);
            assert!(!has_declaration(&table, &destination));
        });
    }

    #[test]
    fn wave6k_source_atom_withdrawal_cannot_leave_a_copy() {
        fixture(|tcx, mut table, source, destination| {
            table
                .seams
                .raw_boundary_atom_groups
                .insert((source.fn_did, source.hir_id), vec![]);
            rebuild(tcx, &mut table);
            assert!(!has_declaration(&table, &destination));
        });
    }

    #[test]
    fn wave6k_destination_atom_withdrawal_cannot_leave_a_copy() {
        fixture(|tcx, mut table, _, destination| {
            table
                .seams
                .raw_boundary_atom_groups
                .insert((destination.fn_did, destination.hir_id), vec![]);
            rebuild(tcx, &mut table);
            assert!(!has_declaration(&table, &destination));
        });
    }
}

/// **The counted READ alias needs no declaration (relay 035; wave-6v 028 route
/// (a)).** `let mut csrc = src as *const libc::c_uchar;` over a `*const c_void`
/// parameter whose counted contract is active is not a copy this family has to
/// type: the contract already rewrote the initializer and every use, so the
/// emitted local IS the byte view (`let mut csrc = src.unwrap_or(&[]); … csrc =
/// &csrc[1..];`). Its type comes from that initializer, so the receiver-form
/// refusal must not degrade it for lacking a declaration it does not need.
///
/// Declaration-FREE, not veto-exempt: this only removes the refusal's claim on
/// the subject; every arm below it still decides the form. wave-6v 028 measured
/// what the exempting form costs — six of their witnesses turn red when the
/// subject short-circuits those arms.
pub(super) fn counted_alias_needs_no_declaration(ctx: &Ctx<'_, '_>, subject: &Subject) -> bool {
    // The relation is the CONTRACT's to state, not the initializer's to imply:
    // report 035 measured three keys derived from this side and all three miss,
    // because the contract that rewrites the local is not the one keyed on the
    // parameter it casts. `counted_void_read::prove` records which local it
    // rewrote (wave-6v's `Contract::alias`), and `alias_contract` resolves it.
    super::counted_void::alias_contract(ctx, subject).is_some()
}
