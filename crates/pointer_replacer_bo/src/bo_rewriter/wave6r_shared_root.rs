//! Shared-root address operands at raw formals.
//!
//! `callee(&mut (*root).field)` where `root` is a shared reference cannot form
//! a mutable reference. When the callee's formal stays raw and its position
//! carries negative-write evidence, the operand is a SHARED view of the place,
//! bridged read-only: `core::ptr::from_ref(&(*root).field).cast_mut()`. No
//! permission is raised; without that evidence the existing `SharedToMut`
//! hold applies.

use rustc_ast as ast;
use rustc_hir::{HirId, def_id::LocalDefId};

use super::decision::{
    Decision, DecisionTable,
    emitability::{Arg, ArgShape, EmitabilityFacts},
    raw_boundary::{BridgeTemplate, RawBoundarySiteFact, RawMutability, RawTargetType},
    seam::{Form, RawBoundaryGlue, SeamEdit, SeamPlan},
};

fn shared(decision: &Decision) -> bool {
    match decision {
        Decision::Ref { mutable } => !mutable,
        Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::Opt { .. }
        | Decision::Box(_)
        | Decision::NestedSlice { .. }
        | Decision::Cursor { .. }
        | Decision::Degraded(_) => false,
    }
}

fn shared_root(table: &DecisionTable, owner: LocalDefId, root: HirId) -> bool {
    table.entries.iter().any(|(subject, decision)| {
        subject.fn_did == owner && subject.hir_id == root && shared(decision)
    })
}

/// `&mut <place>` whose place projects through a dereference of `root`.
fn through_root(shape: &ArgShape, root: HirId) -> bool {
    matches!(
        *shape,
        ArgShape::AddrOf {
            mutable: true,
            base: Some(base),
            through_deref: true,
        } if base == root
    )
}

fn thin_mutable_target(target: &RawTargetType) -> bool {
    target.mutability == RawMutability::Mut && target.depth2.is_none() && !target.is_void_pointee()
}

/// The operand text re-spelled as a shared address.
fn shared_spelling(text: &str) -> Option<String> {
    let rest = text.strip_prefix("&mut")?;
    if rest.starts_with(|c: char| c.is_alphanumeric() || c == '_') {
        return None;
    }
    Some(format!("&{}", rest.trim_start()))
}

fn is_shared_spelling(text: &str) -> bool {
    text.starts_with('&') && shared_spelling(text).is_none()
}

/// Disposition time: the reference view of a mutable field address over a
/// shared root at a thin `*mut` formal is the shared view.
pub(crate) fn disposition_view(
    emitability: &EmitabilityFacts,
    site: &RawBoundarySiteFact,
    node: (LocalDefId, HirId),
    decision: &Decision,
    view: Option<Decision>,
) -> Option<Decision> {
    if site.source_shape != "addr-of-mut" || !thin_mutable_target(&site.target) || !shared(decision)
    {
        return view;
    }
    let Some(callee) = site.callee_local else { return view };
    let through = emitability
        .call_args
        .get(&callee)
        .into_iter()
        .flatten()
        .filter(|call| call.caller == node.0 && call.span == site.call_span)
        .flat_map(|call| call.args.iter())
        .any(|arg| arg.span == site.source_span && through_root(&arg.shape, node.1));
    if through {
        Some(Decision::Ref { mutable: false })
    } else {
        view
    }
}

/// Seam plan: an outbound edit that selected the shared template over a
/// mutable address operand renders from the shared spelling.
pub(crate) fn complete_outbound(table: &DecisionTable, plan: &mut SeamPlan) {
    for edit in &mut plan.edits {
        let SeamEdit {
            raw_outbound: Some(endpoint),
            spec,
            replacement,
            zero_syntax,
            source_shape,
            source_node: Some((owner, root)),
            ..
        } = edit
        else {
            continue;
        };
        if *source_shape != "addr-of-mut"
            || !spec
                .raw_boundary
                .as_ref()
                .is_some_and(|raw| raw.template == BridgeTemplate::RefSharedToRawMut)
            || !shared_root(table, *owner, *root)
        {
            continue;
        }
        let Some(flipped) = shared_spelling(&endpoint.operand_expression) else { continue };
        let Some(rendered) = spec.render_in_context(&flipped, endpoint.enclosing_unsafe_fn) else {
            continue;
        };
        endpoint.operand_expression = flipped;
        *replacement = rendered;
        *zero_syntax = false;
    }
}

/// Terminal sealing: the view an outbound edit already re-spelled as shared.
pub(crate) fn terminal_view(
    current: &Decision,
    old: &SeamEdit,
    view: Option<Decision>,
) -> Option<Decision> {
    let Some(endpoint) = old.raw_outbound.as_ref() else { return view };
    if old.source_shape == "addr-of-mut"
        && shared(current)
        && endpoint.negative_write
        && thin_mutable_target(&endpoint.target)
        && is_shared_spelling(&endpoint.operand_expression)
    {
        Some(Decision::Ref { mutable: false })
    } else {
        view
    }
}

/// Callee-parameter input: the argument's found form over a shared root.
pub(crate) fn input_found(
    table: &DecisionTable,
    caller: LocalDefId,
    arg: &Arg,
    target: &RawTargetType,
    found: Form,
) -> Form {
    if found != (Form::Ref { mutable: true }) || !thin_mutable_target(target) {
        return found;
    }
    let ArgShape::AddrOf {
        mutable: true,
        base: Some(root),
        through_deref: true,
    } = arg.shape
    else {
        return found;
    };
    if shared_root(table, caller, root) {
        Form::Ref { mutable: false }
    } else {
        found
    }
}

/// Callee-parameter input: the operand text for that shared view.
pub(crate) fn input_text(text: String, arg: &Arg, found: Form) -> String {
    if found == (Form::Ref { mutable: false })
        && matches!(arg.shape, ArgShape::AddrOf { mutable: true, .. })
    {
        shared_spelling(&text).unwrap_or(text)
    } else {
        text
    }
}

/// AST graft: the shared template reads a `&mut place` operand as `&place`.
pub(crate) fn graft_argument(mut argument: ast::Expr, raw: &RawBoundaryGlue) -> ast::Expr {
    if raw.template == BridgeTemplate::RefSharedToRawMut
        && let ast::ExprKind::AddrOf(ast::BorrowKind::Ref, permission, _) = &mut argument.kind
    {
        *permission = ast::Mutability::Not;
    }
    argument
}
