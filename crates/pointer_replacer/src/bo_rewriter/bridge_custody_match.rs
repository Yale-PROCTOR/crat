//! R231/R233 shared, parser-only bridge custody comparison.
//! The caller verifies source hashes before supplying these inventories.

use std::collections::BTreeSet;

use rustc_ast::{self as ast, mut_visit::MutVisitor};
use rustc_ast_pretty::pprust;
use rustc_session::parse::ParseSess;
use rustc_span::edition::Edition;
use serde::{Deserialize, Serialize};

use super::bridge_custody_syntax::{
    ArgumentForm, Binding, ByteSpan, Call, GeneratedKind, Inventory,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum BridgeKind {
    PairT2RawView,
    A5SiteProofT2Fallback,
    PairCopySnapshot,
    SiblingOverlapPending,
}

/// File-relative original bytes and zero-based argument indices. An empty
/// whole-call argument list is permitted only for a C9 receipt whose position
/// must be established uniquely by its exact snapshot stamp and actual use.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum SiteAnchor {
    Call {
        span: ByteSpan,
        argument_indices: Vec<usize>,
    },
    Argument {
        span: ByteSpan,
        argument_index: usize,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct C9Stamp {
    pub(crate) basic_block: u32,
    pub(crate) statement_index: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum PendingSourceShape {
    WholeSubject,
    ProjectedReferent,
    NativeReturnExpression {
        argument_span: ByteSpan,
        source_call_span: ByteSpan,
        source_owner: u32,
        source_function: String,
        source_form: String,
        source_type: String,
        temporary: String,
        template: String,
    },
    /// The same carrier placed at a call the argument CONTAINS rather than IS.
    /// Its own arm, so the shape above keeps its exact rule: there the edit
    /// interval and the argument are the same span, here the edit is strictly
    /// inside the argument and the enclosing text must survive verbatim.
    NativeReturnExpressionNested {
        argument_span: ByteSpan,
        source_call_span: ByteSpan,
        source_owner: u32,
        source_function: String,
        source_form: String,
        source_type: String,
        temporary: String,
        template: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct PendingSource {
    pub(crate) binding: Option<String>,
    /// Original compiler binding-pattern span, not a guessed expression root.
    pub(crate) binding_span: Option<ByteSpan>,
    pub(crate) shape: PendingSourceShape,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct BridgeExpectation {
    /// Exact ledger identity, retained separately for whole-call and argument rows.
    pub(crate) identity: String,
    pub(crate) kind: BridgeKind,
    /// Qualified original function identities from the compiler/receipt join.
    pub(crate) caller: String,
    pub(crate) callee: String,
    pub(crate) anchor: SiteAnchor,
    pub(crate) c9_stamp: Option<C9Stamp>,
    #[serde(default)]
    pub(crate) pending_source: Option<PendingSource>,
    pub(crate) tier: String,
    pub(crate) waiver_id: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct OwnerRename {
    pub(crate) original_owner: String,
    pub(crate) emitted_owner: String,
    /// Explicit exposure-mapping receipt; an inferred basename is insufficient.
    pub(crate) evidence: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct CalleeRename {
    pub(crate) original_caller: String,
    /// Exact callee expression spellings, checked through parsed expressions.
    pub(crate) original_callee_text: String,
    pub(crate) emitted_callee_text: String,
    pub(crate) evidence: String,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct BridgeCustodyContext {
    /// rustc SourceFile.start_pos, explicitly supplied rather than inferred
    /// from the first generated name. Parser spans remain file-relative bytes.
    pub(crate) source_global_start: u32,
    pub(crate) owner_renames: Vec<OwnerRename>,
    pub(crate) callee_renames: Vec<CalleeRename>,
    /// **R304-3 — the producer's stated render of each pending call**, keyed by
    /// the ORIGINAL call's file-relative interval.
    ///
    /// R287-1 replaced this arm's *uniqueness* requirement with an *equality*
    /// one, and R299-2 gave that equality a real text. Where a render is
    /// stated, the structural search below is retired for that call: the
    /// matcher asks whether the tree reads what the producer says it emitted,
    /// which is stricter than re-deriving correspondence from a hand-listed
    /// set of argument equivalences — the set that did not know the K19′ void
    /// carrier and reported 85 absences over correct emissions.
    pub(crate) pending_call_renders: std::collections::BTreeMap<(u32, u32), String>,
}

pub(crate) struct BridgeCustodyInput<'a> {
    pub(crate) original: &'a Inventory,
    pub(crate) emitted: &'a Inventory,
    pub(crate) original_source: &'a str,
    pub(crate) emitted_source: &'a str,
    pub(crate) expectations: &'a [BridgeExpectation],
    pub(crate) context: &'a BridgeCustodyContext,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum ReceiptStatus {
    MatchedRaw,
    MatchedC9,
    WaivedPending,
    InvalidRenderedRole,
    Missing,
    Unresolved,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct BindingWitness {
    pub(crate) owner: String,
    pub(crate) binding_id: usize,
    pub(crate) name: String,
    pub(crate) declaration_span: ByteSpan,
    pub(crate) argument_index: usize,
    pub(crate) generated_kind: GeneratedKind,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct ReceiptResult {
    pub(crate) identity: String,
    pub(crate) status: ReceiptStatus,
    pub(crate) reason: String,
    pub(crate) original_call: Option<ByteSpan>,
    pub(crate) emitted_call: Option<ByteSpan>,
    pub(crate) argument_indices: Vec<usize>,
    pub(crate) bindings: Vec<BindingWitness>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct TreeOnlyWitness {
    pub(crate) owner: String,
    pub(crate) binding_id: usize,
    pub(crate) name: String,
    pub(crate) declaration_span: ByteSpan,
    /// None records an unclaimed declaration without an identified call use.
    pub(crate) call_span: Option<ByteSpan>,
    pub(crate) argument_index: Option<usize>,
    pub(crate) reason: String,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct BridgeCustodyReport {
    pub(crate) data: bool,
    pub(crate) rows: Vec<ReceiptResult>,
    pub(crate) tree_only: Vec<TreeOnlyWitness>,
    pub(crate) issues: Vec<String>,
}

type MatchResult<T> = Result<T, String>;

fn expression(text: &str) -> MatchResult<ast::ptr::P<ast::Expr>> {
    let source = format!("fn __custody() {{ let __value = {text}; }}");
    let session = ParseSess::new(rustc_driver::DEFAULT_LOCALE_RESOURCES.to_vec());
    let krate =
        super::slice_use_inventory_tests::parse_crate(&session, "custody-expression.rs", &source)?;
    let [item] = krate.items.as_slice() else { return Err("expression-fragment-items".into()) };
    let ast::ItemKind::Fn(function) = &item.kind else {
        return Err("expression-fragment-function".into());
    };
    let body = function.body.as_ref().ok_or("expression-fragment-body")?;
    let [statement] = body.stmts.as_slice() else {
        return Err("expression-fragment-statements".into());
    };
    let ast::StmtKind::Let(local) = &statement.kind else {
        return Err("expression-fragment-local".into());
    };
    let ast::LocalKind::Init(initializer) = &local.kind else {
        return Err("expression-fragment-initializer".into());
    };
    Ok(initializer.clone())
}

fn unparen(mut expression: &ast::Expr) -> &ast::Expr {
    while let ast::ExprKind::Paren(inner) = &expression.kind {
        expression = inner;
    }
    expression
}

fn expression_key(expression: &ast::Expr) -> String {
    struct Parens;
    impl MutVisitor for Parens {
        fn visit_expr(&mut self, expression: &mut ast::Expr) {
            rustc_ast::mut_visit::walk_expr(self, expression);
            while let ast::ExprKind::Paren(inner) = &expression.kind {
                *expression = (**inner).clone();
            }
        }
    }
    let mut normalized = expression.clone();
    Parens.visit_expr(&mut normalized);
    pprust::expr_to_string(&normalized)
}

fn same_expression(left: &str, right: &str) -> MatchResult<bool> {
    Ok(expression_key(&*expression(left)?) == expression_key(&*expression(right)?))
}

fn path(expression: &ast::Expr) -> Option<String> {
    let ast::ExprKind::Path(None, path) = &unparen(expression).kind else { return None };
    Some(
        path.segments
            .iter()
            .filter(|segment| segment.ident.name != rustc_span::kw::PathRoot)
            .map(|segment| segment.ident.name.to_string())
            .collect::<Vec<_>>()
            .join("::"),
    )
}

/// Only the reborrow surrounding a selected view is stripped. An arbitrary
/// dereference, cast, call, or arithmetic in the source operand is preserved.
fn view_operand(mut expression: &ast::Expr) -> &ast::Expr {
    loop {
        expression = unparen(expression);
        let ast::ExprKind::AddrOf(ast::BorrowKind::Ref, _, inner) = &expression.kind else { break };
        let ast::ExprKind::Unary(ast::UnOp::Deref, base) = &unparen(inner).kind else { break };
        expression = base;
    }
    expression
}

/// **R306-1(ii) — the K19′ carrier replaced the original's raw cast, so the
/// comparison peels that cast on BOTH sides.**
///
/// `raw_initializer_matches` already peels a raw-pointer cast off the emitted
/// initializer; the original kept its own, so `ann` was compared against
/// `ann as *const libc::c_void` and ten correct void carriers over four
/// programs read as `pending-source-view-correspondence-unbuilt`.
///
/// Strict, and for the same reason as the arm above: **only** raw-pointer
/// casts are peeled. A cast to any other type is a different value and still
/// refuses.
fn peel_raw_pointer_casts(mut expression: &ast::Expr) -> &ast::Expr {
    loop {
        expression = unparen(expression);
        let ast::ExprKind::Cast(inner, ty) = &expression.kind else {
            break;
        };
        if !matches!(ty.kind, ast::TyKind::Ptr(_)) {
            break;
        }
        expression = inner;
    }
    expression
}

fn same_view_operand(expression: &ast::Expr, original: &ast::Expr) -> bool {
    expression_key(view_operand(peel_raw_pointer_casts(expression)))
        == expression_key(view_operand(peel_raw_pointer_casts(original)))
}

fn raw_initializer_matches(initializer: &ast::Expr, original: &ast::Expr) -> bool {
    let initializer = unparen(initializer);
    if expression_key(initializer) == expression_key(original) {
        return true;
    }
    match &initializer.kind {
        ast::ExprKind::Cast(inner, ty) if matches!(ty.kind, ast::TyKind::Ptr(_)) => {
            raw_initializer_matches(inner, original)
        }
        ast::ExprKind::Call(callee, arguments)
            if arguments.len() == 1
                && matches!(
                    path(callee).as_deref(),
                    Some(
                        "core::ptr::from_ref"
                            | "core::ptr::from_mut"
                            | "std::ptr::from_ref"
                            | "std::ptr::from_mut"
                    )
                ) =>
        {
            same_view_operand(&arguments[0], original)
        }
        ast::ExprKind::MethodCall(method) => {
            let receiver = &method.receiver;
            let arguments = &method.args;
            match method.seg.ident.name.as_str() {
                "as_ptr" | "as_mut_ptr" if arguments.is_empty() => {
                    same_view_operand(receiver, original)
                }
                "cast" | "cast_mut" | "cast_const" if arguments.is_empty() => {
                    raw_initializer_matches(receiver, original)
                }
                "map_or" if arguments.len() == 2 => {
                    let ast::ExprKind::MethodCall(access) = &unparen(receiver).kind else {
                        return false;
                    };
                    if !access.args.is_empty()
                        || !matches!(
                            access.seg.ident.name.as_str(),
                            "as_deref" | "as_deref_mut" | "as_ref" | "as_mut"
                        )
                        || !same_view_operand(&access.receiver, original)
                    {
                        return false;
                    }
                    let ast::ExprKind::Call(null, null_args) = &unparen(&arguments[0]).kind else {
                        return false;
                    };
                    if !null_args.is_empty()
                        || !matches!(
                            path(null).as_deref(),
                            Some(
                                "core::ptr::null"
                                    | "core::ptr::null_mut"
                                    | "std::ptr::null"
                                    | "std::ptr::null_mut"
                            )
                        )
                    {
                        return false;
                    }
                    if matches!(
                        path(&arguments[1]).as_deref(),
                        Some(
                            "core::ptr::from_ref"
                                | "core::ptr::from_mut"
                                | "std::ptr::from_ref"
                                | "std::ptr::from_mut"
                        )
                    ) {
                        return true;
                    }
                    let ast::ExprKind::Closure(closure) = &unparen(&arguments[1]).kind else {
                        return false;
                    };
                    let [parameter] = closure.fn_decl.inputs.as_slice() else { return false };
                    let ast::PatKind::Ident(_, name, None) = &parameter.pat.kind else {
                        return false;
                    };
                    let ast::ExprKind::MethodCall(project) = &unparen(&closure.body).kind else {
                        return false;
                    };
                    project.args.is_empty()
                        && matches!(project.seg.ident.name.as_str(), "as_ptr" | "as_mut_ptr")
                        && path(&project.receiver).as_deref() == Some(name.name.as_str())
                }
                _ => false,
            }
        }
        _ => false,
    }
}

fn optional_raw_view_matches(initializer: &ast::Expr, original: &ast::Expr) -> bool {
    match &unparen(initializer).kind {
        ast::ExprKind::Cast(inner, ty) if matches!(ty.kind, ast::TyKind::Ptr(_)) => {
            optional_raw_view_matches(inner, original)
        }
        ast::ExprKind::MethodCall(method)
            if method.args.is_empty()
                && matches!(
                    method.seg.ident.name.as_str(),
                    "cast" | "cast_mut" | "cast_const"
                ) =>
        {
            optional_raw_view_matches(&method.receiver, original)
        }
        ast::ExprKind::MethodCall(method) if method.seg.ident.name.as_str() == "map_or" => {
            raw_initializer_matches(initializer, original)
        }
        _ => false,
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum PointerType {
    Raw(bool),
    Reference(bool),
    OptionalReference,
    Other,
}

fn parsed_type(text: &str) -> MatchResult<ast::ptr::P<ast::Ty>> {
    let source = format!("fn __custody(__value: {text}) {{}}");
    let session = ParseSess::new(rustc_driver::DEFAULT_LOCALE_RESOURCES.to_vec());
    let krate =
        super::slice_use_inventory_tests::parse_crate(&session, "custody-type.rs", &source)?;
    let [item] = krate.items.as_slice() else { return Err("type-fragment-items".into()) };
    let ast::ItemKind::Fn(function) = &item.kind else {
        return Err("type-fragment-function".into());
    };
    let [parameter] = function.sig.decl.inputs.as_slice() else {
        return Err("type-fragment-parameters".into());
    };
    Ok(parameter.ty.clone())
}

fn pointer_type(text: &str) -> MatchResult<PointerType> {
    let parsed = parsed_type(text)?;
    let mut ty = &*parsed;
    while let ast::TyKind::Paren(inner) = &ty.kind {
        ty = inner;
    }
    Ok(match &ty.kind {
        ast::TyKind::Ptr(pointer) => PointerType::Raw(pointer.mutbl.is_mut()),
        ast::TyKind::Ref(_, reference) => PointerType::Reference(reference.mutbl.is_mut()),
        ast::TyKind::Path(None, path) => {
            let name = path
                .segments
                .iter()
                .filter(|segment| segment.ident.name != rustc_span::kw::PathRoot)
                .map(|segment| segment.ident.name.to_string())
                .collect::<Vec<_>>()
                .join("::");
            let arguments = path
                .segments
                .last()
                .and_then(|segment| segment.args.as_deref());
            if matches!(
                name.as_str(),
                "Option" | "core::option::Option" | "std::option::Option"
            ) && let Some(ast::GenericArgs::AngleBracketed(arguments)) = arguments
                && let [ast::AngleBracketedArg::Arg(ast::GenericArg::Type(payload))] =
                    arguments.args.as_slice()
            {
                let mut payload = &**payload;
                while let ast::TyKind::Paren(inner) = &payload.kind {
                    payload = inner;
                }
                if matches!(payload.kind, ast::TyKind::Ref(..)) {
                    PointerType::OptionalReference
                } else {
                    PointerType::Other
                }
            } else {
                PointerType::Other
            }
        }
        _ => PointerType::Other,
    })
}

fn mapped_owner<'a>(owner: &'a str, context: &'a BridgeCustodyContext) -> MatchResult<&'a str> {
    let rows = context
        .owner_renames
        .iter()
        .filter(|row| row.original_owner == owner)
        .collect::<Vec<_>>();
    match rows.as_slice() {
        [] => Ok(owner),
        [row] if !row.evidence.is_empty() && !row.emitted_owner.is_empty() => {
            Ok(&row.emitted_owner)
        }
        _ => Err(format!("ambiguous-or-unreceipted-owner-mapping:{owner}")),
    }
}

fn target_owner<'a>(
    input: &'a BridgeCustodyInput<'_>,
    expected: &'a BridgeExpectation,
) -> MatchResult<&'a super::bridge_custody_syntax::Function> {
    let owner = mapped_owner(&expected.callee, input.context)?;
    let functions = input
        .emitted
        .functions
        .iter()
        .filter(|function| function.owner == owner)
        .collect::<Vec<_>>();
    match functions.as_slice() {
        [function] => Ok(function),
        _ => Err(format!("callee-declaration-not-unique:{owner}")),
    }
}

fn original_call<'a>(
    input: &'a BridgeCustodyInput<'_>,
    expected: &BridgeExpectation,
) -> MatchResult<(&'a Call, Vec<usize>)> {
    let candidates = input
        .original
        .calls
        .iter()
        .filter(|call| call.owner == expected.caller)
        .filter(|call| match &expected.anchor {
            SiteAnchor::Call { span, .. } => call.span == *span,
            SiteAnchor::Argument {
                span,
                argument_index,
            } => call
                .arguments
                .get(*argument_index)
                .is_some_and(|argument| argument.span == *span),
        })
        .collect::<Vec<_>>();
    let [call] = candidates.as_slice() else {
        return Err("original-call-anchor-not-unique".into());
    };
    let indices = match &expected.anchor {
        SiteAnchor::Call {
            argument_indices, ..
        } => argument_indices.clone(),
        SiteAnchor::Argument { argument_index, .. } => vec![*argument_index],
    };
    if indices.iter().any(|index| *index >= call.arguments.len())
        || indices.iter().copied().collect::<BTreeSet<_>>().len() != indices.len()
    {
        return Err("invalid-or-duplicate-argument-indices".into());
    }
    if indices.is_empty() && expected.kind != BridgeKind::PairCopySnapshot {
        return Err("missing-argument-indices".into());
    }
    for argument in &call.arguments {
        if input
            .original_source
            .get(argument.span.lo as usize..argument.span.hi as usize)
            != Some(argument.text.as_str())
        {
            return Err("original-inventory-source-mismatch".into());
        }
    }
    Ok((call, indices))
}

fn emitted_candidates<'a>(
    input: &'a BridgeCustodyInput<'_>,
    expected: &BridgeExpectation,
    original: &Call,
) -> MatchResult<Vec<&'a Call>> {
    let owner = mapped_owner(&expected.caller, input.context)?;
    if input
        .original
        .functions
        .iter()
        .filter(|function| function.owner == expected.caller)
        .count()
        != 1
        || input
            .emitted
            .functions
            .iter()
            .filter(|function| function.owner == owner)
            .count()
            != 1
    {
        return Err("caller-declaration-not-unique".into());
    }
    let renames = input
        .context
        .callee_renames
        .iter()
        .filter(|row| {
            row.original_caller == expected.caller
                && row.original_callee_text == original.callee_text
        })
        .collect::<Vec<_>>();
    let callee_text = match renames.as_slice() {
        [] => original.callee_text.as_str(),
        [row] if !row.evidence.is_empty() => row.emitted_callee_text.as_str(),
        _ => return Err("ambiguous-or-unreceipted-callee-mapping".into()),
    };
    let key = expression_key(&*expression(callee_text)?);
    let mut candidates = Vec::new();
    for call in input
        .emitted
        .calls
        .iter()
        .filter(|call| call.owner == owner && call.arguments.len() == original.arguments.len())
    {
        if expression_key(&*expression(&call.callee_text)?) == key {
            candidates.push(call);
        }
    }
    Ok(candidates)
}

fn binding_at<'a>(
    input: &'a BridgeCustodyInput<'_>,
    call: &'a Call,
    index: usize,
) -> MatchResult<&'a Binding> {
    let argument = call.arguments.get(index).ok_or("emitted-argument-absent")?;
    let binding = argument
        .binding
        .as_ref()
        .ok_or("emitted-argument-binding-unresolved")?;
    if binding.owner != call.owner
        || input.emitted.bindings.get(binding.id) != Some(binding)
        || binding.init_span.is_none()
        || binding.declaration_span.hi > call.span.lo
    {
        return Err("binding-identity-or-before-call-placement-invalid".into());
    }
    if input
        .emitted_source
        .get(argument.span.lo as usize..argument.span.hi as usize)
        != Some(argument.text.as_str())
        || binding
            .init_span
            .and_then(|span| input.emitted_source.get(span.lo as usize..span.hi as usize))
            != binding.init_text.as_deref()
    {
        return Err("emitted-binding-inventory-source-mismatch".into());
    }
    Ok(binding)
}

/// Test seam for R304's correspondence witnesses; the predicate itself stays
/// private to this module.
/// Test seam for R306's void-carrier witness.
#[cfg(test)]
pub(crate) fn whole_subject_uses_for_test(expression: &str, binding: &str) -> bool {
    let Ok(parsed) = expression_for_test(expression) else {
        return false;
    };
    whole_subject_uses(&parsed, binding)
}

#[cfg(test)]
fn expression_for_test(text: &str) -> MatchResult<ast::ptr::P<ast::Expr>> {
    expression(text)
}

#[cfg(test)]
pub(crate) fn local_types_correspond_for_test(
    original: Option<&str>,
    emitted: Option<&str>,
) -> MatchResult<bool> {
    local_types_correspond(original, emitted)
}

fn local_types_correspond(original: Option<&str>, emitted: Option<&str>) -> MatchResult<bool> {
    if original == emitted {
        return Ok(true);
    }
    let (Some(original), Some(emitted)) = (original, emitted) else { return Ok(false) };
    let original = parsed_type(original)?;
    let emitted = parsed_type(emitted)?;
    let mut original = &*original;
    let mut emitted = &*emitted;
    while let ast::TyKind::Paren(inner) = &original.kind {
        original = inner;
    }
    while let ast::TyKind::Paren(inner) = &emitted.kind {
        emitted = inner;
    }
    if pprust::ty_to_string(original) == pprust::ty_to_string(emitted) {
        return Ok(true);
    }
    let ast::TyKind::Ptr(raw) = &original.kind else {
        return Ok(false);
    };
    // **The emitted side has more than one safe form, and this predicate knew
    // one of them.** The protected-form check two arms down already accepts
    // `Option<&…>`; this one accepted only `&T`, so a correctly emitted
    // nullable or fat form read as a binding mismatch — measured on
    // tulipindicators' `line`, `*mut c_char` against
    // `Option<&mut [c_char]>`, the single refusal that failed that program.
    //
    // The identity requirement is unchanged: same pointee text, and the
    // reference may not be mutable where the raw pointer was const. Only the
    // two shapes the emitter actually produces are peeled — an `Option`
    // wrapper, which is how null is represented, and a slice pointee, which
    // carries an extent over the same element type.
    let emitted = match option_inner(emitted) {
        Some(inner) => inner,
        None => emitted,
    };
    let ast::TyKind::Ref(_, reference) = &emitted.kind else {
        return Ok(false);
    };
    if reference.mutbl.is_mut() && !raw.mutbl.is_mut() {
        return Ok(false);
    }
    let mut pointee = &*reference.ty;
    while let ast::TyKind::Paren(inner) = &pointee.kind {
        pointee = inner;
    }
    if let ast::TyKind::Slice(element) = &pointee.kind {
        pointee = element;
    }
    Ok(pprust::ty_to_string(&raw.ty) == pprust::ty_to_string(pointee))
}

/// `Option<T>` → `T`, for the one wrapper the emitter uses to represent null.
fn option_inner(ty: &ast::Ty) -> Option<&ast::Ty> {
    let ast::TyKind::Path(None, path) = &ty.kind else {
        return None;
    };
    let segment = path.segments.last()?;
    if segment.ident.name.as_str() != "Option" {
        return None;
    }
    let ast::GenericArgs::AngleBracketed(arguments) = &**segment.args.as_ref()? else {
        return None;
    };
    let [ast::AngleBracketedArg::Arg(ast::GenericArg::Type(inner))] = arguments.args.as_slice()
    else {
        return None;
    };
    Some(inner)
}

fn span_bindings_correspond(
    input: &BridgeCustodyInput<'_>,
    original_owner: &str,
    original_span: ByteSpan,
    emitted_owner: &str,
    emitted_span: ByteSpan,
    visiting: &mut BTreeSet<(usize, usize)>,
) -> bool {
    let ids = |inventory: &Inventory, owner: &str, span: ByteSpan| {
        inventory
            .uses
            .iter()
            .filter(|usage| {
                usage.owner == owner && span.lo <= usage.span.lo && usage.span.hi <= span.hi
            })
            .map(|usage| usage.binding_id)
            .collect::<BTreeSet<_>>()
    };
    let original_ids = ids(input.original, original_owner, original_span);
    let emitted_ids = ids(input.emitted, emitted_owner, emitted_span);
    for &id in &original_ids {
        let Some(original) = input.original.bindings.get(id) else { return false };
        if emitted_ids
            .iter()
            .filter_map(|id| input.emitted.bindings.get(*id))
            .filter(|emitted| same_source_binding_inner(input, original, emitted, visiting))
            .count()
            != 1
        {
            return false;
        }
    }
    for &id in &emitted_ids {
        let Some(emitted) = input.emitted.bindings.get(id) else { return false };
        if original_ids
            .iter()
            .filter_map(|id| input.original.bindings.get(*id))
            .filter(|original| same_source_binding_inner(input, original, emitted, visiting))
            .count()
            != 1
        {
            return false;
        }
    }
    true
}

fn same_source_binding_inner(
    input: &BridgeCustodyInput<'_>,
    original: &Binding,
    emitted: &Binding,
    visiting: &mut BTreeSet<(usize, usize)>,
) -> bool {
    if original.name != emitted.name
        || mapped_owner(&original.owner, input.context).ok() != Some(emitted.owner.as_str())
    {
        return false;
    }
    let original_parameter = input
        .original
        .functions
        .iter()
        .filter(|function| function.owner == original.owner)
        .flat_map(|function| &function.parameters)
        .find(|parameter| {
            parameter.span == original.declaration_span && parameter.binding == original.name
        });
    if let Some(parameter) = original_parameter {
        return input
            .emitted
            .functions
            .iter()
            .filter(|function| function.owner == emitted.owner)
            .flat_map(|function| &function.parameters)
            .any(|candidate| {
                candidate.index == parameter.index
                    && candidate.span == emitted.declaration_span
                    && candidate.binding == emitted.name
            });
    }
    // A local counterpart needs its actual declaration, explicit compatible
    // type and initializer dependencies. Equal names alone never establish it.
    if input
        .original
        .bindings
        .iter()
        .filter(|binding| binding.owner == original.owner && binding.name == original.name)
        .count()
        != 1
        || input
            .emitted
            .bindings
            .iter()
            .filter(|binding| binding.owner == emitted.owner && binding.name == emitted.name)
            .count()
            != 1
        || !local_types_correspond(original.type_text.as_deref(), emitted.type_text.as_deref())
            .unwrap_or(false)
    {
        return false;
    }
    let pair = (original.id, emitted.id);
    if !visiting.insert(pair) {
        return false;
    }
    let result = match (
        original.init_text.as_deref(),
        emitted.init_text.as_deref(),
        original.init_span,
        emitted.init_span,
    ) {
        (Some(left), Some(right), Some(left_span), Some(right_span)) => {
            (same_expression(left, right).unwrap_or(false)
                || null_initializer_corresponds(left, right, emitted.type_text.as_deref()))
                && span_bindings_correspond(
                    input,
                    &original.owner,
                    left_span,
                    &emitted.owner,
                    right_span,
                    visiting,
                )
        }
        (None, None, None, None) => original.type_text == emitted.type_text,
        _ => false,
    };
    visiting.remove(&pair);
    result
}

/// `None` is how an optional reference spells the null a raw local was
/// initialized with.
///
/// The comparator already knows this two arms away — `PointerType::
/// OptionalReference` and `optional_raw_view_matches` are built on it — and
/// this predicate did not, so a correctly emitted nullable local read as an
/// initializer mismatch. The emitted type must actually be an `Option`, and
/// the original initializer must actually be a null pointer literal; nothing
/// else corresponds.
fn null_initializer_corresponds(original: &str, emitted: &str, emitted_type: Option<&str>) -> bool {
    if emitted.trim() != "None" {
        return false;
    }
    if !emitted_type
        .and_then(|text| parsed_type(text).ok())
        .is_some_and(|ty| option_inner(&ty).is_some())
    {
        return false;
    }
    let Ok(parsed) = expression(original) else {
        return false;
    };
    let mut view = unparen(&parsed);
    while let ast::ExprKind::Cast(inner, _) = &view.kind {
        view = unparen(inner);
    }
    matches!(&view.kind, ast::ExprKind::Lit(literal)
        if literal.kind == ast::token::LitKind::Integer && literal.symbol.as_str() == "0")
}

/// **R295-3, applied to a predicate rather than an arm.** `same_source_binding`
/// answers a bare `bool`, and one refusal in tulipindicators reported two
/// identically named bindings as a mismatch with nothing to read. This names
/// the FIRST condition that refuses; it re-derives nothing the predicate does
/// not itself check, and is only ever called on the failing path.
fn source_binding_divergence(
    input: &BridgeCustodyInput<'_>,
    original: &Binding,
    emitted: &Binding,
) -> String {
    if original.name != emitted.name {
        return format!("name:{}!={}", original.name, emitted.name);
    }
    if mapped_owner(&original.owner, input.context).ok() != Some(emitted.owner.as_str()) {
        return format!("owner:{}!={}", original.owner, emitted.owner);
    }
    let count = |inventory: &Inventory, owner: &str, name: &str| {
        inventory
            .bindings
            .iter()
            .filter(|binding| binding.owner == owner && binding.name == name)
            .count()
    };
    let originals = count(input.original, &original.owner, &original.name);
    let emitteds = count(input.emitted, &emitted.owner, &emitted.name);
    if originals != 1 {
        return format!("original-name-not-unique:{originals}");
    }
    if emitteds != 1 {
        return format!("emitted-name-not-unique:{emitteds}");
    }
    if !local_types_correspond(original.type_text.as_deref(), emitted.type_text.as_deref())
        .unwrap_or(false)
    {
        return format!(
            "type:{}!={}",
            original.type_text.as_deref().unwrap_or("-"),
            emitted.type_text.as_deref().unwrap_or("-")
        );
    }
    match (
        original.init_text.as_deref(),
        emitted.init_text.as_deref(),
        original.init_span,
        emitted.init_span,
    ) {
        (Some(left), Some(right), Some(_), Some(_)) => {
            if !same_expression(left, right).unwrap_or(false)
                && !null_initializer_corresponds(left, right, emitted.type_text.as_deref())
            {
                format!("initializer:{left}!={right}")
            } else {
                "initializer-dependencies".to_owned()
            }
        }
        (None, None, None, None) => "declared-type".to_owned(),
        _ => "initializer-presence".to_owned(),
    }
}

fn same_source_binding(
    input: &BridgeCustodyInput<'_>,
    original: &Binding,
    emitted: &Binding,
) -> bool {
    same_source_binding_inner(input, original, emitted, &mut BTreeSet::new())
}

fn validate_initializer_bindings(
    input: &BridgeCustodyInput<'_>,
    original: &Call,
    index: usize,
    temporary: &Binding,
) -> MatchResult<()> {
    let original_span = original.arguments[index].span;
    let init_span = temporary.init_span.ok_or("initializer-span-absent")?;
    let original_ids = input
        .original
        .uses
        .iter()
        .filter(|usage| {
            usage.owner == original.owner
                && original_span.lo <= usage.span.lo
                && usage.span.hi <= original_span.hi
        })
        .map(|usage| usage.binding_id)
        .collect::<BTreeSet<_>>();
    let emitted_ids = input
        .emitted
        .uses
        .iter()
        .filter(|usage| {
            usage.owner == temporary.owner
                && init_span.lo <= usage.span.lo
                && usage.span.hi <= init_span.hi
        })
        .map(|usage| usage.binding_id)
        .collect::<BTreeSet<_>>();
    for &original_id in &original_ids {
        let original = input
            .original
            .bindings
            .get(original_id)
            .ok_or("original-source-binding-absent")?;
        if emitted_ids
            .iter()
            .filter_map(|id| input.emitted.bindings.get(*id))
            .filter(|emitted| same_source_binding(input, original, emitted))
            .count()
            != 1
        {
            return Err("initializer-original-binding-correspondence-unresolved".into());
        }
    }
    for emitted_id in emitted_ids {
        let emitted = input
            .emitted
            .bindings
            .get(emitted_id)
            .ok_or("emitted-source-binding-absent")?;
        if original_ids
            .iter()
            .filter_map(|id| input.original.bindings.get(*id))
            .filter(|original| same_source_binding(input, original, emitted))
            .count()
            != 1
        {
            return Err("initializer-uses-an-unmatched-or-shadowing-binding".into());
        }
    }
    Ok(())
}

fn witness(binding: &Binding, index: usize, kind: GeneratedKind) -> BindingWitness {
    BindingWitness {
        owner: binding.owner.clone(),
        binding_id: binding.id,
        name: binding.name.clone(),
        declaration_span: binding.declaration_span,
        argument_index: index,
        generated_kind: kind,
    }
}

fn validate_raw(
    input: &BridgeCustodyInput<'_>,
    expected: &BridgeExpectation,
    original: &Call,
    call: &Call,
    indices: &[usize],
) -> MatchResult<Vec<BindingWitness>> {
    let target = target_owner(input, expected)?;
    indices
        .iter()
        .map(|&index| {
            let argument = &call.arguments[index];
            let binding = binding_at(input, call, index)?;
            if argument.form != ArgumentForm::Path
                || binding.generated != Some(GeneratedKind::RawTemporary)
            {
                return Err("raw-view-argument-is-not-its-typed-bound-temporary".into());
            }
            let temporary_type = pointer_type(
                binding
                    .type_text
                    .as_deref()
                    .ok_or("raw-temporary-type-absent")?,
            )?;
            let target_type = pointer_type(
                &target
                    .parameters
                    .get(index)
                    .ok_or("raw-target-parameter-absent")?
                    .type_text,
            )?;
            if !matches!(
                (temporary_type, target_type),
                (PointerType::Raw(_), PointerType::Raw(false))
                    | (PointerType::Raw(true), PointerType::Raw(true))
            ) {
                return Err("raw-view-target-or-temporary-is-not-raw".into());
            }
            let init = expression(
                binding
                    .init_text
                    .as_deref()
                    .ok_or("raw-temporary-initializer-absent")?,
            )?;
            let source = expression(&original.arguments[index].text)?;
            if !raw_initializer_matches(&init, &source) {
                return Err("raw-initializer-source-relation-unbuilt".into());
            }
            validate_initializer_bindings(input, original, index, binding)?;
            Ok(witness(binding, index, GeneratedKind::RawTemporary))
        })
        .collect()
}

fn validate_c9(
    input: &BridgeCustodyInput<'_>,
    expected: &BridgeExpectation,
    original: &Call,
    call: &Call,
    indices: &[usize],
    name: &str,
) -> MatchResult<Vec<BindingWitness>> {
    let target = target_owner(input, expected)?;
    indices
        .iter()
        .map(|&index| {
            let argument = &call.arguments[index];
            let binding = binding_at(input, call, index)?;
            if binding.name != name
                || binding.generated != Some(GeneratedKind::C9Temporary)
                || argument.form != ArgumentForm::AddrOfPath
                || argument.address_kind.as_deref() != Some("ref")
                || argument.address_mutable != Some(false)
            {
                return Err("c9-argument-is-not-the-exact-shared-snapshot-borrow".into());
            }
            let target_type = pointer_type(
                &target
                    .parameters
                    .get(index)
                    .ok_or("c9-target-parameter-absent")?
                    .type_text,
            )?;
            if !matches!(
                target_type,
                PointerType::Reference(false) | PointerType::Raw(false)
            ) {
                return Err("c9-target-is-not-a-shared-or-const-raw-parameter".into());
            }
            let init = expression(
                binding
                    .init_text
                    .as_deref()
                    .ok_or("c9-initializer-absent")?,
            )?;
            let ast::ExprKind::Unary(ast::UnOp::Deref, operand) = &unparen(&init).kind else {
                return Err("c9-initializer-is-not-a-private-read".into());
            };
            let source = expression(&original.arguments[index].text)?;
            if !same_view_operand(operand, &source) {
                return Err("c9-initializer-source-mismatch".into());
            }
            validate_initializer_bindings(input, original, index, binding)?;
            Ok(witness(binding, index, GeneratedKind::C9Temporary))
        })
        .collect()
}

/// This correspondence rule is confined to pending-waiver call matching. It
/// recognizes the existing native slice read, without changing raw/C9 view
/// validation or treating a changed scalar argument as an interchangeable site.
struct PendingScalarRead<'a, 'source> {
    input: &'a BridgeCustodyInput<'source>,
    original_owner: &'a str,
    emitted_owner: &'a str,
    visiting: BTreeSet<(usize, usize)>,
}

fn pending_parameter_index(inventory: &Inventory, binding: &Binding) -> Option<usize> {
    let parameters = inventory
        .functions
        .iter()
        .filter(|function| function.owner == binding.owner)
        .flat_map(|function| &function.parameters)
        .filter(|parameter| {
            parameter.binding == binding.name && parameter.span == binding.declaration_span
        })
        .collect::<Vec<_>>();
    match parameters.as_slice() {
        [parameter] => Some(parameter.index),
        _ => None,
    }
}

fn pending_parameter_element(text: &str, original_raw: bool) -> MatchResult<Option<String>> {
    let source = format!("fn __custody(__value: {text}) {{}}");
    let session = ParseSess::new(rustc_driver::DEFAULT_LOCALE_RESOURCES.to_vec());
    let krate =
        super::slice_use_inventory_tests::parse_crate(&session, "pending-base-type.rs", &source)?;
    let [item] = krate.items.as_slice() else { return Err("pending-base-type-items".into()) };
    let ast::ItemKind::Fn(function) = &item.kind else {
        return Err("pending-base-type-function".into());
    };
    let [parameter] = function.sig.decl.inputs.as_slice() else {
        return Err("pending-base-type-parameters".into());
    };
    let mut ty = &*parameter.ty;
    while let ast::TyKind::Paren(inner) = &ty.kind {
        ty = inner;
    }
    let element = if original_raw {
        let ast::TyKind::Ptr(pointer) = &ty.kind else { return Ok(None) };
        &*pointer.ty
    } else {
        let ast::TyKind::Ref(_, reference) = &ty.kind else { return Ok(None) };
        let mut payload = &*reference.ty;
        while let ast::TyKind::Paren(inner) = &payload.kind {
            payload = inner;
        }
        let ast::TyKind::Slice(element) = &payload.kind else { return Ok(None) };
        &**element
    };
    Ok(Some(pprust::ty_to_string(element)))
}

fn pending_local_names(expression: &ast::Expr) -> BTreeSet<String> {
    struct Names(BTreeSet<String>);
    impl<'ast> rustc_ast::visit::Visitor<'ast> for Names {
        fn visit_expr(&mut self, expression: &'ast ast::Expr) {
            if let Some(name) = path(expression)
                && !name.contains("::")
            {
                self.0.insert(name);
            }
            rustc_ast::visit::walk_expr(self, expression);
        }
    }
    let mut names = Names(BTreeSet::new());
    rustc_ast::visit::Visitor::visit_expr(&mut names, expression);
    names.0
}

impl PendingScalarRead<'_, '_> {
    fn binding(inventory: &Inventory, owner: &str, span: ByteSpan, name: &str) -> Option<Binding> {
        let ids = inventory
            .uses
            .iter()
            .filter(|usage| {
                usage.owner == owner && span.lo <= usage.span.lo && usage.span.hi <= span.hi
            })
            .filter_map(|usage| inventory.bindings.get(usage.binding_id))
            .filter(|binding| binding.name == name && binding.owner == owner)
            .map(|binding| binding.id)
            .collect::<BTreeSet<_>>();
        if ids.len() != 1 {
            return None;
        }
        inventory.bindings.get(*ids.first()?).cloned()
    }

    fn corresponding_bindings(
        &self,
        name: &str,
        original_span: ByteSpan,
        emitted_span: ByteSpan,
    ) -> Option<(Binding, Binding)> {
        Some((
            Self::binding(
                self.input.original,
                self.original_owner,
                original_span,
                name,
            )?,
            Self::binding(self.input.emitted, self.emitted_owner, emitted_span, name)?,
        ))
    }

    fn index_binding(&mut self, original: &Binding, emitted: &Binding) -> MatchResult<bool> {
        if original.name != emitted.name
            || original.type_text != emitted.type_text
            || mapped_owner(&original.owner, self.input.context)? != emitted.owner
        {
            return Ok(false);
        }
        let original_parameter = pending_parameter_index(self.input.original, original);
        let emitted_parameter = pending_parameter_index(self.input.emitted, emitted);
        if original_parameter.is_some() || emitted_parameter.is_some() {
            return Ok(original_parameter.is_some() && original_parameter == emitted_parameter);
        }
        if self
            .input
            .original
            .bindings
            .iter()
            .filter(|binding| binding.owner == original.owner && binding.name == original.name)
            .count()
            != 1
            || self
                .input
                .emitted
                .bindings
                .iter()
                .filter(|binding| binding.owner == emitted.owner && binding.name == emitted.name)
                .count()
                != 1
        {
            return Ok(false);
        }
        let (Some(original_text), Some(emitted_text), Some(original_span), Some(emitted_span)) = (
            original.init_text.as_deref(),
            emitted.init_text.as_deref(),
            original.init_span,
            emitted.init_span,
        ) else {
            return Ok(false);
        };
        let pair = (original.id, emitted.id);
        if !self.visiting.insert(pair) {
            return Err("pending-index-initializer-cycle".into());
        }
        let result = (|| {
            let original_expression = expression(original_text)?;
            let emitted_expression = expression(emitted_text)?;
            self.equivalent(
                &original_expression,
                &emitted_expression,
                original_span,
                emitted_span,
            )
        })();
        self.visiting.remove(&pair);
        result
    }

    fn index_bindings(
        &mut self,
        original: &ast::Expr,
        emitted: &ast::Expr,
        original_span: ByteSpan,
        emitted_span: ByteSpan,
    ) -> MatchResult<bool> {
        if expression_key(original) != expression_key(emitted) {
            return Ok(false);
        }
        let names = pending_local_names(original);
        if names != pending_local_names(emitted) {
            return Ok(false);
        }
        for name in names {
            let Some((original, emitted)) =
                self.corresponding_bindings(&name, original_span, emitted_span)
            else {
                return Ok(false);
            };
            if !self.index_binding(&original, &emitted)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn equivalent(
        &mut self,
        original: &ast::Expr,
        emitted: &ast::Expr,
        original_span: ByteSpan,
        emitted_span: ByteSpan,
    ) -> MatchResult<bool> {
        let original = unparen(original);
        let emitted = unparen(emitted);
        if expression_key(original) == expression_key(emitted) {
            return self.index_bindings(original, emitted, original_span, emitted_span);
        }
        if let (
            ast::ExprKind::Cast(original, original_type),
            ast::ExprKind::Cast(emitted, emitted_type),
        ) = (&original.kind, &emitted.kind)
        {
            if pprust::ty_to_string(original_type) != pprust::ty_to_string(emitted_type) {
                return Ok(false);
            }
            return self.equivalent(original, emitted, original_span, emitted_span);
        }
        let ast::ExprKind::Unary(ast::UnOp::Deref, pointer) = &original.kind else {
            return Ok(false);
        };
        let ast::ExprKind::MethodCall(offset) = &unparen(pointer).kind else { return Ok(false) };
        let ast::ExprKind::Index(emitted_base, emitted_index, _) = &emitted.kind else {
            return Ok(false);
        };
        if offset.seg.ident.name.as_str() != "offset"
            || offset.seg.args.is_some()
            || offset.args.len() != 1
        {
            return Ok(false);
        }
        let Some(base) = path(&offset.receiver).filter(|name| !name.contains("::")) else {
            return Ok(false);
        };
        if path(emitted_base).as_deref() != Some(base.as_str()) {
            return Ok(false);
        }
        let Some((original_binding, emitted_binding)) =
            self.corresponding_bindings(&base, original_span, emitted_span)
        else {
            return Ok(false);
        };
        let Some(original_parameter) =
            pending_parameter_index(self.input.original, &original_binding)
        else {
            return Ok(false);
        };
        if pending_parameter_index(self.input.emitted, &emitted_binding) != Some(original_parameter)
        {
            return Ok(false);
        }
        let (Some(original_type), Some(emitted_type)) = (
            original_binding.type_text.as_deref(),
            emitted_binding.type_text.as_deref(),
        ) else {
            return Ok(false);
        };
        let original_element = pending_parameter_element(original_type, true)?;
        if original_element.is_none()
            || original_element != pending_parameter_element(emitted_type, false)?
        {
            return Ok(false);
        }
        let ast::ExprKind::Cast(original_index, original_index_type) =
            &unparen(&offset.args[0]).kind
        else {
            return Ok(false);
        };
        let ast::ExprKind::Cast(emitted_index, emitted_index_type) = &unparen(emitted_index).kind
        else {
            return Ok(false);
        };
        if pprust::ty_to_string(original_index_type) != "isize"
            || pprust::ty_to_string(emitted_index_type) != "usize"
        {
            return Ok(false);
        }
        self.index_bindings(original_index, emitted_index, original_span, emitted_span)
    }
}

fn pending_carrier_witnesses(
    input: &BridgeCustodyInput<'_>,
    expected: &BridgeExpectation,
    original: &Call,
    call: &Call,
    index: usize,
    binding: &Binding,
) -> MatchResult<Vec<BindingWitness>> {
    let mut witnesses = Vec::new();
    for companion in input.expectations.iter().filter(|row| {
        row.kind != BridgeKind::SiblingOverlapPending
            && row.caller == expected.caller
            && row.callee == expected.callee
    }) {
        if companion.kind == BridgeKind::PairCopySnapshot
            && expected.c9_stamp.is_some()
            && companion.c9_stamp != expected.c9_stamp
        {
            continue;
        }
        let mut row = ReceiptResult {
            identity: companion.identity.clone(),
            status: ReceiptStatus::Unresolved,
            reason: String::new(),
            original_call: None,
            emitted_call: None,
            argument_indices: Vec::new(),
            bindings: Vec::new(),
        };
        if match_receipt(input, companion, &mut row).is_err()
            || row.original_call != Some(original.span)
            || row.emitted_call != Some(call.span)
            || !matches!(
                row.status,
                ReceiptStatus::MatchedRaw | ReceiptStatus::MatchedC9
            )
        {
            continue;
        }
        for witness in row.bindings.into_iter().filter(|witness| {
            witness.binding_id == binding.id
                && witness.owner == binding.owner
                && witness.argument_index == index
        }) {
            if !witnesses.contains(&witness) {
                witnesses.push(witness);
            }
        }
    }
    if witnesses.len() != 1 {
        return Err("pending-generated-carrier-lacks-exact-ordinary-receipt".into());
    }
    Ok(witnesses)
}

/// **R306-1(ii) — the K19′ void carrier is the whole subject, cast.**
///
/// `p as *const libc::c_void` reaches a void position as a cast OF the subject,
/// not as a different source, and the ledger's `WholeSubject` claim is right
/// about it. The comparator compared the whole expression to the binding's path
/// and so refused ten correct emissions over four programs.
///
/// Strict: only **raw-pointer** casts are peeled — a cast to any other type is
/// a different value — and what remains must be the binding's own path.
fn whole_subject_uses(expression: &ast::Expr, binding: &str) -> bool {
    let mut view = unparen(expression);
    while let ast::ExprKind::Cast(inner, ty) = &view.kind {
        if !matches!(ty.kind, ast::TyKind::Ptr(_)) {
            return false;
        }
        view = unparen(inner);
    }
    path(view).as_deref() == Some(binding)
}

fn projected_referent_uses(expression: &ast::Expr, binding: &str) -> bool {
    // **R304-2's seal has a SECOND SPELLING, and the comparator knows it as
    // strictly as the decision layer does.** `((*binding).field).as_ptr()` is
    // the same depth-1 projection of the protected referent, viewed as a
    // pointer by an array or slice method instead of borrowed with `&`. The
    // arm is exact: the receiver must be a place, the walk must reach the
    // binding, and the depth must be one — a loaded raw field value still
    // cannot pass, because its walk sees no dereference of the binding.
    let mut view = unparen(expression);
    while let ast::ExprKind::Cast(inner, _) = &view.kind {
        view = unparen(inner);
    }
    if let ast::ExprKind::MethodCall(method) = &view.kind
        && method.args.is_empty()
        && matches!(method.seg.ident.name.as_str(), "as_ptr" | "as_mut_ptr")
    {
        let mut place = unparen(&method.receiver);
        let mut dereferences = 0;
        loop {
            match &place.kind {
                ast::ExprKind::Field(base, _) => place = unparen(base),
                ast::ExprKind::Unary(ast::UnOp::Deref, base) => {
                    dereferences += 1;
                    place = unparen(base);
                }
                _ => break,
            }
        }
        return dereferences == 1 && path(place).as_deref() == Some(binding);
    }
    let ast::ExprKind::AddrOf(ast::BorrowKind::Ref, _, place) = &unparen(expression).kind else {
        return false;
    };
    let mut place = unparen(place);
    let mut dereferences = 0;
    loop {
        match &place.kind {
            ast::ExprKind::Field(base, _) => place = unparen(base),
            ast::ExprKind::Unary(ast::UnOp::Deref, base) => {
                dereferences += 1;
                place = unparen(base);
            }
            _ => break,
        }
    }
    // This is a borrow of the protected referent or its fields. A loaded raw
    // field value has no surrounding reference borrow and cannot pass here.
    dereferences == 1 && path(place).as_deref() == Some(binding)
}

fn pending_original_source(
    input: &BridgeCustodyInput<'_>,
    expected: &BridgeExpectation,
    original: &Call,
    index: usize,
    expression: &ast::Expr,
) -> MatchResult<Binding> {
    let span = original.arguments[index].span;
    let Some(metadata) = &expected.pending_source else {
        let name = path(expression)
            .filter(|name| !name.contains("::"))
            .ok_or("pending-original-source-is-not-a-binding")?;
        return PendingScalarRead::binding(input.original, &original.owner, span, &name)
            .ok_or_else(|| "pending-original-source-binding-unresolved".into());
    };
    if matches!(
        &metadata.shape,
        PendingSourceShape::NativeReturnExpression { .. }
            | PendingSourceShape::NativeReturnExpressionNested { .. }
    ) {
        return Err("pending-native-expression-carrier-unbuilt".into());
    }
    let name = metadata
        .binding
        .as_deref()
        .ok_or("pending-source-binding-name-absent")?;
    let binding_span = metadata
        .binding_span
        .ok_or("pending-source-binding-span-absent")?;
    let candidates = input
        .original
        .bindings
        .iter()
        .filter(|binding| {
            binding.owner == original.owner
                && binding.name == name
                && binding_span.lo <= binding.binding_span.lo
                && binding.binding_span.hi <= binding_span.hi
        })
        .collect::<Vec<_>>();
    let [binding] = candidates.as_slice() else {
        return Err("pending-protected-binding-metadata-not-unique".into());
    };
    let used = PendingScalarRead::binding(input.original, &original.owner, span, name)
        .is_some_and(|used| used.id == binding.id && used == **binding);
    let shape_matches = match &metadata.shape {
        PendingSourceShape::WholeSubject => whole_subject_uses(expression, name),
        PendingSourceShape::ProjectedReferent => projected_referent_uses(expression, name),
        PendingSourceShape::NativeReturnExpression { .. }
        | PendingSourceShape::NativeReturnExpressionNested { .. } => {
            return Err("pending-native-expression-carrier-unbuilt".into());
        }
    };
    // R295-3's rule: two independent conditions, two names.
    if !used {
        return Err(format!(
            "pending-source-operand-binding-not-the-declared-one:{name}"
        ));
    }
    if !shape_matches {
        return Err(format!(
            "pending-source-operand-shape-mismatch:{name}:{:?}",
            metadata.shape
        ));
    }
    Ok((**binding).clone())
}

fn pending_selected_argument(
    input: &BridgeCustodyInput<'_>,
    expected: &BridgeExpectation,
    original: &Call,
    call: &Call,
    index: usize,
) -> MatchResult<Vec<BindingWitness>> {
    let target = target_owner(input, expected)?;
    if !matches!(
        pointer_type(
            &target
                .parameters
                .get(index)
                .ok_or("pending-target-absent")?
                .type_text
        )?,
        PointerType::Raw(_)
    ) {
        return Err("pending-target-is-not-raw".into());
    }
    if expected.pending_source.as_ref().is_some_and(|source| {
        matches!(
            &source.shape,
            PendingSourceShape::NativeReturnExpression { .. }
                | PendingSourceShape::NativeReturnExpressionNested { .. }
        )
    }) {
        return pending_native_expression(input, expected, original, call, index);
    }
    let original_argument = &original.arguments[index];
    let original_expression = expression(&original_argument.text)?;
    let original_binding =
        pending_original_source(input, expected, original, index, &original_expression)?;
    let name = original_binding.name.as_str();
    let argument = &call.arguments[index];
    let mut witnesses = Vec::new();
    let source_span = if argument
        .binding
        .as_ref()
        .is_some_and(|binding| binding.generated.is_some())
    {
        let placed = binding_at(input, call, index)?;
        witnesses = pending_carrier_witnesses(input, expected, original, call, index, placed)?;
        placed
            .init_span
            .ok_or("pending-carrier-initializer-absent")?
    } else {
        let emitted_expression = expression(&argument.text)?;
        if !raw_initializer_matches(&emitted_expression, &original_expression) {
            return Err("pending-source-view-correspondence-unbuilt".into());
        }
        argument.span
    };
    let emitted_binding = PendingScalarRead::binding(input.emitted, &call.owner, source_span, name)
        .ok_or("pending-protected-source-binding-unresolved")?;
    let protected_form = match pointer_type(
        emitted_binding
            .type_text
            .as_deref()
            .ok_or("pending-reference-type-absent")?,
    )? {
        PointerType::Reference(_) => true,
        PointerType::OptionalReference => {
            let source_text = input
                .emitted_source
                .get(source_span.lo as usize..source_span.hi as usize)
                .ok_or("pending-nullable-source-span-invalid")?;
            optional_raw_view_matches(&*expression(source_text)?, &original_expression)
        }
        PointerType::Raw(_) | PointerType::Other => false,
    };
    // **R295-3's rule, applied here too.** One name covered two independent
    // conditions — the emitted binding is not the original's, and the emitted
    // binding's declared form is not a protected one — and a reader could not
    // tell which had fired.
    if !same_source_binding(input, &original_binding, &emitted_binding) {
        return Err(format!(
            "pending-protected-source-binding-mismatch:{name}:{}",
            source_binding_divergence(input, &original_binding, &emitted_binding)
        ));
    }
    if !protected_form {
        return Err(format!(
            "pending-protected-source-not-a-reference:{name}:{}",
            emitted_binding.type_text.as_deref().unwrap_or("-")
        ));
    }
    Ok(witnesses)
}

fn pending_native_view(
    template: &str,
    form: &str,
    temporary: &str,
    target: &ast::Ty,
) -> MatchResult<String> {
    let ast::TyKind::Ptr(pointer) = &target.kind else {
        return Err("pending-native-expression-view-target-not-raw".into());
    };
    let mutable = pointer.mutbl.is_mut();
    let pointee = pprust::ty_to_string(&pointer.ty);
    let text = match (template, form, mutable) {
        ("ref-shared-to-raw-const", "ref-shared", false) => {
            format!("core::ptr::from_ref({temporary})")
        }
        ("ref-mut-to-raw-const", "ref-mut", false) => format!("core::ptr::from_ref(&*{temporary})"),
        ("ref-mut-to-raw-mut", "ref-mut", true) => {
            format!("core::ptr::from_mut(&mut *{temporary})")
        }
        ("shared-ref-to-mut-raw", "ref-shared", true) => {
            format!("core::ptr::from_ref({temporary}).cast_mut()")
        }
        ("slice-mut-to-raw-mut", "slice-mut", true) => format!("{temporary}.as_mut_ptr()"),
        ("slice-to-raw-const", "slice-shared" | "slice-mut", false) => {
            format!("{temporary}.as_ptr()")
        }
        ("slice-to-raw-mut", "slice-shared", true) => format!("{temporary}.as_ptr().cast_mut()"),
        ("option-to-raw-null-map", "opt-ref-mut", true) => format!(
            "{temporary}.as_deref_mut().map_or(core::ptr::null_mut::<{pointee}>(), core::ptr::from_mut)"
        ),
        ("option-to-raw-null-map", "opt-ref-shared" | "opt-ref-mut", false) => format!(
            "{temporary}.as_deref().map_or(core::ptr::null::<{pointee}>(), core::ptr::from_ref)"
        ),
        ("option-to-raw-null-map", "opt-ref-shared", true) => format!(
            "{temporary}.as_deref().map_or(core::ptr::null_mut::<{pointee}>(), |value| core::ptr::from_ref(value).cast_mut())"
        ),
        ("option-to-raw-null-map", "opt-slice-mut", true) => format!(
            "{temporary}.as_deref_mut().map_or(core::ptr::null_mut::<{pointee}>(), |slice| slice.as_mut_ptr())"
        ),
        ("option-to-raw-null-map", "opt-slice-shared" | "opt-slice-mut", false) => format!(
            "{temporary}.as_deref().map_or(core::ptr::null::<{pointee}>(), |slice| slice.as_ptr())"
        ),
        ("option-to-raw-null-map", "opt-slice-shared", true) => format!(
            "{temporary}.as_deref().map_or(core::ptr::null_mut::<{pointee}>(), |slice| slice.as_ptr().cast_mut())"
        ),
        _ => return Err("pending-native-expression-view-template-unbuilt".into()),
    };
    Ok(text)
}

/// Correspondence for the existing raw-to-slice source-call adapter. The
/// named fallback extent remains owned by its adapter receipt and waiver;
/// recognizing this syntax creates no slice-length evidence.
fn pending_native_slice_argument(
    input: &BridgeCustodyInput<'_>,
    source_function: &str,
    original: &Call,
    emitted: &Call,
    position: usize,
    target: &super::bridge_custody_syntax::Function,
) -> MatchResult<bool> {
    let before = &original.arguments[position];
    let after = &emitted.arguments[position];
    let after_expression = expression(&after.text)?;
    let ast::ExprKind::Call(callee, arguments) = &unparen(&after_expression).kind else {
        return Ok(false);
    };
    let constructor_mutable = match path(callee).as_deref() {
        Some("core::slice::from_raw_parts") => false,
        Some("core::slice::from_raw_parts_mut") => true,
        _ => return Ok(false),
    };
    let [operand, extent] = arguments.as_slice() else { return Ok(false) };
    if path(extent).as_deref() != Some("crate::FALLBACK_SLICE_EXTENT")
        || expression_key(operand) != expression_key(&*expression(&before.text)?)
    {
        return Ok(false);
    }
    let original_targets = input
        .original
        .functions
        .iter()
        .filter(|function| function.owner == source_function)
        .collect::<Vec<_>>();
    let [original_target] = original_targets.as_slice() else { return Ok(false) };
    let (Some(before_parameter), Some(after_parameter)) = (
        original_target.parameters.get(position),
        target.parameters.get(position),
    ) else {
        return Ok(false);
    };
    let before_type = parsed_type(&before_parameter.type_text)?;
    let after_type = parsed_type(&after_parameter.type_text)?;
    let (ast::TyKind::Ptr(pointer), ast::TyKind::Ref(_, reference)) =
        (&before_type.kind, &after_type.kind)
    else {
        return Ok(false);
    };
    let ast::TyKind::Slice(element) = &reference.ty.kind else { return Ok(false) };
    if reference.mutbl.is_mut() != constructor_mutable
        || (constructor_mutable && !pointer.mutbl.is_mut())
        || pprust::ty_to_string(&pointer.ty) != pprust::ty_to_string(element)
    {
        return Ok(false);
    }
    // Use the pinned inventory's actual operand span for scope correspondence,
    // never the fresh fragment parser's offsets or a guessed binding name.
    let constructors = input
        .emitted
        .calls
        .iter()
        .filter(|call| {
            call.owner == emitted.owner
                && after.span.lo <= call.span.lo
                && call.span.hi <= after.span.hi
                && call.callee_path.as_deref() == path(callee).as_deref()
                && call.arguments.len() == 2
        })
        .collect::<Vec<_>>();
    let [constructor] = constructors.as_slice() else { return Ok(false) };
    let text = input
        .emitted_source
        .get(constructor.span.lo as usize..constructor.span.hi as usize)
        .ok_or("pending-native-slice-constructor-span-invalid")?;
    if !same_expression(text, &after.text)?
        || !same_expression(&constructor.arguments[0].text, &before.text)?
    {
        return Ok(false);
    }
    Ok(span_bindings_correspond(
        input,
        &original.owner,
        before.span,
        &emitted.owner,
        constructor.arguments[0].span,
        &mut BTreeSet::new(),
    ))
}

/// The one rule that separates the two native-expression carriers.
///
/// The bare carrier edits the argument itself, so its edit interval must BE the
/// argument. The nested carrier edits a call the argument contains, so its
/// interval must sit **strictly** inside: equality would mean it had claimed
/// the whole argument, and anything outside means the receipt does not describe
/// the edit that was made. Neither arm may accept what the other describes --
/// that is what keeps custody catching carrier drift after the shape was added.
pub(crate) fn native_expression_interval_ok(
    argument_span: &ByteSpan,
    source_call_span: &ByteSpan,
    nested: bool,
) -> bool {
    if nested {
        argument_span.lo <= source_call_span.lo
            && source_call_span.hi <= argument_span.hi
            && source_call_span != argument_span
    } else {
        source_call_span == argument_span
    }
}

fn pending_native_expression(
    input: &BridgeCustodyInput<'_>,
    expected: &BridgeExpectation,
    original: &Call,
    call: &Call,
    index: usize,
) -> MatchResult<Vec<BindingWitness>> {
    let metadata = expected
        .pending_source
        .as_ref()
        .ok_or("pending-native-expression-source-missing")?;
    let (
        argument_span,
        source_call_span,
        source_function,
        source_form,
        source_type,
        temporary,
        template,
        nested,
    ) = match &metadata.shape {
        PendingSourceShape::NativeReturnExpression {
            argument_span,
            source_call_span,
            source_function,
            source_form,
            source_type,
            temporary,
            template,
            ..
        } => (
            argument_span,
            source_call_span,
            source_function,
            source_form,
            source_type,
            temporary,
            template,
            false,
        ),
        PendingSourceShape::NativeReturnExpressionNested {
            argument_span,
            source_call_span,
            source_function,
            source_form,
            source_type,
            temporary,
            template,
            ..
        } => (
            argument_span,
            source_call_span,
            source_function,
            source_form,
            source_type,
            temporary,
            template,
            true,
        ),
        _ => return Err("pending-native-expression-source-kind".into()),
    };
    // The two shapes differ in exactly one rule and share every other. The
    // bare carrier requires the edit interval to BE the argument; the nested
    // one requires it to sit strictly inside, which is what keeps the
    // enclosing cast, projection or arithmetic in the caller's hands.
    let interval_ok = native_expression_interval_ok(argument_span, source_call_span, nested);
    if metadata.binding.is_some()
        || metadata.binding_span.is_some()
        || *argument_span != original.arguments[index].span
        || !interval_ok
        || !temporary.starts_with("__crat_outbound_return_")
    {
        return Err("pending-native-expression-source-identity-mismatch".into());
    }
    let sources = input
        .original
        .calls
        .iter()
        .filter(|source| source.owner == original.owner && source.span == *source_call_span)
        .collect::<Vec<_>>();
    let [source] = sources.as_slice() else {
        return Err("pending-native-expression-source-call-not-unique".into());
    };
    let source_path = path(&*expression(&source.callee_text)?)
        .ok_or("pending-native-expression-source-not-direct")?;
    let relative = original
        .owner
        .rsplit_once("::")
        .map(|(module, _)| format!("{module}::{source_path}"));
    if source_path != *source_function && relative.as_ref() != Some(source_function)
        || input
            .original
            .functions
            .iter()
            .filter(|function| function.owner == *source_function)
            .count()
            != 1
    {
        return Err("pending-native-expression-source-callee-mismatch".into());
    }
    let argument = &call.arguments[index];
    if input
        .emitted_source
        .get(argument.span.lo as usize..argument.span.hi as usize)
        != Some(argument.text.as_str())
    {
        return Err("pending-native-expression-argument-source-mismatch".into());
    }
    let parsed = expression(&argument.text)?;
    let ast::ExprKind::Block(block, None) = &unparen(&parsed).kind else {
        return Err("pending-native-expression-argument-block-missing".into());
    };
    let [declaration, tail] = block.stmts.as_slice() else {
        return Err("pending-native-expression-carrier-statements".into());
    };
    let (ast::StmtKind::Let(local), ast::StmtKind::Expr(tail)) = (&declaration.kind, &tail.kind)
    else {
        return Err("pending-native-expression-carrier-shape".into());
    };
    let ast::PatKind::Ident(_, name, None) = &local.pat.kind else {
        return Err("pending-native-expression-temporary-pattern".into());
    };
    let (Some(local_type), ast::LocalKind::Init(initializer)) = (&local.ty, &local.kind) else {
        return Err("pending-native-expression-typed-initializer-missing".into());
    };
    let native_type = parsed_type(source_type)?;
    if name.name.as_str() != temporary
        || pprust::ty_to_string(local_type) != pprust::ty_to_string(&native_type)
        || !matches!(
            pointer_type(source_type)?,
            PointerType::Reference(_) | PointerType::OptionalReference
        )
    {
        return Err("pending-native-expression-temporary-type-or-name".into());
    }
    let bindings = input
        .emitted
        .bindings
        .iter()
        .filter(|binding| {
            binding.owner == call.owner
                && binding.name == *temporary
                && argument.span.lo <= binding.declaration_span.lo
                && binding.declaration_span.hi <= argument.span.hi
        })
        .collect::<Vec<_>>();
    let [binding] = bindings.as_slice() else {
        return Err("pending-native-expression-temporary-not-unique".into());
    };
    let init_span = binding
        .init_span
        .ok_or("pending-native-expression-initializer-span-missing")?;
    let init_text = binding
        .init_text
        .as_deref()
        .ok_or("pending-native-expression-initializer-missing")?;
    if input
        .emitted_source
        .get(init_span.lo as usize..init_span.hi as usize)
        != Some(init_text)
        || !same_expression(init_text, &pprust::expr_to_string(initializer))?
        || binding
            .type_text
            .as_deref()
            .map(parsed_type)
            .transpose()?
            .as_ref()
            .is_none_or(|ty| pprust::ty_to_string(ty) != pprust::ty_to_string(&native_type))
    {
        return Err("pending-native-expression-binding-source-mismatch".into());
    }
    let mut source_expected = expected.clone();
    source_expected.callee = source_function.clone();
    let emitted_sources = emitted_candidates(input, &source_expected, source)?;
    let emitted_sources = emitted_sources
        .into_iter()
        .filter(|source| init_span.lo <= source.span.lo && source.span.hi <= init_span.hi)
        .collect::<Vec<_>>();
    let [emitted_source] = emitted_sources.as_slice() else {
        return Err("pending-native-expression-initializer-call-not-unique".into());
    };
    let call_text = input
        .emitted_source
        .get(emitted_source.span.lo as usize..emitted_source.span.hi as usize)
        .ok_or("pending-native-expression-initializer-call-span-invalid")?;
    if !same_expression(init_text, call_text)? {
        return Err("pending-native-expression-initializer-is-not-source-call".into());
    }
    let source_target = target_owner(input, &source_expected)?;
    for (position, (before, after)) in source
        .arguments
        .iter()
        .zip(&emitted_source.arguments)
        .enumerate()
    {
        if !same_expression(&before.text, &after.text)? {
            let before = expression(&before.text)?;
            let after = expression(&after.text)?;
            let borrowed = source_target
                .parameters
                .get(position)
                .map(|parameter| pointer_type(&parameter.type_text))
                .transpose()?
                .is_some_and(|ty| matches!(ty, PointerType::Reference(_)));
            if (!borrowed || !same_view_operand(&after, &before))
                && !pending_native_slice_argument(
                    input,
                    source_function,
                    source,
                    emitted_source,
                    position,
                    source_target,
                )?
            {
                return Err(
                    "pending-native-expression-source-argument-correspondence-unbuilt".into(),
                );
            }
        }
    }
    validate_initializer_bindings(input, original, index, binding)?;
    let ast::ExprKind::Cast(view, raw_type) = &unparen(tail).kind else {
        return Err("pending-native-expression-raw-view-missing".into());
    };
    let target = target_owner(input, expected)?;
    if pointer_type(&pprust::ty_to_string(raw_type))?
        != pointer_type(&target.parameters[index].type_text)?
    {
        return Err("pending-native-expression-raw-target-mismatch".into());
    }
    let expected_view = pending_native_view(template, source_form, temporary, raw_type)?;
    if !same_expression(&pprust::expr_to_string(view), &expected_view)? {
        return Err("pending-native-expression-raw-view-template-mismatch".into());
    }
    let uses = input
        .emitted
        .uses
        .iter()
        .filter(|usage| {
            usage.owner == call.owner
                && argument.span.lo <= usage.span.lo
                && usage.span.hi <= argument.span.hi
                && input
                    .emitted
                    .bindings
                    .get(usage.binding_id)
                    .is_some_and(|binding| binding.name == *temporary)
        })
        .collect::<Vec<_>>();
    let [usage] = uses.as_slice() else {
        return Err("pending-native-expression-view-use-not-unique".into());
    };
    if usage.binding_id != binding.id
        || usage.span.lo < binding.declaration_span.hi
        || usage.context == super::bridge_custody_syntax::UseContext::AssignmentTarget
    {
        return Err("pending-native-expression-view-binding-mismatch".into());
    }
    // Inline pending views already carry their exact argument in the receipt.
    // This safe native temporary is neither a raw nor a C9 temporary.
    Ok(Vec::new())
}

fn pending(
    input: &BridgeCustodyInput<'_>,
    expected: &BridgeExpectation,
    original: &Call,
    candidates: &[&Call],
    indices: &[usize],
) -> MatchResult<(ByteSpan, Vec<BindingWitness>, ReceiptStatus)> {
    if expected.tier != "T2-pending"
        || expected.waiver_id.as_deref()
            != Some("c-aliasing-semantics-at-unsafe-bridges/v2-pending")
    {
        return Err("pending-tier-or-waiver-mismatch".into());
    }
    let target = target_owner(input, expected)?;
    // **R304-3 — the stated render is the claim.**
    if let Some(rendered) = input
        .context
        .pending_call_renders
        .get(&(original.span.lo, original.span.hi))
    {
        let want = super::bridge_custody_export::normalised_tokens(rendered);
        let mut stated = Vec::new();
        for call in candidates {
            let text = input
                .emitted_source
                .get(call.span.lo as usize..call.span.hi as usize)
                .ok_or("pending-call-span-outside-emitted-source")?;
            // **R306-1(ii) — the A5/PAIR composite is stated as ONE unit.**
            //
            // The producer renders the whole hoisting construct the AST layer
            // emitted at this original span — `{ let __crat_a5_raw_N: T = …;
            // callee(…, __crat_a5_raw_N) }` — bound to its stamp. The
            // candidate here is the CALL, which lives inside that block, so an
            // equality against the call's own span can never hold for these
            // sites. The strict arm: the tree must carry the stated composite,
            // and this candidate must be the call within it.
            let have = super::bridge_custody_export::normalised_tokens(text);
            if have != want
                && !(want.contains(&have)
                    && super::bridge_custody_export::normalised_tokens(input.emitted_source)
                        .contains(&want))
            {
                continue;
            }
            let mut witnesses = Vec::new();
            for &index in indices {
                witnesses.extend(pending_selected_argument(
                    input, expected, original, call, index,
                )?);
            }
            stated.push((*call, witnesses));
        }
        // **Duplicates settle by text equality.** Two calls reading what the
        // producer stated both satisfy an equality claim; that is exactly the
        // property R287-1 chose over uniqueness.
        let Some((call, witnesses)) = stated.into_iter().next() else {
            // R295-3: say WHICH absence. A render the file carries somewhere
            // but no candidate does is a candidate-selection question; a
            // render the file does not carry at all means the AST layer never
            // emitted that call, and R306-1(i) deletes such a row rather than
            // keeping a claim the tree cannot answer.
            let in_file = super::bridge_custody_export::normalised_tokens(input.emitted_source)
                .contains(&want);
            return Err(format!(
                "pending-call-render-absent:candidates={}:in-file={in_file}",
                candidates.len()
            ));
        };
        return Ok((call.span, witnesses, ReceiptStatus::WaivedPending));
    }
    let mut matching = Vec::new();
    for call in candidates {
        let mut same = true;
        let mut witnesses = Vec::new();
        let mut scalar_read = PendingScalarRead {
            input,
            original_owner: &original.owner,
            emitted_owner: &call.owner,
            visiting: BTreeSet::new(),
        };
        for (index, (argument, original_argument)) in
            call.arguments.iter().zip(&original.arguments).enumerate()
        {
            if indices.contains(&index) {
                match pending_selected_argument(input, expected, original, call, index) {
                    Ok(selected) => witnesses.extend(selected),
                    Err(_) => same = false,
                }
                continue;
            }
            if !same_expression(&argument.text, &original_argument.text)? {
                let original_expression = expression(&original_argument.text)?;
                let emitted_expression = expression(&argument.text)?;
                let native_read = scalar_read.equivalent(
                    &original_expression,
                    &emitted_expression,
                    original_argument.span,
                    argument.span,
                )?;
                let primary_reborrow = match (
                    &unparen(&emitted_expression).kind,
                    target
                        .parameters
                        .get(index)
                        .map(|parameter| pointer_type(&parameter.type_text))
                        .transpose()?,
                ) {
                    (
                        ast::ExprKind::AddrOf(ast::BorrowKind::Ref, mutable, _),
                        Some(PointerType::Reference(target_mutable)),
                    ) => {
                        (!target_mutable || mutable.is_mut())
                            && same_view_operand(&emitted_expression, &original_expression)
                            && span_bindings_correspond(
                                input,
                                &original.owner,
                                original_argument.span,
                                &call.owner,
                                argument.span,
                                &mut BTreeSet::new(),
                            )
                    }
                    _ => false,
                };
                same &= native_read || primary_reborrow;
            }
        }
        if same {
            matching.push((*call, witnesses));
        }
    }
    // **R295-3 — the two failures this arm can have are not the same failure.**
    //
    // One message covered both an EMPTY match set — no corresponding call in
    // the tree, a real custody failure — and a set of two or more, which is
    // the uniqueness requirement R287-1 ruled custody never needed. A reader
    // of `pending-call-correspondence-not-unique` could not tell which had
    // happened, and the two want opposite dispositions.
    let [(call, witnesses)] = matching.as_slice() else {
        return Err(if matching.is_empty() {
            "pending-call-correspondence-absent".into()
        } else {
            format!("pending-call-correspondence-not-unique:{}", matching.len())
        });
    };
    Ok((call.span, witnesses.clone(), ReceiptStatus::WaivedPending))
}

/// A raw temporary is evidence of a raw intermediate, not of the callee's
/// terminal role. Nested AST uses can establish the exact binding even when
/// the whole argument is a reborrow, slice construction, or Option view.
fn invalid_rendered_role(
    input: &BridgeCustodyInput<'_>,
    expected: &BridgeExpectation,
    original: &Call,
    candidates: &[&Call],
    indices: &[usize],
    stamp: u32,
) -> MatchResult<Option<(ByteSpan, Vec<BindingWitness>, String)>> {
    let target = target_owner(input, expected)?;
    let mut invalid_calls = Vec::new();
    for call in candidates {
        let mut witnesses = Vec::new();
        let mut reasons = Vec::new();
        for &index in indices {
            let argument = &call.arguments[index];
            let parameter = target
                .parameters
                .get(index)
                .ok_or("role-target-parameter-absent")?;
            if !matches!(
                pointer_type(&parameter.type_text)?,
                PointerType::Reference(_) | PointerType::OptionalReference
            ) {
                continue;
            }
            let pair_name = format!("__crat_pair_raw_{stamp}_{index}");
            let a5_name = format!("__crat_a5_raw_{stamp}_{index}");
            let ids = input
                .emitted
                .uses
                .iter()
                .filter(|usage| {
                    usage.owner == call.owner
                        && argument.span.lo <= usage.span.lo
                        && usage.span.hi <= argument.span.hi
                        && usage.context
                            != super::bridge_custody_syntax::UseContext::AssignmentTarget
                })
                .filter_map(|usage| input.emitted.bindings.get(usage.binding_id))
                .filter(|binding| {
                    binding.owner == call.owner
                        && (binding.name == pair_name || binding.name == a5_name)
                })
                .map(|binding| binding.id)
                .collect::<BTreeSet<_>>();
            if ids.len() > 1 {
                return Err("multiple-stamped-bindings-inside-safe-argument".into());
            }
            let Some(&id) = ids.first() else { continue };
            let binding = &input.emitted.bindings[id];
            if binding.generated != Some(GeneratedKind::RawTemporary)
                || binding.declaration_span.hi > call.span.lo
                || !matches!(
                    pointer_type(
                        binding
                            .type_text
                            .as_deref()
                            .ok_or("role-temporary-type-absent")?
                    )?,
                    PointerType::Raw(_)
                )
            {
                return Err("safe-argument-stamped-binding-is-not-a-placed-raw-temporary".into());
            }
            if input
                .emitted_source
                .get(argument.span.lo as usize..argument.span.hi as usize)
                != Some(argument.text.as_str())
                || binding
                    .init_span
                    .and_then(|span| input.emitted_source.get(span.lo as usize..span.hi as usize))
                    != binding.init_text.as_deref()
            {
                return Err("role-binding-inventory-source-mismatch".into());
            }
            let initializer = expression(
                binding
                    .init_text
                    .as_deref()
                    .ok_or("role-temporary-initializer-absent")?,
            )?;
            let source = expression(&original.arguments[index].text)?;
            if !raw_initializer_matches(&initializer, &source) {
                return Err("role-initializer-source-relation-unbuilt".into());
            }
            validate_initializer_bindings(input, original, index, binding)?;
            witnesses.push(witness(binding, index, GeneratedKind::RawTemporary));
            reasons.push(format!(
                "arg={index};binding-id={id};temporary={};target={};argument={}",
                binding.name, parameter.type_text, argument.text
            ));
        }
        if !witnesses.is_empty() {
            invalid_calls.push((call.span, witnesses, reasons.join(" | ")));
        }
    }
    if invalid_calls.len() > 1 {
        return Err("invalid-role-call-correspondence-not-unique".into());
    }
    Ok(invalid_calls.pop())
}

fn match_receipt(
    input: &BridgeCustodyInput<'_>,
    expected: &BridgeExpectation,
    row: &mut ReceiptResult,
) -> MatchResult<()> {
    let (original, indices) = original_call(input, expected)?;
    row.original_call = Some(original.span);
    row.argument_indices = indices.clone();
    let candidates = emitted_candidates(input, expected, original)?;
    if expected.kind == BridgeKind::SiblingOverlapPending {
        let (span, bindings, status) = pending(input, expected, original, &candidates, &indices)?;
        row.emitted_call = Some(span);
        row.bindings = bindings;
        row.status = status;
        row.reason = "licensed-pending-site-present;waived-not-sound".into();
        return Ok(());
    }
    if expected.kind == BridgeKind::PairCopySnapshot {
        if expected.tier != "T1" || expected.waiver_id.is_some() {
            return Err("c9-tier-or-waiver-mismatch".into());
        }
    } else if expected.tier != "T2"
        || expected.waiver_id.as_deref() != Some(super::bridge_receipt::RAW_BOUNDARY_T2_WAIVER_ID)
    {
        return Err("raw-view-tier-or-waiver-mismatch".into());
    }
    let stamp = input
        .context
        .source_global_start
        .checked_add(original.span.lo)
        .ok_or("source-global-offset-overflow")?;
    let raw_name = |index: usize, a5: bool| {
        format!(
            "__crat_{}_raw_{stamp}_{index}",
            if a5 { "a5" } else { "pair" }
        )
    };
    if expected.kind != BridgeKind::PairCopySnapshot {
        if let Some((call, witnesses, reason)) =
            invalid_rendered_role(input, expected, original, &candidates, &indices, stamp)?
        {
            row.emitted_call = Some(call);
            row.bindings = witnesses;
            row.status = ReceiptStatus::InvalidRenderedRole;
            row.reason = format!(
                "receipt-linked-invalid-rendered-role:raw-temporary-to-safe-parameter;{reason}"
            );
            return Ok(());
        }
        let raw_calls = candidates
            .iter()
            .filter(|call| {
                indices.iter().all(|&index| {
                    call.arguments[index]
                        .binding
                        .as_ref()
                        .is_some_and(|binding| {
                            binding.name == raw_name(index, false)
                                || binding.name == raw_name(index, true)
                        })
                })
            })
            .copied()
            .collect::<Vec<_>>();
        if raw_calls.len() > 1 {
            return Err("multiple-calls-use-the-stamped-raw-view".into());
        }
        if let [call] = raw_calls.as_slice() {
            row.bindings = validate_raw(input, expected, original, call, &indices)?;
            row.emitted_call = Some(call.span);
            row.status = ReceiptStatus::MatchedRaw;
            row.reason = "exact-original-stamp-bound-raw-temporary-and-call".into();
            return Ok(());
        }
    }
    if let Some(c9) = expected.c9_stamp {
        let name = format!("__crat_c9_{}_{}", c9.basic_block, c9.statement_index);
        let mut c9_calls = Vec::new();
        for call in &candidates {
            let selected = if indices.is_empty() {
                call.arguments
                    .iter()
                    .enumerate()
                    .filter_map(|(index, argument)| {
                        argument
                            .binding
                            .as_ref()
                            .is_some_and(|binding| binding.name == name)
                            .then_some(index)
                    })
                    .collect::<Vec<_>>()
            } else {
                indices.clone()
            };
            if !selected.is_empty()
                && selected.iter().all(|&index| {
                    call.arguments[index]
                        .binding
                        .as_ref()
                        .is_some_and(|binding| binding.name == name)
                })
            {
                c9_calls.push((*call, selected));
            }
        }
        if c9_calls.len() > 1 {
            return Err("c9-stamp-call-correspondence-not-unique".into());
        }
        if let [(call, selected)] = c9_calls.as_slice() {
            if indices.is_empty() && selected.len() != 1 {
                return Err("c9-argument-position-not-unique".into());
            }
            row.bindings = validate_c9(input, expected, original, call, selected, &name)?;
            row.argument_indices = selected.clone();
            row.emitted_call = Some(call.span);
            row.status = ReceiptStatus::MatchedC9;
            row.reason = "exact-c9-stamp-private-read-and-call-borrow".into();
            return Ok(());
        }
    } else if candidates.iter().any(|call| {
        call.arguments.iter().enumerate().any(|(index, argument)| {
            (indices.is_empty() || indices.contains(&index))
                && argument
                    .binding
                    .as_ref()
                    .is_some_and(|binding| binding.generated == Some(GeneratedKind::C9Temporary))
        })
    }) {
        return Err("c9-alternative-present-without-exact-proof-stamp".into());
    }
    let owner = mapped_owner(&expected.caller, input.context)?;
    if input.emitted.bindings.iter().any(|binding| {
        binding.owner == owner
            && indices.iter().any(|&index| {
                binding.name == raw_name(index, false) || binding.name == raw_name(index, true)
            })
    }) {
        return Err("stamped-raw-temporary-has-no-exact-bound-call-use".into());
    }
    row.status = ReceiptStatus::Missing;
    row.reason = "no-stamped-raw-view-or-matched-c9-at-original-site".into();
    Ok(())
}

fn generated_name(name: &str) -> bool {
    name.starts_with("__crat_pair_raw_")
        || name.starts_with("__crat_a5_raw_")
        || name.starts_with("__crat_c9_")
}

fn original_binding(input: &BridgeCustodyInput<'_>, binding: &Binding) -> bool {
    let same = |candidate: &Binding| {
        candidate.name == binding.name
            && candidate.type_text == binding.type_text
            && candidate.init_text == binding.init_text
    };
    let originals = input
        .original
        .bindings
        .iter()
        .filter(|candidate| {
            same(candidate)
                && mapped_owner(&candidate.owner, input.context).ok()
                    == Some(binding.owner.as_str())
        })
        .count();
    originals == 1
        && input
            .emitted
            .bindings
            .iter()
            .filter(|candidate| candidate.owner == binding.owner && same(candidate))
            .count()
            == 1
}

fn reverse_census(input: &BridgeCustodyInput<'_>, rows: &[ReceiptResult]) -> Vec<TreeOnlyWitness> {
    let mut extras = Vec::new();
    for binding in input
        .emitted
        .bindings
        .iter()
        .filter(|binding| generated_name(&binding.name) && !original_binding(input, binding))
    {
        let owned = rows
            .iter()
            .flat_map(|row| row.bindings.iter().map(move |witness| (row, witness)))
            .filter(|(_, witness)| {
                witness.binding_id == binding.id && witness.owner == binding.owner
            })
            .collect::<Vec<_>>();
        let uses = input
            .emitted
            .uses
            .iter()
            .filter(|usage| usage.binding_id == binding.id && usage.owner == binding.owner)
            .collect::<Vec<_>>();
        if owned.is_empty() || uses.is_empty() {
            extras.push(TreeOnlyWitness {
                owner: binding.owner.clone(),
                binding_id: binding.id,
                name: binding.name.clone(),
                declaration_span: binding.declaration_span,
                call_span: None,
                argument_index: None,
                reason: "unclaimed-generated-declaration".into(),
            });
        }
        for usage in uses {
            let claimed = owned.iter().any(|(row, witness)| {
                row.emitted_call.is_some_and(|span| {
                    input
                        .emitted
                        .calls
                        .iter()
                        .find(|call| call.owner == binding.owner && call.span == span)
                        .and_then(|call| call.arguments.get(witness.argument_index))
                        .is_some_and(|argument| {
                            argument.span.lo <= usage.span.lo && usage.span.hi <= argument.span.hi
                        })
                })
            });
            if claimed {
                continue;
            }
            let calls = input
                .emitted
                .calls
                .iter()
                .filter(|call| call.owner == binding.owner)
                .flat_map(|call| {
                    call.arguments
                        .iter()
                        .enumerate()
                        .filter(move |(_, argument)| {
                            argument.span.lo <= usage.span.lo && usage.span.hi <= argument.span.hi
                        })
                        .map(move |(index, _)| (call.span, index))
                })
                .collect::<Vec<_>>();
            let location = match calls.as_slice() {
                [location] => Some(*location),
                _ => None,
            };
            extras.push(TreeOnlyWitness {
                owner: binding.owner.clone(),
                binding_id: binding.id,
                name: binding.name.clone(),
                declaration_span: binding.declaration_span,
                call_span: location.map(|(span, _)| span),
                argument_index: location.map(|(_, index)| index),
                reason: format!(
                    "unclaimed-generated-use:{}..{}",
                    usage.span.lo, usage.span.hi
                ),
            });
        }
    }
    extras
}

/// One complete file inventory, including files with no expected ledger rows.
/// Parser scope barriers matter at the exact binding lookup; ordinary unrelated
/// source assignments do not turn into a program-wide custody failure.
pub(crate) fn compare(input: BridgeCustodyInput<'_>) -> BridgeCustodyReport {
    rustc_span::create_session_globals_then(Edition::Edition2018, &[], None, || {
        let mut report = BridgeCustodyReport::default();
        let mut identities = BTreeSet::new();
        let mut duplicates = BTreeSet::new();
        for expected in input.expectations {
            if !identities.insert(expected.identity.as_str()) {
                duplicates.insert(expected.identity.as_str());
            }
        }
        for identity in &duplicates {
            report
                .issues
                .push(format!("duplicate-ledger-identity:{identity}"));
        }
        let normalized_offsets = !input.original_source.starts_with('\u{feff}')
            && !input.original_source.contains("\r\n");
        if !normalized_offsets {
            report
                .issues
                .push("producer-stamp-requires-explicit-LF-no-BOM-source".into());
        }
        for expected in input.expectations {
            let mut row = ReceiptResult {
                identity: expected.identity.clone(),
                status: ReceiptStatus::Unresolved,
                reason: String::new(),
                original_call: None,
                emitted_call: None,
                argument_indices: Vec::new(),
                bindings: Vec::new(),
            };
            let result = if duplicates.contains(expected.identity.as_str()) {
                Err("duplicate-ledger-identity".into())
            } else if !normalized_offsets {
                Err("original-source-offset-normalization-unresolved".into())
            } else {
                match_receipt(&input, expected, &mut row)
            };
            if let Err(reason) = result {
                row.status = ReceiptStatus::Unresolved;
                row.reason = reason;
                row.bindings.clear();
            }
            report.rows.push(row);
        }
        report.tree_only = reverse_census(&input, &report.rows);
        report.data = report.issues.is_empty()
            && report.tree_only.is_empty()
            && report.rows.iter().all(|row| {
                matches!(
                    row.status,
                    ReceiptStatus::MatchedRaw
                        | ReceiptStatus::MatchedC9
                        | ReceiptStatus::WaivedPending
                )
            });
        report
    })
}
