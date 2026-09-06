//! **S3.2′-0 measurement — where a pointer subject's value comes from.**
//!
//! Two questions ride on the construction site, and both were recorded as
//! unmeasurable when the slice addendum was written:
//!
//! - **`Box<T>` vs `Box<[T]>`** — the allocation-size expression is the
//!   discriminator. `malloc(4)` behind a `*mut i32` is one element;
//!   `calloc(k, 4)` is `k`. Under user ruling U-2 condition (b) this is
//!   load-bearing rather than latent: owning fat forms take a *recovered*
//!   length or degrade, because there the length **is** the allocation
//!   parameter — approximating it changes what is allocated, not merely what
//!   is claimed.
//! - **`approx-len` incidence** — the large-length approximation applies where
//!   fatness says array, BO says safe, and no length is recoverable. Forecasting
//!   that set *before* anything is emitted is what U-2 condition (a) requires
//!   and what queue entry **A7**'s sizing depends on.
//!
//! # Measurement only
//!
//! Nothing in `decide_one` reads this. It is collected beside the decision, not
//! inside it, so adding it cannot move a single corpus number — which is the
//! property that lets it ride an ordinary sweep instead of needing its own
//! pre-registration.
//!
//! # Why the recognizer is syntactic, and what that costs
//!
//! It reads HIR initializers, so it sees what the source literally says. A
//! pointer whose length is established somewhere other than its own
//! initializer — the dominant parameter case, where the length arrives as a
//! sibling argument — is reported as **having no local construction site**,
//! not as unrecoverable. Those are different claims and the table keeps them
//! apart: the first is a statement about this analysis's scope, the second
//! would be a statement about the program.

use rustc_hash::FxHashMap;
use rustc_hir::{
    HirId,
    def::{DefKind, Res},
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;

use super::{Decision, DecisionTable, Subject, SubjectKind};
use crate::bo_rewriter::mechanical_receipt::{
    FALLBACK_EXTENT_RECEIPT, MechanicalExtent, SLICE_EXTENT_WAIVER_ID, UnsafeContextPresentation,
    present_unsafe_text,
};

/// How a pointer binding got its value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Construction {
    /// `arr.as_mut_ptr()` / `as_ptr()` — the length is the array's, statically.
    ArrayDecay,
    /// An allocator call. `count` is `Some` only for the two-argument form
    /// (`calloc`), where the element count is a separate argument and is
    /// therefore recoverable without interpreting the size expression.
    Alloc {
        callee: String,
        size: String,
        count: Option<String>,
    },
    /// Assigned from another pointer binding — the length question defers to
    /// the source, and this analysis does not chase it.
    CopyOf,
    /// A null (or integer) literal, after the `as *mut T` cast is peeled.
    NullLit,
    /// `&x` / `&mut x` — a borrow of a single place.
    AddrOf,
    /// `&arr[i]` — an interior pointer; length is the array's minus the index.
    IndexAddr,
    /// `(*s).field` or `*p` — the length lives with the source place.
    PlaceRead,
    /// A call to something that is not a known allocator — the length, if any,
    /// belongs to the callee's contract and is not visible here.
    CallResult,
    /// A `let` with an initializer the recognizer does not classify.
    Other,
}

impl Construction {
    /// The length-recoverability class, as the forecast table reports it.
    pub(crate) fn len_class(&self) -> &'static str {
        match self {
            Construction::ArrayDecay => "array-len",
            // Two-argument form: the count is its own argument.
            Construction::Alloc { count: Some(_), .. } => "alloc-count",
            Construction::Alloc { size, .. } => {
                if size.chars().all(|c| c.is_ascii_digit()) {
                    "alloc-size-literal"
                } else if size.contains("size_of") {
                    "alloc-size-sizeof"
                } else {
                    "alloc-size-dynamic"
                }
            }
            Construction::CopyOf => "copy",
            Construction::NullLit => "null-lit",
            Construction::AddrOf => "addr-of-one",
            Construction::IndexAddr => "interior-index",
            Construction::PlaceRead => "place-read",
            Construction::CallResult => "call-result",
            Construction::Other => "other",
        }
    }

    pub(crate) fn key(&self) -> &'static str {
        match self {
            Construction::ArrayDecay => "array-decay",
            Construction::Alloc { .. } => "alloc",
            Construction::CopyOf => "copy",
            Construction::NullLit => "null-lit",
            Construction::AddrOf => "addr-of",
            Construction::IndexAddr => "index-addr",
            Construction::PlaceRead => "place-read",
            Construction::CallResult => "call-result",
            Construction::Other => "other",
        }
    }
}

#[derive(Default)]
pub(crate) struct ConstructionFacts {
    pub by_binding: FxHashMap<(LocalDefId, HirId), Construction>,
    /// Typed target of a non-allocator call-result construction.  This is a
    /// sidecar rather than payload in [`Construction::CallResult`] so the
    /// long-lived construction key and all unrelated receipts remain stable.
    pub call_result_targets: FxHashMap<(LocalDefId, HirId), CallResultTarget>,
    pub init_spans: FxHashMap<(LocalDefId, HirId), rustc_span::Span>,
    /// HIR identity of the initializer expression. Unlike its source text,
    /// this remains a typed carrier for allocation/result classification.
    pub init_hirs: FxHashMap<(LocalDefId, HirId), HirId>,
    pub init_sources: FxHashMap<(LocalDefId, HirId), HirId>,
    pub statement_spans: FxHashMap<(LocalDefId, HirId), rustc_span::Span>,
    pub first_stores: FxHashMap<(LocalDefId, HirId), Vec<FirstStore>>,
    pub deallocator_calls: FxHashMap<(LocalDefId, HirId), Vec<rustc_span::Span>>,
    pub zero_memsets: FxHashMap<(LocalDefId, HirId), Vec<ZeroMemset>>,
    pub owner_overwrites: FxHashMap<(LocalDefId, HirId), Vec<OwnerOverwrite>>,
    pub realloc_calls: FxHashMap<(LocalDefId, HirId), Vec<rustc_span::Span>>,
    /// Positive layout evidence that an allocator size combines a fixed header
    /// with a separately-sized trailing region. Box wave 2 holds this class;
    /// it is not an initializer failure.
    pub flexible_tail_allocations: FxHashMap<(LocalDefId, HirId), FlexibleTailEvidence>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum SliceLengthSource {
    AllocationElementCount {
        allocator: String,
        argument_index: u32,
    },
    AllocationByteCount {
        allocator: String,
        argument_index: u32,
        element_type: String,
    },
    AssociatedArgument {
        owner: LocalDefId,
        argument_index: u32,
    },
    SealedContract {
        contract: String,
    },
    Fallback,
}

impl SliceLengthSource {
    pub(crate) fn receipt_key(&self) -> String {
        match self {
            Self::AllocationElementCount {
                allocator,
                argument_index,
            } => format!("allocation-element-count:{allocator}:arg{argument_index}"),
            Self::AllocationByteCount {
                allocator,
                argument_index,
                element_type,
            } => format!(
                "allocation-byte-count:{allocator}:arg{argument_index}:element={element_type}"
            ),
            Self::AssociatedArgument {
                owner,
                argument_index,
            } => format!(
                "associated-argument:{}:arg{argument_index}",
                owner.local_def_index.as_u32()
            ),
            Self::SealedContract { contract } => format!("sealed-contract:{contract}"),
            Self::Fallback => FALLBACK_EXTENT_RECEIPT.to_owned(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SliceLengthPlan {
    pub(crate) expression: String,
    pub(crate) source: SliceLengthSource,
    pub(crate) provenance: Vec<SliceLengthProvenance>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum SliceLengthProvenance {
    Inherited {
        owner: LocalDefId,
        binding: HirId,
    },
    /// R206 E11: retained for the CP2 movement count, never length evidence.
    UnlicensedAdjacentArgument {
        owner: LocalDefId,
        argument_index: u32,
    },
}

impl SliceLengthProvenance {
    fn receipt_key(&self) -> String {
        match self {
            Self::Inherited { owner, binding } => format!(
                "inherited:{}:hir{}",
                owner.local_def_index.as_u32(),
                binding.local_id.as_u32()
            ),
            Self::UnlicensedAdjacentArgument {
                owner,
                argument_index,
            } => format!(
                "associated-argument-inert:no-exported-length-association:{}:arg{argument_index}",
                owner.local_def_index.as_u32()
            ),
        }
    }
}

impl SliceLengthPlan {
    pub(crate) fn extent(&self) -> MechanicalExtent {
        match &self.source {
            SliceLengthSource::Fallback => MechanicalExtent::Fallback {
                receipt: FALLBACK_EXTENT_RECEIPT.to_owned(),
                waiver_id: SLICE_EXTENT_WAIVER_ID.to_owned(),
            },
            source => MechanicalExtent::Evidence(source.receipt_key()),
        }
    }

    pub(crate) fn is_fallback(&self) -> bool {
        matches!(self.source, SliceLengthSource::Fallback)
    }

    pub(crate) fn provenance_receipt(&self) -> String {
        if self.provenance.is_empty() {
            "-".to_owned()
        } else {
            self.provenance
                .iter()
                .map(SliceLengthProvenance::receipt_key)
                .collect::<Vec<_>>()
                .join(";")
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SliceConstructionPlan {
    pub(crate) node: (LocalDefId, HirId),
    pub(crate) init_hir: HirId,
    pub(crate) init_span: Span,
    pub(crate) replacement: Option<String>,
    pub(crate) hold_reason: Option<String>,
    pub(crate) element_type: String,
    pub(crate) mutable: bool,
    pub(crate) nullable: bool,
    pub(crate) initializer_kind: &'static str,
    pub(crate) length: SliceLengthPlan,
    pub(crate) composed_edit_spans: Vec<Span>,
    pub(crate) unsafe_context: UnsafeContextPresentation,
}

pub(crate) fn slice_constructor_available(
    facts: &ConstructionFacts,
    node: (LocalDefId, HirId),
) -> bool {
    facts.init_spans.contains_key(&node) && facts.init_hirs.contains_key(&node)
}

fn normalized(value: &str) -> String {
    value.chars().filter(|ch| !ch.is_whitespace()).collect()
}

fn exact_element_size(size: &str, element_type: &str) -> bool {
    let size = normalized(size);
    let mut size = size.as_str();
    while let Some(inner) = size.strip_prefix('(').and_then(|s| s.strip_suffix(')')) {
        size = inner;
    }
    let element = normalized(element_type);
    ["core::mem::", "std::mem::", ""]
        .into_iter()
        .any(|prefix| size == format!("{prefix}size_of::<{element}>()"))
}

fn allocation_length(construction: &Construction, element_type: &str) -> Option<SliceLengthPlan> {
    let Construction::Alloc {
        callee,
        size,
        count,
    } = construction
    else {
        return None;
    };
    if let Some(count) = count
        && exact_element_size(size, element_type)
    {
        return Some(SliceLengthPlan {
            expression: format!("({count}) as usize"),
            source: SliceLengthSource::AllocationElementCount {
                allocator: callee.clone(),
                argument_index: 0,
            },
            provenance: Vec::new(),
        });
    }
    None
}

/// R206 E05/E10: HIR gives the whole expression's operator, so a size factor
/// buried in a sum, cast, or division cannot become exact-product evidence.
fn allocation_product_length(
    tcx: TyCtxt<'_>,
    init_hir: HirId,
    construction: &Construction,
    element_type: &str,
) -> Option<SliceLengthPlan> {
    let Construction::Alloc {
        callee,
        size,
        count: None,
    } = construction
    else {
        return None;
    };
    let expression = Collector::peel(tcx.hir_node(init_hir).expect_expr());
    let rustc_hir::ExprKind::Call(_, args) = expression.kind else { return None };
    let argument_index = usize::from(callee == "realloc");
    let bytes = args.get(argument_index)?;
    let rustc_hir::ExprKind::Binary(operator, left, right) = bytes.kind else { return None };
    if operator.node != rustc_hir::BinOpKind::Mul {
        return None;
    }
    let sm = tcx.sess.source_map();
    let exact_factor = [left, right].into_iter().any(|factor| {
        sm.span_to_snippet(factor.span)
            .ok()
            .is_some_and(|text| exact_element_size(&text, element_type))
    });
    exact_factor.then(|| SliceLengthPlan {
        expression: format!("(({size}) / core::mem::size_of::<{element_type}>()) as usize"),
        source: SliceLengthSource::AllocationByteCount {
            allocator: callee.clone(),
            argument_index: argument_index as u32,
            element_type: element_type.to_owned(),
        },
        provenance: Vec::new(),
    })
}

fn integer_argument(tcx: TyCtxt<'_>, owner: LocalDefId, index: usize) -> bool {
    tcx.fn_sig(owner)
        .skip_binder()
        .skip_binder()
        .inputs()
        .get(index)
        .is_some_and(|ty| {
            matches!(
                ty.kind(),
                rustc_middle::ty::TyKind::Int(_) | rustc_middle::ty::TyKind::Uint(_)
            )
        })
}

/// The frozen model and library contracts export no length-association fact.
/// The former adjacency rule is observed only for the R206 CP2 receipt count.
fn unlicensed_argument_adjacency(
    tcx: TyCtxt<'_>,
    table: &DecisionTable,
    facts: &ConstructionFacts,
    node: (LocalDefId, HirId),
) -> Option<SliceLengthProvenance> {
    let source = *facts.init_sources.get(&node)?;
    let (_, source_decision) = table
        .entries
        .iter()
        .find(|(subject, _)| subject.fn_did == node.0 && subject.hir_id == source)?;
    match source_decision {
        Decision::Degraded(_) => return None,
        Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::Opt { .. }
        | Decision::Box(_) => {}
    }
    let source_subject = table
        .entries
        .iter()
        .find(|(subject, _)| subject.fn_did == node.0 && subject.hir_id == source)?
        .0
        .clone();
    let SubjectKind::Param { hir_index } = source_subject.kind else {
        return None;
    };
    let companion = if integer_argument(tcx, node.0, hir_index + 1) {
        hir_index + 1
    } else if hir_index > 0 && integer_argument(tcx, node.0, hir_index - 1) {
        hir_index - 1
    } else {
        return None;
    };
    Some(SliceLengthProvenance::UnlicensedAdjacentArgument {
        owner: node.0,
        argument_index: u32::try_from(companion).ok()?,
    })
}

fn associated_local_length(
    facts: &ConstructionFacts,
    node: (LocalDefId, HirId),
    known: &FxHashMap<(LocalDefId, HirId), SliceLengthPlan>,
) -> Option<SliceLengthPlan> {
    let source = *facts.init_sources.get(&node)?;
    let inherited = known.get(&(node.0, source))?;
    let mut inherited = inherited.clone();
    inherited.provenance.push(SliceLengthProvenance::Inherited {
        owner: node.0,
        binding: source,
    });
    Some(inherited)
}

fn array_decay_length(
    tcx: TyCtxt<'_>,
    owner: LocalDefId,
    init_hir: HirId,
) -> Option<SliceLengthPlan> {
    let mut expression = tcx.hir_node(init_hir).expect_expr();
    while let rustc_hir::ExprKind::Cast(inner, _) = expression.kind {
        expression = inner;
    }
    let rustc_hir::ExprKind::MethodCall(segment, receiver, _, _) = expression.kind else {
        return None;
    };
    if !matches!(segment.ident.name.as_str(), "as_ptr" | "as_mut_ptr") {
        return None;
    }
    let typeck = tcx.typeck(owner);
    let mut ty = typeck.expr_ty(receiver);
    while let rustc_middle::ty::TyKind::Ref(_, inner, _) = ty.kind() {
        ty = *inner;
    }
    let rustc_middle::ty::TyKind::Array(_, length) = ty.kind() else {
        return None;
    };
    let length = length.try_to_target_usize(tcx)?;
    Some(SliceLengthPlan {
        expression: format!("{length}usize"),
        source: SliceLengthSource::SealedContract {
            contract: format!("array-length:hir{}", receiver.hir_id.local_id.as_u32()),
        },
        provenance: Vec::new(),
    })
}

fn select_length(
    tcx: TyCtxt<'_>,
    table: &DecisionTable,
    facts: &ConstructionFacts,
    subject: &Subject,
    element_type: &str,
    init_hir: HirId,
    known: &FxHashMap<(LocalDefId, HirId), SliceLengthPlan>,
) -> SliceLengthPlan {
    let node = (subject.fn_did, subject.hir_id);
    if let Some(construction) = facts.by_binding.get(&node)
        && let Some(length) = allocation_length(construction, element_type)
            .or_else(|| allocation_product_length(tcx, init_hir, construction, element_type))
    {
        return length;
    }
    if matches!(facts.by_binding.get(&node), Some(Construction::ArrayDecay))
        && let Some(length) = array_decay_length(tcx, subject.fn_did, init_hir)
    {
        return length;
    }
    if let Some(length) = associated_local_length(facts, node, known) {
        return length;
    }
    SliceLengthPlan {
        expression: "crate::FALLBACK_SLICE_EXTENT".to_owned(),
        source: SliceLengthSource::Fallback,
        provenance: unlicensed_argument_adjacency(tcx, table, facts, node)
            .into_iter()
            .collect(),
    }
}

pub(crate) fn render_slice_constructor(
    initializer: &str,
    element_type: &str,
    mutable: bool,
    nullable: bool,
    length_expression: &str,
    enclosing_unsafe_fn: bool,
    local_index: u32,
) -> String {
    let constructor = if mutable {
        "from_raw_parts_mut"
    } else {
        "from_raw_parts"
    };
    let body = if nullable {
        let raw_type = if mutable { "*mut" } else { "*const" };
        let option_method = if mutable { "as_mut" } else { "as_ref" };
        let temp = format!("__crat_slice_ptr_{local_index}");
        format!(
            "{{ let {temp}: {raw_type} {element_type} = {initializer}; {temp}.{option_method}().map(|p| core::slice::{constructor}(p, {length_expression})) }}"
        )
    } else {
        format!("core::slice::{constructor}({initializer}, {length_expression})")
    };
    present_unsafe_text(body, enclosing_unsafe_fn)
}

/// R206 E09: bind the selected allocation argument once, and bind every
/// preceding argument first (notably realloc's pointer). All bindings remain
/// inside the original initializer, preserving left-to-right evaluation.
fn bind_allocation_arguments(
    tcx: TyCtxt<'_>,
    subject: &Subject,
    init_hir: HirId,
    init_span: Span,
    initializer: &str,
    edits: &[(Span, String)],
    length: &SliceLengthPlan,
) -> Result<(Vec<String>, String, String), String> {
    let expression = Collector::peel(tcx.hir_node(init_hir).expect_expr());
    let rustc_hir::ExprKind::Call(callee, args) = expression.kind else {
        return Ok((
            Vec::new(),
            compose_initializer(init_span, initializer, edits)?,
            length.expression.clone(),
        ));
    };
    let (index, divisor) = match &length.source {
        SliceLengthSource::AllocationElementCount { argument_index, .. } => {
            (*argument_index as usize, None)
        }
        SliceLengthSource::AllocationByteCount {
            argument_index,
            element_type,
            ..
        } => (*argument_index as usize, Some(element_type)),
        SliceLengthSource::AssociatedArgument { .. }
        | SliceLengthSource::SealedContract { .. }
        | SliceLengthSource::Fallback => {
            return Ok((
                Vec::new(),
                compose_initializer(init_span, initializer, edits)?,
                length.expression.clone(),
            ));
        }
    };
    if args.get(index).is_none() {
        return Err("allocation length argument missing".to_owned());
    }
    let mut bindings = Vec::new();
    let mut replacements = edits.to_vec();
    let sm = tcx.sess.source_map();
    let typeck = tcx.typeck(subject.fn_did);
    if !matches!(
        typeck.expr_ty_adjusted(callee).kind(),
        rustc_middle::ty::TyKind::FnDef(..) | rustc_middle::ty::TyKind::FnPtr(..)
    ) {
        return Err(
            "composition-crossing-unhoistable:allocation-callee-not-copy-function".to_owned(),
        );
    }
    let captured = std::iter::once(callee).chain(args.iter().take(index + 1));
    for expression in captured {
        let span = expression.span.source_callsite();
        if edits.iter().any(|(edit, _)| {
            edit.lo() < span.hi() && span.lo() < edit.hi() && !span.contains(*edit)
        }) {
            // An opaque enclosing replacement may change control or retain
            // the original call. Its children cannot be hoisted through it.
            return Err(
                "composition-crossing-unhoistable:allocation-callee-or-argument-covered".to_owned(),
            );
        }
    }
    let callee_span = callee.span.source_callsite();
    let callee_edits = edits
        .iter()
        .filter(|(edit, _)| callee_span.contains(*edit))
        .cloned()
        .collect::<Vec<_>>();
    let callee_text = sm
        .span_to_snippet(callee_span)
        .map_err(|_| "allocation callee text unavailable".to_owned())?;
    let callee_text = compose_initializer(callee_span, &callee_text, &callee_edits)?;
    let callee_temp = format!("__crat_slice_callee_{}", subject.local.as_u32());
    bindings.push(format!("let {callee_temp} = {callee_text};"));
    replacements.retain(|(edit, _)| !callee_span.contains(*edit));
    replacements.push((callee_span, callee_temp));
    for (position, argument) in args.iter().enumerate().take(index + 1) {
        let span = argument.span.source_callsite();
        let contained = edits
            .iter()
            .filter(|(edit, _)| span.contains(*edit))
            .cloned()
            .collect::<Vec<_>>();
        let text = sm
            .span_to_snippet(span)
            .map_err(|_| "allocation argument text unavailable".to_owned())?;
        let text = compose_initializer(span, &text, &contained)?;
        let temp = format!("__crat_slice_arg_{}_{}", subject.local.as_u32(), position);
        let ty = typeck.expr_ty_adjusted(argument);
        bindings.push(format!("let {temp}: {ty} = {text};"));
        replacements.retain(|(edit, _)| !span.contains(*edit));
        replacements.push((span, temp));
    }
    let temp = format!("__crat_slice_arg_{}_{}", subject.local.as_u32(), index);
    let length_expression = if let Some(element_type) = divisor {
        format!("({temp} / core::mem::size_of::<{element_type}>()) as usize")
    } else {
        format!("({temp}) as usize")
    };
    Ok((
        bindings,
        compose_initializer(init_span, initializer, &replacements)?,
        length_expression,
    ))
}

pub(crate) fn collect_composable_edits(
    table: &DecisionTable,
    init_span: Span,
) -> Vec<(Span, String)> {
    let init = init_span.source_callsite();
    let contains = |span: Span| {
        let span = span.source_callsite();
        init.lo() <= span.lo() && span.hi() <= init.hi()
    };
    let mut edits = Vec::new();
    for (_, decision) in &table.entries {
        let uses = match decision {
            Decision::Slice { uses, .. } | Decision::Opt { uses, .. } => Some(uses),
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Box(_)
            | Decision::Degraded(_) => None,
        };
        edits.extend(
            uses.into_iter()
                .flatten()
                .filter(|edit| contains(edit.span))
                .map(|edit| (edit.span.source_callsite(), edit.replacement.clone())),
        );
    }
    edits.extend(
        table
            .seams
            .edits
            .iter()
            .filter(|edit| contains(edit.span))
            .map(|edit| (edit.span.source_callsite(), edit.replacement.clone())),
    );
    edits.extend(
        table
            .seams
            .body_edits
            .iter()
            .filter(|edit| contains(edit.span))
            .map(|edit| (edit.span.source_callsite(), edit.replacement.clone())),
    );
    edits.sort_by_key(|(span, replacement)| (span.lo(), span.hi(), replacement.clone()));
    edits.dedup();
    edits
}

pub(crate) fn compose_initializer(
    init_span: Span,
    initializer: &str,
    edits: &[(Span, String)],
) -> Result<String, String> {
    if edits.is_empty() {
        return Ok(initializer.to_owned());
    }
    let init = init_span.source_callsite();
    let exact = edits
        .iter()
        .filter(|(span, _)| span.lo() == init.lo() && span.hi() == init.hi())
        .collect::<Vec<_>>();
    if !exact.is_empty() {
        let first = &exact[0].1;
        if exact.iter().any(|(_, replacement)| replacement != first) {
            return Err("conflicting exact initializer adapters".to_owned());
        }
        return Ok(first.clone());
    }
    let mut ranges = edits
        .iter()
        .map(|(span, replacement)| {
            (
                usize::try_from(span.lo().0 - init.lo().0).unwrap_or(usize::MAX),
                usize::try_from(span.hi().0 - init.lo().0).unwrap_or(usize::MAX),
                replacement,
            )
        })
        .collect::<Vec<_>>();
    ranges.sort_by_key(|(lo, hi, _)| (*lo, *hi));
    if ranges.windows(2).any(|pair| pair[0].1 > pair[1].0) {
        return Err("crossing initializer adapters".to_owned());
    }
    let mut composed = initializer.to_owned();
    for (lo, hi, replacement) in ranges.into_iter().rev() {
        let Some(_) = composed.get(lo..hi) else {
            return Err("initializer adapter range outside expression".to_owned());
        };
        composed.replace_range(lo..hi, replacement);
    }
    Ok(composed)
}

pub(crate) fn plan_slice_constructions(
    tcx: TyCtxt<'_>,
    table: &DecisionTable,
    facts: &ConstructionFacts,
) -> Vec<SliceConstructionPlan> {
    let sm = tcx.sess.source_map();
    let mut plans = Vec::new();
    let mut known_lengths = FxHashMap::default();
    for (subject, decision) in &table.entries {
        match subject.kind {
            SubjectKind::Local => {}
            SubjectKind::Param { .. } => continue,
        }
        let (mutable, nullable) = match decision {
            Decision::Slice { mutable, .. } => (*mutable, false),
            Decision::Opt {
                mutable,
                slice: true,
                ..
            } => (*mutable, true),
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Opt { slice: false, .. }
            | Decision::Box(_)
            | Decision::Degraded(_) => continue,
        };
        let node = (subject.fn_did, subject.hir_id);
        if table.option_value_initializers.contains(&node) {
            continue;
        }
        if table
            .slice_use_receipts
            .iter()
            .any(|receipt| receipt.same_form_initializer == Some(node))
        {
            // R210: item 3 already owns this value as a safe copy/reborrow;
            // wrapping it in a raw-result constructor would cross forms twice.
            continue;
        }
        let Some(&init_span) = facts.init_spans.get(&node) else {
            continue;
        };
        let Some(&init_hir) = facts.init_hirs.get(&node) else {
            continue;
        };
        let initializer = sm
            .span_to_snippet(init_span)
            .unwrap_or_else(|_| "<unrenderable>".to_owned());
        let element_type = subject
            .pointee_span
            .and_then(|span| sm.span_to_snippet(span).ok())
            .unwrap_or_else(|| "_".to_owned());
        let mut length = select_length(
            tcx,
            table,
            facts,
            subject,
            &element_type,
            init_hir,
            &known_lengths,
        );
        let composed_edits = collect_composable_edits(table, init_span);
        let enclosing_unsafe_fn = tcx
            .fn_sig(subject.fn_did)
            .skip_binder()
            .skip_binder()
            .safety
            .is_unsafe();
        let unsafe_context = UnsafeContextPresentation {
            unsafe_fn: enclosing_unsafe_fn,
            wrapper_inserted: !enclosing_unsafe_fn,
            edition: 2018,
        };
        let rendered = bind_allocation_arguments(
            tcx,
            subject,
            init_hir,
            init_span,
            &initializer,
            &composed_edits,
            &length,
        )
        .map(|(bindings, initializer, length_expression)| {
            length.expression = length_expression;
            let constructor = render_slice_constructor(
                &initializer,
                &element_type,
                mutable,
                nullable,
                &length.expression,
                true,
                subject.local.as_u32(),
            );
            let body = if bindings.is_empty() {
                constructor
            } else {
                format!("{{ {} {constructor} }}", bindings.join(" "))
            };
            present_unsafe_text(body, enclosing_unsafe_fn)
        });
        let mut inherited_length = length.clone();
        if !length.is_fallback()
            && let Some(name) = &subject.param_name
        {
            // Allocation temporaries are block-local. A dependent declaration
            // reads the constructed source's length rather than repeating its
            // original allocator count or referring to an out-of-scope temp.
            inherited_length.expression = if nullable {
                format!("{name}.as_deref().map_or(0usize, |slice| slice.len())")
            } else {
                format!("{name}.len()")
            };
        }
        known_lengths.insert(node, inherited_length);
        plans.push(SliceConstructionPlan {
            node,
            init_hir,
            init_span,
            replacement: rendered.as_ref().ok().cloned(),
            hold_reason: rendered.err(),
            element_type,
            mutable,
            nullable,
            initializer_kind: facts
                .by_binding
                .get(&node)
                .map_or("unknown", Construction::key),
            length,
            composed_edit_spans: composed_edits.into_iter().map(|(span, _)| span).collect(),
            unsafe_context,
        });
    }
    plans.sort_by_key(|plan| {
        (
            plan.node.0.local_def_index.as_u32(),
            plan.init_span.lo().0,
            plan.init_span.hi().0,
        )
    });
    plans
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct FlexibleTailEvidence {
    pub expression: String,
    pub span: rustc_span::Span,
}

/// The only call-result target class allowed to license an inferred E2 local
/// is [`DirectLocal`](Self::DirectLocal).  Every other class stays explicit so
/// absence of a local callee can never be mistaken for evidence.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CallResultTarget {
    DirectLocal(LocalDefId),
    Indirect,
    Foreign,
    Unresolved,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct FirstStore {
    pub statement_span: rustc_span::Span,
    pub value_span: rustc_span::Span,
    pub value: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ZeroMemset {
    pub statement_span: rustc_span::Span,
    pub call_span: rustc_span::Span,
    pub bytes: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct OwnerOverwrite {
    pub statement_span: rustc_span::Span,
    pub value_span: rustc_span::Span,
    pub construction: Construction,
}

const ALLOCATORS: &[&str] = &[
    "malloc", "calloc", "realloc", "xmalloc", "xcalloc", "strdup",
];

pub(crate) fn collect(tcx: TyCtxt<'_>, fns: &[LocalDefId]) -> ConstructionFacts {
    let mut facts = ConstructionFacts::default();
    for &fn_did in fns {
        let Some(body_id) = tcx.hir_node_by_def_id(fn_did).body_id() else {
            continue;
        };
        let mut v = Collector {
            tcx,
            fn_did,
            facts: &mut facts,
            local_values: FxHashMap::default(),
        };
        v.visit_body(tcx.hir_body(body_id));
    }
    facts
}

struct Collector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    fn_did: LocalDefId,
    facts: &'a mut ConstructionFacts,
    local_values: FxHashMap<HirId, (String, rustc_span::Span)>,
}

impl Collector<'_, '_> {
    fn snippet(&self, span: rustc_span::Span) -> String {
        self.tcx
            .sess
            .source_map()
            .span_to_snippet(span)
            .unwrap_or_else(|_| "<unrenderable>".to_owned())
            // TSV is the wire here; a tab or newline inside a snippet would
            // silently shift every later column.
            .replace(['\t', '\n', '\r'], " ")
    }

    /// Strip the `as *mut T` C2Rust puts on every allocator result.
    fn peel<'h>(mut e: &'h rustc_hir::Expr<'h>) -> &'h rustc_hir::Expr<'h> {
        while let rustc_hir::ExprKind::Cast(inner, _) = &e.kind {
            e = inner;
        }
        e
    }

    fn classify(&self, init: &rustc_hir::Expr<'_>) -> Construction {
        let e = Self::peel(init);
        match &e.kind {
            rustc_hir::ExprKind::Call(callee, args) => {
                let name = match &callee.kind {
                    rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, p)) => p
                        .segments
                        .last()
                        .map(|s| s.ident.name.to_string())
                        .unwrap_or_default(),
                    _ => String::new(),
                };
                if ALLOCATORS.contains(&name.as_str()) {
                    // Keyed on the CALLEE, never on arity. `calloc(count, size)`
                    // and `realloc(ptr, size)` both take two arguments, and an
                    // arity test reads `realloc`'s POINTER as an element count —
                    // measured on the first de-risk run, where every `realloc`
                    // in libtree came back `alloc-count` with `(*v).p` as its
                    // "count".
                    let (count, size) = match (name.as_str(), args.len()) {
                        ("calloc" | "xcalloc", 2) => {
                            (Some(self.snippet(args[0].span)), self.snippet(args[1].span))
                        }
                        ("realloc", 2) => (None, self.snippet(args[1].span)),
                        _ => (
                            None,
                            args.first()
                                .map(|a| self.snippet(a.span))
                                .unwrap_or_default(),
                        ),
                    };
                    Construction::Alloc {
                        callee: name,
                        size,
                        count,
                    }
                } else {
                    Construction::CallResult
                }
            }
            rustc_hir::ExprKind::MethodCall(seg, ..) => {
                let m = seg.ident.name.to_string();
                if m == "as_mut_ptr" || m == "as_ptr" {
                    Construction::ArrayDecay
                } else {
                    Construction::Other
                }
            }
            rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, p)) => {
                if matches!(p.res, rustc_hir::def::Res::Local(_)) {
                    Construction::CopyOf
                } else {
                    Construction::Other
                }
            }
            // The shapes below were an undifferentiated `Other` on the first
            // de-risk — 106 of 205 bindings, which forecasts nothing. Split
            // because each has a *different* length story, and the whole point
            // of this table is to predict where the approximation fires.
            //
            // A null literal reaches here because `peel` strips the
            // `0 as *mut T` cast C2Rust emits.
            rustc_hir::ExprKind::Lit(_) => Construction::NullLit,
            // `&mut x` / `&x` — length 1 unless the operand is an index or a
            // whole array, which `Index` below catches separately.
            rustc_hir::ExprKind::AddrOf(..) => Construction::AddrOf,
            // `&arr[i] as *mut T` — the C idiom for interior pointers. The
            // length is the array's *minus the offset*, so it is recoverable
            // only with the index, and this records that it is an index case
            // rather than pretending it is a plain decay.
            rustc_hir::ExprKind::Index(..) => Construction::IndexAddr,
            // `(*s).field` and `*p` — the length lives with the source place,
            // which this analysis does not chase.
            rustc_hir::ExprKind::Field(..)
            | rustc_hir::ExprKind::Unary(rustc_hir::UnOp::Deref, _) => Construction::PlaceRead,
            _ => Construction::Other,
        }
    }

    fn call_result_target(&self, init: &rustc_hir::Expr<'_>) -> Option<CallResultTarget> {
        let e = Self::peel(init);
        let rustc_hir::ExprKind::Call(callee, _) = &e.kind else {
            return None;
        };
        match &callee.kind {
            rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) => match path.res {
                Res::Def(DefKind::Fn | DefKind::AssocFn, did) => {
                    Some(if self.tcx.is_mir_available(did) {
                        did.as_local()
                            .map(CallResultTarget::DirectLocal)
                            .unwrap_or(CallResultTarget::Foreign)
                    } else {
                        // An `extern` declaration can surface as `DefKind::Fn`
                        // in this HIR position. Local DefId is therefore not
                        // body evidence; MIR availability is the fail-closed
                        // discriminator for a rewrite-owned callee.
                        CallResultTarget::Foreign
                    })
                }
                Res::Local(_) => Some(CallResultTarget::Indirect),
                Res::Err => Some(CallResultTarget::Unresolved),
                Res::Def(..) => Some(CallResultTarget::Foreign),
                _ => Some(CallResultTarget::Unresolved),
            },
            // A call through a local, field, cast, closure, or other computed
            // expression is indirect even if type checking later identifies a
            // finite target set. E2-FN deliberately does not rewrite webs.
            _ => Some(CallResultTarget::Indirect),
        }
    }

    fn flexible_tail_evidence(&self, init: &rustc_hir::Expr<'_>) -> Option<FlexibleTailEvidence> {
        let e = Self::peel(init);
        let rustc_hir::ExprKind::Call(callee, args) = &e.kind else {
            return None;
        };
        let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = &callee.kind else {
            return None;
        };
        let name = path.segments.last()?.ident.name.as_str();
        if !matches!(name, "malloc" | "calloc" | "xmalloc" | "xcalloc") {
            return None;
        }
        let size = match (name, *args) {
            ("calloc" | "xcalloc", [_, size]) | (_, [size]) => *size,
            _ => return None,
        };
        let (expression, span) = match &Self::peel(&size).kind {
            rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) => {
                let Res::Local(binding) = path.res else {
                    return None;
                };
                self.local_values.get(&binding)?.clone()
            }
            _ => (self.snippet(size.span), size.span),
        };
        let size_of_count = expression.matches("size_of::<").count();
        let combines_regions = expression.contains('+') || expression.contains("wrapping_add");
        let has_trailing_extent = expression.contains('*') || expression.contains("wrapping_mul");
        (size_of_count >= 2 && combines_regions && has_trailing_extent)
            .then_some(FlexibleTailEvidence { expression, span })
    }
}

impl<'tcx> Visitor<'tcx> for Collector<'_, 'tcx> {
    fn visit_stmt(&mut self, stmt: &'tcx rustc_hir::Stmt<'tcx>) {
        if let rustc_hir::StmtKind::Let(local) = stmt.kind
            && matches!(local.pat.kind, rustc_hir::PatKind::Binding(..))
            && let Some(init) = local.init
        {
            let c = self.classify(init);
            if let Some(evidence) = self.flexible_tail_evidence(init) {
                self.facts
                    .flexible_tail_allocations
                    .insert((self.fn_did, local.pat.hir_id), evidence);
            }
            if matches!(c, Construction::CallResult)
                && let Some(target) = self.call_result_target(init)
            {
                self.facts
                    .call_result_targets
                    .insert((self.fn_did, local.pat.hir_id), target);
            }
            self.facts
                .by_binding
                .insert((self.fn_did, local.pat.hir_id), c);
            self.facts
                .init_spans
                .insert((self.fn_did, local.pat.hir_id), init.span);
            self.facts
                .init_hirs
                .insert((self.fn_did, local.pat.hir_id), init.hir_id);
            if let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) =
                Self::peel(init).kind
                && let rustc_hir::def::Res::Local(source) = path.res
            {
                self.facts
                    .init_sources
                    .insert((self.fn_did, local.pat.hir_id), source);
            }
            self.facts
                .statement_spans
                .insert((self.fn_did, local.pat.hir_id), stmt.span);
            self.local_values
                .insert(local.pat.hir_id, (self.snippet(init.span), init.span));
        }
        let expression = match stmt.kind {
            rustc_hir::StmtKind::Semi(expression) | rustc_hir::StmtKind::Expr(expression) => {
                Some(expression)
            }
            _ => None,
        };
        if let Some(expression) = expression
            && let rustc_hir::ExprKind::Assign(lhs, rhs, _) = expression.kind
            && let rustc_hir::ExprKind::Unary(rustc_hir::UnOp::Deref, base) = lhs.kind
            && let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = base.kind
            && let rustc_hir::def::Res::Local(binding) = path.res
            && matches!(Self::peel(rhs).kind, rustc_hir::ExprKind::Lit(_))
        {
            let value = self.snippet(rhs.span);
            self.facts
                .first_stores
                .entry((self.fn_did, binding))
                .or_default()
                .push(FirstStore {
                    statement_span: stmt.span,
                    value_span: rhs.span,
                    value,
                });
        }
        if let Some(expression) = expression
            && let rustc_hir::ExprKind::Assign(lhs, rhs, _) = expression.kind
            && let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, lhs_path)) = lhs.kind
            && let rustc_hir::def::Res::Local(binding) = lhs_path.res
        {
            let construction = self.classify(rhs);
            if matches!(construction, Construction::Alloc { .. }) {
                self.facts
                    .owner_overwrites
                    .entry((self.fn_did, binding))
                    .or_default()
                    .push(OwnerOverwrite {
                        statement_span: stmt.span,
                        value_span: rhs.span,
                        construction,
                    });
            }
        }
        let memset_expression = expression.map(|expression| match expression.kind {
            rustc_hir::ExprKind::Assign(_, rhs, _) => Self::peel(rhs),
            _ => expression,
        });
        if let Some(memset_expression) = memset_expression
            && let rustc_hir::ExprKind::Call(callee, args) = memset_expression.kind
            && let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = callee.kind
            && path
                .segments
                .last()
                .is_some_and(|segment| segment.ident.name.as_str() == "memset")
            && let [pointer, value, bytes] = args
            && self.snippet(Self::peel(value).span).trim() == "0"
            && let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, argument_path)) =
                Self::peel(pointer).kind
            && let rustc_hir::def::Res::Local(binding) = argument_path.res
        {
            let bytes = self.snippet(bytes.span);
            self.facts
                .zero_memsets
                .entry((self.fn_did, binding))
                .or_default()
                .push(ZeroMemset {
                    statement_span: stmt.span,
                    call_span: memset_expression.span,
                    bytes,
                });
        }
        intravisit::walk_stmt(self, stmt);
    }

    fn visit_expr(&mut self, expression: &'tcx rustc_hir::Expr<'tcx>) {
        if let rustc_hir::ExprKind::Call(callee, args) = expression.kind
            && let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = callee.kind
            && path
                .segments
                .last()
                .is_some_and(|segment| matches!(segment.ident.name.as_str(), "free" | "realloc"))
            && let Some(argument) = args.first()
            && let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(_, argument_path)) =
                Self::peel(argument).kind
            && let rustc_hir::def::Res::Local(binding) = argument_path.res
        {
            let callee_name = path
                .segments
                .last()
                .expect("matched callee segment")
                .ident
                .name;
            self.facts
                .deallocator_calls
                .entry((self.fn_did, binding))
                .or_default()
                .push(expression.span);
            if callee_name.as_str() == "realloc" {
                self.facts
                    .realloc_calls
                    .entry((self.fn_did, binding))
                    .or_default()
                    .push(expression.span);
            }
        }
        intravisit::walk_expr(self, expression);
    }
}

#[cfg(test)]
mod slice_construction_tests {
    use super::*;

    /// Test only: isolate construction planning from earlier placement walls.
    /// The real HIR identities and initializers are retained; only p/q's
    /// decision is injected, as permitted for downstream phase witnesses.
    fn slc_construction_plans(input: &str) -> Vec<SliceConstructionPlan> {
        slc_construction_plans_with_enclosing_adapter(input, false)
    }

    fn slc_construction_plans_with_enclosing_adapter(
        input: &str,
        enclosing_adapter: bool,
    ) -> Vec<SliceConstructionPlan> {
        ::utils::compilation::run_compiler_on_input(
            ::utils::compilation::str_to_input(input),
            |tcx| {
                let mut table = crate::bo_rewriter::decide_table(tcx).expect("fixture decisions");
                let owners = tcx.hir_body_owners().collect::<Vec<_>>();
                let facts = collect(tcx, &owners);
                for (subject, decision) in &mut table.entries {
                    if matches!(subject.kind, SubjectKind::Local)
                        && matches!(subject.param_name.as_deref(), Some("p" | "q"))
                    {
                        *decision = Decision::Slice {
                            mutable: false,
                            uses: if enclosing_adapter {
                                let span = facts.init_spans[&(subject.fn_did, subject.hir_id)];
                                vec![super::super::emitability::UseEdit {
                                    span,
                                    replacement: tcx
                                        .sess
                                        .source_map()
                                        .span_to_snippet(span)
                                        .expect("initializer"),
                                    bridge_kind: "subject-use",
                                }]
                            } else {
                                Vec::new()
                            },
                        };
                    }
                }
                // R210 same-form copies are tested through the production
                // pipeline. This helper injects raw-constructor decisions to
                // isolate R206's extent/provenance assertions, so it also
                // clears the earlier production same-form initializer claims.
                for receipt in &mut table.slice_use_receipts {
                    receipt.same_form_initializer = None;
                }
                plan_slice_constructions(tcx, &table, &facts)
            },
        )
        .expect("construction fixture compiles")
    }

    #[test]
    fn slc_r206_callee_is_evaluated_before_the_count() {
        let plans = slc_construction_plans(
            "#![allow(dead_code, unused_unsafe, unused_assignments)]\n\
             extern \"C\" {\n\
                 fn first(n: usize, size: usize) -> *mut i32;\n\
                 fn second(n: usize, size: usize) -> *mut i32;\n\
             }\n\
             pub unsafe fn target() -> i32 {\n\
                 let mut calloc: unsafe extern \"C\" fn(usize, usize) -> *mut i32 = first;\n\
                 let p: *mut i32 = calloc({ calloc = second; 2 }, core::mem::size_of::<i32>());\n\
                 *p.offset(1)\n\
             }\n",
        );
        assert_eq!(plans.len(), 1);
        let expression = plans[0].replacement.as_ref().expect("constructor");
        let callee_read = expression
            .find("= calloc;")
            .expect("callee captured before arguments");
        let argument_effect = expression
            .find("calloc = second")
            .expect("count side effect");
        assert!(callee_read < argument_effect, "{expression}");
    }

    #[test]
    fn slc_r206_enclosing_adapter_cannot_duplicate_a_hoisted_count() {
        let plans = slc_construction_plans_with_enclosing_adapter(
            "#![allow(dead_code, unused_unsafe)]\n\
             extern \"C\" { fn calloc(n: usize, size: usize) -> *mut i32; }\n\
             fn next_count() -> usize { 2 }\n\
             pub unsafe fn target() -> i32 {\n\
                 let p: *mut i32 = calloc(next_count(), core::mem::size_of::<i32>());\n\
                 *p.offset(1)\n\
             }\n",
            true,
        );
        assert_eq!(plans.len(), 1);
        assert!(
            plans[0].replacement.is_none(),
            "enclosing edit discarded argument bindings: {:?}",
            plans[0]
        );
        assert!(
            plans[0]
                .hold_reason
                .as_deref()
                .is_some_and(|reason| reason.starts_with("composition-crossing-unhoistable:"))
        );
    }

    /// Addendum 206 E09: a count with side effects must occur once in the
    /// rendered expression, shared by the allocation and its slice length.
    #[test]
    fn slc_r206_allocator_count_is_evaluated_once() {
        let plans = slc_construction_plans(
            "#![allow(dead_code, unused_unsafe)]\n\
             extern \"C\" { fn calloc(n: usize, size: usize) -> *mut i32; }\n\
             fn next_count(calls: &mut usize) -> usize { *calls += 1; 2 }\n\
             pub unsafe fn target(calls: &mut usize) -> i32 {\n\
                 let p: *mut i32 = calloc(next_count(calls), core::mem::size_of::<i32>());\n\
                 *p.offset(1)\n\
             }\n",
        );
        assert_eq!(plans.len(), 1);
        let expression = plans[0].replacement.as_ref().expect("constructor");
        assert_eq!(
            expression.matches("next_count(calls)").count(),
            1,
            "{expression}"
        );
        assert!(expression.contains("let __crat_slice_arg_"), "{expression}");

        // Execute only this bounded, valid-memory constructor control. The
        // allocator is a local closure returning a live two-element array.
        let directory = std::env::temp_dir().join(format!("crat-slc-r206-{}", std::process::id()));
        std::fs::create_dir_all(&directory).expect("control directory");
        let program = format!(
            r#"
            fn next_count(calls: &mut usize) -> usize {{ *calls += 1; 2 }}
            fn main() {{
                let mut count = 0;
                let calls = &mut count;
                let mut values = [1i32, 2i32];
                let raw = values.as_mut_ptr();
                let calloc = |n: usize, size: usize| {{
                    assert_eq!(n, 2);
                    assert_eq!(size, core::mem::size_of::<i32>());
                    raw
                }};
                // SAFETY: calloc returns this live, initialized, aligned
                // array, and the exact evidence length is its two elements.
                let result = unsafe {{ {expression} }};
                assert_eq!(result, &[1, 2]);
                assert_eq!(*calls, 1);
            }}
        "#
        );
        let source = directory.join("control.rs");
        let binary = directory.join("control");
        std::fs::write(&source, program).expect("control source");
        let compiled = std::process::Command::new("rustc")
            .arg("--edition=2024")
            .arg(&source)
            .arg("-o")
            .arg(&binary)
            .output()
            .expect("control compiler");
        assert!(
            compiled.status.success(),
            "{}",
            String::from_utf8_lossy(&compiled.stderr)
        );
        let executed = std::process::Command::new(&binary)
            .output()
            .expect("control run");
        assert!(
            executed.status.success(),
            "{}",
            String::from_utf8_lossy(&executed.stderr)
        );
        std::fs::remove_dir_all(directory).expect("remove control artifacts");
    }

    /// Addendum 206 E13: provenance inheritance cannot change a fabricated
    /// length into evidence or lose the per-site waiver.
    #[test]
    fn slc_r206_dependent_local_keeps_its_fallback_receipt() {
        let plans = slc_construction_plans(
            "#![allow(dead_code, unused_unsafe)]\n\
             pub unsafe fn target(src: *const i32) -> i32 {\n\
                 let p: *const i32 = src;\n\
                 let q: *const i32 = p;\n\
                 *p.offset(1) + *q.offset(1)\n\
             }\n",
        );
        assert_eq!(plans.len(), 2);
        assert_eq!(
            plans
                .iter()
                .filter(|plan| plan.length.provenance_receipt().contains("inherited:"))
                .count(),
            1,
            "the dependent source association must be retained as provenance"
        );
        for plan in plans {
            assert_eq!(
                plan.length.extent(),
                MechanicalExtent::Fallback {
                    receipt: FALLBACK_EXTENT_RECEIPT.to_owned(),
                    waiver_id: SLICE_EXTENT_WAIVER_ID.to_owned(),
                },
                "dependent local changed its inherited extent: {plan:?}"
            );
        }
    }

    /// Addendum 206 E05/E10: a product appearing inside a sum is not exact
    /// divisibility evidence; production must receipt the fallback.
    #[test]
    fn slc_r206_nondivisible_sum_uses_receipted_fallback() {
        let construction = Construction::Alloc {
            callee: "malloc".to_owned(),
            size: "items * core::mem::size_of::<i32>() + 1".to_owned(),
            count: None,
        };
        assert!(allocation_length(&construction, "i32").is_none());
        let plans = slc_construction_plans(
            "#![allow(dead_code, unused_unsafe)]\n\
             extern \"C\" { fn malloc(size: usize) -> *mut i32; }\n\
             pub unsafe fn target(items: usize) -> i32 {\n\
                 let p: *mut i32 = malloc(items * core::mem::size_of::<i32>() + 1);\n\
                 *p.offset(1)\n\
             }\n",
        );
        assert_eq!(plans.len(), 1);
        assert!(plans[0].length.extent().is_fallback());
    }

    /// Addendum 206 E11: integer adjacency does not license length evidence.
    #[test]
    fn slc_r206_adjacent_integer_is_not_length_evidence() {
        let plans = slc_construction_plans(
            "#![allow(dead_code, unused_unsafe)]\n\
             pub unsafe fn target(src: *const i32, flag: usize) -> i32 {\n\
                 let p: *const i32 = src;\n\
                 *p.offset(1) + flag as i32\n\
             }\n",
        );
        assert_eq!(plans.len(), 1);
        assert!(
            plans[0].length.extent().is_fallback(),
            "{:?}",
            plans[0].length
        );
        assert!(
            plans[0]
                .length
                .provenance_receipt()
                .starts_with("associated-argument-inert:no-exported-length-association:")
        );
    }

    #[test]
    fn slc_length_precedence_requires_exact_typed_byte_evidence() {
        let calloc = Construction::Alloc {
            callee: "calloc".to_owned(),
            size: "core::mem::size_of::<i32>()".to_owned(),
            count: Some("items".to_owned()),
        };
        let selected = allocation_length(&calloc, "i32").expect("exact element count");
        assert_eq!(selected.expression, "(items) as usize");
        assert!(matches!(
            selected.source,
            SliceLengthSource::AllocationElementCount { .. }
        ));

        // R206: whole-expression proof comes from HIR, not substring text.
        let plans = slc_construction_plans(
            "#![allow(dead_code, unused_unsafe)]\n\
             extern \"C\" { fn malloc(size: usize) -> *mut i32; }\n\
             pub unsafe fn target(items: usize) -> i32 {\n\
                 let p: *mut i32 = malloc(items * core::mem::size_of::<i32>());\n\
                 *p.offset(1)\n\
             }\n",
        );
        assert_eq!(plans.len(), 1);
        let selected = &plans[0].length;
        assert!(selected.expression.contains("size_of::<i32>"));
        assert!(matches!(
            selected.source,
            SliceLengthSource::AllocationByteCount { .. }
        ));

        let ambiguous = Construction::Alloc {
            callee: "malloc".to_owned(),
            size: "items * 3".to_owned(),
            count: None,
        };
        assert!(
            allocation_length(&ambiguous, "i32").is_none(),
            "non-divisibility evidence must fall through to the typed fallback"
        );
    }

    #[test]
    fn slc_renderer_preserves_context_null_order_and_single_evaluation() {
        let unsafe_body =
            render_slice_constructor("next_ptr()", "i32", true, false, "8usize", true, 4);
        assert_eq!(unsafe_body.matches("next_ptr()").count(), 1);
        assert!(unsafe_body.starts_with("core::slice::from_raw_parts_mut("));
        assert!(!unsafe_body.starts_with("unsafe {"));

        let safe_body =
            render_slice_constructor("next_ptr()", "i32", false, false, "8usize", false, 4);
        assert!(safe_body.starts_with("unsafe { core::slice::from_raw_parts("));
        assert_eq!(safe_body.matches("next_ptr()").count(), 1);

        let nullable = render_slice_constructor("next_ptr()", "i32", true, true, "8usize", true, 4);
        assert_eq!(nullable.matches("next_ptr()").count(), 1);
        assert!(nullable.contains("__crat_slice_ptr_4.as_mut().map("));
        assert!(!nullable.contains("&mut *next_ptr()"));
    }
}
