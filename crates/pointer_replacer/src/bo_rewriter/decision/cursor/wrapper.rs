//! R394: signed cursors retain the delivered base and use the legacy wrapper's
//! runtime slice checks. Selection consumes offset-sign facts, not a window proof.
use rustc_hir::{
    self as hir,
    def::Res,
    intravisit::{self, Visitor},
};
use rustc_middle::{mir::Local, ty};

use super::{CursorHold, CursorPlan, DeliveredBase, DeliveredBaseProvider, emission};
use crate::bo_rewriter::decision::{Ctx, Decision, Subject, SubjectKind, emitability::UseEdit};

fn local(e: &hir::Expr<'_>) -> Option<hir::HirId> {
    match e.kind {
        hir::ExprKind::Path(hir::QPath::Resolved(_, p)) => match p.res {
            Res::Local(id) => Some(id),
            _ => None,
        },
        _ => None,
    }
}
fn contains(e: &hir::Expr<'_>, id: hir::HirId) -> bool {
    struct Find {
        id: hir::HirId,
        found: bool,
    }
    impl<'v> Visitor<'v> for Find {
        fn visit_expr(&mut self, e: &'v hir::Expr<'v>) {
            self.found |= local(e) == Some(self.id);
            intravisit::walk_expr(self, e);
        }
    }
    let mut v = Find { id, found: false };
    v.visit_expr(e);
    v.found
}
fn text(ctx: &Ctx<'_, '_>, e: &hir::Expr<'_>) -> Result<String, CursorHold> {
    ctx.tcx
        .sess
        .source_map()
        .span_to_snippet(e.span)
        .map_err(|_| CursorHold::SourceUnavailable)
}
pub(crate) fn type_text(
    mutable: bool,
    optional: bool,
    pointee: &str,
    lifetime: Option<&str>,
) -> String {
    let lt = lifetime.unwrap_or("_").trim_start_matches('\'');
    let ty = format!(
        "crate::slice_cursor::SliceCursor{}<'{lt}, {pointee}>",
        if mutable { "Mut" } else { "" }
    );
    if optional {
        format!("Option<{ty}>")
    } else {
        ty
    }
}
fn constructor(mutable: bool) -> &'static str {
    if mutable {
        "crate::slice_cursor::SliceCursorMut"
    } else {
        "crate::slice_cursor::SliceCursor"
    }
}
fn model_ref(ctx: &Ctx<'_, '_>, s: &Subject) -> bool {
    use crate::analyses::borrow_ownership::{SlotKind, solver::SlotRef};
    ctx.slots
        .fn_local_slots
        .get(&s.fn_did)
        .and_then(|slots| slots.slot_for_local_depth(s.local, 0))
        .and_then(|slot| ctx.model.get(&SlotRef::Local(s.fn_did, slot)))
        == Some(&SlotKind::Ref)
}
struct Base {
    parent_cursor: Option<hir::HirId>,
    expression: String,
    binding: Option<hir::HirId>,
    local: Local,
    delivered: Option<DeliveredBase>,
    fallback: bool,
    composed: Vec<rustc_span::Span>,
}
/// A shared cursor over an element loaded from a delivered outer table:
/// `let p: *const T = *table.offset(k)` with `table` a delivered slice. The
/// loaded element is a bare raw base and takes the same receipted fallback as
/// a raw path; the constructor composes the outer's own element rewrite so the
/// two edits never collide at the initializer span. A written element takes the
/// exclusive view only when the table is named once in the function (relay 003).
fn table_element_base(
    ctx: &Ctx<'_, '_>,
    s: &Subject,
    e: &hir::Expr<'_>,
    entries: &[(Subject, Decision)],
    prospective: Option<&super::ProspectiveTable>,
) -> Result<Base, CursorHold> {
    if !model_ref(ctx, s) {
        return Err(CursorHold::RefMissing);
    }
    let hir::ExprKind::Unary(hir::UnOp::Deref, pointer) = e.kind else {
        return Err(CursorHold::BaseMissing);
    };
    let root = source_binding(ctx.tcx, s.fn_did, pointer).ok_or(CursorHold::BaseMissing)?;
    // A written element takes an exclusive view only when it is the function's
    // only view of that buffer: the table is named exactly once (this load),
    // so no other element load and no escape of the table exists (relay 003).
    if s.mutable && !table_named_once(ctx.tcx, s.fn_did, root) {
        return Err(CursorHold::BaseMissing);
    }
    let (_, decision) = entries
        .iter()
        .find(|(source, _)| source.fn_did == s.fn_did && source.hir_id == root)
        .ok_or(CursorHold::BaseMissing)?;
    // A table that delivers its inner level (nested's N1) hands the element as
    // a slice, not a pointer: the constructor is then `new(t[k])`, which takes
    // NO length, so this base fabricates nothing and is evidence-backed by
    // construction (`fallback = false`, 027 (b)).
    // **R512-4.** The prospective flip is this table's, so read the variant it
    // is ABOUT to have. The flip reuses the flat decision's `uses` verbatim, so
    // the element replacement text is the same before and after and only the
    // variant moves; an exclusive row over an element the flip leaves shared is
    // refused rather than rendered.
    let prospective = prospective.filter(|table| table.binding == root);
    if let Some(table) = prospective
        && s.mutable
        && !table.inner_mutable
    {
        return Err(CursorHold::BaseMissing);
    }
    let (uses, delivered_inner) = match decision {
        Decision::Slice { uses, .. } => (uses, prospective.is_some()),
        Decision::NestedSlice { uses, .. } => (uses, true),
        Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Opt { .. }
        | Decision::Box(_)
        | Decision::Cursor { .. }
        | Decision::Degraded(_) => return Err(CursorHold::BaseMissing),
    };
    let element = uses
        .iter()
        .find(|edit| edit.span.source_callsite() == e.span.source_callsite())
        .ok_or(CursorHold::BaseMissing)?;
    Ok(Base {
        parent_cursor: None,
        expression: if delivered_inner {
            // Indexing a `&mut [&mut [T]]` yields a place that cannot be moved
            // out of, so an exclusive element is reborrowed.
            format!(
                "{}::new({}{})",
                constructor(s.mutable),
                if s.mutable { "&mut *" } else { "" },
                element.replacement
            )
        } else {
            format!(
                "unsafe {{ {}::from_raw_parts{}({}, crate::FALLBACK_SLICE_EXTENT) }}",
                constructor(s.mutable),
                if s.mutable { "_mut" } else { "" },
                element.replacement
            )
        },
        binding: None,
        local: s.local,
        delivered: Some(DeliveredBase {
            binding: root,
            window_binding: root,
            initializer: ctx.constructions.init_hirs.get(&(s.fn_did, root)).copied(),
            provider: DeliveredBaseProvider::TableElement,
        }),
        fallback: !delivered_inner,
        composed: vec![element.span],
    })
}
/// Exactly one path expression in the owner's body resolves to `binding`.
pub(crate) fn table_named_once(
    tcx: ty::TyCtxt<'_>,
    owner: rustc_hir::def_id::LocalDefId,
    binding: hir::HirId,
) -> bool {
    struct Names {
        binding: hir::HirId,
        count: usize,
    }
    impl<'v> Visitor<'v> for Names {
        fn visit_expr(&mut self, e: &'v hir::Expr<'v>) {
            if local(e) == Some(self.binding) {
                self.count += 1;
            }
            intravisit::walk_expr(self, e);
        }
    }
    let mut names = Names { binding, count: 0 };
    names.visit_body(tcx.hir_body_owned_by(owner));
    names.count == 1
}
/// c2rust spells pointer arithmetic as `&*p.offset(k) as *const T`; the value
/// is `p.offset(k)`. Only a pointee-preserving cast is peeled (`&T` / `*mut T`
/// to `*const T`); a reinterpreting cast stays a cast base.
fn peel_reborrow_idiom<'h, 'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    owner: rustc_hir::def_id::LocalDefId,
    mut e: &'h hir::Expr<'h>,
) -> &'h hir::Expr<'h> {
    fn pointee<'tcx>(t: ty::Ty<'tcx>) -> Option<ty::Ty<'tcx>> {
        match *t.kind() {
            ty::RawPtr(p, _) | ty::Ref(_, p, _) => Some(p),
            _ => None,
        }
    }
    loop {
        match e.kind {
            hir::ExprKind::Cast(inner, _) => {
                let typeck = tcx.typeck(owner);
                if pointee(typeck.expr_ty(e)).is_some()
                    && pointee(typeck.expr_ty(e)) == pointee(typeck.expr_ty(inner))
                {
                    e = inner;
                } else {
                    return e;
                }
            }
            hir::ExprKind::AddrOf(hir::BorrowKind::Ref, _, inner)
                if matches!(inner.kind, hir::ExprKind::Unary(hir::UnOp::Deref, _)) =>
            {
                let hir::ExprKind::Unary(_, pointer) = inner.kind else { unreachable!() };
                e = pointer;
            }
            _ => return e,
        }
    }
}
fn base(
    ctx: &Ctx<'_, '_>,
    s: &Subject,
    e: &hir::Expr<'_>,
    entries: &[(Subject, Decision)],
    prospective: Option<&super::ProspectiveTable>,
) -> Result<Base, CursorHold> {
    let e = peel_reborrow_idiom(ctx.tcx, s.fn_did, e);
    if let Some(raw) = table_origin(ctx, s, e, entries, &mut rustc_hash::FxHashSet::default()) {
        if raw {
            return Err(CursorHold::BaseModelRaw);
        }
        return table_element_base(ctx, s, e, entries, prospective);
    }
    if let hir::ExprKind::MethodCall(_, receiver, [delta], _) = e.kind
        && emission::method(ctx.tcx, s.fn_did, e, &["offset", "add", "sub"])
    {
        let mut b = base(ctx, s, receiver, entries, prospective)?;
        b.expression = format!(
            "({}).offset_by({})",
            b.expression,
            delta_text(ctx, s, e, delta)?
        );
        return Ok(b);
    }
    if let hir::ExprKind::MethodCall(_, receiver, [], _) = e.kind
        && emission::method(ctx.tcx, s.fn_did, e, &["as_ptr", "as_mut_ptr"])
        && let ty::Ref(_, element, mutable) = *ctx.tcx.typeck(s.fn_did).expr_ty(receiver).kind()
        && matches!(element.kind(), ty::Slice(_) | ty::Array(..))
    {
        let binding = local(receiver).ok_or(CursorHold::BaseMissing)?;
        if s.mutable && !mutable.is_mut() {
            return Err(CursorHold::ScheduleMissing);
        }
        let root = ctx
            .tcx
            .hir_body_owned_by(s.fn_did)
            .params
            .iter()
            .position(
                |p| matches!(p.pat.kind, hir::PatKind::Binding(_, id, _, None) if id == binding),
            )
            .map(|i| Local::from_usize(i + 1))
            .or_else(|| {
                entries
                    .iter()
                    .find(|(other, _)| other.fn_did == s.fn_did && other.hir_id == binding)
                    .map(|(other, _)| other.local)
            })
            .unwrap_or(s.local);
        return Ok(Base {
            parent_cursor: None,
            expression: format!(
                "{}::new(&{}({})[..])",
                constructor(s.mutable),
                if s.mutable { "mut " } else { "" },
                text(ctx, receiver)?
            ),
            binding: Some(binding),
            local: root,
            delivered: Some(DeliveredBase {
                binding,
                window_binding: binding,
                initializer: match ctx.tcx.parent_hir_node(binding) {
                    hir::Node::LetStmt(decl) => decl.init.map(|e| e.hir_id),
                    _ => None,
                },
                provider: DeliveredBaseProvider::OriginalSlice,
            }),
            fallback: false,
            composed: vec![],
        });
    }
    // A delivered slice PARAMETER is the base itself at the safe body
    // (`in_0: &[T]`); the window is the binding's runtime length.
    if let Some(binding) = local(e)
        && let Some((source, decision)) = entries
            .iter()
            .find(|(source, _)| source.fn_did == s.fn_did && source.hir_id == binding)
        && matches!(source.kind, SubjectKind::Param { .. })
        && let Some(mutable) = slice_mutability(decision)
    {
        if s.mutable && !mutable {
            return Err(CursorHold::ScheduleMissing);
        }
        return Ok(Base {
            parent_cursor: None,
            expression: format!("{}::new({})", constructor(s.mutable), text(ctx, e)?),
            binding: Some(binding),
            local: source.local,
            delivered: Some(DeliveredBase {
                binding,
                window_binding: binding,
                initializer: None,
                provider: DeliveredBaseProvider::SliceParameter,
            }),
            fallback: false,
            composed: vec![],
        });
    }
    if let Some(binding) = local(e)
        && let Some((source, decision)) = entries
            .iter()
            .find(|(source, _)| source.fn_did == s.fn_did && source.hir_id == binding)
        && let Some(mutable) = slice_mutability(decision)
    {
        if s.mutable && !mutable {
            return Err(CursorHold::ScheduleMissing);
        }
        let table = crate::bo_rewriter::decision::DecisionTable {
            entries: entries.to_vec(),
            input_interfaces: ctx.input_interfaces.clone(),
            ..Default::default()
        };
        let producer = crate::bo_rewriter::decision::construction::plan_slice_constructions(
            ctx.tcx,
            &table,
            ctx.constructions,
            ctx.family_policy,
        )
        .into_iter()
        .find(|p| {
            p.node == (s.fn_did, binding)
                && p.hold_reason.is_none()
                && p.replacement.is_some()
                && !p.nullable
        })
        .ok_or(CursorHold::BaseMissing)?;
        return Ok(Base {
            parent_cursor: None,
            expression: format!(
                "{}::new(&{}({})[..])",
                constructor(s.mutable),
                if s.mutable { "mut " } else { "" },
                text(ctx, e)?
            ),
            binding: Some(binding),
            local: source.local,
            delivered: Some(DeliveredBase {
                binding,
                window_binding: binding,
                initializer: Some(producer.init_hir),
                provider: DeliveredBaseProvider::Slice { producer },
            }),
            fallback: false,
            composed: vec![],
        });
    }
    if let Some(binding) = local(e)
        && let Some((source, source_decision)) = entries
            .iter()
            .find(|(source, _)| source.fn_did == s.fn_did && source.hir_id == binding)
        && candidate_shape_in(ctx, source, source_decision, entries)
    {
        if s.mutable && !source.mutable {
            return Err(CursorHold::ScheduleMissing);
        }
        let name = emission::binding_name(ctx.tcx, source)?;
        // An optional parent lends its view through the checked accessor; a
        // shared cursor copies out of it.
        let parent_optional = source.null_init
            || ctx
                .facts
                .raw_only_uses
                .get(&(source.fn_did, source.hir_id))
                .is_some_and(|uses| uses.iter().any(|(op, _)| op == "is_null"));
        let expression = match (source.mutable, s.mutable, parent_optional) {
            (false, false, false) => name,
            (false, false, true) => format!("(*{name}.as_ref().expect(\"non-null cursor\"))"),
            (true, true, false) => format!("{name}.as_deref_mut()"),
            (true, true, true) => {
                format!("{name}.as_mut().expect(\"non-null cursor\").as_deref_mut()")
            }
            (true, false, false) => format!("{name}.as_deref_mut().as_deref()"),
            (true, false, true) => {
                format!("{name}.as_mut().expect(\"non-null cursor\").as_deref_mut().as_deref()")
            }
            (false, true, _) => return Err(CursorHold::ScheduleMissing),
        };
        return Ok(Base {
            expression,
            parent_cursor: Some(binding),
            binding: None,
            local: source.local,
            delivered: None,
            fallback: false,
            composed: vec![],
        });
    }
    let mut raw_origin = e;
    while let hir::ExprKind::Cast(inner, _) = raw_origin.kind {
        raw_origin = inner;
    }
    if !model_ref(ctx, s) {
        return Err(CursorHold::RefMissing);
    }
    // A raw base gets the same explicitly receipted fallback as a raw-to-slice
    // construction. Calls and opaque expressions need their own producer. A raw
    // pointer FIELD of a struct is a bare raw base for a shared cursor only: an
    // exclusive view over a field the struct may hand out again is not proven.
    let field_base = matches!(raw_origin.kind, hir::ExprKind::Field(..))
        && !s.mutable
        && matches!(
            ctx.tcx.typeck(s.fn_did).expr_ty(raw_origin).kind(),
            ty::RawPtr(..)
        );
    // **R499-1.** `STATIC.as_ptr()` on an array PLACE (tulip's indicator table):
    // the earlier `as_ptr` branch wants a reference receiver and this is the
    // place itself. The input's own spelling is kept — which is what keeps a
    // `static mut` receiver legal exactly where the input already made it so —
    // and only the extent is added, receipted.
    let array_place_as_ptr =
        emission::method(ctx.tcx, s.fn_did, raw_origin, &["as_ptr", "as_mut_ptr"])
            && matches!(raw_origin.kind, hir::ExprKind::MethodCall(_, receiver, [], _)
            if matches!(
                ctx.tcx.typeck(s.fn_did).expr_ty(receiver).kind(),
                ty::Slice(_) | ty::Array(..)
            ));
    if !matches!(raw_origin.kind, hir::ExprKind::Path(_)) && !field_base && !array_place_as_ptr {
        return Err(CursorHold::BaseMissing);
    }
    let method = if s.mutable {
        "from_raw_parts_mut"
    } else {
        "from_raw_parts"
    };
    Ok(Base {
        parent_cursor: None,
        expression: format!(
            "unsafe {{ {}::{method}({}, crate::FALLBACK_SLICE_EXTENT) }}",
            constructor(s.mutable),
            text(ctx, e)?
        ),
        binding: local(raw_origin),
        local: s.local,
        delivered: None,
        fallback: true,
        composed: vec![],
    })
}
fn delta_text(
    ctx: &Ctx<'_, '_>,
    s: &Subject,
    call: &hir::Expr<'_>,
    delta: &hir::Expr<'_>,
) -> Result<String, CursorHold> {
    let hir::ExprKind::MethodCall(segment, _, _, _) = call.kind else {
        return Err(CursorHold::UseUnbuilt);
    };
    if !emission::method(ctx.tcx, s.fn_did, call, &["offset", "add", "sub"]) {
        return Err(CursorHold::UseUnbuilt);
    }
    let d = text(ctx, delta)?;
    Ok(if segment.ident.name.as_str() == "sub" {
        format!("({d} as isize).wrapping_neg()")
    } else {
        format!("({d}) as isize")
    })
}
struct Uses<'a, 'tcx> {
    ctx: &'a Ctx<'a, 'tcx>,
    subject: &'a Subject,
    entries: &'a [(Subject, Decision)],
    name: String,
    init: Option<hir::HirId>,
    base: Option<hir::HirId>,
    optional: bool,
    exclusive_base: bool,
    tail: Option<hir::HirId>,
    bridges: Vec<super::CursorBridge>,
    edits: Vec<UseEdit>,
    hirs: Vec<hir::HirId>,
    hold: Option<CursorHold>,
    peer_bases: Vec<hir::HirId>,
    /// Peer cursor candidates this cursor's admission leans on: a use of this
    /// subject left to the peer's own edit (its initialiser or re-point from
    /// this cursor, this cursor re-pointed from it). Both are cursors of this
    /// family or neither is emitted.
    peer_cursors: Vec<hir::HirId>,
    /// Ephemeral raw copies of this cursor: `let fresh = p;` whose single use
    /// is a deref read. Each carries its typed `raw-op-cursor-local` receipt.
    local_bridges: Vec<super::CursorLocalBridge>,
    /// Chains ceded to a destination's own construction (R487-3(c)): counted so
    /// that a subject whose ONLY handled use is a cede does not take the root.
    ceded: usize,
    /// **R497-3(c).** This subject is a re-seeded walker: exactly one of its
    /// assignments comes from another value, and that assignment CONSTRUCTS a
    /// fresh cursor rather than seeking the existing one.
    re_seeded: bool,
    /// Set when a re-seed construction fabricated its extent (§77): the plan
    /// carries `fallback`, so the count is auditable.
    re_seed_fabricated: bool,
    /// Use edits of the RE-SEED SOURCE that this constructor's text has taken
    /// over: the AST pass applies the constructor at its span and skips these,
    /// exactly as a table element's outer edit is composed.
    re_seed_composed: Vec<rustc_span::Span>,
    prospective: Option<&'a super::ProspectiveTable>,
}
impl Uses<'_, '_> {
    /// **R497-3(c) — the raw view of a re-seed value.** The re-seed source is
    /// whatever the other families decided it is, so the construction takes a
    /// raw pointer out of that form: a still-raw binding is its own text, a
    /// delivered reference is bridged (addendum 130 — emit the bridge, do not
    /// degrade the subject), and anything else holds.
    fn re_seed_raw_view(&self, rhs: &hir::Expr<'_>) -> Option<(String, Option<rustc_span::Span>)> {
        // **A call-rooted re-seed** (`strchr(search, ';')`, `find(key)`): the
        // call itself is the raw value. Its own arguments keep their spans, so
        // an argument this cursor owns is rewritten by ITS edit and spliced
        // into this constructor by the nested-edit composition.
        if let hir::ExprKind::Call(callee, _) = rhs.kind
            && matches!(
                self.ctx.tcx.typeck(self.subject.fn_did).expr_ty(rhs).kind(),
                ty::RawPtr(..)
            )
        {
            // **R513-4 — fail closed on a re-typed interface.** The
            // construction copies the call's SOURCE TEXT, so it is only
            // correct while that text still type-checks against the callee.
            // If the callee is local and ANY of its parameters has been
            // re-typed by another family, the copied text is stale: measured
            // on tulip's `sample::main_0`, the plan was built and then
            // SILENTLY withdrawn by `restore-family-interface-path`, because
            // `ti_find_indicator::name` had become a `&i8`. A hold here is a
            // receipted refusal instead; the delivering form needs the call's
            // arguments adapted at the layer where the seam's own edits live.
            if let ty::FnDef(did, _) = *self
                .ctx
                .tcx
                .typeck(self.subject.fn_did)
                .expr_ty(callee)
                .kind()
                && let Some(callee_did) = did.as_local()
                && self.entries.iter().any(|(other, decision)| {
                    other.fn_did == callee_did
                        && matches!(other.kind, SubjectKind::Param { .. })
                        && match decision {
                            Decision::Degraded(_) => false,
                            Decision::Ref { .. }
                            | Decision::InferredRef { .. }
                            | Decision::Slice { .. }
                            | Decision::Opt { .. }
                            | Decision::Box(_)
                            | Decision::NestedSlice { .. }
                            | Decision::Cursor { .. } => true,
                        }
                })
            {
                return None;
            }
            return text(self.ctx, rhs).ok().map(|t| (t, None));
        }
        let binding = local(rhs)?;
        let (source, decision) = self
            .entries
            .iter()
            .find(|(source, _)| source.fn_did == self.subject.fn_did && source.hir_id == binding)?;
        let name = emission::binding_name(self.ctx.tcx, source).ok()?;
        // The source's OWN edit at this span (an option's `unwrap`, a slice's
        // presentation) is taken over by this constructor's text.
        let composed = match decision {
            Decision::Opt { uses, .. } => uses
                .iter()
                .find(|edit| edit.span.source_callsite() == rhs.span.source_callsite())
                .map(|edit| edit.span),
            Decision::Slice { uses, .. } | Decision::NestedSlice { uses, .. } => uses
                .iter()
                .find(|edit| edit.span.source_callsite() == rhs.span.source_callsite())
                .map(|edit| edit.span),
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Box(_)
            | Decision::Cursor { .. }
            | Decision::Degraded(_) => None,
        };
        let view = match decision {
            // Still raw in the emitted program: the text is already a pointer.
            Decision::Degraded(_) => Some(name),
            // A shared reference bridges with `from_ref`. An exclusive one is
            // NOT bridged here: taking a raw `*mut` out of a live `&mut` while
            // the cursor walks it is the retained-alias channel, and this arm
            // has no evidence about it.
            Decision::Ref { mutable: false } | Decision::InferredRef { mutable: false, .. }
                if !self.subject.mutable =>
            {
                Some(format!("core::ptr::from_ref({name})"))
            }
            // A thin optional: `None` re-seeds a null cursor, which the
            // optional form already represents.
            Decision::Opt {
                mutable: false,
                slice: false,
                ..
            } if !self.subject.mutable => Some(format!(
                "{name}.map_or(core::ptr::null(), core::ptr::from_ref)"
            )),
            Decision::Ref { .. }
            | Decision::InferredRef { .. }
            | Decision::Opt { .. }
            | Decision::Slice { .. }
            | Decision::NestedSlice { .. }
            | Decision::Box(_)
            | Decision::Cursor { .. } => None,
        };
        view.map(|view| (view, composed))
    }

    /// The construction a re-seed renders, with its §77 fabricated extent. The
    /// re-seed value has no evidence-backed length here — a length recovered
    /// from the source (json.h's `size` bound) is a later, exact form.
    fn re_seed_construction(&mut self, rhs: &hir::Expr<'_>) -> Option<String> {
        let (raw, composed) = self.re_seed_raw_view(rhs)?;
        self.re_seed_composed.extend(composed);
        self.re_seed_fabricated = true;
        let method = if self.subject.mutable {
            "from_raw_parts_mut"
        } else {
            "from_raw_parts"
        };
        let construction = format!(
            "unsafe {{ {}::{method}({raw}, crate::FALLBACK_SLICE_EXTENT) }}",
            constructor(self.subject.mutable),
        );
        Some(if self.optional {
            format!("Some({construction})")
        } else {
            construction
        })
    }

    /// A derived pointer leaving the function through its raw return: the tail
    /// view's address under the raw-boundary T2 receipt (retained by the caller).
    /// The seam planner owns a return that is lifetime-planned; a return permit
    /// on this subject leaves the site to it.
    fn raw_return(&mut self, value: &hir::Expr<'_>) {
        let owner = self.subject.fn_did;
        let output = self
            .ctx
            .tcx
            .fn_sig(owner)
            .skip_binder()
            .skip_binder()
            .output();
        let ty::RawPtr(_, output_mutability) = *output.kind() else {
            self.hold.get_or_insert(CursorHold::RawBoundaryUnbuilt);
            return;
        };
        if self.optional
            || self.ctx.lifetime_eligibility.is_some_and(|eligibility| {
                eligibility
                    .return_permit((owner, self.subject.hir_id))
                    .is_some()
            })
        {
            self.hold.get_or_insert(CursorHold::RawBoundaryUnbuilt);
            return;
        }
        let method = match (self.subject.mutable, output_mutability) {
            (true, _) => "as_mut_ptr",
            (false, ty::Mutability::Not) => "as_ptr",
            (false, ty::Mutability::Mut) => {
                self.hold.get_or_insert(CursorHold::RawBoundaryUnbuilt);
                return;
            }
        };
        match self.index(value) {
            Ok(d) if local(value) == Some(self.subject.hir_id) => {
                self.push(
                    value,
                    format!("{}.{method}()", self.name),
                    "raw-op-cursor-return",
                );
                let _ = d;
            }
            Ok(d) => self.push(
                value,
                format!("{}.offset_by({d}).{method}()", self.name),
                "raw-op-cursor-return",
            ),
            Err(hold) => {
                self.hold.get_or_insert(hold);
            }
        }
    }

    /// **The `let` form of the peer relation** (R478-5). `let base_ip = input;`
    /// binds a SECOND cursor over the same base — brotli's two-pass terminal —
    /// and the destination is this family's own candidate, so it owns its
    /// constructor (`base()`'s parent-cursor arm renders it as the bare name,
    /// the shared wrapper being `Copy`) and this use needs no edit. Exactly the
    /// assignment form (`data = start`) one statement shape over.
    fn let_bound_peer(&self, e: &hir::Expr<'_>) -> Option<hir::HirId> {
        if self.subject.mutable || self.optional {
            return None;
        }
        let hir::Node::LetStmt(stmt) = self.ctx.tcx.parent_hir_node(e.hir_id) else {
            return None;
        };
        if stmt.init.map(|init| init.hir_id) != Some(e.hir_id) {
            return None;
        }
        let hir::PatKind::Binding(_, destination, _, None) = stmt.pat.kind else {
            return None;
        };
        (destination != self.subject.hir_id
            && self.entries.iter().any(|(other, decision)| {
                other.fn_did == self.subject.fn_did
                    && other.hir_id == destination
                    && !other.mutable
                    && candidate_shape(self.ctx, other, decision)
            }))
        .then_some(destination)
    }

    /// **The ceded chain** (R485-4(g), R487-3(c); wave-6k `7bf81651e`). A chain
    /// rooted at this cursor that initialises a local ANOTHER family types is
    /// rendered by that family's construction, which takes the cursor's own view
    /// as its raw source. One edit on the span, and it is theirs — so this
    /// family records none.
    ///
    /// **R487-3(c)**: the family that delivers the root WITHOUT the chain keeps
    /// it. So the cede is admissible only for a subject that is a cursor on its
    /// own account, which is decided at the end of the walk (`plan`): if every
    /// handled use was a cede, the chain is what would have made this family own
    /// the root, and it does not get to. `fill`'s `ff` is that case — its only
    /// use is the chain, and the slice family delivers the destination today.
    ///
    /// The conditions otherwise mirror `construction::cursor_view_text`:
    /// `offset` (not `add`, whose delta is a `usize`), a bare path receiver, and
    /// a destination the slice family types at this mutability.
    fn ceded_to_a_construction(&self, e: &hir::Expr<'_>) -> bool {
        if self.optional {
            return false;
        }
        let tcx = self.ctx.tcx;
        let hir::ExprKind::MethodCall(segment, receiver, [_], _) = e.kind else {
            return false;
        };
        if segment.ident.as_str() != "offset" || local(receiver) != Some(self.subject.hir_id) {
            return false;
        }
        let hir::Node::LetStmt(stmt) = tcx.parent_hir_node(e.hir_id) else {
            return false;
        };
        if stmt.init.map(|init| init.hir_id) != Some(e.hir_id) {
            return false;
        }
        let hir::PatKind::Binding(_, destination, _, None) = stmt.pat.kind else {
            return false;
        };
        self.entries.iter().any(|(other, decision)| {
            other.fn_did == self.subject.fn_did
                && other.hir_id == destination
                && slice_mutability(decision) == Some(self.subject.mutable)
        })
    }

    /// **W-CUR-LOCAL.** The bare subject initialises an unannotated local whose
    /// SINGLE use is a deref read (`let fresh = p; … *fresh`, urlparser
    /// `strrwd`'s idiom). That copy is not a second cursor and needs no base of
    /// its own: it is this cursor's raw view at the current position, which is
    /// exactly the `raw-op-cursor-local` vocabulary the delivered-base arm
    /// already owns. A write through the copy, a second use, an annotated
    /// declaration, an `&mut` of it, an exclusive cursor, or a destination that
    /// is itself a candidate of this family all fall back to the hold.
    fn ephemeral_copy(&self, e: &hir::Expr<'_>) -> Option<(hir::HirId, hir::HirId)> {
        struct Paths<'a, 'tcx> {
            tcx: ty::TyCtxt<'tcx>,
            binding: hir::HirId,
            sites: Vec<&'a hir::Expr<'a>>,
        }
        impl<'v> Visitor<'v> for Paths<'v, '_> {
            fn visit_expr(&mut self, e: &'v hir::Expr<'v>) {
                if local(e) == Some(self.binding) {
                    self.sites.push(e);
                }
                intravisit::walk_expr(self, e);
            }
        }
        // Shared cursors only. An exclusive cursor with a raw copy of its own
        // region alive beside it is a retained alias, and the model already
        // calls such a subject raw (`RefMissing`) — measured, with a control.
        if self.optional || self.subject.mutable {
            return None;
        }
        let tcx = self.ctx.tcx;
        let hir::Node::LetStmt(stmt) = tcx.parent_hir_node(e.hir_id) else {
            return None;
        };
        if stmt.ty.is_some() || stmt.init.map(|init| init.hir_id) != Some(e.hir_id) {
            return None;
        }
        let hir::PatKind::Binding(_, destination, _, None) = stmt.pat.kind else {
            return None;
        };
        // A destination this family would itself take is not an ephemeral copy;
        // one it leaves raw (any other subject, or none) is.
        if self.entries.iter().any(|(other, decision)| {
            other.fn_did == self.subject.fn_did
                && other.hir_id == destination
                && candidate_shape(self.ctx, other, decision)
        }) {
            return None;
        }
        let mut paths = Paths {
            tcx,
            binding: destination,
            sites: vec![],
        };
        paths.visit_body(tcx.hir_body_owned_by(self.subject.fn_did));
        let [site] = paths.sites[..] else { return None };
        let hir::Node::Expr(read) = tcx.parent_hir_node(site.hir_id) else {
            return None;
        };
        if !matches!(read.kind, hir::ExprKind::Unary(hir::UnOp::Deref, _)) {
            return None;
        }
        if let hir::Node::Expr(parent) = tcx.parent_hir_node(read.hir_id) {
            match parent.kind {
                hir::ExprKind::Assign(lhs, ..) | hir::ExprKind::AssignOp(_, lhs, _)
                    if lhs.hir_id == read.hir_id =>
                {
                    return None;
                }
                hir::ExprKind::AddrOf(_, hir::Mutability::Mut, _) => return None,
                _ => {}
            }
        }
        Some((destination, read.hir_id))
    }

    fn view(&self) -> String {
        if self.optional {
            format!(
                "{}.as_{}().expect(\"non-null cursor\")",
                self.name,
                if self.subject.mutable { "mut" } else { "ref" }
            )
        } else {
            self.name.clone()
        }
    }

    /// The cursor's address for an ordering or difference operand, in the
    /// binding's own pointer mutability: a `*mut T` binding is ordered against
    /// `*mut T` operands, and Rust will not order `*const` against `*mut`. The
    /// value is consumed by the comparison/difference, never retained.
    fn address_view(&self, derived: &str) -> String {
        let value = if self.optional {
            format!(
                "{}.as_ref().map_or(core::ptr::null(), |cursor| cursor{derived}.addr())",
                self.name
            )
        } else {
            format!("{}{derived}.addr()", self.name)
        };
        let mutable_pointer = matches!(
            self.ctx
                .tcx
                .typeck(self.subject.fn_did)
                .node_type(self.subject.hir_id)
                .kind(),
            ty::RawPtr(_, hir::Mutability::Mut)
        );
        if mutable_pointer {
            format!("({value}).cast_mut()")
        } else {
            value
        }
    }

    fn push(&mut self, e: &hir::Expr<'_>, replacement: String, kind: &'static str) {
        self.edits.push(UseEdit {
            span: e.span,
            replacement,
            bridge_kind: kind,
        });
        self.hirs.push(e.hir_id);
    }

    /// The bare subject, possibly under an offset chain, is the right-hand side
    /// of an assignment into a shared peer cursor of this family; the peer owns
    /// that edit (`data = start`, `end = data.offset(k)`).
    fn assigned_to_shared_peer(&self, e: &hir::Expr<'_>) -> Option<hir::HirId> {
        let mut node = e.hir_id;
        loop {
            let hir::Node::Expr(parent) = self.ctx.tcx.parent_hir_node(node) else {
                return None;
            };
            match parent.kind {
                hir::ExprKind::MethodCall(_, receiver, [_], _)
                    if receiver.hir_id == node
                        && emission::method(
                            self.ctx.tcx,
                            self.subject.fn_did,
                            parent,
                            &["offset", "add", "sub"],
                        ) =>
                {
                    node = parent.hir_id;
                }
                hir::ExprKind::Assign(lhs, rhs, _) if rhs.hir_id == node => {
                    return local(lhs).filter(|&peer| {
                        peer != self.subject.hir_id
                            && self.entries.iter().any(|(other, decision)| {
                                other.fn_did == self.subject.fn_did
                                    && other.hir_id == peer
                                    && !other.mutable
                                    && candidate_shape(self.ctx, other, decision)
                            })
                    });
                }
                _ => return None,
            }
        }
    }

    fn peer_index(&self, e: &hir::Expr<'_>, peer: hir::HirId) -> Result<String, CursorHold> {
        if local(e) == Some(peer) {
            return Ok("0isize".into());
        }
        if let hir::ExprKind::MethodCall(_, receiver, [delta], _) = e.kind {
            let prior = self.peer_index(receiver, peer)?;
            let d = delta_text(self.ctx, self.subject, e, delta)?;
            return Ok(format!("({prior}).wrapping_add({d})"));
        }
        Err(CursorHold::UseUnbuilt)
    }

    fn index(&self, e: &hir::Expr<'_>) -> Result<String, CursorHold> {
        if local(e) == Some(self.subject.hir_id) {
            return Ok("0isize".into());
        }
        if let hir::ExprKind::MethodCall(_, receiver, [delta], _) = e.kind {
            let prior = self.index(receiver)?;
            let d = delta_text(self.ctx, self.subject, e, delta)?;
            return Ok(format!("({prior}).wrapping_add({d})"));
        }
        Err(CursorHold::UseUnbuilt)
    }
}
impl<'v> Visitor<'v> for Uses<'_, '_> {
    fn visit_expr(&mut self, e: &'v hir::Expr<'v>) {
        if Some(e.hir_id) == self.init {
            return;
        }
        // Only comparison/difference observations are scalar operations:
        // the resulting pointer is consumed by the comparison/difference, never
        // retained. Each operand owns its own edit and typed cursor receipt.
        if let Some(operand) = self
            .ctx
            .facts
            .address_observations
            .iter()
            .filter(|observation| scalar_address_operation(observation.op))
            .flat_map(|observation| &observation.operands)
            .find(|operand| {
                operand.node == (self.subject.fn_did, self.subject.hir_id) && operand.span == e.span
            })
        {
            let value = if self.optional {
                format!(
                    "{}.as_ref().map_or(core::ptr::null(), |cursor| cursor.addr())",
                    self.name
                )
            } else {
                format!("{}.addr()", self.name)
            };
            let value =
                if operand.target.mutability == super::super::raw_boundary::RawMutability::Mut {
                    format!("({value}).cast_mut()")
                } else {
                    value
                };
            self.push(e, value, "cursor-address");
            return;
        }
        if self
            .ctx
            .facts
            .address_observations
            .iter()
            .any(|observation| {
                scalar_address_operation(observation.op) && observation.span == e.span
            })
        {
            intravisit::walk_expr(self, e);
            return;
        }
        // A comparison with an offset-chain operand has no address observation
        // (the shared collector wants two bare locals): each side rooted at this
        // subject takes the derived cursor's address, `S.offset_by(k).addr()`.
        if let hir::ExprKind::Binary(op, lhs, rhs) = e.kind
            && matches!(
                op.node,
                hir::BinOpKind::Lt
                    | hir::BinOpKind::Le
                    | hir::BinOpKind::Gt
                    | hir::BinOpKind::Ge
                    | hir::BinOpKind::Eq
                    | hir::BinOpKind::Ne
            )
            && [lhs, rhs].iter().any(|side| {
                source_binding(self.ctx.tcx, self.subject.fn_did, side) == Some(self.subject.hir_id)
            })
            && [lhs, rhs].iter().any(|side| {
                matches!(side.kind, hir::ExprKind::MethodCall(..))
                    && source_binding(self.ctx.tcx, self.subject.fn_did, side).is_some_and(|root| {
                        root == self.subject.hir_id
                            || self.entries.iter().any(|(other, decision)| {
                                other.fn_did == self.subject.fn_did
                                    && other.hir_id == root
                                    && candidate_shape_in(self.ctx, other, decision, self.entries)
                            })
                    })
            })
            && !self
                .ctx
                .facts
                .address_observations
                .iter()
                .any(|observation| observation.span == e.span)
        {
            for side in [lhs, rhs] {
                if source_binding(self.ctx.tcx, self.subject.fn_did, side)
                    != Some(self.subject.hir_id)
                {
                    self.visit_expr(side);
                    continue;
                }
                let address = |derived: &str| self.address_view(derived);
                match self.index(side) {
                    Ok(_) if local(side) == Some(self.subject.hir_id) => {
                        let value = address("");
                        self.push(side, value, "cursor-address");
                    }
                    Ok(d) => {
                        let value = address(&format!(".offset_by({d})"));
                        self.push(side, value, "cursor-address");
                    }
                    Err(hold) => {
                        self.hold.get_or_insert(hold);
                    }
                }
            }
            return;
        }
        // A difference whose other operand is not a bare local has no address
        // observation; the receiver chain rooted at this subject takes its
        // address and the other operand is left to its own subject.
        if let hir::ExprKind::MethodCall(_, receiver, [other], _) = e.kind
            && emission::method(self.ctx.tcx, self.subject.fn_did, e, &["offset_from"])
            && source_binding(self.ctx.tcx, self.subject.fn_did, receiver)
                == Some(self.subject.hir_id)
            && !self
                .ctx
                .facts
                .address_observations
                .iter()
                .any(|observation| observation.span == e.span)
        {
            let address = |derived: &str| self.address_view(derived);
            match self.index(receiver) {
                Ok(_) if local(receiver) == Some(self.subject.hir_id) => {
                    let value = address("");
                    self.push(receiver, value, "cursor-address");
                }
                Ok(d) => {
                    let value = address(&format!(".offset_by({d})"));
                    self.push(receiver, value, "cursor-address");
                }
                Err(hold) => {
                    self.hold.get_or_insert(hold);
                }
            }
            self.visit_expr(other);
            return;
        }
        // The c2rust reborrow idiom `&*S.offset(k) as *const T` rooted at this
        // subject: a peer's constructor when it initialises or is assigned into
        // a cursor candidate (that peer owns the edit); otherwise the derived
        // address, where a raw value is compared or differenced.
        if matches!(e.kind, hir::ExprKind::Cast(..) | hir::ExprKind::AddrOf(..))
            && let chain = peel_reborrow_idiom(self.ctx.tcx, self.subject.fn_did, e)
            && !std::ptr::eq(chain, e)
            && !matches!(chain.kind, hir::ExprKind::AddrOf(..))
            && source_binding(self.ctx.tcx, self.subject.fn_did, chain) == Some(self.subject.hir_id)
        {
            let parent = self.ctx.tcx.parent_hir_node(e.hir_id);
            let peer_owned = match parent {
                hir::Node::LetStmt(decl) => Some(decl.pat.hir_id).filter(|&peer| {
                    decl.init.is_some_and(|init| init.hir_id == e.hir_id)
                        && self.entries.iter().any(|(other, decision)| {
                            other.fn_did == self.subject.fn_did
                                && other.hir_id == peer
                                && candidate_shape(self.ctx, other, decision)
                        })
                }),
                hir::Node::Expr(parent) => match parent.kind {
                    hir::ExprKind::Assign(lhs, rhs, _) if rhs.hir_id == e.hir_id => local(lhs)
                        .filter(|&peer| {
                            self.entries.iter().any(|(other, decision)| {
                                other.fn_did == self.subject.fn_did
                                    && other.hir_id == peer
                                    && candidate_shape(self.ctx, other, decision)
                            })
                        }),
                    _ => None,
                },
                _ => None,
            };
            if let Some(peer) = peer_owned {
                self.peer_cursors.push(peer);
                return;
            }
            // The idiom handed DIRECTLY to a local callee whose parameter another
            // family delivers as a slice (`ToUpperCase(&mut *dst.offset(k))`,
            // brotli's dictionary-word transform): the callee walks from that
            // address, so the argument is this cursor's tail view at the index —
            // the same view a whole-cursor argument takes, and the seam receipts
            // it under the callee's own arm.
            if let hir::Node::Expr(call) = parent
                && let hir::ExprKind::Call(callee, args) = call.kind
                && let Some(index) = args.iter().position(|arg| arg.hir_id == e.hir_id)
                && let ty::FnDef(did, _) =
                    *self.ctx.tcx.typeck(self.subject.fn_did).expr_ty(callee).kind()
                && let Some(local_callee) = did.as_local()
                && let Some(want) = self
                    .entries
                    .iter()
                    .find(|(s, _)| s.fn_did == local_callee && matches!(s.kind, SubjectKind::Param { hir_index } if hir_index == index))
                    .and_then(|(_, decision)| {
                        slice_mutability(decision).or_else(|| cursor_parameter_mutability(decision))
                    })
                && (self.subject.mutable || !want)
            {
                match self.index(chain) {
                    Ok(d) => {
                        let view = if want { "as_slice_mut" } else { "as_slice" };
                        self.push(
                            e,
                            format!("{}.offset_by({d}).{view}()", self.view()),
                            "cursor-element",
                        );
                    }
                    Err(hold) => {
                        self.hold.get_or_insert(hold);
                    }
                }
                return;
            }
            // Otherwise the idiom's chain is this cursor's derived address where
            // the value is compared or differenced, or stored into a peer whose
            // own edit composes over this inner one; the `&*` and the cast keep
            // their raw meaning. A cast returned as-is stays off the raw-return
            // bridge (the C-N2 control), so any other position holds.
            let composes = match parent {
                hir::Node::LetStmt(decl) => decl.init.is_some_and(|init| init.hir_id == e.hir_id),
                hir::Node::Expr(parent) => match parent.kind {
                    hir::ExprKind::Assign(_, rhs, _) => rhs.hir_id == e.hir_id,
                    hir::ExprKind::Binary(..) => true,
                    hir::ExprKind::MethodCall(_, _, [arg], _) => {
                        arg.hir_id == e.hir_id
                            && emission::method(
                                self.ctx.tcx,
                                self.subject.fn_did,
                                parent,
                                &["offset_from"],
                            )
                    }
                    _ => false,
                },
                _ => false,
            };
            if !composes {
                self.hold.get_or_insert(CursorHold::BorrowedElementUnbuilt);
                return;
            }
            let address = |derived: &str| {
                if self.optional {
                    format!(
                        "{}.as_ref().map_or(core::ptr::null(), |cursor| cursor{derived}.addr())",
                        self.name
                    )
                } else {
                    format!("{}{derived}.addr()", self.name)
                }
            };
            match self.index(chain) {
                Ok(_) if local(chain) == Some(self.subject.hir_id) => {
                    let value = address("");
                    self.push(chain, value, "cursor-address");
                }
                Ok(d) => {
                    let value = address(&format!(".offset_by({d})"));
                    self.push(chain, value, "cursor-address");
                }
                Err(hold) => {
                    self.hold.get_or_insert(hold);
                }
            }
            return;
        }
        if matches!(e.kind, hir::ExprKind::AddrOf(..)) && contains(e, self.subject.hir_id) {
            self.hold.get_or_insert(CursorHold::BorrowedElementUnbuilt);
            return;
        }
        // The derived binding owns its constructor edit; the parent lends its
        // full base only through the wrapper's checked Rust reborrow API.
        if self.index(e).is_ok()
            && let Some((child, _)) = self.entries.iter().find(|(child, child_decision)| {
                child.fn_did == self.subject.fn_did
                    && child.hir_id != self.subject.hir_id
                    && candidate_shape(self.ctx, child, child_decision)
                    && self
                        .ctx
                        .constructions
                        .init_hirs
                        .get(&(child.fn_did, child.hir_id))
                        == Some(&e.hir_id)
            })
        {
            self.peer_cursors.push(child.hir_id);
            return;
        }
        if let hir::ExprKind::Assign(lhs, rhs, _) = e.kind
            && local(lhs) == Some(self.subject.hir_id)
        {
            // A shared cursor re-pointed from a peer cursor of the same base
            // family: `data = start` needs no edit (the wrapper is `Copy`),
            // `end = data.offset(k)` takes the peer's derived cursor. Both
            // peers are cursors of this family or neither is emitted.
            if !self.subject.mutable
                && !self.optional
                && let Some(peer) = source_binding(self.ctx.tcx, self.subject.fn_did, rhs)
                && peer != self.subject.hir_id
                && self.entries.iter().any(|(other, decision)| {
                    other.fn_did == self.subject.fn_did
                        && other.hir_id == peer
                        && !other.mutable
                        && candidate_shape(self.ctx, other, decision)
                })
            {
                self.peer_cursors.push(peer);
                if local(rhs) != Some(peer)
                    && let Ok(d) = self.peer_index(rhs, peer)
                {
                    let name = emission::binding_name(
                        self.ctx.tcx,
                        self.entries
                            .iter()
                            .find(|(other, _)| other.hir_id == peer)
                            .map(|(other, _)| other)
                            .expect("peer entry"),
                    );
                    match name {
                        Ok(name) => {
                            self.push(rhs, format!("{name}.offset_by({d})"), "cursor-advance")
                        }
                        Err(hold) => {
                            self.hold.get_or_insert(hold);
                        }
                    }
                } else if local(rhs) != Some(peer) {
                    self.hold.get_or_insert(CursorHold::UseUnbuilt);
                }
                return;
            }
            match self.index(rhs) {
                Ok(d) => {
                    self.push(
                        e,
                        format!(
                            "{}.seek({d})",
                            if self.optional {
                                format!("{}.as_mut().expect(\"non-null cursor\")", self.name)
                            } else {
                                self.name.clone()
                            }
                        ),
                        "cursor-advance",
                    );
                }
                Err(hold) => {
                    // A shared cursor re-pointed to a delivered base another
                    // family owns (a slice peer, `data = start`) or to a parent
                    // cursor: the base's own constructor, never a fallback.
                    if !self.optional && !self.subject.mutable {
                        match base(self.ctx, self.subject, rhs, self.entries, self.prospective) {
                            Ok(b)
                                if (b.delivered.is_some() || b.parent_cursor.is_some())
                                    && !b.fallback =>
                            {
                                self.peer_bases.extend(peer_base(&b));
                                self.push(
                                    e,
                                    format!("{} = {}", self.name, b.expression),
                                    "cursor-constructor",
                                );
                            }
                            _ => {
                                // **R497-3(c).** A RE-SEEDED walker constructs
                                // a fresh cursor here instead of holding.
                                match self
                                    .re_seeded
                                    .then(|| self.re_seed_construction(rhs))
                                    .flatten()
                                {
                                    Some(construction) => self.push(
                                        e,
                                        format!("{} = {construction}", self.name),
                                        // The existing constructor vocabulary:
                                        // a re-seed IS a construction, and the
                                        // §77 extent receipt rides `fallback`
                                        // through the same channel.
                                        "cursor-constructor",
                                    ),
                                    None => {
                                        self.hold.get_or_insert(hold);
                                    }
                                }
                            }
                        }
                        return;
                    }
                    if self.optional && !self.subject.mutable {
                        match base(self.ctx, self.subject, rhs, self.entries, self.prospective) {
                            Ok(b)
                                if (b.delivered.is_some() || b.parent_cursor.is_some())
                                    && !b.fallback =>
                            {
                                self.peer_bases.extend(peer_base(&b));
                                self.push(
                                    e,
                                    format!("{} = Some({})", self.name, b.expression),
                                    "cursor-constructor",
                                )
                            }
                            _ => {
                                // **R497-3(c)** — as above, with the Option.
                                match self
                                    .re_seeded
                                    .then(|| self.re_seed_construction(rhs))
                                    .flatten()
                                {
                                    Some(construction) => self.push(
                                        e,
                                        format!("{} = {construction}", self.name),
                                        // The existing constructor vocabulary:
                                        // a re-seed IS a construction, and the
                                        // §77 extent receipt rides `fallback`
                                        // through the same channel.
                                        "cursor-constructor",
                                    ),
                                    None => {
                                        self.hold.get_or_insert(hold);
                                    }
                                }
                            }
                        }
                    } else {
                        self.hold.get_or_insert(hold);
                    }
                }
            }
            return;
        }
        if let hir::ExprKind::Ret(Some(value)) = e.kind
            && source_binding(self.ctx.tcx, self.subject.fn_did, value) == Some(self.subject.hir_id)
        {
            self.raw_return(value);
            return;
        }
        if Some(e.hir_id) == self.tail
            && source_binding(self.ctx.tcx, self.subject.fn_did, e) == Some(self.subject.hir_id)
        {
            self.raw_return(e);
            return;
        }
        // Only a deref whose pointer chain is rooted at this subject is this
        // subject's element; an enclosing deref of another pointer that merely
        // carries the subject inside its offset operand is walked instead.
        if let hir::ExprKind::Unary(hir::UnOp::Deref, pointer) = e.kind
            && source_binding(self.ctx.tcx, self.subject.fn_did, pointer)
                == Some(self.subject.hir_id)
        {
            match self.index(pointer) {
                Ok(i) => self.push(e, format!("{}[{i}]", self.view()), "cursor-element"),
                Err(hold) => {
                    self.hold.get_or_insert(hold);
                }
            }
            return;
        }
        if let hir::ExprKind::MethodCall(_, receiver, [], _) = e.kind
            && local(receiver) == Some(self.subject.hir_id)
            && emission::method(self.ctx.tcx, self.subject.fn_did, e, &["is_null"])
        {
            self.push(e, format!("{}.is_none()", self.name), "cursor-element");
            return;
        }
        if let hir::ExprKind::Call(callee, args) = e.kind {
            for (index, arg) in args.iter().enumerate() {
                // A cursor (bare, or an offset chain rooted at it) CAST to a raw
                // pointer at a FOREIGN formal — `memcpy(dst, next_emit as *const
                // c_void, n)`, brotli's fragment compressors. The callee consumes
                // an opaque address, so the cursor's own raw view goes inside the
                // cast and the cast keeps its text; the boundary owns the site's
                // retention receipt, and a site it does not open stays held. A
                // LOCAL callee's void parameter is the region family's subject,
                // not this one's.
                if let hir::ExprKind::Cast(operand, _) = arg.kind
                    && source_binding(self.ctx.tcx, self.subject.fn_did, operand)
                        == Some(self.subject.hir_id)
                    && matches!(
                        self.ctx.tcx.typeck(self.subject.fn_did).expr_ty(arg).kind(),
                        ty::RawPtr(..)
                    )
                    && let ty::FnDef(did, _) =
                        *self.ctx.tcx.typeck(self.subject.fn_did).expr_ty(callee).kind()
                    // Foreign = not a local fn ITEM with a body: a callee declared
                    // in an `extern` block has a local `DefId` too.
                    && did.as_local().is_none_or(|did| {
                        !matches!(self.ctx.tcx.hir_node_by_def_id(did), hir::Node::Item(item)
                            if matches!(item.kind, hir::ItemKind::Fn { .. }))
                    })
                {
                    let view = if self.subject.mutable {
                        "as_mut_ptr"
                    } else {
                        "as_ptr"
                    };
                    // R450-7(b): the boundary's cell for an opaque formal renders
                    // ZERO SYNTAX over this family's own view, so the receipt
                    // arrives with the site rather than gating it — the family
                    // no longer holds on `opens_argument` for this shape.
                    // The T1 receipt for this view is the site's own bridge row;
                    // a callee outside this crate carries no site, so it holds.
                    let Some(callee_did) = did.as_local() else {
                        self.hold.get_or_insert(CursorHold::RawBoundaryUnbuilt);
                        continue;
                    };
                    match self.index(operand) {
                        Ok(d) => {
                            let text = if local(operand) == Some(self.subject.hir_id) {
                                format!("{}.{view}()", self.view())
                            } else {
                                format!("{}.offset_by({d}).{view}()", self.view())
                            };
                            self.push(operand, text, "raw-op-cursor-t1");
                            self.bridges.push(super::CursorBridge {
                                call_hir: e.hir_id,
                                callee: callee_did,
                                argument_span: operand.span,
                                argument_index: index,
                            });
                        }
                        Err(hold) => {
                            self.hold.get_or_insert(hold);
                        }
                    }
                    continue;
                }
                // An offset chain rooted at this cursor handed to a raw formal
                // (`strcmp(s.offset(k), ..)`): the chain is the derived cursor
                // value at the argument, and the boundary's own Arm-A site
                // renders its raw view over it (`s.offset_by(k).as_ptr()`) —
                // the ruled same-span composition, use then seam.
                if !self.optional
                    && local(arg) != Some(self.subject.hir_id)
                    && matches!(arg.kind, hir::ExprKind::MethodCall(..))
                    && source_binding(self.ctx.tcx, self.subject.fn_did, arg)
                        == Some(self.subject.hir_id)
                    && let ty::FnDef(did, _) =
                        *self.ctx.tcx.typeck(self.subject.fn_did).expr_ty(callee).kind()
                    && did.as_local().and_then(|did| {
                        self.entries.iter().find(|(s, _)| s.fn_did == did && matches!(s.kind, SubjectKind::Param { hir_index } if hir_index == index))
                    }).is_none_or(|(_, d)| raw_decision(d))
                {
                    match self.index(arg) {
                        Ok(d) if self.ctx.raw_boundary.is_none_or(|rb| {
                            rb.opens_argument(
                                (self.subject.fn_did, self.subject.hir_id),
                                arg.span,
                                index,
                            )
                        }) =>
                        {
                            self.push(arg, format!("{}.offset_by({d})", self.name), "cursor-advance");
                        }
                        Ok(_) => {
                            self.hold.get_or_insert(CursorHold::RawBoundaryUnbuilt);
                        }
                        Err(hold) => {
                            self.hold.get_or_insert(hold);
                        }
                    }
                    continue;
                }
                // **R513-5.** A cursor handed to an EXTERN callee's raw formal
                // whose symbol the PINNED libc contract table models: rgba's
                // `strstr(str, "rgb(")`, brotli's fragment compressors. The
                // table's rows are `NoRetain`, so the callee cannot keep the
                // pointer past the call and the bridge is unconditional under
                // ruling 130 — no tier-2 waiver, no `opens_argument` permit to
                // wait for. An extern the table does not model has UNKNOWN
                // retention and keeps the hold, which is the control.
                //
                // The argument is the cursor's raw view at its position
                // (`as_ptr`/`as_mut_ptr`), or at the derived index for a chain;
                // the comparison against a returned alias stays on `.addr()`,
                // where the ordering arm already renders it.
                if !self.optional
                    && source_binding(self.ctx.tcx, self.subject.fn_did, arg)
                        == Some(self.subject.hir_id)
                    && let ty::FnDef(did, _) = *self
                        .ctx
                        .tcx
                        .typeck(self.subject.fn_did)
                        .expr_ty(callee)
                        .kind()
                    && self.ctx.tcx.is_foreign_item(did)
                    && super::super::raw_boundary_contracts::contract_table_models_symbol(
                        self.ctx.tcx.item_name(did).as_str(),
                    )
                    && let Some(callee_did) = did.as_local()
                {
                    let view = if self.subject.mutable {
                        "as_mut_ptr"
                    } else {
                        "as_ptr"
                    };
                    match self.index(arg) {
                        Ok(d) => {
                            let text = if local(arg) == Some(self.subject.hir_id) {
                                format!("{}.{view}()", self.view())
                            } else {
                                format!("{}.offset_by({d}).{view}()", self.view())
                            };
                            self.push(arg, text, "raw-op-cursor-t1");
                            self.bridges.push(super::CursorBridge {
                                call_hir: e.hir_id,
                                callee: callee_did,
                                argument_span: arg.span,
                                argument_index: index,
                            });
                        }
                        Err(hold) => {
                            self.hold.get_or_insert(hold);
                        }
                    }
                    continue;
                }
                if local(arg) == Some(self.subject.hir_id) {
                    let ty::FnDef(did, _) = *self
                        .ctx
                        .tcx
                        .typeck(self.subject.fn_did)
                        .expr_ty(callee)
                        .kind()
                    else {
                        self.hold.get_or_insert(CursorHold::RawBoundaryUnbuilt);
                        return;
                    };
                    let target = did.as_local().and_then(|did| self.entries.iter().find(|(s, _)| s.fn_did == did && matches!(s.kind, SubjectKind::Param { hir_index } if hir_index == index)));
                    let raw = target.is_none_or(|(_, d)| raw_decision(d));
                    if raw
                        && !self.optional
                        && index == 0
                        && args.len() == 1
                        && let Some(callee) = emission::scalar_reader(self.ctx.tcx, callee)
                    {
                        self.push(arg, format!("{}.as_ptr()", self.name), "raw-op-cursor-t1");
                        self.bridges.push(super::CursorBridge {
                            call_hir: e.hir_id,
                            callee,
                            argument_span: arg.span,
                            argument_index: index,
                        });
                    } else if raw {
                        // Hypothetical decisions expose the candidate. The final
                        // table must have the existing R130 site permit; that
                        // producer alone owns the argument edit and receipt.
                        if self.ctx.raw_boundary.is_some_and(|rb| {
                            !rb.opens_argument(
                                (self.subject.fn_did, self.subject.hir_id),
                                arg.span,
                                index,
                            )
                        }) {
                            self.hold.get_or_insert(CursorHold::RawBoundaryUnbuilt);
                        }
                    } else if target
                        .and_then(|(_, d)| {
                            slice_mutability(d).or_else(|| cursor_parameter_mutability(d))
                        })
                        .is_some()
                    {
                        // An optional cursor handed to a non-optional slice
                        // position: the C callee dereferences it, so `None` is
                        // the C program's own null path (§28).
                        self.push(
                            arg,
                            format!(
                                "{}.{}()",
                                self.view(),
                                if self.subject.mutable {
                                    "as_slice_mut"
                                } else {
                                    "as_slice"
                                }
                            ),
                            "cursor-element",
                        );
                    } else {
                        self.hold.get_or_insert(CursorHold::RawBoundaryUnbuilt);
                    }
                } else {
                    self.visit_expr(arg);
                }
            }
            self.visit_expr(callee);
            return;
        }
        // A chain this cursor cedes to the destination's own construction.
        if self.ceded_to_a_construction(e) {
            self.ceded += 1;
            return;
        }
        if local(e) == Some(self.subject.hir_id) {
            // The bare subject as the right-hand side of an assignment into a
            // shared peer cursor (`data = start`) is the peer's edit or no edit.
            let assigned_to_peer = if self.subject.mutable {
                None
            } else {
                self.assigned_to_shared_peer(e)
            };
            match assigned_to_peer.or_else(|| self.let_bound_peer(e)) {
                Some(peer) => self.peer_cursors.push(peer),
                None => match self.ephemeral_copy(e) {
                    Some((destination, access)) => {
                        let view = format!("{}.as_ptr()", self.view());
                        self.push(e, view, "raw-op-cursor-local");
                        self.local_bridges.push(super::CursorLocalBridge {
                            destination,
                            initializer: e.hir_id,
                            access,
                        });
                    }
                    None => {
                        self.hold.get_or_insert(CursorHold::UseUnbuilt);
                    }
                },
            }
        }
        if self.exclusive_base && self.base == local(e) && self.base.is_some() {
            self.hold.get_or_insert(CursorHold::ScheduleMissing);
        }
        intravisit::walk_expr(self, e);
    }
}
/// The subject is an operand of a pointer ordering / difference observation:
/// the cursor form carries those as address views, so a forward-only walk
/// that is ordered against another pointer is this family's too (relay 008).
pub(crate) fn ordering_participant(ctx: &Ctx<'_, '_>, s: &Subject) -> bool {
    ctx.facts
        .address_observations
        .iter()
        .filter(|observation| scalar_address_operation(observation.op))
        .flat_map(|observation| &observation.operands)
        .any(|operand| operand.node == (s.fn_did, s.hir_id))
}
/// Ordering participation selects a subject only where the other families
/// DEGRADE it (`ptr-comparison` or a cursor reason): a subject they deliver —
/// a thin reference compared, a slice differenced — keeps its delivered form.
fn ordering_degraded(decision: &Decision) -> bool {
    match decision {
        Decision::Degraded(record) => {
            matches!(record.reason, super::super::DegradeReason::PtrComparison)
                || super::is_cursor_reason(&record.reason)
        }
        Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::NestedSlice { .. }
        | Decision::Opt { .. }
        | Decision::Box(_)
        | Decision::Cursor { .. } => false,
    }
}
/// The option family degraded this null-initialised subject at a use.
fn optional_degraded(decision: &Decision) -> bool {
    match decision {
        Decision::Degraded(record) => {
            matches!(
                record.reason,
                super::super::DegradeReason::OptUseUnsupported
            )
        }
        Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::NestedSlice { .. }
        | Decision::Opt { .. }
        | Decision::Box(_)
        | Decision::Cursor { .. } => false,
    }
}
fn selected(ctx: &Ctx<'_, '_>, s: &Subject, decision: &Decision) -> bool {
    ctx.sign.may_be_negative(s.fn_did, s.local)
        || (ordering_participant(ctx, s) && ordering_degraded(decision))
}
/// **R485-4(c) (wave-6o, relay 052) — the ROOT case of the shape below.**
///
/// A subject the option family degrades `opt-use-unsupported` whose every
/// assignment is an offset chain rooted at ITSELF: a nullable pointer that
/// walks itself (`p = p.offset(1)`; binn `is_integer`, libtree
/// `parse_ld_library_path::search`). [`derived_from_cursor_root`] is its
/// sibling and explicitly declines this case ("a self-advance; not a root"),
/// because there the root must be ANOTHER cursor; and [`selected`] declines it
/// too, because a forward-only walker has no negative offset. The form these
/// subjects want already exists — `CursorPlan.optional` renders
/// `Option<SliceCursor<'_, T>>` with `is_none()`, `as_ref().expect(..)[i]` and
/// `as_mut().expect(..).seek(..)` — so only the admission was missing.
///
/// Deliberately NOT gated on `null_init`: these are nullable by an `is_null`
/// test on a parameter as often as by a null initialiser, and the option
/// family has already settled the nullability by degrading them. The offset
/// itself is still required by `plan`'s own `Offsets` visitor, and a subject
/// with any assignment that is not a self-advance is refused here.
fn self_advancing_root(ctx: &Ctx<'_, '_>, s: &Subject, decision: &Decision) -> bool {
    if s.ptr_depth != 1 || !optional_degraded(decision) {
        return false;
    }
    let (advances, other) = self_assignments(ctx, s);
    advances > 0 && other == 0
}

/// `(assignments rooted at the subject, assignments from anything else)` over
/// the subject's own body. A declaration initialiser is not an assignment.
fn self_assignments(ctx: &Ctx<'_, '_>, s: &Subject) -> (usize, usize) {
    struct Assigns<'a, 'tcx> {
        ctx: &'a Ctx<'a, 'tcx>,
        owner: rustc_hir::def_id::LocalDefId,
        subject: hir::HirId,
        advances: usize,
        other: usize,
    }
    impl<'v> Visitor<'v> for Assigns<'_, '_> {
        fn visit_expr(&mut self, e: &'v hir::Expr<'v>) {
            if let hir::ExprKind::Assign(lhs, rhs, _) = e.kind
                && local(lhs) == Some(self.subject)
            {
                let rhs = peel_reborrow_idiom(self.ctx.tcx, self.owner, rhs);
                if source_binding(self.ctx.tcx, self.owner, rhs) == Some(self.subject) {
                    self.advances += 1;
                } else {
                    self.other += 1;
                }
            }
            intravisit::walk_expr(self, e);
        }
    }
    let mut assigns = Assigns {
        ctx,
        owner: s.fn_did,
        subject: s.hir_id,
        advances: 0,
        other: 0,
    };
    assigns.visit_body(ctx.tcx.hir_body_owned_by(s.fn_did));
    (assigns.advances, assigns.other)
}
/// **R497-3(c) — the RE-SEEDED walker.** `self_advancing_root` wants every
/// assignment rooted at the subject; five corpus rows advance themselves and
/// are additionally **re-seeded once** from another value (`p = envbase`,
/// `p = c`, `search = strchr(search, ';')`, `info = ti_find_indicator(..)`,
/// `backptr = &*in_0.offset(..)`). Exactly one such assignment is admitted:
/// the re-seed constructs a fresh cursor at that point (slicecursor 052 §3),
/// which resets the position, so two of them would make the walker's own
/// positions incomparable with no single base to name.
fn re_seeded_walker(ctx: &Ctx<'_, '_>, s: &Subject, decision: &Decision) -> bool {
    if s.ptr_depth != 1 || !optional_degraded(decision) {
        return false;
    }
    // **Condition (ii), slicecursor 052 §3.** The construction at the re-seed
    // fabricates its window FORWARD from that pointer, so the cursor cannot
    // represent a position below it: a walker that may move backwards after
    // the re-seed would panic where the input program was correct. The sign
    // slot is the fact, the same one `selected` reads.
    if ctx.sign.may_be_negative(s.fn_did, s.local) {
        return false;
    }
    let (advances, other) = self_assignments(ctx, s);
    advances > 0 && other == 1
}

/// A null-initialised local the option family degrades (`opt-use-unsupported`)
/// whose every assignment is an offset chain (or the reborrow idiom) rooted at
/// a cursor root of this family: the optional cursor form covers it.
fn derived_from_cursor_root(
    ctx: &Ctx<'_, '_>,
    s: &Subject,
    decision: &Decision,
    entries: &[(Subject, Decision)],
) -> bool {
    if !s.null_init || s.ptr_depth != 1 || !optional_degraded(decision) {
        return false;
    }
    struct Assigns<'a, 'tcx> {
        ctx: &'a Ctx<'a, 'tcx>,
        owner: rustc_hir::def_id::LocalDefId,
        subject: hir::HirId,
        entries: &'a [(Subject, Decision)],
        rooted: usize,
        other: usize,
    }
    impl<'v> Visitor<'v> for Assigns<'_, '_> {
        fn visit_expr(&mut self, e: &'v hir::Expr<'v>) {
            if let hir::ExprKind::Assign(lhs, rhs, _) = e.kind
                && local(lhs) == Some(self.subject)
            {
                let rhs = peel_reborrow_idiom(self.ctx.tcx, self.owner, rhs);
                let root = source_binding(self.ctx.tcx, self.owner, rhs);
                if root == Some(self.subject) {
                    // a self-advance; not a root
                } else if root.is_some_and(|root| {
                    self.entries.iter().any(|(other, decision)| {
                        other.fn_did == self.owner
                            && other.hir_id == root
                            && (selected(self.ctx, other, decision)
                                || derives_cursor(self.ctx, other, decision, self.entries))
                    })
                }) {
                    self.rooted += 1;
                } else {
                    self.other += 1;
                }
            }
            intravisit::walk_expr(self, e);
        }
    }
    let mut assigns = Assigns {
        ctx,
        owner: s.fn_did,
        subject: s.hir_id,
        entries,
        rooted: 0,
        other: 0,
    };
    assigns.visit_body(ctx.tcx.hir_body_owned_by(s.fn_did));
    assigns.rooted > 0 && assigns.other == 0
}
/// The subject is the root of another subject's cursor candidate — its
/// initializer or an assignment into it is an offset chain (or the c2rust
/// reborrow idiom) rooted here — and the other families degrade it: the
/// derived cursors need their parent in this family.
fn derives_cursor(
    ctx: &Ctx<'_, '_>,
    s: &Subject,
    decision: &Decision,
    entries: &[(Subject, Decision)],
) -> bool {
    if !ordering_degraded(decision) || s.ptr_depth != 1 {
        return false;
    }
    struct Roots<'a, 'tcx> {
        ctx: &'a Ctx<'a, 'tcx>,
        owner: rustc_hir::def_id::LocalDefId,
        subject: hir::HirId,
        entries: &'a [(Subject, Decision)],
        found: bool,
    }
    impl<'v> Visitor<'v> for Roots<'_, '_> {
        fn visit_expr(&mut self, e: &'v hir::Expr<'v>) {
            if let hir::ExprKind::Assign(lhs, rhs, _) = e.kind
                && let Some(target) = local(lhs)
                && source_binding(
                    self.ctx.tcx,
                    self.owner,
                    peel_reborrow_idiom(self.ctx.tcx, self.owner, rhs),
                ) == Some(self.subject)
                && self.entries.iter().any(|(other, decision)| {
                    other.fn_did == self.owner
                        && other.hir_id == target
                        && other.hir_id != self.subject
                        && selected(self.ctx, other, decision)
                })
            {
                self.found = true;
            }
            intravisit::walk_expr(self, e);
        }
    }
    let inits = entries.iter().any(|(other, other_decision)| {
        other.fn_did == s.fn_did
            && other.hir_id != s.hir_id
            && selected(ctx, other, other_decision)
            && ctx
                .constructions
                .init_hirs
                .get(&(other.fn_did, other.hir_id))
                .is_some_and(|init| {
                    source_binding(
                        ctx.tcx,
                        s.fn_did,
                        peel_reborrow_idiom(
                            ctx.tcx,
                            s.fn_did,
                            ctx.tcx.hir_node(*init).expect_expr(),
                        ),
                    ) == Some(s.hir_id)
                })
    });
    if inits {
        return true;
    }
    let mut roots = Roots {
        ctx,
        owner: s.fn_did,
        subject: s.hir_id,
        entries,
        found: false,
    };
    roots.visit_body(ctx.tcx.hir_body_owned_by(s.fn_did));
    roots.found
}
/// The planner as every caller but `promote` uses it: no table is about to
/// flip, so the family reads `entries` as it stands.
pub(super) fn plan(
    ctx: &Ctx<'_, '_>,
    subject: &Subject,
    decision: &Decision,
    entries: &[(Subject, Decision)],
) -> Option<Result<CursorPlan, CursorHold>> {
    plan_with(ctx, subject, decision, entries, None)
}

/// **R512-4 / nested 018 STOP 1, answered in report 061 §4.** The same planner,
/// told that one table is about to deliver its inner level. There is ONE base
/// resolution in this family and this is it: `prospective` is a query parameter
/// threaded to `table_element_base`, not a second entry point that would
/// duplicate the resolution and drift from it.
pub(crate) fn plan_with<'a>(
    ctx: &Ctx<'_, '_>,
    subject: &Subject,
    decision: &Decision,
    entries: &[(Subject, Decision)],
    prospective: Option<&'a super::ProspectiveTable>,
) -> Option<Result<CursorPlan, CursorHold>> {
    // **R515-5(a), nested 019.** A row this family has ALREADY taken, re-planned
    // against a base that is about to flip. The selection question is answered —
    // this family asked it in this pass and said yes — and re-asking it gives
    // the wrong answer rather than a conservative one, because
    // `ordering_degraded` is defined to be false for a `Cursor`, so a row
    // selected by ordering fails a gate it passed minutes earlier. The match
    // below refuses an existing `Cursor` because an ordinary re-plan would be a
    // SECOND commitment of the same row; a prospective flip is not that, it is
    // the same commitment against a different base.
    //
    // So this is the one door: `build` stays `pub(super)` and nested calls
    // `plan_with`. It also makes nested 019 (b) safe by construction — entering
    // construction directly is sound precisely BECAUSE the subject is already a
    // committed cursor, and this condition is what enforces that.
    // S3.0: a `Decision` is consumed through an EXHAUSTIVE match, so a new
    // disposition is a compile error here rather than a silent `false`.
    let already_taken = match decision {
        Decision::Cursor { .. } => true,
        Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::NestedSlice { .. }
        | Decision::Opt { .. }
        | Decision::Box(_)
        | Decision::Degraded(_) => false,
    };
    if prospective.is_some() && already_taken {
        return Some(build(ctx, subject, entries, prospective));
    }
    if (!selected(ctx, subject, decision)
        && !derives_cursor(ctx, subject, decision, entries)
        && !derived_from_cursor_root(ctx, subject, decision, entries)
        && !self_advancing_root(ctx, subject, decision)
        && !re_seeded_walker(ctx, subject, decision))
        || subject.ptr_depth != 1
    {
        return None;
    }
    match decision {
        Decision::Box(_) | Decision::NestedSlice { .. } | Decision::Cursor { .. } => return None,
        Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::Opt { .. }
        | Decision::Degraded(_) => {}
    }
    // Keep ordinary non-arithmetic references out of this family even when
    // their sign slot is absent. An actual pointer offset must be present.
    struct Offsets {
        binding: hir::HirId,
        found: bool,
    }
    impl<'v> Visitor<'v> for Offsets {
        fn visit_expr(&mut self, e: &'v hir::Expr<'v>) {
            if let hir::ExprKind::MethodCall(segment, receiver, _, _) = e.kind
                && ["offset", "add", "sub"].contains(&segment.ident.name.as_str())
                && contains(receiver, self.binding)
            {
                self.found = true;
            }
            intravisit::walk_expr(self, e);
        }
    }
    let mut offsets = Offsets {
        binding: subject.hir_id,
        found: false,
    };
    offsets.visit_body(ctx.tcx.hir_body_owned_by(subject.fn_did));
    // An end marker (`p < end`) may carry no arithmetic of its own; ordering
    // participation admits it beside the walked cursor.
    if !offsets.found
        && !ordering_participant(ctx, subject)
        && !derives_cursor(ctx, subject, decision, entries)
        && !derived_from_cursor_root(ctx, subject, decision, entries)
    {
        return None;
    }
    Some(build(ctx, subject, entries, prospective))
}
pub(super) fn build<'a>(
    ctx: &Ctx<'_, '_>,
    subject: &Subject,
    entries: &[(Subject, Decision)],
    prospective: Option<&'a super::ProspectiveTable>,
) -> Result<CursorPlan, CursorHold> {
    let parameter = matches!(subject.kind, SubjectKind::Param { .. });
    // **The entry window** (R472-6, route 1). A cursor rooted at a raw parameter
    // has its window fabricated forward from the pointer, so it cannot represent
    // a position below the one it was handed: emitting it would panic where the
    // input program was correct. The fact is the derivation's own — the same
    // `RetainedBase` the census column reports — so the guard and the column can
    // never disagree about which rows they mean.
    if parameter
        && super::inspect_subject(ctx.tcx, ctx.slots, ctx.model, subject).findings[0].outcome
            == super::admission::Outcome::Missing(super::admission::Need::EntryWindow)
    {
        return Err(CursorHold::ScheduleMissing);
    }
    let name = emission::binding_name(ctx.tcx, subject)?;
    let init = ctx
        .constructions
        .init_hirs
        .get(&(subject.fn_did, subject.hir_id))
        .copied();
    let null_init = subject.null_init
        || init.is_some_and(|id| is_null_value(ctx, subject, ctx.tcx.hir_node(id).expect_expr()));
    let optional = null_init
        || ctx
            .facts
            .raw_only_uses
            .get(&(subject.fn_did, subject.hir_id))
            .is_some_and(|uses| uses.iter().any(|(op, _)| op == "is_null"));
    let b = if null_init {
        if subject.mutable {
            return Err(CursorHold::OptionalUnbuilt);
        }
        Base {
            parent_cursor: None,
            expression: "None".into(),
            binding: None,
            local: subject.local,
            delivered: None,
            fallback: false,
            composed: vec![],
        }
    } else if parameter {
        if !model_ref(ctx, subject) {
            return Err(CursorHold::RefMissing);
        }
        Base {
            parent_cursor: None,
            expression: String::new(),
            binding: None,
            local: subject.local,
            delivered: None,
            fallback: false,
            composed: vec![],
        }
    } else {
        base(
            ctx,
            subject,
            ctx.tcx
                .hir_node(init.ok_or(CursorHold::BaseMissing)?)
                .expect_expr(),
            entries,
            prospective,
        )?
    };
    // An untyped local (`let mut q = p.offset(k)`) gets its cursor type as an
    // explicit declaration (the custody instrument rejects inferred types); the
    // pointee is the compiler's, rendered.
    let explicit_declaration = if !parameter && subject.ty_span.is_none() {
        let ty::RawPtr(pointee, _) = *ctx
            .tcx
            .typeck(subject.fn_did)
            .node_type(subject.hir_id)
            .kind()
        else {
            return Err(CursorHold::DeclarationUnbuilt);
        };
        Some(type_text(
            subject.mutable,
            optional,
            &pointee.to_string(),
            None,
        ))
    } else {
        None
    };
    let mut v = Uses {
        ctx,
        subject,
        entries,
        prospective,
        name,
        init,
        base: b.binding,
        optional,
        exclusive_base: subject.mutable || b.fallback,
        tail: {
            let body = ctx.tcx.hir_body_owned_by(subject.fn_did);
            match body.value.kind {
                hir::ExprKind::Block(block, _) => block.expr.map(|e| e.hir_id),
                _ => Some(body.value.hir_id),
            }
        },
        bridges: vec![],
        edits: vec![],
        hirs: vec![],
        hold: None,
        peer_bases: vec![],
        peer_cursors: vec![],
        local_bridges: vec![],
        ceded: 0,
        re_seeded: {
            let (advances, other) = self_assignments(ctx, subject);
            advances > 0 && other == 1
        },
        re_seed_fabricated: false,
        re_seed_composed: vec![],
    };
    v.visit_body(ctx.tcx.hir_body_owned_by(subject.fn_did));
    if let Some(hold) = v.hold {
        return Err(hold);
    }
    // **R487-3(c).** A subject whose only handled use was a ceded chain is not a
    // cursor on its own account: the chain is what would make this family own
    // the root, and the family that delivers the root without it keeps it.
    if v.ceded > 0 && v.edits.is_empty() {
        return Err(CursorHold::UseUnbuilt);
    }
    if let Some(init) = init {
        v.push(
            ctx.tcx.hir_node(init).expect_expr(),
            if optional && !null_init {
                format!("Some({})", b.expression)
            } else {
                b.expression
            },
            "cursor-constructor",
        );
    }
    Ok(CursorPlan {
        parent_cursor: b.parent_cursor,
        wrapper: true,
        parameter,
        optional,
        fallback: b.fallback || v.re_seed_fabricated,
        uses: v.edits,
        use_hirs: v.hirs,
        base: b.local,
        component: vec![subject.local],
        extent: 0,
        delivered_base: b.delivered,
        bridges: v.bridges,
        local_bridges: v.local_bridges,
        composed_edit_spans: {
            let mut composed = b.composed;
            composed.extend(v.re_seed_composed);
            composed
        },
        explicit_declaration,
        peer_bases: v.peer_bases,
        peer_cursors: v.peer_cursors,
    })
}

/// The subject a re-point constructor stands on: a parent cursor, or another
/// family's delivered local — never an original safe binding, which no family
/// can withdraw.
fn peer_base(b: &Base) -> Option<hir::HirId> {
    b.parent_cursor.or_else(|| {
        b.delivered
            .as_ref()
            .filter(|d| !matches!(d.provider, DeliveredBaseProvider::OriginalSlice))
            .and(b.binding)
    })
}

/// Recover the compiler-resolved delivered base through a chain of offsets.
pub(crate) fn source_binding(
    tcx: ty::TyCtxt<'_>,
    owner: rustc_hir::def_id::LocalDefId,
    mut e: &hir::Expr<'_>,
) -> Option<hir::HirId> {
    while let hir::ExprKind::MethodCall(_, receiver, _, _) = e.kind {
        if !emission::method(
            tcx,
            owner,
            e,
            &["offset", "add", "sub", "as_ptr", "as_mut_ptr"],
        ) {
            return None;
        }
        e = receiver;
    }
    local(e)
}

pub(crate) fn parameter_form(decision: &Decision) -> super::super::seam::Form {
    use super::super::seam::{Form, form_of};
    match decision {
        Decision::Cursor { mutable, plan } if plan.wrapper && plan.parameter => {
            if plan.optional {
                Form::Opt {
                    mutable: *mutable,
                    slice: true,
                }
            } else {
                Form::Slice { mutable: *mutable }
            }
        }
        Decision::Cursor { .. }
        | Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::Opt { .. }
        | Decision::Box(_)
        | Decision::NestedSlice { .. }
        | Decision::Degraded(_) => form_of(decision),
    }
}

fn slice_mutability(decision: &Decision) -> Option<bool> {
    match decision {
        Decision::Slice { mutable, .. } => Some(*mutable),
        Decision::Cursor { .. }
        | Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Opt { .. }
        | Decision::Box(_)
        | Decision::NestedSlice { .. }
        | Decision::Degraded(_) => None,
    }
}
/// A local callee's parameter that is itself a wrapper cursor is a slice at
/// its safe body (`parameter_form`); the caller hands it the tail view.
fn cursor_parameter_mutability(decision: &Decision) -> Option<bool> {
    match decision {
        Decision::Cursor { mutable, plan } if plan.wrapper && plan.parameter && !plan.optional => {
            Some(*mutable)
        }
        Decision::Cursor { .. }
        | Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::Opt { .. }
        | Decision::Box(_)
        | Decision::NestedSlice { .. }
        | Decision::Degraded(_) => None,
    }
}
fn raw_decision(decision: &Decision) -> bool {
    match decision {
        Decision::Degraded(_) => true,
        Decision::Cursor { .. }
        | Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Slice { .. }
        | Decision::Opt { .. }
        | Decision::Box(_)
        | Decision::NestedSlice { .. } => false,
    }
}

fn is_null_value(ctx: &Ctx<'_, '_>, s: &Subject, e: &hir::Expr<'_>) -> bool {
    if crate::bo_rewriter::decision::emitability::is_zero_literal(e) {
        return true;
    }
    let hir::ExprKind::Call(callee, []) = e.kind else {
        return false;
    };
    let ty::FnDef(did, _) = *ctx.tcx.typeck(s.fn_did).expr_ty(callee).kind() else {
        return false;
    };
    !did.is_local()
        && ctx.tcx.crate_name(did.krate).as_str() == "core"
        && ["null", "null_mut"].contains(&ctx.tcx.item_name(did).as_str())
}

fn table_origin(
    ctx: &Ctx<'_, '_>,
    s: &Subject,
    mut e: &hir::Expr<'_>,
    entries: &[(Subject, Decision)],
    seen: &mut rustc_hash::FxHashSet<hir::HirId>,
) -> Option<bool> {
    while let hir::ExprKind::Cast(inner, _) = e.kind {
        e = inner;
    }
    if let hir::ExprKind::Unary(hir::UnOp::Deref, pointer) = e.kind {
        let root = source_binding(ctx.tcx, s.fn_did, pointer)?;
        let source = entries
            .iter()
            .find(|(source, _)| source.fn_did == s.fn_did && source.hir_id == root)?
            .0
            .clone();
        use crate::analyses::borrow_ownership::{SlotKind, solver::SlotRef};
        let raw = ctx
            .slots
            .fn_local_slots
            .get(&source.fn_did)
            .and_then(|slots| slots.slot_for_local_depth(source.local, 0))
            .and_then(|slot| ctx.model.get(&SlotRef::Local(source.fn_did, slot)))
            == Some(&SlotKind::Raw);
        return Some(raw);
    }
    if let Some(root) = local(e)
        && seen.insert(root)
        && let Some(init) = ctx.constructions.init_hirs.get(&(s.fn_did, root))
    {
        return table_origin(ctx, s, ctx.tcx.hir_node(*init).expect_expr(), entries, seen);
    }
    None
}

fn candidate_shape(ctx: &Ctx<'_, '_>, s: &Subject, decision: &Decision) -> bool {
    candidate_shape_in(ctx, s, decision, &[])
}
/// `entries` lets a root selected only through its derived cursors count.
fn candidate_shape_in(
    ctx: &Ctx<'_, '_>,
    s: &Subject,
    decision: &Decision,
    entries: &[(Subject, Decision)],
) -> bool {
    let uses = ctx.facts.raw_only_uses.get(&(s.fn_did, s.hir_id));
    // Another family's delivery (a thin optional reference, a slice) is not a
    // cursor candidate whatever its sign: a child cannot derive its window
    // from it, and a peer cannot lean on it (binn `plimit` over `p`).
    let open = match decision {
        Decision::Degraded(_) | Decision::Cursor { .. } => true,
        Decision::Slice { .. }
        | Decision::NestedSlice { .. }
        | Decision::Opt { .. }
        | Decision::Ref { .. }
        | Decision::InferredRef { .. }
        | Decision::Box(_) => false,
    };
    open && s.ptr_depth == 1
        && (selected(ctx, s, decision)
            || derives_cursor(ctx, s, decision, entries)
            || (s.null_init && optional_degraded(decision)))
        && (uses.is_some_and(|uses| {
            uses.iter()
                .any(|(op, _)| ["offset", "add", "sub"].contains(&op.as_str()))
        }) || ordering_participant(ctx, s))
        && uses.is_none_or(|uses| uses.iter().all(|(op, _)| op != "is_null"))
}

pub(crate) fn parent_available(
    table: &crate::bo_rewriter::decision::DecisionTable,
    s: &Subject,
    cursor: &CursorPlan,
) -> bool {
    cursor.parent_cursor.is_none_or(|parent| {
        parent.owner.def_id == s.fn_did
            && parent != s.hir_id
            && table.entries.iter().any(|(source, d)| {
                if source.fn_did != s.fn_did || source.hir_id != parent {
                    return false;
                }
                match d {
                    Decision::Cursor { plan, .. } => plan.wrapper,
                    Decision::Ref { .. }
                    | Decision::InferredRef { .. }
                    | Decision::Slice { .. }
                    | Decision::Opt { .. }
                    | Decision::Box(_)
                    | Decision::NestedSlice { .. }
                    | Decision::Degraded(_) => false,
                }
            })
    })
}

fn scalar_address_operation(op: &str) -> bool {
    matches!(
        op,
        "lt" | "le" | "gt" | "ge" | "eq" | "ne" | "ptr-eq" | "difference"
    )
}
