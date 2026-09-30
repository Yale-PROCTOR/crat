//! **wave-6l (R631-4, relay 061): reads past a masked index by a runtime length.**
//!
//! brotli's ring-buffer readers index their buffer at `cur_ix & ring_buffer_mask`
//! and then read ON from there by a length known only at run time:
//! `StoreAndFindMatchesH10` reads `data[cur_ix_masked + cur_len]`, and
//! `FindAllMatchesH10` hands `&data[cur_ix_masked]` to
//! `FindMatchLengthWithLimit(.., max_length)`, which walks `max_length` bytes.
//! C keeps those reads inside the ring's tail and slack; the mask bounds where
//! each read STARTS, not the read. No companion at these signatures carries the
//! buffer's true length (it lives in the encoder's `RingBuffer`), so a slice
//! built over `mask` or `mask + 1` panics where C reads on (wave-6l 058's audit),
//! and the §77 fallback panics sooner. The parameter stays raw under a typed
//! hold: a panicking row is not yield (R544-6).
//!
//! **The rule** — a raw-pointer parameter `p` is held when, in its function:
//!
//! - (A1) `p` is indexed at a masked index plus a non-constant
//!   (`p.offset(m + len)`, `p.offset(m.wrapping_add(len))`); or
//! - (A2) a pointer derived at a masked index (`&*p.offset(m)`, `p.offset(m)`)
//!   is handed to a local callee parameter that reads at a non-constant index,
//!   re-seats itself, or hands itself on to one that does; or
//! - (B) `p` is handed, bare, to a local callee parameter that is held.
//!
//! A masked index is a `&` with a non-literal operand, directly or through a
//! local defined once from one. A read at a masked index plus a CONSTANT is not
//! this hold's: that is R477-6's arm, whose residue is receipted fabricated.
//! Closures the functions run are walked (their captures read the pointer too).
//!
//! **(iv)** — [`always_zero`]: the seam never licenses a companion that is the
//! literal `0` or a local only ever assigned `0`. batch 50's Zopfli root built
//! `from_raw_parts(dist_cache, (gap) as usize)` with `gap = 0`, an empty slice
//! its callees index at once.
use rustc_hir::{
    Expr, ExprKind, HirId, Node, PatKind,
    def::Res,
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::{
    hir::nested_filter::OnlyBodies,
    ty::{TyCtxt, TyKind},
};

/// `Some(chain)` — the functions from `function` to the reader, joined by ` → `
/// — when `function`'s `parameter` is held.
pub(crate) fn held(tcx: TyCtxt<'_>, function: LocalDefId, parameter: usize) -> Option<String> {
    held_at(tcx, function, parameter, &mut Vec::new())
}

/// **Relay 071 (R697-7 (b)): the hold narrowed.** Does some root of
/// `function`'s `parameter` take a FABRICATED length? The walk goes up through
/// the callers: a parameter handed on bare (or under a cast) asks its own
/// callers; a root is real when it is an array start (R625's `[T; N]`, directly
/// or through a local defined once from one) or a licensed field read (the
/// field-carried allocation length). Anything else, and a function whose
/// callers are not all known, is a fabricated root: the reader is held.
pub(crate) fn fabricated_root(
    tcx: TyCtxt<'_>,
    facts: &super::emitability::EmitabilityFacts,
    licences: &super::field_alloc::Licences,
    world: World<'_>,
    function: LocalDefId,
    parameter: usize,
) -> bool {
    fabricated_root_at(
        tcx,
        facts,
        licences,
        world,
        function,
        parameter,
        &mut Vec::new(),
    )
}

/// Whose calls reach a function. `Conservative`: only a private function's
/// (`thin_counted::closed_calls`). `Closed`: the program's own calls, as the
/// emission treats an exported function whose signature it changes in place
/// (the exposure policy's `internal-by-configuration`); a function in a
/// fn-pointer web, a configured entry, or one whose address is taken has
/// callers the program does not see (`thin_counted::chain_gate`'s rule).
#[derive(Clone, Copy)]
pub(crate) enum World<'a> {
    Conservative,
    Closed(Option<&'a super::exposure::ExposurePolicy>),
}

fn callers<'a>(
    tcx: TyCtxt<'_>,
    facts: &'a super::emitability::EmitabilityFacts,
    world: World<'_>,
    function: LocalDefId,
) -> Option<&'a [super::emitability::CallSite]> {
    match world {
        World::Conservative => super::thin_counted::closed_calls(tcx, function, facts).ok(),
        World::Closed(policy) => {
            let refs = facts.referenced.get(&function)?;
            if !super::emitability::RefKind::is_adaptable(refs) {
                return None;
            }
            if policy.is_some_and(|policy| {
                policy.functions().iter().any(|row| {
                    row.did == function
                        && (row.fnptr_web
                            || row
                                .seed
                                .is_some_and(|seed| seed.configured_name || seed.address_taken))
                })
            }) {
                return None;
            }
            let calls = facts.call_args.get(&function).filter(|c| !c.is_empty())?;
            (calls.len() == refs.len()).then_some(calls.as_slice())
        }
    }
}

fn fabricated_root_at(
    tcx: TyCtxt<'_>,
    facts: &super::emitability::EmitabilityFacts,
    licences: &super::field_alloc::Licences,
    world: World<'_>,
    function: LocalDefId,
    parameter: usize,
    visited: &mut Vec<(LocalDefId, usize)>,
) -> bool {
    if visited.contains(&(function, parameter)) {
        return false;
    }
    visited.push((function, parameter));
    let Some(calls) = callers(tcx, facts, world, function) else {
        return true;
    };
    for call in calls {
        let Some(arg) = call.args.iter().find(|a| a.index == parameter) else {
            return true;
        };
        if arg.array_extent.is_some() || licences.length_at(tcx, call.caller, arg.span).is_some() {
            continue;
        }
        let local = match arg.shape {
            super::emitability::ArgShape::BareLocal(id)
            | super::emitability::ArgShape::CastOfLocal { binding: id, .. } => id,
            _ => return true,
        };
        let body = tcx.hir_body_owned_by(call.caller);
        if let Some(index) = body.params.iter().position(|p| p.pat.hir_id == local) {
            if fabricated_root_at(tcx, facts, licences, world, call.caller, index, visited) {
                return true;
            }
            continue;
        }
        // A local defined once, from an array start.
        let definitions = Definitions::of(tcx, body);
        let from_array = !definitions.unknown_writes.contains(&local)
            && !definitions.assignments.contains_key(&local)
            && definitions.initializer.get(&local).is_some_and(|init| {
                super::emitability::array_extent(tcx, call.caller, init).is_some()
            });
        if !from_array {
            return true;
        }
    }
    false
}

fn held_at(
    tcx: TyCtxt<'_>,
    function: LocalDefId,
    parameter: usize,
    visited: &mut Vec<(LocalDefId, usize)>,
) -> Option<String> {
    if visited.contains(&(function, parameter)) {
        return None;
    }
    visited.push((function, parameter));
    let binding = raw_pointer_parameter(tcx, function, parameter)?;
    let body = tcx.hir_body_owned_by(function);
    let definitions = Definitions::of(tcx, body);
    let mut uses = Uses {
        tcx,
        function,
        binding,
        definitions: &definitions,
        direct: false,
        escapes: Vec::new(),
        forwards: Vec::new(),
    };
    uses.visit_body(body);
    let path = || tcx.def_path_str(function.to_def_id());
    if uses.direct
        || uses
            .escapes
            .iter()
            .any(|(callee, index)| runtime_reader(tcx, *callee, *index, &mut Vec::new()))
    {
        return Some(path());
    }
    uses.forwards
        .iter()
        .find_map(|(callee, index)| held_at(tcx, *callee, *index, visited))
        .map(|inner| format!("{} → {inner}", path()))
}

fn raw_pointer_parameter(tcx: TyCtxt<'_>, function: LocalDefId, parameter: usize) -> Option<HirId> {
    let body = tcx.hir_body_owned_by(function);
    let param = body.params.get(parameter)?;
    matches!(
        tcx.typeck(function).pat_ty(param.pat).kind(),
        TyKind::RawPtr(..)
    )
    .then_some(param.pat.hir_id)
}

/// A local callee's parameter that reads from its pointer by a length only
/// known at run time: a non-constant index, a re-seat, or a bare forwarding
/// into one that does.
fn runtime_reader(
    tcx: TyCtxt<'_>,
    function: LocalDefId,
    parameter: usize,
    visited: &mut Vec<(LocalDefId, usize)>,
) -> bool {
    if visited.contains(&(function, parameter)) {
        return false;
    }
    visited.push((function, parameter));
    let Some(binding) = raw_pointer_parameter(tcx, function, parameter) else {
        return false;
    };
    struct Reader<'tcx> {
        tcx: TyCtxt<'tcx>,
        function: LocalDefId,
        binding: HirId,
        variable: bool,
        forwards: Vec<(LocalDefId, usize)>,
    }
    impl<'tcx> Visitor<'tcx> for Reader<'tcx> {
        type NestedFilter = OnlyBodies;

        fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
            self.tcx
        }

        fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
            if is_local(e, self.binding)
                && let Node::Expr(parent) = self.tcx.parent_hir_node(e.hir_id)
            {
                match parent.kind {
                    ExprKind::MethodCall(segment, receiver, [index], _)
                        if receiver.hir_id == e.hir_id
                            && ARITHMETIC.contains(&segment.ident.name.as_str())
                            && !constant(index) =>
                    {
                        self.variable = true
                    }
                    ExprKind::Index(base, index, _)
                        if base.hir_id == e.hir_id && !constant(index) =>
                    {
                        self.variable = true
                    }
                    ExprKind::Assign(lhs, _, _) | ExprKind::AssignOp(_, lhs, _)
                        if lhs.hir_id == e.hir_id =>
                    {
                        self.variable = true
                    }
                    ExprKind::Call(callee, args) => {
                        if let Some(local) = local_callee(self.tcx, self.function, callee)
                            && let Some(index) = args.iter().position(|arg| arg.hir_id == e.hir_id)
                        {
                            self.forwards.push((local, index));
                        }
                    }
                    _ => {}
                }
            }
            intravisit::walk_expr(self, e);
        }
    }
    let mut reader = Reader {
        tcx,
        function,
        binding,
        variable: false,
        forwards: Vec::new(),
    };
    reader.visit_body(tcx.hir_body_owned_by(function));
    reader.variable
        || reader
            .forwards
            .into_iter()
            .any(|(callee, index)| runtime_reader(tcx, callee, index, visited))
}

const ARITHMETIC: &[&str] = &["offset", "add", "wrapping_offset", "wrapping_add"];

fn is_local(e: &Expr<'_>, binding: HirId) -> bool {
    matches!(e.kind, ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) if path.res == Res::Local(binding))
}

fn peel<'a, 'tcx>(mut e: &'a Expr<'tcx>) -> &'a Expr<'tcx> {
    while let ExprKind::Cast(inner, _) | ExprKind::DropTemps(inner) = e.kind {
        e = inner;
    }
    e
}

fn constant(e: &Expr<'_>) -> bool {
    matches!(peel(e).kind, ExprKind::Lit(_))
}

fn zero_literal(e: &Expr<'_>) -> bool {
    matches!(peel(e).kind, ExprKind::Lit(lit) if matches!(lit.node, rustc_ast::LitKind::Int(n, _) if n.get() == 0))
}

/// `x OP rhs` keeps `x == 0` zero: `+ - | ^ << >>` by a literal `0`, or `* &`
/// by anything.
fn zero_preserving_op(op: rustc_ast::AssignOpKind, rhs: &Expr<'_>) -> bool {
    use rustc_ast::AssignOpKind::*;
    match op {
        MulAssign | BitAndAssign => true,
        AddAssign | SubAssign | BitOrAssign | BitXorAssign | ShlAssign | ShrAssign => {
            zero_literal(rhs)
        }
        DivAssign | RemAssign => false,
    }
}

/// `x = x.wrapping_add(0)` and its kin, or `x = x + 0`: the value `x` had.
fn preserves_zero(id: HirId, rhs: &Expr<'_>) -> bool {
    match peel(rhs).kind {
        ExprKind::MethodCall(segment, receiver, [argument], _) => {
            local_of(receiver) == Some(id)
                && match segment.ident.name.as_str() {
                    "wrapping_mul" => true,
                    "wrapping_add" | "wrapping_sub" | "wrapping_shl" | "wrapping_shr" => {
                        zero_literal(argument)
                    }
                    _ => false,
                }
        }
        ExprKind::Binary(op, left, right) => {
            use rustc_hir::BinOpKind::*;
            local_of(left) == Some(id)
                && match op.node {
                    Mul | BitAnd => true,
                    Add | Sub | BitOr | BitXor | Shl | Shr => zero_literal(right),
                    _ => false,
                }
        }
        _ => false,
    }
}

fn local_of(e: &Expr<'_>) -> Option<HirId> {
    match peel(e).kind {
        ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) => match path.res {
            Res::Local(id) => Some(id),
            _ => None,
        },
        _ => None,
    }
}

/// The argument expression at `span` in `caller`'s body, with that body.
fn argument_at<'tcx>(
    tcx: TyCtxt<'tcx>,
    caller: LocalDefId,
    span: rustc_span::Span,
) -> Option<(&'tcx rustc_hir::Body<'tcx>, &'tcx Expr<'tcx>)> {
    struct Find<'tcx> {
        tcx: TyCtxt<'tcx>,
        span: rustc_span::Span,
        found: Option<&'tcx Expr<'tcx>>,
    }
    impl<'tcx> Visitor<'tcx> for Find<'tcx> {
        type NestedFilter = OnlyBodies;

        fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
            self.tcx
        }

        fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
            if self.found.is_none() && e.span == self.span {
                self.found = Some(e);
                return;
            }
            intravisit::walk_expr(self, e);
        }
    }
    tcx.hir_node_by_def_id(caller).body_id()?;
    let body = tcx.hir_body_owned_by(caller);
    let mut find = Find {
        tcx,
        span,
        found: None,
    };
    find.visit_body(body);
    find.found.map(|argument| (body, argument))
}

/// **(iv)** — the call argument at `span` in `caller` is the literal `0`, or a
/// local whose `let` initializer is `0`, every assignment to which stores `0`,
/// and which is never borrowed. Such a companion names no extent.
pub(crate) fn always_zero(tcx: TyCtxt<'_>, caller: LocalDefId, span: rustc_span::Span) -> bool {
    let Some((body, argument)) = argument_at(tcx, caller, span) else {
        return false;
    };
    if zero_literal(argument) {
        return true;
    }
    let Some(id) = local_of(argument) else {
        return false;
    };
    let definitions = Definitions::of(tcx, body);
    definitions
        .initializer
        .get(&id)
        .is_some_and(|init| zero_literal(init))
        && !definitions.nonzero.contains(&id)
}

/// `mask`, or `*_mask`, with C's trailing `_` allowed.
pub(crate) fn mask_named(name: &str) -> bool {
    let name = name.trim_end_matches('_');
    name == "mask" || name.ends_with("_mask")
}

/// **wave-6l relay 063 (item 6; wave-5d 096 STOP 3) — a mask is not a count.**
/// The argument at `span` is an operand named `mask` or `*_mask` (a local, a
/// parameter or a field; C's trailing `_` allowed), or a local defined once
/// from one by `x & m`, `m + 1` or `m.wrapping_add(1)`. A mask is the buffer's
/// size − 1, and a ring-buffer reader reads past it.
pub(crate) fn mask_operand(tcx: TyCtxt<'_>, caller: LocalDefId, span: rustc_span::Span) -> bool {
    let Some((body, argument)) = argument_at(tcx, caller, span) else {
        return false;
    };
    let named = |e: &Expr<'_>| {
        let name = match peel(e).kind {
            ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) => match path.res {
                Res::Local(id) => tcx.hir_name(id),
                _ => return false,
            },
            ExprKind::Field(_, ident) => ident.name,
            _ => return false,
        };
        mask_named(name.as_str())
    };
    if named(argument) {
        return true;
    }
    let definitions = Definitions::of(tcx, body);
    let derived = definitions.resolve(argument);
    // A plain alias (`let m = mask;`) resolves to the mask itself.
    if named(derived) {
        return true;
    }
    match derived.kind {
        ExprKind::Binary(op, left, right) => match op.node {
            rustc_hir::BinOpKind::BitAnd => named(left) || named(right),
            rustc_hir::BinOpKind::Add => {
                (named(left) && constant(right)) || (named(right) && constant(left))
            }
            _ => false,
        },
        ExprKind::MethodCall(segment, receiver, [argument], _) => {
            segment.ident.name.as_str() == "wrapping_add" && named(receiver) && constant(argument)
        }
        _ => false,
    }
}

/// **Relay 066 (R666-2, STOP 1) — a NO-OP mask.** The argument at `span` is a
/// constant expression: literals under casts, `!` / `-`, binary operations of
/// constants, constant items and associated constants (`usize::MAX`). It may
/// be reached through a local every definition of which is constant (its `let`
/// and every plain assignment, C89's declare-then-assign; a compound
/// assignment or a borrow is an unknown write), or through the caller's
/// never-written FORMAL, when any call site passes a constant there (the
/// relay 066 review's A1: brotli Quality10's `mask` reaches inner seams as
/// `ringbuffer_mask`). brotli's `BrotliCompressBufferQuality10` passes `let
/// mask = !0 >> 1` over a flat input. R477-6's `mask + 1` is a §77 claim
/// founded on the masking proof, and it holds for a ring buffer of
/// `mask + 1` elements. A constant mask names no buffer, and `!0 >> 1`
/// renders 2^63, past `from_raw_parts`' `isize::MAX`. The seam refuses it.
pub(crate) fn constant_mask(
    tcx: TyCtxt<'_>,
    facts: &super::emitability::EmitabilityFacts,
    caller: LocalDefId,
    span: rustc_span::Span,
) -> bool {
    constant_mask_at(tcx, facts, caller, span, 0)
}

fn constant_mask_at(
    tcx: TyCtxt<'_>,
    facts: &super::emitability::EmitabilityFacts,
    caller: LocalDefId,
    span: rustc_span::Span,
    depth: u32,
) -> bool {
    if depth > 6 {
        return false;
    }
    let Some((body, argument)) = argument_at(tcx, caller, span) else {
        return false;
    };
    let definitions = Definitions::of(tcx, body);
    if constant_expression(tcx, caller, &definitions, argument, 0) {
        return true;
    }
    // Through the caller's never-written formal: any call site that passes a
    // constant there.
    let Some(id) = local_of(argument) else {
        return false;
    };
    let Some(index) = body.params.iter().position(|param| param.pat.hir_id == id) else {
        return false;
    };
    if definitions.assigned.contains(&id) {
        return false;
    }
    facts.call_args.get(&caller).is_some_and(|sites| {
        sites.iter().any(|site| {
            site.args
                .iter()
                .find(|arg| arg.index == index)
                .is_some_and(|arg| constant_mask_at(tcx, facts, site.caller, arg.span, depth + 1))
        })
    })
}

/// A constant expression in `owner`'s body (see [`constant_mask`]).
fn constant_expression<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    definitions: &Definitions<'tcx>,
    e: &Expr<'tcx>,
    depth: u32,
) -> bool {
    if depth > 16 {
        return false;
    }
    match e.kind {
        ExprKind::Lit(_) => true,
        ExprKind::Unary(rustc_hir::UnOp::Not | rustc_hir::UnOp::Neg, inner)
        | ExprKind::Cast(inner, _)
        | ExprKind::DropTemps(inner) => {
            constant_expression(tcx, owner, definitions, inner, depth + 1)
        }
        ExprKind::Binary(_, left, right) => {
            constant_expression(tcx, owner, definitions, left, depth + 1)
                && constant_expression(tcx, owner, definitions, right, depth + 1)
        }
        ExprKind::Path(ref qpath) => {
            let res = tcx.typeck(owner).qpath_res(qpath, e.hir_id);
            match res {
                Res::Def(
                    rustc_hir::def::DefKind::Const | rustc_hir::def::DefKind::AssocConst,
                    _,
                ) => true,
                Res::Local(id) => {
                    // Every definition constant: the `let` and each plain
                    // assignment; a compound assignment or a borrow is not.
                    if definitions.unknown_writes.contains(&id) {
                        return false;
                    }
                    let mut defs = definitions
                        .initializer
                        .get(&id)
                        .into_iter()
                        .copied()
                        .chain(
                            definitions
                                .assignments
                                .get(&id)
                                .into_iter()
                                .flatten()
                                .copied(),
                        )
                        .peekable();
                    defs.peek().is_some()
                        && defs
                            .all(|def| constant_expression(tcx, owner, definitions, def, depth + 1))
                }
                _ => false,
            }
        }
        _ => false,
    }
}

fn local_callee(tcx: TyCtxt<'_>, owner: LocalDefId, callee: &Expr<'_>) -> Option<LocalDefId> {
    match tcx.typeck(owner).expr_ty(callee).kind() {
        TyKind::FnDef(definition, _) => definition
            .as_local()
            .filter(|local| tcx.hir_node_by_def_id(*local).body_id().is_some()),
        _ => None,
    }
}

/// Each local's `let` initializer, whether it is ever reassigned (or
/// borrowed), and whether any such write may store a value other than `0`.
struct Definitions<'tcx> {
    initializer: rustc_hash::FxHashMap<HirId, &'tcx Expr<'tcx>>,
    assigned: rustc_hash::FxHashSet<HirId>,
    nonzero: rustc_hash::FxHashSet<HirId>,
    /// Every plain assignment's value, per local (relay 066: C89's
    /// declare-then-assign).
    assignments: rustc_hash::FxHashMap<HirId, Vec<&'tcx Expr<'tcx>>>,
    /// Locals written by a compound assignment or through a borrow.
    unknown_writes: rustc_hash::FxHashSet<HirId>,
}

impl<'tcx> Definitions<'tcx> {
    fn of(tcx: TyCtxt<'tcx>, body: &'tcx rustc_hir::Body<'tcx>) -> Self {
        struct Collect<'tcx>(TyCtxt<'tcx>, Definitions<'tcx>);
        impl<'tcx> Visitor<'tcx> for Collect<'tcx> {
            type NestedFilter = OnlyBodies;

            fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
                self.0
            }

            fn visit_local(&mut self, local: &'tcx rustc_hir::LetStmt<'tcx>) {
                if let PatKind::Binding(_, id, _, None) = local.pat.kind
                    && let Some(init) = local.init
                {
                    self.1.initializer.insert(id, init);
                }
                intravisit::walk_local(self, local);
            }

            fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
                if let ExprKind::Assign(lhs, rhs, _) = e.kind
                    && let Some(id) = local_of(lhs)
                {
                    self.1.assigned.insert(id);
                    self.1.assignments.entry(id).or_default().push(rhs);
                    if !zero_literal(rhs) && !preserves_zero(id, rhs) {
                        self.1.nonzero.insert(id);
                    }
                }
                // Codex 062b: `x += 0`, `x |= 0`, `x *= y` leave a zero zero.
                if let ExprKind::AssignOp(op, lhs, rhs) = e.kind
                    && let Some(id) = local_of(lhs)
                {
                    self.1.assigned.insert(id);
                    self.1.unknown_writes.insert(id);
                    if !zero_preserving_op(op.node, rhs) {
                        self.1.nonzero.insert(id);
                    }
                }
                // A borrowed local may be written through the borrow.
                if let ExprKind::AddrOf(_, _, place) = e.kind
                    && let Some(id) = local_of(place)
                {
                    self.1.assigned.insert(id);
                    self.1.unknown_writes.insert(id);
                    self.1.nonzero.insert(id);
                }
                intravisit::walk_expr(self, e);
            }
        }
        let mut collect = Collect(
            tcx,
            Definitions {
                initializer: Default::default(),
                assigned: Default::default(),
                nonzero: Default::default(),
                assignments: Default::default(),
                unknown_writes: Default::default(),
            },
        );
        collect.visit_body(body);
        collect.1
    }

    /// The expression a never-reassigned local stands for.
    fn resolve<'a>(&'a self, e: &'a Expr<'tcx>) -> &'a Expr<'tcx> {
        let mut e = peel(e);
        let mut steps = 0;
        while let ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = e.kind
            && let Res::Local(id) = path.res
            && !self.assigned.contains(&id)
            && let Some(init) = self.initializer.get(&id)
            && steps < 16
        {
            e = peel(init);
            steps += 1;
        }
        e
    }

    /// `x & m` with a non-literal operand, directly or through a local.
    fn masked(&self, e: &Expr<'tcx>) -> bool {
        match self.resolve(e).kind {
            ExprKind::Binary(op, left, right)
                if matches!(op.node, rustc_hir::BinOpKind::BitAnd) =>
            {
                !constant(left) || !constant(right)
            }
            _ => false,
        }
    }

    /// A masked index plus a non-constant: `m + len`, `m.wrapping_add(len)`.
    fn past_mask_by_runtime(&self, e: &Expr<'tcx>) -> bool {
        match self.resolve(e).kind {
            ExprKind::Binary(op, left, right) if matches!(op.node, rustc_hir::BinOpKind::Add) => {
                (self.masked(left) && !constant(right)) || (self.masked(right) && !constant(left))
            }
            ExprKind::MethodCall(segment, receiver, [argument], _)
                if matches!(segment.ident.name.as_str(), "wrapping_add" | "add") =>
            {
                (self.masked(receiver) && !constant(argument))
                    || (self.masked(argument) && !constant(receiver))
            }
            _ => false,
        }
    }
}

struct Uses<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    function: LocalDefId,
    binding: HirId,
    definitions: &'a Definitions<'tcx>,
    /// (A1) indexed past a masked index by a runtime length.
    direct: bool,
    /// (A2) a pointer derived at a masked index, handed to these positions.
    escapes: Vec<(LocalDefId, usize)>,
    /// (B) the pointer handed on, bare, to these positions.
    forwards: Vec<(LocalDefId, usize)>,
}

impl<'tcx> Uses<'_, 'tcx> {
    /// The call position a derived pointer reaches through `&*`, casts and
    /// parentheses, if any.
    fn call_position(&self, mut e: &'tcx Expr<'tcx>) -> Option<(LocalDefId, usize)> {
        loop {
            let Node::Expr(parent) = self.tcx.parent_hir_node(e.hir_id) else {
                return None;
            };
            match parent.kind {
                ExprKind::Cast(..)
                | ExprKind::DropTemps(..)
                | ExprKind::AddrOf(..)
                | ExprKind::Unary(rustc_hir::UnOp::Deref, _) => e = parent,
                ExprKind::Call(callee, args) => {
                    let local = local_callee(self.tcx, self.function, callee)?;
                    let index = args.iter().position(|arg| arg.hir_id == e.hir_id)?;
                    return Some((local, index));
                }
                _ => return None,
            }
        }
    }
}

impl<'tcx> Visitor<'tcx> for Uses<'_, 'tcx> {
    type NestedFilter = OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_expr(&mut self, e: &'tcx Expr<'tcx>) {
        if is_local(e, self.binding)
            && let Node::Expr(parent) = self.tcx.parent_hir_node(e.hir_id)
        {
            match parent.kind {
                ExprKind::MethodCall(segment, receiver, [index], _)
                    if receiver.hir_id == e.hir_id
                        && ARITHMETIC.contains(&segment.ident.name.as_str()) =>
                {
                    if self.definitions.past_mask_by_runtime(index) {
                        self.direct = true;
                    } else if self.definitions.masked(index)
                        && let Some(position) = self.call_position(parent)
                    {
                        self.escapes.push(position);
                    }
                }
                ExprKind::Call(callee, args) => {
                    if let Some(local) = local_callee(self.tcx, self.function, callee)
                        && let Some(index) = args.iter().position(|arg| arg.hir_id == e.hir_id)
                    {
                        self.forwards.push((local, index));
                    }
                }
                _ => {}
            }
        }
        intravisit::walk_expr(self, e);
    }
}
