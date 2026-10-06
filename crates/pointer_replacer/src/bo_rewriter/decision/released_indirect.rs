//! **R857-2 / R858-4 (USER via the seat; reading (A) of era-5c 151; fan-out 074) —
//! the backstop: a lent formal released through a function pointer is decided
//! raw.**
//!
//! The lend's certificate (`licensing/lend.rs`) admits an indirect call that
//! receives a lent formal under R580-1's tier-2 retention waiver. A release is not
//! a retention: brotli's `BrotliEncoderDestroyInstance(state)` hands `state` to
//! `(*m).free_func`, whose program-assigned target `BrotliDefaultFreeFunc` frees
//! it, so the reference the frame emits for `state` is deallocated while its
//! protector is live (UB under Tree Borrows and Stacked Borrows, the fan-out's
//! Miri `repro/`). Until the certificate refuses such a formal, the generator
//! holds it here.
//!
//! **The sites** are the certificate's own: [`lend::Plan::waivers`], one per
//! indirect call a lendable formal's closure reaches.
//!
//! **The targets (reading (A), the closed world of R816):** the functions the
//! program itself makes into a value of the call's function-pointer type — every
//! function item the program's bodies reify at exactly that type, and every
//! function a static initializer names at it. A pointer only a client supplies
//! has no program target and is outside the claim. Reading the type rather than
//! each pointer's stores is a superset of the program's assignments to that
//! pointer: it can hold more, never less. Not covered: a function pointer the
//! program transmutes between two function-pointer types.
//!
//! **Releasing:** libc `free` / `realloc` at argument 0; a program function whose
//! formal (or a copy or cast of it) reaches a releasing argument of a call it
//! makes, directly, through a local callee or through an indirect call whose
//! targets release.
//!
//! **What is held:** the waiver site's formal, only where the settled table
//! delivers it; a formal the table already decides raw keeps its own reason.

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    HirId,
    def::{DefKind, Res},
    def_id::{DefId, LocalDefId},
    intravisit::{self, Visitor},
};
use rustc_middle::{
    mir::{BasicBlock, CastKind, Local, Operand, Rvalue, StatementKind, TerminatorKind},
    ty::{Ty, TyCtxt, TyKind, TypeckResults, adjustment::PointerCoercion},
};

use super::{DegradeReason, Subject, SubjectKind};
use crate::{analyses::borrow_ownership::licensing::lend, utils::rustc::RustProgram};

/// The reason's key in every table and receipt.
pub(crate) const KEY: &str = "held:released-through-indirect-call";

/// The program's function values, by the function-pointer type they are made at.
type Reified<'tcx> = FxHashMap<Ty<'tcx>, FxHashSet<DefId>>;

/// The formals to hold, with their reason; the caller applies them where the
/// settled table delivers the formal.
pub(crate) fn holds(
    program: &RustProgram<'_>,
    subjects: &[Subject],
) -> FxHashMap<(LocalDefId, HirId), DegradeReason> {
    let tcx = program.tcx;
    let plan = lend::collect(program);
    let mut out = FxHashMap::default();
    if plan.waivers.is_empty() {
        return out;
    }
    let functions: FxHashMap<String, LocalDefId> = program
        .functions
        .iter()
        .map(|&f| (tcx.def_path_str(f.to_def_id()), f))
        .collect();
    let reified = reified(program);
    let mut walk = ReleaseWalk::new(program, &reified);
    for site in &plan.waivers {
        let Some(&caller) = functions.get(&site.caller) else {
            continue;
        };
        let Some(formal) = (site.formal as usize).checked_sub(1) else {
            continue;
        };
        let Some(subject) = subjects.iter().find(|subject| {
            subject.fn_did == caller
                && matches!(subject.kind, SubjectKind::Param { hir_index } if hir_index == formal)
        }) else {
            continue;
        };
        let node = (subject.fn_did, subject.hir_id);
        if out.contains_key(&node) {
            continue;
        }
        let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
        let Some(data) = body.basic_blocks.get(BasicBlock::from_u32(site.block)) else {
            continue;
        };
        let func = match &data.terminator().kind {
            TerminatorKind::Call { func, .. } | TerminatorKind::TailCall { func, .. } => func,
            _ => continue,
        };
        let pointer = tcx.erase_regions(func.ty(&*body, tcx));
        let mut releasing = reified
            .get(&pointer)
            .into_iter()
            .flatten()
            .filter(|&&target| walk.releases(target, site.argument))
            .map(|&target| tcx.def_path_str(target))
            .collect::<Vec<_>>();
        releasing.sort();
        if releasing.is_empty() {
            continue;
        }
        out.insert(
            node,
            DegradeReason::ReleasedThroughIndirectCall {
                detail: format!(
                    "released-through-indirect-call:{}:bb{}[{}]:arg{};targets={}",
                    site.caller,
                    site.block,
                    site.statement,
                    site.argument,
                    releasing.join(",")
                ),
            },
        );
    }
    out
}

/// Every function value the program makes, by its function-pointer type: the
/// reifications in the program's bodies and the functions static initializers
/// name (read from HIR: building a static's CTFE MIR would steal its body).
fn reified<'tcx>(program: &RustProgram<'tcx>) -> Reified<'tcx> {
    let tcx = program.tcx;
    let mut out: Reified<'tcx> = FxHashMap::default();
    for &function in &program.functions {
        let body = tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(assign) = &statement.kind else {
                    continue;
                };
                if let Rvalue::Cast(
                    CastKind::PointerCoercion(PointerCoercion::ReifyFnPointer, _),
                    operand,
                    target,
                ) = &assign.1
                    && let Some(constant) = operand.constant()
                    && let TyKind::FnDef(def, _) = *constant.ty().kind()
                {
                    out.entry(tcx.erase_regions(*target))
                        .or_default()
                        .insert(def);
                }
            }
        }
    }
    struct Named<'tcx, 'a> {
        tcx: TyCtxt<'tcx>,
        typeck: &'tcx TypeckResults<'tcx>,
        out: &'a mut Reified<'tcx>,
    }
    impl<'tcx> Visitor<'tcx> for Named<'tcx, '_> {
        fn visit_expr(&mut self, expr: &'tcx rustc_hir::Expr<'tcx>) {
            if let rustc_hir::ExprKind::Path(qpath) = &expr.kind
                && let Res::Def(DefKind::Fn | DefKind::AssocFn, def) =
                    self.typeck.qpath_res(qpath, expr.hir_id)
                && let ty = self.typeck.expr_ty_adjusted(expr)
                && matches!(ty.kind(), TyKind::FnPtr(..))
            {
                self.out
                    .entry(self.tcx.erase_regions(ty))
                    .or_default()
                    .insert(def);
            }
            intravisit::walk_expr(self, expr);
        }
    }
    for def in tcx.hir_crate_items(()).definitions() {
        if matches!(tcx.def_kind(def), DefKind::Static { .. } | DefKind::Const)
            && !tcx.is_foreign_item(def)
            && let Some(body_id) = tcx.hir_node_by_def_id(def).body_id()
        {
            let mut named = Named {
                tcx,
                typeck: tcx.typeck(def),
                out: &mut out,
            };
            named.visit_expr(tcx.hir_body(body_id).value);
        }
    }
    out
}

/// The release walk: does a function release its argument? Answers are cached
/// only when final: a `false` that read a frame still open below it (a cycle
/// through a caller) is recomputed when asked again, so a release found later
/// on that caller's other path is never hidden by a cached `false`.
struct ReleaseWalk<'p, 'tcx> {
    program: &'p RustProgram<'tcx>,
    reified: &'p Reified<'tcx>,
    memo: FxHashMap<(DefId, usize), bool>,
    stack: Vec<(DefId, usize)>,
}

impl<'p, 'tcx> ReleaseWalk<'p, 'tcx> {
    fn new(program: &'p RustProgram<'tcx>, reified: &'p Reified<'tcx>) -> Self {
        Self {
            program,
            reified,
            memo: FxHashMap::default(),
            stack: Vec::new(),
        }
    }

    /// Does `function` release its argument `argument`?
    fn releases(&mut self, function: DefId, argument: usize) -> bool {
        self.visit(function, argument).0
    }

    /// The answer, and the lowest open frame it read (`usize::MAX` for none).
    fn visit(&mut self, function: DefId, argument: usize) -> (bool, usize) {
        let tcx = self.program.tcx;
        if tcx.is_foreign_item(function) {
            let name = tcx.item_name(function);
            return (
                argument == 0 && matches!(name.as_str(), "free" | "realloc"),
                usize::MAX,
            );
        }
        let Some(local) = function
            .as_local()
            .filter(|local| self.program.functions.contains(local))
        else {
            return (false, usize::MAX);
        };
        let key = (function, argument);
        if let Some(&known) = self.memo.get(&key) {
            return (known, usize::MAX);
        }
        if let Some(open) = self.stack.iter().position(|frame| *frame == key) {
            return (false, open);
        }
        let depth = self.stack.len();
        self.stack.push(key);
        let (found, lowest) = self.walk(local, argument);
        self.stack.pop();
        if found || lowest >= depth {
            self.memo.insert(key, found);
        }
        (found, lowest)
    }

    /// One body: the formal's closure (copies, casts, references through it and
    /// pointer results of library calls on it) and every call it reaches.
    fn walk(&mut self, local: LocalDefId, argument: usize) -> (bool, usize) {
        let tcx = self.program.tcx;
        let body = tcx.mir_drops_elaborated_and_const_checked(local).borrow();
        if argument >= body.arg_count {
            return (false, usize::MAX);
        }
        let mut closure = FxHashSet::from_iter([Local::from_usize(argument + 1)]);
        let member = |operand: &Operand<'_>, closure: &FxHashSet<Local>| {
            operand
                .place()
                .is_some_and(|place| place.projection.is_empty() && closure.contains(&place.local))
        };
        loop {
            let size = closure.len();
            for data in body.basic_blocks.iter() {
                for statement in &data.statements {
                    let StatementKind::Assign(assign) = &statement.kind else {
                        continue;
                    };
                    let (destination, rvalue) = &**assign;
                    let derived = match rvalue {
                        Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => {
                            member(operand, &closure)
                        }
                        Rvalue::RawPtr(_, place) | Rvalue::Ref(_, _, place) => {
                            place.is_indirect_first_projection() && closure.contains(&place.local)
                        }
                        _ => false,
                    };
                    if derived && destination.projection.is_empty() {
                        closure.insert(destination.local);
                    }
                }
                if let TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    ..
                } = &data.terminator().kind
                    && destination.projection.is_empty()
                    && body.local_decls[destination.local].ty.is_raw_ptr()
                    && args.iter().any(|operand| member(&operand.node, &closure))
                    && func
                        .constant()
                        .and_then(|constant| match *constant.ty().kind() {
                            TyKind::FnDef(def, _) => Some(def),
                            _ => None,
                        })
                        .is_some_and(|def| !def.is_local())
                {
                    closure.insert(destination.local);
                }
            }
            if closure.len() == size {
                break;
            }
        }
        let mut lowest = usize::MAX;
        for data in body.basic_blocks.iter() {
            let (func, args) = match &data.terminator().kind {
                TerminatorKind::Call { func, args, .. }
                | TerminatorKind::TailCall { func, args, .. } => (func, args),
                _ => continue,
            };
            // A function item called in place, or a function pointer.
            let direct = func
                .constant()
                .and_then(|constant| match *constant.ty().kind() {
                    TyKind::FnDef(def, _) => Some(def),
                    _ => None,
                });
            let pointer = tcx.erase_regions(func.ty(&*body, tcx));
            for (index, operand) in args.iter().enumerate() {
                if !member(&operand.node, &closure) {
                    continue;
                }
                // `visit` answers for a foreign item (`free` / `realloc`), a
                // program function, and no for any other library function.
                let targets: Vec<DefId> = match direct {
                    Some(callee) => vec![callee],
                    None => self
                        .reified
                        .get(&pointer)
                        .into_iter()
                        .flatten()
                        .copied()
                        .collect(),
                };
                for target in targets {
                    let (releasing, open) = self.visit(target, index);
                    lowest = lowest.min(open);
                    if releasing {
                        return (true, lowest);
                    }
                }
            }
        }
        (false, lowest)
    }
}

/// The formals [`holds`] names that the settled table delivers, and those this
/// stage held before that the table now decides raw for another reason (their
/// reason becomes the hold's; their form does not change).
pub(crate) fn to_hold(
    held: &FxHashMap<(LocalDefId, HirId), DegradeReason>,
    table: &super::DecisionTable,
    earlier: &FxHashSet<(LocalDefId, HirId)>,
) -> FxHashMap<(LocalDefId, HirId), DegradeReason> {
    let decided: FxHashMap<(LocalDefId, HirId), bool> = table
        .entries
        .iter()
        .map(|(subject, decision)| {
            // Exhaustive by rule (`import_denylist`): a new disposition is
            // classified here, never dropped by a bypass shape.
            let raw = match decision {
                super::Decision::Degraded(_) => true,
                super::Decision::Ref { .. }
                | super::Decision::InferredRef { .. }
                | super::Decision::Slice { .. }
                | super::Decision::NestedSlice { .. }
                | super::Decision::Cursor { .. }
                | super::Decision::Opt { .. }
                | super::Decision::Box(_) => false,
            };
            ((subject.fn_did, subject.hir_id), raw)
        })
        .collect();
    held.iter()
        .filter(|(node, _)| match decided.get(node) {
            Some(false) => true,
            Some(true) => earlier.contains(node),
            None => false,
        })
        .map(|(node, reason)| (*node, reason.clone()))
        .collect()
}
