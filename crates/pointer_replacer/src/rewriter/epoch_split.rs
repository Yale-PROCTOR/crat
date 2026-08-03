use rustc_ast::{
    ast::{Block, Expr, ExprKind, StmtKind},
    mut_visit::{self, MutVisitor},
};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    self as hir, HirId, QPath,
    def::Res,
    intravisit::{self, Visitor},
};
use rustc_middle::{hir::nested_filter, ty::TyCtxt};
use rustc_span::Symbol;
use utils::{
    hir::{is_lhs, lhs_base},
    ir::AstToHir,
};

use super::Config;

// splits a reused raw-pointer scratch local (`let mut x = null` reassigned to
// several distinct base pointers) into one fresh `let x_N` per epoch, so the
// array-local provenance stage that follows sees single-base locals. runs as a
// pointer-pass stage in its own compiler session, before
// `rewrite_array_local_provenance`. see
// docs/superpowers/specs/2026-07-01-pointer-epoch-split-preprocess-design.md
// for the algorithm and 2026-07-03-pointer-epoch-split-pointer-stage-design.md
// for the placement.

// the finished plan consumed by `EpochSplitApplier`
pub(crate) struct PointerEpochSplitPlan {
    // per-occurrence rename: HIR id of a path expr -> epoch local name.
    pub path_renames: FxHashMap<HirId, Symbol>,
    // HIR id of a base-changing assignment expr -> the `let` to emit in its place.
    pub assignment_replacements: FxHashMap<HirId, EpochLetIntro>,
    // `let`-stmt HIR ids of dead scratch inits to delete.
    pub original_inits_to_remove: FxHashSet<HirId>,
}

pub(crate) struct EpochLetIntro {
    pub new_name: Symbol,
    pub ty_string: String,
}

impl PointerEpochSplitPlan {
    fn empty() -> Self {
        PointerEpochSplitPlan {
            path_renames: FxHashMap::default(),
            assignment_replacements: FxHashMap::default(),
            original_inits_to_remove: FxHashSet::default(),
        }
    }
}

// ── candidate collection ──────────────────────────────────────────────────────

// facts about one candidate scratch local, gathered before the epoch analysis.
struct Candidate {
    // the `let mut x = null;` stmt to delete once the local is split.
    init_let_stmt: HirId,
    // the local's declared type, e.g. "*mut i8", rendered once here.
    ty_string: String,
}

// returns the accepted-shape candidates for one body: `let mut` raw-pointer locals
// with a null-ish init and an identifier pattern, that are not address-taken,
// closure-captured, or AssignOp-written.
fn collect_candidates<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &hir::Body<'tcx>,
) -> FxHashMap<HirId, Candidate> {
    let mut v = CandidateVisitor {
        tcx,
        candidates: FxHashMap::default(),
        disqualified: FxHashSet::default(),
        in_closure: 0,
    };
    v.visit_body(body);
    v.candidates.retain(|id, _| !v.disqualified.contains(id));
    v.candidates
}

struct CandidateVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    candidates: FxHashMap<HirId, Candidate>,
    disqualified: FxHashSet<HirId>,
    in_closure: usize,
}

impl<'tcx> Visitor<'tcx> for CandidateVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_local(&mut self, let_stmt: &'tcx hir::LetStmt<'tcx>) {
        intravisit::walk_local(self, let_stmt);

        // shape: `let mut x: *mut/const T = <null-ish>;` with a plain ident pattern.
        let hir::PatKind::Binding(
            hir::BindingMode(hir::ByRef::No, hir::Mutability::Mut),
            binding_id,
            _,
            None,
        ) = let_stmt.pat.kind
        else {
            return;
        };
        let typeck = self.tcx.typeck(binding_id.owner.def_id);
        let ty = typeck.node_type(binding_id);
        if !ty.is_raw_ptr() {
            return;
        }
        let Some(init) = let_stmt.init else { return };
        if !is_null_init(init) {
            return;
        }
        let ty_string = utils::ir::mir_ty_to_string(ty, self.tcx);
        self.candidates.insert(
            binding_id,
            Candidate {
                init_let_stmt: let_stmt.hir_id,
                ty_string,
            },
        );
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        // track closure nesting so we can disqualify captured locals.
        if matches!(expr.kind, hir::ExprKind::Closure(_)) {
            self.in_closure += 1;
            intravisit::walk_expr(self, expr);
            self.in_closure -= 1;
            return;
        }

        if let hir::ExprKind::Path(QPath::Resolved(_, path)) = expr.kind
            && let Res::Local(binding_id) = path.res
            && self.candidates.contains_key(&binding_id)
        {
            // a use inside a closure means the local is captured -> cannot split.
            if self.in_closure > 0 {
                self.disqualified.insert(binding_id);
            }
            let (_, parent) = self.tcx.hir_parent_iter(expr.hir_id).next().unwrap();
            if let hir::Node::Expr(parent) = parent {
                match parent.kind {
                    // `&x` / `&raw mut x` etc: the binding's address escapes.
                    hir::ExprKind::AddrOf(_, _, inner) if inner.hir_id == expr.hir_id => {
                        self.disqualified.insert(binding_id);
                    }
                    // `x += n`: reads-and-writes in place, cannot become a fresh `let`.
                    hir::ExprKind::AssignOp(_, l, _) if l.hir_id == expr.hir_id => {
                        self.disqualified.insert(binding_id);
                    }
                    _ => {}
                }
            }
        }

        intravisit::walk_expr(self, expr);
    }
}

// recognizes `0 as *mut T`, `std::ptr::null_mut()`, and `null()` initializers.
fn is_null_init(expr: &hir::Expr<'_>) -> bool {
    match expr.kind {
        hir::ExprKind::Cast(inner, _) => {
            matches!(inner.kind, hir::ExprKind::Lit(lit)
                if matches!(lit.node, rustc_ast::LitKind::Int(v, _) if v == 0))
        }
        hir::ExprKind::Call(callee, _) => {
            if let hir::ExprKind::Path(qpath) = callee.kind {
                let name = match qpath {
                    QPath::Resolved(_, p) => p.segments.last().map(|s| s.ident.name),
                    QPath::TypeRelative(_, seg) => Some(seg.ident.name),
                    QPath::LangItem(..) => None,
                };
                matches!(name, Some(n) if n == rustc_span::Symbol::intern("null_mut")
                    || n == rustc_span::Symbol::intern("null"))
            } else {
                false
            }
        }
        _ => false,
    }
}

// ── epoch state ───────────────────────────────────────────────────────────────

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct EpochId(usize);

#[derive(Clone, PartialEq, Eq)]
enum EpochValue {
    Original,
    Epoch(EpochId),
    Ambiguous,
    Blocked,
}

// dataflow value: cloned at branches, merged at joins. holds only per-local state.
#[derive(Clone, Default)]
struct EpochEnv {
    current: FxHashMap<HirId, EpochValue>,
}

impl EpochEnv {
    fn get(&self, local: HirId) -> EpochValue {
        self.current
            .get(&local)
            .cloned()
            .unwrap_or(EpochValue::Original)
    }

    fn set(&mut self, local: HirId, v: EpochValue) {
        self.current.insert(local, v);
    }
}

// shared per-function state: id allocation + tentative results + rejections.
// NOT cloned at branches, so sibling branches cannot mint colliding ids.
struct FnState<'tcx> {
    tcx: TyCtxt<'tcx>,
    candidates: FxHashMap<HirId, Candidate>,
    next_epoch: usize,
    // epoch -> the local it belongs to (for naming + typing at finalization).
    epoch_local: FxHashMap<EpochId, HirId>,
    // tentative: occurrence expr hir_id -> epoch.
    path_renames: FxHashMap<HirId, EpochId>,
    // tentative: base-changing assign expr hir_id -> the new epoch it introduces.
    assignment_epochs: FxHashMap<HirId, EpochId>,
    // candidate locals abandoned because some occurrence would keep the original name.
    rejected: FxHashSet<HirId>,
}

impl<'tcx> FnState<'tcx> {
    fn new(tcx: TyCtxt<'tcx>, candidates: FxHashMap<HirId, Candidate>) -> Self {
        FnState {
            tcx,
            candidates,
            next_epoch: 0,
            epoch_local: FxHashMap::default(),
            path_renames: FxHashMap::default(),
            assignment_epochs: FxHashMap::default(),
            rejected: FxHashSet::default(),
        }
    }

    fn fresh_epoch(&mut self, local: HirId) -> EpochId {
        let id = EpochId(self.next_epoch);
        self.next_epoch += 1;
        self.epoch_local.insert(id, local);
        id
    }

    fn reject(&mut self, local: HirId) {
        self.rejected.insert(local);
    }

    // record a read of `local` in the given state: rename if it maps to a single
    // epoch, otherwise reject the local (all-or-nothing invariant).
    fn read(&mut self, local: HirId, occ: HirId, env: &EpochEnv) {
        match env.get(local) {
            EpochValue::Epoch(id) => {
                self.path_renames.insert(occ, id);
            }
            _ => self.reject(local),
        }
    }
}

// ── structured traversal ──────────────────────────────────────────────────────

impl<'tcx> FnState<'tcx> {
    fn analyze_block(&mut self, block: &hir::Block<'tcx>, mut env: EpochEnv) -> EpochEnv {
        // epochs allocated during this block have their `let` scoped to this block.
        // snapshot the counter so we can invalidate them on exit: a use in an
        // enclosing scope must not rename to an out-of-scope epoch `let`.
        let scope_base = self.next_epoch;
        for stmt in block.stmts {
            env = self.analyze_stmt(stmt, env);
        }
        if let Some(e) = block.expr {
            env = self.analyze_expr(e, env);
        }
        // block-local epochs go out of scope here -> mark Blocked so any later read
        // in a shallower scope rejects the local (the epoch `let` is no longer visible).
        let locals: Vec<HirId> = self.candidates.keys().copied().collect();
        for local in locals {
            if let EpochValue::Epoch(id) = env.get(local)
                && id.0 >= scope_base
            {
                env.set(local, EpochValue::Blocked);
            }
        }
        env
    }

    fn analyze_stmt(&mut self, stmt: &hir::Stmt<'tcx>, env: EpochEnv) -> EpochEnv {
        match stmt.kind {
            // a candidate's own scratch `let` keeps it `Original`; only its init is
            // analyzed (null -> no candidate reads). non-candidate lets: analyze init.
            hir::StmtKind::Let(l) => match l.init {
                Some(init) => self.analyze_expr(init, env),
                None => env,
            },
            hir::StmtKind::Expr(e) | hir::StmtKind::Semi(e) => self.analyze_expr(e, env),
            hir::StmtKind::Item(_) => env,
        }
    }

    fn analyze_expr(&mut self, expr: &'tcx hir::Expr<'tcx>, env: EpochEnv) -> EpochEnv {
        match expr.kind {
            // direct assignment to a candidate: classify it.
            hir::ExprKind::Assign(lhs, rhs, _) if self.assign_target(lhs).is_some() => {
                let local = self.assign_target(lhs).unwrap();
                self.analyze_assign(expr.hir_id, local, lhs, rhs, env)
            }
            // precise if-branch handling: clone env per branch, merge exits.
            hir::ExprKind::If(cond, then, els) => {
                let env = self.analyze_expr(cond, env);
                let then_env = self.analyze_expr(then, env.clone());
                let else_env = match els {
                    Some(e) => self.analyze_expr(e, env.clone()),
                    None => env.clone(),
                };
                self.merge(&then_env, &else_env)
            }
            hir::ExprKind::Loop(body, _, _, _) => {
                // reject any candidate base-changed inside the loop (cannot introduce
                // an epoch `let` in a loop). scan first so we know before renaming.
                for local in self.loop_base_changed(body) {
                    self.reject(local);
                }
                // analyze the body against the incoming env so incoming epochs and
                // same-epoch movements rename; the epoch local is declared outside.
                let _ = self.analyze_block(body, env.clone());
                // conservatively, candidate state after the loop is unchanged for
                // reads (same-epoch movement keeps the epoch; base-changed locals are
                // already rejected). return the incoming env.
                env
            }
            hir::ExprKind::Match(scrutinee, arms, _) => {
                let env = self.analyze_expr(scrutinee, env);
                let mut exit: Option<EpochEnv> = None;
                for arm in arms {
                    let arm_env = self.analyze_expr(arm.body, env.clone());
                    exit = Some(match exit {
                        None => arm_env,
                        Some(prev) => self.merge(&prev, &arm_env),
                    });
                }
                exit.unwrap_or(env)
            }
            hir::ExprKind::Block(block, _) => self.analyze_block(block, env),
            // opaque scope: do not descend (captured candidates already rejected).
            hir::ExprKind::Closure(_) => env,
            // a bare read of a candidate.
            hir::ExprKind::Path(QPath::Resolved(_, path)) => {
                if let Res::Local(local) = path.res
                    && self.candidates.contains_key(&local)
                {
                    self.read(local, expr.hir_id, &env);
                }
                env
            }
            // everything else: recurse left-to-right, recording candidate reads.
            _ => self.record_reads(expr, &env),
        }
    }

    // if `lhs` is exactly `Path(local)` for a candidate, return that local.
    fn assign_target(&self, lhs: &hir::Expr<'tcx>) -> Option<HirId> {
        if let hir::ExprKind::Path(QPath::Resolved(_, path)) = lhs.kind
            && let Res::Local(local) = path.res
            && self.candidates.contains_key(&local)
        {
            Some(local)
        } else {
            None
        }
    }

    fn analyze_assign(
        &mut self,
        assign_hir_id: HirId,
        local: HirId,
        lhs: &'tcx hir::Expr<'tcx>,
        rhs: &'tcx hir::Expr<'tcx>,
        mut env: EpochEnv,
    ) -> EpochEnv {
        // analyze the rhs first, in the INCOMING env (so `x = wrap(x)` renames the
        // read of x to the current epoch before the new epoch begins).
        env = self.analyze_expr(rhs, env);

        if let Some(_recv) = self.same_local_movement(local, rhs) {
            // same-epoch cursor movement: keep the epoch, rename both sides.
            match env.get(local) {
                EpochValue::Epoch(id) => {
                    self.path_renames.insert(lhs.hir_id, id);
                    // the rhs receiver read was already renamed by analyze_expr(rhs).
                    // env unchanged: still Epoch(id).
                }
                // no live epoch to move -> the rhs read of x is unattributable.
                _ => self.reject(local),
            }
            env
        } else {
            // base-changing definition: start a fresh epoch, promote to a `let`.
            let id = self.fresh_epoch(local);
            self.assignment_epochs.insert(assign_hir_id, id);
            env.set(local, EpochValue::Epoch(id));
            env
        }
    }

    // returns Some(receiver) when `rhs` is `x.offset|add|sub|wrapping_*(..)` or
    // `x as *mut U` on the SAME candidate local `x`.
    fn same_local_movement(
        &self,
        local: HirId,
        rhs: &hir::Expr<'tcx>,
    ) -> Option<&'tcx hir::Expr<'tcx>> {
        let is_local_path = |e: &hir::Expr<'tcx>| {
            matches!(e.kind, hir::ExprKind::Path(QPath::Resolved(_, p))
                if matches!(p.res, Res::Local(l) if l == local))
        };
        match rhs.kind {
            hir::ExprKind::MethodCall(seg, receiver, _, _)
                if is_local_path(receiver)
                    && matches!(
                        seg.ident.name.as_str(),
                        "offset"
                            | "add"
                            | "sub"
                            | "wrapping_offset"
                            | "wrapping_add"
                            | "wrapping_sub"
                    ) =>
            {
                Some(receiver)
            }
            hir::ExprKind::Cast(inner, _) if is_local_path(inner) => Some(inner),
            _ => None,
        }
    }

    // merge two branch-exit envs per the spec's merge table. equal states survive;
    // any disagreement becomes Ambiguous; Blocked dominates.
    fn merge(&self, a: &EpochEnv, b: &EpochEnv) -> EpochEnv {
        let mut out = EpochEnv::default();
        for local in self.candidates.keys() {
            let va = a.get(*local);
            let vb = b.get(*local);
            let merged = match (&va, &vb) {
                _ if va == vb => va.clone(),
                (EpochValue::Blocked, _) | (_, EpochValue::Blocked) => EpochValue::Blocked,
                _ => EpochValue::Ambiguous,
            };
            out.set(*local, merged);
        }
        out
    }

    // recurse into `expr`'s subexpressions recording candidate reads in `env`, and
    // rejecting any candidate written by a nested Assign/AssignOp we did not classify.
    fn record_reads(&mut self, expr: &'tcx hir::Expr<'tcx>, env: &EpochEnv) -> EpochEnv {
        let mut v = ReadCollector { state: self, env };
        intravisit::walk_expr(&mut v, expr);
        env.clone()
    }

    // candidate locals that receive a base-changing assignment anywhere in `block`.
    fn loop_base_changed(&self, block: &'tcx hir::Block<'tcx>) -> Vec<HirId> {
        let mut found = Vec::new();
        let mut v = BaseChangeScanner {
            state: self,
            found: &mut found,
        };
        v.visit_block(block);
        found
    }
}

// nested walker used by `record_reads`. does not model control flow; sound because
// it rejects on any unclassified candidate write it encounters.
struct ReadCollector<'a, 'tcx> {
    state: &'a mut FnState<'tcx>,
    env: &'a EpochEnv,
}

impl<'tcx> Visitor<'tcx> for ReadCollector<'_, 'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.state.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        // do not descend into closures.
        if matches!(expr.kind, hir::ExprKind::Closure(_)) {
            return;
        }
        // any unclassified write to a candidate -> reject (soundness).
        if let hir::ExprKind::Assign(l, _, _) | hir::ExprKind::AssignOp(_, l, _) = expr.kind
            && let hir::ExprKind::Path(QPath::Resolved(_, p)) = lhs_base(l).kind
            && let Res::Local(local) = p.res
            && self.state.candidates.contains_key(&local)
        {
            self.state.reject(local);
        }
        // a read of a candidate.
        if let hir::ExprKind::Path(QPath::Resolved(_, path)) = expr.kind
            && let Res::Local(local) = path.res
            && self.state.candidates.contains_key(&local)
            && !is_lhs(expr, self.state.tcx)
        {
            self.state.read(local, expr.hir_id, self.env);
        }
        intravisit::walk_expr(self, expr);
    }
}

struct BaseChangeScanner<'a, 'tcx> {
    state: &'a FnState<'tcx>,
    found: &'a mut Vec<HirId>,
}
impl<'tcx> Visitor<'tcx> for BaseChangeScanner<'_, 'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.state.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        if let hir::ExprKind::Assign(lhs, rhs, _) = expr.kind
            && let Some(local) = self.state.assign_target(lhs)
            && self.state.same_local_movement(local, rhs).is_none()
        {
            self.found.push(local);
        }
        intravisit::walk_expr(self, expr);
    }
}

// ── driver + finalization + name generation ───────────────────────────────────

// entry point: analyze every body in the crate and build the split plan.
fn analyze(tcx: TyCtxt<'_>) -> PointerEpochSplitPlan {
    let mut plan = PointerEpochSplitPlan::empty();
    let mut driver = Driver {
        tcx,
        plan: &mut plan,
    };
    tcx.hir_visit_all_item_likes_in_crate(&mut driver);
    plan
}

struct Driver<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    plan: &'a mut PointerEpochSplitPlan,
}

impl<'tcx> Visitor<'tcx> for Driver<'_, 'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_body(&mut self, body: &hir::Body<'tcx>) {
        analyze_body(self.tcx, body, self.plan);
        intravisit::walk_body(self, body);
    }
}

fn analyze_body<'tcx>(tcx: TyCtxt<'tcx>, body: &hir::Body<'tcx>, plan: &mut PointerEpochSplitPlan) {
    let candidates = collect_candidates(tcx, body);
    if candidates.is_empty() {
        return;
    }
    let mut state = FnState::new(tcx, candidates);
    state.analyze_expr(body.value, EpochEnv::default());
    finalize(tcx, body, &mut state, plan);
}

// commit accepted locals into `plan`, allocating fresh names for their epochs.
fn finalize<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &hir::Body<'tcx>,
    state: &mut FnState<'tcx>,
    plan: &mut PointerEpochSplitPlan,
) {
    let mut existing = existing_names(tcx, body);

    // count base-change epochs per local. only split a local with >= 2 epochs
    // (genuine reuse across distinct bases). a single-base local is left untouched:
    // removing its null init and promoting the sole reassignment to a `let` adds
    // noise and breaks downstream passes for no analysis benefit.
    let mut epoch_count: FxHashMap<HirId, usize> = FxHashMap::default();
    for local in state.epoch_local.values() {
        *epoch_count.entry(*local).or_default() += 1;
    }
    let should_split = |local: &HirId| {
        !state.rejected.contains(local) && epoch_count.get(local).copied().unwrap_or(0) >= 2
    };

    // stable order: name epochs by allocation order so suffixes are deterministic.
    let mut epoch_names: FxHashMap<EpochId, Symbol> = FxHashMap::default();
    let mut epochs: Vec<(EpochId, HirId)> =
        state.epoch_local.iter().map(|(e, l)| (*e, *l)).collect();
    epochs.sort_by_key(|(e, _)| e.0);
    for (epoch, local) in epochs {
        if !should_split(&local) {
            continue;
        }
        let stem = tcx.hir_name(local); // original binding name, e.g. `x`
        let name = fresh_name(stem.as_str(), &mut existing);
        epoch_names.insert(epoch, name);
    }

    // path renames for split locals (only epochs that received a name).
    for (occ, epoch) in &state.path_renames {
        if let Some(name) = epoch_names.get(epoch) {
            plan.path_renames.insert(*occ, *name);
        }
    }
    // assignment -> let intros for split locals.
    for (assign_hir_id, epoch) in &state.assignment_epochs {
        let local = state.epoch_local[epoch];
        if !should_split(&local) {
            continue;
        }
        let name = epoch_names[epoch];
        let ty_string = state.candidates[&local].ty_string.clone();
        plan.assignment_replacements.insert(
            *assign_hir_id,
            EpochLetIntro {
                new_name: name,
                ty_string,
            },
        );
    }
    // remove the scratch init only of split locals.
    for (local, cand) in &state.candidates {
        if should_split(local) {
            plan.original_inits_to_remove.insert(cand.init_let_stmt);
        }
    }
}

// all local + param names in this body, used as the freshness set.
fn existing_names<'tcx>(tcx: TyCtxt<'tcx>, body: &hir::Body<'tcx>) -> FxHashSet<String> {
    let mut names = FxHashSet::default();
    let mut v = NameCollector {
        tcx,
        names: &mut names,
    };
    v.visit_body(body);
    names
}

struct NameCollector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    names: &'a mut FxHashSet<String>,
}
impl<'tcx> Visitor<'tcx> for NameCollector<'_, 'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_pat(&mut self, pat: &'tcx hir::Pat<'tcx>) {
        if let hir::PatKind::Binding(_, _, ident, _) = pat.kind {
            self.names.insert(ident.name.to_string());
        }
        intravisit::walk_pat(self, pat);
    }
}

// `x` -> `x_0`, `x_1`, ...; skips names already present. modeled on
// `fresh_index_name` in pointer_replacer's array_local_index_rewriter.
fn fresh_name(stem: &str, existing: &mut FxHashSet<String>) -> Symbol {
    let mut n = 0usize;
    loop {
        let candidate = format!("{stem}_{n}");
        if !existing.contains(&candidate) {
            existing.insert(candidate.clone());
            return Symbol::intern(&candidate);
        }
        n += 1;
    }
}

// ── plan application ──────────────────────────────────────────────────────────

// applies the plan to the AST: renames epoch-covered path uses, replaces
// base-changing assignments with epoch `let`s, and drops dead scratch inits.
struct EpochSplitApplier<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    ast_to_hir: &'a AstToHir,
    plan: PointerEpochSplitPlan,
}

impl MutVisitor for EpochSplitApplier<'_, '_> {
    fn visit_expr(&mut self, expr: &mut Expr) {
        if matches!(expr.kind, ExprKind::Path(_, _))
            && let Some(hir_expr) = self.ast_to_hir.get_expr(expr.id, self.tcx)
            && let Some(name) = self.plan.path_renames.get(&hir_expr.hir_id)
        {
            // per-occurrence rename to the epoch local (keyed by the occurrence,
            // not the binding: different occurrences map to different epochs).
            *expr = utils::expr!("{name}");
        }
        mut_visit::walk_expr(self, expr);
    }

    fn visit_block(&mut self, b: &mut Block) {
        mut_visit::walk_block(self, b);

        // replace base-changing assignments (`x = rhs;`) with epoch `let`s
        // (`let mut x_N: TY = rhs;`). the rhs is taken from the already-walked
        // statement, so nested renames are in place.
        for stmt in &mut b.stmts {
            let StmtKind::Semi(e) = &stmt.kind else { continue };
            let Some(hir_expr) = self.ast_to_hir.get_expr(e.id, self.tcx) else {
                continue;
            };
            let Some(intro) = self.plan.assignment_replacements.get(&hir_expr.hir_id) else {
                continue;
            };
            let ExprKind::Assign(_, rhs, _) = &e.kind else { continue };
            let rhs_str = pprust::expr_to_string(rhs);
            let new_name = intro.new_name;
            let ty_string = &intro.ty_string;
            *stmt = utils::stmt!("let mut {new_name}: {ty_string} = {rhs_str};");
        }

        // drop the dead scratch inits of split locals.
        b.stmts.retain(|stmt| {
            if let StmtKind::Let(local) = &stmt.kind
                && let Some(hir_stmt) = self.ast_to_hir.get_let_stmt(local.id, self.tcx)
                && self
                    .plan
                    .original_inits_to_remove
                    .contains(&hir_stmt.hir_id)
            {
                false
            } else {
                true
            }
        });
    }
}

// ── entry point ───────────────────────────────────────────────────────────────

pub fn rewrite_epoch_split(_config: &Config, tcx: TyCtxt<'_>) -> (String, bool) {
    let mut krate = utils::ast::expanded_ast(tcx);
    let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

    let plan = analyze(tcx);
    let changed = !plan.path_renames.is_empty()
        || !plan.assignment_replacements.is_empty()
        || !plan.original_inits_to_remove.is_empty();
    if changed {
        let mut applier = EpochSplitApplier {
            tcx,
            ast_to_hir: &ast_to_hir,
            plan,
        };
        applier.visit_crate(&mut krate);
    }
    (pprust::crate_to_string_for_macros(&krate), changed)
}
