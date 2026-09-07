//! Typed null components of tuple patterns in refutable-let expressions.
//! A component stays at its original expression span: its eventual temporary
//! belongs inside that component's block, never before the tuple or guard.
//! Only shared subjects are licensed, using the frozen Foster-derived
//! `subject.mutable` fact rather than raw-pointer spelling. Mutable pattern
//! obligations retain their prior disposition; no binding mutation is added.

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    Expr, ExprKind, HirId, Pat, PatKind,
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::ty::{TyCtxt, TyKind};
use rustc_span::Span;

use super::{
    super::additive::{FamilyPolicy, FamilyStage},
    DeclShape, Subject, SubjectKind,
    construction::{Construction, ConstructionFacts},
    declaration, emitability,
};

pub(crate) type PatternDeclarations = FxHashMap<(LocalDefId, HirId), PatternDeclaration>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PatternDeclaration {
    pub(crate) node: (LocalDefId, HirId),
    pub(crate) init_hir: HirId,
    pub(crate) init_span: Span,
    pub(crate) input_type: String,
    pub(crate) pointee: String,
    pub(crate) temporary: String,
}

struct BindingNames<'a>(&'a mut FxHashSet<String>);

impl<'tcx> Visitor<'tcx> for BindingNames<'_> {
    fn visit_pat(&mut self, pattern: &'tcx Pat<'tcx>) {
        if let PatKind::Binding(_, _, name, _) = pattern.kind {
            self.0.insert(name.name.to_string());
        }
        intravisit::walk_pat(self, pattern);
    }
}

struct Collector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    candidates: &'a FxHashSet<(LocalDefId, HirId)>,
    names: FxHashSet<String>,
    out: &'a mut PatternDeclarations,
}

impl<'tcx> Collector<'_, 'tcx> {
    fn component(&mut self, pattern: &'tcx Pat<'tcx>, expression: &'tcx Expr<'tcx>) {
        match (pattern.kind, expression.kind) {
            (PatKind::Tuple(patterns, rest), ExprKind::Tup(expressions))
                if rest.as_opt_usize().is_none() && patterns.len() == expressions.len() =>
            {
                for (pattern, expression) in patterns.iter().zip(expressions) {
                    self.component(pattern, expression);
                }
            }
            (PatKind::Binding(mode, binding, _, None), _)
                if mode.0 == rustc_ast::ByRef::No
                    && binding == pattern.hir_id
                    && self.candidates.contains(&(self.owner, binding))
                    && emitability::is_zero_literal(expression) =>
            {
                let typeck = self.tcx.typeck(self.owner);
                if !typeck
                    .pat_binding_modes()
                    .get(pattern.hir_id)
                    .is_some_and(|mode| mode.0 == rustc_ast::ByRef::No)
                {
                    return;
                }
                let input_type = typeck.pat_ty(pattern);
                let TyKind::RawPtr(pointee, _) = input_type.kind() else { return };
                if typeck.expr_ty(expression) != input_type
                    || !declaration::pointee_is_nameable(self.tcx, self.owner, *pointee)
                {
                    return;
                }
                let base = format!(
                    "__crat_pattern_null_{}_{}",
                    self.owner.local_def_index.as_u32(),
                    binding.local_id.as_u32()
                );
                let mut temporary = base.clone();
                let mut suffix = 0usize;
                while !self.names.insert(temporary.clone()) {
                    suffix += 1;
                    temporary = format!("{base}_{suffix}");
                }
                let node = (self.owner, binding);
                self.out.insert(
                    node,
                    PatternDeclaration {
                        node,
                        init_hir: expression.hir_id,
                        init_span: expression.span,
                        input_type: declaration::pointee_source(self.tcx, input_type),
                        pointee: declaration::pointee_source(self.tcx, *pointee),
                        temporary,
                    },
                );
            }
            // No tuple projection is inferred through calls, blocks, structs,
            // alternatives, references, rest patterns or binding subpatterns.
            _ => {}
        }
    }
}

impl<'tcx> Visitor<'tcx> for Collector<'_, 'tcx> {
    fn visit_expr(&mut self, expression: &'tcx Expr<'tcx>) {
        if let ExprKind::Let(binding) = expression.kind
            && binding.ty.is_none()
            && matches!(binding.recovered, rustc_ast::Recovered::No)
            && matches!(binding.pat.kind, PatKind::Tuple(..))
        {
            // Parentheses have already been erased by HIR lowering. Recurse
            // only through actual tuple expressions, retaining each leaf span.
            self.component(binding.pat, binding.init);
        }
        intravisit::walk_expr(self, expression);
    }
}

pub(crate) fn collect(tcx: TyCtxt<'_>, subjects: &[Subject]) -> PatternDeclarations {
    let candidates = subjects
        .iter()
        .filter(|subject| {
            matches!(subject.kind, SubjectKind::Local)
                && subject.ty_span.is_none()
                && subject.decl_shape == DeclShape::RawPtr
                && !subject.mutable
        })
        .map(|subject| (subject.fn_did, subject.hir_id))
        .collect::<FxHashSet<_>>();
    let mut owners = candidates
        .iter()
        .map(|(owner, _)| *owner)
        .collect::<Vec<_>>();
    owners.sort_by_key(|owner| owner.local_def_index.as_u32());
    owners.dedup();
    let mut out = PatternDeclarations::default();
    for owner in owners {
        let Some(body_id) = tcx.hir_node_by_def_id(owner).body_id() else { continue };
        let body = tcx.hir_body(body_id);
        let mut names = FxHashSet::default();
        BindingNames(&mut names).visit_body(body);
        Collector {
            tcx,
            owner,
            candidates: &candidates,
            names,
            out: &mut out,
        }
        .visit_body(body);
    }
    out
}

/// Apply only to the caller's stage-local clones. Disabled owners retain their
/// prior facts and flags; no analysis or frozen construction input is mutated.
pub(crate) fn augment(
    patterns: &PatternDeclarations,
    policy: &FamilyPolicy,
    constructions: &mut ConstructionFacts,
    subjects: &mut [Subject],
) {
    for subject in subjects {
        if subject.mutable || !policy.enabled(subject.fn_did, FamilyStage::Declaration) {
            continue;
        }
        let node = (subject.fn_did, subject.hir_id);
        let Some(pattern) = patterns.get(&node) else { continue };
        constructions.by_binding.insert(node, Construction::NullLit);
        constructions.init_hirs.insert(node, pattern.init_hir);
        constructions.init_spans.insert(node, pattern.init_span);
        subject.null_init = true;
        subject.ctor = Some(Construction::NullLit);
    }
}
