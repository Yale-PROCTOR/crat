use rustc_abi::VariantIdx;
use rustc_ast::{
    self as ast,
    mut_visit::{self, MutVisitor as _},
    ptr::P,
};
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    self as hir, BinOpKind, FnRetTy, HirId, PrimTy, QPath,
    def::{DefKind, Res},
    intravisit,
};
use rustc_middle::{
    hir::nested_filter,
    mir::{ConstValue, interpret::Scalar},
    ty::{self, Ty, TyCtxt},
};
use rustc_span::{
    Span, Symbol,
    def_id::{DefId, LocalDefId},
    sym,
};
use smallvec::{SmallVec, smallvec};
use utils::ir::AstToHir;

pub fn replace_enums(tcx: TyCtxt<'_>) -> String {
    let mut krate = utils::ast::expanded_ast(tcx);
    let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
    let analysis = analyze_enums(tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

    let plan = EnumTransformPlan::new(&analysis);
    if !plan.replacements.is_empty() {
        add_coverage_feature(&mut krate, tcx);
    }
    let mut visitor = AstVisitor {
        tcx,
        ast_to_hir,
        replacements: plan.replacements,
        variant_consts: plan.variant_consts,
        cast_sites: plan.cast_sites,
        match_rewrites: plan.match_rewrites,
        inserted_casts: FxHashSet::default(),
    };
    visitor.visit_crate(&mut krate);

    pprust::crate_to_string_for_macros(&krate)
}

#[derive(Debug, Default)]
pub struct EnumAnalysis {
    pub enums: FxHashMap<LocalDefId, EnumInfo>,
    match_rewrites: Vec<MatchRewriteSite>,
}

#[derive(Debug)]
pub struct EnumInfo {
    pub alias: LocalDefId,
    pub repr: IntegerRepr,
    pub variants: Vec<VariantInfo>,
    pub transformable: bool,
    pub reject_reasons: Vec<RejectReason>,
    pub enum_to_int_cast_sites: Vec<CastSite>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntegerRepr {
    Signed(ty::IntTy),
    Unsigned(ty::UintTy),
}

#[derive(Clone, Debug)]
pub struct VariantInfo {
    pub const_def_id: LocalDefId,
    pub name: Symbol,
    pub value: DiscriminantValue,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DiscriminantValue {
    Signed(i128),
    Unsigned(u128),
}

#[derive(Clone, Debug)]
pub struct RejectReason {
    pub kind: RejectReasonKind,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RejectReasonKind {
    IntegerLiteralAssignedToEnum,
    ArithmeticAssignedToEnum,
    CastAssignedToEnum,
    UnknownExpressionAssignedToEnum,
    WrongEnumAssignedToEnum,
    FunctionArgumentRequiresEnum,
    ReturnRequiresEnum,
    DuplicateDiscriminant,
    UnevaluableDiscriminant,
    UnsupportedCastSite,
    CompoundAssignmentToEnum,
}

#[derive(Clone, Debug)]
pub struct CastSite {
    pub enum_alias: LocalDefId,
    pub hir_id: HirId,
    pub span: Span,
    pub kind: CastSiteKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CastSiteKind {
    AssignmentToInteger,
    FunctionArgumentToInteger,
    ReturnToInteger,
    NumericOperator,
    ComparisonToInteger,
}

#[derive(Clone, Debug)]
struct MatchRewriteSite {
    enum_alias: LocalDefId,
    match_hir_id: HirId,
    arms: Vec<ArmRewrite>,
}

#[derive(Clone, Debug)]
struct MatchRewrite {
    arms: FxHashMap<HirId, ArmRewriteAction>,
}

#[derive(Clone, Debug)]
struct ArmRewrite {
    arm_hir_id: HirId,
    action: ArmRewriteAction,
}

#[derive(Clone, Debug)]
enum ArmRewriteAction {
    RewritePattern(Vec<String>),
    KeepWildcard,
    RemoveWildcard,
}

#[derive(Clone, Debug)]
struct EnumReplacement {
    repr: String,
    variants: Vec<VariantReplacement>,
}

#[derive(Clone, Debug)]
struct VariantReplacement {
    name: String,
    value: String,
}

#[derive(Default)]
struct EnumTransformPlan {
    replacements: FxHashMap<LocalDefId, EnumReplacement>,
    variant_consts: FxHashMap<LocalDefId, LocalDefId>,
    cast_sites: FxHashMap<HirId, String>,
    match_rewrites: FxHashMap<HirId, MatchRewrite>,
}

impl EnumTransformPlan {
    fn new(analysis: &EnumAnalysis) -> Self {
        let mut plan = Self::default();

        for (alias, info) in &analysis.enums {
            if !info.transformable {
                continue;
            }

            let repr = repr_name(info.repr).to_string();
            let variants = info
                .variants
                .iter()
                .map(|variant| VariantReplacement {
                    name: variant.name.as_str().to_string(),
                    value: discriminant_literal(variant.value, &repr),
                })
                .collect();
            plan.replacements.insert(
                *alias,
                EnumReplacement {
                    repr: repr.clone(),
                    variants,
                },
            );

            for variant in &info.variants {
                plan.variant_consts.insert(variant.const_def_id, *alias);
            }

            for site in &info.enum_to_int_cast_sites {
                let entry = plan.cast_sites.entry(site.hir_id).or_insert(repr.clone());
                debug_assert_eq!(entry, &repr);
            }
        }

        for site in &analysis.match_rewrites {
            if !analysis
                .enums
                .get(&site.enum_alias)
                .is_some_and(|info| info.transformable)
            {
                continue;
            }

            plan.match_rewrites.insert(
                site.match_hir_id,
                MatchRewrite {
                    arms: site
                        .arms
                        .iter()
                        .map(|arm| (arm.arm_hir_id, arm.action.clone()))
                        .collect(),
                },
            );
        }

        plan
    }
}

struct AstVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    ast_to_hir: AstToHir,
    replacements: FxHashMap<LocalDefId, EnumReplacement>,
    variant_consts: FxHashMap<LocalDefId, LocalDefId>,
    cast_sites: FxHashMap<HirId, String>,
    match_rewrites: FxHashMap<HirId, MatchRewrite>,
    inserted_casts: FxHashSet<HirId>,
}

impl AstVisitor<'_> {
    fn replacement_for_ty(&self, ty: &ast::Ty) -> Option<&EnumReplacement> {
        let hir_ty = self.ast_to_hir.get_ty(ty.id, self.tcx)?;
        let hir::TyKind::Path(QPath::Resolved(_, path)) = hir_ty.kind else {
            return None;
        };
        let Res::Def(DefKind::TyAlias, def_id) = path.res else {
            return None;
        };
        self.replacements.get(&def_id.as_local()?)
    }

    fn replacement_items(
        &self,
        item: &ast::Item,
        replacement: &EnumReplacement,
    ) -> SmallVec<[P<ast::Item>; 1]> {
        let ast::ItemKind::TyAlias(box ast::TyAlias { ident, .. }) = &item.kind else { panic!() };
        let enum_name = ident.name.as_str();
        let variants = replacement
            .variants
            .iter()
            .map(|variant| format!("{} = {}", variant.name, variant.value))
            .collect::<Vec<_>>()
            .join(", ");

        let mut enum_item = P(utils::item!(
            "#[repr({})] #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)] enum {} {{ {} }}",
            replacement.repr,
            enum_name,
            variants
        ));
        enum_item.vis = item.vis.clone();

        let mut attrs = item.attrs.clone();
        attrs.extend(enum_item.attrs.drain(..));
        enum_item.attrs = attrs;

        let mut items = SmallVec::new();
        items.push(enum_item);

        for variant in &replacement.variants {
            let mut use_item = P(utils::item!("use {}::{};", enum_name, variant.name));
            use_item.vis = item.vis.clone();
            items.push(use_item);
        }

        items
    }

    fn rewrite_match_expr(&mut self, expr: &mut ast::Expr) -> bool {
        let Some(hir_expr) = self.ast_to_hir.get_expr(expr.id, self.tcx) else {
            return false;
        };
        let Some(rewrite) = self.match_rewrites.get(&hir_expr.hir_id) else {
            return false;
        };
        let ast::ExprKind::Match(scrutinee, arms, _) = &mut expr.kind else {
            return false;
        };

        let base = pprust::expr_to_string(utils::ast::unwrap_cast_and_paren(scrutinee));
        **scrutinee = utils::expr!("{base}");

        let len = arms.len();
        let mut remove_last = false;
        for (index, arm) in arms.iter_mut().enumerate() {
            let Some(hir_arm) = self.ast_to_hir.get_arm(arm.id, self.tcx) else {
                continue;
            };
            let Some(action) = rewrite.arms.get(&hir_arm.hir_id) else {
                continue;
            };
            match action {
                ArmRewriteAction::RewritePattern(paths) => {
                    let pat = paths.join(" | ");
                    arm.pat = Box::new(utils::pat!("{pat}"));
                }
                ArmRewriteAction::KeepWildcard => {}
                ArmRewriteAction::RemoveWildcard => {
                    remove_last = index + 1 == len;
                }
            }
        }

        if remove_last {
            arms.pop();
        }

        true
    }
}

impl mut_visit::MutVisitor for AstVisitor<'_> {
    fn flat_map_item(&mut self, item: P<ast::Item>) -> SmallVec<[P<ast::Item>; 1]> {
        let def_id = self.ast_to_hir.global_map.get(&item.id).copied();

        if let Some(def_id) = def_id
            && let Some(replacement) = self.replacements.get(&def_id)
        {
            return self.replacement_items(&item, replacement);
        }

        if def_id.is_some_and(|def_id| self.variant_consts.contains_key(&def_id)) {
            return smallvec![];
        }

        mut_visit::walk_flat_map_item(self, item)
    }

    fn visit_expr(&mut self, expr: &mut ast::Expr) {
        mut_visit::walk_expr(self, expr);

        if self.rewrite_match_expr(expr) {
            return;
        }

        if let ast::ExprKind::Cast(_, ty) = &mut expr.kind
            && let Some(repr) = self.replacement_for_ty(ty)
        {
            **ty = utils::ty!("{}", repr.repr);
        }

        let Some(hir_expr) = self.ast_to_hir.get_expr(expr.id, self.tcx) else {
            return;
        };
        let hir_id = hir_expr.hir_id;
        let Some(repr) = self.cast_sites.get(&hir_id) else {
            return;
        };
        if !self.inserted_casts.insert(hir_id) {
            return;
        }

        let expr_str = pprust::expr_to_string(expr);
        *expr = utils::expr!("({expr_str}) as {repr}");
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum HirEnumTy {
    Enum(LocalDefId),
    IntLike,
    Ptr(Box<HirEnumTy>),
    Ref(Box<HirEnumTy>),
    Array(Box<HirEnumTy>),
    Slice(Box<HirEnumTy>),
    Tuple(Vec<HirEnumTy>),
    FnPtr {
        params: Vec<HirEnumTy>,
        ret: Box<HirEnumTy>,
    },
    Other,
}

impl HirEnumTy {
    fn exact_enum(&self) -> Option<LocalDefId> {
        match self {
            Self::Enum(def_id) => Some(*def_id),
            _ => None,
        }
    }

    fn pointee(&self) -> Option<&HirEnumTy> {
        match self {
            Self::Ptr(ty) | Self::Ref(ty) => Some(ty),
            _ => None,
        }
    }

    fn element(&self) -> Option<&HirEnumTy> {
        match self {
            Self::Array(ty) | Self::Slice(ty) | Self::Ptr(ty) => Some(ty),
            _ => None,
        }
    }
}

#[derive(Clone, Debug)]
struct FnSigEnumTy {
    params: Vec<HirEnumTy>,
    ret: HirEnumTy,
}

#[derive(Default)]
struct CandidateData<'tcx> {
    aliases: FxHashMap<LocalDefId, IntegerRepr>,
    alias_rhs: FxHashMap<LocalDefId, &'tcx hir::Ty<'tcx>>,
}

struct CandidateVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    data: CandidateData<'tcx>,
}

impl<'tcx> intravisit::Visitor<'tcx> for CandidateVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_item(&mut self, item: &'tcx hir::Item<'tcx>) -> Self::Result {
        if let hir::ItemKind::TyAlias(_, _, ty) = item.kind {
            self.data.alias_rhs.insert(item.owner_id.def_id, ty);
            if let Some(repr) = integer_repr(
                self.tcx
                    .type_of(item.owner_id.def_id)
                    .instantiate_identity(),
            ) {
                self.data.aliases.insert(item.owner_id.def_id, repr);
            }
        }

        intravisit::walk_item(self, item)
    }
}

struct VariantCollector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    candidate_aliases: &'a FxHashSet<LocalDefId>,
    reprs: &'a FxHashMap<LocalDefId, IntegerRepr>,
    variants: FxHashMap<LocalDefId, Vec<VariantInfo>>,
    reject_reasons: FxHashMap<LocalDefId, Vec<RejectReason>>,
}

impl<'tcx> intravisit::Visitor<'tcx> for VariantCollector<'_, 'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_item(&mut self, item: &'tcx hir::Item<'tcx>) -> Self::Result {
        if let hir::ItemKind::Const(ident, _, ty, _) = item.kind
            && let Some(alias) = direct_candidate_alias(ty, self.candidate_aliases)
        {
            let repr = self.reprs[&alias];
            match eval_discriminant(self.tcx, item.owner_id.def_id, repr) {
                Some(value) => {
                    self.variants.entry(alias).or_default().push(VariantInfo {
                        const_def_id: item.owner_id.def_id,
                        name: ident.name,
                        value,
                    });
                }
                None => {
                    self.reject_reasons
                        .entry(alias)
                        .or_default()
                        .push(RejectReason {
                            kind: RejectReasonKind::UnevaluableDiscriminant,
                            span: item.span,
                        });
                }
            }
        }

        intravisit::walk_item(self, item)
    }
}

struct TypeModelBuilder<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    enum_aliases: &'a FxHashSet<LocalDefId>,
    alias_rhs: &'a FxHashMap<LocalDefId, &'tcx hir::Ty<'tcx>>,
    cache: FxHashMap<LocalDefId, HirEnumTy>,
    visiting: FxHashSet<LocalDefId>,
}

impl<'a, 'tcx> TypeModelBuilder<'a, 'tcx> {
    fn new(
        tcx: TyCtxt<'tcx>,
        enum_aliases: &'a FxHashSet<LocalDefId>,
        alias_rhs: &'a FxHashMap<LocalDefId, &'tcx hir::Ty<'tcx>>,
    ) -> Self {
        Self {
            tcx,
            enum_aliases,
            alias_rhs,
            cache: FxHashMap::default(),
            visiting: FxHashSet::default(),
        }
    }

    fn model_ty(&mut self, ty: &'tcx hir::Ty<'tcx>) -> HirEnumTy {
        match ty.kind {
            hir::TyKind::Path(QPath::Resolved(_, path)) => self.model_path(path.res),
            hir::TyKind::Ptr(mut_ty) => HirEnumTy::Ptr(Box::new(self.model_ty(mut_ty.ty))),
            hir::TyKind::Ref(_, mut_ty) => HirEnumTy::Ref(Box::new(self.model_ty(mut_ty.ty))),
            hir::TyKind::Array(ty, _) => HirEnumTy::Array(Box::new(self.model_ty(ty))),
            hir::TyKind::Slice(ty) => HirEnumTy::Slice(Box::new(self.model_ty(ty))),
            hir::TyKind::Tup(tys) => {
                HirEnumTy::Tuple(tys.iter().map(|ty| self.model_ty(ty)).collect())
            }
            hir::TyKind::BareFn(bare_fn) => {
                let params = bare_fn
                    .decl
                    .inputs
                    .iter()
                    .map(|ty| self.model_ty(ty))
                    .collect();
                let ret = Box::new(self.model_ret_ty(bare_fn.decl.output));
                HirEnumTy::FnPtr { params, ret }
            }
            _ => HirEnumTy::Other,
        }
    }

    fn model_ret_ty(&mut self, ret: FnRetTy<'tcx>) -> HirEnumTy {
        match ret {
            FnRetTy::Return(ty) => self.model_ty(ty),
            FnRetTy::DefaultReturn(_) => HirEnumTy::Other,
        }
    }

    fn model_path(&mut self, res: Res) -> HirEnumTy {
        match res {
            Res::Def(DefKind::TyAlias, def_id) => {
                if let Some(local) = def_id.as_local() {
                    if self.enum_aliases.contains(&local) {
                        return HirEnumTy::Enum(local);
                    }
                    return self.model_alias(local);
                }

                if integer_repr(self.tcx.type_of(def_id).instantiate_identity()).is_some() {
                    HirEnumTy::IntLike
                } else {
                    HirEnumTy::Other
                }
            }
            Res::PrimTy(PrimTy::Int(_)) | Res::PrimTy(PrimTy::Uint(_)) => HirEnumTy::IntLike,
            _ => HirEnumTy::Other,
        }
    }

    fn model_alias(&mut self, alias: LocalDefId) -> HirEnumTy {
        if let Some(ty) = self.cache.get(&alias) {
            return ty.clone();
        }
        if !self.visiting.insert(alias) {
            return HirEnumTy::Other;
        }

        let model = self
            .alias_rhs
            .get(&alias)
            .map(|ty| self.model_ty(ty))
            .unwrap_or(HirEnumTy::Other);

        self.visiting.remove(&alias);
        self.cache.insert(alias, model.clone());
        model
    }

    fn fn_sig(&mut self, decl: &'tcx hir::FnDecl<'tcx>) -> FnSigEnumTy {
        FnSigEnumTy {
            params: decl.inputs.iter().map(|ty| self.model_ty(ty)).collect(),
            ret: self.model_ret_ty(decl.output),
        }
    }
}

#[derive(Default)]
struct HirData {
    local_types: FxHashMap<HirId, HirEnumTy>,
    static_types: FxHashMap<LocalDefId, HirEnumTy>,
    fn_sigs: FxHashMap<DefId, FnSigEnumTy>,
    field_types: FxHashMap<DefId, HirEnumTy>,
    variant_consts: FxHashMap<LocalDefId, LocalDefId>,
}

struct DeclarationVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    model: TypeModelBuilder<'a, 'tcx>,
    data: HirData,
}

impl<'a, 'tcx> DeclarationVisitor<'a, 'tcx> {
    fn insert_pat_bindings(&mut self, pat: &'tcx hir::Pat<'tcx>, ty: &HirEnumTy) {
        if let hir::PatKind::Binding(_, hir_id, _, subpat) = pat.kind {
            self.data.local_types.insert(hir_id, ty.clone());
            if let Some(subpat) = subpat {
                self.insert_pat_bindings(subpat, ty);
            }
        } else {
            intravisit::walk_pat(self, pat);
        }
    }
}

impl<'tcx> intravisit::Visitor<'tcx> for DeclarationVisitor<'_, 'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_item(&mut self, item: &'tcx hir::Item<'tcx>) -> Self::Result {
        match item.kind {
            hir::ItemKind::Const(_, _, ty, _) => {
                if let Some(alias) = direct_candidate_alias(ty, self.model.enum_aliases) {
                    self.data.variant_consts.insert(item.owner_id.def_id, alias);
                }
            }
            hir::ItemKind::Static(_, _, ty, _) => {
                let ty = self.model.model_ty(ty);
                self.data.static_types.insert(item.owner_id.def_id, ty);
            }
            hir::ItemKind::Fn { sig, body, .. } => {
                let fn_sig = self.model.fn_sig(sig.decl);
                let body = self.tcx.hir_body(body);
                for (param, ty) in body.params.iter().zip(&fn_sig.params) {
                    self.insert_pat_bindings(param.pat, ty);
                }
                self.data
                    .fn_sigs
                    .insert(item.owner_id.def_id.to_def_id(), fn_sig);
            }
            hir::ItemKind::Struct(_, _, vd) | hir::ItemKind::Union(_, _, vd) => {
                for field in vd.fields() {
                    let ty = self.model.model_ty(field.ty);
                    self.data.field_types.insert(field.def_id.to_def_id(), ty);
                }
            }
            _ => {}
        }

        intravisit::walk_item(self, item)
    }

    fn visit_foreign_item(&mut self, item: &'tcx hir::ForeignItem<'tcx>) -> Self::Result {
        match item.kind {
            hir::ForeignItemKind::Fn(sig, _, _) => {
                let fn_sig = self.model.fn_sig(sig.decl);
                self.data
                    .fn_sigs
                    .insert(item.owner_id.def_id.to_def_id(), fn_sig);
            }
            hir::ForeignItemKind::Static(ty, _, _) => {
                let ty = self.model.model_ty(ty);
                self.data.static_types.insert(item.owner_id.def_id, ty);
            }
            _ => {}
        }

        intravisit::walk_foreign_item(self, item)
    }

    fn visit_local(&mut self, local: &'tcx hir::LetStmt<'tcx>) -> Self::Result {
        if let Some(ty) = local.ty {
            let ty = self.model.model_ty(ty);
            self.insert_pat_bindings(local.pat, &ty);
        }

        intravisit::walk_local(self, local)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ExprEnumClass {
    Enum(LocalDefId),
    PtrTo(LocalDefId),
    IntLike,
    Other,
    Unknown,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum CastedIntegerValue {
    Signed(i128),
    Unsigned(u128),
}

#[derive(Clone, Debug)]
enum NumericPatValues {
    Values(Vec<CastedIntegerValue>),
    Wildcard,
}

#[derive(Clone, Copy, Debug)]
struct EnumCastScrutinee {
    enum_alias: LocalDefId,
    target_repr: IntegerRepr,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RequiredContext {
    Let,
    Assignment,
    FunctionArgument,
    Return,
    StructField,
    Aggregate,
}

struct BodyVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    data: &'a HirData,
    analysis: &'a mut EnumAnalysis,
    current_ret_ty: Option<HirEnumTy>,
    enum_required_exprs: FxHashSet<HirId>,
    cast_sites: FxHashSet<(LocalDefId, HirId, CastSiteKind)>,
}

impl<'a, 'tcx> BodyVisitor<'a, 'tcx> {
    fn new(tcx: TyCtxt<'tcx>, data: &'a HirData, analysis: &'a mut EnumAnalysis) -> Self {
        Self {
            tcx,
            data,
            analysis,
            current_ret_ty: None,
            enum_required_exprs: FxHashSet::default(),
            cast_sites: FxHashSet::default(),
        }
    }

    fn check_expr_against_type(
        &mut self,
        expr: &'tcx hir::Expr<'tcx>,
        expected: &HirEnumTy,
        context: RequiredContext,
    ) {
        match expected {
            HirEnumTy::Enum(alias) => self.require_enum(expr, *alias, context),
            HirEnumTy::IntLike => {
                let kind = match context {
                    RequiredContext::FunctionArgument => CastSiteKind::FunctionArgumentToInteger,
                    RequiredContext::Return => CastSiteKind::ReturnToInteger,
                    _ => CastSiteKind::AssignmentToInteger,
                };
                self.record_enum_value_cast(expr, kind);
            }
            HirEnumTy::Array(elem) | HirEnumTy::Slice(elem) => {
                let expr = utils::hir::unwrap_drop_temps(expr);
                match expr.kind {
                    hir::ExprKind::Array(exprs) => {
                        for expr in exprs {
                            self.check_expr_against_type(expr, elem, RequiredContext::Aggregate);
                        }
                    }
                    hir::ExprKind::Repeat(expr, _) => {
                        self.check_expr_against_type(expr, elem, RequiredContext::Aggregate);
                    }
                    _ => {}
                }
            }
            HirEnumTy::Tuple(tys) => {
                let expr = utils::hir::unwrap_drop_temps(expr);
                if let hir::ExprKind::Tup(exprs) = expr.kind {
                    for (expr, ty) in exprs.iter().zip(tys) {
                        self.check_expr_against_type(expr, ty, RequiredContext::Aggregate);
                    }
                }
            }
            _ => {}
        }
    }

    fn require_enum(
        &mut self,
        expr: &'tcx hir::Expr<'tcx>,
        expected: LocalDefId,
        context: RequiredContext,
    ) {
        let expr = utils::hir::unwrap_drop_temps(expr);
        if let hir::ExprKind::Block(block, _) = expr.kind
            && let Some(tail) = block.expr
        {
            self.require_enum(tail, expected, context);
            return;
        }

        self.enum_required_exprs.insert(expr.hir_id);
        match self.classify_expr(expr) {
            ExprEnumClass::Enum(alias) if alias == expected => {}
            ExprEnumClass::Enum(_) => self.add_reject(
                expected,
                RejectReasonKind::WrongEnumAssignedToEnum,
                expr.span,
            ),
            _ => {
                let kind = self.reject_kind_for_expr(expr, context);
                self.add_reject(expected, kind, expr.span);
                match context {
                    RequiredContext::FunctionArgument
                        if kind != RejectReasonKind::FunctionArgumentRequiresEnum =>
                    {
                        self.add_reject(
                            expected,
                            RejectReasonKind::FunctionArgumentRequiresEnum,
                            expr.span,
                        );
                    }
                    RequiredContext::Return if kind != RejectReasonKind::ReturnRequiresEnum => {
                        self.add_reject(expected, RejectReasonKind::ReturnRequiresEnum, expr.span);
                    }
                    _ => {}
                }
            }
        }
    }

    fn reject_kind_for_expr(
        &self,
        expr: &'tcx hir::Expr<'tcx>,
        context: RequiredContext,
    ) -> RejectReasonKind {
        match utils::hir::unwrap_drop_temps(expr).kind {
            hir::ExprKind::Lit(_) => RejectReasonKind::IntegerLiteralAssignedToEnum,
            hir::ExprKind::Cast(_, _) => RejectReasonKind::CastAssignedToEnum,
            hir::ExprKind::Binary(_, _, _)
            | hir::ExprKind::Unary(_, _)
            | hir::ExprKind::AssignOp(_, _, _) => RejectReasonKind::ArithmeticAssignedToEnum,
            _ => match context {
                RequiredContext::FunctionArgument => RejectReasonKind::FunctionArgumentRequiresEnum,
                RequiredContext::Return => RejectReasonKind::ReturnRequiresEnum,
                _ => RejectReasonKind::UnknownExpressionAssignedToEnum,
            },
        }
    }

    fn add_reject(&mut self, alias: LocalDefId, kind: RejectReasonKind, span: Span) {
        let info = self.analysis.enums.get_mut(&alias).unwrap();
        info.transformable = false;
        info.reject_reasons.push(RejectReason { kind, span });
    }

    fn add_cast_site(
        &mut self,
        alias: LocalDefId,
        expr: &'tcx hir::Expr<'tcx>,
        kind: CastSiteKind,
    ) {
        if !self.cast_sites.insert((alias, expr.hir_id, kind)) {
            return;
        }
        let info = self.analysis.enums.get_mut(&alias).unwrap();
        info.enum_to_int_cast_sites.push(CastSite {
            enum_alias: alias,
            hir_id: expr.hir_id,
            span: expr.span,
            kind,
        });
    }

    fn record_enum_value_cast(&mut self, expr: &'tcx hir::Expr<'tcx>, kind: CastSiteKind) {
        let expr = utils::hir::unwrap_drop_temps(expr);
        if let ExprEnumClass::Enum(alias) = self.classify_expr(expr) {
            self.add_cast_site(alias, expr, kind);
        }
    }

    fn record_numeric_operand_casts(
        &mut self,
        lhs: &'tcx hir::Expr<'tcx>,
        rhs: Option<&'tcx hir::Expr<'tcx>>,
        kind: CastSiteKind,
    ) {
        self.record_enum_value_cast(lhs, kind);
        if let Some(rhs) = rhs {
            self.record_enum_value_cast(rhs, kind);
        }
    }

    fn enum_cast_scrutinee(&self, scrutinee: &'tcx hir::Expr<'tcx>) -> Option<EnumCastScrutinee> {
        let typeck = self.tcx.typeck(scrutinee.hir_id.owner.def_id);
        let target_repr = integer_repr(typeck.expr_ty(scrutinee))?;

        let mut base = utils::hir::unwrap_drop_temps(scrutinee);
        let mut saw_cast = false;
        loop {
            match base.kind {
                hir::ExprKind::Use(expr, _) => {
                    base = utils::hir::unwrap_drop_temps(expr);
                }
                hir::ExprKind::Cast(expr, _) => {
                    saw_cast = true;
                    base = utils::hir::unwrap_drop_temps(expr);
                }
                _ => break,
            }
        }
        if !saw_cast {
            return None;
        }

        let ExprEnumClass::Enum(enum_alias) = self.classify_expr(base) else {
            return None;
        };
        self.analysis
            .enums
            .get(&enum_alias)
            .is_some_and(|info| info.transformable)
            .then_some(EnumCastScrutinee {
                enum_alias,
                target_repr,
            })
    }

    fn casted_variant_paths(
        &self,
        info: &EnumInfo,
        target_repr: IntegerRepr,
    ) -> Option<FxHashMap<CastedIntegerValue, String>> {
        let mut paths = FxHashMap::default();
        for variant in &info.variants {
            let value = cast_discriminant_value(variant.value, info.repr, target_repr, self.tcx)?;
            let path = format!(
                "crate::{}::{}",
                self.tcx.def_path_str(info.alias.to_def_id()),
                variant.name
            );
            if paths.insert(value, path).is_some() {
                return None;
            }
        }
        Some(paths)
    }

    fn try_record_match_rewrite(
        &mut self,
        expr: &'tcx hir::Expr<'tcx>,
        scrutinee: &'tcx hir::Expr<'tcx>,
        arms: &'tcx [hir::Arm<'tcx>],
    ) {
        let Some(scrutinee) = self.enum_cast_scrutinee(scrutinee) else {
            return;
        };
        let Some(info) = self.analysis.enums.get(&scrutinee.enum_alias) else {
            return;
        };
        let Some(variant_paths) = self.casted_variant_paths(info, scrutinee.target_repr) else {
            return;
        };

        let mut rewrites = Vec::new();
        let mut covered_variants = FxHashSet::default();
        let mut has_guard = false;
        for arm in arms {
            has_guard |= arm.guard.is_some();
            match numeric_pat_values(arm.pat, scrutinee.target_repr, self.tcx) {
                Some(NumericPatValues::Values(values)) => {
                    let mut paths = Vec::with_capacity(values.len());
                    for value in values {
                        let Some(path) = variant_paths.get(&value) else {
                            return;
                        };
                        paths.push(path.clone());
                        if arm.guard.is_none() {
                            covered_variants.insert(value);
                        }
                    }
                    rewrites.push(ArmRewrite {
                        arm_hir_id: arm.hir_id,
                        action: ArmRewriteAction::RewritePattern(paths),
                    });
                }
                Some(NumericPatValues::Wildcard) => {
                    rewrites.push(ArmRewrite {
                        arm_hir_id: arm.hir_id,
                        action: ArmRewriteAction::KeepWildcard,
                    });
                }
                None => return,
            }
        }

        let remove_final_wildcard = !has_guard
            && covered_variants.len() == variant_paths.len()
            && arms.last().is_some_and(|arm| arm.guard.is_none())
            && rewrites
                .last()
                .is_some_and(|arm| matches!(&arm.action, ArmRewriteAction::KeepWildcard));
        if remove_final_wildcard && let Some(last) = rewrites.last_mut() {
            last.action = ArmRewriteAction::RemoveWildcard;
        }

        self.analysis.match_rewrites.push(MatchRewriteSite {
            enum_alias: scrutinee.enum_alias,
            match_hir_id: expr.hir_id,
            arms: rewrites,
        });
    }

    fn classify_expr(&self, expr: &'tcx hir::Expr<'tcx>) -> ExprEnumClass {
        let expr = utils::hir::unwrap_drop_temps(expr);
        match expr.kind {
            hir::ExprKind::Use(expr, _) => self.classify_expr(expr),
            hir::ExprKind::Path(QPath::Resolved(_, path)) => self.classify_path(path.res),
            hir::ExprKind::Field(base, field) => self
                .field_type(base, field.name)
                .map_or(ExprEnumClass::Unknown, Self::classify_decl_ty),
            hir::ExprKind::Index(base, _, _) => self
                .expr_decl_ty(base)
                .and_then(|ty| ty.element())
                .map_or(ExprEnumClass::Unknown, Self::classify_decl_ty),
            hir::ExprKind::Unary(hir::UnOp::Deref, expr) => self
                .expr_decl_ty(expr)
                .and_then(|ty| ty.pointee())
                .map_or_else(
                    || match self.classify_expr(expr) {
                        ExprEnumClass::PtrTo(alias) => ExprEnumClass::Enum(alias),
                        _ => ExprEnumClass::Unknown,
                    },
                    Self::classify_decl_ty,
                ),
            hir::ExprKind::Call(callee, _) => self
                .callee_sig(callee)
                .map_or(ExprEnumClass::Unknown, |sig| {
                    Self::classify_decl_ty(&sig.ret)
                }),
            hir::ExprKind::Block(block, _) => block
                .expr
                .map_or(ExprEnumClass::Other, |expr| self.classify_expr(expr)),
            hir::ExprKind::If(_, then_expr, Some(else_expr)) => {
                let then_class = self.classify_expr(then_expr);
                let else_class = self.classify_expr(else_expr);
                if then_class == else_class {
                    then_class
                } else {
                    ExprEnumClass::Unknown
                }
            }
            hir::ExprKind::Match(_, arms, _) => {
                let mut class = None;
                for arm in arms {
                    let arm_class = self.classify_expr(arm.body);
                    if class.is_some_and(|class| class != arm_class) {
                        return ExprEnumClass::Unknown;
                    }
                    class = Some(arm_class);
                }
                class.unwrap_or(ExprEnumClass::Other)
            }
            hir::ExprKind::Lit(_) | hir::ExprKind::Cast(_, _) => ExprEnumClass::IntLike,
            hir::ExprKind::Binary(_, _, _) | hir::ExprKind::Unary(_, _) => ExprEnumClass::IntLike,
            _ => ExprEnumClass::Unknown,
        }
    }

    fn classify_path(&self, res: Res) -> ExprEnumClass {
        match res {
            Res::Def(DefKind::Const, def_id) => def_id
                .as_local()
                .and_then(|def_id| self.data.variant_consts.get(&def_id).copied())
                .map_or(ExprEnumClass::Unknown, ExprEnumClass::Enum),
            Res::Def(DefKind::Static { .. }, def_id) => def_id
                .as_local()
                .and_then(|def_id| self.data.static_types.get(&def_id))
                .map_or(ExprEnumClass::Unknown, Self::classify_decl_ty),
            Res::Local(hir_id) => self
                .data
                .local_types
                .get(&hir_id)
                .map_or(ExprEnumClass::Unknown, Self::classify_decl_ty),
            _ => ExprEnumClass::Unknown,
        }
    }

    fn classify_decl_ty(ty: &HirEnumTy) -> ExprEnumClass {
        match ty {
            HirEnumTy::Enum(alias) => ExprEnumClass::Enum(*alias),
            HirEnumTy::Ptr(inner) | HirEnumTy::Ref(inner) => {
                if let HirEnumTy::Enum(alias) = **inner {
                    ExprEnumClass::PtrTo(alias)
                } else {
                    ExprEnumClass::Other
                }
            }
            HirEnumTy::IntLike => ExprEnumClass::IntLike,
            _ => ExprEnumClass::Other,
        }
    }

    fn expr_decl_ty(&self, expr: &'tcx hir::Expr<'tcx>) -> Option<&HirEnumTy> {
        let expr = utils::hir::unwrap_drop_temps(expr);
        match expr.kind {
            hir::ExprKind::Use(expr, _) => self.expr_decl_ty(expr),
            hir::ExprKind::Path(QPath::Resolved(_, path)) => match path.res {
                Res::Local(hir_id) => self.data.local_types.get(&hir_id),
                Res::Def(DefKind::Static { .. }, def_id) => def_id
                    .as_local()
                    .and_then(|def_id| self.data.static_types.get(&def_id)),
                Res::Def(DefKind::Const, _) => None,
                _ => None,
            },
            hir::ExprKind::Field(base, field) => self.field_type(base, field.name),
            _ => None,
        }
    }

    fn field_type(&self, base: &'tcx hir::Expr<'tcx>, field: Symbol) -> Option<&HirEnumTy> {
        let typeck = self.tcx.typeck(base.hir_id.owner.def_id);
        let ty = typeck.expr_ty(base);
        let ty::TyKind::Adt(adt_def, _) = ty.kind() else { return None };
        let field = adt_def
            .variant(VariantIdx::from_u32(0))
            .fields
            .iter()
            .find(|field_def| field_def.name == field)?;
        self.data.field_types.get(&field.did)
    }

    fn callee_sig(&self, callee: &'tcx hir::Expr<'tcx>) -> Option<&FnSigEnumTy> {
        let callee = utils::hir::unwrap_drop_temps(callee);
        match callee.kind {
            hir::ExprKind::Path(QPath::Resolved(_, path)) => {
                let Res::Def(_, def_id) = path.res else { return None };
                self.data.fn_sigs.get(&def_id)
            }
            hir::ExprKind::Use(expr, _) => self.callee_sig(expr),
            _ => {
                if let Some(HirEnumTy::FnPtr { params, ret }) = self.expr_decl_ty(callee) {
                    // Function pointer calls are rare in the first enum pass. Keep enough
                    // information to classify direct uses without manufacturing an owned sig.
                    let _ = (params, ret);
                }
                None
            }
        }
    }

    fn check_call_args(&mut self, callee: &'tcx hir::Expr<'tcx>, args: &'tcx [hir::Expr<'tcx>]) {
        let Some(sig) = self.callee_sig(callee).cloned() else { return };
        for (arg, param_ty) in args.iter().zip(&sig.params) {
            self.check_expr_against_type(arg, param_ty, RequiredContext::FunctionArgument);
        }
    }

    fn check_struct_fields(
        &mut self,
        expr: &'tcx hir::Expr<'tcx>,
        fields: &'tcx [hir::ExprField<'tcx>],
    ) {
        let typeck = self.tcx.typeck(expr.hir_id.owner.def_id);
        let ty = typeck.expr_ty(expr);
        let ty::TyKind::Adt(adt_def, _) = ty.kind() else { return };
        let variant = adt_def.variant(VariantIdx::from_u32(0));
        for field in fields {
            let Some(field_def) = variant
                .fields
                .iter()
                .find(|field_def| field_def.name == field.ident.name)
            else {
                continue;
            };
            if let Some(ty) = self.data.field_types.get(&field_def.did).cloned() {
                self.check_expr_against_type(field.expr, &ty, RequiredContext::StructField);
            }
        }
    }

    fn handle_binary(
        &mut self,
        expr: &'tcx hir::Expr<'tcx>,
        op: BinOpKind,
        lhs: &'tcx hir::Expr<'tcx>,
        rhs: &'tcx hir::Expr<'tcx>,
    ) {
        if self.enum_required_exprs.contains(&expr.hir_id) {
            return;
        }

        let lhs_class = self.classify_expr(lhs);
        let rhs_class = self.classify_expr(rhs);
        if is_comparison(op) {
            if matches!(
                (lhs_class, rhs_class),
                (ExprEnumClass::Enum(l), ExprEnumClass::Enum(r)) if l == r
            ) {
                return;
            }
            self.record_numeric_operand_casts(lhs, Some(rhs), CastSiteKind::ComparisonToInteger);
        } else if is_numeric_binop(op) {
            self.record_numeric_operand_casts(lhs, Some(rhs), CastSiteKind::NumericOperator);
        }
    }
}

impl<'tcx> intravisit::Visitor<'tcx> for BodyVisitor<'_, 'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_item(&mut self, item: &'tcx hir::Item<'tcx>) -> Self::Result {
        match item.kind {
            hir::ItemKind::Fn { body, .. } => {
                let old_ret = self.current_ret_ty.clone();
                self.current_ret_ty = self
                    .data
                    .fn_sigs
                    .get(&item.owner_id.def_id.to_def_id())
                    .map(|sig| sig.ret.clone());
                self.visit_body(self.tcx.hir_body(body));
                self.current_ret_ty = old_ret;
            }
            hir::ItemKind::Static(_, _, _, body_id) => {
                if let Some(ty) = self.data.static_types.get(&item.owner_id.def_id).cloned() {
                    let body = self.tcx.hir_body(body_id);
                    self.check_expr_against_type(body.value, &ty, RequiredContext::Assignment);
                    self.visit_body(body);
                }
            }
            hir::ItemKind::Const(..) => {}
            _ => intravisit::walk_item(self, item),
        }
    }

    fn visit_body(&mut self, body: &hir::Body<'tcx>) -> Self::Result {
        intravisit::walk_body(self, body)
    }

    fn visit_local(&mut self, local: &'tcx hir::LetStmt<'tcx>) -> Self::Result {
        if let Some(ty) = local
            .ty
            .and_then(|_| self.data.local_types.get(&local.pat.hir_id).cloned())
            && let Some(init) = local.init
        {
            self.check_expr_against_type(init, &ty, RequiredContext::Let);
        }

        intravisit::walk_local(self, local)
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) -> Self::Result {
        match expr.kind {
            hir::ExprKind::Assign(lhs, rhs, _) => {
                if let Some(ty) = self.expr_decl_ty(lhs).cloned() {
                    self.check_expr_against_type(rhs, &ty, RequiredContext::Assignment);
                }
            }
            hir::ExprKind::AssignOp(_, lhs, _) => {
                if let Some(alias) = self.expr_decl_ty(lhs).and_then(HirEnumTy::exact_enum) {
                    self.add_reject(alias, RejectReasonKind::CompoundAssignmentToEnum, expr.span);
                }
            }
            hir::ExprKind::Ret(Some(ret)) => {
                if let Some(ty) = self.current_ret_ty.clone() {
                    self.check_expr_against_type(ret, &ty, RequiredContext::Return);
                }
            }
            hir::ExprKind::Call(callee, args) => {
                self.check_call_args(callee, args);
            }
            hir::ExprKind::MethodCall(_, _receiver, args, _) => {
                if let Some(def_id) = self
                    .tcx
                    .typeck(expr.hir_id.owner.def_id)
                    .type_dependent_def_id(expr.hir_id)
                    && let Some(sig) = self.data.fn_sigs.get(&def_id).cloned()
                {
                    for (arg, param_ty) in args.iter().zip(sig.params.iter().skip(1)) {
                        self.check_expr_against_type(
                            arg,
                            param_ty,
                            RequiredContext::FunctionArgument,
                        );
                    }
                }
            }
            hir::ExprKind::Struct(_, fields, _) => {
                self.check_struct_fields(expr, fields);
            }
            hir::ExprKind::Match(scrutinee, arms, hir::MatchSource::Normal) => {
                self.try_record_match_rewrite(expr, scrutinee, arms);
            }
            hir::ExprKind::Binary(op, lhs, rhs) => {
                self.handle_binary(expr, op.node, lhs, rhs);
            }
            hir::ExprKind::Unary(op, operand) => {
                if matches!(op, hir::UnOp::Neg | hir::UnOp::Not) {
                    self.record_numeric_operand_casts(operand, None, CastSiteKind::NumericOperator);
                }
            }
            _ => {}
        }

        intravisit::walk_expr(self, expr)
    }
}

fn analyze_enums(tcx: TyCtxt<'_>) -> EnumAnalysis {
    let mut candidates = CandidateVisitor {
        tcx,
        data: CandidateData::default(),
    };
    tcx.hir_visit_all_item_likes_in_crate(&mut candidates);

    let candidate_aliases = candidates.data.aliases.keys().copied().collect();
    let mut variant_collector = VariantCollector {
        tcx,
        candidate_aliases: &candidate_aliases,
        reprs: &candidates.data.aliases,
        variants: FxHashMap::default(),
        reject_reasons: FxHashMap::default(),
    };
    tcx.hir_visit_all_item_likes_in_crate(&mut variant_collector);

    let enum_aliases: FxHashSet<_> = variant_collector.variants.keys().copied().collect();
    let mut analysis = EnumAnalysis::default();
    for (alias, mut variants) in variant_collector.variants {
        variants.sort_by(|l, r| l.value.cmp(&r.value));

        let mut seen = FxHashSet::default();
        let mut reasons = variant_collector
            .reject_reasons
            .remove(&alias)
            .unwrap_or_default();
        for variant in &variants {
            if !seen.insert(variant.value) {
                reasons.push(RejectReason {
                    kind: RejectReasonKind::DuplicateDiscriminant,
                    span: tcx.def_span(variant.const_def_id),
                });
            }
        }

        analysis.enums.insert(
            alias,
            EnumInfo {
                alias,
                repr: candidates.data.aliases[&alias],
                variants,
                transformable: reasons.is_empty(),
                reject_reasons: reasons,
                enum_to_int_cast_sites: vec![],
            },
        );
    }

    if analysis.enums.is_empty() {
        return analysis;
    }

    let mut declarations = DeclarationVisitor {
        tcx,
        model: TypeModelBuilder::new(tcx, &enum_aliases, &candidates.data.alias_rhs),
        data: HirData::default(),
    };
    tcx.hir_visit_all_item_likes_in_crate(&mut declarations);

    let mut bodies = BodyVisitor::new(tcx, &declarations.data, &mut analysis);
    tcx.hir_visit_all_item_likes_in_crate(&mut bodies);

    analysis
}

fn direct_candidate_alias(
    ty: &hir::Ty<'_>,
    candidate_aliases: &FxHashSet<LocalDefId>,
) -> Option<LocalDefId> {
    let hir::TyKind::Path(QPath::Resolved(_, path)) = ty.kind else {
        return None;
    };
    let Res::Def(DefKind::TyAlias, def_id) = path.res else {
        return None;
    };
    let def_id = def_id.as_local()?;
    candidate_aliases.contains(&def_id).then_some(def_id)
}

fn integer_repr(ty: Ty<'_>) -> Option<IntegerRepr> {
    match ty.kind() {
        ty::TyKind::Int(int_ty) => Some(IntegerRepr::Signed(*int_ty)),
        ty::TyKind::Uint(uint_ty) => Some(IntegerRepr::Unsigned(*uint_ty)),
        _ => None,
    }
}

fn numeric_pat_values(
    pat: &hir::Pat<'_>,
    target_repr: IntegerRepr,
    tcx: TyCtxt<'_>,
) -> Option<NumericPatValues> {
    match pat.kind {
        hir::PatKind::Expr(expr) => Some(NumericPatValues::Values(vec![numeric_pat_expr_value(
            expr,
            target_repr,
            tcx,
        )?])),
        hir::PatKind::Or(pats) => {
            let mut values = Vec::new();
            for pat in pats {
                match numeric_pat_values(pat, target_repr, tcx)? {
                    NumericPatValues::Values(pat_values) => values.extend(pat_values),
                    NumericPatValues::Wildcard => return None,
                }
            }
            Some(NumericPatValues::Values(values))
        }
        hir::PatKind::Wild => Some(NumericPatValues::Wildcard),
        _ => None,
    }
}

fn numeric_pat_expr_value(
    expr: &hir::PatExpr<'_>,
    target_repr: IntegerRepr,
    tcx: TyCtxt<'_>,
) -> Option<CastedIntegerValue> {
    let hir::PatExprKind::Lit { lit, negated } = expr.kind else {
        return None;
    };
    let ast::LitKind::Int(value, _) = lit.node else {
        return None;
    };
    cast_literal_value(value.get(), negated, target_repr, tcx)
}

fn cast_literal_value(
    value: u128,
    negated: bool,
    target_repr: IntegerRepr,
    tcx: TyCtxt<'_>,
) -> Option<CastedIntegerValue> {
    let width = integer_width(target_repr, tcx);
    match target_repr {
        IntegerRepr::Signed(_) => {
            let sign_bit = 1u128 << (width - 1);
            let max = sign_bit - 1;
            let value = if negated {
                if value > sign_bit {
                    return None;
                }
                if value == sign_bit && width == 128 {
                    i128::MIN
                } else {
                    -(value as i128)
                }
            } else {
                if value > max {
                    return None;
                }
                value as i128
            };
            Some(CastedIntegerValue::Signed(value))
        }
        IntegerRepr::Unsigned(_) => {
            if negated || value > low_bits_mask(width) {
                return None;
            }
            Some(CastedIntegerValue::Unsigned(value))
        }
    }
}

fn cast_discriminant_value(
    value: DiscriminantValue,
    _source_repr: IntegerRepr,
    target_repr: IntegerRepr,
    tcx: TyCtxt<'_>,
) -> Option<CastedIntegerValue> {
    let width = integer_width(target_repr, tcx);
    let bits = match value {
        DiscriminantValue::Signed(value) => value as u128,
        DiscriminantValue::Unsigned(value) => value,
    } & low_bits_mask(width);
    Some(match target_repr {
        IntegerRepr::Signed(_) => CastedIntegerValue::Signed(signed_value_from_bits(bits, width)),
        IntegerRepr::Unsigned(_) => CastedIntegerValue::Unsigned(bits),
    })
}

fn integer_width(repr: IntegerRepr, tcx: TyCtxt<'_>) -> u32 {
    match repr {
        IntegerRepr::Signed(int_ty) => match int_ty {
            ty::IntTy::Isize => tcx.data_layout.pointer_size.bits() as u32,
            ty::IntTy::I8 => 8,
            ty::IntTy::I16 => 16,
            ty::IntTy::I32 => 32,
            ty::IntTy::I64 => 64,
            ty::IntTy::I128 => 128,
        },
        IntegerRepr::Unsigned(uint_ty) => match uint_ty {
            ty::UintTy::Usize => tcx.data_layout.pointer_size.bits() as u32,
            ty::UintTy::U8 => 8,
            ty::UintTy::U16 => 16,
            ty::UintTy::U32 => 32,
            ty::UintTy::U64 => 64,
            ty::UintTy::U128 => 128,
        },
    }
}

fn low_bits_mask(width: u32) -> u128 {
    if width == 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

fn signed_value_from_bits(bits: u128, width: u32) -> i128 {
    if width == 128 {
        bits as i128
    } else {
        let sign_bit = 1u128 << (width - 1);
        if bits & sign_bit == 0 {
            bits as i128
        } else {
            (bits as i128) - (1i128 << width)
        }
    }
}

fn repr_name(repr: IntegerRepr) -> &'static str {
    match repr {
        IntegerRepr::Signed(int_ty) => match int_ty {
            ty::IntTy::Isize => "isize",
            ty::IntTy::I8 => "i8",
            ty::IntTy::I16 => "i16",
            ty::IntTy::I32 => "i32",
            ty::IntTy::I64 => "i64",
            ty::IntTy::I128 => "i128",
        },
        IntegerRepr::Unsigned(uint_ty) => match uint_ty {
            ty::UintTy::Usize => "usize",
            ty::UintTy::U8 => "u8",
            ty::UintTy::U16 => "u16",
            ty::UintTy::U32 => "u32",
            ty::UintTy::U64 => "u64",
            ty::UintTy::U128 => "u128",
        },
    }
}

fn discriminant_literal(value: DiscriminantValue, repr: &str) -> String {
    match value {
        DiscriminantValue::Signed(value) => format!("{value}{repr}"),
        DiscriminantValue::Unsigned(value) => format!("{value}{repr}"),
    }
}

fn add_coverage_feature(krate: &mut ast::Crate, tcx: TyCtxt<'_>) {
    if krate.attrs.iter().any(|attr| {
        let ast::AttrKind::Normal(normal) = &attr.kind else {
            return false;
        };
        attr.has_name(sym::feature)
            && utils::ast::get_attr_arg(&normal.item.args)
                .is_some_and(|arg| arg.as_str() == "coverage_attribute")
    }) {
        return;
    }

    krate.attrs.push(utils::ast::make_inner_attribute(
        sym::feature,
        Symbol::intern("coverage_attribute"),
        tcx,
    ));
}

fn eval_discriminant(
    tcx: TyCtxt<'_>,
    const_def_id: LocalDefId,
    repr: IntegerRepr,
) -> Option<DiscriminantValue> {
    let value = tcx.const_eval_poly(const_def_id.to_def_id()).ok()?;
    let ConstValue::Scalar(Scalar::Int(int)) = value else {
        return None;
    };
    Some(match repr {
        IntegerRepr::Signed(int_ty) => {
            let value = match int_ty {
                ty::IntTy::Isize => int.to_i64() as i128,
                ty::IntTy::I8 => int.to_i8() as i128,
                ty::IntTy::I16 => int.to_i16() as i128,
                ty::IntTy::I32 => int.to_i32() as i128,
                ty::IntTy::I64 => int.to_i64() as i128,
                ty::IntTy::I128 => int.to_i128(),
            };
            DiscriminantValue::Signed(value)
        }
        IntegerRepr::Unsigned(uint_ty) => {
            let value = match uint_ty {
                ty::UintTy::Usize => int.to_u64() as u128,
                ty::UintTy::U8 => int.to_u8() as u128,
                ty::UintTy::U16 => int.to_u16() as u128,
                ty::UintTy::U32 => int.to_u32() as u128,
                ty::UintTy::U64 => int.to_u64() as u128,
                ty::UintTy::U128 => int.to_u128(),
            };
            DiscriminantValue::Unsigned(value)
        }
    })
}

fn is_numeric_binop(op: BinOpKind) -> bool {
    matches!(
        op,
        BinOpKind::Add
            | BinOpKind::Sub
            | BinOpKind::Mul
            | BinOpKind::Div
            | BinOpKind::Rem
            | BinOpKind::BitAnd
            | BinOpKind::BitOr
            | BinOpKind::BitXor
            | BinOpKind::Shl
            | BinOpKind::Shr
    )
}

fn is_comparison(op: BinOpKind) -> bool {
    matches!(
        op,
        BinOpKind::Eq
            | BinOpKind::Ne
            | BinOpKind::Lt
            | BinOpKind::Le
            | BinOpKind::Gt
            | BinOpKind::Ge
    )
}

#[cfg(test)]
mod tests;
