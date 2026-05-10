use rustc_abi::VariantIdx;
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
};

pub fn replace_enums(tcx: TyCtxt<'_>) {
    let _ = analyze_enums(tcx);
}

#[derive(Debug, Default)]
pub struct EnumAnalysis {
    pub enums: FxHashMap<LocalDefId, EnumInfo>,
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
        if let Some(ret) = self.current_ret_ty.clone() {
            self.check_expr_against_type(body.value, &ret, RequiredContext::Return);
        }

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
