use rustc_ast::*;
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    def::Res,
    def_id::{LocalDefId, LocalModDefId},
    intravisit, {self as hir},
};
use rustc_middle::{
    hir::nested_filter,
    mir::Location,
    thir,
    ty::{self, TyCtxt},
};
use rustc_span::Symbol;
use utils::{
    ast::unwrap_cast_and_paren_mut,
    ir::{AstToHir, HirToThir, ThirToMir},
};

use crate::rustc_ast::mut_visit::MutVisitor as _;

mod unused_assignments;

pub fn simplify(tcx: TyCtxt<'_>) -> String {
    let mut expanded_ast = utils::ast::expanded_ast(tcx);
    let ast_to_hir = utils::ast::make_ast_to_hir(&mut expanded_ast, tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut expanded_ast);

    let mut hir_visitor = HirVisitor {
        tcx,
        imports: FxHashMap::default(),
    };
    tcx.hir_visit_all_item_likes_in_crate(&mut hir_visitor);

    let hir_to_thir = utils::ir::map_hir_to_thir(tcx);
    let unused_assignments = unused_assignments::find_unused_assignments(tcx);

    let mut visitor = AstVisitor {
        tcx,
        ast_to_hir,
        hir_to_thir,
        thir_to_mir: unused_assignments.thir_to_mir,
        imports: hir_visitor.imports,
        dead_assignments: unused_assignments.dead_assignments,
    };

    visitor.visit_crate(&mut expanded_ast);
    pprust::crate_to_string_for_macros(&expanded_ast)
}

struct AstVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    ast_to_hir: AstToHir,
    hir_to_thir: HirToThir,
    thir_to_mir: FxHashMap<LocalDefId, ThirToMir>,
    imports: FxHashMap<LocalModDefId, FxHashSet<LocalDefId>>,
    dead_assignments: FxHashSet<(LocalDefId, Location)>,
}

impl mut_visit::MutVisitor for AstVisitor<'_> {
    fn flat_map_stmt(&mut self, s: Stmt) -> smallvec::SmallVec<[Stmt; 1]> {
        let mut stmts = mut_visit::walk_flat_map_stmt(self, s);
        stmts.retain(|stmt| {
            if let StmtKind::Semi(e) = &stmt.kind
                && let ExprKind::Assign(_, r, _) | ExprKind::AssignOp(_, _, r) = &e.kind
                && !utils::ast::has_side_effects(r)
                && let Some(hir_stmt) = self.ast_to_hir.get_stmt(stmt.id, self.tcx)
                && let hir::StmtKind::Semi(e) = hir_stmt.kind
                && matches!(
                    e.kind,
                    hir::ExprKind::Assign(_, _, _) | hir::ExprKind::AssignOp(_, _, _)
                )
                && let Some(loc) = self.hir_expr_to_loc(e)
            {
                !self
                    .dead_assignments
                    .contains(&(e.hir_id.owner.def_id, loc))
            } else {
                true
            }
        });
        stmts
    }

    fn visit_local(&mut self, local: &mut Local) {
        mut_visit::walk_local(self, local);

        if let LocalKind::Init(init) = &local.kind
            && !utils::ast::has_side_effects(init)
            && let Some(hir_let_stmt) = self.ast_to_hir.get_let_stmt(local.id, self.tcx)
            && let hir::PatKind::Binding(_, hir_id, _, _) = hir_let_stmt.pat.kind
            && let Some(init) = hir_let_stmt.init
            && let Some(loc) = self.hir_expr_to_loc(init)
            && self
                .dead_assignments
                .contains(&(hir_let_stmt.hir_id.owner.def_id, loc))
        {
            let typeck = self.tcx.typeck(hir_let_stmt.hir_id.owner);
            let ty = typeck.node_type(hir_id);
            local.kind = LocalKind::Decl;
            if local.ty.is_none() {
                let ty = utils::ir::mir_ty_to_string(ty, self.tcx);
                local.ty = Some(ptr::P(utils::ty!("{ty}")));
            }
        }
    }

    fn visit_expr(&mut self, expr: &mut Expr) {
        if matches!(expr.kind, ExprKind::Cast(_, _)) {
            let hir_expr = self.ast_to_hir.get_expr(expr.id, self.tcx).unwrap();
            if let Some(v) = self.eval_lit_cast(hir_expr) {
                let annotation = if self.need_annotation(hir_expr) {
                    let typeck = self.tcx.typeck(hir_expr.hir_id.owner);
                    let ty = typeck.expr_ty(hir_expr);
                    format!("{ty}")
                } else {
                    "".to_string()
                };

                let lit = find_lit(expr);
                let new_expr = if v.is_negative() {
                    utils::expr!("{v}{annotation}")
                } else {
                    match lit.as_str().as_bytes() {
                        [b'0', b'x', ..] => utils::expr!("{v:#x}{annotation}"),
                        [b'0', b'o', ..] => utils::expr!("{v:#o}{annotation}"),
                        [b'0', b'b', ..] => utils::expr!("{v:#b}{annotation}"),
                        _ => utils::expr!("{v}{annotation}"),
                    }
                };
                *expr = new_expr;
                return;
            } else if let Some(tys) = self.compress_casts(hir_expr) {
                let e = unwrap_cast_and_paren_mut(expr);
                mut_visit::walk_expr(self, e);
                self.visit_post(e);
                let mut e_str = pprust::expr_to_string(e);
                if !is_atomic(e) {
                    e_str = format!("({e_str})");
                }
                for ty in &tys[1..] {
                    use std::fmt::Write;
                    write!(e_str, " as {ty}").unwrap();
                }
                *expr = utils::expr!("{e_str}");
                return;
            }
        }

        mut_visit::walk_expr(self, expr);

        self.visit_post(expr);
    }

    fn visit_ty(&mut self, ty: &mut Ty) {
        mut_visit::walk_ty(self, ty);

        if let Some(hir_ty) = self.ast_to_hir.get_ty(ty.id, self.tcx)
            && let hir::TyKind::Path(hir::QPath::Resolved(_, path)) = &hir_ty.kind
            && let Res::Def(_, def_id) = path.res
            && let Some(local_def_id) = def_id.as_local()
            && let mod_id = self.tcx.parent_module(hir_ty.hir_id)
            && (mod_id == self.tcx.parent_module_from_def_id(local_def_id)
                || self
                    .imports
                    .get(&mod_id)
                    .is_some_and(|s| s.contains(&local_def_id)))
        {
            *ty = utils::ty!("{}", self.tcx.item_name(def_id));
        }
    }
}

impl<'tcx> AstVisitor<'tcx> {
    fn hir_expr_to_loc(&self, expr: &hir::Expr<'tcx>) -> Option<Location> {
        let expr = utils::hir::unwrap_drop_temps(expr);
        let (thir, _) = self.tcx.thir_body(expr.hir_id.owner).unwrap();
        let thir = thir.borrow();
        if let Some(expr_id) = self.hir_to_thir.exprs.get(&expr.hir_id)
            && let expr_id = thir_unwrap_use(*expr_id, &thir)
            && let Some(thir_to_mir) = self.thir_to_mir.get(&expr.hir_id.owner.def_id)
            && let Some(locs) = thir_to_mir.expr_to_locs.get(&expr_id)
        {
            locs.first().copied()
        } else {
            None
        }
    }

    fn visit_post(&self, expr: &mut Expr) {
        let id = expr.id;
        match &mut expr.kind {
            ExprKind::Paren(e) => {
                if is_atomic(e) {
                    *expr = utils::ast::take_expr(e);
                }
            }
            ExprKind::Binary(op, l, r) => {
                if is_zero(l)
                    && matches!(
                        op.node,
                        BinOpKind::Mul
                            | BinOpKind::Div
                            | BinOpKind::Rem
                            | BinOpKind::BitAnd
                            | BinOpKind::Shl
                            | BinOpKind::Shr
                    )
                    || is_zero(r) && matches!(op.node, BinOpKind::Mul | BinOpKind::BitAnd)
                {
                    // avoid clippy::erasing_op
                    *expr = utils::expr!("0");
                } else if matches!(op.node, BinOpKind::Le | BinOpKind::Gt)
                    && is_zero(r)
                    && let Some(hir_expr) = self.ast_to_hir.get_expr(id, self.tcx)
                    && let hir::ExprKind::Binary(_, hir_l, _) = &hir_expr.kind
                    && let typeck = self.tcx.typeck(hir_expr.hir_id.owner)
                    && let ty = typeck.expr_ty(hir_l)
                    && ty.is_integral()
                    && !ty.is_signed()
                {
                    // avoid clippy::absurd_extreme_comparisons
                    if op.node == BinOpKind::Le {
                        op.node = BinOpKind::Eq;
                    } else {
                        op.node = BinOpKind::Ne;
                    }
                }
            }
            _ => {}
        }
    }

    fn eval_lit_cast(&self, expr: &hir::Expr) -> Option<Int> {
        let typeck = self.tcx.typeck(expr.hir_id.owner);
        let ty = typeck.expr_ty(expr);
        if !ty.is_integral() {
            return None;
        }
        match expr.kind {
            hir::ExprKind::Lit(lit) => {
                if let LitKind::Int(n, _) = lit.node {
                    Some(Int::U128(n.0).to_ty(ty))
                } else {
                    None
                }
            }
            hir::ExprKind::Unary(hir::UnOp::Neg, e) => {
                let v = self.eval_lit_cast(e)?;
                v.neg()
            }
            hir::ExprKind::Cast(e, _) => Some(self.eval_lit_cast(e)?.to_ty(ty)),
            hir::ExprKind::DropTemps(e) => self.eval_lit_cast(e),
            _ => None,
        }
    }

    fn need_annotation(&self, expr: &hir::Expr) -> bool {
        let mut curr_id = expr.hir_id;
        for (parent_id, parent_node) in self.tcx.hir_parent_iter(expr.hir_id) {
            let hir::Node::Expr(parent) = parent_node else { break };
            match parent.kind {
                hir::ExprKind::MethodCall(_, receiver, _, _) => {
                    return receiver.hir_id == curr_id;
                }
                hir::ExprKind::Binary(op, l, _)
                    if matches!(op.node, BinOpKind::Shl | BinOpKind::Shr)
                        && l.hir_id == curr_id =>
                {
                    return true;
                }
                hir::ExprKind::Index(_, _, _) | hir::ExprKind::Cast(_, _) => return false,
                _ => {}
            }
            curr_id = parent_id;
        }
        false
    }

    fn compress_casts(&self, expr: &hir::Expr) -> Option<Vec<ty::Ty<'tcx>>> {
        let typeck = self.tcx.typeck(expr.hir_id.owner);
        let ty = typeck.expr_ty(expr);
        if !ty.is_integral() && !ty.is_bool() {
            return None;
        }
        match expr.kind {
            hir::ExprKind::Cast(e, _) => {
                let mut tys = self.compress_casts(e)?;
                loop {
                    if tys.len() == 1 {
                        if tys[0] != ty {
                            tys.push(ty);
                        }
                        break;
                    }
                    let last = tys.last().unwrap();
                    let size1 = utils::ir::ty_size(*last, expr.hir_id.owner, self.tcx);
                    let size2 = utils::ir::ty_size(ty, expr.hir_id.owner, self.tcx);
                    if size1 != size2 {
                        tys.push(ty);
                        break;
                    } else {
                        tys.pop();
                    }
                }
                Some(tys)
            }
            hir::ExprKind::DropTemps(e) => self.compress_casts(e),
            _ => Some(vec![ty]),
        }
    }
}

fn thir_unwrap_use(expr_id: thir::ExprId, body: &thir::Thir<'_>) -> thir::ExprId {
    if let thir::ExprKind::Use { source } | thir::ExprKind::Scope { value: source, .. } =
        body[expr_id].kind
    {
        thir_unwrap_use(source, body)
    } else {
        expr_id
    }
}

fn is_zero(expr: &Expr) -> bool {
    if let ExprKind::Lit(lit) = &expr.kind {
        lit.kind == token::LitKind::Integer && lit.symbol.as_str() == "0"
    } else {
        false
    }
}

fn find_lit(expr: &Expr) -> Symbol {
    match &expr.kind {
        ExprKind::Lit(lit) => lit.symbol,
        ExprKind::Unary(UnOp::Neg, e) | ExprKind::Cast(e, _) | ExprKind::Paren(e) => find_lit(e),
        _ => panic!("{expr:?}"),
    }
}

fn is_atomic(expr: &Expr) -> bool {
    match &expr.kind {
        ExprKind::Array(..)
        | ExprKind::Call(..)
        | ExprKind::MethodCall(..)
        | ExprKind::Tup(..)
        | ExprKind::Lit(..)
        | ExprKind::Path(..)
        | ExprKind::Break(None, None)
        | ExprKind::Continue(..)
        | ExprKind::Ret(None)
        | ExprKind::Repeat(..)
        | ExprKind::Paren(..)
        | ExprKind::FormatArgs(..) => true,
        ExprKind::Field(e, ..) | ExprKind::Index(e, ..) => is_atomic(e),
        _ => false,
    }
}

#[derive(Debug, Clone, Copy)]
enum Int {
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    I128(i128),
    Isize(isize),
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    U128(u128),
    Usize(usize),
}

macro_rules! impl_int_fmt {
    ($trait:ident, $fmt:expr) => {
        impl std::fmt::$trait for Int {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                match self {
                    Self::I8(v) => std::fmt::$trait::fmt(v, f),
                    Self::I16(v) => std::fmt::$trait::fmt(v, f),
                    Self::I32(v) => std::fmt::$trait::fmt(v, f),
                    Self::I64(v) => std::fmt::$trait::fmt(v, f),
                    Self::I128(v) => std::fmt::$trait::fmt(v, f),
                    Self::Isize(v) => std::fmt::$trait::fmt(v, f),
                    Self::U8(v) => std::fmt::$trait::fmt(v, f),
                    Self::U16(v) => std::fmt::$trait::fmt(v, f),
                    Self::U32(v) => std::fmt::$trait::fmt(v, f),
                    Self::U64(v) => std::fmt::$trait::fmt(v, f),
                    Self::U128(v) => std::fmt::$trait::fmt(v, f),
                    Self::Usize(v) => std::fmt::$trait::fmt(v, f),
                }
            }
        }
    };
}

impl_int_fmt!(Display, "");
impl_int_fmt!(UpperHex, ":X");
impl_int_fmt!(LowerHex, ":x");
impl_int_fmt!(Octal, ":o");
impl_int_fmt!(Binary, ":b");

macro_rules! define_int_conversions {
    ($name:ident, $variant:ident, $ty:ty) => {
        fn $name(self) -> Self {
            match self {
                Self::I8(v) => Self::$variant(v as $ty),
                Self::I16(v) => Self::$variant(v as $ty),
                Self::I32(v) => Self::$variant(v as $ty),
                Self::I64(v) => Self::$variant(v as $ty),
                Self::I128(v) => Self::$variant(v as $ty),
                Self::Isize(v) => Self::$variant(v as $ty),
                Self::U8(v) => Self::$variant(v as $ty),
                Self::U16(v) => Self::$variant(v as $ty),
                Self::U32(v) => Self::$variant(v as $ty),
                Self::U64(v) => Self::$variant(v as $ty),
                Self::U128(v) => Self::$variant(v as $ty),
                Self::Usize(v) => Self::$variant(v as $ty),
            }
        }
    };
}

impl Int {
    define_int_conversions!(to_i8, I8, i8);

    define_int_conversions!(to_i16, I16, i16);

    define_int_conversions!(to_i32, I32, i32);

    define_int_conversions!(to_i64, I64, i64);

    define_int_conversions!(to_i128, I128, i128);

    define_int_conversions!(to_isize, Isize, isize);

    define_int_conversions!(to_u8, U8, u8);

    define_int_conversions!(to_u16, U16, u16);

    define_int_conversions!(to_u32, U32, u32);

    define_int_conversions!(to_u64, U64, u64);

    define_int_conversions!(to_u128, U128, u128);

    define_int_conversions!(to_usize, Usize, usize);

    fn to_ty(self, ty: ty::Ty<'_>) -> Self {
        match ty.kind() {
            ty::Int(ty::IntTy::I8) => self.to_i8(),
            ty::Int(ty::IntTy::I16) => self.to_i16(),
            ty::Int(ty::IntTy::I32) => self.to_i32(),
            ty::Int(ty::IntTy::I64) => self.to_i64(),
            ty::Int(ty::IntTy::I128) => self.to_i128(),
            ty::Int(ty::IntTy::Isize) => self.to_isize(),
            ty::Uint(ty::UintTy::U8) => self.to_u8(),
            ty::Uint(ty::UintTy::U16) => self.to_u16(),
            ty::Uint(ty::UintTy::U32) => self.to_u32(),
            ty::Uint(ty::UintTy::U64) => self.to_u64(),
            ty::Uint(ty::UintTy::U128) => self.to_u128(),
            ty::Uint(ty::UintTy::Usize) => self.to_usize(),
            _ => panic!("{ty}"),
        }
    }

    fn neg(self) -> Option<Self> {
        match self {
            Self::I8(v) => Some(Self::I8(-v)),
            Self::I16(v) => Some(Self::I16(-v)),
            Self::I32(v) => Some(Self::I32(-v)),
            Self::I64(v) => Some(Self::I64(-v)),
            Self::I128(v) => Some(Self::I128(-v)),
            Self::Isize(v) => Some(Self::Isize(-v)),
            _ => None,
        }
    }

    fn is_negative(self) -> bool {
        match self {
            Self::I8(v) => v < 0,
            Self::I16(v) => v < 0,
            Self::I32(v) => v < 0,
            Self::I64(v) => v < 0,
            Self::I128(v) => v < 0,
            Self::Isize(v) => v < 0,
            _ => false,
        }
    }
}

struct HirVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    imports: FxHashMap<LocalModDefId, FxHashSet<LocalDefId>>,
}

impl<'tcx> intravisit::Visitor<'tcx> for HirVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_use(&mut self, path: &'tcx rustc_hir::UsePath<'tcx>, hir_id: rustc_hir::HirId) {
        intravisit::walk_use(self, path, hir_id);

        let mod_id = self.tcx.parent_module(path.segments[0].hir_id);
        let mut add = |res: Option<Res>| {
            if let Some(res) = res
                && let Res::Def(_, def_id) = res
                && let Some(def_id) = def_id.as_local()
            {
                self.imports.entry(mod_id).or_default().insert(def_id);
            }
        };
        add(path.res.value_ns);
        add(path.res.type_ns);
        add(path.res.macro_ns);
    }
}

#[cfg(test)]
mod tests {
    fn run_test(code: &str, includes: &[&str], excludes: &[&str]) {
        let s = utils::compilation::run_compiler_on_str(code, super::simplify).unwrap();
        utils::compilation::run_compiler_on_str(&s, utils::type_check).expect(&s);
        for include in includes {
            assert!(s.contains(include), "Expected to find `{include}` in:\n{s}");
        }
        for exclude in excludes {
            assert!(
                !s.contains(exclude),
                "Expected not to find `{exclude}` in:\n{s}"
            );
        }
    }

    #[test]
    fn test_int_cast() {
        run_test("fn f() { 1 as i32 as i64; }", &["1"], &["as"])
    }

    #[test]
    fn test_neg_int_cast() {
        run_test("fn f() { -1 as i32 as i64; }", &["-1"], &["as"])
    }

    #[test]
    fn test_hex_int_cast() {
        run_test("fn f() { 0xf as i32 as i64; }", &["0xf"], &["as"])
    }

    #[test]
    fn test_octal_int_cast() {
        run_test("fn f() { 0o17 as i32 as i64; }", &["0o17"], &["as"])
    }

    #[test]
    fn test_binary_int_cast() {
        run_test("fn f() { 0b1111 as i32 as i64; }", &["0b1111"], &["as"])
    }

    #[test]
    fn test_int_cast_method_call() {
        run_test("fn f() { (1 as i32).wrapping_add(0); }", &["1i32"], &["as"])
    }

    #[test]
    fn test_int_cast_shift() {
        run_test("fn f() { (1 as i32 as u32) >> 1; }", &["1u32"], &["as"])
    }

    #[test]
    fn test_neg_hex_int_cast() {
        run_test("fn f() { 0xff as u8 as i8; }", &["-1"], &["as"])
    }

    #[test]
    fn test_cast_1() {
        run_test("fn f(x: i32) { x as i32 as i32; }", &["x"], &["as"])
    }

    #[test]
    fn test_cast_2() {
        run_test("fn f(x: i32) { x as u32 as i32; }", &["x"], &["as"])
    }

    #[test]
    fn test_cast_3() {
        run_test(
            "fn f(x: i64) { x as i32 as u32; }",
            &["x as u32"],
            &["as i32"],
        )
    }

    #[test]
    fn test_lit_paren() {
        run_test("fn f() { ((1)); }", &["1"], &["(1)"])
    }

    #[test]
    fn test_path_paren() {
        run_test("fn f(x: i32) { ((x)); }", &["x"], &["((x))"])
    }

    #[test]
    fn test_call_paren() {
        run_test("fn f() { ((f())); }", &["f()"], &["((f()))"])
    }

    #[test]
    fn test_method_call_paren() {
        run_test(
            "fn f() { ((1u32.wrapping_add(1))); }",
            &["1u32.wrapping_add(1)"],
            &["((1u32.wrapping_add(1)))"],
        )
    }

    #[test]
    fn test_index_paren() {
        run_test("fn f(x: &[i32]) { ((x[0])); }", &["x[0]"], &["((x[0]))"])
    }

    #[test]
    fn test_field_paren() {
        run_test(
            "struct S(i32); fn f(x: S) { ((x.0)); }",
            &["x.0"],
            &["((x.0))"],
        )
    }
}
