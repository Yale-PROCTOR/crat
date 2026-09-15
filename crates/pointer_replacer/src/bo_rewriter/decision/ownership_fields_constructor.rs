//! Source-identified zeroed numeric Box and boxed-slice constructors.
use rustc_hir::{Expr, ExprKind, Node, QPath, def::Res};
use rustc_middle::ty::{FloatTy, IntTy, Ty, TyCtxt, TyKind, UintTy};
use rustc_span::{
    Symbol,
    def_id::{DefId, LocalDefId},
};

use super::{
    box_facts::{BoxExprEdit, BoxShape},
    ownership_fields_source::SourceHold,
};

pub(crate) struct Constructor<'tcx> {
    pub(crate) allocation: &'tcx Expr<'tcx>,
    pub(crate) allocator: DefId,
    pub(crate) element: Ty<'tcx>,
    /// The element type as it must be spelled at the binding (`i32`, or a
    /// crate-rooted path for a local struct), for the explicit Box annotation.
    pub(crate) element_spelling: String,
    pub(crate) count: String,
    pub(crate) shape: BoxShape,
    pub(crate) nonempty: bool,
    pub(crate) edit: BoxExprEdit,
}

pub(crate) fn derive<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    init: &'tcx Expr<'tcx>,
    element: Ty<'tcx>,
) -> Result<Constructor<'tcx>, SourceHold> {
    if init.hir_id.owner.def_id != owner {
        return Err(SourceHold::Identity);
    }
    let typeck = tcx.typeck(owner);
    if !matches!(typeck.expr_ty(init).kind(), TyKind::RawPtr(pointee, rustc_hir::Mutability::Mut) if *pointee == element)
    {
        return Err(SourceHold::ConstructorShape);
    }
    let pointer_bits = tcx.data_layout.pointer_size.bits();
    let (zero, element_bits) = zero_value(tcx, element, pointer_bits)?;
    let element_spelling = match element.kind() {
        TyKind::Adt(def, _) => format!("crate::{}", tcx.def_path_str(def.did())),
        _ => element.to_string(),
    };
    let mut allocation = init;
    while let ExprKind::Cast(inner, _) = allocation.kind {
        if !matches!(typeck.expr_ty(allocation).kind(), TyKind::RawPtr(..))
            || !matches!(typeck.expr_ty(inner).kind(), TyKind::RawPtr(..))
        {
            return Err(SourceHold::ConstructorShape);
        }
        allocation = inner;
    }
    let ExprKind::Call(callee, arguments) = allocation.kind else {
        return Err(SourceHold::ConstructorShape);
    };
    let allocator = definition(callee).ok_or(SourceHold::ConstructorIdentity)?;
    let Some(local) = allocator.as_local() else {
        return Err(SourceHold::ConstructorIdentity);
    };
    if !matches!(tcx.hir_node_by_def_id(local), Node::ForeignItem(_)) {
        return Err(SourceHold::ConstructorIdentity);
    }
    let symbol = tcx
        .codegen_fn_attrs(allocator)
        .link_name
        .unwrap_or_else(|| tcx.item_name(allocator));
    let signature = tcx.fn_sig(allocator).skip_binder().skip_binder();
    // A widening integer cast is not enough to establish the foreign ABI.
    // All allocator arguments must be size_t, including its unsigned width.
    let is_malloc = symbol.as_str() == "malloc";
    if (!is_malloc && symbol.as_str() != "calloc")
        || signature.c_variadic
        || signature.abi != (rustc_abi::ExternAbi::C { unwind: false })
        || signature.inputs().len() != (if is_malloc { 1 } else { 2 })
        || signature
            .inputs()
            .iter()
            .any(|ty| unsigned_bits(*ty, pointer_bits) != Some(pointer_bits))
        || !matches!(signature.output().kind(), TyKind::RawPtr(pointee, rustc_hir::Mutability::Mut)
            if matches!(pointee.kind(), TyKind::Adt(def, _) if Some(def.did()) == tcx.lang_items().c_void()))
    {
        return Err(SourceHold::ConstructorIdentity);
    }
    if is_malloc {
        let [bytes] = arguments else { return Err(SourceHold::ConstructorShape) };
        // A narrowed byte local is the one shape whose casts are not all
        // size_t-width; every other arm peels only size_t casts.
        let peeled = peel_size_t(typeck, bytes, pointer_bits).ok();
        let (shape, count, replacement) = if peeled
            .is_some_and(|peeled| exact_size(tcx, typeck, peeled, element, pointer_bits))
        {
            (
                BoxShape::Sized,
                "1".into(),
                format!("::std::boxed::Box::new({zero})"),
            )
        } else if peeled.is_some_and(|peeled| {
            wrapping_product_has_exact_size(tcx, typeck, peeled, element, pointer_bits)
        }) || narrowed_byte_local_has_exact_size(
            tcx,
            owner,
            typeck,
            bytes,
            element,
            pointer_bits,
        ) {
            // The derived corpus spells `n * sizeof(T)` as a `wrapping_mul`
            // chain with a dynamic factor. The complete byte expression is
            // kept and evaluated once; the count is its exact quotient by
            // `size_of::<T>()`. Conditional on a UB-free input (§28): the C
            // program allocated exactly these bytes and every T-typed access
            // lies within them, so the quotient bounds every valid index; a
            // wrapped product mis-sizes the C allocation and its first
            // out-of-bounds access is the input's own UB.
            let original = tcx
                .sess
                .source_map()
                .span_to_snippet(bytes.span)
                .map_err(|_| SourceHold::Missing("constructor-byte-spelling"))?;
            let count = format!("((({original}) as usize) / ::core::mem::size_of::<{element}>())");
            let replacement = format!("::std::vec![{zero}; {count}].into_boxed_slice()");
            return Ok(Constructor {
                allocation,
                allocator,
                element,
                element_spelling: element_spelling.clone(),
                count,
                shape: BoxShape::Slice,
                nonempty: false,
                edit: BoxExprEdit {
                    span: init.span,
                    replacement,
                    receipt: "native-malloc-zero-numeric-wrapping-count",
                },
            });
        } else {
            let Some(peeled) = peeled else { return Err(SourceHold::ConstructorShape) };
            let ExprKind::Binary(operator, left, right) = peeled.kind else {
                return Err(SourceHold::ConstructorShape);
            };
            if operator.node != rustc_hir::BinOpKind::Mul {
                return Err(SourceHold::ConstructorShape);
            }
            let factor = if exact_size(tcx, typeck, right, element, pointer_bits) {
                left
            } else if exact_size(tcx, typeck, left, element, pointer_bits) {
                right
            } else {
                return Err(SourceHold::ConstructorShape);
            };
            let bound =
                unsigned_bound(typeck, factor, pointer_bits).ok_or(SourceHold::ConstructorShape)?;
            let maximum_bytes = (1u128 << (pointer_bits - 1)) - 1;
            if bound == 0
                || bound
                    .checked_mul((element_bits / 8) as u128)
                    .is_none_or(|bytes| bytes > maximum_bytes)
            {
                return Err(SourceHold::ConstructorShape);
            }
            // Keep the complete byte expression, including all source casts,
            // operand order and side effects, evaluated once at the allocation.
            // Exact sizeof and the bound above make this division lossless.
            let original = tcx
                .sess
                .source_map()
                .span_to_snippet(bytes.span)
                .map_err(|_| SourceHold::Missing("constructor-byte-spelling"))?;
            let count = format!("((({original}) as usize) / ::core::mem::size_of::<{element}>())");
            let replacement = format!("::std::vec![{zero}; {count}].into_boxed_slice()");
            (BoxShape::Slice, count, replacement)
        };
        return Ok(Constructor {
            allocation,
            allocator,
            element,
            element_spelling: element_spelling.clone(),
            count,
            shape,
            nonempty: shape == BoxShape::Sized
                || peeled.is_some_and(|peeled| matches!(peeled.kind,ExprKind::Binary(_,left,right) if [left,right].iter().any(|e|matches!(e.kind,ExprKind::Lit(lit) if matches!(lit.node,rustc_ast::LitKind::Int(value,_) if value.get()>0))))),
            edit: BoxExprEdit {
                span: init.span,
                replacement,
                receipt: "native-malloc-zero-numeric",
            },
        });
    }
    let [count_expression, size_expression] = arguments else {
        return Err(SourceHold::ConstructorShape);
    };
    let mut size_expression = size_expression;
    if unsigned_bits(typeck.expr_ty(count_expression), pointer_bits) != Some(pointer_bits)
        || unsigned_bits(typeck.expr_ty(size_expression), pointer_bits) != Some(pointer_bits)
    {
        return Err(SourceHold::ConstructorShape);
    }
    // sizeof is pure, and every removed cast must preserve its usize value.
    // Reject an intermediate narrowing cast even when this particular T fits.
    while let ExprKind::Cast(inner, _) = size_expression.kind {
        if unsigned_bits(typeck.expr_ty(size_expression), pointer_bits) != Some(pointer_bits)
            || unsigned_bits(typeck.expr_ty(inner), pointer_bits) != Some(pointer_bits)
        {
            return Err(SourceHold::ConstructorShape);
        }
        size_expression = inner;
    }
    let ExprKind::Call(size_callee, size_arguments) = size_expression.kind else {
        return Err(SourceHold::ConstructorShape);
    };
    let size_definition = definition(size_callee).ok_or(SourceHold::ConstructorShape)?;
    if !size_arguments.is_empty()
        || !tcx.is_diagnostic_item(Symbol::intern("mem_size_of"), size_definition)
        || !matches!(typeck.expr_ty(size_callee).kind(), TyKind::FnDef(did, args)
            if *did == size_definition && args.type_at(0) == element)
    {
        return Err(SourceHold::ConstructorShape);
    }
    let count = if let ExprKind::Lit(literal) = count_expression.kind
        && let rustc_ast::LitKind::Int(value, _) = literal.node
    {
        let count = value.get();
        let maximum_bytes = 1u128
            .checked_shl((pointer_bits - 1) as u32)
            .and_then(|limit| limit.checked_sub(1))
            .ok_or(SourceHold::ConstructorShape)?;
        if count == 0
            || count
                .checked_mul((element_bits / 8) as u128)
                .is_none_or(|bytes| bytes > maximum_bytes)
        {
            return Err(SourceHold::ConstructorShape);
        }
        count.to_string()
    } else {
        let original = tcx
            .sess
            .source_map()
            .span_to_snippet(count_expression.span)
            .map_err(|_| SourceHold::Missing("constructor-count-spelling"))?;
        // Retain the complete source operand, including any signed/narrowing
        // casts. Only the final ABI value is converted losslessly to usize.
        // vec! evaluates this length once at the original allocation site.
        format!("(({original}) as usize)")
    };
    Ok(Constructor {
        allocation,
        allocator,
        element,
        element_spelling,
        edit: BoxExprEdit {
            span: init.span,
            replacement: format!("::std::vec![{zero}; {count}].into_boxed_slice()"),
            receipt: if element == tcx.types.f32 {
                "native-calloc-zero-f32"
            } else {
                "native-calloc-zero-numeric"
            },
        },
        count,
        shape: BoxShape::Slice,
        nonempty: matches!(count_expression.kind,ExprKind::Lit(lit) if matches!(lit.node,rustc_ast::LitKind::Int(value,_) if value.get()>0)),
    })
}

fn peel_size_t<'tcx>(
    typeck: &rustc_middle::ty::TypeckResults<'tcx>,
    mut expression: &'tcx Expr<'tcx>,
    pointer_bits: u64,
) -> Result<&'tcx Expr<'tcx>, SourceHold> {
    if unsigned_bits(typeck.expr_ty(expression), pointer_bits) != Some(pointer_bits) {
        return Err(SourceHold::ConstructorShape);
    }
    while let ExprKind::Cast(inner, _) = expression.kind {
        if unsigned_bits(typeck.expr_ty(inner), pointer_bits) != Some(pointer_bits) {
            return Err(SourceHold::ConstructorShape);
        }
        expression = inner;
    }
    Ok(expression)
}

fn exact_size<'tcx>(
    tcx: TyCtxt<'tcx>,
    typeck: &rustc_middle::ty::TypeckResults<'tcx>,
    expression: &'tcx Expr<'tcx>,
    element: Ty<'tcx>,
    pointer_bits: u64,
) -> bool {
    let Ok(expression) = peel_size_t(typeck, expression, pointer_bits) else { return false };
    let ExprKind::Call(callee, arguments) = expression.kind else { return false };
    let Some(did) = definition(callee) else { return false };
    arguments.is_empty()
        && tcx.is_diagnostic_item(Symbol::intern("mem_size_of"), did)
        && matches!(typeck.expr_ty(callee).kind(), TyKind::FnDef(actual, args)
            if *actual == did && args.type_at(0) == element)
}

/// A `wrapping_mul` chain over size_t-width unsigned operands in which one
/// factor is exactly `size_of::<T>()`. Every operand must stay at the pointer
/// width through its casts, so no factor is narrowed on the way to `malloc`.
fn wrapping_product_has_exact_size<'tcx>(
    tcx: TyCtxt<'tcx>,
    typeck: &rustc_middle::ty::TypeckResults<'tcx>,
    expression: &'tcx Expr<'tcx>,
    element: Ty<'tcx>,
    pointer_bits: u64,
) -> bool {
    let Ok(expression) = peel_size_t(typeck, expression, pointer_bits) else { return false };
    let ExprKind::MethodCall(segment, receiver, [argument], _) = expression.kind else {
        return false;
    };
    let Some(method) = typeck.type_dependent_def_id(expression.hir_id) else { return false };
    let is_wrapping_mul = segment.ident.name.as_str() == "wrapping_mul"
        && tcx.item_name(method).as_str() == "wrapping_mul"
        && tcx.impl_of_method(method).is_some_and(|imp| {
            tcx.trait_id_of_impl(imp).is_none()
                && unsigned_bits(tcx.type_of(imp).skip_binder(), pointer_bits) == Some(pointer_bits)
        });
    is_wrapping_mul
        && [receiver, argument].iter().all(|operand| {
            unsigned_bits(typeck.expr_ty(operand), pointer_bits) == Some(pointer_bits)
        })
        && [receiver, argument].iter().any(|operand| {
            exact_size(tcx, typeck, operand, element, pointer_bits)
                || wrapping_product_has_exact_size(tcx, typeck, operand, element, pointer_bits)
        })
}

/// `malloc(nbytes as size_t)` where `nbytes` is a `let` local of the same
/// body, initialised exactly once from a `wrapping_mul` chain with the exact
/// `size_of::<T>()` factor and narrowed through integer casts on the way
/// (`… as c_int`), never reassigned or borrowed. Conditional on a UB-free
/// input the narrowed value is the product: a narrowed mismatch mis-sizes the
/// C allocation and its first access past it is the input's own UB.
fn narrowed_byte_local_has_exact_size<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    typeck: &rustc_middle::ty::TypeckResults<'tcx>,
    expression: &'tcx Expr<'tcx>,
    element: Ty<'tcx>,
    pointer_bits: u64,
) -> bool {
    if unsigned_bits(typeck.expr_ty(expression), pointer_bits) != Some(pointer_bits) {
        return false;
    }
    let mut operand = expression;
    while let ExprKind::Cast(inner, _) = operand.kind {
        if !typeck.expr_ty(operand).is_integral() || !typeck.expr_ty(inner).is_integral() {
            return false;
        }
        operand = inner;
    }
    let ExprKind::Path(QPath::Resolved(_, path)) = operand.kind else { return false };
    let Res::Local(binding) = path.res else { return false };
    let Node::Pat(pattern) = tcx.hir_node(binding) else { return false };
    if !matches!(
        pattern.kind,
        rustc_hir::PatKind::Binding(
            rustc_hir::BindingMode::NONE | rustc_hir::BindingMode::MUT,
            ..
        )
    ) {
        return false;
    }
    let Node::LetStmt(local) = tcx.parent_hir_node(binding) else { return false };
    let Some(init) = local.init else { return false };
    if local.els.is_some() {
        return false;
    }
    // The binding must keep its initial value: no assignment, no borrow.
    struct Single {
        binding: rustc_hir::HirId,
        stable: bool,
    }
    impl<'v> rustc_hir::intravisit::Visitor<'v> for Single {
        fn visit_expr(&mut self, e: &'v Expr<'v>) {
            let is_binding = |e: &Expr<'_>| matches!(e.kind, ExprKind::Path(QPath::Resolved(_, path)) if path.res == Res::Local(self.binding));
            match e.kind {
                ExprKind::Assign(lhs, ..) | ExprKind::AssignOp(_, lhs, _) if is_binding(lhs) => {
                    self.stable = false;
                }
                ExprKind::AddrOf(_, _, inner) if is_binding(inner) => self.stable = false,
                _ => {}
            }
            rustc_hir::intravisit::walk_expr(self, e);
        }
    }
    let mut single = Single {
        binding,
        stable: true,
    };
    rustc_hir::intravisit::Visitor::visit_body(&mut single, tcx.hir_body_owned_by(owner));
    if !single.stable {
        return false;
    }
    let mut product = init;
    while let ExprKind::Cast(inner, _) = product.kind {
        if !typeck.expr_ty(product).is_integral() || !typeck.expr_ty(inner).is_integral() {
            return false;
        }
        product = inner;
    }
    wrapping_product_has_exact_size(tcx, typeck, product, element, pointer_bits)
}

fn unsigned_bound(
    typeck: &rustc_middle::ty::TypeckResults<'_>,
    expression: &Expr<'_>,
    pointer_bits: u64,
) -> Option<u128> {
    let bits = unsigned_bits(typeck.expr_ty(expression), pointer_bits)?;
    if let ExprKind::Lit(literal) = expression.kind
        && let rustc_ast::LitKind::Int(value, _) = literal.node
    {
        return Some(value.get());
    }
    if let ExprKind::Cast(inner, _) = expression.kind {
        let inner_bits = unsigned_bits(typeck.expr_ty(inner), pointer_bits)?;
        return (inner_bits <= bits)
            .then(|| unsigned_bound(typeck, inner, pointer_bits))
            .flatten();
    }
    Some(if bits == 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    })
}

fn definition(expression: &Expr<'_>) -> Option<DefId> {
    match expression.kind {
        ExprKind::Path(QPath::Resolved(_, path)) => match path.res {
            Res::Def(rustc_hir::def::DefKind::Fn, did) => Some(did),
            _ => None,
        },
        _ => None,
    }
}

fn unsigned_bits(ty: Ty<'_>, pointer_bits: u64) -> Option<u64> {
    let TyKind::Uint(kind) = ty.kind() else { return None };
    Some(match kind {
        UintTy::U8 => 8,
        UintTy::U16 => 16,
        UintTy::U32 => 32,
        UintTy::U64 => 64,
        UintTy::U128 => 128,
        UintTy::Usize => pointer_bits,
    })
}

/// A spelled all-zero value for a numeric scalar, a raw pointer (null), an
/// array of such, or a `repr(C)` struct whose fields are all such (every
/// field named, so the literal is complete and needs no `unsafe`). C's
/// `malloc` leaves the object indeterminate; the C program writes before it
/// reads, so any valid initial value is behaviour-preserving, and all-zero is
/// a valid value of every such type.
fn zero_value<'tcx>(
    tcx: TyCtxt<'tcx>,
    element: Ty<'tcx>,
    pointer_bits: u64,
) -> Result<(String, u64), SourceHold> {
    match element.kind() {
        TyKind::RawPtr(_, rustc_hir::Mutability::Mut) => {
            Ok(("::core::ptr::null_mut()".into(), pointer_bits))
        }
        TyKind::RawPtr(_, rustc_hir::Mutability::Not) => {
            Ok(("::core::ptr::null()".into(), pointer_bits))
        }
        TyKind::Array(inner, length) => {
            let length = length
                .try_to_target_usize(tcx)
                .ok_or(SourceHold::ConstructorShape)?;
            let (zero, bits) = zero_value(tcx, *inner, pointer_bits)?;
            Ok((
                format!("[{zero}; {length}]"),
                bits.checked_mul(length)
                    .ok_or(SourceHold::ConstructorShape)?,
            ))
        }
        TyKind::Adt(def, args) if def.is_struct() && def.repr().c() && def.did().is_local() => {
            let mut fields = Vec::new();
            for field in def.non_enum_variant().fields.iter() {
                let (zero, _) = zero_value(tcx, field.ty(tcx, args), pointer_bits)?;
                fields.push(format!("{}: {zero}", field.name));
            }
            let layout = tcx
                .layout_of(
                    rustc_middle::ty::TypingEnv::fully_monomorphized().as_query_input(element),
                )
                .map_err(|_| SourceHold::ConstructorShape)?;
            Ok((
                format!(
                    "crate::{} {{ {} }}",
                    tcx.def_path_str(def.did()),
                    fields.join(", ")
                ),
                layout.size.bits(),
            ))
        }
        _ => numeric_zero(element, pointer_bits),
    }
}

fn numeric_zero(element: Ty<'_>, pointer_bits: u64) -> Result<(String, u64), SourceHold> {
    let bits = match element.kind() {
        TyKind::Int(kind) => match kind {
            IntTy::I8 => 8,
            IntTy::I16 => 16,
            IntTy::I32 => 32,
            IntTy::I64 => 64,
            IntTy::I128 => 128,
            IntTy::Isize => pointer_bits,
        },
        TyKind::Uint(_) => unsigned_bits(element, pointer_bits).unwrap(),
        TyKind::Float(FloatTy::F32) => return Ok(("0.0f32".into(), 32)),
        TyKind::Float(FloatTy::F64) => return Ok(("0.0f64".into(), 64)),
        _ => return Err(SourceHold::ConstructorShape),
    };
    Ok((format!("0{element}"), bits))
}

#[cfg(test)]
mod tests {
    use rustc_middle::ty::TyKind;

    use super::*;

    fn inspect(
        declarations: &str,
        element: &str,
        initializer: &str,
    ) -> Result<(String, String, &'static str), SourceHold> {
        let source = format!(
            "#![allow(dead_code,non_camel_case_types)]\nmod libc {{ pub use core::ffi::c_ulong; }}\n{declarations}\nunsafe fn probe(mut n:i32)->*mut {element} {{ {initializer} }}"
        );
        ::utils::compilation::run_compiler_on_str(&source, |tcx| {
            let owner = tcx
                .hir_body_owners()
                .find(|owner| {
                    tcx.opt_item_name(owner.to_def_id())
                        .is_some_and(|name| name.as_str() == "probe")
                })
                .expect("fixture owner");
            let ExprKind::Block(block, _) = tcx.hir_body_owned_by(owner).value.kind else {
                panic!("fixture block")
            };
            let init = block.expr.expect("fixture initializer");
            let TyKind::RawPtr(element, _) = tcx.typeck(owner).expr_ty(init).kind() else {
                panic!("fixture pointer")
            };
            let constructor = derive(tcx, owner, init, *element)?;
            assert_eq!(constructor.element, *element);
            assert_eq!(constructor.edit.span, init.span);
            assert!(matches!(constructor.allocation.kind, ExprKind::Call(..)));
            assert!(constructor.allocator.as_local().is_some());
            Ok((
                constructor.count,
                constructor.edit.replacement,
                constructor.edit.receipt,
            ))
        })
        .expect("constructor fixture compiles")
    }

    const USIZE_CALLOC: &str =
        "unsafe extern \"C\" { fn calloc(n:usize,s:usize)->*mut core::ffi::c_void; }";
    const C_ULONG_CALLOC: &str = "unsafe extern \"C\" { fn calloc(n:libc::c_ulong,s:libc::c_ulong)->*mut core::ffi::c_void; }";
    const USIZE_MALLOC: &str =
        "unsafe extern \"C\" { fn malloc(n:usize)->*mut core::ffi::c_void; }";

    #[test]
    fn constructor_malloc_sized_uses_typed_zero() {
        assert_eq!(
            inspect(
                USIZE_MALLOC,
                "u16",
                "malloc(core::mem::size_of::<u16>()) as *mut u16"
            ),
            Ok((
                "1".into(),
                "::std::boxed::Box::new(0u16)".into(),
                "native-malloc-zero-numeric"
            ))
        );
    }

    #[test]
    fn constructor_malloc_literal_slice_preserves_complete_byte_expression() {
        for bytes in [
            "3 * core::mem::size_of::<f32>()",
            "core::mem::size_of::<f32>() * 3",
        ] {
            let (count, edit, receipt) =
                inspect(USIZE_MALLOC, "f32", &format!("malloc({bytes}) as *mut f32")).unwrap();
            assert_eq!(
                count,
                format!("((({bytes}) as usize) / ::core::mem::size_of::<f32>())")
            );
            assert_eq!(
                edit,
                format!("::std::vec![0.0f32; {count}].into_boxed_slice()")
            );
            assert_eq!(edit.matches(bytes).count(), 1);
            assert_eq!(receipt, "native-malloc-zero-numeric");
        }
    }

    #[test]
    fn constructor_malloc_bounded_effectful_factor_evaluates_once() {
        let bytes = "(next(&mut n) as usize) * core::mem::size_of::<u16>()";
        let (count, edit, _) = inspect(
            &format!("{USIZE_MALLOC} fn next(n:&mut i32)->u16 {{ *n+=1; *n as u16 }}"),
            "u16",
            &format!("malloc({bytes}) as *mut u16"),
        )
        .unwrap();
        assert_eq!(
            count,
            format!("((({bytes}) as usize) / ::core::mem::size_of::<u16>())")
        );
        assert_eq!(edit.matches("next(&mut n)").count(), 1);
    }

    const C_ULONG_MALLOC: &str =
        "unsafe extern \"C\" { fn malloc(n:libc::c_ulong)->*mut core::ffi::c_void; }";

    #[test]
    fn constructor_malloc_wrapping_mul_chain_divides_complete_byte_expression() {
        // The derived corpus spells `n * sizeof(T)` as `wrapping_mul`, in either
        // operand order, sometimes with a second dynamic factor.
        for bytes in [
            "(n as libc::c_ulong).wrapping_mul(core::mem::size_of::<i32>() as libc::c_ulong)",
            "(core::mem::size_of::<i32>() as libc::c_ulong).wrapping_mul(n as libc::c_ulong)",
            "(n as libc::c_ulong).wrapping_mul(core::mem::size_of::<i32>() as libc::c_ulong).wrapping_mul((n + 1) as libc::c_ulong)",
        ] {
            let (count, edit, receipt) = inspect(
                C_ULONG_MALLOC,
                "i32",
                &format!("malloc({bytes}) as *mut i32"),
            )
            .unwrap();
            assert_eq!(
                count,
                format!("((({bytes}) as usize) / ::core::mem::size_of::<i32>())"),
                "{bytes}"
            );
            assert_eq!(
                edit,
                format!("::std::vec![0i32; {count}].into_boxed_slice()")
            );
            assert_eq!(edit.matches(bytes).count(), 1);
            assert_eq!(receipt, "native-malloc-zero-numeric-wrapping-count");
        }
    }

    #[test]
    fn constructor_malloc_narrowed_byte_local_divides_by_its_initializer_factor() {
        // heman `generate_gaussian_row::tmp`: the byte count is a `c_int`
        // local initialised once from the `wrapping_mul` chain and widened
        // back at the allocation.
        let (count, edit, receipt) = inspect(
            C_ULONG_MALLOC,
            "i32",
            "let nbytes = (n as libc::c_ulong).wrapping_mul(core::mem::size_of::<i32>() as libc::c_ulong) as i32; malloc(nbytes as libc::c_ulong) as *mut i32",
        )
        .unwrap();
        assert_eq!(
            count,
            "(((nbytes as libc::c_ulong) as usize) / ::core::mem::size_of::<i32>())"
        );
        assert_eq!(
            edit,
            format!("::std::vec![0i32; {count}].into_boxed_slice()")
        );
        assert_eq!(receipt, "native-malloc-zero-numeric-wrapping-count");
    }

    #[test]
    fn constructor_malloc_narrowed_byte_local_faults_hold_reassigned_borrowed_or_unrelated() {
        for body in [
            "let mut nbytes = (n as libc::c_ulong).wrapping_mul(core::mem::size_of::<i32>() as libc::c_ulong) as i32; nbytes = 4; malloc(nbytes as libc::c_ulong) as *mut i32",
            "let mut nbytes = (n as libc::c_ulong).wrapping_mul(core::mem::size_of::<i32>() as libc::c_ulong) as i32; let r = &mut nbytes; *r += 1; malloc(nbytes as libc::c_ulong) as *mut i32",
            "let nbytes = (n as libc::c_ulong).wrapping_mul(core::mem::size_of::<u32>() as libc::c_ulong) as i32; malloc(nbytes as libc::c_ulong) as *mut i32",
            "let nbytes = n * 4; malloc(nbytes as libc::c_ulong) as *mut i32",
            "let nbytes: libc::c_ulong = 16; malloc(nbytes) as *mut i32",
        ] {
            assert_eq!(
                inspect(C_ULONG_MALLOC, "i32", body),
                Err(SourceHold::ConstructorShape),
                "{body}"
            );
        }
    }

    #[test]
    fn constructor_malloc_wrapping_mul_faults_require_exact_sizeof_factor() {
        for bytes in [
            "(n as libc::c_ulong).wrapping_mul(core::mem::size_of::<u32>() as libc::c_ulong)",
            "(n as libc::c_ulong).wrapping_mul(4 as libc::c_ulong)",
            "(n as libc::c_ulong).wrapping_add(core::mem::size_of::<i32>() as libc::c_ulong)",
            "(n as libc::c_ulong).wrapping_mul(core::mem::size_of::<i32>() as u32 as libc::c_ulong)",
            "((n as libc::c_ulong).wrapping_mul(core::mem::size_of::<i32>() as libc::c_ulong) as u32) as libc::c_ulong",
            "(n as libc::c_ulong).wrapping_mul((core::mem::size_of::<i32>() as u32).wrapping_mul(1) as libc::c_ulong)",
        ] {
            assert_eq!(
                inspect(
                    C_ULONG_MALLOC,
                    "i32",
                    &format!("malloc({bytes}) as *mut i32")
                ),
                Err(SourceHold::ConstructorShape),
                "{bytes}"
            );
        }
    }

    #[test]
    fn constructor_repr_c_struct_zero_names_every_field() {
        let declarations = format!(
            "{C_ULONG_MALLOC} #[repr(C)] #[derive(Copy,Clone)] pub struct Inner {{ pub v: [f32; 2] }} #[repr(C)] #[derive(Copy,Clone)] pub struct Rec {{ pub width: i32, pub data: *mut f32, pub name: *const u8, pub inner: Inner }} pub type Alias = Rec;"
        );
        assert_eq!(
            inspect(
                &declarations,
                "Rec",
                "malloc(core::mem::size_of::<Rec>() as libc::c_ulong) as *mut Alias"
            ),
            Ok((
                "1".into(),
                "::std::boxed::Box::new(crate::Rec { width: 0i32, data: ::core::ptr::null_mut(), name: ::core::ptr::null(), inner: crate::Inner { v: [0.0f32; 2] } })".into(),
                "native-malloc-zero-numeric"
            ))
        );
    }

    #[test]
    fn constructor_struct_zero_faults_hold_non_c_layout_and_non_zeroable_fields() {
        for (declaration, element) in [
            (
                "#[derive(Copy,Clone)] pub struct Plain { pub a: i32 }",
                "Plain",
            ),
            (
                "#[repr(C)] #[derive(Copy,Clone)] pub struct Flag { pub a: bool }",
                "Flag",
            ),
            (
                "#[repr(C)] #[derive(Copy,Clone)] pub struct Refd { pub a: &'static u8 }",
                "Refd",
            ),
            (
                "#[repr(C)] #[derive(Copy,Clone)] pub struct Text { pub a: char }",
                "Text",
            ),
            (
                "#[repr(C)] #[derive(Copy,Clone)] pub enum Tag { A, B }",
                "Tag",
            ),
            (
                "#[repr(C)] #[derive(Copy,Clone)] pub union U { pub a: i32, pub b: f32 }",
                "U",
            ),
        ] {
            assert_eq!(
                inspect(
                    &format!("{C_ULONG_MALLOC} {declaration}"),
                    element,
                    &format!(
                        "malloc(core::mem::size_of::<{element}>() as libc::c_ulong) as *mut {element}"
                    )
                ),
                Err(SourceHold::ConstructorShape),
                "{declaration}"
            );
        }
    }

    #[test]
    fn constructor_malloc_faults_hold_unbounded_narrowing_and_wrong_size() {
        for bytes in [
            "n as usize * core::mem::size_of::<f32>()",
            "(3 * core::mem::size_of::<f32>()) as u8 as usize",
            "3 * (core::mem::size_of::<f32>() as u8 as usize)",
            "3 * core::mem::size_of::<u32>()",
            "0 * core::mem::size_of::<f32>()",
            "usize::MAX * core::mem::size_of::<f32>()",
        ] {
            assert_eq!(
                inspect(USIZE_MALLOC, "f32", &format!("malloc({bytes}) as *mut f32")),
                Err(SourceHold::ConstructorShape),
                "{bytes}"
            );
        }
    }

    #[test]
    fn constructor_malloc_faults_require_c_allocator_and_size_t_abi() {
        for declarations in [
            "unsafe fn malloc(n:usize)->*mut core::ffi::c_void { core::ptr::null_mut() }",
            "unsafe extern \"C-unwind\" { fn malloc(n:usize)->*mut core::ffi::c_void; }",
            "unsafe extern \"C\" { fn malloc(n:u32)->*mut core::ffi::c_void; }",
            "unsafe extern \"C\" { fn malloc(n:isize)->*mut core::ffi::c_void; }",
            "unsafe extern \"C\" { #[link_name=\"not_malloc\"] fn malloc(n:usize)->*mut core::ffi::c_void; }",
        ] {
            assert_eq!(
                inspect(
                    declarations,
                    "f32",
                    "malloc(core::mem::size_of::<f32>() as _) as *mut f32"
                ),
                Err(SourceHold::ConstructorIdentity),
                "{declarations}"
            );
        }
    }

    #[test]
    fn constructor_literal_f32_preserves_existing_rendering() {
        assert_eq!(
            inspect(
                USIZE_CALLOC,
                "f32",
                "calloc(2,core::mem::size_of::<f32>()) as *mut f32"
            ),
            Ok((
                "2".into(),
                "::std::vec![0.0f32; 2].into_boxed_slice()".into(),
                "native-calloc-zero-f32"
            ))
        );
    }

    #[test]
    fn constructor_c_ulong_dynamic_count_preserves_source_cast_once() {
        let (count, edit, receipt) = inspect(
            C_ULONG_CALLOC,
            "f32",
            "calloc((n + 1) as libc::c_ulong,core::mem::size_of::<f32>() as libc::c_ulong) as *mut f32",
        ).unwrap();
        assert_eq!(count, "(((n + 1) as libc::c_ulong) as usize)");
        assert_eq!(edit.matches("n + 1").count(), 1);
        assert_eq!(
            edit,
            format!("::std::vec![0.0f32; {count}].into_boxed_slice()")
        );
        assert_eq!(receipt, "native-calloc-zero-f32");
    }

    #[test]
    fn constructor_uint16_cast_target_selects_typed_zero() {
        let (_, edit, receipt) = inspect(
            &format!("{C_ULONG_CALLOC} type uint16_t=u16;"),
            "uint16_t",
            "calloc(n as libc::c_ulong,core::mem::size_of::<uint16_t>() as libc::c_ulong) as *mut uint16_t",
        ).unwrap();
        assert_eq!(
            edit,
            "::std::vec![0u16; ((n as libc::c_ulong) as usize)].into_boxed_slice()"
        );
        assert_eq!(receipt, "native-calloc-zero-numeric");
    }

    #[test]
    fn constructor_effectful_count_occurs_once_at_original_initializer() {
        let (_, edit, _) = inspect(
            &format!("{USIZE_CALLOC} fn next(n:&mut i32)->usize {{ *n+=1; *n as usize }}"),
            "f32",
            "calloc(next(&mut n),core::mem::size_of::<f32>()) as *mut f32",
        )
        .unwrap();
        assert_eq!(edit.matches("next(&mut n)").count(), 1);
        assert_eq!(
            edit,
            "::std::vec![0.0f32; ((next(&mut n)) as usize)].into_boxed_slice()"
        );
    }

    #[test]
    fn constructor_faults_require_resolved_c_allocator_and_size_t_abi() {
        for declarations in [
            "unsafe fn calloc(n:usize,s:usize)->*mut core::ffi::c_void { core::ptr::null_mut() }",
            "unsafe extern \"C-unwind\" { fn calloc(n:usize,s:usize)->*mut core::ffi::c_void; }",
            "unsafe extern \"C\" { fn calloc(n:u32,s:u32)->*mut core::ffi::c_void; }",
            "unsafe extern \"C\" { fn calloc(n:u128,s:u128)->*mut core::ffi::c_void; }",
            "unsafe extern \"C\" { fn calloc(n:isize,s:isize)->*mut core::ffi::c_void; }",
            "unsafe extern \"C\" { #[link_name=\"not_calloc\"] fn calloc(n:usize,s:usize)->*mut core::ffi::c_void; }",
            "#[repr(C)] struct FakeVoid { x:u8 } unsafe extern \"C\" { fn calloc(n:usize,s:usize)->*mut FakeVoid; }",
        ] {
            assert_eq!(
                inspect(
                    declarations,
                    "f32",
                    "calloc(2,core::mem::size_of::<f32>() as _) as *mut f32"
                ),
                Err(SourceHold::ConstructorIdentity),
                "{declarations}"
            );
        }
    }

    #[test]
    fn constructor_faults_reject_wrong_size_and_non_numeric_payload() {
        for (extra, element, size) in [
            ("", "u16", "core::mem::size_of::<u32>()"),
            ("fn size_of()->usize { 4 }", "f32", "size_of()"),
            ("", "f32", "core::mem::size_of::<f32>() as u8 as usize"),
            ("", "bool", "core::mem::size_of::<bool>()"),
            ("", "char", "core::mem::size_of::<char>()"),
            (
                "#[derive(Clone,Copy)] struct Pair { a:u8 }",
                "Pair",
                "core::mem::size_of::<Pair>()",
            ),
            ("", "&'static u8", "core::mem::size_of::<&'static u8>()"),
        ] {
            assert_eq!(
                inspect(
                    &format!("{USIZE_CALLOC}{extra}"),
                    element,
                    &format!("calloc(2,{size}) as *mut {element}")
                ),
                Err(SourceHold::ConstructorShape),
                "{element} / {size}"
            );
        }
    }

    #[test]
    fn constructor_fault_literal_zero_and_oversize_remain_held() {
        for count in ["0".to_owned(), usize::MAX.to_string()] {
            assert_eq!(
                inspect(
                    USIZE_CALLOC,
                    "f32",
                    &format!("calloc({count},core::mem::size_of::<f32>()) as *mut f32")
                ),
                Err(SourceHold::ConstructorShape)
            );
        }
    }
}
