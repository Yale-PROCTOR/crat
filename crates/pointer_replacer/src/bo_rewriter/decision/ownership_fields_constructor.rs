//! R376 source-identified zeroed numeric boxed-slice constructors.
use rustc_hir::{Expr, ExprKind, Node, QPath, def::Res};
use rustc_middle::ty::{FloatTy, IntTy, Ty, TyCtxt, TyKind, UintTy};
use rustc_span::{
    Symbol,
    def_id::{DefId, LocalDefId},
};

use super::{box_facts::BoxExprEdit, ownership_fields_source::SourceHold};

pub(crate) struct Constructor<'tcx> {
    pub(crate) allocation: &'tcx Expr<'tcx>,
    pub(crate) allocator: DefId,
    pub(crate) element: Ty<'tcx>,
    pub(crate) count: String,
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
    let (zero, element_bits) = numeric_zero(element, pointer_bits)?;
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
    // calloc takes size_t: both unsigned arguments must have pointer width.
    if symbol.as_str() != "calloc"
        || signature.c_variadic
        || signature.abi != (rustc_abi::ExternAbi::C { unwind: false })
        || signature.inputs().len() != 2
        || signature
            .inputs()
            .iter()
            .any(|ty| unsigned_bits(*ty, pointer_bits) != Some(pointer_bits))
        || !matches!(signature.output().kind(), TyKind::RawPtr(pointee, rustc_hir::Mutability::Mut)
            if matches!(pointee.kind(), TyKind::Adt(def, _) if Some(def.did()) == tcx.lang_items().c_void()))
    {
        return Err(SourceHold::ConstructorIdentity);
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
                .find(|owner| tcx.item_name(owner.to_def_id()).as_str() == "probe")
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
