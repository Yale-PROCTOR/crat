//! R365 native constructor/free source proofs for straight-line scalar buffers.
//! Source occurrence identity is not allocation-generation identity. Ordinary
//! call and generated-unwind obligations remain explicit for the bundle owner.
use std::collections::{BTreeMap, BTreeSet};

use rustc_hir::{
    Expr, ExprKind, HirId, Node, QPath,
    def::Res,
    intravisit::{self, Visitor},
};
use rustc_middle::{
    mir::{BasicBlock, CastKind, Local, Operand, Rvalue, StatementKind, TerminatorKind},
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_span::{
    Span, Symbol,
    def_id::{DefId, LocalDefId},
};

use super::{Subject, box_facts::BoxExprEdit, construction::ConstructionFacts};
use crate::utils::rustc::RustProgram;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct SourceCallKey {
    pub(crate) owner: u32,
    pub(crate) call_hir: u32,
    pub(crate) block: u32,
    pub(crate) statement: usize,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum SourceHold {
    Missing(&'static str),
    Identity,
    ConstructorIdentity,
    ConstructorShape,
    UnsupportedOwnerUse,
    FreeIdentity,
    NormalExitCoverage,
    UnsupportedControlFlow,
    Duplicate(SourceCallKey),
    Unexpected(SourceCallKey),
    Absent(SourceCallKey),
}
#[derive(Clone, Debug)]
pub(crate) struct CallObligation {
    key: SourceCallKey,
    callee: DefId,
    argument: usize,
    argument_span: Span,
    call_span: Span,
}
impl CallObligation {
    pub(crate) fn key(&self) -> SourceCallKey {
        self.key
    }

    pub(crate) fn callee(&self) -> DefId {
        self.callee
    }

    pub(crate) fn argument(&self) -> usize {
        self.argument
    }

    pub(crate) fn argument_span(&self) -> Span {
        self.argument_span
    }

    pub(crate) fn call_span(&self) -> Span {
        self.call_span
    }
}
#[derive(Clone, Debug)]
pub(crate) struct SourceFreeSite {
    key: SourceCallKey,
    owner: LocalDefId,
    binding: HirId,
    callee: DefId,
    span: Span,
    root_spelling: String,
}
impl SourceFreeSite {
    pub(crate) fn key(&self) -> SourceCallKey {
        self.key
    }

    pub(crate) fn span(&self) -> Span {
        self.span
    }

    pub(crate) fn owner(&self) -> LocalDefId {
        self.owner
    }

    pub(crate) fn binding(&self) -> HirId {
        self.binding
    }

    pub(crate) fn callee(&self) -> DefId {
        self.callee
    }
}
/// Structural source permit only. The final bundle must discharge every call
/// and unwind obligation before treating these source edits as admissible.
#[derive(Clone, Debug)]
pub(crate) struct SourcePlan {
    owner: LocalDefId,
    binding: HirId,
    count: usize,
    constructor: BoxExprEdit,
    scalar_edits: Vec<BoxExprEdit>,
    frees: Vec<SourceFreeSite>,
    calls: Vec<CallObligation>,
    /// Every intervening native call while this root is live, including other
    /// allocations whose emitted helpers may unwind. Never inferred empty from
    /// `retained_sink`, and never itself an R101 waiver authorization.
    unwind_obligations: Vec<SourceCallKey>,
    mir_aliases: BTreeSet<u32>,
}
impl SourcePlan {
    pub(crate) fn owner(&self) -> LocalDefId {
        self.owner
    }

    pub(crate) fn binding(&self) -> HirId {
        self.binding
    }

    pub(crate) fn count(&self) -> usize {
        self.count
    }

    pub(crate) fn constructor(&self) -> &BoxExprEdit {
        &self.constructor
    }

    pub(crate) fn scalar_edits(&self) -> &[BoxExprEdit] {
        &self.scalar_edits
    }

    pub(crate) fn frees(&self) -> &[SourceFreeSite] {
        &self.frees
    }

    pub(crate) fn calls(&self) -> &[CallObligation] {
        &self.calls
    }

    pub(crate) fn unwind_obligations(&self) -> &[SourceCallKey] {
        &self.unwind_obligations
    }

    pub(crate) fn mir_aliases(&self) -> &BTreeSet<u32> {
        &self.mir_aliases
    }
}

impl super::super::ownership_fields::free_sites::FreePlanSite for SourceFreeSite {
    type Emitted = BoxExprEdit;
    type Hold = SourceHold;
    type Key = SourceCallKey;

    fn key(&self) -> &Self::Key {
        &self.key
    }

    fn missing(key: Self::Key) -> Self::Hold {
        SourceHold::Absent(key)
    }

    fn extra(key: Self::Key) -> Self::Hold {
        SourceHold::Unexpected(key)
    }

    fn duplicate(key: Self::Key) -> Self::Hold {
        SourceHold::Duplicate(key)
    }

    fn plan(&self) -> Result<Self::Emitted, Self::Hold> {
        // These private fields exist only after the constructor/owner-root,
        // exact native free and complete normal-path checks below. This edit
        // is still conditional on SourcePlan's explicit bundle obligations.
        Ok(BoxExprEdit {
            span: self.span,
            replacement: format!("::std::mem::drop({})", self.root_spelling),
            receipt: "c-free-site-drop",
        })
    }
}

#[derive(Default)]
struct Expressions<'tcx>(Vec<&'tcx Expr<'tcx>>);
impl<'tcx> Visitor<'tcx> for Expressions<'tcx> {
    fn visit_expr(&mut self, expression: &'tcx Expr<'tcx>) {
        self.0.push(expression);
        intravisit::walk_expr(self, expression);
    }
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
fn void_pointer(tcx: TyCtxt<'_>, ty: Ty<'_>) -> bool {
    matches!(ty.kind(), TyKind::RawPtr(pointee, rustc_hir::Mutability::Mut)
        if matches!(pointee.kind(), TyKind::Adt(def, _) if Some(def.did()) == tcx.lang_items().c_void()))
}
fn c_function(tcx: TyCtxt<'_>, callee: DefId, expected: &str) -> bool {
    let Some(local) = callee.as_local() else { return false };
    if !matches!(tcx.hir_node_by_def_id(local), Node::ForeignItem(_)) {
        return false;
    }
    let symbol = tcx
        .codegen_fn_attrs(callee)
        .link_name
        .unwrap_or_else(|| tcx.item_name(callee));
    let sig = tcx.fn_sig(callee).skip_binder().skip_binder();
    if symbol.as_str() != expected
        || sig.c_variadic
        || sig.abi != (rustc_abi::ExternAbi::C { unwind: false })
    {
        return false;
    }
    match expected {
        "calloc" => {
            sig.inputs() == [tcx.types.usize, tcx.types.usize] && void_pointer(tcx, sig.output())
        }
        "free" => {
            sig.inputs().len() == 1 && void_pointer(tcx, sig.inputs()[0]) && sig.output().is_unit()
        }
        _ => false,
    }
}
fn peel<'tcx>(
    mut expression: &'tcx Expr<'tcx>,
    typeck: &rustc_middle::ty::TypeckResults<'tcx>,
) -> Result<&'tcx Expr<'tcx>, SourceHold> {
    while let ExprKind::Cast(inner, _) = expression.kind {
        if !matches!(typeck.expr_ty(expression).kind(), TyKind::RawPtr(..))
            || !matches!(typeck.expr_ty(inner).kind(), TyKind::RawPtr(..))
        {
            return Err(SourceHold::UnsupportedOwnerUse);
        }
        expression = inner;
    }
    Ok(expression)
}
fn root_path(expression: &Expr<'_>, binding: HirId) -> bool {
    matches!(expression.kind, ExprKind::Path(QPath::Resolved(_, path))
        if path.res == Res::Local(binding))
}
fn plain_local(operand: &Operand<'_>) -> Option<Local> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place.as_local(),
        Operand::Constant(_) => None,
    }
}
struct MirCall<'tcx> {
    key: SourceCallKey,
    expression: &'tcx Expr<'tcx>,
    callee: DefId,
    destination: Option<Local>,
}

pub(crate) fn derive<'tcx>(
    program: &RustProgram<'tcx>,
    subject: &Subject,
    constructions: &ConstructionFacts,
) -> Result<SourcePlan, SourceHold> {
    let tcx = program.tcx;
    if !program.functions.contains(&subject.fn_did)
        || subject.hir_id.owner.def_id != subject.fn_did
        || !matches!(subject.kind, super::SubjectKind::Local)
        || subject.ptr_depth != 1
    {
        return Err(SourceHold::Identity);
    }
    let body = tcx
        .mir_drops_elaborated_and_const_checked(subject.fn_did)
        .borrow();
    if !matches!(body.local_decls[subject.local].ty.kind(), TyKind::RawPtr(pointee, rustc_hir::Mutability::Mut) if *pointee == tcx.types.f32)
    {
        return Err(SourceHold::ConstructorShape);
    }
    let key = (subject.fn_did, subject.hir_id);
    let init_hir = *constructions
        .init_hirs
        .get(&key)
        .ok_or(SourceHold::Missing("initializer-hir"))?;
    let Node::Expr(init) = tcx.hir_node(init_hir) else { return Err(SourceHold::Identity) };
    if constructions.init_spans.get(&key) != Some(&init.span) {
        return Err(SourceHold::Identity);
    }
    let typeck = tcx.typeck(subject.fn_did);
    let allocation = peel(init, typeck)?;
    let ExprKind::Call(callee_expression, arguments) = allocation.kind else {
        return Err(SourceHold::ConstructorShape);
    };
    let allocator = definition(callee_expression).ok_or(SourceHold::ConstructorIdentity)?;
    if !c_function(tcx, allocator, "calloc") {
        return Err(SourceHold::ConstructorIdentity);
    }
    let [count_expression, size_expression] = arguments else {
        return Err(SourceHold::ConstructorShape);
    };
    let ExprKind::Lit(literal) = count_expression.kind else {
        return Err(SourceHold::ConstructorShape);
    };
    let rustc_ast::LitKind::Int(value, _) = literal.node else {
        return Err(SourceHold::ConstructorShape);
    };
    let count = usize::try_from(value.get())
        .ok()
        .filter(|n| *n > 0)
        .ok_or(SourceHold::ConstructorShape)?;
    // The exact bounded f32 layout, not the old snippet `contains(size_of)`.
    let pointer_bits = tcx.data_layout.pointer_size.bits();
    let maximum_bytes = 1u128
        .checked_shl((pointer_bits - 1) as u32)
        .and_then(|limit| limit.checked_sub(1))
        .ok_or(SourceHold::ConstructorShape)?;
    if (count as u128)
        .checked_mul(4)
        .is_none_or(|bytes| bytes > maximum_bytes)
    {
        return Err(SourceHold::ConstructorShape);
    }
    let ExprKind::Call(size_callee, size_arguments) = size_expression.kind else {
        return Err(SourceHold::ConstructorShape);
    };
    let size_definition = definition(size_callee).ok_or(SourceHold::ConstructorShape)?;
    if !size_arguments.is_empty()
        || !tcx.is_diagnostic_item(Symbol::intern("mem_size_of"), size_definition)
        || !matches!(typeck.expr_ty(size_callee).kind(), TyKind::FnDef(did, args) if *did == size_definition && args.type_at(0) == tcx.types.f32)
    {
        return Err(SourceHold::ConstructorShape);
    }
    let Node::Pat(pattern) = tcx.hir_node(subject.hir_id) else { return Err(SourceHold::Identity) };
    let rustc_hir::PatKind::Binding(_, binding, ident, None) = pattern.kind else {
        return Err(SourceHold::Identity);
    };
    if binding != subject.hir_id {
        return Err(SourceHold::Identity);
    }
    let root_spelling = tcx
        .sess
        .source_map()
        .span_to_snippet(ident.span)
        .map_err(|_| SourceHold::Missing("root-spelling"))?;
    let body_id = tcx
        .hir_node_by_def_id(subject.fn_did)
        .body_id()
        .ok_or(SourceHold::Identity)?;
    let mut expressions = Expressions::default();
    expressions.visit_body(tcx.hir_body(body_id));
    // Whole-caller reference/closure absence is a deliberately narrow scope.
    // Merely recognizing the scalar deref nested inside &*root is not enough.
    if expressions.0.iter().any(|e| {
        matches!(
            e.kind,
            ExprKind::AddrOf(..) | ExprKind::Closure(..) | ExprKind::InlineAsm(..)
        ) || matches!(typeck.expr_ty(e).kind(), TyKind::Ref(..))
    }) {
        return Err(SourceHold::UnsupportedOwnerUse);
    }
    let mut covered = BTreeSet::new();
    let mut scalar_edits = Vec::new();
    let mut root_calls = Vec::new();
    for &expression in &expressions.0 {
        if let ExprKind::Unary(rustc_hir::UnOp::Deref, operand) = expression.kind
            && root_path(operand, binding)
        {
            if typeck.expr_ty(expression) != tcx.types.f32 {
                return Err(SourceHold::UnsupportedOwnerUse);
            }
            covered.insert(operand.hir_id.local_id.as_u32());
            scalar_edits.push(BoxExprEdit {
                span: expression.span,
                replacement: format!("{root_spelling}[0]"),
                receipt: "native-box-scalar-access",
            });
        }
        if let ExprKind::Call(callee, arguments) = expression.kind {
            for (index, argument) in arguments.iter().enumerate() {
                let Ok(operand) = peel(argument, typeck) else { continue };
                if !root_path(operand, binding) {
                    continue;
                }
                let did = definition(callee).ok_or(SourceHold::UnsupportedOwnerUse)?;
                // Returned pointers need their own explicit owner/view protocol.
                if !typeck.expr_ty(expression).is_unit() {
                    return Err(SourceHold::UnsupportedOwnerUse);
                }
                covered.insert(operand.hir_id.local_id.as_u32());
                root_calls.push((expression, did, index, argument.span));
            }
        }
    }
    let all_uses: BTreeSet<_> = expressions
        .0
        .iter()
        .filter(|e| root_path(e, binding))
        .map(|e| e.hir_id.local_id.as_u32())
        .collect();
    if all_uses != covered {
        return Err(SourceHold::UnsupportedOwnerUse);
    }

    // Join every native MIR call to exactly one resolved HIR call. The key
    // includes both identities; no source-order zip or name repair is used.
    let mut mir_calls = BTreeMap::new();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        let TerminatorKind::Call {
            func, destination, ..
        } = &data.terminator().kind
        else {
            continue;
        };
        let did = func
            .constant()
            .and_then(|c| match c.ty().kind() {
                TyKind::FnDef(did, _) => Some(*did),
                _ => None,
            })
            .ok_or(SourceHold::UnsupportedControlFlow)?;
        let span = data.terminator().source_info.span.source_callsite();
        let matches: Vec<_> = expressions
            .0
            .iter()
            .copied()
            .filter(|e| {
                matches!(e.kind, ExprKind::Call(callee, _) if definition(callee) == Some(did))
                    && e.span.source_callsite() == span
            })
            .collect();
        let [expression] = matches.as_slice() else {
            return Err(SourceHold::Missing("hir-mir-call-join"));
        };
        let key = SourceCallKey {
            owner: subject.fn_did.local_def_index.as_u32(),
            call_hir: expression.hir_id.local_id.as_u32(),
            block: block.as_u32(),
            statement: data.statements.len(),
        };
        mir_calls.insert(
            block,
            MirCall {
                key,
                expression,
                callee: did,
                destination: destination.as_local(),
            },
        );
    }
    let allocations: Vec<_> = mir_calls
        .values()
        .filter(|c| c.expression.hir_id == allocation.hir_id && c.callee == allocator)
        .collect();
    let [allocation_call] = allocations.as_slice() else {
        return Err(SourceHold::ConstructorIdentity);
    };
    let allocator_destination = allocation_call
        .destination
        .ok_or(SourceHold::ConstructorShape)?;
    let mut aliases = BTreeSet::from([subject.local.as_u32()]);
    loop {
        let before = aliases.len();
        for data in body.basic_blocks.iter() {
            for statement in &data.statements {
                let StatementKind::Assign(box (destination, rvalue)) = &statement.kind else {
                    continue;
                };
                let Some(destination) = destination.as_local() else { continue };
                let operand = match rvalue {
                    Rvalue::Use(operand) | Rvalue::Cast(CastKind::PtrToPtr, operand, _) => operand,
                    _ => continue,
                };
                let Some(source) = plain_local(operand) else { continue };
                if !matches!(body.local_decls[destination].ty.kind(), TyKind::RawPtr(..))
                    || !matches!(body.local_decls[source].ty.kind(), TyKind::RawPtr(..))
                {
                    continue;
                }
                if aliases.contains(&source.as_u32()) || aliases.contains(&destination.as_u32()) {
                    aliases.insert(source.as_u32());
                    aliases.insert(destination.as_u32());
                }
            }
        }
        if before == aliases.len() {
            break;
        }
    }
    if !aliases.contains(&allocator_destination.as_u32()) {
        return Err(SourceHold::ConstructorIdentity);
    }
    for call in mir_calls.values() {
        if call
            .destination
            .is_some_and(|local| aliases.contains(&local.as_u32()))
            && call.key != allocation_call.key
        {
            return Err(SourceHold::UnsupportedOwnerUse);
        }
    }
    let mut frees = Vec::new();
    let mut calls = Vec::new();
    for (expression, callee, argument, argument_span) in root_calls {
        let matched: Vec<_> = mir_calls
            .values()
            .filter(|c| c.expression.hir_id == expression.hir_id && c.callee == callee)
            .collect();
        let [call] = matched.as_slice() else { return Err(SourceHold::Missing("owner-call-join")) };
        let data = &body.basic_blocks[BasicBlock::from_u32(call.key.block)];
        let TerminatorKind::Call { args, .. } = &data.terminator().kind else {
            return Err(SourceHold::Identity);
        };
        let actual = args
            .get(argument)
            .and_then(|arg| plain_local(&arg.node))
            .ok_or(SourceHold::UnsupportedOwnerUse)?;
        if !aliases.contains(&actual.as_u32()) {
            return Err(SourceHold::Identity);
        }
        if c_function(tcx, callee, "free") {
            if argument != 0 {
                return Err(SourceHold::FreeIdentity);
            }
            frees.push(SourceFreeSite {
                key: call.key,
                owner: subject.fn_did,
                binding,
                callee,
                span: expression.span,
                root_spelling: root_spelling.clone(),
            });
        } else {
            calls.push(CallObligation {
                key: call.key,
                callee,
                argument,
                argument_span,
                call_span: expression.span,
            });
        }
    }
    if frees.len() != 1 {
        return Err(SourceHold::FreeIdentity);
    }
    let free = &frees[0];
    if free.span.lo() < init.span.hi()
        || scalar_edits
            .iter()
            .any(|edit| edit.span.lo() < init.span.hi() || edit.span.hi() > free.span.lo())
        || calls.iter().any(|call| {
            call.call_span.lo() < init.span.hi() || call.call_span.hi() > free.span.lo()
        })
    {
        return Err(SourceHold::UnsupportedOwnerUse);
    }
    // All normal control flow is linear in this first native fragment. Reject
    // every branch/cycle instead of inferring a sink on the unvisited arm.
    let mut block = BasicBlock::from_u32(0);
    let mut visited = BTreeSet::new();
    let mut allocated = false;
    let mut freed = false;
    let mut unwind_obligations = Vec::new();
    loop {
        if !visited.insert(block.as_u32()) {
            return Err(SourceHold::UnsupportedControlFlow);
        }
        let data = &body.basic_blocks[block];
        if let Some(call) = mir_calls.get(&block) {
            if call.key == allocation_call.key {
                if allocated {
                    return Err(SourceHold::NormalExitCoverage);
                }
                allocated = true;
            } else if call.key == free.key {
                if !allocated || freed {
                    return Err(SourceHold::NormalExitCoverage);
                }
                freed = true;
            } else if allocated && !freed {
                unwind_obligations.push(call.key);
            }
        }
        match data.terminator().kind {
            TerminatorKind::Goto { target }
            | TerminatorKind::Call {
                target: Some(target),
                ..
            } => block = target,
            TerminatorKind::Return if allocated && freed => break,
            TerminatorKind::Return => return Err(SourceHold::NormalExitCoverage),
            _ => return Err(SourceHold::UnsupportedControlFlow),
        }
    }
    if mir_calls
        .values()
        .any(|call| !visited.contains(&call.key.block))
    {
        return Err(SourceHold::UnsupportedControlFlow);
    }
    Ok(SourcePlan {
        owner: subject.fn_did,
        binding,
        count,
        constructor: BoxExprEdit {
            span: init.span,
            replacement: format!("::std::vec![0.0f32; {count}].into_boxed_slice()"),
            receipt: "native-calloc-zero-f32",
        },
        scalar_edits,
        frees,
        calls,
        unwind_obligations,
        mir_aliases: aliases,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bo_rewriter as bo;

    fn inspect(source: &str, name: &str) -> Result<(usize, usize, usize, usize), SourceHold> {
        let name = name.to_owned();
        ::utils::compilation::run_compiler_on_str(source, move |tcx| {
            let (table, ctx) = bo::decide_table_with_ctx_config(
                tcx,
                Some((
                    bo::A5Mode::PreciseReplay,
                    Some(bo::WholeProgramAttestation::FrozenBenchmarkGraph),
                )),
            )
            .expect("native source fixture analysis");
            let program = bo::collect_program(tcx);
            let subjects: Vec<_> = table
                .entries
                .iter()
                .filter(|(subject, _)| subject.param_name.as_deref() == Some(name.as_str()))
                .collect();
            assert_eq!(subjects.len(), 1);
            let plan = derive(&program, &subjects[0].0, &ctx.constructions)?;
            assert_eq!(plan.binding(), subjects[0].0.hir_id);
            assert_eq!(plan.owner(), subjects[0].0.fn_did);
            assert_eq!(plan.constructor().receipt, "native-calloc-zero-f32");
            assert!(plan.constructor().replacement.contains("into_boxed_slice"));
            for free in plan.frees() {
                assert_eq!(free.binding(), plan.binding());
                assert_eq!(free.owner(), plan.owner());
                assert!(
                    tcx.sess
                        .source_map()
                        .span_to_snippet(free.span())
                        .unwrap()
                        .starts_with("free(")
                );
            }
            Ok((
                plan.count(),
                plan.frees().len(),
                plan.calls().len(),
                plan.unwind_obligations().len(),
            ))
        })
        .expect("native source fixture compiles")
    }

    #[test]
    fn source_two_buffer_constructor_free_and_unwind_inventory() {
        let source = bo::ownership_fields_native_tests::native_fixture_source(
            "edt_with_payload",
            "edt_with_payload(pl1,pl2);",
        );
        for name in ["pl1", "pl2"] {
            let (count, frees, calls, unwinds) = inspect(&source, name).unwrap();
            assert_eq!((count, frees, calls), (2, 1, 1));
            assert!(
                unwinds >= 1,
                "the ordinary call's generated unwind remains owed"
            );
        }
    }
    #[test]
    fn source_repeated_calls_keep_exact_owner_and_free() {
        let source = bo::ownership_fields_native_tests::native_fixture_source(
            "edt",
            "edt(pl1,pl2);*pl1=*pl2;edt(pl1,pl2);",
        );
        for name in ["pl1", "pl2"] {
            let (count, frees, calls, unwinds) = inspect(&source, name).unwrap();
            assert_eq!((count, frees, calls), (2, 1, 2));
            assert!(unwinds >= 2);
        }
    }
    #[test]
    fn source_missing_free_is_not_no_extra_close_evidence() {
        let source =
            bo::ownership_fields_native_tests::native_fixture_source("edt", "edt(pl1,pl2);")
                .replace("free(pl1 as *mut core::ffi::c_void);", "");
        assert!(matches!(
            inspect(&source, "pl1"),
            Err(SourceHold::FreeIdentity | SourceHold::NormalExitCoverage)
        ));
    }
    #[test]
    fn source_pointer_reassignment_and_escape_hold() {
        let source = bo::ownership_fields_native_tests::native_fixture_source(
            "edt",
            "pl1=pl2;edt(pl1,pl2);",
        );
        assert!(matches!(
            inspect(&source, "pl1"),
            Err(SourceHold::UnsupportedOwnerUse)
        ));
    }
    #[test]
    fn source_reference_and_raw_address_ancestors_hold() {
        for extra in [
            "let r = &*pl1;",
            "let r = &raw const *pl1;",
            "let alias = pl1;",
        ] {
            let source = bo::ownership_fields_native_tests::native_fixture_source(
                "edt",
                &format!("{extra} edt(pl1,pl2);"),
            );
            assert!(matches!(
                inspect(&source, "pl1"),
                Err(SourceHold::UnsupportedOwnerUse)
            ));
        }
    }
    #[test]
    fn source_pointer_returning_call_is_not_a_lend() {
        let source = bo::ownership_fields_native_tests::native_fixture_source(
            "edt",
            "edt(pl1,pl2);",
        )
        .replace(
            "unsafe fn edt(input:*mut f32,output:*mut f32) { *output=*input+1.0; }",
            "unsafe fn edt(input:*mut f32,output:*mut f32)->*mut f32 { *output=*input+1.0; input }",
        );
        assert!(matches!(
            inspect(&source, "pl1"),
            Err(SourceHold::UnsupportedOwnerUse)
        ));
    }
    #[test]
    fn source_local_allocator_impostor_is_not_a_c_contract() {
        let source = bo::ownership_fields_native_tests::native_fixture_source("edt", "edt(pl1,pl2);")
            .replace("fn calloc(count:usize,size:usize)->*mut core::ffi::c_void;", "")
            .replace("unsafe fn edt", "unsafe fn calloc(count:usize,size:usize)->*mut core::ffi::c_void { core::ptr::null_mut() } unsafe fn edt");
        assert!(matches!(
            inspect(&source, "pl1"),
            Err(SourceHold::ConstructorIdentity)
        ));
    }

    #[test]
    fn source_zero_count_is_not_a_nonempty_constructor() {
        let source =
            bo::ownership_fields_native_tests::native_fixture_source("edt", "edt(pl1,pl2);")
                .replace("calloc(2,", "calloc(0,");
        assert!(matches!(
            inspect(&source, "pl1"),
            Err(SourceHold::ConstructorShape)
        ));
    }
}
