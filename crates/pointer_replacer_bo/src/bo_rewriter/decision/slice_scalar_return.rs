//! Complete caller-side use coverage for integer results at forward-slice seams.
//!
//! A pointer-width integer remains a possible pointer carrier. This proof only
//! discharges its returned-child permission when every use destroys that
//! possibility through a scalar comparison or the core integer bit-count
//! operation. It does not certify callee retention, extent, or pointee access.

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::{
    mir::{
        BasicBlock, BinOp, Body, Local, Location, Operand, RETURN_PLACE, Rvalue, Statement,
        StatementKind, TerminatorKind,
        visit::{NonMutatingUseContext, PlaceContext, Visitor},
    },
    ty::{Ty, TyCtxt, TyKind},
};

use super::raw_boundary::{self, RawBoundarySiteKey};

fn integer(ty: Ty<'_>) -> bool {
    matches!(ty.kind(), TyKind::Int(_) | TyKind::Uint(_))
}

fn local(operand: &Operand<'_>) -> Option<Local> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place.as_local(),
        Operand::Constant(_) => None,
    }
}

fn callee(operand: &Operand<'_>) -> Option<DefId> {
    let TyKind::FnDef(definition, _) = *operand.constant()?.ty().kind() else {
        return None;
    };
    Some(definition)
}

/// Require the compiler-resolved inherent method on a core primitive integer.
/// An application function or trait method with the same spelling cannot pass.
fn bit_count<'tcx>(tcx: TyCtxt<'tcx>, definition: DefId, input: Ty<'tcx>) -> bool {
    if definition.is_local()
        || tcx.crate_name(definition.krate).as_str() != "core"
        || tcx.item_name(definition).as_str() != "trailing_zeros"
    {
        return false;
    }
    let Some(implementation) = tcx.impl_of_method(definition) else { return false };
    let signature = tcx.fn_sig(definition).skip_binder().skip_binder();
    integer(input)
        && tcx.trait_id_of_impl(implementation).is_none()
        && tcx.type_of(implementation).instantiate_identity() == input
        && signature.inputs() == [input]
        && !raw_boundary::may_carry_pointer(
            tcx,
            signature.output(),
            raw_boundary::CARRIER_WALK_DEPTH,
        )
}

/// Assignment destinations are definitions; all other MIR local uses,
/// including indices, borrows, casts and inline-assembly operands, are covered.
struct Reads<'a> {
    tracked: &'a FxHashSet<Local>,
    found: bool,
}

impl<'tcx> Visitor<'tcx> for Reads<'_> {
    fn visit_statement(&mut self, statement: &Statement<'tcx>, at: Location) {
        if !matches!(statement.kind, StatementKind::FakeRead(..)) {
            self.super_statement(statement, at);
        }
    }

    fn visit_local(&mut self, local: Local, context: PlaceContext, _: Location) {
        let bookkeeping = matches!(
            context,
            PlaceContext::NonMutatingUse(
                NonMutatingUseContext::FakeBorrow | NonMutatingUseContext::PlaceMention
            )
        );
        if context.is_use()
            && !context.is_place_assignment()
            && !bookkeeping
            && self.tracked.contains(&local)
        {
            self.found = true;
        }
    }
}

fn comparison(operation: BinOp) -> bool {
    matches!(
        operation,
        BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
    )
}

fn transfer_operands<'a, 'tcx>(value: &'a Rvalue<'tcx>) -> Vec<&'a Operand<'tcx>> {
    match value {
        Rvalue::Use(operand) => vec![operand],
        Rvalue::BinaryOp(BinOp::BitXor, operands) => vec![&operands.0, &operands.1],
        _ => Vec::new(),
    }
}

fn scalar_operand<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, operand: &Operand<'tcx>) -> bool {
    integer(operand.ty(body, tcx))
        && (local(operand).is_some() || matches!(operand, Operand::Constant(_)))
}

pub(crate) fn proves(tcx: TyCtxt<'_>, caller: LocalDefId, site: &RawBoundarySiteKey) -> bool {
    if tcx.def_path_str(caller.to_def_id()) != site.caller {
        return false;
    }
    let body = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
    let Some(data) = body.basic_blocks.get(BasicBlock::from_u32(site.block)) else {
        return false;
    };
    if site.statement_index as usize != data.statements.len() {
        return false;
    }
    let TerminatorKind::Call {
        func,
        args,
        destination,
        target: Some(_),
        ..
    } = &data.terminator().kind
    else {
        return false;
    };
    let Some(definition) = callee(func) else { return false };
    let functions = tcx.hir_body_owners().collect::<Vec<_>>();
    if raw_boundary::symbol_key(tcx, definition, &functions) != site.callee
        || site.argument_index >= args.len()
        || !matches!(
            args[site.argument_index]
                .node
                .ty(&body.local_decls, tcx)
                .kind(),
            TyKind::RawPtr(..) | TyKind::Ref(..)
        )
    {
        return false;
    }
    let signature = tcx.fn_sig(definition).skip_binder().skip_binder();
    // This proof covers the returned value only. It must not discharge an
    // independent output-storage channel, even when the return is scalar.
    if signature.c_variadic
        || signature.inputs().iter().any(|input| match input.kind() {
            TyKind::RawPtr(_, mutability) | TyKind::Ref(_, _, mutability) => mutability.is_mut(),
            _ => false,
        })
    {
        return false;
    }
    let Some(root) = destination.as_local() else { return false };
    if !integer(body.local_decls[root].ty) {
        return false;
    }

    // Flow-insensitive closure intentionally overapproximates redefinitions
    // and loop iterations. Thus cycles need no optimistic recursion cutoff.
    let mut edges: FxHashMap<Local, Vec<Local>> = FxHashMap::default();
    for block in body.basic_blocks.iter() {
        for statement in &block.statements {
            let StatementKind::Assign(assignment) = &statement.kind else { continue };
            let Some(destination) = assignment.0.as_local() else { continue };
            if integer(body.local_decls[destination].ty) {
                for operand in transfer_operands(&assignment.1) {
                    if let Some(source) = local(operand) {
                        edges.entry(source).or_default().push(destination);
                    }
                }
            }
        }
    }
    let mut tracked = FxHashSet::default();
    tracked.insert(root);
    let mut pending = vec![root];
    while let Some(source) = pending.pop() {
        for &destination in edges.get(&source).into_iter().flatten() {
            if tracked.insert(destination) {
                pending.push(destination);
            }
        }
    }
    if tracked.contains(&RETURN_PLACE) {
        return false;
    }

    for (block, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, statement) in data.statements.iter().enumerate() {
            let at = Location {
                block,
                statement_index,
            };
            let mut reads = Reads {
                tracked: &tracked,
                found: false,
            };
            reads.visit_statement(statement, at);
            if !reads.found {
                continue;
            }
            let StatementKind::Assign(assignment) = &statement.kind else { return false };
            let Some(destination) = assignment.0.as_local() else { return false };
            match &assignment.1 {
                Rvalue::Use(operand)
                    if scalar_operand(tcx, &body, operand)
                        && integer(body.local_decls[destination].ty) => {}
                Rvalue::BinaryOp(operation, operands)
                    if (*operation == BinOp::BitXor || comparison(*operation))
                        && scalar_operand(tcx, &body, &operands.0)
                        && scalar_operand(tcx, &body, &operands.1) => {}
                _ => return false,
            }
        }
        let at = Location {
            block,
            statement_index: data.statements.len(),
        };
        let mut reads = Reads {
            tracked: &tracked,
            found: false,
        };
        reads.visit_terminator(data.terminator(), at);
        if !reads.found {
            continue;
        }
        let TerminatorKind::Call {
            func,
            args,
            destination,
            target: Some(_),
            ..
        } = &data.terminator().kind
        else {
            return false;
        };
        if args.len() != 1
            || destination.as_local().is_none()
            || !scalar_operand(tcx, &body, &args[0].node)
            || !callee(func).is_some_and(|definition| {
                bit_count(tcx, definition, args[0].node.ty(&body.local_decls, tcx))
            })
        {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check(body: &str, output: &str, accepted: bool) {
        let source = format!(
            "unsafe fn load(p: *const u8) -> u64 {{ *(p as *const u64) }}
             unsafe fn caller(p: *const u8, q: *const u8) -> {output} {{ {body} }}"
        );
        ::utils::compilation::run_compiler_on_str(&source, |tcx| {
            let functions = tcx.hir_body_owners().collect::<Vec<_>>();
            let caller = functions
                .iter()
                .copied()
                .find(|id| tcx.item_name(id.to_def_id()).as_str() == "caller")
                .unwrap();
            let mir = tcx.mir_drops_elaborated_and_const_checked(caller).borrow();
            let (block, data, definition) = mir
                .basic_blocks
                .iter_enumerated()
                .find_map(|(block, data)| {
                    let TerminatorKind::Call { func, .. } = &data.terminator().kind else {
                        return None;
                    };
                    let definition = callee(func)?;
                    (tcx.item_name(definition).as_str() == "load")
                        .then_some((block, data, definition))
                })
                .unwrap();
            let key = RawBoundarySiteKey {
                caller: tcx.def_path_str(caller.to_def_id()),
                block: block.as_u32(),
                statement_index: data.statements.len() as u32,
                callee: raw_boundary::symbol_key(tcx, definition, &functions),
                argument_index: 0,
                subject: "predicate-test".into(),
            };
            assert_eq!(proves(tcx, caller, &key), accepted, "{body}");
        })
        .expect("scalar-use fixture compiles");
    }

    #[test]
    fn wave6s_scalar_result_brotli_xor_bit_count() {
        check(
            "let a = load(p); let b = load(q); if a != b { ((a ^ b).trailing_zeros() >> 3) as usize } else { 8 }",
            "usize",
            true,
        );
    }

    #[test]
    fn wave6s_scalar_result_loop_redefinitions_are_covered() {
        check(
            "let mut n = 0; while n < 8 { let a = load(p); let b = load(q); if a != b { return ((a ^ b).trailing_zeros() >> 3) as usize; } n += 1; } n",
            "usize",
            true,
        );
    }

    #[test]
    fn wave6s_scalar_result_outward_return_is_held() {
        check("load(p)", "u64", false);
    }

    #[test]
    fn wave6s_scalar_result_pointer_reconstruction_is_held() {
        check(
            "let a = load(p); *(a as *const u8) as usize",
            "usize",
            false,
        );
    }

    #[test]
    fn wave6s_scalar_result_same_spelled_local_method_is_held() {
        check(
            "fn trailing_zeros(x: u64) -> u32 { x as u32 } let a = load(p); trailing_zeros(a) as usize",
            "usize",
            false,
        );
    }

    #[test]
    fn wave6s_scalar_result_storage_and_address_are_held() {
        check("let a = load(p); *(q as *mut u64) = a; 0", "usize", false);
        check(
            "let a = load(p); let address = &a; *address as usize",
            "usize",
            false,
        );
    }
}
