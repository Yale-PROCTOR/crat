//! Exactly-once retirement of one formal root, bound to native source events.
//!
//! The ownership inventory supplies identities, not an all-paths proof. This
//! consumer additionally checks native MIR; unsupported effects remain held.
use std::collections::{BTreeMap, BTreeSet};

use rustc_hir::Node;
use rustc_middle::{
    mir::{
        Local, Location, Operand, Place, Rvalue, START_BLOCK, StatementKind, TerminatorKind,
        visit::{PlaceContext, Visitor},
    },
    ty::{Ty, TyCtxt, TyKind},
};
use rustc_span::def_id::{DefId, LocalDefId};

use crate::{
    analyses::borrow_ownership::{
        export::PlaceKey,
        source_events::{
            self, SourceCondition, SourceEventKey, SourceEvents, SourceObject, SourcePhase,
            SourceRole,
        },
    },
    utils::rustc::RustProgram,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Hold {
    Signature,
    Unsupported,
    MissingRetirement,
    Identity,
    RootUse,
    AlreadyFreed,
    PathCoverage,
    Recursion,
}

/// Cannot be manufactured from model Owning or a function-name match.
pub(crate) struct Proof<'a, 'tcx> {
    program: &'a RustProgram<'tcx>,
    callee: LocalDefId,
    argument: usize,
    events: Vec<SourceEventKey>,
}
impl std::fmt::Debug for Proof<'_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DeallocatorProof")
            .field("callee", &self.callee)
            .field("argument", &self.argument)
            .field("events", &self.events)
            .finish()
    }
}
impl<'tcx> Proof<'_, 'tcx> {
    pub(crate) fn matches(
        &self,
        program: &RustProgram<'tcx>,
        callee: LocalDefId,
        argument: usize,
    ) -> bool {
        std::ptr::eq(self.program, program) && self.callee == callee && self.argument == argument
    }

    pub(crate) fn events(&self) -> &[SourceEventKey] {
        &self.events
    }
}

fn primitive(ty: Ty<'_>) -> bool {
    ty.is_unit()
        || matches!(
            ty.kind(),
            TyKind::RawPtr(..)
                | TyKind::Bool
                | TyKind::Char
                | TyKind::Int(..)
                | TyKind::Uint(..)
                | TyKind::Float(..)
        )
}
fn canonical_free(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    let Some(local) = callee.as_local() else { return false };
    if !matches!(tcx.hir_node_by_def_id(local), Node::ForeignItem(_)) {
        return false;
    }
    let symbol = tcx
        .codegen_fn_attrs(callee)
        .link_name
        .unwrap_or_else(|| tcx.item_name(callee));
    let sig = tcx.fn_sig(callee).skip_binder().skip_binder();
    symbol.as_str() == "free"
        && !sig.c_variadic
        && sig.abi == (rustc_abi::ExternAbi::C { unwind: false })
        && sig.output().is_unit()
        && matches!(sig.inputs(), [ty] if matches!(ty.kind(), TyKind::RawPtr(pointee, rustc_hir::Mutability::Mut)
            if matches!(pointee.kind(), TyKind::Adt(def, _) if Some(def.did()) == tcx.lang_items().c_void())))
}
fn root(operand: &Operand<'_>, aliases: &BTreeSet<Local>) -> bool {
    operand
        .place()
        .and_then(|place| place.as_local())
        .is_some_and(|local| aliases.contains(&local))
}
struct Reads<'a> {
    aliases: &'a BTreeSet<Local>,
    found: bool,
}
impl<'tcx> Visitor<'tcx> for Reads<'_> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        self.found |= self.aliases.contains(&place.local);
        self.super_place(place, context, location);
    }
}

pub(crate) fn derive<'a, 'tcx>(
    program: &'a RustProgram<'tcx>,
    callee: LocalDefId,
    argument: usize,
) -> Result<Proof<'a, 'tcx>, Hold> {
    let inventory = source_events::for_construction(program);
    let events = body_proof(program, &inventory, callee, argument, &mut BTreeSet::new())?;
    Ok(Proof {
        program,
        callee,
        argument,
        events: events.into_keys().collect(),
    })
}

fn body_proof(
    program: &RustProgram<'_>,
    inventory: &SourceEvents,
    callee: LocalDefId,
    argument: usize,
    stack: &mut BTreeSet<u32>,
) -> Result<BTreeMap<SourceEventKey, ()>, Hold> {
    if stack.len() >= 4 || !stack.insert(callee.local_def_index.as_u32()) {
        return Err(Hold::Recursion);
    }
    let result = check_body(program, inventory, callee, argument, stack);
    stack.remove(&callee.local_def_index.as_u32());
    result
}
fn check_body(
    program: &RustProgram<'_>,
    inventory: &SourceEvents,
    callee: LocalDefId,
    argument: usize,
    stack: &mut BTreeSet<u32>,
) -> Result<BTreeMap<SourceEventKey, ()>, Hold> {
    if !program.functions.contains(&callee) {
        return Err(Hold::Identity);
    }
    let tcx = program.tcx;
    let body = tcx.mir_drops_elaborated_and_const_checked(callee).borrow();
    let formal = Local::from_usize(argument + 1);
    if argument >= body.arg_count
        || !body.return_ty().is_unit()
        || !matches!(body.local_decls[formal].ty.kind(), TyKind::RawPtr(..))
        || body.local_decls.iter().any(|decl| !primitive(decl.ty))
    {
        return Err(Hold::Signature);
    }
    let function = tcx.def_path_str(callee.to_def_id());
    let mut pending = vec![(
        START_BLOCK,
        BTreeSet::from([formal]),
        false,
        BTreeSet::new(),
    )];
    let mut events = BTreeMap::new();
    let mut returns = 0;
    let mut budget = 512;
    while let Some((block, mut aliases, mut freed, mut visited)) = pending.pop() {
        if budget == 0 || !visited.insert(block) {
            return Err(Hold::PathCoverage);
        }
        budget -= 1;
        let data = &body.basic_blocks[block];
        for (statement_index, statement) in data.statements.iter().enumerate() {
            match &statement.kind {
                StatementKind::StorageLive(_)
                | StatementKind::StorageDead(_)
                | StatementKind::FakeRead(..)
                | StatementKind::PlaceMention(..)
                | StatementKind::AscribeUserType(..)
                | StatementKind::Nop => {}
                StatementKind::Assign(box (destination, value)) => {
                    let Some(local) = destination.as_local() else { return Err(Hold::RootUse) };
                    let copied_root = match value {
                        Rvalue::Use(operand) | Rvalue::Cast(_, operand, _) => {
                            root(operand, &aliases)
                                && matches!(body.local_decls[local].ty.kind(), TyKind::RawPtr(..))
                        }
                        _ => false,
                    };
                    let mut reads = Reads {
                        aliases: &aliases,
                        found: false,
                    };
                    reads.visit_rvalue(
                        value,
                        Location {
                            block,
                            statement_index,
                        },
                    );
                    if reads.found && (!copied_root || freed) {
                        return Err(if freed {
                            Hold::AlreadyFreed
                        } else {
                            Hold::RootUse
                        });
                    }
                    if copied_root {
                        aliases.insert(local);
                    } else {
                        aliases.remove(&local);
                    }
                }
                _ => return Err(Hold::Unsupported),
            }
        }
        let location = Location {
            block,
            statement_index: data.statements.len(),
        };
        let successors = match &data.terminator().kind {
            TerminatorKind::Return => {
                if !freed {
                    return Err(Hold::MissingRetirement);
                }
                returns += 1;
                Vec::new()
            }
            TerminatorKind::Goto { target } => vec![*target],
            TerminatorKind::SwitchInt { discr, targets } => {
                if root(discr, &aliases) {
                    return Err(Hold::RootUse);
                }
                targets.all_targets().to_vec()
            }
            TerminatorKind::Call {
                func,
                args,
                target: Some(target),
                destination,
                ..
            } => {
                if freed {
                    return Err(Hold::AlreadyFreed);
                }
                let target_def = func
                    .constant()
                    .and_then(|c| match c.ty().kind() {
                        TyKind::FnDef(did, _) => Some(*did),
                        _ => None,
                    })
                    .ok_or(Hold::Unsupported)?;
                let targets = inventory
                    .call_targets
                    .get(&(callee, location))
                    .ok_or(Hold::Identity)?;
                if targets.unknown
                    || targets.known.len() != 1
                    || !targets.known.contains(&target_def)
                {
                    return Err(Hold::Identity);
                }
                let root_args: Vec<_> = args
                    .iter()
                    .enumerate()
                    .filter(|(_, a)| root(&a.node, &aliases))
                    .map(|(i, _)| i)
                    .collect();
                let [root_argument] = root_args.as_slice() else { return Err(Hold::RootUse) };
                let place = args[*root_argument].node.place().ok_or(Hold::Identity)?;
                if canonical_free(tcx, target_def) {
                    if args.len() != 1 || *root_argument != 0 {
                        return Err(Hold::Signature);
                    }
                    let key = SourceEventKey {
                        function: function.clone(),
                        block: block.as_u32(),
                        statement: location.statement_index,
                        phase: SourcePhase::Call,
                        role: SourceRole::Free,
                        storage_local: None,
                        condition: SourceCondition::Unconditional,
                    };
                    let event = inventory.retirements.get(&key).ok_or(Hold::Identity)?;
                    if event.key != key
                        || event.object != SourceObject::HeapThrough(PlaceKey::from_place(place))
                    {
                        return Err(Hold::Identity);
                    }
                    events.insert(key, ());
                } else {
                    let inner = target_def
                        .as_local()
                        .filter(|did| program.functions.contains(did))
                        .ok_or(Hold::Unsupported)?;
                    let nested = body_proof(program, inventory, inner, *root_argument, stack)?;
                    let path = tcx.def_path_str(target_def);
                    let route = inventory
                        .calls
                        .iter()
                        .find(|route| {
                            route.caller == function
                                && route.block == block.as_u32()
                                && route.callee == path
                        })
                        .ok_or(Hold::Identity)?;
                    if route.arguments.get(*root_argument)
                        != Some(&Some(PlaceKey::from_place(place)))
                        || nested.keys().any(|key| !route.events.contains(key))
                    {
                        return Err(Hold::Identity);
                    }
                    events.extend(nested);
                }
                // Supported callees contain only scalar/raw operations and proven
                // non-unwinding C frees, so no unexamined unwind effect is hidden.
                if destination.as_local().is_none()
                    || !destination.ty(&body.local_decls, tcx).ty.is_unit()
                {
                    return Err(Hold::Signature);
                }
                freed = true;
                vec![*target]
            }
            _ => return Err(Hold::Unsupported),
        };
        for successor in successors {
            pending.push((successor, aliases.clone(), freed, visited.clone()));
        }
    }
    if returns == 0 || events.is_empty() {
        return Err(Hold::MissingRetirement);
    }
    Ok(events)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check(body: &str, expected: bool) {
        let source =
            format!("unsafe extern \"C\" {{ fn free(p: *mut core::ffi::c_void); }} {body}");
        ::utils::compilation::run_compiler_on_str(&source, |tcx| {
            let program = crate::bo_rewriter::collect_program(tcx);
            let callee = *program
                .functions
                .iter()
                .find(|id| tcx.def_path_str(id.to_def_id()) == "dispose")
                .unwrap();
            let result = derive(&program, callee, 0);
            assert_eq!(result.is_ok(), expected, "{result:?}");
            if let Ok(proof) = result {
                assert!(proof.matches(&program, callee, 0));
                assert!(!proof.matches(&program, callee, 1));
                let other = RustProgram {
                    tcx,
                    functions: program.functions.clone(),
                    structs: program.structs.clone(),
                };
                assert!(!proof.matches(&other, callee, 0));
                assert!(!proof.events().is_empty());
                let mut inventory = source_events::collect(&program);
                inventory.retirements.clear();
                assert!(body_proof(&program, &inventory, callee, 0, &mut BTreeSet::new()).is_err());
            }
        })
        .unwrap_or_else(|error| error.raise());
    }
    #[test]
    fn r395_deallocator_direct_root_free() {
        check(
            "pub unsafe fn dispose(p: *mut f32) { free(p as *mut core::ffi::c_void); }",
            true,
        );
    }
    #[test]
    fn r395_deallocator_transitive_root_free() {
        check(
            "unsafe fn inner(p: *mut f32) { free(p as *mut core::ffi::c_void); } pub unsafe fn dispose(p: *mut f32) { inner(p); }",
            true,
        );
    }
    #[test]
    fn r395_deallocator_branch_coverage() {
        check(
            "pub unsafe fn dispose(p: *mut f32, b: bool) { if b { free(p as *mut core::ffi::c_void); } else { free(p as *mut core::ffi::c_void); } }",
            true,
        );
    }
    #[test]
    fn r395_deallocator_missing_branch_held() {
        check(
            "pub unsafe fn dispose(p: *mut f32, b: bool) { if b { free(p as *mut core::ffi::c_void); } }",
            false,
        );
    }
    #[test]
    fn r395_deallocator_wrong_root_held() {
        check(
            "pub unsafe fn dispose(p: *mut f32, q: *mut f32) { free(q as *mut core::ffi::c_void); }",
            false,
        );
    }
    #[test]
    fn r395_deallocator_duplicate_free_held() {
        check(
            "pub unsafe fn dispose(p: *mut f32) { free(p as *mut core::ffi::c_void); free(p as *mut core::ffi::c_void); }",
            false,
        );
    }
    #[test]
    fn r395_deallocator_retained_store_held() {
        check(
            "static mut SAVED: *mut f32 = core::ptr::null_mut(); pub unsafe fn dispose(p: *mut f32) { SAVED=p; free(p as *mut core::ffi::c_void); }",
            false,
        );
    }
    #[test]
    fn r395_deallocator_after_free_read_held() {
        check(
            "pub unsafe fn dispose(p: *mut f32) { free(p as *mut core::ffi::c_void); let _x = *p; }",
            false,
        );
    }
    #[test]
    fn r395_deallocator_opaque_call_held() {
        check(
            "unsafe extern \"C\" { fn opaque(p: *mut f32); } pub unsafe fn dispose(p: *mut f32) { opaque(p); free(p as *mut core::ffi::c_void); }",
            false,
        );
    }
    #[test]
    fn r395_deallocator_pointer_integer_roundtrip_held() {
        check(
            "pub unsafe fn dispose(p: *mut f32) { let q = p as usize as *mut core::ffi::c_void; free(q); }",
            false,
        );
    }
}
