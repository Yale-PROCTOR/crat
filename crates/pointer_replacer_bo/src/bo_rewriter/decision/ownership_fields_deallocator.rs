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
    // R641-6 (W5): `!` is the type of an early `return;`'s own expression
    // (`if ctx.is_null() { return; }`); a never-typed local holds no value.
    ty.is_unit()
        || ty.is_never()
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
/// `<*mut T>::is_null` / `<*const T>::is_null`, from core.
fn core_is_null(tcx: TyCtxt<'_>, callee: DefId) -> bool {
    tcx.crate_name(callee.krate).as_str() == "core" && tcx.item_name(callee).as_str() == "is_null"
}
/// **R641-6 (W5)** — a place READ THROUGH the root (`(*root).f`): the root is
/// the base of a dereference, never a copied pointer value.
fn through_root(place: &Place<'_>, aliases: &BTreeSet<Local>) -> bool {
    aliases.contains(&place.local)
        && matches!(
            place.projection.first(),
            Some(rustc_middle::mir::ProjectionElem::Deref)
        )
}
/// Does the rvalue name the root only as the base of a dereference (a load of
/// the pointee's contents), never as a value or behind a borrow?
struct BareRoot<'a> {
    aliases: &'a BTreeSet<Local>,
    bare: bool,
}
impl<'tcx> Visitor<'tcx> for BareRoot<'_> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        if self.aliases.contains(&place.local) && !through_root(place, self.aliases) {
            self.bare = true;
        }
        self.super_place(place, context, location);
    }
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
    // R641-6 (W5): per path, the locals holding `is_null(root)` and whether
    // this path is known to hold a null root (it then owes no retirement).
    let mut pending = vec![(
        START_BLOCK,
        BTreeSet::from([formal]),
        false,
        BTreeSet::new(),
        BTreeSet::<Local>::new(),
        false,
    )];
    let mut events = BTreeMap::new();
    let mut returns = 0;
    let mut budget = 512;
    while let Some((block, mut aliases, mut freed, mut visited, mut null_flags, null_root)) =
        pending.pop()
    {
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
                // R641-6 (W5): a store INTO the pointee through the root
                // (`(*root).f = v`, v not the root) retains nothing.
                StatementKind::Assign(box (destination, value))
                    if through_root(destination, &aliases) =>
                {
                    if freed {
                        return Err(Hold::AlreadyFreed);
                    }
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
                    if reads.found {
                        return Err(Hold::RootUse);
                    }
                }
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
                    // R641-6 (W5): a load OUT of the pointee (`_x = (*root).f`)
                    // reads a field value, not the root; no borrow of it.
                    let mut bare = BareRoot {
                        aliases: &aliases,
                        bare: false,
                    };
                    bare.visit_rvalue(
                        value,
                        Location {
                            block,
                            statement_index,
                        },
                    );
                    let pointee_load = reads.found
                        && !bare.bare
                        && !matches!(value, Rvalue::Ref(..) | Rvalue::RawPtr(..));
                    if reads.found && freed {
                        return Err(Hold::AlreadyFreed);
                    }
                    if reads.found && !copied_root && !pointee_load {
                        return Err(Hold::RootUse);
                    }
                    null_flags.remove(&local);
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
                if !freed && !null_root {
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
                // R641-6 (W5): a branch on `is_null(root)`: its nonzero
                // (true) arm holds a null root, which owes no retirement.
                if let Some(flag) = discr.place().and_then(|p| p.as_local())
                    && null_flags.contains(&flag)
                {
                    for (value, target) in targets.iter() {
                        pending.push((
                            target,
                            aliases.clone(),
                            freed,
                            visited.clone(),
                            null_flags.clone(),
                            value != 0 || null_root,
                        ));
                    }
                    pending.push((
                        targets.otherwise(),
                        aliases.clone(),
                        freed,
                        visited.clone(),
                        null_flags.clone(),
                        !targets.iter().any(|(value, _)| value != 0) || null_root,
                    ));
                    continue;
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
                // R641-6 (W5): a pure null test, of the root (its result is a
                // null flag) or of any other pointer; and a libc `free` of a
                // pointer that is not the root (a field's own allocation).
                if core_is_null(tcx, target_def) && args.len() == 1 {
                    let flag = destination.as_local().ok_or(Hold::Signature)?;
                    if root_args.len() == 1 {
                        null_flags.insert(flag);
                    } else {
                        null_flags.remove(&flag);
                    }
                    pending.push((
                        *target,
                        aliases.clone(),
                        freed,
                        visited.clone(),
                        null_flags.clone(),
                        null_root,
                    ));
                    continue;
                }
                if root_args.is_empty() && canonical_free(tcx, target_def) {
                    if destination.as_local().is_none()
                        || !destination.ty(&body.local_decls, tcx).ty.is_unit()
                    {
                        return Err(Hold::Signature);
                    }
                    pending.push((
                        *target,
                        aliases.clone(),
                        freed,
                        visited.clone(),
                        null_flags.clone(),
                        null_root,
                    ));
                    continue;
                }
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
            pending.push((
                successor,
                aliases.clone(),
                freed,
                visited.clone(),
                null_flags.clone(),
                null_root,
            ));
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

    const R641_OSN: &str = "#[repr(C)] #[derive(Copy, Clone)] pub struct osn_context { pub perm: *mut i16, pub grad: *mut i16 }";

    /// **R641-6 (W5)** — heman's `open_simplex_noise_free`: a null guard on
    /// the root (its null arm owes no retirement: nothing to free), field
    /// frees and null stores THROUGH the root before its one retirement.
    #[test]
    fn r641_deallocator_null_guard_and_field_frees() {
        check(
            &format!(
                "{R641_OSN}
pub unsafe extern \"C\" fn dispose(mut ctx: *mut osn_context) {{
    if ctx.is_null() {{ return; }}
    if !((*ctx).perm).is_null() {{ free((*ctx).perm as *mut core::ffi::c_void); (*ctx).perm = 0 as *mut i16; }}
    if !((*ctx).grad).is_null() {{ free((*ctx).grad as *mut core::ffi::c_void); (*ctx).grad = 0 as *mut i16; }}
    free(ctx as *mut core::ffi::c_void);
}}"
            ),
            true,
        );
    }

    /// Control: the root stored into its own field is retained, not freed.
    #[test]
    fn r641_deallocator_root_stored_in_its_own_field_held() {
        check(
            &format!(
                "{R641_OSN}
pub unsafe extern \"C\" fn dispose(mut ctx: *mut osn_context) {{
    if ctx.is_null() {{ return; }}
    (*ctx).perm = ctx as *mut i16;
    free(ctx as *mut core::ffi::c_void);
}}"
            ),
            false,
        );
    }

    /// Control: the null arm excuses only the null root; a non-null path
    /// that returns without the free still owes the retirement.
    #[test]
    fn r641_deallocator_nonnull_path_without_the_free_held() {
        check(
            &format!(
                "{R641_OSN}
pub unsafe extern \"C\" fn dispose(mut ctx: *mut osn_context) {{
    if ctx.is_null() {{ return; }}
    if !((*ctx).perm).is_null() {{ return; }}
    free(ctx as *mut core::ffi::c_void);
}}"
            ),
            false,
        );
    }
}
