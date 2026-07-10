//! detector for struct-parameter field specialization (pointer-flow stage 4):
//! selects struct-pointer parameters that provably access a single field,
//! finds aliasing trigger call sites, closes over param forwarding, and
//! verifies every call site of a selected function is rewritable.

use rustc_abi::FieldIdx;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::{
    mir::{
        Body, Local, Location, Operand, Place, ProjectionElem, Rvalue, Terminator, TerminatorKind,
        visit::{MutatingUseContext, PlaceContext, Visitor},
    },
    ty::{self, TyCtxt},
};
use rustc_span::{Symbol, def_id::LocalDefId};

use crate::{
    analyses::pointer_flow::{
        PointerFlowResult,
        field_access::field_accesses_reachable_from_param,
        graph::{BaseId, PfgNode},
    },
    utils::rustc::RustProgram,
};

/// the field a selected struct-pointer parameter is specialized to
#[derive(Clone, Debug)]
pub struct SpecTarget {
    pub field: FieldIdx,
    pub field_name: Symbol,
    pub struct_def: LocalDefId,
}

// param type must be a raw pointer to a local, non-generic struct
fn struct_pointee<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
) -> Option<(LocalDefId, ty::AdtDef<'tcx>)> {
    if !ty.is_raw_ptr() {
        return None;
    }
    let pointee = ty.builtin_deref(true)?;
    let ty::TyKind::Adt(adt_def, args) = pointee.kind() else {
        return None;
    };
    if !adt_def.is_struct() || adt_def.is_union() || !args.is_empty() {
        return None;
    }
    let _ = tcx;
    adt_def.did().as_local().map(|did| (did, *adt_def))
}

// functions used as values (fn pointers) cannot change signature
fn collect_address_taken_fns(input: &RustProgram<'_>) -> FxHashSet<LocalDefId> {
    struct FnValueScanner<'a> {
        taken: &'a mut FxHashSet<LocalDefId>,
    }
    impl<'tcx> Visitor<'tcx> for FnValueScanner<'_> {
        fn visit_operand(&mut self, operand: &Operand<'tcx>, _: Location) {
            if let Operand::Constant(constant) = operand
                && let ty::TyKind::FnDef(def_id, _) = constant.const_.ty().kind()
                && let Some(local) = def_id.as_local()
            {
                self.taken.insert(local);
            }
        }

        // visit call args and destination but skip the callee operand: a direct
        // call is not an address-taking use
        fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
            if let TerminatorKind::Call {
                args, destination, ..
            } = &terminator.kind
            {
                for arg in args {
                    self.visit_operand(&arg.node, location);
                }
                self.visit_place(
                    destination,
                    PlaceContext::MutatingUse(MutatingUseContext::Call),
                    location,
                );
            } else {
                self.super_terminator(terminator, location);
            }
        }
    }

    let tcx = input.tcx;
    let mut taken = FxHashSet::default();
    for &fn_did in &input.functions {
        let body = tcx.mir_drops_elaborated_and_const_checked(fn_did).borrow();
        FnValueScanner { taken: &mut taken }.visit_body(&body);
    }
    taken
}

#[allow(dead_code)] // query API has no non-test client until Task 3 (final plan assembly)
pub(crate) fn collect_candidates(
    input: &RustProgram<'_>,
    flows: &FxHashMap<LocalDefId, PointerFlowResult>,
    c_exposed_fns: &FxHashSet<String>,
) -> FxHashMap<(LocalDefId, usize), SpecTarget> {
    let tcx = input.tcx;
    let address_taken = collect_address_taken_fns(input);
    let mut candidates = FxHashMap::default();

    for &fn_did in &input.functions {
        let name = tcx.item_name(fn_did.to_def_id());
        if name.as_str() == "main"
            || c_exposed_fns.contains(name.as_str())
            || address_taken.contains(&fn_did)
            || tcx.fn_sig(fn_did).skip_binder().c_variadic()
        {
            continue;
        }
        let Some(flow) = flows.get(&fn_did) else {
            continue;
        };
        let body = tcx.mir_drops_elaborated_and_const_checked(fn_did).borrow();
        for (param_idx, local) in body.args_iter().enumerate() {
            let Some((struct_def, adt_def)) = struct_pointee(tcx, body.local_decls[local].ty)
            else {
                continue;
            };
            let Some(summary) = field_accesses_reachable_from_param(flow, local) else {
                continue;
            };
            // the adjudicated stage-4 client gate
            if !summary.rejects.is_empty()
                || !summary.multi_base_nodes.is_empty()
                || summary.fields.len() != 1
            {
                continue;
            }
            let field = *summary.fields.iter().next().unwrap();
            let field_name = adt_def.non_enum_variant().fields[field].name;
            candidates.insert(
                (fn_did, param_idx),
                SpecTarget {
                    field,
                    field_name,
                    struct_def,
                },
            );
        }
    }
    candidates
}

// per-body maps for walking an argument's definition chain backward
struct BodyDefs<'tcx> {
    // local -> rvalues assigned to it (bare-local destinations only)
    assigns: FxHashMap<Local, Vec<Rvalue<'tcx>>>,
    // as_mut_ptr/as_ptr-style call destination -> receiver place
    call_recv: FxHashMap<Local, Place<'tcx>>,
}

impl<'tcx> BodyDefs<'tcx> {
    fn new(body: &Body<'tcx>, tcx: TyCtxt<'tcx>) -> Self {
        let mut assigns: FxHashMap<Local, Vec<Rvalue<'tcx>>> = FxHashMap::default();
        let mut call_recv = FxHashMap::default();
        for block in body.basic_blocks.iter() {
            for statement in &block.statements {
                if let rustc_middle::mir::StatementKind::Assign(box (place, rvalue)) =
                    &statement.kind
                    && let Some(local) = place.as_local()
                {
                    assigns.entry(local).or_default().push(rvalue.clone());
                }
            }
            if let TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &block.terminator().kind
                && let Some(dest) = destination.as_local()
                && let Some(fn_const) = func.constant()
                && let ty::TyKind::FnDef(def_id, _) = fn_const.ty().kind()
                && matches!(tcx.item_name(*def_id).as_str(), "as_mut_ptr" | "as_ptr")
                && let Some(recv) = args.first().and_then(|arg| arg.node.place())
            {
                call_recv.insert(dest, recv);
            }
        }
        Self { assigns, call_recv }
    }
}

// unique non-null base of an operand's head slot, e.g. the struct pointer
// argument temp copied from a local or param
fn operand_base(flow: &PointerFlowResult, op: &Operand<'_>) -> Option<BaseId> {
    let place = op.place()?;
    let slot = flow.slot_table.local_head_slot(place.local)?;
    flow.provenance.unique_non_null_base(&PfgNode::Slot(slot))
}

// if `place` is `(*prefix).field...`, return the unique non-null base of the
// deref'd prefix
fn deref_field_prefix_base<'tcx>(
    flow: &PointerFlowResult,
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    place: Place<'tcx>,
) -> Option<BaseId> {
    let projection = place.projection.as_ref();
    let deref_idx = projection
        .iter()
        .position(|elem| matches!(elem, ProjectionElem::Deref))?;
    if !matches!(
        projection.get(deref_idx + 1),
        Some(ProjectionElem::Field(..))
    ) {
        return None;
    }
    let prefix = Place::from(place.local).project_deeper(&projection[..deref_idx], tcx);
    let slot = flow.slot_table.place_head_slot(prefix, body, tcx)?;
    flow.provenance.unique_non_null_base(&PfgNode::Slot(slot))
}

// walks an argument backward through the shapes c2rust emits (copies, casts,
// unsize coercions, borrows, as_mut_ptr/as_ptr) until it reaches a field
// address `&raw? (*prefix).field`; returns the prefix's base
fn field_address_base<'tcx>(
    flow: &PointerFlowResult,
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    defs: &BodyDefs<'tcx>,
    op: &Operand<'tcx>,
) -> Option<BaseId> {
    let mut place = op.place()?;
    let mut visited = FxHashSet::default();
    loop {
        if let Some(base) = deref_field_prefix_base(flow, body, tcx, place) {
            return Some(base);
        }
        let local = place.as_local()?;
        if !visited.insert(local) {
            return None;
        }
        if let Some(rvalues) = defs.assigns.get(&local) {
            // multiple assignments end the walk: the chain is no longer a
            // single-definition temp
            let [rvalue] = rvalues.as_slice() else {
                return None;
            };
            match rvalue {
                Rvalue::Use(op) | Rvalue::Cast(_, op, _) => place = op.place()?,
                Rvalue::Ref(_, _, p) | Rvalue::RawPtr(_, p) => place = *p,
                Rvalue::CopyForDeref(p) => place = *p,
                _ => return None,
            }
        } else if let Some(recv) = defs.call_recv.get(&local) {
            place = *recv;
        } else {
            return None;
        }
    }
}

fn call_target(_tcx: TyCtxt<'_>, func: &Operand<'_>) -> Option<LocalDefId> {
    let fn_const = func.constant()?;
    let ty::TyKind::FnDef(def_id, _) = fn_const.ty().kind() else {
        return None;
    };
    def_id.as_local()
}

/// call sites that alias a struct-pointer candidate argument with a pointer
/// derived from a field of the same struct object passed in another argument
/// of the same call. these are the sites the specialization plan (Task 3)
/// must be able to rewrite: after the struct param is replaced by the field's
/// value, the aliasing field-pointer argument would otherwise observe stale
/// data.
pub(crate) fn collect_triggered(
    input: &RustProgram<'_>,
    flows: &FxHashMap<LocalDefId, PointerFlowResult>,
    candidates: &FxHashMap<(LocalDefId, usize), SpecTarget>,
) -> FxHashSet<(LocalDefId, usize)> {
    let tcx = input.tcx;
    let mut triggered = FxHashSet::default();
    for &fn_did in &input.functions {
        let Some(flow) = flows.get(&fn_did) else {
            continue;
        };
        let body = tcx.mir_drops_elaborated_and_const_checked(fn_did).borrow();
        let defs = BodyDefs::new(&body, tcx);
        for block in body.basic_blocks.iter() {
            let TerminatorKind::Call { func, args, .. } = &block.terminator().kind else {
                continue;
            };
            let Some(callee) = call_target(tcx, func) else {
                continue;
            };
            for (i, arg) in args.iter().enumerate() {
                if !candidates.contains_key(&(callee, i)) {
                    continue;
                }
                let Some(base) = operand_base(flow, &arg.node) else {
                    continue;
                };
                let has_sibling_field_ptr = args.iter().enumerate().any(|(j, other)| {
                    j != i
                        && field_address_base(flow, &body, tcx, &defs, &other.node)
                            .is_some_and(|b| b == base)
                });
                if has_sibling_field_ptr {
                    triggered.insert((callee, i));
                }
            }
        }
    }
    triggered
}

#[cfg(test)]
mod tests {
    use rustc_hash::FxHashSet;
    use rustc_hir::{ItemKind, OwnerNode};

    use super::*;
    use crate::{analyses::pointer_flow::pointer_flow_analysis, utils::rustc::RustProgram};

    // local copy of the pointer_flow test helper; test modules cannot import
    // each other's private items
    fn build_rust_program(tcx: rustc_middle::ty::TyCtxt<'_>) -> RustProgram<'_> {
        let mut functions = vec![];
        let mut structs = vec![];
        for maybe_owner in tcx.hir_crate(()).owners.iter() {
            let Some(owner) = maybe_owner.as_owner() else {
                continue;
            };
            let OwnerNode::Item(item) = owner.node() else {
                continue;
            };
            match item.kind {
                ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
                ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
                _ => {}
            }
        }
        RustProgram {
            tcx,
            functions,
            structs,
        }
    }

    // returns sorted (fn name, param index, field name) triples
    fn candidates_for(code: &str) -> Vec<(String, usize, String)> {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = build_rust_program(tcx);
            let flows = pointer_flow_analysis(&program, &FxHashSet::default());
            let candidates = collect_candidates(&program, &flows, &FxHashSet::default());
            let mut out: Vec<(String, usize, String)> = candidates
                .iter()
                .map(|(&(did, idx), target)| {
                    (
                        tcx.item_name(did.to_def_id()).to_string(),
                        idx,
                        target.field_name.to_string(),
                    )
                })
                .collect();
            out.sort();
            out
        })
        .unwrap()
    }

    const SINGLE_FIELD: &str = r#"
use ::libc;
#[repr(C)]
pub struct st {
    pub lookup: [u16; 4],
    pub lit: [u32; 4],
}
pub unsafe extern "C" fn build(mut s: *mut st) -> libc::c_int {
    if !s.is_null() {
        (*s).lookup[0] = 1 as u16;
    }
    return 0 as libc::c_int;
}
"#;

    #[test]
    fn test_single_field_param_is_candidate() {
        assert_eq!(
            candidates_for(SINGLE_FIELD),
            vec![("build".to_string(), 0, "lookup".to_string())]
        );
    }

    #[test]
    fn test_two_field_param_is_not_candidate() {
        let code = r#"
use ::libc;
#[repr(C)]
pub struct st {
    pub lookup: [u16; 4],
    pub lit: [u32; 4],
}
pub unsafe extern "C" fn build(mut s: *mut st) -> libc::c_int {
    (*s).lookup[0] = 1 as u16;
    (*s).lit[0] = 2 as u32;
    return 0 as libc::c_int;
}
"#;
        assert_eq!(candidates_for(code), vec![]);
    }

    #[test]
    fn test_address_taken_fn_is_excluded() {
        let code = r#"
use ::libc;
#[repr(C)]
pub struct st {
    pub lookup: [u16; 4],
}
pub unsafe extern "C" fn build(mut s: *mut st) -> libc::c_int {
    (*s).lookup[0] = 1 as u16;
    return 0 as libc::c_int;
}
pub unsafe extern "C" fn take(mut s: *mut st) -> libc::c_int {
    let f: unsafe extern "C" fn(*mut st) -> libc::c_int = build;
    return f(s);
}
"#;
        assert!(
            candidates_for(code)
                .iter()
                .all(|(name, _, _)| name != "build")
        );
    }

    #[test]
    fn test_c_exposed_fn_is_excluded() {
        let selected = ::utils::compilation::run_compiler_on_str(SINGLE_FIELD, |tcx| {
            let program = build_rust_program(tcx);
            let flows = pointer_flow_analysis(&program, &FxHashSet::default());
            let mut exposed = FxHashSet::default();
            exposed.insert("build".to_string());
            collect_candidates(&program, &flows, &exposed).len()
        })
        .unwrap();
        assert_eq!(selected, 0);
    }

    #[test]
    fn test_forwarding_caller_is_also_candidate() {
        // summary propagation attributes build's lookup access to caller's param
        let code = r#"
use ::libc;
#[repr(C)]
pub struct st {
    pub lookup: [u16; 4],
}
pub unsafe extern "C" fn build(mut s: *mut st) -> libc::c_int {
    (*s).lookup[0] = 1 as u16;
    return 0 as libc::c_int;
}
pub unsafe extern "C" fn caller(mut s: *mut st) -> libc::c_int {
    return build(s);
}
"#;
        assert_eq!(
            candidates_for(code),
            vec![
                ("build".to_string(), 0, "lookup".to_string()),
                ("caller".to_string(), 0, "lookup".to_string()),
            ]
        );
    }

    fn triggered_for(code: &str) -> Vec<(String, usize)> {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = build_rust_program(tcx);
            let flows = pointer_flow_analysis(&program, &FxHashSet::default());
            let candidates = collect_candidates(&program, &flows, &FxHashSet::default());
            let triggered = collect_triggered(&program, &flows, &candidates);
            let mut out: Vec<(String, usize)> = triggered
                .iter()
                .map(|&(did, idx)| (tcx.item_name(did.to_def_id()).to_string(), idx))
                .collect();
            out.sort();
            out
        })
        .unwrap()
    }

    const TRIGGERED: &str = r#"
use ::libc;
#[repr(C)]
pub struct st {
    pub lookup: [u16; 4],
    pub lit: [u32; 4],
}
pub unsafe extern "C" fn build(mut s: *mut st, mut tree: *mut u32) -> libc::c_int {
    if !s.is_null() {
        (*s).lookup[0] = 1 as u16;
    }
    *tree.offset(0) = 0 as u32;
    return 0 as libc::c_int;
}
pub unsafe extern "C" fn fixed(mut s: *mut st) -> libc::c_int {
    return build(s, ((*s).lit).as_mut_ptr());
}
"#;

    #[test]
    fn test_struct_and_field_pointer_call_site_triggers() {
        assert_eq!(triggered_for(TRIGGERED), vec![("build".to_string(), 0)]);
    }

    #[test]
    fn test_struct_pointer_alone_does_not_trigger() {
        let code = r#"
use ::libc;
#[repr(C)]
pub struct st {
    pub lookup: [u16; 4],
}
pub unsafe extern "C" fn build(mut s: *mut st, mut tree: *mut u32) -> libc::c_int {
    (*s).lookup[0] = 1 as u16;
    *tree.offset(0) = 0 as u32;
    return 0 as libc::c_int;
}
pub unsafe extern "C" fn fixed(mut s: *mut st, mut tree: *mut u32) -> libc::c_int {
    return build(s, tree);
}
"#;
        assert_eq!(triggered_for(code), vec![]);
    }
}
