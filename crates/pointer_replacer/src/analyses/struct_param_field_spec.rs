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
use rustc_span::{Span, Symbol, def_id::LocalDefId};

use crate::{
    analyses::pointer_flow::{
        PointerFlowResult,
        builtin::{call_name, is_as_ptr},
        field_access::{FieldAccessKind, field_accesses_reachable_from_param},
        graph::{BaseId, PfgNode, UnknownReason},
    },
    utils::rustc::{RustProgram, is_c_exposed_fn},
};

/// the field a selected struct-pointer parameter is specialized to
#[derive(Clone, Debug)]
pub struct SpecTarget {
    pub field: FieldIdx,
    pub field_name: Symbol,
    pub struct_def: LocalDefId,
    /// mutability of the original raw-pointer parameter; every downstream
    /// pointer/borrow the rewriter emits preserves it
    pub mutbl: ty::Mutability,
    /// true when the function's C ABI must be preserved: the rewriter renames
    /// it to `{name}_field` and re-exposes a wrapper with the original signature
    pub exposed: bool,
}

// param type must be a raw pointer to a local, non-generic struct
fn struct_pointee<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
) -> Option<(LocalDefId, ty::AdtDef<'tcx>, ty::Mutability)> {
    let ty::TyKind::RawPtr(pointee, mutbl) = ty.kind() else {
        return None;
    };
    let ty::TyKind::Adt(adt_def, args) = pointee.kind() else {
        return None;
    };
    if !adt_def.is_struct() || adt_def.is_union() || !args.is_empty() {
        return None;
    }
    let _ = tcx;
    adt_def.did().as_local().map(|did| (did, *adt_def, *mutbl))
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
            || address_taken.contains(&fn_did)
            || tcx.fn_sig(fn_did).skip_binder().c_variadic()
        {
            continue;
        }
        let exposed = is_c_exposed_fn(tcx, fn_did, c_exposed_fns);
        let Some(flow) = flows.get(&fn_did) else {
            continue;
        };
        let body = tcx.mir_drops_elaborated_and_const_checked(fn_did).borrow();
        for (param_idx, local) in body.args_iter().enumerate() {
            let Some((struct_def, adt_def, mutbl)) =
                struct_pointee(tcx, body.local_decls[local].ty)
            else {
                continue;
            };
            // multi-field filter: a field pointer into a one-field struct is
            // byte-equivalent to the struct pointer; narrowing is churn
            if adt_def.non_enum_variant().fields.len() < 2 {
                continue;
            }
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
            // minimal privilege: a field never written through this param can be
            // specialized as *const even when the original pointer was *mut, keeping
            // downstream borrow promotion free to choose shared references at read-only
            // call sites. address-kind accesses may feed writes (e.g. memset through
            // as_mut_ptr), so they conservatively keep the declared mutability
            let needs_mut = summary.accesses.iter().any(|access| {
                matches!(
                    access.kind,
                    FieldAccessKind::Write | FieldAccessKind::Address
                )
            });
            let mutbl = if needs_mut {
                mutbl
            } else {
                ty::Mutability::Not
            };
            candidates.insert(
                (fn_did, param_idx),
                SpecTarget {
                    field,
                    field_name,
                    struct_def,
                    mutbl,
                    exposed,
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
                && let Some((def_id, name)) = call_name(tcx, func)
                && is_as_ptr(tcx, def_id, &name)
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

/// the assembled specialization plan: candidate params selected for
/// rewriting, plus forwarding edges among them
#[derive(Debug, Default)]
pub struct SpecPlan {
    pub targets: FxHashMap<(LocalDefId, usize), SpecTarget>,
    /// forwarding edges among targets: caller (fn, param) passes its own
    /// specialized param directly as callee (fn, param)
    pub forwards: FxHashSet<((LocalDefId, usize), (LocalDefId, usize))>,
    /// per-call-site emission decision for specialized-position arguments
    /// that need neither the null-literal retype nor bare forwarding; keyed
    /// by the caller function, the call terminator's span, and the argument
    /// index (a single call site may specialize multiple arguments).
    // consumed by the rewriter once it lands (guarded-conversion follow-up)
    #[allow(dead_code)]
    pub site_emissions: FxHashMap<(LocalDefId, Span, usize), SiteEmission>,
}

/// how a call-site argument that needs no special-case emission (not a
/// null literal, not a bare forward into a selected target) should be
/// rewritten by the resolver/rewriter
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SiteEmission {
    // provably safe: `&mut/& (*e).fld as *T` inline
    Direct,
    // unprovable: needs a hoisted null-checked let before the statement
    Guarded,
}

// how a call-site argument at a specialized position can be rewritten
#[derive(Clone, Debug, PartialEq, Eq)]
enum ArgClass {
    // NullLike-only provenance: rewrite to `0 as *mut FieldTy`
    Null,
    // the caller's own candidate param passed through; valid only while the
    // caller stays selected
    Forward((LocalDefId, usize)),
    // the same call already takes a field address on the same base, so the
    // caller dereferences the base here anyway
    FieldSibling,
    // non-null per the nullity analysis: `&raw mut (*e).fld` is safe
    NonNull,
    // universal fallback: no class above applies, but the site is still
    // rewritable via a hoisted null-checked guard (Task 2); keeps arg_ok
    // semantics uniform (every candidate position now has a usable class)
    Guarded,
}

// one call site into a candidate position, with every applicable class
#[derive(Debug)]
struct CallSiteFact {
    callee: (LocalDefId, usize),
    classes: Vec<ArgClass>,
    // the caller function, the call terminator's span, and the argument
    // index, used to key `SpecPlan::site_emissions`
    caller: LocalDefId,
    span: Span,
    arg_idx: usize,
}

fn all_bases_null_like(flow: &PointerFlowResult, op: &Operand<'_>) -> bool {
    let Some(place) = op.place() else {
        return false;
    };
    let Some(slot) = flow.slot_table.local_head_slot(place.local) else {
        return false;
    };
    let Some(bases) = flow.provenance.reachable_bases.get(&PfgNode::Slot(slot)) else {
        return false;
    };
    !bases.is_empty()
        && bases.iter().all(|base| {
            matches!(
                base,
                BaseId::Unknown {
                    reason: UnknownReason::NullLike,
                    ..
                }
            )
        })
}

#[allow(clippy::too_many_arguments)]
fn classify_arg<'tcx>(
    flow: &PointerFlowResult,
    body: &Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    defs: &BodyDefs<'tcx>,
    caller: LocalDefId,
    candidates: &FxHashMap<(LocalDefId, usize), SpecTarget>,
    nullity: &crate::analyses::nullity::NullityResult,
    args: &[rustc_span::source_map::Spanned<Operand<'tcx>>],
    arg_idx: usize,
) -> Vec<ArgClass> {
    let mut classes = vec![];
    let arg = &args[arg_idx].node;

    if all_bases_null_like(flow, arg) {
        classes.push(ArgClass::Null);
    }

    let base = operand_base(flow, arg);
    if let Some(BaseId::Param { local, .. }) = &base {
        let param_key = (caller, local.index() - 1);
        if candidates.contains_key(&param_key) {
            classes.push(ArgClass::Forward(param_key));
        }
    }
    if let Some(base) = &base {
        let has_sibling = args.iter().enumerate().any(|(j, other)| {
            j != arg_idx
                && field_address_base(flow, body, tcx, defs, &other.node)
                    .is_some_and(|b| &b == base)
        });
        if has_sibling {
            classes.push(ArgClass::FieldSibling);
        }
    }
    if let Some(place) = arg.place()
        && let Some(locals) = nullity.non_null_locals.get(&caller)
        && locals.contains(place.local)
    {
        classes.push(ArgClass::NonNull);
    }

    // universal fallback: every candidate position is rewritable via a
    // hoisted guard, so arg_ok never needs a "no class matched" case
    classes.push(ArgClass::Guarded);

    classes
}

pub fn find_plan(
    input: &RustProgram<'_>,
    flows: &FxHashMap<LocalDefId, PointerFlowResult>,
    nullity: &crate::analyses::nullity::NullityResult,
    c_exposed_fns: &FxHashSet<String>,
) -> SpecPlan {
    let tcx = input.tcx;
    let candidates = collect_candidates(input, flows, c_exposed_fns);
    let triggered = collect_triggered(input, flows, &candidates);

    // every call site into a candidate position, plus forwarding edges
    let mut facts: Vec<CallSiteFact> = vec![];
    let mut forwards: FxHashSet<((LocalDefId, usize), (LocalDefId, usize))> = FxHashSet::default();
    for &fn_did in &input.functions {
        let Some(flow) = flows.get(&fn_did) else {
            continue;
        };
        let body = tcx.mir_drops_elaborated_and_const_checked(fn_did).borrow();
        let defs = BodyDefs::new(&body, tcx);
        for block in body.basic_blocks.iter() {
            let terminator = block.terminator();
            let TerminatorKind::Call { func, args, .. } = &terminator.kind else {
                continue;
            };
            let Some(callee) = call_target(tcx, func) else {
                continue;
            };
            let span = terminator.source_info.span;
            for i in 0..args.len() {
                if !candidates.contains_key(&(callee, i)) {
                    continue;
                }
                let classes = classify_arg(
                    flow,
                    &body,
                    tcx,
                    &defs,
                    fn_did,
                    &candidates,
                    nullity,
                    args,
                    i,
                );
                for class in &classes {
                    if let ArgClass::Forward(from) = class {
                        forwards.insert((*from, (callee, i)));
                    }
                }
                facts.push(CallSiteFact {
                    callee: (callee, i),
                    classes,
                    caller: fn_did,
                    span,
                    arg_idx: i,
                });
            }
        }
    }

    // closure: a selected caller that forwards its param drags the callee in
    let mut selected: FxHashSet<(LocalDefId, usize)> = triggered;
    loop {
        let additions: Vec<_> = forwards
            .iter()
            .filter(|(from, to)| selected.contains(from) && !selected.contains(to))
            .map(|(_, to)| *to)
            .collect();
        if additions.is_empty() {
            break;
        }
        selected.extend(additions);
    }

    // the rewriter cannot yet emit Guarded call sites (Task 2); until it can,
    // a would-be-Guarded site instead drops its target, mimicking the
    // pre-guarded-conversion behavior exactly. flipped in the guarded-emission task
    let guarded_live = false;

    // validity fixpoint: every call site into a selected position needs a
    // usable class, and a selected forwarder needs its target selected.
    // Guarded is usable only once the rewriter can emit it (guarded_live);
    // until then a Guarded-only site behaves like the old "no usable class"
    // case and sinks its target through the same cascade
    loop {
        let before = selected.len();
        let keep: FxHashSet<(LocalDefId, usize)> = selected
            .iter()
            .filter(|key| {
                let sites_ok = facts
                    .iter()
                    .filter(|fact| fact.callee == **key)
                    .all(|fact| {
                        fact.classes.iter().any(|class| match class {
                            ArgClass::Null | ArgClass::FieldSibling | ArgClass::NonNull => true,
                            ArgClass::Guarded => guarded_live,
                            ArgClass::Forward(from) => selected.contains(from),
                        })
                    });
                let forwards_ok = forwards
                    .iter()
                    .all(|(from, to)| from != *key || selected.contains(to));
                sites_ok && forwards_ok
            })
            .copied()
            .collect();
        selected = keep;
        if selected.len() == before {
            break;
        }
    }

    // per-site emission decisions for arguments into surviving targets that
    // need neither the null-literal retype nor bare forwarding
    let mut site_emissions = FxHashMap::default();
    for fact in &facts {
        if !selected.contains(&fact.callee) {
            continue;
        }
        // skip: null-literal sites keep the retype path
        if fact.classes.contains(&ArgClass::Null) {
            continue;
        }
        // skip: bare-pass sites forwarding a still-selected candidate stay forwarding
        let forwards_selected = fact
            .classes
            .iter()
            .any(|class| matches!(class, ArgClass::Forward(from) if selected.contains(from)));
        if forwards_selected {
            continue;
        }
        let direct = fact
            .classes
            .iter()
            .any(|class| matches!(class, ArgClass::FieldSibling | ArgClass::NonNull));
        let emission = if direct {
            SiteEmission::Direct
        } else {
            // only reachable when guarded_live: otherwise the fixpoint above
            // already sank any target whose sole class here is Guarded
            SiteEmission::Guarded
        };
        site_emissions.insert((fact.caller, fact.span, fact.arg_idx), emission);
    }

    let targets = candidates
        .into_iter()
        .filter(|(key, _)| selected.contains(key))
        .collect();
    let forwards = forwards
        .into_iter()
        .filter(|(from, to)| selected.contains(from) && selected.contains(to))
        .collect();
    SpecPlan {
        targets,
        forwards,
        site_emissions,
    }
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

    // returns sorted (fn name, param index, field name, mutbl) quadruples
    fn candidates_with_mutbl_for(code: &str) -> Vec<(String, usize, String, ty::Mutability)> {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = build_rust_program(tcx);
            let flows = pointer_flow_analysis(&program, &FxHashSet::default());
            let candidates = collect_candidates(&program, &flows, &FxHashSet::default());
            let mut out: Vec<(String, usize, String, ty::Mutability)> = candidates
                .iter()
                .map(|(&(did, idx), target)| {
                    (
                        tcx.item_name(did.to_def_id()).to_string(),
                        idx,
                        target.field_name.to_string(),
                        target.mutbl,
                    )
                })
                .collect();
            out.sort();
            out
        })
        .unwrap()
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

    // returns sorted (fn name, param index, exposed) triples
    fn exposed_flags_for(code: &str, exposed: &[&str]) -> Vec<(String, usize, bool)> {
        let exposed: FxHashSet<String> = exposed.iter().map(|s| s.to_string()).collect();
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = build_rust_program(tcx);
            let flows = pointer_flow_analysis(&program, &FxHashSet::default());
            let candidates = collect_candidates(&program, &flows, &exposed);
            let mut out: Vec<(String, usize, bool)> = candidates
                .iter()
                .map(|(&(did, idx), target)| {
                    (
                        tcx.item_name(did.to_def_id()).to_string(),
                        idx,
                        target.exposed,
                    )
                })
                .collect();
            out.sort();
            out
        })
        .unwrap()
    }

    #[test]
    fn test_c_exposed_fn_is_marked_exposed() {
        // replaces test_c_exposed_fn_is_excluded: exposed fns are now candidates
        // carrying the exposed flag (the rewriter wraps them)
        assert_eq!(
            exposed_flags_for(SINGLE_FIELD, &["build"]),
            vec![("build".to_string(), 0, true)]
        );
    }

    #[test]
    fn test_export_name_c_exposed_fn_is_marked_exposed() {
        // c2rust emits #[export_name] when the C symbol differs from the Rust
        // item name; the c_exposed_fns set is keyed on the C symbol, so the
        // exposed flag must check export_name, not just the Rust item name
        let code = r#"
use ::libc;
#[repr(C)]
pub struct st {
    pub lookup: [u16; 4],
    pub lit: [u32; 4],
}
#[export_name = "exposed_c_name"]
pub unsafe extern "C" fn build(mut s: *mut st) -> libc::c_int {
    (*s).lookup[0] = 1 as u16;
    return 0 as libc::c_int;
}
"#;
        assert_eq!(
            exposed_flags_for(code, &["exposed_c_name"]),
            vec![("build".to_string(), 0, true)]
        );
    }

    #[test]
    fn test_forwarding_caller_is_also_candidate() {
        // summary propagation attributes build's lookup access to caller's param
        let code = r#"
use ::libc;
#[repr(C)]
pub struct st {
    pub lookup: [u16; 4],
    pub lit: [u32; 4],
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

    #[test]
    fn test_single_field_struct_is_filtered() {
        // a one-field struct makes the "field pointer" byte-equivalent to the
        // struct pointer; narrowing is churn, so the candidate is filtered
        let code = r#"
use ::libc;
#[repr(C)]
pub struct rnd {
    pub state: [u64; 2],
}
pub unsafe extern "C" fn next(mut r: *mut rnd) -> libc::c_int {
    (*r).state[0] = 1 as u64;
    return 0 as libc::c_int;
}
"#;
        assert_eq!(candidates_for(code), vec![]);
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
    pub lit: [u32; 4],
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

    fn plan_for(code: &str) -> (Vec<(String, usize, String)>, usize) {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = build_rust_program(tcx);
            let flows = pointer_flow_analysis(&program, &FxHashSet::default());
            let nullity = crate::analyses::nullity::NullityResult {
                non_null_params: FxHashMap::default(),
                non_null_locals: FxHashMap::default(),
            };
            let plan = find_plan(&program, &flows, &nullity, &FxHashSet::default());
            let mut targets: Vec<(String, usize, String)> = plan
                .targets
                .iter()
                .map(|(&(did, idx), target)| {
                    (
                        tcx.item_name(did.to_def_id()).to_string(),
                        idx,
                        target.field_name.to_string(),
                    )
                })
                .collect();
            targets.sort();
            (targets, plan.forwards.len())
        })
        .unwrap()
    }

    // returns sorted (caller fn, arg idx, emission) triples for a callee name
    fn emissions_for(code: &str, callee: &str) -> Vec<(String, usize, String)> {
        ::utils::compilation::run_compiler_on_str(code, |tcx| {
            let program = build_rust_program(tcx);
            let flows = pointer_flow_analysis(&program, &FxHashSet::default());
            let nullity = crate::analyses::nullity::NullityResult {
                non_null_params: FxHashMap::default(),
                non_null_locals: FxHashMap::default(),
            };
            let plan = find_plan(&program, &flows, &nullity, &FxHashSet::default());
            let mut out: Vec<(String, usize, String)> = plan
                .site_emissions
                .iter()
                .filter(|((_, _, _), _)| true)
                .map(|(&(caller, _, idx), em)| {
                    (
                        tcx.item_name(caller.to_def_id()).to_string(),
                        idx,
                        format!("{em:?}"),
                    )
                })
                .collect();
            let _ = callee;
            out.sort();
            out
        })
        .unwrap()
    }

    #[test]
    fn test_field_sibling_site_is_direct() {
        let emissions = emissions_for(TRIGGERED, "build");
        assert!(
            emissions.contains(&("fixed".to_string(), 0, "Direct".to_string())),
            "expected Direct emission for fixed's site, got {emissions:?}"
        );
    }

    #[test]
    #[ignore = "enabled with guarded emission"]
    fn test_unprovable_site_is_guarded() {
        // stranger has neither a sibling field pointer nor a nullity fact for
        // its argument to build: the site is unprovable and must be Guarded,
        // not dropped
        let code = r#"
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
pub unsafe extern "C" fn stranger(mut s: *mut st, mut tree: *mut u32, mut flag: libc::c_int) -> libc::c_int {
    let mut p: *mut st = 0 as *mut st;
    if flag != 0 {
        p = s;
    }
    return build(p, tree);
}
"#;
        let emissions = emissions_for(code, "build");
        assert!(
            emissions.contains(&("stranger".to_string(), 0, "Guarded".to_string())),
            "expected Guarded emission for stranger's site, got {emissions:?}"
        );
        let (targets, _) = plan_for(code);
        assert!(
            !targets.is_empty(),
            "build must remain selected once unprovable sites are guarded, not dropped"
        );
    }

    #[test]
    #[ignore = "enabled with guarded emission"]
    fn test_forward_on_unselected_is_guarded() {
        // outer2 is an untriggered candidate caller that forwards its own
        // param into inner; inner is selected via the sibling trigger in
        // top->outer, but outer2 itself never triggers selection (it has no
        // sibling field pointer and no nullity fact), so its forward
        // degrades to Guarded rather than dropping inner. like test B, this
        // depends on guarded_live=true (a Forward to an unselected caller
        // has no other usable class), so it is ignored until Task 2 flips
        // the flag
        let code = r#"
use ::libc;
#[repr(C)]
pub struct st {
    pub lookup: [u16; 4],
    pub lit: [u32; 4],
}
pub unsafe extern "C" fn inner(mut s: *mut st) -> libc::c_int {
    (*s).lookup[1] = 2 as u16;
    return 0 as libc::c_int;
}
pub unsafe extern "C" fn outer(mut s: *mut st, mut tree: *mut u32) -> libc::c_int {
    (*s).lookup[0] = 1 as u16;
    *tree.offset(0) = 0 as u32;
    return inner(s);
}
pub unsafe extern "C" fn top(mut s: *mut st) -> libc::c_int {
    return outer(s, ((*s).lit).as_mut_ptr());
}
pub unsafe extern "C" fn outer2(mut s: *mut st) -> libc::c_int {
    return inner(s);
}
"#;
        let emissions = emissions_for(code, "inner");
        assert!(
            emissions.contains(&("outer2".to_string(), 0, "Guarded".to_string())),
            "expected Guarded emission for outer2's site, got {emissions:?}"
        );
        let (targets, _) = plan_for(code);
        assert!(
            targets.iter().any(|(name, _, _)| name == "inner"),
            "inner must stay selected, got {targets:?}"
        );
    }

    #[test]
    fn test_plan_selects_triggered_fn_with_null_and_field_sites() {
        // TRIGGERED plus a null-literal call site: both classes rewritable
        let code = r#"
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
pub unsafe extern "C" fn dynamic(mut s: *mut st) -> libc::c_int {
    return build(0 as *mut st, ((*s).lit).as_mut_ptr());
}
"#;
        let (targets, _) = plan_for(code);
        assert_eq!(
            targets,
            vec![("build".to_string(), 0, "lookup".to_string())]
        );
    }

    #[test]
    fn test_plan_closes_over_forwarding() {
        let code = r#"
use ::libc;
#[repr(C)]
pub struct st {
    pub lookup: [u16; 4],
    pub lit: [u32; 4],
}
pub unsafe extern "C" fn inner(mut s: *mut st) -> libc::c_int {
    (*s).lookup[1] = 2 as u16;
    return 0 as libc::c_int;
}
pub unsafe extern "C" fn outer(mut s: *mut st, mut tree: *mut u32) -> libc::c_int {
    (*s).lookup[0] = 1 as u16;
    *tree.offset(0) = 0 as u32;
    return inner(s);
}
pub unsafe extern "C" fn top(mut s: *mut st) -> libc::c_int {
    return outer(s, ((*s).lit).as_mut_ptr());
}
"#;
        let (targets, forwards) = plan_for(code);
        assert_eq!(
            targets,
            vec![
                ("inner".to_string(), 0, "lookup".to_string()),
                ("outer".to_string(), 0, "lookup".to_string()),
            ]
        );
        assert_eq!(forwards, 1);
    }

    #[test]
    fn test_unrewritable_call_site_drops_target_and_cascades() {
        // extra caller passes a maybe-null variable with no sibling field
        // pointer and no nullity fact: inner is unrewritable, and outer
        // (which forwards into inner) must fall with it
        let code = r#"
use ::libc;
#[repr(C)]
pub struct st {
    pub lookup: [u16; 4],
    pub lit: [u32; 4],
}
pub unsafe extern "C" fn inner(mut s: *mut st) -> libc::c_int {
    if !s.is_null() {
        (*s).lookup[1] = 2 as u16;
    }
    return 0 as libc::c_int;
}
pub unsafe extern "C" fn outer(mut s: *mut st, mut tree: *mut u32) -> libc::c_int {
    (*s).lookup[0] = 1 as u16;
    *tree.offset(0) = 0 as u32;
    return inner(s);
}
pub unsafe extern "C" fn top(mut s: *mut st) -> libc::c_int {
    return outer(s, ((*s).lit).as_mut_ptr());
}
pub unsafe extern "C" fn stray(mut s: *mut st, mut flag: libc::c_int) -> libc::c_int {
    let mut p: *mut st = 0 as *mut st;
    if flag != 0 {
        p = s;
    }
    return inner(p);
}
"#;
        let (targets, _) = plan_for(code);
        assert_eq!(targets, vec![]);
    }

    #[test]
    fn test_read_only_field_demotes_to_const() {
        // build only reads (*s).lookup through a declared *mut param; minimal
        // privilege lets the specialization carry *const instead, freeing
        // downstream borrow promotion to choose a shared reference at call sites
        let code = r#"
use ::libc;
#[repr(C)]
pub struct st {
    pub lookup: [u16; 4],
    pub lit: [u32; 4],
}
pub unsafe extern "C" fn build(mut s: *mut st) -> libc::c_int {
    return (*s).lookup[0] as libc::c_int;
}
"#;
        assert_eq!(
            candidates_with_mutbl_for(code),
            vec![(
                "build".to_string(),
                0,
                "lookup".to_string(),
                ty::Mutability::Not
            )]
        );
    }

    #[test]
    fn test_written_field_keeps_mut() {
        let code = r#"
use ::libc;
#[repr(C)]
pub struct st {
    pub lookup: [u16; 4],
    pub lit: [u32; 4],
}
pub unsafe extern "C" fn build(mut s: *mut st) -> libc::c_int {
    (*s).lookup[0] = 1 as u16;
    return 0 as libc::c_int;
}
"#;
        assert_eq!(
            candidates_with_mutbl_for(code),
            vec![(
                "build".to_string(),
                0,
                "lookup".to_string(),
                ty::Mutability::Mut
            )]
        );
    }

    #[test]
    fn test_address_taken_field_keeps_mut() {
        // as_mut_ptr on the field yields an Address-kind access that may feed a
        // write (e.g. through a memset-style callee) even though this function
        // body itself performs no direct Write projection; conservatively keeps
        // the declared mutability
        let code = r#"
use ::libc;
#[repr(C)]
pub struct st {
    pub lookup: [u16; 4],
    pub lit: [u32; 4],
}
pub unsafe extern "C" fn sink(mut p: *mut u16) -> libc::c_int {
    *p.offset(0) = 1 as u16;
    return 0 as libc::c_int;
}
pub unsafe extern "C" fn build(mut s: *mut st) -> libc::c_int {
    return sink(((*s).lookup).as_mut_ptr());
}
"#;
        assert_eq!(
            candidates_with_mutbl_for(code),
            vec![(
                "build".to_string(),
                0,
                "lookup".to_string(),
                ty::Mutability::Mut
            )]
        );
    }
}
