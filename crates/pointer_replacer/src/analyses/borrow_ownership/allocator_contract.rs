//! R409-1 (era-5c): the allocator contract
//! `allocator-contract:brotli-memory-manager/v1@2026-09-15`.
//!
//! brotli allocates through a memory manager: `(*m).alloc_func.expect(..)
//! (opaque, size)` returns a fresh allocation of `size` bytes owned by the
//! caller (brotli's own `exit(1)` guard makes `BrotliAllocate`'s result
//! non-null), released exactly once through `(*m).free_func.expect(..)
//! (opaque, p)`, and nothing else frees it. The default pair is
//! `BrotliDefaultAllocFunc` / `BrotliDefaultFreeFunc` = `malloc` / `free`; the
//! external pair is assumed to honour the same contract (brotli's documented
//! API) — a USER decision, receipted per site, stated in the claims-facing
//! documents.
//!
//! What the model does under `CRAT_ERA5C_ALLOCATOR_CONTRACT=on`: an indirect
//! call whose callee is the `expect`/`unwrap` of an `alloc_func`-named field
//! with the allocation signature is an ownership SOURCE (selector-gated,
//! receipted with the contract name as its callee); one through a
//! `free_func`-named field with the release signature is an ownership SINK;
//! every other indirect call — a `TODO` in the default arm, whose result
//! floats and settles `Owning` by the objective's preference — is an unknown
//! call (destination borrowed, arguments lent). A contract allocation reaching
//! a libc sink, or a libc allocation reaching a contract sink, is refused
//! (`allocator-contract-pairing`): the pointer stays raw rather than freed
//! through the wrong allocator.

use rustc_middle::{
    mir::{
        BasicBlock, Body, Local, Location, Operand, Place, Rvalue, StatementKind, TerminatorKind,
    },
    ty::{Ty, TyCtxt, TyKind},
};

pub(crate) const CONTRACT: &str = "allocator-contract:brotli-memory-manager/v1";

/// R409-1: the contract arm. Its own pin, fail-loud, carried by `solver_identity`.
pub(crate) fn enabled() -> bool {
    static ONCE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ONCE.get_or_init(|| match std::env::var("CRAT_ERA5C_ALLOCATOR_CONTRACT") {
        Err(std::env::VarError::NotPresent) => false,
        Ok(value) => match value.as_str() {
            "on" => true,
            "off" => false,
            other => panic!("CRAT_ERA5C_ALLOCATOR_CONTRACT must be on or off; got {other:?}"),
        },
        Err(error) => panic!("CRAT_ERA5C_ALLOCATOR_CONTRACT is not valid Unicode: {error}"),
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ContractCall {
    /// `alloc_func(opaque, size) -> *mut c_void`: the result is a fresh allocation.
    Alloc,
    /// `free_func(opaque, p)`: argument 1 is released.
    Free,
}

fn is_c_void_ptr(tcx: TyCtxt<'_>, ty: Ty<'_>) -> bool {
    match ty.kind() {
        TyKind::RawPtr(pointee, _) => match pointee.kind() {
            TyKind::Adt(adt, _) => tcx.item_name(adt.did()).as_str() == "c_void",
            _ => false,
        },
        _ => false,
    }
}

/// The contract's two signatures, on a fn-pointer type.
fn signature_class(tcx: TyCtxt<'_>, ty: Ty<'_>) -> Option<ContractCall> {
    let TyKind::FnPtr(sig, _) = ty.kind() else {
        return None;
    };
    let sig = sig.skip_binder();
    let inputs = sig.inputs();
    if inputs.len() != 2 || !is_c_void_ptr(tcx, inputs[0]) {
        return None;
    }
    if inputs[1].is_integral() && is_c_void_ptr(tcx, sig.output()) {
        return Some(ContractCall::Alloc);
    }
    if is_c_void_ptr(tcx, inputs[1]) && sig.output().is_unit() {
        return Some(ContractCall::Free);
    }
    None
}

/// The field a fn-pointer local was loaded from: `_f = copy (*x).field` in
/// `block` before `index`, or anywhere in the body when the local is defined
/// once. Returns the field's name.
fn field_source_name<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, local: Local) -> Option<String> {
    for data in body.basic_blocks.iter() {
        for statement in &data.statements {
            let StatementKind::Assign(assign) = &statement.kind else {
                continue;
            };
            let (dst, rvalue) = &**assign;
            if dst.as_local() != Some(local) {
                continue;
            }
            let Rvalue::Use(Operand::Copy(place) | Operand::Move(place)) = rvalue else {
                return None;
            };
            return field_name_of(tcx, body, place);
        }
    }
    None
}

fn field_name_of<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    place: &Place<'tcx>,
) -> Option<String> {
    let mut base = Place::from(place.local).ty(body, tcx).ty;
    let mut name = None;
    for elem in place.projection {
        match elem {
            rustc_middle::mir::ProjectionElem::Deref => base = base.builtin_deref(true)?,
            rustc_middle::mir::ProjectionElem::Field(field, ty) => {
                let TyKind::Adt(adt, _) = base.kind() else { return None };
                if !adt.is_struct() {
                    return None;
                }
                name = Some(adt.non_enum_variant().fields[field].name.to_string());
                base = ty;
            }
            _ => return None,
        }
    }
    name
}

/// Classify the call terminator at `location` (an indirect call) under the
/// contract: the callee operand is a local defined by `Option::expect` /
/// `unwrap` of a field named `alloc_func` / `free_func` whose fn-pointer type
/// carries the matching signature.
pub(crate) fn classify<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    location: Location,
) -> Option<ContractCall> {
    if !enabled() {
        return None;
    }
    let data = &body.basic_blocks[location.block];
    if location.statement_index != data.statements.len() {
        return None;
    }
    let TerminatorKind::Call { func, .. } = &data.terminator().kind else {
        return None;
    };
    if func.constant().is_some() {
        return None;
    }
    let dbg = std::env::var_os("CRAT_ERA5C_DEBUG").is_some();
    let class = signature_class(tcx, func.ty(body, tcx));
    if dbg {
        eprintln!("E5C classify: signature {class:?}");
    }
    let class = class?;
    let callee_local = func.place()?.as_local()?;
    // The callee local is the destination of an `expect` / `unwrap` call whose
    // first argument was loaded from the named field.
    let mut option_arg: Option<Local> = None;
    for (bb, data) in body.basic_blocks.iter_enumerated() {
        let _: BasicBlock = bb;
        let TerminatorKind::Call {
            func: unwrap,
            args,
            destination,
            ..
        } = &data.terminator().kind
        else {
            continue;
        };
        if destination.as_local() != Some(callee_local) {
            continue;
        }
        let Some((def_id, _)) = unwrap.const_fn_def() else {
            return None;
        };
        let name = tcx.item_name(def_id);
        if !matches!(name.as_str(), "expect" | "unwrap") {
            return None;
        }
        option_arg = args.first().and_then(|arg| arg.node.place()?.as_local());
        break;
    }
    if dbg {
        eprintln!("E5C classify: option_arg {option_arg:?}");
    }
    let field = field_source_name(tcx, body, option_arg?);
    if dbg {
        eprintln!("E5C classify: field {field:?}");
    }
    let field = field?;
    match (class, field.as_str()) {
        (ContractCall::Alloc, "alloc_func") | (ContractCall::Free, "free_func") => Some(class),
        _ => None,
    }
}

/// The allocator class of an endpoint by its recorded callee: the contract's
/// pair, or libc's.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum AllocatorClass {
    Contract,
    Libc,
}

fn class_of(callee: &str) -> Option<AllocatorClass> {
    if callee == CONTRACT {
        Some(AllocatorClass::Contract)
    } else if super::boundary_table::lookup(callee, super::boundary_table::Matcher::ForeignC)
        .is_some()
    {
        Some(AllocatorClass::Libc)
    } else {
        None
    }
}

/// R409-1 pairing: an allocation must be released by its own allocator. For
/// every sink whose argument's value origins carry a `Fresh` source of the
/// OTHER class, the sink's argument is assumed non-owning — a hard row in the
/// family `allocator-contract-pairing` — so the sink's selector is leaked
/// (the free stays a raw-pointer free) and the pointer stays raw rather than
/// being freed through the wrong allocator. Pure over the recorded facts.
pub(crate) struct Refusal {
    pub(crate) var: super::ssa::constraint::Var,
    pub(crate) label: String,
    pub(crate) sink_class: AllocatorClass,
    pub(crate) function: String,
}

pub(crate) fn pairing_refusals(facts: &super::licensing::facts::Facts) -> Vec<Refusal> {
    use super::{
        licensing::{
            transport::CandidateGraph,
            value_origins::{OriginAtom, ValueOrigins},
        },
        ssa::constraint::Var,
    };
    if !enabled() {
        return Vec::new();
    }
    let graph = CandidateGraph::build(facts);
    let origins = ValueOrigins::build(facts);
    let source_class: std::collections::BTreeMap<_, _> = graph
        .sources
        .iter()
        .filter_map(|source| Some((source.equation, class_of(&source.endpoint.callee)?)))
        .collect();
    let mut refusals = Vec::new();
    for sink in &graph.sinks {
        let Some(sink_class) = class_of(&sink.endpoint.callee) else {
            continue;
        };
        for atom in origins.at(sink.node) {
            let OriginAtom::Fresh(equation) = atom else {
                continue;
            };
            let Some(&class) = source_class.get(&equation) else {
                continue;
            };
            if class != sink_class {
                refusals.push(Refusal {
                    var: Var::from_u32(sink.node.var),
                    label: format!(
                        "allocator-contract-pairing({}:{}:{} {:?} frees {:?} allocation)",
                        sink.endpoint.function,
                        sink.endpoint.block,
                        sink.endpoint.statement,
                        sink_class,
                        class
                    ),
                    sink_class,
                    function: sink.endpoint.function.clone(),
                });
                break;
            }
        }
    }
    refusals
}

/// Per-construction state: the local functions whose bodies allocate through
/// the contract (the producers) and the guarded return ports their callers
/// took. Thread-local like the export cursors; reset at every emission.
#[derive(Default)]
struct State {
    producers: rustc_hash::FxHashSet<rustc_hir::def_id::DefId>,
    ports: Vec<Port>,
}

#[derive(Clone, Debug)]
pub(crate) struct Port {
    /// The caller's `def_path_str`.
    pub(crate) function: String,
    pub(crate) guard: z3::ast::Bool,
}

thread_local! {
    static STATE: std::cell::RefCell<State> = std::cell::RefCell::new(State::default());
}

/// Start a construction: forget the previous one and pre-compute the
/// producers by a pure MIR walk, so a caller emitted before its callee still
/// takes a guarded port.
pub(crate) fn prepare<'tcx>(tcx: TyCtxt<'tcx>, functions: &[rustc_hir::def_id::LocalDefId]) {
    STATE.with(|state| *state.borrow_mut() = State::default());
    if !enabled() {
        return;
    }
    for &function in functions {
        let body = tcx
            .mir_drops_elaborated_and_const_checked(function)
            .borrow();
        let producer = body.basic_blocks.iter_enumerated().any(|(bb, data)| {
            let location = Location {
                block: bb,
                statement_index: data.statements.len(),
            };
            classify(tcx, &body, location) == Some(ContractCall::Alloc)
        });
        if producer {
            note_producer(function.to_def_id());
        }
    }
}

pub(crate) fn note_producer(function: rustc_hir::def_id::DefId) {
    STATE.with(|state| {
        state.borrow_mut().producers.insert(function);
    });
}

pub(crate) fn is_producer(function: rustc_hir::def_id::DefId) -> bool {
    enabled() && STATE.with(|state| state.borrow().producers.contains(&function))
}

pub(crate) fn note_port(function: String, guard: z3::ast::Bool) {
    STATE.with(|state| state.borrow_mut().ports.push(Port { function, guard }));
}

pub(crate) fn ports() -> Vec<Port> {
    STATE.with(|state| state.borrow().ports.clone())
}

/// The functions that release a contract allocation through a libc sink:
/// every contract port they took is closed (`¬guard`), so the caller receives
/// a raw view and its libc free stays a raw-pointer free; the producer's own
/// token is untouched for every other caller.
pub(crate) fn misusing_functions(facts: &super::licensing::facts::Facts) -> Vec<String> {
    let mut functions: Vec<String> = pairing_refusals(facts)
        .into_iter()
        .filter(|refusal| refusal.sink_class == AllocatorClass::Libc)
        .map(|refusal| refusal.function)
        .collect::<Vec<_>>();
    functions.sort();
    functions.dedup();
    functions
}
