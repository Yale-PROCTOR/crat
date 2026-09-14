//! Return-independence evidence for forward slice parameters at raw seams.
//! This never grants retention or write permission: it only discharges the
//! separate question whether a returned value carries the source's address.

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    ExprKind, HirId, QPath,
    def::Res,
    def_id::LocalDefId,
    intravisit::{self, Visitor},
};
use rustc_middle::{
    mir::{Local, Operand, RETURN_PLACE, Rvalue, StatementKind, TerminatorKind},
    ty::{TyCtxt, TyKind},
};

use super::raw_boundary::{RawBoundarySiteFacts, RawBoundarySiteKey};
use crate::utils::rustc::RustProgram;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ReturnIndependence {
    FreshMalloc(String),
    ScalarUseClosure,
}

impl std::fmt::Display for ReturnIndependence {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::FreshMalloc(callee) => {
                write!(f, "forward-slice-return-independent:fresh-malloc:{callee}")
            }
            Self::ScalarUseClosure => {
                f.write_str("forward-slice-return-independent:scalar-use-closure")
            }
        }
    }
}

fn forward_parameter(tcx: TyCtxt<'_>, owner: LocalDefId, binding: HirId) -> bool {
    let body = tcx.hir_body_owned_by(owner);
    if !body.params.iter().any(|param| param.pat.hir_id == binding) {
        return false;
    }
    struct Walk {
        binding: HirId,
        found: bool,
    }
    impl<'tcx> Visitor<'tcx> for Walk {
        fn visit_expr(&mut self, expression: &'tcx rustc_hir::Expr<'tcx>) {
            if let ExprKind::Assign(lhs, rhs, _) = expression.kind
                && matches!(lhs.kind, ExprKind::Path(QPath::Resolved(_, path)) if path.res == Res::Local(self.binding))
                && let ExprKind::MethodCall(segment, receiver, [_], _) = rhs.kind
                && segment.ident.name.as_str() == "offset"
                && matches!(receiver.kind, ExprKind::Path(QPath::Resolved(_, path)) if path.res == Res::Local(self.binding))
            {
                self.found = true;
            }
            intravisit::walk_expr(self, expression);
        }
    }
    let mut walk = Walk {
        binding,
        found: false,
    };
    walk.visit_body(body);
    walk.found
}

/// A complete backward slice of the return value contains only pointer copies,
/// pointer casts, and exact foreign malloc results. All definitions participate;
/// a mixed input origin, an address-taken carrier, or a cycle refuses the proof.
fn fresh_return(program: &RustProgram<'_>, callee: LocalDefId) -> bool {
    let tcx = program.tcx;
    let signature = tcx.fn_sig(callee).skip_binder().skip_binder();
    if !signature.output().is_raw_ptr()
        || signature.inputs().iter().any(|ty| matches!(ty.kind(), TyKind::RawPtr(_, mutability) | TyKind::Ref(_, _, mutability) if mutability.is_mut()))
    { return false; }
    let body = tcx.mir_drops_elaborated_and_const_checked(callee).borrow();
    let mut definitions = FxHashMap::<Local, Vec<Option<Local>>>::default();
    let mut unsupported = FxHashSet::default();
    let mut address_taken = FxHashSet::default();
    for block in body.basic_blocks.iter() {
        if matches!(
            block.terminator().kind,
            TerminatorKind::TailCall { .. } | TerminatorKind::InlineAsm { .. }
        ) {
            return false;
        }
        for statement in &block.statements {
            let StatementKind::Assign(assignment) = &statement.kind else { continue };
            let (place, value) = &**assignment;
            if let Rvalue::Ref(_, _, addressed) | Rvalue::RawPtr(_, addressed) = value {
                if !addressed.is_indirect() {
                    address_taken.insert(addressed.local);
                }
            }
            let Some(destination) = place.as_local() else { continue };
            if !body.local_decls[destination].ty.is_raw_ptr() {
                continue;
            }
            let operand = match value {
                Rvalue::Use(operand) => Some(operand),
                Rvalue::Cast(_, operand, target)
                    if target.is_raw_ptr() && operand.ty(&body.local_decls, tcx).is_raw_ptr() =>
                {
                    Some(operand)
                }
                _ => None,
            };
            match operand
                .and_then(Operand::place)
                .and_then(|place| place.as_local())
            {
                Some(source) => definitions
                    .entry(destination)
                    .or_default()
                    .push(Some(source)),
                None => {
                    unsupported.insert(destination);
                }
            }
        }
        if let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &block.terminator().kind
            && let Some(destination) = destination.as_local()
            && body.local_decls[destination].ty.is_raw_ptr()
        {
            let allocator = func
                .constant()
                .and_then(|constant| match constant.ty().kind() {
                    TyKind::FnDef(definition, _) => Some(*definition),
                    _ => None,
                });
            let fresh = allocator.is_some_and(|definition| {
                let symbol = super::raw_boundary::symbol_key(tcx, definition, &program.functions);
                let sig = tcx.fn_sig(definition).skip_binder().skip_binder();
                symbol.foreign
                    && symbol.symbol == "malloc"
                    && symbol.abi.starts_with('C')
                    && args.len() == 1
                    && sig.inputs().len() == 1
                    && matches!(sig.inputs()[0].kind(), TyKind::Uint(_))
                    && matches!(sig.output().kind(), TyKind::RawPtr(_, mutable) if mutable.is_mut())
            });
            if fresh {
                definitions.entry(destination).or_default().push(None);
            } else {
                unsupported.insert(destination);
            }
        }
    }
    fn prove(
        local: Local,
        definitions: &FxHashMap<Local, Vec<Option<Local>>>,
        unsupported: &FxHashSet<Local>,
        addressed: &FxHashSet<Local>,
        visiting: &mut FxHashSet<Local>,
    ) -> bool {
        if unsupported.contains(&local) || addressed.contains(&local) || !visiting.insert(local) {
            return false;
        }
        let result = definitions.get(&local).is_some_and(|values| {
            !values.is_empty()
                && values.iter().all(|value| {
                    value.is_none_or(|source| {
                        prove(source, definitions, unsupported, addressed, visiting)
                    })
                })
        });
        visiting.remove(&local);
        result
    }
    prove(
        RETURN_PLACE,
        &definitions,
        &unsupported,
        &address_taken,
        &mut FxHashSet::default(),
    )
}

pub(crate) fn collect(
    program: &RustProgram<'_>,
    facts: &RawBoundarySiteFacts,
) -> FxHashMap<RawBoundarySiteKey, ReturnIndependence> {
    let mut proofs = FxHashMap::default();
    let mut fresh = FxHashMap::default();
    let mut forward = FxHashMap::default();
    for site in &facts.sites {
        let Some((owner, binding)) = site.node else { continue };
        if !*forward
            .entry((owner, binding))
            .or_insert_with(|| forward_parameter(program.tcx, owner, binding))
        {
            continue;
        }
        if let Some(callee) = site.callee_local
            && *fresh
                .entry(callee)
                .or_insert_with(|| fresh_return(program, callee))
        {
            proofs.insert(
                site.key.clone(),
                ReturnIndependence::FreshMalloc(program.tcx.def_path_str(callee.to_def_id())),
            );
        } else if super::slice_scalar_return::proves(program.tcx, owner, &site.key) {
            proofs.insert(site.key.clone(), ReturnIndependence::ScalarUseClosure);
        }
    }
    proofs
}

#[cfg(test)]
mod tests {
    fn proves(source: &str) -> bool {
        ::utils::compilation::run_compiler_on_str(source, |tcx| {
            let functions: Vec<_> = tcx.hir_body_owners().collect();
            let callee = *functions
                .iter()
                .find(|function| tcx.item_name(function.to_def_id()).as_str() == "target")
                .unwrap();
            super::fresh_return(
                &super::RustProgram {
                    tcx,
                    functions,
                    structs: Vec::new(),
                },
                callee,
            )
        })
        .expect("fresh-return fixture must type-check")
    }

    #[test]
    fn wave6s_fresh_allocation_return_is_independent() {
        assert!(proves(
            r#"
            unsafe extern "C" { fn malloc(n: usize) -> *mut core::ffi::c_void; }
            pub unsafe fn target(input: *const i8) -> *mut i8 {
                let dup = malloc(8) as *mut i8;
                *dup = *input;
                return dup;
            }
        "#
        ));
    }

    #[test]
    fn wave6s_returned_input_is_not_fresh() {
        assert!(!proves(
            "pub unsafe fn target(input: *const i8) -> *mut i8 { input as *mut i8 }"
        ));
    }

    #[test]
    fn wave6s_mixed_return_is_not_fresh() {
        assert!(!proves(
            r#"
            unsafe extern "C" { fn malloc(n: usize) -> *mut core::ffi::c_void; }
            pub unsafe fn target(input: *const i8, choose: bool) -> *mut i8 {
                if choose { return input as *mut i8; }
                malloc(8) as *mut i8
            }
        "#
        ));
    }

    #[test]
    fn wave6s_local_allocator_spelling_is_not_a_contract() {
        assert!(!proves(
            r#"
            unsafe fn malloc(n: usize) -> *mut core::ffi::c_void { n as *mut core::ffi::c_void }
            pub unsafe fn target(input: *const i8) -> *mut i8 { malloc(8) as *mut i8 }
        "#
        ));
    }

    #[test]
    fn wave6s_address_taken_return_carrier_is_not_fresh() {
        assert!(!proves(
            r#"
            unsafe extern "C" { fn malloc(n: usize) -> *mut core::ffi::c_void; }
            pub unsafe fn target(input: *const i8) -> *mut i8 {
                let mut dup = malloc(8) as *mut i8;
                let address = &mut dup;
                *address = input as *mut i8;
                dup
            }
        "#
        ));
    }

    #[test]
    fn wave6s_pointer_output_channel_is_not_return_only() {
        assert!(!proves(
            r#"
            unsafe extern "C" { fn malloc(n: usize) -> *mut core::ffi::c_void; }
            pub unsafe fn target(input: *const i8, out: *mut *const i8) -> *mut i8 {
                *out = input;
                malloc(8) as *mut i8
            }
        "#
        ));
    }
}

/// A raw tail consumer is not bounded by the slice indexing checks. A thin
/// caller cannot supply its full extent through a one-element from_ref view.
pub(crate) fn needs_full_base(
    tcx: TyCtxt<'_>,
    parameter: &super::Subject,
    uses: &super::emitability::SliceUses,
) -> bool {
    uses.raw_uses
        .iter()
        .any(|site| site.boundary_span.is_some())
        && forward_parameter(tcx, parameter.fn_did, parameter.hir_id)
}

/// An adjacent prefix count does not cover the remaining string copied by a
/// fresh-return consumer. Keep that adjacency in LenArm, but fabricate the
/// actual extent through the existing typed fallback constructor.
pub(crate) fn companion_for_tail(
    table: &super::DecisionTable,
    raw: &super::raw_boundary::RawBoundaryDispositionIndex,
    callee: LocalDefId,
    index: usize,
    companion: Option<String>,
) -> Option<String> {
    let node = table.entries.iter().find_map(|(subject, _)| {
        (subject.fn_did == callee && matches!(subject.kind, super::SubjectKind::Param { hir_index } if hir_index == index))
            .then_some((subject.fn_did, subject.hir_id))
    });
    if raw.inventoried_sites().any(|(key, _, site)| {
        site.node == node
            && node.is_some()
            && matches!(
                raw.return_independent(key),
                Some(ReturnIndependence::FreshMalloc(_))
            )
    }) {
        None
    } else {
        companion
    }
}
