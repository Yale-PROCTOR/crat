//! Construction-owned licensing inputs. Export may copy these facts, but is
//! never their producer or an input to this carrier.

use std::{cell::RefCell, collections::BTreeMap, rc::Rc};

use rustc_index::IndexVec;
use z3::ast::Bool;

use super::super::{
    ownership_boundary::{CallArgRegistration, Substitution},
    ownership_evidence::Equation,
    ownership_occurrence::{Consumption, Terminal},
    ssa::constraint::Var,
};

/// Index into this construction's recorded equations, independent of Z3 names.
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize,
)]
pub(crate) struct EquationId {
    pub(crate) construction: u32,
    pub(crate) ordinal: usize,
}

/// The actual emitted predicate, retained alongside its diagnostic equation.
#[derive(Clone, Debug)]
pub(crate) struct GuardBinding {
    pub(crate) equation: EquationId,
    pub(crate) predicate: Bool,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct Facts {
    /// Explicit existing FrozenBenchmarkGraph frame, never inferred from calls.
    pub(crate) frame_attested: bool,
    pub(crate) constructions: u32,
    pub(crate) licensing: Option<Rc<super::snapshot::FrozenTransport>>,
    pub(crate) body_rosters: Vec<super::coverage::BodyRoster>,
    pub(crate) return_selections: Vec<super::coverage::ReturnSelection>,
    pub(crate) phi_edges: Vec<super::coverage::PhiEdge>,
    pub(crate) equations: Vec<Equation>,
    pub(crate) consumes: Vec<Consumption>,
    pub(crate) terminals: Vec<Terminal>,
    pub(crate) boundary_substitutions: Vec<Substitution>,
    pub(crate) call_arg_registrations: Vec<CallArgRegistration>,
    pub(crate) guards: Vec<GuardBinding>,
    /// Filled by moving the real database's indexed AST vector at freeze.
    pub(crate) ownership_asts: IndexVec<Var, Bool>,
    pub(crate) source_occurrences:
        BTreeMap<String, Vec<super::super::origin_evidence::SourceOccurrence>>,
    /// Canonical names are resolved from the compiler, never parsed back into IDs.
    pub(crate) slot_refs: BTreeMap<String, super::super::solver::SlotRef>,
    pub(crate) raw_pointer_heads: Vec<super::value_origins::RawHead>,
    /// Compiler type evidence for unit temporaries, whose missing ownership
    /// consume is intentional rather than an unrepresented pointer.
    pub(crate) unit_locals: Vec<(String, u32)>,
    pub(crate) reader_inputs: super::readers::Inputs,
    pub(crate) reader_plan: super::readers::Plan,
    /// The lend plan: empty unless the lend is switched on.
    pub(crate) lend_plan: super::lend::Plan,
    pub(crate) field_support_inputs: super::field_support::Inputs,
    pub(crate) caller_coverage: Option<super::caller_coverage::Coverage>,
    pub(crate) traversal_native: Option<super::traversal_native::Inputs>,
    pub(crate) fold_types: Option<super::fold_types::Inputs>,
    pub(crate) fold_declarations: Option<Vec<super::fold_declaration::Declaration>>,
    /// The digest of every other field when `licensing` was frozen from them
    /// ([`licensing_inputs_digest`]); the snapshot is read only by facts that still digest to it.
    pub(crate) licensing_inputs: Option<[u8; 32]>,
}

/// SHA-256 over the `Debug` form of everything the licensing snapshot
/// is built from -- every field but the snapshot and this digest. Equal digests mean the snapshot's
/// derivation (a function of these facts) would come out the same, so a reader compares this
/// instead of re-deriving the snapshot.
pub(crate) fn licensing_inputs_digest(facts: &Facts) -> [u8; 32] {
    use std::fmt::Write;

    use sha2::Digest;

    struct Sink(sha2::Sha256);
    impl Write for Sink {
        fn write_str(&mut self, text: &str) -> std::fmt::Result {
            self.0.update(text.as_bytes());
            Ok(())
        }
    }
    let Facts {
        frame_attested,
        constructions,
        licensing: _,
        body_rosters,
        return_selections,
        phi_edges,
        equations,
        consumes,
        terminals,
        boundary_substitutions,
        call_arg_registrations,
        guards,
        ownership_asts,
        source_occurrences,
        slot_refs,
        raw_pointer_heads,
        unit_locals,
        reader_inputs,
        reader_plan,
        lend_plan,
        field_support_inputs,
        caller_coverage,
        traversal_native,
        fold_types,
        fold_declarations,
        licensing_inputs: _,
    } = facts;
    let mut sink = Sink(sha2::Sha256::new());
    let fields: [&dyn std::fmt::Debug; 23] = [
        frame_attested,
        constructions,
        body_rosters,
        return_selections,
        phi_edges,
        equations,
        consumes,
        terminals,
        boundary_substitutions,
        call_arg_registrations,
        guards,
        ownership_asts,
        source_occurrences,
        slot_refs,
        raw_pointer_heads,
        unit_locals,
        reader_inputs,
        reader_plan,
        lend_plan,
        field_support_inputs,
        caller_coverage,
        traversal_native,
        fold_types,
    ];
    for field in fields {
        write!(sink, "{field:?}\u{1f}").expect("digest sink");
    }
    write!(sink, "{fold_declarations:?}").expect("digest sink");
    sink.0.finalize().into()
}

pub(crate) type Builder = Rc<RefCell<Facts>>;

thread_local! {
    static ACTIVE: RefCell<Option<Builder>> = const { RefCell::new(None) };
}

/// Restores an enclosing construction on normal return and unwind.
pub(crate) struct Scope {
    previous: Option<Builder>,
}

impl Drop for Scope {
    fn drop(&mut self) {
        ACTIVE.with(|active| *active.borrow_mut() = self.previous.take());
    }
}

pub(crate) fn activate(builder: &Builder) -> Scope {
    Scope {
        previous: ACTIVE.with(|active| active.replace(Some(Rc::clone(builder)))),
    }
}

pub(crate) fn active() -> bool {
    ACTIVE.with(|active| active.borrow().is_some())
}

/// Existing producer helpers append to the database-owned builder. Absence
/// stays explicit; it is never replaced with an empty positive fact set.
pub(crate) fn record<T>(f: impl FnOnce(&mut Facts) -> T) -> Option<T> {
    let builder = ACTIVE.with(|active| active.borrow().clone())?;
    let mut facts = builder.borrow_mut();
    Some(f(&mut facts))
}

/// Read exact correspondence from the same builder used by the producers.
pub(crate) fn read<T>(f: impl FnOnce(&Facts) -> T) -> Option<T> {
    let builder = ACTIVE.with(|active| active.borrow().clone())?;
    let facts = builder.borrow();
    Some(f(&facts))
}

/// End the active scope before freezing. Moving the builder ensures no mutable
/// alias survives into the solver's immutable facts. An optional exporter can
/// copy the resulting DTO vectors without consulting or changing this state.
pub(crate) fn freeze(
    builder: Builder,
    ownership_asts: IndexVec<Var, Bool>,
) -> anyhow::Result<Rc<Facts>> {
    let mut facts = Rc::try_unwrap(builder)
        .unwrap_or_else(|_| panic!("licensing facts still have an active builder alias"))
        .into_inner();
    facts.ownership_asts = ownership_asts;
    facts.licensing = Some(Rc::new(super::snapshot::FrozenTransport::build(&facts)?));
    crate::phase_log::mark("freeze:licensing_inputs_digest", "start", "");
    crate::analysis_budget::check("freeze:licensing_inputs_digest")?;
    facts.licensing_inputs = Some(licensing_inputs_digest(&facts));
    crate::phase_log::mark("freeze:licensing_inputs_digest", "end", "");
    Ok(Rc::new(facts))
}
