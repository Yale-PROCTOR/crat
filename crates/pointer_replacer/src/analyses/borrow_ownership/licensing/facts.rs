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
    pub(crate) field_support_inputs: super::field_support::Inputs,
    pub(crate) caller_coverage: Option<super::caller_coverage::Coverage>,
    pub(crate) traversal_native: Option<super::traversal_native::Inputs>,
    pub(crate) fold_types: Option<super::fold_types::Inputs>,
    pub(crate) fold_declarations: Option<Vec<super::fold_declaration::Declaration>>,
}

/// R351-3: which pass this construction is. Pass 1 is the era-5a solve as the
/// pin wrote it — none of era-5b's constraints are emitted and the solver is
/// never given licensing facts, so `coherence`'s dispatch falls through to the
/// unconditional `equate` by construction rather than by a second code path.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) enum Pass {
    /// Era-5b's constraints ride the era-5a solve. The measured co-solve.
    #[default]
    Joint,
    /// The pin's constraint system, unchanged.
    EraFiveA,
}

/// R371-2: the joint-pass repair arm. The two families the seat named as the
/// cause of the 52 `ref -> raw` — era-5b's guarded `equate` replacing the pin's
/// unconditional one, and the `no_ref_carriers` `¬ref` exclusion — are withdrawn
/// under `Joint` while every grant constraint stays on. It is an environment arm
/// so the default path is byte-identical and the repair is a measured arm, not a
/// silent behaviour change. Fail-loud on a typo, as `Pass` is.
pub(crate) fn repair() -> bool {
    static ONCE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ONCE.get_or_init(|| match std::env::var("CRAT_ERA5B_REPAIR") {
        Err(std::env::VarError::NotPresent) => false,
        Ok(value) => match value.as_str() {
            "on" => true,
            "off" => false,
            other => panic!("CRAT_ERA5B_REPAIR must be on or off; got {other:?}"),
        },
        Err(error) => panic!("CRAT_ERA5B_REPAIR is not valid Unicode: {error}"),
    })
}

/// R388-1: the licences the frame adds. Field support becomes a solver-level
/// conjunction over the store sources' origins instead of a pre-solve boolean,
/// so the coupled system (params own <= fields own <= stores supported <= params
/// own) has the fixpoint the rest of the system already gets. Default off and
/// carried by `solver_identity`.
pub(crate) fn interface_own() -> bool {
    static ONCE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ONCE.get_or_init(|| match std::env::var("CRAT_ERA5B_INTERFACE_OWN") {
        Err(std::env::VarError::NotPresent) => false,
        Ok(value) => match value.as_str() {
            "on" => true,
            "off" => false,
            other => panic!("CRAT_ERA5B_INTERFACE_OWN must be on or off; got {other:?}"),
        },
        Err(error) => panic!("CRAT_ERA5B_INTERFACE_OWN is not valid Unicode: {error}"),
    })
}

/// R377-1: the return-port rule. A fresh allocation whose only escape from its
/// frame is that frame's return is `Owning` at the return port. Default off and
/// carried by `solver_identity` (R374-1's standing rule), so the two arms cannot
/// share a cache key.
pub(crate) fn return_port() -> bool {
    static ONCE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ONCE.get_or_init(|| match std::env::var("CRAT_ERA5B_RETURN_PORT") {
        Err(std::env::VarError::NotPresent) => false,
        Ok(value) => match value.as_str() {
            "on" => true,
            "off" => false,
            other => panic!("CRAT_ERA5B_RETURN_PORT must be on or off; got {other:?}"),
        },
        Err(error) => panic!("CRAT_ERA5B_RETURN_PORT is not valid Unicode: {error}"),
    })
}

/// R372-3 probe (3): relax the folding frame's `argument_count` and
/// `return_width` while keeping `phis.is_empty()`. The cell plan's walk consults
/// neither — they are gate conditions — so this measures whether a frame that
/// takes arguments and returns a value, but never joins, can carry the cell
/// story as written. An environment arm, so the default path is unchanged.
pub(crate) fn relax_frame() -> bool {
    static ONCE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ONCE.get_or_init(|| match std::env::var("CRAT_ERA5B_RELAX_FRAME") {
        Err(std::env::VarError::NotPresent) => false,
        Ok(value) => match value.as_str() {
            "on" => true,
            "off" => false,
            other => panic!("CRAT_ERA5B_RELAX_FRAME must be on or off; got {other:?}"),
        },
        Err(error) => panic!("CRAT_ERA5B_RELAX_FRAME is not valid Unicode: {error}"),
    })
}

/// R353-2: the pass is read once. It is process-wide by construction — an
/// environment pin — and the inference walk asks per statement, which is not a
/// place to re-read the environment.
/// R467-2 diagnosis: omit era-5b's per-constant SOURCE registration so its
/// cost can be measured. Verdicts are NOT valid with it on.
/// R467-2 diagnosis pins: omit era-5b's joint-gated EMISSION sites in the solver,
/// split so the guarded-reader family can be separated from the rest.
/// Verdicts are NOT valid with either on.
fn skip_family(name: &str) -> bool {
    std::env::var("CRAT_ERA5C_SKIP_FAMILY")
        .unwrap_or_default()
        .split(',')
        .any(|s| {
            let s = s.trim();
            s == name || s == "joint_emission"
        })
}

pub(crate) fn skip_joint_readers() -> bool {
    static ONCE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ONCE.get_or_init(|| skip_family("joint_readers"))
}

pub(crate) fn skip_joint_other() -> bool {
    static ONCE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ONCE.get_or_init(|| skip_family("joint_other"))
}

pub(crate) fn skip_constant_sources() -> bool {
    static ONCE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ONCE.get_or_init(|| {
        std::env::var("CRAT_ERA5C_SKIP_FAMILY")
            .unwrap_or_default()
            .split(',')
            .any(|s| s.trim() == "constant_sources")
    })
}

pub(crate) fn joint() -> bool {
    static ONCE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ONCE.get_or_init(|| Pass::current() == Pass::Joint)
}

impl Pass {
    /// Fail-loud on a set-but-invalid value, as `ForkEngineMode` does: a typo
    /// must not silently produce the joint solve under a pass-1 label.
    pub(crate) fn current() -> Self {
        match std::env::var("CRAT_ERA5B_PASS") {
            Err(std::env::VarError::NotPresent) => Self::Joint,
            Ok(value) => match value.as_str() {
                "joint" => Self::Joint,
                "era5a" => Self::EraFiveA,
                other => panic!("CRAT_ERA5B_PASS must be joint or era5a; got {other:?}"),
            },
            Err(error) => panic!("CRAT_ERA5B_PASS is not valid Unicode: {error}"),
        }
    }
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
pub(crate) fn freeze(builder: Builder, ownership_asts: IndexVec<Var, Bool>) -> Rc<Facts> {
    let mut facts = Rc::try_unwrap(builder)
        .unwrap_or_else(|_| panic!("licensing facts still have an active builder alias"))
        .into_inner();
    facts.ownership_asts = ownership_asts;
    facts.licensing = Some(Rc::new(super::snapshot::FrozenTransport::build(&facts)));
    Rc::new(facts)
}
