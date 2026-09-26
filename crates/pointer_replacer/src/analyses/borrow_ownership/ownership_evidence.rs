//! Recorded ownership equations, distinct from a conservation proof.

use std::cell::RefCell;

use super::{
    export,
    licensing::facts::{self, EquationId, GuardBinding},
    ssa::constraint::Var,
};

/// A source/sink key copied at the assertion site, never reconstructed from a Var.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub(crate) struct Endpoint {
    pub(crate) function: String,
    pub(crate) block: u32,
    pub(crate) statement: usize,
    pub(crate) callee: String,
    pub(crate) role: export::BoundaryRole,
    pub(crate) outcome: Option<super::realloc::ReallocOutcome>,
    /// Ordinary libc endpoints do not yet carry operand correspondence.
    /// None means unavailable, not an unprojected local.
    pub(crate) operand: Option<(u32, Vec<export::ProjKey>)>,
}

impl From<&export::T2AssertKey> for Endpoint {
    fn from(key: &export::T2AssertKey) -> Self {
        Self {
            function: key.function_path.clone(),
            block: key.location.block,
            statement: key.location.statement_index,
            callee: key.callee.clone(),
            role: key.role,
            outcome: key.realloc_outcome,
            operand: key
                .endpoint
                .as_ref()
                .map(|p| (p.local.as_u32(), p.proj.clone())),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub(crate) struct Point {
    pub(crate) construction: u32,
    pub(crate) function: Option<String>,
    pub(crate) phase: String,
    pub(crate) block: Option<u32>,
    pub(crate) statement: Option<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub(crate) struct Equation {
    pub(crate) point: Point,
    pub(crate) ordinal: usize,
    pub(crate) operation: String,
    pub(crate) variables: Vec<u32>,
    pub(crate) value: Option<bool>,
    pub(crate) assumption_class: Option<String>,
    /// Diagnostic predicate only; no stable lend identity is inferred from it.
    pub(crate) guard: Option<String>,
    pub(crate) endpoint: Option<Endpoint>,
    pub(crate) transfer: Option<super::ownership_occurrence::Transfer>,
}

impl Equation {
    pub(crate) fn validate(&self) -> Result<(), &'static str> {
        let arity = match self.operation.as_str() {
            "guarded-original-cell-declared" | "guarded-traversal-call" | "guarded-fold-call" => 0,
            "guarded-original-cell-argument"
            | "guarded-original-cell-legacy"
            | "guarded-traversal-argument-legacy" => 4,
            "assume"
            | "source"
            | "sink"
            | "guarded-traversal-view-zero"
            | "guarded-traversal-formal-zero" => 1,
            "equal"
            | "less-equal"
            | "null-join"
            | "guarded-contract-port"
            | "guarded-lend-source"
            | "guarded-reader-source-tail"
            | "guarded-reader-view-tail"
            | "guarded-reference-scalar-read"
            | "guarded-reference-output"
            | "guarded-reference-outer"
            | "guarded-reference-view-zero"
            | "guarded-original-cell-outer"
            | "guarded-traversal-receiver-legacy"
            | "guarded-traversal-frame" => 2,
            "linear"
            | "eq-min"
            | "guarded-copy"
            | "guarded-move"
            | "guarded-reader-copy"
            | "guarded-reader-move"
            | "guarded-reference-field"
            | "guarded-original-cell-frame" => 3,
            _ => return Err("unknown ownership equation"),
        };
        if self.variables.len() != arity {
            return Err("invalid ownership equation shape");
        }
        let assume = self.operation == "assume";
        if assume != self.value.is_some()
            || assume != self.assumption_class.is_some()
            || self.assumption_class.as_ref().is_some_and(String::is_empty)
        {
            return Err("ownership assumption value mismatch");
        }
        if self.operation.starts_with("guarded-") != self.guard.is_some()
            || self.guard.as_ref().is_some_and(String::is_empty)
        {
            return Err("ownership guard mismatch");
        }
        let valid_point = match self.point.phase.as_str() {
            "global" => {
                self.point.function.is_none()
                    && self.point.block.is_none()
                    && self.point.statement.is_none()
            }
            "function" => {
                self.point.function.is_some()
                    && self.point.block.is_none()
                    && self.point.statement.is_none()
            }
            "phi" | "realloc-edge" => {
                self.point.function.is_some()
                    && self.point.block.is_some()
                    && self.point.statement.is_none()
            }
            "statement" | "terminator" | "return" => {
                self.point.function.is_some()
                    && self.point.block.is_some()
                    && self.point.statement.is_some()
            }
            _ => false,
        };
        if !valid_point || self.point.function.as_ref().is_some_and(String::is_empty) {
            return Err("invalid ownership emission point");
        }
        if matches!(self.operation.as_str(), "source" | "sink") != self.endpoint.is_some() {
            return Err("ownership endpoint key mismatch");
        }
        if let Some(endpoint) = &self.endpoint {
            let role = match endpoint.role {
                export::BoundaryRole::Source => "source",
                export::BoundaryRole::Sink => "sink",
            };
            if role != self.operation
                || self.point.function.as_ref() != Some(&endpoint.function)
                || endpoint.callee.is_empty()
                || (endpoint.outcome.is_some() && endpoint.operand.is_none())
            {
                return Err("invalid ownership endpoint correspondence");
            }
            // Realloc's old claim and R219 continuations emit at the call;
            // a direct-branch fresh result emits on the success successor.
            let placed = (self.point.phase == "terminator"
                && self.point.block == Some(endpoint.block)
                && self.point.statement == Some(endpoint.statement))
                || (endpoint.outcome.is_some() && self.point.phase == "realloc-edge");
            if !placed {
                return Err("ownership endpoint emission site mismatch");
            }
        }
        Ok(())
    }
}

pub(crate) fn validate_function(
    equations: &[Equation],
    function: &str,
) -> Result<(), &'static str> {
    let mut seen = std::collections::BTreeSet::new();
    for equation in equations {
        equation.validate()?;
        if equation
            .point
            .function
            .as_deref()
            .is_some_and(|name| name != function)
            || !seen.insert((equation.point.construction, equation.ordinal))
        {
            return Err("duplicate or foreign ownership equation");
        }
    }
    Ok(())
}

thread_local! {
    static POINT: RefCell<Option<Point>> = const { RefCell::new(None) };
}

pub(crate) fn point() -> Option<Point> {
    POINT.with(|point| point.borrow().clone())
}

pub(crate) struct Scope {
    previous: Option<Point>,
    active: bool,
}

impl Drop for Scope {
    fn drop(&mut self) {
        if self.active {
            POINT.with(|p| *p.borrow_mut() = self.previous.take());
        }
    }
}

fn enter(point: Option<Point>) -> Scope {
    if !facts::active() {
        return Scope {
            previous: None,
            active: false,
        };
    }
    Scope {
        previous: POINT.with(|p| p.replace(point)),
        active: true,
    }
}

pub(crate) fn construction() -> Scope {
    let id = facts::record(|output| {
        let id = output.constructions;
        output.constructions += 1;
        id
    });
    enter(id.map(|construction| Point {
        construction,
        function: None,
        phase: "global".into(),
        block: None,
        statement: None,
    }))
}

pub(crate) fn function(name: impl FnOnce() -> String) -> Scope {
    let mut point = POINT.with(|p| p.borrow().clone());
    if let Some(point) = &mut point {
        point.function = Some(name());
        point.phase = "function".into();
        point.block = None;
        point.statement = None;
    }
    enter(point)
}

pub(crate) fn location(phase: &str, block: u32, statement: Option<usize>) -> Scope {
    let mut point = POINT.with(|p| p.borrow().clone());
    if let Some(point) = &mut point {
        point.phase = phase.into();
        point.block = Some(block);
        point.statement = statement;
    }
    enter(point)
}

pub(crate) fn record(
    operation: &str,
    variables: &[Var],
    value: Option<bool>,
    guard: Option<&z3::ast::Bool>,
) {
    let _ = record_key(operation, variables, value, guard);
}

pub(crate) fn record_key(
    operation: &str,
    variables: &[Var],
    value: Option<bool>,
    guard: Option<&z3::ast::Bool>,
) -> Option<EquationId> {
    record_equation(operation, variables, value, guard, None, guard)
}

pub(crate) fn record_endpoint(key: &export::T2AssertKey, selector: &z3::ast::Bool) {
    let operation = match key.role {
        export::BoundaryRole::Source => "source",
        export::BoundaryRole::Sink => "sink",
    };
    record_equation(
        operation,
        &[key.var],
        None,
        None,
        Some(Endpoint::from(key)),
        Some(selector),
    );
}

fn record_equation(
    operation: &str,
    variables: &[Var],
    value: Option<bool>,
    guard: Option<&z3::ast::Bool>,
    endpoint: Option<Endpoint>,
    dependency: Option<&z3::ast::Bool>,
) -> Option<EquationId> {
    let point = POINT.with(|p| p.borrow().clone())?;
    facts::record(|output| {
        let equation = Equation {
            point,
            ordinal: output.equations.len(),
            operation: operation.into(),
            variables: variables.iter().map(|v| v.as_u32()).collect(),
            value,
            assumption_class: value
                .map(|_| super::solver::current_own_assume_site().as_str().to_owned()),
            guard: guard.map(ToString::to_string),
            endpoint,
            transfer: super::ownership_occurrence::current_transfer(),
        };
        equation.validate().expect("emitted ownership equation");
        if let Some(predicate) = dependency {
            output.guards.push(GuardBinding {
                equation: EquationId {
                    construction: equation.point.construction,
                    ordinal: equation.ordinal,
                },
                predicate: predicate.clone(),
            });
        }
        let key = EquationId {
            construction: equation.point.construction,
            ordinal: equation.ordinal,
        };
        output.equations.push(equation);
        key
    })
}
