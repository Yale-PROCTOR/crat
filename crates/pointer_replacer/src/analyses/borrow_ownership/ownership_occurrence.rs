//! Exact observations at the ownership consumer and transfer sites.
//! Recorded paths never stand in for alias, retention, or conservation proofs.

use std::{cell::RefCell, ops::Range};

use rustc_middle::{
    mir::{Body, Place},
    ty::{Ty, TyCtxt, TyKind},
};

use super::{
    export::{PlaceKey, ProjKey},
    licensing::facts,
    ownership_evidence::Point,
    ptr::Measurable,
    ssa::{constraint::Var, consume::Consume, state::SSAIdx},
};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
#[serde(tag = "state", content = "value", rename_all = "kebab-case")]
pub(crate) enum Availability<T> {
    Present(T),
    Missing(String),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub(crate) enum PathStep {
    Deref,
    Field {
        structure: String,
        index: u32,
        name: String,
    },
    /// The ownership abstraction folds array elements; this is not an exact cell.
    ArrayElement,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub(crate) struct SourceSpan {
    pub(crate) file: String,
    pub(crate) lo: u32,
    pub(crate) hi: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub(crate) struct Window {
    pub(crate) use_start: u32,
    pub(crate) use_end: u32,
    pub(crate) def_start: u32,
    pub(crate) def_end: u32,
}

impl From<&Consume<Range<Var>>> for Window {
    fn from(value: &Consume<Range<Var>>) -> Self {
        Self {
            use_start: value.r#use.start.as_u32(),
            use_end: value.r#use.end.as_u32(),
            def_start: value.def.start.as_u32(),
            def_end: value.def.end.as_u32(),
        }
    }
}

impl Window {
    fn valid(&self) -> bool {
        self.use_start <= self.use_end
            && self.def_start <= self.def_end
            && self.use_end - self.use_start == self.def_end - self.def_start
    }

    fn contains(&self, other: &Window) -> bool {
        self.valid()
            && other.valid()
            && self.use_start <= other.use_start
            && other.use_end <= self.use_end
            && self.def_start <= other.def_start
            && other.def_end <= self.def_end
            && other.use_start - self.use_start == other.def_start - self.def_start
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub(crate) struct Consumption {
    pub(crate) point: Point,
    pub(crate) ordinal: usize,
    pub(crate) span: SourceSpan,
    pub(crate) local: u32,
    pub(crate) projection: Vec<ProjKey>,
    pub(crate) ssa_use: Option<u32>,
    pub(crate) ssa_def: Option<u32>,
    pub(crate) base: Availability<Window>,
    pub(crate) projected: Availability<Window>,
    pub(crate) pointer_paths: Availability<Vec<Vec<PathStep>>>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub(crate) struct Binding {
    pub(crate) consume: usize,
    pub(crate) local: u32,
    pub(crate) projection: Vec<ProjKey>,
    pub(crate) ssa_use: Option<u32>,
    pub(crate) ssa_def: Option<u32>,
    pub(crate) path: Vec<PathStep>,
    pub(crate) pointer_depth: usize,
    pub(crate) use_var: u32,
    pub(crate) def_var: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub(crate) struct Transfer {
    pub(crate) destination: Availability<Binding>,
    pub(crate) source: Availability<Binding>,
    pub(crate) destination_use: u32,
    pub(crate) destination_def: u32,
    pub(crate) source_use: u32,
    pub(crate) source_def: u32,
    pub(crate) by_move: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub(crate) struct TerminalValue {
    pub(crate) var: u32,
    pub(crate) path: Availability<Vec<PathStep>>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize, serde::Deserialize)]
pub(crate) struct Terminal {
    pub(crate) point: Point,
    pub(crate) ordinal: usize,
    pub(crate) local: u32,
    pub(crate) ssa: Option<u32>,
    pub(crate) role: String,
    pub(crate) values: Availability<Vec<TerminalValue>>,
}

fn paths<'tcx>(
    ty: Ty<'tcx>,
    tcx: TyCtxt<'tcx>,
    remaining: u8,
    path: &mut Vec<PathStep>,
    out: &mut Vec<Vec<PathStep>>,
) {
    if remaining == 0 {
        return;
    }
    if let Some(element) = ty.builtin_index() {
        path.push(PathStep::ArrayElement);
        paths(element, tcx, remaining, path, out);
        path.pop();
    } else if let Some(pointee) = ty.builtin_deref(true) {
        out.push(path.clone());
        path.push(PathStep::Deref);
        paths(pointee, tcx, remaining - 1, path, out);
        path.pop();
    } else if let TyKind::Adt(adt, args) = ty.kind() {
        if !adt.is_struct() {
            return;
        }
        for (index, field) in adt.non_enum_variant().fields.iter_enumerated() {
            path.push(PathStep::Field {
                structure: tcx.def_path_str(adt.did()),
                index: index.as_u32(),
                name: field.name.to_string(),
            });
            paths(field.ty(tcx, args), tcx, remaining, path, out);
            path.pop();
        }
    }
}

pub(crate) fn record_consume<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    place: Place<'tcx>,
    ssa: Option<&Consume<SSAIdx>>,
    base: Option<&Consume<Range<Var>>>,
    projected: Option<&Consume<Range<Var>>>,
    measurable: &impl Measurable<'tcx>,
    missing: &str,
) {
    let Some(point) = super::ownership_evidence::point() else {
        return;
    };
    let key = PlaceKey::from_place(place);
    let span = point
        .block
        .and_then(|b| {
            let data = body
                .basic_blocks
                .get(rustc_middle::mir::BasicBlock::from_u32(b))?;
            let s = point.statement?;
            data.statements
                .get(s)
                .map(|s| s.source_info.span)
                .or_else(|| {
                    (s == data.statements.len())
                        .then(|| data.terminator.as_ref().map(|t| t.source_info.span))
                        .flatten()
                })
        })
        .unwrap_or(body.span);
    let pointer_paths = if let Some(base) = base {
        let mut result = Vec::new();
        paths(
            body.local_decls[place.local].ty,
            tcx,
            measurable.absolute_precision(
                body.local_decls[place.local].ty,
                base.r#use.end.as_u32() - base.r#use.start.as_u32(),
            ),
            &mut Vec::new(),
            &mut result,
        );
        if result.len() == (base.r#use.end.as_u32() - base.r#use.start.as_u32()) as usize {
            Availability::Present(result)
        } else {
            Availability::Missing("type-path/ownership-window width mismatch".into())
        }
    } else {
        Availability::Missing(missing.into())
    };
    let _ = facts::record(|facts| {
        let rows = &mut facts.consumes;
        rows.push(Consumption {
            point,
            ordinal: rows.len(),
            span: SourceSpan {
                file: tcx
                    .sess
                    .source_map()
                    .span_to_filename(span)
                    .prefer_local()
                    .to_string(),
                lo: span.lo().0,
                hi: span.hi().0,
            },
            local: key.local.as_u32(),
            projection: key.proj,
            ssa_use: ssa.map(|c| c.r#use.as_u32()),
            ssa_def: ssa.map(|c| c.def.as_u32()),
            base: base
                .map(|b| Availability::Present(b.into()))
                .unwrap_or_else(|| Availability::Missing(missing.into())),
            projected: projected
                .map(|b| Availability::Present(b.into()))
                .unwrap_or_else(|| Availability::Missing(missing.into())),
            pointer_paths,
        });
    });
}

pub(crate) fn record_terminal<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    local: rustc_middle::mir::Local,
    ssa: Option<SSAIdx>,
    vars: Option<&Range<Var>>,
    measurable: &impl Measurable<'tcx>,
) {
    let Some(point) = super::ownership_evidence::point() else {
        return;
    };
    let values = vars
        .map(|vars| {
            let width = vars.end.as_u32() - vars.start.as_u32();
            let mut pointer_paths = Vec::new();
            paths(
                body.local_decls[local].ty,
                tcx,
                measurable.absolute_precision(body.local_decls[local].ty, width),
                &mut Vec::new(),
                &mut pointer_paths,
            );
            Availability::Present(
                vars.clone()
                    .enumerate()
                    .map(|(index, var)| TerminalValue {
                        var: var.as_u32(),
                        path: if pointer_paths.len() == width as usize {
                            Availability::Present(pointer_paths[index].clone())
                        } else {
                            Availability::Missing(
                                "terminal type-path/ownership-window width mismatch".into(),
                            )
                        },
                    })
                    .collect(),
            )
        })
        .unwrap_or_else(|| Availability::Missing("no terminal SSA range".into()));
    let _ = facts::record(|facts| {
        let rows = &mut facts.terminals;
        rows.push(Terminal {
            point,
            ordinal: rows.len(),
            local: local.as_u32(),
            ssa: ssa.map(|ssa| ssa.as_u32()),
            role: if local.as_usize() == 0 {
                "return-output"
            } else if local.as_usize() <= body.arg_count {
                "parameter-output"
            } else {
                "local-final-zero"
            }
            .into(),
            values,
        });
    });
}

/// Resolve one complete observed consume window at the exact recording point.
/// Repeated or unavailable windows remain Missing; no prior-site search occurs.
pub(crate) fn consume_at(point: &Point, window: &Window) -> Availability<usize> {
    let mut matches = Vec::new();
    let mut narrowed = Vec::new();
    let _ = facts::read(|facts| {
        for row in &facts.consumes {
            if &row.point != point {
                continue;
            }
            let Availability::Present(projected) = &row.projected else {
                continue;
            };
            if projected == window {
                matches.push(row.ordinal);
            } else if narrows(window, projected) {
                narrowed.push(row.ordinal);
            }
        }
    });
    if matches.len() == 1 {
        return Availability::Present(matches[0]);
    }
    // R357-2: a native pointer cast transfers the root only, and the
    // certificate's own component loop already says so (`width.min(1)`). The
    // registration's window is then the leading components of the source's,
    // sharing both starts — not a different window. One such source resolves;
    // several stay Missing, and no prior site is searched either way.
    if matches.is_empty() && narrowed.len() == 1 {
        return Availability::Present(narrowed[0]);
    }
    Availability::Missing(format!(
        "exact current-site consume-window matches: {}, leading-window matches: {}",
        matches.len(),
        narrowed.len()
    ))
}

/// Whether `window` is a non-empty leading run of `projected`: the same use and
/// def starts, no wider on either side, and the same width on both.
pub(crate) fn narrows(window: &Window, projected: &Window) -> bool {
    let uses = window.use_end.checked_sub(window.use_start);
    let defs = window.def_end.checked_sub(window.def_start);
    window.use_start == projected.use_start
        && window.def_start == projected.def_start
        && window.use_end <= projected.use_end
        && window.def_end <= projected.def_end
        && uses == defs
        && uses.is_some_and(|width| width > 0)
        && (window.use_end, window.def_end) != (projected.use_end, projected.def_end)
}

/// Record a field view of an already consumed aggregate. This only narrows
/// recorded ranges; it does not consume a place, allocate Vars, or emit frames.
pub(crate) fn record_field_view(
    aggregate: Place<'_>,
    field: Place<'_>,
    aggregate_window: &Consume<Range<Var>>,
    field_window: &Consume<Range<Var>>,
) -> Availability<usize> {
    let Some(point) = super::ownership_evidence::point() else {
        return Availability::Missing("aggregate ownership point unavailable".into());
    };
    let aggregate = PlaceKey::from_place(aggregate);
    let field = PlaceKey::from_place(field);
    let aggregate_window = Window::from(aggregate_window);
    let field_window = Window::from(field_window);
    if aggregate.local != field.local
        || field.proj.len() != aggregate.proj.len() + 1
        || !field.proj.starts_with(&aggregate.proj)
        || !matches!(field.proj.last(), Some(ProjKey::Field(_)))
        || !aggregate_window.contains(&field_window)
    {
        return Availability::Missing("aggregate field view is not an exact subwindow".into());
    }
    facts::record(|facts| {
        let parents: Vec<_> = facts
            .consumes
            .iter()
            .filter(|row| {
                row.point == point
                    && row.local == aggregate.local.as_u32()
                    && row.projection == aggregate.proj
                    && row.projected == Availability::Present(aggregate_window.clone())
            })
            .collect();
        if parents.len() != 1 {
            return Availability::Missing(format!(
                "exact aggregate consume matches: {}",
                parents.len()
            ));
        }
        let mut row = parents[0].clone();
        row.ordinal = facts.consumes.len();
        row.projection = field.proj;
        row.projected = Availability::Present(field_window);
        let id = row.ordinal;
        facts.consumes.push(row);
        Availability::Present(id)
    })
    .unwrap_or_else(|| Availability::Missing("aggregate facts builder unavailable".into()))
}

fn binding(
    point: &Point,
    use_var: Var,
    def_var: Var,
    selected: Option<usize>,
) -> Availability<Binding> {
    let mut matches = Vec::new();
    let _ = facts::read(|facts| {
        for row in facts
            .consumes
            .iter()
            .filter(|row| &row.point == point && selected.is_none_or(|id| row.ordinal == id))
        {
            let (
                Availability::Present(base),
                Availability::Present(projected),
                Availability::Present(paths),
            ) = (&row.base, &row.projected, &row.pointer_paths)
            else {
                continue;
            };
            let u = use_var.as_u32();
            let d = def_var.as_u32();
            if u < projected.use_start
                || u >= projected.use_end
                || d < projected.def_start
                || d >= projected.def_end
                || u - base.use_start != d - base.def_start
            {
                continue;
            }
            let Some(path) = paths.get((u - base.use_start) as usize) else {
                continue;
            };
            matches.push(Binding {
                consume: row.ordinal,
                local: row.local,
                projection: row.projection.clone(),
                ssa_use: row.ssa_use,
                ssa_def: row.ssa_def,
                path: path.clone(),
                pointer_depth: path.iter().filter(|p| matches!(p, PathStep::Deref)).count(),
                use_var: u,
                def_var: d,
            });
        }
    });
    if matches.len() == 1 {
        Availability::Present(matches.remove(0))
    } else {
        Availability::Missing(format!(
            "exact current-site consume matches: {}",
            matches.len()
        ))
    }
}

thread_local! {
    static TRANSFER: RefCell<Option<Transfer>> = const { RefCell::new(None) };
    static DESTINATION_HINT: RefCell<Option<Availability<usize>>> = const { RefCell::new(None) };
}

pub(crate) struct DestinationHint(Option<Availability<usize>>);
impl Drop for DestinationHint {
    fn drop(&mut self) {
        DESTINATION_HINT.with(|hint| *hint.borrow_mut() = self.0.take());
    }
}

/// Select the exact synthetic field row instead of ambiguously matching both
/// that row and its aggregate parent. Missing remains Missing.
pub(crate) fn destination_hint(selected: Availability<usize>) -> DestinationHint {
    DestinationHint(DESTINATION_HINT.with(|hint| hint.replace(Some(selected))))
}
pub(crate) struct Scope(Option<Transfer>);
impl Drop for Scope {
    fn drop(&mut self) {
        TRANSFER.with(|t| *t.borrow_mut() = self.0.take());
    }
}
pub(crate) fn reset() -> Scope {
    Scope(TRANSFER.with(|t| t.replace(None)))
}
pub(crate) fn transfer(lhs: &Consume<Var>, rhs: &Consume<Var>, by_move: bool) -> Scope {
    let value = super::ownership_evidence::point().map(|point| Transfer {
        destination: match DESTINATION_HINT.with(|hint| hint.borrow().clone()) {
            Some(Availability::Present(id)) => binding(&point, lhs.r#use, lhs.def, Some(id)),
            Some(Availability::Missing(reason)) => Availability::Missing(reason),
            None => binding(&point, lhs.r#use, lhs.def, None),
        },
        source: binding(&point, rhs.r#use, rhs.def, None),
        destination_use: lhs.r#use.as_u32(),
        destination_def: lhs.def.as_u32(),
        source_use: rhs.r#use.as_u32(),
        source_def: rhs.def.as_u32(),
        by_move,
    });
    Scope(TRANSFER.with(|t| t.replace(value)))
}
pub(crate) fn current_transfer() -> Option<Transfer> {
    TRANSFER.with(|t| t.borrow().clone())
}

/// Validate only the recorded correspondence. Missing remains missing evidence.
pub(crate) fn validate(
    function: &str,
    rows: &[Consumption],
    equations: &[super::ownership_evidence::Equation],
) -> Result<(), String> {
    use Availability::{Missing, Present};
    let mut by_id = std::collections::BTreeMap::new();
    for row in rows {
        if row.point.function.as_deref() != Some(function)
            || row.point.block.is_none()
            || row.point.statement.is_none()
            || !matches!(row.point.phase.as_str(), "statement" | "terminator")
            || row.span.file.is_empty()
            || row.span.lo > row.span.hi
            || by_id
                .insert((row.point.construction, row.ordinal), row)
                .is_some()
        {
            return Err("invalid or duplicate consume occurrence".into());
        }
        match (&row.base, &row.projected, &row.pointer_paths) {
            (Present(base), projected, paths) => {
                if !base.valid()
                    || matches!(projected,Present(p) if !base.contains(p))
                    || matches!(paths,Present(paths) if paths.len()!=(base.use_end-base.use_start) as usize)
                {
                    return Err("invalid consume window/path correspondence".into());
                }
            }
            (Missing(_), Missing(_), Missing(_)) => {}
            _ => return Err("consume availability has unsupported positive evidence".into()),
        }
    }
    for equation in equations {
        let Some(transfer) = &equation.transfer else {
            if equation.assumption_class.as_deref() == Some("ssa-transfer") {
                return Err("transfer assumption has no matched transfer record".into());
            }
            continue;
        };
        for (binding, u, d) in [
            (
                &transfer.destination,
                transfer.destination_use,
                transfer.destination_def,
            ),
            (&transfer.source, transfer.source_use, transfer.source_def),
        ] {
            let Present(binding) = binding else {
                continue;
            };
            let row = by_id
                .get(&(equation.point.construction, binding.consume))
                .ok_or("missing transfer consume")?;
            let (Present(base), Present(projected), Present(paths)) =
                (&row.base, &row.projected, &row.pointer_paths)
            else {
                return Err("positive transfer uses missing consume".into());
            };
            if row.point != equation.point
                || row.local != binding.local
                || row.projection != binding.projection
                || row.ssa_use != binding.ssa_use
                || row.ssa_def != binding.ssa_def
                || u != binding.use_var
                || d != binding.def_var
                || u < projected.use_start
                || u >= projected.use_end
                || d < projected.def_start
                || d >= projected.def_end
                || u - base.use_start != d - base.def_start
                || paths.get((u - base.use_start) as usize) != Some(&binding.path)
                || binding.pointer_depth
                    != binding
                        .path
                        .iter()
                        .filter(|s| matches!(s, PathStep::Deref))
                        .count()
            {
                return Err("invalid transfer binding correspondence".into());
            }
        }
        let expected = match equation.operation.as_str() {
            "assume" => {
                equation.assumption_class.as_deref() == Some("ssa-transfer")
                    && equation.value == Some(false)
                    && (equation.variables == [transfer.destination_use]
                        || (transfer.by_move && equation.variables == [transfer.source_def]))
            }
            "equal" => {
                transfer.by_move
                    && equation.variables == [transfer.destination_def, transfer.source_use]
            }
            "linear" => {
                !transfer.by_move
                    && equation.variables
                        == [
                            transfer.destination_def,
                            transfer.source_def,
                            transfer.source_use,
                        ]
            }
            "guarded-copy"
            | "guarded-move"
            | "guarded-reader-copy"
            | "guarded-reader-move"
            | "guarded-reference-field"
            | "guarded-original-cell-frame" => {
                equation.variables
                    == [
                        transfer.destination_def,
                        transfer.source_def,
                        transfer.source_use,
                    ]
            }
            _ => false,
        };
        if !expected {
            return Err("transfer/equation operation mismatch".into());
        }
    }
    Ok(())
}

/// Shape checks on recorded terminals, without claiming an all-locals/returns
/// roster or final-zero equation coverage. Those are separate validation gates.
pub(crate) fn validate_terminal_shapes(
    function: &str,
    terminals: &[Terminal],
) -> Result<(), String> {
    let mut ids = std::collections::BTreeSet::new();
    for row in terminals {
        let role_ok = match row.role.as_str() {
            "return-output" => row.local == 0,
            "parameter-output" | "local-final-zero" => row.local != 0,
            _ => false,
        };
        if row.point.function.as_deref() != Some(function)
            || row.point.phase != "return"
            || row.point.block.is_none()
            || row.point.statement.is_none()
            || !role_ok
            || !ids.insert((row.point.construction, row.ordinal))
            || matches!(&row.values, Availability::Missing(reason) if reason.is_empty())
        {
            return Err("invalid or duplicate terminal shape".into());
        }
    }
    Ok(())
}

/// Cross-check represented final values, without asserting that unreferenced
/// missing terminals exhaust all locals or all return sites in the source.
pub(crate) fn validate_terminal_links(
    terminals: &[Terminal],
    boundaries: &[super::ownership_boundary::Substitution],
    equations: &[super::ownership_evidence::Equation],
) -> Result<(), String> {
    use Availability::{Missing, Present};

    use super::ownership_boundary::{Role, Window as BoundaryWindow};
    let mut terminal_keys = std::collections::BTreeMap::new();
    let mut zeros = std::collections::BTreeMap::<Point, std::collections::BTreeSet<u32>>::new();
    for equation in equations {
        if equation.assumption_class.as_deref() == Some("temporary-finalization") {
            if equation.operation != "assume"
                || equation.value != Some(false)
                || equation.variables.len() != 1
            {
                return Err("temporary finalization is not a recorded zero assumption".into());
            }
            zeros
                .entry(equation.point.clone())
                .or_default()
                .insert(equation.variables[0]);
        }
    }
    let mut witnessed = std::collections::BTreeMap::<Point, std::collections::BTreeSet<u32>>::new();
    for terminal in terminals {
        if terminal_keys
            .insert((terminal.point.clone(), terminal.local), terminal)
            .is_some()
        {
            return Err("multiple terminals for one local at one return point".into());
        }
        if terminal.role == "local-final-zero" {
            if let Present(values) = &terminal.values {
                let mut seen = std::collections::BTreeSet::new();
                for value in values {
                    if !seen.insert(value.var)
                        || !zeros
                            .get(&terminal.point)
                            .is_some_and(|vars| vars.contains(&value.var))
                    {
                        return Err(
                            "terminal final value has no corresponding zero assumption".into()
                        );
                    }
                    witnessed
                        .entry(terminal.point.clone())
                        .or_default()
                        .insert(value.var);
                }
            }
        }
    }
    if zeros != witnessed {
        return Err("temporary-finalization equations lack terminal witnesses".into());
    }
    let mut exits = std::collections::BTreeSet::new();
    for boundary in boundaries {
        let (local, role) = match boundary.role {
            Role::ExitReturn => (0, "return-output"),
            Role::ExitOutput => {
                let local = boundary
                    .argument_index
                    .and_then(|index| index.checked_add(1))
                    .and_then(|index| u32::try_from(index).ok())
                    .ok_or("invalid exit argument index")?;
                (local, "parameter-output")
            }
            _ => continue,
        };
        let key = (boundary.point.clone(), local);
        if !exits.insert(key.clone()) {
            return Err("duplicate exit substitution for one terminal".into());
        }
        let terminal = terminal_keys
            .get(&key)
            .ok_or("exit substitution has no terminal")?;
        if terminal.role != role {
            return Err("exit substitution/terminal role mismatch".into());
        }
        match (&terminal.values, &boundary.actual) {
            (Missing(_), Missing(_)) => {}
            (Present(values), Present(BoundaryWindow::Single { start, end })) => {
                if start > end
                    || values.len() as u64 != u64::from(end - start)
                    || !values.iter().map(|value| value.var).eq(*start..*end)
                {
                    return Err("exit actual range disagrees with terminal values".into());
                }
            }
            _ => return Err("exit actual/terminal availability mismatch".into()),
        }
    }
    for (key, terminal) in terminal_keys {
        if matches!(terminal.role.as_str(), "return-output" | "parameter-output")
            && !exits.contains(&key)
        {
            return Err("output terminal has no exit substitution".into());
        }
    }
    Ok(())
}
