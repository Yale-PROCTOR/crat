//! Observed boundary matcher substitutions, without changing ownership laws.

use std::{cell::RefCell, collections::BTreeSet, ops::Range};

use super::{
    licensing::facts,
    ownership_evidence::{self, Point},
    ownership_occurrence::{self, Availability},
    ssa::{constraint::Var, consume::Consume},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum Role {
    Entry,
    ReturnReceiver,
    CallArgument,
    ExitReturn,
    ExitOutput,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub(crate) enum Window {
    Single {
        start: u32,
        end: u32,
    },
    UseDef {
        use_start: u32,
        use_end: u32,
        def_start: u32,
        def_end: u32,
    },
}

impl Window {
    pub(crate) fn single(value: &Range<Var>) -> Self {
        Self::Single {
            start: value.start.as_u32(),
            end: value.end.as_u32(),
        }
    }

    pub(crate) fn consume(value: &Consume<Range<Var>>) -> Self {
        Self::UseDef {
            use_start: value.r#use.start.as_u32(),
            use_end: value.r#use.end.as_u32(),
            def_start: value.def.start.as_u32(),
            def_end: value.def.end.as_u32(),
        }
    }

    fn variables(&self) -> Vec<u32> {
        match *self {
            Self::Single { start, end } => (start..end).collect(),
            Self::UseDef {
                use_start,
                use_end,
                def_start,
                def_end,
            } => (use_start..use_end).chain(def_start..def_end).collect(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub(crate) enum Variables {
    Single { var: u32 },
    UseDef { use_var: u32, def_var: u32 },
}

impl Variables {
    pub(crate) fn single(var: Var) -> Self {
        Self::Single { var: var.as_u32() }
    }

    pub(crate) fn consume(value: &Consume<Var>) -> Self {
        Self::UseDef {
            use_var: value.r#use.as_u32(),
            def_var: value.def.as_u32(),
        }
    }

    fn variables(&self) -> Vec<u32> {
        match *self {
            Self::Single { var } => vec![var],
            Self::UseDef { use_var, def_var } => vec![use_var, def_var],
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct Matched {
    pub(crate) actual: Variables,
    pub(crate) formal: Variables,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct ReferencePeel {
    pub(crate) original_formal: Window,
    pub(crate) skipped: Variables,
    pub(crate) effective_formal: Window,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct CallArgRegistration {
    pub(crate) point: Point,
    pub(crate) ordinal: usize,
    pub(crate) proxy_local: u32,
    pub(crate) window: Window,
    pub(crate) by_reference: bool,
    pub(crate) source_occurrence: Availability<usize>,
}

/// The same proxy-local key selected by InferCtxt::call_args, not a Var search.
#[derive(Clone, Copy)]
pub(crate) struct SelectedProxy {
    pub(crate) proxy_local: u32,
    pub(crate) registration: Option<usize>,
    pub(crate) by_reference: bool,
}

thread_local! {
    static CALL_ARGUMENTS: RefCell<Option<Vec<Option<SelectedProxy>>>> = const { RefCell::new(None) };
}

pub(crate) struct CallScope {
    previous: Option<Vec<Option<SelectedProxy>>>,
    active: bool,
}

impl Drop for CallScope {
    fn drop(&mut self) {
        if self.active {
            CALL_ARGUMENTS.with(|arguments| *arguments.borrow_mut() = self.previous.take());
        }
    }
}

pub(crate) fn call_arguments(arguments: Option<Vec<Option<SelectedProxy>>>) -> CallScope {
    if !facts::active() {
        return CallScope {
            previous: None,
            active: false,
        };
    }
    CallScope {
        previous: CALL_ARGUMENTS.with(|current| current.replace(arguments)),
        active: true,
    }
}

pub(crate) fn register_proxy(
    proxy_local: u32,
    value: &Consume<Range<Var>>,
    by_reference: bool,
) -> Option<usize> {
    let point = ownership_evidence::point()?;
    let source_occurrence = ownership_occurrence::consume_at(&point, &value.into());
    facts::record(|facts| {
        let rows = &mut facts.call_arg_registrations;
        let ordinal = rows.len();
        rows.push(CallArgRegistration {
            point,
            ordinal,
            proxy_local,
            window: Window::consume(value),
            by_reference,
            source_occurrence,
        });
        ordinal
    })
}

fn actual_correspondence(
    point: &Point,
    role: Role,
    index: Option<usize>,
    actual: Option<&Window>,
) -> (Availability<usize>, Availability<usize>) {
    let missing =
        || Availability::Missing("boundary consume/proxy correspondence not recorded".into());
    if role == Role::ReturnReceiver {
        let occurrence = match actual {
            Some(Window::UseDef {
                use_start,
                use_end,
                def_start,
                def_end,
            }) => ownership_occurrence::consume_at(
                point,
                &ownership_occurrence::Window {
                    use_start: *use_start,
                    use_end: *use_end,
                    def_start: *def_start,
                    def_end: *def_end,
                },
            ),
            _ => missing(),
        };
        return (
            occurrence,
            Availability::Missing("return receiver is not an argument proxy".into()),
        );
    }
    if role != Role::CallArgument {
        return (missing(), missing());
    }
    let selected = index.and_then(|index| {
        CALL_ARGUMENTS.with(|arguments| {
            arguments
                .borrow()
                .as_ref()
                .and_then(|arguments| arguments.get(index))
                .copied()
                .flatten()
        })
    });
    let Some(selected) = selected else { return (missing(), missing()) };
    let Some(id) = selected.registration else { return (missing(), missing()) };
    let mut found = Vec::new();
    let _ = facts::read(|facts| {
        for row in &facts.call_arg_registrations {
            if row.ordinal == id
                && row.point.construction == point.construction
                && row.point.function == point.function
                && row.proxy_local == selected.proxy_local
                && row.by_reference == selected.by_reference
                && Some(&row.window) == actual
            {
                found.push(row.source_occurrence.clone());
            }
        }
    });
    if found.len() == 1 {
        (found.remove(0), Availability::Present(id))
    } else {
        (
            missing(),
            Availability::Missing(format!(
                "exact selected proxy registration matches: {}",
                found.len()
            )),
        )
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum LicensingRole {
    #[default]
    Legacy,
    Borrowed,
    OriginalCell,
    TraversalBorrow,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub(crate) struct Substitution {
    pub(crate) point: Point,
    pub(crate) ordinal: usize,
    pub(crate) role: Role,
    #[serde(default)]
    pub(crate) licensing_role: LicensingRole,
    pub(crate) callee: Option<String>,
    /// Original zero-based argument position, including unrepresented arguments.
    pub(crate) argument_index: Option<usize>,
    pub(crate) formal_local: Option<u32>,
    pub(crate) actual: Availability<Window>,
    pub(crate) formal: Availability<Window>,
    /// A matched Var range alone does not identify a caller place or SSA consume.
    pub(crate) actual_occurrence: Availability<usize>,
    pub(crate) call_arg_registration: Availability<usize>,
    pub(crate) reference_peel: Option<ReferencePeel>,
    pub(crate) matched: Vec<Matched>,
    pub(crate) unmatched_actual_vars: Vec<u32>,
    pub(crate) unmatched_formal_vars: Vec<u32>,
}

pub(crate) struct Recording(Substitution);

pub(crate) fn begin(
    role: Role,
    callee: Option<String>,
    argument_index: Option<usize>,
    actual: Option<Window>,
    formal: Option<Window>,
) -> Option<Recording> {
    let point = ownership_evidence::point()?;
    let (actual_occurrence, call_arg_registration) =
        actual_correspondence(&point, role, argument_index, actual.as_ref());
    let formal_local = formal.as_ref().and_then(|_| match role {
        Role::ReturnReceiver | Role::ExitReturn => Some(0),
        Role::Entry | Role::CallArgument | Role::ExitOutput => {
            argument_index.map(|index| (index + 1) as u32)
        }
    });
    Some(Recording(Substitution {
        point,
        ordinal: 0,
        role,
        licensing_role: LicensingRole::Legacy,
        callee,
        argument_index,
        formal_local,
        actual: actual.map(Availability::Present).unwrap_or_else(|| {
            Availability::Missing("actual ownership window not represented at this boundary".into())
        }),
        formal: formal.map(Availability::Present).unwrap_or_else(|| {
            Availability::Missing("formal ownership window not represented at this boundary".into())
        }),
        actual_occurrence,
        call_arg_registration,
        reference_peel: None,
        matched: Vec::new(),
        unmatched_actual_vars: Vec::new(),
        unmatched_formal_vars: Vec::new(),
    }))
}

pub(crate) fn matched(recording: &mut Option<Recording>, actual: Variables, formal: Variables) {
    if let Some(recording) = recording {
        recording.0.matched.push(Matched { actual, formal });
    }
}

pub(crate) fn preview(recording: &Option<Recording>) -> Option<&Substitution> {
    recording.as_ref().map(|recording| &recording.0)
}

pub(crate) fn original_cell(recording: &mut Option<Recording>) {
    if let Some(recording) = recording {
        recording.0.licensing_role = LicensingRole::OriginalCell;
    }
}

pub(crate) fn traversal_borrow(recording: &mut Option<Recording>) {
    if let Some(recording) = recording {
        recording.0.licensing_role = LicensingRole::TraversalBorrow;
    }
}

pub(crate) fn borrowed(recording: &mut Option<Recording>) {
    if let Some(recording) = recording {
        recording.0.licensing_role = LicensingRole::Borrowed;
    }
}

pub(crate) fn peel(recording: &mut Option<Recording>, skipped: &Consume<Var>) {
    let Some(recording) = recording else { return };
    let Availability::Present(original_formal) = &recording.0.formal else { return };
    let Window::UseDef {
        use_end, def_end, ..
    } = *original_formal
    else {
        return;
    };
    let effective_formal = Window::UseDef {
        use_start: skipped.r#use.as_u32() + 1,
        use_end,
        def_start: skipped.def.as_u32() + 1,
        def_end,
    };
    recording.0.reference_peel = Some(ReferencePeel {
        original_formal: original_formal.clone(),
        skipped: Variables::consume(skipped),
        effective_formal: effective_formal.clone(),
    });
    recording.0.formal = Availability::Present(effective_formal);
}

pub(crate) fn finish(recording: Option<Recording>) {
    let _ = finish_recorded(recording);
}

/// Return the assigned key after computing every matched and unmatched row.
pub(crate) fn finish_recorded(recording: Option<Recording>) -> Option<(u32, usize)> {
    let Recording(mut row) = recording?;
    let actual: BTreeSet<_> = row
        .matched
        .iter()
        .flat_map(|pair| pair.actual.variables())
        .collect();
    let formal: BTreeSet<_> = row
        .matched
        .iter()
        .flat_map(|pair| pair.formal.variables())
        .collect();
    if let Availability::Present(window) = &row.actual {
        row.unmatched_actual_vars = window
            .variables()
            .into_iter()
            .filter(|var| !actual.contains(var))
            .collect();
    }
    if let Availability::Present(window) = &row.formal {
        row.unmatched_formal_vars = window
            .variables()
            .into_iter()
            .filter(|var| !formal.contains(var))
            .collect();
    }
    facts::record(|facts| {
        let rows = &mut facts.boundary_substitutions;
        row.ordinal = rows.len();
        let key = (row.point.construction, row.ordinal);
        rows.push(row);
        key
    })
}

impl Window {
    fn valid(&self) -> bool {
        match *self {
            Self::Single { start, end } => start <= end,
            Self::UseDef {
                use_start,
                use_end,
                def_start,
                def_end,
            } => {
                use_start <= use_end
                    && def_start <= def_end
                    && use_end - use_start == def_end - def_start
            }
        }
    }

    fn ranges(&self) -> Vec<(u32, u32)> {
        match *self {
            Self::Single { start, end } => vec![(start, end)],
            Self::UseDef {
                use_start,
                use_end,
                def_start,
                def_end,
            } => {
                vec![(use_start, use_end), (def_start, def_end)]
            }
        }
    }

    fn contains(&self, values: &Variables) -> bool {
        match (self, values) {
            (Self::Single { start, end }, Variables::Single { var }) => start <= var && var < end,
            (
                Self::UseDef {
                    use_start,
                    use_end,
                    def_start,
                    def_end,
                },
                Variables::UseDef { use_var, def_var },
            ) => {
                use_start <= use_var
                    && use_var < use_end
                    && def_start <= def_var
                    && def_var < def_end
                    && use_var - use_start == def_var - def_start
            }
            _ => false,
        }
    }
}

fn valid_window(value: &Availability<Window>, single: bool) -> bool {
    match value {
        Availability::Present(window) => {
            window.valid() && matches!(window, Window::Single { .. }) == single
        }
        Availability::Missing(reason) => !reason.is_empty(),
    }
}

fn valid_reference(value: &Availability<usize>) -> bool {
    !matches!(value, Availability::Missing(reason) if reason.is_empty())
}

fn valid_tails(window: &Availability<Window>, used: &BTreeSet<u32>, tails: &[u32]) -> bool {
    let Availability::Present(window) = window else { return used.is_empty() && tails.is_empty() };
    // Check the expected cardinality before expanding untrusted ranges. Once
    // it agrees, expansion is bounded by supplied matches plus supplied tails.
    let expected_len: u64 = window
        .ranges()
        .into_iter()
        .map(|(start, end)| u64::from(end - start) - used.range(start..end).count() as u64)
        .sum();
    expected_len == tails.len() as u64
        && window
            .variables()
            .into_iter()
            .filter(|var| !used.contains(var))
            .eq(tails.iter().copied())
}

/// Validate observed shapes only. No independent all-calls/locals/returns roster
/// is supplied here; matcher equations and referenced records are separate gates.
pub(crate) fn validate_shapes(
    function: &str,
    substitutions: &[Substitution],
    registrations: &[CallArgRegistration],
) -> Result<(), String> {
    let mut ids = BTreeSet::new();
    for row in registrations {
        if row.point.function.as_deref() != Some(function)
            || row.point.phase != "statement"
            || row.point.block.is_none()
            || row.point.statement.is_none()
            || !ids.insert((row.point.construction, row.ordinal))
            || !row.window.valid()
            || !matches!(row.window, Window::UseDef { .. })
            || !valid_reference(&row.source_occurrence)
        {
            return Err("invalid or duplicate call-argument registration shape".into());
        }
    }
    ids.clear();
    for row in substitutions {
        let indexed = matches!(
            row.role,
            Role::Entry | Role::CallArgument | Role::ExitOutput
        );
        let call = matches!(row.role, Role::ReturnReceiver | Role::CallArgument);
        let phase_ok = match row.role {
            Role::Entry => {
                row.point.phase == "function"
                    && row.point.block.is_none()
                    && row.point.statement.is_none()
            }
            Role::ReturnReceiver | Role::CallArgument => {
                row.point.phase == "terminator"
                    && row.point.block.is_some()
                    && row.point.statement.is_some()
            }
            Role::ExitReturn | Role::ExitOutput => {
                row.point.phase == "return"
                    && row.point.block.is_some()
                    && row.point.statement.is_some()
            }
        };
        let expected_local = if matches!(row.formal, Availability::Present(_)) {
            if indexed {
                row.argument_index
                    .and_then(|index| index.checked_add(1))
                    .and_then(|index| u32::try_from(index).ok())
            } else {
                Some(0)
            }
        } else {
            None
        };
        if row.point.function.as_deref() != Some(function)
            || !phase_ok
            || (row.licensing_role != LicensingRole::Legacy
                && row.role != Role::CallArgument
                && !(row.licensing_role == LicensingRole::TraversalBorrow
                    && row.role == Role::ReturnReceiver))
            || (row.licensing_role == LicensingRole::OriginalCell && row.reference_peel.is_none())
            || !ids.insert((row.point.construction, row.ordinal))
            || indexed != row.argument_index.is_some()
            || call != row.callee.is_some()
            || row.callee.as_ref().is_some_and(String::is_empty)
            || row.formal_local != expected_local
            || (matches!(row.formal, Availability::Present(_)) && expected_local.is_none())
            || !valid_window(&row.actual, !call)
            || !valid_window(&row.formal, row.role != Role::CallArgument)
            || !valid_reference(&row.actual_occurrence)
            || !valid_reference(&row.call_arg_registration)
        {
            return Err("invalid or duplicate boundary-substitution shape".into());
        }
        let mut pairs = BTreeSet::new();
        let mut actual = BTreeSet::new();
        let mut formal = BTreeSet::new();
        for pair in &row.matched {
            let (Availability::Present(actual_window), Availability::Present(formal_window)) =
                (&row.actual, &row.formal)
            else {
                return Err("boundary match has unavailable windows".into());
            };
            if !actual_window.contains(&pair.actual)
                || !formal_window.contains(&pair.formal)
                || !pairs.insert((pair.actual.variables(), pair.formal.variables()))
            {
                return Err("duplicate or out-of-window boundary match".into());
            }
            actual.extend(pair.actual.variables());
            formal.extend(pair.formal.variables());
        }
        if !valid_tails(&row.actual, &actual, &row.unmatched_actual_vars)
            || !valid_tails(&row.formal, &formal, &row.unmatched_formal_vars)
        {
            return Err("boundary unmatched tails disagree with observed matches".into());
        }
    }
    Ok(())
}

fn observed_window(window: &Window) -> Option<ownership_occurrence::Window> {
    match *window {
        Window::UseDef {
            use_start,
            use_end,
            def_start,
            def_end,
        } => Some(ownership_occurrence::Window {
            use_start,
            use_end,
            def_start,
            def_end,
        }),
        Window::Single { .. } => None,
    }
}

fn validate_peel(row: &Substitution) -> Result<(), String> {
    let Some(peel) = &row.reference_peel else { return Ok(()) };
    let (
        Window::UseDef {
            use_start,
            use_end,
            def_start,
            def_end,
        },
        Variables::UseDef { use_var, def_var },
    ) = (&peel.original_formal, &peel.skipped)
    else {
        return Err("reference peel has invalid window/value kinds".into());
    };
    if row.role != Role::CallArgument
        || !matches!(row.actual, Availability::Present(_))
        || !peel.original_formal.valid()
        || use_start >= use_end
        || def_start >= def_end
        || use_var != use_start
        || def_var != def_start
    {
        return Err("reference peel is not the original outer pair".into());
    }
    let expected = Window::UseDef {
        use_start: use_start + 1,
        use_end: *use_end,
        def_start: def_start + 1,
        def_end: *def_end,
    };
    if peel.effective_formal != expected
        || row.formal != Availability::Present(expected)
        || row.matched.iter().any(|pair| {
            pair.formal
                .variables()
                .iter()
                .any(|var| var == use_var || var == def_var)
        })
    {
        return Err("reference peel/effective matches disagree".into());
    }
    Ok(())
}

/// Check only supplied equation and reference correspondence. Missing facts
/// remain unavailable; this does not reconstruct a source/return roster.
pub(crate) fn validate_links(
    function: &str,
    substitutions: &[Substitution],
    registrations: &[CallArgRegistration],
    consumes: &[ownership_occurrence::Consumption],
    equations: &[ownership_evidence::Equation],
) -> Result<(), String> {
    use Availability::{Missing, Present};
    let consumes: std::collections::BTreeMap<_, _> = consumes
        .iter()
        .map(|row| ((row.point.construction, row.ordinal), row))
        .collect();
    let registrations: std::collections::BTreeMap<_, _> = registrations
        .iter()
        .map(|row| ((row.point.construction, row.ordinal), row))
        .collect();
    let mut at_point =
        std::collections::BTreeMap::<Point, Vec<&ownership_evidence::Equation>>::new();
    for equation in equations {
        at_point
            .entry(equation.point.clone())
            .or_default()
            .push(equation);
    }
    let has = |point: &Point, operation: &str, variables: &[u32], value: Option<bool>| {
        at_point.get(point).is_some_and(|equations| {
            equations.iter().any(|equation| {
                equation.operation == operation
                    && equation.variables == variables
                    && equation.value == value
            })
        })
    };
    for registration in registrations.values() {
        if let Present(id) = &registration.source_occurrence {
            let consume = consumes
                .get(&(registration.point.construction, *id))
                .ok_or("proxy registration refers to a missing consume")?;
            let window =
                observed_window(&registration.window).ok_or("proxy has no consume window")?;
            // R357-2: the resolving lookup admits a narrowing cast's leading
            // window, so the check that validates it uses the same rule —
            // otherwise the two disagree about the same registration.
            let corresponds = consume.projected == Present(window.clone())
                || matches!(&consume.projected,
                    Present(projected) if ownership_occurrence::narrows(&window, projected));
            if consume.point != registration.point
                || consume.point.function.as_deref() != Some(function)
                || !corresponds
            {
                return Err("proxy registration/consume correspondence mismatch".into());
            }
        }
    }
    for row in substitutions {
        validate_peel(row)?;
        if row.licensing_role == LicensingRole::Borrowed {
            let formal = row
                .reference_peel
                .as_ref()
                .map(|peel| Present(peel.original_formal.clone()))
                .unwrap_or_else(|| row.formal.clone());
            let (
                Present(Window::UseDef {
                    use_start: a0,
                    use_end: a1,
                    def_start: a2,
                    ..
                }),
                Present(Window::UseDef {
                    use_start: p0,
                    use_end: p1,
                    def_start: p2,
                    def_end: p3,
                }),
            ) = (&row.actual, &formal)
            else {
                return Err("borrowed call needs actual and formal windows".into());
            };
            if !(*a0..*a1)
                .zip(*a2..)
                .all(|(before, after)| has(&row.point, "equal", &[before, after], None))
                || !(*p0..*p1)
                    .chain(*p2..*p3)
                    .all(|var| has(&row.point, "assume", &[var], Some(false)))
            {
                return Err("borrowed call lost full frame or zero-view obligations".into());
            }
        }
        for pair in &row.matched {
            let supported = match (row.role, &pair.actual, &pair.formal) {
                (
                    Role::Entry | Role::ExitReturn | Role::ExitOutput,
                    Variables::Single { var: actual },
                    Variables::Single { var: formal },
                ) => has(&row.point, "equal", &[*actual, *formal], None),
                (
                    Role::ReturnReceiver,
                    Variables::UseDef { use_var, def_var },
                    Variables::Single { var: formal },
                ) => {
                    has(&row.point, "assume", &[*use_var], Some(false))
                        && has(
                            &row.point,
                            if row.licensing_role == LicensingRole::TraversalBorrow {
                                "guarded-traversal-receiver-legacy"
                            } else {
                                "equal"
                            },
                            &[*def_var, *formal],
                            None,
                        )
                }
                (
                    Role::CallArgument,
                    Variables::UseDef {
                        use_var: actual_use,
                        def_var: actual_def,
                    },
                    Variables::UseDef {
                        use_var: formal_use,
                        def_var: formal_def,
                    },
                ) => {
                    if row.licensing_role == LicensingRole::TraversalBorrow {
                        has(
                            &row.point,
                            "guarded-traversal-argument-legacy",
                            &[*formal_use, *actual_use, *formal_def, *actual_def],
                            None,
                        )
                    } else if row.licensing_role == LicensingRole::OriginalCell {
                        // The full two-site and predicate correspondence is
                        // checked by cell_effects::validate_calls. This retained
                        // legacy arm must still name this exact matched pair.
                        has(
                            &row.point,
                            "guarded-original-cell-legacy",
                            &[*formal_use, *actual_use, *formal_def, *actual_def],
                            None,
                        )
                    } else if row.licensing_role == LicensingRole::Borrowed {
                        has(&row.point, "equal", &[*actual_use, *actual_def], None)
                            && has(&row.point, "assume", &[*formal_use], Some(false))
                            && has(&row.point, "assume", &[*formal_def], Some(false))
                    } else {
                        has(&row.point, "equal", &[*formal_use, *actual_use], None)
                            && has(&row.point, "equal", &[*formal_def, *actual_def], None)
                    }
                }
                _ => false,
            };
            if !supported {
                return Err("boundary matched pair has no corresponding emitted equation".into());
            }
        }
        match row.role {
            Role::ReturnReceiver => {
                if matches!(row.call_arg_registration, Present(_)) {
                    return Err("return receiver cannot claim an argument registration".into());
                }
                if let Present(id) = &row.actual_occurrence {
                    let consume = consumes
                        .get(&(row.point.construction, *id))
                        .ok_or("return receiver refers to a missing consume")?;
                    let Present(actual) = &row.actual else {
                        return Err("receiver link has no actual window".into());
                    };
                    let window = observed_window(actual).ok_or("receiver has no consume window")?;
                    if consume.point != row.point
                        || consume.point.function.as_deref() != Some(function)
                        || consume.projected != Present(window)
                    {
                        return Err("receiver/consume correspondence mismatch".into());
                    }
                }
            }
            Role::CallArgument => match &row.call_arg_registration {
                Present(id) => {
                    let registration = registrations
                        .get(&(row.point.construction, *id))
                        .ok_or("argument refers to a missing proxy registration")?;
                    if registration.point.function.as_deref() != Some(function)
                        || row.actual != Present(registration.window.clone())
                        || row.actual_occurrence != registration.source_occurrence
                        || (matches!(row.formal, Present(_))
                            && registration.by_reference != row.reference_peel.is_some())
                    {
                        return Err("argument/proxy registration correspondence mismatch".into());
                    }
                }
                Missing(_) if matches!(row.actual_occurrence, Present(_)) => {
                    return Err("argument consume has no selected proxy registration".into());
                }
                Missing(_) => {}
            },
            Role::Entry | Role::ExitReturn | Role::ExitOutput => {
                if matches!(row.actual_occurrence, Present(_))
                    || matches!(row.call_arg_registration, Present(_))
                {
                    return Err("unsupported positive boundary consume/proxy correspondence".into());
                }
            }
        }
    }
    Ok(())
}
