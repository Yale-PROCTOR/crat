//! Independent compiler body/call observations. Complete means this recorded
//! graph is covered; it proves no memory effect, retention, or attestation.
use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

use super::super::origin_evidence::SourceSite;
use crate::utils::rustc::RustProgram;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) struct LocalCall {
    pub(crate) site: SourceSite,
    pub(crate) target: String,
}
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) struct Coverage {
    pub(crate) configured_functions: BTreeSet<String>,
    pub(crate) compiler_bodies: BTreeSet<String>,
    /// R304-10: `#[automatically_derived]` impl bodies, admitted to the roster
    /// with their role rather than filtered away — a derived `Clone` copies
    /// pointers, so it must stay visible to every consumer that asks.
    #[serde(default, skip_serializing_if = "BTreeSet::is_empty")]
    pub(crate) derived_impl_bodies: BTreeSet<String>,
    pub(crate) local_calls: BTreeSet<LocalCall>,
    pub(crate) indirect_calls: BTreeSet<SourceSite>,
    pub(crate) function_values: BTreeSet<SourceSite>,
    pub(crate) inline_assembly: BTreeSet<SourceSite>,
    pub(crate) duplicate_functions: bool,
}
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub(crate) enum Reason {
    ConfiguredFunctions,
    CompilerBodies,
    BodyRoster,
    SourceCalls,
    IndirectCall,
    FunctionValue,
    InlineAssembly,
}
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub(crate) enum Status {
    Missing,
    Complete,
    Held(BTreeSet<Reason>),
}
impl Coverage {
    pub(crate) fn collect(program: &RustProgram<'_>) -> Self {
        use rustc_middle::{
            mir::{TerminatorKind, visit::Visitor},
            ty::TyKind,
        };
        let tcx = program.tcx;
        let mut result = Self {
            configured_functions: program
                .functions
                .iter()
                .map(|&f| tcx.def_path_str(f))
                .collect(),
            compiler_bodies: tcx.hir_body_owners().map(|f| tcx.def_path_str(f)).collect(),
            derived_impl_bodies: tcx
                .hir_body_owners()
                .filter(|&owner| {
                    let parent = tcx.parent(owner.to_def_id());
                    matches!(tcx.def_kind(parent), rustc_hir::def::DefKind::Impl { .. })
                        && tcx.is_automatically_derived(parent)
                })
                .map(|f| tcx.def_path_str(f))
                .collect(),
            ..Self::default()
        };
        result.duplicate_functions = result.configured_functions.len() != program.functions.len();
        for &function in &program.functions {
            let body = tcx
                .mir_drops_elaborated_and_const_checked(function)
                .borrow();
            let name = tcx.def_path_str(function);
            let mut values = Values {
                tcx,
                body: &body,
                function: name.clone(),
                sites: BTreeSet::new(),
            };
            for (block, data) in body.basic_blocks.iter_enumerated() {
                for (statement_index, statement) in data.statements.iter().enumerate() {
                    values.visit_statement(
                        statement,
                        rustc_middle::mir::Location {
                            block,
                            statement_index,
                        },
                    );
                }
                let location = rustc_middle::mir::Location {
                    block,
                    statement_index: data.statements.len(),
                };
                let site = SourceSite {
                    function: name.clone(),
                    block: block.as_u32(),
                    statement: location.statement_index,
                };
                match &data.terminator().kind {
                    TerminatorKind::Call { func, args, .. }
                    | TerminatorKind::TailCall { func, args, .. } => {
                        for arg in args {
                            values.visit_operand(&arg.node, location);
                        }
                        match *func.ty(&*body, tcx).kind() {
                            TyKind::FnDef(target, _) => {
                                if let Some(local) = target.as_local()
                                    && !matches!(
                                        tcx.hir_node_by_def_id(local),
                                        rustc_hir::Node::ForeignItem(_)
                                    )
                                {
                                    result.local_calls.insert(LocalCall {
                                        site,
                                        target: tcx.def_path_str(target),
                                    });
                                }
                            }
                            _ => {
                                result.indirect_calls.insert(site);
                            }
                        }
                    }
                    TerminatorKind::InlineAsm { .. } => {
                        result.inline_assembly.insert(site);
                    }
                    _ => values.visit_terminator(data.terminator(), location),
                }
            }
            result.function_values.extend(values.sites);
        }
        result
    }
}
pub(crate) fn assess(facts: &super::facts::Facts) -> Status {
    use super::super::origin_evidence::SourceCallee;
    let Some(coverage) = &facts.caller_coverage else { return Status::Missing };
    let functions: BTreeSet<_> = facts.source_occurrences.keys().cloned().collect();
    let mut held = BTreeSet::new();
    if functions.is_empty()
        || coverage.duplicate_functions
        || coverage.configured_functions != functions
        || facts
            .source_occurrences
            .iter()
            .any(|(function, rows)| rows.iter().any(|row| &row.site.function != function))
    {
        held.insert(Reason::ConfiguredFunctions);
    }
    // R304-10: a derived impl body is accounted for by its role, never dropped
    // from the denominator. Every other compiler body still has to be configured.
    if coverage.compiler_bodies.iter().any(|body| {
        !coverage.configured_functions.contains(body)
            && !coverage.derived_impl_bodies.contains(body)
    }) || coverage
        .configured_functions
        .iter()
        .any(|body| !coverage.compiler_bodies.contains(body))
    {
        held.insert(Reason::CompilerBodies);
    }
    let expected: BTreeSet<_> = (0..facts.constructions)
        .flat_map(|construction| {
            functions
                .iter()
                .cloned()
                .map(move |function| (construction, function))
        })
        .collect();
    let bodies: BTreeSet<_> = facts
        .body_rosters
        .iter()
        .filter_map(|body| {
            body.point
                .function
                .clone()
                .map(|function| (body.point.construction, function))
        })
        .collect();
    if facts.constructions == 0 || bodies != expected || bodies.len() != facts.body_rosters.len() {
        held.insert(Reason::BodyRoster);
    }
    let recorded: Vec<_> = facts
        .source_occurrences
        .values()
        .flat_map(|rows| rows.iter())
        .filter_map(|row| match &row.callee {
            Some(SourceCallee::Local(target)) => Some(LocalCall {
                site: row.site.clone(),
                target: target.clone(),
            }),
            _ => None,
        })
        .collect();
    let calls: BTreeSet<_> = recorded.iter().cloned().collect();
    if calls.len() != recorded.len()
        || calls != coverage.local_calls
        || calls.iter().any(|call| {
            !functions.contains(&call.site.function)
                || !(functions.contains(&call.target)
                    || coverage.derived_impl_bodies.contains(&call.target))
        })
    {
        held.insert(Reason::SourceCalls);
    }
    if !coverage.indirect_calls.is_empty() {
        held.insert(Reason::IndirectCall);
    }
    if !coverage.function_values.is_empty() {
        held.insert(Reason::FunctionValue);
    }
    if !coverage.inline_assembly.is_empty() {
        held.insert(Reason::InlineAssembly);
    }
    if held.is_empty() {
        Status::Complete
    } else {
        Status::Held(held)
    }
}

struct Values<'a, 'tcx> {
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    body: &'a rustc_middle::mir::Body<'tcx>,
    function: String,
    sites: BTreeSet<SourceSite>,
}
impl<'tcx> rustc_middle::mir::visit::Visitor<'tcx> for Values<'_, 'tcx> {
    fn visit_operand(
        &mut self,
        operand: &rustc_middle::mir::Operand<'tcx>,
        location: rustc_middle::mir::Location,
    ) {
        if matches!(
            operand.ty(self.body, self.tcx).kind(),
            rustc_middle::ty::TyKind::FnDef(..) | rustc_middle::ty::TyKind::FnPtr(..)
        ) {
            self.sites.insert(SourceSite {
                function: self.function.clone(),
                block: location.block.as_u32(),
                statement: location.statement_index,
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        super::{graph_tests::with_facts, snapshot::Snapshot},
        *,
    };
    const CODE: &str = r#"
unsafe extern "C" {fn malloc(n:usize)->*mut core::ffi::c_void;fn free(p:*mut core::ffi::c_void);}
pub struct Cell {ptr:*mut i32}
pub unsafe fn make()->*mut i32 {let p=malloc(4) as *mut i32;*p=5;p}
pub unsafe fn put(c:*mut Cell,p:*mut i32){(*c).ptr=p;}
pub unsafe fn take(c:*mut Cell)->*mut i32 {let p=(*c).ptr;(*c).ptr=0 as *mut i32;p}
pub unsafe fn release(c:*mut Cell){let p=take(c);free(p as *mut core::ffi::c_void);}
pub unsafe fn f(){let owner=make();let mut c=Cell{ptr:0 as *mut i32};put(&mut c,owner);release(&mut c);}
"#;
    fn held(status: Status, reason: Reason) {
        assert!(matches!(status,Status::Held(reasons) if reasons.contains(&reason)));
    }
    #[test]
    fn c04_caller_coverage_complete_direct_graph_and_snapshot_readback() {
        with_facts(CODE, |facts| {
            let coverage = facts
                .caller_coverage
                .as_ref()
                .expect("normative compiler coverage is always produced");
            assert_eq!(assess(facts), Status::Complete);
            assert_eq!(coverage.configured_functions.len(), 5);
            assert_eq!(coverage.local_calls.len(), 4);
            let snapshot = Snapshot::capture(facts, 0).unwrap();
            let decoded: Snapshot =
                serde_json::from_slice(&serde_json::to_vec(&snapshot).unwrap()).unwrap();
            assert_eq!(
                decoded.metadata.facts().caller_coverage,
                facts.caller_coverage
            );
            assert_eq!(decoded.caller_coverage, Status::Complete);
            decoded.validate().unwrap();
            let mut missing = decoded.clone();
            missing.metadata.caller_coverage = None;
            assert!(missing.validate().is_err());
            let mut corrupt = decoded.clone();
            corrupt
                .metadata
                .caller_coverage
                .as_mut()
                .unwrap()
                .local_calls
                .clear();
            assert!(corrupt.validate().is_err());
        });
    }
    #[test]
    fn c04_caller_coverage_missing_function_body_and_source_call_hold() {
        with_facts(CODE, |facts| {
            assert_eq!(assess(facts), Status::Complete);
            let mut missing = facts.clone();
            missing.source_occurrences.remove("take");
            held(assess(&missing), Reason::ConfiguredFunctions);
            let mut missing = facts.clone();
            missing
                .body_rosters
                .retain(|body| body.point.function.as_deref() != Some("take"));
            held(assess(&missing), Reason::BodyRoster);
            let mut missing = facts.clone();
            missing
                .source_occurrences
                .get_mut("f")
                .unwrap()
                .retain(|row| {
                    row.callee.as_ref()
                        != Some(&super::super::super::origin_evidence::SourceCallee::Local(
                            "put".into(),
                        ))
                });
            held(assess(&missing), Reason::SourceCalls);
            let mut missing = facts.clone();
            missing
                .caller_coverage
                .as_mut()
                .unwrap()
                .compiler_bodies
                .remove("take");
            held(assess(&missing), Reason::CompilerBodies);
        });
    }
    #[test]
    fn c04_caller_coverage_function_values_and_indirect_calls_are_local_holds() {
        for (code, reason) in [
            (
                format!("{CODE}\npub fn escape()->unsafe fn(*mut Cell){{release}}"),
                Reason::FunctionValue,
            ),
            (
                format!(
                    "{CODE}\npub unsafe fn indirect(p:*mut Cell){{let callback:unsafe fn(*mut Cell)=release;callback(p);}}"
                ),
                Reason::IndirectCall,
            ),
        ] {
            with_facts(&code, move |facts| {
                assert!(facts.caller_coverage.is_some());
                held(assess(facts), reason);
                Snapshot::capture(facts, 0).unwrap().validate().unwrap();
            });
        }
    }
    #[test]
    fn c04_caller_coverage_const_and_omitted_nested_body_are_local_gaps() {
        with_facts(
            &format!("{CODE}\npub const CALLBACK:unsafe fn(*mut Cell)=release;"),
            |facts| {
                held(assess(facts), Reason::CompilerBodies);
                Snapshot::capture(facts, 0).unwrap().validate().unwrap();
            },
        );
        with_facts(
            &format!("{CODE}\npub fn outer(){{fn nested(){{}}nested();}}"),
            |facts| {
                let nested = facts
                    .caller_coverage
                    .as_ref()
                    .unwrap()
                    .compiler_bodies
                    .iter()
                    .find(|f| f.ends_with("::nested"))
                    .unwrap()
                    .clone();
                let mut missing = facts.clone();
                missing.source_occurrences.remove(&nested);
                held(assess(&missing), Reason::ConfiguredFunctions);
                missing
                    .caller_coverage
                    .as_mut()
                    .unwrap()
                    .configured_functions
                    .remove(&nested);
                missing
                    .body_rosters
                    .retain(|body| body.point.function.as_ref() != Some(&nested));
                held(assess(&missing), Reason::CompilerBodies);
            },
        );
    }
}
