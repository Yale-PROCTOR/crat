use std::{fmt, fs, io, path::Path};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_index::{IndexVec, bit_set::DenseBitSet};
use rustc_middle::{
    mir::{Local, LocalDecl},
    ty::TyCtxt,
};
use rustc_span::def_id::LocalDefId;

use super::{Analysis, collector::collect_fn_ptrs};
use crate::{
    analyses::ownership::Ownership,
    utils::rustc::RustProgram,
};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PtrKind {
    /// owning pointer represented as Option<Box<T>>
    Move(bool),
    /// reference: &mut T for Ref(true), or &T for Ref(false)
    OptRef(bool),
    /// raw pointer: *mut T for Raw(true), or *const T for Raw(false)
    Raw(bool),
    /// plain slice: &mut [T] for Slice(true), or &[T] for Slice(false)
    Slice(bool),
    /// slice cursor with offset tracking: SliceCursor<T> for SliceCursor(true),
    /// or SliceCursorRef<T> for SliceCursor(false)
    SliceCursor(bool),
}

impl PtrKind {
    pub fn is_mut(&self) -> bool {
        match self {
            PtrKind::Move(m)
            | PtrKind::OptRef(m)
            | PtrKind::Raw(m)
            | PtrKind::Slice(m)
            | PtrKind::SliceCursor(m) => *m,
        }
    }

    pub fn with_mut(self, m: bool) -> Self {
        match self {
            PtrKind::Move(_) => PtrKind::Move(m),
            PtrKind::OptRef(_) => PtrKind::OptRef(m),
            PtrKind::Raw(_) => PtrKind::Raw(m),
            PtrKind::Slice(_) => PtrKind::Slice(m),
            PtrKind::SliceCursor(_) => PtrKind::SliceCursor(m),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SpecPtrClass {
    Move,
    Mut,
    Const,
    RawMove,
    RawMut,
    RawConst,
}

impl fmt::Display for SpecPtrClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SpecPtrClass::Move => write!(f, "Move"),
            SpecPtrClass::Mut => write!(f, "Mut"),
            SpecPtrClass::Const => write!(f, "Const"),
            SpecPtrClass::RawMove => write!(f, "Raw(Move)"),
            SpecPtrClass::RawMut => write!(f, "Raw(Mut)"),
            SpecPtrClass::RawConst => write!(f, "Raw(Const)"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct DecisionConflict {
    pub rule_id: &'static str,
    pub site: String,
    pub legacy_decision: SpecPtrClass,
    pub spec_decision: SpecPtrClass,
    pub chosen: SpecPtrClass,
    pub note: String,
}

impl DecisionConflict {
    pub fn key(&self) -> String {
        format!("{}|{}", self.rule_id, self.site)
    }
}

fn kind_to_spec(kind: PtrKind) -> SpecPtrClass {
    match kind {
        PtrKind::Move(_) => SpecPtrClass::Move,
        PtrKind::OptRef(true) => SpecPtrClass::Mut,
        PtrKind::OptRef(false) => SpecPtrClass::Const,
        PtrKind::Raw(true) => SpecPtrClass::RawMut,
        PtrKind::Raw(false) => SpecPtrClass::RawConst,
        PtrKind::Slice(true) | PtrKind::SliceCursor(true) => SpecPtrClass::RawMut,
        PtrKind::Slice(false) | PtrKind::SliceCursor(false) => SpecPtrClass::RawConst,
    }
}

fn parse_existing_conflict_keys(existing: &str) -> FxHashSet<String> {
    existing
        .lines()
        .filter_map(|line| {
            let trimmed = line.trim();
            let pref = "- KEY: `";
            if !trimmed.starts_with(pref) {
                return None;
            }
            let rest = &trimmed[pref.len()..];
            let end = rest.find('`')?;
            Some(rest[..end].to_owned())
        })
        .collect()
}

fn conflict_markdown_entry(conflict: &DecisionConflict) -> String {
    let mut entry = String::new();
    let key = conflict.key();
    use std::fmt::Write as _;
    writeln!(&mut entry, "- KEY: `{key}`").unwrap();
    writeln!(&mut entry, "  - rule_id: `{}`", conflict.rule_id).unwrap();
    writeln!(&mut entry, "  - site: `{}`", conflict.site).unwrap();
    writeln!(
        &mut entry,
        "  - legacy_decision: `{}`",
        conflict.legacy_decision
    )
    .unwrap();
    writeln!(&mut entry, "  - spec_decision: `{}`", conflict.spec_decision).unwrap();
    writeln!(&mut entry, "  - chosen: `{}`", conflict.chosen).unwrap();
    writeln!(&mut entry, "  - chosen_behavior: `{}`", conflict.chosen).unwrap();
    writeln!(&mut entry, "  - minimal_repro: `<pending capture>`").unwrap();
    writeln!(&mut entry, "  - current_output: `<pending capture>`").unwrap();
    writeln!(&mut entry, "  - expected_output: `<pending capture>`").unwrap();
    writeln!(&mut entry, "  - spec_author_question: {}", conflict.note).unwrap();
    entry
}

pub(crate) fn merge_conflict_log(existing: &str, conflicts: &[DecisionConflict]) -> String {
    let mut merged = existing.to_owned();
    if merged.trim().is_empty() {
        merged.push_str("# Pointer Rewriter Conflicts\n\n");
    } else if !merged.ends_with('\n') {
        merged.push('\n');
    }
    if !merged.contains("## Recorded Conflicts") {
        if !merged.ends_with("\n\n") {
            merged.push('\n');
        }
        merged.push_str("## Recorded Conflicts\n\n");
    }

    let mut seen = parse_existing_conflict_keys(&merged);
    let mut to_append = conflicts.to_vec();
    to_append.sort_by_key(DecisionConflict::key);

    for conflict in to_append {
        let key = conflict.key();
        if !seen.insert(key) {
            continue;
        }
        merged.push_str(&conflict_markdown_entry(&conflict));
        merged.push('\n');
    }

    merged
}

pub(crate) fn append_conflicts_to_file(path: &Path, conflicts: &[DecisionConflict]) -> io::Result<()> {
    if conflicts.is_empty() {
        return Ok(());
    }

    let existing = fs::read_to_string(path).unwrap_or_default();
    let merged = merge_conflict_log(&existing, conflicts);
    if merged != existing {
        fs::write(path, merged)?;
    }
    Ok(())
}

pub(crate) fn ownership_priority_choice_for_test(
    legacy: PtrKind,
    owning: bool,
    is_raw_decl: bool,
    mutable: bool,
    site: &str,
) -> (PtrKind, Option<DecisionConflict>) {
    if !owning {
        return (legacy, None);
    }
    let spec_kind = PtrKind::Move(mutable);
    if legacy == spec_kind {
        return (legacy, None);
    }

    (
        spec_kind,
        Some(DecisionConflict {
            rule_id: "TY-100",
            site: site.to_owned(),
            legacy_decision: kind_to_spec(legacy),
            spec_decision: SpecPtrClass::Move,
            chosen: SpecPtrClass::Move,
            note: if is_raw_decl {
                "Ownership analysis marks this pointer as owning; ownership-first box-class rewrite applied."
                    .to_owned()
            } else {
                "Ownership-first override applied at non-raw declaration site (spec-author note candidate: confirm whether this site should remain box-class under TY/SIG iteration-1)."
                    .to_owned()
            },
        }),
    )
}

pub struct DecisionMaker<'tcx> {
    tcx: TyCtxt<'tcx>,
    file_label: String,
    fn_path: String,
    enable_box_rewrite: bool,
    mutable_pointers: IndexVec<Local, bool>,
    owning_pointers: IndexVec<Local, bool>,
    array_pointers: IndexVec<Local, bool>,
    promoted_mut_refs: DenseBitSet<Local>,
    promoted_shared_refs: DenseBitSet<Local>,
    /// Locals that need a SliceCursor because they are offset with potentially-negative values.
    needs_cursor: DenseBitSet<Local>,
}

impl<'tcx> DecisionMaker<'tcx> {
    pub fn new(analysis: &Analysis, did: LocalDefId, tcx: TyCtxt<'tcx>) -> Self {
        let mir_body = tcx.mir_drops_elaborated_and_const_checked(did);
        let body = mir_body.borrow();
        let mutable_pointers = analysis
            .mutability_result
            .function_body_facts(did)
            .map(|mutabilities| mutabilities.iter().any(|m| m.is_mutable()))
            .collect::<IndexVec<Local, _>>();
        let mut owning_pointers = IndexVec::from_elem_n(false, body.local_decls.len());
        if let Some(owning_results) = analysis.ownership_result.as_ref() {
            let owning_results = owning_results.fn_results(&did.to_def_id());
            for (local, decl) in body.local_decls.iter_enumerated() {
                if !decl.ty.is_raw_ptr() {
                    continue;
                }
                let is_owning = owning_results
                    .local_result(local)
                    .first()
                    .is_some_and(Ownership::is_owning);
                owning_pointers[local] = is_owning;
            }
        }
        let array_pointers = analysis
            .fatness_result
            .function_body_facts(did)
            .map(|fatnesses| fatnesses.iter().next().map(|f| f.is_arr()).unwrap_or(false))
            .collect::<IndexVec<Local, _>>();
        let promoted_mut_refs = analysis.promoted_mut_ref_result.get(&did).unwrap().clone();
        let promoted_shared_refs = analysis
            .promoted_shared_ref_result
            .get(&did)
            .unwrap()
            .clone();
        let hir_to_mir = utils::ir::map_thir_to_mir(did, false, tcx);
        let fn_offset_signs = analysis.offset_sign_result.access_signs.get(&did);
        let mut needs_cursor = DenseBitSet::new_empty(mutable_pointers.len());
        for (hir_id, local) in hir_to_mir.binding_to_local {
            if fn_offset_signs
                .is_some_and(|signs| signs.get(&hir_id).is_some_and(|s| s.needs_cursor()))
            {
                needs_cursor.insert(local);
            }
        }
        DecisionMaker {
            tcx,
            file_label: {
                let file = tcx
                    .sess
                    .source_map()
                    .span_to_filename(tcx.def_span(did))
                    .prefer_local()
                    .to_string();
                file.rsplit(['/', '\\']).next().unwrap_or(&file).to_owned()
            },
            fn_path: tcx.def_path_str(did.to_def_id()),
            enable_box_rewrite: analysis.enable_box_rewrite,
            array_pointers,
            mutable_pointers,
            owning_pointers,
            promoted_mut_refs,
            promoted_shared_refs,
            needs_cursor,
        }
    }

    fn decide_legacy(
        &self,
        local: Local,
        decl: &LocalDecl<'tcx>,
        aliases: Option<&FxHashSet<Local>>,
    ) -> Option<PtrKind> {
        let (ty, m) = super::transform::unwrap_ptr_from_mir_ty(decl.ty)?;
        if ty.is_c_void(self.tcx) || utils::file::contains_file_ty(ty, self.tcx) {
            Some(PtrKind::Raw(m.is_mut()))
        } else if aliases.is_some_and(|aliases| {
            std::iter::once(local)
                .chain(aliases.iter().copied())
                .any(|l| self.mutable_pointers[l])
        }) {
            Some(PtrKind::Raw(self.mutable_pointers[local]))
        } else if self.array_pointers[local] {
            if self.promoted_shared_refs.contains(local) {
                if self.needs_cursor.contains(local) {
                    Some(PtrKind::SliceCursor(false))
                } else {
                    Some(PtrKind::Slice(false))
                }
            } else if self.promoted_mut_refs.contains(local) {
                if self.needs_cursor.contains(local) {
                    Some(PtrKind::SliceCursor(true))
                } else {
                    Some(PtrKind::Slice(true))
                }
            } else {
                Some(PtrKind::Raw(self.mutable_pointers[local]))
            }
        } else if self.promoted_shared_refs.contains(local) {
            Some(PtrKind::OptRef(false))
        } else if self.promoted_mut_refs.contains(local) {
            Some(PtrKind::OptRef(true))
        } else if decl.ty.is_raw_ptr() {
            Some(PtrKind::Raw(self.mutable_pointers[local]))
        } else {
            None
        }
    }

    pub fn decide(
        &self,
        local: Local,
        decl: &LocalDecl<'tcx>,
        aliases: Option<&FxHashSet<Local>>,
    ) -> (Option<PtrKind>, Option<DecisionConflict>) {
        let legacy = self.decide_legacy(local, decl, aliases);
        let owning = self
            .owning_pointers
            .get(local)
            .copied()
            .unwrap_or(false);
        let Some(legacy_kind) = legacy else {
            return (None, None);
        };
        let site = format!(
            "{}|{}|local{}",
            self.file_label,
            self.fn_path,
            local.index()
        );
        if !self.enable_box_rewrite {
            let conflict = if owning {
                Some(DecisionConflict {
                    rule_id: "TY-100",
                    site,
                    legacy_decision: kind_to_spec(legacy_kind),
                    spec_decision: SpecPtrClass::Move,
                    chosen: kind_to_spec(legacy_kind),
                    note: "Ownership marks owning, but box-class rewrite is disabled by legacy-compatible profile (`force_box=false`) (spec-author note candidate: clarify default-option precedence vs mandatory ownership-first behavior).".to_owned(),
                })
            } else {
                None
            };
            return (Some(legacy_kind), conflict);
        }
        let (chosen, conflict) = ownership_priority_choice_for_test(
            legacy_kind,
            owning,
            decl.ty.is_raw_ptr(),
            self.mutable_pointers[local],
            &site,
        );
        (Some(chosen), conflict)
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct SigDecision {
    /// None means no change
    pub input_decs: Vec<Option<PtrKind>>,
    pub output_dec: Option<PtrKind>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct SigDecisions {
    pub data: FxHashMap<LocalDefId, SigDecision>,
    pub conflicts: Vec<DecisionConflict>,
}

impl SigDecisions {
    pub fn new(rust_program: &RustProgram, analysis: &Analysis) -> Self {
        let mut data = FxHashMap::default();
        data.reserve(rust_program.functions.len());
        let mut conflicts = Vec::new();

        // do not change function signatures that are used as function pointers
        let fn_ptrs = collect_fn_ptrs(rust_program);

        for did in rust_program.functions.iter() {
            if fn_ptrs.contains(did) {
                data.insert(
                    *did,
                    SigDecision {
                        input_decs: vec![
                            None;
                            rust_program
                                .tcx
                                .fn_sig(*did)
                                .skip_binder()
                                .inputs()
                                .skip_binder()
                                .len()
                        ],
                        output_dec: None,
                    },
                );
                continue;
            }
            let decision_maker = DecisionMaker::new(analysis, *did, rust_program.tcx);

            let mir_body = rust_program.tcx.mir_drops_elaborated_and_const_checked(*did);
            let body = mir_body.borrow();

            let sig = rust_program.tcx.fn_sig(*did).skip_binder();
            let input_len = sig.inputs().skip_binder().len();

            let aliases = analysis.aliases.get(did);

            let input_decs = body
                .local_decls
                .iter_enumerated()
                .skip(1)
                .take(input_len)
                .map(|(param, param_decl)| {
                    let aliases = aliases.and_then(|aliases| aliases.get(&param));
                    let (dec, conflict) = decision_maker.decide(param, param_decl, aliases);
                    if let Some(conflict) = conflict {
                        conflicts.push(conflict);
                    }
                    dec
                })
                .collect();

            let return_local = Local::from_u32(0);
            let return_decl = &body.local_decls[return_local];
            let return_aliases = aliases.and_then(|a| a.get(&return_local));
            let (output_dec, output_conflict) =
                decision_maker.decide(return_local, return_decl, return_aliases);
            if let Some(conflict) = output_conflict {
                conflicts.push(conflict);
            }
            let output_dec = match output_dec {
                Some(PtrKind::Move(m)) => Some(PtrKind::Move(m)),
                Some(PtrKind::Raw(m)) => Some(PtrKind::Raw(m)),
                _ => None, // no borrow inference for non-raw returns yet
            };

            data.insert(
                *did,
                SigDecision {
                    input_decs,
                    output_dec,
                },
            );
        }
        SigDecisions { data, conflicts }
    }
}
