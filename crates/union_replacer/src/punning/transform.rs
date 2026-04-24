use std::time::Instant;

use rustc_ast::mut_visit::MutVisitor;
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_span::def_id::{DefId, LocalDefId};
use serde::Deserialize;
use utils::ir::AstToHir;

use super::{
    analysis::{UnionUseResult, analyze},
    bytemuck::{BytemuckDeriveVisitor, FieldTypeClass, build_bytemuck_derive_plan},
    callgraph::{build_union_call_contexts, collect_union_seed_functions},
    raw_struct::{
        RawStructVisitor, UnionFieldClassification, UnionUseRewriteVisitor,
        classify_union_field_types,
    },
    reverse_cfg::analyze_reaching_writes,
    ty_visit::{collect_local_union_types, collect_union_related_types},
    utils::needs_bytemuck,
};

#[derive(Debug, Default, Clone, Deserialize)]
pub struct Config {
    pub c_exposed_fns: FxHashSet<String>,
}

#[derive(Debug)]
pub struct TransformationResult {
    pub code: String,
    pub needs_bytemuck: bool,
    pub union_use_stats: (usize, usize, usize),
}

// Time Marker
#[derive(Debug, Clone)]
struct TransformTiming {
    base: Instant,
    marks: Vec<(&'static str, u128)>,
}

impl TransformTiming {
    #[inline]
    fn maybe_new(enabled: bool) -> Option<Self> {
        if !enabled {
            return None;
        }
        Some(Self {
            base: Instant::now(),
            marks: vec![("base", 0)],
        })
    }

    #[inline]
    fn mark(&mut self, label: &'static str) {
        self.marks.push((label, self.base.elapsed().as_millis()));
    }

    fn format_marks(&self) -> String {
        self.marks
            .iter()
            .map(|(label, ms)| format!("{label}:{ms}ms"))
            .collect::<Vec<_>>()
            .join("\n")
    }

    fn mark_ms(&self, label: &str) -> u128 {
        self.marks
            .iter()
            .find_map(|(name, ms)| (*name == label).then_some(*ms))
            .unwrap_or(0)
    }

    fn summary_csv(&self) -> String {
        let before_analysis = self.mark_ms("before_analysis");
        let points_to_done = self.mark_ms("points_to_done");
        let reaching_writes_done = self.mark_ms("reaching_writes_done");
        let analysis_done = self.mark_ms("analysis_done");
        let transform_done = self.mark_ms("transform_done");

        let t1 = points_to_done.saturating_sub(before_analysis);
        let t2 = reaching_writes_done.saturating_sub(points_to_done);
        let t3 = transform_done.saturating_sub(analysis_done);

        format!("{t1},{t2},{t3},{transform_done}")
    }
}

#[inline]
fn record_timing_point(timing: &mut Option<TransformTiming>, label: &'static str) {
    if let Some(timing) = timing.as_mut() {
        timing.mark(label);
    }
}

pub fn replace_unions(tcx: TyCtxt<'_>, verbose: bool, config: &Config) -> TransformationResult {
    let mut krate = utils::ast::expanded_ast(tcx);

    // for debug
    let print_mir = false;
    let verbose_debug = false;
    let print_result = false;

    // Collect union types
    let (union_tys, ty_visitor) = collect_local_union_types(&tcx, verbose_debug);
    let all_local_union_count = union_tys.len();
    if verbose {
        println!("\nLocal unions:");
        if union_tys.is_empty() {
            println!("\t(none)");
        } else {
            for union_ty in &union_tys {
                println!("\t{}", tcx.def_path_str(*union_ty));
            }
        }
    }

    // Classify field types and determine allowed read/write sets
    let mut timing = TransformTiming::maybe_new(print_result);
    let union_field_classes = classify_union_field_types(tcx, &union_tys, verbose_debug);
    let allowed_rw = build_allowed_rw(&union_field_classes);

    // Filter unions to analyze based on the allowed read set
    let analysis_target_tys = union_tys
        .into_iter()
        .filter(|union_ty| {
            if is_nested_union(tcx, *union_ty) {
                return false;
            }
            allowed_rw
                .get(union_ty)
                .is_some_and(|(allowed_reads, _)| !allowed_reads.is_empty())
        })
        .collect::<Vec<_>>();
    let analysis_target_count = analysis_target_tys.len();

    if verbose {
        println!("\nAnalysis target unions:");
        if analysis_target_tys.is_empty() {
            println!("\t(none)");
        } else {
            for union_ty in &analysis_target_tys {
                println!("\t{}", tcx.def_path_str(*union_ty));
            }
        }
    }

    // If there is no union to analyze, early stop
    if analysis_target_tys.is_empty() {
        utils::ast::remove_unnecessary_items_from_ast(&mut krate);
        let code = pprust::crate_to_string_for_macros(&krate);
        record_timing_point(&mut timing, "early_return");
        if print_result {
            print_union_use_stats(all_local_union_count, 0, 0, timing.as_ref());
        }
        return TransformationResult {
            code,
            needs_bytemuck: false,
            union_use_stats: (all_local_union_count, 0, 0),
        };
    }

    // Collect related types and call contexts for the unions to analyze
    let related_types_map =
        collect_union_related_types(&tcx, &analysis_target_tys, &ty_visitor, verbose_debug);
    let seed_functions = collect_union_seed_functions(tcx, &related_types_map, verbose_debug);
    let call_info =
        build_union_call_contexts(tcx, &seed_functions, &related_types_map, verbose_debug);

    record_timing_point(&mut timing, "before_analysis");
    // Analysis Step 1: Union Field Access Identification
    let mut union_uses = analyze(
        tcx,
        &analysis_target_tys,
        &call_info.contexts,
        &call_info.return_locs,
        print_mir,
        verbose_debug,
        &config.c_exposed_fns,
    );
    let _single_syn_unions = single_syntax_field_unions(&mut union_uses);
    record_timing_point(&mut timing, "points_to_done");

    // Analysis Step 2: Safety Condition Checking
    let safety_passed_tys = safety_check(tcx, &union_uses, &allowed_rw);
    if verbose || verbose_debug {
        println!("Safety check passed: {}", safety_passed_tys.len());
    }

    let safety_passed_set = safety_passed_tys
        .iter()
        .map(|union_ty| union_ty.to_def_id())
        .collect::<FxHashSet<_>>();

    // Analysis Step 3: Punning Union Detection
    let reaching_writes =
        analyze_reaching_writes(tcx, &union_uses, &call_info.contexts, &safety_passed_set);
    record_timing_point(&mut timing, "reaching_writes_done");
    let punning_tys = safety_passed_tys
        .into_iter()
        .filter(|union_ty| reaching_writes.punning.contains(&union_ty.to_def_id()))
        .collect::<Vec<_>>();

    let needs_bytemuck = needs_bytemuck(&punning_tys, &union_field_classes);
    // Analysis done
    if verbose || print_result {
        if !punning_tys.is_empty() {
            println!("\npunning:");
            for union_ty in &punning_tys {
                println!("{}", tcx.def_path_str(*union_ty));
            }
        } else {
            println!("\npunning: none");
        }
    }

    // transform the AST
    let ast_to_hir: AstToHir = utils::ast::make_ast_to_hir(&mut krate, tcx);
    // Type Definition Rewriting
    let derive_plan = build_bytemuck_derive_plan(tcx, &punning_tys, &union_field_classes);
    let mut derive_visitor = BytemuckDeriveVisitor::new(tcx, &ast_to_hir, derive_plan);
    derive_visitor.visit_crate(&mut krate);

    // Union Replacement
    let mut raw_struct_visitor =
        RawStructVisitor::new(tcx, &ast_to_hir, &punning_tys, union_field_classes);
    raw_struct_visitor.visit_crate(&mut krate);

    // Expression Rewriting
    let mut use_visitor = UnionUseRewriteVisitor::new(tcx, ast_to_hir, &punning_tys);
    use_visitor.visit_crate(&mut krate);

    utils::ast::remove_unnecessary_items_from_ast(&mut krate);
    record_timing_point(&mut timing, "transform_done");

    let str = pprust::crate_to_string_for_macros(&krate);
    if verbose {
        println!("\n{str}");
    }

    if verbose || print_result {
        print_union_use_stats(
            all_local_union_count,
            analysis_target_count,
            punning_tys.len(),
            timing.as_ref(),
        );
    }

    TransformationResult {
        code: str,
        needs_bytemuck,
        union_use_stats: (
            all_local_union_count,
            analysis_target_count,
            punning_tys.len(),
        ),
    }
}

fn print_union_use_stats(
    benchmark_all_local: usize,
    benchmark_targets: usize,
    punning: usize,
    timing: Option<&TransformTiming>,
) {
    println!("STATS,{benchmark_all_local},{benchmark_targets},{punning}");
    if let Some(timing) = timing {
        println!("{}", timing.format_marks());
        println!("{}", timing.summary_csv());
    }
}

fn single_syntax_field_unions(union_uses: &mut UnionUseResult) -> Vec<DefId> {
    let mut single_syn_unions = Vec::new();
    let syn = &union_uses.syn;
    union_uses.uses.retain(|union_ty, _| {
        let is_single_syntax_field = syn.get(union_ty).is_some_and(|mask| mask.count_ones() == 1);
        if is_single_syntax_field {
            single_syn_unions.push(*union_ty);
        }
        !is_single_syntax_field
    });

    for union_ty in &single_syn_unions {
        union_uses.syn.remove(union_ty);
    }

    single_syn_unions
}

fn is_nested_union(tcx: TyCtxt<'_>, union_ty: LocalDefId) -> bool {
    let ty = tcx.type_of(union_ty).instantiate_identity();
    let mut visited = FxHashSet::default();

    match ty.kind() {
        ty::TyKind::Adt(adt, args) if adt.is_union() => adt
            .all_fields()
            .any(|field| contains_union(tcx, field.ty(tcx, args), &mut visited)),
        _ => false,
    }
}

fn contains_union<'a>(tcx: TyCtxt<'a>, ty: Ty<'a>, visited: &mut FxHashSet<Ty<'a>>) -> bool {
    if !visited.insert(ty) {
        return false;
    }

    match ty.kind() {
        ty::TyKind::Adt(adt, args) => {
            if adt.is_union() {
                return true;
            }
            if !adt.is_struct() {
                return false;
            }
            adt.all_fields()
                .any(|field| contains_union(tcx, field.ty(tcx, args), visited))
        }
        ty::TyKind::Array(elem, _) | ty::TyKind::Slice(elem) => contains_union(tcx, *elem, visited),
        ty::TyKind::Tuple(tys) => tys.iter().any(|elem| contains_union(tcx, elem, visited)),
        _ => false,
    }
}

/// type -> set of fields (allowed_read, allowed_write)
type AllowedPairMap = FxHashMap<LocalDefId, (FxHashSet<usize>, FxHashSet<usize>)>;

fn build_allowed_rw<'tcx>(
    field_classes: &FxHashMap<LocalDefId, Vec<UnionFieldClassification<'tcx>>>,
) -> AllowedPairMap {
    let mut allowed = FxHashMap::default();

    for (&union_ty, fields) in field_classes {
        let mut allowed_read = FxHashSet::default();
        let mut allowed_write = FxHashSet::default();
        for (field_idx, field) in fields.iter().enumerate() {
            match field.class {
                FieldTypeClass::Pod => {
                    allowed_read.insert(field_idx);
                    allowed_write.insert(field_idx);
                }
                FieldTypeClass::AnyBitPattern => {
                    allowed_read.insert(field_idx);
                }
                FieldTypeClass::NoUninit(_) => {
                    allowed_write.insert(field_idx);
                }
                FieldTypeClass::Other => {}
            }
        }
        if !allowed_read.is_empty() || !allowed_write.is_empty() {
            allowed.insert(union_ty, (allowed_read, allowed_write));
        }
    }

    allowed
}

fn filter_syn(fs: &mut FxHashSet<usize>, m: u64) {
    fs.retain(|i| *i < u64::BITS as usize && (m & (1u64 << *i)) != 0);
}

fn merge_filtered_union_fields(
    tcx: TyCtxt<'_>,
    union_ty: DefId,
    type_uses: &super::analysis::UnionInstanceMap,
    syn: u64,
) -> (FxHashSet<usize>, FxHashSet<usize>) {
    let mut merged_reads = FxHashSet::default();
    let mut merged_writes = FxHashSet::default();

    for instance_uses in type_uses.instances.values() {
        for read in instance_uses.reads.values().flatten() {
            let mut fields = read.field.to_fields(tcx, union_ty);
            filter_syn(&mut fields, syn);
            merged_reads.extend(fields);
        }

        for write in instance_uses.writes.values().flatten() {
            let mut fields = write.field.to_fields(tcx, union_ty);
            filter_syn(&mut fields, syn);
            merged_writes.extend(fields);
        }
    }

    (merged_reads, merged_writes)
}

fn safety_check(
    tcx: TyCtxt<'_>,
    union_uses: &UnionUseResult,
    allowed_rw: &AllowedPairMap,
) -> Vec<LocalDefId> {
    let mut target_unions = Vec::new();

    for (&union_ty, type_uses) in &union_uses.uses {
        let Some(local_union_ty) = union_ty.as_local() else {
            continue;
        };
        let Some((allowed_reads, allowed_writes)) = allowed_rw.get(&local_union_ty) else {
            continue;
        };

        let syn = union_uses.syn.get(&union_ty).copied().unwrap_or(0);
        let (merged_reads, merged_writes) =
            merge_filtered_union_fields(tcx, union_ty, type_uses, syn);

        if merged_reads.is_subset(allowed_reads) && merged_writes.is_subset(allowed_writes) {
            target_unions.push(local_union_ty);
        }
    }

    target_unions
}
