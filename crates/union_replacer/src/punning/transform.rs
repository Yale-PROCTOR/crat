use rustc_ast::mut_visit::MutVisitor;
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_span::def_id::LocalDefId;
use serde::Deserialize;
use utils::ir::AstToHir;

use super::{
    analysis::{UnionUseResult, analyze, union_field_ty},
    bytemuck::{BytemuckDeriveVisitor, FieldTypeClass, build_bytemuck_derive_plan},
    callgraph::{build_union_call_contexts, collect_union_seed_functions},
    raw_struct::{
        RawStructVisitor, UnionFieldClassification, UnionUseRewriteVisitor,
        classify_union_field_types,
    },
    reverse_cfg::{ReverseCfgResult, analyze_reaching_writes, print_reaching_writes},
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

pub fn replace_unions(tcx: TyCtxt<'_>, verbose: bool, config: &Config) -> TransformationResult {
    let mut krate = utils::ast::expanded_ast(tcx);

    // for debug
    let print_mir = false;
    let verbose_debug = false;
    let print_result = true;

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
        if print_result {
            print_union_use_stats(all_local_union_count, 0, 0);
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
    let call_contexts =
        build_union_call_contexts(tcx, &seed_functions, &related_types_map, verbose_debug);

    // Analyze union uses and detect overlapping unions
    let union_uses = analyze(
        tcx,
        &analysis_target_tys,
        &call_contexts,
        print_mir,
        verbose_debug,
        &config.c_exposed_fns,
    );
    let reaching_writes = analyze_reaching_writes(tcx, &union_uses, &call_contexts);
    if verbose_debug {
        print_reaching_writes(tcx, &union_uses, &reaching_writes);
    }
    let overlapping_tys = determine_overlapping_unions(
        tcx,
        &union_uses,
        &reaching_writes,
        &allowed_rw,
        verbose_debug,
    );
    let needs_bytemuck = needs_bytemuck(&overlapping_tys, &union_field_classes);

    // Analysis done
    if verbose || print_result {
        if !overlapping_tys.is_empty() {
            println!("\noverlapping:");
            for union_ty in &overlapping_tys {
                println!("{}", tcx.def_path_str(*union_ty));
            }
        } else {
            println!("\noverlapping: none");
        }
    }

    // transform the AST
    let ast_to_hir: AstToHir = utils::ast::make_ast_to_hir(&mut krate, tcx);

    // Step 1: derive bytemuck traits for user-defined field types
    let derive_plan = build_bytemuck_derive_plan(tcx, &overlapping_tys, &union_field_classes);
    if !derive_plan.per_type.is_empty() {
        krate
            .attrs
            .extend(utils::attr!("#![feature(rt, libstd_sys_internals)]"));
    }
    let mut derive_visitor = BytemuckDeriveVisitor::new(tcx, &ast_to_hir, derive_plan);
    derive_visitor.visit_crate(&mut krate);

    // Step 2: replace unions with raw structs
    let mut raw_struct_visitor =
        RawStructVisitor::new(tcx, &ast_to_hir, &overlapping_tys, union_field_classes);
    raw_struct_visitor.visit_crate(&mut krate);

    // Step 3: update union uses
    let mut use_visitor = UnionUseRewriteVisitor::new(tcx, ast_to_hir, &overlapping_tys);
    use_visitor.visit_crate(&mut krate);

    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

    let str = pprust::crate_to_string_for_macros(&krate);
    if verbose {
        println!("\n{str}");
    }

    if verbose || print_result {
        print_union_use_stats(
            all_local_union_count,
            analysis_target_count,
            overlapping_tys.len(),
        );
    }

    TransformationResult {
        code: str,
        needs_bytemuck,
        union_use_stats: (
            all_local_union_count,
            analysis_target_count,
            overlapping_tys.len(),
        ),
    }
}

fn print_union_use_stats(benchmark_all_local: usize, benchmark_targets: usize, overlapping: usize) {
    println!("STATS,{benchmark_all_local},{benchmark_targets},{overlapping}");
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

fn determine_overlapping_unions(
    tcx: TyCtxt<'_>,
    union_uses: &UnionUseResult,
    reaching_writes: &ReverseCfgResult,
    allowed_rw: &AllowedPairMap,
    verbose: bool,
) -> Vec<LocalDefId> {
    let mut target_unions = Vec::new();

    for (&union_ty, type_uses) in &union_uses.uses {
        let Some(local_union_ty) = union_ty.as_local() else {
            continue;
        };
        let Some(union_allowed_pairs) = allowed_rw.get(&local_union_ty) else {
            continue;
        };
        let Some(type_result) = reaching_writes.uses.get(&union_ty) else {
            unreachable!("Writes not found for union: {:?}", union_ty);
        };

        let mut rejected = false;
        let mut saw_allowed_pair = false;
        let mut saw_cross_type_pair = false;

        'instances: for instance in type_uses.instances.keys() {
            let Some(read_to_writes) = type_result.instances.get(instance) else {
                continue;
            };
            for (read, writes) in read_to_writes {
                let read_fields = read.field.to_fields(tcx, union_ty);
                if !read_fields.is_subset(&union_allowed_pairs.0) {
                    rejected = true;
                    break 'instances;
                }

                for write in writes {
                    let write_fields = write.field.to_fields(tcx, union_ty);
                    if !write_fields.is_subset(&union_allowed_pairs.1) {
                        rejected = true;
                        break 'instances;
                    }
                    saw_allowed_pair = true;
                    if has_distinct_type_pair(tcx, union_ty, &write_fields, &read_fields) {
                        saw_cross_type_pair = true;
                    }
                }
            }
        }

        if verbose && rejected {
            println!("\nRejecting {union_ty:?}");
        }

        if !rejected && saw_allowed_pair && saw_cross_type_pair {
            target_unions.push(local_union_ty);
        }
    }

    target_unions
}

fn has_distinct_type_pair(
    tcx: TyCtxt<'_>,
    union_ty: rustc_span::def_id::DefId,
    write_fields: &FxHashSet<usize>,
    read_fields: &FxHashSet<usize>,
) -> bool {
    for &write_idx in write_fields {
        let Some(write_ty) = union_field_ty(
            tcx,
            union_ty,
            super::analysis::UnionAccessField::Field(write_idx),
        ) else {
            continue;
        };
        for &read_idx in read_fields {
            let Some(read_ty) = union_field_ty(
                tcx,
                union_ty,
                super::analysis::UnionAccessField::Field(read_idx),
            ) else {
                continue;
            };
            if write_ty != read_ty {
                return true;
            }
        }
    }
    false
}
