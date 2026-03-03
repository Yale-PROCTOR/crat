use rustc_ast_pretty::pprust;
use rustc_hash::FxHashMap;
use rustc_index::Idx;
use rustc_middle::ty::{Ty, TyCtxt};
use rustc_span::def_id::{DefId, LocalDefId};

use super::{
    analysis::{UnionAccessField, UnionRead, UnionUses, UnionWrite, analyze},
    callgraph::{
        CondensationGraph, build_union_callgraphs, callgraphs_to_condensation_graphs,
        collect_union_seed_functions,
    },
    reverse_cfg::{ReverseCfgAnalysis, analyze_reaching_writes},
    ty_visit::{collect_local_union_types, collect_union_related_types},
};

pub fn replace_unions(tcx: TyCtxt<'_>, verbose: bool) -> String {
    let krate = utils::ast::expanded_ast(tcx);
    let use_optimized_mir = false;
    let print_mir = true;

    let (union_tys, ty_visitor) = collect_local_union_types(&tcx, verbose);
    let related_types_map = collect_union_related_types(&tcx, &union_tys, &ty_visitor, verbose);
    let seed_functions = collect_union_seed_functions(tcx, &union_tys, verbose);
    let callgraphs = build_union_callgraphs(tcx, &seed_functions, &related_types_map, verbose);
    let condensation_graphs = callgraphs_to_condensation_graphs(&callgraphs);

    if verbose {
        print_condensation_graphs(tcx, &condensation_graphs);
    }

    let union_uses = analyze(
        tcx,
        &condensation_graphs,
        print_mir,
        use_optimized_mir,
        verbose,
    );
    let reaching_writes = analyze_reaching_writes(tcx, &union_uses, &callgraphs, use_optimized_mir);

    if verbose {
        print_reaching_writes(tcx, &union_uses, &reaching_writes);
    }

    let str = pprust::crate_to_string_for_macros(&krate);
    if false {
        println!("\n{str}");
    }
    str
}

fn print_condensation_graphs(
    tcx: TyCtxt<'_>,
    condensation_graphs: &FxHashMap<LocalDefId, CondensationGraph>,
) {
    println!("\nCondensation Graphs:");
    let mut union_tys = condensation_graphs.keys().copied().collect::<Vec<_>>();
    union_tys.sort_by_key(|def_id| tcx.def_path_str(*def_id));
    for union_ty in union_tys {
        if let Some(graph) = condensation_graphs.get(&union_ty) {
            println!("\n{}\n{:?}", tcx.def_path_str(union_ty), graph);
        }
    }
}

fn print_reaching_writes(tcx: TyCtxt<'_>, union_uses: &UnionUses, analysis: &ReverseCfgAnalysis) {
    println!("\nReaching Writes:");
    let mut union_tys = union_uses.uses.keys().copied().collect::<Vec<_>>();
    union_tys.sort_by_key(|def_id| tcx.def_path_str(*def_id));
    let mut overlapping_tys = Vec::new();

    for union_ty in union_tys {
        let Some(type_uses) = union_uses.uses.get(&union_ty) else {
            continue;
        };
        let Some(type_result) = analysis.uses.get(&union_ty) else {
            continue;
        };
        let mut is_overlapping = false;
        println!("\t{}:", def_path_str(tcx, union_ty));

        let mut instances = type_uses.instances.iter().collect::<Vec<_>>();
        instances.sort_by_key(|(instance, _)| instance.root.index());

        for (instance, _) in instances {
            println!(
                "\t\tInstance L{}..=L{}:",
                instance.root.index(),
                instance.end.index()
            );

            let Some(reaching) = type_result.instances.get(instance) else {
                println!("\t\t\t(no reads)");
                continue;
            };

            let mut reads = reaching.iter().collect::<Vec<_>>();
            reads.sort_by_key(|(read, _)| {
                (
                    read.site.def_id.index(),
                    read.site.location.block.index(),
                    read.site.location.statement_index,
                )
            });

            if reads.is_empty() {
                println!("\t\t\t(no reads)");
                continue;
            }

            for (read, writes) in reads {
                let read_field = format_access(tcx, union_ty, read);
                let read_field_ty = union_field_ty(tcx, union_ty, read.field);
                let mut writes = writes.clone();
                writes.sort_by_key(|write| {
                    (
                        write.site.def_id.index(),
                        write.site.location.block.index(),
                        write.site.location.statement_index,
                    )
                });

                let write_sites = writes
                    .into_iter()
                    .map(|write| {
                        if is_overlapping_pair(tcx, union_ty, read, &write) {
                            is_overlapping = true;
                        }
                        format!(
                            "{:?}@{:?}\n\t\t\t\t\tfield:\t{}",
                            write.site.def_id,
                            write.site.location,
                            format_access(tcx, union_ty, &write),
                        )
                    })
                    .collect::<Vec<_>>()
                    .join("\n\t\t\t\t");

                println!(
                    "\t\t\tRead {:?}@{:?}\n\t\t\t\tfield:\t{}",
                    read.site.def_id, read.site.location, read_field
                );
                if let Some(ty) = read_field_ty {
                    println!("\t\t\t\ttype:\t{ty:?}");
                }
                if write_sites.is_empty() {
                    println!("\t\t\t\tWrites:\t(none)");
                } else {
                    println!("\t\t\t\tWrites:\n\t\t\t\t{write_sites}");
                }
            }
        }

        if is_overlapping {
            overlapping_tys.push(union_ty);
        }
    }

    if !overlapping_tys.is_empty() {
        overlapping_tys.sort_by_key(|def_id| tcx.def_path_str(*def_id));
        println!("\noverlapping:");
        for union_ty in overlapping_tys {
            println!("{}", def_path_str(tcx, union_ty));
        }
    }
}

fn def_path_str(tcx: TyCtxt<'_>, def_id: DefId) -> String {
    tcx.def_path_str(def_id)
}

fn format_access(tcx: TyCtxt<'_>, union_ty: DefId, access: &impl HasUnionField) -> String {
    match access.union_field() {
        UnionAccessField::Field(index) => {
            let ty = union_field_ty(tcx, union_ty, access.union_field())
                .map(|ty| format!("{ty:?}"))
                .unwrap_or_else(|| "?".to_string());
            format!("field#{index}\t({ty})")
        }
        UnionAccessField::Top => "top\t(unknown)".to_string(),
    }
}

fn union_field_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    union_ty: DefId,
    field: UnionAccessField,
) -> Option<Ty<'tcx>> {
    let UnionAccessField::Field(index) = field else {
        return None;
    };
    let adt = tcx.adt_def(union_ty);
    let field = adt.all_fields().nth(index)?;
    Some(tcx.type_of(field.did).instantiate_identity())
}

fn is_overlapping_pair<'tcx>(
    tcx: TyCtxt<'tcx>,
    union_ty: DefId,
    read: &UnionRead,
    write: &UnionWrite,
) -> bool {
    let Some(read_ty) = union_field_ty(tcx, union_ty, read.field) else {
        return false;
    };
    let Some(write_ty) = union_field_ty(tcx, union_ty, write.field) else {
        return false;
    };
    read_ty != write_ty
}

trait HasUnionField {
    fn union_field(&self) -> UnionAccessField;
}

impl HasUnionField for UnionRead {
    fn union_field(&self) -> UnionAccessField {
        self.field
    }
}

impl HasUnionField for UnionWrite {
    fn union_field(&self) -> UnionAccessField {
        self.field
    }
}
