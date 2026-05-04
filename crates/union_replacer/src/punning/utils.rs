use std::{fs, path::Path, str::FromStr};

use points_to::andersen;
use rustc_hash::FxHashMap;
use rustc_hir::def::DefKind;
use rustc_middle::{
    mir::{Body, Local, StatementKind, TerminatorKind},
    ty::TyCtxt,
};
use rustc_span::def_id::{DefId, LocalDefId};
use toml_edit::{DocumentMut, Item, Table};

use super::raw_struct::UnionFieldClassification;

pub fn needs_bytemuck<'tcx>(
    punning_tys: &[LocalDefId],
    union_field_classes: &FxHashMap<LocalDefId, Vec<UnionFieldClassification<'tcx>>>,
) -> bool {
    punning_tys.iter().any(|union_ty| {
        union_field_classes
            .get(union_ty)
            .is_some_and(|fields| fields.iter().any(|f| !f.class.is_other()))
    })
}

pub fn with_body<'tcx, R, F: FnOnce(&Body<'tcx>) -> R>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
    f: F,
) -> R {
    let body = tcx.mir_drops_elaborated_and_const_checked(def_id);
    let body: &Body<'_> = &body.borrow();
    f(body)
}

#[derive(Clone, Copy)]
struct LocalLocInfo {
    owner: LocalDefId,
    local: Local,
    root: andersen::Loc,
    end: andersen::Loc,
}

fn build_local_loc_infos(result: &andersen::AnalysisResult) -> Vec<LocalLocInfo> {
    let mut infos = Vec::with_capacity(result.var_nodes.len());
    for ((owner, local), node) in &result.var_nodes {
        let root = node.index;
        let end = result.ends[root];
        infos.push(LocalLocInfo {
            owner: *owner,
            local: *local,
            root,
            end,
        });
    }
    infos
}

fn find_local_loc_info(loc: andersen::Loc, infos: &[LocalLocInfo]) -> Option<LocalLocInfo> {
    infos
        .iter()
        .copied()
        .find(|info| info.root <= loc && loc <= info.end)
}

fn format_target_loc(
    loc: andersen::Loc,
    result: &andersen::AnalysisResult,
    infos: &[LocalLocInfo],
) -> String {
    let end = result.ends[loc];
    if let Some(info) = find_local_loc_info(loc, infos) {
        let owner = info.owner;
        let local = info.local;
        let offset = loc.index() - info.root.index();
        if offset == 0 {
            format!("{owner:?}::{local:?} [L{}..=L{}]", loc.index(), end.index())
        } else {
            format!(
                "{owner:?}::{local:?}+{offset} [L{}..=L{}]",
                loc.index(),
                end.index()
            )
        }
    } else {
        format!("L{}..=L{}", loc.index(), end.index())
    }
}

fn print_local_points_to<'tcx>(
    def_id: LocalDefId,
    body: &Body<'tcx>,
    result: &andersen::AnalysisResult,
    infos: &[LocalLocInfo],
) {
    println!("\tLOCAL MAY-POINTS-TO:");
    for (local, decl) in body.local_decls.iter_enumerated() {
        let Some(node) = result.var_nodes.get(&(def_id, local)) else {
            println!("\t\t{local:?}: {:?} -> no index", decl.ty);
            continue;
        };
        let root = node.index;
        let root_end = result.ends[root];
        let sols = &result.solutions[root];
        if sols.is_empty() {
            println!(
                "\t\t{local:?}: {:?} [L{}..=L{}] -> {{}}",
                decl.ty,
                root.index(),
                root_end.index()
            );
            continue;
        }

        let mut targets = Vec::new();
        for target in sols.iter() {
            targets.push(format_target_loc(target, result, infos));
        }
        println!(
            "\t\t{local:?}: {:?} [L{}..=L{}] -> {{{}}}",
            decl.ty,
            root.index(),
            root_end.index(),
            targets.join(", ")
        );
    }
}

fn print_body<'tcx>(
    def_id: LocalDefId,
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    result: &andersen::AnalysisResult,
    print_mir: bool,
    infos: &[LocalLocInfo],
    func_calls: &mut Vec<DefId>,
) {
    if print_mir {
        let args = body.args_iter().collect::<std::collections::BTreeSet<_>>();
        for (local, decl) in body.local_decls.iter_enumerated() {
            if local == Local::from_usize(0) {
                println!("\tRETURN: {local:?} -> {:?}", decl.ty);
            } else if args.contains(&local) {
                println!("\tARG: {local:?} -> {:?}", decl.ty);
            } else {
                println!("\tLOCAL: {local:?} -> {:?}", decl.ty);
            }
        }
    }
    for (bb, bbd) in body.basic_blocks.iter_enumerated() {
        if print_mir {
            println!("\tBB: {bb:?}");
        }
        for (stmt_idx, stmt) in bbd.statements.iter().enumerate() {
            if print_mir && let StatementKind::Assign(box (place, _)) = &stmt.kind {
                let ty = place.ty(body, tcx).ty;
                println!("\t\tSTMT {stmt_idx}: {stmt:?}\n\t\t{ty:?}\n");
            }
        }
        if print_mir {
            println!("\t\tTERM: {:?}", bbd.terminator().kind);
            if let TerminatorKind::Call {
                func, destination, ..
            } = &bbd.terminator().kind
            {
                let ty = destination.ty(body, tcx).ty;
                println!("\t\t{ty:?}");

                if let Some((func_def_id, _)) = func.const_fn_def() {
                    func_calls.push(func_def_id);
                }
            }
        }
    }
    if print_mir {
        print_local_points_to(def_id, body, result, infos);
    }
}

fn print_local_body<'tcx>(
    def_id: LocalDefId,
    tcx: TyCtxt<'tcx>,
    result: &andersen::AnalysisResult,
    print_mir: bool,
    infos: &[LocalLocInfo],
) -> Option<Vec<DefId>> {
    let mut func_calls = Vec::new();
    if tcx.def_kind(def_id) != DefKind::Fn {
        return None;
    }
    if print_mir {
        println!("\nDEF: {def_id:?}");
    }

    let body = tcx.mir_drops_elaborated_and_const_checked(def_id);
    let body: &Body<'_> = &body.borrow();
    print_body(def_id, tcx, body, result, print_mir, infos, &mut func_calls);

    Some(func_calls)
}

pub fn print_all_local_bodies_with_points_to(tcx: TyCtxt<'_>, result: &andersen::AnalysisResult) {
    let infos = build_local_loc_infos(result);
    for def_id in tcx.hir_body_owners() {
        let _ = print_local_body(def_id, tcx, result, true, &infos);
    }
}

pub fn ensure_bytemuck_with_derive(dir: &Path) {
    let path = dir.join("Cargo.toml");
    let content = fs::read_to_string(&path).unwrap();
    let mut doc = content.parse::<DocumentMut>().unwrap();

    if !doc.as_table().contains_key("dependencies") {
        doc["dependencies"] = Item::Table(Table::new());
    }

    let deps = doc["dependencies"].as_table_mut().unwrap();
    deps["bytemuck"] = Item::from_str(
        r#"{ version = "1.24.0", features = ["derive", "min_const_generics", "must_cast"] }"#,
    )
    .unwrap();

    fs::write(path, doc.to_string()).unwrap();
}
