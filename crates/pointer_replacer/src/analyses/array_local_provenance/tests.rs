use points_to::andersen;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{self as hir, ItemKind, OwnerNode, PatKind, intravisit};
use typed_arena::Arena;
use utils::ty_shape;

use super::{
    BaseAdmissibility, BaseId, PfgNode, UnknownReason, analyze_body,
    array_local_provenance_analysis,
};
use crate::{
    analyses::type_qualifier::foster::mutability::mutability_analysis,
    rewriter::array_local_index_rewriter::{
        group_has_rewritable_binding, group_needs_live_base_rewrite,
    },
    utils::rustc::RustProgram,
};

fn build_rust_program(tcx: rustc_middle::ty::TyCtxt<'_>) -> RustProgram<'_> {
    let mut functions = vec![];
    let mut structs = vec![];
    for maybe_owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        match item.kind {
            ItemKind::Fn { .. } => functions.push(item.owner_id.def_id),
            ItemKind::Struct(..) => structs.push(item.owner_id.def_id),
            _ => {}
        }
    }
    RustProgram {
        tcx,
        functions,
        structs,
    }
}

fn collect_bindings(body: &hir::Body<'_>) -> FxHashMap<hir::HirId, String> {
    struct BindingVisitor(FxHashMap<hir::HirId, String>);

    impl<'tcx> intravisit::Visitor<'tcx> for BindingVisitor {
        fn visit_pat(&mut self, pat: &'tcx hir::Pat<'tcx>) {
            if let PatKind::Binding(_, hir_id, ident, _) = pat.kind {
                self.0.insert(hir_id, ident.name.to_string());
            }
            intravisit::walk_pat(self, pat);
        }
    }

    let mut visitor = BindingVisitor(FxHashMap::default());
    intravisit::walk_body(&mut visitor, body);
    visitor.0
}

#[derive(Clone, Debug)]
struct LocalFacts {
    bases: FxHashSet<BaseId>,
    unique: Option<BaseId>,
    unique_non_null: Option<BaseId>,
    admissibility: Option<BaseAdmissibility>,
}

fn run_analysis(code: &str) -> FxHashMap<(String, String), LocalFacts> {
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let rust_program = build_rust_program(tcx);
        let alloc_fns = FxHashSet::default();
        let mut facts = FxHashMap::default();

        for &did in &rust_program.functions {
            let fn_name = tcx.item_name(did.to_def_id()).to_string();
            let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
            let result = analyze_body(tcx, did, &body, &alloc_fns);
            let hir_to_mir = utils::ir::map_thir_to_mir(did, false, tcx);
            let hir_body = tcx.hir_body_owned_by(did);
            let bindings = collect_bindings(hir_body);

            for (hir_id, local) in &hir_to_mir.binding_to_local {
                let Some(var_name) = bindings.get(hir_id) else {
                    continue;
                };
                let bases = result
                    .slot_table
                    .local_head_slot(*local)
                    .and_then(|slot| {
                        result
                            .provenance
                            .reachable_bases
                            .get(&PfgNode::Slot(slot))
                            .cloned()
                    })
                    .unwrap_or_default();
                let unique = result.unique_base_of_local(*local);
                let unique_non_null = result
                    .slot_table
                    .local_head_slot(*local)
                    .and_then(|slot| result.provenance.unique_non_null_base(&PfgNode::Slot(slot)));
                let admissibility = unique
                    .as_ref()
                    .map(|base| result.admissibility_of_base(base));
                facts.insert(
                    (fn_name.clone(), var_name.clone()),
                    LocalFacts {
                        bases,
                        unique,
                        unique_non_null,
                        admissibility,
                    },
                );
            }
        }

        facts
    })
    .unwrap()
}

fn run_interprocedural_analysis(code: &str) -> FxHashMap<(String, String), LocalFacts> {
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let rust_program = build_rust_program(tcx);
        let alloc_fns = FxHashSet::default();
        let results = array_local_provenance_analysis(&rust_program, &alloc_fns);
        let mut facts = FxHashMap::default();

        for &did in &rust_program.functions {
            let fn_name = tcx.item_name(did.to_def_id()).to_string();
            let _body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
            let result = results
                .get(&did)
                .unwrap_or_else(|| panic!("missing provenance result for {fn_name}"));
            let hir_to_mir = utils::ir::map_thir_to_mir(did, false, tcx);
            let hir_body = tcx.hir_body_owned_by(did);
            let bindings = collect_bindings(hir_body);

            for (hir_id, local) in &hir_to_mir.binding_to_local {
                let Some(var_name) = bindings.get(hir_id) else {
                    continue;
                };
                let bases = result
                    .slot_table
                    .local_head_slot(*local)
                    .and_then(|slot| {
                        result
                            .provenance
                            .reachable_bases
                            .get(&PfgNode::Slot(slot))
                            .cloned()
                    })
                    .unwrap_or_default();
                let unique = result.unique_base_of_local(*local);
                let unique_non_null = result
                    .slot_table
                    .local_head_slot(*local)
                    .and_then(|slot| result.provenance.unique_non_null_base(&PfgNode::Slot(slot)));
                let admissibility = unique
                    .as_ref()
                    .map(|base| result.admissibility_of_base(base));
                facts.insert(
                    (fn_name.clone(), var_name.clone()),
                    LocalFacts {
                        bases,
                        unique,
                        unique_non_null,
                        admissibility,
                    },
                );
            }
        }

        facts
    })
    .unwrap()
}

#[derive(Clone, Debug)]
struct RewriteGroupFacts {
    base: BaseId,
    base_name: Option<String>,
    member_names: FxHashSet<String>,
    member_root_names: FxHashSet<String>,
    index_tracked: bool,
    has_rewritable_binding: bool,
    needs_live_base_rewrite: bool,
    kind: &'static str,
    writes_base_binding: bool,
    preserved_call_count: usize,
}

#[derive(Clone, Copy)]
enum RewriteGroupFactMode {
    ReadyOnly,
    Detailed,
}

fn run_rewrite_groups_with_points_to(
    mode: RewriteGroupFactMode,
    code: &str,
) -> FxHashMap<String, Vec<RewriteGroupFacts>> {
    ::utils::compilation::run_compiler_on_str(code, |tcx| {
        let rust_program = build_rust_program(tcx);
        let mutability_result = mutability_analysis(&rust_program);

        let arena = Arena::new();
        let tss = ty_shape::get_ty_shapes(&arena, tcx, false);
        let andersen_config = andersen::Config {
            use_optimized_mir: false,
            c_exposed_fns: FxHashSet::default(),
        };
        let pre_points_to = andersen::pre_analyze(&andersen_config, &tss, tcx);
        let alloc_fns = pre_points_to.alloc_fns.clone();
        let solutions = andersen::analyze(&andersen_config, &pre_points_to, &tss, tcx);
        let points_to =
            andersen::post_analyze(&andersen_config, pre_points_to, solutions, &tss, tcx);
        let results = array_local_provenance_analysis(&rust_program, &alloc_fns);

        let mut facts = FxHashMap::default();
        for &did in &rust_program.functions {
            let fn_name = tcx.item_name(did.to_def_id()).to_string();
            let body = tcx.mir_drops_elaborated_and_const_checked(did).borrow();
            let result = &results[&did];
            let context = super::RewriteSelectionContext {
                tcx,
                points_to: &points_to,
            };
            let statuses = match mode {
                RewriteGroupFactMode::ReadyOnly => {
                    super::select_rewrite_groups(result, &body, &mutability_result, did, context)
                        .into_iter()
                        .map(super::RewriteGroupStatus::Ready)
                        .collect()
                }
                RewriteGroupFactMode::Detailed => {
                    super::classify_rewrite_groups(result, &body, &mutability_result, did, context)
                }
            };

            let mut local_names: FxHashMap<rustc_middle::mir::Local, String> = FxHashMap::default();
            for dbg in &body.var_debug_info {
                if let rustc_middle::mir::VarDebugInfoContents::Place(place) = &dbg.value
                    && let Some(local) = place.as_local()
                {
                    local_names.entry(local).or_insert(dbg.name.to_string());
                }
            }

            let status_facts = statuses
                .into_iter()
                .map(|status| {
                    let (group, kind, writes_base_binding, preserved_call_count) = match status {
                        super::RewriteGroupStatus::Ready(group) => (group, "ready", false, 0),
                        super::RewriteGroupStatus::PreservedAcrossCalls { group, calls } => (
                            group,
                            "preserved_across_calls",
                            calls.iter().any(|call| call.writes_base_binding),
                            calls.len(),
                        ),
                    };
                    let has_rewritable_binding =
                        group_has_rewritable_binding(tcx, did, &body, result, &group);
                    let needs_live_base_rewrite = group_needs_live_base_rewrite(result, &group);
                    let member_names = group
                        .members
                        .iter()
                        .filter_map(|slot| {
                            let info = &result.slot_table.slot_infos[*slot];
                            super::source_var_identity_for_slot(tcx, &body, &local_names, info)
                        })
                        .collect();
                    let member_root_names = group
                        .members
                        .iter()
                        .filter_map(|slot| {
                            let info = &result.slot_table.slot_infos[*slot];
                            local_names.get(&info.root).cloned()
                        })
                        .collect();
                    let base_name = super::base_slot_info(result, &group)
                        .and_then(|info| {
                            super::source_var_identity_for_slot(tcx, &body, &local_names, info)
                        })
                        .or_else(|| local_names.get(&group.base_local).cloned());
                    RewriteGroupFacts {
                        base: group.base,
                        base_name,
                        member_names,
                        member_root_names,
                        kind,
                        index_tracked: group.index_tracked,
                        has_rewritable_binding,
                        needs_live_base_rewrite,
                        writes_base_binding,
                        preserved_call_count,
                    }
                })
                .collect();
            facts.insert(fn_name, status_facts);
        }

        facts
    })
    .unwrap()
}

fn facts<'a>(
    map: &'a FxHashMap<(String, String), LocalFacts>,
    fn_name: &str,
    var_name: &str,
) -> &'a LocalFacts {
    map.get(&(fn_name.to_string(), var_name.to_string()))
        .unwrap_or_else(|| panic!("missing facts for {fn_name}::{var_name}: {map:#?}"))
}

fn assert_unique_param(fact: &LocalFacts) {
    assert!(
        matches!(fact.unique, Some(BaseId::Param { .. })),
        "expected unique param base, got {fact:#?}"
    );
    assert_eq!(
        fact.admissibility,
        Some(BaseAdmissibility::DirectlyRewriteable)
    );
}

fn assert_has_only_nulltransparent_base(fact: &LocalFacts, expected: &BaseId) {
    let non_null_bases: Vec<_> = fact
        .bases
        .iter()
        .filter(|base| {
            !matches!(
                base,
                BaseId::Unknown {
                    reason: UnknownReason::NullLike,
                    ..
                }
            )
        })
        .collect();
    assert_eq!(
        non_null_bases,
        vec![expected],
        "expected exactly one non-null base {expected:?}, got {fact:#?}"
    );
}

#[test]
fn array_local_provenance_rewrite_groups_select_immutable_param_aliases() {
    let map = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::ReadyOnly,
        r#"
        pub unsafe fn f(p: *mut i32, i: usize) {
            let q = p.add(i);
            let r = q.add(1);
            let _ = (*q, *r);
        }
        "#,
    );

    let groups = map
        .get("f")
        .unwrap_or_else(|| panic!("missing f: {map:#?}"));
    assert!(
        groups.iter().any(|group| {
            matches!(group.base, BaseId::Param { .. })
                && group.base_name.as_deref() == Some("p")
                && group.member_names.contains("q")
                && group.member_names.contains("r")
        }),
        "expected Param rewrite group containing q and r: {groups:#?}"
    );
}

#[test]
fn classify_rewrite_groups_marks_cjson_calls_as_preserved() {
    let statuses = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::Detailed,
        r#"
        pub unsafe fn advance(input: &mut *mut i8) {
            *input = (*input).add(1);
        }

        pub unsafe fn minify(input: &mut *mut i8, output: &mut *mut i8) {
            *input = (*input).add(1);
            *output = (*output).add(1);
        }

        pub unsafe fn f(mut json: *mut i8) {
            let mut into = json;
            advance(&mut json);
            minify(&mut json, &mut into);
            let _ = (*json, *into);
        }
        "#,
    );

    let status = statuses["f"]
        .iter()
        .find(|status| {
            status.base_name.as_deref() == Some("json") && status.member_names.contains("into")
        })
        .expect("expected json/into candidate");
    assert_eq!(status.kind, "preserved_across_calls");
    assert!(status.writes_base_binding);
    assert_eq!(status.preserved_call_count, 2);
}

#[test]
fn classify_rewrite_groups_marks_member_only_call_as_preserved() {
    let statuses = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::Detailed,
        r#"
        pub unsafe fn advance(input: &mut *mut i32) {
            *input = (*input).add(1);
        }

        pub unsafe fn f(p: *mut i32) {
            let mut q = p;
            let r = p.add(1);
            advance(&mut q);
            let _ = (*p, *q, *r);
        }
        "#,
    );

    let status = statuses["f"]
        .iter()
        .find(|status| {
            status.base_name.as_deref() == Some("p")
                && status.member_names.contains("q")
                && status.member_names.contains("r")
        })
        .expect("expected p/q/r candidate");
    assert_eq!(status.kind, "preserved_across_calls");
    assert!(!status.writes_base_binding);
    assert_eq!(status.preserved_call_count, 1);
}

#[test]
fn classify_rewrite_groups_accepts_same_base_cross_argument_flow() {
    let statuses = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::Detailed,
        r#"
        pub unsafe fn copy_cursor(input: &mut *mut i32, output: &mut *mut i32) {
            *output = *input;
        }

        pub unsafe fn f(mut p: *mut i32) {
            let mut q = p.add(1);
            let r = p.add(2);
            copy_cursor(&mut p, &mut q);
            let _ = (*p, *q, *r);
        }
        "#,
    );

    let status = statuses["f"]
        .iter()
        .find(|status| {
            status.base_name.as_deref() == Some("p")
                && status.member_names.contains("q")
                && status.member_names.contains("r")
        })
        .expect("expected same-base cross-argument candidate");
    assert_eq!(status.kind, "preserved_across_calls");
    assert!(!status.writes_base_binding);
}

#[test]
fn classify_rewrite_groups_rejects_different_base_cross_argument_flow() {
    let statuses = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::Detailed,
        r#"
        pub unsafe fn copy_cursor(input: &mut *mut i32, output: &mut *mut i32) {
            *output = *input;
        }

        pub unsafe fn f(mut p: *mut i32, mut other: *mut i32) {
            let q = p.add(1);
            copy_cursor(&mut other, &mut p);
            let r = q.add(1);
            let _ = (*p, *q, *r);
        }
        "#,
    );

    assert!(
        !statuses["f"].iter().any(|status| {
            status.base_name.as_deref() == Some("p")
                && status.member_names.contains("q")
                && status.member_names.contains("r")
        }),
        "{:#?}",
        statuses["f"]
    );
}

#[test]
fn classify_rewrite_groups_rejects_summarized_unknown_write() {
    let statuses = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::Detailed,
        r#"
        unsafe extern "C" {
            fn touch(input: *mut *mut i32);
        }

        pub unsafe fn helper(input: &mut *mut i32) {
            touch(input);
        }

        pub unsafe fn f(mut p: *mut i32) {
            let q = p.add(1);
            helper(&mut p);
            let r = q.add(1);
            let _ = (*p, *q, *r);
        }
        "#,
    );

    assert!(
        !statuses["f"].iter().any(|status| {
            status.base_name.as_deref() == Some("p")
                && status.member_names.contains("q")
                && status.member_names.contains("r")
        }),
        "{:#?}",
        statuses["f"]
    );
}

#[test]
fn classify_rewrite_groups_keeps_direct_assignment_ready() {
    let statuses = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::Detailed,
        r#"
        pub unsafe fn f(mut p: *mut i32) {
            let q = p.add(1);
            p = p.add(2);
            let r = q.add(1);
            let _ = (*p, *q, *r);
        }
        "#,
    );

    let status = statuses["f"]
        .iter()
        .find(|status| {
            status.base_name.as_deref() == Some("p")
                && status.member_names.contains("q")
                && status.member_names.contains("r")
        })
        .expect("expected direct-assignment candidate");
    assert_eq!(status.kind, "ready");
    assert!(status.index_tracked);
}

#[test]
fn select_rewrite_groups_excludes_preserved_call_groups() {
    let groups = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::ReadyOnly,
        r#"
        pub unsafe fn advance(input: &mut *mut i32) {
            *input = (*input).add(1);
        }

        pub unsafe fn f(mut p: *mut i32) {
            let q = p;
            advance(&mut p);
            let _ = (*p, *q);
        }
        "#,
    );

    assert!(groups["f"].is_empty(), "{:#?}", groups["f"]);
}

#[test]
fn select_rewrite_groups_accepts_mut_param_when_base_is_not_reassigned() {
    let groups = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::ReadyOnly,
        r#"
        pub unsafe fn f(mut p: *mut i32, i: usize) {
            let q = p.add(i);
            let r = q.add(1);
            let _ = (*q, *r);
        }
        "#,
    );

    let f_groups = groups.get("f").unwrap();
    assert!(
        f_groups.iter().any(|group| {
            matches!(group.base, BaseId::Param { .. })
                && group.member_names.contains("q")
                && group.member_names.contains("r")
        }),
        "mut Param base should be accepted when no base storage write occurs: {f_groups:#?}"
    );
}

#[test]
fn select_rewrite_groups_selects_as_index_tracked_when_param_directly_reassigned_while_member_live()
{
    let groups = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::ReadyOnly,
        r#"
        pub unsafe fn f(mut p: *mut i32, i: usize) {
            let q = p.add(i);
            p = p.add(1);
            let r = q.add(1);
            let _ = (*q, *r);
        }
        "#,
    );

    let f_groups = groups.get("f").unwrap();
    assert!(
        f_groups.iter().any(|group| {
            matches!(group.base, BaseId::Param { .. })
                && group.index_tracked
                && group.member_names.contains("q")
                && group.member_names.contains("r")
        }),
        "Param base with direct-only reassignment while member is live must be selected as index_tracked: {f_groups:#?}"
    );
}

#[test]
fn select_rewrite_groups_index_tracked_when_named_aggregate_member_live_after_direct_param_reassign()
 {
    let groups = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::ReadyOnly,
        r#"
        pub struct Holder { pub ptr: *mut i32 }

        pub unsafe fn f(mut p: *mut i32, i: usize) {
            let q = p.add(i);
            let m = p.add(2);
            let mut h = Holder { ptr: core::ptr::null_mut() };
            h.ptr = q;
            let _ = m;
            p = p.add(1);
            let keep = h.ptr;
            let _ = keep;
        }
        "#,
    );

    let f_groups = groups.get("f").unwrap();
    assert!(
        f_groups.iter().any(|group| {
            matches!(group.base, BaseId::Param { .. })
                && group.index_tracked
                && group.member_names.contains("q")
                && group.member_root_names.contains("h")
        }),
        "direct-only p reassignment while h holds a derived pointer must produce index_tracked group: {f_groups:#?}"
    );
}

#[test]
fn select_rewrite_groups_rejects_mut_param_written_through_pointer_to_param() {
    let groups = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::ReadyOnly,
        r#"
        pub unsafe fn f(mut p: *mut i32, i: usize) {
            let pp = &raw mut p;
            let q = p.add(i);
            *pp = p.add(1);
            let r = q.add(1);
            let _ = (*q, *r);
        }
        "#,
    );

    let f_groups = groups.get("f").unwrap();
    assert!(
        !f_groups.iter().any(|group| {
            matches!(group.base, BaseId::Param { .. })
                && group.member_names.contains("q")
                && group.member_names.contains("r")
        }),
        "Param base must be rejected when *pp may write p while q is live: {f_groups:#?}"
    );
}

#[test]
fn select_rewrite_groups_rejects_param_when_call_may_write_base_storage() {
    let groups = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::ReadyOnly,
        r#"
        unsafe extern "C" {
            fn touch(slot: *mut *mut i32);
        }

        pub unsafe fn f(mut p: *mut i32, i: usize) {
            let pp = &raw mut p;
            let q = p.add(i);
            touch(pp);
            let r = q.add(1);
            let _ = (*r);
        }
        "#,
    );

    let f_groups = groups.get("f").unwrap();
    assert!(
        !f_groups.iter().any(|group| {
            matches!(group.base, BaseId::Param { .. }) && group.member_names.contains("q")
        }),
        "extern call through pp may mutate p while q is live, so Param group must be rejected: {f_groups:#?}"
    );
}

#[test]
fn select_rewrite_groups_rejects_param_when_by_value_aggregate_call_arg_contains_base_pointer() {
    let groups = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::ReadyOnly,
        r#"
        pub struct Holder {
            pub other: *mut i32,
            pub pp: *mut *mut i32,
        }

        unsafe extern "C" {
            fn touch_holder(holder: Holder);
        }

        pub unsafe fn f(mut p: *mut i32, i: usize) {
            let holder = Holder {
                other: 0 as *mut i32,
                pp: &raw mut p,
            };
            let q = p.add(i);
            touch_holder(holder);
            let r = q.add(1);
            let _ = *r;
        }
        "#,
    );

    let f_groups = groups.get("f").unwrap();
    assert!(
        !f_groups.iter().any(|group| {
            matches!(group.base, BaseId::Param { .. }) && group.member_names.contains("q")
        }),
        "by-value aggregate call arg contains pointer to p storage while q is live: {f_groups:#?}"
    );
}

#[test]
fn select_rewrite_groups_rejects_param_when_projected_call_arg_may_write_base_storage() {
    let groups = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::ReadyOnly,
        r#"
        pub struct Holder {
            pub pp: *mut *mut i32,
        }

        unsafe extern "C" {
            fn touch(slot: *mut *mut i32);
        }

        pub unsafe fn f(mut p: *mut i32, i: usize) {
            let holder = Holder { pp: &raw mut p };
            let q = p.add(i);
            touch(holder.pp);
            let r = q.add(1);
            let _ = (*r);
        }
        "#,
    );

    let f_groups = groups.get("f").unwrap();
    assert!(
        !f_groups.iter().any(|group| {
            matches!(group.base, BaseId::Param { .. }) && group.member_names.contains("q")
        }),
        "extern call through holder.pp may mutate p while q is live, so Param group must be rejected: {f_groups:#?}"
    );
}

#[test]
fn select_rewrite_groups_rejects_param_field_when_call_may_write_parent_aggregate() {
    let groups = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::ReadyOnly,
        r#"
        pub struct Pair {
            pub a: *mut i32,
            pub b: *mut i32,
        }

        unsafe extern "C" {
            fn touch_pair(pair: *mut Pair);
        }

        pub unsafe fn f(mut pair: Pair, i: usize) {
            let ppair = &raw mut pair;
            let qb = pair.b.add(i);
            touch_pair(ppair);
            let rb = qb.add(1);
            let _ = *rb;
        }
        "#,
    );

    let f_groups = groups.get("f").unwrap();
    assert!(
        !f_groups.iter().any(|group| {
            matches!(group.base, BaseId::Param { .. }) && group.member_names.contains("qb")
        }),
        "call through parent Pair pointer may mutate pair.b while qb is live: {f_groups:#?}"
    );
}

#[test]
fn select_rewrite_groups_rejects_mut_param_field_written_through_pointer_to_field() {
    let groups = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::ReadyOnly,
        r#"
        pub struct S { pub n: i32, pub p: *mut i32 }

        pub unsafe fn f(mut s: S, i: usize) {
            let pp = &raw mut s.p;
            let q = s.p.add(i);
            *pp = s.p.add(1);
            let r = q.add(1);
            let _ = (*q, *r);
        }
        "#,
    );

    let f_groups = groups.get("f").unwrap();
    assert!(
        !f_groups.iter().any(|group| {
            matches!(group.base, BaseId::Param { .. })
                && group.member_names.contains("q")
                && group.member_names.contains("r")
        }),
        "Param field base must be rejected when *pp may write s.p while q is live: {f_groups:#?}"
    );
}

#[test]
fn select_rewrite_groups_rejects_pointee_param_base_written_through_alias() {
    let groups = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::ReadyOnly,
        r#"
        pub unsafe fn f(p: *mut *mut i32, replacement: *mut i32, i: usize) {
            let pp = p;
            let q = (*p).add(i);
            *pp = replacement;
            let r = q.add(1);
            let _ = (*q, *r);
        }
        "#,
    );

    let f_groups = groups.get("f").unwrap();
    assert!(
        !f_groups.iter().any(|group| {
            matches!(group.base, BaseId::Param { .. })
                && group.member_names.contains("q")
                && group.member_names.contains("r")
        }),
        "Param pointee base must be rejected when an alias writes *p while q is live: {f_groups:#?}"
    );
}

#[test]
fn select_rewrite_groups_index_tracked_for_mutated_struct_param_field() {
    let groups = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::ReadyOnly,
        r#"
        pub struct Pair {
            pub a: *mut i32,
            pub b: *mut i32,
        }

        pub unsafe fn f(mut pair: Pair, i: usize) {
            let qa = pair.a.add(i);
            let qb = pair.b.add(i);
            pair.a = pair.a.add(1);
            let ra = qa.add(1);
            let rb = qb.add(1);
            let _ = (*ra, *rb);
        }
        "#,
    );

    let f_groups = groups.get("f").unwrap();
    assert!(
        f_groups
            .iter()
            .any(|group| group.index_tracked && group.member_names.contains("qa")),
        "group for pair.a should be selected as index_tracked after direct field reassignment: {f_groups:#?}"
    );
    assert!(
        f_groups
            .iter()
            .any(|group| group.member_names.contains("qb")),
        "group for pair.b should remain selectable when only pair.a is reassigned: {f_groups:#?}"
    );
}

#[test]
fn select_rewrite_groups_live_is_null_does_not_destabilize_state_buffer_base() {
    let code = r#"
        pub struct State {
            pub buffer: *mut core::ffi::c_char,
        }

        unsafe extern "C" {
            fn memchr(
                s: *const core::ffi::c_void,
                c: i32,
                n: usize,
            ) -> *mut core::ffi::c_void;
        }

        pub unsafe fn f(state: *mut State, target: core::ffi::c_char, remaining: usize) {
            let mut ptr: *mut core::ffi::c_char = (*state).buffer;
            if state.is_null() {
                let _ = ptr;
            }
            let found: *mut core::ffi::c_char = memchr(
                ptr as *const core::ffi::c_void,
                target as i32,
                remaining,
            ) as *mut core::ffi::c_char;
            ptr = found.offset(1 as core::ffi::c_int as isize);
            let _ = ptr;
        }
        "#;
    let groups = run_rewrite_groups_with_points_to(RewriteGroupFactMode::ReadyOnly, code);

    let facts = groups.get("f").expect("missing facts for f");
    let _group = facts
        .iter()
        .find(|fact| {
            fact.member_names.contains("ptr") && fact.member_names.contains("state.buffer")
        })
        .unwrap_or_else(|| {
            panic!("expected rewrite group containing ptr and state.buffer, got {facts:#?}")
        });
}

#[test]
fn select_rewrite_groups_counts_named_local_field_as_source_var() {
    let groups = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::ReadyOnly,
        r#"
        pub struct Holder {
            pub ptr: *mut i32,
        }

        pub unsafe fn f(p: *mut i32) {
            let mut holder = Holder { ptr: core::ptr::null_mut() };
            holder.ptr = p;
            let mut q = holder.ptr;
            let _ = q;
        }
        "#,
    );

    let facts = groups.get("f").expect("missing facts for f");
    let _group = facts
        .iter()
        .find(|fact| fact.member_names.contains("q") && fact.member_names.contains("holder.ptr"))
        .unwrap_or_else(|| {
            panic!("expected rewrite group containing q and holder.ptr, got {facts:#?}")
        });
}

#[test]
fn select_rewrite_groups_does_not_count_array_element_as_source_var() {
    let groups = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::ReadyOnly,
        r#"
        pub unsafe fn f(p: *mut i32) {
            let mut slots = [core::ptr::null_mut()];
            slots[0] = p;
            let q = slots[0];
            let r = q.offset(1);
            let _ = (*q, *r);
        }
        "#,
    );

    let facts = groups.get("f").expect("missing facts for f");
    let group = facts
        .iter()
        .find(|fact| {
            (fact.member_names.contains("q") || fact.member_root_names.contains("q"))
                && fact.member_root_names.contains("slots")
        })
        .unwrap_or_else(|| {
            panic!("expected rewrite group involving q and slots root, got {facts:#?}")
        });

    assert!(
        !group.member_names.contains("slots"),
        "array element should not be counted as a named source var: {facts:#?}"
    );
    assert!(
        !group.member_names.contains("slots.0"),
        "array element should not be counted as a named source var: {facts:#?}"
    );
}

#[test]
fn select_rewrite_groups_does_not_count_tuple_field_as_source_var() {
    let groups = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::ReadyOnly,
        r#"
        pub unsafe fn f(p: *mut i32) {
            let mut pair = (core::ptr::null_mut(), 1i32);
            pair.0 = p;
            let q = pair.0;
            let r = q.offset(1);
            let _ = (*q, *r);
        }
        "#,
    );

    let facts = groups.get("f").expect("missing facts for f");
    let group = facts
        .iter()
        .find(|fact| {
            (fact.member_names.contains("q") || fact.member_root_names.contains("q"))
                && fact.member_root_names.contains("pair")
        })
        .unwrap_or_else(|| {
            panic!("expected rewrite group involving q and pair root, got {facts:#?}")
        });

    assert!(
        !group.member_names.contains("pair"),
        "tuple field should not be counted as a named source var: {facts:#?}"
    );
    assert!(
        !group.member_names.contains("pair.0"),
        "tuple field should not be counted as a named source var: {facts:#?}"
    );
}

#[test]
fn select_rewrite_groups_accepts_mut_param_reassigned_before_members_exist() {
    let groups = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::ReadyOnly,
        r#"
        pub unsafe fn f(mut p: *mut i32, i: usize) {
            p = p.add(1);
            let q = p.add(i);
            let r = q.add(1);
            let _ = (*q, *r);
        }
        "#,
    );

    let f_groups = groups.get("f").unwrap();
    assert!(
        f_groups.iter().any(|group| {
            matches!(group.base, BaseId::Param { .. })
                && group.member_names.contains("q")
                && group.member_names.contains("r")
        }),
        "Param base reassignment before q/r are live should not reject the group: {f_groups:#?}"
    );
}

#[test]
fn array_local_provenance_rewrite_groups_select_local_array_base() {
    let map = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::ReadyOnly,
        r#"
        pub unsafe fn f(i: usize) {
            let mut arr = [0_i32; 4];
            let p = arr.as_mut_ptr();
            let q = p.add(i);
            let r = q.add(1);
            let _ = (*q, *r);
        }
        "#,
    );

    let groups = map
        .get("f")
        .unwrap_or_else(|| panic!("missing f: {map:#?}"));
    assert!(
        groups.iter().any(|group| {
            matches!(group.base, BaseId::LocalArray { .. })
                && group.base_name.as_deref() == Some("arr")
                && group.member_names.contains("p")
                && group.member_names.contains("q")
                && group.member_names.contains("r")
        }),
        "local-array base should be accepted for rewrite selection: {groups:#?}"
    );
}

#[test]
fn array_local_provenance_param_flows_through_copy_and_arithmetic() {
    let map = run_analysis(
        r#"
        pub unsafe fn f(p: *mut i32, i: usize) {
            let q = p;
            let r = q.add(i);
            let s = r.sub(1);
            let _ = *s;
        }
        "#,
    );

    let s = facts(&map, "f", "s");
    assert!(matches!(s.unique, Some(BaseId::Param { .. })));
    assert_eq!(
        s.admissibility,
        Some(BaseAdmissibility::DirectlyRewriteable)
    );
}

#[test]
fn array_local_provenance_int_cast_is_unique_but_rejected() {
    let map = run_analysis(
        r#"
        pub unsafe fn f(addr: usize) {
            let p = addr as *mut i32;
            let _ = p;
        }
        "#,
    );

    let p = facts(&map, "f", "p");
    assert!(matches!(p.unique, Some(BaseId::IntToPtr { .. })));
    assert_eq!(p.admissibility, Some(BaseAdmissibility::Reject));
}

#[test]
fn array_local_provenance_join_from_two_params_is_not_unique() {
    let map = run_analysis(
        r#"
        pub unsafe fn f(p: *mut i32, r: *mut i32, cond: bool) {
            let q;
            if cond {
                q = p;
            } else {
                q = r;
            }
            let _ = q;
        }
        "#,
    );

    let q = facts(&map, "f", "q");
    assert_eq!(q.bases.len(), 2);
    assert!(q.unique.is_none());
}

#[test]
fn array_local_provenance_raw_borrow_of_scalar_is_directly_rewriteable() {
    let map = run_analysis(
        r#"
        pub unsafe fn f() {
            let mut x = 0_i32;
            let p = &raw mut x;
            let _ = *p;
        }
        "#,
    );

    let p = facts(&map, "f", "p");
    assert!(matches!(p.unique, Some(BaseId::LocalScalar { .. })));
    assert_eq!(
        p.admissibility,
        Some(BaseAdmissibility::DirectlyRewriteable)
    );
}

#[test]
fn array_local_provenance_unknown_pointer_return_is_track_only() {
    let map = run_analysis(
        r#"
        unsafe extern "C" {
            fn make() -> *mut i32;
        }

        pub unsafe fn f() {
            let p = make();
            let _ = p;
        }
        "#,
    );

    let p = facts(&map, "f", "p");
    assert!(matches!(p.unique, Some(BaseId::OpaqueReturn { .. })));
    assert_eq!(p.admissibility, Some(BaseAdmissibility::TrackOnly));
}

#[test]
fn array_local_provenance_simple_field_store_and_load_preserves_base() {
    let map = run_analysis(
        r#"
        pub struct Slot {
            pub p: *mut i32,
        }

        pub unsafe fn f(p: *mut i32) {
            let mut s = Slot { p: core::ptr::null_mut() };
            s.p = p;
            let q = s.p;
            let _ = q;
        }
        "#,
    );

    let q = facts(&map, "f", "q");
    assert!(matches!(q.unique, Some(BaseId::Param { .. })));
    assert_eq!(
        q.admissibility,
        Some(BaseAdmissibility::DirectlyRewriteable)
    );
}

#[test]
fn array_local_provenance_field_slots_are_per_local() {
    let map = run_analysis(
        r#"
        pub struct Slot {
            pub p: *mut i32,
        }

        pub unsafe fn f(p: *mut i32, r: *mut i32) {
            let mut s1 = Slot { p: core::ptr::null_mut() };
            let mut s2 = Slot { p: core::ptr::null_mut() };
            s1.p = p;
            s2.p = r;
            let q = s1.p;
            let t = s2.p;
            let _ = (q, t);
        }
        "#,
    );

    let q = facts(&map, "f", "q");
    let t = facts(&map, "f", "t");
    assert_unique_param(q);
    assert_unique_param(t);
    assert_ne!(q.unique, t.unique);
}

#[test]
fn array_local_provenance_array_index_slots_are_collapsed() {
    let map = run_analysis(
        r#"
        pub unsafe fn f(p: *mut i32, i: usize, j: usize) {
            let mut a = [core::ptr::null_mut(); 2];
            a[i & 1] = p;
            let q = a[j & 1];
            let _ = q;
        }
        "#,
    );

    assert_unique_param(facts(&map, "f", "q"));
}

#[test]
fn array_local_provenance_union_field_projection_is_unknown() {
    let map = run_analysis(
        r#"
        pub union U {
            pub p: *mut i32,
            pub n: usize,
        }

        pub unsafe fn f(u: U) {
            let q = u.p;
            let _ = q;
        }
        "#,
    );

    let q = facts(&map, "f", "q");
    assert!(matches!(q.unique, Some(BaseId::Unknown { .. })));
    assert_eq!(q.admissibility, Some(BaseAdmissibility::Reject));
}

#[test]
fn array_local_provenance_raw_address_load_reads_pointer_field() {
    let map = run_analysis(
        r#"
        pub struct Slot {
            pub p: *mut i32,
        }

        pub unsafe fn f(p: *mut i32) {
            let mut s = Slot { p: core::ptr::null_mut() };
            s.p = p;
            let slot = &raw const s.p;
            let q = *slot;
            let _ = q;
        }
        "#,
    );

    let q = facts(&map, "f", "q");
    assert!(matches!(q.unique, Some(BaseId::Param { .. })));
    assert_eq!(
        q.admissibility,
        Some(BaseAdmissibility::DirectlyRewriteable)
    );
}

#[test]
fn array_local_provenance_raw_address_store_updates_pointer_field() {
    let map = run_analysis(
        r#"
        pub struct Slot {
            pub p: *mut i32,
        }

        pub unsafe fn f(p: *mut i32) {
            let mut s = Slot { p: core::ptr::null_mut() };
            let slot = &raw mut s.p;
            *slot = p;
            let q = s.p;
            let _ = q;
        }
        "#,
    );

    let q = facts(&map, "f", "q");
    assert!(matches!(q.unique, Some(BaseId::Param { .. })));
    assert_eq!(
        q.admissibility,
        Some(BaseAdmissibility::DirectlyRewriteable)
    );
}

#[test]
fn array_local_provenance_copied_raw_address_preserves_pointee_slot() {
    let map = run_analysis(
        r#"
        pub struct Slot {
            pub p: *mut i32,
        }

        pub unsafe fn f(p: *mut i32) {
            let mut s = Slot { p: core::ptr::null_mut() };
            let slot = &raw mut s.p;
            let alias = slot;
            *alias = p;
            let q = s.p;
            let _ = q;
        }
        "#,
    );

    let q = facts(&map, "f", "q");
    assert!(matches!(q.unique, Some(BaseId::Param { .. })));
    assert_eq!(
        q.admissibility,
        Some(BaseAdmissibility::DirectlyRewriteable)
    );
}

#[test]
fn array_local_provenance_struct_param_fields_get_distinct_bases() {
    let map = run_analysis(
        r#"
        pub struct Pair {
            pub a: *mut i32,
            pub b: *mut i32,
        }

        pub unsafe fn f(pair: Pair) {
            let q = pair.a;
            let r = pair.b;
            let _ = (q, r);
        }
        "#,
    );

    let q = facts(&map, "f", "q");
    let r = facts(&map, "f", "r");
    assert_unique_param(q);
    assert_unique_param(r);
    assert_ne!(
        q.unique, r.unique,
        "distinct pointer fields must have distinct Param bases"
    );
}

#[test]
fn array_local_provenance_call_invalidates_pointer_fields_through_struct_pointer() {
    let map = run_analysis(
        r#"
        pub struct Slot {
            pub p: *mut i32,
        }

        unsafe extern "C" {
            fn touch(slot: *mut Slot);
        }

        pub unsafe fn f(p: *mut i32) {
            let mut s = Slot { p };
            let slot = &raw mut s;
            touch(slot);
            let q = s.p;
            let _ = q;
        }
        "#,
    );

    let q = facts(&map, "f", "q");
    assert!(
        matches!(q.unique, Some(BaseId::Unknown { .. })),
        "call invalidation should mark the field unknown: {q:#?}"
    );
    assert_eq!(q.admissibility, Some(BaseAdmissibility::Reject));
}

#[test]
fn array_local_provenance_call_returning_struct_fills_all_pointer_slots() {
    // when a function returns a struct that contains pointer fields, every
    // pointer slot in the destination should receive a CallReturn edge so
    // that provenance propagates to all fields, not only the first one.
    let map = run_analysis(
        r#"
        pub struct Pair {
            pub a: *mut i32,
            pub b: *mut i32,
        }

        unsafe extern "C" {
            fn make_pair() -> Pair;
        }

        pub unsafe fn f() {
            let s = make_pair();
            let q = s.a;
            let r = s.b;
            let _ = (q, r);
        }
        "#,
    );

    let q = facts(&map, "f", "q");
    let r = facts(&map, "f", "r");
    assert!(
        matches!(q.unique, Some(BaseId::OpaqueReturn { .. })),
        "s.a should have unique OpaqueReturn base: {q:#?}"
    );
    assert!(
        matches!(r.unique, Some(BaseId::OpaqueReturn { .. })),
        "s.b should have unique OpaqueReturn base: {r:#?}"
    );
    assert_eq!(
        q.admissibility,
        Some(BaseAdmissibility::TrackOnly),
        "OpaqueReturn base must be TrackOnly: {q:#?}"
    );
    assert_eq!(
        r.admissibility,
        Some(BaseAdmissibility::TrackOnly),
        "OpaqueReturn base must be TrackOnly: {r:#?}"
    );
}

#[test]
fn array_local_provenance_call_returning_raw_pointer_non_regression() {
    // `make()` returns `*mut i32` — the destination IS a raw pointer.
    // Both old (is_raw_ptr) and new (place_slots) code must emit one
    // CallReturn(loc) → slot(p) edge so that p has OpaqueReturn provenance.
    let map = run_analysis(
        r#"
        unsafe extern "C" {
            fn make() -> *mut i32;
        }

        pub unsafe fn f() {
            let p = make();
            let q = p;
            let _ = q;
        }
        "#,
    );

    let q = facts(&map, "f", "q");
    assert!(
        matches!(q.unique, Some(BaseId::OpaqueReturn { .. })),
        "call returning *mut i32 must still give OpaqueReturn provenance (AC 2 non-regression): {q:#?}"
    );
    assert_eq!(
        q.admissibility,
        Some(BaseAdmissibility::TrackOnly),
        "OpaqueReturn base must be TrackOnly: {q:#?}"
    );
}

#[test]
fn array_local_provenance_direct_callee_arg_write_preserves_base() {
    let map = run_interprocedural_analysis(
        r#"
        pub unsafe fn helper(src: *mut i32, out: *mut *mut i32) {
            *out = src;
        }

        pub unsafe fn f(p: *mut i32, i: usize) {
            let q = p.add(i);
            let mut into: *mut i32 = core::ptr::null_mut();
            helper(q, &raw mut into);
            let r = into.add(1);
            let _ = (*q, *r);
        }
        "#,
    );

    let q = facts(&map, "f", "q");
    let into = facts(&map, "f", "into");
    let r = facts(&map, "f", "r");
    assert_unique_param(q);
    assert_has_only_nulltransparent_base(into, q.unique.as_ref().unwrap());
    assert_has_only_nulltransparent_base(r, q.unique.as_ref().unwrap());
}

#[test]
fn array_local_provenance_direct_callee_arg_write_from_first_param_cjson_shape() {
    let map = run_interprocedural_analysis(
        r#"
        pub type c_char = i8;

        pub unsafe fn minify_string(src: *mut c_char, out: *mut *mut c_char) {
            *out = src;
        }

        pub unsafe fn cjson_minify(json: *mut c_char) {
            let mut into = json;
            let q = json.add(1);
            minify_string(q, &raw mut into);
            let r = into.add(1);
            let _ = (*q, *r);
        }
        "#,
    );

    let q = facts(&map, "cjson_minify", "q");
    let into = facts(&map, "cjson_minify", "into");
    let r = facts(&map, "cjson_minify", "r");
    assert_unique_param(q);
    assert_eq!(
        into.unique, q.unique,
        "into should keep q/json base: {into:#?}"
    );
    assert_eq!(r.unique, q.unique, "r should keep q/json base: {r:#?}");
}

#[test]
fn array_local_provenance_reference_self_write_preserves_base() {
    let map = run_interprocedural_analysis(
        r#"
        pub unsafe fn advance(input: &mut *mut i32) {
            *input = (*input).add(1);
        }

        pub unsafe fn f(mut p: *mut i32) {
            let q = p;
            advance(&mut p);
            let r = q.add(1);
            let _ = (*p, *q, *r);
        }
        "#,
    );

    let p = facts(&map, "f", "p");
    let q = facts(&map, "f", "q");
    let r = facts(&map, "f", "r");
    assert_unique_param(p);
    assert_eq!(q.unique, p.unique, "{q:#?}");
    assert_eq!(r.unique, p.unique, "{r:#?}");
}

#[test]
fn array_local_provenance_reference_cross_arg_same_base_preserves_base() {
    let map = run_interprocedural_analysis(
        r#"
        pub unsafe fn copy_cursor(input: &mut *mut i32, output: &mut *mut i32) {
            *output = *input;
        }

        pub unsafe fn f(mut p: *mut i32) {
            let mut q = p.add(2);
            copy_cursor(&mut p, &mut q);
            let r = q.add(1);
            let _ = (*p, *q, *r);
        }
        "#,
    );

    let p = facts(&map, "f", "p");
    let q = facts(&map, "f", "q");
    let r = facts(&map, "f", "r");
    assert_unique_param(p);
    assert_eq!(q.unique, p.unique, "{q:#?}");
    assert_eq!(r.unique, p.unique, "{r:#?}");
}

#[test]
fn array_local_provenance_complete_empty_summary_avoids_unknown_fallback() {
    let map = run_interprocedural_analysis(
        r#"
        pub unsafe fn inspect(_input: &mut *mut i32) {}

        pub unsafe fn f(mut p: *mut i32) {
            inspect(&mut p);
            let q = p.add(1);
            let _ = *q;
        }
        "#,
    );

    assert_unique_param(facts(&map, "f", "q"));
}

#[test]
fn array_local_provenance_direct_callee_unknown_arg_write_preserves_direct_param_copy_slot() {
    let map = run_interprocedural_analysis(
        r#"
        unsafe extern "C" {
            fn unknown(out: *mut *mut i32);
        }

        pub unsafe fn helper(out: *mut *mut i32) {
            let alias = out;
            unknown(alias);
        }

        pub unsafe fn f(out: *mut *mut i32) {
            helper(out);
            let q = *out;
            let _ = q;
        }
        "#,
    );

    let q = facts(&map, "f", "q");
    assert!(
        matches!(q.unique, Some(BaseId::Param { .. })),
        "summary fallback should preserve the direct-param base for q: {q:#?}"
    );
    assert!(
        !q.bases.iter().any(|base| {
            matches!(
                base,
                BaseId::Unknown {
                    reason: UnknownReason::UnsupportedMemoryLoad,
                    ..
                }
            )
        }),
        "summary fallback should not add UnsupportedMemoryLoad to q: {q:#?}"
    );
}

#[test]
fn array_local_provenance_direct_callee_unknown_arg_write_uses_summarized_param_index() {
    let map = run_interprocedural_analysis(
        r#"
        unsafe extern "C" {
            fn unknown(out: *mut *mut i32);
        }

        pub unsafe fn helper(scratch: *mut *mut i32, out: *mut *mut i32) {
            let alias = out;
            unknown(alias);
            let _ = scratch;
        }

        pub unsafe fn f(p: *mut i32, out: *mut *mut i32) {
            let mut local = p;
            helper(&raw mut local, out);
            let q = local;
            let r = *out;
            let _ = (q, r);
        }
        "#,
    );

    let local = facts(&map, "f", "local");
    let q = facts(&map, "f", "q");
    let r = facts(&map, "f", "r");

    assert_unique_param(q);
    assert_eq!(
        local.unique, q.unique,
        "wrong unknown-write summary target should not poison local: {local:#?}"
    );
    assert_unique_param(r);
    assert_ne!(r.unique, q.unique, "r should track out, not p: {r:#?}");
    assert!(
        !q.bases.iter().any(|base| {
            matches!(
                base,
                BaseId::Unknown {
                    reason: UnknownReason::UnsupportedMemoryLoad,
                    ..
                }
            )
        }),
        "q should not gain UnsupportedMemoryLoad from the scratch argument: {q:#?}"
    );
}

#[test]
fn array_local_provenance_direct_callee_return_preserves_param_base() {
    let map = run_interprocedural_analysis(
        r#"
        pub unsafe fn advance(p: *mut i32, i: usize) -> *mut i32 {
            p.add(i)
        }

        pub unsafe fn f(p: *mut i32, i: usize) {
            let q = advance(p, i);
            let r = q.add(1);
            let _ = (*q, *r);
        }
        "#,
    );

    let q = facts(&map, "f", "q");
    let r = facts(&map, "f", "r");
    assert_unique_param(q);
    assert_eq!(r.unique, q.unique, "r should keep q's base: {r:#?}");
}

#[test]
fn array_local_provenance_direct_callee_return_through_pointer_arithmetic() {
    let map = run_interprocedural_analysis(
        r#"
        pub unsafe fn advance_twice(p: *mut i32, i: usize) -> *mut i32 {
            let q = p.add(i);
            q.add(1)
        }

        pub unsafe fn f(p: *mut i32, i: usize) {
            let q = advance_twice(p, i);
            let r = q.add(1);
            let _ = (*q, *r);
        }
        "#,
    );

    let q = facts(&map, "f", "q");
    let r = facts(&map, "f", "r");
    assert_unique_param(q);
    assert_eq!(r.unique, q.unique, "r should keep q's base: {r:#?}");
}

#[test]
fn array_local_provenance_extern_call_stays_conservative() {
    let map = run_interprocedural_analysis(
        r#"
        unsafe extern "C" {
            fn helper(src: *mut i32, out: *mut *mut i32);
        }

        pub unsafe fn f(p: *mut i32, i: usize) {
            let q = p.add(i);
            let mut into: *mut i32 = core::ptr::null_mut();
            helper(q, &raw mut into);
            let r = into.add(1);
            let _ = r;
        }
        "#,
    );

    let into = facts(&map, "f", "into");
    assert!(
        !into
            .bases
            .iter()
            .any(|base| matches!(base, BaseId::Param { .. })),
        "unknown callee write should not introduce a param base: {into:#?}"
    );
    assert!(
        into.bases.iter().any(|base| !matches!(
            base,
            BaseId::Unknown {
                reason: UnknownReason::NullLike,
                ..
            }
        )),
        "unknown callee write should keep at least one non-null-like conservative base: {into:#?}"
    );
    assert!(
        into.unique.is_none() || matches!(into.unique, Some(BaseId::Unknown { .. })),
        "extern call should not be trusted as a direct local summary: {into:#?}"
    );
}

#[test]
fn array_local_provenance_direct_callee_unknown_write_stays_rejected() {
    let map = run_interprocedural_analysis(
        r#"
        unsafe extern "C" {
            fn make() -> *mut i32;
        }

        pub unsafe fn helper(out: *mut *mut i32) {
            *out = make();
        }

        pub unsafe fn f(p: *mut i32, i: usize) {
            let q = p.add(i);
            let mut into: *mut i32 = core::ptr::null_mut();
            helper(&raw mut into);
            let r = into.add(1);
            let _ = (q, r);
        }
        "#,
    );

    let into = facts(&map, "f", "into");
    assert!(
        into.unique.is_none() || into.admissibility != Some(BaseAdmissibility::DirectlyRewriteable),
        "unknown callee write should not become rewriteable: {into:#?}"
    );
}

#[test]
fn array_local_provenance_recursive_summary_does_not_panic() {
    let map = run_interprocedural_analysis(
        r#"
        pub unsafe fn rec(p: *mut i32, n: usize) -> *mut i32 {
            if n == 0 {
                p
            } else {
                rec(p.add(1), n - 1)
            }
        }

        pub unsafe fn f(p: *mut i32, n: usize) {
            let q = rec(p, n);
            let _ = q;
        }
        "#,
    );

    let q = facts(&map, "f", "q");
    assert!(
        q.bases
            .iter()
            .any(|base| matches!(base, BaseId::Param { .. })),
        "recursive summary should keep a Param base in the conservative result: {q:#?}"
    );
    assert!(
        q.bases
            .iter()
            .any(|base| matches!(base, BaseId::OpaqueReturn { .. })),
        "recursive summary should keep an OpaqueReturn base in the conservative result: {q:#?}"
    );
    assert!(
        q.unique.is_none(),
        "recursive summary should stay conservative and non-unique: {q:#?}"
    );
}

#[test]
fn array_local_provenance_use_rvalue_struct_copy_pairs_all_pointer_slots() {
    // Rvalue::Use for a whole-struct copy must pair every pointer slot in the
    // source with the corresponding slot in the destination.  Head slot (i=0)
    // gets an add_edge (unidirectional); tail slots (i>0) get
    // add_bidirectional_edge.  Both fields must carry provenance from their
    // respective parameters after the copy.
    let map = run_analysis(
        r#"
        pub struct Pair {
            pub a: *mut i32,
            pub b: *mut i32,
        }

        pub unsafe fn f(p1: *mut i32, p2: *mut i32) {
            let mut s1 = Pair { a: core::ptr::null_mut(), b: core::ptr::null_mut() };
            s1.a = p1;
            s1.b = p2;
            let s2 = s1;
            let q = s2.a;
            let r = s2.b;
            let _ = (q, r);
        }
        "#,
    );

    let q = facts(&map, "f", "q");
    let r = facts(&map, "f", "r");

    // head slot (a): provenance should flow from p1 via the unidirectional edge
    assert!(
        matches!(q.unique, Some(BaseId::Param { .. })),
        "s2.a should carry p1's Param base after struct copy: {q:#?}"
    );
    assert_eq!(
        q.admissibility,
        Some(BaseAdmissibility::DirectlyRewriteable),
        "p1's base must be DirectlyRewriteable: {q:#?}"
    );

    // tail slot (b): provenance should flow from p2 via the bidirectional edge
    assert!(
        matches!(r.unique, Some(BaseId::Param { .. })),
        "s2.b should carry p2's Param base after struct copy: {r:#?}"
    );
    assert_eq!(
        r.admissibility,
        Some(BaseAdmissibility::DirectlyRewriteable),
        "p2's base must be DirectlyRewriteable: {r:#?}"
    );

    // the two fields must trace back to distinct parameters
    assert_ne!(
        q.unique, r.unique,
        "s2.a and s2.b must have distinct Param bases after copying a Pair"
    );
}

#[test]
fn array_local_provenance_struct_copy_all_pointer_slots_receive_flow_edges() {
    // A struct copy (Rvalue::Use on a struct destination) must propagate
    // provenance to every pointer slot in the destination, not only the head
    // slot.  This test uses a three-field struct so we exercise the head slot
    // (i=0) and two tail slots (i=1, i=2) in a single copy statement.
    //
    // Fields are set via explicit assignment statements (not a struct literal)
    // so that MIR emits individual field-store statements for the source and
    // then a single Rvalue::Use for the whole-struct copy.
    let map = run_analysis(
        r#"
        pub struct Triple {
            pub a: *mut i32,
            pub b: *mut i32,
            pub c: *mut i32,
        }

        pub unsafe fn f(p1: *mut i32, p2: *mut i32, p3: *mut i32) {
            let mut src = Triple {
                a: core::ptr::null_mut(),
                b: core::ptr::null_mut(),
                c: core::ptr::null_mut(),
            };
            src.a = p1;
            src.b = p2;
            src.c = p3;
            let dst = src;
            let q = dst.a;
            let r = dst.b;
            let s = dst.c;
            let _ = (q, r, s);
        }
        "#,
    );

    let q = facts(&map, "f", "q");
    let r = facts(&map, "f", "r");
    let s = facts(&map, "f", "s");

    // every pointer slot in dst must carry its respective Param base
    assert!(
        matches!(q.unique, Some(BaseId::Param { .. })),
        "dst.a should carry p1 Param base after struct copy: {q:#?}"
    );
    assert!(
        matches!(r.unique, Some(BaseId::Param { .. })),
        "dst.b should carry p2 Param base after struct copy: {r:#?}"
    );
    assert!(
        matches!(s.unique, Some(BaseId::Param { .. })),
        "dst.c should carry p3 Param base after struct copy: {s:#?}"
    );
    // each field must trace back to a *distinct* parameter
    assert_ne!(
        q.unique, r.unique,
        "a and b must trace back to distinct params"
    );
    assert_ne!(
        r.unique, s.unique,
        "b and c must trace back to distinct params"
    );
    assert_ne!(
        q.unique, s.unique,
        "a and c must trace back to distinct params"
    );
}

#[test]
fn array_local_provenance_through_pointer_write_struct_field_gets_edge() {
    // when a struct value is written *through* a raw pointer to a struct —
    // i.e., the destination place begins with a Deref projection and the
    // resulting type is a struct containing pointer fields (NOT itself a raw
    // pointer) — every pointer slot in the destination must receive an
    // appropriate edge so that provenance propagates correctly.
    //   1. src.p = p       — direct field write; src.p's slot gets a Param edge
    //                        (raw-pointer destination, handled by old code too).
    //   2. *lptr = src     — add_edge(src.p, (*lptr).p).
    //   3. let q = local.p — direct field read; local.p is linked bidirectionally
    //                        to (*lptr).p via collect_address_links (from step when
    //                        lptr = &raw mut local).
    let map = run_analysis(
        r#"
        pub struct Slot {
            pub p: *mut i32,
        }

        pub unsafe fn f(p: *mut i32) {
            let mut local = Slot { p: core::ptr::null_mut() };
            let lptr = &raw mut local;
            let mut src = Slot { p: core::ptr::null_mut() };
            src.p = p;
            *lptr = src;
            let q = local.p;
            let _ = q;
        }
        "#,
    );

    let q = facts(&map, "f", "q");
    assert!(
        matches!(q.unique, Some(BaseId::Param { .. })),
        "through-pointer struct write should propagate param provenance to the \
         local field slot — q must have a unique Param base: {q:#?}"
    );
    assert_eq!(
        q.admissibility,
        Some(BaseAdmissibility::DirectlyRewriteable),
        "param base must be DirectlyRewriteable: {q:#?}"
    );
}

#[test]
fn array_local_provenance_through_pointer_nested_field_write_slot_gets_edge() {
    let map = run_analysis(
        r#"
        pub struct Inner {
            pub p: *mut i32,
        }

        pub struct Outer {
            pub inner: Inner,
        }

        pub unsafe fn f(p: *mut i32) {
            let mut local = Outer { inner: Inner { p: core::ptr::null_mut() } };
            let ptr = &raw mut local;
            let mut src = Inner { p: core::ptr::null_mut() };
            src.p = p;
            (*ptr).inner = src;
            let q = local.inner.p;
            let _ = q;
        }
        "#,
    );

    let q = facts(&map, "f", "q");
    assert!(
        matches!(q.unique, Some(BaseId::Param { .. })),
        "through-pointer write to a struct field (Inner) containing a pointer must \
         propagate param provenance to the nested pointer slot — q must have a \
         unique Param base (AC 8): {q:#?}"
    );
    assert_eq!(
        q.admissibility,
        Some(BaseAdmissibility::DirectlyRewriteable),
        "param base must be DirectlyRewriteable: {q:#?}"
    );
}

/// source_node must work for a reference-typed source (&*mut i32) so that
/// provenance can flow even when the place is a reference, not a raw pointer.
#[test]
fn array_local_provenance_source_node_reference_to_pointer_flows_provenance() {
    let map = run_analysis(
        r#"
        pub unsafe fn f(p: *mut i32) {
            let r = &p;   // r: &*mut i32 — not a raw pointer
            let q = *r;   // may emit CopyForDeref(r) in MIR
            let _ = q;
        }
        "#,
    );

    let q = facts(&map, "f", "q");
    assert!(
        matches!(q.unique, Some(BaseId::Param { .. })),
        "dereferencing a reference-to-raw-pointer must preserve param provenance \
         via the range-based source_node (AC 5): {q:#?}"
    );
    assert_eq!(
        q.admissibility,
        Some(BaseAdmissibility::DirectlyRewriteable),
        "param base must be DirectlyRewriteable: {q:#?}"
    );
}

#[test]
fn array_local_provenance_rawptr_of_union_field_fills_tail_slot_unknown() {
    let map = run_analysis(
        r#"
        pub union U {
            pub inner: *mut i32,
            pub bits: usize,
        }

        pub unsafe fn f(v: *mut i32) {
            let mut u = U { inner: v };
            let ptr: *mut *mut i32 = &raw mut u.inner;
            let q = *ptr;
            let _ = q;
        }
        "#,
    );

    let q = facts(&map, "f", "q");
    assert!(
        matches!(q.unique, Some(BaseId::Unknown { .. })),
        "loading through a ptr-to-ptr whose tail slot came from an unsupported \
         projection should yield Unknown provenance, not absent provenance: {q:#?}"
    );
    assert_eq!(
        q.admissibility,
        Some(BaseAdmissibility::Reject),
        "Unknown base must be classified as Reject: {q:#?}"
    );
}

#[test]
fn array_local_provenance_cast_to_double_ptr_tail_slot_gets_unknown() {
    // Cast *mut i32 → *mut *mut i32.
    //   slot[0] of pptr = CastResult edge (cast provenance, not directly rewriteable)
    //   slot[1] of pptr = Unknown{UnsupportedProjection}
    let map = run_analysis(
        r#"
        pub unsafe fn f(p: *mut i32) {
            let pptr: *mut *mut i32 = p as *mut *mut i32;
            let q = *pptr;
            let _ = q;
        }
        "#,
    );

    let q = facts(&map, "f", "q");
    assert!(
        matches!(q.unique, Some(BaseId::Unknown { .. })),
        "dereferencing a *mut *mut i32 produced by a Cast must yield Unknown provenance \
         for the inner pointer slot (AC 4 Cast arm): {q:#?}"
    );
    assert_eq!(
        q.admissibility,
        Some(BaseAdmissibility::Reject),
        "Unknown base must be classified as Reject: {q:#?}"
    );
}

#[test]
fn array_local_provenance_cast_single_slot_slot0_preserves_param_provenance() {
    let map = run_analysis(
        r#"
        pub unsafe fn f(sequence: *mut i8) {
            let bools = sequence as *mut bool;
            let _ = bools;
        }
        "#,
    );

    let bools = facts(&map, "f", "bools");
    assert!(
        matches!(bools.unique, Some(BaseId::Param { .. })),
        "slot[0] of a single-slot Cast result must carry Param provenance (AC 4 Cast \
         non-regression): {bools:#?}"
    );
    assert_eq!(
        bools.admissibility,
        Some(BaseAdmissibility::DirectlyRewriteable),
        "Param base must be DirectlyRewriteable: {bools:#?}"
    );
}

#[test]
fn select_rewrite_groups_selects_cast_cursor_over_param_base() {
    let groups = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::ReadyOnly,
        r#"
        fn parse_bool(c: i8) -> bool {
            c == 89 || c == 121
        }

        pub unsafe fn f(sequence: *mut i8, len: usize) -> i32 {
            let bools = sequence as *mut bool;
            let mut i: usize = 0;
            while i < len {
                let val = parse_bool(*sequence.offset(i as isize));
                *bools.offset(i as isize) = val;
                i = i.wrapping_add(1);
            }
            if !*bools.offset(0) {
                return -10;
            }
            0
        }
        "#,
    );

    let f_groups = groups.get("f").unwrap();
    assert!(
        f_groups.iter().any(|group| {
            matches!(group.base, BaseId::Param { .. })
                && group.base_name.as_deref() == Some("sequence")
                && group.member_names.contains("bools")
                && group.has_rewritable_binding
        }),
        "cast cursor over param base should be selected: {f_groups:#?}"
    );
}

#[test]
fn array_local_provenance_rawptr_double_ptr_tail_slot_preserves_param_provenance() {
    let map = run_analysis(
        r#"
        pub unsafe fn f(p: *mut i32) {
            let mut ptr = p;
            let pptr: *mut *mut i32 = &raw mut ptr;
            let q = *pptr;
            let _ = q;
        }
        "#,
    );

    let q = facts(&map, "f", "q");
    assert!(
        matches!(q.unique, Some(BaseId::Param { .. })),
        "dereferencing *mut *mut i32 from &raw mut ptr must yield Param provenance \
         via collect_address_links (AC 4 RawPtr non-regression): {q:#?}"
    );
    assert_eq!(
        q.admissibility,
        Some(BaseAdmissibility::DirectlyRewriteable),
        "Param base must be DirectlyRewriteable: {q:#?}"
    );
}

#[test]
fn array_local_provenance_struct_field_array_offset_pointers_share_base() {
    let map = run_analysis(
        r#"
        pub struct Buf {
            pub data: [i32; 8],
        }
        pub unsafe fn f(buf: *mut Buf, i: usize) {
            let current = &mut *(*buf).data.as_mut_ptr().add(i) as *mut i32;
            let base = &mut *(*buf).data.as_mut_ptr().add(0) as *mut i32;
            let _ = (current, base);
        }
        "#,
    );

    let current = facts(&map, "f", "current");
    let base_var = facts(&map, "f", "base");
    assert!(
        current.unique.is_some(),
        "current should have a unique base: {current:#?}"
    );
    assert_eq!(
        current.unique, base_var.unique,
        "current and base must share the same unique base so offset_from can be rewritten"
    );
    assert!(
        matches!(current.unique, Some(BaseId::LocalArray { .. })),
        "the shared base should be LocalArray: {current:#?}"
    );
}

#[test]
fn select_rewrite_groups_reject_struct_pointer_base_for_field_array_pointers() {
    let groups = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::ReadyOnly,
        r#"
        pub struct Info {
            pub steps: *mut u32,
            pub leaf_addr: [u32; 8],
            pub pk_addr: [u32; 8],
        }

        pub unsafe fn f(v_info: *mut Info) {
            let info = v_info;
            let leaf_addr = ((*info).leaf_addr).as_mut_ptr();
            let pk_addr = ((*info).pk_addr).as_mut_ptr();
            *leaf_addr = 1;
            *pk_addr = 2;
        }
        "#,
    );

    let selected = groups.get("f").cloned().unwrap_or_default();
    assert!(
        selected.is_empty(),
        "field-array pointers must not be selected as cursors over the enclosing struct pointer: {selected:#?}"
    );
}

#[test]
fn select_rewrite_groups_extern_call_with_struct_param_does_not_contaminate_param_field_slot() {
    let groups = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::ReadyOnly,
        r#"
        pub struct State {
            pub out: *mut i8,
        }

        unsafe extern "C" {
            fn process(state: *mut State);
        }

        pub unsafe fn f(state: *mut State, n: usize) {
            process(state);
            let dst: *mut i8 = (*state).out;
            let next: *mut i8 = dst.add(1);
            let _ = (*dst, *next);
        }
        "#,
    );

    let f_groups = groups.get("f").unwrap();
    assert!(
        f_groups.iter().any(|group| {
            matches!(group.base, BaseId::Param { .. })
                && group.member_names.contains("dst")
                && group.member_names.contains("next")
        }),
        "extern call before members are live must not contaminate the param field slot via UML: {f_groups:#?}"
    );
}

#[test]
fn select_rewrite_groups_cp_block_pattern_produces_index_tracked_group() {
    let groups = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::ReadyOnly,
        r#"
        pub struct State {
            pub out: *mut i8,
        }

        unsafe extern "C" {
            fn process(state: *mut State);
        }

        pub unsafe fn f(state: *mut State, backward: usize, n: usize) {
            process(state);
            let src: *const i8 = ((*state).out as *const i8).sub(backward);
            (*state).out = ((*state).out).add(n);
            let _keep: *const i8 = src;
        }
        "#,
    );

    let f_groups = groups.get("f").unwrap();
    assert!(
        f_groups.iter().any(|group| {
            matches!(group.base, BaseId::Param { .. })
                && group.index_tracked
                && group.member_names.contains("state.out")
                && group.member_names.contains("src")
        }),
        "cp_block pattern must produce an index_tracked Param group for state.out and src: {f_groups:#?}"
    );
}

#[test]
fn liveness_gate_rejects_group_when_two_mut_locals_never_simultaneously_live() {
    // q is used and dead before r is created — no simultaneous borrow conflict.
    let groups = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::ReadyOnly,
        r#"
        pub unsafe fn f(p: *mut i32) {
            let q = p.add(1);
            let _ = *q;
            let r = p.add(2);
            let _ = *r;
        }
        "#,
    );
    let f_groups = groups
        .get("f")
        .unwrap_or_else(|| panic!("missing f: {groups:#?}"));
    assert!(
        !f_groups
            .iter()
            .any(|g| { g.member_names.contains("q") && g.member_names.contains("r") }),
        "q and r have non-overlapping live ranges — no group should be selected: {f_groups:#?}"
    );
}

#[test]
fn liveness_gate_accepts_group_when_two_mut_locals_simultaneously_live() {
    // q and r are both live at the tuple read — genuine borrow conflict.
    let groups = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::ReadyOnly,
        r#"
        pub unsafe fn f(p: *mut i32) {
            let q = p.add(1);
            let r = p.add(2);
            let _ = (*q, *r);
        }
        "#,
    );
    let f_groups = groups
        .get("f")
        .unwrap_or_else(|| panic!("missing f: {groups:#?}"));
    assert!(
        f_groups
            .iter()
            .any(|g| { g.member_names.contains("q") && g.member_names.contains("r") }),
        "q and r are simultaneously live — group must be selected: {f_groups:#?}"
    );
}

#[test]
fn liveness_gate_rejects_group_when_mut_and_imm_locals_never_simultaneously_live() {
    // q (mut) is dead before r (const cast) is created.
    let groups = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::ReadyOnly,
        r#"
        pub unsafe fn f(p: *mut i32) {
            let q = p.add(1);
            let _ = *q;
            let r = p.add(2) as *const i32;
            let _ = *r;
        }
        "#,
    );
    let f_groups = groups
        .get("f")
        .unwrap_or_else(|| panic!("missing f: {groups:#?}"));
    assert!(
        !f_groups
            .iter()
            .any(|g| { g.member_names.contains("q") && g.member_names.contains("r") }),
        "q (*mut) and r (*const) have non-overlapping live ranges — no group should be selected: {f_groups:#?}"
    );
}

#[test]
fn liveness_gate_accepts_group_when_mut_and_imm_locals_simultaneously_live() {
    // q (*mut) and r (*const alias of q) are both alive at the tuple read.
    let groups = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::ReadyOnly,
        r#"
        pub unsafe fn f(p: *mut i32) {
            let q = p.add(1);
            let r = q as *const i32;
            let _ = (*q, *r);
        }
        "#,
    );
    let f_groups = groups
        .get("f")
        .unwrap_or_else(|| panic!("missing f: {groups:#?}"));
    assert!(
        f_groups
            .iter()
            .any(|g| { g.member_names.contains("q") && g.member_names.contains("r") }),
        "q (*mut) and r (*const) are simultaneously live — group must be selected: {f_groups:#?}"
    );
}

#[test]
fn group_has_rewritable_binding_for_field_base_group() {
    let code = r#"
        #[repr(C)]
        pub struct Img {
            pub pix: *mut u8,
        }
        pub unsafe fn process(mut img: *mut Img) {
            let mut pix: *mut u8 = (*img).pix;
            let mut a: *mut u8 = pix.offset(3);
            let mut b: *mut u8 = pix.offset(5);
            *a = *b;
            a = a.offset(1);
            b = b.offset(1);
        }
    "#;

    let facts = run_rewrite_groups_with_points_to(RewriteGroupFactMode::ReadyOnly, code);
    let process_groups = facts.get("process").expect("process not found");
    assert!(
        !process_groups.is_empty(),
        "expected at least one rewrite group for process"
    );
    assert!(
        process_groups.iter().any(|g| g.has_rewritable_binding),
        "expected has_rewritable_binding=true for the field-base group, got: {process_groups:?}"
    );
}

#[test]
fn index_tracked_pointee_field_base_group_is_flagged_live_base() {
    // cp_block shape: the base slot (*state).out lives behind a parameter
    // pointer; turning its direct store into an index update would hide the
    // advanced pointer from the caller, so the rewriter uses the live-field /
    // shadow-counter scheme and flags the group accordingly.
    let groups = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::ReadyOnly,
        r#"
        pub struct State {
            pub out: *mut i8,
        }

        unsafe extern "C" {
            fn process(state: *mut State);
        }

        pub unsafe fn f(state: *mut State, backward: usize, n: usize) {
            process(state);
            let src: *const i8 = ((*state).out as *const i8).sub(backward);
            (*state).out = ((*state).out).add(n);
            let _keep: *const i8 = src;
        }
        "#,
    );

    let f_groups = groups.get("f").unwrap();
    let group = f_groups
        .iter()
        .find(|group| group.index_tracked && group.member_names.contains("state.out"))
        .unwrap_or_else(|| panic!("expected index_tracked state.out group: {f_groups:#?}"));
    assert!(
        group.needs_live_base_rewrite,
        "index-tracked pointee field base must be flagged needs_live_base_rewrite: {group:#?}"
    );
}

#[test]
fn index_tracked_by_value_field_base_group_is_not_flagged_live_base() {
    // pair.a lives in the by-value parameter copy; suppressing its store is
    // invisible to the caller, so the group stays plannable without live-base.
    let groups = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::ReadyOnly,
        r#"
        pub struct Pair {
            pub a: *mut i32,
            pub b: *mut i32,
        }

        pub unsafe fn f(mut pair: Pair, i: usize) {
            let qa = pair.a.add(i);
            let qb = pair.b.add(i);
            pair.a = pair.a.add(1);
            let ra = qa.add(1);
            let rb = qb.add(1);
            let _ = (*ra, *rb);
        }
        "#,
    );

    let f_groups = groups.get("f").unwrap();
    let group = f_groups
        .iter()
        .find(|group| group.index_tracked && group.member_names.contains("qa"))
        .unwrap_or_else(|| panic!("expected index_tracked pair.a group: {f_groups:#?}"));
    assert!(
        !group.needs_live_base_rewrite,
        "by-value field base writes a local copy and must stay plannable: {group:#?}"
    );
}

#[test]
fn index_tracked_top_level_param_group_is_not_flagged_live_base() {
    // p is a by-value parameter binding; reassigning it is caller-invisible.
    let groups = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::ReadyOnly,
        r#"
        pub unsafe fn f(mut p: *mut i32, i: usize) {
            let q = p.add(i);
            p = p.add(1);
            let r = q.add(1);
            let _ = (*q, *r);
        }
        "#,
    );

    let f_groups = groups.get("f").unwrap();
    let group = f_groups
        .iter()
        .find(|group| group.index_tracked && group.member_names.contains("q"))
        .unwrap_or_else(|| panic!("expected index_tracked param group: {f_groups:#?}"));
    assert!(
        !group.needs_live_base_rewrite,
        "top-level param cursor must stay plannable: {group:#?}"
    );
}

#[test]
fn user_defined_add_function_is_not_pointer_arithmetic() {
    // a free function named `add` (common in translated C) must not be
    // granted the base-preserving semantics of <*mut T>::add; the genuine
    // inherent method keeps them.
    let map = run_analysis(
        r#"
        pub unsafe fn add(p: *mut i32, _n: i32) -> *mut i32 {
            p
        }

        pub unsafe fn f(p: *mut i32) {
            let q = add(p, 1);
            let r = p.add(1);
            let _ = (*q, *r);
        }
        "#,
    );

    let q = facts(&map, "f", "q");
    assert!(
        matches!(q.unique, Some(BaseId::OpaqueReturn { .. })),
        "user-defined add must yield an opaque return, got {q:#?}"
    );
    let r = facts(&map, "f", "r");
    assert_unique_param(r);
}

#[test]
fn local_function_named_malloc_is_not_heap_alloc() {
    let map = run_analysis(
        r#"
        pub unsafe fn malloc(_size: usize) -> *mut u8 {
            core::ptr::null_mut()
        }

        pub unsafe fn f() {
            let q = malloc(8);
            let _ = *q;
        }
        "#,
    );

    let q = facts(&map, "f", "q");
    assert!(
        !q.bases
            .iter()
            .any(|base| matches!(base, BaseId::HeapAlloc { .. })),
        "local fn named malloc must not get heap-alloc provenance: {q:#?}"
    );
    assert!(
        matches!(q.unique, Some(BaseId::OpaqueReturn { .. })),
        "local fn named malloc must yield an opaque return, got {q:#?}"
    );
}

#[test]
fn foreign_malloc_is_heap_alloc() {
    let map = run_analysis(
        r#"
        unsafe extern "C" {
            fn malloc(size: usize) -> *mut u8;
        }

        pub unsafe fn f() {
            let q = malloc(8);
            let _ = *q;
        }
        "#,
    );

    let q = facts(&map, "f", "q");
    assert!(
        matches!(q.unique, Some(BaseId::HeapAlloc { .. })),
        "foreign malloc must keep heap-alloc provenance, got {q:#?}"
    );
}

#[test]
fn select_rewrite_groups_rejects_size_mismatched_cast_cursor() {
    // `small` is `seq as *mut i8` over an `*mut i32` base: the cast changes the
    // pointee size (4 -> 1), so an index recorded in `small`'s i8 units would be
    // wrong in `seq`'s i32 units. selection must reject the cast cursor.
    let groups = run_rewrite_groups_with_points_to(
        RewriteGroupFactMode::ReadyOnly,
        r#"
        pub unsafe fn f(seq: *mut i32, len: usize) -> i32 {
            let small = seq as *mut i8;
            let mut i: usize = 0;
            while i < len {
                let v = *seq.offset(i as isize);
                *small.offset(i as isize) = v as i8;
                i = i.wrapping_add(1);
            }
            if *small.offset(0) != 0 {
                return -10;
            }
            0
        }
        "#,
    );

    let f_groups = groups.get("f").unwrap();
    assert!(
        !f_groups.iter().any(|group| {
            matches!(group.base, BaseId::Param { .. })
                && group.base_name.as_deref() == Some("seq")
                && group.member_names.contains("small")
        }),
        "size-mismatched cast cursor must not be selected into the base group: {f_groups:#?}"
    );
}

#[test]
fn constant_pointer_string_literal_is_not_nulllike() {
    // a cursor reassigned to a byte-string literal must get a ConstantPointer
    // base (opaque), not a transparent NullLike base.
    let map = run_analysis(
        r#"
        pub unsafe fn f(p: *const i8, cond: bool) {
            let mut q: *const i8 = p.offset(1);
            if cond {
                q = b"x\0" as *const u8 as *const i8;
            }
            let _ = *q;
            let _ = *p;
        }
        "#,
    );
    let q = facts(&map, "f", "q");
    assert!(
        q.bases.iter().any(|b| matches!(
            b,
            BaseId::Unknown {
                reason: UnknownReason::ConstantPointer,
                ..
            }
        )),
        "string-literal reassignment must produce a ConstantPointer base: {q:#?}"
    );
    assert!(
        !q.bases.iter().any(|b| matches!(
            b,
            BaseId::Unknown {
                reason: UnknownReason::NullLike,
                ..
            }
        )),
        "string-literal reassignment must not be classified NullLike: {q:#?}"
    );
}

#[test]
fn constant_pointer_string_literal_breaks_unique_non_null_base() {
    // because ConstantPointer is opaque, the cursor no longer has a unique
    // non-null base, so it is excluded at selection time.
    let map = run_analysis(
        r#"
        pub unsafe fn f(p: *const i8, cond: bool) {
            let mut q: *const i8 = p.offset(1);
            if cond {
                q = b"x\0" as *const u8 as *const i8;
            }
            let _ = *q;
            let _ = *p;
        }
        "#,
    );
    let q = facts(&map, "f", "q");
    assert_eq!(
        q.unique_non_null, None,
        "string-literal reassignment must remove the unique non-null base: {q:#?}"
    );
}

#[test]
fn null_sentinel_reassignment_stays_transparent() {
    // regression: the 0-as-pointer null sentinel must remain a transparent
    // NullLike base so null-initialized cursors keep a unique non-null base.
    let map = run_analysis(
        r#"
        pub unsafe fn f(p: *const i8, cond: bool) {
            let mut q: *const i8 = p.offset(1);
            if cond {
                q = 0 as *const i8;
            }
            let _ = *q;
            let _ = *p;
        }
        "#,
    );
    let q = facts(&map, "f", "q");
    assert!(
        q.bases.iter().any(|b| matches!(
            b,
            BaseId::Unknown {
                reason: UnknownReason::NullLike,
                ..
            }
        )),
        "null sentinel must stay NullLike: {q:#?}"
    );
    assert!(
        !q.bases.iter().any(|b| matches!(
            b,
            BaseId::Unknown {
                reason: UnknownReason::ConstantPointer,
                ..
            }
        )),
        "null sentinel must not become ConstantPointer: {q:#?}"
    );
    assert!(
        matches!(q.unique_non_null, Some(BaseId::Param { .. })),
        "null sentinel must keep a unique non-null Param base: {q:#?}"
    );
}

// --- builtin_summary tests ---

#[test]
fn builtin_summary_strstr_foreign_gives_param_and_null_bases() {
    // strstr returns a cursor into arg0 or null; the result must have
    // Param(uname) as the unique non-null base and a NullLike base too.
    let map = run_analysis(
        r#"
        unsafe extern "C" {
            fn strstr(
                haystack: *const core::ffi::c_char,
                needle: *const core::ffi::c_char,
            ) -> *mut core::ffi::c_char;
        }

        pub unsafe fn f(uname: *const core::ffi::c_char, pat: *const core::ffi::c_char) {
            let str_tmp: *mut core::ffi::c_char = strstr(uname, pat);
            let _ = str_tmp;
        }
        "#,
    );

    let str_tmp = facts(&map, "f", "str_tmp");
    // must carry a Param base (from arg0=uname)
    assert!(
        str_tmp
            .bases
            .iter()
            .any(|b| matches!(b, BaseId::Param { .. })),
        "strstr result must have a Param base: {str_tmp:#?}"
    );
    // must carry a NullLike base (null-on-miss)
    assert!(
        str_tmp.bases.iter().any(|b| matches!(
            b,
            BaseId::Unknown {
                reason: UnknownReason::NullLike,
                ..
            }
        )),
        "strstr result must have a NullLike base: {str_tmp:#?}"
    );
    // unique non-null base must be the Param
    assert!(
        matches!(str_tmp.unique_non_null, Some(BaseId::Param { .. })),
        "strstr unique non-null base must be Param(uname): {str_tmp:#?}"
    );
}

#[test]
fn builtin_summary_strstr_foreign_is_selected_and_nullable() {
    // strstr result must be selected into a rewrite group together with `cur`
    // (both derive from `uname`) and the group is nullable.
    let code = r#"
        unsafe extern "C" {
            fn strstr(
                haystack: *const core::ffi::c_char,
                needle: *const core::ffi::c_char,
            ) -> *mut core::ffi::c_char;
        }

        pub unsafe fn f(mut uname: *const core::ffi::c_char, pat: *const core::ffi::c_char) {
            let str_tmp: *mut core::ffi::c_char = strstr(uname, pat);
            let cur: *mut core::ffi::c_char = str_tmp.offset(1);
            let _ = (*cur, *str_tmp);
        }
        "#;

    // selection check
    let groups = run_rewrite_groups_with_points_to(RewriteGroupFactMode::ReadyOnly, code);
    let f_groups = groups.get("f").expect("missing facts for f");
    assert!(
        f_groups
            .iter()
            .any(|group| group.member_names.contains("str_tmp")),
        "strstr result must be selected into a rewrite group: {f_groups:#?}"
    );

    // nullability check: str_tmp must carry a NullLike base so the rewriter
    // emits Option<isize>; dropping the NullLike flow from base_preserving()
    // would leave the selection assertion above green but break this one.
    let map = run_analysis(code);
    let str_tmp = facts(&map, "f", "str_tmp");
    assert!(
        str_tmp.bases.iter().any(|b| matches!(
            b,
            BaseId::Unknown {
                reason: UnknownReason::NullLike,
                ..
            }
        )),
        "str_tmp must carry a NullLike base (null-on-miss makes it nullable): {str_tmp:#?}"
    );
}

#[test]
fn builtin_summary_local_strstr_not_treated_as_base_preserving() {
    // a LOCAL Rust function named strstr must not be treated as base-preserving
    // by the builtin table; its return gets OpaqueReturn provenance.
    let map = run_analysis(
        r#"
        pub unsafe fn strstr(
            haystack: *const core::ffi::c_char,
            needle: *const core::ffi::c_char,
        ) -> *mut core::ffi::c_char {
            let _ = (haystack, needle);
            core::ptr::null_mut()
        }

        pub unsafe fn f(uname: *const core::ffi::c_char, pat: *const core::ffi::c_char) {
            let str_tmp: *mut core::ffi::c_char = strstr(uname, pat);
            let _ = str_tmp;
        }
        "#,
    );

    let str_tmp = facts(&map, "f", "str_tmp");
    // the local strstr returns null_mut(), so no Param base should flow to str_tmp
    assert!(
        !str_tmp
            .bases
            .iter()
            .any(|b| matches!(b, BaseId::Param { .. })),
        "local strstr must not receive Param base from the builtin table: {str_tmp:#?}"
    );
}

#[test]
fn builtin_summary_mismatched_foreign_strstr_not_base_preserving() {
    // a foreign strstr whose first two args are non-pointer integers does not
    // match the builtin signature guard and falls through to unknown-call handling.
    let map = run_analysis(
        r#"
        unsafe extern "C" {
            fn strstr(a: i32, b: i32) -> *mut core::ffi::c_char;
        }

        pub unsafe fn f(n: i32, m: i32) {
            let str_tmp: *mut core::ffi::c_char = strstr(n, m);
            let _ = str_tmp;
        }
        "#,
    );

    let str_tmp = facts(&map, "f", "str_tmp");
    // mismatched signature must not produce {Param, NullLike} base set
    assert!(
        !str_tmp
            .bases
            .iter()
            .any(|b| matches!(b, BaseId::Param { .. })),
        "signature-mismatched foreign strstr must not receive a Param base: {str_tmp:#?}"
    );
}
