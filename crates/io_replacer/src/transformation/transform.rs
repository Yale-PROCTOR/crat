use std::{
    cell::{Cell, RefCell},
    fmt::Write as _,
    fs,
};

use etrace::some_or;
use lazy_static::lazy_static;
use rustc_abi::FIRST_VARIANT;
use rustc_ast::mut_visit::MutVisitor;
use rustc_ast_pretty::pprust;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{self as hir, HirId};
use rustc_index::IndexVec;
use rustc_middle::{
    mir,
    ty::{List, TyCtxt},
};
use rustc_span::{Span, Symbol, def_id::LocalDefId, sym};
use serde::Deserialize;
use toml_edit::DocumentMut;
use typed_arena::Arena;
use utils::{bit_set::BitSet16, file::api_list::Permission};

use super::{
    file_analysis::{self, UnsupportedReason},
    hir_ctx::{HirCtx, HirLoc, HirVisitor},
    mir_loc::MirLoc,
    stream_ty::*,
    visitor::{Parameter, TransformVisitor},
};

#[derive(Debug, Default, Clone, Copy, Deserialize)]
pub struct Config {
    pub assume_to_str_ok: bool,
}

#[derive(Debug)]
pub struct TransformationResult {
    pub code: String,
    pub tempfile: bool,
    pub bytemuck: bool,
    pub unsupported_reasons: Vec<BitSet16<UnsupportedReason>>,
    pub bound_num: usize,
    pub transformation_time: u128,
    pub analysis_stat: file_analysis::Statistics,
}

pub fn replace_io(config: Config, tcx: TyCtxt<'_>) -> TransformationResult {
    let mut krate = utils::ast::expanded_ast(tcx);

    let arena = Arena::new();
    let analysis_res = file_analysis::analyze(&arena, tcx);

    let ast_to_hir = utils::ast::make_ast_to_hir(&mut krate, tcx);
    utils::ast::remove_unnecessary_items_from_ast(&mut krate);

    let start = std::time::Instant::now();
    let error_returning_fns: FxHashMap<_, Vec<_>> = analysis_res
        .returning_fns
        .iter()
        .map(|(def_id, set)| (*def_id, set.iter().copied().collect()))
        .collect();
    let error_taking_fns: FxHashMap<_, Vec<_>> = analysis_res
        .taking_fns
        .iter()
        .map(|(def_id, set)| (*def_id, set.iter().copied().collect()))
        .collect();
    let tracked_locs: FxHashSet<_> = analysis_res
        .tracking_fns
        .values()
        .flatten()
        .map(|(loc, _)| *loc)
        .collect();
    let tracked_locs: Vec<_> = tracked_locs.into_iter().collect();
    let tracked_loc_to_index: FxHashMap<_, _> = tracked_locs
        .iter()
        .enumerate()
        .map(|(i, loc)| (*loc, i))
        .collect();

    // collect information from HIR
    let mut hir_visitor = HirVisitor {
        tcx,
        ctx: HirCtx::default(),
    };
    tcx.hir_visit_all_item_likes_in_crate(&mut hir_visitor);
    let mut hir_ctx = hir_visitor.ctx;
    let return_locals: FxHashMap<_, _> = hir_ctx
        .return_locals
        .iter()
        .filter_map(|(f, locals)| {
            if locals.len() == 1 {
                locals.iter().next().unwrap().map(|l| (*f, l))
            } else {
                None
            }
        })
        .collect();

    let is_stdin_unsupported = analysis_res
        .unsupported
        .contains(analysis_res.loc_ind_map[&MirLoc::Stdin]);
    let is_stdout_unsupported = analysis_res
        .unsupported
        .contains(analysis_res.loc_ind_map[&MirLoc::Stdout]);
    let is_stderr_unsupported = analysis_res
        .unsupported
        .contains(analysis_res.loc_ind_map[&MirLoc::Stderr]);

    // all unsupported spans
    let mut unsupported = FxHashMap::default();
    let mut unsupported_returns = FxHashSet::default();
    for loc_id in analysis_res.unsupported.iter() {
        let loc = analysis_res.locs[loc_id];
        match loc {
            MirLoc::Var(def_id, local) => {
                let span = mir_local_span(def_id, local, &return_locals, &hir_ctx, tcx);
                unsupported.insert(span, loc);
                if local == mir::Local::ZERO {
                    unsupported_returns.insert(def_id);
                    if let Some(spans) = hir_ctx.return_spans.get(&def_id) {
                        for span in spans {
                            unsupported.insert(*span, loc);
                        }
                    }
                }
            }
            MirLoc::Field(def_id, field_idx) => {
                let node = tcx.hir_node_by_def_id(def_id);
                let hir::Node::Item(item) = node else { panic!() };
                let (hir::ItemKind::Struct(_, _, vd) | hir::ItemKind::Union(_, _, vd)) = item.kind
                else {
                    panic!()
                };
                let hir::VariantData::Struct { fields, .. } = vd else { panic!() };
                unsupported.insert(fields[field_idx.as_usize()].span, loc);
            }
            MirLoc::Stdin | MirLoc::Stdout | MirLoc::Stderr | MirLoc::Extern => {}
        }
    }
    let mut unsupported_locs = FxHashSet::default();
    for (span, loc) in &hir_ctx.binding_span_to_loc {
        let unsupported_loc = *some_or!(unsupported.get(span), continue);
        unsupported_locs.insert(*loc);
        let bounds = some_or!(hir_ctx.loc_to_bound_spans.get(loc), continue);
        for span in bounds {
            // add bound occurrence to unsupported
            unsupported.insert(*span, unsupported_loc);

            // add rhs to unsupported
            if let Some(spans) = hir_ctx.lhs_to_rhs.get(span) {
                for span in spans {
                    unsupported.insert(*span, unsupported_loc);
                }
            }
        }
    }

    let fn_ptr_args: FxHashSet<_> = hir_ctx
        .fn_ptr_arg_spans
        .iter()
        .filter_map(|span| hir_ctx.bound_span_to_loc.get(span))
        .collect();

    let callers: FxHashSet<_> = hir_ctx.call_graph.keys().copied().collect();
    for callees in hir_ctx.call_graph.values_mut() {
        callees.retain(|f| callers.contains(f));
    }
    let sccs: utils::graph::Sccs<_, true> = utils::graph::sccs_copied(&hir_ctx.call_graph);
    let mut recursive_fns = FxHashSet::default();
    for fns in sccs.scc_elems.iter() {
        if fns.len() == 1 {
            let f = fns.iter().next().unwrap();
            if hir_ctx.call_graph[f].contains(f) {
                recursive_fns.insert(*f);
            }
        } else {
            recursive_fns.extend(fns.iter().copied());
        }
    }

    let mut param_to_hir_loc = FxHashMap::default();
    let mut hir_loc_to_param = FxHashMap::default();
    let mut non_generic_params = FxHashSet::default();
    let mut loc_id_to_hir_locs = IndexVec::from_raw(vec![None; analysis_res.locs.len()]);
    let mut hir_loc_to_loc_id = FxHashMap::default();
    for (loc_id, loc) in analysis_res.locs.iter_enumerated() {
        let (hir_locs, ctx) = match loc {
            MirLoc::Var(def_id, local) => {
                let hir::Node::Item(item) = tcx.hir_node_by_def_id(*def_id) else { panic!() };
                match item.kind {
                    hir::ItemKind::Fn { sig, .. } => {
                        let mut locs = vec![];
                        let is_static_return = if *local == mir::Local::ZERO {
                            locs.push(HirLoc::Return(*def_id));
                            hir_ctx.return_statics.contains_key(def_id)
                        } else {
                            false
                        };
                        let span = mir_local_span(*def_id, *local, &return_locals, &hir_ctx, tcx);
                        if let Some(loc) = hir_ctx.binding_span_to_loc.get(&span) {
                            locs.push(*loc);
                        }
                        if locs.is_empty() {
                            continue;
                        }

                        let body = tcx.optimized_mir(*def_id);
                        let ty = body.local_decls[*local].ty;
                        let mut is_param_without_assign = false;

                        if (1..=sig.decl.inputs.len()).contains(&local.as_usize()) {
                            // if this local is a parameter
                            let param = Parameter {
                                func: *def_id,
                                index: local.as_usize() - 1,
                            };
                            let loc = locs[0];
                            param_to_hir_loc.insert(param, loc);
                            hir_loc_to_param.insert(loc, param);

                            if analysis_res.fn_ptrs.contains(def_id)
                                || fn_ptr_args.contains(&loc)
                                || analysis_res.permissions[loc_id].contains(Permission::Lock)
                                || utils::file::is_file_ptr_ptr(ty, tcx)
                                || utils::file::file_param_index(ty, tcx).is_some()
                                || hir_ctx.is_loc_used_in_assign(loc)
                            {
                                non_generic_params.insert(param);
                            }

                            if !hir_ctx.is_loc_used_in_assign(locs[0]) {
                                is_param_without_assign = true;
                            }
                        }

                        let mut ctx = LocCtx::new(ty);
                        ctx.is_non_local_assign = is_static_return;
                        ctx.is_param_without_assign |= is_param_without_assign;
                        ctx.is_recursive = recursive_fns.contains(def_id);
                        (locs, ctx)
                    }
                    hir::ItemKind::Static(_, _, _, _) => {
                        if *local != mir::Local::ZERO {
                            continue;
                        }
                        let body = tcx.mir_for_ctfe(*def_id);
                        let ty = body.local_decls[*local].ty;
                        (vec![HirLoc::Global(*def_id)], LocCtx::new(ty))
                    }
                    _ => panic!(),
                }
            }
            MirLoc::Field(def_id, field) => {
                let hir::Node::Item(item) = tcx.hir_node_by_def_id(*def_id) else { panic!() };
                let adt_def = tcx.adt_def(*def_id);
                let ty = adt_def.variant(FIRST_VARIANT).fields[*field].ty(tcx, List::empty());
                let mut ctx = LocCtx::new(ty);
                ctx.is_union = matches!(item.kind, rustc_hir::ItemKind::Union(_, _, _));
                (vec![HirLoc::Field(*def_id, *field)], ctx)
            }
            _ => continue,
        };
        for hir_loc in &hir_locs {
            hir_loc_to_loc_id.insert(*hir_loc, loc_id);
        }
        loc_id_to_hir_locs[loc_id] = Some((hir_locs, ctx));
    }

    let mut param_flow: FxHashMap<Parameter, FxHashSet<Parameter>> = param_to_hir_loc
        .keys()
        .map(|p| (*p, FxHashSet::default()))
        .collect();
    for ((func, index), spans) in &hir_ctx.fn_param_to_arg_spans {
        let param = Parameter {
            func: *func,
            index: *index,
        };
        if !param_to_hir_loc.contains_key(&param) {
            continue;
        }
        let set = param_flow.get_mut(&param).unwrap();
        for span in spans {
            let loc = some_or!(hir_ctx.bound_span_to_loc.get(span), continue);
            let param = some_or!(hir_loc_to_param.get(loc), continue);
            set.insert(*param);
        }
    }
    let transitive_param_flow = utils::graph::transitive_closure(&param_flow);
    let non_generic_params: FxHashSet<_> = non_generic_params
        .into_iter()
        .flat_map(|param| {
            transitive_param_flow[&param]
                .iter()
                .copied()
                .chain(std::iter::once(param))
        })
        .collect();

    // is a global variable or a field assigned to this location without assigning
    // a local variable to the variable/field in the same function
    let mut non_local_assigns: FxHashSet<_> = FxHashSet::default();
    loop {
        let new_non_local_assigns: FxHashSet<_> = hir_loc_to_loc_id
            .keys()
            .copied()
            .filter(|hir_loc| {
                hir_ctx.rhs_locs_of_lhs(*hir_loc).any(|rhs| {
                    if non_local_assigns.contains(&rhs) {
                        return true;
                    }
                    match rhs {
                        HirLoc::Local(_) | HirLoc::Return(_) => return false,
                        HirLoc::Global(def_id) => {
                            let name = utils::ir::def_id_to_symbol(def_id, tcx).unwrap();
                            let name = name.as_str();
                            if name == "stdin" || name == "stdout" || name == "stderr" {
                                return false;
                            }
                        }
                        HirLoc::Field(_, _) => {}
                    }
                    if matches!(rhs, HirLoc::Local(_)) {
                        return false;
                    }
                    let HirLoc::Local(loc_id) = hir_loc else { return true };
                    // to handle `test_return_old_static`-like cases
                    !hir_ctx.rhs_locs_of_lhs(rhs).any(|rhs| {
                        let HirLoc::Local(hir_id) = rhs else { return false };
                        hir_id.owner == loc_id.owner
                    })
                })
            })
            .collect();
        if non_local_assigns == new_non_local_assigns {
            break;
        }
        non_local_assigns = new_non_local_assigns;
    }

    let arena = Arena::new();
    let type_arena = TypeArena::new(
        &arena,
        analysis_res.unsupported_stdout_errors || analysis_res.unsupported_stderr_errors,
    );
    let mut hir_loc_to_pot = FxHashMap::default();
    let mut uncopiable = vec![];
    for (loc_id, v) in loc_id_to_hir_locs.into_iter_enumerated() {
        let (hir_locs, mut ctx) = some_or!(v, continue);
        let permissions = analysis_res.permissions[loc_id];
        let origins = analysis_res.origins[loc_id];

        for hir_loc in hir_locs {
            if unsupported_locs.contains(&hir_loc) {
                continue;
            }

            ctx.is_non_local_assign |= non_local_assigns.contains(&hir_loc);

            if let Some(param) = hir_loc_to_param.get(&hir_loc)
                && !non_generic_params.contains(param)
            {
                ctx.is_generic = true;
            }

            if utils::file::file_param_index(ctx.ty, tcx).is_some() {
                ctx.is_param_without_assign = true;
            }

            let ty = type_arena.make_ty(permissions, origins, ctx, tcx);
            if !ty.is_copyable()
                && let HirLoc::Field(def_id, field) = hir_loc
            {
                uncopiable.push((def_id, field));
            }

            let pot = Pot {
                permissions,
                origins,
                ty,
                file_param_index: utils::file::file_param_index(ctx.ty, tcx),
            };
            let old = hir_loc_to_pot.insert(hir_loc, pot);
            if let Some(old) = old {
                assert_eq!(pot, old, "{hir_loc:?}");
            }
        }
    }

    for hir_loc in hir_ctx.loc_to_bound_spans.keys() {
        let HirLoc::Global(def_id) = hir_loc else { continue };
        let name = some_or!(utils::ir::def_id_to_symbol(*def_id, tcx), continue);
        let (loc, ty) = match name.as_str() {
            "stdin" => (MirLoc::Stdin, &STDIN_TY),
            "stdout" => (MirLoc::Stdout, &STDOUT_TY),
            "stderr" => (MirLoc::Stderr, &STDERR_TY),
            _ => continue,
        };
        let loc_id = analysis_res.loc_ind_map[&loc];
        hir_loc_to_loc_id.insert(*hir_loc, loc_id);
        let permissions = analysis_res.permissions[loc_id];
        let origins = analysis_res.origins[loc_id];
        let pot = Pot {
            permissions,
            origins,
            ty,
            file_param_index: None,
        };
        let old = hir_loc_to_pot.insert(*hir_loc, pot);
        assert!(old.is_none());
    }

    for param_loc in param_to_hir_loc.values() {
        let bound = some_or!(hir_ctx.loc_to_bound_spans.get(param_loc), continue);
        let mut tys = vec![];
        for rhs in bound {
            let lhs = some_or!(hir_ctx.rhs_to_lhs.get(rhs), continue);
            let lhs_loc = some_or!(hir_ctx.bound_span_to_loc.get(lhs), continue);
            let lhs_pot = some_or!(hir_loc_to_pot.get(lhs_loc), continue);
            tys.push(lhs_pot.ty);
        }
        let ty = some_or!(tys.pop(), continue);
        for t in tys {
            assert_eq!(ty, t);
        }
        let pot = hir_loc_to_pot.get_mut(param_loc).unwrap();
        pot.ty = ty;
    }

    let mut visited = FxHashSet::default();
    let mut work_list = uncopiable;
    let mut uncopiable: FxHashMap<_, Vec<_>> = FxHashMap::default();
    let mut uncopiable_union_fields = vec![];
    while let Some((def_id, field)) = work_list.pop() {
        if !visited.insert(def_id) {
            continue;
        }
        let node = tcx.hir_node_by_def_id(def_id);
        let hir::Node::Item(item) = node else { panic!() };
        uncopiable.entry(def_id).or_default().push(field);
        if matches!(item.kind, hir::ItemKind::Union(_, _, _)) {
            uncopiable_union_fields.push((def_id, field));
        }
        let owning_structs = some_or!(hir_ctx.struct_to_owning_structs.get(&def_id), continue);
        work_list.extend(owning_structs.iter().copied());
    }

    let mut manually_drop_projections: FxHashSet<Span> = FxHashSet::default();
    for (def_id, field) in uncopiable_union_fields {
        let loc = HirLoc::Field(def_id, field);
        if hir_loc_to_pot.contains_key(&loc) {
            continue;
        }
        let bounds = some_or!(hir_ctx.loc_to_bound_spans.get(&loc), continue);
        manually_drop_projections.extend(bounds);
    }

    let mut api_ident_spans = FxHashSet::default();

    for item_id in tcx.hir_free_items() {
        let item = tcx.hir_item(item_id);
        let local_def_id = item.owner_id.def_id;
        if let hir::ItemKind::Fn { ident, .. } = item.kind {
            if ident.name.as_str() == "main" {
                continue;
            }
            if analysis_res.defined_apis.contains(&local_def_id) {
                api_ident_spans.insert(ident.span);
            }
        }
    }

    let mut visitor = TransformVisitor {
        tcx,
        ast_to_hir,
        type_arena: &type_arena,
        analysis_res: &analysis_res,
        hir: &hir_ctx,
        config,

        error_returning_fns: &error_returning_fns,
        error_taking_fns: &error_taking_fns,
        tracked_loc_to_index: &tracked_loc_to_index,

        hir_loc_to_loc_id: &hir_loc_to_loc_id,

        param_to_loc: &param_to_hir_loc,
        loc_to_pot: &hir_loc_to_pot,
        api_ident_spans: &api_ident_spans,
        uncopiable: &uncopiable,
        manually_drop_projections: &manually_drop_projections,

        unsupported: &mut unsupported,
        unsupported_returns: &unsupported_returns,
        is_stdin_unsupported,
        is_stdout_unsupported,
        is_stderr_unsupported,

        tempfile: false,
        bytemuck: Cell::new(false),
        current_fns: vec![],
        bounds: FxHashSet::default(),
        bound_num: 0,
        lib_items: RefCell::new(FxHashSet::default()),
        parsing_fns: RefCell::new(FxHashMap::default()),
        guards: FxHashSet::default(),
        unsupported_reasons: vec![],
    };
    visitor.visit_crate(&mut krate);

    let transformation_time = start.elapsed().as_millis();

    let TransformVisitor {
        tempfile,
        bytemuck,
        bounds,
        bound_num,
        unsupported_reasons,
        parsing_fns,
        lib_items,
        ..
    } = visitor;
    let parsing_fns = parsing_fns.into_inner();
    let mut lib_items = lib_items.into_inner();

    if bounds
        .iter()
        .any(|bound| bound.contains(StreamTrait::AsRawFd))
    {
        lib_items.insert(LibItem::AsRawFd);
    }
    if bounds.iter().any(|bound| bound.contains(StreamTrait::Lock)) {
        lib_items.insert(LibItem::Lock);
    }
    if lib_items.contains(&LibItem::Child) && lib_items.contains(&LibItem::AsRawFd) {
        lib_items.insert(LibItem::ChildAsRawFd);
    }
    if lib_items.contains(&LibItem::Child) && lib_items.contains(&LibItem::Close) {
        lib_items.insert(LibItem::ChildClose);
    }

    krate.items.push(rustc_ast::ptr::P(stdio_mod(
        &bounds,
        &lib_items,
        &parsing_fns,
    )));

    if !krate.attrs.iter().any(|attr| {
        if let rustc_ast::AttrKind::Normal(attr) = &attr.kind
            && attr.item.path.segments.last().unwrap().ident.name == sym::feature
            && let Some(arg) = utils::ast::get_attr_arg(&attr.item.args)
            && arg.as_str() == "formatting_options"
        {
            true
        } else {
            false
        }
    }) {
        krate.attrs.push(utils::ast::make_inner_attribute(
            sym::feature,
            Symbol::intern("formatting_options"),
            tcx,
        ));
    }
    if !krate.attrs.iter().any(|attr| {
        if let rustc_ast::AttrKind::Normal(attr) = &attr.kind
            && attr.item.path.segments.last().unwrap().ident.name == sym::feature
            && let Some(arg) = utils::ast::get_attr_arg(&attr.item.args)
            && arg == sym::coverage_attribute
        {
            true
        } else {
            false
        }
    }) {
        krate.attrs.push(utils::ast::make_inner_attribute(
            sym::feature,
            sym::coverage_attribute,
            tcx,
        ));
    }

    let code = pprust::crate_to_string_for_macros(&krate);
    TransformationResult {
        code,
        tempfile,
        bytemuck: bytemuck.get(),
        unsupported_reasons,
        bound_num,
        transformation_time,
        analysis_stat: analysis_res.stat,
    }
}

fn stdio_mod(
    bounds: &FxHashSet<TraitBound>,
    lib_items: &FxHashSet<LibItem>,
    parsing_fns: &FxHashMap<String, String>,
) -> rustc_ast::Item {
    let mut m = "mod stdio {".to_string();
    m.push_str(
        r#"
        pub static mut STDOUT_ERROR: i32 = 0;
        pub static mut STDERR_ERROR: i32 = 0;
        unsafe extern "C" {
            #[link_name = "stdout"]
            pub static mut STDOUT: *mut std::ffi::c_void;
            #[link_name = "stderr"]
            pub static mut STDERR: *mut std::ffi::c_void;
        }
        "#,
    );
    for bound in bounds {
        if bound.count() <= 1 {
            continue;
        }
        write!(m, "pub trait {} : {}", bound.trait_name(), bound).unwrap();
        for other in bounds {
            if other.count() <= 1 {
                continue;
            }
            if bound != other && bound.superset(other) {
                write!(m, " + {}", other.trait_name()).unwrap();
            }
        }
        write!(
            m,
            "{{}} impl<T: {}> {} for T {{}}",
            bound,
            bound.trait_name(),
        )
        .unwrap();
    }
    for lib_item in lib_items {
        m.push_str(LIB_ITEMS[lib_item]);
    }
    for s in parsing_fns.values() {
        m.push_str(s);
    }
    m.push('}');
    utils::item!("{m}")
}

pub fn add_deps(dir: &std::path::Path, tempfile: bool, bytemuck: bool) {
    let path = dir.join("Cargo.toml");
    let content = fs::read_to_string(&path).unwrap();
    let mut doc = content.parse::<DocumentMut>().unwrap();
    let dependencies = doc["dependencies"].as_table_mut().unwrap();
    if tempfile && !dependencies.contains_key("tempfile") {
        dependencies["tempfile"] = toml_edit::value("3.19.1");
    }
    if bytemuck && !dependencies.contains_key("bytemuck") {
        dependencies["bytemuck"] = toml_edit::value("1.24.0");
    }
    fs::write(path, doc.to_string()).unwrap();
}

fn mir_local_span(
    def_id: LocalDefId,
    local: mir::Local,
    return_locals: &FxHashMap<LocalDefId, HirId>,
    hir_ctx: &HirCtx,
    tcx: TyCtxt<'_>,
) -> Span {
    let node = tcx.hir_node_by_def_id(def_id);
    let hir::Node::Item(item) = node else { panic!() };
    let body = match item.kind {
        hir::ItemKind::Fn { .. } => {
            if local == mir::Local::ZERO
                && let Some(hir_id) = return_locals.get(&def_id)
            {
                let loc = HirLoc::Local(*hir_id);
                return hir_ctx.loc_to_binding_span[&loc];
            }
            tcx.optimized_mir(def_id)
        }
        hir::ItemKind::Static(_, ident, _, _) => {
            if local == mir::Local::ZERO {
                return ident.span;
            }
            tcx.mir_for_ctfe(def_id)
        }
        _ => panic!(),
    };
    let local_decl = &body.local_decls[local];
    local_decl.source_info.span
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum LibItem {
    Peek,
    IsEof,
    ParseChar,
    ParseScanSet,
    ParseString,
    ParseF32,
    ParseF64,
    ParseF128,
    ParseFloat,
    ParseDecimal,
    ParseOctal,
    ParseInteger,
    ParseIntState,
    ParseHexadecimal,
    ParseIntegerAuto,
    Fprintf,
    Vfprintf,
    Xu8,
    Xu16,
    Xu32,
    Xu64,
    Gf64,
    Af64,
    Fgetc,
    Fgets,
    Getdelim,
    Getline,
    Fread,
    Fputc,
    Fputwc,
    Fputs,
    FputsUnchecked,
    Puts,
    Perror,
    Fwrite,
    FwriteUnchecked,
    Fflush,
    Seek,
    Fseek,
    Ftell,
    Rewind,
    Rename,
    Remove,
    Lock,
    Fopen,
    AsRawFd,
    Close,
    Child,
    ChildAsRawFd,
    ChildClose,
}

static LIB_ITEMS_ARRAY: [(LibItem, &str); 50] = [
    (LibItem::Peek, super::fscanf::PEEK),
    (LibItem::IsEof, super::fscanf::IS_EOF),
    (LibItem::ParseChar, super::fscanf::PARSE_CHAR),
    (LibItem::ParseScanSet, super::fscanf::PARSE_SCAN_SET),
    (LibItem::ParseString, super::fscanf::PARSE_STRING),
    (LibItem::ParseF32, super::fscanf::PARSE_F32),
    (LibItem::ParseF64, super::fscanf::PARSE_F64),
    (LibItem::ParseF128, super::fscanf::PARSE_F128),
    (LibItem::ParseFloat, super::fscanf::PARSE_FLOAT),
    (LibItem::ParseDecimal, super::fscanf::PARSE_DECIMAL),
    (LibItem::ParseOctal, super::fscanf::PARSE_OCTAL),
    (LibItem::ParseInteger, super::fscanf::PARSE_INTEGER),
    (LibItem::ParseIntState, super::fscanf::PARSE_INT_STATE),
    (LibItem::ParseHexadecimal, super::fscanf::PARSE_HEXADECIMAL),
    (LibItem::ParseIntegerAuto, super::fscanf::PARSE_INTEGER_AUTO),
    (LibItem::Fprintf, super::fprintf::FPRINTF),
    (LibItem::Vfprintf, super::fprintf::VFPRINTF),
    (LibItem::Xu8, super::fprintf::XU8),
    (LibItem::Xu16, super::fprintf::XU16),
    (LibItem::Xu32, super::fprintf::XU32),
    (LibItem::Xu64, super::fprintf::XU64),
    (LibItem::Gf64, super::fprintf::GF64),
    (LibItem::Af64, super::fprintf::AF64),
    (LibItem::Fgetc, super::fgetc::FGETC),
    (LibItem::Fgets, super::fgets::FGETS),
    (LibItem::Getdelim, super::getdelim::GETDELIM),
    (LibItem::Getline, super::getdelim::GETLINE),
    (LibItem::Fread, super::fread::FREAD),
    (LibItem::Fputc, super::fputc::FPUTC),
    (LibItem::Fputwc, super::fputc::FWPUTC),
    (LibItem::Fputs, super::fputs::FPUTS),
    (LibItem::FputsUnchecked, super::fputs::FPUTS_UNCHECKED),
    (LibItem::Puts, super::fputs::PUTS),
    (LibItem::Perror, super::fputs::PERROR),
    (LibItem::Fwrite, super::fwrite::FWRITE),
    (LibItem::FwriteUnchecked, super::fwrite::FWRITE_UNCHECKED),
    (LibItem::Fflush, super::fflush::FFLUSH),
    (LibItem::Seek, super::fseek::SEEK),
    (LibItem::Fseek, super::fseek::FSEEK),
    (LibItem::Ftell, super::fseek::FTELL),
    (LibItem::Rewind, super::fseek::REWIND),
    (LibItem::Rename, super::visitor::RENAME),
    (LibItem::Remove, super::visitor::REMOVE),
    (LibItem::Lock, super::flockfile::LOCK),
    (LibItem::Fopen, super::fopen::FOPEN),
    (LibItem::AsRawFd, super::fileno::AS_RAW_FD),
    (LibItem::Close, super::close::CLOSE),
    (LibItem::Child, super::popen::CHILD),
    (LibItem::ChildAsRawFd, super::popen::CHILD_AS_RAW_FD),
    (LibItem::ChildClose, super::popen::CHILD_CLOSE),
];

lazy_static! {
    static ref LIB_ITEMS: FxHashMap<LibItem, &'static str> =
        LIB_ITEMS_ARRAY.iter().copied().collect();
}
