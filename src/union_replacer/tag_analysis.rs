use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Write,
    path::PathBuf,
};

use etrace::{ok_or, some_or};
use rustc_abi::{FieldIdx, VariantIdx};
use rustc_ast::{BindingMode, LitKind, Mutability};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    BinOpKind, Block, ByRef, Expr, ExprKind, HirId, ItemKind, MatchSource, Node, Pat, PatExpr,
    PatExprKind, PatKind, QPath, StmtKind, UnOp, VariantData,
    def::Res,
    definitions::DefPathDataName,
    intravisit::{self, Visitor as HVisitor},
};
use rustc_index::{IndexVec, bit_set::DenseBitSet};
use rustc_middle::{
    hir::nested_filter,
    mir::{
        AggregateKind, BasicBlock, BasicBlockData, Body, Const, HasLocalDecls, Local, LocalDecl,
        Location, Operand, Place, PlaceElem, ProjectionElem, Rvalue, Terminator, TerminatorKind,
        visit::{PlaceContext, Visitor as MVisitor},
    },
    ty::{List, Ty, TyCtxt, TyKind, TypeckResults},
};
use rustc_span::{BytePos, Span, Symbol, def_id::LocalDefId, source_map::Spanned};
use serde::Deserialize;
use typed_arena::Arena;

use super::{
    must_analysis::{
        analysis::{AnalysisContext, analyze_body},
        domains::{AbsInt, AbsMem, AccPath, Graph, Obj},
    },
    ty_finder,
    util::suggestion::{AstEdit::*, AstSuggestions},
};
use crate::{ast_util, points_to::andersen, ty_shape};

#[derive(Default, Debug, Clone, Deserialize)]
pub struct Config {
    #[serde(default)]
    pub points_to_file: Option<PathBuf>,
    #[serde(default)]
    pub targets: FxHashSet<String>,
}

#[derive(Default, Debug, Clone, Copy)]
pub struct Statistics {
    pub unions: usize,
    pub structs: usize,
    pub candidates: usize,
    pub bodies: usize,
    pub analyzed_bodies: usize,
    pub tagged_unions: usize,
    pub tagged_structs: usize,
    pub method_lines: usize,
    pub preparation: usize,
    pub may_analysis: usize,
    pub must_analysis: usize,
    pub transformation: usize,
    pub nums: Nums,
}

impl Statistics {
    pub fn show(&self) -> String {
        format!(
            "{} {} {} {} {} {} {} {} {} {} {}",
            self.unions,
            self.candidates,
            self.tagged_unions,
            self.preparation + self.may_analysis + self.must_analysis + self.transformation,
            self.bodies,
            self.analyzed_bodies,
            self.nums.get_tag_num
                + self.nums.set_tag_num
                + self.nums.get_variant_num
                + self.nums.set_variant_num,
            self.nums.get_tag_match_num
                + self.nums.get_variant_match_num
                + self.nums.set_variant_match_num,
            self.nums.get_tag_if_num + self.nums.get_variant_if_num + self.nums.set_variant_if_num,
            self.nums.set_tag_aggregate_num + self.nums.set_variant_aggregate_num,
            self.method_lines,
        )
    }
}

impl std::fmt::Display for Statistics {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} {} {} {} {} {} {} {} {} {} {} {} {}",
            self.unions,
            self.structs,
            self.candidates,
            self.bodies,
            self.analyzed_bodies,
            self.tagged_unions,
            self.tagged_structs,
            self.method_lines,
            self.preparation,
            self.may_analysis,
            self.must_analysis,
            self.transformation,
            self.nums,
        )
    }
}

pub fn analyze(conf: &Config, verbose: bool, tcx: TyCtxt<'_>) -> Statistics {
    let mut stat = Statistics::default();
    let start = std::time::Instant::now();

    let source_map = tcx.sess.source_map();

    let visitor = ty_finder::TyVisitor::new(tcx);
    let (local_tys, foreign_tys) = visitor.find_foreign_tys(tcx);
    let arena = Arena::new();
    // always use optimized mir in union_replacer for now
    let use_optimized_mir = true;
    let tss = ty_shape::get_ty_shapes(&arena, tcx, use_optimized_mir);

    let mut non_tag_fields = FxHashMap::default();
    for item_id in tcx.hir_free_items() {
        let item = tcx.hir_item(item_id);
        let body_id = match item.kind {
            ItemKind::Fn { body: body_id, .. } | ItemKind::Static(_, _, _, body_id) => body_id,
            _ => continue,
        };
        let body = tcx.hir_body(body_id);
        let typeck = tcx.typeck(item_id.owner_id.def_id);
        let mut visitor = FieldVisitor {
            tcx,
            typeck,
            fields: &mut non_tag_fields,
        };
        visitor.visit_body(body);
    }
    let non_tag_fields: FxHashMap<_, FxHashSet<_>> = non_tag_fields
        .into_iter()
        .map(|(s, symbols)| {
            let item = tcx.hir_expect_item(s);
            let ItemKind::Struct(_, _, VariantData::Struct { fields: fs, .. }) = item.kind else {
                unreachable!()
            };
            let fields = symbols
                .into_iter()
                .map(|sym| {
                    fs.iter()
                        .enumerate()
                        .find(|(_, f)| f.ident.name == sym)
                        .map(|(i, _)| FieldIdx::from_usize(i))
                        .unwrap()
                })
                .collect();
            (s, fields)
        })
        .collect();

    let mut num_unions = 0;
    let mut num_structs = 0;
    let mut structs = FxHashMap::default();
    let mut unions = vec![];
    let mut union_to_struct = FxHashMap::default();
    let mut ty_graph: FxHashMap<_, Vec<_>> = FxHashMap::default();
    for item_id in tcx.hir_free_items() {
        let item = tcx.hir_item(item_id);
        let local_def_id = item_id.owner_id.def_id;

        if local_tys.contains(&local_def_id)
            && matches!(
                item.kind,
                ItemKind::Struct(_, _, _) | ItemKind::Union(_, _, _)
            )
        {
            let adt_def = tcx.adt_def(local_def_id);
            let variant = adt_def.variant(VariantIdx::from_u32(0));
            for (i, field) in variant.fields.iter_enumerated() {
                let ty = field.ty(tcx, List::empty());
                let (ty, mut v) = some_or!(ty_to_proj(ty), continue);
                if local_tys.contains(&ty) {
                    v.push(AccElem::Field(i));
                    ty_graph.entry(ty).or_default().push((local_def_id, v));
                }
            }
        }

        if foreign_tys.contains(&local_def_id) {
            continue;
        }
        if !matches!(item.kind, ItemKind::Struct(_, _, _)) {
            if matches!(item.kind, ItemKind::Union(_, _, _)) {
                num_unions += 1;
            }
            continue;
        }
        num_structs += 1;
        let adt_def = tcx.adt_def(local_def_id);
        let variant = adt_def.variant(VariantIdx::from_u32(0));
        let non_tag_fields = non_tag_fields.get(&local_def_id);
        let mut int_fields: FxHashSet<_> = variant
            .fields
            .iter_enumerated()
            .filter(|(i, f)| {
                let ty = f.ty(tcx, List::empty());
                (ty.is_integral() || ty.is_bool())
                    && non_tag_fields.is_none_or(|fields| !fields.contains(i))
            })
            .map(|(i, _)| i)
            .collect();
        if let Some(bitfield) = tss.bitfields.get(&local_def_id) {
            int_fields.extend(bitfield.fields.keys());
        }
        if int_fields.is_empty() {
            continue;
        }
        let mut struct_unions = vec![];
        for (i, f) in variant.fields.iter_enumerated() {
            let TyKind::Adt(adt_def, _) = f.ty(tcx, List::empty()).kind() else { continue };
            if !adt_def.is_union() {
                continue;
            }
            let def_id = adt_def.did();
            let name = tcx.def_path(def_id).data.last().unwrap().data.name();
            let DefPathDataName::Named(name) = name else { continue };
            if !name.to_ident_string().starts_with("C2RustUnnamed") {
                continue;
            }
            let u = def_id.expect_local();
            if conf.targets.is_empty() || conf.targets.contains(&tcx.def_path_str(u)) {
                unions.push(u);
                union_to_struct.insert(u, (i, local_def_id));
                struct_unions.push((i, u));
            }
        }
        if !struct_unions.is_empty() {
            let info = StructInfo {
                int_fields,
                unions: struct_unions,
            };
            structs.insert(local_def_id, info);
        }
    }
    let paths_to_unions: Vec<_> = unions
        .iter()
        .map(|u| {
            let mut ps = FxHashMap::default();
            find_paths(
                *u,
                &mut vec![],
                &ty_graph,
                &mut FxHashSet::default(),
                &mut ps,
            );
            (*u, ps)
        })
        .collect();

    stat.unions = num_unions;
    stat.structs = num_structs;
    stat.candidates = unions.len();
    stat.preparation = start.elapsed().as_millis() as usize;

    if unions.is_empty() {
        if verbose {
            println!("No candidates");
        }
        return stat;
    }
    if verbose {
        println!("{} candidates:", unions.len());
        for u in &unions {
            println!("{u:?}");
        }
    }

    let start = std::time::Instant::now();
    let points_to_config = andersen::Config { use_optimized_mir };
    let pre = andersen::pre_analyze(&points_to_config, &tss, tcx);
    let solutions = if let Some(file) = &conf.points_to_file {
        let arr = std::fs::read(file).unwrap();
        andersen::deserialize_solutions(&arr)
    } else {
        andersen::analyze(&points_to_config, &pre, &tss, tcx)
    };
    let may_points_to = andersen::post_analyze(&points_to_config, pre, solutions, &tss, tcx);
    stat.may_analysis = start.elapsed().as_millis() as usize;

    if verbose {
        println!("Start analysis");
    }

    let start = std::time::Instant::now();
    let mut bodies = 0;
    let mut analyzed_bodies = 0;
    let mut union_uses: FxHashMap<_, UnionUse> = FxHashMap::default();
    let mut aggregates: FxHashMap<_, _> = FxHashMap::default();
    let mut field_values: FxHashMap<FieldAt, BTreeSet<Tag>> = FxHashMap::default();
    let mut access_in_matches: FxHashMap<_, Vec<_>> = FxHashMap::default();
    let mut access_in_ifs: FxHashMap<_, Vec<_>> = FxHashMap::default();
    let mut basic_blocks = FxHashMap::default();
    let mut locals: FxHashMap<_, FxHashMap<_, _>> = FxHashMap::default();
    for item_id in tcx.hir_free_items() {
        let item = tcx.hir_item(item_id);
        let local_def_id = item_id.owner_id.def_id;
        let (body_id, body) = match item.kind {
            ItemKind::Fn { body: body_id, .. } => (body_id, tcx.optimized_mir(local_def_id)),
            ItemKind::Static(_, _, _, body_id) => (body_id, tcx.mir_for_ctfe(local_def_id)),
            _ => continue,
        };
        bodies += 1;
        let hbody = tcx.hir_body(body_id);
        let mut visitor = MBodyVisitor::new(tcx, &body.local_decls, &structs, &unions);
        visitor.visit_body(body);
        let mut hvisitor = HBodyVisitor::new(tcx);
        hvisitor.visit_body(hbody);
        basic_blocks.insert(local_def_id, visitor.basic_blocks);
        let locals = locals.entry(local_def_id).or_default();
        for (local, local_def) in body.local_decls.iter_enumerated() {
            let hir_id = some_or!(hvisitor.bindings.get(&local_def.source_info.span), continue);
            locals.entry(*hir_id).or_insert(local);
        }
        if visitor.accesses.is_empty()
            && visitor.struct_accesses.is_empty()
            && visitor.aggregates.is_empty()
        {
            continue;
        }
        if !hvisitor.inits.is_empty() {
            for (local, location) in &visitor.inits {
                let span = body
                    .stmt_at(*location)
                    .either(|stmt| stmt.source_info.span, |term| term.source_info.span);
                let aggregate_span = some_or!(hvisitor.inits.get(&span), continue);
                aggregates.insert(*aggregate_span, (*local, *location));
            }
        }
        for (local, location) in visitor.aggregates.values().flatten() {
            let span = body
                .stmt_at(*location)
                .either(|stmt| stmt.source_info.span, |term| term.source_info.span);
            aggregates.entry(span).or_insert((*local, *location));
        }
        for a in &visitor.accesses {
            union_uses.entry(a.ty).or_default().insert_field(a.field);
        }
        let local_set: FxHashSet<_> = visitor
            .accesses
            .iter()
            .map(|a| a.local)
            .chain(visitor.struct_accesses.iter().copied())
            .chain(
                visitor
                    .aggregates
                    .values()
                    .flatten()
                    .map(|(local, _)| *local),
            )
            .collect();
        let mut locals = DenseBitSet::new_empty(body.local_decls.len());
        for l in local_set {
            locals.insert(l);
        }
        let mut local_to_unions: FxHashMap<_, Vec<_>> = FxHashMap::default();
        for i in locals.iter() {
            let local = &body.local_decls[i];
            let (local_def_id, elems) = some_or!(ty_to_proj(local.ty), continue);
            for (u, paths) in &paths_to_unions {
                let paths = some_or!(paths.get(&local_def_id), continue);
                let local_to_unions = local_to_unions.entry(*u).or_default();
                for p in paths {
                    let mut path: Vec<_> = elems.iter().copied().rev().collect();
                    path.extend(p);
                    local_to_unions.push((i, path));
                }
            }
        }
        let ctx = AnalysisContext {
            local_def_id,
            tss: &tss,
            may_points_to: &may_points_to,
            no_gc_locals: Some(&locals),
            gc: true,
        };
        if verbose {
            println!("{local_def_id:?}");
        }
        analyzed_bodies += 1;
        let states = analyze_body(body, ctx, tcx);
        let ctx = AccessCtx::new(&states.states, &local_to_unions, body, tcx);
        for access in visitor.accesses {
            let tags = if let Some(access_match) =
                access_in_match(access, &hvisitor.matches, &visitor.switches, ctx)
            {
                let tags = access_match.field_tags.clone();
                access_in_matches
                    .entry(access_match.match_span)
                    .or_default()
                    .push(access_match);
                tags
            } else {
                let accesses_if = access_in_if(access, &hvisitor.ifs, &visitor.ifs, ctx);
                // println!("accesses_if.len() = {}", accesses_if.len());
                let tags = accesses_if
                    .iter()
                    .flat_map(|a| a.field_tags.clone())
                    .collect();
                for access_if in accesses_if {
                    access_in_ifs
                        .entry(access_if.if_span)
                        .or_default()
                        .push(access_if);
                }
                tags
            };
            let span = body.source_info(access.location).span;
            for (f, ns) in tags {
                let vts = union_uses
                    .entry(access.ty)
                    .or_default()
                    .get_access_tags_mut(f);
                for n in ns {
                    vts.insert(access.field, n, span);
                }
            }
        }
        for (loc, mem) in states.states.iter().chain(states.out_states.iter()) {
            let Location {
                block,
                statement_index,
            } = *loc;
            let span = body.source_info(*loc).span;
            let g = mem.g();
            for (u, paths) in &local_to_unions {
                for (l, path) in paths {
                    let len = path.len();
                    let AccElem::Field(f) = path[len - 1] else { unreachable!() };
                    let objs = g.objs_at(*l, &path[..len - 1]);
                    for obj in objs {
                        let Obj::Struct(fs, _) = obj else { continue };
                        let v: Vec<_> = fs
                            .iter()
                            .filter_map(|(f, obj)| {
                                let Obj::Ptr(loc) = obj else { return None };
                                let obj = g.obj_at_location(loc)?;
                                let Obj::AtAddr(n) = obj else { return None };
                                Some((*f, n.clone()))
                            })
                            .collect();
                        for (f, n) in &v {
                            union_uses.entry(*u).or_default().insert_tags(*f, n.iter());
                            let field_at = FieldAt {
                                func: local_def_id,
                                location: *loc,
                                local: *l,
                                field: *f,
                            };
                            field_values
                                .entry(field_at)
                                .or_default()
                                .extend(n.iter().filter_map(|n| n.try_into().ok()).map(Tag));
                        }
                        if body.basic_blocks[block].statements.len() > statement_index {
                            continue;
                        }
                        let terminator = body.basic_blocks[block].terminator();
                        if hvisitor.set_exprs.contains(&terminator.source_info.span) {
                            continue;
                        }
                        let uv = fs
                            .get(&f)
                            .map(|obj| {
                                let Obj::Struct(fs, _) = obj else { return vec![] };
                                fs.keys().cloned().collect()
                            })
                            .unwrap_or_default();
                        if uv.len() == 1 {
                            let variant = uv[0];
                            for (f, ns) in &v {
                                let vts = union_uses.entry(*u).or_default().get_obj_tags_mut(*f);
                                for n in ns.as_set() {
                                    vts.insert(variant, n, span);
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    if verbose {
        println!("Analysis done");
    }

    stat.bodies = bodies;
    stat.analyzed_bodies = analyzed_bodies;

    let mut tagged_unions = FxHashMap::default();
    for (u, uu) in &union_uses {
        let (index_in_struct, struct_local_def_id) = union_to_struct[u];
        let int_fields = &structs[&struct_local_def_id].int_fields;
        if let Some((tag_index, mut variant_tags)) = uu.compute_tags(int_fields) {
            if verbose {
                println!("Union {u:?}");
                println!("Used fields: {:?}", uu.fields);
                println!("Tag field: {tag_index:?}");
            }
            let mut all_fields = uu.fields.clone();
            let mut all_tags = uu.tags[&tag_index].clone();
            let mut tag_variants = FxHashMap::default();
            for (variant, tags) in &variant_tags {
                for tag in tags {
                    all_tags.remove(tag);
                    tag_variants.insert(*tag, Some(*variant));
                }
                if verbose {
                    println!("  {variant:?}: {tags:?}");
                }
                all_fields.remove(variant);
            }
            let mut empty_tags = vec![];
            if !all_tags.is_empty() {
                if verbose {
                    println!("  {all_fields:?}: {all_tags:?}");
                }
                assert!(all_fields.len() <= 1, "{all_fields:?} {all_tags:?}");
                let tags: Vec<_> = all_tags.into_iter().collect();
                if let Some(variant) = all_fields.into_iter().next() {
                    for tag in &tags {
                        tag_variants.insert(*tag, Some(variant));
                    }
                    variant_tags.insert(variant, tags);
                } else {
                    for tag in &tags {
                        tag_variants.insert(*tag, None);
                    }
                    empty_tags.extend(tags);
                }
            }

            let item = tcx.hir_expect_item(*u);
            let ItemKind::Union(ident, _, VariantData::Struct { fields: fs, .. }) = item.kind
            else {
                unreachable!()
            };
            let name = ident.name.to_ident_string();
            let field_names: IndexVec<FieldIdx, _> =
                fs.iter().map(|f| f.ident.name.to_ident_string()).collect();
            let field_tys: IndexVec<FieldIdx, _> = fs
                .iter()
                .map(|f| source_map.span_to_snippet(f.ty.span).unwrap())
                .collect();
            let field_name_to_index = fs
                .iter()
                .enumerate()
                .map(|(i, f)| (f.ident.name.to_ident_string(), FieldIdx::from_usize(i)))
                .collect();
            let tu = TaggedUnion {
                local_def_id: *u,
                name,
                variant_tags,
                empty_tags,
                tag_variants,
                field_names,
                field_tys,
                field_name_to_index,
                struct_local_def_id,
                index_in_struct,
                tag_index,
            };
            tagged_unions.insert(*u, tu);
        } else {
            tracing::info!("Union {:?}", u);
            tracing::info!("Used fields: {:?}", uu.fields);
            tracing::info!("Tags: {:?}", uu.tags);
            tracing::info!("Access:");
            for (f, vts) in &uu.access_tags {
                tracing::info!("  Field {:?}", f);
                for (variant, vs) in &vts.tags {
                    tracing::info!("    Variant {:?}", variant);
                    for (n, spans) in vs {
                        tracing::info!("      Tag {}", n);
                        for span in spans {
                            tracing::info!("        {:?}", span);
                        }
                    }
                }
            }
            tracing::info!("Obj:");
            for (f, vts) in &uu.obj_tags {
                tracing::info!("  Field {:?}", f);
                for (variant, vs) in &vts.tags {
                    tracing::info!("    Variant {:?}", variant);
                    for (n, spans) in vs {
                        tracing::info!("      Tag {}", n);
                        for span in spans {
                            tracing::info!("        {:?}", span);
                        }
                    }
                }
            }
        }
    }

    stat.tagged_unions = tagged_unions.len();
    stat.must_analysis = start.elapsed().as_millis() as usize;

    if verbose {
        println!("Tagged unions");
        for u in tagged_unions.keys() {
            println!("{}", tcx.def_path_str(*u));
        }
        println!("Others");
        for u in &unions {
            if !tagged_unions.contains_key(u) {
                println!("{}", tcx.def_path_str(*u));
            }
        }
    }

    if tagged_unions.is_empty() {
        if verbose {
            println!("No tagged union identified");
        }
        return stat;
    }

    let start = std::time::Instant::now();

    access_in_matches.retain(|_, v| tagged_unions.contains_key(&v[0].access.ty));
    access_in_ifs.retain(|_, v| tagged_unions.contains_key(&v[0].access.ty));

    if verbose {
        println!("{} tagged unions identified", tagged_unions.len());
        println!("access_in_matches: {}", access_in_matches.len());
        println!("access_in_ifs: {}", access_in_ifs.len());
    }

    let mut tagged_structs = FxHashMap::default();
    for (u, tu) in &tagged_unions {
        let s = tu.struct_local_def_id;
        let ts = tagged_structs.entry(s).or_insert_with(|| {
            let item = tcx.hir_expect_item(s);
            let ItemKind::Struct(ident, _, VariantData::Struct { fields: fs, .. }) = item.kind
            else {
                unreachable!()
            };
            let name = ident.name.to_ident_string();
            let mut field_names: IndexVec<FieldIdx, _> =
                fs.iter().map(|f| f.ident.name.to_ident_string()).collect();
            if let Some(bitfield) = tss.bitfields.get(&s) {
                for _ in 0..bitfield.fields.len() {
                    let (name, _) = &bitfield.fields[&field_names.next_index()];
                    field_names.push(name.clone());
                }
            }
            TaggedStruct {
                local_def_id: s,
                name,
                tag_index: tu.tag_index,
                field_names,
                unions: vec![],
            }
        });
        assert_eq!(ts.tag_index, tu.tag_index);
        ts.unions.push((*u, tu.index_in_struct));
    }

    stat.tagged_structs = tagged_structs.len();

    let mut method_lines = 0;
    let mut suggestions = AstSuggestions::new(source_map);
    for (s, ts) in &tagged_structs {
        let item = tcx.hir_expect_item(*s);
        let ItemKind::Struct(ident, _, VariantData::Struct { fields: sfs, .. }) = item.kind else {
            unreachable!()
        };

        let (field_name, field_ty) = if let Some(field) = sfs.get(ts.tag_index.as_usize()) {
            // let span = source_map.span_extend_to_line(field.span); // REMOVED
            suggestions.add(item.span, RemoveFieldDef(field.span)); // shouldn't be extended to line

            let field_name = field.ident.name.to_ident_string();
            let field_ty = source_map.span_to_snippet(field.ty.span).unwrap();
            (field_name, field_ty)
        } else {
            let (name, ty) = tss.bitfields[s].fields[&ts.tag_index].clone();
            let mut lo = ident.span.hi() + BytePos(3);
            'l: for f in sfs {
                loop {
                    let attr_span = source_map.span_extend_to_line(f.span.with_lo(lo).with_hi(lo));
                    let code = source_map.span_to_snippet(attr_span).unwrap();
                    if code.contains(&format!("#[bitfield(name = \"{name}\"")) {
                        // WARINING: believing the span is exactly the field attribute
                        suggestions.add(f.span, RemoveFieldAttr(attr_span));
                        break 'l;
                    }
                    lo = attr_span.hi() + BytePos(1);
                    if attr_span.hi() >= f.span.hi() {
                        break;
                    }
                }
            }
            (name, ty)
        };

        let mut set_tag_method = format!(
            "
impl {} {{
    pub fn set_{}(&mut self, v: {}) {{",
            ts.name, field_name, field_ty,
        );
        for (n, (u, i)) in ts.unions.iter().enumerate() {
            let is_first_union = n == 0;
            let tu = &tagged_unions[u];
            let struct_field_name = &ts.field_names[*i];
            let item = tcx.hir_expect_item(*u);
            let ItemKind::Union(_, _, VariantData::Struct { fields: ufs, .. }) = item.kind else {
                unreachable!()
            };
            let tys: Vec<_> = ufs
                .iter()
                .map(|f| source_map.span_to_snippet(f.ty.span).unwrap().to_string())
                .collect();

            write!(
                &mut set_tag_method,
                "
        self.{struct_field_name} = match v {{"
            )
            .unwrap();
            let mut new_method = format!(
                "impl {} {{
    pub fn new(t: {}) -> Self {{
        match t {{",
                tu.name, field_ty,
            );
            let mut get_tag_method = format!(
                "impl {} {{
    pub fn {}(self) -> {} {{
        match self.{} {{",
                ts.name, field_name, field_ty, struct_field_name
            );
            let mut field_methods = "".to_string();
            let mut enum_str = format!("pub enum {} {{", tu.name);
            for (field, tags) in &tu.variant_tags {
                let field_name = ufs[field.as_usize()].ident.name.to_ident_string();
                let ty = &tys[field.as_usize()];
                let pattern: String = tags
                    .iter()
                    .map(|tag| format!("{}::{}{}(v)", tu.name, field_name, tag))
                    .intersperse(" | ".to_string())
                    .collect();
                writeln!(
                    &mut field_methods,
                    "impl {} {{
    pub fn get_{}(self) -> {} {{
        if let {} = self {{
            v
        }} else {{
            panic!()
        }}
    }}
}}",
                    tu.name, field_name, ty, pattern,
                )
                .unwrap();
                if tags.len() == 1 {
                    let t = tags[0];
                    writeln!(
                        &mut field_methods,
                        "impl {} {{
    pub fn deref_{}_mut(&mut self) -> *mut {} {{
        if !matches!(self, {}) {{
            let v = unsafe {{ std::mem::transmute([0u8; std::mem::size_of::<{}>()]) }};
            *self = Self::{}{}(v);
        }}
        if let {} = self {{
            v as _
        }} else {{
            panic!()
        }}
    }}
}}",
                        tu.name, field_name, ty, pattern, ty, field_name, t, pattern,
                    )
                    .unwrap();
                } else {
                    let mut arms = "".to_string();
                    for t in tags {
                        write!(
                            &mut arms,
                            "
                {} => {}::{}{}(v),",
                            tag_to_string(*t, &field_ty),
                            tu.name,
                            field_name,
                            t
                        )
                        .unwrap();
                    }
                    let default = format!("{}::{}{}(v)", tu.name, field_name, tags[0],);
                    writeln!(
                        &mut field_methods,
                        "impl {} {{
    pub fn deref_{}_mut(&mut self, t: {}) -> *mut {} {{
        if !matches!(self, {}) {{
            let v = unsafe {{ std::mem::transmute([0u8; std::mem::size_of::<{}>()]) }};
            *self = match t {{{}
                _ => {},
            }};
        }}
        if let {} = self {{
            v as _
        }} else {{
            panic!()
        }}
    }}
}}",
                        tu.name, field_name, field_ty, ty, pattern, ty, arms, default, pattern,
                    )
                    .unwrap();
                }
                for t in tags {
                    let variant_name = format!("{field_name}{t}");
                    write!(
                        &mut set_tag_method,
                        "
            {} => {{
                let v = if let {} = self.{} {{
                    v
                }} else {{
                    unsafe {{ std::mem::transmute([0u8; std::mem::size_of::<{}>()]) }}
                }};
                {}::{}(v)
            }}",
                        tag_to_string(*t, &field_ty),
                        pattern,
                        struct_field_name,
                        ty,
                        tu.name,
                        variant_name
                    )
                    .unwrap();
                    write!(
                        &mut new_method,
                        "
            {} => Self::{}(unsafe {{ std::mem::transmute([0u8; std::mem::size_of::<{}>()]) }}),",
                        tag_to_string(*t, &field_ty),
                        variant_name,
                        ty
                    )
                    .unwrap();
                    write!(
                        &mut get_tag_method,
                        "
            {}::{}(_) => {},",
                        tu.name,
                        variant_name,
                        tag_to_string(*t, &field_ty),
                    )
                    .unwrap();
                    write!(
                        &mut enum_str,
                        "
    {variant_name}({ty}),"
                    )
                    .unwrap();
                }
            }
            for t in &tu.empty_tags {
                let variant_name = format!("Empty{t}");
                write!(
                    &mut set_tag_method,
                    "
            {} => {}::{},",
                    tag_to_string(*t, &field_ty),
                    tu.name,
                    variant_name
                )
                .unwrap();
                write!(
                    &mut new_method,
                    "
            {} => Self::{},",
                    tag_to_string(*t, &field_ty),
                    variant_name,
                )
                .unwrap();
                write!(
                    &mut get_tag_method,
                    "
            {}::{} => {},",
                    tu.name,
                    variant_name,
                    tag_to_string(*t, &field_ty),
                )
                .unwrap();
                write!(
                    &mut enum_str,
                    "
    {variant_name},"
                )
                .unwrap();
            }
            set_tag_method.push_str(
                "
            _ => panic!()
        };",
            );
            new_method.push_str(
                "
            _ => panic!(),
        }
    }
}",
            );
            get_tag_method.push_str(
                "
        }
    }
}",
            );
            enum_str.push_str("\n}");

            let method_str = format!(
                "{}\n{}\n{}\n{}",
                enum_str,
                new_method,
                field_methods,
                if is_first_union { &get_tag_method } else { "" },
            );
            method_lines += method_str.split('\n').count();
            suggestions.add(item.span, FlatMapItemsWithAttrs(items!("{}", method_str)));
        }

        set_tag_method.push_str(
            "
    }
}",
        );
        method_lines += set_tag_method.split('\n').count();
        suggestions.add(item.span, AppendAfterItem(item!("{}", set_tag_method)));
    }
    stat.method_lines = method_lines;

    let mut nums = Nums::default();
    for item_id in tcx.hir_free_items() {
        let item = tcx.hir_item(item_id);
        let (ItemKind::Fn { body: body_id, .. } | ItemKind::Static(_, _, _, body_id)) = item.kind
        else {
            continue;
        };
        let hir_body = tcx.hir_body(body_id);
        let local_def_id = item_id.owner_id.def_id;
        let typeck = tcx.typeck(local_def_id);
        let mut visitor = SuggestingVisitor {
            tcx,
            typeck,
            func: local_def_id,
            aggregates: &aggregates,
            field_values: &field_values,
            structs: &tagged_structs,
            unions: &tagged_unions,
            access_in_matches: &access_in_matches,
            access_in_ifs: &access_in_ifs,
            basic_blocks: &basic_blocks[&local_def_id],
            hir_id_to_locals: &locals[&local_def_id],
            suggestions: &mut suggestions,

            locals: FxHashMap::default(),
            match_targets: FxHashMap::default(),
            if_targets: FxHashMap::default(),
            aggregate_spans: vec![],

            nums: Nums::default(),
        };
        visitor.visit_body(hir_body);
        nums += visitor.nums;
    }
    stat.nums = nums;

    for (path, suggestion_vec) in &mut suggestions.suggestions {
        tracing::info!("{:?}", path);
        suggestion_vec.sort_by_key(|s| s.span.lo());
        for suggestion in suggestion_vec {
            tracing::info!("{:?}", suggestion);
        }
    }

    let mut trans_visitor = suggestions.into_transform_visitor();
    let res = ast_util::transform_ast(
        |krate| {
            trans_visitor.transform(krate);
            trans_visitor.updated
        },
        tcx,
    );
    trans_visitor.assert_finished();
    res.apply();

    stat.transformation = start.elapsed().as_millis() as usize;
    stat
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(super) struct Tag(i32);

impl std::fmt::Debug for Tag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::fmt::Display for Tag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0 < 0 {
            write!(f, "_m{}", self.0.abs())
        } else {
            write!(f, "{}", self.0)
        }
    }
}

#[derive(Debug, Default)]
struct UnionUse {
    fields: BTreeSet<FieldIdx>,
    tags: BTreeMap<FieldIdx, BTreeSet<Tag>>,
    access_tags: BTreeMap<FieldIdx, VariantTags>,
    obj_tags: BTreeMap<FieldIdx, VariantTags>,
}

impl UnionUse {
    #[inline]
    fn insert_field(&mut self, field: FieldIdx) {
        self.fields.insert(field);
    }

    #[inline]
    fn insert_tags<T: TryInto<i32>, S: IntoIterator<Item = T>>(
        &mut self,
        field: FieldIdx,
        tags: S,
    ) {
        self.tags
            .entry(field)
            .or_default()
            .extend(tags.into_iter().filter_map(|t| t.try_into().ok().map(Tag)));
    }

    #[inline]
    fn get_access_tags_mut(&mut self, field: FieldIdx) -> &mut VariantTags {
        self.access_tags.entry(field).or_default()
    }

    #[inline]
    fn get_obj_tags_mut(&mut self, field: FieldIdx) -> &mut VariantTags {
        self.obj_tags.entry(field).or_default()
    }

    fn compute_tags(
        &self,
        int_fields: &FxHashSet<FieldIdx>,
    ) -> Option<(FieldIdx, BTreeMap<FieldIdx, Vec<Tag>>)> {
        let fs: FxHashSet<_> = self
            .access_tags
            .keys()
            .chain(self.obj_tags.keys())
            .copied()
            .collect();
        fs.iter()
            .filter_map(|f| {
                if !int_fields.contains(f) {
                    return None;
                }
                let tags = match (self.access_tags.get(f), self.obj_tags.get(f)) {
                    (Some(ts1), Some(ts2)) => {
                        let mut tags = ts1.compute_tags()?;
                        if !ts2.compute_tags_with(&mut tags) {
                            return None;
                        }
                        tags
                    }
                    (Some(ts), None) | (None, Some(ts)) => ts.compute_tags()?,
                    _ => unreachable!(),
                };
                if tags.len() <= 1 {
                    None
                } else {
                    Some((*f, tags))
                }
            })
            .max_by_key(|(_, tags)| tags.len())
    }
}

#[derive(Debug, Default)]
struct VariantTags {
    tags: BTreeMap<FieldIdx, BTreeMap<Tag, Vec<Span>>>,
}

impl VariantTags {
    #[inline]
    fn insert<T: TryInto<i32>>(&mut self, field: FieldIdx, tag: T, span: Span) {
        let tag = ok_or!(tag.try_into(), return);

        // NOTE: Negative tags are not supported. In some cases, a field may
        // serve dual purposes: it acts as a tag when negative and as a regular
        // field when non-negative.  For example, in the `Colamd_Col_Struct`
        // struct from glpk-5.0, the `start` field is set to `-1` or `-2` when
        // acting as a tag for the union `C2RustUnnamed_4`.  When positive, it
        // represents a normal start index.  Since we don't currently handle
        // this tag/field duality, we ignore negative tags.
        if tag < 0 {
            tracing::warn!("Ignoring negative tag: {}", tag);
            return;
        }

        self.tags
            .entry(field)
            .or_default()
            .entry(Tag(tag))
            .or_default()
            .push(span);
    }

    fn compute_tags(&self) -> Option<BTreeMap<FieldIdx, Vec<Tag>>> {
        let mut all_tags = FxHashSet::default();
        let mut field_tags = BTreeMap::new();
        for (f, tags) in &self.tags {
            if tags.is_empty() {
                continue;
            }
            for t in tags.keys() {
                if !all_tags.insert(*t) {
                    return None;
                }
            }
            field_tags.insert(*f, tags.keys().copied().collect());
        }
        Some(field_tags)
    }

    fn compute_tags_with(&self, field_tags: &mut BTreeMap<FieldIdx, Vec<Tag>>) -> bool {
        let existing_tags: FxHashSet<_> = field_tags.values().flatten().copied().collect();
        let mut new_tags = FxHashSet::default();
        for (f, tags) in &self.tags {
            let v: Vec<_> = tags
                .keys()
                .copied()
                .filter(|t| !existing_tags.contains(t))
                .collect();
            if v.is_empty() {
                continue;
            }
            for t in &v {
                if !new_tags.insert(*t) {
                    return false;
                }
            }
            field_tags.entry(*f).or_default().extend(v);
        }
        true
    }
}

#[derive(Debug, Clone, Copy)]
pub enum AccElem {
    Field(FieldIdx),
    Index,
    Deref,
}

fn ty_to_proj(ty: Ty<'_>) -> Option<(LocalDefId, Vec<AccElem>)> {
    match ty.kind() {
        TyKind::Adt(adt_def, _) => {
            let def_id = adt_def.did().as_local()?;
            Some((def_id, vec![]))
        }
        TyKind::Array(ty, _) => {
            let (def_id, mut v) = ty_to_proj(*ty)?;
            v.push(AccElem::Index);
            Some((def_id, v))
        }
        TyKind::Ref(_, ty, _) | TyKind::RawPtr(ty, ..) => {
            let (def_id, mut v) = ty_to_proj(*ty)?;
            v.push(AccElem::Deref);
            Some((def_id, v))
        }
        _ => None,
    }
}

fn find_paths(
    curr: LocalDefId,
    path: &mut Vec<AccElem>,
    graph: &FxHashMap<LocalDefId, Vec<(LocalDefId, Vec<AccElem>)>>,
    visited: &mut FxHashSet<LocalDefId>,
    paths: &mut FxHashMap<LocalDefId, Vec<Vec<AccElem>>>,
) {
    if visited.contains(&curr) {
        return;
    }

    if !path.is_empty() {
        let p = path.iter().copied().rev().collect();
        paths.entry(curr).or_default().push(p);
    }

    visited.insert(curr);
    let succs = some_or!(graph.get(&curr), return);
    for (succ, elems) in succs {
        path.extend(elems);
        find_paths(*succ, path, graph, visited, paths);
        for _ in elems {
            path.pop();
        }
    }
    visited.remove(&curr);
}

type ArmTags = Option<BTreeSet<i128>>;

struct MIf {
    c: Span,
    loc: Location,
    t: BasicBlock,
    f: BasicBlock,
}

struct MBodyVisitor<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    local_decls: &'a IndexVec<Local, LocalDecl<'tcx>>,
    structs: &'a FxHashMap<LocalDefId, StructInfo>,
    unions: &'a Vec<LocalDefId>,
    accesses: Vec<FieldAccess<'tcx>>,
    struct_accesses: FxHashSet<Local>,
    aggregates: FxHashMap<LocalDefId, Vec<(Local, Location)>>,
    inits: Vec<(Local, Location)>,
    switches: FxHashMap<BytePos, (Location, FxHashMap<ArmTags, BasicBlock>)>,
    ifs: Vec<MIf>,
    basic_blocks: Vec<(Span, Location)>,
}

impl<'tcx, 'a> MBodyVisitor<'tcx, 'a> {
    fn new(
        tcx: TyCtxt<'tcx>,
        local_decls: &'a IndexVec<Local, LocalDecl<'tcx>>,
        structs: &'a FxHashMap<LocalDefId, StructInfo>,
        unions: &'a Vec<LocalDefId>,
    ) -> Self {
        Self {
            tcx,
            local_decls,
            structs,
            unions,
            accesses: vec![],
            struct_accesses: FxHashSet::default(),
            aggregates: FxHashMap::default(),
            inits: vec![],
            switches: FxHashMap::default(),
            ifs: vec![],
            basic_blocks: vec![],
        }
    }
}

impl<'tcx> MVisitor<'tcx> for MBodyVisitor<'tcx, '_> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        if !place.projection.is_empty() {
            for i in 0..(place.projection.len() - 1) {
                let ty = Place::ty_from(
                    place.local,
                    &place.projection[..=i],
                    self.local_decls,
                    self.tcx,
                )
                .ty;
                let TyKind::Adt(adt_def, _) = ty.kind() else { continue };
                let def_id = some_or!(adt_def.did().as_local(), continue);
                if self.structs.contains_key(&def_id) {
                    self.struct_accesses.insert(place.local);
                } else if self.unions.contains(&def_id) {
                    let ProjectionElem::Field(f, _) = place.projection[i + 1] else {
                        unreachable!()
                    };
                    let access = FieldAccess {
                        ty: def_id,
                        local: place.local,
                        projection: &place.projection[..=i],
                        field: f,
                        location,
                    };
                    self.accesses.push(access);
                }
            }
        }
        self.super_place(place, context, location);
    }

    fn visit_assign(&mut self, place: &Place<'tcx>, rvalue: &Rvalue<'tcx>, location: Location) {
        match rvalue {
            Rvalue::Aggregate(box AggregateKind::Adt(def_id, _, _, _, _), _) => {
                if let Some(def_id) = def_id.as_local()
                    && (self.structs.contains_key(&def_id) || self.unions.contains(&def_id))
                {
                    self.aggregates
                        .entry(def_id)
                        .or_default()
                        .push((place.local, location));
                }
            }
            Rvalue::Use(Operand::Copy(_) | Operand::Move(_)) => {
                let ty = Place::ty(place, self.local_decls, self.tcx).ty;
                if let TyKind::Adt(adt_def, _) = ty.kind() {
                    let def_id = adt_def.did();
                    if let Some(def_id) = def_id.as_local()
                        && place.projection.is_empty()
                        && self.structs.contains_key(&def_id)
                    {
                        self.inits.push((place.local, location));
                    }
                }
            }
            _ => {}
        }
        self.super_assign(place, rvalue, location);
    }

    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, location: Location) {
        match &terminator.kind {
            TerminatorKind::Call { func, args, .. } => {
                if let Some(constant) = func.constant() {
                    let Const::Val(_, ty) = constant.const_ else { unreachable!() };
                    let TyKind::FnDef(def_id, _) = ty.kind() else { unreachable!() };
                    if def_id.is_local() && self.tcx.impl_of_method(*def_id).is_some() {
                        let ty = args[0].node.ty(self.local_decls, self.tcx);
                        let TyKind::Ref(_, ty, _) = ty.kind() else { unreachable!() };
                        let TyKind::Adt(adt_def, _) = ty.kind() else { unreachable!() };
                        let local_def_id = adt_def.did().expect_local();
                        if self.structs.contains_key(&local_def_id) {
                            self.struct_accesses
                                .insert(args[0].node.place().unwrap().local);
                        }
                    }
                }
            }
            TerminatorKind::SwitchInt { discr, targets } => {
                let span = terminator.source_info.span;
                let ty = discr.ty(self.local_decls, self.tcx);

                // It still can be `if` though ty is integral
                if ty.is_bool() {
                    let mut targets_iter = targets.iter();
                    let (tag, bb) = targets_iter.next().unwrap();
                    assert!(targets_iter.next().is_none());
                    assert_eq!(tag, 0);
                    let mif = MIf {
                        c: span,
                        loc: location,
                        t: targets.otherwise(),
                        f: bb,
                    };
                    self.ifs.push(mif);
                }
                if ty.is_integral() {
                    let mut targets_iter = targets.iter();
                    let (_tag, bb) = targets_iter.next().unwrap();
                    if targets_iter.next().is_none() {
                        // This is a simple if, not a switch
                        let mif = MIf {
                            c: span,
                            loc: location,
                            t: bb,
                            f: targets.otherwise(),
                        };
                        self.ifs.push(mif);
                    }
                }
                if !ty.is_bool() {
                    let mut tags: FxHashMap<_, BTreeSet<_>> = FxHashMap::default();
                    for (tag, bb) in targets.iter() {
                        tags.entry(bb).or_default().insert(tag as i128);
                    }
                    tags.remove(&targets.otherwise());
                    let mut ts: FxHashMap<_, _> =
                        tags.into_iter().map(|(k, v)| (Some(v), k)).collect();
                    ts.insert(None, targets.otherwise());
                    self.switches.insert(span.hi(), (location, ts));
                }
            }
            _ => {}
        }
        self.super_terminator(terminator, location);
    }

    fn visit_basic_block_data(&mut self, block: BasicBlock, data: &BasicBlockData<'tcx>) {
        let spans = data.statements.iter().map(|stmt| stmt.source_info.span);
        let term = data.terminator();
        let spans: Box<dyn Iterator<Item = Span>> =
            if matches!(term.kind, TerminatorKind::Call { .. }) {
                Box::new(spans.chain(std::iter::once(term.source_info.span)))
            } else {
                Box::new(spans)
            };
        if let Some(span) = spans.reduce(|span1, span2| {
            let lo = span1.lo().min(span2.lo());
            let hi = span1.hi().max(span2.hi());
            span1.with_lo(lo).with_hi(hi)
        }) {
            let span = span.with_hi(span.hi() + BytePos(1));
            let location = Location {
                block,
                statement_index: data.statements.len(),
            };
            self.basic_blocks.push((span, location));
        }
        self.super_basic_block_data(block, data);
    }
}

#[derive(Debug, Clone, Copy)]
struct FieldAccess<'tcx> {
    ty: LocalDefId,
    local: Local,
    projection: &'tcx [PlaceElem<'tcx>],
    field: FieldIdx,
    location: Location,
}

impl<'tcx> FieldAccess<'tcx> {
    fn get_path<D: HasLocalDecls<'tcx> + ?Sized>(
        &self,
        state: &AbsMem,
        local_decls: &D,
        tcx: TyCtxt<'tcx>,
    ) -> (AccPath, bool) {
        assert!(!self.projection.is_empty());
        AccPath::from_local_projection(
            self.local,
            &self.projection[..self.projection.len() - 1],
            state,
            local_decls,
            tcx,
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct FieldAt {
    func: LocalDefId,
    location: Location,
    local: Local,
    field: FieldIdx,
}

struct StructInfo {
    int_fields: FxHashSet<FieldIdx>,
    #[allow(unused)]
    unions: Vec<(FieldIdx, LocalDefId)>,
}

struct TaggedStruct {
    #[allow(dead_code)]
    local_def_id: LocalDefId,
    name: String,
    tag_index: FieldIdx,
    field_names: IndexVec<FieldIdx, String>,
    unions: Vec<(LocalDefId, FieldIdx)>,
}

struct TaggedUnion {
    #[allow(dead_code)]
    local_def_id: LocalDefId,
    name: String,
    variant_tags: BTreeMap<FieldIdx, Vec<Tag>>,
    empty_tags: Vec<Tag>,
    tag_variants: FxHashMap<Tag, Option<FieldIdx>>,
    field_names: IndexVec<FieldIdx, String>,
    field_tys: IndexVec<FieldIdx, String>,
    field_name_to_index: FxHashMap<String, FieldIdx>,
    struct_local_def_id: LocalDefId,
    index_in_struct: FieldIdx,
    tag_index: FieldIdx,
}

struct SuggestingVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck: &'a TypeckResults<'tcx>,
    func: LocalDefId,
    aggregates: &'a FxHashMap<Span, (Local, Location)>,
    field_values: &'a FxHashMap<FieldAt, BTreeSet<Tag>>,
    structs: &'a FxHashMap<LocalDefId, TaggedStruct>,
    unions: &'a FxHashMap<LocalDefId, TaggedUnion>,
    access_in_matches: &'a FxHashMap<Span, Vec<AccessInMatch<'tcx>>>,
    access_in_ifs: &'a FxHashMap<Span, Vec<AccessInIf<'tcx>>>,
    basic_blocks: &'a [(Span, Location)],
    hir_id_to_locals: &'a FxHashMap<HirId, Local>,
    suggestions: &'a mut AstSuggestions<'tcx>,

    locals: FxHashMap<HirId, &'tcx Expr<'tcx>>,
    match_targets: FxHashMap<Span, (String, Vec<Span>)>,
    if_targets: FxHashMap<Span, Option<String>>,
    aggregate_spans: Vec<Span>,

    nums: Nums,
}

#[derive(Default, Debug, Clone, Copy)]
pub struct Nums {
    pub match_num: usize,
    pub if_num: usize,
    pub aggregate_num: usize,

    pub new_num: usize,

    pub get_tag_num: usize,
    pub get_tag_match_num: usize,
    pub get_tag_if_num: usize,

    pub set_tag_num: usize,
    pub set_tag_aggregate_num: usize,

    pub get_variant_num: usize,
    pub get_variant_match_num: usize,
    pub get_variant_if_num: usize,

    pub set_variant_num: usize,
    pub set_variant_match_num: usize,
    pub set_variant_if_num: usize,
    pub set_variant_aggregate_num: usize,
}

impl std::fmt::Display for Nums {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} {} {} {} {} {} {} {} {} {} {} {} {} {} {} {}",
            self.match_num,
            self.if_num,
            self.aggregate_num,
            self.new_num,
            self.get_tag_num,
            self.get_tag_match_num,
            self.get_tag_if_num,
            self.set_tag_num,
            self.set_tag_aggregate_num,
            self.get_variant_num,
            self.get_variant_match_num,
            self.get_variant_if_num,
            self.set_variant_num,
            self.set_variant_match_num,
            self.set_variant_if_num,
            self.set_variant_aggregate_num,
        )
    }
}

impl std::ops::AddAssign for Nums {
    fn add_assign(&mut self, rhs: Self) {
        self.match_num += rhs.match_num;
        self.if_num += rhs.if_num;
        self.aggregate_num += rhs.aggregate_num;

        self.new_num += rhs.new_num;

        self.get_tag_num += rhs.get_tag_num;
        self.get_tag_match_num += rhs.get_tag_match_num;
        self.get_tag_if_num += rhs.get_tag_if_num;

        self.set_tag_num += rhs.set_tag_num;
        self.set_tag_aggregate_num += rhs.set_tag_aggregate_num;

        self.get_variant_num += rhs.get_variant_num;
        self.get_variant_match_num += rhs.get_variant_match_num;
        self.get_variant_if_num += rhs.get_variant_if_num;

        self.set_variant_num += rhs.set_variant_num;
        self.set_variant_match_num += rhs.set_variant_match_num;
        self.set_variant_if_num += rhs.set_variant_if_num;
        self.set_variant_aggregate_num += rhs.set_variant_aggregate_num;
    }
}

impl<'tcx> SuggestingVisitor<'_, 'tcx> {
    fn handle_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        let source_map = self.tcx.sess.source_map();

        if let Some(access) = self.access_in_matches.get(&expr.span) {
            let tu = &self.unions[&access[0].access.ty];
            let ts = &self.structs[&tu.struct_local_def_id];
            let union_field_name = &ts.field_names[tu.index_in_struct];

            let struct_expr = self.get_struct(expr).unwrap();
            let ty = self.typeck.expr_ty(struct_expr);
            let TyKind::Adt(adt_def, _) = ty.kind() else { unreachable!() };
            if adt_def.did().as_local() == Some(ts.local_def_id) {
                let struct_str = source_map.span_to_snippet(struct_expr.span).unwrap();
                self.suggestions.add(
                    expr.span,
                    ReplaceExpr(expr!("{}.{}", struct_str, union_field_name)),
                );

                let (root, derefs) = unwrap_deref(unwrap_projection(struct_expr));
                let root = if let ExprKind::Path(QPath::Resolved(_, path)) = root.kind {
                    if let Res::Local(hir_id) = path.res {
                        Some(hir_id)
                    } else {
                        None
                    }
                } else {
                    None
                };
                let is_const = is_from_const_ptr(expr, self.typeck);
                let match_expr = get_parent(expr, self.tcx).unwrap();
                let ExprKind::Match(_, arms, _) = match_expr.kind else { unreachable!() };
                let mut arm_spans = vec![];
                for arm in arms {
                    let span = arm.pat.span;
                    if let Some(tags) = pat_to_tags(arm.pat) {
                        let (pat, cast) = tags_to_pattern(tags.iter().copied(), is_const, tu);
                        self.suggestions.add(span, ReplacePat(pat!("{}", pat)));
                        if matches!(arm.body.kind, ExprKind::Block(_, _))
                            && let Some(cast) = cast
                        {
                            let span = arm.body.span; //.with_lo(pos).with_hi(pos);
                            self.suggestions
                                .add(span, PrependToBlock(stmt!("{}", cast)));
                        }
                    } else if source_map.span_to_snippet(arm.pat.span).unwrap() != "_" {
                        self.suggestions.add(arm.pat.span, ReplacePat(pat!("_")));
                    }
                    let has_assign = root
                        .map(|root| {
                            let mut visitor = AssignVisitor::new(self.tcx);
                            visitor.visit_expr(arm.body);
                            visitor
                                .assigns
                                .iter()
                                .any(|(hir_id, i)| root == *hir_id && *i < derefs)
                        })
                        .unwrap_or(false);
                    if !has_assign {
                        arm_spans.push(arm.body.span);
                    }
                }

                let normalized_struct_str = normalize_expr_str(&struct_str);
                self.match_targets
                    .insert(expr.span, (normalized_struct_str, arm_spans));
                self.nums.match_num += 1;
            }
        } else if let Some(access) = self.access_in_ifs.get(&expr.span)
            && let Some((field, tags)) = find_tag_from_accesses(access)
        {
            let tu = &self.unions[&access[0].access.ty];
            if field == tu.tag_index {
                let ts = &self.structs[&tu.struct_local_def_id];
                let union_field_name = &ts.field_names[tu.index_in_struct];
                if let Some(exprs) = self.decompose_expr(expr) {
                    let expr_strs: FxHashSet<_> = exprs
                        .iter()
                        .map(|e| {
                            let s = source_map.span_to_snippet(e.span).unwrap();
                            normalize_expr_str(&s)
                        })
                        .collect();
                    assert_eq!(expr_strs.len(), 1);
                    let struct_expr = exprs[0];
                    let ty = self.typeck.expr_ty(struct_expr);
                    let TyKind::Adt(adt_def, _) = ty.kind() else { unreachable!() };
                    if adt_def.did().as_local() == Some(ts.local_def_id) {
                        let (root, derefs) = unwrap_deref(unwrap_projection(struct_expr));
                        let root = if let ExprKind::Path(QPath::Resolved(_, path)) = root.kind {
                            if let Res::Local(hir_id) = path.res {
                                Some(hir_id)
                            } else {
                                None
                            }
                        } else {
                            None
                        };
                        let is_const = is_from_const_ptr(struct_expr, self.typeck);
                        let (pat, cast) = tags_to_pattern(tags.iter().copied(), is_const, tu);
                        self.suggestions.add(
                            expr.span,
                            ReplaceExpr(expr!(
                                "let {} = {}.{}",
                                pat,
                                source_map.span_to_snippet(struct_expr.span).unwrap(),
                                union_field_name,
                            )),
                        );

                        let if_expr = get_parent(expr, self.tcx).unwrap();
                        let ExprKind::If(_, t, _) = if_expr.kind else {
                            unreachable!("{:?}", if_expr)
                        };

                        if let Some(cast) = cast {
                            assert!(matches!(t.kind, ExprKind::Block(_, _)));
                            self.suggestions
                                .add(t.span, PrependToBlock(stmt!("{}", cast)));
                        }

                        let has_assign = root
                            .map(|root| {
                                let mut visitor = AssignVisitor::new(self.tcx);
                                visitor.visit_expr(t);
                                visitor
                                    .assigns
                                    .iter()
                                    .any(|(hir_id, i)| root == *hir_id && *i < derefs)
                            })
                            .unwrap_or(false);
                        let s = if has_assign {
                            None
                        } else {
                            Some(expr_strs.into_iter().next().unwrap())
                        };
                        self.if_targets.insert(expr.span, s);
                        self.nums.if_num += 1;
                    }
                } else {
                    tracing::info!(
                        "{:?} {}",
                        tags,
                        source_map.span_to_snippet(expr.span).unwrap(),
                    );
                }
            }
        }

        match expr.kind {
            ExprKind::Struct(_, fs, _) => {
                let TyKind::Adt(adt_def, _) = self.typeck.expr_ty(expr).kind() else {
                    unreachable!()
                };
                let def_id = some_or!(adt_def.did().as_local(), return);
                let ts = some_or!(self.structs.get(&def_id), return);

                let tag_expr = fs.get(ts.tag_index.as_usize()).and_then(|field| {
                    self.suggestions.add(expr.span, RemoveExprField(field.span));

                    source_map.span_to_snippet(field.expr.span).ok()
                });

                let (local, mut location) = self.aggregates[&expr.span];
                location.statement_index += 1;
                let field_at = FieldAt {
                    func: self.func,
                    location,
                    local,
                    field: ts.tag_index,
                };
                let tags = self.field_values.get(&field_at);

                for (u, i) in &ts.unions {
                    let tu = &self.unions[u];
                    let field_name = &ts.field_names[*i];
                    let expr = fs
                        .iter()
                        .find(|f| &f.ident.name.to_ident_string() == field_name)
                        .unwrap()
                        .expr;
                    let ExprKind::Struct(path, ufs, _) = expr.kind else { unreachable!() };
                    let union_name = source_map.span_to_snippet(path.span()).unwrap();
                    let QPath::Resolved(_, path) = path else { unreachable!() };
                    let Res::Def(_, def_id) = path.res else { unreachable!() };
                    assert_eq!(def_id.expect_local(), *u);
                    assert_eq!(ufs.len(), 1);
                    let name = ufs[0].ident.name.to_ident_string();
                    let span = ufs[0].expr.span;
                    let init = source_map.span_to_snippet(span).unwrap();
                    let v = if let Some(tags) = tags {
                        if tags.len() == 1 {
                            let tag = tags.iter().next().unwrap();
                            let i = tu.field_name_to_index[&name];
                            let tags_from_i = &tu.variant_tags[&i];
                            let tag = if tags_from_i.contains(tag) {
                                *tag
                            } else {
                                tags_from_i[0]
                            };
                            format!("{union_name}::{name}{tag}({init})")
                        } else {
                            format!("{}::new({})", union_name, tag_expr.as_ref().unwrap())
                        }
                    } else if let Some(tag_expr) = &tag_expr {
                        format!("{union_name}::new({tag_expr})")
                    } else {
                        let i = tu.field_name_to_index[&name];
                        let tag = tu.variant_tags[&i][0];
                        format!("{union_name}::{name}{tag}({init})")
                    };
                    if v.contains("::new(") {
                        self.nums.new_num += 1;
                    }
                    self.suggestions.add(expr.span, ReplaceExpr(expr!("{}", v)));
                }
            }
            ExprKind::Field(e, field) => {
                let ty = self.typeck.expr_ty(e);
                let TyKind::Adt(adt_def, _) = ty.kind() else { return };
                let did = some_or!(adt_def.did().as_local(), return);

                if let Some(ts) = self.structs.get(&did) {
                    let variant = adt_def.variant(VariantIdx::from_u32(0));
                    if let Some(field_def) = variant.fields.get(ts.tag_index)
                        && field_def.ident(self.tcx).name == field.name
                    {
                        let (ctx, e2) = get_expr_context(e, self.tcx);
                        match ctx {
                            ExprContext::Value => {
                                if self.match_targets.keys().any(|s| s.contains(e.span)) {
                                    self.nums.get_tag_match_num += 1;
                                } else if self.if_targets.keys().any(|s| s.contains(e.span)) {
                                    self.nums.get_tag_if_num += 1;
                                } else {
                                    let expr_str = source_map.span_to_snippet(expr.span).unwrap();
                                    self.suggestions
                                        .add(expr.span, ReplaceExpr(expr!("{}()", expr_str)));
                                    self.nums.get_tag_num += 1;
                                }
                            }
                            ExprContext::Store(op) => {
                                assert!(!op);

                                if self
                                    .aggregate_spans
                                    .iter()
                                    .any(|span| span.contains(expr.span))
                                {
                                    self.nums.set_tag_aggregate_num += 1;
                                } else {
                                    let expr_str = source_map.span_to_snippet(e2.span).unwrap();
                                    let replaced = str_replace_last(
                                        &expr_str,
                                        &format!(".{} = ", field.name),
                                        &format!(".set_{}(", field.name),
                                    );
                                    self.suggestions
                                        .add(e2.span, ReplaceExpr(expr!("{})", replaced)));

                                    self.nums.set_tag_num += 1;
                                }
                            }
                            ExprContext::Address => panic!(),
                        }
                    }
                } else if let Some(tu) = self.unions.get(&did) {
                    let matched = if let Some((match_span, _)) = self
                        .access_in_matches
                        .iter()
                        .find(|(_, ams)| ams.iter().any(|am| am.arm_span.contains(expr.span)))
                    {
                        if let Some((s1, arm_spans)) = self.match_targets.get(match_span) {
                            let ExprKind::Field(expr_struct, _) = e.kind else { unreachable!() };
                            let struct_str = source_map.span_to_snippet(expr_struct.span).unwrap();
                            let s2 = normalize_expr_str(&struct_str);
                            if s1 == &s2 && arm_spans.iter().any(|span| span.contains(expr.span)) {
                                Some(true)
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    } else if let Some((if_span, _)) = self
                        .access_in_ifs
                        .iter()
                        .find(|(_, ais)| ais.iter().any(|ai| ai.branch_span.contains(expr.span)))
                    {
                        if let Some(Some(s1)) = self.if_targets.get(if_span) {
                            let ExprKind::Field(expr_struct, _) = e.kind else { unreachable!() };
                            let struct_str = source_map.span_to_snippet(expr_struct.span).unwrap();
                            let s2 = normalize_expr_str(&struct_str);
                            if s1 == &s2 { Some(false) } else { None }
                        } else {
                            None
                        }
                    } else {
                        None
                    };

                    let (ctx, _) = get_expr_context(expr, self.tcx);
                    if let Some(is_match) = matched {
                        if !self
                            .aggregate_spans
                            .iter()
                            .any(|span| span.contains(expr.span))
                        {
                            self.suggestions
                                .add(expr.span, ReplaceExpr(expr!("(*__v)")));

                            match (is_match, ctx) {
                                (true, ExprContext::Value) => self.nums.get_variant_match_num += 1,
                                (true, _) => self.nums.set_variant_match_num += 1,
                                (false, ExprContext::Value) => self.nums.get_variant_if_num += 1,
                                (false, _) => self.nums.set_variant_if_num += 1,
                            }
                        }
                    } else {
                        let replaced_by_aggregate = self
                            .aggregate_spans
                            .iter()
                            .any(|span| span.contains(expr.span));
                        match ctx {
                            ExprContext::Value => {
                                if !replaced_by_aggregate {
                                    let expr_str = source_map.span_to_snippet(expr.span).unwrap();
                                    let replaced = str_replace_last(
                                        &expr_str,
                                        &format!(".{}", field.name),
                                        &format!(".get_{}()", field.name),
                                    );
                                    self.suggestions
                                        .add(expr.span, ReplaceExpr(expr!("{}", replaced)));

                                    self.nums.get_variant_num += 1;
                                }
                            }
                            ExprContext::Store(_) | ExprContext::Address => {
                                if replaced_by_aggregate {
                                    self.nums.set_variant_aggregate_num += 1;
                                } else {
                                    self.nums.set_variant_num += 1;

                                    let ItemKind::Union(
                                        _,
                                        _,
                                        VariantData::Struct { fields: fs, .. },
                                    ) = self.tcx.hir_expect_item(did).kind
                                    else {
                                        unreachable!()
                                    };
                                    let (i, _) = fs
                                        .iter()
                                        .enumerate()
                                        .find(|(_, f)| f.ident.name == field.name)
                                        .unwrap();
                                    let tags = &tu.variant_tags[&FieldIdx::from(i)];

                                    let call = if tags.len() == 1 {
                                        format!("deref_{}_mut())", field.name)
                                    } else {
                                        let ts = &self.structs[&tu.struct_local_def_id];
                                        let field_name = &ts.field_names[ts.tag_index];
                                        let ExprKind::Field(e2, _) = e.kind else { unreachable!() };
                                        let tag = format!(
                                            "{}.{}",
                                            source_map.span_to_snippet(e2.span).unwrap(),
                                            field_name,
                                        );
                                        format!("deref_{}_mut({}()))", field.name, tag)
                                    };
                                    let expr_str = source_map.span_to_snippet(expr.span).unwrap();
                                    let mut replaced = str_replace_last(
                                        &expr_str,
                                        &format!(".{}", field.name),
                                        &format!(".{call}"),
                                    );
                                    let root = unwrap_projection(expr);
                                    if let ExprKind::Unary(UnOp::Deref, e) = root.kind {
                                        let ty = self.typeck.expr_ty(e);
                                        if let TyKind::RawPtr(ty, Mutability::Not) = ty.kind() {
                                            let e_str = source_map.span_to_snippet(e.span).unwrap();
                                            replaced = replaced.replacen(
                                                &e_str,
                                                &format!("({e_str} as *mut crate::{ty:?})"),
                                                1,
                                            );
                                        }
                                    }
                                    self.suggestions
                                        .add(expr.span, ReplaceExpr(expr!("(*{}", replaced)));
                                }
                            }
                        }
                    }
                }
            }
            ExprKind::Assign(lhs, rhs, _) => {
                if let ExprKind::Path(QPath::Resolved(_, path)) = lhs.kind
                    && let Res::Local(hir_id) = path.res
                {
                    self.locals.insert(hir_id, rhs);
                }
                if let ExprKind::Path(QPath::Resolved(_, path)) = rhs.kind
                    && let Res::Local(hir_id) = path.res
                {
                    self.locals.insert(hir_id, lhs);
                }
            }
            _ => {}
        }
    }

    fn handle_local(&mut self, local: &'tcx rustc_hir::LetStmt<'tcx>) {
        let PatKind::Binding(_, hir_id, _, _) = local.pat.kind else { return };
        let init = some_or!(local.init, return);
        self.locals.insert(hir_id, init);
    }

    fn get_struct(&self, expr: &'tcx Expr<'tcx>) -> Option<&'tcx Expr<'tcx>> {
        match unwrap_cast_and_drop(expr).kind {
            ExprKind::Field(expr_struct, _) | ExprKind::MethodCall(_, expr_struct, _, _) => {
                Some(expr_struct)
            }
            ExprKind::Path(QPath::Resolved(_, path)) => {
                let Res::Local(hir_id) = path.res else { return None };
                let init = self.locals.get(&hir_id)?;
                self.get_struct(init)
            }
            _ => None,
        }
    }

    fn decompose_expr(&self, expr: &'tcx Expr<'tcx>) -> Option<Vec<&'tcx Expr<'tcx>>> {
        let expr = unwrap_cast_and_drop(expr);
        match expr.kind {
            ExprKind::Binary(Spanned { node, .. }, lhs, rhs) => match node {
                BinOpKind::Or => {
                    let mut exprs1 = self.decompose_expr(lhs)?;
                    let exprs2 = self.decompose_expr(rhs)?;
                    exprs1.extend(exprs2);
                    Some(exprs1)
                }
                BinOpKind::Eq => {
                    if let (Some(struct_expr), None) | (None, Some(struct_expr)) =
                        (self.get_struct(lhs), self.get_struct(rhs))
                    {
                        Some(vec![struct_expr])
                    } else {
                        None
                    }
                }
                _ => None,
            },
            ExprKind::Field(struct_expr, _) => Some(vec![struct_expr]),
            _ => None,
        }
    }

    fn handle_block(&mut self, block: &'tcx Block<'tcx>) {
        let mut blocks = AssignBlocks::default();
        for stmt in block.stmts {
            if let StmtKind::Semi(expr) = stmt.kind {
                match expr.kind {
                    ExprKind::Assign(lhs, rhs, _) => {
                        if let Some((struct_ty, struct_expr, fields)) = self.find_struct(lhs) {
                            let s = self
                                .tcx
                                .sess
                                .source_map()
                                .span_to_snippet(struct_expr.span)
                                .unwrap();
                            let struct_expr_string = normalize_expr_str(&s);
                            let bs = AssignBlockStmt {
                                struct_ty,
                                struct_expr,
                                struct_expr_string,
                                fields,
                                rhs,
                                span: stmt.span,
                            };
                            blocks.add_stmt(bs);
                            continue;
                        }
                    }
                    ExprKind::MethodCall(method, struct_expr, v, _) => {
                        if let Some(struct_ty) = self.as_tagged_struct(struct_expr)
                            && v.len() == 1
                        {
                            let method = method.ident.name.to_ident_string();
                            let field = method.strip_prefix("set_").unwrap();
                            let s = self
                                .tcx
                                .sess
                                .source_map()
                                .span_to_snippet(struct_expr.span)
                                .unwrap();
                            let struct_expr_string = normalize_expr_str(&s);
                            let bs = AssignBlockStmt {
                                struct_ty,
                                struct_expr,
                                struct_expr_string,
                                fields: vec![field.to_string()],
                                rhs: &v[0],
                                span: stmt.span,
                            };
                            blocks.add_stmt(bs);
                            continue;
                        }
                    }
                    _ => {}
                }
            }
            blocks.finish_block();
        }
        blocks.finish_block();

        for block in blocks.blocks {
            let ty = block[0].struct_ty;
            let expr = block[0].struct_expr;
            let (root, _) = unwrap_deref(unwrap_projection(expr));
            let ts = self.structs.get(&ty).unwrap();
            let tag_field_name = &ts.field_names[ts.tag_index];

            let mut assigns = FxHashMap::default();
            for bs in &block {
                assigns.insert(bs.fields.clone(), bs);
            }

            let tag_assign = some_or!(assigns.get(&vec![tag_field_name.to_string()]), continue);
            let (_, location) = self
                .basic_blocks
                .iter()
                .find(|(span, _)| span.contains(tag_assign.span))
                .copied()
                .unwrap();

            let mut removed = false;
            for (u, field_idx) in &ts.unions {
                let union_field_name = &ts.field_names[*field_idx];
                let mut fields = vec![union_field_name.clone()];
                let v = make_aggregate(Some(*u), &mut fields, &assigns, self.tcx);
                let Some(AssignedValue::Compound(union_name, vs)) = v else { continue };
                if vs.len() != 1 {
                    continue;
                }
                let (variant, value) = vs.into_iter().next().unwrap();
                if let ExprKind::Path(QPath::Resolved(_, path)) = root.kind {
                    let Res::Local(hir_id) = path.res else { continue };
                    let local = *some_or!(self.hir_id_to_locals.get(&hir_id), continue);
                    let field_at = FieldAt {
                        func: self.func,
                        location,
                        local,
                        field: ts.tag_index,
                    };
                    let tags = self.field_values.get(&field_at);
                    let tags = some_or!(tags, continue);
                    if tags.len() != 1 {
                        continue;
                    }
                    let tag = *tags.iter().next().unwrap();

                    let mut bss: Vec<_> = block
                        .iter()
                        .filter(|bs| &bs.fields[0] == union_field_name)
                        .collect();
                    let bs = bss.pop().unwrap();
                    let value = self.assigned_value_to_string(&value);
                    self.suggestions.add(
                        bs.span,
                        ReplaceStmt(stmt!(
                            "{}.{} = {}::{}{}({});",
                            self.tcx
                                .sess
                                .source_map()
                                .span_to_snippet(expr.span)
                                .unwrap(),
                            union_field_name,
                            union_name,
                            variant,
                            tag,
                            value,
                        )),
                    );
                    self.aggregate_spans.push(bs.span);
                    for bs in bss {
                        self.suggestions.add(bs.span, RemoveStmt);
                        self.aggregate_spans.push(bs.span);
                    }
                    removed = true;
                } else {
                    tracing::info!(
                        "{}",
                        self.tcx
                            .sess
                            .source_map()
                            .span_to_snippet(root.span)
                            .unwrap()
                    );
                }
            }
            if removed {
                self.suggestions.add(tag_assign.span, RemoveStmt);
                self.aggregate_spans.push(tag_assign.span);
                self.nums.aggregate_num += 1;
            }
        }
    }

    fn find_struct(
        &self,
        expr: &'tcx Expr<'tcx>,
    ) -> Option<(LocalDefId, &'tcx Expr<'tcx>, Vec<String>)> {
        let ExprKind::Field(e, f) = expr.kind else { return None };
        let res = if let Some(did) = self.as_tagged_struct(e) {
            (did, e, vec![f.name.to_ident_string()])
        } else {
            let (did, sexpr, mut fs) = self.find_struct(e)?;
            fs.push(f.name.to_ident_string());
            (did, sexpr, fs)
        };
        Some(res)
    }

    fn as_tagged_struct(&self, expr: &'tcx Expr<'tcx>) -> Option<LocalDefId> {
        let ty = self.typeck.expr_ty(expr);
        let TyKind::Adt(adt_def, _) = ty.kind() else { return None };
        let did = adt_def.did().as_local()?;
        if self.structs.contains_key(&did) {
            Some(did)
        } else {
            None
        }
    }

    fn assigned_value_to_string(&self, assigned_value: &AssignedValue<'tcx>) -> String {
        match assigned_value {
            AssignedValue::Compound(name, fields) => {
                let mut s = name.clone();
                s.push_str(" { ");
                for (i, (field, value)) in fields.iter().enumerate() {
                    if i > 0 {
                        s.push_str(", ");
                    }
                    s.push_str(field);
                    let value = self.assigned_value_to_string(value);
                    if field != &value {
                        write!(&mut s, ": {value}").unwrap();
                    }
                }
                s.push_str(" }");
                s
            }
            AssignedValue::Primitive(value) => self.replace_if_union(value),
        }
    }

    fn replace_if_union(&self, expr: &Expr<'tcx>) -> String {
        let source_map = self.tcx.sess.source_map();
        if let ExprKind::Field(e, f) = expr.kind {
            let ty = self.typeck.expr_ty(e);
            if let TyKind::Adt(adt_def, _) = ty.kind()
                && let Some(did) = adt_def.did().as_local()
                && self.unions.contains_key(&did)
            {
                let e = source_map.span_to_snippet(e.span).unwrap();
                return format!("{}.get_{}()", e, f.name);
            }
            let s = self.replace_if_union(e);
            format!("{}.{}", s, f.name)
        } else {
            source_map.span_to_snippet(expr.span).unwrap()
        }
    }
}

fn make_aggregate<'tcx>(
    ty: Option<LocalDefId>,
    fields: &mut Vec<String>,
    assigns: &FxHashMap<Vec<String>, &AssignBlockStmt<'tcx>>,
    tcx: TyCtxt<'tcx>,
) -> Option<AssignedValue<'tcx>> {
    if let Some(bs) = assigns.get(fields) {
        Some(AssignedValue::Primitive(bs.rhs))
    } else {
        let ty = ty?;
        let def_path = tcx.def_path(ty.to_def_id());
        let mut name = "crate".to_string();
        for data in def_path.data {
            let data = format!("{data}");
            let escape = if data == "async" { "r#" } else { "" };
            write!(name, "::{escape}{data}").unwrap();
        }
        let adt_def = tcx.adt_def(ty);
        let (ItemKind::Struct(_, _, vd) | ItemKind::Union(_, _, vd)) = tcx.hir_expect_item(ty).kind
        else {
            unreachable!()
        };
        let variant = adt_def.variant(VariantIdx::from_u32(0));
        let is_struct = adt_def.is_struct();

        let mut field_values = FxHashMap::default();
        for (mfd, hfd) in variant.fields.iter().zip(vd.fields()) {
            let field_name = hfd.ident.name.to_ident_string();
            let ty = mfd.ty(tcx, List::empty());
            let ty = if let TyKind::Adt(adt_def, _) = ty.kind() {
                adt_def.did().as_local()
            } else {
                None
            };
            fields.push(field_name.clone());
            let res = make_aggregate(ty, fields, assigns, tcx);
            fields.pop();
            if let Some(v) = res {
                field_values.insert(field_name, v);
                if !is_struct {
                    break;
                }
            } else if is_struct {
                return None;
            }
        }
        if field_values.is_empty() {
            None
        } else {
            Some(AssignedValue::Compound(name, field_values))
        }
    }
}

enum AssignedValue<'tcx> {
    Compound(String, FxHashMap<String, AssignedValue<'tcx>>),
    Primitive(&'tcx Expr<'tcx>),
}

#[derive(Debug, Default)]
struct AssignBlocks<'tcx> {
    blocks: Vec<AssignBlock<'tcx>>,
    block: AssignBlock<'tcx>,
}

impl<'tcx> AssignBlocks<'tcx> {
    fn add_stmt(&mut self, stmt: AssignBlockStmt<'tcx>) {
        if let Some(curr) = self.block.first()
            && (curr.struct_ty != stmt.struct_ty
                || curr.struct_expr_string != stmt.struct_expr_string)
        {
            self.finish_block();
        }
        self.block.push(stmt);
    }

    fn finish_block(&mut self) {
        let block = std::mem::take(&mut self.block);
        if block.len() > 1 {
            self.blocks.push(block);
        }
    }
}

type AssignBlock<'tcx> = Vec<AssignBlockStmt<'tcx>>;

#[derive(Debug)]
struct AssignBlockStmt<'tcx> {
    struct_ty: LocalDefId,
    struct_expr: &'tcx Expr<'tcx>,
    struct_expr_string: String,
    fields: Vec<String>,
    rhs: &'tcx Expr<'tcx>,
    span: Span,
}

impl<'tcx> HVisitor<'tcx> for SuggestingVisitor<'_, 'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        self.handle_expr(expr);
        intravisit::walk_expr(self, expr);
    }

    fn visit_local(&mut self, local: &'tcx rustc_hir::LetStmt<'tcx>) {
        self.handle_local(local);
        intravisit::walk_local(self, local);
    }

    fn visit_block(&mut self, block: &'tcx Block<'tcx>) {
        self.handle_block(block);
        intravisit::walk_block(self, block);
    }
}

struct HIf {
    c: Span,
    t: Span,
    f: Option<Span>,
}

struct HBodyVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    inits: FxHashMap<Span, Span>,
    set_exprs: FxHashSet<Span>,
    matches: Vec<(Span, Vec<(Span, ArmTags)>)>,
    ifs: Vec<HIf>,
    bindings: FxHashMap<Span, HirId>,
}

impl<'tcx> HBodyVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            inits: FxHashMap::default(),
            set_exprs: FxHashSet::default(),
            matches: vec![],
            ifs: vec![],
            bindings: FxHashMap::default(),
        }
    }

    fn handle_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        match expr.kind {
            ExprKind::Block(block, _) => {
                if block.stmts.len() <= 1 {
                    return;
                }
                let StmtKind::Let(local) = block.stmts[0].kind else { return };
                let PatKind::Binding(_, hir_id, ident, _) = local.pat.kind else { return };
                if ident.name.to_ident_string() != "init" {
                    return;
                }
                let init = some_or!(local.init, return);
                let ExprKind::Struct(_, _, _) = init.kind else { return };
                let e = some_or!(block.expr, return);
                let ExprKind::Path(QPath::Resolved(_, path)) = e.kind else { return };
                let Res::Local(id) = path.res else { return };
                if hir_id != id {
                    return;
                }
                self.inits.insert(e.span, init.span);
                for stmt in block.stmts.iter().skip(1) {
                    let StmtKind::Semi(e) = stmt.kind else { continue };
                    self.set_exprs.insert(e.span);
                }
            }
            ExprKind::Match(e, arms, MatchSource::Normal) => {
                let arms = arms
                    .iter()
                    .map(|arm| (arm.span, pat_to_tags(arm.pat)))
                    .collect();
                self.matches.push((e.span, arms));
            }
            ExprKind::If(c, t, f) => {
                let hif = HIf {
                    c: c.span,
                    t: t.span,
                    f: f.map(|f| f.span),
                };
                self.ifs.push(hif);
            }
            _ => {}
        }
    }

    fn handle_pat(&mut self, pat: &'tcx Pat<'tcx>) {
        let PatKind::Binding(_, hir_id, _, _) = pat.kind else { return };
        self.bindings.insert(pat.span, hir_id);
    }
}

impl<'tcx> HVisitor<'tcx> for HBodyVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        self.handle_expr(expr);
        intravisit::walk_expr(self, expr);
    }

    fn visit_pat(&mut self, pat: &'tcx Pat<'tcx>) {
        self.handle_pat(pat);
        intravisit::walk_pat(self, pat);
    }
}

struct FieldVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck: &'tcx TypeckResults<'tcx>,
    fields: &'a mut FxHashMap<LocalDefId, FxHashSet<Symbol>>,
}

impl<'tcx> FieldVisitor<'_, 'tcx> {
    fn handle_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        let ExprKind::Field(e, f) = expr.kind else { return };
        let ty = self.typeck.expr_ty(expr);
        if !ty.is_integral() && !ty.is_bool() {
            return;
        }
        let ty = self.typeck.expr_ty(e);
        let TyKind::Adt(adt_def, _) = ty.kind() else { return };
        if !adt_def.is_struct() {
            return;
        }
        let def_id = some_or!(adt_def.did().as_local(), return);
        if matches!(
            get_expr_context(expr, self.tcx).0,
            ExprContext::Store(true) | ExprContext::Address
        ) {
            self.fields.entry(def_id).or_default().insert(f.name);
        }
    }
}

impl<'tcx> HVisitor<'tcx> for FieldVisitor<'_, 'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        self.handle_expr(expr);
        intravisit::walk_expr(self, expr);
    }
}

struct AssignVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    assigns: Vec<(HirId, usize)>,
}

impl<'tcx> AssignVisitor<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            assigns: vec![],
        }
    }

    fn handle_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        let ExprKind::Assign(lhs, _, _) = expr.kind else { return };
        let (root, i) = unwrap_deref(lhs);
        let ExprKind::Path(QPath::Resolved(_, path)) = root.kind else { return };
        let Res::Local(hir_id) = path.res else { return };
        self.assigns.push((hir_id, i));
    }
}

impl<'tcx> HVisitor<'tcx> for AssignVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    // fn nested_visit_map(&mut self) -> Self::Map {
    //     self.tcx.hir()
    // }

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        self.handle_expr(expr);
        intravisit::walk_expr(self, expr);
    }
}

#[derive(Debug, Clone, Copy)]
enum ExprContext {
    Value,
    Address,
    Store(bool),
}

fn get_expr_context<'tcx>(
    expr: &'tcx Expr<'tcx>,
    tcx: TyCtxt<'tcx>,
) -> (ExprContext, &'tcx Expr<'tcx>) {
    let parent = tcx.parent_hir_node(expr.hir_id);
    match parent {
        Node::Expr(e) => match e.kind {
            ExprKind::Assign(l, _, _) | ExprKind::AssignOp(_, l, _) => {
                if expr.hir_id == l.hir_id {
                    (
                        ExprContext::Store(matches!(e.kind, ExprKind::AssignOp(_, _, _))),
                        e,
                    )
                } else {
                    (ExprContext::Value, expr)
                }
            }
            ExprKind::AddrOf(_, _, _) => (ExprContext::Address, e),
            ExprKind::Field(_, _) | ExprKind::DropTemps(_) => get_expr_context(e, tcx),
            ExprKind::MethodCall(method, receiver, _, _) => {
                if expr.hir_id == receiver.hir_id
                    && method.ident.name.to_ident_string() == "as_mut_ptr"
                {
                    (ExprContext::Address, expr)
                } else {
                    (ExprContext::Value, expr)
                }
            }
            _ => (ExprContext::Value, e),
        },
        Node::LetStmt(rustc_hir::LetStmt { pat, .. }) => {
            let PatKind::Binding(BindingMode(by_ref, _), _, _, _) = pat.kind else {
                unreachable!()
            };
            if matches!(by_ref, ByRef::Yes(_)) {
                (ExprContext::Address, expr)
            } else {
                (ExprContext::Value, expr)
            }
        }
        Node::ExprField(_) | Node::Stmt(_) | Node::Block(_) => (ExprContext::Value, expr),
        _ => unreachable!("{:?}", parent),
    }
}

fn tag_to_string(tag: Tag, ty: &str) -> String {
    if ty == "bool" {
        (tag.0 != 0).to_string()
    } else if ty.ends_with("c_int") {
        tag.0.to_string()
    } else {
        tag.to_string()
    }
}

fn expr_to_tag(expr: &PatExpr<'_>) -> i128 {
    match expr.kind {
        PatExprKind::Lit { lit, negated } => {
            let LitKind::Int(n, _) = lit.node else { unreachable!() };
            if negated {
                0i128.wrapping_sub(n.get() as i128)
            } else {
                n.get() as i128
            }
        }
        _ => unreachable!(),
    }
}

fn pat_to_tags(pat: &Pat<'_>) -> ArmTags {
    match pat.kind {
        PatKind::Expr(expr) => Some([expr_to_tag(expr)].into_iter().collect()),
        PatKind::Or(pats) => {
            let mut tags = BTreeSet::new();
            for pat in pats {
                tags.extend(pat_to_tags(pat)?);
            }
            Some(tags)
        }
        PatKind::Wild => None,
        _ => unreachable!("{:?}", pat),
    }
}

#[derive(Clone, Copy)]
struct AccessCtx<'a, 'tcx> {
    states: &'a FxHashMap<Location, AbsMem>,
    local_to_unions: &'a FxHashMap<LocalDefId, Vec<(Local, Vec<AccElem>)>>,
    body: &'a Body<'tcx>,
    tcx: TyCtxt<'tcx>,
}

impl<'a, 'tcx> AccessCtx<'a, 'tcx> {
    fn new(
        states: &'a FxHashMap<Location, AbsMem>,
        local_to_unions: &'a FxHashMap<LocalDefId, Vec<(Local, Vec<AccElem>)>>,
        body: &'a Body<'tcx>,
        tcx: TyCtxt<'tcx>,
    ) -> Self {
        Self {
            states,
            local_to_unions,
            body,
            tcx,
        }
    }

    fn compute_tags(&self, access: FieldAccess<'tcx>) -> Vec<(FieldIdx, AbsInt)> {
        let state = some_or!(self.states.get(&access.location), return vec![]);
        let (path, is_deref) = access.get_path(state, &self.body.local_decls, self.tcx);
        let g = state.g();
        let obj = some_or!(g.get_obj(&path, is_deref), return vec![]);
        let Obj::Struct(fields, _) = obj else { return vec![] };
        let mut v: Vec<_> = fields
            .iter()
            .filter_map(|(f, obj)| {
                let Obj::Ptr(loc) = obj else { return None };
                let obj = g.obj_at_location(loc)?;
                let Obj::AtAddr(n) = obj else { return None };
                Some((*f, n.clone()))
            })
            .collect();
        v.sort_by_key(|(f, _)| *f);
        v
    }
}

#[derive(Debug)]
#[allow(dead_code)]
pub(super) struct AccessInMatch<'tcx> {
    access: FieldAccess<'tcx>,
    field_tags: Vec<(FieldIdx, FxHashSet<i128>)>,
    match_loc: Location,
    arm_loc: Location,
    match_span: Span,
    arm_span: Span,
}

fn access_in_match<'tcx>(
    access: FieldAccess<'tcx>,
    matches: &[(Span, Vec<(Span, ArmTags)>)],
    switches: &FxHashMap<BytePos, (Location, FxHashMap<ArmTags, BasicBlock>)>,
    ctx: AccessCtx<'_, 'tcx>,
) -> Option<AccessInMatch<'tcx>> {
    let span = ctx.body.source_info(access.location).span;
    let (match_span, arm_span, tags) = matches.iter().find_map(|(match_span, arms)| {
        let (arm_span, tags) = arms.iter().find(|(s, _)| s.overlaps(span))?;
        Some((*match_span, *arm_span, tags))
    })?;
    let state_tags = ctx.compute_tags(access);
    let mut field_tags = if let Some(tags) = tags {
        vec![state_tags.iter().find_map(|(f, n)| {
            let ts = n.as_set();
            if set_eq(&ts, tags) {
                Some((*f, ts))
            } else {
                None
            }
        })?]
    } else if state_tags.is_empty() {
        return None;
    } else {
        state_tags
            .into_iter()
            .filter_map(|(f, n)| {
                let ts = n.as_set();
                if ts.is_empty() { None } else { Some((f, ts)) }
            })
            .collect()
    };

    let (match_loc, ref targets) = switches[&match_span.hi()];
    let block = targets[tags];
    let arm_loc = Location {
        block,
        statement_index: 0,
    };
    field_tags.retain(|(f, tags)| is_tag_from_branch(*f, tags, match_loc, arm_loc, access, ctx));
    if field_tags.is_empty() {
        return None;
    }

    let access = AccessInMatch {
        access,
        field_tags,
        match_loc,
        arm_loc,
        match_span,
        arm_span,
    };
    Some(access)
}

#[derive(Debug)]
#[allow(dead_code)]
pub(super) struct AccessInIf<'tcx> {
    access: FieldAccess<'tcx>,
    field_tags: Vec<(FieldIdx, FxHashSet<i128>)>,
    if_loc: Location,
    branch_loc: Location,
    if_span: Span,
    branch_span: Span,
}

fn access_in_if<'tcx>(
    access: FieldAccess<'tcx>,
    hifs: &[HIf],
    mifs: &[MIf],
    ctx: AccessCtx<'_, 'tcx>,
) -> Vec<AccessInIf<'tcx>> {
    let span = ctx.body.source_info(access.location).span;
    let state_tags = ctx.compute_tags(access);
    let field_tags: Vec<_> = state_tags
        .into_iter()
        .filter_map(|(f, n)| {
            let ts = n.as_set();
            if ts.is_empty() { None } else { Some((f, ts)) }
        })
        .collect();

    let mut accesses = vec![];
    for hif in hifs {
        let (c_span, branch_span, is_true) = if hif.t.overlaps(span) {
            (hif.c, hif.t, true)
        } else if let Some(f) = hif.f {
            if f.overlaps(span) {
                (hif.c, f, false)
            } else {
                continue;
            }
        } else {
            continue;
        };

        for mif in mifs {
            // println!("Checking MIf: {:?}", mif.c);
            if !mif.c.overlaps(c_span) {
                continue;
            }

            let mut field_tags = field_tags.clone();
            let if_loc = mif.loc;
            let block = if is_true { mif.t } else { mif.f };
            let branch_loc = Location {
                block,
                statement_index: 0,
            };
            field_tags
                .retain(|(f, tags)| is_tag_from_branch(*f, tags, if_loc, branch_loc, access, ctx));
            if !field_tags.is_empty() {
                let access = AccessInIf {
                    access,
                    field_tags,
                    if_loc: mif.loc,
                    branch_loc,
                    if_span: c_span,
                    branch_span,
                };
                accesses.push(access);
            }
        }
    }

    accesses
}

fn is_tag_from_branch<'tcx>(
    f: FieldIdx,
    tags: &FxHashSet<i128>,
    loc_before: Location,
    loc_after: Location,
    access: FieldAccess<'tcx>,
    ctx: AccessCtx<'_, 'tcx>,
) -> bool {
    let mut paths = ctx.local_to_unions[&access.ty].clone();

    filter_paths_by_tag(f, tags, access.location, &mut paths, true, ctx);
    if paths.is_empty() {
        return false;
    }

    filter_paths_by_tag(f, tags, loc_after, &mut paths, true, ctx);
    if paths.is_empty() {
        return false;
    }

    filter_paths_by_tag(f, tags, loc_before, &mut paths, false, ctx);
    !paths.is_empty()
}

fn filter_paths_by_tag(
    f: FieldIdx,
    tags: &FxHashSet<i128>,
    loc: Location,
    paths: &mut Vec<(Local, Vec<AccElem>)>,
    same: bool,
    ctx: AccessCtx<'_, '_>,
) {
    if let Some(state) = ctx.states.get(&loc) {
        let g = state.g();
        paths.retain(|(l, path)| {
            let len = path.len();
            let AccElem::Field(_) = path[len - 1] else { unreachable!() };
            let objs = g.objs_at(*l, &path[..len - 1]);
            objs.iter().any(|obj| {
                let loc_tags = extract_tags_from_obj(obj, g);
                let (_, loc_tags) =
                    some_or!(loc_tags.into_iter().find(|(f1, _)| f == *f1), return false);
                &loc_tags == tags
            }) == same
        });
    } else {
        paths.clear();
    }
}

fn set_eq<T: Eq + Ord + std::hash::Hash>(s1: &FxHashSet<T>, s2: &BTreeSet<T>) -> bool {
    if s1.len() != s2.len() {
        return false;
    }
    s2.iter().all(|x| s1.contains(x))
}

fn extract_tags_from_obj(obj: &Obj, g: &Graph) -> Vec<(FieldIdx, FxHashSet<i128>)> {
    let Obj::Struct(fs, _) = obj else { return vec![] };
    fs.iter()
        .filter_map(|(f, obj)| {
            let Obj::Ptr(loc) = obj else { return None };
            let obj = g.obj_at_location(loc)?;
            let Obj::AtAddr(n) = obj else { return None };
            let ns = n.as_set();
            if ns.is_empty() { None } else { Some((*f, ns)) }
        })
        .collect()
}

fn normalize_expr_str(s: &str) -> String {
    s.chars()
        .filter(|&c| !c.is_whitespace() && c != '(' && c != ')')
        .collect()
}

fn unwrap_projection<'a, 'tcx>(e: &'a Expr<'tcx>) -> &'a Expr<'tcx> {
    match unwrap_cast_and_drop(e).kind {
        ExprKind::MethodCall(_, e, _, _)
        | ExprKind::Cast(e, _)
        | ExprKind::DropTemps(e)
        | ExprKind::Field(e, _)
        | ExprKind::Index(e, _, _) => unwrap_projection(e),
        _ => e,
    }
}

fn find_tag_from_accesses<'a>(
    accesses: &'a [AccessInIf<'_>],
) -> Option<(FieldIdx, &'a FxHashSet<i128>)> {
    let access = accesses.first()?;
    if access.field_tags.len() > 1 {
        return None;
    }
    let (field, ref tags) = access.field_tags[0];
    for access in &accesses[1..] {
        if access.field_tags.len() > 1 {
            return None;
        }
        let (field2, ref tags2) = access.field_tags[0];
        if field != field2 || tags != tags2 {
            return None;
        }
    }
    Some((field, tags))
}

fn tags_to_pattern<I: Iterator<Item = i128>>(
    tags: I,
    is_const: bool,
    tu: &TaggedUnion,
) -> (String, Option<String>) {
    let tag_and_variants: Vec<_> = tags
        .map(|tag| {
            let tag = Tag(tag as _);
            (tag, tu.tag_variants[&tag])
        })
        .collect();
    let variants: FxHashSet<_> = tag_and_variants.iter().map(|(_, v)| *v).collect();
    let field = if variants.len() == 1 {
        variants.into_iter().next().unwrap()
    } else {
        None
    };
    let (binding, cast) = if let Some(field) = field {
        let binding = if is_const { "ref __v" } else { "ref mut __v" };
        let f_ty = &tu.field_tys[field];
        let m = if is_const { "const" } else { "mut" };
        let cast = format!("let __v = __v as *{m} {f_ty};");
        (binding, Some(cast))
    } else {
        ("_", None)
    };
    let pat = tag_and_variants
        .iter()
        .map(|(tag, variant)| {
            if let Some(v) = variant {
                let f_name = &tu.field_names[*v];
                format!("{}::{}{}({})", tu.name, f_name, tag, binding)
            } else {
                format!("{}::Empty{}", tu.name, tag)
            }
        })
        .intersperse(" | ".to_string())
        .collect();
    (pat, cast)
}

fn is_from_const_ptr<'tcx>(expr: &Expr<'tcx>, typeck: &TypeckResults<'tcx>) -> bool {
    let expr_wo_proj = unwrap_projection(expr);
    if let ExprKind::Unary(UnOp::Deref, expr_ptr) = expr_wo_proj.kind {
        let ty = typeck.expr_ty(expr_ptr);
        matches!(ty.kind(), TyKind::RawPtr(_, Mutability::Not))
    } else {
        false
    }
}

fn get_parent<'tcx>(expr: &Expr<'_>, tcx: TyCtxt<'tcx>) -> Option<&'tcx Expr<'tcx>> {
    let Node::Expr(parent) = tcx.parent_hir_node(expr.hir_id) else { return None };
    if matches!(parent.kind, ExprKind::DropTemps(_)) {
        get_parent(parent, tcx)
    } else {
        Some(parent)
    }
}

fn unwrap_cast_and_drop<'a, 'tcx>(e: &'a Expr<'tcx>) -> &'a Expr<'tcx> {
    if let ExprKind::Cast(e, _) | ExprKind::DropTemps(e) = e.kind {
        unwrap_cast_and_drop(e)
    } else {
        e
    }
}

fn unwrap_deref<'a, 'tcx>(e: &'a Expr<'tcx>) -> (&'a Expr<'tcx>, usize) {
    if let ExprKind::Unary(UnOp::Deref, e) = e.kind {
        let (e, i) = unwrap_deref(e);
        (e, i + 1)
    } else {
        (e, 0)
    }
}

fn str_replace_last(s: &str, old: &str, new: &str) -> String {
    if let Some(pos) = s.rfind(old) {
        let mut result = String::with_capacity(s.len() - old.len() + new.len());
        result.push_str(&s[..pos]);
        result.push_str(new);
        result.push_str(&s[pos + old.len()..]);
        result
    } else {
        s.to_string()
    }
}
