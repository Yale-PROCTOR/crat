use etrace::some_or;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    AmbigArg, ItemKind, Node, QPath, Ty, TyKind,
    def::{DefKind, Res},
    intravisit::{self, Visitor},
};
use rustc_index::IndexVec;
use rustc_middle::{
    hir::nested_filter,
    ty::{Ty as MidTy, TyCtxt},
};
use rustc_span::def_id::LocalDefId;

rustc_index::newtype_index! {
    #[orderable]
    #[debug_format = "ty{}"]
    struct TyId {}
}

pub struct TyVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    tys: IndexVec<TyId, LocalDefId>,
    ty_ids: FxHashMap<LocalDefId, TyId>,
    foreign_types: FxHashSet<TyId>,
    unions: FxHashSet<TyId>,
    type_graph: FxHashMap<TyId, FxHashSet<TyId>>,
}

#[derive(Debug, Default, Clone)]
pub struct UnionRelatedTypes<'tcx> {
    pub parent_types: FxHashSet<LocalDefId>,
    pub field_types: FxHashSet<MidTy<'tcx>>,
}

impl std::fmt::Debug for TyVisitor<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TyVisitor")
            .field("tys", &self.tys)
            .field("ty_ids", &self.ty_ids)
            .field("foreign_types", &self.foreign_types)
            .field("unions", &self.unions)
            .field("type_graph", &self.type_graph)
            .finish()
    }
}

pub fn collect_foreign_and_union_types<'tcx>(
    tcx: &TyCtxt<'tcx>,
    verbose: bool,
) -> (Vec<LocalDefId>, Vec<LocalDefId>) {
    let ty_visitor = TyVisitor::new(*tcx);
    let (_local_types, foreign_tys, union_tys) = ty_visitor.analyse_tys(*tcx);

    let mut foreign_vec = foreign_tys.into_iter().collect::<Vec<_>>();
    foreign_vec.sort_by_key(|def_id| tcx.def_path_str(*def_id));

    let mut union_vec = union_tys.into_iter().collect::<Vec<_>>();
    union_vec.sort_by_key(|def_id| tcx.def_path_str(*def_id));

    if verbose {
        println!("\nForeign Types:\n\t{}", {
            let names = foreign_vec
                .iter()
                .map(|def_id| tcx.def_path_str(*def_id))
                .collect::<Vec<_>>();
            names.join("\n\t")
        });

        println!("Union Types:\n\t{}", {
            let names = union_vec
                .iter()
                .map(|def_id| tcx.def_path_str(*def_id))
                .collect::<Vec<_>>();
            names.join("\n\t")
        });
    }

    (foreign_vec, union_vec)
}

pub fn collect_union_related_types<'tcx>(
    tcx: &TyCtxt<'tcx>,
    union_tys: &[LocalDefId],
    verbose: bool,
) -> FxHashMap<LocalDefId, UnionRelatedTypes<'tcx>> {
    let ty_visitor = TyVisitor::new(*tcx);
    let related_types = ty_visitor.analyze_union_related_types(*tcx, union_tys);

    if verbose {
        println!("\nUnion Related Types:");
        let mut unions = related_types.keys().copied().collect::<Vec<_>>();
        unions.sort_by_key(|def_id| tcx.def_path_str(*def_id));
        for union_ty in unions {
            let related = related_types.get(&union_ty).expect("union key exists");
            let mut parent_names = related
                .parent_types
                .iter()
                .map(|def_id| tcx.def_path_str(*def_id))
                .collect::<Vec<_>>();
            parent_names.sort();
            let mut field_names = related
                .field_types
                .iter()
                .map(|ty| format!("{ty:?}"))
                .collect::<Vec<_>>();
            field_names.sort();
            println!("\t{}:", tcx.def_path_str(union_ty));
            println!("\t\tparents: {}", parent_names.join(", "));
            println!("\t\tfields: {}", field_names.join(", "));
        }
    }

    related_types
}

impl<'tcx> TyVisitor<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            tys: IndexVec::new(),
            ty_ids: FxHashMap::default(),
            foreign_types: FxHashSet::default(),
            unions: FxHashSet::default(),
            type_graph: FxHashMap::default(),
        }
    }

    // Return (local_types, foreign_types, union_types)
    pub fn analyse_tys(
        mut self,
        tcx: TyCtxt<'tcx>,
    ) -> (
        FxHashSet<LocalDefId>,
        FxHashSet<LocalDefId>,
        FxHashSet<LocalDefId>,
    ) {
        tcx.hir_visit_all_item_likes_in_crate(&mut self);
        let ftypes: FxHashSet<_> = self
            .foreign_types
            .into_iter()
            .flat_map(|id| utils::graph::reachable_vertices(&self.type_graph, id))
            .collect();
        let unions: FxHashSet<_> = self
            .unions
            .into_iter()
            .flat_map(|id| utils::graph::reachable_vertices(&self.type_graph, id))
            .collect();

        let mut local_types = FxHashSet::default();
        let mut foreign_types = FxHashSet::default();
        let mut union_types = FxHashSet::default();
        for (i, ty) in self.tys.iter_enumerated() {
            if ftypes.contains(&i) {
                foreign_types.insert(*ty);
            } else {
                if unions.contains(&i) {
                    union_types.insert(*ty);
                }
                local_types.insert(*ty);
            }
        }
        (local_types, foreign_types, union_types)
    }

    /// Analyze union-related types: target union type -> (parent struct, fields)
    pub fn analyze_union_related_types(
        mut self,
        tcx: TyCtxt<'tcx>,
        union_tys: &[LocalDefId],
    ) -> FxHashMap<LocalDefId, UnionRelatedTypes<'tcx>> {
        tcx.hir_visit_all_item_likes_in_crate(&mut self);

        let mut reverse_graph: FxHashMap<TyId, FxHashSet<TyId>> = FxHashMap::default();
        for (src, dsts) in &self.type_graph {
            for dst in dsts {
                reverse_graph.entry(*dst).or_default().insert(*src);
            }
        }

        let mut related = FxHashMap::default();
        // for each union type
        for &union_ty in union_tys {
            let mut union_related = UnionRelatedTypes::default();

            let union_adt = tcx.adt_def(union_ty.to_def_id());

            // fields
            for field in union_adt.all_fields() {
                let field_ty = tcx.type_of(field.did).instantiate_identity();
                union_related.field_types.insert(field_ty);
            }

            // parents
            if let Some(&union_id) = self.ty_ids.get(&union_ty)
                && let Some(parent_tys) = reverse_graph.get(&union_id)
            {
                for ty_id in parent_tys {
                    let parent = self.tys[*ty_id];
                    
                    // Only consider struct parents for now
                    if matches!(tcx.def_kind(parent), DefKind::Struct) {
                        union_related.parent_types.insert(parent);
                    }
                }
            }

            related.insert(union_ty, union_related);
        }

        related
    }

    fn ty_to_id(&mut self, ty: LocalDefId) -> TyId {
        self.ty_ids.get(&ty).copied().unwrap_or_else(|| {
            let id = self.tys.next_index();
            self.tys.push(ty);
            self.ty_ids.insert(ty, id);
            id
        })
    }

    fn handle_ty<Unambig>(&mut self, ty: &'tcx Ty<'tcx, Unambig>) {
        let TyKind::Path(QPath::Resolved(_, path)) = ty.kind else { return };

        let Res::Def(_, def_id) = path.res else { return };
        let def_id = some_or!(def_id.as_local(), return);
        let id = self.ty_to_id(def_id);
        if matches!(self.tcx.def_kind(def_id), DefKind::Union) {
            self.unions.insert(id);
        }

        let hir_id = ty.hir_id;
        for parent_id in self.tcx.hir_parent_id_iter(hir_id) {
            let node = self.tcx.hir_node(parent_id);
            match node {
                Node::ForeignItem(_) => {
                    self.foreign_types.insert(id);
                    break;
                }
                Node::Item(item) => {
                    if matches!(
                        item.kind,
                        ItemKind::Struct(_, _, _)
                            | ItemKind::TyAlias(_, _, _)
                            | ItemKind::Union(_, _, _)
                    ) {
                        let item_id = self.ty_to_id(item.owner_id.def_id);
                        self.type_graph.entry(item_id).or_default().insert(id);
                    }
                    break;
                }
                _ => {}
            }
        }
    }
}

impl<'tcx> Visitor<'tcx> for TyVisitor<'tcx> {
    type NestedFilter = nested_filter::All;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_ty(&mut self, ty: &'tcx Ty<'tcx, AmbigArg>) {
        self.handle_ty(ty);
        intravisit::walk_ty(self, ty);
    }
}
