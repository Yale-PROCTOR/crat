use std::collections::{BTreeMap, BTreeSet};

use etrace::some_or;
use rustc_abi::FieldIdx;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::def_id::LocalDefId;
use rustc_index::{
    IndexVec,
    bit_set::{ChunkedBitSet, DenseBitSet},
};
use rustc_middle::{
    mir::{HasLocalDecls, Local, Place, PlaceElem},
    ty::{Ty, TyCtxt, TyKind},
};
use utils::ty_shape::TyShape;

use crate::{points_to::andersen, union_replacer::tag_analysis};

#[derive(Debug, Clone)]
pub enum AbsMem {
    Bot,
    Mem(Graph),
}

impl AbsMem {
    #[inline]
    pub fn top() -> Self {
        Self::Mem(Graph::default())
    }

    #[inline]
    pub fn bot() -> Self {
        Self::Bot
    }

    #[inline]
    pub fn g(&self) -> &Graph {
        match self {
            Self::Bot => panic!(),
            Self::Mem(g) => g,
        }
    }

    #[inline]
    pub fn gm(&mut self) -> &mut Graph {
        match self {
            Self::Bot => panic!(),
            Self::Mem(g) => g,
        }
    }

    #[inline]
    pub fn widen(&self, other: &Self) -> Self {
        let Self::Mem(g1) = self else { return other.clone() };
        let Self::Mem(g2) = other else { return self.clone() };
        Self::Mem(g1.join(g2, true))
    }

    #[inline]
    pub fn join(&self, other: &Self) -> Self {
        let Self::Mem(g1) = self else { return other.clone() };
        let Self::Mem(g2) = other else { return self.clone() };
        Self::Mem(g1.join(g2, false))
    }

    #[inline]
    pub fn ord(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Bot, _) => true,
            (_, Self::Bot) => false,
            (Self::Mem(g1), Self::Mem(g2)) => g1.ord(g2),
        }
    }

    pub fn size(&self) -> (usize, usize) {
        match self {
            Self::Bot => (0, 0),
            Self::Mem(g) => (g.locals.len(), g.nodes.len()),
        }
    }

    pub fn clear_dead_locals(&mut self, dead_locals: &DenseBitSet<Local>) {
        if let Self::Mem(g) = self {
            g.clear_dead_locals(dead_locals);
        }
    }
}

rustc_index::newtype_index! {
    #[orderable]
    #[debug_format = "N{}"]
    pub struct NodeId {}
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Index {
    Num(i128),
    Sym(BTreeSet<Local>),
}

impl std::fmt::Debug for Index {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Index::Num(i) => write!(f, "{i}"),
            Index::Sym(s) => write!(f, "{s:?}"),
        }
    }
}

impl Index {
    fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Num(n1), Self::Num(n2)) if n1 == n2 => Self::Num(*n1),
            (Self::Sym(l1), Self::Sym(l2)) => Self::Sym(l1.intersection(l2).cloned().collect()),
            _ => Self::Sym(BTreeSet::new()),
        }
    }

    fn ord(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Num(n1), Self::Num(n2)) => n1 == n2,
            (Self::Sym(l1), Self::Sym(l2)) => l2.is_subset(l1),
            _ => false,
        }
    }

    fn equiv(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Num(n1), Self::Num(n2)) => n1 == n2,
            (Self::Sym(l1), Self::Sym(l2)) => !l1.is_disjoint(l2),
            _ => false,
        }
    }

    fn collect_locals(&self, locals: &mut DenseBitSet<Local>) {
        if let Self::Sym(ls) = self {
            for local in ls {
                locals.insert(*local);
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum OpVal {
    Place(AccPath, bool),
    Static(LocalDefId),
    Int(i128),
    Other,
}

impl OpVal {
    #[inline]
    pub fn extended(&self, proj: &[AccElem]) -> Self {
        let mut new = self.clone();
        new.extend_projection(proj);
        new
    }

    #[inline]
    pub fn extend_projection(&mut self, proj: &[AccElem]) {
        match self {
            OpVal::Place(path, _) => path.extend_projection(proj),
            OpVal::Static(_) => unreachable!(),
            OpVal::Int(_) => assert!(proj.is_empty()),
            OpVal::Other => {}
        }
    }
}

#[derive(Debug, Clone)]
pub struct AccPath {
    pub local: Local,
    pub projection: Vec<AccElem>,
}

impl AccPath {
    #[inline]
    pub fn new(local: Local, projection: Vec<AccElem>) -> Self {
        Self { local, projection }
    }

    #[inline]
    pub fn from_place<'tcx, D: HasLocalDecls<'tcx> + ?Sized>(
        place: Place<'tcx>,
        state: &AbsMem,
        local_decls: &D,
        tcx: TyCtxt<'tcx>,
    ) -> (Self, bool) {
        Self::from_local_projection(place.local, place.projection, state, local_decls, tcx)
    }

    pub fn from_local_projection<'tcx, D: HasLocalDecls<'tcx> + ?Sized>(
        local: Local,
        proj: &[PlaceElem<'tcx>],
        state: &AbsMem,
        local_decls: &D,
        tcx: TyCtxt<'tcx>,
    ) -> (Self, bool) {
        let is_deref = proj.first().is_some_and(|e| matches!(e, PlaceElem::Deref));
        let mut projections = vec![];
        for (i, e) in proj.iter().enumerate().skip(is_deref as usize) {
            let ty = Place::ty_from(local, &proj[..i], local_decls, tcx).ty;
            let elem = AccElem::from_elem(*e, ty, state);
            projections.push(elem);
        }
        (AccPath::new(local, projections), is_deref)
    }

    #[inline]
    pub fn extended(&self, proj: &[AccElem]) -> Self {
        let mut new = self.clone();
        new.extend_projection(proj);
        new
    }

    #[inline]
    pub fn extend_projection(&mut self, proj: &[AccElem]) {
        self.projection.extend(proj.to_owned());
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AccElem {
    Field(FieldIdx, bool),
    Index(Index),
}

impl std::fmt::Debug for AccElem {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AccElem::Field(i, is_union) => {
                write!(f, ".{}", i.as_u32())?;
                if *is_union {
                    write!(f, "u")?;
                }
                Ok(())
            }
            AccElem::Index(i) => write!(f, "[{i:?}]"),
        }
    }
}

impl AccElem {
    #[inline]
    pub fn num_index(i: i128) -> Self {
        Self::Index(Index::Num(i))
    }

    #[inline]
    pub fn sym_index(ls: BTreeSet<Local>) -> Self {
        Self::Index(Index::Sym(ls))
    }

    pub fn collect_locals(&self, locals: &mut DenseBitSet<Local>) {
        if let Self::Index(i) = self {
            i.collect_locals(locals);
        }
    }

    pub fn from_elem(proj: PlaceElem<'_>, ty: Ty<'_>, state: &AbsMem) -> Self {
        match proj {
            PlaceElem::Deref => unreachable!(),
            PlaceElem::Field(i, _) => {
                let is_union = match ty.kind() {
                    TyKind::Adt(adt_def, _) => adt_def.is_union(),
                    TyKind::Tuple(_) => false,
                    _ => unreachable!(),
                };
                AccElem::Field(i, is_union)
            }
            PlaceElem::Index(local) => {
                let path = AccPath::new(local, vec![]);
                if let Some(i) = state.g().get_x_as_int(&path, false) {
                    AccElem::num_index(i)
                } else {
                    AccElem::sym_index(state.g().find_aliases(local))
                }
            }
            PlaceElem::ConstantIndex { .. } => unreachable!(),
            PlaceElem::Subslice { .. } => unreachable!(),
            PlaceElem::Downcast(_, _) => unreachable!(),
            PlaceElem::OpaqueCast(_) => unreachable!(),
            PlaceElem::UnwrapUnsafeBinder(_) => unreachable!(),
            PlaceElem::Subtype(_) => unreachable!(),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct AbsLoc {
    root: NodeId,
    projection: Vec<AccElem>,
}

impl std::fmt::Debug for AbsLoc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.root)?;
        if !self.projection.is_empty() {
            for elem in self.projection.iter() {
                write!(f, "{elem:?}")?;
            }
        }
        Ok(())
    }
}

impl AbsLoc {
    #[inline]
    pub fn new(root: NodeId, projection: Vec<AccElem>) -> Self {
        Self { root, projection }
    }

    #[inline]
    pub fn new_root(root: NodeId) -> Self {
        Self {
            root,
            projection: vec![],
        }
    }

    #[inline]
    pub fn root(&self) -> NodeId {
        self.root
    }

    #[inline]
    pub fn projection(&self) -> &[AccElem] {
        &self.projection
    }

    #[inline]
    fn push_field(mut self, i: FieldIdx, is_union: bool) -> Self {
        self.projection.push(AccElem::Field(i, is_union));
        self
    }

    #[inline]
    fn push_index(mut self, i: Index) -> Self {
        self.projection.push(AccElem::Index(i));
        self
    }

    #[inline]
    fn is_prefix_of(&self, other: &Self) -> bool {
        self.root == other.root
            && self.projection.len() <= other.projection.len()
            && self
                .projection
                .iter()
                .zip(&other.projection)
                .all(|(e1, e2)| e1 == e2)
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum AbsInt {
    Top,
    Set(FxHashSet<i128>),
}

impl std::fmt::Debug for AbsInt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AbsInt::Top => write!(f, "T"),
            AbsInt::Set(s) => write!(f, "{s:?}"),
        }
    }
}

impl AbsInt {
    #[inline]
    fn singleton(n: i128) -> Self {
        Self::Set([n].into_iter().collect())
    }

    #[inline]
    fn new(ns: FxHashSet<i128>) -> Self {
        if ns.len() > 10 {
            Self::Top
        } else {
            Self::Set(ns)
        }
    }

    #[inline]
    pub fn as_singleton(&self) -> Option<i128> {
        match self {
            Self::Set(s) if s.len() == 1 => Some(*s.iter().next().unwrap()),
            _ => None,
        }
    }

    #[inline]
    pub fn iter(&self) -> Box<dyn Iterator<Item = i128> + '_> {
        match self {
            Self::Top => Box::new(std::iter::empty()),
            Self::Set(s) => Box::new(s.iter().copied()),
        }
    }

    #[inline]
    pub fn as_set(&self) -> FxHashSet<i128> {
        match self {
            Self::Top => FxHashSet::default(),
            Self::Set(s) => s.clone(),
        }
    }

    fn join(&self, other: &Self, widen: bool) -> Self {
        match (self, other) {
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Set(s1), Self::Set(s2)) => {
                if !widen {
                    Self::new(s1.union(s2).copied().collect())
                } else if s2.is_subset(s1) {
                    self.clone()
                } else if s1.is_empty() {
                    other.clone()
                } else {
                    Self::Top
                }
            }
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub enum Obj {
    Top,
    AtAddr(AbsInt),
    Ptr(AbsLoc),
    Struct(FxHashMap<FieldIdx, Obj>, bool),
    Array(FxHashMap<Index, Obj>),
}

impl std::fmt::Debug for Obj {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Top => write!(f, "T"),
            Self::AtAddr(n) => write!(f, "@{n:?}"),
            Self::Ptr(l) => write!(f, "{l:?}"),
            Self::Struct(fs, is_union) => {
                write!(f, "[")?;
                let mut v = fs.keys().cloned().collect::<Vec<_>>();
                v.sort();
                for (i, k) in v.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {:?}", k.as_u32(), fs[k])?;
                }
                write!(f, "]")?;
                if *is_union {
                    write!(f, "u")?;
                }
                Ok(())
            }
            Self::Array(vs) => {
                write!(f, "[")?;
                let mut v = vs.keys().cloned().collect::<Vec<_>>();
                v.sort();
                for (i, k) in v.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{:?}: {:?}", k, vs[k])?;
                }
                write!(f, "]")
            }
        }
    }
}

impl Obj {
    fn at_addr(n: i128) -> Self {
        Self::AtAddr(AbsInt::singleton(n))
    }

    fn project<'a>(&'a self, proj: &[AccElem]) -> Option<&'a Obj> {
        if let Some(elem) = proj.first() {
            let inner = match (self, elem) {
                (Self::Struct(fs, _), AccElem::Field(f, _)) => fs.get(f),
                (Self::Array(vs), AccElem::Index(i)) => vs
                    .iter()
                    .find_map(|(idx, obj)| if idx.equiv(i) { Some(obj) } else { None }),
                _ => None,
            };
            inner?.project(&proj[1..])
        } else {
            Some(self)
        }
    }

    fn project_mut_opt<'a>(&'a mut self, proj: &[AccElem]) -> Option<&'a mut Obj> {
        if let Some(elem) = proj.first() {
            let inner = match elem {
                AccElem::Field(f, _) => {
                    let Self::Struct(fs, _) = self else { return None };
                    fs.get_mut(f)?
                }
                AccElem::Index(i) => {
                    let Self::Array(vs) = self else { return None };
                    vs.iter_mut().find_map(|(idx, obj)| match (idx, i) {
                        (Index::Num(n1), Index::Num(n2)) if n1 == n2 => Some(obj),
                        (Index::Sym(l1), Index::Sym(l2)) if !l1.is_disjoint(l2) => Some(obj),
                        _ => None,
                    })?
                }
            };
            inner.project_mut_opt(&proj[1..])
        } else {
            Some(self)
        }
    }

    fn project_mut<'a>(&'a mut self, proj: &[AccElem], write: bool) -> &'a mut Obj {
        if let Some(elem) = proj.first() {
            let inner = match elem {
                AccElem::Field(f, is_union) => {
                    if !matches!(self, Self::Struct(_, _)) {
                        *self = Self::Struct(FxHashMap::default(), *is_union);
                    }
                    let Self::Struct(fs, _) = self else { unreachable!() };
                    if *is_union {
                        let keys: Vec<_> = fs.keys().copied().collect();
                        for k in keys {
                            if k != *f {
                                fs.remove(&k);
                            }
                        }
                    }
                    fs.entry(*f).or_insert(Obj::Top)
                }
                AccElem::Index(i) => {
                    let vs = match self {
                        Self::Array(vs) => std::mem::take(vs),
                        _ => FxHashMap::default(),
                    };
                    let mut new_vs = FxHashMap::default();
                    let mut exists = false;
                    let mut i = i.clone();
                    for (idx, obj) in vs {
                        match (&idx, &mut i) {
                            (Index::Num(n1), Index::Num(n2)) => {
                                if n1 == n2 {
                                    exists = true;
                                }
                                new_vs.insert(idx, obj);
                            }
                            (Index::Sym(l1), Index::Sym(l2)) if !l1.is_disjoint(l2) => {
                                exists = true;
                                l2.extend(l1);
                                new_vs.insert(i.clone(), obj);
                            }
                            _ => {
                                if !write {
                                    new_vs.insert(idx, obj);
                                }
                            }
                        }
                    }
                    if !exists {
                        new_vs.insert(i.clone(), Obj::Top);
                    }
                    *self = Obj::Array(new_vs);
                    let Obj::Array(vs) = self else { unreachable!() };
                    vs.get_mut(&i).unwrap()
                }
            };
            inner.project_mut(&proj[1..], write)
        } else {
            self
        }
    }

    fn substitute(&mut self, old_loc: &AbsLoc, new_loc: &AbsLoc) {
        match self {
            Self::Top | Self::AtAddr(_) => {}
            Self::Ptr(loc) => {
                if loc == old_loc {
                    *loc = new_loc.clone();
                }
            }
            Self::Struct(fs, _) => {
                for obj in fs.values_mut() {
                    obj.substitute(old_loc, new_loc);
                }
            }
            Self::Array(vs) => {
                for obj in vs.values_mut() {
                    obj.substitute(old_loc, new_loc);
                }
            }
        }
    }

    fn extend_loc(&mut self, loc: &AbsLoc) {
        match self {
            Self::Top | Self::AtAddr(_) => {}
            Self::Ptr(curr_loc) => {
                if curr_loc == loc {
                    curr_loc.projection.push(AccElem::num_index(0));
                }
            }
            Self::Struct(fs, _) => {
                for obj in fs.values_mut() {
                    obj.extend_loc(loc);
                }
            }
            Self::Array(vs) => {
                for obj in vs.values_mut() {
                    obj.extend_loc(loc);
                }
            }
        }
    }

    fn invalidate_symbolic(&mut self, local: Local) {
        match self {
            Self::Top | Self::AtAddr(_) | Self::Ptr(_) => {}
            Self::Struct(fs, _) => {
                for obj in fs.values_mut() {
                    obj.invalidate_symbolic(local);
                }
            }
            Self::Array(vs) => {
                let old_vs = std::mem::take(vs);
                for (mut idx, mut obj) in old_vs {
                    if let Index::Sym(ls) = &mut idx {
                        ls.remove(&local);
                    }
                    obj.invalidate_symbolic(local);
                    vs.insert(idx, obj);
                }
            }
        }
    }

    fn collect_locals(&self, locals: &mut DenseBitSet<Local>) {
        match self {
            Self::Top | Self::AtAddr(_) => {}
            Self::Ptr(loc) => {
                for elem in &loc.projection {
                    elem.collect_locals(locals);
                }
            }
            Self::Struct(fs, _) => {
                for obj in fs.values() {
                    obj.collect_locals(locals);
                }
            }
            Self::Array(vs) => {
                for (idx, obj) in vs {
                    idx.collect_locals(locals);
                    obj.collect_locals(locals);
                }
            }
        }
    }

    pub fn as_ptr(&self) -> &AbsLoc {
        let Obj::Ptr(loc) = self else { panic!() };
        loc
    }

    pub fn field(&self, i: u32) -> &Obj {
        let Obj::Struct(fs, _) = self else { panic!() };
        fs.get(&FieldIdx::from_u32(i)).unwrap()
    }

    #[allow(clippy::should_implement_trait)]
    pub fn index(&self, i: i128) -> &Obj {
        let Obj::Array(vs) = self else { panic!() };
        vs.get(&Index::Num(i)).unwrap()
    }

    pub fn symbolic(&self, index: &[Local]) -> Option<&Obj> {
        let Obj::Array(vs) = self else { panic!() };
        let index = index.iter().copied().collect();
        vs.get(&Index::Sym(index))
    }
}

#[derive(Clone, PartialEq, Eq)]
#[repr(transparent)]
pub struct Node {
    pub obj: Obj,
}

impl std::fmt::Debug for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.obj)
    }
}

impl std::ops::Deref for Node {
    type Target = Obj;

    fn deref(&self) -> &Self::Target {
        &self.obj
    }
}

impl std::ops::DerefMut for Node {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.obj
    }
}

impl Node {
    #[inline]
    fn new(obj: Obj) -> Self {
        Self { obj }
    }
}

#[derive(Clone, Default)]
pub struct Graph {
    pub nodes: IndexVec<NodeId, Node>,
    locals: FxHashMap<Local, NodeId>,
    statics: FxHashMap<LocalDefId, NodeId>,
    ints: FxHashMap<i128, AbsLoc>,
}

impl std::fmt::Debug for Graph {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let nodes: BTreeMap<_, _> = self.nodes.iter().enumerate().collect();
        let locals: BTreeMap<_, _> = self.locals.iter().map(|(l, n)| (*l, *n)).collect();
        f.debug_struct("Graph")
            .field("nodes", &nodes)
            .field("locals", &locals)
            .finish()
    }
}

impl Graph {
    fn join(&self, other: &Self, widen: bool) -> Self {
        let mut ctx = JoinCtx {
            joined: Graph::default(),
            id_map: FxHashMap::default(),
            remaining: vec![],
            widen,
        };

        for (l1, id1) in &self.locals {
            let (_, id2) = some_or!(other.locals.iter().find(|(l2, _)| l1 == *l2), continue);
            let (id, _) = ctx.joined.get_local_node_mut(*l1);
            let idp = (AbsLoc::new_root(*id1), AbsLoc::new_root(*id2));
            ctx.id_map.insert(idp.clone(), id);
            ctx.remaining.push(idp);
        }

        for (s1, id1) in &self.statics {
            let (_, id2) = some_or!(other.statics.iter().find(|(s2, _)| s1 == *s2), continue);
            let id = ctx.joined.get_static(*s1);
            let idp = (AbsLoc::new_root(*id1), AbsLoc::new_root(*id2));
            ctx.id_map.insert(idp.clone(), id);
            ctx.remaining.push(idp);
        }

        while let Some((loc1, loc2)) = ctx.remaining.pop() {
            let obj1 = self.obj_at_location(&loc1);
            let obj2 = other.obj_at_location(&loc2);
            let id = ctx.id_map[&(loc1, loc2)];

            let mut obj = Obj::Top;
            if let (Some(obj1), Some(obj2)) = (obj1, obj2) {
                join_objs(obj1, obj2, &mut obj, AbsLoc::new_root(id), &mut ctx);
            }
            ctx.joined.nodes[id].obj = obj;
        }

        ctx.joined
    }

    fn ord(&self, other: &Self) -> bool {
        let mut id_set = FxHashSet::default();
        let mut remaining = vec![];

        for (l2, id2) in &other.locals {
            let (_, id1) = some_or!(self.locals.iter().find(|(l1, _)| *l1 == l2), return false);
            let idp = (*id1, *id2);
            id_set.insert(idp);
            remaining.push(idp);
        }

        while let Some((id1, id2)) = remaining.pop() {
            let node1 = &self.nodes[id1];
            let node2 = &other.nodes[id2];

            if !ord_objs(node1, node2, &mut id_set, &mut remaining) {
                return false;
            }
        }

        true
    }

    fn add_node(&mut self) -> (NodeId, &mut Node) {
        let id = self.nodes.next_index();
        self.nodes.push(Node::new(Obj::Top));
        (id, &mut self.nodes[id])
    }

    fn get_int_node(&mut self, n: i128) -> AbsLoc {
        if let Some(id) = self.ints.get(&n) {
            id.clone()
        } else {
            let id = self.nodes.next_index();
            let node = Node::new(Obj::at_addr(n));
            self.nodes.push(node);
            let loc = AbsLoc::new_root(id);
            self.ints.insert(n, loc.clone());
            loc
        }
    }

    fn get_local_node_mut(&mut self, l: Local) -> (NodeId, &mut Node) {
        let id = if let Some(id) = self.locals.get(&l) {
            *id
        } else {
            let (id, _) = self.add_node();
            self.locals.insert(l, id);
            id
        };
        (id, &mut self.nodes[id])
    }

    pub fn assign(&mut self, l: &AccPath, l_deref: bool, r: &OpVal) {
        match r {
            OpVal::Place(r, r_deref) => self.x_eq_y(l, l_deref, r, *r_deref),
            OpVal::Static(s) => self.x_eq_static(l, l_deref, *s),
            OpVal::Int(n) => self.x_eq_int(l, l_deref, *n),
            OpVal::Other => self.x_eq(l, l_deref),
        }
    }

    pub fn assign_union<'a, T>(
        &mut self,
        l: &AccPath,
        l_deref: bool,
        r: &OpVal,
        tys: &[(T, &'a TyShape<'a, '_>)],
    ) {
        let OpVal::Place(r_path, r_deref) = r else { return };
        let loc = some_or!(self.path_to_loc(r_path.clone()), return);
        let loc = if *r_deref {
            let obj = some_or!(self.obj_at_location(&loc), return);
            let Obj::Ptr(loc) = obj else { return };
            loc
        } else {
            &loc
        };
        let obj = some_or!(self.obj_at_location(loc), return);
        let Obj::Struct(fields, is_union) = obj else { return };
        assert!(*is_union);
        assert!(fields.len() <= 1);
        let (f, _) = some_or!(fields.iter().next(), return);

        let l = l.extended(&[AccElem::Field(*f, true)]);
        let r = r.extended(&[AccElem::Field(*f, true)]);
        let ty = tys[f.as_usize()].1;
        self.assign_with_ty(&l, l_deref, &r, ty);
    }

    pub fn assign_with_ty<'a>(
        &mut self,
        l: &AccPath,
        l_deref: bool,
        r: &OpVal,
        ty: &'a TyShape<'a, '_>,
    ) {
        match ty {
            TyShape::Primitive(_) => self.assign(l, l_deref, r),
            TyShape::Array(ty, len) => {
                for i in 0..(*len).min(10) {
                    let l = l.extended(&[AccElem::num_index(i as _)]);
                    let r = r.extended(&[AccElem::num_index(i as _)]);
                    self.assign_with_ty(&l, l_deref, &r, ty);
                }
            }
            TyShape::Struct(_, tys, is_union) => {
                if *is_union {
                    self.assign_union(l, l_deref, r, tys);
                } else {
                    for (i, (_, ty)) in tys.iter().enumerate() {
                        let i = FieldIdx::from_usize(i);
                        let l = l.extended(&[AccElem::Field(i, false)]);
                        let r = r.extended(&[AccElem::Field(i, false)]);
                        self.assign_with_ty(&l, l_deref, &r, ty);
                    }
                }
            }
        }
    }

    pub fn objs_at(&self, l: Local, proj: &[tag_analysis::AccElem]) -> Vec<&Obj> {
        let id = some_or!(self.locals.get(&l), return vec![]);
        self.obj_at_rec(&self.nodes[*id].obj, proj)
    }

    fn obj_at_rec<'a>(&'a self, obj: &'a Obj, proj: &[tag_analysis::AccElem]) -> Vec<&'a Obj> {
        if let Some(elem) = proj.first() {
            match elem {
                tag_analysis::AccElem::Field(f) => {
                    let Obj::Struct(fs, _) = obj else { return vec![] };
                    let obj = some_or!(fs.get(f), return vec![]);
                    self.obj_at_rec(obj, &proj[1..])
                }
                tag_analysis::AccElem::Index => {
                    let Obj::Array(vs) = obj else { return vec![] };
                    vs.values()
                        .flat_map(|obj| self.obj_at_rec(obj, &proj[1..]))
                        .collect()
                }
                tag_analysis::AccElem::Deref => {
                    let Obj::Ptr(loc) = obj else { return vec![] };
                    let obj = some_or!(self.obj_at_location(loc), return vec![]);
                    self.obj_at_rec(obj, &proj[1..])
                }
            }
        } else {
            vec![obj]
        }
    }

    pub fn get_obj(&self, x: &AccPath, deref: bool) -> Option<&Obj> {
        if deref {
            let id = self.locals.get(&x.local)?;
            let mut loc = self.get_pointed_loc(*id, &[])?;
            loc.projection.extend(x.projection.to_owned());
            let node = &self.nodes[loc.root];
            node.project(&loc.projection)
        } else {
            let id = self.locals.get(&x.local)?;
            let node = &self.nodes[*id];
            node.project(&x.projection)
        }
    }

    fn lvalue(&mut self, x: &AccPath, deref: bool) -> &mut Obj {
        if deref {
            let (id, _) = self.get_local_node_mut(x.local);
            let mut loc = self.get_pointed_loc_mut(id, &[], true);
            loc.projection.extend(x.projection.to_owned());
            let node = &mut self.nodes[loc.root];
            node.project_mut(&loc.projection, true)
        } else {
            let (_, node) = self.get_local_node_mut(x.local);
            node.project_mut(&x.projection, true)
        }
    }

    fn rvalue(&mut self, x: &AccPath, deref: bool) -> AbsLoc {
        let (id, _) = self.get_local_node_mut(x.local);
        if deref {
            let mut loc = self.get_pointed_loc_mut(id, &[], false);
            loc.projection.extend(x.projection.to_owned());
            self.get_pointed_loc_mut(loc.root, &loc.projection, false)
        } else {
            self.get_pointed_loc_mut(id, &x.projection, false)
        }
    }

    fn x_eq_y(&mut self, x: &AccPath, x_deref: bool, y: &AccPath, y_deref: bool) {
        let loc = self.rvalue(y, y_deref);
        let obj = self.lvalue(x, x_deref);
        *obj = Obj::Ptr(loc);
    }

    fn get_static(&mut self, s: LocalDefId) -> NodeId {
        if let Some(id) = self.statics.get(&s) {
            *id
        } else {
            let (id, _) = self.add_node();
            self.statics.insert(s, id);
            id
        }
    }

    fn x_eq_static(&mut self, x: &AccPath, x_deref: bool, y: LocalDefId) {
        let id = self.get_static(y);
        let obj = self.lvalue(x, x_deref);
        *obj = Obj::Ptr(AbsLoc::new_root(id));
    }

    fn x_eq_int(&mut self, x: &AccPath, deref: bool, n: i128) {
        let loc = self.get_int_node(n);
        let obj = self.lvalue(x, deref);
        *obj = Obj::Ptr(loc);
    }

    pub fn x_eq(&mut self, x: &AccPath, deref: bool) {
        let obj = self.lvalue(x, deref);
        *obj = Obj::Top;
    }

    pub fn x_eq_ref_y(&mut self, x: &AccPath, y: &AccPath, y_deref: bool) {
        let (id, _) = self.get_local_node_mut(y.local);
        let loc = if y_deref {
            let mut loc = self.get_pointed_loc_mut(id, &[], false);
            loc.projection.extend(y.projection.to_owned());
            loc
        } else {
            AbsLoc::new(id, y.projection.to_owned())
        };

        let obj = self.lvalue(x, false);
        *obj = Obj::Ptr(loc);
    }

    pub fn x_eq_offset(&mut self, x: &AccPath, y: &AccPath, idx: OpVal) {
        let (id, _) = self.get_local_node_mut(y.local);
        let loc = self.get_pointed_loc_mut(id, &[], false);
        let mut loc = if loc.projection.is_empty() {
            let Obj::Ptr(loc) = &self.nodes[id].obj else { panic!() };
            let mut loc = loc.clone();
            self.extend_loc(&loc);
            loc.projection.push(AccElem::num_index(0));
            self.obj_at_location_mut(&loc, false);
            loc
        } else {
            loc
        };
        let elem = loc.projection.last_mut().unwrap();
        if let AccElem::Index(Index::Num(n)) = elem {
            match idx {
                OpVal::Place(idx, idx_deref) => {
                    assert!(idx.projection.is_empty());
                    assert!(!idx_deref);
                    *elem = AccElem::sym_index(self.find_aliases(idx.local));
                    let obj = self.lvalue(x, false);
                    *obj = Obj::Ptr(loc);
                }
                OpVal::Static(_) => unreachable!(),
                OpVal::Int(idx) => {
                    *n += idx;
                    let obj = self.lvalue(x, false);
                    *obj = Obj::Ptr(loc);
                }
                OpVal::Other => {
                    let obj = self.lvalue(x, false);
                    *obj = Obj::Top;
                }
            }
        } else {
            let obj = self.lvalue(x, false);
            *obj = Obj::Top;
        }
    }

    pub fn x_eq_offset_int(&mut self, x: &AccPath, y: &AccPath, idx: i128) {
        let (id, _) = self.get_local_node_mut(y.local);
        let mut loc = self.get_pointed_loc_mut(id, &[], false);
        let obj = self.lvalue(x, false);
        let elem = loc.projection.last_mut().unwrap();
        if let AccElem::Index(Index::Num(n)) = elem {
            *n += idx;
            *obj = Obj::Ptr(loc);
        } else {
            *obj = Obj::Top;
        }
    }

    pub fn filter_x_int(&mut self, x: &AccPath, deref: bool, n: i128) {
        let ptr_loc = self.set_obj_ptr(|this| this.lvalue(x, deref));
        if let Some(n_loc) = self.ints.get(&n) {
            let n_loc = n_loc.clone();
            self.substitute(&ptr_loc, &n_loc);
        } else {
            let obj = self.obj_at_location_mut(&ptr_loc, false);
            *obj = Obj::at_addr(n);
            self.ints.insert(n, ptr_loc);
        }
    }

    pub fn filter_x_not_ints<I: Iterator<Item = i128>>(
        &mut self,
        x: &AccPath,
        deref: bool,
        nums: I,
    ) {
        let ptr_loc = self.set_obj_ptr(|this| this.lvalue(x, deref));
        let obj = self.obj_at_location_mut(&ptr_loc, false);
        let Obj::AtAddr(ns) = obj else { return };
        let mut nset = ns.as_set();
        let mut removed = false;
        for n in nums {
            removed |= nset.remove(&n);
        }
        if !removed {
            return;
        }
        if nset.len() == 1 {
            let n = *nset.iter().next().unwrap();
            if let Some(n_loc) = self.ints.get(&n) {
                let n_loc = n_loc.clone();
                self.substitute(&ptr_loc, &n_loc);
            } else {
                let obj = self.obj_at_location_mut(&ptr_loc, false);
                *obj = Obj::at_addr(n);
                self.ints.insert(n, ptr_loc);
            }
        } else {
            *ns = AbsInt::new(nset);
        }
    }

    fn substitute(&mut self, old_loc: &AbsLoc, new_loc: &AbsLoc) {
        for node in &mut self.nodes {
            node.substitute(old_loc, new_loc);
        }
    }

    fn extend_loc(&mut self, loc: &AbsLoc) {
        for node in &mut self.nodes {
            node.extend_loc(loc);
        }
    }

    pub fn find_aliases(&self, local: Local) -> BTreeSet<Local> {
        let mut aliases = BTreeSet::new();
        aliases.insert(local);
        let loc1 = some_or!(self.loc_pointed_by_local(local), return aliases);
        for l in self.locals.keys() {
            let loc2 = some_or!(self.loc_pointed_by_local(*l), continue);
            if loc1 == loc2 {
                aliases.insert(*l);
            }
        }
        aliases
    }

    fn loc_pointed_by_local(&self, local: Local) -> Option<&AbsLoc> {
        let id = self.locals.get(&local)?;
        let node = &self.nodes[*id];
        if let Obj::Ptr(loc) = &node.obj {
            Some(loc)
        } else {
            None
        }
    }

    pub fn get_local_as_int(&self, x: Local) -> Option<i128> {
        self.get_x_as_int(&AccPath::new(x, vec![]), false)
    }

    pub fn get_x_as_int(&self, x: &AccPath, deref: bool) -> Option<i128> {
        let id = self.locals.get(&x.local)?;
        let loc = if deref {
            let mut loc = self.get_pointed_loc(*id, &[])?;
            loc.projection.extend(x.projection.to_owned());
            self.get_pointed_loc(loc.root, &loc.projection)?
        } else {
            self.get_pointed_loc(*id, &x.projection)?
        };
        self.get_absloc_as_int(&loc)
    }

    pub fn get_absloc_as_int(&self, loc: &AbsLoc) -> Option<i128> {
        let obj = self.obj_at_location(loc)?;
        let Obj::AtAddr(n) = obj else { return None };
        n.as_singleton()
    }

    pub fn invalidate_symbolic(&mut self, local: Local) {
        for node in &mut self.nodes {
            node.invalidate_symbolic(local);
        }
    }

    fn get_pointed_loc(&self, node_id: NodeId, proj: &[AccElem]) -> Option<AbsLoc> {
        let obj = self.nodes[node_id].project(proj)?;
        let Obj::Ptr(loc) = obj else { return None };
        Some(loc.clone())
    }

    fn get_pointed_loc_mut(&mut self, node_id: NodeId, proj: &[AccElem], write: bool) -> AbsLoc {
        self.set_obj_ptr(|this| this.nodes[node_id].project_mut(proj, write))
    }

    #[inline]
    fn set_obj_ptr<F: Fn(&mut Self) -> &mut Obj>(&mut self, f: F) -> AbsLoc {
        let obj = f(self);
        if let Obj::Ptr(loc) = obj {
            loc.clone()
        } else {
            let obj: *mut Obj = obj;
            let next_id = self.nodes.next_index();
            let loc = AbsLoc::new(next_id, vec![AccElem::num_index(0)]);
            unsafe {
                *obj = Obj::Ptr(loc.clone());
            }
            let obj = Obj::Array(FxHashMap::from_iter([(Index::Num(0), Obj::Top)]));
            self.nodes.push(Node::new(obj));
            loc
        }
    }

    pub fn deref_local_id(&self, local: Local) -> Option<NodeId> {
        let id = self.locals.get(&local)?;
        let loc = self.get_pointed_loc(*id, &[])?;
        Some(loc.root)
    }

    pub fn obj_at_location(&self, loc: &AbsLoc) -> Option<&Obj> {
        self.nodes[loc.root].project(&loc.projection)
    }

    fn obj_at_location_mut_opt(&mut self, loc: &AbsLoc) -> Option<&mut Obj> {
        self.nodes[loc.root].project_mut_opt(&loc.projection)
    }

    fn obj_at_location_mut(&mut self, loc: &AbsLoc, write: bool) -> &mut Obj {
        self.nodes[loc.root].project_mut(&loc.projection, write)
    }

    pub fn get_local_id(&self, local: Local) -> NodeId {
        *self.locals.get(&local).unwrap()
    }

    pub fn get_local_node(&self, local: Local) -> &Node {
        &self.nodes[self.get_local_id(local)]
    }

    fn clear_dead_locals(&mut self, dead_locals: &DenseBitSet<Local>) {
        let mut locals = DenseBitSet::new_empty(dead_locals.domain_size());
        for node in &self.nodes {
            node.collect_locals(&mut locals);
        }
        self.locals
            .retain(|local, _| !dead_locals.contains(*local) || locals.contains(*local));
    }

    fn path_to_loc(&self, path: AccPath) -> Option<AbsLoc> {
        let root = self.locals.get(&path.local)?;
        Some(AbsLoc::new(*root, path.projection))
    }

    pub fn strong_update_loc(&self, path: AccPath, deref: bool) -> Option<AbsLoc> {
        let mut loc = self.path_to_loc(path)?;
        let loc = if deref {
            let projection = std::mem::take(&mut loc.projection);
            let obj = self.obj_at_location(&loc)?;
            let Obj::Ptr(loc) = obj else { return None };
            let mut loc = loc.clone();
            loc.projection.extend(projection);
            loc
        } else {
            loc
        };
        Some(loc)
    }

    pub fn invalidate(
        &mut self,
        func: LocalDefId,
        strong_update: Option<&AbsLoc>,
        strong_local: bool,
        may_points_to: &andersen::AnalysisResult,
        writes: &ChunkedBitSet<andersen::Loc>,
    ) {
        let mut no_update_locals = FxHashSet::default();
        if strong_local {
            for node_id in self.locals.values() {
                no_update_locals.insert(*node_id);
            }
        }
        let mut worklist: Vec<_> = self
            .locals
            .iter()
            .map(|(local, node_id)| {
                let loc = AbsLoc::new_root(*node_id);
                let node = may_points_to.var_nodes[&(func, *local)];
                (loc, node)
            })
            .collect();
        let mut visited = FxHashSet::default();
        let ctx = InvalidateCtx {
            strong_update,
            no_update_locals: &no_update_locals,
            may_points_to,
            writes,
        };
        while let Some((loc, node)) = worklist.pop() {
            let obj = some_or!(self.obj_at_location_mut_opt(&loc), continue);
            worklist.extend(invalidate_rec(loc, obj, node, &mut visited, ctx));
        }
    }
}

#[derive(Clone, Copy)]
struct InvalidateCtx<'a> {
    strong_update: Option<&'a AbsLoc>,
    no_update_locals: &'a FxHashSet<NodeId>,
    may_points_to: &'a andersen::AnalysisResult,
    writes: &'a ChunkedBitSet<andersen::Loc>,
}

fn invalidate_rec(
    loc: AbsLoc,
    obj: &mut Obj,
    node: andersen::LocNode,
    visited: &mut FxHashSet<(AbsLoc, andersen::LocNode)>,
    ctx: InvalidateCtx<'_>,
) -> Vec<(AbsLoc, andersen::LocNode)> {
    if !visited.insert((loc.clone(), node)) {
        return vec![];
    }
    let edges = &ctx.may_points_to.graph[&node];
    match obj {
        Obj::Top | Obj::AtAddr(_) => vec![],
        Obj::Ptr(ptr_loc) => {
            let v = if let andersen::LocEdges::Deref(nodes) = edges {
                nodes.iter().map(|node| (ptr_loc.clone(), *node)).collect()
            } else {
                vec![]
            };

            if node.prefix == 0
                && ctx.writes.contains(node.index)
                && !ctx.no_update_locals.contains(&loc.root)
                && ctx
                    .strong_update
                    .map(|s| !s.is_prefix_of(&loc))
                    .unwrap_or(true)
            {
                *obj = Obj::Top;
            }

            v
        }
        Obj::Struct(fs, is_union) => {
            let mut v = vec![];
            if let andersen::LocEdges::Fields(fs2) = edges {
                for (index, node) in fs2.iter_enumerated() {
                    let obj = some_or!(fs.get_mut(&index), continue);
                    let loc = loc.clone().push_field(index, *is_union);
                    v.extend(invalidate_rec(loc, obj, *node, visited, ctx));
                }
            }
            if *is_union {
                let index = node.index;
                if let Some(offsets) = ctx.may_points_to.union_offsets.get(&index) {
                    for (field, (offset, next)) in
                        offsets.iter().zip(offsets.iter().skip(1)).enumerate()
                    {
                        if !fs.contains_key(&FieldIdx::from_usize(field))
                            && (*offset..*next).any(|o| ctx.writes.contains(index + o))
                        {
                            *fs = FxHashMap::default();
                            break;
                        }
                    }
                }
            }
            v
        }
        Obj::Array(vs) => {
            let mut v = vec![];
            if let andersen::LocEdges::Index(node) = edges {
                for (elem, obj) in vs {
                    let loc = loc.clone().push_index(elem.clone());
                    v.extend(invalidate_rec(loc, obj, *node, visited, ctx));
                }
            }
            v
        }
    }
}

struct JoinCtx {
    joined: Graph,
    id_map: FxHashMap<(AbsLoc, AbsLoc), NodeId>,
    remaining: Vec<(AbsLoc, AbsLoc)>,
    widen: bool,
}

fn join_objs(obj1: &Obj, obj2: &Obj, obj: &mut Obj, curr_loc: AbsLoc, ctx: &mut JoinCtx) {
    match (obj1, obj2) {
        (Obj::AtAddr(i1), Obj::AtAddr(i2)) => {
            let i = i1.join(i2, ctx.widen);
            if let Some(i) = i.as_singleton() {
                ctx.joined.ints.insert(i, curr_loc);
            }
            *obj = Obj::AtAddr(i);
        }
        (Obj::Ptr(l1), Obj::Ptr(l2)) => {
            let (idp, l) = if let Some(l) = cmp_projection(&l1.projection, &l2.projection) {
                ((AbsLoc::new_root(l1.root), AbsLoc::new_root(l2.root)), l)
            } else {
                ((l1.clone(), l2.clone()), vec![])
            };
            let nid = if let Some(id) = ctx.id_map.get(&idp) {
                *id
            } else {
                let (id, _) = ctx.joined.add_node();
                ctx.id_map.insert(idp.clone(), id);
                ctx.remaining.push(idp);
                id
            };
            *obj = Obj::Ptr(AbsLoc::new(nid, l));
        }
        (Obj::Struct(fs1, u1), Obj::Struct(fs2, u2)) => {
            assert_eq!(u1, u2);
            let mut fs = FxHashMap::default();
            for (f, obj1) in fs1 {
                let obj2 = some_or!(fs2.get(f), continue);
                let mut new_obj = Obj::Top;
                let curr_loc = curr_loc.clone().push_field(*f, *u1);
                join_objs(obj1, obj2, &mut new_obj, curr_loc, ctx);
                fs.insert(*f, new_obj);
            }
            *obj = Obj::Struct(fs, *u1);
        }
        (Obj::Array(vs1), Obj::Array(vs2)) => {
            let mut fs = FxHashMap::default();
            for (v1, obj1) in vs1 {
                for (v2, obj2) in vs2 {
                    let v = v1.join(v2);
                    let mut nobj = Obj::Top;
                    let curr_loc = curr_loc.clone().push_index(v.clone());
                    join_objs(obj1, obj2, &mut nobj, curr_loc, ctx);
                    fs.insert(v, nobj);
                }
            }
            *obj = Obj::Array(fs);
        }
        _ => {}
    }
}

fn cmp_projection(proj1: &[AccElem], proj2: &[AccElem]) -> Option<Vec<AccElem>> {
    if proj1.len() != proj2.len() {
        return None;
    }
    let mut proj = vec![];
    for e in proj1.iter().zip(proj2) {
        match e {
            (AccElem::Field(i1, u1), AccElem::Field(i2, u2)) if i1 == i2 && u1 == u2 => {
                proj.push(AccElem::Field(*i1, *u1))
            }
            (AccElem::Index(Index::Num(i1)), AccElem::Index(Index::Num(i2))) if i1 == i2 => {
                proj.push(AccElem::num_index(*i1))
            }
            (AccElem::Index(Index::Sym(l1)), AccElem::Index(Index::Sym(l2))) => {
                let l: BTreeSet<_> = l1.intersection(l2).copied().collect();
                if l.is_empty() {
                    return None;
                }
                proj.push(AccElem::sym_index(l));
            }
            _ => return None,
        }
    }
    Some(proj)
}

fn ord_objs(
    obj1: &Obj,
    obj2: &Obj,
    id_set: &mut FxHashSet<(NodeId, NodeId)>,
    remaining: &mut Vec<(NodeId, NodeId)>,
) -> bool {
    match (obj1, obj2) {
        (_, Obj::Top) => true,
        (Obj::AtAddr(i1), Obj::AtAddr(i2)) => i1 == i2,
        (Obj::Ptr(l1), Obj::Ptr(l2)) => {
            let idp = (l1.root, l2.root);
            if !id_set.contains(&idp) {
                id_set.insert(idp);
                remaining.push(idp);
            }
            ord_projection(&l1.projection, &l2.projection)
        }
        (Obj::Struct(fs1, _), Obj::Struct(fs2, _)) => fs2.iter().all(|(f, obj2)| {
            let obj1 = some_or!(fs1.get(f), return false);
            ord_objs(obj1, obj2, id_set, remaining)
        }),
        (Obj::Array(vs1), Obj::Array(vs2)) => vs2.iter().all(|(idx2, obj2)| {
            let obj1 = vs1
                .iter()
                .find_map(|(idx1, obj1)| if idx1.ord(idx2) { Some(obj1) } else { None });
            let obj1 = some_or!(obj1, return false);
            ord_objs(obj1, obj2, id_set, remaining)
        }),
        _ => false,
    }
}

fn ord_projection(proj1: &[AccElem], proj2: &[AccElem]) -> bool {
    if proj1.len() != proj2.len() {
        return true;
    }
    let mut b = true;
    for e in proj1.iter().zip(proj2) {
        match e {
            (AccElem::Field(i1, u1), AccElem::Field(i2, u2)) if i1 == i2 && u1 == u2 => {}
            (AccElem::Index(Index::Num(i1)), AccElem::Index(Index::Num(i2))) if i1 == i2 => {}
            (AccElem::Index(Index::Sym(l1)), AccElem::Index(Index::Sym(l2))) => {
                if l1.is_disjoint(l2) {
                    return true;
                }
                if !l2.is_subset(l1) {
                    b = false;
                }
            }
            _ => return true,
        }
    }
    b
}

#[derive(Debug, Clone, Copy)]
pub struct DiscrVal {
    pub equal: bool,
    pub lhs: Local,
    pub rhs: Local,
}
