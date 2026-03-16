use petgraph::{
    algo::TarjanScc,
    graph::{DiGraph, NodeIndex},
};
use rustc_hash::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{Terminator, TerminatorKind, visit::Visitor},
    ty::TyCtxt,
};
use rustc_type_ir::TyKind::FnDef;
use smallvec::SmallVec;

use crate::analyses::{
    lattice::{FlatSet, Lattice},
    ownership::vec_vec::VecVec,
};

pub struct FnSig<T> {
    pub ret: T,
    pub args: SmallVec<[T; 4]>,
}

impl<T> FnSig<T> {
    pub fn new(ret: T, args: SmallVec<[T; 4]>) -> Self {
        FnSig { ret, args }
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> {
        std::iter::once(&self.ret).chain(self.args.iter())
    }
}

impl<T> FromIterator<T> for FnSig<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut iter = iter.into_iter();
        let ret = iter.next().unwrap();
        let args = iter.collect();
        FnSig { ret, args }
    }
}

impl<T: Default> Default for FnSig<T> {
    fn default() -> Self {
        Self {
            ret: Default::default(),
            args: Default::default(),
        }
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for FnSig<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("(")?;
        f.write_str(
            &self
                .args
                .iter()
                .map(|data| format!("{:?}", data))
                .collect::<Vec<_>>()
                .join(", "),
        )?;
        f.write_str(") -> ")?;
        f.write_fmt(format_args!("{:?}", self.ret))
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
pub enum Monotonicity {
    Alloc,
    Dealloc,
}

struct MonotonicityChecker<'me, 'tcx> {
    this: FlatSet<Monotonicity>,
    monotonicity: &'me FxHashMap<DefId, FlatSet<Monotonicity>>,
    tcx: TyCtxt<'tcx>,
}

impl<'me, 'tcx> Visitor<'tcx> for MonotonicityChecker<'me, 'tcx> {
    fn visit_terminator(&mut self, terminator: &Terminator<'tcx>, _: rustc_middle::mir::Location) {
        let TerminatorKind::Call { func, .. } = &terminator.kind else {
            return;
        };
        let Some(func) = func.constant() else {
            return;
        };
        let ty = func.ty();
        let &FnDef(callee, _) = ty.kind() else { unreachable!() };
        let Some(local_did) = callee.as_local() else {
            return;
        };

        match self.tcx.hir_node_by_def_id(local_did) {
            rustc_hir::Node::ForeignItem(foreign_item) => match foreign_item.ident.as_str() {
                "free" => {
                    self.this.meet(&FlatSet::Elem(Monotonicity::Dealloc));
                }
                "malloc" | "calloc" | "realloc" => {
                    self.this.meet(&FlatSet::Elem(Monotonicity::Alloc));
                }
                _ => {}
            },
            rustc_hir::Node::Item(..) => {
                let that = self.monotonicity[&callee];
                self.this.meet(&that);
            }
            _ => {}
        }
    }
}

pub struct CallGraph {
    post_order: VecVec<DefId>,
    ranked_by_n_alloc_deallocs: Vec<DefId>,
    monotonicity: FxHashMap<DefId, FlatSet<Monotonicity>>,
}

impl CallGraph {
    pub fn new(tcx: TyCtxt, functions: &[DefId]) -> Self {
        let mut graph = DiGraph::<DefId, ()>::new();
        let mut node_idx = FxHashMap::default();
        node_idx.reserve(functions.len());
        for &did in functions {
            let idx = graph.add_node(did);
            node_idx.insert(did, idx);
        }
        for &did in functions {
            let caller_idx = node_idx[&did];
            CallGraphConstruction {
                caller: did,
                caller_idx,
                graph: &mut graph,
                node_idx: &node_idx,
            }
            .visit_body(tcx.optimized_mir(did));
        }

        let mut tarjan_scc = TarjanScc::new();
        let mut post_order = VecVec::with_indices_capacity(functions.len());
        tarjan_scc.run(&graph, |nodes| {
            post_order.push_vec(nodes.iter().map(|&idx| graph[idx]));
        });
        let post_order = post_order.done();

        let mut n_alloc_deallocs = rustc_hash::FxHashMap::default();
        n_alloc_deallocs.reserve(functions.len());
        for did in functions {
            struct Vis<'tcx>(TyCtxt<'tcx>, usize);
            impl<'tcx> Visitor<'tcx> for Vis<'tcx> {
                fn visit_terminator(
                    &mut self,
                    terminator: &Terminator<'tcx>,
                    _: rustc_middle::mir::Location,
                ) {
                    let tcx = self.0;
                    let TerminatorKind::Call { func, .. } = &terminator.kind else { return };
                    if let Some(func) = func.constant() {
                        let ty = func.ty();
                        let &FnDef(callee, _) = ty.kind() else { unreachable!() };
                        if let Some(local_did) = callee.as_local() {
                            if let rustc_hir::Node::ForeignItem(foreign_item) =
                                tcx.hir_node_by_def_id(local_did)
                            {
                                match foreign_item.ident.as_str() {
                                    "free" => self.1 += 10,
                                    "malloc" | "calloc" | "realloc" => self.1 += 1,
                                    _ => {}
                                }
                            }
                        }
                    }
                }
            }
            let mut vis = Vis(tcx, 0);
            let body = tcx.optimized_mir(*did);
            vis.visit_body(body);
            n_alloc_deallocs.insert(*did, vis.1);
        }
        let mut ranked_by_n_alloc_deallocs = functions.to_vec();
        ranked_by_n_alloc_deallocs
            .sort_by(|f, g| n_alloc_deallocs[f].cmp(&n_alloc_deallocs[g]).reverse());

        let mut monotonicity = FxHashMap::default();
        monotonicity.reserve(functions.len());
        tarjan_scc.run(&graph, |nodes| {
            monotonicity.extend(nodes.iter().map(|&node| (graph[node], FlatSet::Top)));
            loop {
                let mut changed = false;

                for did in nodes {
                    let did = graph[*did];
                    let body = tcx.optimized_mir(did);
                    let original = monotonicity[&did];
                    let mut mc = MonotonicityChecker {
                        this: original,
                        monotonicity: &monotonicity,
                        tcx,
                    };
                    mc.visit_body(body);
                    let new = mc.this;
                    if original != new {
                        changed = true;
                        *monotonicity.get_mut(&did).unwrap() = new;
                    }
                }

                if !changed {
                    break;
                }
            }
        });

        CallGraph {
            post_order,
            ranked_by_n_alloc_deallocs,
            monotonicity,
        }
    }

    pub fn monotonicity(&self, did: DefId) -> FlatSet<Monotonicity> {
        self.monotonicity[&did]
    }

    #[inline]
    pub fn fns(&self) -> &[DefId] {
        &self.ranked_by_n_alloc_deallocs
    }

    pub fn sccs(&self) -> impl Iterator<Item = &[DefId]> {
        self.post_order.iter()
    }
}

struct CallGraphConstruction<'me> {
    caller: DefId,
    caller_idx: NodeIndex,
    graph: &'me mut DiGraph<DefId, ()>,
    node_idx: &'me FxHashMap<DefId, NodeIndex>,
}

impl<'me, 'tcx> Visitor<'tcx> for CallGraphConstruction<'me> {
    fn visit_terminator(
        &mut self,
        terminator: &Terminator<'tcx>,
        _location: rustc_middle::mir::Location,
    ) {
        let TerminatorKind::Call { func, .. } = &terminator.kind else { return };
        let Some(func_constant) = func.constant() else { return };
        let ty = func_constant.ty();
        let &FnDef(callee, _generic_args) = ty.kind() else {
            unreachable!("what could it be? {}", ty)
        };
        let Some(&callee_idx) = self.node_idx.get(&callee) else { return };
        self.graph.add_edge(self.caller_idx, callee_idx, ());
    }
}

#[cfg(test)]
mod test {
    use rustc_hir::{ItemKind, OwnerNode, def_id::DefId};
    use rustc_middle::ty::TyCtxt;
    use utils::compilation;

    use super::CallGraph;

    const TEST_PROGRAMS: &str = "
        fn f() {
            assert!(true);
            if cond() {
                g()
            }
        }
        fn g() {
            h()
        }
        fn h() {
            if !cond() {
                f();
            }
            if cond() {
                g();
            }
            l()
        }
        fn m() {
            g()
        }
        fn l() {}
        #[inline(never)]
        fn cond() -> bool {
            true
        }
        ";

    fn run_compiler<F: FnOnce(TyCtxt<'_>) + Send>(code: &str, f: F) {
        compilation::run_compiler_on_str(code, f).unwrap_or_else(|e| e.raise());
    }

    fn collect_functions(tcx: TyCtxt<'_>) -> Vec<DefId> {
        let mut functions = Vec::new();
        for maybe_owner in tcx.hir_crate(()).owners.iter() {
            let Some(owner) = maybe_owner.as_owner() else { continue };
            let OwnerNode::Item(item) = owner.node() else { continue };
            if let ItemKind::Fn { .. } = item.kind {
                functions.push(item.owner_id.def_id.to_def_id());
            }
        }
        functions
    }

    fn short_name(tcx: TyCtxt<'_>, did: DefId) -> String {
        let path = tcx.def_path_str(did);
        path.rsplit("::").next().unwrap_or(&path).to_string()
    }

    #[test]
    fn test() {
        run_compiler(TEST_PROGRAMS, |tcx| {
            let functions = collect_functions(tcx);
            let call_graph = CallGraph::new(tcx, &functions[..]);

            assert_eq!(call_graph.sccs().count(), 4);

            let mut groups = call_graph
                .sccs()
                .map(|nodes| {
                    let mut names = nodes
                        .iter()
                        .map(|&did| short_name(tcx, did))
                        .collect::<Vec<_>>();
                    names.sort();
                    names
                })
                .collect::<Vec<_>>();
            groups.sort();

            let mut expected = vec![
                vec!["cond".to_string()],
                vec!["l".to_string()],
                vec!["f".to_string(), "g".to_string(), "h".to_string()],
                vec!["m".to_string()],
            ];
            expected.sort();

            assert_eq!(groups, expected);
        });
    }
}
