use etrace::some_or;
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{ItemKind, def_id::LocalDefId};
use rustc_middle::{
    mir::{Const, Local, Operand, Rvalue, Statement, StatementKind, Terminator, TerminatorKind},
    ty::{TyCtxt, TyKind},
};

use super::andersen;

pub(super) fn find_alloc_funcs(
    config: &andersen::Config,
    tcx: TyCtxt<'_>,
) -> FxHashSet<LocalDefId> {
    let mut call_graph = FxHashMap::default();
    let mut assigns = FxHashMap::default();
    for item_id in tcx.hir_free_items() {
        let item = tcx.hir_item(item_id);
        if !matches!(item.kind, ItemKind::Fn { .. }) {
            continue;
        }
        let local_def_id = item_id.owner_id.def_id;
        let sig = tcx.fn_sig(local_def_id).skip_binder();
        let output = sig.output().skip_binder();
        let TyKind::RawPtr(ty, ..) = output.kind() else {
            continue;
        };
        if !ty.is_c_void(tcx) {
            continue;
        }
        let body = if config.use_optimized_mir {
            tcx.optimized_mir(local_def_id)
        } else {
            &tcx.mir_drops_elaborated_and_const_checked(local_def_id)
                .borrow()
        };
        let mut analyzer = Analyzer::new(tcx);
        for bbd in body.basic_blocks.iter() {
            for stmt in &bbd.statements {
                analyzer.transfer_stmt(stmt);
            }
            analyzer.transfer_term(bbd.terminator());
        }
        analyzer.remove_address_takens();
        assigns.insert(local_def_id, analyzer.assigns);
        call_graph.insert(local_def_id, analyzer.calls);
    }
    let fns: FxHashSet<_> = call_graph.keys().copied().collect();
    for callees in call_graph.values_mut() {
        callees.retain(|callee| fns.contains(callee));
    }
    let sccs: utils::graph::Sccs<_, false> = utils::graph::sccs_copied(&call_graph);
    let mut alloc_fns = FxHashSet::default();
    for scc_id in sccs.post_order() {
        let scc = &sccs.scc_elems[scc_id];
        for f in scc {
            let assigns = &assigns[f];
            if is_alloc(Local::ZERO, assigns, &alloc_fns) {
                alloc_fns.insert(*f);
            }
        }
    }
    alloc_fns
}

fn is_alloc(
    local: Local,
    assigns: &FxHashMap<Local, FxHashSet<Value>>,
    alloc_fns: &FxHashSet<LocalDefId>,
) -> bool {
    let vs = some_or!(assigns.get(&local), return false);
    for v in vs {
        let b = match v {
            Value::Local(l) => is_alloc(*l, assigns, alloc_fns),
            Value::IntraCall(def_id) => alloc_fns.contains(def_id),
            Value::CCall => true,
        };
        if b {
            return true;
        }
    }
    false
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Value {
    Local(Local),
    IntraCall(LocalDefId),
    CCall,
}

struct Analyzer<'tcx> {
    tcx: TyCtxt<'tcx>,
    assigns: FxHashMap<Local, FxHashSet<Value>>,
    address_takens: FxHashSet<Local>,
    calls: FxHashSet<LocalDefId>,
}

impl<'tcx> Analyzer<'tcx> {
    #[inline]
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            assigns: FxHashMap::default(),
            address_takens: FxHashSet::default(),
            calls: FxHashSet::default(),
        }
    }

    #[inline]
    fn remove_address_takens(&mut self) {
        self.assigns
            .retain(|local, _| !self.address_takens.contains(local));
    }

    fn transfer_stmt(&mut self, stmt: &Statement<'tcx>) {
        let StatementKind::Assign(box (l, r)) = &stmt.kind else {
            return;
        };
        if !l.projection.is_empty() {
            return;
        }
        match r {
            Rvalue::Use(r) | Rvalue::Cast(_, r, _) => {
                if let Some(r) = self.transfer_op(r) {
                    self.assigns.entry(l.local).or_default().insert(r);
                }
            }
            Rvalue::Ref(_, _, r) => {
                self.address_takens.insert(r.local);
            }
            _ => {}
        }
    }

    fn transfer_op(&self, op: &Operand<'tcx>) -> Option<Value> {
        let place = op.place()?;
        if place.projection.is_empty() {
            Some(Value::Local(place.local))
        } else {
            None
        }
    }

    fn transfer_term(&mut self, term: &Terminator<'tcx>) {
        let TerminatorKind::Call {
            func, destination, ..
        } = &term.kind
        else {
            return;
        };
        if !destination.projection.is_empty() {
            return;
        }
        let constant = some_or!(func.constant(), return);
        let Const::Val(_, ty) = constant.const_ else { unreachable!() };
        let TyKind::FnDef(def_id, _) = ty.kind() else { unreachable!() };
        let local_def_id = some_or!(def_id.as_local(), return);
        let name: Vec<_> = self
            .tcx
            .def_path(*def_id)
            .data
            .into_iter()
            .map(|data| data.to_string())
            .collect();
        let is_extern = name.iter().any(|s| s.starts_with("{extern#"));
        if is_extern {
            let name = name.last().unwrap();
            if name == "malloc" || name == "calloc" || name == "realloc" {
                self.assigns
                    .entry(destination.local)
                    .or_default()
                    .insert(Value::CCall);
            }
        } else {
            self.assigns
                .entry(destination.local)
                .or_default()
                .insert(Value::IntraCall(local_def_id));
            self.calls.insert(local_def_id);
        }
    }
}
