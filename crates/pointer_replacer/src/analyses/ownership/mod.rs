pub mod infer;
pub mod solidify;
pub mod whole_program;

mod assoc;
mod call_graph;
mod discretization;
mod ptr;
pub mod ssa;
mod struct_ctxt;
mod vec_vec;

use rustc_middle::mir::Body;
use serde::{Deserialize, Serialize};

use crate::{
    analyses::{
        output_params::OutputParams,
        ownership::ssa::{
            constraint::Database,
            consume::{Consume, Voidable},
        },
    },
    utils::rustc::RustProgram,
};

#[derive(Clone, Copy, PartialEq, Eq, Debug, Serialize, Deserialize)]
pub enum Ownership {
    Owning,
    Transient,
    Unknown,
}

impl Ownership {
    #[inline]
    pub fn is_owning(&self) -> bool {
        *self == Ownership::Owning
    }
}

impl From<Option<bool>> for Ownership {
    fn from(value: Option<bool>) -> Self {
        match value {
            Some(true) => Ownership::Owning,
            Some(false) => Ownership::Transient,
            None => Ownership::Unknown,
        }
    }
}

impl std::fmt::Display for Ownership {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ownership::Owning => write!(f, "&move"),
            Ownership::Transient => write!(f, "&"),
            Ownership::Unknown => write!(f, "&any"),
        }
    }
}

impl Voidable for &[Ownership] {
    const VOID: Self = &[];

    #[inline]
    fn is_void(&self) -> bool {
        self.is_empty()
    }
}

#[derive(Clone, Debug)]
pub enum Param<Var> {
    Output(Consume<Var>),
    Normal(Var),
}

#[cfg(not(debug_assertions))]
const _: () = assert!(
    std::mem::size_of::<
        Option<Param<std::ops::Range<crate::analyses::ownership::ssa::constraint::Var>>>,
    >() == 16
);

impl<Value> Param<Value> {
    #[inline]
    pub fn map<U>(self, f: impl Fn(Value) -> U) -> Param<U> {
        match self {
            Param::Output(output_param) => Param::Output(output_param.repack(f)),
            Param::Normal(param) => Param::Normal(f(param)),
        }
    }

    #[inline]
    pub fn expect_normal(self) -> Value {
        match self {
            Param::Normal(sigs) => sigs,
            Param::Output(..) => panic!("expect normal parameter"),
        }
    }

    #[cfg(test)]
    pub fn expect_output(self) -> Consume<Value> {
        match self {
            Param::Output(consume) => consume,
            Param::Normal(..) => panic!("expect output parameter"),
        }
    }

    #[inline]
    pub fn into_input(self) -> Value {
        match self {
            Param::Output(Consume { r#use, .. }) => r#use,
            Param::Normal(normal) => normal,
        }
    }

    #[inline]
    pub fn into_output(self) -> Option<Value> {
        if let Param::Output(Consume { def, .. }) = self {
            Some(def)
        } else {
            None
        }
    }

    pub fn is_output(&self) -> bool {
        matches!(self, Param::Output(..))
    }
}

pub trait AnalysisKind<'analysis, 'db, 'tcx> {
    /// Analysis results
    type Results;
    /// Interprocedural context
    type InterCtxt;
    type DB: Database;
    fn analyze(
        crate_ctxt: CrateCtxt<'tcx>,
        output_params: &OutputParams,
    ) -> anyhow::Result<Self::Results>;
}

pub type Precision = u8;

pub struct CrateCtxt<'tcx> {
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    fn_ctxt: call_graph::CallGraph,
    struct_ctxt: struct_ctxt::StructCtxt<'tcx>,
}

impl<'tcx> CrateCtxt<'tcx> {
    pub fn new(program: &RustProgram<'tcx>) -> Self {
        let fns = program
            .functions
            .iter()
            .map(|did| did.to_def_id())
            .collect::<Vec<_>>();
        let structs = program
            .structs
            .iter()
            .map(|did| did.to_def_id())
            .collect::<Vec<_>>();

        CrateCtxt {
            tcx: program.tcx,
            fn_ctxt: call_graph::CallGraph::new(program.tcx, &fns),
            struct_ctxt: struct_ctxt::StructCtxt::new(program.tcx, &structs),
        }
    }

    #[inline]
    pub fn fns(&self) -> &[rustc_hir::def_id::DefId] {
        self.fn_ctxt.fns()
    }
}

pub fn total_deref_level(body: &Body) -> Precision {
    use rustc_middle::mir::{
        Place,
        visit::{MutatingUseContext, NonMutatingUseContext, PlaceContext, Visitor},
    };

    struct AccessDepthApproximation {
        read: usize,
        write: usize,
    }

    impl<'tcx> Visitor<'tcx> for AccessDepthApproximation {
        fn visit_place(
            &mut self,
            _: &Place<'tcx>,
            context: PlaceContext,
            _: rustc_middle::mir::Location,
        ) {
            if matches!(
                context,
                PlaceContext::MutatingUse(MutatingUseContext::Store)
            ) {
                self.write += 1;
            } else if matches!(
                context,
                PlaceContext::NonMutatingUse(
                    NonMutatingUseContext::Copy | NonMutatingUseContext::Move
                )
            ) {
                self.read += 1;
            } else if matches!(
                context,
                PlaceContext::NonMutatingUse(NonMutatingUseContext::Inspect)
            ) {
                // deref copies
                self.write += 1;
                self.read += 1;
            }
        }
    }

    let mut approximator = AccessDepthApproximation { read: 0, write: 0 };
    approximator.visit_body(body);

    let max_depth = approximator.read.max(approximator.write);

    // FIXME ok?
    // generally we expect a maximum ptr chased of depth 2
    u8::try_from(max_depth).unwrap_or(2)
}
