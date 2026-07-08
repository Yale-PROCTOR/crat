use crate::analyses::pointer_flow::{
    graph::{PfgNode, UnknownReason},
    slots::{SlotIdx, SlotPathElem},
};

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct FunctionSummary {
    pub(crate) completeness: SummaryCompleteness,
    pub(crate) return_flows: Vec<SummaryFlow>,
    pub(crate) arg_write_flows: Vec<ArgWriteFlow>,
    pub(crate) unknown_return_slots: Vec<Vec<SlotPathElem>>,
    pub(crate) unknown_arg_writes: Vec<ArgWriteTarget>,
}

impl FunctionSummary {
    pub(crate) fn is_complete(&self) -> bool {
        self.completeness == SummaryCompleteness::Complete
    }

    pub(crate) fn normalize(&mut self) {
        self.return_flows.sort();
        self.return_flows.dedup();
        self.arg_write_flows.sort();
        self.arg_write_flows.dedup();
        self.unknown_return_slots.sort();
        self.unknown_return_slots.dedup();
        self.unknown_arg_writes.sort();
        self.unknown_arg_writes.dedup();
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) enum SummaryCompleteness {
    Complete,
    #[default]
    Incomplete,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct SummaryFlow {
    pub(crate) dst_return_path: Vec<SlotPathElem>,
    pub(crate) src: SummarySource,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct ArgWriteFlow {
    pub(crate) dst_arg_index: usize,
    pub(crate) dst_path: Vec<SlotPathElem>,
    pub(crate) src: SummarySource,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct ArgWriteTarget {
    pub(crate) arg_index: usize,
    pub(crate) path: Vec<SlotPathElem>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum SummarySource {
    ParamSlot {
        arg_index: usize,
        path: Vec<SlotPathElem>,
    },
    Unknown(UnknownReason),
    OpaqueReturn,
    HeapAlloc,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct InstantiatedArgWrite {
    pub(crate) dst_arg_index: usize,
    pub(crate) destination: SlotIdx,
    pub(crate) sources: Vec<PfgNode>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct InstantiatedUnknownArgWrite {
    pub(crate) dst_arg_index: usize,
    pub(crate) destination: SlotIdx,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct CallEffects {
    pub(crate) complete: bool,
    pub(crate) writes: Vec<InstantiatedArgWrite>,
    pub(crate) unknown_writes: Vec<InstantiatedUnknownArgWrite>,
}
