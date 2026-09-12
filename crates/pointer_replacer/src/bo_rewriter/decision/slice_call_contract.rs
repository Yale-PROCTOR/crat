//! R349-1 pure call-carrier and reader-chain contract, deliberately unwired.
//!
//! The future production adapter maps compiler identities and settled forms to
//! these records. This module does not inspect HIR, classify fatness, emit an
//! edit, or alter class dependencies. Its result preserves the carrier's native
//! arm; `Hold` resumes the existing family refusal and class finalization.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum InterfaceForm {
    RefShared,
    RefMut,
    SliceShared,
    SliceMut,
    Other,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct SourceSpan {
    pub lo: u32,
    pub hi: u32,
}

impl SourceSpan {
    fn is_real(self) -> bool {
        self.lo < self.hi
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CallSite {
    pub owner: String,
    pub caller: String,
    pub callee: String,
    pub argument_index: usize,
    pub argument_span: SourceSpan,
    pub expected: InterfaceForm,
    pub found: InterfaceForm,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum GlueVerdict {
    NoEdit,
    Adapter,
    Blocked,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum CarrierKind {
    Edit,
    ZeroSyntax {
        bridge_kind: String,
        glue: GlueVerdict,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Carrier {
    pub site: CallSite,
    pub kind: CarrierKind,
    pub native_arm: String,
    pub dependency_registered: bool,
    pub held: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SelectedCarrier {
    pub kind: CarrierKind,
    pub native_arm: String,
    pub dependency_registered: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum CarrierHold {
    Missing,
    Ambiguous { candidates: usize },
    Held,
    Incompatible,
}

pub(crate) fn select_carrier(
    wanted: &CallSite,
    edits: &[Carrier],
    zero_syntax: &[Carrier],
) -> Result<SelectedCarrier, CarrierHold> {
    let matches: Vec<_> = edits
        .iter()
        .chain(zero_syntax)
        .filter(|carrier| carrier.site == *wanted)
        .collect();
    let [carrier] = matches.as_slice() else {
        return if matches.is_empty() {
            Err(CarrierHold::Missing)
        } else {
            Err(CarrierHold::Ambiguous {
                candidates: matches.len(),
            })
        };
    };
    if carrier.held {
        return Err(CarrierHold::Held);
    }
    let compatible = match &carrier.kind {
        CarrierKind::Edit => true,
        CarrierKind::ZeroSyntax { bridge_kind, glue } => {
            bridge_kind == "interface-call-zero-syntax"
                && carrier.site.argument_span.is_real()
                && *glue == GlueVerdict::NoEdit
                && forms_need_no_edit(carrier.site.expected, carrier.site.found)
                && (carrier.site.caller == carrier.site.callee || carrier.dependency_registered)
        }
    };
    if !compatible {
        return Err(CarrierHold::Incompatible);
    }
    Ok(SelectedCarrier {
        kind: carrier.kind.clone(),
        native_arm: carrier.native_arm.clone(),
        dependency_registered: carrier.dependency_registered,
    })
}

fn forms_need_no_edit(expected: InterfaceForm, found: InterfaceForm) -> bool {
    matches!(
        (expected, found),
        (
            InterfaceForm::RefShared,
            InterfaceForm::RefShared | InterfaceForm::RefMut
        ) | (InterfaceForm::RefMut, InterfaceForm::RefMut)
            | (
                InterfaceForm::SliceShared,
                InterfaceForm::SliceShared | InterfaceForm::SliceMut
            )
            | (InterfaceForm::SliceMut, InterfaceForm::SliceMut)
    )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ReaderForm {
    ThinRef,
    Slice,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ReaderHop {
    pub subject: String,
    pub form: ReaderForm,
    /// `Some(true)` is the existing whole-program `Arr` result.
    pub array: Option<bool>,
    /// True when this hop, or any callee reachable through it, indexes the
    /// pointer as an array. The production adapter derives this transitively.
    pub downstream_array_use: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ReaderHold {
    ReaderChainNarrowsRange {
        subject: String,
        needs_array_fact: bool,
    },
}

pub(crate) fn preserve_reader_chain(
    hops: &[ReaderHop],
) -> Result<Vec<(String, ReaderForm)>, ReaderHold> {
    let mut out = Vec::with_capacity(hops.len());
    for hop in hops {
        let form = if hop.downstream_array_use {
            match (hop.form, hop.array) {
                (ReaderForm::Slice, _) | (ReaderForm::ThinRef, Some(true)) => ReaderForm::Slice,
                (ReaderForm::ThinRef, None | Some(false)) => {
                    return Err(ReaderHold::ReaderChainNarrowsRange {
                        subject: hop.subject.clone(),
                        needs_array_fact: true,
                    });
                }
            }
        } else {
            hop.form
        };
        out.push((hop.subject.clone(), form));
    }
    Ok(out)
}
