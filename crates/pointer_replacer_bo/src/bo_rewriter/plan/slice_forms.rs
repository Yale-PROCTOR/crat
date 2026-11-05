//! Plan the index declaration with the same owner and dependencies as its uses.

use rustc_span::Span;

use super::{
    super::{
        bridge_receipt::{BridgeSitePlan, SignatureClassId},
        decision::{Arm, DecisionTable, Subject},
    },
    Edit, FileKey, Justification,
};

pub(super) fn append(
    table: &DecisionTable,
    subject: &Subject,
    ty_file: &FileKey,
    span_to_loc: &impl Fn(Span) -> Result<(FileKey, usize, usize), &'static str>,
    owner_path: &str,
    subject_id: &str,
    subject_atom_ids: &[String],
    subject_arms: &str,
    use_edits: &mut Vec<Edit>,
    use_failure: &mut Option<&'static str>,
) {
    if let Some(parameter) = table
        .forward_slice_parameters
        .iter()
        .find(|parameter| parameter.node == (subject.fn_did, subject.hir_id))
    {
        let insertion = parameter
            .body_span
            .with_lo(parameter.body_span.lo() + rustc_span::BytePos(1))
            .shrink_to_lo();
        match span_to_loc(insertion) {
            Ok((file, lo, hi)) if &file == ty_file => use_edits.push(Edit {
                lo,
                hi,
                replacement: format!("\nlet mut {}: usize = 0;\n", parameter.index_name),
                justification: Justification::StoreForm {
                    form: "forward-slice-index",
                },
                owner_class: Some(SignatureClassId::of(subject.fn_did)),
                owner_path: owner_path.to_owned(),
                bridge: Some(BridgeSitePlan::local(
                    subject.fn_did,
                    subject.fn_did,
                    Arm::Surface.key(),
                    subject_id.to_owned(),
                    "forward-slice-index",
                )),
                atom_ids: subject_atom_ids.to_vec(),
                subject_id: subject_id.to_owned(),
                required_arms: subject_arms.to_owned(),
                edit_kind: "forward-slice-index",
            }),
            Ok(_) => *use_failure = Some("forward index is in a different file from its parameter"),
            Err(reason) => *use_failure = Some(reason),
        }
    }
}
