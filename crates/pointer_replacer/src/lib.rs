#![feature(rustc_private)]
#![feature(array_windows)]
#![feature(box_patterns)]
#![feature(min_specialization)]
#![feature(allocator_api)]

extern crate rustc_abi;
extern crate rustc_data_structures;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
extern crate rustc_span;
extern crate rustc_type_ir;

mod analyses;
mod utils;

use analyses::*;
use rustc_hir::{ItemKind, OwnerNode};
use rustc_middle::ty::TyCtxt;
use utils::rustc::RustProgram;

pub fn replace_local_borrows(tcx: TyCtxt<'_>) {
    let mut functions = vec![];
    let mut structs = vec![];

    for maybe_owner in tcx.hir_crate(()).owners.iter() {
        let Some(owner) = maybe_owner.as_owner() else {
            continue;
        };
        let OwnerNode::Item(item) = owner.node() else {
            continue;
        };
        match item.kind {
            ItemKind::Fn { .. } => functions.push(item.owner_id.def_id.to_def_id()),
            ItemKind::Struct(..) => structs.push(item.owner_id.def_id.to_def_id()),
            _ => {}
        };
    }

    let input = RustProgram {
        tcx,
        functions,
        structs,
    };

    let mutability_result = type_qualifier::foster::mutability::mutability_analysis(&input);
    let output_params = output_params::compute_output_params(&input, &mutability_result);
    let source_var_groups = mir_variable_grouping::SourceVarGroups::new(&input);
    let promoted_mut_refs = source_var_groups.postprocess_promoted_mut_refs(
        borrow::mutable_references_no_guarantee(&input),
    );
}
