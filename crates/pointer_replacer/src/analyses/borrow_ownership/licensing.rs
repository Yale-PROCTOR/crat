//! Ownership licensing: regression witnesses precede the transport rules.

pub(crate) mod caller_coverage;
pub(crate) mod cell_effects;
pub(crate) mod chain_effects;
pub(crate) mod chain_entry;
pub(crate) mod chain_permission;
pub(crate) mod coverage;
pub(crate) mod facts;
pub(crate) mod field_support;
pub(crate) mod first_permission;
#[cfg(test)]
mod fold_activation_tests;
pub(crate) mod fold_call;
pub(crate) mod fold_caller;
#[cfg(test)]
mod fold_caller_tests;
#[cfg(test)]
mod fold_chain_tests;
#[cfg(test)]
mod fold_control_flow_tests;
pub(crate) mod fold_coverage;
pub(crate) mod fold_custody;
#[cfg(test)]
mod fold_custody_tests;
pub(crate) mod fold_declaration;
pub(crate) mod fold_eligibility;
#[cfg(test)]
mod fold_eligibility_tests;
pub(crate) mod fold_internal;
pub(crate) mod fold_laws;
pub(crate) mod fold_member_caller;
#[cfg(test)]
mod fold_member_caller_tests;
pub(crate) mod fold_member_laws;
#[cfg(test)]
mod fold_member_laws_tests;
pub(crate) mod fold_member_output;
#[cfg(test)]
mod fold_member_output_tests;
pub(crate) mod fold_permission;
#[cfg(test)]
mod fold_recursion_tests;
#[cfg(test)]
mod fold_selection_tests;
pub(crate) mod fold_subtree;
#[cfg(test)]
mod fold_subtree_tests;
#[cfg(test)]
mod fold_tests;
pub(crate) mod fold_types;
#[cfg(test)]
mod fold_views_tests;
pub(crate) mod fold_zero;
pub(crate) mod grants;
pub(crate) mod matched;
pub(crate) mod model_selection;
pub(crate) mod read_b;
pub(crate) mod reader_replay;
pub(crate) mod readers;
pub(crate) mod recursive;
pub(crate) mod ref_effects;
pub(crate) mod snapshot;
pub(crate) mod stack_entry;
pub(crate) mod stack_export;
pub(crate) mod transport;
#[cfg(test)]
mod traversal_activation;
pub(crate) mod traversal_call;
pub(crate) mod traversal_correspondence;
pub(crate) mod traversal_discharge;
pub(crate) mod traversal_native;
#[cfg(test)]
pub(crate) mod traversal_projected;
pub(crate) mod traversal_replay;
pub(crate) mod traversal_return;
pub(crate) mod value_origins;

#[cfg(test)]
mod value_origin_tests;

#[cfg(test)]
mod objective_tests;

#[cfg(test)]
mod objective_grant_tests;

#[cfg(test)]
mod recursive_tests;

#[cfg(test)]
mod serialization_tests;

#[cfg(test)]
mod matched_tests;

#[cfg(test)]
mod aggregate_tests;

#[cfg(test)]
pub(crate) mod graph_tests;

#[cfg(test)]
mod gate_tests;

#[cfg(test)]
mod reader_tests;

#[cfg(test)]
mod ref_support_tests;

#[cfg(test)]
mod cell_effect_tests;

#[cfg(test)]
mod input_store_tests;

#[cfg(test)]
mod input_support_tests;

#[cfg(test)]
mod return_forward_tests;

#[cfg(test)]
mod exit_tests;

#[cfg(test)]
mod transport_tests;

#[cfg(test)]
mod tests;
#[cfg(test)]
mod witnesses;

#[cfg(test)]
mod occurrence_capture;

#[cfg(test)]
mod call_tests;

#[cfg(test)]
mod export_differential;

#[cfg(test)]
mod export_tests;
