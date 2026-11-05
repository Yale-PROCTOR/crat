#![feature(rustc_private)]
#![feature(array_windows)]
#![feature(box_patterns)]
#![feature(min_specialization)]
#![feature(allocator_api)]
#![feature(step_trait)]
#![feature(trusted_step)]
#![feature(impl_trait_in_assoc_type)]
#![warn(unused_extern_crates)]
// The master CI runs `cargo clippy -- -D warnings`. These lints are structural or stylistic over a
// large analysis crate (argument counts, nested tuple types, doc continuation, boolean shapes, index
// loops, ...); they are allowed here, not rewritten, at the merge. `private_interfaces` /
// `private_bounds`: crate-internal types in `pub(crate)` signatures of public-module items.
#![allow(
    private_interfaces,
    private_bounds,
    clippy::too_many_arguments,
    clippy::type_complexity,
    clippy::doc_lazy_continuation,
    clippy::nonminimal_bool,
    clippy::needless_range_loop,
    clippy::field_reassign_with_default,
    clippy::collapsible_match,
    clippy::collapsible_if,
    clippy::large_enum_variant,
    clippy::result_large_err,
    clippy::if_same_then_else,
    clippy::while_let_loop,
    clippy::redundant_guards,
    clippy::empty_line_after_doc_comments,
    clippy::only_used_in_recursion,
    clippy::question_mark,
    clippy::needless_borrows_for_generic_args,
    clippy::enum_variant_names,
    clippy::useless_conversion,
    clippy::iter_skip_zero,
    clippy::cloned_ref_to_slice_refs,
    clippy::single_range_in_vec_init,
    clippy::filter_map_bool_then,
    clippy::drop_non_drop,
    clippy::wrong_self_convention,
    clippy::unnecessary_get_then_check,
    clippy::match_like_matches_macro,
    clippy::unnecessary_filter_map,
    clippy::redundant_locals,
    clippy::uninlined_format_args,
    clippy::redundant_closure
)]

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
extern crate rustc_parse;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_target;
extern crate rustc_type_ir;
extern crate smallvec;
extern crate thin_vec;

// The analyses this crate owns: BO's own (`borrow_ownership`, which also holds the two parts of
// the legacy analyses BO runs differently: `borrow_fork` and `mutability`). Every other
// `crate::analyses::…` path resolves to the legacy crate's module through the glob.
pub mod analyses {
    pub mod bo_adapter;
    pub mod borrow_ownership;
    pub use pointer_replacer::analyses::*;
}
mod analysis_budget;
mod bo_pipeline;
mod bo_rewriter;
#[cfg(test)]
mod coverage_recon;
mod phase_log;
mod raw_boundary_census_schema;
pub use bo_pipeline::{BoReceipt, Config, query_timeout_env_value, rewrite_bo};
pub use pointer_replacer::{rewriter, utils};

#[cfg(test)]
mod r1312_fixtures;
#[cfg(test)]
mod r1314_p12_tests;
#[cfg(test)]
mod tests;
