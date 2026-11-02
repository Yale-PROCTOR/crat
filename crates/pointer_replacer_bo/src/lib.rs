#![feature(rustc_private)]
#![feature(array_windows)]
#![feature(box_patterns)]
#![feature(min_specialization)]
#![feature(allocator_api)]
#![feature(step_trait)]
#![feature(trusted_step)]
#![feature(impl_trait_in_assoc_type)]
#![warn(unused_extern_crates)]

extern crate either;
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
