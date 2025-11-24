#![feature(rustc_private)]
#![feature(box_patterns)]
#![warn(unused_extern_crates)]

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_data_structures;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_middle;
extern crate rustc_span;
extern crate smallvec;

mod error_analysis;
mod file_analysis;
mod likely_lit;
mod mir_loc;
mod transformation;

pub use transformation::transform::{add_deps, replace_io};

#[cfg(test)]
mod tests;
