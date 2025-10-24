#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(iter_intersperse)]
#![warn(unused_extern_crates)]

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_data_structures;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
extern crate rustc_span;
extern crate smallvec;
extern crate thin_vec;

mod must_analysis;
pub mod tag_analysis;
mod ty_finder;
mod util;

pub use tag_analysis::Config;
