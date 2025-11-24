#![feature(rustc_private)]
#![feature(array_windows)]
#![feature(box_patterns)]
#![feature(min_specialization)]
#![feature(allocator_api)]
#![warn(unused_extern_crates)]

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_const_eval;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
extern crate rustc_span;
extern crate rustc_type_ir;
extern crate smallvec;

mod analyses;
mod rewriter;
mod utils;

pub use rewriter::{Config, replace_local_borrows};
