//! Collection of relatively simple passes

#![feature(rustc_private)]
#![feature(box_patterns)]
#![warn(unused_extern_crates)]

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_literal_escaper;
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
extern crate rustc_span;
extern crate rustc_type_ir;
extern crate smallvec;
extern crate thin_vec;

pub mod bin_file_adder;
pub mod expander;
pub mod extern_resolver;
pub mod formatter;
pub mod interface_fixer;
pub mod libc_replacer;
pub mod preprocessor;
pub mod simplifier;
pub mod splitter;
pub mod unexpander;
pub mod unsafe_resolver;
