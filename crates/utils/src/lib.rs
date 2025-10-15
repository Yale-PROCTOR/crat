#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(if_let_guard)]
#![feature(iter_intersperse)]
#![warn(unused_extern_crates)]

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_feature;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_parse;
extern crate rustc_session;
extern crate rustc_span;
extern crate smallvec;
extern crate thin_vec;

pub mod ast;
pub mod bit_set;
pub mod compilation;
pub mod disjoint_set;
pub mod equiv_classes;
pub mod graph;
pub mod ir;
pub mod ty_shape;
pub mod unsafety;
