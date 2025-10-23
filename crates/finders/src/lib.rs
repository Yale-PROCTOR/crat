#![feature(rustc_private)]
#![feature(box_patterns)]
#![warn(unused_extern_crates)]

extern crate rustc_ast;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_parse;
extern crate rustc_span;

pub mod example;
pub mod macro_finder;
pub mod mapper;
pub mod mir;
pub mod unsafe_finder;
