#![feature(rustc_private)]
#![feature(box_patterns)]
#![warn(unused_extern_crates)]

extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_middle;

mod transformation;

pub use transformation::replace_static;
