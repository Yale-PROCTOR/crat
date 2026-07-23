#![feature(rustc_private)]
#![feature(box_patterns)]

extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;
extern crate smallvec;

mod skeleton;
mod validator;

pub use skeleton::*;
pub use validator::*;
