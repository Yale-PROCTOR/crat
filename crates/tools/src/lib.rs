#![feature(rustc_private)]
#![feature(box_patterns)]

extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;
extern crate smallvec;
extern crate thin_vec;

mod item_replacer;
mod skeleton;
mod validator;

pub use item_replacer::*;
pub use skeleton::*;
pub use validator::*;
