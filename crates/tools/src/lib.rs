#![feature(rustc_private)]
#![feature(box_patterns)]

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_parse;
extern crate rustc_session;
extern crate rustc_span;
extern crate smallvec;
extern crate thin_vec;

mod item_replacer;
mod observation;
mod preservation;
mod printf;
mod rule;
mod skeleton;
mod validator;
mod view;

pub use item_replacer::*;
pub use observation::*;
pub use rule::*;
pub use skeleton::*;
pub use validator::*;
pub use view::*;
