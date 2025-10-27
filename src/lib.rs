#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(map_try_insert)]
#![warn(unused_extern_crates)]

extern crate rustc_abi;
extern crate rustc_const_eval;
extern crate rustc_data_structures;
extern crate rustc_hash;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
extern crate rustc_span;
extern crate rustc_type_ir;
extern crate rustc_ast;
extern crate rustc_ast_pretty;

use utils::{graph as graph_utils, ir as ir_utils};

pub mod outparam_replacer;
