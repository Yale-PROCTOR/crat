#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(if_let_guard)]
#![feature(iter_intersperse)]
#![feature(map_try_insert)]
#![warn(unused_extern_crates)]

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_ast_pretty;
extern crate rustc_const_eval;
extern crate rustc_data_structures;
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

use utils::{ast as ast_utils, graph as graph_utils, ir as ir_utils};

pub mod bin_file_adder;
pub mod expander;
pub mod extern_resolver;
pub mod formatter;
pub mod io_replacer;
pub mod libc_replacer;
pub mod outparam_replacer;
pub mod preprocessor;
pub mod splitter;
pub mod type_checker;
pub mod unexpander;
pub mod union_replacer;
pub mod unsafe_resolver;
