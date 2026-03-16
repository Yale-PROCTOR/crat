#![feature(rustc_private)]
#![feature(box_patterns)]
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
extern crate rustc_middle;
extern crate rustc_mir_dataflow;
extern crate rustc_span;
extern crate rustc_type_ir;

use std::path::PathBuf;

use rustc_hash::FxHashSet;
use serde::Deserialize;

fn default_max_loop_head_states() -> usize {
    usize::MAX
}

#[derive(Debug, Default, Deserialize)]
pub struct Config {
    // analysis
    #[serde(default = "default_max_loop_head_states")]
    pub max_loop_head_states: usize,
    #[serde(default)]
    pub check_global_alias: bool,
    #[serde(default)]
    pub check_param_alias: bool,
    #[serde(default)]
    pub no_widening: bool,
    #[serde(default)]
    pub points_to_file: Option<PathBuf>,

    // transformation
    #[serde(default)]
    pub simplify: bool,
    #[serde(default)]
    pub analysis_file: Option<PathBuf>,
    #[serde(default)]
    pub c_exposed_fns: FxHashSet<String>,
    #[serde(default)]
    pub transformed_fns_file: Option<PathBuf>,

    // debug
    #[serde(default)]
    pub function_times: Option<usize>,
    #[serde(default)]
    pub print_functions: Vec<String>,
}

pub mod ai;
pub mod transform;
