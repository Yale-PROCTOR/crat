use std::path::PathBuf;

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

    // debug
    #[serde(default)]
    pub function_times: Option<usize>,
    #[serde(default)]
    pub print_functions: Vec<String>,
}

pub mod ai;
