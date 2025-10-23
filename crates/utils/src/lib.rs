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
extern crate rustc_type_ir;
extern crate smallvec;
extern crate thin_vec;

pub mod ast;
pub mod bit_set;
pub mod compilation;
pub mod disjoint_set;
pub mod equiv_classes;
pub mod file;
pub mod graph;
pub mod ir;
pub mod ty_shape;
pub mod unsafety;

pub fn find_lib_path(dir: &std::path::Path) -> Result<String, String> {
    let cargo_file = dir.join("Cargo.toml");
    if !cargo_file.exists() {
        return Err(format!("{cargo_file:?} does not exist"));
    }
    let content = std::fs::read_to_string(&cargo_file).unwrap();
    let table = content.parse::<toml::Table>().unwrap();
    let Some(toml::Value::Table(lib)) = table.get(&"lib".to_string()) else {
        return Err(format!("No [lib] section in {cargo_file:?}"));
    };
    let Some(toml::Value::String(path)) = lib.get(&"path".to_string()) else {
        return Err(format!("No path in [lib] section in {cargo_file:?}"));
    };
    Ok(path.clone())
}
