#![feature(rustc_private)]
#![feature(box_patterns)]
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
extern crate rustc_literal_escaper;
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

pub fn type_check(tcx: rustc_middle::ty::TyCtxt<'_>) {
    let () = tcx.analysis(());
}

pub fn format(code: &str) -> String {
    compilation::run_compiler_on_str(code, |tcx| {
        let r = tcx.crate_for_resolver(()).borrow();
        let (ref krate, _) = *r;
        rustc_ast_pretty::pprust::crate_to_string_for_macros(krate)
    })
    .unwrap()
}

#[inline]
pub fn unescape_byte_str(s: &str) -> Vec<u8> {
    // from rustc_ast/src/util/literal.rs
    let mut buf = Vec::with_capacity(s.len());
    rustc_literal_escaper::unescape_unicode(
        s,
        rustc_literal_escaper::Mode::ByteStr,
        &mut |_, c| buf.push(rustc_literal_escaper::byte_from_char(c.unwrap())),
    );
    buf
}

pub fn format_rust_str_from_bytes<W: std::fmt::Write>(
    mut format: W,
    bytes: &[u8],
) -> std::fmt::Result {
    for c in String::from_utf8_lossy(bytes).chars() {
        match c {
            '{' => write!(format, "{{")?,
            '}' => write!(format, "}}")?,
            '\n' => write!(format, "\\n")?,
            '\r' => write!(format, "\\r")?,
            '\t' => write!(format, "\\t")?,
            '\\' => write!(format, "\\\\")?,
            '\0' => {}
            '\"' => write!(format, "\\\"")?,
            _ => {
                if c.is_ascii_alphanumeric() || c.is_ascii_graphic() || c == ' ' {
                    write!(format, "{c}")?;
                } else {
                    write!(format, "\\u{{{:x}}}", c as u32)?;
                }
            }
        }
    }
    Ok(())
}

pub fn escape(c: u8) -> Option<&'static str> {
    match c {
        b'\n' => Some("\\n"),
        b'\r' => Some("\\r"),
        b'\t' => Some("\\t"),
        b'\\' => Some("\\\\"),
        b'\'' => Some("\\'"),
        b'\"' => Some("\\\""),
        b'\0' => Some("\\0"),
        _ => None,
    }
}
