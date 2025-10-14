use std::{fmt::Write as _, fs, path::Path};

use rustc_ast as ast;
use rustc_ast_pretty::pprust;

use crate::ast_util;

pub fn split(path: &Path) {
    let file = path.join("c2rust-lib.rs");
    let code = fs::read_to_string(&file).unwrap();
    let krate = ast_util::parse_crate(code);
    write_mod(path, None, &krate.attrs, &krate.items);
}

/// If `name` is `None`, this is the root module and we write `c2rust-lib.rs`
fn write_mod<I: AsRef<ast::Item>>(
    path: &Path,
    name: Option<&str>,
    attrs: &[ast::Attribute],
    items: &[I],
) {
    let dir = if let Some(name) = name {
        path.join(name)
    } else {
        path.to_path_buf()
    };
    let mut has_submodules = false;
    let mut code = String::new();
    for attr in attrs {
        if attr.style == ast::AttrStyle::Inner {
            writeln!(code, "{}", pprust::attribute_to_string(attr)).unwrap();
        }
    }
    for item in items {
        let item = item.as_ref();
        if let ast::ItemKind::Mod(safety, ident, kind) = &item.kind {
            assert_eq!(*safety, ast::Safety::Default);
            let ast::ModKind::Loaded(items, ast::Inline::Yes, _, Ok(())) = kind else { panic!() };
            has_submodules = true;
            if !dir.exists() {
                fs::create_dir(&dir).unwrap();
            }
            let name = ident.name.as_str();
            for attr in &item.attrs {
                if attr.style == ast::AttrStyle::Outer {
                    writeln!(code, "{}", pprust::attribute_to_string(attr)).unwrap();
                }
            }
            let raw = if ident.is_raw_guess() { "r#" } else { "" };
            writeln!(code, "pub mod {raw}{name};").unwrap();
            write_mod(&dir, Some(name), &item.attrs, items);
        } else {
            writeln!(code, "{}", pprust::item_to_string(item)).unwrap();
        }
    }
    let file = if let Some(name) = name {
        if has_submodules {
            dir.join("mod.rs")
        } else {
            path.join(format!("{name}.rs"))
        }
    } else {
        dir.join("c2rust-lib.rs")
    };
    fs::write(file, code).unwrap();
}
