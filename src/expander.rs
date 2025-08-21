use std::sync::Arc;

use rustc_ast::{
    AttrKind,
    mut_visit::{self, MutVisitor},
};
use rustc_ast_pretty::pprust;
use rustc_middle::ty::TyCtxt;

pub fn expand(tcx: TyCtxt<'_>) -> String {
    let (_, mut krate) = tcx.resolver_for_lowering().steal();
    let mut visitor = AstVisitor;
    let krate = Arc::get_mut(&mut krate).unwrap();
    visitor.visit_crate(krate);
    let s = pprust::crate_to_string_for_macros(krate);
    s.replace(
        "#[prelude_import]\nuse std::prelude::rust_2021::*;",
        "
#![feature(derive_clone_copy)]
#![feature(panic_internals)]
#![feature(hint_must_use)]",
    )
    .replace("#[macro_use]\nextern crate c2rust_asm_casts;", "")
    .replace("#[macro_use]\nextern crate std;", "")
    .replace("extern crate libc;", "")
    .replace("::alloc::__export::must_use", "std::hint::must_use")
    .replace("::alloc::fmt::format", "std::fmt::format")
}

struct AstVisitor;

impl MutVisitor for AstVisitor {
    fn visit_field_def(&mut self, fd: &mut rustc_ast::FieldDef) {
        fd.attrs.retain(|attr| {
            let AttrKind::Normal(attr) = &attr.kind else { return true };
            let seg = attr.item.path.segments.last().unwrap();
            seg.ident.name.as_str() != "bitfield"
        });
        mut_visit::walk_field_def(self, fd);
    }
}
