use rustc_ast::visit::{self, Visitor};
use rustc_hash::FxHashSet;
use rustc_middle::ty::TyCtxt;

use crate::ast_utils;

pub fn find_macros(tcx: TyCtxt<'_>) {
    let mut finder = MacroFinder::default();
    ast_utils::foreach_crate(
        |krate| {
            finder.visit_crate(&krate);
        },
        tcx,
    );
    for mac in finder.macros {
        println!("{mac}");
    }
}

#[derive(Default)]
struct MacroFinder {
    macros: FxHashSet<String>,
}

impl Visitor<'_> for MacroFinder {
    fn visit_mac_call(&mut self, mac: &rustc_ast::MacCall) {
        let mut s = String::new();
        for seg in &mac.path.segments {
            if !s.is_empty() {
                s += "::";
            }
            s += seg.ident.name.as_str();
        }
        self.macros.insert(s);
        visit::walk_mac(self, mac);
    }
}
