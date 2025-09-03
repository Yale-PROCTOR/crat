use std::path::{Path, PathBuf};

use etrace::some_or;
use rustc_hash::FxHashMap;
use rustc_hir::definitions::DefPathData;
use rustc_middle::ty::TyCtxt;
use rustc_span::{FileName, RealFileName};

use crate::{ast_util, ir_util, rustc_ast::visit::Visitor};

pub fn run(dir: &Path, tcx: TyCtxt<'_>) {
    let borrowed = tcx.resolver_for_lowering().borrow();
    let mut expanded_crate = borrowed.1.as_ref().clone();
    drop(borrowed);

    let mut path_to_mod_id = FxHashMap::default();
    tcx.hir_for_each_module(|mod_id| {
        let def_path = tcx.def_path(mod_id.to_def_id());
        let mut path = dir.to_path_buf();
        for data in def_path.data {
            let DefPathData::TypeNs(name) = data.data else { panic!() };
            path.push(name.as_str());
        }
        path.set_extension("rs");
        path_to_mod_id.insert(path, mod_id);
    });

    let source_map = tcx.sess.source_map();
    let parse_sess = ast_util::new_parse_sess();

    for file in source_map.files().iter() {
        let p = match &file.name {
            FileName::Real(RealFileName::LocalPath(p)) => p.clone(),
            FileName::Custom(p) => PathBuf::from(p),
            _ => continue,
        };
        let src = some_or!(file.src.as_ref(), continue);
        if p.file_name().unwrap().to_str().unwrap() == "c2rust-lib.rs" {
            continue;
        }
        let mut parser = rustc_parse::new_parser_from_source_str(
            &parse_sess,
            file.name.clone(),
            src.to_string(),
        )
        .unwrap();
        let mut krate = parser.parse_crate_mod().unwrap();
        let mod_id = path_to_mod_id[&p];
        let (module, _, _) = tcx.hir_get_module(mod_id);
        let mut mapper = ir_util::AstToHirMapper::new(tcx);
        mapper.map_crate_to_mod(&mut krate, module, false);
        let mut checker = ir_util::AstToHirChecker {
            tcx,
            ast_to_hir: mapper.ast_to_hir,
        };
        for item in &krate.items {
            checker.visit_item(item);
        }
    }

    let mut mapper = ir_util::AstToHirMapper::new(tcx);
    let module = tcx.hir_root_module();
    mapper.map_crate_to_mod(&mut expanded_crate, module, true);
    let mut checker = ir_util::AstToHirChecker {
        tcx,
        ast_to_hir: mapper.ast_to_hir,
    };
    for item in &expanded_crate.items {
        checker.visit_item(item);
    }

    let hir_to_thir = ir_util::map_hir_to_thir(tcx);
    let mut checker = ir_util::HirToThirChecker { tcx, hir_to_thir };
    tcx.hir_visit_all_item_likes_in_crate(&mut checker);

    ir_util::map_thir_to_mir(tcx);
}
