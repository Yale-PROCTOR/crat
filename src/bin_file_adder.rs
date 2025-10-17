use std::{
    fs::{self, File},
    io::Write as _,
    path::Path,
};

use rustc_hir as hir;
use rustc_hir::intravisit;
use rustc_middle::{hir::nested_filter, ty::TyCtxt};
use rustc_span::def_id::LocalDefId;
use serde::Deserialize;
use toml_edit::{DocumentMut, Table};

#[derive(Debug, Default, Deserialize)]
pub struct Config {
    #[serde(default)]
    pub ignores: Vec<String>,
    pub name: Option<String>,
}

pub fn add_bin_files(dir: &Path, config: &Config, tcx: TyCtxt<'_>) {
    let mut visitor = HirVisitor {
        tcx,
        data: HirData::default(),
    };
    tcx.hir_visit_all_item_likes_in_crate(&mut visitor);

    let path = dir.join("Cargo.toml");
    let content = fs::read_to_string(&path).unwrap();
    let mut doc = content.parse::<DocumentMut>().unwrap();
    let lib = doc["lib"].as_table().unwrap();
    let crate_name = lib["name"].as_str().unwrap().to_string();
    let bins = doc["bin"]
        .or_insert(toml_edit::array())
        .as_array_of_tables_mut()
        .unwrap();

    let mut names = vec![];
    for def_id in visitor.data.mains {
        let def_path_str = tcx.def_path_str(def_id);
        if config.ignores.iter().any(|s| def_path_str.starts_with(s)) {
            continue;
        }

        let bin_name = def_path_str.replace("::", "_").replace("r#", "");
        let filename = format!("{bin_name}.rs");
        let path = dir.join(&filename);
        let mut file = File::create_new(path).unwrap();
        write!(file, "fn main() {{ {crate_name}::{def_path_str}(); }}").unwrap();

        names.push((bin_name, filename));
    }

    for (bin_name, filename) in &names {
        let mut t = Table::new();
        let bin_name = if let Some(name) = &config.name
            && names.len() == 1
        {
            name
        } else {
            bin_name
        };
        t["name"] = toml_edit::value(bin_name);
        t["path"] = toml_edit::value(filename);
        bins.push(t);
    }

    fs::write(path, doc.to_string()).unwrap();
}

struct HirVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    data: HirData,
}

#[derive(Default)]
struct HirData {
    mains: Vec<LocalDefId>,
}

impl<'tcx> intravisit::Visitor<'tcx> for HirVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_item(&mut self, item: &'tcx hir::Item<'tcx>) -> Self::Result {
        if let hir::ItemKind::Fn { ident, .. } = item.kind
            && ident.name.as_str() == "main"
        {
            self.data.mains.push(item.owner_id.def_id);
        }

        intravisit::walk_item(self, item)
    }
}
