#![feature(rustc_private)]

extern crate rustc_ast;
extern crate rustc_ast_pretty;

mod cofactor;

use std::{
    collections::{BTreeMap, BTreeSet},
    ffi::{OsStr, OsString},
    fmt::Write as _,
    fs,
    path::{Path, PathBuf},
};

use rustc_ast::{AttrStyle, ItemKind};
use rustc_ast_pretty::pprust;
use serde::Deserialize;
use serde_json::Value;
use toml_edit::{Array, DocumentMut, Item, Table, value};

use crate::cofactor::{Expr, Solver, Universe};

#[derive(Deserialize)]
struct RawTranslation {
    dir: PathBuf,
    #[serde(flatten)]
    config: BTreeMap<String, Value>,
}

struct Translation {
    dir: PathBuf,
    config: BTreeMap<String, String>,
    features: Vec<String>,
}

struct SharedFile {
    name: &'static str,
    contents: Vec<u8>,
}

struct ParsedRustFile {
    inner_attrs: Vec<String>,
    items: Vec<ParsedItem>,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum ItemBucket {
    Use,
    ExternCrate,
    ForeignMod,
    Mod,
    Other,
    Global,
    Type,
    Trait,
    Impl,
    Fn,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ParsedItem {
    text: String,
    bucket: ItemBucket,
    group_name: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct OrderedItem {
    text: String,
    bucket: ItemBucket,
    group_name: Option<String>,
    first_seen: usize,
}

pub fn merge(translations_json: &Path, output_root: &Path) -> Result<(), String> {
    let translations = load_translations(translations_json)?;
    let common_dir_name = common_dir_name(&translations)?;

    if output_root.exists() && !output_root.is_dir() {
        return Err(format!("{output_root:?} is not a directory"));
    }
    fs::create_dir_all(output_root)
        .map_err(|e| format!("failed to create {output_root:?}: {e}"))?;

    let output_dir = output_root.join(&common_dir_name);
    if output_dir.exists() && !output_dir.is_dir() {
        return Err(format!("{output_dir:?} is not a directory"));
    }
    fs::create_dir_all(&output_dir).map_err(|e| format!("failed to create {output_dir:?}: {e}"))?;
    clean_output_dir(&output_dir)?;

    let cargo_toml = shared_required_file(&translations, "Cargo.toml")?;
    let build_rs = shared_optional_file(&translations, "build.rs")?;
    let toolchain = shared_toolchain_file(&translations)?;

    write_shared_file(&output_dir, &cargo_toml)?;
    add_features_to_cargo_toml(&output_dir.join("Cargo.toml"), feature_union(&translations))?;
    if let Some(file) = build_rs.as_ref() {
        write_shared_file(&output_dir, file)?;
    }
    if let Some(file) = toolchain.as_ref() {
        write_shared_file(&output_dir, file)?;
    }

    for (relative_path, variants) in collect_source_files(&translations)? {
        write_merged_rust_file(&output_dir.join(relative_path), &translations, &variants)?;
    }

    Ok(())
}

fn load_translations(translations_json: &Path) -> Result<Vec<Translation>, String> {
    let content = fs::read_to_string(translations_json)
        .map_err(|e| format!("failed to read {translations_json:?}: {e}"))?;
    let raw: Vec<RawTranslation> = serde_json::from_str(&content)
        .map_err(|e| format!("failed to parse {translations_json:?}: {e}"))?;
    if raw.is_empty() {
        return Err(format!(
            "{translations_json:?} does not contain any translations"
        ));
    }

    let base_dir = translations_json.parent().unwrap_or_else(|| Path::new("."));
    let expected_keys: BTreeSet<String> = raw[0].config.keys().cloned().collect();
    let varying_params = varying_params(&raw, &expected_keys)?;
    let mut feature_map = BTreeMap::<String, (String, String)>::new();
    let mut seen_configs = BTreeSet::<BTreeMap<String, String>>::new();
    let mut translations = Vec::with_capacity(raw.len());

    for (index, entry) in raw.into_iter().enumerate() {
        let keys: BTreeSet<String> = entry.config.keys().cloned().collect();
        if keys != expected_keys {
            return Err(format!(
                "translation {} has different configuration parameters",
                index + 1
            ));
        }

        let dir = resolve_dir(base_dir, &entry.dir);
        if !dir.is_dir() {
            return Err(format!("{dir:?} is not a directory"));
        }

        let mut config = BTreeMap::new();
        let mut features = Vec::with_capacity(varying_params.len());
        for (param, value) in entry.config {
            let raw_value = config_value_to_string(&param, &value)?;
            if varying_params.contains(&param) {
                let feature = make_feature_name(&param, &raw_value)?;
                if let Some((existing_param, existing_value)) = feature_map.get(&feature) {
                    if existing_param != &param || existing_value != &raw_value {
                        return Err(format!(
                            "feature name collision: {feature:?} maps to both {existing_param}={existing_value} and {param}={raw_value}"
                        ));
                    }
                } else {
                    feature_map.insert(feature.clone(), (param.clone(), raw_value.clone()));
                }
                features.push(feature);
            }
            config.insert(param.clone(), raw_value);
        }
        if !seen_configs.insert(config.clone()) {
            return Err(format!(
                "duplicate configuration detected for translation directory {dir:?}"
            ));
        }
        translations.push(Translation {
            dir,
            config,
            features,
        });
    }

    Ok(translations)
}

fn varying_params(
    raw: &[RawTranslation],
    expected_keys: &BTreeSet<String>,
) -> Result<BTreeSet<String>, String> {
    let mut value_sets = expected_keys
        .iter()
        .cloned()
        .map(|param| (param, BTreeSet::new()))
        .collect::<BTreeMap<_, _>>();

    for entry in raw {
        for param in expected_keys {
            let value = entry
                .config
                .get(param)
                .ok_or_else(|| format!("missing configuration parameter {param:?}"))?;
            let value = config_value_to_string(param, value)?;
            value_sets
                .get_mut(param)
                .expect("expected key was pre-populated")
                .insert(value);
        }
    }

    Ok(value_sets
        .into_iter()
        .filter_map(|(param, values)| (values.len() > 1).then_some(param))
        .collect())
}

fn resolve_dir(base_dir: &Path, dir: &Path) -> PathBuf {
    if dir.is_absolute() {
        dir.to_path_buf()
    } else {
        base_dir.join(dir)
    }
}

fn config_value_to_string(param: &str, value: &Value) -> Result<String, String> {
    match value {
        Value::String(s) => Ok(s.clone()),
        Value::Bool(b) => Ok(b.to_string()),
        Value::Number(n) => Ok(n.to_string()),
        _ => Err(format!(
            "configuration value for {param:?} must be a string, number, or boolean"
        )),
    }
}

fn make_feature_name(param: &str, value: &str) -> Result<String, String> {
    let param = normalize_feature_component(param)?;
    let value = normalize_feature_component(value)?;
    Ok(format!("{param}_{value}"))
}

fn normalize_feature_component(component: &str) -> Result<String, String> {
    let mut normalized = String::new();
    let mut previous_underscore = false;
    for ch in component.chars() {
        let ch = ch.to_ascii_lowercase();
        if ch.is_ascii_alphanumeric() {
            normalized.push(ch);
            previous_underscore = false;
        } else if ch == '_' && !previous_underscore {
            normalized.push(ch);
            previous_underscore = true;
        } else if !previous_underscore && !normalized.is_empty() {
            normalized.push('_');
            previous_underscore = true;
        }
    }
    while normalized.ends_with('_') {
        normalized.pop();
    }
    if normalized.is_empty() {
        return Err(format!(
            "cannot derive a cargo feature component from {component:?}"
        ));
    }
    Ok(normalized)
}

fn common_dir_name(translations: &[Translation]) -> Result<OsString, String> {
    let first_name = translations[0]
        .dir
        .file_name()
        .ok_or_else(|| format!("{:?} does not have a directory name", translations[0].dir))?
        .to_os_string();
    for translation in &translations[1..] {
        let name = translation
            .dir
            .file_name()
            .ok_or_else(|| format!("{:?} does not have a directory name", translation.dir))?;
        if name != first_name {
            return Err("translation directories must share the same final component".to_string());
        }
    }
    Ok(first_name)
}

fn shared_required_file(
    translations: &[Translation],
    name: &'static str,
) -> Result<SharedFile, String> {
    let first_path = translations[0].dir.join(name);
    let first_contents =
        fs::read(&first_path).map_err(|e| format!("failed to read {first_path:?}: {e}"))?;
    for translation in &translations[1..] {
        let path = translation.dir.join(name);
        let contents = fs::read(&path).map_err(|e| format!("failed to read {path:?}: {e}"))?;
        if contents != first_contents {
            return Err(format!("{name} differs across translation directories"));
        }
    }
    Ok(SharedFile {
        name,
        contents: first_contents,
    })
}

fn shared_optional_file(
    translations: &[Translation],
    name: &'static str,
) -> Result<Option<SharedFile>, String> {
    let first_path = translations[0].dir.join(name);
    let first_contents = if first_path.exists() {
        Some(fs::read(&first_path).map_err(|e| format!("failed to read {first_path:?}: {e}"))?)
    } else {
        None
    };

    for translation in &translations[1..] {
        let path = translation.dir.join(name);
        let contents = if path.exists() {
            Some(fs::read(&path).map_err(|e| format!("failed to read {path:?}: {e}"))?)
        } else {
            None
        };
        if contents != first_contents {
            return Err(format!("{name} differs across translation directories"));
        }
    }

    Ok(first_contents.map(|contents| SharedFile { name, contents }))
}

fn shared_toolchain_file(translations: &[Translation]) -> Result<Option<SharedFile>, String> {
    let first = detect_toolchain_file(&translations[0].dir)?;
    for translation in &translations[1..] {
        let candidate = detect_toolchain_file(&translation.dir)?;
        match (&first, &candidate) {
            (None, None) => {}
            (Some(lhs), Some(rhs)) if lhs.name == rhs.name && lhs.contents == rhs.contents => {}
            _ => return Err("toolchain file differs across translation directories".to_string()),
        }
    }
    Ok(first)
}

fn detect_toolchain_file(dir: &Path) -> Result<Option<SharedFile>, String> {
    let mut matches = Vec::new();
    for name in ["rust-toolchain", "rust-toolchain.toml"] {
        let path = dir.join(name);
        if path.exists() {
            let contents = fs::read(&path).map_err(|e| format!("failed to read {path:?}: {e}"))?;
            matches.push(SharedFile { name, contents });
        }
    }
    match matches.len() {
        0 => Ok(None),
        1 => Ok(matches.pop()),
        _ => Err(format!(
            "{dir:?} contains both rust-toolchain and rust-toolchain.toml"
        )),
    }
}

fn write_shared_file(output_dir: &Path, file: &SharedFile) -> Result<(), String> {
    let path = output_dir.join(file.name);
    fs::write(&path, &file.contents).map_err(|e| format!("failed to write {path:?}: {e}"))
}

fn feature_union(translations: &[Translation]) -> Vec<String> {
    let mut features = BTreeSet::new();
    for translation in translations {
        features.extend(translation.features.iter().cloned());
    }
    features.into_iter().collect()
}

fn add_features_to_cargo_toml(cargo_toml: &Path, features: Vec<String>) -> Result<(), String> {
    let content = fs::read_to_string(cargo_toml)
        .map_err(|e| format!("failed to read {cargo_toml:?}: {e}"))?;
    let mut doc = content
        .parse::<DocumentMut>()
        .map_err(|e| format!("failed to parse {cargo_toml:?}: {e}"))?;

    if !doc.contains_key("features") {
        doc.insert("features", Item::Table(Table::new()));
    }
    let feature_table = doc
        .get_mut("features")
        .and_then(Item::as_table_mut)
        .ok_or_else(|| format!("{cargo_toml:?} has a non-table [features] entry"))?;

    for feature in features {
        if !feature_table.contains_key(&feature) {
            feature_table[&feature] = value(Array::default());
        }
    }

    fs::write(cargo_toml, doc.to_string())
        .map_err(|e| format!("failed to write {cargo_toml:?}: {e}"))
}

fn clean_output_dir(dir: &Path) -> Result<(), String> {
    remove_named_file(dir.join("Cargo.toml"))?;
    remove_named_file(dir.join("Cargo.lock"))?;
    remove_named_file(dir.join("rust-toolchain"))?;
    remove_named_file(dir.join("rust-toolchain.toml"))?;
    remove_rs_files(dir)?;
    Ok(())
}

fn remove_named_file(path: PathBuf) -> Result<(), String> {
    if path.exists() {
        fs::remove_file(&path).map_err(|e| format!("failed to remove {path:?}: {e}"))?;
    }
    Ok(())
}

fn remove_rs_files(dir: &Path) -> Result<(), String> {
    let mut entries = read_dir_sorted(dir)?;
    for entry in entries.drain(..) {
        let path = entry.path();
        let name = entry.file_name();
        if path.is_dir() {
            if name == OsStr::new("target") {
                continue;
            }
            remove_rs_files(&path)?;
            if fs::read_dir(&path)
                .map_err(|e| format!("failed to read {path:?}: {e}"))?
                .next()
                .is_none()
            {
                fs::remove_dir(&path).map_err(|e| format!("failed to remove {path:?}: {e}"))?;
            }
        } else if path.extension() == Some(OsStr::new("rs")) {
            fs::remove_file(&path).map_err(|e| format!("failed to remove {path:?}: {e}"))?;
        }
    }
    Ok(())
}

fn collect_source_files(
    translations: &[Translation],
) -> Result<BTreeMap<PathBuf, Vec<(usize, PathBuf)>>, String> {
    let mut grouped = BTreeMap::<PathBuf, Vec<(usize, PathBuf)>>::new();
    for (index, translation) in translations.iter().enumerate() {
        let mut files = Vec::new();
        collect_rs_files(&translation.dir, &translation.dir, &mut files)?;
        for relative_path in files {
            grouped
                .entry(relative_path.clone())
                .or_default()
                .push((index, translation.dir.join(relative_path)));
        }
    }
    Ok(grouped)
}

fn collect_rs_files(dir: &Path, root: &Path, files: &mut Vec<PathBuf>) -> Result<(), String> {
    for entry in read_dir_sorted(dir)? {
        let path = entry.path();
        let name = entry.file_name();
        if path.is_dir() {
            if name == OsStr::new("target") {
                continue;
            }
            collect_rs_files(&path, root, files)?;
        } else if path.extension() == Some(OsStr::new("rs")) && name != OsStr::new("build.rs") {
            let relative = path
                .strip_prefix(root)
                .map_err(|e| format!("failed to compute relative path for {path:?}: {e}"))?;
            files.push(relative.to_path_buf());
        }
    }
    Ok(())
}

fn read_dir_sorted(dir: &Path) -> Result<Vec<fs::DirEntry>, String> {
    let mut entries = fs::read_dir(dir)
        .map_err(|e| format!("failed to read {dir:?}: {e}"))?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|e| format!("failed to read {dir:?}: {e}"))?;
    entries.sort_by_key(|entry| entry.path());
    Ok(entries)
}

fn write_merged_rust_file(
    output_path: &Path,
    translations: &[Translation],
    variants: &[(usize, PathBuf)],
) -> Result<(), String> {
    let mut shared_inner_attrs: Option<Vec<String>> = None;
    let mut ordered_items = Vec::new();
    let mut item_variants = BTreeMap::<String, BTreeSet<usize>>::new();
    let mut merged = String::new();
    let mut next_first_seen = 0usize;

    for (variant_index, (_, path)) in variants.iter().enumerate() {
        let parsed = parse_rust_file(path)?;
        if let Some(existing) = shared_inner_attrs.as_ref() {
            if existing != &parsed.inner_attrs {
                return Err(format!(
                    "inner attributes differ for merged file {output_path:?}"
                ));
            }
        } else {
            shared_inner_attrs = Some(parsed.inner_attrs.clone());
        }

        let mut seen_in_variant = BTreeSet::new();
        for item in parsed.items {
            if !seen_in_variant.insert(item.text.clone()) {
                continue;
            }

            let variants_for_item = item_variants.entry(item.text.clone()).or_default();
            if variants_for_item.is_empty() {
                ordered_items.push(OrderedItem {
                    text: item.text.clone(),
                    bucket: item.bucket,
                    group_name: item.group_name,
                    first_seen: next_first_seen,
                });
                next_first_seen += 1;
            }
            variants_for_item.insert(variant_index);
        }
    }

    for item in reorder_items(ordered_items) {
        if let Some(cfg) = merged_cfg_attribute(&item.text, &item_variants, translations, variants)
        {
            writeln!(merged, "{cfg}").unwrap();
            writeln!(merged, "{}", item.text).unwrap();
        } else {
            writeln!(merged, "{}", item.text).unwrap();
        }
    }

    let mut code = String::new();
    if let Some(inner_attrs) = shared_inner_attrs {
        for attr in inner_attrs {
            writeln!(code, "{attr}").unwrap();
        }
        if !code.is_empty() && !merged.is_empty() {
            code.push('\n');
        }
    }
    code.push_str(&merged);

    if let Some(parent) = output_path.parent() {
        fs::create_dir_all(parent).map_err(|e| format!("failed to create {parent:?}: {e}"))?;
    }
    fs::write(output_path, code).map_err(|e| format!("failed to write {output_path:?}: {e}"))
}

fn merged_cfg_attribute(
    item: &str,
    item_variants: &BTreeMap<String, BTreeSet<usize>>,
    translations: &[Translation],
    variants: &[(usize, PathBuf)],
) -> Option<String> {
    let variant_indexes = item_variants.get(item).unwrap();
    if variant_indexes.len() == variants.len() {
        return None;
    }

    let condition = simplified_cfg_condition(variant_indexes, translations, variants);
    Some(format!("#[cfg({condition})]"))
}

fn simplified_cfg_condition(
    variant_indexes: &BTreeSet<usize>,
    translations: &[Translation],
    variants: &[(usize, PathBuf)],
) -> String {
    let params = varying_config_params(translations, variants);
    let value_lists = params
        .iter()
        .map(|param| {
            variants
                .iter()
                .map(|(translation_index, _)| {
                    translations[*translation_index].config[param].clone()
                })
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let value_indexes = value_lists
        .iter()
        .map(|values| {
            values
                .iter()
                .enumerate()
                .map(|(index, value)| (value.clone(), index))
                .collect::<BTreeMap<_, _>>()
        })
        .collect::<Vec<_>>();
    let feature_lists = params
        .iter()
        .zip(&value_lists)
        .map(|(param, values)| {
            values
                .iter()
                .map(|value| {
                    make_feature_name(param, value).expect("existing config value is valid")
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    let universe = Universe::new(value_lists.iter().map(Vec::len).collect());
    let coords = universe.all_coordinates();
    let mut target = universe.empty_bits(&coords);
    for &variant_index in variant_indexes {
        let translation = &translations[variants[variant_index].0];
        let tuple = params
            .iter()
            .enumerate()
            .map(|(coord, param)| value_indexes[coord][&translation.config[param]])
            .collect::<Vec<_>>();
        universe.set_tuple_bit(&coords, &mut target, &tuple);
    }

    let expr = Solver::new(&universe).solve(target);
    lower_cfg_expr(&expr, &feature_lists)
}

fn lower_cfg_expr(expr: &Expr, feature_lists: &[Vec<String>]) -> String {
    match expr {
        Expr::True => "all()".to_string(),
        Expr::False => "any()".to_string(),
        Expr::Lit { coord, values } => lower_cfg_literal(*coord, values, feature_lists),
        Expr::Not(expr) => format!("not({})", lower_cfg_expr(expr, feature_lists)),
        Expr::And(args) => lower_cfg_operator("all", args, feature_lists),
        Expr::Or(args) => lower_cfg_operator("any", args, feature_lists),
    }
}

fn lower_cfg_operator(name: &str, args: &[Expr], feature_lists: &[Vec<String>]) -> String {
    let args = args
        .iter()
        .map(|arg| lower_cfg_expr(arg, feature_lists))
        .collect::<Vec<_>>()
        .join(", ");
    format!("{name}({args})")
}

fn lower_cfg_literal(
    coord: usize,
    values: &BTreeSet<usize>,
    feature_lists: &[Vec<String>],
) -> String {
    let domain_size = feature_lists[coord].len();
    if values.is_empty() {
        return "any()".to_string();
    }
    if values.len() == domain_size {
        return "all()".to_string();
    }
    if values.len() == 1 {
        return feature_clause(&feature_lists[coord][*values.iter().next().unwrap()]);
    }

    let positive_cost = values.len() + 1;
    let excluded = (0..domain_size)
        .filter(|value| !values.contains(value))
        .collect::<Vec<_>>();
    let negative_cost = match excluded.len() {
        0 => 1,
        1 => 2,
        count => count + 2,
    };

    if positive_cost <= negative_cost {
        let clauses = values
            .iter()
            .map(|value| feature_clause(&feature_lists[coord][*value]))
            .collect::<Vec<_>>();
        lower_cfg_primitive_or(&clauses)
    } else if excluded.len() == 1 {
        format!(
            "not({})",
            feature_clause(&feature_lists[coord][excluded[0]])
        )
    } else {
        let clauses = excluded
            .into_iter()
            .map(|value| feature_clause(&feature_lists[coord][value]))
            .collect::<Vec<_>>();
        format!("not({})", lower_cfg_primitive_or(&clauses))
    }
}

fn lower_cfg_primitive_or(clauses: &[String]) -> String {
    match clauses {
        [] => "any()".to_string(),
        [clause] => clause.clone(),
        _ => format!("any({})", clauses.join(", ")),
    }
}

fn feature_clause(feature: &str) -> String {
    format!("feature = {feature:?}")
}

fn varying_config_params(
    translations: &[Translation],
    variants: &[(usize, PathBuf)],
) -> Vec<String> {
    translations[variants[0].0]
        .config
        .keys()
        .filter(|param| {
            variants
                .iter()
                .map(|(translation_index, _)| &translations[*translation_index].config[*param])
                .collect::<BTreeSet<_>>()
                .len()
                > 1
        })
        .cloned()
        .collect()
}

fn reorder_items(items: Vec<OrderedItem>) -> Vec<OrderedItem> {
    let mut grouped_items = BTreeMap::<(ItemBucket, String), Vec<OrderedItem>>::new();
    let mut ungrouped_items = Vec::new();

    for item in items {
        if should_group_bucket(item.bucket) {
            let name = item
                .group_name
                .clone()
                .expect("grouped item buckets must carry a name");
            grouped_items
                .entry((item.bucket, name))
                .or_default()
                .push(item);
        } else {
            ungrouped_items.push(item);
        }
    }

    let mut group_order = grouped_items
        .into_iter()
        .map(|((bucket, _), mut items)| {
            items.sort_by_key(|item| item.first_seen);
            let first_seen = items[0].first_seen;
            (bucket, first_seen, items)
        })
        .collect::<Vec<_>>();
    group_order.sort_by_key(|(bucket, first_seen, _)| (*bucket, *first_seen));

    ungrouped_items.sort_by_key(|item| (item.bucket, item.first_seen));

    let mut ordered = Vec::with_capacity(
        ungrouped_items.len()
            + group_order
                .iter()
                .map(|(_, _, items)| items.len())
                .sum::<usize>(),
    );
    let mut ungrouped_items = ungrouped_items.into_iter().peekable();
    let mut group_order = group_order.into_iter().peekable();

    for bucket in [
        ItemBucket::Use,
        ItemBucket::ExternCrate,
        ItemBucket::ForeignMod,
        ItemBucket::Mod,
        ItemBucket::Other,
        ItemBucket::Global,
        ItemBucket::Type,
        ItemBucket::Trait,
        ItemBucket::Impl,
        ItemBucket::Fn,
    ] {
        while matches!(ungrouped_items.peek(), Some(item) if item.bucket == bucket) {
            ordered.push(ungrouped_items.next().unwrap());
        }
        while matches!(group_order.peek(), Some((group_bucket, _, _)) if *group_bucket == bucket) {
            ordered.extend(group_order.next().unwrap().2);
        }
    }

    ordered
}

fn should_group_bucket(bucket: ItemBucket) -> bool {
    matches!(
        bucket,
        ItemBucket::Global | ItemBucket::Type | ItemBucket::Trait | ItemBucket::Fn
    )
}

fn parse_rust_file(path: &Path) -> Result<ParsedRustFile, String> {
    let source = fs::read_to_string(path).map_err(|e| format!("failed to read {path:?}: {e}"))?;
    parse_rust_source(&source).map_err(|_| format!("failed to parse {path:?}"))
}

fn parse_rust_source(source: &str) -> Result<ParsedRustFile, ()> {
    let krate =
        std::panic::catch_unwind(|| utils::ast::parse_crate(source.to_string())).map_err(|_| ())?;

    let inner_attrs = krate
        .attrs
        .iter()
        .filter(|attr| attr.style == AttrStyle::Inner)
        .map(pprust::attribute_to_string)
        .collect();
    let items = krate
        .items
        .iter()
        .map(|item| ParsedItem {
            text: pprust::item_to_string(item),
            bucket: classify_item_kind(&item.kind),
            group_name: grouped_item_name(item),
        })
        .collect();
    Ok(ParsedRustFile { inner_attrs, items })
}

fn classify_item_kind(kind: &ItemKind) -> ItemBucket {
    match kind {
        ItemKind::Use(..) => ItemBucket::Use,
        ItemKind::ExternCrate(..) => ItemBucket::ExternCrate,
        ItemKind::ForeignMod(..) => ItemBucket::ForeignMod,
        ItemKind::Mod(..) => ItemBucket::Mod,
        ItemKind::Static(..) | ItemKind::Const(..) => ItemBucket::Global,
        ItemKind::TyAlias(..) | ItemKind::Enum(..) | ItemKind::Union(..) | ItemKind::Struct(..) => {
            ItemBucket::Type
        }
        ItemKind::Trait(..) | ItemKind::TraitAlias(..) => ItemBucket::Trait,
        ItemKind::Impl(..) => ItemBucket::Impl,
        ItemKind::Fn(..) => ItemBucket::Fn,
        _ => ItemBucket::Other,
    }
}

fn grouped_item_name(item: &rustc_ast::Item) -> Option<String> {
    match classify_item_kind(&item.kind) {
        ItemBucket::Global | ItemBucket::Type | ItemBucket::Trait | ItemBucket::Fn => {
            item.kind.ident().map(|ident| ident.name.to_string())
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use std::{
        collections::{BTreeMap, BTreeSet},
        path::PathBuf,
    };

    use super::{
        ItemBucket, OrderedItem, Translation, make_feature_name, merged_cfg_attribute,
        reorder_items,
    };

    fn translation_with_features(
        config: BTreeMap<String, String>,
        varying_params: &BTreeSet<String>,
    ) -> Translation {
        let features = config
            .iter()
            .filter(|(param, _)| varying_params.contains(*param))
            .map(|(param, value)| make_feature_name(param, value).expect("test config is valid"))
            .collect::<Vec<_>>();

        Translation {
            dir: PathBuf::new(),
            config,
            features,
        }
    }

    fn ordered_item(
        text: &str,
        bucket: ItemBucket,
        group_name: Option<&str>,
        first_seen: usize,
    ) -> OrderedItem {
        OrderedItem {
            text: text.to_string(),
            bucket,
            group_name: group_name.map(str::to_string),
            first_seen,
        }
    }

    fn reordered_item_texts(items: Vec<OrderedItem>) -> Vec<String> {
        reorder_items(items)
            .into_iter()
            .map(|item| item.text)
            .collect()
    }

    #[test]
    fn merged_cfg_attribute_uses_cofactor_simplification() {
        let translations = vec![
            translation_with_features(
                [("os", "linux"), ("arch", "x86")]
                    .into_iter()
                    .map(|(param, value)| (param.to_string(), value.to_string()))
                    .collect(),
                &["os".to_string(), "arch".to_string()].into_iter().collect(),
            ),
            translation_with_features(
                [("os", "linux"), ("arch", "arm")]
                    .into_iter()
                    .map(|(param, value)| (param.to_string(), value.to_string()))
                    .collect(),
                &["os".to_string(), "arch".to_string()].into_iter().collect(),
            ),
            translation_with_features(
                [("os", "mac"), ("arch", "x86")]
                    .into_iter()
                    .map(|(param, value)| (param.to_string(), value.to_string()))
                    .collect(),
                &["os".to_string(), "arch".to_string()].into_iter().collect(),
            ),
            translation_with_features(
                [("os", "mac"), ("arch", "arm")]
                    .into_iter()
                    .map(|(param, value)| (param.to_string(), value.to_string()))
                    .collect(),
                &["os".to_string(), "arch".to_string()].into_iter().collect(),
            ),
        ];
        let variants = vec![
            (0, PathBuf::from("linux-x86.rs")),
            (1, PathBuf::from("linux-arm.rs")),
            (2, PathBuf::from("mac-x86.rs")),
            (3, PathBuf::from("mac-arm.rs")),
        ];
        let mut item_variants = BTreeMap::<String, BTreeSet<usize>>::new();
        item_variants.insert(
            "fn shared() {}".to_string(),
            [0usize, 1usize].into_iter().collect(),
        );

        let cfg = merged_cfg_attribute("fn shared() {}", &item_variants, &translations, &variants);
        assert_eq!(cfg, Some("#[cfg(feature = \"os_linux\")]".to_string()));
    }

    #[test]
    fn merged_cfg_attribute_omits_globally_constant_parameters() {
        let varying_params = ["arch".to_string()].into_iter().collect();
        let translations = vec![
            translation_with_features(
                [("os", "linux"), ("arch", "x86")]
                    .into_iter()
                    .map(|(param, value)| (param.to_string(), value.to_string()))
                    .collect(),
                &varying_params,
            ),
            translation_with_features(
                [("os", "linux"), ("arch", "arm")]
                    .into_iter()
                    .map(|(param, value)| (param.to_string(), value.to_string()))
                    .collect(),
                &varying_params,
            ),
        ];
        let variants = vec![
            (0, PathBuf::from("linux-x86.rs")),
            (1, PathBuf::from("linux-arm.rs")),
        ];
        let mut item_variants = BTreeMap::<String, BTreeSet<usize>>::new();
        item_variants.insert(
            "fn x86_only() {}".to_string(),
            [0usize].into_iter().collect(),
        );

        let cfg =
            merged_cfg_attribute("fn x86_only() {}", &item_variants, &translations, &variants);
        assert_eq!(cfg, Some("#[cfg(feature = \"arch_x86\")]".to_string()));
        assert_eq!(translations[0].features, vec!["arch_x86".to_string()]);
        assert_eq!(translations[1].features, vec!["arch_arm".to_string()]);
    }

    #[test]
    fn reorder_items_uses_bucket_order() {
        let items = reordered_item_texts(vec![
            ordered_item("fn zeta() {}", ItemBucket::Fn, Some("zeta"), 0),
            ordered_item("impl Foo {}", ItemBucket::Impl, None, 1),
            ordered_item("trait Worker {}", ItemBucket::Trait, Some("Worker"), 2),
            ordered_item("type Alias = i32;", ItemBucket::Type, Some("Alias"), 3),
            ordered_item("struct Foo;", ItemBucket::Type, Some("Foo"), 4),
            ordered_item(
                "const VALUE: i32 = 1;",
                ItemBucket::Global,
                Some("VALUE"),
                5,
            ),
            ordered_item("mod inner {}", ItemBucket::Mod, None, 6),
            ordered_item(
                "unsafe extern \"C\" {\n    fn foreign();\n}",
                ItemBucket::ForeignMod,
                None,
                7,
            ),
            ordered_item("extern crate core;", ItemBucket::ExternCrate, None, 8),
            ordered_item("use std::fmt;", ItemBucket::Use, None, 9),
        ]);

        assert_eq!(
            items,
            vec![
                "use std::fmt;",
                "extern crate core;",
                "unsafe extern \"C\" {\n    fn foreign();\n}",
                "mod inner {}",
                "const VALUE: i32 = 1;",
                "type Alias = i32;",
                "struct Foo;",
                "trait Worker {}",
                "impl Foo {}",
                "fn zeta() {}",
            ]
        );
    }

    #[test]
    fn reorder_items_groups_types_traits_and_functions_by_name() {
        let items = reordered_item_texts(vec![
            ordered_item(
                "fn zebra() {\n    let _ = 0;\n}",
                ItemBucket::Fn,
                Some("zebra"),
                0,
            ),
            ordered_item(
                "fn apple() {\n    let _ = 1;\n}",
                ItemBucket::Fn,
                Some("apple"),
                1,
            ),
            ordered_item("trait Beta {}", ItemBucket::Trait, Some("Beta"), 2),
            ordered_item("type Shared = i32;", ItemBucket::Type, Some("Shared"), 3),
            ordered_item("struct Pair;", ItemBucket::Type, Some("Pair"), 4),
            ordered_item(
                "trait AliasName = Clone;",
                ItemBucket::Trait,
                Some("AliasName"),
                5,
            ),
            ordered_item(
                "fn apple() {\n    let _ = 2;\n}",
                ItemBucket::Fn,
                Some("apple"),
                6,
            ),
            ordered_item("enum Shared {}", ItemBucket::Type, Some("Shared"), 7),
            ordered_item(
                "trait AliasName = Copy;",
                ItemBucket::Trait,
                Some("AliasName"),
                8,
            ),
            ordered_item(
                "union Pair {\n    field: i32,\n}",
                ItemBucket::Type,
                Some("Pair"),
                9,
            ),
            ordered_item(
                "fn zebra() {\n    let _ = 3;\n}",
                ItemBucket::Fn,
                Some("zebra"),
                10,
            ),
        ]);

        assert_eq!(
            items,
            vec![
                "type Shared = i32;",
                "enum Shared {}",
                "struct Pair;",
                "union Pair {\n    field: i32,\n}",
                "trait Beta {}",
                "trait AliasName = Clone;",
                "trait AliasName = Copy;",
                "fn zebra() {\n    let _ = 0;\n}",
                "fn zebra() {\n    let _ = 3;\n}",
                "fn apple() {\n    let _ = 1;\n}",
                "fn apple() {\n    let _ = 2;\n}",
            ]
        );
    }

    #[test]
    fn reorder_items_groups_globals_by_name() {
        let items = reordered_item_texts(vec![
            ordered_item("const BETA: i32 = 1;", ItemBucket::Global, Some("BETA"), 0),
            ordered_item(
                "static ALPHA: i32 = 2;",
                ItemBucket::Global,
                Some("ALPHA"),
                1,
            ),
            ordered_item(
                "const ALPHA: i32 = 3;",
                ItemBucket::Global,
                Some("ALPHA"),
                2,
            ),
            ordered_item("const BETA: i32 = 4;", ItemBucket::Global, Some("BETA"), 3),
            ordered_item("fn run() {}", ItemBucket::Fn, Some("run"), 4),
            ordered_item(
                "macro_rules! demo { () => {}; }",
                ItemBucket::Other,
                None,
                5,
            ),
        ]);

        assert_eq!(
            items,
            vec![
                "macro_rules! demo { () => {}; }",
                "const BETA: i32 = 1;",
                "const BETA: i32 = 4;",
                "static ALPHA: i32 = 2;",
                "const ALPHA: i32 = 3;",
                "fn run() {}",
            ]
        );
    }
}
