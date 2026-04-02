#![feature(rustc_private)]

extern crate rustc_ast;
extern crate rustc_ast_pretty;

use std::{
    collections::{BTreeMap, BTreeSet},
    ffi::{OsStr, OsString},
    fmt::Write as _,
    fs,
    path::{Path, PathBuf},
};

use rustc_ast::AttrStyle;
use rustc_ast_pretty::pprust;
use serde::Deserialize;
use serde_json::Value;
use toml_edit::{Array, DocumentMut, Item, Table, value};

#[derive(Deserialize)]
struct RawTranslation {
    dir: PathBuf,
    #[serde(flatten)]
    config: BTreeMap<String, Value>,
}

struct Translation {
    dir: PathBuf,
    features: Vec<String>,
}

struct SharedFile {
    name: &'static str,
    contents: Vec<u8>,
}

struct ParsedRustFile {
    inner_attrs: Vec<String>,
    items: Vec<String>,
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
    let mut feature_map = BTreeMap::<String, (String, String)>::new();
    let mut seen_feature_sets = BTreeSet::<Vec<String>>::new();
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

        let mut features = Vec::with_capacity(entry.config.len());
        for (param, value) in entry.config {
            let raw_value = config_value_to_string(&param, &value)?;
            let feature = make_feature_name(&param, &raw_value)?;
            if let Some((existing_param, existing_value)) = feature_map.get(&feature) {
                if existing_param != &param || existing_value != &raw_value {
                    return Err(format!(
                        "feature name collision: {feature:?} maps to both {existing_param}={existing_value} and {param}={raw_value}"
                    ));
                }
            } else {
                feature_map.insert(feature.clone(), (param, raw_value));
            }
            features.push(feature);
        }
        if !seen_feature_sets.insert(features.clone()) {
            return Err(format!(
                "duplicate configuration detected for translation directory {dir:?}"
            ));
        }
        translations.push(Translation { dir, features });
    }

    Ok(translations)
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
    let mut merged = String::new();

    for (index, path) in variants {
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

        let cfg = cfg_attribute(&translations[*index].features);
        for item in parsed.items {
            writeln!(merged, "{cfg}").unwrap();
            writeln!(merged, "{item}").unwrap();
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

fn parse_rust_file(path: &Path) -> Result<ParsedRustFile, String> {
    let source = fs::read_to_string(path).map_err(|e| format!("failed to read {path:?}: {e}"))?;
    let krate = std::panic::catch_unwind(|| utils::ast::parse_crate(source))
        .map_err(|_| format!("failed to parse {path:?}"))?;

    let inner_attrs = krate
        .attrs
        .iter()
        .filter(|attr| attr.style == AttrStyle::Inner)
        .map(pprust::attribute_to_string)
        .collect();
    let items = krate
        .items
        .iter()
        .map(|item| pprust::item_to_string(item))
        .collect();
    Ok(ParsedRustFile { inner_attrs, items })
}

fn cfg_attribute(features: &[String]) -> String {
    let clauses = features
        .iter()
        .map(|feature| format!("feature = {feature:?}"))
        .collect::<Vec<_>>()
        .join(", ");
    format!("#[cfg(all({clauses}))]")
}
