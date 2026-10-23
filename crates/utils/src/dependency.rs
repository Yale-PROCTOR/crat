use std::{fs, path::Path};

pub fn ensure_crates_io_dependency(
    manifest: &Path,
    name: &str,
    minimum_version: &str,
) -> Result<(), String> {
    let contents = fs::read_to_string(manifest)
        .map_err(|error| format!("failed to read Cargo.toml: {error}"))?;
    if let Some(updated) = normalize_crates_io_dependency(&contents, name, minimum_version)? {
        fs::write(manifest, updated)
            .map_err(|error| format!("failed to write Cargo.toml: {error}"))?;
    }
    Ok(())
}

fn normalize_crates_io_dependency(
    contents: &str,
    name: &str,
    minimum_version: &str,
) -> Result<Option<String>, String> {
    let minimum = cargo_version_key(minimum_version)
        .ok_or_else(|| format!("invalid minimum Cargo version requirement: {minimum_version}"))?;
    let mut cargo = contents
        .parse::<toml::Value>()
        .map_err(|error| format!("working Cargo.toml is invalid: {error}"))?;
    let root = cargo
        .as_table_mut()
        .ok_or_else(|| "Cargo manifest root must be a table".to_owned())?;
    if !root.contains_key("dependencies") {
        root.insert(
            "dependencies".to_owned(),
            toml::Value::Table(toml::Table::new()),
        );
    }
    let dependencies = root
        .get_mut("dependencies")
        .and_then(toml::Value::as_table_mut)
        .ok_or_else(|| "Cargo [dependencies] must be a table".to_owned())?;

    let aliases = dependencies
        .iter()
        .filter_map(|(dependency_name, value)| {
            (dependency_name != name
                && value
                    .as_table()
                    .and_then(|table| table.get("package"))
                    .and_then(toml::Value::as_str)
                    == Some(name))
            .then_some(dependency_name.clone())
        })
        .collect::<Vec<_>>();
    if !aliases.is_empty() {
        return Err(format!(
            "Cargo {name} dependency must use the name {name}, not {aliases:?}"
        ));
    }

    let mut changed = false;
    match dependencies.get_mut(name) {
        None => {
            dependencies.insert(
                name.to_owned(),
                toml::Value::String(minimum_version.to_owned()),
            );
            changed = true;
        }
        Some(toml::Value::String(requirement)) => {
            if cargo_requirement_needs_upgrade(requirement, minimum) {
                *requirement = minimum_version.to_owned();
                changed = true;
            }
        }
        Some(toml::Value::Table(dependency)) => {
            if dependency
                .get("package")
                .is_some_and(|package| package.as_str() != Some(name))
            {
                return Err(format!(
                    "Cargo dependency named {name} aliases a different package"
                ));
            }
            let non_registry = ["git", "path", "workspace"]
                .iter()
                .any(|key| dependency.contains_key(*key));
            let alternate_registry = dependency
                .get("registry")
                .is_some_and(|registry| registry.as_str() != Some("crates-io"));
            if !non_registry && !alternate_registry {
                match dependency.get_mut("version") {
                    None => {
                        dependency.insert(
                            "version".to_owned(),
                            toml::Value::String(minimum_version.to_owned()),
                        );
                        changed = true;
                    }
                    Some(toml::Value::String(requirement)) => {
                        if cargo_requirement_needs_upgrade(requirement, minimum) {
                            *requirement = minimum_version.to_owned();
                            changed = true;
                        }
                    }
                    Some(_) => {
                        return Err(format!("Cargo {name} dependency version must be a string"));
                    }
                }
            }
        }
        Some(_) => {
            return Err(format!("Cargo {name} dependency must be a string or table"));
        }
    }
    if changed {
        toml::to_string(&cargo)
            .map(Some)
            .map_err(|error| format!("failed to serialize Cargo.toml: {error}"))
    } else {
        Ok(None)
    }
}

fn cargo_requirement_needs_upgrade(requirement: &str, minimum: (u64, u64, u64, bool)) -> bool {
    let mut lower_bounds = vec![];
    for raw in requirement.split(',') {
        let Some((operator, version)) = split_cargo_comparator(raw) else {
            return true;
        };
        if cargo_version_key(version).is_none()
            && cargo_wildcard_version_key(version).flatten().is_none()
        {
            return true;
        }
        if matches!(operator, "<" | "<=") {
            continue;
        }
        if let Some(wildcard) = cargo_wildcard_version_key(version).flatten() {
            lower_bounds.push(wildcard);
        } else if let Some(version) = cargo_version_key(version) {
            lower_bounds.push(version);
        } else {
            return true;
        }
    }
    !lower_bounds.into_iter().any(|bound| bound >= minimum)
}

fn cargo_version_key(version: &str) -> Option<(u64, u64, u64, bool)> {
    let (version, build) = version
        .split_once('+')
        .map_or((version, None), |(base, build)| (base, Some(build)));
    if build.is_some_and(|build| !valid_cargo_version_suffix(build)) {
        return None;
    }
    let (numbers, prerelease) = version
        .split_once('-')
        .map_or((version, None), |(numbers, prerelease)| {
            (numbers, Some(prerelease))
        });
    if prerelease.is_some_and(|prerelease| !valid_cargo_version_suffix(prerelease)) {
        return None;
    }
    let mut components = numbers.split('.');
    let major = parse_cargo_version_number(components.next()?)?;
    let minor = parse_cargo_version_number(components.next().unwrap_or("0"))?;
    let patch = parse_cargo_version_number(components.next().unwrap_or("0"))?;
    if components.next().is_some() {
        return None;
    }
    Some((major, minor, patch, prerelease.is_none()))
}

fn cargo_wildcard_version_key(version: &str) -> Option<Option<(u64, u64, u64, bool)>> {
    let (version, build) = version
        .split_once('+')
        .map_or((version, None), |(core, build)| (core, Some(build)));
    if build.is_some_and(|build| !valid_cargo_version_suffix(build)) {
        return None;
    }
    let (core, prerelease) = version
        .split_once('-')
        .map_or((version, None), |(core, prerelease)| {
            (core, Some(prerelease))
        });
    if prerelease.is_some_and(|prerelease| !valid_cargo_version_suffix(prerelease)) {
        return None;
    }
    let components = core.split('.').collect::<Vec<_>>();
    if components.is_empty() || components.len() > 3 {
        return None;
    }
    if !components.iter().all(|component| {
        matches!(*component, "x" | "X" | "*") || parse_cargo_version_number(component).is_some()
    }) {
        return None;
    }
    let Some(wildcard) = components
        .iter()
        .position(|component| matches!(*component, "x" | "X" | "*"))
    else {
        return Some(None);
    };
    if prerelease.is_some() || build.is_some() {
        return None;
    }
    let mut numeric = components[..wildcard]
        .iter()
        .map(|component| parse_cargo_version_number(component))
        .collect::<Option<Vec<_>>>()?;
    if numeric.is_empty() {
        return None;
    }
    numeric.resize(3, 0);
    Some(Some((numeric[0], numeric[1], numeric[2], true)))
}

fn parse_cargo_version_number(component: &str) -> Option<u64> {
    (!component.is_empty() && component.bytes().all(|byte| byte.is_ascii_digit()))
        .then(|| component.parse().ok())?
}

fn valid_cargo_version_suffix(suffix: &str) -> bool {
    !suffix.is_empty()
        && suffix
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'-'))
}

fn split_cargo_comparator(comparator: &str) -> Option<(&str, &str)> {
    let comparator = comparator.trim();
    for operator in [">=", "<=", ">", "<", "=", "^", "~"] {
        if let Some(version) = comparator.strip_prefix(operator) {
            let version = version.trim();
            return (!version.is_empty()).then_some((operator, version));
        }
    }
    (!comparator.is_empty()).then_some(("", comparator))
}

#[cfg(test)]
mod tests {
    use super::normalize_crates_io_dependency;

    const NAME: &str = "proctor-libc";
    const MINIMUM: &str = "0.3.0";

    fn normalized_dependency(manifest: &str) -> toml::Value {
        let normalized = normalize_crates_io_dependency(manifest, NAME, MINIMUM)
            .unwrap()
            .unwrap_or_else(|| manifest.to_owned());
        normalized.parse().unwrap()
    }

    #[test]
    fn preserves_or_upgrades_crates_io_requirements() {
        for manifest in [
            "[package]\nname = \"sample\"\nversion = \"0.1.0\"\n",
            "[dependencies]\n",
        ] {
            let normalized = normalized_dependency(manifest);
            assert_eq!(normalized["dependencies"][NAME].as_str(), Some(MINIMUM));
        }
        for requirement in [
            "0.0.1",
            "0.1.0",
            "0.2.9",
            "0.3.0-alpha.1",
            "0.4.0+??",
            "0.4.x-alpha",
            "0.4.*+meta",
            "18446744073709551616",
        ] {
            let manifest = format!("[dependencies]\n{NAME} = \"{requirement}\"\n");
            assert_eq!(
                normalized_dependency(&manifest)["dependencies"][NAME].as_str(),
                Some(MINIMUM)
            );
        }
        for requirement in [
            "0.3",
            "^0.3.0",
            ">=0.3.0",
            "0.4",
            "1",
            "18446744073709551615",
        ] {
            let manifest = format!("[dependencies]\n{NAME} = \"{requirement}\"\n");
            assert!(
                normalize_crates_io_dependency(&manifest, NAME, MINIMUM)
                    .unwrap()
                    .is_none()
            );
        }

        let normalized = normalized_dependency(
            "[dependencies]\nproctor-libc = { version = \"0.2\", features = [\"x\"], default-features = false }\n",
        );
        let dependency = normalized["dependencies"][NAME].as_table().unwrap();
        assert_eq!(dependency["version"].as_str(), Some(MINIMUM));
        assert_eq!(dependency["features"].as_array().unwrap().len(), 1);
        assert_eq!(dependency["default-features"].as_bool(), Some(false));

        let normalized =
            normalized_dependency("[dependencies]\nproctor-libc = { default-features = false }\n");
        let dependency = normalized["dependencies"][NAME].as_table().unwrap();
        assert_eq!(dependency["version"].as_str(), Some(MINIMUM));
        assert_eq!(dependency["default-features"].as_bool(), Some(false));

        for dependency in [
            "{ path = \"../proctor-libc\" }",
            "{ git = \"https://example.invalid/repo\" }",
            "{ workspace = true }",
            "{ registry = \"private\", version = \"0.1\" }",
            "{ registry = 7, version = \"0.1\" }",
        ] {
            let manifest = format!("[dependencies]\n{NAME} = {dependency}\n");
            assert!(
                normalize_crates_io_dependency(&manifest, NAME, MINIMUM)
                    .unwrap()
                    .is_none()
            );
        }
    }

    #[test]
    fn rejects_aliases_and_malformed_values() {
        let cases = [
            ("[dependencies", "working Cargo.toml is invalid:"),
            ("dependencies = 7", "Cargo [dependencies] must be a table"),
            (
                "[dependencies]\nproctor-libc = 7",
                "Cargo proctor-libc dependency must be a string or table",
            ),
            (
                "[dependencies]\nproctor-libc = { version = 7 }",
                "Cargo proctor-libc dependency version must be a string",
            ),
            (
                "[dependencies]\npl = { package = \"proctor-libc\", version = \"0.1\" }",
                "Cargo proctor-libc dependency must use the name proctor-libc",
            ),
            (
                "[dependencies]\nproctor-libc = { package = \"another-crate\", version = \"0.1\" }",
                "Cargo dependency named proctor-libc aliases a different package",
            ),
            (
                "[dependencies]\nproctor-libc = { package = 7, version = \"0.1\" }",
                "Cargo dependency named proctor-libc aliases a different package",
            ),
        ];
        for (manifest, expected) in cases {
            let error = normalize_crates_io_dependency(manifest, NAME, MINIMUM).unwrap_err();
            assert!(error.starts_with(expected), "{error}");
        }
    }

    #[test]
    fn preserves_unrelated_manifest_values() {
        let manifest = r#"
[package]
name = "sample"
version = "0.1.0"

[lib]
path = "root.rs"

[dependencies]
serde = { version = "1", features = ["derive"] }
bytemuck = "1.25.2"
xj_scanf = "0.2.6"
proctor-libc = { version = "0.2", features = ["x"], default-features = false, registry = "crates-io" }
"#;
        let before = manifest.parse::<toml::Value>().unwrap();
        let updated = normalize_crates_io_dependency(manifest, NAME, MINIMUM)
            .unwrap()
            .unwrap();
        let after = updated.parse::<toml::Value>().unwrap();
        assert_eq!(after["package"], before["package"]);
        assert_eq!(after["lib"], before["lib"]);
        for name in ["serde", "bytemuck", "xj_scanf"] {
            assert_eq!(after["dependencies"][name], before["dependencies"][name]);
        }
        for field in ["features", "default-features", "registry"] {
            assert_eq!(
                after["dependencies"][NAME][field],
                before["dependencies"][NAME][field]
            );
        }
        assert_eq!(
            after["dependencies"][NAME]["version"].as_str(),
            Some(MINIMUM)
        );
    }
}
