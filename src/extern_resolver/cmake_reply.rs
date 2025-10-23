use std::path::{Component, Path};

use rustc_hash::{FxHashMap, FxHashSet};
use serde::Deserialize;

#[derive(Debug, Deserialize)]
struct Index {
    reply: Reply,
}

#[derive(Debug, Deserialize)]
struct Reply {
    #[serde(rename = "codemodel-v2")]
    code_model_v2: CodeModelV2,
}

#[derive(Debug, Deserialize)]
struct CodeModelV2 {
    #[serde(rename = "jsonFile")]
    json_file: String,
}

#[derive(Debug, Deserialize)]
struct CodeModel {
    configurations: Vec<Configuration>,
}

#[derive(Debug, Deserialize)]
struct Configuration {
    targets: Vec<ConfigurationTarget>,
}

#[derive(Debug, Deserialize)]
struct ConfigurationTarget {
    #[serde(rename = "jsonFile")]
    json_file: String,
}

#[derive(Debug, Deserialize)]
struct Target {
    #[serde(rename = "type")]
    type_: String,
    artifacts: Vec<Artifact>,
    link: Option<Link>,
    sources: Vec<Source>,
}

#[derive(Debug, Deserialize)]
struct Artifact {
    path: String,
}

#[derive(Debug, Deserialize)]
struct Link {
    #[serde(rename = "commandFragments")]
    command_fragments: Vec<CommandFragment>,
}

#[derive(Debug, Deserialize)]
struct CommandFragment {
    fragment: String,
    role: String,
}

#[derive(Debug, Deserialize)]
struct Source {
    path: String,
}

pub(super) fn parse_index_file(
    index_file: &Path,
    build_dir: &Path,
    source_dir: &Path,
    top_level_mods: &FxHashSet<&str>,
) -> FxHashMap<String, usize> {
    let index: Index = serde_json::from_reader(std::fs::File::open(index_file).unwrap()).unwrap();
    let code_model_file = index_file
        .parent()
        .unwrap()
        .join(index.reply.code_model_v2.json_file);

    let code_model: CodeModel =
        serde_json::from_reader(std::fs::File::open(code_model_file).unwrap()).unwrap();
    let [configuration] = &code_model.configurations[..] else { panic!() };

    let mut executable = None;
    let mut dependencies: FxHashMap<_, Vec<_>> = FxHashMap::default();
    for target in &configuration.targets {
        let target_file = index_file.parent().unwrap().join(&target.json_file);
        let target: Target =
            serde_json::from_reader(std::fs::File::open(target_file).unwrap()).unwrap();
        let mut sources = target.link.map_or_else(Vec::new, |link| {
            link.command_fragments
                .iter()
                .filter(|fragment| fragment.role != "flags" && !fragment.fragment.starts_with('-'))
                .map(|fragment| build_dir.join(&fragment.fragment))
                .collect()
        });
        if target.type_ == "OBJECT_LIBRARY" {
            assert_eq!(target.artifacts.len(), target.sources.len());
            for (artifact, source) in target.artifacts.iter().zip(&target.sources) {
                let mut sources = sources.clone();
                sources.push(source_dir.join(&source.path));
                dependencies.insert(build_dir.join(&artifact.path), sources);
            }
        } else {
            let [artifact] = &target.artifacts[..] else { panic!() };
            let artifact_path = build_dir.join(&artifact.path);
            if target.type_ == "EXECUTABLE" {
                assert!(executable.is_none());
                executable = Some(artifact_path.clone());
            }
            sources.extend(target.sources.iter().map(|s| source_dir.join(&s.path)));
            dependencies.insert(artifact_path, sources);
        }
    }

    let executable = executable.unwrap();
    let mut worklist = vec![];
    let mut sources = vec![];
    worklist.extend(dependencies[&executable].iter().rev());

    while let Some(path) = worklist.pop() {
        if path.extension() == Some("c".as_ref()) {
            sources.push(path);
        } else {
            worklist.extend(dependencies[path].iter().rev());
        }
    }

    sources
        .iter()
        .enumerate()
        .map(|(i, source)| {
            let source = source.strip_prefix(source_dir).unwrap();
            let mut started = false;
            let mut module_path = "src".to_string();
            for comp in source.with_extension("").components() {
                let Component::Normal(comp) = comp else { panic!() };
                let comp = comp.to_str().unwrap();
                if top_level_mods.contains(comp) {
                    started = true;
                }
                if started {
                    module_path.push_str("::");
                    module_path.push_str(comp);
                }
            }
            (module_path, i)
        })
        .collect()
}
