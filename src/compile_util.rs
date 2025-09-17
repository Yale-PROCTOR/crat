//! utils to run compiler

use std::{
    path::{Path, PathBuf},
    process::Command,
    sync::Arc,
};

use etrace::ok_or;
use rustc_errors::{
    ColorConfig, DiagInner, FatalError, Level,
    emitter::{Emitter, HumanEmitter},
    registry::Registry,
};
use rustc_feature::UnstableFeatures;
use rustc_hash::FxHashMap;
use rustc_interface::Config;
use rustc_middle::{
    ty::TyCtxt,
    mir::{Body, TerminatorKind},
};
use rustc_session::{
    EarlyDiagCtxt,
    config::{CrateType, ErrorOutputType, Input, Options},
};
use rustc_span::{FileName, edition::Edition, source_map::SourceMap};

#[inline]
pub fn run_compiler_on_path<R: Send, F: FnOnce(TyCtxt<'_>) -> R + Send>(
    path: &Path,
    f: F,
) -> Result<R, FatalError> {
    run_compiler_on_input(path_to_input(path), f)
}

#[inline]
pub fn run_compiler_on_str<R: Send, F: FnOnce(TyCtxt<'_>) -> R + Send>(
    code: &str,
    f: F,
) -> Result<R, FatalError> {
    run_compiler_on_input(str_to_input(code), f)
}

#[inline]
pub fn run_compiler_on_input<R: Send, F: FnOnce(TyCtxt<'_>) -> R + Send>(
    input: Input,
    f: F,
) -> Result<R, FatalError> {
    run_compiler(make_config(input), f)
}

#[inline]
pub fn run_compiler<R: Send, F: FnOnce(TyCtxt<'_>) -> R + Send>(
    config: Config,
    f: F,
) -> Result<R, FatalError> {
    rustc_driver::catch_fatal_errors(|| {
        rustc_interface::run_compiler(config, |compiler| {
            let krate = rustc_interface::parse(&compiler.sess);
            rustc_interface::create_and_enter_global_ctxt(compiler, krate, f)
        })
    })
}

#[inline]
pub fn path_to_input(path: &Path) -> Input {
    Input::File(path.to_path_buf())
}

#[inline]
pub fn str_to_input(code: &str) -> Input {
    Input::Str {
        name: FileName::Custom("main.rs".to_string()),
        input: code.to_string(),
    }
}

#[inline]
pub fn make_config(input: Input) -> Config {
    let opts = find_deps();
    Config {
        opts: Options {
            sysroot: sys_root().unwrap(),
            search_paths: opts.search_paths,
            externs: opts.externs,
            unstable_features: UnstableFeatures::Allow,
            crate_types: vec![CrateType::Rlib],
            debug_assertions: false,
            edition: Edition::Edition2021,
            ..Options::default()
        },
        crate_cfg: vec![],
        crate_check_cfg: vec![],
        input,
        output_dir: None,
        output_file: None,
        ice_file: None,
        file_loader: None,
        locale_resources: rustc_driver::DEFAULT_LOCALE_RESOURCES.to_vec(),
        lint_caps: FxHashMap::default(),
        psess_created: Some(Box::new(|ps| {
            let sm = ps.clone_source_map();
            ps.dcx().set_emitter(Box::new(ErrorEmitter::new(sm)));
        })),
        register_lints: None,
        override_queries: None,
        extra_symbols: vec![],
        make_codegen_backend: None,
        registry: Registry::new(rustc_errors::codes::DIAGNOSTICS),
        hash_untracked_state: None,
        using_internal_features: &rustc_driver::USING_INTERNAL_FEATURES,
        expanded_args: vec![],
    }
}

/// Emit errors but not warnings
struct ErrorEmitter(HumanEmitter);

impl ErrorEmitter {
    fn new(sm: Arc<SourceMap>) -> Self {
        let emitter = HumanEmitter::new(
            rustc_errors::emitter::stderr_destination(ColorConfig::Auto),
            rustc_driver::default_translator(),
        )
        .sm(Some(sm));
        Self(emitter)
    }
}

impl Emitter for ErrorEmitter {
    fn source_map(&self) -> Option<&SourceMap> {
        self.0.source_map()
    }

    fn emit_diagnostic(&mut self, diag: DiagInner, registry: &Registry) {
        if matches!(diag.level(), Level::Fatal | Level::Error) {
            self.0.emit_diagnostic(diag, registry);
        }
    }

    fn translator(&self) -> &rustc_errors::translation::Translator {
        self.0.translator()
    }
}

fn find_deps() -> Options {
    let mut args = vec!["a.rs".to_string()];

    let dir = std::env::var("DIR").unwrap_or_else(|_| ".".to_string());
    let dep = format!("{dir}/deps_crate/target/debug/deps");
    if let Ok(dir) = std::fs::read_dir(&dep) {
        args.push("-L".to_string());
        args.push(format!("dependency={dep}"));

        for f in dir {
            let f = ok_or!(f, continue);
            let f = f.file_name().to_str().unwrap().to_string();
            if !f.ends_with(".rlib") {
                continue;
            }
            let i = f.find('-').unwrap();
            let name = f[3..i].to_string();
            let d = format!("{name}={dep}/{f}");
            args.push("--extern".to_string());
            args.push(d);
        }
    }

    let mut handler = EarlyDiagCtxt::new(ErrorOutputType::default());
    let matches = rustc_driver::handle_options(&handler, &args).unwrap();
    rustc_session::config::build_session_options(&mut handler, &matches)
}

fn sys_root() -> Option<PathBuf> {
    std::env::var("SYSROOT")
        .ok()
        .map(PathBuf::from)
        .or_else(|| {
            let home = std::env::var("RUSTUP_HOME")
                .or_else(|_| std::env::var("MULTIRUST_HOME"))
                .ok();
            let toolchain = std::env::var("RUSTUP_TOOLCHAIN")
                .or_else(|_| std::env::var("MULTIRUST_TOOLCHAIN"))
                .ok();
            toolchain_path(home, toolchain)
        })
        .or_else(|| {
            Command::new("rustc")
                .arg("--print")
                .arg("sysroot")
                .output()
                .ok()
                .and_then(|out| String::from_utf8(out.stdout).ok())
                .map(|s| PathBuf::from(s.trim()))
        })
        .or_else(|| option_env!("SYSROOT").map(PathBuf::from))
        .or_else(|| {
            let home = option_env!("RUSTUP_HOME")
                .or(option_env!("MULTIRUST_HOME"))
                .map(ToString::to_string);
            let toolchain = option_env!("RUSTUP_TOOLCHAIN")
                .or(option_env!("MULTIRUST_TOOLCHAIN"))
                .map(ToString::to_string);
            toolchain_path(home, toolchain)
        })
}

fn toolchain_path(home: Option<String>, toolchain: Option<String>) -> Option<PathBuf> {
    home.and_then(|home| {
        toolchain.map(|toolchain| {
            let mut path = PathBuf::from(home);
            path.push("toolchains");
            path.push(toolchain);
            path
        })
    })
}

pub fn body_to_str(body: &Body<'_>) -> String {
    use std::fmt::Write;
    let mut s = String::new();
    writeln!(s, "{:?} {{", body.source.instance.def_id()).unwrap();
    for (bb, bbd) in body.basic_blocks.iter_enumerated() {
        writeln!(s, "    {:?}:", bb).unwrap();
        for stmt in &bbd.statements {
            writeln!(s, "        {:?}", stmt).unwrap();
        }
        if !matches!(
            bbd.terminator().kind,
            TerminatorKind::Return | TerminatorKind::Assert { .. }
        ) {
            writeln!(s, "        {:?}", bbd.terminator().kind).unwrap();
        }
    }
    writeln!(s, "}}").unwrap();
    s
}

pub fn body_size(body: &Body<'_>) -> usize {
    body.basic_blocks
        .iter()
        .map(|bbd| bbd.statements.len() + 1)
        .sum()
}
