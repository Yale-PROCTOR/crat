#![feature(rustc_private)]

use std::{
    fs,
    fs::File,
    path::{Path, PathBuf},
};

use clap::{Parser, ValueEnum};
use passes::*;
use serde::Deserialize;
use utils::compilation::run_compiler_on_path;

#[derive(Parser)]
#[command(version)]
struct Args {
    #[arg(long, help = "Keep allow attributes inserted by C2Rust")]
    expand_keep_allows: bool,

    #[arg(long, help = "Path to the CMake reply index file")]
    extern_cmake_reply_index_file: Option<PathBuf>,
    #[arg(long, help = "Path to the top-level build directory for CMake")]
    extern_build_dir: Option<PathBuf>,
    #[arg(long, help = "Path to the top-level source directory for CMake")]
    extern_source_dir: Option<PathBuf>,
    #[arg(long, help = "Choose an arbitrary one when multiple candidates exist")]
    extern_choose_arbitrary: bool,
    #[arg(long, help = "Ignore return types when resolving extern functions")]
    extern_ignore_return_type: bool,
    #[arg(long, help = "Ignore parameter types when resolving extern functions")]
    extern_ignore_param_type: bool,
    #[arg(long, num_args = 2, value_names = ["FROM", "TO"], help = "Resolve hint for extern functions (example: `from::foo to::foo`)")]
    extern_function_hints: Vec<String>,
    #[arg(long, num_args = 2, value_names = ["FROM", "TO"], help = "Resolve hint for extern static variables (example: `from::foo to::foo`)")]
    extern_static_hints: Vec<String>,
    #[arg(long, num_args = 2, value_names = ["FROM", "TO"], help = "Resolve hint for extern types (example: `from::foo to::foo`)")]
    extern_type_hints: Vec<String>,

    #[arg(
        long,
        help = "Enable verbose ownership solver output for the translate pass"
    )]
    pointer_verbose: bool,
    #[arg(short, long, help = "Enable verbose output")]
    verbose: bool,
    #[arg(long, value_delimiter = ',', help = "Transformation passes to run")]
    pass: Vec<Pass>,
    #[arg(long, help = "Path to the configuration file")]
    config: Option<PathBuf>,
    #[arg(long, value_delimiter = ',', help = "Names of functions exposed to C")]
    c_exposed_fn: Vec<String>,
    #[arg(long, help = "Write the translate pass's emission receipt to this file")]
    bo_receipt: Option<PathBuf>,

    #[arg(long, help = "Enable in-place transformation of the input directory")]
    inplace: bool,
    #[arg(short, long, help = "Path to the output directory")]
    output: Option<PathBuf>,
    #[arg(short, long, help = "Path to the log file")]
    log_file: Option<PathBuf>,
    #[arg(help = "Path to the input directory containing Cargo.toml")]
    input: PathBuf,
}

#[derive(Clone, Debug, ValueEnum, Deserialize)]
#[clap(rename_all = "lower")]
#[serde(rename_all = "lowercase")]
enum Pass {
    Prepare,
    Translate,
    Check,
}

#[derive(Debug, Default, Deserialize)]
struct Config {
    #[serde(default)]
    expand: expander::Config,
    #[serde(default)]
    r#extern: extern_resolver::Config,
    #[serde(default)]
    pointer: pointer_replacer::Config,

    #[serde(default)]
    c_exposed_fns: Vec<String>,

    #[serde(default)]
    verbose: bool,
    #[serde(default)]
    passes: Vec<Pass>,
    #[serde(default)]
    inplace: bool,
    log_file: Option<PathBuf>,
    output: Option<PathBuf>,
}

fn main() {
    let args = Args::parse();

    let mut config = args
        .config
        .map(|path| {
            let content = fs::read_to_string(path).unwrap();
            toml::from_str::<Config>(&content).unwrap()
        })
        .unwrap_or_default();
    config.c_exposed_fns.extend(args.c_exposed_fn);
    config.verbose |= args.verbose;
    config.inplace |= args.inplace;
    config.pointer.verbose |= args.pointer_verbose;
    config.passes.extend(args.pass);
    if args.output.is_some() {
        config.output = args.output;
    }

    if config.passes.is_empty() {
        eprintln!("No passes specified");
        std::process::exit(1);
    }

    if let Some(log) = args.log_file.or(config.log_file) {
        let log_file = File::create(log).unwrap();
        tracing_subscriber::fmt()
            .with_max_level(tracing::Level::INFO)
            .without_time()
            .with_ansi(false)
            .with_level(false)
            .with_writer(log_file)
            .init();
    }

    config.expand.keep_allows |= args.expand_keep_allows;

    if args.extern_cmake_reply_index_file.is_some() {
        config.r#extern.cmake_reply_index_file = args.extern_cmake_reply_index_file;
    }
    if args.extern_build_dir.is_some() {
        config.r#extern.build_dir = args.extern_build_dir;
    }
    if args.extern_source_dir.is_some() {
        config.r#extern.source_dir = args.extern_source_dir;
    }
    config.r#extern.ignore_return_type |= args.extern_ignore_return_type;
    config.r#extern.ignore_param_type |= args.extern_ignore_param_type;
    config.r#extern.choose_arbitrary |= args.extern_choose_arbitrary;
    for args in args.extern_function_hints.chunks(2) {
        let [from, to] = args else { panic!() };
        config
            .r#extern
            .function_hints
            .push(extern_resolver::LinkHint::new(from.clone(), to.clone()));
    }
    for args in args.extern_static_hints.chunks(2) {
        let [from, to] = args else { panic!() };
        config
            .r#extern
            .static_hints
            .push(extern_resolver::LinkHint::new(from.clone(), to.clone()));
    }
    for args in args.extern_type_hints.chunks(2) {
        let [from, to] = args else { panic!() };
        config
            .r#extern
            .type_hints
            .push(extern_resolver::LinkHint::new(from.clone(), to.clone()));
    }

    config
        .pointer
        .c_exposed_fns
        .extend(config.c_exposed_fns.iter().cloned());

    let receipt_path = args.bo_receipt;

    let dir = if let Some(mut output) = config.output {
        output.push(args.input.file_name().unwrap());
        if output.exists() {
            if !output.is_dir() {
                eprintln!("{output:?} is not a directory");
                std::process::exit(1);
            }
            clear_dir(&output);
        } else if fs::create_dir(&output).is_err() {
            eprintln!("Cannot create {output:?}");
            std::process::exit(1);
        }
        copy_dir(&args.input, &output, true);
        output
    } else if config.inplace {
        args.input
    } else {
        eprintln!("Output directory should be specified when not running in-place");
        std::process::exit(1)
    };

    let lib_path = utils::find_lib_path(&dir).unwrap_or_else(|e| {
        eprintln!("{e}");
        std::process::exit(1);
    });
    let file = dir.join(&lib_path);

    for pass in config.passes {
        if config.verbose {
            println!("{pass:?}");
        }
        match pass {
            Pass::Prepare => {
                let s = run_compiler_on_path(&file, |tcx| expander::expand(config.expand, tcx))
                    .unwrap();
                remove_rs_files(&dir, true);
                std::fs::write(&file, s).unwrap();
                let s = run_compiler_on_path(&file, |tcx| {
                    extern_resolver::resolve_extern(&config.r#extern, tcx)
                })
                .unwrap();
                std::fs::write(&file, s).unwrap();
                let s = run_compiler_on_path(&file, preprocessor::preprocess).unwrap();
                std::fs::write(&file, s).unwrap();
            }
            Pass::Check => {
                run_compiler_on_path(&file, utils::type_check).unwrap();
            }
            Pass::Translate => {
                let receipt =
                    pointer_replacer::rewrite_bo(&file, config.pointer.c_exposed_fns.iter().cloned())
                        .unwrap_or_else(|e| {
                            eprintln!("{e}");
                            std::process::exit(1);
                        });
                println!("{}", receipt.summary());
                if let Some(path) = &receipt_path {
                    std::fs::write(path, receipt.render()).unwrap();
                }
            }
        }
    }
}

fn clear_dir(path: &Path) {
    for entry in fs::read_dir(path).unwrap() {
        let entry_path = entry.unwrap().path();
        if entry_path.is_dir() {
            let name = entry_path.file_name().unwrap();
            if name != "target" {
                fs::remove_dir_all(entry_path).unwrap();
            }
        } else {
            fs::remove_file(entry_path).unwrap();
        }
    }
}

fn remove_rs_files(path: &Path, root: bool) {
    for entry in fs::read_dir(path).unwrap() {
        let entry_path = entry.unwrap().path();
        let name = entry_path.file_name().unwrap();
        if root && (name == "target" || name == "build.rs") {
            continue;
        }
        if entry_path.is_dir() {
            remove_rs_files(&entry_path, false);
            if fs::read_dir(&entry_path).unwrap().next().is_none() {
                fs::remove_dir(entry_path).unwrap();
            }
        } else if name.to_str().unwrap().ends_with(".rs") {
            fs::remove_file(entry_path).unwrap();
        }
    }
}

fn copy_dir(src: &Path, dst: &Path, root: bool) {
    for entry in fs::read_dir(src).unwrap() {
        let src_path = entry.unwrap().path();
        let name = src_path.file_name().unwrap();
        let dst_path = dst.join(name);
        if src_path.is_file() {
            fs::copy(src_path, dst_path).unwrap();
        } else if src_path.is_dir() && (!root || name != "target") {
            fs::create_dir(&dst_path).unwrap();
            copy_dir(&src_path, &dst_path, false);
        }
    }
}
