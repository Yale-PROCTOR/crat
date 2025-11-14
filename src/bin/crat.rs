#![feature(rustc_private)]

use std::{
    fs,
    fs::File,
    path::{Path, PathBuf},
};

use clap::{Parser, ValueEnum};
use crat::outparam_replacer;
use passes::*;
use serde::Deserialize;
use utils::compilation::run_compiler_on_path;

#[derive(Parser)]
#[command(version)]
struct Args {
    // Expand
    #[arg(long, help = "Keep allow attributes inserted by C2Rust")]
    expand_keep_allows: bool,

    // Extern
    #[arg(long, help = "Path to the CMake reply index file")]
    extern_cmake_reply_index_file: Option<PathBuf>,
    #[arg(long, help = "Path to the top-level build directory for CMake")]
    extern_build_dir: Option<PathBuf>,
    #[arg(long, help = "Path to the top-level source directory for CMake")]
    extern_source_dir: Option<PathBuf>,
    #[arg(long, help = "Choose an arbitrary one when multiple candidates exist")]
    extern_choose_arbitrary: bool,
    #[arg(long, num_args = 2, value_names = ["FROM", "TO"], help = "Resolve hint for extern functions (example: `from::foo to::foo`)")]
    extern_function_hints: Vec<String>,
    #[arg(long, num_args = 2, value_names = ["FROM", "TO"], help = "Resolve hint for extern static variables (example: `from::foo to::foo`)")]
    extern_static_hints: Vec<String>,
    #[arg(long, num_args = 2, value_names = ["FROM", "TO"], help = "Resolve hint for extern types (example: `from::foo to::foo`)")]
    extern_type_hints: Vec<String>,

    // Unsafe
    #[arg(long, help = "Remove unused items")]
    unsafe_remove_unused: bool,
    #[arg(long, help = "Remove no_mangle attributes")]
    unsafe_remove_no_mangle: bool,
    #[arg(long, help = "Replace `pub` with `pub(crate)`")]
    unsafe_replace_pub: bool,

    // Bin
    #[arg(
        long,
        value_delimiter = ',',
        help = "Main function to ignore when adding bin files"
    )]
    bin_ignore: Vec<String>,
    #[arg(
        long,
        help = "Name of the binary. Works only when there is a single main function."
    )]
    bin_name: Option<String>,

    // Andersen
    #[arg(long, help = "Use optimized MIR for points-to analysis")]
    andersen_use_optimized_mir: bool,

    // Union
    #[arg(long, value_delimiter = ',', help = "Target unions to replace")]
    union_target: Vec<String>,

    // OutParam
    #[arg(long, value_parser = max_sensitivity_in_range, help = "Maximum number of states at loop heads")]
    outparam_max_loop_head_states: Option<usize>,
    #[arg(
        long,
        help = "Check aliasing of function parameters with global variables"
    )]
    outparam_check_global_alias: bool,
    #[arg(long, help = "Check aliasing of function parameters with each other")]
    outparam_check_param_alias: bool,
    #[arg(long, help = "Disable widening in the analysis")]
    outparam_no_widening: bool,
    #[arg(
        long,
        help = "Enable simplification during output parameter transformation"
    )]
    outparam_simplify: bool,
    #[arg(long, help = "File containing the result of output parameter analysis")]
    outparam_analysis_file: Option<PathBuf>,
    #[arg(
        long,
        help = "Print the analysis times for the n functions with the longest times."
    )]
    outparam_function_times: Option<usize>,
    #[arg(
        long,
        value_delimiter = ',',
        help = "Print analysis results of the specified functions"
    )]
    outparam_print_functions: Vec<String>,

    #[arg(short, long, help = "Enable verbose output")]
    verbose: bool,
    #[arg(long, value_delimiter = ',', help = "Transformation passes to run")]
    pass: Vec<Pass>,
    #[arg(long, help = "Analysis to run")]
    analysis: Option<Analysis>,
    #[arg(long, help = "Path to the configuration file")]
    config: Option<PathBuf>,
    #[arg(long, help = "File containing the result of points-to analysis")]
    points_to_file: Option<PathBuf>,

    #[arg(long, help = "Enable in-place transformation of the input directory")]
    inplace: bool,
    #[arg(short, long, help = "Path to the output directory")]
    output: Option<PathBuf>,
    #[arg(short, long, help = "Path to the analysis output file")]
    analysis_output: Option<PathBuf>,
    #[arg(short, long, help = "Path to the log file")]
    log_file: Option<PathBuf>,
    #[arg(help = "Path to the input directory containing Cargo.toml")]
    input: PathBuf,
}

#[derive(Clone, Debug, ValueEnum, Deserialize)]
#[clap(rename_all = "lower")]
#[serde(rename_all = "lowercase")]
enum Pass {
    Expand,
    Preprocess,
    Extern,
    Unsafe,
    Unexpand,
    Split,
    Bin,
    Check,
    Format,
    Libc,
    OutParam,
    Lock,
    Union,
    Io,
    Pointer,
    Static,
}

#[derive(Clone, Debug, ValueEnum, Deserialize)]
#[clap(rename_all = "lower")]
#[serde(rename_all = "lowercase")]
enum Analysis {
    Andersen,
    OutParam,
}

#[derive(Debug, Default, Deserialize)]
struct Config {
    #[serde(default)]
    expand: expander::Config,
    #[serde(default)]
    r#extern: extern_resolver::Config,
    #[serde(default)]
    r#unsafe: unsafe_resolver::Config,
    #[serde(default)]
    bin: bin_file_adder::Config,
    #[serde(default)]
    r#union: union_replacer::Config,
    #[serde(default)]
    outparam: outparam_replacer::Config,
    #[serde(default)]
    andersen: points_to::andersen::Config,

    #[serde(default)]
    verbose: bool,
    #[serde(default)]
    passes: Vec<Pass>,
    analysis: Option<Analysis>,
    #[serde(default)]
    inplace: bool,
    log_file: Option<PathBuf>,
    output: Option<PathBuf>,
    analysis_output: Option<PathBuf>,
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
    config.verbose |= args.verbose;
    config.inplace |= args.inplace;
    config.passes.extend(args.pass);
    if args.analysis.is_some() {
        config.analysis = args.analysis;
    }
    if args.output.is_some() {
        config.output = args.output;
    }
    if args.analysis_output.is_some() {
        config.analysis_output = args.analysis_output;
    }

    if config.passes.is_empty() && config.analysis.is_none() {
        eprintln!("No passes or analysis specified");
        std::process::exit(1);
    }

    if !config.passes.is_empty() && config.analysis.is_some() {
        eprintln!("Cannot run analysis and passes at the same time");
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

    config.r#unsafe.remove_unused |= args.unsafe_remove_unused;
    config.r#unsafe.remove_no_mangle |= args.unsafe_remove_no_mangle;
    config.r#unsafe.replace_pub |= args.unsafe_replace_pub;

    for arg in args.bin_ignore {
        config.bin.ignores.push(arg);
    }
    if args.bin_name.is_some() {
        config.bin.name = args.bin_name;
    }

    config.andersen.use_optimized_mir |= args.andersen_use_optimized_mir;

    for u in args.union_target {
        config.r#union.targets.insert(u);
    }
    if args.points_to_file.is_some() {
        config.r#union.points_to_file = args.points_to_file.clone();
    }

    if let Some(v) = args.outparam_max_loop_head_states {
        config.outparam.max_loop_head_states = v;
    }

    if config.outparam.max_loop_head_states == 0 {
        config.outparam.max_loop_head_states = usize::MAX;
    }

    config.outparam.check_global_alias |= args.outparam_check_global_alias;
    config.outparam.check_param_alias |= args.outparam_check_param_alias;
    config.outparam.no_widening |= args.outparam_no_widening;
    config.outparam.simplify |= args.outparam_simplify;

    config
        .outparam
        .print_functions
        .extend(args.outparam_print_functions);

    if args.outparam_function_times.is_some() {
        config.outparam.function_times = args.outparam_function_times;
    }
    if args.outparam_analysis_file.is_some() {
        config.outparam.analysis_file = args.outparam_analysis_file;
    }
    if args.points_to_file.is_some() {
        config.outparam.points_to_file = args.points_to_file;
    }

    let dir = if !config.passes.is_empty() {
        if config.analysis_output.is_some() {
            eprintln!("Analysis output is not supported when running passes");
            std::process::exit(1);
        }
        if let Some(mut output) = config.output {
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
        }
    } else {
        if config.output.is_some() {
            eprintln!("Output directory is not supported when running analysis");
            std::process::exit(1);
        }
        if config.analysis_output.is_none() {
            eprintln!("Analysis output file should be specified when running analysis");
            std::process::exit(1);
        }
        args.input
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
            Pass::Expand => {
                let s = run_compiler_on_path(&file, |tcx| expander::expand(config.expand, tcx))
                    .unwrap();
                remove_rs_files(&dir, true);
                std::fs::write(&file, s).unwrap();
            }
            Pass::Extern => {
                let s = run_compiler_on_path(&file, |tcx| {
                    extern_resolver::resolve_extern(&config.r#extern, tcx)
                })
                .unwrap();
                std::fs::write(&file, s).unwrap();
            }
            Pass::Unsafe => {
                let s = run_compiler_on_path(&file, |tcx| {
                    unsafe_resolver::resolve_unsafe(&config.r#unsafe, tcx)
                })
                .unwrap();
                std::fs::write(&file, s).unwrap();
            }
            Pass::Preprocess => {
                let s = run_compiler_on_path(&file, preprocessor::preprocess).unwrap();
                std::fs::write(&file, s).unwrap();
            }
            Pass::Unexpand => {
                let s = run_compiler_on_path(&file, unexpander::unexpand).unwrap();
                std::fs::write(&file, s).unwrap();
            }
            Pass::Split => {
                run_compiler_on_path(&file, |_| splitter::split(&dir, &lib_path)).unwrap();
            }
            Pass::Bin => {
                run_compiler_on_path(&file, |tcx| {
                    bin_file_adder::add_bin_files(&dir, &config.bin, tcx)
                })
                .unwrap();
            }
            Pass::Check => {
                run_compiler_on_path(&file, utils::type_check).unwrap();
            }
            Pass::Format => {
                run_compiler_on_path(&file, formatter::format).unwrap();
            }
            Pass::Libc => {
                let s = run_compiler_on_path(&file, libc_replacer::replace_libc).unwrap();
                std::fs::write(&file, s).unwrap();
            }
            Pass::OutParam => {
                run_compiler_on_path(&file, |tcx| {
                    outparam_replacer::transform::transform(tcx, &dir, &lib_path, &config.outparam)
                })
                .unwrap();
            }
            Pass::Lock => {
                todo!()
            }
            Pass::Union => {
                let _res = run_compiler_on_path(&file, |tcx| {
                    union_replacer::tag_analysis::analyze(&config.r#union, config.verbose, tcx)
                })
                .unwrap();
            }
            Pass::Io => {
                let res = run_compiler_on_path(&file, io_replacer::replace_io).unwrap();
                std::fs::write(&file, res.code).unwrap();
                io_replacer::add_deps(&dir, res.tempfile, res.bytemuck);
            }
            Pass::Pointer => {
                let s =
                    run_compiler_on_path(&file, pointer_replacer::replace_local_borrows).unwrap();
                std::fs::write(&file, s).unwrap();
            }
            Pass::Static => {
                let s = run_compiler_on_path(&file, static_replacer::replace_static).unwrap();
                std::fs::write(&file, s).unwrap();
            }
        }
    }

    if let Some(analysis) = config.analysis {
        if config.verbose {
            println!("{analysis:?}");
        }
        let analysis_output = config.analysis_output.unwrap();
        match analysis {
            Analysis::Andersen => {
                run_compiler_on_path(&file, |tcx| {
                    let solutions = points_to::andersen::run_analysis(&config.andersen, tcx);
                    let file = std::fs::File::create(analysis_output).unwrap();
                    let file = std::io::BufWriter::new(file);
                    points_to::andersen::write_solutions(file, &solutions).unwrap();
                })
                .unwrap();
            }
            Analysis::OutParam => {
                run_compiler_on_path(&file, |tcx| {
                    let res = outparam_replacer::ai::analysis::analyze(
                        &config.outparam,
                        config.verbose,
                        tcx,
                    )
                    .0;
                    let fns = res
                        .iter()
                        .filter(|(_, res)| !res.output_params.is_empty())
                        .count();
                    let musts = res
                        .values()
                        .map(|res| res.output_params.iter().filter(|p| p.must).count())
                        .sum::<usize>();
                    let mays = res
                        .values()
                        .map(|res| res.output_params.iter().filter(|p| !p.must).count())
                        .sum::<usize>();
                    println!("{fns} {musts} {mays}");

                    outparam_replacer::ai::analysis::write_analysis_result(&analysis_output, &res);
                })
                .unwrap();
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

fn max_sensitivity_in_range(s: &str) -> Result<usize, String> {
    let m: usize = s
        .parse()
        .map_err(|_| "max_loop_head_states must be a positive integer".to_string())?;
    if m == 0 {
        Err("max_loop_head_states must be greater than 0".to_string())
    } else {
        Ok(m)
    }
}
