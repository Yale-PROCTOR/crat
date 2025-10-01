#![feature(rustc_private)]

use std::{
    fs,
    fs::File,
    path::{Path, PathBuf},
};

use clap::{Parser, ValueEnum};
use compile_util::run_compiler_on_path;
use crat::*;
use serde::Deserialize;

#[derive(Parser)]
#[command(version)]
struct Args {
    // Extern
    #[arg(long, help = "Choose an arbitrary one when multiple candidates exist")]
    extern_choose_arbitrary: bool,
    #[arg(long, num_args = 2, value_names = ["FROM", "TO"], help = "Resolve hint for extern functions (example: `from::foo to::foo`)")]
    extern_function_hints: Vec<String>,
    #[arg(long, num_args = 2, value_names = ["FROM", "TO"], help = "Resolve hint for extern static variables (example: `from::foo to::foo`)")]
    extern_static_hints: Vec<String>,
    #[arg(long, num_args = 2, value_names = ["FROM", "TO"], help = "Resolve hint for extern types (example: `from::foo to::foo`)")]
    extern_type_hints: Vec<String>,

    // Bin
    #[arg(
        long,
        value_delimiter = ',',
        help = "Main function to ignore when adding bin files"
    )]
    bin_ignore: Vec<String>,

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
    #[arg(help = "Path to the input directory containing c2rust-lib.rs")]
    input: PathBuf,
}

#[derive(Clone, Debug, ValueEnum, Deserialize)]
#[clap(rename_all = "lower")]
#[serde(rename_all = "lowercase")]
enum Pass {
    Expand,
    Extern,
    ExternE,
    Unsafe,
    Preprocess,
    PreprocessE,
    Bin,
    Check,
    Libc,
    OutParam,
    Lock,
    Union,
    Io,
    Pointer,
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
    r#extern: extern_resolver::Config,
    #[serde(default)]
    bin: bin_file_adder::Config,
    #[serde(default)]
    r#union: union_replacer::tag_analysis::Config,
    #[serde(default)]
    outparam: outparam_replacer::Config,

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

    for arg in args.bin_ignore {
        config.bin.ignores.push(arg);
    }

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
        config.outparam.points_to_file = args.points_to_file.clone();
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
    let file = dir.join("c2rust-lib.rs");

    for pass in config.passes {
        if config.verbose {
            println!("{pass:?}");
        }
        match pass {
            Pass::Expand => {
                let s = run_compiler_on_path(&file, expander::expand).unwrap();
                remove_rs_files(&dir, true);
                std::fs::write(&file, s).unwrap();
            }
            Pass::Extern => {
                run_compiler_on_path(&file, |tcx| {
                    extern_resolver::resolve_extern(&config.r#extern, tcx)
                })
                .unwrap();
            }
            Pass::ExternE => {
                let s = run_compiler_on_path(&file, |tcx| {
                    extern_resolver::resolve_extern_in_expanded_ast(&config.r#extern, tcx)
                })
                .unwrap();
                std::fs::write(&file, s).unwrap();
            }
            Pass::Unsafe => {
                run_compiler_on_path(&file, unsafe_resolver::resolve_unsafe).unwrap();
            }
            Pass::Preprocess => {
                run_compiler_on_path(&file, preprocessor::preprocess).unwrap();
            }
            Pass::PreprocessE => {
                let s = run_compiler_on_path(&file, preprocessor::preprocess_expanded_ast).unwrap();
                std::fs::write(&file, s).unwrap();
            }
            Pass::Bin => {
                run_compiler_on_path(&file, |tcx| {
                    bin_file_adder::add_bin_files(&dir, &config.bin, tcx)
                })
                .unwrap();
            }
            Pass::Check => {
                run_compiler_on_path(&file, type_checker::type_check).unwrap();
            }
            Pass::Libc => {
                run_compiler_on_path(&file, libc_replacer::run).unwrap();
            }
            Pass::OutParam => {
                todo!()
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
                let _res =
                    run_compiler_on_path(&file, |tcx| io_replacer::replace_io(&dir, tcx)).unwrap();
            }
            Pass::Pointer => {
                todo!()
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
                    let solutions = points_to::andersen::run_analysis(tcx);
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
                    );
                    let fns = res
                        .iter()
                        .filter(|(_, (_, res))| {
                            !res.output_params.is_empty()
                        })
                        .count();
                    let musts = res
                        .values()
                        .map(|res| res.1.output_params.iter().filter(|p| p.must).count())
                        .sum::<usize>();
                    let mays = res
                        .values()
                        .map(|res| res.1.output_params.iter().filter(|p| !p.must).count())
                        .sum::<usize>();
                    println!("{} {} {}", fns, musts, mays);

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
