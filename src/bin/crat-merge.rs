#![feature(rustc_private)]

use std::path::PathBuf;

use clap::Parser;

#[derive(Parser)]
#[command(version)]
struct Args {
    #[arg(help = "Path to translations.json")]
    translations: PathBuf,

    #[arg(help = "Directory under which the merged crate will be created")]
    output: PathBuf,
}

fn main() {
    let args = Args::parse();
    utils::compilation::run_compiler_on_str("fn main() {}", |_| {
        if let Err(e) = merger::merge(&args.translations, &args.output) {
            eprintln!("{e}");
            std::process::exit(1);
        }
    })
    .unwrap();
}
