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

    #[arg(long, help = "Expose fixed boolean parameters as no-op Cargo features")]
    ignore_boolean: bool,
}

fn main() {
    let args = Args::parse();
    utils::compilation::run_compiler_on_str("fn main() {}", |_| {
        if let Err(e) = merger::merge(&args.translations, &args.output, args.ignore_boolean) {
            eprintln!("{e}");
            std::process::exit(1);
        }
    })
    .unwrap();
}
