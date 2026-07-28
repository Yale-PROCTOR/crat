#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;

use std::{
    collections::BTreeSet,
    env, fs,
    path::{Path, PathBuf},
};

use rustc_driver::{Callbacks, Compilation, RunCompiler};
use rustc_hir::def::DefKind;
use rustc_interface::{interface, Queries};
use rustc_middle::{
    mir::{
        visit::{PlaceContext, Visitor},
        Local, Location, Place, ProjectionElem, VarDebugInfoContents,
    },
    ty::TyCtxt,
};

struct Cli {
    input: PathBuf,
    universe: PathBuf,
}

impl Cli {
    fn parse() -> Result<Self, String> {
        let mut input = None;
        let mut universe = None;
        let mut args = env::args().skip(1);
        while let Some(flag) = args.next() {
            let value = args
                .next()
                .ok_or_else(|| format!("{flag} requires a path"))?;
            match flag.as_str() {
                "--input" => input = Some(PathBuf::from(value)),
                "--universe" => universe = Some(PathBuf::from(value)),
                _ => return Err(format!("unknown argument {flag}")),
            }
        }
        Ok(Self {
            input: input.ok_or_else(|| "--input is required".to_owned())?,
            universe: universe.ok_or_else(|| "--universe is required".to_owned())?,
        })
    }
}

struct Counter {
    universe: BTreeSet<String>,
}

impl Callbacks for Counter {
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &interface::Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        queries.global_ctxt().unwrap().enter(|tcx| {
            let (usages, seen) = count_usages(tcx, &self.universe);
            let missing = self.universe.difference(&seen).cloned().collect::<Vec<_>>();
            assert!(
                missing.is_empty(),
                "official declaration keys did not map to 2023 optimized MIR: {missing:?}"
            );
            println!("{usages}");
        });
        Compilation::Stop
    }
}

fn count_usages(tcx: TyCtxt<'_>, universe: &BTreeSet<String>) -> (u64, BTreeSet<String>) {
    let mut seen = BTreeSet::new();
    let mut total = 0;
    for did in tcx.hir().body_owners() {
        if !matches!(tcx.def_kind(did), DefKind::Fn | DefKind::AssocFn) {
            continue;
        }
        let body = tcx.optimized_mir(did.to_def_id());
        let function = tcx.def_path_str(did.to_def_id());
        let mut roots = BTreeSet::new();
        for info in &body.var_debug_info {
            if let VarDebugInfoContents::Place(place) = &info.value {
                if let Some(local) = place.as_local() {
                    let key = format!("{function}::{}", info.name);
                    if universe.contains(&key) {
                        roots.insert(local);
                        seen.insert(key);
                    }
                }
            }
        }
        let mut visitor = UsageVisitor {
            roots: &roots,
            usages: 0,
        };
        visitor.visit_body(body);
        total += visitor.usages;
    }
    (total, seen)
}

struct UsageVisitor<'a> {
    roots: &'a BTreeSet<Local>,
    usages: u64,
}

impl<'tcx> Visitor<'tcx> for UsageVisitor<'_> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        if self.roots.contains(&place.local)
            && place
                .projection
                .iter()
                .any(|element| matches!(element, ProjectionElem::Deref))
        {
            self.usages += 1;
        }
        self.super_place(place, context, location);
    }
}

fn find_rlib(deps: &Path, prefix: &str) -> Result<PathBuf, String> {
    let mut matches = fs::read_dir(deps)
        .map_err(|error| format!("read {}: {error}", deps.display()))?
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .map_or(false, |name| {
                    name.starts_with(prefix) && name.ends_with(".rlib")
                })
        })
        .collect::<Vec<_>>();
    matches.sort();
    match matches.as_slice() {
        [path] => Ok(path.clone()),
        _ => Err(format!(
            "expected one {prefix}*.rlib in {}, found {matches:?}",
            deps.display()
        )),
    }
}

fn run() -> Result<(), String> {
    let cli = Cli::parse()?;
    let universe = fs::read_to_string(&cli.universe)
        .map_err(|error| format!("read {}: {error}", cli.universe.display()))?
        .lines()
        .filter(|line| !line.is_empty())
        .map(str::to_owned)
        .collect::<BTreeSet<_>>();
    if universe.is_empty() {
        return Err("declaration universe is empty".to_owned());
    }

    let deps = env::current_exe()
        .map_err(|error| format!("locate executable: {error}"))?
        .parent()
        .ok_or_else(|| "executable has no parent".to_owned())?
        .join("deps");
    let libc = find_rlib(&deps, "liblibc-")?;
    let bitfields = find_rlib(&deps, "libc2rust_bitfields-")?;
    let rustc_args = vec![
        "crown-usage-rustc".to_owned(),
        "--edition=2021".to_owned(),
        "--crate-type=rlib".to_owned(),
        "-L".to_owned(),
        format!("dependency={}", deps.display()),
        "--extern".to_owned(),
        format!("libc={}", libc.display()),
        "--extern".to_owned(),
        format!("c2rust_bitfields={}", bitfields.display()),
        cli.input.display().to_string(),
    ];
    RunCompiler::new(&rustc_args, &mut Counter { universe })
        .run()
        .map_err(|_| format!("rustc rejected {}", cli.input.display()))
}

fn main() {
    if let Err(error) = run() {
        eprintln!("crown-usage-metric: {error}");
        std::process::exit(1);
    }
}
