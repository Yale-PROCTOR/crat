//! decl_counter: CROWN's official declaration metric (the CROWN-artifact inventory library, as vendored in
//! `inventory/`) applied to any emitted program against any CROWN analysis universe.
//! usage: decl_counter <emitted-crate-dir> <analysis_results-dir> [strip-src] [inline-mods] [twin] [slots=<tsv>]
//! prints: universe, eliminated_ref, eliminated_box, after, rate, parse_failures, raw_decl_positions
//!
//! Two driver-side options; the library is unmodified:
//! - `inline-mods`: an emitted tree that is one `lib.rs` holding the program's modules inline
//!   (`pub mod src { pub mod avl { .. } }`), while the library qualifies its keys by the FILE's module
//!   (it does not descend into inline `mod` items). The option splits each file's inline modules into one
//!   named source per module, the crate root (`lib.rs`, `c2rust-lib.rs`) taking the empty path, so the keys come out as
//!   `src::avl::insert::node`, CROWN's own layout (`src/avl.rs`). Items keep their tokens unchanged.
//! - `slots=<tsv>`: writes one row per universe key with the walker's classification (ref / box / both / none).
use crown_artifact_inventory::{analyze_json_claims, analyze_named_rust_sources, analyze_rust_source};
use quote::ToTokens;
use std::{ffi::OsStr, fs, io, path::{Path, PathBuf}};

fn collect(dir: &Path, files: &mut Vec<PathBuf>) -> io::Result<()> {
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if entry.file_type()?.is_dir() {
            if entry.file_name() != OsStr::new("target") && entry.file_name() != OsStr::new("analysis_results") {
                collect(&path, files)?;
            }
        } else if path.extension() == Some(OsStr::new("rs")) {
            files.push(path);
        }
    }
    Ok(())
}

fn module(root: &Path, path: &Path) -> String {
    path.strip_prefix(root).unwrap_or(path).with_extension("").iter()
        .map(|c| c.to_string_lossy().replace('-', "_")).collect::<Vec<_>>().join("::")
}

/// Splits a file's inline modules into (module path, source) pairs; every non-module item stays in its module.
fn split_inline(items: Vec<syn::Item>, path: &str, out: &mut Vec<(String, String)>) {
    let mut here = Vec::new();
    for item in items {
        match item {
            syn::Item::Mod(m) if m.content.is_some() => {
                let name = m.ident.to_string();
                let sub = if path.is_empty() { name } else { format!("{path}::{name}") };
                split_inline(m.content.unwrap().1, &sub, out);
            }
            other => here.push(other),
        }
    }
    let mut tokens = proc_macro2::TokenStream::new();
    for item in &here {
        item.to_tokens(&mut tokens);
    }
    out.push((path.to_owned(), tokens.to_string()));
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (emitted, analysis) = (PathBuf::from(&args[0]), PathBuf::from(&args[1]));
    let flags = &args[2..];
    let strip = flags.iter().any(|f| f == "strip-src");
    let inline = flags.iter().any(|f| f == "inline-mods");
    let slots_out = flags.iter().find_map(|f| f.strip_prefix("slots=")).map(PathBuf::from);
    let mut files = Vec::new();
    collect(&emitted, &mut files)?;
    files.sort();
    let mut sources: Vec<(String, String)> = Vec::new();
    for p in &files {
        if p.file_name() == Some(OsStr::new("build.rs")) && inline {
            continue;
        }
        let text = fs::read_to_string(p)?;
        if inline {
            let m = module(&emitted, p);
            let base = if m == "lib" || m == "main" || m == "c2rust_lib" { String::new() } else { m };
            match syn::parse_file(&text) {
                Ok(file) => split_inline(file.items, &base, &mut sources),
                Err(_) => sources.push((base, text)),
            }
        } else {
            sources.push((module(&emitted, p), text));
        }
    }
    let refs: Vec<(&str, &str)> = sources.iter().map(|(m, s)| (m.as_str(), s.as_str())).collect();
    let (counts, failures) = match analyze_named_rust_sources(&refs) {
        Ok(c) => (c, 0usize),
        Err(_) => {
            // the inventory's own fallback: report the files that do not parse
            let bad = sources.iter().filter(|(_, s)| analyze_rust_source(s).is_err()).count();
            (Default::default(), bad)
        }
    };
    let rd = |k: &str| fs::read_to_string(analysis.join(format!("{k}.json")));
    let claims = analyze_json_claims(&rd("ownership")?, &rd("statistics")?, &rd("mutability")?, &rd("fatness")?)?;
    // optional key normalization: `strip-src` drops a leading `src::` module segment on both sides, for
    // an emitted program laid out flat (c2rust-lib.rs + x.rs) against a universe computed on `src/x.rs`
    let norm = |k: &String| -> String { if strip { k.strip_prefix("src::").unwrap_or(k).to_owned() } else { k.clone() } };
    // `twin` (NOT CROWN's counter verbatim; a diagnostic): the translator's exposure wrapper keeps the C-named
    // function with the C signature and moves the safe body to `__jobcrat_safe_<name>`; the option reads the twin's
    // slots under the C name, so the difference it makes is exactly the wrapper's renaming.
    let twin = flags.iter().any(|f| f == "twin");
    let detwin = |k: String| -> String { if twin { k.replace("::__jobcrat_safe_", "::") } else { k } };
    let u: std::collections::BTreeSet<String> = claims.fn_d0_mut_ptr_keys.iter().map(norm).collect();
    let collisions = claims.fn_d0_mut_ptr_keys.len() - u.len();
    let refs_n: std::collections::BTreeSet<String> = counts.reference_function_slot_keys.iter().map(norm).map(detwin).collect();
    let boxes_n: std::collections::BTreeSet<String> = counts.box_function_slot_keys.iter().map(norm).map(detwin).collect();
    let er = refs_n.intersection(&u).count();
    let eb = boxes_n.intersection(&u).count();
    let before = claims.fn_d0_mut_ptr_keys.len();
    if collisions > 0 { eprintln!("key collisions after normalization: {collisions}"); }
    let after = before - er - eb;
    let d = &counts.declarations;
    let raw = d.local_raw_mut + d.local_raw_const + d.param_raw_mut + d.param_raw_const
        + d.return_raw_mut + d.return_raw_const + d.field_raw_mut + d.field_raw_const;
    let rate = if before > 0 { 100.0 * (er + eb) as f64 / before as f64 } else { 0.0 };
    if let Some(path) = slots_out {
        let mut tsv = String::from("key\twalker\n");
        for k in &u {
            let class = match (refs_n.contains(k), boxes_n.contains(k)) {
                (true, true) => "both",
                (true, false) => "ref",
                (false, true) => "box",
                (false, false) => "none",
            };
            tsv.push_str(&format!("{k}\t{class}\n"));
        }
        fs::write(path, tsv)?;
    }
    println!("universe={before} eliminated_ref={er} eliminated_box={eb} after={after} rate={rate:.1} parse_failures={failures} raw_decl_positions={raw}");
    Ok(())
}
