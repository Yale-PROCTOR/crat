//! Bakes the analysis identity into the build: the code fingerprint over this
//! crate's `src/analyses` and the legacy files the analysis runs on
//! (`BO_ANALYSIS_FINGERPRINT`), the toolchain file's and the lockfile's SHA-256
//! (`BO_TOOLCHAIN_SHA256`, `BO_LOCK_SHA256`), and the covered list in `OUT_DIR`.
//! The analysis reads no source tree at run time.

#[path = "src/analyses/borrow_ownership/code_fingerprint.rs"]
mod code_fingerprint;

use std::path::{Path, PathBuf};

use sha2::{Digest, Sha256};

fn main() {
    let manifest = PathBuf::from(std::env::var_os("CARGO_MANIFEST_DIR").expect("manifest dir"));
    let analyses = manifest.join("src/analyses");
    let legacy = manifest.join("../pointer_replacer/src");
    let toolchain = manifest.join("../../rust-toolchain.toml");
    let lock = manifest.join("../../Cargo.lock");
    let roots = code_fingerprint::analysis_roots(&analyses, &legacy);

    let covered = code_fingerprint::covered(&roots);
    let out = PathBuf::from(std::env::var_os("OUT_DIR").expect("OUT_DIR"));
    let list: String = covered
        .iter()
        .map(|(name, _)| format!("{name}\n"))
        .collect();
    std::fs::write(out.join("bo_analysis_files.txt"), list).expect("covered list");

    let sha = |path: &Path| {
        let bytes =
            std::fs::read(path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
        format!("{:x}", Sha256::digest(bytes))
    };
    println!(
        "cargo:rustc-env=BO_ANALYSIS_FINGERPRINT={}",
        code_fingerprint::fingerprint(&roots)
    );
    println!("cargo:rustc-env=BO_TOOLCHAIN_SHA256={}", sha(&toolchain));
    println!("cargo:rustc-env=BO_LOCK_SHA256={}", sha(&lock));

    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed={}", analyses.display());
    for (_, path) in covered
        .iter()
        .filter(|(name, _)| name.starts_with("legacy/"))
    {
        println!("cargo:rerun-if-changed={}", path.display());
    }
    println!("cargo:rerun-if-changed={}", toolchain.display());
    println!("cargo:rerun-if-changed={}", lock.display());
}
