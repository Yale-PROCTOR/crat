# packaging/ -- deriving the artifact-evaluation source zip from a head (path A)

This directory derives the artifact-evaluation source zip (the translator under the paper's name, `jobcrat`, with
`artifact/` and `benchmarks/`) from a head of `borrow-ownership-to-master` (R1260-1: path A, the zip from the cleaned
branch). The derivation packages and checks; it edits no code except the legacy crate's cut (option 3A) and the
driver (a template holding the shipped passes). Everything a reviewer should not see is removed on the branch, and the
derivation's greps prove it is gone: a hit is cleanup work on the branch, never an edit here. The plan of record is
`docs/agents/plan/2026-10-20-ae-zip-path-a-derivation.md` (ruled R1261-5). `evaluation/` is excluded from the zip,
except `evaluation/docker/` (taken from `ARTIFACT_REV`), which becomes the zip's `artifact/`.

## Running

```
bash evaluation/packaging/rederive.sh <head> <tag>      # -> $SCRATCH/jobcrat-source.zip, rederive.log, branch rederive-<tag>
DRY_RUN=1 bash evaluation/packaging/rederive.sh ...     # the hits listed under $SCRATCH/hits/, the derived tree built, no zip
LEGACY_SEARCH=1 bash evaluation/packaging/rederive.sh ...  # option 3A's list made again by the compiler ($SCRATCH/legacy-cut.txt)
bash evaluation/packaging/smoke.sh <tag> [program ...]  # the driver from the unpacked zip on avl and bst
```

Needs the pinned toolchain (`rust-toolchain.toml`), the solver and libclang variables the top-level README names,
python3 >= 3.11 and `unzip`. Two inputs are required, because the evaluation's inputs are not in the repository:
`BENCH` (a zip whose `jobcrat-source/benchmarks/` holds them, or a directory laid out as `benchmarks/`) and
`BENCH_SHA256SUMS` (the SHA-256 of its `SHA256SUMS`; the derivation stops unless it matches, every file checks and none
but `README.md` is unlisted). The other parameters, with defaults under `target/packaging/<tag>`, are listed at the top
of `rederive.sh`: `REPO`, `SCRATCH`, `WORKTREES`, `TOOLS_TARGET`, `CARGO`, `ARTIFACT_REV`, `LEGACY_LIST`,
`IDENTITY_PATTERNS` / `IDENTITY_ALLOW`, `PROVENANCE_PATTERNS`, `FORBIDDEN` / `FORBIDDEN_RE` / `FORBIDDEN_ALLOW`,
`HASH_REPOS`, `DRY_RUN`.

## The derivation, one commit per step on the branch `rederive-<tag>`

- **A. What ships.** Removed: development files, `examples/`, `evaluation/`, `LICENSE`, the tools directories, the
  crates the shipped passes do not use (`finders`, `io_replacer`, `merger`, `outparam_replacer`, `static_replacer`,
  `union_replacer`) and the other binaries; `dev-dependencies`. `BENCH`'s `benchmarks/` becomes the zip's
  `benchmarks/`, byte for byte, exempt from the rename and reported separately by the identity grep;
  `ARTIFACT_REV`'s `evaluation/docker/` becomes `artifact/`. The driver is `driver-template.crat.rs`: the branch's
  `src/bin/crat.rs` holding only the passes `expand`, `extern`, `preprocess` and `pointer` and their options (no
  `pointer-old`). The README is `README-template.md`.
- **B. Tests.** `tools/cfgcut` deletes every `#[cfg(test)]` item by byte range (syn); `reach.py` walks `mod`
  declarations from the crate roots (`modscan.py`: inline modules resolve as the compiler resolves them), removes
  unresolved test modules and the orphans; unreferenced data files go.
- **C. Option 3A** (`legacy_search.py`). The legacy rewriter keeps `collector::collect_fn_ptrs` and
  `diagnostics::DiagnosticsMode`, which the pointer pass reads (the item cuts). Which modules of the crates beside the
  pointer pass's own (`pointer_replacer`, `passes`, `points_to`, `utils`) ship is decided by the compiler: the modules
  that read the cut rewriter go first, then every module subtree is removed in turn, top-down, and the removal kept when
  `cargo check` reports no error, until a whole round removes nothing; the crate dependencies `-W
  unused_crate_dependencies` then reports unused in those crates go. The removals are frozen into `legacy-cut.txt`;
  every derivation applies the list (an entry that does not apply stops it) and its release build re-proves it.
- **D. The rename** (`rename.py`), word-boundary rules only, over every text file: R1 `CRAT_` -> `JOBCRAT_`; R2 the
  word `crat` -> `jobcrat`; R3 `crat_` -> `jobcrat_`; R4 `_crat` -> `_jobcrat`; R5 the word `Crat` -> `Jobcrat`; R6
  `__crat_` / `__CRAT_` -> `__jobcrat_` / `__JOBCRAT_`. `crate`-family words and `CRAT` alone are untouched
  (`rename.py untouched` lists them). The binary and the wrapper are renamed. Comments ship (R1261-5 (b)); the rename
  applies to them as to everything else.
- **E. Build and checks.** `cargo build --release` of the derived tree (warnings printed per crate); the lockfile as
  cargo resolved it. Over the whole tree but `benchmarks/`: the identity grep, the provenance grep, the forbidden names
  (`FORBIDDEN` fixed strings, `FORBIDDEN_RE` patterns: the internal names of the survey's N rows), commit hashes of our
  repositories; `cfg(test)` left; the comments shipped (tokens and lines, per crate). Any hit stops the derivation
  before the zip; `DRY_RUN=1` lists them all under `$SCRATCH/hits/` instead.
- **The zip.** `mkzip.sh`: the tree under `jobcrat-source/`, zipped in sorted order with Python's zipfile; unzipped
  and compared with the staged copy; `cargo build --release --locked` from the unpacked zip.

## The smoke

`smoke.sh` builds `deps_crate` from the unpacked zip, runs `jobcrat -v --pass expand,extern,preprocess,pointer` on each
program (avl and bst by default) and compares every emitted `.rs` file with the tree of record, byte for byte or modulo
rule R6.
