# packaging/ -- deriving the submission source zip from a head

This directory re-derives the submission source zip (the translator under the paper's name, `jobcrat`) from a
`borrow-ownership` head. The zip builds on its own and is not an artifact-evaluation package. Its SHA-256 and file
count are recorded in the packaging lane's report, not here. `evaluation/` is excluded from the zip (the user's
ruling of 10-15; `packaging/` holds the identity grep and the rename map), except `evaluation/docker/`, which becomes
the zip's `artifact/` (R1236-1) and goes through the rename and every check like the rest of the tree.

## Running

```
bash evaluation/packaging/rederive.sh <head> <tag>      # -> $SCRATCH/jobcrat-source.zip, rederive.log, branch rederive-<tag>
bash evaluation/packaging/smoke.sh <tag> [program ...]  # the driver from the unpacked zip on avl and bst
```

Needs the pinned toolchain (`rust-toolchain.toml`), the solver and libclang variables the top-level README names,
python3 >= 3.11 and `unzip`. Two inputs are required, because the evaluation's inputs are not in the repository:
`BENCH` (a zip whose `jobcrat-source/benchmarks/` holds them, e.g. an earlier submission zip, or a directory laid out
as `benchmarks/`) and `BENCH_SHA256SUMS` (the SHA-256 of its `SHA256SUMS`; the derivation stops unless it matches,
every file checks and none but `README.md` is unlisted). Everything else is a parameter with a default under `target/packaging/<tag>`: `REPO`,
`SCRATCH`, `WORKTREES`, `TOOLS_TARGET`, `CARGO` (the cargo command), `ENVREL` (the environment of record, relative
to the head), `IDENTITY_PATTERNS` (the identity grep; the operator adds the authors' and hosts' names),
`IDENTITY_ALLOW` (fixed strings the identity grep ignores: the crates.io index, the third parties' own repositories
the artifact fetches from), `PROVENANCE_PATTERNS` (the internal-provenance grep over `artifact/`: lane names, relay /
report numbers, ruling ids, addenda, batch names), `ARTIFACT_REV` (the revision whose `evaluation/docker/` becomes
`artifact/`; default: the head). The translator is derived from the head, which stays the frozen source the paper
evaluated; `ARTIFACT_REV` lets the artifact come from the working branch (R1253-5). A hit of either grep stops the
derivation before the zip. For
`smoke.sh`: `INPUTS` (prepared inputs), `REF_TREES` (the emitted trees of record), `DEPS_TARGET`.

## The derivation, one commit per step on the branch `rederive-<tag>`

- **A. Removals and the trim** (relays 001 s2, 002, 003, 004, 005 s1). Development files, `benchmarks/`,
  `examples/`, `evaluation/`, `LICENSE`, the frames and tools directories; every crate and pass the evaluated pipeline did not
  run (kept: `passes` trimmed to expander / extern_resolver / preprocessor, `pointer_replacer`, `points_to`,
  `utils`, `deps_crate`); `dev-dependencies`. `BENCH`'s `benchmarks/` becomes the zip's `benchmarks/`, byte for
  byte, exempt from the rename and reported separately by the identity grep. **Option 3** (`option3.py`): the legacy rewriter out, keeping
  `collect_fn_ptrs`, `DiagnosticsMode` and `Config`, and the seven analyses only it used. The driver
  (`driver-template.crat.rs`) with the passes `prepare` (expand, extern, preprocess), `translate` (the analysis
  and emission path of record, `--analysis-env`, `--receipt`, `--c-exposed-fn`) and `check`. The README
  (`README-template.md`). `config/analysis-env.sh` = the exports of `ENVREL`, host-local lines dropped.
- **B. Tests.** `tools/cfgcut` deletes every `#[cfg(test)]` item by byte range (syn); `reach.py` walks `mod`
  declarations from the crate roots, removes unresolved test modules and the orphans; unreferenced data files go.
- **C. Comments.** `tools/rslex strip` removes every comment with the compiler's lexer (`rustc_lexer`); `rslex dump`
  verifies the token streams are otherwise equal. `strip_misc.py` does TOML (value equality checked).
- **D. The rename** (`rename.py`, relays 002 and 003), word-boundary rules only, over every text file: R1 `CRAT_` -> `JOBCRAT_`; R2 the word `crat` -> `jobcrat`; R3 `crat_` -> `jobcrat_`; R4 `_crat` -> `_jobcrat`;
  R5 the word `Crat` -> `Jobcrat`; R6 `__crat_` / `__CRAT_` -> `__jobcrat_` / `__JOBCRAT_`. `crate`-family words and
  `CRAT` alone are untouched (`rename.py untouched` lists them). The binary and the wrapper are renamed.
- **E. String edits.** `edits.py`: host names, dated and numbered process ids and label strings become neutral; the
  `reason = "..."` arguments of lint attributes go (`strip_reasons.py`). `kit_edits.py` runs only when a kit copy is
  in the tree (it is not, since the user's ruling); `HASH_REPOS`: every hash-like token is resolved against our repositories.
  `allow_warnings.py`: `#![allow(warnings)]` after the last inner attribute of every crate root, so the zip builds
  without warnings (the trims leave dead code behind).
- **F. Build and checks.** `cargo build --release` of the derived tree; the lockfile as cargo resolved it, header
  stripped. The checks printed: the old names (0), the identity grep (0; the crates.io registry URL in lockfiles is
  exempt), commit hashes of our repositories (0), process fingerprints in Rust sources (0), comments left (0), list-2 words in string literals (0), and
  `evaluation/` files in the tree (0).
- **The zip.** `mkzip.sh`: the tree under `jobcrat-source/`, zipped in sorted order with Python's zipfile; unzipped
  and compared with the staged copy; `cargo build --release --locked` from the unpacked zip.

## The smoke

`smoke.sh` builds `deps_crate` from the unpacked zip, runs `jobcrat -v --pass translate` on each program (avl and
bst by default) and compares every emitted `.rs` file with the tree of record, byte for byte or modulo rule R6.
