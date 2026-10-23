# packaging/ -- deriving the artifact-evaluation source zip from the frozen source

This directory derives the artifact-evaluation source zip (the translator under the paper's name, `jobcrat`, with
`artifact/` and `benchmarks/`) from the source the paper evaluated, `borrow-ownership@b0eb75189` (R1265-3: the AE
looks only at that source; nothing on `borrow-ownership-to-master` feeds it). The derivation is the cleaning (R1265-1:
no internal development test, fixture, measurement driver, development switch or hook in the AE's source): the owners'
patches, the removals, the test cut, option 3A, the compiler's dead code, the unused dependencies, the comment strip,
the rename and the string edits. It prints the counts of that bar, and every one of them, with every grep, must be 0
before a zip is made. The plan of record is crat-packaging report 025 (accepted R1272-2). `evaluation/` is excluded
from the zip, except `evaluation/docker/` (taken from `ARTIFACT_REV`, the kit's commit on the lineage), which becomes
the zip's `artifact/`.

## Running

```
bash evaluation/packaging/rederive.sh <head> <tag>        # -> $SCRATCH/jobcrat-source.zip, rederive.log, branch rederive-<tag>
DRY_RUN=1 bash evaluation/packaging/rederive.sh ...       # hits and counts under $SCRATCH/hits/, the derived tree built, no zip
LEGACY_SEARCH=1 bash evaluation/packaging/rederive.sh ... # option 3A's list made again by the compiler ($SCRATCH/legacy-cut.txt)
REF=<sha256sum list> bash evaluation/packaging/check-trees.sh <tag> [program ...]   # the output check (below)
bash evaluation/packaging/smoke.sh <tag> [program ...]    # the driver from the unpacked zip on avl and bst
```

Needs the pinned toolchain (`rust-toolchain.toml`), the solver and libclang variables the top-level README names,
python3 >= 3.11 and `unzip`. Two inputs are required, because the evaluation's inputs are not in the repository:
`BENCH` (a zip whose `jobcrat-source/benchmarks/` holds them, or a directory laid out as `benchmarks/`) and
`BENCH_SHA256SUMS` (the SHA-256 of its `SHA256SUMS`; the derivation stops unless it matches, every file checks and none
but `README.md` is unlisted). The other parameters are listed at the top of `rederive.sh`.

## The derivation, one commit per step on the branch `rederive-<tag>`

1. **The worktree** at `<head>`; `config/analysis-env.sh` = the environment of record's exports, less the toolchain's
   names and the five no reader takes once `patches/20-` is applied (the execution role, the two recipe digests, the
   raw-cause ledger and its budget) (`CONFIG_DROP`).
2. **The owners' patches** (`patches/NN-<lane>-<topic>.patch`, against `<head>` in its own paths and names), in name
   order with `git apply --index`; one that does not apply stops the derivation. Each patch names its survey rows in
   its header; its owner builds `<head>` with it applied as their own check.
3. **Removals:** development files, `examples/`, `evaluation/`, `LICENSE`, `frames/`, the tools directories, the crates
   and passes the shipped passes do not use, the other binaries, test files and directories, `dev-dependencies`; the
   observed-alias table (`observed_out.py`). `BENCH`'s `benchmarks/` becomes the zip's `benchmarks/`, byte for byte;
   `ARTIFACT_REV`'s `evaluation/docker/` becomes `artifact/`. The driver is `driver-template.crat.rs` (the passes
   `prepare`, `translate`, `check`; `--bo-receipt`; no switch-file loader: `artifact/run.sh` exports
   `config/analysis-env.sh`, a variable already set winning, as the loader did), the README `README-template.md`.
4. **Tests.** `tools/cfgcut` deletes every `#[cfg(test)]` item by byte range (syn); `reach.py` walks the `mod`
   declarations from the crate roots (`modscan.py`), removes unresolved test modules and the orphans; unreferenced data
   files go.
5. **Option 3A** (`legacy_search.py`, item cuts `option3.py`): the legacy rewriter keeps
   `collector::collect_fn_ptrs`, `diagnostics::DiagnosticsMode` and `Config`; then the compiler decides which module
   subtrees of `pointer_replacer` (the pointer pass's own modules excepted, `SEARCH_SKIP`), `passes`, `points_to` and
   `utils` ship: each is removed in turn, top-down, and the removal kept when `cargo check` reports no error, until a
   round removes nothing. The removals are frozen into `legacy-cut-<head>.txt`; every derivation applies the list and
   its release build re-proves it.
6. **The compiler's dead code** (`deadcut.py`, `tools/itemcut`), to a fixpoint: `cargo fix` applies the compiler's
   machine-applicable suggestions (unused imports and extern crates, `mut`, unused variables), the sources touched
   first (a crate the last check left fresh has its warnings replayed from the cache, and nothing fixed); every item a
   `dead_code` or `unused_macros` warning names is cut with its attributes (a type or trait with its impls in the same
   file); `--force-warn` makes the lints fire where an `allow` attribute would hide them. A set of cuts that does not
   check is undone and made again by halves; an item that failed is tried again with the others that failed, one by
   one only in a round that otherwise changes nothing. Fields never read and variants never constructed stay (listed in
   `deadcut-left.tsv`; their owners' patches), as do the cuts that never check (`deadcut-failed.tsv`).
7. **Unused crate dependencies** (`-W unused_crate_dependencies`) leave every manifest; the lock follows.
8. **The comment strip** (`tools/rslex strip`; `strip_misc.py` for TOML) and the `reason = "..."` of lint attributes.
9. **The rename** (`rename.py`): R1 `CRAT_` -> `JOBCRAT_`; R2 the word `crat` -> `jobcrat`; R3 `crat_` -> `jobcrat_`;
   R4 `_crat` -> `_jobcrat`; R5 the word `Crat` -> `Jobcrat`; R6 `__crat_` / `__CRAT_` -> `__jobcrat_` / `__JOBCRAT_`;
   then R7 and on, the rules of `rename-rules.tsv` (the internal names' identifier renames, once worded), applied to
   the text and to the paths. The binary and the wrapper are renamed. Then the string edits (`edits.py`).
10. **Checks and counts.** The compiler's warnings as the sources stand (`warnings.py`; `#![allow(warnings)]` at a
    crate that still warns), the release build, the lockfile. Over the whole tree but `benchmarks/`: the identity
    grep, the provenance grep, the forbidden names (`FORBIDDEN`, `FORBIDDEN_RE` less `FORBIDDEN_EXEMPT`; the lines
    `FORBIDDEN_ALLOW` lets through are counted), commit hashes of our repositories, `cfg(test)` left, comments left;
    `counts.py`: test files, measurement drivers, environment names off the record, `artifact/` hooks. A hit or a
    count above 0 stops the derivation before the zip; `DRY_RUN=1` lists them under `$SCRATCH/hits/` instead.
11. **The zip.** `mkzip.sh`: the tree under `jobcrat-source/`, zipped in sorted order; unzipped and compared with the
    staged copy; `cargo build --release --locked` from the unpacked zip.

## The output check

`check-trees.sh` runs the derived translator on the programs (default: the `--small` ones) exactly as `artifact/run.sh`
does (prepare, a copy, translate in place; the configuration exported by `run.sh`'s own `analysis_env`; the
evaluation's two variables) and checks every emitted file against `REF`, a `sha256sum` list of the reference trees (the
interim zip's full run, `f3-trees.sha256`). Every edit leaves the output unchanged: each patch set is checked this way
before the next.
