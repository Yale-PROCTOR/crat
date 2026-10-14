# evaluation/ -- reproducing the paper's evaluation

This directory is the kit for the paper's three research questions. It holds the scripts, drivers, configuration files and per-program inputs that turn a checkout of `borrow-ownership` at the final head into the numbers the paper prints, given the external artifacts listed in `MANIFEST.md`. It holds no outputs.

- **What it is not.** `evaluation/` is not built by the workspace, and it is not in the submission source zip.
- **Where the code of record is.** The tool is the code at `32d966b9f` (60s′). The environment of record is `crates/pointer_replacer/frames/l01p14u-s39-mutlend-o-env.sh`, referenced here, not copied.
- **Reports.** A plain report number is the analysis lane's (`agents/reports/analysis-fanout/` in the documentation repository); another lane's report is named with its lane.

## 1. The map: research question → table → keys → directory, in the order of the steps

### The steps

0. **Frame-independent work, any time.** None of this needs our tool:
   - the input, CROWN and Laertes sides of the counters: `positions-uses/run_nobuild.py --side input|crown|laertes`, `positions-uses/run_t5.py input|crown|laertes`, `declarations/` (CROWN's declaration counter);
   - `setup/sloc104.py`;
   - the CROWN and Laertes timings (`crown-laertes/`);
   - &inator's runs (`inator/inator/`) and its type counter (`inator-types/`);
   - the C line counts (`inator-types/manifest.py`);
   - Miri on CROWN's and Laertes's trees (`runtime/`).
1. **Substrate** (`pipeline/substrate/`, main): `benchmarks/rs-crown` → `benchmarks/rs-crown-derived` (expand → extern → preprocess).
2. **Solve** (`pipeline/solve/`, era-5c):
   - build the release test binary;
   - source the environment of record and launch the solve of record (`launch/`), which writes the model cache;
   - check the frame (`frame/`): analysis `1d8dcd40`, configuration `d9a474da`, launch `2e94d9a5`;
   - the serial timing run (`timing/`) re-solves the same models one program at a time, for Table scale-crown.
3. **Emission** (`pipeline/emit/`, main): the cache-only census writes `emitted-trees/<p>`, with the exposure lists, the compile check, the custody check and the count.
4. **Counters** over the emitted trees:
   - `positions-uses/` and `declarations/` (`--side ours`, the twin readings);
   - `rq3-trials/` or `inator/ours/` (our trials of the nine, which run steps 1–3 on each) → `inator-types/ours.py`;
   - `runtime/` (the six suites and Miri);
   - `setup/seed_g5.py` and `analysis-waivers/` (reading the solve's cache).
5. **Record** (`record/`): the seeders turn the counters' outputs into rows of `numbers-of-record.md`, and the paper's `scripts/gen_numbers.py` writes `numbers.tex`. `record/README.md` gives the row format and the check.

### RQ1 — effectiveness (steps 0–5)

| table / text | keys | directory (step) |
|---|---|---|
| Table effect-all (every declaration; uses) | `setup.<p>.sloc`, `setup.sloc` | `setup/sloc104.py` (0) |
| | `rq1.<p>.alldecl.{before,rate}`, `rq2.<p>.alldecl.{crown,laertes}`, totals | `positions-uses/run_nobuild.py` (0, 4) → `alldecl945.py` |
| | `rq1.<p>.uses.{before,rate}`, `rq2.<p>.uses.{crown,laertes}`, totals | `positions-uses/` `rq2_pos_counter` via `run_nobuild.py` (0, 4) |
| Table effect-crown (CROWN's population) | `rq1.<p>.decl.before`, `rq2.<p>.decl.{crown,laertes}`, `rq2.total.decl.{crown,laertes}-rate` | `declarations/decl_driver` + `compute.py` (0) |
| | `rq1.<p>.decl-twin.rate`, total | `declarations/decl_twin.py` (4) |
| | `rq1.<p>.decl-uses.before`, `rq2.<p>.decl-uses.{crown,laertes}`, totals | `positions-uses/run_t5.py` (0) |
| | `rq1.<p>.decl-uses-twin.rate`, total | `positions-uses/run_t5.py ours` + `decl_uses_twin.py` (4) |
| Table effect-inator (&inator's nine) | `rq3.inator.<q>.types.{pos, inator.static, inator.dynamic, inator.other}` | `inator/inator/` runs (0) → `inator-types/` |
| | `rq3.inator.<q>.types.ours.{safe,raw}` | `inator/prep/` (c2rust) → `inator/ours/` or `rq3-trials/` (4) → `inator-types/ours.py`, `pairs.py`, `rebucket2.py` |
| the text's totals, the introduction | `rq1.total.*`, `rq2.total.*`, `rq1.total.alldecl.{delivered,before}` | the same counters' totals (§2's rule) |

### RQ2 — scalability (steps 0–2, 4)

| table / text | keys | directory (step) |
|---|---|---|
| Table scale-crown (the twenty) | `rq3.<p>.analysis-s`, `rq3.total.analysis-s`, `rq3.largest.analysis-s` (brotli) | `pipeline/solve/timing/` (2) → `rq3-trials/rq3times146.py` |
| | `rq3.<p>.{crown-s,laertes-s}`, totals | `crown-laertes/` (0) |
| Table scale-inator (the nine) | `rq3.inator.<q>.loc` | `inator-types/manifest.py` (0) |
| | `rq3.inator.<q>.host-s` | `inator/inator/` (0; tisp from the source build) |
| | `rq3.inator.<q>.total-s` | `inator/ours/` (4; the driver of record) |

### RQ3 — soundness in practice (steps 1–4)

| table / text | keys | directory (step) |
|---|---|---|
| the compile-and-tests line | every emitted program compiles (no key) | `pipeline/emit/` compile check (3) |
| | `rq1.tests.suites.programs` | `runtime/` (4) |
| Table miri (the six suites under Miri) | `rq4.suite.<p>.*`, `rq4.suite.total.*` | `runtime/` (4) |
| | `rq4.suite.{crown,laertes}.<p>.{runs,ub}` | `runtime/` (0) |

### Setup and threats

| keys | directory |
|---|---|
| `setup.programs` | `record/seed_numbers.py` |
| `setup.solver`, `setup.depth.third-level-slots` | `setup/seed_g5.py` (4) |
| `setup.host` | by hand: `lscpu` / `lsmem` (report 102) |
| `setup.rustc` | `rust-toolchain.toml` |
| `analysis.release-sites.opaque-origin` | `analysis-waivers/release_sites.py` (4) |
| `design.fallback-slice-extent` | the census's override `CRAT_FALLBACK_SLICE_EXTENT=268435456` (R693-1; the code's default constant is 1024) |

## 2. The counters (this lane's directories)

The scripts take their main inputs as arguments. Other inputs are read at paths relative to the current directory, named in the table; run from a directory where they resolve (links are enough):
- `scratch/main/<census>/`: a census's output, e.g. `batch60sp/` with `emitted-trees/`;
- `crat/`: this repository, with the documentation repository checked out at `crat/docs/`;
- `crown-artifact/`: CROWN's artifact;
- `worktrees/<solve>/`: a solve and its model cache;
- the earlier counter outputs the table names under `scratch/analysis-fanout/`.

`pos_census.py`, `decl_walker_vs_census.py` and `setup/sloc104.py` read `record/seed_numbers.py`.

| keys the paper prints | counter | how to run it | inputs | report |
|---|---|---|---|---|
| `rq1.<p>.uses.{before,rate}`, `rq2.<p>.uses.{crown,laertes}`, their totals (Table effect-all, uses); the per-side `positions.tsv` also feeds `alldecl945.py` | `positions-uses/pos_counter/` (`rq2_pos_counter`: T1 pointer layers, T2 per-function uses), driven by `positions-uses/pos_census.py` | build `pos_counter` (`cargo build --release` with its `rust-toolchain.toml`, target `POS_TARGET`); `python3 positions-uses/run_nobuild.py run --side {input,ours,crown,laertes} --out DIR [--census scratch/main/<census>]`, then `run_nobuild.py summarize --out DIR` (`pos_census.py run` builds the counter itself through `crat/docs/agents/tools/crat-cargo.sh`; `pos_census.py calibrate` reads `docs/agents/tasks/2026-07-28-crown-usage-metric-candidates.csv` under `seed_numbers.CRAT`, which must name this repository). `seed_rq2.py` supplies `laertes_root()`; its own `main()` seeds the documentation repository's record and is not needed here. Rules: `uses.before` = the input's T2 `full_roots`; `uses.delivered` = before - the output's; `rate` = delivered / before. (The T1 `pos.*` keys this counter also writes are no longer cited, S70.) | the emitted tree (ours: `<census>/emitted-trees/<p>`), `crat/benchmarks/rs-crown/<p>`, CROWN's `rs-crown-transformed/<p>`, the artifact's Laertes trees (`seed_rq2.laertes_root`) | 031, 094 |
| `rq1.<p>.alldecl.*`, `rq2.<p>.alldecl.{crown,laertes}` (Table effect-all, every declaration; safe = its outermost pointer layer safe) | `positions-uses/alldecl.py` (the rule) + `alldecl945.py` (R945-1: CROWN's counter in full) | `TREES=scratch/main/<census>/emitted-trees OURSDIR=<run_nobuild out>/ours CTL_DECLS=<a control run's decls/> python3 positions-uses/alldecl945.py` (the control: every strict verdict must equal that run's `decls/<side>-<p>.tsv`; the run of record used batch 56's alldecl) (writes `decls/<side>-<p>.tsv` and `per-program.json` beside itself) | `positions.tsv` per side, read at `scratch/analysis-fanout/r065/out/<side>/<p>/`, `r117/out/laertes/libzahl/`, `r116/t5/out/laertes_before/` | 095, 115 |
| `rq1.<p>.decl-uses.before`, `rq1.<p>.decl-uses-twin.rate`, `rq2.<p>.decl-uses.{crown,laertes}` (Table effect-crown, uses, over CROWN's population) | `positions-uses/run_t5.py` (`rq2_pos_counter` keyed to CROWN's universe = its `fn_data` d0 Mut and Ptr keys), `decl_uses_twin.py` (the twin reading); `adapt_llvm_asm.py` adapts libzahl's Laertes tree | `python3 positions-uses/run_t5.py SIDE [PROG...]` (writes `scratch/analysis-fanout/r146/trees/t5/out/<side>/`); `python3 positions-uses/decl_uses_twin.py SIDE`. Rules: `before` = the input's `official` count (CROWN's usage rule); `delivered` = before - the output's `official_raw` (negative when the output has more raw uses, never clamped); `decl-uses-twin.rate` = delivered / before | as above, plus CROWN's `analysis_results/` | 094, 100 |
| `rq1.<p>.decl.before`, `rq1.<p>.decl-twin.rate`, `rq2.<p>.decl.{crown,laertes}`, `rq2.total.decl.{crown,laertes}-rate` (Table effect-crown, declarations) | `declarations/decl_driver/` (`rq2_decl_driver` = CROWN's declaration counter) + `r945.py` / `srcscan.py` / `compute.py` (R945-1); `decl_twin.py` (the twin reading) | build `declarations/decl_driver` (`cargo build --release`, nightly-2023-01-26 with rustc-dev); `RECORD=<numbers-of-record.md> python3 declarations/compute.py` (reads `run_t5.py`'s outputs); `python3 declarations/decl_twin.py <census> <out>`. Rule: `rate` = the declarations of CROWN's population whose binding is no longer a raw pointer / the population | the emitted tree, CROWN's `analysis_results/`, `crown-artifact/comparison/` | 015, 030, 115 |
| `rq3.inator.<q>.types.{pos, inator.static, inator.dynamic, inator.other, ours.safe, ours.raw}` (Table effect-inator) | `inator-types/` | from inside `inator-types/` (the scripts read and write the current directory), holding `inator-outputs/` (&inator's results: `{img,diag}/runs/<p>/trial-1/...`) and `c2rust-out/` (the c2rust translations of the nine): `python3 run_inator.py && python3 reconcile.py` (= `reconcile.json`), `python3 rebucket.py`, `python3 ours.py <run-root> ours-positions.tsv`, `python3 pairs.py ours-positions.tsv`, `python3 rebucket2.py pairs.tsv`. Rule: per position, dynamic if any level of &inator's type is reference-counted or interior-mutable, unknown if its type is `unknown`, else static; ours safe = reference / mutable reference / box; the values are `rebucket2.py`'s with-fields line (`all`) | &inator's `rtypes.txt` / `stypes.txt` (`inator/inator/`'s runs); our census of the nine (`<run-root>/prep/<p>/census-t1`, where `<run-root>` is the `RQ3_OUT` of `rq3_trials.py prep` and `trial` over the nine: `inator/ours/` or `rq3-trials/`; the run of record's copy differed only in mapping the solve job's z3 library directory to the host's) | 119, 124a, 129 |
| `rq3.inator.<p>.loc` | `inator-types/manifest.py` (cloc code lines over each benchmark's .c / .h) | `python3 inator-types/manifest.py GH_BENCHMARKS_DIR ZENODO_BENCHMARKS_DIR CLOC_PL OUTDIR` | &inator's benchmarks; cloc 2.00 | 016 |
| `rq3.inator.<q>.total-s` (Table scale-inator, ours) | `rq3-trials/rq3_trials.py` (`solve_busy.py` its lock helper); the run of record used rq3-inator's copy, now `inator/ours/rq3_trials.py`, which differs in its root path, tolerates a missing `SLOT-FREE` marker, checks that the model-cache entry of record is available on the host (`rec_avail`), takes z3's library from the release's `bin/`, and screens out the driving agent's CLI by name | `RQ3_ROOT=<dir with c2rust-out/ and bin/> python3 rq3-trials/rq3_trials.py prep PROG`, then `trial PROG N` (or `run PROG...`). Rule: per trial the sum of its three stages; the value = the minimum over trials | `c2rust-out/` of the nine, release `crat` / `pointer_replacer` (`RQ3_CRAT`, `RQ3_BIN`), the solve's job environment; relative to the current directory, the nightly-2025-06-23 toolchain at `home/.rustup/toolchains/nightly-2025-06-23-x86_64-unknown-linux-gnu` and z3 4.15.4.0's library at `home/.local/opt/z3-solver-4.15.4.0/z3/lib`; with `RQ3_IDLE=1`, the run-window marker `scratch/main/SLOT-FREE`. `RQ3_SKIP_EXE` names a process the memory screen ignores (default: none) | 017, 018 |
| `rq3.<p>.analysis-s`, `rq3.total.analysis-s`, `rq3.largest.analysis-s` (Table scale-crown, ours; largest = brotli, the largest program) | the serial release timing run (`pipeline/solve/timing/run_serial.py`: one program at a time, the release test binary, the same models as the solve of record) writes each program's `wall_s`; `rq3-trials/rq3times146.py` reads it back (the last complete record per program) | `python3 rq3-trials/rq3times146.py <the timing run's directory>` | its `progress.jsonl` and `workers/<p>.json` | 104, 128; era-5c 174 |
| `rq3.<p>.{crown-s,laertes-s}`, `rq3.total.{crown-s,laertes-s}` (Table scale-crown) | `crown-laertes/` | `bash crown-laertes/run-all.sh` (CROWN, image `crown:latest`; it also runs a Laertes pass through `laertes-one.sh` that is not of record, inputs `IN=`); `python3 crown-laertes/prep_laertes2.py` (no arguments) then `bash crown-laertes/run-laertes2.sh` (Laertes of record, image `aliasing-limits-oopsla23:final`; inside the container the scripts use the image's `~reviewer/artifact`, or `LAERTES_ARTIFACT` when set there); `python3 crown-laertes/tables.py`. Rule: per program the minimum wall over 3 trials; Laertes timed only where it completes. The scripts write `in2/`, `out/`, logs beside themselves | the two images; `crown-artifact/comparison/laertes-{crown,laertes}/before/<p>`; GNU time 1.7 (Ubuntu bionic's `time` package) at `crown-laertes/bin/time-bionic` for the Laertes image; the run-window guard `guard.py` reads `scratch/main/SLOT-FREE` (an empty file is an open window on an idle host) and `worktrees/CORPUS-SLOT*.lock` | 122, 123 |
| `setup.<p>.sloc`, `setup.sloc` | `setup/sloc104.py` (+ `frac_lib.py`) | `python3 setup/sloc104.py <trees root> <out.json>` | the twenty input trees | 080 |
| `setup.depth.third-level-slots`, `setup.solver`, `setup.host` | `setup/seed_g5.py` (+ `model_head.py`) | `python3 setup/seed_g5.py <census-dir> <solve-dir>`. The printed `setup.host` (CPU model, cores, memory) is read by hand with `lscpu` / `lsmem` (report 102); `seed_g5.py` writes the `/proc` form | the census; the solve and its model cache; the documentation repository at `crat/docs` (origin/main) | 088, 102 |
| `analysis.release-sites.opaque-origin` | `analysis-waivers/release_sites.py` | `python3 analysis-waivers/release_sites.py` | the solve of record's model-cache entries, `MODEL_CACHE` (default `worktrees/era5c-r215-kindorder/cache/era5b-model-cache-v1`); read by mmap in windows, never whole | 039, 127 |

Totals (`rq1.total.*`, `rq2.total.*`, the only aggregates the paper prints): a total count is the sum over the twenty programs, and a total rate is the summed delivered over the summed before. It is pooled, not a mean of rates, and a negative per-program delivered is summed as is. Laertes has no output for brotli, so the Laertes totals (`rq2.total.*.laertes`, `rq2.total.decl.laertes-rate`) count brotli as 0 delivered over the twenty (R891-1), as CROWN's Table 2 does.

**The other lanes' directories** (each with its own README):

| directory | lane | what |
|---|---|---|
| `pipeline/substrate/` | main | the derived substrate |
| `pipeline/solve/` | era-5c | `launch/` (the solve of record), `frame/` (the frame check), `timing/` (the serial release timing, `run_serial.py`; era-5c 174 / 175) |
| `pipeline/emit/` | main | the census runner, the exposure lists, the compile check, the custody check, the count |
| `runtime/` | wave-6o | the six suites, the Miri harness and its drivers, the repair list, CROWN's and Laertes's tree preparation (wave-6o 156) |
| `inator/` | rq3-inator | `prep/` (the c2rust fork), `ours/` (our trials of the nine, the driver of record), `inator/` (&inator's image runs and the tisp source build) (rq3-inator 022) |
| `record/` | analysis-fanout | the seeders and the record's row rules |

Still cited, not in this kit: `crates/pointer_replacer/tools/crown_usage_metric/` (in this repository; the calibration of `rq1.<p>.decl-uses.before`); `setup.rustc` and `design.fallback-slice-extent`, which are constants.

## 3. What is not in the repository

| what | where it is named | how it is made |
|---|---|---|
| the twenty inputs `benchmarks/rs-crown/<p>` (gitignored) and CROWN's outputs `benchmarks/rs-crown-transformed/<p>` | `MANIFEST.md` 17 | copied from CROWN's artifact (`MANIFEST.md` 1); `crown:latest` reproduces the outputs |
| the derived substrate `benchmarks/rs-crown-derived` | `MANIFEST.md` 17 (tree digest `db96829b…`) | step 1 |
| the model cache of the solve of record | `MANIFEST.md` 19 | step 2 (hours; the serial timing run alone is about 2.6 h on one core). The worker admits a job only on a host named in its host list (`model_cache::WORKER_HOSTS`, an identity field), and the jobs seal absolute paths: era-5c 175 §4 states what a reproducing host needs |
| the census output and the emitted trees (`batch60sp`) | the batch-60s′ landing record | step 3, cache-only |
| the images: CROWN, Laertes, &inator (artifact and source build), the c2rust fork | `MANIFEST.md` 2–5, 7 | `docker load` from the artifacts; the c2rust and tisp images are built from their Dockerfiles |
| the toolchains and tools: Rust nightlies, Miri, Z3, cloc, GNU time | `MANIFEST.md` 8–16 | rustup, the releases named there |
| the C reference runs for the input-UB control | `MANIFEST.md` 20 | the native census (`runtime/`) |
| the record `numbers-of-record.md` and the documentation repository's reports | the documentation repository (`paper/`, `agents/`) | `record/` writes the rows |
| the paper and `scripts/gen_numbers.py` | the paper repository | -- |
