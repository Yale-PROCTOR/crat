# rq3/ — Table miri and the shipped test suites

`rq3/run_rq3.sh <trees> <substrate> <out> [--small] [--cap SECONDS] [--jobs N] [--tools ours,crown,laertes]` (the artifact's `run.sh rq3` calls it with `results/trees results/substrate results/rq3`) runs two things, both on the emitted trees:

- **The shipped test suites, natively.** These are the six programs of CROWN's benchmark that ship a suite: buffer, genann, libtree, quadtree, rgba, urlparser.
  - libtree's suite is nine `make check` directories.
  - Each of the other five suites is one test program built with the library; every assert must hold.
- **Miri under Tree Borrows on five of them.** These are buffer, genann, libtree, quadtree and rgba. urlparser is left out because its C original has an out-of-bounds access of its own.
  - The run covers our translations.
  - With `--tools ours,crown,laertes` it also covers CROWN's and Laertes's, read from `results/third-party/` (`third-party/run.sh`).

It writes:
- `results/rq3/keys.txt`: one `key = value` line per key Table miri and the test line cite. `../compare.py` sets them against `../expected.tsv`;
- `results/tables/miri.csv`, `results/tables/miri.tex`: the table, and its keys as the paper's `numbers.tex` rows;
- `results/rq3/native-suites.txt`, `results/rq3/native/`: the native runs;
- `results/rq3/miri/<tool>/`: one Miri run per program. `<p>/miri-runs-emitted-TB.tsv` holds each run's first report, `runs-emitted/<input>/miri-std{out,err}` its output, and `proj-emitted-<input>/harness-edits.txt` the edits applied.

## The Miri configuration

- **Miri:** the `miri` of `nightly-2026-09-17` (rustc `1.100.0-nightly (923c95cdf 2026-09-16)`), with `rust-src`. Override with `MIRI_TOOLCHAIN`.
- **Flags:** `-Zmiri-tree-borrows -Zmiri-disable-isolation -Zmiri-ignore-leaks`, plus `-Zmiri-address-reuse-rate=0` with the extents below; every crate is built with `panic = "abort"`.
- **The slice lengths.** The translator gives a slice whose length it cannot infer an arbitrary bound (`FALLBACK_SLICE_EXTENT`). Before the run, `harness/miri_oracle.py` replaces each such construction by the allocation's real extent, read from an allocation registry the harness adds (array-bound inference is outside the translator's scope).
- **The input defects.** `repairs.tsv` declares the fixes of defects already in the C2Rust translations: libtree's four sites (rows) where C2Rust builds a raw pointer through a reference (`&mut x as *mut T`, `.as_mut_ptr()`) become `&raw mut x`, and genann's test closes a stream twice. They are applied identically to every tool's tree, but only where the tree kept the C2Rust text; the receipts say where they applied. The C2Rust text is the prepared input in `results/substrate/<p>`. The applying code is `harness/miri_repair.py`.
- **The time limit:** `--cap` / `MIRI_CAP`, in seconds per run (default 28,800, the paper's eight hours). Our genann does not finish within it: its cell counts the run with no UB found, as the paper's dagger says. CROWN's genann finishes within it (6,904 s in the paper's measurement).

## The table's cells

| cell | how it is read |
|---|---|
| Runs | the test cases executed: libtree 9, the others 1 |
| UB | the runs whose first Miri report is `Undefined Behavior` |
| `aborts` | the program stopped without UB: an assertion failure, or a call to a function Miri cannot run (`unsupported operation`) |
| `does not compile` | the tree does not build |
| `no main` | the test's module has no `main` function |
| `error` | Miri exited without a report (for libtree: a test failed with no Miri report), so the run did not happen, e.g. no Miri sysroot; `compare.py` then reports the key as differing |

## `--small`

- **Skipped:** genann on our translation and on CROWN's, the two longest runs. Ours runs to the eight-hour cap; CROWN's finishes in about two hours. Their keys are written `skipped (--small: 8 h cap)`.
- **Still run:** everything else, the native suites and Miri on the other programs. This takes minutes.

On a slower host our genann may complete fewer of its test groups before the cap; its cell (runs 1, no UB) does not change. CROWN's genann reaches the cap only on a host about four times slower than the paper's (28,800 s against 6,904 s).

## The harness

`harness/` is the measurement harness, cut to the six programs; otherwise only its paths (the artifact's roots) and the names of the translator's helpers are changed. It contains:
- `miri_census.py`: one Cargo project per program and run, then the Miri run and its first report;
- `miri_oracle.py`: the extents;
- `miri_repair.py`: the declared repairs;
- `jobcrat_libc_models.rs`: models of the C library functions Miri has no shim for (`sscanf`, `strdup`, …), compiled into each project;
- `libtree_suite.py`: libtree's nine `make check` runs, each reaching the Miri project through a wrapper;
- `runtime_census.py` + `six_suites.py`: the native runs;
- `rust_scan.py`: a helper (the function that owns a source line).

`lib/flatten.py` turns a multi-file tree (CROWN's, Laertes's) into one crate root, as ours are. `lib/rq3.py` drives the steps and reads the results.

Needs: `python3`, `gcc` and `make` (libtree's suite builds small ELF fixtures), the translator's toolchain `nightly-2025-06-23` with `deps_crate` built (the native runs), and the Miri toolchain above with `cargo miri setup` done.
