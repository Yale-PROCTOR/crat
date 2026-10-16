# rq1/ — Tables effect-all, effect-crown and effect-inator

`rq1/run.sh [--small]` counts the emitted trees (`results/trees/<p>`) and the inputs (`benchmarks/`). It writes:
- `results/rq1/keys.txt`: one `key = value` line per key the tables cite;
- `results/tables/effect-{all,crown,inator}.{csv,tex}`: the `.tex` files hold the paper's `numbers.tex` rows.

The comparison columns (CROWN, Laertes, &inator) need `third-party/run.sh` to have run first.

## The counters (built once by `build.sh`; `run.sh` builds them when missing)
| counter | what it is | reads |
|---|---|---|
| `counters/typed/` → `typed_counter` | a rustc driver on nightly-2025-06-23 | One crate per call, compiled with the translator's own configuration (`deps_crate`'s rlibs, found through `$SRC`). It writes T1 (`positions.tsv`: every pointer layer of every declaration, with its form) and T2 (`uses.tsv`: raw-pointer uses per function; CROWN's usage rule over its population) |
| `counters/decl/` → `decl_counter` | CROWN's own declaration metric (the inventory library from CROWN's artifact, vendored in `inventory/`) | Run on CROWN's twenty outputs. It must reproduce CROWN's evaluation table 20 / 20 before any key on CROWN's population is written (`results/rq1/counter/crown-control.txt`) |

## What each table needs
| table | keys | needs |
|---|---|---|
| effect-all | `rq1.<p>.{alldecl,uses}.{before,rate}`, `rq2.<p>.{alldecl,uses}.{crown,laertes}`, `setup.<p>.sloc`, the totals | Ours and before: only the trees and `benchmarks/crown`. CROWN / Laertes: their distributed trees (`third-party/run.sh trees`) |
| effect-crown | `rq1.<p>.{decl,decl-uses}.before`, `rq1.<p>.{decl-twin,decl-uses-twin}.rate`, `rq2.<p>.{decl,decl-uses}.{crown,laertes}`, the totals | The mutable non-array population is CROWN's own, so this table needs `third-party/run.sh crown` (its outputs with `analysis_results/` and its evaluation table) |
| effect-inator | `rq3.inator.<q>.types.{pos,ours.*,inator.*}`, `rq3.inator.<q>.loc` | Ours: the eight's trees and `data/inator-positions.tsv` (the 311 positions &inator's outputs and the translation share, as bare identities). &inator's columns: its outputs (`third-party/run.sh inator`); the join is recomputed then and must equal the shipped list. `loc`: the eight's C sources and `cloc` 2.00 |

The definitions are in `lib/measure.py` and `lib/inator_types.py`.
- **Ours** is read through the exposure twin: `__jobcrat_safe_f` stands for `f`.
- **Totals** are pooled (summed delivered over summed before).
- **Laertes** has no output for brotli. Its cells are 0.0 %, and brotli counts 0 in the Laertes totals.

## `--small`
- **Our side:** lil and brotli are not translated, so their four ours rates and the four pooled ours totals are written `skipped (--small)`. Everything else is counted on all twenty, because the input / CROWN / Laertes sides take seconds.
- **&inator:** under `--small` it runs on five of the eight, so the other three programs' &inator columns are skipped.

## Expected values
`../expected.tsv` holds every key the paper cites, as the paper prints it. `../compare.py` writes `results/compare.txt`:
- counts and rates must be `equal`;
- times are `reported` with their ratio to the paper's.

`../expected-trees.tsv` lists the sha256 of every file of the distributed CROWN and Laertes trees the counts read, relative to `results/third-party/`.
