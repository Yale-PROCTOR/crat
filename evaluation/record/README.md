# evaluation/record/ -- how a measured value becomes a key of `numbers-of-record.md`

The manuscript never carries a literal number. Every quantity is a key, `\nr{key}` (or `\nrt{key}` / `\nrlayer{key}`), resolved through the paper's generated `numbers.tex`. That file is written by the paper repository's `scripts/gen_numbers.py` from one Markdown table, `paper/numbers-of-record.md` in the documentation repository. This directory holds the tools that write rows into that table from the counters' outputs (`../README.md` §2).

## The row

```
| key | value | status | layer | unit | provenance |
```

| cell | rule |
|---|---|
| `key` | `[A-Za-z][A-Za-z0-9._-]*`, unique in the table. The families are `rq1.<p>.*` / `rq2.<p>.*` (one row per program), `rq1.total.*` / `rq2.total.*` (pooled over the twenty: summed delivered over summed before), `rq3.<p>.*`, `rq3.inator.<p>.*`, `rq4.suite.*` and `setup.*`. |
| `value` | As printed: a count, a percent with one decimal (`40.9%`), seconds with one decimal, or a short status text (`blocked`, `—`). `gen_numbers.py` escapes TeX specials, so a value cannot carry TeX. A print form such as `$2^{28}$` lives in the paper's `scripts/provisional-overrides.tsv`, which applies to `pending` rows only. |
| `status` | `pending`: written, not yet of record. `measured`: of record. `superseded`: kept for history. A `measured` row with an empty value or an empty provenance makes the generator abort. |
| `layer` | `decided` / `delivered` / `both` / `n/a`. The paper prints it as a superscript label. |
| `unit` | Free text, informational: `count`, `percent`, `seconds`, `text`. |
| `provenance` | What measured the value: the counter, its input (the census, the solve, the tool's trees), the frame, the report that wrote the row. A later writer PREPENDS its phrase (e.g. `measured at 60s' (R1115-1, …):`) and keeps the old text whole, so a row reads newest first. |

**Pending to measured.** A seeder writes `pending` rows with a `provisional:` provenance; the paper's default build (`make numbers`, `NUMBERS_MODE=provisional`) prints their values marked as provisional. A row is flipped to `measured` only when the value is the final frame's (or is frame-independent: another tool's output, the input programs, the toolchain). The flip prepends that reason.

**The check.** From the paper repository at the manuscript's commit:

```
python3 scripts/gen_numbers.py --check --input <numbers-of-record.md>
```

It must report `0 undefined`: every key the manuscript cites exists in the table. Then `make numbers` must also succeed: a strict build and the provisional build with the overrides.

## The tools

All four are copies of the documentation repository's `agents/tools/` originals. The only edits replace home-path and host-name defaults with roots relative to this checkout:

- `CRAT_ROOT`: this repository (`seed_numbers.py`, `rq2/seed_rq2.py`; by default the root above `evaluation/`);
- `RECORD`: the table (`seed_numbers.py`, `rq2/seed_rq2.py`, `rq3/seed_rq3_inator.py`; by default `docs/paper/numbers-of-record.md` under the checkout). `rq2/seed_pos.py` reads it as `NOR`, as its original does;
- `DOCS_ROOT`: the documentation repository, by default `docs/`;
- `CROWN_ARTIFACT`: by default `crown-artifact/`;
- `RQ2_TARGET`: by default `declarations/decl_driver/target`;
- `RQ3_HOST`: the name the provenance gives the measuring host, by default `host-b`. The record's existing rows name the host itself, so a newly seeded row reads differently from them.

How each writes, and what it may change:
- **`seed_numbers.py`** writes the record unless `--dry-run` is given. It changes only `pending` rows: rows are written `pending` with a `provisional:` provenance, or `measured` with `--measured`; a row already `measured` or `superseded` is skipped and named.
- **`rq2/seed_rq2.py`** writes `--table OUT.tsv` when asked, and the record only with `--write`. **Do not run `--write` against the record of record.** It re-stamps every row it seeds as `measured` and replaces the provenance whole (no prepend). Its rows are already `measured` in the record, so a `--write` would erase their history.
- **`rq2/seed_pos.py`** writes the record only with `--write`. It skips `measured` rows; a `superseded` row it seeds goes back to `pending`.
- **`rq3/seed_rq3_inator.py`** writes the record only with `--write`. It changes only `pending` rows and names the rest.

| file | purpose | inputs | outputs | keys it feeds |
|---|---|---|---|---|
| `seed_numbers.py` (main) | the census-side seeder; also the library `pos_census.py`, `decl_walker_vs_census.py` and `sloc104.py` import (the SLOC definition, CROWN's declaration universe `crown_universe`) | `--census <census> --label '<frame>' --solve <solve>` | the record (`$RECORD`) | `setup.programs` (cited); `setup.<p>.sloc`, `setup.sloc`, `setup.largest-*`, `rq3.largest/rest.{analysis-s,emit-s,verify-rounds}` (the cited ones of these were set by later reports: 104, 128) |
| `rq2/seed_rq2.py` | CROWN's declaration counter (`../declarations/decl_driver`) over CROWN's and Laertes's outputs, after re-checking CROWN's `evaluation.tsv` 20 / 20 | `benchmarks/rs-crown`, `$CROWN_ARTIFACT`, `$RQ2_TARGET` | the record with `--write`; `--table OUT.tsv` | `rq2.<p>.decl.{crown,laertes}` (cited); `rq2.total.decl.crown` (no longer cited, S70; the numerator of the cited `rq2.total.decl.crown-rate`); `rq2.median.decl.{crown,laertes}`, `rq2.wins.decl` (not cited) |
| `rq2/seed_pos.py` | turns a `pos_census.py` / `run_nobuild.py` output into rows | `--out DIR` (`../positions-uses/`'s output) | the record with `--write` (`$NOR`) | `rq1.<p>.uses.*` and totals (cited); `rq1.<p>.pos.*`, `rq2.<p>.pos.*`, medians (no longer cited, S70) |
| `rq3/seed_rq3_inator.py` (rq3-inator) | turns &inator's and our trial TSVs into rows | `--tsv-dir DIR` (rq3-inator 002a / 021), or `--ours TSV --ours-note TEXT` (our `rq3_trials.py run`) | the record with `--write` (`$RECORD`) | `rq3.inator.<p>.host-s` (cited); `rq3.inator.<p>.reported-s`, or with `--ours` `rq3.inator.<p>.{analysis-s, emit-s}` (no longer cited, S70; `total-s` was seeded from 021's per-trial totals by analysis-fanout 123) |

The keys the paper prints today that these four do not write were set by the analysis lane's apply scripts. Each is kept with its report under the documentation repository's `agents/artifacts/<date>-analysis-fanout-<n>/` (e.g. `apply_154.py`, the flip of report 127). Unlike `rq2/seed_rq2.py`, they read the record and the counter's output, change only the named rows, prepend their provenance phrase, and fail closed when any other row would change.
