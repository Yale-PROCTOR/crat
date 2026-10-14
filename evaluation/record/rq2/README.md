# evaluation/record/rq2/ -- the RQ1 Table effect-all / effect-crown seeders

See `../README.md` for the row format, the environment variables, and the check.

| file | purpose | inputs | outputs | keys it feeds |
|---|---|---|---|---|
| `seed_rq2.py` | runs CROWN's declaration counter (`../../declarations/decl_driver`) over the inputs, CROWN's and Laertes's outputs, after re-checking CROWN's `evaluation.tsv` 20 / 20 | `benchmarks/rs-crown`, `$CROWN_ARTIFACT`, `$RQ2_TARGET` | the record with `--write`; `--table OUT.tsv` | `rq2.<p>.decl.{crown,laertes}` (cited); `rq2.total.decl.crown` (no longer cited, S70); `rq2.median.decl.{crown,laertes}`, `rq2.wins.decl` (not cited). With `--write` it re-stamps its rows `measured` and replaces their provenance: do not run it against the record of record (`../README.md`) |
| `seed_pos.py` | turns a `pos_census.py` / `run_nobuild.py` output into rows | `--out DIR` (`../../positions-uses/`'s output) | the record with `--write` (`$NOR`) | `rq1.<p>.uses.*`, totals; `rq1.<p>.pos.*`, `rq2.<p>.pos.*` (no longer cited, S70) |
