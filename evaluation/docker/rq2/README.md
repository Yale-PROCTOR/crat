# rq2/ — Table scale (running times)

`rq2/run.sh [--small]` reads the translate step's receipts and time files and the comparison tools' times. It translates nothing: the artifact's `run.sh` times the translate pass first. It writes:
- `results/rq2/keys.txt`: one `key = value` line per key. A key that was not produced reads `skipped (<why>)`; one whose run failed (an exit status, a signal, no receipt or time file) reads `failed (<why>)`; a total reads `no total (...)` where a status word stands in one of its cells. compare.py counts the last two as differences;
- `results/rq2/runs.tsv`: per program, the exit status, the receipt's outcome / verify rounds / reverted functions / files changed, the wall, the solve time and the peak memory;
- `results/tables/scale.csv`: both halves of the table (the sizes come from `results/rq1/keys.txt`);
- `results/tables/scale.tex`: the produced keys as the paper's `numbers.tex` rows.

## What the times are
For each program, one at a time, the translate step runs `jobcrat --pass prepare` (not timed), then `jobcrat --pass translate --inplace --bo-receipt <p>.receipt` on the prepared tree under GNU time (`<p>.time`). Its environment is fixed by `run.sh`: `JOBCRAT_ERA5C_RAW_CAUSE_LEDGER=off`, and `JOBCRAT_FALLBACK_SLICE_EXTENT=268435456` for the twenty (unset for the eight).

| key | definition |
|---|---|
| `rq3.<p>.total-s` | the wall of the translate pass: the solve and the code generation, in one process |
| `rq3.<p>.solve-s` | the receipt's `solve_wall_s` |
| `rq3.<p>.codegen-s` | `total-s` − `solve-s` |
| `rq3.total.*` | the sums of the unrounded per-program values |
| `rq3.largest.analysis-s` | brotli's `solve-s` (the largest of the twenty by lines) |
| `rq3.<p>.{crown,laertes}-s`, `rq3.inator.<q>.{host,c2rust}-s` | the comparison tools' times from `results/third-party/times.tsv` (`third-party/run.sh`). A status in place of a time (e.g. `crash`) is the cell. Their totals sum the printed values; Laertes's is over the programs it completes |
| `rq3.inator.<q>.with-c2rust-s` | `c2rust-s` + `total-s`, both as printed; the total the same way |
| `rq3.inator.total.vs-inator-with-c2rust.factor` | `host-s` total / `with-c2rust-s` total, rounded half up to a whole number |

The twenty print to 0.1 s, the eight to 0.01 s.

**The wall.** The paper's walls were measured around the invocation. If the translate step leaves `<p>.wall` (seconds) beside `<p>.time`, that value is used; otherwise GNU time's "Elapsed (wall clock)" line is read. That line truncates to 10 ms and reads about 0.01 s lower per program. On the paper's own runs, 29 of the 161 keys then move by one unit in their last digit, and the factor reads 166 instead of 165.

## `--small`
- **Not translated:** lil and brotli. Our keys for them, the twenty's totals, `rq3.largest.analysis-s` and the CROWN / Laertes totals read `skipped (--small)`; so do CROWN's and Laertes's cells for them when `times.tsv` has no row.
- **&inator:** `third-party/run.sh --small` runs it on five of the eight. The `host-s` of rbtree, jccc and tisp, their total and the factor then read `skipped (--small)`.
- **c2rust:** runs on all eight, so `with-c2rust-s` is produced throughout.

## Expected values
`../expected.tsv` holds every key the paper cites. `../compare.py` prints each time beside the paper's with their ratio (`reported`). A status word in place of a time must be `equal`. The hardware the paper's times were taken on is in `HARDWARE.md`.
