# evaluation/record/rq3/ -- the &inator seeder

See `../README.md` for the row format, the environment variables, and the check.

| file | purpose | inputs | outputs | keys it feeds |
|---|---|---|---|---|
| `seed_rq3_inator.py` | turns rq3-inator's trial TSVs (`../../inator/`) into rows | `--tsv-dir DIR` (&inator's trials), or `--ours TSV --ours-note TEXT` (our `rq3_trials.py run`) | the record with `--write` (`$RECORD`) | `rq3.inator.<p>.host-s` (cited); `rq3.inator.<p>.{reported-s, analysis-s, emit-s}` (no longer cited, S70) |
