# artifact/ -- reproducing the paper's evaluation (RQ1 to RQ3)

This directory rebuilds the translator from this source tree in a container and re-runs the paper's evaluation on
the inputs in `benchmarks/`: CROWN's twenty programs and &inator's eight. Every number the paper cites is printed
beside the value the run produced, in `results/compare.txt`.

## What it needs

- Docker with BuildKit (Docker 23 or newer), on x86-64 Linux. The image is built from the source root, which is
  the parent of this directory.
- **The full run: 128 GB of memory.** The analysis of lil peaks at 90.1 GiB, brotli at 33.2 GiB and libzahl at
  23.9 GiB; every other program stays at 9.5 GiB or less. **`--small` runs in 32 GB:** it leaves out lil and
  brotli, and genann's Miri run.
- Network access while the image is built (Ubuntu packages, rustup, crates.io, PyPI, npm for cloc), and for the optional
  third-party step. The runs themselves need none. The image takes about 10 minutes to build on a 32-thread machine
  and 6.1 GB of disk.

## Running

```
docker build -f artifact/Dockerfile -t jobcrat-artifact .                       # from the source root
mkdir -p results
docker run --rm -v "$PWD/results:/jobcrat-source/results" jobcrat-artifact all --small   # about 1.5 hours
docker run --rm -v "$PWD/results:/jobcrat-source/results" jobcrat-artifact all           # about 11 hours
```

`all` runs four steps, each of which can also be run alone (`translate`, `rq1`, `rq2`, `rq3`). An `rqN` step
first runs the translation step, which skips every program already translated.

1. **translate.** Every program of `lists/programs.tsv` is translated one at a time, as the paper's runs did:
   `jobcrat --pass prepare` writes `results/substrate/<p>` (not timed). The step then copies it to
   `results/trees/<p>` and translates that copy in place under GNU time. The environment is
   `config/analysis-env.sh`, plus `JOBCRAT_ERA5_PROGRAM=<p>` and `JOBCRAT_ERA5C_RAW_CAUSE_LEDGER=off`. CROWN's
   twenty also get `JOBCRAT_FALLBACK_SLICE_EXTENT=268435456`. `run.sh` lists the exact commands.
2. **rq1:** the counters on the inputs and the emitted trees.
3. **rq2:** the running times, from the receipts and GNU time's records of step 1.
4. **rq3:** the shipped tests run natively, and Miri on the emitted programs.
5. **compare.py** writes `results/compare.txt`.

`results/` belongs to the host. Delete it to start over. A rootful Docker daemon writes it as root.

### The comparison tools (optional)

Some columns come from the comparison tools:
- Laertes's and CROWN's columns of Tables `tab:effect-all` and `tab:scale`;
- every column of Table `tab:effect-crown`, whose population is CROWN's own analysis;
- &inator's columns of Table `tab:effect-inator`;
- C2Rust's time.

These columns need `third-party/run.sh`. It fetches the tools' own artifacts from their Zenodo records and runs
them with their published configurations. It runs **on the host**, from the source root, because it needs a Docker
daemon (and `curl`, `unzip`, `python3`). It writes `results/third-party/`, which the container's steps then read:

```
bash artifact/third-party/run.sh [--small]        # about 8.5 GB of downloads, about 70 GB of disk with the images
docker run --rm -v "$PWD/results:/jobcrat-source/results" jobcrat-artifact all [--small] --third-party
```

`third-party/README.md` gives its steps, walls and options (e.g. `TP_DOWNLOADS`, a directory of archives fetched
beforehand, since the downloads can be slow).

Without this step, those keys read `skipped` and every other column is still produced. `--third-party` makes the
container stop if `results/third-party/` is missing.

## What each table maps to

| paper | RQ | script | results | keys in `compare.txt` |
|---|---|---|---|---|
| Table `tab:effect-all` (declarations and uses made safe) | RQ1 | `rq1/run.sh` | `results/tables/effect-all.{csv,tex}` | `rq1.<p>.{alldecl,uses}.*`, `rq2.<p>.{alldecl,uses}.*`, `setup.*` |
| Table `tab:effect-crown` (CROWN's mutable non-array population) | RQ1 | `rq1/run.sh` | `results/tables/effect-crown.{csv,tex}` | `rq1.<p>.{decl,decl-uses}*`, `rq2.<p>.{decl,decl-uses}.*` |
| Table `tab:effect-inator` (interface pointer kinds, &inator's eight) | RQ1 | `rq1/run.sh` | `results/tables/effect-inator.{csv,tex}` | `rq3.inator.<q>.types.*`, `rq3.inator.<q>.loc` |
| Table `tab:scale` (running times) | RQ2 | `rq2/run.sh` | `results/tables/scale.{csv,tex}` | `rq3.<p>.*-s`, `rq3.inator.<q>.*-s`, the factors |
| Table `tab:miri`, the shipped tests | RQ3 | `rq3/run_rq3.sh` | `results/tables/miri.csv` | `rq4.suite.*`, `rq1.tests.*` |

`expected.tsv` holds every key the paper cites, as the paper prints it. Each `rqN` step writes
`results/<rqN>/keys.txt`. `compare.py` gives each key one verdict:
- `equal`: a count, rate or verdict equal to the paper's;
- `reported`: a time, with its ratio to the paper's;
- `skipped`: the run did not produce the key, e.g. under `--small` or without the third-party step;
- `differ`.

Its last line sums them up. The `.tex` files hold the rows in the paper's `numbers.tex` form.

## The results directory

```
results/substrate/<p>/       prepared inputs           results/trees/<p>/      emitted programs
results/rq2/runs/<p>.{time,receipt,rc}                 results/rq{1,2,3}/keys.txt
results/third-party/         the comparison tools'     results/tables/         the tables (CSV, .tex rows)
results/logs/                one log per program and step, run.log            results/compare.txt
```

## What is not reproduced bit for bit

- **Times.** The paper's times were taken on an AMD Ryzen 9 9950X (16 cores, 32 threads) with 128 GB of memory,
  one program at a time on an idle machine, with one trial (C2Rust: the minimum of three). Another machine, or a
  container, changes them, so `compare.txt` reports them with their ratio and never compares them. The full run's
  translation takes about 2.6 hours on that machine, and the `--small` run's about 80 minutes (`rq2/HARDWARE.md`).
- **genann's Miri run.** It stops at its 8-hour cap, as in the paper; a slower machine completes fewer of its test
  groups by then. `--miri-cap` changes the cap.
- **Everything else is expected to be `equal`:**
  - the counts and rates, deterministic given the solver;
  - the Miri verdicts.
- **lodepng's prepared input** differs from the paper's in form, not in meaning. `prepare` resolves the three
  `#[cfg_attr(target_os = …, link_section = …)]` attributes on its static initializers to Linux's
  `#[link_section = ".init_array"]`, where the paper's prepared input kept all three, so 33 token lines of the
  prepared input and of the emitted program differ; no key moves.
