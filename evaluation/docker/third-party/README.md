# third-party/ — the comparison tools, fetched from their public archives and run as the evaluation ran them

Optional and separate. `run.sh` produces every jobcrat column without this directory. This part supplies:
- the CROWN, Laertes and &inator columns of RQ1 (their distributed translations and &inator's types);
- their times, and c2rust's time, for RQ2's Table scale;
- the trees the Miri step reads for the CROWN and Laertes rows of RQ3.

**Runs on the host.** It needs a Docker daemon, which the jobcrat image does not have, plus `curl`, `unzip` and `python3`, and about 70 GB of disk for the downloads and the loaded images. Network is needed only to fetch and to build; every tool runs with `--network none`.

```sh
artifact/third-party/run.sh             # everything (≈ 5.5 h, &inator's jccc and tisp dominate)
artifact/third-party/run.sh --small     # ≈ 10 min after the downloads
artifact/third-party/run.sh crown laertes tables   # any subset of steps, in that order
```

Run it on the host from the source root, before the container's `run.sh … --third-party`, which reads what it writes. Outputs go to `results/third-party/` (`THIRD_PARTY`).

## The sources

`sources.tsv` lists each file by URL, size and digest. A download is checked before use and resumed if interrupted.

| tool | archive | used as |
|---|---|---|
| CROWN (CAV'23) | Zenodo 10.5281/zenodo.7876586, `artifact.zip`, 2,612,422,584 B, md5 `7436500a…` (the record's first version; the later version 7966511 is a different file) | `cav-artifact/crown.tar.gz` → `docker load` → `crown:latest`. Its `/root/crown` holds CROWN's twenty inputs (`benchmark/`) and `comparison/` (Laertes's distributed trees and inputs) |
| Laertes (Aliasing Limits, OOPSLA'23) | Zenodo 10.5281/zenodo.7714175, `aliasing-limits-oopsla23.tar.gz`, 5,227,965,191 B, md5 `f4436443…` | `docker load` → `aliasing-limits-oopsla23:final` (the 2023 tool, toolchain `nightly-2020-10-15`) |
| &inator | Zenodo 10.5281/zenodo.19650358: `refinator-linux-amd64.tar.gz` (the image), `refinator-src.tar.gz` (the source, for tisp), `benchmarks.tar.gz` | `docker load` → `refinator:latest`; the source built with its own Dockerfile → `tp-inator-src:4f1d6a5` |
| &inator's carrays, jccc, tisp | the authors' repository at the pinned commit `4fdf3309` (Zenodo's `benchmarks.tar.gz` carries the other six) | every one of the 58 benchmark files is checked against `inator/inputs-sha256.tsv`. `INATOR_BENCHMARKS=<dir>` supplies a local copy instead |
| c2rust 0.21.0-p1 | upstream c2rust `v0.21.0` (`93471e6`) + `c2rust/c2rust-0.21.0-p1.patch` (13 lines) | `c2rust/Dockerfile` checks the patched tree's git hash (`e2631f82`) and builds `tp-c2rust:0.21.0-p1` |
| GNU time 1.9 | the GNU mirror, sha256 `fbacf0c8…` | built static once, mounted read-only into every tool's container as the clock |

**Downloads take hours.** Zenodo can serve one connection at about 150–200 KB/s, so the ≈ 8.5 GB below may take many hours. `fetch` resumes an interrupted transfer. Files fetched beforehand, for example with a downloader that opens several connections, are used from a directory given as `TP_DOWNLOADS=<dir>`. Each is checked by size and md5 before use:

| file name in `TP_DOWNLOADS` | bytes | md5 |
|---|---:|---|
| `crown-artifact.zip` | 2,612,422,584 | `7436500a8342131d252dbe866b09fab3` |
| `aliasing-limits-oopsla23.tar.gz` | 5,227,965,191 | `f443644380803c1e230d5731f08000ca` |
| `refinator-linux-amd64.tar.gz` | 635,034,527 | `75be10de6694ea022595a457f93e62a2` |
| `refinator-src.tar.gz` | 107,046 | `702f2fdea6589d368bbe9e3878380bce` |
| `inator-benchmarks.tar.gz` | 26,002 | `7892009f0317c6f30328a0b7293f0f97` |
| `time-1.9.tar.gz` | 596,779 | sha256 `fbacf0c81e62429df3e33bda4cee38756604f18e01d977338e23306a3e3b521e` |
| `inator-impl-4fdf3309.tar.gz` | — | its 58 benchmark files are checked against `inator/inputs-sha256.tsv` |

An image that is already loaded (`crown:latest`, `aliasing-limits-oopsla23:final`, `refinator:latest`) is used as it is, and its archive is not fetched.

## The steps and the protocol of record

Each tool runs one program at a time, in one throw-away container per trial (`--rm --network none`), with GNU time inside the container. Times are reported, not compared: they depend on the host. The statuses and the trees are compared.

| step | runs | trials (full / `--small`) | writes |
|---|---|---|---|
| `crown` | CROWN's three calls per program, as its `preprocess.sh` and `run.sh` make them (`preprocess`, `explicit-addr`, `rewrite --results-path …` with the artifact's per-program options); the wall covers the three | 3 / 1 | `crown/runs/<p>/t<k>/`; `trees/crown/<p>/` (trial 1's tree with `analysis_results/`); `crown/evaluation.csv` (CROWN's `evaluate.sh` over the twenty; full run only); `comparison/`, `crown/benchmark/` copied out of the image |
| `laertes` | the mode of record: `cargo run --release --bin resolve-lifetimes -- -f --emulate-lifetime-only -- …`<br>• CROWN's eleven: the artifact's `comparison/laertes-crown/before/<p>`, with the crate-root header of Laertes's output (`laertes/ADAPTATION.tsv`: three gates the 2020 toolchain rejects removed, the output's gates added);<br>• Laertes's own eight: the image's `initial-benchmarks/<p>` with `--merge-field-lifetimes`;<br>• brotli: CROWN's input.<br>Then once without `--emulate-lifetime-only` (the tool's own mode) | 3 where trial 1 completes, else 1 / 1; own mode 1 | `laertes/inputs/`, `laertes/runs/{emulate,noemulate}/<p>/t<k>/` (each with the rewritten `tree/`) |
| `inator` | &inator's own driver `refinator <q>` in its image; tisp in the source build (the image stops on tisp before analysis) | 5 where trial 1 is under 600 s, else 1 / 1 (ulidgen, leftpad, amp, nandc, carrays) | `inator/runs/<q>/t<k>/`; `inator/<q>/{rtypes,stypes,times}.txt` (trial 1); `inator/src/<q>/` (the C sources) |
| `c2rust` | `c2rust transpile --emit-modules --fail-on-error --reduce-type-annotations --emit-build-files` on &inator's `source.c` (jccc: `-Isrc`); the wall covers `transpile` only | 3 / 1 | `c2rust/runs/<q>/t<k>/meta.txt` with the identity line against `c2rust/translations-sha256.tsv` (the translations of record = the source tree's `benchmarks/inator/`) |
| `tables` | — | — | `times.tsv`, `check.txt` |

## What the other steps read

| path under `results/third-party/` | reader |
|---|---|
| `trees/crown/<p>/`, `crown/evaluation.csv`, `comparison/` | rq1 (Tables effect-all / effect-crown); rq3's `third_party.sh` (the CROWN and Laertes Miri rows, with its own crate-root and gate shims) |
| `inator/<q>/{rtypes,stypes}.txt`, `inator/src/<q>/` | rq1 (Table effect-inator, `loc`) |
| `times.tsv` (`key`, `trials`, `min`, `status`; the value is `min` when set, else `status`) | rq2 (Table scale) |

The keys in `times.tsv`:
- `rq3.<p>.crown-s`, `rq3.<p>.laertes-s` (`crash` where Laertes does not complete), `rq3.<p>.laertes-own-mode` (`ok` / `stops`);
- `rq3.inator.<q>.host-s` (&inator's own phase timers: representation + constraints + solving);
- `rq3.inator.<q>.c2rust-s`.

## What to expect

- **CROWN:** `check.txt` reports every source file of `trees/crown/` and all of `comparison/` `equal` to `expected-trees.tsv`.
  - CROWN writes `analysis_results/{ownership,mutability,fatness}.json` in hash order, so their bytes change from run to run. `expected-trees.tsv`'s third column holds the digest of the record's file with its keys sorted, and such a file is reported `equal (content)` when that matches.
  - `statistics.json` is stable.
- **Laertes:**
  - **In the mode of record**, 15 of the twenty complete. binn, brotli, heman, quadtree and rgba do not (`crash`): on the distributed inputs, the tool stops on a diagnostic it cannot handle, or on the initial program.
  - **In its own mode**, 12 complete. avl, libzahl and lodepng stop in the tool, the other five as above.
- **&inator:** completes on its eight (tisp through the source build).
  - Its `rtypes.txt` numbers its variables differently from run to run.
  - The type of each interface position is the same.
  - **tisp's time depends on the build.** &inator's own solving time on tisp varies with the source build: its Dockerfile, run unmodified, installs the current stable Rust and resolves crates without a lock. It also varies with Z3's run-to-run assertion order.
    - The record's run used rustc 1.98.1 with `cc` 1.5.1, `libc` 0.2.189, `llvm-sys` 170.4.0 and `syn` 3.0.6.
    - A build made later (rustc 1.99.1, newer crates) solved the same 283,289 assertions in 1.6× the record's time, with the same types.
    - The record's build is kept in our archive. To get a record-like time on tisp, pin those versions in your own copy of &inator's Dockerfile.
- **c2rust:** every trial's output equals the translation of record.
