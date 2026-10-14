# evaluation/MANIFEST.md -- the external artifacts, by identity

Everything the evaluation needs that is not in this repository, one entry each. Each entry gives:
- the identity, as recorded;
- where the artifact comes from;
- which step uses it;
- the report that establishes it: `<lane> <n>` is a report of the documentation repository (`agents/reports/<lane>/<n>-…`); `MANIFEST-131` marks a value read on the measuring host for analysis-fanout 131.

**About image IDs.** An image ID below is the local id that `docker load` / `docker build` gives, not a registry digest. None of these images is in a registry.

## Tools of the comparison

**1. CROWN's artifact (CAV 2023)**
- **Archive:** `artifact.zip`, 2,695,974,877 B, sha256 `1e3b1cb82cc88d30fbcefc2d56db0d9c52d5e965dbe7c75042e7a80b130c115f` (MANIFEST-131). It unpacks to `cav-artifact/{README.md, LICENSE, crown.tar.gz}`.
- **Tool and benchmarks:** `KomaEc/crown`, branch `artifact`, commit `e46e2284a4b1c236e492337345552b1da070e74c`.
- **Official table:** `evaluation.tsv`, sha256 `7aa16d5b63ff39e6aaabd3590ec2be9c88c9d8a753bd9f74cd4e6056d9974fd7`.
- **Source:** https://github.com/KomaEc/crown (no DOI found).
- **Used by:**
  - the CROWN and Laertes columns of Tables effect-all / effect-crown, through `$CROWN_ARTIFACT`: `c-code/`, `benchmark/`, `analysis_results/`, `comparison/laertes-{crown,laertes}/{before,after}/<p>`;
  - Table miri's CROWN and Laertes trees (`runtime/`);
  - setup's C line counts.
- **Established by:** the seat's ruling R693-2; analysis-fanout 048, 122; wave-6o 156.

**2. CROWN's image `crown:latest`**
- **Identity:** loaded from the artifact's `crown.tar.gz` (`docker load`); image ID `sha256:195933186d8a2518fa5f106b2017dff8e58cda2bee1874c6119df5d77fd973b7` (MANIFEST-131), created 2023-05-24. The tool is at `/root/crown/target/release/crown`, toolchain nightly-2023-01-26.
- **Used by:**
  - `crown-laertes/run-all.sh` + `crown-one.sh` (Table scale-crown, `rq3.<p>.crown-s`), with the artifact's own per-program `run.sh` options;
  - its output equals `rs-crown-transformed/<p>` on 20 / 20.
- **Established by:** analysis-fanout 122 §1.

**3. Laertes's image `aliasing-limits-oopsla23:final`**
- **Identity:** the OOPSLA 2023 "Aliasing Limits" artifact, `aliasing-limits-oopsla23.tar.gz`, 5,227,965,191 B, md5 `f443644380803c1e230d5731f08000ca` (as published; no sha256 recorded). Image ID `sha256:20b9f9996c0fa82ad220c870a1b68433956889b06047daa39317aa537b5de6d5`, created 2023-03-09; resolve-lifetimes on nightly-2020-10-15.
- **Source:** Zenodo `10.5281/zenodo.7714175`.
- **Used by:** `crown-laertes/prep_laertes2.py` + `run-laertes2.sh` + `laertes-one2.sh` (Table scale-crown, `rq3.<p>.laertes-s`). RQ3's Miri runs do not use the image; they use only the distributed Laertes trees in CROWN's artifact.
- **Established by:** analysis-fanout 047, 050 (image id), 122 §2.

**4. &inator's artifact**
- **Identity:** Zenodo `10.5281/zenodo.19650358` (concept `10.5281/zenodo.18989696`), with these files:
  - `refinator-linux-amd64.tar.gz`, sha256 `76bd4a8822d0a07986a041c761ced743dfaed808b5fd665cc35695cd403d7500` (md5 `75be10de6694ea022595a457f93e62a2`). It gives image `refinator@sha256:ce24df0ef894178c685e044a6d322b3dd04349a0afcd52d1d6786098170e2944` (Fedora 42, rustc 1.94.0, LLVM 17.0.6, Z3 4.15.4; binary sha256 `72334a186c444b20d4b26af672aecd3de04ef544d41400ab4dcb4dcf2cdff58d`).
  - `refinator-src.tar.gz`, sha256 `373d1bc230f4c76bb738e329917b0d8ca09e7568c590a19be47b9ab86c9f2663` (md5 `702f2fdea6589d368bbe9e3878380bce`).
  - `benchmarks.tar.gz`, sha256 `61a983f813b83c2ae922645e9804bc86ac1c07a646cfa40f4b1275f751dab0e7` (md5 `7892009f0317c6f30328a0b7293f0f97`).
- **Source:** https://zenodo.org/records/19650358
- **Used by:** `inator/` (rq3-inator's runs: Table scale-inator `rq3.inator.<p>.host-s`) and `inator-types/` (Table effect-inator, from &inator's `rtypes.txt` / `stypes.txt`).
- **Established by:** rq3-inator 001, 022.

**5. &inator's source**
- **Identity:** `PLaSSticity/refinator-impl`:
  - `4f1d6a543ac7ab1c26b7e30fb3aff5c5b1673349`, the Zenodo source archive's commit, built for tisp;
  - `4fdf3309d2a3763786b0090ae956940d97661855`, the same plus one README line; its `benchmarks/` are the nine's inputs. carrays, jccc and tisp exist only there. The stable identity of the inputs is the 58 per-file sha256 in `inator/prep/inputs-sha256.tsv`.
- **The source-build image:** `refinator-src:4f1d6a5` = `sha256:5d290ece5afbfde04f5409bb8741acad18d22dedeac4aa638ba5808f4cdc4b13`, built with the unmodified Dockerfile. A rebuild re-resolves Fedora 42 and gives another digest.
- **Source:** https://github.com/PLaSSticity/refinator-impl
- **Used by:** tisp's `host-s` (the shipped image panics on tisp); the nine's C inputs (`inator/prep/`, `inator-types/manifest.py`).
- **Established by:** rq3-inator 002, 002a, 022; analysis-fanout 016.

**6. &inator's paper**
- **Identity:** arXiv `2604.17261v2` (PACMPL 10 PLDI, Art. 192), PDF sha256 `c1089650a27af3e5eea0363433cd45ce72612dc63ea2e9a87f1cf4f3b08b08c3`.
- **Used by:** `rq3.inator.<p>.reported-s` (its Table 3), which is no longer cited (S70).
- **Established by:** rq3-inator 002, 020.

**7. The c2rust fork that translated the nine**
- **Identity:** `Yale-PROCTOR/c2rust` at `e4a13cab5b6e53aba676d6b2505322425d269932` (C2Rust 0.21.0, built with nightly-2022-08-08 and clang 14), as the image `crat-c2rust:yale-proctor-e4a13ca` = `sha256:5e43a323e3930f1bb1fbf1902114b78c9826adbe39a52b9beb8681c45c16ce0e` (base `ubuntu:22.04@sha256:104ae83764a5119017b8e8d6218fa0832b09df65aae7d5a6de29a85d813da2fb`).
- **CROWN's flags:** `c2rust transpile --emit-modules --fail-on-error --reduce-type-annotations --emit-build-files` over a one-entry `compile_commands.json` (`-Isrc` for jccc only). The outputs' 54 sha256 are in `inator/prep/c2rust-out-sha256.tsv`.
- **Source:** https://github.com/Yale-PROCTOR/c2rust; the recipe is `inator/prep/Dockerfile.c2rust`.
- **Used by:** `inator/prep/`, our trials of the nine (`inator/ours/`, `rq3-trials/`), `inator-types/`.
- **Established by:** analysis-fanout 017; rq3-inator 022.

## Toolchains and tools

**8. Rust nightly-2025-06-23**
- **Identity:** rustc 1.89.0-nightly (`be19eda0dc4c22c5cf5f1b48fd163acf9bd4b0a6`, 2025-06-22); components rustfmt, clippy, rust-src, rustc-dev, llvm-tools-preview. Pinned by the repository's `rust-toolchain.toml`.
- **Used by:** every crat step (substrate, solve, emission, compile check, our trials); key `setup.rustc`.
- **Established by:** analysis-fanout 102.

**9. Rust nightly-2023-01-26**
- **Identity:** the channel (the full version hash is not recorded).
- **Used by:** CROWN's tool and tree builds; `declarations/decl_driver` (CROWN's declaration counter, with rustc-dev); `crates/pointer_replacer/tools/crown_usage_metric`.
- **Established by:** analysis-fanout 048, 126.

**10. Miri**
- **Identity:** miri 0.1.0 on rustc 1.100.0-nightly (`923c95cdf` 2026-09-16), the default `nightly` with the `miri` component. It is not pinned by the repository: the harness calls `cargo +nightly`. Flags: `-Zmiri-tree-borrows -Zmiri-disable-isolation -Zmiri-ignore-leaks`, `-C panic=abort`; pass C adds `-Zmiri-address-reuse-rate=0`.
- **Used by:** `runtime/` (Table miri, `rq4.suite.*`).
- **Established by:** wave-6o 097, 156.

**11. Z3 4.15.4 (release)**
- **Identity:** `z3-4.15.4-x64-glibc-2.39.zip`, sha256 `a41b690e89c343931471506cdc6d957b6044a200fd2d240cc017432afdff7d3e`.
- **Source:** https://github.com/Z3Prover/z3/releases (tag `z3-4.15.4`).
- **Used by:** the solve of record and its serial timing (`pipeline/solve/`, key `setup.solver`); the nine's builds and trials.
- **Established by:** era-5c 174; rq3-inator 003.

**12. Z3 4.15.4 (pip)**
- **Identity:** `z3-solver==4.15.4.0` (PyPI), its `z3/lib` and `z3/include` through `Z3_SYS_Z3_HEADER` / `Z3_LIBRARY_PATH_OVERRIDE` / `LD_LIBRARY_PATH`. The same solver version as 11, packaged differently.
- **Used by:** the census and counter builds.
- **Established by:** analysis-fanout 126.

**13. cloc 2.00**
- **Identity:** `cloc-2.00.pl`, sha256 `2e8d7d57112b0af14d8578d8679423b6e82f1007b29f71c71510f0bc09563b95`, run as `perl cloc-2.00.pl --quiet --csv --include-ext=c,h <dir>` (the SUM row's code column).
- **Source:** https://github.com/AlDanial/cloc/releases/tag/v2.00
- **Used by:** `inator-types/manifest.py` (`rq3.inator.<p>.loc`), the C line counts.
- **Established by:** analysis-fanout 016, 104.

rq3-inator's own cross-count used cloc 2.06; it is not of record (rq3-inator 022).

**14. GNU time 1.7**
- **Identity:** Ubuntu bionic's `time_1.7-25.1build1_amd64.deb`, sha256 `c46db7f84e8e92004ebb437e36560e3bfe656ff79d4d1a359a8a193a6c2521c2`. The extracted binary has sha256 `f3c4104d963b00e1b3a3dcf80722fea57f15f67b57a512cc30adc434b60e6e03` and is mounted read-only in the Laertes image as `crown-laertes/bin/time-bionic`.
- **Used by:** `rq3.<p>.laertes-s`.
- **Established by:** analysis-fanout 122, 124.

**15. GNU time 1.9 (host)**
- **Identity:** the measuring host's `/usr/bin/time`, Ubuntu package `time` 1.9-0.3, binary sha256 `acc7bb5fc9250d5a6abe1974c39fe4e11ca4e9454f3994e3117aceae1b988d57` (MANIFEST-131). It is mounted read-only in `crown:latest`.
- **Used by:** `rq3.<p>.crown-s`.
- **Established by:** analysis-fanout 122.

**16. GNU time 1.9 (static)**
- **Identity:** built from `time-1.9.tar.gz` (sha256 `fbacf0c81e62429df3e33bda4cee38756604f18e01d977338e23306a3e3b521e`) with `./configure CFLAGS='-O2 -std=gnu17' LDFLAGS=-static`, giving `gnu-time-1.9-static`, sha256 `a8ea45d8555b30980c2d73a5ce44dbc773cda44fb0c16531007e6f86825bde42`.
- **Used by:** the &inator trials' in-container wrapper (`inator/inator/build-gnu-time.sh`).
- **Established by:** rq3-inator 022.

## Inputs and the solve that are not in the repository

**17. The twenty inputs**
- **Identity:** `benchmarks/rs-crown/<p>` = CROWN's artifact `benchmark/<p>` byte for byte (CROWN's c2rust 0.16.0 translations). `benchmarks/rs-*` is gitignored, so they are copied from the artifact.
- **The derived substrate:** `benchmarks/rs-crown-derived` (`pipeline/substrate/`), pinned by tree digest `db96829b5c2b0db28fb4bb9ddd3d32901b5d4e6e4134da07ada0d513d94eb4c6`.
- **CROWN's outputs:** `benchmarks/rs-crown-transformed/<p>` are CROWN's outputs; `crown:latest` reproduces them 20 / 20.
- **Established by:** analysis-fanout 122 §1.

**18. tulipindicators' C source** (not in CROWN's artifact)
- **Identity:** `TulipCharts/tulipindicators` `6b3ff6d2227ceed377862750d5c38eed8ac0a0bb` (0.8.4).
- **Used by:** its C line count.
- **Established by:** analysis-fanout 104.

**19. The solve of record**
- **Identity:** `era5c-r215-kindorder`, analysis `1d8dcd40`, configuration `d9a474da`, launch `2e94d9a5`, toolchain `6735e704`, dependencies `a69f2655`.
- **The cache of record:** 20 entries under `cache/era5b-model-cache-v1/`, 50,568,311,000 B, keycheck 20 / 20. Its identity line is sha256 `61887aebda711853bf497db3adf8125f4b81d4fb6352be1acb7ed4253141be02` over the twenty rows `program \t key \t entry_sha256 \t payload_sha256 \t launch_sha256`, sorted by program, from its `workers/*.json`.
- **The source row:** `era5c-l01p14u-solve`, whose `launch-manifest.json` has sha256 `02d40d85e4da4b87120028288cf2a0bde237b18b18ab836d74fc2464b5d13b4f`.
- **The files every job seals:**
  - the input manifests, listing sha256 `3e98ee46…`;
  - the source seal `90c0842f…`;
  - the toolchain recipe `6735e704…`;
  - the dependencies `a69f2655…`.
- **The binaries,** built, not shipped: the solve's debug test binary `5ca1db2d8307371bc3814c911ec9bec0b0191becb0fb19c482f4ff49dcc5bcd6`; the serial timing's release test binary `0cb4e62743e07ce2009400a8df6ec006617dff4d1b11b1d5ae07e79b984b2018`.
- **What a reproducing host needs** (the host list, the sealed absolute paths): era-5c 175 §4. The environment of record is in the repository: `crates/pointer_replacer/frames/l01p14u-s39-mutlend-o-env.sh` and `l01p14u-s39-mutlend-o-frame.md`. The serial release timing re-solves the same models; its cache keys and model payload digests equal the solve's (20 / 20).
- **Used by:** `pipeline/solve/` (its model cache) → `pipeline/emit/` (cache-only emission), `setup/seed_g5.py`, `analysis-waivers/release_sites.py`.
- **Established by:** the batch-60s′ landing record; era-5c 174, 175.

**20. The C reference runs**
- **Identity:** the native census's run directory `runtime-frame13`, the input-UB control (`$NATIVE_REF`).
- **Used by:** `runtime/`.
- **Established by:** wave-6o 156.
