# The frame record: L01^14u-S39 (S39 adopted, R975-1)

| item | value |
|---|---|
| frame name | `L01^14u-S39` (the identity's `analysis_frame` constant stays `era5c-l01p14-v1`; the configuration digest separates the frames) |
| what it is | L01^14u (`l01p14u-frame.md`) with S39's two switches on: `CRAT_COPY_RELAX=depth0-borrow-to-raw` (identity `era5c_copy_relax=depth0-borrow-to-raw+c3-destination-v2`) and `CRAT_MERGE_LIVENESS=on` (identity `era5c_merge_liveness=on`); the analyses tree moves to `2c6824c70` (L01^14u's `0cede10fd` + era-5c's five S39 commits, re-picked onto 58'' as `584941494..3eaf5228d`); adopted by the USER on main 219's count (R975-1) |
| env file | `l01p14u-s39-env.sh`, sha256 `b0f0e064ea142e9c941b969109a9a1d822183b85d8d818ad4c26ac17f296cf90` |
| its diff against L01^14u's env of record (`l01p14u-env.sh`, sha256 `0a94f23e…`) | the two switches, `TMPDIR` (host-local, not in the identity), and the header comment |
| analysis fingerprint (over `src/analyses`) | `746aad538fb71934aa0aeca3df2ad6cfb9b62b457ad44b16d3e8dc781b7ab754` (analyses tree `2c6824c70`) |
| launch digest (`CRAT_ERA5_LAUNCH_DIGEST`) | `09eec6ff33f2494bc0653b2c34600cb206fe2a964516cb30cfea4d498bf3f1c5` = sha256 of row A2's `launch-manifest.json` (era-5c 167c); all twenty jobs seal that file (the lambda7 ten through its verbatim copy `launch-manifest-A2.json` in the solve directory), and all twenty worker receipts carry it |
| configuration digest (`E5C_IDENTITY_SHA256`) | `beff8254eda6f3c6d4595b9fcd57fde722da7a9c779677d922b651ef09081c26`, reproduced from `l01p14u-s39-env.sh` ALONE under the launch digest above by the gate binary at `3eaf5228d` (era-5c 169) and by main 219's census preflight |
| toolchain / dependencies | `6735e704…` / `a69f2655…` (unchanged) |
| solve directory | `/home/p51lee/dev/agent-worktrees/era5c-r211-s39pp` (lambda7) |
| how the twenty were solved | ten (binn, brotli, bzip2, genann, heman, libcsv, libtree, libzahl, lil, tulipindicators) on lambda9 as row A2 at `e363a00dc` (verifier `c509854d…`, solve dir `era5c-r208-relax2`), copied into the solve directory; ten (avl, bst, buffer, ht, json.h, lodepng, quadtree, rgba, robotfindskitten, urlparser) on lambda7 at `3eaf5228d` (verifier `c4a2fa2b…`, inventory seal `8db463ca…`); `e363a00dc` and `3eaf5228d` have the same analyses tree, so the twenty share all six key inputs (era-5c 168 §3) |
| cache directory | `/home/p51lee/dev/agent-worktrees/era5c-r211-s39pp/cache` (entries under `era5b-model-cache-v1/<fingerprint>.json`); READY 2026-10-11 08:47Z; every entry checked against the head's six inputs and its recorded bytes (`keycheck.py`, 20 / 20) |
| accepted-cache manifest | `l01p14u-s39-manifest.tsv` in the solve directory (`program`, `fingerprint`, `entry_sha256`; from the two solves' `progress.jsonl`), sha256 `4406c00d…`; its `program`/`fingerprint` columns equal main's `batch58pps39-manifest.tsv` |
| the census of record | main's `batch58pps39` (relay 323, 08:49Z–11:41Z 10-11, on `3eaf5228d`): main 219, 2,678 by the tree, 79.09 % (R956-1), +51 / −22 vs 58'' |
| the frame check's recipe | `l01p14u-s39-env.sh` ALONE (nothing layered under it), with `CRAT_ERA5_LAUNCH_DIGEST` from the solve's worker records, as L01^14u's; `check_frame_configuration.py` needs the two switches under its own names in the checker's subshell only: `CRAT_ERA5C_COPY_RELAX=depth0-borrow-to-raw+c3-destination-v2`, `CRAT_ERA5C_MERGE_LIVENESS=on` (the solver never reads those names) |
| the code's defaults | both switches OFF at `3eaf5228d` (named in the identity only when set); making them the defaults is a separate change offered for batch 59 (R975-1 item 3) |
