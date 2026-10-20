# The frame record: L01^14u (the uniform objective)

| item | value |
|---|---|
| frame name | `L01^14u` (the identity's `analysis_frame` constant stays `era5c-l01p14-v1`; the configuration digest separates the frames, era-5c 152) |
| what it is | L01^14 (seal `d09892164`, analyses tree `0cede10fd`, the restored substrate) with both owner preference terms off: `CRAT_ERA5C_LEAK_PARITY=off`, `CRAT_ERA5C_OWN_PREFER_LOCAL=off`; nothing else changes (R857-0, R858-1) |
| solve directory | `/home/p51lee/dev/agent-worktrees/era5c-l01p14u-solve` |
| env file | `l01p14u-env.sh`, sha256 `0a94f23e244f94bd70d170521dcd2c442d362b41d348c14aea3f191e1ebba28f` (byte-identical to the solve directory's `l01p14-env.sh`) |
| its diff against L01^14's env of record (`l01p14-env.sh`, sha256 `b92362720d98f5fcb30f0b31c987cf3ccd00d7ecf07e150e3eb331bcad9a1155`, the restored solve's copy) | three lines: `CRAT_ERA5C_LEAK_PARITY` on → off, `CRAT_ERA5C_OWN_PREFER_LOCAL` on → off, `TMPDIR` (host-local, not in the identity) |
| launch digest (`CRAT_ERA5_LAUNCH_DIGEST`, = sha256 of `launch-manifest.json`) | `02d40d85e4da4b87120028288cf2a0bde237b18b18ab836d74fc2464b5d13b4f` (in all 20 jobs' environment blocks) |
| configuration digest (`E5C_IDENTITY_SHA256`) | `888aee0f6d8f7d9f24eea8d3d7d8837bd2f20fad047821fdd8fcf30ef625ed48` |
| analysis fingerprint (over `src/analyses`) | `1681ec8dfdacaa5d57eeae1959e1f1b24aaf15d395bf07145e3563428355d636` (unchanged from L01^14) |
| toolchain / dependencies | `6735e704…` / `a69f2655…` (unchanged) |
| verifier (the sealed binary, not rebuilt) | `3087c5dc614e08ba289cad5a74c27f5a5490f769d263acada9ec57e46f1749e5` |
| inventory seal | `003e5c7addd44d184aa01fb7fb02d2426cc0df0b793b6be05063283b6b2d5c45` |
| cache directory | `/home/p51lee/dev/agent-worktrees/era5c-l01p14u-solve/cache` (entries under `era5b-model-cache-v1/<fingerprint>.json`) |
| accepted-cache manifest (what wave-6o's C1 `--verify-sha256` reads) | `l01p14u-manifest.tsv` (`program`, `fingerprint`, `entry_sha256`, one row per accepted program), written from the runner's `progress.jsonl` at its `done` event into this directory and `/home/p51lee/dev/.crat-scratch/era-5c/r195/final/l01p14u-manifest.tsv`; same format and derivation as main's `l01p14-manifest.tsv` (the derivation reproduces main's L01^14 file byte for byte) |
| criterion 5's line | `l01p14u-criterion5.txt` here and one marker line at the `done` event (`<utc> era-5c L01^14u solve records (criterion 5): …`); per program in `l01p14u-solve-records.tsv` |
| the frame check's recipe | `l01p14u-env.sh` ALONE (nothing layered under it), with `CRAT_ERA5_LAUNCH_DIGEST` from the solve's worker records, as L01^14's |
