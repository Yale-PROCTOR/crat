# The frame record: L01^14u-S39-M (59m, the mutable copy-lend adopted, R1026-1)

| item | value |
|---|---|
| frame name | `L01^14u-S39-M` (the identity's `analysis_frame` constant stays `era5c-l01p14-v1`; the configuration digest separates the frames) |
| what it is | L01^14u-S39 (`l01p14u-s39-frame.md`) with the mutable copy-lend on: `CRAT_ERA5C_COPY_LEND_MUT=on` (identity `era5c_copy_lend_mut=on`; era-5c relays 213/214, R988-1); the analyses tree moves to `ef8a94708` (S39's `2c6824c70` + era-5c's seven `0ac8acd65..c94ea5de5`, composed as batch 59m); adopted by the USER on main 222's count (R1026-1) |
| env file | `l01p14u-s39-mutlend-env.sh`, sha256 `400b1155a37a5101462ee6a4ae4e62bff12cba5074082807a853845e07b15478` |
| its diff against L01^14u-S39's env (`l01p14u-s39-env.sh`, sha256 `b0f0e064…`) | the switch, `TMPDIR` (host-local, not in the identity), and the header comment; equal to the solve row's `ablation-env.sh` variable for variable but `TMPDIR` and the host's z3 library path |
| analysis fingerprint (over `src/analyses`) | `0da300f641816c170fa797d7dbdb6738f1eaf65cf7c10d0cfd534af04384d6ef` (analyses tree `ef8a94708`) |
| launch digest (`CRAT_ERA5_LAUNCH_DIGEST`) | `c7867a07246f910418de569640f4c929f4a54dddfdbbbc94e967a1cb3329f127` = sha256 of the solve row's `launch-manifest.json`; in all twenty jobs' environments and all twenty worker receipts |
| configuration digest (`E5C_IDENTITY_SHA256`) | `334ee80aed21f9c0af4f6eb0fe3305804a608139820c535b9e1b8bb7f11ba725`, reproduced from `l01p14u-s39-mutlend-env.sh` ALONE under the launch digest above by the gate binary of `c94ea5de5` (era-5c 172) and by main 222's census preflight |
| toolchain / dependencies | `6735e704…` / `a69f2655…` (unchanged) |
| solve directory | lambda9 `agent-worktrees/era5c-r213-mutlend` (all twenty at `c94ea5de5`, the binary built there; 19 programs 10-11 19:46Z–10-12 00:02Z, lil 04:19Z–08:25Z), copied to lambda7 `/home/p51lee/dev/agent-worktrees/era5c-r213-mutlend` |
| cache directory | `/home/p51lee/dev/agent-worktrees/era5c-r213-mutlend/cache` (lambda7; entries under `era5b-model-cache-v1/<fingerprint>.json`); READY 2026-10-12 08:30:27Z; every entry checked against the head's six inputs and its recorded bytes (`keycheck.py`, 20 / 20; era-5c 171) |
| the census of record | main's `batch59m` (relay 326, 12:31Z–15:08Z 10-12, on `614029ca1`): main 222, 2,676 by the tree, 79.05 % (R956-1 with D6), −11 vs 59 |
| the frame check's recipe | `l01p14u-s39-mutlend-env.sh` ALONE, with `CRAT_ERA5_LAUNCH_DIGEST` from the solve's worker records; `check_frame_configuration.py` needs S39's two switches under its own names in the checker's subshell only (`l01p14u-s39-frame.md`); `CRAT_ERA5C_COPY_LEND_MUT` it reads by name |
| the code's default | `CRAT_ERA5C_COPY_LEND_MUT` OFF at `614029ca1` (named in the identity only when on) |
