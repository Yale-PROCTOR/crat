# The frame record: L01^14u-S39-M-O (the objective's order Ref > Owning > Raw, R1038-1 — the FINAL frame)

| item | value |
|---|---|
| frame name | `L01^14u-S39-M-O` (the identity's `analysis_frame` constant stays `era5c-l01p14-v1`; the configuration digest separates the frames) |
| what it is | L01^14u-S39-M (`l01p14u-s39-mutlend-frame.md`, 59m) with the objective's order `CRAT_ERA5C_KIND_ORDER=ref-own-raw`: `own` weighted 1 on every slot in place of the raw term (raw no weight; `ref_` at slots + 1), identity `era5c_kind_order=ref-own-raw(ref=slots+1,own=1,raw=0)`; era-5c relays 215–218 (R1022-1, R1024-1); in the final frame unconditionally (R1038-1), its count measured by main for the paper's sentence |
| env file | `l01p14u-s39-mutlend-o-env.sh`, sha256 `ed55f385730b001d497b6971cb3711331060a682e721393dc793881666d504bc` |
| its diff against L01^14u-S39-M's env (`l01p14u-s39-mutlend-env.sh`, sha256 `400b1155…`) | the switch, `TMPDIR` (host-local, not in the identity), and the header comment; equal to the solve row's `ablation-env.sh` variable for variable but `TMPDIR` and the host's z3 library path |
| analysis fingerprint (over `src/analyses`) | `1d8dcd4092b59826e0987619b9c668d1680d1fe19f15234f7e85e1b8fade712e` (the switch's tree at `319a07f91`) |
| launch digest (`CRAT_ERA5_LAUNCH_DIGEST`) | `2e94d9a5d6557a307b8f8f0df3610a62ae7a66a1682d44b0e13d78d95de1bc8e` = sha256 of the solve row's `launch-manifest.json`; in all twenty jobs' environments and all twenty worker receipts |
| configuration digest (`E5C_IDENTITY_SHA256`) | `d9a474dae778f44541b3392d18834f0e00bcaa3e42ef7be6099e8651ab4cf0ca`, reproduced from `l01p14u-s39-mutlend-o-env.sh` ALONE under the launch digest above by the gate binary of `319a07f91` (era-5c 172b) |
| toolchain / dependencies | `6735e704…` / `a69f2655…` (unchanged) |
| solve directory | lambda9 `agent-worktrees/era5c-r215-kindorder` (all twenty at `319a07f91`, the binary built there; the user's launch 10-13 03:01:57Z, lil last at guard 5 GiB), copied to lambda7 `/home/p51lee/dev/agent-worktrees/era5c-r215-kindorder` |
| cache directory | `/home/p51lee/dev/agent-worktrees/era5c-r215-kindorder/cache` (lambda7; entries under `era5b-model-cache-v1/<fingerprint>.json`); READY 2026-10-13 11:28:10Z; every entry checked against the head's six inputs and its recorded bytes (`keycheck.py`, 20 / 20) |
| the census of record | main's (relay 328, by identity against batch 60's census), on the READY line `era-5c CACHE 60-KINDORDER READY` with `r215/ko-extra-env.sh` |
| the frame check's recipe | `l01p14u-s39-mutlend-o-env.sh` ALONE, with `CRAT_ERA5_LAUNCH_DIGEST` from the solve's worker records; `check_frame_configuration.py` needs S39's two switches under its own names in the checker's subshell only (`l01p14u-s39-frame.md`); `CRAT_ERA5C_COPY_LEND_MUT` and `CRAT_ERA5C_KIND_ORDER` it reads by name |
| the code's default | `CRAT_ERA5C_KIND_ORDER` absent = `ref-raw` (the order of L01^14u … 59m) at `319a07f91`; named in the identity only when set |
