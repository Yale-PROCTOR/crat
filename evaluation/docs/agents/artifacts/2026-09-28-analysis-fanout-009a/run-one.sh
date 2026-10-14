#!/usr/bin/env bash
# r6/run-one.sh <program> <A|B|C>   (C = bo mode, Mode-A: the A5-off control)
set -euo pipefail; P=$1; ARM=$2; shift 2
R=scratch/analysis-fanout/r6
BIN=scratch/era-5c/target-l01p9b/debug/deps/pointer_replacer-c3659d0505ff69ae
[ "$(sha256sum "$BIN" | cut -d' ' -f1)" = 7f7c2a91cbc0e01122dba60fe5217dbe7ec677d52009b85f4e2385aa7dea7874 ] || exit 1
SRC=crat/benchmarks/rs-crown-derived/$P/lib.rs
[ -f "$SRC" ] || SRC=crat/benchmarks/rs-crown-derived/$P/c2rust-lib.rs
set +u; . docs/agents/artifacts/2026-09-27-main-126/frame-of-record/l01p9-env.sh; set -u
export TMPDIR=$R/tmp DIR=crat   # deps_crate, as the frame's jobs set it (jobs/*.json); fan-out 009 §3
unset CRAT_ERA5_LAUNCH_DIGEST CRAT_ERA5_PROGRAM CRAT_ERA5_INPUT_ROOT
export CRAT_BOC1_INPUT=$SRC CRAT_BOC1_NAME=$P CRAT_ERA5C_DEBUG=1
case $ARM in
  A) export CRAT_BOC1_MODE=a5-batch-model CRAT_BO_L2_GUARDED_COMMITS=0 \
       CRAT_A5_OFFICIAL_EVALUATION=crat/benchmarks/rs-crown-transformed/evaluation.tsv \
       CRAT_A5_OFFICIAL_EVALUATION_SHA256=7aa16d5b63ff39e6aaabd3590ec2be9c88c9d8a753bd9f74cd4e6056d9974fd7 \
       CRAT_A5_BATCH_SHARD_DIR=$R/shards/$P-A ;;
  B) export CRAT_BOC1_MODE=bo CRAT_BO_L2_GUARDED_COMMITS=1 CRAT_POINTER_DECISION_DIAGNOSTICS=full CRAT_BO_L2_TRANSITION_DIAGNOSTICS=1 ;;
  C) export CRAT_BOC1_MODE=bo CRAT_BO_L2_GUARDED_COMMITS=0 CRAT_BOC1_ER4_OUT=$R/runs/$P-C/er4.tsv ;;   # the loan-identity dump (MIR locations) for the witness; fan-out 009 §3 (2)
esac
OUT=$R/runs/$P-$ARM; mkdir -p "$OUT" "$R/tmp" "$R/shards"
env | grep -E '^(CRAT_|RUSTUP_TOOLCHAIN|SYSROOT|LD_LIBRARY_PATH|TMPDIR)' | sort > "$OUT/env.txt"
( ulimit -v $((16*1024*1024)); exec nice -n 10 ionice -c3 /usr/bin/time -v "$BIN" \
    bo_c1::boc1_run_one --exact --ignored --nocapture --test-threads=1 ) > "$OUT/stdout.txt" 2> "$OUT/stderr.txt" \
  || echo "exit=$?" >> "$OUT/status.txt"
