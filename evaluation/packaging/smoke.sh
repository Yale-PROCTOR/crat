#!/bin/bash
# The driver built from the unpacked zip, run on prepared inputs; each emitted tree compared with a reference tree.
# usage: smoke.sh <tag> [program ...]   (default programs: avl bst)
# Environment: SCRATCH (rederive.sh's; default $REPO/target/packaging/<tag>), REPO (default: the repository containing this script),
#   INPUTS (holds <program>/; default: the zip's benchmarks/crown with PASSES=expand,extern,preprocess,pointer, else $REPO/benchmarks/rs-crown-derived with pointer), REF_TREES (holds <program>/, the
#   emitted trees of record, in the repository's names; unset: the emitted files' digests are printed instead of a comparison),
#   DEPS_TARGET (cargo target of deps_crate, built here when absent; default $SCRATCH/deps-target), CARGO (default cargo)
set -u
TAG=${1:?tag}; shift; PROGS=${*:-avl bst}
P=$(cd "$(dirname "$0")" && pwd); REPO=${REPO:-$(git -C "$P" rev-parse --show-toplevel)}
SCRATCH=${SCRATCH:-$REPO/target/packaging/$TAG}; REF_TREES=${REF_TREES:-}
Z=$SCRATCH/unzipped/jobcrat-source
if [ -z "${INPUTS:-}" ] && [ -d $Z/benchmarks/crown ]; then INPUTS=$Z/benchmarks/crown; PASSES=${PASSES:-expand,extern,preprocess,pointer}; else INPUTS=${INPUTS:-$REPO/benchmarks/rs-crown-derived}; PASSES=${PASSES:-pointer}; fi
DEPS_TARGET=${DEPS_TARGET:-$SCRATCH/deps-target}; CARGO=${CARGO:-cargo}
BIN=$SCRATCH/zip-target/release/jobcrat
SR=$(rustup run nightly-2025-06-23 rustc --print sysroot)
export LD_LIBRARY_PATH=$SR/lib:$SR/lib/rustlib/x86_64-unknown-linux-gnu/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}
export DIR=$Z SYSROOT=$SR
[ -d $DEPS_TARGET/debug/deps ] || CARGO_TARGET_DIR=$DEPS_TARGET $CARGO build --manifest-path $Z/deps_crate/Cargo.toml > $SCRATCH/build-deps.log 2>&1 || { echo "deps_crate does not build: $SCRATCH/build-deps.log"; exit 1; }
ln -sfn $DEPS_TARGET $Z/deps_crate/target
K=$SCRATCH/smoke; rm -rf $K; mkdir -p $K
echo "SMOKE START $(date -u +%FT%TZ) bin=$BIN inputs=$INPUTS passes=$PASSES ref=${REF_TREES:-none}"
for p in $PROGS; do
  mkdir -p $K/in $K/out-$p; cp -r $INPUTS/$p $K/in/$p; rm -rf $K/in/$p/target
  echo "=== $p ==="; ( cd $K && $BIN -v --pass $PASSES -o $K/out-$p --bo-receipt $K/$p.receipt $K/in/$p > $K/$p.log 2> $K/$p.err ); echo "rc=$?"
  grep -E '^(analysis switches|outcome=)' $K/$p.log | cut -c1-330
  for f in $(cd $K/out-$p/$p && find . -name '*.rs' | sort); do
    if [ -z "$REF_TREES" ]; then echo "$(sha256sum $K/out-$p/$p/$f | cut -c1-16) $f"
    elif cmp -s $K/out-$p/$p/$f $REF_TREES/$p/$f; then echo "identical $f"
    elif cmp -s <(sed 's/__jobcrat_/__crat_/g; s/__JOBCRAT_/__CRAT_/g' $K/out-$p/$p/$f) $REF_TREES/$p/$f; then echo "identical modulo the rename (rule R6) $f"
    else echo "DIFFERS $f"; diff <(sed 's/__jobcrat_/__crat_/g; s/__JOBCRAT_/__CRAT_/g' $K/out-$p/$p/$f) $REF_TREES/$p/$f | head -6; fi
  done
done
rm -f $Z/deps_crate/target
echo "SMOKE END $(date -u +%FT%TZ)"
