#!/bin/bash
# The output check of a derivation: the derived translator on the programs, run as artifact/run.sh runs them (prepare,
# a copy, translate in place with config/analysis-env.sh exported by run.sh's own analysis_env, the evaluation's two
# variables), one at a time on the host; every emitted file checked against a reference digest list.
# usage: check-trees.sh <tag> [program ...]   (default: the --small programs of artifact/lists/programs.tsv)
# Environment: SCRATCH, WORKTREES (rederive.sh's), REF (a `sha256sum` list of reference trees, paths <program>/<file>;
#   unset: the digests are printed), DEPS_TARGET (cargo target of deps_crate; default $SCRATCH/deps-target), CARGO
# The tree is the unpacked zip when there is one, else the derivation's worktree; the binary is the one built from it.
set -u
TAG=${1:?tag}; shift
P=$(cd "$(dirname "$0")" && pwd); REPO=${REPO:-$(git -C "$P" rev-parse --show-toplevel)}
SCRATCH=${SCRATCH:-$REPO/target/packaging/$TAG}; WORKTREES=${WORKTREES:-$SCRATCH/worktrees}; REF=${REF:-}
if [ -d $SCRATCH/unzipped/jobcrat-source ]; then T=$SCRATCH/unzipped/jobcrat-source; BIN=$SCRATCH/zip-target/release/jobcrat
else T=$WORKTREES/rederive-$TAG; BIN=$SCRATCH/target/release/jobcrat; fi
[ -x $BIN ] || { echo "no binary $BIN"; exit 1; }
PROGS=${*:-$(awk -F'\t' '$1 !~ /^#/ && $3 == 1 {print $1}' $T/artifact/lists/programs.tsv)}
DEPS_TARGET=${DEPS_TARGET:-$SCRATCH/deps-target}; CARGO=${CARGO:-cargo}
SR=$(rustup run nightly-2025-06-23 rustc --print sysroot)
[ -d $DEPS_TARGET/debug/deps ] || CARGO_TARGET_DIR=$DEPS_TARGET $CARGO build --manifest-path $T/deps_crate/Cargo.toml > $SCRATCH/build-deps.log 2>&1 || { echo "deps_crate does not build: $SCRATCH/build-deps.log"; exit 1; }
ln -sfn $DEPS_TARGET $T/deps_crate/target
eval "$(sed -n '/^analysis_env() {/,/^}/p' $T/artifact/run.sh)"; type analysis_env > /dev/null || { echo "artifact/run.sh has no analysis_env"; exit 1; }
K=$SCRATCH/check-trees; rm -rf $K; mkdir -p $K/substrate $K/trees $K/runs
echo "CHECK START $(date -u +%FT%TZ) bin=$BIN tree=$T programs=$(echo $PROGS | wc -w) ref=${REF:-none}"
for p in $PROGS; do
  suite=$(awk -F'\t' -v p=$p '$1 == p {print $2}' $T/artifact/lists/programs.tsv)
  ( cd $T && env DIR=$T SYSROOT=$SR LD_LIBRARY_PATH=$SR/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH} $BIN --pass prepare -o $K/substrate benchmarks/$suite/$p > $K/runs/$p.prepare.log 2>&1 ) || { echo "$p: prepare FAILED"; continue; }
  cp -a $K/substrate/$p $K/trees/$p
  ext=; [ "$suite" = crown ] && ext=JOBCRAT_FALLBACK_SLICE_EXTENT=268435456
  ( cd $T && analysis_env $T/config/analysis-env.sh
    env -u JOBCRAT_FALLBACK_SLICE_EXTENT JOBCRAT_ERA5C_RAW_CAUSE_LEDGER=off $ext DIR=$T SYSROOT=$SR LD_LIBRARY_PATH=$SR/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH} \
      /usr/bin/time -v -o $K/runs/$p.time $BIN -v --pass translate --inplace --bo-receipt $K/runs/$p.receipt $K/trees/$p > $K/runs/$p.log 2>&1 )
  rc=$?; wall=$(sed -n 's/.*Elapsed (wall clock) time.*: //p' $K/runs/$p.time)
  if [ -n "$REF" ]; then
    grep -E "  $p/" $REF > $K/runs/$p.ref; n=$(grep -c . $K/runs/$p.ref)
    got=$(cd $K/trees && find $p -type f ! -path '*/target/*' | wc -l)
    if [ $n -gt 0 ] && (cd $K/trees && sha256sum -c --quiet $K/runs/$p.ref > $K/runs/$p.cmp 2>&1) && [ $got = $n ]; then v="identical $n/$n"; else v="DIFFERS ($(grep -c FAILED $K/runs/$p.cmp) of $n; files $got)"; fi
  else v=$(cd $K/trees && find $p -type f ! -path '*/target/*' | sort | xargs sha256sum | sha256sum | cut -c1-16); fi
  echo "$p rc=$rc wall=$wall $v"
done
rm -f $T/deps_crate/target
echo "CHECK END $(date -u +%FT%TZ)"
