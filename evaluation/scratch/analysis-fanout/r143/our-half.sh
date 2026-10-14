#!/bin/bash
# analysis-fanout relay 143, our half: the nine through the RQ3 pipeline (substrate -> S2 entry -> S1 solve -> census
# child), ONE trial, at the FINAL landed head; then ours.py reads the emitted types, model kinds and raw causes.
# Waits for: the assembler's LANDED line for 60s in main's SLOT-FREE AND the final frame's env file
# (frames/l01p14u-s39-mutlend-o-env.sh) at origin/borrow-ownership; fallback at 2026-10-14T00:00Z: batch 60 7682bb8a0
# with a not-the-final-head receipt. Window: no corpus lock, the last main CENSUS line ENDED, MemAvailable >= 65 GiB,
# load1 <= 6 (never beside a gate or a census). Kills: none (PID-keyed only, never by pattern).
set -u
W=scratch/analysis-fanout/r143
R=scratch/analysis-fanout/rq3
SF=scratch/main/SLOT-FREE
SOLVE=worktrees/era5c-r215-kindorder
ENVF=crates/pointer_replacer/frames/l01p14u-s39-mutlend-o-env.sh
START_LINES=$(wc -l < $SF)
log(){ echo "$(date -u +%FT%TZ) $*" | tee -a $W/our-half.log; }
landed(){
  tail -n +$((START_LINES+1)) $SF | grep -qiE 'assembler LANDED .*60s' || grep -qiE 'assembler LANDED (batch[- ])?60s' $SF || return 1
  git -C crat fetch -q origin borrow-ownership || return 1
  git -C crat cat-file -e origin/borrow-ownership:$ENVF 2>/dev/null
}
window(){
  ls worktrees/CORPUS-SLOT*.lock >/dev/null 2>&1 && return 1
  [ "$(awk '/MemAvailable/{print int($2/1048576)}' /proc/meminfo)" -ge 65 ] || return 1
  grep -E '^main .*CENSUS (STARTED|ENDED)' $SF | tail -1 | grep -q ENDED || return 1
  awk '{exit !($1 <= 6)}' /proc/loadavg
}
MODE=final
until landed; do
  if [ "$(date -u +%s)" -ge "$(date -u -d 2026-10-14T00:00:00Z +%s)" ]; then MODE=fallback; break; fi
  sleep 120
done
if [ $MODE = final ]; then HEAD=$(git -C crat rev-parse origin/borrow-ownership); else HEAD=$(git -C crat rev-parse 7682bb8a0); fi
S=${HEAD:0:9}
log "trigger: mode=$MODE head=$HEAD"
until window; do sleep 60; done
OUT=$W/ours-$S; mkdir -p $OUT/bin
WT=worktrees/crat-analysis-fanout-r143-$S
[ -d $WT ] || git -C crat worktree add --detach $WT $HEAD || { log "worktree failed"; exit 1; }
[ -z "$(git -C $WT status --porcelain)" ] || { log "worktree dirty"; exit 1; }
export Z3_SYS_Z3_HEADER=home/.local/opt/z3-solver-4.15.4.0/z3/include/z3.h
export Z3_LIBRARY_PATH_OVERRIDE=home/.local/opt/z3-solver-4.15.4.0/z3/lib LIBRARY_PATH=home/.local/opt/z3-solver-4.15.4.0/z3/lib
export BINDGEN_EXTRA_CLANG_ARGS=-I/usr/lib/gcc/x86_64-linux-gnu/15/include
export RUSTUP_TOOLCHAIN=nightly-2025-06-23-x86_64-unknown-linux-gnu
export CARGO_TARGET_DIR=dev/.crat-release-target-analysis-fanout CRAT_LANE=analysis-fanout CARGO_INCREMENTAL=0
echo "$(date -u +%FT%TZ) analysis-fanout build START (relay 143): RQ3 types table, release build at $S ($MODE) in my own target (clean -p, CARGO_INCREMENTAL=0; no corpus program, no lock)" >> $SF
( cd $WT && cargo clean -p pointer_replacer --release >/dev/null 2>&1; \
  bash docs/agents/tools/crat-cargo.sh build --release -p pointer_replacer --tests --message-format=json-render-diagnostics > $OUT/build-release.json \
  && bash docs/agents/tools/crat-cargo.sh build --release --bin crat ) \
  || { echo "$(date -u +%FT%TZ) analysis-fanout build END (relay 143): FAILED" >> $SF; log "BUILD FAILED"; echo build-failed > $OUT/done; exit 3; }
echo "$(date -u +%FT%TZ) analysis-fanout build END (relay 143): ok" >> $SF
grep -o '"src_path":"[^"]*"' $OUT/build-release.json | grep -c pointer_replacer > /dev/null
T=$(python3 -c "
import json
for l in open('$OUT/build-release.json'):
    try: m=json.loads(l)
    except Exception: continue
    if m.get('reason')=='compiler-artifact' and m.get('target',{}).get('name')=='pointer_replacer' and m.get('profile',{}).get('test') and m.get('executable'): print(m['executable'])
")
cp -p "$T" $OUT/bin/pointer_replacer-release && cp -p $CARGO_TARGET_DIR/release/crat $OUT/bin/crat-release
( cd $OUT/bin && sha256sum * > SHA256SUMS ); log "built: $(tr '\n' ' ' < $OUT/bin/SHA256SUMS)"
grep -h 'Compiling pointer_replacer' $OUT/build-release.json | head -1 >> $W/our-half.log
export RQ3_OUT=$OUT RQ3_BIN=$OUT/bin/pointer_replacer-release RQ3_CRAT=$OUT/bin/crat-release RQ3_FRAME=$HEAD RQ3_SOLVE=$SOLVE
echo "$(date -u +%FT%TZ) analysis-fanout run START (relay 143): the nine (RQ3 pipeline, one trial, $MODE head $S; no corpus program)" >> $SF
cd $R
for p in running-example ulidgen leftpad amp nandc rbtree carrays jccc tisp; do
  until window; do sleep 60; done
  python3 -u rq3_trials.py prep $p >> $OUT/run.log 2>&1 || log "$p prep failed"
  python3 -u rq3_trials.py trial $p 1 >> $OUT/run.log 2>&1 || log "$p trial failed"
  log "$p done"
done
echo "$(date -u +%FT%TZ) analysis-fanout run END (relay 143): the nine ($MODE head $S)" >> $SF
python3 $W/ours.py $OUT $OUT/ours-positions.tsv > $OUT/ours.out 2>&1; log "ours.py exit $?"
echo "$MODE $HEAD" > $OUT/done; log "done"
