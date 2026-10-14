#!/bin/bash
# analysis-fanout relay 145 (supersedes 143's waiter): our half of RQ3's types table at the 60s' head, NO BUILD.
#  binary : main's 60s' census build (newest release/deps/pointer_replacer-* in main's target, built inside the
#           'main BATCH 60SP CENSUS STARTED..ENDED' window; main's own convention), copied and pinned by sha256
#  crat   : rq3/bin/crat-4feea9176-release for the substrate only (crates/passes, utils, src/bin unchanged
#           4feea9176..29a90cdf2); each substrate tree is checked equal to the earlier prep's
#  env    : the final frame's solve jobs (era5c-r215-kindorder; CRAT_ERA5C_RAW_CAUSE_LEDGER=on is in it)
#  trigger: 'main BATCH 60SP CENSUS ENDED' AND (the assembler's LANDED 60s' line OR 2026-10-14T00:00Z = the the head main censused)
# Window: no corpus lock, the last main CENSUS line ENDED, MemAvailable >= 65 GiB, load1 <= 6. PID-keyed kills only.
set -u
W=scratch/analysis-fanout/r145
R=scratch/analysis-fanout/rq3
SF=scratch/main/SLOT-FREE
SOLVE=worktrees/era5c-r215-kindorder
log(){ echo "$(date -u +%FT%TZ) $*" | tee -a $W/our-half.log; }
window(){
  ls worktrees/CORPUS-SLOT*.lock >/dev/null 2>&1 && return 1
  [ "$(awk '/MemAvailable/{print int($2/1048576)}' /proc/meminfo)" -ge 65 ] || return 1
  grep -E '^main .*CENSUS (STARTED|ENDED)' $SF | tail -1 | grep -q ENDED || return 1
  awk '{exit !($1 <= 6)}' /proc/loadavg
}
log "armed pid $$"
until grep -qE '^main BATCH 60SP CENSUS ENDED' $SF; do sleep 120; done
MODE=""
until [ -n "$MODE" ]; do
  L=$(grep -E "assembler LANDED (batch-)?60s(p|′|'|-prime)" $SF | tail -1)
  if [ -n "$L" ]; then MODE=final
  elif [ "$(date -u +%s)" -ge "$(date -u -d 2026-10-14T00:00:00Z +%s)" ]; then MODE=composed
  else sleep 120; fi
done
git -C crat fetch -q origin borrow-ownership
# the head main censused for 60s' = the hash on the last 'main BATCH 60SP CENSUS STARTED ... on <hash>' line
CH=$(grep -E '^main BATCH 60SP CENSUS STARTED' $SF | tail -1 | sed -E 's/.* on ([0-9a-f]{7,40}).*/\1/')
COMPOSED=$(git -C crat rev-parse "$CH") || { log "cannot resolve main's census head $CH"; echo no-head > $W/done; exit 4; }
if [ $MODE = final ]; then HEAD=$(git -C crat rev-parse origin/borrow-ownership); else HEAD=$COMPOSED; fi
log "trigger: mode=$MODE head=$HEAD landed-line='${L:-none}'"
[ "$HEAD" = "$COMPOSED" ] || log "NOTE: the head $HEAD is not $COMPOSED, the head main censused; main's binary may not be this head's -- STOP"
[ "$HEAD" = "$COMPOSED" ] || { echo stop-head > $W/done; exit 2; }
CS=$(grep -E '^main BATCH 60SP CENSUS STARTED' $SF | tail -1 | awk '{print $6}'); CE=$(grep -E '^main BATCH 60SP CENSUS ENDED' $SF | tail -1 | awk '{print $6}')
BIN=$(find dev/.crat-release-target/release/deps -maxdepth 1 -type f -executable -name 'pointer_replacer-*' ! -name '*.*' -newermt "$CS" ! -newermt "$CE" -printf '%T@ %p\n' | sort -rn | head -1 | cut -d' ' -f2)
[ -n "$BIN" ] || { log "no pointer_replacer binary built inside the 60SP census window $CS..$CE"; echo no-binary > $W/done; exit 3; }
OUT=$W/ours-${HEAD:0:9}; mkdir -p $OUT/bin
cp -p "$BIN" $OUT/bin/pointer_replacer-release && cp -p $R/bin/crat-4feea9176-release $OUT/bin/crat-4feea9176-release
( cd $OUT/bin && sha256sum * > SHA256SUMS ); log "binary $BIN (mtime $(stat -c %y $BIN)); $(tr '\n' ' ' < $OUT/bin/SHA256SUMS)"
export RQ3_OUT=$OUT RQ3_BIN=$OUT/bin/pointer_replacer-release RQ3_CRAT=$OUT/bin/crat-4feea9176-release RQ3_FRAME=$HEAD RQ3_SOLVE=$SOLVE
until window; do sleep 60; done
echo "$(date -u +%FT%TZ) analysis-fanout run START (relay 145): RQ3's nine at $MODE head ${HEAD:0:9} (one trial, main's census binary, no build; no corpus program)" >> $SF
cd $R; T=$W/rq3_trials_l7.py
for p in running-example ulidgen leftpad amp nandc rbtree carrays jccc tisp; do
  until window; do sleep 60; done
  python3 -u $T prep $p >> $OUT/run.log 2>&1 || log "$p prep failed"
  python3 -c "
import json,sys
a=json.load(open('$OUT/prep/$p/prep.json'))['substrate_tree_sha256']
try: b=json.load(open('$R/prep/$p/prep.json'))['substrate_tree_sha256']
except Exception: b='(no earlier prep)'
print('$p substrate', 'EQUAL' if a==b else 'DIFFERS', a[:16], b[:16])" >> $W/our-half.log 2>&1
  python3 -u $T trial $p 1 >> $OUT/run.log 2>&1 || log "$p trial failed"
  log "$p done"
done
echo "$(date -u +%FT%TZ) analysis-fanout run END (relay 145): RQ3's nine ($MODE head ${HEAD:0:9})" >> $SF
cp scratch/analysis-fanout/r143/reconcile.json $W/reconcile.json 2>/dev/null
python3 scratch/analysis-fanout/r143/ours.py $OUT $OUT/ours-positions.tsv > $OUT/ours.out 2>&1; log "ours.py exit $?"
echo "$MODE $HEAD" > $W/done; log "done"
