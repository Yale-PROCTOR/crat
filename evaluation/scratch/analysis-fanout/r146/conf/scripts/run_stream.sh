#!/bin/bash
# r146 conf (re-pointed r141 run_stream.sh): the cache-streaming checkers, python only, no rustc.
# Each step waits for MemAvailable >= 30 GiB and is stopped (by its pid) if MemAvailable drops below 30 GiB.
# usage: run_stream.sh c1|rs <census-dir> <cache-dir> <manifest.tsv> <out-dir>
#   c1 = C1 FactFidelity --verify-sha256 against the cache + manifest; rs = resid_scan over the manifest's 20 entries
set -u
export PYTHONDONTWRITEBYTECODE=1
CH=$1; CEN=$2; C=$3; MAN=$4; OUT=$5
T=scratch/analysis-fanout/r146/conf/tools
avail() { awk '/MemAvailable/{print int($2/1048576)}' /proc/meminfo; }
guarded() { # out err cmd...
  local out=$1 err=$2; shift 2
  until [ "$(avail)" -ge 30 ]; do sleep 30; done
  nice -n 10 "$@" > "$out" 2> "$err" & local pid=$!
  while kill -0 $pid 2>/dev/null; do
    if [ "$(avail)" -lt 30 ]; then kill $pid; echo "STOPPED pid $pid: MemAvailable < 30 GiB at $(date -u +%FT%TZ)" >> "$err"; fi
    sleep 10
  done
  wait $pid; echo "exit=$? $(date -u +%FT%TZ)" >> "$out.exit"
}
mkdir -p $OUT; cd $T
case $CH in
 c1) date -u +%FT%TZ > $OUT/start-c1.txt
     guarded $OUT/c1.txt $OUT/c1.err python3 c1_fact_fidelity.py $CEN $C $MAN --verify-sha256 ;;
 rs) date -u +%FT%TZ > $OUT/start-rs.txt
     guarded $OUT/control-final-replay.tsv $OUT/control.err python3 resid_scan.py $C $(tail -n +2 $MAN | cut -f2) ;;
 *) echo "chain?"; exit 1 ;;
esac
date -u +%FT%TZ > $OUT/done-$CH
