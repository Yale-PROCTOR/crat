#!/bin/bash
# r146 conf (re-pointed r141 run_py.sh): wave-6o C2/C3/C4 (python only, no rustc) at a census.
# usage: run_py.sh <census-dir> <out-dir> <contracts-src>
set -u
export PYTHONDONTWRITEBYTECODE=1
CENSUS=$1; OUT=$2; SRC=$3
T=scratch/analysis-fanout/r146/conf/tools
mkdir -p $OUT; cd $T
date -u +%FT%TZ > $OUT/start.txt
nice -n 10 python3 c2_retained_lifecycle.py "$CENSUS" crat/benchmarks/rs-crown-derived > "$OUT/c2.txt" 2> "$OUT/c2.err"
nice -n 10 python3 c3_form_conformance.py "$CENSUS" > "$OUT/c3.txt" 2> "$OUT/c3.err"
nice -n 10 python3 c3_form_conformance.py "$CENSUS" --table > "$OUT/c3-table.tsv" 2>> "$OUT/c3.err"
nice -n 10 python3 c4_core_coverage.py "$CENSUS" --kinds --contracts "$SRC" > "$OUT/c4.txt" 2> "$OUT/c4.err"
nice -n 10 python3 c4_core_coverage.py "$CENSUS" --contracts "$SRC" > "$OUT/c4-receipts.txt" 2> "$OUT/c4-receipts.err"
date -u +%FT%TZ > $OUT/done-py
