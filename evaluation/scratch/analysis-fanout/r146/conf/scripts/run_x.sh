#!/bin/bash
# r146 conf (re-pointed r141 run_x.sh): wave-6o's C2b (--panic-abort) and X instruments on a census's emitted trees;
# one rustc --emit=mir at a time, nice 10, no lock. Fails closed if the run window does not hold.
# usage: run_x.sh <census-dir> <out-dir> <label>
set -u
export PYTHONDONTWRITEBYTECODE=1
C=$1; X=$2; LBL=$3
O=scratch/analysis-fanout/r146/conf; T=$O/tools; D=crat/deps_crate/target/debug/deps
MK=scratch/main/SLOT-FREE
bash $O/scripts/window.sh || exit 1
mkdir -p $X
echo "$(date -u +%FT%TZ) analysis-fanout run START (relay 146): wave-6o's C2b + X conformance instruments on $LBL; one rustc --emit=mir at a time, nice 10; no lock" >> $MK
cd $T
date -u +%FT%TZ > $X/start.txt
nice -n 10 python3 c2b_implicit_release.py $C $X/c2b $D --panic-abort > $X/c2b.txt 2> $X/c2b.err; echo "c2b rc=$?" >> $X/rc.txt
nice -n 10 python3 x_instruments.py $C $X/x $D > $X/x.txt 2> $X/x.err; echo "x rc=$?" >> $X/rc.txt
date -u +%FT%TZ > $X/done
echo "$(date -u +%FT%TZ) analysis-fanout run END (relay 146): C2b + X on $LBL" >> $MK
