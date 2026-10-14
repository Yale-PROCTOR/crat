#!/bin/bash
set -u
H=scratch/analysis-fanout/r146/census; W=$H/work; CA=$H/cache; S=worktrees/era5c-r215-kindorder
export FRAME=60sp
N="nice -n 10 ionice -c2 -n7"
( cd $W/g088b/keymap141 && $N python3 build_keymap.py > run-60sp.out 2> run-60sp.err ); echo "keymap rc=$?" >> $H/pre60.status
$N python3 $CA/qfacts/qfacts_stream.py $S $CA/qfacts/qfacts-60sp.tsv 2> $CA/qfacts/stream-60sp.log; echo "qfacts rc=$?" >> $H/pre60.status
$N python3 $CA/s17/final_discharges.py $S $CA/s17/out-60sp > $CA/s17/extract-60sp.log 2>&1; echo "s17 rc=$?" >> $H/pre60.status
echo done >> $H/pre60.status
