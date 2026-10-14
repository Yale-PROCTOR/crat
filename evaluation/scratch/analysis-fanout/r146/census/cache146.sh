#!/bin/bash
# r146 / census: every cache product, for FRAME s39 (the CONTROL, the S39 cache) and 60sp (era5c-r215-kindorder).
# Streaming / bounded-head / mmap readers only; never a whole entry. MemAvailable >= 30 GiB before each step.
set -u
H=scratch/analysis-fanout/r146/census
W=$H/work; CA=$H/cache
AW=dev/worktrees
LOG=$H/cache146.status
memok() { while true; do m=$(awk '/MemAvailable/{print int($2/1048576)}' /proc/meminfo); [ $m -ge 30 ] && return; echo "$(date -u +%T) wait mem $m GiB" >> $LOG; sleep 60; done; }
st() { echo "$(date -u +%FT%TZ) $*" >> $LOG; }
N="nice -n 10 ionice -c2 -n7"
for F in s39 60sp; do
  case $F in s39) S=$AW/era5c-r211-s39pp; C=scratch/main/batch58pps39;; 60sp) S=$AW/era5c-r215-kindorder; C=scratch/main/batch60sp;; esac
  export FRAME=$F
  memok; st "$F keymap start"
  ( cd $W/g088b/keymap141 && $N python3 build_keymap.py > run-$F.out 2> run-$F.err ); st "$F keymap rc=$?"
  memok; st "$F qfacts start"
  $N python3 $CA/qfacts/qfacts_stream.py $S $CA/qfacts/qfacts-$F.tsv 2> $CA/qfacts/stream-$F.log; st "$F qfacts rc=$?"
  memok; st "$F s17 start"
  $N python3 $CA/s17/final_discharges.py $S $CA/s17/out-$F > $CA/s17/extract-$F.log 2>&1; st "$F s17 rc=$?"
  memok; st "$F s9 start"
  $N python3 $CA/s9/readers.py > $CA/s9/readers-$F.out 2> $CA/s9/readers-$F.err; st "$F s9 readers rc=$?"
  $N python3 $CA/s9/replay.py > $CA/s9/replay-$F.out 2> $CA/s9/replay-$F.err; st "$F s9 replay rc=$?"
  memok; st "$F s16 start"
  bash $CA/s16/drive141.sh $F $S; st "$F s16 rc=$?"
  memok; st "$F layers start"
  mkdir -p $W/out146
  ( cd $W && $N python3 d6prod/layers141.py $C $S $W/out146/layers-$F.tsv 2> $W/out146/layers-$F.log ); st "$F layers rc=$?"
  memok; st "$F reader start"
  mkdir -p $CA/reader/$F
  PYTHONPATH=home/.cache/uv/archive-v0/0r-DC3CyAKin9PcT READER_SOLVE=$S READER_OUT=$CA/reader/$F $N python3 $CA/reader/read_records.py > $CA/reader/$F/run.out 2> $CA/reader/$F/run.err; st "$F reader rc=$?"
done
st ALLDONE
