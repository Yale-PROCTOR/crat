#!/usr/bin/env bash
# The repair-round runs for the paper's example (analysis-fanout relays 009/010/012): libtree B, libtree A, avl B, avl A, then the Mode-A A5-off control C for both.
# One program at a time, one thread, 16 GiB cap, nice 10 / ionice -c3, a private TMPDIR under r6/; never the frame cache. Launch from tmux after lil's inner solve releases the slot.
set -u; R=scratch/analysis-fanout/r6; L=$R/run-all.log
for spec in "libtree B" "libtree A" "avl B" "avl A" "libtree C" "avl C"; do set -- $spec; echo "$(date -u +%FT%TZ) start $1 $2" >> $L; bash $R/run-one.sh "$1" "$2" >> $L 2>&1; echo "$(date -u +%FT%TZ) end $1 $2 (status: $(cat $R/runs/$1-$2/status.txt 2>/dev/null || echo ok))" >> $L; done
echo "$(date -u +%FT%TZ) all done" >> $L
