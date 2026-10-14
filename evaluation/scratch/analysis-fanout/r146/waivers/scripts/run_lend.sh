#!/bin/bash
# r146: pure Python streaming over the 58''' (S39) cache (control) and 60s' (60-KINDORDER) cache; 64 MiB chunks; no binary.
# Each cache's 20 entries are checked against the census manifest first (fingerprint = file name).
S=scratch/analysis-fanout/r146/waivers; O=$S/out146; M=scratch/main
for x in batch58pps39:era5c-r211-s39pp batch60sp:era5c-r215-kindorder; do
  n=${x%%:*}; c=worktrees/${x#*:}/cache/era5b-model-cache-v1
  a=$(ls $c/*.json | xargs -n1 basename | sed 's/\.json$//' | sort); b=$(tail -n +2 $M/$n-manifest.tsv | cut -f2 | sort)
  [ "$a" = "$b" ] || { echo "MANIFEST MISMATCH $n" > $O/lend-$n.out; exit 1; }
  m=$(awk '/MemAvailable/{print int($2/1048576)}' /proc/meminfo); [ $m -ge 30 ] || { echo "MemAvailable $m < 30, stop" > $O/lend-$n.out; exit 1; }
  nice -n 10 python3 $S/scripts/lend_waiver_sites.py $c > $O/lend-$n.out 2>&1 || { echo "FAILED $n" >> $O/lend-$n.out; exit 1; }
done
echo done > $O/lend.done
