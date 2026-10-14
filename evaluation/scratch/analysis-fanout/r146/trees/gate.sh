#!/bin/bash
# gate (relay 146): no corpus lock, MemAvailable >= 65 GiB, last main CENSUS line ENDED, last era-5c SCAN line END,
# no assembler GATE START without a later GATE END / LANDED / COMPOSED line
SF=scratch/main/SLOT-FREE
ls worktrees/CORPUS-SLOT*.lock >/dev/null 2>&1 && { echo "GATE: lock present"; exit 1; }
m=$(awk '/MemAvailable/{print int($2/1048576)}' /proc/meminfo); [ "$m" -ge 65 ] || { echo "GATE: mem $m GiB"; exit 1; }
c=$(grep -E '^main .*CENSUS (STARTED|ENDED)' $SF | tail -1); echo "$c" | grep -q 'ENDED' || { echo "GATE: census $c"; exit 1; }
e=$(grep 'era-5c SCAN' $SF | tail -1); echo "$e" | grep -q 'SCAN END' || { echo "GATE: era5c $e"; exit 1; }
a=$(grep -nE 'assembler .*GATE START' $SF | tail -1 | cut -d: -f1)
if [ -n "$a" ]; then
  tail -n +"$a" $SF | grep -qE 'assembler .*(GATE END|LANDED|COMPOSED)' || { echo "GATE: assembler gate open (line $a)"; exit 1; }
fi
echo "GATE OK mem=${m}GiB"
