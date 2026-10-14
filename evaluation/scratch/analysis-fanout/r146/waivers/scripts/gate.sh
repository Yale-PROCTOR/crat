#!/bin/bash
# gate.sh: the lane's preconditions for a binary run; exit 0 only when all hold
F=scratch/main/SLOT-FREE
ls worktrees/CORPUS-SLOT*.lock >/dev/null 2>&1 && { echo "lock present"; exit 1; }
m=$(awk '/MemAvailable/{print int($2/1048576)}' /proc/meminfo); [ "$m" -ge 65 ] || { echo "MemAvailable $m"; exit 1; }
l=$(grep -E '^main .*CENSUS (STARTED|ENDED)' $F | tail -1); echo "$l" | grep -q 'CENSUS ENDED' || [ -z "$l" ] || { echo "main census: $l"; exit 1; }
s=$(grep 'era-5c SCAN' $F | tail -1); [ -z "$s" ] || echo "$s" | grep -qE 'SCAN END|SCAN.*\bEND\b' || { echo "era-5c scan: $s"; exit 1; }
# assembler: the last GATE START must be followed by a GATE END / LANDED / COMPOSED line
gs=$(grep -n 'assembler .*GATE START' $F | tail -1 | cut -d: -f1)
if [ -n "$gs" ]; then tail -n +$((gs+1)) $F | grep -qE 'assembler .*(GATE END|LANDED|COMPOSED)' || { echo "assembler gate open at line $gs"; exit 1; }; fi
echo "gate ok MemAvailable $m; main: ${l:0:100}; era-5c: ${s:0:100}"
