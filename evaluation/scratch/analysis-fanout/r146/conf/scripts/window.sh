#!/bin/bash
# r146 conf: the binary-run window (relay 146 HARD RULES). exit 0 = open; prints the reason and exits 1 otherwise.
MK=scratch/main/SLOT-FREE
ls worktrees/CORPUS-SLOT*.lock >/dev/null 2>&1 && { echo "window: corpus lock present"; exit 1; }
[ "$(awk '/MemAvailable/{print int($2/1048576)}' /proc/meminfo)" -ge 65 ] || { echo "window: MemAvailable < 65 GiB"; exit 1; }
grep -E '^main .*CENSUS (STARTED|ENDED)' $MK | tail -1 | grep -q 'CENSUS ENDED' || { echo "window: main census not ENDED"; exit 1; }
grep -E 'era-5c SCAN' $MK | tail -1 | grep -q 'SCAN END' || { echo "window: era-5c SCAN not END"; exit 1; }
# an assembler GATE START without a later END / LANDED / COMPOSED line for the same tag
python3 - "$MK" <<'PY' || exit 1
import re, sys
open_ = {}
for l in open(sys.argv[1], errors='replace'):
    m = re.search(r'assembler (\S+) GATE START', l)
    if m: open_[m.group(1)] = l.strip(); continue
    m = re.search(r'assembler (\S+) GATE END', l) or re.search(r'assembler (?:LANDED|COMPOSED) (\S+)', l)
    if m: open_.pop(m.group(1), None)
if open_:
    print('window: assembler GATE open: ' + '; '.join(open_.values())); sys.exit(1)
PY
exit 0
