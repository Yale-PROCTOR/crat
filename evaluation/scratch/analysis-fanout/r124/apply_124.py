#!/usr/bin/env python3
"""Relay 124 (S29, the user 10-09): the setup keys' print forms; host-ours / host-inator marked uncited."""
import sys
NR = sys.argv[1]
P = "analysis-fanout 102 (relay 124, S29, the user 2026-10-09): "
SET = {
 'setup.rustc': ('1.89.0-nightly', P + "print form '1.89.0-nightly' (no hash, no date); full version, kept here: 'rustc 1.89.0-nightly (be19eda0d 2025-06-22)' (rustc +nightly-2025-06-23 --version on host-a, 2026-10-09; channel nightly-2025-06-23 in the record's rust-toolchain.toml); "),
 'setup.host': ('an AMD Ryzen 9 9950X (16 cores, 32 threads) and 128 GiB of RAM', P + "print form as worded by the user (installed memory, no OS); verified on host-a, the host of every census of record, 2026-10-09: lscpu 'Model name: AMD Ryzen 9 9950X 16-Core Processor', 'Socket(s): 1', 'Core(s) per socket: 16', 'Thread(s) per core: 2', 'CPU(s): 32'; installed memory: lsmem 'Total online memory: 128G' (64 blocks of 2G, range 0x0-0x1fffffffff), four DMI type-17 memory devices; /proc/meminfo MemTotal 127011100 kB = 121.1 GiB is the memory left to the OS after firmware/kernel reservations (the old value's 121 GiB); detail kept here: Ubuntu 25.10, kernel 6.17.0-41-generic; host-b (RQ3's host) has the same CPU, RAM and OS (rq3-inator 001 section 3); "),
 'setup.host-ours': (None, P + "UNCITED: defined but no longer cited by the manuscript (S29; paper origin/main 61bf60b cites only setup.rustc and setup.host, evaluation.tex:51); "),
 'setup.host-inator': (None, P + "UNCITED: defined but no longer cited by the manuscript (S29; paper origin/main 61bf60b); "),
}
lines = open(NR).read().split('\n'); done = []
for i, l in enumerate(lines):
    for k, (v, pre) in SET.items():
        if l.startswith(f'| {k} |'):
            c = l.split(' | ')
            old = c[1]
            if v is not None: c[1] = v
            c[5] = pre + 'previously: value ' + repr(old) + '; ' + c[5]
            lines[i] = ' | '.join(c); done.append((k, old, c[1]))
assert len(done) == len(SET), done
open(NR, 'w').write('\n'.join(lines))
for d in done: print(d)
