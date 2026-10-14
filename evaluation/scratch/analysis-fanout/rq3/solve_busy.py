#!/usr/bin/env python3
"""Count running processes of the L01^11 solve (its sealed binary lives under target-l01p11 / the night-solve dir).
The pattern lives in this file, never on a command line (census-launcher pgrep hazard)."""
import os
PAT = ('target-l01p11', 'target-l01p12', 'target-l01p13', 'night-solve/')
n = 0
for pid in os.listdir('/proc'):
    if not pid.isdigit() or int(pid) == os.getpid():
        continue
    try:
        exe = open(f'/proc/{pid}/cmdline', 'rb').read().split(b'\0')[0].decode(errors='replace')
    except OSError:
        continue
    if any(p in exe for p in PAT):
        n += 1
print(n)
