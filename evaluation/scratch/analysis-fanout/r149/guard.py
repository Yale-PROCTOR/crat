#!/usr/bin/env python3
"""guard.py -- exit 0 when the lane's run window is open, else print why and exit 1.
Window: no CORPUS-SLOT*.lock; MemAvailable >= 65 GiB; the last main CENSUS STARTED/ENDED line is ENDED; the last era-5c
SCAN line is END; no GATE START without a later GATE END for the same lane and tag; the host idle (1-min load < 2.0 and
no rustc / cargo / z3 / crat-family / crown / resolve-lifetimes / miri / cc1 / ld process)."""
import glob, re, sys

M = "scratch/main/SLOT-FREE"
why = []
if glob.glob("worktrees/CORPUS-SLOT*.lock"):
    why.append("corpus lock")
mem = int(re.search(r"MemAvailable:\s+(\d+)", open("/proc/meminfo").read()).group(1))
if mem < 65 * 1024 * 1024:
    why.append("MemAvailable %.1f GiB" % (mem / 1024 / 1024))
lines = open(M, encoding="utf-8", errors="replace").read().splitlines()
cen = [l for l in lines if re.match(r"^main .*CENSUS (STARTED|ENDED)", l)]
if cen and "CENSUS STARTED" in cen[-1]:
    why.append("main census open")
scan = [l for l in lines if " era-5c SCAN " in l and re.search(r"SCAN (START|END)", l)]
if scan and "SCAN START" in scan[-1]:
    why.append("era-5c scan open")
open_g = {}
for l in lines:
    m = re.match(r"^\S+ (\S+) (\S+) GATE (START|END)\b", l)
    if m:
        k = (m.group(1), m.group(2))
        if m.group(3) == "START":
            open_g[k] = l
        else:
            open_g.pop(k, None)
if open_g:
    why.append("open gate: " + "; ".join(" ".join(k) for k in open_g))
la1 = float(open("/proc/loadavg").read().split()[0])
busy = []
import os
for d in os.listdir("/proc"):
    if d.isdigit():
        try:
            c = open("/proc/%s/comm" % d).read().strip()
        except OSError:
            continue
        if c in ("rustc", "cargo", "z3", "crown", "resolve-lifetim", "miri", "cc1", "ld") or c.startswith(("crat", "pointer_repl", "big_census", "boc1")):
            busy.append(c)
if busy or la1 >= 2.0:
    why.append("host not idle (load1 %.2f; %s)" % (la1, ",".join(sorted(set(busy))) or "-"))
if why:
    print("CLOSED: " + ", ".join(why))
    sys.exit(1)
print("OPEN")
