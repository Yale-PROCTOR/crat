#!/usr/bin/env python3
"""restamp_119.py -- analysis-fanout 120 (relay 147 item 3): 119's 36 rq3.inator.<p>.types.ours.* rows were written at
the composed 60s' head; 60s' landed as the same 32d966b9f, so their provenance becomes 'landed'. Values unchanged.
usage: restamp_119.py <landed-at UTC> <assembler report>   (rewrites r146/apply/record-60sp.md in place; fails closed)"""
import hashlib, re, sys

LANDED_AT, ASSEMBLER = sys.argv[1], sys.argv[2]
PATH = "scratch/analysis-fanout/r146/apply/record-60sp.md"
OLD = ("at the composed head 32d966b9f (NOT a landed head: the composed 60s' head 32d966b9f that main 225 censused, "
       "relay 145's fallback at 10-14 00:00Z (the landing is held for the user's word, assembler 150a))")
NEW = ("at the landed head 32d966b9f (60s' landed on borrow-ownership %s, assembler %s, R1088-1; measured 10-14 "
       "00:02-00:11Z at this same head before the landing, relay 145's fallback; re-stamped landed by analysis-fanout 120 "
       "(relay 147): the values stand, the nine's half not re-run)" % (LANDED_AT, ASSEMBLER))
ROW = re.compile(r"^\| (rq3\.inator\.[a-z-]+\.types\.ours\.(ref|mut|box|raw)) \| ([^|]*) \|")


def die(m):
    raise SystemExit("restamp_119: FAIL: " + m)


text = open(PATH, encoding="utf-8").read()
lines = text.split("\n")
hits = []
for i, l in enumerate(lines):
    if OLD in l:
        m = ROW.match(l)
        if not m:
            die("the fragment outside a rq3.inator.<p>.types.ours.* row: line %d" % (i + 1))
        if l.count(OLD) != 1:
            die("fragment twice on line %d" % (i + 1))
        new = l.replace(OLD, NEW)
        if ROW.match(new).group(3) != m.group(3) or new.count("|") != l.count("|"):
            die("value or cells moved: " + m.group(1))
        lines[i] = new
        hits.append(m.group(1))
if len(hits) != 36 or len(set(hits)) != 36:
    die("hit %d rows" % len(hits))
if "composed head" in "\n".join(l for l in lines if l.startswith("| rq3.inator.")):
    die("a composed-head mention remains")
out = "\n".join(lines)
open(PATH, "w", encoding="utf-8", newline="").write(out)
print("re-stamped", len(hits), "rows; in md5", hashlib.md5(text.encode()).hexdigest(), "out md5",
      hashlib.md5(out.encode()).hexdigest())
