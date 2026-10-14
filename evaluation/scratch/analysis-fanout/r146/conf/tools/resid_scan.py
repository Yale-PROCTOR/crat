#!/usr/bin/env python3
"""Read-only streaming scan of era5b-model-cache-v1 entries.

Per cache file it reports: program; residual-conflicts availability/source_rows
(+ a head of the records when non-empty); counts of "invalid":true / false
(the E-R4 `loans` family is the only producer of that key); and the sequence of
retirement review records (conflicts / demotions / unresolved emptiness and
ordinary_error_points, with the round number, or FINAL when absent).
"""
import os
import re
import sys

CHUNK = 64 << 20
K = 512

P_PROG = re.compile(rb'"inputs":\{"program":"([^"]+)"')
P_ALL = re.compile(
    rb'\{"fields":\{"conflicts":\[(.)'
    rb'|"demotions":\[(.)'
    rb'|"unresolved":\[(.)'
    rb'|"ordinary_error_points":(\d+)(?:,"round":(\d+))?'
    rb'|"invalid":(true|false)'
    rb'|"residual-conflicts":\{"availability":\{"state":"(\w+)"'
)
P_SRC = re.compile(rb'"source_rows":(\d+)\}')


def scan(path):
    size = os.path.getsize(path)
    prog = None
    res_off = None
    res_state = None
    inv = {b"true": 0, b"false": 0}
    events = []
    with open(path, "rb") as fh:
        pos = 0          # file offset of buf[0]
        buf = b""
        eof = False
        while not eof:
            data = fh.read(CHUNK)
            if not data:
                eof = True
            buf = buf + data
            limit = len(buf) if eof else max(0, len(buf) - K)
            if prog is None:
                m = P_PROG.search(buf)
                if m:
                    prog = m.group(1).decode()
            for m in P_ALL.finditer(buf, 0, len(buf)):
                if m.start() >= limit:
                    break
                g = m.groups()
                if g[0] is not None:
                    events.append(("C", g[0] != b"]"))
                elif g[1] is not None:
                    events.append(("D", g[1] != b"]"))
                elif g[2] is not None:
                    events.append(("U", g[2] != b"]"))
                elif g[3] is not None:
                    events.append(("E", int(g[3]), None if g[4] is None else int(g[4])))
                elif g[5] is not None:
                    inv[g[5]] += 1
                elif g[6] is not None and res_off is None:
                    res_off = pos + m.end()
                    res_state = g[6].decode()
            pos += limit
            buf = buf[limit:]
    res = None
    if res_off is not None:
        with open(path, "rb") as fh:
            fh.seek(res_off)
            blob = fh.read(64 << 20)
        ms = P_SRC.search(blob)
        if ms:
            res = (res_state, int(ms.group(1)), blob[:ms.start()][:1500])
        else:
            res = (res_state, -1, blob[:1500])
    return prog, size, res, inv[b"true"], inv[b"false"], events


def summarize(events):
    recs = []
    cur = {}
    for ev in events:
        if ev[0] == "C":
            cur = {"conflicts": ev[1]}
        elif ev[0] == "D":
            cur.setdefault("demotions", ev[1])
        elif ev[0] == "E":
            if "conflicts" in cur and "oep" not in cur:
                cur["oep"] = ev[1]
                cur["round"] = ev[2]
        elif ev[0] == "U":
            if "oep" in cur:
                cur["unresolved"] = ev[1]
                recs.append(cur)
            cur = {}
    return recs


def main():
    d = sys.argv[1]
    files = sorted(f for f in os.listdir(d) if f.endswith(".json"))
    if len(sys.argv) > 2:
        files = [f for f in files if f.startswith(tuple(sys.argv[2:]))]
    print("program\tbytes\tresidual_state\tresidual_rows\tloans_invalid_true\tloans_invalid_false"
          "\tretire_rounds\tfinal_conflicts_nonempty\tfinal_demotions_nonempty"
          "\tfinal_unresolved_nonempty\tfinal_ordinary_error_points\tround_oeps\tfile", flush=True)
    for f in files:
        prog, size, res, it, iff, events = scan(os.path.join(d, f))
        recs = summarize(events)
        final = [r for r in recs if r.get("round") is None]
        rounds = [r for r in recs if r.get("round") is not None]
        fin = final[-1] if final else {}
        print("\t".join(str(x) for x in [
            prog, size,
            res[0] if res else "absent", res[1] if res else "absent",
            it, iff, len(rounds),
            fin.get("conflicts"), fin.get("demotions"), fin.get("unresolved"),
            fin.get("oep"),
            ",".join(str(r.get("oep")) for r in rounds),
            f]), flush=True)
        if res and res[1] not in (0,):
            sys.stderr.write(f"{prog} residual head: {res[2][:1500]!r}\n")


if __name__ == "__main__":
    main()
