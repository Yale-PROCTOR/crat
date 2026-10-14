#!/usr/bin/env python3
"""Bounded prefix reader for an era5b-model-cache-v1 entry: returns the head's
`universe` (list) and `model` (dict slot_key -> kind) WITHOUT loading the entry.

The entry is one JSON object whose top-level keys are, in order:
schema, key, inputs, functions, universe, model, baseline, receipt, exports, ...
(`exports` and later are the GB-sized tail). We read 4 MiB chunks, stop as soon as
the `"baseline":` key after `"model":` has been seen, and parse only the
`universe` and `model` values with json.JSONDecoder.raw_decode. A hard cap
(256 MiB of prefix) aborts the read rather than ever approaching the tail.
"""
import json

CHUNK = 4 << 20
CAP = 256 << 20


def read_head(path):
    dec = json.JSONDecoder()
    buf = b''
    with open(path, 'rb') as f:
        while True:
            m = buf.find(b',"model":')
            if m >= 0 and buf.find(b',"baseline":', m) >= 0:
                break
            if len(buf) > CAP:
                raise RuntimeError(f'{path}: model section not closed within {CAP} bytes')
            chunk = f.read(CHUNK)
            if not chunk:
                raise RuntimeError(f'{path}: EOF before model section closed')
            buf += chunk
    text = buf.decode('utf-8', errors='strict') if False else None
    # decode only the region we need
    u = buf.find(b',"universe":')
    m = buf.find(b',"model":')
    b = buf.find(b',"baseline":', m)
    universe, _ = dec.raw_decode(buf[u + len(b',"universe":'):m].decode())
    model, _ = dec.raw_decode(buf[m + len(b',"model":'):b].decode())
    prog = None
    i = buf.find(b'"program":"')
    if i >= 0:
        j = buf.find(b'"', i + 11)
        prog = buf[i + 11:j].decode()
    return prog, universe, model, len(buf)


if __name__ == '__main__':
    import sys
    p, u, m, n = read_head(sys.argv[1])
    import collections
    print(p, len(u), len(m), dict(collections.Counter(m.values())), 'prefix_bytes', n)
