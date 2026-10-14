#!/usr/bin/env python3
"""Crude PDF text extraction (read-only): inflate FlateDecode streams, pull Tj/TJ strings.
Usage: pdftxt.py in.pdf > out.txt"""
import re, sys, zlib
data = open(sys.argv[1], 'rb').read()
out = []
for m in re.finditer(rb'stream\r?\n', data):
    s = m.end()
    e = data.find(b'endstream', s)
    if e < 0: continue
    raw = data[s:e]
    try:
        dec = zlib.decompress(raw)
    except Exception:
        try: dec = zlib.decompressobj().decompress(raw)
        except Exception: continue
    if b'BT' not in dec: continue
    line = []
    for tm in re.finditer(rb'\[(.*?)\]\s*TJ|\((.*?)(?<!\\)\)\s*Tj|(T\*|Td|TD|ET)', dec, re.S):
        if tm.group(1) is not None:
            parts = re.findall(rb'\(((?:\\.|[^\\)])*)\)|(-?\d+\.?\d*)', tm.group(1))
            for p, num in parts:
                if p: line.append(p)
                elif num and float(num) < -200: line.append(b' ')
        elif tm.group(2) is not None:
            line.append(tm.group(2))
        else:
            line.append(b'\n')
    txt = b''.join(line)
    txt = re.sub(rb'\\([()\\])', rb'\1', txt)
    out.append(txt.decode('latin-1'))
sys.stdout.write('\n'.join(out))
