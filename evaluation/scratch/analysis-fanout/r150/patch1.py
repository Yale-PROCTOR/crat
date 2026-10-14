p = "scratch/analysis-fanout/r150/apply_150.py"
s = open(p).read()
Q3 = "'" * 3


def rep(a, b):
    global s
    assert s.count(a) == 1, a[:70]
    s = s.replace(a, b)


rep('ROW = re.compile(r"^\\| (?P<key>[^|]*?) \\| (?P<value>[^|]*?) \\| (?P<status>[^|]*?) \\| (?P<layer>[^|]*?) "\n'
    '                 r"\\| (?P<unit>[^|]*?) \\| (?P<prov>.*) \\|$")',
    'ROW = re.compile(r"^\\| (?P<key>[^|]*?) \\| (?P<value>[^|]*?) \\| (?P<status>[^|]*?) \\| (?P<layer>[^|]*?) "\n'
    '                 r"\\| (?P<unit>[^|]*?) \\| (?P<prov>.*) \\|$")\n'
    'LOOSE = re.compile(r"^\\| (?P<key>[^ |]+) \\|")   # any table row, an empty value cell \'| |\' included')
rep('for i, l in enumerate(lines):\n    m = ROW.match(l)\n    if m and not l.startswith("| key |"):',
    'for i, l in enumerate(lines):\n    m = LOOSE.match(l)\n    if m and not l.startswith("| key |") and not l.startswith("|---"):')
rep('''def note(k, text):
    c = ROW.match(out[rows[k]]).groupdict()
    if "|" in text:
        die("pipe in note " + k)
    c["prov"] = text + c["prov"]
    out[rows[k]] = render(c)
    log.append((k, "note", c["value"], c["value"]))''',
    '''def note(k, text):
    """insert text at the start of the provenance cell (after the 6th '|' and its space); every other byte kept."""
    l = out[rows[k]]
    if "|" in text:
        die("pipe in note " + k)
    pos = [i for i, ch in enumerate(l) if ch == "|"]
    if len(pos) < 7:
        die("cells " + k)
    j = pos[5] + 2
    out[rows[k]] = l[:j] + text + l[j:]
    v = l[pos[1] + 1:pos[2]].strip()
    log.append((k, "note", v, v))''')
old_tw = s[s.index('TWENTY = T % 3 + ('):s.index('cls = {}')]
new_tw = ('TWENTY = T % 3 + ("TWENTY-program key of the frame-14u RQ4 design (the earlier whole-corpus runs; NOT of record "\n'
          '                  "under R817, whatever census a value was last re-derived at); the paper cites the six only: "\n'
          '                  "section RQ3 and Appendix C should not print it; ")\n'
          'CONFIG = T % 3 + ("SETTING as the frame-14u run\'s facts state it (wave-6o 097, the twenty-program design: pass C, "\n'
          '                  "harness-edits.txt); whether the six-program runs (wave-6o 118 / 149 / 151) used the same flags is "\n'
          '                  "not shown in this row\'s provenance -- wave-6o confirms before the paper prints it (Appendix C "\n'
          '                  "tab:rq4-config); ")\n'
          'CENSUS = T % 3 + ("CENSUS LABEL: names the frame-14u census (4a47f16f7, the L01^14u cache), the one the RQ4 runs "\n'
          '                  "last ran on; for the paper\'s six at 60s\' the trees are byte-identical to 58" + "\'" * 3 + " ("\n'
          '                  + W151 + "), so the census of record for the six is main/batch60sp -- the seat restates the "\n'
          '                  "value before Appendix C prints it; ")\n')
s = s.replace(old_tw, new_tw)
rep('''    elif k in ("rq4.checker", "rq4.config", "rq4.discipline"):
        cls[k] = SET''', '''    elif k in ("rq4.checker", "rq4.discipline"):
        cls[k] = SET
    elif k == "rq4.config":
        cls[k] = CONFIG
    elif k == "rq4.census":
        cls[k] = CENSUS''')
rep('''"notes", sum(1 for x in log if x[1] == "note"), "rq4 six/set/twenty",
      sum(1 for v in cls.values() if v is SIX), sum(1 for v in cls.values() if v is SET),
      sum(1 for v in cls.values() if v is TWENTY))''', '''"notes", sum(1 for x in log if x[1] == "note"), "rq4 six/set/config/census/twenty",
      sum(1 for v in cls.values() if v is SIX), sum(1 for v in cls.values() if v is SET),
      sum(1 for v in cls.values() if v is CONFIG), sum(1 for v in cls.values() if v is CENSUS),
      sum(1 for v in cls.values() if v is TWENTY), "rq4 rows", len(cls))''')
open(p, "w").write(s)
print("patched")
