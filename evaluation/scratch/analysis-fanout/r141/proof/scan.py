"""relay 141 item 3: comment- and string-stripped scan of the _CoqProject theories for unproved vernacular."""
import re, subprocess, sys
P = "crat-proof"
WORDS = ["Admitted", "admit", "give_up", "Axiom", "Axioms", "Parameter", "Parameters", "Conjecture"]
def git(*a):
    return subprocess.run(["git", "-C", P] + list(a), capture_output=True, text=True, check=True).stdout
def strip(s):
    out, i, depth, n = [], 0, 0, len(s)
    instr = False
    while i < n:
        if not instr and s.startswith("(*", i):
            depth += 1; i += 2; continue
        if depth and s.startswith("*)", i):
            depth -= 1; i += 2; continue
        if depth:
            i += 1; continue
        if s[i] == '"':
            instr = not instr; i += 1; continue
        if not instr:
            out.append(s[i])
        i += 1
    return "".join(out)
c = sys.argv[1]
files = [l for l in git("show", c + ":_CoqProject").splitlines() if re.match(r"^theories/.*\.v$", l)]
hits = {w: 0 for w in WORDS}
lines = 0
for f in files:
    t = git("show", c + ":" + f)
    lines += t.count("\n")
    s = strip(t)
    for w in WORDS:
        hits[w] += len(re.findall(r"(?<![A-Za-z0-9_'.])" + w + r"(?![A-Za-z0-9_'])", s))
print(c, "files", len(files), "lines", lines, hits)
