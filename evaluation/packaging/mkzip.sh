#!/bin/bash
# usage: W=<worktree> ZS=<scratch> mkzip.sh -> copies the worktree (minus .git and target) to $ZS/stage/jobcrat-source, zips it with Python zipfile (deterministic order), unzips to $ZS/unzipped, prints facts
set -u
W=${W:?the derivation worktree}
S=${ZS:?the scratch directory}
rm -rf "$S/stage" "$S/unzipped"
mkdir -p "$S/stage/jobcrat-source" "$S/unzipped"
tar -C "$W" --exclude=.git --exclude=target -cf - . | tar -C "$S/stage/jobcrat-source" -xf -
find "$S/stage/jobcrat-source" -type f | wc -l > "$S/zip-file-count.txt"
rm -f "$S/jobcrat-source.zip"
python3 -I - "$S/stage" "$S/jobcrat-source.zip" <<'PY'
import os, sys, zipfile
root, out = sys.argv[1], sys.argv[2]
with zipfile.ZipFile(out, 'w', zipfile.ZIP_DEFLATED) as z:
    for dp, dn, fn in os.walk(root):
        dn.sort()
        for f in sorted(fn):
            p = os.path.join(dp, f)
            z.write(p, os.path.relpath(p, root))
PY
ls -l "$S/jobcrat-source.zip"
sha256sum "$S/jobcrat-source.zip"
echo "files staged: $(cat $S/zip-file-count.txt)"
echo "entries: $(unzip -Z1 $S/jobcrat-source.zip | wc -l)"
unzip -q "$S/jobcrat-source.zip" -d "$S/unzipped"
diff -r "$S/stage/jobcrat-source" "$S/unzipped/jobcrat-source" && echo "unzipped tree identical to the staged copy"
unzip -l "$S/jobcrat-source.zip" | head -40 > "$S/zip-listing-head.txt"
