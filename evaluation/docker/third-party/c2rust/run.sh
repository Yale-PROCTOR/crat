#!/bin/bash
# third-party step `c2rust`: c2rust 0.21.0-p1's translation time for the eight, with CROWN's flags (each program's unit
# is &inator's source.c; jccc adds -Isrc). 3 trials (one under --small), one at a time, one throw-away container per
# trial (--rm --network none); GNU time inside the container around `c2rust transpile` only (container start-up
# excluded): the minimum is rq3.inator.<q>.c2rust-s. Each trial's crate and compile_commands.json are compared with
# the translations of record (translations-sha256.tsv; the same files as the source tree's benchmarks/inator/).
# Needs the step `inator`'s benchmarks (or INATOR_BENCHMARKS). Writes c2rust/runs/<q>/t<k>/ (meta.txt with the
# identity line, inner.time, stdout, stderr; the crate is removed once it is checked) and c2rust-build.log.
set -euo pipefail
source "$(dirname "$0")/../lib/common.sh"
T=$THIRD_PARTY
IMG=tp-c2rust:0.21.0-p1
B=$T/inator/benchmarks
[ -f "$B/.ok" ] || die "c2rust needs the step inator first (&inator's benchmarks)"
if ! $DOCKER image inspect "$IMG" >/dev/null 2>&1; then
  log "build $IMG (upstream v0.21.0 + the patch; ~10 min)"
  $DOCKER build -t "$IMG" "$TP_HOME/c2rust" > "$T/c2rust-build.log" 2>&1 || die "c2rust build failed (c2rust-build.log)"
fi
gnu_time
N=$(trials_of 3)
for q in $EIGHT; do
  extra=(); [ "$q" = jccc ] && extra=(-Isrc)
  for k in $(seq 1 "$N"); do
    d=$T/c2rust/runs/$q/t$k
    [ -f "$d/meta.txt" ] && grep -q '^ident ' "$d/meta.txt" && continue
    rm -rf "$d"; mkdir -p "$d/out" "$d/$q.cc"; chmod -R 777 "$d"
    python3 -c 'import json,sys; tu=sys.argv[1]; print(json.dumps([{"directory": "/in", "arguments": ["cc", "-c", *sys.argv[2:], tu], "file": tu}], indent=1))' \
      source.c "${extra[@]}" > "$d/$q.cc/compile_commands.json"
    echo "start_utc=$(date -u +%FT%TZ) load=$(cut -d' ' -f1-3 /proc/loadavg)" > "$d/meta.txt"
    set +e
    $DOCKER run --rm --network none -v "$B/$q":/in:ro -v "$d/$q.cc":/cc:ro -v "$d/out":/out -v "$GNU_TIME":/opt/time:ro \
      --entrypoint /opt/time "$IMG" -v -o /out/inner.time \
      c2rust transpile --emit-modules --fail-on-error --reduce-type-annotations --emit-build-files -o "/out/$q" /cc/compile_commands.json \
      > "$d/stdout" 2> "$d/stderr"
    rc=$?; set -e
    echo "exit_code=$rc end_utc=$(date -u +%FT%TZ)" >> "$d/meta.txt"
    ident=$(python3 - "$d" "$q" "$TP_HOME/c2rust/translations-sha256.tsv" <<'PY'
import csv, hashlib, os, sys
d, q, m = sys.argv[1:4]
rows = [r for r in csv.DictReader(open(m), delimiter='\t') if r['program'] == q]
ok, bad = 0, []
for r in rows:
    p = r['path']
    f = os.path.join(d, p) if p.startswith(q + '.cc/') else os.path.join(d, 'out', p)
    if os.path.exists(f) and hashlib.sha256(open(f, 'rb').read()).hexdigest() == r['sha256']:
        ok += 1
    else:
        bad.append(p)
print(f"identical={ok}/{len(rows)}" + (f" differ={bad}" if bad else ""))
PY
)
    echo "ident $ident" >> "$d/meta.txt"
    mv "$d/out/inner.time" "$d/inner.time" 2>/dev/null || true
    rm -rf "$d/out"
    log "c2rust $q t$k exit=$rc inner=$(wall_of "$d/inner.time") $ident"
  done
done
log "c2rust done"
