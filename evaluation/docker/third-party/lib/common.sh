# third-party/lib/common.sh -- sourced by every step. Paths, the downloads, the static GNU time, the program lists.
#   SRC          the source root (default: the current directory)
#   RESULTS      default $SRC/results
#   THIRD_PARTY  default $RESULTS/third-party (every step writes only below it)
#   TP_DOWNLOADS default $THIRD_PARTY/downloads (the fetched archives, ~8.5 GB)
#   DOCKER       default docker
#   SMALL        1 under --small
#   TRIALS       the per-tool trial count of record unless set (--trials N)
TP_HOME=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
SRC=${SRC:-$(pwd)}
RESULTS=${RESULTS:-$SRC/results}
THIRD_PARTY=${THIRD_PARTY:-$RESULTS/third-party}
TP_DOWNLOADS=${TP_DOWNLOADS:-$THIRD_PARTY/downloads}
DOCKER=${DOCKER:-docker}
SMALL=${SMALL:-0}
TRIALS=${TRIALS:-}
mkdir -p "$THIRD_PARTY" "$TP_DOWNLOADS"
THIRD_PARTY=$(cd "$THIRD_PARTY" && pwd)
TP_DOWNLOADS=$(cd "$TP_DOWNLOADS" && pwd)
GNU_TIME=$THIRD_PARTY/bin/gnu-time-1.9-static

# CROWN's twenty, in the record's order; the json.h directory is keyed `jsonh`.
TWENTY="avl binn brotli bst buffer bzip2 genann heman ht json.h libcsv libtree libzahl lil lodepng quadtree rgba robotfindskitten tulipindicators urlparser"
# &inator's eight (its running example is not one of them).
EIGHT="ulidgen leftpad amp nandc rbtree carrays jccc tisp"
if [ "$SMALL" = 1 ]; then
  TWENTY_RUN=$(echo $TWENTY | tr ' ' '\n' | grep -vx -e lil -e brotli | tr '\n' ' ')
  EIGHT_INATOR="ulidgen leftpad amp nandc carrays"   # rbtree 615 s, jccc 5,775 s, tisp 13,088 s on the record's host
else
  TWENTY_RUN=$TWENTY
  EIGHT_INATOR=$EIGHT
fi

log() { echo "$(date -u +%FT%TZ) $*" | tee -a "$THIRD_PARTY/run.log" >&2; }
die() { log "ERROR: $*"; exit 1; }
key_of() { [ "$1" = json.h ] && echo jsonh || echo "$1"; }
trials_of() { [ -n "$TRIALS" ] && echo "$TRIALS" || { [ "$SMALL" = 1 ] && echo 1 || echo "$1"; }; }

# wall seconds from a GNU time -v report
wall_of() {
  awk -F': ' '/Elapsed \(wall clock\)/{n=split($2,a,":"); s=0; for(i=1;i<=n;i++) s=s*60+a[i]; print s}' "$1" 2>/dev/null
}

# fetch <name>: one row of sources.tsv into $TP_DOWNLOADS, checked by size and digest. A file already there (fetched
# earlier, or placed there beforehand, also as a symbolic link) is used when it checks; a partial one is resumed.
check_file() {  # file bytes digest
  if [ "$2" != - ] && [ "$(stat -L -c %s "$1")" != "$2" ]; then return 1; fi
  case $3 in
    md5:*) [ "$(md5sum "$1" | cut -d' ' -f1)" = "${3#md5:}" ] ;;
    sha256:*) [ "$(sha256sum "$1" | cut -d' ' -f1)" = "${3#sha256:}" ] ;;
    *) return 0 ;;   # files:<manifest>: checked file by file after unpacking
  esac
}
fetch() {
  local name=$1 row url bytes digest f i
  row=$(awk -F'\t' -v n="$name" '$1==n' "$TP_HOME/sources.tsv")
  [ -n "$row" ] || die "no source named $name"
  url=$(cut -f2 <<<"$row"); bytes=$(cut -f3 <<<"$row"); digest=$(cut -f4 <<<"$row")
  f=$TP_DOWNLOADS/$name
  [ -f "$f.ok" ] && return 0
  if [ -f "$f" ] && { [ "$bytes" = - ] || [ "$(stat -L -c %s "$f")" -ge "$bytes" ]; }; then
    check_file "$f" "$bytes" "$digest" && { touch "$f.ok"; log "using $name (already present, $digest)"; return 0; }
    rm -f "$f"   # complete in size but not in content: fetch it again
  fi
  log "fetch $name ($url)"
  for i in $(seq 1 30); do   # Zenodo can be slow and drop long transfers: resume until complete
    curl -fL --retry 5 --retry-delay 10 -C - -o "$f" "$url" && break
    [ "$bytes" != - ] && [ -f "$f" ] && [ "$(stat -L -c %s "$f")" -ge "$bytes" ] && break
    log "fetch $name: interrupted at $(stat -L -c %s "$f" 2>/dev/null || echo 0) bytes, resuming ($i)"; sleep 10
  done
  check_file "$f" "$bytes" "$digest" || die "$name: size or digest differs from the record (expected $bytes bytes, $digest)"
  touch "$f.ok"; log "fetched $name ($(stat -L -c %s "$f") bytes, $digest)"
}

# the image GNU time is built in: Ubuntu 22.04 (pinned) with a C toolchain
TP_BUILD_BASE=ubuntu:22.04@sha256:104ae83764a5119017b8e8d6218fa0832b09df65aae7d5a6de29a85d813da2fb
TP_BUILD_IMAGE=tp-build:22.04
build_image() {
  $DOCKER image inspect "$TP_BUILD_IMAGE" >/dev/null 2>&1 && return 0
  log "build $TP_BUILD_IMAGE"
  printf 'FROM %s\nRUN apt-get update && apt-get install -y --no-install-recommends build-essential ca-certificates && rm -rf /var/lib/apt/lists/*\n' \
    "$TP_BUILD_BASE" | $DOCKER build -q -t "$TP_BUILD_IMAGE" - >/dev/null || die "build image failed"
}

# GNU time 1.9 built static, so the one binary runs inside every tool's container (mounted at /opt/time)
gnu_time() {
  [ -x "$GNU_TIME" ] && return 0
  fetch time-1.9.tar.gz; build_image
  mkdir -p "$(dirname "$GNU_TIME")"
  log "build GNU time 1.9 (static)"
  $DOCKER run --rm --network none -v "$TP_DOWNLOADS":/dl:ro -v "$(dirname "$GNU_TIME")":/out "$TP_BUILD_IMAGE" bash -c '
    set -e; cd /tmp && tar xzf /dl/time-1.9.tar.gz && cd time-1.9
    ./configure CFLAGS="-O2 -std=gnu17" LDFLAGS=-static >/dev/null && make >/dev/null
    cp time /out/gnu-time-1.9-static && chmod 755 /out/gnu-time-1.9-static' || die "GNU time build failed"
}

# CROWN's image (CROWN's artifact.zip carries cav-artifact/crown.tar.gz); its /root/crown holds the benchmarks and comparison/
CROWN_IMAGE=crown:latest
crown_image() {
  $DOCKER image inspect "$CROWN_IMAGE" >/dev/null 2>&1 && return 0
  fetch crown-artifact.zip
  log "load $CROWN_IMAGE"
  unzip -p "$TP_DOWNLOADS/crown-artifact.zip" cav-artifact/crown.tar.gz | gzip -dc | $DOCKER load >/dev/null || die "load crown failed"
}

# make a host directory writable by any container user (the tools' images run as root or as their own user)
open_dir() { mkdir -p "$1"; chmod 777 "$1"; }
