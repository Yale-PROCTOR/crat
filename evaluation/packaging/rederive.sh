#!/bin/bash
# Derive the artifact-evaluation source zip from the frozen source the paper evaluated (R1265-3). See README.md.
# usage: rederive.sh <head> <tag>
#   <tag> names the derivation branch (rederive-<tag>), its worktree and the scratch directory.
# The derivation is the cleaning: the owners' patches, the removals, the test cut, option 3A, the compiler's dead code,
# the unused dependencies, the comment strip, the rename and the string edits, then the build, the greps and the
# counts of the development-material bar (R1265-1). A hit of a grep or a count above 0 stops it before the zip.
# Environment (all optional):
#   REPO               the repository (default: the one containing this script)
#   SCRATCH            work directory: logs, build targets, the zip (default: $REPO/target/packaging/<tag>)
#   WORKTREES          where the derivation worktree is created (default: $SCRATCH/worktrees)
#   TOOLS_TARGET       cargo target of the helper binaries under tools/ (default: $SCRATCH/tools-target)
#   CARGO              the cargo command (default: cargo). The solver and libclang variables the top-level README
#                      names must be in the environment, as for any build of the repository.
#   ENVREL             the environment of record, relative to the head (default: the final frame's env file); it becomes
#                      config/analysis-env.sh without the names in CONFIG_DROP (the toolchain's, and the record's
#                      names no reader takes once patches/20- is applied)
#   ARTIFACT_REV       the revision whose evaluation/docker/ becomes artifact/ (default: <head>)
#   PATCHES            the owners' patches against <head>, applied in name order (default: patches/ beside this script)
#   LEGACY_LIST        option 3A's list (default: legacy-cut-<head>.txt beside this script); LEGACY_SEARCH=1 makes it
#                      again by the compiler and writes it to $SCRATCH/legacy-cut.txt
#   IDENTITY_PATTERNS  the identity grep (grep -E, case-insensitive) over the tree but benchmarks/; the default covers
#                      paths and services, the operator adds the names of the authors and of the hosts
#   IDENTITY_ALLOW     fixed strings (one per line) removed from a line before the identity grep reads it
#   PROVENANCE_PATTERNS  the internal-provenance grep (grep -E) over the tree but benchmarks/
#   FORBIDDEN          fixed strings, FORBIDDEN_RE extended regular expressions (one per line): the internal names that
#                      must not appear in the tree but benchmarks/; FORBIDDEN_ALLOW: fixed strings removed from a line
#                      first; FORBIDDEN_EXEMPT: `regex<TAB>path prefix` lines, a pattern not applied under that prefix
#   HASH_REPOS         repositories (space-separated) whose commit hashes must not appear in the tree (default: REPO)
#   DRY_RUN=1          every hit and count is listed under $SCRATCH/hits/ and the derivation goes on through the build
#                      of the derived tree; no zip
# Environment (required): the evaluation's inputs, which are not in the repository (they become the zip's benchmarks/):
#   BENCH              a zip whose jobcrat-source/benchmarks/ holds them, or a directory laid out as benchmarks/
#   BENCH_SHA256SUMS   the SHA-256 of that benchmarks/SHA256SUMS; the derivation stops unless it matches and every file
#                      but README.md and SHA256SUMS is listed in it and checks
set -u
HEAD=${1:?head}; TAG=${2:?tag}; ARTIFACT_REV=${ARTIFACT_REV:-$HEAD}
BENCH=${BENCH:?BENCH: a zip carrying jobcrat-source/benchmarks/ or a benchmarks/ directory}; BENCH_SHA256SUMS=${BENCH_SHA256SUMS:?BENCH_SHA256SUMS: the SHA-256 of benchmarks/SHA256SUMS}
P=$(cd "$(dirname "$0")" && pwd)
REPO=${REPO:-$(git -C "$P" rev-parse --show-toplevel)}
SCRATCH=${SCRATCH:-$REPO/target/packaging/$TAG}; ZS=$SCRATCH
WORKTREES=${WORKTREES:-$SCRATCH/worktrees}; W=$WORKTREES/rederive-$TAG
TOOLS_TARGET=${TOOLS_TARGET:-$SCRATCH/tools-target}; TOOLS=$TOOLS_TARGET/release
CARGO=${CARGO:-cargo}; DRY_RUN=${DRY_RUN:-0}; LEGACY_SEARCH=${LEGACY_SEARCH:-0}
LEGACY_LIST=${LEGACY_LIST:-$P/legacy-cut-$(git -C $REPO rev-parse --short=9 "$HEAD^{commit}").txt}
ENVREL=${ENVREL:-crates/pointer_replacer/frames/l01p14u-s39-mutlend-o-env.sh}
CONFIG_DROP=${CONFIG_DROP:-SYSROOT LD_LIBRARY_PATH TMPDIR RUSTUP_TOOLCHAIN CRAT_ERA5_EXECUTION_ROLE CRAT_ERA5_TOOLCHAIN_DIGEST CRAT_ERA5_DEPENDENCY_DIGEST CRAT_ERA5C_RAW_CAUSE_LEDGER CRAT_ERA5C_RAW_CAUSE_BUDGET_S}
PATCHES=${PATCHES:-$P/patches}
IDENTITY_PATTERNS=${IDENTITY_PATTERNS:-'/home/|agent-worktrees|anthropic|claude|codex|openai|github\.com|Co-Authored'}
HASH_REPOS=${HASH_REPOS:-$REPO}
IDENTITY_ALLOW=${IDENTITY_ALLOW:-'registry+https://github.com/rust-lang/crates.io-index
https://github.com/immunant/c2rust.git
https://codeload.github.com/PLaSSticity/refinator-impl/tar.gz/4fdf3309d2a3763786b0090ae956940d97661855
https://github.com/rust-lang/rust/'}
PROVENANCE_PATTERNS=${PROVENANCE_PATTERNS:-'\b(wave-[0-9][a-z0-9]*|era-5c|analysis-fanout|fan-out|rq3-inator|crat-packaging|slicecursor|ownership-fields|assembler)\b|\b[Rr]elays? [0-9]+|\b[Rr]eports? [0-9]+|\bR[0-9]{3,4}-[0-9]+\b|\b[Aa]ddend(um|a)\b|\b[Bb]atch(es)? [0-9]+|\b60s\b|\bL01'}
FORBIDDEN=${FORBIDDEN:-'retained_alias_observed
ERA5_PROGRAM
observed:pass-'}
FORBIDDEN_RE=${FORBIDDEN_RE:-'[Ee]ra-?5|ERA5|\bE5C\b|\be5c_
[Ww]ave-?[0-9]|WAVE[0-9]
\bL01
\b[Nn][Bb][0-9]
\bbo_c1\b
\b[Mm]ode[-_]?A\b|\bmode_a\b
②
\bL2\b|\bl2_|_l2\b
\bT2\b|\bt2_|_t2\b
\bA5\b|\bA5[A-Z_]|\ba5_|_a5\b
\b[Aa]1[46]\b|\b[Aa]1[46]_|_a1[46]\b
\b[Cc]9_|\bC9[A-Z]
\bw[0-9]{2}_fault
\bS2[0-9][A-Z]'}
FORBIDDEN_ALLOW=${FORBIDDEN_ALLOW:-'std::env::var("JOBCRAT_ERA5_PROGRAM")'}
FORBIDDEN_EXEMPT=${FORBIDDEN_EXEMPT:-'\bT2\b|\bt2_|_t2\b	artifact/rq1/'}
export IDENTITY_PATTERNS IDENTITY_ALLOW FORBIDDEN FORBIDDEN_RE FORBIDDEN_ALLOW FORBIDDEN_EXEMPT
SR=$(rustup run nightly-2025-06-23 rustc --print sysroot); export LD_LIBRARY_PATH=$SR/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}
export W ZS TOOLS KEPT=$ZS/kept-rs-files.txt ORPHANS=$ZS/orphans.txt CARGO CARGO_INCREMENTAL=0
mkdir -p $ZS $WORKTREES; rm -rf $ZS/stage $ZS/unzipped $ZS/hits $ZS/deadcut.tsv $ZS/deadcut.log; mkdir -p $ZS/hits
log=$ZS/rederive.log; : > $log; exec > >(tee -a $log) 2>&1
echo "START $(date -u +%FT%TZ) head=$HEAD artifact=$ARTIFACT_REV tag=$TAG env=$ENVREL dry_run=$DRY_RUN repo=$REPO scratch=$ZS"
step() { echo "== $(date -u +%T) $*"; }
commit() { git -C $W add -A >/dev/null; git -C $W -c user.name=submission -c user.email=submission@localhost commit -q -m "$1" && echo "   commit $(git -C $W rev-parse --short=9 HEAD): $1"; }
build() { local label=$1 dir=$2; shift 2; echo "   build $label: $CARGO build --release --manifest-path $dir/Cargo.toml $* (target $CARGO_TARGET_DIR)"; $CARGO build --release --manifest-path $dir/Cargo.toml "$@" > $ZS/build-$label.log 2>&1; local rc=$?; echo "   build $label END $(date -u +%FT%TZ) rc=$rc"; return $rc; }
reach_sweep() {  # .rs files no module declares, data files no kept file names
  find $W/crates $W/src $W/deps_crate -name '*.rs' -type f | sort > $KEPT
  for i in 1 2 3; do python3 -I $P/reach.py > $ZS/reach-$i.txt; grep -E '^UNRESOLVED' $ZS/reach-$i.txt | while read _ f name _; do sed -i -E "/^\s*(pub(\([a-z]+\))? )?mod $name;\s*$/d" $W/$f; echo "   unresolved mod $name removed from $f"; done; grep -q '^UNRESOLVED' $ZS/reach-$i.txt || break; done
  head -1 $ZS/reach-$i.txt
  sed -n "/./s#^#$W/#p" $ORPHANS | xargs -r git -C $W rm -q -f -- 2>/dev/null; sed -n "/./s#^#$W/#p" $ORPHANS | xargs -r rm -f --
  find $W/crates $W/src $W/deps_crate -name '*.rs' -type f | sort > $KEPT
  for f in $(find $W/crates/*/src -type f ! -name '*.rs' ! -name 'Cargo.toml'); do b=$(basename $f); grep -q -l -F -- "$b" $(cat $KEPT) || { git -C $W rm -q -f -- $f 2>/dev/null || rm -f $f; echo "   unreferenced data file removed: ${f#$W/}"; }; done
  find $W/crates $W/src -type d -empty -delete
}

step "0 the helper binaries (cfgcut, rslex, itemcut)"
if [ ! -x $TOOLS/cfgcut ] || [ ! -x $TOOLS/rslex ] || [ ! -x $TOOLS/itemcut ] || [ -n "$(find $P/tools/src -newer $TOOLS/itemcut -name '*.rs' 2>/dev/null)" ]; then export CARGO_TARGET_DIR=$TOOLS_TARGET; build tools $P/tools || { echo "the tools do not build: $ZS/build-tools.log"; exit 1; }; fi
echo "   $TOOLS/cfgcut, $TOOLS/rslex, $TOOLS/itemcut"

step "1 worktree; config/analysis-env.sh from the environment of record"
git -C $REPO worktree remove --force $W 2>/dev/null; [ -d $W ] && rm -rf $W; git -C $REPO branch -D rederive-$TAG 2>/dev/null
git -C $REPO worktree add $W -b rederive-$TAG $HEAD >/dev/null 2>&1 || { echo "worktree failed"; exit 1; }
echo "   base tree $(git -C $W rev-parse $HEAD^{tree}) files $(git -C $W ls-files | wc -l)"
[ -f $W/$ENVREL ] || { echo "env of record $ENVREL absent"; exit 1; }
mkdir -p $W/config; grep -E '^export ' $W/$ENVREL | sed -E 's/[[:space:]]+#.*$//' | grep -v -E "^export ($(echo $CONFIG_DROP | tr ' ' '|'))=" > $ZS/env-exports.txt
{ echo '#!/bin/bash'; cat $ZS/env-exports.txt; echo 'export SYSROOT="$(rustc --print sysroot)"'; echo 'export LD_LIBRARY_PATH="$SYSROOT/lib:$SYSROOT/lib/rustlib/x86_64-unknown-linux-gnu/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"'; } > $W/config/analysis-env.sh; chmod +x $W/config/analysis-env.sh
echo "   config/analysis-env.sh: $(grep -c '^export' $W/config/analysis-env.sh) exports from $ENVREL (left out: $CONFIG_DROP)"

step "2 the owners' patches"
n=0; for p in $(ls $PATCHES/*.patch 2>/dev/null | sort); do
  git -C $W apply --index --whitespace=nowarn $p || { echo "patch $(basename $p) does not apply to $HEAD"; exit 1; }
  n=$((n+1)); echo "   applied $(basename $p): $(git -C $W diff --cached --shortstat | sed 's/^ *//')"; commit "Packaging A0: $(basename $p .patch)" > /dev/null
done
echo "   $n patches applied from ${PATCHES#$P/}"

step "3 removals; benchmarks/ from BENCH; artifact/ from ARTIFACT_REV's evaluation/docker; the table out; the driver template"
rm -rf $ZS/bench-keep $ZS/bench-unzip
if [ -d "$BENCH" ]; then cp -a "$BENCH" $ZS/bench-keep; else mkdir -p $ZS/bench-unzip; unzip -q "$BENCH" 'jobcrat-source/benchmarks/*' -d $ZS/bench-unzip && mv $ZS/bench-unzip/jobcrat-source/benchmarks $ZS/bench-keep; rm -rf $ZS/bench-unzip; fi
[ -f $ZS/bench-keep/SHA256SUMS ] || { echo "BENCH has no benchmarks/SHA256SUMS: $BENCH"; exit 1; }
got=$(sha256sum $ZS/bench-keep/SHA256SUMS | cut -c1-64); [ "$got" = "$BENCH_SHA256SUMS" ] || { echo "benchmarks/SHA256SUMS is $got, not BENCH_SHA256SUMS $BENCH_SHA256SUMS"; exit 1; }
( cd $ZS/bench-keep && sha256sum -c --quiet SHA256SUMS ) || { echo "benchmarks/: a file does not match SHA256SUMS"; exit 1; }
unlisted=$(cd $ZS/bench-keep && find . -type f ! -path ./SHA256SUMS ! -path ./README.md | sed 's#^\./##' | sort | comm -23 - <(sed -E 's/^[0-9a-f]{64}  //' SHA256SUMS | sort))
[ -z "$unlisted" ] || { echo "benchmarks/: files not in SHA256SUMS: $unlisted"; exit 1; }
echo "   BENCH $BENCH: SHA256SUMS sha256 $got, $(grep -c . $ZS/bench-keep/SHA256SUMS) entries checked, no unlisted file"
rm -rf $ZS/artifact-keep
git -C $REPO cat-file -e "$ARTIFACT_REV:evaluation/docker" 2>/dev/null || { echo "ARTIFACT_REV $ARTIFACT_REV has no evaluation/docker"; exit 1; }
mkdir -p $ZS/artifact-keep; git -C $REPO archive "$ARTIFACT_REV" evaluation/docker | tar -x -C $ZS/artifact-keep --strip-components=2
echo "   artifact/ from $ARTIFACT_REV ($(git -C $REPO rev-parse --short=9 "$ARTIFACT_REV^{commit}")): evaluation/docker tree $(git -C $REPO rev-parse "$ARTIFACT_REV:evaluation/docker")"
for p in .compound-engineering .github .gitignore .claudignore CLAUDE.md AGENTS.md .claude .codex .vscode M0-KNOWN-DEFECTS.md README.md LICENSE benchmarks tool.py rustfmt.toml examples crates/pointer_replacer/frames crates/pointer_replacer/tools crates/finders crates/io_replacer crates/merger crates/outparam_replacer crates/static_replacer crates/union_replacer src/bin/crat-finder.rs src/bin/crat-merge.rs crat-finder crat-merge crates/passes/src/bin_file_adder.rs crates/passes/src/enum_replacer crates/passes/src/formatter.rs crates/passes/src/interface_fixer.rs crates/passes/src/libc_replacer crates/passes/src/simplifier crates/passes/src/simplifier.rs crates/passes/src/splitter.rs crates/passes/src/unexpander.rs crates/passes/src/unsafe_resolver crates/utils/src/bit_set.rs crates/utils/src/unsafety.rs evaluation; do [ -e $W/$p ] && git -C $W rm -r -q -f -- $p; done
find $W/crates $W/src -type f \( -name '*_tests.rs' -o -name 'tests.rs' -o -name 'test_*.py' \) -print0 | xargs -0 -r git -C $W rm -q -f --
find $W/crates $W/src -type d -name tests -print0 | xargs -0 -r git -C $W rm -r -q -f --
python3 - <<'PY'
import os, re
W=os.environ['W']
p=W+'/crates/passes/src/lib.rs'; s=open(p).read()
s=''.join(l for l in s.splitlines(True) if not (l.startswith('pub mod ') and l.strip() not in ('pub mod expander;','pub mod extern_resolver;','pub mod preprocessor;')))
open(p,'w').write(s)
p=W+'/crates/utils/src/lib.rs'; s=open(p).read(); s=s.replace('pub mod bit_set;\n','').replace('pub mod unsafety;\n',''); open(p,'w').write(s)
p=W+'/Cargo.toml'; s=open(p).read()
for m in ['finders','io_replacer','merger','outparam_replacer','static_replacer','union_replacer']:
    s=s.replace(f'  "crates/{m}",\n','').replace(f'{m} = {{ path = "crates/{m}" }}\n','')
s=re.sub(r'exclude = \["deps_crate", "examples"\]','exclude = ["deps_crate"]',s)
open(p,'w').write(s)
for root,_,files in os.walk(W+'/crates'):
    for f in files:
        if f=='Cargo.toml':
            p=os.path.join(root,f); s=open(p).read(); n=re.sub(r'\n\[dev-dependencies\]\n(?:[^\[\n][^\n]*\n|\n)*?(?=\[|\Z)','\n',s)
            if n!=s: open(p,'w').write(n); print('   dev-dependencies removed:',p.replace(W+'/',''))
# the driver template reads no analysis-switch file: the crate root no longer exports the loader
p=W+'/crates/pointer_replacer/src/lib.rs'; s=open(p).read(); old='env_from_file as bo_env_from_file, '
assert s.count(old)==1, 'the crate root does not export the loader once: the head is not the one this kit was written for'
open(p,'w').write(s.replace(old,'')); print('   lib.rs: the loader no longer exported (the driver template reads no switch file)')
PY
mkdir -p $W/benchmarks; mv $ZS/bench-keep/* $W/benchmarks/; echo "   benchmarks/: $(find $W/benchmarks -type f | wc -l) files from BENCH (byte for byte)"
mv $ZS/artifact-keep $W/artifact; echo "   artifact/: $(find $W/artifact -type f | wc -l) files from evaluation/docker"
python3 -I $P/observed_out.py || { echo "observed_out.py did not apply: the head is not the source it was written for"; exit 1; }
cp $P/driver-template.crat.rs $W/src/bin/crat.rs
cp $P/README-template.md $W/README.md
echo "   removed: $(git -C $W diff --cached --name-only --diff-filter=D | wc -l) tracked paths"
commit "Packaging A: removals, benchmarks/, artifact/, the table out, the driver template, config and README"

step "4 cfg(test) cut + orphans"
find $W/crates $W/src $W/deps_crate -name '*.rs' -type f | sort > $KEPT
$TOOLS/cfgcut $(cat $KEPT) > $ZS/cfgcut.tsv 2> $ZS/cfgcut.err; tail -1 $ZS/cfgcut.err
reach_sweep
commit "Packaging B: the cfg(test) cut, unresolved test modules, orphans, unreferenced data"

step "5 option 3A: the legacy rewriter's item cuts (option3.py), then the modules the compiler finds unused"
export CARGO_TARGET_DIR=$ZS/check-target CHECK_TARGET=$ZS/check-target CHECK_LOG=$ZS/check.log ITEM_CUTS=$P/option3.py SEARCH_DEPS=0 SEARCH_ALLOW=0
export SEARCH_SKIP=${SEARCH_SKIP:-crates/pointer_replacer/src/bo_rewriter crates/pointer_replacer/src/analyses/borrow_ownership crates/pointer_replacer/src/bo_pipeline.rs}
if [ "$LEGACY_SEARCH" = 1 ]; then python3 -I $P/legacy_search.py search $ZS/legacy-cut.txt || { echo "option 3A's search failed: $ZS/check.log"; exit 1; }
else [ -f "$LEGACY_LIST" ] || { echo "no option 3A list $LEGACY_LIST: run with LEGACY_SEARCH=1"; exit 1; }; python3 -I $P/legacy_search.py apply "$LEGACY_LIST" || exit 1; fi
reach_sweep
commit "Packaging C: option 3A (the legacy part keeps what the pointer pass reads)"

step "6 the compiler's dead code, to a fixpoint (deadcut)"
python3 -I $P/deadcut.py || { echo "deadcut failed: $ZS/deadcut.log"; exit 1; }
reach_sweep
commit "Packaging D: the dead code the compiler reports"

step "7 unused crate dependencies"
python3 -I $P/legacy_search.py deps
commit "Packaging E: the unused crate dependencies"

step "8 comment strip; lint reasons"
find $W/crates $W/src $W/deps_crate -name '*.rs' -type f | sort > $KEPT
$TOOLS/rslex strip $(cat $KEPT) > $ZS/strip-rs.tsv; awk -F'\t' '{f++; c+=$2} END {printf "   rs files=%d comments_removed=%d\n", f, c}' $ZS/strip-rs.tsv
python3 -I $P/strip_misc.py toml $W/Cargo.toml $W/crates/*/Cargo.toml $W/deps_crate/Cargo.toml $W/deps_crate/Cargo.lock > $ZS/strip-toml.tsv; awk -F'\t' '{c+=$2} END {printf "   toml comments_removed=%d\n", c}' $ZS/strip-toml.tsv
git -C $W grep -l -E 'reason\s*=\s*"' -- '*.rs' | sort > $ZS/reason-files.txt; python3 -I $P/strip_reasons.py $ZS/reason-files.txt > $ZS/reasons-deleted.tsv 2> $ZS/reasons.err; cat $ZS/reasons.err
commit "Packaging F: the comment strip, the lint reasons"

step "9 rename crat -> jobcrat (R1-R6) and the rules of rename-rules.tsv (R7 and on); string edits"
python3 -I $P/rename.py apply > $ZS/rename-map.tsv 2> $ZS/rename-map.err; grep '#COUNTS' $ZS/rename-map.err
git -C $W mv src/bin/crat.rs src/bin/jobcrat.rs; git -C $W mv crat jobcrat
python3 -I $P/edits.py | tee $ZS/edits.txt | tail -3
commit "Packaging G: the rename, the string edits"

step "10 warnings, build, lock, checks, the counts"
python3 -I $P/warnings.py > $ZS/warnings.txt || { echo "the derived tree does not check: $ZS/warnings-check.err"; exit 1; }; grep -v '^#WARNINGS' $ZS/warnings.txt; nwarn=$(sed -n 's/^#WARNINGS //p' $ZS/warnings.txt)
export CARGO_TARGET_DIR=$ZS/target; build derived $W || { echo "the derived tree does not build: $ZS/build-derived.log"; tail -30 $ZS/build-derived.log; exit 1; }
echo "   warnings in the derived build: $(grep -c -E '^warning' $ZS/build-derived.log)"
python3 -I $P/strip_misc.py toml $W/Cargo.lock > /dev/null; git -C $W add -A; git -C $W -c user.name=submission -c user.email=submission@localhost commit -q -m "Packaging H: allow(warnings) where a crate warns; the lockfile as cargo resolved it, header stripped" 2>/dev/null && echo "   committed: allow lines, lock"
echo "   TREE $(git -C $W rev-parse HEAD^{tree}) files $(git -C $W ls-files | wc -l)"
echo "   crat word: $(git -C $W grep -n -w -e crat -- . | wc -l); bCRAT_: $(git -C $W grep -n -P '\bCRAT_' -- . | wc -l); __crat_: $(git -C $W grep -n -e '__crat_' -e '__CRAT_' -- . | wc -l); Crat: $(git -C $W grep -n -w -e Crat -- . | wc -l)"
git -C $W grep -n -I -i -E -e "$IDENTITY_PATTERNS" -- . ':!benchmarks' | python3 -I -c 'import os, re, sys
allow = [a for a in os.environ["IDENTITY_ALLOW"].splitlines() if a]; pat = re.compile(os.environ["IDENTITY_PATTERNS"], re.I)
for line in sys.stdin:
    path, _, text = line.partition(":")
    for a in allow: text = text.replace(a, "")
    if pat.search(text): sys.stdout.write(line)' > $ZS/hits/identity.txt
git -C $W grep -n -I -E -e "$PROVENANCE_PATTERNS" -- . ':!benchmarks' > $ZS/hits/provenance.txt
printf '%s\n' "$FORBIDDEN" | grep . > $ZS/forbidden.txt; printf '%s\n' "$FORBIDDEN_RE" | grep . > $ZS/forbidden-re.txt
git -C $W grep -n -I -E -f <(cat $ZS/forbidden-re.txt; sed 's/[][\.*^$+?(){}|]/\\&/g' $ZS/forbidden.txt) -- . ':!benchmarks' | python3 -I -c 'import os, re, sys
allow = [a for a in os.environ["FORBIDDEN_ALLOW"].splitlines() if a]
exempt = [l.split("\t") for l in os.environ["FORBIDDEN_EXEMPT"].splitlines() if "\t" in l]
fixed = [f for f in os.environ["FORBIDDEN"].splitlines() if f]; res = [(r, re.compile(r)) for r in os.environ["FORBIDDEN_RE"].splitlines() if r]
for line in sys.stdin:
    path, _, rest = line.partition(":"); n, _, text = rest.partition(":")
    for a in allow: text = text.replace(a, "")
    hit = [f for f in fixed if f in text] + [r for r, c in res if c.search(text) and not any(r == e and path.startswith(pre) for e, pre in exempt)]
    for h in hit: sys.stdout.write(f"{path}\t{n}\t{h}\t{text.strip()[:200]}\n")' > $ZS/hits/forbidden.tsv
printf '%s\n' "$FORBIDDEN_ALLOW" | grep . > $ZS/forbidden-allow.txt; git -C $W grep -n -I -F -f $ZS/forbidden-allow.txt -- . > $ZS/hits/forbidden-allowed.txt
idl=$(cat $ZS/hits/identity.txt); prov=$(cat $ZS/hits/provenance.txt); forb=$(cat $ZS/hits/forbidden.tsv)
echo "   identity grep (outside benchmarks/, minus IDENTITY_ALLOW): $(grep -c . $ZS/hits/identity.txt); in benchmarks/ (third-party inputs, kept byte for byte): $(git -C $W grep -n -i -E -e "$IDENTITY_PATTERNS" -- benchmarks | wc -l) lines in $(git -C $W grep -l -i -E -e "$IDENTITY_PATTERNS" -- benchmarks | wc -l) files"
echo "   provenance grep (outside benchmarks/): $(grep -c . $ZS/hits/provenance.txt) lines in $(cut -d: -f1 $ZS/hits/provenance.txt | sort -u | grep -c .) files"
echo "   forbidden names (outside benchmarks/): $(cut -f1,2 $ZS/hits/forbidden.tsv | sort -u | grep -c .) lines in $(cut -f1 $ZS/hits/forbidden.tsv | sort -u | grep -c .) files; lines with an allowed string (FORBIDDEN_ALLOW): $(grep -c . $ZS/hits/forbidden-allowed.txt); by pattern:"
cut -f3 $ZS/hits/forbidden.tsv | sort | uniq -c | sort -rn | sed 's/^/      /'
ours=$(git -C $W grep -o -h -I -E '\b[0-9a-f]{7,40}\b' -- . | sort -u | while read t; do case $t in *[a-f]*) ;; *) continue;; esac; case $t in *[0-9]*) ;; *) continue;; esac; for r in $HASH_REPOS; do git -C $r rev-parse --verify --quiet "$t^{commit}" >/dev/null 2>&1 && { echo $t; break; }; done; done)
printf '%s\n' "$ours" | grep . > $ZS/hits/hashes.txt
echo "   commit hashes of our repositories in the tree: $(grep -c . $ZS/hits/hashes.txt)${ours:+ -- $(echo $ours | cut -c1-200)}"
find $W/crates $W/src $W/deps_crate -name '*.rs' -type f | sort > $KEPT; $TOOLS/rslex count $(cat $KEPT) > $ZS/comments.tsv
tests=$(for f in $(cat $KEPT); do $TOOLS/rslex dump $f; done | cut -f2 | tr '\n' ' ' | grep -o -E '# !? ?\[ cfg \( test \) \]|# \[ test \]' | wc -l)
echo "   cfg(test) / #[test] attributes left (by the lexer's tokens): $tests"
ncom=$(awk -F'\t' '{c+=$2} END {print c+0}' $ZS/comments.tsv); echo "   comments shipped: $ncom"
python3 -I $P/counts.py > $ZS/counts.txt; grep -v '^#BAR' $ZS/counts.txt; bar=$(sed -n 's/^#BAR //p' $ZS/counts.txt)
echo "   artifact/ in the tree: $(git -C $W ls-files -- artifact | wc -l) files; evaluation/ in the tree: $(git -C $W ls-files -- evaluation | wc -l) files (must be 0)"
nbar=$((bar + tests + nwarn + ncom)); [ -s $ZS/hits/forbidden-allowed.txt ] && nbar=$((nbar + $(grep -c . $ZS/hits/forbidden-allowed.txt)))
if [ -n "$idl$prov$forb$ours" ] || [ $nbar -gt 0 ]; then
  if [ "$DRY_RUN" = 1 ]; then echo "DRY RUN: the hits and the counts are listed under $ZS/hits/; no zip"; echo "END $(date -u +%FT%TZ)"; exit 0; fi
  echo "a grep has hits, the tree names a commit of ours, or a count of the bar is above 0 ($nbar); no zip (the lists: $ZS/hits/):"; printf '%s\n' "$idl" "$prov" "$forb" "$ours" | grep . | head -40 | cut -c1-240; exit 1
fi
[ "$DRY_RUN" = 1 ] && { echo "DRY RUN: no hits; no zip"; echo "END $(date -u +%FT%TZ)"; exit 0; }

step "11 zip + from-zip build"
$P/mkzip.sh | tail -4
rm -rf $ZS/zip-target; export CARGO_TARGET_DIR=$ZS/zip-target; build from-zip $ZS/unzipped/jobcrat-source --locked || { echo "the zip does not build: $ZS/build-from-zip.log"; tail -30 $ZS/build-from-zip.log; exit 1; }
echo "   warnings in the from-zip build: $(grep -c -E '^warning' $ZS/build-from-zip.log)"
echo "ZIP $ZS/jobcrat-source.zip sha256=$(sha256sum $ZS/jobcrat-source.zip | cut -c1-64) bytes=$(stat -c %s $ZS/jobcrat-source.zip) entries=$(unzip -Z1 $ZS/jobcrat-source.zip | wc -l)"
echo "END $(date -u +%FT%TZ)"
