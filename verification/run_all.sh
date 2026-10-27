#!/usr/bin/env bash
# Repeat every verification step from a clean build, writing the logs to verification/logs/.
#
# Usage (from the repository root, i.e. the folder that contains lean/ and verification/):
#     bash verification/run_all.sh
# Environment:
#     JOBS=2          number of parallel Lean jobs (default 2). The largest generated certificate modules reached
#                     8.7 GB each in the run of record, so keep JOBS x 9 GB below the free memory. This Lake version
#                     (4.27.0) has no -j option; JOBS is passed as LEAN_NUM_THREADS, which sets the size of Lake's job
#                     pool and of each Lean process's thread pool. Also used for the parallel kernel replay.
#     LEAN4CHECKER    path to a lean4checker executable built from tag v4.27.0 (optional; the step is skipped if unset)
#     FETCH_CACHE=1   run `lake exe cache get` first (needed on a fresh machine; downloads the Mathlib build cache)
#     PYTHON          Python 3 interpreter with numpy, scipy and sympy (default: py on Windows, else python3)
#
# Steps: file manifest -> cache fetch (if FETCH_CACHE=1) -> environment record -> clean `lake build` of all 342 modules
# -> statements and axioms (Headline.lean) -> axioms of every declaration (AxiomAudit.lean) -> upstream pin (generated from
# the vendored upstream file) -> Lean evaluation of the Theorem C model (fidelity.lean) -> kernel replay (lean4checker)
# -> source scan, statement text check, numbers -> regeneration of the 302 generated modules from the JSON data
# -> exact checks of the Theorem C and Theorem B certificates -> small-case checks -> summary.
# Only lean/.lake/build is deleted; lean/.lake/packages (Mathlib) is never written to unless FETCH_CACHE=1.
# The summary ends with "RESULT: PASS" only if every step that ran passed.
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
L="$ROOT/verification/logs"
mkdir -p "$L"
PY="${PYTHON:-$(command -v py >/dev/null 2>&1 && echo py || echo python3)}"
JOBS="${JOBS:-2}"
export LEAN_NUM_THREADS="$JOBS"
export PYTHONDONTWRITEBYTECODE=1
NMOD=342
START="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
cd "$ROOT" || exit 1

# The manifest is checked first, before any log is rewritten (verification/logs/ is left out of this check).
( "$PY" -B verification/make_manifest.py --check --skip-logs ) > "$L/manifest.log" 2>&1; echo "exit=$?" >> "$L/manifest.log"

cd "$ROOT/lean" || exit 1
# Fetch first, so that the environment record below sees the Mathlib checkout that Lake has just cloned.
if [ "${FETCH_CACHE:-0}" = "1" ]; then lake exe cache get > "$L/cache_get.log" 2>&1; fi

{
  echo "# run_all.sh started $START"
  echo "os: $(uname -s -r -m)"
  echo "JOBS (LEAN_NUM_THREADS): $JOBS"
  lean --version
  lake --version
  echo "lean-toolchain: $(cat lean-toolchain)"
  "$PY" -B -c "import json;m=json.load(open('lake-manifest.json'));print('\n'.join('manifest: %s %s %s'%(p['name'],p.get('rev'),p.get('inputRev')) for p in m['packages']))"
  echo "mathlib checkout HEAD: $(git -C .lake/packages/mathlib rev-parse HEAD 2>/dev/null || echo unknown)"
  "$PY" -B -c "import sys,numpy,scipy,sympy;print('python',sys.version.split()[0],'numpy',numpy.__version__,'scipy',scipy.__version__,'sympy',sympy.__version__)"
  if [ -n "${LEAN4CHECKER:-}" ]; then echo "lean4checker: $(basename "$LEAN4CHECKER")"; else echo "lean4checker: not set"; fi
  echo "sha256 of the Lake project files (the 342 modules are checked in source_scan.log):"
  sha256sum Erdos1186.lean lakefile.toml lake-manifest.json lean-toolchain
} > "$L/environment.txt" 2>&1

rm -rf .lake/build
( time lake build ) > "$L/build.log" 2>&1; echo "exit=$?" >> "$L/build.log"

( time lake env lean ../verification/Headline.lean ) > "$L/headline.log" 2>&1; echo "exit=$?" >> "$L/headline.log"
( time lake env lean ../verification/AxiomAudit.lean ) > "$L/axioms.log" 2>&1; echo "exit=$?" >> "$L/axioms.log"
( cd "$ROOT" && "$PY" -B verification/make_upstream_pin.py ) > "$L/upstream_pin.log" 2>&1
( time lake env lean ../verification/generated/UpstreamPin.lean ) >> "$L/upstream_pin.log" 2>&1; echo "exit=$?" >> "$L/upstream_pin.log"

# The Python model of the Theorem C certificates against the Lean definitions: Lean evaluates them at test points,
# the output must equal the recorded one, and fidelity_check.py compares it with the Python model.
{
  ( time lake env lean ../computation/theorem-c/fidelity.lean ) > "$L/fidelity_lean_out.txt" 2> "$L/fidelity_lean_time.txt"
  r0=$?
  echo "lean exit=$r0"
  cat "$L/fidelity_lean_time.txt"; rm -f "$L/fidelity_lean_time.txt"
  "$PY" -B -c "import sys;a,b=(open(p,'rb').read().replace(b'\r',b'').strip() for p in sys.argv[1:]);print('Lean output equals computation/theorem-c/data/fidelity_lean_out.txt:',a==b);sys.exit(a!=b)" \
    "$L/fidelity_lean_out.txt" "$ROOT/computation/theorem-c/data/fidelity_lean_out.txt"
  r1=$?
  ( cd "$ROOT" && "$PY" -B computation/theorem-c/fidelity_check.py )
  r2=$?
  echo "exit=$(( r0 != 0 || r1 != 0 || r2 != 0 ))"
} > "$L/model_fidelity.log" 2>&1

if [ -n "${LEAN4CHECKER:-}" ]; then
  T="$(mktemp -d)"
  export LEAN4CHECKER T
  {
    echo "== $(date -u +%Y-%m-%dT%H:%M:%SZ) lean4checker: $(basename "$LEAN4CHECKER"), $NMOD modules, $JOBS in parallel"
    ls Erdos/Proofs/*.lean | sed 's#/#.#g; s#\.lean$##' | xargs -P "$JOBS" -n 1 bash -c \
      'm=$1; s=$(date +%s); lake env "$LEAN4CHECKER" "$m" > "$T/$m.out" 2>&1; echo "$m exit $? ($(( $(date +%s) - s )) s)" > "$T/$m.status"' _
    for f in $(ls "$T"/*.status | sort); do cat "$f"; sed 's/^/    /' "${f%.status}.out"; done
    echo "== finished $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  } > "$L/lean4checker.log" 2>&1
  rm -rf "$T"
else
  echo "LEAN4CHECKER not set; kernel replay skipped" > "$L/lean4checker.log"
fi

cd "$ROOT" || exit 1
pystep() { log=$1; shift; ( time "$PY" -B "$@" ) > "$L/$log.log" 2>&1; echo "exit=$?" >> "$L/$log.log"; }
pystep source_scan verification/source_scan.py
pystep fidelity_check verification/fidelity_check.py verification/upstream/FormalConjectures_ErdosProblems_1186.lean \
  lean/Erdos/Proofs/P1186.lean lean/Erdos/Proofs/P1186LowMain.lean lean/Erdos/Proofs/P1186M2Main.lean lean/Erdos/Proofs/P1186ExFinal.lean
pystep number_checks verification/number_checks.py
pystep regen_check verification/regen_check.py
pystep theorem_c_certs computation/theorem-c/verify_certs.py
pystep theorem_c_bareiss computation/theorem-c/verify_pd_bareiss.py
pystep theorem_c_star computation/theorem-c/check_star.py
( time PYTHON="$PY" bash computation/theorem-b/run_checks.sh quick "$L/theorem-b" ) > "$L/theorem_b_checks.log" 2>&1; echo "exit=$?" >> "$L/theorem_b_checks.log"
pystep oeis_small computation/small-cases/oeis_small.py 26
pystep disc_cutcell computation/small-cases/disc_cutcell_check.py
pystep lemma2_symbolic computation/small-cases/lemma2_symbolic.py

# Helpers. Logs written by Python on Windows have CRLF line endings, so CR bytes are removed before matching.
last() { tail -1 "$L/$1.log" | tr -d '\r'; }
lines() { tr -d '\r' < "$L/$1.log" | grep -E "$2"; }
count() { tr -d '\r' < "$L/$1.log" | grep -cE "$2"; }
has() { tr -d '\r' < "$L/$1.log" | grep -qE "$2"; }
# axiom lines: every `#print axioms` answer; nonstandard: answers that list any axiom outside the standard three
AXLINE="depends on axioms|does not depend on any axioms"
axbad() { tr -d '\r' < "$L/$1.log" | grep 'depends on axioms' | grep -cvE 'depends on axioms: \[((propext|Classical\.choice|Quot\.sound)(, )?)+\]$'; }
LEANERR=':[0-9]+:[0-9]+: error'
{
  echo "# summary $(date -u +%Y-%m-%dT%H:%M:%SZ) (started $START, JOBS=$JOBS)"
  echo "manifest:       $(lines manifest 'files listed' | tail -1) [$(last manifest)]"
  echo "build:          $(lines build '^(Build completed|error)' | tail -1) $(count build "declaration uses 'sorry'") sorry warnings [$(last build)]"
  echo "headline:       $(count headline "$AXLINE") axiom lines, $(axbad headline) non-standard, $(count headline "$LEANERR") error lines [$(last headline)]"
  echo "axioms:         $(lines axioms 'AXIOM AUDIT|TOTAL' | tr '\n' ' ') [$(last axioms)]"
  echo "upstream pin:   $(count upstream_pin "$AXLINE") axiom lines, $(axbad upstream_pin) non-standard, $(count upstream_pin "$LEANERR") error lines [$(last upstream_pin)]"
  echo "model fidelity: $(lines model_fidelity '^FIDELITY|equals' | tr '\n' ' ') [$(last model_fidelity)]"
  if [ -n "${LEAN4CHECKER:-}" ]; then echo "lean4checker:   $(count lean4checker ' exit 0 \(') of $NMOD modules exit 0"
  else echo "lean4checker:   SKIPPED (LEAN4CHECKER not set)"; fi
  echo "source scan:    $(lines source_scan '^(import closure|forbidden words in code|RESULT)' | tr '\n' ' ') [$(last source_scan)]"
  echo "statement text: $(lines fidelity_check '^RESULT') [$(last fidelity_check)]"
  echo "numbers:        $(lines number_checks '^(ALL|FAILED)') [$(last number_checks)]"
  echo "regeneration:   $(lines regen_check '^(regenerated byte|RESULT)' | sed 's/; not regenerated here.*//' | tr '\n' ' ') [$(last regen_check)]"
  echo "C certificates: $(lines theorem_c_certs '^ALL OK|FAIL' | tr '\n' ' ') [$(last theorem_c_certs)]"
  echo "C Bareiss:      $(lines theorem_c_bareiss '^BAREISS') [$(last theorem_c_bareiss)]"
  echo "C star value:   $(lines theorem_c_star '^(OK$|T direct)' | tr '\n' ' ') [$(last theorem_c_star)]"
  echo "B certificates: $(lines theorem_b_checks '^(ALL CHECKS|FAILED)' | tr '\n' ' ') [$(last theorem_b_checks)]"
  echo "OEIS A121385:   $(lines oeis_small '^RESULT') [$(last oeis_small)]"
  echo "cut-cell lemma: $(lines disc_cutcell '^RESULT') [$(last disc_cutcell)]"
  echo "lemma symbolic: $(lines lemma2_symbolic '^(ALL OK|FAILED)') [$(last lemma2_symbolic)]"
} | tee "$L/SUMMARY.txt"

# Exit status: 0 only if every step passed (the kernel replay counts only when LEAN4CHECKER is set).
fail=0
for f in manifest build headline axioms upstream_pin model_fidelity source_scan fidelity_check number_checks regen_check \
         theorem_c_certs theorem_c_bareiss theorem_c_star theorem_b_checks oeis_small disc_cutcell lemma2_symbolic; do
  [ "$(last "$f")" = "exit=0" ] || { fail=1; echo "step failed: $f" >> "$L/SUMMARY.txt"; }
done
need() { has "$1" "$2" || { fail=1; echo "missing in $1.log: $2" >> "$L/SUMMARY.txt"; }; }
need build '^Build completed successfully'
[ "$(count build "declaration uses 'sorry'")" = "0" ] || fail=1
for f in headline upstream_pin; do
  [ "$(count "$f" "$LEANERR")" = "0" ] || fail=1
  [ "$(axbad "$f")" = "0" ] || fail=1
done
[ "$(count headline "$AXLINE")" = "36" ] || fail=1
[ "$(count upstream_pin "$AXLINE")" = "7" ] || fail=1
need axioms 'AXIOM AUDIT PASSED'
need model_fidelity '^FIDELITY OK'
need source_scan '^RESULT: ALL OK'
need fidelity_check '^RESULT: ALL OK'
need number_checks '^ALL 14 CHECKS PASSED'
need regen_check '^regenerated byte for byte: 302 of 342 modules'
need regen_check '^RESULT: ALL IDENTICAL'
need theorem_c_certs '^ALL OK for regions \[1, 2, 3, 4, 5\]'
need theorem_c_bareiss '^BAREISS OK for regions \[1, 2, 3, 4, 5\]'
need theorem_c_star '^OK$'
need theorem_b_checks '^ALL CHECKS PASSED \(18 runs'
need oeis_small '^RESULT: ALL OK'
need disc_cutcell '^RESULT: ALL OK'
need lemma2_symbolic '^ALL OK'
if [ -n "${LEAN4CHECKER:-}" ]; then [ "$(count lean4checker ' exit 0 \(')" = "$NMOD" ] || fail=1; fi
if [ "$fail" != 0 ]; then echo "RESULT: FAIL (see the logs above)"
elif [ -n "${LEAN4CHECKER:-}" ]; then echo "RESULT: PASS"
else echo "RESULT: PASS (kernel replay skipped)"; fi | tee -a "$L/SUMMARY.txt"
exit "$fail"
