#!/usr/bin/env bash
# Re-runs the exact-arithmetic checks of the Theorem B certificates and of the evidence certificates (Python; needs
# numpy and scipy). One process at a time.
#
# usage: bash computation/theorem-b/run_checks.sh [quick|full] [LOGDIR]
#   quick  L <= 256 (about 3 minutes on the authoring machine)
#   full   adds L = 512 (about 13 minutes in all there; the L = 512 PRS-diagonal check alone took about 9 minutes)
#   LOGDIR defaults to computation/theorem-b/logs, which holds the recorded run of 26 October 2026 (it is overwritten);
#          verification/run_all.sh passes verification/logs/theorem-b.
# Environment: PYTHON (default: py if present, else python3).
#
# Every run appends its output and its exit status ("exit=<code>") to the log of its group. The last line printed
# (and written to LOGDIR/verify_done.log) is "ALL CHECKS PASSED (<n> runs, mode <m>)" if every run exited 0, otherwise
# "FAILED: <k> of <n> runs"; the exit status of this script is 0 only in the first case.
# (The research package's version of this script printed ALL-DONE whatever the exit codes; this one does not.)
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
mode=${1:-quick}
LOG="${2:-$HERE/logs}"
mkdir -p "$LOG"
LOG="$(cd "$LOG" && pwd)"
PY="${PYTHON:-$(command -v py >/dev/null 2>&1 && echo py || echo python3)}"
export PYTHONDONTWRITEBYTECODE=1
cd "$HERE" || exit 1
fails=0
runs=0
run() {
  name=$1; shift
  runs=$((runs + 1))
  echo "### $name: $*" >> "$LOG/$name.log"
  s=$(date +%s)
  "$PY" -B "$@" >> "$LOG/$name.log" 2>&1
  rc=$?
  echo "exit=$rc ($(( $(date +%s) - s )) s)" >> "$LOG/$name.log"
  if [ "$rc" != 0 ]; then fails=$((fails + 1)); echo "FAILED (exit $rc): $name $*"; fi
}
for f in verify_model2cuts verify_model2cuts_dd verify_model2_diag verify_sdp_prs verify_tri_prs_cuts; do : > "$LOG/$f.log"; done
# Theorem B and the evidence of Section 8: the sharper cover with triangle cuts
for L in 32 64 128 192 256; do run verify_model2cuts verify_model2cuts.py $L --brute; done
for L in 128 256; do run verify_model2cuts_dd verify_model2cuts_dd.py $L; done
# the sharper cover with diagonal certificates only
for L in 64 128 256; do run verify_model2_diag verify_model2.py $L --exact --brute; done
# Theorem A: the strip cover of Parrilo, Robertson and Saracino with diagonal certificates
for L in 128 256; do run verify_sdp_prs verify_sdp.py $L --exact; done
# evidence: the strip cover with triangle cuts
for L in 64 128 256; do run verify_tri_prs_cuts verify_tri.py data/sdp_tri_L$L.json; run verify_tri_prs_cuts verify_dd.py data/sdp_tri_L$L.json; done
if [ "$mode" = full ]; then
  run verify_model2cuts_dd verify_model2cuts_dd.py 512
  run verify_sdp_prs verify_sdp.py 512 --exact
  run verify_tri_prs_cuts verify_dd.py data/sdp_tri_L512.json
fi
if [ "$fails" = 0 ]; then echo "ALL CHECKS PASSED ($runs runs, mode $mode)"; else echo "FAILED: $fails of $runs runs"; fi | tee "$LOG/verify_done.log"
[ "$fails" = 0 ]
