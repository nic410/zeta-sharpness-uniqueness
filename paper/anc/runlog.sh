#!/usr/bin/env bash
# Run one verifier from the anc/ directory and record a log with a header and a footer.
# Usage (from anc/):   ./runlog.sh LOGFILE  command [args...]
# Example:             export PY=python3
#                      ./runlog.sh positivity/logs/cert_gtail.log "$PY" positivity/cert_gtail.py
# Environment variables read by the verifiers (COEFF_DATA, COEFF_EXTRA, NGL, NSUB) are recorded in the header when set;
# give paths relative to anc/.  Several checks of the verifiers are Python assert statements, so Python must not run
# with -O or with PYTHONOPTIMIZE set; this wrapper refuses both.
set -u
cd "$(dirname "$0")"
log="$1"; shift
PYBIN="${PY:-python3}"
if [ -n "${PYTHONOPTIMIZE:-}" ] || { [ "${1:-}" = "$PYBIN" ] && case "${2:-}" in -O*) true;; *) false;; esac; }; then
  echo "runlog.sh: Python optimisation (-O or PYTHONOPTIMIZE) would remove assert checks; refusing to run" >&2
  exit 2
fi
mkdir -p "$(dirname "$log")"
{
  shown="$*"
  if [ "${1:-}" = "$PYBIN" ]; then shown="python ${*:2}"; fi    # never print the interpreter's absolute path
  envs=""
  for v in COEFF_DATA COEFF_EXTRA NGL NSUB; do
    if [ -n "${!v+x}" ]; then val="${!v}"; envs="$envs $v=${val#"$PWD"/}"; fi
  done
  [ -n "$envs" ] || envs=" (COEFF_DATA, COEFF_EXTRA, NGL, NSUB not set)"
  echo "# command : $shown"
  echo "# env     :$envs"
  echo "# date    : $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "# system  : $(uname -sm), $(env -u OMP_NUM_THREADS -u OMP_THREAD_LIMIT nproc) visible cores"
  echo "# python  : $("$PYBIN" -c 'import sys, flint
try:
    import mpmath; mv = mpmath.__version__
except ImportError:
    mv = "not installed"
print(sys.version.split()[0], "| python-flint", flint.__version__, "| mpmath", mv)')"
} > "$log"
t0=$(date +%s.%N)
"$@" >> "$log" 2>&1
rc=$?
t1=$(date +%s.%N)
awk -v a="$t0" -v b="$t1" -v rc="$rc" 'BEGIN{printf "# exit code %d; wall time %.1f s\n", rc, b-a}' >> "$log"
exit $rc
