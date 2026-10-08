#!/usr/bin/env bash
# The audit of the Lean spine of Part II (library `PositivityRigidityII`). Run from anywhere after `lake build`:
#   scripts/audit.sh            (CORES=10-11 LEAN_NUM_THREADS=2 scripts/audit.sh to pin to other cores)
# CORES (default 0-3) is a CPU list for `taskset`; the pinning is skipped if `taskset` is not available (e.g. macOS)
# or cannot pin to CORES, and CORES= (empty) disables it. LEAN_NUM_THREADS defaults to 4. AUDIT_NO_GIT=1 lists the
# files for the provenance digest without git.
# One command, one final line: `AUDIT PASSED` (or `AUDIT FAILED`).
#
# (0) `lake build --no-build PositivityRigidityII` succeeds: the checked .olean files are those of the current
#     sources (of this project and of Part I's spine, on which it depends).
# (a) no `sorry` / `admit` / `native_decide` token anywhere in the Lean sources (PositivityRigidityII/,
#     PositivityRigidityII.lean, scripts/; comments and string literals stripped);
# (b) axioms: no `axiom` declaration outside PositivityRigidityII/Ledger.lean (textual, comments and strings
#     stripped, and in the environment: scripts/Audit.lean); the number of ledger axioms (textual and in the
#     environment) equals the total in LEDGER.md, and LEDGER.md names every ledger axiom; no declaration of the
#     library depends on an axiom other than propext, Classical.choice, Quot.sound, the ledger axioms of Part II and
#     the ledger axioms of Part I (so no sorryAx, no Lean.ofReduceBool, no Lean.trustCompiler); the Part I ledger
#     axioms that are used are listed in LEDGER.md; every headline theorem exists and is a theorem;
# (c) `#print axioms` regression: the output of scripts/print_axioms.lean equals axioms.log, its `# ` header lines
#     excepted, exactly;
# (d) statement pin: the output of scripts/Statements.lean (the types of the headline theorems, of the ledger axioms
#     of Part II and of the Part I ledger axioms they use, and the types and bodies of every definition of Part I or
#     Part II they unfold to, with structural hashes) equals scripts/Statements.baseline.txt exactly;
# (e) provenance: every SHA-256 (or prefix) cited in PositivityRigidityII/Ledger.lean matches the cited file of the
#     ancillary directory (..), and every log line quoted there occurs in the cited log (scripts/check_provenance.py);
#     reported as SKIPPED, without failing, if the ancillary directory is not present next to the project;
# (f) non-vacuity: scripts/NonVacuity.lean compiles, and each of its 10 theorems depends only on propext,
#     Classical.choice, Quot.sound;
# (g) hygiene (scripts/check_hygiene.py): no absolute path in the files of the project; and, when the maintainers'
#     list of names that must not be published is present (HYGIENE_PATTERNS, by default a file in a directory next to
#     paper/ that is not published), none of those names either; without the list (as in the public repository) that
#     part is reported as skipped, not as a failure.
# Provenance (printed, not enforced): a sha256 over the project's files (`git ls-files`, or, outside a git checkout
# or with AUDIT_NO_GIT=1, every file except `.lake/`).
set -u
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
CORES=${CORES-0-3}
PIN=""
if [ -n "$CORES" ] && command -v taskset >/dev/null 2>&1 && taskset -c "$CORES" true >/dev/null 2>&1; then
  PIN="taskset -c $CORES"
fi
RUN="env LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-4} $PIN lake env lean"
fail=0

echo "== provenance (printed, not enforced) =="
if [ -z "${AUDIT_NO_GIT:-}" ] && git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  files=$(git ls-files --cached --others --exclude-standard . | LC_ALL=C sort -u); src="git ls-files, tracked and untracked-unignored"
else
  files=$(find . -path ./.lake -prune -o -type f -print | sed 's|^\./||' | LC_ALL=C sort); src="all files except .lake/"
fi
nfiles=$(echo "$files" | sed '/^$/d' | wc -l)
digest=$(echo "$files" | sed '/^$/d' | while IFS= read -r f; do [ -f "$f" ] && sha256sum -- "$f"; done | sha256sum | cut -d' ' -f1)
echo "sha256 over $nfiles files ($src; sha256sum lines, sorted by path): $digest"
echo

echo "== (0) the build is up to date with the sources =="
if nb_out=$($PIN lake build --no-build PositivityRigidityII 2>&1); then
  echo "lake build --no-build PositivityRigidityII: $(echo "$nb_out" | tail -1)"
else
  echo "$nb_out" | grep -v '^Note: \|^warning\|^⚠\|^ℹ\|^info' | tail -5
  echo "FAIL: the build is not up to date (run \`lake build\` first; it must succeed)"; fail=1
fi
echo

echo "== (a) no sorry / admit / native_decide in the Lean sources =="
stripped=$(find PositivityRigidityII scripts -name '*.lean' -print0 | LC_ALL=C sort -z | xargs -0 perl -e '
  for my $f (@ARGV) { open(my $h, "<:encoding(UTF-8)", $f) or die "$f: $!"; local $/; my $s = <$h>; close $h;
    my ($o, $d, $i, $n) = ("", 0, 0, length $s);
    while ($i < $n) { my $c = substr($s, $i, 2);
      if ($c eq "/-") { $d++; $i += 2; next }
      if ($d > 0) { if ($c eq "-/") { $d--; $i += 2 } else { $o .= "\n" if substr($s, $i, 1) eq "\n"; $i++ } next }
      if ($c eq "--") { $i++ while $i < $n && substr($s, $i, 1) ne "\n"; next }
      if (substr($s, $i, 1) eq "\"") { $i++; while ($i < $n && substr($s, $i, 1) ne "\"") { $i += (substr($s, $i, 1) eq "\\") ? 2 : 1 } $i++; next }
      $o .= substr($s, $i, 1); $i++ }
    binmode(STDOUT, ":encoding(UTF-8)");
    my $ln = 0; for my $l (split /\n/, $o) { $ln++; print "$f:$ln: $l\n" if $l =~ /\S/ } }' PositivityRigidityII.lean)
tok_hits=$(echo "$stripped" | perl -ne 'print if /^[^:]*:\d+: .*(?<![\w.])(sorry|admit|native_decide)(?![\w])/')
if [ -n "$tok_hits" ]; then echo "$tok_hits"; echo "FAIL: sorry/admit/native_decide in the sources"; fail=1
else echo "sorry/admit/native_decide (outside comments and strings; PositivityRigidityII, scripts): none"; fi
echo

echo "== (b) axioms: only in the ledger, counted in LEDGER.md =="
axiom_re='^[^:]*:[0-9]+: \s*(@\[[^]]*\]\s*)?(noncomputable\s+)?(private\s+|protected\s+)?axiom\s'
outside=$(echo "$stripped" | grep -E "$axiom_re" | grep -v '^PositivityRigidityII/Ledger\.lean:')
if [ -n "$outside" ]; then echo "$outside"; echo "FAIL: axiom declaration outside PositivityRigidityII/Ledger.lean"; fail=1
else echo "axiom declarations outside PositivityRigidityII/Ledger.lean (textual): none"; fi
n_text=$(echo "$stripped" | grep -E "$axiom_re" | grep -c '^PositivityRigidityII/Ledger\.lean:')
n_md=$(sed -n 's/^| \*\*Total\*\* | \*\*\([0-9]*\)\*\* |.*/\1/p' LEDGER.md | head -1)
audit_out=$($RUN scripts/Audit.lean 2>&1)
echo "$audit_out"
n_lean=$(echo "$audit_out" | sed -n 's/^ledger axioms (axiom declarations in PositivityRigidityII.Ledger): \([0-9]*\)$/\1/p')
echo "ledger axioms: $n_text in Ledger.lean (textual), ${n_lean:-?} in the environment, ${n_md:-?} in LEDGER.md (Total)"
if [ -z "$n_md" ] || [ -z "$n_lean" ] || [ "$n_text" != "$n_md" ] || [ "$n_lean" != "$n_md" ]; then
  echo "FAIL: the number of ledger axioms differs from LEDGER.md"; fail=1; fi
for ax in $(echo "$audit_out" | sed -n 's/^  PosRigII\.\([A-Za-z0-9_]*\)$/\1/p'); do
  grep -qF "\`$ax\`" LEDGER.md || { echo "FAIL: ledger axiom $ax is not named in LEDGER.md"; fail=1; }
done
for ax in $(echo "$audit_out" | sed -n 's/^Part I ledger axioms used by Part II ([0-9]* of [0-9]*): //p' | tr ',' ' '); do
  ax=${ax#PosRig.}
  grep -qF "\`$ax\`" LEDGER.md || { echo "FAIL: Part I ledger axiom $ax is used but not listed in LEDGER.md"; fail=1; }
done
echo "$audit_out" | grep -q '^axiom declarations outside PositivityRigidityII.Ledger: none$' \
  || { echo "FAIL: axiom declarations outside PositivityRigidityII.Ledger (environment)"; fail=1; }
echo "$audit_out" | grep -q '^axioms other than propext / Classical.choice / Quot.sound and the ledger axioms of Parts I and II .*: none$' \
  || { echo "FAIL: some declaration depends on an axiom outside the ledgers (sorryAx, native_decide, ...)"; fail=1; }
echo "$audit_out" | grep -q '^declarations depending on sorryAx: none$' \
  || { echo "FAIL: some declaration depends on sorryAx"; fail=1; }
if echo "$audit_out" | grep -q '^headline .*: \(MISSING\|NOT A THEOREM\)'; then
  echo "FAIL: a headline theorem is missing"; fail=1; fi
n_head=$(echo "$audit_out" | grep -c '^headline .*: theorem; ')
[ "$n_head" -eq 13 ] || { echo "FAIL: expected 13 headline theorems, found $n_head"; fail=1; }
echo

echo "== (c) regression: scripts/print_axioms.lean against axioms.log =="
pa_out=$($RUN scripts/print_axioms.lean 2>&1)
pa_exp=$(grep -v '^# ' axioms.log)
if [ "$pa_out" = "$pa_exp" ]; then
  echo "axioms.log reproduced exactly: $(echo "$pa_out" | grep -c "^'") declarations (all headline theorems among them)"
else
  echo "FAIL: #print axioms differs from axioms.log:"; diff <(echo "$pa_exp") <(echo "$pa_out") | head -40; fail=1
fi
if echo "$pa_out" | grep -q 'sorryAx'; then echo "FAIL: a printed declaration depends on sorryAx"; fail=1; fi
echo

echo "== (d) statement pin: scripts/Statements.lean against scripts/Statements.baseline.txt =="
st_out=$($RUN scripts/Statements.lean 2>&1)
if [ "$st_out" = "$(cat scripts/Statements.baseline.txt)" ]; then
  echo "statement pin: $(echo "$st_out" | head -1 | sed -n 's/^== statement pin: \([0-9]*\) declarations.*/\1/p') declarations, identical to scripts/Statements.baseline.txt"
else
  echo "FAIL: the statements differ from scripts/Statements.baseline.txt (the meaning of a headline or of an axiom changed):"
  diff <(cat scripts/Statements.baseline.txt) <(echo "$st_out") | head -60
  fail=1
fi
echo

echo "== (e) provenance: cited hashes and quoted log lines against the ancillary files =="
prov_out=$(python3 scripts/check_provenance.py 2>&1); prov_rc=$?
if [ $prov_rc -eq 0 ]; then
  echo "$(echo "$prov_out" | tail -1)"
elif [ $prov_rc -eq 2 ]; then
  echo "$prov_out" | tail -1; echo "(not counted as a failure)"
else
  echo "$prov_out" | grep -v '^OK'; echo "FAIL: scripts/check_provenance.py"; fail=1
fi
echo

echo "== (f) non-vacuity checks (scripts/NonVacuity.lean) =="
nv_out=$($RUN scripts/NonVacuity.lean 2>&1); nv_rc=$?
echo "$nv_out"
std_re="'PosRigII\.NonVacuity\.[A-Za-z0-9_]+' (does not depend on any axioms|depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\])"
nv_bad=$(echo "$nv_out" | sed '/^$/d' | grep -vxE "$std_re")
nv_n=$(echo "$nv_out" | grep -cxE "$std_re")
if [ $nv_rc -ne 0 ] || [ -n "$nv_bad" ]; then
  echo "FAIL: scripts/NonVacuity.lean has errors, or a theorem there uses an axiom other than propext, Classical.choice, Quot.sound"; fail=1
elif [ "$nv_n" -ne 10 ]; then echo "FAIL: expected 10 non-vacuity theorems, found $nv_n"; fail=1
else
  for t in classW_nonempty gammaInf_faithful voronoi_indexing positivity_transfer vanishing_transfer cones_not_junk \
           exact_magic_meaning zero_set_of_strict identity_theorem deriv_at_zero_of_nonneg; do
    echo "$nv_out" | grep -q "^'PosRigII\.NonVacuity\.$t' " || { echo "FAIL: non-vacuity theorem $t missing"; fail=1; }
  done
  echo "non-vacuity: $nv_n theorems, each with axioms among propext, Classical.choice, Quot.sound"
fi
echo

echo "== (g) hygiene of the project files =="
if hyg_out=$(python3 scripts/check_hygiene.py 2>&1); then
  echo "$hyg_out" | tail -1
else
  echo "$hyg_out"; echo "FAIL: scripts/check_hygiene.py"; fail=1
fi
echo
if [ $fail -eq 0 ]; then
  echo "no sorry/admit/native_decide; $n_md ledger axioms, all in Ledger.lean and LEDGER.md; axioms.log and the statement pin reproduced; provenance and hygiene checked; non-vacuity checks pass"
  echo "AUDIT PASSED"
else echo "AUDIT FAILED"; fi
exit $fail
