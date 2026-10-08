#!/usr/bin/env python3
"""Provenance check of the ledger docstrings (scripts/audit.sh, check (e)); Python standard library only.

PositivityRigidityII/Ledger.lean cites files of the ancillary directory (the parent directory of this Lean project)
in two forms:
  * `relative/path` (sha256 HEX)   or   `relative/path` (sha256 HEX…)  -- a full SHA-256 or a prefix of one;
  * log `relative/path.log`: `line`, `line`, ...                       -- lines quoted from a shipped log.
This script checks that every cited file exists, that its SHA-256 starts with the cited hexadecimal string, and that
every quoted line occurs in the cited log, after replacing `±` by the logs' plus-slash-minus sign (Lean docstrings
cannot contain a slash followed by a hyphen); a quoted line may be a part of a log line (run times are omitted).  The
decisive lines of the primary proof of H > 0 (list REQUIRED below) must be among the quoted lines.

Exit code 0 if everything matches, 1 otherwise, 2 (with the word SKIPPED) if the ancillary directory is not
present next to this project (for instance when the Lean project is used on its own).
"""
import hashlib
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.dirname(HERE)
ANC = os.path.dirname(LEAN)
LEDGER = os.path.join(LEAN, "PositivityRigidityII", "Ledger.lean")
PM = "+" + "/" + "-"

# The decisive lines of the primary proof of H > 0 on the real line (Corollary 7.12: Certificate M-box, Theorem 6.8, and
# the large-|t| theorem on the trivial-bound box at T0 = 9, Theorem 7.11 with Proposition 7.10).  They must be quoted in
# the ledger (and, like every quoted line, occur in the cited log).
REQUIRED = [
    ("positivity/logs/cert_moments_box.log",
     "for |t| <= 10.35546875 (moments M_0..M_30) ; covers [0, 9]: True"),
    ("positivity/logs/cert_large_t_T9_box.log", "margin = [0.965950136102 ± 4.98e-13]"),
    ("positivity/logs/cert_large_t_T9_box.log",
     "DECISIVE (all-Arb): Theorem L hypotheses verified for T0 = 9: True"),
    ("positivity/logs/cert_gtail_box.log", "rhobar(4) = [4.347086309e-9 ± 7.56e-20]  (< 1 needed): True"),
    ("positivity/logs/cert_gtail_box.log", "DECISIVE: g > 0 on [4, oo): True"),
]


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def main():
    if not os.path.isdir(os.path.join(ANC, "positivity")):
        print("SKIPPED: the ancillary directory (../positivity) is not present")
        return 2
    text = open(LEDGER, encoding="utf-8").read()
    bad = 0
    n_hash = n_line = 0
    for path, hexd in re.findall(r"`([A-Za-z0-9_./-]+)`\s*\(sha256 ([0-9a-f]{16,64})…?\)", text):
        n_hash += 1
        full = os.path.join(ANC, path)
        if not os.path.isfile(full):
            print(f"FAIL: cited file missing: {path}")
            bad += 1
            continue
        got = sha256(full)
        if got.startswith(hexd):
            print(f"OK hash {path}: {hexd}")
        else:
            print(f"FAIL hash {path}: cited {hexd}, file has {got}")
            bad += 1
    quoted = []
    for path, block in re.findall(r"log `([^`]+\.log)`:((?:\s*`[^`]*`\s*[,;.)]*)+)", text):
        full = os.path.join(ANC, path)
        if not os.path.isfile(full):
            print(f"FAIL: cited log missing: {path}")
            bad += 1
            continue
        lines = open(full, encoding="utf-8").read().splitlines()
        for q in re.findall(r"`([^`]*)`", block):
            quoted.append((path, q))
            n_line += 1
            target = q.replace("±", PM)
            if any(target in ln for ln in lines):
                print(f"OK line {path}: {q[:70]}")
            else:
                print(f"FAIL line {path}: not found verbatim: {q}")
                bad += 1
    for path, frag in REQUIRED:
        if any(p == path and frag in q for p, q in quoted):
            print(f"OK required {path}: {frag[:60]}")
        else:
            print(f"FAIL: required citation missing from the ledger: {path}: {frag}")
            bad += 1
    if n_hash == 0 or n_line == 0:
        print("FAIL: no citations found (the docstring format changed?)")
        bad += 1
    print(f"{n_hash} SHA-256 citations, {n_line} quoted log lines: {'all match' if bad == 0 else f'{bad} mismatches'}")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
