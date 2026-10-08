#!/usr/bin/env python3
"""Hygiene check of the files of this Lean project (scripts/audit.sh, check (g)); Python standard library only.

Every file of the project (outside .lake/ and build/; this script included) is searched for
  * generic patterns, always: absolute file-system paths;
  * a maintainers' list of names that must not be published, read from the file named by the environment variable
    HYGIENE_PATTERNS, by default a maintainers' file outside the published tree (DEFAULT_LIST below; a directory
    next to paper/ that is not published).  The list is optional: when the file is not present, as in the
    public repository, this part of the check is reported as skipped.  Format of the list: one line per pattern,
    "label<TAB>Python regular expression"; lines starting with '#' are comments.

Exit code 0 if no file matches, 1 otherwise (the matching lines are printed).
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
DEFAULT_LIST = os.path.join(ROOT, "..", "..", "..", "internal", "lean-hygiene-patterns.txt")

GENERIC = [("absolute path", r"(?<![\w.])/(?:home|Users|tmp|root|mnt)/")]


def load_list(path):
    out = []
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.rstrip("\n")
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            label, _, pat = line.partition("\t")
            out.append((label.strip() or "listed name", pat))
    return out


def files():
    for dirpath, dirnames, filenames in os.walk(ROOT):
        dirnames[:] = [d for d in dirnames if d not in (".lake", "build", ".git", "__pycache__")]
        for f in sorted(filenames):
            yield os.path.join(dirpath, f)


def main():
    path = os.environ.get("HYGIENE_PATTERNS", DEFAULT_LIST)
    patterns = list(GENERIC)
    if os.path.isfile(path):
        listed = load_list(path)
        patterns += listed
        note = f"{len(listed)} listed patterns"
    else:
        note = "list of names not present: that part SKIPPED"
    bad = 0
    n = 0
    for p in files():
        n += 1
        try:
            text = open(p, encoding="utf-8").read()
        except UnicodeDecodeError:
            continue
        for i, line in enumerate(text.splitlines(), 1):
            for what, pat in patterns:
                if re.search(pat, line):
                    print(f"{os.path.relpath(p, ROOT)}:{i}: {what}: {line.strip()[:120]}")
                    bad += 1
    print(f"hygiene: {n} files scanned, {len(GENERIC)} generic pattern(s) and {note}; {bad} matches")
    return 0 if bad == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
