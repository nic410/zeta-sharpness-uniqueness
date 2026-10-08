#!/usr/bin/env python3
"""Compare verifier logs after removing what legitimately changes between runs (dates, machine line, timings).

Usage (from anc/):
    python tools/logdiff.py OLD.log NEW.log          compare two logs
    python tools/logdiff.py OLD_DIR NEW_DIR          compare every *.log under OLD_DIR with the same path under NEW_DIR
Options:
    -v               print the differing lines (unified diff of the normalised logs, at most 40 lines per log)
    --any-order      also accept logs whose normalised lines agree up to order (progress lines of parallel runs)

Normalisation (nothing else is changed; every printed number other than a timing must agree digit for digit):
    * the header lines '# date : ...' and '# system : ...' are dropped ('# command' and '# python' are compared);
    * the footer '# exit code K; wall time T s' keeps K and drops T;
    * timing tokens are replaced by '<T>': a number followed by ' s' or 's' and then ')', ']', ',', ';' or the end of
      the line (e.g. '(455 s)', '[0.1 s]', 'total time 1.2 s'), and the JSON field '"secs": T'.
Exit code 0 if every compared pair agrees (IDENTICAL, or SAME LINES IN ANOTHER ORDER with --any-order), 1 otherwise.
Dependencies: Python 3 standard library only.
"""
import difflib
import os
import re
import sys

TIMING = re.compile(r'(?<![\w.])\d+(?:\.\d+)?\s?s(?=[)\],;]|\s*$)')
SECS = re.compile(r'"secs": [0-9.eE+-]+')
FOOTER = re.compile(r'^# exit code (-?\d+); wall time .*$')


def normalise(path):
    out = []
    with open(path, errors='replace') as fh:
        for line in fh:
            line = line.rstrip()
            if line.startswith('# date') or line.startswith('# system'):
                continue
            m = FOOTER.match(line)
            if m:
                out.append('# exit code %s; wall time <T>' % m.group(1))
                continue
            line = SECS.sub('"secs": <T>', line)
            out.append(TIMING.sub('<T>', line))
    return out


def compare(a, b, verbose, any_order):
    la, lb = normalise(a), normalise(b)
    if la == lb:
        return 'IDENTICAL', True
    if sorted(la) == sorted(lb):
        return 'SAME LINES IN ANOTHER ORDER', any_order
    diff = [d for d in difflib.unified_diff(la, lb, lineterm='', n=0) if not d.startswith(('---', '+++', '@@'))]
    if verbose:
        for d in diff[:40]:
            print('    ' + d)
    return 'DIFFERENT (%d lines)' % len(diff), False


def main(argv):
    verbose = '-v' in argv
    any_order = '--any-order' in argv
    args = [x for x in argv if not x.startswith('-')]
    if len(args) != 2:
        sys.exit(__doc__)
    a, b = args
    if os.path.isdir(a) and os.path.isdir(b):
        rels = sorted(os.path.relpath(os.path.join(r, f), a) for r, _, fs in os.walk(a) for f in fs if f.endswith('.log'))
        pairs = [(os.path.join(a, r), os.path.join(b, r), r) for r in rels]
    else:
        pairs = [(a, b, b)]
    ok_all, n_missing = True, 0
    for pa, pb, name in pairs:
        if not os.path.isfile(pb):
            print('%-50s MISSING in %s' % (name, b))
            n_missing += 1
            ok_all = False
            continue
        if verbose:
            print('%s:' % name)
        verdict, ok = compare(pa, pb, verbose, any_order)
        ok_all = ok_all and ok
        print('%-50s %s' % (name, verdict))
    print('%d log(s) compared, %d missing: %s' % (len(pairs) - n_missing, n_missing, 'ALL AGREE' if ok_all else 'DIFFERENCES'))
    return 0 if ok_all else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
