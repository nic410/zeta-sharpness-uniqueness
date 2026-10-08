"""Compare the fresh outputs in coefficients/out/ (written by cert_an.py, cert_small_n.py and make_extra.py) with the three
pinned coefficient files in coefficients/data/, which are the inputs read by positivity/.  Not used in any proof.

For each pinned file, every certified ball of the fresh file -- a [midpoint string, radius] pair or an Arb ball string
'[m +/- r]' -- is compared with the entry under the same key of the pinned file, and classified as
    identical    the same midpoint string and the same radius (for a ball string: the same string),
    overlapping  different, but the two balls intersect,
    DISJOINT     the two balls do not intersect.
Other entries (the integer cutoffs 'cmax') must be equal.  Both files must have the same keys.  The 'meta' entries
(parameters, the SHA-256 prefixes of the producing scripts, notes) are not compared.
Second check: the split-independent values of the cross-check run of cert_H0.py with eta1 = 1.25
(coefficients/out/H0_cert_eta1_1.25_crosscheck.json) must overlap those of the run with eta1 = 1 (coefficients/out/H0_cert.json);
J_low and J_high are integrals over different ranges for the two splits and are not compared."""
import os, json, hashlib
from flint import arb, ctx
ctx.prec = 256
HERE = os.path.dirname(os.path.abspath(__file__))                                      # coefficients/
OUT, DATA = os.path.join(HERE, 'out'), os.path.join(HERE, 'data')
sha = lambda f: hashlib.sha256(open(f, 'rb').read()).hexdigest()[:16]
print('compare_outputs.py sha %s' % sha(os.path.abspath(__file__)))


def is_pair(v):
    return isinstance(v, list) and len(v) == 2 and isinstance(v[0], str) and isinstance(v[1], (int, float))


def ball(v):
    """the Arb ball of a stored entry: arb(mid, rad) for a [mid, rad] pair; Arb parses '[m +/- r]' strings itself."""
    return arb(v[0], v[1]) if is_pair(v) else arb(v)


def leaves(d, path=()):
    """(key path, value) for every non-dict entry, the 'meta' entry excluded."""
    for k, v in d.items():
        if not path and k == 'meta':
            continue
        if isinstance(v, dict):
            yield from leaves(v, path + (k,))
        else:
            yield path + (k,), v


ok_all = True
tot = {'identical': 0, 'overlapping': 0, 'DISJOINT': 0, 'other equal': 0, 'DIFFERENT': 0, 'MISSING': 0}
for nm in ['an_small_X1e4.json', 'an_cert_X1e4.json', 'extra_smalln_X3e5.json']:
    fp, ff = os.path.join(DATA, nm), os.path.join(OUT, nm)
    P, F = dict(leaves(json.load(open(fp)))), dict(leaves(json.load(open(ff))))
    cnt = dict.fromkeys(tot, 0)
    notes = []
    for key in sorted(set(P) | set(F), key=lambda k: [(0, int(x)) if x.isdigit() else (1, x) for x in k]):
        if key not in P or key not in F:
            cls = 'MISSING'
        elif F[key] == P[key]:
            cls = 'identical' if (is_pair(F[key]) or isinstance(F[key], str)) else 'other equal'
        elif (is_pair(F[key]) or isinstance(F[key], str)) and (is_pair(P[key]) or isinstance(P[key], str)):
            cls = 'overlapping' if ball(F[key]).overlaps(ball(P[key])) else 'DISJOINT'
        else:
            cls = 'DIFFERENT'
        cnt[cls] += 1
        if cls not in ('identical', 'other equal'):
            notes.append('    %-12s %-24s pinned %s ; fresh %s' % (cls, '/'.join(key), P.get(key), F.get(key)))
    ok = cnt['DISJOINT'] == cnt['DIFFERENT'] == cnt['MISSING'] == 0
    ok_all &= ok
    for k in tot:
        tot[k] += cnt[k]
    print('%-24s pinned sha %s, fresh sha %s (byte-identical: %s) ; %d balls: %d identical, %d overlapping, %d disjoint ; '
          '%d other entries equal, %d different ; %d keys missing on one side ; ok: %s'
          % (nm, sha(fp), sha(ff), sha(fp) == sha(ff), cnt['identical'] + cnt['overlapping'] + cnt['DISJOINT'], cnt['identical'],
             cnt['overlapping'], cnt['DISJOINT'], cnt['other equal'], cnt['DIFFERENT'], cnt['MISSING'], ok))
    for line in notes[:40]:
        print(line)
nb = tot['identical'] + tot['overlapping'] + tot['DISJOINT']
print('DECISIVE: every certified ball of the fresh run is identical to (same midpoint string and radius) or overlaps the '
      'pinned ball (%d balls: %d identical, %d overlapping only) and all other entries agree: %s'
      % (nb, tot['identical'], tot['overlapping'], ok_all))

f1, f2 = os.path.join(OUT, 'H0_cert.json'), os.path.join(OUT, 'H0_cert_eta1_1.25_crosscheck.json')
h1, h2 = json.load(open(f1)), json.load(open(f2))
print('\n%s (sha %s, eta1 = %s) vs %s (sha %s, eta1 = %s):' % (os.path.basename(f1), sha(f1), h1['meta']['eta1'], os.path.basename(f2), sha(f2), h2['meta']['eta1']))
ok_h = True
for k in ['Pint', 'twopiM', 'H_raw0', 'C', 'b1', 'A', 'Ghat_S_1']:
    b1, b2 = ball(h1[k]), ball(h2[k])
    ov = b1.overlaps(b2); ok_h &= ov
    print('    %-9s %s +- %.3e  |  %s +- %.3e  overlap: %s' % (k, h1[k][0][:22], h1[k][1], h2[k][0][:22], h2[k][1], ov))
print('DECISIVE: the eta1 = 1.25 cross-check of cert_H0.py overlaps the eta1 = 1 run in all 7 split-independent values: %s' % ok_h)
