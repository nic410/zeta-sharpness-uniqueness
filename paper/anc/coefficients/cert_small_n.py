"""Certificate (Appendix A.1 of the paper): rigorous a_n = n Kc_n + delta_{n,1}/4 and alpha_n = a_n(1) for a FEW small n
with a LARGE c-cutoff X (Kc_n is S_n of the paper, alpha_n is A_n(1)).

Kloosterman sums: c = q * r with q the (unique, since Q0^2 > X) prime-power factor q > Q0 if any:
    S(1,n;c) = S(1, n rbar^2 mod q; q) * S(1, n qbar^2 mod r; r)        (twisted multiplicativity)
  - prime powers q <= Q0: rigorous Arb-DFT tables (coefficients/cache/kloost_tables_X{Q0}.npz, written by cert_an.py,
    or rebuilt here when absent);
  - prime powers q > Q0: kloost_fast.PrimePowerKloost (exact residues + rigorous float cos table + Higham summation bound).
Bessel hats: coefflib (Arb). Tail c > X: coefflib.weil_tail / weil_tail_alpha.
Writes coefficients/out/an_smalln_TAG.json.
Usage: cert_small_n.py X Q0 LIST TAG    (LIST: comma-separated values of n, e.g. 1,2,3,4,5,6)
"""
import sys, os, time, json, hashlib, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from coefflib import *
from kloost_fast import PrimePowerKloost

X, Q0 = int(sys.argv[1]), int(sys.argv[2])
ns = [int(v) for v in sys.argv[3].split(',')]
TAG = sys.argv[4]
PREC = 96
HERE = os.path.dirname(os.path.abspath(__file__)); BASE = os.path.dirname(HERE)     # coefficients/ ; the top directory
OUT, CACHE = os.path.join(HERE, 'out'), os.path.join(HERE, 'cache')   # fresh outputs; Kloosterman-table cache
os.makedirs(OUT, exist_ok=True); os.makedirs(CACHE, exist_ok=True)
assert Q0 * Q0 > X
t0 = time.time()


def sha(path):
    return hashlib.sha256(open(path, 'rb').read()).hexdigest()[:16]


print('cert_small_n.py X=%d Q0=%d ns=%s prec=%d' % (X, Q0, ns, PREC))
print('input hashes: coefflib %s kloost_fast %s script %s' % (sha(os.path.join(HERE, 'coefflib.py')), sha(os.path.join(HERE, 'kloost_fast.py')), sha(os.path.abspath(__file__))))
tfn = os.path.join(CACHE, 'kloost_tables_X%d.npz' % Q0)
if os.path.exists(tfn):
    tabs = load_tables(tfn)
    print('Arb-DFT tables for prime powers <= %d loaded (sha %s)' % (Q0, sha(tfn)))
else:
    tabs, _ = build_tables(Q0, PREC)
    save_tables(tabs, tfn)
    print('Arb-DFT tables for prime powers <= %d built (sha %s)' % (Q0, sha(tfn)))
spf = spf_sieve(X)

# ---------------------------------------------------------------- large prime-power factors q > Q0
# qpart[c] = (list S(1, n rbar^2; q), list S(1, -n rbar^2; q), err, q)   for c = q r
qpart = {}
nq = 0; worst_err = 0.0
for p in range(2, X + 1):
    if spf[p] != p:
        continue
    q = p
    while q <= X:
        if q > Q0:
            K = PrimePowerKloost(q, p)
            worst_err = max(worst_err, K.err)
            for r in range(1, X // q + 1):
                if r % p == 0:
                    continue
                m = pow(r, -2, q)
                Sp = [K.S((n * m) % q)[0] for n in ns]
                Sm = [K.S((-n * m) % q)[0] for n in ns]
                qpart[q * r] = (Sp, Sm, K.err, q)
            nq += 1
            if nq % 2000 == 0:
                print('   large prime powers: %d done (q ~ %d), %.0fs' % (nq, q, time.time() - t0), flush=True)
        q *= p
print('large prime-power Kloosterman sums done: %d moduli q > %d, max proved float error %.2e (%.0fs)' % (nq, Q0, worst_err, time.time() - t0), flush=True)

# ---------------------------------------------------------------- main sum
ctx.prec = PREC
N = len(ns)
accK = [arb(0)] * N; accA = [arb(0)] * N
checkpoints = {}
for c in range(1, X + 1):
    if c in qpart:
        Sp_q, Sm_q, e, q = qpart[c]
        r = c // q
        if r == 1:
            Sp = [arb(v, e) for v in Sp_q]; Sm = [arb(v, e) for v in Sm_q]
        else:
            qb2 = pow(q, -2, r)
            Sp = []; Sm = []
            for i, n in enumerate(ns):
                rp, rm = kloost_pm([(n * qb2) % r], r, tabs, spf, PREC)    # S(1,m;r), S(-1,m;r) = S(1,-m;r)
                Sp.append(arb(Sp_q[i], e) * rp[0]); Sm.append(arb(Sm_q[i], e) * rm[0])
    else:
        Sp, Sm = kloost_pm(ns, c, tabs, spf, PREC)
    for i, n in enumerate(ns):
        ctx.prec = PREC
        zc = 4 * arb.pi() * arb(n).sqrt() / c
        ctx.prec = PREC + 16
        accA[i] += 2 * (Sp[i] * zc.bessel_j(2) - Sm[i] * zc.bessel_i(2)) / c
        ctx.prec = PREC
        I, J = hats(zc, PREC)
        ctx.prec = PREC
        accK[i] += (Sp[i] * J - Sm[i] * I) / c
    if c in (10000, 30000, 100000, 300000, 1000000) and c < X:
        checkpoints[c] = [accK[i].str(25) for i in range(N)]
        print('   c <= %d: Kc partial sums %s  (%.0fs)' % (c, [accK[i].str(18) for i in range(N)], time.time() - t0), flush=True)
res = {}
for i, n in enumerate(ns):
    ctx.prec = PREC
    tK = weil_tail(n, X, PREC); tA = 2 * weil_tail_alpha(n, X, PREC)
    K = accK[i] + arb(0, tK.upper()); A = accA[i] + arb(0, tA.upper())
    a = n * K + (arb(1) / 4 if n == 1 else 0)
    res[n] = dict(a=a, K=K, alpha=A, tailK=tK, tailA=tA)
    print('DECISIVE n=%d: Kc_n = %s ; a_n = %s (rel rad %.2e) ; alpha_n = %s ; c-tail bounds %s / %s'
          % (n, K.str(20), a.str(20), float(a.rad() / abs(a.mid())), A.str(20), tK.str(4), tA.str(4)))
if 1 in res:
    a1 = res[1]['a']
    for n in ns:
        if n > 1:
            print('b_%d/b_1 = %s' % (n, (res[n]['a'] / a1).str(20)))
    print('A/b_1 = 1/(8 pi^4 (1 + 4 Kc_1)) = %s' % (1 / (8 * arb.pi() ** 4 * (1 + 4 * res[1]['K']))).str(20))
out = {'meta': dict(X=X, Q0=Q0, ns=ns, prec=PREC, hash_lib=sha(os.path.join(HERE, 'coefflib.py')), hash_fast=sha(os.path.join(HERE, 'kloost_fast.py')),
                    hash_script=sha(os.path.abspath(__file__)), note='a_n = n Kc_n + delta_{n,1}/4 ; alpha_n = a_n(1) ; Arb ball strings (rigorous)'),
       'a': {n: r['a'].str(30) for n, r in res.items()}, 'K': {n: r['K'].str(30) for n, r in res.items()},
       'alpha': {n: r['alpha'].str(30) for n, r in res.items()},
       'a_mid_rad': {n: [r['a'].mid().str(40, radius=False), float(r['a'].rad())] for n, r in res.items()},
       'K_mid_rad': {n: [r['K'].mid().str(40, radius=False), float(r['K'].rad())] for n, r in res.items()},
       'alpha_mid_rad': {n: [r['alpha'].mid().str(40, radius=False), float(r['alpha'].rad())] for n, r in res.items()},
       'checkpoints_K': checkpoints}
fn = os.path.join(OUT, 'an_smalln_%s.json' % TAG)
json.dump(out, open(fn, 'w'), indent=0)
os.system('"%s" "%s" "%s"' % (sys.executable, os.path.join(HERE, 'fix_json_radii.py'), fn))
print('wrote %s sha %s (%.0fs)' % (os.path.relpath(fn, BASE), sha(fn), time.time() - t0))
