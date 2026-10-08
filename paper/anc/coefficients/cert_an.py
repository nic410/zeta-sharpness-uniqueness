"""Certificate (Appendix A.1 of the paper): rigorous enclosures of a_n = n Kc_n + delta_{n,1}/4  (b_n = C a_n), n <= NBIG
(Kc_n is S_n of the paper).

  Kc_n = sum_{c>=1} c^{-1}[S(1,n;c) Jhat(4 pi sqrt n/c) - S(-1,n;c) Ihat(4 pi sqrt n/c)]

  n <= NSMALL : all c <= X summed exactly (Arb balls; Kloosterman tables from rigorous Arb DFTs), c > X by weil_tail.
  NSMALL < n <= NBIG : c <= C2(n) := max(C2, ceil(4 pi sqrt n) + 1) summed exactly, c > C2(n) by weil_tail.
Every number below is an Arb ball that provably contains the true value (see the coefflib.py docstring for the bounds used).
Writes coefficients/out/an_small_OUTTAG.json (n <= NSMALL) and coefficients/out/an_cert_OUTTAG.json (n <= NBIG); the
Kloosterman tables are cached in coefficients/cache/ (not shipped; rebuilt when absent).

Usage: cert_an.py NSMALL X NBIG C2 OUTTAG
"""
import sys, os, time, json, hashlib, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from coefflib import *

NSMALL, X, NBIG, C2, TAG = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
PREC = 96
HERE = os.path.dirname(os.path.abspath(__file__))           # coefficients/
BASE = os.path.dirname(HERE)                                 # the top directory of the ancillary files
OUT, CACHE = os.path.join(HERE, 'out'), os.path.join(HERE, 'cache')   # fresh outputs; Kloosterman-table cache
os.makedirs(OUT, exist_ok=True); os.makedirs(CACHE, exist_ok=True)
t0 = time.time()


def sha(path):
    return hashlib.sha256(open(path, 'rb').read()).hexdigest()[:16]


print('cert_an.py  NSMALL=%d X=%d NBIG=%d C2=%d  prec=%d' % (NSMALL, X, NBIG, C2, PREC))
print('input hashes: coefflib.py %s  cert_an.py %s' % (sha(os.path.join(HERE, 'coefflib.py')), sha(os.path.abspath(__file__))))

CMAX_BIG = max(C2, int(math.ceil(4 * math.pi * math.sqrt(NBIG))) + 1)
XT = max(X, CMAX_BIG)
tfn = os.path.join(CACHE, 'kloost_tables_X%d.npz' % XT)
if os.path.exists(tfn):
    tabs = load_tables(tfn); spf = spf_sieve(XT)
    print('Kloosterman tables loaded from %s (sha %s)' % (os.path.basename(tfn), sha(tfn)))
else:
    tabs, spf = build_tables(XT, PREC, verbose=False)
    save_tables(tabs, tfn)
    print('Kloosterman tables for prime powers <= %d built and saved (%.0fs), sha %s' % (XT, time.time() - t0, sha(tfn)))
print('max table error %.2e' % max(e for (_, e) in tabs.values()), flush=True)

ctx.prec = PREC
res = {}
# ---------------------------------------------------------------- small n: c <= X exact
ns = list(range(1, NSMALL + 1))
acc = [arb(0)] * NSMALL                  # sum_{2<=c<=X}
accal = [arb(0)] * NSMALL                # alpha_n = a_n(1): sum_{1<=c<=X} 2 c^{-1}[S J_2 - S I_2]
acc_abs = [arb(0)] * NSMALL              # sum |term| (for the record)
c2t = [arb(0)] * NSMALL
for c in range(1, X + 1):
    Sp, Sm = kloost_pm(ns, c, tabs, spf, PREC)
    for i, n in enumerate(ns):
        ctx.prec = PREC
        zc = 4 * arb.pi() * arb(n).sqrt() / c
        if zc.upper() < 8:
            ctx.prec = PREC + 16
            accal[i] += 2 * (Sp[i] * zc.bessel_j(2) - Sm[i] * zc.bessel_i(2)) / c
        else:
            ctx.prec = PREC + 32
            accal[i] += 2 * (Sp[i] * zc.bessel_j(2) - Sm[i] * zc.bessel_i(2)) / c
        ctx.prec = PREC
        if c == 1:
            continue
        tm = term_c(n, c, Sp[i], Sm[i], PREC)
        acc[i] += tm
        acc_abs[i] += abs(tm)
        if c == 2:
            c2t[i] = tm
    if c in (100, 1000, 3000) or c % 5000 == 0:
        print('   small n: c <= %d done (%.0fs)' % (c, time.time() - t0), flush=True)
for i, n in enumerate(ns):
    T1 = c1_term(n, 256)
    ctx.prec = PREC
    tail = weil_tail(n, X, PREC)
    K = T1 + acc[i] + arb(0, tail.upper())
    a = n * K + (arb(1) / 4 if n == 1 else 0)
    tal = 2 * weil_tail_alpha(n, X, PREC)
    al = accal[i] + arb(0, tal.upper())
    res[n] = dict(a=a, K=K, T1=T1, cs=acc[i], cs_abs=acc_abs[i], tail=tail, c2=c2t[i], cmax=X, alpha=al, alpha_tail=tal)
print('small n done (%.0fs)' % (time.time() - t0), flush=True)
ctx.prec = PREC
a1s = res[1]['a']
outs = {'meta': dict(NSMALL=NSMALL, X=X, prec=PREC, hash_lib=sha(os.path.join(HERE, 'coefflib.py')), hash_script=sha(os.path.abspath(__file__)),
                     note='a_n = n Kc_n + delta_{n,1}/4 (b_n = C a_n); alpha_n = a_n(1) Niebur coefficient at nu=1 (alpha_n prime = 4 Kc_n). Balls rigorous.'),
        'a': {n: res[n]['a'].str(30) for n in ns}, 'K': {n: res[n]['K'].str(30) for n in ns},
        'alpha': {n: res[n]['alpha'].str(30) for n in ns},
        'a_mid_rad': {n: [res[n]['a'].mid().str(40, radius=False), float(res[n]['a'].rad())] for n in ns},
        'alpha_mid_rad': {n: [res[n]['alpha'].mid().str(40, radius=False), float(res[n]['alpha'].rad())] for n in ns},
        'ratio_b_over_b1': {n: (res[n]['a'] / a1s).str(30) for n in ns},
        'tail_bound_K': {n: res[n]['tail'].str(6) for n in ns}}
fns = os.path.join(OUT, 'an_small_%s.json' % TAG)
json.dump(outs, open(fns, 'w'), indent=0)
os.system('"%s" "%s" "%s"' % (sys.executable, os.path.join(HERE, 'fix_json_radii.py'), fns))
print('wrote %s sha %s' % (os.path.relpath(fns, BASE), sha(fns)))
print('a_1 = %s ; alpha_1 = %s' % (res[1]['a'].str(25), res[1]['alpha'].str(25)))
for n in range(2, 7):
    print('b_%d/b_1 = %s' % (n, (res[n]['a'] / a1s).str(22)))
sys.stdout.flush()

# ---------------------------------------------------------------- large n: c <= C2(n) exact
for n in range(NSMALL + 1, NBIG + 1):
    Cn = max(C2, int(math.ceil(4 * math.pi * math.sqrt(n))) + 1)
    s = arb(0); sa = arb(0); c2v = arb(0)
    for c in range(2, Cn + 1):
        Sp, Sm = kloost_pm([n], c, tabs, spf, PREC)
        tm = term_c(n, c, Sp[0], Sm[0], PREC)
        s += tm; sa += abs(tm)
        if c == 2:
            c2v = tm
    T1 = c1_term(n, 256)
    ctx.prec = PREC
    tail = weil_tail(n, Cn, PREC)
    K = T1 + s + arb(0, tail.upper())
    res[n] = dict(a=n * K, K=K, T1=T1, cs=s, cs_abs=sa, tail=tail, c2=c2v, cmax=Cn)
    if n % 250 == 0:
        print('   large n: n = %d done (%.0fs)' % (n, time.time() - t0), flush=True)

# ---------------------------------------------------------------- checks and output
ctx.prec = PREC
allpos = all(r['a'] > 0 for r in res.values())
print('\nDECISIVE: all a_n > 0 (ball lower endpoints) for n <= %d: %s' % (NBIG, allpos))
worst = max(((r['cs_abs'] + r['tail']) / abs(r['T1']), n) for n, r in res.items())
print('DECISIVE: max_n (sum_{c>=2}|term_c| incl. tail bound)/(c=1 term) = %s at n = %d'
      % (worst[0].str(5), worst[1]))
a1 = res[1]['a']
print('a_1 = %s' % a1.str(30))
print('Kc_1 = %s   (c=1 term %s)' % (res[1]['K'].str(25), res[1]['T1'].str(25)))
ctx.prec = PREC
Aratio = 1 / (8 * arb.pi() ** 4 * (1 + 4 * res[1]['K']))
print('A/b_1 = 1/(8 pi^4 (1 + 4 Kc_1)) = %s' % Aratio.str(20))
for n in range(2, 11):
    print('b_%d/b_1 = %s' % (n, (res[n]['a'] / a1).str(22)))
for n in (20, 30, 40, 50, 60, 100, 200, 400, 800, 1500):
    if n in res:
        print('a_%d = %s   rel.rad %.2e   (c-tail bound %s, c<=%d)' % (n, res[n]['a'].str(20), float(res[n]['a'].rad() / abs(res[n]['a'].mid())), res[n]['tail'].str(3), res[n]['cmax']))

out = {'meta': dict(NSMALL=NSMALL, X=X, NBIG=NBIG, C2=C2, prec=PREC, hash_lib=sha(os.path.join(HERE, 'coefflib.py')),
                    hash_script=sha(os.path.abspath(__file__)),
                    note='a_n = n Kc_n + delta_{n,1}/4 ; balls [mid +/- rad] rigorous; b_n = C a_n'),
       'a': {n: [r['a'].mid().str(40, radius=False), float(r['a'].rad())] for n, r in res.items()},
       'a_str': {n: r['a'].str(30) for n, r in res.items()},
       'K': {n: r['K'].str(30) for n, r in res.items()},
       'T1': {n: r['T1'].str(40) for n, r in res.items()},
       'tail_bound': {n: r['tail'].str(6) for n, r in res.items()},
       'cmax': {n: r['cmax'] for n, r in res.items()},
       'ratio_b_over_b1': {n: (r['a'] / a1).str(30) for n, r in res.items() if n <= NSMALL}}
fn = os.path.join(OUT, 'an_cert_%s.json' % TAG)
json.dump(out, open(fn, 'w'), indent=0)
os.system('"%s" "%s" "%s"' % (sys.executable, os.path.join(HERE, 'fix_json_radii.py'), fn))
print('wrote %s  sha %s  (%.0fs)' % (os.path.relpath(fn, BASE), sha(fn), time.time() - t0))
