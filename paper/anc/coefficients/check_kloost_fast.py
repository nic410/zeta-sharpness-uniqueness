"""Self-test (not a certificate) of the float Kloosterman engine kloost_fast.py against Arb: the cosine table (random
samples) and S(1,j;q) against brute-force Arb sums and the Arb-DFT tables of coefflib.py."""
import sys, os, random, time
import hashlib; print('%s sha %s' % (os.path.basename(__file__), hashlib.sha256(open(os.path.abspath(__file__), 'rb').read()).hexdigest()[:16]))  # SELF_SHA
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from kloost_fast import *
from coefflib import kloost_brute, kloost_table, arb, ctx
random.seed(1)
worst = 0.0
for q in [7, 97, 1009, 10007, 65537, 99991, 3**9, 2**13, 5**6, 199999]:
    C = cos_table_rig(q)
    for _ in range(300):
        k = random.randrange(q)
        ctx.prec = 128
        ex = (arb(2) * k / q).cos_pi()
        d = abs(float((arb(C[k]) - ex).mid())) + float(ex.rad())
        worst = max(worst, d)
print('cos_table_rig: max |C[k] - cos(2 pi k/q)| over samples = %.2e  (EPS_TAB = %.0e)' % (worst, EPS_TAB))
for (q, p) in [(7, 7), (97, 97), (1009, 1009), (3**5, 3), (2**7, 2), (5**4, 5), (10007, 10007)]:
    K = PrimePowerKloost(q, p)
    mid, err = kloost_table(q, p, 96)
    w = 0.0
    for j in list(range(0, min(q, 50))) + [q - 1, q - 7, q // 3]:
        s, e = K.S(j)
        w = max(w, abs(s - mid[j]))
        if q <= 1009 and j < 5:
            b = kloost_brute(1, j, q)
            assert abs(s - float(b.mid())) <= e + float(b.rad()), (q, j, s, b)
    print('q=%6d: max |fast - DFT table| = %.2e ; proved error bound %.2e + table err %.2e' % (q, w, K.err, err))
t = time.time(); K = PrimePowerKloost(199999, 199999); t1 = time.time() - t
t = time.time()
for j in range(1, 41): K.S(j)
print('q=199999: setup %.2fs, 40 sums %.2fs' % (t1, time.time() - t))
