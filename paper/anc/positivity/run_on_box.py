"""Run the large-|t| certifiers cert_large_t.py and cert_gtail.py, UNCHANGED, on the trivial-bound box instead of the
certified coefficient balls: the large-|t| theorem on the trivial-bound box (Section 7 of the paper).

The box (boxlib.py; Section 6.1 of the paper): for n <= 300 each coefficient ball is replaced by the hull of
    [ c_n - w_n, c_n + w_n ],   c_n = n T1_n + delta_{n1}/4,   w_n = abar_n varrho(z_n),
that is, the term c = 1 of the Kloosterman series (S(+-1, n; 1) = 1) and the bound |S(+-1, n; c)| <= phi(c) for the terms
c >= 2 (proof of Theorem 6.1).  For n > 300 the certifiers use 0 < a_n <= A0(n) = abar_n (Theorems 6.1-6.2), which every
element of the box satisfies.  The certifiers enclose each quantity they bound (B and A, the integrals p(T0), n(T0) and
A_Phi, rhobar(4)) in Arb, as a function of the coefficient balls; so with the box hulls as inputs every certified bound
holds for every sequence in the box, in particular for the coefficients a_n of the paper.  (That each a_n enters linearly
only makes these enclosures tight.)  The optional file COEFF_EXTRA is not used.
Usage: run_on_box.py large_t T0 kappa Ys Yz Y3 Np Nn      (shipped run: large_t 9 0.5 1 0.90 4 2000 8000)
       run_on_box.py gtail"""
import sys, os, json, runpy, hashlib
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import poslib as L
import boxlib as BX
from flint import arb


def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()[:16]


class BoxCoeffs(L.Coeffs):
    """Coefficient balls = hulls of the trivial-bound box (n <= nmax); same interface as poslib.Coeffs."""
    def __init__(self, path_small, path_big, nmax=200, extra=None):
        d = json.load(open(path_big))
        self.meta = ('trivial-bound box from the T1 entries of %s' % os.path.basename(path_big),)
        self.nmax = nmax
        self.a = [None]
        for n in range(1, nmax + 1):
            self.a.append(BX.box_hull(n, d['T1'][str(n)]))
        assert all(self.a[n] > 0 and self.a[n] < L.Coeffs.A0(n) for n in range(1, nmax + 1)), 'box not inside (0, A0(n)]'
        print('box: a_1 in [%s, %s], a_2 in [%s, %s] ; every box hull for n <= %d lies in (0, A0(n)): True' % (
            arb(self.a[1].lower()).str(10), arb(self.a[1].upper()).str(10), arb(self.a[2].lower()).str(12),
            arb(self.a[2].upper()).str(12), nmax), flush=True)


which = sys.argv[1]
script = os.path.join(HERE, {'large_t': 'cert_large_t.py', 'gtail': 'cert_gtail.py'}[which])
print('run_on_box.py %s ; boxlib %s ; running the UNCHANGED %s (sha %s) on the trivial-bound box' % (
    sha(os.path.abspath(__file__)), sha(os.path.join(HERE, 'boxlib.py')), os.path.basename(script), sha(script)), flush=True)
L.Coeffs = BoxCoeffs
os.environ.pop('COEFF_EXTRA', None)
sys.argv = [script] + sys.argv[2:]
runpy.run_path(script, run_name='__main__')
