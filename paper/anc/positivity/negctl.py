"""Negative control: the same all-Arb certifier with ALL error terms, applied to coefficients with
the c >= 2 Kloosterman terms dropped, a_n -> n*T1_n + delta_{n,1}/4 (T1 = c = 1 term: the 'T1' ball strings of
an_cert_X1e4.json; the printed radius is KEPT and doubled for decimal printing).  Certifies an UPPER bound R < 0 on
small cells."""
import os, sys, json, hashlib, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ.pop('COEFF_EXTRA', None)
import cert_window as CW
import poslib as L
from flint import arb
d = json.load(open(CW.COEFF_DIR + 'an_cert_X1e4.json'))
class NegCoeffs(L.Coeffs):
    def __init__(self, nmax=300):
        self.nmax = nmax; self.a = [None]
        for n in range(1, nmax + 1):
            s = d['T1'][str(n)]
            if '+/-' in s:
                mid, rad = s.strip('[] ').split('+/-')
                T1 = arb(mid.strip(), float(rad) * 2)
            else:
                T1 = arb(s)
            self.a.append(n * T1 + (arb(1) / 4 if n == 1 else 0))
        # the tail n > nmax uses A0(n): n*T1_n <= A0(n) (the upper bound A0(n) of the coefficient bound proved in the paper
        # is a bound on the c = 1 main term) -- checked:
        assert self.a[nmax] < L.Coeffs.A0(nmax)
here = os.path.dirname(os.path.abspath(__file__))
H = lambda f: hashlib.sha256(open(f, 'rb').read()).hexdigest()[:16]
print('negctl: hashes poslib %s cert_window %s negctl %s an_cert %s' % (H(os.path.join(here, 'poslib.py')), H(os.path.join(here, 'cert_window.py')),
      H(os.path.abspath(__file__)), H(CW.COEFF_DIR + 'an_cert_X1e4.json')), flush=True)
t0 = time.time()
S = CW.Setup(NegCoeffs())
allneg = True
for tc, dd in [(0.0, 1e-6), (0.25, 0.25), (0.75, 0.25)]:
    Rmin, R0, info = CW.certify(S, tc, dd, 20, 1.0)
    neg = info['Rmax'] < 0
    allneg &= neg
    print('NEG-CONTROL (c = 1 terms only), cell [%g, %g]: R(tc) = %s ; certified upper bound of R on the cell = %s ; R < 0 certified: %s'
          % (tc - dd, tc + dd, R0.str(10), info['Rmax'].str(10), neg), flush=True)
print('DECISIVE (negative control): R < 0 certified on [-1e-6, 1e-6], [0, 0.5], [0.5, 1] for the c=1-only coefficients: %s   (%.0fs)' % (allneg, time.time() - t0))
