"""Positivity of g on [Y3, oo), Y3 = 4 (the tail lemma for g in the proof of Theorem L), in majorant form:
   g(Y) >= 2 pi a_1 sqrt(Y) K0(2 pi Y) (1 - rho(Y)) (since a_n > 0), and for Y >= Y3 = 4,
   rho(Y) := sum_{n>=2} n a_n K0(2 pi n Y)/(a_1 K0(2 pi Y)) <= rhobar(Y) := sum_{n>=2} sqrt(n) (A0(n)/a_1) e^{-2 pi (n-1) Y} / (1 - 1/(16 pi Y)),
   using sqrt(pi/(2x)) e^{-x}(1 - 1/(8x)) <= K0(x) <= sqrt(pi/(2x)) e^{-x}  (x > 0; DLMF 10.40(ii), remainder sign/size).
   rhobar is decreasing in Y; certify rhobar(4) < 1."""
import os, sys, json, hashlib
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import poslib as L
from flint import arb
L.setprec(160)
COEFF_DIR = os.environ.get('COEFF_DATA', os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'coefficients', 'data', ''))   # directory of the coefficient files (default coefficients/data/)
EXTRA = os.environ.get('COEFF_EXTRA')
C = L.Coeffs(COEFF_DIR + 'an_small_X1e4.json', COEFF_DIR + 'an_cert_X1e4.json', nmax=300, extra=json.load(open(EXTRA)) if EXTRA else None)
Y = arb(4); PI = L.PI
a1lo = arb(C.a[1].lower())
s = arb(0)
for n in range(2, 400):
    s += arb(n).sqrt() * L.Coeffs.A0(n) / a1lo * (-2 * PI * (n - 1) * Y).exp()
# tail n >= 400: terms decrease geometrically with ratio < e^{-2 pi Y + 2 pi/sqrt(n)} (1+1/n) < 1e-10
s += arb(0, (arb(400).sqrt() * L.Coeffs.A0(400) / a1lo * (-2 * PI * 399 * Y).exp() * 2).upper())
rb = s / (1 - 1 / (16 * PI * Y))
H = lambda f: hashlib.sha256(open(f, 'rb').read()).hexdigest()[:16]
print('cert_gtail: hashes poslib %s cert_gtail %s an_small %s an_cert %s extra %s' % (H(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'poslib.py')),
      H(os.path.abspath(__file__)), H(COEFF_DIR + 'an_small_X1e4.json'), H(COEFF_DIR + 'an_cert_X1e4.json'), H(EXTRA) if EXTRA else 'none'))
print('rhobar(4) = %s  (< 1 needed): %s' % (rb.str(10), rb < 1))
print('DECISIVE: g > 0 on [4, oo): %s' % (rb < 1))
