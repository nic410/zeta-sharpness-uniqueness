"""The elementary regime (Section 6.3 of the paper; not used in any proof): H_raw(t) > 0 for |t| < t1 from elementary
bounds of Ghat_raw, through one-dimensional integrals of elementary functions evaluated in Arb.

Inputs: Theorem 6.2 of the paper ((1 - 2/z_n) abar_n <= a_n <= abar_n for every n >= 1), the K0 bounds
sqrt(pi/2y) e^{-y} (1 - 1/(8y)) <= K0(y) <= sqrt(pi/2y) e^{-y} (DLMF 10.40(ii)), and comparison of sums with integrals.
With s = sqrt x, kappa = 4 pi (s - 1), abar_n sqrt(pi/(8 pi sqrt(n) s)) e^{-4 pi sqrt(n) s} = e^{-kappa sqrt n}/(16 pi^2 sqrt s):
  U(x) := sin^2(pi x) x^{1/4} e^{-kappa} (1 + 2(1+kappa)/kappa^2) / (16 pi^2)                 >= Ghat_raw(x)   (x > 1)
  L(x) := sin^2(pi x) x^{1/4} [2 e^{-kappa}(1+kappa)/kappa^2 - (2.125/(2 pi))/kappa] / (16 pi^2) <= Ghat_raw(x)   (x > 1)
(L: (1 - 2/z_n)(1 - 1/(8 z_n s)) >= 1 - 2.125/z_n; sum_{n>=1} e^{-k sqrt n} >= int_1^oo; sum_{n>=1} n^{-1/2} e^{-k sqrt n} <= int_0^oo = 2/k.)
Then, by the moment minorant of Section 6.3 of the paper, F(t) >= M0 - 2 pi^2 t^2 M2 (> 0 for |t| < (2 pi^2 M2/M0)^{-1/2}) and
F(t) >= M0 - 2 pi^2 t^2 M2 + (2 pi t)^4 M4/24 - (2 pi t)^6 M6/720, with
  M0 >= (1/pi) int_1^{x1} L dx/x,  M4 >= (1/pi) int_1^{x1} (log x/2pi)^4 L dx/x,  M_{2j} <= (1/pi) int_1^oo W_j U dx/x (j = 1, 3)
(on [1, x1] only the term m = 1 of W_j is kept, and W_0 = 1 there; Ghat_raw >= 0 elsewhere).
All integrals by Arb's rigorous acb.integral (analytic integrands; the removable singularity at x = 1 written with sinc),
the range x > X by an incomplete-Gamma bound.  Variant 'a1': the n = 1 term kept as a_1 sqrt(x) K0(4 pi sqrt x) sin^2(pi x)
with a_1 in its trivial-bound interval [c_1 - w_1, c_1 + w_1] (boxlib.py: the term c = 1 and the trivial bound), and the
terms n >= 2 bounded as above.
Usage: cert_elementary.py [x1] [X]    (shipped run: 1.3 30)"""
import sys, os, time, hashlib, json, math
from flint import arb, acb, ctx
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import boxlib as BX
ctx.prec = 96
PI = arb.pi()
X1S = sys.argv[1] if len(sys.argv) > 1 else '1.3'
X1 = arb(X1S)
XMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 30
DATA = os.path.join(HERE, '..', 'coefficients', 'data', 'an_cert_X1e4.json')
C1, W1 = BX.centre_halfwidth(1, json.load(open(DATA))['T1']['1'])          # a_1 in [C1 - W1, C1 + W1]
A1LO = arb((C1 - W1).lower()); A1HI = arb((C1 + W1).upper())


AN = [False]          # the 'analytic' flag of acb.integral, threaded into every branch-cut function


def parts(x):
    """common analytic pieces for complex ball x near the real axis, Re x > 0 (principal branches; with AN[0] = True the
    branch-cut functions return non-finite balls on inputs touching the cut, as acb.integral requires)."""
    s = x.sqrt(analytic=AN[0])
    kap = 4 * PI * (s - 1)
    sc = (PI * (x - 1)).sinc()                  # sin(pi(x-1))/(pi(x-1)), entire
    q = (s + 1) / 4 * sc                         # = -sin(pi x)/kappa (analytic, removable at x = 1)
    sn = (PI * x).sin()
    return s, kap, sn, q


def U_full(x):
    s, kap, sn, q = parts(x)
    # sin^2 e^{-k}(1 + 2(1+k)/k^2) = e^{-k}(sin^2 + 2(1+k) q^2)
    return s.sqrt(analytic=AN[0]) * (-kap).exp() * (sn ** 2 + 2 * (1 + kap) * q ** 2) / (16 * PI ** 2)


def L_full(x):
    s, kap, sn, q = parts(x)
    # sin^2 [2 e^{-k}(1+k)/k^2 - c/k] = 2 e^{-k}(1+k) q^2 + c sin * q    (sin^2/k = -sin q)
    c = arb('2.125') / (2 * PI)
    return s.sqrt(analytic=AN[0]) * (2 * (-kap).exp() * (1 + kap) * q ** 2 + c * sn * q) / (16 * PI ** 2)


def K0c(z):
    """K0 for a complex ball z, Re z > 0: Arb K0 at the exact midpoint (precision raised until tight) plus
    r * sup|K0'| = r * sup|K1| <= r K1(Re mid - r) (|K_nu(w)| <= K_nu(Re w), K1 decreasing)."""
    if not z.is_finite():
        return acb('nan')
    m = acb(z.real.mid(), z.imag.mid()); r = z.real.rad() + z.imag.rad()
    old = ctx.prec; best = None
    for extra in (32, 128, 400):
        ctx.prec = old + extra
        k = m.bessel_k(0)
        if k.is_finite() and (best is None or k.real.rad() + k.imag.rad() < best.real.rad() + best.imag.rad()):
            best = k
        if k.is_finite() and (k.real.rad() + k.imag.rad()) < abs(k).lower() * arb(2) ** (-old + 10):
            break
    ctx.prec = old
    if r == 0:
        return +best
    xmin = m.real - r
    if not (xmin > 0):
        return acb('nan')
    e = (r * arb(xmin.lower()).bessel_k(1)).upper()
    return best + acb(arb(0, e), arb(0, e))


def U_a1(x):
    """n = 1 term with a_1 <= A1HI (K0 complex via Arb), n >= 2 elementary: sum_{n>=2} e^{-k sqrt n} <= e^{-k sqrt2}(1 + 2(1+k sqrt2)/k^2)."""
    s, kap, sn, q = parts(x)
    r2 = arb(2).sqrt()
    rest = (-kap * r2).exp() * (sn ** 2 + 2 * (1 + kap * r2) * q ** 2) / (16 * PI ** 2) * s.sqrt(analytic=AN[0])
    return sn ** 2 * s * A1HI * K0c(4 * PI * s) + rest


def L_a1(x):
    s, kap, sn, q = parts(x)
    r2 = arb(2).sqrt()
    c = arb('2.125') / (2 * PI)
    # sum_{n>=2} (1 - 0.169/sqrt n) e^{-k sqrt n} >= int_2^oo e^{-k sqrt y} dy - 0.169 int_1^oo y^{-1/2} e^{-k sqrt y} dy
    rest = s.sqrt(analytic=AN[0]) * (2 * (-kap * r2).exp() * (1 + kap * r2) * q ** 2 + c * (-kap).exp() * sn * q) / (16 * PI ** 2)
    # n = 1: a_1 K0 >= A1LO * K0 (exact K0)
    return sn ** 2 * s * A1LO * K0c(4 * PI * s) + rest


def W(x, m, j):
    return ((x / m).log(analytic=AN[0]) / (2 * PI)) ** (2 * j)


def dcount(m):
    return sum(1 for d in range(1, m + 1) if m % d == 0)


def _wrap(f):
    def g(x, an):
        AN[0] = bool(an)
        if an and not (x.real > 0):
            return acb('nan')
        v = f(x)
        AN[0] = False
        return v
    return g


def integ(f, a, b):
    r = acb.integral(_wrap(f), acb(a), acb(b), rel_tol=arb(2) ** -40, abs_tol=arb(2) ** -90,
                     eval_limit=10 ** 6, deg_limit=60, depth_limit=2000)
    assert r.is_finite(), 'integral not finite'
    return r.real


def tail_bound(j, X):
    """(1/pi) int_X^oo W_j U dx/x <= (2/pi) c^{2j} fac int_X^oo x^{j+3/4} e^{-4 pi sqrt x} dx  (as in cert_moments.py)."""
    X = arb(X)
    kapX = 4 * PI * (X.sqrt() - 1)
    fac = (1 + 2 * (1 + kapX) / kapX ** 2) / (16 * PI ** 2) * (4 * PI).exp()
    cX = X.log() / (2 * PI * X.sqrt())
    qq = arb(j) + arb(0.75); b = 4 * PI
    return arb((2 / PI * cX ** (2 * j) * fac * 2 * b ** (-2 * qq - 2) * (b * X.sqrt()).gamma_upper(2 * qq + 2)).upper())


def run(name, Lf, Uf):
    t0 = time.time()
    M0 = integ(lambda x: Lf(x) / x, arb(1), X1) / PI
    M4 = integ(lambda x: W(x, 1, 2) * Lf(x) / x, arb(1), X1) / PI
    M2 = arb(0); M6 = arb(0)
    for m in range(1, XMAX):
        wm = arb(dcount(m)) / arb(m).sqrt()
        for k in range(m, XMAX):
            M2 += wm * integ(lambda x: W(x, m, 1) * Uf(x) / x, arb(k), arb(k + 1)) / PI
            M6 += wm * integ(lambda x: W(x, m, 3) * Uf(x) / x, arb(k), arb(k + 1)) / PI
    M2 += tail_bound(1, XMAX); M6 += tail_bound(3, XMAX)
    t1 = arb((1 / (2 * PI ** 2 * arb(M2.upper()) / arb(M0.lower())).sqrt()).lower())
    # 4-moment bound: cells [ta, tb] of width 1/64 (monotone parts), up to the first cell where it may fail
    tt = arb(0); reach = 0.0
    while True:
        ta = tt; tb = tt + arb(1) / 64
        Pp = arb(M0.lower()) + (2 * PI * ta) ** 4 / 24 * arb(M4.lower())
        Pm = (2 * PI * tb) ** 2 / 2 * arb(M2.upper()) + (2 * PI * tb) ** 6 / 720 * arb(M6.upper())
        if not (Pp - Pm > 0) or float(tb.mid()) > 12:
            break
        reach = float(tb.mid()); tt = tb
    print('[%s] M0 >= %s  M2 <= %s  M4 >= %s  M6 <= %s ; 2-moment: H_raw > 0 for |t| < %s ; 4-moment: |t| <= %.6f  (%.0fs)' % (
        name, arb(M0.lower()).str(6), arb(M2.upper()).str(6), arb(M4.lower()).str(6), arb(M6.upper()).str(6), t1.str(6), reach, time.time() - t0), flush=True)
    # the better of the two bounds: |t| < t1 (open) or |t| <= reach (closed)
    return ('|t| < %.4f' % (math.floor(float(t1.lower()) * 1e4) / 1e4)) if t1 > reach else ('|t| <= %.6f' % reach)


print('cert_elementary.py x1=%s X=%d prec=%d ; script %s boxlib %s an_cert_X1e4.json %s ; a_1 in [%s, %s]' % (
    X1S, XMAX, ctx.prec, hashlib.sha256(open(os.path.abspath(__file__), 'rb').read()).hexdigest()[:16],
    hashlib.sha256(open(os.path.join(HERE, 'boxlib.py'), 'rb').read()).hexdigest()[:16],
    hashlib.sha256(open(DATA, 'rb').read()).hexdigest()[:16], A1LO.str(10), A1HI.str(10)))
ra = run('Theorem 6.2 only', L_full, U_full)
rb = run('a_1 in its trivial-bound interval, n >= 2 by Theorem 6.2', L_a1, U_a1)
print('DECISIVE (elementary regime, not used in any proof): H_raw(t) > 0 for %s using only Theorem 6.2 ; for %s with a_1 in its trivial-bound interval'
      % (ra, rb))
