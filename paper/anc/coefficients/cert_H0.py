"""Certificate: H_raw(0), sign coherence, and the normalising constant C = 1/H_raw(0) (Proposition 6.4 of the paper;
Kc_n below is S_n of the paper, al_n = a_n(1) is A_n(1) and al'_n is A_n'(1)).

Object: G_raw(x) = sin^2(pi x) sqrt(x) ell(x),  ell(x) = sum_n a_n K0(4 pi sqrt(n x)) (x > 1; continued),  a_n = n Kc_n + delta_{n,1}/4.
H(t) := M[g](1/2+it) / gamma_oo(t)^2,  g = G/(2 pi sqrt x),  gamma_oo(0)^2 = pi^{-1/2} Gamma(1/4)^2 / 64.   C := 1/H_raw(0).

Decomposition (Appendix A of the paper):
  2 pi M[g](1/2) = Pint + int_0^oo d_rest(eta) sqrt(eta) Q(eta) d eta
  Pint  = int_0^oo sin^2(pi x) x^{-1/2} P(x) dx,      P(x) = 1/(32 pi^4 (x^2-1)) + 1/(8 pi^4 (x^2-1)^2)
  Q(eta) = int_0^oo sin^2(pi x) x^{-1/2} K0(2 pi eta x) dx = 2^{-5/2} (2 pi eta)^{-1/2} Gamma(1/4)^2 [1 - 2F1(1/4,1/4;1/2;-1/eta^2)]
           (Gradshteyn-Ryzhik 6.699.12)
  d_rest = d - d_grow:
     eta in (0, eta1]:  d(eta) = eta^{-5/2} sum_n 2 n a_n K0(2 pi n/eta)  (cusp 0),
                        d_grow = sqrt(eta) I0(2 pi eta)/(8 pi^2) + eta^{3/2} I1(2 pi eta)/(2 pi)
     eta >= eta1:       d_rest = -(1/(16 pi^2)) [ 4 pi eta^{3/2}(K1 - y K0)(2 pi eta)
                                  + sum_n 4 pi n eta^{3/2}( al'_n (K1 - y K0)(y) + al_n (K0/y - 2 K1)(y) ) ],  y = 2 pi n eta,
                        al_n = a_n(1) (Niebur), al'_n = 4 Kc_n         (expansion at the cusp oo; Appendix A of the paper)
All integrals: Arb acb.integral (rigorous Gauss-Legendre with error bounds from complex-ball bounds of the integrand),
plus explicit analytic bounds for [0, eps], [eta2, oo), x > XP and the n-tails.  Coefficients: Arb balls from
coefficients/out/an_small_X1e4.json (n <= 60) and, if present, coefficients/out/an_smalln_X3e5.json (n <= 6, tighter) and
coefficients/out/an_smalln_X6e5.json (n <= 2, tightest); these are written by cert_an.py and cert_small_n.py.
Usage: cert_H0.py [eta1] [eta2] [outtag]  (writes coefficients/out/H0_cert<outtag>.json)
"""
import sys, os, json, time, hashlib, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from flint import arb, acb, ctx
from coefflib import K01

PREC = 160
ctx.prec = PREC
HERE = os.path.dirname(os.path.abspath(__file__)); BASE = os.path.dirname(HERE)     # coefficients/ ; the top directory
OUT = os.path.join(HERE, 'out')                                                       # fresh outputs (inputs and output here)
ETA1 = arb(sys.argv[1]) if len(sys.argv) > 1 else arb(1)
ETA2 = arb(sys.argv[2]) if len(sys.argv) > 2 else arb(8)
EPS = arb('1e-8')
XP = 2000
NLOW = 60          # cusp-0 terms kept explicitly
NHIGH = 30         # cusp-oo modes kept explicitly
t0 = time.time()
pi = arb.pi()
G14 = arb(0.25).gamma()


def sha(path):
    return hashlib.sha256(open(path, 'rb').read()).hexdigest()[:16]


fn1 = os.path.join(OUT, 'an_small_X1e4.json')
fn2 = os.path.join(OUT, 'an_smalln_X3e5.json')
print('cert_H0.py eta1=%s eta2=%s eps=%s XP=%d prec=%d' % (ETA1, ETA2, EPS, XP, PREC))
print('input hashes: script %s ; %s %s' % (sha(os.path.abspath(__file__)), os.path.basename(fn1), sha(fn1)))
D1 = json.load(open(fn1))
B = {}; AL = {}; KC = {}
for k in D1['a_mid_rad']:
    n = int(k)
    m, r = D1['a_mid_rad'][k]; B[n] = arb(m, r)
    m, r = D1['alpha_mid_rad'][k]; AL[n] = arb(m, r)
    KC[n] = (B[n] - (arb(1) / 4 if n == 1 else 0)) / n
if os.path.exists(fn2):
    D2 = json.load(open(fn2))
    print('   tighter small-n balls from %s %s (X = %d)' % (os.path.basename(fn2), sha(fn2), D2['meta']['X']))
    for k in D2['a_mid_rad']:
        n = int(k)
        m, r = D2['a_mid_rad'][k]; Bn = arb(m, r)
        m, r = D2['alpha_mid_rad'][k]; An = arb(m, r)
        m, r = D2['K_mid_rad'][k]; Kn = arb(m, r)
        assert Bn.overlaps(B[n]) and An.overlaps(AL[n]) and Kn.overlaps(KC[n]), 'inconsistent coefficient balls at n=%d' % n
        B[n], AL[n], KC[n] = Bn, An, Kn
fn3 = os.path.join(OUT, 'an_smalln_X6e5.json')
if os.path.exists(fn3):
    D3 = json.load(open(fn3))
    print('   tighter n<=2 balls from %s %s (X = %d)' % (os.path.basename(fn3), sha(fn3), D3['meta']['X']))
    for k in D3['a_mid_rad']:
        n = int(k)
        Bn = arb(*D3['a_mid_rad'][k]); An = arb(*D3['alpha_mid_rad'][k]); Kn = arb(*D3['K_mid_rad'][k])
        assert Bn.overlaps(B[n]) and An.overlaps(AL[n]) and Kn.overlaps(KC[n]), 'inconsistent coefficient balls at n=%d' % n
        B[n], AL[n], KC[n] = Bn, An, Kn
print('   a_1 = %s ; alpha_1 = %s' % (B[1].str(20), AL[1].str(20)))


def A0(n):                                      # a_n <= A0(n) for all n (Theorem 6.2 of the paper)
    return arb(n) ** arb(0.25) * (4 * pi * arb(n).sqrt()).exp() / (4 * arb(2).sqrt() * pi ** 2)


def Ebound(n):                                  # E(z_n); |alpha_n| <= 2.33 E(z_n) (bound for the coefficients at nu = 1, proved in the paper)
    z = 4 * pi * arb(n).sqrt()
    return z.exp() / (2 * pi * z).sqrt()


def _Kc_point(m, nu):
    """K_nu at an EXACT (midpoint) complex argument m, Re m > 0; escalate precision until tight (Arb's K is rigorous
    but can be loose at moderate |m| because of series cancellation)."""
    az = float(abs(m).mid())
    old = ctx.prec
    best = None; bestr = None
    extras = (16, int(3 * az) + 64, int(6 * az) + 160) if az < 600 else (16, 64)
    for extra in extras:
        ctx.prec = PREC + extra
        k = m.bessel_k(nu)
        if k.is_finite():
            r = k.real.rad() + k.imag.rad()
            if best is None or r < bestr:
                best, bestr = k, r
            if r <= abs(k).lower() * arb(2) ** (-PREC + 20):
                break
    ctx.prec = old
    return best


def _Kc(z, nu):
    """Rigorous K_nu(z), nu in {0,1}, for a complex ball z with Re z > 0:
    K_nu(mid) at the exact midpoint, plus |K_nu(z) - K_nu(mid)| <= r * sup_ball |K_nu'|, where
    K_0' = -K_1, K_1' = -K_0 - K_1/w, and |K_nu(w)| <= K_nu(Re w) <= K_1(x_min) (K_nu(w) = int e^{-w cosh t} cosh(nu t) dt;
    K_0 <= K_1 and K_1 decreasing on (0,oo)); x_min = Re(mid) - r > 0.  K_1(x_min): Part I's tight real K01."""
    if not z.is_finite():
        return acb('nan')
    m = acb(z.real.mid(), z.imag.mid())
    r = z.real.rad() + z.imag.rad()
    k = _Kc_point(m, nu)
    if k is None:
        return acb('nan')
    if r == 0:
        return +k
    xmin = m.real - r
    if not (xmin > 0):
        return acb('nan')
    k0, k1 = K01(arb(xmin.lower()), PREC)
    K1max = k1.upper()
    der = K1max if nu == 0 else K1max * (1 + 1 / xmin.lower())
    e = (r * der).upper()
    return k + acb(arb(0, e), arb(0, e))


def K0c(z):
    return _Kc(z, 0)


def K1c(z):
    return _Kc(z, 1)


def Qc(eta, analytic):
    s = (2 * pi * eta).sqrt(analytic=analytic)
    F = (-1 / eta ** 2).hypgeom_2f1(0.25, 0.25, 0.5, ab=True)
    return arb(2) ** arb(-2.5) * G14 ** 2 * (1 - F) / s


NaN = acb('nan')


def cusp0_tail_bound(rho):
    """|sum_{n > NLOW} 2 n a_n K0(2 pi n w)| for Re w >= rho > 0: terms <= 2n A0(n) K0(2 pi n rho) <= 2n A0(n) sqrt(pi/(4 pi n rho)) e^{-2 pi n rho}
    (|K0(w)| <= K0(Re w), K0(x) <= sqrt(pi/(2x)) e^{-x}); geometric tail checked."""
    n = NLOW + 1
    t = 2 * n * A0(n) * (pi / (4 * pi * n * rho)).sqrt() * (-2 * pi * n * rho).exp()
    ratio = (A0(n + 1) / A0(n)) * arb(n + 1) / n * (-2 * pi * rho).exp()
    if not (ratio < 0.5):
        return None
    return 2 * t


def f_low(eta, analytic):
    if analytic and not (eta.real > 0):
        return NaN
    w = 1 / eta
    rho = w.real.lower() if w.real.is_finite() else arb(0)
    if analytic and not (rho > 0):
        return NaN
    if not (rho > 0):
        return NaN
    se = eta.sqrt(analytic=analytic)
    s = acb(0)
    for n in range(1, NLOW + 1):
        s += 2 * n * B[n] * K0c(2 * pi * n * w)
    tb = cusp0_tail_bound(rho)
    if tb is None:
        return NaN
    s += acb(arb(0, tb.upper()), arb(0, tb.upper()))
    d = s / (se ** 5)
    z1 = 2 * pi * eta
    dg = se * z1.bessel_i(0) / (8 * pi ** 2) + eta * se * z1.bessel_i(1) / (2 * pi)
    return (d - dg) * se * Qc(eta, analytic)


def head_tail_bound(rho, aeta):
    """Upper bound for sum_{n > NHIGH} 4 pi n [ |al'_n| (|K1(y)| + |y| |K0(y)|) + |al_n| (|K0(y)|/|y| + 2|K1(y)|) ],  y = 2 pi n eta,
    for Re eta >= rho > 0, |eta| <= aeta:  |K_nu(y)| <= K_nu(Re y) <= K_{3/2}(x), x = 2 pi n rho  (K_nu(w) = int e^{-w cosh t} cosh(nu t) dt;
    K_nu increasing in nu, decreasing in x);  |y| <= 2 pi n aeta ; 1/|y| <= 1/x ;
    |al'_n| = 4 Kc_n <= 4 A0(n)/n (Theorem 6.2 of the paper) ; |al_n| <= 2.33 E(z_n) (bound for the coefficients at nu = 1, proved in the paper).
    Terms decay geometrically once 2 pi rho > 2 pi/sqrt(n); summed until negligible, x2 safety."""
    tot = arb(0)
    for n in range(NHIGH + 1, NHIGH + 400):
        x = 2 * pi * n * rho
        K = (pi / (2 * x)).sqrt() * (-x).exp() * (1 + 1 / x)
        t = 4 * pi * n * K * ((4 * A0(n) / n) * (1 + 2 * pi * n * aeta) + arb('2.33') * Ebound(n) * (1 / x + 2))
        tot += t
        if n > NHIGH + 5 and t < tot * arb(2) ** (-PREC):
            return tot * 2
    return None


def f_high(eta, analytic):
    if analytic and not (eta.real > 0):
        return NaN
    if not (eta.real > 0):
        return NaN
    se = eta.sqrt(analytic=analytic)
    e32 = eta * se
    y1 = 2 * pi * eta
    k0, k1 = K0c(y1), K1c(y1)
    s = 4 * pi * e32 * (k1 - y1 * k0)
    for n in range(1, NHIGH + 1):
        y = 2 * pi * n * eta
        k0, k1 = K0c(y), K1c(y)
        s += 4 * pi * n * e32 * (4 * KC[n] * (k1 - y * k0) + AL[n] * (k0 / y - 2 * k1))
    rho = eta.real.lower()
    tb = head_tail_bound(rho, abs(eta).upper())
    if tb is None:
        return NaN
    tb = tb * abs(e32).upper()
    s += acb(arb(0, tb.upper()), arb(0, tb.upper()))
    drest = -s / (16 * pi ** 2)
    return drest * se * Qc(eta, analytic)


def f_P(u, analytic):
    """2 sin^2(pi u^2) P(u^2) written with sinc so that it is entire except at u = +-i (x = -1)."""
    x = u * u
    sc = (pi * (x - 1)).sinc()
    return 2 * pi ** 2 * sc ** 2 * ((x - 1) / (32 * pi ** 4 * (x + 1)) + 1 / (8 * pi ** 4 * (x + 1) ** 2))


def integ(f, a, b, tol):
    r = acb.integral(f, a, b, abs_tol=tol, rel_tol=arb(2) ** (-60), eval_limit=10 ** 7, deg_limit=200, depth_limit=4000)
    return r


# ---------------------------------------------------------------- Q formula sanity (numerical; the formula is Gradshteyn-Ryzhik 6.699.12)
print('Q(1) = %s' % Qc(acb(1), False).real.str(20), flush=True)

# ---------------------------------------------------------------- Pint
UP = arb(XP).sqrt()
I_P = integ(f_P, acb(0), acb(UP), arb('1e-30')).real
# tail x > XP: |sin^2 P x^{-1/2}| <= x^{-1/2}[1/(32pi^4(x^2-1)) + 1/(8pi^4(x^2-1)^2)] ; crude rigorous bound
X = arb(XP)
tailP = (1 + 2 / (X ** 2 - 1)) * (arb(2) / 3 * X ** arb(-1.5) / (32 * pi ** 4) + arb(2) / 7 * X ** arb(-3.5) / (8 * pi ** 4) * 4)
# centre: (1/2) int_XP^oo x^{-1/2} P(x) dx lies in [ (1/2)(2/3) X^{-3/2}/(32 pi^4), (1/2) tailP ]; the cos part is <= f(XP)/pi
lo = arb(1) / 2 * (arb(2) / 3) * X ** arb(-1.5) / (32 * pi ** 4)
hi = tailP / 2
cosb = X ** arb(-0.5) * (1 / (32 * pi ** 4 * (X ** 2 - 1)) + 1 / (8 * pi ** 4 * (X ** 2 - 1) ** 2)) / pi / 2
Ptail = (lo + hi) / 2 + arb(0, ((hi - lo) / 2 + cosb).upper())
Pint = I_P + Ptail
print('Pint = %s   (quadrature [0,%d]: %s ; tail %s)  (%.0fs)' % (Pint.str(20), XP, I_P.str(20), Ptail.str(5), time.time() - t0), flush=True)

# ---------------------------------------------------------------- J_low on [eps, eta1] + [0, eps] bound
Jl = integ(f_low, acb(EPS), acb(ETA1), arb('1e-26')).real
c0 = (1 + arb('1e-6')) / (8 * pi ** 2) * arb(2) ** arb(-1.5) * (2 * pi) ** arb(-0.5) * G14 ** 2
# [0, eps] END BOUND -- proof (the end bound on [0, 1e-8], proved in Appendix A of the paper). For 0 < eta <= eps = 1e-8:
#   |Q_s(eta)| <= Q(eta) <= int x^{-1/2} K0(2 pi eta x) dx = 2^{-3/2} Gamma(1/4)^2 (2 pi eta)^{-1/2}      (|x^{s-1}| = x^{-1/2}, sin^2 <= 1);
#   0 <= d_grow(eta) <= (1 + 1e-14) sqrt(eta)/(8 pi^2)       (I0(2 pi eta) <= 1 + 1e-15 ; eta^{3/2} I1(2 pi eta)/(2 pi) <= 0.51 eta^{5/2});
#   0 <= d(eta) <= eta^{-2} sum_n sqrt(n) A0(n) e^{-2 pi n/eta} <= eta^{-2} sum_n sqrt(n) e^{-pi n/eta} <= 2 eta^{-2} e^{-pi/eta}
#        <= 1e-6 sqrt(eta)/(8 pi^2)                           (K0(x) <= sqrt(pi/2x) e^{-x}; 0 < B_n = a_n <= A0(n) <= n^{1/4}e^{4 pi sqrt n} <= e^{pi n/eta});
#   hence |(d - d_grow) sqrt(eta) Q_s| <= 2 c0 sqrt(eta) and |int_0^eps| <= (4/3) c0 eps^{3/2}  (= eps_bound).
eps_bound = 2 * c0 * arb(2) / 3 * EPS ** arb(1.5)
Jlow = Jl + arb(0, eps_bound.upper())
print('J_low = %s  (quadrature %s ; [0,eps] bound %s)  (%.0fs)' % (Jlow.str(20), Jl.str(20), eps_bound.str(3), time.time() - t0), flush=True)

# ---------------------------------------------------------------- J_high on [eta1, eta2] + [eta2, oo) bound
Jh = integ(f_high, acb(ETA1), acb(ETA2), arb('1e-26')).real
# eta >= eta2: |d_rest| <= (1/(4 pi)) eta^{3/2} [ (1+y1) K32(y1) + sum_n n ( |al'_n|(1+y) + |al_n|(1/y + 2) ) K32(y) ],
# Q(eta) <= pi^2 sqrt2 Gamma(5/4)^2 (2 pi eta)^{-5/2};  integrand <= C eta^{3/2+1/2-5/2} * poly * e^{-2 pi eta}
def hb(eta):
    y1 = 2 * pi * eta
    K32 = lambda x: (pi / (2 * x)).sqrt() * (-x).exp() * (1 + 1 / x)
    s = (1 + y1) * K32(y1)
    for n in range(1, 400):
        y = 2 * pi * n * eta
        t = n * ((4 * A0(n) / n) * (1 + y) + arb('2.33') * Ebound(n) * (1 / y + 2)) * K32(y)
        s += t
        if n > 5 and t < s * arb(2) ** (-80):
            break
    return s / (4 * pi) * eta ** arb(1.5) * eta.sqrt() * pi ** 2 * arb(2).sqrt() * arb(1.25).gamma() ** 2 * (2 * pi * eta) ** arb(-2.5)
# [eta2, oo) END BOUND -- proof (the end bound on [8, oo), proved in Appendix A of the paper). hb(eta) majorises |d_rest(eta) sqrt(eta) Q_s(eta)|
#   term by term
#   (expansion of the density at the cusp oo, Appendix A of the paper; K0 <= K1 <= K_{3/2} = k; |al'_n| <= 4 A0(n)/n; |al_n| <= 2.33 E(z_n);
#   |Q_s| <= Q <= sqrt2 pi^2 Gamma(5/4)^2 (2 pi eta)^{-5/2}). Every summand is const * eta^{-1/2} g(y) y^{-1/2} e^{-y}, y = 2 pi n eta,
#   with g(y) = (1+y)(1+1/y) or (2+1/y)(1+1/y), so g(y)/y is non-increasing; hence summand(eta) <= summand(eta2) e^{-2 pi n (eta-eta2)}
#   and int_{eta2}^oo hb_full <= hb_full(eta2)/(2 pi). hb() stops the n-sum at a term < 2^-80 of the sum; later terms have ratio <= 1/2,
#   so hb_full <= (1 + 2^-79) hb. tail_hi below is >= 2 hb(eta2)/(2 pi), which covers both.
tail_hi = hb(ETA2) * (1 / (2 * pi)) * (1 + 2 / (2 * pi * ETA2) + 2 / (2 * pi * ETA2) ** 2) * 2
Jhigh = Jh + arb(0, tail_hi.upper())
print('J_high = %s  (quadrature %s ; [eta2,oo) bound %s)  (%.0fs)' % (Jhigh.str(20), Jh.str(20), tail_hi.str(3), time.time() - t0), flush=True)

# ---------------------------------------------------------------- assemble
twopiM = Pint + Jlow + Jhigh
M = twopiM / (2 * pi)
gam0 = pi ** arb(-0.5) * G14 ** 2 / 64
H0 = M / gam0
print('\n2 pi M[g](1/2) = %s' % twopiM.str(20))
print('DECISIVE: H_raw(0) = %s   (> 0: %s)  => SIGN COHERENCE (C > 0)' % (H0.str(15), H0 > 0))
Cn = 1 / H0
print('DECISIVE: C = 1/H_raw(0) = %s' % Cn.str(15))
print('DECISIVE: b_1 = C a_1 = %s' % (Cn * B[1]).str(15))
print('A = C/(32 pi^4) = %s ; G^(1) = pi^2 A = %s  (> 0)' % ((Cn / (32 * pi ** 4)).str(12), (Cn / (32 * pi ** 2)).str(12)))
print('total %.0fs' % (time.time() - t0))

def mr(x):
    return '%s +- %.3e' % (x.mid().str(20, radius=False), float(x.rad()))
print('\nmid +- rad:')
for nm, v in (('Pint', Pint), ('J_low', Jlow), ('J_high', Jhigh), ('2 pi M', twopiM), ('H_raw(0)', H0), ('C', Cn), ('b_1', Cn * B[1]),
              ('A', Cn / (32 * pi ** 4)), ('Ghat_S(1)', Cn / (32 * pi ** 2)), ('A/b_1', 1 / (32 * pi ** 4 * B[1]))):
    print('  %-10s = %s' % (nm, mr(v)))
out = {nm: [v.mid().str(30, radius=False), float(v.rad())] for nm, v in (('Pint', Pint), ('J_low', Jlow), ('J_high', Jhigh), ('twopiM', twopiM),
       ('H_raw0', H0), ('C', Cn), ('b1', Cn * B[1]), ('A', Cn / (32 * pi ** 4)), ('Ghat_S_1', Cn / (32 * pi ** 2)))}
out['meta'] = dict(script_sha=sha(os.path.abspath(__file__)), eta1=str(ETA1), eta2=str(ETA2), XP=XP, prec=PREC)
OUTTAG = sys.argv[3] if len(sys.argv) > 3 else ''
fo = os.path.join(OUT, 'H0_cert%s.json' % OUTTAG)
json.dump(out, open(fo, 'w'), indent=0)
os.system('"%s" "%s" "%s"' % (sys.executable, os.path.join(HERE, 'fix_json_radii.py'), fo))
print('wrote %s sha %s' % (os.path.relpath(fo, BASE), sha(fo)))
