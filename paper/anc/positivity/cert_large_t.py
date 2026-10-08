"""Certificate for the large-t theorem (Theorem L of the paper): R(t) > 0 for all t >= T0.
All decisive arithmetic in Arb with directed (exact-endpoint) rounding; g^- and the cell minima of g are exact Arb
endpoints; the A_Phi quadrature uses the m-node Gauss-Legendre bound and Arb majorants (functions from cert_window.py);
the axis bound is called A_Phi (A0(n) denotes the coefficient majorant a_n <= A0(n)).  The positivity of g on [Y3, oo)
is certified separately by cert_gtail.py.

R(t) = axis(t) + arcs(t),  |axis(t)| <= A_Phi := int_1^oo Phi,  arcs(t) = 1/2 int_{1/2}^oo g fhat_t.
With th_s = th(Ys), Yz slightly above the last sign change of g, and t >= T0 >= t_mono:
  e^{-t(pi/2-th_s)} arcs(t) >= p(t) - n(t),
  p(t) = 1/2 int_{Ys}^{Y3} g(Y) * (1/2) sqrt(sin th/sin(th+kap th/2)) e^{t(th_s-th)} erf(sqrt(t kap th)) rlow(t/2) dY   (nondecreasing)
  n(t) = 1/2 int_{1/2}^{Yz} g^-(Y) * (1/2) sqrt(sin th) rup(t/2) sqrt(2 pi t) [e^{-t(pi-th-th_s)} P0(cos th)
                                         + (1/2)(e^{-t(th-th_s)} + e^{-t(2pi-th-th_s)}) P0(-cos th)] dY             (nonincreasing for t >= t_mono)
  rlow(y) = exp(-9/(32y^2) - 1/(3y)) <= r(y) := |Gamma(3/4+iy)|^2 e^{pi y}/(2 pi sqrt y) <= rup(y) = exp(9/(64 y^2) + 1/(3y))
  (Stirling with |R_1(z)| <= sec^2(ph z/2)/(12|z|), DLMF 5.11(ii)).   P0 = P_{-1/2}.
Sufficient: p(T0) > n(T0) + A_Phi e^{-T0(pi/2-th_s)}, T0 >= t_mono = 1/(2(th(Yz)-th_s)), g > 0 on [Yz, Y3] (here) and on
[Y3, oo) (cert_gtail).  Integrals by Riemann sums of rigorous ball enclosures over cells (lower sum for p, upper for n).
Usage: cert_large_t.py T0 [kappa Ys Yz Y3 Np Nn]"""
import sys, os, time, hashlib, json
from flint import arb, ctx
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import poslib as L
from poslib import Coeffs, phi_g, Conical, conical_pm, PI, gl_nodes, ellipse_box
import cert_window as CW          # Arb box/majorant/GL-error functions

L.setprec(160)
COEFF_DIR = os.environ.get('COEFF_DATA', os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'coefficients', 'data', ''))   # directory of the coefficient files (default coefficients/data/)
args = sys.argv[1:]
T0 = float(args[0]); kap = float(args[1]) if len(args) > 1 else 0.5
Ys = float(args[2]) if len(args) > 2 else 1.0
Yz = float(args[3]) if len(args) > 3 else 0.870
Y3 = float(args[4]) if len(args) > 4 else 4.0
Np = int(args[5]) if len(args) > 5 else 1500
Nn = int(args[6]) if len(args) > 6 else 1200
t00 = time.time()
EXTRA = os.environ.get('COEFF_EXTRA')
C = Coeffs(COEFF_DIR + 'an_small_X1e4.json', COEFF_DIR + 'an_cert_X1e4.json', nmax=300, extra=json.load(open(EXTRA)) if EXTRA else None)
here = os.path.dirname(os.path.abspath(__file__))
H = lambda f: hashlib.sha256(open(f, 'rb').read()).hexdigest()[:16]
print('cert_large_t: T0=%g kappa=%g Ys=%g Yz=%g Y3=%g Np=%d Nn=%d; hashes poslib %s cert_window %s cert_large_t %s an_small %s an_cert %s extra %s' % (
    T0, kap, Ys, Yz, Y3, Np, Nn, H(os.path.join(here, 'poslib.py')), H(os.path.join(here, 'cert_window.py')), H(os.path.abspath(__file__)),
    H(COEFF_DIR + 'an_small_X1e4.json'), H(COEFF_DIR + 'an_cert_X1e4.json'), H(EXTRA) if EXTRA else 'none'), flush=True)
L.setprec(160)


def th(Y): return 2 * (1 / (2 * arb(Y))).atan()


def amin(vals):
    m = vals[0]
    for v in vals[1:]:
        m = arb(m.union(v).lower())
    return m


ths = th(Ys); thz = th(Yz)
cmin = thz - ths
t_mono = 1 / (2 * cmin)
print('th_s = %s, th(Yz) = %s, t_mono = %s' % (ths.str(10), thz.str(10), t_mono.str(8)))
T = arb(T0); y = T / 2
rlow = (-arb(9) / (32 * y * y) - 1 / (3 * y)).exp()
rup = (arb(9) / (64 * y * y) + 1 / (3 * y)).exp()


def partition(a, b, N, geom=False):
    if geom:
        r = (b / a) ** (1.0 / N)
        pts = [a * r ** i for i in range(N + 1)]
    else:
        pts = [a + (b - a) * i / N for i in range(N + 1)]
    pts[0] = a; pts[-1] = b
    return pts                    # float cell ends: exact binary numbers; cells tile [a, b] exactly


# --- (1) g > 0 on [Yz, Y3] (ball evaluation on cells) and p(T0) (lower Riemann sum on [Ys, Y3])
pts_z = partition(Yz, Ys, 300)
gz = [arb(phi_g(C, arb(lo).union(arb(hi)))[1].lower()) for lo, hi in zip(pts_z[:-1], pts_z[1:])]
gmin_z = amin(gz)
print('(1a) min lower bound of g on [Yz, Ys] = %s  (> 0 needed)' % gmin_z.str(6), flush=True)
pts_p = partition(Ys, Y3, Np, geom=True)
p = arb(0); gp = []
for lo, hi in zip(pts_p[:-1], pts_p[1:]):
    Yb = arb(lo).union(arb(hi))
    Ph, g = phi_g(C, Yb)
    gp.append(arb(g.lower()))
    t_ = th(Yb); dl = kap * t_
    f = arb(1) / 2 * ((t_.sin()) / ((t_ + dl / 2).sin())).sqrt() * (T * (ths - t_)).exp() * (T * dl).sqrt().erf() * rlow
    integrand = g / 2 * f
    p = arb((p + (arb(hi) - arb(lo)) * arb(integrand.lower())).lower())      # lower Riemann sum, rounded down
gmin_p = amin(gp)
print('(1b) min lower bound of g on [Ys, Y3] = %s ; p(T0) >= %s  (%.0fs)' % (gmin_p.str(6), p.str(12), time.time() - t00), flush=True)

# --- (2) n(T0): upper Riemann sum over [1/2, Yz] of g^- u_T, g^- <= -(lower end of g) (exact Arb)
cn0 = Conical(arb(0), K=400)
pts_n = partition(0.5, Yz, Nn)
nsum = arb(0); negcells = 0
for lo, hi in zip(pts_n[:-1], pts_n[1:]):
    Yb = arb(lo).union(arb(hi))
    Ph, g = phi_g(C, Yb)
    gl = arb(g.lower())
    if gl >= 0:
        continue                                      # g >= 0 on the cell: g^- = 0
    gneg = -gl                                        # exact arb >= g^- on the cell
    negcells += 1
    t_ = th(Yb)
    Pp, Pm = conical_pm(cn0, Yb)                       # P0(cos th), P0(-cos th)
    u = arb(1) / 2 * t_.sin().sqrt() * rup * (2 * PI * T).sqrt() * ((-T * (PI - t_ - ths)).exp() * Pp
         + ((-T * (t_ - ths)).exp() + (-T * (2 * PI - t_ - ths)).exp()) / 2 * Pm)
    nsum = arb((nsum + (arb(hi) - arb(lo)) * arb((gneg / 2 * u).upper())).upper())   # upper Riemann sum, rounded up
print('(2) n(T0) <= %s  (%d cells with possible g < 0)  (%.0fs)' % (nsum.str(12), negcells, time.time() - t00), flush=True)

# --- (3) A_Phi = int_1^oo Phi: Gauss-Legendre (30 nodes) + m-node ellipse error bound (Arb) + Y tail (upper bound)
panels = [1.0, 1.1, 1.2, 1.35, 1.5, 1.7, 1.9, 2.2, 2.5, 2.9, 3.3, 3.8, 4.4, 5.0, 5.8, 6.6, 7.6, 8.6, 10.0, 11.5, 13.0]
AP = arb(0); err = arb(0)
for a, b in zip(panels[:-1], panels[1:]):
    rho = 2.0
    xlo_f, xhi_f, yhi_f = ellipse_box(a, b, rho)          # parameter choice only
    while xlo_f < 0.86 * a:
        rho -= 0.05; xlo_f, xhi_f, yhi_f = ellipse_box(a, b, rho)
    xlo, xhi, yhi = CW.ellipse_box_arb(a, b, rho)
    assert xlo > 0
    M = CW.phi_g_majorant_arb(C, xlo, xhi, yhi)
    A_, B_ = arb(a), arb(b); h = (B_ - A_) / 2; c = (A_ + B_) / 2
    s = arb(0)
    for (x, w) in gl_nodes(30):
        s += w * phi_g(C, c + h * x)[0]
    AP += s * h
    err = arb((err + CW.gl_err(a, b, rho, M, 30)).upper())
m1 = CW.phi_g_majorant_arb(C, arb(13), arb(14), arb(0))
qy = (arb(14) / 13).sqrt() * (-2 * PI).exp()
assert qy < 1
ytail = arb((m1 / (1 - qy)).upper())
APup = arb((AP + arb(0, (err + ytail).upper())).upper())
print('(3) A_Phi = int_1^oo Phi in %s  (quad err <= %s, Y-tail <= %s): A_Phi <= %s' % (AP.str(12), err.str(3), ytail.str(3), APup.str(12)), flush=True)

axterm = arb((APup * (-T * (PI / 2 - ths)).exp()).upper())
margin = arb(p.lower()) - arb(nsum.upper()) - axterm          # exact operations on exact endpoints (tiny radius)
ok = (gmin_z > 0) and (gmin_p > 0) and (arb(T0) >= t_mono) and (margin > 0)
print('p(T0) >= %s ; n(T0) <= %s ; A_Phi e^{-T0(pi/2-th_s)} <= %s ; margin = %s ; ratio p/(n + axis term) >= %s' % (
    arb(p.lower()).str(12), arb(nsum.upper()).str(12), axterm.str(12), margin.str(12),
    arb((arb(p.lower()) / arb((arb(nsum.upper()) + axterm).upper())).lower()).str(6)))
print('DECISIVE (all-Arb): Theorem L hypotheses verified for T0 = %g: %s   (%.0fs)' % (T0, ok, time.time() - t00))
