"""Certificate W: R(t) = axis(t) + arcs(t) > 0 on a t-interval, by Taylor models with rigorous remainders.
Every error term is an Arb upper end; Gauss-Legendre error bound for m-node rules; outward ellipse boxes and Arb
analyticity tests; k-tail bracket constant proved in the paper (see below); Cauchy disc kept in |Im z| < 3/2; the lower
bound for P_t(0) is evaluated at the exact endpoint of the t-ball (a wide union ball would lose precision).

Notation and formula: see the poslib.py docstring and the paper.  H_raw(t) = R(t)/(2 pi^2 (t^2+1/4)^2).

For a centre tc and half-width d, with Cauchy radius rt in (d, 3/2) and Taylor length K:
  Q(t) := Gauss-Legendre sum (arcs nodes + axis nodes) with the EXACT conical kernel: an entire function of t.
  Q_trunc(t): the same sum with the k-truncated conical representation used for the Taylor coefficients; it contains
          1/P_t(0) = Gamma(3/4+it/2)Gamma(3/4-it/2)/sqrt(pi), with poles at t = +-i(3/2+2m) that the truncated numerator
          does not cancel, so Q_trunc is analytic only on |Im t| < 3/2 (the psi-poles at +-i/2 are removable: cosh(pi t) = 0
          there).  Hence the Cauchy disc |z - tc| <= rt must satisfy rt < 3/2 (asserted).
  R(t) = Q_trunc(t) + Q_ktail(t) + E_quad(t) + E_Ytail(t)   (real t),
  |E_quad| <= sum_panels ((b-a)/2)(64/15) M rho^{-2m}/(1 - rho^{-2})   for an m-node rule (Trefethen ATAP Thm 19.3
          is stated for the (n+1)-point rule; the m-node form is proved in the paper), M >= sup over the Bernstein
          ellipse of |integrand| for t in the cell.
  Q_trunc(t) = sum_{j<K} q_j (t-tc)^j + rem,  |rem| <= MQ (d/rt)^K / (1 - d/rt),  MQ >= sup_{|z-tc|=rt} |Q_trunc(z)|.
  MQ: |cos(z log Y)| <= cosh(rt |log Y|);  |P_{-1/2+iz}(cos a)| <= P_{-1/2+iT}(cos a), T = |tc| + rt (Mehler-Dirichlet,
      DLMF 14.12.1, |cosh(z phi)| <= cosh(Re z phi), monotone in T); 1/|P_z(0)| bounded on the circle by 96 covering boxes
      (and on the disc by the maximum principle); plus the k-tail.
  k-tail bracket: for k >= kmax+1 >= 301 + 7T and |z| <= T, Re(k+1/2 -+ iz) >= k+1/2-T >= 1 and |psi'(w)| <= psi'(Re w)
      <= 2/Re w, so |br_k(z)| = |2psi(k+1) - psi(k+1/2+iz) - psi(k+1/2-iz)| <= 4(1/2+T)/(kmax+3/2-T) <= 4/7 < 0.6.
  Y-tail (Y >= 13): fhat_t bounded directly from the series -- no elliptic-integral inequality needed.
Usage: cert_window.py tc d [K rt]  -> prints DECISIVE line.  Library: poslib.py."""
import sys, time, math, json, hashlib, os
from flint import arb, acb, ctx, arb_series, acb_series, arb_poly
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import poslib as L
from poslib import Coeffs, phi_g, Conical, gl_nodes, ellipse_box, PI

PREC = 192
L.setprec(PREC)
COEFF_DIR = os.environ.get('COEFF_DATA', os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'coefficients', 'data', ''))   # directory of the coefficient files (default coefficients/data/; with a trailing separator)
EXTRA = os.environ.get('COEFF_EXTRA')   # optional sharper small-n balls (json {n: [mid, rad]})

ARC_PANELS = [0.5, 0.55, 0.6, 0.65, 0.7, 0.75, 0.8, 0.85, 0.9, 0.95, 1.0, 1.1, 1.2, 1.35, 1.5, 1.7, 1.9, 2.2, 2.5, 2.9, 3.3,
              3.8, 4.4, 5.0, 5.8, 6.6, 7.6, 8.6, 10.0, 11.5, 13.0]
AX_PANELS = [1.0, 1.1, 1.2, 1.35, 1.5, 1.7, 1.9, 2.2, 2.5, 2.9, 3.3, 3.8, 4.4, 5.0, 5.8, 6.6, 7.6, 8.6, 10.0, 11.5, 13.0]
NGL = int(os.environ.get('NGL', '30'))
YMAX = arb(13)


def sha(path):
    return hashlib.sha256(open(path, 'rb').read()).hexdigest()[:16]


def up(x):
    """exact arb equal to the upper end of the ball x"""
    return arb(x.upper())


def rho_for(a, b):
    """ellipse parameter (a parameter CHOICE only, float is harmless): keep Re Y >= 0.86 a and 4(xlo^2 - yhi^2)+1 > 1.35.
       The boxes actually used are recomputed in Arb with outward ends (ellipse_box_arb) and re-tested in Arb."""
    best = None
    for r in [1.5 + 0.05 * i for i in range(200)]:
        xlo, xhi, yhi = ellipse_box(a, b, r)
        if xlo >= 0.86 * a and 4 * (xlo ** 2 - yhi ** 2) + 1 > 1.35:
            best = r
    return best


def ellipse_box_arb(a, b, rho):
    """outward Arb box [xlo, xhi] x [-yhi, yhi] containing the Bernstein ellipse E_rho of [a, b]."""
    a = arb(a); b = arb(b); rho = arb(rho)
    c = (a + b) / 2; h = (b - a) / 2
    ax = h * (rho + 1 / rho) / 2; ay = h * (rho - 1 / rho) / 2
    return arb((c - ax).lower()), arb((c + ax).upper()), arb(ay.upper())


def phi_g_majorant_arb(C, x_lo, x_hi, y_hi):
    """Arb upper bound of max(|Phi(Y)|, |g(Y)|) on the box Re Y in [x_lo, x_hi], |Im Y| <= y_hi (x_lo > 0):
       |a_n| <= upper end of the ball (n <= nmax), |sqrt Y| <= |Y|^{1/2}, |K0(z)| <= K0(Re z) <= K0(2 pi n x_lo);
       tail n > N via a_n <= A0(n) (the coefficient bound proved in the paper; |a_n| <= A0(n) also needs a_n >= 0,
       proved there as well)."""
    absY = up((x_hi ** 2 + y_hi ** 2).sqrt())
    sabs = up(absY.sqrt())
    s = arb(0); N = C.nmax
    for n in range(1, C.nmax + 1):
        tm = up(2 * PI * n * up(abs(C.a[n])) * sabs * up(L.K0(2 * PI * n * x_lo)))
        s = up(s + tm)
        if n > 12 and tm < s * arb(2) ** -200:
            N = n
            break
    s = up(s + up(L._tail_terms(C, x_lo, absY, N + 1)))
    return s


def P0_lower(cn):
    """lower bound of P_t(0) = sqrt(pi)/|Gamma(3/4+it/2)|^2 over the real t-ball of cn (P_t(0) increasing in |t|),
       evaluated at the exact endpoint |t|_lo (a wide union ball would lose precision through its 30-bit radius)."""
    tlo = arb(abs(cn.t).lower())
    if tlo < 0:
        tlo = arb(0)
    G = acb(arb(3) / 4, tlo / 2).gamma()
    v = arb.const_sqrt_pi() / (G.real ** 2 + G.imag ** 2)
    lo = arb(v.lower())
    assert lo > 0
    return lo


def fhat_majorant_arb(cn, x_lo, x_hi, y_hi):
    """Arb upper bound of |fhat_t(Y)| on the box, for every t in the real ball of the Conical object cn."""
    den_lo = 4 * (x_lo ** 2 - y_hi ** 2) + 1
    den_hi = 4 * (x_hi ** 2 + y_hi ** 2) + 1
    assert den_lo > arb('1.3'), 'box: |z1| too large'
    za = up(1 / den_lo)
    Lz = up(den_hi.log() + PI / 2)          # |log z1| <= log|4Y^2+1| + |arg| <= log den_hi + pi/2 (den_lo > 1)
    S1 = arb(0); S2 = arb(0); zk = arb(1)
    for k in range(cn.K + 1):
        ck = up(cn.c[k]); bk = up(abs(cn.br[k]))
        S1 = up(S1 + ck * zk)
        S2 = up(S2 + ck * zk * (bk + Lz))
        zk = up(zk * za)
        if k > 8 and ck * zk < S1 * arb(2) ** -200:
            break
    s_hi = up(cn.s)
    q = up((1 + s_hi / arb(k + 1) ** 2) * za)
    assert q < arb('0.9')
    tf = up(up(cn.c[k + 1]) * zk / (1 - q))
    kh = arb(k) + arb('1.5')
    bm = up(2 / kh + s_hi * (2 / kh ** 3 + 1 / kh ** 2))     # >= max(2/kh, s(2/kh^3 + 1/kh^2)) >= |br_j|, j > k
    S1 = up(S1 + tf); S2 = up(S2 + tf * (bm + Lz))
    absY = up((x_hi ** 2 + y_hi ** 2).sqrt())
    pref = up(2 * (absY * za).sqrt())
    return up(pref * (S1 + up(cn.coshpi) / PI * S2) / (2 * P0_lower(cn)))


def gl_err(a, b, rho, M, m):
    """Gauss-Legendre error bound for an m-node rule: ((b-a)/2)(64/15) M rho^{-2m}/(1 - rho^{-2})."""
    rho = arb(rho)
    return up((arb(b) - arb(a)) / 2 * arb(64) / 15 * M * rho ** (-2 * m) / (1 - rho ** -2))


class Setup:
    def __init__(self, coeffs=None, ngl=None):
        self.ngl = ngl or NGL
        if coeffs is None:
            extra = json.load(open(EXTRA)) if EXTRA else None
            coeffs = Coeffs(COEFF_DIR + 'an_small_X1e4.json', COEFF_DIR + 'an_cert_X1e4.json', nmax=300, extra=extra)
        self.C = C = coeffs
        self.arc = []
        for a, b in zip(ARC_PANELS[:-1], ARC_PANELS[1:]):
            rho = rho_for(a, b)
            xlo, xhi, yhi = ellipse_box_arb(a, b, rho)
            # analyticity on the box (Arb): Re Y >= xlo > 0 (sqrt Y, log Y, K0(2 pi n Y)); Re(4Y^2+1) >= 4(xlo^2-yhi^2)+1 > 1.3
            # (|z1| < 1/1.3: the conical series converge; log z1 analytic); |arg Y| + |arg(4Y^2+1)| < pi/2 (sqrt(Y z1))
            den = 4 * (xlo ** 2 - yhi ** 2) + 1
            argsum = (yhi / xlo).atan() + (8 * xhi * yhi / den).atan()
            assert xlo > 0 and den > arb('1.3') and argsum < PI / 2, 'panel box not admissible'
            gmaj = phi_g_majorant_arb(C, xlo, xhi, yhi)
            A_, B_ = arb(a), arb(b); h = (B_ - A_) / 2; c = (A_ + B_) / 2
            nodes = []
            for (x, w) in gl_nodes(self.ngl):
                Y = c + h * x
                Ph, g = phi_g(C, Y)
                z1 = 1 / (4 * Y * Y + 1)
                nodes.append((w * h / 2, g, z1, z1.log(), 2 * (Y * z1).sqrt(), Ph))
            self.arc.append(dict(a=a, b=b, rho=arb(rho), box=(xlo, xhi, yhi), gmaj=gmaj, nodes=nodes))
        self.ax = []
        for a, b in zip(AX_PANELS[:-1], AX_PANELS[1:]):
            rho = rho_for(a, b)
            xlo, xhi, yhi = ellipse_box_arb(a, b, rho)
            assert xlo > 0
            pmaj = phi_g_majorant_arb(C, xlo, xhi, yhi)
            A_, B_ = arb(a), arb(b); h = (B_ - A_) / 2; c = (A_ + B_) / 2
            nodes = []
            for (x, w) in gl_nodes(self.ngl):
                Y = c + h * x
                Ph, g = phi_g(C, Y)
                nodes.append((w * h, Ph, Y.log()))
            self.ax.append(dict(a=a, b=b, rho=arb(rho), box=(xlo, xhi, yhi), pmaj=pmaj, nodes=nodes))
        # Y-tail: int_13^oo Phi <= sup_[13,14] Phi / (1 - sqrt(14/13) e^{-2 pi})   (Phi(Y+1) <= sqrt((Y+1)/Y) e^{-2pi} Phi(Y),
        # from (log K0)' = -K1/K0 <= -1 and a_n > 0)
        m1 = phi_g_majorant_arb(C, arb(13), arb(14), arb(0))
        q = (arb(14) / 13).sqrt() * (-2 * PI).exp()
        assert q < 1
        self.ytail_int = up(m1 / (1 - q))


def series_data(tc, K, kmax):
    """Y-independent power series (in d = t - tc, length K): c_k, e_k = c_k*br_k (k <= kmax) as coefficient tables,
       cosh(pi t), 1/P_t(0); returned as lists of arb (per m) and arb_polys in z for c and e."""
    ctx.cap = K
    tcA = arb(tc)
    tser = arb_series([tcA, 1], prec=K)
    s = tser * tser
    c = arb_series([1], prec=K)
    C = []; E = []
    # psi(1/2 + i(tc+d)) series: lgamma(1/2 + i tc + i d) = L(d); psi = -i L'(d)
    Lg = acb_series([acb(arb(1) / 2, tcA), acb(0, 1)], prec=K + 1).lgamma()
    psi = Lg.derivative() * acb(0, -1)
    g = arb.const_euler()
    H = arb(0)
    for k in range(kmax + 2):
        rpsi = arb_series([z.real for z in psi.coeffs()] + [arb(0)] * (K - len(psi.coeffs())), prec=K)
        br = arb_series([2 * (H - g)], prec=K) - 2 * rpsi
        C.append(c); E.append(c * br)
        # update
        c = c * (arb_series([(arb(1) / 2 + k) ** 2], prec=K) + s) * (arb(1) / arb(k + 1) ** 2)
        H += arb(1) / (k + 1)
        inc = acb_series([acb(arb(1) / 2 + k, tcA), acb(0, 1)], prec=K)   # 1/2 + k + i(tc + d)
        psi = psi + 1 / inc
    coshpi = ((PI * tser).exp() + (-PI * tser).exp()) / 2
    lg1 = acb_series([acb(arb(3) / 4, tcA / 2), acb(0, arb(1) / 2)], prec=K).lgamma()
    lg2 = acb_series([acb(arb(3) / 4, -tcA / 2), acb(0, -arb(1) / 2)], prec=K).lgamma()
    ip = (lg1 + lg2).exp()
    invP0 = arb_series([z.real for z in ip.coeffs()], prec=K) / arb.const_sqrt_pi()
    # coefficient polys in z1 for each order m
    cpol = [arb_poly([C[k].coeffs()[m] if m < len(C[k].coeffs()) else arb(0) for k in range(kmax + 1)]) for m in range(K)]
    epol = [arb_poly([E[k].coeffs()[m] if m < len(E[k].coeffs()) else arb(0) for k in range(kmax + 1)]) for m in range(K)]
    return dict(C=C, E=E, coshpi=coshpi, invP0=invP0, cpol=cpol, epol=epol, kmax=kmax)


def ktail_bound_arb(T, kmax):
    """sup over |z| <= T (complex) and real nodes Y >= 1/2 (z1 <= 1/2) of the k-tails beyond kmax; returns (plain,
       bracket-weighted).  c_k(z^2) <= c_k(T^2); ratio <= (1 + T^2/(k+1)^2) z1; bracket constant proved in the paper
       (|br_k| <= 4(1/2+T)/(kmax+3/2-T); see the module docstring)."""
    cn = Conical(arb(T), K=kmax + 5)
    zmax = arb(1) / 2
    ck = up(up(cn.c[kmax + 1]) * zmax ** (kmax + 1))
    q = up((1 + up(cn.s) / arb(kmax + 2) ** 2) * zmax)
    assert q < arb('0.95')
    plain = up(ck / (1 - q))
    den = arb(kmax) + arb('1.5') - T
    assert den >= 1
    brk = up(4 * (arb('0.5') + T) / den)
    assert brk < arb('0.6')
    lz = up((4 * YMAX ** 2 + 1).log())               # |log z1| at real nodes Y in [1/2, 13]
    return plain, up(plain * (brk + lz))


def fhat_ytail_bound(cn):
    """Arb upper bound of sup_{Y >= 13, t in the real ball of cn} fhat_t(Y) (direct series bound):
       fhat <= 2 sqrt(Y z1)[S1 + (cosh(pi t)/pi)(Sb + |log z1| S1)]/(2 P_t(0)), sqrt(Y z1) <= 1/(2 sqrt 13),
       sqrt(Y z1)|log z1| <= log(4*13^2+1)/(2 sqrt 13) (decreasing for Y >= 13), S1 = sum c_k z1^k, Sb = sum c_k |br_k| z1^k
       increasing in z1, evaluated at z1 = 1/677."""
    z = arb(1) / (4 * YMAX ** 2 + 1)
    S1 = arb(0); Sb = arb(0); zk = arb(1)
    for k in range(50):
        S1 = up(S1 + up(cn.c[k]) * zk)
        Sb = up(Sb + up(cn.c[k]) * up(abs(cn.br[k])) * zk)
        zk = up(zk * z)
    s_hi = up(cn.s)
    q = up((1 + s_hi / arb(51) ** 2) * z)
    assert q < arb('0.5')
    tf = up(up(cn.c[50]) * zk / (1 - q))
    S1 = up(S1 + tf); Sb = up(Sb + tf * (1 + s_hi))          # |br_k| <= max(2/(k+1/2), s(...)) <= 1 + s for k >= 50
    a = up(1 / (2 * YMAX.sqrt()))
    bL = up((4 * YMAX ** 2 + 1).log() / (2 * YMAX.sqrt()))
    num = up(2 * (a * S1 + up(cn.coshpi) / PI * (a * Sb + bL * S1)))
    return up(num / (2 * P0_lower(cn)))


def certify(S, tc, d, K=20, rt=1.0, kmax=None, verbose=False, nsub=8):
    """Returns (Rmin, q0, info): Rmin = exact arb lower bound of R on [tc-d, tc+d]; info['Rmax'] = upper bound."""
    t0 = time.time()
    tcA = arb(tc); dA = arb(d); rtA = arb(rt)
    assert 0 < d < rt < 1.5, 'need d < rt and the Cauchy disc inside |Im z| < 3/2'
    kmax = kmax or int(300 + 8 * (abs(tc) + rt))
    D = series_data(tc, K, kmax)
    ctx.cap = K
    arcs = arb_series([0], prec=K)
    for P in S.arc:
        for (W, g, z1, lz, pref, Ph) in P['nodes']:
            s1 = arb_series([D['cpol'][m](z1) for m in range(K)], prec=K)
            se = arb_series([D['epol'][m](z1) for m in range(K)], prec=K)
            s2 = se - lz * s1
            f = pref * (s1 + D['coshpi'] * s2 / PI) * D['invP0'] / 2
            arcs = arcs + (W * g) * f
    tser = arb_series([tcA, 1], prec=K)
    axis = arb_series([0], prec=K)
    for P in S.ax:
        for (W, Ph, lY) in P['nodes']:
            axis = axis + (W * Ph) * (tser * lY).cos()
    q = (arcs + axis).coeffs()
    T = abs(tcA) + rtA
    plain, brt = ktail_bound_arb(T, kmax)
    # |1/P_z(0)| on the circle |z - tc| = rt: 96 boxes of half-width 0.066 rt (half-chord between centres 0.0327 rt)
    ipmax = arb(0)
    for j in range(96):
        ang = 2 * PI * j / 96
        cx = tcA + rtA * ang.cos(); cy = rtA * ang.sin()
        zc = acb(arb(cx.mid(), (cx.rad() + rtA * arb('0.066')).upper()), arb(cy.mid(), (cy.rad() + rtA * arb('0.066')).upper()))
        v = (acb(arb(3) / 4) + acb(0, 1) * zc / 2).gamma() * (acb(arb(3) / 4) - acb(0, 1) * zc / 2).gamma()
        ipmax = up(ipmax.union(up(abs(v) / arb.const_sqrt_pi())))
    coshT = up(((PI * T).exp() + (-PI * T).exp()) / 2)
    sumWgpref = arb(0)
    for P in S.arc:
        for (W, g, z1, lz, pref, Ph) in P['nodes']:
            sumWgpref = up(sumWgpref + up(abs(W * g * pref)))
    ktail = up(sumWgpref * (plain + coshT / PI * brt) * ipmax / 2)
    cnT = Conical(arb(T), K=kmax + 200)
    MQa = arb(0)
    twoP0T = up(2 * cnT.P0)
    for P in S.arc:
        for (W, g, z1, lz, pref, Ph) in P['nodes']:
            Y = ((1 / z1 - 1) / 4).sqrt()
            fT = cnT.fhat(Y)
            MQa = up(MQa + up(abs(W * g)) * up(fT) * twoP0T / 2 * ipmax)
    MQx = arb(0)
    for P in S.ax:
        for (W, Ph, lY) in P['nodes']:
            MQx = up(MQx + up(abs(W * Ph)) * up((rtA * up(abs(lY))).cosh()))
    MQ = up(MQa + MQx + ktail)
    rat = dA / rtA
    cauchy = up(MQ * rat ** K / (1 - rat))
    cnI = Conical(arb(tc, d), K=kmax + 200)
    Eq = arb(0)
    for P in S.arc:
        xlo, xhi, yhi = P['box']
        M = up(arb('0.5') * P['gmaj'] * fhat_majorant_arb(cnI, xlo, xhi, yhi))
        Eq = up(Eq + gl_err(P['a'], P['b'], P['rho'], M, S.ngl))
    tabs = abs(tcA) + dA
    for P in S.ax:
        xlo, xhi, yhi = P['box']
        M = up(P['pmaj'] * up((tabs * up((yhi / xlo).atan())).cosh()))
        Eq = up(Eq + gl_err(P['a'], P['b'], P['rho'], M, S.ngl))
    fy = fhat_ytail_bound(cnI)
    Ey = up(S.ytail_int * (arb('0.5') * fy + 1))
    rem = up(cauchy + Eq + Ey + ktail)
    lows = []; highs = []
    for i in range(nsub):
        lo = -d + 2 * d * i / nsub; hi = lo + 2 * d / nsub
        dl = arb((lo + hi) / 2, (hi - lo) / 2)
        val = arb(0)
        for m in reversed(range(K)):
            val = val * dl + q[m]
        lows.append(arb((val - arb(0, rem.upper())).lower()))
        highs.append(arb((val + arb(0, rem.upper())).upper()))
    Rmin = lows[0]
    for v in lows[1:]:
        Rmin = arb(Rmin.union(v).lower())
    Rmax = highs[0]
    for v in highs[1:]:
        Rmax = arb(Rmax.union(v).upper())
    info = dict(cauchy=cauchy, quad=Eq, ytail=Ey, ktail=ktail, MQ=MQ, fy=fy, Rmax=Rmax, secs=time.time() - t0)
    if verbose:
        print('centre %.4f half-width %.4f K=%d rt=%.3f kmax=%d NGL=%d: R(tc)=%s  MQ=%s cauchy=%s quad=%s ytail=%s ktail=%s  lower=%s upper=%s (%.1fs)' % (
            tc, d, K, rt, kmax, S.ngl, q[0].str(12), MQ.str(3), cauchy.str(3), Eq.str(3), Ey.str(3), ktail.str(3),
            Rmin.str(8), Rmax.str(8), time.time() - t0), flush=True)
    return Rmin, q[0], info


if __name__ == '__main__':
    tc = float(sys.argv[1]); d = float(sys.argv[2])
    K = int(sys.argv[3]) if len(sys.argv) > 3 else 20
    rt = float(sys.argv[4]) if len(sys.argv) > 4 else 1.0
    t0 = time.time()
    S = Setup()
    print('setup %.1fs; poslib sha %s; cert_window sha %s; coeff sha %s %s' % (time.time() - t0, sha(L.__file__), sha(os.path.abspath(__file__)),
          sha(COEFF_DIR + 'an_small_X1e4.json'), sha(COEFF_DIR + 'an_cert_X1e4.json')))
    Rmin, R0, info = certify(S, tc, d, K, rt, verbose=True)
    print('DECISIVE: R(t) > 0 on [%.6f, %.6f]: %s (lower bound %s)' % (tc - d, tc + d, Rmin > 0, Rmin.str(10)))
