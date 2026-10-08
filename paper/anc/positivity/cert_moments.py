"""Certificate M (the moment certificate): H_raw(t) > 0 for |t| <= T from finitely many positive moments (all Arb balls).

MATHEMATICS (Section 6 of the paper).  F := Xi^2 H_raw lies in the test class, and by the Voronoi decoupling (Lemma 3.2(c);
H_raw in W_delta by Proposition 5.9(b), its Gamma-only transform is Ghat_raw by Proposition 5.9(c))
    Fhat(xi) = sum_{m>=1} d(m) m^{-1/2} Ghat_raw(m e^{2 pi xi})   (every real xi).
For xi >= 0 every argument m e^{2 pi xi} is >= 1, where Ghat_raw(x) = sin^2(pi x) sqrt(x) sum_n a_n K0(4 pi sqrt(n x)) >= 0
(a_n > 0, Theorem 6.1; Theorem 5.4(c) and (5.8)) and Ghat_raw(1) = 1/(32 pi^2) (Theorem 5.4(d)).  Fhat is even (F even, real).
Hence Fhat >= 0 on R and
    F(t) = int Fhat(xi) cos(2 pi xi t) dxi >= sum_{j=0}^{2K+1} (-1)^j (2 pi t)^{2j} M_{2j} / (2j)!          (all real t)
because cos y >= sum_{j<=2K+1} (-1)^j y^{2j}/(2j)! for all real y; here M_{2j} := int xi^{2j} Fhat(xi) dxi
    = (1/pi) int_1^oo W_j(x) Ghat_raw(x) dx/x,    W_j(x) := sum_{m<=x} d(m) m^{-1/2} (log(x/m)/(2 pi))^{2j}.
If the right side is > 0 at t then F(t) > 0, hence Xi(t) != 0 and H_raw(t) = F(t)/Xi(t)^2 > 0.

EVALUATION (every number an Arb ball; binary64 numbers only choose parameters):
 * Ghat_raw(x) at real x > 1: sin^2(pi x) sqrt(x) [sum_{n<=N} a_n K0(4 pi sqrt(n x)) + T_N(x)], K0 from Part I's validated
   lib/besselk.K01; for n > N the analytic bracket of Theorem 6.1: abar_n (lambda_0(z_n) - eta_N) <= a_n <=
   abar_n (1 - 1/z_n + eps_N) (eta_N, eps_N = the decreasing remainder terms of lambda_-, lambda_+ at z_{N+1});
   K0(y) in sqrt(pi/2y) e^{-y} [1 - 1/(8y), 1] (DLMF 10.40(ii)); abar_n sqrt(pi/(8 pi sqrt(n) s)) e^{-4 pi sqrt(n) s}
   = e^{-kappa sqrt n}/(16 pi^2 sqrt s), s = sqrt x, kappa = 4 pi (s - 1); sums over n > N compared with integrals
   (the summands e^{-kappa sqrt y} and y^{-1/2} e^{-kappa sqrt y} decrease).
 * Quadrature: Gauss-Legendre (Arb nodes/weights) on panels with integer end points (W_j is analytic on each [k, k+1]),
   geometrically graded towards x = 1; error <= h (64/15) M rho^{-2m}/(1 - rho^{-2}) (Lemma A.2 of the paper), with M an Arb
   upper bound of |integrand| on an outward box containing the Bernstein ellipse, from |K0(w)| <= K0(Re w),
   Re sqrt(x) >= sqrt(Re x), |sin(pi x)| <= sinh(pi |x - k|) and <= cosh(pi Im x).
 * [1, 1 + 2^-KG]: 0 <= Ghat_raw(x) <= x^{1/4} [(x-1)^2/16 + x/(32 pi^2)] (from 0 < a_n <= abar_n, all n).
 * [X, oo): Ghat_raw(x) <= x^{1/4} e^{-kappa} (1 + 2(1+kappa)/kappa^2)/(16 pi^2), sum_{m<=x} d(m) m^{-1/2} <= x(1+log x),
   log x <= sqrt(x) log X/sqrt X (x >= X >= e^2) and an upper incomplete Gamma function.
 * Balls passed between processes are sent as (decimal midpoint, radius, a bound for the decimal rounding of the midpoint)
   and rebuilt with the two radii added in Arb; the sender asserts that the rebuilt ball contains the original.
MODES: true (the certified coefficient balls of Appendix A.1); triv (each a_n replaced by the hull of its interval in the
trivial-bound box, coefficients by coefficient; a weaker per-moment version of cert_moments_box.py).  The functions are also
used by cert_moments_box.py with the centres c_n of the box ('centre'), which is not a coefficient sequence of H.
Moment-polynomial positivity is checked on cells [ta, tb] of width 1/256 via P >= P_+(ta) - P_-(tb): P_+ (even j, lower ends)
and P_- (odd j, upper ends) bound the even and odd parts, which are increasing in t >= 0 because the exact moments are >= 0.
The verdict is that the certified interval [0, reach] contains [0, T_REQ].
Usage: cert_moments.py MODE NMAX J T T_REQ PREC NPROC    (shipped run: true 1500 15 12 9 128 6)"""
import sys, os, json, math, time, hashlib
from multiprocessing import Pool
from flint import arb, acb, ctx

HERE = os.path.dirname(os.path.abspath(__file__))
ANC = os.path.join(HERE, '..')                               # the top directory of the ancillary files
sys.path.insert(0, ANC)
sys.path.insert(0, HERE)
from lib.besselk import K01
import boxlib as BX

MODE, NMAX, J, TMAX, TREQ, PREC, NPROC = 'true', 1500, 15, 12.0, 9.0, 128, 6     # defaults; set by main() or configure()
KG = 22            # geometric panels [1 + 2^-k-1, 1 + 2^-k], k = 1..KG-1 ; sliver [1, 1 + 2^-KG]
XMAX = 40          # panels up to X; tail bound beyond
MNODES = 24
PI = None


def configure(prec):
    """set the working precision and pi (called at import, by main() and by cert_moments_box.py)."""
    global PREC, PI
    PREC = prec
    ctx.prec = prec
    PI = arb.pi()


configure(PREC)


def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()[:16]


def unship(t):
    """the ball [mid +/- (rad + extra)] of a shipped triple (mid string, rad, extra); radii are added in Arb (rounded up)."""
    return arb(t[0], t[1]) + arb(0, t[2])


def ship(x, digits):
    """an Arb ball as (decimal midpoint with `digits` digits, exact radius, bound for the decimal rounding of the
    midpoint); the sender checks that the ball rebuilt from it contains x."""
    t = (x.mid().str(digits, radius=False), float(x.rad()), abs(float(x.mid())) * 10.0 ** (2 - digits) + 1e-300)
    assert unship(t).contains(x), 'ball serialization lost containment'
    return t


# ------------------------------------------------------------------ coefficients
DATA = os.path.join(ANC, 'coefficients', 'data')


def load_coeffs(mode, nmax):
    big = json.load(open(os.path.join(DATA, 'an_cert_X1e4.json')))
    sm = json.load(open(os.path.join(DATA, 'an_small_X1e4.json')))
    ex = json.load(open(os.path.join(DATA, 'extra_smalln_X3e5.json')))
    infl = lambda mid, rad: arb(mid, float(rad) * (1 + 1e-9) + abs(float(mid)) * 1e-30)   # outward safety inflation
    a = [None]
    for n in range(1, nmax + 1):
        if mode == 'true':
            b = infl(*big['a'][str(n)])
            for src in (sm['a_mid_rad'], ex):
                if str(n) in src:
                    c = infl(*src[str(n)])
                    assert c.overlaps(b), 'coefficient balls disagree at n=%d' % n
                    if float(c.rad()) < float(b.rad()):
                        b = c
            a.append(b)
        elif mode == 'centre':
            a.append(BX.centre_halfwidth(n, big['T1'][str(n)])[0])
        elif mode == 'triv':
            a.append(BX.box_hull(n, big['T1'][str(n)]))
        else:
            raise ValueError('unknown mode %s' % mode)
    files = {'an_cert_X1e4.json': sha(os.path.join(DATA, 'an_cert_X1e4.json')),
             'an_small_X1e4.json': sha(os.path.join(DATA, 'an_small_X1e4.json')),
             'extra_smalln_X3e5.json': sha(os.path.join(DATA, 'extra_smalln_X3e5.json'))}
    return a, files


def tail_consts(N):
    """(eps_N, eta_N): for n > N, a_n/abar_n <= 1 - 1/z_n + eps_N and >= lambda_0(z_n) - eta_N (Theorem 6.1 and the
    monotonicity statements in its proof), with lambda_0(z) >= 1 - 11/(8z) - c2/z^2, c2 = 3/32 + pi^3/16.
    Every element of the trivial-bound box satisfies the same bounds."""
    z = 4 * PI * arb(N + 1).sqrt()
    e = BX.ee(z)
    epsN = ((PI + 1) / 2 + 2 / z ** 2) * z / (2 * e) + BX.varrho(z)
    etaN = (PI + 1) * z / (4 * e) + BX.varrho(z)
    c2 = arb(3) / 32 + PI ** 3 / 16
    return epsN, etaN, c2


# ------------------------------------------------------------------ Ghat_raw
def I0int(kap, M):     # int_M^oo e^{-kap sqrt y} dy
    r = kap * arb(M).sqrt()
    return 2 * (-r).exp() * (1 + r) / kap ** 2


def Ihalf(kap, M):     # int_M^oo y^{-1/2} e^{-kap sqrt y} dy
    return 2 * (-kap * arb(M).sqrt()).exp() / kap


def choose_N(xf, nmax):
    """parameter choice (binary64): smallest N with the tail below 2^-80 of the leading term, capped at nmax."""
    s = math.sqrt(xf); kap = 4 * math.pi * (s - 1)
    for N in (20, 40, 60, 100, 150, 200, 300, 450, 600, 800, 1000, 1200, nmax):
        if N >= nmax:
            return nmax
        r = kap * math.sqrt(N)
        if r > 0 and math.exp(-r) * (1 + r) / kap ** 2 * 2 < 2.0 ** -80 * math.exp(-kap) * 1e-3:
            return N
    return nmax


def tail_bracket(x, N, TC):
    """[lower, upper] for sum_{n > N} a_n K0(4 pi sqrt(n x)), real ball x > 1 (as an arb ball)."""
    epsN, etaN, c2 = TC
    s = x.sqrt()
    kap = 4 * PI * (s - 1)
    pref = 1 / (16 * PI ** 2 * s.sqrt())
    zN1 = 4 * PI * arb(N + 1).sqrt()
    # upper: (1 - 1/z_n + eps)(K0 factor <= 1)  ->  (1+eps) sum e^{-k sqrt n} - (1/4pi) sum n^{-1/2} e^{-k sqrt n}
    up = (1 + epsN) * I0int(kap, N) - Ihalf(kap, N + 1) / (4 * PI)
    # lower: (lambda_0 - eta)(1 - 1/(8 z s)) >= 1 - (11/8 + 1/8)/z_n - c2/z_{N+1}^2 - eta   (s >= 1)
    cL = 1 - c2 / zN1 ** 2 - etaN
    lo = cL * I0int(kap, N + 1) - (arb(1.5) / (4 * PI)) * Ihalf(kap, N)
    lo = pref * lo; up = pref * up
    return arb(lo.lower()).union(arb(up.upper()))


def K0(y):
    p = ctx.prec
    v = K01(y, p)[0]
    ctx.prec = p
    return v


_A = None; _TC = {}


def _init(mode, nmax, prec):
    global _A, _TC
    configure(prec)
    _A = load_coeffs(mode, nmax)[0]


def Ghat(x, nmax):
    """Ghat_raw(x) for a real ball x > 1; returns (ball, N used)."""
    xf = float(x.mid())
    N = choose_N(xf, nmax)
    if N not in _TC:
        _TC[N] = tail_consts(N)
    S = arb(0)
    fourpi = 4 * PI
    for n in range(1, N + 1):
        S += _A[n] * K0(fourpi * (n * x).sqrt())
    T = tail_bracket(x, N, _TC[N])
    return (PI * x).sin() ** 2 * x.sqrt() * (S + T), N


def _work(args):
    xs_str, nmax = args
    out = []
    for xs in xs_str:
        x = unship(xs)
        g, N = Ghat(x, nmax)
        out.append((ship(g, 40), N))
    return out


# ------------------------------------------------------------------ divisor weights
def dcount(m):
    return sum(1 for d in range(1, m + 1) if m % d == 0)


def W_list(x, k, J):
    """[W_0(x), ..., W_J(x)] for x in [k, k+1] (sum over m <= k), real or ball x."""
    out = [arb(0)] * (J + 1)
    for m in range(1, k + 1):
        L = (x / m).log() / (2 * PI)
        w = arb(dcount(m)) / arb(m).sqrt()
        L2 = L * L
        p = arb(1)
        for j in range(J + 1):
            out[j] = out[j] + w * p
            p = p * L2
    return out


def panels():
    P = []
    for k in range(KG - 1, 0, -1):                                  # [1 + 2^-(k+1), 1 + 2^-k]
        a = 1 + arb(2) ** (-(k + 1)); b = 1 + arb(2) ** (-k)
        P.append((a, b, 1, arb(2)))
    P.append((arb(1.5), arb(1.75), 1, arb(3)))
    P.append((arb(1.75), arb(2), 1, arb(3)))
    for k in range(2, XMAX):
        P.append((arb(k), arb(k) + arb(0.5), k, arb(4)))
        P.append((arb(k) + arb(0.5), arb(k + 1), k, arb(4)))
    return P


def ellipse_box(a, b, rho):
    c = (a + b) / 2; h = (b - a) / 2
    A = h * (rho + 1 / rho) / 2; B = h * (rho - 1 / rho) / 2
    return arb((c - A).lower()), arb((c + A).upper()), arb(B.upper())


def Mbound(a, b, k, rho, N, A, TC, J):
    """Arb upper bounds of sup |(1/pi) W_j(x) Ghat_raw(x)/x| on the box containing E_rho, j = 0..J, and of
    sup |(1/pi) Wcos_t(x) Ghat/x| / cosh-factor (for the point values F(t))."""
    xlo, xhi, B = ellipse_box(a, b, rho)
    assert xlo > 1, 'ellipse box leaves Re x > 1'
    absx_hi = (xhi ** 2 + B ** 2).sqrt()
    # |sin(pi x)|^2
    rx = arb(abs(xhi - k).upper()).max(arb(abs(xlo - k).upper()))
    r = arb((rx ** 2 + B ** 2).sqrt().upper())
    s2 = (PI * r).sinh() ** 2
    s2b = (PI * B).cosh() ** 2
    s2 = s2 if s2 < s2b else s2b
    sx = absx_hi.sqrt()
    smin = xlo.sqrt()
    Ssum = arb(0)
    for n in range(1, N + 1):
        Ssum += abs(A[n]) * K0(4 * PI * smin * arb(n).sqrt())
    kap = 4 * PI * (smin - 1)
    epsN = TC[0]
    Tup = (1 + epsN) * I0int(kap, N) / (16 * PI ** 2 * smin.sqrt())
    Gsup = arb((s2 * sx * (Ssum + Tup)).upper())
    # |W_j|: |log(x/m)| <= max(|log(|x|/m)|) + |arg x|
    argx = (B / xlo).atan()
    res = []
    Wb = [arb(0)] * (J + 1)
    for m in range(1, k + 1):
        Lm = arb(abs((xlo / m).log()).upper()).max(arb(abs((absx_hi / m).log()).upper())) + argx
        Lm = arb(Lm.upper()) / (2 * PI)
        w = arb(dcount(m)) / arb(m).sqrt()
        for j in range(J + 1):
            Wb[j] = Wb[j] + w * Lm ** (2 * j)
    Wc = sum((arb(dcount(m)) / arb(m).sqrt() for m in range(1, k + 1)), arb(0))
    for j in range(J + 1):
        res.append(arb((Wb[j] * Gsup / (PI * xlo)).upper()))
    return res, arb((Wc * Gsup / (PI * xlo)).upper()), argx, xlo


def xi_half():
    """Xi(0) = xi(1/2) = (1/2) s (s-1) pi^{-s/2} Gamma(s/2) zeta(s) at s = 1/2 (Arb; used only for a cross-check)."""
    s = arb(1) / 2
    return s * (s - 1) / 2 * PI ** (-s / 2) * (s / 2).gamma() * acb(s).zeta().real


def main():
    global MODE, NMAX, J, TMAX, TREQ, NPROC
    a = sys.argv[1:]
    MODE = a[0] if len(a) > 0 else MODE
    NMAX = int(a[1]) if len(a) > 1 else NMAX
    J = int(a[2]) if len(a) > 2 else J
    TMAX = float(a[3]) if len(a) > 3 else TMAX
    TREQ = float(a[4]) if len(a) > 4 else TREQ
    NPROC = int(a[6]) if len(a) > 6 else NPROC
    configure(int(a[5]) if len(a) > 5 else PREC)
    if MODE not in ('true', 'triv'):
        raise ValueError('MODE must be true or triv')
    t0 = time.time()
    A, files = load_coeffs(MODE, NMAX)
    here = os.path.abspath(__file__)
    print('cert_moments.py mode=%s NMAX=%d J=%d T=%g T_req=%g prec=%d nodes/panel=%d KG=%d XMAX=%d' % (
        MODE, NMAX, J, TMAX, TREQ, PREC, MNODES, KG, XMAX))
    print('hashes: script %s boxlib %s besselk %s ; %s' % (sha(here), sha(os.path.join(HERE, 'boxlib.py')),
          sha(os.path.join(ANC, 'lib', 'besselk.py')), ' '.join('%s %s' % kv for kv in files.items())))
    print('a_1 = %s   a_2 = %s' % (A[1].str(15), A[2].str(15)), flush=True)
    GL = [arb.legendre_p_root(MNODES, i, weight=True) for i in range(MNODES)]
    P = panels()
    # nodes
    jobs = []; meta = []
    for (a_, b, k, rho) in P:
        h = (b - a_) / 2; c = (a_ + b) / 2
        xs = [c + h * x for (x, w) in GL]
        meta.append((a_, b, k, rho, xs, [h * w for (x, w) in GL]))
        jobs.append([ship(x, 50) for x in xs])
    # balance: split the near-1 panels (expensive) into single-node jobs
    flat = []
    for pi_, js in enumerate(jobs):
        for ni, xs in enumerate(js):
            flat.append((pi_, ni, xs))
    flat.sort(key=lambda r: float(r[2][0]))
    chunks = [flat[i::NPROC * 8] for i in range(NPROC * 8)]
    with Pool(NPROC, initializer=_init, initargs=(MODE, NMAX, PREC)) as pool:
        res = pool.map(_work, [([c[2] for c in ch], NMAX) for ch in chunks])
    G = {}
    Nused = {}
    for ch, rr in zip(chunks, res):
        for (pi_, ni, _), (gs, N) in zip(ch, rr):
            G[(pi_, ni)] = unship(gs)
            Nused[pi_] = max(Nused.get(pi_, 0), N)
    print('node values: %d nodes in %.0fs' % (len(G), time.time() - t0), flush=True)
    TC = {N: tail_consts(N) for N in set(Nused.values())}
    # assemble moments
    Mom = [arb(0)] * (J + 1)
    errs = [arb(0)] * (J + 1)
    tcheck = [0, 2, 4, 6, 8, 10, 12]
    Fchk = {t: arb(0) for t in tcheck}; Fabs = {t: arb(0) for t in tcheck}; Ferr = {t: arb(0) for t in tcheck}
    gmin = None
    for pi_, (a_, b, k, rho, xs, ws) in enumerate(meta):
        N = Nused[pi_]
        Mb, Mc, argx, xlo = Mbound(a_, b, k, rho, N, A, TC[N], J)
        q = (64 * (b - a_) / 2 / 15) * rho ** (-2 * MNODES) / (1 - rho ** -2)
        for ni, (x, w) in enumerate(zip(xs, ws)):
            g = G[(pi_, ni)]
            if gmin is None or g.lower() < gmin:
                gmin = g.lower()
            Wl = W_list(x, k, J)
            base = w * g / (PI * x)
            for j in range(J + 1):
                Mom[j] += Wl[j] * base
            for t in tcheck:
                Wc = arb(0); Wa = arb(0)
                for m in range(1, k + 1):
                    cc = arb(dcount(m)) / arb(m).sqrt() * (arb(t) * (x / m).log()).cos()
                    Wc += cc; Wa += abs(cc)
                Fchk[t] += Wc * base; Fabs[t] += Wa * base
        for j in range(J + 1):
            errs[j] += q * Mb[j]
        for t in tcheck:
            Ferr[t] += q * Mc * (arb(t) * argx).cosh()
    # sliver [1, 1 + 2^-KG]
    hs = arb(2) ** (-KG)
    gs = (1 + hs) ** arb(0.25) * (hs ** 2 / 16 + (1 + hs) / (32 * PI ** 2))
    sl = [arb(0)] * (J + 1)
    for j in range(J + 1):
        sl[j] = hs * gs * ((1 + hs).log() / (2 * PI)) ** (2 * j) / PI
    # tail [X, oo)
    X = arb(XMAX)
    kapX = 4 * PI * (X.sqrt() - 1)
    fac = (1 + 2 * (1 + kapX) / kapX ** 2) / (16 * PI ** 2) * (4 * PI).exp()     # Ghat <= x^{1/4} e^{4pi} e^{-4pi sqrt x} fac'
    tl = []
    for j in range(J + 1):
        # integrand (1/pi) W_j Ghat / x <= (1/pi) x(1+log x) (x^{j} c^{2j}) x^{1/4} fac e^{-4 pi sqrt x} / x, c = log X/(2 pi sqrt X)
        # and 1 + log x <= 2 sqrt(x) (x >= 1):  <= (2/pi) c^{2j} fac x^{j + 3/4} e^{-4 pi sqrt x};  int_X^oo x^q e^{-b sqrt x} dx
        # = 2 b^{-2q-2} Gamma(2q+2, b sqrt X)
        cX = X.log() / (2 * PI * X.sqrt())
        qq = arb(j) + arb(0.75)
        b4 = 4 * PI
        integ = 2 * b4 ** (-2 * qq - 2) * (b4 * X.sqrt()).gamma_upper(2 * qq + 2)      # Gamma(2q+2, b sqrt X)
        tl.append(arb((2 / PI * cX ** (2 * j) * fac * integ).upper()))
    for j in range(J + 1):
        Mom[j] = Mom[j] + arb(0, errs[j].upper()) + arb(0, sl[j].upper()) / 2 + sl[j] / 2 + arb(0, tl[j].upper()) / 2 + tl[j] / 2
    for t in tcheck:
        Fchk[t] = Fchk[t] + arb(0, Ferr[t].upper()) + arb(0, (sl[0] + tl[0]).upper())
    print('min lower end of Ghat over all nodes: %s' % arb(gmin).str(5))
    for j in range(J + 1):
        print('M_%-2d = %s   (rel. radius %.2e ; quad err %.1e ; sliver %.1e ; tail %.1e)' % (
            2 * j, Mom[j].str(14), float(Mom[j].rad() / Mom[j].mid()), float(errs[j].upper()), float(sl[j].upper()), float(tl[j].upper())))
    M0 = Mom[0]
    print('[C] F(0) = M_0 = %s > 0 : %s' % (M0.str(14), M0 > 0))
    if MODE == 'true':
        xi0 = xi_half()
        r0 = M0 / xi0 ** 2
        prop64 = arb('0.0011355097904', 1.86e-9)
        print('[cross-check, not used in any proof] Xi(0) = %s ; M_0/Xi(0)^2 = H_raw(0) in %s ; Proposition 6.4: %s ; overlap: %s'
              % (xi0.str(13), r0.str(10, radius=True, more=True), prop64.str(11, radius=True, more=True), r0.overlaps(prop64)))
    for t in tcheck:
        print('[C] F(%2d) = %s ; int Fhat |cos| = %s ; conditioning int|.|/F = %s' % (t, Fchk[t].str(12), Fabs[t].str(8), (Fabs[t] / Fchk[t]).str(5) if Fchk[t] > 0 else 'n/a'))
    # polynomial lower bound positivity on [0, T]: P(t) = Pp(t) - Pm(t), Pp, Pm increasing in t >= 0 (exact moments >= 0)
    best = None
    for K in range(0, (J - 1) // 2 + 1):
        top = 2 * K + 1
        def PpPm(t):
            Pp = arb(0); Pm = arb(0)
            for j in range(top + 1):
                c = (2 * PI * t) ** (2 * j) / arb(2 * j).fac()
                if j % 2 == 0:
                    Pp += c * arb(Mom[j].lower())
                else:
                    Pm += c * arb(Mom[j].upper())
            return Pp, Pm
        # cells of width dt: on [ta, tb], P >= Pp(ta) - Pm(tb)
        dt = 1 / arb(256)
        ta = arb(0); reach = 0.0; ok = True
        while float(ta.mid()) < TMAX - 1e-12:
            tb = ta + dt
            Pp, _ = PpPm(ta); _, Pm = PpPm(tb)
            if not ((Pp - Pm) > 0):
                ok = False
                break
            reach = float(tb.mid()); ta = tb
        print('moment bound with M_0..M_%d: F > 0 certified on [0, %.8f]%s' % (2 * top, reach, '' if not ok else ' (= requested T)'), flush=True)
        if best is None or reach > best[1]:
            best = (2 * top, reach)
    print('DECISIVE (Certificate M, mode=%s): F(t) = Xi(t)^2 H_raw(t) > 0, hence H_raw(t) > 0, for |t| <= %.8f (moments M_0..M_%d) ; '
          'covers [0, %g]: %s   (%.0fs)' % (MODE, best[1], best[0], TREQ, best[1] >= TREQ, time.time() - t0))
    out = {'mode': MODE, 'NMAX': NMAX, 'prec': PREC, 'moments': {str(2 * j): Mom[j].str(30, radius=True, more=True) for j in range(J + 1)},
           'reach': best, 'script_sha': sha(here)}
    os.makedirs(os.path.join(HERE, 'out'), exist_ok=True)
    with open(os.path.join(HERE, 'out', 'moments_%s_N%d_p%d.json' % (MODE, NMAX, PREC)), 'w') as f:
        json.dump(out, f, indent=0)


if __name__ == '__main__':
    main()
