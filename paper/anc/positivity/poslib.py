"""Positivity library: rigorous (Arb ball) evaluation of the physical-side four-path formula for H.

  H_raw(t) = R(t) / (2 pi^2 (t^2 + 1/4)^2),   R(t) = axis(t) + arcs(t)          (a_n-units: a_n = n S_n + delta_{n,1}/4)
  axis(t) = int_1^oo  Phi(Y) cos(t log Y) dY,          Phi(Y) = sum_n 2 pi n a_n sqrt(Y) K0(2 pi n Y)          (> 0)
  arcs(t) = 1/2 int_{1/2}^oo g(Y) fhat_t(Y) dY,        g(Y)   = sum_n (-1)^{n+1} 2 pi n a_n sqrt(Y) K0(2 pi n Y)
  fhat_t(Y) = sqrt(sin th) [P_t(cos th) + P_t(-cos th)] / (2 P_t(0)),  th = 2 arccot(2Y),  P_t = P_{-1/2+it} (Ferrers)
  With z1 := sin^2(th/2) = 1/(4Y^2+1) (<= 1/2 for Y >= 1/2):  sqrt(sin th) = 2 sqrt(Y z1),
     P_t(cos th)  = sum_k c_k z1^k                                    (2F1(1/2-it,1/2+it;1;z1))
     P_t(-cos th) = (cosh(pi t)/pi) sum_k c_k [2 psi(k+1) - 2 Re psi(k+1/2+it) - log z1] z1^k   (DLMF 15.8.10, c=a+b)
     c_k = prod_{j<k} ((1/2+j)^2 + t^2) / (k!)^2,   P_t(0) = sqrt(pi)/|Gamma(3/4+it/2)|^2.
Coefficients: certified balls (JSON files in coefficients/data/); tail n > NMAX bounded with the coefficient bound
a_n <= A0(n) = n^{1/4} e^{4 pi sqrt n}/(4 sqrt2 pi^2), proved in the paper.
K0 for real arguments: the Part I library lib/besselk.K01 (rigorous, tight).  Complex-argument majorant: |K0(z)| <= K0(Re z).
Quadrature: Gauss-Legendre (arb.legendre_p_root, rigorous nodes/weights) per panel; for an m-NODE rule the error bound is
   |I - G_m| <= ((b-a)/2) (64/15) M rho^{-2m} / (1 - rho^{-2}),  M >= sup |f| on the Bernstein ellipse E_rho
   (Trefethen, ATAP Thm 19.3 is stated for the (n+1)-point rule; the m-node form used here is proved in the paper).
All tail factors are Arb upper ends; the Arb majorants of the error terms live in cert_window.py; Coeffs checks that
balls from different sources overlap.
"""
import sys, os, json, math
from flint import arb, acb, ctx
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))     # the top directory (lib/ = Part I library)
from lib.besselk import K01 as _K01

PREC = 160
ctx.prec = PREC
PI = arb.pi()


def setprec(p):
    global PREC
    PREC = p
    ctx.prec = p


def K0(x):
    """rigorous K0 for a real arb ball x > 0 (Part I library)."""
    p = ctx.prec
    v = _K01(x, p)[0]
    ctx.prec = p
    return v


# ------------------------------------------------------------------ coefficients
class Coeffs:
    def __init__(self, path_small, path_big, nmax=200, extra=None):
        """a_n balls: an_cert (n <= 1500) replaced by the sharper of {an_small, extra} where available."""
        d1 = json.load(open(path_small)); d2 = json.load(open(path_big))
        self.meta = (d1['meta'], d2['meta'])
        # outward safety inflation of every stored [mid_string, rad_float] pair (independent of the outward rounding
        # already applied to the stored radii):
        # rad -> rad (1 + 1e-9) + |mid| 1e-30 ; arb(str, rad) adds rad to the decimal->binary conversion radius.
        infl = lambda mid, rad: arb(mid, float(rad) * (1 + 1e-9) + abs(float(mid)) * 1e-30)
        A = {int(k): infl(mid, rad) for k, (mid, rad) in d2['a'].items()}
        srcs = [d1['a_mid_rad']] + ([extra] if extra else [])
        for S in srcs:
            for k, (mid, rad) in S.items():
                b = infl(mid, rad); k = int(k)
                if k in A:
                    assert A[k].overlaps(b), 'coefficient balls from different sources do not overlap (n=%d)' % k
                if k not in A or float(b.rad()) < float(A[k].rad()):
                    A[k] = b
        self.nmax = min(nmax, max(A))
        self.a = [None] + [A[n] for n in range(1, self.nmax + 1)]

    @staticmethod
    def A0(n):
        """Coefficient bound proved in the paper: a_n <= A0(n) = n^{1/4} e^{4 pi sqrt n} / (4 sqrt 2 pi^2)  (all n >= 1)."""
        n = arb(n)
        return n ** arb('0.25') * (4 * PI * n.sqrt()).exp() / (4 * arb(2).sqrt() * PI ** 2)


def _tail_terms(C, x_lo, absY_hi, N):
    """rigorous upper bound (arb) for sum_{n >= N} 2 pi n A0(n) |Y|^{1/2} K0(2 pi n x),  x >= x_lo > 0, |Y| <= absY_hi.
       K0(z) <= sqrt(pi/(2z)) e^{-z};  U(n) := 2 pi n A0(n) absY^{1/2} sqrt(pi/(4 pi n x_lo)) e^{-2 pi n x_lo};
       U(n+1)/U(n) <= ((n+1)/n)^{3/4} e^{2 pi/sqrt(n) - 2 pi x_lo} =: q_n, decreasing in n; sum <= U(N)/(1 - q_N)."""
    x = arb(x_lo); N = int(N)
    U = 2 * PI * N * Coeffs.A0(N) * arb(absY_hi).sqrt() * (PI / (4 * PI * N * x)).sqrt() * (-2 * PI * N * x).exp()
    q = (arb(N + 1) / N) ** arb('0.75') * (2 * PI / arb(N).sqrt() - 2 * PI * x).exp()
    if not (q < 1):
        raise ValueError('tail bound: q_N >= 1 (N=%d, x_lo=%s)' % (N, x_lo))
    return U / (1 - q)


def phi_g(C, Y, N=None):
    """(Phi(Y), g(Y)) for real ball Y >= 1/2, with tail bound for n > N."""
    N = N or C.nmax
    Y = arb(Y)
    sY = Y.sqrt()
    S0 = arb(0); Sg = arb(0)
    for n in range(1, N + 1):
        tm = 2 * PI * n * C.a[n] * sY * K0(2 * PI * n * Y)
        S0 += tm
        Sg += tm if n % 2 else -tm
        if n > 12 and float(tm.upper()) < 1e-60 * float(S0.lower()):
            N = n
            break
    tail = _tail_terms(C, Y.lower(), Y.upper(), N + 1)
    tl = arb(0, tail.upper())
    return S0 + tl, Sg + tl


# ------------------------------------------------------------------ conical functions
def s_ball(tb):
    """s = t^2 as a tight ball for a real ball t (handles balls containing 0)."""
    a = arb(abs(tb).lower()); b = arb(abs(tb).upper())
    sl = (a * a).lower(); sh = (b * b).upper()
    return arb(sl).union(arb(sh))


class Conical:
    """P_{-1/2+it} pieces for a real ball t (precomputing the k-sequences up to K).
       For a ball t = [t_lo, t_hi] (0 <= t_lo), the t-dependent scalars are enclosed by monotonicity in |t|:
       c_k(s) increasing in s = t^2; Re psi(x+iy) increasing in y^2 (series psi(x+iy) - psi(x) = sum_j y^2/((x+j)((x+j)^2+y^2)));
       cosh(pi t) increasing; P_t(0) = sqrt(pi)/|Gamma(3/4+it/2)|^2 increasing (|Gamma(3/4+iy)| decreasing in y)."""
    def __init__(self, tb, K=200):
        tb = arb(tb)
        self.t = tb
        self.s = s = s_ball(tb)
        self.K = K
        c = [arb(1)]
        for k in range(K + 1):
            c.append(c[-1] * ((arb(1) / 2 + k) ** 2 + s) / arb(k + 1) ** 2)
        self.c = c
        tl = arb(abs(tb).lower()); th_ = arb(abs(tb).upper())
        pts = [tl] if float(tb.rad()) == 0 else [tl, th_]
        brs = []; chs = []; p0s = []
        for tp in pts:
            z = acb(arb(1) / 2, tp)
            ps = z.digamma()
            g = arb.const_euler()
            H = arb(0)
            br = []
            for k in range(K + 2):
                br.append(2 * (H - g) - 2 * ps.real)
                H += arb(1) / (k + 1)
                ps = ps + 1 / (z + k)
            brs.append(br)
            chs.append((PI * tp).cosh())
            G = acb(arb(3) / 4, tp / 2).gamma()
            p0s.append(arb.const_sqrt_pi() / (G.real ** 2 + G.imag ** 2))
        if len(pts) == 1:
            self.br = brs[0]; self.coshpi = chs[0]; self.P0 = p0s[0]
        else:
            self.br = [brs[0][k].union(brs[1][k]) for k in range(K + 2)]
            self.coshpi = chs[0].union(chs[1]); self.P0 = p0s[0].union(p0s[1])
        self.s_up = arb(s.upper())
        self.s_hi = float(self.s_up)          # float copy: loop control only, never in a bound

    def _tailfac(self, z_up, k):
        """Arb upper bound for sum_{j > k} c_j z^j / (c_{k+1} z^{k+1}) <= 1/(1-q), q = (1 + s/(k+1)^2) z
           (ratio c_{j+1}/c_j = ((1/2+j)^2 + s)/(j+1)^2 <= 1 + s/(k+1)^2 for j >= k)."""
        q = arb(((1 + self.s_up / arb(k + 1) ** 2) * arb(z_up)).upper())
        if not (q < arb('0.9')):
            raise ValueError('conical tail: q=%s' % q.str(5))
        return arb((1 / (1 - q)).upper())

    def _brbound(self, k):
        """Arb upper bound of |br_j|, j > k (real t, t^2 <= s): max(2/(j+1/2), s(2/(j+1/2)^3 + 1/(j+1/2)^2)) is decreasing
           in j; 0 <= psi(j+1) - psi(j+1/2) <= 1/(j+1/2), 0 <= Re psi(x+it) - psi(x) <= t^2(1/x^3 + 1/(2x^2))."""
        kh = arb(k) + arb('1.5')
        return arb((2 / kh + self.s_up * (2 / kh ** 3 + 1 / kh ** 2)).upper())

    def fhat(self, Y):
        """fhat_t(Y) for a real ball Y >= 1/2 (z1 = 1/(4Y^2+1) <= 1/2)."""
        Y = arb(Y)
        z1 = 1 / (4 * Y * Y + 1)
        lz = z1.log()
        S1 = arb(0); S2 = arb(0); zk = arb(1)
        for k in range(self.K + 1):
            tm = self.c[k] * zk
            S1 += tm
            S2 += tm * (self.br[k] - lz)
            zk = zk * z1
            if k > 8 and float(tm.upper()) < 2.0 ** (-PREC - 10) * float(S1.lower()):
                break
        else:
            raise ValueError('conical series: increase K')
        kk = k
        tailc = arb((self.c[kk + 1] * zk).upper()) * self._tailfac(z1.upper(), kk)
        bmax = self._brbound(kk) + arb(abs(lz).upper())
        S1 += arb(0, tailc.upper())
        S2 += arb(0, (tailc * bmax).upper())
        num = S1 + self.coshpi / PI * S2
        return 2 * (Y * z1).sqrt() * num / (2 * self.P0)


# ------------------------------------------------------------------ Gauss-Legendre with ellipse error bound
_GL = {}


def gl_nodes(n):
    if n not in _GL:
        p = ctx.prec
        _GL[n] = [arb.legendre_p_root(n, k, weight=True) for k in range(n)]
        ctx.prec = p
    return _GL[n]


def ellipse_box(a, b, rho):
    c = (a + b) / 2; h = (b - a) / 2
    ax = h * (rho + 1 / rho) / 2; ay = h * (rho - 1 / rho) / 2
    return c - ax, c + ax, ay


def gl_panel(f, a, b, n, rho, M):
    """sum_j w_j f(x_j) on [a,b] plus rigorous error ball given M >= sup|f| on E_rho."""
    a_ = arb(a); b_ = arb(b)
    h = (b_ - a_) / 2; c = (a_ + b_) / 2
    S = arb(0)
    for (x, w) in gl_nodes(n):
        S += w * f(c + h * x)
    S = S * h
    rho = arb(rho)
    err = arb(((b_ - a_) / 2 * arb(64) / 15 * arb(M) * rho ** (-2 * n) / (1 - rho ** -2)).upper())   # n NODES (m-node form)
    return S + arb(0, err.upper()), err


def conical_pm(cn, Y):
    """(P_t(cos th), P_t(-cos th)) for a real ball Y >= 1/2, th = 2 arccot(2Y); same series and tail bounds as Conical.fhat."""
    Y = arb(Y)
    z1 = 1 / (4 * Y * Y + 1)
    lz = z1.log()
    S1 = arb(0); S2 = arb(0); zk = arb(1)
    for k in range(cn.K + 1):
        tm = cn.c[k] * zk
        S1 += tm
        S2 += tm * (cn.br[k] - lz)
        zk = zk * z1
        if k > 8 and float(tm.upper()) < 2.0 ** (-PREC - 10) * float(S1.lower()):
            break
    else:
        raise ValueError('conical series: increase K')
    tailc = arb((cn.c[k + 1] * zk).upper()) * cn._tailfac(z1.upper(), k)
    bmax = cn._brbound(k) + arb(abs(lz).upper())
    S1 += arb(0, tailc.upper())
    S2 += arb(0, (tailc * bmax).upper())
    return S1, cn.coshpi / PI * S2
