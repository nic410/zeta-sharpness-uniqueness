"""Certified library of the coefficient certificates (Appendix A.1 of the paper): Bessel order derivatives, Kloosterman
sums and c-tail bounds.

Everything returned as an arb ball is a RIGOROUS enclosure (Arb ball arithmetic via python-flint), with every
truncation bounded explicitly.  Floating point is used only for bookkeeping (indices) and never as a proof step.

Objects (notation of the paper, which writes S_n for Kc_n and A_n(1) for alpha_n = a_n(1)):
  Ihat(z) := d/dmu I_mu(z) |_{mu=2},  Jhat(z) := d/dmu J_mu(z) |_{mu=2}
  Kc_n    := sum_{c>=1} c^{-1} [ S(1,n;c) Jhat(4 pi sqrt n / c) - S(-1,n;c) Ihat(4 pi sqrt n / c) ]
  a_n     := n Kc_n + delta_{n,1}/4          (b_n = C a_n)
  S(m,n;c) = sum_{d mod c, (d,c)=1} e((m dbar + n d)/c)

Bessel hats:
  * series (z <= ZSER): termwise mu-derivative of the ascending series of I_mu, J_mu at mu = 2 (proved in the paper):
        Ihat(z) = sum_k  (z/2)^{2k+2}/(k!(k+2)!) [log(z/2) - psi(k+3)]
        Jhat(z) = sum_k (-1)^k (z/2)^{2k+2}/(k!(k+2)!) [log(z/2) - psi(k+3)]
    truncated when the term ratio bound is <= 1/2 and the last term is below 2^-prec relative;
    remaining tail <= 2 * |next term bound| (geometric), added as a ball radius.
  * closed forms (z > ZSER) (DLMF 10.38.3 and 10.15.3 at n = 2):
        Ihat = -K_2 + 2 I_0/z^2 - 2 I_1/z,   Jhat = (pi/2) Y_2 + 2 J_0/z^2 + 2 J_1/z
    evaluated with Arb's Bessel functions (rigorous enclosures; precision raised with z), except K_0, K_1, which come
    from the Part I library lib/besselk.py.
Kloosterman sums:
  * twisted multiplicativity S(1,n;c) = prod_{q || c} S(1, n (c/q)^{-2} mod q ; q)   (e.g. Iwaniec-Kowalski (1.59))
  * for each prime power q: the whole table j -> S(1,j;q) from ONE rigorous Arb DFT (acb.dft) of
    x_d = e(dbar/q) (d a unit), x_d = 0 otherwise:  dft(x)_j = sum_d x_d e(-jd/q) = S(1,-j;q).
    Stored as float64 midpoints + one rigorous radius per table (Arb radius + float conversion error).
Weil bound: |S(m,n;c)| <= d(c) (m,n,c)^{1/2} c^{1/2}   (Weil 1948; Estermann 1961; Iwaniec-Kowalski Cor. 11.12)
"""
import math, sys, os
import numpy as np
from flint import arb, acb, ctx

ZSER = arb(8)          # series for z <= 8, closed forms above


# ------------------------------------------------------------------------------------------- Bessel hats
_psi_cache = {}


def _psi_int(m, prec):
    """psi(m) for integer m >= 1, as arb: -gamma + H_{m-1}."""
    key = (m, prec)
    if key not in _psi_cache:
        ctx.prec = prec
        h = arb(0)
        for j in range(1, m):
            h += arb(1) / j
        _psi_cache[key] = h - arb.const_euler()
    return _psi_cache[key]


def hats_series(z, prec=96):
    """Rigorous (Ihat(z), Jhat(z)) from the ascending series. z: arb > 0 (any size; cost/precision grow with z)."""
    ctx.prec = prec
    z = arb(z)
    w = z * z / 4                       # (z/2)^2
    lz = (z / 2).log()
    wf = float(w.upper())
    # term_k = w^{k+1}/(k!(k+2)!) * (lz - psi(k+3))
    t = w / 2                           # w^{1}/(0! 2!)
    sI = arb(0); sJ = arb(0)
    k = 0
    H = arb(1) + arb(1) / 2             # H_{k+2} with k = 0  (psi(k+3) = H_{k+2} - gamma)
    g = arb.const_euler()
    while True:
        term = t * (lz - (H - g))
        sI += term
        sJ += term if k % 2 == 0 else -term
        k += 1
        t = t * w / (k * (k + 2))
        H += arb(1) / (k + 2)
        # ratio bound for k' >= k:  |t_{k'+1}/t_{k'}| <= w/((k'+1)(k'+3)) * (1 + 1/(k'+3)/max(|lz - psi|,..)) ; use crude:
        # |term_{k'}| <= t_{k'} (|lz| + H_{k'+2}) and (|lz|+H_{k'+3})/(|lz|+H_{k'+2}) <= 1 + 1/(k'+3) <= 2
        if k > 2 * wf + 4 and 2 * wf / ((k + 1) * (k + 3)) <= 0.45:
            tb = t * (abs(lz) + H)      # bound for |term_k| (next term)
            if tb.upper() < (abs(sI) + abs(sJ) + arb(1e-300)).lower() * arb(2) ** (-prec - 4):
                break
    rad = 2 * tb                        # geometric tail with ratio <= 1/2
    sI += arb(0, rad.upper()); sJ += arb(0, rad.upper())
    return sI, sJ


def hats_closed(z, prec=96):
    """Rigorous (Ihat, Jhat) via DLMF closed forms.  K_2 = K_0 + 2K_1/z with the tight Part I K_0/K_1 enclosures
    (Arb's own bessel_k can return loose balls); I_0, I_1, J_0, J_1, Y_2 from Arb at prec + 32 bits."""
    p = prec + 32
    ctx.prec = p
    z = arb(z)
    k0, k1 = K01(z, p)
    ctx.prec = p
    K2 = k0 + 2 * k1 / z
    I = -K2 + 2 * z.bessel_i(0) / z ** 2 - 2 * z.bessel_i(1) / z
    J = arb.pi() / 2 * z.bessel_y(2) + 2 * z.bessel_j(0) / z ** 2 + 2 * z.bessel_j(1) / z
    ctx.prec = prec
    return +I, +J


def hats(z, prec=96):
    z = arb(z)
    if z.upper() <= ZSER:
        return hats_series(z, prec)
    return hats_closed(z, prec)


# ------------------------------------------------------------------------------------------- arithmetic helpers
def spf_sieve(N):
    """smallest prime factor table for 0..N"""
    spf = np.zeros(N + 1, dtype=np.int64)
    for i in range(2, N + 1):
        if spf[i] == 0:
            spf[i::i][spf[i::i] == 0] = i
    return spf


def factor_pp(c, spf):
    """list of (p, q=p^k) with q || c"""
    out = []
    while c > 1:
        p = int(spf[c]); q = 1
        while c % p == 0:
            c //= p; q *= p
        out.append((p, q))
    return out


def divisor_count_upto(N):
    d = np.zeros(N + 1, dtype=np.int64)
    for k in range(1, N + 1):
        d[k::k] += 1
    return d


# ------------------------------------------------------------------------------------------- Kloosterman tables
def kloost_table(q, p, prec=96):
    """Rigorous table of S(1,j;q), j = 0..q-1, for a prime power q = p^k.
    Returns (mid: float64 array, err: float) with |S(1,j;q) - mid[j]| <= err for all j."""
    if q == 1:
        return np.ones(1), 0.0
    ctx.prec = prec
    # roots of unity R[k] = e(k/q) via repeated multiplication from e(1/q) (rigorous balls)
    zeta = acb(arb(2) / q).exp_pi_i()
    R = [acb(1)] * q
    cur = acb(1)
    for k in range(1, q):
        cur = cur * zeta
        R[k] = cur
    x = [acb(0)] * q
    for d in range(1, q):
        if d % p:
            x[d] = R[pow(d, -1, q)]                 # e(dbar/q)
    y = acb.dft(x)                                  # y_j = sum_d x_d e(-j d/q) = S(1,-j;q)
    mid = np.empty(q)
    err = 0.0
    for j in range(q):
        re = y[(-j) % q].real                       # S(1,j;q) is real; imaginary part ignored (it is 0)
        m = float(re.mid())
        mid[j] = m
        e = float(re.rad()) + abs(m) * 2.0 ** -52 + abs(float(re.mid()) - m)
        if e > err:
            err = e
    # inflate slightly to absorb the float evaluation of the bound itself
    return mid, err * 1.001 + 1e-300


def build_tables(X, prec=96, verbose=False):
    """tables for all prime powers q <= X.  Returns dict q -> (mid, err), and spf sieve."""
    import time
    spf = spf_sieve(X)
    tabs = {}
    t0 = time.time()
    for p in range(2, X + 1):
        if spf[p] != p:
            continue
        q = p
        while q <= X:
            tabs[q] = kloost_table(q, p, prec)
            q *= p
        if verbose and p > 1000 and (p < 1100 or p % 997 == 0):
            print('   tables up to p=%d  (%.0fs)' % (p, time.time() - t0), flush=True)
    return tabs, spf


def kloost_pm(ns, c, tabs, spf, prec=96):
    """lists of arb balls S(1,n;c), S(-1,n;c) for n in ns (Python ints)."""
    ctx.prec = prec
    if c == 1:
        return [arb(1)] * len(ns), [arb(1)] * len(ns)
    fac = factor_pp(c, spf)
    Sp = [arb(1)] * len(ns); Sm = [arb(1)] * len(ns)
    for (p, q) in fac:
        mid, err = tabs[q]
        r = c // q
        m = pow(r, -2, q) if q > 1 else 0
        for i, n in enumerate(ns):
            jp = (n * m) % q; jm = (-n * m) % q
            Sp[i] = Sp[i] * arb(mid[jp], err)
            Sm[i] = Sm[i] * arb(mid[jm], err)
    return Sp, Sm


def kloost_brute(m, n, c, prec=96):
    """rigorous S(m,n;c) by direct summation (small c only)."""
    ctx.prec = prec
    s = arb(0)
    for d in range(c):
        if math.gcd(d, c) == 1:
            db = pow(d, -1, c) if c > 1 else 0
            s += (arb(2) * ((m * db + n * d) % c) / c).cos_pi()
    return s


# ------------------------------------------------------------------------------------------- rigorous tails
def small_z_majorant_coeffs(wX, prec=96):
    """For 0 < z with w = (z/2)^2 <= wX (and z < 2):
         |Ihat(z)|, |Jhat(z)| <= B(z) := (w/2) [ (log(2/z) + psi(3)) (1 + (w/3) e^w) + (w/9)(1+w) e^w ]
       (the small-argument bound for Ihat, Jhat, proved in the paper);
       returns (alpha, gam) with B(z) <= (w/2) [ alpha (log(2/z) + psi(3)) + gam ] for all w <= wX."""
    ctx.prec = prec
    wX = arb(wX)
    alpha = 1 + wX / 3 * wX.exp()
    gam = wX / 9 * (1 + wX) * wX.exp()
    return alpha, gam


def _I_j(X, j, s):
    """int_X^oo u^{-s-1} (log u)^j du, j = 0,1,2 (exact closed forms), X, s arb."""
    L = X.log()
    if j == 0:
        return X ** (-s) / s
    if j == 1:
        return X ** (-s) * (L / s + 1 / s ** 2)
    if j == 2:
        return X ** (-s) * (L ** 2 / s + 2 * L / s ** 2 + 2 / s ** 3)
    raise ValueError


def weil_tail(n, X, prec=96):
    """Rigorous upper bound for  sum_{c > X} c^{-1} |S(1,n;c) Jhat(z_c) - S(-1,n;c) Ihat(z_c)|,  z_c = 4 pi sqrt(n)/c,
    using Weil |S| <= d(c) sqrt(c), the small-z majorant B, D(u) = sum_{c<=u} d(c) <= u (1 + log u), and
    partial summation.  Requires z_X <= 1 (i.e. X >= 4 pi sqrt n).  Returns arb (upper bound as exact-ish ball)."""
    ctx.prec = prec
    X = arb(X); n = arb(n)
    zX = 4 * arb.pi() * n.sqrt() / X
    assert zX.upper() <= 1, 'weil_tail needs X >= 4 pi sqrt(n)'
    wX = zX * zX / 4
    alpha, gam = small_z_majorant_coeffs(wX, prec)
    psi3 = _psi_int(3, prec)
    # B(z_c) <= (w_c/2)[alpha (log c - log(2 pi sqrt n) + psi3) + gam],  w_c/2 = 2 pi^2 n / c^2
    # |term_c| <= d(c) c^{-1/2} * 2 B(z_c) = 4 pi^2 n d(c) c^{-5/2} [alpha log c + beta]
    beta = alpha * (psi3 - (2 * arb.pi() * n.sqrt()).log()) + gam
    # f(u) = u^{-5/2}(alpha log u + beta) must be decreasing & positive on [X, oo): need alpha log X + beta >= 2 alpha/5
    assert (alpha * X.log() + beta - 2 * alpha / 5).lower() > 0
    s = arb(3) / 2
    fX = X ** arb(-2.5) * (alpha * X.log() + beta)
    gX = X * (X.log() + 1)
    # sum_{c>X} d(c) f(c) <= g(X) f(X) + int_X^oo (log u + 2) f(u) du
    integ = alpha * _I_j(X, 2, s) + (beta + 2 * alpha) * _I_j(X, 1, s) + 2 * beta * _I_j(X, 0, s)
    tot = 4 * arb.pi() ** 2 * n * (gX * fX + integ)
    return arb(tot.upper())                            # exact upper bound value


def trivial_tail(n, X, prec=96):
    """Same with the trivial bound |S| <= phi(c) <= c (no Weil): sum_{c>X} 2B(z_c) <= 4 pi^2 n int_X^oo u^{-2}(alpha log u + beta) du
    (f decreasing => sum_{c>X} f(c) <= int_X^oo f)."""
    ctx.prec = prec
    X = arb(X); n = arb(n)
    zX = 4 * arb.pi() * n.sqrt() / X
    assert zX.upper() <= 1
    wX = zX * zX / 4
    alpha, gam = small_z_majorant_coeffs(wX, prec)
    psi3 = _psi_int(3, prec)
    beta = alpha * (psi3 - (2 * arb.pi() * n.sqrt()).log()) + gam
    assert (alpha * X.log() + beta - alpha / 2).lower() > 0      # u^{-2}(alpha log u + beta) decreasing
    s = arb(1)
    tot = 4 * arb.pi() ** 2 * n * (alpha * _I_j(X, 1, s) + beta * _I_j(X, 0, s))
    return arb(tot.upper())


def term_c(n, c, Sp, Sm, prec=96):
    """c^{-1} [S(1,n;c) Jhat(z) - S(-1,n;c) Ihat(z)], z = 4 pi sqrt(n)/c (arb)."""
    ctx.prec = prec
    z = 4 * arb.pi() * arb(n).sqrt() / c
    I, J = hats(z, prec)
    ctx.prec = prec
    return (Sp * J - Sm * I) / c


def c1_term(n, prec=256):
    """Jhat(4 pi sqrt n) - Ihat(4 pi sqrt n) (the c = 1 term of Kc_n), rigorous."""
    ctx.prec = prec
    z = 4 * arb.pi() * arb(n).sqrt()
    I, J = hats(z, prec)
    ctx.prec = prec
    return J - I


def arb_str(x, digits=25):
    return x.str(digits, radius=True)


# ------------------------------------------------------------------------------------------- tight K0, K1 (Part I library)
_ANC = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))     # the top directory (lib/ = Part I library)
if _ANC not in sys.path:
    sys.path.insert(0, _ANC)
from lib.besselk import K01 as _K01_paper1     # rigorous K_0, K_1 for real z > 0 (series / asymptotic with DLMF 10.40(ii) bound)


def K01(z, prec=128):
    """Rigorous, TIGHT balls for (K_0(z), K_1(z)), z > 0 (arb's own bessel_k can return loose balls; see Part I's library)."""
    k0, k1 = _K01_paper1(arb(z), prec)
    ctx.prec = prec
    return k0, k1


def weil_tail_alpha(n, X, prec=96):
    """Rigorous upper bound for sum_{c>X} c^{-1}|S(1,n;c) J_2(z_c) - S(-1,n;c) I_2(z_c)|, z_c = 4 pi sqrt(n)/c, X >= 4 pi sqrt n.
    For w = z_c <= 1 (v = w^2/4): |J_2(w)|, I_2(w) <= (v/2)(1 + (v/3)e^v)  [series, 2/(k!(k+2)!) <= 1/(3(k-1)!)].
    => term_c <= d(c) c^{-1/2} * 2 (2 pi^2 n/c^2) (1 + (vX/3) e^vX) ; partial summation with D(u) <= u(1+log u).
    (alpha_n = 2 * Kloosterman-Bessel sum, so the tail of alpha_n is 2 * this.)"""
    ctx.prec = prec
    X = arb(X); n = arb(n)
    zX = 4 * arb.pi() * n.sqrt() / X
    assert zX.upper() <= 1
    vX = zX * zX / 4
    kap = 1 + vX / 3 * vX.exp()
    s = arb(3) / 2
    # sum_{c>X} d(c) c^{-5/2} <= X(log X + 1) X^{-5/2} + int_X^oo (log u + 2) u^{-5/2} du
    S = X * (X.log() + 1) * X ** arb(-2.5) + _I_j(X, 1, s) + 2 * _I_j(X, 0, s)
    tot = 4 * arb.pi() ** 2 * n * kap * S
    return arb(tot.upper())


def save_tables(tabs, fn):
    qs = sorted(tabs)
    offs = np.cumsum([0] + [len(tabs[q][0]) for q in qs])
    np.savez(fn, qs=np.array(qs), offs=offs, mids=np.concatenate([tabs[q][0] for q in qs]),
             errs=np.array([tabs[q][1] for q in qs]))


def load_tables(fn):
    d = np.load(fn)
    qs, offs, mids, errs = d['qs'], d['offs'], d['mids'], d['errs']     # read each array ONCE
    tabs = {}
    for i, q in enumerate(qs):
        tabs[int(q)] = (mids[offs[i]:offs[i + 1]], float(errs[i]))
    X = int(max(tabs))
    return tabs
