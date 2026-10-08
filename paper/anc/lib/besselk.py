"""Rigorous enclosures of the modified Bessel functions K_0(z), K_1(z) for real z > 0.

Arb ball arithmetic (python-flint).  Arb's own bessel_k / hypgeom_u are deliberately NOT used: for z of
moderate size their enclosures can lose about e^{2z} in relative accuracy, and the slow fallback path can stall.

Small and moderate z: the convergent power series (DLMF 10.31.2 and 10.31.1 with n = 1), q = z^2/4,
    I_0 = sum_k q^k/(k!)^2,                    K_0 = -(log(z/2) + gamma) I_0 + sum_{k>=1} H_k q^k/(k!)^2,
    I_1 = (z/2) sum_k q^k/(k!(k+1)!),          K_1 = 1/z + log(z/2) I_1 - (z/4) sum_k (psi(k+1)+psi(k+2)) q^k/(k!(k+1)!),
with H_k the harmonic numbers and psi(k+1) + psi(k+2) = H_k + H_{k+1} - 2 gamma.  The cancellation between the
growing I-parts and the decaying K is about e^{2z}, so the series is summed at working precision
P + 2.885 z + 64 (+2%) bits.  Truncation: the loop stops at an index k with 4q <= (k+1)^2 and the last terms below
2^-wp relative; from there on every term ratio is <= 1/2 (term ratios q/(k+1)^2 <= 1/4 times coefficient ratios
H_{k+1}/H_k <= 2), so each remaining tail is at most the last term; twice the last term is added as a ball radius.

Large z: the asymptotic expansion (DLMF 10.40.2)
    K_nu(z) = sqrt(pi/(2z)) e^{-z} [ sum_{k<l} a_k(nu) z^{-k} + R_l ],
    a_k(nu) = prod_{j=1..k} (4 nu^2 - (2j-1)^2) / (k! 8^k),
with the error bound of DLMF 10.40(ii): for real z > 0, real nu and l >= |nu| - 1/2, |R_l| <= |a_l(nu)| z^{-l}.
It is used when this bound reaches 2^-(P+20); otherwise the series is used.

Ball arguments: K is evaluated at the exact midpoint m of the ball z = [m +/- r] and the radius is propagated
analytically (feeding a ball into the e^{2z}-cancelling series would inflate the radius by about e^{2z} r):
    |K_0(z) - K_0(m)| <= r max K_1 <= r K_1(m) e^{r(1 + 1/(m-r))},
    |K_1(z) - K_1(m)| <= r max (K_0 + K_1/w) <= r K_1(m-r) (1 + 1/(m-r)),
using K_0' = -K_1, K_1' = -K_0 - K_1/w, 0 < K_0 <= K_1 and (log K_1)' >= -1 - 1/w.
"""
from flint import arb, ctx
from .common import require


def _series(z, wp):
    ctx.prec = wp
    q = z * z / 4
    g = arb.const_euler()
    lz = (z / 2).log()
    t = arb(1); I0 = arb(1); S0 = arb(0); H = arb(0)          # K_0 pieces
    u = arb(1); I1s = arb(1); T1 = (1 - 2 * g) * u           # K_1 pieces; psi(1) + psi(2) = 1 - 2 gamma
    k = 0
    while True:
        k += 1
        t = t * q / (k * k)
        H = H + arb(1) / k
        I0 += t
        S0 += H * t
        u = u * q / (k * (k + 1))
        c = 2 * H + arb(1) / (k + 1) - 2 * g                  # psi(k+1) + psi(k+2)
        I1s += u
        T1 += c * u
        if (4 * q <= (k + 1) * (k + 1) and abs(t) * (1 + H) < abs(I0) * arb(2) ** (-wp)
                and abs(c * u) < abs(I1s) * arb(2) ** (-wp)):
            break
    tail0 = 2 * abs(t) * (1 + H)
    tail1 = 2 * abs(c * u) + 2 * abs(u)
    I0 += arb(0, tail0.upper()); S0 += arb(0, tail0.upper())
    I1s += arb(0, tail1.upper()); T1 += arb(0, tail1.upper())
    K0 = -(lz + g) * I0 + S0
    K1 = 1 / z + lz * (z / 2) * I1s - (z / 4) * T1
    return K0, K1


def _asymptotic(z, nu, P):
    """Asymptotic series with rigorous remainder; None if the bound cannot reach 2^-(P+20)."""
    s = arb(1); term = arb(1); k = 0
    tol = arb(2) ** (-(P + 20))
    mu = 4 * nu * nu
    while True:
        k += 1
        nt = term * (mu - (2 * k - 1) ** 2) / (k * 8 * z)
        if abs(nt) < tol:
            s += arb(0, abs(nt).upper())                     # |R_k| <= |a_k| z^-k  (k >= 1 >= |nu| - 1/2)
            break
        if abs(nt) >= abs(term) and k > 2:
            return None
        s += nt
        term = nt
        if k > 20000:
            return None
    return (arb.pi() / (2 * z)).sqrt() * (-z).exp() * s


def _K01_point(m, P):
    zf = float(m.mid())
    if zf > 0.35 * (P + 40) + 5:
        ctx.prec = P + 64
        a0 = _asymptotic(m, 0, P)
        a1 = _asymptotic(m, 1, P)
        if a0 is not None and a1 is not None:
            return a0, a1
    return _series(m, P + int(2.885 * zf) + 64 + int(P * 0.02))


def K01(z, P):
    """Balls containing K_0(z) and K_1(z) for every z in the (positive) ball z; target accuracy about 2^-P relative."""
    old = ctx.prec
    try:
        m = arb(z.mid())
        r = arb(z.rad())
        K0, K1 = _K01_point(m, P)
        if r != 0:
            ctx.prec = P + 64
            ml = m - r
            require(ml > 0, 'K01: the ball argument must lie in (0, oo)')
            K1l = abs(K1).upper() * (r * (1 + 1 / ml)).exp()       # >= K_1 on [m - r, m]
            K0 = K0 + arb(0, (r * K1l).upper())
            K1 = K1 + arb(0, (r * K1l * (1 + 1 / ml)).upper())
        ctx.prec = P + 64
        return +K0, +K1
    finally:
        ctx.prec = old


def K32_upper(z):
    """K_{3/2}(z) = sqrt(pi/(2z)) e^{-z} (1 + 1/z), an upper bound for K_0(z) <= K_1(z) (z > 0)."""
    return (arb.pi() / (2 * z)).sqrt() * (-z).exp() * (1 + 1 / z)
