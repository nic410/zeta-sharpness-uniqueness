"""Rigorous Kloosterman sums S(1,j;q) for LARGE prime powers q and a FEW j, in float64 with a PROVED error bound.

S(1,j;q) = sum_{d mod q, (d,q)=1} cos(2 pi (dbar + j d)/q)       (real; the sine parts cancel under d -> -d)

  * residues r_d = (dbar + j d) mod q are computed EXACTLY in int64 (q^2 < 2^62);
  * dbar for all units d: exact, via powers of a generator of (Z/q)^* (odd p) or Python pow (p = 2);
  * the table C[k] ~ cos(2 pi k/q), k = 0..q-1, is computed by cos_table_rig() below with |C[k] - cos(2 pi k/q)| <= EPS_TAB;
  * S_hat = numpy.sum(C[r]) ; for ANY summation order, |fl(sum x_i) - sum x_i| <= gamma_{m-1} sum|x_i|,
    gamma_k = k u/(1 - k u), u = 2^-53 (Higham, Accuracy and Stability, 2nd ed., Lemma 3.1 / eq. (4.4)).
    Hence |S_hat - S| <= m EPS_TAB + gamma_{m-1} m (1 + EPS_TAB),  m = phi(q).

cos_table_rig(q): exact integer octant reduction k -> (N, D, f, sign) with cos(2 pi k/q) = sign * f(pi N/D), 0 <= pi N/D <= pi/4,
f in {cos, sin}; x = fl(fl(pi) * fl(N/D)); |x - pi N/D| <= 3.1e-16 (two roundings + |fl(pi) - pi| <= 1.23e-16);
Taylor polynomials of degree 22 (cos) / 23 (sin) by Horner in y = x^2: truncation <= (pi/4)^24/24! < 1e-25;
Horner rounding <= gamma_{2*12} * cosh(pi/4) + coefficient rounding u*cosh(pi/4) < 4.0e-15 (Higham Eq. (5.3));
total < 4.5e-15.  We use EPS_TAB = 1e-14.
All of this uses only IEEE-754 binary64 +,-,*,/ with round-to-nearest (numpy), no libm.
"""
import math
import numpy as np

U = 2.0 ** -53
EPS_TAB = 1e-14
PI_HI = 3.141592653589793          # fl(pi); |fl(pi) - pi| <= 1.23e-16
_C_COS = [(-1) ** i / math.factorial(2 * i) for i in range(12)]          # degree 22 in x
_C_SIN = [(-1) ** i / math.factorial(2 * i + 1) for i in range(12)]      # degree 23 in x


def _horner(coefs, y):
    acc = np.full_like(y, coefs[-1])
    for c in reversed(coefs[:-1]):
        acc = acc * y + c
    return acc


def cos_table_rig(q):
    """float64 array C with |C[k] - cos(2 pi k / q)| <= EPS_TAB for k = 0..q-1 (proof in module docstring)."""
    k = np.arange(q, dtype=np.int64)
    m = np.minimum(k, q - k)                      # cos(2 pi k/q) = cos(2 pi m/q), 0 <= m <= q/2
    out = np.empty(q)
    e8 = 8 * m
    # case A: 8m <= q          : cos(pi*(2m)/q)
    # case B: q < 8m <= 2q      : sin(pi*(q-4m)/(2q))
    # case C: 2q < 8m <= 3q     : -sin(pi*(4m-q)/(2q))
    # case D: 3q < 8m (<= 4q)   : -cos(pi*(q-2m)/q)
    A = e8 <= q; B = (e8 > q) & (e8 <= 2 * q); Cc = (e8 > 2 * q) & (e8 <= 3 * q); Dd = e8 > 3 * q
    for mask, num, den, f, sg in ((A, 2 * m, q, 'c', 1.0), (B, q - 4 * m, 2 * q, 's', 1.0),
                                  (Cc, 4 * m - q, 2 * q, 's', -1.0), (Dd, q - 2 * m, q, 'c', -1.0)):
        if not mask.any():
            continue
        N = num[mask].astype(np.float64); Dn = np.float64(den)        # exact (integers < 2^53)
        x = PI_HI * (N / Dn)
        y = x * x
        if f == 'c':
            v = _horner(_C_COS, y)
        else:
            v = x * _horner(_C_SIN, y)
        out[mask] = sg * v
    return out


def gamma(k):
    return k * U / (1 - k * U)


def unit_inverses(q, p):
    """(d, dbar) arrays over the units d mod q (q = p^k), exact int64."""
    if p == 2:
        ds = np.arange(1, q, 2, dtype=np.int64)
        inv = np.array([pow(int(d), -1, q) for d in ds], dtype=np.int64)
        return ds, inv
    phi = q // p * (p - 1)
    # generator of (Z/p^k)^*: primitive root mod p that is also one mod p^2
    fs = []
    t = p - 1; f = 2
    while f * f <= t:
        if t % f == 0:
            fs.append(f)
            while t % f == 0:
                t //= f
        f += 1
    if t > 1:
        fs.append(t)
    g = 2
    while True:
        if all(pow(g, (p - 1) // f, p) != 1 for f in fs) and (q == p or pow(g, p - 1, p * p) != 1):
            break
        g += 1
    B = int(math.isqrt(phi)) + 1
    small = np.empty(B, dtype=np.int64); v = 1
    for i in range(B):
        small[i] = v; v = (v * g) % q
    gB = v
    nb = phi // B + 1
    big = np.empty(nb, dtype=np.int64); v = 1
    for i in range(nb):
        big[i] = v; v = (v * gB) % q
    pw = ((big[:, None] * small[None, :]) % q).ravel()[:phi]       # pw[i] = g^i mod q (exact)
    inv = np.empty(phi, dtype=np.int64)
    inv[0] = 1
    inv[1:] = pw[::-1][:phi - 1]                                     # g^{-i} = g^{phi - i}
    return pw, inv


class PrimePowerKloost:
    """Rigorous S(1,j;q) for one prime power q, many j: value and error bound."""

    def __init__(self, q, p):
        self.q = q
        self.d, self.dbar = unit_inverses(q, p)
        self.C = cos_table_rig(q)
        m = len(self.d)
        self.err = m * EPS_TAB + gamma(max(m - 1, 1)) * m * (1 + EPS_TAB)
        self.err *= 1.0001                     # absorb rounding in the evaluation of the bound itself

    def S(self, j):
        r = (self.dbar + (j % self.q) * self.d) % self.q
        return float(np.sum(self.C[r])), self.err
