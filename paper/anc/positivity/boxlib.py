"""The trivial-bound box of the coefficients a_n (Section 6.1 of the paper), in Arb at the current precision.

a_n = n S_n + delta_{n1}/4, and S_n = T1(z_n) + R_n with z_n = 4 pi sqrt(n), where T1(z) = Jdot_2(z) - Idot_2(z) is the term
c = 1 of S_n (S(+-1, n; 1) = 1).  The proof of Theorem 6.1 of the paper bounds the terms c >= 2 with the trivial bound
|S(+-1, n; c)| <= phi(c) only:  n |R_n| <= abar_n varrho(z_n).  Hence

    |a_n - c_n| <= w_n,    c_n := n T1(z_n) + delta_{n1}/4,    w_n := abar_n varrho(z_n),

with abar_n = n (2/z_n) ee(z_n) = n^{1/4} e^{4 pi sqrt n}/(4 sqrt2 pi^2), ee(w) = e^w/sqrt(2 pi w), and varrho the function of
Section 6.1 of the paper.  The set of real sequences (b_n) with |b_n - c_n| <= w_n for every n is the trivial-bound box.
By the proofs of Theorems 6.1 and 6.2, every element of the box satisfies 0 < (1 - 2/z_n) abar_n <= b_n <= abar_n.

The values T1(z_n) are read from the key 'T1' of coefficients/data/an_cert_X1e4.json, where they are stored as printed Arb
balls '[mid +/- rad]' (computed at 256 bits); the printed radius is kept and doubled.  They involve no Kloosterman sum.
Every function evaluates pi at the current working precision."""
from flint import arb


def ee(w):
    return w.exp() / (2 * arb.pi() * w).sqrt()


def varrho(z):
    """The function varrho of Section 6.1 of the paper: |c >= 2 part of S_n| <= (2/z) ee(z) varrho(z), z = z_n."""
    PI = arb.pi()
    k1 = 1 + arb(1).exp() / 3; k2 = 2 * arb(1).exp() / 9
    psi3 = arb(1.5) - arb.const_euler(); k3 = k1 * psi3 + k2
    e = ee(z)
    return ((PI + 2) * z / (8 * e) + arb(2).sqrt() * (-z / 2).exp() + (PI + 2) * z ** 2 / (8 * e)
            + arb(3).sqrt() * z ** 2 / 4 * (-2 * z / 3).exp() + (k3 + z / 2 * (k1 + k3)) * z / (2 * e))


def abar(n):
    PI = arb.pi()
    n = arb(n)
    return n ** arb(0.25) * (4 * PI * n.sqrt()).exp() / (4 * arb(2).sqrt() * PI ** 2)


def T1_ball(s):
    """The stored c = 1 term '[mid +/- rad]' as an Arb ball (printed radius kept and doubled)."""
    mid, rad = s.strip('[] ').split('+/-')
    return arb(mid.strip(), float(rad) * 2)


def centre_halfwidth(n, T1str):
    """(c_n, w_n) as Arb balls."""
    PI = arb.pi()
    c = n * T1_ball(T1str) + (arb(1) / 4 if n == 1 else 0)
    w = abar(n) * varrho(4 * PI * arb(n).sqrt())
    return c, w


def box_hull(n, T1str):
    """A ball containing [c_n - w_n, c_n + w_n]."""
    c, w = centre_halfwidth(n, T1str)
    return arb((c - w).lower()).union(arb((c + w).upper()))
