"""Arithmetic check (Arb) of the explicit constants of Theorems 6.1-6.2 of the paper (the fully analytic proof of
Kc_n > 0, hence a_n > 0 and b_n = C a_n of the sign of C, for every n; and (1 - 2/z_n) A0(n) <= a_n <= A0(n)), and of the
constants of the bound for the coefficients alpha_n = a_n(1) at nu = 1 (proved in the paper).  The paper writes S_n for
Kc_n, A_n(1) for alpha_n, and lambda_0, varrho, lambda_-, lambda_+ for lambda, rho, Lambda, Upsilon below.

Notation: z = 4 pi sqrt(n) >= 4 pi,  E(w) = e^w / sqrt(2 pi w),  G(z) := (2/z) E(z)   (so n G(z_n) = A0(n)).
  lambda(z) = (1 - 1/z)(1 - 3/(8z) - 15/(32 z^2)) - (pi^3/16)/z^2                      [-Ihat(z) >= G lambda for z >= 1]
  rho(z)    = sum of the five majorant pieces of |R_n| / G(z)    [R_n = the terms c >= 2 of Kc_n; |R_n| <= G rho]
      r1 = (pi+2) z / (8 E(z))           (c = 2, Jhat and 2/w^2 parts)
      r2 = sqrt(2) e^{-z/2}              (c = 2, I part)
      r3 = (pi+2) z^2 / (8 E(z))         (3 <= c <= z/2, constant parts)
      r4 = (z^2/4) sqrt(3) e^{-2z/3}     (3 <= c <= z/2, I part)
      r5 = [k3 + (z/2)(k1 + k3)] z / (2 E(z))   (c > z/2, small-w majorant B; k1 = 1 + e/3, k3 = k1 psi(3) + 2e/9)
  Lambda(z) = lambda(z) - (pi+1) z/(4 E(z)) - rho(z)                                    [Kc_n >= G Lambda]
  Upsilon(z) = 1 - 1/z + (2/z^2 + (pi+1)/2) z/(2E(z)) + rho(z)                         [Kc_n <= G Upsilon]
All bounds in brackets are proved in the paper.
Monotonicity facts used (elementary; proved in the paper): lambda increasing on z >= 1; each r_i and z*r_i decreasing on
z >= 4 pi; hence Lambda increasing and z(Upsilon - 1 + 1/z) decreasing on [4 pi, oo).  They are spot-checked here on a grid
(sanity only, lines marked [not a certificate]; the proofs are the one-line derivative computations in the paper).
"""
import os, sys, hashlib
from flint import arb, ctx
ctx.prec = 128
pi = arb.pi()
e = arb(1).exp()
psi3 = arb(3) / 2 - arb.const_euler()
k1 = 1 + e / 3
k2 = 2 * e / 9
k3 = k1 * psi3 + k2


def E(w):
    return w.exp() / (2 * pi * w).sqrt()


def lam(z):
    return (1 - 1 / z) * (1 - arb(3) / (8 * z) - arb(15) / (32 * z ** 2)) - pi ** 3 / 16 / z ** 2


def parts(z):
    r1 = (pi + 2) * z / (8 * E(z))
    r2 = arb(2).sqrt() * (-z / 2).exp()
    r3 = (pi + 2) * z ** 2 / (8 * E(z))
    r4 = z ** 2 / 4 * arb(3).sqrt() * (-2 * z / 3).exp()
    r5 = (k3 + z / 2 * (k1 + k3)) * z / (2 * E(z))
    return r1, r2, r3, r4, r5


def Lam(z):
    return lam(z) - (pi + 1) * z / (4 * E(z)) - sum(parts(z))


def Ups(z):
    return 1 - 1 / z + (2 / z ** 2 + (pi + 1) / 2) * z / (2 * E(z)) + sum(parts(z))


print('analytic_constants.py  sha256 %s' % hashlib.sha256(open(os.path.abspath(__file__), 'rb').read()).hexdigest()[:16])
print('k1 = 1+e/3 = %s ; k2 = 2e/9 = %s ; k3 = %s' % (k1.str(10), k2.str(10), k3.str(10)))
z0 = 4 * pi
print('z0 = 4 pi = %s ; E(z0) = %s ; G(z0) = (2/z0)E(z0) = %s' % (z0.str(15), E(z0).str(15), (2 / z0 * E(z0)).str(15)))
print('lambda(4pi) = %s' % lam(z0).str(15))
for name, r in zip(('r1', 'r2', 'r3', 'r4', 'r5'), parts(z0)):
    print('  %s(4pi) = %s' % (name, r.str(8)))
rho0 = sum(parts(z0))
print('rho(4pi) = %s' % rho0.str(10))
print('DECISIVE: Lambda(4pi) = %s  (> 0 required; Kc_n >= Lambda(z_n) G(z_n) for all n)' % Lam(z0).str(12))
print('DECISIVE: Upsilon(4pi) = %s ; 4pi*(Upsilon - 1 + 1/z)(4pi) = %s  (< 1 required => a_n <= A0(n) for all n)'
      % (Ups(z0).str(12), (z0 * (Ups(z0) - 1 + 1 / z0)).str(12)))
# lower bound a_n >= (1 - 2/z) A0(n):  need z(Lambda - 1 + 2/z) >= 0 ; = z(lambda - 1 + 2/z) - z*(decaying)
zl = z0 * (lam(z0) - 1 + 2 / z0)
zd = z0 * ((pi + 1) * z0 / (4 * E(z0)) + rho0)
print('DECISIVE: at 4pi: z(lambda - 1 + 2/z) = %s (increasing in z) ; z*(decaying part) = %s (decreasing) ; difference %s (> 0 required)'
      % (zl.str(10), zd.str(10), (zl - zd).str(10)))
# a_1 check: a_1 <= A0(1) Upsilon(4pi) + 1/4 <= A0(1)
A01 = (2 / z0) * E(z0)
print('A0(1) = %s ; A0(1) Upsilon(4pi) + 1/4 = %s' % (A01.str(12), (A01 * Ups(z0) + arb(1) / 4).str(12)))
# grid sanity (not a proof step): monotonicity of Lambda and z(Upsilon - 1 + 1/z), z(Lambda - 1 + 2/z)
prev = None; ok = True
zs = [z0 * (1 + arb(k) / 40) for k in range(0, 4001)]
L_prev = None; U_prev = None; W_prev = None
for z in zs:
    L = Lam(z); U = z * (Ups(z) - 1 + 1 / z); W = z * (Lam(z) - 1 + 2 / z)
    if L_prev is not None:
        if not (L > L_prev - arb(1e-30)): ok = False
        if not (U < U_prev + arb(1e-30)): ok = False
    if not (W > 0): ok = False
    L_prev, U_prev, W_prev = L, U, W
print('[not a certificate] grid z in [4pi, 404pi] (4001 pts): Lambda increasing, z(Upsilon-1+1/z) decreasing, z(Lambda-1+2/z) > 0: %s' % ok)
print('[not a certificate] Lambda(z) at z = 4pi*sqrt(n), n = 1,2,4,10,100: %s' % ', '.join(Lam(4 * pi * arb(n).sqrt()).str(6) for n in (1, 2, 4, 10, 100)))

# ---------------------------------------------------------------- §alpha: the coefficients alpha_n = a_n(1) at nu = 1 (A_n(1) in the paper; bound proved in the paper)
# |J2| <= 1 ; I2(w) <= E(w)(1 + (pi^3/16)/w) ; for w >= 2: |J2| + I2 <= 1 + E(w)(1 + pi^3/32) ; w < 2: |J2| + I2 <= kappa1 w^2/4
# rho_alpha(z) = [ (1/2)(1 + c2 E(z/2)) + (z/2)(1 + c2 E(z/3)) + kappa1 (1 + z/2) ] / E(z),  c2 = 1 + pi^3/32
c2 = 1 + pi ** 3 / 32
def rho_alpha(z):
    return (arb(1) / 2 * (1 + c2 * E(z / 2)) + z / 2 * (1 + c2 * E(z / 3)) + k1 * (1 + z / 2)) / E(z)
def alpha_upper_factor(z):     # |alpha_n| <= 2 E(z) * this
    return 1 + pi ** 3 / 16 / z + 1 / E(z) + rho_alpha(z)
def alpha_lower_factor(z):     # -alpha_n >= 2 E(z) * this
    return (1 - 2 / z) * (1 - arb(3) / (8 * z) - arb(15) / (32 * z ** 2)) - 1 / E(z) - rho_alpha(z)
print('§alpha: rho_alpha(4pi) = %s ; |alpha_n| <= 2E(z_n) * %s ; -alpha_n >= 2E(z_n) * %s  (at n = 1; upper factor decreasing, lower increasing in z)'
      % (rho_alpha(z0).str(8), alpha_upper_factor(z0).str(8), alpha_lower_factor(z0).str(8)))
ok = True
prevU = None; prevL = None
for z in zs:
    U = alpha_upper_factor(z); L = alpha_lower_factor(z)
    if prevU is not None and not (U < prevU + arb(1e-30) and L > prevL - arb(1e-30)):
        ok = False
    prevU, prevL = U, L
print('[not a certificate] grid: alpha upper factor decreasing and lower factor increasing on [4pi, 404pi]: %s' % ok)

# ---------------------------------------------------------------- §Jhat-large: decaying bound for |Jhat(x)|, x >= 2 (informational only; not used by the paper or the certificates)
# Watson §13.74 (from Nicholson's formula): x (J_nu^2 + Y_nu^2)(x) is decreasing for nu > 1/2, increasing for nu < 1/2 (limit 2/pi).
# => |J_0(x)| <= sqrt(2/(pi x)) ; |J_1(x)|^2 <= (J_1^2+Y_1^2)(x) <= 2 M1sq/x ; |Y_2(x)|^2 <= 2 M2sq/x  (x >= 2),
#    M_nu sq := (J_nu^2 + Y_nu^2)(2) (upper endpoints).  Jhat = (pi/2) Y_2 + 2 J_0/x^2 + 2 J_1/x.
x0 = arb(2)
M1sq = x0.bessel_j(1) ** 2 + x0.bessel_y(1) ** 2
M2sq = x0.bessel_j(2) ** 2 + x0.bessel_y(2) ** 2
cY = pi / 2 * (2 * M2sq).sqrt(); cJ0 = 2 * (2 / pi).sqrt(); cJ1 = 2 * (2 * M1sq).sqrt()
print("§Jhat-large: for x >= 2, |Jhat(x)| <= %s x^{-1/2} + %s x^{-3/2} + %s x^{-5/2}" % (cY.str(6), cJ1.str(6), cJ0.str(6)))
ok = True
for k in range(0, 400):
    x = arb(2) + arb(k) / 4
    J = pi / 2 * x.bessel_y(2) + 2 * x.bessel_j(0) / x ** 2 + 2 * x.bessel_j(1) / x
    bnd = cY / x.sqrt() + cJ1 / x ** arb(1.5) + cJ0 / x ** arb(2.5)
    if not (abs(J) < bnd):
        ok = False
    for nu, inc in ((0, True), (1, False), (2, False)):
        xm = x * (x.bessel_j(nu) ** 2 + x.bessel_y(nu) ** 2)
        xm2 = (x + arb(1) / 4) * ((x + arb(1) / 4).bessel_j(nu) ** 2 + (x + arb(1) / 4).bessel_y(nu) ** 2)
        if inc and not (xm2 > xm - arb(1e-25)): ok = False
        if (not inc) and not (xm2 < xm + arb(1e-25)): ok = False
print('[not a certificate] grid x in [2, 102]: bound holds and x M_nu^2 monotone as stated (nu=0 incr., nu=1,2 decr.): %s' % ok)
