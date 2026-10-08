"""Figure 1 of the paper (an illustration, NOT a certificate).

(a) H(t) on [0, 40], log scale:
    - the curve joins H(0) = 1 and the values H(t_c) at the 80 cell centres of certificate W, computed from the quadrature
      values R(t_c) printed in positivity/out/window_0_40.json (no error terms) as H = R(t)/(16 (t^2+1/4)^2 R(0));
    - the steps are lower bounds for H on each cell, formed from the certified cell lower bounds of the same file and the
      upper end of the certified enclosure of R(0) (Theorem 7.10; positivity/logs/check_r0.log), with (t^2+1/4)^2 taken at
      the right end of the cell;
    - the dashed line is the bound of Theorem 7.4, R(t) >= 0.2554 e^{0.6435 t} for t >= 8, converted in the same way.
(b) e^{4 pi sqrt x} Ghat_H(x) / 10^6 on 1 <= x <= 6, where Ghat_H(x) = C sin^2(pi x) sqrt(x) sum_n a_n K_0(4 pi sqrt(n x))
    (Theorem 4 of the paper), in binary64 from the coefficient midpoints: coefficients/data/extra_smalln_X3e5.json (n <= 6)
    and coefficients/data/an_cert_X1e4.json (n <= 1500); for n > 1500 the term c = 1 of the Kloosterman series,
    a_n ~ n (Jdot_2 - Idot_2)(4 pi sqrt n), whose relative error is below e^{-100}. C is the midpoint in
    coefficients/out/H0_cert.json. At x = 1 the value is C/(32 pi^2) (Theorem 5.4(d)); for x > 1 the series is summed until
    the remaining terms are below 1e-17 of the total. Sanity checks are printed.

Usage (from the top directory of the ancillary files): "$PY" figures/make_figure1.py
Needs numpy, scipy and matplotlib. Writes figures/figure1_H.csv, figures/figure1_G.csv and figures/figure1.pdf.
"""
import json, math, os, sys
import numpy as np
from scipy.special import ive, k0e

import scipy, matplotlib
print('make_figure1: numpy %s, scipy %s, matplotlib %s (an illustration, not a certificate)' % (np.__version__, scipy.__version__,
                                                                                               matplotlib.__version__))
HERE = os.path.dirname(os.path.abspath(__file__))
TOP = os.path.dirname(HERE)
P = lambda *a: os.path.join(TOP, *a)

# Certified enclosure of R(0) = Pi(0) (Theorem 7.10 of the paper; positivity/logs/check_r0.log):
R0_LO = 0.001400011269 - 2.50e-13
R0_HI = 0.001401746815 + 4.55e-13
R0_MID = 0.5 * (R0_LO + R0_HI)


def mid(s):  # "[m +/- r]" -> m
    return float(s.strip('[]').split('+/-')[0])


def lower_end(s):  # "[m +/- r]" -> m - r
    m, r = s.strip('[]').split('+/-')
    return float(m) - float(r)


# ---------------------------------------------------------------- panel (a)
cells = json.load(open(P('positivity', 'out', 'window_0_40.json')))
rows = [(0.0, 1.0, float('nan'), float('nan'), float('nan'))]
for c in cells:
    tc, low, ok, R = c[0], c[1], c[2], c[3]
    assert ok is True
    t_hi = tc + 0.25
    H_c = mid(R) / (16 * (tc * tc + 0.25) ** 2 * R0_MID)
    H_lo = lower_end(low) / (16 * (t_hi * t_hi + 0.25) ** 2 * R0_HI)
    assert 0 < H_lo < H_c
    rows.append((tc, H_c, tc - 0.25, t_hi, H_lo))
with open(os.path.join(HERE, 'figure1_H.csv'), 'w') as f:
    f.write('# t, H(t) (quadrature value, no error terms), cell_left, cell_right, lower bound for H on the cell (certified inputs)\n')
    for r in rows:
        f.write('%.2f,%.10e,%.2f,%.2f,%.10e\n' % r)
tL = np.linspace(8, 40, 161)
HL = 0.2554 * np.exp(0.6435 * tL) / (16 * (tL ** 2 + 0.25) ** 2 * R0_HI)

# ---------------------------------------------------------------- panel (b)
a = {int(k): float(v[0]) for k, v in json.load(open(P('coefficients', 'data', 'an_cert_X1e4.json')))['a'].items()}
for k, v in json.load(open(P('coefficients', 'data', 'extra_smalln_X3e5.json'))).items():
    a[int(k)] = float(v[0])
N0 = max(a)
assert sorted(a) == list(range(1, N0 + 1)) and N0 == 1500
C = float(json.load(open(P('coefficients', 'out', 'H0_cert.json')))['C'][0])
loga_small = np.log(np.array([a[n] for n in range(1, N0 + 1)]))


def scaled_c1(n):
    """a_n e^{-z_n} from the term c = 1, n (Jdot_2 - Idot_2)(z_n), z_n = 4 pi sqrt n, using
    Idot_2(z) = -K_2(z) + 2 I_0(z)/z^2 - 2 I_1(z)/z (DLMF 10.38.3); K_2 e^{-z} and Jdot_2 e^{-z} are below 1e-200 here."""
    z = 4 * np.pi * np.sqrt(n)
    return n * (2 * ive(1, z) / z - 2 * ive(0, z) / z ** 2)


chk = scaled_c1(np.array([float(N0)]))[0] / math.exp(math.log(a[N0]) - 4 * math.pi * math.sqrt(N0))
print('check: c = 1 term / certified midpoint at n = %d: 1 %+.2e' % (N0, chk - 1))
assert abs(chk - 1) < 1e-12


def G_scaled(x):
    """e^{4 pi sqrt x} Ghat_H(x) for x > 1."""
    s = math.sqrt(x)
    n = np.arange(1, N0 + 1, dtype=float)
    w = 4 * np.pi * np.sqrt(n * x)
    tot = np.sum(np.exp(loga_small - w + 4 * np.pi * s) * k0e(w))
    a_ = 4 * np.pi * (s - 1)
    N = int(min(max(N0, math.ceil((45.0 / a_) ** 2)), 4_000_000))
    tail_max = 0.0
    for lo in range(N0 + 1, N + 1, 500_000):
        n = np.arange(lo, min(N, lo + 499_999) + 1, dtype=float)
        z = 4 * np.pi * np.sqrt(n)
        w = z * s
        terms = scaled_c1(n) * np.exp(z - w + 4 * np.pi * s) * k0e(w)
        tot += np.sum(terms)
        tail_max = terms[-1]
    assert tail_max <= 1e-17 * tot, (x, N, tail_max, tot)
    return C * math.sin(math.pi * x) ** 2 * s * tot


xs = np.concatenate([np.round(np.arange(1.004, 1.1, 0.002), 3), np.round(np.arange(1.1, 6.0 + 1e-9, 0.005), 3)])
G1 = C / (32 * math.pi ** 2) * math.exp(4 * math.pi)
Gs = np.array([G_scaled(float(x)) for x in xs])
print('check: e^{4 pi} Ghat(1) = %.6e; series at x = 1.004: %.6e' % (G1, Gs[0]))
assert np.all(Gs >= 0)
X = np.concatenate([[1.0], xs])
Y = np.concatenate([[G1], Gs]) / 1e6
with open(os.path.join(HERE, 'figure1_G.csv'), 'w') as f:
    f.write('# x, e^{4 pi sqrt x} Ghat_H(x) / 10^6 (binary64 from coefficient midpoints; x = 1: C/(32 pi^2) e^{4 pi} / 10^6)\n')
    for x, y in zip(X, Y):
        f.write('%.3f,%.10e\n' % (x, y))
for xv in (1.5, 2.5, 3.5):
    i = int(np.argmin(abs(X - xv)))
    print('x = %.1f: e^{4 pi sqrt x} Ghat_H(x) / 10^6 = %.6f' % (X[i], Y[i]))

# ---------------------------------------------------------------- the figure
import logging
logging.getLogger('fontTools').setLevel(logging.ERROR)
import matplotlib
matplotlib.use('pdf')
import matplotlib.pyplot as plt
matplotlib.rcParams.update({'font.family': 'serif', 'font.serif': ['cmr10'], 'mathtext.fontset': 'cm',
                            'axes.formatter.use_mathtext': True, 'axes.unicode_minus': False, 'font.size': 8,
                            'pdf.fonttype': 42, 'axes.linewidth': 0.6, 'lines.linewidth': 0.9})
fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(6.3, 2.45))
H = np.array(rows)
ax1.semilogy(H[:, 0], H[:, 1], color='black', label=r'$H(t)$')
for r in rows[1:]:
    ax1.plot([r[2], r[3]], [r[4], r[4]], color='tab:blue', linewidth=1.1, solid_capstyle='butt')
ax1.plot([], [], color='tab:blue', linewidth=1.1, label='lower bound from certificate W, per cell')
ax1.semilogy(tL, HL, color='tab:red', linestyle='--', label=r'bound of Theorem 7.4 ($t\geq 8$)')
ax1.set_xlim(0, 40)
ax1.set_xlabel(r'$t$')
ax1.set_title(r'(a) $H(t)$, $0\leq t\leq 40$', fontsize=8)
ax1.legend(fontsize=6.5, frameon=False, loc='upper left')
ax2.plot(X, Y, color='black')
for k in (2, 3, 4, 5):
    ax2.axvline(k, color='0.6', linewidth=0.5, linestyle=':')
ax2.set_xlim(1, 6)
ax2.set_ylim(0, None)
ax2.set_xlabel(r'$x$')
ax2.set_title(r'(b) $e^{4\pi\sqrt{x}}\,\widehat{G}_H(x)\,/\,10^{6}$, $1\leq x\leq 6$', fontsize=8)
fig.tight_layout(pad=0.4, w_pad=1.2)
fig.savefig(os.path.join(HERE, 'figure1.pdf'), metadata={'Creator': None, 'Producer': None, 'CreationDate': None})
print('wrote figures/figure1_H.csv, figures/figure1_G.csv, figures/figure1.pdf')
