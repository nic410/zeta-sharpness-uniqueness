# Ancillary files: certified computations of Part II

This directory contains the computer-assisted certificates of the paper *Sharpness and uniqueness for positive solutions
of the explicit formula for ζ(s)* (Part II of a series). The companion paper *Positive solutions of the explicit formula
for ζ(s): near-criticality and uniqueness* is called Part I. The directory holds the exact input files, standalone verification
scripts and logs of fresh runs of the shipped scripts on the shipped inputs. Sections 3–9 list each certificate with its
statement, method, inputs (SHA-256), exact command, expected output and runtime. Section 13 describes the data and script
of Figure 1 of the paper, which is an illustration and not a certificate.

The directory `lean/` (if present) is a separate component with its own README. It is not described here and is not
covered by `SHA256SUMS`.

## 1. Requirements and conventions

- Python ≥ 3.10 with **python-flint 0.9.0** (FLINT/Arb ball arithmetic): `pip install python-flint==0.9.0`. The scripts
  of `positivity/` use nothing else (no numpy, scipy, sympy or mpmath). `runlog.sh` records the mpmath version in the
  log header if mpmath is installed. The scripts of `coefficients/` also use **numpy** (the shipped runs used numpy 2.2.6;
  `runlog.sh` does not record its version).
- Run every command from this directory (the top directory of the ancillary files). Scripts locate their inputs relative
  to their own location: the Part I library in `lib/` and the coefficient files in `coefficients/data/`. The scripts of
  `coefficients/` write their results to `coefficients/out/` and read the results of earlier steps from there; the
  Kloosterman tables are cached in `coefficients/cache/` (Section 8).
- **Environment variables** read by the scripts:
  - `COEFF_EXTRA`: path of the file with sharper balls for the first coefficients. The shipped runs of
    Sections 3, 4 and 5 set it to `coefficients/data/extra_smalln_X3e5.json`. `check_r0.py` uses that file by default,
    and `negctl.py` ignores the variable.
  - `COEFF_DATA`: directory of the coefficient files, written with a final `/` (default `coefficients/data/`).
  - `NGL`: Gauss–Legendre nodes per panel (default 30).
  - `NSUB`: sub-balls per cell in `run_window.py` (default 8).

  `runlog.sh` records those that are set in the `# env` line of the log header. Give paths relative to this directory.
  The scripts of `coefficients/` read none of these variables.
- `./runlog.sh LOGFILE "$PY" SCRIPT ARGS` (after `export PY=python3`, or any interpreter with python-flint) runs one
  verifier. It writes a log with a header and a footer:
  - header: command, environment variables, UTC date, system, Python/python-flint/mpmath versions;
  - footer: exit code, wall time.

  Every log shipped here was produced this way, in a fresh run of the shipped script on the shipped inputs.
- **Arithmetic.** "Arb" means rigorous ball arithmetic (midpoint–radius intervals with outward rounding) at the stated
  working precision in bits; every quantity printed as a ball `[m +/- r]` contains the exact value. Exact rationals
  (Python `Fraction`) are used for the coverage check of the cells. In `positivity/`, binary64 numbers are used only in
  four ways, and never to compute a bound:
  - to choose parameters (cell centres, partition points and sub-balls), which are then used as the exact binary numbers
    they are;
  - to choose the ellipse parameters ρ;
  - for truncation and loop control;
  - to enlarge the stored coefficient radii.

  In `coefficients/`, binary64 numbers also hold the midpoints of the Arb-DFT Kloosterman tables (with one rigorous
  radius per table), and `kloost_fast.py` computes Kloosterman sums in binary64 with an a-priori bound for all rounding
  errors (Section 8); both enter Arb as balls with these radii.
- **Lower and upper bounds.** A certified lower or upper bound is an exact binary number computed in Arb, for example the
  minimum of the lower endpoints over the sub-balls of a cell. It is printed as a decimal ball `[m +/- r]` that contains
  it, so the lower end of the printed ball of a lower bound is again a lower bound, and the upper end of the printed ball
  of an upper bound is again an upper bound. The verdicts (`ok=True`, `R(0) > 0: True`, the `DECISIVE` lines) are exact
  Arb comparisons, not comparisons of printed decimals.
- **Verdicts and checks.** The result of each certificate is its `DECISIVE` line (Sections 3, 4, 5, 7, 8 and 9; Section 6 has
  the line `[certified] R(0) in [...] ... R(0) > 0: True`).
  - The scripts exit with code 0 whether the verdict is `True` or `False`, so the verdict line is the result, not the
    exit code.
  - Preconditions and internal checks are Python `assert` statements or raise `ValueError`; a failing check stops the run
    with a traceback and a non-zero exit code. These include the coverage of [T_A, T_B] by the cells, r_t < 3/2, the
    admissibility of the ellipse boxes, the ratio bounds of the geometric tails of the K₀-sums, of the conical series
    and of the Y-tail, the bracket constant < 0.6 and the overlap of coefficient balls from different files; in
    `coefficients/`, also the hypotheses of the c-tail bounds (X ≥ 4π√n) and Q0² > X.
  - `python -O` removes `assert` statements, so the scripts must be run without `-O` and without `PYTHONOPTIMIZE`.
    `runlog.sh` refuses to run in either case.
- **Bessel functions.** K₀ for real arguments comes from `lib/besselk.py`: Part I's library, shipped byte-identical, with
  the DLMF 10.31 series and the DLMF 10.40 asymptotics with the error bound of DLMF 10.40(ii). Complex arguments occur
  only through the majorant |K₀(z)| ≤ K₀(Re z) (Re z > 0). In `positivity/`, Arb's own `bessel_k` is not used. In
  `coefficients/`, K₀ and K₁ for real arguments also come from `lib/besselk.py` and the other Bessel functions
  (I₀, I₁, I₂, J₀, J₁, J₂, Y₂) from Arb; `cert_H0.py` and `cert_Ht.py` call Arb's `bessel_k` only at exact (midpoint)
  complex arguments and add a derivative bound for the radius (Section 9).
- `tools/logdiff.py` compares a re-run log, or the window output JSON, with the shipped one after removing dates, the
  system line and timings (Section 11).

## 2. Layout

| Path | Contents |
|---|---|
| `positivity/` | The positivity certificates for R (Sections 3–7). `poslib.py`: library (coefficient balls and the n-tail bound, the K₀-sums A and B, the conical functions P_{−1/2+it} by hypergeometric series with Arb tail bounds, Gauss–Legendre nodes). `cert_window.py`: certificate W on one cell (Taylor model in t with all error terms). `run_window.py`: the driver over [T_A, T_B] (8 worker processes). `cert_large_t.py`: the numerical hypotheses of Theorem L at T₀. `cert_gtail.py`: B > 0 on [4, ∞). `check_r0.py`: the enclosure of R(0). `negctl.py`: the negative control. `positivity/logs/` holds the logs of the shipped runs, and `positivity/out/` the per-cell output of the window run (JSON). |
| `coefficients/` | The coefficient certificates (Sections 8 and 9). `coefflib.py`: library (the Bessel order derivatives J̇₂, İ₂, the Kloosterman tables by Arb DFT with twisted multiplicativity, the c-tail bounds). `kloost_fast.py`: Kloosterman sums for prime powers q > 10⁴ in binary64 with a proved error bound. `cert_an.py`, `cert_small_n.py`: the coefficient balls. `fix_json_radii.py`: outward rounding of the stored radii (called by the writers). `make_extra.py`: the {n: [midpoint, radius]} files in the format of `COEFF_EXTRA`. `analytic_constants.py`: the constants of Theorems 6.1–6.2 of the paper. `cert_H0.py`: H_raw(0) and the normalising constant C. `cert_Ht.py`: H_raw(t) by the same route (cross-check). `compare_window.py`, `compare_outputs.py`: comparisons with the window certificate and with `coefficients/data/`. `check_kloost_fast.py`: self-test of `kloost_fast.py`. `coefficients/logs/` holds the logs of the shipped runs, and `coefficients/out/` their outputs (JSON). `.gitignore`: excludes `cache/`. |
| `coefficients/data/` | The three coefficient files read by `positivity/` (certified balls for a_n). Their numerical content is that of the files consumed by the original certified runs; one metadata key was renamed before publication (Section 10). |
| `coefficients/cache/` | Not shipped: the cache of Kloosterman tables (47 MB), written by `cert_an.py` and rebuilt when absent (Section 8). |
| `figures/` | Figure 1 of the paper, an illustration and not a certificate (Section 13). `make_figure1.py`: the script. `figure1_H.csv`, `figure1_G.csv`: the plotted values. `figure1.pdf`: the figure included by the paper. `figures/logs/` holds the log of the shipped run. |
| `lib/` | Part I library, byte-identical to the files of the same names in Part I's ancillary files. `besselk.py`: rigorous K₀, K₁ for real arguments. `common.py`: the explicit-check helper used by `besselk.py` (with other helpers of Part I that are not used here). `__init__.py`: empty. |
| `tools/` | `logdiff.py`: compare logs (or the window JSON) up to dates and timings. |
| `runlog.sh` | Wrapper that writes a log with header and footer. |
| `SHA256SUMS` | SHA-256 of every shipped file except the logs, this README and `lean/` (`sha256sum -c SHA256SUMS`); the cache `coefficients/cache/` is not shipped. |
| `lean/` | If present: a separate component with its own README, not covered by `SHA256SUMS`. |

## 3. Certificate W: R(t) > 0 on [0, 40] (`positivity/run_window.py`)

**What it proves** (Certificate W: Theorem 7.10 of the paper, where R is called Π). For every t ∈ [0, 40],

  R(t) = axis(t) + arcs(t) > 0,  axis(t) = ∫₁^∞ A(Y) cos(t log Y) dY,  arcs(t) = ½ ∫_{1/2}^∞ B(Y) c_t(θ(Y)) dY.

Here:
- A(Y) = Σ_{n≥1} 2πn a_n √Y K₀(2πnY) and B(Y) = Σ_{n≥1} (−1)^{n+1} 2πn a_n √Y K₀(2πnY);
- θ(Y) = 2 arccot(2Y), and c_t(θ) = √(sin θ)[P(cos θ) + P(−cos θ)]/(2P(0)), with P = P_{−1/2+it} the Ferrers (conical)
  function;
- a_n = n S_n + δ_{n,1}/4 is the coefficient sequence of the paper.

In the scripts A is `Phi`, B is `g`, c_t is `fhat_t`, and H_raw(t) = R(t)/(2π²(t² + 1/4)²). R is even, so W gives
R > 0 on [−40, 40]. Theorem L (Sections 4 and 5) covers |t| ≥ 8, so W and Theorem L together give R > 0 on ℝ.

**Method** (all in Arb at 192 bits; the m-node bound and the bracket bound below are Lemmas A.2 and A.1 of the paper).
- **Cells.** [0, 40] is covered by 80 closed cells [t_c − 1/4, t_c + 1/4], t_c = 1/4, 3/4, …, 79/4. The coverage is
  checked in exact rationals before any cell is certified.
- **Quadrature.** Gauss–Legendre with rigorous nodes and weights (`arb.legendre_p_root`), m = 30 nodes per panel:
  30 panels on [1/2, 13] for arcs and 20 panels on [1, 13] for axis. The error per panel is at most
  ((b−a)/2)(64/15) M ρ^{−2m}/(1 − ρ^{−2}) for the m-node rule. Here M bounds the integrand, uniformly for t in the
  cell, on an outward Arb box that contains the Bernstein ellipse E_ρ; the analyticity of the integrand on the box is
  tested in Arb.
- **Taylor model.** In δ = t − t_c the sum has order K = 20 and is computed by Arb power-series arithmetic. The Cauchy
  remainder is M_Q (d/r_t)^K/(1 − d/r_t), with d = 1/4 and M_Q ≥ sup |Q_trunc| on the circle |z − t_c| = r_t = 1.
  - The truncated conical representation contains 1/P(0), which has poles at ±i(3/2 + 2m), so the radius must satisfy
    r_t < 3/2 (checked).
  - M_Q uses the Mehler–Dirichlet majorant |P_{−1/2+iz}(cos α)| ≤ P_{−1/2+iT}(cos α), T = |t_c| + r_t.
  - 1/|P_z(0)| is bounded on the circle by 96 covering Arb boxes, and on the disc by the maximum principle.
- **Conical series.** P(±cos θ) are hypergeometric series in z₁ = 1/(4Y² + 1) ≤ 1/2 (DLMF 15.8.10 for P(−cos θ)),
  truncated at k_max = ⌊300 + 8T⌋. The k-tail uses the ratio bound of the coefficients and the bracket bound
  |br_k| ≤ 4(1/2 + T)/(k_max + 3/2 − T) < 0.6.
- **Y-tail.** Beyond Y = 13: ∫_{13}^∞ A ≤ sup_{[13,14]} A/(1 − √(14/13) e^{−2π}), |B| ≤ A, and c_t is bounded from its
  series at z₁ = 1/677.
- **n-tail.** The terms n ≤ N ≤ 300 use the coefficient balls. For n > N, |a_n| ≤ A0(n) = n^{1/4}e^{4π√n}/(4√2π²)
  (the coefficient bound a_n ≤ A0(n) together with a_n > 0: Theorems 6.1 and 6.2 of the paper, where A0(n) is written ā_n), K₀(x) ≤ √(π/(2x))e^{−x} and a
  geometric series.
- **Positivity on the cell.** The Taylor polynomial is evaluated on 8 sub-balls of [−1/4, 1/4] that cover the cell
  exactly (dyadic endpoints). All error terms (quadrature, Cauchy remainder, k-tail, Y-tail) are subtracted as one
  exact radius. The minimum of the lower endpoints is the certified lower bound `lower=` of the cell, and the cell is
  `ok` if it is > 0.

The log prints, for each cell, R(t_c) (the quadrature value, without error terms), the certified lower bound and the four
error terms. From these printed values, every cell lower bound is at least 0.2952·R(t_c) (the smallest ratio, 0.29528, is
on the cell [0.5, 1]). The quadrature error is at most 1.35·10⁻⁷·R(t_c) (the largest ratio, 1.3420·10⁻⁷, is on the cell
[39.5, 40]) and the Cauchy remainder at most 1.33·10⁻⁷·R(t_c) on every cell; these figures are informational.

**Inputs.**
- `coefficients/data/an_small_X1e4.json` (`59fe6e24647252db`), `coefficients/data/an_cert_X1e4.json`
  (`59d50f17db2199b1`) and `coefficients/data/extra_smalln_X3e5.json` (`ff4b86318eed86f1`); see Section 10 for their
  provenance.
- Scripts `positivity/run_window.py`, `positivity/cert_window.py`, `positivity/poslib.py`, `lib/besselk.py`.

The log prints the first 16 hex digits of the SHA-256 of the three scripts of `positivity/` and of the three input
files; full hashes are in Section 10 and `SHA256SUMS`.

**Command** (from this directory):

```sh
COEFF_EXTRA=coefficients/data/extra_smalln_X3e5.json ./runlog.sh positivity/logs/window_0_40.log "$PY" positivity/run_window.py 0 40 0.25 20 1 0_40
```

The arguments are T_A = 0, T_B = 40, d = 0.25, K = 20, r_t = 1 and the tag `0_40`. The run writes
`positivity/out/window_0_40.json`: one entry per cell with t_c, the lower bound, the verdict, R(t_c) and the error terms
`cauchy`, `quad`, `ytail`, `ktail`, the bound `MQ`, the Y-tail factor `fy`, the certified upper bound `Rmax` and the
timing `secs`.

**Expected output** (verbatim lines or parts of lines of `positivity/logs/window_0_40.log`):
- `[0, 40] d=0.25 K=20 rt=1 NGL=30 nsub=8, 80 cells (coverage verified in exact rationals)`
- `cell [0.0000, 0.5000]: R(tc)=[0.002192 +/- 9.41e-7]  lower=[0.00112926259401 +/- 1.26e-15]  ok=True`
- `cell [39.5000, 40.0000]: R(tc)=[1.2287975e+17 +/- 3.08e+9]  lower=[9.03419817418e+16 +/- 3.11e+4]  ok=True`
- `DECISIVE: R(t) > 0 on [0, 40] (all 80 cells certified): True`

**Runtime.** 31.2 s wall time with 8 worker processes on 8 cores. Each worker first builds the quadrature nodes
(about 12 s).

## 4. Theorem L at T₀ = 8: R(t) > 0 for |t| ≥ 8 (`positivity/cert_large_t.py`)

**What it proves** (the numerical inputs of Theorem L, the large-|t| theorem: Proposition 7.9 of the paper, used in Theorem 7.4, at T₀ = 8). The notation is that of
Section 3, with B⁻ = max(−B, 0). The parameters are Y_z = 0.87, Y_s = 1, Y₃ = 4 and κ = 1/2, and
θ_s = θ(Y_s) = 2 arccot 2. The script certifies, in Arb with directed rounding:
- (a) B(Y) > 0 on [Y_z, Y₃]. The minimum of the cell lower bounds is ≥ 0.581726 on [0.87, 1] and ≥ 1.74105·10⁻⁷ on
  [1, 4].
- (b) T₀ = 8 ≥ t_mono := 1/(2(θ(Y_z) − θ_s)) = 4.3125243….
- (c) p(T₀) − n(T₀) − A_Φ e^{−T₀(π/2 − θ_s)} > 0. The certified margin is [0.255407883141 ± 3.57·10⁻¹³].

The quantities in (c) are:
- p(t) = ½ ∫_{Y_s}^{Y₃} B(Y) · ½ √(sin θ / sin(θ + κθ/2)) e^{t(θ_s − θ)} erf(√(tκθ)) r₋(t/2) dY;
- n(t) = ½ ∫_{1/2}^{Y_z} B⁻(Y) · ½ √(sin θ) r₊(t/2) √(2πt) [e^{−t(π−θ−θ_s)} P₀(cos θ) + ½(e^{−t(θ−θ_s)} + e^{−t(2π−θ−θ_s)}) P₀(−cos θ)] dY;
- A_Φ = ∫₁^∞ A(Y) dY (`A_Phi`), which bounds |axis(t)|.

Here θ = θ(Y), r₋(y) = exp(−9/(32y²) − 1/(3y)), r₊(y) = exp(9/(64y²) + 1/(3y)) and P₀ = P_{−1/2}.

With B > 0 on [4, ∞) (Section 5), these are the hypotheses of Theorem L, which then gives R(t) > 0 for every |t| ≥ 8.
The `DECISIVE` line of this script covers (a), (b) and (c); the hypothesis B > 0 on [4, ∞) is certified separately by
`cert_gtail.py`.

**Method** (Arb at 160 bits; integration cells are exact balls with binary64 endpoints that tile the intervals exactly).
- **p(T₀).** A lower Riemann sum over 2000 geometric cells of [1, 4]. The integrand is enclosed on each cell, with B
  given by its K₀-sum and the n-tail bound of Section 3, and the sum is rounded down.
- **n(T₀).** An upper Riemann sum over 8000 cells of [1/2, 0.87], rounded up. On each cell, B⁻ is bounded by the
  negative of the lower endpoint of the ball of B, an exact number. P₀(±cos θ) comes from the conical series at t = 0.
  7009 cells contribute.
- **(a).** The minimum of the exact lower endpoints of B over 300 cells of [0.87, 1] and the 2000 cells of [1, 4].
- **A_Φ.** 20 panels × 30 Gauss–Legendre nodes on [1, 13] with the m-node error bound of Section 3 and Arb majorants on
  ellipse boxes, plus the Y-tail ∫_{13}^∞ A ≤ sup_{[13,14]} A/(1 − √(14/13)e^{−2π}). The result is
  A_Φ ≤ 5.58489336212, with quadrature error ≤ 2.51·10⁻¹⁷ and Y-tail ≤ 5.02·10⁻³².
- **The margin.** It is formed from the exact endpoints p(T₀)_lower, n(T₀)_upper and the upper bound of the axis term.

**Inputs.** The three coefficient files of Section 3. Scripts `positivity/cert_large_t.py`, `positivity/cert_window.py`
(for the Arb majorants and ellipse boxes), `positivity/poslib.py` and `lib/besselk.py`. The log prints the hash prefixes.

**Command** (from this directory):

```sh
COEFF_EXTRA=coefficients/data/extra_smalln_X3e5.json ./runlog.sh positivity/logs/cert_large_t_T8.log "$PY" positivity/cert_large_t.py 8 0.5 1 0.87 4 2000 8000
```

The arguments are T₀, κ, Y_s, Y_z, Y₃, then the cell counts N_p = 2000 for p and N_n = 8000 for n.

**Expected output** (verbatim parts of lines of `positivity/logs/cert_large_t_T8.log`):
- `t_mono = [4.3125243 +/- 1.90e-8]`
- `(1a) min lower bound of g on [Yz, Ys] = [0.581726 +/- 3.27e-7]  (> 0 needed)`
- `(1b) min lower bound of g on [Ys, Y3] = [1.74105e-7 +/- 7.7e-16] ; p(T0) >= [2.22681094932 +/- 1.09e-12]`
- `(2) n(T0) <= [1.93894945416 +/- 1.93e-12]  (7009 cells with possible g < 0)`
- `A_Phi <= [5.58489336212 +/- 3.21e-12]`
- `A_Phi e^{-T0(pi/2-th_s)} <= [0.0324536120224 +/- 3.66e-14] ; margin = [0.255407883141 +/- 3.57e-13] ; ratio p/(n + axis term) >= [1.12956 +/- 3.61e-6]`
- `DECISIVE (all-Arb): Theorem L hypotheses verified for T0 = 8: True`

**Runtime.** 137.2 s wall time on one core.

## 5. B > 0 on [4, ∞) (`positivity/cert_gtail.py`)

**What it proves** (the positivity of B on [Y₃, ∞), Y₃ = 4: Lemma 7.7(b) and Proposition 7.9(ii) of the paper, used in the proof of Theorem 7.4). For every
Y ≥ 4, B(Y) > 0. Write

  ρ(Y) = Σ_{n≥2} n a_n K₀(2πnY)/(a₁K₀(2πY)).

Then B(Y) ≥ 2πa₁√Y K₀(2πY)(1 − ρ(Y)), since a_n > 0. For Y ≥ 4,

  ρ(Y) ≤ ρ̄(Y) := Σ_{n≥2} √n (A0(n)/a₁) e^{−2π(n−1)Y}/(1 − 1/(16πY)),

and ρ̄ is decreasing in Y. The script certifies ρ̄(4) < 1.

**Method** (Arb at 160 bits).
- The bound on ρ uses √(π/(2x))e^{−x}(1 − 1/(8x)) ≤ K₀(x) ≤ √(π/(2x))e^{−x} for x > 0 (DLMF 10.40(ii): the remainder
  is bounded by the first neglected term and has its sign).
- a₁ is replaced by the lower endpoint of its ball.
- The terms 2 ≤ n ≤ 399 are summed in Arb. The tail n ≥ 400 is at most twice the term n = 400, since the ratio of
  consecutive terms is at most (1 + 1/n) e^{2π/√n − 2πY} < 10⁻¹⁰ for n ≥ 400 and Y = 4 (from
  A0(n+1)/A0(n) ≤ (1 + 1/n)^{1/4} e^{2π/√n}; this estimate is not re-checked by the script).

**Inputs.** The three coefficient files of Section 3 (only a₁ is used, from its sharpest ball). Scripts
`positivity/cert_gtail.py` and `positivity/poslib.py`.

**Command** (from this directory):

```sh
COEFF_EXTRA=coefficients/data/extra_smalln_X3e5.json ./runlog.sh positivity/logs/cert_gtail.log "$PY" positivity/cert_gtail.py
```

**Expected output** (verbatim lines of `positivity/logs/cert_gtail.log`):
- `rhobar(4) = [4.198895694e-9 +/- 1.65e-19]  (< 1 needed): True`
- `DECISIVE: g > 0 on [4, oo): True`

**Runtime.** 0.1 s wall time.

## 6. The enclosure of R(0) (`positivity/check_r0.py`)

**What it proves** (the enclosure of Π(0) stated in Theorem 7.10 of the paper). R(0) ∈ [0.001400011269, 0.001401746815] (each endpoint up to the radius of
its printed ball). Hence R(0) > 0 and H_raw(0) = 8R(0)/π² > 0. This is sign coherence: the normalising constant
C = π²/(8R(0)) is positive. Certificate W also gives R(0) > 0, since its first cell contains t = 0; this script gives the
two-sided enclosure.

**Method.** The certifier of Section 3, with all error terms, on the cell [−10⁻⁶, 10⁻⁶] (K = 8, r_t = 1/2, 192 bits).
It returns the minimum of the lower endpoints and the maximum of the upper endpoints over the 8 sub-balls of the cell.
The point t = 0 is the left endpoint of one of these sub-balls.

The line also prints, for comparison only, an independently computed value H_raw(0) = 0.0011355097904 ± 1.9·10⁻⁹ (a
constant in the script; see Section 9). The script does not check this value.

The lines marked `[not a certificate]` compare H(t) = R(t)/(16(t² + 1/4)²R(0)) at t = 1, 2, 4, 8, 12, 20, 40 with
Fourier-side floating-point values of H(t) that are constants in the script. Both R(t) and R(0) are the quadrature values
without error terms. The relative differences are about 3.9·10⁻⁷, a constant offset in t (a relative offset of 3.9·10⁻⁷ in
R(0) corresponds to a change of only about 5·10⁻⁸ in a₁; see **Conditioning** below).

**Conditioning.** R(0) is a small difference of large terms in the coefficients. At t = 0 the formula is linear in the a_n:
R(0) = Σ_n a_n w_n, where w_n is the value at t = 0 of the axis and arc integrals for the n-th terms of A and B. The terms
a_n w_n are about +51.7, −330, +719, −849, +680, −413, +203 (n = 1, …, 7), against R(0) ≈ 1.40·10⁻³: a cancellation of
about 6·10⁵:1. In particular ∂R(0)/∂a₁ = w₁ ≈ 0.0113, and a relative change of −2.7·10⁻⁵ in a₁ alone would make R(0)
vanish. The certifier handles this rigorously: every a_n enters through a certified enclosure (the balls of Section 8 for
n ≤ 300, which include the tail of the Kloosterman series, and 0 < a_n ≤ A0(n) beyond), and all radii are propagated. The
radius of the enclosure above, 8.7·10⁻⁷, is mostly (7.7·10⁻⁷) w₁ times the radius 6.9·10⁻⁵ of a₁ in
`extra_smalln_X3e5.json`, and R(0) exceeds it by a factor of about 1600. A floating-point reproduction of R(0), or of
H_raw(0) = 8R(0)/π² at the precision of Section 9, needs a₁ to an absolute accuracy of about 2·10⁻⁷. The c-series must
therefore be summed far: its partial sums for a₁ up to c = 10⁴ and up to c = 3·10⁵ differ by 3.2·10⁻⁷ (`checkpoints_K` in
`coefficients/out/an_smalln_X6e5.json`). The certificate of Section 9 uses a route that is far less sensitive to a₁. See
Remark 7.13 of the paper; the figures other than the certified radii are floating-point evaluations and are not used by any
proof.

**Inputs.** The three coefficient files of Section 3; `COEFF_EXTRA` defaults to `coefficients/data/extra_smalln_X3e5.json`.
Scripts `positivity/check_r0.py`, `positivity/cert_window.py`, `positivity/poslib.py` and `lib/besselk.py`.

**Command** (from this directory):

```sh
./runlog.sh positivity/logs/check_r0.log "$PY" positivity/check_r0.py
```

**Expected output** (verbatim line of `positivity/logs/check_r0.log`):
- `[certified] R(0) in [[0.001400011269 +/- 2.50e-13], [0.001401746815 +/- 4.55e-13]] ; H_raw(0) = 8 R(0)/pi^2 in [0.00114 +/- 5.20e-6]  (independent value, not checked here: 0.0011355097904 +- 1.9e-9) ; R(0) > 0: True`

**Runtime.** 17.6 s wall time on one core.

## 7. Negative control (`positivity/negctl.py`; Remark 7.12 of the paper; not used by any proof)

**What it shows.** The same certifier, with all error terms, is run with the coefficients replaced by
a_n → n·T1_n + δ_{n,1}/4. Here T1_n is the c = 1 Kloosterman term, so the terms with c ≥ 2 are dropped. The T1 balls are
read from `an_cert_X1e4.json` with their printed radii kept and doubled. The tail n > 300 still uses A0(n); the script
checks 300·T1_300 < A0(300).

The script certifies **upper bounds R < 0**:
- −0.2526760380 on [−10⁻⁶, 10⁻⁶];
- −0.2506014462 on [0, 1/2];
- −0.2270255023 on [1/2, 1].

So the positivity of R near t = 0 depends on the c ≥ 2 terms of the coefficients, and the certifier proves a negative
sign when the sign is negative. The cells [0, 1/2] and [1/2, 1] are covered exactly by their sub-balls. The cell
[−10⁻⁶, 10⁻⁶] is covered by its 8 sub-balls up to three gaps narrower than 3·10⁻²²: its binary64 sub-ball endpoints are
rounded.

**Inputs.** `coefficients/data/an_cert_X1e4.json` (`59d50f17db2199b1`; its `T1` entries). `COEFF_EXTRA` is ignored.
Scripts `positivity/negctl.py`, `positivity/cert_window.py`, `positivity/poslib.py` and `lib/besselk.py`.

**Command** (from this directory):

```sh
./runlog.sh positivity/logs/negctl.log "$PY" positivity/negctl.py
```

**Expected output** (verbatim parts of lines of `positivity/logs/negctl.log`):
- `certified upper bound of R on the cell = [-0.2526760380 +/- 4.77e-11]`
- `certified upper bound of R on the cell = [-0.2506014462 +/- 4.29e-11]`
- `certified upper bound of R on the cell = [-0.2270255023 +/- 3.49e-11]`
- `DECISIVE (negative control): R < 0 certified on [-1e-6, 1e-6], [0, 0.5], [0.5, 1] for the c=1-only coefficients: True`

**Runtime.** 15.9 s wall time on one core.

## 8. Coefficient balls (`coefficients/cert_an.py`, `coefficients/cert_small_n.py`)

**What it proves** (Appendix A.1 of the paper). Certified balls for the coefficients

  a_n = n S_n + δ_{n,1}/4,  S_n = Σ_{c≥1} c⁻¹ [S(1,n;c) J̇₂(4π√n/c) − S(−1,n;c) İ₂(4π√n/c)],

where S(m,n;c) is the Kloosterman sum and J̇₂ = ∂_μJ_μ|_{μ=2}, İ₂ = ∂_μI_μ|_{μ=2}. They also certify the coefficients at
ν = 1, α_n = A_n(1) = 2 Σ_{c≥1} c⁻¹ [S(1,n;c) J₂(4π√n/c) − S(−1,n;c) I₂(4π√n/c)], which Section 9 uses together with
A_n′(1) = 4S_n. The scripts write `Kc_n` or `K` for S_n, and `alpha` for α_n.
- `cert_an.py`: a_n for n ≤ 1500, from the terms c ≤ 10⁴ (n ≤ 60) or c ≤ max(600, ⌈4π√n⌉ + 1) (60 < n ≤ 1500), plus a
  rigorous bound for all further terms; α_n for n ≤ 60. Every a_n with n ≤ 1500 is certified positive; Theorem 6.1 of
  the paper proves a_n > 0 for every n without computation. The ratio of Σ_{c≥2} |term_c| (including the bound for
  c > X) to the term c = 1 is at most 0.0035754 for every n ≤ 1500, with the maximum at n = 1.
- `cert_small_n.py`: sharper balls for n ≤ 6 from the terms c ≤ 3·10⁵, and for n ≤ 2 from c ≤ 6·10⁵. For example
  a₁ = 4581.3705534082 ± 6.86·10⁻⁵, a₂ = 1025727.234918 ± 2.67·10⁻⁴ and a₃ = 62590223.689992 ± 5.9·10⁻⁴ (c ≤ 3·10⁵),
  and a₁ = 4581.3705534088 ± 2.69·10⁻⁵ (c ≤ 6·10⁵). The radius of a₁ is dominated by the bound for the terms c > X.

**Method** (Arb at 96 bits, the term c = 1 at 256 bits; the Bessel bounds below are proved in the paper).
- **Kloosterman sums, prime powers q ≤ 10⁴.** For each q the whole table j ↦ S(1,j;q) is one discrete Fourier
  transform in Arb (`acb.dft`) of x_d = e(d̄/q). It is stored as binary64 midpoints with one rigorous radius per table
  (about 5.7·10⁻¹⁴). Composite moduli use twisted multiplicativity in Arb: S(1,n;qr) = S(1,n r̄²;q)·S(1,n q̄²;r) for
  (q,r) = 1.
- **Kloosterman sums, prime powers 10⁴ < q ≤ 6·10⁵** (`kloost_fast.py`, used by `cert_small_n.py`). The sum
  S(1,j;q) = Σ_d C[(d̄ + jd) mod q] is computed in binary64 with exact integer residues. The cosine table has the proved
  error |C[k] − cos(2πk/q)| ≤ 10⁻¹⁴ (exact octant reduction, Taylor polynomials of degree 22 and 23, Horner rounding
  bound). The summation, in any order, is bounded by Higham's bound γ_{m−1} Σ|x_i| (m = φ(q), γ_k = ku/(1 − ku),
  u = 2⁻⁵³). The resulting error bound, about 1.0·10⁻⁵ for the largest q at X = 3·10⁵ and 4.0·10⁻⁵ at X = 6·10⁵, is the
  radius of the Arb ball of each such sum.
- **Bessel order derivatives.** For arguments ≤ 8, J̇₂ and İ₂ come from their ascending series (termwise μ-derivatives)
  with a geometric tail bound. Beyond, they come from the closed forms −İ₂ = K₂ + (2/z)I₁ − (2/z²)I₀ and
  J̇₂ = (π/2)Y₂ + 2J₀/z² + 2J₁/z (DLMF 10.38.3 and 10.15.3 at n = 2), with K₀, K₁ from Part I's `lib/besselk.py`
  (K₂ = K₀ + 2K₁/z) and I₀, I₁, J₀, J₁, Y₂ from Arb. J₂ and I₂ (for α_n) come from Arb.
- **c-tail.** The terms c > X are bounded with the Weil–Estermann bound |S(±1,n;c)| ≤ d(c)c^{1/2}, the small-argument
  bound |İ₂(w)|, |J̇₂(w)| ≤ (w²/8)[(log(2/w) + ψ(3))(1 + (v/3)eᵛ) + (v/9)(1 + v)eᵛ] (v = w²/4, 0 < w ≤ 2), and partial
  summation with Σ_{c≤u} d(c) ≤ u(1 + log u). This needs X ≥ 4π√n, which is checked. The bound for α_n is the same with
  I₂(w), |J₂(w)| ≤ (v/2)(1 + (v/3)eᵛ). For S₁ it is at most 6.86·10⁻⁵ at X = 3·10⁵ and 2.69·10⁻⁵ at X = 6·10⁵.
- **Storage.** Each ball is stored as [40-digit decimal midpoint, radius]. `fix_json_radii.py` replaces the radius by
  nextafter(radius·(1 + 10⁻¹²) + |midpoint|·10⁻³⁸, +∞), so that the stored ball contains the computed ball.

**Inputs.** No data files. Scripts `coefficients/cert_an.py`, `coefficients/cert_small_n.py`, `coefficients/coefflib.py`,
`coefficients/kloost_fast.py`, `coefficients/fix_json_radii.py` and `lib/besselk.py`; the logs print the hash prefixes of
the scripts of `coefficients/` that they use. `cert_an.py` computes the Arb-DFT tables for q ≤ 10⁴ and caches them in
`coefficients/cache/kloost_tables_X10000.npz` (47 MB). The cache is not shipped (`coefficients/.gitignore`), and
`cert_small_n.py` loads it, or rebuilds it when it is absent. Its SHA-256 prefix, printed in the logs, is
`8bbdb234c3ecca4f` with numpy 2.2.6.

**Commands** (from this directory). Run `cert_an.py` first, since it builds the cache. The two runs of `cert_small_n.py` may
then run in parallel, followed by `make_extra.py`:

```sh
./runlog.sh coefficients/logs/cert_an_X1e4.log "$PY" -u coefficients/cert_an.py 60 10000 1500 600 X1e4
./runlog.sh coefficients/logs/cert_small_n_X3e5.log "$PY" -u coefficients/cert_small_n.py 300000 10000 1,2,3,4,5,6 X3e5
./runlog.sh coefficients/logs/cert_small_n_X6e5.log "$PY" -u coefficients/cert_small_n.py 600000 10000 1,2 X6e5
./runlog.sh coefficients/logs/make_extra.log "$PY" coefficients/make_extra.py X3e5 X6e5
```

The arguments of `cert_an.py` are N_small = 60 (the n summed up to c ≤ X), X = 10⁴, N_big = 1500, C2 = 600 and a tag.
Those of `cert_small_n.py` are X, Q0 = 10⁴, the list of n and a tag. Prime powers ≤ Q0 come from the Arb tables and
larger ones from `kloost_fast.py`; Q0² > X is checked, so each c has at most one prime-power factor > Q0. The option `-u`
keeps the lines printed by the radius-rounding subprocess in order. The runs write the following files to
`coefficients/out/`:
- `an_small_X1e4.json`: n ≤ 60, with a_n, S_n and α_n;
- `an_cert_X1e4.json`: n ≤ 1500, with a_n, S_n, the terms c = 1 (`T1`) and the cutoffs;
- `an_smalln_X3e5.json` and `an_smalln_X6e5.json`;
- `extra_smalln_X3e5.json` and `extra_smalln_X6e5.json` (written by `make_extra.py`): {n: [midpoint, radius]} of a_n,
  the format of `COEFF_EXTRA`.

**Expected output** (verbatim lines or parts of lines):
- `coefficients/logs/cert_an_X1e4.log`:
  - `DECISIVE: all a_n > 0 (ball lower endpoints) for n <= 1500: True`
  - `DECISIVE: max_n (sum_{c>=2}|term_c| incl. tail bound)/(c=1 term) = [0.0035753 +/- 2.75e-8] at n = 1`
  - `Kc_1 = [4581.12 +/- 6.71e-3]   (c=1 term [4565.895200290628930730491 +/- 2.56e-22])`
- `coefficients/logs/cert_small_n_X3e5.log` (and the lines for n = 2, …, 6):
  - `DECISIVE n=1: Kc_n = [4581.121 +/- 5.16e-4] ; a_n = [4581.371 +/- 5.16e-4] (rel rad 1.50e-08) ; alpha_n = [-55336.1783 +/- 5.87e-5] ; c-tail bounds [6.858e-5 +/- 3.89e-9] / [1.143e-5 +/- 4.85e-9]`
- `coefficients/logs/cert_small_n_X6e5.log`:
  - `DECISIVE n=1: Kc_n = [4581.1206 +/- 7.35e-5] ; a_n = [4581.3706 +/- 7.35e-5] (rel rad 5.87e-09) ; alpha_n = [-55336.17835 +/- 6.99e-6] ; c-tail bounds [2.689e-5 +/- 1.57e-9] / [4.239e-6 +/- 8.99e-11]`
  - `DECISIVE n=2: Kc_n = [512863.617 +/- 5.12e-4] ; a_n = [1025727.235 +/- 1.87e-4] (rel rad 1.02e-10) ; alpha_n = [-8871189.5680 +/- 3.59e-5] ; c-tail bounds [5.231e-5 +/- 2.30e-9] / [8.478e-6 +/- 1.80e-10]`

A printed ball `[m +/- r]` encloses the computed ball after rounding m to the printed digits, so r can exceed the radius of
the computed ball (`rel rad` is the relative radius of the computed ball). The stored balls are those quoted under "What it
proves".

**Runtime** (one core each). `cert_an.py`: 260 s, of which 162 s are spent building the tables. `cert_small_n.py`: 700 s
(X = 3·10⁵) and 1408 s (X = 6·10⁵). `make_extra.py`: under 1 s.

**Fresh outputs and the pinned inputs.** `coefficients/data/` holds the three coefficient files read by `positivity/`.
Their numerical content is that of the files consumed by the original certified runs; one metadata key was renamed
before publication (Section 10). `coefficients/out/` holds the outputs of the fresh runs of this section and of Section 9. The pinned files come from the same computation, run before the scripts had their
present names, so their `meta` entries (script names and hashes) differ. `compare_outputs.py` compares every certified
ball of the three fresh files with the pinned ones:

```sh
./runlog.sh coefficients/logs/compare_outputs.log "$PY" coefficients/compare_outputs.py
```

Result (`coefficients/logs/compare_outputs.log`, run after Section 9): every non-meta entry of the three fresh files equals
the pinned one. These are 7986 balls with the same midpoint string and the same radius (420 in `an_small_X1e4.json`, 7560
in `an_cert_X1e4.json`, 6 in `extra_smalln_X3e5.json`) and the 1500 cutoffs of `an_cert_X1e4.json`.
`extra_smalln_X3e5.json` has no `meta` entry and is byte-identical to the pinned file. The second line below is the
cross-check of Section 9:
- `DECISIVE: every certified ball of the fresh run is identical to (same midpoint string and radius) or overlaps the pinned ball (7986 balls: 7986 identical, 0 overlapping only) and all other entries agree: True`
- `DECISIVE: the eta1 = 1.25 cross-check of cert_H0.py overlaps the eta1 = 1 run in all 7 split-independent values: True`

**The constants of Theorems 6.1–6.2** (`coefficients/analytic_constants.py`). The proofs of Theorems 6.1 and 6.2 of the
paper reduce to elementary expressions at z = 4π and to two monotone envelopes. These are λ₀, ϱ, λ₋ and λ₊ of the paper,
called `lambda`, `rho`, `Lambda` and `Upsilon` in the script. The script evaluates them in Arb at 128 bits, together with
ϱ_α(4π) and the two factors of the bound for α_n. Lines marked `[not a certificate]` are grid spot checks of the
monotonicity facts, which are proved in the paper. The `§Jhat-large` lines are informational.

```sh
./runlog.sh coefficients/logs/analytic_constants.log "$PY" coefficients/analytic_constants.py
```

Expected output (verbatim parts of lines of `coefficients/logs/analytic_constants.log`):
- `DECISIVE: Lambda(4pi) = [0.850104915628 +/- 1.60e-13]  (> 0 required; Kc_n >= Lambda(z_n) G(z_n) for all n)`
- `DECISIVE: Upsilon(4pi) = [0.948271747553 +/- 3.66e-13] ; 4pi*(Upsilon - 1 + 1/z)(4pi) = [0.349963608522 +/- 4.63e-13]  (< 1 required => a_n <= A0(n) for all n)`
- `difference [0.1163628165 +/- 1.29e-11] (> 0 required)`
- `§alpha: rho_alpha(4pi) = [0.0081679591 +/- 3.61e-11]`

Runtime: 0.7 s.

**Self-test of the float Kloosterman engine** (`coefficients/check_kloost_fast.py`; not a certificate). It compares
`kloost_fast.py` with Arb in two ways:
- 300 random entries of the cosine table for each of 10 moduli; the largest error is about 1.5·10⁻¹⁶, against the proved
  10⁻¹⁴;
- S(1,j;q) for 7 moduli, against the Arb-DFT tables and, for q ≤ 1009 and j < 5, against brute-force Arb sums (`assert`).

```sh
./runlog.sh coefficients/logs/check_kloost_fast.log "$PY" coefficients/check_kloost_fast.py
```

Runtime: 0.6 s.

## 9. Normalising constant and cross-check (`coefficients/cert_H0.py`, `coefficients/cert_Ht.py`)

**What it proves** (Proposition 6.4 of the paper). Let Ĝ_raw(x) = sin²(πx)√x Σ_{n≥1} a_n K₀(4π√(nx)) for x > 1, continued
analytically to x > 0, and g_raw = Ĝ_raw/(2π√x). With γ_∞(0)² = π^{−1/2}Γ(1/4)²/64,

  H_raw(0) = M\[g_raw](1/2)/γ_∞(0)² = 0.0011355097904015565 ± 1.854·10⁻⁹ > 0,  M\[g](s) = ∫₀^∞ g(x)x^{s−1} dx.

Hence C := 1/H_raw(0) = 880.6617155075 ± 1.442·10⁻³ > 0 (sign coherence), and C/(32π²) = 2.7884277347 ± 4.6·10⁻⁶. The
script also prints b₁ = C·a₁ and A = C/(32π⁴).

**Method** (Arb at 160 bits; the formula and the two end bounds are proved in Appendix A of the paper).
- **Formula.** 2π M\[g_raw](1/2) = 𝒫 + ∫₀^∞ d_rest(η)√η Q(η) dη. Here 𝒫 = ∫₀^∞ sin²(πx)x^{−1/2}P(x) dx with
  P(x) = 1/(32π⁴(x²−1)) + 1/(8π⁴(x²−1)²), and the kernel has the closed form
  Q(η) = ∫₀^∞ sin²(πx)x^{−1/2}K₀(2πηx) dx = 2^{−5/2}(2πη)^{−1/2}Γ(1/4)²[1 − ₂F₁(1/4,1/4;1/2;−1/η²)]
  (Gradshteyn–Ryzhik 6.699.12).
- **Density.** On (0, 1], d_rest = d − d_grow, with the cusp-0 density d(η) = η^{−5/2} Σ_n 2n a_n K₀(2πn/η) and
  d_grow(η) = √η I₀(2πη)/(8π²) + η^{3/2}I₁(2πη)/(2π). On [1, 8], d_rest comes from its expansion at the cusp ∞, with the
  coefficients α_n = A_n(1) and A_n′(1) = 4S_n.
- **Coefficients.** The balls of Section 8, read from `coefficients/out/`: n ≤ 60 from c ≤ 10⁴, replaced by the c ≤ 3·10⁵
  balls for n ≤ 6 and the c ≤ 6·10⁵ balls for n ≤ 2 (balls for the same n must overlap, which is checked). For n > 60
  (cusp 0) and n > 30 (cusp ∞), the bounds a_n ≤ A0(n), |A_n′(1)| ≤ 4A0(n)/n (Theorem 6.2) and |α_n| ≤ 2.33·e^z/√(2πz),
  z = 4π√n (proved in the paper), enter as ball radii.
- **Integrals.** They use Arb's rigorous integration `acb.integral` (adaptive Gauss–Legendre, with error bounds from
  complex-ball evaluations of the integrand); off Re η > 0, where √, K and ₂F₁ branch, the integrands return NaN. K₀ and
  K₁ of complex argument are evaluated with Arb's `bessel_k` at the exact midpoint, plus r·sup|K′| over the ball, using
  |K_ν(w)| ≤ K_ν(Re w) ≤ K₁(Re w) and Part I's real K₁.
- **𝒫.** The part x ∈ [0, 2000] is integrated in u = √x (sinc form, entire integrand). The part x > 2000 is bracketed, with a
  second-mean-value bound for the cosine part.
- **Ends.** The contributions of η ∈ [0, 10⁻⁸] and η ∈ [8, ∞) are bounded analytically, by at most 3.14·10⁻¹⁴ and
  3.48·10⁻²⁰; the proofs are repeated as comments at the corresponding lines of `cert_H0.py`.

**Cross-checks** (not used in any proof).
- **Another split.** `cert_H0.py` with the split at η₁ = 1.25 instead of 1 gives H_raw(0) = 0.0011355097894920618 ±
  3.057·10⁻⁹. `compare_outputs.py` checks that its seven split-independent values (𝒫, 2πM, H_raw(0), C, b₁, A,
  C/(32π²)) overlap those of the run with η₁ = 1.
- **The same route at s = 1/2 + it** (`cert_Ht.py`; Appendix A.2 of the paper). The changes from `cert_H0.py` are:
  - Q_s(η) = (1/2)·2^{s−2}(2πη)^{−s}Γ(s/2)²[1 − ₂F₁(s/2,s/2;1/2;−1/η²)] (Gradshteyn–Ryzhik 6.699.12 at μ = s);
  - 𝒫_s has x^{s−1} in place of x^{−1/2}; its tail x > 2000 is the exact ∫x^{s−3}/(32π⁴) plus explicit bounds, and
    [0, 10⁻⁶] in u is bounded explicitly;
  - |Q_s| ≤ Q is used in the end bounds;
  - H_raw(t) = M\[g_raw](s)/γ_∞(t)² with γ_∞(t)² = (1/4)s²(s−1)²π^{−s}Γ(s/2)².

  Every piece is complex, and the script certifies that the imaginary part of H_raw(t) contains 0. At t = 0 it reproduces
  `cert_H0.py`, and H(0) = C·H_raw(0) contains 1.
- **Comparison with the window certificate** (`compare_window.py`; Appendix A.2 of the paper). It compares
  R(t) = 2π²(t² + 1/4)²H_raw(t) from `cert_Ht.py` with R(t_c) of the window certificate (Theorem 7.10 of the paper;
  Section 3 here; `positivity/out/window_0_40.json`). The points are the 16 cell centres t_c = 0.25, 0.75, …, 7.75 and t_c = 10.25,
  15.25, 20.25, 30.25, 39.75, and all 21 pairs of balls overlap. The two routes share only the coefficient balls. The
  relative radius of the density route grows roughly like e^{2√(2πt)}: about 10⁻⁸ up to t ≈ 8, 3·10⁻⁵ at t = 20,
  1.3·10⁻² at t = 30 and 0.85 at t = 39.75.

**Inputs.** `coefficients/out/an_small_X1e4.json`, `coefficients/out/an_smalln_X3e5.json` and
`coefficients/out/an_smalln_X6e5.json` (Section 8; full hashes in `SHA256SUMS`). `cert_Ht.py` also reads C from
`coefficients/out/H0_cert.json`, and `compare_window.py` reads `positivity/out/window_0_40.json`. Scripts
`coefficients/cert_H0.py`, `coefficients/cert_Ht.py`, `coefficients/coefflib.py` (for K₀, K₁),
`coefficients/fix_json_radii.py`, `coefficients/compare_window.py` and `lib/besselk.py`. The logs print the hash prefixes
of the script and of the input files.

**Commands** (from this directory, after those of Section 8):

```sh
./runlog.sh coefficients/logs/cert_H0.log "$PY" -u coefficients/cert_H0.py 1 8
./runlog.sh coefficients/logs/cert_H0_eta1_1.25_crosscheck.log "$PY" -u coefficients/cert_H0.py 1.25 8 _eta1_1.25_crosscheck
for t in 0 0.25 0.75 1.25 1.75 2.25 2.75 3.25 3.75 4.25 4.75 5.25 5.75 6.25 6.75 7.25 7.75 10.25 15.25 20.25 30.25 39.75; do
  ./runlog.sh coefficients/logs/cert_Ht_t$t.log "$PY" -u coefficients/cert_Ht.py $t
done
./runlog.sh coefficients/logs/compare_window.log "$PY" coefficients/compare_window.py
./runlog.sh coefficients/logs/compare_outputs.log "$PY" coefficients/compare_outputs.py
```

The arguments of `cert_H0.py` are η₁, η₂ and a tag; the output file is `coefficients/out/H0_cert<tag>.json`. `cert_Ht.py`
takes t (optionally followed by η₁ and η₂).

**Expected output** (verbatim lines or parts of lines):
- `coefficients/logs/cert_H0.log`:
  - `DECISIVE: H_raw(0) = [0.00113551 +/- 2.07e-9]   (> 0: True)  => SIGN COHERENCE (C > 0)`
  - `DECISIVE: C = 1/H_raw(0) = [880.66 +/- 3.16e-3]`
  - `DECISIVE: b_1 = C a_1 = [4.03464e+6 +/- 8.98]`
  - `H_raw(0)   = 0.0011355097904015565291 +- 1.854e-09`
  - `C          = 880.66171550750732422 +- 1.441e-03`
- `coefficients/logs/cert_H0_eta1_1.25_crosscheck.log`:
  - `DECISIVE: H_raw(0) = [0.00113551 +/- 3.27e-9]   (> 0: True)  => SIGN COHERENCE (C > 0)`
  - `H_raw(0)   = 0.0011355097894920618273 +- 3.057e-09`
- `coefficients/logs/cert_Ht_t0.log`:
  - `DECISIVE: H_raw(t=0) = [0.00113551 +/- 2.07e-9] + [+/- 4.36e-13]j   (imag part should contain 0: True)`
  - `H(t) = C H_raw(t), C from H0_cert.json`, ending in `[880.66 +/- 3.16e-3]:  [1.0000 +/- 3.27e-6]`
- `coefficients/logs/compare_window.log`: `DECISIVE: 21/21 compared points overlap: True`
- `coefficients/logs/compare_outputs.log`: the two `DECISIVE` lines quoted in Section 8.

**Runtime** (one core per run). `cert_H0.py`: 88 s and 91 s. `cert_Ht.py`: 88–104 s per value of t; the 22 values took
4.8 minutes on 8 cores. `compare_window.py` and `compare_outputs.py`: under 1 s each.

## 10. Input files with SHA-256

| File | Content | SHA-256 |
|---|---|---|
| `coefficients/data/an_small_X1e4.json` | certified balls for a_n, n ≤ 60 (Kloosterman sums with c ≤ 10⁴ plus a tail bound); key `a_mid_rad` = [decimal midpoint, radius] | `59fe6e24647252db6cfa4e673b5ba89e741ed5c0b34b56e2db5cfe0c97aa546a` |
| `coefficients/data/an_cert_X1e4.json` | certified balls for a_n, n ≤ 1500 (key `a`), and the c = 1 terms (key `T1`, used only by the negative control) | `59d50f17db2199b1e9a039a616f1a9de51bfdf642549b25097c341e5e077b577` |
| `coefficients/data/extra_smalln_X3e5.json` | sharper certified balls for a_n, n ≤ 6 (Kloosterman sums with c ≤ 3·10⁵ plus a tail bound), {n: [midpoint, radius]} | `ff4b86318eed86f1badcde7e53c0c80f859f2cbee74a287d9493b2643d173e76` |
| `lib/besselk.py` | Part I library (byte-identical) | `3d3fd6601742c49b17fc355a0d9310474704ad480508010f91ae92615131501a` |
| `lib/common.py` | Part I library (byte-identical) | `d8e3056e04fdb144a8706bbc31ef0d3028860f21bd5dc09e0db9ee65aa14242a` |
| `lib/__init__.py` | Part I library (byte-identical, empty) | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `positivity/out/window_0_40.json` | per-cell output of the window run (Section 3) | `SHA256SUMS` |
| `coefficients/out/*.json` | outputs of the fresh runs of Sections 8 and 9; `an_small_X1e4.json`, `an_smalln_X3e5.json`, `an_smalln_X6e5.json` and `H0_cert.json` are read by `cert_H0.py` and `cert_Ht.py` | `SHA256SUMS` |

How the scripts read the coefficient files:
- Provenance. The numerical content of the three coefficient files is identical to that of the files consumed by the
  original certified runs, under the same file names. Before publication, one key of the `meta` field of
  `an_small_X1e4.json` and `an_cert_X1e4.json` was renamed to `hash_coefflib` (its value, the SHA-256 prefix of the
  coefficient library used for the original runs, is unchanged); nothing else changed, as a JSON comparison of the
  non-`meta` content confirms. Old → new SHA-256: `an_small_X1e4.json`
  `4f57199725f738543e4838f42597ada5d044012b27a89e6c6a8cc23a414a3c53` →
  `59fe6e24647252db6cfa4e673b5ba89e741ed5c0b34b56e2db5cfe0c97aa546a`; `an_cert_X1e4.json`
  `6ba6a52d9ae9e6291ebe6c2670f9513a7189809dace58ee520ea42fc15102555` →
  `59d50f17db2199b1e9a039a616f1a9de51bfdf642549b25097c341e5e077b577`; `extra_smalln_X3e5.json` is unchanged.
- Every consumer was re-run on the renamed files: Sections 3–7, `compare_outputs.py`, `compare_window.py` and Figure 1
  (Section 13). Every decisive line and every certified number is unchanged (`tools/logdiff.py` against the logs of the
  original runs reports differences only in the lines that print the input hashes, and the window JSON is identical up
  to timings); the Figure 1 files are reproduced byte for byte. The shipped logs are those of these re-runs.
- The `meta` fields record the SHA-256 prefixes of the original versions of the producing scripts, and write `Kc_n` for
  S_n.
- The scripts read every stored [midpoint, radius] pair as an Arb ball. They enlarge the radius to
  radius·(1 + 10⁻⁹) + |midpoint|·10⁻³⁰ and add the decimal-to-binary conversion error.
- For each n the sharpest of the available balls is used. Balls for the same n from different files must overlap,
  which is checked.
- Only n ≤ 300 are used; larger n go through the bound A0(n).

The coefficient balls themselves are certified in Section 8, where `compare_outputs.py` also checks, ball by ball, that a
fresh run reproduces the three pinned files.

## 11. Re-running and comparing with the shipped logs

From this directory, with `PY` set to a Python that has python-flint 0.9.0 (and numpy, for `coefficients/`):

```sh
export PY=python3
COEFF_EXTRA=coefficients/data/extra_smalln_X3e5.json ./runlog.sh positivity/logs/window_0_40.log "$PY" positivity/run_window.py 0 40 0.25 20 1 0_40
COEFF_EXTRA=coefficients/data/extra_smalln_X3e5.json ./runlog.sh positivity/logs/cert_large_t_T8.log "$PY" positivity/cert_large_t.py 8 0.5 1 0.87 4 2000 8000
COEFF_EXTRA=coefficients/data/extra_smalln_X3e5.json ./runlog.sh positivity/logs/cert_gtail.log "$PY" positivity/cert_gtail.py
./runlog.sh positivity/logs/check_r0.log "$PY" positivity/check_r0.py
./runlog.sh positivity/logs/negctl.log "$PY" positivity/negctl.py
```

These commands are those recorded in the first two lines (`# command`, `# env`) of the shipped logs. In total they take
about 3.5 minutes of wall time, most of it in `cert_large_t.py`; the window run uses 8 worker processes.

The coefficient certificates (Sections 8 and 9) are re-run with the commands of those sections, in this order:

```sh
./runlog.sh coefficients/logs/cert_an_X1e4.log "$PY" -u coefficients/cert_an.py 60 10000 1500 600 X1e4
./runlog.sh coefficients/logs/cert_small_n_X3e5.log "$PY" -u coefficients/cert_small_n.py 300000 10000 1,2,3,4,5,6 X3e5
./runlog.sh coefficients/logs/cert_small_n_X6e5.log "$PY" -u coefficients/cert_small_n.py 600000 10000 1,2 X6e5
./runlog.sh coefficients/logs/make_extra.log "$PY" coefficients/make_extra.py X3e5 X6e5
./runlog.sh coefficients/logs/analytic_constants.log "$PY" coefficients/analytic_constants.py
./runlog.sh coefficients/logs/check_kloost_fast.log "$PY" coefficients/check_kloost_fast.py
./runlog.sh coefficients/logs/cert_H0.log "$PY" -u coefficients/cert_H0.py 1 8
./runlog.sh coefficients/logs/cert_H0_eta1_1.25_crosscheck.log "$PY" -u coefficients/cert_H0.py 1.25 8 _eta1_1.25_crosscheck
for t in 0 0.25 0.75 1.25 1.75 2.25 2.75 3.25 3.75 4.25 4.75 5.25 5.75 6.25 6.75 7.25 7.75 10.25 15.25 20.25 30.25 39.75; do
  ./runlog.sh coefficients/logs/cert_Ht_t$t.log "$PY" -u coefficients/cert_Ht.py $t
done
./runlog.sh coefficients/logs/compare_window.log "$PY" coefficients/compare_window.py
./runlog.sh coefficients/logs/compare_outputs.log "$PY" coefficients/compare_outputs.py
```

Figure 1 (Section 13) is regenerated with `./runlog.sh figures/logs/make_figure1.log "$PY" figures/make_figure1.py`; this
needs numpy, scipy and matplotlib in addition, and takes a few seconds.

These runs are long:
- In sequence they take about 77 minutes of computing time. Most of it goes to the two runs of `cert_small_n.py`
  (12 and 23 minutes) and to the 22 runs of `cert_Ht.py` (88–104 s each).
- The shipped runs took 33 minutes of wall time. The two runs of `cert_small_n.py` ran in parallel, as did the two
  runs of `cert_H0.py`, and the runs of `cert_Ht.py` ran 8 at a time.
- `cert_an.py` writes the cache `coefficients/cache/kloost_tables_X10000.npz` (162 s) when it is absent, as in the
  shipped run. With the cache present it loads the file, and its log then reads `loaded from` instead of `built and
  saved` in that line.
- The log of `compare_window.py` prints the SHA-256 prefix of `positivity/out/window_0_40.json`. That prefix changes if
  the window run is repeated first in the same copy; `tools/logdiff.py` then reports this one line as different. Every
  other log of `coefficients/` should be `IDENTICAL` if `coefficients/cache/` is absent at the start.

The shipped runs were pinned with `taskset`: 8 cores for the window run and one core each for the others. Pinning,
precision and the number of workers affect only the running time, not the validity of a successful run.

A re-run overwrites `positivity/logs/*.log`, `positivity/out/window_0_40.json`, `coefficients/logs/*.log` and
`coefficients/out/*.json`. Run it on a copy of this directory (the first command is run from the parent directory) and
compare:

```sh
cp -r anc anc-rerun && cd anc-rerun && export PY=python3      # then the commands above
"$PY" tools/logdiff.py ../anc/positivity/logs positivity/logs                                   # every log: IDENTICAL
"$PY" tools/logdiff.py ../anc/positivity/out/window_0_40.json positivity/out/window_0_40.json   # IDENTICAL
"$PY" tools/logdiff.py ../anc/coefficients/logs coefficients/logs                               # IDENTICAL (see above)
```

The window JSON records per-cell timings (`secs`), so a re-run changes its SHA-256, and `sha256sum -c SHA256SUMS` then
reports it as `FAILED`. `tools/logdiff.py` ignores the `secs` fields. Every other shipped file is unchanged by a re-run;
the files in `coefficients/out/` contain no timings and are reproduced byte for byte.

**SHA256SUMS policy.** `SHA256SUMS` lists the full SHA-256 of every shipped file except the logs (`*/logs/*`), this
README and `lean/`, as `<hash>  ./relative/path` sorted by path, so that `sha256sum -c SHA256SUMS` works from this
directory. The cache `coefficients/cache/` is not shipped and not listed. `SHA256SUMS` is regenerated with:

```sh
find . -type f ! -path './lean/*' ! -path '*/logs/*' ! -path '*/__pycache__/*' ! -path './coefficients/cache/*' ! -name README.md ! -name SHA256SUMS -print0 | LC_ALL=C sort -z | xargs -0 sha256sum > SHA256SUMS
```

## 12. Software and hardware

- Python 3.10.12; python-flint 0.9.0, built on FLINT 3.6.0, which contains Arb. The header of every log records the
  versions actually used. The scripts of `coefficients/` also used numpy 2.2.6, which the log headers do not record.
- The scripts are deterministic. A re-run with the same versions reproduces each log except the date, the system line
  and the timings, and every field of the window JSON except `secs`; `tools/logdiff.py` checks both. With another numpy
  version or processor, the binary64 sums of `kloost_fast.py` may change in the last bits. Their proved error bound holds
  for any order of summation, so `compare_outputs.py` would then report overlapping rather than identical balls.
- Runtimes are wall times on an Intel Xeon Platinum 8362 (2.8 GHz) shared with other jobs.

## 13. Figure 1 of the paper (`figures/make_figure1.py`; an illustration, not a certificate)

**What it shows.** Panel (a): H(t) for 0 ≤ t ≤ 40 on a logarithmic scale, where H(t) = R(t)/(16(t² + 1/4)² R(0)). The
curve joins H(0) = 1 and the values at the 80 cell centres of certificate W, computed from the quadrature values R(t_c)
in `positivity/out/window_0_40.json` (without error terms). The steps are lower bounds for H on each cell, formed from
the certified cell lower bounds of the same file and the upper end of the certified enclosure of R(0) (Section 6), with
(t² + 1/4)² taken at the right end of the cell. The dashed curve is the bound R(t) ≥ 0.2554 e^{0.6435 t} of Theorem L
(Section 4), converted in the same way. Panel (b): e^{4π√x} Ĝ_H(x)/10⁶ for 1 ≤ x ≤ 6, where
Ĝ_H(x) = C sin²(πx) √x Σ_n a_n K₀(4π√(nx)) (Theorem 4 of the paper), in binary64 from the coefficient midpoints
(`coefficients/data/extra_smalln_X3e5.json` for n ≤ 6 and `coefficients/data/an_cert_X1e4.json` for n ≤ 1500; for
n > 1500 the term c = 1 of the Kloosterman series, whose relative error is far below binary64 precision) and the midpoint
of C in `coefficients/out/H0_cert.json`. At x = 1 the value is C/(32π²). For x > 1 the series is summed until the
remaining terms are below 10⁻¹⁷ of the total.

**Checks printed.** At n = 1500 the term c = 1 agrees with the certified midpoint to a relative 3.6·10⁻¹⁴; the value at
x = 1.004 is consistent with the value at x = 1; and the plotted values are non-negative.

**Inputs.** `positivity/out/window_0_40.json`, `coefficients/data/an_cert_X1e4.json` (`59d50f17db2199b1`),
`coefficients/data/extra_smalln_X3e5.json` (`ff4b86318eed86f1`), `coefficients/out/H0_cert.json`; the enclosure of R(0)
is a constant in the script (Section 6).

**Command** (from this directory; needs numpy, scipy and matplotlib):

```sh
./runlog.sh figures/logs/make_figure1.log "$PY" figures/make_figure1.py
```

**Output.** `figures/figure1_H.csv`, `figures/figure1_G.csv` and `figures/figure1.pdf`; with numpy 2.2.6, scipy 1.15.3 and
matplotlib 3.10.9 a re-run reproduces all three byte for byte (the PDF carries no creation date). Runtime: 3.6 s.
