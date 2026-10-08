/-
# The axiom ledger of Part II

Every input of the Part II spine that is not proved in Lean, and is not already an axiom of Part I's spine, is
an `axiom` in this file, and nowhere else.  `LEDGER.md` tabulates them.  There are two:

* `voronoi_decoupling` **[paper]**: Lemma "Voronoi decoupling" (`lem:voronoi`), parts (b) and (c), a statement
  about *every* function of the class `𝒲_δ`, `δ < 1/2`; no object is posited;
* `exists_integer_critical_object` **[paper + certificate + classical]**: the existence of the object `H` with
  exactly the four properties that the assembly uses.  It is one *joint* existence statement (as in Part I's
  ledger: no axiom about a chosen witness), so the classical inputs, the analytic steps and the certificates
  behind the four properties are listed in its docstring, property by property, with the decisive log lines.

Log lines are quoted verbatim from the logs shipped in the ancillary directory (paths relative to it, i.e. to
the parent directory of this Lean project), except that `±` stands for the logs' three-character plus-minus sign
(plus, slash, hyphen: slash followed by hyphen opens a comment in Lean) and that run times at the ends of lines
are omitted.  `scripts/check_provenance.py` checks every quoted line against the cited log and every cited
SHA-256 (prefix) against the cited file.  Statements of Part II are cited by name and LaTeX label.

The inputs from Part I (the explicit formula, the bound (4.1) for `Ξ`, Theorem 3.6, Theorem 2.9(b), the duality
theorem) are Part I's own ledger axioms or theorems, imported from its spine; they are not restated here.
-/
import PositivityRigidityII.Defs

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder

namespace PosRigII

open PosRig

/-- **[paper] Lemma "Voronoi decoupling" (`lem:voronoi`), parts (b) and (c).**  Let `0 < δ < 1/2` and `H ∈ 𝒲_δ`.
Then `G_H = γ_∞² H` is integrable on `ℝ`, and for every real `ξ`, `F = Ξ² H` satisfies
`F̂(ξ) = Σ_{m ≥ 1} d(m) m^{−1/2} Ĝ_H(ξ + ξ_m)`, the series converging absolutely.

Source: Part II, Lemma "Voronoi decoupling" (`lem:voronoi`): (b) gives `|G_H(z)| ≤ C (1 + |Re z|)^{−4+δ}` on `S_δ`,
hence the integrability of `G_H` on `ℝ`; (c) is the identity (eq:voronoi) with absolute convergence.  Part (a),
`Ξ² H ∈ 𝒯_δ`, is proved in Lean (`classW_inTδ`).  Proof in the paper: Stirling's formula, uniformly for
`Re s ∈ [−δ, 1 + δ]` (DLMF 5.11.9), gives `|γ_∞(s)|² ≍ |Im s|^{3 + Re s} e^{−π|Im s|/2}`; the line of integration of
`F̂(ξ)` moves to `Im w = −τ`, `τ ∈ (1/2, 1/2 + δ]` (Cauchy's theorem), where `ζ(1/2 + iw)² = Σ_m d(m) m^{−1/2−iw}`
converges absolutely; termwise integration (Fubini) and moving each line back to `ℝ` (`G_H` is analytic on
`−τ ≤ Im w ≤ 0`) give the `m`-th term.  The double pole of `ζ²` at `s = 1` is crossed only by `F` as a whole.  The
lemma was re-proved by an independent referee.

Faithful: a statement about every `H` of the class `𝒲_δ`, `δ < 1/2`; no object is posited.  Not stated: the
bounds of (b) for `G_H` and `Ĝ_H`, the reality and continuity of `Ĝ_H`, and the bound
`C_τ d(m) m^{−1/2−τ} e^{−2πτξ}` for the `m`-th term in (c). -/
axiom voronoi_decoupling {δ : ℝ} {H : ℂ → ℂ} (hH : ClassW δ H) (hδ : δ < 1 / 2) : VoronoiIdentity H

/-- **[paper + certificate + classical] The object: Theorem "The object" (`thm:main-object`) with
Corollary `cor:Pi-positive`, as used in the proof of Theorem `thm:main-S`.**  There is a function `H` (the paper's
`H_raw`) such that
1. `H ∈ 𝒲_δ` for some `δ ∈ (0, 1/2)`;
2. (C3) `Ĝ_H(ξ_k) = 0` for every integer `k ≥ 2`;
3. `Ĝ_H(ξ) ≥ 0` for every `ξ ≥ 0` (`x ≥ 1`; (C4) and more);
4. (C2), strictly: `H(t) > 0` for every real `t`.

Sources, property by property (Part II; `sec:assembly`, "Proof of Theorem `thm:main-S`", checks 1–4):
1. Proposition `prop:Hraw`: `H_raw(t) = −R(it)/(8π³(t² + 1/4)²)` (Definition `def:Hraw`) is entire, even and real on
   `ℝ` ((a)); `|H_raw(z)| ≤ C_δ (1 + |z|)^{−9+δ} e^{π|Re z|/2}` on `S_δ`, so `H_raw ∈ 𝒲_δ`, for every `δ ∈ (0, 1)` ((b));
   its Γ-only transform is `Ĝ_raw` ((c)).  The chain behind it: [classical] the odd Niebur–Poincaré series `P_ν`
   (Proposition `prop:niebur`; D. Niebur, 1973; J. Fay, 1977) and its Fourier expansion with Kloosterman sums of
   `J_{2ν}` and `I_{2ν}` and the constant `2` for every `Re ν > 1/2` (Theorem "Fourier expansion",
   `thm:niebur-fourier`, with Lemma "The Weyl-element integral", `lem:weyl`; compare K. Bringmann, J. Jorgenson,
   L. Smajlović, 2025, §2.4); [paper] Lemma "A Jordan block" (`lem:jordan`: `Φ̃ = ∂_ν[(2∂_v + ν²/v) P_ν]` at `ν = 1`
   is an exact eigenfunction with eigenvalue `1/4`), Proposition `prop:Pt`, Lemma "Symmetric-square equivariance"
   (`lem:sym2`) and Proposition `prop:sym2` (cusp expansions); Lemma "The Mellin transform of the kernel"
   (`lem:kernel-mellin`), Lemma "The four-path functional" (`lem:four-path`), Theorem "The lift" (`thm:lift`:
   the class member `𝒢 = −16π² Ĝ_raw` is analytic on `Re x > 0`, equals `−16π² sin²(πx) √x Σ_n a_n K₀(4π√(nx))` for
   `x > 1`, has `𝒢(1) = −1/2`, and its Mellin transform is `γ₀(w) R(w)` with `R(−w) = R(w)`); Lemma "Small `x`"
   (`lem:small-x`) and Lemma `lem:R-entire` (`R` entire and even, with double zeros at `w = ±1/2`).  [classical]
   Bessel and Mellin identities from DLMF and Gradshteyn–Ryzhik (Lemma `lem:K0K0`).
2. Proposition `prop:C3`(a): `Ĝ_raw(ξ_n) = ∂_ξ Ĝ_raw(ξ_n) = 0` for every integer `n ≥ 2` (Theorem `thm:lift`(f):
   `sin²(πn) = 0`, the series converging at every `x > 1`).
3. Theorem "Positivity of the coefficients" (`thm:an-positive`): `a_n = n𝒦_n + δ_{n1}/4 > 0` for every `n ≥ 1`, using only
   the trivial Kloosterman bound and no finite check (with Theorem "Two-sided bounds", `thm:an-bounds`); `K₀ > 0`; so
   `Ĝ_raw(x) = sin²(πx) √x Σ_n a_n K₀(4π√(nx)) ≥ 0` for `x > 1` (Theorem `thm:lift`(c)), and `Ĝ_raw(1) = 1/(32π²) > 0`
   (Proposition `prop:C3`(a)).
4. Corollary `cor:Pi-positive`: `Π(t) > 0`, hence `H_raw(t) > 0`, for every real `t`, from
   * Theorem "The physical-side formula" (`thm:F`): `H_raw(t) = Π(t)/(2π² (t² + 1/4)²)`,
     `Π(t) = ∫_1^∞ A(Y) cos(t log Y) dY + (1/2) ∫_{1/2}^∞ B(Y) k_t(θ(Y)) dY` with `A`, `B` the `K₀`-series in the `a_n` of
     (eq:AB), `θ(Y) = 2 arccot(2Y)` and the conical kernel `k_t` of (eq:ck); `Π` is even;
   * Theorem "Positivity of the kernel" (`thm:kernel-pos`; Mehler–Dirichlet's formula, DLMF 14.12.1);
   * Theorem "Window; computer-assisted" (`thm:window`): `Π(t) > 0` on `[0, 40]` (80 cells of width `1/2`, a Taylor model
     of degree 19 in `t` with a Cauchy remainder, Gauss–Legendre quadrature with Bernstein-ellipse error bounds, tails
     in `Y`, in the conical series and in `n`, all in Arb ball arithmetic).  Script `positivity/run_window.py`
     (sha256 f4e45fad77bd5b40…) with `positivity/cert_window.py` (sha256 9f6e359deabc174b…) and `positivity/poslib.py`
     (sha256 6d1830c291015d03…); log `positivity/logs/window_0_40.log`:
     `cell [0.0000, 0.5000]: R(tc)=[0.002192 ± 9.41e-7]  lower=[0.00112926259401 ± 1.26e-15]  ok=True`,
     `DECISIVE: R(t) > 0 on [0, 40] (all 80 cells certified): True`;
   * Theorem "Large `|t|`" (`thm:large-t`): `Π(t) ≥ 0.2554 e^{0.6435|t|}` for `|t| ≥ 8`, from Lemmas "Stirling bracket"
     (`lem:stirling`, DLMF §5.11(ii)), "Kernel bounds" (`lem:kernel-bounds`), "Signs of `B`" (`lem:B-sign`; DLMF §10.40(ii)
     for `K₀`), `lem:comparison` and the six numbers of Proposition "Computer-assisted" (`prop:L-numbers`).  Script
     `positivity/cert_large_t.py` (sha256 11a38aac755bf0ef…); log `positivity/logs/cert_large_t_T8.log`:
     `th_s = [0.9272952180 ± 1.62e-12], th(Yz) = [1.043236594 ± 1.93e-10], t_mono = [4.3125243 ± 1.90e-8]`,
     `(1a) min lower bound of g on [Yz, Ys] = [0.581726 ± 3.27e-7]  (> 0 needed)`,
     `(1b) min lower bound of g on [Ys, Y3] = [1.74105e-7 ± 7.7e-16] ; p(T0) >= [2.22681094932 ± 1.09e-12]`,
     `(2) n(T0) <= [1.93894945416 ± 1.93e-12]  (7009 cells with possible g < 0)`,
     `(3) A_Phi = int_1^oo Phi in [5.5848933 ± 6.46e-8]  (quad err <= [2.51e-17 ± 4.88e-20], Y-tail <= [5.02e-32 ± 8.03e-36]): A_Phi <= [5.58489336212 ± 3.21e-12]`,
     `p(T0) >= [2.22681094932 ± 1.09e-12] ; n(T0) <= [1.93894945416 ± 1.93e-12] ; A_Phi e^{-T0(pi/2-th_s)} <= [0.0324536120224 ± 3.66e-14] ; margin = [0.255407883141 ± 3.57e-13] ; ratio p/(n + axis term) >= [1.12956 ± 3.61e-6]`,
     `DECISIVE (all-Arb): Theorem L hypotheses verified for T0 = 8: True`;
     and script `positivity/cert_gtail.py` (sha256 5601d7dc6c5f48b8…), log `positivity/logs/cert_gtail.log`:
     `rhobar(4) = [4.198895694e-9 ± 1.65e-19]  (< 1 needed): True`, `DECISIVE: g > 0 on [4, oo): True`;
   * `[0, 40] ∪ [8, ∞) ⊇ [0, ∞)` and `Π` is even.  (Also certified, and not needed for the sign of `H_raw`: `Π(0)`,
     script `positivity/check_r0.py` (sha256 ab3b7412b7b452de…), log `positivity/logs/check_r0.log`:
     `[certified] R(0) in [[0.001400011269 ± 2.50e-13], [0.001401746815 ± 4.55e-13]] ; H_raw(0) = 8 R(0)/pi^2 in [0.00114 ± 5.20e-6]`.)
   The logs write `R` for `Π`, `Phi` for `A` and `g` for `B`; a SHA-256 ending in `…` is the 16-hex-digit prefix that
   the logs record.  Inputs of both certificates: the certified balls for the
   `a_n`, `n ≤ 300`, in `coefficients/data/an_small_X1e4.json`
   (sha256 59fe6e24647252db6cfa4e673b5ba89e741ed5c0b34b56e2db5cfe0c97aa546a), `coefficients/data/an_cert_X1e4.json`
   (sha256 59d50f17db2199b1e9a039a616f1a9de51bfdf642549b25097c341e5e077b577) and
   `coefficients/data/extra_smalln_X3e5.json` (sha256 ff4b86318eed86f1badcde7e53c0c80f859f2cbee74a287d9493b2643d173e76);
   the bound `|a_n| ≤ ā_n` of Theorem `thm:an-bounds`; and Part I's rigorous `K₀`, `lib/besselk.py`
   (sha256 3d3fd6601742c49b17fc355a0d9310474704ad480508010f91ae92615131501a).  The certificates were audited by an
   independent referee, whose own all-Arb reruns agree (80 of 80 cells; the margin of Theorem `thm:large-t`
   `0.2554078831 ± 4.1e-11`).

Weaker than the paper: only one `δ` is asserted (the paper has every `δ < 1`, and the exponent `−9 + δ`); `H` entire,
the formula for `Ĝ_H` and the double zeros of `Ĝ_H` are not stated; the normalisation `H(0) = 1` is not part of the
axiom (it is derived in Lean, `exists_object`).  Everything that the spine derives from this axiom (`H(0) = 1` after
scaling, (C4), (C5), `F = Ξ² H ∈ 𝒞_OPS ⊆ 𝒞`, `F̂(ξ_n) = 0`, `∫ F > 0`, `𝒜(F) = 0`, and Theorems S and U) is proved
in Lean. -/
axiom exists_integer_critical_object :
    ∃ H : ℂ → ℂ, (∃ δ : ℝ, δ < 1 / 2 ∧ ClassW δ H) ∧ CondC3 H ∧ CondC4Zero H ∧ CondC2Strict H

end PosRigII
