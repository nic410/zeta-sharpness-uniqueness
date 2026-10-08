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
3. `Ĝ_H(ξ) ≥ 0` for every `ξ ≥ 0` (`x ≥ 1`; (C4) and more), and `Ĝ_H(ξ) > 0` for `0 ≤ ξ < ξ₂` (`1 ≤ x < 2`, the
   window);
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
   (Proposition `prop:C3`(a)).  The window clause: for `1 < x < 2` every factor of that formula is positive
   (`sin²(πx) > 0` as `x ∉ ℤ`, every `a_n > 0`, `K₀ > 0`, the series converging, so its sum is at least
   `a_1 K₀(4π√x) > 0`), and at `x = 1` the value is `1/(32π²) > 0`; this is the proof of part (a) of Corollary 8.2
   (`cor:nogap`, "The classical cone"), from Theorem "The object" (`thm:main-object`(a),(b)) and Theorem "Positivity
   of the coefficients" (`thm:an-positive`), independently refereed.
4. Corollary 7.12 (`cor:Pi-positive`): `Π(t) > 0`, hence `H_raw(t) > 0`, for every real `t`.  The proof of Corollary 7.12
   (the primary path):
   * Theorem 7.3 "The physical-side formula" (`thm:F`): `H_raw(t) = Π(t)/(2π² (t² + 1/4)²)`,
     `Π(t) = ∫_1^∞ A(Y) cos(t log Y) dY + (1/2) ∫_{1/2}^∞ B(Y) k_t(θ(Y)) dY` with `A`, `B` the `K₀`-series in the `a_n` of
     (eq:AB), `θ(Y) = 2 arccot(2Y)` and the conical kernel `k_t` of (eq:ck), positive by Theorem 7.2 "Positivity of the
     kernel" (`thm:kernel-pos`; Mehler–Dirichlet's formula, DLMF 14.12.1); `Π` is even;
   * Theorem 6.8 "Moment certificate" (`thm:moments`, Certificate M-box), with Lemma 6.7 "Moment minorant"
     (`lem:moments`) and Proposition 6.5 "Positive definiteness" (`prop:posdef`): `H_raw(t) > 0` for `|t| ≤ 10.355`, the
     coefficients entering only through the trivial-bound box `TB` of (6.1) (`eq:box`: `|a_n − c_n| ≤ w_n`, from the
     trivial Kloosterman bound in the proof of Theorem 6.1).  Script `positivity/cert_moments_box.py`
     (sha256 b7b795195be452fafa58f24d9bb07f06772e018d10e5cbb59a92b27de65a9a38) with `positivity/cert_moments.py`
     (sha256 22be4eba843685fafad7bc78ceccd67f57f9b0018f5686d0543bade891389940) and `positivity/boxlib.py`
     (sha256 3d42eb955f76f78118470367183d02d44ff69115e9189256efdbadeddbe94b93); log `positivity/logs/cert_moments_box.log`:
     `eps = max_{n0<n<=N} w_n/(c_n - w_n) = [1.7331e-8 ± 1.33e-14]`,
     `box moment bound with M_0..M_30: lower bound of P_K(t; b) > 0 for every b in the box, on [0, 10.35546875]`,
     `DECISIVE (Certificate M-box, trivial Kloosterman bound only): P_K(t; b) > 0 for every b in the box, hence (b = a) F(t) = Xi(t)^2 H_raw(t) > 0 and H_raw(t) > 0, for |t| <= 10.35546875 (moments M_0..M_30) ; covers [0, 9]: True`;
   * Theorem 7.11 "Large `|t|` from the trivial bound" (`thm:large-t-box`): `Π(t) ≥ 0.9659 e^{0.6435|t|}` for `|t| ≥ 9`,
     for every sequence in `TB`, from Lemmas 7.5 "Stirling bracket" (`lem:stirling`, DLMF §5.11(ii)), 7.6 "Kernel bounds"
     (`lem:kernel-bounds`), 7.7 "Signs of `B`" (`lem:B-sign`; DLMF §10.40(ii) for `K₀`), 7.8 (`lem:comparison`) and the numbers
     of Proposition 7.10 (`prop:L-numbers-box`); it also gives the explicit lower bound for `|t| ≥ 9` (constant `0.9659`)
     in the statement of Corollary 7.12, which this axiom does not use.  Script `positivity/run_on_box.py`
     (sha256 916b9bbef306d6086cbe0a3adef023177b1f5047b6c6e0dc26aeeb8db6d77785), which runs the unchanged
     `positivity/cert_large_t.py` (sha256 11a38aac755bf0efe400f53c5437021c61ef865fec4235a8fb5b5f4b136e6b22) and
     `positivity/cert_gtail.py` (sha256 5601d7dc6c5f48b8b6f3c21b3e9da89e731013cf3c418899291ab9e454df15f2) on `TB`;
     log `positivity/logs/cert_large_t_T9_box.log`:
     `box: a_1 in [[4425.193206 ± 1.10e-7], [4707.097194 ± 4.72e-7]], a_2 in [[1024479.78541 ± 3.69e-6], [1027350.95717 ± 4.25e-6]] ; every box hull for n <= 300 lies in (0, A0(n)): True`,
     `p(T0) >= [2.69351335258 ± 2.81e-12] ; n(T0) <= [1.71015174683 ± 4.54e-12] ; A_Phi e^{-T0(pi/2-th_s)} <= [0.0174114696412 ± 4.28e-14] ; margin = [0.965950136102 ± 4.98e-13] ; ratio p/(n + axis term) >= [1.55914 ± 2.55e-7]`,
     `DECISIVE (all-Arb): Theorem L hypotheses verified for T0 = 9: True`;
     log `positivity/logs/cert_gtail_box.log`:
     `rhobar(4) = [4.347086309e-9 ± 7.56e-20]  (< 1 needed): True`, `DECISIVE: g > 0 on [4, oo): True`;
   * `[0, 10.355] ∪ [9, ∞) ⊇ [0, ∞)` and `Π` is even.
   Independent checks, not used in the proof of Corollary 7.12 (the same statements with the certified coefficient
   enclosures in place of `TB`):
   * Theorem 7.13 "Window; computer-assisted" (`thm:window`, Certificate W): `Π(t) > 0` on `[0, 40]` (80 cells, Taylor
     models in `t`, Arb ball arithmetic).  Script `positivity/run_window.py`
     (sha256 f4e45fad77bd5b4065cdc8a32a41f4c2d7c2e628c6253bdf5304139322d4e71c) with `positivity/cert_window.py`
     (sha256 9f6e359deabc174b925347a308eca36831587a34c1c748d4fed75f48f5087bca) and `positivity/poslib.py`
     (sha256 6d1830c291015d03ed43e8811af463e08689a27638da28145ac7b7c8ece73a50); log `positivity/logs/window_0_40.log`:
     `cell [0.0000, 0.5000]: R(tc)=[0.002192 ± 9.41e-7]  lower=[0.00112926259401 ± 1.26e-15]  ok=True`,
     `DECISIVE: R(t) > 0 on [0, 40] (all 80 cells certified): True`;
   * Theorem 7.4 "Large `|t|`" (`thm:large-t`, `T₀ = 8`, certified coefficients), from Proposition 7.9 (`prop:L-numbers`);
     log `positivity/logs/cert_large_t_T8.log`:
     `margin = [0.255407883141 ± 3.57e-13]`,
     `DECISIVE (all-Arb): Theorem L hypotheses verified for T0 = 8: True`;
     log `positivity/logs/cert_gtail.log`:
     `rhobar(4) = [4.198895694e-9 ± 1.65e-19]  (< 1 needed): True`, `DECISIVE: g > 0 on [4, oo): True`;
   * Certificate M with the certified enclosures (the remark after Theorem 6.8): output
     `positivity/out/moments_true_N1500_p128.json` (sha256 0fe5c48adfd2f1d4563eff6cd9711af3fa714666056e3e4861e8667dfef2ef6a);
     log `positivity/logs/cert_moments_true.log`:
     `DECISIVE (Certificate M, mode=true): F(t) = Xi(t)^2 H_raw(t) > 0, hence H_raw(t) > 0, for |t| <= 10.40234375 (moments M_0..M_30) ; covers [0, 9]: True`;
   * `Π(0)`, script `positivity/check_r0.py` (sha256 ab3b7412b7b452de2b184ce5d6f119760b170bb01faab949eca85153551c629c),
     log `positivity/logs/check_r0.log`:
     `[certified] R(0) in [[0.001400011269 ± 2.50e-13], [0.001401746815 ± 4.55e-13]] ; H_raw(0) = 8 R(0)/pi^2 in [0.00114 ± 5.20e-6]`.
   The logs write `R` for `Π`, `Phi` for `A`, `g` for `B` and "Theorem L" for the large-`|t|` theorems.  Inputs of the
   certificates: the coefficient data `coefficients/data/an_small_X1e4.json`
   (sha256 59fe6e24647252db6cfa4e673b5ba89e741ed5c0b34b56e2db5cfe0c97aa546a), `coefficients/data/an_cert_X1e4.json`
   (sha256 59d50f17db2199b1e9a039a616f1a9de51bfdf642549b25097c341e5e077b577) and
   `coefficients/data/extra_smalln_X3e5.json` (sha256 ff4b86318eed86f1badcde7e53c0c80f859f2cbee74a287d9493b2643d173e76);
   the bounds of Theorems 6.1–6.2 (`thm:an-positive`, `thm:an-bounds`), which define `TB`; and Part I's rigorous `K₀`,
   `lib/besselk.py` (sha256 3d3fd6601742c49b17fc355a0d9310474704ad480508010f91ae92615131501a).  The SHA-256 values are
   those of the ancillary `SHA256SUMS`.  The certificates were refereed independently.

Weaker than the paper: only one `δ` is asserted (the paper has every `δ < 1`, and the exponent `−9 + δ`); `H` entire,
the formula for `Ĝ_H` and the double zeros of `Ĝ_H` are not stated; the normalisation `H(0) = 1` is not part of the
axiom (it is derived in Lean, `exists_object`).  Everything that the spine derives from this axiom (`H(0) = 1` after
scaling, (C4), (C5), `F = Ξ² H ∈ 𝒞_OPS ⊆ 𝒞`, `F̂(ξ_n) = 0`, `∫ F > 0`, `𝒜(F) = 0`, `F̂ > 0` on `(−ξ₂, ξ₂)`, Theorems S
and U, Corollary 3 and Corollary 8.2) is proved in Lean.  The window clause of property 3 was added for Corollary 8.2
(an added conjunct of the same axiom; it is used only in `NoGap.lean`). -/
axiom exists_integer_critical_object :
    ∃ H : ℂ → ℂ, (∃ δ : ℝ, δ < 1 / 2 ∧ ClassW δ H) ∧ CondC3 H ∧ CondC4Zero H ∧ CondWindow H ∧
      CondC2Strict H

end PosRigII
