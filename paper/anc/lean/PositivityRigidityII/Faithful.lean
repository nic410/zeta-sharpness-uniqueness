/-
Faithfulness and sanity checks of the definitions of `Defs.lean`, and elementary facts about them (Mathlib, and
Zeta23 through Part I's `Zeta.lean`; no ledger axiom of Part I or Part II).

* `γ_∞` is the paper's: `γ_∞(s) = ½ s(s−1) Γ_ℝ(s)` for `s ≠ 0`, `γ_∞(0) = −1`, and `Ξ(t) = γ_∞(½ + it) ζ(½ + it)` on
  the real line (so `G_H = γ_∞² H` is the Γ-factor part of `F = Ξ² H`, as in (eq:GH));
* the class `𝒲_δ` is not empty: it contains the constant `1` (then `Ξ² H = Ξ²`), which is positive on `ℝ`; so the
  hypothesis of the ledger axiom `voronoi_decoupling` can be met;
* `𝒲_δ` and the conditions (C2)–(C4) are invariant under positive scaling (`ClassW.smul`, `GammaFT_smul`);
* identity theorem: an `H ∈ 𝒲_δ` that is not identically zero on `S_δ` has a real point with `H(t) ≠ 0`;
* the indexing of the Voronoi series: the term `m = 0` vanishes and the term `m = 1` is `Ĝ_H(ξ)`; `ξ_m ≥ 0`;
  `ξ_n + ξ_m = ξ_{nm}` (the arithmetic behind "`F̂` vanishes at the integers where `Ĝ_H` vanishes");
* a real-valued function `≥ 0` has derivative `0` (if any) at each of its zeros.
-/
import PositivityRigidityII.Defs

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder

namespace PosRigII

open PosRig

/-! ## `γ_∞` -/

/-- `γ_∞(s) = ½ s(s−1) π^{−s/2} Γ(s/2) = ½ s(s−1) Γ_ℝ(s)` for `s ≠ 0` (at `s = 0` the right-hand side has a
removable singularity, where Mathlib's `Γ(0)` is the junk value `0`). -/
theorem gammaInf_eq_gammaR {s : ℂ} (hs : s ≠ 0) :
    gammaInf s = s * (s - 1) / 2 * Complex.Gammaℝ s := by
  have h2 : s / 2 ≠ 0 := div_ne_zero hs two_ne_zero
  unfold gammaInf
  rw [Complex.Gamma_add_one _ h2, Complex.Gammaℝ_def]
  ring

/-- `γ_∞(0) = −1`: the Lean function has the true value at the removable singularity. -/
theorem gammaInf_zero : gammaInf 0 = -1 := by
  simp [gammaInf, Complex.Gamma_one]

/-- `Ξ(t) = γ_∞(½ + it) ζ(½ + it)` for real `t`: `Ξ = γ_∞ ζ`, as in the paper. -/
theorem Xi_eq_gammaInf_mul_zeta (t : ℝ) :
    Xi t = gammaInf (1 / 2 + I * t) * riemannZeta (1 / 2 + I * t) := by
  set s : ℂ := 1 / 2 + I * t with hs
  have hre : s.re = 1 / 2 := by simp [hs]
  have hG : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by rw [hre]; norm_num)
  have h1 : s ≠ 1 := fun h => by rw [h] at hre; norm_num at hre
  have h0 : s ≠ 0 := fun h => by rw [h] at hre; norm_num at hre
  show xiR s = gammaInf s * riemannZeta s
  rw [xiR_eq hG h1, gammaInf_eq_gammaR h0]

/-- On the real line, `F(t) = Ξ(t)² H(t) = G_H(t) ζ(½ + it)²`. -/
theorem Xi_sq_mul_eq_GammaOnly_mul (H : ℂ → ℂ) (t : ℝ) :
    Xi t ^ 2 * H t = GammaOnly H t * riemannZeta (1 / 2 + I * t) ^ 2 := by
  rw [Xi_eq_gammaInf_mul_zeta, GammaOnly]
  ring

/-! ## The class `𝒲_δ` -/

/-- The constant function `1` lies in `𝒲_δ` for every `0 < δ < 1` (`(1 + |z|)⁸ ≤ C e^{π|Re z|/2}` on the strip),
and it is positive on `ℝ`.  So the hypothesis of `voronoi_decoupling` can be met (for `H = 1` it is the classical
Voronoi summation for `Ξ²`). -/
theorem one_classW {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) : ClassW δ (fun _ => 1) where
  pos := h0
  lt_one := h1
  even := fun _ _ => rfl
  real := fun _ => by simp
  analytic := fun _ _ => analyticAt_const
  bound := by
    obtain ⟨K, hK0, hK⟩ := poly_exp_le_inv_sq (c := Real.pi / 2) (by positivity) 8
    refine ⟨3 ^ 8 * K, fun z hz => ?_⟩
    have hy : |z.im| ≤ 1 / 2 + δ := hz
    have hy' : |z.im| ≤ 3 / 2 := by linarith
    set x := z.re with hx
    have hnorm : 1 + ‖z‖ ≤ 3 * (1 + |x|) := by
      have := Complex.norm_le_abs_re_add_abs_im z
      have : 0 ≤ |x| := abs_nonneg x
      linarith
    have hKx := hK x
    have hinv : (1 + x ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])
    have hpoly : (1 + |x|) ^ 8 ≤ K * Real.exp (Real.pi / 2 * |x|) := by
      have h2 : (1 + |x|) ^ 8 * Real.exp (-(Real.pi / 2) * |x|) ≤ K := by
        calc (1 + |x|) ^ 8 * Real.exp (-(Real.pi / 2) * |x|) ≤ K * (1 + x ^ 2)⁻¹ := hKx
          _ ≤ K * 1 := by gcongr
          _ = K := mul_one K
      have hexp : Real.exp (-(Real.pi / 2) * |x|) * Real.exp (Real.pi / 2 * |x|) = 1 := by
        rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
      calc (1 + |x|) ^ 8 = (1 + |x|) ^ 8 * Real.exp (-(Real.pi / 2) * |x|) *
            Real.exp (Real.pi / 2 * |x|) := by rw [mul_assoc, hexp, mul_one]
        _ ≤ K * Real.exp (Real.pi / 2 * |x|) := by gcongr
    rw [norm_one, mul_one]
    calc (1 + ‖z‖) ^ 8 ≤ (3 * (1 + |x|)) ^ 8 := by gcongr
      _ = 3 ^ 8 * (1 + |x|) ^ 8 := by ring
      _ ≤ 3 ^ 8 * (K * Real.exp (Real.pi / 2 * |x|)) := by gcongr
      _ = 3 ^ 8 * K * Real.exp (Real.pi / 2 * |x|) := by ring

/-- The constant `1` is positive on `ℝ` (the strict form of (C2)). -/
theorem one_condC2Strict : CondC2Strict (fun _ => 1) := fun _ => one_pos

/-- `𝒲_δ` is closed under multiplication by real constants. -/
theorem ClassW.smul {δ : ℝ} {H : ℂ → ℂ} (hH : ClassW δ H) (c : ℝ) :
    ClassW δ (fun z => (c : ℂ) * H z) where
  pos := hH.pos
  lt_one := hH.lt_one
  even := fun z hz => by simp only [hH.even z hz]
  real := fun t => by simp [Complex.mul_im, hH.real t]
  analytic := analyticOnNhd_const.mul hH.analytic
  bound := by
    obtain ⟨C, hC⟩ := hH.bound
    refine ⟨|c| * C, fun z hz => ?_⟩
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc (1 + ‖z‖) ^ 8 * (|c| * ‖H z‖) = |c| * ((1 + ‖z‖) ^ 8 * ‖H z‖) := by ring
      _ ≤ |c| * (C * Real.exp (Real.pi / 2 * |z.re|)) :=
          mul_le_mul_of_nonneg_left (hC z hz) (abs_nonneg c)
      _ = |c| * C * Real.exp (Real.pi / 2 * |z.re|) := by ring

/-- The Γ-only transform is linear: `Ĝ_{cH} = c Ĝ_H`. -/
theorem GammaFT_smul (H : ℂ → ℂ) (c : ℂ) (ξ : ℝ) :
    GammaFT (fun z => c * H z) ξ = c * GammaFT H ξ := by
  have h : GammaOnly (fun z => c * H z) = fun z => c * GammaOnly H z := by
    funext z
    simp only [GammaOnly]
    ring
  unfold GammaFT
  rw [h, FT_smul]

/-- The closed strip `{|Im z| ≤ b}` is convex. -/
theorem convex_closedStrip (b : ℝ) : Convex ℝ (closedStrip b) := by
  have h : closedStrip b = Complex.imLm ⁻¹' Set.Icc (-b) b := by
    ext z
    simp [closedStrip, abs_le]
  rw [h]
  exact (convex_Icc (-b) b).linear_preimage Complex.imLm

/-- **Identity theorem for `𝒲_δ`.**  If `H ∈ 𝒲_δ` is not identically zero on `S_δ` (`H ≢ 0`), then `H(t) ≠ 0` for
some real `t`. -/
theorem ClassW.exists_real_ne_zero {δ : ℝ} {H : ℂ → ℂ} (hH : ClassW δ H)
    (hne : ∃ z ∈ closedStrip (1 / 2 + δ), H z ≠ 0) : ∃ t : ℝ, H t ≠ 0 := by
  by_contra hall
  push Not at hall
  obtain ⟨z₁, hz₁, hHz₁⟩ := hne
  have h0 : (0 : ℂ) ∈ closedStrip (1 / 2 + δ) := by
    show |(0 : ℂ).im| ≤ 1 / 2 + δ
    rw [Complex.zero_im, abs_zero]
    linarith [hH.pos]
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), H z = 0 := by
    intro hev
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
    obtain ⟨ε, hε, hball⟩ := hev
    have hpos : 0 < ε / 2 := by positivity
    have hmem : ((ε / 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
    have hd : dist ((ε / 2 : ℝ) : ℂ) 0 < ε := by
      rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      linarith
    exact hball hd hmem (hall (ε / 2))
  have hEq := hH.analytic.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_closedStrip _).isPreconnected h0 hfreq
  exact hHz₁ (hEq hz₁)

/-! ## The indexing of the Voronoi series -/

/-- `ξ_m = log m/2π ≥ 0` for every natural number `m` (`ξ_0 = 0` by Mathlib's `log 0 = 0`). -/
theorem xiOf_natCast_nonneg (m : ℕ) : 0 ≤ xiOf m := by
  unfold xiOf
  rcases Nat.eq_zero_or_pos m with h | h
  · simp [h]
  · exact div_nonneg (Real.log_nonneg (by exact_mod_cast h)) (by positivity)

/-- `ξ_n + ξ_m = ξ_{nm}` for `n, m ≥ 1`. -/
theorem xiOf_add_natCast {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    xiOf n + xiOf m = xiOf ((n * m : ℕ) : ℝ) := by
  unfold xiOf
  rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hn) (by exact_mod_cast hm), add_div]

/-- The coefficient `d(m) m^{−1/2}` of the Voronoi series is non-negative. -/
theorem voronoiCoeff_nonneg (m : ℕ) :
    0 ≤ (((ArithmeticFunction.sigma 0 m : ℕ) : ℝ) / Real.sqrt m : ℝ) := by
  positivity

/-- The term `m = 0` of the Voronoi series vanishes (`σ₀(0) = 0`): the series runs over `m ≥ 1`. -/
theorem voronoiTerm_zero (H : ℂ → ℂ) (ξ : ℝ) : voronoiTerm H ξ 0 = 0 := by
  simp [voronoiTerm]

/-- The term `m = 1` of the Voronoi series is `Ĝ_H(ξ)` (`d(1) = 1`, `ξ_1 = 0`). -/
theorem voronoiTerm_one (H : ℂ → ℂ) (ξ : ℝ) : voronoiTerm H ξ 1 = GammaFT H ξ := by
  simp [voronoiTerm, xiOf, ArithmeticFunction.sigma_apply]

/-! ## Derivatives at zeros of a non-negative function -/

/-- If `f : ℝ → ℂ` is `≥ 0` everywhere (real and non-negative) and `f(x₀) = 0`, then every derivative of `f` at `x₀`
is `0`: `x₀` is a minimum of `Re f`, and `Im f ≡ 0`. -/
theorem hasDerivAt_eq_zero_of_nonneg {f : ℝ → ℂ} {x₀ : ℝ} (hnn : ∀ x, 0 ≤ f x) (h0 : f x₀ = 0)
    {D : ℂ} (hD : HasDerivAt f D x₀) : D = 0 := by
  have hre : HasDerivAt (fun x => (f x).re) D.re x₀ := by
    have C : HasFDerivAt Complex.re Complex.reCLM (f x₀) := Complex.reCLM.hasFDerivAt
    simpa using! (C.comp x₀ hD.hasFDerivAt).hasDerivAt
  have him : HasDerivAt (fun x => (f x).im) D.im x₀ := by
    have C : HasFDerivAt Complex.im Complex.imCLM (f x₀) := Complex.imCLM.hasFDerivAt
    simpa using! (C.comp x₀ hD.hasFDerivAt).hasDerivAt
  have hmin : IsLocalMin (fun x => (f x).re) x₀ :=
    Filter.Eventually.of_forall fun x => by
      show (f x₀).re ≤ (f x).re
      rw [h0, Complex.zero_re]
      exact (Complex.nonneg_iff.mp (hnn x)).1
  have h1 : D.re = 0 := hmin.hasDerivAt_eq_zero hre
  have himc : (fun x => (f x).im) = fun _ => (0 : ℝ) := by
    funext x
    exact ((Complex.nonneg_iff.mp (hnn x)).2).symm
  rw [himc] at him
  have h2 : D.im = 0 := him.unique (hasDerivAt_const x₀ (0 : ℝ))
  exact Complex.ext h1 h2

end PosRigII
