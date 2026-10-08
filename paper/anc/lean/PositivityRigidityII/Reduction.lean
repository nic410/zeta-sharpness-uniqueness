/-
Section "Reduction to a Γ-only integer-critical function" (`sec:reduction`) of Part II, proved in Lean.

* `classW_inTδ` — Lemma "Voronoi decoupling" (`lem:voronoi`), part (a): `H ∈ 𝒲_δ`, `δ < 1/2` ⇒ `F = Ξ² H ∈ 𝒯_δ`.
  From Part I's bound (4.1) for `Ξ` (Part I ledger axiom `xi_decay`) with `b = 1/2 + δ < 1`: the exponential factors
  cancel exactly, and the exponent `8` of (C1) is what `(1 + |Re z|)⁶` needs.
* The transfer from `Ĝ_H` to `F̂` through the Voronoi series, *given* the Voronoi identity (`VoronoiIdentity`, the
  conclusion of the ledger axiom `voronoi_decoupling`), uses no axiom beyond Mathlib's:
  `Ĝ_H ≥ 0` on `[a, ∞)` ⇒ `F̂ ≥ 0` on `[a, ∞)` (every `ξ + ξ_m ≥ ξ`); (C3) ⇒ `F̂(ξ_n) = 0` for every `n ≥ 2`
  (`ξ_n + ξ_m = ξ_{nm}`); (C3) ⇒ `F̂(0) = Ĝ_H(0)`.
* `Arch_eq_zero_of_FT_vanish`: Part I's Corollary 4.4 (`zero_killing_EF`, from the explicit formula) and
  `F̂(ξ_n) = 0` at every prime power give `𝒜(F) = 0`.
* `reduction` — Proposition "Exact magic functions from Γ-only data" (`prop:reduction`): for `H ∈ 𝒲_δ`, `δ < 1/2`,
  `H ≢ 0`, with (C2)–(C4): `F ∈ 𝒞`, `F̂(ξ_n) = 0` (`n ≥ 2`), `∫ F = F̂(0) = Ĝ_H(0) > 0`, `𝒜(F) = 0`, `F` is an exact
  magic function and `κ* ≤ 0`; `reduction_OPS`: if moreover `Ĝ_H ≥ 0` on `[0, ∞)`, then `F ∈ 𝒞_OPS` and `κ*_OPS ≤ 0`.
-/
import PositivityRigidityII.Ledger
import PositivityRigidityII.Faithful

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder

namespace PosRigII

open PosRig

/-! ## Lemma "Voronoi decoupling", part (a): `H ∈ 𝒲_δ ⇒ Ξ² H ∈ 𝒯_δ` -/

/-- **Lemma "Voronoi decoupling" (`lem:voronoi`), (a).**  If `0 < δ < 1/2` and `H ∈ 𝒲_δ`, then `F = Ξ² H ∈ 𝒯_δ`: on
`S_δ`, `|F(z)| ≤ C_b² (1 + |Re z|)⁶ e^{−π|Re z|/2} · C_H (1 + |z|)^{−8} e^{π|Re z|/2} ≤ C (1 + |z|)^{−2}`. -/
theorem classW_inTδ {δ : ℝ} {H : ℂ → ℂ} (hH : ClassW δ H) (hδ : δ < 1 / 2) :
    InTδ δ (fun z => Xi z ^ 2 * H z) := by
  obtain ⟨CX, hCX⟩ := xi_decay (1 / 2 + δ) (by linarith [hH.pos]) (by linarith)
  obtain ⟨CH, hCH⟩ := hH.bound
  refine ⟨hH.pos, hδ, ?_, ?_, ?_, ?_⟩
  · intro z hz
    simp only [Xi_even, hH.even z hz]
  · intro t
    have hX : Xi t = ((Xi t).re : ℂ) := Complex.ext (by simp) (by simp [Xi_real t])
    have hHt : H t = ((H t).re : ℂ) := Complex.ext (by simp) (by simp [hH.real t])
    rw [hX, hHt]
    simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_im]
  · intro z hz
    exact ((differentiable_Xi.pow 2).analyticAt z).mul (hH.analytic z hz)
  · refine ⟨CX ^ 2 * CH, fun z hz => ?_⟩
    have hz' : |z.im| ≤ 1 / 2 + δ := hz
    set x := z.re with hx
    set E := Real.exp (-(Real.pi / 4) * |x|) with hEdef
    set E' := Real.exp (Real.pi / 2 * |x|) with hE'def
    have hXz : 1 + |x| ≤ 1 + ‖z‖ := by
      have := Complex.abs_re_le_norm z
      linarith
    have hX0 : 0 ≤ 1 + |x| := by positivity
    have hXi : ‖Xi z‖ ≤ CX * (1 + |x|) ^ 3 * E := hCX z hz'
    have hHz : (1 + ‖z‖) ^ 8 * ‖H z‖ ≤ CH * E' := hCH z hz
    have hEE : E ^ 2 * E' = 1 := by
      rw [hEdef, hE'def, sq, ← Real.exp_add, ← Real.exp_add]
      have : -(Real.pi / 4) * |x| + -(Real.pi / 4) * |x| + Real.pi / 2 * |x| = 0 := by ring
      rw [this, Real.exp_zero]
    have hpoly : (1 + |x|) ^ 6 * (1 + ‖z‖) ^ 2 ≤ (1 + ‖z‖) ^ 8 := by
      calc (1 + |x|) ^ 6 * (1 + ‖z‖) ^ 2 ≤ (1 + ‖z‖) ^ 6 * (1 + ‖z‖) ^ 2 := by gcongr
        _ = (1 + ‖z‖) ^ 8 := by ring
    rw [norm_mul, norm_pow]
    calc (1 + ‖z‖) ^ 2 * (‖Xi z‖ ^ 2 * ‖H z‖)
        ≤ (1 + ‖z‖) ^ 2 * ((CX * (1 + |x|) ^ 3 * E) ^ 2 * ‖H z‖) := by gcongr
      _ = (CX ^ 2 * E ^ 2) * (((1 + |x|) ^ 6 * (1 + ‖z‖) ^ 2) * ‖H z‖) := by ring
      _ ≤ (CX ^ 2 * E ^ 2) * ((1 + ‖z‖) ^ 8 * ‖H z‖) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right hpoly (norm_nonneg _)
      _ ≤ (CX ^ 2 * E ^ 2) * (CH * E') := by
          apply mul_le_mul_of_nonneg_left hHz (by positivity)
      _ = CX ^ 2 * CH * (E ^ 2 * E') := by ring
      _ = CX ^ 2 * CH := by rw [hEE, mul_one]

/-- `H ∈ 𝒲_δ`, `δ < 1/2` ⇒ `Ξ² H ∈ 𝒯`. -/
theorem classW_mem_TestClass {δ : ℝ} {H : ℂ → ℂ} (hH : ClassW δ H) (hδ : δ < 1 / 2) :
    (fun z => Xi z ^ 2 * H z) ∈ TestClass :=
  ⟨δ, classW_inTδ hH hδ⟩

/-! ## The transfer through the Voronoi series (no axiom beyond Mathlib's, given the identity) -/

/-- **Positivity transfer.**  Given the Voronoi identity, `Ĝ_H ≥ 0` on `[a, ∞)` implies `F̂ ≥ 0` on `[a, ∞)`:
`F̂(ξ) = Σ_{m ≥ 1} d(m) m^{−1/2} Ĝ_H(ξ + ξ_m)` with positive weights and every `ξ + ξ_m ≥ ξ ≥ a`. -/
theorem FT_nonneg_of_voronoi {H : ℂ → ℂ} (hV : VoronoiIdentity H) {a : ℝ}
    (hG : ∀ ξ : ℝ, a ≤ ξ → 0 ≤ GammaFT H ξ) {ξ : ℝ} (hξ : a ≤ ξ) :
    0 ≤ FT (fun z => Xi z ^ 2 * H z) ξ := by
  rw [(hV.2 ξ).2]
  refine tsum_nonneg fun m => ?_
  unfold voronoiTerm
  refine mul_nonneg (Complex.zero_le_real.mpr (voronoiCoeff_nonneg m)) (hG _ ?_)
  have := xiOf_natCast_nonneg m
  linarith

/-- **Vanishing transfer.**  Given the Voronoi identity, (C3) implies `F̂(ξ_n) = 0` for every integer `n ≥ 2`:
`F̂(ξ_n) = Σ_{m ≥ 1} d(m) m^{−1/2} Ĝ_H(ξ_{nm})` and `nm ≥ 2`. -/
theorem FT_xiOf_eq_zero_of_voronoi {H : ℂ → ℂ} (hV : VoronoiIdentity H) (h3 : CondC3 H) {n : ℕ}
    (hn : 2 ≤ n) : FT (fun z => Xi z ^ 2 * H z) (xiOf n) = 0 := by
  rw [(hV.2 (xiOf n)).2]
  have hterm : ∀ m : ℕ, voronoiTerm H (xiOf n) m = 0 := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact voronoiTerm_zero H _
    · unfold voronoiTerm
      have hnm : 2 ≤ n * m := le_trans hn (Nat.le_mul_of_pos_right n hm)
      rw [xiOf_add_natCast (by omega) hm.ne', h3 (n * m) hnm, mul_zero]
  simp [hterm]

/-- **`F̂(0) = Ĝ_H(0)`**, given the Voronoi identity and (C3): only the term `m = 1` survives. -/
theorem FT_zero_of_voronoi {H : ℂ → ℂ} (hV : VoronoiIdentity H) (h3 : CondC3 H) :
    FT (fun z => Xi z ^ 2 * H z) 0 = GammaFT H 0 := by
  rw [(hV.2 0).2, tsum_eq_single 1]
  · exact voronoiTerm_one H 0
  · intro m hm
    rcases Nat.lt_or_ge m 2 with h | h
    · interval_cases m
      · exact voronoiTerm_zero H 0
      · exact absurd rfl hm
    · unfold voronoiTerm
      rw [zero_add, h3 m h, mul_zero]

/-- `F̂(0) = ∫ F` (Part I's normalisation of the Fourier transform). -/
theorem FT_zero_eq_integral (F : ℂ → ℂ) : FT F 0 = ∫ t : ℝ, F t := by
  unfold FT onR
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp

/-- For `F ∈ 𝒯`, `F̂(0) = ∫ F` (a real number). -/
theorem FT_zero_eq_intR {F : ℂ → ℂ} (hF : F ∈ TestClass) : FT F 0 = (intR F : ℂ) := by
  rw [FT_zero_eq_integral, TestClass.integral_eq hF]

/-! ## Part I's Corollary 4.4: `𝒜(F) = 0` -/

/-- **`𝒜(Ξ² H) = 0`** if `Ξ² H ∈ 𝒯` and `F̂(ξ_n) = 0` for every integer `n ≥ 2`: Part I's Corollary 4.4
(`zero_killing_EF`) gives `𝒜(F) = (1/π) Σ_n Λ(n) n^{−1/2} F̂(ξ_n)`, and every term vanishes (`Λ(0) = Λ(1) = 0`). -/
theorem Arch_eq_zero_of_FT_vanish {H : ℂ → ℂ} (hF : (fun z => Xi z ^ 2 * H z) ∈ TestClass)
    (hz : ∀ n : ℕ, 2 ≤ n → FT (fun z => Xi z ^ 2 * H z) (xiOf n) = 0) :
    Arch (fun z => Xi z ^ 2 * H z) = 0 := by
  obtain ⟨-, hEF⟩ := zero_killing_EF hF
  have hterms : ∀ n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      FT (fun z => Xi z ^ 2 * H z) (xiOf n) = 0 := by
    intro n
    rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · rw [hz n h, mul_zero]
  simp only [hterms, tsum_zero, mul_zero] at hEF
  exact_mod_cast hEF

/-! ## Positivity of `∫ F` -/

/-- `Ξ(t)² H(t) ≥ 0` on `ℝ` if `H ≥ 0` on `ℝ` (`Ξ` is real on `ℝ`). -/
theorem Xi_sq_mul_nonneg {H : ℂ → ℂ} (h2 : CondC2 H) (t : ℝ) : 0 ≤ Xi t ^ 2 * H t := by
  have hX : Xi t = ((Xi t).re : ℂ) := Complex.ext (by simp) (by simp [Xi_real t])
  have h0 : 0 ≤ Xi t ^ 2 := by
    rw [hX, ← Complex.ofReal_pow]
    exact Complex.zero_le_real.mpr (sq_nonneg _)
  exact mul_nonneg h0 (h2 t)

/-- **`∫ Ξ² H > 0`** if `H ∈ 𝒲_δ` (`δ < 1/2`) is `≥ 0` on `ℝ` and `H(t₁) ≠ 0` for some real `t₁`: `H ≠ 0` on an
interval around `t₁`, which is not contained in the countable set `Z_ζ`, so `F = Ξ² H` is positive somewhere; and
`F` is continuous, integrable and `≥ 0`. -/
theorem intR_pos_of_C2 {δ : ℝ} {H : ℂ → ℂ} (hH : ClassW δ H) (hδ : δ < 1 / 2) (h2 : CondC2 H)
    (hne : ∃ t : ℝ, H t ≠ 0) : 0 < intR (fun z => Xi z ^ 2 * H z) := by
  have hT := classW_mem_TestClass hH hδ
  obtain ⟨t₁, ht₁⟩ := hne
  have hcontH : ContinuousAt (fun t : ℝ => H t) t₁ :=
    (hH.analytic (t₁ : ℂ) (ofReal_mem_closedStrip hH.pos t₁)).continuousAt.comp
      Complex.continuous_ofReal.continuousAt
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hcontH.eventually_ne ht₁)
  obtain ⟨t₀, ht₀I, ht₀Z⟩ : ∃ t ∈ Set.Ioo (t₁ - ε) (t₁ + ε), t ∉ Zzeta := by
    by_contra h
    push Not at h
    have hmeas := measure_mono (μ := (volume : Measure ℝ)) (show Set.Ioo (t₁ - ε) (t₁ + ε) ⊆ Zzeta from h)
    rw [Zzeta_countable.measure_zero volume, Real.volume_Ioo] at hmeas
    have hlen : (0 : ℝ) < t₁ + ε - (t₁ - ε) := by linarith
    exact absurd hmeas (not_le.mpr (ENNReal.ofReal_pos.mpr hlen))
  have hHt₀ : H t₀ ≠ 0 := by
    apply hball
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [ht₀I.1, ht₀I.2]
  have hcont : Continuous (fun t : ℝ => ((fun z => Xi z ^ 2 * H z) (t : ℂ)).re) :=
    Complex.continuous_re.comp (TestClass.continuous hT)
  have hnn : 0 ≤ (fun t : ℝ => ((fun z => Xi z ^ 2 * H z) (t : ℂ)).re) := fun t =>
    (Complex.nonneg_iff.mp (Xi_sq_mul_nonneg h2 t)).1
  have hpos : 0 < ((fun z => Xi z ^ 2 * H z) (t₀ : ℂ)).re := by
    have hX : Xi t₀ = ((Xi t₀).re : ℂ) := Complex.ext (by simp) (by simp [Xi_real t₀])
    have hXne : (Xi t₀).re ≠ 0 := by
      intro h0
      apply ht₀Z
      rw [← Xi_eq_zero_iff, hX, h0, Complex.ofReal_zero]
    have h0 : 0 < Xi t₀ ^ 2 := by
      rw [hX, ← Complex.ofReal_pow]
      exact Complex.zero_lt_real.mpr (by positivity)
    have hH0 : 0 < H t₀ := lt_of_le_of_ne (h2 t₀) (Ne.symm hHt₀)
    exact (Complex.pos_iff.mp (mul_pos h0 hH0)).1
  exact integral_pos_of_integrable_nonneg_nonzero hcont (TestClass.integrable_re hT) hnn hpos.ne'

/-! ## Proposition "Exact magic functions from Γ-only data" -/

/-- **Proposition "Exact magic functions from Γ-only data" (`prop:reduction`).**  Let `0 < δ < 1/2` and `H ∈ 𝒲_δ`,
`H ≢ 0` (not identically zero on `S_δ`), and assume (C2) `H ≥ 0` on `ℝ`, (C3) `Ĝ_H(ξ_k) = 0` for every integer
`k ≥ 2`, and (C4) `Ĝ_H ≥ 0` on `[ξ₂, ∞)`.  Then `F = Ξ² H` lies in `𝒞`, `F̂(ξ_n) = 0` for every integer `n ≥ 2`,
`∫ F = F̂(0) = Ĝ_H(0) > 0` and `𝒜(F) = 0`.  So `F` is an exact magic function and `κ* ≤ 0`. -/
theorem reduction {δ : ℝ} {H : ℂ → ℂ} (hH : ClassW δ H) (hδ : δ < 1 / 2)
    (hne : ∃ z ∈ closedStrip (1 / 2 + δ), H z ≠ 0) (h2 : CondC2 H) (h3 : CondC3 H) (h4 : CondC4 H) :
    (fun z => Xi z ^ 2 * H z) ∈ Cone ∧
      (∀ n : ℕ, 2 ≤ n → FT (fun z => Xi z ^ 2 * H z) (xiOf n) = 0) ∧
      (intR (fun z => Xi z ^ 2 * H z) : ℂ) = FT (fun z => Xi z ^ 2 * H z) 0 ∧
      FT (fun z => Xi z ^ 2 * H z) 0 = GammaFT H 0 ∧
      0 < intR (fun z => Xi z ^ 2 * H z) ∧
      Arch (fun z => Xi z ^ 2 * H z) = 0 ∧
      IsExactMagic (fun z => Xi z ^ 2 * H z) ∧ kappaStar ≤ 0 := by
  have hT := classW_mem_TestClass hH hδ
  have hV := voronoi_decoupling hH hδ
  have hz : ∀ n : ℕ, 2 ≤ n → FT (fun z => Xi z ^ 2 * H z) (xiOf n) = 0 :=
    fun n hn => FT_xiOf_eq_zero_of_voronoi hV h3 hn
  have hC : (fun z => Xi z ^ 2 * H z) ∈ Cone :=
    ⟨hT, fun t => Xi_sq_mul_nonneg h2 t, fun ξ hξ => FT_nonneg_of_voronoi hV h4 hξ⟩
  have hpos := intR_pos_of_C2 hH hδ h2 (hH.exists_real_ne_zero hne)
  have hA := Arch_eq_zero_of_FT_vanish hT hz
  have hk := slack_le homog_Arch (scalable_ConeG_Arch xi2) hC hpos
  rw [hA, zero_div] at hk
  exact ⟨hC, hz, (FT_zero_eq_intR hT).symm, FT_zero_of_voronoi hV h3, hpos, hA, ⟨hC, hpos, hA⟩,
    by exact_mod_cast hk⟩

/-- **Proposition `prop:reduction`, last sentence.**  If moreover `Ĝ_H ≥ 0` on `[0, ∞)`, then `F = Ξ² H ∈ 𝒞_OPS`
and `κ*_OPS ≤ 0`: `F̂ ≥ 0` on `[0, ∞)` by the Voronoi series, and `F̂` is even.  ((C4) is implied by the new
hypothesis and is not assumed separately.) -/
theorem reduction_OPS {δ : ℝ} {H : ℂ → ℂ} (hH : ClassW δ H) (hδ : δ < 1 / 2)
    (hne : ∃ z ∈ closedStrip (1 / 2 + δ), H z ≠ 0) (h2 : CondC2 H) (h3 : CondC3 H)
    (h4z : CondC4Zero H) :
    (fun z => Xi z ^ 2 * H z) ∈ ConeOPS ∧ kappaOPS ≤ 0 := by
  have hT := classW_mem_TestClass hH hδ
  have hV := voronoi_decoupling hH hδ
  have heven : ∀ t : ℝ, (fun z => Xi z ^ 2 * H z) (-(t : ℂ)) = (fun z => Xi z ^ 2 * H z) t := by
    intro t
    simp only [Xi_even, hH.even (t : ℂ) (ofReal_mem_closedStrip hH.pos t)]
  have hOPS : (fun z => Xi z ^ 2 * H z) ∈ ConeOPS := by
    refine ⟨hT, fun t => Xi_sq_mul_nonneg h2 t, fun ξ => ?_⟩
    rcases le_total 0 ξ with hξ | hξ
    · exact FT_nonneg_of_voronoi hV h4z hξ
    · have h := FT_neg_of_even (fun z => Xi z ^ 2 * H z) heven (-ξ)
      rw [neg_neg] at h
      rw [h]
      exact FT_nonneg_of_voronoi hV h4z (neg_nonneg.mpr hξ)
  have h4 : CondC4 H := fun ξ hξ =>
    h4z ξ (le_trans (div_nonneg (Real.log_nonneg (by norm_num)) (by positivity)) hξ)
  obtain ⟨-, -, -, -, hpos, hA, -, -⟩ := reduction hH hδ hne h2 h3 h4
  have hk := slack_le homog_Arch scalable_ConeOPS_Arch hOPS hpos
  rw [hA, zero_div] at hk
  exact ⟨hOPS, by exact_mod_cast hk⟩

/-- **(C5) is automatic**: under the hypotheses of Proposition `prop:reduction` without (C4),
`Ĝ_H(0) = ∫ Ξ² H > 0`. -/
theorem condC5_of {δ : ℝ} {H : ℂ → ℂ} (hH : ClassW δ H) (hδ : δ < 1 / 2)
    (hne : ∃ z ∈ closedStrip (1 / 2 + δ), H z ≠ 0) (h2 : CondC2 H) (h3 : CondC3 H) : CondC5 H := by
  have hT := classW_mem_TestClass hH hδ
  have hV := voronoi_decoupling hH hδ
  have hpos := intR_pos_of_C2 hH hδ h2 (hH.exists_real_ne_zero hne)
  have h0 : GammaFT H 0 = (intR (fun z => Xi z ^ 2 * H z) : ℂ) := by
    rw [← FT_zero_of_voronoi hV h3, FT_zero_eq_intR hT]
  unfold CondC5
  rw [h0]
  exact Complex.zero_lt_real.mpr hpos

end PosRigII
