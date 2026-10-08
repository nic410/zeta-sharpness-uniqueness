/-
Corollary 8.2 (`cor:nogap`; Section 8, subsection "The classical cone") at the gap `ℓ = 0`, and Lemma C.1, "Transfer
across the gap", of Appendix C (`lem:transfer`, `app:gap`):

  **RH ⟺ `𝒜(F) ≥ 0` for every `F ∈ 𝒯` with `F ≥ 0` and `F̂ ≥ 0` on `ℝ` ⟺ `κ*_OPS ≥ 0` ⟺ `κ*_OPS = 0`;**
  if RH fails, `κ* ≤ κ*_OPS < 0`.

* `Arch_add`: `𝒜` is additive on `𝒯`.  The archimedean integral converges absolutely for `F ∈ 𝒯`, since
  `|F(t)| ≤ C(1+|t|)^{−2}` and `|Ω_∞(t)| ≤ K(1+|t|)^{1/2}` (Stirling for `Re ψ`: Zeta23's `gammaFacts` and
  `abs_mu_le_of_gammaFacts`, proved there without hypotheses).  `TestClass.add`: `𝒯` is closed under addition.
* `transfer` (Lemma C.1 "Transfer across the gap", `lem:transfer`, for any `L` additive on `𝒯` and homogeneous): if `Θ ∈ 𝒞_OPS` has `Θ̂ > 0` on
  `[0, ℓ₁)`, `ℓ₁ > 0`, and `L(Θ) ≤ 0`, then `L ≥ 0` on `𝒞_OPS` implies `L ≥ 0` on `𝒞_{ℓ₁}`.  The proof is the paper's:
  `F₁ = F + ε e^{−πt²}`, then `F₂ = F₁ + (M/m) Θ ∈ 𝒞_OPS`; the margin near `ℓ₁` comes from the compactness of
  `{ξ ∈ [0, ℓ₁] : Re F̂₁(ξ) ≤ 0}`, which lies in `[0, ℓ₁)`.  No ledger axiom is used.
* `FT_window` (Corollary 8.2(a)): for the object, `F̂₀ ≥ Ĝ_H > 0` on `[0, ξ₂)`, from the Voronoi identity and
  the window clause of the ledger axiom `exists_integer_critical_object`; so `F̂₀ > 0` on `(−ξ₂, ξ₂)`.
* `arch_nonneg_Cone_iff_ConeOPS`, `kappaStar_nonneg_iff_kappaOPS_nonneg`: unconditionally (no Theorem U, no duality),
  `𝒜 ≥ 0` on `𝒞` ⟺ `𝒜 ≥ 0` on `𝒞_OPS`, and `κ* ≥ 0` ⟺ `κ*_OPS ≥ 0`.
* `rh_iff_kappaOPS_zero`: the corollary at the gap `0`.
-/
import PositivityRigidityII.Main
import Zeta23.GammaFacts.Complete
import Zeta23.ExplicitFormula.Bridge

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder

namespace PosRigII

open PosRig

/-! ## `Ω_∞`, and the additivity of `𝒜` on `𝒯` -/

/-- Part I's `Ω_∞` is Zeta23's `μ`. -/
theorem Ωinf_eq_mu (t : ℝ) : Ωinf t = Zeta23.mu t := by
  unfold Ωinf Zeta23.mu
  ring

/-- `Ω_∞` is continuous (Zeta23: `μ` is smooth). -/
theorem continuous_Ωinf : Continuous Ωinf := by
  have h : Ωinf = Zeta23.mu := funext Ωinf_eq_mu
  rw [h]
  exact Zeta23.gammaFacts.smooth.continuous

/-- `|Ω_∞(t)| ≤ K (1 + |t|)^{1/2}` (Zeta23, from Stirling for `Re ψ`). -/
theorem abs_Ωinf_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, |Ωinf t| ≤ K * (1 + |t|) ^ (1 / 2 : ℝ) := by
  obtain ⟨K, hK, h⟩ := Zeta23.EF.abs_mu_le_of_gammaFacts Zeta23.gammaFacts
  exact ⟨K, hK, fun t => by rw [Ωinf_eq_mu]; exact h t⟩

/-- For `F ∈ 𝒯`, the archimedean integrand `Re F(t) Ω_∞(t)` is integrable. -/
theorem TestClass.integrable_re_mul_Ωinf {F : ℂ → ℂ} (hF : F ∈ TestClass) :
    Integrable (fun t : ℝ => (F t).re * Ωinf t) := by
  obtain ⟨δ, h⟩ := hF
  obtain ⟨C, hC⟩ := h.bound
  obtain ⟨K, hK0, hK⟩ := abs_Ωinf_le
  have hcont : Continuous (fun t : ℝ => (F t).re * Ωinf t) :=
    (Complex.continuous_re.comp (TestClass.continuous ⟨δ, h⟩)).mul continuous_Ωinf
  have hint : Integrable (fun t : ℝ => (C * K) * (1 + ‖t‖) ^ (-(3 / 2 : ℝ))) :=
    (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3 / 2) (by norm_num)).const_mul (C * K)
  refine hint.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  have h1 := hC (t : ℂ) (ofReal_mem_closedStrip h.pos t)
  rw [Complex.norm_real] at h1
  set X : ℝ := 1 + ‖t‖ with hX
  have hX0 : 0 < X := by rw [hX]; positivity
  have hC0 : 0 ≤ C := le_trans (by positivity) h1
  have hF1 : ‖F t‖ ≤ C / X ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    linarith [h1]
  have hΩ : |Ωinf t| ≤ K * X ^ (1 / 2 : ℝ) := by
    have := hK t
    rwa [← Real.norm_eq_abs t] at this
  have hre : |(F t).re| ≤ C / X ^ 2 := le_trans (Complex.abs_re_le_norm _) hF1
  have hpow : X ^ (1 / 2 : ℝ) / X ^ 2 = X ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_two, ← Real.rpow_sub hX0]
    norm_num
  rw [Real.norm_eq_abs, abs_mul]
  calc |(F t).re| * |Ωinf t| ≤ (C / X ^ 2) * (K * X ^ (1 / 2 : ℝ)) :=
        mul_le_mul hre hΩ (abs_nonneg _) (by positivity)
    _ = (C * K) * (X ^ (1 / 2 : ℝ) / X ^ 2) := by ring
    _ = (C * K) * X ^ (-(3 / 2 : ℝ)) := by rw [hpow]

/-- **`𝒜` is additive on `𝒯`.** -/
theorem Arch_add {F G : ℂ → ℂ} (hF : F ∈ TestClass) (hG : G ∈ TestClass) :
    Arch (fun z => F z + G z) = Arch F + Arch G := by
  have h1 := TestClass.integrable_re_mul_Ωinf hF
  have h2 := TestClass.integrable_re_mul_Ωinf hG
  have hint : (∫ t : ℝ, (F t + G t).re * Ωinf t) =
      (∫ t : ℝ, (F t).re * Ωinf t) + ∫ t : ℝ, (G t).re * Ωinf t := by
    rw [← integral_add h1 h2]
    congr 1
    funext t
    rw [Complex.add_re, add_mul]
  show (F (I / 2) + G (I / 2) + (F (-I / 2) + G (-I / 2))).re +
      (∫ t : ℝ, (F t + G t).re * Ωinf t) = Arch F + Arch G
  rw [hint]
  unfold Arch
  simp only [Complex.add_re]
  ring

/-- The closed strips increase with their width. -/
theorem closedStrip_mono {a b : ℝ} (h : a ≤ b) : closedStrip a ⊆ closedStrip b :=
  fun _ hz => le_trans hz h

/-- **`𝒯` is closed under addition** (`𝒯_δ ⊇ 𝒯_{δ'}` for `δ ≤ δ'`). -/
theorem TestClass.add {F G : ℂ → ℂ} (hF : F ∈ TestClass) (hG : G ∈ TestClass) :
    (fun z => F z + G z) ∈ TestClass := by
  obtain ⟨δ₁, h₁⟩ := hF
  obtain ⟨δ₂, h₂⟩ := hG
  obtain ⟨C₁, hC₁⟩ := h₁.bound
  obtain ⟨C₂, hC₂⟩ := h₂.bound
  have hs₁ : closedStrip (1 / 2 + min δ₁ δ₂) ⊆ closedStrip (1 / 2 + δ₁) :=
    closedStrip_mono (by have := min_le_left δ₁ δ₂; linarith)
  have hs₂ : closedStrip (1 / 2 + min δ₁ δ₂) ⊆ closedStrip (1 / 2 + δ₂) :=
    closedStrip_mono (by have := min_le_right δ₁ δ₂; linarith)
  refine ⟨min δ₁ δ₂, lt_min h₁.pos h₂.pos, lt_of_le_of_lt (min_le_left _ _) h₁.lt_half,
    fun z hz => ?_, fun t => ?_, (h₁.analytic.mono hs₁).add (h₂.analytic.mono hs₂), ⟨C₁ + C₂, fun z hz => ?_⟩⟩
  · show F (-z) + G (-z) = F z + G z
    rw [h₁.even z (hs₁ hz), h₂.even z (hs₂ hz)]
  · show (F t + G t).im = 0
    rw [Complex.add_im, h₁.real t, h₂.real t, add_zero]
  · calc (1 + ‖z‖) ^ 2 * ‖F z + G z‖ ≤ (1 + ‖z‖) ^ 2 * (‖F z‖ + ‖G z‖) := by
          gcongr
          exact norm_add_le _ _
      _ = (1 + ‖z‖) ^ 2 * ‖F z‖ + (1 + ‖z‖) ^ 2 * ‖G z‖ := by ring
      _ ≤ C₁ + C₂ := add_le_add (hC₁ z (hs₁ hz)) (hC₂ z (hs₂ hz))

/-! ## The transfer lemma (Lemma C.1 "Transfer across the gap", `lem:transfer`) -/

/-- The Gaussian is `≥ 0` on `ℝ`. -/
theorem gauss_nonneg (t : ℝ) : 0 ≤ gauss t := by
  rw [gauss_ofReal]
  exact Complex.zero_le_real.mpr (Real.exp_pos _).le

/-- **Lemma C.1 "Transfer across the gap" (`lem:transfer`).**  Let `ℓ₁ > 0`, let `Θ ∈ 𝒞_OPS` with `Re Θ̂ > 0` on
`[0, ℓ₁)`, and let `L` be additive on `𝒯` and homogeneous, with `L(Θ) ≤ 0`.  If `L ≥ 0` on `𝒞_OPS`, then `L ≥ 0` on
`𝒞_{ℓ₁}`. -/
theorem transfer {L : (ℂ → ℂ) → ℝ}
    (hadd : ∀ F G : ℂ → ℂ, F ∈ TestClass → G ∈ TestClass → L (fun z => F z + G z) = L F + L G)
    (hsmul : ∀ (F : ℂ → ℂ) (c : ℝ), L (fun z => (c : ℂ) * F z) = c * L F)
    {ℓ₁ : ℝ} {Θ : ℂ → ℂ} (hΘ : Θ ∈ ConeOPS) (hΘpos : ∀ ξ : ℝ, 0 ≤ ξ → ξ < ℓ₁ → 0 < (FT Θ ξ).re)
    (hLΘ : L Θ ≤ 0) (hL : ∀ F ∈ ConeOPS, 0 ≤ L F) : ∀ F ∈ ConeG ℓ₁, 0 ≤ L F := by
  intro F hF
  by_contra hneg
  push Not at hneg
  -- Step 1: the Gaussian margin `F₁ = F + ε e^{−πt²}` with `L(F₁) < 0`.
  have hgT : ∀ c : ℝ, (fun z => (c : ℂ) * gauss z) ∈ TestClass := fun c => TestClass.smul gauss_mem_TestClass c
  set A : ℝ := L gauss with hA
  set ε : ℝ := -L F / (2 * (|A| + 1)) with hε
  have hεpos : 0 < ε := div_pos (by linarith) (by positivity)
  have hεA : ε * A < -L F / 2 := by
    have h1 : ε * A ≤ ε * |A| := mul_le_mul_of_nonneg_left (le_abs_self A) hεpos.le
    have h2 : ε * |A| < -L F / 2 := by
      rw [hε, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [abs_nonneg A]
    linarith
  have hF₁T : (fun z => F z + (ε : ℂ) * gauss z) ∈ TestClass := TestClass.add hF.1 (hgT ε)
  have hLF₁ : L (fun z => F z + (ε : ℂ) * gauss z) < 0 := by
    have h := hadd F (fun z => (ε : ℂ) * gauss z) hF.1 (hgT ε)
    rw [hsmul] at h
    rw [h]
    linarith
  -- Step 2: `φ = Re F̂₁` is positive on `[ℓ₁, ∞)`; `ψ = Re Θ̂`.
  set φ : ℝ → ℝ := fun ξ => (FT (fun z => F z + (ε : ℂ) * gauss z) ξ).re with hφdef
  set ψ : ℝ → ℝ := fun ξ => (FT Θ ξ).re with hψdef
  have hφc : Continuous φ := Complex.continuous_re.comp (TestClass.continuous_FT hF₁T)
  have hψc : Continuous ψ := Complex.continuous_re.comp (TestClass.continuous_FT hΘ.1)
  have hφval : ∀ ξ, φ ξ = (FT F ξ).re + ε * Real.exp (-Real.pi * ξ ^ 2) := by
    intro ξ
    simp only [hφdef]
    rw [FT_add_of_integrable (TestClass.integrable hF.1) (TestClass.integrable (hgT ε)), FT_smul, FT_gauss,
      Complex.add_re, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hφpos : ∀ ξ, ℓ₁ ≤ ξ → 0 < φ ξ := by
    intro ξ hξ
    rw [hφval]
    have h1 : 0 ≤ (FT F ξ).re := (Complex.nonneg_iff.mp (hF.2.2 ξ hξ)).1
    have h2 : 0 < ε * Real.exp (-Real.pi * ξ ^ 2) := mul_pos hεpos (Real.exp_pos _)
    linarith
  have hψnn : ∀ ξ, 0 ≤ ψ ξ := fun ξ => (Complex.nonneg_iff.mp (hΘ.2.2 ξ)).1
  -- Step 3: the compact set where `φ ≤ 0` lies in `[0, ℓ₁)`, where `ψ > 0`.
  set K : Set ℝ := Set.Icc 0 ℓ₁ ∩ {ξ | φ ξ ≤ 0} with hKdef
  have hKc : IsCompact K := isCompact_Icc.inter_right (isClosed_le hφc continuous_const)
  have hKlt : ∀ ξ ∈ K, ξ < ℓ₁ := by
    intro ξ hξ
    rcases lt_or_eq_of_le hξ.1.2 with h | h
    · exact h
    · exfalso
      have h1 := hφpos ξ (le_of_eq h.symm)
      have h2 : φ ξ ≤ 0 := hξ.2
      linarith
  have hKψ : ∀ ξ ∈ K, 0 < ψ ξ := fun ξ hξ => hΘpos ξ hξ.1.1 (hKlt ξ hξ)
  obtain ⟨M, m, hm, hM, hMm⟩ : ∃ M m : ℝ, 0 < m ∧ 0 ≤ M ∧ ∀ ξ ∈ K, -M ≤ φ ξ ∧ m ≤ ψ ξ := by
    by_cases hKne : K.Nonempty
    · obtain ⟨a, haK, ha⟩ := hKc.exists_isMinOn hKne hψc.continuousOn
      obtain ⟨b, hbK, hb⟩ := hKc.exists_isMinOn hKne hφc.continuousOn
      have hb0 : φ b ≤ 0 := hbK.2
      refine ⟨-φ b, ψ a, hKψ a haK, by linarith, fun ξ hξ => ⟨?_, ?_⟩⟩
      · have h1 : φ b ≤ φ ξ := hb hξ
        linarith
      · exact ha hξ
    · refine ⟨0, 1, one_pos, le_rfl, fun ξ hξ => absurd ⟨ξ, hξ⟩ hKne⟩
  -- Step 4: the correction `F₂ = F₁ + (M/m) Θ ∈ 𝒞_OPS`, with `L(F₂) < 0`.
  have hlam : 0 ≤ M / m := div_nonneg hM hm.le
  have hΘsT : (fun z => ((M / m : ℝ) : ℂ) * Θ z) ∈ TestClass := TestClass.smul hΘ.1 (M / m)
  have hF₂T : (fun z => (F z + (ε : ℂ) * gauss z) + ((M / m : ℝ) : ℂ) * Θ z) ∈ TestClass :=
    TestClass.add hF₁T hΘsT
  have hFT₂ : ∀ ξ, FT (fun z => (F z + (ε : ℂ) * gauss z) + ((M / m : ℝ) : ℂ) * Θ z) ξ =
      FT (fun z => F z + (ε : ℂ) * gauss z) ξ + ((M / m : ℝ) : ℂ) * FT Θ ξ := by
    intro ξ
    rw [FT_add_of_integrable (TestClass.integrable hF₁T) (TestClass.integrable hΘsT), FT_smul]
  have hre₂ : ∀ ξ, 0 ≤ ξ →
      0 ≤ (FT (fun z => (F z + (ε : ℂ) * gauss z) + ((M / m : ℝ) : ℂ) * Θ z) ξ).re := by
    intro ξ hξ
    rw [hFT₂, Complex.add_re, Complex.re_ofReal_mul]
    change 0 ≤ φ ξ + M / m * ψ ξ
    have hψξ := hψnn ξ
    by_cases hφξ : 0 < φ ξ
    · have : 0 ≤ M / m * ψ ξ := mul_nonneg hlam hψξ
      linarith
    · push Not at hφξ
      have hξg : ξ ≤ ℓ₁ := by
        by_contra h
        push Not at h
        have := hφpos ξ h.le
        linarith
      have hξK : ξ ∈ K := ⟨⟨hξ, hξg⟩, hφξ⟩
      obtain ⟨h1, h2⟩ := hMm ξ hξK
      have h3 : M ≤ M / m * ψ ξ := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hm]
        exact mul_le_mul_of_nonneg_left h2 hM
      linarith
  have hOPS₂ : (fun z => (F z + (ε : ℂ) * gauss z) + ((M / m : ℝ) : ℂ) * Θ z) ∈ ConeOPS := by
    refine ⟨hF₂T, fun t => ?_, fun ξ => ?_⟩
    · exact add_nonneg (add_nonneg (hF.2.1 t)
        (mul_nonneg (Complex.zero_le_real.mpr hεpos.le) (gauss_nonneg t)))
        (mul_nonneg (Complex.zero_le_real.mpr hlam) (hΘ.2.1 t))
    · have him := TestClass.FT_real hF₂T
      obtain ⟨δ, hδ⟩ := hF₂T
      have heven : ∀ t : ℝ, (fun z => (F z + (ε : ℂ) * gauss z) + ((M / m : ℝ) : ℂ) * Θ z) (-(t : ℂ)) =
          (fun z => (F z + (ε : ℂ) * gauss z) + ((M / m : ℝ) : ℂ) * Θ z) t :=
        fun t => hδ.even (t : ℂ) (ofReal_mem_closedStrip hδ.pos t)
      rcases le_total 0 ξ with hξ | hξ
      · exact Complex.nonneg_iff.mpr ⟨hre₂ ξ hξ, (him ξ).symm⟩
      · have h := FT_neg_of_even (fun z => (F z + (ε : ℂ) * gauss z) + ((M / m : ℝ) : ℂ) * Θ z) heven (-ξ)
        rw [neg_neg] at h
        rw [h]
        exact Complex.nonneg_iff.mpr ⟨hre₂ (-ξ) (neg_nonneg.mpr hξ), (him (-ξ)).symm⟩
  have hL₂ : L (fun z => (F z + (ε : ℂ) * gauss z) + ((M / m : ℝ) : ℂ) * Θ z) < 0 := by
    have h := hadd (fun z => F z + (ε : ℂ) * gauss z) (fun z => ((M / m : ℝ) : ℂ) * Θ z) hF₁T hΘsT
    rw [hsmul] at h
    rw [h]
    have : M / m * L Θ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam hLΘ
    linarith
  exact absurd (hL _ hOPS₂) (not_le.mpr hL₂)

/-- **The transfer lemma for `𝒜`.** -/
theorem transfer_Arch {ℓ₁ : ℝ} {Θ : ℂ → ℂ} (hΘ : Θ ∈ ConeOPS)
    (hΘpos : ∀ ξ : ℝ, 0 ≤ ξ → ξ < ℓ₁ → 0 < (FT Θ ξ).re) (hAΘ : Arch Θ ≤ 0)
    (hA : ∀ F ∈ ConeOPS, 0 ≤ Arch F) : ∀ F ∈ ConeG ℓ₁, 0 ≤ Arch F :=
  transfer (fun _ _ hF hG => Arch_add hF hG) Arch_smul hΘ hΘpos hAΘ hA

/-! ## Part (a): the window -/

/-- Each term of the Voronoi series at `ξ ≥ 0` is `≥ 0` if `Ĝ_H ≥ 0` on `[0, ∞)`. -/
theorem voronoiTerm_nonneg {H : ℂ → ℂ} (h4z : CondC4Zero H) {ξ : ℝ} (hξ : 0 ≤ ξ) (m : ℕ) :
    0 ≤ voronoiTerm H ξ m :=
  mul_nonneg (Complex.zero_le_real.mpr (voronoiCoeff_nonneg m))
    (h4z _ (add_nonneg hξ (xiOf_natCast_nonneg m)))

/-- Given the Voronoi identity, `Ĝ_H ≥ 0` on `[0, ∞)` gives `Re F̂(ξ) ≥ Re Ĝ_H(ξ)` for `ξ ≥ 0` (the term `m = 1`). -/
theorem FT_re_ge_GammaFT_re {H : ℂ → ℂ} (hV : VoronoiIdentity H) (h4z : CondC4Zero H) {ξ : ℝ}
    (hξ : 0 ≤ ξ) : (GammaFT H ξ).re ≤ (FT (fun z => Xi z ^ 2 * H z) ξ).re := by
  obtain ⟨hsum, heq⟩ := hV.2 ξ
  have hre : HasSum (fun m => (voronoiTerm H ξ m).re) (FT (fun z => Xi z ^ 2 * H z) ξ).re := by
    rw [heq]
    exact Complex.hasSum_re hsum.hasSum
  have h := le_hasSum hre 1 fun m _ => (Complex.nonneg_iff.mp (voronoiTerm_nonneg h4z hξ m)).1
  rwa [voronoiTerm_one] at h

/-- `ξ₂ = log 2/2π > 0`. -/
theorem xi2_pos : 0 < xi2 :=
  div_pos (Real.log_pos (by norm_num)) (by positivity)

/-- **Corollary 8.2 (`cor:nogap`), part (a).**  For the object `H` (`H(0) = 1`, `H > 0` on `ℝ`, Γ-only integer-critical) and
`F = Ξ² H ∈ 𝒞_OPS` with `𝒜(F) = 0`: `F̂(ξ) ≥ Ĝ_H(ξ) > 0` for `0 ≤ ξ < ξ₂`, hence `F̂ > 0` on `(−ξ₂, ξ₂)`.  (The zero set
`{±ξ_n : n ≥ 2}` of `F̂` is not formalised.) -/
theorem FT_window :
    ∃ H : ℂ → ℂ, (∃ δ : ℝ, δ < 1 / 2 ∧ IntegerCritical δ H) ∧ CondC2Strict H ∧
      (fun z => Xi z ^ 2 * H z) ∈ ConeOPS ∧ Arch (fun z => Xi z ^ 2 * H z) = 0 ∧
      (∀ ξ : ℝ, 0 ≤ ξ → ξ < xi2 → GammaFT H ξ ≤ FT (fun z => Xi z ^ 2 * H z) ξ ∧ 0 < GammaFT H ξ) ∧
      ∀ ξ : ℝ, |ξ| < xi2 → 0 < FT (fun z => Xi z ^ 2 * H z) ξ := by
  obtain ⟨H, δ, hδ, hIC, h2s, h4z, -, hwin⟩ := exists_object
  obtain ⟨hW, hH0, h2, h3, h4⟩ := hIC
  have hne : ∃ z ∈ closedStrip (1 / 2 + δ), H z ≠ 0 :=
    ⟨0, by show |(0 : ℂ).im| ≤ 1 / 2 + δ; rw [Complex.zero_im, abs_zero]; linarith [hW.pos],
      by rw [hH0]; exact one_ne_zero⟩
  obtain ⟨hOPS, -⟩ := reduction_OPS hW hδ hne h2 h3 h4z
  obtain ⟨-, -, -, -, -, hA, -, -⟩ := reduction hW hδ hne h2 h3 h4
  have hV := voronoi_decoupling hW hδ
  have hT := classW_mem_TestClass hW hδ
  have hreal : ∀ ξ, (FT (fun z => Xi z ^ 2 * H z) ξ).im = 0 := TestClass.FT_real hT
  have hpos : ∀ ξ : ℝ, 0 ≤ ξ → ξ < xi2 →
      GammaFT H ξ ≤ FT (fun z => Xi z ^ 2 * H z) ξ ∧ 0 < GammaFT H ξ := by
    intro ξ h0 h1
    have hG := hwin ξ h0 h1
    have hGim : (GammaFT H ξ).im = 0 := ((Complex.pos_iff.mp hG).2).symm
    exact ⟨Complex.le_def.mpr ⟨FT_re_ge_GammaFT_re hV h4z h0, by rw [hGim, hreal]⟩, hG⟩
  refine ⟨H, ⟨δ, hδ, hW, hH0, h2, h3, h4⟩, h2s, hOPS, hA, hpos, fun ξ hξ => ?_⟩
  have heven : ∀ t : ℝ, (fun z => Xi z ^ 2 * H z) (-(t : ℂ)) = (fun z => Xi z ^ 2 * H z) t := by
    intro t
    simp only [Xi_even, hW.even (t : ℂ) (ofReal_mem_closedStrip hW.pos t)]
  have habs : FT (fun z => Xi z ^ 2 * H z) ξ = FT (fun z => Xi z ^ 2 * H z) |ξ| := by
    rcases le_total 0 ξ with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h]
      have := FT_neg_of_even (fun z => Xi z ^ 2 * H z) heven ξ
      exact this.symm
  rw [habs]
  obtain ⟨hle, hG⟩ := hpos |ξ| (abs_nonneg ξ) hξ
  exact lt_of_lt_of_le hG hle

/-! ## The corollary -/

/-- **Unconditionally (no Theorem U, no duality): `𝒜 ≥ 0` on `𝒞` iff `𝒜 ≥ 0` on `𝒞_OPS`.**  (`𝒞_OPS ⊆ 𝒞`; and the
transfer lemma with `Θ = F₀`, `ℓ₁ = ξ₂`.) -/
theorem arch_nonneg_Cone_iff_ConeOPS : (∀ F ∈ Cone, 0 ≤ Arch F) ↔ ∀ F ∈ ConeOPS, 0 ≤ Arch F := by
  refine ⟨fun h F hF => h F (ConeOPS_subset_Cone hF), fun h => ?_⟩
  obtain ⟨H, -, -, hOPS, hA, hpos, -⟩ := FT_window
  have hΘpos : ∀ ξ : ℝ, 0 ≤ ξ → ξ < xi2 → 0 < (FT (fun z => Xi z ^ 2 * H z) ξ).re := by
    intro ξ h0 h1
    have h' := hpos ξ h0 h1
    exact lt_of_lt_of_le (Complex.pos_iff.mp h'.2).1 (Complex.le_def.mp h'.1).1
  exact transfer_Arch hOPS hΘpos (le_of_eq hA) h

/-- **Unconditionally: `κ* ≥ 0` iff `κ*_OPS ≥ 0`** (hence, with Theorem S, `κ* = 0` iff `κ*_OPS = 0`). -/
theorem kappaStar_nonneg_iff_kappaOPS_nonneg : 0 ≤ kappaStar ↔ 0 ≤ kappaOPS := by
  rw [← duality_ii_iv, arch_nonneg_Cone_iff_ConeOPS]
  exact (slack_nonneg_iff homog_Arch scalable_ConeOPS_Arch).symm

/-- **Corollary 8.2 (`cor:nogap`), at the gap `ℓ = 0` (its last sentence).**  RH holds if and
only if `𝒜(F) ≥ 0` for every `F ∈ 𝒯` with `F ≥ 0` and `F̂ ≥ 0` on `ℝ` (`F ∈ 𝒞_OPS`), if and only if `κ*_OPS ≥ 0`, if and
only if `κ*_OPS = 0`.  If RH fails, then `κ* ≤ κ*_OPS < 0`. -/
theorem rh_iff_kappaOPS_zero :
    (RiemannHypothesis ↔ ∀ F ∈ ConeOPS, 0 ≤ Arch F) ∧ (RiemannHypothesis ↔ 0 ≤ kappaOPS) ∧
      (RiemannHypothesis ↔ kappaOPS = 0) ∧
      (¬ RiemannHypothesis → kappaStar ≤ kappaOPS ∧ kappaOPS < 0) := by
  have hS := theorem1
  have hOPS0 : 0 ≤ kappaOPS ↔ ∀ F ∈ ConeOPS, 0 ≤ Arch F :=
    slack_nonneg_iff homog_Arch scalable_ConeOPS_Arch
  have hRH0 : RiemannHypothesis ↔ 0 ≤ kappaOPS := by
    rw [corollary3.1, corollary3.2.1, kappaStar_nonneg_iff_kappaOPS_nonneg]
  have h00 : 0 ≤ kappaOPS ↔ kappaOPS = 0 := ⟨fun h => le_antisymm hS.2 h, fun h => h ▸ le_rfl⟩
  refine ⟨hRH0.trans hOPS0, hRH0, hRH0.trans h00, fun hn => ⟨hS.1, ?_⟩⟩
  exact not_le.mp fun h => hn (hRH0.mpr h)


/-! ## Corollary 8.2 at every gap `ℓ ∈ [0, ξ₂]` -/

/-- `𝒞_ℓ ⊆ 𝒞_{ℓ'}` for `ℓ ≤ ℓ'`. -/
theorem ConeG_mono {ℓ ℓ' : ℝ} (h : ℓ ≤ ℓ') : ConeG ℓ ⊆ ConeG ℓ' :=
  fun _ hF => ⟨hF.1, hF.2.1, fun ξ hξ => hF.2.2 ξ (le_trans h hξ)⟩

/-- `𝒞_0 = 𝒞_OPS` (`F̂` is even). -/
theorem ConeG_zero_eq : ConeG 0 = ConeOPS := by
  ext F
  refine ⟨fun hF => ⟨hF.1, hF.2.1, fun ξ => ?_⟩, fun hF => ConeOPS_subset_ConeG 0 hF⟩
  rcases le_total 0 ξ with hξ | hξ
  · exact hF.2.2 ξ hξ
  · obtain ⟨δ, hδ⟩ := hF.1
    have heven : ∀ t : ℝ, F (-(t : ℂ)) = F t := fun t => hδ.even (t : ℂ) (ofReal_mem_closedStrip hδ.pos t)
    have h := FT_neg_of_even F heven (-ξ)
    rw [neg_neg] at h
    rw [h]
    exact hF.2.2 (-ξ) (neg_nonneg.mpr hξ)

/-- The slack decreases as the set grows. -/
theorem slack_anti {A : (ℂ → ℂ) → ℝ} {C C' : Set (ℂ → ℂ)} (h : C ⊆ C') : slack A C' ≤ slack A C := by
  unfold slack
  exact biInf_mono fun _ hF => ⟨h hF.1, hF.2⟩

/-- **Corollary 8.2 (`cor:nogap`), part (b).**  Let `0 ≤ ℓ ≤ ξ₂`.  Every pair admissible at the gap `ℓ` (`ν` on
`[ℓ, ∞)`) has `ν([ℓ, ξ₂)) = 0`; thus `𝒦_ℓ = 𝒦`.  No hypothesis on the zeros of `ζ`.  (Complementary slackness at the gap
`ℓ` with `F₀ ∈ 𝒞_OPS ⊆ 𝒞_ℓ`, `𝒜(F₀) = 0`, and `F̂₀ > 0` on `[0, ξ₂)`.) -/
theorem corollary8_2_b {ℓ : ℝ} (h0 : 0 ≤ ℓ) (h1 : ℓ ≤ xi2) : Kset Arch ℓ = K := by
  obtain ⟨H, -, -, hOPS, hA, -, hpos⟩ := FT_window
  ext p
  constructor
  · intro hp
    obtain ⟨-, hν⟩ := comp_slackness_gen hp (ConeOPS_subset_ConeG ℓ hOPS) hA
    refine ⟨hp.1, measure_mono_null (Set.compl_subset_compl.mpr fun ξ hξ => ?_) hν, hp.2.2⟩
    obtain ⟨hℓξ, hz⟩ := hξ
    show xi2 ≤ ξ
    by_contra hlt
    push Not at hlt
    have hab : |ξ| < xi2 := by rw [abs_of_nonneg (le_trans h0 hℓξ)]; exact hlt
    exact (hpos ξ hab).ne' hz
  · intro hp
    exact admissible_mono_gap h1 hp

/-- **Corollary 8.2 (`cor:nogap`), parts (c) and (d), at every gap `ℓ ∈ [0, ξ₂]`** (`κ*_ℓ` is `slack Arch (ConeG ℓ)`,
Part I §5.5).  The following are equivalent: (i) RH; (ii) `𝒦_ℓ ≠ ∅`; (iii) `𝒜(F) ≥ 0` for every `F ∈ 𝒞_ℓ`;
(v) `κ*_ℓ ≥ 0`; (vi) `κ*_ℓ = 0`.  If RH holds, `𝒦_ℓ = {p_ζ}` and `κ*_ℓ = 0`; if RH fails, `𝒦_ℓ = ∅` and
`κ* ≤ κ*_ℓ ≤ κ*_OPS < 0`.  (Clause (iv), on `𝒞_ℓ ∩ 𝒢`, uses Proposition C.2 and is not formalised.) -/
theorem corollary8_2 {ℓ : ℝ} (h0 : 0 ≤ ℓ) (h1 : ℓ ≤ xi2) :
    (RiemannHypothesis ↔ (Kset Arch ℓ).Nonempty) ∧
      (RiemannHypothesis ↔ ∀ F ∈ ConeG ℓ, 0 ≤ Arch F) ∧
      (RiemannHypothesis ↔ 0 ≤ slack Arch (ConeG ℓ)) ∧
      (RiemannHypothesis ↔ slack Arch (ConeG ℓ) = 0) ∧
      (RiemannHypothesis → Kset Arch ℓ = {pZeta}) ∧
      (¬ RiemannHypothesis → Kset Arch ℓ = ∅ ∧ kappaStar ≤ slack Arch (ConeG ℓ) ∧
        slack Arch (ConeG ℓ) ≤ kappaOPS ∧ kappaOPS < 0) := by
  have hb := corollary8_2_b h0 h1
  obtain ⟨hR1, -, -, hR4⟩ := rh_iff_kappaOPS_zero
  have hiii : RiemannHypothesis ↔ ∀ F ∈ ConeG ℓ, 0 ≤ Arch F := by
    rw [hR1]
    refine ⟨fun h F hF => arch_nonneg_Cone_iff_ConeOPS.mpr h F (ConeG_mono h1 hF),
      fun h F hF => h F (ConeOPS_subset_ConeG ℓ hF)⟩
  have hv : 0 ≤ slack Arch (ConeG ℓ) ↔ ∀ F ∈ ConeG ℓ, 0 ≤ Arch F :=
    slack_nonneg_iff homog_Arch (scalable_ConeG_Arch ℓ)
  have hle : slack Arch (ConeG ℓ) ≤ kappaOPS := slack_anti (ConeOPS_subset_ConeG ℓ)
  have hge : kappaStar ≤ slack Arch (ConeG ℓ) := slack_anti (ConeG_mono h1)
  have hS := theorem1
  refine ⟨?_, hiii, hiii.trans hv.symm, ?_, fun hRH => ?_, fun hn => ?_⟩
  · rw [hb]
    exact corollary3.1
  · rw [hiii, ← hv]
    exact ⟨fun h => le_antisymm (hle.trans hS.2) h, fun h => h ▸ le_rfl⟩
  · rw [hb]
    exact (corollary3_RH hRH).1
  · rw [hb]
    exact ⟨(corollary3_notRH hn).2, hge, hle, (hR4 hn).2⟩

end PosRigII
