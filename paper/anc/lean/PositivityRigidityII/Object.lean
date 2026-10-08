/-
The object `H` and the exact magic function `F = Ξ² H` (Theorem `thm:main-S`, first part).

The ledger axiom `exists_integer_critical_object` gives one function `H_raw` with `H_raw ∈ 𝒲_δ` (some `δ < 1/2`),
(C3), `Ĝ ≥ 0` on `[0, ∞)` and `H_raw > 0` on `ℝ`.  Everything else is proved here, as in the proof of
Theorem `thm:main-S` (`sec:assembly`): `H := H_raw/H_raw(0)` is a Γ-only integer-critical function with `H(0) = 1`
and `H > 0` on `ℝ`, and `F = Ξ² H` satisfies (a) `F ∈ 𝒞_OPS`, (b) `F̂(ξ_n) = 0` and `F̂'(ξ_n) = 0` (whenever the
derivative exists) for every integer `n ≥ 2`, (c) `∫ F = F̂(0) > 0` and `𝒜(F) = 0`; its real zeros are exactly `Z_ζ`.
-/
import PositivityRigidityII.Reduction

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder

namespace PosRigII

open PosRig

/-- `ξ₂ = log 2/2π ≥ 0`. -/
theorem xi2_nonneg : 0 ≤ xi2 :=
  div_nonneg (Real.log_nonneg (by norm_num)) (by positivity)

/-- The real zeros of `Ξ² H` are those of `Ξ`, i.e. `Z_ζ`, if `H` has no real zero. -/
theorem ZF_Xi_sq_mul {H : ℂ → ℂ} (h2 : CondC2Strict H) :
    ZF (fun z => Xi z ^ 2 * H z) = Zzeta := by
  ext t
  have hH : H t ≠ 0 := (h2 t).ne'
  show Xi t ^ 2 * H t = 0 ↔ t ∈ Zzeta
  rw [mul_eq_zero, pow_eq_zero_iff two_ne_zero, or_iff_left hH]
  exact Xi_eq_zero_iff t

/-- **The object, normalised** (`sec:assembly`: `H := C H_raw`, `C = 1/H_raw(0) > 0`).  There is a Γ-only
integer-critical function `H` (`H ∈ 𝒲_δ` for some `δ < 1/2`, `H(0) = 1`, (C2)–(C4)) that is positive on `ℝ`, with
`Ĝ_H ≥ 0` on `[0, ∞)`, (C5), and `Ĝ_H > 0` on the window `[0, ξ₂)`. -/
theorem exists_object :
    ∃ H : ℂ → ℂ, ∃ δ : ℝ, δ < 1 / 2 ∧ IntegerCritical δ H ∧ CondC2Strict H ∧ CondC4Zero H ∧
      CondC5 H ∧ CondWindow H := by
  obtain ⟨H₀, ⟨δ, hδ, hW⟩, h3, h4z, hwin, h2s⟩ := exists_integer_critical_object
  have h00 : 0 < H₀ 0 := by simpa using h2s 0
  obtain ⟨hre, him⟩ := Complex.pos_iff.mp h00
  set r : ℝ := (H₀ 0).re with hr
  set c : ℝ := 1 / r with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  set H : ℂ → ℂ := fun z => (c : ℂ) * H₀ z with hHdef
  have hWH : ClassW δ H := hW.smul c
  have hH0 : H 0 = 1 := by
    have hH₀0 : H₀ 0 = (r : ℂ) := Complex.ext (by simp [hr]) (by simp [← him])
    simp only [hHdef, hH₀0, hc, ← Complex.ofReal_mul]
    rw [one_div_mul_cancel hre.ne', Complex.ofReal_one]
  have h2sH : CondC2Strict H := fun t => mul_pos (Complex.zero_lt_real.mpr hcpos) (h2s t)
  have h2H : CondC2 H := fun t => (h2sH t).le
  have h3H : CondC3 H := fun k hk => by rw [hHdef, GammaFT_smul, h3 k hk, mul_zero]
  have h4zH : CondC4Zero H := fun ξ hξ => by
    rw [hHdef, GammaFT_smul]
    exact mul_nonneg (Complex.zero_le_real.mpr hcpos.le) (h4z ξ hξ)
  have h4H : CondC4 H := fun ξ hξ => h4zH ξ (le_trans xi2_nonneg hξ)
  have hne : ∃ z ∈ closedStrip (1 / 2 + δ), H z ≠ 0 :=
    ⟨0, by show |(0 : ℂ).im| ≤ 1 / 2 + δ; rw [Complex.zero_im, abs_zero]; linarith [hW.pos],
      by rw [hH0]; exact one_ne_zero⟩
  have hwinH : CondWindow H := fun ξ h0 h1 => by
    rw [hHdef, GammaFT_smul]
    exact mul_pos (Complex.zero_lt_real.mpr hcpos) (hwin ξ h0 h1)
  exact ⟨H, δ, hδ, ⟨hWH, hH0, h2H, h3H, h4H⟩, h2sH, h4zH, condC5_of hWH hδ hne h2H h3H, hwinH⟩

/-- **Theorem `thm:main-S`, first part: the function `H` and the exact magic function `F = Ξ² H`.**  There is a
function `H` with `H ∈ 𝒲_δ` for some `δ ∈ (0, 1/2)` (even, real on `ℝ`, analytic near `S_δ`, with (C1)), `H(0) = 1`
and `H(t) > 0` for every real `t` (and Γ-only integer-critical), such that `F = Ξ² H` satisfies
* (a) `F ∈ 𝒞_OPS`: `F ≥ 0` and `F̂ ≥ 0` on `ℝ`;
* (b) `F̂(ξ_n) = 0` for every integer `n ≥ 2`, and every derivative of `F̂` at `ξ_n` is `0`;
* (c) `∫ F = F̂(0) > 0` and `𝒜(F) = 0`;
and consequently `F ∈ 𝒞`, `F` is an exact magic function (Part I, Definition 2.11), and the real zeros of `F` are
exactly `Z_ζ`. -/
theorem theorem1_object :
    ∃ H : ℂ → ℂ, (∃ δ : ℝ, δ < 1 / 2 ∧ IntegerCritical δ H) ∧ H 0 = 1 ∧ CondC2Strict H ∧
      (fun z => Xi z ^ 2 * H z) ∈ ConeOPS ∧
      (∀ n : ℕ, 2 ≤ n → FT (fun z => Xi z ^ 2 * H z) (xiOf n) = 0 ∧
        ∀ D : ℂ, HasDerivAt (FT (fun z => Xi z ^ 2 * H z)) D (xiOf n) → D = 0) ∧
      (intR (fun z => Xi z ^ 2 * H z) : ℂ) = FT (fun z => Xi z ^ 2 * H z) 0 ∧
      0 < intR (fun z => Xi z ^ 2 * H z) ∧ Arch (fun z => Xi z ^ 2 * H z) = 0 ∧
      (fun z => Xi z ^ 2 * H z) ∈ Cone ∧ IsExactMagic (fun z => Xi z ^ 2 * H z) ∧
      ZF (fun z => Xi z ^ 2 * H z) = Zzeta := by
  obtain ⟨H, δ, hδ, hIC, h2s, h4z, -, -⟩ := exists_object
  obtain ⟨hW, hH0, h2, h3, h4⟩ := hIC
  have hne : ∃ z ∈ closedStrip (1 / 2 + δ), H z ≠ 0 :=
    ⟨0, by show |(0 : ℂ).im| ≤ 1 / 2 + δ; rw [Complex.zero_im, abs_zero]; linarith [hW.pos],
      by rw [hH0]; exact one_ne_zero⟩
  obtain ⟨hC, hz, hint, -, hpos, hA, hM, -⟩ := reduction hW hδ hne h2 h3 h4
  obtain ⟨hOPS, -⟩ := reduction_OPS hW hδ hne h2 h3 h4z
  refine ⟨H, ⟨δ, hδ, hW, hH0, h2, h3, h4⟩, hH0, h2s, hOPS, fun n hn => ⟨hz n hn, fun D hD => ?_⟩,
    hint, hpos, hA, hC, hM, ZF_Xi_sq_mul h2s⟩
  exact hasDerivAt_eq_zero_of_nonneg (fun ξ => hOPS.2.2 ξ) (hz n hn) hD

end PosRigII
