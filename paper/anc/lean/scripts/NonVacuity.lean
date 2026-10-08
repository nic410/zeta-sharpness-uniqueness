/-
Non-vacuity and sanity checks (`scripts/audit.sh`, check (f)).  Run (after `lake build`):
  lake env lean scripts/NonVacuity.lean

The headline theorems of Part II and its two ledger axioms quantify over the class `𝒲_δ`, the Γ-only transform and
the Voronoi series; they would be vacuous, or say less than they seem to, if the class were empty, if `γ_∞` were not
the paper's, if the indexing of the Voronoi series were off, or if the steps that the assembly takes from the
Voronoi identity were not what they claim.  Each theorem below checks one of these points, and must depend only on
`propext`, `Classical.choice` and `Quot.sound` (no ledger axiom of Part I or Part II); the `#print axioms` lines at
the end are checked by `scripts/audit.sh`.

* `classW_nonempty`: the constant `1` lies in `𝒲_δ` for every `0 < δ < 1` and is positive on `ℝ` (so the hypothesis
  of `voronoi_decoupling` can be met, by a function positive on `ℝ`);
* `gammaInf_faithful`: `γ_∞(s) = ½ s(s−1) Γ_ℝ(s)` (`s ≠ 0`), `γ_∞(0) = −1`, and `Ξ(t) = γ_∞(½+it) ζ(½+it)` on `ℝ`;
* `voronoi_indexing`: the Voronoi series starts at `m = 1` with the term `Ĝ_H(ξ)`, and `ξ_n + ξ_m = ξ_{nm}`;
* `positivity_transfer`, `vanishing_transfer`: given the Voronoi identity (the conclusion of the ledger axiom), the
  transfer of `Ĝ_H ≥ 0` and of (C3) to `F̂` uses no axiom;
* `cones_not_junk`: the normalised cone elements that define `κ*` and `κ*_OPS` exist (the Gaussian), so
  `κ*, κ*_OPS < ∞` is not a junk value;
* `exact_magic_meaning`: an exact magic function forces `κ* ≤ 0`, and one in `𝒞_OPS` forces `κ*_OPS ≤ 0`;
* `zero_set_of_strict`: if `H > 0` on `ℝ`, the real zeros of `Ξ² H` are exactly `Z_ζ` (how Theorem U uses strict
  positivity);
* `identity_theorem`: "`H ≢ 0`" in Proposition `prop:reduction` gives a real point with `H(t) ≠ 0`;
* `deriv_at_zero_of_nonneg`: a non-negative real-valued function has derivative `0` (if any) at its zeros (how
  Theorem S(b) passes from `F̂(ξ_n) = 0` to `F̂'(ξ_n) = 0`);
* `transfer_lemma`: Lemma C.1 (the transfer lemma of Corollary 8.2) for `𝒜` needs no axiom;
* `arch_additive`: `𝒜` is additive on `𝒯`, and `𝒯` is closed under addition;
* `classical_cone_zero`: `𝒞_0 = 𝒞_OPS`, so Corollary 8.2 at the gap `0` is about the classical cone.
-/
import PositivityRigidityII

open MeasureTheory Filter Complex
open scoped ComplexOrder

namespace PosRigII.NonVacuity

open PosRig PosRigII

/-- `𝒲_δ` contains the constant `1` for every `0 < δ < 1`, and `1 > 0` on `ℝ`. -/
theorem classW_nonempty :
    (∀ δ : ℝ, 0 < δ → δ < 1 → ClassW δ (fun _ => 1)) ∧ CondC2Strict (fun _ => 1) :=
  ⟨fun _ h0 h1 => one_classW h0 h1, one_condC2Strict⟩

/-- `γ_∞` is the paper's archimedean factor, and `Ξ = γ_∞ ζ` on the real line. -/
theorem gammaInf_faithful :
    (∀ s : ℂ, s ≠ 0 → gammaInf s = s * (s - 1) / 2 * Complex.Gammaℝ s) ∧ gammaInf 0 = -1 ∧
      ∀ t : ℝ, Xi t = gammaInf (1 / 2 + I * t) * riemannZeta (1 / 2 + I * t) :=
  ⟨fun _ hs => gammaInf_eq_gammaR hs, gammaInf_zero, Xi_eq_gammaInf_mul_zeta⟩

/-- The Voronoi series runs over `m ≥ 1`, its first term is `Ĝ_H(ξ)`, and `ξ_n + ξ_m = ξ_{nm}`. -/
theorem voronoi_indexing :
    (∀ (H : ℂ → ℂ) (ξ : ℝ), voronoiTerm H ξ 0 = 0 ∧ voronoiTerm H ξ 1 = GammaFT H ξ) ∧
      (∀ n m : ℕ, n ≠ 0 → m ≠ 0 → xiOf n + xiOf m = xiOf ((n * m : ℕ) : ℝ)) ∧
      ∀ m : ℕ, 0 ≤ xiOf m :=
  ⟨fun H ξ => ⟨voronoiTerm_zero H ξ, voronoiTerm_one H ξ⟩, fun _ _ hn hm => xiOf_add_natCast hn hm,
    xiOf_natCast_nonneg⟩

/-- Given the Voronoi identity, `Ĝ_H ≥ 0` on `[a, ∞)` gives `F̂ ≥ 0` on `[a, ∞)` (no axiom). -/
theorem positivity_transfer {H : ℂ → ℂ} (hV : VoronoiIdentity H) {a : ℝ}
    (hG : ∀ ξ : ℝ, a ≤ ξ → 0 ≤ GammaFT H ξ) :
    ∀ ξ : ℝ, a ≤ ξ → 0 ≤ FT (fun z => Xi z ^ 2 * H z) ξ :=
  fun _ hξ => FT_nonneg_of_voronoi hV hG hξ

/-- Given the Voronoi identity, (C3) gives `F̂(ξ_n) = 0` for every `n ≥ 2`, and `F̂(0) = Ĝ_H(0)` (no axiom). -/
theorem vanishing_transfer {H : ℂ → ℂ} (hV : VoronoiIdentity H) (h3 : CondC3 H) :
    (∀ n : ℕ, 2 ≤ n → FT (fun z => Xi z ^ 2 * H z) (xiOf n) = 0) ∧
      FT (fun z => Xi z ^ 2 * H z) 0 = GammaFT H 0 :=
  ⟨fun _ hn => FT_xiOf_eq_zero_of_voronoi hV h3 hn, FT_zero_of_voronoi hV h3⟩

/-- The normalised cone elements that define `κ*` and `κ*_OPS` exist (the Gaussian has `∫ = 1`), so the slacks are
not the junk value `⊤`. -/
theorem cones_not_junk :
    gauss ∈ ConeOPS ∧ gauss ∈ Cone ∧ intR gauss = 1 ∧ kappaStar ≠ ⊤ ∧ kappaOPS ≠ ⊤ :=
  ⟨gauss_mem_ConeOPS, gauss_mem_Cone, intR_gauss, kappaStar_ne_top, kappaOPS_ne_top⟩

/-- An exact magic function forces `κ* ≤ 0`; one in `𝒞_OPS` forces `κ*_OPS ≤ 0` (Part I's definitions). -/
theorem exact_magic_meaning {F : ℂ → ℂ} :
    (IsExactMagic F → kappaStar ≤ 0) ∧
      (F ∈ ConeOPS → 0 < intR F → Arch F = 0 → kappaOPS ≤ 0) := by
  refine ⟨fun ⟨hC, hpos, hA⟩ => ?_, fun hO hpos hA => ?_⟩
  · have hk := slack_le homog_Arch (scalable_ConeG_Arch xi2) hC hpos
    rw [hA, zero_div] at hk
    exact_mod_cast hk
  · have hk := slack_le homog_Arch scalable_ConeOPS_Arch hO hpos
    rw [hA, zero_div] at hk
    exact_mod_cast hk

/-- If `H > 0` on `ℝ`, the real zeros of `Ξ² H` are exactly `Z_ζ`. -/
theorem zero_set_of_strict {H : ℂ → ℂ} (h : CondC2Strict H) : ZF (fun z => Xi z ^ 2 * H z) = Zzeta :=
  ZF_Xi_sq_mul h

/-- `H ∈ 𝒲_δ`, `H ≢ 0` on `S_δ` ⇒ `H(t) ≠ 0` for some real `t` (identity theorem). -/
theorem identity_theorem {δ : ℝ} {H : ℂ → ℂ} (hH : ClassW δ H)
    (hne : ∃ z ∈ closedStrip (1 / 2 + δ), H z ≠ 0) : ∃ t : ℝ, H t ≠ 0 :=
  hH.exists_real_ne_zero hne

/-- A function `ℝ → ℂ` that is `≥ 0` everywhere has derivative `0` (if any) at each of its zeros. -/
theorem deriv_at_zero_of_nonneg {f : ℝ → ℂ} {x₀ : ℝ} (hnn : ∀ x, 0 ≤ f x) (h0 : f x₀ = 0) {D : ℂ}
    (hD : HasDerivAt f D x₀) : D = 0 :=
  hasDerivAt_eq_zero_of_nonneg hnn h0 hD

/-- Lemma C.1 "Transfer across the gap" (`lem:transfer`), for `L = 𝒜`, uses no axiom: if `Θ ∈ 𝒞_OPS` has `Re Θ̂ > 0` on `[0, ℓ₁)` and
`𝒜(Θ) ≤ 0`, then `𝒜 ≥ 0` on `𝒞_OPS` implies `𝒜 ≥ 0` on `𝒞_{ℓ₁}`.  (Only the window positivity of the object, which is
an input, enters Corollary 8.2 through the ledger.) -/
theorem transfer_lemma {ℓ₁ : ℝ} {Θ : ℂ → ℂ} (hΘ : Θ ∈ ConeOPS)
    (hΘpos : ∀ ξ : ℝ, 0 ≤ ξ → ξ < ℓ₁ → 0 < (FT Θ ξ).re) (hAΘ : Arch Θ ≤ 0)
    (hA : ∀ F ∈ ConeOPS, 0 ≤ Arch F) : ∀ F ∈ ConeG ℓ₁, 0 ≤ Arch F :=
  transfer_Arch hΘ hΘpos hAΘ hA

/-- `𝒜` is additive on `𝒯` (the archimedean integral converges absolutely on `𝒯`, by Zeta23's bound for `Ω_∞`). -/
theorem arch_additive {F G : ℂ → ℂ} (hF : F ∈ TestClass) (hG : G ∈ TestClass) :
    Arch (fun z => F z + G z) = Arch F + Arch G ∧ (fun z => F z + G z) ∈ TestClass :=
  ⟨Arch_add hF hG, TestClass.add hF hG⟩

/-- At the gap `0` the cone is the classical one: `𝒞_0 = 𝒞_OPS`. -/
theorem classical_cone_zero : ConeG 0 = ConeOPS :=
  ConeG_zero_eq

end PosRigII.NonVacuity

#print axioms PosRigII.NonVacuity.classW_nonempty
#print axioms PosRigII.NonVacuity.gammaInf_faithful
#print axioms PosRigII.NonVacuity.voronoi_indexing
#print axioms PosRigII.NonVacuity.positivity_transfer
#print axioms PosRigII.NonVacuity.vanishing_transfer
#print axioms PosRigII.NonVacuity.cones_not_junk
#print axioms PosRigII.NonVacuity.exact_magic_meaning
#print axioms PosRigII.NonVacuity.zero_set_of_strict
#print axioms PosRigII.NonVacuity.identity_theorem
#print axioms PosRigII.NonVacuity.deriv_at_zero_of_nonneg
#print axioms PosRigII.NonVacuity.transfer_lemma
#print axioms PosRigII.NonVacuity.arch_additive
#print axioms PosRigII.NonVacuity.classical_cone_zero
