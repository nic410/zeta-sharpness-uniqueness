/-
Positivity–rigidity, Part II: definitions.

Part II proves Conjectures S and U of Part I.  This file contains *definitions only* (no axioms, no theorems).
Every object of Part I (the test class `𝒯`, the cones `𝒞`, `𝒞_OPS`, the functional `Arch`, the slacks `κ*`,
`κ*_OPS`, the admissible pairs `𝒦`, `p_ζ`, `Ξ`, `ξ_n`, (E), (S), (U), `q_min`, …) is reused from Part I's spine
(namespace `PosRig`, library `PositivityRigidity`) and is not redefined here.  New here:

* the archimedean factor `γ_∞` and the Γ-only transform `Ĝ_H` (Part II, (eq:GH));
* the class `𝒲_δ` (Definition "The class 𝒲_δ", label `def:W`) and the conditions (C2)–(C5) of Proposition
  "Exact magic functions from Γ-only data" (`prop:reduction`); Γ-only integer-critical functions;
* the terms of the Voronoi decoupling `F̂(ξ) = Σ_{m ≥ 1} d(m) m^{-1/2} Ĝ_H(ξ + ξ_m)` (Lemma "Voronoi decoupling",
  `lem:voronoi`), and its conclusion as a proposition about `H` (`VoronoiIdentity`).

Statements of Part II are cited by name and LaTeX label; numbers are added when the paper fixes them.
-/
import PositivityRigidity

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder

namespace PosRigII

open PosRig

/-! ## The archimedean factor `γ_∞` and the Γ-only transform -/

/-- `γ_∞(s) = ½ s(s−1) π^{−s/2} Γ(s/2) = (s − 1) π^{−s/2} Γ(1 + s/2)` (Part II, (eq:gi); the paper writes
`γ_∞(t)` for its value at `s = ½ + it`).

The second form is used: it has no removable singularity at `s = 0` (where `γ_∞(0) = −1`), so the Lean
function is `γ_∞` on all of `Re s > −2`, without a junk value.  `gammaInf_eq_gammaR` (`Faithful.lean`) checks
`γ_∞(s) = ½ s(s−1) Γ_ℝ(s)` (Mathlib's `Complex.Gammaℝ s = π^{−s/2} Γ(s/2)`) for `s ≠ 0`, and
`Xi_eq_gammaInf_mul_zeta` checks `Ξ(t) = γ_∞(½ + it) ζ(½ + it)` on the real line.  Only the values on the line
`Re s = ½` enter the Γ-only transform. -/
def gammaInf (s : ℂ) : ℂ := (s - 1) * (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2 + 1)

/-- `G_H(z) = γ_∞(½ + iz)² H(z)` (Part II, (eq:GH)): the Γ-factor part of `F = Ξ² H`. -/
def GammaOnly (H : ℂ → ℂ) : ℂ → ℂ := fun z => gammaInf (1 / 2 + I * z) ^ 2 * H z

/-- The Γ-only transform `Ĝ_H(ξ) = ∫_ℝ G_H(t) e^{−2πiξt} dt` (Part II, (eq:GH); Part I's normalisation of the
Fourier transform, `FT`).  In the variable `x = e^{2πξ}` the paper writes `Ĝ_H(x)`; `x = n` is `ξ = ξ_n`. -/
def GammaFT (H : ℂ → ℂ) : ℝ → ℂ := FT (GammaOnly H)

/-! ## The class `𝒲_δ` and the integer-critical conditions -/

/-- The class `𝒲_δ` (Definition "The class `𝒲_δ`", `def:W`), for `0 < δ < 1`: `H` is even, real on `ℝ`, analytic
on a neighbourhood of the closed strip `S_δ = {|Im z| ≤ 1/2 + δ}`, and satisfies (C1):
`sup_{z ∈ S_δ} (1 + |z|)⁸ e^{−π|Re z|/2} |H(z)| < ∞`.

Conventions as in Part I's `𝒯_δ` (`InTδ`): `H : ℂ → ℂ`, only its values on `S_δ` matter, evenness is required on
`S_δ`, and `AnalyticOnNhd ℂ H S` means "analytic at every point of `S`". -/
structure ClassW (δ : ℝ) (H : ℂ → ℂ) : Prop where
  pos : 0 < δ
  lt_one : δ < 1
  even : ∀ z ∈ closedStrip (1 / 2 + δ), H (-z) = H z
  real : ∀ t : ℝ, (H t).im = 0
  analytic : AnalyticOnNhd ℂ H (closedStrip (1 / 2 + δ))
  bound : ∃ C : ℝ, ∀ z ∈ closedStrip (1 / 2 + δ),
    (1 + ‖z‖) ^ 8 * ‖H z‖ ≤ C * Real.exp (Real.pi / 2 * |z.re|)

/-- (C2) `H ≥ 0` on `ℝ` (`0 ≤ z` for `z : ℂ` is Mathlib's order on `ℂ`: `z` real and `≥ 0`). -/
def CondC2 (H : ℂ → ℂ) : Prop := ∀ t : ℝ, 0 ≤ H t

/-- (C2), strictly: `H(t) > 0` for every real `t`. -/
def CondC2Strict (H : ℂ → ℂ) : Prop := ∀ t : ℝ, 0 < H t

/-- (C3) `Ĝ_H(ξ_k) = 0` for every integer `k ≥ 2` (`ξ_k = log k/2π`, i.e. `Ĝ_H(x = k) = 0`). -/
def CondC3 (H : ℂ → ℂ) : Prop := ∀ k : ℕ, 2 ≤ k → GammaFT H (xiOf k) = 0

/-- (C4) `Ĝ_H ≥ 0` on `[ξ₂, ∞)` (`x ≥ 2`). -/
def CondC4 (H : ℂ → ℂ) : Prop := ∀ ξ : ℝ, xi2 ≤ ξ → 0 ≤ GammaFT H ξ

/-- `Ĝ_H ≥ 0` on `[0, ∞)` (`x ≥ 1`): the hypothesis of the last sentence of Proposition `prop:reduction`, which
gives `F ∈ 𝒞_OPS`. -/
def CondC4Zero (H : ℂ → ℂ) : Prop := ∀ ξ : ℝ, 0 ≤ ξ → 0 ≤ GammaFT H ξ

/-- `Ĝ_H > 0` on the window `[0, ξ₂)` (`1 ≤ x < 2`): the strict positivity of the Γ-only transform used in the proof
of Corollary 8.2 (`cor:nogap`, "The classical cone"), part (a). -/
def CondWindow (H : ℂ → ℂ) : Prop := ∀ ξ : ℝ, 0 ≤ ξ → ξ < xi2 → 0 < GammaFT H ξ

/-- (C5) `Ĝ_H(0) > 0` (`x = 1`); automatic under (C2) and (C3) for `H ≢ 0` (`condC5_of`). -/
def CondC5 (H : ℂ → ℂ) : Prop := 0 < GammaFT H 0

/-- A Γ-only integer-critical function (Part II, after Proposition `prop:reduction`): `H ∈ 𝒲_δ` with `H(0) = 1`
satisfying (C2)–(C4). -/
def IntegerCritical (δ : ℝ) (H : ℂ → ℂ) : Prop :=
  ClassW δ H ∧ H 0 = 1 ∧ CondC2 H ∧ CondC3 H ∧ CondC4 H

/-! ## The Voronoi decoupling -/

/-- The `m`-th term `d(m) m^{−1/2} Ĝ_H(ξ + ξ_m)` of the Voronoi decoupling (eq:voronoi), `d = σ₀` the divisor
function.  For `m = 0` the term is `0` (`σ₀(0) = 0` in Mathlib), so sums over `ℕ` are sums over `m ≥ 1`. -/
def voronoiTerm (H : ℂ → ℂ) (ξ : ℝ) (m : ℕ) : ℂ :=
  (((ArithmeticFunction.sigma 0 m : ℕ) : ℝ) / Real.sqrt m : ℝ) * GammaFT H (ξ + xiOf m)

/-- The conclusion of Lemma "Voronoi decoupling" (`lem:voronoi`), parts (b) and (c), for `H`: `G_H` is integrable
on `ℝ` (so `Ĝ_H` is a genuine Fourier integral), and for every real `ξ` the series
`Σ_{m ≥ 1} d(m) m^{−1/2} Ĝ_H(ξ + ξ_m)` converges absolutely (`Summable` in `ℂ`) to `F̂(ξ)`, `F = Ξ² H`. -/
def VoronoiIdentity (H : ℂ → ℂ) : Prop :=
  Integrable (onR (GammaOnly H)) ∧
    ∀ ξ : ℝ, Summable (voronoiTerm H ξ) ∧
      FT (fun z => Xi z ^ 2 * H z) ξ = ∑' m : ℕ, voronoiTerm H ξ m

end PosRigII
