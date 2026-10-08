/-
# The main results of Part II: Theorem S (`thm:main-S`), Theorem U (`thm:main-U`), Corollary (`cor:main-RH`)

Each theorem is stated with Part I's definitions (`κ*`, `κ*_OPS`, `𝒞`, `𝒞_OPS`, `𝒦`, `p_ζ`, (E), (S), (U), `q_min`),
reused from Part I's spine, and proved from Mathlib, Part I's spine (its theorems and ledger axioms) and the two
ledger axioms of `Ledger.lean`.  `axioms.log` records `#print axioms` for each.

Theorem S is unconditional and says `κ* ≤ κ*_OPS ≤ 0`; it does not say that `κ*` is attained.  Attainment is the
content of `corollary_minimiser`: `F/∫F` is a minimiser for `κ*` if and only if RH holds.  Corollary 3 states
`RH ⇔ (E) ⇔ κ* ≥ 0 ⇔ κ* = 0` and gives `RH ⇒ κ*_OPS = 0`; the converse, `κ*_OPS = 0 ⇒ RH`, is Corollary 8.2
(`cor:nogap`; `NoGap.lean`, `rh_iff_kappaOPS_zero`).
-/
import PositivityRigidityII.Object

noncomputable section

open Complex MeasureTheory Filter Topology
open scoped FourierTransform ComplexOrder

namespace PosRigII

open PosRig

/-- **Theorem S (`thm:main-S`), last sentence: `κ* ≤ κ*_OPS ≤ 0`, unconditionally.**  (The exact magic function
`F = Ξ² H` of `theorem1_object` lies in `𝒞_OPS`, has `∫ F > 0` and `𝒜(F) = 0`, so `κ*_OPS ≤ 𝒜(F)/∫ F = 0`; and
`κ* ≤ κ*_OPS` because `𝒞_OPS ⊆ 𝒞`.) -/
theorem theorem1 : kappaStar ≤ kappaOPS ∧ kappaOPS ≤ 0 := by
  obtain ⟨H, -, -, -, hOPS, -, -, hpos, hA, -, -, -⟩ := theorem1_object
  refine ⟨kappaStar_le_kappaOPS, ?_⟩
  have hk := slack_le homog_Arch scalable_ConeOPS_Arch hOPS hpos
  rw [hA, zero_div] at hk
  exact_mod_cast hk

/-- **Theorem S (`thm:main-S`), "In particular":** Conjecture S holds (`κ* ≤ 0`), and `q_min ≥ 1`, already for the
classical cone: `q_min = e^{−2πκ*} ≥ 1` and `e^{−2πκ*_OPS} ≥ 1`. -/
theorem theorem1_conductor : CondS ∧ 1 ≤ qmin ∧ 1 ≤ qminOPS := by
  have h1 := theorem1
  have hS : CondS := le_trans h1.1 h1.2
  refine ⟨hS, ?_, ?_⟩
  · unfold qmin
    have h0 : kappaStar.toReal ≤ 0 := EReal.toReal_nonpos hS
    rw [Real.one_le_exp_iff]
    nlinarith [Real.pi_pos]
  · unfold qminOPS
    have h0 : kappaOPS.toReal ≤ 0 := EReal.toReal_nonpos h1.2
    rw [Real.one_le_exp_iff]
    nlinarith [Real.pi_pos]

/-- **Theorem S, the slacks are finite** (so "`≤ 0`" is not about a junk value): `κ*` and `κ*_OPS` are real
numbers (Part I: `κ* ≥ −1.3231` by the floor in the proof of Proposition 2.8, `κ* ≤ κ*_OPS`, and `κ*_OPS < ∞`, by the
Gaussian). -/
theorem theorem1_finite : kappaStar ≠ ⊥ ∧ kappaStar ≠ ⊤ ∧ kappaOPS ≠ ⊥ ∧ kappaOPS ≠ ⊤ :=
  ⟨kappaStar_ne_bot, kappaStar_ne_top, kappaOPS_ne_bot, kappaOPS_ne_top⟩

/-- **Theorem U (`thm:main-U`).**  Every admissible pair is `ζ`'s pair: `(μ, ν) ∈ 𝒦 ⇒ (μ, ν) = p_ζ`.  (Part I's
Corollary 3.9(a), the magic-function principle, which rests on complementary slackness and Theorem 3.6, applied to
`F = Ξ² H`: `F ∈ 𝒞`, `𝒜(F) = 0`, and the real zeros of `F` are exactly `Z_ζ`, because `H > 0` on `ℝ`.) -/
theorem theorem2 : ∀ p ∈ K, p = pZeta := by
  obtain ⟨H, -, -, -, -, -, -, -, hA, hC, -, hZ⟩ := theorem1_object
  have hU := (magic_principle_zero hC hA (by rw [hZ]; exact Set.subset_union_left)).1
  exact fun p hp => hU hp

/-- **Theorem U (`thm:main-U`), as Part I's statement (U): `𝒦 ⊆ {p_ζ}`, i.e. Conjecture U holds.** -/
theorem theorem2_condU : CondU := fun _ hp => theorem2 _ hp

/-- **Corollary (`cor:main-RH`), the equivalences.**  The following are equivalent: (i) RH; (ii) admissible pairs
exist ((E)); (iii) `κ* ≥ 0`; (iv) `κ* = 0`.  (Part I's Theorem 2.9(c) with Theorem U gives (i) ⇔ (ii) ⇔ (iii), the
second through Theorem 2.7(a); Theorem S gives (iii) ⇔ (iv).) -/
theorem corollary3 :
    (RiemannHypothesis ↔ CondE) ∧ (CondE ↔ 0 ≤ kappaStar) ∧ (0 ≤ kappaStar ↔ kappaStar = 0) := by
  have hS := theorem1
  obtain ⟨hRE, hEk⟩ := logic_c.2.2 theorem2_condU
  exact ⟨hRE, hEk, ⟨fun h => le_antisymm (hS.1.trans hS.2) h, fun h => h ▸ le_rfl⟩⟩

/-- **Corollary (`cor:main-RH`), if they hold.**  Under RH: `𝒦 = {p_ζ}`, `κ* = κ*_OPS = 0`, and the optimised
conductor bounds are exactly `1`: `q_min = e^{−2πκ*_OPS} = 1`.  (The converse `κ*_OPS = 0 ⇒ RH` is Corollary 8.2, `rh_iff_kappaOPS_zero`.) -/
theorem corollary3_RH (hRH : RiemannHypothesis) :
    K = {pZeta} ∧ kappaStar = 0 ∧ kappaOPS = 0 ∧ qmin = 1 ∧ qminOPS = 1 := by
  have hK : K = {pZeta} := (logic_c.1.mp theorem2_condU).2 hRH
  have hk : kappaStar = 0 := corollary3.2.2.mp (corollary3.2.1.mp (corollary3.1.mp hRH))
  have h1 := theorem1
  have hOPS : kappaOPS = 0 := le_antisymm h1.2 (by rw [← hk]; exact h1.1)
  refine ⟨hK, hk, hOPS, ?_, ?_⟩
  · unfold qmin
    rw [hk]
    simp
  · unfold qminOPS
    rw [hOPS]
    simp

/-- **Corollary (`cor:main-RH`), last sentence.**  If RH fails, then `κ* < 0` and `𝒦 = ∅`. -/
theorem corollary3_notRH (hRH : ¬ RiemannHypothesis) : kappaStar < 0 ∧ K = ∅ := by
  have hE : ¬ CondE := fun hE => hRH (corollary3.1.mpr hE)
  exact ⟨not_le.mp fun h => hE (corollary3.2.1.mpr h), Set.not_nonempty_iff_eq_empty.mp hE⟩

/-- **Corollary (`cor:main-RH`), the minimiser, and the precise sense in which `κ*` is attained.**  For the exact
magic function `F = Ξ² H` of Theorem S: unconditionally `κ* ≤ κ*_OPS ≤ 𝒜(F)/∫ F = 0`; `F/∫ F` is a minimiser for
`κ*` (`κ* = 𝒜(F)/∫ F`) if and only if RH holds; and under RH it is a minimiser for `κ*_OPS` as well. -/
theorem corollary_minimiser :
    ∃ H : ℂ → ℂ, (∃ δ : ℝ, δ < 1 / 2 ∧ IntegerCritical δ H) ∧ CondC2Strict H ∧
      IsExactMagic (fun z => Xi z ^ 2 * H z) ∧ (fun z => Xi z ^ 2 * H z) ∈ ConeOPS ∧
      kappaStar ≤ kappaOPS ∧
      kappaOPS ≤ ((Arch (fun z => Xi z ^ 2 * H z) / intR (fun z => Xi z ^ 2 * H z) : ℝ) : EReal) ∧
      (kappaStar = ((Arch (fun z => Xi z ^ 2 * H z) / intR (fun z => Xi z ^ 2 * H z) : ℝ) : EReal) ↔
        RiemannHypothesis) ∧
      (RiemannHypothesis →
        kappaOPS = ((Arch (fun z => Xi z ^ 2 * H z) / intR (fun z => Xi z ^ 2 * H z) : ℝ) : EReal)) := by
  obtain ⟨H, hIC, -, h2s, hOPS, -, -, -, hA, -, hM, -⟩ := theorem1_object
  have hq : ((Arch (fun z => Xi z ^ 2 * H z) / intR (fun z => Xi z ^ 2 * H z) : ℝ) : EReal) = 0 := by
    rw [hA, zero_div, EReal.coe_zero]
  refine ⟨H, hIC, h2s, hM, hOPS, kappaStar_le_kappaOPS, ?_, ?_, fun hRH => ?_⟩
  · rw [hq]
    exact theorem1.2
  · rw [hq]
    exact ⟨fun h => corollary3.1.mpr (corollary3.2.1.mpr (corollary3.2.2.mpr h)),
      fun hRH => (corollary3_RH hRH).2.1⟩
  · rw [hq]
    exact (corollary3_RH hRH).2.2.1

/-- **Summary: Conjectures S and U of Part I hold, and `RH ⇔ (E) ⇔ κ* = 0`.** -/
theorem main_summary :
    CondS ∧ CondU ∧ (RiemannHypothesis ↔ CondE) ∧ (CondE ↔ kappaStar = 0) :=
  ⟨theorem1_conductor.1, theorem2_condU, corollary3.1, corollary3.2.1.trans corollary3.2.2⟩

end PosRigII
