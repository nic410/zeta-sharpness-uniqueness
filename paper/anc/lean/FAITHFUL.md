# Faithfulness: each Lean statement against the paper

Each headline Lean statement, the paper statement it transcribes (by name and LaTeX label of the Part II draft), and
every difference between the two. Lean names are in namespace `PosRigII`; Part I's objects are in namespace `PosRig`
(Part I's spine) and are reused, not redefined. Notation: `F = Ξ² H`, `F̂ = FT F`, `Ĝ_H = GammaFT H`, `ξ_n = xiOf n`.

## Conventions inherited from Part I's spine

* Functions are `ℂ → ℂ`; only their values on the relevant closed strip enter. `F̂` is Mathlib's Fourier transform of
  the restriction to `ℝ`, with the paper's normalisation `F̂(ξ) = ∫ F(t) e^{−2πiξt} dt`.
* `0 ≤ z` and `0 < z` for `z : ℂ` are Mathlib's order on `ℂ`: `z` is real and `≥ 0` (resp. `> 0`). So "`F̂ ≥ 0`" also
  says that `F̂` is real, as it is in the paper.
* `κ*`, `κ*_OPS` are `EReal` infima (`kappaStar`, `kappaOPS`); `q_min = e^{−2πκ*}` and `e^{−2πκ*_OPS}` are `qmin`,
  `qminOPS`. (E), (S), (U) are `CondE` (`𝒦 ≠ ∅`), `CondS` (`κ* ≤ 0`), `CondU` (`𝒦 ⊆ {p_ζ}`). `RiemannHypothesis` is
  Mathlib's. `𝒦` is `K`, the admissible pairs of Part I's Definition 2.4. See Part I's `README.md`, "Faithfulness".

## Definitions (`Defs.lean`)

| Paper | Lean | Notes |
|---|---|---|
| `γ_∞(s) = ½ s(s−1) π^{−s/2} Γ(s/2)` (eq:gi) | `gammaInf` | Written as `(s − 1) π^{−s/2} Γ(1 + s/2)`, equal for `s ≠ 0` (`gammaInf_eq_gammaR`) and with the true value `−1` at `s = 0` (`gammaInf_zero`); `Ξ(t) = γ_∞(½ + it) ζ(½ + it)` on `ℝ` is proved (`Xi_eq_gammaInf_mul_zeta`) |
| `G_H = γ_∞² H`, `Ĝ_H(ξ) = ∫ G_H(t) e^{−2πiξt} dt` (eq:GH) | `GammaOnly`, `GammaFT` | `G_H(z) = γ_∞(½ + iz)² H(z)`; only real `z` enter `Ĝ_H` |
| The class `𝒲_δ`, `0 < δ < 1` (Definition `def:W`), with (C1) | `ClassW δ H` | Even on `S_δ`, real on `ℝ`, `AnalyticOnNhd` on the closed strip (= analytic on a neighbourhood), and `(1 + ‖z‖)⁸ ‖H z‖ ≤ C e^{π|Re z|/2}` on `S_δ`, which is (C1) |
| (C2) `H ≥ 0` on `ℝ`; `H > 0` on `ℝ` | `CondC2`, `CondC2Strict` | |
| (C3) `Ĝ_H(ξ_k) = 0`, every integer `k ≥ 2` | `CondC3` | |
| (C4) `Ĝ_H ≥ 0` on `[ξ₂, ∞)`; `Ĝ_H ≥ 0` on `[0, ∞)` | `CondC4`, `CondC4Zero` | |
| `Ĝ_H > 0` on `[0, ξ₂)` (`1 ≤ x < 2`), used in Corollary 8.2(a) | `CondWindow` | Added for Corollary 8.2, as a conjunct of the object axiom |
| (C5) `Ĝ_H(0) > 0` | `CondC5` | Not a hypothesis of the paper's proposition (which assumes `H ≢ 0`); proved from it (`condC5_of`) |
| Γ-only integer-critical function: `H ∈ 𝒲_δ`, `H(0) = 1`, (C2)–(C4) (after Proposition `prop:reduction`) | `IntegerCritical δ H` | |
| The `m`-th term of (eq:voronoi), `d(m) m^{−1/2} Ĝ_H(ξ + ξ_m)` | `voronoiTerm` | `d = σ₀`; the term `m = 0` is `0`, so `∑'` over `ℕ` is the sum over `m ≥ 1` (`voronoiTerm_zero`, `voronoiTerm_one`) |
| Lemma `lem:voronoi` (b), (c): `G_H ∈ L¹(ℝ)` and (eq:voronoi), absolutely convergent | `VoronoiIdentity H` | `Summable` in `ℂ` is absolute convergence |

## Theorems

| Paper | Lean | File | Status | Differences |
|---|---|---|---|---|
| Theorem S (`thm:main-S`), last sentence: `κ* ≤ κ*_OPS ≤ 0` | `theorem1 : kappaStar ≤ kappaOPS ∧ kappaOPS ≤ 0` | `Main.lean` | proved from axioms | none; unconditional; nothing is said about attainment |
| Theorem S, "In particular Conjecture S holds, and `q_min ≥ 1`, already for the classical cone" | `theorem1_conductor : CondS ∧ 1 ≤ qmin ∧ 1 ≤ qminOPS` | `Main.lean` | proved from axioms | none |
| — (supports Theorem S: the slacks are real numbers) | `theorem1_finite : kappaStar ≠ ⊥ ∧ kappaStar ≠ ⊤ ∧ kappaOPS ≠ ⊥ ∧ kappaOPS ≠ ⊤` | `Main.lean` | proved from Part I's axiom `floor_bound` | not a statement of Part II (Part I, Proposition 2.8) |
| Theorem S, first part: there is an even entire `H`, real on `ℝ`, `H > 0` on `ℝ`, `H(0) = 1`, with (eq:intro-C1) for every `δ ∈ (0, 1)`, such that `F = Ξ² H` has (a) `F ∈ 𝒞_OPS`, (b) `F̂(ξ_n) = F̂′(ξ_n) = 0` for `n ≥ 2`, (c) `∫ F = F̂(0) > 0` and `𝒜(F) = 0` | `theorem1_object` | `Object.lean` | proved from axioms | weaker in the class of `H`: `H ∈ 𝒲_δ` for one `δ < 1/2` (the paper: entire, and the bound with exponent `−9 + δ` for every `δ < 1`); (b) is stated as "`F̂(ξ_n) = 0`, and every `D` with `HasDerivAt F̂ D ξ_n` is `0`" — the differentiability of `F̂`, which the paper gets from `tF ∈ L¹` with the exponent `−9 + δ`, is not formalised; the theorem also gives `F ∈ 𝒞`, `IsExactMagic F`, `ZF F = Z_ζ` and that `H` is integer-critical |
| Theorem U (`thm:main-U`): `𝒦_ad ⊆ {p_ζ}`, Conjecture U | `theorem2 : ∀ p ∈ K, p = pZeta`; `theorem2_condU : CondU` | `Main.lean` | proved from axioms | none (the conclusion is vacuous if `𝒦 = ∅`, as in the paper: under RH, `p_ζ ∈ 𝒦` by Part I's Theorem 2.9(a)) |
| Corollary (`cor:main-RH`): (i) RH, (ii) (E), (iii) `κ* ≥ 0`, (iv) `κ* = 0` are equivalent | `corollary3 : (RiemannHypothesis ↔ CondE) ∧ (CondE ↔ 0 ≤ kappaStar) ∧ (0 ≤ kappaStar ↔ kappaStar = 0)` | `Main.lean` | proved from axioms | none |
| Corollary: if they hold, `𝒦_ad = {p_ζ}`, `κ*_OPS = 0` (and, in the text after it, the optimised conductor bound is exactly `1` in either cone) | `corollary3_RH : RiemannHypothesis → K = {pZeta} ∧ kappaStar = 0 ∧ kappaOPS = 0 ∧ qmin = 1 ∧ qminOPS = 1` | `Main.lean` | proved from axioms | hypothesis RH (equivalent to the others by `corollary3`); `κ*_OPS = 0 ⇒ RH` is not claimed |
| Corollary: `F/∫F` is a minimiser for both `κ*` and `κ*_OPS` if they hold; the text after Theorem S: `κ*` is not claimed to be attained, unconditionally `κ* ≤ 0 = 𝒜(F)/∫F` | `corollary_minimiser` | `Main.lean` | proved from axioms | states in addition the converse: `κ* = 𝒜(F)/∫F` (i.e. `F/∫F` is a minimiser for `κ*`) if and only if RH |
| Corollary: if RH fails, then `κ* < 0` and `𝒦_ad = ∅` | `corollary3_notRH` | `Main.lean` | proved from axioms | none |
| Conjectures S and U hold, and RH ⇔ (E) ⇔ `κ* = 0` | `main_summary` | `Main.lean` | proved from axioms | a summary |
| Lemma "Voronoi decoupling" (`lem:voronoi`), (a): `H ∈ 𝒲_δ`, `δ < 1/2` ⇒ `Ξ² H ∈ 𝒯_δ` | `classW_inTδ`, `classW_mem_TestClass` | `Reduction.lean` | proved from Part I's axiom `xi_decay` | none |
| Lemma `lem:voronoi`, (b) (integrability of `G_H`) and (c) | `voronoi_decoupling` | `Ledger.lean` | **ledger axiom** | the bounds of (b) and of the `m`-th term in (c) are not stated |
| Proposition "Exact magic functions from Γ-only data" (`prop:reduction`): `0 < δ < 1/2`, `H ∈ 𝒲_δ`, `H ≢ 0`, (C2)–(C4) ⇒ `F ∈ 𝒞`, `F̂(ξ_n) = 0` (`n ≥ 2`), `∫ F = F̂(0) = Ĝ_H(0) > 0`, `𝒜(F) = 0`; `F` exact magic and `κ* ≤ 0` | `reduction` | `Reduction.lean` | proved from axioms | "`H ≢ 0`" is "`H(z) ≠ 0` for some `z ∈ S_δ`"; the identity theorem turns it into a real point with `H(t) ≠ 0` (`ClassW.exists_real_ne_zero`) |
| Proposition `prop:reduction`, last sentence: if moreover `Ĝ_H ≥ 0` on `[0, ∞)`, then `F ∈ 𝒞_OPS` and `κ*_OPS ≤ 0` | `reduction_OPS` | `Reduction.lean` | proved from axioms | (C4), implied by the new hypothesis, is not assumed |
| (C5) `Ĝ_H(0) = ∫ F > 0` (the proposition's `∫ F = Ĝ_H(0) > 0`) | `condC5_of` | `Reduction.lean` | proved from axioms | |
| The object: Theorem "The object" (`thm:main-object`) with Corollary `cor:Pi-positive`, as used in the proof of Theorem S | `exists_integer_critical_object` | `Ledger.lean` | **ledger axiom** | weaker: see `LEDGER.md` |
| The normalisation `H := H_raw/H_raw(0)` (`sec:assembly`) | `exists_object` | `Object.lean` | proved from axioms | also carries the window clause |
| Corollary 8.2 (`cor:nogap`, "The classical cone"), last sentence: RH ⟺ `𝒜(F) ≥ 0` for every `F ∈ 𝒯` with `F ≥ 0`, `F̂ ≥ 0` on `ℝ` ⟺ `κ*_OPS = 0` | `rh_iff_kappaOPS_zero : (RH ↔ ∀ F ∈ ConeOPS, 0 ≤ Arch F) ∧ (RH ↔ 0 ≤ kappaOPS) ∧ (RH ↔ kappaOPS = 0) ∧ (¬RH → kappaStar ≤ kappaOPS ∧ kappaOPS < 0)` | `NoGap.lean` | proved from axioms | adds `κ*_OPS ≥ 0` and the case `ℓ = 0` of (d) |
| Corollary 8.2 (a): `F̂₀ ≥ Ĝ_H > 0` on `[0, ξ₂)`, `F̂₀ > 0` on `(−ξ₂, ξ₂)`, real zeros of `F̂₀` exactly `±ξ_n` | `FT_window` | `NoGap.lean` | proved from axioms | the zero-set statement is not formalised; the comparison `F̂₀ ≥ Ĝ_H` is stated in `ℂ`'s order (both sides real) |
| Corollary 8.2 (b): `0 ≤ ℓ ≤ ξ₂` ⇒ every `(μ, ν) ∈ 𝒦_ℓ` has `ν([ℓ, ξ₂)) = 0`; `𝒦_ℓ = 𝒦` | `corollary8_2_b : Kset Arch ℓ = K` | `NoGap.lean` | proved from axioms | `𝒦_ℓ` is Part I's `Kset Arch ℓ` (pairs admissible at the gap `ℓ`; an atom of `ν` at `0` is allowed when `ℓ = 0`); the set equality contains the statement on `ν` |
| Corollary 8.2 (c), (d), `0 ≤ ℓ ≤ ξ₂`: (i) RH, (ii) `𝒦_ℓ ≠ ∅`, (iii) `𝒜 ≥ 0` on `𝒞_ℓ`, (iv) on `𝒞_ℓ ∩ 𝒢`, (v) `κ*_ℓ ≥ 0`, (vi) `κ*_ℓ = 0` are equivalent; RH ⇒ `𝒦_ℓ = {p_ζ}`, `κ*_ℓ = 0`; ¬RH ⇒ `𝒦_ℓ = ∅`, `κ* ≤ κ*_ℓ ≤ κ*_OPS < 0` | `corollary8_2` | `NoGap.lean` | proved from axioms | clause (iv) is omitted (it needs Proposition C.2, not formalised); `𝒞_ℓ` is `ConeG ℓ` and `κ*_ℓ` is `slack Arch (ConeG ℓ)` (Part I §5.5); `𝒞_0 = 𝒞_OPS` is `ConeG_zero_eq`; "`κ*_ℓ = 0` under RH" is the equivalence (i) ⟺ (vi) |
| — (by-product of Lemma C.1 and Theorem S, without Theorem U or duality): `κ* ≥ 0` ⟺ `κ*_OPS ≥ 0` | `kappaStar_nonneg_iff_kappaOPS_nonneg`, `arch_nonneg_Cone_iff_ConeOPS` | `NoGap.lean` | proved from axioms | the optional addition suggested by the referee of Corollary 8.2 |
| Lemma C.1 "Transfer across the gap" (`lem:transfer`): `ℓ₁ > 0`, `Θ ∈ 𝒞_OPS` with `Θ̂ > 0` on `[0, ℓ₁)`, `L : 𝒯 → ℝ` linear with `L(Θ) ≤ 0`; if `L ≥ 0` on `𝒞_OPS` then `L ≥ 0` on `𝒞_{ℓ₁}` (hence on `𝒞_ℓ`, `ℓ ≤ ℓ₁`) | `transfer`; for `L = 𝒜`, `transfer_Arch` | `NoGap.lean` | **proved (Mathlib and Zeta23; no ledger axiom)** | "linear" is "additive on `𝒯` and homogeneous for real scalars"; the hypothesis `ℓ₁ > 0` is not needed; "hence on `𝒞_ℓ`" is `ConeG_mono` |

The two ledger axioms, and the six axioms of Part I that the spine uses, are described in `LEDGER.md`.

## Non-vacuity

`scripts/NonVacuity.lean` (audit check (f)) proves, from Mathlib (and Zeta23 through Part I) alone, with no ledger
axiom of Part I or Part II:

| Theorem | What it shows |
|---|---|
| `classW_nonempty` | `𝒲_δ` contains the constant `1` for every `0 < δ < 1`, which is positive on `ℝ`: the hypothesis of `voronoi_decoupling` can be met |
| `gammaInf_faithful` | `γ_∞(s) = ½ s(s−1) Γ_ℝ(s)` (`s ≠ 0`), `γ_∞(0) = −1`, `Ξ(t) = γ_∞(½ + it) ζ(½ + it)` on `ℝ` |
| `voronoi_indexing` | the Voronoi series starts at `m = 1` with the term `Ĝ_H(ξ)`; `ξ_n + ξ_m = ξ_{nm}`; `ξ_m ≥ 0` |
| `positivity_transfer` | given the Voronoi identity, `Ĝ_H ≥ 0` on `[a, ∞)` ⇒ `F̂ ≥ 0` on `[a, ∞)` — the elementary positivity transfer `F̂(x) = Σ d(m) m^{−1/2} Ĝ_H(mx) ≥ 0` |
| `vanishing_transfer` | given the Voronoi identity, (C3) ⇒ `F̂(ξ_n) = 0` for `n ≥ 2`, and `F̂(0) = Ĝ_H(0)` |
| `cones_not_junk` | the Gaussian lies in `𝒞_OPS ⊆ 𝒞` with `∫ = 1`, so `κ*, κ*_OPS < ∞` is not a junk value |
| `exact_magic_meaning` | an exact magic function forces `κ* ≤ 0`; one in `𝒞_OPS` forces `κ*_OPS ≤ 0` |
| `zero_set_of_strict` | `H > 0` on `ℝ` ⇒ the real zeros of `Ξ² H` are exactly `Z_ζ` (how Theorem U uses strict positivity) |
| `identity_theorem` | "`H ≢ 0`" in Proposition `prop:reduction` gives a real point with `H(t) ≠ 0` |
| `deriv_at_zero_of_nonneg` | a non-negative real-valued function has derivative `0`, if any, at each of its zeros (Theorem S(b)) |
| `transfer_lemma` | Lemma C.1 for `𝒜` uses no axiom: only the window positivity of the object, an input, reaches Corollary 8.2 through the ledger |
| `arch_additive` | `𝒜` is additive on `𝒯` and `𝒯` is closed under addition (the archimedean integral converges absolutely on `𝒯`) |
| `classical_cone_zero` | `𝒞_0 = 𝒞_OPS`: Corollary 8.2 at the gap `0` is about the classical cone |

The lower finiteness `κ* ≠ ⊥` needs Part I's `floor_bound` and is `theorem1_finite`, not a non-vacuity theorem.

## What the Lean kernel does and does not check

The kernel checks that the headline statements follow from Mathlib, Part I's spine and the two axioms of Part II. It
does not check the axioms: the Voronoi decoupling, the construction of the object and its positivity (with the
certificates) are the paper's. `scripts/check_provenance.py` checks only that the docstrings quote the shipped logs
and cite the shipped files correctly.
