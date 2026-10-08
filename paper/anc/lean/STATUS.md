# Status: every statement of Part II

The statements of the Part II draft, in order, by name and LaTeX label (numbers will be added when the paper fixes
them). Status values:

* **proved (Mathlib only)** — no ledger axiom (Zeta23, a proved library, through Part I's spine, is noted where used);
* **proved from axioms [list]** — from the ledger axioms listed (Part I's are prefixed `PosRig.`);
* **ledger axiom** — the statement, or the named part, is an axiom of `PositivityRigidityII/Ledger.lean`;
* **Part I** — a result of Part I restated in Part II; its status is that of Part I's spine;
* **not formalised (reason)**.

Lean names are in namespace `PosRigII` (Part II) or `PosRig` (Part I). The statuses of Part I's results are those of
Part I's spine at tag `v1.3` of its public repository (commit `5bed664909d161fb148a0232e715f55f9a520f1b`), the
dependency pinned in `lakefile.lean` and `lake-manifest.json`. `scripts/audit.sh` checks the statements and axioms
listed here (README, "The audit").

## §1 Introduction

| Statement | Lean | Status |
|---|---|---|
| Theorem S (`thm:main-S`) | `theorem1`, `theorem1_conductor`, `theorem1_object`; `theorem1_finite` | proved from axioms [`voronoi_decoupling`, `exists_integer_critical_object`, `PosRig.explicit_formula`, `PosRig.xi_decay`]; `theorem1_finite` from [`PosRig.floor_bound`]. Weaker than the paper in the class of `H` (one `δ < 1/2`, exponent `8`; entireness not stated) and in (b) (the differentiability of `F̂` is not formalised; it states only that any derivative of `F̂` at `ξ_n`, if it exists, is `0`) — `FAITHFUL.md` |
| Theorem U (`thm:main-U`) | `theorem2`, `theorem2_condU` | proved from axioms [as Theorem S, plus `PosRig.zero_support_rigidity`, `PosRig.logic_b`] |
| Corollary (`cor:main-RH`) | `corollary3`, `corollary3_RH`, `corollary3_notRH`, `corollary_minimiser`; `main_summary` | proved from axioms [as Theorem U, plus `PosRig.duality_no_gap`] |
| Theorem "The object" (`thm:main-object`) | — | not formalised (Kloosterman sums, order derivatives of Bessel functions, `K₀`: not in Mathlib). The properties of the object that the proofs use are the **ledger axiom** `exists_integer_critical_object` |
| Remark 1.1 (`rem:intro-classical`, preview of Corollary 8.2) | `rh_iff_kappaOPS_zero` | its statement is the last sentence of Corollary 8.2: proved from axioms (see §8) |

## §2 The setting, and the results of Part I that are used

| Statement | Lean | Status |
|---|---|---|
| Definition `def:testclass` (Part I, Def. 2.1) | `PosRig.InTδ`, `PosRig.TestClass` | Part I: definition |
| Lemma `lem:I-decay` (Part I, Lemma 2.2(a)) | — | Part I: not formalised (used only for the evenness of `F̂`, which is proved directly: `PosRig.FT_neg_of_even`) |
| Lemma `lem:I-EF` (Part I, Lemma 2.3) | `PosRig.explicit_formula` | Part I: ledger axiom (classical) |
| Definition `def:admissible` (Part I, Def. 2.4) | `PosRig.Admissible`, `K`, `Cone`, `ConeOPS`, `kappaStar`, `kappaOPS`, `CondE`, `CondU`, `CondS` | Part I: definitions |
| Conjecture U (`conj:U`), Conjecture S (`conj:S`) | `PosRig.CondU`, `PosRig.CondS` | stated; proved: Theorems U and S |
| Definition `def:magic` (Part I, Def. 2.11) | `PosRig.IsExactMagic` | Part I: definition |
| Theorem `thm:I-duality` (Part I, Thm 2.7(a)) | `PosRig.condE_iff_kappaStar_nonneg` | Part I: proved from [`PosRig.duality_no_gap`] |
| Theorem `thm:I-logic` (Part I, Thm 2.9) | `PosRig.logic_c`, `PosRig.logic_d`, `PosRig.logic_a`, `PosRig.logic_b` | Part I: (a), (c), (d) proved, (b) ledger axiom |
| Lemma `lem:I-compslack` (Part I, Lemma 2.13) | `PosRig.comp_slackness` | Part I: proved (Mathlib only) |
| Theorem `thm:I-zerosupport` (Part I, Thm 3.6) | `PosRig.zero_support_theorem` | Part I: proved from [`PosRig.zero_support_rigidity`, `PosRig.logic_b`] |
| Corollary `cor:I-magic` (Part I, Cor. 3.9(a)) | `PosRig.magic_principle_zero` | Part I: proved from [`PosRig.zero_support_rigidity`, `PosRig.logic_b`] |
| Lemma `lem:I-XB` (Part I, (4.1)) | `PosRig.xi_decay` | Part I: ledger axiom (classical) |
| Corollary `cor:I-zerokilling` (Part I, Cor. 4.4) | `PosRig.zero_killing_EF` | Part I: proved from [`PosRig.explicit_formula`] |

## §3 Reduction to a Γ-only integer-critical function

| Statement | Lean | Status |
|---|---|---|
| (eq:GH): `G_H`, `Ĝ_H` | `GammaOnly`, `GammaFT`, `gammaInf` | definitions; `γ_∞` checked against `Γ_ℝ` and `Ξ = γ_∞ ζ` (proved, Mathlib + Zeta23) |
| Definition "The class `𝒲_δ`" (`def:W`) | `ClassW` | definition; non-empty (`one_classW`, proved, Mathlib only) |
| Lemma "Voronoi decoupling" (`lem:voronoi`) | (a) `classW_inTδ`; (b), (c) `voronoi_decoupling` | (a) proved from [`PosRig.xi_decay`]; (b) (integrability of `G_H`) and (c) **ledger axiom**; the bounds in (b), (c) and the reality and continuity of `Ĝ_H` not formalised |
| Proposition "Exact magic functions from Γ-only data" (`prop:reduction`) | `reduction`, `reduction_OPS`, `condC5_of`; steps `FT_nonneg_of_voronoi`, `FT_xiOf_eq_zero_of_voronoi`, `FT_zero_of_voronoi`, `Arch_eq_zero_of_FT_vanish`, `intR_pos_of_C2`, `ClassW.exists_real_ne_zero` | proved from axioms [`voronoi_decoupling`, `PosRig.explicit_formula`, `PosRig.xi_decay`]; the transfer steps from the Voronoi identity and the identity theorem are proved (Mathlib only) |
| Remark "The converse direction; not used" (`rem:mobius`) | — | not formalised (not used) |
| Γ-only integer-critical function (definition after `rem:mobius`) | `IntegerCritical` | definition |

## §4 The automorphic input

| Statement | Status |
|---|---|
| Lemma `lem:bessel-basic`; Proposition `prop:niebur`; Lemma "The Weyl-element integral" (`lem:weyl`); Theorem "Fourier expansion" (`thm:niebur-fourier`); Remark `rem:niebur-lit`; Lemma "A Jordan block" (`lem:jordan`); Proposition `prop:Pt`; Lemma "Symmetric-square equivariance" (`lem:sym2`); Proposition `prop:sym2`; Remark `rem:rep` | not formalised (Maass forms, Poincaré series, Bessel functions of complex order and their order derivatives, Kloosterman sums: not in Mathlib). They enter the spine only through property 1 of the ledger axiom `exists_integer_critical_object` (`H ∈ 𝒲_δ`) |

## §5 The Green-flux lift

| Statement | Status |
|---|---|
| Lemma "The Mellin transform of the kernel" (`lem:kernel-mellin`); Lemma `lem:weights`; Lemma "The four-path functional" (`lem:four-path`); Theorem "The lift" (`thm:lift`); Lemma `lem:K0K0`; Lemma "Small `x`" (`lem:small-x`); Lemma `lem:R-entire`; Definition `def:Hraw`; Proposition `prop:Hraw` | not formalised; they enter through properties 1–3 of `exists_integer_critical_object` (`prop:Hraw`: `H_raw ∈ 𝒲_δ` with Γ-only transform `Ĝ_raw`; `thm:lift`(c), (d), (f): the formula, `𝒢(1) = −1/2`, the integer zeros) |
| Remark "Growth along the imaginary axis; not used" (`rem:infinite-type`) | not formalised (not used) |
| Proposition `prop:C3` | (a) the vanishing of `Ĝ_raw` at the `ξ_n`, `n ≥ 2`, is property 2 of the **ledger axiom** `exists_integer_critical_object` (the vanishing of `∂_ξ Ĝ_raw` there is not stated); (a) `Ĝ_raw(0) = 1/(32π²)` and (b) are not formalised (the spine proves `Ĝ_H(0) = ∫ F > 0` instead, `condC5_of`) |

## §6 Positivity on the Fourier side

| Statement | Status |
|---|---|
| Theorem 6.1 "Positivity of the coefficients" (`thm:an-positive`); Theorem 6.2 "Two-sided bounds" (`thm:an-bounds`); Remark 6.3 "The Weil bound is not needed"; the trivial-bound box `TB`, (6.1) (`eq:box`) | not formalised; `a_n > 0` enters through property 3 of `exists_integer_critical_object` (`Ĝ_H ≥ 0` on `[0, ∞)`, `> 0` on `[0, ξ₂)`), and `TB` through property 4 (the certificates of Theorems 6.8 and 7.11 hold uniformly on `TB`) |
| Proposition 6.4 "Computer-assisted" (`prop:C`); Proposition 6.5 "Positive definiteness" (`prop:posdef`); Remark 6.6 "Checks of the normalising constant" (`rem:sign`) | not formalised. Proposition 6.5 is an input of Theorem 6.8 (property 4 of the ledger axiom); its first display, `F̂_raw = Σ d(m) m^{−1/2} Ĝ_raw(· + ξ_m) ≥ 0` on `[0, ∞)`, is what the spine proves in Lean from the Voronoi identity (`FT_nonneg_of_voronoi`, `reduction_OPS`). The sign of the normalisation needs no computation in the spine either: `exists_object` divides by `H_raw(0) > 0`, which property 4 gives |
| Lemma 6.7 "Moment minorant" (`lem:moments`); Theorem 6.8 "Moment certificate; computer-assisted" (`thm:moments`, Certificate M-box); Remark 6.9 "Conditioning, and the elementary range" (`rem:moments`) | not formalised; Theorem 6.8 (`H_raw > 0` for `|t| ≤ 10.355`, uniformly on `TB`) is part of property 4 of the **ledger axiom** `exists_integer_critical_object`, whose docstring quotes the decisive lines of `positivity/logs/cert_moments_box.log` (checked by `scripts/check_provenance.py`) |

## §7 Positivity on the physical side

| Statement | Status |
|---|---|
| Lemma 7.1 "Closed form of the kernel" (`lem:conical`); Theorem 7.2 "Positivity of the kernel" (`thm:kernel-pos`); Theorem 7.3 "The physical-side formula" (`thm:F`) | not formalised; inputs of property 4 of `exists_integer_critical_object` (the sign transfer between `Π` and `H_raw`) |
| Lemmas 7.5 "Stirling bracket" (`lem:stirling`), 7.6 "Kernel bounds" (`lem:kernel-bounds`), 7.7 "Signs of `B`" (`lem:B-sign`), 7.8 (`lem:comparison`); Proposition 7.10 "Computer-assisted; trivial-bound box" (`prop:L-numbers-box`); Theorem 7.11 "Large `|t|` from the trivial bound" (`thm:large-t-box`) | not formalised; Theorem 7.11 (`Π > 0` for `|t| ≥ 9`, uniformly on `TB`) is part of property 4 of the **ledger axiom**, whose docstring quotes the decisive lines of `positivity/logs/cert_large_t_T9_box.log` and `positivity/logs/cert_gtail_box.log` (checked by `scripts/check_provenance.py`) |
| Corollary 7.12 (`cor:Pi-positive`): `Π > 0`, hence `H_raw > 0`, on `ℝ` | property 4 of the **ledger axiom** `exists_integer_critical_object` (from Theorems 6.8, 7.11 and 7.3). The explicit lower bound for `|t| ≥ 9` in its statement (from Theorem 7.11, constant `0.9659`) is not part of the axiom |
| Theorem 7.4 "Large `|t|`" (`thm:large-t`, `T₀ = 8`, certified coefficients); Proposition 7.9 "Computer-assisted" (`prop:L-numbers`); Theorem 7.13 "Window; computer-assisted" (`thm:window`, Certificate W) | not formalised and not used by the proof of Corollary 7.12: independent checks, whose decisive lines are also quoted in the docstring of the ledger axiom (and checked) |
| Remarks 7.14 "Conditioning, not arithmetic" (`rem:negctl`) and 7.15 "Conditioning of `Π(0)` in the coefficients" (`rem:conditioning`) | not formalised (remarks) |

## §8 Proofs of the main results

| Statement | Lean | Status |
|---|---|---|
| Proof of Theorem `thm:main-object` | — | not formalised |
| Proof of Theorem `thm:main-S` (the normalisation `H = C H_raw`, the hypotheses of `prop:reduction`, `κ* ≤ κ*_OPS ≤ 0`, `q_min ≥ 1`, the derivatives) | `exists_object`, `theorem1_object`, `theorem1`, `theorem1_conductor` | proved from axioms (except the differentiability of `F̂`) |
| Proof of Theorem `thm:main-U` | `ZF_Xi_sq_mul`, `theorem2` | proved from axioms |
| Proof of Corollary `cor:main-RH` | `corollary3`, `corollary3_RH`, `corollary3_notRH`, `corollary_minimiser` | proved from axioms |
| Remark "Where each input enters" (`rem:inputs`) | `axioms.log` | confirmed: Theorem S uses Part I only through `PosRig.explicit_formula` and `PosRig.xi_decay` (and the definitions); Theorem U adds `PosRig.zero_support_rigidity`, `PosRig.logic_b`; the Corollary adds `PosRig.duality_no_gap` |
| Corollary 8.2 (`cor:nogap`, subsection "The classical cone"), last sentence: RH ⟺ `𝒜 ≥ 0` on `𝒞_OPS` ⟺ `κ*_OPS = 0` | `rh_iff_kappaOPS_zero` | proved from axioms [those of Corollary 3: `voronoi_decoupling`, `exists_integer_critical_object` (with its window clause), `PosRig.explicit_formula`, `PosRig.xi_decay`, `PosRig.zero_support_rigidity`, `PosRig.logic_b`, `PosRig.duality_no_gap`]; also states `κ*_OPS ≥ 0` and, under ¬RH, `κ* ≤ κ*_OPS < 0` |
| Corollary 8.2 (a) | `FT_window` | `F̂₀ ≥ Ĝ_H > 0` on `[0, ξ₂)` and `F̂₀ > 0` on `(−ξ₂, ξ₂)`: proved from axioms [as Theorem S; `Ĝ_H > 0` on `[0, ξ₂)` is the window clause of `exists_integer_critical_object`]. The zero set `{±ξ_n : n ≥ 2}` of `F̂₀` is not formalised (it needs `Ĝ_H > 0` at every non-integer `x ≥ 1`) |
| Corollary 8.2 (b), `0 ≤ ℓ ≤ ξ₂` | `corollary8_2_b` | `𝒦_ℓ = 𝒦` (`Kset Arch ℓ = K`): proved from axioms [as Theorem S] (complementary slackness at the gap `ℓ`, Part I's `comp_slackness_gen`) |
| Corollary 8.2 (c), (d), `0 ≤ ℓ ≤ ξ₂` | `corollary8_2` | (i) ⟺ (ii) ⟺ (iii) ⟺ (v) ⟺ (vi) and (d): proved from axioms [as Corollary 3]; `κ*_ℓ` is Part I's `slack Arch (ConeG ℓ)`, and `ConeG_zero_eq : 𝒞_0 = 𝒞_OPS`. Clause (iv) (`𝒜 ≥ 0` on `𝒞_ℓ ∩ 𝒢`) is not formalised: it uses Proposition C.2 |
| By-product: `κ* ≥ 0` ⟺ `κ*_OPS ≥ 0` (and `𝒜 ≥ 0` on `𝒞` ⟺ on `𝒞_OPS`), unconditionally | `kappaStar_nonneg_iff_kappaOPS_nonneg`, `arch_nonneg_Cone_iff_ConeOPS` | proved from axioms [as Theorem S]: no Theorem U and no duality theorem |
| Remark 8.3 (`rem:nogap`) | — | not formalised (remarks: inputs, the role of the gap, size, larger gaps, what is not claimed) |

## Appendix C (`app:gap`): duality at an arbitrary gap

| Statement | Lean | Status |
|---|---|---|
| Lemma C.1 "Transfer across the gap" (`lem:transfer`; test function `Θ`) | `transfer` (any `L` additive on `𝒯` and homogeneous), `transfer_Arch` | **proved, with no ledger axiom** (Mathlib and Zeta23: the additivity of `𝒜` on `𝒯`, `Arch_add`, uses Zeta23's bound `|Ω_∞(t)| ≤ K(1+|t|)^{1/2}`); the margin near `ℓ₁` uses the compactness of `{ξ ∈ [0, ℓ₁] : Re F̂₁(ξ) ≤ 0}` |
| Proposition C.2 "Duality at an arbitrary gap" (`prop:gap-duality`) | — | not formalised (Part I's duality proof at the gap `ℓ`; Corollary 8.2 uses it only for clause (c)(iv), which is not formalised either) |
| Remarks C.3 (`rem:gap-uses`), C.4 (`rem:xi0`) | — | not formalised (remarks) |

## §9 and the appendices

| Statement | Status |
|---|---|
| §9 (remarks and open questions) | not formalised (remarks) |
| Appendix A (certificates: A.1 coefficient enclosures, A.2 window, A.3 moment certificate, A.4 large `|t|`, A.5 normalising constant, A.6 constants of Section 6, A.7 the Lean formalisation `app:lean`): Lemmas A.1 (`lem:bracket`), A.2 (`lem:gauss`), A.3 (`lem:D-infinity`) | not formalised (inside the certificates); A.7 describes this project |
| Appendix B (Bessel estimates): Lemmas "Ascending series" (`lem:dot-series`), "Small argument" (`lem:small-w`), "Uniform bounds" (`lem:dotbounds`), "Inequalities for `I₀, I₁, K₂`" (`lem:IK`), "The order derivative `İ`" (`lem:Idot`), "The coefficients at `ν = 1`" (`lem:alpha`) | not formalised (inside §§4–6) |

## Coverage (Corollary 8.2)

Corollary 8.2 is formalised except for the zero set in (a) and clause (c)(iv): its last sentence is
`rh_iff_kappaOPS_zero`, and (a)–(d) are `FT_window`, `corollary8_2_b`, `corollary8_2`. Lemma C.1 is proved with no ledger
axiom; Proposition C.2 is not formalised.

## Coverage

Of the 4 main statements of §1, 3 are formalised and proved from the ledger (Theorems S and U, the Corollary), and 1
(Theorem "The object") is not formalised; the properties of the object that the proofs use are one ledger axiom. Of the
3 numbered statements of §3, 2 are formalised and proved (Definition `def:W`, Proposition `prop:reduction`) and 1 is
formalised as part proved (`lem:voronoi`(a)) and part ledger axiom ((b), (c)). The statements of §§4–7 and of the
appendices (the construction of the object and its positivity) are not formalised; they are the sources of the ledger
axiom `exists_integer_critical_object`.
