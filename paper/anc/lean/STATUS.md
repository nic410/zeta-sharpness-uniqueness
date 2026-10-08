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
| Theorem "Positivity of the coefficients" (`thm:an-positive`); Theorem "Two-sided bounds" (`thm:an-bounds`); Remark "The Weil bound is not needed" | not formalised; `a_n > 0` enters through property 3 of `exists_integer_critical_object` (`Ĝ_H ≥ 0` on `[0, ∞)`) |
| Proposition "Computer-assisted" (`prop:C`); Remark "Sign coherence three times" (`rem:sign`) | not formalised and not used by the spine (the sign of the normalisation is automatic: `exists_object` normalises by `H_raw(0) > 0`, which property 4 gives) |

## §7 Positivity on the physical side

| Statement | Status |
|---|---|
| Lemma "Closed form of the kernel" (`lem:conical`); Theorem "Positivity of the kernel" (`thm:kernel-pos`); Theorem "The physical-side formula" (`thm:F`); Theorem "Large `|t|`" (`thm:large-t`); Lemmas "Stirling bracket" (`lem:stirling`), "Kernel bounds" (`lem:kernel-bounds`), "Signs of `B`" (`lem:B-sign`), `lem:comparison`; Proposition "Computer-assisted" (`prop:L-numbers`); Theorem "Window; computer-assisted" (`thm:window`); Corollary `cor:Pi-positive` | not formalised; `cor:Pi-positive` (`H_raw > 0` on `ℝ`) is property 4 of the **ledger axiom** `exists_integer_critical_object`, whose docstring quotes the decisive lines of the window certificate, of the numbers of `prop:L-numbers` at `T₀ = 8` and of `ρ̄(4) < 1`, checked against the shipped logs by `scripts/check_provenance.py` |
| Remark "The certificate is sharp at small `t`" (`rem:negctl`) | not formalised (a control, not used) |

## §8 Proofs of the main results

| Statement | Lean | Status |
|---|---|---|
| Proof of Theorem `thm:main-object` | — | not formalised |
| Proof of Theorem `thm:main-S` (the normalisation `H = C H_raw`, the hypotheses of `prop:reduction`, `κ* ≤ κ*_OPS ≤ 0`, `q_min ≥ 1`, the derivatives) | `exists_object`, `theorem1_object`, `theorem1`, `theorem1_conductor` | proved from axioms (except the differentiability of `F̂`) |
| Proof of Theorem `thm:main-U` | `ZF_Xi_sq_mul`, `theorem2` | proved from axioms |
| Proof of Corollary `cor:main-RH` | `corollary3`, `corollary3_RH`, `corollary3_notRH`, `corollary_minimiser` | proved from axioms |
| Remark "Where each input enters" (`rem:inputs`) | `axioms.log` | confirmed: Theorem S uses Part I only through `PosRig.explicit_formula` and `PosRig.xi_decay` (and the definitions); Theorem U adds `PosRig.zero_support_rigidity`, `PosRig.logic_b`; the Corollary adds `PosRig.duality_no_gap` |

## §9 and the appendices

| Statement | Status |
|---|---|
| §9 (remarks and open questions) | not formalised (remarks) |
| Appendix A (certificates): Lemmas `lem:bracket`, `lem:gauss`, `lem:D-infinity` | not formalised (inside the certificates) |
| Appendix B (Bessel estimates): Lemmas "Ascending series" (`lem:dot-series`), "Small argument" (`lem:small-w`), "Uniform bounds" (`lem:dotbounds`), "Inequalities for `I₀, I₁, K₂`" (`lem:IK`), "The order derivative `İ`" (`lem:Idot`), "The coefficients at `ν = 1`" (`lem:alpha`) | not formalised (inside §§4–6) |

## Coverage

Of the 4 main statements of §1, 3 are formalised and proved from the ledger (Theorems S and U, the Corollary), and 1
(Theorem "The object") is not formalised; the properties of the object that the proofs use are one ledger axiom. Of the
3 numbered statements of §3, 2 are formalised and proved (Definition `def:W`, Proposition `prop:reduction`) and 1 is
formalised as part proved (`lem:voronoi`(a)) and part ledger axiom ((b), (c)). The statements of §§4–7 and of the
appendices (the construction of the object and its positivity) are not formalised; they are the sources of the ledger
axiom `exists_integer_critical_object`.
