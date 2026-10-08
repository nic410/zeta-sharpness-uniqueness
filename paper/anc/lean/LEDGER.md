# The axiom ledger of the Part II spine

Every input of the Lean spine of Part II that is neither proved in Lean nor an axiom of Part I's spine is an `axiom`
in `PositivityRigidityII/Ledger.lean`, and nowhere else. `scripts/audit.sh` checks this, the count in the table
below, and that every axiom is named here. The docstring of each axiom repeats the information of this file, with the
decisive log lines quoted verbatim; `scripts/check_provenance.py` (audit check (e)) checks every quoted line against
the shipped log and every cited SHA-256 against the shipped file of the ancillary directory.

Statements of Part II are cited by name and LaTeX label (for instance Lemma "Voronoi decoupling", `lem:voronoi`);
numbers will be added when the paper fixes them.

## The two axioms of Part II

| Category | Number | Axioms |
|---|---|---|
| Analytic step proved in the paper, not formalised (a statement about every function of a class; no posited object) | 1 | `voronoi_decoupling` |
| Joint existence of the object: analytic steps proved in the paper, the certificates of Part II, and classical inputs | 1 | `exists_integer_critical_object` |
| **Total** | **2** | |

By the categories of the request, as they appear at the level of the spine:

* (i) **cited classical results**: no axiom of their own. The Niebur–Poincaré series and its Fourier expansion
  (Niebur 1973, Fay 1977; Bringmann–Jorgenson–Smajlović 2025, §2.4) and the DLMF identities (Mehler–Dirichlet
  14.12.1, the Stirling remainder §5.11(ii), the `K₀` bounds §10.40(ii), Stirling 5.11.9) are inputs of the analytic
  steps below and are cited in the docstrings of the two axioms;
* (ii) **paper-internal analytic steps**: `voronoi_decoupling`, and the analytic part of
  `exists_integer_critical_object` (class membership through the Green-flux lift, `H` entire with (C1), (C3),
  `a_n > 0 ⇒ Ĝ ≥ 0`, Theorem F, the kernel positivity, Theorem L);
* (iii) **certificates**: no axiom of their own. Certificate W (`thm:window`) and the numbers of Theorem L at
  `T₀ = 8` (`prop:L-numbers`), with `ρ̄(4) < 1`, are quoted with their decisive log lines in the docstring of
  `exists_integer_critical_object`, the joint axiom whose fourth property (`H > 0` on `ℝ`) they certify.

Why one joint axiom. The object `H` is defined in the paper by a Maass-form construction (Kloosterman sums, order
derivatives of Bessel functions, a four-path Green-flux integral, a Mellin transform), which Mathlib cannot express at
present. So the spine characterises it abstractly, by exactly the four properties that the assembly uses, in one
existence statement. Splitting it into several axioms about a chosen witness (`Classical.choose`) would make each
axiom's truth depend on which witness is chosen; Part I's ledger avoids this for the same reason (its BRS axioms are
joint existence statements). Every theorem of the spine holds for every witness.

### `voronoi_decoupling` [paper]

| | |
|---|---|
| Lean | `axiom voronoi_decoupling {δ : ℝ} {H : ℂ → ℂ} (hH : ClassW δ H) (hδ : δ < 1 / 2) : VoronoiIdentity H` |
| Part II statement | Lemma "Voronoi decoupling" (`lem:voronoi`), parts (b) (integrability of `G_H` on `ℝ`) and (c) (the identity (eq:voronoi) `F̂(ξ) = Σ_{m ≥ 1} d(m) m^{−1/2} Ĝ_H(ξ + ξ_m)`, absolutely convergent), for `0 < δ < 1/2`, `H ∈ 𝒲_δ`, `F = Ξ² H` |
| Proof in the paper | Stirling (DLMF 5.11.9) uniformly in vertical strips; a Cauchy shift of the line of integration to `Im w = −τ`, `τ ∈ (1/2, 1/2 + δ]`, where the Dirichlet series of `ζ²` converges absolutely; Fubini; each line moved back to `ℝ`. Re-proved by an independent referee |
| Faithful / weaker | Faithful (parts (b), (c)); a statement about every `H` of the class, no object posited. Not stated: the bounds of (b) for `G_H` and `Ĝ_H`, the reality and continuity of `Ĝ_H`, and the bound for the `m`-th term in (c). Part (a), `Ξ² H ∈ 𝒯_δ`, is proved in Lean (`classW_inTδ`) |
| Non-vacuity | Its hypothesis can be met: `one_classW` (the constant `1` is in `𝒲_δ` for every `0 < δ < 1`; for `H = 1` the identity is the classical Voronoi summation for `Ξ²`). The steps that the spine takes from its conclusion (`FT_nonneg_of_voronoi`, `FT_xiOf_eq_zero_of_voronoi`, `FT_zero_of_voronoi`) use no axiom |

### `exists_integer_critical_object` [paper + certificate + classical]

| | |
|---|---|
| Lean | `axiom exists_integer_critical_object : ∃ H : ℂ → ℂ, (∃ δ : ℝ, δ < 1 / 2 ∧ ClassW δ H) ∧ CondC3 H ∧ CondC4Zero H ∧ CondC2Strict H` |
| Part II statement | Theorem "The object" (`thm:main-object`) with Corollary `cor:Pi-positive`, as used in the proof of Theorem `thm:main-S` (`sec:assembly`): the function `H_raw` satisfies (1) `H_raw ∈ 𝒲_δ`, (2) (C3), (3) `Ĝ ≥ 0` on `[0, ∞)`, (4) `H_raw > 0` on `ℝ` |
| Faithful / weaker | Weaker than the paper: one `δ < 1/2` (the paper: every `δ < 1`, exponent `−9 + δ`); `H` entire, the formula for `Ĝ_H`, the double zeros of `Ĝ_H` and the normalisation `H(0) = 1` are not stated (the normalisation is derived in Lean, `exists_object`) |

What its four properties rest on (Part II statements by label; the certificates with their shipped logs, paths
relative to the ancillary directory):

| Property | Part II statements | Kind | Certificate log, decisive line |
|---|---|---|---|
| 1. `H ∈ 𝒲_δ` | Proposition `prop:Hraw` (a), (b), (c); behind it Theorem "Fourier expansion" (`thm:niebur-fourier`) with Lemma `lem:weyl` and Proposition `prop:niebur`; Lemma "A Jordan block" (`lem:jordan`), Proposition `prop:Pt`, Lemma `lem:sym2`, Proposition `prop:sym2`; Lemmas `lem:kernel-mellin`, `lem:four-path`, `lem:K0K0`; Theorem "The lift" (`thm:lift`); Lemmas "Small `x`" (`lem:small-x`) and `lem:R-entire` | paper; classical (Niebur 1973, Fay 1977, Bringmann–Jorgenson–Smajlović 2025; DLMF, Gradshteyn–Ryzhik) | — |
| 2. (C3) `Ĝ_H(ξ_k) = 0`, `k ≥ 2` | Proposition `prop:C3`(a), from Theorem `thm:lift`(f) (`sin²(πk) = 0`) | paper | — |
| 3. `Ĝ_H ≥ 0` on `[0, ∞)` | Theorem "Positivity of the coefficients" (`thm:an-positive`: every `a_n > 0`, trivial Kloosterman bound, no finite check) with `thm:an-bounds`; `K₀ > 0`; Theorem `thm:lift`(c); `Ĝ_raw(1) = 1/(32π²)` (Proposition `prop:C3`(a)) | paper (the constants at `z = 4π` are elementary; also evaluated in ball arithmetic as a check) | — |
| 4. `H > 0` on `ℝ` | Corollary `cor:Pi-positive`: Theorem "The physical-side formula" (`thm:F`), Theorem "Positivity of the kernel" (`thm:kernel-pos`, DLMF 14.12.1), Theorem "Window; computer-assisted" (`thm:window`, `Π > 0` on `[0, 40]`), Theorem "Large `|t|`" (`thm:large-t`, `Π > 0` for `|t| ≥ 8`; Lemmas `lem:stirling`, `lem:kernel-bounds`, `lem:B-sign`, `lem:comparison`; Proposition `prop:L-numbers`) | paper + certificates; classical (DLMF 14.12.1, §5.11(ii), §10.40(ii)) | `positivity/logs/window_0_40.log`: `DECISIVE: R(t) > 0 on [0, 40] (all 80 cells certified): True`; `positivity/logs/cert_large_t_T8.log`: `margin = [0.255407883141 +/- 3.57e-13]`, `DECISIVE (all-Arb): Theorem L hypotheses verified for T0 = 8: True`; `positivity/logs/cert_gtail.log`: `rhobar(4) = [4.198895694e-9 +/- 1.65e-19]  (< 1 needed): True`, `DECISIVE: g > 0 on [4, oo): True` |

The certificate scripts are `positivity/run_window.py` with `positivity/cert_window.py` and `positivity/poslib.py`,
`positivity/cert_large_t.py` and `positivity/cert_gtail.py`; their inputs are the coefficient balls
`coefficients/data/an_small_X1e4.json`, `an_cert_X1e4.json`, `extra_smalln_X3e5.json` (SHA-256 in the docstring and in
the ancillary README) and Part I's `lib/besselk.py`. The logs write `R` for the paper's `Π`, `Phi` for `A` and `g` for
`B`. The docstring also quotes the six numbers of Theorem L at `T₀ = 8` (`t_mono`, the two minima of `B`, `p(8)`, `n(8)`,
`A_Φ`) and the enclosure of `Π(0)` (`positivity/logs/check_r0.log`), which is not needed for the sign of `H`.

## The axioms of Part I that the spine uses

The spine imports Part I's spine (`PositivityRigidity`, 22 ledger axioms, see its `LEDGER.md`) and uses 6 of its
axioms. `axioms.log` lists, for every theorem, exactly which.

| Part I axiom | Part I statement | Category in Part I | Used by |
|---|---|---|---|
| `explicit_formula` | Lemma 2.3 (explicit formula on `𝒯`) | classical | Corollary 4.4 (`zero_killing_EF`), hence `𝒜(F) = 0`: Proposition `prop:reduction`, Theorems S and U, the Corollary |
| `xi_decay` | bound (4.1) for `Ξ` | classical | Lemma `lem:voronoi`(a) (`classW_inTδ`): `Ξ² H ∈ 𝒯`; everything downstream |
| `zero_support_rigidity` | Theorem 3.6 (zero-side support), first conclusion | paper | Corollary 3.9(a) (`magic_principle_zero`): Theorem U, the Corollary |
| `logic_b` | Theorem 2.9(b) | paper | Theorem 3.6 (RH and `μ = μ_ζ`), Theorem 2.9(c): Theorem U, the Corollary |
| `duality_no_gap` | Theorem 2.7(a), (ii) ⇒ (i) | paper | `(E) ⇔ κ* ≥ 0` (Theorem 2.7(a)): the Corollary |
| `floor_bound` | the floor in the proof of Proposition 2.8 | paper | only `theorem1_finite` (`κ*` and `κ*_OPS` are finite) |

So Theorem S (`theorem1`, `theorem1_conductor`, `theorem1_object`) rests on `explicit_formula` and `xi_decay` from
Part I; Theorem U adds `zero_support_rigidity` and `logic_b`; the Corollary adds `duality_no_gap`. This is the list of
Part II's remark "Where each input enters" (`rem:inputs`).

## Hygiene

* *No posited object.* `voronoi_decoupling` is a statement about every function of the class `𝒲_δ`.
  `exists_integer_critical_object` asserts the existence of a function with four properties, and every theorem that
  uses it holds for every such function; no axiom refers to a chosen witness.
* *No junk values.* `γ_∞` is defined without a removable singularity (`gammaInf_zero : γ_∞(0) = −1`). The Γ-only
  transform is a Fourier integral, which Mathlib sets to `0` for non-integrable functions; `voronoi_decoupling`
  asserts the integrability of `G_H` on `ℝ`, so `Ĝ_H` is a genuine integral for every `H` to which it applies. The
  slacks are Part I's `EReal` infima, finite by `theorem1_finite`. The derivative statement of Theorem S(b) is stated
  for every `D` with `HasDerivAt`, not with Mathlib's `deriv` (which is `0` where there is no derivative).
* *Faithfulness of the definitions* (no ledger axiom; `Faithful.lean`, `scripts/NonVacuity.lean`): `γ_∞` is the
  paper's and `Ξ = γ_∞ ζ` on `ℝ`; `𝒲_δ` contains the constant `1`; the Voronoi series starts at `m = 1` with the term
  `Ĝ_H(ξ)`, and `ξ_n + ξ_m = ξ_{nm}`; the transfer steps from the Voronoi identity use no axiom.
* *Consistency.* Both axioms are theorems of the paper (the second together with its certificates), or weaker; so
  they hold together with Part I's axioms in the intended model.
* `#print axioms` for every formalised statement is in `axioms.log`: only the two axioms above, Part I's ledger axioms
  and `propext`, `Classical.choice`, `Quot.sound` occur. No `sorry`, no `native_decide` anywhere.
