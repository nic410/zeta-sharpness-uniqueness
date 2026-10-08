# PositivityRigidityII: the logical spine of Part II in Lean 4

A Lean 4 / Mathlib formalisation of the logical spine of

> *Sharpness and uniqueness for positive solutions of the explicit formula for ζ(s)* (Part II),

which proves Conjectures S and U of Part I (*Positive solutions of the explicit formula for ζ(s): near-criticality
and uniqueness*). It builds on the Lean spine of Part I (library `PositivityRigidity`, namespace `PosRig`; fetched by
Lake from Part I's public repository at tag `v1.3`, see "Building"), whose
definitions — the test class `𝒯`, the cones `𝒞` and `𝒞_OPS`, the functional `𝒜`, the slacks `κ*` and `κ*_OPS`, the
admissible pairs `𝒦`, `p_ζ`, (E), (S), (U), `q_min` — are reused, not redefined.

The spine states the main results of Part II faithfully in Lean and proves them from Mathlib, Part I's spine and an
explicit **axiom ledger of two axioms**. Statements of Part II are cited by name and LaTeX label (for instance
Proposition "Exact magic functions from Γ-only data", `prop:reduction`); numbers will be added when the paper fixes
them. `FAITHFUL.md` maps every Lean name to the paper statement, `STATUS.md` lists every statement of Part II with
its status, and `LEDGER.md` describes the axioms.

## Main results

| Part II | Lean (namespace `PosRigII`) | Statement in Lean |
|---|---|---|
| Theorem S (`thm:main-S`) | `theorem1` | `kappaStar ≤ kappaOPS ∧ kappaOPS ≤ 0` — unconditional |
| | `theorem1_conductor` | `CondS ∧ 1 ≤ qmin ∧ 1 ≤ qminOPS` |
| | `theorem1_object` | there is `H ∈ 𝒲_δ` (some `δ < 1/2`), `H(0) = 1`, `H > 0` on `ℝ`, Γ-only integer-critical, with `F = Ξ² H ∈ 𝒞_OPS`; `F̂(ξ_n) = 0` and `F̂′(ξ_n) = 0` (`n ≥ 2`; formalised as: any derivative of `F̂` at `ξ_n`, if it exists, is `0`); `∫ F = F̂(0) > 0`; `𝒜(F) = 0`; `F` an exact magic function; real zeros of `F` = `Z_ζ` |
| Theorem U (`thm:main-U`) | `theorem2`, `theorem2_condU` | `∀ p ∈ K, p = pZeta`; `CondU` |
| Corollary (`cor:main-RH`) | `corollary3` | `(RH ↔ CondE) ∧ (CondE ↔ 0 ≤ kappaStar) ∧ (0 ≤ kappaStar ↔ kappaStar = 0)` |
| | `corollary3_RH` | `RH → K = {pZeta} ∧ kappaStar = 0 ∧ kappaOPS = 0 ∧ qmin = 1 ∧ qminOPS = 1` |
| | `corollary3_notRH` | `¬RH → kappaStar < 0 ∧ K = ∅` |
| | `corollary_minimiser` | `F/∫F` is a minimiser for `κ*` iff RH; under RH also for `κ*_OPS`; unconditionally `κ* ≤ κ*_OPS ≤ 𝒜(F)/∫F = 0` |
| Proposition `prop:reduction` | `reduction`, `reduction_OPS` | `H ∈ 𝒲_δ`, `H ≢ 0`, (C2)–(C4) ⇒ `F ∈ 𝒞`, `F̂(ξ_n) = 0`, `∫F = F̂(0) = Ĝ_H(0) > 0`, `𝒜(F) = 0`, exact magic, `κ* ≤ 0`; with `Ĝ_H ≥ 0` on `[0, ∞)`: `F ∈ 𝒞_OPS`, `κ*_OPS ≤ 0` |
| Corollary 8.2 (`cor:nogap`, "The classical cone"), last sentence | `rh_iff_kappaOPS_zero` | `(RH ↔ ∀ F ∈ ConeOPS, 0 ≤ Arch F) ∧ (RH ↔ 0 ≤ kappaOPS) ∧ (RH ↔ kappaOPS = 0) ∧ (¬RH → kappaStar ≤ kappaOPS ∧ kappaOPS < 0)` |
| Corollary 8.2 (c), (d), every gap `0 ≤ ℓ ≤ ξ₂` | `corollary8_2` | RH ⟺ `𝒦_ℓ ≠ ∅` ⟺ `𝒜 ≥ 0` on `𝒞_ℓ` ⟺ `κ*_ℓ ≥ 0` ⟺ `κ*_ℓ = 0`; under RH `𝒦_ℓ = {p_ζ}`; under ¬RH `𝒦_ℓ = ∅` and `κ* ≤ κ*_ℓ ≤ κ*_OPS < 0` (clause (iv), on `𝒞_ℓ ∩ 𝒢`, not formalised) |
| Corollary 8.2 (b) | `corollary8_2_b` | `Kset Arch ℓ = K` for `0 ≤ ℓ ≤ ξ₂` (`𝒦_ℓ = 𝒦`, no hypothesis on the zeros) |
| Corollary 8.2 (a) | `FT_window` | `F̂ ≥ Ĝ_H > 0` on `[0, ξ₂)`, so `F̂ > 0` on `(−ξ₂, ξ₂)` (the zero set of `F̂` not formalised) |
| (by-product, unconditional) | `kappaStar_nonneg_iff_kappaOPS_nonneg` | `0 ≤ kappaStar ↔ 0 ≤ kappaOPS`, without Theorem U or the duality theorem |
| Lemma C.1 "Transfer across the gap" (`lem:transfer`) | `transfer` | for every `L` additive on `𝒯` and homogeneous: `Θ ∈ 𝒞_OPS`, `Re Θ̂ > 0` on `[0, ℓ₁)`, `L(Θ) ≤ 0`, `L ≥ 0` on `𝒞_OPS` ⇒ `L ≥ 0` on `𝒞_{ℓ₁}` — proved with no ledger axiom |

Theorem S says `κ* ≤ κ*_OPS ≤ 0`; it does not say that `κ*` is attained (it is attained, by `F/∫F`, exactly under RH:
`corollary_minimiser`). Corollary 3 gives `RH ⇒ κ*_OPS = 0`; the converse is Corollary 8.2 (`rh_iff_kappaOPS_zero`), which
also covers every gap `ℓ ∈ [0, ξ₂]`.

## Status

* `lake build` succeeds with **no `sorry`**, no `native_decide`, and no `axiom` outside
  `PositivityRigidityII/Ledger.lean`.
* **2 ledger axioms** (`LEDGER.md`):
  * `voronoi_decoupling` [paper] — Lemma "Voronoi decoupling" (`lem:voronoi`), parts (b) and (c), for every
    `H ∈ 𝒲_δ`, `δ < 1/2`: `G_H = γ_∞² H ∈ L¹(ℝ)` and `F̂(ξ) = Σ_{m ≥ 1} d(m) m^{−1/2} Ĝ_H(ξ + ξ_m)`;
  * `exists_integer_critical_object` [paper + certificate + classical] — Theorem "The object" (`thm:main-object`)
    with Corollary `cor:Pi-positive`: there is `H ∈ 𝒲_δ` (some `δ < 1/2`) with (C3) `Ĝ_H(ξ_k) = 0` for every integer
    `k ≥ 2`, `Ĝ_H ≥ 0` on `[0, ∞)` and `Ĝ_H > 0` on the window `[0, ξ₂)`, and `H > 0` on `ℝ`. Its docstring cites, property by property, the statements of
    Part II behind it and quotes the decisive lines of the certificates of Corollary 7.12 (Certificate M-box,
    Theorem 6.8: `H_raw > 0` for `|t| ≤ 10.355`; the large-`|t|` numbers at `T₀ = 9` on the trivial-bound box,
    Proposition 7.10 and Theorem 7.11; `ρ̄(4) < 1`), and, as independent checks, those of Certificate W (Theorem 7.13)
    and of `T₀ = 8` with the certified coefficients (Theorem 7.4), from the logs shipped in the ancillary directory.
* **6 axioms of Part I's ledger are used**: `explicit_formula`, `xi_decay` (Theorem S); `zero_support_rigidity`,
  `logic_b` (Theorem U); `duality_no_gap` (Corollary 3); `floor_bound` (only for `theorem1_finite`, the finiteness of
  `κ*` and `κ*_OPS`).
* **Corollary 8.2** (`cor:nogap`, RH ⟺ `κ*_OPS = 0`) is formalised (`NoGap.lean`), except for the zero set in its part (a)
  and its clause (c)(iv). It uses exactly the axioms of Corollary 3; the transfer lemma (Lemma C.1) is proved with no
  ledger axiom. For it, the object axiom gained one conjunct, `Ĝ_H > 0` on `[0, ξ₂)` (the strict positivity proved in
  Corollary 8.2(a)); the number of axioms is unchanged.
* `#print axioms` of every formalised statement lists only these axioms and `propext`, `Classical.choice`,
  `Quot.sound` (`axioms.log`).
* `scripts/audit.sh` passes (`AUDIT PASSED`): see "The audit" below.

## The axiom ledger, in short

| Category | Number | Axioms |
|---|---|---|
| Analytic step proved in the paper, not formalised (about every function of a class; no posited object) | 1 | `voronoi_decoupling` |
| Joint existence of the object (analytic steps proved in the paper, certificates, classical inputs) | 1 | `exists_integer_critical_object` |
| **Total (Part II)** | **2** | |
| Used from Part I's ledger (2 classical, 4 analytic steps of Part I) | 6 | `explicit_formula`, `xi_decay`, `zero_support_rigidity`, `logic_b`, `duality_no_gap`, `floor_bound` |

Classical results (the Niebur–Poincaré expansion, DLMF identities) and the certificates of Part II have no axiom of
their own: they are inputs of the object, which is characterised abstractly by exactly the four properties the proofs
use, in one existence statement (`LEDGER.md` explains why). The Lean kernel checks that the main statements follow
from these axioms; it does not check the axioms themselves.

## Building

Toolchain and pins are those of Part I's spine:

* `lean-toolchain`: `leanprover/lean4:v4.33.0-rc2`;
* Mathlib `51e6992efd06126df61a496bebf8f49482a4e129`; Zeta23 `fbdc36bbf17d20af3fd0447c6d1a8a02773c9844` (both through
  Part I's spine);
* Part I's spine itself: the public repository `github.com/nic410/zeta-positive-solutions`, tag `v1.3` (commit
  `5bed664909d161fb148a0232e715f55f9a520f1b`), Lean project in `paper/anc/lean`. It is one line of `lakefile.lean`,

  ```lean
  require PositivityRigidity from git "https://github.com/nic410/zeta-positive-solutions" @ "5bed664909d161fb148a0232e715f55f9a520f1b" / "paper/anc/lean"
  ```

  and `lake-manifest.json` pins the same commit, and every other package at the revision of Part I's manifest;
* `lakefile.lean` sets `autoImplicit = false`, `relaxedAutoImplicit = false`.

Lake fetches everything; no checkout of Part I is needed:

```sh
export PATH="$HOME/.elan/bin:$PATH"     # elan; it installs the toolchain of lean-toolchain
lake exe cache get                      # Lake clones the pinned packages, then Mathlib's build cache is downloaded
lake build                              # builds the imported Zeta23 modules, Part I's spine and PositivityRigidityII
scripts/audit.sh                        # the full audit (below)
```

A cold `lake build` compiles the imported Zeta23 modules from source, which takes hours on four cores; Part I's spine
(about 7,800 lines) then takes a few minutes, and this project under a minute. If a built checkout of a project with
the same pins is at hand (Part I's spine, for instance), its packages can be reused by a hardlink copy before the first
build (`cp -al <built project>/.lake/packages .lake/packages`, no extra disk space); Lake then fetches and builds only
Part I's spine.

Do **not** run `lake update` without an argument: it would move the pins. To move the pin of Part I's spine, change the
commit in `lakefile.lean` and run `lake update PositivityRigidity`, which rewrites only that entry of
`lake-manifest.json`. To work against a local, modified checkout of Part I's spine, replace the `require` line by a
path dependency, `require PositivityRigidity from "<path to its paper/anc/lean>"`, and the manifest entry by a
`"type": "path"` entry with the same `"dir"`. `.lake/` is git-ignored.

**Continuous integration.** `.github/workflows/lean.yml`, at the root of the repository, is the workflow of Part I's
spine with working directory `paper/anc/lean`. On every push and pull request to `main` (and on demand) it frees disk
space, adds 8 GB of swap, starts a resource monitor, installs elan, restores the `.lake` cache (keyed on
`lake-manifest.json` and `lean-toolchain`), downloads Mathlib's build cache (`lake exe cache get`), runs `lake build`,
saves the cache, runs `scripts/audit.sh`, and uploads the build, audit and monitor logs. The first, cold run compiles the
imported Zeta23 modules from source and takes hours on the 4-core runner; later runs reuse the cache.

## Module map (`PositivityRigidityII/`)

| File | Content |
|---|---|
| `Defs.lean` | `γ_∞` (`gammaInf`), `G_H` (`GammaOnly`), the Γ-only transform `Ĝ_H` (`GammaFT`); the class `𝒲_δ` (`ClassW`); (C2)–(C5) (`CondC2`, `CondC2Strict`, `CondC3`, `CondC4`, `CondC4Zero`, `CondC5`); `IntegerCritical`; the Voronoi terms (`voronoiTerm`) and identity (`VoronoiIdentity`) |
| `Ledger.lean` | **The 2 axioms** (and nothing else) |
| `Faithful.lean` | `γ_∞ = ½ s(s−1) Γ_ℝ`, `γ_∞(0) = −1`, `Ξ = γ_∞ ζ` on `ℝ`; `1 ∈ 𝒲_δ`; scaling; the identity theorem for `𝒲_δ`; the indexing of the Voronoi series; derivatives at zeros of a non-negative function (all without ledger axioms) |
| `Reduction.lean` | Lemma `lem:voronoi`(a) (`classW_inTδ`); the positivity and vanishing transfer through the Voronoi series; Part I's Corollary 4.4 gives `𝒜(F) = 0`; `∫ F > 0`; **Proposition `prop:reduction`** (`reduction`, `reduction_OPS`, `condC5_of`) |
| `Object.lean` | The normalised object (`exists_object`) and **Theorem S, first part** (`theorem1_object`) |
| `Main.lean` | **Theorem S** (`theorem1`, `theorem1_conductor`, `theorem1_finite`), **Theorem U** (`theorem2`, `theorem2_condU`), **Corollary 3** (`corollary3`, `corollary3_RH`, `corollary3_notRH`, `corollary_minimiser`), `main_summary` |
| `NoGap.lean` | **Corollary 8.2** (`rh_iff_kappaOPS_zero`, `corollary8_2`, `corollary8_2_b`, `FT_window`), **Lemma C.1** (`transfer`, `transfer_Arch`); `𝒜` additive on `𝒯` (`Arch_add`, via Zeta23's bound for `Ω_∞`), `𝒯` closed under addition, `𝒞_0 = 𝒞_OPS`, `κ* ≥ 0 ⟺ κ*_OPS ≥ 0` |

## The audit

`scripts/audit.sh` prints one final line, `AUDIT PASSED` or `AUDIT FAILED` (exit code 0 or 1). It fails on:

| Check | What it verifies |
|---|---|
| (0) | `lake build --no-build PositivityRigidityII` succeeds: the audited `.olean` files are those of the current sources |
| (a) | no `sorry`, `admit` or `native_decide` token in any Lean file of the project (comments and strings stripped) |
| (b) | no `axiom` declaration outside `PositivityRigidityII/Ledger.lean` (textually, and in the environment: `scripts/Audit.lean`); the number of ledger axioms equals the total in `LEDGER.md`, which names each of them and each Part I axiom used; no declaration depends on an axiom other than `propext`, `Classical.choice`, `Quot.sound` and the ledger axioms of Parts I and II (so no `sorryAx`, no `Lean.ofReduceBool`); the 19 headline theorems exist |
| (c) | the output of `scripts/print_axioms.lean` (`#print axioms` for every formalised statement) equals `axioms.log` (its `# ` header lines excepted) exactly |
| (d) | statement pin: the output of `scripts/Statements.lean` — the types of the 19 headline theorems, of the 2 ledger axioms and of the 6 Part I axioms they use, and the types and bodies of every definition of Part I or Part II they unfold to, with structural hashes — equals `scripts/Statements.baseline.txt` exactly (so a change of Part I's spine that changes the meaning of a statement of Part II fails the audit) |
| (e) | provenance (`scripts/check_provenance.py`): every SHA-256 cited in `Ledger.lean` matches the cited file of the ancillary directory (`..`), and every log line quoted there occurs in the cited shipped log; SKIPPED (not a failure) if the ancillary directory is absent |
| (f) | non-vacuity: `scripts/NonVacuity.lean` compiles, and each of its 13 theorems uses only `propext`, `Classical.choice`, `Quot.sound` (`FAITHFUL.md`, "Non-vacuity") |
| (g) | hygiene (`scripts/check_hygiene.py`): no absolute path in the files of the project; and, when the maintainers' list of names that must not be published is present (`HYGIENE_PATTERNS`, by default a file in a directory next to `paper/` that is not published), none of those names either. In the public repository the list is absent and that part is reported as skipped |

`CORES` (default `0-3`) is the CPU list for `taskset` (`CORES=` disables pinning), `LEAN_NUM_THREADS` defaults to 4,
and `AUDIT_NO_GIT=1` computes the printed provenance digest without git. After a deliberate change, regenerate the
baselines: `lake env lean scripts/print_axioms.lean` (with the header of `axioms.log`) and
`lake env lean scripts/Statements.lean > scripts/Statements.baseline.txt`, and update `LEDGER.md` if an axiom is added
or removed.
