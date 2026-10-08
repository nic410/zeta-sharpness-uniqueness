# Sharpness and uniqueness for positive solutions of the explicit formula for ζ(s)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23238100.svg)](https://doi.org/10.5281/zenodo.23238100) [![Lean](https://github.com/nic410/zeta-sharpness-uniqueness/actions/workflows/lean.yml/badge.svg)](https://github.com/nic410/zeta-sharpness-uniqueness/actions/workflows/lean.yml)

**Status: preprint, version 1.3 (October 2026); not peer-reviewed.** This paper was produced by AI agents,
mainly Anthropic's Claude with supplementary assistance from OpenAI's Astra, under the author's direction; it has not yet
been checked by a human expert. Author: Nic Johns. Licences: the paper and documentation are CC BY 4.0; the code, data
and Lean formalisation are Apache-2.0 (see [Licence](#licence)).

**Read the paper (PDF): [`paper/build/main.pdf`](paper/build/main.pdf).** This is Part II of a series; Part I is
[doi:10.5281/zenodo.23197915](https://doi.org/10.5281/zenodo.23197915). Specialists who would like to check one part of
the proof in a few hours: see the [reviewing guide](REVIEWING.md).

## What the result says

Riemann's explicit formula, in Weil's form, balances a sum over the zeros of ζ against a sum over the prime powers; the
remaining term depends only on the archimedean (Gamma-function) data of ζ. A *positive solution* puts non-negative
weights on the zero side and on the prime side (beyond log 2/2π) so that the formula holds; ζ's own zeros and prime
powers give one exactly when the Riemann hypothesis holds. The paper proves:

- **Sharpness.** The classical explicit-formula method of Odlyzko, Poitou and Serre is sharp for ζ: there is no positive
  slack (κ* ≤ 0), witnessed by an explicit function. Numerical optimisation had reached the conductor bound 0.997; the
  explicit function reaches the conductor 1 of ζ exactly.
- **Uniqueness.** If the formula has any solution in non-negative weights, it is ζ's own: its zeros on one side and the
  prime powers, with their usual weights, on the other.
- **The classical cone.** The classical method, with test functions F ≥ 0 whose Fourier transform is ≥ 0 everywhere,
  proves no conductor bound above 1 if and only if the Riemann hypothesis holds: RH is equivalent to 𝒜(F) ≥ 0 for every
  such F, a condition with no gap on the prime side and no arithmetic input. For every gap up to log 2/2π the positive
  solutions are the same as above.
- These resolve Conjectures S and U of Part I.

**Why it matters.** It shows that a classical optimisation method of analytic number theory is exactly sharp for ζ, with
an explicit extremal function of the kind Viazovska found for sphere packing, and that positivity together with the
Gamma factor leaves room for no positive solution other than ζ's own zeros and primes; along the way it constructs an
explicit eigenfunction of the hyperbolic Laplacian built from Kloosterman sums.

**What it does not say.** The Riemann hypothesis is **not** proved. By these results it is equivalent to the existence
of a positive solution, and to κ*_OPS = 0; we do not claim that either reformulation makes it easier. There is no circularity in using ζ to build the
function: it has the form F = Ξ²H, and Ξ vanishes at every non-trivial zero of ζ, on or off the critical line, so no
information about where the zeros lie is used and the Riemann hypothesis is assumed nowhere.

## The function

The proof constructs an explicit "magic function" F = Ξ²H: a test function that shows the bound is attained, as in the
sphere-packing bounds of Cohn–Elkies and Viazovska. F and its Fourier transform are non-negative, the transform vanishes
at log n/2π for every integer n ≥ 2, and the archimedean side of the formula vanishes on F. The function H comes from an
eigenfunction of the hyperbolic Laplacian with eigenvalue ¼, a spectral derivative of an odd Niebur–Poincaré series made
into an exact eigenfunction by a first-order operator at a double root. A contour argument that follows the architecture
of Viazovska's sphere-packing construction, with Green's identity in place of Cauchy's theorem and this non-holomorphic
function as its new input, then produces F. Figure 1 of the paper plots H and its Γ-only transform, and Table 1 lists
the first coefficients.

## How the claims are supported

| Evidence | Covers | Where |
|---|---|---|
| **Written proofs** | everything except the items marked computer-assisted | `paper/` |
| **Certified computation** (FLINT/Arb ball arithmetic) | positivity of H for \|t\| ≤ 10.355 (moments of the transform of Ξ²H) and the numerical inputs of the large-\|t\| bound at t = 9, both using only the term c = 1 and the trivial bound for Kloosterman sums; certified enclosures of the first coefficients and the value of the normalising constant (its sign is proved without computation); independent checks (the window [0, 40], the large-\|t\| bound at t = 8) | `paper/anc/` (README, SHA256SUMS, logs) |
| **Lean 4 spine** | the logical assembly: Theorems 1–2 and Corollaries 3 and 8.2 (the latter except the zero set in its part (a) and its clause (c)(iv)) derived in Lean from Part I's spine (6 of its axioms) plus 2 named Part II axioms (an analytic lemma, and the existence of the object with its properties). The existence of the object itself is **not** formalised. | `paper/anc/lean/` (README, LEDGER, FAITHFUL, STATUS) |
| **AI referees** | separate (AI) referees, also Claude agents, checked each component and re-ran the certificates; an external review by another AI system is pending | — |

No human mathematician has yet checked the proofs line by line.

## Structure

- `REVIEWING.md`: a guide for reviewers who want to check one slice of the proof.
- `paper/`: LaTeX sources (`main.tex`, `sections/`, `refs.bib`), the PDF (`build/main.pdf`) and the ancillary files
  (`anc/`):
  - `anc/positivity/`: the moment certificate and the large-|t| constants on the trivial-bound box (used in the
    proofs); the window certificate, the large-|t| constants with the certified coefficients, the tail check, R(0), the
    elementary range and a negative control (checks);
  - `anc/coefficients/`: coefficient enclosures and the normalising constant;
  - `anc/figures/`: the data and script of Figure 1 (an illustration, not a certificate);
  - `anc/lib/`, `anc/tools/`, `anc/runlog.sh`: shared code (Part I's K₀/K₁ library, unchanged);
  - `anc/lean/`: the Lean 4 spine (it depends on Part I's spine).
- `.github/workflows/lean.yml`: Lean CI. It builds the spine against Part I's public repository (version 1.3) and runs
  the audit script.

## Reproducing

- **Certificates:** Python ≥ 3.10 with python-flint 0.9.0 (plus numpy for `coefficients/`). Every certificate has its
  command, inputs (SHA-256) and expected decisive output lines in `paper/anc/README.md`. Run `sha256sum -c SHA256SUMS`
  in `paper/anc/`.
- **Figure 1:** numpy, scipy and matplotlib; see `paper/anc/README.md`.
- **Lean:** run `lake build` and `scripts/audit.sh` in `paper/anc/lean/` (toolchain and pins as in Part I).
- **PDF:** run pdflatex, then bibtex, then pdflatex until stable, from `paper/`.

## Version notes

- **v1.3** (October 2026; doi:10.5281/zenodo.23246727): a new result, Corollary 8.2 with Appendix C. The equivalences of Corollary 3 hold
  for every prime-side gap in [0, log 2/2π], in particular for the classical cone: RH holds if and only if 𝒜(F) ≥ 0 for
  every F with F ≥ 0 and F̂ ≥ 0, if and only if κ*_OPS = 0. The proof uses the transform of the function of Theorem 1,
  which is positive on (−log 2/2π, log 2/2π), a transfer lemma, and a proof of the duality theorem at every gap. The
  positivity proof is reorganised: Ξ²H is positive definite, which gives the sign of the normalising constant without
  computation, and the positivity of H now rests on a moment certificate for |t| ≤ 10.355 and the large-|t| bound from
  t = 9, which use only the term c = 1 and the trivial bound for Kloosterman sums. The window certificate and the
  large-|t| bound at t = 8 are kept as independent checks. The statements of Theorems 1–4 and Corollary 3 are unchanged.
- **v1.2** (October 2026; doi:10.5281/zenodo.23240818): credits only. Bondarenko–Radchenko–Seip are credited as the precedent for removing
  all zeros of ζ (test functions that vanish, with multiplicity, at every non-trivial zero); the inputs from Part I now
  carry precise locators. The mathematics is unchanged.
- **v1.1** (October 2026; doi:10.5281/zenodo.23239278): attributions and citations only. The architecture of Sections 4–5 is credited to
  Viazovska's construction; Remark 4.11 cites the Laplacian lemma of Alfes, Burban and Raum; the history of how the input
  was found is told in full; Odlyzko's Open Problem 2.2 is cited; and related work on exact bootstrap functionals,
  zero-killing devices and compactly supported test functions is added. The mathematics, the theorem statements, the
  labels and the certificates are unchanged.
- **v1.0** (October 2026): first public version (doi:10.5281/zenodo.23238101).

## Citing

```bibtex
@misc{JohnsPartII,
  author       = {Johns, Nic},
  title        = {Sharpness and uniqueness for positive solutions of the explicit formula for $\zeta(s)$},
  howpublished = {Preprint (Part II), \url{https://github.com/nic410/zeta-sharpness-uniqueness}},
  year         = {2026},
  doi          = {10.5281/zenodo.23238100}
}
```

The DOI above is the concept DOI, which always resolves to the latest archived version; each release also has its own
version DOI on [Zenodo](https://doi.org/10.5281/zenodo.23238100) (v1.0: 10.5281/zenodo.23238101; v1.1: 10.5281/zenodo.23239278; v1.2: 10.5281/zenodo.23240818; v1.3: 10.5281/zenodo.23246727). GitHub's "Cite this
repository" button (generated from `CITATION.cff`) gives the same reference in other formats.

Part I: N. Johns, *Positive solutions of the explicit formula for ζ(s): near-criticality and uniqueness*,
[doi:10.5281/zenodo.23197915](https://doi.org/10.5281/zenodo.23197915).

## Related repositories

- [nic410/zeta-positive-solutions](https://github.com/nic410/zeta-positive-solutions) (DOI
  [10.5281/zenodo.23197915](https://doi.org/10.5281/zenodo.23197915)) is Part I of this series. It sets up the framework,
  poses Conjectures S and U, and proves the zero-side support theorem used here. This paper restates what it uses from
  Part I, and its Lean spine depends on Part I's spine at version 1.3.
- [nic410/dirichlet-critical-zeros](https://github.com/nic410/dirichlet-critical-zeros) (DOI
  [10.5281/zenodo.23070759](https://doi.org/10.5281/zenodo.23070759)) is an earlier paper by the same author, produced
  the same way: an unconditional proportion of simple zeros on the critical line for a weighted family of Dirichlet
  L-functions, with a Lean 4 formalisation. It is independent of this series; neither uses the other's results.

## Contact

Comments, questions and corrections are welcome by e-mail: Nic Johns, njohns@gmail.com.

## Licence

The paper and documentation are licensed under CC BY 4.0 (`LICENSE-CC-BY-4.0`). The code and data (everything under
`paper/anc/`, including the Lean formalisation) and the CI workflow are licensed under the Apache License 2.0 (`LICENSE`).
