# Reviewing guide

This guide is for specialists who want to check one part of the paper in a few hours. The paper is
[`paper/build/main.pdf`](paper/build/main.pdf) (49 pages); all numbers below are as printed there. No human expert has
checked the proofs yet. The paper splits into three slices that can be checked independently: each slice may assume the
interface statements listed for it, which the other slices prove.

## Load-bearing signs and constants

These are the places where a wrong sign or constant would break the proof. Each is cheap to check.

1. **The order derivative** ∂_μI_μ(z)|_{μ=1} = K₁(z) − I₀(z)/z (Lemma 4.1(b), equation (4.1)). It enters the coefficient
   formula β_n = −16πa_n (Proposition 4.7(d)) and the growing modes (Proposition 4.9(d)).
2. **The constant ¼** in m_{iv}(w) = ¼v^{−w} (Lemma 5.1(i), and (K4)). It fixes the normalisation of the lift,
   𝒢(1) = −½ (Theorem 5.4(d)).
3. **The decay of D_rest**: |D_rest(v)| ≤ C_D(1+v)²e^{−2πv} for v ≥ 1 (display (4.10)); the factor (1+v)² cannot be
   removed. It is used in Theorem 5.4(d) and Lemma 5.6.
4. **The Niebur–Poincaré constant 2** in the Fourier expansion, for all Re ν > 0 (Lemma 4.3, Theorem 4.4; compare
   Remark 4.5).
5. **The growing modes** (q, q′) = (4, −1/π) (after Proposition 4.9) and **the absence of constant terms**
   (Proposition 4.9(e)). They make the double pole at x = 1 residue-free and H entire (Theorem 5.4(d), Lemma 5.6).
6. **The cancellation of the Gamma factors** in the physical-side formula (Theorem 7.3, through Lemmas 5.1 and 7.1).
7. **The inequality at T₀ = 9 on the trivial-bound box** (Theorem 7.11 and the certified numbers of Proposition 7.10;
   margin ≥ 0.96595013), with Y_z = 0.90, so that t_mono = 5.754 ≤ 9 and B > 0 on [0.90, 4] for every sequence in the box.
8. **Positive definiteness and the moment minorant** (Proposition 6.5, Lemma 6.7). F̂_raw ≥ 0 must come from Ĝ_raw ≥ 0
   on [1, ∞) (Theorem 5.4(c),(d) with (5.8), and a_n > 0), not from Theorem 4(b), which presupposes C > 0; it gives
   C > 0 without computation. The bound cos y ≥ Σ_{j≤2K+1} (−1)^j y^{2j}/(2j)! holds for every real y because the
   truncation stops after a negative term; it gives F_raw(t) ≥ P_K(t). (On the physical side Π(0) is a cancellation of
   about 6·10⁵ : 1 in the coefficients, Remark 7.15; since version 1.3 the positivity proof does not evaluate Π near t = 0.)
9. **The Voronoi decoupling at growth exactly e^{π|Re z|/2}** (Definition 3.1, Lemma 3.2): the factor cancels against
   the decay of Ξ², and the power 8 in (C1) is what keeps Ξ²H a test function.
10. **Strict positivity H > 0 on ℝ** (Corollary 7.12) is what Theorem 2 needs: it makes the real zeros of F = Ξ²H exactly
    the zeros of ζ, so that the zero-side support theorem (Theorem I.3.6) applies.
11. **The ε-margin in the transfer lemma** (Lemma C.1). The transform of F₀ = Ξ²H vanishes doubly at ξ₂ = log 2/2π, so
    adding a multiple of F₀ cannot in general repair a test function whose transform is negative just below ξ₂; the Gaussian margin
    ε𝗀 is what makes the transfer work. Corollary 8.2 also uses the strict positivity of F̂₀ on [0, ξ₂) (part (a)).

## Slice A: framework, reduction and assembly (§§1–3, §8 and Appendix C; pages 1–13, 33–36 and 45–47)

**May assume.** The properties of H proved in §§4–7, which are the hypotheses of Proposition 3.3: (C1) (Proposition 5.9),
(C2) H > 0 (Corollary 7.12), (C3) the integer zeros (Proposition 5.11), (C4) Ĝ_H ≥ 0 on [0, ∞) (Theorem 4(b) with
Theorem 6.1); ∫F > 0 then follows in Proposition 3.3 from H ≢ 0. Also Part I's results as restated in §2, with the list (P1)–(P5) of
the Part I proofs and inputs that are not reproduced. For Corollary 8.2, also Theorem 4(a),(b) (every a_n > 0, and C > 0,
which is Proposition 6.5).

**Check first.**
- Lemma 3.2: the contour shift to Im w = −η with Re(½ + iw) > 1, and the bound |G_H| ≤ C(1+|Re z|)^{−4+δ} at growth exactly
  e^{π|Re z|/2}.
- Proposition 3.3, including ∫F = Ĝ_H(0) > 0 from H ≢ 0.
- §8: the argument that F̂′(ξ_n) = 0 (tF ∈ L¹); Theorem 2 from Corollary I.3.9(a); the logic of Corollary 3.
- Corollary 8.2 (the classical cone): the positivity of F̂₀ on [0, ξ₂) in part (a), complementary slackness at the gap ℓ in part (b),
  and the logic of part (c), which uses Part I's duality theorem only at the gap ξ₂.
- Appendix C: the transfer lemma (Lemma C.1) and the duality theorem at an arbitrary gap (Proposition C.2), against Part I,
  Appendices B.1.1–B.1.2 (Remark C.3 lists every place where the gap enters).
- §2: the restatements against Part I.

## Slice B: the automorphic object and the Green-flux lift (§§4–5; pages 13–25)

**May assume.** Standard facts on Bessel functions (DLMF) and Kloosterman sums; the bounds of Appendix B.

**Delivers** (the interface to the rest of the paper):
- Theorem 4(b), (c): the Γ-only transform of H_raw is −𝒢(x)/(16π²), equal to sin²(πx)√x Σ a_n K₀(4π√(nx)) for x > 1
  and to 1/(32π²) at x = 1;
- H_raw entire with (C1) (Proposition 5.9);
- the integer double zeros and the normalisation ∫Ξ²H_raw = 1/(32π²) (Proposition 5.11);
- the four-path representation used in §7 (Theorem 5.4(e)).

**Check first.**
- Lemma 4.3 (the Weyl-element integral; the constant 2) and Theorem 4.4 (J for S(1, n; c), I for S(−1, n; c)).
- Proposition 4.7(d) (β_n = −16πa_n, where the ¼ comes from (4.1)).
- Lemma 4.6 (a three-line identity).
- Lemma 4.8 and Proposition 4.9 (Sym² components, growing modes, no constant terms).
- Theorem 5.4(b): Stokes on the regions near the cusps, orientations, and the connectors (only for x > 1).
- Theorem 5.4(d): 𝒢(1) = −½ and the residue-free double pole.
- Lemma 5.6 (small x) and Proposition 5.9.

**A quick numerical test.** Compute the density D(v) at v = 1 from the expansion at the cusp 0, (4.9), and from the
expansion at the cusp ∞ (Lemma A.3). They must agree. This one test checks the constant 2, the ¼, the sign of (4.1) and
the Kloosterman conventions together.

## Slice C: positivity and certificates (§§6–7, Appendices A–B; pages 25–33 and 38–45)

**May assume.** Theorem 4 (the coefficients a_n and the Γ-only transform), Definition 5.8, Proposition 5.9,
Proposition 5.11, Lemma 5.1 and Theorem 5.4 (the four-path functional and its values), all from Slice B, and the
Voronoi decoupling (Lemma 3.2) from Slice A.

**Check first.**
- Theorem 6.1: every a_n is positive, from the term c = 1 and the trivial Kloosterman bound; its constants at z = 4π
  (λ₋(4π) = 0.8501…). The trivial-bound box (6.1), which its proof gives.
- Proposition 6.5 (positive definiteness of Ξ²H_raw, and C > 0 without computation) and Lemma 6.7 (the moment
  minorant).
- Theorem 6.8, the moment certificate (|t| ≤ 10.355), with the method in Appendix A.3: the tail bracket, the quadrature
  bound (Lemma A.2), the ends, the uniformity on the box and the cell test in t.
- Theorem 7.3: the physical-side formula and the cancellation of the Gamma factors.
- Theorem 7.2: Mehler–Dirichlet positivity of the conical kernel.
- Theorem 7.11 (|t| ≥ 9), with Lemmas 7.5–7.8 and the numbers of Proposition 7.10 (Appendix A.4).
- Appendix B.

Not needed for the proofs: the window certificate (Theorem 7.13, Appendix A.2), Theorem 7.4 at T₀ = 8 and Remark 7.15;
they are independent checks.

## Reproducing in five minutes

From the top of the repository, with Python ≥ 3.10 and python-flint 0.9.0:

```sh
cd paper/anc
sha256sum -c SHA256SUMS                            # every file: OK
cp -r . ../anc-rerun && cd ../anc-rerun            # re-runs overwrite the logs, so work on a copy
export PY=python3
./runlog.sh positivity/logs/cert_moments_box.log "$PY" positivity/cert_moments_box.py 60 8 15 12 9 64 6
./runlog.sh positivity/logs/cert_large_t_T9_box.log "$PY" positivity/run_on_box.py large_t 9 0.5 1 0.90 4 2000 8000
./runlog.sh positivity/logs/cert_gtail_box.log "$PY" positivity/run_on_box.py gtail
"$PY" tools/logdiff.py ../anc/positivity/logs positivity/logs     # every log: IDENTICAL
```

These are the certificates on which the positivity of H rests (Corollary 7.12), and they use the coefficients only through
the term c = 1 and the trivial Kloosterman bound. The moment certificate takes about 15 s on 6 cores and ends with
`DECISIVE (Certificate M-box, trivial Kloosterman bound only): ... for |t| <= 10.35546875 (moments M_0..M_30) ; covers [0, 9]: True`.
The large-|t| run takes about 135 s and ends with `DECISIVE (all-Arb): Theorem L hypotheses verified for T0 = 9: True`,
and the tail check with `DECISIVE: g > 0 on [4, oo): True`. Here R is the function Π of the paper. The independent checks
(the window [0, 40] and the large-|t| run at T₀ = 8) take about 3 minutes more, and the coefficient certificates and the
normalising constant about 77 CPU-minutes; see `paper/anc/README.md`, Sections 7–13.

**Lean.** In `paper/anc/lean/`, run `lake build` and `scripts/audit.sh`; the spine depends on Part I's Lean project (see
`paper/anc/lean/README.md`). It checks the assembly of the proof from named axioms, not the existence of the object; it
covers Theorems 1–2 and Corollaries 3 and 8.2 (the latter except the zero set in its part (a) and its clause (c)(iv)).

## What is not claimed

- The Riemann hypothesis is not proved, nor is the existence of an admissible pair, which is equivalent to it (Corollary 3).
- κ* is not claimed to be attained when RH fails (under RH it is attained, by F/∫F: Corollary 3).
- The integer-critical function is not claimed to be unique.
- The growth of H off the strip (order 1, not of exponential type) is only sketched (Remark 5.10) and is not used.
- Positivity of H rests on two certified computations on the trivial-bound box: Theorem 6.8 for |t| ≤ 10.355 and
  Proposition 7.10 for |t| ≥ 9. Only H(0) > 0 is proved without computation (Proposition 6.5). No proof without computer is
  claimed; the range |t| < 4.4699 of Remark 6.9 rests on two integrals evaluated in Arb and is not used in the proofs.
- Theorem 2 and Corollaries 3 and 8.2 rest on Part I's Theorem I.3.6, whose proof is not reproduced here (§2, items (P1)–(P5)).

## How to report

Please e-mail Nic Johns at njohns@gmail.com. A one-line "this is wrong because X" is very welcome, and so is
"I checked slice B and found nothing wrong". Please say which slice you read.
