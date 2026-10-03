# STATUS of module L3a (strip Poisson kernel, h_lam, Theorem 2 from Theorem 1)

Date: 2026-10-02.  Toolchain: Lean v4.33.1, Mathlib 0df444a3 (as in `LEAN_BRIEF.md`).
Paper: `proofs/strip-inequality/PROOF.md`, sections 0 and 5 (Lemmas 5, 6, eq. (5.1), Theorem 2).
All declarations are in the namespace `OQP27.StripL3a`.

## Summary

* Theorem 2 of the paper (the strip inequality (*) for every matrix size `M`, its exact defect formula and its
  equality case) is PROVED in Lean from Theorem 1 (2BMV), which enters as the explicit hypothesis `Hyp_BMV2`,
  for any density `F` with the regularity of Theorem 1 (`DensityReg`).  No `sorry`, no `axiom`, no
  `native_decide`; `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every result
  (`OQP27/StripAxiomsL3a.lean`, log `OQP27/logs/StripAxiomsL3a.log`).
* Combined with module L3b (`OQP27/StripBMV.lean`, Theorem 1 from the Radon identity), Theorem 2 for the
  explicit density `F = OQP27.StripL3b.stripF (1 - B) g` is PROVED from `OQP27.StripL3b.Hyp_RI M` alone
  (`OQP27/StripTheorem2.lean`), and the skeleton hypotheses `OQP27.Hyp_StripInequality` and
  `OQP27.Hyp_StripEquality` of module L1 are PROVED from `∀ M, OQP27.StripL3b.Hyp_RI M`
  (`OQP27/StripSkeleton.lean`).

## Files (build order) and logs

| File | Content | Build log |
|---|---|---|
| `OQP27/StripKernel.lean` | `K_X`: positivity, exponential bound, Fourier transform, mass, first moment | `OQP27/logs/StripKernel.log` |
| `OQP27/StripPoisson.lean` | Poisson measures `ω_ν`, eq. (5.1) (imaginary axis), `hLam`, ramp kernel, analytic core, Fourier uniqueness | `OQP27/logs/StripPoisson.log` |
| `OQP27/StripSpectral.lean` | matrix facts: traces through charpoly roots, eigenvalue strip, compression spectrum, `stripD`, equality-case algebra | `OQP27/logs/StripSpectral.log` |
| `OQP27/StripFromBMV.lean` | `Hyp_BMV2`, `DensityReg`, the balayage `V`, **Theorem 2** | `OQP27/logs/StripFromBMV.log` |
| `OQP27/StripLaplace.lean` | Lemma 5 in its Laplace form (real `a`, complex strip), eq. (5.1) for real `a` (not needed for Theorem 2) | `OQP27/logs/StripLaplace.log` |
| `OQP27/StripTheorem2.lean` | bridge to L3b: Theorem 2 for `stripF` from `Hyp_RI` | `OQP27/logs/StripTheorem2.log` |
| `OQP27/StripSkeleton.lean` | bridge to L1: `Hyp_StripInequality`, `Hyp_StripEquality` from `Hyp_RI` | `OQP27/logs/StripSkeleton.log` |
| `OQP27/StripAxiomsL3a.lean` | `#print axioms` for all main results | `OQP27/logs/StripAxiomsL3a.log` |

Build each with `bash OQP27/leanrun.sh OQP27/<File>.lean -o .lake/build/lib/lean/OQP27/<File>.olean -i .lake/build/lib/lean/OQP27/<File>.ilean`
in the order of the table (`StripKernel` before `StripPoisson`; `StripSpectral` is independent of both;
`StripTheorem2` also needs L3b's `StripBMV`; `StripSkeleton` also needs L1's `Skeleton`).

## Table of results

| Lean name | Paper statement | Status |
|---|---|---|
| `stripKernel`, `stripKernel_pos`, `stripKernel_le`, `stripKernel_neg` | Lemma 5: `K_X(u) = sin(πX)/(2(cosh πu - cos πX)) > 0`, `K_X(u) ≤ C_X e^{-π\|u\|}`, `K_X` even | PROVED |
| `fourier_stripKernel` | Lemma 5 at `a = iκ`: `∫ e^{-iκu} K_X(u) du = sinh(κ(1-X))/sinh κ` (`κ ≠ 0`) | PROVED |
| `integral_stripKernel`, `integral_mul_stripKernel` | mass `∫ K_X = 1 - X`; first moment `0` | PROVED |
| `laplace_stripKernel` | Lemma 5: `∫ e^{-au} K_X(u) du = sin(a(1-X))/sin a`, real `0 < \|a\| < π` | PROVED |
| `sin_mul_kernelLaplace` | `sin a · ∫ e^{-au} K_X = sin(a(1-X))` for complex `\|Re a\| < π` | PROVED |
| `hLam` | `h_λ` on the closed strip: `(y-λ)_+` on `x = 0`, `0` on `x = 1`, Poisson integral inside (definition, as in `LEAN_BRIEF.md`) | DEFINITION |
| `fourier_stripKernel_sub`, `laplace_stripKernel_sub` | eq. (5.1): `∫ e^{aw} ω_ν(dw) = e^{ay} sin(a(1-x))/sin a` (imaginary and real `a`) | PROVED |
| `integral_stripKernel_sub`, `integral_mul_stripKernel_sub` | mass `1 - x` and first moment `(1-x)y` of `ω_ν` | PROVED |
| `trace_pow_eq_sum_roots`, `trace_exp_smul_eq_sum_roots` | `Tr Xⁿ = Σ νⁿ`, `Tr e^{cX} = Σ e^{cν}` over charpoly roots (any complex matrix) | PROVED |
| `re_mem_Icc_of_mem_roots` | eigenvalues of `B + ig` satisfy `0 ≤ Re ν ≤ 1` | PROVED |
| `exists_compression_basis`, `trace_mul_exp_of_diag`, `posPartTrace_compress_eq` | `spec(PgP\|ran P)`: `Tr_P e^{aPgP} = Σ_j p_j e^{a d_j}`, `Tr[(P(g-λ)P)_+] = Σ_j p_j (d_j - λ)_+` | PROVED |
| `mass_moment_eq` | step (b): `ρ`, `σ` have equal mass and first moment | PROVED |
| `stripD`, `stripD_sub_eq` | `D(a,t)` (section 0); step (a): `D(iκ,-κ) - D(iκ,κ)` through the eigenvalues | PROVED |
| `stripD_eq_sub_pinch` | `D(a,t) = Tr e^{ag-tP} - Tr e^{a g_d - tP}` (L3b's `bmvD`) | PROVED |
| `poissonDefect_eq_rampDefect`, `integrable_rampDefect`, `continuous_poissonDefect`, `fourier_rampDefect` | step (b): Fourier transform of `λ ↦ ∫ (u-λ)_+ d(ρ-σ)` is `-(ρ̂ - σ̂)/κ²` | PROVED |
| `eq_zero_of_fourier_eq_zero` | uniqueness of the Fourier transform (continuous integrable functions) | PROVED |
| `stripBalayage`, `DensityReg.continuous_stripBalayage`, `DensityReg.fourier_balayageProd` | the defect `V(λ) = ∫_0^1 ∫_ℝ K_{1-τ}(s-λ) F ds dτ`: continuity, Fourier transform | PROVED |
| `rhohat_sub_sigmahat` | (5.2) on the imaginary axis: `ρ̂ - σ̂ = -κ² V̂` | PROVED from `Hyp_BMV2`, `DensityReg` |
| `strip_defect_formula` | **Theorem 2**: `Σ_ν h_λ(ν) - Tr[(P(g-λ)P)_+] = V(λ)` | PROVED from `Hyp_BMV2`, `DensityReg` |
| `strip_inequality` | **(*)**: `Tr[(P(g-λ)P)_+] ≤ Σ_ν h_λ(ν)` | PROVED from `Hyp_BMV2`, `DensityReg` |
| `strip_equality_iff` | **Theorem 2 (d)**: equality at `λ` iff `[B, g] = 0` | PROVED from `Hyp_BMV2`, `DensityReg` |
| `commute_of_stripD_zero`, `stripD_zero_of_commute` | `D(·,0) ≡ 0` iff `[B,g] = 0` (replaces Remark 4.3) | PROVED |
| `Hyp_BMV2 B g F` | Theorem 1 (2BMV): `D(a,t) = a² ∫_0^1 ∫_ℝ e^{as-tτ} F(s,τ) ds dτ`, all `(a,t) ∈ ℂ²` | HYPOTHESIS (paper: `Q_2bmv/PROOF.md` s.1-4; `Q_RI/PROOF.md` s.4) |
| `DensityReg F` | regularity of Theorem 1: measurable, `F ≥ 0`, `F = 0` off `0 < τ < 1`, compact `s`-support, `F ≤ C/√(τ(1-τ))` | assumption on `F`; for `stripF` PROVED by L3b |
| `densityReg_stripF`, `hyp_BMV2_of_RI` | the two hypotheses for `F = OQP27.StripL3b.stripF (1 - B) g` | PROVED from `OQP27.StripL3b.Hyp_RI` |
| `strip_defect_formula_of_RI`, `strip_inequality_of_RI`, `strip_equality_iff_of_RI` | Theorem 2 for the explicit density | PROVED from `OQP27.StripL3b.Hyp_RI` |
| `hyp_StripInequality_of_RI`, `hyp_StripEquality_of_RI` | L1's `OQP27.Hyp_StripInequality`, `OQP27.Hyp_StripEquality` | PROVED from `∀ M, OQP27.StripL3b.Hyp_RI M` |

## Formalisation choices

* `F` is a parameter: `Hyp_BMV2 B g F` is the identity of Theorem 1 for a given density `F`, and Theorem 2 is
  proved for every `F` satisfying `DensityReg`.  For the explicit density of the paper (L3b's `stripF`, the
  roots of `det(g - s - x(P - τ))`), both are discharged in `StripTheorem2.lean` (from L3b's `bmv2_package`).
  Continuity of `F` is not needed.
* `D(a,t)` is the three-term form of the paper, with `Tr_P e^{aPgP}` written as `Tr(P e^{aPgP})`
  (`stripD`); `stripD_eq_sub_pinch` and `stripD_eq_bmvDPaper` connect it with L3b's `bmvD`/`bmvDPaper`.
* `Tr[(P(g-λ)P)_+]` is `posPartTrace (P * (g - λ • 1) * P)`, `= Σ_i max(λ_i, 0)` (`posPartTrace_eq`);
  `h_λ` is defined as the Poisson integral (the `Li₂` formula of Lemma 6 is a remark, not formalised).
* Route: Theorem 1 is used at `(a, t) = (iκ, ∓κ)`, `κ` real (the paper uses `t = ±ia`, `a` real).  On this
  line Lemma 5 is a Fourier transform, proved by computing the inverse Fourier transform of
  `sinh(κ(1-X))/sinh κ` (geometric series + Mittag-Leffler expansion of the cotangent, Mathlib) and Fourier
  inversion.  The function `W` and the two integrations by parts of step (b) are replaced by a Fubini argument
  with the ramp kernel `k(u,λ) = (u-λ)_+` (`λ ≥ 0`), `(λ-u)_+` (`λ < 0`), whose Fourier transform is
  `(1 + iκu - e^{iκu})/κ²`.  Uniqueness is Mathlib's Fourier inversion; no analytic continuation and no
  Laplace-transform uniqueness (Lemma U of `Q_RI/PROOF.md` s.5) is needed.  The equality case uses the second
  derivative of `a ↦ D(a, 0)` at `0` (`= 2‖BgP‖_F²`) instead of the Duhamel formula of Remark 4.3.
* Not formalised (not needed): the series `K_X(u) = Σ_n sin(nπX) e^{-nπ|u|}` of Lemma 5 and the harmonicity /
  `Li₂` closed form of Lemma 6.
