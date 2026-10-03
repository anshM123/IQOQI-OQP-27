# STATUS_L3b -- module L3b (Theorem 1, 2BMV, distribution-free route; the Radon identity)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.  Namespace `OQP27.StripL3b`.  Date: 2026-10-02.
Toolchain: Lean v4.33.1 and the Mathlib of `LEAN_BRIEF.md`.

Build (from lean/): `bash OQP27/logs/build_L3b.sh` (all files, in dependency order:
StripJensen StripPencil StripSlice StripBounds StripBMV StripRIContour StripRIPencil StripRISums StripRISmooth
StripRIEnds StripRIBoundary StripRIAssembly StripRIMain StripRIChain StripAxiomsL3b).  `StripRIChain` also needs the
oleans of L3a's `StripTheorem2`, `StripSkeleton` and L1's `Skeleton`.
All files compile with no `sorry`, `admit`, `axiom` or `native_decide`, and with no warnings; `#print axioms`
(`OQP27/StripAxiomsL3b.lean`, log `OQP27/logs/StripAxiomsL3b.log`) shows only `[propext, Classical.choice, Quot.sound]`
for all 59 listed results.

Paper references: Q_2bmv = `proofs/strip-inequality/PROOF.md`; Q_RI = `proofs/radon-identity/PROOF.md`.

## Summary

* **The Radon identity is PROVED**: `hyp_RI : ∀ M, Hyp_RI M` (StripRIMain), following Q_RI s.1-2.
* **Theorem 1 (2BMV) is PROVED with no hypotheses**, for all `(a, t) ∈ ℂ²`: `theorem1_bmv2`, `theorem1_iterated`,
  `theorem1_package` (StripRIMain).
* With the bridges of module L3a, **Theorem 2** (exact defect, the strip inequality (*), equality case) and the L1
  skeleton hypotheses **`OQP27.Hyp_StripInequality`, `OQP27.Hyp_StripEquality` are PROVED** (StripRIChain:
  `strip_defect_formula_noHyp`, `strip_inequality_noHyp`, `strip_equality_iff_noHyp`, `hyp_StripInequality`,
  `hyp_StripEquality`).  Any theorem taking `hRI : ∀ M, OQP27.StripL3b.Hyp_RI M` (e.g. in `OQP27/Main.lean`) can be
  applied to `OQP27.StripL3b.hyp_RI`.
* No hypotheses remain in module L3b.

## Results: Theorem 1 from (RI) (Q_2bmv; Q_RI s.4)

| Lean name (file) | paper statement | status |
|---|---|---|
| `integral_log_norm_sub`, `tendsto_logPot` (StripJensen) | `∫_{-L}^L log|x - z| dx` in closed form; asymptotics `→ π|Im z|` | PROVED |
| `tendsto_integral_log_norm_eval` (StripJensen) | real-line Jensen asymptotics for a polynomial | PROVED |
| `jensen_identity` (StripJensen) | **Lemma 2** (Q_2bmv): `∫_ℝ log|p/q| = π ∑ |Im x_i|`, with integrability | PROVED |
| `pencilRoots_eq_roots_det`, `det_pencil` (StripPencil) | pencil roots = roots of `det(H - y(P - τ))`; leading coefficient `det(-(P - τ))` | PROVED |
| `pencilRoots_pinch_im` (StripPencil) | **Lemma 1(d)**: the pinched pencil has only real roots | PROVED |
| `sum_pencilRoots_pinch` (StripPencil) | **Lemma 1(e)**: equal root sums (and equal leading coefficients) | PROVED |
| `measurable_stripF`, `stripF_nonneg` (StripPencil) | `F ≥ 0`, `F` measurable on `ℝ²` (Lemma 1(f) is replaced by measurability) | PROVED |
| `stripF_eq_jensen` (StripPencil) | eq. (3.4): `F = (1/2π²) ∫ log|p/q|` | PROVED |
| `normSq_nonreal_root_le`, `stripF_le` (StripBounds) | **Lemma 1(b)** (with the Frobenius norm): `F ≤ M‖g - s‖_F/(2π√(τ(1-τ)))` | PROVED |
| `pencilRoots_im_of_posSemidef`, `stripF_eq_zero_of_semidef` (StripBounds) | **Lemma 1(c)**: `F(s,τ) = 0` unless `λ_min < s < λ_max` | PROVED |
| `stripF_support`, `stripF_bound` (StripBounds) | compact support in `s`; `F ≤ C/√(τ(1-τ))` | PROVED |
| `trace_exp_smul_isHermitian` (StripSlice) | `Tr e^{aA} = ∑ e^{aλ_i}` | PROVED |
| `integral_exp_mul_sliceU` (StripSlice) | **Lemma 3(b)** (real `a ≠ 0`): `∫ e^{aw} U_ξ(w) dw = D(a, aξ)/a²` | PROVED |
| `trace_exp_pinch`, `bmvD_eq_paper` (StripBMV) | `Tr e^{a g_d - tP} = e^{-t}Tr_P e^{aPgP} + Tr_B e^{aBgB}`; `bmvD` = paper's `D` | PROVED |
| `radon_eq_sliceFun` (StripBMV) | (RI) ⟹ `∫_0^1 F(w + ξτ, τ) dτ = U_ξ(w)` (Q_RI eq. (4.1)) | PROVED from `Hyp_RI` |
| `integral_exp_mul_stripF`, `bmv2_real` (StripBMV) | (RI) ⟹ `D(a,t) = a² ∫∫ e^{as - tτ} F` for real `a ≠ 0`, real `t` (Tonelli) | PROVED from `Hyp_RI` |
| `bmv2_of_RI`, `bmv2_of_RI_complex` (StripBMV) | **Theorem 1**: real `a` and complex `t`; all `(a, t) ∈ ℂ²` | PROVED from `Hyp_RI` |
| `laplaceF_eq_iterated`, `bmv2_package` (StripBMV) | the double integral as `∫_0^1 ∫_ℝ`; interface for L3a | PROVED from `Hyp_RI` |

## Results: proof of the Radon identity (Q_RI s.1-2)

Notation: `Rt P A τ c` = roots of `det(A + c - y(P - τ))`; `S_±` = `Sup`/`Slo`, `Λ_±` = `Lup`/`Llo` (sums of the roots,
resp. of their logarithms, in `ℂ₊`/`ℂ₋`); `A_d = pinch P A`; `F = S_+(A) - S_+(A_d)`; `Ψ(c) = ∫_0^1 F dτ`;
`E(c) = ∑ ω(λ⁰_j + c) - ∑ ω(λ_j + c)`, `ω(z) = z Log z`.

| Lean name (file) | paper statement | status |
|---|---|---|
| `circleIntegral_mul_logDeriv` (StripRIContour) | eq. (1.1): `∮ φ p'/p = 2πi ∑_{roots in disc} φ` | PROVED |
| `hasDerivAt_circleIntegral`, `continuousOn_circleIntegral` (StripRIContour) | (F3): differentiation/continuity of circle integrals in parameters | PROVED |
| `penPoly_eq_lagrange`, `penPolyDt_eq` (StripRIPencil) | Lemma C: `p(y; τ, c) = f(y, c + yτ)`, hence `p_τ = y p_c` | PROVED |
| `root_im_identity`, `pencilRoot_im_bounds` (StripRIPencil) | **Lemma A(a)**: `Im c = a Im y`; no real roots; `Im y ≥ Im c/(1 - τ)` in `ℂ₊`, `≤ -Im c/τ` in `ℂ₋` | PROVED |
| `pencilRoot_norm_bound` (StripRIPencil) | **Lemma B(ii)** | PROVED |
| `pencilRoot_norm_bound_all` (StripRISmooth) | **Lemma B(i)** | PROVED |
| `Sup_add_Slo`, `sum_Rt_pinch`, `norm_Sup_sub_le` (StripRISums) | **Lemma B(iii)**: trace identity and `|S_+ - S⁰_+| ≤ 2M√K/√(τ(1-τ))` | PROVED |
| `upper_global`, `lower_global` (StripRISmooth) | **Lemma C**: regularity of `S_±`, `Λ_±` on `(0,1) × ℂ₊` and `∂_τ Λ_± = ∂_c S_±` | PROVED |
| `upper_end` (StripRIEnds) | **Lemma D(a)**: `Λ_+(A) - Λ_+(A_d) → 0` as `τ → 1`, uniformly on compacts | PROVED |
| `lower_end` (StripRIEnds) | mirror of D(a): `Λ_-(A) - Λ_-(A_d) → 0` as `τ → 0`, uniformly on compacts (replaces D(b), see below) | PROVED |
| `jensen_error`, `logPot_error` (StripRIBoundary) | quantitative real-line Jensen: error `≤ 10 n R²/L` | PROVED |
| `norm_det_add_I_mono` (StripRIBoundary) | `ε ↦ |det(N + iε)|` nondecreasing (`N` Hermitian) | PROVED |
| `tendsto_imAbsSum_vertical` (StripRIBoundary) | **Lemma E** (imaginary parts): `∑|Im y(τ, c₀ + iε)| → ∑|Im y(τ, c₀)|` | PROVED |
| `exp_Gup_add_Glo`, `exists_int_Gup_add_Glo` (StripRIAssembly) | `exp(Λ_+ + Λ_-)(A) / exp(Λ_+ + Λ_-)(A_d) = det(A + c)/det(A_d + c) = exp Θ₁`; the `2πiℤ` constant `k` | PROVED |
| `hasDerivAt_PsiD`, `tendsto_PsiD` (StripRIAssembly) | **Step 1**: `Ψ_δ' = G(1-δ, c) - G(δ, c)`; `Ψ_δ → Ψ` | PROVED |
| `hasDerivAt_Efun`, `tendsto_im_omegaF` (StripRIAssembly) | `E' = -Θ₁`; `Im (t + iε) Log(t + iε) → π min(t, 0)` | PROVED |
| `Psi_sub_E_affine` (StripRIAssembly) | **Steps 1-2**, eq. (2.1): `Ψ - E = -2πik c + κ` on `ℂ₊` | PROVED |
| `im_Fd`, `tendsto_im_Psi`, `tendsto_im_Efun` (StripRIMain) | **Step 3**: boundary values `Im Ψ → π L(H + c₀)`, `Im E → π R(H + c₀)` | PROVED |
| `radon_identity`, `integrableOn_imAbsSum` (StripRIMain) | **Theorem RI** (Step 4), with integrability | PROVED |
| `hyp_RI` (StripRIMain) | `Hyp_RI M` for every `M` | PROVED |
| `theorem1_bmv2`, `theorem1_iterated`, `theorem1_package`, `radon_slices` (StripRIMain) | **Theorem 1 (2BMV)**, all `(a,t) ∈ ℂ²`, no hypotheses; Radon slices of `F` | PROVED |
| `hyp_BMV2_stripF` (StripRIChain) | L3a's `Hyp_BMV2 B g (stripF (1 - B) g)` | PROVED |
| `strip_defect_formula_noHyp`, `strip_inequality_noHyp`, `strip_equality_iff_noHyp` (StripRIChain) | **Theorem 2** of Q_2bmv (via L3a) | PROVED |
| `hyp_StripInequality`, `hyp_StripEquality` (StripRIChain) | L1's skeleton hypotheses `OQP27.Hyp_StripInequality`, `OQP27.Hyp_StripEquality` | PROVED |

### Differences from the paper proof (Q_RI s.1-2)

* Lemma A(b) (the count `M - r` of roots in `ℂ₊`) and Proposition 2.1 (`κ = 0`) are not needed.
* Lemma D(b) (Schur complement at `τ → 0`) is replaced by `lower_end` (the mirror of D(a), with `τ Y → -(1 - P)(A + c)`)
  plus `exp(Λ_+ + Λ_-) = det((P - τ)⁻¹(A + c))`: the function `G + G₋ - Θ₁` is continuous with values in `2πiℤ` on the
  connected set `(0,1) × ℂ₊`, hence a constant `2πik`.
* Weierstrass' theorem (Step 1) is replaced by the mean value inequality on segments in `ℂ₊`.
* Lemma E is proved with the quantitative real-line Jensen formula and dominated convergence instead of the continuity of
  the roots.
* Step 4 uses `c₀ ≥ 1 + ∑|λ_j| + ∑|λ⁰_j|` (all pencil roots real by Lemma 1(c), `Tr(H + c₀)_+ = Tr(H + c₀)`).

## Build logs
`OQP27/logs/<File>.log` for every file listed above (`StripJensen` ... `StripAxiomsL3b`); build script
`OQP27/logs/build_L3b.sh`.

## Notes for L3a (Theorem 2) and for the final assembly
* `OQP27.StripL3b.hyp_RI : ∀ M, Hyp_RI M` discharges every `hRI` argument (L3a's `StripTheorem2.lean`, `StripSkeleton.lean`,
  and `OQP27/Main.lean`).
* `theorem1_package hP hg` (= `bmv2_package (hyp_RI M) hP hg`) gives `F := stripF P g` measurable, `≥ 0`, zero for
  `τ ∉ (0,1)` and for `|s| ≥ R`, bounded by `C/√(τ(1-τ))`, all Laplace integrands integrable, and
  `bmvDPaper P g a t = a² ∫∫ e^{as - tτ} F` for all complex `a, t`, where
  `bmvDPaper P g a t = Tr e^{ag - tP} - e^{-t} Tr(P e^{a PgP}) - Tr((1-P) e^{a (1-P)g(1-P)})`.
