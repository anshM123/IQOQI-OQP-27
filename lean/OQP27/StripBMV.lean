import OQP27.StripBounds
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Theorem 1 (2BMV, explicit density) from the Radon identity (module L3b)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

`bmvD P g a t = Tr e^{a g - t P} - Tr e^{a g_d - t P}`; `bmvD_eq_paper` shows that this is the paper's
`D(a, t) = Tr e^{a g - t P} - e^{-t} Tr_P e^{a P g P} - Tr_B e^{a B g B}`.

Main results:
* `radon_eq_sliceFun`: (RI) implies that the Radon projection of `F` in every direction `ξ` is the
  slice function `U_ξ`;
* `integral_exp_mul_stripF`: (RI) implies, for real `a ≠ 0` and real `ξ`, that `e^{a s - a ξ τ} F` is
  integrable on `ℝ²` with integral `D(a, a ξ)/a²` (Tonelli, translation invariance, Lemma 3(b));
* `bmv2_of_RI` (real `a`, complex `t`) and `bmv2_of_RI_complex` (all `(a, t) ∈ ℂ²`):
  **Theorem 1**, `D(a, t) = a² ∫∫ e^{a s - t τ} F(s, τ) ds dτ` (identity theorem in `t`, then in `a`);
  `laplaceF_eq_iterated`: the same integral as `∫_0^1 ∫_ℝ`;
* `bmv2_package`: everything Theorem 2 needs about `F`, in one statement.

Hypothesis used: `Hyp_RI M` (**the Radon identity**), stated below.  Its paper proof is in
`iqoqi/programs/oqp27B_all/Q_RI/PROOF.md` (sections 1-2); it is PROVED in Lean for every `M`
(`OQP27.StripL3b.hyp_RI`, `OQP27/StripRIMain.lean`), where the hypothesis-free forms of the theorems
below are stated (`theorem1_bmv2`, `theorem1_iterated`, `theorem1_package`, `radon_slices`).
Paper: `iqoqi/programs/oqp27B_all/Q_RI/PROOF.md`, section 4; `Q_2bmv/PROOF.md`, Theorem 1.
-/

namespace OQP27.StripL3b

open Matrix MeasureTheory Filter Topology Real

variable {M : ℕ}

/-- `D(a, t) = Tr e^{a g - t P} - Tr e^{a g_d - t P}`
(`= Tr e^{a g - t P} - e^{-t} Tr_P e^{a P g P} - Tr_B e^{a B g B}`). -/
noncomputable def bmvD (P g : Matrix (Fin M) (Fin M) ℂ) (a t : ℂ) : ℂ :=
  (NormedSpace.exp (a • g - t • P)).trace - (NormedSpace.exp (a • pinch P g - t • P)).trace

/-! ### The paper's form of `D` -/

set_option backward.isDefEq.respectTransparency false in
/-- If `X V = c V` then `e^X V = e^c V`. -/
lemma exp_mul_of_mul_eq_smul {X V : Matrix (Fin M) (Fin M) ℂ} {c : ℂ} (h : X * V = c • V) :
    NormedSpace.exp X * V = Complex.exp c • V := by
  have hpow : ∀ n : ℕ, X ^ n * V = c ^ n • V := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', Matrix.mul_assoc, ih, Matrix.mul_smul, h, smul_smul, ← pow_succ]
  open scoped Matrix.Norms.Operator in
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) X).mul_right V
  open scoped Matrix.Norms.Operator in
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) c).smul_const V
  have hfun : (fun n : ℕ => ((n.factorial : ℂ)⁻¹ • X ^ n) * V)
      = fun n : ℕ => ((n.factorial : ℂ)⁻¹ • c ^ n) • V := by
    funext n; rw [Matrix.smul_mul, hpow, smul_smul, smul_eq_mul]
  rw [hfun] at h1
  rw [← Complex.exp_eq_exp_ℂ] at h2
  exact h1.unique h2

set_option backward.isDefEq.respectTransparency false in
/-- If `V X = c V` then `V e^X = e^c V`. -/
lemma mul_exp_of_mul_eq_smul {X V : Matrix (Fin M) (Fin M) ℂ} {c : ℂ} (h : V * X = c • V) :
    V * NormedSpace.exp X = Complex.exp c • V := by
  have hpow : ∀ n : ℕ, V * X ^ n = c ^ n • V := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.smul_mul, h, smul_smul, ← pow_succ]
  open scoped Matrix.Norms.Operator in
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) X).mul_left V
  open scoped Matrix.Norms.Operator in
  have h2 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) c).smul_const V
  have hfun : (fun n : ℕ => V * ((n.factorial : ℂ)⁻¹ • X ^ n))
      = fun n : ℕ => ((n.factorial : ℂ)⁻¹ • c ^ n) • V := by
    funext n; rw [Matrix.mul_smul, hpow, smul_smul, smul_eq_mul]
  rw [hfun] at h1
  rw [← Complex.exp_eq_exp_ℂ] at h2
  exact h1.unique h2

/-- `Tr e^{a g_d - t P} = e^{-t} Tr_P e^{a P g P} + Tr_B e^{a B g B}`, where
`Tr_P e^{a P g P} = Tr (P e^{a P g P})` (the trace over `ran P` of the exponential of the compression),
and similarly for `B = 1 - P`. -/
theorem trace_exp_pinch {P : Matrix (Fin M) (Fin M) ℂ} (hP : P * P = P)
    (g : Matrix (Fin M) (Fin M) ℂ) (a t : ℂ) :
    (NormedSpace.exp (a • pinch P g - t • P)).trace
      = Complex.exp (-t) * (P * NormedSpace.exp (a • (P * g * P))).trace
        + ((1 - P) * NormedSpace.exp (a • ((1 - P) * g * (1 - P)))).trace := by
  have hPB : P * (1 - P) = 0 := proj_mul_compl hP
  have hBP : (1 - P) * P = 0 := compl_mul_proj hP
  set B := 1 - P with hB
  set X := a • (B * g * B) with hX
  set Y := a • (P * g * P) - t • P with hY
  have hsplit : a • pinch P g - t • P = X + Y := by
    rw [hX, hY]; unfold pinch; rw [smul_add]; abel
  have e1 : B * g * B * P = 0 := by rw [Matrix.mul_assoc, hBP, Matrix.mul_zero]
  have e2 : B * g * B * (P * g * P) = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.zero_mul, Matrix.zero_mul]
  have e3 : P * (B * g * B) = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPB, Matrix.zero_mul, Matrix.zero_mul]
  have e4 : P * g * P * (B * g * B) = 0 := by rw [Matrix.mul_assoc (P * g) P, e3, Matrix.mul_zero]
  have hXY : X * Y = 0 := by
    rw [hX, hY, Matrix.mul_sub, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
      e2, e1]
    simp
  have hYX : Y * X = 0 := by
    rw [hX, hY, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
      e4, e3]
    simp
  have hcomm : Commute X Y := by rw [Commute, SemiconjBy, hXY, hYX]
  rw [hsplit, Matrix.exp_add_of_commute X Y hcomm]
  have hPX : P * NormedSpace.exp X = P := by
    have := mul_exp_of_mul_eq_smul (X := X) (V := P) (c := 0)
      (by rw [hX, Matrix.mul_smul, e3, smul_zero, zero_smul])
    simpa using this
  have hYB : NormedSpace.exp Y * B = B := by
    have hYB0 : Y * B = 0 := by
      rw [hY, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc (P * g) P, hPB,
        Matrix.mul_zero]
      simp
    have := exp_mul_of_mul_eq_smul (X := Y) (V := B) (c := 0) (by rw [hYB0, zero_smul])
    simpa using this
  have hcomm2 : Commute (a • (P * g * P)) ((-t) • P) := by
    have h1 : P * g * P * P = P * g * P := by rw [Matrix.mul_assoc, hP]
    have h2 : P * (P * g * P) = P * g * P := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP]
    rw [Commute, SemiconjBy, Matrix.smul_mul, Matrix.mul_smul, h1, Matrix.smul_mul, Matrix.mul_smul,
      h2, smul_smul, smul_smul, mul_comm]
  have hYsplit : Y = a • (P * g * P) + (-t) • P := by rw [hY, neg_smul, sub_eq_add_neg]
  have hexpY : NormedSpace.exp Y
      = NormedSpace.exp (a • (P * g * P)) * NormedSpace.exp ((-t) • P) := by
    rw [hYsplit, Matrix.exp_add_of_commute _ _ hcomm2]
  have hEP : NormedSpace.exp ((-t) • P) * P = Complex.exp (-t) • P :=
    exp_mul_of_mul_eq_smul (by rw [Matrix.smul_mul, hP])
  have hsum : B + P = 1 := by rw [hB, sub_add_cancel]
  calc (NormedSpace.exp X * NormedSpace.exp Y).trace
      = ((B + P) * (NormedSpace.exp X * NormedSpace.exp Y)).trace := by rw [hsum, Matrix.one_mul]
    _ = (B * NormedSpace.exp X * NormedSpace.exp Y).trace
          + (P * NormedSpace.exp X * NormedSpace.exp Y).trace := by
        rw [Matrix.add_mul, Matrix.trace_add, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = (B * NormedSpace.exp X).trace + (P * NormedSpace.exp Y).trace := by
        rw [Matrix.trace_mul_comm (B * NormedSpace.exp X), ← Matrix.mul_assoc, hYB, hPX]
    _ = (B * NormedSpace.exp X).trace
          + Complex.exp (-t) * (P * NormedSpace.exp (a • (P * g * P))).trace := by
        congr 1
        rw [hexpY, ← Matrix.mul_assoc,
          Matrix.trace_mul_comm (P * NormedSpace.exp (a • (P * g * P))), ← Matrix.mul_assoc, hEP,
          Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    _ = _ := by rw [hX, add_comm]

/-- The paper's `D(a, t) = Tr e^{a g - t P} - e^{-t} Tr_P e^{a P g P} - Tr_B e^{a B g B}`. -/
noncomputable def bmvDPaper (P g : Matrix (Fin M) (Fin M) ℂ) (a t : ℂ) : ℂ :=
  (NormedSpace.exp (a • g - t • P)).trace
    - Complex.exp (-t) * (P * NormedSpace.exp (a • (P * g * P))).trace
    - ((1 - P) * NormedSpace.exp (a • ((1 - P) * g * (1 - P)))).trace

theorem bmvD_eq_paper {P : Matrix (Fin M) (Fin M) ℂ} (hP : P * P = P)
    (g : Matrix (Fin M) (Fin M) ℂ) (a t : ℂ) : bmvD P g a t = bmvDPaper P g a t := by
  rw [bmvD, bmvDPaper, trace_exp_pinch hP g a t]
  ring

/-- **The Radon identity (RI)**, for matrices of size `M`. -/
def Hyp_RI (M : ℕ) : Prop :=
  ∀ (P H : Matrix (Fin M) (Fin M) ℂ) (hP : IsProj P) (hH : H.IsHermitian),
    IntegrableOn (fun τ => imAbsSum (pencilRoots P H τ)) (Set.Ioo 0 1) ∧
    (∫ τ in Set.Ioo (0 : ℝ) 1, imAbsSum (pencilRoots P H τ)) / (2 * π)
      = ∑ i, max (hH.eigenvalues i) 0 - ∑ i, max ((isHermitian_pinch hP.1 hH).eigenvalues i) 0

section Slices

variable {P g : Matrix (Fin M) (Fin M) ℂ}

lemma isHermitian_sub_smul (hP : IsProj P) (hg : g.IsHermitian) (ξ : ℝ) :
    (g - (ξ : ℂ) • P).IsHermitian :=
  hg.sub (hP.1.smul (isSelfAdjoint_ofReal ξ))

/-- The slice function `U_ξ(w) = ∑ (λ_j(ξ) - w)_+ - ∑ (λ^0_j(ξ) - w)_+`, `λ_j(ξ)` the eigenvalues of
`g - ξ P` and `λ^0_j(ξ)` those of `g_d - ξ P` (the pinching of `g - ξ P`). -/
noncomputable def sliceFun (hP : IsProj P) (hg : g.IsHermitian) (ξ : ℝ) (w : ℝ) : ℝ :=
  sliceU (isHermitian_sub_smul hP hg ξ).eigenvalues
    (isHermitian_pinch hP.1 (isHermitian_sub_smul hP hg ξ)).eigenvalues w

lemma eigenvalues_congr {A B : Matrix (Fin M) (Fin M) ℂ} (h : A = B) (hA : A.IsHermitian)
    (hB : B.IsHermitian) : hA.eigenvalues = hB.eigenvalues := by
  subst h; rfl

/-- **(RI) ⟹ Radon slices.**  The Radon projection of `F` in direction `ξ` is `U_ξ`:
`∫_0^1 F(w + ξ τ, τ) dτ = U_ξ(w)`. -/
theorem radon_eq_sliceFun (hRI : Hyp_RI M) (hP : IsProj P) (hg : g.IsHermitian) (ξ w : ℝ) :
    IntegrableOn (fun τ => stripF P g (w + ξ * τ) τ) (Set.Ioo 0 1) ∧
    ∫ τ in Set.Ioo (0 : ℝ) 1, stripF P g (w + ξ * τ) τ = sliceFun hP hg ξ w := by
  set A := g - (ξ : ℂ) • P with hA_def
  have hA : A.IsHermitian := isHermitian_sub_smul hP hg ξ
  set H := A - (w : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ) with hH_def
  have hH : H.IsHermitian := hA.sub (isHermitian_one.smul (isSelfAdjoint_ofReal w))
  obtain ⟨hint, heq⟩ := hRI P H hP hH
  have hpt : Set.EqOn (fun τ => stripF P g (w + ξ * τ) τ)
      (fun τ => imAbsSum (pencilRoots P H τ) / (2 * π)) (Set.Ioo 0 1) := by
    intro τ hτ
    have h0 : τ ≠ 0 := hτ.1.ne'
    have h1 : τ ≠ 1 := hτ.2.ne
    simp only [stripF]
    rw [if_pos (show 0 < τ ∧ τ < 1 from hτ)]
    have e : g - (((w + ξ * τ : ℝ)) : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)
        = H + (ξ : ℂ) • (P - (τ : ℂ) • 1) := by
      rw [hH_def, hA_def]; push_cast; module
    have e' : imAbsSum (pencilRoots P (g - (((w + ξ * τ : ℝ)) : ℂ) • 1) τ)
        = imAbsSum (pencilRoots P H τ) := by
      rw [e, pencilRoots_add_smul hP.2 h0 h1, imAbsSum_map_add_ofReal]
    rw [e']
  refine ⟨IntegrableOn.congr_fun (hint.div_const (2 * π)) hpt.symm measurableSet_Ioo, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioo hpt, integral_div, heq]
  have e1 : ∑ i, max (hH.eigenvalues i) 0 = ∑ i, max (hA.eigenvalues i - w) 0 :=
    sum_eigenvalues_sub_smul_one hA w hH (fun x => max x 0)
  have hpinch : pinch P H = pinch P A - (w : ℂ) • 1 := by
    rw [hH_def, pinch_sub, pinch_smul, pinch_one hP.2]
  have hA0 : (pinch P A).IsHermitian := isHermitian_pinch hP.1 hA
  have hA0w : (pinch P A - (w : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)).IsHermitian :=
    hpinch ▸ isHermitian_pinch hP.1 hH
  have e2 : ∑ i, max ((isHermitian_pinch hP.1 hH).eigenvalues i) 0
      = ∑ i, max (hA0.eigenvalues i - w) 0 := by
    rw [eigenvalues_congr hpinch (isHermitian_pinch hP.1 hH) hA0w]
    exact sum_eigenvalues_sub_smul_one hA0 w hA0w (fun x => max x 0)
  rw [e1, e2]
  rfl

lemma sliceFun_nonneg (hRI : Hyp_RI M) (hP : IsProj P) (hg : g.IsHermitian) (ξ w : ℝ) :
    0 ≤ sliceFun hP hg ξ w := by
  rw [← (radon_eq_sliceFun hRI hP hg ξ w).2]
  exact setIntegral_nonneg measurableSet_Ioo fun τ _ => stripF_nonneg _ _ _ _

/-- **Tonelli step.** `∫∫ e^{a s - a ξ τ} F(s, τ) = ∫ e^{a w} U_ξ(w) dw` (in `[0, ∞]`). -/
theorem lintegral_exp_mul_stripF (hRI : Hyp_RI M) (hP : IsProj P) (hg : g.IsHermitian)
    (a ξ : ℝ) :
    ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (Real.exp (a * q.1 - a * ξ * q.2) * stripF P g q.1 q.2)
      = ∫⁻ w, ENNReal.ofReal (Real.exp (a * w) * sliceFun hP hg ξ w) := by
  have hF : Measurable (Function.uncurry (stripF P g)) := measurable_stripF hP.2 g
  set f : ℝ × ℝ → ENNReal := fun q =>
    ENNReal.ofReal (Real.exp (a * q.1 - a * ξ * q.2) * stripF P g q.1 q.2) with hf_def
  have hfm : Measurable f := by
    apply ENNReal.measurable_ofReal.comp
    exact (by fun_prop : Measurable fun q : ℝ × ℝ => Real.exp (a * q.1 - a * ξ * q.2)).mul hF
  rw [Measure.volume_eq_prod, lintegral_prod_symm' f hfm]
  have hshift : ∀ τ : ℝ, ∫⁻ s, f (s, τ)
      = ∫⁻ w, ENNReal.ofReal (Real.exp (a * w) * stripF P g (w + ξ * τ) τ) := by
    intro τ
    rw [← lintegral_add_right_eq_self (fun s => f (s, τ)) (ξ * τ)]
    congr 1
    funext w
    simp only [hf_def]
    congr 3
    ring
  simp_rw [hshift]
  have hm2 : Measurable (Function.uncurry fun τ w =>
      ENNReal.ofReal (Real.exp (a * w) * stripF P g (w + ξ * τ) τ)) := by
    apply ENNReal.measurable_ofReal.comp
    have h1 : Measurable fun p : ℝ × ℝ => Real.exp (a * p.2) := by fun_prop
    have h2 : Measurable fun p : ℝ × ℝ => stripF P g (p.2 + ξ * p.1) p.1 :=
      hF.comp (by fun_prop : Measurable fun p : ℝ × ℝ => (p.2 + ξ * p.1, p.1))
    exact h1.mul h2
  rw [lintegral_lintegral_swap hm2.aemeasurable]
  congr 1
  funext w
  have hR := radon_eq_sliceFun hRI hP hg ξ w
  have hmeas : Measurable fun τ => ENNReal.ofReal (stripF P g (w + ξ * τ) τ) :=
    ENNReal.measurable_ofReal.comp
      (hF.comp (by fun_prop : Measurable fun τ : ℝ => (w + ξ * τ, τ)))
  have hsupp : Function.support (fun τ => ENNReal.ofReal (stripF P g (w + ξ * τ) τ))
      ⊆ Set.Ioo 0 1 := by
    intro τ hτ
    by_contra h
    apply hτ
    simp [stripF_of_not_mem (show ¬ (0 < τ ∧ τ < 1) from h)]
  calc ∫⁻ τ, ENNReal.ofReal (Real.exp (a * w) * stripF P g (w + ξ * τ) τ)
      = ∫⁻ τ, ENNReal.ofReal (Real.exp (a * w)) * ENNReal.ofReal (stripF P g (w + ξ * τ) τ) := by
        congr 1; funext τ; exact ENNReal.ofReal_mul (Real.exp_pos _).le
    _ = ENNReal.ofReal (Real.exp (a * w)) * ∫⁻ τ, ENNReal.ofReal (stripF P g (w + ξ * τ) τ) :=
        lintegral_const_mul _ hmeas
    _ = ENNReal.ofReal (Real.exp (a * w))
          * ∫⁻ τ in Set.Ioo 0 1, ENNReal.ofReal (stripF P g (w + ξ * τ) τ) := by
        rw [setLIntegral_eq_of_support_subset hsupp]
    _ = ENNReal.ofReal (Real.exp (a * w))
          * ENNReal.ofReal (∫ τ in Set.Ioo 0 1, stripF P g (w + ξ * τ) τ) := by
        rw [ofReal_integral_eq_lintegral_ofReal hR.1
          (ae_of_all _ fun τ => stripF_nonneg _ _ _ _)]
    _ = ENNReal.ofReal (Real.exp (a * w) * sliceFun hP hg ξ w) := by
        rw [hR.2, ← ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- **Real Laplace identity.**  For real `a ≠ 0` and real `ξ`: `e^{a s - a ξ τ} F` is integrable on
`ℝ²` and its integral is `(∑ e^{a λ_j(ξ)} - ∑ e^{a λ^0_j(ξ)}) / a²`. -/
theorem integral_exp_mul_stripF (hRI : Hyp_RI M) (hP : IsProj P) (hg : g.IsHermitian)
    {a : ℝ} (ha : a ≠ 0) (ξ : ℝ) :
    Integrable (fun q : ℝ × ℝ => Real.exp (a * q.1 - a * ξ * q.2) * stripF P g q.1 q.2) ∧
    ∫ q : ℝ × ℝ, Real.exp (a * q.1 - a * ξ * q.2) * stripF P g q.1 q.2
      = (∑ i, Real.exp (a * (isHermitian_sub_smul hP hg ξ).eigenvalues i)
          - ∑ i, Real.exp (a *
            (isHermitian_pinch hP.1 (isHermitian_sub_smul hP hg ξ)).eigenvalues i)) / a ^ 2 := by
  have hA := isHermitian_sub_smul hP hg ξ
  have hA0 := isHermitian_pinch hP.1 hA
  have hsum : ∑ i, hA.eigenvalues i = ∑ i, hA0.eigenvalues i :=
    sum_eigenvalues_eq_of_trace_eq hA hA0 (trace_pinch hP.2 _).symm
  obtain ⟨hSint0, hSval0⟩ := integral_exp_mul_sliceU hA.eigenvalues hA0.eigenvalues hsum ha
  have hSint : Integrable (fun w => Real.exp (a * w) * sliceFun hP hg ξ w) := hSint0
  have hSval : ∫ w, Real.exp (a * w) * sliceFun hP hg ξ w
      = (∑ j, Real.exp (a * hA.eigenvalues j) - ∑ j, Real.exp (a * hA0.eigenvalues j)) / a ^ 2 :=
    hSval0
  have hnn : ∀ q : ℝ × ℝ, 0 ≤ Real.exp (a * q.1 - a * ξ * q.2) * stripF P g q.1 q.2 :=
    fun q => mul_nonneg (Real.exp_pos _).le (stripF_nonneg _ _ _ _)
  have hSnn : ∀ w, 0 ≤ Real.exp (a * w) * sliceFun hP hg ξ w :=
    fun w => mul_nonneg (Real.exp_pos _).le (sliceFun_nonneg hRI hP hg ξ w)
  have hL : ∫⁻ q : ℝ × ℝ, ENNReal.ofReal (Real.exp (a * q.1 - a * ξ * q.2) * stripF P g q.1 q.2)
      = ENNReal.ofReal (∫ w, Real.exp (a * w) * sliceFun hP hg ξ w) := by
    rw [lintegral_exp_mul_stripF hRI hP hg a ξ,
      ofReal_integral_eq_lintegral_ofReal hSint (ae_of_all _ hSnn)]
  have hmeas : Measurable fun q : ℝ × ℝ => Real.exp (a * q.1 - a * ξ * q.2) * stripF P g q.1 q.2 :=
    (by fun_prop : Measurable fun q : ℝ × ℝ => Real.exp (a * q.1 - a * ξ * q.2)).mul
      (measurable_stripF hP.2 g)
  have hint : Integrable (fun q : ℝ × ℝ => Real.exp (a * q.1 - a * ξ * q.2) * stripF P g q.1 q.2) := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hnn), hL]
    exact ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn) hmeas.aestronglyMeasurable, hL,
    ENNReal.toReal_ofReal (integral_nonneg hSnn)]
  exact hSval

/-- `D(a, a ξ)` for real `a`, `ξ` in terms of the eigenvalues of `g - ξ P` and `g_d - ξ P`. -/
lemma bmvD_real (hP : IsProj P) (hg : g.IsHermitian) (a ξ : ℝ) :
    bmvD P g a ((a : ℂ) * ξ)
      = ((∑ i, Real.exp (a * (isHermitian_sub_smul hP hg ξ).eigenvalues i)
          - ∑ i, Real.exp (a *
            (isHermitian_pinch hP.1 (isHermitian_sub_smul hP hg ξ)).eigenvalues i) : ℝ) : ℂ) := by
  have hA := isHermitian_sub_smul hP hg ξ
  have hA0 := isHermitian_pinch hP.1 hA
  have e1 : (a : ℂ) • g - ((a : ℂ) * ξ) • P = (a : ℂ) • (g - (ξ : ℂ) • P) := by
    rw [smul_sub, smul_smul]
  have e2 : (a : ℂ) • pinch P g - ((a : ℂ) * ξ) • P = (a : ℂ) • pinch P (g - (ξ : ℂ) • P) := by
    rw [pinch_sub, pinch_smul, pinch_self hP.2, smul_sub, smul_smul]
  unfold bmvD
  rw [e1, e2, trace_exp_smul_isHermitian hA, trace_exp_smul_isHermitian hA0]
  push_cast
  rfl

end Slices


/-! ### Theorem 1 -/

section Theorem1

variable {P g : Matrix (Fin M) (Fin M) ℂ}

/-- **Theorem 1 for real `a ≠ 0` and real `t`.** -/
theorem bmv2_real (hRI : Hyp_RI M) (hP : IsProj P) (hg : g.IsHermitian) {a : ℝ} (ha : a ≠ 0)
    (t : ℝ) :
    Integrable (fun q : ℝ × ℝ => Real.exp (a * q.1 - t * q.2) * stripF P g q.1 q.2) ∧
    bmvD P g a t
      = ((a ^ 2 * ∫ q : ℝ × ℝ, Real.exp (a * q.1 - t * q.2) * stripF P g q.1 q.2 : ℝ) : ℂ) := by
  have hξ : a * (t / a) = t := by field_simp
  obtain ⟨hint, hval⟩ := integral_exp_mul_stripF hRI hP hg ha (t / a)
  have hfun : (fun q : ℝ × ℝ => Real.exp (a * q.1 - a * (t / a) * q.2) * stripF P g q.1 q.2)
      = fun q => Real.exp (a * q.1 - t * q.2) * stripF P g q.1 q.2 := by
    funext q; rw [hξ]
  rw [hfun] at hint hval
  refine ⟨hint, ?_⟩
  have h := bmvD_real hP hg a (t / a)
  rw [show ((a : ℂ) * ((t / a : ℝ) : ℂ)) = (t : ℂ) by rw [← Complex.ofReal_mul, hξ]] at h
  rw [h, hval]
  congr 1
  field_simp

/-- `e^{b s} F(s, τ)` is integrable on `ℝ²` for every real `b`. -/
lemma integrable_exp_mul_stripF (hRI : Hyp_RI M) (hP : IsProj P) (hg : g.IsHermitian) (b : ℝ) :
    Integrable (fun q : ℝ × ℝ => Real.exp (b * q.1) * stripF P g q.1 q.2) := by
  by_cases hb : b = 0
  · have h1 := (bmv2_real hRI hP hg one_ne_zero 0).1
    have h2 := (bmv2_real hRI hP hg (neg_ne_zero.mpr one_ne_zero) 0).1
    have hmeas : Measurable fun q : ℝ × ℝ => Real.exp (b * q.1) * stripF P g q.1 q.2 :=
      (by fun_prop : Measurable fun q : ℝ × ℝ => Real.exp (b * q.1)).mul (measurable_stripF hP.2 g)
    refine (h1.add h2).mono' hmeas.aestronglyMeasurable (ae_of_all _ fun q => ?_)
    have hF := stripF_nonneg P g q.1 q.2
    have e1 := Real.exp_pos q.1
    have e2 := Real.exp_pos (-q.1)
    have e3 : 1 ≤ Real.exp q.1 + Real.exp (-q.1) := by
      rcases le_total 0 q.1 with h | h
      · linarith [Real.one_le_exp h]
      · linarith [Real.one_le_exp (neg_nonneg.mpr h)]
    rw [hb, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [zero_mul, Real.exp_zero, one_mul, sub_zero, neg_mul, Pi.add_apply]
    nlinarith [mul_nonneg (sub_nonneg.mpr e3) hF]
  · simpa using (bmv2_real hRI hP hg hb 0).1

/-- The Laplace transform `L(a, t) = ∫∫ e^{a s - t τ} F(s, τ) ds dτ` (complex `a`, `t`). -/
noncomputable def laplaceF (P g : Matrix (Fin M) (Fin M) ℂ) (a t : ℂ) : ℂ :=
  ∫ q : ℝ × ℝ, Complex.exp (a * q.1 - t * q.2) * (stripF P g q.1 q.2 : ℂ)

lemma laplaceF_real (a t : ℝ) :
    laplaceF P g a t
      = ((∫ q : ℝ × ℝ, Real.exp (a * q.1 - t * q.2) * stripF P g q.1 q.2 : ℝ) : ℂ) := by
  unfold laplaceF
  rw [← integral_complex_ofReal]
  congr 1
  funext q
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  push_cast
  ring

open scoped Matrix.Norms.Operator in
/-- `t ↦ D(a, t)` is entire. -/
lemma differentiable_bmvD_t (P g : Matrix (Fin M) (Fin M) ℂ) (a : ℂ) :
    Differentiable ℂ (fun t : ℂ => bmvD P g a t) := by
  have htr : Differentiable ℂ (fun X : Matrix (Fin M) (Fin M) ℂ => X.trace) :=
    (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin M) ℂ ℂ)).differentiable
  have hterm : ∀ A : Matrix (Fin M) (Fin M) ℂ,
      Differentiable ℂ (fun t : ℂ => (NormedSpace.exp (A - t • P)).trace) := by
    intro A t
    have hexp : DifferentiableAt ℂ (NormedSpace.exp : Matrix (Fin M) (Fin M) ℂ → _) (A - t • P) :=
      (NormedSpace.exp_analytic (𝕂 := ℂ) (A - t • P)).differentiableAt
    have haff : DifferentiableAt ℂ (fun t : ℂ => A - t • P) t :=
      (differentiableAt_const A).sub (differentiableAt_id.smul_const P)
    exact (htr _).comp t (hexp.comp t haff)
  unfold bmvD
  exact (hterm (a • g)).sub (hterm (a • pinch P g))

/-- `t ↦ L(a, t)` is entire for real `a`. -/
lemma differentiable_laplaceF_t (hRI : Hyp_RI M) (hP : IsProj P) (hg : g.IsHermitian) (a : ℝ) :
    Differentiable ℂ (fun t : ℂ => laplaceF P g a t) := by
  intro t₀
  have hFm : Measurable fun q : ℝ × ℝ => stripF P g q.1 q.2 := measurable_stripF hP.2 g
  have hbd := integrable_exp_mul_stripF hRI hP hg a
  set C : ℝ := Real.exp (|t₀.re| + 1) with hC
  have hmeasF : ∀ t : ℂ, Measurable fun q : ℝ × ℝ =>
      Complex.exp (a * q.1 - t * q.2) * (stripF P g q.1 q.2 : ℂ) := fun t =>
    (by fun_prop : Measurable fun q : ℝ × ℝ => Complex.exp (a * q.1 - t * q.2)).mul
      (Complex.measurable_ofReal.comp hFm)
  have hexpb : ∀ (t : ℂ) (q : ℝ × ℝ), 0 < q.2 → q.2 < 1 →
      ‖Complex.exp (a * q.1 - t * q.2)‖ ≤ Real.exp (|t.re|) * Real.exp (a * q.1) := by
    intro t q h0 h1
    rw [Complex.norm_exp, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
    have : -(t.re * q.2) ≤ |t.re| := by
      have := neg_abs_le t.re
      nlinarith [abs_nonneg t.re]
    linarith
  have hkey := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (t : ℂ) (q : ℝ × ℝ) => Complex.exp (a * q.1 - t * q.2) * (stripF P g q.1 q.2 : ℂ))
    (F' := fun (t : ℂ) (q : ℝ × ℝ) =>
      (-(q.2 : ℂ)) * Complex.exp (a * q.1 - t * q.2) * (stripF P g q.1 q.2 : ℂ))
    (x₀ := t₀) (s := Metric.ball t₀ 1)
    (bound := fun q => C * (Real.exp (a * q.1) * stripF P g q.1 q.2))
    (Metric.ball_mem_nhds t₀ one_pos)
    (Eventually.of_forall fun t => (hmeasF t).aestronglyMeasurable)
    (by
      refine (hbd.const_mul (Real.exp (|t₀.re|))).mono' (hmeasF t₀).aestronglyMeasurable
        (ae_of_all _ fun q => ?_)
      by_cases hq : 0 < q.2 ∧ q.2 < 1
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (stripF_nonneg _ _ _ _), ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hexpb t₀ q hq.1 hq.2) (stripF_nonneg _ _ _ _)
      · rw [stripF_of_not_mem hq]
        simp)
    (by
      refine ((by fun_prop : Measurable fun q : ℝ × ℝ => (-(q.2 : ℂ))
        * Complex.exp (a * q.1 - t₀ * q.2)).mul
        (Complex.measurable_ofReal.comp hFm)).aestronglyMeasurable)
    (ae_of_all _ fun q t ht => by
      by_cases hq : 0 < q.2 ∧ q.2 < 1
      · have hre : |t.re| ≤ |t₀.re| + 1 := by
          have h1 : |t.re - t₀.re| ≤ ‖t - t₀‖ := by
            rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
          have h2 : ‖t - t₀‖ < 1 := by rw [← dist_eq_norm]; exact ht
          have := abs_sub_abs_le_abs_sub t.re t₀.re
          linarith
        rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg (stripF_nonneg _ _ _ _), abs_of_pos hq.1]
        have hb := hexpb t q hq.1 hq.2
        have hC' : Real.exp (|t.re|) ≤ C := Real.exp_le_exp.mpr hre
        have hF := stripF_nonneg P g q.1 q.2
        have hE := Real.exp_pos (a * q.1)
        calc q.2 * ‖Complex.exp (a * q.1 - t * q.2)‖ * stripF P g q.1 q.2
            ≤ 1 * (Real.exp (|t.re|) * Real.exp (a * q.1)) * stripF P g q.1 q.2 := by
              apply mul_le_mul_of_nonneg_right _ hF
              exact mul_le_mul hq.2.le hb (norm_nonneg _) zero_le_one
          _ ≤ C * (Real.exp (a * q.1) * stripF P g q.1 q.2) := by
              rw [one_mul, mul_assoc]
              exact mul_le_mul_of_nonneg_right hC' (by positivity)
      · rw [stripF_of_not_mem hq]
        simp)
    (hbd.const_mul C)
    (ae_of_all _ fun q t _ => by
      have h1 : HasDerivAt (fun t : ℂ => (a : ℂ) * q.1 - t * q.2) (-(1 * (q.2 : ℂ))) t :=
        ((hasDerivAt_id t).mul_const (q.2 : ℂ)).const_sub _
      have h2 := (h1.cexp).mul_const (stripF P g q.1 q.2 : ℂ)
      refine h2.congr_deriv ?_
      ring)
  exact hkey.2.differentiableAt

/-- **Theorem 1 (2BMV) from (RI): real `a`, complex `t`.**
`D(a, t) = a² ∫∫ e^{a s - t τ} F(s, τ) ds dτ` for all real `a` and complex `t`. -/
theorem bmv2_of_RI (hRI : Hyp_RI M) (hP : IsProj P) (hg : g.IsHermitian) (a : ℝ) (t : ℂ) :
    bmvD P g a t = (a : ℂ) ^ 2 * laplaceF P g a t := by
  by_cases ha : a = 0
  · subst ha
    simp [bmvD]
  · have hL := differentiable_bmvD_t P g (a : ℂ)
    have hR : Differentiable ℂ (fun t : ℂ => (a : ℂ) ^ 2 * laplaceF P g a t) :=
      (differentiable_laplaceF_t hRI hP hg a).const_mul _
    have hreal : ∀ t : ℝ, bmvD P g a t = (a : ℂ) ^ 2 * laplaceF P g a t := by
      intro t
      rw [(bmv2_real hRI hP hg ha t).2, laplaceF_real]
      push_cast
      ring
    have hseq : Tendsto (fun n : ℕ => (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
        rw [Complex.ofReal_zero] at h
        exact h
      · refine Eventually.of_forall fun n => ?_
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
        positivity
    have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), bmvD P g a z = (a : ℂ) ^ 2 * laplaceF P g a z :=
      hseq.frequently (Frequently.of_forall fun n => hreal _)
    have := AnalyticOnNhd.eq_of_frequently_eq (fun z _ => hL.analyticAt z)
      (fun z _ => hR.analyticAt z) hfreq
    exact congrFun this t

end Theorem1


/-! ### Extension to complex `a`, and the iterated form -/

section Complex

variable {P g : Matrix (Fin M) (Fin M) ℂ}

/-- `‖e^{a s - t τ}‖ ≤ e^{|Re t|} e^{(Re a) s}` for `0 < τ < 1`. -/
lemma norm_cexp_le {a t : ℂ} {q : ℝ × ℝ} (h0 : 0 < q.2) (h1 : q.2 < 1) :
    ‖Complex.exp (a * q.1 - t * q.2)‖ ≤ Real.exp (|t.re|) * Real.exp (a.re * q.1) := by
  rw [Complex.norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]
  have : -(t.re * q.2) ≤ |t.re| := by
    have := neg_abs_le t.re
    nlinarith [abs_nonneg t.re]
  linarith

/-- The integrand of the Laplace transform is integrable for all complex `a`, `t`. -/
lemma integrable_laplace_integrand (hRI : Hyp_RI M) (hP : IsProj P) (hg : g.IsHermitian)
    (a t : ℂ) :
    Integrable (fun q : ℝ × ℝ => Complex.exp (a * q.1 - t * q.2) * (stripF P g q.1 q.2 : ℂ)) := by
  have hFm : Measurable fun q : ℝ × ℝ => stripF P g q.1 q.2 := measurable_stripF hP.2 g
  have hmeas : Measurable fun q : ℝ × ℝ =>
      Complex.exp (a * q.1 - t * q.2) * (stripF P g q.1 q.2 : ℂ) :=
    (by fun_prop : Measurable fun q : ℝ × ℝ => Complex.exp (a * q.1 - t * q.2)).mul
      (Complex.measurable_ofReal.comp hFm)
  refine ((integrable_exp_mul_stripF hRI hP hg a.re).const_mul (Real.exp (|t.re|))).mono'
    hmeas.aestronglyMeasurable (ae_of_all _ fun q => ?_)
  by_cases hq : 0 < q.2 ∧ q.2 < 1
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (stripF_nonneg _ _ _ _),
      ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (norm_cexp_le hq.1 hq.2) (stripF_nonneg _ _ _ _)
  · rw [stripF_of_not_mem hq]
    simp

/-- `|s| e^{x s} ≤ e^{(c+2) s} + 2 e^{c s} + e^{(c-2) s}` whenever `|x - c| ≤ 1`. -/
lemma abs_mul_exp_le {x c s : ℝ} (hx : |x - c| ≤ 1) :
    |s| * Real.exp (x * s)
      ≤ Real.exp ((c + 2) * s) + 2 * Real.exp (c * s) + Real.exp ((c - 2) * s) := by
  have h1 : |s| ≤ Real.exp s + Real.exp (-s) := by
    rcases le_total 0 s with h | h
    · rw [abs_of_nonneg h]
      linarith [Real.add_one_le_exp s, Real.exp_pos (-s)]
    · rw [abs_of_nonpos h]
      linarith [Real.add_one_le_exp (-s), Real.exp_pos s]
  have h2 : Real.exp (x * s) ≤ Real.exp ((c + 1) * s) + Real.exp ((c - 1) * s) := by
    have hx' := abs_le.mp hx
    rcases le_total 0 s with h | h
    · have : x * s ≤ (c + 1) * s := mul_le_mul_of_nonneg_right (by linarith) h
      linarith [Real.exp_le_exp.mpr this, Real.exp_pos ((c - 1) * s)]
    · have : x * s ≤ (c - 1) * s := mul_le_mul_of_nonpos_right (by linarith) h
      linarith [Real.exp_le_exp.mpr this, Real.exp_pos ((c + 1) * s)]
  calc |s| * Real.exp (x * s)
      ≤ (Real.exp s + Real.exp (-s)) * (Real.exp ((c + 1) * s) + Real.exp ((c - 1) * s)) :=
        mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
    _ = Real.exp ((c + 2) * s) + 2 * Real.exp (c * s) + Real.exp ((c - 2) * s) := by
        simp only [add_mul, mul_add, ← Real.exp_add]
        ring_nf

open scoped Matrix.Norms.Operator in
/-- `a ↦ D(a, t)` is entire. -/
lemma differentiable_bmvD_a (P g : Matrix (Fin M) (Fin M) ℂ) (t : ℂ) :
    Differentiable ℂ (fun a : ℂ => bmvD P g a t) := by
  have htr : Differentiable ℂ (fun X : Matrix (Fin M) (Fin M) ℂ => X.trace) :=
    (LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin M) ℂ ℂ)).differentiable
  have hterm : ∀ A : Matrix (Fin M) (Fin M) ℂ,
      Differentiable ℂ (fun a : ℂ => (NormedSpace.exp (a • A - t • P)).trace) := by
    intro A a
    have hexp : DifferentiableAt ℂ (NormedSpace.exp : Matrix (Fin M) (Fin M) ℂ → _)
        (a • A - t • P) :=
      (NormedSpace.exp_analytic (𝕂 := ℂ) (a • A - t • P)).differentiableAt
    have haff : DifferentiableAt ℂ (fun a : ℂ => a • A - t • P) a :=
      (differentiableAt_id.smul_const A).sub (differentiableAt_const _)
    exact (htr _).comp a (hexp.comp a haff)
  unfold bmvD
  exact (hterm g).sub (hterm (pinch P g))

/-- `a ↦ L(a, t)` is entire. -/
lemma differentiable_laplaceF_a (hRI : Hyp_RI M) (hP : IsProj P) (hg : g.IsHermitian) (t : ℂ) :
    Differentiable ℂ (fun a : ℂ => laplaceF P g a t) := by
  intro a₀
  have hFm : Measurable fun q : ℝ × ℝ => stripF P g q.1 q.2 := measurable_stripF hP.2 g
  set c : ℝ := a₀.re with hc
  set K : ℝ := Real.exp (|t.re|) with hK
  have hmeasF : ∀ a : ℂ, Measurable fun q : ℝ × ℝ =>
      Complex.exp (a * q.1 - t * q.2) * (stripF P g q.1 q.2 : ℂ) := fun a =>
    (by fun_prop : Measurable fun q : ℝ × ℝ => Complex.exp (a * q.1 - t * q.2)).mul
      (Complex.measurable_ofReal.comp hFm)
  have hbd : Integrable fun q : ℝ × ℝ => K * ((Real.exp ((c + 2) * q.1)
      + 2 * Real.exp (c * q.1) + Real.exp ((c - 2) * q.1)) * stripF P g q.1 q.2) := by
    have h1 := integrable_exp_mul_stripF hRI hP hg (c + 2)
    have h2 := integrable_exp_mul_stripF hRI hP hg c
    have h3 := integrable_exp_mul_stripF hRI hP hg (c - 2)
    have := ((h1.add (h2.const_mul 2)).add h3).const_mul K
    refine this.congr (ae_of_all _ fun q => ?_)
    simp only [Pi.add_apply]
    ring
  have hkey := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (a : ℂ) (q : ℝ × ℝ) => Complex.exp (a * q.1 - t * q.2) * (stripF P g q.1 q.2 : ℂ))
    (F' := fun (a : ℂ) (q : ℝ × ℝ) =>
      (q.1 : ℂ) * Complex.exp (a * q.1 - t * q.2) * (stripF P g q.1 q.2 : ℂ))
    (x₀ := a₀) (s := Metric.ball a₀ 1)
    (bound := fun q => K * ((Real.exp ((c + 2) * q.1)
      + 2 * Real.exp (c * q.1) + Real.exp ((c - 2) * q.1)) * stripF P g q.1 q.2))
    (Metric.ball_mem_nhds a₀ one_pos)
    (Eventually.of_forall fun a => (hmeasF a).aestronglyMeasurable)
    (integrable_laplace_integrand hRI hP hg a₀ t)
    (((by fun_prop : Measurable fun q : ℝ × ℝ => (q.1 : ℂ)
        * Complex.exp (a₀ * q.1 - t * q.2)).mul
        (Complex.measurable_ofReal.comp hFm)).aestronglyMeasurable)
    (ae_of_all _ fun q a ha => by
      by_cases hq : 0 < q.2 ∧ q.2 < 1
      · have hre : |a.re - c| ≤ 1 := by
          have h1 : |a.re - a₀.re| ≤ ‖a - a₀‖ := by
            rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
          have h2 : ‖a - a₀‖ < 1 := by rw [← dist_eq_norm]; exact ha
          rw [hc]; linarith
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg (stripF_nonneg _ _ _ _)]
        have hb := norm_cexp_le (a := a) (t := t) hq.1 hq.2
        have hF := stripF_nonneg P g q.1 q.2
        have hm := abs_mul_exp_le (s := q.1) hre
        calc |q.1| * ‖Complex.exp (a * q.1 - t * q.2)‖ * stripF P g q.1 q.2
            ≤ |q.1| * (K * Real.exp (a.re * q.1)) * stripF P g q.1 q.2 := by
              apply mul_le_mul_of_nonneg_right _ hF
              exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
          _ = K * (|q.1| * Real.exp (a.re * q.1)) * stripF P g q.1 q.2 := by ring
          _ ≤ K * ((Real.exp ((c + 2) * q.1) + 2 * Real.exp (c * q.1)
                + Real.exp ((c - 2) * q.1))) * stripF P g q.1 q.2 := by
              apply mul_le_mul_of_nonneg_right _ hF
              exact mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le
          _ = K * ((Real.exp ((c + 2) * q.1) + 2 * Real.exp (c * q.1)
                + Real.exp ((c - 2) * q.1)) * stripF P g q.1 q.2) := by ring
      · rw [stripF_of_not_mem hq]
        simp)
    hbd
    (ae_of_all _ fun q a _ => by
      have h1 : HasDerivAt (fun a : ℂ => a * q.1 - t * q.2) (1 * (q.1 : ℂ)) a :=
        ((hasDerivAt_id a).mul_const (q.1 : ℂ)).sub_const _
      have h2 := (h1.cexp).mul_const (stripF P g q.1 q.2 : ℂ)
      refine h2.congr_deriv ?_
      ring)
  exact hkey.2.differentiableAt

/-- **Theorem 1 (2BMV) from (RI), all `(a, t) ∈ ℂ²`.**
`D(a, t) = a² ∫∫ e^{a s - t τ} F(s, τ) ds dτ`. -/
theorem bmv2_of_RI_complex (hRI : Hyp_RI M) (hP : IsProj P) (hg : g.IsHermitian) (a t : ℂ) :
    bmvD P g a t = a ^ 2 * laplaceF P g a t := by
  have hL := differentiable_bmvD_a P g t
  have hR : Differentiable ℂ (fun a : ℂ => a ^ 2 * laplaceF P g a t) :=
    (differentiable_id.pow 2).mul (differentiable_laplaceF_a hRI hP hg t)
  have hreal : ∀ a : ℝ, bmvD P g a t = (a : ℂ) ^ 2 * laplaceF P g a t :=
    fun a => bmv2_of_RI hRI hP hg a t
  have hseq : Tendsto (fun n : ℕ => (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
      rw [Complex.ofReal_zero] at h
      exact h
    · refine Eventually.of_forall fun n => ?_
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
      positivity
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), bmvD P g z t = z ^ 2 * laplaceF P g z t :=
    hseq.frequently (Frequently.of_forall fun n => hreal _)
  have := AnalyticOnNhd.eq_of_frequently_eq (fun z _ => hL.analyticAt z)
    (fun z _ => hR.analyticAt z) hfreq
  exact congrFun this a

/-- The iterated form `∫∫ e^{a s - t τ} F = ∫_0^1 ∫_ℝ e^{a s - t τ} F(s, τ) ds dτ`. -/
lemma laplaceF_eq_iterated (hRI : Hyp_RI M) (hP : IsProj P) (hg : g.IsHermitian) (a t : ℂ) :
    laplaceF P g a t
      = ∫ τ in (0 : ℝ)..1, ∫ s : ℝ, Complex.exp (a * s - t * τ) * (stripF P g s τ : ℂ) := by
  unfold laplaceF
  have hint := integrable_laplace_integrand hRI hP hg a t
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [integral_prod_symm _ hint, intervalIntegral.integral_of_le zero_le_one]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro τ hτ
  have hτ' : ¬ (0 < τ ∧ τ < 1) := fun h => hτ ⟨h.1, h.2.le⟩
  simp [stripF_of_not_mem hτ']

end Complex


/-! ### Interface for Theorem 2 -/

/-- **Theorem 1 with all the properties of `F` used downstream** (for Theorem 2): `F` is jointly
measurable, nonnegative, vanishes for `τ ∉ (0, 1)` and for `|s| ≥ R`, is bounded by
`C / √(τ (1 - τ))`, `e^{a s - t τ} F` is integrable for all complex `a`, `t`, and
`D(a, t) = a² ∫∫ e^{a s - t τ} F(s, τ) ds dτ` with the paper's `D`. -/
theorem bmv2_package (hRI : Hyp_RI M) {P g : Matrix (Fin M) (Fin M) ℂ} (hP : IsProj P)
    (hg : g.IsHermitian) :
    Measurable (Function.uncurry (stripF P g)) ∧
    (∀ s τ, 0 ≤ stripF P g s τ) ∧
    (∀ s τ, ¬ (0 < τ ∧ τ < 1) → stripF P g s τ = 0) ∧
    (∃ R : ℝ, 0 < R ∧ ∀ s τ : ℝ, R ≤ |s| → stripF P g s τ = 0) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ s τ : ℝ, 0 < τ → τ < 1 → stripF P g s τ ≤ C / √(τ * (1 - τ))) ∧
    (∀ a t : ℂ, Integrable (fun q : ℝ × ℝ =>
      Complex.exp (a * q.1 - t * q.2) * (stripF P g q.1 q.2 : ℂ))) ∧
    (∀ a t : ℂ, bmvDPaper P g a t
      = a ^ 2 * ∫ q : ℝ × ℝ, Complex.exp (a * q.1 - t * q.2) * (stripF P g q.1 q.2 : ℂ)) :=
  ⟨measurable_stripF hP.2 g, stripF_nonneg P g, fun _ _ h => stripF_of_not_mem h,
    stripF_support hP hg, stripF_bound hP hg, integrable_laplace_integrand hRI hP hg,
    fun a t => by rw [← bmvD_eq_paper hP.2 g a t]; exact bmv2_of_RI_complex hRI hP hg a t⟩

end OQP27.StripL3b
