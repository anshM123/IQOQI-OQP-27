import OQP27.StripPencil
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Real slices: the Laplace transform of `U_ξ` (Lemma 3(b), module L3b)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

Proved here (no hypotheses, no `sorry`):
* `trace_exp_smul_isHermitian`: `Tr e^{a A} = ∑_i e^{a λ_i(A)}` for Hermitian `A` and complex `a`;
* `eigenvalues_sub_smul_one`, `sum_eigenvalues_sub_smul_one`: the spectrum of `A - w` is that of `A`
  shifted by `-w`; `trace_pinch`: `Tr H_d = Tr H`;
* `integral_exp_mul_sliceU` (**Lemma 3(b)**, real form): if `∑ λ_j = ∑ μ_j` then
  `U(w) = ∑_j (λ_j - w)_+ - ∑_j (μ_j - w)_+` is continuous with compact support and, for real `a ≠ 0`,
  `∫_ℝ e^{a w} U(w) dw = (∑ e^{a λ_j} - ∑ e^{a μ_j}) / a²`.

No hypotheses remain in this file.
Paper: `iqoqi/programs/oqp27B_all/Q_2bmv/PROOF.md`, Lemma 3; `Q_RI/PROOF.md`, section 4 (ii).
-/

namespace OQP27.StripL3b

open Matrix Polynomial MeasureTheory Filter Topology Real

variable {M : ℕ}

/-! ### Spectral helper lemmas -/

/-- `Tr exp (a A) = ∑ exp (a λ_i)` for Hermitian `A`. -/
lemma trace_exp_smul_isHermitian {A : Matrix (Fin M) (Fin M) ℂ} (hA : A.IsHermitian) (a : ℂ) :
    (NormedSpace.exp (a • A)).trace = ∑ i, Complex.exp (a * hA.eigenvalues i) := by
  set U : Matrix (Fin M) (Fin M) ℂ := (hA.eigenvectorUnitary : Matrix (Fin M) (Fin M) ℂ) with hU
  set D : Matrix (Fin M) (Fin M) ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hD
  have hsU : star U * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hUinv : U⁻¹ = star U := Matrix.inv_eq_left_inv hsU
  have hUunit : IsUnit U :=
    (Matrix.isUnit_iff_isUnit_det U).mpr (Matrix.isUnit_det_of_left_inverse hsU)
  have hA' : a • A = U * (a • D) * U⁻¹ := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, hUinv, Matrix.mul_smul, Matrix.smul_mul]
  rw [hA', Matrix.exp_conj _ _ hUunit, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det U).mp hUunit), Matrix.one_mul, hD,
    ← Matrix.diagonal_smul, Matrix.exp_diagonal, Matrix.trace_diagonal]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  simp

/-- The eigenvalues of `A - w` are those of `A` shifted by `-w` (as multisets). -/
lemma eigenvalues_sub_smul_one {A : Matrix (Fin M) (Fin M) ℂ} (hA : A.IsHermitian) (w : ℝ)
    (hAw : (A - (w : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)).IsHermitian) :
    Multiset.map hAw.eigenvalues Finset.univ.val
      = Multiset.map (fun i => hA.eigenvalues i - w) Finset.univ.val := by
  have h2 : (A - (w : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)).charpoly.roots
      = (A.charpoly.roots).map (fun x => x - (w : ℂ)) := by
    have e : A - (w : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ) = A - Matrix.scalar (Fin M) (w : ℂ) := by
      rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    rw [e, Matrix.charpoly_sub_scalar]
    rw [show (X + C (w : ℂ) : ℂ[X]) = C 1 * X + C (w : ℂ) by simp,
      Polynomial.roots_comp_C_mul_X_add_C _ 1 _ isUnit_one]
    congr 1
    funext x
    simp
  rw [hAw.roots_charpoly_eq_eigenvalues, hA.roots_charpoly_eq_eigenvalues, Multiset.map_map] at h2
  apply Multiset.map_injective Complex.ofReal_injective
  rw [Multiset.map_map, Multiset.map_map]
  refine h2.trans ?_
  congr 1
  funext i
  simp

lemma sum_eigenvalues_sub_smul_one {A : Matrix (Fin M) (Fin M) ℂ} (hA : A.IsHermitian) (w : ℝ)
    (hAw : (A - (w : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)).IsHermitian) (f : ℝ → ℝ) :
    ∑ i, f (hAw.eigenvalues i) = ∑ i, f (hA.eigenvalues i - w) := by
  have h := congrArg (fun m => (m.map f).sum) (eigenvalues_sub_smul_one hA w hAw)
  simpa only [Multiset.map_map, Function.comp_def, ← Finset.sum_eq_multiset_sum] using h

lemma trace_pinch {P : Matrix (Fin M) (Fin M) ℂ} (hP : P * P = P) (H : Matrix (Fin M) (Fin M) ℂ) :
    (pinch P H).trace = H.trace := by
  have hBB : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, proj_mul_compl hP, sub_zero]
  have t1 : ((1 - P) * H * (1 - P)).trace = ((1 - P) * H).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hBB]
  have t2 : (P * H * P).trace = (P * H).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hP]
  unfold pinch
  rw [Matrix.trace_add, t1, t2, ← Matrix.trace_add, ← Matrix.add_mul, sub_add_cancel,
    Matrix.one_mul]

lemma sum_eigenvalues_eq_of_trace_eq {A B : Matrix (Fin M) (Fin M) ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (h : A.trace = B.trace) :
    ∑ i, hA.eigenvalues i = ∑ i, hB.eigenvalues i := by
  rw [hA.trace_eq_sum_eigenvalues, hB.trace_eq_sum_eigenvalues] at h
  exact_mod_cast h

/-! ### The slice function and its Laplace transform (Lemma 3(b)) -/

/-- `U(w) = ∑_j (λ_j - w)_+ - ∑_j (μ_j - w)_+`. -/
noncomputable def sliceU {ι : Type*} [Fintype ι] (lam mu : ι → ℝ) (w : ℝ) : ℝ :=
  ∑ j, max (lam j - w) 0 - ∑ j, max (mu j - w) 0

lemma continuous_sliceU {ι : Type*} [Fintype ι] (lam mu : ι → ℝ) : Continuous (sliceU lam mu) := by
  unfold sliceU
  fun_prop

/-- `∫_{-R}^{R} e^{a w} (c - w)_+ dw` for `|c| ≤ R`. -/
lemma integral_exp_mul_posPart {a R c : ℝ} (ha : a ≠ 0) (hc1 : -R ≤ c) (hc2 : c ≤ R) :
    ∫ w in (-R)..R, Real.exp (a * w) * max (c - w) 0
      = Real.exp (a * c) / a ^ 2 - Real.exp (a * (-R)) * (c + R) / a
        - Real.exp (a * (-R)) / a ^ 2 := by
  have hint : ∀ u v : ℝ, IntervalIntegrable (fun w => Real.exp (a * w) * max (c - w) 0) volume u v :=
    fun u v => (by fun_prop : Continuous fun w => Real.exp (a * w) * max (c - w) 0).intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint (-R) c) (hint c R)]
  have h2 : ∫ w in c..R, Real.exp (a * w) * max (c - w) 0 = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro w hw
      rw [Set.uIcc_of_le hc2] at hw
      simp [max_eq_right (by linarith [hw.1] : c - w ≤ 0)]
  have h1 : ∫ w in (-R)..c, Real.exp (a * w) * max (c - w) 0
      = ∫ w in (-R)..c, Real.exp (a * w) * (c - w) := by
    apply intervalIntegral.integral_congr
    intro w hw
    rw [Set.uIcc_of_le hc1] at hw
    simp [max_eq_left (by linarith [hw.2] : 0 ≤ c - w)]
  rw [h2, add_zero, h1]
  have hderiv : ∀ w : ℝ, HasDerivAt
      (fun w => Real.exp (a * w) * (c - w) / a + Real.exp (a * w) / a ^ 2)
      (Real.exp (a * w) * (c - w)) w := by
    intro w
    have he : HasDerivAt (fun w => Real.exp (a * w)) (Real.exp (a * w) * a) w := by
      simpa using ((hasDerivAt_id' w).const_mul a).exp
    have h3 := ((he.mul ((hasDerivAt_id' w).const_sub c)).div_const a).add
      (he.div_const (a ^ 2))
    refine h3.congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun w _ => hderiv w)
    ((by fun_prop : Continuous fun w => Real.exp (a * w) * (c - w)).intervalIntegrable _ _)]
  field_simp
  ring

/-- **Lemma 3(b), real form.**  If `∑ λ_j = ∑ μ_j`, then `e^{a w} U(w)` is integrable and
`∫ e^{a w} U(w) dw = (∑ e^{a λ_j} - ∑ e^{a μ_j}) / a²` for real `a ≠ 0`. -/
theorem integral_exp_mul_sliceU {ι : Type*} [Fintype ι] (lam mu : ι → ℝ)
    (hsum : ∑ j, lam j = ∑ j, mu j) {a : ℝ} (ha : a ≠ 0) :
    Integrable (fun w => Real.exp (a * w) * sliceU lam mu w) ∧
    ∫ w, Real.exp (a * w) * sliceU lam mu w
      = (∑ j, Real.exp (a * lam j) - ∑ j, Real.exp (a * mu j)) / a ^ 2 := by
  set R : ℝ := 1 + ∑ j, (|lam j| + |mu j|) with hR
  have hlam : ∀ j, |lam j| ≤ R := fun j => by
    have := Finset.single_le_sum (f := fun j => |lam j| + |mu j|)
      (fun j _ => by positivity) (Finset.mem_univ j)
    linarith [abs_nonneg (mu j)]
  have hmu : ∀ j, |mu j| ≤ R := fun j => by
    have := Finset.single_le_sum (f := fun j => |lam j| + |mu j|)
      (fun j _ => by positivity) (Finset.mem_univ j)
    linarith [abs_nonneg (lam j)]
  have hU0 : ∀ w, w ∉ Set.Ioc (-R) R → sliceU lam mu w = 0 := by
    intro w hw
    simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hw
    unfold sliceU
    rcases hw with hw | hw
    · have e1 : ∀ j, max (lam j - w) 0 = lam j - w := fun j =>
        max_eq_left (by linarith [neg_abs_le (lam j), hlam j])
      have e2 : ∀ j, max (mu j - w) 0 = mu j - w := fun j =>
        max_eq_left (by linarith [neg_abs_le (mu j), hmu j])
      simp only [e1, e2, Finset.sum_sub_distrib, hsum, sub_self]
    · have e1 : ∀ j, max (lam j - w) 0 = 0 := fun j =>
        max_eq_right (by linarith [le_abs_self (lam j), hlam j])
      have e2 : ∀ j, max (mu j - w) 0 = 0 := fun j =>
        max_eq_right (by linarith [le_abs_self (mu j), hmu j])
      simp [e1, e2]
  have hcont : Continuous fun w => Real.exp (a * w) * sliceU lam mu w :=
    (by fun_prop : Continuous fun w => Real.exp (a * w)).mul (continuous_sliceU lam mu)
  have hsupp : HasCompactSupport fun w => Real.exp (a * w) * sliceU lam mu w := by
    apply HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R))
    intro w hw
    have : w ∉ Set.Ioc (-R) R := fun h => hw ⟨h.1.le, h.2⟩
    simp [hU0 w this]
  refine ⟨hcont.integrable_of_hasCompactSupport hsupp, ?_⟩
  have hRpos : -R ≤ R := by
    have : 0 ≤ ∑ j, (|lam j| + |mu j|) := Finset.sum_nonneg fun j _ => by positivity
    linarith
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Set.Ioc (-R) R) (fun w hw => by simp [hU0 w hw]),
    ← intervalIntegral.integral_of_le hRpos]
  have hterm : ∀ (c : ℝ), IntervalIntegrable (fun w => Real.exp (a * w) * max (c - w) 0)
      volume (-R) R := fun c =>
    (by fun_prop : Continuous fun w => Real.exp (a * w) * max (c - w) 0).intervalIntegrable _ _
  have hexpand : (fun w => Real.exp (a * w) * sliceU lam mu w)
      = fun w => ∑ j, Real.exp (a * w) * max (lam j - w) 0
          - ∑ j, Real.exp (a * w) * max (mu j - w) 0 := by
    funext w
    simp only [sliceU, mul_sub, Finset.mul_sum]
  rw [hexpand, intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun w => ∑ j, Real.exp (a * w) * max (lam j - w) 0).intervalIntegrable
        _ _)
      ((by fun_prop : Continuous fun w => ∑ j, Real.exp (a * w) * max (mu j - w) 0).intervalIntegrable
        _ _),
    intervalIntegral.integral_finsetSum (fun j _ => hterm (lam j)),
    intervalIntegral.integral_finsetSum (fun j _ => hterm (mu j))]
  have hl : ∀ j, ∫ w in (-R)..R, Real.exp (a * w) * max (lam j - w) 0
      = Real.exp (a * lam j) / a ^ 2 - Real.exp (a * (-R)) * (lam j + R) / a
        - Real.exp (a * (-R)) / a ^ 2 := fun j =>
    integral_exp_mul_posPart ha (by linarith [neg_abs_le (lam j), hlam j])
      (by linarith [le_abs_self (lam j), hlam j])
  have hm : ∀ j, ∫ w in (-R)..R, Real.exp (a * w) * max (mu j - w) 0
      = Real.exp (a * mu j) / a ^ 2 - Real.exp (a * (-R)) * (mu j + R) / a
        - Real.exp (a * (-R)) / a ^ 2 := fun j =>
    integral_exp_mul_posPart ha (by linarith [neg_abs_le (mu j), hmu j])
      (by linarith [le_abs_self (mu j), hmu j])
  simp only [hl, hm]
  rw [← Finset.sum_sub_distrib]
  have hpt : ∀ j, (Real.exp (a * lam j) / a ^ 2 - Real.exp (a * (-R)) * (lam j + R) / a
      - Real.exp (a * (-R)) / a ^ 2) - (Real.exp (a * mu j) / a ^ 2
      - Real.exp (a * (-R)) * (mu j + R) / a - Real.exp (a * (-R)) / a ^ 2)
      = (Real.exp (a * lam j) - Real.exp (a * mu j)) / a ^ 2
        - (Real.exp (a * (-R)) / a) * (lam j - mu j) := by
    intro j; ring
  simp only [hpt]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, hsum, sub_self, mul_zero, sub_zero]

end OQP27.StripL3b
