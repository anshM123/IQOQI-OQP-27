import OQP27.StripBounds
import OQP27.StripRIContour
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Polynomial

/-!
# The pencil polynomial with a complex shift (module L3b, proof of RI)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

For `A` Hermitian, `P` an orthogonal projection, `τ ∈ ℝ` and `c ∈ ℂ`, `penPoly P A τ c` is the polynomial
`p(z) = det(A + c - z (P - τ))`; for `0 < τ < 1` its roots are the pencil roots of `A + c`
(`roots_penPoly`).
Main results:
* `penPoly_eq_lagrange`, `penPolyDt_eq`: the Lagrange representation of `p` through the node values
  `χ_{jP - A}(c + jτ)`, and the transport identity `∂_τ p = z ∂_c p` (from `p(z) = f(z, c + zτ)`);
* `root_im_identity`, `pencilRoot_im_bounds` (**Lemma A(a)**): `Im c |v|² = Im y ⟨v, (P - τ) v⟩`; for
  `Im c > 0` no root is real, roots in `ℂ₊` have `(1 - τ) Im y ≥ Im c`, roots in `ℂ₋` have
  `τ Im y ≤ -Im c`;
* `pencilRoot_norm_bound` (**Lemma B(ii)**): `|y|² τ (1 - τ) ≤ ‖A + c‖_F²` for roots in `ℂ₊` when
  `τ ≤ 1/2` and for roots in `ℂ₋` when `τ ≥ 1/2`;
* `upperRoots`, `lowerRoots`, `upper_add_lower`: the roots in `ℂ₊` and in `ℂ₋`.

Hypotheses: none.
Paper: `iqoqi/programs/oqp27B_all/Q_RI/PROOF.md`, section 1 (Lemma A(a), Lemma B(ii), `p_τ = y p_c` in
Lemma C).
-/

namespace OQP27.StripL3b

open Matrix Polynomial Complex Metric Filter Topology Set Real

variable {M : ℕ}

/-- The pencil polynomial `z ↦ det (A + c - z (P - τ))`. -/
noncomputable def penPoly (P A : Matrix (Fin M) (Fin M) ℂ) (τ : ℝ) (c : ℂ) : ℂ[X] :=
  ((X : ℂ[X]) • (-(P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))).map C
    + (A + c • (1 : Matrix (Fin M) (Fin M) ℂ)).map C).det

section PenPoly

variable (P A : Matrix (Fin M) (Fin M) ℂ) (τ : ℝ) (c : ℂ)

lemma natDegree_penPoly_le : (penPoly P A τ c).natDegree ≤ M := by
  have := natDegree_det_X_add_C_le (-(P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)))
    (A + c • (1 : Matrix (Fin M) (Fin M) ℂ))
  simpa [penPoly] using this

lemma eval_penPoly (z : ℂ) :
    (penPoly P A τ c).eval z = (A + c • 1 - z • (P - (τ : ℂ) • 1)).det := by
  unfold penPoly
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.neg_apply, Matrix.sub_apply, smul_eq_mul, coe_evalRingHom, eval_add, eval_mul, eval_X,
    eval_C]
  ring

/-- `det (A + c - z (P - τ)) = χ_{z P - A}(c + z τ)`. -/
lemma eval_penPoly' (z : ℂ) :
    (penPoly P A τ c).eval z
      = (Matrix.charpoly (z • P - A)).eval (c + z * τ) := by
  rw [eval_penPoly, Matrix.eval_charpoly, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
  congr 1
  rw [smul_sub, smul_smul, mul_comm z]
  rw [add_smul]
  abel

end PenPoly

lemma penPoly_eq_det_form {P A : Matrix (Fin M) (Fin M) ℂ} {τ : ℝ} {c : ℂ} :
    penPoly P A τ c
      = (((A + c • 1).map Polynomial.C) - (Polynomial.X : ℂ[X])
          • ((P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)).map Polynomial.C)).det := by
  unfold penPoly
  congr 1
  have hneg : (-(P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))).map Polynomial.C
      = -((P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)).map Polynomial.C) := by
    ext i j; simp
  rw [hneg, smul_neg]
  abel

/-- The roots of the pencil polynomial are the pencil roots of `A + c`. -/
lemma roots_penPoly {P : Matrix (Fin M) (Fin M) ℂ} (hP : P * P = P) (A : Matrix (Fin M) (Fin M) ℂ)
    {τ : ℝ} (h0 : τ ≠ 0) (h1 : τ ≠ 1) (c : ℂ) :
    (penPoly P A τ c).roots = pencilRoots P (A + c • 1) τ := by
  rw [penPoly_eq_det_form, pencilRoots_eq_roots_det hP h0 h1]

lemma penPoly_ne_zero {P : Matrix (Fin M) (Fin M) ℂ} (hP : P * P = P) (A : Matrix (Fin M) (Fin M) ℂ)
    {τ : ℝ} (h0 : τ ≠ 0) (h1 : τ ≠ 1) (c : ℂ) : penPoly P A τ c ≠ 0 := by
  intro h
  have hd : (-(P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))).det ≠ 0 := by
    rw [Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (isUnit_det_P_sub hP h0 h1).ne_zero
  have hpoly : (((P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹ * (A + c • 1)).charpoly) = 0 := by
    apply Polynomial.funext
    intro z
    have hz := det_pencil (H := A + c • 1) hP h0 h1 z
    have hz0 : (A + c • 1 - z • (P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))).det = 0 := by
      rw [← eval_penPoly, h, eval_zero]
    rw [hz0] at hz
    rw [eval_zero]
    exact (mul_eq_zero.mp hz.symm).resolve_left hd
  exact (Matrix.charpoly_monic _).ne_zero hpoly

/-! ### Lagrange representation and the parameter derivatives -/

/-- Lagrange nodes `0, 1, …, M`. -/
def lagNodes (M : ℕ) : Finset ℕ := Finset.range (M + 1)

/-- The Lagrange basis polynomials at the nodes `0, 1, …, M`. -/
noncomputable def lagBasis (M : ℕ) (j : ℕ) : ℂ[X] :=
  Lagrange.basis (lagNodes M) (fun n : ℕ => (n : ℂ)) j

/-- The value of the pencil polynomial at the node `j`. -/
noncomputable def penVal (P A : Matrix (Fin M) (Fin M) ℂ) (j : ℕ) (τ : ℝ) (c : ℂ) : ℂ :=
  (Matrix.charpoly ((j : ℂ) • P - A)).eval (c + j * τ)

/-- Its derivative in `c` (and, up to the factor `j`, in `τ`). -/
noncomputable def penValD (P A : Matrix (Fin M) (Fin M) ℂ) (j : ℕ) (τ : ℝ) (c : ℂ) : ℂ :=
  (Matrix.charpoly ((j : ℂ) • P - A)).derivative.eval (c + j * τ)

lemma penPoly_eq_lagrange (P A : Matrix (Fin M) (Fin M) ℂ) (τ : ℝ) (c : ℂ) :
    penPoly P A τ c = ∑ j ∈ lagNodes M, C (penVal P A j τ c) * lagBasis M j := by
  have hinj : Set.InjOn (fun n : ℕ => (n : ℂ)) (lagNodes M : Set ℕ) :=
    fun a _ b _ h => Nat.cast_injective h
  have hdeg : (penPoly P A τ c).degree < (lagNodes M).card := by
    rw [lagNodes, Finset.card_range]
    calc (penPoly P A τ c).degree ≤ ((penPoly P A τ c).natDegree : WithBot ℕ) := degree_le_natDegree
      _ < ((M + 1 : ℕ) : WithBot ℕ) := by
        exact_mod_cast Nat.lt_succ_of_le (natDegree_penPoly_le P A τ c)
  rw [Lagrange.eq_interpolate hinj hdeg, Lagrange.interpolate_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_penPoly', penVal, lagBasis]

/-- The `c`-derivative polynomial `D_c f`. -/
noncomputable def penPolyDc (P A : Matrix (Fin M) (Fin M) ℂ) (τ : ℝ) (c : ℂ) : ℂ[X] :=
  ∑ j ∈ lagNodes M, C (penValD P A j τ c) * lagBasis M j

/-- The `τ`-derivative polynomial `D_τ f`. -/
noncomputable def penPolyDt (P A : Matrix (Fin M) (Fin M) ℂ) (τ : ℝ) (c : ℂ) : ℂ[X] :=
  ∑ j ∈ lagNodes M, C ((j : ℂ) * penValD P A j τ c) * lagBasis M j

lemma hasDerivAt_penVal_c (P A : Matrix (Fin M) (Fin M) ℂ) (j : ℕ) (τ : ℝ) (c : ℂ) :
    HasDerivAt (fun c => penVal P A j τ c) (penValD P A j τ c) c := by
  unfold penVal penValD
  exact HasDerivAt.comp_add_const c ((j : ℂ) * τ)
    ((Matrix.charpoly ((j : ℂ) • P - A)).hasDerivAt (c + j * τ))

/-- Derivative of `τ ↦ Q(c + w τ)` for a polynomial `Q` (real variable `τ`). -/
lemma hasDerivAt_eval_affine_real (Q : ℂ[X]) (c w : ℂ) (τ : ℝ) :
    HasDerivAt (fun τ : ℝ => Q.eval (c + w * τ)) (w * Q.derivative.eval (c + w * τ)) τ := by
  have h1 : HasDerivAt (fun x : ℂ => c + w * x) w (τ : ℂ) := by
    simpa using ((hasDerivAt_id (τ : ℂ)).const_mul w).const_add c
  have h2 : HasDerivAt ((fun y => Q.eval y) ∘ fun x : ℂ => c + w * x)
      (Q.derivative.eval (c + w * τ) * w) (τ : ℂ) :=
    HasDerivAt.comp (τ : ℂ) (Q.hasDerivAt (c + w * τ)) h1
  rw [mul_comm]
  exact h2.comp_ofReal

lemma hasDerivAt_penVal_t (P A : Matrix (Fin M) (Fin M) ℂ) (j : ℕ) (τ : ℝ) (c : ℂ) :
    HasDerivAt (fun τ : ℝ => penVal P A j τ c) ((j : ℂ) * penValD P A j τ c) τ := by
  unfold penVal penValD
  exact hasDerivAt_eval_affine_real _ c (j : ℂ) τ

/-- Generic differentiation of `x ↦ (∑_j C (v_j x) * L_j).eval z`. -/
lemma hasDerivAt_lagrange_eval {𝕜 : Type*} [RCLike 𝕜] [NormedAlgebra 𝕜 ℂ]
    (v v' : ℕ → 𝕜 → ℂ) (x : 𝕜) (hv : ∀ j, HasDerivAt (v j) (v' j x) x) (Q : ℕ → ℂ[X]) (z : ℂ) :
    HasDerivAt (fun x => (∑ j ∈ lagNodes M, C (v j x) * Q j).eval z)
      ((∑ j ∈ lagNodes M, C (v' j x) * Q j).eval z) x := by
  simp only [eval_finsetSum, eval_mul, eval_C]
  exact HasDerivAt.fun_sum fun j _ => (hv j).mul_const _

lemma hasDerivAt_penPoly_c (P A : Matrix (Fin M) (Fin M) ℂ) (τ : ℝ) (c z : ℂ) :
    HasDerivAt (fun c => (penPoly P A τ c).eval z) ((penPolyDc P A τ c).eval z) c := by
  simp only [penPoly_eq_lagrange P A τ, penPolyDc]
  exact hasDerivAt_lagrange_eval (M := M) (fun j c => penVal P A j τ c)
    (fun j c => penValD P A j τ c) c (fun j => hasDerivAt_penVal_c P A j τ c) _ z

lemma hasDerivAt_penPoly_c' (P A : Matrix (Fin M) (Fin M) ℂ) (τ : ℝ) (c z : ℂ) :
    HasDerivAt (fun c => (penPoly P A τ c).derivative.eval z)
      ((penPolyDc P A τ c).derivative.eval z) c := by
  simp only [penPoly_eq_lagrange P A τ, penPolyDc, derivative_sum, derivative_mul, derivative_C,
    zero_mul, zero_add]
  exact hasDerivAt_lagrange_eval (M := M) (fun j c => penVal P A j τ c)
    (fun j c => penValD P A j τ c) c (fun j => hasDerivAt_penVal_c P A j τ c) _ z

lemma hasDerivAt_penPoly_t (P A : Matrix (Fin M) (Fin M) ℂ) (τ : ℝ) (c z : ℂ) :
    HasDerivAt (fun τ : ℝ => (penPoly P A τ c).eval z) ((penPolyDt P A τ c).eval z) τ := by
  simp only [penPoly_eq_lagrange P A _ c, penPolyDt]
  exact hasDerivAt_lagrange_eval (M := M) (𝕜 := ℝ) (fun j τ => penVal P A j τ c)
    (fun j τ => (j : ℂ) * penValD P A j τ c) τ (fun j => hasDerivAt_penVal_t P A j τ c) _ z

lemma hasDerivAt_penPoly_t' (P A : Matrix (Fin M) (Fin M) ℂ) (τ : ℝ) (c z : ℂ) :
    HasDerivAt (fun τ : ℝ => (penPoly P A τ c).derivative.eval z)
      ((penPolyDt P A τ c).derivative.eval z) τ := by
  simp only [penPoly_eq_lagrange P A _ c, penPolyDt, derivative_sum, derivative_mul, derivative_C,
    zero_mul, zero_add]
  exact hasDerivAt_lagrange_eval (M := M) (𝕜 := ℝ) (fun j τ => penVal P A j τ c)
    (fun j τ => (j : ℂ) * penValD P A j τ c) τ (fun j => hasDerivAt_penVal_t P A j τ c) _ z

/-- **The transport identity** `∂_τ f = z ∂_c f` (from `f(z; τ, c) = Q(z, c + z τ)`). -/
lemma penPolyDt_eq (P A : Matrix (Fin M) (Fin M) ℂ) (τ : ℝ) (c : ℂ) :
    penPolyDt P A τ c = X * penPolyDc P A τ c := by
  apply Polynomial.funext
  intro z
  -- both sides are derivatives of `τ ↦ f(z; τ, c)` along the two parametrisations
  have h1 := hasDerivAt_penPoly_t P A τ c z
  have h2 : HasDerivAt (fun τ : ℝ => (penPoly P A τ c).eval z)
      (z * (Matrix.charpoly (z • P - A)).derivative.eval (c + z * τ)) τ := by
    simp only [eval_penPoly']
    exact hasDerivAt_eval_affine_real _ c z τ
  have h3 := hasDerivAt_penPoly_c P A τ c z
  have h4 : HasDerivAt (fun c => (penPoly P A τ c).eval z)
      ((Matrix.charpoly (z • P - A)).derivative.eval (c + z * τ)) c := by
    simp only [eval_penPoly']
    exact HasDerivAt.comp_add_const c (z * (τ : ℂ))
      ((Matrix.charpoly (z • P - A)).hasDerivAt (c + z * τ))
  rw [eval_mul, eval_X, h1.unique h2, h3.unique h4]


/-! ### Root locations for a complex shift `c` with `Im c > 0` (Lemmas A, B of Q_RI) -/

section Locations

variable {P A : Matrix (Fin M) (Fin M) ℂ}

/-- `|(P - τ) v|² = (1 - 2τ) ⟨v, (P - τ) v⟩ + τ (1 - τ) |v|²`. -/
lemma dot_P_sub_mulVec_gen (hP : IsProj P) (τ : ℝ) (v : Fin M → ℂ) :
    star ((P - (τ : ℂ) • 1) *ᵥ v) ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)
      = (1 - 2 * (τ : ℂ)) * (star v ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v))
        + ((τ : ℂ) * (1 - τ)) * (star v ⬝ᵥ v) := by
  have hQ := isHermitian_P_sub hP.1 τ
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hQ.eq, Matrix.mulVec_mulVec,
    P_sub_mul_self hP.2, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]

lemma re_dot_proj_nonneg (hP : IsProj P) (v : Fin M → ℂ) : 0 ≤ (star v ⬝ᵥ (P *ᵥ v)).re := by
  have h : star v ⬝ᵥ (P *ᵥ v) = star (P *ᵥ v) ⬝ᵥ (P *ᵥ v) := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hP.1.eq, Matrix.mulVec_mulVec, hP.2]
  rw [h, re_star_dotProduct_self]
  positivity

lemma re_dot_compl_nonneg (hP : IsProj P) (v : Fin M → ℂ) :
    0 ≤ (star v ⬝ᵥ ((1 - P) *ᵥ v)).re := by
  have hB : IsProj (1 - P) := by
    refine ⟨isHermitian_one.sub hP.1, ?_⟩
    rw [Matrix.sub_mul, Matrix.one_mul, proj_mul_compl hP.2, sub_zero]
  exact re_dot_proj_nonneg hB v

/-- The basic identity for a root `y` with eigenvector `v`: `Im c |v|² = Im y · ⟨v, (P - τ) v⟩`, and
`⟨v, (P - τ) v⟩` is real with `-τ |v|² ≤ ⟨v, (P - τ) v⟩ ≤ (1 - τ) |v|²`. -/
lemma root_im_identity (hP : IsProj P) (hA : A.IsHermitian) (τ : ℝ) (c : ℂ) {y : ℂ}
    {v : Fin M → ℂ} (hv : (A + c • 1) *ᵥ v = y • ((P - (τ : ℂ) • 1) *ᵥ v)) :
    c.im * (star v ⬝ᵥ v).re = y.im * (star v ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)).re ∧
    (star v ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)).im = 0 ∧
    -τ * (star v ⬝ᵥ v).re ≤ (star v ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)).re ∧
    (star v ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)).re ≤ (1 - τ) * (star v ⬝ᵥ v).re := by
  have hQim : (star v ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)).im = 0 := by
    simpa using (isHermitian_P_sub hP.1 τ).im_star_dotProduct_mulVec_self v
  have hAim : (star v ⬝ᵥ (A *ᵥ v)).im = 0 := by
    simpa using hA.im_star_dotProduct_mulVec_self v
  have hvv : (star v ⬝ᵥ v).im = 0 := by
    simpa using (isHermitian_one (n := Fin M) (α := ℂ)).im_star_dotProduct_mulVec_self v
  have hlhs : star v ⬝ᵥ ((A + c • 1) *ᵥ v) = star v ⬝ᵥ (A *ᵥ v) + c * (star v ⬝ᵥ v) := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add, dotProduct_smul,
      smul_eq_mul]
  have hrhs : star v ⬝ᵥ (y • ((P - (τ : ℂ) • 1) *ᵥ v))
      = y * (star v ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)) := by
    rw [dotProduct_smul, smul_eq_mul]
  have heq := congrArg Complex.im (hlhs.symm.trans ((congrArg (star v ⬝ᵥ ·) hv).trans hrhs))
  simp only [Complex.add_im, Complex.mul_im, hAim, hvv, hQim, mul_zero, zero_add] at heq
  -- the bounds on `⟨v, (P - τ) v⟩`
  have hsplit : star v ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)
      = star v ⬝ᵥ (P *ᵥ v) - (τ : ℂ) * (star v ⬝ᵥ v) := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub, dotProduct_smul,
      smul_eq_mul]
  have hPB : star v ⬝ᵥ v = star v ⬝ᵥ (P *ᵥ v) + star v ⬝ᵥ ((1 - P) *ᵥ v) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]; ring
  have hP0 := re_dot_proj_nonneg hP v
  have hB0 := re_dot_compl_nonneg hP v
  have hre := congrArg Complex.re hPB
  simp only [Complex.add_re] at hre
  refine ⟨heq, hQim, ?_, ?_⟩
  · rw [hsplit]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hvv, mul_zero,
      sub_zero]
    nlinarith
  · rw [hsplit]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hvv, mul_zero,
      sub_zero]
    nlinarith

/-- **Lemma A(a)** (Q_RI).  For `Im c > 0` no pencil root is real; roots in `ℂ₊` satisfy
`(1 - τ) Im y ≥ Im c` and roots in `ℂ₋` satisfy `τ Im y ≤ -Im c`. -/
lemma pencilRoot_im_bounds (hP : IsProj P) (hA : A.IsHermitian) {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1)
    {c : ℂ} (hc : 0 < c.im) {y : ℂ} (hy : y ∈ pencilRoots P (A + c • 1) τ) :
    y.im ≠ 0 ∧ (0 < y.im → c.im ≤ (1 - τ) * y.im) ∧ (y.im < 0 → τ * y.im ≤ -c.im) := by
  obtain ⟨v, hv0, hv⟩ := exists_pencil_eigvec hP.2 h0.ne' h1.ne hy
  obtain ⟨hkey, -, hlo, hhi⟩ := root_im_identity hP hA τ c hv
  have hn := re_star_dotProduct_self_pos hv0
  set n := (star v ⬝ᵥ v).re
  set a := (star v ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)).re
  have hcn : 0 < c.im * n := mul_pos hc hn
  refine ⟨fun h => by rw [h, zero_mul] at hkey; linarith, fun hy0 => ?_, fun hy0 => ?_⟩
  · -- `a > 0` and `a ≤ (1 - τ) n`
    have ha : 0 < a := by
      by_contra h
      push Not at h
      nlinarith
    have : c.im * n ≤ (1 - τ) * y.im * n := by
      rw [hkey]; nlinarith
    nlinarith
  · have ha : a < 0 := by
      by_contra h
      push Not at h
      nlinarith
    have : c.im * n ≤ -τ * y.im * n := by
      rw [hkey]; nlinarith
    nlinarith

/-- **Lemma B(ii)** (Q_RI).  A root in `ℂ₊` with `τ ≤ 1/2`, or a root in `ℂ₋` with `τ ≥ 1/2`,
satisfies `|y|² τ (1 - τ) ≤ ‖A + c‖_F²`. -/
lemma pencilRoot_norm_bound (hP : IsProj P) (hA : A.IsHermitian) {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1)
    {c : ℂ} (hc : 0 < c.im) {y : ℂ} (hy : y ∈ pencilRoots P (A + c • 1) τ)
    (hside : (0 < y.im ∧ τ ≤ 1 / 2) ∨ (y.im < 0 ∧ 1 / 2 ≤ τ)) :
    ‖y‖ ^ 2 * (τ * (1 - τ)) ≤ frob (A + c • 1) := by
  obtain ⟨v, hv0, hv⟩ := exists_pencil_eigvec hP.2 h0.ne' h1.ne hy
  obtain ⟨hkey, hQim, -, -⟩ := root_im_identity hP hA τ c hv
  have hn := re_star_dotProduct_self_pos hv0
  set n := (star v ⬝ᵥ v).re
  set a := (star v ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)).re
  have hcn : 0 < c.im * n := mul_pos hc hn
  -- `(1 - 2τ) a ≥ 0`
  have hsign : 0 ≤ (1 - 2 * τ) * a := by
    rcases hside with ⟨hy0, hτ⟩ | ⟨hy0, hτ⟩
    · have ha : 0 < a := by
        by_contra h
        push Not at h
        nlinarith
      nlinarith
    · have ha : a < 0 := by
        by_contra h
        push Not at h
        nlinarith
      nlinarith
  have hQQ := dot_P_sub_mulVec_gen hP τ v
  have hQQre : (star ((P - (τ : ℂ) • 1) *ᵥ v) ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)).re
      = (1 - 2 * τ) * a + τ * (1 - τ) * n := by
    have e1 : (1 - 2 * (τ : ℂ)) = ((1 - 2 * τ : ℝ) : ℂ) := by push_cast; ring
    have e2 : ((τ : ℂ) * (1 - τ)) = ((τ * (1 - τ) : ℝ) : ℂ) := by push_cast; ring
    rw [hQQ, e1, e2, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  have hlow : τ * (1 - τ) * n ≤ (star ((P - (τ : ℂ) • 1) *ᵥ v) ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)).re := by
    rw [hQQre]; linarith
  -- `|A' v|² = |y|² |(P - τ) v|²`
  have hAv : star ((A + c • 1) *ᵥ v) ⬝ᵥ ((A + c • 1) *ᵥ v)
      = ((‖y‖ : ℂ) ^ 2) * (star ((P - (τ : ℂ) • 1) *ᵥ v) ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)) := by
    rw [hv, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      Complex.star_def, Complex.conj_mul']
  have hle := re_dot_mulVec_le_frob (A + c • 1) v
  rw [hAv] at hle
  have hre : (((‖y‖ : ℂ) ^ 2) * (star ((P - (τ : ℂ) • 1) *ᵥ v) ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v))).re
      = ‖y‖ ^ 2 * (star ((P - (τ : ℂ) • 1) *ᵥ v) ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)).re := by
    have e : ((‖y‖ : ℂ) ^ 2) = ((‖y‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.re_ofReal_mul]
  rw [hre] at hle
  have h3 : ‖y‖ ^ 2 * (τ * (1 - τ) * n) ≤ frob (A + c • 1) * n :=
    le_trans (mul_le_mul_of_nonneg_left hlow (by positivity)) hle
  have h4 : ‖y‖ ^ 2 * (τ * (1 - τ)) * n ≤ frob (A + c • 1) * n := by linarith
  exact le_of_mul_le_mul_right h4 hn

end Locations

/-! ### Upper and lower root sums -/

/-- The roots in the upper half plane. -/
noncomputable def upperRoots (S : Multiset ℂ) : Multiset ℂ := S.filter fun z => 0 < z.im

/-- The roots in the lower half plane. -/
noncomputable def lowerRoots (S : Multiset ℂ) : Multiset ℂ := S.filter fun z => z.im < 0

lemma upper_add_lower {S : Multiset ℂ} (h : ∀ z ∈ S, z.im ≠ 0) :
    upperRoots S + lowerRoots S = S := by
  unfold upperRoots lowerRoots
  conv_rhs => rw [← Multiset.filter_add_not (fun z : ℂ => 0 < z.im) S]
  congr 1
  apply Multiset.filter_congr
  intro z hz
  constructor
  · intro hlt; exact not_lt.mpr hlt.le
  · intro hn; exact lt_of_le_of_ne (not_lt.mp hn) (h z hz)

/-- `|∑ z| ≤ card · B` if every `|z| ≤ B`. -/
lemma norm_multiset_sum_le_card_mul {S : Multiset ℂ} {B : ℝ} (h : ∀ z ∈ S, ‖z‖ ≤ B) :
    ‖S.sum‖ ≤ S.card * B := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    rw [Multiset.sum_cons, Multiset.card_cons]
    have ha := h a (Multiset.mem_cons_self a S)
    have hS := ih fun z hz => h z (Multiset.mem_cons_of_mem hz)
    push_cast
    calc ‖a + S.sum‖ ≤ ‖a‖ + ‖S.sum‖ := norm_add_le _ _
      _ ≤ B + S.card * B := add_le_add ha hS
      _ = (S.card + 1) * B := by ring

lemma card_pencilRoots (P H : Matrix (Fin M) (Fin M) ℂ) (τ : ℝ) :
    (pencilRoots P H τ).card = M := by
  unfold pencilRoots
  rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

lemma card_filter_le (S : Multiset ℂ) (q : ℂ → Prop) [DecidablePred q] :
    (S.filter q).card ≤ S.card := Multiset.card_le_card (Multiset.filter_le q S)

end OQP27.StripL3b
