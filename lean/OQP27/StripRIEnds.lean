import OQP27.StripRISmooth

/-!
# The two ends `τ → 1` and `τ → 0` (module L3b, proof of RI)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

Main results:
* `upper_end` (**Lemma D(a)**): `Λ_+(A) - Λ_+(A_d) → 0` as `τ → 1⁻`, uniformly on compact subsets of
  `ℂ₊`;
* `lower_end`: `Λ_-(A) - Λ_-(A_d) → 0` as `τ → 0⁺`, uniformly on compact subsets of `ℂ₊`.

Route.  With `Y = (P - τ)⁻¹ (A + c)`, `(1 - τ) Y → P (A + c)` and `τ Y → -(1 - P)(A + c)` (`Zmat`, `Wmat`).
The limits for `A` and for `A_d` have the same characteristic polynomial (`charpoly_Zmat_one`,
`charpoly_Wmat_zero`), whose non-zero roots lie on the lines `Im w = ± Im c` (`root_compression`), and
the half-plane log-sums are circle integrals that converge uniformly (`uniform_end_limit`).  This
replaces the Schur-complement limit of Lemma D(b): the end `τ → 0` of `Λ_+` is recovered in
`OQP27/StripRIAssembly.lean` from `lower_end` and `exp(Λ_+ + Λ_-) = det((P - τ)⁻¹ (A + c))`.

Hypotheses: none.
Paper: `iqoqi/programs/oqp27B_all/Q_RI/PROOF.md`, section 1, Lemma D and the remark after it.
-/

namespace OQP27.StripL3b

open Matrix Polynomial Complex Metric Filter Topology Set Real

variable {M : ℕ}

/-! ### General polynomial facts -/

/-- A polynomial of degree `≤ M` is the Lagrange interpolant of its values at `0, …, M`. -/
lemma lagrange_rep (p : ℂ[X]) (hp : p.natDegree ≤ M) :
    p = ∑ j ∈ lagNodes M, C (p.eval (j : ℂ)) * lagBasis M j := by
  have hinj : Set.InjOn (fun n : ℕ => (n : ℂ)) (lagNodes M : Set ℕ) :=
    fun a _ b _ h => Nat.cast_injective h
  have hdeg : p.degree < (lagNodes M).card := by
    rw [lagNodes, Finset.card_range]
    calc p.degree ≤ (p.natDegree : WithBot ℕ) := degree_le_natDegree
      _ < ((M + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_of_le hp
  conv_lhs => rw [Lagrange.eq_interpolate hinj hdeg]
  rw [Lagrange.interpolate_apply]
  rfl

/-- Roots of `χ_{s N}` for `s ≠ 0`. -/
lemma roots_charpoly_smul (N : Matrix (Fin M) (Fin M) ℂ) {s : ℂ} (hs : s ≠ 0) :
    (Matrix.charpoly (s • N)).roots = (Matrix.charpoly N).roots.map (s * ·) := by
  have key : Matrix.charpoly (s • N)
      = C (s ^ M) * (Matrix.charpoly N).comp (C s⁻¹ * X + C 0) := by
    apply Polynomial.funext
    intro z
    rw [Matrix.eval_charpoly, eval_mul, eval_C, eval_comp, Matrix.eval_charpoly]
    simp only [eval_add, eval_mul, eval_C, eval_X, add_zero]
    have h : Matrix.scalar (Fin M) z - s • N = s • (Matrix.scalar (Fin M) (s⁻¹ * z) - N) := by
      rw [smul_sub, Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
        ← Matrix.smul_one_eq_diagonal, smul_smul, mul_inv_cancel_left₀ hs]
    rw [h, Matrix.det_smul, Fintype.card_fin]
  rw [key, roots_C_mul _ (pow_ne_zero _ hs), roots_comp_C_mul_X_add_C _ _ _ (isUnit_iff_ne_zero.mpr
    (inv_ne_zero hs))]
  congr 1
  funext x
  simp [Ring.inverse_eq_inv']

lemma charpoly_proj_mul {Q : Matrix (Fin M) (Fin M) ℂ} (hQ : Q * Q = Q) (N : Matrix (Fin M) (Fin M) ℂ) :
    Matrix.charpoly (Q * N) = Matrix.charpoly (Q * N * Q) := by
  conv_lhs => rw [← hQ, Matrix.mul_assoc]
  rw [Matrix.charpoly_mul_comm]

/-- The eigenvalues of `s Q (A + c) Q` (`Q` a projection, `A` Hermitian, `s = ±1`) are `0` or lie
on the line `Im w = s Im c` with `|w|² ≤ ‖A + c‖_F²`. -/
lemma root_compression {Q A : Matrix (Fin M) (Fin M) ℂ} (hQ : IsProj Q) (hA : A.IsHermitian)
    {s : ℝ} (hs : s ^ 2 = 1) (c : ℂ) {w : ℂ}
    (hw : w ∈ (Matrix.charpoly ((s : ℂ) • (Q * (A + c • 1) * Q))).roots) :
    w = 0 ∨ (w.im = s * c.im ∧ ‖w‖ ^ 2 ≤ frob (A + c • 1)) := by
  by_cases hw0 : w = 0
  · exact Or.inl hw0
  right
  set N := (s : ℂ) • (Q * (A + c • 1) * Q) with hN
  have hroot : (Matrix.charpoly N).IsRoot w :=
    (Polynomial.mem_roots (Matrix.charpoly_monic N).ne_zero).mp hw
  rw [Polynomial.IsRoot.def, Matrix.eval_charpoly] at hroot
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hroot
  have hNv : N *ᵥ v = w • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  -- `v` lies in the range of `Q`
  have hQv : Q *ᵥ v = v := by
    have h1 : Q *ᵥ (N *ᵥ v) = N *ᵥ v := by
      rw [Matrix.mulVec_mulVec, hN, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        hQ.2]
    rw [hNv, Matrix.mulVec_smul] at h1
    exact smul_right_injective _ hw0 h1
  set u := (A + c • 1) *ᵥ v with hu
  have hNv' : N *ᵥ v = (s : ℂ) • (Q *ᵥ u) := by
    rw [hN, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hQv, hu]
  have hn := re_star_dotProduct_self_pos hv0
  have hvv : (star v ⬝ᵥ v).im = 0 := by
    simpa using (isHermitian_one (n := Fin M) (α := ℂ)).im_star_dotProduct_mulVec_self v
  have hAim : (star v ⬝ᵥ (A *ᵥ v)).im = 0 := by
    simpa using hA.im_star_dotProduct_mulVec_self v
  -- `⟨v, Q u⟩ = ⟨v, u⟩` since `Q v = v`
  have hstar : star v ᵥ* Q = star (Q *ᵥ v) := by rw [Matrix.star_mulVec, hQ.1.eq]
  have hvQu : star v ⬝ᵥ (Q *ᵥ u) = star v ⬝ᵥ u := by
    rw [Matrix.dotProduct_mulVec, hstar, hQv]
  have hvu : star v ⬝ᵥ u = star v ⬝ᵥ (A *ᵥ v) + c * (star v ⬝ᵥ v) := by
    rw [hu, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add,
      dotProduct_smul, smul_eq_mul]
  have heq : (s : ℂ) * (star v ⬝ᵥ u) = w * (star v ⬝ᵥ v) := by
    have := congrArg (star v ⬝ᵥ ·) (hNv'.symm.trans hNv)
    simp only [dotProduct_smul, smul_eq_mul, hvQu] at this
    exact this
  constructor
  · have him := congrArg Complex.im heq
    rw [hvu] at him
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im, Complex.add_re,
      hAim, hvv, zero_mul, add_zero, mul_zero, zero_add, Complex.mul_re, sub_zero] at him
    have hn' : (star v ⬝ᵥ v).re ≠ 0 := hn.ne'
    have : (w.im - s * c.im) * (star v ⬝ᵥ v).re = 0 := by linarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hn')
  · -- norms: `|w|² |v|² = |s Q u|² ≤ |u|² ≤ ‖A + c‖_F² |v|²`
    have hQu : (star (Q *ᵥ u) ⬝ᵥ (Q *ᵥ u)).re ≤ (star u ⬝ᵥ u).re := by
      have h1 : star (Q *ᵥ u) ⬝ᵥ (Q *ᵥ u) = star u ⬝ᵥ (Q *ᵥ u) := by
        rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hQ.1.eq, Matrix.mulVec_mulVec, hQ.2]
      have h2 : star u ⬝ᵥ u = star u ⬝ᵥ (Q *ᵥ u) + star u ⬝ᵥ ((1 - Q) *ᵥ u) := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub]; ring
      have h3 := re_dot_compl_nonneg hQ u
      rw [h1, h2, Complex.add_re]
      linarith
    have hwv : star (w • v) ⬝ᵥ (w • v) = ((‖w‖ : ℂ) ^ 2) * (star v ⬝ᵥ v) := by
      rw [star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
        Complex.star_def, Complex.conj_mul']
    have hsQu : star ((s : ℂ) • (Q *ᵥ u)) ⬝ᵥ ((s : ℂ) • (Q *ᵥ u))
        = star (Q *ᵥ u) ⬝ᵥ (Q *ᵥ u) := by
      rw [star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
        Complex.star_def, Complex.conj_ofReal]
      have : ((s : ℂ) * s) = 1 := by rw [← Complex.ofReal_mul, ← sq, hs, Complex.ofReal_one]
      rw [this, one_mul]
    have hfrob := re_dot_mulVec_le_frob (A + c • 1) v
    rw [← hu] at hfrob
    have hmain : ‖w‖ ^ 2 * (star v ⬝ᵥ v).re ≤ frob (A + c • 1) * (star v ⬝ᵥ v).re := by
      have e1 : (star (w • v) ⬝ᵥ (w • v)).re = ‖w‖ ^ 2 * (star v ⬝ᵥ v).re := by
        rw [hwv]
        have e : ((‖w‖ : ℂ) ^ 2) = ((‖w‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
        rw [e, Complex.re_ofReal_mul]
      rw [← e1, ← hNv, hNv', hsQu]
      exact hQu.trans hfrob
    exact le_of_mul_le_mul_right hmain hn


/-! ### Continuity of characteristic polynomials of matrix families -/

lemma eval_charpoly_eq_det (N : Matrix (Fin M) (Fin M) ℂ) (w : ℂ) :
    (Matrix.charpoly N).eval w = (w • (1 : Matrix (Fin M) (Fin M) ℂ) - N).det := by
  rw [Matrix.eval_charpoly, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

lemma continuousOn_eval_charpoly {X : Type*} [TopologicalSpace X] {Z : X → Matrix (Fin M) (Fin M) ℂ}
    {S : Set X} (hZ : ContinuousOn Z S) :
    ContinuousOn (fun p : X × ℂ => (Matrix.charpoly (Z p.1)).eval p.2) (S ×ˢ univ) := by
  simp only [eval_charpoly_eq_det]
  refine (continuous_id.matrix_det).comp_continuousOn ?_
  exact ((continuous_snd.smul continuous_const).continuousOn).sub
    (hZ.comp continuousOn_fst fun p hp => hp.1)

lemma continuousOn_eval_charpoly_deriv {X : Type*} [TopologicalSpace X]
    {Z : X → Matrix (Fin M) (Fin M) ℂ} {S : Set X} (hZ : ContinuousOn Z S) :
    ContinuousOn (fun p : X × ℂ => (Matrix.charpoly (Z p.1)).derivative.eval p.2) (S ×ˢ univ) := by
  have h : ∀ p : X × ℂ, (Matrix.charpoly (Z p.1)).derivative.eval p.2
      = ∑ j ∈ lagNodes M, (Matrix.charpoly (Z p.1)).eval (j : ℂ)
          * (lagBasis M j).derivative.eval p.2 := by
    intro p
    conv_lhs => rw [lagrange_rep (Matrix.charpoly (Z p.1))
      (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin])]
    simp only [derivative_sum, derivative_mul, derivative_C, zero_mul, zero_add, eval_finsetSum,
      eval_mul, eval_C]
  simp only [h]
  refine continuousOn_finsetSum _ fun j _ => ContinuousOn.mul ?_ ?_
  · have := continuousOn_eval_charpoly hZ
    exact this.comp (f := fun p : X × ℂ => (p.1, (j : ℂ))) (by fun_prop) fun p hp => ⟨hp.1, trivial⟩
  · exact ((lagBasis M j).derivative.continuous.comp continuous_snd).continuousOn

/-- **Uniform end limit.**  For two continuous matrix families on a compact parameter set whose
characteristic polynomials agree on the slice `τ = τ₁` and do not vanish on a circle, the circle
integral of `φ (q₁'/q₁ - q₂'/q₂)` tends to `0` as `τ → τ₁`, uniformly in `c`. -/
theorem uniform_end_limit {S : Set (ℝ × ℂ)} (hS : IsCompact S)
    (Z₁ Z₂ : ℝ × ℂ → Matrix (Fin M) (Fin M) ℂ) (hZ₁ : ContinuousOn Z₁ S)
    (hZ₂ : ContinuousOn Z₂ S) {z₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (hne₁ : ∀ q ∈ S, ∀ w ∈ sphere z₀ R, (Matrix.charpoly (Z₁ q)).eval w ≠ 0)
    (hne₂ : ∀ q ∈ S, ∀ w ∈ sphere z₀ R, (Matrix.charpoly (Z₂ q)).eval w ≠ 0)
    {φ : ℂ → ℂ} (hφ : ContinuousOn φ (sphere z₀ R)) {τ₁ : ℝ}
    (heq : ∀ q ∈ S, q.1 = τ₁ → Matrix.charpoly (Z₁ q) = Matrix.charpoly (Z₂ q)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ q ∈ S, |q.1 - τ₁| < δ → ((τ₁, q.2) : ℝ × ℂ) ∈ S →
      ‖∮ w in C(z₀, R), φ w * ((Matrix.charpoly (Z₁ q)).derivative.eval w
          / (Matrix.charpoly (Z₁ q)).eval w
        - (Matrix.charpoly (Z₂ q)).derivative.eval w / (Matrix.charpoly (Z₂ q)).eval w)‖ < ε := by
  set G : ℝ × ℂ → ℂ := fun q => ∮ w in C(z₀, R), φ w * ((Matrix.charpoly (Z₁ q)).derivative.eval w
      / (Matrix.charpoly (Z₁ q)).eval w
    - (Matrix.charpoly (Z₂ q)).derivative.eval w / (Matrix.charpoly (Z₂ q)).eval w) with hG
  have hsub : S ×ˢ sphere z₀ R ⊆ S ×ˢ univ := fun p hp => ⟨hp.1, trivial⟩
  have hcont : ContinuousOn (fun p : (ℝ × ℂ) × ℂ => φ p.2 * ((Matrix.charpoly (Z₁ p.1)).derivative.eval p.2
      / (Matrix.charpoly (Z₁ p.1)).eval p.2
    - (Matrix.charpoly (Z₂ p.1)).derivative.eval p.2 / (Matrix.charpoly (Z₂ p.1)).eval p.2))
      (S ×ˢ sphere z₀ R) := by
    refine (hφ.comp continuousOn_snd fun p hp => hp.2).mul (ContinuousOn.sub ?_ ?_)
    · exact ((continuousOn_eval_charpoly_deriv hZ₁).mono hsub).div
        ((continuousOn_eval_charpoly hZ₁).mono hsub) fun p hp => hne₁ p.1 hp.1 p.2 hp.2
    · exact ((continuousOn_eval_charpoly_deriv hZ₂).mono hsub).div
        ((continuousOn_eval_charpoly hZ₂).mono hsub) fun p hp => hne₂ p.1 hp.1 p.2 hp.2
  have hGc : ContinuousOn G S := continuousOn_circleIntegral (F := fun q w =>
    φ w * ((Matrix.charpoly (Z₁ q)).derivative.eval w / (Matrix.charpoly (Z₁ q)).eval w
      - (Matrix.charpoly (Z₂ q)).derivative.eval w / (Matrix.charpoly (Z₂ q)).eval w)) hR.le hcont
  have hU := hS.uniformContinuousOn_of_continuous hGc
  rw [Metric.uniformContinuousOn_iff] at hU
  obtain ⟨δ, hδ, hδ'⟩ := hU ε hε
  refine ⟨δ, hδ, fun q hq hτ hq1 => ?_⟩
  have hG1 : G (τ₁, q.2) = 0 := by
    rw [hG]
    simp only
    rw [heq (τ₁, q.2) hq1 rfl]
    simp only [sub_self, mul_zero]
    exact circleIntegral_zero' z₀ R
  have hd : dist q (τ₁, q.2) < δ := by
    rw [Prod.dist_eq, Real.dist_eq, dist_self, max_eq_left (abs_nonneg _)]
    exact hτ
  have := hδ' q hq (τ₁, q.2) hq1 hd
  rw [dist_eq_norm, hG1, sub_zero] at this
  exact this


/-! ### Half-plane root sums of a general polynomial -/

theorem upper_sum_poly (p : ℂ[X]) (hp : p ≠ 0) (him : ∀ w ∈ p.roots, w.im ≠ 0) {η ρ : ℝ}
    (hη : 0 < η) (hup : ∀ w ∈ p.roots, 0 < w.im → η ≤ w.im ∧ ‖w‖ ≤ ρ) {φ : ℂ → ℂ}
    (hφ : DiffContOnCl ℂ φ (ball (upCenter η ρ) (upRadius η ρ))) :
    ((upperRoots p.roots).map φ).sum
      = (2 * π * I)⁻¹ * ∮ w in C(upCenter η ρ, upRadius η ρ),
          φ w * (p.derivative.eval w / p.eval w) := by
  have hiff : ∀ a ∈ p.roots, dist a (upCenter η ρ) < upRadius η ρ ↔ 0 < a.im := by
    intro a ha
    constructor
    · intro hd
      have := im_ge_of_dist_upCenter_le (ρ := ρ) hη hd.le
      linarith
    · intro hpos
      obtain ⟨h1', h2'⟩ := hup a ha hpos
      exact dist_upCenter_lt hη h1' h2'
  have hdist : ∀ a ∈ p.roots, dist a (upCenter η ρ) ≠ upRadius η ρ := by
    intro a ha heq
    rcases lt_or_gt_of_ne (him a ha) with hneg | hpos
    · have := im_ge_of_dist_upCenter_le (ρ := ρ) hη heq.le
      linarith
    · have := (hiff a ha).mpr hpos
      linarith
  rw [circleIntegral_mul_logDeriv _ hp (upRadius_pos hη) hdist hφ, upperRoots,
    Multiset.filter_congr hiff, ← mul_assoc,
    inv_mul_cancel₀ (by simp [Real.pi_ne_zero, I_ne_zero]), one_mul]

theorem lower_sum_poly (p : ℂ[X]) (hp : p ≠ 0) (him : ∀ w ∈ p.roots, w.im ≠ 0) {η ρ : ℝ}
    (hη : 0 < η) (hlo : ∀ w ∈ p.roots, w.im < 0 → w.im ≤ -η ∧ ‖w‖ ≤ ρ) {φ : ℂ → ℂ}
    (hφ : DiffContOnCl ℂ φ (ball (loCenter η ρ) (upRadius η ρ))) :
    ((lowerRoots p.roots).map φ).sum
      = (2 * π * I)⁻¹ * ∮ w in C(loCenter η ρ, upRadius η ρ),
          φ w * (p.derivative.eval w / p.eval w) := by
  have hiff : ∀ a ∈ p.roots, dist a (loCenter η ρ) < upRadius η ρ ↔ a.im < 0 := by
    intro a ha
    constructor
    · intro hd
      have := im_le_of_dist_loCenter_le (ρ := ρ) hη hd.le
      linarith
    · intro hneg
      obtain ⟨h1', h2'⟩ := hlo a ha hneg
      exact dist_loCenter_lt hη h1' h2'
  have hdist : ∀ a ∈ p.roots, dist a (loCenter η ρ) ≠ upRadius η ρ := by
    intro a ha heq
    rcases lt_or_gt_of_ne (him a ha) with hneg | hpos
    · have := (hiff a ha).mpr hneg
      linarith
    · have := im_le_of_dist_loCenter_le (ρ := ρ) hη heq.le
      linarith
  rw [circleIntegral_mul_logDeriv _ hp (upRadius_pos hη) hdist hφ, lowerRoots,
    Multiset.filter_congr hiff, ← mul_assoc,
    inv_mul_cancel₀ (by simp [Real.pi_ne_zero, I_ne_zero]), one_mul]

/-! ### The rescaled pencils at the two ends -/

section Rescaled

variable {P A : Matrix (Fin M) (Fin M) ℂ}

/-- `(1 - τ) (P - τ)⁻¹ (A + c)`, continuous up to `τ = 1`. -/
noncomputable def Zmat (P A : Matrix (Fin M) (Fin M) ℂ) (q : ℝ × ℂ) : Matrix (Fin M) (Fin M) ℂ :=
  (P - (((1 - q.1) / q.1 : ℝ) : ℂ) • (1 - P)) * (A + q.2 • 1)

/-- `τ (P - τ)⁻¹ (A + c)`, continuous up to `τ = 0`. -/
noncomputable def Wmat (P A : Matrix (Fin M) (Fin M) ℂ) (q : ℝ × ℂ) : Matrix (Fin M) (Fin M) ℂ :=
  ((((q.1 / (1 - q.1)) : ℝ) : ℂ) • P - (1 - P)) * (A + q.2 • 1)

lemma continuousOn_Zmat (P A : Matrix (Fin M) (Fin M) ℂ) :
    ContinuousOn (Zmat P A) {q : ℝ × ℂ | q.1 ≠ 0} := by
  unfold Zmat
  have hs : ContinuousOn (fun q : ℝ × ℂ => ((((1 - q.1) / q.1 : ℝ)) : ℂ)) {q : ℝ × ℂ | q.1 ≠ 0} :=
    Complex.continuous_ofReal.comp_continuousOn
      (((continuous_const.sub continuous_fst).continuousOn).div continuous_fst.continuousOn
        fun q hq => hq)
  have h1 : ContinuousOn (fun q : ℝ × ℂ => P - ((((1 - q.1) / q.1 : ℝ)) : ℂ) • (1 - P))
      {q : ℝ × ℂ | q.1 ≠ 0} :=
    continuousOn_const.sub (hs.smul (continuousOn_const (c := (1 - P))))
  have h2 : Continuous (fun q : ℝ × ℂ => A + q.2 • (1 : Matrix (Fin M) (Fin M) ℂ)) := by fun_prop
  exact h1.mul h2.continuousOn

lemma continuousOn_Wmat (P A : Matrix (Fin M) (Fin M) ℂ) :
    ContinuousOn (Wmat P A) {q : ℝ × ℂ | 1 - q.1 ≠ 0} := by
  unfold Wmat
  have hs : ContinuousOn (fun q : ℝ × ℂ => (((q.1 / (1 - q.1)) : ℝ) : ℂ)) {q : ℝ × ℂ | 1 - q.1 ≠ 0} :=
    Complex.continuous_ofReal.comp_continuousOn
      (continuous_fst.continuousOn.div ((continuous_const.sub continuous_fst).continuousOn)
        fun q hq => hq)
  have h1 : ContinuousOn (fun q : ℝ × ℂ => (((q.1 / (1 - q.1)) : ℝ) : ℂ) • P - (1 - P))
      {q : ℝ × ℂ | 1 - q.1 ≠ 0} :=
    (hs.smul (continuousOn_const (c := P))).sub continuousOn_const
  have h2 : Continuous (fun q : ℝ × ℂ => A + q.2 • (1 : Matrix (Fin M) (Fin M) ℂ)) := by fun_prop
  exact h1.mul h2.continuousOn

lemma Zmat_eq (hP : P * P = P) {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) (c : ℂ) :
    Zmat P A (τ, c) = (((1 - τ : ℝ)) : ℂ) • ((P - (τ : ℂ) • 1)⁻¹ * (A + c • 1)) := by
  rw [inv_P_sub hP h0.ne' h1.ne, ← Matrix.smul_mul, Zmat]
  congr 1
  show P - (((1 - τ) / τ : ℝ) : ℂ) • (1 - P) = _
  have hτ : (τ : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  have hτ1 : (1 - (τ : ℂ)) ≠ 0 := by
    intro h; apply h1.ne; exact_mod_cast (sub_eq_zero.mp h).symm
  have e1 : (((1 - τ : ℝ)) : ℂ) * (1 - (τ : ℂ))⁻¹ = 1 := by
    push_cast; exact mul_inv_cancel₀ hτ1
  have e2 : (((1 - τ : ℝ)) : ℂ) * (τ : ℂ)⁻¹ = (((1 - τ) / τ : ℝ) : ℂ) := by
    push_cast; ring
  rw [smul_sub (((1 - τ : ℝ)) : ℂ), smul_smul, smul_smul, e1, e2, one_smul]

lemma Wmat_eq (hP : P * P = P) {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) (c : ℂ) :
    Wmat P A (τ, c) = (τ : ℂ) • ((P - (τ : ℂ) • 1)⁻¹ * (A + c • 1)) := by
  rw [inv_P_sub hP h0.ne' h1.ne, ← Matrix.smul_mul, Wmat]
  congr 1
  show (((τ / (1 - τ)) : ℝ) : ℂ) • P - (1 - P) = _
  have hτ : (τ : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  rw [smul_sub (τ : ℂ), smul_smul, smul_smul, mul_inv_cancel₀ hτ, one_smul]
  congr 2
  push_cast
  ring

lemma roots_Zmat (hP : P * P = P) {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) (c : ℂ) :
    (Matrix.charpoly (Zmat P A (τ, c))).roots = (Rt P A τ c).map ((((1 - τ : ℝ)) : ℂ) * ·) := by
  rw [Zmat_eq hP h0 h1, roots_charpoly_smul _ (by exact_mod_cast (sub_pos.mpr h1).ne')]
  rfl

lemma roots_Wmat (hP : P * P = P) {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) (c : ℂ) :
    (Matrix.charpoly (Wmat P A (τ, c))).roots = (Rt P A τ c).map ((τ : ℂ) * ·) := by
  rw [Wmat_eq hP h0 h1, roots_charpoly_smul _ (by exact_mod_cast h0.ne')]
  rfl

lemma Zmat_one (P A : Matrix (Fin M) (Fin M) ℂ) (c : ℂ) :
    Zmat P A (1, c) = P * (A + c • 1) := by
  simp [Zmat]

lemma Wmat_zero (P A : Matrix (Fin M) (Fin M) ℂ) (c : ℂ) :
    Wmat P A (0, c) = -(1 - P) * (A + c • 1) := by
  simp [Wmat]

lemma pinch_compress (hP : P * P = P) (A : Matrix (Fin M) (Fin M) ℂ) (c : ℂ) :
    P * (pinch P A + c • 1) * P = P * (A + c • 1) * P := by
  have hPB := proj_mul_compl hP
  have hBP := compl_mul_proj hP
  unfold pinch
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    ← Matrix.mul_assoc, hPB, hP, Matrix.zero_mul]
  rw [Matrix.mul_assoc (P * A) P P, hP, zero_add]

lemma pinch_compress' (hP : P * P = P) (A : Matrix (Fin M) (Fin M) ℂ) (c : ℂ) :
    (1 - P) * (pinch P A + c • 1) * (1 - P) = (1 - P) * (A + c • 1) * (1 - P) := by
  have hQ : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, proj_mul_compl hP, sub_zero]
  have hPB := proj_mul_compl hP
  have hBP := compl_mul_proj hP
  unfold pinch
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    ← Matrix.mul_assoc, hBP, hQ, Matrix.zero_mul]
  rw [Matrix.mul_assoc ((1 - P) * A) (1 - P) (1 - P), hQ, add_zero]

lemma charpoly_Zmat_one (hP : P * P = P) (A : Matrix (Fin M) (Fin M) ℂ) (c : ℂ) :
    Matrix.charpoly (Zmat P (pinch P A) (1, c)) = Matrix.charpoly (Zmat P A (1, c)) := by
  rw [Zmat_one, Zmat_one, charpoly_proj_mul hP, charpoly_proj_mul hP, pinch_compress hP]

lemma charpoly_neg_proj_mul {Q : Matrix (Fin M) (Fin M) ℂ} (hQ : Q * Q = Q)
    (N : Matrix (Fin M) (Fin M) ℂ) :
    Matrix.charpoly (-Q * N) = Matrix.charpoly (((-1 : ℝ) : ℂ) • (Q * N * Q)) := by
  have h1 : -Q * N = Q * (-N) := by rw [Matrix.neg_mul, Matrix.mul_neg]
  rw [h1, charpoly_proj_mul hQ, Matrix.mul_neg, Matrix.neg_mul]
  congr 1
  simp

lemma charpoly_Wmat_zero (hP : P * P = P) (A : Matrix (Fin M) (Fin M) ℂ) (c : ℂ) :
    Matrix.charpoly (Wmat P (pinch P A) (0, c)) = Matrix.charpoly (Wmat P A (0, c)) := by
  have hQ : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, proj_mul_compl hP, sub_zero]
  rw [Wmat_zero, Wmat_zero, charpoly_neg_proj_mul hQ, charpoly_neg_proj_mul hQ, pinch_compress' hP]

end Rescaled


/-! ### The end limits (Lemma D of Q_RI, in the block-triangular form) -/

section EndThm

variable {P A : Matrix (Fin M) (Fin M) ℂ}

lemma sum_log_map_mul (S : Multiset ℂ) {r : ℝ} (hr : 0 < r) (hS : ∀ y ∈ S, y ≠ 0) :
    ((S.map ((r : ℂ) * ·)).map Complex.log).sum
      = (S.card : ℂ) * (Real.log r : ℂ) + (S.map Complex.log).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    rw [Complex.log_ofReal_mul hr (hS a (Multiset.mem_cons_self a S)),
      ih fun y hy => hS y (Multiset.mem_cons_of_mem hy)]
    push_cast
    ring

lemma upperRoots_map_mul (S : Multiset ℂ) {r : ℝ} (hr : 0 < r) :
    upperRoots (S.map ((r : ℂ) * ·)) = (upperRoots S).map ((r : ℂ) * ·) := by
  unfold upperRoots
  rw [Multiset.filter_map]
  congr 1
  apply Multiset.filter_congr
  intro y _
  simp only [Function.comp_apply, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero]
  constructor
  · intro h; exact pos_of_mul_pos_right h hr.le
  · intro h; exact mul_pos hr h

lemma lowerRoots_map_mul (S : Multiset ℂ) {r : ℝ} (hr : 0 < r) :
    lowerRoots (S.map ((r : ℂ) * ·)) = (lowerRoots S).map ((r : ℂ) * ·) := by
  unfold lowerRoots
  rw [Multiset.filter_map]
  congr 1
  apply Multiset.filter_congr
  intro y _
  simp only [Function.comp_apply, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero]
  constructor
  · intro h; by_contra h'; push Not at h'; nlinarith
  · intro h; nlinarith

/-- An integer of absolute value `< 1` is zero. -/
lemma int_cast_eq_zero_of_norm_lt {n : ℤ} (h : ‖(n : ℂ)‖ < 1) : n = 0 := by
  rw [Complex.norm_intCast] at h
  have : |n| < 1 := by exact_mod_cast h
  exact Int.abs_lt_one_iff.mp this

/-- **The end `τ → 1`.**  `Λ_+(A) - Λ_+(A_d) → 0` as `τ → 1⁻`, uniformly on compact subsets of
`ℂ₊`. -/
theorem upper_end (hP : IsProj P) (hA : A.IsHermitian) {K : Set ℂ} (hK : IsCompact K)
    (hKpos : ∀ c ∈ K, 0 < c.im) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ > 0, ∀ τ : ℝ, 1 - δ₀ < τ → τ < 1 → ∀ c ∈ K,
      ‖Lup P A τ c - Lup P (pinch P A) τ c‖ < ε := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨1, one_pos, fun τ _ _ c hc => by rw [hKe] at hc; exact absurd hc (Set.notMem_empty c)⟩
  obtain ⟨c₁, hc₁K, hc₁min⟩ := hK.exists_isMinOn hKne Complex.continuous_im.continuousOn
  set η := c₁.im with hη_def
  have hη : 0 < η := hKpos c₁ hc₁K
  have hηle : ∀ c ∈ K, η ≤ c.im := fun c hc => hc₁min hc
  set A₀ := pinch P A with hA₀_def
  have hA₀ : A₀.IsHermitian := isHermitian_pinch hP.1 hA
  have hcf : ContinuousOn (fun c : ℂ => frob (A + c • 1) + frob (A₀ + c • 1)) K := by
    apply Continuous.continuousOn; unfold frob; fun_prop
  obtain ⟨Kf, hKf⟩ := hK.exists_bound_of_continuousOn hcf
  set ρ := √(max Kf 0) with hρ
  have hfrob : ∀ B : Matrix (Fin M) (Fin M) ℂ, (B = A ∨ B = A₀) → ∀ c ∈ K,
      frob (B + c • 1) ≤ max Kf 0 := by
    intro B hB c hc
    have h1 := hKf c hc
    rw [Real.norm_eq_abs] at h1
    have hA1 := frob_nonneg (A + c • 1)
    have hA2 := frob_nonneg (A₀ + c • 1)
    rw [abs_of_nonneg (by linarith)] at h1
    rcases hB with hB | hB
    · rw [hB]; exact (by linarith : frob (A + c • 1) ≤ Kf).trans (le_max_left _ _)
    · rw [hB]; exact (by linarith : frob (A₀ + c • 1) ≤ Kf).trans (le_max_left _ _)
  -- the parameter set and the circle
  set S := Icc (1 / 2 : ℝ) 1 ×ˢ K with hS_def
  have hS : IsCompact S := isCompact_Icc.prod hK
  have hSsub : S ⊆ {q : ℝ × ℂ | q.1 ≠ 0} := fun q hq => by
    have := hq.1.1; exact ne_of_gt (by linarith)
  set z₀ := upCenter η ρ
  set R := upRadius η ρ
  have hR : 0 < R := upRadius_pos hη
  -- root facts for `B ∈ {A, A₀}`
  have hroots : ∀ B : Matrix (Fin M) (Fin M) ℂ, (B = A ∨ B = A₀) → B.IsHermitian →
      ∀ q ∈ S, q.1 < 1 → ∀ w ∈ (Matrix.charpoly (Zmat P B q)).roots,
        w.im ≠ 0 ∧ (0 < w.im → η ≤ w.im ∧ ‖w‖ ≤ ρ) := by
    intro B hB hBh q hq hq1 w hw
    obtain ⟨τ, c⟩ := q
    have hτ0 : 0 < τ := by have := hq.1.1; simp only at this; linarith
    have hc := hq.2
    simp only at hq1 hc
    rw [roots_Zmat hP.2 hτ0 hq1] at hw
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hw
    have hcpos := hKpos c hc
    obtain ⟨hyim, hyup, -⟩ := pencilRoot_im_bounds hP hBh hτ0 hq1 hcpos hy
    have h1τ : 0 < 1 - τ := by linarith
    have him : ((((1 - τ : ℝ)) : ℂ) * y).im = (1 - τ) * y.im := by
      simp [Complex.mul_im]
    refine ⟨by rw [him]; exact mul_ne_zero h1τ.ne' hyim, fun hpos => ?_⟩
    rw [him] at hpos ⊢
    have hypos : 0 < y.im := pos_of_mul_pos_right hpos h1τ.le
    refine ⟨(hηle c hc).trans (hyup hypos), ?_⟩
    have hBnd := pencilRoot_norm_bound_all hP hBh hτ0 hq1 c hy
    have hτhalf : 1 / 2 ≤ τ := hq.1.1
    rw [min_eq_right (by linarith)] at hBnd
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1τ]
    rw [hρ, ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (1 - τ) * ‖y‖)]
    apply Real.sqrt_le_sqrt
    calc ((1 - τ) * ‖y‖) ^ 2 = ‖y‖ ^ 2 * (1 - τ) ^ 2 := by ring
      _ ≤ frob (B + c • 1) := hBnd
      _ ≤ max Kf 0 := hfrob B hB c hc
  have hroots1 : ∀ B : Matrix (Fin M) (Fin M) ℂ, (B = A ∨ B = A₀) → B.IsHermitian →
      ∀ c ∈ K, ∀ w ∈ (Matrix.charpoly (Zmat P B (1, c))).roots,
        w = 0 ∨ (η ≤ w.im ∧ ‖w‖ ≤ ρ) := by
    intro B hB hBh c hc w hw
    rw [Zmat_one, charpoly_proj_mul hP.2] at hw
    have hw' : w ∈ (Matrix.charpoly (((1 : ℝ) : ℂ) • (P * (B + c • 1) * P))).roots := by
      simpa using hw
    rcases root_compression hP hBh (s := 1) (by norm_num) c hw' with h0 | ⟨him, hnorm⟩
    · exact Or.inl h0
    · right
      refine ⟨by rw [him, one_mul]; exact hηle c hc, ?_⟩
      rw [hρ, ← Real.sqrt_sq (norm_nonneg w)]
      exact Real.sqrt_le_sqrt (hnorm.trans (hfrob B hB c hc))
  -- no zeros on the circle
  have hne : ∀ B : Matrix (Fin M) (Fin M) ℂ, (B = A ∨ B = A₀) → B.IsHermitian →
      ∀ q ∈ S, ∀ w ∈ sphere z₀ R, (Matrix.charpoly (Zmat P B q)).eval w ≠ 0 := by
    intro B hB hBh q hq w hw h0
    have hwr : w ∈ (Matrix.charpoly (Zmat P B q)).roots :=
      (Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).mpr h0
    have hwim : η / 2 ≤ w.im := im_ge_of_dist_upCenter_le (ρ := ρ) hη (mem_sphere.mp hw).le
    have hin : η ≤ w.im ∧ ‖w‖ ≤ ρ := by
      rcases lt_or_eq_of_le hq.1.2 with hq1 | hq1
      · exact ((hroots B hB hBh q hq hq1 w hwr).2 (by linarith))
      · obtain ⟨τ, c⟩ := q
        simp only at hq1
        subst hq1
        rcases hroots1 B hB hBh c hq.2 w hwr with h0' | h'
        · rw [h0'] at hwim; simp at hwim; linarith
        · exact h'
    have := dist_upCenter_lt hη hin.1 hin.2
    rw [mem_sphere.mp hw] at this
    exact lt_irrefl _ this
  have hneA := hne A (Or.inl rfl) hA
  have hneA₀ := hne A₀ (Or.inr rfl) hA₀
  have hslit : ∀ w ∈ sphere z₀ R, w ∈ slitPlane := fun w hw =>
    Or.inr (by have := im_ge_of_dist_upCenter_le (ρ := ρ) hη (mem_sphere.mp hw).le; linarith)
  have hlogc : ContinuousOn Complex.log (sphere z₀ R) := fun w hw =>
    (continuousAt_clog (hslit w hw)).continuousWithinAt
  have hZA := (continuousOn_Zmat P A).mono hSsub
  have hZA₀ := (continuousOn_Zmat P A₀).mono hSsub
  have heq1 : ∀ q ∈ S, q.1 = 1 → Matrix.charpoly (Zmat P A q) = Matrix.charpoly (Zmat P A₀ q) := by
    intro q _ hq1
    obtain ⟨τ, c⟩ := q
    simp only at hq1
    subst hq1
    exact (charpoly_Zmat_one hP.2 A c).symm
  obtain ⟨δL, hδL, hL⟩ := uniform_end_limit hS (Zmat P A) (Zmat P A₀) hZA hZA₀ hR hneA hneA₀ hlogc
    heq1 (ε := 2 * π * ε) (by positivity)
  obtain ⟨δ1, hδ1, h1⟩ := uniform_end_limit hS (Zmat P A) (Zmat P A₀) hZA hZA₀ hR hneA hneA₀
    (φ := fun _ => 1) continuousOn_const heq1 (ε := π) Real.pi_pos
  refine ⟨min (min δL δ1) (1 / 2), by positivity, fun τ hτ1 hτ c hc => ?_⟩
  have hmin1 := min_le_left (min δL δ1) (1 / 2)
  have hmin2 := min_le_right (min δL δ1) (1 / 2)
  have hminL := min_le_left δL δ1
  have hmin1' := min_le_right δL δ1
  have hτhalf : 1 / 2 ≤ τ := by linarith
  have hτ0 : 0 < τ := by linarith
  have hq : ((τ, c) : ℝ × ℂ) ∈ S := ⟨⟨hτhalf, hτ.le⟩, hc⟩
  have hq1 : ((1, c) : ℝ × ℂ) ∈ S := ⟨⟨by norm_num, le_rfl⟩, hc⟩
  have habs : |(τ, c).1 - 1| < min (min δL δ1) (1 / 2) := by
    simp only; rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
  have hGL := hL (τ, c) hq (by linarith) hq1
  have hG1 := h1 (τ, c) hq (by linarith) hq1
  -- contour representations of the rescaled sums
  have hrep : ∀ B : Matrix (Fin M) (Fin M) ℂ, (B = A ∨ B = A₀) → B.IsHermitian →
      ∀ φ : ℂ → ℂ, DiffContOnCl ℂ φ (ball z₀ R) →
        ((upperRoots (Matrix.charpoly (Zmat P B (τ, c))).roots).map φ).sum
          = (2 * π * I)⁻¹ * ∮ w in C(z₀, R), φ w * ((Matrix.charpoly (Zmat P B (τ, c))).derivative.eval w
            / (Matrix.charpoly (Zmat P B (τ, c))).eval w) := by
    intro B hB hBh φ hφ
    exact upper_sum_poly _ (Matrix.charpoly_monic _).ne_zero
      (fun w hw => (hroots B hB hBh (τ, c) hq hτ w hw).1) hη
      (fun w hw => (hroots B hB hBh (τ, c) hq hτ w hw).2) hφ
  -- relation with `Λ_+`
  have hrel : ∀ B : Matrix (Fin M) (Fin M) ℂ, B.IsHermitian →
      ((upperRoots (Matrix.charpoly (Zmat P B (τ, c))).roots).map Complex.log).sum
        = ((upperRoots (Rt P B τ c)).card : ℂ) * (Real.log (1 - τ) : ℂ) + Lup P B τ c := by
    intro B hBh
    rw [roots_Zmat hP.2 hτ0 hτ, upperRoots_map_mul _ (by linarith : (0 : ℝ) < 1 - τ),
      sum_log_map_mul _ (by linarith) fun y hy h0 => by
        have := (Multiset.mem_filter.mp hy).2; rw [h0] at this; simp at this]
    rfl
  have hcount : ∀ B : Matrix (Fin M) (Fin M) ℂ, B.IsHermitian →
      ((upperRoots (Matrix.charpoly (Zmat P B (τ, c))).roots).map fun _ => (1 : ℂ)).sum
        = ((upperRoots (Rt P B τ c)).card : ℂ) := by
    intro B _
    rw [roots_Zmat hP.2 hτ0 hτ, upperRoots_map_mul _ (by linarith : (0 : ℝ) < 1 - τ)]
    simp
  -- integrability on the circle
  have hint : ∀ B : Matrix (Fin M) (Fin M) ℂ, (B = A ∨ B = A₀) → B.IsHermitian →
      ∀ φ : ℂ → ℂ, ContinuousOn φ (sphere z₀ R) →
        CircleIntegrable (fun w => φ w * ((Matrix.charpoly (Zmat P B (τ, c))).derivative.eval w
          / (Matrix.charpoly (Zmat P B (τ, c))).eval w)) z₀ R := by
    intro B hB hBh φ hφ
    refine ContinuousOn.circleIntegrable hR.le (hφ.mul ?_)
    exact ((Polynomial.continuous _).continuousOn).div ((Polynomial.continuous _).continuousOn)
      fun w hw => hne B hB hBh (τ, c) hq w hw
  -- the count difference vanishes
  have hcnt : ((upperRoots (Rt P A τ c)).card : ℂ) = ((upperRoots (Rt P A₀ τ c)).card : ℂ) := by
    have hd := hcount A hA
    have hd₀ := hcount A₀ hA₀
    rw [hrep A (Or.inl rfl) hA _ diffContOnCl_const] at hd
    rw [hrep A₀ (Or.inr rfl) hA₀ _ diffContOnCl_const] at hd₀
    have hdiff : ((upperRoots (Rt P A τ c)).card : ℂ) - ((upperRoots (Rt P A₀ τ c)).card : ℂ)
        = (2 * π * I)⁻¹ * ∮ w in C(z₀, R), (fun _ => (1 : ℂ)) w
          * ((Matrix.charpoly (Zmat P A (τ, c))).derivative.eval w
            / (Matrix.charpoly (Zmat P A (τ, c))).eval w
          - (Matrix.charpoly (Zmat P A₀ (τ, c))).derivative.eval w
            / (Matrix.charpoly (Zmat P A₀ (τ, c))).eval w) := by
      rw [← hd, ← hd₀, ← mul_sub, ← circleIntegral.integral_sub
        (hint A (Or.inl rfl) hA _ continuousOn_const) (hint A₀ (Or.inr rfl) hA₀ _ continuousOn_const)]
      congr 2
      funext w
      ring
    have hsmall : ‖((upperRoots (Rt P A τ c)).card : ℂ) - ((upperRoots (Rt P A₀ τ c)).card : ℂ)‖ < 1 := by
      rw [hdiff, norm_mul, norm_inv]
      have h2pi : ‖(2 * π * I : ℂ)‖ = 2 * π := by
        simp [abs_of_pos Real.pi_pos]
      rw [h2pi]
      have := hG1
      calc (2 * π)⁻¹ * _ < (2 * π)⁻¹ * π := by
            gcongr
        _ < 1 := by
            rw [inv_mul_lt_iff₀ (by positivity)]; linarith [Real.pi_pos]
    have hint' := int_cast_eq_zero_of_norm_lt (n := ((upperRoots (Rt P A τ c)).card : ℤ)
      - ((upperRoots (Rt P A₀ τ c)).card : ℤ)) (by push_cast; exact hsmall)
    have : ((upperRoots (Rt P A τ c)).card : ℤ) = ((upperRoots (Rt P A₀ τ c)).card : ℤ) :=
      sub_eq_zero.mp hint'
    exact_mod_cast this
  -- conclusion
  have hLA := hrel A hA
  have hLA₀ := hrel A₀ hA₀
  rw [hrep A (Or.inl rfl) hA _ (diffContOnCl_log_upper hη)] at hLA
  rw [hrep A₀ (Or.inr rfl) hA₀ _ (diffContOnCl_log_upper hη)] at hLA₀
  have hdiffL : Lup P A τ c - Lup P A₀ τ c
      = (2 * π * I)⁻¹ * ∮ w in C(z₀, R), Complex.log w
          * ((Matrix.charpoly (Zmat P A (τ, c))).derivative.eval w
            / (Matrix.charpoly (Zmat P A (τ, c))).eval w
          - (Matrix.charpoly (Zmat P A₀ (τ, c))).derivative.eval w
            / (Matrix.charpoly (Zmat P A₀ (τ, c))).eval w) := by
    have e : Lup P A τ c - Lup P A₀ τ c
        = (2 * π * I)⁻¹ * (∮ w in C(z₀, R), Complex.log w
            * ((Matrix.charpoly (Zmat P A (τ, c))).derivative.eval w
              / (Matrix.charpoly (Zmat P A (τ, c))).eval w))
          - (2 * π * I)⁻¹ * (∮ w in C(z₀, R), Complex.log w
            * ((Matrix.charpoly (Zmat P A₀ (τ, c))).derivative.eval w
              / (Matrix.charpoly (Zmat P A₀ (τ, c))).eval w)) := by
      rw [hLA, hLA₀, hcnt]; ring
    rw [e, ← mul_sub, ← circleIntegral.integral_sub
      (hint A (Or.inl rfl) hA _ hlogc) (hint A₀ (Or.inr rfl) hA₀ _ hlogc)]
    congr 2
    funext w
    ring
  rw [hdiffL, norm_mul, norm_inv]
  have h2pi : ‖(2 * π * I : ℂ)‖ = 2 * π := by
    simp [abs_of_pos Real.pi_pos]
  rw [h2pi]
  calc (2 * π)⁻¹ * _ < (2 * π)⁻¹ * (2 * π * ε) := by gcongr
    _ = ε := by field_simp

/-- **The end `τ → 0`.**  `Λ_-(A) - Λ_-(A_d) → 0` as `τ → 0⁺`, uniformly on compact subsets of
`ℂ₊`. -/
theorem lower_end (hP : IsProj P) (hA : A.IsHermitian) {K : Set ℂ} (hK : IsCompact K)
    (hKpos : ∀ c ∈ K, 0 < c.im) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ₀ > 0, ∀ τ : ℝ, 0 < τ → τ < δ₀ → ∀ c ∈ K,
      ‖Llo P A τ c - Llo P (pinch P A) τ c‖ < ε := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨1, one_pos, fun τ _ _ c hc => by rw [hKe] at hc; exact absurd hc (Set.notMem_empty c)⟩
  obtain ⟨c₁, hc₁K, hc₁min⟩ := hK.exists_isMinOn hKne Complex.continuous_im.continuousOn
  set η := c₁.im with hη_def
  have hη : 0 < η := hKpos c₁ hc₁K
  have hηle : ∀ c ∈ K, η ≤ c.im := fun c hc => hc₁min hc
  set A₀ := pinch P A with hA₀_def
  have hA₀ : A₀.IsHermitian := isHermitian_pinch hP.1 hA
  have hcf : ContinuousOn (fun c : ℂ => frob (A + c • 1) + frob (A₀ + c • 1)) K := by
    apply Continuous.continuousOn; unfold frob; fun_prop
  obtain ⟨Kf, hKf⟩ := hK.exists_bound_of_continuousOn hcf
  set ρ := √(max Kf 0) with hρ
  have hfrob : ∀ B : Matrix (Fin M) (Fin M) ℂ, (B = A ∨ B = A₀) → ∀ c ∈ K,
      frob (B + c • 1) ≤ max Kf 0 := by
    intro B hB c hc
    have h1 := hKf c hc
    rw [Real.norm_eq_abs] at h1
    have hA1 := frob_nonneg (A + c • 1)
    have hA2 := frob_nonneg (A₀ + c • 1)
    rw [abs_of_nonneg (by linarith)] at h1
    rcases hB with hB | hB
    · rw [hB]; exact (by linarith : frob (A + c • 1) ≤ Kf).trans (le_max_left _ _)
    · rw [hB]; exact (by linarith : frob (A₀ + c • 1) ≤ Kf).trans (le_max_left _ _)
  -- the parameter set and the circle
  set S := Icc (0 : ℝ) (1 / 2) ×ˢ K with hS_def
  have hS : IsCompact S := isCompact_Icc.prod hK
  have hSsub : S ⊆ {q : ℝ × ℂ | 1 - q.1 ≠ 0} := fun q hq => by
    have := hq.1.2; exact ne_of_gt (by linarith)
  set z₀ := loCenter η ρ
  set R := upRadius η ρ
  have hR : 0 < R := upRadius_pos hη
  -- root facts for `B ∈ {A, A₀}`
  have hroots : ∀ B : Matrix (Fin M) (Fin M) ℂ, (B = A ∨ B = A₀) → B.IsHermitian →
      ∀ q ∈ S, 0 < q.1 → ∀ w ∈ (Matrix.charpoly (Wmat P B q)).roots,
        w.im ≠ 0 ∧ (w.im < 0 → w.im ≤ -η ∧ ‖w‖ ≤ ρ) := by
    intro B hB hBh q hq hq0 w hw
    obtain ⟨τ, c⟩ := q
    have hτ1 : τ < 1 := by have := hq.1.2; simp only at this; linarith
    have hc := hq.2
    simp only at hq0 hc
    rw [roots_Wmat hP.2 hq0 hτ1] at hw
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hw
    have hcpos := hKpos c hc
    obtain ⟨hyim, -, hylo⟩ := pencilRoot_im_bounds hP hBh hq0 hτ1 hcpos hy
    have him : ((τ : ℂ) * y).im = τ * y.im := by
      simp [Complex.mul_im]
    refine ⟨by rw [him]; exact mul_ne_zero hq0.ne' hyim, fun hneg => ?_⟩
    rw [him] at hneg ⊢
    have hyneg : y.im < 0 := by
      by_contra h; push Not at h; nlinarith
    refine ⟨by linarith [hylo hyneg, hηle c hc], ?_⟩
    have hBnd := pencilRoot_norm_bound_all hP hBh hq0 hτ1 c hy
    have hτhalf : τ ≤ 1 / 2 := hq.1.2
    rw [min_eq_left (by linarith)] at hBnd
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]
    rw [hρ, ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ τ * ‖y‖)]
    apply Real.sqrt_le_sqrt
    calc (τ * ‖y‖) ^ 2 = ‖y‖ ^ 2 * τ ^ 2 := by ring
      _ ≤ frob (B + c • 1) := hBnd
      _ ≤ max Kf 0 := hfrob B hB c hc
  have hroots1 : ∀ B : Matrix (Fin M) (Fin M) ℂ, (B = A ∨ B = A₀) → B.IsHermitian →
      ∀ c ∈ K, ∀ w ∈ (Matrix.charpoly (Wmat P B (0, c))).roots,
        w = 0 ∨ (w.im ≤ -η ∧ ‖w‖ ≤ ρ) := by
    intro B hB hBh c hc w hw
    have hQ : (1 - P) * (1 - P) = 1 - P := by
      rw [Matrix.sub_mul, Matrix.one_mul, proj_mul_compl hP.2, sub_zero]
    have hQproj : IsProj (1 - P) := ⟨isHermitian_one.sub hP.1, hQ⟩
    rw [Wmat_zero, charpoly_neg_proj_mul hQ] at hw
    rcases root_compression hQproj hBh (s := -1) (by norm_num) c hw with h0 | ⟨him, hnorm⟩
    · exact Or.inl h0
    · right
      refine ⟨by rw [him]; linarith [hηle c hc], ?_⟩
      rw [hρ, ← Real.sqrt_sq (norm_nonneg w)]
      exact Real.sqrt_le_sqrt (hnorm.trans (hfrob B hB c hc))
  -- no zeros on the circle
  have hne : ∀ B : Matrix (Fin M) (Fin M) ℂ, (B = A ∨ B = A₀) → B.IsHermitian →
      ∀ q ∈ S, ∀ w ∈ sphere z₀ R, (Matrix.charpoly (Wmat P B q)).eval w ≠ 0 := by
    intro B hB hBh q hq w hw h0
    have hwr : w ∈ (Matrix.charpoly (Wmat P B q)).roots :=
      (Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).mpr h0
    have hwim : w.im ≤ -(η / 2) := im_le_of_dist_loCenter_le (ρ := ρ) hη (mem_sphere.mp hw).le
    have hin : w.im ≤ -η ∧ ‖w‖ ≤ ρ := by
      rcases lt_or_eq_of_le hq.1.1 with hq0 | hq0
      · exact ((hroots B hB hBh q hq hq0 w hwr).2 (by linarith))
      · obtain ⟨τ, c⟩ := q
        simp only at hq0
        subst hq0
        rcases hroots1 B hB hBh c hq.2 w hwr with h0' | h'
        · rw [h0'] at hwim; simp at hwim; linarith
        · exact h'
    have := dist_loCenter_lt hη hin.1 hin.2
    rw [mem_sphere.mp hw] at this
    exact lt_irrefl _ this
  have hneA := hne A (Or.inl rfl) hA
  have hneA₀ := hne A₀ (Or.inr rfl) hA₀
  have hslit : ∀ w ∈ sphere z₀ R, w ∈ slitPlane := fun w hw =>
    Or.inr (by have := im_le_of_dist_loCenter_le (ρ := ρ) hη (mem_sphere.mp hw).le; linarith)
  have hlogc : ContinuousOn Complex.log (sphere z₀ R) := fun w hw =>
    (continuousAt_clog (hslit w hw)).continuousWithinAt
  have hZA := (continuousOn_Wmat P A).mono hSsub
  have hZA₀ := (continuousOn_Wmat P A₀).mono hSsub
  have heq1 : ∀ q ∈ S, q.1 = 0 → Matrix.charpoly (Wmat P A q) = Matrix.charpoly (Wmat P A₀ q) := by
    intro q _ hq1
    obtain ⟨τ, c⟩ := q
    simp only at hq1
    subst hq1
    exact (charpoly_Wmat_zero hP.2 A c).symm
  obtain ⟨δL, hδL, hL⟩ := uniform_end_limit hS (Wmat P A) (Wmat P A₀) hZA hZA₀ hR hneA hneA₀ hlogc
    heq1 (ε := 2 * π * ε) (by positivity)
  obtain ⟨δ1, hδ1, h1⟩ := uniform_end_limit hS (Wmat P A) (Wmat P A₀) hZA hZA₀ hR hneA hneA₀
    (φ := fun _ => 1) continuousOn_const heq1 (ε := π) Real.pi_pos
  refine ⟨min (min δL δ1) (1 / 2), by positivity, fun τ hτ0 hτ c hc => ?_⟩
  have hmin1 := min_le_left (min δL δ1) (1 / 2)
  have hmin2 := min_le_right (min δL δ1) (1 / 2)
  have hminL := min_le_left δL δ1
  have hmin1' := min_le_right δL δ1
  have hτhalf : τ ≤ 1 / 2 := by linarith
  have hτ1 : τ < 1 := by linarith
  have hq : ((τ, c) : ℝ × ℂ) ∈ S := ⟨⟨hτ0.le, hτhalf⟩, hc⟩
  have hq1 : ((0, c) : ℝ × ℂ) ∈ S := ⟨⟨le_rfl, by norm_num⟩, hc⟩
  have habs : |(τ, c).1 - 0| < min (min δL δ1) (1 / 2) := by
    simp only; rw [sub_zero, abs_of_pos hτ0]; linarith
  have hGL := hL (τ, c) hq (by linarith) hq1
  have hG1 := h1 (τ, c) hq (by linarith) hq1
  -- contour representations of the rescaled sums
  have hrep : ∀ B : Matrix (Fin M) (Fin M) ℂ, (B = A ∨ B = A₀) → B.IsHermitian →
      ∀ φ : ℂ → ℂ, DiffContOnCl ℂ φ (ball z₀ R) →
        ((lowerRoots (Matrix.charpoly (Wmat P B (τ, c))).roots).map φ).sum
          = (2 * π * I)⁻¹ * ∮ w in C(z₀, R), φ w * ((Matrix.charpoly (Wmat P B (τ, c))).derivative.eval w
            / (Matrix.charpoly (Wmat P B (τ, c))).eval w) := by
    intro B hB hBh φ hφ
    exact lower_sum_poly _ (Matrix.charpoly_monic _).ne_zero
      (fun w hw => (hroots B hB hBh (τ, c) hq hτ0 w hw).1) hη
      (fun w hw => (hroots B hB hBh (τ, c) hq hτ0 w hw).2) hφ
  -- relation with `Λ_+`
  have hrel : ∀ B : Matrix (Fin M) (Fin M) ℂ, B.IsHermitian →
      ((lowerRoots (Matrix.charpoly (Wmat P B (τ, c))).roots).map Complex.log).sum
        = ((lowerRoots (Rt P B τ c)).card : ℂ) * (Real.log τ : ℂ) + Llo P B τ c := by
    intro B hBh
    rw [roots_Wmat hP.2 hτ0 hτ1, lowerRoots_map_mul _ hτ0,
      sum_log_map_mul _ hτ0 fun y hy h0 => by
        have := (Multiset.mem_filter.mp hy).2; rw [h0] at this; simp at this]
    rfl
  have hcount : ∀ B : Matrix (Fin M) (Fin M) ℂ, B.IsHermitian →
      ((lowerRoots (Matrix.charpoly (Wmat P B (τ, c))).roots).map fun _ => (1 : ℂ)).sum
        = ((lowerRoots (Rt P B τ c)).card : ℂ) := by
    intro B _
    rw [roots_Wmat hP.2 hτ0 hτ1, lowerRoots_map_mul _ hτ0]
    simp
  -- integrability on the circle
  have hint : ∀ B : Matrix (Fin M) (Fin M) ℂ, (B = A ∨ B = A₀) → B.IsHermitian →
      ∀ φ : ℂ → ℂ, ContinuousOn φ (sphere z₀ R) →
        CircleIntegrable (fun w => φ w * ((Matrix.charpoly (Wmat P B (τ, c))).derivative.eval w
          / (Matrix.charpoly (Wmat P B (τ, c))).eval w)) z₀ R := by
    intro B hB hBh φ hφ
    refine ContinuousOn.circleIntegrable hR.le (hφ.mul ?_)
    exact ((Polynomial.continuous _).continuousOn).div ((Polynomial.continuous _).continuousOn)
      fun w hw => hne B hB hBh (τ, c) hq w hw
  -- the count difference vanishes
  have hcnt : ((lowerRoots (Rt P A τ c)).card : ℂ) = ((lowerRoots (Rt P A₀ τ c)).card : ℂ) := by
    have hd := hcount A hA
    have hd₀ := hcount A₀ hA₀
    rw [hrep A (Or.inl rfl) hA _ diffContOnCl_const] at hd
    rw [hrep A₀ (Or.inr rfl) hA₀ _ diffContOnCl_const] at hd₀
    have hdiff : ((lowerRoots (Rt P A τ c)).card : ℂ) - ((lowerRoots (Rt P A₀ τ c)).card : ℂ)
        = (2 * π * I)⁻¹ * ∮ w in C(z₀, R), (fun _ => (1 : ℂ)) w
          * ((Matrix.charpoly (Wmat P A (τ, c))).derivative.eval w
            / (Matrix.charpoly (Wmat P A (τ, c))).eval w
          - (Matrix.charpoly (Wmat P A₀ (τ, c))).derivative.eval w
            / (Matrix.charpoly (Wmat P A₀ (τ, c))).eval w) := by
      rw [← hd, ← hd₀, ← mul_sub, ← circleIntegral.integral_sub
        (hint A (Or.inl rfl) hA _ continuousOn_const) (hint A₀ (Or.inr rfl) hA₀ _ continuousOn_const)]
      congr 2
      funext w
      ring
    have hsmall : ‖((lowerRoots (Rt P A τ c)).card : ℂ) - ((lowerRoots (Rt P A₀ τ c)).card : ℂ)‖ < 1 := by
      rw [hdiff, norm_mul, norm_inv]
      have h2pi : ‖(2 * π * I : ℂ)‖ = 2 * π := by
        simp [abs_of_pos Real.pi_pos]
      rw [h2pi]
      have := hG1
      calc (2 * π)⁻¹ * _ < (2 * π)⁻¹ * π := by
            gcongr
        _ < 1 := by
            rw [inv_mul_lt_iff₀ (by positivity)]; linarith [Real.pi_pos]
    have hint' := int_cast_eq_zero_of_norm_lt (n := ((lowerRoots (Rt P A τ c)).card : ℤ)
      - ((lowerRoots (Rt P A₀ τ c)).card : ℤ)) (by push_cast; exact hsmall)
    have : ((lowerRoots (Rt P A τ c)).card : ℤ) = ((lowerRoots (Rt P A₀ τ c)).card : ℤ) :=
      sub_eq_zero.mp hint'
    exact_mod_cast this
  -- conclusion
  have hLA := hrel A hA
  have hLA₀ := hrel A₀ hA₀
  rw [hrep A (Or.inl rfl) hA _ (diffContOnCl_log_lower hη)] at hLA
  rw [hrep A₀ (Or.inr rfl) hA₀ _ (diffContOnCl_log_lower hη)] at hLA₀
  have hdiffL : Llo P A τ c - Llo P A₀ τ c
      = (2 * π * I)⁻¹ * ∮ w in C(z₀, R), Complex.log w
          * ((Matrix.charpoly (Wmat P A (τ, c))).derivative.eval w
            / (Matrix.charpoly (Wmat P A (τ, c))).eval w
          - (Matrix.charpoly (Wmat P A₀ (τ, c))).derivative.eval w
            / (Matrix.charpoly (Wmat P A₀ (τ, c))).eval w) := by
    have e : Llo P A τ c - Llo P A₀ τ c
        = (2 * π * I)⁻¹ * (∮ w in C(z₀, R), Complex.log w
            * ((Matrix.charpoly (Wmat P A (τ, c))).derivative.eval w
              / (Matrix.charpoly (Wmat P A (τ, c))).eval w))
          - (2 * π * I)⁻¹ * (∮ w in C(z₀, R), Complex.log w
            * ((Matrix.charpoly (Wmat P A₀ (τ, c))).derivative.eval w
              / (Matrix.charpoly (Wmat P A₀ (τ, c))).eval w)) := by
      rw [hLA, hLA₀, hcnt]; ring
    rw [e, ← mul_sub, ← circleIntegral.integral_sub
      (hint A (Or.inl rfl) hA _ hlogc) (hint A₀ (Or.inr rfl) hA₀ _ hlogc)]
    congr 2
    funext w
    ring
  rw [hdiffL, norm_mul, norm_inv]
  have h2pi : ‖(2 * π * I : ℂ)‖ = 2 * π := by
    simp [abs_of_pos Real.pi_pos]
  rw [h2pi]
  calc (2 * π)⁻¹ * _ < (2 * π)⁻¹ * (2 * π * ε) := by gcongr
    _ = ε := by field_simp

end EndThm

end OQP27.StripL3b
