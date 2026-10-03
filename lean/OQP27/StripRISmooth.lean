import OQP27.StripRISums

/-!
# Contour representations, regularity and the Burgers identity (module L3b, proof of RI)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

Main results:
* `pencilRoot_norm_bound_all` (**Lemma B(i)**): `|y|² min(τ, 1 - τ)² ≤ ‖A + c‖_F²` for every root;
* `upper_sum_eq_circleIntegral`, `lower_sum_eq_circleIntegral`: the half-plane sums `∑ φ(y)` are
  circle integrals of `φ p'/p` over circles centred at `upCenter`, `loCenter` (eq. (1.1));
* `local_box`: near `(τ₀, c₀) ∈ (0, 1) × ℂ₊` the roots stay in fixed compact parts of `ℂ₊` and `ℂ₋`;
* `upper_global`, `lower_global` (**Lemma C**): on `domRI = (0, 1) × ℂ₊`, `S_±` are holomorphic in `c`
  with jointly continuous derivative, `S_±` and `Λ_±` are continuous, and the Burgers identities
  `∂_τ Λ_± = ∂_c S_±` hold.

Hypotheses: none.
Paper: `iqoqi/programs/oqp27B_all/Q_RI/PROOF.md`, section 1, Lemma B(i) and Lemma C.
-/

namespace OQP27.StripL3b

open Matrix Polynomial Complex Metric Filter Topology Set Real

variable {M : ℕ}

/-! ### Lemma B(i): all roots -/

/-- **Lemma B(i)** (Q_RI).  Every root satisfies `|y|² min(τ, 1 - τ)² ≤ ‖A + c‖_F²`. -/
lemma pencilRoot_norm_bound_all {P A : Matrix (Fin M) (Fin M) ℂ} (hP : IsProj P)
    (hA : A.IsHermitian) {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) (c : ℂ) {y : ℂ}
    (hy : y ∈ pencilRoots P (A + c • 1) τ) :
    ‖y‖ ^ 2 * (min τ (1 - τ)) ^ 2 ≤ frob (A + c • 1) := by
  obtain ⟨v, hv0, hv⟩ := exists_pencil_eigvec hP.2 h0.ne' h1.ne hy
  obtain ⟨-, hQim, hlo, hhi⟩ := root_im_identity hP hA τ c hv
  have hn := re_star_dotProduct_self_pos hv0
  set n := (star v ⬝ᵥ v).re
  set a := (star v ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)).re
  have hQQ := dot_P_sub_mulVec_gen hP τ v
  have hQQre : (star ((P - (τ : ℂ) • 1) *ᵥ v) ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)).re
      = (1 - 2 * τ) * a + τ * (1 - τ) * n := by
    have e1 : (1 - 2 * (τ : ℂ)) = ((1 - 2 * τ : ℝ) : ℂ) := by push_cast; ring
    have e2 : ((τ : ℂ) * (1 - τ)) = ((τ * (1 - τ) : ℝ) : ℂ) := by push_cast; ring
    rw [hQQ, e1, e2, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  have hlow : (min τ (1 - τ)) ^ 2 * n
      ≤ (star ((P - (τ : ℂ) • 1) *ᵥ v) ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)).re := by
    rw [hQQre]
    rcases le_total τ (1 / 2) with hτ | hτ
    · rw [min_eq_left (by linarith)]
      nlinarith
    · rw [min_eq_right (by linarith)]
      nlinarith
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
  have h3 : ‖y‖ ^ 2 * ((min τ (1 - τ)) ^ 2 * n) ≤ frob (A + c • 1) * n :=
    le_trans (mul_le_mul_of_nonneg_left hlow (by positivity)) hle
  have h4 : ‖y‖ ^ 2 * (min τ (1 - τ)) ^ 2 * n ≤ frob (A + c • 1) * n := by linarith
  exact le_of_mul_le_mul_right h4 hn

/-! ### Discs in the half planes -/

/-- Centre of a disc in `ℂ₊` containing `{Im z ≥ η, |z| ≤ ρ}`. -/
noncomputable def upCenter (η ρ : ℝ) : ℂ := ((ρ ^ 2 / η + η + 1 : ℝ) : ℂ) * I

/-- Its radius. -/
noncomputable def upRadius (η ρ : ℝ) : ℝ := ρ ^ 2 / η + η / 2 + 1

lemma upRadius_pos {η ρ : ℝ} (hη : 0 < η) : 0 < upRadius η ρ := by
  unfold upRadius; positivity

lemma dist_upCenter_lt {η ρ : ℝ} (hη : 0 < η) {z : ℂ} (hz : η ≤ z.im) (hzρ : ‖z‖ ≤ ρ) :
    dist z (upCenter η ρ) < upRadius η ρ := by
  have hρ : 0 ≤ ρ := (norm_nonneg z).trans hzρ
  set T := ρ ^ 2 / η + η + 1 with hT
  have hTη : T * η = ρ ^ 2 + η ^ 2 + η := by rw [hT]; field_simp
  rw [dist_eq_norm, upCenter, ← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm,
    Complex.normSq_apply]
  have hR : 0 < upRadius η ρ := upRadius_pos hη
  rw [Real.sqrt_lt' hR]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.sub_im, Complex.mul_im]
  have hz2 : z.re * z.re + z.im * z.im ≤ ρ ^ 2 := by
    have := Complex.sq_norm z
    rw [Complex.normSq_apply] at this
    nlinarith [norm_nonneg z]
  have hR' : upRadius η ρ = T - η / 2 := by rw [upRadius, hT]; ring
  rw [hR']
  nlinarith

lemma im_ge_of_dist_upCenter_le {η ρ : ℝ} (_hη : 0 < η) {z : ℂ}
    (hz : dist z (upCenter η ρ) ≤ upRadius η ρ) : η / 2 ≤ z.im := by
  have h := (Complex.abs_im_le_norm (z - upCenter η ρ)).trans (le_of_eq (dist_eq_norm _ _).symm)
  have h2 : (z - upCenter η ρ).im = z.im - (ρ ^ 2 / η + η + 1) := by
    simp only [upCenter, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, zero_mul, add_zero]
  rw [h2] at h
  have := (abs_le.mp (h.trans hz)).1
  unfold upRadius at this
  linarith

/-- Centre of a disc in `ℂ₋` containing `{Im z ≤ -η, |z| ≤ ρ}`. -/
noncomputable def loCenter (η ρ : ℝ) : ℂ := -upCenter η ρ

lemma dist_loCenter_lt {η ρ : ℝ} (hη : 0 < η) {z : ℂ} (hz : z.im ≤ -η) (hzρ : ‖z‖ ≤ ρ) :
    dist z (loCenter η ρ) < upRadius η ρ := by
  have h := dist_upCenter_lt (ρ := ρ) hη (z := -z) (by simp only [Complex.neg_im]; linarith)
    (by rwa [norm_neg])
  rw [loCenter, dist_eq_norm] at *
  rw [show z - -upCenter η ρ = -(-z - upCenter η ρ) by ring, norm_neg]
  exact h

lemma im_le_of_dist_loCenter_le {η ρ : ℝ} (hη : 0 < η) {z : ℂ}
    (hz : dist z (loCenter η ρ) ≤ upRadius η ρ) : z.im ≤ -(η / 2) := by
  have h := im_ge_of_dist_upCenter_le hη (z := -z) (ρ := ρ) (by
    rw [loCenter, dist_eq_norm] at hz
    rw [dist_eq_norm, show -z - upCenter η ρ = -(z - -upCenter η ρ) by ring, norm_neg]
    exact hz)
  simp at h
  linarith


/-! ### Contour representation of the half-plane root sums -/

section Rep

variable {P A : Matrix (Fin M) (Fin M) ℂ}

lemma Rt_eq_roots (hP : IsProj P) (A : Matrix (Fin M) (Fin M) ℂ) {τ : ℝ} (h0 : 0 < τ)
    (h1 : τ < 1) (c : ℂ) : (penPoly P A τ c).roots = Rt P A τ c :=
  roots_penPoly hP.2 A h0.ne' h1.ne c

/-- If the upper roots lie in `{Im ≥ η, |y| ≤ ρ}`, their `φ`-sum is a circle integral. -/
theorem upper_sum_eq_circleIntegral (hP : IsProj P) (hA : A.IsHermitian) {τ : ℝ} (h0 : 0 < τ)
    (h1 : τ < 1) {c : ℂ} (hc : 0 < c.im) {η ρ : ℝ} (hη : 0 < η)
    (hup : ∀ y ∈ Rt P A τ c, 0 < y.im → η ≤ y.im ∧ ‖y‖ ≤ ρ) {φ : ℂ → ℂ}
    (hφ : DiffContOnCl ℂ φ (ball (upCenter η ρ) (upRadius η ρ))) :
    ((upperRoots (Rt P A τ c)).map φ).sum
      = (2 * π * I)⁻¹ * ∮ z in C(upCenter η ρ, upRadius η ρ),
          φ z * ((penPoly P A τ c).derivative.eval z / (penPoly P A τ c).eval z) := by
  have hne := penPoly_ne_zero hP.2 A h0.ne' h1.ne c
  have hRt := Rt_eq_roots hP A h0 h1 c
  have him := Rt_im_ne_zero hP hA h0 h1 hc
  have hiff : ∀ a ∈ Rt P A τ c, dist a (upCenter η ρ) < upRadius η ρ ↔ 0 < a.im := by
    intro a ha
    constructor
    · intro hd
      have := im_ge_of_dist_upCenter_le (ρ := ρ) hη hd.le
      linarith
    · intro hpos
      obtain ⟨h1', h2'⟩ := hup a ha hpos
      exact dist_upCenter_lt hη h1' h2'
  have hdist : ∀ a ∈ (penPoly P A τ c).roots, dist a (upCenter η ρ) ≠ upRadius η ρ := by
    intro a ha heq
    rw [hRt] at ha
    rcases lt_or_gt_of_ne (him a ha) with hneg | hpos
    · have := im_ge_of_dist_upCenter_le (ρ := ρ) hη heq.le
      linarith
    · have := (hiff a ha).mpr hpos
      linarith
  rw [circleIntegral_mul_logDeriv _ hne (upRadius_pos hη) hdist hφ]
  have hfilter : (penPoly P A τ c).roots.filter (fun a => dist a (upCenter η ρ) < upRadius η ρ)
      = upperRoots (Rt P A τ c) := by
    rw [hRt, upperRoots]
    exact Multiset.filter_congr hiff
  rw [hfilter, ← mul_assoc, inv_mul_cancel₀ (by simp [Real.pi_ne_zero, I_ne_zero]), one_mul]

/-- If the lower roots lie in `{Im ≤ -η, |y| ≤ ρ}`, their `φ`-sum is a circle integral. -/
theorem lower_sum_eq_circleIntegral (hP : IsProj P) (hA : A.IsHermitian) {τ : ℝ} (h0 : 0 < τ)
    (h1 : τ < 1) {c : ℂ} (hc : 0 < c.im) {η ρ : ℝ} (hη : 0 < η)
    (hlo : ∀ y ∈ Rt P A τ c, y.im < 0 → y.im ≤ -η ∧ ‖y‖ ≤ ρ) {φ : ℂ → ℂ}
    (hφ : DiffContOnCl ℂ φ (ball (loCenter η ρ) (upRadius η ρ))) :
    ((lowerRoots (Rt P A τ c)).map φ).sum
      = (2 * π * I)⁻¹ * ∮ z in C(loCenter η ρ, upRadius η ρ),
          φ z * ((penPoly P A τ c).derivative.eval z / (penPoly P A τ c).eval z) := by
  have hne := penPoly_ne_zero hP.2 A h0.ne' h1.ne c
  have hRt := Rt_eq_roots hP A h0 h1 c
  have him := Rt_im_ne_zero hP hA h0 h1 hc
  have hiff : ∀ a ∈ Rt P A τ c, dist a (loCenter η ρ) < upRadius η ρ ↔ a.im < 0 := by
    intro a ha
    constructor
    · intro hd
      have := im_le_of_dist_loCenter_le (ρ := ρ) hη hd.le
      linarith
    · intro hneg
      obtain ⟨h1', h2'⟩ := hlo a ha hneg
      exact dist_loCenter_lt hη h1' h2'
  have hdist : ∀ a ∈ (penPoly P A τ c).roots, dist a (loCenter η ρ) ≠ upRadius η ρ := by
    intro a ha heq
    rw [hRt] at ha
    rcases lt_or_gt_of_ne (him a ha) with hneg | hpos
    · have := (hiff a ha).mpr hneg
      linarith
    · have := im_le_of_dist_loCenter_le (ρ := ρ) hη heq.le
      linarith
  rw [circleIntegral_mul_logDeriv _ hne (upRadius_pos hη) hdist hφ]
  have hfilter : (penPoly P A τ c).roots.filter (fun a => dist a (loCenter η ρ) < upRadius η ρ)
      = lowerRoots (Rt P A τ c) := by
    rw [hRt, lowerRoots]
    exact Multiset.filter_congr hiff
  rw [hfilter, ← mul_assoc, inv_mul_cancel₀ (by simp [Real.pi_ne_zero, I_ne_zero]), one_mul]

lemma diffContOnCl_log_upper {η ρ : ℝ} (hη : 0 < η) :
    DiffContOnCl ℂ Complex.log (ball (upCenter η ρ) (upRadius η ρ)) := by
  refine DifferentiableOn.diffContOnCl_ball (U := closedBall (upCenter η ρ) (upRadius η ρ)) ?_
    subset_rfl
  intro z hz
  have := im_ge_of_dist_upCenter_le hη (mem_closedBall.mp hz)
  exact (Complex.differentiableAt_log (Or.inr (by linarith))).differentiableWithinAt

lemma diffContOnCl_log_lower {η ρ : ℝ} (hη : 0 < η) :
    DiffContOnCl ℂ Complex.log (ball (loCenter η ρ) (upRadius η ρ)) := by
  refine DifferentiableOn.diffContOnCl_ball (U := closedBall (loCenter η ρ) (upRadius η ρ)) ?_
    subset_rfl
  intro z hz
  have := im_le_of_dist_loCenter_le hη (mem_closedBall.mp hz)
  exact (Complex.differentiableAt_log (Or.inr (by linarith))).differentiableWithinAt

/-- **Local box.**  Around `(τ₀, c₀) ∈ (0, 1) × ℂ₊` the roots stay in fixed compact parts of the
two half planes: upper roots in `{Im ≥ η, |y| ≤ ρ}`, lower roots in `{Im ≤ -η, |y| ≤ ρ}`. -/
theorem local_box (hP : IsProj P) (hA : A.IsHermitian) {τ₀ : ℝ} (h0 : 0 < τ₀) (h1 : τ₀ < 1)
    {c₀ : ℂ} (hc₀ : 0 < c₀.im) :
    ∃ δ r η ρ : ℝ, 0 < δ ∧ 0 < r ∧ 0 < η ∧
      (∀ τ ∈ Icc (τ₀ - δ) (τ₀ + δ), 0 < τ ∧ τ < 1) ∧
      (∀ c ∈ closedBall c₀ r, η ≤ c.im) ∧
      ∀ τ ∈ Icc (τ₀ - δ) (τ₀ + δ), ∀ c ∈ closedBall c₀ r, ∀ y ∈ Rt P A τ c,
        (0 < y.im → η ≤ y.im ∧ ‖y‖ ≤ ρ) ∧ (y.im < 0 → y.im ≤ -η ∧ ‖y‖ ≤ ρ) := by
  set m := min τ₀ (1 - τ₀) with hm
  have hm0 : 0 < m := lt_min h0 (by linarith)
  set δ := m / 2 with hδ
  set r := c₀.im / 2 with hr
  have hcont : ContinuousOn (fun c : ℂ => frob (A + c • (1 : Matrix (Fin M) (Fin M) ℂ)))
      (closedBall c₀ r) := by
    apply Continuous.continuousOn
    unfold frob
    fun_prop
  obtain ⟨K, hK⟩ := (isCompact_closedBall c₀ r).exists_bound_of_continuousOn hcont
  refine ⟨δ, r, r, √(max K 0) / (m / 2), by positivity, by positivity, by positivity, ?_, ?_, ?_⟩
  · intro τ hτ
    have hm1 : m ≤ τ₀ := min_le_left _ _
    have hm2 : m ≤ 1 - τ₀ := min_le_right _ _
    constructor <;> linarith [hτ.1, hτ.2]
  · intro c hc
    have := (Complex.abs_im_le_norm (c - c₀)).trans (le_of_eq (dist_eq_norm c c₀).symm)
    rw [Complex.sub_im] at this
    have := (abs_le.mp (this.trans (mem_closedBall.mp hc))).1
    linarith
  · intro τ hτ c hc y hy
    have hm1 : m ≤ τ₀ := min_le_left _ _
    have hm2 : m ≤ 1 - τ₀ := min_le_right _ _
    have hτ0 : 0 < τ := by linarith [hτ.1]
    have hτ1 : τ < 1 := by linarith [hτ.2]
    have hcim : r ≤ c.im := by
      have := (Complex.abs_im_le_norm (c - c₀)).trans (le_of_eq (dist_eq_norm c c₀).symm)
      rw [Complex.sub_im] at this
      have := (abs_le.mp (this.trans (mem_closedBall.mp hc))).1
      linarith
    have hcpos : 0 < c.im := lt_of_lt_of_le (by positivity) hcim
    obtain ⟨-, hup, hlo⟩ := pencilRoot_im_bounds hP hA hτ0 hτ1 hcpos hy
    -- norm bound
    have hB := pencilRoot_norm_bound_all hP hA hτ0 hτ1 c hy
    have hmin : m / 2 ≤ min τ (1 - τ) := le_min (by linarith [hτ.1]) (by linarith [hτ.2])
    have hKc : frob (A + c • 1) ≤ max K 0 := by
      have := hK c hc
      rw [Real.norm_eq_abs, abs_of_nonneg (frob_nonneg _)] at this
      exact this.trans (le_max_left _ _)
    have hnorm : ‖y‖ ≤ √(max K 0) / (m / 2) := by
      rw [le_div_iff₀ (by positivity), ← Real.sqrt_sq (norm_nonneg y),
        ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ m / 2), ← Real.sqrt_mul (sq_nonneg _)]
      apply Real.sqrt_le_sqrt
      calc ‖y‖ ^ 2 * (m / 2) ^ 2 ≤ ‖y‖ ^ 2 * (min τ (1 - τ)) ^ 2 := by gcongr
        _ ≤ frob (A + c • 1) := hB
        _ ≤ max K 0 := hKc
    refine ⟨fun hpos => ⟨?_, hnorm⟩, fun hneg => ⟨?_, hnorm⟩⟩
    · have := hup hpos
      nlinarith
    · have := hlo hneg
      nlinarith

end Rep


/-! ### Joint continuity and parameter derivatives of the log-derivative -/

section Reg

variable {P A : Matrix (Fin M) (Fin M) ℂ}

lemma continuous_penVal (P A : Matrix (Fin M) (Fin M) ℂ) (j : ℕ) :
    Continuous fun q : ℝ × ℂ => penVal P A j q.1 q.2 := by
  unfold penVal
  exact (Polynomial.continuous _).comp (by fun_prop)

lemma continuous_penValD (P A : Matrix (Fin M) (Fin M) ℂ) (j : ℕ) :
    Continuous fun q : ℝ × ℂ => penValD P A j q.1 q.2 := by
  unfold penValD
  exact (Polynomial.continuous _).comp (by fun_prop)

lemma continuous_lagrange_eval (v : ℕ → ℝ × ℂ → ℂ) (hv : ∀ j, Continuous (v j)) (Q : ℕ → ℂ[X]) :
    Continuous fun p : (ℝ × ℂ) × ℂ => (∑ j ∈ lagNodes M, C (v j p.1) * Q j).eval p.2 := by
  simp only [eval_finsetSum, eval_mul, eval_C]
  exact continuous_finsetSum _ fun j _ =>
    ((hv j).comp continuous_fst).mul ((Q j).continuous.comp continuous_snd)

lemma continuous_eval_penPoly (P A : Matrix (Fin M) (Fin M) ℂ) :
    Continuous fun p : (ℝ × ℂ) × ℂ => (penPoly P A p.1.1 p.1.2).eval p.2 := by
  have h : (fun p : (ℝ × ℂ) × ℂ => (penPoly P A p.1.1 p.1.2).eval p.2)
      = fun p => (∑ j ∈ lagNodes M, C (penVal P A j p.1.1 p.1.2) * lagBasis M j).eval p.2 := by
    funext p; rw [penPoly_eq_lagrange]
  rw [h]
  exact continuous_lagrange_eval (fun j q => penVal P A j q.1 q.2) (continuous_penVal P A) _

lemma continuous_eval_penPoly_deriv (P A : Matrix (Fin M) (Fin M) ℂ) :
    Continuous fun p : (ℝ × ℂ) × ℂ => (penPoly P A p.1.1 p.1.2).derivative.eval p.2 := by
  have h : (fun p : (ℝ × ℂ) × ℂ => (penPoly P A p.1.1 p.1.2).derivative.eval p.2)
      = fun p => (∑ j ∈ lagNodes M, C (penVal P A j p.1.1 p.1.2)
          * (lagBasis M j).derivative).eval p.2 := by
    funext p
    rw [penPoly_eq_lagrange]
    simp only [derivative_sum, derivative_mul, derivative_C, zero_mul, zero_add]
  rw [h]
  exact continuous_lagrange_eval (fun j q => penVal P A j q.1 q.2) (continuous_penVal P A) _

lemma continuous_eval_penPolyDc (P A : Matrix (Fin M) (Fin M) ℂ) :
    Continuous fun p : (ℝ × ℂ) × ℂ => (penPolyDc P A p.1.1 p.1.2).eval p.2 :=
  continuous_lagrange_eval (fun j q => penValD P A j q.1 q.2) (continuous_penValD P A) _

lemma continuous_eval_penPolyDc_deriv (P A : Matrix (Fin M) (Fin M) ℂ) :
    Continuous fun p : (ℝ × ℂ) × ℂ => (penPolyDc P A p.1.1 p.1.2).derivative.eval p.2 := by
  have h : (fun p : (ℝ × ℂ) × ℂ => (penPolyDc P A p.1.1 p.1.2).derivative.eval p.2)
      = fun p => (∑ j ∈ lagNodes M, C (penValD P A j p.1.1 p.1.2)
          * (lagBasis M j).derivative).eval p.2 := by
    funext p
    simp only [penPolyDc, derivative_sum, derivative_mul, derivative_C, zero_mul, zero_add]
  rw [h]
  exact continuous_lagrange_eval (fun j q => penValD P A j q.1 q.2) (continuous_penValD P A) _

/-- `(q/p)'(z) = (q'(z) p(z) - q(z) p'(z)) / p(z)²`. -/
noncomputable def ratDeriv (p q : ℂ[X]) (z : ℂ) : ℂ :=
  (q.derivative.eval z * p.eval z - q.eval z * p.derivative.eval z) / (p.eval z) ^ 2

lemma hasDerivAt_ratio (p q : ℂ[X]) {z : ℂ} (hz : p.eval z ≠ 0) :
    HasDerivAt (fun z => q.eval z / p.eval z) (ratDeriv p q z) z :=
  (q.hasDerivAt z).div (p.hasDerivAt z) hz

/-- `∂_c (f'/f) = ratDeriv f (D_c f)`. -/
lemma hasDerivAt_logDeriv_c (P A : Matrix (Fin M) (Fin M) ℂ) (τ : ℝ) (c z : ℂ)
    (hz : (penPoly P A τ c).eval z ≠ 0) :
    HasDerivAt (fun c => (penPoly P A τ c).derivative.eval z / (penPoly P A τ c).eval z)
      (ratDeriv (penPoly P A τ c) (penPolyDc P A τ c) z) c := by
  refine ((hasDerivAt_penPoly_c' P A τ c z).div (hasDerivAt_penPoly_c P A τ c z) hz).congr_deriv ?_
  unfold ratDeriv
  ring

/-- `∂_τ (f'/f) = ratDeriv f (D_τ f)`. -/
lemma hasDerivAt_logDeriv_t (P A : Matrix (Fin M) (Fin M) ℂ) (τ : ℝ) (c z : ℂ)
    (hz : (penPoly P A τ c).eval z ≠ 0) :
    HasDerivAt (fun τ : ℝ => (penPoly P A τ c).derivative.eval z / (penPoly P A τ c).eval z)
      (ratDeriv (penPoly P A τ c) (penPolyDt P A τ c) z) τ := by
  refine ((hasDerivAt_penPoly_t' P A τ c z).div (hasDerivAt_penPoly_t P A τ c z) hz).congr_deriv ?_
  unfold ratDeriv
  ring

/-- **The Burgers identity at the level of integrands**: with `u = D_c f / f`,
`log z · ∂_τ(f'/f) - z · ∂_c(f'/f) = ((z log z - z) u)'`. -/
lemma hasDerivAt_burgers (P A : Matrix (Fin M) (Fin M) ℂ) (τ : ℝ) (c z : ℂ)
    (hz : (penPoly P A τ c).eval z ≠ 0) (hzs : z ∈ slitPlane) :
    HasDerivAt (fun z => (z * Complex.log z - z)
        * ((penPolyDc P A τ c).eval z / (penPoly P A τ c).eval z))
      (Complex.log z * ratDeriv (penPoly P A τ c) (penPolyDt P A τ c) z
        - z * ratDeriv (penPoly P A τ c) (penPolyDc P A τ c) z) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hzs
  have hlog := Complex.hasDerivAt_log hzs
  have h1 : HasDerivAt (fun z => z * Complex.log z - z) (Complex.log z) z := by
    refine (((hasDerivAt_id' z).mul hlog).sub (hasDerivAt_id' z)).congr_deriv ?_
    field_simp
    ring
  have h2 := hasDerivAt_ratio (penPoly P A τ c) (penPolyDc P A τ c) hz
  refine (h1.mul h2).congr_deriv ?_
  rw [penPolyDt_eq]
  unfold ratDeriv
  simp only [derivative_mul, derivative_X, one_mul, eval_add, eval_mul, eval_X]
  field_simp
  ring

end Reg


/-! ### Local regularity of the root sums; the Burgers identity -/

section LocalReg

variable {P A : Matrix (Fin M) (Fin M) ℂ}

/-- `z f'(z)/f(z)`. -/
noncomputable def intS (P A : Matrix (Fin M) (Fin M) ℂ) (q : ℝ × ℂ) (z : ℂ) : ℂ :=
  z * ((penPoly P A q.1 q.2).derivative.eval z / (penPoly P A q.1 q.2).eval z)

/-- `log z f'(z)/f(z)`. -/
noncomputable def intL (P A : Matrix (Fin M) (Fin M) ℂ) (q : ℝ × ℂ) (z : ℂ) : ℂ :=
  Complex.log z * ((penPoly P A q.1 q.2).derivative.eval z / (penPoly P A q.1 q.2).eval z)

/-- `z ∂_c(f'/f)(z)`. -/
noncomputable def intSd (P A : Matrix (Fin M) (Fin M) ℂ) (q : ℝ × ℂ) (z : ℂ) : ℂ :=
  z * ratDeriv (penPoly P A q.1 q.2) (penPolyDc P A q.1 q.2) z

/-- `log z ∂_τ(f'/f)(z)`, written with `∂_τ(f'/f) = z ∂_c(f'/f) + D_c f / f`. -/
noncomputable def intLd (P A : Matrix (Fin M) (Fin M) ℂ) (q : ℝ × ℂ) (z : ℂ) : ℂ :=
  Complex.log z * (z * ratDeriv (penPoly P A q.1 q.2) (penPolyDc P A q.1 q.2) z
    + (penPolyDc P A q.1 q.2).eval z / (penPoly P A q.1 q.2).eval z)

lemma ratDeriv_Dt (P A : Matrix (Fin M) (Fin M) ℂ) (τ : ℝ) (c z : ℂ) :
    ratDeriv (penPoly P A τ c) (penPolyDt P A τ c) z
      = z * ratDeriv (penPoly P A τ c) (penPolyDc P A τ c) z
        + (penPolyDc P A τ c).eval z / (penPoly P A τ c).eval z := by
  rw [penPolyDt_eq]
  unfold ratDeriv
  by_cases hz : (penPoly P A τ c).eval z = 0
  · simp [hz]
  · simp only [derivative_mul, derivative_X, one_mul, eval_add, eval_mul, eval_X]
    field_simp
    ring

lemma continuousOn_intS (P A : Matrix (Fin M) (Fin M) ℂ) {S : Set (ℝ × ℂ)} {T : Set ℂ}
    (hne : ∀ q ∈ S, ∀ z ∈ T, (penPoly P A q.1 q.2).eval z ≠ 0) :
    ContinuousOn (fun p : (ℝ × ℂ) × ℂ => intS P A p.1 p.2) (S ×ˢ T) := by
  unfold intS
  exact continuous_snd.continuousOn.mul ((continuous_eval_penPoly_deriv P A).continuousOn.div
    (continuous_eval_penPoly P A).continuousOn fun p hp => hne p.1 hp.1 p.2 hp.2)

lemma continuousOn_intL (P A : Matrix (Fin M) (Fin M) ℂ) {S : Set (ℝ × ℂ)} {T : Set ℂ}
    (hne : ∀ q ∈ S, ∀ z ∈ T, (penPoly P A q.1 q.2).eval z ≠ 0) (hT : ∀ z ∈ T, z ∈ slitPlane) :
    ContinuousOn (fun p : (ℝ × ℂ) × ℂ => intL P A p.1 p.2) (S ×ˢ T) := by
  unfold intL
  refine ContinuousOn.mul (fun p hp => (continuousAt_clog (hT p.2 hp.2)).comp
    continuous_snd.continuousAt |>.continuousWithinAt) ?_
  exact (continuous_eval_penPoly_deriv P A).continuousOn.div
    (continuous_eval_penPoly P A).continuousOn fun p hp => hne p.1 hp.1 p.2 hp.2

lemma continuousOn_ratDeriv (P A : Matrix (Fin M) (Fin M) ℂ) {S : Set (ℝ × ℂ)} {T : Set ℂ}
    (hne : ∀ q ∈ S, ∀ z ∈ T, (penPoly P A q.1 q.2).eval z ≠ 0) :
    ContinuousOn (fun p : (ℝ × ℂ) × ℂ =>
      ratDeriv (penPoly P A p.1.1 p.1.2) (penPolyDc P A p.1.1 p.1.2) p.2) (S ×ˢ T) := by
  unfold ratDeriv
  refine ContinuousOn.div ?_ ?_ fun p hp => pow_ne_zero 2 (hne p.1 hp.1 p.2 hp.2)
  · exact (((continuous_eval_penPolyDc_deriv P A).mul (continuous_eval_penPoly P A)).sub
      ((continuous_eval_penPolyDc P A).mul (continuous_eval_penPoly_deriv P A))).continuousOn
  · exact ((continuous_eval_penPoly P A).pow 2).continuousOn

lemma continuousOn_intSd (P A : Matrix (Fin M) (Fin M) ℂ) {S : Set (ℝ × ℂ)} {T : Set ℂ}
    (hne : ∀ q ∈ S, ∀ z ∈ T, (penPoly P A q.1 q.2).eval z ≠ 0) :
    ContinuousOn (fun p : (ℝ × ℂ) × ℂ => intSd P A p.1 p.2) (S ×ˢ T) := by
  unfold intSd
  exact continuous_snd.continuousOn.mul (continuousOn_ratDeriv P A hne)

lemma continuousOn_intLd (P A : Matrix (Fin M) (Fin M) ℂ) {S : Set (ℝ × ℂ)} {T : Set ℂ}
    (hne : ∀ q ∈ S, ∀ z ∈ T, (penPoly P A q.1 q.2).eval z ≠ 0) (hT : ∀ z ∈ T, z ∈ slitPlane) :
    ContinuousOn (fun p : (ℝ × ℂ) × ℂ => intLd P A p.1 p.2) (S ×ˢ T) := by
  unfold intLd
  refine ContinuousOn.mul (fun p hp => (continuousAt_clog (hT p.2 hp.2)).comp
    continuous_snd.continuousAt |>.continuousWithinAt) ?_
  refine (continuous_snd.continuousOn.mul (continuousOn_ratDeriv P A hne)).add ?_
  exact (continuous_eval_penPolyDc P A).continuousOn.div
    (continuous_eval_penPoly P A).continuousOn fun p hp => hne p.1 hp.1 p.2 hp.2

lemma penPoly_ne_zero_on_sphere (hP : IsProj P) {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) {c : ℂ}
    {z₀ : ℂ} {R : ℝ} (hroot : ∀ y ∈ Rt P A τ c, dist y z₀ ≠ R) :
    ∀ z ∈ sphere z₀ R, (penPoly P A τ c).eval z ≠ 0 := by
  intro z hz h0z
  have hz' : z ∈ Rt P A τ c := by
    rw [← Rt_eq_roots hP A h0 h1 c]
    exact (mem_roots (penPoly_ne_zero hP.2 A h0.ne' h1.ne c)).mpr h0z
  exact hroot z hz' (mem_sphere.mp hz)

/-- Restricting a jointly continuous integrand to a slice `τ = const`. -/
lemma continuousOn_slice_c {G : ℝ × ℂ → ℂ → ℂ} {S : Set (ℝ × ℂ)} {T : Set ℂ}
    (hG : ContinuousOn (fun p : (ℝ × ℂ) × ℂ => G p.1 p.2) (S ×ˢ T)) (τ : ℝ) {U : Set ℂ}
    (hU : ∀ c ∈ U, ((τ, c) : ℝ × ℂ) ∈ S) :
    ContinuousOn (fun p : ℂ × ℂ => G (τ, p.1) p.2) (U ×ˢ T) :=
  hG.comp (f := fun p : ℂ × ℂ => (((τ, p.1) : ℝ × ℂ), p.2)) (by fun_prop)
    fun p hp => ⟨hU p.1 hp.1, hp.2⟩

/-- Restricting a jointly continuous integrand to a slice `c = const`. -/
lemma continuousOn_slice_t {G : ℝ × ℂ → ℂ → ℂ} {S : Set (ℝ × ℂ)} {T : Set ℂ}
    (hG : ContinuousOn (fun p : (ℝ × ℂ) × ℂ => G p.1 p.2) (S ×ˢ T)) (c : ℂ) {U : Set ℝ}
    (hU : ∀ τ ∈ U, ((τ, c) : ℝ × ℂ) ∈ S) :
    ContinuousOn (fun p : ℝ × ℂ => G (p.1, c) p.2) (U ×ˢ T) :=
  hG.comp (f := fun p : ℝ × ℂ => (((p.1, c) : ℝ × ℂ), p.2)) (by fun_prop)
    fun p hp => ⟨hU p.1 hp.1, hp.2⟩

/-- **Generic local regularity.**  If, on a box `[τ₀ - δ, τ₀ + δ] × B̄(c₀, r)`, two functions
`Ssum`, `Lsum` are given by the circle integrals of `z f'/f` and `log z f'/f` over a fixed circle on
which `f` does not vanish, then `Ssum` is holomorphic in `c` with a jointly continuous derivative
`Sd`, and `∂_τ Lsum = Sd` (the Burgers identity, Lemma C of Q_RI). -/
theorem local_reg_generic (P A : Matrix (Fin M) (Fin M) ℂ) {τ₀ δ r : ℝ} {c₀ : ℂ} (_hδ : 0 < δ)
    (_hr : 0 < r) {z₀ : ℂ} {R : ℝ} (hR : 0 < R) (Ssum Lsum : ℝ → ℂ → ℂ)
    (hne : ∀ q ∈ Icc (τ₀ - δ) (τ₀ + δ) ×ˢ closedBall c₀ r, ∀ z ∈ sphere z₀ R,
      (penPoly P A q.1 q.2).eval z ≠ 0)
    (hslit : ∀ z ∈ sphere z₀ R, z ∈ slitPlane)
    (hrepS : ∀ q ∈ Icc (τ₀ - δ) (τ₀ + δ) ×ˢ closedBall c₀ r,
      Ssum q.1 q.2 = (2 * π * I)⁻¹ * ∮ z in C(z₀, R), intS P A q z)
    (hrepL : ∀ q ∈ Icc (τ₀ - δ) (τ₀ + δ) ×ˢ closedBall c₀ r,
      Lsum q.1 q.2 = (2 * π * I)⁻¹ * ∮ z in C(z₀, R), intL P A q z) :
    ∃ Sd : ℝ → ℂ → ℂ,
      ContinuousOn (fun q : ℝ × ℂ => Sd q.1 q.2) (Icc (τ₀ - δ) (τ₀ + δ) ×ˢ closedBall c₀ r) ∧
      ContinuousOn (fun q : ℝ × ℂ => Ssum q.1 q.2) (Icc (τ₀ - δ) (τ₀ + δ) ×ˢ closedBall c₀ r) ∧
      ContinuousOn (fun q : ℝ × ℂ => Lsum q.1 q.2) (Icc (τ₀ - δ) (τ₀ + δ) ×ˢ closedBall c₀ r) ∧
      (∀ τ ∈ Icc (τ₀ - δ) (τ₀ + δ), ∀ c ∈ ball c₀ r,
        HasDerivAt (fun c => Ssum τ c) (Sd τ c) c) ∧
      (∀ τ ∈ Ioo (τ₀ - δ) (τ₀ + δ), ∀ c ∈ closedBall c₀ r,
        HasDerivAt (fun τ => Lsum τ c) (Sd τ c) τ) := by
  set box := Icc (τ₀ - δ) (τ₀ + δ) ×ˢ closedBall c₀ r with hbox
  have hcS := continuousOn_intS P A hne
  have hcL := continuousOn_intL P A hne hslit
  have hcSd := continuousOn_intSd P A hne
  have hcLd := continuousOn_intLd P A hne hslit
  refine ⟨fun τ c => (2 * π * I)⁻¹ * ∮ z in C(z₀, R), intSd P A (τ, c) z, ?_, ?_, ?_, ?_, ?_⟩
  · exact continuousOn_const.mul (continuousOn_circleIntegral (F := intSd P A) hR.le hcSd)
  · exact (continuousOn_const.mul (continuousOn_circleIntegral (F := intS P A) hR.le hcS)).congr
      fun q hq => hrepS q hq
  · exact (continuousOn_const.mul (continuousOn_circleIntegral (F := intL P A) hR.le hcL)).congr
      fun q hq => hrepL q hq
  · -- derivative in `c`
    intro τ hτ c hc
    set ε := (r - dist c c₀) / 2 with hε
    have hε0 : 0 < ε := by have := mem_ball.mp hc; rw [hε]; linarith
    have hsub : ∀ c' ∈ closedBall c ε, ((τ, c') : ℝ × ℂ) ∈ box := by
      intro c' hc'
      refine ⟨hτ, ?_⟩
      rw [mem_closedBall] at hc' ⊢
      have := dist_triangle c' c c₀
      have := mem_ball.mp hc
      linarith
    have key := hasDerivAt_circleIntegral (𝕜 := ℂ) (x₀ := c) (ε := ε) hε0 (z₀ := z₀) hR
      (F := fun c' z => intS P A (τ, c') z) (F' := fun c' z => intSd P A (τ, c') z)
      (fun c' hc' => (continuousOn_slice_c hcS τ (U := {c'})
          (fun c'' h => by rw [mem_singleton_iff.mp h]; exact hsub c' (ball_subset_closedBall hc'))).comp
        (f := fun z : ℂ => (c', z)) (by fun_prop) fun z hz => ⟨rfl, hz⟩)
      (continuousOn_slice_c hcSd τ hsub)
      (fun c' hc' z hz => by
        have h := (hasDerivAt_logDeriv_c P A τ c' z
          (hne _ (hsub c' (ball_subset_closedBall hc')) z hz)).const_mul z
        exact h)
    refine (key.const_mul ((2 * π * I)⁻¹)).congr_of_eventuallyEq ?_
    filter_upwards [ball_mem_nhds c hε0] with c' hc'
    exact hrepS (τ, c') (hsub c' (ball_subset_closedBall hc'))
  · -- derivative in `τ`, and the Burgers identity
    intro τ hτ c hc
    set ε := min (τ - (τ₀ - δ)) (τ₀ + δ - τ) / 2 with hε
    have hε0 : 0 < ε := by
      have := hτ.1; have := hτ.2
      rw [hε]; exact half_pos (lt_min (by linarith) (by linarith))
    have hsub : ∀ t ∈ closedBall τ ε, ((t, c) : ℝ × ℂ) ∈ box := by
      intro t ht
      refine ⟨?_, hc⟩
      rw [mem_closedBall, Real.dist_eq, abs_le] at ht
      have h1' := min_le_left (τ - (τ₀ - δ)) (τ₀ + δ - τ)
      have h2' := min_le_right (τ - (τ₀ - δ)) (τ₀ + δ - τ)
      constructor <;> linarith [ht.1, ht.2]
    have key := hasDerivAt_circleIntegral (𝕜 := ℝ) (x₀ := τ) (ε := ε) hε0 (z₀ := z₀) hR
      (F := fun t z => intL P A (t, c) z) (F' := fun t z => intLd P A (t, c) z)
      (fun t ht => (continuousOn_slice_t hcL c (U := {t})
          (fun t' h => by rw [mem_singleton_iff.mp h]; exact hsub t (ball_subset_closedBall ht))).comp
        (f := fun z : ℂ => (t, z)) (by fun_prop) fun z hz => ⟨rfl, hz⟩)
      (continuousOn_slice_t hcLd c hsub)
      (fun t ht z hz => by
        have h := hasDerivAt_logDeriv_t P A t c z (hne _ (hsub t (ball_subset_closedBall ht)) z hz)
        rw [ratDeriv_Dt] at h
        exact h.const_mul (Complex.log z))
    have hq : ((τ, c) : ℝ × ℂ) ∈ box := hsub τ (mem_closedBall_self hε0.le)
    have hburg : (∮ z in C(z₀, R), intLd P A (τ, c) z) = ∮ z in C(z₀, R), intSd P A (τ, c) z := by
      have hzero := circleIntegral.integral_eq_zero_of_hasDerivWithinAt hR.le
        (f := fun z => (z * Complex.log z - z)
          * ((penPolyDc P A τ c).eval z / (penPoly P A τ c).eval z))
        (f' := fun z => intLd P A (τ, c) z - intSd P A (τ, c) z)
        fun z hz => by
          have h := hasDerivAt_burgers P A τ c z (hne _ hq z hz) (hslit z hz)
          rw [ratDeriv_Dt] at h
          exact h.hasDerivWithinAt
      have hc1 : ContinuousOn (fun z => intLd P A (τ, c) z) (sphere z₀ R) :=
        hcLd.comp (f := fun z : ℂ => (((τ, c) : ℝ × ℂ), z)) (by fun_prop) fun z hz => ⟨hq, hz⟩
      have hc2 : ContinuousOn (fun z => intSd P A (τ, c) z) (sphere z₀ R) :=
        hcSd.comp (f := fun z : ℂ => (((τ, c) : ℝ × ℂ), z)) (by fun_prop) fun z hz => ⟨hq, hz⟩
      rw [circleIntegral.integral_sub (hc1.circleIntegrable hR.le) (hc2.circleIntegrable hR.le)]
        at hzero
      exact sub_eq_zero.mp hzero
    have key' := key.const_mul ((2 * π * I)⁻¹)
    rw [hburg] at key'
    refine key'.congr_of_eventuallyEq ?_
    filter_upwards [ball_mem_nhds τ hε0] with t ht
    exact hrepL (t, c) (hsub t (ball_subset_closedBall ht))

end LocalReg


/-! ### Upper and lower local regularity, and the global statements -/

section Global

variable {P A : Matrix (Fin M) (Fin M) ℂ}

/-- The open domain `(0, 1) × ℂ₊`. -/
def domRI : Set (ℝ × ℂ) := Ioo 0 1 ×ˢ {c : ℂ | 0 < c.im}

lemma isOpen_domRI : IsOpen domRI :=
  isOpen_Ioo.prod (isOpen_lt continuous_const Complex.continuous_im)

/-- Local data in `ℂ₊` or `ℂ₋`: the conclusion of `local_reg_generic` around `(τ₀, c₀)`. -/
def LocalData (Ssum Lsum : ℝ → ℂ → ℂ) (τ₀ : ℝ) (c₀ : ℂ) : Prop :=
  ∃ δ r : ℝ, 0 < δ ∧ 0 < r ∧ ∃ Sd : ℝ → ℂ → ℂ,
    ContinuousOn (fun q : ℝ × ℂ => Sd q.1 q.2) (Icc (τ₀ - δ) (τ₀ + δ) ×ˢ closedBall c₀ r) ∧
    ContinuousOn (fun q : ℝ × ℂ => Ssum q.1 q.2) (Icc (τ₀ - δ) (τ₀ + δ) ×ˢ closedBall c₀ r) ∧
    ContinuousOn (fun q : ℝ × ℂ => Lsum q.1 q.2) (Icc (τ₀ - δ) (τ₀ + δ) ×ˢ closedBall c₀ r) ∧
    (∀ τ ∈ Icc (τ₀ - δ) (τ₀ + δ), ∀ c ∈ ball c₀ r, HasDerivAt (fun c => Ssum τ c) (Sd τ c) c) ∧
    (∀ τ ∈ Ioo (τ₀ - δ) (τ₀ + δ), ∀ c ∈ closedBall c₀ r,
      HasDerivAt (fun τ => Lsum τ c) (Sd τ c) τ)

theorem upper_local (hP : IsProj P) (hA : A.IsHermitian) {τ₀ : ℝ} (h0 : 0 < τ₀) (h1 : τ₀ < 1)
    {c₀ : ℂ} (hc₀ : 0 < c₀.im) : LocalData (Sup P A) (Lup P A) τ₀ c₀ := by
  obtain ⟨δ, r, η, ρ, hδ, hr, hη, hτbox, hcim, hroots⟩ := local_box hP hA h0 h1 hc₀
  have hR : 0 < upRadius η ρ := upRadius_pos hη
  have hup : ∀ q ∈ Icc (τ₀ - δ) (τ₀ + δ) ×ˢ closedBall c₀ r, ∀ y ∈ Rt P A q.1 q.2,
      0 < y.im → η ≤ y.im ∧ ‖y‖ ≤ ρ :=
    fun q hq y hy => (hroots q.1 hq.1 q.2 hq.2 y hy).1
  have hdist : ∀ q ∈ Icc (τ₀ - δ) (τ₀ + δ) ×ˢ closedBall c₀ r, ∀ y ∈ Rt P A q.1 q.2,
      dist y (upCenter η ρ) ≠ upRadius η ρ := by
    intro q hq y hy heq
    have him := im_ge_of_dist_upCenter_le (ρ := ρ) hη heq.le
    obtain ⟨h1', h2'⟩ := hup q hq y hy (by linarith)
    have := dist_upCenter_lt hη h1' h2'
    rw [heq] at this
    exact lt_irrefl _ this
  refine ⟨δ, r, hδ, hr, ?_⟩
  refine local_reg_generic P A hδ hr hR (Sup P A) (Lup P A)
    (fun q hq => penPoly_ne_zero_on_sphere hP (hτbox q.1 hq.1).1 (hτbox q.1 hq.1).2 (hdist q hq))
    (fun z hz => Or.inr (by
      have := im_ge_of_dist_upCenter_le (ρ := ρ) hη (mem_sphere.mp hz).le; linarith))
    (fun q hq => ?_) (fun q hq => ?_)
  · have := upper_sum_eq_circleIntegral hP hA (hτbox q.1 hq.1).1 (hτbox q.1 hq.1).2
      (lt_of_lt_of_le hη (hcim q.2 hq.2)) hη (hup q hq) (φ := fun z => z)
      differentiable_id.diffContOnCl
    simpa [Sup, intS] using this
  · exact upper_sum_eq_circleIntegral hP hA (hτbox q.1 hq.1).1 (hτbox q.1 hq.1).2
      (lt_of_lt_of_le hη (hcim q.2 hq.2)) hη (hup q hq) (diffContOnCl_log_upper hη)

theorem lower_local (hP : IsProj P) (hA : A.IsHermitian) {τ₀ : ℝ} (h0 : 0 < τ₀) (h1 : τ₀ < 1)
    {c₀ : ℂ} (hc₀ : 0 < c₀.im) : LocalData (Slo P A) (Llo P A) τ₀ c₀ := by
  obtain ⟨δ, r, η, ρ, hδ, hr, hη, hτbox, hcim, hroots⟩ := local_box hP hA h0 h1 hc₀
  have hR : 0 < upRadius η ρ := upRadius_pos hη
  have hlo : ∀ q ∈ Icc (τ₀ - δ) (τ₀ + δ) ×ˢ closedBall c₀ r, ∀ y ∈ Rt P A q.1 q.2,
      y.im < 0 → y.im ≤ -η ∧ ‖y‖ ≤ ρ :=
    fun q hq y hy => (hroots q.1 hq.1 q.2 hq.2 y hy).2
  have hdist : ∀ q ∈ Icc (τ₀ - δ) (τ₀ + δ) ×ˢ closedBall c₀ r, ∀ y ∈ Rt P A q.1 q.2,
      dist y (loCenter η ρ) ≠ upRadius η ρ := by
    intro q hq y hy heq
    have him := im_le_of_dist_loCenter_le (ρ := ρ) hη heq.le
    obtain ⟨h1', h2'⟩ := hlo q hq y hy (by linarith)
    have := dist_loCenter_lt hη h1' h2'
    rw [heq] at this
    exact lt_irrefl _ this
  refine ⟨δ, r, hδ, hr, ?_⟩
  refine local_reg_generic P A hδ hr hR (Slo P A) (Llo P A)
    (fun q hq => penPoly_ne_zero_on_sphere hP (hτbox q.1 hq.1).1 (hτbox q.1 hq.1).2 (hdist q hq))
    (fun z hz => Or.inr (by
      have := im_le_of_dist_loCenter_le (ρ := ρ) hη (mem_sphere.mp hz).le; linarith))
    (fun q hq => ?_) (fun q hq => ?_)
  · have := lower_sum_eq_circleIntegral hP hA (hτbox q.1 hq.1).1 (hτbox q.1 hq.1).2
      (lt_of_lt_of_le hη (hcim q.2 hq.2)) hη (hlo q hq) (φ := fun z => z)
      differentiable_id.diffContOnCl
    simpa [Slo, intS] using this
  · exact lower_sum_eq_circleIntegral hP hA (hτbox q.1 hq.1).1 (hτbox q.1 hq.1).2
      (lt_of_lt_of_le hη (hcim q.2 hq.2)) hη (hlo q hq) (diffContOnCl_log_lower hη)

/-- From local data everywhere on `domRI` to global statements. -/
theorem global_of_local {Ssum Lsum : ℝ → ℂ → ℂ}
    (hloc : ∀ q ∈ domRI, LocalData Ssum Lsum q.1 q.2) :
    (∀ q ∈ domRI, HasDerivAt (fun c => Ssum q.1 c) (deriv (fun c => Ssum q.1 c) q.2) q.2) ∧
    (∀ q ∈ domRI, HasDerivAt (fun τ => Lsum τ q.2) (deriv (fun c => Ssum q.1 c) q.2) q.1) ∧
    ContinuousOn (fun q : ℝ × ℂ => deriv (fun c => Ssum q.1 c) q.2) domRI ∧
    ContinuousOn (fun q : ℝ × ℂ => Ssum q.1 q.2) domRI ∧
    ContinuousOn (fun q : ℝ × ℂ => Lsum q.1 q.2) domRI := by
  -- the basic facts at a point
  have hpt : ∀ q ∈ domRI, ∃ δ r : ℝ, 0 < δ ∧ 0 < r ∧ ∃ Sd : ℝ → ℂ → ℂ,
      ContinuousOn (fun q' : ℝ × ℂ => Sd q'.1 q'.2) (Icc (q.1 - δ) (q.1 + δ) ×ˢ closedBall q.2 r) ∧
      ContinuousOn (fun q' : ℝ × ℂ => Ssum q'.1 q'.2) (Icc (q.1 - δ) (q.1 + δ) ×ˢ closedBall q.2 r) ∧
      ContinuousOn (fun q' : ℝ × ℂ => Lsum q'.1 q'.2) (Icc (q.1 - δ) (q.1 + δ) ×ˢ closedBall q.2 r) ∧
      (∀ τ ∈ Icc (q.1 - δ) (q.1 + δ), ∀ c ∈ ball q.2 r,
        HasDerivAt (fun c => Ssum τ c) (Sd τ c) c) ∧
      (∀ τ ∈ Ioo (q.1 - δ) (q.1 + δ), ∀ c ∈ closedBall q.2 r,
        HasDerivAt (fun τ => Lsum τ c) (Sd τ c) τ) := fun q hq => hloc q hq
  have hbox_nhds : ∀ (q : ℝ × ℂ) (δ r : ℝ), 0 < δ → 0 < r →
      Icc (q.1 - δ) (q.1 + δ) ×ˢ closedBall q.2 r ∈ 𝓝 q := by
    intro q δ r hδ hr
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod (Icc_mem_nhds (by linarith) (by linarith))
      (closedBall_mem_nhds q.2 hr)
  have hderiv_eq : ∀ q ∈ domRI, ∃ δ r : ℝ, 0 < δ ∧ 0 < r ∧ ∃ Sd : ℝ → ℂ → ℂ,
      ContinuousOn (fun q' : ℝ × ℂ => Sd q'.1 q'.2) (Icc (q.1 - δ) (q.1 + δ) ×ˢ closedBall q.2 r) ∧
      (∀ q' ∈ Ioo (q.1 - δ) (q.1 + δ) ×ˢ ball q.2 r, deriv (fun c => Ssum q'.1 c) q'.2 = Sd q'.1 q'.2) ∧
      (∀ τ ∈ Ioo (q.1 - δ) (q.1 + δ), ∀ c ∈ closedBall q.2 r,
        HasDerivAt (fun τ => Lsum τ c) (Sd τ c) τ) ∧
      HasDerivAt (fun c => Ssum q.1 c) (Sd q.1 q.2) q.2 := by
    intro q hq
    obtain ⟨δ, r, hδ, hr, Sd, hSd, -, -, hc, ht⟩ := hpt q hq
    refine ⟨δ, r, hδ, hr, Sd, hSd, fun q' hq' => (hc q'.1 (Ioo_subset_Icc_self hq'.1) q'.2 hq'.2).deriv,
      ht, hc q.1 ⟨by linarith, by linarith⟩ q.2 (mem_ball_self hr)⟩
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · obtain ⟨δ, r, hδ, hr, Sd, -, -, -, hc⟩ := hderiv_eq q hq
    rw [hc.deriv]; exact hc
  · obtain ⟨δ, r, hδ, hr, Sd, -, -, ht, hc⟩ := hderiv_eq q hq
    rw [hc.deriv]
    exact ht q.1 ⟨by linarith, by linarith⟩ q.2 (mem_closedBall_self hr.le)
  · obtain ⟨δ, r, hδ, hr, Sd, hSd, heq, -, -⟩ := hderiv_eq q hq
    have hopen : Ioo (q.1 - δ) (q.1 + δ) ×ˢ ball q.2 r ∈ 𝓝 q := by
      rw [nhds_prod_eq]
      exact Filter.prod_mem_prod (Ioo_mem_nhds (by linarith) (by linarith)) (ball_mem_nhds q.2 hr)
    have hcont : ContinuousAt (fun q' : ℝ × ℂ => Sd q'.1 q'.2) q :=
      hSd.continuousAt (hbox_nhds q δ r hδ hr)
    refine (hcont.congr ?_).continuousWithinAt
    filter_upwards [hopen] with q' hq'
    exact (heq q' hq').symm
  · obtain ⟨δ, r, hδ, hr, Sd, -, hS, -, -, -⟩ := hpt q hq
    exact (hS.continuousAt (hbox_nhds q δ r hδ hr)).continuousWithinAt
  · obtain ⟨δ, r, hδ, hr, Sd, -, -, hL, -, -⟩ := hpt q hq
    exact (hL.continuousAt (hbox_nhds q δ r hδ hr)).continuousWithinAt

/-- **Regularity of `S_±`, `Λ_±` on `(0, 1) × ℂ₊`** and **the Burgers identities**
`∂_τ Λ_± = ∂_c S_±`. -/
theorem upper_global (hP : IsProj P) (hA : A.IsHermitian) :
    (∀ q ∈ domRI, HasDerivAt (fun c => Sup P A q.1 c) (deriv (fun c => Sup P A q.1 c) q.2) q.2) ∧
    (∀ q ∈ domRI, HasDerivAt (fun τ => Lup P A τ q.2) (deriv (fun c => Sup P A q.1 c) q.2) q.1) ∧
    ContinuousOn (fun q : ℝ × ℂ => deriv (fun c => Sup P A q.1 c) q.2) domRI ∧
    ContinuousOn (fun q : ℝ × ℂ => Sup P A q.1 q.2) domRI ∧
    ContinuousOn (fun q : ℝ × ℂ => Lup P A q.1 q.2) domRI :=
  global_of_local fun _ hq => upper_local hP hA hq.1.1 hq.1.2 hq.2

theorem lower_global (hP : IsProj P) (hA : A.IsHermitian) :
    (∀ q ∈ domRI, HasDerivAt (fun c => Slo P A q.1 c) (deriv (fun c => Slo P A q.1 c) q.2) q.2) ∧
    (∀ q ∈ domRI, HasDerivAt (fun τ => Llo P A τ q.2) (deriv (fun c => Slo P A q.1 c) q.2) q.1) ∧
    ContinuousOn (fun q : ℝ × ℂ => deriv (fun c => Slo P A q.1 c) q.2) domRI ∧
    ContinuousOn (fun q : ℝ × ℂ => Slo P A q.1 q.2) domRI ∧
    ContinuousOn (fun q : ℝ × ℂ => Llo P A q.1 q.2) domRI :=
  global_of_local fun _ hq => lower_local hP hA hq.1.1 hq.1.2 hq.2

end Global

end OQP27.StripL3b
