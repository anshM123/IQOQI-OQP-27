import OQP27.StripRIPencil

/-!
# Upper and lower root sums of the shifted pencil (module L3b, proof of RI)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

`Rt P A τ c` are the pencil roots of `A + c`; `Sup`, `Slo` (`S_±`) are the sums of the roots in `ℂ₊`, `ℂ₋`,
and `Lup`, `Llo` (`Λ_±`) the sums of their principal logarithms.  The pinched matrix is
`A_d = pinch P A`; the paper's `S⁰_+` is `Sup P (pinch P A)` (Lemma A(c)).
Main results:
* `Sup_add_Slo`, `sum_Rt_pinch`, `Sup_sub_eq`: `S_+ + S_- = ∑ roots` and the trace identity
  `∑ roots(A + c) = ∑ roots(A_d + c)`;
* `norm_Sup_sub_le` (**Lemma B(iii)**, the domination): `|S_+(A) - S_+(A_d)| ≤ 2 M √K / √(τ (1 - τ))`
  whenever `K ≥ ‖A + c‖_F², ‖A_d + c‖_F²`.

Hypotheses: none.
Paper: `iqoqi/programs/oqp27B_all/Q_RI/PROOF.md`, section 1, Lemma B.
-/

namespace OQP27.StripL3b

open Matrix Polynomial Complex Metric Filter Topology Set Real

variable {M : ℕ}

/-- The pencil roots of `A + c` at `τ`. -/
noncomputable def Rt (P A : Matrix (Fin M) (Fin M) ℂ) (τ : ℝ) (c : ℂ) : Multiset ℂ :=
  pencilRoots P (A + c • 1) τ

/-- `S_+`: the sum of the roots in the upper half plane. -/
noncomputable def Sup (P A : Matrix (Fin M) (Fin M) ℂ) (τ : ℝ) (c : ℂ) : ℂ :=
  (upperRoots (Rt P A τ c)).sum

/-- `S_-`: the sum of the roots in the lower half plane. -/
noncomputable def Slo (P A : Matrix (Fin M) (Fin M) ℂ) (τ : ℝ) (c : ℂ) : ℂ :=
  (lowerRoots (Rt P A τ c)).sum

/-- `Λ_+`: the sum of the logarithms of the roots in the upper half plane. -/
noncomputable def Lup (P A : Matrix (Fin M) (Fin M) ℂ) (τ : ℝ) (c : ℂ) : ℂ :=
  ((upperRoots (Rt P A τ c)).map Complex.log).sum

/-- `Λ_-`: the sum of the logarithms of the roots in the lower half plane. -/
noncomputable def Llo (P A : Matrix (Fin M) (Fin M) ℂ) (τ : ℝ) (c : ℂ) : ℂ :=
  ((lowerRoots (Rt P A τ c)).map Complex.log).sum

section Sums

variable {P A : Matrix (Fin M) (Fin M) ℂ}

lemma pinch_add_smul_one (hP : P * P = P) (A : Matrix (Fin M) (Fin M) ℂ) (c : ℂ) :
    pinch P (A + c • 1) = pinch P A + c • 1 := by
  rw [pinch_add, pinch_smul, pinch_one hP]

lemma Rt_im_ne_zero (hP : IsProj P) (hA : A.IsHermitian) {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) {c : ℂ}
    (hc : 0 < c.im) : ∀ y ∈ Rt P A τ c, y.im ≠ 0 :=
  fun _ hy => (pencilRoot_im_bounds hP hA h0 h1 hc hy).1

/-- `S_+ + S_- = ∑ roots = Tr ((P - τ)⁻¹ (A + c))`. -/
lemma Sup_add_Slo (hP : IsProj P) (hA : A.IsHermitian) {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1)
    {c : ℂ} (hc : 0 < c.im) : Sup P A τ c + Slo P A τ c = (Rt P A τ c).sum := by
  unfold Sup Slo
  rw [← Multiset.sum_add, upper_add_lower (Rt_im_ne_zero hP hA h0 h1 hc)]

/-- The trace identity: the pencils of `A + c` and `A_d + c` have the same root sum. -/
lemma sum_Rt_pinch (hP : IsProj P) (A : Matrix (Fin M) (Fin M) ℂ) {τ : ℝ} (h0 : 0 < τ)
    (h1 : τ < 1) (c : ℂ) : (Rt P (pinch P A) τ c).sum = (Rt P A τ c).sum := by
  unfold Rt
  rw [← pinch_add_smul_one hP.2 A c, sum_pencilRoots_pinch hP.2 h0.ne' h1.ne]

/-- `S_+(A) - S_+(A_d) = S_-(A_d) - S_-(A)`. -/
lemma Sup_sub_eq (hP : IsProj P) (hA : A.IsHermitian) {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1)
    {c : ℂ} (hc : 0 < c.im) :
    Sup P A τ c - Sup P (pinch P A) τ c = Slo P (pinch P A) τ c - Slo P A τ c := by
  have h1' := Sup_add_Slo hP hA h0 h1 hc
  have h2' := Sup_add_Slo hP (isHermitian_pinch hP.1 hA) h0 h1 hc
  have h3 := sum_Rt_pinch hP A h0 h1 c
  rw [← h1', ← h2'] at h3
  linear_combination -h3

lemma norm_le_of_sq_bound {y : ℂ} {K τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1)
    (h : ‖y‖ ^ 2 * (τ * (1 - τ)) ≤ K) : ‖y‖ ≤ √K / √(τ * (1 - τ)) := by
  have hτ : 0 < τ * (1 - τ) := mul_pos h0 (by linarith)
  rw [le_div_iff₀ (Real.sqrt_pos.mpr hτ), ← Real.sqrt_sq (norm_nonneg y),
    ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt h

/-- `|S_+(A)| ≤ M √‖A + c‖_F² / √(τ(1-τ))` for `τ ≤ 1/2`. -/
lemma norm_Sup_le (hP : IsProj P) (hA : A.IsHermitian) {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1)
    (hτ : τ ≤ 1 / 2) {c : ℂ} (hc : 0 < c.im) :
    ‖Sup P A τ c‖ ≤ M * (√(frob (A + c • 1)) / √(τ * (1 - τ))) := by
  unfold Sup
  have hb : ∀ y ∈ upperRoots (Rt P A τ c), ‖y‖ ≤ √(frob (A + c • 1)) / √(τ * (1 - τ)) := by
    intro y hy
    have hy' : y ∈ Rt P A τ c := Multiset.mem_of_mem_filter hy
    have hpos : 0 < y.im := (Multiset.mem_filter.mp hy).2
    exact norm_le_of_sq_bound h0 h1
      (pencilRoot_norm_bound hP hA h0 h1 hc hy' (Or.inl ⟨hpos, hτ⟩))
  refine (norm_multiset_sum_le_card_mul hb).trans ?_
  have hcard : ((upperRoots (Rt P A τ c)).card : ℝ) ≤ M := by
    have := card_filter_le (Rt P A τ c) (fun z => 0 < z.im)
    unfold Rt at this ⊢
    rw [card_pencilRoots] at this
    exact_mod_cast this
  exact mul_le_mul_of_nonneg_right hcard (by positivity)

/-- `|S_-(A)| ≤ M √‖A + c‖_F² / √(τ(1-τ))` for `τ ≥ 1/2`. -/
lemma norm_Slo_le (hP : IsProj P) (hA : A.IsHermitian) {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1)
    (hτ : 1 / 2 ≤ τ) {c : ℂ} (hc : 0 < c.im) :
    ‖Slo P A τ c‖ ≤ M * (√(frob (A + c • 1)) / √(τ * (1 - τ))) := by
  unfold Slo
  have hb : ∀ y ∈ lowerRoots (Rt P A τ c), ‖y‖ ≤ √(frob (A + c • 1)) / √(τ * (1 - τ)) := by
    intro y hy
    have hy' : y ∈ Rt P A τ c := Multiset.mem_of_mem_filter hy
    have hneg : y.im < 0 := (Multiset.mem_filter.mp hy).2
    exact norm_le_of_sq_bound h0 h1
      (pencilRoot_norm_bound hP hA h0 h1 hc hy' (Or.inr ⟨hneg, hτ⟩))
  refine (norm_multiset_sum_le_card_mul hb).trans ?_
  have hcard : ((lowerRoots (Rt P A τ c)).card : ℝ) ≤ M := by
    have := card_filter_le (Rt P A τ c) (fun z => z.im < 0)
    unfold Rt at this ⊢
    rw [card_pencilRoots] at this
    exact_mod_cast this
  exact mul_le_mul_of_nonneg_right hcard (by positivity)

/-- **Lemma B(iii)** (domination).  With `K ≥ ‖A + c‖_F², ‖A_d + c‖_F²`:
`|S_+(A) - S_+(A_d)| ≤ 2 M √K / √(τ (1 - τ))` on `(0, 1)`. -/
theorem norm_Sup_sub_le (hP : IsProj P) (hA : A.IsHermitian) {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1)
    {c : ℂ} (hc : 0 < c.im) {K : ℝ} (hK1 : frob (A + c • 1) ≤ K)
    (hK2 : frob (pinch P A + c • 1) ≤ K) :
    ‖Sup P A τ c - Sup P (pinch P A) τ c‖ ≤ 2 * M * (√K / √(τ * (1 - τ))) := by
  have hAd := isHermitian_pinch hP.1 hA
  have hs1 : √(frob (A + c • 1)) / √(τ * (1 - τ)) ≤ √K / √(τ * (1 - τ)) :=
    div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hK1) (Real.sqrt_nonneg _)
  have hs2 : √(frob (pinch P A + c • 1)) / √(τ * (1 - τ)) ≤ √K / √(τ * (1 - τ)) :=
    div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hK2) (Real.sqrt_nonneg _)
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  rcases le_or_gt τ (1 / 2) with hτ | hτ
  · calc ‖Sup P A τ c - Sup P (pinch P A) τ c‖
        ≤ ‖Sup P A τ c‖ + ‖Sup P (pinch P A) τ c‖ := norm_sub_le _ _
      _ ≤ M * (√K / √(τ * (1 - τ))) + M * (√K / √(τ * (1 - τ))) :=
          add_le_add ((norm_Sup_le hP hA h0 h1 hτ hc).trans (mul_le_mul_of_nonneg_left hs1 hM))
            ((norm_Sup_le hP hAd h0 h1 hτ hc).trans (mul_le_mul_of_nonneg_left hs2 hM))
      _ = 2 * M * (√K / √(τ * (1 - τ))) := by ring
  · rw [Sup_sub_eq hP hA h0 h1 hc]
    calc ‖Slo P (pinch P A) τ c - Slo P A τ c‖
        ≤ ‖Slo P (pinch P A) τ c‖ + ‖Slo P A τ c‖ := norm_sub_le _ _
      _ ≤ M * (√K / √(τ * (1 - τ))) + M * (√K / √(τ * (1 - τ))) :=
          add_le_add ((norm_Slo_le hP hAd h0 h1 hτ.le hc).trans
              (mul_le_mul_of_nonneg_left hs2 hM))
            ((norm_Slo_le hP hA h0 h1 hτ.le hc).trans (mul_le_mul_of_nonneg_left hs1 hM))
      _ = 2 * M * (√K / √(τ * (1 - τ))) := by ring

end Sums

end OQP27.StripL3b
