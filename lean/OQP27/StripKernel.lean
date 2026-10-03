import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The strip Poisson kernel (OQP 27B formalisation, module L3a)

For `0 < X < 1` the Poisson kernel of the strip `{0 < Re z < 1}` for its left edge is
`K_X(u) = sin(πX) / (2 (cosh(πu) - cos(πX)))` (`stripKernel`).

Proved in this file (no hypotheses; all proofs complete):
* `stripKernel_pos`, `stripKernel_le`: `K_X > 0` and `K_X(u) ≤ C_X exp(-π|u|)`;
* `stripKernel_neg`: `K_X` is even; integrability of `K_X`, `u K_X`, `u² K_X`;
* `fourier_stripKernel`: `∫ exp(-iκu) K_X(u) du = sinh(κ(1-X)) / sinh κ` for real `κ ≠ 0`
  (`sinhRatio`); this is Lemma 5 of the paper on the imaginary axis `a = iκ`.  The proof computes
  the inverse Fourier transform of `κ ↦ sinh(κ(1-X))/sinh κ` (geometric series, dominated
  convergence, and the Mittag-Leffler expansion of the cotangent, Mathlib
  `tendsto_logDeriv_euler_cot_sub`) and then applies Fourier inversion
  (`MeasureTheory.Integrable.fourier_fourierInv_eq`);
* `integral_stripKernel`: the mass `∫ K_X = 1 - X`;
* `integral_mul_stripKernel`: `∫ u K_X(u) du = 0`.

Paper: `iqoqi/programs/oqp27B_all/Q_2bmv/PROOF.md`, section 5, Lemma 5.
-/

open Real MeasureTheory Set Filter Topology Complex
open scoped FourierTransform

namespace OQP27.StripL3a

noncomputable def stripKernel (X u : ℝ) : ℝ :=
  Real.sin (π * X) / (2 * (Real.cosh (π * u) - Real.cos (π * X)))

lemma cos_pi_mul_lt_one {X : ℝ} (h0 : 0 < X) (h1 : X < 1) : Real.cos (π * X) < 1 := by
  have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) (by nlinarith [Real.pi_pos])
    (by positivity : (0:ℝ) < π * X)
  simpa using this

lemma sin_pi_mul_pos {X : ℝ} (h0 : 0 < X) (h1 : X < 1) : 0 < Real.sin (π * X) :=
  Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])

lemma stripKernel_denom_pos {X : ℝ} (h0 : 0 < X) (h1 : X < 1) (u : ℝ) :
    0 < Real.cosh (π * u) - Real.cos (π * X) := by
  have := Real.one_le_cosh (π * u)
  have := cos_pi_mul_lt_one h0 h1
  linarith

lemma stripKernel_pos {X : ℝ} (h0 : 0 < X) (h1 : X < 1) (u : ℝ) : 0 < stripKernel X u := by
  unfold stripKernel
  have := stripKernel_denom_pos h0 h1 u
  have := sin_pi_mul_pos h0 h1
  positivity

lemma stripKernel_neg (X u : ℝ) : stripKernel X (-u) = stripKernel X u := by
  simp [stripKernel, mul_neg, Real.cosh_neg]

/-- The constant `C_X` of the bound `K_X(u) ≤ C_X exp(-π|u|)`. -/
noncomputable def kernelConst (X : ℝ) : ℝ := Real.sin (π * X) / (1 - max (Real.cos (π * X)) 0)

lemma exp_abs_le_two_mul_cosh (x : ℝ) : Real.exp |x| ≤ 2 * Real.cosh x := by
  rw [Real.cosh_eq]
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]; linarith [Real.exp_pos (-x)]
  · rw [abs_of_nonpos hx]; linarith [Real.exp_pos x]

lemma stripKernel_le {X : ℝ} (h0 : 0 < X) (h1 : X < 1) (u : ℝ) :
    stripKernel X u ≤ kernelConst X * Real.exp (-(π * |u|)) := by
  set c := Real.cos (π * X) with hc
  have hc1 : c < 1 := cos_pi_mul_lt_one h0 h1
  have hs : 0 < Real.sin (π * X) := sin_pi_mul_pos h0 h1
  have hm : 0 < 1 - max c 0 := by
    rcases le_total c 0 with h | h
    · rw [max_eq_right h]; norm_num
    · rw [max_eq_left h]; linarith
  have hcosh := exp_abs_le_two_mul_cosh (π * u)
  have habs : |π * u| = π * |u| := by rw [abs_mul, abs_of_pos Real.pi_pos]
  rw [habs] at hcosh
  have hch1 : 1 ≤ Real.cosh (π * u) := Real.one_le_cosh _
  -- the denominator is at least (1 - c⁺) exp(π|u|)
  have hden : (1 - max c 0) * Real.exp (π * |u|) ≤ 2 * (Real.cosh (π * u) - c) := by
    rcases le_total c 0 with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]
      have : (1 - c) * Real.exp (π * |u|) ≤ (1 - c) * (2 * Real.cosh (π * u)) :=
        mul_le_mul_of_nonneg_left hcosh (by linarith)
      nlinarith
  unfold stripKernel kernelConst
  rw [← hc]
  have hE : 0 < Real.exp (π * |u|) := Real.exp_pos _
  have hrhs : Real.sin (π * X) / (1 - max c 0) * Real.exp (-(π * |u|))
      = Real.sin (π * X) / ((1 - max c 0) * Real.exp (π * |u|)) := by
    rw [Real.exp_neg]; field_simp
  rw [hrhs]
  exact div_le_div_of_nonneg_left hs.le (by positivity) hden

lemma kernelConst_pos {X : ℝ} (h0 : 0 < X) (h1 : X < 1) : 0 < kernelConst X := by
  unfold kernelConst
  have hc1 := cos_pi_mul_lt_one h0 h1
  have hs := sin_pi_mul_pos h0 h1
  have hm : 0 < 1 - max (Real.cos (π * X)) 0 := by
    rcases le_total (Real.cos (π * X)) 0 with h | h
    · rw [max_eq_right h]; norm_num
    · rw [max_eq_left h]; linarith
  positivity

lemma continuous_stripKernel {X : ℝ} (h0 : 0 < X) (h1 : X < 1) : Continuous (stripKernel X) := by
  unfold stripKernel
  refine continuous_const.div (by fun_prop) (fun u => ?_)
  have := stripKernel_denom_pos h0 h1 u
  positivity

lemma measurable_stripKernel_uncurry : Measurable (fun p : ℝ × ℝ => stripKernel p.1 p.2) := by
  unfold stripKernel
  fun_prop

/-! ### Integrability of exponentially decaying functions -/

lemma integrable_exp_neg_mul_abs {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => Real.exp (-(b * |x|))) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0:ℝ)), integrableOn_union]
  constructor
  · refine (integrableOn_exp_mul_Iic hb 0).congr_fun (fun x hx => ?_) measurableSet_Iic
    simp only [mem_Iic] at hx
    simp [abs_of_nonpos hx]
  · refine (exp_neg_integrableOn_Ioi 0 hb).congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp only [mem_Ioi] at hx
    simp [abs_of_pos hx]

lemma sq_mul_exp_neg_abs_le {c : ℝ} (hc : 0 < c) (x : ℝ) :
    x ^ 2 * Real.exp (-(c * |x|)) ≤ 2 / c ^ 2 := by
  have h := Real.pow_div_factorial_le_exp (x := c * |x|) (by positivity) 2
  simp only [Nat.factorial, Nat.succ_eq_add_one, zero_add, mul_one] at h
  rw [Real.exp_neg]
  have hE : 0 < Real.exp (c * |x|) := Real.exp_pos _
  rw [← div_eq_mul_inv, div_le_div_iff₀ hE (by positivity)]
  have : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  rw [this]
  have h' : (c * |x|) ^ 2 ≤ 2 * Real.exp (c * |x|) := by linarith
  nlinarith [sq_nonneg (c * |x|)]

lemma integrable_stripKernel {X : ℝ} (h0 : 0 < X) (h1 : X < 1) : Integrable (stripKernel X) := by
  refine ((integrable_exp_neg_mul_abs Real.pi_pos).const_mul (kernelConst X)).mono'
    (continuous_stripKernel h0 h1).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (stripKernel_pos h0 h1 u)]
  exact stripKernel_le h0 h1 u

lemma integrable_sq_mul_stripKernel {X : ℝ} (h0 : 0 < X) (h1 : X < 1) :
    Integrable (fun u => u ^ 2 * stripKernel X u) := by
  have hb : (0:ℝ) < π / 2 := by positivity
  refine ((integrable_exp_neg_mul_abs hb).const_mul (kernelConst X * (2 / (π / 2) ^ 2))).mono'
    ((continuous_pow 2).mul (continuous_stripKernel h0 h1)).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg u) (stripKernel_pos h0 h1 u).le)]
  have hK := stripKernel_le h0 h1 u
  have hsq := sq_mul_exp_neg_abs_le hb u
  have hC := kernelConst_pos h0 h1
  have hsplit : Real.exp (-(π * |u|)) = Real.exp (-(π / 2 * |u|)) * Real.exp (-(π / 2 * |u|)) := by
    rw [← Real.exp_add]; ring_nf
  calc u ^ 2 * stripKernel X u ≤ u ^ 2 * (kernelConst X * Real.exp (-(π * |u|))) :=
        mul_le_mul_of_nonneg_left hK (sq_nonneg u)
    _ = kernelConst X * (u ^ 2 * Real.exp (-(π / 2 * |u|))) * Real.exp (-(π / 2 * |u|)) := by
        rw [hsplit]; ring
    _ ≤ kernelConst X * (2 / (π / 2) ^ 2) * Real.exp (-(π / 2 * |u|)) := by
        gcongr
    _ = _ := rfl


/-- The ratio `sinh(κ(1-X)) / sinh κ`, extended by its limit `1 - X` at `κ = 0`. -/
noncomputable def sinhRatio (X κ : ℝ) : ℝ :=
  if κ = 0 then 1 - X else Real.sinh (κ * (1 - X)) / Real.sinh κ

lemma sinhRatio_of_ne {X κ : ℝ} (hκ : κ ≠ 0) :
    sinhRatio X κ = Real.sinh (κ * (1 - X)) / Real.sinh κ := if_neg hκ

lemma sinhRatio_zero (X : ℝ) : sinhRatio X 0 = 1 - X := if_pos rfl

lemma sinhRatio_neg (X κ : ℝ) : sinhRatio X (-κ) = sinhRatio X κ := by
  rcases eq_or_ne κ 0 with rfl | hκ
  · simp
  · rw [sinhRatio_of_ne hκ, sinhRatio_of_ne (neg_ne_zero.mpr hκ), neg_mul, Real.sinh_neg,
      Real.sinh_neg, neg_div_neg_eq]

lemma sinhRatio_pos_bounds {X κ : ℝ} (hX0 : 0 ≤ X) (hX1 : X ≤ 1) (hκ : 0 < κ) :
    0 ≤ sinhRatio X κ ∧ sinhRatio X κ ≤ Real.exp (-(X * κ)) := by
  rw [sinhRatio_of_ne hκ.ne']
  have hs : 0 < Real.sinh κ := Real.sinh_pos_iff.mpr hκ
  constructor
  · exact div_nonneg (Real.sinh_nonneg_iff.mpr (by nlinarith)) hs.le
  · rw [div_le_iff₀ hs, Real.sinh_eq, Real.sinh_eq]
    have h1 : Real.exp (-(X * κ)) * Real.exp κ = Real.exp (κ * (1 - X)) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp (-(X * κ)) * Real.exp (-κ) = Real.exp (-(κ * (1 + X))) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : Real.exp (-(κ * (1 + X))) ≤ Real.exp (-(κ * (1 - X))) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h4 : Real.exp (-(X * κ)) * ((Real.exp κ - Real.exp (-κ)) / 2)
        = (Real.exp (κ * (1 - X)) - Real.exp (-(κ * (1 + X)))) / 2 := by
      rw [mul_div_assoc', mul_sub, h1, h2]
    rw [h4]
    linarith

lemma sinhRatio_nonneg {X : ℝ} (hX0 : 0 ≤ X) (hX1 : X ≤ 1) (κ : ℝ) : 0 ≤ sinhRatio X κ := by
  rcases lt_trichotomy κ 0 with h | rfl | h
  · rw [← sinhRatio_neg]; exact (sinhRatio_pos_bounds hX0 hX1 (neg_pos.mpr h)).1
  · rw [sinhRatio_zero]; linarith
  · exact (sinhRatio_pos_bounds hX0 hX1 h).1

lemma sinhRatio_le_exp {X : ℝ} (hX0 : 0 ≤ X) (hX1 : X ≤ 1) (κ : ℝ) :
    sinhRatio X κ ≤ Real.exp (-(X * |κ|)) := by
  rcases lt_trichotomy κ 0 with h | rfl | h
  · rw [← sinhRatio_neg, abs_of_neg h]; exact (sinhRatio_pos_bounds hX0 hX1 (neg_pos.mpr h)).2
  · simp [sinhRatio_zero]; linarith
  · rw [abs_of_pos h]; exact (sinhRatio_pos_bounds hX0 hX1 h).2

lemma measurable_sinhRatio (X : ℝ) : Measurable (sinhRatio X) := by
  unfold sinhRatio
  exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)

lemma integrable_sinhRatio {X : ℝ} (hX0 : 0 < X) (hX1 : X ≤ 1) : Integrable (sinhRatio X) := by
  refine (integrable_exp_neg_mul_abs hX0).mono' (measurable_sinhRatio X).aestronglyMeasurable
    (Eventually.of_forall fun κ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sinhRatio_nonneg hX0.le hX1 κ)]
  exact sinhRatio_le_exp hX0.le hX1 κ

lemma hasSum_sinhRatio (X : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    HasSum (fun m : ℕ => Real.exp (-(κ * (X + 2 * m))) - Real.exp (-(κ * (2 - X + 2 * m))))
      (sinhRatio X κ) := by
  set r := Real.exp (-(2 * κ)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    have := Real.exp_lt_exp.mpr (show -(2 * κ) < 0 by linarith)
    simpa [hr] using this
  have hg := (hasSum_geometric_of_lt_one hr0 hr1).mul_left
    (Real.exp (-(κ * X)) - Real.exp (-(κ * (2 - X))))
  have hfun : (fun m : ℕ => Real.exp (-(κ * (X + 2 * m))) - Real.exp (-(κ * (2 - X + 2 * m))))
      = fun i : ℕ => (Real.exp (-(κ * X)) - Real.exp (-(κ * (2 - X)))) * r ^ i := by
    funext m
    have e1 : Real.exp (-(κ * (X + 2 * m))) = Real.exp (-(κ * X)) * r ^ m := by
      rw [hr, ← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
    have e2 : Real.exp (-(κ * (2 - X + 2 * m))) = Real.exp (-(κ * (2 - X))) * r ^ m := by
      rw [hr, ← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
    rw [e1, e2]; ring
  have hval : sinhRatio X κ = (Real.exp (-(κ * X)) - Real.exp (-(κ * (2 - X)))) * (1 - r)⁻¹ := by
    rw [sinhRatio_of_ne hκ.ne', Real.sinh_eq, Real.sinh_eq]
    have hA : 0 < Real.exp κ := Real.exp_pos κ
    have f1 : Real.exp (κ * (1 - X)) = Real.exp κ * Real.exp (-(κ * X)) := by
      rw [← Real.exp_add]; ring_nf
    have f2 : Real.exp (-(κ * (1 - X))) = Real.exp κ * Real.exp (-(κ * (2 - X))) := by
      rw [← Real.exp_add]; ring_nf
    have f3 : Real.exp (-κ) = Real.exp κ * r := by
      rw [hr, ← Real.exp_add]; ring_nf
    rw [f1, f2, f3]
    have h1r : (1 - r) ≠ 0 := by linarith
    field_simp
  rw [hfun, hval]
  exact hg

lemma tendsto_sinhRatio_zero (X : ℝ) : Tendsto (sinhRatio X) (𝓝[≠] 0) (𝓝 (1 - X)) := by
  have h1 : HasDerivAt (fun t : ℝ => Real.sinh (t * (1 - X))) (1 - X) 0 := by
    have := ((hasDerivAt_id (0:ℝ)).mul_const (1 - X)).sinh
    simpa using this
  have h2 : HasDerivAt Real.sinh 1 0 := by simpa using Real.hasDerivAt_sinh 0
  rw [hasDerivAt_iff_tendsto_slope_zero] at h1 h2
  have := h1.div h2 one_ne_zero
  simp only [zero_add, zero_mul, Real.sinh_zero, sub_zero, smul_eq_mul, div_one] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [sinhRatio_of_ne ht]
  have ht' : t⁻¹ ≠ 0 := inv_ne_zero ht
  simp only [Pi.div_apply]
  rw [mul_div_mul_left _ _ ht']

lemma continuousAt_sinhRatio (X : ℝ) {κ : ℝ} (hκ : κ ≠ 0) : ContinuousAt (sinhRatio X) κ := by
  have hc : ContinuousAt (fun t => Real.sinh (t * (1 - X)) / Real.sinh t) κ :=
    (by fun_prop : Continuous fun t : ℝ => Real.sinh (t * (1 - X))).continuousAt.div
      Real.continuous_sinh.continuousAt (by simpa using hκ)
  refine hc.congr ?_
  filter_upwards [eventually_ne_nhds hκ] with t ht
  rw [sinhRatio_of_ne ht]



/-! ### The Mittag-Leffler expansion of the cotangent, in the form used below -/

lemma cot_partial_succ (z : ℂ) (N : ℕ) :
    ∑ m ∈ Finset.range (N + 1), (1 / (z + m) + 1 / (z - (m + 1))) =
      1 / z + (∑ j ∈ Finset.range N, cotTerm z j + 1 / (z - (N + 1))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp only [cotTerm]
    push_cast
    ring

lemma tendsto_one_div_sub_nat (z : ℂ) :
    Tendsto (fun N : ℕ => 1 / (z - ((N : ℂ) + 1))) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : Tendsto (fun N : ℕ => (N : ℝ) + (1 - ‖z‖)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun N : ℕ => ‖z - ((N : ℂ) + 1)‖) atTop atTop := by
    refine tendsto_atTop_mono (fun N => ?_) h1
    have h := norm_sub_norm_le ((N : ℂ) + 1) z
    rw [norm_sub_rev] at h
    have hn : ‖(N : ℂ) + 1‖ = (N : ℝ) + 1 := by
      rw [show ((N : ℂ) + 1) = ((N + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      push_cast; ring
    linarith
  refine (tendsto_inv_atTop_zero.comp h2).congr (fun N => ?_)
  simp

lemma tendsto_cot_partial {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N, (1 / (z + m) + 1 / (z - (m + 1))))
      atTop (𝓝 (π * Complex.cot (π * z))) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  have h := (tendsto_logDeriv_euler_cot_sub hz).add (tendsto_one_div_sub_nat z)
  have h' := (tendsto_const_nhds (x := 1 / z)).add h
  have hlim : 1 / z + (π * Complex.cot (π * z) - 1 / z + 0) = π * Complex.cot (π * z) := by ring
  rw [hlim] at h'
  refine h'.congr (fun N => ?_)
  rw [cot_partial_succ]

lemma mem_integerComplement_of_re {z : ℂ} (h0 : 0 < z.re) (h1 : z.re < 1) :
    z ∈ Complex.integerComplement := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨n, hn⟩
  have hre : (n : ℝ) = z.re := by rw [← hn]; simp
  rcases le_or_gt n 0 with h | h
  · have : (n : ℝ) ≤ 0 := by exact_mod_cast h
    linarith
  · have : (1 : ℝ) ≤ n := by exact_mod_cast h
    linarith

lemma cot_add_cot_eq {X : ℝ} (h0 : 0 < X) (h1 : X < 1) (u : ℝ) :
    (π : ℂ) * Complex.cot (π * ((X + I * u) / 2)) + π * Complex.cot (π * ((X - I * u) / 2))
      = 4 * π * (stripKernel X u : ℂ) := by
  set w₁ := (π : ℂ) * ((X + I * u) / 2) with hw₁
  set w₂ := (π : ℂ) * ((X - I * u) / 2) with hw₂
  have hz₁ : ((X : ℂ) + I * u) / 2 ∈ Complex.integerComplement :=
    mem_integerComplement_of_re (by simp; linarith) (by simp; linarith)
  have hz₂ : ((X : ℂ) - I * u) / 2 ∈ Complex.integerComplement :=
    mem_integerComplement_of_re (by simp; linarith) (by simp; linarith)
  have hs₁ : Complex.sin w₁ ≠ 0 := sin_pi_mul_ne_zero hz₁
  have hs₂ : Complex.sin w₂ ≠ 0 := sin_pi_mul_ne_zero hz₂
  have hsum : w₁ + w₂ = ((π * X : ℝ) : ℂ) := by rw [hw₁, hw₂]; push_cast; ring
  have hdiff : w₁ - w₂ = ((π * u : ℝ) : ℂ) * I := by rw [hw₁, hw₂]; push_cast; ring
  have hprod : Complex.sin w₁ * Complex.sin w₂
      = ((Real.cosh (π * u) : ℂ) - (Real.cos (π * X) : ℂ)) / 2 := by
    have e1 := Complex.cos_sub w₁ w₂
    have e2 := Complex.cos_add w₁ w₂
    rw [hdiff, Complex.cos_mul_I] at e1
    rw [hsum] at e2
    rw [Complex.ofReal_cosh, Complex.ofReal_cos]
    linear_combination (e2 - e1) / 2
  have hcot : Complex.cot w₁ + Complex.cot w₂
      = Complex.sin (w₁ + w₂) / (Complex.sin w₁ * Complex.sin w₂) := by
    rw [Complex.cot_eq_cos_div_sin, Complex.cot_eq_cos_div_sin, Complex.sin_add]
    field_simp
    ring
  rw [← mul_add, hcot, hprod, hsum, ← Complex.ofReal_sin]
  have hden : Real.cosh (π * u) - Real.cos (π * X) ≠ 0 := (stripKernel_denom_pos h0 h1 u).ne'
  have hden' : ((Real.cosh (π * u) : ℂ) - (Real.cos (π * X) : ℂ)) ≠ 0 := by
    exact_mod_cast hden
  unfold stripKernel
  push_cast
  field_simp
  ring

/-! ### The inverse Fourier transform of `sinhRatio` -/

lemma term_expand (u a b κ : ℝ) :
    (cexp (I * u * κ) + cexp (-(I * u * κ))) * ((Real.exp (-(κ * a)) - Real.exp (-(κ * b)) : ℝ) : ℂ)
      = cexp (-(a - I * u) * κ) + cexp (-(a + I * u) * κ) - cexp (-(b - I * u) * κ)
          - cexp (-(b + I * u) * κ) := by
  have e : ∀ x y : ℂ, cexp x * cexp y = cexp (x + y) := fun x y => (Complex.exp_add x y).symm
  push_cast
  rw [add_mul, mul_sub, mul_sub, e, e, e, e]
  ring_nf

lemma integrableOn_cexp_neg_mul {d : ℂ} (hd : 0 < d.re) :
    IntegrableOn (fun κ : ℝ => cexp (-d * κ)) (Ioi 0) :=
  integrableOn_exp_mul_complex_Ioi (by simpa using hd) 0

lemma integrableOn_Ioi_term (u a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun κ : ℝ => (cexp (I * u * κ) + cexp (-(I * u * κ))) *
        ((Real.exp (-(κ * a)) - Real.exp (-(κ * b)) : ℝ) : ℂ)) (Ioi 0) := by
  simp_rw [term_expand]
  have r1 : 0 < (a - I * u).re := by simpa using ha
  have r2 : 0 < (a + I * u).re := by simpa using ha
  have r3 : 0 < (b - I * u).re := by simpa using hb
  have r4 : 0 < (b + I * u).re := by simpa using hb
  exact (((integrableOn_cexp_neg_mul r1).add (integrableOn_cexp_neg_mul r2)).sub
    (integrableOn_cexp_neg_mul r3)).sub (integrableOn_cexp_neg_mul r4)

lemma integral_Ioi_term (u a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ κ in Ioi (0:ℝ), (cexp (I * u * κ) + cexp (-(I * u * κ))) *
        ((Real.exp (-(κ * a)) - Real.exp (-(κ * b)) : ℝ) : ℂ)
      = 1 / (a - I * u) + 1 / (a + I * u) - 1 / (b - I * u) - 1 / (b + I * u) := by
  have key : ∀ d : ℂ, 0 < d.re → ∫ κ in Ioi (0:ℝ), cexp (-d * κ) = 1 / d := by
    intro d hd
    rw [integral_exp_mul_complex_Ioi (by simpa using hd) 0]
    simp
  have r1 : 0 < (a - I * u).re := by simpa using ha
  have r2 : 0 < (a + I * u).re := by simpa using ha
  have r3 : 0 < (b - I * u).re := by simpa using hb
  have r4 : 0 < (b + I * u).re := by simpa using hb
  simp_rw [term_expand]
  rw [integral_sub, integral_sub, integral_add, key _ r1, key _ r2, key _ r3, key _ r4]
  · exact integrableOn_cexp_neg_mul r1
  · exact integrableOn_cexp_neg_mul r2
  · exact (integrableOn_cexp_neg_mul r1).add (integrableOn_cexp_neg_mul r2)
  · exact integrableOn_cexp_neg_mul r3
  · exact ((integrableOn_cexp_neg_mul r1).add (integrableOn_cexp_neg_mul r2)).sub
      (integrableOn_cexp_neg_mul r3)
  · exact integrableOn_cexp_neg_mul r4

/-- `∫_{(0,∞)} (e^{iuκ} + e^{-iuκ}) sinh(κ(1-X))/sinh(κ) dκ = 2π K_X(u)`: termwise integration of
the geometric series of `sinhRatio` (dominated convergence) and the Mittag-Leffler expansion of the
cotangent. -/
lemma integral_Ioi_sinhRatio {X : ℝ} (h0 : 0 < X) (h1 : X < 1) (u : ℝ) :
    ∫ κ in Ioi (0:ℝ), (cexp (I * u * κ) + cexp (-(I * u * κ))) * (sinhRatio X κ : ℂ)
      = 2 * π * stripKernel X u := by
  set f : ℕ → ℝ → ℝ := fun m κ =>
    Real.exp (-(κ * (X + 2 * m))) - Real.exp (-(κ * (2 - X + 2 * m))) with hf
  set E : ℝ → ℂ := fun κ => cexp (I * u * κ) + cexp (-(I * u * κ)) with hE
  set c : ℕ → ℂ := fun m => 1 / ((X + 2 * m : ℝ) - I * u) + 1 / ((X + 2 * m : ℝ) + I * u)
      - 1 / ((2 - X + 2 * m : ℝ) - I * u) - 1 / ((2 - X + 2 * m : ℝ) + I * u) with hc
  have hEn : ∀ κ : ℝ, ‖E κ‖ ≤ 2 := by
    intro κ
    have a1 : ‖cexp (I * u * κ)‖ = 1 := by
      rw [Complex.norm_exp]; simp
    have a2 : ‖cexp (-(I * u * κ))‖ = 1 := by
      rw [Complex.norm_exp]; simp
    calc ‖E κ‖ ≤ ‖cexp (I * u * κ)‖ + ‖cexp (-(I * u * κ))‖ := norm_add_le _ _
      _ = 2 := by rw [a1, a2]; norm_num
  have hf_nonneg : ∀ m : ℕ, ∀ κ : ℝ, 0 ≤ κ → 0 ≤ f m κ := by
    intro m κ hκ
    simp only [hf, sub_nonneg]
    exact Real.exp_le_exp.mpr (by nlinarith)
  -- (1) integrals of the partial sums
  have hpart : ∀ N : ℕ, ∫ κ in Ioi (0:ℝ), E κ * ((∑ m ∈ Finset.range N, f m κ : ℝ) : ℂ)
      = ∑ m ∈ Finset.range N, c m := by
    intro N
    have hterm : ∀ m : ℕ, ∫ κ in Ioi (0:ℝ), E κ * ((f m κ : ℝ) : ℂ) = c m := by
      intro m
      have := integral_Ioi_term u (X + 2 * m) (2 - X + 2 * m) (by positivity) (by linarith)
      simp only [hE, hf, hc]
      convert this using 3
    have hint : ∀ m : ℕ, Integrable (fun κ => E κ * ((f m κ : ℝ) : ℂ)) (volume.restrict (Ioi 0)) :=
      fun m => integrableOn_Ioi_term u (X + 2 * m) (2 - X + 2 * m) (by positivity) (by linarith)
    simp only [Complex.ofReal_sum, Finset.mul_sum]
    rw [integral_finsetSum _ (fun m _ => hint m)]
    exact Finset.sum_congr rfl (fun m _ => hterm m)
  -- (2) dominated convergence for the partial sums
  have hdct : Tendsto (fun N : ℕ => ∫ κ in Ioi (0:ℝ), E κ * ((∑ m ∈ Finset.range N, f m κ : ℝ) : ℂ))
      atTop (𝓝 (∫ κ in Ioi (0:ℝ), E κ * (sinhRatio X κ : ℂ))) := by
    refine tendsto_integral_of_dominated_convergence (fun κ => 2 * sinhRatio X κ) ?_ ?_ ?_ ?_
    · intro N
      refine Continuous.aestronglyMeasurable ?_
      simp only [hE, hf]
      fun_prop
    · exact ((integrable_sinhRatio h0 h1.le).const_mul 2).integrableOn
    · intro N
      refine ae_restrict_of_forall_mem measurableSet_Ioi (fun κ hκ => ?_)
      have hκ' : 0 < κ := hκ
      have hS0 : 0 ≤ ∑ m ∈ Finset.range N, f m κ :=
        Finset.sum_nonneg (fun m _ => hf_nonneg m κ hκ'.le)
      have hS1 : ∑ m ∈ Finset.range N, f m κ ≤ sinhRatio X κ :=
        sum_le_hasSum (Finset.range N) (fun m _ => hf_nonneg m κ hκ'.le) (hasSum_sinhRatio X hκ')
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS0]
      calc ‖E κ‖ * (∑ m ∈ Finset.range N, f m κ) ≤ 2 * (∑ m ∈ Finset.range N, f m κ) :=
            mul_le_mul_of_nonneg_right (hEn κ) hS0
        _ ≤ 2 * sinhRatio X κ := by linarith
    · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun κ hκ => ?_)
      have hκ' : 0 < κ := hκ
      have := (hasSum_sinhRatio X hκ').tendsto_sum_nat
      exact ((Complex.continuous_ofReal.tendsto _).comp this).const_mul (E κ)
  -- (3) the limit of the partial sums, via the cotangent
  set z₁ : ℂ := ((X : ℂ) + I * u) / 2 with hz₁
  set z₂ : ℂ := ((X : ℂ) - I * u) / 2 with hz₂
  have hcm : ∀ m : ℕ, c m = (1 / 2 : ℂ) * ((1 / (z₁ + m) + 1 / (z₁ - (m + 1)))
      + (1 / (z₂ + m) + 1 / (z₂ - (m + 1)))) := by
    intro m
    have e1 : z₁ + m = ((X + 2 * m : ℝ) + I * u) / 2 := by rw [hz₁]; push_cast; ring
    have e2 : z₁ - (m + 1) = -(((2 - X + 2 * m : ℝ) - I * u) / 2) := by rw [hz₁]; push_cast; ring
    have e3 : z₂ + m = ((X + 2 * m : ℝ) - I * u) / 2 := by rw [hz₂]; push_cast; ring
    have e4 : z₂ - (m + 1) = -(((2 - X + 2 * m : ℝ) + I * u) / 2) := by rw [hz₂]; push_cast; ring
    rw [e1, e2, e3, e4, one_div_neg_eq_neg_one_div, one_div_neg_eq_neg_one_div,
      one_div_div, one_div_div, one_div_div, one_div_div]
    simp only [hc]
    ring
  have hz₁m : z₁ ∈ Complex.integerComplement :=
    mem_integerComplement_of_re (by rw [hz₁]; simp; linarith) (by rw [hz₁]; simp; linarith)
  have hz₂m : z₂ ∈ Complex.integerComplement :=
    mem_integerComplement_of_re (by rw [hz₂]; simp; linarith) (by rw [hz₂]; simp; linarith)
  have hcot := ((tendsto_cot_partial hz₁m).add (tendsto_cot_partial hz₂m)).const_mul (1 / 2 : ℂ)
  have hlim : (1 / 2 : ℂ) * (π * Complex.cot (π * z₁) + π * Complex.cot (π * z₂))
      = 2 * π * stripKernel X u := by
    rw [hz₁, hz₂, cot_add_cot_eq h0 h1 u]; ring
  rw [hlim] at hcot
  have hcot' : Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N, c m) atTop
      (𝓝 (2 * π * stripKernel X u)) := by
    refine hcot.congr (fun N => ?_)
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m _ => (hcm m).symm)
  have hdct' : Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N, c m) atTop
      (𝓝 (∫ κ in Ioi (0:ℝ), E κ * (sinhRatio X κ : ℂ))) := by
    simpa only [hpart] using hdct
  simpa only [hE] using tendsto_nhds_unique hdct' hcot'

lemma integrable_cexp_mul_sinhRatio {X : ℝ} (h0 : 0 < X) (h1 : X < 1) (u : ℝ) :
    Integrable (fun κ : ℝ => cexp (I * u * κ) * (sinhRatio X κ : ℂ)) := by
  refine (integrable_sinhRatio h0 h1.le).mono'
    ((by fun_prop : Continuous fun κ : ℝ => cexp (I * u * κ)).aestronglyMeasurable.mul
      (Complex.measurable_ofReal.comp (measurable_sinhRatio X)).aestronglyMeasurable)
    (Eventually.of_forall fun κ => ?_)
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sinhRatio_nonneg h0.le h1.le κ)]
  simp

lemma integral_cexp_mul_sinhRatio {X : ℝ} (h0 : 0 < X) (h1 : X < 1) (u : ℝ) :
    ∫ κ : ℝ, cexp (I * u * κ) * (sinhRatio X κ : ℂ) = 2 * π * stripKernel X u := by
  set g : ℝ → ℂ := fun κ => cexp (I * u * κ) * (sinhRatio X κ : ℂ) with hg
  have hgi : Integrable g := integrable_cexp_mul_sinhRatio h0 h1 u
  have hgi' : Integrable (fun κ => g (-κ)) := by
    have : (fun κ => g (-κ)) = fun κ : ℝ => cexp (I * (-u : ℝ) * κ) * (sinhRatio X κ : ℂ) := by
      funext κ; simp only [hg, sinhRatio_neg]; push_cast; ring_nf
    rw [this]; exact integrable_cexp_mul_sinhRatio h0 h1 (-u)
  have hneg : ∫ x in Iic (0:ℝ), g x = ∫ x in Ioi (0:ℝ), g (-x) := by
    rw [integral_comp_neg_Ioi 0 g, neg_zero]
  rw [← integral_add_compl measurableSet_Ioi hgi, compl_Ioi, hneg,
    ← integral_add hgi.integrableOn hgi'.integrableOn]
  rw [← integral_Ioi_sinhRatio h0 h1 u]
  congr 1
  funext κ
  simp only [hg, sinhRatio_neg]
  push_cast
  ring_nf

/-- The inverse Fourier transform of `ξ ↦ sinhRatio X (2πξ)` is the strip kernel `K_X`. -/
lemma fourierInv_sinhRatio {X : ℝ} (h0 : 0 < X) (h1 : X < 1) :
    𝓕⁻ (fun ξ : ℝ => (sinhRatio X (2 * π * ξ) : ℂ)) = fun u => (stripKernel X u : ℂ) := by
  funext u
  rw [Real.fourierInv_eq']
  have h := Measure.integral_comp_mul_left
    (fun κ : ℝ => cexp (I * u * κ) * (sinhRatio X κ : ℂ)) (2 * π)
  have hrw : (fun v : ℝ => cexp (↑(2 * π * inner ℝ v u) * I) • (sinhRatio X (2 * π * v) : ℂ))
      = fun v => cexp (I * u * ↑(2 * π * v)) * (sinhRatio X (2 * π * v) : ℂ) := by
    funext v
    rw [smul_eq_mul]
    congr 2
    simp only [RCLike.inner_apply, conj_trivial]
    push_cast
    ring
  rw [hrw, h, integral_cexp_mul_sinhRatio h0 h1 u,
    abs_of_pos (by positivity : (0:ℝ) < (2 * π)⁻¹), Complex.real_smul]
  push_cast
  field_simp

/-- **Fourier transform of the strip kernel** (Lemma 5 of the paper on the imaginary axis):
`∫ e^{-iκu} K_X(u) du = sinh(κ(1-X)) / sinh κ` for `κ ≠ 0`. -/
theorem fourier_stripKernel {X : ℝ} (h0 : 0 < X) (h1 : X < 1) {κ : ℝ} (hκ : κ ≠ 0) :
    ∫ u : ℝ, cexp (-(I * κ * u)) * (stripKernel X u : ℂ) = sinhRatio X κ := by
  set f : ℝ → ℂ := fun ξ => (sinhRatio X (2 * π * ξ) : ℂ) with hf
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  have hfi0 : Integrable (fun y : ℝ => ((sinhRatio X y : ℝ) : ℂ)) :=
    (integrable_sinhRatio h0 h1.le).ofReal
  have hfi : Integrable f := hfi0.comp_mul_left' hπ
  have hFf : 𝓕 f = fun u => (stripKernel X u : ℂ) := by
    funext w
    have := Real.fourierInv_eq_fourier_neg f (-w)
    rw [neg_neg] at this
    rw [← this, fourierInv_sinhRatio h0 h1]
    simp only [stripKernel_neg]
  have hFfi : Integrable (𝓕 f) := by rw [hFf]; exact (integrable_stripKernel h0 h1).ofReal
  set v : ℝ := κ / (2 * π) with hv
  have h2v : 2 * π * v = κ := by rw [hv]; field_simp
  have hc1 : ContinuousAt (sinhRatio X) (2 * π * v) := by
    rw [h2v]; exact continuousAt_sinhRatio X hκ
  have hc2 : ContinuousAt (fun ξ : ℝ => sinhRatio X (2 * π * ξ)) v :=
    hc1.comp (by fun_prop : ContinuousAt (fun ξ : ℝ => 2 * π * ξ) v)
  have hcont : ContinuousAt f v := Complex.continuous_ofReal.continuousAt.comp hc2
  have key := hfi.fourier_fourierInv_eq hFfi hcont
  rw [fourierInv_sinhRatio h0 h1, Real.fourier_real_eq_integral_exp_smul] at key
  simp only [hf, h2v] at key
  rw [← key]
  congr 1
  funext u
  rw [smul_eq_mul]
  congr 2
  rw [← h2v]
  push_cast
  ring

lemma integrable_mul_stripKernel {X : ℝ} (h0 : 0 < X) (h1 : X < 1) :
    Integrable (fun u => u * stripKernel X u) := by
  refine ((integrable_stripKernel h0 h1).add (integrable_sq_mul_stripKernel h0 h1)).mono'
    ((continuous_id.mul (continuous_stripKernel h0 h1)).aestronglyMeasurable)
    (Eventually.of_forall fun u => ?_)
  have hK := (stripKernel_pos h0 h1 u).le
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK]
  have : |u| ≤ 1 + u ^ 2 := by nlinarith [abs_nonneg u, sq_abs u]
  simp only [Pi.add_apply]
  nlinarith

/-- The mass of the strip kernel: `∫ K_X = 1 - X`. -/
theorem integral_stripKernel {X : ℝ} (h0 : 0 < X) (h1 : X < 1) :
    ∫ u, stripKernel X u = 1 - X := by
  set T : ℝ → ℂ := fun κ => ∫ u : ℝ, cexp (-(I * κ * u)) * (stripKernel X u : ℂ) with hT
  have hTc : Continuous T := by
    refine continuous_of_dominated (bound := stripKernel X) (fun κ => ?_) (fun κ => ?_)
      (integrable_stripKernel h0 h1) (Eventually.of_forall fun u => ?_)
    · exact (Continuous.mul (by fun_prop)
        (Complex.continuous_ofReal.comp (continuous_stripKernel h0 h1))).aestronglyMeasurable
    · refine Eventually.of_forall (fun u => ?_)
      rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (stripKernel_pos h0 h1 u)]
      simp
    · fun_prop
  have h1' : Tendsto T (𝓝[≠] 0) (𝓝 (T 0)) :=
    hTc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h2' : Tendsto T (𝓝[≠] 0) (𝓝 ((1 - X : ℝ) : ℂ)) := by
    have := (Complex.continuous_ofReal.tendsto _).comp (tendsto_sinhRatio_zero X)
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with κ hκ
    exact (fourier_stripKernel h0 h1 hκ).symm
  have h3 := tendsto_nhds_unique h1' h2'
  simp only [hT, Complex.ofReal_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero,
    one_mul] at h3
  rw [integral_complex_ofReal] at h3
  exact_mod_cast h3

/-- The first moment of the strip kernel vanishes (`K_X` is even). -/
theorem integral_mul_stripKernel (X : ℝ) : ∫ u, u * stripKernel X u = 0 := by
  have h := integral_neg_eq_self (fun u => u * stripKernel X u) volume
  simp only [stripKernel_neg, neg_mul, integral_neg] at h
  linarith

end OQP27.StripL3a
