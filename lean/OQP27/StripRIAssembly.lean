import OQP27.StripRIBoundary
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Proof of the Radon identity, Steps 1-2: `Ψ - E` is affine (module L3b)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

Notation: `F = S_+(A) - S_+(A_d)` (`Fd`), `G = Λ_+(A) - Λ_+(A_d)` (`Gup`), `G₋ = Λ_-(A) - Λ_-(A_d)`
(`Glo`), `Ψ(c) = ∫_0^1 F(τ, c) dτ` (`PsiRI`), `E(c) = ∑ ω(λ⁰_j + c) - ∑ ω(λ_j + c)` with
`ω(z) = z Log z` (`Efun`, `omegaF`), `Θ₁(c) = ∑ Log(λ_j + c) - ∑ Log(λ⁰_j + c)` (`Theta1`); `λ`, `λ⁰` are
the eigenvalues of `A` and `A_d`.
Main results:
* `hasDerivAt_intervalIntegral_param`: differentiation under an interval integral in a complex
  parameter; `eq_of_continuousOn_int`: a continuous `2πiℤ`-valued function on a preconnected set is
  constant;
* `tendsto_im_omegaF`: `Im ω(t + iε) → π min(t, 0)` as `ε → 0⁺`; `hasDerivAt_Efun`: `E' = -Θ₁`;
* `exp_Gup_add_Glo`: `exp(G + G₋) = det(A + c)/det(A_d + c) = exp Θ₁`;
* `hasDerivAt_PsiD` (**Step 1**): `d/dc ∫_δ^{1-δ} F dτ = G(1 - δ, c) - G(δ, c)`; `tendsto_PsiD`:
  `∫_δ^{1-δ} F dτ → Ψ(c)` as `δ → 0⁺`;
* `exists_int_Gup_add_Glo`: `G + G₋ - Θ₁ ≡ 2πik` on `(0, 1) × ℂ₊`;
* `Psi_sub_E_affine` (**Steps 1-2**): `(Ψ - E)(c) - (Ψ - E)(c') = -2πik (c - c')` on `ℂ₊`.

Deviations from the paper: Weierstrass' theorem is replaced by the mean value inequality on segments
(the derivative of `∫_δ^{1-δ} F - E + 2πik c` is `G(1 - δ, c) + G₋(δ, c)`, which tends to `0` uniformly on
compact subsets of `ℂ₊`), and the Schur-complement limit `Θ` of Lemma D(b) is replaced by
`exp(G + G₋) = exp Θ₁` together with the end `G₋(δ, c) → 0`.
Hypotheses: none.
Paper: `iqoqi/programs/oqp27B_all/Q_RI/PROOF.md`, section 2, Steps 1-2.
-/

namespace OQP27.StripL3b

open Matrix Polynomial Complex Metric Filter Topology Set Real MeasureTheory
open scoped Interval

variable {M : ℕ}

/-! ### Generic analytic tools -/

/-- Differentiation under an interval integral in a complex parameter, with jointly continuous
integrand and derivative on a compact box. -/
theorem hasDerivAt_intervalIntegral_param {F F' : ℝ → ℂ → ℂ} {a b : ℝ} (hab : a ≤ b) {c₀ : ℂ}
    {r : ℝ} (hr : 0 < r)
    (hF : ContinuousOn (fun q : ℝ × ℂ => F q.1 q.2) (Icc a b ×ˢ closedBall c₀ r))
    (hF' : ContinuousOn (fun q : ℝ × ℂ => F' q.1 q.2) (Icc a b ×ˢ closedBall c₀ r))
    (hd : ∀ τ ∈ Icc a b, ∀ c ∈ ball c₀ r, HasDerivAt (F τ) (F' τ c) c) :
    HasDerivAt (fun c => ∫ τ in a..b, F τ c) (∫ τ in a..b, F' τ c₀) c₀ := by
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc.prod (isCompact_closedBall c₀ r)).exists_bound_of_continuousOn hF'
  have hsub : Ι a b ⊆ Icc a b := by
    rw [uIoc_of_le hab]; exact Ioc_subset_Icc_self
  have hslice : ∀ c ∈ closedBall c₀ r, ContinuousOn (fun τ => F τ c) (Icc a b) := fun c hc =>
    hF.comp (continuous_id.prodMk continuous_const).continuousOn (fun τ hτ => ⟨hτ, hc⟩)
  have hslice' : ∀ c ∈ closedBall c₀ r, ContinuousOn (fun τ => F' τ c) (Icc a b) := fun c hc =>
    hF'.comp (continuous_id.prodMk continuous_const).continuousOn (fun τ hτ => ⟨hτ, hc⟩)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun c τ => F τ c) (F' := fun c τ => F' τ c) (x₀ := c₀) (s := ball c₀ r)
    (bound := fun _ => C) (μ := volume) (a := a) (b := b)
    (ball_mem_nhds c₀ hr)
    (by
      filter_upwards [ball_mem_nhds c₀ hr] with c hc
      exact ((hslice c (ball_subset_closedBall hc)).mono hsub).aestronglyMeasurable
        measurableSet_uIoc)
    ((hslice c₀ (mem_closedBall_self hr.le)).intervalIntegrable_of_Icc hab)
    (((hslice' c₀ (mem_closedBall_self hr.le)).mono hsub).aestronglyMeasurable measurableSet_uIoc)
    (Eventually.of_forall fun τ hτ c hc => hC (τ, c) ⟨hsub hτ, ball_subset_closedBall hc⟩)
    intervalIntegrable_const
    (Eventually.of_forall fun τ hτ c hc => hd τ (hsub hτ) c hc)
  exact key.2

lemma im_two_pi_I_int (n : ℤ) : (2 * π * I * n : ℂ).im / (2 * π) = n := by
  have : (2 * π * I * n : ℂ).im = 2 * π * n := by simp
  rw [this]
  field_simp

/-- A continuous function with values in `2 π i ℤ` on a preconnected set is constant. -/
lemma eq_of_continuousOn_int {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsPreconnected S)
    {f : X → ℂ} (hf : ContinuousOn f S) (hint : ∀ x ∈ S, ∃ n : ℤ, f x = 2 * π * I * n) {x y : X}
    (hx : x ∈ S) (hy : y ∈ S) : f x = f y := by
  have hg : ContinuousOn (fun z => (f z).im / (2 * π)) S :=
    (Complex.continuous_im.comp_continuousOn hf).div_const _
  have key : ∀ a ∈ S, ∀ b ∈ S, ∀ m n : ℤ, f a = 2 * π * I * m → f b = 2 * π * I * n → m ≤ n →
      m = n := by
    intro a ha b hb m n hm hn hmn
    by_contra hne
    have hlt : m < n := lt_of_le_of_ne hmn hne
    have hga : (f a).im / (2 * π) = m := by rw [hm]; exact im_two_pi_I_int m
    have hgb : (f b).im / (2 * π) = n := by rw [hn]; exact im_two_pi_I_int n
    have hmn' : (m : ℝ) + 1 ≤ n := by exact_mod_cast hlt
    have hmem : (m : ℝ) + 1 / 2 ∈ Icc ((f a).im / (2 * π)) ((f b).im / (2 * π)) := by
      rw [hga, hgb]; constructor <;> linarith
    obtain ⟨z, hz, hgz⟩ := hS.intermediate_value ha hb hg hmem
    obtain ⟨k, hk⟩ := hint z hz
    have hgk : (f z).im / (2 * π) = k := by rw [hk]; exact im_two_pi_I_int k
    simp only at hgz
    rw [hgk] at hgz
    have h2 : ((2 * k : ℤ) : ℝ) = ((2 * m + 1 : ℤ) : ℝ) := by push_cast; linarith
    have h2' : 2 * k = 2 * m + 1 := by exact_mod_cast h2
    omega
  obtain ⟨m, hm⟩ := hint x hx
  obtain ⟨n, hn⟩ := hint y hy
  rcases le_total m n with h | h
  · rw [hm, hn, key x hx y hy m n hm hn h]
  · rw [hm, hn, key y hy x hx n m hn hm h]

/-! ### The function `ω(z) = z Log z` -/

/-- `ω(z) = z Log z`. -/
noncomputable def omegaF (z : ℂ) : ℂ := z * Complex.log z

lemma im_omegaF (z : ℂ) : (omegaF z).im = z.re * Complex.arg z + z.im * Real.log ‖z‖ := by
  unfold omegaF
  rw [Complex.mul_im, Complex.log_im, Complex.log_re]

lemma hasDerivAt_omegaF {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt omegaF (Complex.log z + 1) z := by
  have h := (hasDerivAt_id' z).mul (Complex.hasDerivAt_log hz)
  refine h.congr_deriv ?_
  rw [mul_inv_cancel₀ (slitPlane_ne_zero hz)]
  ring

/-- **Boundary values of `Im ω`**: `Im ((t + i ε) Log (t + i ε)) → π min(t, 0)` as `ε → 0⁺`. -/
theorem tendsto_im_omegaF (t : ℝ) :
    Tendsto (fun ε : ℝ => (omegaF ((t : ℂ) + ε * I)).im) (𝓝[>] 0) (𝓝 (π * min t 0)) := by
  have hre : ∀ ε : ℝ, ((t : ℂ) + ε * I).re = t := by intro ε; simp
  have him : ∀ ε : ℝ, ((t : ℂ) + ε * I).im = ε := by intro ε; simp
  simp only [im_omegaF, hre, him]
  -- the term `ε log |t + i ε|`
  have h2 : Tendsto (fun ε : ℝ => ε * Real.log ‖(t : ℂ) + ε * I‖) (𝓝[>] 0) (𝓝 0) := by
    rcases eq_or_ne t 0 with ht | ht
    · subst ht
      have hc : Tendsto (fun x : ℝ => x * Real.log x) (𝓝 0) (𝓝 0) := by
        have := Real.continuous_mul_log.tendsto 0
        simpa using this
      refine (hc.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0 : ℝ) < ε := hε
      simp [abs_of_pos hε']
    · have hne : ∀ ε : ℝ, ‖(t : ℂ) + ε * I‖ ≠ 0 := by
        intro ε h
        rw [norm_eq_zero] at h
        have := congrArg Complex.re h
        simp at this
        exact ht this
      have hcont : Continuous fun ε : ℝ => ε * Real.log ‖(t : ℂ) + ε * I‖ :=
        continuous_id.mul ((by fun_prop : Continuous fun ε : ℝ => ‖(t : ℂ) + ε * I‖).log hne)
      have := hcont.tendsto 0
      simp only [zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
  -- the term `t arg (t + i ε)`
  have h1 : Tendsto (fun ε : ℝ => t * Complex.arg ((t : ℂ) + ε * I)) (𝓝[>] 0)
      (𝓝 (π * min t 0)) := by
    rcases lt_trichotomy t 0 with ht | ht | ht
    · have hpath : Tendsto (fun ε : ℝ => (t : ℂ) + ε * I) (𝓝[>] 0)
          (𝓝[{z : ℂ | 0 ≤ z.im}] (t : ℂ)) := by
        apply tendsto_nhdsWithin_iff.mpr
        constructor
        · have : Continuous fun ε : ℝ => (t : ℂ) + ε * I := by fun_prop
          have h := this.tendsto 0
          simp only [ofReal_zero, zero_mul, add_zero] at h
          exact h.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with ε hε
          show 0 ≤ ((t : ℂ) + ε * I).im
          rw [him]; exact le_of_lt hε
      have harg := (Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
        (z := (t : ℂ)) (by simpa using ht) (by simp)).comp hpath
      have := harg.const_mul t
      rw [min_eq_left ht.le, mul_comm π t]
      exact this
    · subst ht
      simp only [zero_mul, min_self, mul_zero]
      exact tendsto_const_nhds
    · have hslit : (t : ℂ) ∈ slitPlane := by simp [slitPlane, ht]
      have hcont : ContinuousAt (fun ε : ℝ => Complex.arg ((t : ℂ) + ε * I)) 0 := by
        have h1 : ContinuousAt (fun ε : ℝ => (t : ℂ) + ε * I) 0 := by fun_prop
        have h2 : ContinuousAt Complex.arg ((t : ℂ) + ((0 : ℝ) : ℂ) * I) := by
          simp only [ofReal_zero, zero_mul, add_zero]
          exact Complex.continuousAt_arg hslit
        exact ContinuousAt.comp (f := fun ε : ℝ => (t : ℂ) + ε * I) (x := (0 : ℝ)) h2 h1
      have := (hcont.tendsto.const_mul t).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simp only [ofReal_zero, zero_mul, add_zero, Complex.arg_ofReal_of_nonneg ht.le,
        mul_zero] at this
      rw [min_eq_right ht.le, mul_zero]
      exact this
  have := h1.add h2
  rw [add_zero] at this
  exact this

/-! ### The comparison function `E(c) = Tr ω(A_d + c) - Tr ω(A + c)` -/

/-- `E(c) = ∑ ω(λ⁰_j + c) - ∑ ω(λ_j + c)`. -/
noncomputable def Efun (lam lam0 : Fin M → ℝ) (c : ℂ) : ℂ :=
  ∑ i, omegaF ((lam0 i : ℂ) + c) - ∑ i, omegaF ((lam i : ℂ) + c)

/-- `Θ₁(c) = ∑ Log (λ_j + c) - ∑ Log (λ⁰_j + c)`. -/
noncomputable def Theta1 (lam lam0 : Fin M → ℝ) (c : ℂ) : ℂ :=
  ∑ i, Complex.log ((lam i : ℂ) + c) - ∑ i, Complex.log ((lam0 i : ℂ) + c)

lemma mem_slitPlane_of_im_pos {w : ℂ} (hw : 0 < w.im) : w ∈ slitPlane := Or.inr hw.ne'

lemma ofReal_add_mem_slitPlane (x : ℝ) {c : ℂ} (hc : 0 < c.im) : (x : ℂ) + c ∈ slitPlane :=
  mem_slitPlane_of_im_pos (by simpa using hc)

theorem hasDerivAt_Efun (lam lam0 : Fin M → ℝ) {c : ℂ} (hc : 0 < c.im) :
    HasDerivAt (Efun lam lam0) (-Theta1 lam lam0 c) c := by
  have h0 : HasDerivAt (fun c => ∑ i, omegaF ((lam0 i : ℂ) + c))
      (∑ i, (Complex.log ((lam0 i : ℂ) + c) + 1)) c :=
    HasDerivAt.fun_sum fun i _ =>
      (hasDerivAt_omegaF (ofReal_add_mem_slitPlane (lam0 i) hc)).comp_const_add _ _
  have h1 : HasDerivAt (fun c => ∑ i, omegaF ((lam i : ℂ) + c))
      (∑ i, (Complex.log ((lam i : ℂ) + c) + 1)) c :=
    HasDerivAt.fun_sum fun i _ =>
      (hasDerivAt_omegaF (ofReal_add_mem_slitPlane (lam i) hc)).comp_const_add _ _
  refine (h0.sub h1).congr_deriv ?_
  unfold Theta1
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

lemma continuousOn_Theta1 (lam lam0 : Fin M → ℝ) :
    ContinuousOn (Theta1 lam lam0) {c : ℂ | 0 < c.im} := by
  unfold Theta1
  apply ContinuousOn.sub <;> apply continuousOn_finsetSum <;> intro i _ <;>
    exact ContinuousOn.clog (continuousOn_const.add continuousOn_id)
      (fun c hc => ofReal_add_mem_slitPlane _ hc)


/-! ### The differences `F = S_+(A) - S_+(A_d)`, `G = Λ_+(A) - Λ_+(A_d)`, `G₋ = Λ_-(A) - Λ_-(A_d)` -/

/-- `F(τ, c) = S_+(A)(τ, c) - S_+(A_d)(τ, c)`. -/
noncomputable def Fd (P A : Matrix (Fin M) (Fin M) ℂ) (τ : ℝ) (c : ℂ) : ℂ :=
  Sup P A τ c - Sup P (pinch P A) τ c

/-- `∂_c F`. -/
noncomputable def Fd' (P A : Matrix (Fin M) (Fin M) ℂ) (τ : ℝ) (c : ℂ) : ℂ :=
  deriv (fun c => Sup P A τ c) c - deriv (fun c => Sup P (pinch P A) τ c) c

/-- `G(τ, c) = Λ_+(A)(τ, c) - Λ_+(A_d)(τ, c)`. -/
noncomputable def Gup (P A : Matrix (Fin M) (Fin M) ℂ) (τ : ℝ) (c : ℂ) : ℂ :=
  Lup P A τ c - Lup P (pinch P A) τ c

/-- `G₋(τ, c) = Λ_-(A)(τ, c) - Λ_-(A_d)(τ, c)`. -/
noncomputable def Glo (P A : Matrix (Fin M) (Fin M) ℂ) (τ : ℝ) (c : ℂ) : ℂ :=
  Llo P A τ c - Llo P (pinch P A) τ c

/-- `Ψ(c) = ∫_0^1 (S_+(A) - S_+(A_d)) dτ`. -/
noncomputable def PsiRI (P A : Matrix (Fin M) (Fin M) ℂ) (c : ℂ) : ℂ :=
  ∫ τ in Ioo (0 : ℝ) 1, Fd P A τ c

/-! ### `exp Θ₁ = det (A + c) / det (A_d + c)` and `exp (Λ_+ + Λ_-) = det ((P - τ)⁻¹ (A + c))` -/

section ExpDet

variable {P A : Matrix (Fin M) (Fin M) ℂ}

lemma exp_sum_log_eigen {N : Matrix (Fin M) (Fin M) ℂ} (hN : N.IsHermitian) {c : ℂ}
    (hc : 0 < c.im) :
    Complex.exp (∑ i, Complex.log ((hN.eigenvalues i : ℂ) + c)) = (N + c • 1).det := by
  rw [Complex.exp_sum, det_add_smul_one_eq_prod hN]
  exact Finset.prod_congr rfl fun i _ =>
    Complex.exp_log (slitPlane_ne_zero (ofReal_add_mem_slitPlane _ hc))

lemma exp_Theta1 (hA : A.IsHermitian) (hAd : (pinch P A).IsHermitian) {c : ℂ} (hc : 0 < c.im) :
    Complex.exp (Theta1 hA.eigenvalues hAd.eigenvalues c)
      = (A + c • 1).det / (pinch P A + c • 1).det := by
  unfold Theta1
  rw [Complex.exp_sub, exp_sum_log_eigen hA hc, exp_sum_log_eigen hAd hc]

lemma Lup_add_Llo (hP : IsProj P) (hA : A.IsHermitian) {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1)
    {c : ℂ} (hc : 0 < c.im) :
    Lup P A τ c + Llo P A τ c = ((Rt P A τ c).map Complex.log).sum := by
  unfold Lup Llo
  rw [← Multiset.sum_add, ← Multiset.map_add, upper_add_lower (Rt_im_ne_zero hP hA h0 h1 hc)]

lemma exp_Lup_add_Llo (hP : IsProj P) (hA : A.IsHermitian) {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1)
    {c : ℂ} (hc : 0 < c.im) :
    Complex.exp (Lup P A τ c + Llo P A τ c)
      = ((P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹ * (A + c • 1)).det := by
  have hne : ∀ y ∈ Rt P A τ c, y ≠ 0 := fun y hy h =>
    (Rt_im_ne_zero hP hA h0 h1 hc y hy) (by rw [h]; simp)
  rw [Lup_add_Llo hP hA h0 h1 hc, Complex.exp_multiset_sum, Multiset.map_map,
    Multiset.map_congr rfl (f := Complex.exp ∘ Complex.log) (g := fun y => y)
      (fun y hy => Complex.exp_log (hne y hy)),
    Multiset.map_id', Matrix.det_eq_prod_roots_charpoly]
  rfl

lemma exp_Gup_add_Glo (hP : IsProj P) (hA : A.IsHermitian) {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1)
    {c : ℂ} (hc : 0 < c.im) :
    Complex.exp (Gup P A τ c + Glo P A τ c)
      = Complex.exp (Theta1 hA.eigenvalues (isHermitian_pinch hP.1 hA).eigenvalues c) := by
  have hAd := isHermitian_pinch hP.1 hA
  have e : Gup P A τ c + Glo P A τ c
      = (Lup P A τ c + Llo P A τ c) - (Lup P (pinch P A) τ c + Llo P (pinch P A) τ c) := by
    unfold Gup Glo; ring
  have hD : ((P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹).det ≠ 0 :=
    (Matrix.isUnit_nonsing_inv_det _ (isUnit_det_P_sub hP.2 h0.ne' h1.ne)).ne_zero
  rw [e, Complex.exp_sub, exp_Lup_add_Llo hP hA h0 h1 hc, exp_Lup_add_Llo hP hAd h0 h1 hc,
    exp_Theta1 hA hAd hc, Matrix.det_mul, Matrix.det_mul, mul_div_mul_left _ _ hD]

end ExpDet

section Diff

variable {P A : Matrix (Fin M) (Fin M) ℂ}

theorem diff_global (hP : IsProj P) (hA : A.IsHermitian) :
    (∀ q ∈ domRI, HasDerivAt (fun c => Fd P A q.1 c) (Fd' P A q.1 q.2) q.2) ∧
    (∀ q ∈ domRI, HasDerivAt (fun τ => Gup P A τ q.2) (Fd' P A q.1 q.2) q.1) ∧
    ContinuousOn (fun q : ℝ × ℂ => Fd' P A q.1 q.2) domRI ∧
    ContinuousOn (fun q : ℝ × ℂ => Fd P A q.1 q.2) domRI ∧
    ContinuousOn (fun q : ℝ × ℂ => Gup P A q.1 q.2) domRI ∧
    ContinuousOn (fun q : ℝ × ℂ => Glo P A q.1 q.2) domRI := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := upper_global hP hA
  obtain ⟨b1, b2, b3, b4, b5⟩ := upper_global hP (isHermitian_pinch hP.1 hA)
  obtain ⟨-, -, -, -, c5⟩ := lower_global hP hA
  obtain ⟨-, -, -, -, d5⟩ := lower_global hP (isHermitian_pinch hP.1 hA)
  refine ⟨fun q hq => ?_, fun q hq => ?_, ?_, ?_, ?_, ?_⟩
  · have h := (a1 q hq).sub (b1 q hq)
    unfold Fd Fd'
    exact h
  · have h := (a2 q hq).sub (b2 q hq)
    unfold Gup Fd'
    exact h
  · have h := a3.sub b3
    unfold Fd'
    exact h
  · have h := a4.sub b4
    unfold Fd
    exact h
  · have h := a5.sub b5
    unfold Gup
    exact h
  · have h := c5.sub d5
    unfold Glo
    exact h

/-- **Lemma B(iii)** in the form used below: `|F(τ, c)| ≤ 2 M √K / √(τ (1 - τ))`. -/
lemma norm_Fd_le (hP : IsProj P) (hA : A.IsHermitian) {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1)
    {c : ℂ} (hc : 0 < c.im) {K : ℝ} (hK1 : frob (A + c • 1) ≤ K)
    (hK2 : frob (pinch P A + c • 1) ≤ K) :
    ‖Fd P A τ c‖ ≤ 2 * M * √K * wgt τ := by
  have := norm_Sup_sub_le hP hA h0 h1 hc hK1 hK2
  unfold Fd wgt
  calc _ ≤ 2 * M * (√K / √(τ * (1 - τ))) := this
    _ = _ := by rw [div_eq_mul_inv]; ring

lemma integrableOn_Fd (hP : IsProj P) (hA : A.IsHermitian) {c : ℂ} (hc : 0 < c.im) :
    IntegrableOn (fun τ => Fd P A τ c) (Ioo 0 1) := by
  obtain ⟨-, -, -, hcont, -, -⟩ := diff_global hP hA
  have hmeas : AEStronglyMeasurable (fun τ => Fd P A τ c) (volume.restrict (Ioo 0 1)) := by
    have h := hcont.comp (s := Ioo 0 1) (Continuous.prodMk_left c).continuousOn
      (fun τ hτ => ⟨hτ, hc⟩)
    exact h.aestronglyMeasurable measurableSet_Ioo
  set K := max (frob (A + c • 1)) (frob (pinch P A + c • 1))
  refine Integrable.mono' (integrableOn_wgt.const_mul (2 * M * √K)) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
  exact norm_Fd_le hP hA hτ.1 hτ.2 hc (le_max_left _ _) (le_max_right _ _)

lemma closedBall_im_pos {c : ℂ} (hc : 0 < c.im) : ∀ c' ∈ closedBall c (c.im / 2), 0 < c'.im := by
  intro c' hc'
  rw [mem_closedBall, dist_eq_norm] at hc'
  have h1 := Complex.abs_im_le_norm (c' - c)
  rw [Complex.sub_im] at h1
  have h2 := neg_abs_le (c'.im - c.im)
  linarith

/-- **Step 1**: `d/dc ∫_δ^{1-δ} F(τ, c) dτ = G(1 - δ, c) - G(δ, c)` (Burgers identity + FTC). -/
theorem hasDerivAt_PsiD (hP : IsProj P) (hA : A.IsHermitian) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 2) {c : ℂ} (hc : 0 < c.im) :
    HasDerivAt (fun c => ∫ τ in δ..(1 - δ), Fd P A τ c) (Gup P A (1 - δ) c - Gup P A δ c) c := by
  obtain ⟨g1, g2, g3, g4, -, -⟩ := diff_global hP hA
  have hab : δ ≤ 1 - δ := by linarith
  have hr0 : 0 < c.im / 2 := by positivity
  have hbox : Icc δ (1 - δ) ×ˢ closedBall c (c.im / 2) ⊆ domRI := fun q hq =>
    ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, closedBall_im_pos hc q.2 hq.2⟩
  have hderiv := hasDerivAt_intervalIntegral_param (F := Fd P A) (F' := Fd' P A) hab hr0
    (g4.mono hbox) (g3.mono hbox)
    (fun τ hτ c' hc' => g1 (τ, c') (hbox ⟨hτ, ball_subset_closedBall hc'⟩))
  refine hderiv.congr_deriv ?_
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun τ => Gup P A τ c)
    (fun τ hτ => ?_) ?_
  · rw [uIcc_of_le hab] at hτ
    exact g2 (τ, c) (hbox ⟨hτ, mem_closedBall_self hr0.le⟩)
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    have h := g3.comp (s := Icc δ (1 - δ)) (Continuous.prodMk_left c).continuousOn
      (fun τ hτ => hbox ⟨hτ, mem_closedBall_self hr0.le⟩)
    exact h

/-- `∫_δ^{1-δ} F(τ, c) dτ → Ψ(c)` as `δ → 0⁺`. -/
theorem tendsto_PsiD (hP : IsProj P) (hA : A.IsHermitian) {c : ℂ} (hc : 0 < c.im) :
    Tendsto (fun δ => ∫ τ in δ..(1 - δ), Fd P A τ c) (𝓝[>] 0) (𝓝 (PsiRI P A c)) := by
  have hint := integrableOn_Fd hP hA hc
  set K := max (frob (A + c • 1)) (frob (pinch P A + c • 1))
  have heq : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∫ τ in Ioo (0 : ℝ) 1,
      (Ioc δ (1 - δ)).indicator (fun τ => Fd P A τ c) τ = ∫ τ in δ..(1 - δ), Fd P A τ c := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with δ hδ
    have hsub : Ioc δ (1 - δ) ⊆ Ioo 0 1 := fun τ hτ =>
      ⟨by linarith [hδ.1, hτ.1], by linarith [hδ.1, hτ.2]⟩
    rw [intervalIntegral.integral_of_le (by linarith [hδ.2]),
      setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.mpr hsub]
  refine Tendsto.congr' heq ?_
  unfold PsiRI
  refine tendsto_integral_filter_of_dominated_convergence (fun τ => 2 * M * √K * wgt τ)
    (Eventually.of_forall fun δ => hint.1.indicator measurableSet_Ioc)
    (Eventually.of_forall fun δ => ?_) (integrableOn_wgt.const_mul _) ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
    rw [Set.indicator_apply]
    split_ifs
    · exact norm_Fd_le hP hA hτ.1 hτ.2 hc (le_max_left _ _) (le_max_right _ _)
    · rw [norm_zero]; exact mul_nonneg (by positivity) (wgt_nonneg τ)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
    apply tendsto_const_nhds.congr'
    have hpos : (0 : ℝ) < min τ (1 - τ) := lt_min hτ.1 (by linarith [hτ.2])
    filter_upwards [Ioo_mem_nhdsGT hpos] with δ hδ
    have h1 := min_le_left τ (1 - τ)
    have h2 := min_le_right τ (1 - τ)
    have hmem : τ ∈ Ioc δ (1 - δ) := ⟨by linarith [hδ.2], by linarith [hδ.2]⟩
    exact (Set.indicator_of_mem (s := Ioc δ (1 - δ)) hmem (fun τ => Fd P A τ c)).symm

end Diff

/-! ### Steps 1-2: `Ψ - E` is affine with slope `-2 π i k` -/

section Affine

variable {P A : Matrix (Fin M) (Fin M) ℂ}

/-- `G + G₋ - Θ₁ ∈ 2 π i ℤ` is continuous on the connected set `(0, 1) × ℂ₊`, hence constant. -/
theorem exists_int_Gup_add_Glo (hP : IsProj P) (hA : A.IsHermitian) :
    ∃ k : ℤ, ∀ q ∈ domRI, Gup P A q.1 q.2 + Glo P A q.1 q.2
      - Theta1 hA.eigenvalues (isHermitian_pinch hP.1 hA).eigenvalues q.2 = 2 * π * I * k := by
  have hAd := isHermitian_pinch hP.1 hA
  obtain ⟨-, -, -, -, h5, h6⟩ := diff_global hP hA
  have hcont : ContinuousOn (fun q : ℝ × ℂ => Gup P A q.1 q.2 + Glo P A q.1 q.2
      - Theta1 hA.eigenvalues hAd.eigenvalues q.2) domRI :=
    (h5.add h6).sub ((continuousOn_Theta1 _ _).comp continuous_snd.continuousOn
      (fun q hq => hq.2))
  have hint : ∀ q ∈ domRI, ∃ n : ℤ, Gup P A q.1 q.2 + Glo P A q.1 q.2
      - Theta1 hA.eigenvalues hAd.eigenvalues q.2 = 2 * π * I * n := by
    intro q hq
    have he := exp_Gup_add_Glo hP hA hq.1.1 hq.1.2 hq.2
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
    exact ⟨n, by rw [hn]; ring⟩
  have hconn : IsPreconnected domRI :=
    ((convex_Ioo (0 : ℝ) 1).prod (convex_halfSpace_im_gt 0)).isPreconnected
  have hq0 : ((1 / 2 : ℝ), I) ∈ domRI := ⟨⟨by norm_num, by norm_num⟩, by simp⟩
  obtain ⟨k, hk⟩ := hint _ hq0
  exact ⟨k, fun q hq => (eq_of_continuousOn_int hconn hcont hint hq hq0).trans hk⟩

/-- **Steps 1-2 of the proof of RI**: there is `k ∈ ℤ` with
`(Ψ - E)(c) - (Ψ - E)(c') = -2 π i k (c - c')` on `ℂ₊`. -/
theorem Psi_sub_E_affine (hP : IsProj P) (hA : A.IsHermitian) :
    ∃ k : ℤ, ∀ c c' : ℂ, 0 < c.im → 0 < c'.im →
      (PsiRI P A c - Efun hA.eigenvalues (isHermitian_pinch hP.1 hA).eigenvalues c)
        - (PsiRI P A c' - Efun hA.eigenvalues (isHermitian_pinch hP.1 hA).eigenvalues c')
        = -(2 * π * I * k) * (c - c') := by
  set lam := hA.eigenvalues with hlam
  set lam0 := (isHermitian_pinch hP.1 hA).eigenvalues with hlam0
  obtain ⟨k, hk⟩ := exists_int_Gup_add_Glo hP hA
  refine ⟨k, fun c c' hc hc' => ?_⟩
  set κ : ℂ := 2 * π * I * k with hκ
  set Kseg := segment ℝ c' c with hKseg
  have hKc : IsCompact Kseg := by
    rw [hKseg, segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  have hKpos : ∀ z ∈ Kseg, 0 < z.im := fun z hz =>
    (convex_halfSpace_im_gt 0).segment_subset hc' hc hz
  have hKconv : Convex ℝ Kseg := convex_segment c' c
  set X := ‖(PsiRI P A c - Efun lam lam0 c + κ * c) - (PsiRI P A c' - Efun lam lam0 c' + κ * c')‖
    with hX
  have key : ∀ η > 0, X ≤ η * ‖c - c'‖ := by
    intro η hη
    obtain ⟨δ₁, hδ₁, hup⟩ := upper_end hP hA hKc hKpos (half_pos hη)
    obtain ⟨δ₂, hδ₂, hlo⟩ := lower_end hP hA hKc hKpos (half_pos hη)
    have hbound : ∀ δ, 0 < δ → δ < min (min δ₁ δ₂) (1 / 2) →
        ‖((∫ τ in δ..(1 - δ), Fd P A τ c) - Efun lam lam0 c + κ * c)
          - ((∫ τ in δ..(1 - δ), Fd P A τ c') - Efun lam lam0 c' + κ * c')‖ ≤ η * ‖c - c'‖ := by
      intro δ hδ hδm
      have hδ1 : δ < δ₁ := lt_of_lt_of_le hδm (le_trans (min_le_left _ _) (min_le_left _ _))
      have hδ2 : δ < δ₂ := lt_of_lt_of_le hδm (le_trans (min_le_left _ _) (min_le_right _ _))
      have hδh : δ < 1 / 2 := lt_of_lt_of_le hδm (min_le_right _ _)
      have hderiv : ∀ z ∈ Kseg, HasDerivWithinAt
          (fun z => (∫ τ in δ..(1 - δ), Fd P A τ z) - Efun lam lam0 z + κ * z)
          (Gup P A (1 - δ) z + Glo P A δ z) Kseg z := by
        intro z hz
        have hz0 := hKpos z hz
        have h1 := hasDerivAt_PsiD hP hA hδ hδh hz0
        have h2 := hasDerivAt_Efun lam lam0 hz0
        have h3 := (hasDerivAt_id' z).const_mul κ
        have h4 := (h1.sub h2).add h3
        have hq := hk (δ, z) ⟨⟨hδ, by linarith⟩, hz0⟩
        simp only at hq
        have hder : Gup P A (1 - δ) z - Gup P A δ z - -Theta1 lam lam0 z + κ * 1
            = Gup P A (1 - δ) z + Glo P A δ z := by
          linear_combination -hq
        have h5 := (h4.congr_deriv hder).hasDerivWithinAt (s := Kseg)
        exact h5
      have hbd : ∀ z ∈ Kseg, ‖Gup P A (1 - δ) z + Glo P A δ z‖ ≤ η := by
        intro z hz
        have a1 : ‖Gup P A (1 - δ) z‖ < η / 2 := hup (1 - δ) (by linarith) (by linarith) z hz
        have a2 : ‖Glo P A δ z‖ < η / 2 := hlo δ hδ hδ2 z hz
        calc _ ≤ ‖Gup P A (1 - δ) z‖ + ‖Glo P A δ z‖ := norm_add_le _ _
          _ ≤ η / 2 + η / 2 := add_le_add a1.le a2.le
          _ = η := by ring
      have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbd hKconv
        (left_mem_segment ℝ c' c) (right_mem_segment ℝ c' c)
      exact hmv
    have hlim : Tendsto (fun δ => ‖((∫ τ in δ..(1 - δ), Fd P A τ c) - Efun lam lam0 c + κ * c)
          - ((∫ τ in δ..(1 - δ), Fd P A τ c') - Efun lam lam0 c' + κ * c')‖) (𝓝[>] 0)
        (𝓝 X) :=
      ((((tendsto_PsiD hP hA hc).sub_const _).add_const _).sub
        (((tendsto_PsiD hP hA hc').sub_const _).add_const _)).norm
    apply le_of_tendsto hlim
    have hm : (0 : ℝ) < min (min δ₁ δ₂) (1 / 2) := lt_min (lt_min hδ₁ hδ₂) (by norm_num)
    filter_upwards [Ioo_mem_nhdsGT hm] with δ hδ
    exact hbound δ hδ.1 hδ.2
  have hX0 : X ≤ 0 := by
    by_contra hXpos
    have hXp : 0 < X := not_le.mp hXpos
    have hY : 0 ≤ ‖c - c'‖ := norm_nonneg _
    have h := key (X / (2 * (‖c - c'‖ + 1))) (by positivity)
    have h2 : X / (2 * (‖c - c'‖ + 1)) * ‖c - c'‖ < X := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have hz : (PsiRI P A c - Efun lam lam0 c + κ * c) - (PsiRI P A c' - Efun lam lam0 c' + κ * c')
      = 0 := norm_eq_zero.mp (le_antisymm hX0 (norm_nonneg _))
  linear_combination hz

end Affine

end OQP27.StripL3b
