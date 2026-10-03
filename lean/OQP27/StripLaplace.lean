import OQP27.StripKernel
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The Laplace transform of the strip Poisson kernel (module L3a)

Lemma 5 of the paper in its original form: for `0 < X < 1` and real `a` with `0 < |a| < π`,
`∫ e^{-au} K_X(u) du = sin(a(1 - X)) / sin(a)` (`laplace_stripKernel`), and `= 1 - X` at `a = 0`
(`integral_stripKernel`), and eq. (5.1) of the paper for real `a` (`laplace_stripKernel_sub`).
More generally `sin(a) ∫ e^{-au} K_X(u) du = sin(a(1 - X))` for every
complex `a` with `|Re a| < π` (`sin_mul_kernelLaplace`).

Proof: `a ↦ ∫ e^{-au} K_X(u) du` is holomorphic on the strip `|Re a| < π` (differentiation under
the integral sign, `K_X(u) ≤ C_X e^{-π|u|}`); on the imaginary axis the identity is the Fourier
transform `fourier_stripKernel`; the identity theorem extends it to the whole strip.

This file is not needed for Theorem 2 (`OQP27/StripFromBMV.lean` works on the imaginary axis).

Paper: `iqoqi/programs/oqp27B_all/Q_2bmv/PROOF.md`, section 5, Lemma 5.
-/

open Real MeasureTheory Set Filter Topology Complex

namespace OQP27.StripL3a

/-- The strip `|Re a| < π`. -/
def laplaceStrip : Set ℂ := Complex.re ⁻¹' Ioo (-π) π

lemma isOpen_laplaceStrip : IsOpen laplaceStrip := isOpen_Ioo.preimage Complex.continuous_re

lemma isPreconnected_laplaceStrip : IsPreconnected laplaceStrip :=
  ((convex_Ioo (-π) π).linear_preimage Complex.reLm).isPreconnected

lemma mem_laplaceStrip {a : ℂ} : a ∈ laplaceStrip ↔ |a.re| < π := by
  simp [laplaceStrip, abs_lt]

/-- The two-sided Laplace transform `a ↦ ∫ e^{-au} K_X(u) du` of the strip kernel. -/
noncomputable def kernelLaplace (X : ℝ) (a : ℂ) : ℂ :=
  ∫ u : ℝ, cexp (-(a * u)) * (stripKernel X u : ℂ)

lemma norm_cexp_neg_mul_le (a : ℂ) (u : ℝ) : ‖cexp (-(a * u))‖ ≤ Real.exp (|a.re| * |u|) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]
  rw [← abs_mul]
  exact neg_le_abs _

lemma abs_mul_exp_neg_le {ε : ℝ} (hε : 0 < ε) (u : ℝ) :
    |u| * Real.exp (-(ε * |u|)) ≤ (2 / ε) * Real.exp (-(ε / 2 * |u|)) := by
  have h1 : ε / 2 * |u| ≤ Real.exp (ε / 2 * |u|) := by
    have := Real.add_one_le_exp (ε / 2 * |u|); linarith
  have h2 : Real.exp (-(ε * |u|)) = Real.exp (-(ε / 2 * |u|)) * Real.exp (-(ε / 2 * |u|)) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp (ε / 2 * |u|) * Real.exp (-(ε / 2 * |u|)) = 1 := by
    rw [← Real.exp_add]; simp
  have hE := Real.exp_pos (-(ε / 2 * |u|))
  calc |u| * Real.exp (-(ε * |u|))
      = (|u| * Real.exp (-(ε / 2 * |u|))) * Real.exp (-(ε / 2 * |u|)) := by rw [h2]; ring
    _ ≤ (2 / ε) * Real.exp (-(ε / 2 * |u|)) := by
        apply mul_le_mul_of_nonneg_right _ hE.le
        have h4 : |u| ≤ (2 / ε) * Real.exp (ε / 2 * |u|) := by
          calc |u| = (2 / ε) * (ε / 2 * |u|) := by field_simp
            _ ≤ (2 / ε) * Real.exp (ε / 2 * |u|) := mul_le_mul_of_nonneg_left h1 (by positivity)
        calc |u| * Real.exp (-(ε / 2 * |u|))
            ≤ (2 / ε) * Real.exp (ε / 2 * |u|) * Real.exp (-(ε / 2 * |u|)) :=
              mul_le_mul_of_nonneg_right h4 hE.le
          _ = 2 / ε := by rw [mul_assoc, h3, mul_one]

lemma integrable_abs_mul_exp_neg {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun u : ℝ => |u| * Real.exp (-(ε * |u|))) := by
  refine ((integrable_exp_neg_mul_abs (half_pos hε)).const_mul (2 / ε)).mono'
    ((continuous_abs.mul (by fun_prop)).aestronglyMeasurable) (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact abs_mul_exp_neg_le hε u

lemma laplace_integrand_le {X : ℝ} (h0 : 0 < X) (h1 : X < 1) (a : ℂ) (u : ℝ) :
    ‖cexp (-(a * u)) * (stripKernel X u : ℂ)‖
      ≤ kernelConst X * Real.exp (-((π - |a.re|) * |u|)) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (stripKernel_pos h0 h1 u)]
  have hK := stripKernel_le h0 h1 u
  have hE := norm_cexp_neg_mul_le a u
  have hC := kernelConst_pos h0 h1
  calc ‖cexp (-(a * u))‖ * stripKernel X u
      ≤ Real.exp (|a.re| * |u|) * (kernelConst X * Real.exp (-(π * |u|))) :=
        mul_le_mul hE hK (stripKernel_pos h0 h1 u).le (Real.exp_pos _).le
    _ = kernelConst X * Real.exp (-((π - |a.re|) * |u|)) := by
        rw [mul_left_comm, ← Real.exp_add]; ring_nf

lemma integrable_laplace_integrand {X : ℝ} (h0 : 0 < X) (h1 : X < 1) {a : ℂ}
    (ha : |a.re| < π) : Integrable (fun u : ℝ => cexp (-(a * u)) * (stripKernel X u : ℂ)) := by
  refine ((integrable_exp_neg_mul_abs (sub_pos.mpr ha)).const_mul (kernelConst X)).mono'
    ((Continuous.mul (by fun_prop)
      (Complex.continuous_ofReal.comp (continuous_stripKernel h0 h1))).aestronglyMeasurable)
    (Eventually.of_forall fun u => laplace_integrand_le h0 h1 a u)

/-- `a ↦ ∫ e^{-au} K_X(u) du` is holomorphic on the strip `|Re a| < π`. -/
theorem differentiableOn_kernelLaplace {X : ℝ} (h0 : 0 < X) (h1 : X < 1) :
    DifferentiableOn ℂ (kernelLaplace X) laplaceStrip := by
  intro a₀ ha₀
  rw [mem_laplaceStrip] at ha₀
  set ε := (π - |a₀.re|) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hball : Metric.ball a₀ ε ∈ 𝓝 a₀ := Metric.ball_mem_nhds a₀ hεpos
  have hre : ∀ a ∈ Metric.ball a₀ ε, |a.re| ≤ |a₀.re| + ε := by
    intro a ha
    have h1 : |a.re - a₀.re| ≤ ‖a - a₀‖ := by
      rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
    have h2 : ‖a - a₀‖ < ε := by simpa [dist_eq_norm] using ha
    have h3 := abs_sub_abs_le_abs_sub a.re a₀.re
    linarith
  have hderiv : ∀ (a : ℂ) (u : ℝ), HasDerivAt (fun a : ℂ => cexp (-(a * u)) * (stripKernel X u : ℂ))
      (-(u : ℂ) * cexp (-(a * u)) * (stripKernel X u : ℂ)) a := by
    intro a u
    have h := (((hasDerivAt_id a).mul_const (u : ℂ)).neg.cexp).mul_const (stripKernel X u : ℂ)
    refine h.congr_deriv ?_
    simp only [id_eq, one_mul, Pi.neg_apply]
    ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun a : ℂ => fun u : ℝ => cexp (-(a * u)) * (stripKernel X u : ℂ))
    (F' := fun a : ℂ => fun u : ℝ => -(u : ℂ) * cexp (-(a * u)) * (stripKernel X u : ℂ))
    (bound := fun u : ℝ => kernelConst X * (|u| * Real.exp (-(ε * |u|))))
    hball
    (Eventually.of_forall fun a => (Continuous.mul (by fun_prop)
      (Complex.continuous_ofReal.comp (continuous_stripKernel h0 h1))).aestronglyMeasurable)
    (integrable_laplace_integrand h0 h1 ha₀)
    ((Continuous.mul (by fun_prop)
      (Complex.continuous_ofReal.comp (continuous_stripKernel h0 h1))).aestronglyMeasurable)
    (Eventually.of_forall fun u a ha => ?_)
    ((integrable_abs_mul_exp_neg hεpos).const_mul _)
    (Eventually.of_forall fun u a _ => hderiv a u)
  · exact key.2.differentiableAt.differentiableWithinAt
  · have hb := laplace_integrand_le h0 h1 a u
    have hra := hre a ha
    rw [show -(u : ℂ) * cexp (-(a * u)) * (stripKernel X u : ℂ)
        = -(u : ℂ) * (cexp (-(a * u)) * (stripKernel X u : ℂ)) by ring, norm_mul, norm_neg,
      Complex.norm_real, Real.norm_eq_abs]
    have hmono : Real.exp (-((π - |a.re|) * |u|)) ≤ Real.exp (-(ε * |u|)) := by
      apply Real.exp_le_exp.mpr
      have : ε ≤ π - |a.re| := by rw [hε] at hra ⊢; linarith
      nlinarith [abs_nonneg u]
    calc |u| * ‖cexp (-(a * u)) * (stripKernel X u : ℂ)‖
        ≤ |u| * (kernelConst X * Real.exp (-((π - |a.re|) * |u|))) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg u)
      _ ≤ |u| * (kernelConst X * Real.exp (-(ε * |u|))) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg u)
          exact mul_le_mul_of_nonneg_left hmono (kernelConst_pos h0 h1).le
      _ = kernelConst X * (|u| * Real.exp (-(ε * |u|))) := by ring

/-- `sin(a) ∫ e^{-au} K_X(u) du = sin(a(1 - X))` for every complex `a` with `|Re a| < π`. -/
theorem sin_mul_kernelLaplace {X : ℝ} (h0 : 0 < X) (h1 : X < 1) {a : ℂ} (ha : |a.re| < π) :
    Complex.sin a * kernelLaplace X a = Complex.sin (a * (1 - X)) := by
  set g : ℂ → ℂ := fun a => Complex.sin a * kernelLaplace X a - Complex.sin (a * (1 - X)) with hg
  have hgd : DifferentiableOn ℂ g laplaceStrip :=
    (Complex.differentiable_sin.differentiableOn.mul (differentiableOn_kernelLaplace h0 h1)).sub
      ((Complex.differentiable_sin.comp (differentiable_id.mul_const _)).differentiableOn)
  have hga := hgd.analyticOnNhd isOpen_laplaceStrip
  -- g vanishes on the imaginary axis
  have hzero : ∀ κ : ℝ, κ ≠ 0 → g (I * κ) = 0 := by
    intro κ hκ
    simp only [hg, kernelLaplace]
    rw [fourier_stripKernel h0 h1 hκ, sinhRatio_of_ne hκ, mul_comm I, Complex.sin_mul_I,
      show (κ : ℂ) * I * (1 - X) = ((κ * (1 - X) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.sin_mul_I, ← Complex.ofReal_sinh, ← Complex.ofReal_sinh]
    have hs : Real.sinh κ ≠ 0 := by simpa using hκ
    have hs' : Complex.sinh (κ : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_sinh]; exact_mod_cast hs
    push_cast
    rw [mul_comm (Complex.sinh (κ : ℂ)) I, mul_assoc I, mul_div_cancel₀ _ hs']
    ring
  have hseq : Tendsto (fun n : ℕ => I * (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
      rw [Complex.ofReal_zero] at h
      simpa using h.const_mul I
    · refine Eventually.of_forall fun n => ?_
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, mul_eq_zero, I_ne_zero,
        Complex.ofReal_eq_zero, false_or]
      positivity
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), g z = 0 :=
    hseq.frequently (Frequently.of_forall fun n => hzero _ (by positivity))
  have h0mem : (0 : ℂ) ∈ laplaceStrip := by rw [mem_laplaceStrip]; simp [Real.pi_pos]
  have := hga.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_laplaceStrip h0mem
    hfreq (mem_laplaceStrip.mpr ha)
  simpa [hg, sub_eq_zero] using this

/-- **Lemma 5 (Laplace transform of the strip kernel)**: for `0 < X < 1` and real `a` with
`0 < |a| < π`, `∫ e^{-au} K_X(u) du = sin(a(1 - X)) / sin(a)`. -/
theorem laplace_stripKernel {X : ℝ} (h0 : 0 < X) (h1 : X < 1) {a : ℝ} (ha0 : a ≠ 0)
    (ha : |a| < π) :
    ∫ u : ℝ, Real.exp (-(a * u)) * stripKernel X u = Real.sin (a * (1 - X)) / Real.sin a := by
  have hsin : Real.sin a ≠ 0 := by
    rcases lt_or_gt_of_ne ha0 with h | h
    · have := Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr h) (by rw [abs_of_neg h] at ha; linarith)
      rw [Real.sin_neg] at this; linarith
    · exact (Real.sin_pos_of_pos_of_lt_pi h (by rw [abs_of_pos h] at ha; exact ha)).ne'
  have h := sin_mul_kernelLaplace h0 h1 (a := (a : ℂ)) (by simpa using ha)
  have hL : kernelLaplace X a = ((∫ u : ℝ, Real.exp (-(a * u)) * stripKernel X u : ℝ) : ℂ) := by
    unfold kernelLaplace
    rw [← integral_complex_ofReal]
    congr 1; funext u; push_cast; ring_nf
  rw [hL, ← Complex.ofReal_sin, show (a : ℂ) * (1 - X) = ((a * (1 - X) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_sin, ← Complex.ofReal_mul] at h
  have h' := Complex.ofReal_injective h
  field_simp
  linarith

/-- **Eq. (5.1) of the paper for real `a`**: the Laplace transform of the Poisson measure
`ω_ν(dw) = K_x(y - w) dw` of an interior point `ν = x + iy` is
`∫ e^{aw} K_x(y - w) dw = e^{ay} sin(a(1 - x)) / sin(a)` for `0 < |a| < π`. -/
theorem laplace_stripKernel_sub {X : ℝ} (h0 : 0 < X) (h1 : X < 1) (y : ℝ) {a : ℝ} (ha0 : a ≠ 0)
    (ha : |a| < π) :
    ∫ w : ℝ, Real.exp (a * w) * stripKernel X (y - w)
      = Real.exp (a * y) * (Real.sin (a * (1 - X)) / Real.sin a) := by
  have e : (fun w : ℝ => Real.exp (a * w) * stripKernel X (y - w))
      = fun w => (fun v : ℝ => Real.exp (a * y) * (Real.exp (-(a * v)) * stripKernel X v)) (y - w) := by
    funext w
    simp only
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [e, integral_sub_left_eq_self
    (fun v : ℝ => Real.exp (a * y) * (Real.exp (-(a * v)) * stripKernel X v)) volume y,
    integral_const_mul, laplace_stripKernel h0 h1 ha0 ha]

end OQP27.StripL3a
