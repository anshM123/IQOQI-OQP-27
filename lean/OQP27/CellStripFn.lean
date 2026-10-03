/-
OQP27/CellStripFn.lean  (module L5, layer 5: regularity of the strip function `h_λ`)

L1 defines `h_λ = hStrip λ` on the closed strip as `(y - λ)_+` on `Re w = 0`, `0` on `Re w = 1`, and inside
as the Poisson integral `∫ K_x(y - s) (s - λ)_+ ds`, `K_x(u) = sin(πx)/(2(cosh(πu) - cos(πx)))`.
Proved here (complete proofs), for every `λ`:
* `stripKernel_eq_re`: `K_x(y - s) = Re( i / (e^{iπw + πs} - 1) )`, `w = x + iy` (so the Poisson kernel is
  the real part of a function holomorphic in `w`);
* `hStrip_eq_re`: on the open strip `hStrip λ w = Re H(w)`, `H(w) = ∫ i (s - λ)_+ / (e^{iπw + πs} - 1) ds`,
  and `H` is holomorphic there (differentiation under the integral sign); hence `hStrip λ` is harmonic on
  the open strip (`harmonicOnNhd_hStrip`);
* continuity on the closed strip and the linear growth bound (`continuousOn_hStrip`, `abs_hStrip_le`),
  from the mass `∫ K_x = 1 - x` (module L3a) and the decay of `∫ K_x(u) |u| du` as `x → 0⁺`, `x → 1⁻`;
* `hStrip_regular : Hyp_hStripRegular`, and the final `continuumCell d : Hyp_ContinuumCell d`.
-/
import OQP27.CellFinal
import OQP27.StripPoisson
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false

namespace OQP27.Cell

open Polynomial Matrix Filter Topology Complex MeasureTheory Metric Set Real

/-! ### The Poisson kernel as a real part -/

lemma hStrip_interior (lam : ℝ) {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    OQP27.hStrip lam w = ∫ s, StripL3a.stripKernel w.re (w.im - s) * max (s - lam) 0 := by
  unfold OQP27.hStrip
  rw [if_neg (not_le.2 h0), if_neg (not_le.2 h1)]
  rfl

lemma exp_strip (w : ℂ) (s : ℝ) :
    Complex.exp (I * π * w + π * s) =
      (Real.exp (π * (s - w.im)) : ℂ) * (Real.cos (π * w.re) + Real.sin (π * w.re) * I) := by
  have e : I * π * w + π * s = ((π * (s - w.im) : ℝ) : ℂ) + ((π * w.re : ℝ) : ℂ) * I := by
    conv_lhs => rw [← Complex.re_add_im w]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [e, Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]

lemma normSq_exp_strip_sub_one (w : ℂ) (s : ℝ) :
    Complex.normSq (Complex.exp (I * π * w + π * s) - 1) =
      Real.exp (π * (s - w.im)) ^ 2 - 2 * Real.exp (π * (s - w.im)) * Real.cos (π * w.re) + 1 := by
  rw [exp_strip, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, Complex.one_re,
    Complex.one_im]
  have := Real.sin_sq_add_cos_sq (π * w.re)
  nlinarith [this]

lemma norm_exp_strip (w : ℂ) (s : ℝ) :
    ‖Complex.exp (I * π * w + π * s)‖ = Real.exp (π * (s - w.im)) := by
  rw [Complex.norm_exp]
  congr 1
  simp
  ring

lemma exp_strip_sub_one_ne {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) (s : ℝ) :
    Complex.exp (I * π * w + π * s) - 1 ≠ 0 := by
  intro h
  have h2 := normSq_exp_strip_sub_one w s
  rw [h, Complex.normSq_zero] at h2
  have hsin := StripL3a.sin_pi_mul_pos h0 h1
  have := Real.sin_sq_add_cos_sq (π * w.re)
  nlinarith [sq_nonneg (Real.exp (π * (s - w.im)) - Real.cos (π * w.re))]

/-- `K_x(y - s) = Re(i/(e^{iπw + πs} - 1))`. -/
lemma stripKernel_eq_re {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) (s : ℝ) :
    StripL3a.stripKernel w.re (w.im - s) = (I / (Complex.exp (I * π * w + π * s) - 1)).re := by
  set R := Real.exp (π * (s - w.im)) with hR
  set a := π * w.re with ha
  have hRpos : 0 < R := Real.exp_pos _
  have hsin : 0 < Real.sin a := StripL3a.sin_pi_mul_pos h0 h1
  have hden : 0 < R ^ 2 - 2 * R * Real.cos a + 1 := by
    have := Real.sin_sq_add_cos_sq a
    nlinarith [sq_nonneg (R - Real.cos a)]
  rw [Complex.div_re, normSq_exp_strip_sub_one, exp_strip]
  simp only [Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add, Complex.sub_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im, Complex.add_re,
    Complex.mul_re, Complex.one_im, sub_zero, mul_zero, zero_add, mul_one]
  rw [← hR, ← ha]
  unfold StripL3a.stripKernel
  rw [← ha]
  have hcosh : Real.cosh (π * (w.im - s)) = (R + R⁻¹) / 2 := by
    rw [Real.cosh_eq, hR, ← Real.exp_neg]
    congr 1
    ring_nf
  rw [hcosh]
  have hRne : R ≠ 0 := hRpos.ne'
  have h2 : 2 * ((R + R⁻¹) / 2 - Real.cos a) = (R ^ 2 - 2 * R * Real.cos a + 1) / R := by
    field_simp
    ring
  rw [h2]
  field_simp
  ring

/-- The lower bound `|e^{iπw+πs} - 1|² ≥ (1 - κ)(e^{2π(s - Im w)} + 1)` when `|cos(π Re w)| ≤ κ`. -/
lemma normSq_exp_strip_ge (w : ℂ) (s : ℝ) {κ : ℝ} (hκ : |Real.cos (π * w.re)| ≤ κ) :
    (1 - κ) * (Real.exp (π * (s - w.im)) ^ 2 + 1) ≤
      Complex.normSq (Complex.exp (I * π * w + π * s) - 1) := by
  rw [normSq_exp_strip_sub_one]
  set R := Real.exp (π * (s - w.im))
  have hR : 0 < R := Real.exp_pos _
  have hc : Real.cos (π * w.re) ≤ κ := (le_abs_self _).trans hκ
  have hκ0 : 0 ≤ κ := (abs_nonneg _).trans hκ
  nlinarith [sq_nonneg (R - 1), mul_le_mul_of_nonneg_left hc hR.le]

/-- `|cos(πx)| ≤ cos(πδ)` for `0 ≤ δ ≤ x ≤ 1 - δ`. -/
lemma abs_cos_pi_le {x δ : ℝ} (hδ0 : 0 ≤ δ) (hx0 : δ ≤ x) (hx1 : x ≤ 1 - δ) :
    |Real.cos (π * x)| ≤ Real.cos (π * δ) := by
  have hπ := Real.pi_pos
  rcases le_total x (1 / 2) with hx | hx
  · have hc0 : 0 ≤ Real.cos (π * x) :=
      Real.cos_nonneg_of_mem_Icc ⟨by nlinarith, by nlinarith⟩
    rw [abs_of_nonneg hc0]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by nlinarith) (by nlinarith) (by nlinarith)
  · have hc0 : Real.cos (π * x) ≤ 0 := by
      have : Real.cos (π * x) = -Real.cos (π * (1 - x)) := by
        rw [show π * (1 - x) = π - π * x by ring, Real.cos_pi_sub]
        ring
      rw [this, neg_nonpos]
      exact Real.cos_nonneg_of_mem_Icc ⟨by nlinarith, by nlinarith⟩
    rw [abs_of_nonpos hc0]
    have : -Real.cos (π * x) = Real.cos (π * (1 - x)) := by
      rw [show π * (1 - x) = π - π * x by ring, Real.cos_pi_sub]
    rw [this]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by nlinarith) (by nlinarith) (by nlinarith)

/-! ### The holomorphic integrand -/

/-- `F(w, s) = i (s - λ)_+ / (e^{iπw+πs} - 1)`. -/
noncomputable def hInt (lam : ℝ) (w : ℂ) (s : ℝ) : ℂ :=
  I * ((max (s - lam) 0 : ℝ) : ℂ) / (Complex.exp (I * π * w + π * s) - 1)

/-- `∂_w F(w, s) = π (s - λ)_+ e^{iπw+πs} / (e^{iπw+πs} - 1)²`. -/
noncomputable def hIntDeriv (lam : ℝ) (w : ℂ) (s : ℝ) : ℂ :=
  π * ((max (s - lam) 0 : ℝ) : ℂ) * Complex.exp (I * π * w + π * s) /
    (Complex.exp (I * π * w + π * s) - 1) ^ 2

lemma hasDerivAt_hInt (lam s : ℝ) {w : ℂ} (hne : Complex.exp (I * π * w + π * s) - 1 ≠ 0) :
    HasDerivAt (fun v => hInt lam v s) (hIntDeriv lam w s) w := by
  have hE : HasDerivAt (fun v : ℂ => Complex.exp (I * π * v + π * s) - 1)
      (Complex.exp (I * π * w + π * s) * (I * π)) w := by
    have h1 : HasDerivAt (fun v : ℂ => I * π * v + π * s) (I * π) w := by
      simpa using ((hasDerivAt_id w).const_mul (I * π)).add_const ((π : ℂ) * s)
    exact ((Complex.hasDerivAt_exp _).comp w h1).sub_const 1
  have h := (hasDerivAt_const w (I * ((max (s - lam) 0 : ℝ) : ℂ))).div hE hne
  have hval : (0 * (Complex.exp (I * π * w + π * s) - 1) - I * ((max (s - lam) 0 : ℝ) : ℂ) *
      (Complex.exp (I * π * w + π * s) * (I * π))) / (Complex.exp (I * π * w + π * s) - 1) ^ 2 =
      hIntDeriv lam w s := by
    unfold hIntDeriv
    congr 1
    linear_combination (-((π : ℂ) * ((max (s - lam) 0 : ℝ) : ℂ) *
      Complex.exp (I * π * w + π * s))) * Complex.I_sq
  unfold hInt
  exact h.congr_deriv hval

lemma continuous_hInt (lam : ℝ) {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    Continuous (hInt lam w) := by
  unfold hInt
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro s
  exact exp_strip_sub_one_ne h0 h1 s

lemma continuous_hIntDeriv (lam : ℝ) {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    Continuous (hIntDeriv lam w) := by
  unfold hIntDeriv
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro s
  exact pow_ne_zero 2 (exp_strip_sub_one_ne h0 h1 s)

/-! ### Bounds -/

lemma integrable_abs_add_mul_exp (y₀ K : ℝ) :
    Integrable (fun s : ℝ => (|y₀ - s| + K) * Real.exp (-(π * |y₀ - s|))) := by
  have hb : (0 : ℝ) < π / 2 := by positivity
  have hπ := Real.pi_pos
  have h1 : Integrable (fun u : ℝ => (|u| + K) * Real.exp (-(π * |u|))) := by
    refine ((StripL3a.integrable_exp_neg_mul_abs hb).const_mul (2 / π + |K|)).mono'
      (by fun_prop) (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hE : Real.exp (-(π * |u|)) = Real.exp (-(π / 2 * |u|)) * Real.exp (-(π / 2 * |u|)) := by
      rw [← Real.exp_add]
      ring_nf
    have hx : π / 2 * |u| ≤ Real.exp (π / 2 * |u|) := by
      linarith [Real.add_one_le_exp (π / 2 * |u|)]
    have h3 : |u| * Real.exp (-(π / 2 * |u|)) ≤ 2 / π := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) hπ]
      nlinarith
    have h4 : Real.exp (-(π / 2 * |u|)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [abs_nonneg u]
    have h5 : |(|u| + K)| ≤ |u| + |K| := by
      calc |(|u| + K)| ≤ |(|u|)| + |K| := abs_add_le _ _
        _ = |u| + |K| := by rw [abs_abs]
    have h6 : 0 ≤ Real.exp (-(π / 2 * |u|)) := (Real.exp_pos _).le
    calc |(|u| + K)| * Real.exp (-(π * |u|)) ≤ (|u| + |K|) * Real.exp (-(π * |u|)) :=
          mul_le_mul_of_nonneg_right h5 (Real.exp_pos _).le
      _ = (|u| * Real.exp (-(π / 2 * |u|)) + |K| * Real.exp (-(π / 2 * |u|))) *
            Real.exp (-(π / 2 * |u|)) := by rw [hE]; ring
      _ ≤ (2 / π + |K|) * Real.exp (-(π / 2 * |u|)) := by
          apply mul_le_mul_of_nonneg_right _ h6
          nlinarith [abs_nonneg K]
  exact h1.comp_sub_left y₀

lemma div_sq_add_one_le (t : ℝ) : Real.exp t / (Real.exp t ^ 2 + 1) ≤ Real.exp (-|t|) := by
  have hE := Real.exp_pos t
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht, Real.exp_neg, div_le_iff₀ (by positivity)]
    have : Real.exp t ^ 2 = Real.exp t * Real.exp t := by ring
    rw [this]
    field_simp
    nlinarith
  · rw [abs_of_nonpos ht, neg_neg, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (Real.exp t)]

lemma norm_hIntDeriv_le (lam : ℝ) (w : ℂ) (s : ℝ) {c : ℝ} (hc : 0 < c)
    (hcos : |Real.cos (π * w.re)| ≤ 1 - c) :
    ‖hIntDeriv lam w s‖ ≤ π / c * (max (s - lam) 0 * Real.exp (-(π * |s - w.im|))) := by
  have hπ := Real.pi_pos
  have hns := normSq_exp_strip_ge w s hcos
  set R := Real.exp (π * (s - w.im)) with hR
  have hRpos : 0 < R := Real.exp_pos _
  have hf : 0 ≤ max (s - lam) 0 := le_max_right _ _
  have hns' : 0 < Complex.normSq (Complex.exp (I * π * w + π * s) - 1) := by
    have : 0 < c * (R ^ 2 + 1) := by positivity
    rw [sub_sub_cancel] at hns
    linarith
  unfold hIntDeriv
  rw [norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hπ, abs_of_nonneg hf, norm_exp_strip,
    Complex.sq_norm, ← hR]
  have hRR := div_sq_add_one_le (π * (s - w.im))
  rw [← hR, show |π * (s - w.im)| = π * |s - w.im| by rw [abs_mul, abs_of_pos hπ]] at hRR
  rw [sub_sub_cancel] at hns
  calc π * max (s - lam) 0 * R / Complex.normSq (Complex.exp (I * π * w + π * s) - 1)
      ≤ π * max (s - lam) 0 * R / (c * (R ^ 2 + 1)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity) hns
    _ = π / c * (max (s - lam) 0 * (R / (R ^ 2 + 1))) := by
        field_simp
    _ ≤ π / c * (max (s - lam) 0 * Real.exp (-(π * |s - w.im|))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hRR hf

lemma ramp_div_max_le (s y lam : ℝ) :
    max (s - lam) 0 / max (Real.exp (π * (s - y))) 1 ≤
      Real.exp (π * |y - lam|) * ((|y - s| + |y| + |lam|) * Real.exp (-(π * |y - s|))) := by
  have hπ := Real.pi_pos
  set K := |y - s| + |y| + |lam| with hK
  have hK0 : 0 ≤ K := by positivity
  rcases le_total s lam with hsl | hsl
  · rw [max_eq_right (by linarith), zero_div]
    positivity
  have hfle : max (s - lam) 0 ≤ K := by
    rw [max_eq_left (by linarith)]
    have := abs_sub_abs_le_abs_sub s y
    rw [abs_sub_comm s y] at this
    linarith [le_abs_self s, neg_abs_le lam]
  have hkey : 1 / max (Real.exp (π * (s - y))) 1 ≤
      Real.exp (π * |y - lam|) * Real.exp (-(π * |y - s|)) := by
    rw [← Real.exp_add]
    rcases le_total y s with hys | hys
    · rw [max_eq_left (Real.one_le_exp (by nlinarith)), one_div, ← Real.exp_neg, Real.exp_le_exp,
        abs_of_nonpos (by linarith : y - s ≤ 0)]
      nlinarith [abs_nonneg (y - lam)]
    · rw [max_eq_right (Real.exp_le_one_iff.2 (by nlinarith)), div_one]
      apply Real.one_le_exp
      rw [abs_of_nonneg (by linarith : 0 ≤ y - s)]
      have : y - s ≤ |y - lam| := by
        have := le_abs_self (y - lam)
        linarith
      nlinarith
  calc max (s - lam) 0 / max (Real.exp (π * (s - y))) 1 =
        max (s - lam) 0 * (1 / max (Real.exp (π * (s - y))) 1) := by ring
    _ ≤ K * (Real.exp (π * |y - lam|) * Real.exp (-(π * |y - s|))) :=
        mul_le_mul hfle hkey (by positivity) hK0
    _ = Real.exp (π * |y - lam|) * (K * Real.exp (-(π * |y - s|))) := by ring

lemma norm_hInt_le (lam : ℝ) (w : ℂ) (s : ℝ) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hcos : |Real.cos (π * w.re)| ≤ 1 - c) :
    ‖hInt lam w s‖ ≤ 1 / c * (max (s - lam) 0 / max (Real.exp (π * (s - w.im))) 1) := by
  have hns := normSq_exp_strip_ge w s hcos
  rw [sub_sub_cancel] at hns
  set R := Real.exp (π * (s - w.im)) with hR
  have hRpos : 0 < R := Real.exp_pos _
  have hf : 0 ≤ max (s - lam) 0 := le_max_right _ _
  have hm : 0 < max R 1 := lt_max_of_lt_right one_pos
  have hmsq : max R 1 ^ 2 ≤ R ^ 2 + 1 := by
    rcases le_total R 1 with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith
  have hlow : c * max R 1 ≤ ‖Complex.exp (I * π * w + π * s) - 1‖ := by
    rw [← sq_le_sq₀ (by positivity) (norm_nonneg _), Complex.sq_norm]
    calc (c * max R 1) ^ 2 = c * c * max R 1 ^ 2 := by ring
      _ ≤ c * 1 * max R 1 ^ 2 := by gcongr
      _ ≤ c * (R ^ 2 + 1) := by nlinarith
      _ ≤ _ := hns
  unfold hInt
  rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hf]
  calc max (s - lam) 0 / ‖Complex.exp (I * π * w + π * s) - 1‖ ≤ max (s - lam) 0 / (c * max R 1) :=
        div_le_div_of_nonneg_left hf (by positivity) hlow
    _ = 1 / c * (max (s - lam) 0 / max R 1) := by field_simp

lemma abs_cos_lt_one {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : |Real.cos (π * x)| < 1 := by
  have hs := StripL3a.sin_pi_mul_pos h0 h1
  have := Real.sin_sq_add_cos_sq (π * x)
  rw [abs_lt]
  constructor <;> nlinarith

lemma integrable_hInt (lam : ℝ) {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    Integrable (hInt lam w) := by
  set c := 1 - |Real.cos (π * w.re)| with hc
  have hcpos : 0 < c := by linarith [abs_cos_lt_one h0 h1]
  have hc1 : c ≤ 1 := by linarith [abs_nonneg (Real.cos (π * w.re))]
  have hcos : |Real.cos (π * w.re)| ≤ 1 - c := by rw [hc]; ring_nf; rfl
  refine ((integrable_abs_add_mul_exp w.im (|w.im| + |lam|)).const_mul
    (1 / c * Real.exp (π * |w.im - lam|))).mono' (continuous_hInt lam h0 h1).aestronglyMeasurable
    (Eventually.of_forall fun s => ?_)
  refine (norm_hInt_le lam w s hcpos hc1 hcos).trans ?_
  have := ramp_div_max_le s w.im lam
  have h2 : 0 ≤ 1 / c := by positivity
  calc 1 / c * (max (s - lam) 0 / max (Real.exp (π * (s - w.im))) 1)
      ≤ 1 / c * (Real.exp (π * |w.im - lam|) *
          ((|w.im - s| + |w.im| + |lam|) * Real.exp (-(π * |w.im - s|)))) :=
        mul_le_mul_of_nonneg_left this h2
    _ = 1 / c * Real.exp (π * |w.im - lam|) *
          ((|w.im - s| + (|w.im| + |lam|)) * Real.exp (-(π * |w.im - s|))) := by ring

/-! ### Holomorphy of `H(w) = ∫ F(w, s) ds` and harmonicity of `h_λ` -/

theorem hasDerivAt_hIntegral (lam : ℝ) {w₀ : ℂ} (h0 : 0 < w₀.re) (h1 : w₀.re < 1) :
    HasDerivAt (fun w => ∫ s, hInt lam w s) (∫ s, hIntDeriv lam w₀ s) w₀ := by
  have hπ := Real.pi_pos
  set δ : ℝ := min w₀.re (1 - w₀.re) / 2 with hδ
  have hδ0 : 0 < δ := by
    have : 0 < min w₀.re (1 - w₀.re) := lt_min h0 (by linarith)
    positivity
  have hδa : δ ≤ w₀.re / 2 := by
    have := min_le_left w₀.re (1 - w₀.re)
    rw [hδ]
    linarith
  have hδb : δ ≤ (1 - w₀.re) / 2 := by
    have := min_le_right w₀.re (1 - w₀.re)
    rw [hδ]
    linarith
  set ρ : ℝ := min δ (1 / 2) with hρ
  have hρ0 : 0 < ρ := lt_min hδ0 (by norm_num)
  have hball : ∀ w ∈ ball w₀ ρ, δ ≤ w.re ∧ w.re ≤ 1 - δ ∧ |w.im - w₀.im| ≤ 1 / 2 := by
    intro w hw
    rw [mem_ball, dist_eq_norm] at hw
    have hre : |w.re - w₀.re| < ρ := by
      have := Complex.abs_re_le_norm (w - w₀)
      rw [Complex.sub_re] at this
      linarith
    have him : |w.im - w₀.im| < ρ := by
      have := Complex.abs_im_le_norm (w - w₀)
      rw [Complex.sub_im] at this
      linarith
    have hρδ : ρ ≤ δ := min_le_left _ _
    have hρh : ρ ≤ 1 / 2 := min_le_right _ _
    rw [abs_lt] at hre
    refine ⟨by linarith, by linarith, by linarith⟩
  have hstrip : ∀ w ∈ ball w₀ ρ, 0 < w.re ∧ w.re < 1 := by
    intro w hw
    obtain ⟨ha, hb, -⟩ := hball w hw
    exact ⟨by linarith, by linarith⟩
  set c : ℝ := 1 - Real.cos (π * δ) with hc
  have hcpos : 0 < c := by
    have : Real.cos (π * δ) < 1 := by
      have h2 : δ < 1 := by linarith
      have := StripL3a.cos_pi_mul_lt_one hδ0 h2
      exact this
    linarith
  have hcos : ∀ w ∈ ball w₀ ρ, |Real.cos (π * w.re)| ≤ 1 - c := by
    intro w hw
    rw [hc, sub_sub_cancel]
    exact abs_cos_pi_le hδ0.le (hball w hw).1 (hball w hw).2.1
  set y₀ := w₀.im with hy₀
  set bound : ℝ → ℝ := fun s => π / c * Real.exp (π / 2) *
    ((|y₀ - s| + (|y₀| + |lam|)) * Real.exp (-(π * |y₀ - s|))) with hbound
  have hbint : Integrable bound := (integrable_abs_add_mul_exp y₀ (|y₀| + |lam|)).const_mul _
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds w₀ hρ0) ?_
    (integrable_hInt lam h0 h1) (continuous_hIntDeriv lam h0 h1).aestronglyMeasurable ?_ hbint ?_).2
  · filter_upwards [ball_mem_nhds w₀ hρ0] with w hw
    exact (continuous_hInt lam (hstrip w hw).1 (hstrip w hw).2).aestronglyMeasurable
  · refine Eventually.of_forall fun s w hw => ?_
    refine (norm_hIntDeriv_le lam w s hcpos (hcos w hw)).trans ?_
    have him := (hball w hw).2.2
    have hf : max (s - lam) 0 ≤ |y₀ - s| + (|y₀| + |lam|) := by
      apply max_le _ (by positivity)
      have := abs_sub_abs_le_abs_sub s y₀
      rw [abs_sub_comm s y₀] at this
      linarith [le_abs_self s, neg_abs_le lam]
    have hexp : Real.exp (-(π * |s - w.im|)) ≤ Real.exp (π / 2) * Real.exp (-(π * |y₀ - s|)) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      have : |y₀ - s| ≤ |s - w.im| + 1 / 2 := by
        have := abs_sub_le y₀ w.im s
        rw [abs_sub_comm y₀ w.im, abs_sub_comm w.im s] at this
        linarith
      nlinarith
    simp only [hbound]
    have hcπ : 0 ≤ π / c := by positivity
    calc π / c * (max (s - lam) 0 * Real.exp (-(π * |s - w.im|)))
        ≤ π / c * ((|y₀ - s| + (|y₀| + |lam|)) *
            (Real.exp (π / 2) * Real.exp (-(π * |y₀ - s|)))) := by
          apply mul_le_mul_of_nonneg_left _ hcπ
          exact mul_le_mul hf hexp (Real.exp_pos _).le (by positivity)
      _ = π / c * Real.exp (π / 2) *
            ((|y₀ - s| + (|y₀| + |lam|)) * Real.exp (-(π * |y₀ - s|))) := by ring
  · exact Eventually.of_forall fun s w hw => hasDerivAt_hInt lam s
      (exp_strip_sub_one_ne (hstrip w hw).1 (hstrip w hw).2 s)

/-- The holomorphic function `H(w) = ∫ i (s - λ)_+ / (e^{iπw+πs} - 1) ds` on the open strip. -/
noncomputable def hHol (lam : ℝ) (w : ℂ) : ℂ := ∫ s, hInt lam w s

lemma differentiableOn_hHol (lam : ℝ) : DifferentiableOn ℂ (hHol lam) strip := by
  intro w hw
  exact (hasDerivAt_hIntegral lam hw.1 hw.2).differentiableAt.differentiableWithinAt

/-- On the open strip, `h_λ = Re H`. -/
theorem hStrip_eq_re (lam : ℝ) {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    OQP27.hStrip lam w = (hHol lam w).re := by
  rw [hStrip_interior lam h0 h1, hHol]
  have hre : (∫ s, hInt lam w s).re = ∫ s, (hInt lam w s).re :=
    (Complex.reCLM.integral_comp_comm (integrable_hInt lam h0 h1)).symm
  rw [hre]
  apply integral_congr_ae
  refine Eventually.of_forall fun s => ?_
  simp only
  unfold hInt
  rw [mul_comm I, mul_div_assoc, Complex.re_ofReal_mul, ← stripKernel_eq_re h0 h1]
  ring

/-- **`h_λ` is harmonic on the open strip.** -/
theorem harmonicOnNhd_hStrip (lam : ℝ) : InnerProductSpace.HarmonicOnNhd (OQP27.hStrip lam) strip := by
  intro w hw
  have han : AnalyticAt ℂ (hHol lam) w :=
    (differentiableOn_hHol lam).analyticAt (isOpen_strip.mem_nhds hw)
  apply (InnerProductSpace.harmonicAt_congr_nhds _).2 han.harmonicAt_re
  filter_upwards [isOpen_strip.mem_nhds hw] with v hv
  exact hStrip_eq_re lam hv.1 hv.2

/-! ### The absolute first moment of the kernel -/

/-- `m(x) = ∫ K_x(u) |u| du`. -/
noncomputable def kMom (x : ℝ) : ℝ := ∫ u, StripL3a.stripKernel x u * |u|

lemma integrable_kernel_abs {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    Integrable (fun u => StripL3a.stripKernel x u * |u|) := by
  have := (StripL3a.integrable_mul_stripKernel h0 h1).abs
  refine this.congr (Eventually.of_forall fun u => ?_)
  simp only
  rw [abs_mul, abs_of_pos (StripL3a.stripKernel_pos h0 h1 u), mul_comm]

lemma kMom_nonneg {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : 0 ≤ kMom x :=
  integral_nonneg fun u => mul_nonneg (StripL3a.stripKernel_pos h0 h1 u).le (abs_nonneg u)

lemma stripKernel_half (u : ℝ) : StripL3a.stripKernel (1 / 2) u = 1 / (2 * Real.cosh (π * u)) := by
  unfold StripL3a.stripKernel
  rw [show π * (1 / 2) = π / 2 by ring, Real.sin_pi_div_two, Real.cos_pi_div_two, sub_zero]

/-- `K_x(u) ≤ sin(πx) K_{1/2}(u)` for `1/2 ≤ x < 1`. -/
lemma stripKernel_le_right {x : ℝ} (hx : 1 / 2 ≤ x) (h1 : x < 1) (u : ℝ) :
    StripL3a.stripKernel x u ≤ Real.sin (π * x) * StripL3a.stripKernel (1 / 2) u := by
  have h0 : 0 < x := by linarith
  have hs := StripL3a.sin_pi_mul_pos h0 h1
  have hc : Real.cos (π * x) ≤ 0 := by
    apply Real.cos_nonpos_of_pi_div_two_le_of_le <;> nlinarith [Real.pi_pos]
  have hch := Real.cosh_pos (π * u)
  rw [stripKernel_half]
  unfold StripL3a.stripKernel
  rw [div_le_iff₀ (by linarith), mul_one_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith

/-- `K_x(u) ≤ (sin(πx)/c_η) K_{1/2}(u)` for `|u| ≥ η`, `0 < x ≤ 1/2`, `c_η = 1 - 1/cosh(πη)`. -/
lemma stripKernel_le_left {x η u : ℝ} (h0 : 0 < x) (hx : x ≤ 1 / 2) (hη : 0 < η) (hu : η ≤ |u|) :
    StripL3a.stripKernel x u ≤
      Real.sin (π * x) / (1 - 1 / Real.cosh (π * η)) * StripL3a.stripKernel (1 / 2) u := by
  have h1 : x < 1 := by linarith
  have hs := StripL3a.sin_pi_mul_pos h0 h1
  have hcos : Real.cos (π * x) ≤ 1 := Real.cos_le_one _
  have hchη : 1 < Real.cosh (π * η) := Real.one_lt_cosh.2 (by positivity)
  have hchu : Real.cosh (π * η) ≤ Real.cosh (π * u) := by
    rw [Real.cosh_le_cosh, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hη]
    exact mul_le_mul_of_nonneg_left hu Real.pi_pos.le
  have hcη : 0 < 1 - 1 / Real.cosh (π * η) := by
    rw [sub_pos, div_lt_one (by linarith)]
    exact hchη
  have hden : (1 - 1 / Real.cosh (π * η)) * Real.cosh (π * u) ≤
      Real.cosh (π * u) - Real.cos (π * x) := by
    have : Real.cosh (π * u) / Real.cosh (π * η) ≥ 1 := by
      rw [ge_iff_le, le_div_iff₀ (by linarith)]
      linarith
    have e : (1 - 1 / Real.cosh (π * η)) * Real.cosh (π * u) =
        Real.cosh (π * u) - Real.cosh (π * u) / Real.cosh (π * η) := by
      field_simp
    rw [e]
    linarith
  have hch := Real.cosh_pos (π * u)
  rw [stripKernel_half]
  unfold StripL3a.stripKernel
  have hd1 : 0 < Real.cosh (π * u) - Real.cos (π * x) := by nlinarith
  rw [div_mul_eq_mul_div, mul_one_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hden hs.le]

lemma kMom_le_right {x : ℝ} (hx : 1 / 2 ≤ x) (h1 : x < 1) :
    kMom x ≤ Real.sin (π * x) * kMom (1 / 2) := by
  have h0 : 0 < x := by linarith
  unfold kMom
  rw [← integral_const_mul]
  apply integral_mono (integrable_kernel_abs h0 h1)
    ((integrable_kernel_abs (by norm_num) (by norm_num)).const_mul _)
  intro u
  simp only
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (stripKernel_le_right hx h1 u) (abs_nonneg u)

lemma kMom_le_left {x η : ℝ} (h0 : 0 < x) (hx : x ≤ 1 / 2) (hη : 0 < η) :
    kMom x ≤ η + Real.sin (π * x) / (1 - 1 / Real.cosh (π * η)) * kMom (1 / 2) := by
  have h1 : x < 1 := by linarith
  have hs := StripL3a.sin_pi_mul_pos h0 h1
  have hchη : 1 < Real.cosh (π * η) := Real.one_lt_cosh.2 (by positivity)
  have hcη : 0 < 1 - 1 / Real.cosh (π * η) := by
    rw [sub_pos, div_lt_one (by linarith)]
    exact hchη
  set A := Real.sin (π * x) / (1 - 1 / Real.cosh (π * η)) with hA
  have hA0 : 0 ≤ A := by positivity
  have hpt : ∀ u, StripL3a.stripKernel x u * |u| ≤
      η * StripL3a.stripKernel x u + A * (StripL3a.stripKernel (1 / 2) u * |u|) := by
    intro u
    have hK := (StripL3a.stripKernel_pos h0 h1 u).le
    have hK2 := (StripL3a.stripKernel_pos (X := 1 / 2) (by norm_num) (by norm_num) u).le
    rcases le_total |u| η with hu | hu
    · have : StripL3a.stripKernel x u * |u| ≤ η * StripL3a.stripKernel x u := by nlinarith
      nlinarith [mul_nonneg hA0 (mul_nonneg hK2 (abs_nonneg u))]
    · have := stripKernel_le_left h0 hx hη hu
      have h3 : StripL3a.stripKernel x u * |u| ≤ A * StripL3a.stripKernel (1 / 2) u * |u| :=
        mul_le_mul_of_nonneg_right this (abs_nonneg u)
      nlinarith [mul_nonneg hη.le hK]
  have hint1 := StripL3a.integrable_stripKernel h0 h1
  have hint2 := (integrable_kernel_abs (x := 1 / 2) (by norm_num) (by norm_num)).const_mul A
  calc kMom x ≤ ∫ u, (η * StripL3a.stripKernel x u + A * (StripL3a.stripKernel (1 / 2) u * |u|)) :=
        integral_mono (integrable_kernel_abs h0 h1) ((hint1.const_mul η).add hint2) hpt
    _ = η * (1 - x) + A * kMom (1 / 2) := by
        rw [integral_add (hint1.const_mul η) hint2, integral_const_mul, integral_const_mul,
          StripL3a.integral_stripKernel h0 h1]
        rfl
    _ ≤ η + A * kMom (1 / 2) := by nlinarith

/-! ### The Poisson integral against the ramp -/

lemma integrable_kernel_ramp (lam : ℝ) {x : ℝ} (h0 : 0 < x) (h1 : x < 1) (y : ℝ) :
    Integrable (fun s => StripL3a.stripKernel x (y - s) * max (s - lam) 0) := by
  have hb : Integrable (fun s => |s * StripL3a.stripKernel x (y - s)| +
      |lam| * StripL3a.stripKernel x (y - s)) :=
    (StripL3a.integrable_mul_stripKernel_sub h0 h1 y).abs.add
      ((StripL3a.integrable_stripKernel_sub h0 h1 y).const_mul _)
  refine hb.mono' (((StripL3a.continuous_stripKernel_sub h0 h1 y).mul
    (by fun_prop)).aestronglyMeasurable) (Eventually.of_forall fun s => ?_)
  have hK := (StripL3a.stripKernel_pos h0 h1 (y - s)).le
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK, abs_of_nonneg (le_max_right _ _), abs_mul,
    abs_of_nonneg hK]
  have : max (s - lam) 0 ≤ |s| + |lam| := max_le (by linarith [le_abs_self s, neg_abs_le lam])
    (by positivity)
  nlinarith

/-- `|h_λ(x + iy) - (1 - x)(y - λ)_+| ≤ m(x)` inside the strip. -/
lemma hStrip_sub_le (lam : ℝ) {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    |OQP27.hStrip lam w - (1 - w.re) * max (w.im - lam) 0| ≤ kMom w.re := by
  rw [hStrip_interior lam h0 h1]
  set x := w.re
  set y := w.im
  have hmass := StripL3a.integral_stripKernel_sub h0 h1 y
  have hint := integrable_kernel_ramp lam h0 h1 y
  have hint0 := StripL3a.integrable_stripKernel_sub h0 h1 y
  have e : ∫ s, StripL3a.stripKernel x (y - s) * (max (s - lam) 0 - max (y - lam) 0) =
      (∫ s, StripL3a.stripKernel x (y - s) * max (s - lam) 0) - (1 - x) * max (y - lam) 0 := by
    have h2 : (fun s => StripL3a.stripKernel x (y - s) * (max (s - lam) 0 - max (y - lam) 0)) =
        fun s => StripL3a.stripKernel x (y - s) * max (s - lam) 0 -
          StripL3a.stripKernel x (y - s) * max (y - lam) 0 := by
      funext s
      ring
    rw [h2, integral_sub hint (hint0.mul_const _), integral_mul_const, hmass]
  rw [← e]
  have hmom : ∫ s, StripL3a.stripKernel x (y - s) * |y - s| = kMom x := by
    unfold kMom
    exact integral_sub_left_eq_self (fun u => StripL3a.stripKernel x u * |u|) volume y
  rw [← hmom]
  refine (abs_integral_le_integral_abs).trans (integral_mono ?_ ?_ fun s => ?_)
  · have hI : Integrable (fun s => StripL3a.stripKernel x (y - s) *
        (max (s - lam) 0 - max (y - lam) 0)) := by
      have := hint.sub (hint0.mul_const (max (y - lam) 0))
      refine this.congr (Eventually.of_forall fun s => ?_)
      simp only [Pi.sub_apply]
      ring
    exact hI.abs
  · exact (integrable_kernel_abs h0 h1).comp_sub_left y
  · simp only
    have hK := (StripL3a.stripKernel_pos h0 h1 (y - s)).le
    rw [abs_mul, abs_of_nonneg hK]
    apply mul_le_mul_of_nonneg_left _ hK
    calc |max (s - lam) 0 - max (y - lam) 0| ≤ |(s - lam) - (y - lam)| := abs_max_sub_max_le_abs _ _ _
      _ = |y - s| := by rw [abs_sub_comm]; ring_nf

lemma abs_hStrip_interior_le (lam : ℝ) {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    |OQP27.hStrip lam w| ≤ kMom w.re + (1 - w.re) * (|w.im| + |lam|) := by
  have h := hStrip_sub_le lam h0 h1
  have hf : |(1 - w.re) * max (w.im - lam) 0| ≤ (1 - w.re) * (|w.im| + |lam|) := by
    rw [abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg (le_max_right _ _)]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    exact max_le (by linarith [le_abs_self w.im, neg_abs_le lam]) (by positivity)
  have := abs_sub_abs_le_abs_sub (OQP27.hStrip lam w) ((1 - w.re) * max (w.im - lam) 0)
  linarith

/-! ### Continuity on the closed strip -/

lemma kMom_small {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ x, 0 < x → x < δ → kMom x < ε := by
  have hπ := Real.pi_pos
  set η := ε / 2 with hη
  have hη0 : 0 < η := by positivity
  set cη := 1 - 1 / Real.cosh (π * η) with hcη
  have hchη : 1 < Real.cosh (π * η) := Real.one_lt_cosh.2 (by positivity)
  have hcη0 : 0 < cη := by
    rw [hcη, sub_pos, div_lt_one (by linarith)]
    exact hchη
  have hm0 : 0 ≤ kMom (1 / 2) := kMom_nonneg (by norm_num) (by norm_num)
  refine ⟨min (1 / 2) (ε * cη / (2 * π * (kMom (1 / 2) + 1))), by positivity, fun x hx0 hx => ?_⟩
  have hx1 : x ≤ 1 / 2 := (lt_of_lt_of_le hx (min_le_left _ _)).le
  have hx2 : x < ε * cη / (2 * π * (kMom (1 / 2) + 1)) := lt_of_lt_of_le hx (min_le_right _ _)
  have h1 := kMom_le_left hx0 hx1 hη0
  have hsin : Real.sin (π * x) ≤ π * x := Real.sin_le (by positivity)
  have h2 : Real.sin (π * x) / cη * kMom (1 / 2) ≤ π * x / cη * (kMom (1 / 2) + 1) := by
    apply mul_le_mul (div_le_div_of_nonneg_right hsin hcη0.le) (by linarith) hm0 (by positivity)
  have h3 : π * x / cη * (kMom (1 / 2) + 1) < ε / 2 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hcη0]
    rw [lt_div_iff₀ (by positivity)] at hx2
    nlinarith
  rw [← hcη] at h1
  linarith

theorem continuousWithinAt_hStrip_left (lam : ℝ) {w₀ : ℂ} (hw₀ : w₀.re = 0) :
    ContinuousWithinAt (OQP27.hStrip lam) cstrip w₀ := by
  set F : ℂ → ℝ := fun w => (1 - w.re) * max (w.im - lam) 0 with hF
  have hFc : Continuous F := by
    simp only [hF]
    fun_prop
  have hval : OQP27.hStrip lam w₀ = F w₀ := by
    unfold OQP27.hStrip
    rw [if_pos (le_of_eq hw₀)]
    simp [hF, hw₀]
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁, hF1⟩ := Metric.continuousAt_iff.1 hFc.continuousAt (ε / 2) (by positivity)
  obtain ⟨δ₂, hδ₂, hm⟩ := kMom_small (ε := ε / 2) (by positivity)
  refine ⟨min (min δ₁ δ₂) (1 / 2), by positivity, fun {w} hw hdist => ?_⟩
  have hd1 : dist w w₀ < δ₁ := lt_of_lt_of_le hdist ((min_le_left _ _).trans (min_le_left _ _))
  have hd2 : dist w w₀ < δ₂ := lt_of_lt_of_le hdist ((min_le_left _ _).trans (min_le_right _ _))
  have hd3 : dist w w₀ < 1 / 2 := lt_of_lt_of_le hdist (min_le_right _ _)
  have hFw := hF1 hd1
  rw [hval]
  rcases le_or_gt w.re 0 with h0 | h0
  · have hwF : OQP27.hStrip lam w = F w := by
      unfold OQP27.hStrip
      rw [if_pos h0]
      have : w.re = 0 := le_antisymm h0 hw.1
      simp [hF, this]
    rw [hwF]
    linarith
  · have hre : w.re ≤ dist w w₀ := by
      have := Complex.abs_re_le_norm (w - w₀)
      rw [Complex.sub_re, hw₀, sub_zero, ← dist_eq_norm] at this
      exact (le_abs_self _).trans this
    have h1 : w.re < 1 := by linarith
    have hb := hStrip_sub_le lam h0 h1
    have hk := hm w.re h0 (by linarith)
    rw [Real.dist_eq] at hFw ⊢
    have : |OQP27.hStrip lam w - F w| < ε / 2 := lt_of_le_of_lt hb hk
    calc |OQP27.hStrip lam w - F w₀| ≤ |OQP27.hStrip lam w - F w| + |F w - F w₀| := abs_sub_le _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add this hFw
      _ = ε := by ring

theorem continuousWithinAt_hStrip_right (lam : ℝ) {w₀ : ℂ} (hw₀ : w₀.re = 1) :
    ContinuousWithinAt (OQP27.hStrip lam) cstrip w₀ := by
  have hπ := Real.pi_pos
  have hval : OQP27.hStrip lam w₀ = 0 := by
    unfold OQP27.hStrip
    rw [if_neg (by rw [hw₀]; norm_num), if_pos (le_of_eq hw₀.symm)]
  have hm0 : 0 ≤ kMom (1 / 2) := kMom_nonneg (by norm_num) (by norm_num)
  set K := π * kMom (1 / 2) + |w₀.im| + 1 + |lam| with hK
  have hK0 : 0 ≤ K := by positivity
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  refine ⟨min (1 / 2) (ε / (K + 1)), by positivity, fun {w} hw hdist => ?_⟩
  have hd1 : dist w w₀ < 1 / 2 := lt_of_lt_of_le hdist (min_le_left _ _)
  have hd2 : dist w w₀ < ε / (K + 1) := lt_of_lt_of_le hdist (min_le_right _ _)
  have hre : 1 - w.re ≤ dist w w₀ := by
    have := Complex.abs_re_le_norm (w - w₀)
    rw [Complex.sub_re, hw₀, ← dist_eq_norm, abs_sub_comm] at this
    exact (le_abs_self _).trans this
  have him : |w.im| ≤ |w₀.im| + 1 := by
    have := Complex.abs_im_le_norm (w - w₀)
    rw [Complex.sub_im, ← dist_eq_norm] at this
    have h2 := abs_sub_abs_le_abs_sub w.im w₀.im
    linarith
  rw [hval, Real.dist_eq, sub_zero]
  rcases le_or_gt 1 w.re with h1 | h1
  · have : OQP27.hStrip lam w = 0 := by
      unfold OQP27.hStrip
      rw [if_neg (by linarith), if_pos h1]
    rw [this, abs_zero]
    exact hε
  · have h0 : 0 < w.re := by linarith
    have hhalf : 1 / 2 ≤ w.re := by linarith
    have hb := abs_hStrip_interior_le lam h0 h1
    have hk := kMom_le_right hhalf h1
    have hsin : Real.sin (π * w.re) ≤ π * (1 - w.re) := by
      rw [show π * w.re = π - π * (1 - w.re) by ring, Real.sin_pi_sub]
      exact Real.sin_le (by nlinarith)
    have h3 : |OQP27.hStrip lam w| ≤ (1 - w.re) * K := by
      have h4 : kMom w.re ≤ π * (1 - w.re) * kMom (1 / 2) :=
        hk.trans (mul_le_mul_of_nonneg_right hsin hm0)
      have h5 : (1 - w.re) * (|w.im| + |lam|) ≤ (1 - w.re) * (|w₀.im| + 1 + |lam|) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      calc |OQP27.hStrip lam w| ≤ kMom w.re + (1 - w.re) * (|w.im| + |lam|) := hb
        _ ≤ π * (1 - w.re) * kMom (1 / 2) + (1 - w.re) * (|w₀.im| + 1 + |lam|) := by linarith
        _ = (1 - w.re) * K := by rw [hK]; ring
    have h6 : (1 - w.re) * K < ε := by
      have h7 : 1 - w.re < ε / (K + 1) := lt_of_le_of_lt hre hd2
      have h8 : (1 - w.re) * K ≤ (1 - w.re) * (K + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      rw [lt_div_iff₀ (by positivity)] at h7
      linarith
    linarith

/-- **Continuity of `h_λ` on the closed strip.** -/
theorem continuousOn_hStrip (lam : ℝ) : ContinuousOn (OQP27.hStrip lam) cstrip := by
  intro w hw
  rcases eq_or_lt_of_le hw.1 with h0 | h0
  · exact continuousWithinAt_hStrip_left lam h0.symm
  rcases eq_or_lt_of_le hw.2 with h1 | h1
  · exact continuousWithinAt_hStrip_right lam h1
  have hws : w ∈ strip := ⟨h0, h1⟩
  have hc : ContinuousAt (fun v => (hHol lam v).re) w :=
    Complex.continuous_re.continuousAt.comp
      ((differentiableOn_hHol lam).continuousOn.continuousAt (isOpen_strip.mem_nhds hws))
  apply ContinuousAt.continuousWithinAt
  apply hc.congr
  filter_upwards [isOpen_strip.mem_nhds hws] with v hv
  exact (hStrip_eq_re lam hv.1 hv.2).symm

/-- **Linear growth of `h_λ` on the closed strip.** -/
theorem abs_hStrip_le (lam : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ cstrip, |OQP27.hStrip lam w| ≤ C * (1 + ‖w‖) := by
  have hπ := Real.pi_pos
  have hch : 1 < Real.cosh (π * 1) := Real.one_lt_cosh.2 (by positivity)
  set c1 := 1 - 1 / Real.cosh (π * 1) with hc1
  have hc10 : 0 < c1 := by
    rw [hc1, sub_pos, div_lt_one (by linarith)]
    exact hch
  have hc11 : c1 ≤ 1 := by
    rw [hc1]
    have : 0 < 1 / Real.cosh (π * 1) := by positivity
    linarith
  have hm0 : 0 ≤ kMom (1 / 2) := kMom_nonneg (by norm_num) (by norm_num)
  set M0 := 1 + kMom (1 / 2) / c1 with hM0
  have hM0 : 0 ≤ M0 := by positivity
  have hmom : ∀ x, 0 < x → x < 1 → kMom x ≤ M0 := by
    intro x h0 h1
    rcases le_total x (1 / 2) with hx | hx
    · have := kMom_le_left h0 hx one_pos
      have hs : Real.sin (π * x) ≤ 1 := Real.sin_le_one _
      have hs0 : 0 ≤ Real.sin (π * x) := (StripL3a.sin_pi_mul_pos h0 h1).le
      have : Real.sin (π * x) / c1 * kMom (1 / 2) ≤ kMom (1 / 2) / c1 := by
        rw [div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_right (by nlinarith) hc10.le
      rw [← hc1] at *
      linarith
    · have := kMom_le_right hx h1
      have hs : Real.sin (π * x) ≤ 1 := Real.sin_le_one _
      have : kMom (1 / 2) ≤ kMom (1 / 2) / c1 := by
        rw [le_div_iff₀ hc10]
        nlinarith
      nlinarith
  refine ⟨M0 + |lam| + 1, by positivity, fun w hw => ?_⟩
  have hy : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
  have hn : 0 ≤ ‖w‖ := norm_nonneg w
  by_cases h0 : w.re ≤ 0
  · have : OQP27.hStrip lam w = max (w.im - lam) 0 := by
      unfold OQP27.hStrip
      rw [if_pos h0]
    rw [this, abs_of_nonneg (le_max_right _ _)]
    apply max_le _ (by positivity)
    nlinarith [le_abs_self w.im, neg_abs_le lam, abs_nonneg lam]
  by_cases h1 : 1 ≤ w.re
  · have : OQP27.hStrip lam w = 0 := by
      unfold OQP27.hStrip
      rw [if_neg h0, if_pos h1]
    rw [this, abs_zero]
    positivity
  push Not at h0 h1
  have hb := abs_hStrip_interior_le lam h0 h1
  have hk := hmom w.re h0 h1
  have h2 : (1 - w.re) * (|w.im| + |lam|) ≤ |w.im| + |lam| := by
    have : 0 ≤ |w.im| + |lam| := by positivity
    nlinarith
  nlinarith [abs_nonneg lam]

/-! ### The final theorem -/

/-- The regularity of `h_{λ*}` holds. -/
theorem hStrip_regular : Hyp_hStripRegular :=
  ⟨harmonicOnNhd_hStrip lamStar, continuousOn_hStrip lamStar, abs_hStrip_le lamStar⟩

/-- **The analytic link `(*) ⇒ QD2-L1`** (module L5): L1's `Hyp_ContinuumCell d`,
`Hyp_StripInequality → Hyp_CellInequalities d`, holds for every `d ≥ 1`. -/
theorem continuumCell (d : ℕ) [NeZero d] : OQP27.Hyp_ContinuumCell d :=
  continuumCell_of_regular d hStrip_regular

end OQP27.Cell
