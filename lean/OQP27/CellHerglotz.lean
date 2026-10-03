/-
OQP27/CellHerglotz.lean  (module L5, layer 1: Herglotz functions of arcs)

For real `a < b` the Herglotz transform of the indicator of the arc `(a, b)` of the unit circle is
    `arcH a b z = (b - a)/(2π) + (i/π) (Log(1 - z e^{-ia}) - Log(1 - z e^{-ib}))`
(Q_rig/RIGIDITY_ALLD.md s.3.2: `(1/2π) ∫_a^b (e^{iφ}+z)/(e^{iφ}-z) dφ`).  Proved here (complete proofs):
* `differentiableOn_arcH`  holomorphic on the open unit disc;
* `arcH_zero`              `arcH a b 0 = (b - a)/(2π)`;
* `sum_arcH`               for a partition `0 = t₀ < ... < tₙ = 2π` the arcs' functions sum to `1`;
* `re_arcH_pos`            `0 < Re (arcH a b z)` for `|z| < 1` (positivity of the Poisson kernel;
                           proof by the fundamental theorem of calculus);
* `re_arcH_boundary`, `im_arcH_boundary`   boundary values at `e^{iθ}` (`θ` not an endpoint):
      `Re = 1` on the arc, `0` off the arc, and `Im = (ℓ(θ - a) - ℓ(θ - b))/π`,
      `ℓ(u) = log |2 sin(u/2)|` (so the boundary value of the step field is `B + i g`, with `g`
      the conjugate function of RIGIDITY_ALLD.md (3.1));
* `continuousAt_arcH_boundary`   continuity at boundary points other than the endpoints;
* `norm_arcH_le`           the domination bound (3.2) of RIGIDITY_ALLD.md for `1/2 ≤ r < 1`.
No hypotheses remain.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Integrals.LogTrigonometric
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

namespace OQP27.Cell

open Complex Real Set Metric Filter Topology

/-- The Herglotz transform of the indicator of the arc `(a, b)` of the unit circle. -/
noncomputable def arcH (a b : ℝ) (z : ℂ) : ℂ :=
  (((b - a) / (2 * π) : ℝ) : ℂ) +
    (I / π) * (Complex.log (1 - z * Complex.exp (-((a : ℂ) * I))) -
      Complex.log (1 - z * Complex.exp (-((b : ℂ) * I))))

/-- `ℓ(u) = log |2 sin (u/2)|` (Lean's `Real.log` is `log |·|`). -/
noncomputable def ell (u : ℝ) : ℝ := Real.log (2 * Real.sin (u / 2))

lemma exp_neg_mul_I (a : ℝ) : Complex.exp (-((a : ℂ) * I)) = Complex.exp (((-a : ℝ) : ℂ) * I) := by
  push_cast; ring_nf

lemma norm_exp_neg_mul_I (a : ℝ) : ‖Complex.exp (-((a : ℂ) * I))‖ = 1 := by
  rw [exp_neg_mul_I, Complex.norm_exp_ofReal_mul_I]

lemma one_sub_mem_slitPlane {z : ℂ} (hz : ‖z‖ < 1) (a : ℝ) :
    1 - z * Complex.exp (-((a : ℂ) * I)) ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have h1 : (z * Complex.exp (-((a : ℂ) * I))).re ≤ ‖z * Complex.exp (-((a : ℂ) * I))‖ :=
    Complex.re_le_norm _
  rw [norm_mul, norm_exp_neg_mul_I, mul_one] at h1
  simp only [sub_re, one_re]
  linarith

lemma differentiableAt_arcH (a b : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ (arcH a b) z := by
  unfold arcH
  apply DifferentiableAt.add (differentiableAt_const _)
  apply DifferentiableAt.mul (differentiableAt_const _)
  apply DifferentiableAt.sub
  · exact ((differentiableAt_const _).sub (differentiableAt_id.mul (differentiableAt_const _))).clog
      (one_sub_mem_slitPlane hz a)
  · exact ((differentiableAt_const _).sub (differentiableAt_id.mul (differentiableAt_const _))).clog
      (one_sub_mem_slitPlane hz b)

lemma differentiableOn_arcH (a b : ℝ) : DifferentiableOn ℂ (arcH a b) (ball 0 1) := by
  intro z hz
  rw [mem_ball, dist_zero_right] at hz
  exact (differentiableAt_arcH a b hz).differentiableWithinAt

lemma arcH_zero (a b : ℝ) : arcH a b 0 = (((b - a) / (2 * π) : ℝ) : ℂ) := by
  simp [arcH]

/-- The Herglotz functions of a partition of the circle into arcs sum to `1`. -/
lemma sum_arcH {n : ℕ} (t : ℕ → ℝ) (h0 : t 0 = 0) (hn : t n = 2 * π) (z : ℂ) :
    ∑ k ∈ Finset.range n, arcH (t k) (t (k + 1)) z = 1 := by
  unfold arcH
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 : ∑ k ∈ Finset.range n, ((((t (k + 1) - t k) / (2 * π) : ℝ)) : ℂ) = 1 := by
    rw [← Complex.ofReal_sum, ← Finset.sum_div, Finset.sum_range_sub (fun k => t k) n, hn, h0]
    rw [sub_zero, div_self (by positivity)]
    simp
  have h2 : ∑ k ∈ Finset.range n, (Complex.log (1 - z * Complex.exp (-((t k : ℂ) * I))) -
      Complex.log (1 - z * Complex.exp (-((t (k + 1) : ℂ) * I)))) = 0 := by
    rw [Finset.sum_range_sub' (fun k => Complex.log (1 - z * Complex.exp (-((t k : ℂ) * I)))) n]
    simp only [hn, h0]
    have : Complex.exp (-(((2 * π : ℝ) : ℂ) * I)) = 1 := by
      rw [exp_neg_mul_I]
      push_cast
      rw [show (-(2 * (π : ℂ))) * I = -(2 * π * I) by ring, Complex.exp_neg,
        Complex.exp_two_pi_mul_I, inv_one]
    rw [this]
    simp
  rw [h1, h2, mul_zero, add_zero]

/-! ### Real and imaginary parts -/

lemma re_arcH_eq (a b : ℝ) (z : ℂ) : (arcH a b z).re = (b - a) / (2 * π) -
    (Complex.log (1 - z * Complex.exp (-((a : ℂ) * I))) -
      Complex.log (1 - z * Complex.exp (-((b : ℂ) * I)))).im / π := by
  unfold arcH
  rw [add_re, ofReal_re, mul_re, div_ofReal_re, div_ofReal_im, I_re, I_im]
  ring

lemma im_arcH_eq (a b : ℝ) (z : ℂ) : (arcH a b z).im =
    (Complex.log (1 - z * Complex.exp (-((a : ℂ) * I))) -
      Complex.log (1 - z * Complex.exp (-((b : ℂ) * I)))).re / π := by
  unfold arcH
  rw [add_im, ofReal_im, mul_im, div_ofReal_re, div_ofReal_im, I_re, I_im]
  ring

/-! ### Positivity of the real part (harmonic measure of an arc) -/

lemma one_sub_ne_zero {z : ℂ} (hz : ‖z‖ < 1) (a : ℝ) :
    1 - z * Complex.exp (-((a : ℂ) * I)) ≠ 0 :=
  slitPlane_ne_zero (one_sub_mem_slitPlane hz a)

/-- `Re ((1 + w)/(1 - w)) > 0` for `|w| < 1`. -/
lemma re_cayley_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < ((1 + w) / (1 - w)).re := by
  have h1w : 1 - w ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [← h] at hw
    simp at hw
  have hn : 0 < Complex.normSq (1 - w) := Complex.normSq_pos.2 h1w
  rw [Complex.div_re, ← add_div]
  apply div_pos _ hn
  have hw2 : Complex.normSq w < 1 := by
    rw [← Complex.sq_norm]
    nlinarith [norm_nonneg w]
  have : (1 + w).re * (1 - w).re + (1 + w).im * (1 - w).im = 1 - Complex.normSq w := by
    simp only [add_re, one_re, sub_re, add_im, one_im, sub_im, Complex.normSq_apply]
    ring
  rw [this]
  linarith

lemma hasDerivAt_logterm {z : ℂ} (hz : ‖z‖ < 1) (s : ℝ) :
    HasDerivAt (fun σ : ℂ => Complex.log (1 - z * Complex.exp (-(σ * I))))
      ((I * (z * Complex.exp (-((s : ℂ) * I)))) / (1 - z * Complex.exp (-((s : ℂ) * I))))
      (s : ℂ) := by
  have h1 : HasDerivAt (fun σ : ℂ => -(σ * I)) (-I) (s : ℂ) := by
    have h0 := (hasDerivAt_id (s : ℂ)).mul_const (-I)
    simp only [id, one_mul] at h0
    have heq : (fun σ : ℂ => -(σ * I)) = fun σ => σ * -I := by
      funext σ
      ring
    rw [heq]
    exact h0
  have h2 : HasDerivAt (fun σ : ℂ => Complex.exp (-(σ * I)))
      (Complex.exp (-((s : ℂ) * I)) * (-I)) (s : ℂ) :=
    (Complex.hasDerivAt_exp _).comp (s : ℂ) h1
  have h3 : HasDerivAt (fun σ : ℂ => 1 - z * Complex.exp (-(σ * I)))
      (-(z * (Complex.exp (-((s : ℂ) * I)) * (-I)))) (s : ℂ) :=
    (h2.const_mul z).const_sub 1
  have h4 := h3.clog (one_sub_mem_slitPlane hz s)
  convert h4 using 1
  ring

lemma re_sub_two_I_mul (σ : ℝ) (L : ℂ) : ((σ : ℂ) - 2 * I * L).re = σ + 2 * L.im := by
  simp

/-- Positivity of the harmonic measure of a nonempty arc. -/
lemma re_arcH_pos {a b : ℝ} (hab : a < b) {z : ℂ} (hz : ‖z‖ < 1) : 0 < (arcH a b z).re := by
  have hwn : ∀ x : ℝ, ‖z * Complex.exp (-((x : ℂ) * I))‖ < 1 := by
    intro x
    rw [norm_mul, norm_exp_neg_mul_I, mul_one]
    exact hz
  let f : ℝ → ℝ := fun x =>
    ((1 + z * Complex.exp (-((x : ℂ) * I))) / (1 - z * Complex.exp (-((x : ℂ) * I)))).re
  let e : ℂ → ℂ := fun σ => σ - 2 * I * Complex.log (1 - z * Complex.exp (-(σ * I)))
  have hderiv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => (e y).re) (f x) x := by
    intro x
    have h := (hasDerivAt_id (x : ℂ)).sub ((hasDerivAt_logterm hz x).const_mul (2 * I))
    have hd := one_sub_ne_zero hz x
    have hval : (1 : ℂ) - 2 * I * ((I * (z * Complex.exp (-((x : ℂ) * I)))) /
        (1 - z * Complex.exp (-((x : ℂ) * I)))) =
        (1 + z * Complex.exp (-((x : ℂ) * I))) / (1 - z * Complex.exp (-((x : ℂ) * I))) := by
      set w := z * Complex.exp (-((x : ℂ) * I))
      calc (1 : ℂ) - 2 * I * (I * w / (1 - w)) = 1 - 2 * (I * I) * w / (1 - w) := by ring
        _ = 1 + 2 * w / (1 - w) := by rw [Complex.I_mul_I]; ring
        _ = (1 + w) / (1 - w) := by field_simp; ring
    rw [hval] at h
    exact h.real_of_complex
  have hcont : Continuous f := by
    apply Complex.continuous_re.comp
    apply Continuous.div
    · exact continuous_const.add (continuous_const.mul (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.mul continuous_const).neg)))
    · exact continuous_const.sub (continuous_const.mul (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.mul continuous_const).neg)))
    · intro x
      exact one_sub_ne_zero hz x
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
    (hcont.intervalIntegrable a b)
  have hpos := intervalIntegral.intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable a b)
    (fun x _ => re_cayley_pos (hwn x)) hab
  rw [hFTC] at hpos
  have hrel : (e b).re - (e a).re = 2 * π * (arcH a b z).re := by
    simp only [e]
    rw [re_sub_two_I_mul, re_sub_two_I_mul, re_arcH_eq, sub_im]
    field_simp
    ring
  rw [hrel] at hpos
  have hπ : 0 < 2 * π := by positivity
  exact pos_of_mul_pos_right hpos hπ.le

/-! ### Boundary values -/

lemma exp_mul_exp_neg (θ a : ℝ) :
    Complex.exp ((θ : ℂ) * I) * Complex.exp (-((a : ℂ) * I)) = Complex.exp (((θ - a : ℝ) : ℂ) * I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `1 - e^{iu} = 2 sin(u/2) e^{i(u-π)/2}`. -/
lemma one_sub_exp_eq_pos (u : ℝ) :
    1 - Complex.exp ((u : ℂ) * I) =
      ((2 * Real.sin (u / 2) : ℝ) : ℂ) * Complex.exp ((((u - π) / 2 : ℝ) : ℂ) * I) := by
  set q := Complex.exp (((u / 2 : ℝ) : ℂ) * I) with hq
  have hq0 : q ≠ 0 := Complex.exp_ne_zero _
  have h1 : Complex.exp ((u : ℂ) * I) = q * q := by
    rw [hq, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h2 : Complex.exp ((((u - π) / 2 : ℝ) : ℂ) * I) = q * (-I) := by
    rw [hq, show ((((u - π) / 2 : ℝ) : ℂ) * I) = (((u / 2 : ℝ) : ℂ) * I) + (-(π / 2 : ℂ) * I) by
      push_cast; ring, Complex.exp_add]
    congr 1
    rw [show (-(π / 2 : ℂ) * I) = -((π / 2 : ℂ) * I) by ring, Complex.exp_neg]
    have : Complex.exp ((π / 2 : ℂ) * I) = I := by
      rw [show (π / 2 : ℂ) * I = ((π / 2 : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
      rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
      simp
    rw [this, Complex.inv_I]
  have h3 : Complex.sin ((u : ℂ) / 2) = (q⁻¹ - q) * I / 2 := by
    have hq' : q = Complex.exp ((u : ℂ) / 2 * I) := by
      rw [hq]
      push_cast
      ring_nf
    rw [hq', ← Complex.exp_neg, Complex.sin]
    ring_nf
  rw [h1, h2]
  push_cast
  rw [h3]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

lemma norm_one_sub_exp (u : ℝ) : ‖1 - Complex.exp ((u : ℂ) * I)‖ = |2 * Real.sin (u / 2)| := by
  rw [one_sub_exp_eq_pos, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs]

lemma arg_exp_real_mul_I {x : ℝ} (hx : x ∈ Ioc (-π) π) : (Complex.exp ((x : ℂ) * I)).arg = x := by
  rw [Complex.arg_exp_mul_I, toIocMod_eq_self]
  constructor
  · exact hx.1
  · have := hx.2
    linarith

lemma arg_one_sub_exp_pos {u : ℝ} (h0 : 0 < u) (h1 : u < 2 * π) :
    (1 - Complex.exp ((u : ℂ) * I)).arg = (u - π) / 2 := by
  have hs : 0 < 2 * Real.sin (u / 2) := by
    have := Real.sin_pos_of_pos_of_lt_pi (x := u / 2) (by linarith) (by linarith)
    linarith
  rw [one_sub_exp_eq_pos, Complex.arg_real_mul _ hs, arg_exp_real_mul_I]
  constructor <;> linarith [Real.pi_pos]

lemma arg_one_sub_exp_neg {u : ℝ} (h0 : -(2 * π) < u) (h1 : u < 0) :
    (1 - Complex.exp ((u : ℂ) * I)).arg = (u + π) / 2 := by
  have hs : 0 < -(2 * Real.sin (u / 2)) := by
    have := Real.sin_pos_of_pos_of_lt_pi (x := -(u / 2)) (by linarith) (by linarith)
    rw [Real.sin_neg] at this
    linarith
  have hfac : 1 - Complex.exp ((u : ℂ) * I) =
      ((-(2 * Real.sin (u / 2)) : ℝ) : ℂ) * Complex.exp ((((u + π) / 2 : ℝ) : ℂ) * I) := by
    rw [one_sub_exp_eq_pos]
    have : Complex.exp ((((u + π) / 2 : ℝ) : ℂ) * I) =
        -Complex.exp ((((u - π) / 2 : ℝ) : ℂ) * I) := by
      rw [show ((((u + π) / 2 : ℝ) : ℂ) * I) = (((u - π) / 2 : ℝ) : ℂ) * I + π * I by
        push_cast; ring, Complex.exp_add, Complex.exp_pi_mul_I]
      ring
    rw [this]
    push_cast
    ring
  rw [hfac, Complex.arg_real_mul _ hs, arg_exp_real_mul_I]
  constructor <;> linarith [Real.pi_pos]

/-- Real part of `arcH` on the boundary: the indicator of the arc. -/
lemma re_arcH_boundary {a b θ : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 2 * π) (hθ0 : 0 < θ)
    (hθ1 : θ < 2 * π) (hθa : θ ≠ a) (hθb : θ ≠ b) :
    (arcH a b (Complex.exp ((θ : ℂ) * I))).re = if a < θ ∧ θ < b then 1 else 0 := by
  rw [re_arcH_eq, exp_mul_exp_neg, exp_mul_exp_neg, sub_im, Complex.log_im, Complex.log_im]
  have hπ : 0 < π := Real.pi_pos
  rcases lt_or_gt_of_ne hθa with h1 | h1
  · -- θ < a < b
    have h2 : θ < b := lt_trans h1 hab
    rw [arg_one_sub_exp_neg (by linarith) (by linarith),
      arg_one_sub_exp_neg (by linarith) (by linarith), if_neg (by intro h; linarith [h.1])]
    field_simp
    ring
  · rcases lt_or_gt_of_ne hθb with h2 | h2
    · -- a < θ < b
      rw [arg_one_sub_exp_pos (by linarith) (by linarith),
        arg_one_sub_exp_neg (by linarith) (by linarith), if_pos ⟨h1, h2⟩]
      field_simp
      ring
    · -- a < b < θ
      rw [arg_one_sub_exp_pos (by linarith) (by linarith),
        arg_one_sub_exp_pos (by linarith) (by linarith), if_neg (by intro h; linarith [h.2])]
      field_simp
      ring

/-- Imaginary part of `arcH` on the boundary. -/
lemma im_arcH_boundary (a b θ : ℝ) :
    (arcH a b (Complex.exp ((θ : ℂ) * I))).im = (ell (θ - a) - ell (θ - b)) / π := by
  rw [im_arcH_eq, exp_mul_exp_neg, exp_mul_exp_neg, sub_re, Complex.log_re, Complex.log_re,
    norm_one_sub_exp, norm_one_sub_exp, Real.log_abs, Real.log_abs]
  rfl

lemma one_sub_exp_mem_slitPlane {u : ℝ} (h0 : -(2 * π) < u) (h1 : u < 2 * π) (hu : u ≠ 0) :
    1 - Complex.exp ((u : ℂ) * I) ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have hc : Real.cos u < 1 := by
    rcases lt_or_eq_of_le (Real.cos_le_one u) with h | h
    · exact h
    · exact absurd ((Real.cos_eq_one_iff_of_lt_of_lt h0 h1).1 h) hu
  simp only [sub_re, one_re, Complex.exp_ofReal_mul_I_re]
  linarith

/-- Continuity of `arcH` at boundary points other than the endpoints. -/
lemma continuousAt_arcH_boundary {a b θ : ℝ} (ha : 0 ≤ a) (ha2 : a ≤ 2 * π) (hb : 0 ≤ b)
    (hb2 : b ≤ 2 * π) (hθ0 : 0 < θ) (hθ1 : θ < 2 * π) (hθa : θ ≠ a) (hθb : θ ≠ b) :
    ContinuousAt (arcH a b) (Complex.exp ((θ : ℂ) * I)) := by
  have hsa : 1 - Complex.exp ((θ : ℂ) * I) * Complex.exp (-((a : ℂ) * I)) ∈ slitPlane := by
    rw [exp_mul_exp_neg]
    exact one_sub_exp_mem_slitPlane (by linarith) (by linarith) (sub_ne_zero.2 hθa)
  have hsb : 1 - Complex.exp ((θ : ℂ) * I) * Complex.exp (-((b : ℂ) * I)) ∈ slitPlane := by
    rw [exp_mul_exp_neg]
    exact one_sub_exp_mem_slitPlane (by linarith) (by linarith) (sub_ne_zero.2 hθb)
  unfold arcH
  apply continuousAt_const.add
  apply continuousAt_const.mul
  apply ContinuousAt.sub
  · exact (continuousAt_const.sub (continuousAt_id.mul continuousAt_const)).clog hsa
  · exact (continuousAt_const.sub (continuousAt_id.mul continuousAt_const)).clog hsb

/-! ### Domination near the boundary -/

lemma normSq_one_sub_real_mul_exp (r u : ℝ) :
    Complex.normSq (1 - (r : ℂ) * Complex.exp ((u : ℂ) * I)) =
      (1 - r) ^ 2 + 4 * r * Real.sin (u / 2) ^ 2 := by
  have hc : Real.cos u = 1 - 2 * Real.sin (u / 2) ^ 2 := by
    have h1 := Real.cos_sq (u / 2)
    rw [show 2 * (u / 2) = u by ring] at h1
    have h2 := Real.sin_sq_add_cos_sq (u / 2)
    linarith
  have hsc := Real.sin_sq_add_cos_sq u
  rw [Complex.normSq_apply]
  simp only [sub_re, one_re, mul_re, ofReal_re, ofReal_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero, sub_im, one_im, mul_im, zero_sub]
  linear_combination (-2 * r) * hc + r ^ 2 * hsc

lemma abs_log_norm_le {r u : ℝ} (hr1 : 1 / 2 ≤ r) (hr2 : r ≤ 1) (hs : Real.sin (u / 2) ≠ 0) :
    |Real.log ‖1 - (r : ℂ) * Complex.exp ((u : ℂ) * I)‖| ≤
      Real.log 2 + |Real.log (Real.sin (u / 2))| := by
  set w := 1 - (r : ℂ) * Complex.exp ((u : ℂ) * I) with hw
  have hn2 : ‖w‖ ^ 2 = (1 - r) ^ 2 + 4 * r * Real.sin (u / 2) ^ 2 := by
    rw [Complex.sq_norm, hw, normSq_one_sub_real_mul_exp]
  have hup : ‖w‖ ≤ 2 := by
    calc ‖w‖ ≤ ‖(1 : ℂ)‖ + ‖(r : ℂ) * Complex.exp ((u : ℂ) * I)‖ := norm_sub_le _ _
      _ = 1 + r := by
        rw [norm_one, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      _ ≤ 2 := by linarith
  have hlow : |Real.sin (u / 2)| ≤ ‖w‖ := by
    have h : Real.sin (u / 2) ^ 2 ≤ ‖w‖ ^ 2 := by
      rw [hn2]
      nlinarith [sq_nonneg (1 - r), sq_nonneg (Real.sin (u / 2))]
    exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).1 (by rw [sq_abs]; exact h)
  have hspos : 0 < |Real.sin (u / 2)| := abs_pos.2 hs
  have hs1 : |Real.sin (u / 2)| ≤ 1 := Real.abs_sin_le_one _
  have hwpos : 0 < ‖w‖ := lt_of_lt_of_le hspos hlow
  have hlog1 : Real.log ‖w‖ ≤ Real.log 2 := Real.log_le_log hwpos hup
  have hlog2 : Real.log |Real.sin (u / 2)| ≤ Real.log ‖w‖ := Real.log_le_log hspos hlow
  have hlog3 : Real.log |Real.sin (u / 2)| ≤ 0 := Real.log_nonpos (abs_nonneg _) hs1
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [Real.log_abs] at hlog2 hlog3
  rw [abs_le, abs_of_nonpos hlog3]
  constructor <;> linarith

lemma norm_log_one_sub_le {r u : ℝ} (hr1 : 1 / 2 ≤ r) (hr2 : r ≤ 1) (hs : Real.sin (u / 2) ≠ 0) :
    ‖Complex.log (1 - (r : ℂ) * Complex.exp ((u : ℂ) * I))‖ ≤
      π + Real.log 2 + |Real.log (Real.sin (u / 2))| := by
  have h1 := Complex.norm_le_abs_re_add_abs_im (Complex.log (1 - (r : ℂ) * Complex.exp ((u : ℂ) * I)))
  rw [Complex.log_re, Complex.log_im] at h1
  have h2 := abs_log_norm_le hr1 hr2 hs
  have h3 := Complex.abs_arg_le_pi (1 - (r : ℂ) * Complex.exp ((u : ℂ) * I))
  linarith

/-- The dominating function of RIGIDITY_ALLD.md (3.2) for one arc. -/
noncomputable def domH (a b θ : ℝ) : ℝ :=
  3 + (2 * Real.log 2 + |Real.log (Real.sin ((θ - a) / 2))| +
    |Real.log (Real.sin ((θ - b) / 2))|) / π

lemma norm_arcH_le {a b : ℝ} (hab : a ≤ b) (hb : b - a ≤ 2 * π) {r θ : ℝ} (hr1 : 1 / 2 ≤ r)
    (hr2 : r ≤ 1) (hsa : Real.sin ((θ - a) / 2) ≠ 0) (hsb : Real.sin ((θ - b) / 2) ≠ 0) :
    ‖arcH a b ((r : ℂ) * Complex.exp ((θ : ℂ) * I))‖ ≤ domH a b θ := by
  unfold arcH domH
  simp only [mul_assoc, exp_mul_exp_neg]
  set La := Complex.log (1 - (r : ℂ) * Complex.exp (((θ - a : ℝ) : ℂ) * I)) with hLa
  set Lb := Complex.log (1 - (r : ℂ) * Complex.exp (((θ - b : ℝ) : ℂ) * I)) with hLb
  have h1 : ‖La‖ ≤ π + Real.log 2 + |Real.log (Real.sin ((θ - a) / 2))| :=
    norm_log_one_sub_le hr1 hr2 hsa
  have h2 : ‖Lb‖ ≤ π + Real.log 2 + |Real.log (Real.sin ((θ - b) / 2))| :=
    norm_log_one_sub_le hr1 hr2 hsb
  have hπ : 0 < π := Real.pi_pos
  have hc : ‖((((b - a) / (2 * π) : ℝ)) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_one (by positivity)]
    exact hb
  have hIπ : ‖I / (π : ℂ) * (La - Lb)‖ = ‖La - Lb‖ / π := by
    rw [norm_mul, norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hπ]
    ring
  have hdiff : ‖La - Lb‖ ≤ ‖La‖ + ‖Lb‖ := norm_sub_le _ _
  have hsum : ‖La - Lb‖ / π ≤ 2 + (2 * Real.log 2 + |Real.log (Real.sin ((θ - a) / 2))| +
      |Real.log (Real.sin ((θ - b) / 2))|) / π := by
    rw [div_le_iff₀ hπ, add_mul, div_mul_cancel₀ _ hπ.ne']
    linarith
  calc ‖((((b - a) / (2 * π) : ℝ)) : ℂ) + I / (π : ℂ) * (La - Lb)‖
      ≤ ‖((((b - a) / (2 * π) : ℝ)) : ℂ)‖ + ‖I / (π : ℂ) * (La - Lb)‖ := norm_add_le _ _
    _ ≤ 1 + (2 + (2 * Real.log 2 + |Real.log (Real.sin ((θ - a) / 2))| +
      |Real.log (Real.sin ((θ - b) / 2))|) / π) := by
        rw [hIπ]
        linarith
    _ = 3 + (2 * Real.log 2 + |Real.log (Real.sin ((θ - a) / 2))| +
      |Real.log (Real.sin ((θ - b) / 2))|) / π := by ring

/-- Interval integrability of `θ ↦ |log |sin ((θ - a)/2)||` on `[0, 2π]`. -/
lemma intervalIntegrable_abs_log_sin_half (a : ℝ) :
    IntervalIntegrable (fun θ => |Real.log (Real.sin ((θ - a) / 2))|) MeasureTheory.volume 0
      (2 * π) := by
  have h1 : IntervalIntegrable (fun x => Real.log (Real.sin (x - a / 2))) MeasureTheory.volume
      (0 - a / 2 + a / 2) (π - a / 2 + a / 2) :=
    (intervalIntegrable_log_sin (a := 0 - a / 2) (b := π - a / 2)).comp_sub_right (a / 2)
  simp only [sub_add_cancel] at h1
  have h2 := h1.comp_mul_left (c := 1 / 2)
  have h3 : IntervalIntegrable (fun θ => Real.log (Real.sin ((θ - a) / 2))) MeasureTheory.volume
      0 (2 * π) := by
    convert h2 using 2
    · ring_nf
    · simp
    · field_simp
  exact h3.abs

lemma intervalIntegrable_domH (a b : ℝ) :
    IntervalIntegrable (domH a b) MeasureTheory.volume 0 (2 * π) := by
  unfold domH
  apply intervalIntegrable_const.add
  apply IntervalIntegrable.div_const
  exact (intervalIntegrable_const.add (intervalIntegrable_abs_log_sin_half a)).add
    (intervalIntegrable_abs_log_sin_half b)

end OQP27.Cell
