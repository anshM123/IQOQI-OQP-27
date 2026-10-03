import OQP27.StripKernel

/-!
# Poisson measures of the strip, `h_λ`, and the analytic core of Theorem 2 (module L3a)

For `ν = x + iy` in the closed strip `0 ≤ x ≤ 1` let `ω_ν` be the measure `K_x(y - w) dw` for
`0 < x < 1`, `δ_y` for `x = 0` and `0` for `x = 1`.

Proved here (no hypotheses; all proofs complete):
* `fourier_stripKernel_sub`: eq. (5.1) of the paper on the imaginary axis,
  `∫ e^{iκw} ω_ν(dw) = e^{iκy} sinh(κ(1-x))/sinh κ`; mass `1 - x` and first moment `(1 - x) y`
  of `ω_ν` (`integral_stripKernel_sub`, `integral_mul_stripKernel_sub`);
* `hLam`: `h_λ(ν) = ∫ (w - λ)_+ ω_ν(dw)` (this is the definition, following the shared
  conventions of `OQP27/LEAN_BRIEF.md`; Lemma 6 of the paper identifies it with
  `-(1/π²) Im Li₂(e^{π(y-λ)} e^{-iπx})`, which is not needed here);
* the ramp kernel `rampKer u λ` (`(u-λ)_+` for `λ ≥ 0`, `(λ-u)_+` for `λ < 0`) and its Fourier
  transform `(1 + iκu - e^{iκu})/κ²`, and Fubini against densities with finite second moment;
* `poissonDefect S d p λ = Σ_{ν ∈ S} h_λ(ν) - Σ_j p_j (d_j - λ)_+` for a finite multiset `S` of
  points of the closed strip and finitely many weighted atoms.  If `ρ = Σ_{ν ∈ S} ω_ν` and
  `σ = Σ_j p_j δ_{d_j}` have the same mass and first moment, then this function is continuous
  (`continuous_poissonDefect`), equals the integrable function `rampDefect`
  (`poissonDefect_eq_rampDefect`, `integrable_rampDefect`), and its Fourier transform is
  `-(ρ̂(κ) - σ̂(κ))/κ²` for `κ ≠ 0` (`fourier_rampDefect`).  This replaces the function `W` and
  the two integrations by parts in step (b) of the paper's proof of Theorem 2;
* `eq_zero_of_fourier_eq_zero`: a continuous integrable function whose Fourier transform vanishes
  off `0` is zero (from Mathlib's Fourier inversion theorem).

Paper: `iqoqi/programs/oqp27B_all/Q_2bmv/PROOF.md`, section 5 (Lemma 6, eq. (5.1), proof of
Theorem 2, steps (a)-(c)).
-/

open Real MeasureTheory Set Filter Topology Complex
open scoped FourierTransform

namespace OQP27.StripL3a

/-! ### The Poisson measure `ω_ν(dw) = K_x(y - w) dw` of an interior point `ν = x + iy` -/

section Shifted

variable {X : ℝ}

lemma continuous_stripKernel_sub (h0 : 0 < X) (h1 : X < 1) (y : ℝ) :
    Continuous (fun w => stripKernel X (y - w)) :=
  (continuous_stripKernel h0 h1).comp (continuous_const.sub continuous_id)

lemma integrable_stripKernel_sub (h0 : 0 < X) (h1 : X < 1) (y : ℝ) :
    Integrable (fun w => stripKernel X (y - w)) :=
  (integrable_stripKernel h0 h1).comp_sub_left y

lemma integrable_mul_stripKernel_sub (h0 : 0 < X) (h1 : X < 1) (y : ℝ) :
    Integrable (fun w => w * stripKernel X (y - w)) := by
  have h : Integrable (fun v => (y - v) * stripKernel X v) := by
    simp_rw [sub_mul]
    exact ((integrable_stripKernel h0 h1).const_mul y).sub (integrable_mul_stripKernel h0 h1)
  simpa using h.comp_sub_left y

lemma integrable_sq_mul_stripKernel_sub (h0 : 0 < X) (h1 : X < 1) (y : ℝ) :
    Integrable (fun w => w ^ 2 * stripKernel X (y - w)) := by
  have h : Integrable (fun v => (y - v) ^ 2 * stripKernel X v) := by
    have e : (fun v => (y - v) ^ 2 * stripKernel X v) = fun v =>
        y ^ 2 * stripKernel X v - 2 * y * (v * stripKernel X v) + v ^ 2 * stripKernel X v := by
      funext v; ring
    rw [e]
    exact (((integrable_stripKernel h0 h1).const_mul _).sub
      ((integrable_mul_stripKernel h0 h1).const_mul _)).add (integrable_sq_mul_stripKernel h0 h1)
  simpa using h.comp_sub_left y

lemma integral_stripKernel_sub (h0 : 0 < X) (h1 : X < 1) (y : ℝ) :
    ∫ w, stripKernel X (y - w) = 1 - X := by
  rw [integral_sub_left_eq_self (fun w => stripKernel X w) volume y]
  exact integral_stripKernel h0 h1

lemma integral_mul_stripKernel_sub (h0 : 0 < X) (h1 : X < 1) (y : ℝ) :
    ∫ w, w * stripKernel X (y - w) = (1 - X) * y := by
  have e : (fun w => w * stripKernel X (y - w)) =
      fun w => (fun v => (y - v) * stripKernel X v) (y - w) := by
    funext w; simp
  rw [e, integral_sub_left_eq_self (fun v => (y - v) * stripKernel X v) volume y]
  simp_rw [sub_mul]
  rw [integral_sub ((integrable_stripKernel h0 h1).const_mul y) (integrable_mul_stripKernel h0 h1),
    integral_const_mul, integral_stripKernel h0 h1, integral_mul_stripKernel]
  ring

/-- Fourier transform of the Poisson measure of an interior point (eq. (5.1) of the paper on the
imaginary axis): `∫ e^{iκw} K_x(y - w) dw = e^{iκy} sinh(κ(1-x))/sinh κ`. -/
lemma fourier_stripKernel_sub (h0 : 0 < X) (h1 : X < 1) (y : ℝ) {κ : ℝ} (hκ : κ ≠ 0) :
    ∫ w : ℝ, cexp (I * κ * w) * (stripKernel X (y - w) : ℂ) = cexp (I * κ * y) * sinhRatio X κ := by
  have e : (fun w : ℝ => cexp (I * κ * w) * (stripKernel X (y - w) : ℂ)) =
      fun w => (fun v : ℝ => cexp (I * κ * y) * (cexp (-(I * κ * v)) * (stripKernel X v : ℂ)))
        (y - w) := by
    funext w
    simp only
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast; ring
  rw [e, integral_sub_left_eq_self
    (fun v : ℝ => cexp (I * κ * y) * (cexp (-(I * κ * v)) * (stripKernel X v : ℂ))) volume y,
    integral_const_mul, fourier_stripKernel h0 h1 hκ]

end Shifted

/-! ### `h_λ` on the closed strip -/

/-- `h_λ(ν)` for `ν = x + iy` in the closed strip `0 ≤ x ≤ 1`, defined (as in the shared
conventions of `OQP27/LEAN_BRIEF.md`) as `(y - λ)_+` on `x = 0`, `0` on `x = 1` and the Poisson
integral `∫ (w - λ)_+ K_x(y - w) dw` inside.  (Values for `x < 0` or `x > 1` are irrelevant: the
eigenvalues of `B + ig` lie in the closed strip.)  By Lemma 6 of the paper this equals
`-(1/π²) Im Li₂(e^{π(y-λ)} e^{-iπx})`; that closed form is not used here. -/
noncomputable def hLam (lam : ℝ) (ν : ℂ) : ℝ :=
  if ν.re ≤ 0 then max (ν.im - lam) 0
  else if 1 ≤ ν.re then 0
  else ∫ w, max (w - lam) 0 * stripKernel ν.re (ν.im - w)

/-! ### The ramp kernel and its Fourier transform -/

/-- `k(u, λ) = (u - λ)_+` for `λ ≥ 0` and `(λ - u)_+` for `λ < 0`.  It differs from `(u - λ)_+` by
an affine function of `u` (for `λ < 0`), and is integrable in `λ` with `∫ k(u, ·) = u²/2`. -/
noncomputable def rampKer (u lam : ℝ) : ℝ := if 0 ≤ lam then max (u - lam) 0 else max (lam - u) 0

lemma rampKer_eq (u lam : ℝ) :
    rampKer u lam = max (u - lam) 0 - (if 0 ≤ lam then 0 else u - lam) := by
  unfold rampKer
  split_ifs with h
  · ring
  · rcases le_total (u - lam) 0 with h' | h'
    · rw [max_eq_right h', max_eq_left (by linarith)]; ring
    · rw [max_eq_left h', max_eq_right (by linarith)]; ring

lemma rampKer_nonneg (u lam : ℝ) : 0 ≤ rampKer u lam := by
  unfold rampKer; split_ifs <;> exact le_max_right _ _

lemma rampKer_le (u lam : ℝ) : rampKer u lam ≤ |u| + |lam| := by
  unfold rampKer
  split_ifs <;> refine max_le ?_ (by positivity) <;>
    linarith [le_abs_self u, neg_abs_le u, le_abs_self lam, neg_abs_le lam]

lemma measurable_rampKer : Measurable (fun p : ℝ × ℝ => rampKer p.1 p.2) := by
  unfold rampKer
  exact Measurable.ite (measurableSet_le measurable_const measurable_snd) (by fun_prop) (by fun_prop)

lemma rampKer_of_nonneg {u : ℝ} (hu : 0 ≤ u) :
    rampKer u = Set.indicator (Set.Icc 0 u) (fun l => u - l) := by
  funext l
  unfold rampKer
  by_cases hl : l ∈ Set.Icc 0 u
  · rw [Set.indicator_of_mem hl, if_pos hl.1, max_eq_left (by linarith [hl.2])]
  · rw [Set.indicator_of_notMem hl]
    simp only [Set.mem_Icc, not_and_or, not_le] at hl
    split_ifs with h
    · rcases hl with hl | hl
      · linarith
      · exact max_eq_right (by linarith)
    · exact max_eq_right (by linarith)

lemma rampKer_of_neg {u : ℝ} (hu : u < 0) :
    rampKer u = Set.indicator (Set.Ico u 0) (fun l => l - u) := by
  funext l
  unfold rampKer
  by_cases hl : l ∈ Set.Ico u 0
  · rw [Set.indicator_of_mem hl, if_neg (not_le.mpr hl.2), max_eq_left (by linarith [hl.1])]
  · rw [Set.indicator_of_notMem hl]
    simp only [Set.mem_Ico, not_and_or, not_le, not_lt] at hl
    split_ifs with h
    · exact max_eq_right (by linarith)
    · rcases hl with hl | hl
      · exact max_eq_right (by linarith)
      · linarith

/-- The integral of `λ ↦ e^{iκλ} k(u, λ)` reduces to the interval integral `∫_0^u e^{iκl}(u - l) dl`
(both orientations). -/
lemma integral_rampKer_eq_interval (u : ℝ) (g : ℝ → ℂ) :
    ∫ lam, g lam * (rampKer u lam : ℂ) = ∫ l in (0:ℝ)..u, g l * ((u - l : ℝ) : ℂ) := by
  rcases le_or_gt 0 u with hu | hu
  · rw [rampKer_of_nonneg hu]
    have e : (fun lam => g lam * ((Set.indicator (Set.Icc 0 u) (fun l => u - l) lam : ℝ) : ℂ)) =
        Set.indicator (Set.Icc 0 u) (fun l => g l * ((u - l : ℝ) : ℂ)) := by
      funext lam
      by_cases h : lam ∈ Set.Icc 0 u
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h]
    rw [e, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hu]
  · rw [rampKer_of_neg hu]
    have e : (fun lam => g lam * ((Set.indicator (Set.Ico u 0) (fun l => l - u) lam : ℝ) : ℂ)) =
        Set.indicator (Set.Ico u 0) (fun l => g l * ((l - u : ℝ) : ℂ)) := by
      funext lam
      by_cases h : lam ∈ Set.Ico u 0
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h]
    rw [e, integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioo,
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hu.le,
      intervalIntegral.integral_symm]
    rw [← intervalIntegral.integral_neg]
    congr 1
    funext l
    push_cast
    ring

lemma integrable_rampKer (u : ℝ) : Integrable (rampKer u) := by
  rcases le_or_gt 0 u with hu | hu
  · rw [rampKer_of_nonneg hu]
    exact ((continuous_const.sub continuous_id).integrableOn_Icc).integrable_indicator
      measurableSet_Icc
  · rw [rampKer_of_neg hu]
    exact (((continuous_id.sub continuous_const).integrableOn_Icc).mono_set
      Set.Ico_subset_Icc_self).integrable_indicator measurableSet_Ico

lemma integral_rampKer (u : ℝ) : ∫ lam, rampKer u lam = u ^ 2 / 2 := by
  have h := integral_rampKer_eq_interval u (fun _ => (1 : ℂ))
  simp only [one_mul] at h
  rw [integral_complex_ofReal, intervalIntegral.integral_ofReal] at h
  have h2 : ∫ l in (0:ℝ)..u, (u - l) = u ^ 2 / 2 := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
      integral_id, intervalIntegral.integral_const]
    simp; ring
  rw [h2] at h
  exact_mod_cast h

/-- Fourier transform of the ramp kernel: `∫ e^{iκλ} k(u, λ) dλ = (1 + iκu - e^{iκu}) / κ²`. -/
lemma fourier_rampKer (u : ℝ) {κ : ℝ} (hκ : κ ≠ 0) :
    ∫ lam : ℝ, cexp (I * κ * lam) * (rampKer u lam : ℂ) = (1 + I * κ * u - cexp (I * κ * u)) / κ ^ 2 := by
  rw [integral_rampKer_eq_interval u (fun lam : ℝ => cexp (I * κ * lam))]
  have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ
  have hIκ : I * (κ : ℂ) ≠ 0 := mul_ne_zero I_ne_zero hκ'
  set G : ℝ → ℂ := fun l => cexp (I * κ * l) * ((u - l : ℝ) : ℂ) / (I * κ)
    + cexp (I * κ * l) / (I * κ) ^ 2 with hG
  have hderiv : ∀ l ∈ Set.uIcc (0:ℝ) u,
      HasDerivAt G (cexp (I * κ * l) * ((u - l : ℝ) : ℂ)) l := by
    intro l _
    have h1 : HasDerivAt (fun l : ℝ => cexp (I * κ * l)) (cexp (I * κ * l) * (I * κ)) l := by
      have := ((hasDerivAt_id (l : ℂ)).const_mul (I * κ)).cexp
      simpa using this.comp_ofReal
    have h2 : HasDerivAt (fun l : ℝ => ((u - l : ℝ) : ℂ)) (-1) l := by
      have := ((hasDerivAt_id l).const_sub u).ofReal_comp
      simpa using this
    have h3 := ((h1.mul h2).div_const (I * κ)).add (h1.div_const ((I * κ) ^ 2))
    refine h3.congr_deriv ?_
    rw [div_add_div _ _ hIκ (pow_ne_zero 2 hIκ), div_eq_iff (mul_ne_zero hIκ (pow_ne_zero 2 hIκ))]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((Continuous.mul (by fun_prop) (by fun_prop)).intervalIntegrable _ _)]
  simp only [hG, sub_self, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, zero_div,
    zero_add, Complex.ofReal_sub]
  field_simp
  rw [show I ^ 2 = -1 from Complex.I_sq]
  ring


/-! ### Fubini for the ramp kernel against a density with finite second moment -/

lemma integrable_rampKer_mul (r : ℝ → ℝ) (hrc : Continuous r)
    (hr2 : Integrable (fun u => u ^ 2 * r u)) :
    Integrable (fun p : ℝ × ℝ => rampKer p.1 p.2 * r p.1) (volume.prod volume) := by
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => rampKer p.1 p.2 * r p.1)
      (volume.prod volume) :=
    (measurable_rampKer.mul (hrc.measurable.comp measurable_fst)).aestronglyMeasurable
  rw [integrable_prod_iff hmeas]
  constructor
  · exact Eventually.of_forall fun u => (integrable_rampKer u).mul_const (r u)
  · have e : (fun u => ∫ lam, ‖rampKer u lam * r u‖) = fun u => (1 / 2) * |u ^ 2 * r u| := by
      funext u
      have : (fun lam => ‖rampKer u lam * r u‖) = fun lam => rampKer u lam * |r u| := by
        funext lam; rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (rampKer_nonneg u lam)]
      rw [this, integral_mul_const, integral_rampKer, abs_mul, abs_of_nonneg (sq_nonneg u)]
      ring
    rw [e]
    exact hr2.abs.const_mul (1 / 2)

lemma integrable_rampKer_integral (r : ℝ → ℝ) (hrc : Continuous r)
    (hr2 : Integrable (fun u => u ^ 2 * r u)) :
    Integrable (fun lam => ∫ u, rampKer u lam * r u) :=
  (integrable_rampKer_mul r hrc hr2).integral_prod_right

lemma fourier_rampKer_integral (r : ℝ → ℝ) (hrc : Continuous r)
    (hr2 : Integrable (fun u => u ^ 2 * r u)) {κ : ℝ} (hκ : κ ≠ 0) :
    ∫ lam : ℝ, cexp (I * κ * lam) * ((∫ u, rampKer u lam * r u : ℝ) : ℂ)
      = ∫ u : ℝ, (1 + I * κ * u - cexp (I * κ * u)) / κ ^ 2 * (r u : ℂ) := by
  have hJ := integrable_rampKer_mul r hrc hr2
  have e1 : ∀ lam : ℝ, cexp (I * κ * lam) * ((∫ u, rampKer u lam * r u : ℝ) : ℂ)
      = ∫ u, cexp (I * κ * lam) * ((rampKer u lam * r u : ℝ) : ℂ) := by
    intro lam
    rw [← integral_complex_ofReal, ← integral_const_mul]
  simp_rw [e1]
  rw [integral_integral_swap]
  · congr 1
    funext u
    have e2 : (fun lam : ℝ => cexp (I * κ * lam) * ((rampKer u lam * r u : ℝ) : ℂ))
        = fun lam : ℝ => cexp (I * κ * lam) * (rampKer u lam : ℂ) * (r u : ℂ) := by
      funext lam; push_cast; ring
    rw [e2, integral_mul_const, fourier_rampKer u hκ]
  · have hJc : Integrable (fun p : ℝ × ℝ => ((rampKer p.2 p.1 * r p.2 : ℝ) : ℂ))
        (volume.prod volume) := hJ.swap.ofReal
    refine hJc.bdd_mul (c := 1)
      ((by fun_prop : Continuous fun p : ℝ × ℝ => cexp (I * κ * p.1)).aestronglyMeasurable)
      (Eventually.of_forall fun p => ?_)
    rw [Complex.norm_exp]
    simp

/-! ### The ramp-corrected Poisson integral `ψ_ν` -/

/-- `ψ_ν(λ) = ∫ k(u, λ) ω_ν(du)`: `k(y, λ)` on `x ≤ 0`, `0` on `x ≥ 1`, and
`∫ k(u, λ) K_x(y - u) du` inside. -/
noncomputable def psiRamp (ν : ℂ) (lam : ℝ) : ℝ :=
  if ν.re ≤ 0 then rampKer ν.im lam
  else if 1 ≤ ν.re then 0
  else ∫ u, rampKer u lam * stripKernel ν.re (ν.im - u)

lemma psiRamp_of_re_nonpos {ν : ℂ} (h : ν.re ≤ 0) : psiRamp ν = rampKer ν.im :=
  funext fun _ => if_pos h

lemma psiRamp_of_one_le {ν : ℂ} (h0 : ¬ ν.re ≤ 0) (h1 : 1 ≤ ν.re) : psiRamp ν = 0 :=
  funext fun _ => by simp [psiRamp, h0, h1]

lemma psiRamp_of_interior {ν : ℂ} (h0 : 0 < ν.re) (h1 : ν.re < 1) :
    psiRamp ν = fun lam => ∫ u, rampKer u lam * stripKernel ν.re (ν.im - u) :=
  funext fun _ => by simp [psiRamp, not_le.mpr h0, not_le.mpr h1]

lemma hLam_of_re_nonpos {ν : ℂ} (h : ν.re ≤ 0) (lam : ℝ) : hLam lam ν = max (ν.im - lam) 0 :=
  if_pos h

lemma hLam_of_one_le {ν : ℂ} (h0 : ¬ ν.re ≤ 0) (h1 : 1 ≤ ν.re) (lam : ℝ) : hLam lam ν = 0 := by
  simp [hLam, h0, h1]

lemma hLam_of_interior {ν : ℂ} (h0 : 0 < ν.re) (h1 : ν.re < 1) (lam : ℝ) :
    hLam lam ν = ∫ w, max (w - lam) 0 * stripKernel ν.re (ν.im - w) := by
  simp [hLam, not_le.mpr h0, not_le.mpr h1]

lemma integrable_psiRamp (ν : ℂ) : Integrable (psiRamp ν) := by
  by_cases h0 : ν.re ≤ 0
  · rw [psiRamp_of_re_nonpos h0]; exact integrable_rampKer ν.im
  by_cases h1 : 1 ≤ ν.re
  · rw [psiRamp_of_one_le h0 h1]; exact integrable_zero _ _ _
  push Not at h0 h1
  rw [psiRamp_of_interior h0 h1]
  exact integrable_rampKer_integral _ (continuous_stripKernel_sub h0 h1 ν.im)
    (integrable_sq_mul_stripKernel_sub h0 h1 ν.im)

/-- Integrability of `w ↦ f(w) K_x(y - w)` for `|f(w)| ≤ |w| + c`. -/
lemma integrable_mul_stripKernel_sub_of_le {X : ℝ} (h0 : 0 < X) (h1 : X < 1) (y c : ℝ)
    {f : ℝ → ℝ} (hf : Measurable f) (hle : ∀ w, |f w| ≤ |w| + c) :
    Integrable (fun w => f w * stripKernel X (y - w)) := by
  refine ((integrable_mul_stripKernel_sub h0 h1 y).abs.add
    ((integrable_stripKernel_sub h0 h1 y).const_mul c)).mono'
    ((hf.mul (continuous_stripKernel_sub h0 h1 y).measurable).aestronglyMeasurable)
    (Eventually.of_forall fun w => ?_)
  have hK := (stripKernel_pos h0 h1 (y - w)).le
  simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg hK]
  calc |f w| * stripKernel X (y - w) ≤ (|w| + c) * stripKernel X (y - w) :=
        mul_le_mul_of_nonneg_right (hle w) hK
    _ = |w| * stripKernel X (y - w) + c * stripKernel X (y - w) := by ring

lemma hLam_sub_psiRamp {ν : ℂ} (h0 : 0 ≤ ν.re) (h1 : ν.re ≤ 1) (lam : ℝ) :
    hLam lam ν - psiRamp ν lam
      = if 0 ≤ lam then 0 else (1 - ν.re) * ν.im - lam * (1 - ν.re) := by
  by_cases hx0 : ν.re ≤ 0
  · have hx : ν.re = 0 := le_antisymm hx0 h0
    rw [hLam_of_re_nonpos hx0, psiRamp_of_re_nonpos hx0, rampKer_eq, hx]
    split_ifs <;> ring
  by_cases hx1 : 1 ≤ ν.re
  · have hx : ν.re = 1 := le_antisymm h1 hx1
    rw [hLam_of_one_le hx0 hx1, psiRamp_of_one_le hx0 hx1, hx]
    split_ifs <;> simp
  push Not at hx0 hx1
  rw [hLam_of_interior hx0 hx1, psiRamp_of_interior hx0 hx1]
  have hA : Integrable (fun w => max (w - lam) 0 * stripKernel ν.re (ν.im - w)) := by
    refine integrable_mul_stripKernel_sub_of_le hx0 hx1 ν.im |lam| (by fun_prop) (fun w => ?_)
    rw [abs_of_nonneg (le_max_right _ _)]
    refine max_le ?_ (by positivity)
    linarith [le_abs_self w, neg_abs_le lam]
  have hB : Integrable (fun w => rampKer w lam * stripKernel ν.re (ν.im - w)) := by
    refine integrable_mul_stripKernel_sub_of_le hx0 hx1 ν.im |lam|
      (measurable_rampKer.comp (measurable_id.prodMk measurable_const)) (fun w => ?_)
    rw [abs_of_nonneg (rampKer_nonneg w lam)]
    exact rampKer_le w lam
  rw [← integral_sub hA hB]
  have e : (fun w => max (w - lam) 0 * stripKernel ν.re (ν.im - w)
      - rampKer w lam * stripKernel ν.re (ν.im - w))
      = fun w => (if 0 ≤ lam then 0 else w - lam) * stripKernel ν.re (ν.im - w) := by
    funext w; rw [rampKer_eq]; ring
  rw [e]
  split_ifs with hl
  · simp
  · simp_rw [sub_mul]
    rw [integral_sub (integrable_mul_stripKernel_sub hx0 hx1 ν.im)
      ((integrable_stripKernel_sub hx0 hx1 ν.im).const_mul lam), integral_const_mul,
      integral_mul_stripKernel_sub hx0 hx1, integral_stripKernel_sub hx0 hx1]
    ring

lemma sinhRatio_zero_left {κ : ℝ} (hκ : κ ≠ 0) : sinhRatio 0 κ = 1 := by
  rw [sinhRatio_of_ne hκ, sub_zero, mul_one, div_self (by simpa using hκ)]

lemma sinhRatio_one_left {κ : ℝ} (hκ : κ ≠ 0) : sinhRatio 1 κ = 0 := by
  rw [sinhRatio_of_ne hκ, sub_self, mul_zero, Real.sinh_zero, zero_div]

/-- Fourier transform of `ψ_ν` for `ν` in the closed strip:
`∫ e^{iκλ} ψ_ν(λ) dλ = ((1-x) + iκ(1-x)y - e^{iκy} sinh(κ(1-x))/sinh κ) / κ²`. -/
lemma fourier_psiRamp {ν : ℂ} (h0 : 0 ≤ ν.re) (h1 : ν.re ≤ 1) {κ : ℝ} (hκ : κ ≠ 0) :
    ∫ lam : ℝ, cexp (I * κ * lam) * (psiRamp ν lam : ℂ)
      = ((1 - ν.re : ℝ) + I * κ * ((1 - ν.re) * ν.im : ℝ)
          - cexp (I * κ * ν.im) * (sinhRatio ν.re κ : ℂ)) / κ ^ 2 := by
  by_cases hx0 : ν.re ≤ 0
  · have hx : ν.re = 0 := le_antisymm hx0 h0
    rw [psiRamp_of_re_nonpos hx0, fourier_rampKer _ hκ, hx, sinhRatio_zero_left hκ]
    push_cast; ring
  by_cases hx1 : 1 ≤ ν.re
  · have hx : ν.re = 1 := le_antisymm h1 hx1
    rw [psiRamp_of_one_le hx0 hx1, hx, sinhRatio_one_left hκ]
    simp
  push Not at hx0 hx1
  rw [psiRamp_of_interior hx0 hx1, fourier_rampKer_integral _ (continuous_stripKernel_sub hx0 hx1 _)
    (integrable_sq_mul_stripKernel_sub hx0 hx1 _) hκ]
  set x := ν.re
  set y := ν.im
  have i1 : Integrable (fun u : ℝ => ((stripKernel x (y - u) : ℝ) : ℂ)) :=
    (integrable_stripKernel_sub hx0 hx1 y).ofReal
  have i2 : Integrable (fun u : ℝ => ((u * stripKernel x (y - u) : ℝ) : ℂ)) :=
    (integrable_mul_stripKernel_sub hx0 hx1 y).ofReal
  have i3 : Integrable (fun u : ℝ => cexp (I * κ * u) * ((stripKernel x (y - u) : ℝ) : ℂ)) := by
    refine i1.bdd_mul (c := 1) ((by fun_prop : Continuous fun u : ℝ => cexp (I * κ * u)).aestronglyMeasurable)
      (Eventually.of_forall fun u => ?_)
    rw [Complex.norm_exp]; simp
  have e : (fun u : ℝ => (1 + I * κ * u - cexp (I * κ * u)) / κ ^ 2 * ((stripKernel x (y - u) : ℝ) : ℂ))
      = fun u => (1 / (κ : ℂ) ^ 2) * (((stripKernel x (y - u) : ℝ) : ℂ)
          + I * κ * ((u * stripKernel x (y - u) : ℝ) : ℂ)
          - cexp (I * κ * u) * ((stripKernel x (y - u) : ℝ) : ℂ)) := by
    funext u; push_cast; ring
  have i12 : Integrable (fun u : ℝ => ((stripKernel x (y - u) : ℝ) : ℂ)
      + I * κ * ((u * stripKernel x (y - u) : ℝ) : ℂ)) := i1.add (i2.const_mul _)
  rw [e, integral_const_mul, integral_sub i12 i3,
    integral_add i1 (i2.const_mul _), integral_const_mul, integral_complex_ofReal,
    integral_complex_ofReal, integral_stripKernel_sub hx0 hx1, integral_mul_stripKernel_sub hx0 hx1,
    fourier_stripKernel_sub hx0 hx1 y hκ]
  ring

/-! ### Continuity of `λ ↦ h_λ(ν)` -/

lemma continuous_hLam (ν : ℂ) : Continuous (fun lam => hLam lam ν) := by
  by_cases hx0 : ν.re ≤ 0
  · simp_rw [hLam_of_re_nonpos hx0]; fun_prop
  by_cases hx1 : 1 ≤ ν.re
  · simp_rw [hLam_of_one_le hx0 hx1]; exact continuous_const
  push Not at hx0 hx1
  simp_rw [hLam_of_interior hx0 hx1]
  rw [continuous_iff_continuousAt]
  intro lam0
  refine continuousAt_of_dominated
    (bound := fun w => (|w| + (|lam0| + 1)) * stripKernel ν.re (ν.im - w))
    (Eventually.of_forall fun lam => ((by fun_prop : Continuous fun w : ℝ => max (w - lam) 0).mul
      (continuous_stripKernel_sub hx0 hx1 ν.im)).aestronglyMeasurable) ?_ ?_
    (Eventually.of_forall fun w => by fun_prop)
  · filter_upwards [Metric.ball_mem_nhds lam0 one_pos] with lam hlam
    refine Eventually.of_forall fun w => ?_
    have hK := (stripKernel_pos hx0 hx1 (ν.im - w)).le
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK, abs_of_nonneg (le_max_right _ _)]
    refine mul_le_mul_of_nonneg_right (max_le ?_ (by positivity)) hK
    have : |lam - lam0| < 1 := by simpa [Real.dist_eq] using hlam
    linarith [le_abs_self w, neg_abs_le lam0, abs_sub_abs_le_abs_sub lam lam0, neg_abs_le lam]
  · have : (fun w => (|w| + (|lam0| + 1)) * stripKernel ν.re (ν.im - w)) =
        fun w => |w * stripKernel ν.re (ν.im - w)| + (|lam0| + 1) * stripKernel ν.re (ν.im - w) := by
      funext w
      rw [abs_mul, abs_of_nonneg (stripKernel_pos hx0 hx1 (ν.im - w)).le]; ring
    rw [this]
    exact (integrable_mul_stripKernel_sub hx0 hx1 ν.im).abs.add
      ((integrable_stripKernel_sub hx0 hx1 ν.im).const_mul _)

/-! ### Uniqueness of the Fourier transform -/

/-- A continuous integrable function whose Fourier transform vanishes off `0` is zero. -/
theorem eq_zero_of_fourier_eq_zero {f : ℝ → ℂ} (hc : Continuous f) (hi : Integrable f)
    (h : ∀ κ : ℝ, κ ≠ 0 → ∫ u : ℝ, cexp (I * κ * u) * f u = 0) : f = 0 := by
  set T : ℝ → ℂ := fun κ => ∫ u : ℝ, cexp (I * κ * u) * f u with hT
  have hTc : Continuous T := by
    refine continuous_of_dominated (bound := fun u => ‖f u‖) (fun κ => ?_) (fun κ => ?_)
      hi.norm (Eventually.of_forall fun u => by fun_prop)
    · exact ((by fun_prop : Continuous fun u : ℝ => cexp (I * κ * u)).mul hc).aestronglyMeasurable
    · refine Eventually.of_forall fun u => ?_
      rw [norm_mul, Complex.norm_exp]; simp
  have hT0 : ∀ κ, T κ = 0 := by
    intro κ
    rcases eq_or_ne κ 0 with rfl | hκ
    · have h1 : Tendsto T (𝓝[≠] 0) (𝓝 (T 0)) :=
        hTc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have h2 : Tendsto T (𝓝[≠] 0) (𝓝 0) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with κ hκ
        exact (h κ hκ).symm
      exact tendsto_nhds_unique h1 h2
    · exact h κ hκ
  have hF : 𝓕 f = 0 := by
    funext ξ
    rw [Pi.zero_apply, Real.fourier_real_eq_integral_exp_smul]
    have := hT0 (-2 * π * ξ)
    simp only [hT] at this
    rw [← this]
    congr 1
    funext u
    rw [smul_eq_mul]
    congr 2
    push_cast; ring
  funext v
  rw [Pi.zero_apply]
  have key := hi.fourierInv_fourier_eq (v := v) (by rw [hF]; exact integrable_zero _ _ _)
    hc.continuousAt
  rw [hF] at key
  rw [← key, Real.fourierInv_eq]
  simp


/-! ### Finite sums over a multiset of points -/

lemma ofReal_multiset_map_sum (S : Multiset ℂ) (f : ℂ → ℝ) :
    (((S.map f).sum : ℝ) : ℂ) = (S.map (fun ν => (f ν : ℂ))).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih => simp [ih]

lemma integrable_multiset_sum_fun {E : Type*} [NormedAddCommGroup E] (S : Multiset ℂ)
    (F : ℂ → ℝ → E) (h : ∀ ν ∈ S, Integrable (F ν)) :
    Integrable (fun lam => (S.map (fun ν => F ν lam)).sum) := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact (h a (Multiset.mem_cons_self a S)).add
      (ih (fun ν hν => h ν (Multiset.mem_cons_of_mem hν)))

lemma integral_multiset_sum_fun (S : Multiset ℂ) (G : ℂ → ℝ → ℂ)
    (h : ∀ ν ∈ S, Integrable (G ν)) :
    ∫ lam, (S.map (fun ν => G ν lam)).sum = (S.map (fun ν => ∫ lam, G ν lam)).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    rw [integral_add (h a (Multiset.mem_cons_self a S))
      (integrable_multiset_sum_fun S G (fun ν hν => h ν (Multiset.mem_cons_of_mem hν))),
      ih (fun ν hν => h ν (Multiset.mem_cons_of_mem hν))]

lemma multiset_sum_three (S : Multiset ℂ) (a b c : ℂ → ℂ) (k q : ℂ) :
    (S.map (fun ν => (a ν + k * b ν - c ν) / q)).sum
      = ((S.map a).sum + k * (S.map b).sum - (S.map c).sum) / q := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons x S ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih]
    ring

/-! ### The analytic core of Theorem 2 -/

section Core

variable {ι : Type*} [Fintype ι]

/-- The defect function `Φ(λ) = Σ_{ν ∈ S} h_λ(ν) - Σ_j p_j (d_j - λ)_+`. -/
noncomputable def poissonDefect (S : Multiset ℂ) (d p : ι → ℝ) (lam : ℝ) : ℝ :=
  (S.map (hLam lam)).sum - ∑ j, p j * max (d j - lam) 0

/-- Its ramp-corrected version `Ψ(λ) = Σ_{ν ∈ S} ψ_ν(λ) - Σ_j p_j k(d_j, λ)`. -/
noncomputable def rampDefect (S : Multiset ℂ) (d p : ι → ℝ) (lam : ℝ) : ℝ :=
  (S.map (fun ν => psiRamp ν lam)).sum - ∑ j, p j * rampKer (d j) lam

lemma continuous_poissonDefect (S : Multiset ℂ) (d p : ι → ℝ) :
    Continuous (poissonDefect S d p) := by
  unfold poissonDefect
  refine (continuous_multiset_sum S (f := fun ν lam => hLam lam ν)
    (fun ν _ => continuous_hLam ν)).sub ?_
  exact continuous_finsetSum _ (fun j _ => by fun_prop)

lemma poissonDefect_eq_rampDefect (S : Multiset ℂ) (hS : ∀ ν ∈ S, 0 ≤ ν.re ∧ ν.re ≤ 1)
    (d p : ι → ℝ) (hmass : (S.map (fun ν => 1 - ν.re)).sum = ∑ j, p j)
    (hmom : (S.map (fun ν => (1 - ν.re) * ν.im)).sum = ∑ j, p j * d j) (lam : ℝ) :
    poissonDefect S d p lam = rampDefect S d p lam := by
  unfold poissonDefect rampDefect
  have h1 : (S.map (hLam lam)).sum = (S.map (fun ν => psiRamp ν lam)).sum
      + (S.map (fun ν => if 0 ≤ lam then 0 else (1 - ν.re) * ν.im - lam * (1 - ν.re))).sum := by
    rw [← Multiset.sum_map_add]
    congr 1
    refine Multiset.map_congr rfl (fun ν hν => ?_)
    have := hLam_sub_psiRamp (hS ν hν).1 (hS ν hν).2 lam
    linarith
  have h2 : ∑ j, p j * max (d j - lam) 0 = ∑ j, p j * rampKer (d j) lam
      + ∑ j, p j * (if 0 ≤ lam then 0 else d j - lam) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [rampKer_eq]; ring
  rw [h1, h2]
  split_ifs with hl
  · simp
  · rw [Multiset.sum_map_sub, Multiset.sum_map_mul_left, hmom, hmass]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring

lemma integrable_rampDefect (S : Multiset ℂ) (d p : ι → ℝ) :
    Integrable (rampDefect S d p) := by
  unfold rampDefect
  exact (integrable_multiset_sum_fun S psiRamp (fun ν _ => integrable_psiRamp ν)).sub
    (integrable_finsetSum _ (fun j _ => (integrable_rampKer (d j)).const_mul (p j)))

lemma fourier_rampDefect (S : Multiset ℂ) (hS : ∀ ν ∈ S, 0 ≤ ν.re ∧ ν.re ≤ 1)
    (d p : ι → ℝ) (hmass : (S.map (fun ν => 1 - ν.re)).sum = ∑ j, p j)
    (hmom : (S.map (fun ν => (1 - ν.re) * ν.im)).sum = ∑ j, p j * d j) {κ : ℝ} (hκ : κ ≠ 0) :
    ∫ lam : ℝ, cexp (I * κ * lam) * (rampDefect S d p lam : ℂ)
      = -((S.map (fun ν => cexp (I * κ * ν.im) * (sinhRatio ν.re κ : ℂ))).sum
          - ∑ j, (p j : ℂ) * cexp (I * κ * d j)) / κ ^ 2 := by
  -- integrability of the pieces
  have hbdd : ∀ g : ℝ → ℂ, Integrable g →
      Integrable (fun lam : ℝ => cexp (I * κ * lam) * g lam) := by
    intro g hg
    refine hg.bdd_mul (c := 1)
      ((by fun_prop : Continuous fun lam : ℝ => cexp (I * κ * lam)).aestronglyMeasurable)
      (Eventually.of_forall fun lam => ?_)
    rw [Complex.norm_exp]; simp
  have hA : ∀ ν ∈ S, Integrable (fun lam : ℝ => cexp (I * κ * lam) * (psiRamp ν lam : ℂ)) :=
    fun ν _ => hbdd _ (integrable_psiRamp ν).ofReal
  have hB : ∀ j ∈ (Finset.univ : Finset ι),
      Integrable (fun lam : ℝ => (p j : ℂ) * (cexp (I * κ * lam) * (rampKer (d j) lam : ℂ))) :=
    fun j _ => (hbdd _ (integrable_rampKer (d j)).ofReal).const_mul _
  have e : (fun lam : ℝ => cexp (I * κ * lam) * (rampDefect S d p lam : ℂ)) =
      fun lam : ℝ => (S.map (fun ν => cexp (I * κ * lam) * (psiRamp ν lam : ℂ))).sum
        - ∑ j, (p j : ℂ) * (cexp (I * κ * lam) * (rampKer (d j) lam : ℂ)) := by
    funext lam
    unfold rampDefect
    push_cast
    rw [ofReal_multiset_map_sum, mul_sub, ← Multiset.sum_map_mul_left, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [e, integral_sub (integrable_multiset_sum_fun S _ hA) (integrable_finsetSum _ hB),
    integral_multiset_sum_fun S _ hA, integral_finsetSum _ hB]
  -- evaluate each piece
  have e1 : (S.map (fun ν => ∫ lam : ℝ, cexp (I * κ * lam) * (psiRamp ν lam : ℂ))) =
      S.map (fun ν => (((1 - ν.re : ℝ) : ℂ) + I * κ * (((1 - ν.re) * ν.im : ℝ) : ℂ)
        - cexp (I * κ * ν.im) * (sinhRatio ν.re κ : ℂ)) / κ ^ 2) :=
    Multiset.map_congr rfl (fun ν hν => fourier_psiRamp (hS ν hν).1 (hS ν hν).2 hκ)
  have e2 : ∀ j, ∫ lam : ℝ, (p j : ℂ) * (cexp (I * κ * lam) * (rampKer (d j) lam : ℂ))
      = ((p j : ℂ) + I * κ * ((p j * d j : ℝ) : ℂ) - (p j : ℂ) * cexp (I * κ * d j)) / κ ^ 2 := by
    intro j
    rw [integral_const_mul, fourier_rampKer (d j) hκ]
    push_cast; ring
  rw [e1, multiset_sum_three, Finset.sum_congr rfl (fun j _ => e2 j), ← Finset.sum_div,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  -- use the mass and moment identities
  have hm : (S.map (fun ν => ((1 - ν.re : ℝ) : ℂ))).sum = ∑ j, (p j : ℂ) := by
    rw [← ofReal_multiset_map_sum, hmass]; push_cast; rfl
  have hmo : (S.map (fun ν => (((1 - ν.re) * ν.im : ℝ) : ℂ))).sum = ∑ j, ((p j * d j : ℝ) : ℂ) := by
    rw [← ofReal_multiset_map_sum, hmom]; push_cast; rfl
  rw [hm, hmo]
  ring

end Core

end OQP27.StripL3a
