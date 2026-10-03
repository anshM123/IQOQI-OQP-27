/-
OQP27/CellClausen.lean  (module L5: the Clausen function as an integral)

Module L4 (`OQP27/CertDefs.lean`) defines the Clausen function by its Fourier series
`clausen2 θ = ∑_{k ≥ 1} sin(kθ)/k²`.  The cell-embedding argument needs its integral form
    `Cl₂(x) = -∫₀ˣ log|2 sin(u/2)| du`        (`clausen2_eq_neg_integral`),
i.e. `-ℓ`, `ℓ(u) = log|2 sin(u/2)|` (`OQP27.Cell.ell`), is the derivative of `Cl₂` off `2πℤ`.
Proof: for `0 ≤ r < 1` the damped series `S_r(θ) = ∑ r^k sin(kθ)/k²` may be differentiated termwise,
`S_r'(θ) = ∑ r^k cos(kθ)/k = -log|1 - r e^{iθ}|` (Taylor series of `-log(1 - z)`), so
`S_r(x) = -∫₀ˣ log|1 - r e^{iθ}| dθ`; let `r → 1` (Tannery's theorem on the left, dominated
convergence with the bound `log 2 + |log|sin(θ/2)||` on the right).
Also proved: `clausen2` is continuous, odd, `2π`-periodic, `Cl₂(0) = Cl₂(π) = 0`, and
`∫_p^q ℓ(θ - t) dθ = Cl₂(p - t) - Cl₂(q - t)` (`integral_ell_sub`).
No hypotheses.  (This is the classical identity behind `G'' = cot(π·/N)` in QD2/LOG.md s.4 (ii).)
-/
import OQP27.CertDefs
import OQP27.CellHerglotz
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

namespace OQP27.Cell

open Real Complex Filter Topology MeasureTheory Set
open scoped Interval

/-! ### Elementary properties of the Clausen series -/

lemma summable_inv_sq_succ : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2 := by
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  simpa [Nat.cast_add, Nat.cast_one] using this

lemma norm_clausen_term_le (k : ℕ) (θ : ℝ) :
    ‖Real.sin (((k : ℝ) + 1) * θ) / ((k : ℝ) + 1) ^ 2‖ ≤ 1 / ((k : ℝ) + 1) ^ 2 := by
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((k : ℝ) + 1) ^ 2)]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)

lemma continuous_clausen2 : Continuous clausen2 := by
  unfold clausen2
  exact continuous_tsum (fun k => (Real.continuous_sin.comp (continuous_const.mul continuous_id)).div_const _)
    summable_inv_sq_succ (fun k θ => norm_clausen_term_le k θ)

lemma clausen2_zero : clausen2 0 = 0 := by
  simp [clausen2]

lemma clausen2_pi : clausen2 π = 0 := by
  unfold clausen2
  have h : ∀ k : ℕ, Real.sin (((k : ℝ) + 1) * π) = 0 := fun k => by
    have := Real.sin_nat_mul_pi (k + 1)
    push_cast at this
    exact this
  simp [h]

lemma clausen2_neg (x : ℝ) : clausen2 (-x) = -clausen2 x := by
  unfold clausen2
  rw [← tsum_neg]
  congr 1
  funext k
  rw [mul_neg, Real.sin_neg, neg_div]

lemma clausen2_add_two_pi (x : ℝ) : clausen2 (x + 2 * π) = clausen2 x := by
  unfold clausen2
  congr 1
  funext k
  congr 1
  have : ((k : ℝ) + 1) * (x + 2 * π) = ((k : ℝ) + 1) * x + ((k + 1 : ℕ) : ℤ) * (2 * π) := by
    push_cast
    ring
  rw [this, Real.sin_add_int_mul_two_pi]

/-! ### The damped series -/

/-- `S_r(θ) = ∑_{k ≥ 1} r^k sin(kθ)/k²`. -/
noncomputable def clS (r θ : ℝ) : ℝ :=
  ∑' k : ℕ, r ^ (k + 1) * Real.sin (((k : ℝ) + 1) * θ) / ((k : ℝ) + 1) ^ 2

/-- `C_r(θ) = ∑_{k ≥ 1} r^k cos(kθ)/k`. -/
noncomputable def clC (r θ : ℝ) : ℝ :=
  ∑' k : ℕ, r ^ (k + 1) * Real.cos (((k : ℝ) + 1) * θ) / ((k : ℝ) + 1)

lemma summable_pow_succ {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) : Summable fun k : ℕ => r ^ (k + 1) :=
  (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one h0 h1)

lemma hasDerivAt_clS {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (θ : ℝ) :
    HasDerivAt (clS r) (clC r θ) θ := by
  unfold clS clC
  have hk1 : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  refine hasDerivAt_tsum (𝕜 := ℝ) (F := ℝ) (u := fun k : ℕ => r ^ (k + 1))
    (g := fun k y => r ^ (k + 1) * Real.sin (((k : ℝ) + 1) * y) / ((k : ℝ) + 1) ^ 2)
    (g' := fun k y => r ^ (k + 1) * Real.cos (((k : ℝ) + 1) * y) / ((k : ℝ) + 1))
    (summable_pow_succ h0 h1) ?_ ?_ ?_ θ (y₀ := 0)
  · intro k y
    have h := ((Real.hasDerivAt_sin (((k : ℝ) + 1) * y)).comp y
      ((hasDerivAt_id y).const_mul ((k : ℝ) + 1)))
    have h2 := (h.const_mul (r ^ (k + 1))).div_const (((k : ℝ) + 1) ^ 2)
    have hk : ((k : ℝ) + 1) ≠ 0 := (hk1 k).ne'
    have hval : r ^ (k + 1) * (Real.cos (((k : ℝ) + 1) * y) * (((k : ℝ) + 1) * 1)) /
        ((k : ℝ) + 1) ^ 2 = r ^ (k + 1) * Real.cos (((k : ℝ) + 1) * y) / ((k : ℝ) + 1) := by
      field_simp
    rw [hval] at h2
    exact h2
  · intro k y
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (hk1 k), abs_of_nonneg (pow_nonneg h0 _)]
    rw [div_le_iff₀ (hk1 k)]
    calc r ^ (k + 1) * |Real.cos (((k : ℝ) + 1) * y)| ≤ r ^ (k + 1) * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (pow_nonneg h0 _)
      _ ≤ r ^ (k + 1) * ((k : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
            (pow_nonneg h0 _)
  · simp

lemma norm_real_mul_exp_lt {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (θ : ℝ) :
    ‖(r : ℂ) * Complex.exp ((θ : ℂ) * I)‖ < 1 := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg h0]
  exact h1

lemma clC_eq {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (θ : ℝ) :
    clC r θ = -Real.log ‖1 - (r : ℂ) * Complex.exp ((θ : ℂ) * I)‖ := by
  have hz := norm_real_mul_exp_lt h0 h1 θ
  have hs := Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log' hz)
  rw [Complex.neg_re, Complex.log_re] at hs
  rw [← hs.tsum_eq]
  unfold clC
  congr 1
  funext k
  rw [mul_pow, ← Complex.exp_nat_mul]
  have e1 : ((k + 1 : ℕ) : ℂ) * ((θ : ℂ) * I) = ((((k : ℝ) + 1) * θ : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [e1]
  have e2 : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [e2, ← Complex.ofReal_pow, Complex.div_ofReal_re, Complex.re_ofReal_mul,
    Complex.exp_ofReal_mul_I_re]

lemma one_sub_real_mul_exp_ne_zero {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (θ : ℝ) :
    1 - (r : ℂ) * Complex.exp ((θ : ℂ) * I) ≠ 0 := by
  intro h
  have := norm_real_mul_exp_lt h0 h1 θ
  rw [sub_eq_zero] at h
  rw [← h, norm_one] at this
  exact lt_irrefl _ this

lemma clS_eq_integral {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (x : ℝ) :
    clS r x = -∫ θ in (0 : ℝ)..x, Real.log ‖1 - (r : ℂ) * Complex.exp ((θ : ℂ) * I)‖ := by
  have hcontC : Continuous (clC r) := by
    have : clC r = fun θ : ℝ => -Real.log ‖1 - (r : ℂ) * Complex.exp ((θ : ℂ) * I)‖ :=
      funext (clC_eq h0 h1)
    rw [this]
    apply Continuous.neg
    apply Continuous.log (by fun_prop)
    intro θ
    exact norm_ne_zero_iff.2 (one_sub_real_mul_exp_ne_zero h0 h1 θ)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => hasDerivAt_clS h0 h1 θ) (hcontC.intervalIntegrable 0 x)
  have h00 : clS r 0 = 0 := by simp [clS]
  rw [h00, sub_zero] at hFTC
  rw [← hFTC, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only
  rw [clC_eq h0 h1]

/-! ### The limit `r → 1` -/

lemma ae_sin_half_ne_zero : ∀ᵐ θ ∂(volume : Measure ℝ), Real.sin (θ / 2) ≠ 0 := by
  have hc : {θ : ℝ | Real.sin (θ / 2) = 0}.Countable := by
    have : {θ : ℝ | Real.sin (θ / 2) = 0} ⊆ Set.range (fun k : ℤ => (k : ℝ) * (2 * π)) := by
      intro θ hθ
      obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.1 hθ
      exact ⟨k, by linarith⟩
    exact (Set.countable_range _).mono this
  filter_upwards [hc.ae_notMem volume] with θ hθ
  exact hθ

lemma intervalIntegrable_log_sin_half (p q : ℝ) :
    IntervalIntegrable (fun θ => Real.log (Real.sin (θ / 2))) volume p q := by
  have h := (intervalIntegrable_log_sin (a := p / 2) (b := q / 2)).comp_mul_left (c := 1 / 2)
  have e : (fun θ : ℝ => Real.log (Real.sin (θ / 2))) = fun θ => (Real.log ∘ Real.sin) (1 / 2 * θ) := by
    funext θ
    simp only [Function.comp]
    ring_nf
  rw [e]
  convert h using 1 <;> field_simp

lemma intervalIntegrable_ell (p q : ℝ) : IntervalIntegrable ell volume p q := by
  have h : IntervalIntegrable (fun θ => Real.log 2 + Real.log (Real.sin (θ / 2))) volume p q :=
    intervalIntegrable_const.add (intervalIntegrable_log_sin_half p q)
  apply h.congr_ae
  filter_upwards [ae_restrict_of_ae ae_sin_half_ne_zero] with θ hθ
  unfold ell
  rw [Real.log_mul two_ne_zero hθ]

/-- **The Clausen function as an integral**: `Cl₂(x) = -∫₀ˣ log|2 sin(u/2)| du`. -/
theorem clausen2_eq_neg_integral (x : ℝ) : clausen2 x = -∫ θ in (0 : ℝ)..x, ell θ := by
  set rs : ℕ → ℝ := fun m => 1 - 1 / ((m : ℝ) + 2) with hrs
  have hrs_half : ∀ m, 1 / 2 ≤ rs m := by
    intro m
    simp only [hrs]
    have : 1 / ((m : ℝ) + 2) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    linarith
  have hrs_lt : ∀ m, rs m < 1 := by
    intro m
    simp only [hrs]
    have : 0 < 1 / ((m : ℝ) + 2) := by positivity
    linarith
  have hrs_lim : Tendsto rs atTop (𝓝 1) := by
    have : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 2)) atTop (𝓝 0) := by
      have h2 : Tendsto (fun m : ℕ => (m : ℝ) + 2) atTop atTop :=
        tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      simpa [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp h2
    rw [hrs]
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
  -- the series side
  have hA : Tendsto (fun m => clS (rs m) x) atTop (𝓝 (clausen2 x)) := by
    unfold clS clausen2
    apply tendsto_tsum_of_dominated_convergence summable_inv_sq_succ
    · intro k
      have hp : Tendsto (fun m => rs m ^ (k + 1)) atTop (𝓝 1) := by
        simpa using hrs_lim.pow (k + 1)
      have := (hp.mul_const (Real.sin (((k : ℝ) + 1) * x))).div_const (((k : ℝ) + 1) ^ 2)
      simpa using this
    · apply Eventually.of_forall
      intro m k
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < ((k : ℝ) + 1) ^ 2)]
      apply div_le_div_of_nonneg_right _ (by positivity)
      rw [abs_of_nonneg (pow_nonneg (by linarith [hrs_half m]) _)]
      calc rs m ^ (k + 1) * |Real.sin (((k : ℝ) + 1) * x)| ≤ 1 * 1 :=
            mul_le_mul (pow_le_one₀ (by linarith [hrs_half m]) (hrs_lt m).le)
              (Real.abs_sin_le_one _) (abs_nonneg _) zero_le_one
        _ = 1 := by ring
  -- the integral side
  have hB : Tendsto (fun m => clS (rs m) x) atTop (𝓝 (-∫ θ in (0 : ℝ)..x, ell θ)) := by
    have heq : (fun m => clS (rs m) x) = fun m =>
        -∫ θ in (0 : ℝ)..x, Real.log ‖1 - ((rs m : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I)‖ := by
      funext m
      exact clS_eq_integral (by linarith [hrs_half m]) (hrs_lt m) x
    rw [heq]
    apply Tendsto.neg
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun θ => Real.log 2 + |Real.log (Real.sin (θ / 2))|)
    · apply Eventually.of_forall
      intro m
      apply Continuous.aestronglyMeasurable
      apply Continuous.log (by fun_prop)
      intro θ
      exact norm_ne_zero_iff.2
        (one_sub_real_mul_exp_ne_zero (by linarith [hrs_half m]) (hrs_lt m) θ)
    · apply Eventually.of_forall
      intro m
      filter_upwards [ae_sin_half_ne_zero] with θ hθ _
      rw [Real.norm_eq_abs]
      exact abs_log_norm_le (hrs_half m) (hrs_lt m).le hθ
    · exact intervalIntegrable_const.add (intervalIntegrable_log_sin_half 0 x).abs
    · filter_upwards [ae_sin_half_ne_zero] with θ hθ _
      have hne : (1 : ℂ) - Complex.exp ((θ : ℂ) * I) ≠ 0 := by
        intro h0
        have := norm_one_sub_exp θ
        rw [h0, norm_zero] at this
        have h2 : |2 * Real.sin (θ / 2)| ≠ 0 := by
          rw [abs_ne_zero]
          exact mul_ne_zero two_ne_zero hθ
        exact h2 this.symm
      have hc : ContinuousAt (fun r : ℝ => Real.log ‖1 - (r : ℂ) * Complex.exp ((θ : ℂ) * I)‖) 1 := by
        apply ContinuousAt.log (by fun_prop)
        simpa using hne
      have := hc.tendsto.comp hrs_lim
      have hval : Real.log ‖1 - ((1 : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I)‖ = ell θ := by
        rw [Complex.ofReal_one, one_mul, norm_one_sub_exp, Real.log_abs]
        rfl
      rw [hval] at this
      exact this
  exact tendsto_nhds_unique hA hB

/-- `∫_a^b ℓ = Cl₂(a) - Cl₂(b)`. -/
theorem integral_ell (a b : ℝ) : ∫ u in a..b, ell u = clausen2 a - clausen2 b := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (intervalIntegrable_ell a 0)
    (intervalIntegrable_ell 0 b), intervalIntegral.integral_symm 0 a,
    clausen2_eq_neg_integral a, clausen2_eq_neg_integral b]
  ring

/-- `∫_p^q ℓ(θ - t) dθ = Cl₂(p - t) - Cl₂(q - t)`. -/
theorem integral_ell_sub (p q t : ℝ) :
    ∫ θ in p..q, ell (θ - t) = clausen2 (p - t) - clausen2 (q - t) := by
  rw [intervalIntegral.integral_comp_sub_right ell t, integral_ell]

end OQP27.Cell
