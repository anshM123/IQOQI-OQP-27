/-
OQP27/CellLegendre.lean  (module L5, layer 5: the Legendre step via the one-dimensional window)

For a strip function `h` (harmonic on the open strip, continuous on the closed strip, of linear growth)
with the boundary values of `h_λ` at `λ* = log 2/(2π)`, namely `h(iy) = (y - λ*)_+` and `h(1 + iy) = 0`,
we prove (`window_value`)
    `h(1/4) + λ*/4 = Cl₂(π/2)/π²   (= Φ_c(1/4, 1/4))`.
Proof (Q_quantum/LOG.md Q-R1: "for the arc, ∫_{B^c} (g - λ)_+ dm = h_λ(β)", and RIGIDITY_ALLD.md 3.6):
apply `mean_value_boundary` to the scalar (`M = 1`) window field `B = 1` on `(0, π/2)`, `B = 0` on
`(π/2, 2π)`: the boundary values give `2π h(1/4) = ∫_{π/2}^{2π} (g(θ) - λ*)_+ dθ` with
`g(θ) = (ℓ(θ) - ℓ(θ - π/2))/π`; an elementary trigonometric comparison shows `g > λ*` exactly on
`(π/2, π)`, and `∫_{π/2}^{π} g = 2 Cl₂(π/2)/π` (`integral_ell_sub`, `Cl₂(0) = Cl₂(π) = 0`).
So no dilogarithm identity is needed: the minimiser `λ*` and the value `Φ_c` come out of the same
mean-value identity.  No hypotheses beyond the stated ones.
-/
import OQP27.CellQT1

set_option autoImplicit false

namespace OQP27.Cell

open Polynomial Matrix Filter Topology Complex MeasureTheory Metric Set Real
open scoped Interval

/-- `λ* = log 2/(2π)`, the minimiser of `λ ↦ λ/4 + h_λ(1/4)`. -/
noncomputable def lamStar : ℝ := Real.log 2 / (2 * π)

/-! ### Trigonometric comparison -/

lemma sqrt_two_mul_sin_sub (φ : ℝ) :
    Real.sqrt 2 * Real.sin (φ - π / 4) = Real.sin φ - Real.cos φ := by
  rw [Real.sin_sub, Real.cos_pi_div_four, Real.sin_pi_div_four]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  linear_combination (Real.sin φ - Real.cos φ) / 2 * h2

/-- `π g(θ) = ℓ(θ) - ℓ(θ - π/2)` compared with `π λ* = (log 2)/2`. -/
lemma window_g_gt {θ : ℝ} (h1 : π / 2 < θ) (h2 : θ < π) :
    Real.log 2 / 2 < ell θ - ell (θ - π / 2) := by
  set φ := θ / 2 with hφ
  have hφ1 : π / 4 < φ := by rw [hφ]; linarith
  have hφ2 : φ < π / 2 := by rw [hφ]; linarith
  have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith)
  have hc : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hφ2⟩
  have hb : 0 < Real.sin (φ - π / 4) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hsq := sqrt_two_mul_sin_sub φ
  have hsqrt : 0 < Real.sqrt 2 := by positivity
  unfold ell
  rw [show (θ - π / 2) / 2 = φ - π / 4 by rw [hφ]; ring, show θ / 2 = φ from rfl]
  have ha2 : 0 < 2 * Real.sin φ := by positivity
  have hb2 : 0 < 2 * Real.sin (φ - π / 4) := by positivity
  have hlt : Real.sqrt 2 * (2 * Real.sin (φ - π / 4)) < 2 * Real.sin φ := by nlinarith
  have hl := Real.log_lt_log (by positivity) hlt
  rw [Real.log_mul hsqrt.ne' hb2.ne', Real.log_sqrt (by norm_num)] at hl
  linarith

lemma window_g_lt {θ : ℝ} (h1 : π < θ) (h2 : θ < 2 * π) :
    ell θ - ell (θ - π / 2) < Real.log 2 / 2 := by
  set φ := θ / 2 with hφ
  have hφ1 : π / 2 < φ := by rw [hφ]; linarith
  have hφ2 : φ < π := by rw [hφ]; linarith
  have hs : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) hφ2
  have hc : Real.cos φ < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt hφ1 (by linarith)
  have hb : 0 < Real.sin (φ - π / 4) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hsq := sqrt_two_mul_sin_sub φ
  have hsqrt : 0 < Real.sqrt 2 := by positivity
  unfold ell
  rw [show (θ - π / 2) / 2 = φ - π / 4 by rw [hφ]; ring, show θ / 2 = φ from rfl]
  have ha2 : 0 < 2 * Real.sin φ := by positivity
  have hb2 : 0 < 2 * Real.sin (φ - π / 4) := by positivity
  have hlt : 2 * Real.sin φ < Real.sqrt 2 * (2 * Real.sin (φ - π / 4)) := by nlinarith
  have hl := Real.log_lt_log ha2 hlt
  rw [Real.log_mul hsqrt.ne' hb2.ne', Real.log_sqrt (by norm_num)] at hl
  linarith

/-! ### The one-dimensional window -/

/-- Endpoints `0, π/2, π, 2π` of the window partition. -/
noncomputable def winT (k : ℕ) : ℝ :=
  if k = 0 then 0 else if k = 1 then π / 2 else if k = 2 then π else 2 * π

/-- The window partition of the circle into `(0, π/2)`, `(π/2, π)`, `(π, 2π)`. -/
noncomputable def winP : ArcPartition 3 where
  t := winT
  t_zero := by simp [winT]
  t_last := by simp [winT]
  t_lt := by
    intro k hk
    have hπ := Real.pi_pos
    interval_cases k <;> simp [winT] <;> linarith

/-- The window field `B = 1` on the first arc, `0` elsewhere (`M = 1`). -/
noncomputable def winB (k : ℕ) : Matrix (Fin 1) (Fin 1) ℂ := if k = 0 then 1 else 0

lemma winB_proj (k : ℕ) : IsProj (winB k) := by
  unfold winB
  split_ifs
  · exact ⟨Matrix.isHermitian_one, by simp⟩
  · exact ⟨Matrix.isHermitian_zero, by simp⟩

lemma win_op : ∑ k ∈ Finset.range 3,
    ((((winP.t (k + 1) - winP.t k) / (2 * π)) : ℝ) : ℂ) • winB k = (((1 / 4 : ℝ)) : ℂ) • 1 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, winB]
  norm_num
  simp only [winP, winT]
  norm_num
  field_simp
  ring

lemma one_by_one_eq (X : Matrix (Fin 1) (Fin 1) ℂ) : X = X 0 0 • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext i j
  fin_cases i
  fin_cases j
  simp

lemma sum_roots_one_by_one (X : Matrix (Fin 1) (Fin 1) ℂ) (h : ℂ → ℝ) :
    (X.charpoly.roots.map h).sum = h (X 0 0) := by
  conv_lhs => rw [one_by_one_eq X]
  rw [sum_roots_scalar]
  simp

lemma integral_congr_Ioo {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (h : ∀ x ∈ Ioo a b, f x = g x) :
    ∫ x in a..b, f x = ∫ x in a..b, g x := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [(Set.countable_singleton b).ae_notMem volume] with x hxb hx
  rw [Set.uIoc_of_le hab] at hx
  exact h x ⟨hx.1, lt_of_le_of_ne hx.2 hxb⟩

/-- **The window value** (Legendre step): `h(1/4) + λ*/4 = Cl₂(π/2)/π²`. -/
theorem window_value {h : ℂ → ℝ} (hharm : InnerProductSpace.HarmonicOnNhd h strip)
    (hcont : ContinuousOn h cstrip) {C : ℝ} (hC : 0 ≤ C)
    (hgrowth : ∀ w ∈ cstrip, |h w| ≤ C * (1 + ‖w‖))
    (hleft : ∀ y : ℝ, h ((y : ℂ) * I) = max (y - lamStar) 0)
    (hright : ∀ y : ℝ, h (1 + (y : ℂ) * I) = 0) :
    h ((1 / 4 : ℝ) : ℂ) + lamStar / 4 = clausen2 (π / 2) / π ^ 2 := by
  have hπ := Real.pi_pos
  obtain ⟨hint, hval⟩ := mean_value_boundary winP winB winB_proj (by norm_num) (by norm_num) win_op
    hharm hcont hC hgrowth
  set ustar : ℝ → ℝ := fun θ =>
    ((herg winP winB (Complex.exp ((θ : ℂ) * I))).charpoly.roots.map h).sum with hustar
  -- the value of `ustar` on the three arcs
  have hval_arc : ∀ x < 3, ∀ θ, winP.t x < θ → θ < winP.t (x + 1) →
      ustar θ = h (winB x 0 0 + I * ((gcoef winP 0 θ : ℝ) : ℂ)) := by
    intro x hx θ h1 h2
    simp only [hustar]
    rw [herg_boundary_eq winP winB hx h1 h2, sum_roots_one_by_one]
    congr 1
    simp [gconj, winB]
  have hA : ∫ θ in (0 : ℝ)..π / 2, ustar θ = 0 := by
    rw [integral_congr_Ioo (g := fun _ => 0) (by positivity)]
    · simp
    · intro θ hθ
      rw [hval_arc 0 (by norm_num) θ (by simpa [winP, winT] using hθ.1)
        (by simpa [winP, winT] using hθ.2)]
      simp only [winB, if_pos, Matrix.one_apply_eq]
      rw [show (1 : ℂ) + I * ((gcoef winP 0 θ : ℝ) : ℂ) = 1 + ((gcoef winP 0 θ : ℝ) : ℂ) * I by ring]
      exact hright _
  have hB : ∫ θ in π / 2..π, ustar θ = ∫ θ in π / 2..π, (gcoef winP 0 θ - lamStar) := by
    apply integral_congr_Ioo (by linarith)
    intro θ hθ
    rw [hval_arc 1 (by norm_num) θ (by simpa [winP, winT] using hθ.1)
      (by simpa [winP, winT] using hθ.2)]
    simp only [winB, if_neg one_ne_zero, Matrix.zero_apply, zero_add]
    rw [show I * ((gcoef winP 0 θ : ℝ) : ℂ) = ((gcoef winP 0 θ : ℝ) : ℂ) * I by ring, hleft]
    apply max_eq_left
    have := window_g_gt hθ.1 hθ.2
    simp only [gcoef, winP, winT]
    norm_num
    unfold lamStar
    rw [← div_div]
    exact div_le_div_of_nonneg_right this.le hπ.le
  have hC' : ∫ θ in π..2 * π, ustar θ = 0 := by
    rw [integral_congr_Ioo (g := fun _ => 0) (by linarith)]
    · simp
    · intro θ hθ
      rw [hval_arc 2 (by norm_num) θ (by simpa [winP, winT] using hθ.1)
        (by simpa [winP, winT] using hθ.2)]
      simp only [winB, show (2 : ℕ) ≠ 0 by norm_num, if_false, Matrix.zero_apply, zero_add]
      rw [show I * ((gcoef winP 0 θ : ℝ) : ℂ) = ((gcoef winP 0 θ : ℝ) : ℂ) * I by ring, hleft]
      apply max_eq_right
      have := window_g_lt hθ.1 hθ.2
      simp only [gcoef, winP, winT]
      norm_num
      unfold lamStar
      rw [← div_div]
      linarith [div_le_div_of_nonneg_right this.le hπ.le]
  have hgint : ∫ θ in π / 2..π, gcoef winP 0 θ = 2 * clausen2 (π / 2) / π := by
    have e : ∀ θ, gcoef winP 0 θ = (ell (θ - 0) - ell (θ - π / 2)) / π := by
      intro θ
      simp [gcoef, winP, winT]
    simp_rw [e]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
      (intervalIntegrable_ell_sub _ _ _) (intervalIntegrable_ell_sub _ _ _), integral_ell_sub,
      integral_ell_sub]
    rw [show π / 2 - 0 = π / 2 by ring, show π - 0 = π by ring, show π / 2 - π / 2 = (0 : ℝ) by ring,
      show π - π / 2 = π / 2 by ring, clausen2_pi, clausen2_zero]
    ring
  have hsplit : ∫ θ in (0 : ℝ)..2 * π, ustar θ = (∫ θ in (0 : ℝ)..π / 2, ustar θ) +
      (∫ θ in π / 2..π, ustar θ) + ∫ θ in π..2 * π, ustar θ := by
    have hI : ∀ a b : ℝ, a ∈ uIcc 0 (2 * π) → b ∈ uIcc 0 (2 * π) →
        IntervalIntegrable ustar volume a b := fun a b ha hb => hint.mono_set (uIcc_subset_uIcc ha hb)
    have hm : ∀ a : ℝ, 0 ≤ a → a ≤ 2 * π → a ∈ uIcc 0 (2 * π) := fun a h1 h2 => by
      rw [uIcc_of_le (by positivity)]
      exact ⟨h1, h2⟩
    rw [intervalIntegral.integral_add_adjacent_intervals
        (hI 0 (π / 2) (hm 0 le_rfl (by positivity)) (hm _ (by positivity) (by linarith)))
        (hI (π / 2) π (hm _ (by positivity) (by linarith)) (hm _ hπ.le (by linarith))),
      intervalIntegral.integral_add_adjacent_intervals
        (hI 0 π (hm 0 le_rfl (by positivity)) (hm _ hπ.le (by linarith)))
        (hI π (2 * π) (hm _ hπ.le (by linarith)) (hm _ (by positivity) le_rfl))]
  rw [hsplit, hA, hB, hC', intervalIntegral.integral_sub
    (intervalIntegrable_gcoef winP 0 _ _) intervalIntegrable_const, hgint,
    intervalIntegral.integral_const, smul_eq_mul] at hval
  push_cast at hval ⊢
  have hπ2 : π ^ 2 ≠ 0 := by positivity
  field_simp at hval ⊢
  linarith

end OQP27.Cell
