import OQP27.CertInterval
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Rigorous rational enclosures of `π`, `sin(π r)` and `cos(π r)` (module L4)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

* `OQP27.piLo < π < OQP27.piHi` (20 correct digits, from `Real.pi_gt_d20`, `Real.pi_lt_d20`).
* Taylor bounds for `0 ≤ x ≤ 1`: the partial sums of the sine and cosine series alternate around the value
  (`OQP27.sinTaylor_le_sin`, `OQP27.sin_le_sinTaylor`, `OQP27.cosTaylor_le_cos`, `OQP27.cos_le_cosTaylor`), from
  `Real.hasSum_sin`, `Real.hasSum_cos` and the alternating series bounds of Mathlib.
* `OQP27.sinSmall r`, `OQP27.cosSmall r`: enclosures of `sin(π r)`, `cos(π r)` for small `r ≥ 0`, using the
  monotonicity of `sin` and `cos` and the Taylor bounds at the rational endpoints `piLo * r`, `piHi * r`
  (rounded outward to the grid `2^-100`).
* `OQP27.sinPi r`: an enclosure of `sin(π r)` for every rational `r`, by reduction to `[0, 1/4]`
  (periodicity, `sin(x + π) = -sin x`, `sin(π - x) = sin x`, `sin x = cos(π/2 - x)`).

Every enclosure is sound for every input (`OQP27.mem_sinPi`): when a side condition fails the functions return
the trivial interval `[-1, 1]`.

No hypotheses.
-/

namespace OQP27

open Finset Real

/-- Working precision: outward rounding to the grid `2^-100`. -/
def prec : ℕ := 100

/-! ### π -/

def piLo : ℚ := 314159265358979323846 / 100000000000000000000

def piHi : ℚ := 314159265358979323847 / 100000000000000000000

theorem piLo_lt_pi : (piLo : ℝ) < π := by
  have h := Real.pi_gt_d20
  unfold piLo
  push_cast
  convert h using 1
  norm_num

theorem pi_lt_piHi : π < (piHi : ℝ) := by
  have h := Real.pi_lt_d20
  unfold piHi
  push_cast
  convert h using 1
  norm_num

theorem piLo_pos : (0 : ℝ) < piLo := by unfold piLo; push_cast; norm_num

/-! ### Taylor bounds for sine and cosine on `[0, 1]` -/

/-- `∑_{i<n} (-1)^i x^(2i+1)/(2i+1)!`. -/
def sinTaylor (x : ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ range n, (-1) ^ i * (x ^ (2 * i + 1) / ((2 * i + 1).factorial : ℚ))

/-- `∑_{i<n} (-1)^i x^(2i)/(2i)!`. -/
def cosTaylor (x : ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ range n, (-1) ^ i * (x ^ (2 * i) / ((2 * i).factorial : ℚ))

theorem sinTaylor_cast (x : ℚ) (n : ℕ) :
    ((sinTaylor x n : ℚ) : ℝ) =
      ∑ i ∈ range n, (-1) ^ i * ((x : ℝ) ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ)) := by
  unfold sinTaylor; push_cast; rfl

theorem cosTaylor_cast (x : ℚ) (n : ℕ) :
    ((cosTaylor x n : ℚ) : ℝ) =
      ∑ i ∈ range n, (-1) ^ i * ((x : ℝ) ^ (2 * i) / ((2 * i).factorial : ℝ)) := by
  unfold cosTaylor; push_cast; rfl

theorem sin_terms_antitone {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Antitone fun i : ℕ => x ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ) := by
  refine antitone_nat_of_succ_le fun i => ?_
  apply div_le_div₀ (by positivity)
  · exact pow_le_pow_of_le_one h0 h1 (by omega)
  · exact_mod_cast Nat.factorial_pos _
  · exact_mod_cast Nat.factorial_le (by omega)

theorem cos_terms_antitone {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Antitone fun i : ℕ => x ^ (2 * i) / ((2 * i).factorial : ℝ) := by
  refine antitone_nat_of_succ_le fun i => ?_
  apply div_le_div₀ (by positivity)
  · exact pow_le_pow_of_le_one h0 h1 (by omega)
  · exact_mod_cast Nat.factorial_pos _
  · exact_mod_cast Nat.factorial_le (by omega)

theorem sin_tendsto (x : ℝ) :
    Filter.Tendsto (fun n => ∑ i ∈ range n, (-1) ^ i * (x ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ)))
      Filter.atTop (nhds (Real.sin x)) := by
  have h := (Real.hasSum_sin x).tendsto_sum_nat
  simp_rw [mul_div_assoc] at h
  exact h

theorem cos_tendsto (x : ℝ) :
    Filter.Tendsto (fun n => ∑ i ∈ range n, (-1) ^ i * (x ^ (2 * i) / ((2 * i).factorial : ℝ)))
      Filter.atTop (nhds (Real.cos x)) := by
  have h := (Real.hasSum_cos x).tendsto_sum_nat
  simp_rw [mul_div_assoc] at h
  exact h

theorem sinTaylor_le_sin {x : ℚ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (k : ℕ) :
    ((sinTaylor x (2 * k) : ℚ) : ℝ) ≤ Real.sin x := by
  have h0' : (0 : ℝ) ≤ x := by exact_mod_cast h0
  have h1' : (x : ℝ) ≤ 1 := by exact_mod_cast h1
  rw [sinTaylor_cast]
  exact (sin_terms_antitone h0' h1').alternating_series_le_tendsto (sin_tendsto x) k

theorem sin_le_sinTaylor {x : ℚ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (k : ℕ) :
    Real.sin x ≤ ((sinTaylor x (2 * k + 1) : ℚ) : ℝ) := by
  have h0' : (0 : ℝ) ≤ x := by exact_mod_cast h0
  have h1' : (x : ℝ) ≤ 1 := by exact_mod_cast h1
  rw [sinTaylor_cast]
  exact (sin_terms_antitone h0' h1').tendsto_le_alternating_series (sin_tendsto x) k

theorem cosTaylor_le_cos {x : ℚ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (k : ℕ) :
    ((cosTaylor x (2 * k) : ℚ) : ℝ) ≤ Real.cos x := by
  have h0' : (0 : ℝ) ≤ x := by exact_mod_cast h0
  have h1' : (x : ℝ) ≤ 1 := by exact_mod_cast h1
  rw [cosTaylor_cast]
  exact (cos_terms_antitone h0' h1').alternating_series_le_tendsto (cos_tendsto x) k

theorem cos_le_cosTaylor {x : ℚ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (k : ℕ) :
    Real.cos x ≤ ((cosTaylor x (2 * k + 1) : ℚ) : ℝ) := by
  have h0' : (0 : ℝ) ≤ x := by exact_mod_cast h0
  have h1' : (x : ℝ) ≤ 1 := by exact_mod_cast h1
  rw [cosTaylor_cast]
  exact (cos_terms_antitone h0' h1').tendsto_le_alternating_series (cos_tendsto x) k

/-! ### `sin(π r)` and `cos(π r)` for small `r ≥ 0` -/

/-- Enclosure of `sin(π r)`; informative for `0 ≤ r` with `piHi * r ≤ 1` (e.g. `0 ≤ r ≤ 1/4`). -/
def sinSmall (r : ℚ) : QI :=
  let xl := QI.rdDown prec (piLo * r)
  let xh := QI.rdUp prec (piHi * r)
  if 0 ≤ r ∧ xh ≤ 1 then ⟨QI.rdDown prec (sinTaylor xl 10), QI.rdUp prec (sinTaylor xh 11)⟩
  else ⟨-1, 1⟩

/-- Enclosure of `cos(π r)`; informative for `0 ≤ r` with `piHi * r ≤ 1` (e.g. `0 ≤ r ≤ 1/4`). -/
def cosSmall (r : ℚ) : QI :=
  let xl := QI.rdDown prec (piLo * r)
  let xh := QI.rdUp prec (piHi * r)
  if 0 ≤ r ∧ xh ≤ 1 then ⟨QI.rdDown prec (cosTaylor xh 10), QI.rdUp prec (cosTaylor xl 11)⟩
  else ⟨-1, 1⟩

theorem mem_trivial_sin (x : ℝ) : QI.Mem ⟨-1, 1⟩ (Real.sin x) := by
  unfold QI.Mem; push_cast; exact ⟨Real.neg_one_le_sin x, Real.sin_le_one x⟩

theorem mem_trivial_cos (x : ℝ) : QI.Mem ⟨-1, 1⟩ (Real.cos x) := by
  unfold QI.Mem; push_cast; exact ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩

/-- The rational endpoints bracket `π r`. -/
theorem pi_mul_bounds {r : ℚ} (hr : 0 ≤ r) :
    ((QI.rdDown prec (piLo * r) : ℚ) : ℝ) ≤ π * r ∧ π * r ≤ ((QI.rdUp prec (piHi * r) : ℚ) : ℝ) ∧
      0 ≤ QI.rdDown prec (piLo * r) := by
  have hr' : (0 : ℝ) ≤ r := by exact_mod_cast hr
  have h1 : ((QI.rdDown prec (piLo * r) : ℚ) : ℝ) ≤ ((piLo * r : ℚ) : ℝ) := by
    exact_mod_cast QI.rdDown_le prec _
  have h2 : ((piHi * r : ℚ) : ℝ) ≤ ((QI.rdUp prec (piHi * r) : ℚ) : ℝ) := by
    exact_mod_cast QI.le_rdUp prec _
  push_cast at h1 h2
  refine ⟨h1.trans (mul_le_mul_of_nonneg_right piLo_lt_pi.le hr'),
    (mul_le_mul_of_nonneg_right pi_lt_piHi.le hr').trans h2, ?_⟩
  exact QI.rdDown_nonneg prec (mul_nonneg (by unfold piLo; norm_num) hr)

theorem mem_sinSmall (r : ℚ) : (sinSmall r).Mem (Real.sin (π * r)) := by
  unfold sinSmall
  simp only
  split_ifs with h
  · obtain ⟨hr, hxh⟩ := h
    obtain ⟨hl, hh, hl0⟩ := pi_mul_bounds hr
    have hxh' : ((QI.rdUp prec (piHi * r) : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hxh
    have hpi2 : (1 : ℝ) ≤ π / 2 := by linarith [Real.pi_gt_three]
    have hxl1 : QI.rdDown prec (piLo * r) ≤ 1 := by
      have : ((QI.rdDown prec (piLo * r) : ℚ) : ℝ) ≤ 1 := by linarith
      exact_mod_cast this
    have hxh0 : 0 ≤ QI.rdUp prec (piHi * r) := by
      have : (0 : ℝ) ≤ ((QI.rdUp prec (piHi * r) : ℚ) : ℝ) := by
        have : (0 : ℝ) ≤ ((QI.rdDown prec (piLo * r) : ℚ) : ℝ) := by exact_mod_cast hl0
        linarith
      exact_mod_cast this
    have hl0' : (0 : ℝ) ≤ ((QI.rdDown prec (piLo * r) : ℚ) : ℝ) := by exact_mod_cast hl0
    constructor
    · have e1 : ((QI.rdDown prec (sinTaylor (QI.rdDown prec (piLo * r)) 10) : ℚ) : ℝ) ≤
          ((sinTaylor (QI.rdDown prec (piLo * r)) (2 * 5) : ℚ) : ℝ) := by
        exact_mod_cast QI.rdDown_le prec _
      have e2 := sinTaylor_le_sin hl0 hxl1 5
      have e3 : Real.sin ((QI.rdDown prec (piLo * r) : ℚ) : ℝ) ≤ Real.sin (π * r) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith) hl
      linarith
    · have e1 : ((sinTaylor (QI.rdUp prec (piHi * r)) (2 * 5 + 1) : ℚ) : ℝ) ≤
          ((QI.rdUp prec (sinTaylor (QI.rdUp prec (piHi * r)) 11) : ℚ) : ℝ) := by
        exact_mod_cast QI.le_rdUp prec _
      have e2 := sin_le_sinTaylor hxh0 hxh 5
      have hpr : (0 : ℝ) ≤ π * r := mul_nonneg Real.pi_pos.le (by exact_mod_cast hr)
      have e3 : Real.sin (π * r) ≤ Real.sin ((QI.rdUp prec (piHi * r) : ℚ) : ℝ) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith) hh
      linarith
  · exact mem_trivial_sin _

theorem mem_cosSmall (r : ℚ) : (cosSmall r).Mem (Real.cos (π * r)) := by
  unfold cosSmall
  simp only
  split_ifs with h
  · obtain ⟨hr, hxh⟩ := h
    obtain ⟨hl, hh, hl0⟩ := pi_mul_bounds hr
    have hxh' : ((QI.rdUp prec (piHi * r) : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hxh
    have hxl1 : QI.rdDown prec (piLo * r) ≤ 1 := by
      have : ((QI.rdDown prec (piLo * r) : ℚ) : ℝ) ≤ 1 := by linarith
      exact_mod_cast this
    have hl0' : (0 : ℝ) ≤ ((QI.rdDown prec (piLo * r) : ℚ) : ℝ) := by exact_mod_cast hl0
    have hxh0 : 0 ≤ QI.rdUp prec (piHi * r) := by
      have : (0 : ℝ) ≤ ((QI.rdUp prec (piHi * r) : ℚ) : ℝ) := by linarith
      exact_mod_cast this
    have hpi : (1 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
    have hpr : (0 : ℝ) ≤ π * r := by linarith
    constructor
    · have e1 : ((QI.rdDown prec (cosTaylor (QI.rdUp prec (piHi * r)) 10) : ℚ) : ℝ) ≤
          ((cosTaylor (QI.rdUp prec (piHi * r)) (2 * 5) : ℚ) : ℝ) := by
        exact_mod_cast QI.rdDown_le prec _
      have e2 := cosTaylor_le_cos hxh0 hxh 5
      have e3 : Real.cos ((QI.rdUp prec (piHi * r) : ℚ) : ℝ) ≤ Real.cos (π * r) :=
        Real.cos_le_cos_of_nonneg_of_le_pi hpr (by linarith) hh
      linarith
    · have e1 : ((cosTaylor (QI.rdDown prec (piLo * r)) (2 * 5 + 1) : ℚ) : ℝ) ≤
          ((QI.rdUp prec (cosTaylor (QI.rdDown prec (piLo * r)) 11) : ℚ) : ℝ) := by
        exact_mod_cast QI.le_rdUp prec _
      have e2 := cos_le_cosTaylor hl0 hxl1 5
      have e3 : Real.cos (π * r) ≤ Real.cos ((QI.rdDown prec (piLo * r) : ℚ) : ℝ) :=
        Real.cos_le_cos_of_nonneg_of_le_pi hl0' (by linarith) hl
      linarith
  · exact mem_trivial_cos _

/-! ### `sin(π r)` for every rational `r` -/

/-- Enclosure of `sin(π r)` for every rational `r` (reduction to `[0, 1/4]`). -/
def sinPi (r : ℚ) : QI :=
  let r0 := r - 2 * (⌊r / 2⌋ : ℚ)
  let r1 := if 1 ≤ r0 then r0 - 1 else r0
  let r2 := if 1 / 2 < r1 then 1 - r1 else r1
  let base := if r2 ≤ 1 / 4 then sinSmall r2 else cosSmall (1 / 2 - r2)
  if 1 ≤ r0 then QI.neg base else base

theorem mem_sinPi (r : ℚ) : (sinPi r).Mem (Real.sin (π * r)) := by
  unfold sinPi
  simp only
  set r0 : ℚ := r - 2 * (⌊r / 2⌋ : ℚ) with hr0
  set r1 : ℚ := if 1 ≤ r0 then r0 - 1 else r0 with hr1
  set r2 : ℚ := if 1 / 2 < r1 then 1 - r1 else r1 with hr2
  -- step 0: periodicity
  have s0 : Real.sin (π * r) = Real.sin (π * r0) := by
    have : π * (r : ℝ) = π * (r0 : ℝ) + ((⌊r / 2⌋ : ℤ) : ℝ) * (2 * π) := by
      rw [hr0]; push_cast; ring
    rw [this, Real.sin_add_int_mul_two_pi]
  -- step 1: half period
  have s1 : Real.sin (π * r0) = if 1 ≤ r0 then -Real.sin (π * r1) else Real.sin (π * r1) := by
    rw [hr1]
    split_ifs with h
    · have : π * (r0 : ℝ) = π * ((r0 - 1 : ℚ) : ℝ) + π := by push_cast; ring
      rw [this, Real.sin_add_pi]
    · rfl
  -- step 2: reflection
  have s2 : Real.sin (π * r1) = Real.sin (π * r2) := by
    rw [hr2]
    split_ifs with h
    · have : π * (r1 : ℝ) = π - π * ((1 - r1 : ℚ) : ℝ) := by push_cast; ring
      rw [this, Real.sin_pi_sub]
    · rfl
  -- step 3: base enclosure
  have s3 : (if r2 ≤ 1 / 4 then sinSmall r2 else cosSmall (1 / 2 - r2)).Mem (Real.sin (π * r2)) := by
    split_ifs with h
    · exact mem_sinSmall r2
    · have := mem_cosSmall (1 / 2 - r2)
      have e : π * ((1 / 2 - r2 : ℚ) : ℝ) = π / 2 - π * r2 := by push_cast; ring
      rw [e, Real.cos_pi_div_two_sub] at this
      exact this
  rw [s0, s1, s2]
  by_cases h : 1 ≤ r0
  · rw [if_pos h, if_pos h]; exact s3.neg
  · rw [if_neg h, if_neg h]; exact s3

end OQP27
