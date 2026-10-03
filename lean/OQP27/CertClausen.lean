import OQP27.CertDefs
import OQP27.CertTrig
import Mathlib.Analysis.SumOverResidueClass
import Mathlib.Algebra.BigOperators.Fin

/-!
# Rigorous enclosures of the Clausen function at rational angles, and of `Ĝ` (module L4)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

For integers `Q ≥ 1`, `c ≥ 0`, grouping the Clausen series by residues mod `Q` gives the exact identity
(`OQP27.clausen2_rat`)

  `Cl₂(2π c/Q) = ∑_{a=0}^{Q-1} sin(2π c (a+1)/Q) · H(Q, a+1)`,  `H(Q, b) = ∑_{i ≥ 0} 1/(b + Q i)²`.

`H(Q, b)` is enclosed by `I = 20` explicit terms plus a tail bracket (`OQP27.mem_hEnc`):
`∑_{i ≥ 0} 1/(i + y)²` lies between `g₅(y) = 1/y + 1/(2y²) + 1/(6y³) - 1/(30y⁵)` and
`g₇(y) = g₅(y) + 1/(42y⁷)` for `y ≥ 1` (`OQP27.tail_bounds`).  This rests on the exact telescoping identities

  `g₇(t) - g₇(t+1) - 1/t² = (63t⁴ + 126t³ + 98t² + 35t + 5) / (210 t⁷ (t+1)⁷)`,
  `1/t² - (g₅(t) - g₅(t+1)) = (5t² + 5t + 1) / (30 t⁵ (t+1)⁵)`,

whose right-hand sides are positive for `t > 0`.  The sines are enclosed by `OQP27.sinPi` (file `CertTrig`).
The result is the enclosure `OQP27.clEnc` of `Cl₂(2π c/Q)` (`OQP27.mem_clEnc`) and, with `Q = 4dq`, the enclosure
`OQP27.gEnc` of `Ĝ(J/q)` for `0 ≤ J ≤ 2dq` (`OQP27.mem_gEnc`).

No hypotheses.
-/

namespace OQP27

open Finset Real

/-! ### Tail of `∑ 1/(i+y)²` -/

/-- `g₅(t) = 1/t + 1/(2t²) + 1/(6t³) - 1/(30t⁵)`. -/
noncomputable def g5 (t : ℝ) : ℝ := 1 / t + 1 / (2 * t ^ 2) + 1 / (6 * t ^ 3) - 1 / (30 * t ^ 5)

/-- `g₇(t) = g₅(t) + 1/(42t⁷)`. -/
noncomputable def g7 (t : ℝ) : ℝ := g5 t + 1 / (42 * t ^ 7)

theorem g7_tele {t : ℝ} (ht : 0 < t) : 1 / t ^ 2 ≤ g7 t - g7 (t + 1) := by
  have key : g7 t - g7 (t + 1) - 1 / t ^ 2 =
      (63 * t ^ 4 + 126 * t ^ 3 + 98 * t ^ 2 + 35 * t + 5) / (210 * t ^ 7 * (t + 1) ^ 7) := by
    unfold g7 g5
    have h1 : t + 1 ≠ 0 := by positivity
    field_simp
    ring
  have hpos : 0 ≤ (63 * t ^ 4 + 126 * t ^ 3 + 98 * t ^ 2 + 35 * t + 5) / (210 * t ^ 7 * (t + 1) ^ 7) := by
    positivity
  linarith

theorem g5_tele {t : ℝ} (ht : 0 < t) : g5 t - g5 (t + 1) ≤ 1 / t ^ 2 := by
  have key : 1 / t ^ 2 - (g5 t - g5 (t + 1)) = (5 * t ^ 2 + 5 * t + 1) / (30 * t ^ 5 * (t + 1) ^ 5) := by
    unfold g5
    have h1 : t + 1 ≠ 0 := by positivity
    field_simp
    ring
  have hpos : 0 ≤ (5 * t ^ 2 + 5 * t + 1) / (30 * t ^ 5 * (t + 1) ^ 5) := by positivity
  linarith

theorem g7_nonneg {t : ℝ} (ht : 1 ≤ t) : 0 ≤ g7 t := by
  unfold g7 g5
  have ht0 : 0 < t := by linarith
  have h1 : 1 / (30 * t ^ 5) ≤ 1 / t := by
    apply one_div_le_one_div_of_le ht0
    have : t ≤ t ^ 5 := by
      calc t = t ^ 1 := (pow_one t).symm
        _ ≤ t ^ 5 := pow_le_pow_right₀ ht (by norm_num)
    nlinarith
  have h2 : 0 ≤ 1 / (2 * t ^ 2) := by positivity
  have h3 : 0 ≤ 1 / (6 * t ^ 3) := by positivity
  have h4 : 0 ≤ 1 / (42 * t ^ 7) := by positivity
  linarith

theorem g5_le {t : ℝ} (ht : 1 ≤ t) : g5 t ≤ 2 / t := by
  unfold g5
  have ht0 : 0 < t := by linarith
  have h2 : 1 / (2 * t ^ 2) ≤ 1 / (2 * t) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have h3 : 1 / (6 * t ^ 3) ≤ 1 / (6 * t) := by
    apply one_div_le_one_div_of_le (by positivity)
    have : t ≤ t ^ 3 := by
      calc t = t ^ 1 := (pow_one t).symm
        _ ≤ t ^ 3 := pow_le_pow_right₀ ht (by norm_num)
    nlinarith
  have h4 : 0 ≤ 1 / (30 * t ^ 5) := by positivity
  have e : 1 / t + 1 / (2 * t) + 1 / (6 * t) = (5 / 3) / t := by field_simp; ring
  have e2 : (5 / 3) / t ≤ 2 / t := by
    apply div_le_div_of_nonneg_right (by norm_num) ht0.le
  linarith

theorem partial_upper {y : ℝ} (hy : 0 < y) (n : ℕ) :
    ∑ i ∈ range n, 1 / ((i : ℝ) + y) ^ 2 ≤ g7 y - g7 (y + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have h := g7_tele (t := y + (n : ℝ)) (by positivity)
    have e1 : y + (n : ℝ) + 1 = y + ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    have e3 : (n : ℝ) + y = y + (n : ℝ) := by ring
    rw [e1] at h
    rw [e3]
    linarith

theorem partial_lower {y : ℝ} (hy : 0 < y) (n : ℕ) :
    g5 y - g5 (y + n) ≤ ∑ i ∈ range n, 1 / ((i : ℝ) + y) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have h := g5_tele (t := y + (n : ℝ)) (by positivity)
    have e1 : y + (n : ℝ) + 1 = y + ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    have e3 : (n : ℝ) + y = y + (n : ℝ) := by ring
    rw [e1] at h
    rw [e3]
    linarith

theorem summable_inv_sq_shift {y : ℝ} (hy : 1 ≤ y) :
    Summable fun i : ℕ => 1 / ((i : ℝ) + y) ^ 2 := by
  have h : Summable fun i : ℕ => 1 / ((i : ℝ) + 1) ^ 2 := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa [Nat.cast_add, Nat.cast_one] using this
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) h
  apply one_div_le_one_div_of_le (by positivity)
  have : (i : ℝ) + 1 ≤ (i : ℝ) + y := by linarith
  have h0 : (0 : ℝ) ≤ (i : ℝ) + 1 := by positivity
  nlinarith

/-- `g₅(y) ≤ ∑_{i ≥ 0} 1/(i + y)² ≤ g₇(y)` for `y ≥ 1`. -/
theorem tail_bounds {y : ℝ} (hy : 1 ≤ y) :
    g5 y ≤ ∑' i : ℕ, 1 / ((i : ℝ) + y) ^ 2 ∧ ∑' i : ℕ, 1 / ((i : ℝ) + y) ^ 2 ≤ g7 y := by
  have hy0 : 0 < y := by linarith
  have hs := summable_inv_sq_shift hy
  constructor
  · -- lower bound by a limit argument
    by_contra hcon
    push Not at hcon
    set S := ∑' i : ℕ, 1 / ((i : ℝ) + y) ^ 2
    have hε : 0 < g5 y - S := by linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (2 / (g5 y - S))
    have h1 := partial_lower hy0 n
    have h2 : ∑ i ∈ range n, 1 / ((i : ℝ) + y) ^ 2 ≤ S :=
      hs.sum_le_tsum _ (fun i _ => by positivity)
    have hyn : 1 ≤ y + n := by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith
    have h3 := g5_le hyn
    have hn' : 0 < (n : ℝ) := lt_trans (by positivity) hn
    have h4 : 2 / (y + n) < g5 y - S := by
      rw [div_lt_iff₀ (by linarith)]
      rw [div_lt_iff₀ hε] at hn
      nlinarith
    linarith
  · refine Real.tsum_le_of_sum_range_le (fun i => by positivity) fun n => ?_
    have h1 := partial_upper hy0 n
    have hyn : 1 ≤ y + n := by have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith
    have h2 := g7_nonneg hyn
    linarith

/-! ### The sums `H(Q, b) = ∑_{i ≥ 0} 1/(b + Q i)²` -/

/-- `H(Q, b) = ∑_{i ≥ 0} 1/(b + Q i)²`. -/
noncomputable def hurwitzQ (Q b : ℕ) : ℝ := ∑' i : ℕ, 1 / ((b : ℝ) + Q * i) ^ 2

theorem summable_hurwitzQ {Q b : ℕ} (hQ : 1 ≤ Q) (hb : 1 ≤ b) :
    Summable fun i : ℕ => 1 / ((b : ℝ) + Q * i) ^ 2 := by
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
    (summable_inv_sq_shift (y := 1) le_rfl)
  apply one_div_le_one_div_of_le (by positivity)
  have hQ' : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hi : (0 : ℝ) ≤ i := i.cast_nonneg
  have : (i : ℝ) + 1 ≤ (b : ℝ) + Q * i := by nlinarith
  have h0 : (0 : ℝ) ≤ (i : ℝ) + 1 := by positivity
  nlinarith

theorem hurwitzQ_split {Q b : ℕ} (hQ : 1 ≤ Q) (hb : 1 ≤ b) (I : ℕ) :
    hurwitzQ Q b = ∑ i ∈ range I, 1 / ((b : ℝ) + Q * i) ^ 2 +
      (1 / (Q : ℝ) ^ 2) * ∑' i : ℕ, 1 / ((i : ℝ) + ((I : ℝ) + (b : ℝ) / Q)) ^ 2 := by
  unfold hurwitzQ
  rw [← (summable_hurwitzQ hQ hb).sum_add_tsum_nat_add I, ← tsum_mul_left]
  congr 1
  refine tsum_congr fun i => ?_
  have hQ0 : (Q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  push_cast
  field_simp
  ring

/-! ### Rational enclosure of `H(Q, b)` -/

/-- `g₅` over `ℚ`. -/
def tailLo (y : ℚ) : ℚ := 1 / y + 1 / (2 * y ^ 2) + 1 / (6 * y ^ 3) - 1 / (30 * y ^ 5)

/-- `g₇` over `ℚ`. -/
def tailHi (y : ℚ) : ℚ := tailLo y + 1 / (42 * y ^ 7)

theorem tailLo_cast (y : ℚ) : ((tailLo y : ℚ) : ℝ) = g5 y := by unfold tailLo g5; push_cast; ring

theorem tailHi_cast (y : ℚ) : ((tailHi y : ℚ) : ℝ) = g7 y := by
  unfold tailHi g7; push_cast; rw [tailLo_cast]

/-- Number of explicit terms in `H(Q, b)`. -/
def hTerms : ℕ := 20

/-- Enclosure of `H(Q, b)` (`Q ≥ 1`, `b ≥ 1`): `hTerms` explicit terms plus the tail bracket. -/
def hEnc (Q b : ℕ) : QI :=
  let base : ℚ := ∑ i ∈ range hTerms, 1 / ((b : ℚ) + Q * i) ^ 2
  let y : ℚ := (hTerms : ℚ) + (b : ℚ) / Q
  QI.round prec ⟨base + tailLo y / (Q : ℚ) ^ 2, base + tailHi y / (Q : ℚ) ^ 2⟩

theorem mem_hEnc {Q b : ℕ} (hQ : 1 ≤ Q) (hb : 1 ≤ b) : (hEnc Q b).Mem (hurwitzQ Q b) := by
  unfold hEnc
  simp only
  apply QI.Mem.round
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  set y : ℚ := (hTerms : ℚ) + (b : ℚ) / Q with hy
  have hy1 : (1 : ℝ) ≤ (y : ℝ) := by
    rw [hy]; push_cast
    have : (0 : ℝ) ≤ (b : ℝ) / Q := by positivity
    have : (1 : ℝ) ≤ (hTerms : ℝ) := by unfold hTerms; norm_num
    linarith
  obtain ⟨hlo, hhi⟩ := tail_bounds hy1
  rw [hurwitzQ_split hQ hb hTerms]
  have hycast : ((y : ℚ) : ℝ) = (hTerms : ℝ) + (b : ℝ) / Q := by rw [hy]; push_cast; ring
  rw [hycast] at hlo hhi
  have hbase : ((∑ i ∈ range hTerms, 1 / ((b : ℚ) + Q * i) ^ 2 : ℚ) : ℝ) =
      ∑ i ∈ range hTerms, 1 / ((b : ℝ) + Q * i) ^ 2 := by push_cast; rfl
  have hQ2 : (0 : ℝ) < 1 / (Q : ℝ) ^ 2 := by positivity
  unfold QI.Mem
  simp only
  push_cast
  rw [hbase.symm.trans (by push_cast; rfl)] at *
  constructor
  · have := mul_le_mul_of_nonneg_left hlo hQ2.le
    rw [tailLo_cast, hycast]
    have e : g5 ((hTerms : ℝ) + (b : ℝ) / Q) / (Q : ℝ) ^ 2 =
        1 / (Q : ℝ) ^ 2 * g5 ((hTerms : ℝ) + (b : ℝ) / Q) := by ring
    rw [e]
    linarith
  · have := mul_le_mul_of_nonneg_left hhi hQ2.le
    rw [tailHi_cast, hycast]
    have e : g7 ((hTerms : ℝ) + (b : ℝ) / Q) / (Q : ℝ) ^ 2 =
        1 / (Q : ℝ) ^ 2 * g7 ((hTerms : ℝ) + (b : ℝ) / Q) := by ring
    rw [e]
    linarith

/-! ### `Cl₂` at rational multiples of `2π` -/

theorem sum_zmod_val {M : Type*} [AddCommMonoid M] (Q : ℕ) [NeZero Q] (F : ℕ → M) :
    ∑ j : ZMod Q, F j.val = ∑ a ∈ range Q, F a := by
  obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by have := NeZero.pos Q; omega⟩
  exact Fin.sum_univ_eq_sum_range F (Q' + 1)

/-- Grouping the Clausen series by residues mod `Q`. -/
theorem clausen2_rat {Q : ℕ} (hQ : 1 ≤ Q) (c : ℕ) :
    clausen2 (2 * π * c / Q) =
      ∑ a ∈ range Q, Real.sin (2 * π * c * ((a : ℝ) + 1) / Q) * hurwitzQ Q (a + 1) := by
  have : NeZero Q := ⟨by omega⟩
  have hQ0 : (Q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold clausen2
  rw [Nat.sumByResidueClasses (clausen2_summable _) Q]
  rw [sum_zmod_val Q (fun a => ∑' m : ℕ, Real.sin (((((a + Q * m : ℕ) : ℝ)) + 1) * (2 * π * c / Q)) /
      ((((a + Q * m : ℕ) : ℝ)) + 1) ^ 2)]
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold hurwitzQ
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  have hsin : Real.sin ((((a + Q * m : ℕ) : ℝ) + 1) * (2 * π * c / Q)) =
      Real.sin (2 * π * c * ((a : ℝ) + 1) / Q) := by
    have : (((a + Q * m : ℕ) : ℝ) + 1) * (2 * π * c / Q) =
        2 * π * c * ((a : ℝ) + 1) / Q + ((c * m : ℕ) : ℝ) * (2 * π) := by
      push_cast; field_simp; ring
    rw [this, Real.sin_add_nat_mul_two_pi]
  rw [hsin]
  push_cast
  ring

/-! ### Rational enclosure of `Cl₂(2π c/Q)` -/

/-- Table of enclosures of `sin(2π b/Q)`, `b = 0, …, Q-1`. -/
def sinTab (Q : ℕ) : List QI := (List.range Q).map fun b : ℕ => sinPi (2 * (b : ℚ) / Q)

/-- Table of enclosures of `H(Q, a+1)`, `a = 0, …, Q-1`. -/
def hTab (Q : ℕ) : List QI := (List.range Q).map fun a => hEnc Q (a + 1)

/-- Enclosure of `Cl₂(2π c/Q)` from the two tables. -/
def clEnc (Q : ℕ) (sT hT : List QI) (c : ℕ) : QI :=
  QI.round prec (QI.sumRange Q fun a => QI.mul (sT.getD ((c * (a + 1)) % Q) default) (hT.getD a default))

theorem mem_sinTab {Q : ℕ} (hQ : 1 ≤ Q) (N : ℕ) :
    ((sinTab Q).getD (N % Q) default).Mem (Real.sin (2 * π * N / Q)) := by
  unfold sinTab
  rw [QI.getD_map_range _ _ _ (Nat.mod_lt _ (by omega))]
  have hQ0 : (Q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h := mem_sinPi (2 * ((N % Q : ℕ) : ℚ) / Q)
  have e : Real.sin (2 * π * N / Q) = Real.sin (π * ((2 * ((N % Q : ℕ) : ℚ) / Q : ℚ) : ℝ)) := by
    have hN : (N : ℝ) = ((N % Q : ℕ) : ℝ) + Q * ((N / Q : ℕ) : ℝ) := by
      have := Nat.mod_add_div N Q
      exact_mod_cast this.symm
    have : 2 * π * (N : ℝ) / Q = π * ((2 * ((N % Q : ℕ) : ℚ) / Q : ℚ) : ℝ) + ((N / Q : ℕ) : ℝ) * (2 * π) := by
      rw [hN]; push_cast; field_simp
    rw [this, Real.sin_add_nat_mul_two_pi]
  rw [e]
  exact h

theorem mem_clEnc {Q : ℕ} (hQ : 1 ≤ Q) (c : ℕ) :
    (clEnc Q (sinTab Q) (hTab Q) c).Mem (clausen2 (2 * π * c / Q)) := by
  unfold clEnc
  rw [clausen2_rat hQ c]
  apply QI.Mem.round
  apply QI.mem_sumRange
  intro a ha
  apply QI.Mem.mul
  · have h := mem_sinTab hQ (c * (a + 1))
    have e : 2 * π * ((c * (a + 1) : ℕ) : ℝ) / Q = 2 * π * c * ((a : ℝ) + 1) / Q := by push_cast; ring
    rw [e] at h
    exact h
  · unfold hTab
    rw [QI.getD_map_range _ _ _ ha]
    exact mem_hEnc hQ (by omega)

/-- Table of enclosures of `Cl₂(2π c/Q)`, `c = 0, …, n`. -/
def clTab (Q n : ℕ) : List QI :=
  let sT := sinTab Q
  let hT := hTab Q
  (List.range (n + 1)).map fun c => clEnc Q sT hT c

theorem mem_clTab {Q n c : ℕ} (hQ : 1 ≤ Q) (hc : c ≤ n) :
    ((clTab Q n).getD c default).Mem (clausen2 (2 * π * c / Q)) := by
  unfold clTab
  simp only
  rw [QI.getD_map_range _ _ _ (by omega)]
  exact mem_clEnc hQ c

/-! ### `Ĝ(J/q)` -/

/-- Enclosure of `N²/(2π²)`, `N = 4d`. -/
def factorEnc (d : ℕ) : QI :=
  QI.round prec ⟨(4 * d : ℚ) ^ 2 / (2 * piHi ^ 2), (4 * d : ℚ) ^ 2 / (2 * piLo ^ 2)⟩

theorem mem_factorEnc (d : ℕ) : (factorEnc d).Mem ((4 * (d : ℝ)) ^ 2 / (2 * π ^ 2)) := by
  unfold factorEnc
  apply QI.Mem.round
  unfold QI.Mem
  simp only
  push_cast
  have hlo := piLo_lt_pi
  have hhi := pi_lt_piHi
  have hlo0 := piLo_pos
  have hN : (0 : ℝ) ≤ (4 * (d : ℝ)) ^ 2 := by positivity
  constructor
  · apply div_le_div_of_nonneg_left hN (by positivity)
    have : π ^ 2 ≤ (piHi : ℝ) ^ 2 := by
      apply pow_le_pow_left₀ Real.pi_pos.le hhi.le
    linarith
  · apply div_le_div_of_nonneg_left hN (by positivity)
    have : (piLo : ℝ) ^ 2 ≤ π ^ 2 := by
      apply pow_le_pow_left₀ hlo0.le hlo.le
    linarith

/-- Enclosure of `Ĝ(J/q) = -(N²/2π²) (Cl₂(2πJ/Q) + Cl₂(2π(2dq-J)/Q))`, `Q = 4dq`, from a table of `Cl₂(2πc/Q)`,
`c = 0, …, 2dq`. -/
def gEnc (d q : ℕ) (clT : List QI) (J : ℕ) : QI :=
  QI.round prec (QI.neg (QI.mul (factorEnc d) (QI.add (clT.getD J default) (clT.getD (2 * d * q - J) default))))

theorem coneGhat_rat {d q J : ℕ} (hd : 1 ≤ d) (hq : 1 ≤ q) (hJ : J ≤ 2 * d * q) :
    coneGhat d ((J : ℝ) / q) = -((4 * (d : ℝ)) ^ 2 / (2 * π ^ 2)) *
      (clausen2 (2 * π * (J : ℕ) / ((4 * d * q : ℕ) : ℝ)) +
        clausen2 (2 * π * ((2 * d * q - J : ℕ) : ℝ) / ((4 * d * q : ℕ) : ℝ))) := by
  unfold coneGhat coneG
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have e1 : 2 * π * ((J : ℝ) / q) / (4 * (d : ℝ)) = 2 * π * (J : ℕ) / ((4 * d * q : ℕ) : ℝ) := by
    push_cast; field_simp
  have e2 : 2 * π * (2 * (d : ℝ) - (J : ℝ) / q) / (4 * (d : ℝ)) =
      2 * π * ((2 * d * q - J : ℕ) : ℝ) / ((4 * d * q : ℕ) : ℝ) := by
    rw [Nat.cast_sub hJ]; push_cast; field_simp
  rw [e1, e2]
  ring

theorem mem_gEnc {d q J : ℕ} (hd : 1 ≤ d) (hq : 1 ≤ q) (hJ : J ≤ 2 * d * q) :
    (gEnc d q (clTab (4 * d * q) (2 * d * q)) J).Mem (coneGhat d ((J : ℝ) / q)) := by
  unfold gEnc
  rw [coneGhat_rat hd hq hJ]
  apply QI.Mem.round
  have hQ : 1 ≤ 4 * d * q := by
    have := Nat.mul_le_mul (Nat.mul_le_mul (le_refl 4) hd) hq
    omega
  have h1 := mem_clTab (Q := 4 * d * q) (n := 2 * d * q) (c := J) hQ hJ
  have h2 := mem_clTab (Q := 4 * d * q) (n := 2 * d * q) (c := 2 * d * q - J) hQ (Nat.sub_le _ _)
  have h := ((mem_factorEnc d).mul (h1.add h2)).neg
  rw [neg_mul]
  exact h

end OQP27
