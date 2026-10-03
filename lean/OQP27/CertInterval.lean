import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Rational interval arithmetic with soundness proofs (module L4)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

Closed intervals `[lo, hi]` with rational endpoints (`OQP27.QI`), the enclosure predicate
`OQP27.QI.Mem I x : lo ≤ x ≤ hi` for real `x`, and the operations used by the certificate checkers:
sum, negation, difference, scalar multiple, product, reciprocal of a positive interval, magnitude bound, outward
rounding to the dyadic grid `2^-k ℤ`, finite sums and table look-up.  Every operation comes with a soundness
theorem (`OQP27.QI.Mem.add`, `OQP27.QI.Mem.mul`, ...).

All operations are plain computable functions on `ℚ`, so concrete instances can be evaluated by the Lean kernel
(`decide +kernel`); the soundness theorems transfer the result to real numbers.

No hypotheses.
-/

namespace OQP27

open Finset

/-- A closed interval `[lo, hi]` with rational endpoints. -/
structure QI where
  lo : ℚ
  hi : ℚ

namespace QI

instance : Inhabited QI := ⟨⟨0, 0⟩⟩

/-- `I.Mem x`: the real number `x` lies in the interval `I`. -/
def Mem (I : QI) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

/-- The point interval `[q, q]`. -/
def pt (q : ℚ) : QI := ⟨q, q⟩

def add (I J : QI) : QI := ⟨I.lo + J.lo, I.hi + J.hi⟩

def neg (I : QI) : QI := ⟨-I.hi, -I.lo⟩

def sub (I J : QI) : QI := ⟨I.lo - J.hi, I.hi - J.lo⟩

/-- Multiplication by a rational scalar. -/
def smul (c : ℚ) (I : QI) : QI := if 0 ≤ c then ⟨c * I.lo, c * I.hi⟩ else ⟨c * I.hi, c * I.lo⟩

def mul (I J : QI) : QI :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)),
   max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))⟩

/-- Reciprocal; sound when `0 < lo`. -/
def inv (I : QI) : QI := ⟨1 / I.hi, 1 / I.lo⟩

/-- An upper bound for `|x|` on the interval. -/
def mag (I : QI) : ℚ := max |I.lo| |I.hi|

/-- Rounding down to the grid `2^-k ℤ`. -/
def rdDown (k : ℕ) (x : ℚ) : ℚ := (⌊x * 2 ^ k⌋ : ℚ) / 2 ^ k

/-- Rounding up to the grid `2^-k ℤ`. -/
def rdUp (k : ℕ) (x : ℚ) : ℚ := (⌈x * 2 ^ k⌉ : ℚ) / 2 ^ k

/-- Outward rounding of both endpoints to the grid `2^-k ℤ`. -/
def round (k : ℕ) (I : QI) : QI := ⟨rdDown k I.lo, rdUp k I.hi⟩

/-- `∑_{i < n} f i`. -/
def sumRange (n : ℕ) (f : ℕ → QI) : QI :=
  ⟨∑ i ∈ range n, (f i).lo, ∑ i ∈ range n, (f i).hi⟩

/-! ### Soundness -/

theorem mem_pt (q : ℚ) : (pt q).Mem q := ⟨le_rfl, le_rfl⟩

theorem Mem.add {I J : QI} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) : (add I J).Mem (x + y) := by
  unfold Mem QI.add at *
  push_cast
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem Mem.neg {I : QI} {x : ℝ} (hx : I.Mem x) : (neg I).Mem (-x) := by
  unfold Mem QI.neg at *
  push_cast
  constructor <;> linarith [hx.1, hx.2]

theorem Mem.sub {I J : QI} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) : (sub I J).Mem (x - y) := by
  unfold Mem QI.sub at *
  push_cast
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem Mem.smul {I : QI} {x : ℝ} (c : ℚ) (hx : I.Mem x) : (smul c I).Mem ((c : ℝ) * x) := by
  unfold Mem QI.smul at *
  split_ifs with hc
  · have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
    push_cast
    exact ⟨mul_le_mul_of_nonneg_left hx.1 hc', mul_le_mul_of_nonneg_left hx.2 hc'⟩
  · have hc' : (c : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (not_le.mp hc))
    push_cast
    exact ⟨mul_le_mul_of_nonpos_left hx.2 hc', mul_le_mul_of_nonpos_left hx.1 hc'⟩

theorem mul_lower {a b c d x y : ℝ} (ha : a ≤ x) (hb : x ≤ b) (hc : c ≤ y) (hd : y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y := by
  have h1 : min (a * y) (b * y) ≤ x * y := by
    rcases le_total 0 y with hy | hy
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right ha hy)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hb hy)
  have h2 : min (a * c) (a * d) ≤ a * y := by
    rcases le_total 0 a with h | h
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hc h)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hd h)
  have h3 : min (b * c) (b * d) ≤ b * y := by
    rcases le_total 0 b with h | h
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hc h)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hd h)
  exact (min_le_min h2 h3).trans h1

theorem mul_upper {a b c d x y : ℝ} (ha : a ≤ x) (hb : x ≤ b) (hc : c ≤ y) (hd : y ≤ d) :
    x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have h1 : x * y ≤ max (a * y) (b * y) := by
    rcases le_total 0 y with hy | hy
    · exact (mul_le_mul_of_nonneg_right hb hy).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_right ha hy).trans (le_max_left _ _)
  have h2 : a * y ≤ max (a * c) (a * d) := by
    rcases le_total 0 a with h | h
    · exact (mul_le_mul_of_nonneg_left hd h).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left hc h).trans (le_max_left _ _)
  have h3 : b * y ≤ max (b * c) (b * d) := by
    rcases le_total 0 b with h | h
    · exact (mul_le_mul_of_nonneg_left hd h).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left hc h).trans (le_max_left _ _)
  exact h1.trans (max_le_max h2 h3)

theorem Mem.mul {I J : QI} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) : (mul I J).Mem (x * y) := by
  unfold Mem QI.mul at *
  push_cast
  exact ⟨mul_lower hx.1 hx.2 hy.1 hy.2, mul_upper hx.1 hx.2 hy.1 hy.2⟩

theorem Mem.inv {I : QI} {x : ℝ} (hx : I.Mem x) (hpos : 0 < I.lo) : (inv I).Mem (1 / x) := by
  unfold Mem QI.inv at *
  have hlo : (0 : ℝ) < I.lo := by exact_mod_cast hpos
  have hxpos : 0 < x := lt_of_lt_of_le hlo hx.1
  push_cast
  exact ⟨one_div_le_one_div_of_le hxpos hx.2, one_div_le_one_div_of_le hlo hx.1⟩

theorem Mem.abs_le_mag {I : QI} {x : ℝ} (hx : I.Mem x) : |x| ≤ (I.mag : ℝ) := by
  unfold Mem mag at *
  push_cast
  rw [abs_le]
  constructor
  · have : -(I.lo : ℝ) ≤ |(I.lo : ℝ)| := neg_le_abs _
    have : |(I.lo : ℝ)| ≤ max |(I.lo : ℝ)| |(I.hi : ℝ)| := le_max_left _ _
    linarith [hx.1]
  · have : (I.hi : ℝ) ≤ |(I.hi : ℝ)| := le_abs_self _
    have : |(I.hi : ℝ)| ≤ max |(I.lo : ℝ)| |(I.hi : ℝ)| := le_max_right _ _
    linarith [hx.2]

theorem rdDown_le (k : ℕ) (x : ℚ) : rdDown k x ≤ x := by
  unfold rdDown
  have h : (0 : ℚ) < 2 ^ k := by positivity
  rw [div_le_iff₀ h]
  exact Int.floor_le _

theorem le_rdUp (k : ℕ) (x : ℚ) : x ≤ rdUp k x := by
  unfold rdUp
  have h : (0 : ℚ) < 2 ^ k := by positivity
  rw [le_div_iff₀ h]
  exact Int.le_ceil _

theorem rdDown_nonneg (k : ℕ) {x : ℚ} (hx : 0 ≤ x) : 0 ≤ rdDown k x := by
  unfold rdDown
  have h : (0 : ℚ) ≤ x * 2 ^ k := by positivity
  have h2 : (0 : ℤ) ≤ ⌊x * 2 ^ k⌋ := Int.floor_nonneg.mpr h
  have h3 : (0 : ℚ) ≤ (⌊x * 2 ^ k⌋ : ℚ) := by exact_mod_cast h2
  positivity

theorem Mem.round {I : QI} {x : ℝ} (k : ℕ) (hx : I.Mem x) : (round k I).Mem x := by
  unfold Mem QI.round at *
  have h1 : ((rdDown k I.lo : ℚ) : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast rdDown_le k I.lo
  have h2 : (I.hi : ℝ) ≤ ((rdUp k I.hi : ℚ) : ℝ) := by exact_mod_cast le_rdUp k I.hi
  exact ⟨h1.trans hx.1, hx.2.trans h2⟩

theorem Mem.widen {I J : QI} {x : ℝ} (hx : I.Mem x) (hlo : J.lo ≤ I.lo) (hhi : I.hi ≤ J.hi) :
    J.Mem x := by
  unfold Mem at *
  have h1 : (J.lo : ℝ) ≤ I.lo := by exact_mod_cast hlo
  have h2 : (I.hi : ℝ) ≤ J.hi := by exact_mod_cast hhi
  exact ⟨h1.trans hx.1, hx.2.trans h2⟩

theorem mem_sumRange {n : ℕ} {f : ℕ → QI} {x : ℕ → ℝ} (h : ∀ i < n, (f i).Mem (x i)) :
    (sumRange n f).Mem (∑ i ∈ range n, x i) := by
  unfold Mem sumRange
  simp only [Rat.cast_sum]
  constructor
  · exact Finset.sum_le_sum fun i hi => (h i (Finset.mem_range.mp hi)).1
  · exact Finset.sum_le_sum fun i hi => (h i (Finset.mem_range.mp hi)).2

/-! ### Tables -/

theorem getD_map_range {α : Type*} (n : ℕ) (f : ℕ → α) (dflt : α) {i : ℕ} (hi : i < n) :
    ((List.range n).map f).getD i dflt = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

end QI

end OQP27
