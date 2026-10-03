import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import OQP27.CertDefs

/-!
# The classical Theorem B for every `d` (module L7): definitions

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

Paper: `publish/CGLMP/paper-classical-all-d/main.tex`, Sections 3-4 (Lemma `lem:cot`, Theorem A and its proof).

This file only fixes the objects shared by the files `OQP27/Classical*.lean` (no theorems of substance;
no hypotheses).  The main result of module L7, `OQP27.ClassB.classicalTheoremB` (module L6's
`Hyp_ClassicalTheoremB d` for every `d ≥ 1`), is in `OQP27/ClassicalTheoremB.lean`; see `OQP27/STATUS_L7.md`.
For `N ≥ 1` and `u ∈ ℤ_N` (represented by `u.val ∈ {0, …, N-1}`):

* `kap N u = cot(π u/N)` (`κ` of the paper; `κ(0) = 0` because `cot 0 = cos 0 / sin 0 = 0` in Lean);
* `kbarR N m = (N²/(2π²)) (2 Cl₂(2πm/N) - Cl₂(2π(m+1)/N) - Cl₂(2π(m-1)/N))` for real `m`, and
  `kbar N u = kbarR N u.val`: the tent-smoothed kernel `κ̄(m) = ∫_{-1}^{1} (1-|v|) κ(m+v) dv` of Lemma
  `lem:smear`, written with the Clausen function `Cl₂` (`OQP27.clausen2`, module L4) as the second difference
  of the second antiderivative `G(u) = -(N²/(2π²)) Cl₂(2πu/N)` of `κ`;
* `ejun N u = kap N u - kbar N u`: the junction term `e(m) = κ(m) - κ̄(m)`;
* `pairK f X Y = ∑_{x ∈ X} ∑_{y ∈ Y} f(x - y)`: the pairing `⟨X, Y⟩` for the kernel `f`;
* `ico r L = {r, r+1, …, r+L-1}`: the interval `r + [0, L)` of `ℤ_N`;
* `CycOrd A B`: the colouring `(A, B, C = ℤ_N ∖ (A ∪ B))` is cyclically ordered (no adjacent pair `(x, x+1)` is
  coloured `(A,B)`, `(B,C)` or `(C,A)`);
* `wind A B = #{x ∈ A : x - 1 ∈ B}`: the number of junctions `B | A` (the winding number of a cyclically
  ordered colouring);
* `scSum N e = ∑_{m=2}^{N/2-1} (m-1)(-e(m))` and `fwSum N e = ∑_{m=2}^{N/2-1} m(-e(m))`: the sums `sc` and `fw`
  of Lemma `lem:junction`(4) (summed up to `N/2 - 1`; `e(N/2) = 0` for even `N`).
-/

namespace OQP27.ClassB

open Real Finset

/-- `κ(u) = cot(π u/N)` on `ℤ_N`; `κ(0) = 0`. -/
noncomputable def kap (N : ℕ) (u : ZMod N) : ℝ := Real.cot (π * (u.val : ℝ) / N)

/-- `κ̄(m) = (N²/(2π²)) (2 Cl₂(2πm/N) - Cl₂(2π(m+1)/N) - Cl₂(2π(m-1)/N))` for real `m`. -/
noncomputable def kbarR (N : ℕ) (m : ℝ) : ℝ :=
  (N : ℝ) ^ 2 / (2 * π ^ 2) *
    (2 * clausen2 (2 * π * m / N) - clausen2 (2 * π * (m + 1) / N) - clausen2 (2 * π * (m - 1) / N))

/-- The smeared kernel on `ℤ_N`: `κ̄(u) = kbarR N u.val`. -/
noncomputable def kbar (N : ℕ) (u : ZMod N) : ℝ := kbarR N (u.val : ℝ)

/-- The junction term `e = κ - κ̄` on `ℤ_N`. -/
noncomputable def ejun (N : ℕ) (u : ZMod N) : ℝ := kap N u - kbar N u

/-- The pairing `⟨X, Y⟩_f = ∑_{x ∈ X} ∑_{y ∈ Y} f(x - y)`. -/
noncomputable def pairK {N : ℕ} (f : ZMod N → ℝ) (X Y : Finset (ZMod N)) : ℝ :=
  ∑ x ∈ X, ∑ y ∈ Y, f (x - y)

/-- The interval `r + [0, L) = {r, r + 1, …, r + L - 1}` of `ℤ_N`. -/
def ico {N : ℕ} (r : ZMod N) (L : ℕ) : Finset (ZMod N) :=
  (range L).image fun i : ℕ => r + (i : ZMod N)

/-- The colouring `(A, B, C)`, `C = ℤ_N ∖ (A ∪ B)`, is cyclically ordered: no adjacent pair `(x, x+1)` is
coloured `(A, B)`, `(B, C)` or `(C, A)`. -/
def CycOrd {N : ℕ} (A B : Finset (ZMod N)) : Prop :=
  ∀ x : ZMod N, ¬ (x ∈ A ∧ x + 1 ∈ B) ∧ ¬ (x ∈ B ∧ x + 1 ∉ A ∧ x + 1 ∉ B) ∧
    ¬ (x ∉ A ∧ x ∉ B ∧ x + 1 ∈ A)

/-- The number of junctions `B | A`: `#{x ∈ A : x - 1 ∈ B}`. -/
def wind {N : ℕ} (A B : Finset (ZMod N)) : ℕ :=
  (A.filter fun x => x - 1 ∈ B).card

/-- `sc = ∑_{m=2}^{N/2-1} (m - 1) (-e(m))`. -/
noncomputable def scSum (N : ℕ) (e : ZMod N → ℝ) : ℝ :=
  ∑ m ∈ Ico 2 (N / 2), ((m : ℝ) - 1) * (-e (m : ZMod N))

/-- `fw = ∑_{m=2}^{N/2-1} m (-e(m))`. -/
noncomputable def fwSum (N : ℕ) (e : ZMod N → ℝ) : ℝ :=
  ∑ m ∈ Ico 2 (N / 2), (m : ℝ) * (-e (m : ZMod N))

/-! ## Elementary facts used by several files -/

lemma pairK_add {N : ℕ} (f g : ZMod N → ℝ) (X Y : Finset (ZMod N)) :
    pairK (fun u => f u + g u) X Y = pairK f X Y + pairK g X Y := by
  unfold pairK
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_add_distrib]

lemma pairK_congr {N : ℕ} {f g : ZMod N → ℝ} (h : ∀ u, f u = g u) (X Y : Finset (ZMod N)) :
    pairK f X Y = pairK g X Y := by
  unfold pairK
  simp only [h]

lemma kap_eq_add (N : ℕ) (u : ZMod N) : kap N u = kbar N u + ejun N u := by
  unfold ejun
  ring

end OQP27.ClassB
