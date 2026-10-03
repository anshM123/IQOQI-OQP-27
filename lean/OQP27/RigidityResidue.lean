import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Mul

/-!
# OQP 27B rigidity, Step 3: the residue lemma (module L6)

Paper proof: `iqoqi/programs/oqp27B_all/Q_rig/RIGIDITY_ALLD.md`, section 4 (Lemma 4.1 and
Proposition 4.2), with the explicit conjugate function (3.1) of section 3.2.

What is proved here (no hypotheses remain in this file):

* `OQP27.residue_scalar`, `OQP27.residue_lemma`, `OQP27.residue_lemma_paper` (Lemma 4.1).
  If `∑ⱼ cot((θ - tⱼ)/2) • Jⱼ = 0` for all `θ` in a set whose image under `θ ↦ e^{iθ}` is infinite
  (for instance a nonempty open interval avoiding the poles), and the `tⱼ` are pairwise distinct
  modulo `2π`, then every `Jⱼ = 0`. The proof is the residue argument of the paper in algebraic form:
  with `u = e^{iθ}`, `aⱼ = e^{itⱼ}` one has `cot((θ - tⱼ)/2) = i (u + aⱼ)/(u - aⱼ)`, so the identity
  says that a polynomial in `u` has infinitely many roots; evaluating that polynomial (which is then
  zero) at `u = aⱼ` isolates the residue `2 aⱼ Jⱼ ∏_{k ≠ j} (aⱼ - a_k)`.
* `OQP27.log_residue`: if `∑ⱼ log|sin((θ - tⱼ)/2)| • cⱼ = 0` on a nondegenerate open interval
  without poles, then every `cⱼ = 0` (differentiate: `d/dθ log|sin((θ - t)/2)| = cot((θ - t)/2)/2`,
  then Lemma 4.1).
* The cell geometry of a cell vector `ℓ` with all cells positive (`cellT`, `cellT_strictMono`, ...).
* `OQP27.conjField`: the explicit conjugate function (3.1),
  `g(θ) = (1/π) ∑_{j ∈ ℤ_N} (B_j - B_{j-1}) log|sin((θ - t_j)/2)|`, and `OQP27.stepField`, the step
  field `θ ↦ B_x` on `[t_x, t_{x+1})`.
* `OQP27.commute_of_ae_commute` (Proposition 4.2): if `[B(θ), g(θ)] = 0` for almost every
  `θ ∈ (0, 2π)` and all cells have positive length, then all `B_x` commute pairwise.
-/

set_option linter.unusedSectionVars false

open Complex Polynomial MeasureTheory

namespace OQP27

/-! ## Elementary identities -/

/-- `e^{iθ} - e^{it} = 2 i sin((θ - t)/2) e^{i(θ+t)/2}`. -/
lemma exp_sub_exp (θ t : ℝ) :
    exp ((θ : ℂ) * I) - exp ((t : ℂ) * I)
      = 2 * I * (Real.sin ((θ - t) / 2) : ℂ) * exp ((((θ + t) / 2 : ℝ) : ℂ) * I) := by
  have h1 : (θ : ℂ) * I = (((θ + t) / 2 : ℝ) : ℂ) * I + (((θ - t) / 2 : ℝ) : ℂ) * I := by
    push_cast; ring
  have h2 : (t : ℂ) * I = (((θ + t) / 2 : ℝ) : ℂ) * I + (-(((θ - t) / 2 : ℝ) : ℂ)) * I := by
    push_cast; ring
  rw [h1, h2, Complex.exp_add, Complex.exp_add, Complex.ofReal_sin]
  have hs := Complex.two_sin ((((θ - t) / 2 : ℝ) : ℂ))
  have : (2 : ℂ) * I * Complex.sin ((((θ - t) / 2 : ℝ) : ℂ))
      = exp ((((θ - t) / 2 : ℝ) : ℂ) * I) - exp ((-(((θ - t) / 2 : ℝ) : ℂ)) * I) := by
    have e : (2 : ℂ) * I * Complex.sin ((((θ - t) / 2 : ℝ) : ℂ))
        = (2 * Complex.sin ((((θ - t) / 2 : ℝ) : ℂ))) * I := by ring
    rw [e, hs]
    have hI : I * I = -1 := Complex.I_mul_I
    linear_combination (exp (-((((θ - t) / 2 : ℝ) : ℂ)) * I) - exp ((((θ - t) / 2 : ℝ) : ℂ) * I)) * hI
  rw [this]
  ring

/-- `e^{iθ} + e^{it} = 2 cos((θ - t)/2) e^{i(θ+t)/2}`. -/
lemma exp_add_exp (θ t : ℝ) :
    exp ((θ : ℂ) * I) + exp ((t : ℂ) * I)
      = 2 * (Real.cos ((θ - t) / 2) : ℂ) * exp ((((θ + t) / 2 : ℝ) : ℂ) * I) := by
  have h1 : (θ : ℂ) * I = (((θ + t) / 2 : ℝ) : ℂ) * I + (((θ - t) / 2 : ℝ) : ℂ) * I := by
    push_cast; ring
  have h2 : (t : ℂ) * I = (((θ + t) / 2 : ℝ) : ℂ) * I + (-(((θ - t) / 2 : ℝ) : ℂ)) * I := by
    push_cast; ring
  rw [h1, h2, Complex.exp_add, Complex.exp_add, Complex.ofReal_cos, Complex.two_cos]
  ring

lemma exp_ne_exp_of_sin_ne_zero {θ t : ℝ} (h : Real.sin ((θ - t) / 2) ≠ 0) :
    exp ((θ : ℂ) * I) - exp ((t : ℂ) * I) ≠ 0 := by
  rw [exp_sub_exp]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero I_ne_zero) ?_) (Complex.exp_ne_zero _)
  exact_mod_cast h

/-- `cot((θ - t)/2) = i (e^{iθ} + e^{it}) / (e^{iθ} - e^{it})` away from the poles. -/
lemma cot_half_sub {θ t : ℝ} (h : Real.sin ((θ - t) / 2) ≠ 0) :
    ((Real.cot ((θ - t) / 2) : ℝ) : ℂ)
      = I * (exp ((θ : ℂ) * I) + exp ((t : ℂ) * I)) / (exp ((θ : ℂ) * I) - exp ((t : ℂ) * I)) := by
  rw [exp_sub_exp, exp_add_exp, Real.cot_eq_cos_div_sin]
  have hs : ((Real.sin ((θ - t) / 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h
  have he := Complex.exp_ne_zero ((((θ + t) / 2 : ℝ) : ℂ) * I)
  push_cast
  field_simp

/-- `sin((θ - t)/2) = 0` exactly at the poles `θ ∈ t + 2πℤ`. -/
lemma sin_half_sub_ne_zero_iff (θ t : ℝ) :
    Real.sin ((θ - t) / 2) ≠ 0 ↔ ∀ n : ℤ, θ ≠ t + n * (2 * Real.pi) := by
  rw [Ne, Real.sin_eq_zero_iff, not_exists]
  refine forall_congr' fun n => ?_
  constructor
  · intro h1 h2
    apply h1
    rw [h2]; ring
  · intro h1 h2
    apply h1
    linarith

/-- Two real numbers have the same `e^{i·}` iff they agree modulo `2π`. -/
lemma exp_mul_I_eq_iff (s t : ℝ) :
    exp ((s : ℂ) * I) = exp ((t : ℂ) * I) ↔ ∃ n : ℤ, s = t + n * (2 * Real.pi) := by
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine exists_congr fun n => ?_
  constructor
  · intro h
    have := congrArg Complex.im h
    simpa using this
  · intro h
    rw [h]; push_cast; ring

/-! ## Lemma 4.1 (residue lemma) -/

/-- **Lemma 4.1, scalar form.** Let `aⱼ = e^{itⱼ}` be pairwise distinct. If
`∑ⱼ cⱼ cot((θ - tⱼ)/2) = 0` for every `θ ∈ S`, no `θ ∈ S` is a pole, and `{e^{iθ} : θ ∈ S}` is
infinite, then all `cⱼ` vanish. -/
theorem residue_scalar {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ι → ℝ)
    (ht : Function.Injective fun j => exp ((t j : ℂ) * I))
    (c : ι → ℂ) (S : Set ℝ) (hS : ((fun θ : ℝ => exp ((θ : ℂ) * I)) '' S).Infinite)
    (hpole : ∀ θ ∈ S, ∀ j, Real.sin ((θ - t j) / 2) ≠ 0)
    (hsum : ∀ θ ∈ S, ∑ j, c j * (Real.cot ((θ - t j) / 2) : ℂ) = 0) :
    ∀ j, c j = 0 := by
  set a : ι → ℂ := fun j => exp ((t j : ℂ) * I) with ha
  set P : ℂ[X] := ∑ j, C (c j) * (X + C (a j)) * ∏ k ∈ Finset.univ.erase j, (X - C (a k)) with hP
  have hroot : ∀ θ ∈ S, P.eval (exp ((θ : ℂ) * I)) = 0 := by
    intro θ hθ
    set u := exp ((θ : ℂ) * I) with hu_def
    have hu : ∀ k, u - a k ≠ 0 := fun k => exp_ne_exp_of_sin_ne_zero (hpole θ hθ k)
    have key : ∀ j, c j * (u + a j) * ∏ k ∈ Finset.univ.erase j, (u - a k)
        = (-I * ∏ k, (u - a k)) * (c j * (Real.cot ((θ - t j) / 2) : ℂ)) := by
      intro j
      have hc : (Real.cot ((θ - t j) / 2) : ℂ) * (u - a j) = I * (u + a j) := by
        rw [cot_half_sub (hpole θ hθ j)]
        exact div_mul_cancel₀ _ (hu j)
      have hI : I * I = -1 := Complex.I_mul_I
      have e : u + a j = -I * ((Real.cot ((θ - t j) / 2) : ℂ) * (u - a j)) := by
        rw [hc]; linear_combination (u + a j) * hI
      rw [e, ← Finset.mul_prod_erase Finset.univ (fun k => u - a k) (Finset.mem_univ j)]
      ring
    simp only [hP, eval_finsetSum, eval_mul, eval_C, eval_add, eval_X, eval_prod, eval_sub]
    rw [Finset.sum_congr rfl (fun j _ => key j), ← Finset.mul_sum, hsum θ hθ, mul_zero]
  have hP0 : P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono _ hS
    rintro _ ⟨θ, hθ, rfl⟩
    exact hroot θ hθ
  intro j
  have hev : P.eval (a j) = c j * (2 * a j) * ∏ k ∈ Finset.univ.erase j, (a j - a k) := by
    simp only [hP, eval_finsetSum, eval_mul, eval_C, eval_add, eval_X, eval_prod, eval_sub]
    rw [Finset.sum_eq_single j]
    · ring
    · intro i _ hij
      rw [Finset.prod_eq_zero (Finset.mem_erase.2 ⟨Ne.symm hij, Finset.mem_univ j⟩) (sub_self _),
        mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [hP0, eval_zero] at hev
  have h2 : (2 * a j) ≠ 0 := mul_ne_zero two_ne_zero (Complex.exp_ne_zero _)
  have h3 : ∏ k ∈ Finset.univ.erase j, (a j - a k) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro k hk
    exact sub_ne_zero.2 (fun h => (Finset.mem_erase.1 hk).1 (ht h).symm)
  rcases mul_eq_zero.1 hev.symm with h | h
  · rcases mul_eq_zero.1 h with h' | h'
    · exact h'
    · exact absurd h' h2
  · exact absurd h h3

/-- **Lemma 4.1 (residue lemma), vector form**: coefficients in any complex vector space
(in particular `Matrix ι ι ℂ`). -/
theorem residue_lemma {V : Type*} [AddCommGroup V] [Module ℂ V] {ι : Type*} [Fintype ι]
    (t : ι → ℝ) (ht : Function.Injective fun j => exp ((t j : ℂ) * I))
    (J : ι → V) (S : Set ℝ) (hS : ((fun θ : ℝ => exp ((θ : ℂ) * I)) '' S).Infinite)
    (hpole : ∀ θ ∈ S, ∀ j, Real.sin ((θ - t j) / 2) ≠ 0)
    (hsum : ∀ θ ∈ S, ∑ j, (Real.cot ((θ - t j) / 2) : ℂ) • J j = 0) :
    ∀ j, J j = 0 := by
  classical
  intro j
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ (J j)]
  intro φ
  refine residue_scalar t ht (fun j => φ (J j)) S hS hpole (fun θ hθ => ?_) j
  have h := congrArg φ (hsum θ hθ)
  rw [map_sum, map_zero] at h
  simpa [mul_comm] using h

/-- The image of a nondegenerate interval under `θ ↦ e^{iθ}` is infinite. -/
lemma image_exp_Ioo_infinite {a b : ℝ} (hab : a < b) :
    ((fun θ : ℝ => exp ((θ : ℂ) * I)) '' Set.Ioo a b).Infinite := by
  set b' := min b (a + Real.pi) with hb'
  have hab' : a < b' := lt_min hab (by linarith [Real.pi_pos])
  have hsub : Set.Ioo a b' ⊆ Set.Ioo a b := Set.Ioo_subset_Ioo_right (min_le_left _ _)
  refine Set.Infinite.mono (Set.image_mono hsub) ?_
  refine (Set.Ioo_infinite hab').image ?_
  intro x hx y hy hxy
  obtain ⟨n, hn'⟩ := (exp_mul_I_eq_iff x y).1 hxy
  have hxb : x < a + Real.pi := lt_of_lt_of_le hx.2 (min_le_right _ _)
  have hyb : y < a + Real.pi := lt_of_lt_of_le hy.2 (min_le_right _ _)
  have h0 : (n : ℝ) = 0 := by
    have hlt : |(n : ℝ)| * (2 * Real.pi) < 2 * Real.pi := by
      have : |x - y| < Real.pi := by
        rw [abs_lt]; constructor <;> linarith [hx.1, hy.1]
      have e : x - y = n * (2 * Real.pi) := by linarith
      rw [e, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at this
      linarith [Real.pi_pos]
    have h1 : |(n : ℝ)| < 1 := by
      have hp : (0:ℝ) < 2 * Real.pi := by positivity
      nlinarith
    have h2 : |n| < 1 := by exact_mod_cast h1
    have : n = 0 := by rw [abs_lt] at h2; omega
    simp [this]
  rw [hn', h0]; ring

/-- **Lemma 4.1 exactly as stated in the paper.** Let `t₀, …, t_{n-1}` be pairwise distinct modulo
`2π` and `Jⱼ ∈ M_M(ℂ)`. If `∑ⱼ Jⱼ cot((θ - tⱼ)/2) = 0` for all `θ` in a nonempty open interval
`(a, b)` contained in `ℝ ∖ ⋃ⱼ (tⱼ + 2πℤ)`, then all `Jⱼ = 0`. -/
theorem residue_lemma_paper {κ : Type*} [Fintype κ] {ι : Type*} (t : κ → ℝ)
    (ht : ∀ i j, i ≠ j → ∀ n : ℤ, t i ≠ t j + n * (2 * Real.pi))
    (J : κ → Matrix ι ι ℂ) {a b : ℝ} (hab : a < b)
    (hI : ∀ θ ∈ Set.Ioo a b, ∀ j, ∀ n : ℤ, θ ≠ t j + n * (2 * Real.pi))
    (hsum : ∀ θ ∈ Set.Ioo a b, ∑ j, (Real.cot ((θ - t j) / 2) : ℂ) • J j = 0) :
    ∀ j, J j = 0 := by
  classical
  refine residue_lemma t ?_ J (Set.Ioo a b) (image_exp_Ioo_infinite hab)
    (fun θ hθ j => (sin_half_sub_ne_zero_iff θ (t j)).2 (hI θ hθ j)) hsum
  intro i j hij
  by_contra hne
  obtain ⟨n, hn⟩ := (exp_mul_I_eq_iff (t i) (t j)).1 hij
  exact ht i j hne n hn

/-! ## The logarithmic form -/

lemma hasDerivAt_log_sin_half {θ t : ℝ} (h : Real.sin ((θ - t) / 2) ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.log |Real.sin ((x - t) / 2)|) (Real.cot ((θ - t) / 2) / 2) θ := by
  simp_rw [Real.log_abs]
  have h1 : HasDerivAt (fun x : ℝ => (x - t) / 2) (1 / 2) θ :=
    ((hasDerivAt_id θ).sub_const t).div_const 2
  have h2 := (h1.sin).log h
  convert h2 using 1
  rw [Real.cot_eq_cos_div_sin]
  ring

/-- If `∑ⱼ log|sin((θ - tⱼ)/2)| • cⱼ = 0` on a nondegenerate open interval without poles and the
`e^{itⱼ}` are pairwise distinct, then all `cⱼ = 0` (differentiate, then Lemma 4.1). -/
theorem log_residue {V : Type*} [AddCommGroup V] [Module ℂ V] {ι : Type*} [Fintype ι]
    (t : ι → ℝ) (ht : Function.Injective fun j => exp ((t j : ℂ) * I))
    (c : ι → V) {a b : ℝ} (hab : a < b)
    (hpole : ∀ θ ∈ Set.Ioo a b, ∀ j, Real.sin ((θ - t j) / 2) ≠ 0)
    (hzero : ∀ θ ∈ Set.Ioo a b, ∑ j, ((Real.log |Real.sin ((θ - t j) / 2)| : ℝ) : ℂ) • c j = 0) :
    ∀ j, c j = 0 := by
  classical
  intro j
  rw [← Module.forall_dual_apply_eq_zero_iff ℂ (c j)]
  intro φ
  refine residue_scalar t ht (fun j => φ (c j)) (Set.Ioo a b) (image_exp_Ioo_infinite hab) hpole
    (fun θ hθ => ?_) j
  set F : ℝ → ℂ := fun x => ∑ j, ((Real.log |Real.sin ((x - t j) / 2)| : ℝ) : ℂ) * φ (c j) with hF
  have hF0 : ∀ x ∈ Set.Ioo a b, F x = 0 := by
    intro x hx
    have h := congrArg φ (hzero x hx)
    rw [map_sum, map_zero] at h
    simpa [hF] using h
  have hd1 : HasDerivAt F 0 θ := by
    have hev : F =ᶠ[nhds θ] fun _ => (0 : ℂ) :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hθ) hF0
    exact (hasDerivAt_const θ (0 : ℂ)).congr_of_eventuallyEq hev
  have hd2 : HasDerivAt F (∑ j, ((Real.cot ((θ - t j) / 2) / 2 : ℝ) : ℂ) * φ (c j)) θ := by
    apply HasDerivAt.fun_sum
    intro j _
    exact ((hasDerivAt_log_sin_half (hpole θ hθ j)).ofReal_comp).mul_const _
  have h := hd2.unique hd1
  have h' : ∑ j, φ (c j) * (Real.cot ((θ - t j) / 2) : ℂ)
      = 2 * ∑ j, ((Real.cot ((θ - t j) / 2) / 2 : ℝ) : ℂ) * φ (c j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast; ring
  rw [h', h, mul_zero]

/-! ## Cell geometry of a cell vector with all cells positive (sections 1.5 and 3.1) -/

section Cells

variable {d : ℕ} [NeZero d]

/-- Periodic extension of the cell lengths: `ℓ_x := ℓ_{x mod d}` (`x : ℕ`). -/
def cellLen (ell : Fin d → ℝ) (x : ℕ) : ℝ := ell ⟨x % d, Nat.mod_lt _ (NeZero.pos d)⟩

/-- Left endpoints `L_x = ℓ_0 + ⋯ + ℓ_{x-1}` of the cells `I_x = [L_x, L_{x+1})`. -/
def cellL (ell : Fin d → ℝ) (x : ℕ) : ℝ := ∑ i ∈ Finset.range x, cellLen ell i

/-- Angular endpoints `t_x = 2π L_x / N`, `N = 4d` (the map `ξ ↦ 2πξ/N` of section 3.1). -/
noncomputable def cellT (ell : Fin d → ℝ) (x : ℕ) : ℝ := 2 * Real.pi * cellL ell x / (4 * d)

lemma cellL_succ (ell : Fin d → ℝ) (x : ℕ) : cellL ell (x + 1) = cellL ell x + cellLen ell x :=
  Finset.sum_range_succ _ _

lemma cellL_zero (ell : Fin d → ℝ) : cellL ell 0 = 0 := by simp [cellL]

lemma cellL_strictMono {ell : Fin d → ℝ} (hpos : ∀ r, 0 < ell r) : StrictMono (cellL ell) :=
  strictMono_nat_of_lt_succ fun x => by
    have h := hpos ⟨x % d, Nat.mod_lt _ (NeZero.pos d)⟩
    rw [cellL_succ]
    simp only [cellLen]
    linarith

lemma cellL_mul (ell : Fin d → ℝ) (m : ℕ) : cellL ell (m * d) = m * ∑ r, ell r := by
  induction m with
  | zero => simp [cellL]
  | succ m ih =>
    have h : ∑ i ∈ Finset.range d, cellLen ell (m * d + i) = ∑ r, ell r := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => cellLen ell (m * d + i)) d]
      refine Finset.sum_congr rfl fun r _ => ?_
      simp only [cellLen]
      congr 1
      ext
      simp [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt r.isLt]
    rw [Nat.succ_mul, cellL, Finset.sum_range_add, ← cellL, ih, h]
    push_cast; ring

lemma cellL_N {ell : Fin d → ℝ} (hsum : ∑ r, ell r = d) : cellL ell (4 * d) = 4 * d := by
  rw [cellL_mul, hsum]; push_cast; ring

lemma four_d_pos : (0 : ℝ) < 4 * d := by
  have : (0 : ℝ) < d := Nat.cast_pos.2 (NeZero.pos d)
  linarith

lemma cellT_strictMono {ell : Fin d → ℝ} (hpos : ∀ r, 0 < ell r) : StrictMono (cellT ell) := by
  intro x y hxy
  have h := cellL_strictMono hpos hxy
  unfold cellT
  rw [div_lt_div_iff_of_pos_right four_d_pos]
  nlinarith [Real.pi_pos]

lemma cellT_zero (ell : Fin d → ℝ) : cellT ell 0 = 0 := by simp [cellT, cellL_zero]

lemma cellT_N {ell : Fin d → ℝ} (hsum : ∑ r, ell r = d) : cellT ell (4 * d) = 2 * Real.pi := by
  unfold cellT
  rw [cellL_N hsum]
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  field_simp

lemma cellT_nonneg {ell : Fin d → ℝ} (hpos : ∀ r, 0 < ell r) (j : ℕ) : 0 ≤ cellT ell j := by
  rw [← cellT_zero ell]; exact (cellT_strictMono hpos).monotone (Nat.zero_le j)

lemma cellT_lt_two_pi {ell : Fin d → ℝ} (hpos : ∀ r, 0 < ell r) (hsum : ∑ r, ell r = d) {j : ℕ}
    (hj : j < 4 * d) : cellT ell j < 2 * Real.pi := by
  rw [← cellT_N hsum]; exact cellT_strictMono hpos hj

/-- No point of an open arc `J_x = (t_x, t_{x+1})` is a pole: `sin((θ - t_j)/2) ≠ 0` for all `j`. -/
lemma sin_ne_zero_of_mem_arc {ell : Fin d → ℝ} (hpos : ∀ r, 0 < ell r) (hsum : ∑ r, ell r = d)
    {x j : ℕ} (hx : x < 4 * d) (hj : j < 4 * d) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (cellT ell x) (cellT ell (x + 1))) :
    Real.sin ((θ - cellT ell j) / 2) ≠ 0 := by
  have hmono := cellT_strictMono hpos
  have htj0 := cellT_nonneg hpos j
  have htjN := cellT_lt_two_pi hpos hsum hj
  have htx0 := cellT_nonneg hpos x
  have htx1 : cellT ell (x + 1) ≤ 2 * Real.pi := by
    rw [← cellT_N hsum]; exact hmono.monotone (by omega)
  have hne : θ ≠ cellT ell j := by
    intro heq
    rcases Nat.lt_or_ge x j with h | h
    · have : cellT ell (x + 1) ≤ cellT ell j := hmono.monotone (by omega)
      linarith [hθ.2]
    · have : cellT ell j ≤ cellT ell x := hmono.monotone h
      linarith [hθ.1]
  have hy1 : -Real.pi < (θ - cellT ell j) / 2 := by linarith [hθ.1]
  have hy2 : (θ - cellT ell j) / 2 < Real.pi := by linarith [hθ.2]
  have hy0 : (θ - cellT ell j) / 2 ≠ 0 := by
    intro h; apply hne; linarith
  rcases lt_or_gt_of_ne hy0 with h | h
  · have := Real.sin_pos_of_pos_of_lt_pi (neg_pos.2 h) (by linarith)
    rw [Real.sin_neg] at this
    linarith
  · exact (Real.sin_pos_of_pos_of_lt_pi h hy2).ne'

/-- The cell endpoints are pairwise distinct modulo `2π`. -/
lemma cellT_exp_injective {ell : Fin d → ℝ} (hpos : ∀ r, 0 < ell r) (hsum : ∑ r, ell r = d) :
    Function.Injective fun j : ZMod (4 * d) => exp ((cellT ell j.val : ℂ) * I) := by
  intro i j hij
  obtain ⟨n, hn⟩ := (exp_mul_I_eq_iff _ _).1 hij
  have hi0 := cellT_nonneg hpos i.val
  have hj0 := cellT_nonneg hpos j.val
  have hi1 := cellT_lt_two_pi hpos hsum (ZMod.val_lt i)
  have hj1 := cellT_lt_two_pi hpos hsum (ZMod.val_lt j)
  have hn0 : (n : ℝ) = 0 := by
    have hp : (0 : ℝ) < 2 * Real.pi := by positivity
    have h1 : (n : ℝ) * (2 * Real.pi) < 2 * Real.pi := by linarith
    have h2 : -(2 * Real.pi) < (n : ℝ) * (2 * Real.pi) := by linarith
    have h3 : (n : ℝ) < 1 := by nlinarith
    have h4 : -1 < (n : ℝ) := by nlinarith
    have h5 : n < 1 := by exact_mod_cast h3
    have h6 : -1 < n := by exact_mod_cast h4
    have : n = 0 := by omega
    simp [this]
  rw [hn0, zero_mul, add_zero] at hn
  exact ZMod.val_injective _ ((cellT_strictMono hpos).injective hn)

/-- The open arc `J_x` is contained in `(0, 2π)`. -/
lemma arc_subset {ell : Fin d → ℝ} (hpos : ∀ r, 0 < ell r) (hsum : ∑ r, ell r = d) {x : ℕ}
    (hx : x < 4 * d) :
    Set.Ioo (cellT ell x) (cellT ell (x + 1)) ⊆ Set.Ioo 0 (2 * Real.pi) := by
  apply Set.Ioo_subset_Ioo (cellT_nonneg hpos x)
  rw [← cellT_N hsum]
  exact (cellT_strictMono hpos).monotone (by omega)

end Cells

/-! ## The step field, its conjugate function, and Proposition 4.2 -/

section Fields

variable {d : ℕ} [NeZero d] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The explicit conjugate function (3.1) of the step field `θ ↦ B_x` (`θ ∈ [t_x, t_{x+1})`):
`g(θ) = (1/π) ∑_{j ∈ ℤ_N} (B_j - B_{j-1}) log|sin((θ - t_j)/2)|`. -/
noncomputable def conjField (ell : Fin d → ℝ) (B : ZMod (4 * d) → Matrix ι ι ℂ)
    (θ : ℝ) : Matrix ι ι ℂ :=
  ∑ j : ZMod (4 * d),
    ((Real.log |Real.sin ((θ - cellT ell j.val) / 2)| / Real.pi : ℝ) : ℂ) • (B j - B (j - 1))

/-- The step field: `B(θ) = B_x` for `θ ∈ [t_x, t_{x+1})`, `x ∈ ℤ_N` (and `0` outside `[0, 2π)`). -/
noncomputable def stepField (ell : Fin d → ℝ) (B : ZMod (4 * d) → Matrix ι ι ℂ)
    (θ : ℝ) : Matrix ι ι ℂ :=
  ∑ x : ZMod (4 * d), (Set.Ico (cellT ell x.val) (cellT ell (x.val + 1))).indicator (fun _ => B x) θ

lemma stepField_eq {ell : Fin d → ℝ} (hpos : ∀ r, 0 < ell r)
    (B : ZMod (4 * d) → Matrix ι ι ℂ) (x : ZMod (4 * d)) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (cellT ell x.val) (cellT ell (x.val + 1))) : stepField ell B θ = B x := by
  have hmono := cellT_strictMono hpos
  unfold stepField
  rw [Finset.sum_eq_single x]
  · exact Set.indicator_of_mem (Set.Ioo_subset_Ico_self hθ) _
  · intro y _ hyx
    apply Set.indicator_of_notMem
    intro hy
    apply hyx
    apply ZMod.val_injective
    have h1 : y.val < x.val + 1 := hmono.lt_iff_lt.1 (lt_of_le_of_lt hy.1 hθ.2)
    have h2 : x.val < y.val + 1 := hmono.lt_iff_lt.1 (lt_of_lt_of_le hθ.1 hy.2.le)
    omega
  · intro h; exact absurd (Finset.mem_univ x) h

lemma continuousOn_conjField {ell : Fin d → ℝ} (hpos : ∀ r, 0 < ell r) (hsum : ∑ r, ell r = d)
    (B : ZMod (4 * d) → Matrix ι ι ℂ) (x : ZMod (4 * d)) :
    ContinuousOn (conjField ell B) (Set.Ioo (cellT ell x.val) (cellT ell (x.val + 1))) := by
  unfold conjField
  apply continuousOn_finsetSum
  intro j _
  refine ContinuousOn.fun_smul ?_ continuousOn_const
  intro θ hθ
  apply ContinuousAt.continuousWithinAt
  have h := (hasDerivAt_log_sin_half
    (sin_ne_zero_of_mem_arc hpos hsum (ZMod.val_lt x) (ZMod.val_lt j) hθ)).continuousAt
  exact Complex.continuous_ofReal.continuousAt.comp (h.div_const _)

/-- **Proposition 4.2.** Let `ℓ` be a cell vector with all cells positive (`ℓ_r > 0`,
`∑ ℓ_r = d`) and `B : ℤ_N → M_M(ℂ)`. If the step field commutes with its conjugate function (3.1)
for almost every `θ ∈ (0, 2π)`, then all `B_x` commute pairwise. -/
theorem commute_of_ae_commute {ell : Fin d → ℝ} (hpos : ∀ r, 0 < ell r) (hsum : ∑ r, ell r = d)
    (B : ZMod (4 * d) → Matrix ι ι ℂ)
    (hae : ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (2 * Real.pi))),
      stepField ell B θ * conjField ell B θ = conjField ell B θ * stepField ell B θ) :
    ∀ x y, B x * B y = B y * B x := by
  intro x
  set J := Set.Ioo (cellT ell x.val) (cellT ell (x.val + 1)) with hJdef
  have hJsub : J ⊆ Set.Ioo 0 (2 * Real.pi) := arc_subset hpos hsum (ZMod.val_lt x)
  have hJ : ∀ θ ∈ J, B x * conjField ell B θ = conjField ell B θ * B x := by
    have hae' : ∀ᵐ θ ∂(volume.restrict J), B x * conjField ell B θ = conjField ell B θ * B x := by
      have h1 := ae_restrict_of_ae_restrict_of_subset hJsub hae
      filter_upwards [h1, ae_restrict_mem measurableSet_Ioo] with θ h hθ
      rwa [stepField_eq hpos B x hθ] at h
    have hg := continuousOn_conjField hpos hsum B x
    exact Measure.eqOn_open_of_ae_eq hae' isOpen_Ioo (continuousOn_const.mul hg)
      (hg.mul continuousOn_const)
  -- the commutator `[B_x, g(θ)]` is a combination of the functions `log|sin((θ - t_j)/2)|`
  have hc : ∀ θ ∈ J, ∑ j : ZMod (4 * d),
      ((Real.log |Real.sin ((θ - cellT ell j.val) / 2)| : ℝ) : ℂ) •
        ((Real.pi : ℂ)⁻¹ • (B x * (B j - B (j - 1)) - (B j - B (j - 1)) * B x)) = 0 := by
    intro θ hθ
    have e : ∑ j : ZMod (4 * d),
        ((Real.log |Real.sin ((θ - cellT ell j.val) / 2)| : ℝ) : ℂ) •
          ((Real.pi : ℂ)⁻¹ • (B x * (B j - B (j - 1)) - (B j - B (j - 1)) * B x))
        = B x * conjField ell B θ - conjField ell B θ * B x := by
      simp only [conjField, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
        Matrix.mul_smul, Matrix.smul_mul, smul_smul, ← smul_sub]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      push_cast
      ring
    rw [e, hJ θ hθ, sub_self]
  have hab : cellT ell x.val < cellT ell (x.val + 1) := cellT_strictMono hpos (Nat.lt_succ_self _)
  have hjump := log_residue (fun j : ZMod (4 * d) => cellT ell j.val)
    (cellT_exp_injective hpos hsum) _ hab
    (fun θ hθ j => sin_ne_zero_of_mem_arc hpos hsum (ZMod.val_lt x) (ZMod.val_lt j) hθ) hc
  have hpi : (Real.pi : ℂ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  have hstep : ∀ j : ZMod (4 * d),
      B x * B j - B j * B x = B x * B (j - 1) - B (j - 1) * B x := by
    intro j
    have h := (smul_eq_zero.1 (hjump j)).resolve_left hpi
    rw [mul_sub, sub_mul] at h
    rw [← sub_eq_zero, ← h]
    abel
  have hk : ∀ k : ℕ, B x * B (x + k) - B (x + k) * B x = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [hstep, show x + ((k + 1 : ℕ) : ZMod (4 * d)) - 1 = x + (k : ZMod (4 * d)) by
        push_cast; ring, ih]
  intro y
  have h := hk (y - x).val
  rw [ZMod.natCast_zmod_val, add_sub_cancel] at h
  exact sub_eq_zero.1 h

end Fields

end OQP27
