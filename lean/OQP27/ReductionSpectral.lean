import OQP27.ReductionClock

/-!
# OQP 27B, module L2 (reduction), part 6: spectral projective measurements of unitaries of finite order

For a unitary `R` with `R^n = 1` and a primitive `n`-th root of unity `ζ`, the matrices
`P_a = (1/n) ∑_{t ∈ ℤ/n} ζ^{-a t} R^t` (`a ∈ ℤ/n`) form a projective measurement with
`∑_a ζ^a P_a = R` (explicit functional calculus; no spectral theorem is used).
This realises any four unitaries `R_1, …, R_4` with `R_i^d = 1` as a projective strategy on the maximally
entangled state ("conversely, any four unitaries … come from a projective strategy", paper Section 2.2).

Main results (all PROVED, no hypotheses):
* `OQP27.Red.sum_chi_mul`: orthogonality of the characters `x ↦ ζ^x` of `ℤ/n`.
* `OQP27.Red.genSpec_mul`, `OQP27.Red.sum_genSpec`, `OQP27.Red.sum_chi_smul_genSpec`,
  `OQP27.Red.genSpec_isHermitian`.
* `OQP27.Red.specPVM_isPVM`, `OQP27.Red.pvmU_specPVM`: `P_a` (with `ζ = w = e^{2πi/d}`) is a PVM whose
  unitary `∑_a w^a P_a` is `R`.
-/

namespace OQP27.Red

open Complex Finset ComplexConjugate Matrix

noncomputable section

/-! ### Characters of `ℤ/n` -/

section Characters

variable {n : ℕ} [NeZero n]

/-- The character `χ(x) = ζ^x` of `ℤ/n` (for `ζ^n = 1`). -/
def chi (ζ : ℂ) (x : ZMod n) : ℂ := ζ ^ x.val

variable {ζ : ℂ}

omit [NeZero n] in
lemma pow_mod_of_pow_eq_one (hζ : ζ ^ n = 1) (k : ℕ) : ζ ^ (k % n) = ζ ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k n, pow_add, pow_mul, hζ, one_pow, mul_one]

lemma chi_add (hζ : ζ ^ n = 1) (x y : ZMod n) : chi ζ (x + y) = chi ζ x * chi ζ y := by
  rw [chi, chi, chi, ZMod.val_add, pow_mod_of_pow_eq_one hζ, pow_add]

omit [NeZero n] in
lemma chi_zero : chi ζ (0 : ZMod n) = 1 := by simp [chi]

lemma chi_neg (hζ : ζ ^ n = 1) (x : ZMod n) : chi ζ (-x) = (chi ζ x)⁻¹ := by
  have h := chi_add hζ x (-x)
  rw [add_neg_cancel, chi_zero] at h
  exact (inv_eq_of_mul_eq_one_right h.symm).symm

lemma chi_ne_one (hprim : IsPrimitiveRoot ζ n) {x : ZMod n} (hx : x ≠ 0) : chi ζ x ≠ 1 :=
  hprim.pow_ne_one_of_pos_of_lt (by rwa [Ne, ZMod.val_eq_zero]) (ZMod.val_lt x)

/-- Orthogonality: `∑_t ζ^{c t} = n [c = 0]`. -/
lemma sum_chi_mul (hprim : IsPrimitiveRoot ζ n) (c : ZMod n) :
    ∑ t : ZMod n, chi ζ (c * t) = if c = 0 then (n : ℂ) else 0 := by
  have hζ : ζ ^ n = 1 := hprim.pow_eq_one
  split_ifs with hc
  · subst hc
    simp [chi_zero, ZMod.card]
  · have key : chi ζ c * ∑ t : ZMod n, chi ζ (c * t) = ∑ t : ZMod n, chi ζ (c * t) := by
      rw [mul_sum]
      have e : ∀ t : ZMod n, chi ζ c * chi ζ (c * t) = chi ζ (c * (t + 1)) := by
        intro t
        rw [← chi_add hζ]
        ring_nf
      simp_rw [e]
      exact Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun t => rfl)
    have h1 : (chi ζ c - 1) * ∑ t : ZMod n, chi ζ (c * t) = 0 := by
      rw [sub_mul, key, one_mul, sub_self]
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (sub_eq_zero.1 h) (chi_ne_one hprim hc)
    · exact h

end Characters

/-! ### Spectral projections of a unitary of order dividing `n` -/

section GenSpec

variable {n : ℕ} [NeZero n] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- `P_a = (1/n) ∑_{t ∈ ℤ/n} ζ^{-a t} E^t`, the spectral projection of `E` (`E^n = 1`) for the
eigenvalue `ζ^a`. -/
def genSpec (ζ : ℂ) (E : Matrix κ κ ℂ) (a : ZMod n) : Matrix κ κ ℂ :=
  (1 / (n : ℂ)) • ∑ t : ZMod n, chi ζ (-(a * t)) • E ^ t.val

variable {ζ : ℂ} {E : Matrix κ κ ℂ}

omit [NeZero n] in
lemma pow_mod_n (hE : E ^ n = 1) (k : ℕ) : E ^ (k % n) = E ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k n, pow_add, pow_mul, hE, one_pow, mul_one]

lemma pow_val_add_n (hE : E ^ n = 1) (s t : ZMod n) : E ^ (s + t).val = E ^ s.val * E ^ t.val := by
  rw [ZMod.val_add, pow_mod_n hE, pow_add]

lemma genSpec_mul (hprim : IsPrimitiveRoot ζ n) (hE : E ^ n = 1) (a b : ZMod n) :
    genSpec ζ E a * genSpec ζ E b = if a = b then genSpec ζ E a else 0 := by
  have hζ : ζ ^ n = 1 := hprim.pow_eq_one
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  unfold genSpec
  rw [smul_mul_smul_comm, Finset.sum_mul_sum]
  simp_rw [smul_mul_smul_comm, ← pow_val_add_n hE]
  have e1 : ∀ s : ZMod n, ∑ t : ZMod n, (chi ζ (-(a * s)) * chi ζ (-(b * t))) • E ^ (s + t).val
      = ∑ u : ZMod n, (chi ζ (-(b * u)) * chi ζ ((b - a) * s)) • E ^ u.val := by
    intro s
    refine Fintype.sum_equiv (Equiv.addLeft s) _ _ (fun t => ?_)
    simp only [Equiv.coe_addLeft]
    congr 1
    rw [← chi_add hζ, ← chi_add hζ]
    congr 1
    ring
  simp_rw [e1]
  rw [sum_comm]
  simp_rw [← sum_smul, ← mul_sum, sum_chi_mul hprim, sub_eq_zero]
  split_ifs with h1 h2 h2
  · subst h1
    rw [smul_sum, smul_sum]
    refine sum_congr rfl fun u _ => ?_
    rw [smul_smul, smul_smul]
    congr 1
    field_simp
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · simp

lemma genSpec_sq (hprim : IsPrimitiveRoot ζ n) (hE : E ^ n = 1) (a : ZMod n) :
    genSpec ζ E a * genSpec ζ E a = genSpec ζ E a := by
  rw [genSpec_mul hprim hE, if_pos rfl]

lemma genSpec_orth (hprim : IsPrimitiveRoot ζ n) (hE : E ^ n = 1) {a b : ZMod n} (hab : a ≠ b) :
    genSpec ζ E a * genSpec ζ E b = 0 := by
  rw [genSpec_mul hprim hE, if_neg hab]

lemma sum_genSpec (hprim : IsPrimitiveRoot ζ n) (E : Matrix κ κ ℂ) :
    ∑ a : ZMod n, genSpec ζ E a = 1 := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  unfold genSpec
  rw [← smul_sum, sum_comm]
  simp_rw [← sum_smul]
  have e : ∀ t : ZMod n, ∑ a : ZMod n, chi ζ (-(a * t)) = if t = 0 then (n : ℂ) else 0 := by
    intro t
    calc ∑ a : ZMod n, chi ζ (-(a * t)) = ∑ a : ZMod n, chi ζ (-t * a) :=
          sum_congr rfl fun a _ => by congr 1; ring
      _ = if -t = 0 then (n : ℂ) else 0 := sum_chi_mul hprim (-t)
      _ = if t = 0 then (n : ℂ) else 0 := by simp only [neg_eq_zero]
  simp_rw [e]
  rw [sum_eq_single (0 : ZMod n)]
  · simp only [if_true, ZMod.val_zero, pow_zero, smul_smul]
    rw [one_div, inv_mul_cancel₀ hn, one_smul]
  · intro t _ ht
    rw [if_neg ht, zero_smul]
  · intro h
    exact absurd (mem_univ _) h

lemma sum_chi_smul_genSpec (hprim : IsPrimitiveRoot ζ n) (E : Matrix κ κ ℂ) :
    ∑ a : ZMod n, chi ζ a • genSpec ζ E a = E ^ (1 : ZMod n).val := by
  have hζ : ζ ^ n = 1 := hprim.pow_eq_one
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne n)
  unfold genSpec
  have h1 : ∀ a : ZMod n, chi ζ a • ((1 / (n : ℂ)) • ∑ t : ZMod n, chi ζ (-(a * t)) • E ^ t.val)
      = ∑ t : ZMod n, (1 / (n : ℂ) * chi ζ ((1 - t) * a)) • E ^ t.val := by
    intro a
    rw [smul_sum, smul_sum]
    refine sum_congr rfl fun t _ => ?_
    rw [smul_smul, smul_smul]
    congr 1
    rw [mul_comm (chi ζ a), mul_assoc, ← chi_add hζ]
    congr 2
    ring
  rw [sum_congr rfl fun a _ => h1 a, sum_comm]
  simp_rw [← sum_smul, ← mul_sum, sum_chi_mul hprim, sub_eq_zero]
  rw [sum_eq_single (1 : ZMod n)]
  · rw [if_pos rfl, one_div, inv_mul_cancel₀ hn, one_smul]
  · intro t _ ht
    rw [if_neg (Ne.symm ht), mul_zero, zero_smul]
  · intro h
    exact absurd (mem_univ _) h

lemma genSpec_isHermitian (hprim : IsPrimitiveRoot ζ n) (hE : E ^ n = 1) (hU : IsUnitaryM E)
    (a : ZMod n) : (genSpec ζ E a).IsHermitian := by
  have hζ : ζ ^ n = 1 := hprim.pow_eq_one
  -- `(E^t)ᴴ = E^{(-t)}`
  have hEt : ∀ t : ZMod n, (E ^ t.val)ᴴ = E ^ (-t).val := by
    intro t
    have h1 : E ^ (-t).val * E ^ t.val = 1 := by
      rw [← pow_val_add_n hE, neg_add_cancel, ZMod.val_zero, pow_zero]
    have h2 : E ^ t.val * (E ^ t.val)ᴴ = 1 := hU.pow_mul_conjTranspose_pow t.val
    calc (E ^ t.val)ᴴ = (E ^ (-t).val * E ^ t.val) * (E ^ t.val)ᴴ := by rw [h1, one_mul]
      _ = E ^ (-t).val := by rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  -- conjugate of the character
  have hconj : ∀ x : ZMod n, star (chi ζ x) = chi ζ (-x) := by
    intro x
    have hz : ‖ζ‖ = 1 := by
      have := congrArg (fun z => ‖z‖) hζ
      simp only [norm_pow, norm_one] at this
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne n)).1 this
    rw [chi_neg hζ, chi, Complex.star_def, map_pow, ← inv_pow]
    congr 1
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hz]
    simp
  unfold Matrix.IsHermitian genSpec
  rw [conjTranspose_smul, conjTranspose_sum]
  simp_rw [conjTranspose_smul, hEt, hconj]
  have hs : star (1 / (n : ℂ)) = 1 / (n : ℂ) := by simp
  rw [hs]
  congr 1
  refine Fintype.sum_equiv (Equiv.neg (ZMod n)) _ _ (fun t => ?_)
  simp only [Equiv.neg_apply, neg_neg]
  congr 2
  ring

end GenSpec

/-! ### The spectral PVM of a unitary `R` with `R^d = 1` -/

section SpecPVM

variable {d : ℕ} [NeZero d] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The spectral projective measurement of a unitary `R` with `R^d = 1`:
`P_a = (1/d) ∑_t w^{-a t} R^t`, so that `R = ∑_a w^a P_a`. -/
def specPVM (d : ℕ) [NeZero d] (R : Matrix κ κ ℂ) (a : ZMod d) : Matrix κ κ ℂ := genSpec (wd d) R a

theorem specPVM_isPVM {R : Matrix κ κ ℂ} (hU : IsUnitaryM R) (hR : R ^ d = 1) :
    IsPVM (specPVM d R) :=
  ⟨fun a => ⟨genSpec_isHermitian (wd_prim (NeZero.ne d)) hR hU a,
    genSpec_sq (wd_prim (NeZero.ne d)) hR a⟩, sum_genSpec (wd_prim (NeZero.ne d)) R⟩

/-- The unitary of the spectral PVM of `R` is `R`. -/
theorem pvmU_specPVM {R : Matrix κ κ ℂ} (hR : R ^ d = 1) : pvmU (specPVM d R) = R := by
  have h : pvmU (specPVM d R) = R ^ (1 : ZMod d).val :=
    sum_chi_smul_genSpec (κ := κ) (wd_prim (NeZero.ne d)) R
  rw [h]
  rcases Nat.lt_or_ge d 2 with hd | hd
  · -- `d = 1`: `R = R^1 = 1`
    have hd1 : d = 1 := by have := NeZero.ne d; omega
    subst hd1
    rw [pow_one] at hR
    rw [hR, one_pow]
  · have : Fact (1 < d) := ⟨by omega⟩
    rw [ZMod.val_one, pow_one]

end SpecPVM

end

end OQP27.Red
