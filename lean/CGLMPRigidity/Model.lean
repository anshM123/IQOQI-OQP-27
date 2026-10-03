import CGLMPRigidity.Links

/-!
# Non-vacuity of `rigidity`: the canonical DKZ model satisfies its hypotheses

For every `d ≥ 1`, in `Matrix (Fin d) (Fin d) ℂ` let `X` be the cyclic shift `|j⟩ ↦ |j + 1⟩`,
`Π = |0⟩⟨0|`, `D = 1 - (1 + i) Π`, `z = exp (i π / (2 d))` (so `z ^ d = i`), and
`R₁ = X`, `R₂ = z D R₁`, `R₃ = z D R₂`, `R₄ = z D R₃`: the canonical DKZ tuple of `RIGIDITY.md` (1.4).
`CGLMPRigidity.canonical_model` proves that this tuple satisfies every hypothesis of
`CGLMPRigidity.rigidity`, with the two-eigenvalue relations for every `n ≤ d`.
-/

set_option linter.unusedSectionVars false

namespace CGLMPRigidity

open Complex Matrix

section General

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

/-- Lemma 3.1, (iii) ⇒ (i): a quarter-phase unitary is two-valued. -/
lemma qp_two_valued {E : A} (hE : IsStarProjection E) : (qp E - 1) * (qp E - I • 1) = 0 := by
  obtain ⟨h1, -⟩ := isStarProjection_iff'.1 hE
  simp only [qp, add_sub_cancel_left, smul_mul_assoc, mul_sub, mul_add, mul_one, mul_smul_comm, h1]
  module

/-- If `T = z (D S)` with `S` unitary, then `S T⋆ = z⋆ D⋆`. -/
lemma link_of_eq {S T D : A} {z : ℂ} (hS : IsU S) (h : T = z • (D * S)) :
    S * star T = star z • star D := by
  rw [h, star_smul, star_mul, mul_smul_comm, ← mul_assoc, hS.2, one_mul]

end General

section Model

open Fin.NatCast Fin.CommRing

variable (d : ℕ) [NeZero d]

/-- The cyclic shift `|j⟩ ↦ |j + 1⟩`. -/
noncomputable def shiftM : Matrix (Fin d) (Fin d) ℂ := ∑ j : Fin d, single (j + 1) j 1

/-- The rank-one projection `|0⟩⟨0|`. -/
noncomputable def proj0 : Matrix (Fin d) (Fin d) ℂ := single 0 0 1

/-- `z = exp (i π / (2 d)) = exp (2 π i / (4 d))`. -/
noncomputable def zeta : ℂ := exp (((Real.pi / (2 * d) : ℝ) : ℂ) * I)

/-- `D = 1 - (1 + i) |0⟩⟨0|`. -/
noncomputable def Dm : Matrix (Fin d) (Fin d) ℂ := 1 - (1 + I) • proj0 d

/-- `R₂ = z D R₁`. -/
noncomputable def R2m : Matrix (Fin d) (Fin d) ℂ := zeta d • (Dm d * shiftM d)

/-- `R₃ = z D R₂`. -/
noncomputable def R3m : Matrix (Fin d) (Fin d) ℂ := zeta d • (Dm d * R2m d)

/-- `R₄ = z D R₃`. -/
noncomputable def R4m : Matrix (Fin d) (Fin d) ℂ := zeta d • (Dm d * R3m d)

variable {d}

lemma sum_shift_mul_single (i b c : Fin d) :
    (∑ a : Fin d, single (a + i) a (1 : ℂ)) * single b c 1 = single (b + i) c 1 := by
  rw [Finset.sum_mul, Finset.sum_eq_single b]
  · rw [single_mul_single_same, mul_one]
  · intro a _ hab
    simp [hab]
  · intro h
    exact absurd (Finset.mem_univ b) h

lemma single_mul_sum_shift (i b c : Fin d) :
    single b c (1 : ℂ) * (∑ a : Fin d, single a (a + i) 1) = single b (c + i) 1 := by
  rw [Finset.mul_sum, Finset.sum_eq_single c]
  · rw [single_mul_single_same, mul_one]
  · intro a _ hac
    simp [Ne.symm hac]
  · intro h
    exact absurd (Finset.mem_univ c) h

lemma single_mul_shift (b c : Fin d) : single b c (1 : ℂ) * shiftM d = single b (c - 1) 1 := by
  rw [shiftM, Finset.mul_sum, Finset.sum_eq_single (c - 1)]
  · rw [sub_add_cancel, single_mul_single_same, mul_one]
  · intro a _ ha
    apply single_mul_single_of_ne
    intro h
    apply ha
    rw [h, add_sub_cancel_right]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma shift_pow (n : ℕ) : shiftM d ^ n = ∑ a : Fin d, single (a + (n : Fin d)) a (1 : ℂ) := by
  induction n with
  | zero => simp [sum_single_one]
  | succ n ih =>
    rw [pow_succ', ih, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [shiftM, sum_shift_mul_single]
    congr 1
    push_cast
    ring

lemma star_shift_pow (n : ℕ) :
    star (shiftM d ^ n) = ∑ a : Fin d, single a (a + (n : Fin d)) (1 : ℂ) := by
  rw [shift_pow, star_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [star_eq_conjTranspose, conjTranspose_single, star_one]

lemma shift_isU : IsU (shiftM d) := by
  have e : star (shiftM d) = ∑ a : Fin d, single a (a + 1) (1 : ℂ) := by
    simpa using star_shift_pow (d := d) 1
  have h1 : star (shiftM d) * shiftM d = 1 := by
    rw [e, Finset.sum_mul]
    simp_rw [single_mul_shift, add_sub_cancel_right]
    exact sum_single_one
  exact ⟨h1, mul_eq_one_comm.1 h1⟩

lemma shift_pow_d : shiftM d ^ d = 1 := by
  rw [shift_pow, Fin.natCast_self]
  simp [sum_single_one]

lemma proj0_isStarProjection : IsStarProjection (proj0 d) := by
  rw [isStarProjection_iff']
  constructor
  · simp [proj0]
  · simp [proj0, star_eq_conjTranspose]

lemma cP_model (j : ℕ) :
    cP (shiftM d) (proj0 d) j = single (j : Fin d) (j : Fin d) (1 : ℂ) := by
  rw [cP, ← star_pow, star_shift_pow, shift_pow, proj0, sum_shift_mul_single, single_mul_sum_shift,
    zero_add]

lemma cP_model_orth (i j : ℕ) (hi : i < d) (hj : j < d) (hij : i ≠ j) :
    cP (shiftM d) (proj0 d) i * cP (shiftM d) (proj0 d) j = 0 := by
  rw [cP_model, cP_model]
  apply single_mul_single_of_ne
  intro h
  apply hij
  have := congrArg Fin.val h
  simpa [Fin.val_natCast, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using this

lemma cE_model : cE (shiftM d) (proj0 d) d = 1 := by
  rw [cE]
  simp_rw [cP_model]
  rw [← Fin.sum_univ_eq_sum_range (fun j => single (j : Fin d) (j : Fin d) (1 : ℂ)) d]
  simp [sum_single_one]

lemma zeta_unimod : star (zeta d) * zeta d = 1 := by
  rw [zeta, Complex.star_def, Complex.conj_mul', Complex.norm_exp_ofReal_mul_I]
  simp

lemma zeta_pow : zeta d ^ d = I := by
  rw [zeta, ← Complex.exp_nat_mul]
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  have e : (d : ℂ) * (((Real.pi / (2 * d) : ℝ) : ℂ) * I) = (Real.pi : ℂ) / 2 * I := by
    push_cast
    field_simp
  rw [e, Complex.exp_pi_div_two_mul_I]

/-- **Non-vacuity.** The canonical DKZ tuple satisfies all hypotheses of `rigidity`. -/
theorem canonical_model :
    star (zeta d) * zeta d = 1 ∧ zeta d ^ d = I ∧
    IsU (shiftM d) ∧ IsU (R2m d) ∧ IsU (R3m d) ∧ IsU (R4m d) ∧
    shiftM d ^ d = 1 ∧ R2m d ^ d = 1 ∧
    shiftM d * star (R2m d) = R2m d * star (R3m d) ∧
    R2m d * star (R3m d) = R3m d * star (R4m d) ∧
    ∀ n, n ≤ d → (zeta d ^ n • (shiftM d ^ n * star (R2m d) ^ n) - 1) *
      (zeta d ^ n • (shiftM d ^ n * star (R2m d) ^ n) - I • 1) = 0 := by
  have hz := zeta_unimod (d := d)
  have hp := proj0_isStarProjection (d := d)
  have hp2 : star (proj0 d) = proj0 d := (isStarProjection_iff'.1 hp).2
  have hD : Dm d = star (qp (proj0 d)) := by
    rw [Dm, star_qp hp2]
    module
  have hDU : IsU (Dm d) := by rw [hD]; exact (qp_isU hp).star'
  have hX := shift_isU (d := d)
  have hR2 : IsU (R2m d) := (hDU.mul hX).smul hz
  have hR3 : IsU (R3m d) := (hDU.mul hR2).smul hz
  have hR4 : IsU (R4m d) := (hDU.mul hR3).smul hz
  have hstar2 : star (R2m d) = star (zeta d) • (star (shiftM d) * qp (proj0 d)) := by
    rw [R2m, star_smul, star_mul, hD, star_star]
  have hprod : ∀ n, zeta d ^ n • (shiftM d ^ n * star (R2m d) ^ n)
      = prodQ (shiftM d) (proj0 d) n := zpow_link hz hX hstar2
  have horth : ∀ n, n ≤ d → ∀ i j, i < n → j < n → i ≠ j →
      cP (shiftM d) (proj0 d) i * cP (shiftM d) (proj0 d) j = 0 :=
    fun n hn i j hi hj hij => cP_model_orth i j (by omega) (by omega) hij
  have hT : ∀ n, n ≤ d → (zeta d ^ n • (shiftM d ^ n * star (R2m d) ^ n) - 1) *
      (zeta d ^ n • (shiftM d ^ n * star (R2m d) ^ n) - I • 1) = 0 := by
    intro n hn
    rw [hprod n]
    obtain ⟨hE, hq⟩ := cE_prop hX hp n (horth n hn)
    rw [hq]
    exact qp_two_valued hE
  have hXd : shiftM d ^ d = 1 := shift_pow_d
  have hR2d : R2m d ^ d = 1 := by
    have h1 := hprod d
    obtain ⟨-, hq⟩ := cE_prop hX hp d (horth d le_rfl)
    have h2 : qp (1 : Matrix (Fin d) (Fin d) ℂ) = I • 1 := by
      rw [qp]
      module
    rw [hq, cE_model, zeta_pow, hXd, one_mul, h2] at h1
    have h3 : star (R2m d) ^ d = 1 := by
      have h4 := congrArg (fun x => (-I) • x) h1
      simp only [smul_smul] at h4
      rwa [show (-I * I : ℂ) = 1 by cring, one_smul, one_smul] at h4
    calc R2m d ^ d = star (star (R2m d) ^ d) := by rw [star_pow, star_star]
      _ = 1 := by rw [h3, star_one]
  refine ⟨hz, zeta_pow, hX, hR2, hR3, hR4, hXd, hR2d, ?_, ?_, hT⟩
  · rw [link_of_eq (T := R2m d) (D := Dm d) (z := zeta d) hX rfl,
      link_of_eq (T := R3m d) (D := Dm d) (z := zeta d) hR2 rfl]
  · rw [link_of_eq (T := R3m d) (D := Dm d) (z := zeta d) hR2 rfl,
      link_of_eq (T := R4m d) (D := Dm d) (z := zeta d) hR3 rfl]

end Model

end CGLMPRigidity
