import OQP27.RigidityClassical
import Mathlib.Tactic.IntervalCases

/-!
# OQP 27B rigidity: the 27B configuration of a reduced family (module L6)

Paper: `iqoqi/programs/oqp27B_all/Q_rig/RIGIDITY_ALLD.md`, section 1.3, eq. (1.0).

For unitaries `V_0, …, V_{d-1}` with `V_k^4 = 1` let `E_k = V_k^*` and let `Q_{k - d a}` be the spectral
projection of `E_k` for the eigenvalue `i^a` (`a ∈ ℤ_4`), written as the polynomial
`P_a(E) = (1/4) ∑_{t<4} (i^{-a} E)^t` (`OQP27.Rig.specProj`). This file proves (no hypotheses):

* `OQP27.Rig.specProj_isProj`, `specProj_mul`, `sum_specProj`, `sum_I_pow_smul_specProj`: the `P_a(E)`
  are pairwise orthogonal projections with `∑_a P_a = 1` and `∑_a i^a P_a = E`;
* `OQP27.Rig.specConfig_isConfig`: the family `x ↦ Q_x` (`OQP27.Rig.specConfig`) is a 27B configuration;
* `OQP27.Rig.redV_specConfig`: its reduced family is `V` again, `∑_a (-i)^a Q_{k - d a} = V_k`
  (eq. (1.0)).

This file is self-contained; the main chain of the module uses module L2's equivalent construction
`OQP27.Red.Qcfg` (bridged to `OQP27.Rig.IsConfig` in `OQP27/RigidityReduction.lean`).
-/

set_option linter.unusedSectionVars false

open Complex Matrix Finset

namespace OQP27.Rig

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Powers of `i` -/

lemma negI_pow_four : (-I) ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, neg_sq, I_sq]; norm_num

lemma I_pow_mul_negI_pow (n : ℕ) : I ^ n * (-I) ^ n = 1 := by
  rw [← mul_pow, mul_neg, I_mul_I, neg_neg, one_pow]

lemma negI_pow_three : (-I) ^ 3 = I := by linear_combination (-I) * I_sq

lemma negI_pow_three_mul (n : ℕ) : (-I) ^ (3 * n) = I ^ n := by
  rw [pow_mul, negI_pow_three]

lemma negI_pow_mod (n : ℕ) : (-I) ^ n = (-I) ^ (n % 4) := by
  conv_lhs => rw [← Nat.mod_add_div n 4, pow_add, pow_mul, negI_pow_four, one_pow, mul_one]

lemma star_negI_pow' (n : ℕ) : star ((-I) ^ n) = (-I) ^ (3 * n) := by
  rw [star_pow, Complex.star_def, map_neg, Complex.conj_I, neg_neg, negI_pow_three_mul]

lemma I_pow_three : I ^ 3 = -I := by linear_combination I * I_sq

/-- Character sums of `ℤ_4`: `∑_{t<4} i^{c t} = 4 [c = 0]`. -/
lemma sum_I_pow_mul (c : ZMod 4) :
    ∑ t ∈ Finset.range 4, I ^ (c.val * t) = if c = 0 then 4 else 0 := by
  have hc : c.val < 4 := ZMod.val_lt c
  have h0 : c = 0 ↔ c.val = 0 := (ZMod.val_eq_zero c).symm
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, mul_zero, pow_zero, mul_one]
  by_cases hc0 : c = 0
  · rw [if_pos hc0, h0.1 hc0]; norm_num
  · rw [if_neg hc0]
    have hc0' : c.val ≠ 0 := fun h => hc0 (h0.2 h)
    generalize c.val = n at hc hc0' ⊢
    interval_cases n
    · exact absurd rfl hc0'
    · rw [show 1 * 2 = 2 from rfl, show 1 * 3 = 3 from rfl, pow_one, I_sq, I_pow_three]; ring
    · rw [show 2 * 2 = 2 * 2 from rfl, show 2 * 3 = 2 * 3 from rfl, pow_mul, pow_mul, I_sq]; norm_num
    · rw [show 3 * 2 = 3 * 2 from rfl, show 3 * 3 = 3 * 3 from rfl, pow_mul, pow_mul, I_pow_three]
      linear_combination (I ^ 2 - I + 1) * I_sq - I * I_pow_three

/-! ## Spectral projections of an order-four unitary -/

/-- `P_a(E) = (1/4) ∑_{t<4} (i^{-a} E)^t`: for a unitary `E` with `E^4 = 1`, the spectral projection
of `E` for the eigenvalue `i^a`. -/
noncomputable def specProj (E : Matrix ι ι ℂ) (a : ZMod 4) : Matrix ι ι ℂ :=
  (1 / 4 : ℂ) • ∑ t ∈ Finset.range 4, (-I) ^ (a.val * t) • E ^ t

lemma specProj_expand (E : Matrix ι ι ℂ) (a : ZMod 4) :
    specProj E a = (1 / 4 : ℂ) • (1 + (-I) ^ a.val • E + (-I) ^ (2 * a.val) • E ^ 2
      + (-I) ^ (3 * a.val) • E ^ 3) := by
  simp only [specProj, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, mul_zero, pow_zero,
    one_smul, mul_one, pow_one]
  congr 1
  rw [mul_comm a.val 2, mul_comm a.val 3]

variable {E : Matrix ι ι ℂ}

/-- Scalar identities between powers of `i` with a concrete exponent are decided by computing real and
imaginary parts. -/
macro "cpow_tac" : tactic =>
  `(tactic| (simp only [Complex.ext_iff, pow_succ, pow_zero, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im,
    Complex.zero_re, Complex.zero_im, Complex.ofReal_re, Complex.ofReal_im] <;> norm_num))

/-- The eigen-relation `E P_a = i^a P_a`. -/
lemma mul_specProj (h4 : E ^ 4 = 1) (a : ZMod 4) : E * specProj E a = I ^ a.val • specProj E a := by
  have hE3 : E * E ^ 3 = 1 := by rw [← pow_succ', h4]
  have hE2 : E * E ^ 2 = E ^ 3 := by rw [← pow_succ']
  have hE1 : E * E = E ^ 2 := by rw [sq]
  rw [specProj_expand, Matrix.mul_smul]
  simp only [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, hE1, hE2, hE3]
  have ha : a.val < 4 := ZMod.val_lt a
  generalize a.val = n at ha ⊢
  interval_cases n <;> match_scalars <;> cpow_tac

lemma pow_mul_specProj (h4 : E ^ 4 = 1) (a : ZMod 4) (t : ℕ) :
    E ^ t * specProj E a = I ^ (a.val * t) • specProj E a := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, Matrix.mul_assoc, mul_specProj h4, Matrix.mul_smul, ih, smul_smul, ← pow_add,
      Nat.mul_succ, add_comm]

lemma negI_pow_mul_I_pow (a b : ZMod 4) (t : ℕ) :
    (-I) ^ (a.val * t) * I ^ (b.val * t) = I ^ ((b - a).val * t) := by
  rw [pow_mul, pow_mul, pow_mul, ← mul_pow, I_pow_val_mul]

lemma specProj_mul (h4 : E ^ 4 = 1) (a b : ZMod 4) :
    specProj E a * specProj E b = if a = b then specProj E b else 0 := by
  have h : specProj E a * specProj E b
      = ((1 / 4 : ℂ) * ∑ t ∈ Finset.range 4, I ^ ((b - a).val * t)) • specProj E b := by
    conv_lhs => rw [specProj]
    rw [Matrix.smul_mul, Finset.sum_mul]
    simp_rw [Matrix.smul_mul, pow_mul_specProj h4, smul_smul, negI_pow_mul_I_pow]
    rw [← Finset.sum_smul, smul_smul]
  rw [h, sum_I_pow_mul]
  by_cases hab : a = b
  · rw [if_pos (sub_eq_zero.2 hab.symm), if_pos hab]; norm_num
  · rw [if_neg (fun h => hab (sub_eq_zero.1 h).symm), if_neg hab, mul_zero, zero_smul]

lemma sum_zmod4' {M : Type*} [AddCommMonoid M] (f : ZMod 4 → M) :
    ∑ a : ZMod 4, f a = f 0 + f 1 + f 2 + f 3 := Fin.sum_univ_four f

lemma val_zmod4 : (0 : ZMod 4).val = 0 ∧ (1 : ZMod 4).val = 1 ∧ (2 : ZMod 4).val = 2 ∧
    (3 : ZMod 4).val = 3 := ⟨rfl, rfl, rfl, rfl⟩

lemma sum_specProj (E : Matrix ι ι ℂ) : ∑ a : ZMod 4, specProj E a = 1 := by
  rw [sum_zmod4']
  simp only [specProj_expand, val_zmod4]
  match_scalars <;> cpow_tac

lemma sum_I_pow_smul_specProj (h4 : E ^ 4 = 1) : ∑ a : ZMod 4, I ^ a.val • specProj E a = E := by
  have hE4 : E ^ 4 = 1 := h4
  rw [sum_zmod4']
  simp only [specProj_expand, val_zmod4, smul_add, smul_smul]
  match_scalars <;> cpow_tac

/-- `P_a(E)` is Hermitian when `E` is unitary with `E^4 = 1`. -/
lemma specProj_isHermitian (hU : Eᴴ * E = 1) (h4 : E ^ 4 = 1) (a : ZMod 4) :
    (specProj E a).IsHermitian := by
  have hE : Eᴴ = E ^ 3 := by
    calc Eᴴ = Eᴴ * E ^ 4 := by rw [h4, Matrix.mul_one]
      _ = Eᴴ * E * E ^ 3 := by rw [Matrix.mul_assoc, ← pow_succ']
      _ = E ^ 3 := by rw [hU, Matrix.one_mul]
  have h2 : (E ^ 2)ᴴ = E ^ 2 := by
    rw [conjTranspose_pow, hE, ← pow_mul, show 3 * 2 = 4 + 2 by rfl, pow_add, h4, Matrix.one_mul]
  have h3 : (E ^ 3)ᴴ = E := by
    rw [conjTranspose_pow, hE, ← pow_mul, show 3 * 3 = 4 + 4 + 1 by rfl, pow_add, pow_add, h4,
      Matrix.one_mul, Matrix.one_mul, pow_one]
  unfold Matrix.IsHermitian
  rw [specProj_expand]
  simp only [conjTranspose_smul, conjTranspose_add, conjTranspose_one, hE, h2, h3]
  have ha : a.val < 4 := ZMod.val_lt a
  generalize a.val = n at ha ⊢
  interval_cases n <;> match_scalars <;> cpow_tac

lemma specProj_isProj (hU : Eᴴ * E = 1) (h4 : E ^ 4 = 1) (a : ZMod 4) : IsProj (specProj E a) :=
  ⟨specProj_isHermitian hU h4 a, by rw [specProj_mul h4, if_pos rfl]⟩

/-! ## The configuration of a family of order-four unitaries -/

section Config

variable {d : ℕ} [NeZero d]

/-- `(k - d a).val = k + d ((4 - a) mod 4)` in `ℤ_{4d}`. -/
lemma siteIdx_val (k : Fin d) (a : ZMod 4) :
    (siteIdx d k a).val = (k : ℕ) + d * ((4 - a.val) % 4) := by
  have ha : a.val < 4 := ZMod.val_lt a
  have hk : (k : ℕ) < d := k.isLt
  have hlt : (k : ℕ) + d * ((4 - a.val) % 4) < 4 * d := by
    have : (4 - a.val) % 4 ≤ 3 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
    nlinarith
  have heq : siteIdx d k a = (((k : ℕ) + d * ((4 - a.val) % 4) : ℕ) : ZMod (4 * d)) := by
    unfold siteIdx
    rw [sub_eq_iff_eq_add]
    push_cast
    have h4 : a.val + (4 - a.val) % 4 = 0 ∨ a.val + (4 - a.val) % 4 = 4 := by omega
    have hcast : ((d : ℕ) : ZMod (4 * d)) * (4 : ℕ) = 0 := by
      rw [← Nat.cast_mul, mul_comm, ZMod.natCast_self]
    rcases h4 with h | h
    · have : (a.val : ZMod (4 * d)) + (((4 - a.val) % 4 : ℕ) : ZMod (4 * d)) = 0 := by
        rw [← Nat.cast_add, h, Nat.cast_zero]
      linear_combination (-(d : ZMod (4 * d))) * this
    · have : (a.val : ZMod (4 * d)) + (((4 - a.val) % 4 : ℕ) : ZMod (4 * d)) = ((4 : ℕ) : ZMod (4 * d)) := by
        rw [← Nat.cast_add, h]
      linear_combination (-(d : ZMod (4 * d))) * this - hcast
  rw [heq, ZMod.val_natCast_of_lt hlt]

lemma siteIdx_mod (k : Fin d) (a : ZMod 4) : (siteIdx d k a).val % d = k := by
  rw [siteIdx_val, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt k.isLt]

lemma siteIdx_div (k : Fin d) (a : ZMod 4) :
    -(((siteIdx d k a).val / d : ℕ) : ZMod 4) = a := by
  have hd : 0 < d := NeZero.pos d
  rw [siteIdx_val, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt k.isLt, zero_add]
  have ha : a.val < 4 := ZMod.val_lt a
  have key : ∀ b : ZMod 4, -(((4 - b.val) % 4 : ℕ) : ZMod 4) = b := by decide
  exact key a

/-- The 27B configuration of a family `V_0, …, V_{d-1}`: `Q_x = P_a(V_k^*)` for `x = k - d a`. -/
noncomputable def specConfig (V : Fin d → Matrix ι ι ℂ) (x : ZMod (4 * d)) : Matrix ι ι ℂ :=
  specProj (star (V ⟨x.val % d, Nat.mod_lt _ (NeZero.pos d)⟩)) (-((x.val / d : ℕ) : ZMod 4))

lemma specConfig_siteIdx (V : Fin d → Matrix ι ι ℂ) (k : Fin d) (a : ZMod 4) :
    specConfig V (siteIdx d k a) = specProj (star (V k)) a := by
  unfold specConfig
  have h1 : (⟨(siteIdx d k a).val % d, Nat.mod_lt _ (NeZero.pos d)⟩ : Fin d) = k :=
    Fin.ext (siteIdx_mod k a)
  rw [h1, siteIdx_div]

variable {V : Fin d → Matrix ι ι ℂ}

/-- **The configuration of a unitary family with `V_k^4 = 1` is a 27B configuration.** -/
theorem specConfig_isConfig (hU : ∀ k, (V k)ᴴ * V k = 1) (h4 : ∀ k, V k ^ 4 = 1) :
    IsConfig (specConfig V) := by
  have hU' : ∀ k, (star (V k))ᴴ * star (V k) = 1 := by
    intro k
    rw [star_eq_conjTranspose, conjTranspose_conjTranspose]
    exact mul_eq_one_comm.1 (hU k)
  have h4' : ∀ k, (star (V k)) ^ 4 = 1 := by
    intro k; rw [← star_pow, h4, star_one]
  refine ⟨fun x => ?_, fun k => ?_, fun k a b hab => ?_⟩
  · exact specProj_isProj (hU' _) (h4' _) _
  · simp_rw [specConfig_siteIdx]
    exact sum_specProj _
  · rw [specConfig_siteIdx, specConfig_siteIdx, specProj_mul (h4' k), if_neg hab]

/-- **Eq. (1.0)**: the reduced family of the configuration of `V` is `V`. -/
theorem redV_specConfig (hU : ∀ k, (V k)ᴴ * V k = 1) (h4 : ∀ k, V k ^ 4 = 1) (k : Fin d) :
    redV (specConfig V) k = V k := by
  have hU' : (star (V k))ᴴ * star (V k) = 1 := by
    rw [star_eq_conjTranspose, conjTranspose_conjTranspose]
    exact mul_eq_one_comm.1 (hU k)
  have h4' : (star (V k)) ^ 4 = 1 := by rw [← star_pow, h4, star_one]
  have h := congrArg conjTranspose (sum_I_pow_smul_specProj h4')
  rw [conjTranspose_sum, ← star_eq_conjTranspose, star_star] at h
  rw [← h, redV]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [specConfig_siteIdx, conjTranspose_smul, (specProj_isHermitian hU' h4' a).eq, ← star_negI_pow,
    star_star]

end Config

end OQP27.Rig
