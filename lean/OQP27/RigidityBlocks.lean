import CGLMPRigidity.Rigidity
import OQP27.ReductionClock

/-!
# OQP 27B rigidity, Step 5 (second half): from the reduced family to the rigidity hypotheses (module L6)

Paper: `iqoqi/programs/oqp27B_all/Q_rig/RIGIDITY_ALLD.md` 6.1 ("Q's commute ⟺ the reduced family
commutes ⟺ R has equal links"), and `publish/CGLMP/rigidity/RIGIDITY.md` Lemma 7.2 and Theorem 3.8.

The reduced family of a chain `R = (R_1, …, R_4)` is the explicit block family of module L2,
`V_k = ∑_s |s⟩⟨s+1| ⊗ z^{-k} R_{s+1}^{-k} R_{s+2}^k` (`OQP27.Red.Vred`, with `R_5 = w R_1`). This file
reads the hypotheses of the algebraic rigidity theorem `CGLMPRigidity.rigidity` off two block relations
of this family (no hypotheses; everything is proved):

* `OQP27.Rig.links_of_Vred_comm`: if `V_0` and `V_1` commute, the first three links of `R` are equal,
  `R_1 R_2^* = R_2 R_3^* = R_3 R_4^*` (condition (E_1') of `RIGIDITY.md`). Indeed `V_0` is the block
  shift and `V_0 V_1 = V_1 V_0` compares neighbouring blocks of `V_1`.
* `OQP27.Rig.twoValued_of_Vred`: if `Y = V_0 V_n^*` satisfies `(Y - 1)(Y - i) = 0`, then so does
  `z^n R_1^n R_2^{-n}` (condition (T_n)): the block `s = 0` of `Y` is `z^n R_2^{-n} R_1^n`, which is
  conjugate to `z^n R_1^n R_2^{-n}` by `R_1^n`.
* `OQP27.Rig.rigidity_of_Vred`: consequently, for a chain of `D × D` unitaries with `R_i^d = 1`
  (`d ≥ 2`) whose reduced family commutes and satisfies these two-eigenvalue relations for
  `1 ≤ n ≤ d - 1`, the conclusion of `CGLMPRigidity.rigidity` holds (a projection `p` with
  `R_{k+1} = z (1 - (1 + i) p) R_k` and `d × d` matrix units `R_1^j p R_1^{*k}` with sum `1` in which
  `R_1` is the cyclic shift), and `d ∣ D`.
-/

set_option linter.unusedSectionVars false

open Complex Matrix Finset ComplexConjugate OQP27.Red
open scoped ComplexOrder

namespace OQP27.Rig

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {d : ℕ}

/-! ## Block matrices on `ℤ/4 × κ` -/

lemma SB_apply_add (r : ZMod 4) (B : ZMod 4 → Matrix κ κ ℂ) (s : ZMod 4) (α β : κ) :
    SB r B (s, α) (s + r, β) = B s α β := by
  rw [SB_apply, if_pos rfl]

lemma SB_injective {r : ZMod 4} {B B' : ZMod 4 → Matrix κ κ ℂ} (h : SB r B = SB r B') :
    B = B' := by
  funext s
  ext α β
  rw [← SB_apply_add r B s α β, ← SB_apply_add r B' s α β, h]

lemma SB_sub (r : ZMod 4) (B B' : ZMod 4 → Matrix κ κ ℂ) :
    SB r B - SB r B' = SB r (fun s => B s - B' s) := by
  ext p q
  rw [Matrix.sub_apply, SB_apply, SB_apply, SB_apply]
  split_ifs <;> simp

lemma SB_smul (r : ZMod 4) (c : ℂ) (B : ZMod 4 → Matrix κ κ ℂ) :
    c • SB r B = SB r (fun s => c • B s) := by
  ext p q
  rw [Matrix.smul_apply, SB_apply, SB_apply]
  split_ifs <;> simp

lemma SB_zero_one : (1 : Matrix (ZMod 4 × κ) (ZMod 4 × κ) ℂ) = SB 0 (fun _ => 1) :=
  (SB_zero_of_eq_one _ fun _ => rfl).symm

lemma SB_zero_zero : (0 : Matrix (ZMod 4 × κ) (ZMod 4 × κ) ℂ) = SB 0 (fun _ => 0) := by
  ext p q
  simp [SB_apply]

lemma SB_zero_mul (B B' : ZMod 4 → Matrix κ κ ℂ) :
    SB 0 B * SB 0 B' = SB 0 (fun s => B s * B' s) := by
  rw [SB_mul, add_zero]
  simp only [add_zero]

/-! ## The blocks of the reduced family -/

lemma blk_zero (R : ZMod 4 → Matrix κ κ ℂ) (s : ZMod 4) : blk d R 0 s = 1 := by
  simp [blk]

lemma Vred_zero (R : ZMod 4 → Matrix κ κ ℂ) : Vred d R 0 = SB 1 (fun _ => 1) := by
  rw [Vred]
  congr 1
  funext s
  exact blk_zero R s

lemma blk_one (R : ZMod 4 → Matrix κ κ ℂ) (s : ZMod 4) (hs : s ≠ 3) :
    blk d R 1 s = (zd d)⁻¹ • ((R s)ᴴ * R (s + 1)) := by
  simp [blk, hs]

/-- **(E_1') from `[V_0, V_1] = 0`.** -/
theorem links_of_Vred_comm (R : ZMod 4 → Matrix κ κ ℂ) (hU : ∀ s, IsUnitaryM (R s))
    (h : Vred d R 0 * Vred d R 1 = Vred d R 1 * Vred d R 0) :
    R 0 * (R 1)ᴴ = R 1 * (R 2)ᴴ ∧ R 1 * (R 2)ᴴ = R 2 * (R 3)ᴴ := by
  have hb : ∀ s, blk d R 1 (s + 1) = blk d R 1 s := by
    have e1 : Vred d R 0 * Vred d R 1 = SB 2 (fun s => blk d R 1 (s + 1)) := by
      rw [Vred_zero, Vred, SB_mul]
      congr 1
      funext s
      rw [one_mul]
    have e2 : Vred d R 1 * Vred d R 0 = SB 2 (fun s => blk d R 1 s) := by
      rw [Vred_zero, Vred, SB_mul]
      congr 1
      funext s
      rw [mul_one]
    rw [e1, e2] at h
    intro s
    exact congrFun (SB_injective h) s
  have hz : (zd d)⁻¹ ≠ 0 := inv_ne_zero zd_ne_zero
  -- `R_{s+1}^* R_{s+2} = R_s^* R_{s+1}` for `s = 0, 1`
  have key : ∀ s : ZMod 4, s ≠ 3 → s + 1 ≠ 3 →
      (R (s + 1))ᴴ * R (s + 1 + 1) = (R s)ᴴ * R (s + 1) := by
    intro s hs hs1
    have h1 := hb s
    rw [blk_one R (s + 1) hs1, blk_one R s hs] at h1
    exact smul_right_injective _ hz h1
  have link : ∀ s : ZMod 4, s ≠ 3 → s + 1 ≠ 3 →
      R s * (R (s + 1))ᴴ = R (s + 1) * (R (s + 1 + 1))ᴴ := by
    intro s hs hs1
    have k := key s hs hs1
    -- `R_{s+2} = R_{s+1} R_s^* R_{s+1}`
    have e : R (s + 1 + 1) = R (s + 1) * (R s)ᴴ * R (s + 1) := by
      calc R (s + 1 + 1) = R (s + 1) * ((R (s + 1))ᴴ * R (s + 1 + 1)) := by
            rw [← Matrix.mul_assoc, (hU (s + 1)).mul_conjTranspose, Matrix.one_mul]
        _ = R (s + 1) * (R s)ᴴ * R (s + 1) := by rw [k, Matrix.mul_assoc]
    rw [e, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, (hU (s + 1)).mul_conjTranspose, Matrix.one_mul]
  refine ⟨link 0 (by decide) (by decide), ?_⟩
  have := link 1 (by decide) (by decide)
  rwa [show (1 : ZMod 4) + 1 = 2 from rfl, show (2 : ZMod 4) + 1 = 3 from rfl] at this

/-- **(T_n) from the two-eigenvalue relation of `V_0 V_n^*`.** -/
theorem twoValued_of_Vred (R : ZMod 4 → Matrix κ κ ℂ) (hU : ∀ s, IsUnitaryM (R s)) (n : ℕ)
    (h : (Vred d R 0 * (Vred d R n)ᴴ - 1) * (Vred d R 0 * (Vred d R n)ᴴ - I • 1) = 0) :
    (zd d ^ n • (R 0 ^ n * (R 1)ᴴ ^ n) - 1) * (zd d ^ n • (R 0 ^ n * (R 1)ᴴ ^ n) - I • 1) = 0 := by
  set C : ZMod 4 → Matrix κ κ ℂ := fun s => (blk d R n s)ᴴ with hC
  have hY : Vred d R 0 * (Vred d R n)ᴴ = SB 0 C := by
    rw [Vred_mul_conjTranspose]
    congr 1
    funext s
    rw [blk_zero, one_mul]
  rw [hY, SB_zero_one, SB_sub, SB_smul, SB_sub, SB_zero_mul, SB_zero_zero] at h
  have h0 := congrFun (SB_injective h) 0
  -- the block `s = 0`: `C 0 = z^n R_2^{-n} R_1^n`
  have hC0 : C 0 = zd d ^ n • ((R 1 ^ n)ᴴ * R 0 ^ n) := by
    simp only [hC, blk, if_neg (by decide : (0 : ZMod 4) ≠ 3), mul_one, conjTranspose_smul,
      conjTranspose_mul, conjTranspose_conjTranspose, zero_add]
    congr 1
    rw [Complex.star_def, map_inv₀, conj_zd_pow, inv_inv]
  have hP : R 0 ^ n * (R 0 ^ n)ᴴ = 1 := (hU 0).pow_mul_conjTranspose_pow n
  have hP' : (R 0 ^ n)ᴴ * R 0 ^ n = 1 := (hU 0).conjTranspose_pow_mul_pow n
  -- `z^n R_1^n R_2^{-n} = R_1^n (C 0) R_1^{-n}`
  have hX : zd d ^ n • (R 0 ^ n * (R 1)ᴴ ^ n) = R 0 ^ n * C 0 * (R 0 ^ n)ᴴ := by
    rw [hC0, Matrix.mul_smul, Matrix.smul_mul, ← conjTranspose_pow, Matrix.mul_assoc,
      Matrix.mul_assoc, hP, Matrix.mul_one]
  have hX1 : zd d ^ n • (R 0 ^ n * (R 1)ᴴ ^ n) - 1 = R 0 ^ n * (C 0 - 1) * (R 0 ^ n)ᴴ := by
    rw [hX, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hP]
  have hXI : zd d ^ n • (R 0 ^ n * (R 1)ᴴ ^ n) - I • 1
      = R 0 ^ n * (C 0 - I • 1) * (R 0 ^ n)ᴴ := by
    rw [hX, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hP]
  rw [hX1, hXI]
  calc R 0 ^ n * (C 0 - 1) * (R 0 ^ n)ᴴ * (R 0 ^ n * (C 0 - I • 1) * (R 0 ^ n)ᴴ)
      = R 0 ^ n * ((C 0 - 1) * ((R 0 ^ n)ᴴ * R 0 ^ n) * (C 0 - I • 1)) * (R 0 ^ n)ᴴ := by
        simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hP', Matrix.mul_one, h0, Matrix.mul_zero, Matrix.zero_mul]

lemma isU_of_isUnitaryM {U : Matrix κ κ ℂ} (hU : IsUnitaryM U) : CGLMPRigidity.IsU U :=
  ⟨hU, hU.mul_conjTranspose⟩

/-- **The hypotheses of `CGLMPRigidity.rigidity` from the reduced family.** For a chain of unitaries
`R_1, …, R_4` (stored as `R 0, …, R 3`) with `R_i^d = 1`, `d ≥ 2`: if `V_0 V_1 = V_1 V_0` and
`Y_n = V_0 V_n^*` satisfies `(Y_n - 1)(Y_n - i) = 0` for `1 ≤ n ≤ d - 1`, then `R` is in canonical DKZ
form (conclusion of `CGLMPRigidity.rigidity`, with `z = e^{2πi/(4d)}`). -/
theorem rigidity_of_Vred (hd : 2 ≤ d) (R : ZMod 4 → Matrix κ κ ℂ) (hU : ∀ s, IsUnitaryM (R s))
    (hpow : ∀ s, R s ^ d = 1)
    (hcomm : Vred d R 0 * Vred d R 1 = Vred d R 1 * Vred d R 0)
    (hrel : ∀ n, 1 ≤ n → n < d →
      (Vred d R 0 * (Vred d R n)ᴴ - 1) * (Vred d R 0 * (Vred d R n)ᴴ - I • 1) = 0) :
    ∃ p : Matrix κ κ ℂ, IsStarProjection p ∧
      R 1 = zd d • ((1 - (1 + I) • p) * R 0) ∧ R 2 = zd d • ((1 - (1 + I) • p) * R 1) ∧
      R 3 = zd d • ((1 - (1 + I) • p) * R 2) ∧
      (∀ j k l m, k < d → l < d →
        CGLMPRigidity.mu (R 0) p j k * CGLMPRigidity.mu (R 0) p l m
          = if k = l then CGLMPRigidity.mu (R 0) p j m else 0) ∧
      (∀ j k, star (CGLMPRigidity.mu (R 0) p j k) = CGLMPRigidity.mu (R 0) p k j) ∧
      (∑ j ∈ Finset.range d, CGLMPRigidity.mu (R 0) p j j = 1) ∧
      R 0 = ∑ j ∈ Finset.range d, CGLMPRigidity.mu (R 0) p ((j + 1) % d) j := by
  have hd0 : d ≠ 0 := by omega
  have hC : ∀ x : Matrix κ κ ℂ, star x * x = 0 → x = 0 := by
    intro x hx
    rw [star_eq_conjTranspose] at hx
    exact Matrix.conjTranspose_mul_self_eq_zero.1 hx
  obtain ⟨hE₁, hE₂⟩ := links_of_Vred_comm R hU hcomm
  refine CGLMPRigidity.rigidity hC star_zd_mul (zd_pow_d hd0) (isU_of_isUnitaryM (hU 0))
    (isU_of_isUnitaryM (hU 1)) (isU_of_isUnitaryM (hU 2)) (hpow 0) (hpow 1) hE₁ hE₂ ?_
  intro n hn1 hn2
  rcases Nat.lt_or_ge n d with hnd | hnd
  · have := twoValued_of_Vred R hU n (hrel n hn1 hnd)
    simpa [star_eq_conjTranspose] using this
  · -- `n = d` (only for `d = 2`): `z^d R_1^d R_2^{-d} = i`
    have hnd' : n = d := by omega
    subst hnd'
    have h1 : R 0 ^ n * star (R 1) ^ n = 1 := by
      rw [← star_pow, hpow 0, hpow 1, star_one, Matrix.one_mul]
    rw [h1, zd_pow_d hd0, sub_self, Matrix.mul_zero]

end OQP27.Rig
