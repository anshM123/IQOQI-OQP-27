import OQP27.ReductionSpectral
import OQP27.ReductionCsc

/-!
# OQP 27B, module L2 (reduction), part 7: covariant strategies (paper Theorem 2.3(1))

Paper: `publish/CGLMP/paper-classical-all-d/main.tex`, eq. (covariant), Theorem 2.3(1) and Appendix A
("Covariant strategies: proof of (1)").

For order-4 unitaries `V_0, …, V_{d-1}` on `ℂ^M` let `X` be the cyclic shift `|k⟩ ↦ |k+1⟩` on `ℂ^d`,
`W = ∑_k |k⟩⟨k| ⊗ z^k V_k`, `R_1 = X ⊗ 1` and `R_{i+1} = W R_i W^*` (index set `ℤ/d × κ`, `M = |κ|`).

Main results (all PROVED, no hypotheses):
* `OQP27.Red.Lam_Rcov`: all four links have the same trace, `Λ_n(R^V) = 4 τ(L^{(0)}_n)`, with
  `τ(L^{(0)}_n) = (z^{-n}/d) [∑_{k ≥ n} tr(V_{k-n} V_k^*) + i ∑_{k < n} tr(V_{k-n+d} V_k^*)]`.
* `OQP27.Red.sum_cd_Lam_Rcov` (**Theorem 2.3(1), trace form**): `∑_{n=1}^{d-1} c_n Λ_n(R^V) = -(2/d) F(V)`.
-/

namespace OQP27.Red

open Complex Finset ComplexConjugate Matrix

noncomputable section

/-! ### Generalities -/

section General

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma SB_zero_pow (B : G → Matrix κ κ ℂ) (m : ℕ) : SB (0 : G) B ^ m = SB 0 (fun s => B s ^ m) := by
  induction m with
  | zero =>
    rw [pow_zero]
    exact (SB_zero_of_eq_one _ (fun s => pow_zero _)).symm
  | succ m ih =>
    rw [pow_succ, ih, SB_mul, add_zero]
    simp only [add_zero, ← pow_succ]

omit [Fintype κ] [DecidableEq κ] [Fintype G] in
lemma SB_smul (r : G) (c : ℂ) (B : G → Matrix κ κ ℂ) :
    SB r (fun s => c • B s) = c • SB r B := by
  ext p q
  rw [SB_apply, Matrix.smul_apply, Matrix.smul_apply, SB_apply]
  split_ifs <;> simp

/-- Conjugating a block-diagonal matrix by a block shift. -/
lemma SB_conj_shift (r : G) (B : G → Matrix κ κ ℂ) :
    SB (-r) (fun _ => (1 : Matrix κ κ ℂ)) * SB 0 B * SB r (fun _ => 1) = SB 0 (fun s => B (s - r)) := by
  rw [SB_mul, SB_mul]
  congr 1
  · abel
  · funext s
    rw [one_mul, mul_one, sub_eq_add_neg]

lemma unitary_conj_pow {U A : Matrix κ κ ℂ} (hU : IsUnitaryM U) (m : ℕ) :
    (U * A * Uᴴ) ^ m = U * A ^ m * Uᴴ := by
  induction m with
  | zero => simp [hU.mul_conjTranspose]
  | succ m ih =>
    rw [pow_succ, ih, pow_succ]
    have : U * A ^ m * Uᴴ * (U * A * Uᴴ) = U * A ^ m * (Uᴴ * U) * A * Uᴴ := by
      simp only [Matrix.mul_assoc]
    rw [this, hU, Matrix.mul_one]
    simp only [Matrix.mul_assoc]

lemma ntr_unitary_conj {U Y : Matrix κ κ ℂ} (hU : IsUnitaryM U) : ntr (U * Y * Uᴴ) = ntr Y := by
  rw [ntr, ntr, trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

end General

/-! ### The covariant strategy -/

section Covariant

variable {d : ℕ} [NeZero d] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- `X ⊗ 1` on `ℂ^d ⊗ ℂ^M` (index set `ℤ/d × κ`), `X |k⟩ = |k+1⟩`. -/
def shiftX (d : ℕ) [NeZero d] (κ : Type*) [Fintype κ] [DecidableEq κ] :
    Matrix (ZMod d × κ) (ZMod d × κ) ℂ :=
  SB (-1 : ZMod d) (fun _ => (1 : Matrix κ κ ℂ))

/-- The blocks `W_k = z^k V_k`. -/
def Wblk (d : ℕ) (V : ℕ → Matrix κ κ ℂ) (s : ZMod d) : Matrix κ κ ℂ := zd d ^ s.val • V s.val

/-- `W = ∑_k |k⟩⟨k| ⊗ z^k V_k`. -/
def Wcov (d : ℕ) [NeZero d] (V : ℕ → Matrix κ κ ℂ) : Matrix (ZMod d × κ) (ZMod d × κ) ℂ :=
  SB (0 : ZMod d) (Wblk d V)

/-- **The covariant strategy** (paper eq. (covariant)): `R_1 = X ⊗ 1`, `R_{i+1} = W R_i W^*`, as a chain
`s ↦ R_{s+1} = W^s (X ⊗ 1) W^{-s}` (`s ∈ ℤ/4`). -/
def Rcov (d : ℕ) [NeZero d] (V : ℕ → Matrix κ κ ℂ) (s : ZMod 4) :
    Matrix (ZMod d × κ) (ZMod d × κ) ℂ :=
  Wcov d V ^ s.val * shiftX d κ * (Wcov d V ^ s.val)ᴴ

lemma shiftX_pow (m : ℕ) : shiftX d κ ^ m = SB (-(m : ZMod d)) (fun _ => (1 : Matrix κ κ ℂ)) := by
  induction m with
  | zero =>
    rw [pow_zero, Nat.cast_zero, neg_zero]
    exact (SB_zero_of_eq_one _ (fun _ => rfl)).symm
  | succ m ih =>
    rw [pow_succ, ih, shiftX, SB_mul, Matrix.one_mul]
    congr 1
    push_cast
    ring

lemma shiftX_pow_conjTranspose (m : ℕ) :
    (shiftX d κ ^ m)ᴴ = SB (m : ZMod d) (fun _ => (1 : Matrix κ κ ℂ)) := by
  rw [shiftX_pow, SB_conjTranspose, neg_neg]
  simp only [conjTranspose_one]

lemma shiftX_unitary : IsUnitaryM (shiftX d κ) := by
  unfold IsUnitaryM
  have h := shiftX_pow_conjTranspose (d := d) (κ := κ) 1
  rw [pow_one] at h
  rw [h, shiftX, SB_mul, Matrix.one_mul, Nat.cast_one, add_neg_cancel]
  exact SB_zero_of_eq_one _ (fun _ => rfl)

lemma shiftX_pow_d : shiftX d κ ^ d = 1 := by
  rw [shiftX_pow, ZMod.natCast_self, neg_zero]
  exact SB_zero_of_eq_one _ (fun _ => rfl)

variable {V : ℕ → Matrix κ κ ℂ}

omit [NeZero d] in
lemma Wblk_unitary (hV : ∀ k, IsUnitaryM (V k)) (s : ZMod d) : IsUnitaryM (Wblk d V s) :=
  (hV _).smul (by rw [conj_zd_pow, inv_mul_cancel₀ (pow_ne_zero _ zd_ne_zero)])

lemma Wcov_unitary (hV : ∀ k, IsUnitaryM (V k)) : IsUnitaryM (Wcov d V) := by
  unfold IsUnitaryM Wcov
  rw [SB_conjTranspose, neg_zero, SB_mul, add_zero]
  apply SB_zero_of_eq_one
  intro s
  rw [sub_zero, add_zero]
  exact Wblk_unitary hV s

lemma Wcov_pow_four (hV4 : ∀ k, V k ^ 4 = 1) :
    Wcov d V ^ 4 = SB (0 : ZMod d) (fun s => wd d ^ s.val • (1 : Matrix κ κ ℂ)) := by
  rw [Wcov, SB_zero_pow]
  congr 1
  funext s
  rw [Wblk, smul_pow, hV4, ← pow_mul, mul_comm, pow_mul, zd_pow_four (NeZero.ne d)]

lemma wd_pow_val_sub_sub (s : ZMod d) (m : ℕ) :
    wd d ^ s.val * conj (wd d ^ (s - m).val) = wd d ^ m := by
  have h := wd_pow_val_sub 1 s (s - (m : ZMod d))
  simp only [one_mul, sub_sub_cancel] at h
  rw [conj_wd_pow, ← h, ZMod.val_natCast, wd_pow_mod (NeZero.ne d)]

/-- `W^4 X^m W^{-4} = w^m X^m` (from `W^4 = Z_0 ⊗ 1` and `Z_0 X Z_0^* = w X`). -/
lemma Wcov_pow_four_conj (hV4 : ∀ k, V k ^ 4 = 1) (m : ℕ) :
    Wcov d V ^ 4 * shiftX d κ ^ m * (Wcov d V ^ 4)ᴴ = wd d ^ m • shiftX d κ ^ m := by
  rw [Wcov_pow_four hV4, shiftX_pow, SB_conjTranspose, SB_mul, SB_mul, ← SB_smul]
  congr 1
  · simp
  · funext s
    simp only [zero_add, sub_zero, Matrix.mul_one, conjTranspose_smul, conjTranspose_one,
      smul_mul_smul_comm]
    rw [Complex.star_def, ← sub_eq_add_neg, wd_pow_val_sub_sub]

/-! ### The four links have the same trace -/

/-- `L^{(0)}_n = R_1^n R_2^{-n} = X^n W X^{-n} W^*`. -/
def Lzero (d : ℕ) [NeZero d] (V : ℕ → Matrix κ κ ℂ) (m : ℕ) : Matrix (ZMod d × κ) (ZMod d × κ) ℂ :=
  shiftX d κ ^ m * Wcov d V * (shiftX d κ ^ m)ᴴ * (Wcov d V)ᴴ

lemma conj_link {U W A B : Matrix (ZMod d × κ) (ZMod d × κ) ℂ} (hU : IsUnitaryM U) :
    U * A * Uᴴ * ((U * W) * B * (U * W)ᴴ) = U * (A * W * B * Wᴴ) * Uᴴ := by
  rw [conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᴴ U, hU, Matrix.one_mul]

lemma link_succ (hW : IsUnitaryM (Wcov d V)) (a m : ℕ) :
    ntr ((Wcov d V ^ a * shiftX d κ * (Wcov d V ^ a)ᴴ) ^ m
        * ((Wcov d V ^ (a + 1) * shiftX d κ * (Wcov d V ^ (a + 1))ᴴ) ^ m)ᴴ) = ntr (Lzero d V m) := by
  have hWa := hW.pow a
  have key : (Wcov d V ^ a * shiftX d κ ^ m * (Wcov d V ^ a)ᴴ)
      * (Wcov d V ^ (a + 1) * shiftX d κ ^ m * (Wcov d V ^ (a + 1))ᴴ)ᴴ
      = Wcov d V ^ a * Lzero d V m * (Wcov d V ^ a)ᴴ := by
    rw [pow_succ, Lzero]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Wcov d V ^ a)ᴴ (Wcov d V ^ a), hWa, Matrix.one_mul]
  rw [unitary_conj_pow hWa, unitary_conj_pow (hW.pow (a + 1)), key, ntr_unitary_conj hWa]

lemma link_three (hV4 : ∀ k, V k ^ 4 = 1) (hW : IsUnitaryM (Wcov d V)) (m : ℕ) :
    ntr ((Wcov d V ^ 3 * shiftX d κ * (Wcov d V ^ 3)ᴴ) ^ m * (shiftX d κ ^ m)ᴴ)
      = wd d ^ m * ntr (Lzero d V m) := by
  have hW3 := hW.pow 3
  have hX : (shiftX d κ ^ m)ᴴ = wd d ^ m • (Wcov d V ^ 4 * (shiftX d κ ^ m)ᴴ * (Wcov d V ^ 4)ᴴ) := by
    have h := congrArg conjTranspose (Wcov_pow_four_conj (d := d) (κ := κ) hV4 m)
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_smul,
      Complex.star_def, conj_wd_pow, ← Matrix.mul_assoc] at h
    rw [h, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ wd_ne_zero), one_smul]
  have key : Wcov d V ^ 3 * shiftX d κ ^ m * (Wcov d V ^ 3)ᴴ
      * (Wcov d V ^ 4 * (shiftX d κ ^ m)ᴴ * (Wcov d V ^ 4)ᴴ)
      = Wcov d V ^ 3 * Lzero d V m * (Wcov d V ^ 3)ᴴ := by
    rw [show Wcov d V ^ 4 = Wcov d V ^ 3 * Wcov d V from pow_succ _ 3, Lzero]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Wcov d V ^ 3)ᴴ (Wcov d V ^ 3), hW3, Matrix.one_mul]
  rw [unitary_conj_pow hW3, hX, Matrix.mul_smul, ntr_smul, key, ntr_unitary_conj hW3]

/-- **All four links of a covariant strategy have the same trace**: `Λ_n(R^V) = 4 τ(L^{(0)}_n)`. -/
theorem Lam_Rcov (hV : ∀ k, IsUnitaryM (V k)) (hV4 : ∀ k, V k ^ 4 = 1) (m : ℕ) :
    Lam d (Rcov d V) m = 4 * ntr (Lzero d V m) := by
  have hW := Wcov_unitary (d := d) hV
  rw [Lam, sum_zmod4]
  simp only [Rcov, twist]
  have v0 : (0 : ZMod 4).val = 0 := rfl
  have v1 : (1 : ZMod 4).val = 1 := rfl
  have v2 : (2 : ZMod 4).val = 2 := rfl
  have v3 : (3 : ZMod 4).val = 3 := rfl
  have h01 : (0 : ZMod 4) + 1 = 1 := rfl
  have h11 : (1 : ZMod 4) + 1 = 2 := rfl
  have h21 : (2 : ZMod 4) + 1 = 3 := rfl
  have h31 : (3 : ZMod 4) + 1 = 0 := rfl
  rw [h01, h11, h21, h31, v0, v1, v2, v3]
  have n0 : (0 : ZMod 4) ≠ 3 := by decide
  have n1 : (1 : ZMod 4) ≠ 3 := by decide
  have n2 : (2 : ZMod 4) ≠ 3 := by decide
  simp only [n0, n1, n2, if_false, if_true, one_mul]
  have e0 := link_succ (d := d) hW 0 m
  have e1 := link_succ (d := d) hW 1 m
  have e2 := link_succ (d := d) hW 2 m
  have e3 := link_three (d := d) hV4 hW m
  simp only [zero_add] at e0
  rw [e0, e1, e2]
  have hX0 : Wcov d V ^ 0 * shiftX d κ * (Wcov d V ^ 0)ᴴ = shiftX d κ := by simp
  rw [hX0, e3, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ wd_ne_zero), one_mul]
  ring

/-- `L^{(0)}_n = ∑_k |k⟩⟨k| ⊗ W_{k-n} W_k^*`. -/
lemma Lzero_eq (m : ℕ) :
    Lzero d V m = SB (0 : ZMod d) (fun s => Wblk d V (s - m) * (Wblk d V s)ᴴ) := by
  rw [Lzero, shiftX_pow_conjTranspose, shiftX_pow, Wcov, SB_conj_shift, SB_conjTranspose, SB_mul]
  simp only [neg_zero, add_zero, sub_zero]

/-- `τ(L^{(0)}_n) = (z^{-n}/d) [∑_{k ≥ n} tr(V_{k-n} V_k^*) + i ∑_{k < n} tr(V_{k-n+d} V_k^*)]`
(paper Appendix A), for `1 ≤ n ≤ d - 1`. -/
theorem ntr_Lzero {m : ℕ} (hm0 : 1 ≤ m) (hmd : m < d) :
    ntr (Lzero d V m) = (zd d ^ m)⁻¹ / d *
      (∑ j ∈ range (d - m), ntr (V j * (V (m + j))ᴴ)
        + I * ∑ k ∈ range m, ntr (V (k + (d - m)) * (V k)ᴴ)) := by
  have hd0 : d ≠ 0 := NeZero.ne d
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd0
  rw [Lzero_eq, ntr_SB_zero_gen, ZMod.card, sum_zmod_eq_sum_range]
  have hsplit : range d = range (m + (d - m)) := by rw [Nat.add_sub_cancel' hmd.le]
  rw [hsplit, sum_range_add]
  have hz0 : ∀ k : ℕ, zd d ^ k ≠ 0 := fun k => pow_ne_zero _ zd_ne_zero
  -- the terms with `k ≥ n`
  have hA : ∀ j ∈ range (d - m), ntr (Wblk d V (((m + j : ℕ) : ZMod d) - m) * (Wblk d V ((m + j : ℕ) : ZMod d))ᴴ)
      = (zd d ^ m)⁻¹ * ntr (V j * (V (m + j))ᴴ) := by
    intro j hj
    have hj' := mem_range.1 hj
    have e1 : (((m + j : ℕ) : ZMod d) - m) = (j : ZMod d) := by push_cast; ring
    have e2 : ((j : ℕ) : ZMod d).val = j := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have e3 : ((m + j : ℕ) : ZMod d).val = m + j := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    rw [e1, Wblk, Wblk, e2, e3, conjTranspose_smul, smul_mul_smul_comm, ntr_smul, Complex.star_def,
      conj_zd_pow, pow_add]
    have h1 := hz0 j
    have h2 := hz0 m
    field_simp
  -- the terms with `k < n`
  have hB : ∀ k ∈ range m, ntr (Wblk d V ((k : ℕ) - m) * (Wblk d V (k : ℕ))ᴴ)
      = I * (zd d ^ m)⁻¹ * ntr (V (k + (d - m)) * (V k)ᴴ) := by
    intro k hk
    have hk' := mem_range.1 hk
    have e1 : ((k : ZMod d) - m) = ((k + (d - m) : ℕ) : ZMod d) := by
      rw [Nat.cast_add, Nat.cast_sub hmd.le, ZMod.natCast_self]
      ring
    have e2 : ((k + (d - m) : ℕ) : ZMod d).val = k + (d - m) := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have e3 : ((k : ℕ) : ZMod d).val = k := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    have hzd : zd d ^ (d - m) * zd d ^ m = I := by
      rw [← pow_add, Nat.sub_add_cancel hmd.le, zd_pow_d hd0]
    rw [e1, Wblk, Wblk, e2, e3, conjTranspose_smul, smul_mul_smul_comm, ntr_smul, Complex.star_def,
      conj_zd_pow, pow_add]
    have : zd d ^ k * zd d ^ (d - m) * (zd d ^ k)⁻¹ = I * (zd d ^ m)⁻¹ := by
      have h1 := hz0 k
      have h2 := hz0 m
      rw [← hzd]
      field_simp
    rw [this]
  rw [sum_congr rfl hB, sum_congr rfl hA, ← mul_sum, ← mul_sum]
  ring

/-! ### Theorem 2.3(1) -/

omit [NeZero d] in
lemma I_mul_hd_reflect (hd0 : d ≠ 0) {n : ℕ} (hn : n ≤ d) : I * hd d (d - n) = conj (hd d n) := by
  rw [hd, hd, secd_reflect hd0 hn, cscd_reflect hd0 hn, map_sub, map_mul, Complex.conj_I,
    Complex.conj_ofReal, Complex.conj_ofReal]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Theorem 2.3(1) of the paper (trace form).** For the covariant strategy of order-4 unitaries
`V_0, …, V_{d-1}`: `∑_{n=1}^{d-1} c_n Λ_n(R^V) = -(2/d) F(V)`. -/
theorem sum_cd_Lam_Rcov (hV : ∀ k, IsUnitaryM (V k)) (hV4 : ∀ k, V k ^ 4 = 1) :
    ∑ n ∈ Ico 1 d, cd d n * Lam d (Rcov d V) n = -(2 / (d : ℂ)) * (clockF d V : ℂ) := by
  have hd0 : d ≠ 0 := NeZero.ne d
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd0
  set P : ℂ := ∑ k ∈ range d, ∑ j ∈ range k, hd d (k - j) * ntr (V j * (V k)ᴴ) with hP
  -- each term
  have hterm : ∀ n ∈ Ico 1 d, cd d n * Lam d (Rcov d V) n
      = -(1 / (d : ℂ)) * (hd d n * ∑ j ∈ range (d - n), ntr (V j * (V (n + j))ᴴ)
        + I * hd d n * ∑ k ∈ range n, ntr (V (k + (d - n)) * (V k)ᴴ)) := by
    intro n hn
    have hn' := mem_Ico.1 hn
    have hc : 4 * cd d n * (zd d ^ n)⁻¹ = -hd d n := by
      have h := hd_mul_zd_pow hd0 (by omega : n ≠ 0) hn'.2
      have hz : zd d ^ n ≠ 0 := pow_ne_zero _ zd_ne_zero
      field_simp
      linear_combination h
    rw [Lam_Rcov hV hV4, ntr_Lzero hn'.1 hn'.2]
    linear_combination (1 / (d : ℂ) * (∑ j ∈ range (d - n), ntr (V j * (V (n + j))ᴴ)
      + I * ∑ k ∈ range n, ntr (V (k + (d - n)) * (V k)ᴴ))) * hc
  rw [sum_congr rfl hterm, ← mul_sum, sum_add_distrib]
  -- the first sum is `P`
  have h1 : ∑ n ∈ Ico 1 d, hd d n * ∑ j ∈ range (d - n), ntr (V j * (V (n + j))ᴴ) = P := by
    simp_rw [mul_sum]
    rw [sum_Ico_range_sub (fun n j => hd d n * ntr (V j * (V (n + j))ᴴ)) d, hP]
    refine sum_congr rfl fun k _ => sum_congr rfl fun j hj => ?_
    rw [Nat.sub_add_cancel (mem_range.1 hj).le]
  -- the second sum is `conj P`
  have h2 : ∑ n ∈ Ico 1 d, I * hd d n * ∑ k ∈ range n, ntr (V (k + (d - n)) * (V k)ᴴ) = conj P := by
    rw [← sum_Ico_reflect' (fun n => I * hd d n * ∑ k ∈ range n, ntr (V (k + (d - n)) * (V k)ᴴ)) d]
    have e : ∀ n ∈ Ico 1 d, I * hd d (d - n) * ∑ k ∈ range (d - n), ntr (V (k + (d - (d - n))) * (V k)ᴴ)
        = ∑ k ∈ range (d - n), conj (hd d n * ntr (V k * (V (n + k))ᴴ)) := by
      intro n hn
      have hn' := mem_Ico.1 hn
      rw [I_mul_hd_reflect hd0 hn'.2.le, Nat.sub_sub_self hn'.2.le, mul_sum]
      refine sum_congr rfl fun k _ => ?_
      rw [map_mul, conj_ntr, conjTranspose_mul, conjTranspose_conjTranspose, add_comm k n]
    rw [sum_congr rfl e, sum_Ico_range_sub (fun n k => conj (hd d n * ntr (V k * (V (n + k))ᴴ))) d,
      hP, map_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [map_sum]
    refine sum_congr rfl fun j hj => ?_
    rw [Nat.sub_add_cancel (mem_range.1 hj).le]
  rw [h1, h2, Complex.add_conj]
  have hF : clockF d V = P.re := by
    rw [clockF, hP, re_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [re_sum]
  rw [hF]
  push_cast
  ring

/-! ### The covariant strategy as a projective strategy -/

lemma Rcov_unitary (hV : ∀ k, IsUnitaryM (V k)) (s : ZMod 4) : IsUnitaryM (Rcov d V s) := by
  have hW := (Wcov_unitary (d := d) hV).pow s.val
  exact (hW.mul shiftX_unitary).mul hW.conjTranspose

lemma Rcov_pow_d (hV : ∀ k, IsUnitaryM (V k)) (s : ZMod 4) : Rcov d V s ^ d = 1 := by
  have hW := (Wcov_unitary (d := d) hV).pow s.val
  rw [Rcov, unitary_conj_pow hW, shiftX_pow_d, Matrix.mul_one, hW.mul_conjTranspose]

/-- Alice's measurements of the covariant strategy: `A_1` (index `0`) is the spectral PVM of `R_3`,
`A_2` (index `1`) that of `R_1`. -/
def covA (d : ℕ) [NeZero d] (V : ℕ → Matrix κ κ ℂ) : Fin 2 → ZMod d → Matrix (ZMod d × κ) (ZMod d × κ) ℂ :=
  ![specPVM d (Rcov d V 2), specPVM d (Rcov d V 0)]

/-- Bob's measurements of the covariant strategy: `B_1` (index `0`) is the spectral PVM of `R_4ᵀ`,
`B_2` (index `1`) that of `R_2ᵀ`. -/
def covB (d : ℕ) [NeZero d] (V : ℕ → Matrix κ κ ℂ) : Fin 2 → ZMod d → Matrix (ZMod d × κ) (ZMod d × κ) ℂ :=
  ![specPVM d (Rcov d V 3)ᵀ, specPVM d (Rcov d V 1)ᵀ]

lemma covA_isPVM (hV : ∀ k, IsUnitaryM (V k)) (x : Fin 2) : IsPVM (covA d V x) := by
  fin_cases x
  · exact specPVM_isPVM (Rcov_unitary hV 2) (Rcov_pow_d hV 2)
  · exact specPVM_isPVM (Rcov_unitary hV 0) (Rcov_pow_d hV 0)

lemma transpose_pow_d {R : Matrix (ZMod d × κ) (ZMod d × κ) ℂ} (hR : R ^ d = 1) : Rᵀ ^ d = 1 := by
  rw [← transpose_pow, hR, transpose_one]

lemma covB_isPVM (hV : ∀ k, IsUnitaryM (V k)) (y : Fin 2) : IsPVM (covB d V y) := by
  fin_cases y
  · exact specPVM_isPVM (Rcov_unitary hV 3).transpose (transpose_pow_d (Rcov_pow_d hV 3))
  · exact specPVM_isPVM (Rcov_unitary hV 1).transpose (transpose_pow_d (Rcov_pow_d hV 1))

lemma vec4_self {M : Type*} (f : ZMod 4 → M) : vec4 (f 0) (f 1) (f 2) (f 3) = f := by
  funext s
  obtain rfl | rfl | rfl | rfl : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by revert s; decide
  · exact vec4_zero _ _ _ _
  · exact vec4_one _ _ _ _
  · exact vec4_two _ _ _ _
  · exact vec4_three _ _ _ _

/-- The chain unitaries of the covariant strategy are `R^V`. -/
theorem chainR_cov (hV : ∀ k, IsUnitaryM (V k)) : chainR (covA d V) (covB d V) = Rcov d V := by
  unfold chainR covA covB
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [pvmU_specPVM (Rcov_pow_d hV 0), pvmU_specPVM (transpose_pow_d (Rcov_pow_d hV 1)),
    pvmU_specPVM (Rcov_pow_d hV 2), pvmU_specPVM (transpose_pow_d (Rcov_pow_d hV 3)),
    transpose_transpose, transpose_transpose]
  exact vec4_self _

/-- **Theorem 2.3(1) of the paper.** For order-4 unitaries `V_0, …, V_{d-1}` (`d ≥ 2`), the covariant
strategy `R^V`, realised by projective measurements on the maximally entangled state of `ℂ^d ⊗ ℂ^M`, has
`S(R^V) = 2(d-1) - (2/d) F(V)` and `I_d(R^V) = 4F(V)/(d(d-1))`. -/
theorem cglmp_cov [Nonempty κ] (hd : 2 ≤ d) (hV : ∀ k, IsUnitaryM (V k)) (hV4 : ∀ k, V k ^ 4 = 1) :
    chainS (probME (covA d V) (covB d V)) = 2 * ((d : ℝ) - 1) - 2 / d * clockF d V ∧
    cglmp (probME (covA d V) (covB d V)) = 4 * clockF d V / ((d : ℝ) * ((d : ℝ) - 1)) := by
  have hS : chainS (probME (covA d V) (covB d V)) = 2 * ((d : ℝ) - 1) - 2 / d * clockF d V := by
    have h := chainS_trace (covA d V) (covB d V) (covA_isPVM hV) (covB_isPVM hV)
    rw [chainR_cov hV, sum_cd_Lam_Rcov hV hV4] at h
    have h' := congrArg Complex.re h
    simp only [Complex.ofReal_re] at h'
    rw [h']
    simp
    ring
  refine ⟨hS, ?_⟩
  rw [cglmp_eq_chain hd _ (probME_normalised _ _ (covA_isPVM hV) (covB_isPVM hV)), hS]
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  field_simp
  ring

end Covariant

end

end OQP27.Red
