import OQP27.ReductionCovariant

/-!
# OQP 27B, module L2 (reduction), part 9: `R` is a direct summand of `R^V` (paper Theorem 2.3(2))

Paper: `publish/CGLMP/paper-classical-all-d/main.tex`, Theorem 2.3(2) and Appendix A ("Twirl: proof of (2)").

In the twirl `R̃ = ⊕_{r ∈ ℤ_{4d}} ρ^r(R)` the strategy `R` is the summand `r = 0`; in the basis
`e_{k,s,v} = R̃_1^k f_{s,v}` of the appendix this summand is the range of the isometry
`J v = d^{-1/2} ∑_k |k⟩ ⊗ |0⟩ ⊗ R_1^{-k} v`.  We prove directly, for the reduced family `V = Vred R`:

* `OQP27.Red.Jt_isometry`: `J^* J = 1`;
* `OQP27.Red.direct_summand`: `R^V_i J = J R_i` for `i = 1, …, 4`.

So `R` is unitarily equivalent to the restriction of `R^V` to the invariant subspace `ran J` (a direct
summand, since the `R^V_i` are unitary).  All PROVED, no hypotheses.
-/

namespace OQP27.Red

open Complex Finset ComplexConjugate Matrix

noncomputable section

/-! ### Block rows -/

section BlockRows

variable {d : ℕ} [NeZero d] {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

/-- The `k`-th block row `M_k` of a matrix `M` on `(ℤ/d × κ) × ι`. -/
def brow (M : Matrix (ZMod d × κ) ι ℂ) (k : ZMod d) : Matrix κ ι ℂ := Matrix.of fun x α => M (k, x) α

omit [Fintype ι] [DecidableEq ι] in
lemma shiftX_mul_brow (M : Matrix (ZMod d × κ) ι ℂ) (k : ZMod d) :
    brow (shiftX d κ * M) k = brow M (k - 1) := by
  ext x α
  simp only [brow, of_apply]
  rw [mul_apply, Fintype.sum_prod_type]
  have h : ∀ (k' : ZMod d) (x' : κ),
      shiftX d κ (k, x) (k', x') * M (k', x') α
        = if k' = k - 1 then (1 : Matrix κ κ ℂ) x x' * M (k', x') α else 0 := by
    intro k' x'
    rw [shiftX, SB_apply, ← sub_eq_add_neg]
    split_ifs <;> simp
  simp_rw [h, sum_ite_irrel, sum_const_zero]
  rw [sum_ite_eq' univ (k - 1), if_pos (mem_univ _)]
  simp [one_apply]

omit [DecidableEq κ] [Fintype ι] [DecidableEq ι] in
lemma SB_zero_conjTranspose_mul_brow (B : ZMod d → Matrix κ κ ℂ) (M : Matrix (ZMod d × κ) ι ℂ)
    (k : ZMod d) : brow ((SB (0 : ZMod d) B)ᴴ * M) k = (B k)ᴴ * brow M k := by
  ext x α
  simp only [brow, of_apply]
  rw [mul_apply, mul_apply, Fintype.sum_prod_type]
  have h : ∀ (k' : ZMod d) (x' : κ),
      (SB (0 : ZMod d) B)ᴴ (k, x) (k', x') * M (k', x') α
        = if k' = k then (B k)ᴴ x x' * M (k', x') α else 0 := by
    intro k' x'
    rw [conjTranspose_apply, SB_apply, add_zero]
    by_cases hk : k = k'
    · subst hk
      simp [conjTranspose_apply]
    · simp [hk, Ne.symm hk]
  simp_rw [h, sum_ite_irrel, sum_const_zero]
  rw [sum_ite_eq' univ k, if_pos (mem_univ _)]
  rfl

omit [DecidableEq κ] [Fintype ι] [DecidableEq ι] in
lemma conjTranspose_mul_self_brow (M : Matrix (ZMod d × κ) ι ℂ) :
    Mᴴ * M = ∑ k : ZMod d, (brow M k)ᴴ * brow M k := by
  ext α α'
  rw [mul_apply, Fintype.sum_prod_type, Matrix.sum_apply]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_apply]
  rfl

omit [NeZero d] [Fintype κ] [DecidableEq κ] [DecidableEq ι] in
lemma brow_mul (M : Matrix (ZMod d × κ) ι ℂ) (N : Matrix ι ι ℂ) (k : ZMod d) :
    brow (M * N) k = brow M k * N := by
  ext x α
  simp only [brow, of_apply, mul_apply]

omit [NeZero d] [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι] in
lemma eq_of_brow {M N : Matrix (ZMod d × κ) ι ℂ} (h : ∀ k, brow M k = brow N k) : M = N := by
  ext ⟨k, x⟩ α
  have := congrFun (congrFun (h k) x) α
  simpa [brow] using this

end BlockRows

/-! ### The column embeddings `E_t` -/

section Ecol

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `E_t v = |t⟩ ⊗ v` (`t ∈ ℤ/4`). -/
def Ecol (t : ZMod 4) : Matrix (ZMod 4 × ι) ι ℂ :=
  Matrix.of fun x γ => if x.1 = t then (1 : Matrix ι ι ℂ) x.2 γ else 0

lemma Ecol_isometry (t : ZMod 4) : (Ecol (ι := ι) t)ᴴ * Ecol (ι := ι) t = 1 := by
  ext γ γ'
  rw [mul_apply, Fintype.sum_prod_type, sum_eq_single t]
  · by_cases h : γ = γ'
    · subst h
      simp [Ecol, conjTranspose_apply, one_apply]
    · simp [Ecol, conjTranspose_apply, one_apply, h, Ne.symm h]
  · intro s _ hs
    simp [Ecol, hs]
  · intro h
    exact absurd (mem_univ t) h

/-- `(SB r B)^* E_t = E_{t+r} (B t)^*`. -/
lemma SB_conjTranspose_mul_Ecol (r : ZMod 4) (B : ZMod 4 → Matrix ι ι ℂ) (t : ZMod 4) :
    (SB r B)ᴴ * Ecol t = Ecol (t + r) * (B t)ᴴ := by
  ext ⟨s, β⟩ γ
  rw [mul_apply, mul_apply, Fintype.sum_prod_type, sum_eq_single t]
  · simp only [Ecol, of_apply, if_true, conjTranspose_apply, SB_apply, one_apply]
    split_ifs with h <;> simp
  · intro x _ hx
    refine sum_eq_zero fun y _ => ?_
    simp [Ecol, hx]
  · intro h
    exact absurd (mem_univ t) h

end Ecol

/-! ### The isometry `J` and the direct summand -/

section Summand

variable {d : ℕ} [NeZero d] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `J_t v = d^{-1/2} ∑_k |k⟩ ⊗ |t⟩ ⊗ (R_{t+1}^k)^* v`. -/
def Jt (d : ℕ) [NeZero d] (R : ZMod 4 → Matrix ι ι ℂ) (t : ZMod 4) :
    Matrix (ZMod d × (ZMod 4 × ι)) ι ℂ :=
  Matrix.of fun p α =>
    (((((Real.sqrt d : ℝ) : ℂ)⁻¹) • (Ecol t * (R t ^ p.1.val)ᴴ) : Matrix (ZMod 4 × ι) ι ℂ)) p.2 α

lemma brow_Jt (R : ZMod 4 → Matrix ι ι ℂ) (t : ZMod 4) (k : ZMod d) :
    brow (Jt d R t) k = (((Real.sqrt d : ℝ) : ℂ)⁻¹) • (Ecol t * (R t ^ k.val)ᴴ) := by
  ext x α
  rfl

omit [NeZero d] in
lemma sqrt_d_sq : star (((Real.sqrt d : ℝ) : ℂ)⁻¹) * (((Real.sqrt d : ℝ) : ℂ)⁻¹) = (d : ℂ)⁻¹ := by
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (Nat.cast_nonneg d)]
  push_cast
  rfl

/-- **`J_t` is an isometry**: `J_t^* J_t = 1`. -/
theorem Jt_isometry (R : ZMod 4 → Matrix ι ι ℂ) (t : ZMod 4) (hR : IsUnitaryM (R t)) :
    (Jt d R t)ᴴ * Jt d R t = 1 := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  rw [conjTranspose_mul_self_brow]
  have e : ∀ k : ZMod d, (brow (Jt d R t) k)ᴴ * brow (Jt d R t) k = (d : ℂ)⁻¹ • (1 : Matrix ι ι ℂ) := by
    intro k
    rw [brow_Jt, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, sqrt_d_sq,
      conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc (Ecol t)ᴴ,
      Ecol_isometry, Matrix.one_mul, (hR.pow k.val).mul_conjTranspose]
  rw [sum_congr rfl fun k _ => e k, sum_const, card_univ, ZMod.card, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul, mul_inv_cancel₀ hd, one_smul]

lemma pow_val_pred (R : Matrix ι ι ℂ) (hRd : R ^ d = 1) (k : ZMod d) :
    R ^ k.val = R * R ^ (k - 1).val := by
  have h1 : R ^ (1 : ZMod d).val = R := by
    rcases Nat.lt_or_ge d 2 with hd | hd
    · have hd1 : d = 1 := by have := NeZero.ne d; omega
      subst hd1
      rw [pow_one] at hRd
      rw [hRd, one_pow]
    · have : Fact (1 < d) := ⟨by omega⟩
      rw [ZMod.val_one, pow_one]
  conv_lhs => rw [show k = 1 + (k - 1) by ring]
  rw [pow_val_add_n hRd, h1]

/-- `(X ⊗ 1) J_t = J_t R_{t+1}`. -/
theorem shiftX_mul_Jt (R : ZMod 4 → Matrix ι ι ℂ) (t : ZMod 4) (hR : IsUnitaryM (R t))
    (hRd : R t ^ d = 1) : shiftX d (ZMod 4 × ι) * Jt d R t = Jt d R t * R t := by
  apply eq_of_brow
  intro k
  rw [shiftX_mul_brow, brow_mul, brow_Jt, brow_Jt, Matrix.smul_mul, Matrix.mul_assoc]
  congr 2
  rw [pow_val_pred (R t) hRd k, conjTranspose_mul, Matrix.mul_assoc, hR, Matrix.mul_one]

/-- `W^* J_t = J_{t+1}` for `t ≠ 3` (the block of `W` at `s = t` carries no phase). -/
theorem Wcov_conjTranspose_mul_Jt (R : ZMod 4 → Matrix ι ι ℂ) (hR : ∀ s, IsUnitaryM (R s))
    {t : ZMod 4} (ht : t ≠ 3) :
    (Wcov d (Vred d R))ᴴ * Jt d R t = Jt d R (t + 1) := by
  apply eq_of_brow
  intro k
  rw [Wcov, SB_zero_conjTranspose_mul_brow, brow_Jt, brow_Jt, Wblk, Vred, conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc, SB_conjTranspose_mul_Ecol, blk,
    if_neg ht, mul_one, conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, Matrix.mul_assoc,
    (hR t).pow_mul_conjTranspose_pow, Matrix.mul_one]
  congr 1
  rw [star_inv₀]
  have hz : star (zd d ^ k.val) ≠ 0 := star_ne_zero.2 (pow_ne_zero _ zd_ne_zero)
  field_simp

lemma Wpow_conjTranspose_mul_Jt (R : ZMod 4 → Matrix ι ι ℂ) (hR : ∀ s, IsUnitaryM (R s)) :
    ∀ m : ℕ, m ≤ 3 → (Wcov d (Vred d R) ^ m)ᴴ * Jt d R 0 = Jt d R (m : ZMod 4)
  | 0, _ => by simp
  | m + 1, hm => by
    have ih := Wpow_conjTranspose_mul_Jt R hR m (by omega)
    have hm3 : (m : ZMod 4) ≠ 3 := by
      intro h
      have := congrArg ZMod.val h
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), show (3 : ZMod 4).val = 3 from rfl] at this
      omega
    rw [pow_succ, conjTranspose_mul, Matrix.mul_assoc, ih, Wcov_conjTranspose_mul_Jt R hR hm3,
      Nat.cast_succ]

/-- **Theorem 2.3(2), "direct summand" clause.** For a chain of unitaries `R_1, …, R_4` with `R_i^d = 1`
and its reduced family `V`, the isometry `J = J_0` (`J^* J = 1`, `OQP27.Red.Jt_isometry`) intertwines `R` with
the covariant strategy: `R^V_i J = J R_i` for `i = 1, …, 4`.  Hence `R` is unitarily equivalent to the
restriction of `R^V` to the invariant subspace `ran J`. -/
theorem direct_summand (R : ZMod 4 → Matrix ι ι ℂ) (hR : ∀ s, IsUnitaryM (R s))
    (hRd : ∀ s, R s ^ d = 1) (s : ZMod 4) :
    Rcov d (Vred d R) s * Jt d R 0 = Jt d R 0 * R s := by
  have hW := Wcov_unitary (d := d) (Vred_unitary (d := d) R hR)
  have hWs := hW.pow s.val
  have h1 : (Wcov d (Vred d R) ^ s.val)ᴴ * Jt d R 0 = Jt d R s := by
    rw [Wpow_conjTranspose_mul_Jt R hR s.val (by have := ZMod.val_lt s; omega),
      ZMod.natCast_zmod_val]
  have h2 : Wcov d (Vred d R) ^ s.val * Jt d R s = Jt d R 0 := by
    rw [← h1, ← Matrix.mul_assoc, hWs.mul_conjTranspose, Matrix.one_mul]
  rw [Rcov, Matrix.mul_assoc, h1, Matrix.mul_assoc, shiftX_mul_Jt R s (hR s) (hRd s),
    ← Matrix.mul_assoc, h2]

end Summand

end

end OQP27.Red
