import OQP27.ReductionChain

/-!
# OQP 27B, module L2 (reduction), part 3: the clock model and the reduced family

Paper: `publish/CGLMP/paper-classical-all-d/main.tex`, Section 2.3 (Theorem 2.3) and Appendix A
("Twirl: proof of (2)").

For a chain `R_1, …, R_4` of unitaries with `R_i^d = 1` (stored as `R s = R_{s+1}`, `s ∈ ℤ/4`) the twirl of
the appendix is `R̃_i = ⊕_{r ∈ ℤ_{4d}} (ρ^r R)_i`, `ρ(R) = (R_2, R_3, R_4, w R_1)`. Its eigenspace
`H_0 = ker(W^4 - 1)` of the shift `W` consists of the vectors that are `4`-periodic in `r`, and in the basis
`f_{s,v} = d^{-1/2} ∑_j e_{s+4j} ⊗ v` (`s ∈ ℤ/4`) of `H_0 ≅ ℂ^4 ⊗ ℂ^D` the operators
`W_k = R̃_1^{-k} W R̃_1^k |_{H_0}` of the appendix are explicit block shifts:
`(W_k φ)(s) = R_{s+1}^{-k} R_{s+2}^k φ(s+1)` (with `R_5 = w R_1`). So the reduced family of the paper
(`V_k = z^{-k} W_k`, `M = 4D`) is

  `V_k = ∑_s |s⟩⟨s+1| ⊗ z^{-k} R_{s+1}^{-k} R_{s+2}^k`   (`OQP27.Red.Vred`).

Main results (all PROVED, no hypotheses):
* `OQP27.Red.Vred_unitary`, `OQP27.Red.Vred_pow_four`: `V_k` is unitary and `V_k^4 = 1`.
* `OQP27.Red.ntr_Vred`: `tr(V_j V_k^*) = z^{k-j} Λ_{k-j}(R) / 4` for `j ≤ k`.
* `OQP27.Red.clockF_Vred`: `F(V) = -∑_{n=1}^{d-1} (d-n) Re(c_n Λ_n(R))`, `F` the clock functional of paper
  eq. (F).
* `OQP27.Red.chainS_eq_clockF` (**Theorem 2.3(2)**, trace form): `S = 2(d-1) - (2/d) F(V)` for the reduced
  family of the chain unitaries of any projective strategy on the maximally entangled state;
* `OQP27.Red.cglmp_eq_clockF`: hence `I_d = 4 F(V) / (d(d-1))`.
-/

namespace OQP27.Red

open Complex Finset ComplexConjugate Matrix

noncomputable section

variable {d : ℕ}

/-! ### Unitary matrices and their powers -/

section Unitary

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- A unitary matrix: `Uᴴ U = 1` (for square matrices this implies `U Uᴴ = 1`). -/
def IsUnitaryM (U : Matrix κ κ ℂ) : Prop := Uᴴ * U = 1

variable {U : Matrix κ κ ℂ}

lemma IsUnitaryM.mul_conjTranspose (hU : IsUnitaryM U) : U * Uᴴ = 1 := mul_eq_one_comm.1 hU

lemma IsUnitaryM.pow_mul_conjTranspose_pow (hU : IsUnitaryM U) : ∀ n : ℕ, U ^ n * (U ^ n)ᴴ = 1
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, conjTranspose_mul, mul_assoc, ← mul_assoc U, hU.mul_conjTranspose, one_mul,
      hU.pow_mul_conjTranspose_pow n]

lemma IsUnitaryM.conjTranspose_pow_mul_pow (hU : IsUnitaryM U) (n : ℕ) : (U ^ n)ᴴ * U ^ n = 1 :=
  mul_eq_one_comm.1 (hU.pow_mul_conjTranspose_pow n)

lemma IsUnitaryM.pow_add_mul_conjTranspose (hU : IsUnitaryM U) (m n : ℕ) :
    U ^ (n + m) * (U ^ m)ᴴ = U ^ n := by
  rw [pow_add, mul_assoc, hU.pow_mul_conjTranspose_pow, mul_one]

lemma IsUnitaryM.pow_mul_conjTranspose_pow_add (hU : IsUnitaryM U) (m n : ℕ) :
    U ^ m * (U ^ (n + m))ᴴ = (U ^ n)ᴴ := by
  rw [pow_add, conjTranspose_mul, ← mul_assoc, hU.pow_mul_conjTranspose_pow, one_mul]

lemma IsUnitaryM.pow_sub_eq (hU : IsUnitaryM U) (hd : U ^ d = 1) {n : ℕ} (hn : n ≤ d) :
    U ^ (d - n) = (U ^ n)ᴴ := by
  have h := hU.pow_add_mul_conjTranspose n (d - n)
  rw [Nat.sub_add_cancel hn, hd, one_mul] at h
  exact h.symm

lemma IsUnitaryM.mul {V : Matrix κ κ ℂ} (hU : IsUnitaryM U) (hV : IsUnitaryM V) :
    IsUnitaryM (U * V) := by
  unfold IsUnitaryM at *
  rw [conjTranspose_mul, mul_assoc, ← mul_assoc Uᴴ, hU, one_mul, hV]

lemma IsUnitaryM.conjTranspose (hU : IsUnitaryM U) : IsUnitaryM Uᴴ := by
  unfold IsUnitaryM
  rw [conjTranspose_conjTranspose]
  exact hU.mul_conjTranspose

lemma IsUnitaryM.pow (hU : IsUnitaryM U) (n : ℕ) : IsUnitaryM (U ^ n) :=
  hU.conjTranspose_pow_mul_pow n

lemma IsUnitaryM.smul (hU : IsUnitaryM U) {c : ℂ} (hc : conj c * c = 1) : IsUnitaryM (c • U) := by
  unfold IsUnitaryM at *
  have hc' : star c * c = 1 := by rw [Complex.star_def]; exact hc
  rw [conjTranspose_smul, smul_mul_smul_comm, hU, hc', one_smul]

end Unitary

/-! ### Block-shift matrices on `ℤ/4 × κ` -/

section Block

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The block matrix on `G × κ` (`G` a finite abelian group, e.g. `ℤ/4` or `ℤ/d`) whose block `(s, s + r)`
is `B s` (all other blocks vanish). -/
def SB (r : G) (B : G → Matrix κ κ ℂ) : Matrix (G × κ) (G × κ) ℂ :=
  Matrix.of fun p q => if q.1 = p.1 + r then B p.1 p.2 q.2 else 0

omit [Fintype κ] [DecidableEq κ] [Fintype G] in
lemma SB_apply (r : G) (B : G → Matrix κ κ ℂ) (p q : G × κ) :
    SB r B p q = if q.1 = p.1 + r then B p.1 p.2 q.2 else 0 := rfl

omit [DecidableEq κ] in
lemma SB_mul (r r' : G) (B B' : G → Matrix κ κ ℂ) :
    SB r B * SB r' B' = SB (r + r') (fun s => B s * B' (s + r)) := by
  ext ⟨s, α⟩ ⟨t, β⟩
  rw [mul_apply, Fintype.sum_prod_type, SB_apply]
  simp only [SB_apply, ite_mul, zero_mul]
  rw [sum_comm, sum_congr rfl fun γ _ => sum_ite_eq' univ (s + r) _]
  simp only [mem_univ, if_true, mul_ite, mul_zero]
  rw [sum_ite_irrel, sum_const_zero]
  by_cases h : t = s + (r + r')
  · rw [if_pos (by rw [h, add_assoc]), if_pos h, mul_apply]
  · rw [if_neg (by rw [add_assoc]; exact h), if_neg h]

omit [Fintype κ] [DecidableEq κ] [Fintype G] in
lemma SB_conjTranspose (r : G) (B : G → Matrix κ κ ℂ) :
    (SB r B)ᴴ = SB (-r) (fun s => (B (s - r))ᴴ) := by
  ext ⟨s, α⟩ ⟨t, β⟩
  rw [conjTranspose_apply, SB_apply, SB_apply]
  simp only
  by_cases h : s = t + r
  · rw [if_pos h, if_pos (by rw [h]; abel), conjTranspose_apply, show t = s - r by rw [h]; abel]
  · rw [if_neg h, if_neg (by intro h'; apply h; rw [h']; abel), star_zero]

omit [Fintype κ] [Fintype G] in
lemma SB_zero_of_eq_one (B : G → Matrix κ κ ℂ) (hB : ∀ s, B s = 1) : SB 0 B = 1 := by
  ext ⟨s, α⟩ ⟨t, β⟩
  rw [SB_apply, one_apply, add_zero, hB, one_apply]
  simp only [Prod.mk.injEq]
  by_cases h : t = s
  · subst h
    simp
  · rw [if_neg h, if_neg (by tauto)]

omit [DecidableEq κ] in
lemma trace_SB_zero (B : G → Matrix κ κ ℂ) : trace (SB 0 B) = ∑ s, trace (B s) := by
  rw [trace, Fintype.sum_prod_type]
  refine sum_congr rfl fun s _ => ?_
  rw [trace]
  refine sum_congr rfl fun α _ => ?_
  rw [diag_apply, SB_apply, add_zero, if_pos rfl]
  rfl

omit [DecidableEq κ] in
lemma ntr_SB_zero_gen (B : G → Matrix κ κ ℂ) :
    ntr (SB 0 B) = (∑ s, ntr (B s)) / Fintype.card G := by
  rw [ntr, trace_SB_zero, Fintype.card_prod]
  unfold ntr
  rw [← sum_div]
  push_cast
  rw [mul_comm (Fintype.card G : ℂ), div_div]

omit [DecidableEq κ] in
lemma ntr_SB_zero (B : ZMod 4 → Matrix κ κ ℂ) :
    ntr (SB 0 B) = (∑ s, ntr (B s)) / 4 := by
  rw [ntr_SB_zero_gen, ZMod.card]
  push_cast
  rfl

end Block

/-! ### The clock functional and the reduced family -/

section Clock

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **The clock functional**, paper eq. (F): `F(V) = ∑_{0 ≤ j < k ≤ d-1} Re[h_{k-j} tr(V_j V_k^*)]`,
`tr` the normalised trace. The family is indexed by `ℕ`; only `V 0, …, V (d-1)` enter. -/
def clockF (d : ℕ) (V : ℕ → Matrix κ κ ℂ) : ℝ :=
  ∑ k ∈ range d, ∑ j ∈ range k, (hd d (k - j) * ntr (V j * (V k)ᴴ)).re

/-- The blocks `z^{-k} R_{s+1}^{-k} R_{s+2}^k` of the reduced family (with `R_5 = w R_1`). -/
def blk (d : ℕ) (R : ZMod 4 → Matrix κ κ ℂ) (k : ℕ) (s : ZMod 4) : Matrix κ κ ℂ :=
  ((zd d ^ k)⁻¹ * (if s = 3 then wd d ^ k else 1)) • ((R s ^ k)ᴴ * R (s + 1) ^ k)

/-- **The reduced family** of a chain `R` (paper, Theorem 2.3(2) and its appendix, for the basis
`f_{s,v}` of `H_0` described in the module docstring): `V_k = ∑_s |s⟩⟨s+1| ⊗ z^{-k} R_{s+1}^{-k} R_{s+2}^k`,
a family of matrices of size `M = 4D`. -/
def Vred (d : ℕ) (R : ZMod 4 → Matrix κ κ ℂ) (k : ℕ) : Matrix (ZMod 4 × κ) (ZMod 4 × κ) ℂ :=
  SB 1 (blk d R k)

lemma Vred_mul_conjTranspose (R : ZMod 4 → Matrix κ κ ℂ) (j k : ℕ) :
    Vred d R j * (Vred d R k)ᴴ = SB 0 (fun s => blk d R j s * (blk d R k s)ᴴ) := by
  rw [Vred, Vred, SB_conjTranspose, SB_mul, add_neg_cancel]
  simp only [add_sub_cancel_right]

lemma conj_blk_coeff (k : ℕ) (s : ZMod 4) :
    conj ((zd d ^ k)⁻¹ * (if s = 3 then wd d ^ k else 1))
      = zd d ^ k * (if s = 3 then (wd d ^ k)⁻¹ else 1) := by
  rw [map_mul, map_inv₀, conj_zd_pow, inv_inv]
  split_ifs
  · rw [conj_wd_pow]
  · rw [map_one]

/-- `tr(B_j(s) B_k(s)^*) = z^{k-j} · (phase) · τ(R_{s+1}^{k-j} R_{s+2}^{-(k-j)})` for `j ≤ k`. -/
lemma ntr_blk (R : ZMod 4 → Matrix κ κ ℂ) (hR : ∀ s, IsUnitaryM (R s)) {j k : ℕ}
    (hjk : j ≤ k) (s : ZMod 4) :
    ntr (blk d R j s * (blk d R k s)ᴴ)
      = zd d ^ (k - j) * (twist d s (k - j) * ntr (R s ^ (k - j) * (R (s + 1) ^ (k - j))ᴴ)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hjk
  rw [Nat.add_sub_cancel_left]
  unfold blk
  rw [conjTranspose_smul, smul_mul_smul_comm, conjTranspose_mul, conjTranspose_conjTranspose]
  -- the matrix part
  have hm : (R s ^ j)ᴴ * R (s + 1) ^ j * ((R (s + 1) ^ (j + n))ᴴ * R s ^ (j + n))
      = (R s ^ j)ᴴ * ((R (s + 1) ^ n)ᴴ * R s ^ (j + n)) := by
    rw [mul_assoc, ← mul_assoc (R (s + 1) ^ j), add_comm j n,
      (hR (s + 1)).pow_mul_conjTranspose_pow_add j n]
  rw [hm]
  have ht : trace ((R s ^ j)ᴴ * ((R (s + 1) ^ n)ᴴ * R s ^ (n + j)))
      = trace (R s ^ n * (R (s + 1) ^ n)ᴴ) := by
    rw [trace_mul_comm, mul_assoc, (hR s).pow_add_mul_conjTranspose j n, trace_mul_comm]
  unfold ntr
  rw [trace_smul, add_comm j n, ht, smul_eq_mul, Complex.star_def, conj_blk_coeff, twist]
  have hz : zd d ^ (n + j) = zd d ^ n * zd d ^ j := pow_add _ _ _
  have hw : wd d ^ (n + j) = wd d ^ n * wd d ^ j := pow_add _ _ _
  have hz0 : zd d ^ j ≠ 0 := pow_ne_zero _ zd_ne_zero
  have hw0 : wd d ^ j ≠ 0 := pow_ne_zero _ wd_ne_zero
  have hw0' : wd d ^ n ≠ 0 := pow_ne_zero _ wd_ne_zero
  split_ifs
  · rw [hz, hw]
    field_simp
  · rw [hz]
    field_simp

/-- **`tr(V_j V_k^*) = z^{k-j} Λ_{k-j}(R)/4`** for `j ≤ k` (reduced family of a unitary chain). -/
theorem ntr_Vred (R : ZMod 4 → Matrix κ κ ℂ) (hR : ∀ s, IsUnitaryM (R s)) {j k : ℕ}
    (hjk : j ≤ k) :
    ntr (Vred d R j * (Vred d R k)ᴴ) = zd d ^ (k - j) * Lam d R (k - j) / 4 := by
  rw [Vred_mul_conjTranspose, ntr_SB_zero]
  simp_rw [ntr_blk R hR hjk]
  rw [← mul_sum, Lam]

lemma blk_coeff_unimod (k : ℕ) (s : ZMod 4) :
    conj ((zd d ^ k)⁻¹ * (if s = 3 then wd d ^ k else 1))
      * ((zd d ^ k)⁻¹ * (if s = 3 then wd d ^ k else 1)) = 1 := by
  rw [conj_blk_coeff]
  have hz0 : zd d ^ k ≠ 0 := pow_ne_zero _ zd_ne_zero
  have hw0 : wd d ^ k ≠ 0 := pow_ne_zero _ wd_ne_zero
  split_ifs
  · field_simp
  · field_simp

lemma blk_unitary (R : ZMod 4 → Matrix κ κ ℂ) (hR : ∀ s, IsUnitaryM (R s)) (k : ℕ)
    (s : ZMod 4) : IsUnitaryM (blk d R k s) :=
  (((hR s).pow k).conjTranspose.mul ((hR (s + 1)).pow k)).smul (blk_coeff_unimod k s)

/-- The reduced family consists of unitaries. -/
theorem Vred_unitary (R : ZMod 4 → Matrix κ κ ℂ) (hR : ∀ s, IsUnitaryM (R s))
    (k : ℕ) : IsUnitaryM (Vred d R k) := by
  unfold IsUnitaryM Vred
  rw [SB_conjTranspose, SB_mul, neg_add_cancel]
  apply SB_zero_of_eq_one
  intro s
  rw [← sub_eq_add_neg]
  exact blk_unitary R hR k (s - 1)

lemma zmod4_add_four (t : ZMod 4) : t + 1 + 1 + 1 + 1 = t := by
  fin_cases t <;> rfl

lemma phase_prod (k : ℕ) (s : ZMod 4) :
    (if s = 3 then wd d ^ k else 1) * (if s + 1 = 3 then wd d ^ k else 1)
      * (if s + 1 + 1 = 3 then wd d ^ k else 1) * (if s + 1 + 1 + 1 = 3 then wd d ^ k else 1)
      = wd d ^ k := by
  obtain rfl | rfl | rfl | rfl : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by revert s; decide
  all_goals simp +decide

/-- The cyclic product of the four blocks of `V_k` is `1`. -/
lemma blk_cyclic (hd0 : d ≠ 0) (R : ZMod 4 → Matrix κ κ ℂ) (hR : ∀ s, IsUnitaryM (R s)) (k : ℕ)
    (s : ZMod 4) :
    blk d R k s * blk d R k (s + 1) * blk d R k (s + 1 + 1) * blk d R k (s + 1 + 1 + 1) = 1 := by
  unfold blk
  simp only [smul_mul_smul_comm]
  have hM : (R s ^ k)ᴴ * R (s + 1) ^ k * ((R (s + 1) ^ k)ᴴ * R (s + 1 + 1) ^ k)
      * ((R (s + 1 + 1) ^ k)ᴴ * R (s + 1 + 1 + 1) ^ k)
      * ((R (s + 1 + 1 + 1) ^ k)ᴴ * R (s + 1 + 1 + 1 + 1) ^ k) = 1 := by
    rw [zmod4_add_four]
    simp only [mul_assoc]
    rw [← mul_assoc (R (s + 1) ^ k), (hR (s + 1)).pow_mul_conjTranspose_pow, one_mul,
      ← mul_assoc (R (s + 1 + 1) ^ k), (hR (s + 1 + 1)).pow_mul_conjTranspose_pow, one_mul,
      ← mul_assoc (R (s + 1 + 1 + 1) ^ k), (hR (s + 1 + 1 + 1)).pow_mul_conjTranspose_pow, one_mul,
      (hR s).conjTranspose_pow_mul_pow]
  rw [hM]
  have hc : (zd d ^ k)⁻¹ * (if s = 3 then wd d ^ k else 1)
      * ((zd d ^ k)⁻¹ * (if s + 1 = 3 then wd d ^ k else 1))
      * ((zd d ^ k)⁻¹ * (if s + 1 + 1 = 3 then wd d ^ k else 1))
      * ((zd d ^ k)⁻¹ * (if s + 1 + 1 + 1 = 3 then wd d ^ k else 1)) = 1 := by
    have h4 : (zd d ^ k) ^ 4 = wd d ^ k := by rw [← pow_mul, mul_comm, pow_mul, zd_pow_four hd0]
    have hp := phase_prod (d := d) k s
    have hz0 : zd d ^ k ≠ 0 := pow_ne_zero _ zd_ne_zero
    calc (zd d ^ k)⁻¹ * (if s = 3 then wd d ^ k else 1)
          * ((zd d ^ k)⁻¹ * (if s + 1 = 3 then wd d ^ k else 1))
          * ((zd d ^ k)⁻¹ * (if s + 1 + 1 = 3 then wd d ^ k else 1))
          * ((zd d ^ k)⁻¹ * (if s + 1 + 1 + 1 = 3 then wd d ^ k else 1))
        = ((zd d ^ k) ^ 4)⁻¹ * ((if s = 3 then wd d ^ k else 1) * (if s + 1 = 3 then wd d ^ k else 1)
            * (if s + 1 + 1 = 3 then wd d ^ k else 1) * (if s + 1 + 1 + 1 = 3 then wd d ^ k else 1)) := by
          rw [← inv_pow]
          ring
      _ = 1 := by rw [hp, h4, inv_mul_cancel₀ (pow_ne_zero _ wd_ne_zero)]
  rw [hc, one_smul]

/-- The reduced family consists of unitaries of order dividing four: `V_k^4 = 1`. -/
theorem Vred_pow_four (hd0 : d ≠ 0) (R : ZMod 4 → Matrix κ κ ℂ) (hR : ∀ s, IsUnitaryM (R s))
    (k : ℕ) : Vred d R k ^ 4 = 1 := by
  have e : Vred d R k ^ 4 = Vred d R k * Vred d R k * Vred d R k * Vred d R k := by
    rw [pow_succ, pow_succ, pow_succ, pow_one]
  rw [e, Vred, SB_mul, SB_mul, SB_mul]
  have h4 : (1 : ZMod 4) + 1 + 1 + 1 = 0 := rfl
  rw [h4]
  apply SB_zero_of_eq_one
  intro s
  have := blk_cyclic hd0 R hR k s
  simpa [add_assoc] using this

/-! ### `F` of the reduced family -/

/-- `∑_{0 ≤ j < k < d} g(k - j) = ∑_{n=1}^{d-1} (d - n) g(n)`. -/
lemma sum_pairs (g : ℕ → ℝ) (d : ℕ) :
    ∑ k ∈ range d, ∑ j ∈ range k, g (k - j) = ∑ n ∈ Ico 1 d, ((d : ℝ) - n) * g n := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [sum_range_succ, ih]
    have h1 : ∑ j ∈ range d, g (d - j) = ∑ n ∈ Ico 1 (d + 1), g n := by
      rw [← sum_range_reflect (fun j => g (d - j)) d, sum_Ico_eq_sum_range]
      refine sum_congr (by simp) fun j hj => ?_
      have := mem_range.1 hj
      congr 1
      omega
    rw [h1]
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · subst h0
      simp
    · rw [sum_Ico_succ_top (by omega : 1 ≤ d), sum_Ico_succ_top (by omega : 1 ≤ d)]
      push_cast
      rw [show ∀ x y z : ℝ, x + (y + z) = x + y + z by intros; ring]
      congr 1
      · rw [← sum_add_distrib]
        refine sum_congr rfl fun n _ => ?_
        ring
      · ring

/-- Reflection `n ↦ d - n` of `[1, d)`. -/
lemma sum_Ico_reflect' {M : Type*} [AddCommMonoid M] (f : ℕ → M) (d : ℕ) :
    ∑ n ∈ Ico 1 d, f (d - n) = ∑ n ∈ Ico 1 d, f n := by
  refine Finset.sum_nbij' (fun n => d - n) (fun n => d - n) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    rw [mem_Ico] at hn ⊢
    omega
  · intro n hn
    rw [mem_Ico] at hn ⊢
    omega
  · intro n hn
    rw [mem_Ico] at hn
    omega
  · intro n hn
    rw [mem_Ico] at hn
    omega
  · intro n hn
    rfl

/-- If `g(d - n) = g(n)` on `[1, d)`, then `∑ (d - n) g(n) = (d/2) ∑ g(n)`. -/
lemma sum_symm (g : ℕ → ℝ) (d : ℕ) (hg : ∀ n ∈ Ico 1 d, g (d - n) = g n) :
    ∑ n ∈ Ico 1 d, ((d : ℝ) - n) * g n = (d : ℝ) / 2 * ∑ n ∈ Ico 1 d, g n := by
  have h := sum_Ico_reflect' (fun n => ((d : ℝ) - n) * g n) d
  have h2 : ∑ n ∈ Ico 1 d, ((d : ℝ) - ((d - n : ℕ) : ℝ)) * g (d - n)
      = ∑ n ∈ Ico 1 d, (n : ℝ) * g n := by
    refine sum_congr rfl fun n hn => ?_
    have hn' := mem_Ico.1 hn
    rw [Nat.cast_sub (by omega), hg n hn]
    ring
  rw [h2] at h
  have h3 : ∑ n ∈ Ico 1 d, ((d : ℝ) - n) * g n + ∑ n ∈ Ico 1 d, ((d : ℝ) - n) * g n
      = (d : ℝ) * ∑ n ∈ Ico 1 d, g n := by
    conv_lhs => arg 2; rw [← h]
    rw [← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    ring
  linarith

/-- `F` of the reduced family: `F(V) = -∑_{n=1}^{d-1} (d - n) Re(c_n Λ_n(R))`. -/
theorem clockF_Vred (hd0 : d ≠ 0) (R : ZMod 4 → Matrix κ κ ℂ) (hR : ∀ s, IsUnitaryM (R s)) :
    clockF d (Vred d R) = -∑ n ∈ Ico 1 d, ((d : ℝ) - n) * (cd d n * Lam d R n).re := by
  have step : ∀ k ∈ range d, ∑ j ∈ range k, (hd d (k - j) * ntr (Vred d R j * (Vred d R k)ᴴ)).re
      = ∑ j ∈ range k, -(cd d (k - j) * Lam d R (k - j)).re := by
    intro k hk
    refine sum_congr rfl fun j hj => ?_
    have hk' := mem_range.1 hk
    have hj' := mem_range.1 hj
    rw [ntr_Vred R hR (le_of_lt hj'), ← mul_div_assoc, ← mul_assoc,
      hd_mul_zd_pow hd0 (by omega) (by omega)]
    have : -4 * cd d (k - j) * Lam d R (k - j) / 4 = -(cd d (k - j) * Lam d R (k - j)) := by ring
    rw [this, Complex.neg_re]
  rw [clockF, sum_congr rfl step, sum_pairs (fun n => -(cd d n * Lam d R n).re) d, ← sum_neg_distrib]
  refine sum_congr rfl fun n _ => ?_
  ring

/-- `Λ_{d-n}(R) = conj Λ_n(R)` for a unitary chain with `R_i^d = 1`. -/
theorem Lam_reflect (hd0 : d ≠ 0) (R : ZMod 4 → Matrix κ κ ℂ) (hR : ∀ s, IsUnitaryM (R s))
    (hRd : ∀ s, R s ^ d = 1) {n : ℕ} (hn : n ≤ d) : Lam d R (d - n) = conj (Lam d R n) := by
  rw [Lam, Lam, map_sum]
  refine sum_congr rfl fun s _ => ?_
  rw [(hR s).pow_sub_eq (hRd s) hn, (hR (s + 1)).pow_sub_eq (hRd (s + 1)) hn, map_mul, conj_ntr,
    conjTranspose_mul, conjTranspose_conjTranspose]
  congr 1
  · unfold twist
    split_ifs
    · have h1 : wd d ^ (d - n) * wd d ^ n = 1 := by
        rw [← pow_add, Nat.sub_add_cancel hn, wd_pow_d hd0]
      rw [map_inv₀, conj_wd_pow, inv_inv, inv_eq_of_mul_eq_one_right h1]
    · rw [map_one]
  · unfold ntr
    rw [trace_mul_comm]

/-- The sum `∑ c_n Λ_n` is real and `∑ (d - n) Re(c_n Λ_n) = (d/2) ∑ Re(c_n Λ_n)`. -/
theorem sum_weighted_Lam (hd0 : d ≠ 0) (R : ZMod 4 → Matrix κ κ ℂ) (hR : ∀ s, IsUnitaryM (R s))
    (hRd : ∀ s, R s ^ d = 1) :
    ∑ n ∈ Ico 1 d, ((d : ℝ) - n) * (cd d n * Lam d R n).re
      = (d : ℝ) / 2 * ∑ n ∈ Ico 1 d, (cd d n * Lam d R n).re := by
  apply sum_symm
  intro n hn
  have hn' := mem_Ico.1 hn
  rw [cd_reflect hd0 (by omega), Lam_reflect hd0 R hR hRd (by omega), ← map_mul, Complex.conj_re]

end Clock

/-! ### Theorem 2.3(2): the reduction of a projective strategy to the clock model -/

section Strategy

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [NeZero d]

lemma vec4_cases {M : Type*} (P : M → Prop) {a b c e : M} (ha : P a) (hb : P b) (hc : P c)
    (he : P e) (s : ZMod 4) : P (vec4 a b c e s) := by
  unfold vec4
  split_ifs <;> assumption

lemma IsUnitaryM.transpose {U : Matrix ι ι ℂ} (hU : IsUnitaryM U) : IsUnitaryM Uᵀ := by
  unfold IsUnitaryM
  rw [conjTranspose_transpose_eq_transpose_conjTranspose, ← transpose_mul, hU.mul_conjTranspose,
    transpose_one]

lemma pvmU_isUnitaryM {P : ZMod d → Matrix ι ι ℂ} (hP : IsPVM P) : IsUnitaryM (pvmU P) :=
  pvmU_unitary hP

lemma chainR_unitary (A B : Fin 2 → ZMod d → Matrix ι ι ℂ) (hA : ∀ x, IsPVM (A x))
    (hB : ∀ y, IsPVM (B y)) (s : ZMod 4) : IsUnitaryM (chainR A B s) :=
  vec4_cases IsUnitaryM (pvmU_unitary (hA 1)) (pvmU_isUnitaryM (hB 1)).transpose
    (pvmU_unitary (hA 0)) (pvmU_isUnitaryM (hB 0)).transpose s

lemma chainR_pow_d (A B : Fin 2 → ZMod d → Matrix ι ι ℂ) (hA : ∀ x, IsPVM (A x))
    (hB : ∀ y, IsPVM (B y)) (s : ZMod 4) : chainR A B s ^ d = 1 := by
  have hT : ∀ y, ((pvmU (B y))ᵀ) ^ d = 1 := by
    intro y
    rw [← transpose_pow, pvmU_pow_d (hB y), transpose_one]
  exact vec4_cases (fun X : Matrix ι ι ℂ => X ^ d = 1) (pvmU_pow_d (hA 1)) (hT 1) (pvmU_pow_d (hA 0))
    (hT 0) s

/-- **Theorem 2.3(2) of the paper (trace form).** For every projective strategy on the maximally
entangled state, with `V` the reduced family of its chain unitaries, `S = 2(d-1) - (2/d) F(V)`. -/
theorem chainS_eq_clockF [Nonempty ι] (A B : Fin 2 → ZMod d → Matrix ι ι ℂ) (hA : ∀ x, IsPVM (A x))
    (hB : ∀ y, IsPVM (B y)) :
    chainS (probME A B) = 2 * ((d : ℝ) - 1) - 2 / d * clockF d (Vred d (chainR A B)) := by
  have hd0 : d ≠ 0 := NeZero.ne d
  have hR := chainR_unitary A B hA hB
  have hRd := chainR_pow_d A B hA hB
  have h1 := congrArg Complex.re (chainS_trace A B hA hB)
  rw [Complex.ofReal_re, Complex.add_re, Complex.re_sum] at h1
  have h2c : (2 * ((d : ℂ) - 1)).re = 2 * ((d : ℝ) - 1) := by simp
  rw [h2c] at h1
  rw [clockF_Vred hd0 _ hR, sum_weighted_Lam hd0 _ hR hRd, h1]
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd0
  field_simp
  ring

/-- **The reduction to the clock model**: `I_d = 4 F(V) / (d (d - 1))` for every projective strategy on
the maximally entangled state, `V` the reduced family (paper, Theorem 2.3(2)). -/
theorem cglmp_eq_clockF [Nonempty ι] (hd : 2 ≤ d) (A B : Fin 2 → ZMod d → Matrix ι ι ℂ)
    (hA : ∀ x, IsPVM (A x)) (hB : ∀ y, IsPVM (B y)) :
    cglmp (probME A B) = 4 * clockF d (Vred d (chainR A B)) / ((d : ℝ) * ((d : ℝ) - 1)) := by
  rw [cglmp_eq_chain hd _ (probME_normalised A B hA hB), chainS_eq_clockF A B hA hB]
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  field_simp
  ring

end Strategy

end

end OQP27.Red
