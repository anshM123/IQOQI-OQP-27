import OQP27.RigidityReduction

/-!
# OQP 27B rigidity: from the canonical DKZ tuple to the DKZ measurements (module L6)

Paper: `publish/CGLMP/paper-classical-all-d/main.tex`, Section 2.4 (the DKZ chain is
`(R_1, …, R_4) = G R^{(0)} G^*`, `G = W_0^{-2} = diag(z^{-2j})`) and the proof of Corollary C;
`publish/CGLMP/rigidity/RIGIDITY.md` Theorem 4.1 (translation to PVMs and Bob's conjugate frame).

All chain matrices are weighted cyclic shifts `wsh c` (entry `(j, j')` equal to `c_j` if `j = j' + 1`
mod `d`, else `0`). This file proves (no hypotheses):

* `OQP27.Rig.Gdkz_conj_canonR`: `G R^c_i G^* = R^DKZ_i` for `i = 1, …, 4`, where `R^c` is the canonical
  tuple of `CGLMPRigidity.canonical_model` and `R^DKZ` is the chain (module L2's `chainR`) of the DKZ
  strategy `OQP27.dkz d` of module L1;
* `OQP27.Rig.pvm_inversion`: `P_a = (1/d) ∑_{n<d} w^{-n a} U^n` for a PVM with `U = ∑_b w^b P_b`;
* `OQP27.Rig.isDKZTensorId_of_canonical`: if `u R_i u^* = R^c_i ⊗ 1_K` for the chain of a strategy `S`,
  then `S.IsDKZTensorId` (the exact form of `OQP27.RigidityStatement`), with the unitary `(G ⊗ 1) u`;
  Bob's frame is the entrywise conjugate, obtained by transposing `R_2 = (U'_2)^T`, `R_4 = (U'_1)^T`.
-/

set_option linter.unusedSectionVars false

open Complex Matrix Finset
open scoped Kronecker

namespace OQP27.Rig

variable {d : ℕ} [NeZero d]

/-! ## Weighted cyclic shifts -/

/-- The weighted cyclic shift `∑_j c_j |j⟩⟨j - 1|`. -/
def wsh (c : Fin d → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun j j' => if j = j' + 1 then c j else 0

lemma wsh_apply (c : Fin d → ℂ) (j j' : Fin d) : wsh c j j' = if j = j' + 1 then c j else 0 := rfl

lemma wsh_ext {c c' : Fin d → ℂ} (h : ∀ j, c j = c' j) : wsh c = wsh c' := by
  rw [funext h]

lemma shiftM_eq_wsh : CGLMPRigidity.shiftM d = wsh (fun _ => 1) := by
  ext j j'
  rw [CGLMPRigidity.shiftM, Matrix.sum_apply, wsh_apply]
  rw [Finset.sum_eq_single j']
  · simp only [Matrix.single_apply]
    by_cases h : j = j' + 1
    · simp [h]
    · rw [if_neg (fun h' => h h'.1.symm), if_neg h]
  · intro k _ hk
    rw [Matrix.single_apply, if_neg (fun h' => hk h'.2)]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma diagonal_mul_wsh (δ c : Fin d → ℂ) : diagonal δ * wsh c = wsh (fun j => δ j * c j) := by
  ext j j'
  rw [diagonal_mul, wsh_apply, wsh_apply]
  split_ifs <;> simp

lemma smul_wsh (a : ℂ) (c : Fin d → ℂ) : a • wsh c = wsh (fun j => a * c j) := by
  ext j j'
  rw [Matrix.smul_apply, wsh_apply, wsh_apply]
  split_ifs <;> simp

lemma wsh_mul_diagonal (c g : Fin d → ℂ) : wsh c * diagonal g = wsh (fun j => c j * g (j - 1)) := by
  ext j j'
  rw [mul_diagonal, wsh_apply, wsh_apply]
  split_ifs with h
  · rw [h, add_sub_cancel_right]
  · simp

lemma Dm_eq_diagonal : CGLMPRigidity.Dm d = diagonal (fun j => if j = 0 then -I else 1) := by
  ext j j'
  simp only [CGLMPRigidity.Dm, CGLMPRigidity.proj0, Matrix.sub_apply, Matrix.one_apply,
    Matrix.smul_apply, Matrix.single_apply, diagonal_apply, smul_eq_mul]
  by_cases h : j = j'
  · subst h
    by_cases h0 : j = 0
    · simp [h0]
    · simp [h0, Ne.symm h0]
  · simp [h]
    intro h1 h2
    exact absurd (h1.symm.trans h2) h

lemma R2m_eq_wsh :
    CGLMPRigidity.R2m d = wsh (fun j => CGLMPRigidity.zeta d * (if j = 0 then -I else 1)) := by
  rw [CGLMPRigidity.R2m, Dm_eq_diagonal, shiftM_eq_wsh, diagonal_mul_wsh, smul_wsh]
  apply wsh_ext
  intro j
  ring

lemma R3m_eq_wsh :
    CGLMPRigidity.R3m d = wsh (fun j => CGLMPRigidity.zeta d ^ 2 * (if j = 0 then -1 else 1)) := by
  rw [CGLMPRigidity.R3m, Dm_eq_diagonal, R2m_eq_wsh, diagonal_mul_wsh, smul_wsh]
  apply wsh_ext
  intro j
  split_ifs
  · linear_combination (CGLMPRigidity.zeta d) ^ 2 * I_sq
  · ring

lemma R4m_eq_wsh :
    CGLMPRigidity.R4m d = wsh (fun j => CGLMPRigidity.zeta d ^ 3 * (if j = 0 then I else 1)) := by
  rw [CGLMPRigidity.R4m, Dm_eq_diagonal, R3m_eq_wsh, diagonal_mul_wsh, smul_wsh]
  apply wsh_ext
  intro j
  split_ifs
  · ring
  · ring

/-! ## The root of unity `z = e^{2πi/(4d)}` -/

lemma zz_eq_zd : zz d = Red.zd d := by
  unfold zz Red.zd
  congr 1
  push_cast
  ring

lemma zeta_eq_zz : CGLMPRigidity.zeta d = zz d := by
  rw [← zd_eq_zeta, zz_eq_zd]

lemma zz_pow_d : zz d ^ d = I := by
  rw [zz_eq_zd]; exact Red.zd_pow_d (NeZero.ne d)

lemma zz_zpow_d : zz d ^ (d : ℤ) = I := by
  rw [zpow_natCast, zz_pow_d]

lemma wd_eq_zz_pow : Red.wd d = zz d ^ 4 := by
  rw [zz_eq_zd, Red.zd_pow_four (NeZero.ne d)]

lemma zz_zpow_two_d : zz d ^ (2 * (d : ℤ)) = -1 := by
  rw [mul_comm, _root_.zpow_mul, zz_zpow_d, zpow_two, I_mul_I]

/-! ## The diagonal unitary `G = diag(z^{-2j})` -/

/-- `G = W_0^{-2} = diag(z^{-2j})` (`paper-classical-all-d`, Section 2.4). -/
noncomputable def Gdkz (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  diagonal (fun j => zz d ^ (-(2 * ((j : ℕ) : ℤ))))

lemma Gdkz_conjTranspose : (Gdkz d)ᴴ = diagonal (fun j : Fin d => zz d ^ (2 * ((j : ℕ) : ℤ))) := by
  rw [Gdkz, diagonal_conjTranspose]
  congr 1
  funext j
  simp only [Pi.star_apply]
  rw [star_zz_zpow, neg_neg]

lemma Gdkz_mul_conjTranspose : Gdkz d * (Gdkz d)ᴴ = 1 := by
  rw [Gdkz_conjTranspose, Gdkz, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext j
  rw [← zpow_add₀ zz_ne_zero, neg_add_cancel, zpow_zero]

lemma Gdkz_conjTranspose_mul : (Gdkz d)ᴴ * Gdkz d = 1 :=
  mul_eq_one_comm.1 Gdkz_mul_conjTranspose

lemma Gdkz_conj_wsh (c : Fin d → ℂ) :
    Gdkz d * wsh c * (Gdkz d)ᴴ = wsh (fun j => zz d ^ (-(2 * ((j : ℕ) : ℤ))) * c j *
      zz d ^ (2 * (((j - 1 : Fin d) : ℕ) : ℤ))) := by
  rw [Gdkz_conjTranspose, Gdkz, diagonal_mul_wsh, wsh_mul_diagonal]

lemma val_sub_one (j : Fin d) :
    ((j - 1 : Fin d) : ℕ) = if (j : ℕ) = 0 then d - 1 else (j : ℕ) - 1 := by
  rw [Fin.val_sub, Fin.val_one']
  have hj := j.isLt
  have hd := NeZero.pos d
  rcases Nat.lt_or_ge 1 d with h1 | h1
  · rw [Nat.mod_eq_of_lt h1]
    split_ifs with h0
    · rw [h0, add_zero, Nat.mod_eq_of_lt (by omega)]
    · rw [show d - 1 + (j : ℕ) = ((j : ℕ) - 1) + d by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)]
  · have hd1 : d = 1 := by omega
    subst hd1
    have : (j : ℕ) = 0 := by omega
    simp

/-- For `j = j' + 1` in `Fin d`: `j - j' = 1` if `j ≠ 0`, and `1 - d` if `j = 0`. -/
lemma sub_of_eq_add_one {j j' : Fin d} (h : j = j' + 1) :
    (((j : ℕ) : ℤ) - (j' : ℕ)) = if (j : ℕ) = 0 then 1 - (d : ℤ) else 1 := by
  have hj' : j' = j - 1 := by rw [h, add_sub_cancel_right]
  have hd := NeZero.pos d
  have hlt := j.isLt
  rw [hj', val_sub_one]
  split_ifs with h0
  · rw [h0]
    push_cast [Nat.cast_sub (by omega : 1 ≤ d)]
    ring
  · push_cast [Nat.cast_sub (by omega : 1 ≤ (j : ℕ))]
    ring

/-! ## The chain of the DKZ strategy -/

lemma zz_zpow_four_d_mul (q : ℤ) : zz d ^ (4 * ((d : ℤ) * q)) = 1 := by
  have h : zz d ^ ((4 * d : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast]; exact (zz_isPrimitiveRoot (NeZero.pos d)).pow_eq_one
  rw [show 4 * ((d : ℤ) * q) = ((4 * d : ℕ) : ℤ) * q by push_cast; ring, _root_.zpow_mul, h,
    _root_.one_zpow]

/-- Character sum of `ℤ/d`: `∑_b (z^{4r})^b = d [d ∣ r]`. -/
lemma sum_zmod_zz_pow (r : ℤ) :
    ∑ b : ZMod d, (zz d ^ (4 * r)) ^ b.val = if (d : ℤ) ∣ r then (d : ℂ) else 0 := by
  rw [Red.sum_zmod_eq_sum_range]
  have e : ∀ j ∈ range d, (zz d ^ (4 * r)) ^ ((j : ZMod d).val) = (zz d ^ (4 * r)) ^ j := by
    intro j hj
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.1 hj)]
  rw [Finset.sum_congr rfl e]
  split_ifs with h
  · obtain ⟨q, rfl⟩ := h
    rw [zz_zpow_four_d_mul]
    simp
  · exact sum_zz_pow_four_mul (NeZero.pos d) h

lemma val_add_one_of_lt {j' : Fin d} (h : (j' : ℕ) + 1 < d) : ((j' + 1 : Fin d) : ℕ) = j' + 1 := by
  rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod, Nat.mod_eq_of_lt h]

lemma val_add_one_of_eq {j' : Fin d} (h : (j' : ℕ) + 1 = d) : ((j' + 1 : Fin d) : ℕ) = 0 := by
  rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod, h, Nat.mod_self]

/-- `d ∣ 1 - (j - j')` iff `j = j' + 1` in `Fin d`. -/
lemma dvd_one_sub_iff (j j' : Fin d) :
    (d : ℤ) ∣ 1 - (((j : ℕ) : ℤ) - (j' : ℕ)) ↔ j = j' + 1 := by
  have hj := j.isLt
  have hj' := j'.isLt
  constructor
  · intro h
    by_contra hne
    have h0 : 1 - (((j : ℕ) : ℤ) - (j' : ℕ)) ≠ 0 := by
      intro h0
      apply hne
      apply Fin.ext
      rw [val_add_one_of_lt (by omega)]
      omega
    have hd' : 1 - (((j : ℕ) : ℤ) - (j' : ℕ)) ≠ d := by
      intro h1
      apply hne
      apply Fin.ext
      rw [val_add_one_of_eq (by omega)]
      omega
    have habs : |1 - (((j : ℕ) : ℤ) - (j' : ℕ))| < d := by
      rw [abs_lt]; constructor <;> omega
    exact dkz_not_dvd_of_abs_lt h0 habs h
  · intro h
    rw [sub_of_eq_add_one h]
    split_ifs
    · exact ⟨1, by ring⟩
    · exact ⟨0, by ring⟩

/-- `d ∣ 1 + (j - j')` iff `j' = j + 1` in `Fin d`. -/
lemma dvd_one_add_iff (j j' : Fin d) :
    (d : ℤ) ∣ 1 + (((j : ℕ) : ℤ) - (j' : ℕ)) ↔ j' = j + 1 := by
  rw [← dvd_one_sub_iff j' j]
  constructor <;> intro h <;> convert h using 1 <;> ring

/-- Entries of `∑_b w^b P_b` for the phase projectors `P_b = phaseProj (-4b + c₀)` (Alice's DKZ type). -/
lemma phaseSumA_apply (c₀ : ℤ) (j j' : Fin d) :
    (∑ b : ZMod d, (Red.wd d ^ b.val) • phaseProj d (-(4 * ((b.val : ℕ) : ℤ)) + c₀)) j j'
      = if j = j' + 1 then zz d ^ ((((j : ℕ) : ℤ) - (j' : ℕ)) * c₀) else 0 := by
  set e : ℤ := ((j : ℕ) : ℤ) - (j' : ℕ) with he
  have hterm : ∀ b : ZMod d, (Red.wd d ^ b.val) * ((d : ℂ)⁻¹ * zz d ^ (e * (-(4 * ((b.val : ℕ) : ℤ)) + c₀)))
      = ((d : ℂ)⁻¹ * zz d ^ (e * c₀)) * (zz d ^ (4 * (1 - e))) ^ b.val := by
    intro b
    rw [wd_eq_zz_pow, ← pow_mul, ← zpow_natCast (zz d) (4 * b.val), ← zpow_natCast _ b.val,
      ← _root_.zpow_mul]
    have hz := zz_ne_zero (d := d)
    rw [mul_left_comm, mul_assoc, ← zpow_add₀ hz, mul_assoc, ← zpow_add₀ hz]
    congr 2
    push_cast
    ring
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, phaseProj, of_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun b _ => hterm b), ← Finset.mul_sum, sum_zmod_zz_pow]
  have hiff := dvd_one_sub_iff j j'
  by_cases h : j = j' + 1
  · rw [if_pos (hiff.2 h), if_pos h]
    have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
    field_simp
  · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h, mul_zero]

/-- Entries of `∑_b w^b P_b` for the phase projectors `P_b = phaseProj (4b + c₀)` (Bob's DKZ type). -/
lemma phaseSumB_apply (c₀ : ℤ) (j j' : Fin d) :
    (∑ b : ZMod d, (Red.wd d ^ b.val) • phaseProj d (4 * ((b.val : ℕ) : ℤ) + c₀)) j j'
      = if j' = j + 1 then zz d ^ ((((j : ℕ) : ℤ) - (j' : ℕ)) * c₀) else 0 := by
  set e : ℤ := ((j : ℕ) : ℤ) - (j' : ℕ) with he
  have hterm : ∀ b : ZMod d, (Red.wd d ^ b.val) * ((d : ℂ)⁻¹ * zz d ^ (e * (4 * ((b.val : ℕ) : ℤ) + c₀)))
      = ((d : ℂ)⁻¹ * zz d ^ (e * c₀)) * (zz d ^ (4 * (1 + e))) ^ b.val := by
    intro b
    rw [wd_eq_zz_pow, ← pow_mul, ← zpow_natCast (zz d) (4 * b.val), ← zpow_natCast _ b.val,
      ← _root_.zpow_mul]
    have hz := zz_ne_zero (d := d)
    rw [mul_left_comm, mul_assoc, ← zpow_add₀ hz, mul_assoc, ← zpow_add₀ hz]
    congr 2
    push_cast
    ring
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, phaseProj, of_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun b _ => hterm b), ← Finset.mul_sum, sum_zmod_zz_pow]
  have hiff := dvd_one_add_iff j j'
  by_cases h : j' = j + 1
  · rw [if_pos (hiff.2 h), if_pos h]
    have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
    field_simp
  · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h, mul_zero]

/-! ## All four chains as weighted shifts `j ↦ z^{m e(j)}`, `e(j) = j - (j - 1)` -/

/-- `e(j) = j - (j - 1)` as integers: `1` for `j ≠ 0`, `1 - d` for `j = 0`. -/
def eStep (j : Fin d) : ℤ := ((j : ℕ) : ℤ) - (((j - 1 : Fin d) : ℕ) : ℤ)

lemma eStep_eq (j : Fin d) : eStep j = if (j : ℕ) = 0 then 1 - (d : ℤ) else 1 :=
  sub_of_eq_add_one (sub_add_cancel j 1).symm

lemma fin_eq_zero_iff (j : Fin d) : j = 0 ↔ (j : ℕ) = 0 := by
  rw [Fin.ext_iff, Fin.val_zero]

lemma zz_zpow_mul_eStep (m : ℕ) (j : Fin d) :
    zz d ^ ((m : ℤ) * eStep j) = zz d ^ m * (if j = 0 then (-I) ^ m else 1) := by
  rw [eStep_eq]
  by_cases h : (j : ℕ) = 0
  · have hj : j = 0 := (fin_eq_zero_iff j).2 h
    rw [if_pos h, if_pos hj]
    have hz := zz_ne_zero (d := d)
    rw [show (m : ℤ) * (1 - (d : ℤ)) = (m : ℤ) + (d : ℤ) * (-(m : ℤ)) by ring, zpow_add₀ hz,
      _root_.zpow_mul, zz_zpow_d, zpow_natCast, _root_.zpow_neg, zpow_natCast, ← inv_pow, Complex.inv_I]
  · have hj : j ≠ 0 := fun h' => h ((fin_eq_zero_iff j).1 h')
    rw [if_neg h, if_neg hj, mul_one, zpow_natCast, mul_one]

lemma negI_cube : (-I : ℂ) ^ 3 = I := by linear_combination (-I) * I_sq

lemma canonR_eq_wsh (s : ZMod 4) :
    canonR d s = wsh (fun j => zz d ^ ((s.val : ℤ) * eStep j)) := by
  have h3 : ∀ j : Fin d, (if j = 0 then I else (1 : ℂ)) = if j = 0 then (-I) ^ 3 else 1 := by
    intro j; rw [negI_cube]
  obtain rfl | rfl | rfl | rfl : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by revert s; decide
  · simp only [canonR, Red.vec4_zero, shiftM_eq_wsh]
    apply wsh_ext; intro j
    rw [show ((0 : ZMod 4).val : ℤ) = ((0 : ℕ) : ℤ) from rfl, zz_zpow_mul_eStep]; simp
  · simp only [canonR, Red.vec4_one, R2m_eq_wsh]
    apply wsh_ext; intro j
    rw [show ((1 : ZMod 4).val : ℤ) = ((1 : ℕ) : ℤ) from rfl, zz_zpow_mul_eStep, zeta_eq_zz]
    simp
  · simp only [canonR, Red.vec4_two, R3m_eq_wsh]
    apply wsh_ext; intro j
    rw [show ((2 : ZMod 4).val : ℤ) = ((2 : ℕ) : ℤ) from rfl, zz_zpow_mul_eStep, zeta_eq_zz]
    congr 1
    split_ifs <;> simp [I_sq]
  · simp only [canonR, Red.vec4_three, R4m_eq_wsh]
    apply wsh_ext; intro j
    rw [show ((3 : ZMod 4).val : ℤ) = ((3 : ℕ) : ℤ) from rfl, zz_zpow_mul_eStep, zeta_eq_zz, h3]

lemma Gdkz_conj_wsh_zz (m : ℤ) :
    Gdkz d * wsh (fun j => zz d ^ (m * eStep j)) * (Gdkz d)ᴴ
      = wsh (fun j => zz d ^ ((m - 2) * eStep j)) := by
  rw [Gdkz_conj_wsh]
  apply wsh_ext
  intro j
  have hz := zz_ne_zero (d := d)
  rw [← zpow_add₀ hz, ← zpow_add₀ hz]
  congr 1
  unfold eStep
  ring

/-- Alice's DKZ unitary `U_x = ∑_b w^b A^DKZ_{x,b}`. -/
lemma pvmU_dkzA (x : Fin 2) :
    Red.pvmU (Red.stratA (dkz d) x)
      = ∑ b : ZMod d, (Red.wd d ^ b.val) • phaseProj d (-(4 * ((b.val : ℕ) : ℤ)) + -alpha4 x) := by
  unfold Red.pvmU
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  show dkzA d x (Red.zToFin b) = _
  unfold dkzA
  congr 1
  simp only [Red.zToFin]
  try ring

/-- Bob's DKZ unitary `U'_y = ∑_b w^b B^DKZ_{y,b}`. -/
lemma pvmU_dkzB (y : Fin 2) :
    Red.pvmU (Red.stratB (dkz d) y)
      = ∑ b : ZMod d, (Red.wd d ^ b.val) • phaseProj d (4 * ((b.val : ℕ) : ℤ) + -beta4 y) := by
  unfold Red.pvmU
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1

lemma pvmU_dkzA_eq_wsh (x : Fin 2) :
    Red.pvmU (Red.stratA (dkz d) x) = wsh (fun j => zz d ^ (-alpha4 x * eStep j)) := by
  rw [pvmU_dkzA]
  ext j j'
  rw [phaseSumA_apply, wsh_apply]
  by_cases h : j = j' + 1
  · rw [if_pos h, if_pos h, mul_comm]
    congr 2
    have hj' : j - 1 = j' := by rw [h, add_sub_cancel_right]
    rw [eStep, hj']
  · rw [if_neg h, if_neg h]

lemma pvmU_dkzB_transpose_eq_wsh (y : Fin 2) :
    (Red.pvmU (Red.stratB (dkz d) y))ᵀ = wsh (fun j => zz d ^ (beta4 y * eStep j)) := by
  rw [pvmU_dkzB]
  ext j j'
  rw [transpose_apply, phaseSumB_apply, wsh_apply]
  by_cases h : j = j' + 1
  · rw [if_pos h, if_pos h]
    congr 1
    have hj' : j - 1 = j' := by rw [h, add_sub_cancel_right]
    rw [eStep, hj']
    ring
  · rw [if_neg h, if_neg h]

/-- **The DKZ chain is `G R^c G^*`** (`paper-classical-all-d`, Section 2.4), for all four links. -/
theorem Gdkz_conj_canonR (s : ZMod 4) :
    Gdkz d * canonR d s * (Gdkz d)ᴴ = Red.chainR (Red.stratA (dkz d)) (Red.stratB (dkz d)) s := by
  rw [canonR_eq_wsh, Gdkz_conj_wsh_zz]
  obtain rfl | rfl | rfl | rfl : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by revert s; decide
  · rw [Red.chainR, Red.vec4_zero, pvmU_dkzA_eq_wsh]
    apply wsh_ext; intro j
    congr 1
    try simp [alpha4]
  · rw [Red.chainR, Red.vec4_one, pvmU_dkzB_transpose_eq_wsh]
    apply wsh_ext; intro j
    congr 1
    try simp [beta4]
    try norm_num
  · rw [Red.chainR, Red.vec4_two, pvmU_dkzA_eq_wsh]
    apply wsh_ext; intro j
    congr 1
    try simp [alpha4]
  · rw [Red.chainR, Red.vec4_three, pvmU_dkzB_transpose_eq_wsh]
    apply wsh_ext; intro j
    congr 1
    try simp [beta4]

/-! ## From the chain to the measurements -/

section Inversion

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **PVM inversion**: `P_a = (1/d) ∑_{n<d} w^{-n a} U^n` for `U = ∑_b w^b P_b`. -/
lemma pvm_inversion {P : ZMod d → Matrix ι ι ℂ} (hP : Red.IsPVM P) (a : ZMod d) :
    P a = ((d : ℂ)⁻¹) • ∑ n ∈ range d, (Red.wd d ^ (n * a.val))⁻¹ • Red.pvmU P ^ n := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  have key : ∑ n ∈ range d, (Red.wd d ^ (n * a.val))⁻¹ • Red.pvmU P ^ n = (d : ℂ) • P a := by
    simp_rw [Red.pvmU_pow hP, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have hb : ∀ b : ZMod d, ∑ n ∈ range d, ((Red.wd d ^ (n * a.val))⁻¹ * Red.wd d ^ (n * b.val)) • P b
        = (if a.val = b.val then (d : ℂ) else 0) • P b := by
      intro b
      rw [← Finset.sum_smul]
      congr 1
      rw [← Red.sum_pow_ratio (NeZero.ne d) (ZMod.val_lt a) (ZMod.val_lt b)]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [mul_pow, inv_pow, ← pow_mul, ← pow_mul, mul_comm (a.val) n, mul_comm (b.val) n, mul_comm]
    rw [Finset.sum_congr rfl (fun b _ => hb b)]
    rw [Finset.sum_eq_single a]
    · rw [if_pos rfl]
    · intro b _ hba
      rw [if_neg (fun h => hba (ZMod.val_injective _ h).symm), zero_smul]
    · intro h; exact absurd (Finset.mem_univ a) h
  rw [key, smul_smul, inv_mul_cancel₀ hd, one_smul]

end Inversion

section Conjugation

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

lemma conj_pow {u : Matrix m n ℂ} (hu1 : u * uᴴ = 1) (hu2 : uᴴ * u = 1) (X : Matrix n n ℂ) :
    ∀ k : ℕ, u * X ^ k * uᴴ = (u * X * uᴴ) ^ k
  | 0 => by rw [pow_zero, pow_zero, Matrix.mul_one, hu1]
  | k + 1 => by rw [pow_succ, conj_mul hu2, conj_pow hu1 hu2 X k, pow_succ]

/-- Conjugating the inversion formula. -/
lemma conj_pvm {u : Matrix m n ℂ} (hu1 : u * uᴴ = 1) (hu2 : uᴴ * u = 1)
    {P : ZMod d → Matrix n n ℂ} (hP : Red.IsPVM P) {P' : ZMod d → Matrix m m ℂ} (hP' : Red.IsPVM P')
    (hU : u * Red.pvmU P * uᴴ = Red.pvmU P') (a : ZMod d) : u * P a * uᴴ = P' a := by
  rw [pvm_inversion hP a, pvm_inversion hP' a, conj_smul, conj_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [conj_smul, conj_pow hu1 hu2, hU]

lemma map_star_mul_conjTranspose {u : Matrix m n ℂ} (hu : u * uᴴ = 1) :
    u.map star * (u.map star)ᴴ = 1 := by
  have e : (u.map star)ᴴ = (uᴴ).map star := by
    ext i j; simp [conjTranspose_apply]
  rw [e]
  have h := congrArg (fun X => X.map (starRingEnd ℂ)) hu
  simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
  exact h

lemma map_star_conjTranspose_mul {u : Matrix m n ℂ} (hu : uᴴ * u = 1) :
    (u.map star)ᴴ * u.map star = 1 := by
  have e : (u.map star)ᴴ = (uᴴ).map star := by
    ext i j; simp [conjTranspose_apply]
  rw [e]
  have h := congrArg (fun X => X.map (starRingEnd ℂ)) hu
  simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at h
  exact h

lemma transpose_conj (u : Matrix m n ℂ) (X : Matrix n n ℂ) :
    (u * X * uᴴ)ᵀ = u.map star * Xᵀ * (u.map star)ᴴ := by
  rw [transpose_mul, transpose_mul, Matrix.mul_assoc]
  have e1 : (uᴴ)ᵀ = u.map star := by ext i j; simp [conjTranspose_apply]
  have e2 : uᵀ = (u.map star)ᴴ := by ext i j; simp [conjTranspose_apply]
  rw [e1, e2]

end Conjugation

lemma tens_transpose {K : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : (tens K A)ᵀ = tens K Aᵀ := by
  rw [tens, tens]
  conv_rhs => rw [← transpose_one]
  rw [kroneckerMap_transpose]

lemma tens_conjTranspose {K : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : (tens K A)ᴴ = tens K Aᴴ := by
  rw [tens, tens, conjTranspose_kronecker, conjTranspose_one]

lemma tens_pvmU {K : ℕ} (P : ZMod d → Matrix (Fin d) (Fin d) ℂ) :
    tens K (Red.pvmU P) = Red.pvmU (fun a => tens K (P a)) := by
  rw [Red.pvmU, Red.pvmU, tens_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [tens_smul]

lemma tens_isPVM {K : ℕ} {P : ZMod d → Matrix (Fin d) (Fin d) ℂ} (hP : Red.IsPVM P) :
    Red.IsPVM (fun a => tens K (P a)) := by
  refine ⟨fun a => ⟨?_, ?_⟩, ?_⟩
  · show (tens K (P a))ᴴ = tens K (P a)
    rw [tens_conjTranspose, (hP.1 a).1.eq]
  · rw [← tens_mul, (hP.1 a).2]
  · rw [← tens_sum, hP.2, tens_one]

lemma dkz_stratA_isPVM (x : Fin 2) : Red.IsPVM (Red.stratA (dkz d) x) := Red.stratA_isPVM _ x

lemma dkz_stratB_isPVM (y : Fin 2) : Red.IsPVM (Red.stratB (dkz d) y) := Red.stratB_isPVM _ y

/-- **From the canonical form to the DKZ measurements** (`RIGIDITY.md` Theorem 4.1; `paper-classical-all-d`
Corollary C): if `u R_i u^* = R^c_i ⊗ 1_K` for the chain `R` of a strategy `S`, then `S` is DKZ ⊗ 1_K up to
the local unitary `v ⊗ v̄` with `v = (G ⊗ 1) u`. -/
theorem isDKZTensorId_of_canonical {D : ℕ} (S : Strategy d D) {K : ℕ} (hDK : D = d * K)
    (u : Matrix (Fin d × Fin K) (Fin D) ℂ) (hu1 : u * uᴴ = 1) (hu2 : uᴴ * u = 1)
    (hR : ∀ s : ZMod 4, u * Red.chainR (Red.stratA S) (Red.stratB S) s * uᴴ = tens K (canonR d s)) :
    S.IsDKZTensorId := by
  set v : Matrix (Fin d × Fin K) (Fin D) ℂ := tens K (Gdkz d) * u with hv
  have hvH : vᴴ = uᴴ * tens K (Gdkz d)ᴴ := by
    rw [hv, conjTranspose_mul, tens_conjTranspose]
  have hG1 : tens K (Gdkz d) * tens K (Gdkz d)ᴴ = 1 := by
    rw [← tens_mul, Gdkz_mul_conjTranspose, tens_one]
  have hG2 : tens K (Gdkz d)ᴴ * tens K (Gdkz d) = 1 := by
    rw [← tens_mul, Gdkz_conjTranspose_mul, tens_one]
  have hv1 : v * vᴴ = 1 := by
    rw [hvH, hv]
    calc tens K (Gdkz d) * u * (uᴴ * tens K (Gdkz d)ᴴ)
        = tens K (Gdkz d) * (u * uᴴ) * tens K (Gdkz d)ᴴ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hu1, Matrix.mul_one, hG1]
  have hv2 : vᴴ * v = 1 := by
    rw [hvH, hv]
    calc uᴴ * tens K (Gdkz d)ᴴ * (tens K (Gdkz d) * u)
        = uᴴ * (tens K (Gdkz d)ᴴ * tens K (Gdkz d)) * u := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hG2, Matrix.mul_one, hu2]
  -- the chain of `S` is mapped to the DKZ chain
  have hchain : ∀ s : ZMod 4, v * Red.chainR (Red.stratA S) (Red.stratB S) s * vᴴ
      = tens K (Red.chainR (Red.stratA (dkz d)) (Red.stratB (dkz d)) s) := by
    intro s
    rw [hvH, hv, ← Gdkz_conj_canonR, tens_mul, tens_mul]
    calc tens K (Gdkz d) * u * Red.chainR (Red.stratA S) (Red.stratB S) s * (uᴴ * tens K (Gdkz d)ᴴ)
        = tens K (Gdkz d) * (u * Red.chainR (Red.stratA S) (Red.stratB S) s * uᴴ)
            * tens K (Gdkz d)ᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hR]
  -- Alice
  have hA : ∀ x : Fin 2, v * Red.pvmU (Red.stratA S x) * vᴴ
      = Red.pvmU (fun a => tens K (Red.stratA (dkz d) x a)) := by
    intro x
    rw [← tens_pvmU]
    fin_cases x
    · have h := hchain 2
      simp only [Red.chainR, Red.vec4_two] at h
      exact h
    · have h := hchain 0
      simp only [Red.chainR, Red.vec4_zero] at h
      exact h
  -- Bob, after transposing `R_2 = (U'_2)^T` and `R_4 = (U'_1)^T`
  have hB : ∀ y : Fin 2, v.map star * Red.pvmU (Red.stratB S y) * (v.map star)ᴴ
      = Red.pvmU (fun b => tens K (Red.stratB (dkz d) y b)) := by
    intro y
    rw [← tens_pvmU]
    have key : ∀ s : ZMod 4, ∀ X Y : Matrix _ _ ℂ,
        Red.chainR (Red.stratA S) (Red.stratB S) s = Xᵀ →
        Red.chainR (Red.stratA (dkz d)) (Red.stratB (dkz d)) s = Yᵀ →
        v.map star * X * (v.map star)ᴴ = tens K Y := by
      intro s X Y hX hY
      have h := congrArg Matrix.transpose (hchain s)
      rw [transpose_conj, hX, hY, tens_transpose, transpose_transpose, transpose_transpose] at h
      exact h
    fin_cases y
    · exact key 3 _ _ (by simp [Red.chainR]) (by simp [Red.chainR])
    · exact key 1 _ _ (by simp [Red.chainR]) (by simp [Red.chainR])
  refine ⟨K, hDK, v, hv1, hv2, fun x a => ?_, fun y b => ?_⟩
  · have h := conj_pvm hv1 hv2 (Red.stratA_isPVM S x) (tens_isPVM (dkz_stratA_isPVM x)) (hA x)
      ((a : ℕ) : ZMod d)
    simp only [Red.stratA, Red.zToFin_natCast] at h
    exact h
  · have hbar1 := map_star_mul_conjTranspose hv1
    have hbar2 := map_star_conjTranspose_mul hv2
    have h := conj_pvm hbar1 hbar2 (Red.stratB_isPVM S y) (tens_isPVM (dkz_stratB_isPVM y)) (hB y)
      ((b : ℕ) : ZMod d)
    simp only [Red.stratB, Red.zToFin_natCast] at h
    exact h

end OQP27.Rig
