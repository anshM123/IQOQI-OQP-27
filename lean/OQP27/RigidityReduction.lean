import OQP27.Reduction
import OQP27.RigidityClassical
import OQP27.RigidityBlocks
import OQP27.RigidityUnits
import CGLMPRigidity.Model

/-!
# OQP 27B rigidity, Step 5: a commuting optimal configuration forces the canonical DKZ form (module L6)

Paper: `iqoqi/programs/oqp27B_all/Q_rig/RIGIDITY_ALLD.md`, section 6 (6.1-6.3), with
`publish/CGLMP/paper-classical-all-d/main.tex` (Theorem B, Corollary C) and
`publish/CGLMP/rigidity/RIGIDITY.md` (Lemma 7.2, Theorems 3.8, 3.9).

Setting: a projective strategy `S` on `Φ_D` (module L1), its chain unitaries `R = chainR` and reduced family
`V = redFamily S` (`V_k = ∑_s |s⟩⟨s+1| ⊗ z^{-k} R_{s+1}^{-k} R_{s+2}^k`) and its 27B configuration
`Q = redConfig S` (spectral projections of `V_k^*`), all from module L2 (`OQP27/Reduction*.lean`).

Main result (`OQP27.Rig.canonical_form`): if all `Q_x` commute and `S` attains `I_ME(d)` (`d ≥ 2`), then,
given the classical commutative-sector statement `OQP27.Rig.Hyp_ClassicalTheoremB d`, `D = d K` and there is
a unitary `u : ℂ^D → ℂ^d ⊗ ℂ^K` with `u R_i u^* = R^c_i ⊗ 1_K` (`i = 1, …, 4`), where `R^c` is the canonical
DKZ tuple of `CGLMPRigidity.canonical_model` (`R^c_1 = X`, `R^c_{i+1} = z (1 - (1 + i)|0⟩⟨0|) R^c_i`).

Proof (all steps formal): `Q` is a configuration in the sense of `OQP27.Rig.IsConfig` and its reduced family is
`V` (bridges to module L2); `I_d = I_ME(d)` gives `F(V) = F_DKZ` (module L2's deficit formula); the
commutative-sector theorem (`OQP27.Rig.commuting_optimal_relations`) gives `[V_0, V_1] = 0` and the
two-eigenvalue relations of `V_0 V_n^*`; `OQP27.Rig.rigidity_of_Vred` turns them into the hypotheses of
`CGLMPRigidity.rigidity`, whose matrix units give the unitary (`OQP27.Rig.exists_unitary_of_matrixUnits`).

Hypothesis remaining: `OQP27.Rig.Hyp_ClassicalTheoremB d` only.
-/

set_option linter.unusedSectionVars false

open Complex Matrix Finset
open scoped Kronecker

namespace OQP27.Rig

/-! ## Bridges to module L2 -/

section Bridges

variable {d : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

lemma siteIdx_eq_qd (k : Fin d) (a : ZMod 4) : siteIdx d k a = Red.qd d k a := by
  rw [Red.qd_eq, siteIdx, Red.mu]

lemma isConfig_of_isConfig27B {Q : ZMod (4 * d) → Matrix κ κ ℂ} (hQ : Red.IsConfig27B d Q) :
    IsConfig Q := by
  refine ⟨fun x => ⟨(hQ.1 x).1, (hQ.1 x).2⟩, fun k => ?_, fun k a b hab => ?_⟩
  · simp_rw [siteIdx_eq_qd]
    exact hQ.2 k k.isLt
  · rw [siteIdx_eq_qd, siteIdx_eq_qd]
    exact (Red.site_isPVM hQ k.isLt).mul_eq_zero hab

lemma three_mul_val_mod (a : ZMod 4) : (3 * a.val) % 4 = (-a).val := by
  revert a; decide

lemma negI_pow_eq_iz_neg (a : ZMod 4) : (-I) ^ a.val = Red.iz (-a) := by
  rw [Red.iz, ← three_mul_val_mod, Red.I_pow_mod, pow_mul]
  congr 1
  linear_combination (-I) * I_sq

lemma redV_Qcfg [NeZero d] {V : ℕ → Matrix κ κ ℂ} (hV : ∀ k, Red.IsUnitaryM (V k))
    (hV4 : ∀ k, V k ^ 4 = 1) (k : Fin d) : redV (Red.Qcfg d V) k = V k := by
  rw [Red.V_eq_sum hV hV4 k, redV]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [siteIdx_eq_qd, Red.Qcfg_qd V k.isLt, negI_pow_eq_iz_neg]

lemma sum_fin_lt (g : ℕ → ℕ → ℝ) :
    ∑ j : Fin d, ∑ k : Fin d, (if j < k then g j k else 0) = ∑ k ∈ range d, ∑ j ∈ range k, g j k := by
  rw [Finset.sum_comm, ← Fin.sum_univ_eq_sum_range (fun k => ∑ j ∈ range k, g j k) d]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : ∑ j : Fin d, (if j < k then g j k else 0)
      = ∑ j ∈ range d, (if j < (k : ℕ) then g j k else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => if j < (k : ℕ) then g j k else 0) d]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (Fin.lt_def.1 h1) h2
    · exact absurd (Fin.lt_def.2 h2) h1
    · rfl
  rw [h1, ← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  have := k.isLt
  omega

/-- The clock functional of this module agrees with that of module L2. -/
lemma clockF_eq_red (V : ℕ → Matrix κ κ ℂ) :
    clockF (fun k : Fin d => V k) = Red.clockF d V := by
  unfold clockF Red.clockF
  rw [sum_fin_lt (fun j k => (hm d (k - j) * ((V j * star (V k)).trace / Fintype.card κ)).re)]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  have hh : hm d (k - j) = Red.hd d (k - j) := rfl
  rw [hh, Red.ntr, star_eq_conjTranspose]

lemma FDKZ_eq_red (d : ℕ) : FDKZ d = Red.FDKZ d := by
  unfold FDKZ Red.FDKZ Red.secd Red.psi
  rfl

end Bridges

/-! ## Tensoring with `1_K` and conjugation by a unitary -/

section Kron

variable {d K : ℕ}

/-- `A ↦ A ⊗ 1_K`. -/
abbrev tens (K : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d × Fin K) (Fin d × Fin K) ℂ :=
  A ⊗ₖ (1 : Matrix (Fin K) (Fin K) ℂ)

lemma tens_mul (A B : Matrix (Fin d) (Fin d) ℂ) : tens K (A * B) = tens K A * tens K B := by
  rw [tens, tens, tens, ← mul_kronecker_mul, Matrix.mul_one]

lemma tens_one : tens K (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := one_kronecker_one

lemma tens_smul (c : ℂ) (A : Matrix (Fin d) (Fin d) ℂ) : tens K (c • A) = c • tens K A :=
  smul_kronecker c A 1

lemma tens_sub (A B : Matrix (Fin d) (Fin d) ℂ) : tens K (A - B) = tens K A - tens K B := by
  ext ⟨i, i'⟩ ⟨j, j'⟩
  simp [kroneckerMap_apply, sub_mul]

lemma tens_sum {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin d) (Fin d) ℂ) :
    tens K (∑ i ∈ s, A i) = ∑ i ∈ s, tens K (A i) := by
  ext ⟨i, i'⟩ ⟨j, j'⟩
  simp [kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul]

end Kron

section Conj

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  {u : Matrix m n ℂ}

lemma conj_mul (hu : uᴴ * u = 1) (X Y : Matrix n n ℂ) :
    u * (X * Y) * uᴴ = (u * X * uᴴ) * (u * Y * uᴴ) := by
  calc u * (X * Y) * uᴴ = u * X * (uᴴ * u) * Y * uᴴ := by
        rw [hu, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = (u * X * uᴴ) * (u * Y * uᴴ) := by simp only [Matrix.mul_assoc]

lemma conj_one (hu : u * uᴴ = 1) : u * (1 : Matrix n n ℂ) * uᴴ = 1 := by
  rw [Matrix.mul_one, hu]

lemma conj_smul (c : ℂ) (X : Matrix n n ℂ) : u * (c • X) * uᴴ = c • (u * X * uᴴ) := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

lemma conj_sub (X Y : Matrix n n ℂ) : u * (X - Y) * uᴴ = u * X * uᴴ - u * Y * uᴴ := by
  rw [Matrix.mul_sub, Matrix.sub_mul]

lemma conj_sum {ι : Type*} (s : Finset ι) (X : ι → Matrix n n ℂ) :
    u * (∑ i ∈ s, X i) * uᴴ = ∑ i ∈ s, u * X i * uᴴ := by
  rw [Matrix.mul_sum, Matrix.sum_mul]

end Conj

/-! ## The canonical form -/

lemma zd_eq_zeta (d : ℕ) [NeZero d] : Red.zd d = CGLMPRigidity.zeta d := by
  unfold Red.zd CGLMPRigidity.zeta
  congr 1
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  push_cast
  field_simp
  ring

/-- The canonical DKZ tuple `R^c` of `CGLMPRigidity.canonical_model`, indexed by `ℤ/4` like the chain of
module L2 (`canonR d s = R^c_{s+1}`). -/
noncomputable def canonR (d : ℕ) [NeZero d] : ZMod 4 → Matrix (Fin d) (Fin d) ℂ :=
  Red.vec4 (CGLMPRigidity.shiftM d) (CGLMPRigidity.R2m d) (CGLMPRigidity.R3m d)
    (CGLMPRigidity.R4m d)

lemma shiftM_eq_sum (d : ℕ) [NeZero d] :
    CGLMPRigidity.shiftM d = ∑ j ∈ range d, Matrix.single
      (⟨(j + 1) % d, Nat.mod_lt _ (NeZero.pos d)⟩ : Fin d)
      (⟨j % d, Nat.mod_lt _ (NeZero.pos d)⟩ : Fin d) (1 : ℂ) := by
  rw [CGLMPRigidity.shiftM,
    ← Fin.sum_univ_eq_sum_range (fun j => Matrix.single
      (⟨(j + 1) % d, Nat.mod_lt _ (NeZero.pos d)⟩ : Fin d)
      (⟨j % d, Nat.mod_lt _ (NeZero.pos d)⟩ : Fin d) (1 : ℂ)) d]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  · ext
    simp [Fin.val_add]
  · ext
    simp [Nat.mod_eq_of_lt j.isLt]

/-- **The canonical form** (`RIGIDITY_ALLD.md` s.6; `paper-classical-all-d` Corollary C via
`RIGIDITY.md` Theorems 3.8-3.9): a strategy attaining `I_ME(d)` whose 27B configuration commutes is, up to
a unitary `u : ℂ^D → ℂ^d ⊗ ℂ^K`, the canonical DKZ chain tensored with `1_K`. -/
theorem canonical_form {d : ℕ} [NeZero d] (hd : 2 ≤ d) (hB : Hyp_ClassicalTheoremB d) {D : ℕ}
    (hD : 0 < D) (S : Strategy d D)
    (hcomm : ∀ x y, Red.redConfig S x * Red.redConfig S y = Red.redConfig S y * Red.redConfig S x)
    (hS : S.cglmp = IME d) :
    ∃ K : ℕ, D = d * K ∧ ∃ u : Matrix (Fin d × Fin K) (Fin D) ℂ, u * uᴴ = 1 ∧ uᴴ * u = 1 ∧
      ∀ s : ZMod 4, u * Red.chainR (Red.stratA S) (Red.stratB S) s * uᴴ = tens K (canonR d s) := by
  have hd0 : d ≠ 0 := NeZero.ne d
  set R := Red.chainR (Red.stratA S) (Red.stratB S) with hRdef
  set V := Red.redFamily S with hVdef
  set Q := Red.redConfig S with hQdef
  have hU : ∀ s, Red.IsUnitaryM (R s) :=
    Red.chainR_unitary _ _ (Red.stratA_isPVM S) (Red.stratB_isPVM S)
  have hpow : ∀ s, R s ^ d = 1 := Red.chainR_pow_d _ _ (Red.stratA_isPVM S) (Red.stratB_isPVM S)
  have hV : ∀ k, Red.IsUnitaryM (V k) := Red.redFamily_unitary S
  have hV4 : ∀ k, V k ^ 4 = 1 := Red.redFamily_pow_four S
  have hQ : IsConfig Q := isConfig_of_isConfig27B (Red.redConfig_isConfig S)
  have hredV : ∀ k : Fin d, redV Q k = V k := redV_Qcfg hV hV4
  -- `F(V) = F_DKZ`
  have hF : clockF (redV Q) = FDKZ d := by
    have h1 := (Red.deficit_strategy hd hD S).1
    rw [hS, sub_self] at h1
    have hpos : 0 < 4 / ((d : ℝ) * ((d : ℝ) - 1)) := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      apply div_pos four_pos
      nlinarith
    have h2 : Red.FDKZ d - Red.clockF d V = 0 := by
      rcases mul_eq_zero.1 h1.symm with h | h
      · exact absurd h hpos.ne'
      · exact h
    have e : redV Q = fun k : Fin d => V k := funext hredV
    rw [e, clockF_eq_red, FDKZ_eq_red]
    linarith
  -- the commutative sector
  obtain ⟨hcommV, hrel⟩ := commuting_optimal_relations hB hQ hcomm hF
  have hc01 : Red.Vred d R 0 * Red.Vred d R 1 = Red.Vred d R 1 * Red.Vred d R 0 := by
    have h := hcommV ⟨0, by omega⟩ ⟨1, by omega⟩
    rw [hredV, hredV] at h
    exact h
  have hrel' : ∀ n, 1 ≤ n → n < d →
      (Red.Vred d R 0 * (Red.Vred d R n)ᴴ - 1) * (Red.Vred d R 0 * (Red.Vred d R n)ᴴ - I • 1) = 0 := by
    intro n hn1 hnd
    have h := hrel n hn1 hnd.le ⟨n, hnd⟩
    have e : relY (redV Q) n ⟨n, hnd⟩ = Red.Vred d R 0 * (Red.Vred d R n)ᴴ := by
      unfold relY
      rw [dif_pos (le_refl n)]
      rw [hredV, hredV, star_eq_conjTranspose]
      simp
      rfl
    rw [e] at h
    exact h
  -- algebraic rigidity
  obtain ⟨p, hp, h1, h2, h3, hmu, hstar, hsum, hR0⟩ := rigidity_of_Vred hd R hU hpow hc01 hrel'
  have hstar' : ∀ j k, (CGLMPRigidity.mu (R 0) p j k)ᴴ = CGLMPRigidity.mu (R 0) p k j := by
    intro j k
    rw [← star_eq_conjTranspose]
    exact hstar j k
  obtain ⟨K, hDK, u, hu1, hu2, hue⟩ :=
    exists_unitary_of_matrixUnits d (by omega) (CGLMPRigidity.mu (R 0) p) hmu hstar' hsum
  refine ⟨K, hDK, u, hu1, hu2, ?_⟩
  -- images of `R_1` and of `p`
  have hφR0 : u * R 0 * uᴴ = tens K (CGLMPRigidity.shiftM d) := by
    conv_lhs => rw [hR0]
    rw [conj_sum, shiftM_eq_sum, tens_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    have h := hue ⟨(j + 1) % d, Nat.mod_lt _ (NeZero.pos d)⟩ ⟨j, hj'⟩
    simp only at h
    rw [h]
    simp only [Nat.mod_eq_of_lt hj']
  have hφp : u * p * uᴴ = tens K (CGLMPRigidity.proj0 d) := by
    have h := hue ⟨0, NeZero.pos d⟩ ⟨0, NeZero.pos d⟩
    have e : CGLMPRigidity.mu (R 0) p 0 0 = p := by simp [CGLMPRigidity.mu]
    simp only at h
    rw [e] at h
    rw [h]
    rfl
  -- the recursion `R_{k+1} = z D R_k`
  have hstep : ∀ X : Matrix (Fin D) (Fin D) ℂ, ∀ Y : Matrix (Fin d) (Fin d) ℂ,
      u * X * uᴴ = tens K Y →
      u * (Red.zd d • ((1 - (1 + I) • p) * X)) * uᴴ
        = tens K (CGLMPRigidity.zeta d • (CGLMPRigidity.Dm d * Y)) := by
    intro X Y hX
    rw [conj_smul, conj_mul hu2, conj_sub, conj_one hu1, conj_smul, hφp, hX, zd_eq_zeta,
      CGLMPRigidity.Dm, tens_smul, tens_mul, tens_sub, tens_one, tens_smul]
  have hφR1 : u * R 1 * uᴴ = tens K (CGLMPRigidity.R2m d) := by
    rw [h1]; exact hstep _ _ hφR0
  have hφR2 : u * R 2 * uᴴ = tens K (CGLMPRigidity.R3m d) := by
    rw [h2]; exact hstep _ _ hφR1
  have hφR3 : u * R 3 * uᴴ = tens K (CGLMPRigidity.R4m d) := by
    rw [h3]; exact hstep _ _ hφR2
  intro s
  obtain rfl | rfl | rfl | rfl : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by revert s; decide
  · rw [hφR0]; simp [canonR]
  · rw [hφR1]; simp [canonR]
  · rw [hφR2]; simp [canonR]
  · rw [hφR3]; simp [canonR]

end OQP27.Rig
