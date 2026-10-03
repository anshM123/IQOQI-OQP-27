import OQP27.ReductionCsc
import OQP27.ReductionCovariant
import OQP27.ReductionProj
import OQP27.ReductionTwirl
import OQP27.Skeleton

/-!
# OQP 27B, module L2 (reduction): main theorems and the discharge of `OQP27.Hyp_Reduction`

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

Paper chain formalised in `OQP27/Reduction*.lean` (all steps PROVED, no hypotheses):

  projective strategy on `Φ_D`  (`OQP27.Strategy`, module L1)
    → chain unitaries `R_1 … R_4`                       (`OQP27.Red.chainR`; paper eq. (chainR))
    → chain form `I_d = 4 - 2S/(d-1)`                   (`OQP27.Red.cglmp_eq_chain`; paper Lemma 2.1)
    → trace form `S = 2(d-1) + ∑ c_n Λ_n(R)`            (`OQP27.Red.chainS_trace`; paper eq. (Strace))
    → reduced family `V_0 … V_{d-1}`, `V_k^4 = 1`       (`OQP27.Red.Vred`; paper Theorem 2.3(2), appendix)
    → `I_d = 4 F(V)/(d(d-1))`                            (`OQP27.Red.cglmp_eq_clockF`)
    → 27B configuration `Q_x` (spectral projections)    (`OQP27.Red.Qcfg`; paper eq. (projform))
    → `F(V) = ∑_{m=1}^{d-1} csc(πm/(2d)) N(m)`            (`OQP27.Red.clockF_eq_csc`; QD-L7)
    → `I_d = I_ME(d) + 2/(d(d-1)) ⟨v, δ⟩`                (`OQP27.Red.hyp_reduction`).

This file proves `OQP27.Hyp_Reduction d` of `OQP27/Skeleton.lean` for every `d ≥ 1` (theorem
`OQP27.Red.hyp_reduction`), the equivalence `F(V) ≤ F_DKZ ⟺ I_d ≤ I_ME(d)` with the deficit formula, and
`I_ME(d) = 4 F_DKZ/(d(d-1))`.
-/

namespace OQP27.Red

open Complex Finset ComplexConjugate Matrix
open scoped Real

noncomputable section

/-! ### `F_DKZ` and `I_ME(d)` -/

/-- `F_DKZ = F(1, …, 1) = ∑_{m=1}^{d-1} (d - m) sec(π m/(2d))` (paper eq. (FDKZ)). -/
def FDKZ (d : ℕ) : ℝ := ∑ m ∈ Ico 1 d, ((d : ℝ) - m) * secd d m

/-- `F_DKZ = ∑_{m=1}^{d-1} m csc(π m/(2d))`. -/
theorem FDKZ_eq_csc (d : ℕ) : FDKZ d = ∑ m ∈ Ico 1 d, (m : ℝ) * cscd d m := by
  unfold FDKZ
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  rw [← sum_Ico_reflect' (fun m => (m : ℝ) * cscd d m) d]
  refine sum_congr rfl fun m hm => ?_
  have hm' := mem_Ico.1 hm
  rw [Nat.cast_sub hm'.2.le, cscd_reflect hd.ne' hm'.2.le]

/-- `I_ME(d) = 4 F_DKZ / (d(d-1))` (paper eq. (FDKZ)). -/
theorem IME_eq_FDKZ (d : ℕ) : IME d = 4 * FDKZ d / ((d : ℝ) * ((d : ℝ) - 1)) := by
  have h : ∑ j ∈ Ico 1 d, ((d : ℝ) - j) / Real.cos (π * j / (2 * d)) = FDKZ d := by
    refine sum_congr rfl fun j _ => ?_
    rw [secd, psi, mul_one_div]
  rw [IME, h]
  ring

/-! ### From `OQP27.Strategy` (module L1) to the chain unitaries -/

section Adapter

variable {d D : ℕ} [NeZero d]

/-- `ℤ/d → Fin d`, `a ↦ a.val`. -/
def zToFin (a : ZMod d) : Fin d := ⟨a.val, ZMod.val_lt a⟩

lemma natCast_zToFin (a : ZMod d) : (((zToFin a : Fin d) : ℕ) : ZMod d) = a :=
  ZMod.natCast_zmod_val a

lemma zToFin_natCast (i : Fin d) : zToFin ((i : ℕ) : ZMod d) = i := by
  ext
  simp [zToFin, ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt]

/-- The equivalence `ℤ/d ≃ Fin d`. -/
def zFinEquiv : ZMod d ≃ Fin d where
  toFun := zToFin
  invFun i := ((i : ℕ) : ZMod d)
  left_inv := natCast_zToFin
  right_inv := zToFin_natCast

/-- Alice's measurements of a strategy, with outcomes in `ℤ/d`. -/
def stratA (S : Strategy d D) : Fin 2 → ZMod d → Matrix (Fin D) (Fin D) ℂ :=
  fun x a => (S.A x).proj (zToFin a)

/-- Bob's measurements of a strategy, with outcomes in `ℤ/d`. -/
def stratB (S : Strategy d D) : Fin 2 → ZMod d → Matrix (Fin D) (Fin D) ℂ :=
  fun y b => (S.B y).proj (zToFin b)

lemma pvm_isPVM (P : PVM d D) : IsPVM (fun a : ZMod d => P.proj (zToFin a)) := by
  refine ⟨fun a => P.isProj _, ?_⟩
  rw [← P.sum_eq_one]
  exact Fintype.sum_equiv zFinEquiv _ _ (fun a => rfl)

lemma stratA_isPVM (S : Strategy d D) (x : Fin 2) : IsPVM (stratA S x) := pvm_isPVM (S.A x)

lemma stratB_isPVM (S : Strategy d D) (y : Fin 2) : IsPVM (stratB S y) := pvm_isPVM (S.B y)

lemma probME_strat (S : Strategy d D) (x y : Fin 2) (a b : ZMod d) :
    probME (stratA S) (stratB S) x y a b = S.prob x y (zToFin a) (zToFin b) := by
  rw [probME, Fintype.card_fin]
  rfl

lemma sum_zmod_eq_sum_fin {M : Type*} [AddCommMonoid M] (F : ZMod d → M) :
    ∑ a : ZMod d, F a = ∑ i : Fin d, F ((i : ℕ) : ZMod d) :=
  (Fintype.sum_equiv zFinEquiv.symm _ _ (fun _ => rfl)).symm

lemma probAB_eq (S : Strategy d D) (x y : Fin 2) (k : ℤ) :
    S.probAB x y k = pAB (probME (stratA S) (stratB S)) x y (k : ZMod d) := by
  unfold Strategy.probAB pAB
  rw [sum_zmod_eq_sum_fin]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_zmod_eq_sum_fin]
  refine sum_congr rfl fun j _ => ?_
  rw [probME_strat, zToFin_natCast, zToFin_natCast]

lemma probBA_eq (S : Strategy d D) (x y : Fin 2) (k : ℤ) :
    S.probBA x y k = pBA (probME (stratA S) (stratB S)) x y (k : ZMod d) := by
  unfold Strategy.probBA pBA
  rw [sum_zmod_eq_sum_fin]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_zmod_eq_sum_fin]
  refine sum_congr rfl fun j _ => ?_
  rw [probME_strat, zToFin_natCast, zToFin_natCast]

/-- The CGLMP value of module L1 (`OQP27.Strategy.cglmp`) is the CGLMP expression `OQP27.Red.cglmp` of the
maximally entangled probabilities. -/
theorem cglmp_strategy (S : Strategy d D) : S.cglmp = cglmp (probME (stratA S) (stratB S)) := by
  unfold Strategy.cglmp cglmp
  refine sum_congr rfl fun k _ => ?_
  simp only [probAB_eq, probBA_eq]
  push_cast
  rfl

end Adapter

/-! ### The reduction for strategies of module L1 -/

section Main

variable {d D : ℕ} [NeZero d]

/-- The reduced family of a strategy (paper Theorem 2.3(2)): `M = 4D`, index set `ℤ/4 × Fin D`. -/
def redFamily (S : Strategy d D) : ℕ → Matrix (ZMod 4 × Fin D) (ZMod 4 × Fin D) ℂ :=
  Vred d (chainR (stratA S) (stratB S))

theorem redFamily_unitary (S : Strategy d D) (k : ℕ) : IsUnitaryM (redFamily S k) :=
  Vred_unitary _ (chainR_unitary _ _ (stratA_isPVM S) (stratB_isPVM S)) k

theorem redFamily_pow_four (S : Strategy d D) (k : ℕ) : redFamily S k ^ 4 = 1 :=
  Vred_pow_four (NeZero.ne d) _ (chainR_unitary _ _ (stratA_isPVM S) (stratB_isPVM S)) k

/-- **Theorem 2.3(2) of the paper** for the strategies of module L1: `I_d = 4 F(V)/(d(d-1))`. -/
theorem cglmp_eq_clockF_strategy (hd : 2 ≤ d) (hD : 0 < D) (S : Strategy d D) :
    S.cglmp = 4 * clockF d (redFamily S) / ((d : ℝ) * ((d : ℝ) - 1)) := by
  have : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  rw [cglmp_strategy, cglmp_eq_clockF hd _ _ (stratA_isPVM S) (stratB_isPVM S)]
  rfl

/-- The 27B configuration of a strategy: spectral projections of its reduced family. -/
def redConfig (S : Strategy d D) : ZMod (4 * d) → Matrix (ZMod 4 × Fin D) (ZMod 4 × Fin D) ℂ :=
  Qcfg d (redFamily S)

theorem redConfig_isConfig (S : Strategy d D) : IsConfig27B d (redConfig S) :=
  Qcfg_isConfig (redFamily_unitary S) (redFamily_pow_four S)

/-- **Strategy → linear form (QD-L7)**: `I_d = (4/(d(d-1))) ∑_{m=1}^{d-1} csc(πm/(2d)) N(m)`. -/
theorem cglmp_eq_csc_strategy (hd : 2 ≤ d) (hD : 0 < D) (S : Strategy d D) :
    S.cglmp = 4 / ((d : ℝ) * ((d : ℝ) - 1)) *
      ∑ m ∈ Ico 1 d, cscd d m * Nnet d (redConfig S) m := by
  rw [cglmp_eq_clockF_strategy hd hD S,
    clockF_eq_csc (redFamily_unitary S) (redFamily_pow_four S)]
  unfold redConfig
  ring

/-- **The deficit formula**: `I_ME(d) - I_d = (4/(d(d-1))) (F_DKZ - F(V))
= (4/(d(d-1))) ∑_{m=1}^{d-1} csc(πm/(2d)) (m - N(m))`. -/
theorem deficit_strategy (hd : 2 ≤ d) (hD : 0 < D) (S : Strategy d D) :
    IME d - S.cglmp = 4 / ((d : ℝ) * ((d : ℝ) - 1)) * (FDKZ d - clockF d (redFamily S)) ∧
    IME d - S.cglmp = 4 / ((d : ℝ) * ((d : ℝ) - 1)) *
      ∑ m ∈ Ico 1 d, cscd d m * ((m : ℝ) - Nnet d (redConfig S) m) := by
  constructor
  · rw [IME_eq_FDKZ, cglmp_eq_clockF_strategy hd hD S]
    ring
  · rw [IME_eq_FDKZ, cglmp_eq_csc_strategy hd hD S, FDKZ_eq_csc]
    have e : 4 * (∑ m ∈ Ico 1 d, (m : ℝ) * cscd d m) / ((d : ℝ) * ((d : ℝ) - 1))
        = 4 / ((d : ℝ) * ((d : ℝ) - 1)) * ∑ m ∈ Ico 1 d, (m : ℝ) * cscd d m := by ring
    rw [e, ← mul_sub, ← sum_sub_distrib]
    congr 1
    refine sum_congr rfl fun m _ => ?_
    ring

/-- **The equivalence** `F(V) ≤ F_DKZ ⟺ I_d ≤ I_ME(d)` for the reduced family of a strategy. -/
theorem cglmp_le_IME_iff (hd : 2 ≤ d) (hD : 0 < D) (S : Strategy d D) :
    S.cglmp ≤ IME d ↔ clockF d (redFamily S) ≤ FDKZ d := by
  have hpos : 0 < 4 / ((d : ℝ) * ((d : ℝ) - 1)) := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    apply div_pos four_pos
    nlinarith
  have h := (deficit_strategy hd hD S).1
  constructor
  · intro hle
    have : 0 ≤ 4 / ((d : ℝ) * ((d : ℝ) - 1)) * (FDKZ d - clockF d (redFamily S)) := by linarith
    have := (mul_nonneg_iff_of_pos_left hpos).1 this
    linarith
  · intro hle
    have : 0 ≤ 4 / ((d : ℝ) * ((d : ℝ) - 1)) * (FDKZ d - clockF d (redFamily S)) :=
      mul_nonneg hpos.le (by linarith)
    linarith

/-- **Optimality from the clock-model inequality**: if `F(V) ≤ F_DKZ` for every family of order-4
unitaries (of any size), then `I_d ≤ I_ME(d)` for every projective strategy on a maximally entangled
state (paper Theorem 2.3, "consequently" clause, direction `⇐`). -/
theorem optimality_of_clock (hd : 2 ≤ d)
    (h : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] [Nonempty κ] (V : ℕ → Matrix κ κ ℂ),
      (∀ k, IsUnitaryM (V k)) → (∀ k, V k ^ 4 = 1) → clockF d V ≤ FDKZ d) :
    OptimalityStatement d := by
  intro D hD S
  have : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  exact (cglmp_le_IME_iff hd hD S).2 (h _ _ (redFamily_unitary S) (redFamily_pow_four S))

end Main

/-! ### Transport to `Fin (4D)` and the discharge of `OQP27.Hyp_Reduction` -/

section Transport

variable {κ κ' : Type*} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']

omit [DecidableEq κ] [DecidableEq κ'] in
lemma trace_submatrix_equiv (X : Matrix κ κ ℂ) (f : κ' ≃ κ) : trace (X.submatrix f f) = trace X := by
  unfold trace
  exact Equiv.sum_comp f (fun j => X j j)

omit [Fintype κ] [Fintype κ'] [DecidableEq κ] [DecidableEq κ'] in
lemma submatrix_sum_equiv {ι : Type*} (s : Finset ι) (X : ι → Matrix κ κ ℂ) (f : κ' ≃ κ) :
    (∑ i ∈ s, X i).submatrix f f = ∑ i ∈ s, (X i).submatrix f f := by
  ext p q
  simp [Matrix.sum_apply]

end Transport

section Discharge

variable {d D : ℕ} [NeZero d]

/-- `ℤ/4 × Fin D ≃ Fin (4D)`. -/
def prodEquiv (D : ℕ) : ZMod 4 × Fin D ≃ Fin (4 * D) :=
  (Equiv.prodCongr (ZMod.finEquiv 4).toEquiv.symm (Equiv.refl _)).trans finProdFinEquiv

omit [NeZero d] in
lemma siteIndex_eq_qd (k : Fin d) (a : ZMod 4) : siteIndex d k a = qd d k a := by
  rw [qd_eq, siteIndex, mu]

/-- The 27B configuration of a strategy as an `OQP27.QConfig d (4D)` (module L1). -/
def toQConfig (S : Strategy d D) : QConfig d (4 * D) where
  Q x := (redConfig S x).submatrix (prodEquiv D).symm (prodEquiv D).symm
  isProj x := by
    have h := (redConfig_isConfig S).1 x
    refine ⟨h.1.submatrix _, ?_⟩
    rw [submatrix_mul_equiv, h.2]
  pvm k := by
    rw [← submatrix_sum_equiv]
    simp_rw [siteIndex_eq_qd]
    rw [(redConfig_isConfig S).2 k k.isLt, submatrix_one_equiv]

lemma toQConfig_corr (S : Strategy d D) (n : ZMod (4 * d)) :
    (toQConfig S).corr n = Ccorr d (redConfig S) n := by
  unfold QConfig.corr Ccorr
  refine sum_congr rfl fun u _ => ?_
  simp only [toQConfig]
  rw [submatrix_mul_equiv, trace_submatrix_equiv, ntr, Fintype.card_prod, ZMod.card,
    Fintype.card_fin, Complex.div_natCast_re]

lemma toQConfig_delta (S : Strategy d D) (m : ℕ) :
    (toQConfig S).delta m = Nnet d (redConfig S) m - m := by
  rw [QConfig.delta, QConfig.netCount_eq_corr, toQConfig_corr, toQConfig_corr, Nnet]

/-- **`OQP27.Hyp_Reduction d` holds for every `d ≥ 1`** (the reduction strategy → clock model →
Q-configuration → linear form; paper Theorem 2.3 and appendix, QD-L7, RIGIDITY_ALLD.md 1.2-1.4). -/
theorem hyp_reduction : Hyp_Reduction d := by
  intro D hD S
  refine ⟨4 * D, by omega, toQConfig S, ?_⟩
  rcases (show d = 1 ∨ 2 ≤ d by have := NeZero.ne d; omega) with h1 | hd
  · subst h1
    simp [Strategy.cglmp, IME, pairingIco]
  · have hδ : (toQConfig S).delta = fun m => Nnet d (redConfig S) m - m :=
      funext (toQConfig_delta S)
    rw [cglmp_eq_csc_strategy hd hD S, hδ]
    refine Eq.trans ?_ (clock_value_eq_linear d (fun m => Nnet d (redConfig S) m))
    congr 1
    refine sum_congr rfl fun m _ => ?_
    rw [cscd, psi]
    ring

end Discharge

/-! ### The equivalences (paper Theorem 2.3, "consequently" clause) -/

section Equivalence

variable {d : ℕ} [NeZero d]

/-- A projective measurement on `ℂ^ι` (outcomes in `ℤ/d`) as an `OQP27.PVM d D` (module L1), along a
bijection `ι ≃ Fin D`. -/
def toPVM {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ} (e : ι ≃ Fin D)
    (P : ZMod d → Matrix ι ι ℂ) (hP : IsPVM P) : PVM d D where
  proj i := (P ((i : ℕ) : ZMod d)).submatrix e.symm e.symm
  isProj i := ⟨(hP.1 _).1.submatrix _, by rw [submatrix_mul_equiv, (hP.1 _).2]⟩
  sum_eq_one := by
    rw [← submatrix_sum_equiv, ← sum_zmod_eq_sum_fin (fun a => P a), hP.2, submatrix_one_equiv]

/-- The covariant strategy of a clock family as an `OQP27.Strategy` (module L1), on `ℂ^D`,
`D = d · |κ|`. -/
def covStrategy {κ : Type} [Fintype κ] [DecidableEq κ] (V : ℕ → Matrix κ κ ℂ)
    (hV : ∀ k, IsUnitaryM (V k)) : Strategy d (Fintype.card (ZMod d × κ)) where
  A x := toPVM (Fintype.equivFin _) (covA d V x) (covA_isPVM hV x)
  B y := toPVM (Fintype.equivFin _) (covB d V y) (covB_isPVM hV y)

lemma probME_covStrategy {κ : Type} [Fintype κ] [DecidableEq κ] (V : ℕ → Matrix κ κ ℂ)
    (hV : ∀ k, IsUnitaryM (V k)) :
    probME (stratA (covStrategy V hV)) (stratB (covStrategy V hV)) = probME (covA d V) (covB d V) := by
  funext x y a b
  simp only [probME, stratA, stratB, covStrategy, toPVM, natCast_zToFin]
  rw [transpose_submatrix, submatrix_mul_equiv, trace_submatrix_equiv, Fintype.card_fin]

/-- **Theorem 2.3(2), equality of values**: a strategy and the covariant strategy of its reduced family
have the same CGLMP value, `I_d(R) = I_d(R^V) = 4F(V)/(d(d-1))`. -/
theorem cglmp_eq_cglmp_cov (hd : 2 ≤ d) {D : ℕ} (hD : 0 < D) (S : Strategy d D) :
    S.cglmp = cglmp (probME (covA d (redFamily S)) (covB d (redFamily S))) := by
  have : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  rw [cglmp_eq_clockF_strategy hd hD S, (cglmp_cov hd (redFamily_unitary S) (redFamily_pow_four S)).2]

/-- **Theorem 2.3(2), direct summand**: every projective strategy on `Φ_D` is unitarily equivalent to a direct
summand of the covariant strategy of its reduced family: the isometry `J : ℂ^D → ℂ^d ⊗ ℂ^{4D}`
(`J^* J = 1`) satisfies `R^V_i J = J R_i` for the four chain unitaries. -/
theorem redFamily_direct_summand {D : ℕ} (S : Strategy d D) :
    (Jt d (chainR (stratA S) (stratB S)) 0)ᴴ * Jt d (chainR (stratA S) (stratB S)) 0 = 1 ∧
    ∀ s : ZMod 4, Rcov d (redFamily S) s * Jt d (chainR (stratA S) (stratB S)) 0
      = Jt d (chainR (stratA S) (stratB S)) 0 * chainR (stratA S) (stratB S) s := by
  have hR := chainR_unitary _ _ (stratA_isPVM S) (stratB_isPVM S)
  have hRd := chainR_pow_d _ _ (stratA_isPVM S) (stratB_isPVM S)
  exact ⟨Jt_isometry _ 0 (hR 0), direct_summand _ hR hRd⟩

/-- **Converse direction of Theorem 2.3**: if `I_d ≤ I_ME(d)` for every projective strategy on a maximally
entangled state, then `F(V) ≤ F_DKZ` for every family of order-4 unitaries (via the covariant strategy,
Theorem 2.3(1)). -/
theorem clock_of_optimality (hd : 2 ≤ d) (hopt : OptimalityStatement d) {κ : Type} [Fintype κ]
    [DecidableEq κ] [Nonempty κ] (V : ℕ → Matrix κ κ ℂ) (hV : ∀ k, IsUnitaryM (V k))
    (hV4 : ∀ k, V k ^ 4 = 1) : clockF d V ≤ FDKZ d := by
  have hD : 0 < Fintype.card (ZMod d × κ) := Fintype.card_pos
  have h1 := hopt _ hD (covStrategy V hV)
  rw [cglmp_strategy, probME_covStrategy, (cglmp_cov hd hV hV4).2, IME_eq_FDKZ] at h1
  have hpos : 0 < (d : ℝ) * ((d : ℝ) - 1) := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have := (div_le_div_iff_of_pos_right hpos).1 h1
  linarith

/-- **Theorem 2.3 of the paper, "consequently" clause**: `I_d ≤ I_ME(d)` for all projective strategies on
maximally entangled states (of every dimension) if and only if `F(V) ≤ F_DKZ` for all families of
order-4 unitaries (of every size). -/
theorem optimality_iff_clock (hd : 2 ≤ d) :
    OptimalityStatement d ↔ ∀ (κ : Type) [Fintype κ] [DecidableEq κ] [Nonempty κ]
      (V : ℕ → Matrix κ κ ℂ), (∀ k, IsUnitaryM (V k)) → (∀ k, V k ^ 4 = 1) → clockF d V ≤ FDKZ d :=
  ⟨fun h _ _ _ _ V hV hV4 => clock_of_optimality hd h V hV hV4, optimality_of_clock hd⟩

omit [NeZero d] in
lemma qcfg_isConfig27B {M : ℕ} (C : QConfig d M) : IsConfig27B d C.Q := by
  refine ⟨C.isProj, fun k hk => ?_⟩
  have h := C.pvm ⟨k, hk⟩
  simp_rw [siteIndex_eq_qd] at h
  exact h

lemma qcfg_corr_eq_Ccorr {M : ℕ} (C : QConfig d M) (n : ZMod (4 * d)) :
    C.corr n = Ccorr d C.Q n := by
  unfold QConfig.corr Ccorr
  refine sum_congr rfl fun u _ => ?_
  rw [ntr, Fintype.card_fin, Complex.div_natCast_re]

lemma qcfg_delta_eq {M : ℕ} (C : QConfig d M) (m : ℕ) : C.delta m = Nnet d C.Q m - m := by
  rw [QConfig.delta, QConfig.netCount_eq_corr, qcfg_corr_eq_Ccorr, qcfg_corr_eq_Ccorr, Nnet]

/-- `⟨v, δ⟩ = 2 ∑_m csc(πm/(2d)) N(m) - 2 F_DKZ`. -/
lemma pairing_delta_eq {M : ℕ} (C : QConfig d M) :
    pairingIco d (coneV d) C.delta = 2 * (∑ m ∈ Ico 1 d, cscd d m * Nnet d C.Q m) - 2 * FDKZ d := by
  rw [pairingIco, FDKZ_eq_csc, mul_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun m _ => ?_
  rw [qcfg_delta_eq, coneV, cscd, psi]
  ring

/-- **Optimality ⟺ the linear form is nonpositive on every 27B configuration**: `I_d ≤ I_ME(d)` for all
projective strategies on maximally entangled states if and only if `⟨v, δ⟩ ≤ 0` for every 27B
configuration (of every size), `v_m = 2 csc(πm/(2d))`, `δ_m = N(m) - m`. -/
theorem optimality_iff_config (hd : 2 ≤ d) :
    OptimalityStatement d ↔ ∀ M : ℕ, 0 < M → ∀ C : QConfig d M, pairingIco d (coneV d) C.delta ≤ 0 := by
  constructor
  · intro hopt M hM C
    have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
    have hQ := qcfg_isConfig27B C
    have h := clock_of_optimality hd hopt (famOf d C.Q) (famOf_unitary hQ) (famOf_pow_four hQ)
    rw [clockF_eq_csc (famOf_unitary hQ) (famOf_pow_four hQ), Qcfg_famOf hQ] at h
    rw [pairing_delta_eq]
    linarith
  · intro h D hD S
    obtain ⟨M, hM, C, hS⟩ := hyp_reduction (d := d) D hD S
    rw [hS]
    have := h M hM C
    have hpos : 0 < 2 / ((d : ℝ) * ((d : ℝ) - 1)) := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      apply div_pos two_pos
      nlinarith
    nlinarith

end Equivalence

end

end OQP27.Red
