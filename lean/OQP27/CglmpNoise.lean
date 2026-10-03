import OQP27.Main

/-!
# Noise resistance of the CGLMP violation (OQP 27B, noise clause, CGLMP reading)

For an arbitrary behaviour `p : Fin 2 → Fin 2 → Fin d → Fin d → ℝ`, `cglmpOf p` is the CGLMP expression
`Strategy.cglmp` evaluated on `p` (`cglmpOf_prob`: on the behaviour of a strategy it is `Strategy.cglmp`).

* `cglmpOf_unif`: the CGLMP expression vanishes on the behaviour `unif d` of completely random, uniform outcomes.
* `cglmpOf_noisy`: mixing with uniform noise scales it, `cglmpOf (v p + (1 - v) u) = v * cglmpOf p`.
* `noisy_violation_iff`: the noisy behaviour of a projective strategy on a maximally entangled state violates the CGLMP
  inequality (`2 < I_d`) if and only if `2 < v * I_d(S)`; so the CGLMP noise threshold of `S` is `2 / I_d(S)`.
* `noisy_violation_imp_le_twenty` (no hypotheses, `2 ≤ d ≤ 20`) and `noisy_violation_imp` (every `d`, given `CONE_d`
  for `d ≥ 21`): a violation needs `2 < v * IME d`; `dkz_noisy_violation_iff`: DKZ violates exactly when
  `2 < v * IME d`.  Hence DKZ has the lowest CGLMP noise threshold, `2 / IME d`, and by the rigidity theorem it is the
  only strategy (up to `u ⊗ ū` and an inert identity factor) with `I_d(S) = IME d`.
-/

namespace OQP27

open Finset

variable {d D : ℕ}

/-- `P(A_x = B_y + k)` for a behaviour `p`. -/
noncomputable def bprobAB (p : Fin 2 → Fin 2 → Fin d → Fin d → ℝ) (x y : Fin 2) (k : ℤ) : ℝ :=
  ∑ a : Fin d, ∑ b : Fin d,
    if ((a : ℕ) : ZMod d) = ((b : ℕ) : ZMod d) + (k : ZMod d) then p x y a b else 0

/-- `P(B_y = A_x + k)` for a behaviour `p`. -/
noncomputable def bprobBA (p : Fin 2 → Fin 2 → Fin d → Fin d → ℝ) (x y : Fin 2) (k : ℤ) : ℝ :=
  ∑ a : Fin d, ∑ b : Fin d,
    if ((b : ℕ) : ZMod d) = ((a : ℕ) : ZMod d) + (k : ZMod d) then p x y a b else 0

/-- The CGLMP expression of an arbitrary behaviour; the same formula as `Strategy.cglmp`. -/
noncomputable def cglmpOf (p : Fin 2 → Fin 2 → Fin d → Fin d → ℝ) : ℝ :=
  ∑ k ∈ range (d / 2), (1 - 2 * (k : ℝ) / ((d : ℝ) - 1)) *
    ((bprobAB p 0 0 k + bprobBA p 1 0 (k + 1) + bprobAB p 1 1 k + bprobBA p 0 1 k) -
      (bprobAB p 0 0 (-(k : ℤ) - 1) + bprobBA p 1 0 (-(k : ℤ)) + bprobAB p 1 1 (-(k : ℤ) - 1) +
        bprobBA p 0 1 (-(k : ℤ) - 1)))

/-- On the behaviour of a strategy, `cglmpOf` is the CGLMP value of the strategy. -/
theorem cglmpOf_prob (S : Strategy d D) : cglmpOf S.prob = S.cglmp := rfl

/-- The behaviour of completely random, uniform outcomes. -/
noncomputable def unif (d : ℕ) : Fin 2 → Fin 2 → Fin d → Fin d → ℝ := fun _ _ _ _ => 1 / ((d : ℝ) ^ 2)

/-- The behaviour `p` mixed with uniform noise at visibility `v`. -/
noncomputable def noisy (p : Fin 2 → Fin 2 → Fin d → Fin d → ℝ) (v : ℝ) :
    Fin 2 → Fin 2 → Fin d → Fin d → ℝ :=
  fun x y a b => v * p x y a b + (1 - v) * unif d x y a b

lemma sum_fin_ite_eq_real [NeZero d] (c : ZMod d) (r : ℝ) :
    ∑ a : Fin d, (if ((a : ℕ) : ZMod d) = c then r else 0) = r := by
  have key : ∀ a : Fin d, ((a : ℕ) : ZMod d) = c ↔ a = ⟨c.val, ZMod.val_lt c⟩ := by
    intro a
    constructor
    · intro h
      ext
      simp only
      rw [← h, ZMod.val_natCast, Nat.mod_eq_of_lt a.isLt]
    · intro h
      subst h
      simp
  simp_rw [key]
  simp

lemma bprobAB_unif [NeZero d] (x y : Fin 2) (k : ℤ) : bprobAB (unif d) x y k = 1 / (d : ℝ) := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  unfold bprobAB unif
  rw [Finset.sum_comm]
  simp_rw [sum_fin_ite_eq_real]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

lemma bprobBA_unif [NeZero d] (x y : Fin 2) (k : ℤ) : bprobBA (unif d) x y k = 1 / (d : ℝ) := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  unfold bprobBA unif
  simp_rw [sum_fin_ite_eq_real]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The CGLMP expression vanishes on the uniform behaviour. -/
theorem cglmpOf_unif [NeZero d] : cglmpOf (unif d) = 0 := by
  unfold cglmpOf
  simp only [bprobAB_unif, bprobBA_unif, sub_self, mul_zero, Finset.sum_const_zero]

lemma bprobAB_noisy (p : Fin 2 → Fin 2 → Fin d → Fin d → ℝ) (v : ℝ) (x y : Fin 2) (k : ℤ) :
    bprobAB (noisy p v) x y k = v * bprobAB p x y k + (1 - v) * bprobAB (unif d) x y k := by
  unfold bprobAB noisy
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> ring

lemma bprobBA_noisy (p : Fin 2 → Fin 2 → Fin d → Fin d → ℝ) (v : ℝ) (x y : Fin 2) (k : ℤ) :
    bprobBA (noisy p v) x y k = v * bprobBA p x y k + (1 - v) * bprobBA (unif d) x y k := by
  unfold bprobBA noisy
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> ring

/-- Mixing with uniform noise scales the CGLMP value by the visibility. -/
theorem cglmpOf_noisy [NeZero d] (p : Fin 2 → Fin 2 → Fin d → Fin d → ℝ) (v : ℝ) :
    cglmpOf (noisy p v) = v * cglmpOf p := by
  have h : cglmpOf (noisy p v) = v * cglmpOf p + (1 - v) * cglmpOf (unif d) := by
    unfold cglmpOf
    simp only [bprobAB_noisy, bprobBA_noisy]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [h, cglmpOf_unif]
  ring

/-- The noisy behaviour of a strategy violates the CGLMP inequality iff `2 < v * I_d(S)`: the CGLMP noise threshold
of `S` is `2 / I_d(S)`. -/
theorem noisy_violation_iff [NeZero d] (S : Strategy d D) (v : ℝ) :
    2 < cglmpOf (noisy S.prob v) ↔ 2 < v * S.cglmp := by
  rw [cglmpOf_noisy, cglmpOf_prob]

/-- **CGLMP noise threshold, `2 ≤ d ≤ 20`, no hypotheses**: every projective strategy on every maximally entangled
state needs visibility `v` with `2 < v * IME d` for its noisy behaviour to violate the CGLMP inequality. -/
theorem noisy_violation_imp_le_twenty [NeZero d] (h2 : 2 ≤ d) (h20 : d ≤ 20) (hD : 0 < D)
    (S : Strategy d D) {v : ℝ} (hv : 0 ≤ v) (h : 2 < cglmpOf (noisy S.prob v)) : 2 < v * IME d := by
  rw [noisy_violation_iff] at h
  have hopt : S.cglmp ≤ IME d := (maxEntClause_le_twenty d h2 h20).1.1 D hD S
  nlinarith [mul_le_mul_of_nonneg_left hopt hv]

/-- **CGLMP noise threshold, every `d ≥ 2`**, given `CONE_d` for `d ≥ 21` (the only hypothesis of the main theorem). -/
theorem noisy_violation_imp (hlarge : Hyp_ConeCertPos_large) [NeZero d] (h2 : 2 ≤ d) (hD : 0 < D)
    (S : Strategy d D) {v : ℝ} (hv : 0 ≤ v) (h : 2 < cglmpOf (noisy S.prob v)) : 2 < v * IME d := by
  rw [noisy_violation_iff] at h
  have hopt : S.cglmp ≤ IME d := (maxEntClause_all hlarge d h2).1.1 D hD S
  nlinarith [mul_le_mul_of_nonneg_left hopt hv]

/-- DKZ violates the CGLMP inequality under noise exactly when `2 < v * IME d`. -/
theorem dkz_noisy_violation_iff [NeZero d] (h2 : 2 ≤ d) (v : ℝ) :
    2 < cglmpOf (noisy (dkz d).prob v) ↔ 2 < v * IME d := by
  rw [noisy_violation_iff, dkz_cglmp h2]

/-- Equality of thresholds forces DKZ (rigidity), `2 ≤ d ≤ 20`, no hypotheses: a strategy with `I_d(S) = IME d`
(equivalently, CGLMP noise threshold `2 / IME d`) is DKZ tensored with an inert identity, up to `u ⊗ ū`. -/
theorem noisy_threshold_rigid_le_twenty [NeZero d] (h2 : 2 ≤ d) (h20 : d ≤ 20) (hD : 0 < D)
    (S : Strategy d D) (h : S.cglmp = IME d) : S.IsDKZTensorId :=
  (maxEntClause_le_twenty d h2 h20).1.2 D hD S h

/-- Equality of thresholds forces DKZ (rigidity), every `d ≥ 2`, given `CONE_d` for `d ≥ 21`. -/
theorem noisy_threshold_rigid (hlarge : Hyp_ConeCertPos_large) [NeZero d] (h2 : 2 ≤ d) (hD : 0 < D)
    (S : Strategy d D) (h : S.cglmp = IME d) : S.IsDKZTensorId :=
  (maxEntClause_all hlarge d h2).1.2 D hD S h

end OQP27
