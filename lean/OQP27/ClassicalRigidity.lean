import OQP27.ClassicalTheoremB
import OQP27.RigidityTight

/-!
# The rigidity chain with the classical Theorem B discharged (module L7)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

Module L6 (`OQP27/Rigidity*.lean`) proves Theorem R and the max-ent clause from named hypotheses, one of
which is the classical Theorem B, `OQP27.Rig.Hyp_ClassicalTheoremB d`.  It is proved for every `d ≥ 1` in
`OQP27/ClassicalTheoremB.lean` (`OQP27.ClassB.classicalTheoremB`).  This file restates module L6's
theorems without that hypothesis:
* `clockF_le_commuting`: **Theorem B of the paper (commutative sector), every `d ≥ 1`**: for a 27B
  configuration of pairwise commuting projections (equivalently, commuting reduced family `V_k`),
  `F(V) ≤ F_DKZ` (module L6's `clockF_le`);
* `jp_eq_zero_commuting`, `commuting_optimal_relations'`: its equality case (module L6's `jp_eq_zero`,
  `commuting_optimal_relations`): if `F(V) = F_DKZ`, every joint spectral projection of a non-one-step
  configuration vanishes, and the reduced family satisfies the relations of `RIGIDITY.md` Lemma 7.2;
* `hyp_reductionRig_all`: module L1's `Hyp_ReductionRig d` for every `d ≥ 2`, unconditionally;
* `theoremR_of_strip_cone`: Theorem R from `(*)`, its equality case and `ConeCertPos d`;
* `theoremR_le_twenty_of_strip'`: Theorem R for `2 ≤ d ≤ 20` from `(*)` and its equality case;
* `theoremR_every_d_of_strip'`: Theorem R for every `d ≥ 2` from `(*)`, its equality case and module L4's
  `Hyp_ConeCertPos_large`;
* `maxEntClause_of_strip_cone`: the max-ent clause from `(*)`, its equality case and `ConeCertPos d`.
No new hypotheses.
-/

set_option autoImplicit false

namespace OQP27.ClassB

/-! ## Consequences for the rigidity chain (module L6), with Theorem B discharged -/

section Commuting

attribute [local instance] Rig.cAlgCommRing

variable {d : ℕ} [NeZero d] {ι : Type*} [Fintype ι] [DecidableEq ι] {Q : ZMod (4 * d) → Matrix ι ι ℂ}

/-- **Theorem B (commutative sector), every `d ≥ 1`**: for a 27B configuration of pairwise commuting
projections, `F(V) ≤ F_DKZ` for the reduced family `V`. -/
theorem clockF_le_commuting [Fact (∀ x, (Q x).IsHermitian)] [Fact (∀ x y, Q x * Q y = Q y * Q x)]
    (hQ : Rig.IsConfig Q) (hM : 0 < Fintype.card ι) : Rig.clockF (Rig.redV Q) ≤ Rig.FDKZ d :=
  Rig.clockF_le (classicalTheoremB d (Nat.pos_of_ne_zero (NeZero.ne d))) hQ hM

/-- **Equality case of Theorem B**: if `F(V) = F_DKZ`, every joint spectral projection `Π_a` with `a` not
one-step vanishes. -/
theorem jp_eq_zero_commuting [Fact (∀ x, (Q x).IsHermitian)] [Fact (∀ x y, Q x * Q y = Q y * Q x)]
    (hQ : Rig.IsConfig Q) (hM : 0 < Fintype.card ι) (hF : Rig.clockF (Rig.redV Q) = Rig.FDKZ d)
    (a : Fin d → ZMod 4) (ha : ¬ Rig.IsOneStep a) : Rig.jp Q a = 0 :=
  Rig.jp_eq_zero (classicalTheoremB d (Nat.pos_of_ne_zero (NeZero.ne d))) hQ hM hF a ha

/-- **The relations of the equality case** (`RIGIDITY.md` Lemma 7.2) for an optimal commuting
configuration, every `d ≥ 1`. -/
theorem commuting_optimal_relations' (hQ : Rig.IsConfig Q) (hcomm : ∀ x y, Q x * Q y = Q y * Q x)
    (hF : Rig.clockF (Rig.redV Q) = Rig.FDKZ d) :
    (∀ j k, Rig.redV Q j * Rig.redV Q k = Rig.redV Q k * Rig.redV Q j) ∧
    ∀ n : ℕ, 1 ≤ n → n ≤ d → ∀ k : Fin d,
      (Rig.relY (Rig.redV Q) n k - 1) * (Rig.relY (Rig.redV Q) n k - Complex.I • 1) = 0 :=
  Rig.commuting_optimal_relations (classicalTheoremB d (Nat.pos_of_ne_zero (NeZero.ne d))) hQ hcomm hF

end Commuting

/-- Module L1's `Hyp_ReductionRig d` for every `d ≥ 2` (module L6's `hyp_reductionRig` with Theorem B). -/
theorem hyp_reductionRig_all {d : ℕ} [NeZero d] (hd : 2 ≤ d) : Hyp_ReductionRig d :=
  Rig.hyp_reductionRig hd (classicalTheoremB d (by omega))

/-- **Theorem R (every `d ≥ 2`)** from the strip inequality `(*)`, its equality case and CONE_d with an
all-positive cell vector (module L6's `theoremR_of_strip`, Theorem B discharged). -/
theorem theoremR_of_strip_cone {d : ℕ} [NeZero d] (hd : 2 ≤ d) (hs : Hyp_StripInequality)
    (hse : Hyp_StripEquality) (hcone : ConeCertPos d) : RigidityStatement d :=
  Rig.theoremR_of_strip hd hs hse hcone (classicalTheoremB d (by omega))

/-- **Theorem R for `2 ≤ d ≤ 20`** from `(*)` and its equality case only. -/
theorem theoremR_le_twenty_of_strip' {d : ℕ} [NeZero d] (hd2 : 2 ≤ d) (hd20 : d ≤ 20)
    (hs : Hyp_StripInequality) (hse : Hyp_StripEquality) : RigidityStatement d :=
  Rig.theoremR_le_twenty_of_strip hd2 hd20 hs hse (classicalTheoremB d (by omega))

/-- **Theorem R for every `d ≥ 2`** from `(*)`, its equality case and module L4's
`Hyp_ConeCertPos_large`. -/
theorem theoremR_every_d_of_strip' (hlarge : Hyp_ConeCertPos_large) (hs : Hyp_StripInequality)
    (hse : Hyp_StripEquality) (d : ℕ) [NeZero d] (hd : 2 ≤ d) : RigidityStatement d :=
  Rig.theoremR_every_d_of_strip hlarge hs hse (fun d _ hd => classicalTheoremB d (by omega)) d hd

/-- **The max-ent clause of OQP 27B** (optimality and rigidity) from `(*)`, its equality case and CONE_d
with an all-positive cell vector. -/
theorem maxEntClause_of_strip_cone {d : ℕ} [NeZero d] (hd : 2 ≤ d) (hs : Hyp_StripInequality)
    (hse : Hyp_StripEquality) (hcone : ConeCertPos d) : MaxEntClause d :=
  Rig.maxEntClause_of_strip_thmB hd hs hse hcone (classicalTheoremB d (by omega))

end OQP27.ClassB
