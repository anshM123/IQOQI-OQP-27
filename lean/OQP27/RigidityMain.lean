import OQP27.RigidityDKZ
import OQP27.RigidityResidue

/-!
# OQP 27B rigidity for every `d`: the chain from named hypotheses (module L6)

Paper: `iqoqi/programs/oqp27B_all/Q_rig/RIGIDITY_ALLD.md` (Theorem R, sections 2-6).
Target statement: `OQP27.RigidityStatement d` of module L1 (`OQP27/Statement.lean`): every projective
strategy on `Φ_D` attaining `I_ME(d)` has `d ∣ D` and is DKZ ⊗ 1 up to a local unitary `u ⊗ ū`.

Proved here:
* `OQP27.Rig.rigidity_clause`: if the 27B configuration of a strategy (module L2's `toQConfig`)
  commutes and the strategy attains `I_ME(d)`, the strategy is DKZ ⊗ 1 up to local unitary
  (`RIGIDITY_ALLD.md` s.6), given `OQP27.Rig.Hyp_ClassicalTheoremB d`.
* `OQP27.Rig.hyp_reductionRig`: hence the hypothesis `OQP27.Hyp_ReductionRig d` of module L1's skeleton
  holds, given only `Hyp_ClassicalTheoremB d` (the reduction itself is module L2's, proved).
* `OQP27.Rig.hyp_cellEquality_of_ae`: the hypothesis `OQP27.Hyp_CellEquality d` of the skeleton (a tight
  cell inequality with all cells positive forces all `Q_x` to commute) follows from the equality analysis
  of the continuum theorem, `OQP27.Rig.Hyp_CellEqualityAE d` (equality in the cell inequality implies
  `[B(θ), g(θ)] = 0` for almost every `θ`), by the residue lemma (`OQP27.commute_of_ae_commute`,
  `RIGIDITY_ALLD.md` s.4, proved).
* `OQP27.Rig.rigidity_all_d`: **Theorem R** (`RigidityStatement d` for `d ≥ 2`) from
  `Hyp_CellInequalities d`, `Hyp_CellEqualityAE d`, `ConeCertPos d` and `Hyp_ClassicalTheoremB d`.

Hypotheses remaining (all precise statements):
* `OQP27.Hyp_CellInequalities d` (module L1): QD2-L1, the cell-embedding inequalities `⟨u^ℓ, δ⟩ ≤ 0`
  (`QD2/LOG.md` s.4; continuum theorem Q-T1 for step fields, from the strip inequality `(*)`).
* `OQP27.Rig.Hyp_CellEqualityAE d`: `RIGIDITY_ALLD.md` s.2 (second half) and s.3 (the equality analysis of
  Q-T1, which uses the equality case of `(*)`, `Q_2bmv/PROOF.md` Theorem 2(d)).
* `OQP27.ConeCertPos d` (module L1/L4): CONE_d with a cell vector with all cells positive and positive
  weight (`RIGIDITY_ALLD.md` s.5; computer-assisted).
* `OQP27.Rig.Hyp_ClassicalTheoremB d`: Theorem B of `paper-classical-all-d` for one joint eigenvector
  (the discrete rearrangement inequality with its equality case; proved by hand in that paper).
-/

set_option linter.unusedSectionVars false

open Complex Matrix Finset MeasureTheory

namespace OQP27.Rig

variable {d : ℕ} [NeZero d]

/-! ## Step 5: the rigidity clause of the reduction -/

lemma submatrix_equiv_injective {α β : Type*} (e : α ≃ β) {X Y : Matrix β β ℂ}
    (h : X.submatrix e e = Y.submatrix e e) : X = Y := by
  ext i j
  have := congrFun (congrFun h (e.symm i)) (e.symm j)
  simpa using this

/-- **The rigidity clause** (`RIGIDITY_ALLD.md` s.6): if the projections of the 27B configuration of a
strategy commute and the strategy attains `I_ME(d)`, then it is DKZ ⊗ 1 up to a local unitary. -/
theorem rigidity_clause (hd : 2 ≤ d) (hB : Hyp_ClassicalTheoremB d) {D : ℕ} (hD : 0 < D)
    (S : Strategy d D)
    (hcomm : ∀ x y, (Red.toQConfig S).Q x * (Red.toQConfig S).Q y
      = (Red.toQConfig S).Q y * (Red.toQConfig S).Q x)
    (hS : S.cglmp = IME d) : S.IsDKZTensorId := by
  have hcomm' : ∀ x y, Red.redConfig S x * Red.redConfig S y
      = Red.redConfig S y * Red.redConfig S x := by
    intro x y
    have h := hcomm x y
    simp only [Red.toQConfig] at h
    rw [submatrix_mul_equiv, submatrix_mul_equiv] at h
    exact submatrix_equiv_injective _ h
  obtain ⟨K, hDK, u, hu1, hu2, hR⟩ := canonical_form hd hB hD S hcomm' hS
  exact isDKZTensorId_of_canonical S hDK u hu1 hu2 hR

/-- **`OQP27.Hyp_ReductionRig d` holds, given the classical Theorem B.** -/
theorem hyp_reductionRig (hd : 2 ≤ d) (hB : Hyp_ClassicalTheoremB d) : Hyp_ReductionRig d := by
  intro D hD S
  refine ⟨4 * D, by omega, Red.toQConfig S, ?_, fun hc hS => rigidity_clause hd hB hD S hc hS⟩
  have h1 := clock_value_eq_linear d (fun m => Red.Nnet d (Red.redConfig S) m)
  have e1 : ∑ m ∈ Ico 1 d, Red.cscd d m * Red.Nnet d (Red.redConfig S) m
      = ∑ m ∈ Ico 1 d, Red.Nnet d (Red.redConfig S) m / Real.sin (Real.pi * m / (2 * d)) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Red.cscd, Red.psi]
    ring
  have e2 : pairingIco d (coneV d) (Red.toQConfig S).delta
      = pairingIco d (coneV d) (fun m => Red.Nnet d (Red.redConfig S) m - m) := by
    unfold pairingIco
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Red.toQConfig_delta]
  rw [Red.cglmp_eq_csc_strategy hd hD S, e1, e2]
  exact h1

/-! ## Steps 2-3: the equality analysis and the residue lemma -/

/-- The cell lengths `ℓ_0, …, ℓ_{d-1}` of a cell vector given as a function `ℕ → ℝ` (module L4). -/
def ellFin (ell : ℕ → ℝ) : Fin d → ℝ := fun r => ell r

/-- The field `B_x = Q_{x+d}` of a configuration (`RIGIDITY_ALLD.md` 1.3). -/
def fieldB {M : ℕ} (C : QConfig d M) : ZMod (4 * d) → Matrix (Fin M) (Fin M) ℂ :=
  fun x => C.Q (x + d)

/-- **Hypothesis: the equality analysis of the continuum theorem** (`RIGIDITY_ALLD.md` s.2, last
paragraph, and s.3, eqs. (2.1) and (3.6)). Let `ℓ` be a cell vector with all cells positive and let the
cell inequality of `ℓ` be tight for a 27B configuration on `ℂ^M`, `⟨u^ℓ, δ⟩ = 0`. Embed the
configuration in the circle with the cells of `ℓ` (`θ = 2πξ/N`, endpoints `t_x = 2π L_x/N`); then the step
field `B(θ) = B_x = Q_{x+d}` on `[t_x, t_{x+1})` commutes with its conjugate function
`g(θ) = (1/π) ∑_j (B_j - B_{j-1}) log|sin((θ - t_j)/2)|` for almost every `θ ∈ (0, 2π)`.
Paper proof: equality in every rotated cell inequality (identity (1.4) and (1.3), s.2), then equality in
the strip inequality `(*)` at `λ* = log 2/(2π)` for almost every `θ` (s.3.7), then the equality case of
`(*)` (`Q_2bmv/PROOF.md` Theorem 2(d)). -/
def Hyp_CellEqualityAE (d : ℕ) [NeZero d] : Prop :=
  ∀ M : ℕ, 0 < M → ∀ C : QConfig d M, ∀ ell : ℕ → ℝ, IsPosConeCell d ell →
    pairingIco d (cellDirection d ell) C.delta = 0 →
    ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (2 * Real.pi))),
      stepField (ellFin ell) (fieldB C) θ * conjField (ellFin ell) (fieldB C) θ
        = conjField (ellFin ell) (fieldB C) θ * stepField (ellFin ell) (fieldB C) θ

/-- **Steps 2-3** (`RIGIDITY_ALLD.md` s.3-4): the equality analysis and the residue lemma give the
hypothesis `OQP27.Hyp_CellEquality d` of the skeleton. -/
theorem hyp_cellEquality_of_ae (h : Hyp_CellEqualityAE d) : Hyp_CellEquality d := by
  intro M hM C ell hell h0 x y
  have hae := h M hM C ell hell h0
  have hpos : ∀ r : Fin d, 0 < ellFin ell r := fun r => hell.2 r r.isLt
  have hsum : ∑ r : Fin d, ellFin ell r = d := by
    rw [show (∑ r : Fin d, ellFin ell r) = ∑ r ∈ range d, ell r from
      Fin.sum_univ_eq_sum_range (fun r => ell r) d]
    exact hell.1.2
  have hcomm := commute_of_ae_commute hpos hsum (fieldB C) hae
  have := hcomm (x - d) (y - d)
  simpa [fieldB, sub_add_cancel] using this

/-! ## Theorem R -/

/-- **Theorem R (rigidity, every `d ≥ 2`)** from the named hypotheses: the cell inequalities (QD2-L1),
the equality analysis of the continuum theorem, CONE_d with an all-positive cell vector, and the
classical Theorem B. -/
theorem rigidity_all_d (hd : 2 ≤ d) (hcell : Hyp_CellInequalities d)
    (hcellEq : Hyp_CellEqualityAE d) (hcone : ConeCertPos d) (hB : Hyp_ClassicalTheoremB d) :
    RigidityStatement d :=
  rigidity_of_cells hd hcell (hyp_cellEquality_of_ae hcellEq) hcone (hyp_reductionRig hd hB)

end OQP27.Rig
