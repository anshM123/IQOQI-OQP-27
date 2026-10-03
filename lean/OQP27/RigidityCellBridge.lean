import OQP27.RigidityFinal
import OQP27.CellFinal

/-!
# OQP 27B rigidity: the single cell inequalities from the strip inequality (module L6, link to module L5)

Module L5 (`OQP27/Cell*.lean`) proves Q-T1 for one cell-embedded step field, `OQP27.Cell.cellFamily_ineq`,
from the strip inequality `(*)` (module L1's `Hyp_StripInequality`) and the regularity of `h_{λ*}`
(`OQP27.Cell.Hyp_hStripRegular`: harmonic on the open strip, continuous on the closed strip, linear growth).
This file restates that result as this module's hypothesis (1.3) for cell vectors with all cells positive and
records the resulting form of Theorem R.

* `OQP27.Rig.cellIneqSinglePos_of_strip`: `Hyp_hStripRegular → Hyp_StripInequality → Hyp_CellIneqSinglePos d`.
* `OQP27.Rig.rigidity_of_strip_regular`: **Theorem R** from `Hyp_hStripRegular`, the strip inequality and its
  equality case, step (a) of `RIGIDITY_ALLD.md` s.3.7 (`Hyp_ContinuumTight d`), CONE_d with an all-positive
  cell vector, and the classical Theorem B.
-/

set_option linter.unusedSectionVars false

open Finset

namespace OQP27.Rig

variable {d : ℕ} [NeZero d]

/-- **(1.3) for positive cells from `(*)`** (module L5's `cellFamily_ineq`, divided by `M`). -/
theorem cellIneqSinglePos_of_strip (hreg : Cell.Hyp_hStripRegular) (hs : Hyp_StripInequality) :
    Hyp_CellIneqSinglePos d := by
  intro M hM C ell hl
  obtain ⟨hharm, hcont, Cg, hCg, hgrowth⟩ := hreg
  have h := Cell.cellFamily_ineq hl (Cell.toCellFamily C) hharm hcont hCg hgrowth
    (Cell.hStrip_left Cell.lamStar) (Cell.hStrip_right Cell.lamStar)
    (Cell.starAt_of_hyp hs M Cell.lamStar)
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.2 hM
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  have e : cellFunctional ell C = (∑ x : ZMod (4 * d), ∑ y : ZMod (4 * d),
      cellPairKernel d ell x.val y.val * (C.Q x * C.Q (y + d)).trace.re) / M := by
    unfold cellFunctional pairTerm
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  have hw : windowValue d = (4 * d) ^ 2 * clausen2 (Real.pi / 2) / Real.pi ^ 2 := by
    unfold windowValue coneG
    rw [show 2 * Real.pi * (d : ℝ) / (4 * (d : ℝ)) = Real.pi / 2 by field_simp; ring]
    field_simp
  rw [e, hw, div_le_iff₀ hMpos]
  calc (∑ x : ZMod (4 * d), ∑ y : ZMod (4 * d),
        cellPairKernel d ell x.val y.val * (C.Q x * C.Q (y + d)).trace.re)
      ≤ (4 * d) ^ 2 * M * clausen2 (Real.pi / 2) / Real.pi ^ 2 := h
    _ = (4 * d) ^ 2 * clausen2 (Real.pi / 2) / Real.pi ^ 2 * M := by ring

/-- **Theorem R (every `d ≥ 2`)** from the regularity of `h_{λ*}`, the strip inequality `(*)` and its equality
case, step (a) of `RIGIDITY_ALLD.md` s.3.7, CONE_d with an all-positive cell vector, and the classical
Theorem B (the cell inequalities QD2-L1 are module L5's `continuumCell_of_regular`). -/
theorem rigidity_of_strip_regular (hd : 2 ≤ d) (hreg : Cell.Hyp_hStripRegular)
    (hs : Hyp_StripInequality) (hse : Hyp_StripEquality) (htight : Hyp_ContinuumTight d)
    (hcone : ConeCertPos d) (hB : Hyp_ClassicalTheoremB d) : RigidityStatement d :=
  rigidity_of_strip_tight hd (Cell.continuumCell_of_regular d hreg hs)
    (cellIneqSinglePos_of_strip hreg hs) htight hse hcone hB

/-- **Theorem R for `d = 2`** from the regularity of `h_{λ*}`, `(*)` with its equality case, and step (a). -/
theorem rigidity_two_of_strip (hreg : Cell.Hyp_hStripRegular) (hs : Hyp_StripInequality)
    (hse : Hyp_StripEquality) (htight : Hyp_ContinuumTight 2) : RigidityStatement 2 :=
  rigidity_of_strip_regular le_rfl hreg hs hse htight coneCertPos_2 classicalTheoremB_two

end OQP27.Rig
