import OQP27.RigidityWindow

/-!
# OQP 27B rigidity: the continuum equality analysis through the strip inequality (module L6)

Paper: `iqoqi/programs/oqp27B_all/Q_rig/RIGIDITY_ALLD.md`, section 3.7, and
`iqoqi/programs/oqp27B_all/Q_2bmv/PROOF.md`, Theorem 2 (equality case of the strip inequality `(*)`).

Section 3.7 of the paper has two steps: (a) a tight cell inequality `Q^ℓ(Q) = N² Φ_c(1/4,1/4)` makes the
pointwise strip inequality `(*)` tight at `λ* = log 2/(2π)` for the pair `(B(θ), g(θ))` (step field and its
conjugate function) for almost every `θ`, because the integrated slack vanishes and the integrand is
nonnegative; (b) the equality case of `(*)` gives `[B(θ), g(θ)] = 0`. Step (a) is stated as the hypothesis
`OQP27.Rig.Hyp_ContinuumTight d`; step (b) is module L1's `OQP27.Hyp_StripEquality`.

Proved here (no further hypotheses):
* `OQP27.Rig.stepField_isProjection`: for `θ ∈ (0, 2π)` the step field is one of the projections `B_x`
  (the cells cover the circle);
* `OQP27.Rig.conjField_isHermitian`: the conjugate function is Hermitian;
* `OQP27.Rig.continuumEquality_of_tight`: `Hyp_ContinuumTight d` and `Hyp_StripEquality` give
  `Hyp_ContinuumEquality d`;
* `OQP27.Rig.rigidity_of_strip_tight`: **Theorem R** from the cell inequalities (QD2-L1), (1.3) for positive
  cells, (a), the equality case of `(*)`, CONE_d with an all-positive cell vector, and the classical Theorem B;
* `OQP27.Rig.continuumCell_of_single`, `OQP27.Rig.continuumCellEq_of_tight`: the skeleton hypotheses
  `OQP27.Hyp_ContinuumCell d` and `OQP27.Hyp_ContinuumCellEq d` of module L1 follow from the statements
  "(*) implies (1.3)" and "(*) implies (a)";
* `OQP27.Rig.maxEntClause_of_strip_tight`: the max-ent clause (optimality and rigidity) from `(*)`, its
  equality case, the continuum statements, CONE_d with a positive cell vector, and the classical Theorem B.
-/

set_option linter.unusedSectionVars false

open Complex Matrix Finset MeasureTheory

namespace OQP27.Rig

variable {d : ℕ} [NeZero d]

/-! ## The step field is a projection, the conjugate function is Hermitian -/

section Fields

variable {M : ℕ}

/-- Every `θ ∈ [0, 2π)` lies in one cell `[t_x, t_{x+1})`. -/
lemma exists_cell {ell : Fin d → ℝ} (hsum : ∑ r, ell r = d) {θ : ℝ}
    (h0 : 0 ≤ θ) (h1 : θ < 2 * Real.pi) :
    ∃ x : ℕ, x < 4 * d ∧ θ ∈ Set.Ico (cellT ell x) (cellT ell (x + 1)) := by
  have hex : ∃ n : ℕ, θ < cellT ell (n + 1) := by
    refine ⟨4 * d - 1, ?_⟩
    rw [show 4 * d - 1 + 1 = 4 * d by have := NeZero.pos d; omega, cellT_N hsum]
    exact h1
  classical
  set x := Nat.find hex with hx
  have hxlt : θ < cellT ell (x + 1) := Nat.find_spec hex
  refine ⟨x, ?_, ?_, hxlt⟩
  · by_contra hcon
    have hle : x ≥ 4 * d := by omega
    have hmin := Nat.find_min' hex (show θ < cellT ell (4 * d - 1 + 1) by
      rw [show 4 * d - 1 + 1 = 4 * d by have := NeZero.pos d; omega, cellT_N hsum]; exact h1)
    have := NeZero.pos d
    omega
  · rcases Nat.eq_zero_or_pos x with hx0 | hx0
    · rw [hx0, cellT_zero]; exact h0
    · have hmin := Nat.find_min hex (show x - 1 < x by omega)
      push Not at hmin
      rw [show x - 1 + 1 = x by omega] at hmin
      exact hmin

lemma stepField_eq_of_mem_Ico {ell : Fin d → ℝ} (hpos : ∀ r, 0 < ell r)
    (B : ZMod (4 * d) → Matrix (Fin M) (Fin M) ℂ) (x : ZMod (4 * d)) {θ : ℝ}
    (hθ : θ ∈ Set.Ico (cellT ell x.val) (cellT ell (x.val + 1))) : stepField ell B θ = B x := by
  have hmono := cellT_strictMono hpos
  unfold stepField
  rw [Finset.sum_eq_single x]
  · exact Set.indicator_of_mem hθ _
  · intro y _ hyx
    apply Set.indicator_of_notMem
    intro hy
    apply hyx
    apply ZMod.val_injective
    have h1 : y.val < x.val + 1 := hmono.lt_iff_lt.1 (lt_of_le_of_lt hy.1 hθ.2)
    have h2 : x.val < y.val + 1 := hmono.lt_iff_lt.1 (lt_of_le_of_lt hθ.1 hy.2)
    omega
  · intro h; exact absurd (Finset.mem_univ x) h

/-- For `θ ∈ (0, 2π)` the step field is one of the `B_x`; in particular a projection. -/
lemma stepField_isProjection {ell : Fin d → ℝ} (hpos : ∀ r, 0 < ell r) (hsum : ∑ r, ell r = d)
    (B : ZMod (4 * d) → Matrix (Fin M) (Fin M) ℂ) (hB : ∀ x, IsProjection (B x)) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (2 * Real.pi)) : IsProjection (stepField ell B θ) := by
  obtain ⟨x, hx, hmem⟩ := exists_cell hsum hθ.1.le hθ.2
  have hxv : ((x : ZMod (4 * d))).val = x := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hx]
  rw [stepField_eq_of_mem_Ico hpos B (x : ZMod (4 * d)) (by rw [hxv]; exact hmem)]
  exact hB _

/-- The conjugate function of a field of Hermitian matrices is Hermitian. -/
lemma conjField_isHermitian (ell : Fin d → ℝ) (B : ZMod (4 * d) → Matrix (Fin M) (Fin M) ℂ)
    (hB : ∀ x, (B x).IsHermitian) (θ : ℝ) : (conjField ell B θ).IsHermitian := by
  unfold conjField Matrix.IsHermitian
  rw [conjTranspose_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : (B j - B (j - 1))ᴴ = B j - B (j - 1) := ((hB j).sub (hB (j - 1))).eq
  rw [conjTranspose_smul, hj, Complex.star_def, Complex.conj_ofReal]

end Fields

/-! ## The continuum equality analysis -/

/-- `λ* = log 2/(2π)`, the minimiser of `λ ↦ λ/4 + h_λ(1/4)` (`RIGIDITY_ALLD.md` 3.6). -/
noncomputable def lamStar : ℝ := Real.log 2 / (2 * Real.pi)

/-- **Hypothesis (step (a) of `RIGIDITY_ALLD.md` s.3.7)**: if the cell inequality (1.3) of a cell vector
with all cells positive is an equality, `Q^ℓ(Q) = N² Φ_c(1/4, 1/4)`, then the strip inequality `(*)` is an
equality at `λ* = log 2/(2π)` for the pair `(B(θ), g(θ))` (step field `B(θ) = Q_{x+d}` on the cells and its
conjugate function) for almost every `θ ∈ (0, 2π)`:
`∑_{ν ∈ spec(B(θ) + i g(θ))} h_{λ*}(ν) = Tr[(P(θ)(g(θ) - λ*)P(θ))_+]`, `P = 1 - B`.
Paper proof: the chain (3.4)-(3.5) is tight at `λ*`, and the integrand of the second inequality is
nonnegative at every `θ` off the cell endpoints. -/
def Hyp_ContinuumTight (d : ℕ) [NeZero d] : Prop :=
  ∀ M : ℕ, 0 < M → ∀ C : QConfig d M, ∀ ell : ℕ → ℝ, IsPosConeCell d ell →
    cellFunctional ell C = windowValue d →
    ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (2 * Real.pi))),
      stripSum lamStar (stepField (ellFin ell) (fieldB C) θ) (conjField (ellFin ell) (fieldB C) θ)
        = posPartTrace ((1 - stepField (ellFin ell) (fieldB C) θ) *
            (conjField (ellFin ell) (fieldB C) θ - (lamStar : ℂ) • 1) *
            (1 - stepField (ellFin ell) (fieldB C) θ))

/-- **Step (b) of `RIGIDITY_ALLD.md` s.3.7**: with the equality case of the strip inequality, almost-everywhere
tightness of `(*)` gives `[B(θ), g(θ)] = 0` almost everywhere. -/
theorem continuumEquality_of_tight (htight : Hyp_ContinuumTight d) (hstripEq : Hyp_StripEquality) :
    Hyp_ContinuumEquality d := by
  intro M hM C ell hell hQ
  have hpos : ∀ r : Fin d, 0 < ellFin ell r := fun r => hell.2 r r.isLt
  have hsum : ∑ r : Fin d, ellFin ell r = d := by
    rw [show (∑ r : Fin d, ellFin ell r) = ∑ r ∈ range d, ell r from
      Fin.sum_univ_eq_sum_range (fun r => ell r) d]
    exact hell.1.2
  filter_upwards [htight M hM C ell hell hQ, ae_restrict_mem measurableSet_Ioo] with θ h hθ
  exact hstripEq M _ _ (stepField_isProjection hpos hsum (fieldB C) (fun x => C.isProj _) hθ)
    (conjField_isHermitian _ _ (fun x => (C.isProj _).1) θ) lamStar h

/-- **Theorem R (rigidity, every `d ≥ 2`)** from: the cell inequalities (QD2-L1), the single cell
inequalities (1.3) for positive cells (Q-T1 for step fields), the tightness of `(*)` almost everywhere under
equality (step (a) of s.3.7), the equality case of the strip inequality, CONE_d with an all-positive cell
vector, and the classical Theorem B. -/
theorem rigidity_of_strip_tight (hd : 2 ≤ d) (hcell : Hyp_CellInequalities d)
    (h1 : Hyp_CellIneqSinglePos d) (htight : Hyp_ContinuumTight d) (hstripEq : Hyp_StripEquality)
    (hcone : ConeCertPos d) (hB : Hyp_ClassicalTheoremB d) : RigidityStatement d :=
  rigidity_all_d'' hd hcell h1 (continuumEquality_of_tight htight hstripEq) hcone hB

/-! ## The skeleton hypotheses of module L1 -/

/-- `OQP27.Hyp_ContinuumCell d` from the statement "(*) implies (1.3)". -/
theorem continuumCell_of_single (h : Hyp_StripInequality → Hyp_CellIneqSingle d) :
    Hyp_ContinuumCell d :=
  fun hs => cellInequalities_of_single (h hs)

/-- `OQP27.Hyp_ContinuumCellEq d` from the statements "(*) implies (1.3) for positive cells" and
"(*) implies step (a)". -/
theorem continuumCellEq_of_tight (h1 : Hyp_StripInequality → Hyp_CellIneqSinglePos d)
    (h2 : Hyp_StripInequality → Hyp_ContinuumTight d) : Hyp_ContinuumCellEq d :=
  fun hs hse => hyp_cellEquality_of_ae
    (cellEqualityAE_of_continuum (h1 hs) (continuumEquality_of_tight (h2 hs) hse))

/-- **The max-ent clause of OQP 27B for `d` outcomes** (optimality and rigidity), from the strip inequality
`(*)` and its equality case, the continuum theorem in the forms "(*) implies QD2-L1" (module L1's
`Hyp_ContinuumCell d`), "(*) implies (1.3) for positive cells" and "(*) implies step (a) of s.3.7",
CONE_d with an all-positive cell vector, and the classical Theorem B; the reduction is module L2's and the
rigidity clause and the residue lemma are proved in this module. -/
theorem maxEntClause_of_strip_tight (hd : 2 ≤ d) (hstrip : Hyp_StripInequality)
    (hstripEq : Hyp_StripEquality) (hcont : Hyp_ContinuumCell d)
    (h1 : Hyp_StripInequality → Hyp_CellIneqSinglePos d)
    (htight : Hyp_StripInequality → Hyp_ContinuumTight d) (hcone : ConeCertPos d)
    (hB : Hyp_ClassicalTheoremB d) : MaxEntClause d :=
  maxEntClause_of_strip hd hstrip hstripEq hcont (continuumCellEq_of_tight h1 htight) hcone
    (hyp_reductionRig hd hB)

end OQP27.Rig
