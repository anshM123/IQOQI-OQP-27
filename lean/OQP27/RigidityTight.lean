import OQP27.RigidityCellBridge
import OQP27.CellStripFn

/-!
# OQP 27B rigidity, Step 2: the equality analysis of the continuum theorem (module L6)

Paper: `iqoqi/programs/oqp27B_all/Q_rig/RIGIDITY_ALLD.md`, section 3.7 (step (a)).

Module L5 proves Q-T1 for step fields (`OQP27.Cell.stepField_ineq`): on each open arc `J_x` of the cell
partition the integrand `L_x(θ) = Re Tr(A_x (g(θ) - λ))` is bounded by
`Tr[(P(g(θ) - λ)P)_+] ≤ ∑_{ν ∈ spec(B_x + i g(θ))} h_λ(ν) = u*(θ)`, and `∫ u* = 2π M h_λ(1/4)` (mean value
identity).  This file proves the equality case: if `Q^ℓ(Q) = N² Φ_c(1/4,1/4)` then the integrated slack
vanishes, so the nonnegative integrand `u* - L_x` vanishes almost everywhere on every arc, and the strip
inequality `(*)` is an equality at `λ* = log 2/(2π)` for `(B(θ), g(θ))` for almost every `θ`.

All proofs are complete; the regularity of `h_{λ*}` is module L5's `OQP27.Cell.hStrip_regular` (proved).

* `OQP27.Rig.conjField_eq_gconj`: the conjugate function (3.1) of this module equals module L5's `gconj`
  on the open arcs (summation by parts; `log|2 sin| = log 2 + log|sin|`).
* `OQP27.Rig.pointwise_first`: the first half of the pointwise inequality (3.4),
  `Re Tr(A g) - λ Re Tr A ≤ Tr[(P(g - λ)P)_+]` for orthogonal projections `A ⟂ B`, `P = 1 - B`.
* `OQP27.Rig.continuumTight_of_strip`: `Hyp_StripInequality → Hyp_ContinuumTight d` (step (a) of s.3.7).
  (Module L5's `OQP27.Cell.continuumTight_of_strip` in `OQP27/CellRigidity.lean` is an independent proof of
  the same statement.)
* `OQP27.Rig.hyp_continuumEquality`, `hyp_cellEqualityAE`: this module's `Hyp_ContinuumEquality d` and
  `Hyp_CellEqualityAE d` (equality in the cell inequality forces `[B(θ), g(θ)] = 0` a.e.) from `(*)` and its
  equality case.
* `OQP27.Rig.hyp_continuumCellEq`: module L1's `Hyp_ContinuumCellEq d`, unconditionally.
* `OQP27.Rig.theoremR_of_strip`: **Theorem R** (`RigidityStatement d`, every `d ≥ 2`) from the strip
  inequality `(*)` and its equality case, CONE_d with an all-positive cell vector, and the classical
  Theorem B; `maxEntClause_of_strip_thmB`: the max-ent clause (optimality and rigidity) from the same.
* `OQP27.Rig.theoremR_two_of_strip` (`d = 2`, from `(*)` and its equality case only),
  `theoremR_le_twenty_of_strip` (`2 ≤ d ≤ 20`, plus Theorem B), `theoremR_every_d_of_strip` (every `d ≥ 2`,
  plus Theorem B and module L4's `Hyp_ConeCertPos_large`).
-/

set_option linter.unusedSectionVars false

open Complex Matrix Finset MeasureTheory Set Filter

namespace OQP27.Rig

variable {d : ℕ} [NeZero d]

/-! ## Comparison with module L5's conjugate function -/

section Compare

variable {ell : ℕ → ℝ}

lemma lamStar_eq_cell : lamStar = Cell.lamStar := rfl

lemma cellT_eq_partition (hl : IsPosConeCell d ell) (n : ℕ) :
    cellT (ellFin (d := d) ell) n = (Cell.cellPartition hl).t n := by
  rw [Cell.cellPartition_t hl]
  rfl

lemma cell_ell_eq_log {u : ℝ} (hu : Real.sin (u / 2) ≠ 0) :
    Cell.ell u = Real.log 2 + Real.log |Real.sin (u / 2)| := by
  unfold Cell.ell
  rw [Real.log_mul two_ne_zero hu, Real.log_abs]

lemma cell_ell_sub_two_pi (θ : ℝ) : Cell.ell (θ - 2 * Real.pi) = Cell.ell θ := by
  unfold Cell.ell
  rw [show (θ - 2 * Real.pi) / 2 = θ / 2 - Real.pi by ring, Real.sin_sub_pi, mul_neg,
    Real.log_neg_eq_log]

/-- Cyclic summation by parts on `ℤ_N`. -/
lemma cyclic_sum_by_parts {N : ℕ} [NeZero N] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : ℕ → ℂ) (hf : f N = f 0) (B : ZMod N → V) :
    ∑ y ∈ range N, (f y - f (y + 1)) • B (y : ZMod N)
      = ∑ y ∈ range N, f y • (B (y : ZMod N) - B ((y : ZMod N) - 1)) := by
  set h : ℕ → V := fun i => f i • B ((i : ZMod N) - 1) with hh
  have hshift : ∑ y ∈ range N, f (y + 1) • B (y : ZMod N) = ∑ y ∈ range N, h y := by
    have e1 : ∀ y, f (y + 1) • B (y : ZMod N) = h (y + 1) := by
      intro y
      simp only [hh]
      congr 2
      push_cast
      ring
    simp_rw [e1]
    have e2 := Finset.sum_range_succ' h N
    have e3 := Finset.sum_range_succ h N
    have hN : h N = h 0 := by
      simp only [hh, ZMod.natCast_self, Nat.cast_zero, hf]
    rw [e3, hN] at e2
    linear_combination (norm := skip) e2.symm
    abel
  rw [Finset.sum_congr rfl fun y _ => sub_smul (f y) (f (y + 1)) (B (y : ZMod N)),
    Finset.sum_sub_distrib, hshift]
  simp only [hh, smul_sub, Finset.sum_sub_distrib]

lemma sum_cyclic_diff {N : ℕ} [NeZero N] {V : Type*} [AddCommGroup V] (B : ZMod N → V) :
    ∑ y ∈ range N, (B (y : ZMod N) - B ((y : ZMod N) - 1)) = 0 := by
  rw [Finset.sum_sub_distrib, sub_eq_zero]
  rw [Cell.sum_range_eq_sum_zmod N (fun y => B y), Cell.sum_range_eq_sum_zmod N (fun y => B (y - 1))]
  exact (Fintype.sum_equiv (Equiv.subRight 1) _ _ (fun y => rfl)).symm

/-- **The conjugate function (3.1) is module L5's `gconj`** at every point of an open arc. -/
lemma conjField_eq_gconj (hl : IsPosConeCell d ell) {M : ℕ}
    (B : ZMod (4 * d) → Matrix (Fin M) (Fin M) ℂ) {θ : ℝ}
    (hθ : ∀ j : ℕ, j < 4 * d → Real.sin ((θ - (Cell.cellPartition hl).t j) / 2) ≠ 0) :
    conjField (ellFin ell) B θ
      = Cell.gconj (Cell.cellPartition hl) (fun y : ℕ => B (y : ZMod (4 * d))) θ := by
  set P := Cell.cellPartition hl with hP
  set f : ℕ → ℂ := fun y => ((Cell.ell (θ - P.t y) / Real.pi : ℝ) : ℂ) with hf
  have hfN : f (4 * d) = f 0 := by
    simp only [hf, P.t_last, P.t_zero, sub_zero, cell_ell_sub_two_pi]
  -- module L5's side
  have hg : Cell.gconj P (fun y : ℕ => B (y : ZMod (4 * d))) θ
      = ∑ y ∈ range (4 * d), (f y - f (y + 1)) • B (y : ZMod (4 * d)) := by
    unfold Cell.gconj Cell.gcoef
    refine Finset.sum_congr rfl fun y _ => ?_
    congr 1
    simp only [hf]
    push_cast
    ring
  rw [hg, cyclic_sum_by_parts f hfN B]
  -- this module's side, as a sum over `range N`
  unfold conjField
  rw [Red.sum_zmod_eq_sum_range]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hterm : ∀ y ∈ range (4 * d),
      f y • (B (y : ZMod (4 * d)) - B ((y : ZMod (4 * d)) - 1))
        = (((Real.log |Real.sin ((θ - cellT (ellFin (d := d) ell) ((y : ZMod (4 * d)).val)) / 2)| /
            Real.pi : ℝ)) : ℂ) • (B (y : ZMod (4 * d)) - B ((y : ZMod (4 * d)) - 1))
          + ((Real.log 2 / Real.pi : ℝ) : ℂ) • (B (y : ZMod (4 * d)) - B ((y : ZMod (4 * d)) - 1)) := by
    intro y hy
    have hy' := Finset.mem_range.1 hy
    rw [← add_smul]
    congr 1
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hy', cellT_eq_partition hl, hf]
    simp only
    rw [cell_ell_eq_log (hθ y hy')]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.smul_sum, sum_cyclic_diff,
    smul_zero, add_zero]

end Compare

/-! ## The equality analysis -/

section Tight

variable {M : ℕ}

/-- The first step of the pointwise inequality (3.4): `Re Tr(A g) - λ Re Tr A ≤ Tr[(P(g - λ)P)_+]`. -/
lemma pointwise_first {A B g : Matrix (Fin M) (Fin M) ℂ} (hA : Cell.IsProj A) (hB : Cell.IsProj B)
    (hAB : A * B = 0) (hg : g.IsHermitian) (lam : ℝ) :
    (A * g).trace.re - lam * (A.trace).re
      ≤ posPartTrace ((1 - B) * (g - (lam : ℂ) • 1) * (1 - B)) := by
  have hY : (g - (lam : ℂ) • 1).IsHermitian := by
    apply hg.sub
    rw [Matrix.IsHermitian, conjTranspose_smul, conjTranspose_one, Complex.star_def,
      Complex.conj_ofReal]
  have hX := Cell.isHermitian_compress hB hY
  have h1 : (A * g).trace.re - lam * (A.trace).re =
      (A * ((1 - B) * (g - (lam : ℂ) • 1) * (1 - B))).trace.re := by
    rw [Cell.trace_compress hA hB hAB, Matrix.mul_sub, trace_sub, Matrix.mul_smul, Matrix.mul_one,
      trace_smul, smul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  rw [h1]
  refine (Cell.re_trace_mul_le_posPart hA hX).trans (le_of_eq ?_)
  unfold posPartTrace
  rw [dif_pos hX]

/-- **Step (a) of `RIGIDITY_ALLD.md` s.3.7**: with the strip inequality `(*)`, a tight cell inequality
(1.3) with all cells positive makes `(*)` an equality at `λ*` for `(B(θ), g(θ))` for almost every `θ`. -/
theorem continuumTight_of_strip (hs : Hyp_StripInequality) : Hyp_ContinuumTight d := by
  intro M hM C ell hl hQ
  set N := 4 * d with hN
  set P := Cell.cellPartition hl with hP
  set A : ℕ → Matrix (Fin M) (Fin M) ℂ := fun x => C.Q (x : ZMod (4 * d)) with hAdef
  set Bn : ℕ → Matrix (Fin M) (Fin M) ℂ := fun x => C.Q ((x : ZMod (4 * d)) + d) with hBdef
  have hA : ∀ k, Cell.IsProj (A k) := fun k => C.isProj _
  have hB : ∀ k, Cell.IsProj (Bn k) := fun k => C.isProj _
  have hAB : ∀ k, A k * Bn k = 0 := fun k => Cell.qconfig_orth_d C _
  obtain ⟨hharm, hcont, Cg, hCg, hgrowth⟩ := Cell.hStrip_regular
  have hstar := Cell.starAt_of_hyp hs M Cell.lamStar
  have hop := Cell.cell_op_B hl (Cell.toCellFamily C)
  obtain ⟨hint, hval⟩ := Cell.mean_value_boundary P Bn hB (β := 1 / 4) (by norm_num) (by norm_num)
    hop hharm hcont hCg hgrowth
  set ustar : ℝ → ℝ := fun θ =>
    ((Cell.herg P Bn (Complex.exp ((θ : ℂ) * I))).charpoly.roots.map (hStrip Cell.lamStar)).sum
    with hustar
  set L : ℕ → ℝ → ℝ := fun x θ =>
    ∑ y ∈ Finset.range N, Cell.gcoef P y θ * (A x * Bn y).trace.re - Cell.lamStar * (A x).trace.re
    with hL
  set pp : ℕ → ℝ → ℝ := fun x θ =>
    posPartTrace ((1 - Bn x) * (Cell.gconj P Bn θ - (Cell.lamStar : ℂ) • 1) * (1 - Bn x)) with hpp
  -- the two pointwise inequalities on the open arcs
  have hpt : ∀ x < N, ∀ θ, P.t x < θ → θ < P.t (x + 1) → L x θ ≤ pp x θ ∧ pp x θ ≤ ustar θ := by
    intro x hx θ h1 h2
    have hg := Cell.isHermitian_gconj P Bn hB θ
    constructor
    · have h := pointwise_first (hA x) (hB x) (hAB x) hg Cell.lamStar
      rw [Cell.re_trace_mul_gconj] at h
      exact h
    · have h := hstar (Bn x) (Cell.gconj P Bn θ) (hB x) hg
      simp only [hustar]
      rw [Cell.herg_boundary_eq P Bn hx h1 h2]
      exact h
  -- integrability and the values of the arc integrals
  have hsub : ∀ k ≤ N, P.t k ∈ uIcc 0 (2 * Real.pi) := by
    intro k hk
    rw [Set.uIcc_of_le (by positivity)]
    exact ⟨P.t_nonneg hk, P.t_le_two_pi hk⟩
  have hU_int : ∀ x < N, IntervalIntegrable ustar volume (P.t x) (P.t (x + 1)) := fun x hx =>
    hint.mono_set (Set.uIcc_subset_uIcc (hsub x hx.le) (hsub (x + 1) hx))
  have hsplit : ∫ θ in (0 : ℝ)..2 * Real.pi, ustar θ =
      ∑ x ∈ Finset.range N, ∫ θ in P.t x..P.t (x + 1), ustar θ := by
    rw [intervalIntegral.sum_integral_adjacent_intervals, P.t_zero, P.t_last]
    intro k hk
    exact hU_int k hk
  have hL_int : ∀ x, IntervalIntegrable (L x) volume (P.t x) (P.t (x + 1)) := by
    intro x
    apply IntervalIntegrable.sub _ intervalIntegrable_const
    apply Cell.intervalIntegrable_fun_sum
    intro y _
    exact (Cell.intervalIntegrable_gcoef P y _ _).mul_const _
  have hL_val : ∀ x, ∫ θ in P.t x..P.t (x + 1), L x θ =
      (∑ y ∈ Finset.range N, Cell.arcKernel P x y * (A x * Bn y).trace.re) / Real.pi -
        Cell.lamStar * ((P.t (x + 1) - P.t x) * (A x).trace.re) := by
    intro x
    simp only [hL]
    rw [intervalIntegral.integral_sub _ intervalIntegrable_const,
      intervalIntegral.integral_finsetSum, intervalIntegral.integral_const, smul_eq_mul,
      Finset.sum_div]
    · congr 1
      · apply Finset.sum_congr rfl
        intro y _
        rw [intervalIntegral.integral_mul_const, Cell.integral_gcoef]
        ring
      · ring
    · intro y _
      exact (Cell.intervalIntegrable_gcoef P y _ _).mul_const _
    · apply Cell.intervalIntegrable_fun_sum
      intro y _
      exact (Cell.intervalIntegrable_gcoef P y _ _).mul_const _
  -- the global identity, from the tightness of the cell inequality
  have hMne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hdne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  have hconv : ∑ x ∈ Finset.range N, ∑ y ∈ Finset.range N,
      Cell.arcKernel P x y * (A x * Bn y).trace.re
        = 2 * Real.pi ^ 2 / (4 * d) ^ 2 * (M * cellFunctional ell C) := by
    have e1 : (M : ℝ) * cellFunctional ell C = ∑ x : ZMod N, ∑ y : ZMod N,
        cellPairKernel d ell x.val y.val * (C.Q x * C.Q (y + d)).trace.re := by
      unfold cellFunctional pairTerm
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      field_simp
    have hF : ∀ x ∈ Finset.range N, ∑ y ∈ Finset.range N,
        Cell.arcKernel P x y * (A x * Bn y).trace.re
          = 2 * Real.pi ^ 2 / (4 * d) ^ 2 * ∑ y : ZMod N, cellPairKernel d ell (x : ZMod N).val y.val *
              (C.Q (x : ZMod N) * C.Q (y + d)).trace.re := by
      intro x hx
      rw [Finset.mul_sum, ← Cell.sum_range_eq_sum_zmod N (fun y : ZMod N => 2 * Real.pi ^ 2 / (4 * d) ^ 2 *
        (cellPairKernel d ell (x : ZMod N).val y.val * (C.Q (x : ZMod N) * C.Q (y + d)).trace.re))]
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [Cell.arcKernel_cellPartition hl, ZMod.val_natCast, ZMod.val_natCast,
        Nat.mod_eq_of_lt (Finset.mem_range.1 hx), Nat.mod_eq_of_lt (Finset.mem_range.1 hy)]
      ring
    rw [Finset.sum_congr rfl hF, ← Finset.mul_sum,
      Cell.sum_range_eq_sum_zmod N (fun x : ZMod N => ∑ y : ZMod N,
        cellPairKernel d ell x.val y.val * (C.Q x * C.Q (y + d)).trace.re), e1]
  have hW : windowValue d = (4 * d) ^ 2 * clausen2 (Real.pi / 2) / Real.pi ^ 2 := by
    unfold windowValue coneG
    rw [show 2 * Real.pi * (d : ℝ) / (4 * (d : ℝ)) = Real.pi / 2 by field_simp; ring]
    field_simp
  have hw := Cell.window_value hharm hcont hCg hgrowth (Cell.hStrip_left Cell.lamStar)
    (Cell.hStrip_right Cell.lamStar)
  have htrA : ∑ x ∈ Finset.range N, (P.t (x + 1) - P.t x) * (A x).trace.re = Real.pi / 2 * M :=
    Cell.cell_trace_A hl (Cell.toCellFamily C)
  have htotal : ∑ x ∈ Finset.range N, ∫ θ in P.t x..P.t (x + 1), L x θ
      = ∑ x ∈ Finset.range N, ∫ θ in P.t x..P.t (x + 1), ustar θ := by
    rw [← hsplit, hval, Finset.sum_congr rfl (fun x _ => hL_val x), Finset.sum_sub_distrib,
      ← Finset.sum_div, ← Finset.mul_sum, hconv, htrA, hQ, hW]
    have hh : hStrip Cell.lamStar ((1 / 4 : ℝ) : ℂ) = clausen2 (Real.pi / 2) / Real.pi ^ 2
        - Cell.lamStar / 4 := by linarith
    rw [hh]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  -- every arc slack vanishes
  have hle_int : ∀ x ∈ Finset.range N, ∫ θ in P.t x..P.t (x + 1), L x θ
      ≤ ∫ θ in P.t x..P.t (x + 1), ustar θ := by
    intro x hx
    have hx' := Finset.mem_range.1 hx
    apply intervalIntegral.integral_mono_on_of_le_Ioo (P.t_lt x hx').le (hL_int x) (hU_int x hx')
    intro θ hθ
    exact (hpt x hx' θ hθ.1 hθ.2).1.trans (hpt x hx' θ hθ.1 hθ.2).2
  have hzero : ∀ x ∈ Finset.range N, (∫ θ in P.t x..P.t (x + 1), ustar θ)
      - ∫ θ in P.t x..P.t (x + 1), L x θ = 0 := by
    have hsum0 : ∑ x ∈ Finset.range N, ((∫ θ in P.t x..P.t (x + 1), ustar θ)
        - ∫ θ in P.t x..P.t (x + 1), L x θ) = 0 := by
      rw [Finset.sum_sub_distrib, htotal, sub_self]
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun x hx => sub_nonneg.2 (hle_int x hx))).1 hsum0
  -- hence `(*)` is tight almost everywhere on every arc
  have hae_arc : ∀ x < N, ∀ᵐ θ ∂(volume.restrict (Set.Ioo (P.t x) (P.t (x + 1)))),
      pp x θ = ustar θ := by
    intro x hx
    have hab : P.t x ≤ P.t (x + 1) := (P.t_lt x hx).le
    have hfi : IntervalIntegrable (fun θ => ustar θ - L x θ) volume (P.t x) (P.t (x + 1)) :=
      (hU_int x hx).sub (hL_int x)
    have hrestrict : volume.restrict (Set.Ioc (P.t x) (P.t (x + 1)))
        = volume.restrict (Set.Ioo (P.t x) (P.t (x + 1))) :=
      (Measure.restrict_congr_set Ioo_ae_eq_Ioc).symm
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (P.t x) (P.t (x + 1)))] (fun θ => ustar θ - L x θ) := by
      rw [hrestrict]
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
      have h := hpt x hx θ hθ.1 hθ.2
      simp only [Pi.zero_apply]
      linarith [h.1, h.2]
    have h0 : ∫ θ in P.t x..P.t (x + 1), (ustar θ - L x θ) = 0 := by
      rw [intervalIntegral.integral_sub (hU_int x hx) (hL_int x)]
      exact hzero x (Finset.mem_range.2 hx)
    have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hab hnn hfi).1 h0
    rw [hrestrict] at hae
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with θ h1 hθ
    have h := hpt x hx θ hθ.1 hθ.2
    simp only [Pi.zero_apply] at h1
    linarith [h.1, h.2]
  -- assemble on `(0, 2π)`
  rw [ae_restrict_iff' measurableSet_Ioo]
  have hall : ∀ᵐ θ ∂(volume : Measure ℝ), ∀ x : Fin N,
      θ ∈ Set.Ioo (P.t x) (P.t (x + 1)) → pp x θ = ustar θ := by
    rw [ae_all_iff]
    intro x
    exact (ae_restrict_iff' measurableSet_Ioo).1 (hae_arc x x.isLt)
  have hends : ∀ᵐ θ ∂(volume : Measure ℝ), ∀ k : Fin (N + 1), θ ≠ P.t k := by
    rw [ae_all_iff]
    intro k
    exact compl_mem_ae_iff.2 (measure_singleton (P.t k))
  filter_upwards [hall, hends] with θ h1 h2 hθ
  have hpos : ∀ r : Fin d, 0 < ellFin ell r := fun r => hl.2 r r.isLt
  have hsum : ∑ r : Fin d, ellFin ell r = d := by
    rw [show (∑ r : Fin d, ellFin ell r) = ∑ r ∈ range d, ell r from
      Fin.sum_univ_eq_sum_range (fun r => ell r) d]
    exact hl.1.2
  obtain ⟨x, hx, hmem⟩ := exists_cell hsum hθ.1.le hθ.2
  rw [cellT_eq_partition hl, cellT_eq_partition hl] at hmem
  have hne : θ ≠ P.t x := h2 ⟨x, by omega⟩
  have hθx : θ ∈ Set.Ioo (P.t x) (P.t (x + 1)) := ⟨lt_of_le_of_ne hmem.1 (Ne.symm hne), hmem.2⟩
  have hppx := h1 ⟨x, hx⟩ hθx
  have hxv : ((x : ZMod (4 * d))).val = x := by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hx]
  have hstep : stepField (ellFin ell) (fieldB C) θ = Bn x := by
    rw [stepField_eq hpos (fieldB C) (x : ZMod (4 * d))
      (by rw [hxv, cellT_eq_partition hl, cellT_eq_partition hl]; exact hθx)]
    rfl
  have hsin : ∀ j : ℕ, j < 4 * d → Real.sin ((θ - P.t j) / 2) ≠ 0 := fun j hj =>
    P.sin_half_ne_zero hθ (by omega) (h2 ⟨j, by omega⟩)
  have hconj : conjField (ellFin ell) (fieldB C) θ = Cell.gconj P Bn θ := by
    rw [conjField_eq_gconj hl (fieldB C) hsin]
    rfl
  rw [hstep, hconj]
  have hu : stripSum lamStar (Bn x) (Cell.gconj P Bn θ) = ustar θ := by
    simp only [hustar, stripSum]
    rw [Cell.herg_boundary_eq P Bn hx hθx.1 hθx.2]
    rfl
  rw [hu, ← hppx]
  rfl

end Tight

/-! ## Theorem R from the strip inequality -/

section Final

/-- **Module L1's `Hyp_ContinuumCellEq d`** (`(*)` and its equality case imply the rigidity steps 1-3), from
module L5's (1.3) for positive cells and `continuumTight_of_strip`. -/
theorem hyp_continuumCellEq : Hyp_ContinuumCellEq d :=
  continuumCellEq_of_tight (fun hs => cellIneqSinglePos_of_strip Cell.hStrip_regular hs)
    (fun hs => continuumTight_of_strip hs)

/-- **`Hyp_ContinuumEquality d`** (s.3.7: a tight cell inequality with all cells positive forces
`[B(θ), g(θ)] = 0` for almost every `θ`) from `(*)` and its equality case. -/
theorem hyp_continuumEquality (hs : Hyp_StripInequality) (hse : Hyp_StripEquality) :
    Hyp_ContinuumEquality d :=
  continuumEquality_of_tight (continuumTight_of_strip hs) hse

/-- **`Hyp_CellEqualityAE d`** (s.2-3: `⟨u^ℓ, δ⟩ = 0` with all cells positive forces `[B(θ), g(θ)] = 0` for
almost every `θ`) from `(*)` and its equality case. -/
theorem hyp_cellEqualityAE (hs : Hyp_StripInequality) (hse : Hyp_StripEquality) :
    Hyp_CellEqualityAE d :=
  cellEqualityAE_of_continuum (cellIneqSinglePos_of_strip Cell.hStrip_regular hs)
    (hyp_continuumEquality hs hse)

/-- **Theorem R (every `d ≥ 2`)** from the strip inequality `(*)` and its equality case (module L1's
`Hyp_StripInequality`, `Hyp_StripEquality`), CONE_d with an all-positive cell vector (`ConeCertPos d`), and
the classical Theorem B (`Hyp_ClassicalTheoremB d`). -/
theorem theoremR_of_strip (hd : 2 ≤ d) (hs : Hyp_StripInequality) (hse : Hyp_StripEquality)
    (hcone : ConeCertPos d) (hB : Hyp_ClassicalTheoremB d) : RigidityStatement d :=
  rigidity_of_strip_regular hd Cell.hStrip_regular hs hse (continuumTight_of_strip hs) hcone hB

/-- **The max-ent clause of OQP 27B** (optimality and rigidity) from `(*)` and its equality case, CONE_d with an
all-positive cell vector, and the classical Theorem B. -/
theorem maxEntClause_of_strip_thmB (hd : 2 ≤ d) (hs : Hyp_StripInequality) (hse : Hyp_StripEquality)
    (hcone : ConeCertPos d) (hB : Hyp_ClassicalTheoremB d) : MaxEntClause d :=
  maxEntClause_of_strip_tight hd hs hse (Cell.continuumCell d)
    (fun hs' => cellIneqSinglePos_of_strip Cell.hStrip_regular hs')
    (fun hs' => continuumTight_of_strip hs') hcone hB

end Final

/-- **Theorem R for `d = 2`** from `(*)` and its equality case only (CONE_2: module L4's `coneCertPos_2`;
Theorem B for `d = 2`: `classicalTheoremB_two`). -/
theorem theoremR_two_of_strip (hs : Hyp_StripInequality) (hse : Hyp_StripEquality) :
    RigidityStatement 2 :=
  theoremR_of_strip le_rfl hs hse coneCertPos_2 classicalTheoremB_two

/-- **Theorem R for `2 ≤ d ≤ 20`** from `(*)`, its equality case, and the classical Theorem B (CONE_d with an
all-positive cell vector: module L4's `coneCertPos_le_twenty`). -/
theorem theoremR_le_twenty_of_strip {d : ℕ} [NeZero d] (hd2 : 2 ≤ d) (hd20 : d ≤ 20)
    (hs : Hyp_StripInequality) (hse : Hyp_StripEquality) (hB : Hyp_ClassicalTheoremB d) :
    RigidityStatement d :=
  theoremR_of_strip hd2 hs hse (coneCertPos_le_twenty d hd2 hd20) hB

/-- **Theorem R for every `d ≥ 2`** from `(*)`, its equality case, the classical Theorem B, and module L4's
`Hyp_ConeCertPos_large` (CONE_d with an all-positive cell vector for `d ≥ 21`). -/
theorem theoremR_every_d_of_strip (hlarge : Hyp_ConeCertPos_large) (hs : Hyp_StripInequality)
    (hse : Hyp_StripEquality) (hB : ∀ d [NeZero d], 2 ≤ d → Hyp_ClassicalTheoremB d)
    (d : ℕ) [NeZero d] (hd : 2 ≤ d) : RigidityStatement d :=
  theoremR_of_strip hd hs hse (coneCertPos_all hlarge d hd) (hB d hd)

end OQP27.Rig
