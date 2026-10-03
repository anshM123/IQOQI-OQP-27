/-
OQP27/CellRigidity.lean  (module L5: the continuum inputs of the rigidity chain)

Module L6 (`OQP27/RigidityWindow.lean`, `OQP27/RigidityStrip.lean`) reduces the analytic part of rigidity to
two statements about one cell-embedded step field (Q_rig/RIGIDITY_ALLD.md s.3):
* `OQP27.Rig.Hyp_CellIneqSinglePos d` / `Hyp_CellIneqSingle d`: (1.3), `Q^ℓ(Q) ≤ N² Φ_c(1/4,1/4)`;
* `OQP27.Rig.Hyp_ContinuumTight d`: step (a) of s.3.7, a tight cell inequality forces equality in `(*)` at
  `λ* = log 2/(2π)` for the pair `(B(θ), g(θ))` for almost every `θ`.
Proved here (complete proofs), from L1's `Hyp_StripInequality`:
* `cellIneqSinglePos_of_strip`, `cellIneqSingle_of_strip` ((1.3), positive cells and all cells);
* `stepField_tight`: if Q-T1 for a step field is an equality, then `(*)` is an equality a.e. on every arc
  (the integrated slack `∫ (u* - Re Tr(A(g-λ)))` vanishes and the integrand dominates the `(*)`-defect);
* `conjField_eq_gconj`: L6's conjugate function (3.1) is the boundary imaginary part used here;
* `continuumTight_of_strip`: `Hyp_StripInequality → Hyp_ContinuumTight d`;
* `continuumCellEq`: L1's `Hyp_ContinuumCellEq d` (`(*)` and its equality case imply the rigidity steps 1-3),
  via L6's `continuumCellEq_of_tight`.
-/
import OQP27.CellStripFn
import OQP27.RigidityStrip

set_option autoImplicit false

namespace OQP27.Cell

open Polynomial Matrix Filter Topology Complex MeasureTheory Metric Set Real
open scoped Interval

variable {M : ℕ}

/-! ### Q-T1 for step fields with its slack -/

/-- **Equality analysis of Q-T1 for step fields** (RIGIDITY_ALLD.md s.3.7 (a)): if the inequality of
`stepField_ineq` is an equality, then on every arc the strip inequality `(*)` is an equality for the pair
`(B_x, g(θ))` for almost every `θ`. -/
theorem stepField_tight {n : ℕ} (P : ArcPartition n) (A B : ℕ → Matrix (Fin M) (Fin M) ℂ)
    (hA : ∀ k, IsProj (A k)) (hB : ∀ k, IsProj (B k)) (hAB : ∀ k, A k * B k = 0)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hop : ∑ k ∈ Finset.range n,
      ((((P.t (k + 1) - P.t k) / (2 * π)) : ℝ) : ℂ) • B k = (β : ℂ) • 1)
    {h : ℂ → ℝ} (hharm : InnerProductSpace.HarmonicOnNhd h strip)
    (hcont : ContinuousOn h cstrip) {C : ℝ} (hC : 0 ≤ C)
    (hgrowth : ∀ w ∈ cstrip, |h w| ≤ C * (1 + ‖w‖)) {lam : ℝ} (hstar : StarAt M h lam)
    (htight : (∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n, arcKernel P x y * (A x * B y).trace.re) / π -
      lam * ∑ x ∈ Finset.range n, (P.t (x + 1) - P.t x) * (A x).trace.re = 2 * π * (M * h β)) :
    ∀ x < n, ∀ᵐ θ ∂(volume.restrict (Ioo (P.t x) (P.t (x + 1)))),
      ((B x + I • gconj P B θ).charpoly.roots.map h).sum =
        OQP27.posPartTrace ((1 - B x) * (gconj P B θ - (lam : ℂ) • 1) * (1 - B x)) := by
  obtain ⟨hint, hval⟩ := mean_value_boundary P B hB hβ0 hβ1 hop hharm hcont hC hgrowth
  set ustar : ℝ → ℝ := fun θ => ((herg P B (Complex.exp ((θ : ℂ) * I))).charpoly.roots.map h).sum
    with hustar
  have hsub : ∀ k ≤ n, P.t k ∈ uIcc 0 (2 * π) := by
    intro k hk
    rw [uIcc_of_le (by positivity)]
    exact ⟨P.t_nonneg hk, P.t_le_two_pi hk⟩
  have hintx : ∀ x < n, IntervalIntegrable ustar volume (P.t x) (P.t (x + 1)) := fun x hx =>
    hint.mono_set (uIcc_subset_uIcc (hsub x hx.le) (hsub (x + 1) hx))
  have hsplit : ∫ θ in (0 : ℝ)..2 * π, ustar θ =
      ∑ x ∈ Finset.range n, ∫ θ in P.t x..P.t (x + 1), ustar θ := by
    rw [intervalIntegral.sum_integral_adjacent_intervals, P.t_zero, P.t_last]
    intro k hk
    exact hintx k hk
  set L : ℕ → ℝ → ℝ := fun x θ =>
    ∑ y ∈ Finset.range n, gcoef P y θ * (A x * B y).trace.re - lam * (A x).trace.re with hL
  have hL_int : ∀ x, IntervalIntegrable (L x) volume (P.t x) (P.t (x + 1)) := by
    intro x
    apply IntervalIntegrable.sub _ intervalIntegrable_const
    apply intervalIntegrable_fun_sum
    intro y _
    exact (intervalIntegrable_gcoef P y _ _).mul_const _
  have hL_val : ∀ x, ∫ θ in P.t x..P.t (x + 1), L x θ =
      (∑ y ∈ Finset.range n, arcKernel P x y * (A x * B y).trace.re) / π -
        lam * ((P.t (x + 1) - P.t x) * (A x).trace.re) := by
    intro x
    simp only [hL]
    rw [intervalIntegral.integral_sub _ intervalIntegrable_const,
      intervalIntegral.integral_finsetSum, intervalIntegral.integral_const, smul_eq_mul,
      Finset.sum_div]
    · congr 1
      · apply Finset.sum_congr rfl
        intro y _
        rw [intervalIntegral.integral_mul_const, integral_gcoef]
        ring
      · ring
    · intro y _
      exact (intervalIntegrable_gcoef P y _ _).mul_const _
    · apply intervalIntegrable_fun_sum
      intro y _
      exact (intervalIntegrable_gcoef P y _ _).mul_const _
  set pp : ℕ → ℝ → ℝ := fun x θ =>
    OQP27.posPartTrace ((1 - B x) * (gconj P B θ - (lam : ℂ) • 1) * (1 - B x)) with hpp
  -- pointwise chain on the open arcs
  have hchain : ∀ x < n, ∀ θ ∈ Ioo (P.t x) (P.t (x + 1)), L x θ ≤ pp x θ ∧ pp x θ ≤ ustar θ := by
    intro x hx θ hθ
    have hg := isHermitian_gconj P B hB θ
    have hY : (gconj P B θ - (lam : ℂ) • 1).IsHermitian := by
      apply hg.sub
      rw [Matrix.IsHermitian, conjTranspose_smul, conjTranspose_one, Complex.star_def,
        Complex.conj_ofReal]
    have hX := isHermitian_compress (hB x) hY
    have hppX : pp x θ = ∑ i, max (hX.eigenvalues i) 0 := by
      simp only [hpp]
      unfold OQP27.posPartTrace
      rw [dif_pos hX]
    constructor
    · have h1 : L x θ = (A x * ((1 - B x) * (gconj P B θ - (lam : ℂ) • 1) * (1 - B x))).trace.re := by
        simp only [hL]
        rw [← re_trace_mul_gconj, trace_compress (hA x) (hB x) (hAB x), mul_sub, trace_sub,
          Matrix.mul_smul, mul_one, trace_smul, smul_eq_mul, Complex.sub_re, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rw [h1, hppX]
      exact re_trace_mul_le_posPart (hA x) hX
    · simp only [hpp, hustar]
      rw [herg_boundary_eq P B hx hθ.1 hθ.2]
      exact hstar (B x) (gconj P B θ) (hB x) hg
  -- the slack on every arc vanishes
  have hnonneg : ∀ x ∈ Finset.range n,
      0 ≤ (∫ θ in P.t x..P.t (x + 1), ustar θ) - ∫ θ in P.t x..P.t (x + 1), L x θ := by
    intro x hx
    have hx' := Finset.mem_range.1 hx
    have := intervalIntegral.integral_mono_on_of_le_Ioo (P.t_lt x hx').le (hL_int x) (hintx x hx')
      (fun θ hθ => ((hchain x hx' θ hθ).1).trans (hchain x hx' θ hθ).2)
    linarith
  have hS1 : ∑ x ∈ Finset.range n,
      ((∫ θ in P.t x..P.t (x + 1), ustar θ) - ∫ θ in P.t x..P.t (x + 1), L x θ) =
        (∫ θ in (0 : ℝ)..2 * π, ustar θ) -
          ∑ x ∈ Finset.range n, ∫ θ in P.t x..P.t (x + 1), L x θ := by
    rw [Finset.sum_sub_distrib, hsplit]
  have hS2 : ∑ x ∈ Finset.range n, ∫ θ in P.t x..P.t (x + 1), L x θ =
      (∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n, arcKernel P x y * (A x * B y).trace.re) / π -
        lam * ∑ x ∈ Finset.range n, (P.t (x + 1) - P.t x) * (A x).trace.re := by
    rw [Finset.sum_congr rfl fun x _ => hL_val x, Finset.sum_sub_distrib, ← Finset.sum_div,
      ← Finset.mul_sum]
  have hsum0 : ∑ x ∈ Finset.range n,
      ((∫ θ in P.t x..P.t (x + 1), ustar θ) - ∫ θ in P.t x..P.t (x + 1), L x θ) = 0 := by
    rw [hS1, hval, hS2, htight, sub_self]
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hsum0
  intro x hx
  have hx' : x ∈ Finset.range n := Finset.mem_range.2 hx
  have hab : P.t x ≤ P.t (x + 1) := (P.t_lt x hx).le
  -- `∫_{J_x} (u* - L_x) = 0` with a nonnegative integrand
  have hdiff_int : IntervalIntegrable (fun θ => ustar θ - L x θ) volume (P.t x) (P.t (x + 1)) :=
    (hintx x hx).sub (hL_int x)
  have hI0 : ∫ θ in Ioc (P.t x) (P.t (x + 1)), (ustar θ - L x θ) = 0 := by
    rw [← intervalIntegral.integral_of_le hab, intervalIntegral.integral_sub (hintx x hx) (hL_int x)]
    exact hzero x hx'
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (P.t x) (P.t (x + 1)))] fun θ => ustar θ - L x θ := by
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [(Set.countable_singleton (P.t (x + 1))).ae_notMem volume] with θ hθe hθ
    have hθ' : θ ∈ Ioo (P.t x) (P.t (x + 1)) := ⟨hθ.1, lt_of_le_of_ne hθ.2 hθe⟩
    have := hchain x hx θ hθ'
    simp only [Pi.zero_apply]
    linarith [this.1, this.2]
  have hae := (setIntegral_eq_zero_iff_of_nonneg_ae hnn
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hdiff_int)).1 hI0
  have hae' : ∀ᵐ θ ∂(volume.restrict (Ioo (P.t x) (P.t (x + 1)))), ustar θ - L x θ = 0 :=
    ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioc_self hae
  rw [ae_restrict_iff' measurableSet_Ioo] at hae' ⊢
  filter_upwards [hae'] with θ hθ0 hθ
  have h0 := hθ0 hθ
  have hc := hchain x hx θ hθ
  have hpe : pp x θ = ustar θ := by linarith [hc.1, hc.2]
  simp only [hpp, hustar] at hpe
  rw [herg_boundary_eq P B hx hθ.1 hθ.2] at hpe
  exact hpe.symm

/-! ### Arcs of a partition -/

lemma ArcPartition.exists_arc {n : ℕ} (P : ArcPartition n) {θ : ℝ} (hθ : θ ∈ Ioo 0 (2 * π))
    (hne : ∀ k ≤ n, θ ≠ P.t k) : ∃ x < n, θ ∈ Ioo (P.t x) (P.t (x + 1)) := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have h1 := P.t_last
      rw [P.t_zero] at h1
      have := Real.pi_pos
      linarith
    · exact h
  have hex : ∃ k, θ < P.t (k + 1) := ⟨n - 1, by rw [Nat.sub_add_cancel hn, P.t_last]; exact hθ.2⟩
  classical
  set x := Nat.find hex with hxdef
  have hx1 : θ < P.t (x + 1) := Nat.find_spec hex
  have hxn : x < n := by
    have := Nat.find_min' hex (show θ < P.t (n - 1 + 1) by
      rw [Nat.sub_add_cancel hn, P.t_last]; exact hθ.2)
    omega
  refine ⟨x, hxn, ?_, hx1⟩
  rcases Nat.eq_zero_or_pos x with h0 | h0
  · rw [h0, P.t_zero]
    exact hθ.1
  · have hmin := Nat.find_min hex (show x - 1 < x by omega)
    rw [Nat.sub_add_cancel h0] at hmin
    push Not at hmin
    exact lt_of_le_of_ne hmin (Ne.symm (hne x hxn.le))

/-! ### (1.3) in the form of module L6 -/

section L6

variable {d : ℕ} [NeZero d] {ell : ℕ → ℝ}

lemma windowValue_eq : OQP27.Rig.windowValue d = (4 * d) ^ 2 * clausen2 (π / 2) / π ^ 2 := by
  unfold OQP27.Rig.windowValue coneG
  have := d_pos (d := d)
  rw [show 2 * π * (d : ℝ) / (4 * d) = π / 2 by field_simp; ring]
  field_simp

lemma cellFunctional_eq (C : OQP27.QConfig d M) :
    OQP27.Rig.cellFunctional ell C = (∑ x : ZMod (4 * d), ∑ y : ZMod (4 * d),
      cellPairKernel d ell x.val y.val * (C.Q x * C.Q (y + d)).trace.re) / M := by
  unfold OQP27.Rig.cellFunctional OQP27.Rig.pairTerm
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- The double sum of the cell-pair kernel in terms of the arc kernel of the cell partition. -/
lemma sum_kernel_eq_arc (hl : IsPosConeCell d ell) (F : CellFamily d M) :
    ∑ x : ZMod (4 * d), ∑ y : ZMod (4 * d),
      cellPairKernel d ell x.val y.val * (F.Q x * F.Q (y + d)).trace.re =
        (4 * d) ^ 2 / (2 * π ^ 2) * ∑ x ∈ Finset.range (4 * d), ∑ y ∈ Finset.range (4 * d),
          arcKernel (cellPartition hl) x y *
            (F.Q (x : ZMod (4 * d)) * F.Q ((y : ZMod (4 * d)) + d)).trace.re := by
  have hπ := Real.pi_pos
  have hd := d_pos (d := d)
  rw [Finset.mul_sum]
  rw [← sum_range_eq_sum_zmod (4 * d) (fun x => ∑ y : ZMod (4 * d),
    cellPairKernel d ell x.val y.val * (F.Q x * F.Q (y + d)).trace.re)]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  rw [← sum_range_eq_sum_zmod (4 * d) (fun y => cellPairKernel d ell (x : ZMod (4 * d)).val y.val *
    (F.Q (x : ZMod (4 * d)) * F.Q (y + d)).trace.re)]
  apply Finset.sum_congr rfl
  intro y hy
  rw [arcKernel_cellPartition hl, ZMod.val_natCast, ZMod.val_natCast,
    Nat.mod_eq_of_lt (Finset.mem_range.1 hx), Nat.mod_eq_of_lt (Finset.mem_range.1 hy)]
  field_simp

/-- **(1.3) from `(*)`**: `Q^ℓ(Q) ≤ N² Φ_c(1/4,1/4)` for positive cell vectors, in L6's form. -/
theorem cellFunctional_le_of_strip (hS : OQP27.Hyp_StripInequality) (hl : IsPosConeCell d ell)
    (C : OQP27.QConfig d M) (hM : 0 < M) :
    OQP27.Rig.cellFunctional ell C ≤ OQP27.Rig.windowValue d := by
  obtain ⟨hharm, hcont, Cg, hCg, hgrowth⟩ := hStrip_regular
  have h := cellFamily_ineq hl (toCellFamily C) hharm hcont hCg hgrowth (hStrip_left lamStar)
    (hStrip_right lamStar) (starAt_of_hyp hS M lamStar)
  have hMr : (0 : ℝ) < M := Nat.cast_pos.2 hM
  rw [cellFunctional_eq, windowValue_eq, div_le_iff₀ hMr]
  calc ∑ x : ZMod (4 * d), ∑ y : ZMod (4 * d),
        cellPairKernel d ell x.val y.val * (C.Q x * C.Q (y + d)).trace.re
      ≤ (4 * d) ^ 2 * M * clausen2 (π / 2) / π ^ 2 := h
    _ = (4 * d) ^ 2 * clausen2 (π / 2) / π ^ 2 * M := by ring

/-- L6's `Hyp_CellIneqSinglePos d` from the strip inequality. -/
theorem cellIneqSinglePos_of_strip (d : ℕ) [NeZero d] :
    OQP27.Hyp_StripInequality → OQP27.Rig.Hyp_CellIneqSinglePos d :=
  fun hS _ hM C _ hl => cellFunctional_le_of_strip hS hl C hM

/-- L6's `Hyp_CellIneqSingle d` (all cell vectors, zero cells allowed) from the strip inequality. -/
theorem cellIneqSingle_of_strip (d : ℕ) [NeZero d] :
    OQP27.Hyp_StripInequality → OQP27.Rig.Hyp_CellIneqSingle d := by
  intro hS M hM C ell hl
  set ellf : ℝ → ℕ → ℝ := fun ε r => (1 - ε) * ell r + ε with hellf
  have hpos : ∀ ε, 0 < ε → ε ≤ 1 → IsPosConeCell d (ellf ε) := by
    intro ε h0 h1
    refine ⟨⟨fun r hr => ?_, ?_⟩, fun r hr => ?_⟩
    · have := hl.1 r hr
      simp only [hellf]
      nlinarith
    · simp only [hellf]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hl.2, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      ring
    · have := hl.1 r hr
      simp only [hellf]
      nlinarith
  have hc : ∀ r, Continuous fun ε => ellf ε r := fun r => by
    simp only [hellf]
    fun_prop
  have hcont : Continuous fun ε => OQP27.Rig.cellFunctional (ellf ε) C := by
    unfold OQP27.Rig.cellFunctional
    exact continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun y _ =>
      (continuous_cellPairKernel hc _ _).mul continuous_const
  have h0 : ellf 0 = ell := by
    funext r
    simp [hellf]
  have htend : Tendsto (fun ε => OQP27.Rig.cellFunctional (ellf ε) C) (𝓝[>] 0)
      (𝓝 (OQP27.Rig.cellFunctional ell C)) := by
    have := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rwa [h0] at this
  apply le_of_tendsto htend
  filter_upwards [Ioc_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with ε hε
  exact cellFunctional_le_of_strip hS (hpos ε hε.1 hε.2) C hM

end L6

/-! ### The conjugate function of module L6 -/

section Conj

variable {d : ℕ} [NeZero d] {ell : ℕ → ℝ}

lemma cellT_eq_t (hl : IsPosConeCell d ell) (j : ℕ) :
    OQP27.cellT (OQP27.Rig.ellFin (d := d) ell) j = (cellPartition hl).t j := by
  rw [cellPartition_t]
  unfold OQP27.cellT OQP27.cellL OQP27.cellLen OQP27.Rig.ellFin cellBoundary
  rfl

lemma ell_sub_two_pi (θ : ℝ) : OQP27.Cell.ell (θ - 2 * π) = OQP27.Cell.ell θ := by
  unfold OQP27.Cell.ell
  rw [show (θ - 2 * π) / 2 = θ / 2 - π by ring, Real.sin_sub_pi, mul_neg, Real.log_neg_eq_log]

/-- L6's conjugate function (3.1) equals the imaginary boundary part `g = ∑_y g_y B_y` used here. -/
lemma conjField_eq_gconj (hl : IsPosConeCell d ell) (C : OQP27.QConfig d M) {θ : ℝ}
    (hθ : θ ∈ Ioo 0 (2 * π)) (hne : ∀ k ≤ 4 * d, θ ≠ (cellPartition hl).t k) :
    OQP27.conjField (OQP27.Rig.ellFin ell) (OQP27.Rig.fieldB C) θ =
      gconj (cellPartition hl) (fun x => C.Q ((x : ZMod (4 * d)) + d)) θ := by
  have hBz : ∀ z, OQP27.Rig.fieldB C z = C.Q (z + d) := fun z => rfl
  -- the coefficients `ℓ(θ - t_j)/π`
  have h1 : gconj (cellPartition hl) (fun x => C.Q ((x : ZMod (4 * d)) + d)) θ =
      ∑ y ∈ Finset.range (4 * d), ((OQP27.Cell.ell (θ - (cellPartition hl).t y) / π : ℝ) : ℂ) •
          OQP27.Rig.fieldB C (y : ZMod (4 * d)) -
        ∑ y ∈ Finset.range (4 * d),
          ((OQP27.Cell.ell (θ - (cellPartition hl).t (y + 1)) / π : ℝ) : ℂ) •
            OQP27.Rig.fieldB C (y : ZMod (4 * d)) := by
    unfold gconj
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y _
    rw [hBz, ← sub_smul]
    congr 1
    simp only [gcoef]
    push_cast
    ring
  -- shift of the second sum
  have hshift : ∑ y ∈ Finset.range (4 * d),
      ((OQP27.Cell.ell (θ - (cellPartition hl).t (y + 1)) / π : ℝ) : ℂ) •
        OQP27.Rig.fieldB C (y : ZMod (4 * d)) =
      ∑ j ∈ Finset.range (4 * d), ((OQP27.Cell.ell (θ - (cellPartition hl).t j) / π : ℝ) : ℂ) •
        OQP27.Rig.fieldB C ((j : ZMod (4 * d)) - 1) := by
    set φ : ℕ → Matrix (Fin M) (Fin M) ℂ := fun j =>
      ((OQP27.Cell.ell (θ - (cellPartition hl).t j) / π : ℝ) : ℂ) •
        OQP27.Rig.fieldB C ((j : ZMod (4 * d)) - 1) with hφ
    have hφs : ∀ y, ((OQP27.Cell.ell (θ - (cellPartition hl).t (y + 1)) / π : ℝ) : ℂ) •
        OQP27.Rig.fieldB C (y : ZMod (4 * d)) = φ (y + 1) := by
      intro y
      simp only [hφ]
      congr 2
      push_cast
      ring
    have hφN : φ (4 * d) = φ 0 := by
      simp only [hφ]
      have e1 : ((4 * d : ℕ) : ZMod (4 * d)) = 0 := ZMod.natCast_self _
      rw [e1, Nat.cast_zero, (cellPartition hl).t_last, (cellPartition hl).t_zero, sub_zero,
        ell_sub_two_pi]
    have h2 := Finset.sum_range_succ' φ (4 * d)
    have h3 := Finset.sum_range_succ φ (4 * d)
    rw [hφN] at h3
    rw [Finset.sum_congr rfl fun y _ => hφs y]
    exact add_right_cancel (h2.symm.trans h3)
  -- the constant `log 2` drops out
  have hsin : ∀ j ∈ Finset.range (4 * d), Real.sin ((θ - (cellPartition hl).t j) / 2) ≠ 0 :=
    fun j hj => (cellPartition hl).sin_half_ne_zero hθ (Finset.mem_range.1 hj).le
      (hne j (Finset.mem_range.1 hj).le)
  have hsplit : ∀ j ∈ Finset.range (4 * d),
      ((OQP27.Cell.ell (θ - (cellPartition hl).t j) / π : ℝ) : ℂ) •
        (OQP27.Rig.fieldB C (j : ZMod (4 * d)) - OQP27.Rig.fieldB C ((j : ZMod (4 * d)) - 1)) =
      ((Real.log 2 / π : ℝ) : ℂ) •
        (OQP27.Rig.fieldB C (j : ZMod (4 * d)) - OQP27.Rig.fieldB C ((j : ZMod (4 * d)) - 1)) +
      ((Real.log |Real.sin ((θ - (cellPartition hl).t j) / 2)| / π : ℝ) : ℂ) •
        (OQP27.Rig.fieldB C (j : ZMod (4 * d)) - OQP27.Rig.fieldB C ((j : ZMod (4 * d)) - 1)) := by
    intro j hj
    rw [← add_smul, ← Complex.ofReal_add]
    congr 2
    unfold OQP27.Cell.ell
    rw [Real.log_mul two_ne_zero (hsin j hj), Real.log_abs]
    ring
  have hzero : ∑ j ∈ Finset.range (4 * d), ((Real.log 2 / π : ℝ) : ℂ) •
      (OQP27.Rig.fieldB C (j : ZMod (4 * d)) - OQP27.Rig.fieldB C ((j : ZMod (4 * d)) - 1)) = 0 := by
    rw [← Finset.smul_sum, Finset.sum_sub_distrib]
    have e1 := sum_range_eq_sum_zmod (4 * d) (OQP27.Rig.fieldB C)
    have e2 := sum_range_eq_sum_zmod (4 * d) (fun z => OQP27.Rig.fieldB C (z - 1))
    have e3 : ∑ z : ZMod (4 * d), OQP27.Rig.fieldB C (z - 1) = ∑ z, OQP27.Rig.fieldB C z :=
      Equiv.sum_comp (Equiv.subRight (1 : ZMod (4 * d))) (OQP27.Rig.fieldB C)
    rw [e1, e2, e3, sub_self, smul_zero]
  rw [h1, hshift, ← Finset.sum_sub_distrib]
  have hcomb : ∀ j ∈ Finset.range (4 * d),
      ((OQP27.Cell.ell (θ - (cellPartition hl).t j) / π : ℝ) : ℂ) •
        OQP27.Rig.fieldB C (j : ZMod (4 * d)) -
      ((OQP27.Cell.ell (θ - (cellPartition hl).t j) / π : ℝ) : ℂ) •
        OQP27.Rig.fieldB C ((j : ZMod (4 * d)) - 1) =
      ((OQP27.Cell.ell (θ - (cellPartition hl).t j) / π : ℝ) : ℂ) •
        (OQP27.Rig.fieldB C (j : ZMod (4 * d)) - OQP27.Rig.fieldB C ((j : ZMod (4 * d)) - 1)) :=
    fun j _ => (smul_sub _ _ _).symm
  rw [Finset.sum_congr rfl hcomb, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hzero,
    zero_add]
  unfold OQP27.conjField
  rw [← sum_range_eq_sum_zmod (4 * d) (fun z => ((Real.log |Real.sin ((θ -
    OQP27.cellT (OQP27.Rig.ellFin (d := d) ell) z.val) / 2)| / Real.pi : ℝ) : ℂ) •
      (OQP27.Rig.fieldB C z - OQP27.Rig.fieldB C (z - 1)))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.1 hj), cellT_eq_t hl]

end Conj

/-! ### Step (a) of RIGIDITY_ALLD.md s.3.7 -/

section Tight

variable {d : ℕ} [NeZero d]

/-- **`(*)` implies step (a)**: a tight cell inequality with all cells positive makes `(*)` tight at
`λ*` for the pair `(B(θ), g(θ))` for almost every `θ` (L6's `Hyp_ContinuumTight d`). -/
theorem continuumTight_of_strip (d : ℕ) [NeZero d] (hS : OQP27.Hyp_StripInequality) :
    OQP27.Rig.Hyp_ContinuumTight d := by
  intro M hM C ell hl hQ
  obtain ⟨hharm, hcont, Cg, hCg, hgrowth⟩ := hStrip_regular
  have hπ := Real.pi_pos
  have hd := d_pos (d := d)
  have hMr : (0 : ℝ) < M := Nat.cast_pos.2 hM
  have hw := window_value hharm hcont hCg hgrowth (hStrip_left lamStar) (hStrip_right lamStar)
  -- the tightness of Q-T1 for the step field
  have h1 : ∑ x : ZMod (4 * d), ∑ y : ZMod (4 * d),
      cellPairKernel d ell x.val y.val * (C.Q x * C.Q (y + d)).trace.re =
        (4 * d) ^ 2 / (2 * π ^ 2) * ∑ x ∈ Finset.range (4 * d), ∑ y ∈ Finset.range (4 * d),
          arcKernel (cellPartition hl) x y *
            (C.Q (x : ZMod (4 * d)) * C.Q ((y : ZMod (4 * d)) + d)).trace.re :=
    sum_kernel_eq_arc hl (toCellFamily C)
  have hsum : ∑ x ∈ Finset.range (4 * d), ∑ y ∈ Finset.range (4 * d),
      arcKernel (cellPartition hl) x y *
        (C.Q (x : ZMod (4 * d)) * C.Q ((y : ZMod (4 * d)) + d)).trace.re =
          2 * M * clausen2 (π / 2) := by
    rw [cellFunctional_eq, windowValue_eq, div_eq_iff hMr.ne', h1] at hQ
    have hN2 : (0 : ℝ) < (4 * d) ^ 2 := by positivity
    field_simp at hQ
    nlinarith [hQ]
  have htr : ∑ x ∈ Finset.range (4 * d), ((cellPartition hl).t (x + 1) - (cellPartition hl).t x) *
      (C.Q (x : ZMod (4 * d))).trace.re = π / 2 * M := cell_trace_A hl (toCellFamily C)
  have htight : (∑ x ∈ Finset.range (4 * d), ∑ y ∈ Finset.range (4 * d),
      arcKernel (cellPartition hl) x y *
        (C.Q (x : ZMod (4 * d)) * C.Q ((y : ZMod (4 * d)) + d)).trace.re) / π -
        lamStar * ∑ x ∈ Finset.range (4 * d),
          ((cellPartition hl).t (x + 1) - (cellPartition hl).t x) *
            (C.Q (x : ZMod (4 * d))).trace.re =
          2 * π * (M * OQP27.hStrip lamStar ((1 / 4 : ℝ) : ℂ)) := by
    rw [hsum, htr]
    have : OQP27.hStrip lamStar ((1 / 4 : ℝ) : ℂ) = clausen2 (π / 2) / π ^ 2 - lamStar / 4 := by
      linarith
    rw [this]
    field_simp
    ring
  have hae := stepField_tight (cellPartition hl) (fun x => C.Q (x : ZMod (4 * d)))
    (fun x => C.Q ((x : ZMod (4 * d)) + d)) (fun x => (toCellFamily C).proj _)
    (fun x => (toCellFamily C).proj _) (fun x => (toCellFamily C).orth _)
    (by norm_num) (by norm_num) (cell_op_B hl (toCellFamily C)) hharm hcont hCg hgrowth
    (starAt_of_hyp hS M lamStar) htight
  -- transfer to the step field and the conjugate function of module L6
  rw [ae_restrict_iff' measurableSet_Ioo]
  have hall : ∀ᵐ θ ∂(volume : Measure ℝ), ∀ x : Fin (4 * d),
      θ ∈ Ioo ((cellPartition hl).t x) ((cellPartition hl).t (x + 1)) →
        ((C.Q (((x : ℕ) : ZMod (4 * d)) + d) + I •
          gconj (cellPartition hl) (fun x => C.Q ((x : ZMod (4 * d)) + d)) θ).charpoly.roots.map
            (OQP27.hStrip lamStar)).sum =
        OQP27.posPartTrace ((1 - C.Q (((x : ℕ) : ZMod (4 * d)) + d)) *
          (gconj (cellPartition hl) (fun x => C.Q ((x : ZMod (4 * d)) + d)) θ - (lamStar : ℂ) • 1) *
          (1 - C.Q (((x : ℕ) : ZMod (4 * d)) + d))) := by
    rw [ae_all_iff]
    intro x
    have := hae x x.2
    rw [ae_restrict_iff' measurableSet_Ioo] at this
    filter_upwards [this] with θ hθ hmem
    exact hθ hmem
  have hTc : ((cellPartition hl).ends : Set ℝ).Countable := (Finset.finite_toSet _).countable
  filter_upwards [hall, hTc.ae_notMem volume] with θ hθ hθe hθI
  have hne : ∀ k ≤ 4 * d, θ ≠ (cellPartition hl).t k := by
    intro k hk h
    exact hθe (h ▸ (cellPartition hl).mem_ends hk)
  obtain ⟨x, hx, hmem⟩ := (cellPartition hl).exists_arc hθI hne
  have hpos : ∀ r, 0 < OQP27.Rig.ellFin ell r := fun r => hl.2 r r.isLt
  have hxv : ((x : ZMod (4 * d))).val = x := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hx]
  have hstep : OQP27.stepField (OQP27.Rig.ellFin ell) (OQP27.Rig.fieldB C) θ =
      C.Q ((x : ZMod (4 * d)) + d) := by
    rw [OQP27.stepField_eq hpos (OQP27.Rig.fieldB C) (x : ZMod (4 * d))
      (by rw [hxv, cellT_eq_t hl, cellT_eq_t hl]; exact hmem)]
    rfl
  have hconj : OQP27.conjField (OQP27.Rig.ellFin ell) (OQP27.Rig.fieldB C) θ =
      gconj (cellPartition hl) (fun x => C.Q ((x : ZMod (4 * d)) + d)) θ :=
    conjField_eq_gconj hl C hθI hne
  have hlam : OQP27.Rig.lamStar = lamStar := rfl
  rw [hstep, hconj, hlam]
  exact hθ ⟨x, hx⟩ hmem

/-- **L1's `Hyp_ContinuumCellEq d`**: `(*)` and its equality case imply the rigidity steps 1-3
(via L6's `continuumCellEq_of_tight`). -/
theorem continuumCellEq (d : ℕ) [NeZero d] : OQP27.Hyp_ContinuumCellEq d :=
  OQP27.Rig.continuumCellEq_of_tight (cellIneqSinglePos_of_strip d) (continuumTight_of_strip d)

end Tight

end OQP27.Cell
