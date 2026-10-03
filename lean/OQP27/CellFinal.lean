/-
OQP27/CellFinal.lean  (module L5: the cell-embedding inequalities from the strip inequality)

Main results (complete proofs):
* `cellIneq_all`: QD2-L1, `⟨u^ℓ, δ⟩ ≤ 0` for every 27B configuration and every cell vector `ℓ ∈ Δ_d`
  (zero cells allowed), for any strip function `h` that is harmonic on the open strip, continuous on the
  closed strip, of linear growth, has the boundary values of `h_{λ*}`, and satisfies `(*)` at `λ*`.
  Positive cells: `cellIneq_pos` (file `CellEmbedding`); zero cells: limit `ℓ_ε = (1-ε)ℓ + ε → ℓ`
  (the cell directions depend continuously on `ℓ`), as in RIGIDITY_ALLD.md 3.1 ("zero-length cells are
  harmless").
* `continuumCell_of_regular`: L1's `Hyp_ContinuumCell d` (`Hyp_StripInequality → Hyp_CellInequalities d`)
  for every `d`, assuming only `Hyp_hStripRegular`: the regularity of L1's `hStrip λ*` (harmonic on the
  open strip, continuous on the closed strip, linear growth).  The boundary values of `hStrip` hold by
  definition (`hStrip_left`, `hStrip_right`).
`Hyp_hStripRegular` is a classical property of the Poisson integral of the strip; it is PROVED in
`OQP27/CellStripFn.lean` (`hStrip_regular`), which also states the unconditional result
`OQP27.Cell.continuumCell d : Hyp_ContinuumCell d`.
-/
import OQP27.CellEmbedding

set_option autoImplicit false

namespace OQP27.Cell

open Polynomial Matrix Filter Topology Complex MeasureTheory Metric Set Real Finset

/-! ### Continuity of the cell directions in the cell vector -/

section Continuity

variable {d : ℕ} {ellf : ℝ → ℕ → ℝ}

lemma continuous_coneG : Continuous (coneG d) := by
  unfold coneG
  exact continuous_const.mul (continuous_clausen2.comp (by fun_prop))

lemma continuous_cellBoundary (hc : ∀ r, Continuous fun ε => ellf ε r) (n : ℕ) :
    Continuous fun ε => cellBoundary d (ellf ε) n := by
  unfold cellBoundary
  exact continuous_finsetSum _ fun i _ => hc _

lemma continuous_cellPairKernel (hc : ∀ r, Continuous fun ε => ellf ε r) (x y : ℕ) :
    Continuous fun ε => cellPairKernel d (ellf ε) x y := by
  unfold cellPairKernel
  have hb := continuous_cellBoundary (d := d) hc
  have hG := continuous_coneG (d := d)
  exact (((hG.comp ((hb _).sub (hb _))).sub (hG.comp ((hb _).sub (hb _)))).sub
    (hG.comp ((hb _).sub (hb _)))).add (hG.comp ((hb _).sub (hb _)))

lemma continuous_cellKernelAvg (hc : ∀ r, Continuous fun ε => ellf ε r) (n : ℕ) :
    Continuous fun ε => cellKernelAvg d (ellf ε) n := by
  unfold cellKernelAvg
  exact (continuous_finsetSum _ fun r _ => continuous_cellPairKernel hc _ _).div_const _

lemma continuous_cellDirection (hc : ∀ r, Continuous fun ε => ellf ε r) (m : ℕ) :
    Continuous fun ε => cellDirection d (ellf ε) m := by
  unfold cellDirection
  exact (continuous_cellKernelAvg hc _).add (continuous_cellKernelAvg hc _)

end Continuity

/-! ### Zero-length cells -/

section AllCells

variable {d M : ℕ} [NeZero d] {ell : ℕ → ℝ}

/-- **QD2-L1 (cell-embedding inequalities)** for every cell vector `ℓ ∈ Δ_d`. -/
theorem cellIneq_all (hl : IsConeCell d ell) (C : OQP27.QConfig d M) (hM : 0 < M)
    {h : ℂ → ℝ} (hharm : InnerProductSpace.HarmonicOnNhd h strip)
    (hcont : ContinuousOn h cstrip) {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgrowth : ∀ w ∈ cstrip, |h w| ≤ Cg * (1 + ‖w‖))
    (hleft : ∀ y : ℝ, h ((y : ℂ) * I) = max (y - lamStar) 0)
    (hright : ∀ y : ℝ, h (1 + (y : ℂ) * I) = 0) (hstar : StarAt M h lamStar) :
    OQP27.pairingIco d (cellDirection d ell) C.delta ≤ 0 := by
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
  have hle : ∀ ε, 0 < ε → ε ≤ 1 →
      OQP27.pairingIco d (cellDirection d (ellf ε)) C.delta ≤ 0 := fun ε h0 h1 =>
    cellIneq_pos (hpos ε h0 h1) C hM hharm hcont hCg hgrowth hleft hright hstar
  have hc : ∀ r, Continuous fun ε => ellf ε r := fun r => by
    simp only [hellf]
    fun_prop
  have hcont' : Continuous fun ε => OQP27.pairingIco d (cellDirection d (ellf ε)) C.delta := by
    unfold OQP27.pairingIco
    exact continuous_finsetSum _ fun m _ => (continuous_cellDirection hc m).mul continuous_const
  have h0 : ellf 0 = ell := by
    funext r
    simp [hellf]
  have htend : Tendsto (fun ε => OQP27.pairingIco d (cellDirection d (ellf ε)) C.delta)
      (𝓝[>] 0) (𝓝 (OQP27.pairingIco d (cellDirection d ell) C.delta)) := by
    have := (hcont'.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rwa [h0] at this
  apply le_of_tendsto htend
  filter_upwards [Ioc_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with ε hε
  exact hle ε hε.1 hε.2

end AllCells

/-! ### Connection with module L1 -/

lemma hStrip_left (lam y : ℝ) : OQP27.hStrip lam ((y : ℂ) * I) = max (y - lam) 0 := by
  unfold OQP27.hStrip
  simp

lemma hStrip_right (lam y : ℝ) : OQP27.hStrip lam (1 + (y : ℂ) * I) = 0 := by
  unfold OQP27.hStrip
  simp

/-- **Regularity of `h_{λ*}`** (L1's `hStrip`, the Poisson integral of `(y - λ*)_+` over the left edge of the
strip): harmonic on the open strip, continuous on the closed strip, and of linear growth.  Classical
(Q_2bmv/PROOF.md Lemma 6 identifies `h_λ = -(1/π²) Im Li₂(e^{π(y-λ)} e^{-iπx})`); proved in
`OQP27/CellStripFn.lean`. -/
def Hyp_hStripRegular : Prop :=
  InnerProductSpace.HarmonicOnNhd (OQP27.hStrip lamStar) strip ∧
    ContinuousOn (OQP27.hStrip lamStar) cstrip ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ cstrip, |OQP27.hStrip lamStar w| ≤ C * (1 + ‖w‖)

/-- **The analytic link `(*) ⇒ QD2-L1`**: L1's `Hyp_ContinuumCell d` for every `d ≥ 1`, given the
regularity of `h_{λ*}`. -/
theorem continuumCell_of_regular (d : ℕ) [NeZero d] (hreg : Hyp_hStripRegular) :
    OQP27.Hyp_ContinuumCell d := by
  intro hS M hM C ell hl
  obtain ⟨hharm, hcont, Cg, hCg, hgrowth⟩ := hreg
  exact cellIneq_all hl C hM hharm hcont hCg hgrowth (hStrip_left lamStar) (hStrip_right lamStar)
    (starAt_of_hyp hS M lamStar)

end OQP27.Cell
