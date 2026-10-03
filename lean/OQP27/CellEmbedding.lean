/-
OQP27/CellEmbedding.lean  (module L5, layer 6: the cell embedding of 27B configurations)

QD2/LOG.md s.4 (ii)-(iii) and Q_rig/RIGIDITY_ALLD.md 1.5, 3.1.  For a cell vector `ℓ` with all cells positive,
the cells `I_x = [L_x, L_{x+1})` of `ℝ/Nℤ` (`N = 4d`, `L_x = cellBoundary d ℓ x`) become the arcs
`t_x = 2π L_x/N` of the circle (`cellPartition`).  A 27B configuration gives the step fields
`A = Q_x`, `B = Q_{x+d}` on these arcs; they satisfy the operator constraints `∑ (ℓ_x/N) Q_x = 1/4`,
`∑ (ℓ_x/N) Q_{x+d} = 1/4` because every residue class mod `d` is a PVM (`CellFamily.siteSum`), and the
same holds for every rotation `Q_x ↦ Q_{x-c}` (`CellFamily.rot`).

Proved here (complete proofs, no hypotheses beyond the stated ones):
* `cellFamily_ineq` (RIGIDITY_ALLD.md (1.3)): `∑_{x,y} K^ℓ(x,y) Re Tr(Q_x Q_{y+d}) ≤ N² M Cl₂(π/2)/π²`, from
  Q-T1 for step fields (`stepField_ineq`, which uses `(*)` at `λ* = log 2/(2π)`) and the window value
  `h(1/4) + λ*/4 = Cl₂(π/2)/π²` (`window_value`); here `K^ℓ = (N²/(2π²)) κ` (`arcKernel_cellPartition`);
* kernel symmetries (periodicity, `d`-shift invariance, antisymmetry), the rotation average
  `∑_{c<d} K^ℓ(x+c, y+c) = d K̃(x - y)` (`sum_kernel_diag`), and the folding
  `∑_n K̃(n) T(n) = ⟨u^ℓ, N⟩ + K̃(d) N(d)` (`fold_pairCount`, with `N(2d-m) = N(m)`, `N(d) = d`);
* `window_identity`: `⟨u^ℓ, (m)_m⟩ + d K̃(d) = N² Cl₂(π/2)/π²` (summation by parts on `K̃ = Δ²P`);
* `cellIneq_pos`: QD2-L1, `⟨u^ℓ, δ⟩ ≤ 0`, for every 27B configuration and every positive cell vector.
-/
import OQP27.CellLegendre
import OQP27.ReductionQ

set_option autoImplicit false

namespace OQP27.Cell

open Polynomial Matrix Filter Topology Complex MeasureTheory Metric Set Real Finset
open scoped Interval

/-! ### Residues and sums over `ℤ_N` -/

/-- The residue map `ℤ_{4d} → ℤ_d`. -/
def resid (d : ℕ) : ZMod (4 * d) →+* ZMod d := ZMod.castHom (dvd_mul_left d 4) (ZMod d)

lemma resid_natCast {d : ℕ} (n : ℕ) : resid d (n : ZMod (4 * d)) = (n : ZMod d) := map_natCast _ n

lemma resid_self {d : ℕ} : resid d (d : ZMod (4 * d)) = 0 := by
  rw [resid_natCast, ZMod.natCast_self]

lemma sum_range_eq_sum_zmod {β : Type*} [AddCommMonoid β] (N : ℕ) [NeZero N] (g : ZMod N → β) :
    ∑ x ∈ Finset.range N, g (x : ZMod N) = ∑ x : ZMod N, g x := by
  refine Finset.sum_nbij' (fun x => (x : ZMod N)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
  · intro x _
    exact Finset.mem_univ _
  · intro x _
    exact Finset.mem_range.2 (ZMod.val_lt x)
  · intro x hx
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.1 hx)]
  · intro x _
    simp
  · intro x _
    rfl

/-! ### The cell partition of a positive cell vector -/

section Partition

variable {d : ℕ} {ell : ℕ → ℝ}

lemma cellBoundary_zero' : cellBoundary d ell 0 = 0 := by
  simp [cellBoundary]

lemma cellBoundary_succ' (n : ℕ) :
    cellBoundary d ell (n + 1) = cellBoundary d ell n + ell (n % d) := by
  simp [cellBoundary, Finset.sum_range_succ]

lemma cellBoundary_add_N (hl : IsConeCell d ell) (n : ℕ) :
    cellBoundary d ell (n + 4 * d) = cellBoundary d ell n + 4 * d := by
  have h := cellBoundary_add_period hl
  rw [show n + 4 * d = n + d + d + d + d by ring, h, h, h, h]
  ring

variable [NeZero d]

omit [NeZero d] in
lemma cellBoundary_N (hl : IsConeCell d ell) : cellBoundary d ell (4 * d) = 4 * d := by
  have := cellBoundary_add_N hl 0
  rwa [zero_add, cellBoundary_zero', zero_add] at this

lemma d_pos : (0 : ℝ) < d := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne d))

/-- The arc partition `t_x = 2π L_x/N` of a positive cell vector. -/
noncomputable def cellPartition (hl : IsPosConeCell d ell) : ArcPartition (4 * d) where
  t := fun x => 2 * π * cellBoundary d ell x / (4 * d)
  t_zero := by simp [cellBoundary_zero']
  t_last := by
    rw [cellBoundary_N hl.1]
    have := d_pos (d := d)
    field_simp
  t_lt := by
    intro k _
    rw [cellBoundary_succ']
    have hpos : 0 < ell (k % d) := hl.2 _ (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne d)))
    have := d_pos (d := d)
    have hπ := Real.pi_pos
    apply div_lt_div_of_pos_right _ (by positivity)
    nlinarith

lemma cellPartition_t (hl : IsPosConeCell d ell) (x : ℕ) :
    (cellPartition hl).t x = 2 * π * cellBoundary d ell x / (4 * d) := rfl

lemma cellPartition_len (hl : IsPosConeCell d ell) (x : ℕ) :
    ((cellPartition hl).t (x + 1) - (cellPartition hl).t x) / (2 * π) = ell (x % d) / (4 * d) := by
  rw [cellPartition_t, cellPartition_t, cellBoundary_succ']
  have := d_pos (d := d)
  have hπ := Real.pi_pos
  field_simp
  ring

/-- The arc kernel of the cell partition is `(2π²/N²)` times the cell-pair kernel `K^ℓ`. -/
lemma arcKernel_cellPartition (hl : IsPosConeCell d ell) (x y : ℕ) :
    arcKernel (cellPartition hl) x y =
      2 * π ^ 2 / (4 * d) ^ 2 * cellPairKernel d ell x y := by
  unfold arcKernel cellPairKernel coneG
  simp only [cellPartition_t]
  have := d_pos (d := d)
  have hπ := Real.pi_pos
  have e : ∀ a b : ℝ, 2 * π * (a - b) / (4 * d) = 2 * π * a / (4 * d) - 2 * π * b / (4 * d) := by
    intro a b
    ring
  simp only [e]
  field_simp
  ring

end Partition

/-! ### Families of projections indexed by `ℤ_{4d}` -/

/-- The properties of a 27B configuration used by the cell embedding: projections, `Q_x Q_{x+d} = 0`,
and the site sums `∑_x f(x mod d) Q_x = (∑_k f k) 1`. -/
structure CellFamily (d M : ℕ) [NeZero d] where
  Q : ZMod (4 * d) → Matrix (Fin M) (Fin M) ℂ
  proj : ∀ x, IsProj (Q x)
  orth : ∀ x, Q x * Q (x + d) = 0
  siteSum : ∀ f : ZMod d → ℂ, ∑ x, f (resid d x) • Q x = (∑ k, f k) • (1 : Matrix (Fin M) (Fin M) ℂ)

namespace CellFamily

variable {d M : ℕ} [NeZero d]

/-- The rotated family `Q'_x = Q_{x - c}`. -/
def rot (F : CellFamily d M) (c : ZMod (4 * d)) : CellFamily d M where
  Q := fun x => F.Q (x - c)
  proj := fun x => F.proj (x - c)
  orth := fun x => by
    rw [show x + (d : ZMod (4 * d)) - c = x - c + d by ring]
    exact F.orth (x - c)
  siteSum := fun f => by
    rw [← Equiv.sum_comp (Equiv.addRight c)]
    simp only [Equiv.coe_addRight, add_sub_cancel_right, map_add]
    rw [F.siteSum (fun k => f (k + resid d c))]
    congr 1
    exact Equiv.sum_comp (Equiv.addRight (resid d c)) f

end CellFamily

/-! ### 27B configurations are cell families -/

section Config

variable {d M : ℕ} [NeZero d]

omit [NeZero d] in
lemma siteIndex_eq_qd (k : Fin d) (a : ZMod 4) : OQP27.siteIndex d k a = OQP27.Red.qd d k a := by
  rw [OQP27.Red.qd_eq]
  rfl

omit [NeZero d] in
lemma pvm_qd (C : OQP27.QConfig d M) {k : ℕ} (hk : k < d) :
    ∑ a : ZMod 4, C.Q (OQP27.Red.qd d k a) = 1 := by
  have := C.pvm ⟨k, hk⟩
  simpa [siteIndex_eq_qd] using this

/-- The PVM of the site `k`. -/
def sitePVM (C : OQP27.QConfig d M) {k : ℕ} (hk : k < d) : OQP27.PVM 4 M where
  proj := fun a => C.Q (OQP27.Red.qd d k a)
  isProj := fun _ => C.isProj _
  sum_eq_one := pvm_qd C hk

lemma qconfig_orth (C : OQP27.QConfig d M) (x : ZMod (4 * d)) {a b : ZMod 4} (hab : a ≠ b) :
    C.Q (OQP27.Red.qd d (OQP27.Red.site d x) a) * C.Q (OQP27.Red.qd d (OQP27.Red.site d x) b) = 0 :=
  (sitePVM C (OQP27.Red.site_lt (Nat.pos_of_ne_zero (NeZero.ne d)) x)).mul_eq_zero hab

lemma qconfig_orth_d (C : OQP27.QConfig d M) (x : ZMod (4 * d)) : C.Q x * C.Q (x + d) = 0 := by
  have h1 := OQP27.Red.qd_site_label x
  have h2 : x + (d : ZMod (4 * d)) =
      OQP27.Red.qd d (OQP27.Red.site d x) (OQP27.Red.label d x - 1) := by
    conv_lhs => rw [← h1]
    rw [OQP27.Red.qd_add_d]
  rw [h2]
  conv_lhs => arg 1; rw [← h1]
  apply qconfig_orth
  intro h
  have : (0 : ZMod 4) = -1 := by
    have := congrArg (fun t => t - OQP27.Red.label d x) h
    simp only [sub_self] at this
    rw [this]
    ring
  exact absurd this (by decide)

lemma qconfig_orth_2d (C : OQP27.QConfig d M) (x : ZMod (4 * d)) :
    C.Q x * C.Q (x + 2 * d) = 0 := by
  have h1 := OQP27.Red.qd_site_label x
  have h2 : x + 2 * (d : ZMod (4 * d)) =
      OQP27.Red.qd d (OQP27.Red.site d x) (OQP27.Red.label d x - 1 - 1) := by
    conv_lhs => rw [← h1]
    rw [two_mul, ← add_assoc, OQP27.Red.qd_add_d, OQP27.Red.qd_add_d]
  rw [h2]
  conv_lhs => arg 1; rw [← h1]
  apply qconfig_orth
  intro h
  have : (0 : ZMod 4) = -1 - 1 := by
    have := congrArg (fun t => t - OQP27.Red.label d x) h
    simp only [sub_self] at this
    rw [this]
    ring
  exact absurd this (by decide)

omit [NeZero d] in
lemma resid_qd (k : ℕ) (a : ZMod 4) :
    resid d (OQP27.Red.qd d k a) = (k : ZMod d) := by
  rw [OQP27.Red.qd_eq, map_sub, resid_natCast]
  unfold OQP27.Red.mu
  rw [map_mul, resid_self, zero_mul, sub_zero]

lemma qconfig_siteSum (C : OQP27.QConfig d M) (f : ZMod d → ℂ) :
    ∑ x, f (resid d x) • C.Q x = (∑ k, f k) • (1 : Matrix (Fin M) (Fin M) ℂ) := by
  rw [OQP27.Red.sum_zmod4d]
  have h : ∀ k ∈ Finset.range d, ∑ a : ZMod 4, f (resid d (OQP27.Red.qd d k a)) •
      C.Q (OQP27.Red.qd d k a) = f (k : ZMod d) • (1 : Matrix (Fin M) (Fin M) ℂ) := by
    intro k hk
    simp only [resid_qd]
    rw [← Finset.smul_sum, pvm_qd C (Finset.mem_range.1 hk)]
  rw [Finset.sum_congr rfl h, ← Finset.sum_smul, sum_range_eq_sum_zmod d f]

/-- A 27B configuration as a cell family. -/
def toCellFamily (C : OQP27.QConfig d M) : CellFamily d M where
  Q := C.Q
  proj := C.isProj
  orth := qconfig_orth_d C
  siteSum := qconfig_siteSum C

end Config

/-! ### The cell inequality for one family -/

section OneFamily

variable {d M : ℕ} [NeZero d] {ell : ℕ → ℝ}

omit [NeZero d] in
lemma ell_mod_eq (x : ℕ) : ell (x % d) = ell ((resid d (x : ZMod (4 * d))).val) := by
  rw [resid_natCast, ZMod.val_natCast]

lemma sum_ell_zmod (hl : IsConeCell d ell) : ∑ k : ZMod d, ell k.val = d := by
  rw [← sum_range_eq_sum_zmod d (fun k => ell k.val), ← hl.2]
  apply Finset.sum_congr rfl
  intro k hk
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.1 hk)]

/-- Operator constraint for `B_x = Q_{x+d}` on the cell partition. -/
lemma cell_op_B (hl : IsPosConeCell d ell) (F : CellFamily d M) :
    ∑ x ∈ Finset.range (4 * d), (((((cellPartition hl).t (x + 1) - (cellPartition hl).t x) /
      (2 * π)) : ℝ) : ℂ) • F.Q ((x : ZMod (4 * d)) + d) = ((1 / 4 : ℝ) : ℂ) • 1 := by
  simp only [cellPartition_len, ell_mod_eq]
  rw [sum_range_eq_sum_zmod (4 * d)
    (fun z => ((ell (resid d z).val / (4 * d) : ℝ) : ℂ) • F.Q (z + d))]
  rw [← Equiv.sum_comp (Equiv.subRight (d : ZMod (4 * d)))]
  simp only [Equiv.subRight_apply, sub_add_cancel, map_sub, resid_self, sub_zero]
  rw [F.siteSum (fun k => ((ell k.val / (4 * d) : ℝ) : ℂ))]
  congr 1
  rw [← Complex.ofReal_sum, ← Finset.sum_div, sum_ell_zmod hl.1]
  have := d_pos (d := d)
  congr 1
  field_simp

/-- `∑_x |J_x| Re Tr Q_x = (π/2) M`. -/
lemma cell_trace_A (hl : IsPosConeCell d ell) (F : CellFamily d M) :
    ∑ x ∈ Finset.range (4 * d), ((cellPartition hl).t (x + 1) - (cellPartition hl).t x) *
      (F.Q (x : ZMod (4 * d))).trace.re = π / 2 * M := by
  have hlen : ∀ x, (cellPartition hl).t (x + 1) - (cellPartition hl).t x =
      2 * π * (ell (x % d) / (4 * d)) := by
    intro x
    have := cellPartition_len hl x
    have hπ := Real.pi_pos
    field_simp at this ⊢
    linarith
  simp only [hlen, ell_mod_eq]
  rw [sum_range_eq_sum_zmod (4 * d)
    (fun z => 2 * π * (ell (resid d z).val / (4 * d)) * (F.Q z).trace.re)]
  have h1 : ∑ z : ZMod (4 * d), 2 * π * (ell (resid d z).val / (4 * d)) * (F.Q z).trace.re =
      (Matrix.trace (∑ z : ZMod (4 * d),
        (((2 * π * (ell (resid d z).val / (4 * d))) : ℝ) : ℂ) • F.Q z)).re := by
    rw [Matrix.trace_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  rw [h1, F.siteSum (fun k => ((2 * π * (ell k.val / (4 * d)) : ℝ) : ℂ)), trace_smul, trace_one,
    Fintype.card_fin, smul_eq_mul, ← Complex.ofReal_sum]
  rw [show ∑ k : ZMod d, 2 * π * (ell k.val / (4 * d)) = 2 * π * ((∑ k : ZMod d, ell k.val) / (4 * d)) by
    rw [← Finset.mul_sum, Finset.sum_div], sum_ell_zmod hl.1]
  have := d_pos (d := d)
  rw [Complex.re_ofReal_mul, Complex.natCast_re]
  field_simp
  ring

/-- **The cell inequality for one family** (QD2-L1 before rotation averaging):
`∑_{x,y} K^ℓ(x,y) Re Tr(Q_x Q_{y+d}) ≤ N² M Cl₂(π/2)/π²`. -/
theorem cellFamily_ineq (hl : IsPosConeCell d ell) (F : CellFamily d M)
    {h : ℂ → ℝ} (hharm : InnerProductSpace.HarmonicOnNhd h strip)
    (hcont : ContinuousOn h cstrip) {C : ℝ} (hC : 0 ≤ C)
    (hgrowth : ∀ w ∈ cstrip, |h w| ≤ C * (1 + ‖w‖))
    (hleft : ∀ y : ℝ, h ((y : ℂ) * I) = max (y - lamStar) 0)
    (hright : ∀ y : ℝ, h (1 + (y : ℂ) * I) = 0) (hstar : StarAt M h lamStar) :
    ∑ x : ZMod (4 * d), ∑ y : ZMod (4 * d),
      cellPairKernel d ell x.val y.val * (F.Q x * F.Q (y + d)).trace.re ≤
        (4 * d) ^ 2 * M * clausen2 (π / 2) / π ^ 2 := by
  set P := cellPartition hl
  have hineq := stepField_ineq P (fun x => F.Q (x : ZMod (4 * d)))
    (fun x => F.Q ((x : ZMod (4 * d)) + d)) (fun x => F.proj _) (fun x => F.proj _)
    (fun x => F.orth _) (by norm_num) (by norm_num) (cell_op_B hl F) hharm hcont hC hgrowth hstar
  have hw := window_value hharm hcont hC hgrowth hleft hright
  rw [cell_trace_A hl F] at hineq
  have hπ := Real.pi_pos
  have hd := d_pos (d := d)
  -- `∑ κ Re Tr ≤ 2 M Cl₂(π/2)`
  have hκ : ∑ x ∈ Finset.range (4 * d), ∑ y ∈ Finset.range (4 * d),
      arcKernel P x y * (F.Q (x : ZMod (4 * d)) * F.Q ((y : ZMod (4 * d)) + d)).trace.re ≤
        2 * M * clausen2 (π / 2) := by
    have h2 : lamStar * (π / 2 * M) = 2 * π * (M * (lamStar / 4)) := by ring
    have h3 : 2 * π * (M * h ((1 / 4 : ℝ) : ℂ)) + 2 * π * (M * (lamStar / 4)) =
        2 * π * M * (clausen2 (π / 2) / π ^ 2) := by
      rw [← hw]
      ring
    have h4 : 2 * π * M * (clausen2 (π / 2) / π ^ 2) = 2 * M * clausen2 (π / 2) / π := by
      field_simp
    rw [div_sub' (ne_of_gt hπ), div_le_iff₀ hπ] at hineq
    have h5 : 2 * π * M * (clausen2 (π / 2) / π ^ 2) * π = 2 * M * clausen2 (π / 2) := by
      field_simp
    nlinarith
  -- convert to the cell-pair kernel and to sums over `ℤ_N`
  have hconv : ∑ x : ZMod (4 * d), ∑ y : ZMod (4 * d),
      cellPairKernel d ell x.val y.val * (F.Q x * F.Q (y + d)).trace.re =
        (4 * d) ^ 2 / (2 * π ^ 2) * ∑ x ∈ Finset.range (4 * d), ∑ y ∈ Finset.range (4 * d),
          arcKernel P x y * (F.Q (x : ZMod (4 * d)) * F.Q ((y : ZMod (4 * d)) + d)).trace.re := by
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
  rw [hconv]
  calc (4 * d) ^ 2 / (2 * π ^ 2) * ∑ x ∈ Finset.range (4 * d), ∑ y ∈ Finset.range (4 * d),
        arcKernel P x y * (F.Q (x : ZMod (4 * d)) * F.Q ((y : ZMod (4 * d)) + d)).trace.re
      ≤ (4 * d) ^ 2 / (2 * π ^ 2) * (2 * M * clausen2 (π / 2)) :=
        mul_le_mul_of_nonneg_left hκ (by positivity)
    _ = (4 * d) ^ 2 * M * clausen2 (π / 2) / π ^ 2 := by
        field_simp

end OneFamily

/-! ### Symmetries of the cell-pair kernel -/

/-- Rotating the summation index of a `d`-periodic function. -/
lemma sum_range_shift_periodic {d : ℕ} (f : ℕ → ℝ) (hf : ∀ i, f (i + d) = f i) (n : ℕ) :
    ∑ i ∈ Finset.range d, f (n + i) = ∑ i ∈ Finset.range d, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := Finset.sum_range_succ' (fun i => f (n + i)) d
    have h2 := Finset.sum_range_succ (fun i => f (n + i)) d
    simp only [add_zero] at h1 h2
    rw [← ih]
    have e : ∀ i, f (n + 1 + i) = f (n + (i + 1)) := fun i => by rw [add_assoc, add_comm 1 i]
    simp_rw [e]
    rw [hf n] at h2
    have := h1.symm.trans h2
    exact add_right_cancel this

section Kernel

variable {d : ℕ} [NeZero d] {ell : ℕ → ℝ}

lemma coneG_add_N (u : ℝ) : coneG d (u + 4 * d) = coneG d u := by
  unfold coneG
  have hd := d_pos (d := d)
  congr 1
  rw [show 2 * π * (u + 4 * d) / (4 * d) = 2 * π * u / (4 * d) + 2 * π by field_simp,
    clausen2_add_two_pi]

lemma coneG_sub_N (u : ℝ) : coneG d (u - 4 * d) = coneG d u := by
  rw [← coneG_add_N (u - 4 * d), sub_add_cancel]

omit [NeZero d] in
lemma coneG_neg (u : ℝ) : coneG d (-u) = -coneG d u := by
  unfold coneG
  rw [show 2 * π * (-u) / (4 * d) = -(2 * π * u / (4 * d)) by ring, clausen2_neg]
  ring

lemma cellPairKernel_add_N_left (hl : IsConeCell d ell) (x y : ℕ) :
    cellPairKernel d ell (x + 4 * d) y = cellPairKernel d ell x y := by
  unfold cellPairKernel
  rw [show x + 4 * d + 1 = (x + 1) + 4 * d by ring, cellBoundary_add_N hl, cellBoundary_add_N hl]
  simp only [show ∀ a b : ℝ, a + 4 * d - b = (a - b) + 4 * d from fun a b => by ring, coneG_add_N]

lemma cellPairKernel_add_N_right (hl : IsConeCell d ell) (x y : ℕ) :
    cellPairKernel d ell x (y + 4 * d) = cellPairKernel d ell x y := by
  unfold cellPairKernel
  rw [show y + 4 * d + 1 = (y + 1) + 4 * d by ring, cellBoundary_add_N hl, cellBoundary_add_N hl]
  simp only [show ∀ a b : ℝ, a - (b + 4 * d) = (a - b) - 4 * d from fun a b => by ring, coneG_sub_N]

omit [NeZero d] in
lemma cellPairKernel_add_d (hl : IsConeCell d ell) (x y : ℕ) :
    cellPairKernel d ell (x + d) (y + d) = cellPairKernel d ell x y := by
  unfold cellPairKernel
  rw [show x + d + 1 = (x + 1) + d by ring, show y + d + 1 = (y + 1) + d by ring]
  simp only [cellBoundary_add_period hl]
  simp only [show ∀ a b : ℝ, a + d - (b + d) = a - b from fun a b => by ring]

omit [NeZero d] in
lemma cellPairKernel_swap (x y : ℕ) : cellPairKernel d ell y x = -cellPairKernel d ell x y := by
  unfold cellPairKernel
  have e : ∀ a b : ℝ, coneG d (a - b) = -coneG d (b - a) := by
    intro a b
    rw [← coneG_neg, neg_sub]
  rw [e (cellBoundary d ell (y + 1)) (cellBoundary d ell x),
    e (cellBoundary d ell y) (cellBoundary d ell x),
    e (cellBoundary d ell (y + 1)) (cellBoundary d ell (x + 1)),
    e (cellBoundary d ell y) (cellBoundary d ell (x + 1))]
  ring

lemma cellPairKernel_mod_left (hl : IsConeCell d ell) (x y : ℕ) :
    cellPairKernel d ell (x % (4 * d)) y = cellPairKernel d ell x y := by
  conv_rhs => rw [← Nat.mod_add_div x (4 * d)]
  generalize x / (4 * d) = k
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, ← add_assoc, cellPairKernel_add_N_left hl, ih]

lemma cellPairKernel_mod_right (hl : IsConeCell d ell) (x y : ℕ) :
    cellPairKernel d ell x (y % (4 * d)) = cellPairKernel d ell x y := by
  conv_rhs => rw [← Nat.mod_add_div y (4 * d)]
  generalize y / (4 * d) = k
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, ← add_assoc, cellPairKernel_add_N_right hl, ih]

lemma cellPairKernel_congr (hl : IsConeCell d ell) {x x' y y' : ℕ}
    (hx : (x : ZMod (4 * d)) = x') (hy : (y : ZMod (4 * d)) = y') :
    cellPairKernel d ell x y = cellPairKernel d ell x' y' := by
  rw [ZMod.natCast_eq_natCast_iff'] at hx hy
  rw [← cellPairKernel_mod_left hl, ← cellPairKernel_mod_right hl, hx, hy,
    cellPairKernel_mod_left hl, cellPairKernel_mod_right hl]

/-- Rotation average of the kernel along a diagonal: `∑_{c<d} K(x+c, y+c) = d K̃(x - y)`. -/
lemma sum_kernel_diag (hl : IsConeCell d ell) (x y : ZMod (4 * d)) :
    ∑ c ∈ Finset.range d, cellPairKernel d ell (x.val + c) (y.val + c) =
      d * cellKernelAvg d ell (x - y).val := by
  set n := (x - y).val with hn
  have hrw : ∀ c, cellPairKernel d ell (x.val + c) (y.val + c) =
      cellPairKernel d ell (y.val + c + n) (y.val + c) := by
    intro c
    apply cellPairKernel_congr hl _ rfl
    push_cast
    simp only [hn, ZMod.natCast_val, ZMod.cast_id', id]
    ring
  simp_rw [hrw]
  unfold cellKernelAvg
  have hd := d_pos (d := d)
  rw [mul_div_cancel₀ _ hd.ne']
  have hper : ∀ r, cellPairKernel d ell (r + d + n) (r + d) = cellPairKernel d ell (r + n) r := by
    intro r
    rw [show r + d + n = (r + n) + d by ring, cellPairKernel_add_d hl]
  exact sum_range_shift_periodic (fun r => cellPairKernel d ell (r + n) r) hper y.val

omit [NeZero d] in
lemma cellKernelAvg_zero : cellKernelAvg d ell 0 = 0 := by
  unfold cellKernelAvg
  have : ∀ r, cellPairKernel d ell r r = 0 := by
    intro r
    have := cellPairKernel_swap (d := d) (ell := ell) r r
    linarith
  simp [this]

lemma cellKernelAvg_reflect (hl : IsConeCell d ell) {n : ℕ} (hn : n ≤ 4 * d) :
    cellKernelAvg d ell (4 * d - n) = -cellKernelAvg d ell n := by
  unfold cellKernelAvg
  rw [← neg_div, ← Finset.sum_neg_distrib]
  congr 1
  have h1 : ∀ r, cellPairKernel d ell (r + (4 * d - n)) r =
      -cellPairKernel d ell (4 * d - n + r + n) (4 * d - n + r) := by
    intro r
    rw [cellPairKernel_swap, show 4 * d - n + r + n = r + 4 * d by omega,
      cellPairKernel_add_N_left hl, show 4 * d - n + r = r + (4 * d - n) by ring]
  simp_rw [h1]
  rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib]
  congr 1
  have hper : ∀ r, cellPairKernel d ell (r + d + n) (r + d) = cellPairKernel d ell (r + n) r := by
    intro r
    rw [show r + d + n = (r + n) + d by ring, cellPairKernel_add_d hl]
  exact sum_range_shift_periodic (fun r => cellPairKernel d ell (r + n) r) hper (4 * d - n)

lemma cellKernelAvg_two_d (hl : IsConeCell d ell) : cellKernelAvg d ell (2 * d) = 0 := by
  have := cellKernelAvg_reflect hl (n := 2 * d) (by omega)
  rw [show 4 * d - 2 * d = 2 * d by omega] at this
  linarith

end Kernel

/-! ### Folding sums over `ℤ_{4d}` -/

section Folding

lemma sum_Ico_fold (d : ℕ) (g : ℕ → ℝ) (hd : 1 ≤ d) :
    ∑ m ∈ Finset.Ico 1 (2 * d), g m = ∑ m ∈ Finset.Ico 1 d, (g m + g (2 * d - m)) + g d := by
  rw [Finset.sum_add_distrib, ← Finset.sum_Ico_consecutive _ hd (by omega : d ≤ 2 * d),
    Finset.sum_eq_sum_Ico_succ_bot (by omega : d < 2 * d)]
  have hr : ∑ m ∈ Finset.Ico 1 d, g (2 * d - m) = ∑ m ∈ Finset.Ico (d + 1) (2 * d), g m := by
    rw [Finset.sum_Ico_reflect g 1 (by omega : d ≤ 2 * d + 1),
      show 2 * d + 1 - d = d + 1 by omega, show 2 * d + 1 - 1 = 2 * d by omega]
  rw [hr]
  ring

lemma sum_range_four_fold (d : ℕ) (g h : ℕ → ℝ) (hd : 1 ≤ d) (hg0 : g 0 = 0) (hg2 : g (2 * d) = 0)
    (hrefl : ∀ j, 1 ≤ j → j < 2 * d → g (4 * d - j) = h j) :
    ∑ n ∈ Finset.range (4 * d), g n = ∑ j ∈ Finset.Ico 1 (2 * d), (g j + h j) := by
  rw [show 4 * d = 2 * d + 2 * d by ring, Finset.sum_range_add, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < 2 * d), hg0, zero_add]
  · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < 2 * d), add_zero, hg2,
      zero_add]
    have h1 : ∀ n ∈ Finset.Ico 1 (2 * d), g (2 * d + n) = h (2 * d - n) := by
      intro n hn
      rw [Finset.mem_Ico] at hn
      rw [← hrefl (2 * d - n) (by omega) (by omega)]
      congr 1
      omega
    rw [Finset.sum_congr rfl h1, Finset.sum_Ico_reflect h 1 (by omega : 2 * d ≤ 2 * d + 1),
      show 2 * d + 1 - 2 * d = 1 by omega, show 2 * d + 1 - 1 = 2 * d by omega]

/-- `∑_{m=1}^{K} m Δ²P(m) = K (P(K+1) - P(K)) - (P(K) - P(0))` (summation by parts). -/
lemma sum_mul_second_diff (P : ℕ → ℝ) (K : ℕ) :
    ∑ m ∈ Finset.Ico 1 (K + 1), (m : ℝ) * (P (m + 1) - 2 * P m + P (m - 1)) =
      K * (P (K + 1) - P K) - (P K - P 0) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ K + 1), ih]
    simp only [Nat.add_sub_cancel]
    push_cast
    ring

end Folding

/-! ### The window identity (equality of every cell inequality at the windows) -/

section Window

variable {d : ℕ} [NeZero d] {ell : ℕ → ℝ}

/-- `P(k) = (1/d) ∑_{r<d} G(L_{r+k} - L_r)` (the window-sum potential of QD2-L2). -/
noncomputable def winPot (d : ℕ) (ell : ℕ → ℝ) (k : ℕ) : ℝ :=
  (∑ r ∈ Finset.range d, coneG d (cellBoundary d ell (r + k) - cellBoundary d ell r)) / d

omit [NeZero d] in
lemma winPot_shift (hl : IsConeCell d ell) (k s : ℕ) :
    ∑ r ∈ Finset.range d, coneG d (cellBoundary d ell (s + r + k) - cellBoundary d ell (s + r)) =
      ∑ r ∈ Finset.range d, coneG d (cellBoundary d ell (r + k) - cellBoundary d ell r) := by
  have hper : ∀ r, coneG d (cellBoundary d ell (r + d + k) - cellBoundary d ell (r + d)) =
      coneG d (cellBoundary d ell (r + k) - cellBoundary d ell r) := by
    intro r
    rw [show r + d + k = (r + k) + d by ring, cellBoundary_add_period hl, cellBoundary_add_period hl]
    ring_nf
  have := sum_range_shift_periodic
    (fun r => coneG d (cellBoundary d ell (r + k) - cellBoundary d ell r)) hper s
  simpa [add_assoc] using this

omit [NeZero d] in
/-- `K̃(n) = P(n+1) - 2P(n) + P(n-1)` for `n ≥ 1`. -/
lemma kernelAvg_second_diff (hl : IsConeCell d ell) {n : ℕ} (hn : 1 ≤ n) :
    cellKernelAvg d ell n = winPot d ell (n + 1) - 2 * winPot d ell n + winPot d ell (n - 1) := by
  unfold cellKernelAvg winPot cellPairKernel
  have h3 := winPot_shift hl n 1
  have h4 := winPot_shift hl (n - 1) 1
  have e3 : ∀ r, cellBoundary d ell (r + n + 1) - cellBoundary d ell (r + 1) =
      cellBoundary d ell (1 + r + n) - cellBoundary d ell (1 + r) := by
    intro r
    rw [show r + n + 1 = 1 + r + n by ring, show r + 1 = 1 + r by ring]
  have e4 : ∀ r, cellBoundary d ell (r + n) - cellBoundary d ell (r + 1) =
      cellBoundary d ell (1 + r + (n - 1)) - cellBoundary d ell (1 + r) := by
    intro r
    rw [show 1 + r + (n - 1) = r + n by omega, show r + 1 = 1 + r by ring]
  have e1 : ∀ r, cellBoundary d ell (r + n + 1) - cellBoundary d ell r =
      cellBoundary d ell (r + (n + 1)) - cellBoundary d ell r := by
    intro r
    rw [show r + n + 1 = r + (n + 1) by ring]
  simp only [e1, e3, e4]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, h3, h4]
  ring

omit [NeZero d] in
lemma window_sum_d (hl : IsConeCell d ell) (r : ℕ) :
    cellBoundary d ell (r + d) - cellBoundary d ell r = d := by
  rw [cellBoundary_add_period hl]
  ring

omit [NeZero d] in
lemma window_sum_two_d (hl : IsConeCell d ell) (r : ℕ) :
    cellBoundary d ell (r + 2 * d) - cellBoundary d ell r = 2 * d := by
  rw [show r + 2 * d = r + d + d by ring, cellBoundary_add_period hl, cellBoundary_add_period hl]
  ring

omit [NeZero d] in
lemma winPot_zero : winPot d ell 0 = 0 := by
  unfold winPot coneG
  simp [clausen2_zero]

lemma winPot_d (hl : IsConeCell d ell) : winPot d ell d = coneG d d := by
  unfold winPot
  simp only [window_sum_d hl, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have := d_pos (d := d)
  field_simp

lemma winPot_two_d (hl : IsConeCell d ell) : winPot d ell (2 * d) = 0 := by
  unfold winPot
  simp only [window_sum_two_d hl]
  unfold coneG
  have := d_pos (d := d)
  rw [show 2 * π * (2 * (d : ℝ)) / (4 * d) = π by field_simp; ring, clausen2_pi]
  simp

/-- **The window identity**: `∑_{m=1}^{d-1} u^ℓ_m m + d K̃(d) = N² Cl₂(π/2)/π²` (the value of every
cell functional on the DKZ windows). -/
theorem window_identity (hl : IsConeCell d ell) :
    ∑ m ∈ Finset.Ico 1 d, cellDirection d ell m * m + d * cellKernelAvg d ell d =
      (4 * d) ^ 2 * clausen2 (π / 2) / π ^ 2 := by
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  set P := winPot d ell with hP
  set Q : ℕ → ℝ := fun j => P (2 * d - j) with hQ
  have hIco : Finset.Ico 1 d = Finset.Ico 1 (d - 1 + 1) := by
    rw [Nat.sub_add_cancel hd1]
  have hA : ∑ m ∈ Finset.Ico 1 d, (m : ℝ) * cellKernelAvg d ell m =
      (d - 1 : ℕ) * (P (d - 1 + 1) - P (d - 1)) - (P (d - 1) - P 0) := by
    rw [← sum_mul_second_diff P (d - 1), ← hIco]
    apply Finset.sum_congr rfl
    intro m hm
    rw [kernelAvg_second_diff hl (Finset.mem_Ico.1 hm).1]
  have hB : ∑ m ∈ Finset.Ico 1 d, (m : ℝ) * cellKernelAvg d ell (2 * d - m) =
      (d - 1 : ℕ) * (Q (d - 1 + 1) - Q (d - 1)) - (Q (d - 1) - Q 0) := by
    rw [← sum_mul_second_diff Q (d - 1), ← hIco]
    apply Finset.sum_congr rfl
    intro m hm
    have hm' := Finset.mem_Ico.1 hm
    rw [kernelAvg_second_diff hl (by omega : 1 ≤ 2 * d - m)]
    simp only [hQ]
    rw [show 2 * d - m + 1 = 2 * d - (m - 1) by omega, show 2 * d - m - 1 = 2 * d - (m + 1) by omega]
    ring
  have hC : (d : ℝ) * cellKernelAvg d ell d = d * (P (d + 1) - 2 * P d + P (d - 1)) := by
    rw [kernelAvg_second_diff hl hd1]
  have hsplit : ∑ m ∈ Finset.Ico 1 d, cellDirection d ell m * m =
      ∑ m ∈ Finset.Ico 1 d, (m : ℝ) * cellKernelAvg d ell m +
        ∑ m ∈ Finset.Ico 1 d, (m : ℝ) * cellKernelAvg d ell (2 * d - m) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    unfold cellDirection
    ring
  rw [hsplit, hA, hB, hC]
  simp only [hQ, Nat.sub_add_cancel hd1, hP]
  rw [show 2 * d - d = d by omega, show 2 * d - (d - 1) = d + 1 by omega, Nat.sub_zero,
    winPot_zero, winPot_two_d hl, winPot_d hl]
  have hcast : ((d - 1 : ℕ) : ℝ) = d - 1 := by
    rw [Nat.cast_sub hd1, Nat.cast_one]
  rw [hcast]
  unfold coneG
  have := d_pos (d := d)
  have hπ := Real.pi_pos
  rw [show 2 * π * (d : ℝ) / (4 * d) = π / 2 by field_simp; ring]
  field_simp
  ring

end Window

/-! ### Rotation averaging and the cell inequality for positive cells -/

section Average

variable {d M : ℕ} [NeZero d] {ell : ℕ → ℝ}

lemma double_sum_shift (f : ZMod (4 * d) → ZMod (4 * d) → ℝ) (c : ZMod (4 * d)) :
    ∑ x, ∑ y, f x y = ∑ x, ∑ y, f (x + c) (y + c) := by
  rw [← Equiv.sum_comp (Equiv.addRight c)]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Equiv.sum_comp (Equiv.addRight c)]
  rfl

lemma netCount_reflect (C : OQP27.QConfig d M) {m : ℕ} (hm : m ≤ 2 * d) :
    C.netCount ((2 * d - m : ℕ) : ZMod (4 * d)) = C.netCount (m : ZMod (4 * d)) := by
  rw [OQP27.QConfig.netCount_eq_corr, OQP27.QConfig.netCount_eq_corr, Nat.cast_sub hm]
  have e1 : ((2 * d : ℕ) : ZMod (4 * d)) - m - d = -((m : ZMod (4 * d)) - d) := by
    push_cast
    ring
  have e2 : ((2 * d : ℕ) : ZMod (4 * d)) - m + d = -((m : ZMod (4 * d)) + d) := by
    have h4 : ((4 * d : ℕ) : ZMod (4 * d)) = 0 := ZMod.natCast_self _
    push_cast at h4 ⊢
    linear_combination h4
  rw [e1, e2, OQP27.QConfig.corr_neg, OQP27.QConfig.corr_neg]

lemma netCount_d (C : OQP27.QConfig d M) (hM : 0 < M) :
    C.netCount (d : ZMod (4 * d)) = d := by
  rw [OQP27.QConfig.netCount_eq_corr, sub_self]
  have h0 : C.corr 0 = d := by
    unfold OQP27.QConfig.corr
    have hproj : ∀ u, C.Q u * C.Q (u + 0) = C.Q u := fun u => by rw [add_zero, (C.isProj u).2]
    simp only [hproj]
    rw [← Finset.sum_div]
    have hs := qconfig_siteSum C (fun _ => 1)
    simp only [one_smul, Finset.sum_const, Finset.card_univ, ZMod.card] at hs
    have htr : ∑ u : ZMod (4 * d), (C.Q u).trace.re = (Matrix.trace (∑ u, C.Q u)).re := by
      rw [Matrix.trace_sum, Complex.re_sum]
    rw [htr, hs, trace_smul, trace_one, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul]
    have hMr : (0 : ℝ) < M := Nat.cast_pos.2 hM
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero]
    field_simp
    simp
  have h2 : C.corr ((d : ZMod (4 * d)) + d) = 0 := by
    unfold OQP27.QConfig.corr
    apply Finset.sum_eq_zero
    intro u _
    rw [show (d : ZMod (4 * d)) + d = 2 * d by ring, qconfig_orth_2d C u]
    simp
  rw [h0, h2, sub_zero]

/-- The rotation-averaged cell inequality in pair-count form:
`∑_{n ∈ ℤ_N} K̃(n) T(n) ≤ N² Cl₂(π/2)/π²`. -/
theorem averaged_ineq (hl : IsPosConeCell d ell) (C : OQP27.QConfig d M) (hM : 0 < M)
    {h : ℂ → ℝ} (hharm : InnerProductSpace.HarmonicOnNhd h strip)
    (hcont : ContinuousOn h cstrip) {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgrowth : ∀ w ∈ cstrip, |h w| ≤ Cg * (1 + ‖w‖))
    (hleft : ∀ y : ℝ, h ((y : ℂ) * I) = max (y - lamStar) 0)
    (hright : ∀ y : ℝ, h (1 + (y : ℂ) * I) = 0) (hstar : StarAt M h lamStar) :
    ∑ n : ZMod (4 * d), cellKernelAvg d ell n.val * C.pairCount n ≤
      (4 * d) ^ 2 * clausen2 (π / 2) / π ^ 2 := by
  set F := toCellFamily C
  set G : ZMod (4 * d) → ZMod (4 * d) → ℝ := fun x y => (C.Q x * C.Q (y + d)).trace.re with hG
  set Φ : ℝ := (4 * d) ^ 2 * M * clausen2 (π / 2) / π ^ 2 with hΦ
  have hrot : ∀ c : ℕ, ∑ x : ZMod (4 * d), ∑ y : ZMod (4 * d),
      cellPairKernel d ell (x.val + c) (y.val + c) * G x y ≤ Φ := by
    intro c
    have h1 := cellFamily_ineq hl (F.rot (c : ZMod (4 * d))) hharm hcont hCg hgrowth hleft hright
      hstar
    rw [double_sum_shift _ (c : ZMod (4 * d))] at h1
    convert h1 using 3 with x _ y _
    simp only [CellFamily.rot, F, toCellFamily, add_sub_cancel_right, hG]
    rw [show y + (c : ZMod (4 * d)) + d - c = y + d by ring]
    congr 1
    apply cellPairKernel_congr hl.1 <;> simp
  have hsum : ∑ c ∈ Finset.range d, ∑ x : ZMod (4 * d), ∑ y : ZMod (4 * d),
      cellPairKernel d ell (x.val + c) (y.val + c) * G x y ≤ d * Φ := by
    calc _ ≤ ∑ c ∈ Finset.range d, Φ := Finset.sum_le_sum fun c _ => hrot c
      _ = d * Φ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hswap : ∑ c ∈ Finset.range d, ∑ x : ZMod (4 * d), ∑ y : ZMod (4 * d),
      cellPairKernel d ell (x.val + c) (y.val + c) * G x y =
        d * ∑ x : ZMod (4 * d), ∑ y : ZMod (4 * d), cellKernelAvg d ell (x - y).val * G x y := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [← Finset.sum_mul, sum_kernel_diag hl.1 x y]
    ring
  have hpair : ∑ x : ZMod (4 * d), ∑ y : ZMod (4 * d), cellKernelAvg d ell (x - y).val * G x y =
      M * ∑ n : ZMod (4 * d), cellKernelAvg d ell n.val * C.pairCount n := by
    rw [Finset.sum_comm]
    have h1 : ∀ y : ZMod (4 * d), ∑ x : ZMod (4 * d), cellKernelAvg d ell (x - y).val * G x y =
        ∑ n : ZMod (4 * d), cellKernelAvg d ell n.val * G (y + n) y := by
      intro y
      rw [← Equiv.sum_comp (Equiv.addLeft y)]
      apply Finset.sum_congr rfl
      intro n _
      simp only [Equiv.coe_addLeft, add_sub_cancel_left]
    simp_rw [h1]
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [← Finset.mul_sum]
    unfold OQP27.QConfig.pairCount
    have hMr : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
    rw [← Finset.sum_div]
    simp only [hG]
    field_simp
  rw [hswap, hpair] at hsum
  have hd := d_pos (d := d)
  have hMr : (0 : ℝ) < M := Nat.cast_pos.2 hM
  rw [hΦ] at hsum
  have : (d : ℝ) * M * ∑ n : ZMod (4 * d), cellKernelAvg d ell n.val * C.pairCount n ≤
      (d * M) * ((4 * d) ^ 2 * clausen2 (π / 2) / π ^ 2) := by
    have e : (d : ℝ) * ((4 * d) ^ 2 * M * clausen2 (π / 2) / π ^ 2) =
        (d * M) * ((4 * d) ^ 2 * clausen2 (π / 2) / π ^ 2) := by ring
    rw [← e]
    nlinarith
  exact le_of_mul_le_mul_left this (by positivity)

/-- Folding the averaged sum: `∑_n K̃(n) T(n) = ⟨u^ℓ, N⟩ + K̃(d) N(d)`. -/
lemma fold_pairCount (hl : IsConeCell d ell) (C : OQP27.QConfig d M) :
    ∑ n : ZMod (4 * d), cellKernelAvg d ell n.val * C.pairCount n =
      ∑ m ∈ Finset.Ico 1 d, cellDirection d ell m * C.netCount (m : ZMod (4 * d)) +
        cellKernelAvg d ell d * C.netCount (d : ZMod (4 * d)) := by
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (NeZero.ne d)
  rw [← sum_range_eq_sum_zmod (4 * d) (fun n => cellKernelAvg d ell n.val * C.pairCount n)]
  have hval : ∀ n ∈ Finset.range (4 * d), cellKernelAvg d ell ((n : ZMod (4 * d))).val *
      C.pairCount (n : ZMod (4 * d)) = cellKernelAvg d ell n * C.pairCount (n : ZMod (4 * d)) := by
    intro n hn
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.1 hn)]
  rw [Finset.sum_congr rfl hval]
  rw [sum_range_four_fold d (fun n => cellKernelAvg d ell n * C.pairCount (n : ZMod (4 * d)))
    (fun j => -(cellKernelAvg d ell j * C.pairCount (-(j : ZMod (4 * d))))) hd1
    (by rw [cellKernelAvg_zero, zero_mul])
    (by rw [cellKernelAvg_two_d hl, zero_mul])]
  · have h2 : ∀ j ∈ Finset.Ico 1 (2 * d), cellKernelAvg d ell j * C.pairCount (j : ZMod (4 * d)) +
        -(cellKernelAvg d ell j * C.pairCount (-(j : ZMod (4 * d)))) =
        cellKernelAvg d ell j * C.netCount (j : ZMod (4 * d)) := by
      intro j _
      unfold OQP27.QConfig.netCount
      ring
    rw [Finset.sum_congr rfl h2, sum_Ico_fold d _ hd1]
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    have hm' := Finset.mem_Ico.1 hm
    rw [netCount_reflect C (by omega : m ≤ 2 * d)]
    unfold cellDirection
    ring
  · intro j hj1 hj2
    rw [cellKernelAvg_reflect hl (by omega : j ≤ 4 * d), Nat.cast_sub (by omega : j ≤ 4 * d)]
    have h4 : ((4 * d : ℕ) : ZMod (4 * d)) = 0 := ZMod.natCast_self _
    rw [h4, zero_sub]
    ring

/-- **QD2-L1 for positive cell vectors**: `⟨u^ℓ, δ⟩ ≤ 0`. -/
theorem cellIneq_pos (hl : IsPosConeCell d ell) (C : OQP27.QConfig d M) (hM : 0 < M)
    {h : ℂ → ℝ} (hharm : InnerProductSpace.HarmonicOnNhd h strip)
    (hcont : ContinuousOn h cstrip) {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgrowth : ∀ w ∈ cstrip, |h w| ≤ Cg * (1 + ‖w‖))
    (hleft : ∀ y : ℝ, h ((y : ℂ) * I) = max (y - lamStar) 0)
    (hright : ∀ y : ℝ, h (1 + (y : ℂ) * I) = 0) (hstar : StarAt M h lamStar) :
    OQP27.pairingIco d (cellDirection d ell) C.delta ≤ 0 := by
  have hav := averaged_ineq hl C hM hharm hcont hCg hgrowth hleft hright hstar
  rw [fold_pairCount hl.1 C, netCount_d C hM] at hav
  have hw := window_identity hl.1 (d := d)
  unfold OQP27.pairingIco OQP27.QConfig.delta
  have e : ∑ m ∈ Finset.Ico 1 d, cellDirection d ell m * (C.netCount (m : ZMod (4 * d)) - m) =
      ∑ m ∈ Finset.Ico 1 d, cellDirection d ell m * C.netCount (m : ZMod (4 * d)) -
        ∑ m ∈ Finset.Ico 1 d, cellDirection d ell m * m := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [e]
  linarith

end Average

end OQP27.Cell
