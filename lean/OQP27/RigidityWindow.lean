import OQP27.RigidityMain

/-!
# OQP 27B rigidity, Step 1 (second half): the rotation identity (1.4) and the single cell inequalities
(module L6)

Paper: `iqoqi/programs/oqp27B_all/Q_rig/RIGIDITY_ALLD.md`, sections 1.5 and 2 (identity (1.4),
inequality (1.3), equation (2.1)); `iqoqi/programs/oqp27B_all/QD2/LOG.md` s.4 (QD2-L1, QD2-L2).

For a cell vector `ℓ ∈ Δ_d` and a 27B configuration `Q` on `ℂ^M` (module L1's `QConfig`) the cell
functional is `Q^ℓ(Q) = ∑_{x,y ∈ ℤ_N} K^ℓ(x,y) τ(A_x B_y)` (`OQP27.Rig.cellFunctional`), with module L1's
cell-pair kernel `K^ℓ` (`OQP27.cellPairKernel`, the double integral of `cot(π(ξ-η)/N)` over the cells
`I_x × I_y`, written with the second antiderivative `G`), and the window value is
`N² Φ_c(1/4, 1/4) = -2 G(d) = (N²/π²) Cl₂(π/2)` (`OQP27.Rig.windowValue`).

Proved here (no hypotheses):
* `OQP27.Rig.window_identity` (**identity (1.4)**): for every configuration and every cell vector,
  `(1/d) ∑_{c<d} [Q^ℓ(rot_c Q) - N² Φ_c] = ⟨u^ℓ, δ⟩` with `(rot_c Q)_x = Q_{x-c}`.
* `OQP27.Rig.cellInequalities_of_single`: the single cell inequalities (1.3) imply module L1's
  `Hyp_CellInequalities d` (QD2-L1).
* `OQP27.Rig.cellEqualityAE_of_continuum`: (1.3) and the equality analysis of the continuum theorem in
  its continuum form (`Q^ℓ(Q) = N² Φ_c` ⟹ `[B(θ), g(θ)] = 0` a.e., `Hyp_ContinuumEquality`) imply
  `Hyp_CellEqualityAE d` (`RIGIDITY_ALLD.md` s.2: every rotated cell inequality is tight).
* `OQP27.Rig.rigidity_all_d'`: Theorem R from (1.3), the continuum equality analysis, CONE_d with an
  all-positive cell vector, and the classical Theorem B; `OQP27.Rig.rigidity_all_d''`: the same with module
  L1's cell inequalities and (1.3) only for cell vectors with all cells positive.
* `OQP27.Rig.optimality_of_single`: optimality from (1.3) and CONE_d.

Hypotheses introduced (precise statements below): `OQP27.Rig.Hyp_CellIneqSingle d` and its positive-cell
form `OQP27.Rig.Hyp_CellIneqSinglePos d` ((1.3): Q-T1 for one cell-embedded step field, `RIGIDITY_ALLD.md`
s.3.1-3.6), and `OQP27.Rig.Hyp_ContinuumEquality d` (`RIGIDITY_ALLD.md` s.3.7, using the equality case of
the strip inequality; reduced further in `OQP27/RigidityStrip.lean`).
-/

set_option linter.unusedSectionVars false

open Complex Matrix Finset MeasureTheory

namespace OQP27.Rig

/-! ## The Clausen function and the antiderivative `G` -/

lemma clausen2_neg (θ : ℝ) : clausen2 (-θ) = -clausen2 θ := by
  unfold clausen2
  rw [← tsum_neg]
  congr 1
  funext k
  rw [mul_neg, Real.sin_neg, neg_div]

lemma clausen2_add_two_pi (θ : ℝ) : clausen2 (θ + 2 * Real.pi) = clausen2 θ := by
  unfold clausen2
  congr 1
  funext k
  congr 1
  rw [mul_add, show ((k : ℝ) + 1) * (2 * Real.pi) = ((k + 1 : ℕ) : ℝ) * (2 * Real.pi) by push_cast; ring,
    Real.sin_add_nat_mul_two_pi]

lemma clausen2_zero : clausen2 0 = 0 := by
  unfold clausen2
  simp

lemma clausen2_pi : clausen2 Real.pi = 0 := by
  unfold clausen2
  have h : ∀ k : ℕ, Real.sin (((k : ℝ) + 1) * Real.pi) = 0 := by
    intro k
    rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring]
    exact Real.sin_nat_mul_pi (k + 1)
  simp [h]

variable {d : ℕ} [NeZero d]

lemma four_d_ne_zero' : (4 * (d : ℝ)) ≠ 0 := by
  have : (0 : ℝ) < d := Nat.cast_pos.2 (NeZero.pos d)
  positivity

lemma coneG_neg (u : ℝ) : coneG d (-u) = -coneG d u := by
  unfold coneG
  rw [show 2 * Real.pi * -u / (4 * (d : ℝ)) = -(2 * Real.pi * u / (4 * (d : ℝ))) by ring,
    clausen2_neg]
  ring

lemma coneG_add_period (u : ℝ) : coneG d (u + 4 * d) = coneG d u := by
  unfold coneG
  have h : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  rw [show 2 * Real.pi * (u + 4 * (d : ℝ)) / (4 * (d : ℝ))
      = 2 * Real.pi * u / (4 * (d : ℝ)) + 2 * Real.pi by field_simp, clausen2_add_two_pi]

lemma coneG_zero : coneG d 0 = 0 := by
  unfold coneG
  simp [clausen2_zero]

lemma coneG_two_d : coneG d (2 * d) = 0 := by
  unfold coneG
  have h : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  rw [show 2 * Real.pi * (2 * (d : ℝ)) / (4 * (d : ℝ)) = Real.pi by field_simp; ring, clausen2_pi,
    mul_zero]

/-! ## Invariances of the cell-pair kernel -/

variable {ell : ℕ → ℝ}

lemma cellBoundary_add_four_period (hl : IsConeCell d ell) (n : ℕ) :
    cellBoundary d ell (n + 4 * d) = cellBoundary d ell n + 4 * d := by
  have h := cellBoundary_add_period hl
  rw [show n + 4 * d = n + d + d + d + d by ring, h, h, h, h]
  ring

lemma cellPairKernel_add_add (hl : IsConeCell d ell) (a b : ℕ) :
    cellPairKernel d ell (a + d) (b + d) = cellPairKernel d ell a b := by
  have h := cellBoundary_add_period hl
  unfold cellPairKernel
  rw [show a + d + 1 = a + 1 + d by ring, show b + d + 1 = b + 1 + d by ring, h, h, h, h]
  ring_nf

lemma cellPairKernel_add_left (hl : IsConeCell d ell) (a b : ℕ) :
    cellPairKernel d ell (a + 4 * d) b = cellPairKernel d ell a b := by
  have h := cellBoundary_add_four_period hl
  unfold cellPairKernel
  rw [show a + 4 * d + 1 = a + 1 + 4 * d by ring, h, h]
  rw [show cellBoundary d ell (a + 1) + 4 * d - cellBoundary d ell b
      = (cellBoundary d ell (a + 1) - cellBoundary d ell b) + 4 * d by ring,
    show cellBoundary d ell a + 4 * d - cellBoundary d ell b
      = (cellBoundary d ell a - cellBoundary d ell b) + 4 * d by ring,
    show cellBoundary d ell (a + 1) + 4 * d - cellBoundary d ell (b + 1)
      = (cellBoundary d ell (a + 1) - cellBoundary d ell (b + 1)) + 4 * d by ring,
    show cellBoundary d ell a + 4 * d - cellBoundary d ell (b + 1)
      = (cellBoundary d ell a - cellBoundary d ell (b + 1)) + 4 * d by ring]
  simp only [coneG_add_period]

lemma cellPairKernel_antisymm (a b : ℕ) : cellPairKernel d ell a b = -cellPairKernel d ell b a := by
  unfold cellPairKernel
  rw [show cellBoundary d ell (b + 1) - cellBoundary d ell a
      = -(cellBoundary d ell a - cellBoundary d ell (b + 1)) by ring,
    show cellBoundary d ell b - cellBoundary d ell a
      = -(cellBoundary d ell a - cellBoundary d ell b) by ring,
    show cellBoundary d ell (b + 1) - cellBoundary d ell (a + 1)
      = -(cellBoundary d ell (a + 1) - cellBoundary d ell (b + 1)) by ring,
    show cellBoundary d ell b - cellBoundary d ell (a + 1)
      = -(cellBoundary d ell (a + 1) - cellBoundary d ell b) by ring]
  simp only [coneG_neg]
  ring

lemma cellPairKernel_add_right (hl : IsConeCell d ell) (a b : ℕ) :
    cellPairKernel d ell a (b + 4 * d) = cellPairKernel d ell a b := by
  rw [cellPairKernel_antisymm, cellPairKernel_add_left hl, ← cellPairKernel_antisymm]

lemma cellPairKernel_mod (hl : IsConeCell d ell) (a b : ℕ) :
    cellPairKernel d ell (a % (4 * d)) (b % (4 * d)) = cellPairKernel d ell a b := by
  have hL : ∀ q a' b', cellPairKernel d ell (a' + 4 * d * q) b' = cellPairKernel d ell a' b' := by
    intro q
    induction q with
    | zero => intro a' b'; simp
    | succ q ih =>
      intro a' b'
      rw [show a' + 4 * d * (q + 1) = a' + 4 * d * q + 4 * d by ring, cellPairKernel_add_left hl, ih]
  have hR : ∀ q a' b', cellPairKernel d ell a' (b' + 4 * d * q) = cellPairKernel d ell a' b' := by
    intro q a' b'
    rw [cellPairKernel_antisymm, hL, ← cellPairKernel_antisymm]
  conv_rhs => rw [← Nat.mod_add_div a (4 * d), ← Nat.mod_add_div b (4 * d)]
  rw [hL, hR]

lemma cellPairKernel_self (a : ℕ) : cellPairKernel d ell a a = 0 := by
  have h := cellPairKernel_antisymm (d := d) (ell := ell) a a
  linarith

/-! ## Rotation averages of the kernel -/

lemma zmod_val_add_natCast (z : ZMod (4 * d)) (c : ℕ) :
    (z + (c : ZMod (4 * d))).val = (z.val + c) % (4 * d) := by
  rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod]

/-- `∑_{c<d} K^ℓ(x + c, y + c) = ∑_{r<d} K^ℓ(r + n, r)`, `n = x - y` (the rotation average of the kernel
depends only on `x - y`). -/
lemma cellPairKernel_rot_sum (hl : IsConeCell d ell) (x y : ZMod (4 * d)) :
    ∑ c ∈ range d, cellPairKernel d ell (x + (c : ZMod (4 * d))).val (y + (c : ZMod (4 * d))).val
      = ∑ r ∈ range d, cellPairKernel d ell (r + (x - y).val) r := by
  simp_rw [zmod_val_add_natCast, cellPairKernel_mod hl]
  have hx : ∀ c : ℕ, cellPairKernel d ell (x.val + c) (y.val + c)
      = cellPairKernel d ell (y.val + c + (x - y).val) (y.val + c) := by
    intro c
    rw [← cellPairKernel_mod hl (x.val + c), ← cellPairKernel_mod hl (y.val + c + (x - y).val)]
    congr 1
    have h : ((x.val + c : ℕ) : ZMod (4 * d)) = ((y.val + c + (x - y).val : ℕ) : ZMod (4 * d)) := by
      push_cast
      simp only [ZMod.natCast_zmod_val]
      ring
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).1 h
  simp_rw [hx]
  have hper : ∀ i, cellPairKernel d ell (i + d + (x - y).val) (i + d)
      = cellPairKernel d ell (i + (x - y).val) i := by
    intro i
    rw [show i + d + (x - y).val = i + (x - y).val + d by ring, cellPairKernel_add_add hl]
  have h := cell_sum_range_rotate (fun i => cellPairKernel d ell (i + (x - y).val) i) hper y.val
  rw [← h]

/-- `K̃(4d - n) = -K̃(n)`. -/
lemma cellKernelAvg_reflect (hl : IsConeCell d ell) {n : ℕ} (hn : n ≤ 4 * d) :
    cellKernelAvg d ell (4 * d - n) = -cellKernelAvg d ell n := by
  unfold cellKernelAvg
  rw [← neg_div, ← Finset.sum_neg_distrib]
  congr 1
  have h1 : ∀ r, cellPairKernel d ell (r + (4 * d - n)) r
      = -cellPairKernel d ell (r + (4 * d - n) + n) (r + (4 * d - n)) := by
    intro r
    rw [cellPairKernel_antisymm, show r + (4 * d - n) + n = r + 4 * d by omega,
      cellPairKernel_add_left hl]
  simp_rw [h1]
  have hper : ∀ i, -cellPairKernel d ell (i + d + n) (i + d) = -cellPairKernel d ell (i + n) i := by
    intro i
    rw [show i + d + n = i + n + d by ring, cellPairKernel_add_add hl]
  have h := cell_sum_range_rotate (fun i => -cellPairKernel d ell (i + n) i) hper (4 * d - n)
  rw [← h]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [show r + (4 * d - n) = 4 * d - n + r by ring]

lemma cellKernelAvg_zero : cellKernelAvg d ell 0 = 0 := by
  unfold cellKernelAvg
  simp [cellPairKernel_self]

lemma cellKernelAvg_two_d (hl : IsConeCell d ell) : cellKernelAvg d ell (2 * d) = 0 := by
  have h := cellKernelAvg_reflect hl (show 2 * d ≤ 4 * d by omega)
  rw [show 4 * d - 2 * d = 2 * d by omega] at h
  linarith

/-! ## The window value -/

/-- `N² Φ_c(1/4, 1/4) = -2 G(d) = (N²/π²) Cl₂(π/2)`: the value of every cell functional on the window
configuration. -/
noncomputable def windowValue (d : ℕ) : ℝ := -2 * coneG d d

/-- Summation by parts against the tent function: `∑_{m=1}^{k} m Δ²f(m) = k (f(k+1) - f(k)) - (f(k) - f(0))`. -/
lemma sum_mul_second_diff (f : ℕ → ℝ) (k : ℕ) :
    ∑ m ∈ Ico 1 (k + 1), (m : ℝ) * (f (m + 1) - 2 * f m + f (m - 1))
      = k * (f (k + 1) - f k) - (f k - f 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Ico_succ_top (by omega), ih, show k + 1 - 1 = k by omega]
    push_cast
    ring

lemma tent_identity (f : ℕ → ℝ) (hd : 1 ≤ d) :
    ∑ m ∈ Ico 1 d, (m : ℝ) * ((f (m + 1) - 2 * f m + f (m - 1))
        + (f (2 * d - m + 1) - 2 * f (2 * d - m) + f (2 * d - m - 1)))
      + d * (f (d + 1) - 2 * f d + f (d - 1)) = f 0 + f (2 * d) - 2 * f d := by
  set g : ℕ → ℝ := fun n => f (2 * d - n) with hg
  have hsplit : ∀ m ∈ Ico 1 d, (m : ℝ) * ((f (m + 1) - 2 * f m + f (m - 1))
        + (f (2 * d - m + 1) - 2 * f (2 * d - m) + f (2 * d - m - 1)))
      = (m : ℝ) * (f (m + 1) - 2 * f m + f (m - 1)) + (m : ℝ) * (g (m + 1) - 2 * g m + g (m - 1)) := by
    intro m hm
    have hm' := Finset.mem_Ico.1 hm
    simp only [hg]
    rw [show 2 * d - (m + 1) = 2 * d - m - 1 by omega, show 2 * d - (m - 1) = 2 * d - m + 1 by omega]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have e1 := sum_mul_second_diff f (d - 1)
  have e2 := sum_mul_second_diff g (d - 1)
  rw [show d - 1 + 1 = d by omega] at e1 e2
  rw [e1, e2]
  simp only [hg]
  rw [show 2 * d - d = d by omega, show 2 * d - (d - 1) = d + 1 by omega,
    show 2 * d - 0 = 2 * d by omega]
  have hd' : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub hd]; simp
  rw [hd']
  ring

lemma coneWindowSum_period (hl : IsConeCell d ell) (r : ℕ) : coneWindowSum d ell r d = d := by
  rw [coneWindowSum_eq, show r + d = r + d from rfl, cellBoundary_add_period hl]
  ring

lemma coneWindowSum_two_period (hl : IsConeCell d ell) (r : ℕ) :
    coneWindowSum d ell r (2 * d) = 2 * d := by
  rw [coneWindowSum_eq, show r + 2 * d = r + d + d by ring, cellBoundary_add_period hl,
    cellBoundary_add_period hl]
  ring

lemma coneWindowSum_zero (r : ℕ) : coneWindowSum d ell r 0 = 0 := by
  simp [coneWindowSum]

/-- **The window identity**: `∑_{m=1}^{d-1} m u^ℓ_m + d K̃(d) = -2 G(d)` (the value of the averaged cell
functional at the window configuration `N(m) = m`). -/
lemma window_sum (hl : IsConeCell d ell) :
    ∑ m ∈ Ico 1 d, cellDirection d ell m * m + d * cellKernelAvg d ell d = windowValue d := by
  set P : ℕ → ℝ := fun k => (∑ r ∈ range d, coneG d (coneWindowSum d ell r k)) / d with hP
  have hd1 : 1 ≤ d := NeZero.pos d
  have hK : ∀ n, 1 ≤ n → cellKernelAvg d ell n = P (n + 1) - 2 * P n + P (n - 1) := by
    intro n hn
    rw [cellKernelAvg_eq hn]
  have hP0 : P 0 = 0 := by simp [hP, coneWindowSum_zero, coneG_zero]
  have hPd : P d = coneG d d := by
    simp only [hP, coneWindowSum_period hl, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
    field_simp
  have hP2d : P (2 * d) = 0 := by
    simp only [hP, coneWindowSum_two_period hl, coneG_two_d, Finset.sum_const_zero, zero_div]
  have hsum : ∀ m ∈ Ico 1 d, cellDirection d ell m * m
      = (m : ℝ) * ((P (m + 1) - 2 * P m + P (m - 1))
        + (P (2 * d - m + 1) - 2 * P (2 * d - m) + P (2 * d - m - 1))) := by
    intro m hm
    have hm' := Finset.mem_Ico.1 hm
    unfold cellDirection
    rw [hK m hm'.1, hK (2 * d - m) (by omega)]
    ring
  rw [Finset.sum_congr rfl hsum, hK d hd1, tent_identity P hd1, hP0, hP2d, hPd, windowValue]
  ring

/-! ## Net pair counts of a configuration (bridge to module L2) -/

section Counts

variable {M : ℕ}

lemma qconfig_isConfig27B (C : QConfig d M) : Red.IsConfig27B d C.Q := by
  refine ⟨fun x => ⟨(C.isProj x).1, (C.isProj x).2⟩, fun k hk => ?_⟩
  have h := C.pvm ⟨k, hk⟩
  simp_rw [Red.siteIndex_eq_qd] at h
  exact h

lemma corr_eq_Ccorr (C : QConfig d M) (n : ZMod (4 * d)) : C.corr n = Red.Ccorr d C.Q n := by
  unfold QConfig.corr Red.Ccorr
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Red.ntr, Fintype.card_fin, Complex.div_natCast_re]

lemma netCount_eq_Nnet (C : QConfig d M) (m : ℕ) :
    C.netCount (m : ZMod (4 * d)) = Red.Nnet d C.Q m := by
  rw [QConfig.netCount_eq_corr, corr_eq_Ccorr, corr_eq_Ccorr, Red.Nnet]

lemma netCount_reflect (C : QConfig d M) {m : ℕ} (hm : m ≤ 2 * d) :
    C.netCount ((2 * d - m : ℕ) : ZMod (4 * d)) = C.netCount (m : ZMod (4 * d)) := by
  rw [netCount_eq_Nnet, netCount_eq_Nnet, Red.Nnet_reflect C.Q hm]

lemma netCount_d (C : QConfig d M) (hM : 0 < M) : C.netCount ((d : ℕ) : ZMod (4 * d)) = d := by
  have : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  rw [netCount_eq_Nnet, Red.Nnet_d (qconfig_isConfig27B C)]

lemma netCount_neg (C : QConfig d M) (n : ZMod (4 * d)) : C.netCount (-n) = -C.netCount n := by
  unfold QConfig.netCount
  rw [neg_neg]
  ring

end Counts

/-! ## The cell functional and the rotation identity (1.4) -/

section Functional

variable {M : ℕ}

/-- `τ(A_x B_y) = Re Tr(Q_x Q_{y+d}) / M` (`A_x = Q_x`, `B_y = Q_{y+d}`). -/
noncomputable def pairTerm (C : QConfig d M) (x y : ZMod (4 * d)) : ℝ :=
  (C.Q x * C.Q (y + d)).trace.re / M

/-- **The cell functional** `Q^ℓ(Q) = ∑_{x,y ∈ ℤ_N} K^ℓ(x,y) τ(A_x B_y)` (`RIGIDITY_ALLD.md` 1.5). -/
noncomputable def cellFunctional (ell : ℕ → ℝ) (C : QConfig d M) : ℝ :=
  ∑ x : ZMod (4 * d), ∑ y : ZMod (4 * d), cellPairKernel d ell x.val y.val * pairTerm C x y

lemma siteIndex_eq_sub_mu (k : Fin d) (a : ZMod 4) :
    siteIndex d k a = ((k : ℕ) : ZMod (4 * d)) - Red.mu d a := rfl

/-- The rotated configuration `(rot_c Q)_x = Q_{x - c}`, `0 ≤ c < d` (`RIGIDITY_ALLD.md` 1.3). -/
def rotateCfg (C : QConfig d M) (c : Fin d) : QConfig d M where
  Q x := C.Q (x - ((c : ℕ) : ZMod (4 * d)))
  isProj _ := C.isProj _
  pvm k := by
    by_cases h : (c : ℕ) ≤ k
    · have e : ∀ a, siteIndex d k a - ((c : ℕ) : ZMod (4 * d))
          = siteIndex d ⟨k - c, by have := k.isLt; omega⟩ a := by
        intro a
        rw [siteIndex_eq_sub_mu, siteIndex_eq_sub_mu]
        push_cast [Nat.cast_sub h]
        ring
      simp_rw [e]
      exact C.pvm _
    · have e : ∀ a, siteIndex d k a - ((c : ℕ) : ZMod (4 * d))
          = siteIndex d ⟨k + d - c, by have := c.isLt; omega⟩ (a + 1) := by
        intro a
        rw [siteIndex_eq_sub_mu, siteIndex_eq_sub_mu, Red.mu_add, Red.mu_one]
        have hc := c.isLt
        push_cast [Nat.cast_sub (by omega : (c : ℕ) ≤ k + d)]
        ring
      simp_rw [e]
      rw [Fintype.sum_equiv (Equiv.addRight (1 : ZMod 4))
        (fun a => C.Q (siteIndex d ⟨k + d - c, by have := c.isLt; omega⟩ (a + 1)))
        (fun a => C.Q (siteIndex d ⟨k + d - c, by have := c.isLt; omega⟩ a)) (fun a => rfl)]
      exact C.pvm _

lemma cellFunctional_rotate (ell : ℕ → ℝ) (C : QConfig d M) (c : Fin d) :
    cellFunctional ell (rotateCfg C c) = ∑ x : ZMod (4 * d), ∑ y : ZMod (4 * d),
      cellPairKernel d ell (x + ((c : ℕ) : ZMod (4 * d))).val (y + ((c : ℕ) : ZMod (4 * d))).val
        * pairTerm C x y := by
  unfold cellFunctional
  set e := Equiv.addRight (((c : ℕ) : ZMod (4 * d)))
  rw [← Fintype.sum_equiv e _ _ (fun x => rfl)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Fintype.sum_equiv e _ _ (fun y => rfl)]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [e, Equiv.coe_addRight, pairTerm, rotateCfg]
  rw [add_sub_cancel_right, show y + ((c : ℕ) : ZMod (4 * d)) + (d : ZMod (4 * d))
    - ((c : ℕ) : ZMod (4 * d)) = y + d by ring]

lemma sum_cellFunctional_rotate (hl : IsConeCell d ell) (C : QConfig d M) :
    ∑ c : Fin d, cellFunctional ell (rotateCfg C c)
      = d * ∑ x : ZMod (4 * d), ∑ y : ZMod (4 * d),
          cellKernelAvg d ell (x - y).val * pairTerm C x y := by
  simp_rw [cellFunctional_rotate]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.sum_mul]
  have h := cellPairKernel_rot_sum hl x y
  rw [← Fin.sum_univ_eq_sum_range (fun c => cellPairKernel d ell
    (x + (c : ZMod (4 * d))).val (y + (c : ZMod (4 * d))).val) d] at h
  rw [h, cellKernelAvg]
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  field_simp

lemma sum_kernelAvg_pairTerm (C : QConfig d M) :
    ∑ x : ZMod (4 * d), ∑ y : ZMod (4 * d), cellKernelAvg d ell (x - y).val * pairTerm C x y
      = ∑ n : ZMod (4 * d), cellKernelAvg d ell n.val * C.pairCount n := by
  calc ∑ x : ZMod (4 * d), ∑ y : ZMod (4 * d), cellKernelAvg d ell (x - y).val * pairTerm C x y
      = ∑ y : ZMod (4 * d), ∑ x : ZMod (4 * d), cellKernelAvg d ell (x - y).val * pairTerm C x y :=
        Finset.sum_comm
    _ = ∑ y : ZMod (4 * d), ∑ n : ZMod (4 * d), cellKernelAvg d ell n.val * pairTerm C (n + y) y := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← Fintype.sum_equiv (Equiv.addRight y) _ _ (fun n => rfl)]
        refine Finset.sum_congr rfl fun n _ => ?_
        simp only [Equiv.coe_addRight, add_sub_cancel_right]
    _ = ∑ n : ZMod (4 * d), ∑ y : ZMod (4 * d), cellKernelAvg d ell n.val * pairTerm C (n + y) y :=
        Finset.sum_comm
    _ = ∑ n : ZMod (4 * d), cellKernelAvg d ell n.val * C.pairCount n := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [QConfig.pairCount, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [pairTerm, add_comm n y]

end Functional

/-! ## Folding the sum over `ℤ_N` -/

lemma fold_four_d (f : ℕ → ℝ) (hf0 : f 0 = 0) (hf2d : f (2 * d) = 0) :
    ∑ j ∈ range (4 * d), f j = ∑ m ∈ Ico 1 (2 * d), (f m + f (4 * d - m)) := by
  have hd := NeZero.pos d
  rw [← Finset.sum_range_add_sum_Ico f (show 2 * d ≤ 4 * d by omega),
    Red.sum_range_eq_add_Ico f (show 0 < 2 * d by omega), hf0, zero_add,
    Finset.sum_eq_sum_Ico_succ_bot (show 2 * d < 4 * d by omega), hf2d, zero_add,
    Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_Ico_reflect f 1 (show 2 * d ≤ 4 * d + 1 by omega),
    show 4 * d + 1 - 2 * d = 2 * d + 1 by omega, show 4 * d + 1 - 1 = 4 * d by omega]

lemma fold_two_d (g : ℕ → ℝ) :
    ∑ m ∈ Ico 1 (2 * d), g m = ∑ m ∈ Ico 1 d, (g m + g (2 * d - m)) + g d := by
  have hd := NeZero.pos d
  rw [← Finset.sum_Ico_consecutive g (show 1 ≤ d by omega) (show d ≤ 2 * d by omega),
    Finset.sum_eq_sum_Ico_succ_bot (show d < 2 * d by omega), Finset.sum_add_distrib]
  rw [Finset.sum_Ico_reflect g 1 (show d ≤ 2 * d + 1 by omega),
    show 2 * d + 1 - d = d + 1 by omega, show 2 * d + 1 - 1 = 2 * d by omega]
  ring

/-- `∑_{n ∈ ℤ_N} K̃(n) T(n) = ∑_{m=1}^{d-1} u^ℓ_m N(m) + d K̃(d)` (uses `N(2d - m) = N(m)`, `N(d) = d`). -/
lemma sum_kernelAvg_pairCount (hl : IsConeCell d ell) {M : ℕ} (hM : 0 < M) (C : QConfig d M) :
    ∑ n : ZMod (4 * d), cellKernelAvg d ell n.val * C.pairCount n
      = ∑ m ∈ Ico 1 d, cellDirection d ell m * C.netCount (m : ZMod (4 * d))
        + d * cellKernelAvg d ell d := by
  have hd := NeZero.pos d
  rw [Red.sum_zmod_eq_sum_range]
  have hval : ∀ j ∈ range (4 * d), cellKernelAvg d ell ((j : ZMod (4 * d)).val)
      * C.pairCount (j : ZMod (4 * d)) = cellKernelAvg d ell j * C.pairCount (j : ZMod (4 * d)) := by
    intro j hj
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.1 hj)]
  rw [Finset.sum_congr rfl hval]
  rw [fold_four_d (fun j => cellKernelAvg d ell j * C.pairCount (j : ZMod (4 * d)))
    (by simp [cellKernelAvg_zero]) (by simp [cellKernelAvg_two_d hl])]
  have hstep : ∀ m ∈ Ico 1 (2 * d), cellKernelAvg d ell m * C.pairCount (m : ZMod (4 * d))
      + cellKernelAvg d ell (4 * d - m) * C.pairCount ((4 * d - m : ℕ) : ZMod (4 * d))
      = cellKernelAvg d ell m * C.netCount (m : ZMod (4 * d)) := by
    intro m hm
    have hm' := Finset.mem_Ico.1 hm
    have hcast : ((4 * d - m : ℕ) : ZMod (4 * d)) = -(m : ZMod (4 * d)) := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub]
    rw [cellKernelAvg_reflect hl (by omega), hcast, QConfig.netCount]
    ring
  rw [Finset.sum_congr rfl hstep, fold_two_d]
  rw [netCount_d C hM]
  congr 1
  · refine Finset.sum_congr rfl fun m hm => ?_
    have hm' := Finset.mem_Ico.1 hm
    rw [netCount_reflect C (by omega), cellDirection]
    ring
  · ring

/-- **Identity (1.4)** (`RIGIDITY_ALLD.md` 1.5 (ii); QD2-L1/L2): the average over the `d` rotations of the
cell functional, minus the window value, is the cell pairing `⟨u^ℓ, δ⟩`. -/
theorem window_identity (hl : IsConeCell d ell) {M : ℕ} (hM : 0 < M) (C : QConfig d M) :
    (∑ c : Fin d, (cellFunctional ell (rotateCfg C c) - windowValue d)) / d
      = pairingIco d (cellDirection d ell) C.delta := by
  have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  rw [Finset.sum_sub_distrib, sum_cellFunctional_rotate hl, sum_kernelAvg_pairTerm,
    sum_kernelAvg_pairCount hl hM, ← window_sum hl]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold pairingIco QConfig.delta
  rw [← mul_sub, add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib, mul_div_cancel_left₀ _ hd]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-! ## The single cell inequalities and the continuum equality analysis -/

/-- **Hypothesis (1.3)**: Q-T1 for one cell-embedded step field (`RIGIDITY_ALLD.md` s.3.1-3.6; `QD2/LOG.md`
s.4 (ii)): for every configuration on `ℂ^M` and every cell vector `ℓ ∈ Δ_d`,
`Q^ℓ(Q) ≤ N² Φ_c(1/4, 1/4)`. -/
def Hyp_CellIneqSingle (d : ℕ) [NeZero d] : Prop :=
  ∀ M : ℕ, 0 < M → ∀ C : QConfig d M, ∀ ell : ℕ → ℝ, IsConeCell d ell →
    cellFunctional ell C ≤ windowValue d

/-- **Hypothesis (1.3) for cell vectors with all cells positive** (the form needed for rigidity; it is the
form proved from `(*)` by module L5, `OQP27.Cell.cellFamily_ineq`, up to the factor `M`). -/
def Hyp_CellIneqSinglePos (d : ℕ) [NeZero d] : Prop :=
  ∀ M : ℕ, 0 < M → ∀ C : QConfig d M, ∀ ell : ℕ → ℝ, IsPosConeCell d ell →
    cellFunctional ell C ≤ windowValue d

lemma Hyp_CellIneqSingle.pos (h : Hyp_CellIneqSingle d) : Hyp_CellIneqSinglePos d :=
  fun M hM C ell hell => h M hM C ell hell.1

/-- **Hypothesis: the equality analysis of the continuum theorem** (`RIGIDITY_ALLD.md` s.3.7, using the
equality case of the strip inequality, `Q_2bmv/PROOF.md` Theorem 2(d)): if the cell inequality (1.3) of a
cell vector with all cells positive is an equality, `Q^ℓ(Q) = N² Φ_c(1/4, 1/4)`, then the step field
`B(θ) = Q_{x+d}` on the cells commutes with its conjugate function `g(θ)` for almost every `θ`. -/
def Hyp_ContinuumEquality (d : ℕ) [NeZero d] : Prop :=
  ∀ M : ℕ, 0 < M → ∀ C : QConfig d M, ∀ ell : ℕ → ℝ, IsPosConeCell d ell →
    cellFunctional ell C = windowValue d →
    ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (2 * Real.pi))),
      stepField (ellFin ell) (fieldB C) θ * conjField (ellFin ell) (fieldB C) θ
        = conjField (ellFin ell) (fieldB C) θ * stepField (ellFin ell) (fieldB C) θ

/-- **QD2-L1 from (1.3)**: the single cell inequalities imply the cell-embedding inequalities
`⟨u^ℓ, δ⟩ ≤ 0` of module L1 (average over the rotations, identity (1.4)). -/
theorem cellInequalities_of_single (h : Hyp_CellIneqSingle d) : Hyp_CellInequalities d := by
  intro M hM C ell hl
  rw [← window_identity hl hM C]
  apply div_nonpos_of_nonpos_of_nonneg _ (Nat.cast_nonneg d)
  exact Finset.sum_nonpos fun c _ => sub_nonpos.2 (h M hM (rotateCfg C c) ell hl)

lemma cellFunctional_rotate_zero (ell : ℕ → ℝ) {M : ℕ} (C : QConfig d M) :
    cellFunctional ell (rotateCfg C ⟨0, NeZero.pos d⟩) = cellFunctional ell C := by
  simp [cellFunctional, pairTerm, rotateCfg]

/-- **Step 1, second half** (`RIGIDITY_ALLD.md` s.2, eq. (2.1)), and **Step 2**: a tight cell inequality
`⟨u^ℓ, δ⟩ = 0` makes every rotated single cell inequality tight, in particular `Q^ℓ(Q) = N² Φ_c`, and the
continuum equality analysis gives `[B(θ), g(θ)] = 0` almost everywhere. -/
theorem cellEqualityAE_of_continuum (h1 : Hyp_CellIneqSinglePos d) (h2 : Hyp_ContinuumEquality d) :
    Hyp_CellEqualityAE d := by
  intro M hM C ell hell h0
  rw [← window_identity hell.1 hM C] at h0
  have hsum : ∑ c : Fin d, (cellFunctional ell (rotateCfg C c) - windowValue d) = 0 := by
    have hd : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
    rcases div_eq_zero_iff.1 h0 with h | h
    · exact h
    · exact absurd h hd
  have hzero := (Finset.sum_eq_zero_iff_of_nonpos (fun c _ =>
    sub_nonpos.2 (h1 M hM (rotateCfg C c) ell hell))).1 hsum ⟨0, NeZero.pos d⟩ (Finset.mem_univ _)
  have hQ : cellFunctional ell C = windowValue d := by
    rw [← cellFunctional_rotate_zero]
    linarith
  exact h2 M hM C ell hell hQ

/-- **Theorem R (rigidity, every `d ≥ 2`)** from the single cell inequalities (1.3), the equality
analysis of the continuum theorem, CONE_d with an all-positive cell vector, and the classical Theorem B. -/
theorem rigidity_all_d' (hd : 2 ≤ d) (h1 : Hyp_CellIneqSingle d) (h2 : Hyp_ContinuumEquality d)
    (hcone : ConeCertPos d) (hB : Hyp_ClassicalTheoremB d) : RigidityStatement d :=
  rigidity_all_d hd (cellInequalities_of_single h1) (cellEqualityAE_of_continuum h1.pos h2) hcone hB

/-- **Theorem R** with the cell inequalities of module L1 (QD2-L1, in the rotation-averaged form) and the
single cell inequalities (1.3) only for cell vectors with all cells positive. -/
theorem rigidity_all_d'' (hd : 2 ≤ d) (hcell : Hyp_CellInequalities d)
    (h1 : Hyp_CellIneqSinglePos d) (h2 : Hyp_ContinuumEquality d) (hcone : ConeCertPos d)
    (hB : Hyp_ClassicalTheoremB d) : RigidityStatement d :=
  rigidity_all_d hd hcell (cellEqualityAE_of_continuum h1 h2) hcone hB

/-- **Optimality** from the single cell inequalities (1.3) and CONE_d (the reduction is module L2's). -/
theorem optimality_of_single (hd : 2 ≤ d) (h1 : Hyp_CellIneqSingle d) (hcone : ConeCert d) :
    OptimalityStatement d :=
  optimality_of_cells hd (cellInequalities_of_single h1) hcone Red.hyp_reduction

end OQP27.Rig
