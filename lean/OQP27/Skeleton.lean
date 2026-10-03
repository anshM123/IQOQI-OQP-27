import OQP27.Statement
import OQP27.CertDefs
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# OQP 27B (max-ent clause, every `d`): the logical skeleton

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

This file states, as explicit `Prop`-valued hypotheses, the results of the paper chain that are proved on
paper but not (yet) formalised, and proves in Lean that they imply the statements of
`OQP27/Statement.lean`:
* `OQP27.optimality_of_cells`, `OQP27.optimality_of_strip`: `OptimalityStatement d`;
* `OQP27.rigidity_of_cells`, `OQP27.rigidity_of_strip`: `RigidityStatement d`;
* `OQP27.maxEntClause_of_strip`, `OQP27.maxEntClause_all_d`: the whole max-ent clause.

## Objects (definitions follow `iqoqi/programs/oqp27B_all/QD2/LOG.md`, section 4, and `SHARED_LEMMAS.md` [QD2])
* `OQP27.QConfig d M`: a 27B configuration on `ℂ^M` (`N = 4d` projections `Q_x`, `x ∈ ℤ_N`; for every site
  `k` the four projections `Q_{k - d a}`, `a ∈ ℤ_4`, form a PVM); `A_x = Q_x`, `B_x = Q_{x+d}`, `τ = Tr/M`.
* `T(m) = ∑_y τ(A_{y+m} B_y)` (`QConfig.pairCount`), `N(m) = T(m) - T(-m)` (`QConfig.netCount`),
  `δ_m = N(m) - m` (`QConfig.delta`), `⟨a, b⟩ = ∑_{m=1}^{d-1} a_m b_m` (`OQP27.pairingIco`).
* `v_m = 2 csc(π m/(2d))`: `OQP27.coneV` (from `OQP27/CertDefs.lean`, module L4).
* cell vectors `ℓ ∈ Δ_d` (`OQP27.IsConeCell`, from `CertDefs.lean`); the cell boundaries
  `L_n = ℓ_0 + ⋯ + ℓ_{n-1}` (`OQP27.cellBoundary`), the cell-pair kernel
  `K^ℓ(x,y) = ∫_{I_x} ∫_{I_y} cot(π(ξ-η)/N) = G(L_{x+1}-L_y) - G(L_x-L_y) - G(L_{x+1}-L_{y+1}) + G(L_x-L_{y+1})`
  with `G(u) = -(N²/(2π²)) Cl₂(2πu/N)` (`OQP27.cellPairKernel`, `OQP27.coneG`), its rotation average
  `K̃(n) = (1/d) ∑_{r<d} K^ℓ(r+n, r)` and the cell direction `u^ℓ_m = K̃(m) + K̃(2d-m)`
  (`OQP27.cellDirection`), exactly as in QD2-L1 / QD2 section 4 (ii).
* the strip: the Poisson kernel `K_x(u) = sin(πx)/(2(cosh(πu) - cos(πx)))` of `0 < Re w < 1` for its
  left edge (`OQP27.stripPoissonKernel`), `h_λ` on the closed strip (`OQP27.hStrip`), the spectral sum
  `∑_{ν ∈ spec(B + ig)} h_λ(ν)` over the roots of the characteristic polynomial (`OQP27.stripSum`) and
  `Tr X_+` (`OQP27.posPartTrace`).

## Proved here (no hypotheses)
* `OQP27.cellDirection_eq_coneU` (QD2-L2, window-sum form): for every cell vector, the kernel-form cell
  direction equals the window-sum form `coneU` used by the certificates of module L4;
* `OQP27.pairing_coneV_nonpos` (QD2-R1, the CONE step): cell inequalities + `CONE_d` give
  `⟨v, δ⟩ ≤ 0` for every configuration (a finite sum of nonpositive terms);
* `OQP27.exists_pos_cell_tight` (step 1 of the rigidity chain);
* the chain theorems listed above;
* bridges for the integration with module L2: `OQP27.QConfig.netCount_eq_corr`
  (`N(m) = C(m - d) - C(m + d)`, `C(n) = ∑_u τ(Q_u Q_{u+n})`, `RIGIDITY_ALLD.md` 1.4),
  `OQP27.IME_eq_sum_csc` (`I_ME(d) = 4/(d(d-1)) ∑_m m csc(πm/(2d))`) and `OQP27.clock_value_eq_linear`
  (if `F = ∑_m csc(πm/(2d)) N(m)` (QD-L7), then `4F/(d(d-1)) = I_ME(d) + 2/(d(d-1)) ⟨v, δ⟩`).

## Hypotheses (paper results, not formalised here)
* `OQP27.Hyp_StripInequality`: the strip inequality `(*)` for every `M` (`Q_2bmv/PROOF.md`, Theorem 2).
* `OQP27.Hyp_StripEquality`: its equality case, `[B, g] = 0` (`Q_2bmv/PROOF.md`, Theorem 2, equality clause).
* `OQP27.Hyp_CellInequalities d`: QD2-L1, `⟨u^ℓ, δ⟩ ≤ 0` for every cell vector and configuration
  (`QD2/LOG.md` s.4 (ii); it is the continuum theorem Q-T1 for cell-embedded step fields averaged over
  rotations).  `OQP27.Hyp_ContinuumCell d` records that it follows from `(*)` (Q-T1:
  `Q_quantum/LOG.md` s.4 and s.8; `Q_rig/RIGIDITY_ALLD.md` s.3).
* `OQP27.Hyp_CellEquality d`: steps 1-3 of `Q_rig/RIGIDITY_ALLD.md` (a tight cell inequality with all cells
  positive forces all `Q_x` to commute); `OQP27.Hyp_ContinuumCellEq d` records that it follows from `(*)`
  and its equality case.
* `OQP27.ConeCert d` (module L4, `CertDefs.lean`) and its strengthening `OQP27.ConeCertPos d` (one cell
  vector with all cells positive carries positive weight): `QD2/LOG.md` s.3, 8, 9 (QD2-T1, T2, T3;
  computer-assisted).
* `OQP27.Hyp_Reduction d`, `OQP27.Hyp_ReductionRig d`: the reduction strategy → clock model →
  Q-configuration → linear form (`paper-classical-all-d/main.tex` Theorem 2.3 and appendix; QD-L7;
  `Q_rig/RIGIDITY_ALLD.md` 1.2-1.4) and, for rigidity, the commutative-sector theorem (Theorem B and
  Corollary C of `main.tex`; `RIGIDITY_ALLD.md` s.6).
-/

namespace OQP27

open Matrix Complex Finset
open scoped ComplexOrder Real

/-! ## 27B configurations and the linear form -/

section Config

/-- The index `k - d a ∈ ℤ_{4d}` of the label `a ∈ ℤ_4` at the site `k` (`RIGIDITY_ALLD.md` 1.3). -/
def siteIndex (d : ℕ) (k : Fin d) (a : ZMod 4) : ZMod (4 * d) :=
  ((k : ℕ) : ZMod (4 * d)) - (d : ZMod (4 * d)) * ((a.val : ℕ) : ZMod (4 * d))

/-- A 27B configuration ("Q-configuration") on `ℂ^M` (`QD2/LOG.md` s.4, `RIGIDITY_ALLD.md` 1.3):
projections `Q_x`, `x ∈ ℤ_{4d}`, such that for every site `k ∈ {0, …, d-1}` the four projections
`Q_{k - d a}` (`a ∈ ℤ_4`), i.e. `Q_k, Q_{k+d}, Q_{k+2d}, Q_{k+3d}`, form a PVM. -/
structure QConfig (d M : ℕ) where
  /-- the projections `Q_x`, `x ∈ ℤ_{4d}` -/
  Q : ZMod (4 * d) → Matrix (Fin M) (Fin M) ℂ
  isProj : ∀ x, IsProjection (Q x)
  pvm : ∀ k : Fin d, ∑ a : ZMod 4, Q (siteIndex d k a) = 1

namespace QConfig

variable {d M : ℕ} [NeZero d] (C : QConfig d M)

/-- `T(m) = ∑_{y ∈ ℤ_{4d}} τ(A_{y+m} B_y)`, `A_x = Q_x`, `B_x = Q_{x+d}`, `τ = Tr/M` (the trace is real). -/
noncomputable def pairCount (m : ZMod (4 * d)) : ℝ :=
  ∑ y : ZMod (4 * d), (C.Q (y + m) * C.Q (y + d)).trace.re / M

/-- The net `B → A` pair count `N(m) = T(m) - T(-m)`. -/
noncomputable def netCount (m : ZMod (4 * d)) : ℝ :=
  C.pairCount m - C.pairCount (-m)

/-- `δ_m = N(m) - m`, used for `m = 1, …, d-1` (`δ = 0` for the DKZ window configuration). -/
noncomputable def delta (m : ℕ) : ℝ :=
  C.netCount (m : ZMod (4 * d)) - m

end QConfig

/-- `⟨a, b⟩ = ∑_{m=1}^{d-1} a_m b_m`. -/
def pairingIco (d : ℕ) (a b : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Ico 1 d, a m * b m

end Config

/-! ## Cell embeddings: the kernel form of the cell directions (QD2-L1) -/

section Cells

/-- The cell boundaries `L_n = ℓ_0 + ℓ_1 + ⋯ + ℓ_{n-1}` (indices mod `d`): in the cell embedding of
`ℤ_{4d}` into `ℝ/4dℤ` the cell of `x` is `I_x = [L_x, L_{x+1})`, of length `ℓ_{x mod d}`. -/
def cellBoundary (d : ℕ) (ell : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range n, ell (i % d)

/-- The cell-pair kernel `K^ℓ(x,y) = ∫_{I_x} ∫_{I_y} cot(π(ξ - η)/N) dη dξ`, `N = 4d`, written with the
second antiderivative `G = coneG d` of `cot(π · /N)` (QD2 section 4 (ii)):
`K^ℓ(x,y) = G(L_{x+1} - L_y) - G(L_x - L_y) - G(L_{x+1} - L_{y+1}) + G(L_x - L_{y+1})`. -/
noncomputable def cellPairKernel (d : ℕ) (ell : ℕ → ℝ) (x y : ℕ) : ℝ :=
  coneG d (cellBoundary d ell (x + 1) - cellBoundary d ell y) -
    coneG d (cellBoundary d ell x - cellBoundary d ell y) -
    coneG d (cellBoundary d ell (x + 1) - cellBoundary d ell (y + 1)) +
    coneG d (cellBoundary d ell x - cellBoundary d ell (y + 1))

/-- The rotation average `K̃(n) = (1/d) ∑_{r<d} K^ℓ(r + n, r)`. -/
noncomputable def cellKernelAvg (d : ℕ) (ell : ℕ → ℝ) (n : ℕ) : ℝ :=
  (∑ r ∈ range d, cellPairKernel d ell (r + n) r) / d

/-- The cell direction of QD2-L1: `u^ℓ_m = K̃(m) + K̃(2d - m)`, `m = 1, …, d-1`. -/
noncomputable def cellDirection (d : ℕ) (ell : ℕ → ℝ) (m : ℕ) : ℝ :=
  cellKernelAvg d ell m + cellKernelAvg d ell (2 * d - m)

/-- A cell vector with all cells positive (`ℓ ∈ Δ_d^+`). -/
def IsPosConeCell (d : ℕ) (ell : ℕ → ℝ) : Prop :=
  IsConeCell d ell ∧ ∀ r < d, 0 < ell r

variable {d : ℕ} {ell : ℕ → ℝ}

/-- Rotating the summation index of a `d`-periodic function. -/
lemma cell_sum_range_rotate (f : ℕ → ℝ)
    (hf : ∀ i, f (i + d) = f i) (n : ℕ) : ∑ i ∈ range d, f (n + i) = ∑ i ∈ range d, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 := sum_range_succ' (fun i => f (n + i)) d
    have h2 := sum_range_succ (fun i => f (n + i)) d
    simp only [add_zero] at h1 h2
    rw [← ih]
    have e : ∀ i, f (n + 1 + i) = f (n + (i + 1)) := fun i => by rw [add_assoc, add_comm 1 i]
    simp_rw [e]
    rw [hf n] at h2
    have := h1.symm.trans h2
    exact add_right_cancel this

lemma cellBoundary_add (n m : ℕ) :
    cellBoundary d ell (n + m) = cellBoundary d ell n + coneWindowSum d ell n m := by
  rw [cellBoundary, sum_range_add]
  rfl

lemma coneWindowSum_eq (r m : ℕ) :
    coneWindowSum d ell r m = cellBoundary d ell (r + m) - cellBoundary d ell r := by
  rw [cellBoundary_add]
  ring

lemma coneWindowSum_add_period (r m : ℕ) :
    coneWindowSum d ell (r + d) m = coneWindowSum d ell r m := by
  unfold coneWindowSum
  refine sum_congr rfl fun i _ => ?_
  congr 1
  rw [show r + d + i = r + i + d by ring, Nat.add_mod_right]

lemma cellBoundary_add_period (hl : IsConeCell d ell) (n : ℕ) :
    cellBoundary d ell (n + d) = cellBoundary d ell n + d := by
  rw [cellBoundary_add]
  congr 1
  unfold coneWindowSum
  rw [cell_sum_range_rotate (fun i => ell (i % d)) (fun i => by simp [Nat.add_mod_right]) n,
    ← hl.2]
  refine sum_congr rfl fun i hi => ?_
  rw [Nat.mod_eq_of_lt (mem_range.1 hi)]

/-- `K̃(n) = P(n+1) - 2 P(n) + P(n-1)` with `P(k) = (1/d) ∑_r G(S_r(k))` (`n ≥ 1`). -/
lemma cellKernelAvg_eq {n : ℕ} (hn : 1 ≤ n) :
    cellKernelAvg d ell n =
      (∑ r ∈ range d, coneG d (coneWindowSum d ell r (n + 1))) / d -
        2 * ((∑ r ∈ range d, coneG d (coneWindowSum d ell r n)) / d) +
        (∑ r ∈ range d, coneG d (coneWindowSum d ell r (n - 1))) / d := by
  have hrot : ∀ k, ∑ r ∈ range d, coneG d (coneWindowSum d ell (1 + r) k) =
      ∑ r ∈ range d, coneG d (coneWindowSum d ell r k) := fun k =>
    cell_sum_range_rotate (fun r => coneG d (coneWindowSum d ell r k))
      (fun r => by simp only [coneWindowSum_add_period]) 1
  have hK : ∀ r, cellPairKernel d ell (r + n) r =
      coneG d (coneWindowSum d ell r (n + 1)) - coneG d (coneWindowSum d ell r n) -
        coneG d (coneWindowSum d ell (1 + r) n) + coneG d (coneWindowSum d ell (1 + r) (n - 1)) := by
    intro r
    simp only [cellPairKernel, coneWindowSum_eq]
    rw [show r + (n + 1) = r + n + 1 by ring, show 1 + r + n = r + n + 1 by ring,
      show 1 + r + (n - 1) = r + n by omega, show 1 + r = r + 1 by ring]
  unfold cellKernelAvg
  simp_rw [hK]
  rw [sum_add_distrib, sum_sub_distrib, sum_sub_distrib, hrot, hrot]
  ring

/-- For `j ≤ d`: `∑_r G(S_r(2d - j)) = ∑_r G(2d - S_r(j))` (a window of length `2d - j` is a full period
plus the complement of a window of length `j`). -/
lemma sum_coneG_window_reflect (hl : IsConeCell d ell) {j : ℕ} (hj : j ≤ d) :
    ∑ r ∈ range d, coneG d (coneWindowSum d ell r (2 * d - j)) =
      ∑ r ∈ range d, coneG d (2 * (d : ℝ) - coneWindowSum d ell r j) := by
  have hper := cellBoundary_add_period hl
  have key : ∀ r, coneWindowSum d ell r (2 * d - j) =
      2 * (d : ℝ) - coneWindowSum d ell ((d - j) + r) j := by
    intro r
    rw [coneWindowSum_eq, coneWindowSum_eq]
    have e1 : r + (2 * d - j) = (r + (d - j)) + d := by omega
    have e2 : d - j + r + j = r + d := by omega
    rw [e1, e2, hper, hper, show d - j + r = r + (d - j) by ring]
    ring
  simp_rw [key]
  exact cell_sum_range_rotate (fun r => coneG d (2 * (d : ℝ) - coneWindowSum d ell r j))
    (fun r => by simp only [coneWindowSum_add_period]) (d - j)

/-- **QD2-L2 (window-sum form).** For every cell vector `ℓ ∈ Δ_d` and `1 ≤ m ≤ d - 1`, the kernel-form
cell direction `u^ℓ_m = K̃(m) + K̃(2d - m)` equals `Δ²_m (1/d) ∑_r Ĝ(S_r(m))` (`coneU`, module L4). -/
theorem cellDirection_eq_coneU (hl : IsConeCell d ell) {m : ℕ} (hm1 : 1 ≤ m) (hm2 : m ≤ d - 1) :
    cellDirection d ell m = coneU d ell m := by
  unfold cellDirection coneU coneP
  rw [cellKernelAvg_eq hm1, cellKernelAvg_eq (by omega : 1 ≤ 2 * d - m)]
  rw [show 2 * d - m + 1 = 2 * d - (m - 1) by omega, show 2 * d - m - 1 = 2 * d - (m + 1) by omega,
    sum_coneG_window_reflect hl (by omega : m - 1 ≤ d), sum_coneG_window_reflect hl (by omega : m ≤ d),
    sum_coneG_window_reflect hl (by omega : m + 1 ≤ d)]
  simp only [coneGhat, sum_add_distrib]
  ring

end Cells

/-! ## The strip -/

section Strip

/-- The Poisson kernel of the strip `0 < Re w < 1` for its left edge `Re w = 0`:
`K_x(u) = sin(πx) / (2 (cosh(πu) - cos(πx)))` (mass `1 - x`; same formula as
`OQP27.StripL3a.stripKernel`). -/
noncomputable def stripPoissonKernel (x u : ℝ) : ℝ :=
  Real.sin (π * x) / (2 * (Real.cosh (π * u) - Real.cos (π * x)))

/-- `h_λ` on the closed strip `0 ≤ Re w ≤ 1`: boundary values `(y - λ)_+` on `Re w = 0` and `0` on
`Re w = 1`, and inside the Poisson integral `h_λ(x + iy) = ∫ K_x(y - s) (s - λ)_+ ds` (the integrand is
integrable: `K_x(u) = O(e^{-π|u|})`).  Equivalently `h_λ(x+iy) = -(1/π²) Im Li₂(e^{π(y-λ)} e^{-iπx})`
(`Q_2bmv/PROOF.md`, Theorem 2).  Values off the closed strip are irrelevant: every eigenvalue of `B + ig`
(`B` a projection, `g` Hermitian) has real part in `[0, 1]`. -/
noncomputable def hStrip (lam : ℝ) (w : ℂ) : ℝ :=
  if w.re ≤ 0 then max (w.im - lam) 0
  else if 1 ≤ w.re then 0
  else ∫ s : ℝ, stripPoissonKernel w.re (w.im - s) * max (s - lam) 0

/-- `Tr X_+ = ∑_i max(λ_i(X), 0)` for a Hermitian matrix `X` (and `0` otherwise). -/
noncomputable def posPartTrace {M : ℕ} (X : Matrix (Fin M) (Fin M) ℂ) : ℝ := by
  classical
  exact if h : X.IsHermitian then ∑ i, max (h.eigenvalues i) 0 else 0

/-- `∑_{ν ∈ spec(B + ig)} h_λ(ν)`, eigenvalues with algebraic multiplicity (roots of the characteristic
polynomial). -/
noncomputable def stripSum {M : ℕ} (lam : ℝ) (B g : Matrix (Fin M) (Fin M) ℂ) : ℝ :=
  ((B + Complex.I • g).charpoly.roots.map (hStrip lam)).sum

/-- **The strip inequality `(*)`** (`Q_2bmv/PROOF.md`, Theorem 2; module L3): for every `M`, every
projection `B` on `ℂ^M` (`P = 1 - B`), every Hermitian `g` and every real `λ`,
`∑_{ν ∈ spec(B + ig)} h_λ(ν) ≥ Tr[(P(g - λ)P)_+]`. -/
def Hyp_StripInequality : Prop :=
  ∀ (M : ℕ) (B g : Matrix (Fin M) (Fin M) ℂ), IsProjection B → g.IsHermitian → ∀ lam : ℝ,
    posPartTrace ((1 - B) * (g - (lam : ℂ) • 1) * (1 - B)) ≤ stripSum lam B g

/-- **Equality case of `(*)`** (`Q_2bmv/PROOF.md`, Theorem 2: equality at one `λ` iff `[B, g] = 0`):
equality forces `B` and `g` to commute. -/
def Hyp_StripEquality : Prop :=
  ∀ (M : ℕ) (B g : Matrix (Fin M) (Fin M) ℂ), IsProjection B → g.IsHermitian → ∀ lam : ℝ,
    stripSum lam B g = posPartTrace ((1 - B) * (g - (lam : ℂ) • 1) * (1 - B)) → B * g = g * B

end Strip

/-! ## The hypotheses of the chain -/

section Hypotheses

variable (d : ℕ)

/-- **Cell-embedding inequalities (QD2-L1)**: for every `M ≥ 1`, every 27B configuration on `ℂ^M` and
every cell vector `ℓ ∈ Δ_d`, `⟨u^ℓ, δ⟩ ≤ 0`.  Paper: `QD2/LOG.md` s.4 (ii) (the continuum theorem Q-T1
for the cell-embedded step field, averaged over the rotations `Q_x ↦ Q_{x-c}`). -/
def Hyp_CellInequalities [NeZero d] : Prop :=
  ∀ M : ℕ, 0 < M → ∀ C : QConfig d M, ∀ ell : ℕ → ℝ, IsConeCell d ell →
    pairingIco d (cellDirection d ell) C.delta ≤ 0

/-- The continuum theorem in the form used: `(*)` for every `M` implies the cell inequalities
(Q-T1: `Q_quantum/LOG.md` s.4 and s.8; `Q_rig/RIGIDITY_ALLD.md` s.3, with every step displayed;
`QD2/LOG.md` s.4 (ii) for the rotation average). -/
def Hyp_ContinuumCell [NeZero d] : Prop := Hyp_StripInequality → Hyp_CellInequalities d

/-- **Rigidity steps 1-3 (`Q_rig/RIGIDITY_ALLD.md` s.2-4)**: if a cell inequality with all cells positive is
tight, `⟨u^ℓ, δ⟩ = 0`, then all projections of the configuration commute (equality in every rotated
continuum inequality, equality in `(*)` a.e., and the residue lemma). -/
def Hyp_CellEquality [NeZero d] : Prop :=
  ∀ M : ℕ, 0 < M → ∀ C : QConfig d M, ∀ ell : ℕ → ℝ, IsPosConeCell d ell →
    pairingIco d (cellDirection d ell) C.delta = 0 → ∀ x y, C.Q x * C.Q y = C.Q y * C.Q x

/-- Steps 1-3 of the rigidity chain follow from `(*)` and its equality case (`RIGIDITY_ALLD.md` s.2-4). -/
def Hyp_ContinuumCellEq [NeZero d] : Prop :=
  Hyp_StripInequality → Hyp_StripEquality → Hyp_CellEquality d

/-- `CONE_d` with one all-positive cell vector of positive weight (`RIGIDITY_ALLD.md` s.5: all LP
certificates for `d ≤ 200` have every `n_r ≥ 1`; for `d ≥ 201` the Dirichlet-type measures charge only
all-positive cell vectors). -/
def ConeCertPos : Prop :=
  ∃ (K : ℕ) (ell : Fin K → ℕ → ℝ) (lam : Fin K → ℝ),
    (∀ k, IsConeCell d (ell k)) ∧ (∀ k, 0 ≤ lam k) ∧
    (∀ m : ℕ, 1 ≤ m → m ≤ d - 1 → ∑ k, lam k * coneU d (ell k) m = coneV d m) ∧
    ∃ k, 0 < lam k ∧ ∀ r < d, 0 < ell k r

/-- **The reduction** (`paper-classical-all-d/main.tex`, Theorem 2.3 and appendix; QD-L7;
`Q_rig/RIGIDITY_ALLD.md` 1.2-1.4): every projective strategy on `Φ_D` has a 27B configuration (on `ℂ^M`,
`M = 4D`) with `I_d = I_ME(d) + 2/(d(d-1)) ⟨v, δ⟩` (equivalently `F(V) - F_DKZ = ⟨v, δ⟩/2`). -/
def Hyp_Reduction [NeZero d] : Prop :=
  ∀ D : ℕ, 0 < D → ∀ S : Strategy d D, ∃ M : ℕ, 0 < M ∧ ∃ C : QConfig d M,
    S.cglmp = IME d + 2 / ((d : ℝ) * ((d : ℝ) - 1)) * pairingIco d (coneV d) C.delta

/-- **The reduction with its rigidity clause**: as `Hyp_Reduction`, and if the projections of the
configuration commute (equivalently: the reduced family commutes, the strategy has equal links) and the
strategy attains `I_ME(d)`, then it is DKZ ⊗ 1 up to a local unitary (`main.tex` Proposition 2.4,
Theorem B and Corollary C; `RIGIDITY_ALLD.md` s.6). -/
def Hyp_ReductionRig [NeZero d] : Prop :=
  ∀ D : ℕ, 0 < D → ∀ S : Strategy d D, ∃ M : ℕ, 0 < M ∧ ∃ C : QConfig d M,
    S.cglmp = IME d + 2 / ((d : ℝ) * ((d : ℝ) - 1)) * pairingIco d (coneV d) C.delta ∧
    ((∀ x y, C.Q x * C.Q y = C.Q y * C.Q x) → S.cglmp = IME d → S.IsDKZTensorId)

variable {d}

theorem ConeCertPos.coneCert (h : ConeCertPos d) : ConeCert d := by
  obtain ⟨K, ell, lam, h1, h2, h3, -⟩ := h
  exact ⟨K, ell, lam, h1, h2, h3⟩

theorem Hyp_ReductionRig.reduction [NeZero d] (h : Hyp_ReductionRig d) : Hyp_Reduction d := by
  intro D hD S
  obtain ⟨M, hM, C, h1, -⟩ := h D hD S
  exact ⟨M, hM, C, h1⟩

end Hypotheses

/-! ## Bridges to the reduction module (L2) -/

section Bridges

namespace QConfig

variable {d M : ℕ} [NeZero d] (C : QConfig d M)

/-- `C(n) = ∑_{u ∈ ℤ_{4d}} τ(Q_u Q_{u+n})` (`RIGIDITY_ALLD.md` 1.4). -/
noncomputable def corr (n : ZMod (4 * d)) : ℝ :=
  ∑ u : ZMod (4 * d), (C.Q u * C.Q (u + n)).trace.re / M

/-- `T(m) = C(d - m)`. -/
theorem pairCount_eq_corr (m : ZMod (4 * d)) : C.pairCount m = C.corr (d - m) := by
  unfold pairCount corr
  rw [← (Equiv.subRight m).sum_comp]
  refine sum_congr rfl fun u _ => ?_
  simp only [Equiv.subRight_apply, sub_add_cancel]
  rw [show u - m + (d : ZMod (4 * d)) = u + (d - m) by ring]

/-- `C(-n) = C(n)`. -/
theorem corr_neg (n : ZMod (4 * d)) : C.corr (-n) = C.corr n := by
  unfold corr
  refine Fintype.sum_equiv (Equiv.subRight n) _ _ fun u => ?_
  simp only [Equiv.subRight_apply, sub_add_cancel]
  rw [Matrix.trace_mul_comm (C.Q (u - n)), sub_eq_add_neg]

/-- `N(m) = C(m - d) - C(m + d)`: the form of the net pair count used in `RIGIDITY_ALLD.md` 1.4 and
in module L2. -/
theorem netCount_eq_corr (m : ZMod (4 * d)) :
    C.netCount m = C.corr (m - d) - C.corr (m + d) := by
  unfold netCount
  rw [pairCount_eq_corr, pairCount_eq_corr, ← C.corr_neg (m - d)]
  congr 2 <;> ring

end QConfig

/-- `I_ME(d) = 4/(d(d-1)) ∑_{m=1}^{d-1} m csc(π m/(2d))` (reflection `m ↦ d - m`;
`F_DKZ = ∑_m (d - m) sec ψ_m = ∑_m m csc ψ_m`). -/
theorem IME_eq_sum_csc (d : ℕ) :
    IME d = 4 / ((d : ℝ) * ((d : ℝ) - 1)) *
      ∑ m ∈ Ico 1 d, (m : ℝ) / Real.sin (π * m / (2 * d)) := by
  unfold IME
  congr 1
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have hrefl := Finset.sum_Ico_reflect (fun m : ℕ => (m : ℝ) / Real.sin (π * m / (2 * d))) 1
    (show d ≤ d + 1 by omega)
  rw [show d + 1 - d = 1 by omega, show d + 1 - 1 = d by omega] at hrefl
  rw [← hrefl]
  refine sum_congr rfl fun j hj => ?_
  have hj' := mem_Ico.1 hj
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [Nat.cast_sub hj'.2.le]
  congr 1
  rw [← Real.cos_pi_div_two_sub]
  congr 1
  field_simp
  ring

/-- From the clock-model form to the linear form: if `F = ∑_{m=1}^{d-1} csc(π m/(2d)) N(m)` (QD-L7) then
`4F/(d(d-1)) = I_ME(d) + 2/(d(d-1)) ⟨v, δ⟩` with `δ_m = N(m) - m` and `v_m = 2 csc(π m/(2d))`. -/
theorem clock_value_eq_linear (d : ℕ) (N : ℕ → ℝ) :
    4 / ((d : ℝ) * ((d : ℝ) - 1)) * ∑ m ∈ Ico 1 d, N m / Real.sin (π * m / (2 * d)) =
      IME d + 2 / ((d : ℝ) * ((d : ℝ) - 1)) * pairingIco d (coneV d) (fun m => N m - m) := by
  rw [IME_eq_sum_csc]
  unfold pairingIco coneV
  rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun m _ => ?_
  ring

end Bridges

/-! ## The chain -/

section Chain

variable {d : ℕ}

/-- `⟨v, δ⟩ = ∑_k λ_k ⟨u^{ℓ_k}, δ⟩` for a cone representation of `v`. -/
lemma pairing_coneV_eq_sum {K : ℕ} {ell : Fin K → ℕ → ℝ} {lam : Fin K → ℝ}
    (hl : ∀ k, IsConeCell d (ell k))
    (hv : ∀ m : ℕ, 1 ≤ m → m ≤ d - 1 → ∑ k, lam k * coneU d (ell k) m = coneV d m) (δ : ℕ → ℝ) :
    pairingIco d (coneV d) δ = ∑ k, lam k * pairingIco d (cellDirection d (ell k)) δ := by
  unfold pairingIco
  have e : ∀ m ∈ Ico 1 d, coneV d m * δ m = ∑ k, lam k * (cellDirection d (ell k) m * δ m) := by
    intro m hm
    have hm' := mem_Ico.1 hm
    rw [← hv m hm'.1 (by omega), sum_mul]
    refine sum_congr rfl fun k _ => ?_
    rw [cellDirection_eq_coneU (hl k) hm'.1 (by omega)]
    ring
  rw [sum_congr rfl e, sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_sum]

variable [NeZero d]

/-- **The CONE step (QD2-R1).** If the cell inequalities hold and `CONE_d` holds, then `⟨v, δ⟩ ≤ 0` for
every 27B configuration: `⟨v, δ⟩ = ∑_k λ_k ⟨u^{ℓ_k}, δ⟩` is a finite sum of nonpositive terms. -/
theorem pairing_coneV_nonpos (hcell : Hyp_CellInequalities d) (hcone : ConeCert d) {M : ℕ}
    (hM : 0 < M) (C : QConfig d M) : pairingIco d (coneV d) C.delta ≤ 0 := by
  obtain ⟨K, ell, lam, hl, hlam, hv⟩ := hcone
  rw [pairing_coneV_eq_sum hl hv]
  exact sum_nonpos fun k _ => mul_nonpos_of_nonneg_of_nonpos (hlam k) (hcell M hM C (ell k) (hl k))

/-- **Step 1 of the rigidity chain** (`RIGIDITY_ALLD.md` s.2): if `⟨v, δ⟩ = 0`, then some cell
inequality with all cells positive is tight. -/
theorem exists_pos_cell_tight (hcell : Hyp_CellInequalities d) (hcone : ConeCertPos d) {M : ℕ}
    (hM : 0 < M) (C : QConfig d M) (h0 : pairingIco d (coneV d) C.delta = 0) :
    ∃ ell : ℕ → ℝ, IsPosConeCell d ell ∧ pairingIco d (cellDirection d ell) C.delta = 0 := by
  obtain ⟨K, ell, lam, hl, hlam, hv, k₀, hk₀, hpos⟩ := hcone
  rw [pairing_coneV_eq_sum hl hv] at h0
  have hnp : ∀ k ∈ (univ : Finset (Fin K)), lam k * pairingIco d (cellDirection d (ell k)) C.delta ≤ 0 :=
    fun k _ => mul_nonpos_of_nonneg_of_nonpos (hlam k) (hcell M hM C (ell k) (hl k))
  have hzero := (sum_eq_zero_iff_of_nonpos hnp).1 h0 k₀ (mem_univ k₀)
  refine ⟨ell k₀, ⟨hl k₀, hpos⟩, ?_⟩
  rcases mul_eq_zero.1 hzero with h | h
  · exact absurd h hk₀.ne'
  · exact h

omit [NeZero d] in
lemma chain_two_div_pos (hd : 2 ≤ d) : 0 < 2 / ((d : ℝ) * ((d : ℝ) - 1)) := by
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  apply div_pos two_pos
  nlinarith

/-- **Optimality from the cell inequalities, `CONE_d` and the reduction.** -/
theorem optimality_of_cells (hd : 2 ≤ d) (hcell : Hyp_CellInequalities d) (hcone : ConeCert d)
    (hred : Hyp_Reduction d) : OptimalityStatement d := by
  intro D hD S
  obtain ⟨M, hM, C, hS⟩ := hred D hD S
  rw [hS]
  have := pairing_coneV_nonpos hcell hcone hM C
  have := chain_two_div_pos hd
  nlinarith

/-- **Optimality from the strip inequality** (and the continuum theorem, `CONE_d`, the reduction). -/
theorem optimality_of_strip (hd : 2 ≤ d) (hstrip : Hyp_StripInequality)
    (hcont : Hyp_ContinuumCell d) (hcone : ConeCert d) (hred : Hyp_Reduction d) :
    OptimalityStatement d :=
  optimality_of_cells hd (hcont hstrip) hcone hred

/-- **Rigidity from the cell inequalities, their equality case, `CONE_d` (with a positive cell vector)
and the reduction with its rigidity clause.** -/
theorem rigidity_of_cells (hd : 2 ≤ d) (hcell : Hyp_CellInequalities d)
    (hcellEq : Hyp_CellEquality d) (hcone : ConeCertPos d) (hred : Hyp_ReductionRig d) :
    RigidityStatement d := by
  intro D hD S hS
  obtain ⟨M, hM, C, hval, hrig⟩ := hred D hD S
  have h0 : pairingIco d (coneV d) C.delta = 0 := by
    have hpos := chain_two_div_pos hd
    rw [hS] at hval
    have : 2 / ((d : ℝ) * ((d : ℝ) - 1)) * pairingIco d (coneV d) C.delta = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hpos.ne'
    · exact h
  obtain ⟨ell, hell, htight⟩ := exists_pos_cell_tight hcell hcone hM C h0
  exact hrig (hcellEq M hM C ell hell htight) hS

/-- **Rigidity from the strip inequality and its equality case.** -/
theorem rigidity_of_strip (hd : 2 ≤ d) (hstrip : Hyp_StripInequality)
    (hstripEq : Hyp_StripEquality) (hcont : Hyp_ContinuumCell d) (hcontEq : Hyp_ContinuumCellEq d)
    (hcone : ConeCertPos d) (hred : Hyp_ReductionRig d) : RigidityStatement d :=
  rigidity_of_cells hd (hcont hstrip) (hcontEq hstrip hstripEq) hcone hred

/-- **The max-ent clause of OQP 27B for `d` outcomes** from the named hypotheses. -/
theorem maxEntClause_of_strip (hd : 2 ≤ d) (hstrip : Hyp_StripInequality)
    (hstripEq : Hyp_StripEquality) (hcont : Hyp_ContinuumCell d) (hcontEq : Hyp_ContinuumCellEq d)
    (hcone : ConeCertPos d) (hred : Hyp_ReductionRig d) : MaxEntClause d :=
  ⟨optimality_of_strip hd hstrip hcont hcone.coneCert hred.reduction,
    rigidity_of_strip hd hstrip hstripEq hcont hcontEq hcone hred⟩

end Chain

/-- **The max-ent clause of OQP 27B for every `d ≥ 2`**, from the named hypotheses for every `d`;
the value `I_ME(d)` is attained by the DKZ strategy (`OQP27.dkz_cglmp`, proved). -/
theorem maxEntClause_all_d (hstrip : Hyp_StripInequality) (hstripEq : Hyp_StripEquality)
    (hcont : ∀ d [NeZero d], 2 ≤ d → Hyp_ContinuumCell d)
    (hcontEq : ∀ d [NeZero d], 2 ≤ d → Hyp_ContinuumCellEq d)
    (hcone : ∀ d [NeZero d], 2 ≤ d → ConeCertPos d)
    (hred : ∀ d [NeZero d], 2 ≤ d → Hyp_ReductionRig d) (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    MaxEntClause d ∧ (dkz d).cglmp = IME d :=
  ⟨maxEntClause_of_strip hd hstrip hstripEq (hcont d hd) (hcontEq d hd) (hcone d hd) (hred d hd),
    dkz_cglmp hd⟩

end OQP27
