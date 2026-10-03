import OQP27.CertDefs
import OQP27.CertInterval
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field

/-!
# The verified interface: certificate ⇒ CONE_d (module L4)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

**Certificate format** (`OQP27.ConeCertificate`), as produced by `QD2/verify_cone.py`:
* `d`, a denominator `q > 0` and `K` cells `ℓ^(k) = n^(k)/q`, `n^(k)` natural vectors with `∑_{r<d} n^(k)_r = d q`
  (zero entries allowed);
* rational approximate weights `λ̃_k` (`lam`);
* a rational `(d-1) × (d-1)` matrix `R` (an approximate inverse of `W = U Uᵀ`);
* two rational numbers `eps`, `beta`.

**Residual-correction scheme** (the one of `QD2/verify_cone.py`, function `verify`).  Let `U` be the real
`(d-1) × K` matrix `U_{m,k} = u^{ℓ^(k)}_{m+1}` and `v_m = v_{m+1}`.  Given rational intervals `UI`, `vI` enclosing
`U` and `v` entrywise, the checker `OQP27.coneCheckCore` verifies, in exact rational interval arithmetic:
1. `0 ≤ eps < 1`, `0 ≤ beta`;
2. for every row `i`: `∑_j |I - R W|_{ij} ≤ eps`, with `W = U Uᵀ` (interval enclosure);
3. for every row `i`: `|R (v - U λ̃)|_i ≤ beta`;
4. for every column `k`: `λ̃_k - (∑_m |U_{m,k}|) · beta/(1 - eps) > 0`.

**Interface theorem** (`OQP27.ConeCertificate.sound`): if the cells are valid and the four checks pass for some
interval enclosures of the entries of `U` and `v`, then `OQP27.ConeCert d` (`OQP27.ConeCertificate.sound_strong`:
moreover every weight is positive).  Proof: by (2) and `eps < 1`, `W` is
injective, hence invertible (finite dimension); the exact solution `y` of `W y = v - U λ̃` satisfies
`‖y‖_∞ ≤ beta/(1 - eps)` (from `y = (I - R W) y + R (v - U λ̃)`), and `λ = λ̃ + Uᵀ y` satisfies `U λ = v` exactly,
with `λ_k > 0` by (4).

No hypotheses; the enclosures of `U` and `v` are inputs of the interface theorem.  They are produced, with
soundness proofs, in `OQP27/CertTrig.lean`, `OQP27/CertClausen.lean` and `OQP27/CertPipeline.lean`.
-/

namespace OQP27

open Finset Matrix

/-! ### Linear algebra: an approximate inverse certifies solvability -/

theorem norm_le_of_approx_inverse {n : ℕ} (W R : Matrix (Fin n) (Fin n) ℝ) {eps : ℝ} (heps0 : 0 ≤ eps)
    (hE : ∀ i, ∑ j, |(1 - R * W) i j| ≤ eps) (z : Fin n → ℝ) :
    ‖z‖ ≤ eps * ‖z‖ + ‖R *ᵥ (W *ᵥ z)‖ := by
  have hz : z = (1 - R * W) *ᵥ z + R *ᵥ (W *ᵥ z) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]; abel
  have hnn : 0 ≤ eps * ‖z‖ + ‖R *ᵥ (W *ᵥ z)‖ := by positivity
  refine (pi_norm_le_iff_of_nonneg hnn).mpr fun i => ?_
  have h1 : ‖((1 - R * W) *ᵥ z) i‖ ≤ eps * ‖z‖ := by
    rw [Real.norm_eq_abs]
    calc |((1 - R * W) *ᵥ z) i| = |∑ j, (1 - R * W) i j * z j| := rfl
      _ ≤ ∑ j, |(1 - R * W) i j * z j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |(1 - R * W) i j| * |z j| := by simp_rw [abs_mul]
      _ ≤ ∑ j, |(1 - R * W) i j| * ‖z‖ := by
          gcongr with j
          rw [← Real.norm_eq_abs]; exact norm_le_pi_norm z j
      _ = (∑ j, |(1 - R * W) i j|) * ‖z‖ := by rw [Finset.sum_mul]
      _ ≤ eps * ‖z‖ := by gcongr; exact hE i
  have h2 : ‖(R *ᵥ (W *ᵥ z)) i‖ ≤ ‖R *ᵥ (W *ᵥ z)‖ := norm_le_pi_norm _ i
  calc ‖z i‖ = ‖((1 - R * W) *ᵥ z) i + (R *ᵥ (W *ᵥ z)) i‖ := by
        conv_lhs => rw [hz]
        rfl
    _ ≤ ‖((1 - R * W) *ᵥ z) i‖ + ‖(R *ᵥ (W *ᵥ z)) i‖ := norm_add_le _ _
    _ ≤ eps * ‖z‖ + ‖R *ᵥ (W *ᵥ z)‖ := add_le_add h1 h2

/-- If `R` is an approximate inverse of `W` with `‖I - R W‖_∞ ≤ eps < 1`, then `W y = b` has a solution with
`‖y‖_∞ ≤ ‖R b‖_∞ / (1 - eps)`. -/
theorem exists_solve_of_approx_inverse {n : ℕ} (W R : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    {eps beta : ℝ} (heps0 : 0 ≤ eps) (heps : eps < 1) (hbeta : 0 ≤ beta)
    (hE : ∀ i, ∑ j, |(1 - R * W) i j| ≤ eps) (hb : ∀ i, |(R *ᵥ b) i| ≤ beta) :
    ∃ y : Fin n → ℝ, W *ᵥ y = b ∧ ∀ i, |y i| ≤ beta / (1 - eps) := by
  have hpos : 0 < 1 - eps := by linarith
  have hinj : Function.Injective W.mulVecLin := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    rw [Matrix.mulVecLin_apply] at hz
    have h := norm_le_of_approx_inverse W R heps0 hE z
    rw [hz, Matrix.mulVec_zero, norm_zero, add_zero] at h
    have h0 : ‖z‖ ≤ 0 := by nlinarith [norm_nonneg z]
    exact norm_le_zero_iff.mp h0
  obtain ⟨y, hy⟩ := LinearMap.injective_iff_surjective.mp hinj b
  rw [Matrix.mulVecLin_apply] at hy
  refine ⟨y, hy, fun i => ?_⟩
  have hRb : ‖R *ᵥ b‖ ≤ beta := by
    refine (pi_norm_le_iff_of_nonneg hbeta).mpr fun j => ?_
    rw [Real.norm_eq_abs]; exact hb j
  have h := norm_le_of_approx_inverse W R heps0 hE y
  rw [hy] at h
  have hy' : ‖y‖ ≤ beta / (1 - eps) := by
    rw [le_div_iff₀ hpos]; nlinarith
  calc |y i| = ‖y i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖y‖ := norm_le_pi_norm y i
    _ ≤ beta / (1 - eps) := hy'

/-! ### The checker -/

/-- The core cone check (residual-correction scheme of `QD2/verify_cone.py`).  Rows `i < n`, columns `k < K`;
`UI i k` and `vI i` are interval enclosures of `U_{i,k}` and `v_i`. -/
def coneCheckCore (n K : ℕ) (UI : ℕ → ℕ → QI) (vI : ℕ → QI) (lam : ℕ → ℚ) (R : ℕ → ℕ → ℚ)
    (eps beta : ℚ) : Bool :=
  let W : List (List QI) := (List.range n).map fun i => (List.range n).map fun j =>
    QI.round 100 (QI.sumRange K fun k => QI.mul (UI i k) (UI j k))
  let WI : ℕ → ℕ → QI := fun i j => (W.getD i []).getD j default
  let EI : ℕ → ℕ → QI := fun i j =>
    QI.sub (QI.pt (if i = j then 1 else 0)) (QI.sumRange n fun l => QI.smul (R i l) (WI l j))
  let res : List QI := (List.range n).map fun i =>
    QI.round 100 (QI.sub (vI i) (QI.sumRange K fun k => QI.smul (lam k) (UI i k)))
  let resI : ℕ → QI := fun i => res.getD i default
  let RrI : ℕ → QI := fun i => QI.sumRange n fun l => QI.smul (R i l) (resI l)
  decide (0 ≤ eps) && decide (eps < 1) && decide (0 ≤ beta) &&
    (List.range n).all (fun i => decide (∑ j ∈ range n, (EI i j).mag ≤ eps)) &&
    (List.range n).all (fun i => decide ((RrI i).mag ≤ beta)) &&
    (List.range K).all (fun k => decide (0 < lam k - (∑ i ∈ range n, (UI i k).mag) * (beta / (1 - eps))))

theorem coneCheckCore_sound {n K : ℕ} {UI : ℕ → ℕ → QI} {vI : ℕ → QI} {lam : ℕ → ℚ}
    {R : ℕ → ℕ → ℚ} {eps beta : ℚ} (U : ℕ → ℕ → ℝ) (v : ℕ → ℝ)
    (hU : ∀ i < n, ∀ k < K, (UI i k).Mem (U i k)) (hv : ∀ i < n, (vI i).Mem (v i))
    (hc : coneCheckCore n K UI vI lam R eps beta = true) :
    ∃ x : ℕ → ℝ, (∀ k < K, 0 < x k) ∧ ∀ i < n, ∑ k ∈ range K, U i k * x k = v i := by
  unfold coneCheckCore at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨heps0, heps1⟩, hbeta0⟩, hrows⟩, hRr⟩, hcols⟩ := hc
  -- the real matrices
  set Wr : ℕ → ℕ → ℝ := fun i j => ∑ k ∈ range K, U i k * U j k with hWr
  set res : ℕ → ℝ := fun i => v i - ∑ k ∈ range K, (lam k : ℝ) * U i k with hres
  -- enclosures
  have hW : ∀ i < n, ∀ j < n, ((((List.range n).map fun i => (List.range n).map fun j =>
      QI.round 100 (QI.sumRange K fun k => QI.mul (UI i k) (UI j k))).getD i []).getD j default).Mem
      (Wr i j) := by
    intro i hi j hj
    rw [QI.getD_map_range _ _ _ hi, QI.getD_map_range _ _ _ hj]
    exact QI.Mem.round 100 (QI.mem_sumRange fun k hk => (hU i hi k hk).mul (hU j hj k hk))
  have hresI : ∀ i < n, (((List.range n).map fun i =>
      QI.round 100 (QI.sub (vI i) (QI.sumRange K fun k => QI.smul (lam k) (UI i k)))).getD i default).Mem
      (res i) := by
    intro i hi
    rw [QI.getD_map_range _ _ _ hi]
    exact QI.Mem.round 100 ((hv i hi).sub (QI.mem_sumRange fun k hk => (hU i hi k hk).smul (lam k)))
  -- Fin matrices
  let Wm : Matrix (Fin n) (Fin n) ℝ := fun i j => Wr i j
  let Rm : Matrix (Fin n) (Fin n) ℝ := fun i j => (R i j : ℝ)
  let bv : Fin n → ℝ := fun i => res i
  have hE : ∀ i : Fin n, ∑ j, |(1 - Rm * Wm) i j| ≤ (eps : ℝ) := by
    intro i
    have hrow := hrows i i.2
    have hrowR : (∑ j ∈ range n, ((QI.sub (QI.pt (if (i : ℕ) = j then 1 else 0))
        (QI.sumRange n fun l => QI.smul (R i l) ((((List.range n).map fun i => (List.range n).map fun j =>
          QI.round 100 (QI.sumRange K fun k => QI.mul (UI i k) (UI j k))).getD l []).getD j default))).mag : ℝ))
        ≤ (eps : ℝ) := by exact_mod_cast hrow
    refine le_trans ?_ hrowR
    rw [← Fin.sum_univ_eq_sum_range (fun j => ((QI.sub (QI.pt (if (i : ℕ) = j then 1 else 0))
        (QI.sumRange n fun l => QI.smul (R i l) ((((List.range n).map fun i => (List.range n).map fun j =>
          QI.round 100 (QI.sumRange K fun k => QI.mul (UI i k) (UI j k))).getD l []).getD j default))).mag : ℝ))]
    refine Finset.sum_le_sum fun j _ => ?_
    apply QI.Mem.abs_le_mag
    have hentry : (1 - Rm * Wm) i j = (if (i : ℕ) = (j : ℕ) then (1 : ℝ) else 0) -
        ∑ l ∈ range n, (R i l : ℝ) * Wr l j := by
      rw [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply,
        ← Fin.sum_univ_eq_sum_range (fun l => (R i l : ℝ) * Wr l j)]
      simp only [Fin.val_inj, Rm, Wm]
    rw [hentry]
    have h1 : (QI.pt (if (i : ℕ) = (j : ℕ) then 1 else 0)).Mem (if (i : ℕ) = (j : ℕ) then (1 : ℝ) else 0) := by
      split_ifs
      · have h := QI.mem_pt (1 : ℚ); rwa [Rat.cast_one] at h
      · have h := QI.mem_pt (0 : ℚ); rwa [Rat.cast_zero] at h
    exact h1.sub (QI.mem_sumRange fun l hl => (hW l hl j j.2).smul (R i l))
  have hb : ∀ i : Fin n, |(Rm *ᵥ bv) i| ≤ (beta : ℝ) := by
    intro i
    have h := hRr i i.2
    have hR : ((QI.sumRange n fun l => QI.smul (R i l) ((((List.range n).map fun i =>
        QI.round 100 (QI.sub (vI i) (QI.sumRange K fun k => QI.smul (lam k) (UI i k)))).getD l default))).Mem
        (∑ l ∈ range n, (R i l : ℝ) * res l)) :=
      QI.mem_sumRange fun l hl => (hresI l hl).smul (R i l)
    have hval : (Rm *ᵥ bv) i = ∑ l ∈ range n, (R i l : ℝ) * res l := by
      rw [← Fin.sum_univ_eq_sum_range (fun l => (R i l : ℝ) * res l)]
      rfl
    rw [hval]
    exact (hR.abs_le_mag).trans (by exact_mod_cast h)
  have heps0' : (0 : ℝ) ≤ eps := by exact_mod_cast heps0
  have heps1' : (eps : ℝ) < 1 := by exact_mod_cast heps1
  have hbeta0' : (0 : ℝ) ≤ beta := by exact_mod_cast hbeta0
  obtain ⟨y, hy, hybd⟩ := exists_solve_of_approx_inverse Wm Rm bv heps0' heps1' hbeta0' hE hb
  -- extend y to ℕ
  let yN : ℕ → ℝ := fun i => if h : i < n then y ⟨i, h⟩ else 0
  have hyN : ∀ (i : ℕ) (hi : i < n), yN i = y ⟨i, hi⟩ := fun i hi => by simp [yN, hi]
  have hyNbd : ∀ i < n, |yN i| ≤ (beta : ℝ) / (1 - eps) := fun i hi => by rw [hyN i hi]; exact hybd _
  refine ⟨fun k => (lam k : ℝ) + ∑ i ∈ range n, U i k * yN i, ?_, ?_⟩
  · -- positivity of the corrected weights
    intro k hk
    have hcol := hcols k hk
    have hcol' : (0 : ℝ) < (lam k : ℝ) - (∑ i ∈ range n, ((UI i k).mag : ℝ)) * ((beta : ℝ) / (1 - eps)) := by
      exact_mod_cast hcol
    have hcorr : |∑ i ∈ range n, U i k * yN i| ≤
        (∑ i ∈ range n, ((UI i k).mag : ℝ)) * ((beta : ℝ) / (1 - eps)) := by
      calc |∑ i ∈ range n, U i k * yN i| ≤ ∑ i ∈ range n, |U i k * yN i| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ i ∈ range n, |U i k| * |yN i| := by simp_rw [abs_mul]
        _ ≤ ∑ i ∈ range n, ((UI i k).mag : ℝ) * ((beta : ℝ) / (1 - eps)) := by
            refine Finset.sum_le_sum fun i hi => ?_
            have hi' := Finset.mem_range.mp hi
            exact mul_le_mul ((hU i hi' k hk).abs_le_mag) (hyNbd i hi') (abs_nonneg _)
              ((abs_nonneg _).trans ((hU i hi' k hk).abs_le_mag))
        _ = (∑ i ∈ range n, ((UI i k).mag : ℝ)) * ((beta : ℝ) / (1 - eps)) := by rw [Finset.sum_mul]
    have := neg_abs_le (∑ i ∈ range n, U i k * yN i)
    linarith
  · -- the equation U x = v
    intro i hi
    have hyi : ∑ l ∈ range n, Wr i l * yN l = res i := by
      have h := congrFun hy ⟨i, hi⟩
      have hl : (Wm *ᵥ y) ⟨i, hi⟩ = ∑ l ∈ range n, Wr i l * yN l := by
        rw [← Fin.sum_univ_eq_sum_range (fun l => Wr i l * yN l)]
        simp only [Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl fun l _ => ?_
        have e : yN (l : ℕ) = y l := hyN l l.2
        rw [e]
        try rfl
      rw [← hl, h]
    have hexp : ∑ k ∈ range K, U i k * ((lam k : ℝ) + ∑ l ∈ range n, U l k * yN l) =
        ∑ k ∈ range K, (lam k : ℝ) * U i k + ∑ l ∈ range n, Wr i l * yN l := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, hWr, Finset.sum_mul]
      congr 1
      · exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
    rw [hexp, hyi, hres]
    ring

/-! ### Certificates for CONE_d -/

/-- A CONE_d certificate: cells `ℓ^(k) = n^(k)/q`, approximate weights `λ̃`, an approximate inverse `R` of
`U Uᵀ`, and the bounds `eps`, `beta` (see the module docstring). -/
structure ConeCertificate where
  d : ℕ
  q : ℕ
  cells : List (List ℕ)
  lam : List ℚ
  R : List (List ℚ)
  eps : ℚ
  beta : ℚ

/-- The real cell vector `ℓ_r = n_r / q`. -/
noncomputable def cellVec (q : ℕ) (n : List ℕ) : ℕ → ℝ := fun r => (n.getD r 0 : ℝ) / q

namespace ConeCertificate

/-- The cells are valid: `q > 0` and `∑_{r<d} n_r = d q` for every cell. -/
def cellsOK (c : ConeCertificate) : Bool :=
  decide (0 < c.q) && c.cells.all fun n => decide (∑ r ∈ range c.d, n.getD r 0 = c.d * c.q)

def lamF (c : ConeCertificate) : ℕ → ℚ := fun k => c.lam.getD k 0

def RF (c : ConeCertificate) : ℕ → ℕ → ℚ := fun i j => (c.R.getD i []).getD j 0

/-- The real matrix `U_{i,k} = u^{ℓ^(k)}_{i+1}` (`i < d-1`, `k < K`). -/
noncomputable def Umat (c : ConeCertificate) : ℕ → ℕ → ℝ :=
  fun i k => coneU c.d (cellVec c.q (c.cells.getD k [])) (i + 1)

/-- The check of a certificate, given interval enclosures `UI`, `vI` of the entries of `U` and `v`. -/
def check (c : ConeCertificate) (UI : ℕ → ℕ → QI) (vI : ℕ → QI) : Bool :=
  c.cellsOK && coneCheckCore (c.d - 1) c.cells.length UI vI c.lamF c.RF c.eps c.beta

theorem isConeCell_cellVec {d q : ℕ} {n : List ℕ} (hq : 0 < q)
    (hsum : ∑ r ∈ range d, n.getD r 0 = d * q) : IsConeCell d (cellVec q n) := by
  refine ⟨fun r _ => by unfold cellVec; positivity, ?_⟩
  unfold cellVec
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [← Finset.sum_div, div_eq_iff hq']
  exact_mod_cast hsum

/-- **The verified interface, strong form.**  A certificate whose check passes, for some rational interval
enclosures `UI`, `vI` of the entries `u^{ℓ^(k)}_{i+1}` and `v_{i+1}` (`i < d-1`): all its cells are cell vectors
and there are weights `λ_k > 0` (every `k`) with `∑_k λ_k u^{ℓ^(k)}_m = v_m` for `m = 1, …, d-1`. -/
theorem sound_strong (c : ConeCertificate) (UI : ℕ → ℕ → QI) (vI : ℕ → QI)
    (hU : ∀ i < c.d - 1, ∀ k < c.cells.length, (UI i k).Mem (c.Umat i k))
    (hv : ∀ i < c.d - 1, (vI i).Mem (coneV c.d (i + 1)))
    (hc : c.check UI vI = true) :
    (∀ k < c.cells.length, IsConeCell c.d (cellVec c.q (c.cells.getD k []))) ∧
      ∃ x : ℕ → ℝ, (∀ k < c.cells.length, 0 < x k) ∧
        ∀ m : ℕ, 1 ≤ m → m ≤ c.d - 1 →
          ∑ k : Fin c.cells.length, x k * coneU c.d (cellVec c.q (c.cells.getD k [])) m = coneV c.d m := by
  unfold check at hc
  rw [Bool.and_eq_true] at hc
  obtain ⟨hcells, hcore⟩ := hc
  unfold cellsOK at hcells
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hcells
  obtain ⟨hq, hsums⟩ := hcells
  obtain ⟨x, hxpos, hxeq⟩ := coneCheckCore_sound c.Umat (fun i => coneV c.d (i + 1)) hU hv hcore
  refine ⟨fun k hk => ?_, x, hxpos, fun m hm1 hm2 => ?_⟩
  · refine isConeCell_cellVec hq ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    exact hsums _ (List.getElem_mem _)
  · have hi : m - 1 < c.d - 1 := by omega
    have h := hxeq (m - 1) hi
    have hm : m - 1 + 1 = m := by omega
    simp only [Umat, hm] at h
    rw [← h, ← Fin.sum_univ_eq_sum_range (fun k => coneU c.d (cellVec c.q (c.cells.getD k [])) m * x k)]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **The verified interface.**  A certificate whose check passes, for some rational interval enclosures `UI`,
`vI` of the entries `u^{ℓ^(k)}_{i+1}` and `v_{i+1}` (`i < d-1`), proves `CONE_d`. -/
theorem sound (c : ConeCertificate) (UI : ℕ → ℕ → QI) (vI : ℕ → QI)
    (hU : ∀ i < c.d - 1, ∀ k < c.cells.length, (UI i k).Mem (c.Umat i k))
    (hv : ∀ i < c.d - 1, (vI i).Mem (coneV c.d (i + 1)))
    (hc : c.check UI vI = true) : ConeCert c.d := by
  obtain ⟨hcell, x, hxpos, hxeq⟩ := c.sound_strong UI vI hU hv hc
  exact ⟨c.cells.length, fun k => cellVec c.q (c.cells.getD k []), fun k => x k,
    fun k => hcell k k.2, fun k => (hxpos k k.2).le, hxeq⟩

end ConeCertificate

end OQP27
