import OQP27.StripJensen
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Instances.Matrix

/-!
# The pencil `det (H - y (P - τ))`, the density `F`, and Lemma 1 (module L3b)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

Conventions: `P` is an orthogonal projection on `ℂ^M` (`IsProj P`), `B = 1 - P`, `H_d = B H B + P H P`
(`pinch P H`).  For `0 < τ < 1` the pencil roots `pencilRoots P H τ` are the eigenvalues (with
multiplicity) of `(P - τ)⁻¹ H`; by `pencilRoots_eq_roots_det` they are exactly the roots of the
polynomial `y ↦ det (H - y (P - τ))`.  The density of Theorem 1 is
`stripF P g s τ = (1/2π) ∑_i |Im x_i(s, τ)|` (`x_i` the pencil roots of `g - s`) for `0 < τ < 1`, and `0`
otherwise.

Proved here (no hypotheses, no `sorry`):
* `inv_P_sub`: `(P - τ)⁻¹ = (1 - τ)⁻¹ P - τ⁻¹ B`; `pencilRoots_add_smul`: adding `ξ (P - τ)` to `H`
  shifts the roots by `ξ`;
* Lemma 1(d) `pencilRoots_pinch_im`: the pinched pencil has only real roots;
* Lemma 1(e) `sum_pencilRoots_pinch`: the two pencils have the same root sum (both characteristic
  polynomials are monic of degree `M`; `det_pencil` gives the common leading coefficient
  `det (-(P - τ))` of the paper's normalisation);
* `stripF_nonneg`, `measurable_stripF` (joint measurability of `F`);
* `stripF_eq_jensen`: `F = (1/2π²) ∫_ℝ log |p/q|` (the paper's eq. (3.4)), from Lemma 2.

No hypotheses remain in this file.  Lemma 1(b),(c) are in `OQP27/StripBounds.lean`.
Paper: `iqoqi/programs/oqp27B_all/Q_2bmv/PROOF.md`, Lemma 1 and eq. (3.4).
-/

namespace OQP27.StripL3b

open Matrix Polynomial MeasureTheory Filter Topology Real

variable {M : ℕ}

/-- `P` is an orthogonal projection. -/
def IsProj (P : Matrix (Fin M) (Fin M) ℂ) : Prop := P.IsHermitian ∧ P * P = P

/-- The pinching `H_d = B H B + P H P`, `B = 1 - P`. -/
def pinch (P H : Matrix (Fin M) (Fin M) ℂ) : Matrix (Fin M) (Fin M) ℂ :=
  (1 - P) * H * (1 - P) + P * H * P

/-- The pencil roots at `τ`: the eigenvalues (with multiplicity) of `(P - τ)⁻¹ H`, i.e. the roots of
`y ↦ det (H - y (P - τ))` for `0 < τ < 1` (see `det_pencil`). -/
noncomputable def pencilRoots (P H : Matrix (Fin M) (Fin M) ℂ) (τ : ℝ) : Multiset ℂ :=
  (((P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹ * H).charpoly).roots

/-- `∑ |Im z|` over a multiset of complex numbers. -/
noncomputable def imAbsSum (S : Multiset ℂ) : ℝ := (S.map fun z => |z.im|).sum

/-- The density `F(s, τ) = (1/2π) ∑_i |Im x_i(s, τ)|` for `0 < τ < 1` (and `0` otherwise), where
`x_i(s, τ)` are the roots of `det (g - s - x (P - τ))`. -/
noncomputable def stripF (P g : Matrix (Fin M) (Fin M) ℂ) (s τ : ℝ) : ℝ :=
  if 0 < τ ∧ τ < 1 then imAbsSum (pencilRoots P (g - (s : ℂ) • 1) τ) / (2 * π) else 0

lemma imAbsSum_nonneg (S : Multiset ℂ) : 0 ≤ imAbsSum S :=
  Multiset.sum_nonneg fun x hx => by
    obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp hx
    exact abs_nonneg _

lemma stripF_nonneg (P g : Matrix (Fin M) (Fin M) ℂ) (s τ : ℝ) : 0 ≤ stripF P g s τ := by
  unfold stripF
  split_ifs
  · exact div_nonneg (imAbsSum_nonneg _) (by positivity)
  · exact le_rfl

lemma stripF_of_not_mem {P g : Matrix (Fin M) (Fin M) ℂ} {s τ : ℝ} (h : ¬ (0 < τ ∧ τ < 1)) :
    stripF P g s τ = 0 := by
  simp [stripF, h]

lemma imAbsSum_map_add_ofReal (S : Multiset ℂ) (ξ : ℝ) :
    imAbsSum (S.map (· + (ξ : ℂ))) = imAbsSum S := by
  simp [imAbsSum, Multiset.map_map]

/-! ### The inverse of `P - τ` -/

section Inverse

variable {P : Matrix (Fin M) (Fin M) ℂ}

lemma proj_mul_compl (hP : P * P = P) : P * (1 - P) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, hP, sub_self]

lemma compl_mul_proj (hP : P * P = P) : (1 - P) * P = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, hP, sub_self]

/-- `(P - τ) ((1 - τ)⁻¹ P - τ⁻¹ (1 - P)) = 1` for `τ ∉ {0, 1}`. -/
lemma P_sub_mul_explicit {τ : ℝ} (hP : P * P = P) (h0 : τ ≠ 0) (h1 : τ ≠ 1) :
    (P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))
      * (((1 - (τ : ℂ))⁻¹) • P - ((τ : ℂ)⁻¹) • (1 - P)) = 1 := by
  have hτ : (τ : ℂ) ≠ 0 := by exact_mod_cast h0
  have hτ1 : (1 - (τ : ℂ)) ≠ 0 := by
    intro h; apply h1; exact_mod_cast (sub_eq_zero.mp h).symm
  set a : ℂ := (1 - (τ : ℂ))⁻¹
  set b : ℂ := (τ : ℂ)⁻¹
  have ha : a * (1 - τ) = 1 := inv_mul_cancel₀ hτ1
  have hb : b * τ = 1 := inv_mul_cancel₀ hτ
  have key : (P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)) * (a • P - b • (1 - P))
      = (a * (1 - τ)) • P + (b * τ) • (1 - P) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, hP]
    module
  rw [key, ha, hb, one_smul, one_smul]
  abel

/-- For `τ ∉ {0, 1}`: `(P - τ)⁻¹ = (1 - τ)⁻¹ P - τ⁻¹ (1 - P)`. -/
lemma inv_P_sub {τ : ℝ} (hP : P * P = P) (h0 : τ ≠ 0) (h1 : τ ≠ 1) :
    (P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹
      = ((1 - (τ : ℂ))⁻¹) • P - ((τ : ℂ)⁻¹) • (1 - P) :=
  Matrix.inv_eq_right_inv (P_sub_mul_explicit hP h0 h1)

lemma isUnit_det_P_sub {τ : ℝ} (hP : P * P = P) (h0 : τ ≠ 0) (h1 : τ ≠ 1) :
    IsUnit (P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)).det :=
  Matrix.isUnit_det_of_right_inverse (P_sub_mul_explicit hP h0 h1)

lemma inv_P_sub_mul_self {τ : ℝ} (hP : P * P = P) (h0 : τ ≠ 0) (h1 : τ ≠ 1) :
    (P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹ * (P - (τ : ℂ) • 1) = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_det_P_sub hP h0 h1)

end Inverse

/-! ### Shift of the pencil along `P - τ` -/

/-- Adding `ξ (P - τ)` to `H` shifts every pencil root by `ξ`. -/
lemma pencilRoots_add_smul {P H : Matrix (Fin M) (Fin M) ℂ} (hP : P * P = P) {τ : ℝ}
    (h0 : τ ≠ 0) (h1 : τ ≠ 1) (ξ : ℂ) :
    pencilRoots P (H + ξ • (P - (τ : ℂ) • 1)) τ = (pencilRoots P H τ).map (· + ξ) := by
  unfold pencilRoots
  rw [Matrix.mul_add, Matrix.mul_smul, inv_P_sub_mul_self hP h0 h1]
  have h2 : (P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹ * H + ξ • 1
      = (P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹ * H - Matrix.scalar (Fin M) (-ξ) := by
    rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, neg_smul, sub_neg_eq_add]
  rw [h2, Matrix.charpoly_sub_scalar]
  have h3 : (X + C (-ξ) : ℂ[X]) = C 1 * X + C (-ξ) := by simp
  rw [h3, Polynomial.roots_comp_C_mul_X_add_C _ 1 (-ξ) isUnit_one]
  congr 1
  funext x
  simp

/-! ### The pinching -/

section Pinch

variable {P : Matrix (Fin M) (Fin M) ℂ}

lemma pinch_add (P A B : Matrix (Fin M) (Fin M) ℂ) : pinch P (A + B) = pinch P A + pinch P B := by
  simp only [pinch, Matrix.mul_add, Matrix.add_mul]; abel

lemma pinch_sub (P A B : Matrix (Fin M) (Fin M) ℂ) : pinch P (A - B) = pinch P A - pinch P B := by
  simp only [pinch, Matrix.mul_sub, Matrix.sub_mul]; abel

lemma pinch_smul (P A : Matrix (Fin M) (Fin M) ℂ) (c : ℂ) : pinch P (c • A) = c • pinch P A := by
  simp only [pinch, Matrix.mul_smul, Matrix.smul_mul, smul_add]

lemma pinch_one (hP : P * P = P) : pinch P 1 = 1 := by
  have hBB : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, proj_mul_compl hP, sub_zero]
  simp only [pinch, Matrix.mul_one, hBB, hP]
  abel

lemma pinch_self (hP : P * P = P) : pinch P P = P := by
  simp only [pinch, compl_mul_proj hP, Matrix.zero_mul, hP, zero_add]

lemma isHermitian_pinch (hP : P.IsHermitian) {H : Matrix (Fin M) (Fin M) ℂ}
    (hH : H.IsHermitian) : (pinch P H).IsHermitian := by
  have hB : (1 - P).IsHermitian := isHermitian_one.sub hP
  unfold pinch
  have h1 := isHermitian_mul_mul_conjTranspose (1 - P) hH
  have h2 := isHermitian_mul_mul_conjTranspose P hH
  rw [hB.eq] at h1
  rw [hP.eq] at h2
  exact h1.add h2

lemma isSelfAdjoint_ofReal (r : ℝ) : IsSelfAdjoint (r : ℂ) := Complex.conj_ofReal r

/-- `(P - τ)⁻¹ H_d = (1 - τ)⁻¹ P H P - τ⁻¹ B H B`. -/
lemma inv_P_sub_mul_pinch {τ : ℝ} (hP : P * P = P) (h0 : τ ≠ 0) (h1 : τ ≠ 1)
    (H : Matrix (Fin M) (Fin M) ℂ) :
    (P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹ * pinch P H
      = ((1 - (τ : ℂ))⁻¹) • (P * H * P) - ((τ : ℂ)⁻¹) • ((1 - P) * H * (1 - P)) := by
  rw [inv_P_sub hP h0 h1]
  unfold pinch
  have hPB := proj_mul_compl hP
  have hBP := compl_mul_proj hP
  have hBB : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, hPB, sub_zero]
  set B := 1 - P
  simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, ← Matrix.mul_assoc, hP, hPB, hBP,
    hBB, Matrix.zero_mul, smul_zero]
  abel

/-- The pinched pencil `q` has only real roots (Lemma 1(d)): `(P - τ)⁻¹ H_d` is Hermitian. -/
lemma isHermitian_inv_P_sub_mul_pinch {τ : ℝ} (hP : IsProj P) (h0 : τ ≠ 0) (h1 : τ ≠ 1)
    {H : Matrix (Fin M) (Fin M) ℂ} (hH : H.IsHermitian) :
    ((P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹ * pinch P H).IsHermitian := by
  rw [inv_P_sub_mul_pinch hP.2 h0 h1]
  have hB : (1 - P).IsHermitian := isHermitian_one.sub hP.1
  have h2 := isHermitian_mul_mul_conjTranspose P hH
  have h3 := isHermitian_mul_mul_conjTranspose (1 - P) hH
  rw [hP.1.eq] at h2
  rw [hB.eq] at h3
  have e1 : (1 - (τ : ℂ))⁻¹ = (((1 - τ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  have e2 : (τ : ℂ)⁻¹ = ((τ⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [e1, e2]
  exact (h2.smul (isSelfAdjoint_ofReal _)).sub (h3.smul (isSelfAdjoint_ofReal _))

/-- Lemma 1(d): every root of the pinched pencil is real. -/
lemma pencilRoots_pinch_im {τ : ℝ} (hP : IsProj P) (h0 : τ ≠ 0) (h1 : τ ≠ 1)
    {H : Matrix (Fin M) (Fin M) ℂ} (hH : H.IsHermitian) :
    ∀ z ∈ pencilRoots P (pinch P H) τ, z.im = 0 := by
  intro z hz
  unfold pencilRoots at hz
  rw [(isHermitian_inv_P_sub_mul_pinch hP h0 h1 hH).roots_charpoly_eq_eigenvalues] at hz
  obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hz
  simp

/-- Lemma 1(e): `p` and `q` have the same sum of roots (both are monic of degree `M`). -/
lemma trace_inv_P_sub_mul_pinch {τ : ℝ} (hP : P * P = P) (h0 : τ ≠ 0) (h1 : τ ≠ 1)
    (H : Matrix (Fin M) (Fin M) ℂ) :
    ((P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹ * pinch P H).trace
      = ((P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹ * H).trace := by
  rw [inv_P_sub_mul_pinch hP h0 h1, inv_P_sub hP h0 h1]
  have hPB := proj_mul_compl hP
  have hBB : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, hPB, sub_zero]
  have t1 : (P * H * P).trace = (P * H).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hP]
  have t2 : ((1 - P) * H * (1 - P)).trace = ((1 - P) * H).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hBB]
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, t1, t2,
    Matrix.sub_mul (((1 - (τ : ℂ))⁻¹) • P), Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_smul]

lemma sum_pencilRoots_pinch {τ : ℝ} (hP : P * P = P) (h0 : τ ≠ 0) (h1 : τ ≠ 1)
    (H : Matrix (Fin M) (Fin M) ℂ) :
    (pencilRoots P (pinch P H) τ).sum = (pencilRoots P H τ).sum := by
  unfold pencilRoots
  rw [← Matrix.trace_eq_sum_roots_charpoly, ← Matrix.trace_eq_sum_roots_charpoly,
    trace_inv_P_sub_mul_pinch hP h0 h1]

end Pinch

/-! ### Measurability of `F` -/

/-- Explicit form of `(P - τ)⁻¹ (g - s)`, valid for `τ ∉ {0, 1}`. -/
noncomputable def pencilMatE (P g : Matrix (Fin M) (Fin M) ℂ) (s τ : ℝ) :
    Matrix (Fin M) (Fin M) ℂ :=
  ((((1 - τ)⁻¹ : ℝ) : ℂ) • P - ((τ⁻¹ : ℝ) : ℂ) • (1 - P)) * (g - (s : ℂ) • 1)

lemma pencilMatE_eq {P g : Matrix (Fin M) (Fin M) ℂ} (hP : P * P = P) {s τ : ℝ} (h0 : τ ≠ 0)
    (h1 : τ ≠ 1) :
    (P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹ * (g - (s : ℂ) • 1) = pencilMatE P g s τ := by
  rw [inv_P_sub hP h0 h1, pencilMatE]
  push_cast
  rfl

lemma measurable_log_det (P g : Matrix (Fin M) (Fin M) ℂ) :
    Measurable (fun q : (ℝ × ℝ) × ℝ =>
      Real.log ‖((q.2 : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ) - pencilMatE P g q.1.1 q.1.2).det‖) := by
  have hΦ : Continuous (fun v : ℝ × ℝ × ℝ × ℝ =>
      ((v.1 : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)
        - ((v.2.2.1 : ℂ) • P - (v.2.2.2 : ℂ) • (1 - P)) * (g - (v.2.1 : ℂ) • 1)).det) := by
    fun_prop
  have hin : Measurable (fun q : (ℝ × ℝ) × ℝ => (q.2, q.1.1, (1 - q.1.2)⁻¹, q.1.2⁻¹)) := by
    fun_prop
  exact (hΦ.measurable.comp hin).norm.log

lemma measurable_integral_log_det (P g : Matrix (Fin M) (Fin M) ℂ) (n : ℕ) :
    Measurable (fun q : ℝ × ℝ =>
      ∫ x in (-(n : ℝ))..n, Real.log ‖((x : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)
        - pencilMatE P g q.1 q.2).det‖) := by
  have h := (measurable_log_det P g).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Set.Ioc (-(n : ℝ)) n))
  have hle : -(n : ℝ) ≤ n := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have heq : (fun q : ℝ × ℝ => ∫ x in (-(n : ℝ))..n, Real.log ‖((x : ℂ) •
      (1 : Matrix (Fin M) (Fin M) ℂ) - pencilMatE P g q.1 q.2).det‖)
      = fun q => ∫ x, Real.log ‖((x : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)
          - pencilMatE P g q.1 q.2).det‖ ∂(volume.restrict (Set.Ioc (-(n : ℝ)) n)) := by
    funext q
    rw [intervalIntegral.integral_of_le hle]
  rw [heq]
  exact h.measurable

/-- **`F` is (jointly) measurable.**  Proof: on `0 < τ < 1`, `F` is the pointwise limit of the
measurable functions `(∫_{-n}^{n} log |det (x - (P - τ)⁻¹ (g - s))| dx - M (2 n log n - 2 n)) / (2 π²)`
(real-line Jensen asymptotics, `tendsto_integral_log_norm_eval`). -/
theorem measurable_stripF {P : Matrix (Fin M) (Fin M) ℂ} (hP : P * P = P)
    (g : Matrix (Fin M) (Fin M) ℂ) : Measurable (Function.uncurry (stripF P g)) := by
  let f : ℕ → ℝ × ℝ → ℝ := fun n q => if 0 < q.2 ∧ q.2 < 1 then
      ((∫ x in (-(n : ℝ))..n, Real.log ‖((x : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)
        - pencilMatE P g q.1 q.2).det‖) - M * (2 * n * Real.log n - 2 * n)) / (2 * π ^ 2)
    else 0
  apply measurable_of_tendsto_metrizable (f := f)
  · intro n
    apply Measurable.ite
    · exact (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_const)
    · exact ((measurable_integral_log_det P g n).sub measurable_const).div_const _
    · exact measurable_const
  · rw [tendsto_pi_nhds]
    rintro ⟨s, τ⟩
    simp only [f, Function.uncurry_apply_pair, stripF]
    split_ifs with h
    · have h0 : τ ≠ 0 := h.1.ne'
      have h1 : τ ≠ 1 := h.2.ne
      set A := (P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹ * (g - (s : ℂ) • 1) with hA_def
      have hA : pencilMatE P g s τ = A := (pencilMatE_eq hP h0 h1).symm
      have hmon : A.charpoly.Monic := Matrix.charpoly_monic A
      have key := (tendsto_integral_log_norm_eval A.charpoly hmon.ne_zero).comp
        tendsto_natCast_atTop_atTop
      have key2 := key.div_const (2 * π ^ 2)
      have hlim : π * (A.charpoly.roots.map (fun z => |z.im|)).sum / (2 * π ^ 2)
          = imAbsSum (pencilRoots P (g - (s : ℂ) • 1) τ) / (2 * π) := by
        unfold pencilRoots imAbsSum
        rw [← hA_def]
        field_simp
      rw [hlim] at key2
      refine key2.congr (fun n => ?_)
      simp only [Function.comp_apply, hmon.leadingCoeff, norm_one, Real.log_one, mul_zero,
        sub_zero, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, hA, Matrix.eval_charpoly,
        Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    · exact tendsto_const_nhds


/-! ### `F` as a Jensen integral (paper, eq. (3.4)) -/

lemma pinch_sub_smul_one {P : Matrix (Fin M) (Fin M) ℂ} (hP : P * P = P)
    (g : Matrix (Fin M) (Fin M) ℂ) (s : ℂ) :
    pinch P (g - s • 1) = pinch P g - s • 1 := by
  rw [pinch_sub, pinch_smul, pinch_one hP]

/-- **`F` via the Jensen integral** (paper, eq. (3.4)).  For `0 < τ < 1`, with `p`, `q` the monic
characteristic polynomials of `(P - τ)⁻¹ (g - s)` and `(P - τ)⁻¹ (g_d - s)` (whose roots are the
roots of `det (g - s - x (P - τ))` and `det (g_d - s - x (P - τ))`):
`x ↦ log |p(x)/q(x)|` is integrable and `F(s, τ) = (1/2π²) ∫_ℝ log |p(x)/q(x)| dx`. -/
theorem stripF_eq_jensen {P g : Matrix (Fin M) (Fin M) ℂ} (hP : IsProj P) (hg : g.IsHermitian)
    {s τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) :
    Integrable (fun x : ℝ =>
      Real.log ‖(((P - (τ : ℂ) • 1)⁻¹ * (g - (s : ℂ) • 1)).charpoly).eval (x : ℂ)
        / (((P - (τ : ℂ) • 1)⁻¹ * (pinch P g - (s : ℂ) • 1)).charpoly).eval (x : ℂ)‖) ∧
    stripF P g s τ
      = (∫ x : ℝ, Real.log ‖(((P - (τ : ℂ) • 1)⁻¹ * (g - (s : ℂ) • 1)).charpoly).eval (x : ℂ)
          / (((P - (τ : ℂ) • 1)⁻¹ * (pinch P g - (s : ℂ) • 1)).charpoly).eval (x : ℂ)‖)
        / (2 * π ^ 2) := by
  have hτ0 : τ ≠ 0 := h0.ne'
  have hτ1 : τ ≠ 1 := h1.ne
  set H := g - (s : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ) with hH_def
  have hH : H.IsHermitian := hg.sub (isHermitian_one.smul (isSelfAdjoint_ofReal s))
  have hpin : pinch P g - (s : ℂ) • 1 = pinch P H := (pinch_sub_smul_one hP.2 g (s : ℂ)).symm
  rw [hpin]
  set p := ((P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹ * H).charpoly with hp_def
  set q := ((P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹ * pinch P H).charpoly with hq_def
  have hpm : p.Monic := Matrix.charpoly_monic _
  have hqm : q.Monic := Matrix.charpoly_monic _
  have hJ := jensen_identity (p := p) (q := q) hpm.ne_zero (by rw [hpm.leadingCoeff, hqm.leadingCoeff])
    (by rw [hp_def, hq_def, Matrix.charpoly_natDegree_eq_dim, Matrix.charpoly_natDegree_eq_dim])
    (pencilRoots_pinch_im hP hτ0 hτ1 hH)
    (sum_pencilRoots_pinch hP.2 hτ0 hτ1 H).symm
  refine ⟨hJ.1, ?_⟩
  rw [hJ.2, stripF, if_pos ⟨h0, h1⟩]
  unfold imAbsSum pencilRoots
  rw [← hH_def, ← hp_def]
  field_simp


/-! ### Faithfulness: pencil roots are the roots of `y ↦ det (H - y (P - τ))` -/

/-- `det (H - y (P - τ)) = det (-(P - τ)) · χ_{(P - τ)⁻¹ H}(y)` for `τ ∉ {0, 1}`. -/
lemma det_pencil {P H : Matrix (Fin M) (Fin M) ℂ} (hP : P * P = P) {τ : ℝ} (h0 : τ ≠ 0)
    (h1 : τ ≠ 1) (y : ℂ) :
    (H - y • (P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))).det
      = (-(P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))).det
        * (((P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹ * H).charpoly).eval y := by
  set Q := P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ) with hQ_def
  have hQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_det_P_sub hP h0 h1)
  have e : H - y • Q = -Q * (Matrix.scalar (Fin M) y - Q⁻¹ * H) := by
    rw [Matrix.neg_mul, Matrix.mul_sub, ← Matrix.mul_assoc, hQ, Matrix.one_mul,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
    abel
  rw [e, Matrix.det_mul, Matrix.eval_charpoly]

/-- **The pencil roots are exactly the roots (with multiplicity) of the polynomial
`y ↦ det (H - y (P - τ))`**, for `τ ∉ {0, 1}`. -/
theorem pencilRoots_eq_roots_det {P H : Matrix (Fin M) (Fin M) ℂ} (hP : P * P = P) {τ : ℝ}
    (h0 : τ ≠ 0) (h1 : τ ≠ 1) :
    pencilRoots P H τ
      = ((H.map Polynomial.C) - (Polynomial.X : ℂ[X])
          • ((P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)).map Polynomial.C)).det.roots := by
  set Q := P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ) with hQ_def
  have hQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_det_P_sub hP h0 h1)
  have key : (H.map Polynomial.C) - (Polynomial.X : ℂ[X]) • (Q.map Polynomial.C)
      = ((-Q).map Polynomial.C) * Matrix.charmatrix (Q⁻¹ * H) := by
    have hm : (Q.map Polynomial.C) * ((Q⁻¹ * H).map Polynomial.C) = H.map Polynomial.C := by
      rw [← Matrix.map_mul, ← Matrix.mul_assoc, hQ, Matrix.one_mul]
    have hneg : (-Q).map Polynomial.C = -(Q.map Polynomial.C) := by
      ext i j; simp
    rw [Matrix.charmatrix, hneg, Matrix.neg_mul, Matrix.mul_sub, RingHom.mapMatrix_apply, hm,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
    abel
  have hdet : (-Q).det ≠ 0 := by
    rw [Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (isUnit_det_P_sub hP h0 h1).ne_zero
  have hC : ((-Q).map Polynomial.C).det = Polynomial.C (-Q).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  rw [key, Matrix.det_mul, hC, Polynomial.roots_C_mul _ hdet]
  rfl

end OQP27.StripL3b
