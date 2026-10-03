/-
OQP27/CellMeanValue.lean  (module L5, layers 3-4: mean value on circles and the boundary limit)

Setting (Q_rig/RIGIDITY_ALLD.md s.3.1-3.5, Q_quantum/LOG.md s.4 (i)-(iii)).  A partition
`0 = t₀ < t₁ < ... < tₙ = 2π` of the circle into arcs `J_k = (t_k, t_{k+1})`, projections `B_k` on `ℂ^M`
with the operator constraint `∑_k (|J_k|/2π) B_k = β 1` (`0 < β < 1`), and the matrix Herglotz function
    `herg z = ∑_k arcH(t_k, t_{k+1}, z) B_k`
(holomorphic on the unit disc, `herg 0 = β 1`, boundary values `B_k + i g(θ)` on `J_k`).

Proved here (complete proofs):
* `roots_mem_strip`: for `|z| < 1` every eigenvalue of `herg z` lies in the open strip
  `{0 < Re w < 1}` (numerical-range argument, RIGIDITY_ALLD.md s.3.3); `roots_mem_cstrip`: at every
  point of the closed disc where all `Re arcH ≥ 0` (in particular on the boundary) they lie in the closed
  strip;
* `mean_value_boundary`: for every `h` harmonic on the open strip, continuous on the closed strip and
  of linear growth, the boundary eigenvalue sum `u*(θ) = ∑_{ν ∈ spec herg(e^{iθ})} h ν` is integrable
  on `[0, 2π]` and
      `∫₀^{2π} u*(θ) dθ = 2π M h(β)`
  (mean value property of the harmonic function `u(z) = ∑_{ν ∈ spec herg z} h ν` on circles of radius
  `r < 1`, then `r → 1` by dominated convergence; RIGIDITY_ALLD.md (3.3)).
No hypotheses remain.
-/
import OQP27.CellContour
import OQP27.CellHerglotz
import Mathlib.LinearAlgebra.Matrix.Hermitian

set_option autoImplicit false

namespace OQP27.Cell

open Polynomial Matrix Filter Topology Complex MeasureTheory Metric Set Real
open scoped Interval

variable {M : ℕ}

/-! ### Projections and quadratic forms -/

/-- A projection: a Hermitian idempotent matrix. -/
def IsProj (B : Matrix (Fin M) (Fin M) ℂ) : Prop := B.IsHermitian ∧ B * B = B

lemma IsProj.one_sub {B : Matrix (Fin M) (Fin M) ℂ} (hB : IsProj B) : IsProj (1 - B) := by
  refine ⟨(Matrix.isHermitian_one).sub hB.1, ?_⟩
  rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, hB.2]
  abel

/-- The squared Euclidean norm of a vector. -/
noncomputable def vsq (v : Fin M → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

lemma star_dotProduct_self (v : Fin M → ℂ) : star v ⬝ᵥ v = (vsq v : ℂ) := by
  simp only [dotProduct, vsq, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.star_def, Complex.conj_mul']

lemma vsq_nonneg (v : Fin M → ℂ) : 0 ≤ vsq v := by
  unfold vsq
  positivity

lemma vsq_eq_zero {v : Fin M → ℂ} : vsq v = 0 ↔ v = 0 := by
  unfold vsq
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)]
  constructor
  · intro h
    funext i
    have := h i (Finset.mem_univ i)
    simpa using this
  · rintro rfl
    simp

lemma star_dot_proj {B : Matrix (Fin M) (Fin M) ℂ} (hB : IsProj B) (v : Fin M → ℂ) :
    star v ⬝ᵥ (B *ᵥ v) = (vsq (B *ᵥ v) : ℂ) := by
  have h1 : star (B *ᵥ v) = star v ᵥ* B := by
    rw [Matrix.star_mulVec, hB.1]
  have h2 : B *ᵥ (B *ᵥ v) = B *ᵥ v := by
    rw [Matrix.mulVec_mulVec, hB.2]
  rw [← star_dotProduct_self, h1, ← Matrix.dotProduct_mulVec, h2]

lemma vsq_split {B : Matrix (Fin M) (Fin M) ℂ} (hB : IsProj B) (v : Fin M → ℂ) :
    vsq v = vsq (B *ᵥ v) + vsq ((1 - B) *ᵥ v) := by
  have h : (vsq v : ℂ) = (vsq (B *ᵥ v) : ℂ) + (vsq ((1 - B) *ᵥ v) : ℂ) := by
    rw [← star_dot_proj hB, ← star_dot_proj hB.one_sub, ← dotProduct_add, ← Matrix.add_mulVec,
      add_sub_cancel, Matrix.one_mulVec, star_dotProduct_self]
  exact_mod_cast h

lemma vsq_proj_le {B : Matrix (Fin M) (Fin M) ℂ} (hB : IsProj B) (v : Fin M → ℂ) :
    vsq (B *ᵥ v) ≤ vsq v := by
  rw [vsq_split hB v]
  linarith [vsq_nonneg ((1 - B) *ᵥ v)]

/-! ### Eigenvalues of positive combinations of projections lie in the strip -/

/-- The open strip `{0 < Re w < 1}`. -/
def strip : Set ℂ := {w | 0 < w.re ∧ w.re < 1}

/-- The closed strip `{0 ≤ Re w ≤ 1}`. -/
def cstrip : Set ℂ := {w | 0 ≤ w.re ∧ w.re ≤ 1}

lemma isOpen_strip : IsOpen strip :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

lemma isClosed_cstrip : IsClosed cstrip :=
  (isClosed_le continuous_const Complex.continuous_re).inter
    (isClosed_le Complex.continuous_re continuous_const)

lemma strip_subset_cstrip : strip ⊆ cstrip := fun _ hw => ⟨hw.1.le, hw.2.le⟩

lemma re_root_eq {n : ℕ} (w : ℕ → ℂ) (B : ℕ → Matrix (Fin M) (Fin M) ℂ) (hB : ∀ k, IsProj (B k))
    {ν : ℂ} (hν : ν ∈ (∑ k ∈ Finset.range n, w k • B k).charpoly.roots) :
    ∃ v : Fin M → ℂ, v ≠ 0 ∧
      ν.re * vsq v = ∑ k ∈ Finset.range n, (w k).re * vsq (B k *ᵥ v) := by
  obtain ⟨v, hv, hXv⟩ := mem_roots_eigvec hν
  refine ⟨v, hv, ?_⟩
  have h1 : star v ⬝ᵥ ((∑ k ∈ Finset.range n, w k • B k) *ᵥ v) = ν * (vsq v : ℂ) := by
    rw [hXv, dotProduct_smul, star_dotProduct_self, smul_eq_mul]
  rw [Matrix.sum_mulVec, dotProduct_sum] at h1
  have h2 : ∀ k ∈ Finset.range n, star v ⬝ᵥ ((w k • B k) *ᵥ v) = w k * (vsq (B k *ᵥ v) : ℂ) := by
    intro k _
    rw [Matrix.smul_mulVec, dotProduct_smul, star_dot_proj (hB k), smul_eq_mul]
  rw [Finset.sum_congr rfl h2] at h1
  have h3 := congrArg Complex.re h1
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero] at h3
  exact h3.symm

/-- Eigenvalues of `∑ w_k B_k` with `Re w_k ≥ 0`, `∑ w_k = 1` lie in the closed strip. -/
lemma roots_mem_cstrip {n : ℕ} (w : ℕ → ℂ) (B : ℕ → Matrix (Fin M) (Fin M) ℂ)
    (hB : ∀ k, IsProj (B k)) (hw : ∀ k ∈ Finset.range n, 0 ≤ (w k).re)
    (hsum : ∑ k ∈ Finset.range n, w k = 1) :
    ∀ ν ∈ (∑ k ∈ Finset.range n, w k • B k).charpoly.roots, ν ∈ cstrip := by
  intro ν hν
  obtain ⟨v, hv, heq⟩ := re_root_eq w B hB hν
  have hvpos : 0 < vsq v := lt_of_le_of_ne (vsq_nonneg v) (fun h => hv (vsq_eq_zero.1 h.symm))
  have hsumre : ∑ k ∈ Finset.range n, (w k).re = 1 := by
    rw [← Complex.re_sum, hsum, Complex.one_re]
  constructor
  · have : 0 ≤ ν.re * vsq v := by
      rw [heq]
      exact Finset.sum_nonneg fun k hk => mul_nonneg (hw k hk) (vsq_nonneg _)
    exact nonneg_of_mul_nonneg_left this hvpos
  · have h1 : (1 - ν.re) * vsq v =
        ∑ k ∈ Finset.range n, (w k).re * (vsq v - vsq (B k *ᵥ v)) := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsumre, ← heq]
      ring
    have : 0 ≤ (1 - ν.re) * vsq v := by
      rw [h1]
      exact Finset.sum_nonneg fun k hk =>
        mul_nonneg (hw k hk) (sub_nonneg.2 (vsq_proj_le (hB k) v))
    have := nonneg_of_mul_nonneg_left this hvpos
    linarith

/-- Eigenvalues of `∑ w_k B_k` with `Re w_k > 0`, `∑ w_k = 1` lie in the open strip, provided the
`B_k` satisfy an operator constraint `∑ c_k B_k = β 1` with `∑ c_k = 1`, `0 < β < 1`. -/
lemma roots_mem_strip {n : ℕ} (w : ℕ → ℂ) (B : ℕ → Matrix (Fin M) (Fin M) ℂ)
    (hB : ∀ k, IsProj (B k)) (hw : ∀ k ∈ Finset.range n, 0 < (w k).re)
    (hsum : ∑ k ∈ Finset.range n, w k = 1) (c : ℕ → ℝ) (hc : ∑ k ∈ Finset.range n, c k = 1)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hop : ∑ k ∈ Finset.range n, (c k : ℂ) • B k = (β : ℂ) • 1) :
    ∀ ν ∈ (∑ k ∈ Finset.range n, w k • B k).charpoly.roots, ν ∈ strip := by
  intro ν hν
  obtain ⟨v, hv, heq⟩ := re_root_eq w B hB hν
  have hvpos : 0 < vsq v := lt_of_le_of_ne (vsq_nonneg v) (fun h => hv (vsq_eq_zero.1 h.symm))
  have hsumre : ∑ k ∈ Finset.range n, (w k).re = 1 := by
    rw [← Complex.re_sum, hsum, Complex.one_re]
  have hopv : ∑ k ∈ Finset.range n, (c k : ℂ) • (B k *ᵥ v) = (β : ℂ) • v := by
    have := congrArg (fun X => X *ᵥ v) hop
    simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at this
    exact this
  constructor
  · by_contra hcon
    push Not at hcon
    have hle : ∑ k ∈ Finset.range n, (w k).re * vsq (B k *ᵥ v) ≤ 0 := by
      rw [← heq]
      exact mul_nonpos_of_nonpos_of_nonneg hcon (vsq_nonneg v)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun k hk =>
      mul_nonneg (hw k hk).le (vsq_nonneg (B k *ᵥ v)))).1
      (le_antisymm hle (Finset.sum_nonneg fun k hk => mul_nonneg (hw k hk).le (vsq_nonneg _)))
    have hBv : ∀ k ∈ Finset.range n, B k *ᵥ v = 0 := by
      intro k hk
      have := hz k hk
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (hw k hk).ne'
      · exact vsq_eq_zero.1 h
    have : (β : ℂ) • v = 0 := by
      rw [← hopv]
      exact Finset.sum_eq_zero fun k hk => by rw [hBv k hk, smul_zero]
    rcases smul_eq_zero.1 this with h | h
    · exact absurd (Complex.ofReal_eq_zero.1 h) hβ0.ne'
    · exact hv h
  · by_contra hcon
    push Not at hcon
    have h1 : (1 - ν.re) * vsq v =
        ∑ k ∈ Finset.range n, (w k).re * (vsq v - vsq (B k *ᵥ v)) := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsumre, ← heq]
      ring
    have hnn : ∀ k ∈ Finset.range n, 0 ≤ (w k).re * (vsq v - vsq (B k *ᵥ v)) := fun k hk =>
      mul_nonneg (hw k hk).le (sub_nonneg.2 (vsq_proj_le (hB k) v))
    have hle : ∑ k ∈ Finset.range n, (w k).re * (vsq v - vsq (B k *ᵥ v)) ≤ 0 := by
      rw [← h1]
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (vsq_nonneg v)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (le_antisymm hle (Finset.sum_nonneg hnn))
    have hBv : ∀ k ∈ Finset.range n, B k *ᵥ v = v := by
      intro k hk
      have := hz k hk
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h (hw k hk).ne'
      · have h2 : vsq ((1 - B k) *ᵥ v) = 0 := by
          have := vsq_split (hB k) v
          linarith
        have h3 := vsq_eq_zero.1 h2
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h3
        exact h3.symm
    have : (β : ℂ) • v = v := by
      rw [← hopv, Finset.sum_congr rfl fun k hk => by rw [hBv k hk], ← Finset.sum_smul]
      rw [← Complex.ofReal_sum, hc, Complex.ofReal_one, one_smul]
    have h4 : ((β : ℂ) - 1) • v = 0 := by
      rw [sub_smul, this, one_smul, sub_self]
    rcases smul_eq_zero.1 h4 with h | h
    · have : (β : ℂ) = 1 := sub_eq_zero.1 h
      have : β = 1 := by exact_mod_cast this
      linarith
    · exact hv h

/-! ### Small facts about eigenvalue sums -/

lemma sum_roots_scalar (β : ℂ) (h : ℂ → ℝ) :
    (((β • (1 : Matrix (Fin M) (Fin M) ℂ)).charpoly.roots).map h).sum = M * h β := by
  rw [Matrix.smul_one_eq_diagonal, Matrix.charpoly_diagonal]
  have : (∏ _i : Fin M, (Polynomial.X - Polynomial.C β)) =
      ((Multiset.replicate M β).map fun a => Polynomial.X - Polynomial.C a).prod := by
    simp [Finset.prod_const, Multiset.map_replicate, Multiset.prod_replicate]
  rw [this, roots_multiset_prod_X_sub_C, Multiset.map_replicate, Multiset.sum_replicate,
    nsmul_eq_mul]

lemma abs_sum_roots_le (X : Matrix (Fin M) (Fin M) ℂ) (h : ℂ → ℝ) {K : ℝ}
    (hK : ∀ ν ∈ X.charpoly.roots, |h ν| ≤ K) :
    |(X.charpoly.roots.map h).sum| ≤ M * K := by
  calc |(X.charpoly.roots.map h).sum| ≤ ((X.charpoly.roots.map h).map abs).sum :=
        Multiset.abs_sum_le_sum_abs
    _ ≤ Multiset.card ((X.charpoly.roots.map h).map abs) • K := by
        apply Multiset.sum_le_card_nsmul
        intro x hx
        rw [Multiset.map_map, Multiset.mem_map] at hx
        obtain ⟨ν, hν, rfl⟩ := hx
        exact hK ν hν
    _ = M * K := by
        rw [Multiset.card_map, Multiset.card_map, card_roots_charpoly, nsmul_eq_mul]

lemma mnorm_add (X Y : Matrix (Fin M) (Fin M) ℂ) : mnorm (X + Y) ≤ mnorm X + mnorm Y := by
  unfold mnorm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  exact norm_add_le _ _

lemma mnorm_smul (c : ℂ) (X : Matrix (Fin M) (Fin M) ℂ) : mnorm (c • X) = ‖c‖ * mnorm X := by
  unfold mnorm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul]

lemma mnorm_zero : mnorm (0 : Matrix (Fin M) (Fin M) ℂ) = 0 := by
  simp [mnorm]

lemma mnorm_sum_le (s : Finset ℕ) (X : ℕ → Matrix (Fin M) (Fin M) ℂ) :
    mnorm (∑ k ∈ s, X k) ≤ ∑ k ∈ s, mnorm (X k) := by
  induction s using Finset.induction_on with
  | empty => simp [mnorm_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (mnorm_add _ _).trans (by linarith)

lemma intervalIntegrable_fun_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} {a b : ℝ}
    (h : ∀ i ∈ s, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun x => ∑ i ∈ s, f i x) volume a b := by
  have heq : (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, f i := by
    funext x
    simp [Finset.sum_apply]
  rw [heq]
  exact IntervalIntegrable.sum s h

/-! ### Arc partitions and the matrix Herglotz function -/

/-- A partition `0 = t₀ < t₁ < ⋯ < tₙ = 2π` of the circle into `n` arcs `(t_k, t_{k+1})`. -/
structure ArcPartition (n : ℕ) where
  /-- the endpoints (only `t 0, …, t n` are used) -/
  t : ℕ → ℝ
  t_zero : t 0 = 0
  t_last : t n = 2 * π
  t_lt : ∀ k < n, t k < t (k + 1)

namespace ArcPartition

variable {n : ℕ} (P : ArcPartition n)

lemma t_le_add (j m : ℕ) (h : j + m ≤ n) : P.t j ≤ P.t (j + m) := by
  induction m with
  | zero => simp
  | succ m ih => exact (ih (by omega)).trans (P.t_lt (j + m) (by omega)).le

lemma t_le_t {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ n) : P.t j ≤ P.t k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjk
  exact P.t_le_add j m hk

lemma t_lt_t {j k : ℕ} (hjk : j < k) (hk : k ≤ n) : P.t j < P.t k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hjk
  exact (P.t_le_add j m (by omega)).trans_lt (P.t_lt (j + m) (by omega))

lemma t_nonneg {k : ℕ} (hk : k ≤ n) : 0 ≤ P.t k := by
  have := P.t_le_t (Nat.zero_le k) hk
  rwa [P.t_zero] at this

lemma t_le_two_pi {k : ℕ} (hk : k ≤ n) : P.t k ≤ 2 * π := by
  have := P.t_le_t hk le_rfl
  rwa [P.t_last] at this

/-- The relative lengths `|J_k|/2π` sum to `1`. -/
lemma sum_len : ∑ k ∈ Finset.range n, (P.t (k + 1) - P.t k) / (2 * π) = 1 := by
  rw [← Finset.sum_div, Finset.sum_range_sub (fun k => P.t k), P.t_last, P.t_zero, sub_zero,
    div_self (by positivity)]

/-- The finite set of endpoints. -/
noncomputable def ends : Finset ℝ := (Finset.range (n + 1)).image P.t

lemma mem_ends {k : ℕ} (hk : k ≤ n) : P.t k ∈ P.ends :=
  Finset.mem_image_of_mem _ (Finset.mem_range.2 (by omega))

/-- A point of `(0, 2π]` that is not an endpoint lies in `(0, 2π)` and avoids all `t_k`. -/
lemma not_end {θ : ℝ} (hθ : θ ∈ Ioc 0 (2 * π)) (hT : θ ∉ (P.ends : Set ℝ)) :
    θ ∈ Ioo 0 (2 * π) ∧ ∀ k ≤ n, θ ≠ P.t k := by
  have hne : ∀ k ≤ n, θ ≠ P.t k := by
    intro k hk h
    exact hT (h ▸ P.mem_ends hk)
  refine ⟨⟨hθ.1, lt_of_le_of_ne hθ.2 ?_⟩, hne⟩
  intro h
  exact hne n le_rfl (h.trans P.t_last.symm)

lemma sin_half_ne_zero {θ : ℝ} (hθ : θ ∈ Ioo 0 (2 * π)) {k : ℕ} (hk : k ≤ n)
    (hne : θ ≠ P.t k) : Real.sin ((θ - P.t k) / 2) ≠ 0 := by
  have h0 := P.t_nonneg hk
  have h1 := P.t_le_two_pi hk
  intro h
  rw [Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [hθ.1, hθ.2]) (by linarith [hθ.1, hθ.2])] at h
  apply hne
  linarith

end ArcPartition

/-- The matrix Herglotz function of the step field `B` on the arcs of `P`. -/
noncomputable def herg {n : ℕ} (P : ArcPartition n) (B : ℕ → Matrix (Fin M) (Fin M) ℂ) (z : ℂ) :
    Matrix (Fin M) (Fin M) ℂ :=
  ∑ k ∈ Finset.range n, arcH (P.t k) (P.t (k + 1)) z • B k

lemma herg_apply {n : ℕ} (P : ArcPartition n) (B : ℕ → Matrix (Fin M) (Fin M) ℂ) (z : ℂ)
    (i j : Fin M) :
    herg P B z i j = ∑ k ∈ Finset.range n, arcH (P.t k) (P.t (k + 1)) z * B k i j := by
  simp [herg, Matrix.sum_apply, Matrix.smul_apply]

lemma differentiableOn_herg {n : ℕ} (P : ArcPartition n) (B : ℕ → Matrix (Fin M) (Fin M) ℂ)
    (i j : Fin M) : DifferentiableOn ℂ (fun z => herg P B z i j) (ball 0 1) := by
  simp only [herg_apply]
  exact DifferentiableOn.fun_sum fun k _ => (differentiableOn_arcH _ _).mul_const _

lemma herg_zero {n : ℕ} (P : ArcPartition n) (B : ℕ → Matrix (Fin M) (Fin M) ℂ) {β : ℝ}
    (hop : ∑ k ∈ Finset.range n,
      ((((P.t (k + 1) - P.t k) / (2 * π)) : ℝ) : ℂ) • B k = (β : ℂ) • 1) :
    herg P B 0 = (β : ℂ) • 1 := by
  rw [← hop]
  unfold herg
  simp only [arcH_zero]

lemma continuousAt_herg_boundary {n : ℕ} (P : ArcPartition n)
    (B : ℕ → Matrix (Fin M) (Fin M) ℂ) {θ : ℝ} (hθ : θ ∈ Ioo 0 (2 * π))
    (hne : ∀ k ≤ n, θ ≠ P.t k) : ContinuousAt (herg P B) (Complex.exp ((θ : ℂ) * I)) := by
  unfold herg
  apply tendsto_finsetSum
  intro k hk
  have hk' := Finset.mem_range.1 hk
  exact (continuousAt_arcH_boundary (P.t_nonneg (by omega)) (P.t_le_two_pi (by omega))
    (P.t_nonneg (by omega)) (P.t_le_two_pi (by omega)) hθ.1 hθ.2 (hne k (by omega))
    (hne (k + 1) (by omega))).tendsto.smul tendsto_const_nhds

lemma herg_roots_mem_strip {n : ℕ} (P : ArcPartition n) (B : ℕ → Matrix (Fin M) (Fin M) ℂ)
    (hB : ∀ k, IsProj (B k)) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hop : ∑ k ∈ Finset.range n,
      ((((P.t (k + 1) - P.t k) / (2 * π)) : ℝ) : ℂ) • B k = (β : ℂ) • 1)
    {z : ℂ} (hz : ‖z‖ < 1) : ∀ ν ∈ (herg P B z).charpoly.roots, ν ∈ strip :=
  roots_mem_strip (fun k => arcH (P.t k) (P.t (k + 1)) z) B hB
    (fun k hk => re_arcH_pos (P.t_lt k (Finset.mem_range.1 hk)) hz)
    (sum_arcH P.t P.t_zero P.t_last z) (fun k => (P.t (k + 1) - P.t k) / (2 * π)) P.sum_len
    hβ0 hβ1 hop

/-! ### The mean value identity and the boundary limit -/

/-- **Mean value on circles and boundary limit** (RIGIDITY_ALLD.md (3.3)): for `h` harmonic on the
open strip, continuous on the closed strip, with `|h w| ≤ C (1 + |w|)`, the boundary eigenvalue sum
`u*(θ) = ∑_{ν ∈ spec herg(e^{iθ})} h ν` is integrable on `[0, 2π]` and `∫₀^{2π} u* = 2π M h(β)`. -/
theorem mean_value_boundary {n : ℕ} (P : ArcPartition n) (B : ℕ → Matrix (Fin M) (Fin M) ℂ)
    (hB : ∀ k, IsProj (B k)) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hop : ∑ k ∈ Finset.range n,
      ((((P.t (k + 1) - P.t k) / (2 * π)) : ℝ) : ℂ) • B k = (β : ℂ) • 1)
    {h : ℂ → ℝ} (hharm : InnerProductSpace.HarmonicOnNhd h strip)
    (hcont : ContinuousOn h cstrip) {C : ℝ} (hC : 0 ≤ C)
    (hgrowth : ∀ w ∈ cstrip, |h w| ≤ C * (1 + ‖w‖)) :
    IntervalIntegrable (fun θ : ℝ => ((herg P B (Complex.exp ((θ : ℂ) * I))).charpoly.roots.map h).sum)
      volume 0 (2 * π) ∧
    ∫ θ in (0 : ℝ)..2 * π, ((herg P B (Complex.exp ((θ : ℂ) * I))).charpoly.roots.map h).sum =
      2 * π * (M * h β) := by
  set u : ℂ → ℝ := fun z => ((herg P B z).charpoly.roots.map h).sum with hu
  have hπ : 0 < 2 * π := by positivity
  -- harmonicity of `u` on the unit disc
  have hspec : ∀ z ∈ ball (0 : ℂ) 1, ∀ ν ∈ (herg P B z).charpoly.roots, ν ∈ strip := by
    intro z hz
    rw [mem_ball, dist_zero_right] at hz
    exact herg_roots_mem_strip P B hB hβ0 hβ1 hop hz
  have hharmu : InnerProductSpace.HarmonicOnNhd u (ball 0 1) :=
    harmonicOnNhd_sum_roots isOpen_ball (differentiableOn_herg P B) isOpen_strip hharm hspec
  have hu0 : u 0 = M * h β := by
    simp only [hu]
    rw [herg_zero P B hop]
    exact sum_roots_scalar (β : ℂ) h
  -- the mean value identity on circles of radius `r < 1`
  have hmv : ∀ r : ℝ, 0 < r → r < 1 →
      ∫ θ in (0 : ℝ)..2 * π, u (circleMap 0 r θ) = 2 * π * (M * h β) := by
    intro r hr0 hr1
    have hsub : closedBall (0 : ℂ) |r| ⊆ ball 0 1 := by
      rw [abs_of_pos hr0]
      exact closedBall_subset_ball hr1
    have h1 := InnerProductSpace.HarmonicOnNhd.circleAverage_eq (hharmu.mono hsub)
    rw [Real.circleAverage_def, hu0, smul_eq_mul] at h1
    rw [← h1, ← mul_assoc, mul_inv_cancel₀ hπ.ne', one_mul]
  -- the radii and the exceptional set
  set rs : ℕ → ℝ := fun m => 1 - 1 / ((m : ℝ) + 2) with hrs
  have hrs_half : ∀ m, 1 / 2 ≤ rs m := by
    intro m
    simp only [hrs]
    have : 1 / ((m : ℝ) + 2) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
    linarith
  have hrs_lt : ∀ m, rs m < 1 := by
    intro m
    simp only [hrs]
    have : 0 < 1 / ((m : ℝ) + 2) := by positivity
    linarith
  have hrs_lim : Tendsto rs atTop (𝓝 1) := by
    have : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 2)) atTop (𝓝 0) := by
      have h2 : Tendsto (fun m : ℕ => (m : ℝ) + 2) atTop atTop :=
        tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      simpa [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp h2
    rw [hrs]
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
  have hTc : (P.ends : Set ℝ).Countable := (Finset.finite_toSet _).countable
  -- the dominating function
  set bound : ℝ → ℝ := fun θ =>
    M * (C * (1 + ∑ k ∈ Finset.range n, domH (P.t k) (P.t (k + 1)) θ * mnorm (B k))) with hbound
  have hbound_int : IntervalIntegrable bound volume 0 (2 * π) := by
    simp only [hbound]
    apply IntervalIntegrable.const_mul
    apply IntervalIntegrable.const_mul
    apply intervalIntegrable_const.add
    apply intervalIntegrable_fun_sum
    intro k _
    exact (intervalIntegrable_domH _ _).mul_const _
  have hptbound : ∀ θ ∈ Ioo 0 (2 * π), (∀ k ≤ n, θ ≠ P.t k) →
      ∀ r : ℝ, 1 / 2 ≤ r → r < 1 → |u ((r : ℂ) * Complex.exp ((θ : ℂ) * I))| ≤ bound θ := by
    intro θ hθ hne r hr1 hr2
    set z := (r : ℂ) * Complex.exp ((θ : ℂ) * I) with hz
    have hzn : ‖z‖ < 1 := by
      rw [hz, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith)]
      exact hr2
    have hmn : mnorm (herg P B z) ≤
        ∑ k ∈ Finset.range n, domH (P.t k) (P.t (k + 1)) θ * mnorm (B k) := by
      unfold herg
      refine (mnorm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
      have hk' := Finset.mem_range.1 hk
      rw [mnorm_smul]
      apply mul_le_mul_of_nonneg_right _ (mnorm_nonneg _)
      exact norm_arcH_le (P.t_lt k hk').le
        (by linarith [P.t_nonneg (k := k) (by omega), P.t_le_two_pi (k := k + 1) (by omega)])
        hr1 hr2.le (P.sin_half_ne_zero hθ (by omega) (hne k (by omega)))
        (P.sin_half_ne_zero hθ (by omega) (hne (k + 1) (by omega)))
    have hK : ∀ ν ∈ (herg P B z).charpoly.roots,
        |h ν| ≤ C * (1 + ∑ k ∈ Finset.range n, domH (P.t k) (P.t (k + 1)) θ * mnorm (B k)) := by
      intro ν hν
      have hνs := strip_subset_cstrip (hspec z (by rwa [mem_ball, dist_zero_right]) ν hν)
      refine (hgrowth ν hνs).trans ?_
      apply mul_le_mul_of_nonneg_left _ hC
      linarith [norm_le_mnorm hν]
    exact abs_sum_roots_le _ h hK
  have hlim : ∀ θ ∈ Ioo 0 (2 * π), (∀ k ≤ n, θ ≠ P.t k) →
      Tendsto (fun m => u ((rs m : ℂ) * Complex.exp ((θ : ℂ) * I))) atTop
        (𝓝 (u (Complex.exp ((θ : ℂ) * I)))) := by
    intro θ hθ hne
    have hz : Tendsto (fun m => (rs m : ℂ) * Complex.exp ((θ : ℂ) * I)) atTop
        (𝓝 (Complex.exp ((θ : ℂ) * I))) := by
      have := ((Complex.continuous_ofReal.tendsto 1).comp hrs_lim).mul_const
        (Complex.exp ((θ : ℂ) * I))
      simpa using this
    have hX := (continuousAt_herg_boundary P B hθ hne).tendsto.comp hz
    apply tendsto_sum_roots hX isClosed_cstrip hcont
    intro m ν hν
    apply strip_subset_cstrip
    apply hspec _ _ ν hν
    rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hrs_half m])]
    exact hrs_lt m
  -- the a.e. statements
  have hae : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∉ (P.ends : Set ℝ) := hTc.ae_notMem volume
  have hFmeas : ∀ m, AEStronglyMeasurable (fun θ => u (circleMap 0 (rs m) θ))
      (volume.restrict (Ι (0 : ℝ) (2 * π))) := by
    intro m
    apply Continuous.aestronglyMeasurable
    apply hharmu.continuousOn.comp_continuous (continuous_circleMap 0 (rs m))
    intro θ
    rw [mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_pos (by linarith [hrs_half m])]
    exact hrs_lt m
  have hFbound : ∀ m, ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Ι (0 : ℝ) (2 * π) →
      ‖u (circleMap 0 (rs m) θ)‖ ≤ bound θ := by
    intro m
    filter_upwards [hae] with θ hθT hθI
    rw [Set.uIoc_of_le hπ.le] at hθI
    obtain ⟨hθ, hne⟩ := P.not_end hθI hθT
    rw [Real.norm_eq_abs, circleMap, zero_add]
    exact hptbound θ hθ hne (rs m) (hrs_half m) (hrs_lt m)
  have hFlim : ∀ᵐ θ ∂(volume : Measure ℝ), θ ∈ Ι (0 : ℝ) (2 * π) →
      Tendsto (fun m => u (circleMap 0 (rs m) θ)) atTop (𝓝 (u (Complex.exp ((θ : ℂ) * I)))) := by
    filter_upwards [hae] with θ hθT hθI
    rw [Set.uIoc_of_le hπ.le] at hθI
    obtain ⟨hθ, hne⟩ := P.not_end hθI hθT
    simp only [circleMap, zero_add]
    exact hlim θ hθ hne
  have hDCT := intervalIntegral.tendsto_integral_filter_of_dominated_convergence bound
    (Eventually.of_forall hFmeas) (Eventually.of_forall hFbound) hbound_int hFlim
  have hconst : (fun m => ∫ θ in (0 : ℝ)..2 * π, u (circleMap 0 (rs m) θ)) =
      fun _ => 2 * π * (M * h β) := by
    funext m
    exact hmv (rs m) (by linarith [hrs_half m]) (hrs_lt m)
  rw [hconst] at hDCT
  refine ⟨?_, (tendsto_nhds_unique hDCT tendsto_const_nhds)⟩
  -- integrability of the boundary function
  have hres : ∀ᵐ (θ : ℝ) ∂(volume.restrict (Ι (0 : ℝ) (2 * π))),
      Tendsto (fun m => u (circleMap 0 (rs m) θ)) atTop (𝓝 (u (Complex.exp ((θ : ℂ) * I)))) :=
    (ae_restrict_iff' measurableSet_uIoc).2 hFlim
  have hmeas : AEStronglyMeasurable (fun θ : ℝ => u (Complex.exp ((θ : ℂ) * I)))
      (volume.restrict (Ι (0 : ℝ) (2 * π))) :=
    aestronglyMeasurable_of_tendsto_ae atTop hFmeas hres
  have hle : ∀ᵐ (θ : ℝ) ∂(volume.restrict (Ι (0 : ℝ) (2 * π))),
      ‖u (Complex.exp ((θ : ℂ) * I))‖ ≤ bound θ := by
    have hb : ∀ᵐ (θ : ℝ) ∂(volume.restrict (Ι (0 : ℝ) (2 * π))),
        ∀ m, ‖u (circleMap 0 (rs m) θ)‖ ≤ bound θ := by
      rw [ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [ae_all_iff.2 hFbound] with θ hθ hθI m
      exact hθ m hθI
    filter_upwards [hres, hb] with θ h1 h2
    exact le_of_tendsto (h1.norm) (Eventually.of_forall h2)
  have hbint : IntegrableOn bound (Ι (0 : ℝ) (2 * π)) volume :=
    (intervalIntegrable_iff.1 hbound_int)
  exact intervalIntegrable_iff.2 (Integrable.mono' hbint hmeas hle)

end OQP27.Cell
