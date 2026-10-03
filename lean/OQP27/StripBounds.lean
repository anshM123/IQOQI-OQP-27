import OQP27.StripSlice
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef

/-!
# Bounds on the pencil roots and on `F` (Lemma 1(b),(c), module L3b)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

Proved here (no hypotheses, no `sorry`):
* `exists_pencil_eigvec`: every pencil root `x` has an eigenvector, `H v = x (P - τ) v`, `v ≠ 0`;
* `nonreal_root_orth`: for a non-real root, `⟨v, (P - τ) v⟩ = 0 = ⟨v, H v⟩`;
* **Lemma 1(b)** `normSq_nonreal_root_le`: a non-real root satisfies `|x|² τ (1 - τ) ≤ ‖H‖_F²`;
  hence `stripF_le`: `F(s, τ) ≤ M ‖g - s‖_F / (2π √(τ (1 - τ)))`;
* **Lemma 1(c)** `pencilRoots_im_of_posSemidef`: if `H` or `-H` is positive semidefinite, all roots
  are real; hence `stripF_eq_zero_of_semidef`: `F(s, τ) = 0` for `s ≤ λ_min(g)` or `s ≥ λ_max(g)`;
* `stripF_support`, `stripF_bound`: there are `R`, `C` with `F(s, τ) = 0` for `|s| ≥ R` and
  `F(s, τ) ≤ C / √(τ (1 - τ))` for `0 < τ < 1` (compact support and integrability of `F`).

Here `‖·‖_F` is the Frobenius norm (`frob A = ∑ |A_ij|²`); the paper uses the operator norm, which
is smaller, so the paper's bound is slightly sharper.  No hypotheses remain in this file.
Paper: `iqoqi/programs/oqp27B_all/Q_2bmv/PROOF.md`, Lemma 1(b),(c).
-/

namespace OQP27.StripL3b

open Matrix Polynomial MeasureTheory Filter Topology Real
open scoped ComplexOrder

variable {M : ℕ}

/-! ### Euclidean quantities through dot products -/

/-- `Re ⟨v, v⟩ = ∑ |v_i|²`. -/
lemma re_star_dotProduct_self (v : Fin M → ℂ) : (star v ⬝ᵥ v).re = ∑ i, ‖v i‖ ^ 2 := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.star_def, Complex.mul_re, Complex.conj_re,
    Complex.conj_im]
  ring

lemma re_star_dotProduct_self_pos {v : Fin M → ℂ} (hv : v ≠ 0) : 0 < (star v ⬝ᵥ v).re := by
  rw [re_star_dotProduct_self]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have hpos : 0 < ‖v i‖ ^ 2 := by positivity
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2)
    (fun j _ => by positivity) (Finset.mem_univ i))

/-- The squared Frobenius norm `∑ |A_ij|²`. -/
noncomputable def frob (A : Matrix (Fin M) (Fin M) ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

lemma frob_nonneg (A : Matrix (Fin M) (Fin M) ℂ) : 0 ≤ frob A :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity

/-- `|A v|² ≤ ‖A‖_F² |v|²`. -/
lemma re_dot_mulVec_le_frob (A : Matrix (Fin M) (Fin M) ℂ) (v : Fin M → ℂ) :
    (star (A *ᵥ v) ⬝ᵥ (A *ᵥ v)).re ≤ frob A * (star v ⬝ᵥ v).re := by
  rw [re_star_dotProduct_self, re_star_dotProduct_self, frob, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖(A *ᵥ v) i‖ ≤ ∑ j, ‖A i j‖ * ‖v j‖ := by
    simp only [Matrix.mulVec, dotProduct]
    exact (norm_sum_le _ _).trans (le_of_eq (by simp))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖A i j‖) (fun j => ‖v j‖)
  calc ‖(A *ᵥ v) i‖ ^ 2 ≤ (∑ j, ‖A i j‖ * ‖v j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

/-! ### Eigenvectors of the pencil -/

/-- Every pencil root comes with an eigenvector: `H v = x (P - τ) v`, `v ≠ 0`. -/
lemma exists_pencil_eigvec {P H : Matrix (Fin M) (Fin M) ℂ} (hP : P * P = P) {τ : ℝ}
    (h0 : τ ≠ 0) (h1 : τ ≠ 1) {x : ℂ} (hx : x ∈ pencilRoots P H τ) :
    ∃ v : Fin M → ℂ, v ≠ 0 ∧ H *ᵥ v = x • ((P - (τ : ℂ) • 1) *ᵥ v) := by
  unfold pencilRoots at hx
  set Q := P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ) with hQ
  have hmon := Matrix.charpoly_monic (Q⁻¹ * H)
  have hroot : (Q⁻¹ * H).charpoly.IsRoot x := (Polynomial.mem_roots hmon.ne_zero).mp hx
  rw [Polynomial.IsRoot.def, Matrix.eval_charpoly] at hroot
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hroot
  refine ⟨v, hv0, ?_⟩
  have h2 : (Q⁻¹ * H) *ᵥ v = x • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  have hQinv : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_det_P_sub hP h0 h1)
  calc H *ᵥ v = (Q * (Q⁻¹ * H)) *ᵥ v := by rw [← Matrix.mul_assoc, hQinv, Matrix.one_mul]
    _ = Q *ᵥ ((Q⁻¹ * H) *ᵥ v) := (Matrix.mulVec_mulVec _ _ _).symm
    _ = Q *ᵥ (x • v) := by rw [h2]
    _ = x • (Q *ᵥ v) := Matrix.mulVec_smul _ _ _

lemma isHermitian_P_sub {P : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) (τ : ℝ) :
    (P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)).IsHermitian :=
  hP.sub (isHermitian_one.smul (isSelfAdjoint_ofReal τ))

/-- For a non-real pencil root with eigenvector `v`: `⟨v, (P - τ) v⟩ = 0` and `⟨v, H v⟩ = 0`. -/
lemma nonreal_root_orth {P H : Matrix (Fin M) (Fin M) ℂ} (hP : P.IsHermitian) (hH : H.IsHermitian)
    (τ : ℝ) {v : Fin M → ℂ} {x : ℂ} (hv : H *ᵥ v = x • ((P - (τ : ℂ) • 1) *ᵥ v))
    (hx : x.im ≠ 0) :
    star v ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v) = 0 ∧ star v ⬝ᵥ (H *ᵥ v) = 0 := by
  have hc : (star v ⬝ᵥ ((P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)) *ᵥ v)).im = 0 := by
    simpa using (isHermitian_P_sub hP τ).im_star_dotProduct_mulVec_self v
  have hh : (star v ⬝ᵥ (H *ᵥ v)).im = 0 := by
    simpa using hH.im_star_dotProduct_mulVec_self v
  set c := star v ⬝ᵥ ((P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)) *ᵥ v) with hc_def
  have heq : star v ⬝ᵥ (H *ᵥ v) = x * c := by
    rw [hv, dotProduct_smul, smul_eq_mul]
  rw [heq] at hh
  have hcre : c.re = 0 := by
    rw [Complex.mul_im, hc, mul_zero, zero_add] at hh
    exact (mul_eq_zero.mp hh).resolve_left hx
  have hc0 : c = 0 := Complex.ext hcre hc
  exact ⟨hc0, by rw [heq, hc0, mul_zero]⟩

/-- `(P - τ)² = (1 - 2τ)(P - τ) + τ(1 - τ)`. -/
lemma P_sub_mul_self {P : Matrix (Fin M) (Fin M) ℂ} (hP : P * P = P) (τ : ℂ) :
    (P - τ • (1 : Matrix (Fin M) (Fin M) ℂ)) * (P - τ • 1)
      = (1 - 2 * τ) • (P - τ • 1) + (τ * (1 - τ)) • (1 : Matrix (Fin M) (Fin M) ℂ) := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, hP]
  module

/-- If `⟨v, (P - τ) v⟩ = 0` then `|(P - τ) v|² = τ (1 - τ) |v|²`. -/
lemma dot_P_sub_mulVec {P : Matrix (Fin M) (Fin M) ℂ} (hP : IsProj P) (τ : ℝ) (v : Fin M → ℂ)
    (hv : star v ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v) = 0) :
    star ((P - (τ : ℂ) • 1) *ᵥ v) ⬝ᵥ ((P - (τ : ℂ) • 1) *ᵥ v)
      = ((τ : ℂ) * (1 - τ)) * (star v ⬝ᵥ v) := by
  have hQ := isHermitian_P_sub hP.1 τ
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hQ.eq, Matrix.mulVec_mulVec,
    P_sub_mul_self hP.2, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_add, dotProduct_smul, dotProduct_smul, hv,
    smul_zero, zero_add, smul_eq_mul]

/-- **Lemma 1(b).**  Every non-real pencil root satisfies `|x|² τ (1 - τ) ≤ ‖H‖_F²`. -/
lemma normSq_nonreal_root_le {P H : Matrix (Fin M) (Fin M) ℂ} (hP : IsProj P)
    (hH : H.IsHermitian) {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) {x : ℂ}
    (hx : x ∈ pencilRoots P H τ) (hxim : x.im ≠ 0) :
    ‖x‖ ^ 2 * (τ * (1 - τ)) ≤ frob H := by
  obtain ⟨v, hv0, hv⟩ := exists_pencil_eigvec hP.2 h0.ne' h1.ne hx
  have horth := (nonreal_root_orth hP.1 hH τ hv hxim).1
  have hQQ := dot_P_sub_mulVec hP τ v horth
  have hHv : star (H *ᵥ v) ⬝ᵥ (H *ᵥ v)
      = ((‖x‖ : ℂ) ^ 2 * ((τ : ℂ) * (1 - τ))) * (star v ⬝ᵥ v) := by
    rw [hv, star_smul, smul_dotProduct, dotProduct_smul, hQQ, smul_eq_mul,
      smul_eq_mul, ← mul_assoc, ← mul_assoc, Complex.star_def, Complex.conj_mul']
  have hle := re_dot_mulVec_le_frob H v
  rw [hHv] at hle
  have hre : (((‖x‖ : ℂ) ^ 2 * ((τ : ℂ) * (1 - τ))) * (star v ⬝ᵥ v)).re
      = (‖x‖ ^ 2 * (τ * (1 - τ))) * (star v ⬝ᵥ v).re := by
    have e : ((‖x‖ : ℂ) ^ 2 * ((τ : ℂ) * (1 - τ))) = ((‖x‖ ^ 2 * (τ * (1 - τ)) : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.re_ofReal_mul]
  rw [hre] at hle
  exact le_of_mul_le_mul_right hle (re_star_dotProduct_self_pos hv0)

/-- `∑ |Im x_i| ≤ M ‖H‖_F / √(τ (1 - τ))`. -/
lemma imAbsSum_pencilRoots_le {P H : Matrix (Fin M) (Fin M) ℂ} (hP : IsProj P)
    (hH : H.IsHermitian) {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) :
    imAbsSum (pencilRoots P H τ) ≤ M * (√(frob H) / √(τ * (1 - τ))) := by
  have hτ : 0 < τ * (1 - τ) := mul_pos h0 (by linarith)
  have hterm : ∀ x ∈ pencilRoots P H τ, |x.im| ≤ √(frob H) / √(τ * (1 - τ)) := by
    intro x hx
    by_cases hxim : x.im = 0
    · rw [hxim, abs_zero]; positivity
    · have hb := normSq_nonreal_root_le hP hH h0 h1 hx hxim
      have h2 : ‖x‖ ≤ √(frob H) / √(τ * (1 - τ)) := by
        rw [le_div_iff₀ (Real.sqrt_pos.mpr hτ), ← Real.sqrt_sq (norm_nonneg x),
          ← Real.sqrt_mul (sq_nonneg _)]
        exact Real.sqrt_le_sqrt hb
      exact (Complex.abs_im_le_norm x).trans h2
  have hcard : (pencilRoots P H τ).card = M := by
    unfold pencilRoots
    rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  unfold imAbsSum
  calc ((pencilRoots P H τ).map fun z => |z.im|).sum
      ≤ ((pencilRoots P H τ).map fun _ => √(frob H) / √(τ * (1 - τ))).sum :=
        Multiset.sum_map_le_sum_map _ _ hterm
    _ = M * (√(frob H) / √(τ * (1 - τ))) := by
        rw [Multiset.map_const', Multiset.sum_replicate, hcard, nsmul_eq_mul]

/-- **Bound on `F`** (Lemma 1(b)): `F(s, τ) ≤ M ‖g - s‖_F / (2π √(τ (1 - τ)))`. -/
theorem stripF_le {P g : Matrix (Fin M) (Fin M) ℂ} (hP : IsProj P) (hg : g.IsHermitian)
    (s : ℝ) {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) :
    stripF P g s τ ≤ M * (√(frob (g - (s : ℂ) • 1)) / √(τ * (1 - τ))) / (2 * π) := by
  rw [stripF, if_pos ⟨h0, h1⟩]
  have hH : (g - (s : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)).IsHermitian :=
    hg.sub (isHermitian_one.smul (isSelfAdjoint_ofReal s))
  exact div_le_div_of_nonneg_right (imAbsSum_pencilRoots_le hP hH h0 h1) (by positivity)

/-! ### Semidefinite slices: all roots real (Lemma 1(c)) -/

/-- **Lemma 1(c).**  If `H` or `-H` is positive semidefinite, all pencil roots are real. -/
lemma pencilRoots_im_of_posSemidef {P H : Matrix (Fin M) (Fin M) ℂ} (hP : IsProj P)
    (hH : H.PosSemidef ∨ (-H).PosSemidef) {τ : ℝ} (h0 : τ ≠ 0) (h1 : τ ≠ 1) :
    ∀ x ∈ pencilRoots P H τ, x.im = 0 := by
  intro x hx
  by_contra hxim
  have hHerm : H.IsHermitian := by
    rcases hH with h | h
    · exact h.isHermitian
    · simpa using h.isHermitian.neg
  obtain ⟨v, hv0, hv⟩ := exists_pencil_eigvec hP.2 h0 h1 hx
  have horth := (nonreal_root_orth hP.1 hHerm τ hv hxim).2
  have hHv : H *ᵥ v = 0 := by
    rcases hH with h | h
    · exact (h.dotProduct_mulVec_zero_iff v).mp horth
    · have : star v ⬝ᵥ ((-H) *ᵥ v) = 0 := by
        rw [Matrix.neg_mulVec, dotProduct_neg, horth, neg_zero]
      have h2 := (h.dotProduct_mulVec_zero_iff v).mp this
      rw [Matrix.neg_mulVec, neg_eq_zero] at h2
      exact h2
  rw [hHv] at hv
  have hx0 : x ≠ 0 := fun h => hxim (by rw [h, Complex.zero_im])
  have hQv : (P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)) *ᵥ v = 0 :=
    (smul_eq_zero.mp hv.symm).resolve_left hx0
  apply hv0
  calc v = ((P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹ * (P - (τ : ℂ) • 1)) *ᵥ v := by
        rw [inv_P_sub_mul_self hP.2 h0 h1, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, hQv, Matrix.mulVec_zero]

/-- Spectral form of `A - c` for Hermitian `A`. -/
lemma sub_smul_one_eq_conj {A : Matrix (Fin M) (Fin M) ℂ} (hA : A.IsHermitian) (c : ℝ) :
    A - (c : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)
      = (hA.eigenvectorUnitary : Matrix (Fin M) (Fin M) ℂ)
        * Matrix.diagonal (fun i => ((hA.eigenvalues i - c : ℝ) : ℂ))
        * star (hA.eigenvectorUnitary : Matrix (Fin M) (Fin M) ℂ) := by
  set U : Matrix (Fin M) (Fin M) ℂ := (hA.eigenvectorUnitary : Matrix (Fin M) (Fin M) ℂ) with hU
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hdiag : Matrix.diagonal (fun i => ((hA.eigenvalues i - c : ℝ) : ℂ))
      = Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) - (c : ℂ) • 1 := by
    rw [Matrix.smul_one_eq_diagonal, Matrix.diagonal_sub]
    congr 1
    funext i
    simp
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, hdiag, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
    Matrix.mul_one, Matrix.smul_mul, hUU]

lemma posSemidef_sub_smul_one {A : Matrix (Fin M) (Fin M) ℂ} (hA : A.IsHermitian) {c : ℝ}
    (h : ∀ i, c ≤ hA.eigenvalues i) : (A - (c : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)).PosSemidef := by
  have hd : (Matrix.diagonal (fun i => ((hA.eigenvalues i - c : ℝ) : ℂ))).PosSemidef :=
    PosSemidef.diagonal fun i => Complex.zero_le_real.mpr (by linarith [h i])
  have := hd.mul_mul_conjTranspose_same (hA.eigenvectorUnitary : Matrix (Fin M) (Fin M) ℂ)
  rw [sub_smul_one_eq_conj hA c, Matrix.star_eq_conjTranspose]
  exact this

lemma posSemidef_neg_sub_smul_one {A : Matrix (Fin M) (Fin M) ℂ} (hA : A.IsHermitian) {c : ℝ}
    (h : ∀ i, hA.eigenvalues i ≤ c) :
    (-(A - (c : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))).PosSemidef := by
  have hd : (Matrix.diagonal (fun i => ((c - hA.eigenvalues i : ℝ) : ℂ))).PosSemidef :=
    PosSemidef.diagonal fun i => Complex.zero_le_real.mpr (by linarith [h i])
  have hconj := hd.mul_mul_conjTranspose_same (hA.eigenvectorUnitary : Matrix (Fin M) (Fin M) ℂ)
  have e : Matrix.diagonal (fun i => ((c - hA.eigenvalues i : ℝ) : ℂ))
      = -Matrix.diagonal (fun i => ((hA.eigenvalues i - c : ℝ) : ℂ)) := by
    rw [Matrix.diagonal_neg]
    congr 1
    funext i
    push_cast
    ring
  rw [e, Matrix.mul_neg, Matrix.neg_mul, ← Matrix.star_eq_conjTranspose] at hconj
  rw [sub_smul_one_eq_conj hA c]
  exact hconj

/-- **Support of `F` in `s`** (Lemma 1(c)): `F(s, τ) = 0` if `s ≤ λ_min(g)` or `s ≥ λ_max(g)`. -/
theorem stripF_eq_zero_of_semidef {P g : Matrix (Fin M) (Fin M) ℂ} (hP : IsProj P)
    (hg : g.IsHermitian) {s τ : ℝ}
    (hs : (∀ i, s ≤ hg.eigenvalues i) ∨ (∀ i, hg.eigenvalues i ≤ s)) :
    stripF P g s τ = 0 := by
  unfold stripF
  split_ifs with hτ
  · have hpsd : (g - (s : ℂ) • 1).PosSemidef ∨ (-(g - (s : ℂ) • 1)).PosSemidef := by
      rcases hs with h | h
      · exact Or.inl (posSemidef_sub_smul_one hg h)
      · exact Or.inr (posSemidef_neg_sub_smul_one hg h)
    have hreal := pencilRoots_im_of_posSemidef hP hpsd hτ.1.ne' hτ.2.ne
    have hzero : imAbsSum (pencilRoots P (g - (s : ℂ) • 1) τ) = 0 := by
      unfold imAbsSum
      rw [Multiset.map_congr rfl (fun z hz => by rw [hreal z hz, abs_zero])]
      simp
    rw [hzero, zero_div]
  · rfl

/-- **Compact support of `F`**: there is `R` with `F(s, τ) = 0` whenever `|s| ≥ R`. -/
theorem stripF_support {P g : Matrix (Fin M) (Fin M) ℂ} (hP : IsProj P) (hg : g.IsHermitian) :
    ∃ R : ℝ, 0 < R ∧ ∀ s τ : ℝ, R ≤ |s| → stripF P g s τ = 0 := by
  refine ⟨1 + ∑ i, |hg.eigenvalues i|, by positivity, fun s τ hs => ?_⟩
  have hle : ∀ i, |hg.eigenvalues i| ≤ ∑ i, |hg.eigenvalues i| := fun i =>
    Finset.single_le_sum (f := fun i => |hg.eigenvalues i|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
  apply stripF_eq_zero_of_semidef hP hg
  rcases le_or_gt 0 s with h | h
  · rw [abs_of_nonneg h] at hs
    exact Or.inr fun i => by linarith [le_abs_self (hg.eigenvalues i), hle i]
  · rw [abs_of_neg h] at hs
    exact Or.inl fun i => by linarith [neg_abs_le (hg.eigenvalues i), hle i]

/-- **Uniform bound on `F`**: there is `C` with `F(s, τ) ≤ C / √(τ (1 - τ))` for all `s` and
`0 < τ < 1`. -/
theorem stripF_bound {P g : Matrix (Fin M) (Fin M) ℂ} (hP : IsProj P) (hg : g.IsHermitian) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s τ : ℝ, 0 < τ → τ < 1 → stripF P g s τ ≤ C / √(τ * (1 - τ)) := by
  obtain ⟨R, hR, hsupp⟩ := stripF_support hP hg
  have hcont : Continuous fun s : ℝ => √(frob (g - (s : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))) := by
    unfold frob
    fun_prop
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨M * max K 0 / (2 * π), by positivity, fun s τ h0 h1 => ?_⟩
  have hτ : 0 < √(τ * (1 - τ)) := Real.sqrt_pos.mpr (mul_pos h0 (by linarith))
  by_cases hs : R ≤ |s|
  · rw [hsupp s τ hs]; positivity
  · have hs : |s| < R := not_le.mp hs
    have hsI : s ∈ Set.Icc (-R) R := ⟨by linarith [neg_abs_le s], by linarith [le_abs_self s]⟩
    have hKs : √(frob (g - (s : ℂ) • 1)) ≤ max K 0 := by
      have := hK s hsI
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at this
      exact this.trans (le_max_left _ _)
    calc stripF P g s τ ≤ M * (√(frob (g - (s : ℂ) • 1)) / √(τ * (1 - τ))) / (2 * π) :=
          stripF_le hP hg s h0 h1
      _ ≤ M * (max K 0 / √(τ * (1 - τ))) / (2 * π) := by
          gcongr
      _ = M * max K 0 / (2 * π) / √(τ * (1 - τ)) := by ring

end OQP27.StripL3b
