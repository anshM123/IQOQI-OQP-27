import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Algebra.BigOperators.Fin

/-!
# OQP 27B rigidity: matrix units give the tensor decomposition `ℂ^D ≅ ℂ^d ⊗ ℂ^K` (module L6)

Paper: `publish/CGLMP/rigidity/RIGIDITY.md`, Theorem 3.9 (finite-dimensional form). The Lean library
`formal-conjectures/CGLMPRigidity` proves only the consequence `d ∣ D`; here the unitary itself is
constructed (no hypotheses):

* `OQP27.Rig.exists_isometry_of_proj`: for a projection `p` on `ℂ^n` there are `K` and an isometry
  `Φ : ℂ^K → ℂ^n` with `Φ^* Φ = 1` and `Φ Φ^* = p` (columns: the eigenvectors of `p` for the eigenvalue
  `1`, from the spectral theorem `Matrix.IsHermitian.spectral_theorem`).
* `OQP27.Rig.exists_unitary_of_matrixUnits`: if `e_{jk}` (`j, k < d`) are `d × d` matrix units in
  `M_D(ℂ)` (`e_{jk} e_{lm} = δ_{kl} e_{jm}`, `e_{jk}^* = e_{kj}`, `∑_j e_{jj} = 1`), then `D = d K` and there
  is a unitary `u : ℂ^D → ℂ^d ⊗ ℂ^K` with `u e_{jk} u^* = |j⟩⟨k| ⊗ 1_K`. Explicitly
  `u^* (|j⟩ ⊗ v) = e_{j0} Φ v`.
-/

set_option linter.unusedSectionVars false

open Matrix Finset
open scoped Kronecker

namespace OQP27.Rig

/-- **Isometry onto the range of a projection.** -/
theorem exists_isometry_of_proj {n : Type*} [Fintype n] [DecidableEq n] (p : Matrix n n ℂ)
    (hH : p.IsHermitian) (hI : p * p = p) :
    ∃ K : ℕ, ∃ Φ : Matrix n (Fin K) ℂ, Φᴴ * Φ = 1 ∧ Φ * Φᴴ = p := by
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  set ev : n → ℝ := hH.eigenvalues with hev_def
  have hUU : Uᴴ * U = 1 := by
    have := (hH.eigenvectorUnitary).2
    rw [Matrix.mem_unitaryGroup_iff'] at this
    exact this
  have hUU' : U * Uᴴ = 1 := mul_eq_one_comm.1 hUU
  have hspec : p = U * diagonal (fun i => (ev i : ℂ)) * Uᴴ := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  -- the eigenvalues of a projection are `0` or `1`
  have hev : ∀ i, ev i = 0 ∨ ev i = 1 := by
    have h1 : Uᴴ * p * U = diagonal (fun i => (ev i : ℂ)) := by
      rw [hspec]
      simp only [Matrix.mul_assoc, hUU, Matrix.mul_one]
      rw [← Matrix.mul_assoc, hUU, Matrix.one_mul]
    have hΛ : diagonal (fun i => (ev i : ℂ)) * diagonal (fun i => (ev i : ℂ))
        = diagonal (fun i => (ev i : ℂ)) := by
      rw [← h1]
      calc Uᴴ * p * U * (Uᴴ * p * U) = Uᴴ * p * (U * Uᴴ) * p * U := by
            simp only [Matrix.mul_assoc]
        _ = Uᴴ * (p * p) * U := by rw [hUU', Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = Uᴴ * p * U := by rw [hI]
    intro i
    have h2 := congrFun (congrFun hΛ i) i
    rw [diagonal_mul_diagonal, diagonal_apply_eq, diagonal_apply_eq] at h2
    have h3 : ev i * ev i = ev i := by exact_mod_cast h2
    have h4 : ev i * (ev i - 1) = 0 := by linarith
    rcases mul_eq_zero.1 h4 with h | h
    · left; exact h
    · right; linarith
  -- the eigenvectors for the eigenvalue `1`
  set S : Finset n := Finset.univ.filter (fun i => ev i = 1) with hS
  set eqv : { x // x ∈ S } ≃ Fin S.card := S.equivFin with heqv
  refine ⟨S.card, Matrix.of fun r μ => U r (eqv.symm μ : n), ?_, ?_⟩
  · ext μ ν
    rw [Matrix.mul_apply]
    simp only [conjTranspose_apply, of_apply]
    have h := congrFun (congrFun hUU (eqv.symm μ : n)) (eqv.symm ν : n)
    rw [Matrix.mul_apply] at h
    simp only [conjTranspose_apply] at h
    rw [h, one_apply, one_apply]
    by_cases hμν : μ = ν
    · subst hμν; simp
    · rw [if_neg hμν, if_neg]
      intro h'
      exact hμν (eqv.symm.injective (Subtype.ext h'))
  · ext r r'
    rw [Matrix.mul_apply]
    simp only [conjTranspose_apply, of_apply]
    have hsum : ∑ μ : Fin S.card, U r (eqv.symm μ : n) * star (U r' (eqv.symm μ : n))
        = ∑ i ∈ S, U r i * star (U r' i) := by
      rw [← Finset.sum_coe_sort S]
      exact Fintype.sum_equiv eqv.symm _ _ (fun μ => rfl)
    rw [hsum]
    conv_rhs => rw [hspec]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, conjTranspose_apply]
    rw [hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases hev i with h | h
    · rw [if_neg (by rw [h]; norm_num), h]; simp
    · rw [if_pos h, h]; simp

/-- **Matrix units in `M_D(ℂ)` give `ℂ^D ≅ ℂ^d ⊗ ℂ^K`** (`RIGIDITY.md` Theorem 3.9). -/
theorem exists_unitary_of_matrixUnits {D : ℕ} (d : ℕ) (hd : 0 < d)
    (e : ℕ → ℕ → Matrix (Fin D) (Fin D) ℂ)
    (hmul : ∀ j k l m, k < d → l < d → e j k * e l m = if k = l then e j m else 0)
    (hstar : ∀ j k, (e j k)ᴴ = e k j)
    (hsum : ∑ j ∈ Finset.range d, e j j = 1) :
    ∃ K : ℕ, D = d * K ∧ ∃ u : Matrix (Fin d × Fin K) (Fin D) ℂ, u * uᴴ = 1 ∧ uᴴ * u = 1 ∧
      ∀ j k : Fin d,
        u * e j k * uᴴ = Matrix.single j k (1 : ℂ) ⊗ₖ (1 : Matrix (Fin K) (Fin K) ℂ) := by
  obtain ⟨K, Φ, hΦ1, hΦ2⟩ := exists_isometry_of_proj (e 0 0) (hstar 0 0)
    (by rw [hmul 0 0 0 0 hd hd, if_pos rfl])
  have hP : Φᴴ * e 0 0 * Φ = 1 := by
    rw [← hΦ2, show Φᴴ * (Φ * Φᴴ) * Φ = Φᴴ * Φ * (Φᴴ * Φ) by simp only [Matrix.mul_assoc], hΦ1,
      Matrix.mul_one]
  -- block identities
  have hB3 : ∀ j k a b : ℕ, j < d → k < d → a < d → b < d →
      (e j 0 * Φ)ᴴ * e a b * (e k 0 * Φ) = if j = a ∧ b = k then 1 else 0 := by
    intro j k a b hj hk ha hb
    rw [conjTranspose_mul, hstar]
    have e1 : Φᴴ * e 0 j * e a b * (e k 0 * Φ) = Φᴴ * (e 0 j * e a b * e k 0) * Φ := by
      simp only [Matrix.mul_assoc]
    rw [e1, hmul 0 j a b hj ha]
    split_ifs with h1 h2 h2
    · rw [hmul 0 b k 0 hb hk, if_pos h2.2, hP]
    · rw [hmul 0 b k 0 hb hk, if_neg (fun h => h2 ⟨h1, h⟩), Matrix.mul_zero, Matrix.zero_mul]
    · exact absurd h2.1 h1
    · rw [Matrix.zero_mul, Matrix.mul_zero, Matrix.zero_mul]
  have hB1 : ∀ j k : ℕ, j < d → k < d → (e j 0 * Φ)ᴴ * (e k 0 * Φ) = if j = k then 1 else 0 := by
    intro j k hj hk
    rw [conjTranspose_mul, hstar]
    have e1 : Φᴴ * e 0 j * (e k 0 * Φ) = Φᴴ * (e 0 j * e k 0) * Φ := by
      simp only [Matrix.mul_assoc]
    rw [e1, hmul 0 j k 0 hj hk]
    split_ifs
    · exact hP
    · rw [Matrix.mul_zero, Matrix.zero_mul]
  have hB2 : ∑ j ∈ Finset.range d, (e j 0 * Φ) * (e j 0 * Φ)ᴴ = 1 := by
    rw [← hsum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    rw [conjTranspose_mul, hstar]
    calc e j 0 * Φ * (Φᴴ * e 0 j) = e j 0 * (Φ * Φᴴ) * e 0 j := by simp only [Matrix.mul_assoc]
      _ = e j j := by rw [hΦ2, hmul j 0 0 0 hd hd, if_pos rfl, hmul j 0 0 j hd hd, if_pos rfl]
  -- the unitary
  set W : Matrix (Fin D) (Fin d × Fin K) ℂ := Matrix.of fun r q => (e q.1 0 * Φ) r q.2 with hW
  have hE1 : ∀ X : Matrix (Fin D) (Fin D) ℂ, ∀ q q' : Fin d × Fin K,
      (Wᴴ * X * W) q q' = ((e q.1 0 * Φ)ᴴ * X * (e q'.1 0 * Φ)) q.2 q'.2 := by
    intro X q q'
    simp only [Matrix.mul_apply, conjTranspose_apply, hW, of_apply]
  have hE2 : ∀ r r' : Fin D,
      (W * Wᴴ) r r' = ∑ j ∈ Finset.range d, ((e j 0 * Φ) * (e j 0 * Φ)ᴴ) r r' := by
    intro r r'
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    simp only [conjTranspose_apply, hW, of_apply]
    rw [← Fin.sum_univ_eq_sum_range (fun j => ((e j 0 * Φ) * (e j 0 * Φ)ᴴ) r r') d]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_apply]
    simp only [conjTranspose_apply]
  have hWW : Wᴴ * W = 1 := by
    ext q q'
    have h := hE1 1 q q'
    rw [Matrix.mul_one, Matrix.mul_one] at h
    rw [h, hB1 q.1 q'.1 q.1.isLt q'.1.isLt]
    obtain ⟨j, μ⟩ := q
    obtain ⟨k, ν⟩ := q'
    simp only [one_apply, Prod.mk.injEq]
    by_cases hjk : (j : ℕ) = k
    · have : j = k := Fin.ext hjk
      subst this
      simp [Matrix.one_apply]
    · have : j ≠ k := fun h => hjk (congrArg Fin.val h)
      simp [hjk, this]
  have hWW' : W * Wᴴ = 1 := by
    ext r r'
    rw [hE2, ← Matrix.sum_apply, hB2]
  refine ⟨K, ?_, Wᴴ, ?_, ?_, ?_⟩
  · have h := congrArg Matrix.trace hWW'
    rw [Matrix.trace_mul_comm, hWW, trace_one, trace_one] at h
    simp only [Fintype.card_prod, Fintype.card_fin] at h
    exact_mod_cast h.symm
  · rw [conjTranspose_conjTranspose]; exact hWW
  · rw [conjTranspose_conjTranspose]; exact hWW'
  · intro a b
    rw [conjTranspose_conjTranspose]
    ext q q'
    rw [hE1, hB3 q.1 q'.1 a b q.1.isLt q'.1.isLt a.isLt b.isLt, kroneckerMap_apply,
      single_apply]
    obtain ⟨j, μ⟩ := q
    obtain ⟨k, ν⟩ := q'
    simp only
    by_cases h1 : (j : ℕ) = a
    · have e1 : j = a := Fin.ext h1
      subst e1
      by_cases h2 : (b : ℕ) = k
      · have e2 : b = k := Fin.ext h2
        subst e2
        simp [Matrix.one_apply]
      · have e2 : b ≠ k := fun h => h2 (congrArg Fin.val h)
        simp [h2, e2]
    · have e1 : a ≠ j := fun h => h1 (congrArg Fin.val h.symm)
      simp [h1, e1]

end OQP27.Rig
