import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Matrix facts for the strip inequality (OQP 27B formalisation, module L3a)

`B` is an orthogonal projection on `ℂ^M` (`B.IsHermitian ∧ B * B = B`), `P = 1 - B`, `g` is
Hermitian.  The eigenvalues of the non-Hermitian matrix `B + i g` are the multiset
`(B + I • g).charpoly.roots` (shared convention of `OQP27/LEAN_BRIEF.md`).

Proved here (no hypotheses; all proofs complete):
* `trace_pow_eq_sum_roots`, `trace_exp_smul_eq_sum_roots`: `Tr Xⁿ = Σ νⁿ` and `Tr e^{cX} = Σ e^{cν}`
  over the roots `ν` of the characteristic polynomial of any complex matrix `X` (generalized
  eigenspace decomposition);
* `re_mem_Icc_of_mem_roots`: the eigenvalues of `B + ig` lie in the closed strip `0 ≤ Re ν ≤ 1`;
* `exists_compression_basis`: a unitary `U` diagonalising both `P` (eigenvalues `p_j ∈ {0, 1}`) and
  the compression `PgP` (eigenvalues `d_j`, `d_j = 0` when `p_j = 0`), so that
  `spec(PgP|ran P) = {d_j : p_j = 1}`; consequences `trace_mul_exp_of_diag`
  (`Tr_P e^{a PgP} = Σ_j p_j e^{a d_j}`) and `posPartTrace_compress_eq`
  (`Tr[(P(g - λ)P)_+] = Σ_j p_j (d_j - λ)_+`);
* `mass_moment_eq`: `Σ_ν (1 - Re ν) = Σ_j p_j` and `Σ_ν (1 - Re ν) Im ν = Σ_j p_j d_j`;
* `stripD`: the function `D(a, t)` of the paper, and `stripD_sub_eq`, the matrix side of step (a)
  of the proof of Theorem 2;
* `stripD_eq_sub_pinch`: `D(a, t) = Tr e^{ag - tP} - Tr e^{a g_d - tP}` with the pinching
  `g_d = BgB + PgP` (the form used by module L3b);
* the equality case: `stripD_zero_of_commute` (`[B, g] = 0 ⇒ D(·, 0) ≡ 0`) and
  `commute_of_stripD_zero` (`D(·, 0) ≡ 0 ⇒ [B, g] = 0`, via the second derivative at `0`,
  `2 ‖BgP‖_F²`; this replaces the Duhamel computation of Remark 4.3 of the paper).

Paper: `iqoqi/programs/oqp27B_all/Q_2bmv/PROOF.md`, section 0 and section 5 (proof of Theorem 2).
-/

open Matrix Polynomial Complex
open scoped ComplexOrder

namespace OQP27.StripL3a

variable {M : ℕ}

/-! ### Traces of powers and exponentials through the roots of the characteristic polynomial -/

/-- On a generalized eigenspace, `trace (f|^n) = μ^n · dim`. -/
lemma trace_restrict_pow {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (μ : ℂ) (n : ℕ) :
    LinearMap.trace ℂ _ ((f.restrict (f.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ)) ^ n)
      = μ ^ n * (Module.finrank ℂ (f.maxGenEigenspace μ) : ℂ) := by
  set g := f.restrict (f.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ) with hg
  have hnil : IsNilpotent (g - algebraMap ℂ (Module.End ℂ (f.maxGenEigenspace μ)) μ) :=
    f.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ
  induction n with
  | zero => simp [LinearMap.trace_one]
  | succ n ih =>
    rw [pow_succ, Module.End.mul_eq_comp, LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent μ
      ((Commute.refl g).pow_left n) hnil, ih]
    ring

/-- `Tr Xⁿ = Σ νⁿ` over the roots `ν` of the characteristic polynomial (with multiplicity). -/
theorem trace_pow_eq_sum_roots (X : Matrix (Fin M) (Fin M) ℂ) (n : ℕ) :
    (X ^ n).trace = (X.charpoly.roots.map (fun ν => ν ^ n)).sum := by
  classical
  set f : Module.End ℂ (Fin M → ℂ) := Matrix.toLin' X with hf
  have hint : DirectSum.IsInternal (fun μ => f.maxGenEigenspace μ) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top f.independent_maxGenEigenspace
      f.iSup_maxGenEigenspace_eq_top
  have hfin : {μ | f.maxGenEigenspace μ ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep f.independent_maxGenEigenspace
  have hmaps : ∀ μ, Set.MapsTo (f ^ n) (f.maxGenEigenspace μ) (f.maxGenEigenspace μ) :=
    fun μ => f.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right n) μ
  have hcp : LinearMap.charpoly f = X.charpoly := Matrix.charpoly_toLin' X
  have hne : X.charpoly ≠ 0 := X.charpoly_monic.ne_zero
  rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_pow, ← hf,
    LinearMap.trace_eq_sum_trace_restrict' hint hfin hmaps]
  have hloc : ∀ μ, LinearMap.trace ℂ _ ((f ^ n).restrict (hmaps μ))
      = μ ^ n * ((X.charpoly.rootMultiplicity μ : ℕ) : ℂ) := by
    intro μ
    rw [← hcp, ← LinearMap.finrank_maxGenEigenspace_eq, ← trace_restrict_pow f μ n]
    exact congrArg _ (Module.End.pow_restrict n (f.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ)).symm
  rw [Finset.sum_congr rfl (fun μ _ => hloc μ), Finset.sum_multiset_map_count]
  have hset : hfin.toFinset = X.charpoly.roots.toFinset := by
    ext μ
    rw [Set.Finite.mem_toFinset, Multiset.mem_toFinset, Polynomial.mem_roots hne,
      ← Polynomial.rootMultiplicity_pos hne, ← hcp, ← LinearMap.finrank_maxGenEigenspace_eq,
      Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    rfl
  rw [hset]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [Polynomial.count_roots, nsmul_eq_mul]
  ring

lemma hasSum_multiset_sum {β : Type*} (S : Multiset β) (F : β → ℕ → ℂ) (G : β → ℂ)
    (h : ∀ b ∈ S, HasSum (F b) (G b)) :
    HasSum (fun n => (S.map (fun b => F b n)).sum) (S.map G).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact (h a (Multiset.mem_cons_self a S)).add
      (ih fun b hb => h b (Multiset.mem_cons_of_mem hb))

/-- `Tr exp(c X) = Σ e^{cν}` over the roots `ν` of the characteristic polynomial. -/
theorem trace_exp_smul_eq_sum_roots (X : Matrix (Fin M) (Fin M) ℂ) (c : ℂ) :
    (NormedSpace.exp (c • X)).trace = (X.charpoly.roots.map (fun ν => cexp (c * ν))).sum := by
  let : NormedRing (Matrix (Fin M) (Fin M) ℂ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℂ (Matrix (Fin M) (Fin M) ℂ) := Matrix.linftyOpNormedAlgebra
  have hX := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (c • X)
  have hT := hX.map (Matrix.traceAddMonoidHom (Fin M) ℂ) (continuous_id.matrix_trace)
  have hterm : ∀ n : ℕ, (Matrix.traceAddMonoidHom (Fin M) ℂ) (((n.factorial : ℂ))⁻¹ • (c • X) ^ n)
      = (X.charpoly.roots.map (fun ν => ((n.factorial : ℂ))⁻¹ • (c * ν) ^ n)).sum := by
    intro n
    rw [Matrix.traceAddMonoidHom_apply, smul_pow, Matrix.trace_smul, Matrix.trace_smul,
      trace_pow_eq_sum_roots]
    simp_rw [smul_eq_mul, mul_pow]
    rw [Multiset.sum_map_mul_left, Multiset.sum_map_mul_left]
  have hR : HasSum (fun n : ℕ => (X.charpoly.roots.map
      (fun ν => ((n.factorial : ℂ))⁻¹ • (c * ν) ^ n)).sum)
      (X.charpoly.roots.map (fun ν => cexp (c * ν))).sum := by
    refine hasSum_multiset_sum _ (fun ν n => ((n.factorial : ℂ))⁻¹ • (c * ν) ^ n) _ (fun ν _ => ?_)
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (c * ν)
  have hT' : HasSum (fun n : ℕ => (X.charpoly.roots.map
      (fun ν => ((n.factorial : ℂ))⁻¹ • (c * ν) ^ n)).sum) (NormedSpace.exp (c • X)).trace := by
    refine hT.congr_fun ?_
    intro n
    exact (hterm n).symm
  exact hT'.unique hR

/-! ### The eigenvalues of `B + i g` lie in the closed strip -/

lemma card_roots_charpoly (X : Matrix (Fin M) (Fin M) ℂ) : X.charpoly.roots.card = M := by
  rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

lemma trace_im_eq_zero {A : Matrix (Fin M) (Fin M) ℂ} (hA : A.IsHermitian) : A.trace.im = 0 := by
  have h := Matrix.trace_conjTranspose A
  rw [hA.eq] at h
  exact Complex.conj_eq_iff_im.mp h.symm

lemma exists_mulVec_eq_smul_of_mem_roots {X : Matrix (Fin M) (Fin M) ℂ} {ν : ℂ}
    (hν : ν ∈ X.charpoly.roots) : ∃ v : Fin M → ℂ, v ≠ 0 ∧ X *ᵥ v = ν • v := by
  have hroot : X.charpoly.IsRoot ν := (Polynomial.mem_roots X.charpoly_monic.ne_zero).mp hν
  have hdet : (Matrix.scalar (Fin M) ν - X).det = 0 := by
    rw [← Matrix.eval_charpoly]; exact hroot
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨v, hv0, ?_⟩
  rw [Matrix.sub_mulVec, sub_eq_zero] at hv
  rw [← hv]
  simp [Matrix.scalar_apply]

/-- **The eigenvalues of `B + i g` lie in the closed strip** `0 ≤ Re ν ≤ 1` (`Re ⟨v, Xv⟩ = |Bv|²`). -/
theorem re_mem_Icc_of_mem_roots {B g : Matrix (Fin M) (Fin M) ℂ} (hB : B.IsHermitian ∧ B * B = B)
    (hg : g.IsHermitian) {ν : ℂ} (hν : ν ∈ (B + I • g).charpoly.roots) :
    0 ≤ ν.re ∧ ν.re ≤ 1 := by
  obtain ⟨v, hv0, hXv⟩ := exists_mulVec_eq_smul_of_mem_roots hν
  have hBB : B = Bᴴ * B := by rw [hB.1.eq, hB.2]
  have hPh : (1 - B).IsHermitian := isHermitian_one.sub hB.1
  have hPP : (1 - B) * (1 - B) = 1 - B := by
    rw [sub_mul, mul_sub, mul_sub, hB.2]; simp
  have hPP' : 1 - B = (1 - B)ᴴ * (1 - B) := by rw [hPh.eq, hPP]
  have hBpos : 0 ≤ star v ⬝ᵥ (B *ᵥ v) := by
    rw [hBB]; exact (posSemidef_conjTranspose_mul_self B).dotProduct_mulVec_nonneg v
  have hPpos : 0 ≤ star v ⬝ᵥ ((1 - B) *ᵥ v) := by
    rw [hPP']; exact (posSemidef_conjTranspose_mul_self (1 - B)).dotProduct_mulVec_nonneg v
  have hsum : star v ⬝ᵥ (B *ᵥ v) + star v ⬝ᵥ ((1 - B) *ᵥ v) = star v ⬝ᵥ v := by
    rw [← dotProduct_add, ← Matrix.add_mulVec, add_sub_cancel, Matrix.one_mulVec]
  have hgre : (star v ⬝ᵥ (g *ᵥ v)).im = 0 := hg.im_star_dotProduct_mulVec_self v
  have hq : 0 < (star v ⬝ᵥ v).re := by
    have := (Matrix.dotProduct_star_self_pos_iff (v := v)).mpr hv0
    exact (Complex.pos_iff.mp this).1
  have hqim : (star v ⬝ᵥ v).im = 0 := by
    have := (Matrix.dotProduct_star_self_pos_iff (v := v)).mpr hv0
    exact ((Complex.pos_iff.mp this).2).symm
  have hmain : ν * (star v ⬝ᵥ v) = star v ⬝ᵥ (B *ᵥ v) + I * (star v ⬝ᵥ (g *ᵥ v)) := by
    have h1 : star v ⬝ᵥ ((B + I • g) *ᵥ v) = ν * (star v ⬝ᵥ v) := by
      rw [hXv, dotProduct_smul, smul_eq_mul]
    rw [← h1, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hre := congrArg Complex.re hmain
  simp only [Complex.mul_re, hqim, mul_zero, sub_zero, Complex.add_re, Complex.I_re, zero_mul,
    Complex.I_im, hgre, add_zero] at hre
  have hB0 := (Complex.nonneg_iff.mp hBpos).1
  have hP0 := (Complex.nonneg_iff.mp hPpos).1
  have hs := congrArg Complex.re hsum
  rw [Complex.add_re] at hs
  constructor
  · by_contra hneg
    push Not at hneg
    have : ν.re * (star v ⬝ᵥ v).re < 0 := mul_neg_of_neg_of_pos hneg hq
    linarith
  · by_contra hgt
    push Not at hgt
    have : (star v ⬝ᵥ v).re < ν.re * (star v ⬝ᵥ v).re := by nlinarith
    linarith


/-! ### The positive part of a Hermitian matrix -/

/-- `Tr[A_+] = Σ_i max(λ_i(A), 0)` for Hermitian `A` (the shared convention of
`OQP27/LEAN_BRIEF.md`); `0` if `A` is not Hermitian. -/
noncomputable def posPartTrace (A : Matrix (Fin M) (Fin M) ℂ) : ℝ :=
  if h : A.IsHermitian then ∑ i, max (h.eigenvalues i) 0 else 0

lemma posPartTrace_eq {A : Matrix (Fin M) (Fin M) ℂ} (hA : A.IsHermitian) :
    posPartTrace A = ∑ i, max (hA.eigenvalues i) 0 := dif_pos hA

/-- `P (g - λ) P` is Hermitian for a projection `B`, `P = 1 - B`, and Hermitian `g`. -/
lemma isHermitian_compress_sub {B g : Matrix (Fin M) (Fin M) ℂ} (hB : B.IsHermitian)
    (hg : g.IsHermitian) (lam : ℝ) : ((1 - B) * (g - (lam : ℂ) • 1) * (1 - B)).IsHermitian := by
  have hPh : (1 - B).IsHermitian := isHermitian_one.sub hB
  have hgl : (g - (lam : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)).IsHermitian := by
    refine hg.sub ?_
    unfold IsHermitian
    rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
  unfold IsHermitian
  rw [conjTranspose_mul, conjTranspose_mul, hPh.eq, hgl.eq, Matrix.mul_assoc]

/-! ### The compression `P g P` in an eigenbasis adapted to `P = 1 - B` -/

section Compression

variable {B g : Matrix (Fin M) (Fin M) ℂ}

lemma proj_compl_facts (hB : B.IsHermitian ∧ B * B = B) :
    (1 - B).IsHermitian ∧ (1 - B) * (1 - B) = 1 - B ∧ B * (1 - B) = 0 ∧ (1 - B) * B = 0 := by
  refine ⟨isHermitian_one.sub hB.1, ?_, ?_, ?_⟩
  · rw [sub_mul, mul_sub, mul_sub, hB.2]; simp
  · rw [mul_sub, hB.2]; simp
  · rw [sub_mul, hB.2]; simp

lemma isHermitian_compress (hB : B.IsHermitian ∧ B * B = B) (hg : g.IsHermitian) :
    ((1 - B) * g * (1 - B)).IsHermitian := by
  have hPh := (proj_compl_facts hB).1
  unfold IsHermitian
  rw [conjTranspose_mul, conjTranspose_mul, hPh.eq, hg.eq, Matrix.mul_assoc]

/-- There is a unitary `U` diagonalising both `P = 1 - B` (eigenvalues `p_j ∈ {0, 1}`) and the
compression `P g P` (eigenvalues `d_j`, with `d_j = 0` when `p_j = 0`).  So
`spec(PgP|ran P) = {d_j : p_j = 1}`.  (Eigenbasis of `PgP + c B` for a real `c` that is not an
eigenvalue of `PgP`.) -/
theorem exists_compression_basis (hB : B.IsHermitian ∧ B * B = B) (hg : g.IsHermitian) :
    ∃ (U : Matrix (Fin M) (Fin M) ℂ) (d p : Fin M → ℝ), U ∈ unitaryGroup (Fin M) ℂ ∧
      (∀ j, p j = 0 ∨ p j = 1) ∧ (∀ j, p j = 0 → d j = 0) ∧
      1 - B = U * diagonal (fun j => (p j : ℂ)) * star U ∧
      (1 - B) * g * (1 - B) = U * diagonal (fun j => (d j : ℂ)) * star U := by
  obtain ⟨hPh, hPP, hBP, hPB⟩ := proj_compl_facts hB
  have hQh := isHermitian_compress hB hg
  set P := 1 - B with hPdef
  set Q := P * g * P with hQdef
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset (Finset.univ.image hQh.eigenvalues)
  have hcQ : ∀ w : Fin M → ℂ, Q *ᵥ w = (c : ℂ) • w → w = 0 := by
    intro w hw
    by_contra hw0
    have hdet : (Matrix.scalar (Fin M) (c : ℂ) - Q).det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      refine ⟨w, hw0, ?_⟩
      rw [Matrix.sub_mulVec, hw]
      simp [Matrix.scalar_apply]
    have hroot : (c : ℂ) ∈ Q.charpoly.roots := by
      rw [Polynomial.mem_roots Q.charpoly_monic.ne_zero, Polynomial.IsRoot.def,
        Matrix.eval_charpoly]
      exact hdet
    rw [hQh.roots_charpoly_eq_eigenvalues, Multiset.mem_map] at hroot
    obtain ⟨i, _, hi⟩ := hroot
    apply hc
    rw [Finset.mem_image]
    refine ⟨i, Finset.mem_univ _, ?_⟩
    have hi' : ((hQh.eigenvalues i : ℝ) : ℂ) = (c : ℂ) := hi
    exact_mod_cast hi'
  set H := Q + (c : ℂ) • B with hHdef
  have hHh : H.IsHermitian := by
    refine hQh.add ?_
    unfold IsHermitian
    rw [conjTranspose_smul, hB.1.eq, Complex.star_def, Complex.conj_ofReal]
  set U : Matrix (Fin M) (Fin M) ℂ := (hHh.eigenvectorUnitary : Matrix (Fin M) (Fin M) ℂ) with hUdef
  have hU : U ∈ unitaryGroup (Fin M) ℂ := hHh.eigenvectorUnitary.2
  set η := hHh.eigenvalues with hη
  set u : Fin M → Fin M → ℂ := fun j => (hHh.eigenvectorBasis j).ofLp with hu
  have hUu : ∀ i j, U i j = u j i := fun i j => hHh.eigenvectorUnitary_apply i j
  have hHu : ∀ j, H *ᵥ u j = (η j : ℂ) • u j := by
    intro j
    have := hHh.mulVec_eigenvectorBasis j
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)] at this
    exact this
  have hBH : B * H = (c : ℂ) • B := by
    rw [hHdef, hQdef, mul_add, Matrix.mul_smul, hB.2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hBP]
    simp
  have hPH : P * H = Q := by
    rw [hHdef, hQdef, mul_add, Matrix.mul_smul, hPB, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP]
    simp
  have hQP : Q * P = Q := by rw [hQdef, Matrix.mul_assoc, hPP]
  set p : Fin M → ℝ := fun j => if η j = c then 0 else 1 with hp
  set d : Fin M → ℝ := fun j => if η j = c then 0 else η j with hd
  have hvec : ∀ j, P *ᵥ u j = (p j : ℂ) • u j ∧ Q *ᵥ u j = (d j : ℂ) • u j := by
    intro j
    have e1 : (c : ℂ) • (B *ᵥ u j) = (η j : ℂ) • (B *ᵥ u j) := by
      have := congrArg (B *ᵥ ·) (hHu j)
      simp only [Matrix.mulVec_mulVec, hBH, Matrix.mulVec_smul, Matrix.smul_mulVec] at this
      exact this
    have e2 : Q *ᵥ u j = (η j : ℂ) • (P *ᵥ u j) := by
      have := congrArg (P *ᵥ ·) (hHu j)
      simp only [Matrix.mulVec_mulVec, hPH, Matrix.mulVec_smul] at this
      exact this
    have e3 : Q *ᵥ u j = Q *ᵥ (P *ᵥ u j) := by rw [Matrix.mulVec_mulVec, hQP]
    by_cases hj : η j = c
    · have hPu : P *ᵥ u j = 0 := by
        apply hcQ
        rw [← e3, e2, hj]
      have hp0 : p j = 0 := by simp [hp, hj]
      have hd0 : d j = 0 := by simp [hd, hj]
      rw [hp0, hd0]
      simp only [Complex.ofReal_zero, zero_smul]
      exact ⟨hPu, by rw [e3, hPu, Matrix.mulVec_zero]⟩
    · have hBu : B *ᵥ u j = 0 := by
        have h0 : ((η j : ℂ) - c) • (B *ᵥ u j) = 0 := by rw [sub_smul, ← e1, sub_self]
        have hne : (η j : ℂ) - c ≠ 0 := by
          rw [sub_ne_zero]; exact_mod_cast hj
        exact (smul_eq_zero.mp h0).resolve_left hne
      have hPu : P *ᵥ u j = u j := by
        rw [hPdef, Matrix.sub_mulVec, Matrix.one_mulVec, hBu, sub_zero]
      have hp1 : p j = 1 := by simp [hp, hj]
      have hd1 : d j = η j := by simp [hd, hj]
      rw [hp1, hd1]
      simp only [Complex.ofReal_one, one_smul]
      exact ⟨hPu, by rw [e2, hPu]⟩
  have hcol : ∀ (A : Matrix (Fin M) (Fin M) ℂ) (w : Fin M → ℝ),
      (∀ j, A *ᵥ u j = (w j : ℂ) • u j) → A * U = U * diagonal (fun j => (w j : ℂ)) := by
    intro A w hA
    ext i j
    rw [Matrix.mul_diagonal, Matrix.mul_apply, hUu i j]
    have := congrFun (hA j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    simp_rw [hUu]
    rw [this, mul_comm]
  have hUU : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hconj : ∀ (A : Matrix (Fin M) (Fin M) ℂ) (w : Fin M → ℝ),
      A * U = U * diagonal (fun j => (w j : ℂ)) → A = U * diagonal (fun j => (w j : ℂ)) * star U := by
    intro A w hA
    calc A = A * (U * star U) := by rw [hUU, Matrix.mul_one]
      _ = U * diagonal (fun j => (w j : ℂ)) * star U := by rw [← Matrix.mul_assoc, hA]
  refine ⟨U, d, p, hU, ?_, ?_, ?_, ?_⟩
  · intro j; simp only [hp]; split_ifs <;> simp
  · intro j hj
    simp only [hp, hd] at hj ⊢
    split_ifs with h
    · rfl
    · rw [if_neg h] at hj; norm_num at hj
  · exact hconj P p (hcol P p (fun j => (hvec j).1))
  · exact hconj Q d (hcol Q d (fun j => (hvec j).2))

lemma trace_conj_unitary {U : Matrix (Fin M) (Fin M) ℂ} (hU : U ∈ unitaryGroup (Fin M) ℂ)
    (A : Matrix (Fin M) (Fin M) ℂ) : (U * A * star U).trace = A.trace := by
  rw [Matrix.trace_mul_cycle, Matrix.mem_unitaryGroup_iff'.mp hU, Matrix.one_mul]

/-- `Tr(P e^{a PgP}) = Σ_j p_j e^{a d_j}`; for `p_j ∈ {0,1}` this is `Tr_P e^{a PgP}`. -/
lemma trace_mul_exp_of_diag {P Q U : Matrix (Fin M) (Fin M) ℂ} {d p : Fin M → ℝ}
    (hU : U ∈ unitaryGroup (Fin M) ℂ) (hP : P = U * diagonal (fun j => (p j : ℂ)) * star U)
    (hQ : Q = U * diagonal (fun j => (d j : ℂ)) * star U) (a : ℂ) :
    (P * NormedSpace.exp (a • Q)).trace = ∑ j, (p j : ℂ) * cexp (a * d j) := by
  have hUU' : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hinv : U⁻¹ = star U := Matrix.inv_eq_left_inv hUU'
  have hunit : IsUnit U := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact Matrix.isUnit_det_of_left_inverse hUU'
  have hexp : NormedSpace.exp (a • Q) = U * diagonal (fun j => cexp (a * d j)) * star U := by
    have h1 : a • Q = U * diagonal (fun j => a * (d j : ℂ)) * U⁻¹ := by
      rw [hQ, hinv]
      have : diagonal (fun j => a * (d j : ℂ)) = a • diagonal (fun j => (d j : ℂ)) := by
        rw [← Matrix.diagonal_smul]; rfl
      rw [this, Matrix.mul_smul, Matrix.smul_mul]
    rw [h1, Matrix.exp_conj _ _ hunit, Matrix.exp_diagonal, Pi.exp_def, hinv]
    simp_rw [← Complex.exp_eq_exp_ℂ]
  rw [hexp, hP]
  have : U * diagonal (fun j => (p j : ℂ)) * star U * (U * diagonal (fun j => cexp (a * d j)) * star U)
      = U * diagonal (fun j => (p j : ℂ) * cexp (a * d j)) * star U := by
    rw [← diagonal_mul_diagonal]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star U) U, hUU', Matrix.one_mul]
  rw [this, trace_conj_unitary hU, trace_diagonal]

lemma roots_charpoly_conj_diagonal {U : Matrix (Fin M) (Fin M) ℂ} (hU : U ∈ unitaryGroup (Fin M) ℂ)
    (w : Fin M → ℂ) :
    (U * diagonal w * star U).charpoly.roots = Finset.univ.val.map w := by
  have hUU' : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hmap : Multiset.map (fun i => Polynomial.X - Polynomial.C (w i)) Finset.univ.val
      = (Finset.univ.val.map w).map (fun a => Polynomial.X - Polynomial.C a) := by
    rw [Multiset.map_map]; rfl
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hUU', Matrix.one_mul, charpoly_diagonal,
    Finset.prod_eq_multiset_prod, hmap, Polynomial.roots_multiset_prod_X_sub_C]

/-- `Tr[(P(g - λ)P)_+] = Σ_j p_j (d_j - λ)_+`, i.e. `Σ_{μ ∈ spec(PgP|ran P)} (μ - λ)_+`. -/
theorem posPartTrace_compress_eq (hB : B.IsHermitian ∧ B * B = B) (hg : g.IsHermitian)
    {U : Matrix (Fin M) (Fin M) ℂ} {d p : Fin M → ℝ} (hU : U ∈ unitaryGroup (Fin M) ℂ)
    (hp01 : ∀ j, p j = 0 ∨ p j = 1) (hpd : ∀ j, p j = 0 → d j = 0)
    (hP : 1 - B = U * diagonal (fun j => (p j : ℂ)) * star U)
    (hQ : (1 - B) * g * (1 - B) = U * diagonal (fun j => (d j : ℂ)) * star U) (lam : ℝ) :
    posPartTrace ((1 - B) * (g - (lam : ℂ) • 1) * (1 - B)) = ∑ j, p j * max (d j - lam) 0 := by
  obtain ⟨hPh, hPP, -, -⟩ := proj_compl_facts hB
  set A := (1 - B) * (g - (lam : ℂ) • 1) * (1 - B) with hAdef
  have hA1 : A = (1 - B) * g * (1 - B) - (lam : ℂ) • (1 - B) := by
    have h0 : (1 - B) * (g - (lam : ℂ) • 1) = (1 - B) * g - (lam : ℂ) • (1 - B) := by
      rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
    rw [hAdef, h0, Matrix.sub_mul, Matrix.smul_mul, hPP]
  have hA2 : A = U * diagonal (fun j => ((d j - lam * p j : ℝ) : ℂ)) * star U := by
    rw [hA1, hQ, hP]
    have : diagonal (fun j => ((d j - lam * p j : ℝ) : ℂ))
        = diagonal (fun j => (d j : ℂ)) - (lam : ℂ) • diagonal (fun j => (p j : ℂ)) := by
      rw [← Matrix.diagonal_smul, Matrix.diagonal_sub]
      congr 1; funext j; simp only [Pi.smul_apply, smul_eq_mul]; push_cast; ring
    rw [this, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hAh : A.IsHermitian := by
    rw [hA1]
    refine (isHermitian_compress hB hg).sub ?_
    unfold IsHermitian
    rw [conjTranspose_smul, hPh.eq, Complex.star_def, Complex.conj_ofReal]
  unfold posPartTrace
  rw [dif_pos hAh]
  have hroots := hAh.roots_charpoly_eq_eigenvalues
  have hroots2 : A.charpoly.roots = Finset.univ.val.map (fun j => ((d j - lam * p j : ℝ) : ℂ)) := by
    rw [hA2]; exact roots_charpoly_conj_diagonal hU _
  rw [hroots2] at hroots
  have hsum := congrArg (fun s : Multiset ℂ => (s.map (fun z => max z.re 0)).sum) hroots
  simp only [Multiset.map_map, Function.comp_def, Complex.ofReal_re] at hsum
  have hre : ∀ x : ℝ, (RCLike.ofReal x : ℂ).re = x := fun x => RCLike.ofReal_re (K := ℂ) x
  simp only [hre] at hsum
  have e1 : ∑ i, max (hAh.eigenvalues i) 0
      = (Finset.univ.val.map (fun i => max (hAh.eigenvalues i) 0)).sum := rfl
  rw [e1, ← hsum]
  change (Finset.univ.val.map (fun j => max (d j - lam * p j) 0)).sum = _
  rw [← Finset.sum_eq_multiset_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rcases hp01 j with h | h
  · rw [hpd j h, h]; simp
  · rw [h]; simp

end Compression

/-! ### Mass and first moment -/

lemma multiset_map_re_sum (S : Multiset ℂ) : (S.map Complex.re).sum = S.sum.re := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih => simp [ih]

lemma multiset_map_im_sum (S : Multiset ℂ) : (S.map Complex.im).sum = S.sum.im := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih => simp [ih]

lemma multiset_map_re_mul_im (S : Multiset ℂ) :
    (S.map (fun ν => ν.re * ν.im)).sum = (S.map (fun ν => ν ^ 2)).sum.im / 2 := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Complex.add_im, ih, pow_two, Complex.mul_im]
    ring

/-- **Equal mass and first moment** of `ρ = Σ_ν ω_ν` (ν over the eigenvalues of `B + ig`) and
`σ = Σ_j p_j δ_{d_j}`: `Σ_ν (1 - Re ν) = Σ_j p_j` and `Σ_ν (1 - Re ν) Im ν = Σ_j p_j d_j`
(from `Tr X = Σ ν` and `Tr X² = Σ ν²`). -/
theorem mass_moment_eq {B g : Matrix (Fin M) (Fin M) ℂ} (hB : B.IsHermitian ∧ B * B = B)
    (hg : g.IsHermitian) {U : Matrix (Fin M) (Fin M) ℂ} {d p : Fin M → ℝ}
    (hU : U ∈ unitaryGroup (Fin M) ℂ) (hpd : ∀ j, p j = 0 → d j = 0)
    (hp01 : ∀ j, p j = 0 ∨ p j = 1)
    (hP : 1 - B = U * diagonal (fun j => (p j : ℂ)) * star U)
    (hQ : (1 - B) * g * (1 - B) = U * diagonal (fun j => (d j : ℂ)) * star U) :
    ((B + I • g).charpoly.roots.map (fun ν => 1 - ν.re)).sum = ∑ j, p j ∧
    ((B + I • g).charpoly.roots.map (fun ν => (1 - ν.re) * ν.im)).sum = ∑ j, p j * d j := by
  obtain ⟨hPh, hPP, hBP, hPB⟩ := proj_compl_facts hB
  set X := B + I • g with hX
  set S := X.charpoly.roots with hS
  have h1 : S.sum = X.trace := (Matrix.trace_eq_sum_roots_charpoly X).symm
  have h2 : (S.map (fun ν => ν ^ 2)).sum = (X ^ 2).trace := (trace_pow_eq_sum_roots X 2).symm
  have hcard : S.card = M := card_roots_charpoly X
  have hBim : B.trace.im = 0 := trace_im_eq_zero hB.1
  have hgim : g.trace.im = 0 := trace_im_eq_zero hg
  have hggim : (g * g).trace.im = 0 := by
    refine trace_im_eq_zero ?_
    unfold IsHermitian; rw [conjTranspose_mul, hg.eq]
  have htrP : (1 - B).trace = ∑ j, (p j : ℂ) := by rw [hP, trace_conj_unitary hU, trace_diagonal]
  have htrQ : ((1 - B) * g * (1 - B)).trace = ∑ j, (d j : ℂ) := by
    rw [hQ, trace_conj_unitary hU, trace_diagonal]
  have hdp : ∀ j, d j = p j * d j := by
    intro j; rcases hp01 j with h | h
    · rw [hpd j h, h]; ring
    · rw [h]; ring
  have htrX : X.trace = B.trace + I * g.trace := by rw [hX, trace_add, trace_smul, smul_eq_mul]
  have hX2 : X ^ 2 = B + I • (B * g + g * B) - g * g := by
    rw [hX, pow_two, add_mul, mul_add, mul_add, hB.2, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, I_mul_I, neg_one_smul, smul_add]
    abel
  have htrX2 : (X ^ 2).trace = B.trace + 2 * I * (B * g).trace - (g * g).trace := by
    rw [hX2, trace_sub, trace_add, trace_smul, trace_add, Matrix.trace_mul_comm g B, smul_eq_mul]
    ring
  have htrPg : ((1 - B) * g * (1 - B)).trace = g.trace - (B * g).trace := by
    rw [Matrix.trace_mul_cycle, hPP, sub_mul, Matrix.one_mul, trace_sub]
  constructor
  · -- mass
    have e : (S.map (fun ν => 1 - ν.re)).sum = S.card - (S.map Complex.re).sum := by
      rw [Multiset.sum_map_sub]; simp
    rw [e, hcard, multiset_map_re_sum, h1, htrX]
    have hre := congrArg Complex.re htrP
    rw [trace_sub, trace_one, Fintype.card_fin, Complex.sub_re, Complex.natCast_re] at hre
    rw [show (∑ j, p j) = (∑ j, (p j : ℂ)).re by simp, ← hre]
    simp [hgim]
  · -- first moment
    have e : (S.map (fun ν => (1 - ν.re) * ν.im)).sum
        = (S.map Complex.im).sum - (S.map (fun ν => ν.re * ν.im)).sum := by
      rw [← Multiset.sum_map_sub]; congr 1; apply Multiset.map_congr rfl; intro ν _; ring
    rw [e, multiset_map_im_sum, multiset_map_re_mul_im, h1, h2, htrX, htrX2]
    have hre := congrArg Complex.re htrQ
    rw [htrPg, Complex.sub_re] at hre
    rw [show (∑ j, p j * d j) = ∑ j, d j from (Finset.sum_congr rfl (fun j _ => (hdp j).symm)),
      show (∑ j, d j) = (∑ j, (d j : ℂ)).re by simp, ← hre]
    simp [hBim, hgim, hggim]



/-! ### The function `D(a, t)` -/

/-- `D(a, t) = Tr e^{a g - t P} - e^{-t} Tr_P e^{a PgP} - Tr_B e^{a BgB}` (`P = 1 - B`), as in
section 0 of the paper.  Here `Tr_P e^{a PgP}` is written `Tr(P e^{a PgP})`: since `PgP` vanishes
on `ran B`, `e^{a PgP}` is the identity there, and `Tr(P e^{a PgP})` is the trace over `ran P` of
the exponential of the compression `PgP|_{ran P}`; likewise for `B`. -/
noncomputable def stripD (B g : Matrix (Fin M) (Fin M) ℂ) (a t : ℂ) : ℂ :=
  (NormedSpace.exp (a • g - t • (1 - B))).trace
    - cexp (-t) * ((1 - B) * NormedSpace.exp (a • ((1 - B) * g * (1 - B)))).trace
    - (B * NormedSpace.exp (a • (B * g * B))).trace

/-! ### Exponentials and eigen-relations -/

/-- If `W Q = μ Q` then `e^W Q = e^μ Q`. -/
lemma exp_mul_of_mul_eq_smul {W Q : Matrix (Fin M) (Fin M) ℂ} {μ : ℂ} (h : W * Q = μ • Q) :
    NormedSpace.exp W * Q = cexp μ • Q := by
  let _ : NormedRing (Matrix (Fin M) (Fin M) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix (Fin M) (Fin M) ℂ) := Matrix.linftyOpNormedAlgebra
  have hpow : ∀ n : ℕ, W ^ n * Q = μ ^ n • Q := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', Matrix.mul_assoc, ih, Matrix.mul_smul, h, smul_smul, pow_succ]
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) W).mul_right Q
  have h2 : HasSum (fun n : ℕ => (((n.factorial : ℂ))⁻¹ * μ ^ n) • Q) (cexp μ • Q) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) μ).smul_const Q
  refine h1.unique (h2.congr_fun fun n => ?_)
  rw [Matrix.smul_mul, hpow, smul_smul]

/-- If `Q W = μ Q` then `Q e^W = e^μ Q`. -/
lemma mul_exp_of_mul_eq_smul {W Q : Matrix (Fin M) (Fin M) ℂ} {μ : ℂ} (h : Q * W = μ • Q) :
    Q * NormedSpace.exp W = cexp μ • Q := by
  let _ : NormedRing (Matrix (Fin M) (Fin M) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix (Fin M) (Fin M) ℂ) := Matrix.linftyOpNormedAlgebra
  have hpow : ∀ n : ℕ, Q * W ^ n = μ ^ n • Q := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.smul_mul, h, smul_smul, pow_succ]
  have h1 := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) W).mul_left Q
  have h2 : HasSum (fun n : ℕ => (((n.factorial : ℂ))⁻¹ * μ ^ n) • Q) (cexp μ • Q) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) μ).smul_const Q
  refine h1.unique (h2.congr_fun fun n => ?_)
  rw [Matrix.mul_smul, hpow, smul_smul]

lemma exp_smul_one (c : ℂ) :
    NormedSpace.exp (c • (1 : Matrix (Fin M) (Fin M) ℂ)) = cexp c • 1 := by
  have h := exp_mul_of_mul_eq_smul (W := c • (1 : Matrix (Fin M) (Fin M) ℂ))
    (Q := (1 : Matrix (Fin M) (Fin M) ℂ)) (μ := c) (by rw [Matrix.mul_one])
  rwa [Matrix.mul_one] at h

lemma exp_add_smul_one (Y : Matrix (Fin M) (Fin M) ℂ) (c : ℂ) :
    NormedSpace.exp (Y + c • (1 : Matrix (Fin M) (Fin M) ℂ)) = cexp c • NormedSpace.exp Y := by
  let _ : NormedRing (Matrix (Fin M) (Fin M) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℚ (Matrix (Fin M) (Fin M) ℂ) := Matrix.linftyOpNormedAlgebra
  have hc : Commute Y (c • (1 : Matrix (Fin M) (Fin M) ℂ)) := (Commute.one_right Y).smul_right c
  rw [Matrix.exp_add_of_commute _ _ hc, exp_smul_one, Matrix.mul_smul, Matrix.mul_one]

lemma star_multiset_map_sum (S : Multiset ℂ) (f : ℂ → ℂ) :
    star (S.map f).sum = (S.map (fun ν => star (f ν))).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih => simp [ih]

/-- `Tr e^{iκ g - κ P} = Σ_ν e^{κ(ν - 1)}`, `ν` over the eigenvalues of `B + ig`. -/
lemma trace_exp_right (B g : Matrix (Fin M) (Fin M) ℂ) (κ : ℝ) :
    (NormedSpace.exp ((I * κ) • g - (κ : ℂ) • (1 - B))).trace
      = ((B + I • g).charpoly.roots.map (fun ν => cexp (κ * (ν - 1)))).sum := by
  have e : (I * κ) • g - (κ : ℂ) • (1 - B) = (κ : ℂ) • (B + I • g) + (-(κ : ℂ)) • 1 := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [e, exp_add_smul_one, trace_smul, trace_exp_smul_eq_sum_roots, smul_eq_mul,
    ← Multiset.sum_map_mul_left]
  congr 1
  refine Multiset.map_congr rfl (fun ν _ => ?_)
  rw [← Complex.exp_add]; ring_nf

/-- `Tr e^{iκ g + κ P} = Σ_ν e^{κ(1 - ν̄)}`, `ν` over the eigenvalues of `B + ig`. -/
lemma trace_exp_left {B g : Matrix (Fin M) (Fin M) ℂ} (hB : B.IsHermitian) (hg : g.IsHermitian)
    (κ : ℝ) :
    (NormedSpace.exp ((I * κ) • g - (-(κ : ℂ)) • (1 - B))).trace
      = ((B + I • g).charpoly.roots.map (fun ν => cexp (κ * (1 - star ν)))).sum := by
  have hstar : ((-(κ : ℂ)) • (B + I • g))ᴴ = (-(κ : ℂ)) • (B - I • g) := by
    rw [conjTranspose_smul, conjTranspose_add, conjTranspose_smul, hB.eq, hg.eq]
    simp [Complex.conj_ofReal, sub_eq_add_neg]
  have e : (I * κ) • g - (-(κ : ℂ)) • (1 - B) = ((-(κ : ℂ)) • (B + I • g))ᴴ + (κ : ℂ) • 1 := by
    rw [hstar]
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [e, exp_add_smul_one, trace_smul, Matrix.exp_conjTranspose, trace_conjTranspose,
    trace_exp_smul_eq_sum_roots, star_multiset_map_sum, smul_eq_mul, ← Multiset.sum_map_mul_left]
  congr 1
  refine Multiset.map_congr rfl (fun ν _ => ?_)
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  simp only [map_mul, map_neg, Complex.conj_ofReal]
  ring_nf

lemma star_eq_re_sub_im (ν : ℂ) : star ν = (ν.re : ℂ) - ν.im * I := by
  rw [Complex.star_def]
  apply Complex.ext <;> simp

/-- The matrix side of step (a) of the proof of Theorem 2:
`D(iκ, -κ) - D(iκ, κ) = Σ_ν e^{iκ Im ν} 2 sinh(κ(1 - Re ν)) - 2 sinh κ · Σ_j p_j e^{iκ d_j}`. -/
theorem stripD_sub_eq {B g : Matrix (Fin M) (Fin M) ℂ} (hB : B.IsHermitian ∧ B * B = B)
    (hg : g.IsHermitian) {U : Matrix (Fin M) (Fin M) ℂ} {d p : Fin M → ℝ}
    (hU : U ∈ unitaryGroup (Fin M) ℂ) (hP : 1 - B = U * diagonal (fun j => (p j : ℂ)) * star U)
    (hQ : (1 - B) * g * (1 - B) = U * diagonal (fun j => (d j : ℂ)) * star U) (κ : ℝ) :
    stripD B g (I * κ) (-(κ : ℂ)) - stripD B g (I * κ) κ
      = ((B + I • g).charpoly.roots.map
          (fun ν => cexp (I * κ * ν.im) * (2 * (Real.sinh (κ * (1 - ν.re)) : ℂ)))).sum
        - 2 * (Real.sinh κ : ℂ) * ∑ j, (p j : ℂ) * cexp (I * κ * d j) := by
  unfold stripD
  rw [trace_exp_left hB.1 hg κ, trace_exp_right B g κ,
    trace_mul_exp_of_diag hU hP hQ (I * κ)]
  have hsinh : ∀ x : ℝ, (2 * (Real.sinh x : ℂ)) = cexp x - cexp (-x) := by
    intro x
    rw [Complex.ofReal_sinh, Complex.sinh]
    ring
  have hterm : ∀ ν : ℂ, cexp (κ * (1 - star ν)) - cexp (κ * (ν - 1))
      = cexp (I * κ * ν.im) * (2 * (Real.sinh (κ * (1 - ν.re)) : ℂ)) := by
    intro ν
    rw [hsinh, mul_sub (cexp (I * κ * ν.im)), ← Complex.exp_add, ← Complex.exp_add]
    have e1 : (κ : ℂ) * (1 - star ν) = I * κ * ν.im + ((κ * (1 - ν.re) : ℝ) : ℂ) := by
      rw [star_eq_re_sub_im]; push_cast; ring
    have e2 : (κ : ℂ) * (ν - 1) = I * κ * ν.im + -((κ * (1 - ν.re) : ℝ) : ℂ) := by
      conv_lhs => rw [← Complex.re_add_im ν]
      push_cast; ring
    rw [e1, e2]
  have hmap : (B + I • g).charpoly.roots.map
      (fun ν => cexp (κ * (1 - star ν)) - cexp (κ * (ν - 1)))
      = (B + I • g).charpoly.roots.map
          (fun ν => cexp (I * κ * ν.im) * (2 * (Real.sinh (κ * (1 - ν.re)) : ℂ))) :=
    Multiset.map_congr rfl (fun ν _ => hterm ν)
  rw [← hmap, Multiset.sum_map_sub, hsinh κ, neg_neg]
  ring

/-! ### The two-term form of `D` (pinching) -/

/-- `D(a, t) = Tr e^{a g - t P} - Tr e^{a g_d - t P}` with the pinching `g_d = BgB + PgP`
(the form `bmvD` used in module L3b, `OQP27/StripBMV.lean`). -/
theorem stripD_eq_sub_pinch {B g : Matrix (Fin M) (Fin M) ℂ} (hB : B.IsHermitian ∧ B * B = B)
    (a t : ℂ) :
    stripD B g a t = (NormedSpace.exp (a • g - t • (1 - B))).trace
      - (NormedSpace.exp (a • (B * g * B + (1 - B) * g * (1 - B)) - t • (1 - B))).trace := by
  obtain ⟨-, hPP, hBP, hPB⟩ := proj_compl_facts hB
  set P := 1 - B with hPdef
  set Y := a • (B * g * B) with hY
  set Z := a • (P * g * P) - t • P with hZ
  have hYP : Y * P = 0 := by
    rw [hY, Matrix.smul_mul, Matrix.mul_assoc, hBP, Matrix.mul_zero, smul_zero]
  have hBZ : B * Z = 0 := by
    rw [hZ, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, hBP, Matrix.zero_mul, Matrix.zero_mul, smul_zero, smul_zero, sub_zero]
  have hYZ : Y * Z = 0 := by
    have : B * g * B * (P * g * P) = (B * g) * (B * P) * g * P := by noncomm_ring
    rw [hY, hZ, Matrix.smul_mul, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, this,
      Matrix.mul_assoc (B * g) B P, hBP]
    simp
  have hZY : Z * Y = 0 := by
    have : P * g * P * (B * g * B) = (P * g) * (P * B) * g * B := by noncomm_ring
    have h' : P * (B * g * B) = (P * B) * g * B := by noncomm_ring
    rw [hY, hZ, Matrix.mul_smul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, this, h', hPB]
    simp
  have hcomm : Commute Y Z := by
    unfold Commute SemiconjBy; rw [hYZ, hZY]
  have hsplit : a • (B * g * B + P * g * P) - t • P = Y + Z := by
    rw [hY, hZ, smul_add]; abel
  -- e^{Y+Z} = e^Y B + P e^Z
  have hexp : NormedSpace.exp (Y + Z) = NormedSpace.exp Y * B + P * NormedSpace.exp Z := by
    let _ : NormedRing (Matrix (Fin M) (Fin M) ℂ) := Matrix.linftyOpNormedRing
    let _ : NormedAlgebra ℚ (Matrix (Fin M) (Fin M) ℂ) := Matrix.linftyOpNormedAlgebra
    have e1 : NormedSpace.exp Y * P = P := by
      have := exp_mul_of_mul_eq_smul (W := Y) (Q := P) (μ := 0) (by rw [hYP, zero_smul])
      rwa [Complex.exp_zero, one_smul] at this
    have e2 : B * NormedSpace.exp Z = B := by
      have := mul_exp_of_mul_eq_smul (W := Z) (Q := B) (μ := 0) (by rw [hBZ, zero_smul])
      rwa [Complex.exp_zero, one_smul] at this
    rw [Matrix.exp_add_of_commute _ _ hcomm]
    calc NormedSpace.exp Y * NormedSpace.exp Z
        = NormedSpace.exp Y * (B + P) * NormedSpace.exp Z := by
          rw [hPdef, add_sub_cancel, Matrix.mul_one]
      _ = NormedSpace.exp Y * (B * NormedSpace.exp Z)
            + NormedSpace.exp Y * P * NormedSpace.exp Z := by
          rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = NormedSpace.exp Y * B + P * NormedSpace.exp Z := by rw [e2, e1]
  -- Tr(P e^Z) = e^{-t} Tr(P e^{a PgP})
  have hPZ : (P * NormedSpace.exp Z).trace
      = cexp (-t) * (P * NormedSpace.exp (a • (P * g * P))).trace := by
    let _ : NormedRing (Matrix (Fin M) (Fin M) ℂ) := Matrix.linftyOpNormedRing
    let _ : NormedAlgebra ℚ (Matrix (Fin M) (Fin M) ℂ) := Matrix.linftyOpNormedAlgebra
    have hc0 : Commute (P * g * P) P := by
      unfold Commute SemiconjBy
      rw [Matrix.mul_assoc, hPP, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP]
    have hc : Commute (a • (P * g * P)) ((-t) • P) := (hc0.smul_left a).smul_right (-t)
    have hZ' : Z = a • (P * g * P) + (-t) • P := by rw [hZ, neg_smul, sub_eq_add_neg]
    have e3 : NormedSpace.exp ((-t) • P) * P = cexp (-t) • P := by
      refine exp_mul_of_mul_eq_smul ?_
      rw [Matrix.smul_mul, hPP]
    rw [hZ', Matrix.exp_add_of_commute _ _ hc, Matrix.trace_mul_comm, Matrix.mul_assoc, e3,
      Matrix.mul_smul, trace_smul, smul_eq_mul, Matrix.trace_mul_comm]
  rw [hsplit, hexp, trace_add, hPZ, Matrix.trace_mul_comm (NormedSpace.exp Y) B]
  unfold stripD
  ring

/-! ### The equality case: `D(·, 0) ≡ 0` iff `[B, g] = 0` -/

lemma compress_conj_eq_zero {B g : Matrix (Fin M) (Fin M) ℂ} (hB : B.IsHermitian ∧ B * B = B)
    (hg : g.IsHermitian) (h : B * g * (1 - B) = 0) : (1 - B) * g * B = 0 := by
  have := congrArg conjTranspose h
  rw [conjTranspose_mul, conjTranspose_mul, (isHermitian_one.sub hB.1).eq, hg.eq, hB.1.eq,
    conjTranspose_zero, ← Matrix.mul_assoc] at this
  exact this

lemma commute_iff_compress_eq_zero {B g : Matrix (Fin M) (Fin M) ℂ}
    (hB : B.IsHermitian ∧ B * B = B) (hg : g.IsHermitian) :
    Commute B g ↔ B * g * (1 - B) = 0 := by
  constructor
  · intro h
    have h' : B * g = g * B := h
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, ← h', ← Matrix.mul_assoc, hB.2, sub_self]
  · intro h
    have h1 : B * g = B * g * B := by
      rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h; exact h
    have h2 := compress_conj_eq_zero hB hg h
    have h3 : g * B = B * g * B := by
      rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h2; exact h2
    show B * g = g * B
    rw [h1, h3]

/-- If `[B, g] = 0` then `D(a, 0) = 0` for every `a`. -/
theorem stripD_zero_of_commute {B g : Matrix (Fin M) (Fin M) ℂ} (hB : B.IsHermitian ∧ B * B = B)
    (hg : g.IsHermitian) (hc : Commute B g) (a : ℂ) : stripD B g a 0 = 0 := by
  have h0 := (commute_iff_compress_eq_zero hB hg).mp hc
  have hPgB := compress_conj_eq_zero hB hg h0
  have hg_split : g = B * g * B + (1 - B) * g * (1 - B) := by
    have e1 : B * g = B * g * B := by
      rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h0; exact h0
    have e2 : (1 - B) * g = (1 - B) * g * (1 - B) := by
      rw [Matrix.mul_sub, Matrix.mul_one, hPgB, sub_zero]
    calc g = B * g + (1 - B) * g := by rw [← Matrix.add_mul, add_sub_cancel, Matrix.one_mul]
      _ = _ := by rw [← e1, ← e2]
  rw [stripD_eq_sub_pinch hB a 0, ← hg_split, sub_self]

/-- The trace identity behind the second derivative of `a ↦ D(a, 0)` at `0`:
`Tr g² - Tr(P(PgP)²) - Tr(B(BgB)²) = 2 Tr((BgP)(BgP)ᴴ)`. -/
lemma trace_second_derivative {B g : Matrix (Fin M) (Fin M) ℂ} (hB : B.IsHermitian ∧ B * B = B)
    (hg : g.IsHermitian) :
    (g * g).trace - ((1 - B) * ((1 - B) * g * (1 - B) * ((1 - B) * g * (1 - B)))).trace
      - (B * (B * g * B * (B * g * B))).trace
      = 2 * ((B * g * (1 - B)) * (B * g * (1 - B))ᴴ).trace := by
  obtain ⟨hPh, hPP, -, -⟩ := proj_compl_facts hB
  set P := 1 - B with hPdef
  -- cyclic reductions
  have cyc : ∀ Q : Matrix (Fin M) (Fin M) ℂ, Q * Q = Q →
      (Q * (Q * g * Q * (Q * g * Q))).trace = (g * Q * g * Q).trace := by
    intro Q hQ
    have e : Q * (Q * g * Q * (Q * g * Q)) = (Q * Q) * g * (Q * Q) * g * Q := by noncomm_ring
    rw [e, hQ, Matrix.trace_mul_cycle (Q * g * Q) g Q]
    have e2 : Q * (Q * g * Q) * g = (Q * Q) * (g * Q * g) := by noncomm_ring
    rw [e2, hQ, Matrix.trace_mul_comm]
  have hPg : (g * P * g * P).trace = (g * g).trace - 2 * (g * g * B).trace + (g * B * g * B).trace := by
    have e : g * P * g * P = g * g - g * g * B - g * B * g + g * B * g * B := by
      rw [hPdef]; noncomm_ring
    have e2 : (g * B * g).trace = (g * g * B).trace := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
    rw [e, trace_add, trace_sub, trace_sub, e2]
    ring
  have hconj : (B * g * P) * (B * g * P)ᴴ = B * g * g * B - B * g * B * g * B := by
    rw [conjTranspose_mul, conjTranspose_mul, hPh.eq, hg.eq, hB.1.eq]
    have e : B * g * P * (P * (g * B)) = B * g * (P * P) * g * B := by noncomm_ring
    rw [e, hPP, hPdef]
    noncomm_ring
  have t1 : (B * g * g * B).trace = (g * g * B).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hB.2, Matrix.mul_assoc,
      Matrix.trace_mul_comm, Matrix.mul_assoc]
  have t2 : (B * g * B * g * B).trace = (g * B * g * B).trace := by
    have := cyc B hB.2
    have e : B * (B * g * B * (B * g * B)) = B * g * B * g * B := by
      have e' : B * (B * g * B * (B * g * B)) = (B * B) * g * (B * B) * g * B := by noncomm_ring
      rw [e', hB.2]
    rw [← e, this]
  rw [cyc P hPP, cyc B hB.2, hPg, hconj, trace_sub, t1, t2]
  ring

/-- If `D(a, 0) = 0` for all `a`, then `[B, g] = 0` (the second derivative of `a ↦ D(a, 0)` at `0`
is `2 ‖BgP‖_F²`). -/
theorem commute_of_stripD_zero {B g : Matrix (Fin M) (Fin M) ℂ} (hB : B.IsHermitian ∧ B * B = B)
    (hg : g.IsHermitian) (hD : ∀ a : ℂ, stripD B g a 0 = 0) : Commute B g := by
  rw [commute_iff_compress_eq_zero hB hg]
  set P := 1 - B with hPdef
  let _ : NormedRing (Matrix (Fin M) (Fin M) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix (Fin M) (Fin M) ℂ) := Matrix.linftyOpNormedAlgebra
  let L : Matrix (Fin M) (Fin M) ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin M) ℂ ℂ)
  have hder : ∀ (Q Y : Matrix (Fin M) (Fin M) ℂ) (a : ℂ),
      HasDerivAt (fun a : ℂ => (Q * NormedSpace.exp (a • Y)).trace)
        ((Q * (NormedSpace.exp (a • Y) * Y)).trace) a := by
    intro Q Y a
    have h1 := (hasDerivAt_exp_smul_const (𝕂 := ℂ) Y a).const_mul Q
    have h2 := L.hasFDerivAt.comp_hasDerivAt a h1
    exact h2
  have hder' : ∀ (Q Y : Matrix (Fin M) (Fin M) ℂ) (a : ℂ),
      HasDerivAt (fun a : ℂ => (Q * (NormedSpace.exp (a • Y) * Y)).trace)
        ((Q * ((NormedSpace.exp (a • Y) * Y) * Y)).trace) a := by
    intro Q Y a
    have h1 := ((hasDerivAt_exp_smul_const (𝕂 := ℂ) Y a).mul_const Y).const_mul Q
    have h2 := L.hasFDerivAt.comp_hasDerivAt a h1
    exact h2
  have hf : (fun a : ℂ => stripD B g a 0) = fun a => (1 * NormedSpace.exp (a • g)).trace
      - (P * NormedSpace.exp (a • (P * g * P))).trace
      - (B * NormedSpace.exp (a • (B * g * B))).trace := by
    funext a
    simp [stripD, hPdef]
  set f1 : ℂ → ℂ := fun a => (1 * (NormedSpace.exp (a • g) * g)).trace
      - (P * (NormedSpace.exp (a • (P * g * P)) * (P * g * P))).trace
      - (B * (NormedSpace.exp (a • (B * g * B)) * (B * g * B))).trace with hf1
  have hf1z : ∀ a, f1 a = 0 := by
    intro a
    have h1 : HasDerivAt (fun a => stripD B g a 0) (f1 a) a := by
      rw [hf]
      exact ((hder 1 g a).sub (hder P (P * g * P) a)).sub (hder B (B * g * B) a)
    have h2 : HasDerivAt (fun a => stripD B g a 0) 0 a := by
      have : (fun a => stripD B g a 0) = fun _ => (0 : ℂ) := funext hD
      rw [this]; exact hasDerivAt_const a 0
    exact h1.unique h2
  have h3 : HasDerivAt f1 ((1 * ((NormedSpace.exp ((0 : ℂ) • g) * g) * g)).trace
      - (P * ((NormedSpace.exp ((0 : ℂ) • (P * g * P)) * (P * g * P)) * (P * g * P))).trace
      - (B * ((NormedSpace.exp ((0 : ℂ) • (B * g * B)) * (B * g * B)) * (B * g * B))).trace) 0 :=
    ((hder' 1 g 0).sub (hder' P (P * g * P) 0)).sub (hder' B (B * g * B) 0)
  have h4 : HasDerivAt f1 0 0 := by
    have : f1 = fun _ => (0 : ℂ) := funext hf1z
    rw [this]; exact hasDerivAt_const 0 0
  have key := h3.unique h4
  simp only [zero_smul, NormedSpace.exp_zero, Matrix.one_mul] at key
  have key2 := trace_second_derivative hB hg
  rw [← hPdef] at key2
  rw [key] at key2
  have h0 : ((B * g * P) * (B * g * P)ᴴ).trace = 0 := by
    have : (2 : ℂ) * ((B * g * P) * (B * g * P)ᴴ).trace = 0 := key2.symm
    simpa using this
  exact Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp h0

end OQP27.StripL3a
