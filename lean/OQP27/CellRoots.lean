/-
OQP27/CellRoots.lean  (module L5, layer 2a: eigenvalues of matrix families)

What is proved here (complete proofs):
* `mem_roots_eigvec`        a root of `charpoly X` is an eigenvalue (it has an eigenvector);
* `norm_le_mnorm`           every root `ν` of `charpoly X` satisfies `‖ν‖ ≤ ∑ i j, ‖X i j‖`;
* `card_roots_charpoly`, `charpoly_eq_prod_roots`   over `ℂ`, `charpoly X = ∏ (X - ν)` over the
                            multiset of its `M` roots;
* `tendsto_sum_roots`       continuity of `X ↦ ∑_{ν ∈ spec X} f ν` along convergent sequences, for
                            `f` continuous on a closed set containing all spectra (compactness proof);
* `eventually_roots_near`   upper semicontinuity of the spectrum: near `z₀` every root of
                            `charpoly (X z)` is `ε`-close to a root of `charpoly (X z₀)`;
* `differentiableOn_charpoly_coeff`   the coefficients of `charpoly (X z)` are holomorphic in `z`
                            when the entries of `X z` are;
* `eval_derivative_prod_X_sub_C`      the logarithmic-derivative formula `p'/p = ∑ 1/(ζ - ν)`.
No hypotheses remain.  These are the eigenvalue facts used in Q_quantum/LOG.md s.4 (ii)-(iii) and
Q_rig/RIGIDITY_ALLD.md s.3.4-3.5 ("eigenvalues move continuously").
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false

namespace OQP27.Cell

open Polynomial Matrix Filter Topology

variable {M : ℕ}

/-- Entrywise `ℓ¹`-size of a matrix. -/
noncomputable def mnorm (X : Matrix (Fin M) (Fin M) ℂ) : ℝ := ∑ i, ∑ j, ‖X i j‖

lemma mnorm_nonneg (X : Matrix (Fin M) (Fin M) ℂ) : 0 ≤ mnorm X := by
  unfold mnorm; positivity

lemma continuous_mnorm : Continuous (mnorm : Matrix (Fin M) (Fin M) ℂ → ℝ) := by
  unfold mnorm
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact continuous_norm.comp ((continuous_apply j).comp (continuous_apply i))

lemma charpoly_ne_zero (X : Matrix (Fin M) (Fin M) ℂ) : X.charpoly ≠ 0 :=
  X.charpoly_monic.ne_zero

lemma card_roots_charpoly (X : Matrix (Fin M) (Fin M) ℂ) :
    Multiset.card X.charpoly.roots = M := by
  rw [(splits_iff_card_roots.1 (IsAlgClosed.splits X.charpoly)), charpoly_natDegree_eq_dim,
    Fintype.card_fin]

lemma charpoly_eq_prod_roots (X : Matrix (Fin M) (Fin M) ℂ) :
    X.charpoly = (X.charpoly.roots.map fun a => Polynomial.X - C a).prod :=
  (prod_multiset_X_sub_C_of_monic_of_roots_card_eq X.charpoly_monic
    (splits_iff_card_roots.1 (IsAlgClosed.splits X.charpoly))).symm

lemma eval_charpoly_eq_prod (X : Matrix (Fin M) (Fin M) ℂ) (ζ : ℂ) :
    X.charpoly.eval ζ = (X.charpoly.roots.map fun a => ζ - a).prod := by
  conv_lhs => rw [charpoly_eq_prod_roots X]
  rw [eval_multiset_prod, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro a _
  simp

/-- A root of the characteristic polynomial has an eigenvector. -/
lemma mem_roots_eigvec {X : Matrix (Fin M) (Fin M) ℂ} {ν : ℂ} (hν : ν ∈ X.charpoly.roots) :
    ∃ v : Fin M → ℂ, v ≠ 0 ∧ X *ᵥ v = ν • v := by
  have hroot : X.charpoly.eval ν = 0 := (mem_roots (charpoly_ne_zero X)).1 hν
  rw [eval_charpoly] at hroot
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hroot
  refine ⟨v, hv, ?_⟩
  rw [sub_mulVec] at hv0
  have hs : (Matrix.scalar (Fin M) ν) *ᵥ v = ν • v := by
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  rw [hs] at hv0
  exact (sub_eq_zero.1 hv0).symm

/-- Every eigenvalue is bounded by the entrywise `ℓ¹`-size. -/
lemma norm_le_mnorm {X : Matrix (Fin M) (Fin M) ℂ} {ν : ℂ} (hν : ν ∈ X.charpoly.roots) :
    ‖ν‖ ≤ mnorm X := by
  obtain ⟨v, hv, hXv⟩ := mem_roots_eigvec hν
  have hM : Nonempty (Fin M) := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hv (funext fun i => (h.false i).elim)
  obtain ⟨i, hi⟩ := Finite.exists_max fun j => ‖v j‖
  have hvi : 0 < ‖v i‖ := by
    by_contra h
    push Not at h
    apply hv
    funext j
    have := (hi j).trans h
    simpa using norm_le_zero_iff.1 this
  have h1 : ν * v i = ∑ j, X i j * v j := by
    have := congrFun hXv i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    exact this.symm
  have h2 : ‖ν‖ * ‖v i‖ ≤ (∑ j, ‖X i j‖) * ‖v i‖ := by
    rw [← norm_mul, h1, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hi j) (norm_nonneg _)
  have h3 : ‖ν‖ ≤ ∑ j, ‖X i j‖ := le_of_mul_le_mul_right h2 hvi
  refine h3.trans ?_
  unfold mnorm
  exact Finset.single_le_sum (f := fun i => ∑ j, ‖X i j‖) (fun k _ => by positivity)
    (Finset.mem_univ i)

/-- Any multiset of cardinality `M` is the image of an enumeration `Fin M → ℂ`. -/
lemma exists_enum (s : Multiset ℂ) (hs : Multiset.card s = M) :
    ∃ e : Fin M → ℂ, Multiset.map e Finset.univ.val = s := by
  have hl : s.toList.length = M := by simp [hs]
  refine ⟨fun i => s.toList.get (Fin.cast hl.symm i), ?_⟩
  rw [Fin.univ_val_map]
  conv_rhs => rw [← Multiset.coe_toList s]
  congr 1
  apply List.ext_get (by simp [hl])
  intro n h1 h2
  simp

/-- Continuity of `X ↦ ∑_{ν ∈ spec X} f ν` along a convergent sequence of matrices, for `f`
continuous on a closed set `T` containing all the spectra of the sequence. -/
theorem tendsto_sum_roots {X : ℕ → Matrix (Fin M) (Fin M) ℂ} {X₀ : Matrix (Fin M) (Fin M) ℂ}
    (hX : Tendsto X atTop (𝓝 X₀)) {f : ℂ → ℝ} {T : Set ℂ} (hT : IsClosed T)
    (hf : ContinuousOn f T) (hXT : ∀ n, ∀ ν ∈ (X n).charpoly.roots, ν ∈ T) :
    Tendsto (fun n => ((X n).charpoly.roots.map f).sum) atTop
      (𝓝 ((X₀.charpoly.roots.map f).sum)) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  choose e he using fun n => exists_enum _ (card_roots_charpoly (X (ns n)))
  -- uniform bound on the roots
  have hconv : Tendsto (fun n => mnorm (X (ns n))) atTop (𝓝 (mnorm X₀)) :=
    (continuous_mnorm.tendsto X₀).comp (hX.comp hns)
  obtain ⟨R, hR⟩ : ∃ R, ∀ n, mnorm (X (ns n)) ≤ R := by
    obtain ⟨R, hR⟩ := hconv.bddAbove_range
    exact ⟨R, fun n => hR ⟨n, rfl⟩⟩
  have hR0 : 0 ≤ R := (mnorm_nonneg _).trans (hR 0)
  have hbd : ∀ n, e n ∈ Metric.closedBall (0 : Fin M → ℂ) R := by
    intro n
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR0]
    intro i
    have hmem : e n i ∈ (X (ns n)).charpoly.roots := by
      rw [← he n]
      exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)
    exact (norm_le_mnorm hmem).trans (hR n)
  obtain ⟨μ, -, ψ, hψ, hlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hbd
  refine ⟨ψ, ?_⟩
  have hXψ : Tendsto (fun n => X (ns (ψ n))) atTop (𝓝 X₀) :=
    hX.comp (hns.comp hψ.tendsto_atTop)
  -- evaluation of the characteristic polynomials through the enumerations
  have hev : ∀ n ζ, (X (ns n)).charpoly.eval ζ = ∏ i, (ζ - e n i) := by
    intro n ζ
    rw [eval_charpoly_eq_prod, ← he n, Multiset.map_map]
    rfl
  have hX₀ : X₀.charpoly = ∏ i, (Polynomial.X - C (μ i)) := by
    apply Polynomial.funext
    intro ζ
    rw [eval_prod]
    simp only [eval_sub, eval_X, eval_C]
    have hA : Tendsto (fun n => (X (ns (ψ n))).charpoly.eval ζ) atTop
        (𝓝 (X₀.charpoly.eval ζ)) := by
      simp only [eval_charpoly]
      have hc : Continuous fun Y : Matrix (Fin M) (Fin M) ℂ => (Matrix.scalar (Fin M) ζ - Y).det :=
        (continuous_const.sub continuous_id).matrix_det
      exact (hc.tendsto X₀).comp hXψ
    have hB : Tendsto (fun n => (X (ns (ψ n))).charpoly.eval ζ) atTop
        (𝓝 (∏ i, (ζ - μ i))) := by
      simp only [hev]
      apply tendsto_finsetProd
      intro i _
      exact tendsto_const_nhds.sub (((continuous_apply i).tendsto μ).comp hlim)
    exact tendsto_nhds_unique hA hB
  have hroots : X₀.charpoly.roots = Multiset.map μ Finset.univ.val := by
    rw [hX₀]
    have : (∏ i, (Polynomial.X - C (μ i))) =
        ((Multiset.map μ Finset.univ.val).map fun a => Polynomial.X - C a).prod := by
      rw [Multiset.map_map]
      rfl
    rw [this, roots_multiset_prod_X_sub_C]
  have hsum : ∀ n, ((X (ns (ψ n))).charpoly.roots.map f).sum = ∑ i, f (e (ψ n) i) := by
    intro n
    rw [← he (ψ n), Multiset.map_map]
    rfl
  simp only [hsum]
  rw [hroots, Multiset.map_map]
  change Tendsto (fun n => ∑ i, f (e (ψ n) i)) atTop (𝓝 (∑ i, f (μ i)))
  apply tendsto_finsetSum
  intro i _
  have hei : Tendsto (fun n => e (ψ n) i) atTop (𝓝 (μ i)) :=
    ((continuous_apply i).tendsto μ).comp hlim
  have heT : ∀ n, e (ψ n) i ∈ T := by
    intro n
    apply hXT (ns (ψ n))
    rw [← he (ψ n)]
    exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)
  have hμT : μ i ∈ T := hT.mem_of_tendsto hei (Eventually.of_forall heT)
  exact (hf (μ i) hμT).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hei, Eventually.of_forall heT⟩)

/-- Upper semicontinuity of the spectrum. -/
theorem eventually_roots_near {Z : Type*} [TopologicalSpace Z] {X : Z → Matrix (Fin M) (Fin M) ℂ}
    {z₀ : Z} (hX : ContinuousAt X z₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z in 𝓝 z₀, ∀ ν ∈ (X z).charpoly.roots, ∃ ν₀ ∈ (X z₀).charpoly.roots, ‖ν - ν₀‖ < ε := by
  set R := mnorm (X z₀) + 1
  have hR : ∀ᶠ z in 𝓝 z₀, mnorm (X z) < R :=
    (continuous_mnorm.continuousAt.comp hX).eventually (gt_mem_nhds (by simp [R]))
  -- the determinant function
  set P : Z → ℂ → ℂ := fun z ζ => (Matrix.scalar (Fin M) ζ - X z).det with hPdef
  have hPc : ∀ ζ₀ : ℂ, ContinuousAt (fun p : Z × ℂ => P p.1 p.2 - P z₀ p.2) (z₀, ζ₀) := by
    intro ζ₀
    have hsc : Continuous fun ζ : ℂ => Matrix.scalar (Fin M) ζ := by
      have : (fun ζ : ℂ => Matrix.scalar (Fin M) ζ) = fun ζ => Matrix.diagonal fun _ => ζ := by
        funext ζ; rfl
      rw [this]
      exact Continuous.matrix_diagonal (continuous_pi fun _ => continuous_id)
    have h1 : ContinuousAt (fun p : Z × ℂ => Matrix.scalar (Fin M) p.2 - X p.1) (z₀, ζ₀) :=
      (hsc.comp continuous_snd).continuousAt.sub (hX.comp continuousAt_fst)
    have h2 : ContinuousAt (fun p : Z × ℂ => Matrix.scalar (Fin M) p.2 - X z₀) (z₀, ζ₀) :=
      ((hsc.comp continuous_snd).sub continuous_const).continuousAt
    have hdet : Continuous fun Y : Matrix (Fin M) (Fin M) ℂ => Y.det := continuous_id.matrix_det
    exact (hdet.continuousAt.comp h1).sub (hdet.continuousAt.comp h2)
  have hεM : 0 < ε ^ M := pow_pos hε M
  have hunif : ∀ᶠ z in 𝓝 z₀, ∀ ζ ∈ Metric.closedBall (0 : ℂ) R, ‖P z ζ - P z₀ ζ‖ < ε ^ M := by
    apply (isCompact_closedBall (0 : ℂ) R).eventually_forall_of_forall_eventually
    intro ζ₀ _
    have h0 := (hPc ζ₀).eventually (Metric.ball_mem_nhds _ hεM)
    filter_upwards [h0] with p hp
    simp only [sub_self, dist_zero_right] at hp
    exact hp
  filter_upwards [hR, hunif] with z hz hzu
  intro ν hν
  by_contra hcon
  push Not at hcon
  have hνR : ν ∈ Metric.closedBall (0 : ℂ) R := by
    rw [mem_closedBall_zero_iff]
    exact (norm_le_mnorm hν).trans hz.le
  have hPz : P z ν = 0 := by
    have := (mem_roots (charpoly_ne_zero (X z))).1 hν
    rw [IsRoot, eval_charpoly] at this
    exact this
  have hlt : ‖P z₀ ν‖ < ε ^ M := by
    have := hzu ν hνR
    rwa [hPz, zero_sub, norm_neg] at this
  have hge : ε ^ M ≤ ‖P z₀ ν‖ := by
    have hP0 : P z₀ ν = (X z₀).charpoly.eval ν := by rw [eval_charpoly]
    obtain ⟨e, he⟩ := exists_enum _ (card_roots_charpoly (X z₀))
    have hprod : (X z₀).charpoly.eval ν = ∏ i, (ν - e i) := by
      rw [eval_charpoly_eq_prod, ← he, Multiset.map_map]
      rfl
    rw [hP0, hprod, norm_prod]
    calc ε ^ M = ∏ _i : Fin M, ε := by simp
      _ ≤ ∏ i, ‖ν - e i‖ := by
        apply Finset.prod_le_prod (fun _ _ => hε.le)
        intro i _
        apply hcon
        rw [← he]
        exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)
  exact absurd hlt (not_lt.2 hge)

/-! ### Holomorphic dependence of the characteristic polynomial -/

lemma differentiableOn_mvPolynomial_eval₂ {σ : Type*} {U : Set ℂ} (g : σ → ℂ → ℂ)
    (hg : ∀ s, DifferentiableOn ℂ (g s) U) (q : MvPolynomial σ ℤ) :
    DifferentiableOn ℂ (fun z => MvPolynomial.eval₂ (Int.castRingHom ℂ) (fun s => g s z) q) U := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.eval₂_C]
    exact differentiableOn_const _
  | add p q hp hq =>
    simp only [MvPolynomial.eval₂_add]
    exact hp.add hq
  | mul_X p n hp =>
    simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    exact hp.mul (hg n)

/-- The coefficients of `charpoly (X z)` are holomorphic where the entries of `X z` are. -/
lemma differentiableOn_charpoly_coeff {U : Set ℂ} {X : ℂ → Matrix (Fin M) (Fin M) ℂ}
    (hX : ∀ i j, DifferentiableOn ℂ (fun z => X z i j) U) (k : ℕ) :
    DifferentiableOn ℂ (fun z => (X z).charpoly.coeff k) U := by
  have h : (fun z => (X z).charpoly.coeff k) = fun z =>
      MvPolynomial.eval₂ (Int.castRingHom ℂ) (fun p : Fin M × Fin M => X z p.1 p.2)
        ((Matrix.charpoly.univ ℤ (Fin M)).coeff k) := by
    funext z
    have hof : Matrix.of (Function.curry fun p : Fin M × Fin M => X z p.1 p.2) = X z := by
      ext i j; rfl
    rw [← MvPolynomial.coe_eval₂Hom, Matrix.charpoly.univ_coeff_eval₂Hom, hof]
  rw [h]
  exact differentiableOn_mvPolynomial_eval₂ (σ := Fin M × Fin M) (fun (p : Fin M × Fin M) (z : ℂ) => X z p.1 p.2)
    (fun p => hX p.1 p.2) _

lemma eval_charpoly_eq_sum (Y : Matrix (Fin M) (Fin M) ℂ) (ζ : ℂ) :
    Y.charpoly.eval ζ = ∑ k ∈ Finset.range (M + 1), Y.charpoly.coeff k * ζ ^ k :=
  eval_eq_sum_range' (by rw [charpoly_natDegree_eq_dim, Fintype.card_fin]; omega) ζ

lemma eval_derivative_charpoly_eq_sum (Y : Matrix (Fin M) (Fin M) ℂ) (ζ : ℂ) :
    (derivative Y.charpoly).eval ζ =
      ∑ k ∈ Finset.range (M + 1), Y.charpoly.coeff (k + 1) * ((k : ℂ) + 1) * ζ ^ k := by
  have hdeg : (derivative Y.charpoly).natDegree < M + 1 := by
    have := natDegree_derivative_le Y.charpoly
    rw [charpoly_natDegree_eq_dim, Fintype.card_fin] at this
    omega
  rw [eval_eq_sum_range' hdeg ζ]
  simp [coeff_derivative]

/-- Logarithmic derivative of `∏ (X - a)`. -/
lemma eval_derivative_prod_X_sub_C (s : Multiset ℂ) (ζ : ℂ) (hζ : ∀ a ∈ s, ζ ≠ a) :
    (derivative (s.map fun a => Polynomial.X - C a).prod).eval ζ =
      (s.map fun a => Polynomial.X - C a).prod.eval ζ * (s.map fun a => (ζ - a)⁻¹).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : ζ - a ≠ 0 := sub_ne_zero.2 (hζ a (Multiset.mem_cons_self a s))
    have ih' := ih (fun b hb => hζ b (Multiset.mem_cons_of_mem hb))
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, derivative_mul,
      derivative_sub, derivative_X, derivative_C, sub_zero, one_mul, eval_add, eval_mul,
      eval_sub, eval_X, eval_C] at ih' ⊢
    rw [ih']
    field_simp

/-- `p'/p = ∑ 1/(ζ - ν)` for characteristic polynomials. -/
lemma eval_derivative_charpoly (Y : Matrix (Fin M) (Fin M) ℂ) (ζ : ℂ)
    (hζ : ∀ a ∈ Y.charpoly.roots, ζ ≠ a) :
    (derivative Y.charpoly).eval ζ =
      Y.charpoly.eval ζ * (Y.charpoly.roots.map fun a => (ζ - a)⁻¹).sum := by
  conv_lhs => rw [charpoly_eq_prod_roots Y]
  conv_rhs => rw [charpoly_eq_prod_roots Y]
  rw [eval_derivative_prod_X_sub_C _ ζ hζ, roots_multiset_prod_X_sub_C]

end OQP27.Cell
