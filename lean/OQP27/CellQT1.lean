/-
OQP27/CellQT1.lean  (module L5: Q-T1 for step fields, from the strip inequality)

Q_quantum/LOG.md s.4 (Q-T1) and Q_rig/RIGIDITY_ALLD.md s.3.6, for a step field on a partition of the circle
into arcs `J_x = (t_x, t_{x+1})`: projections `A_x, B_x` with `A_x B_x = 0`, the operator constraint
`∑_x (|J_x|/2π) B_x = β 1` (`0 < β < 1`), and a strip function `h` (harmonic on the open strip, continuous
on the closed strip, of linear growth) for which the strip inequality `(*)` holds at `λ` for matrices of
size `M` (`StarAt M h λ`).  Then (`stepField_ineq`)
    `(1/π) ∑_{x,y} κ(x,y) Re Tr(A_x B_y) - λ ∑_x |J_x| Re Tr A_x ≤ 2π M h(β)`,
`κ(x,y) = Cl₂(t_x - t_y) - Cl₂(t_{x+1} - t_y) - Cl₂(t_x - t_{y+1}) + Cl₂(t_{x+1} - t_{y+1})`
(`arcKernel`; `κ/π = ∫_{J_x} g_y`, `g = ∑_y g_y B_y` the conjugate function of the field).
The proof: on `J_x` the boundary value of the Herglotz function is `B_x + i g(θ)`
(`herg_boundary_eq`); `Re Tr(A_x (g - λ)) ≤ Tr[(P(g-λ)P)_+] ≤ ∑_{ν ∈ spec(B_x + ig)} h(ν)`
(`re_trace_mul_le_posPart`, `trace_compress`, then `(*)`); integrate and use `mean_value_boundary`.
No hypotheses beyond the stated ones (`(*)` enters as the argument `hstar`).
-/
import OQP27.CellMeanValue
import OQP27.CellClausen
import OQP27.Skeleton

set_option autoImplicit false

namespace OQP27.Cell

open Polynomial Matrix Filter Topology Complex MeasureTheory Metric Set Real
open scoped Interval

variable {M : ℕ}

/-- The strip inequality `(*)` at a fixed `λ` for a fixed strip function `h`, for matrices of size `M`. -/
def StarAt (M : ℕ) (h : ℂ → ℝ) (lam : ℝ) : Prop :=
  ∀ Bm g : Matrix (Fin M) (Fin M) ℂ, IsProj Bm → g.IsHermitian →
    OQP27.posPartTrace ((1 - Bm) * (g - (lam : ℂ) • 1) * (1 - Bm)) ≤
      ((Bm + I • g).charpoly.roots.map h).sum

/-- L1's `Hyp_StripInequality` gives `StarAt` for `hStrip λ`. -/
lemma starAt_of_hyp (hS : OQP27.Hyp_StripInequality) (M : ℕ) (lam : ℝ) :
    StarAt M (OQP27.hStrip lam) lam :=
  fun Bm g hB hg => hS M Bm g hB hg lam

/-! ### A trace inequality -/

lemma proj_diag {W : Matrix (Fin M) (Fin M) ℂ} (hW : IsProj W) (i : Fin M) :
    (W i i).im = 0 ∧ 0 ≤ (W i i).re ∧ (W i i).re ≤ 1 := by
  have hsum : W i i = ((∑ k, ‖W i k‖ ^ 2 : ℝ) : ℂ) := by
    have h1 : W i i = (W * W) i i := by rw [hW.2]
    rw [h1, Matrix.mul_apply]
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    have hk : W k i = star (W i k) := by
      have := congrFun (congrFun hW.1 k) i
      rw [Matrix.conjTranspose_apply] at this
      exact this.symm
    rw [hk, Complex.star_def, Complex.mul_conj']
  set s := ∑ k, ‖W i k‖ ^ 2 with hs
  have hs0 : 0 ≤ s := by positivity
  have hsq : ‖W i i‖ ^ 2 ≤ s := by
    rw [hs]
    exact Finset.single_le_sum (f := fun k => ‖W i k‖ ^ 2) (fun k _ => by positivity)
      (Finset.mem_univ i)
  rw [hsum] at hsq
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hsq
  rw [hsum, Complex.ofReal_im, Complex.ofReal_re]
  refine ⟨rfl, hs0, ?_⟩
  by_contra hcon
  push Not at hcon
  nlinarith

/-- `Re Tr(A X) ≤ ∑ max(λ_i(X), 0)` for a projection `A` and a Hermitian `X`. -/
lemma re_trace_mul_le_posPart {A X : Matrix (Fin M) (Fin M) ℂ} (hA : IsProj A)
    (hX : X.IsHermitian) : (A * X).trace.re ≤ ∑ i, max (hX.eigenvalues i) 0 := by
  have hspec := hX.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  set U : Matrix (Fin M) (Fin M) ℂ := (hX.eigenvectorUnitary : Matrix (Fin M) (Fin M) ℂ) with hU
  set D : Matrix (Fin M) (Fin M) ℂ := diagonal (RCLike.ofReal ∘ hX.eigenvalues) with hD
  have hU1 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hX.eigenvectorUnitary.2
  have hU2 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hX.eigenvectorUnitary.2
  set W := star U * A * U with hWdef
  have hW : IsProj W := by
    constructor
    · rw [hWdef, Matrix.IsHermitian, conjTranspose_mul, conjTranspose_mul, hA.1,
        Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose, mul_assoc]
    · rw [hWdef]
      calc star U * A * U * (star U * A * U) = star U * A * (U * star U) * A * U := by
            simp only [mul_assoc]
        _ = star U * A * U := by rw [hU2, mul_one, mul_assoc (star U) A A, hA.2]
  have htr : (A * X).trace = (W * D).trace := by
    rw [hspec, hWdef]
    calc (A * (U * D * star U)).trace = ((A * U * D) * star U).trace := by simp only [mul_assoc]
      _ = (star U * (A * U * D)).trace := trace_mul_comm _ _
      _ = (star U * A * U * D).trace := by simp only [mul_assoc]
  rw [htr, Matrix.trace]
  simp only [Matrix.diag, hD, Matrix.mul_diagonal, Function.comp, Complex.re_sum]
  apply Finset.sum_le_sum
  intro i _
  obtain ⟨him, hre0, hre1⟩ := proj_diag hW i
  have : (W i i * ((hX.eigenvalues i : ℝ) : ℂ)).re = (W i i).re * hX.eigenvalues i := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [show (RCLike.ofReal (hX.eigenvalues i) : ℂ) = ((hX.eigenvalues i : ℝ) : ℂ) from rfl, this]
  rcases le_total (hX.eigenvalues i) 0 with he | he
  · rw [max_eq_right he]
    exact mul_nonpos_of_nonneg_of_nonpos hre0 he
  · rw [max_eq_left he]
    calc (W i i).re * hX.eigenvalues i ≤ 1 * hX.eigenvalues i :=
          mul_le_mul_of_nonneg_right hre1 he
      _ = hX.eigenvalues i := one_mul _

lemma mul_one_sub_eq {A B : Matrix (Fin M) (Fin M) ℂ} (hAB : A * B = 0) : A * (1 - B) = A := by
  rw [mul_sub, mul_one, hAB, sub_zero]

lemma one_sub_mul_eq {A B : Matrix (Fin M) (Fin M) ℂ} (hA : IsProj A) (hB : IsProj B)
    (hAB : A * B = 0) : (1 - B) * A = A := by
  have hBA : B * A = 0 := by
    have := congrArg conjTranspose hAB
    rw [conjTranspose_mul, hA.1, hB.1, conjTranspose_zero] at this
    exact this
  rw [sub_mul, one_mul, hBA, sub_zero]

lemma trace_compress {A B Y : Matrix (Fin M) (Fin M) ℂ} (hA : IsProj A) (hB : IsProj B)
    (hAB : A * B = 0) : (A * ((1 - B) * Y * (1 - B))).trace = (A * Y).trace := by
  calc (A * ((1 - B) * Y * (1 - B))).trace = ((A * (1 - B)) * Y * (1 - B)).trace := by
        simp only [mul_assoc]
    _ = (A * Y * (1 - B)).trace := by rw [mul_one_sub_eq hAB]
    _ = ((1 - B) * (A * Y)).trace := trace_mul_comm _ _
    _ = (((1 - B) * A) * Y).trace := by simp only [mul_assoc]
    _ = (A * Y).trace := by rw [one_sub_mul_eq hA hB hAB]

lemma isHermitian_compress {B Y : Matrix (Fin M) (Fin M) ℂ} (hB : IsProj B) (hY : Y.IsHermitian) :
    ((1 - B) * Y * (1 - B)).IsHermitian := by
  have h1 : (1 - B).IsHermitian := hB.one_sub.1
  have := Matrix.isHermitian_conjTranspose_mul_mul (1 - B) hY
  rwa [h1.eq] at this

/-- The pointwise inequality: `Re Tr(A g) - λ Re Tr A ≤ ∑_{ν ∈ spec(B + ig)} h ν`. -/
lemma pointwise_star {A B g : Matrix (Fin M) (Fin M) ℂ} (hA : IsProj A) (hB : IsProj B)
    (hAB : A * B = 0) (hg : g.IsHermitian) {h : ℂ → ℝ} {lam : ℝ} (hstar : StarAt M h lam) :
    (A * g).trace.re - lam * (A.trace).re ≤ ((B + I • g).charpoly.roots.map h).sum := by
  have hY : (g - (lam : ℂ) • 1).IsHermitian := by
    apply hg.sub
    rw [Matrix.IsHermitian, conjTranspose_smul, conjTranspose_one, Complex.star_def,
      Complex.conj_ofReal]
  have hX := isHermitian_compress hB hY
  have h1 : (A * g).trace.re - lam * (A.trace).re =
      (A * ((1 - B) * (g - (lam : ℂ) • 1) * (1 - B))).trace.re := by
    rw [trace_compress hA hB hAB, mul_sub, trace_sub, Matrix.mul_smul, mul_one, trace_smul,
      smul_eq_mul, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
  rw [h1]
  refine (re_trace_mul_le_posPart hA hX).trans ?_
  have h2 : OQP27.posPartTrace ((1 - B) * (g - (lam : ℂ) • 1) * (1 - B)) =
      ∑ i, max (hX.eigenvalues i) 0 := by
    unfold OQP27.posPartTrace
    rw [dif_pos hX]
  rw [← h2]
  exact hstar B g hB hg

/-! ### The boundary value of the Herglotz function on an arc -/

/-- The coefficients `g_y(θ) = (ℓ(θ - t_y) - ℓ(θ - t_{y+1}))/π` of the conjugate function. -/
noncomputable def gcoef {n : ℕ} (P : ArcPartition n) (y : ℕ) (θ : ℝ) : ℝ :=
  (ell (θ - P.t y) - ell (θ - P.t (y + 1))) / π

/-- The conjugate function `g(θ) = ∑_y g_y(θ) B_y` of the step field (RIGIDITY_ALLD.md (3.1)). -/
noncomputable def gconj {n : ℕ} (P : ArcPartition n) (B : ℕ → Matrix (Fin M) (Fin M) ℂ) (θ : ℝ) :
    Matrix (Fin M) (Fin M) ℂ :=
  ∑ y ∈ Finset.range n, ((gcoef P y θ : ℝ) : ℂ) • B y

lemma isHermitian_gconj {n : ℕ} (P : ArcPartition n) (B : ℕ → Matrix (Fin M) (Fin M) ℂ)
    (hB : ∀ k, IsProj (B k)) (θ : ℝ) : (gconj P B θ).IsHermitian := by
  unfold gconj
  rw [Matrix.IsHermitian, Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [conjTranspose_smul, (hB y).1.eq, Complex.star_def, Complex.conj_ofReal]

lemma ArcPartition.interior_ne_ends {n : ℕ} (P : ArcPartition n) {x : ℕ} (hx : x < n) {θ : ℝ}
    (h1 : P.t x < θ) (h2 : θ < P.t (x + 1)) :
    θ ∈ Ioo 0 (2 * π) ∧ ∀ k ≤ n, θ ≠ P.t k := by
  constructor
  · exact ⟨(P.t_nonneg (by omega)).trans_lt h1, h2.trans_le (P.t_le_two_pi (by omega))⟩
  · intro k hk heq
    rcases le_or_gt k x with hkx | hkx
    · have := P.t_le_t hkx (by omega)
      linarith
    · have := P.t_le_t (show x + 1 ≤ k by omega) hk
      linarith

lemma re_arcH_on_arc {n : ℕ} (P : ArcPartition n) {x : ℕ} (hx : x < n) {θ : ℝ}
    (h1 : P.t x < θ) (h2 : θ < P.t (x + 1)) {y : ℕ} (hy : y < n) :
    (arcH (P.t y) (P.t (y + 1)) (Complex.exp ((θ : ℂ) * I))).re = if y = x then 1 else 0 := by
  obtain ⟨hθ, hne⟩ := P.interior_ne_ends hx h1 h2
  rw [re_arcH_boundary (P.t_nonneg (by omega)) (P.t_lt y hy) (P.t_le_two_pi (by omega)) hθ.1 hθ.2
    (hne y (by omega)) (hne (y + 1) (by omega))]
  by_cases hyx : y = x
  · subst hyx
    rw [if_pos ⟨h1, h2⟩, if_pos rfl]
  · rw [if_neg hyx, if_neg]
    rintro ⟨h3, h4⟩
    rcases lt_or_gt_of_ne hyx with hlt | hgt
    · have := P.t_le_t (show y + 1 ≤ x by omega) (by omega)
      linarith
    · have := P.t_le_t (show x + 1 ≤ y by omega) (by omega)
      linarith

/-- On the arc `J_x` the boundary value of the Herglotz function is `B_x + i g(θ)`. -/
lemma herg_boundary_eq {n : ℕ} (P : ArcPartition n) (B : ℕ → Matrix (Fin M) (Fin M) ℂ) {x : ℕ}
    (hx : x < n) {θ : ℝ} (h1 : P.t x < θ) (h2 : θ < P.t (x + 1)) :
    herg P B (Complex.exp ((θ : ℂ) * I)) = B x + I • gconj P B θ := by
  unfold herg gconj
  have hsplit : ∀ y ∈ Finset.range n, arcH (P.t y) (P.t (y + 1)) (Complex.exp ((θ : ℂ) * I)) • B y =
      (if y = x then (1 : ℂ) else 0) • B y + I • (((gcoef P y θ : ℝ) : ℂ) • B y) := by
    intro y hy
    have hy' := Finset.mem_range.1 hy
    have hre := re_arcH_on_arc P hx h1 h2 hy'
    have him := im_arcH_boundary (P.t y) (P.t (y + 1)) θ
    have hval : arcH (P.t y) (P.t (y + 1)) (Complex.exp ((θ : ℂ) * I)) =
        (if y = x then (1 : ℂ) else 0) + I * ((gcoef P y θ : ℝ) : ℂ) := by
      apply Complex.ext
      · rw [hre]
        by_cases hyx : y = x <;> simp [hyx]
      · rw [him]
        by_cases hyx : y = x <;> simp [hyx, gcoef]
    rw [hval, add_smul, mul_smul]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ← Finset.smul_sum]
  congr 1
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hyx
    simp [hyx]
  · intro hx'
    exact absurd (Finset.mem_range.2 hx) hx'

/-! ### Integration over the arcs -/

/-- `κ(x,y) = Cl₂(t_x - t_y) - Cl₂(t_{x+1} - t_y) - Cl₂(t_x - t_{y+1}) + Cl₂(t_{x+1} - t_{y+1})`. -/
noncomputable def arcKernel {n : ℕ} (P : ArcPartition n) (x y : ℕ) : ℝ :=
  clausen2 (P.t x - P.t y) - clausen2 (P.t (x + 1) - P.t y) - clausen2 (P.t x - P.t (y + 1)) +
    clausen2 (P.t (x + 1) - P.t (y + 1))

lemma intervalIntegrable_ell_sub (t p q : ℝ) :
    IntervalIntegrable (fun θ => ell (θ - t)) volume p q := by
  have := (intervalIntegrable_ell (p - t) (q - t)).comp_sub_right t
  simpa using this

lemma intervalIntegrable_gcoef {n : ℕ} (P : ArcPartition n) (y : ℕ) (p q : ℝ) :
    IntervalIntegrable (gcoef P y) volume p q := by
  unfold gcoef
  exact ((intervalIntegrable_ell_sub _ p q).sub (intervalIntegrable_ell_sub _ p q)).div_const _

lemma integral_gcoef {n : ℕ} (P : ArcPartition n) (x y : ℕ) :
    ∫ θ in P.t x..P.t (x + 1), gcoef P y θ = arcKernel P x y / π := by
  unfold gcoef arcKernel
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub
    (intervalIntegrable_ell_sub _ _ _) (intervalIntegrable_ell_sub _ _ _), integral_ell_sub,
    integral_ell_sub]
  ring

lemma re_trace_mul_gconj {n : ℕ} (P : ArcPartition n) (A : Matrix (Fin M) (Fin M) ℂ)
    (B : ℕ → Matrix (Fin M) (Fin M) ℂ) (θ : ℝ) :
    (A * gconj P B θ).trace.re = ∑ y ∈ Finset.range n, gcoef P y θ * (A * B y).trace.re := by
  unfold gconj
  rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [Matrix.mul_smul, trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

/-- **Q-T1 for step fields** (Q_quantum/LOG.md s.4, RIGIDITY_ALLD.md (3.5)):
`(1/π) ∑_{x,y} κ(x,y) Re Tr(A_x B_y) - λ ∑_x |J_x| Re Tr A_x ≤ 2π M h(β)`. -/
theorem stepField_ineq {n : ℕ} (P : ArcPartition n) (A B : ℕ → Matrix (Fin M) (Fin M) ℂ)
    (hA : ∀ k, IsProj (A k)) (hB : ∀ k, IsProj (B k)) (hAB : ∀ k, A k * B k = 0)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hop : ∑ k ∈ Finset.range n,
      ((((P.t (k + 1) - P.t k) / (2 * π)) : ℝ) : ℂ) • B k = (β : ℂ) • 1)
    {h : ℂ → ℝ} (hharm : InnerProductSpace.HarmonicOnNhd h strip)
    (hcont : ContinuousOn h cstrip) {C : ℝ} (hC : 0 ≤ C)
    (hgrowth : ∀ w ∈ cstrip, |h w| ≤ C * (1 + ‖w‖)) {lam : ℝ} (hstar : StarAt M h lam) :
    (∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n, arcKernel P x y * (A x * B y).trace.re) / π -
      lam * ∑ x ∈ Finset.range n, (P.t (x + 1) - P.t x) * (A x).trace.re ≤ 2 * π * (M * h β) := by
  obtain ⟨hint, hval⟩ := mean_value_boundary P B hB hβ0 hβ1 hop hharm hcont hC hgrowth
  set ustar : ℝ → ℝ := fun θ => ((herg P B (Complex.exp ((θ : ℂ) * I))).charpoly.roots.map h).sum
    with hustar
  have hsub : ∀ k ≤ n, P.t k ∈ uIcc 0 (2 * π) := by
    intro k hk
    rw [uIcc_of_le (by positivity)]
    exact ⟨P.t_nonneg hk, P.t_le_two_pi hk⟩
  have hsplit : ∫ θ in (0 : ℝ)..2 * π, ustar θ =
      ∑ x ∈ Finset.range n, ∫ θ in P.t x..P.t (x + 1), ustar θ := by
    rw [intervalIntegral.sum_integral_adjacent_intervals, P.t_zero, P.t_last]
    intro k hk
    exact hint.mono_set (uIcc_subset_uIcc (hsub k hk.le) (hsub (k + 1) hk))
  set L : ℕ → ℝ → ℝ := fun x θ =>
    ∑ y ∈ Finset.range n, gcoef P y θ * (A x * B y).trace.re - lam * (A x).trace.re with hL
  have hL_int : ∀ x, IntervalIntegrable (L x) volume (P.t x) (P.t (x + 1)) := by
    intro x
    apply IntervalIntegrable.sub _ intervalIntegrable_const
    apply intervalIntegrable_fun_sum
    intro y _
    exact (intervalIntegrable_gcoef P y _ _).mul_const _
  have hL_val : ∀ x, ∫ θ in P.t x..P.t (x + 1), L x θ =
      (∑ y ∈ Finset.range n, arcKernel P x y * (A x * B y).trace.re) / π -
        lam * ((P.t (x + 1) - P.t x) * (A x).trace.re) := by
    intro x
    simp only [hL]
    rw [intervalIntegral.integral_sub _ intervalIntegrable_const, intervalIntegral.integral_finsetSum,
      intervalIntegral.integral_const, smul_eq_mul, Finset.sum_div]
    · congr 1
      · apply Finset.sum_congr rfl
        intro y _
        rw [intervalIntegral.integral_mul_const, integral_gcoef]
        ring
      · ring
    · intro y _
      exact (intervalIntegrable_gcoef P y _ _).mul_const _
    · apply intervalIntegrable_fun_sum
      intro y _
      exact (intervalIntegrable_gcoef P y _ _).mul_const _
  have hL_le : ∀ x ∈ Finset.range n, ∫ θ in P.t x..P.t (x + 1), L x θ ≤
      ∫ θ in P.t x..P.t (x + 1), ustar θ := by
    intro x hx
    have hx' := Finset.mem_range.1 hx
    apply intervalIntegral.integral_mono_on_of_le_Ioo (P.t_lt x hx').le (hL_int x)
      (hint.mono_set (uIcc_subset_uIcc (hsub x hx'.le) (hsub (x + 1) hx')))
    intro θ hθ
    simp only [hL, hustar]
    rw [← re_trace_mul_gconj, herg_boundary_eq P B hx' hθ.1 hθ.2]
    exact pointwise_star (hA x) (hB x) (hAB x) (isHermitian_gconj P B hB θ) hstar
  calc (∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n, arcKernel P x y * (A x * B y).trace.re) / π -
        lam * ∑ x ∈ Finset.range n, (P.t (x + 1) - P.t x) * (A x).trace.re
      = ∑ x ∈ Finset.range n, ∫ θ in P.t x..P.t (x + 1), L x θ := by
        rw [Finset.sum_congr rfl fun x _ => hL_val x, Finset.sum_sub_distrib, Finset.sum_div,
          Finset.mul_sum]
    _ ≤ ∑ x ∈ Finset.range n, ∫ θ in P.t x..P.t (x + 1), ustar θ := Finset.sum_le_sum hL_le
    _ = 2 * π * (M * h β) := by rw [← hsplit, hval]

end OQP27.Cell
