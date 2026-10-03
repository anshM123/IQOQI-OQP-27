import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Contour integrals of logarithmic derivatives of polynomials (module L3b, proof of RI)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

Main results:
* `circleIntegral_mul_logDeriv`: for a polynomial `p ≠ 0` without roots on the circle
  `|z - z₀| = ρ` and `φ` holomorphic on the open disc and continuous on its closure,
  `∮ φ p'/p dz = 2πi ∑_{|a - z₀| < ρ} φ(a)` (roots with multiplicity): formula (1.1) of Q_RI;
* `hasDerivAt_circleIntegral`, `continuousOn_circleIntegral`: differentiation under the circle
  integral and continuity of circle integrals in a parameter.

Hypotheses: none.
Paper: `iqoqi/programs/oqp27B_all/Q_RI/PROOF.md`, Lemma C, eq. (1.1); formalisation notes (F2), (F3).
-/

namespace OQP27.StripL3b

open Complex Polynomial Metric MeasureTheory Filter Topology Set Real

/-- `p'/p = ∑_{roots} 1/(z - a)` at a point that is not a root. -/
lemma logDeriv_eq_sum_inv (p : ℂ[X]) {z : ℂ} (hz : p.eval z ≠ 0) :
    p.derivative.eval z / p.eval z = (p.roots.map fun a => (z - a)⁻¹).sum := by
  rw [(IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero hz]
  simp [one_div]

lemma circleIntegral_zero' (c : ℂ) (R : ℝ) : (∮ _ in C(c, R), (0 : ℂ)) = 0 := by
  simp [circleIntegral]

lemma circleIntegrable_multiset_sum {ι : Type*} (S : Multiset ι) (F : ι → ℂ → ℂ) {c : ℂ} {R : ℝ}
    (hF : ∀ i ∈ S, CircleIntegrable (F i) c R) :
    CircleIntegrable (fun z => (S.map fun i => F i z).sum) c R := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons j S ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact (hF j (Multiset.mem_cons_self j S)).add
      (ih fun i hi => hF i (Multiset.mem_cons_of_mem hi))

/-- Circle integral of a finite (multiset) sum. -/
lemma circleIntegral_multiset_sum {ι : Type*} (S : Multiset ι) (F : ι → ℂ → ℂ) {c : ℂ} {R : ℝ}
    (hF : ∀ i ∈ S, CircleIntegrable (F i) c R) :
    (∮ z in C(c, R), (S.map fun i => F i z).sum) = (S.map fun i => ∮ z in C(c, R), F i z).sum := by
  induction S using Multiset.induction_on with
  | empty => simpa using circleIntegral_zero' c R
  | cons i S ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    have hS : ∀ j ∈ S, CircleIntegrable (F j) c R := fun j hj => hF j (Multiset.mem_cons_of_mem hj)
    rw [circleIntegral.integral_add (hF i (Multiset.mem_cons_self i S))
      (circleIntegrable_multiset_sum S F hS), ih hS]

lemma multiset_sum_map_ite_eq {S : Multiset ℂ} (q : ℂ → Prop) [DecidablePred q] (g : ℂ → ℂ) :
    (S.map fun a => if q a then g a else 0).sum = ((S.filter q).map g).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons b S ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.filter_cons]
    split_ifs <;> simp

/-- **Contour root sums.**  Let `p ≠ 0` have no root on the circle `|z - z₀| = ρ` and let `φ` be
holomorphic on the open disc and continuous on its closure.  Then
`∮ φ(z) p'(z)/p(z) dz = 2πi ∑_{roots a, |a - z₀| < ρ} φ(a)` (roots with multiplicity). -/
theorem circleIntegral_mul_logDeriv (p : ℂ[X]) (hp : p ≠ 0) {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hroot : ∀ a ∈ p.roots, dist a z₀ ≠ ρ) {φ : ℂ → ℂ} (hφ : DiffContOnCl ℂ φ (ball z₀ ρ)) :
    (∮ z in C(z₀, ρ), φ z * (p.derivative.eval z / p.eval z))
      = 2 * π * I * ((p.roots.filter fun a => dist a z₀ < ρ).map φ).sum := by
  have hne : ∀ z ∈ sphere z₀ ρ, p.eval z ≠ 0 := by
    intro z hz h0
    have hz' : z ∈ p.roots := (mem_roots hp).mpr h0
    exact hroot z hz' (mem_sphere.mp hz)
  have hcongr : EqOn (fun z => φ z * (p.derivative.eval z / p.eval z))
      (fun z => (p.roots.map fun a => φ z * (z - a)⁻¹).sum) (sphere z₀ ρ) := by
    intro z hz
    simp only
    rw [logDeriv_eq_sum_inv p (hne z hz), Multiset.sum_map_mul_left]
  rw [circleIntegral.integral_congr hρ.le hcongr]
  have hcont : ContinuousOn φ (closedBall z₀ ρ) := by
    simpa [closure_ball z₀ hρ.ne'] using hφ.continuousOn
  have hint : ∀ a ∈ p.roots, CircleIntegrable (fun z => φ z * (z - a)⁻¹) z₀ ρ := by
    intro a ha
    refine ContinuousOn.circleIntegrable hρ.le ?_
    refine (hcont.mono sphere_subset_closedBall).mul ?_
    refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) fun z hz h0 => ?_
    have : z = a := sub_eq_zero.mp h0
    subst this
    exact hroot z ha (mem_sphere.mp hz)
  have hone : ∀ a ∈ p.roots, (∮ z in C(z₀, ρ), φ z * (z - a)⁻¹)
      = if dist a z₀ < ρ then 2 * π * I * φ a else 0 := by
    intro a ha
    split_ifs with h
    · have := hφ.circleIntegral_sub_inv_smul (w := a) (mem_ball.mpr h)
      simp only [smul_eq_mul] at this
      rw [← this]
      congr 1
      funext z
      ring
    · have hout : ρ < dist a z₀ := lt_of_le_of_ne (not_lt.mp h) (hroot a ha).symm
      apply DiffContOnCl.circleIntegral_eq_zero hρ.le
      have hdiff : DifferentiableOn ℂ (fun z => (z - a)⁻¹) (closedBall z₀ ρ) := by
        refine DifferentiableOn.inv (differentiableOn_id.sub_const a) fun z hz h0 => ?_
        have : z = a := sub_eq_zero.mp h0
        subst this
        have := mem_closedBall.mp hz
        linarith
      exact hφ.smul (hdiff.diffContOnCl_ball subset_rfl)
  rw [circleIntegral_multiset_sum p.roots _ hint, Multiset.map_congr rfl hone,
    multiset_sum_map_ite_eq, Multiset.sum_map_mul_left]


/-! ### Circle integrals depending on a parameter -/

lemma continuous_deriv_circleMap (z₀ : ℂ) (R : ℝ) :
    Continuous fun θ : ℝ => deriv (circleMap z₀ R) θ := by
  have h : (fun θ : ℝ => deriv (circleMap z₀ R) θ) = fun θ => circleMap 0 R θ * I :=
    funext (deriv_circleMap z₀ R)
  rw [h]
  exact (continuous_circleMap 0 R).mul continuous_const

lemma continuous_circleMap_comp {F : ℂ → ℂ} {z₀ : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hF : ContinuousOn F (sphere z₀ R)) : Continuous fun θ : ℝ => F (circleMap z₀ R θ) :=
  hF.comp_continuous (continuous_circleMap z₀ R) fun θ => circleMap_mem_sphere z₀ hR θ

/-- **Differentiation under the circle integral** (parameter in `ℝ` or `ℂ`). -/
theorem hasDerivAt_circleIntegral {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 ℂ]
    [SMulCommClass 𝕜 ℂ ℂ] {F F' : 𝕜 → ℂ → ℂ} {x₀ : 𝕜} {ε : ℝ} (hε : 0 < ε) {z₀ : ℂ} {R : ℝ}
    (hR : 0 < R) (hF : ∀ x ∈ ball x₀ ε, ContinuousOn (F x) (sphere z₀ R))
    (hF' : ContinuousOn (fun p : 𝕜 × ℂ => F' p.1 p.2) (closedBall x₀ ε ×ˢ sphere z₀ R))
    (hd : ∀ x ∈ ball x₀ ε, ∀ z ∈ sphere z₀ R, HasDerivAt (fun x => F x z) (F' x z) x) :
    HasDerivAt (fun x => ∮ z in C(z₀, R), F x z) (∮ z in C(z₀, R), F' x₀ z) x₀ := by
  -- a uniform bound for `F'` on the compact set `closedBall x₀ ε × sphere z₀ R`
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x₀ ε).prod (isCompact_sphere z₀ R)).exists_bound_of_continuousOn
    hF'
  have hF'x : ∀ x ∈ closedBall x₀ ε, ContinuousOn (F' x) (sphere z₀ R) := fun x hx =>
    hF'.comp (continuousOn_const.prodMk continuousOn_id) fun z hz => ⟨hx, hz⟩
  have hx₀ : x₀ ∈ ball x₀ ε := mem_ball_self hε
  unfold circleIntegral
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume) (a := 0) (b := 2 * π)
    (F := fun x θ => deriv (circleMap z₀ R) θ • F x (circleMap z₀ R θ))
    (F' := fun x θ => deriv (circleMap z₀ R) θ • F' x (circleMap z₀ R θ))
    (x₀ := x₀) (s := ball x₀ ε) (bound := fun _ => R * C)
    (isOpen_ball.mem_nhds hx₀)
    (Filter.eventually_of_mem (isOpen_ball.mem_nhds hx₀) fun x hx =>
      (((continuous_deriv_circleMap z₀ R)).smul
        (continuous_circleMap_comp hR.le (hF x hx))).aestronglyMeasurable)
    ((((continuous_deriv_circleMap z₀ R)).smul
        (continuous_circleMap_comp hR.le (hF x₀ hx₀))).intervalIntegrable _ _)
    ((((continuous_deriv_circleMap z₀ R)).smul
        (continuous_circleMap_comp hR.le (hF'x x₀ (mem_closedBall_self hε.le)))).aestronglyMeasurable)
    (MeasureTheory.ae_of_all _ fun θ _ x hx => by
      rw [norm_smul, deriv_circleMap, norm_mul, norm_circleMap_zero, norm_I, mul_one,
        abs_of_pos hR]
      exact mul_le_mul_of_nonneg_left (hC (x, circleMap z₀ R θ)
        ⟨ball_subset_closedBall hx, circleMap_mem_sphere z₀ hR.le θ⟩) hR.le)
    intervalIntegrable_const
    (MeasureTheory.ae_of_all _ fun θ _ x hx =>
      (hd x hx _ (circleMap_mem_sphere z₀ hR.le θ)).const_smul (deriv (circleMap z₀ R) θ))
  exact key.2

/-- **Continuity of circle integrals in a parameter.** -/
theorem continuousOn_circleIntegral {X : Type*} [TopologicalSpace X] {F : X → ℂ → ℂ} {S : Set X}
    {z₀ : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hF : ContinuousOn (fun p : X × ℂ => F p.1 p.2) (S ×ˢ sphere z₀ R)) :
    ContinuousOn (fun x => ∮ z in C(z₀, R), F x z) S := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hc : Continuous fun p : S × ℝ =>
      deriv (circleMap z₀ R) p.2 • F (p.1 : X) (circleMap z₀ R p.2) := by
    refine ((continuous_deriv_circleMap z₀ R).comp continuous_snd).smul ?_
    refine hF.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk
      ((continuous_circleMap z₀ R).comp continuous_snd)) fun p => ⟨p.1.2, ?_⟩
    exact circleMap_mem_sphere z₀ hR p.2
  have := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := MeasureTheory.volume) (f := fun (x : S) θ => deriv (circleMap z₀ R) θ • F (x : X) (circleMap z₀ R θ))
    hc 0 (2 * π)
  exact this

end OQP27.StripL3b
