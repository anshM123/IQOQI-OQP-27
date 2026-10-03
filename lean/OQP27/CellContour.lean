/-
OQP27/CellContour.lean  (module L5, layer 2b: holomorphic functional calculus via contours)

What is proved here (complete proofs):
* `circleIntegral_logDeriv_charpoly`   argument-principle formula: for `f` holomorphic on a closed
      disc whose boundary circle carries no eigenvalue of `Y`,
      `∮ (p'/p) f = 2πi ∑_{ν ∈ spec Y, |ν - c| < ε} f ν`  (`p = charpoly Y`);
* `differentiableOn_circleIntegral_param`   a circle integral of a family that is jointly continuous
      and holomorphic in the parameter is holomorphic in the parameter (Cauchy formula + Fubini);
* `harmonicOnNhd_sum_roots`   if `z ↦ X z` is holomorphic on an open set `U`, all eigenvalues of
      `X z` (`z ∈ U`) lie in an open set `S`, and `h` is harmonic on `S`, then
      `z ↦ ∑_{ν ∈ spec (X z)} h ν` (algebraic multiplicities) is harmonic on `U`.
This is step (ii) of the proof of Q-T1 (Q_quantum/LOG.md s.4) and RIGIDITY_ALLD.md s.3.4
("u_lam(z) = Re Tr phi_lam(H(z)) is harmonic"), done locally: near each eigenvalue cluster `h` is
the real part of a holomorphic function (Mathlib), and the cluster sum is a contour integral.
No hypotheses remain.
-/
import OQP27.CellRoots
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

set_option autoImplicit false

namespace OQP27.Cell

open Polynomial Matrix Filter Topology Complex MeasureTheory Metric Set Real

variable {M : ℕ}

/-! ### The argument-principle formula -/

lemma circleIntegral_sum_inv_mul (s : Multiset ℂ) {c : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hsph : ∀ ν ∈ s, ‖ν - c‖ ≠ ε) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (closedBall c ε)) :
    (∮ ζ in C(c, ε), (s.map fun a => (ζ - a)⁻¹ * f ζ).sum) =
      (2 * π * I) * ((s.filter fun ν => ‖ν - c‖ < ε).map f).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [circleIntegral]
  | cons a s ih =>
    have ha : ‖a - c‖ ≠ ε := hsph a (Multiset.mem_cons_self a s)
    have ih' := ih (fun b hb => hsph b (Multiset.mem_cons_of_mem hb))
    have hfc : ContinuousOn f (closedBall c ε) := hf.continuousOn
    -- integrability of the single term
    have hint_a : CircleIntegrable (fun ζ => (ζ - a)⁻¹ * f ζ) c ε := by
      apply ContinuousOn.circleIntegrable hε.le
      apply ContinuousOn.mul _ (hfc.mono sphere_subset_closedBall)
      apply ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
      intro ζ hζ h0
      apply ha
      change ζ - a = 0 at h0
      rw [sub_eq_zero] at h0
      rw [← h0, mem_sphere_iff_norm.1 hζ]
    have hint_s : CircleIntegrable (fun ζ => (s.map fun b => (ζ - b)⁻¹ * f ζ).sum) c ε := by
      apply ContinuousOn.circleIntegrable hε.le
      refine continuousOn_multiset_sum (f := fun b ζ => (ζ - b)⁻¹ * f ζ) s ?_
      intro b hb
      apply ContinuousOn.mul _ (hfc.mono sphere_subset_closedBall)
      apply ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
      intro ζ hζ h0
      apply hsph b (Multiset.mem_cons_of_mem hb)
      change ζ - b = 0 at h0
      rw [sub_eq_zero] at h0
      rw [← h0, mem_sphere_iff_norm.1 hζ]
    simp only [Multiset.map_cons, Multiset.sum_cons]
    rw [circleIntegral.integral_add hint_a hint_s, ih']
    by_cases hlt : ‖a - c‖ < ε
    · rw [Multiset.filter_cons_of_pos (p := fun ν => ‖ν - c‖ < ε) s hlt, Multiset.map_cons, Multiset.sum_cons]
      have hcauchy : (∮ ζ in C(c, ε), (ζ - a)⁻¹ * f ζ) = (2 * π * I) * f a := by
        have := DiffContOnCl.circleIntegral_sub_inv_smul (R := ε) (c := c) (w := a) (f := f)
          (by
            apply DifferentiableOn.diffContOnCl
            rwa [closure_ball c hε.ne'])
          (by rwa [mem_ball, dist_eq_norm])
        simpa [smul_eq_mul] using this
      rw [hcauchy]
      ring
    · rw [Multiset.filter_cons_of_neg (p := fun ν => ‖ν - c‖ < ε) s hlt]
      have hgt : ε < ‖a - c‖ := lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm ha)
      have hzero : (∮ ζ in C(c, ε), (ζ - a)⁻¹ * f ζ) = 0 := by
        apply circleIntegral_eq_zero_of_differentiable_on_off_countable hε.le countable_empty
        · apply ContinuousOn.mul _ hfc
          apply ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
          intro ζ hζ h0
          change ζ - a = 0 at h0
          rw [sub_eq_zero] at h0
          rw [h0, mem_closedBall, dist_eq_norm] at hζ
          linarith
        · intro ζ hζ
          have hζ' : ζ ∈ ball c ε := hζ.1
          apply DifferentiableAt.mul
          · apply DifferentiableAt.inv (differentiableAt_id.sub (differentiableAt_const _))
            intro h0
            rw [sub_eq_zero] at h0
            rw [h0, mem_ball, dist_eq_norm] at hζ'
            linarith
          · exact hf.differentiableAt (closedBall_mem_nhds_of_mem hζ')
      rw [hzero]
      ring

/-- The argument-principle formula for characteristic polynomials. -/
theorem circleIntegral_logDeriv_charpoly (Y : Matrix (Fin M) (Fin M) ℂ) {c : ℂ} {ε : ℝ}
    (hε : 0 < ε) (hsph : ∀ ν ∈ Y.charpoly.roots, ‖ν - c‖ ≠ ε) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (closedBall c ε)) :
    (∮ ζ in C(c, ε), ((derivative Y.charpoly).eval ζ / Y.charpoly.eval ζ) * f ζ) =
      (2 * π * I) * ((Y.charpoly.roots.filter fun ν => ‖ν - c‖ < ε).map f).sum := by
  rw [← circleIntegral_sum_inv_mul _ hε hsph hf]
  apply circleIntegral.integral_congr hε.le
  intro ζ hζ
  have hζr : ∀ a ∈ Y.charpoly.roots, ζ ≠ a := by
    intro a ha h
    apply hsph a ha
    rw [← h]
    exact mem_sphere_iff_norm.1 hζ
  have hP : Y.charpoly.eval ζ ≠ 0 := by
    intro h0
    exact hζr ζ ((mem_roots (charpoly_ne_zero Y)).2 h0) rfl
  simp only
  rw [eval_derivative_charpoly Y ζ hζr, mul_div_cancel_left₀ _ hP, Multiset.sum_map_mul_right]

/-! ### Holomorphic dependence of circle integrals on a parameter -/

/-- Fubini for interval integrals of a continuous function of two real variables. -/
lemma intervalIntegral_swap {f : ℝ → ℝ → ℂ} (hf : Continuous (Function.uncurry f))
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    (∫ x in a..b, ∫ y in c..d, f x y) = ∫ y in c..d, ∫ x in a..b, f x y := by
  simp only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  apply MeasureTheory.integral_integral_swap
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact (ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    hf.continuousOn).mono_set (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)

/-- A circle integral of a family that is jointly continuous and holomorphic in the parameter
is holomorphic in the parameter. -/
theorem differentiableOn_circleIntegral_param {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ}
    (hR : 0 < R) {Ψ : ℂ → ℂ → ℂ} (hcont : ContinuousOn (Function.uncurry Ψ) (U ×ˢ sphere c R))
    (hdiff : ∀ ζ ∈ sphere c R, DifferentiableOn ℂ (fun z => Ψ z ζ) U) :
    DifferentiableOn ℂ (fun z => ∮ ζ in C(c, R), Ψ z ζ) U := by
  set J : ℂ → ℂ := fun z => ∮ ζ in C(c, R), Ψ z ζ with hJdef
  have hcm : ∀ θ, circleMap c R θ ∈ sphere c R := fun θ => circleMap_mem_sphere c hR.le θ
  -- continuity of `J` on `U`
  have hJc : ContinuousOn J U := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hcj : Continuous (Function.uncurry fun (w : U) (θ : ℝ) =>
        deriv (circleMap c R) θ • Ψ w (circleMap c R θ)) := by
      show Continuous fun p : U × ℝ => deriv (circleMap c R) p.2 • Ψ p.1 (circleMap c R p.2)
      simp only [smul_eq_mul]
      apply Continuous.mul
      · simp only [deriv_circleMap]
        exact ((continuous_circleMap 0 R).comp continuous_snd).mul continuous_const
      · apply hcont.comp_continuous
          (by fun_prop : Continuous fun p : U × ℝ => ((p.1 : ℂ), circleMap c R p.2))
        intro p
        exact ⟨p.1.2, hcm p.2⟩
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hcj 0 (2 * π)
  intro z₀ hz₀
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU z₀ hz₀
  set δ : ℝ := r / 2 with hδ
  have hδpos : 0 < δ := by positivity
  have hcb : closedBall z₀ δ ⊆ U := (closedBall_subset_ball (by linarith)).trans hball
  -- Cauchy representation of `J` on `ball z₀ δ`
  have hrep : ∀ z ∈ ball z₀ δ, J z = (2 * π * I)⁻¹ • ∮ w in C(z₀, δ), (w - z)⁻¹ • J w := by
    intro z hz
    have hwz : ∀ φ : ℝ, circleMap z₀ δ φ - z ≠ 0 := by
      intro φ h0
      rw [sub_eq_zero] at h0
      have h1 := circleMap_mem_sphere z₀ hδpos.le φ
      rw [h0, mem_sphere, dist_eq_norm] at h1
      rw [mem_ball, dist_eq_norm] at hz
      linarith
    have hpt : ∀ θ : ℝ, Ψ z (circleMap c R θ) = (2 * π * I)⁻¹ *
        ∫ φ in (0 : ℝ)..2 * π, deriv (circleMap z₀ δ) φ *
          ((circleMap z₀ δ φ - z)⁻¹ * Ψ (circleMap z₀ δ φ) (circleMap c R θ)) := by
      intro θ
      have hdc : DiffContOnCl ℂ (fun w => Ψ w (circleMap c R θ)) (ball z₀ δ) := by
        apply DifferentiableOn.diffContOnCl
        rw [closure_ball z₀ hδpos.ne']
        exact (hdiff _ (hcm θ)).mono hcb
      have := hdc.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hz
      rw [← this]
      simp only [circleIntegral, smul_eq_mul]
    -- the double integrand
    set G : ℝ → ℝ → ℂ := fun θ φ => deriv (circleMap c R) θ * (deriv (circleMap z₀ δ) φ *
      ((circleMap z₀ δ φ - z)⁻¹ * Ψ (circleMap z₀ δ φ) (circleMap c R θ))) with hG
    have hGc : Continuous (Function.uncurry G) := by
      simp only [hG, deriv_circleMap]
      apply Continuous.mul
      · exact ((continuous_circleMap 0 R).comp continuous_fst).mul continuous_const
      apply Continuous.mul
      · exact ((continuous_circleMap 0 δ).comp continuous_snd).mul continuous_const
      apply Continuous.mul
      · exact Continuous.inv₀ (((continuous_circleMap z₀ δ).comp continuous_snd).sub
          continuous_const) (fun p => hwz p.2)
      · apply hcont.comp_continuous (by fun_prop : Continuous fun p : ℝ × ℝ =>
          (circleMap z₀ δ p.2, circleMap c R p.1))
        intro p
        exact ⟨hcb (sphere_subset_closedBall (circleMap_mem_sphere z₀ hδpos.le p.2)), hcm p.1⟩
    calc J z = ∫ θ in (0 : ℝ)..2 * π, deriv (circleMap c R) θ * Ψ z (circleMap c R θ) := by
          simp only [hJdef, circleIntegral, smul_eq_mul]
      _ = ∫ θ in (0 : ℝ)..2 * π, (2 * π * I)⁻¹ * ∫ φ in (0 : ℝ)..2 * π, G θ φ := by
          apply intervalIntegral.integral_congr
          intro θ _
          simp only [hpt θ, hG]
          rw [intervalIntegral.integral_const_mul]
          ring
      _ = (2 * π * I)⁻¹ * ∫ φ in (0 : ℝ)..2 * π, ∫ θ in (0 : ℝ)..2 * π, G θ φ := by
          rw [intervalIntegral.integral_const_mul,
            intervalIntegral_swap hGc (by positivity) (by positivity)]
      _ = (2 * π * I)⁻¹ * ∫ φ in (0 : ℝ)..2 * π, deriv (circleMap z₀ δ) φ *
            ((circleMap z₀ δ φ - z)⁻¹ * J (circleMap z₀ δ φ)) := by
          congr 1
          apply intervalIntegral.integral_congr
          intro φ _
          simp only [hG, hJdef, circleIntegral, smul_eq_mul]
          rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro θ _
          ring
      _ = (2 * π * I)⁻¹ • ∮ w in C(z₀, δ), (w - z)⁻¹ • J w := by
          simp only [circleIntegral, smul_eq_mul]
  -- analyticity of the Cauchy integral
  have hint : CircleIntegrable J z₀ (⟨δ, hδpos.le⟩ : NNReal) :=
    (hJc.mono ((sphere_subset_closedBall).trans hcb)).circleIntegrable hδpos.le
  have hps := hasFPowerSeriesOn_cauchy_integral hint (by exact_mod_cast hδpos)
  have hda : DifferentiableAt ℂ (fun z => (2 * π * I)⁻¹ • ∮ w in C(z₀, δ), (w - z)⁻¹ • J w) z₀ :=
    hps.analyticAt.differentiableAt
  have heq : J =ᶠ[𝓝 z₀] fun z => (2 * π * I)⁻¹ • ∮ w in C(z₀, δ), (w - z)⁻¹ • J w := by
    filter_upwards [ball_mem_nhds z₀ hδpos] with z hz
    exact hrep z hz
  exact (hda.congr_of_eventuallyEq heq).differentiableWithinAt

/-! ### Harmonicity of the eigenvalue sum -/

/-- Splitting a multiset sum according to `ε`-separated centres. -/
lemma multiset_sum_eq_sum_filter {β : Type*} [AddCommMonoid β] (s : Multiset ℂ) (C : Finset ℂ)
    {ε : ℝ} (g : ℂ → β) (hcover : ∀ a ∈ s, ∃ c ∈ C, ‖a - c‖ < ε)
    (hsep : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' → 2 * ε ≤ ‖c - c'‖) :
    (s.map g).sum = ∑ c ∈ C, ((s.filter fun a => ‖a - c‖ < ε).map g).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons,
      ih (fun b hb => hcover b (Multiset.mem_cons_of_mem hb))]
    obtain ⟨c₀, hc₀, ha₀⟩ := hcover a (Multiset.mem_cons_self a s)
    have key : ∀ c ∈ C, ((Multiset.filter (fun x => ‖x - c‖ < ε) (a ::ₘ s)).map g).sum =
        (if ‖a - c‖ < ε then g a else 0) +
          ((Multiset.filter (fun x => ‖x - c‖ < ε) s).map g).sum := by
      intro c _
      by_cases h : ‖a - c‖ < ε
      · rw [Multiset.filter_cons_of_pos (p := fun x => ‖x - c‖ < ε) s h, if_pos h,
          Multiset.map_cons, Multiset.sum_cons]
      · rw [Multiset.filter_cons_of_neg (p := fun x => ‖x - c‖ < ε) s h, if_neg h, zero_add]
    rw [Finset.sum_congr rfl key, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single c₀]
    · rw [if_pos ha₀]
    · intro c hc hne
      rw [if_neg]
      intro hlt
      have h1 := hsep c hc c₀ hc₀ hne
      have h2 : ‖c - c₀‖ < 2 * ε := by
        calc ‖c - c₀‖ = ‖(a - c₀) - (a - c)‖ := by ring_nf
          _ ≤ ‖a - c₀‖ + ‖a - c‖ := norm_sub_le _ _
          _ < 2 * ε := by linarith
      linarith
    · intro h
      exact absurd hc₀ h

lemma re_multiset_sum (s : Multiset ℂ) (g : ℂ → ℂ) :
    ((s.map g).sum).re = (s.map fun a => (g a).re).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih]

/-- **Harmonicity of eigenvalue sums.**  If `z ↦ X z` is holomorphic on the open set `U`, all
eigenvalues of `X z` (`z ∈ U`) lie in the open set `S`, and `h` is harmonic on `S`, then
`z ↦ ∑_{ν ∈ spec (X z)} h ν` (algebraic multiplicities) is harmonic on `U`. -/
theorem harmonicOnNhd_sum_roots {U : Set ℂ} (hU : IsOpen U) {X : ℂ → Matrix (Fin M) (Fin M) ℂ}
    (hX : ∀ i j, DifferentiableOn ℂ (fun z => X z i j) U) {S : Set ℂ} (hS : IsOpen S)
    {h : ℂ → ℝ} (hh : InnerProductSpace.HarmonicOnNhd h S)
    (hspec : ∀ z ∈ U, ∀ ν ∈ (X z).charpoly.roots, ν ∈ S) :
    InnerProductSpace.HarmonicOnNhd (fun z => ((X z).charpoly.roots.map h).sum) U := by
  intro z₀ hz₀
  set R₀ : Finset ℂ := (X z₀).charpoly.roots.toFinset with hR₀
  have hR₀S : ∀ ν ∈ R₀, ν ∈ S := fun ν hν => hspec z₀ hz₀ ν (Multiset.mem_toFinset.1 hν)
  -- choice of the radius
  obtain ⟨ε, hε, hballS, hsep⟩ : ∃ ε > 0, (∀ ν ∈ R₀, ball ν (2 * ε) ⊆ S) ∧
      (∀ ν ∈ R₀, ∀ ν' ∈ R₀, ν ≠ ν' → 3 * ε ≤ ‖ν - ν'‖) := by
    have h1 : ∀ ν ∈ R₀, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ball ν (2 * ε) ⊆ S := by
      intro ν hν
      obtain ⟨r, hr, hrS⟩ := Metric.isOpen_iff.1 hS ν (hR₀S ν hν)
      have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), 2 * ε < r :=
        (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simpa using hr)
      filter_upwards [nhdsWithin_le_nhds hev] with ε hε'
      exact (ball_subset_ball hε'.le).trans hrS
    have h2 : ∀ p ∈ R₀ ×ˢ R₀, ∀ᶠ ε in 𝓝[>] (0 : ℝ), p.1 ≠ p.2 → 3 * ε ≤ ‖p.1 - p.2‖ := by
      intro p _
      by_cases hp : p.1 = p.2
      · exact Eventually.of_forall fun _ h => absurd hp h
      · have hpos : 0 < ‖p.1 - p.2‖ := norm_pos_iff.2 (sub_ne_zero.2 hp)
        have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), 3 * ε < ‖p.1 - p.2‖ :=
          (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simpa using hpos)
        filter_upwards [nhdsWithin_le_nhds hev] with ε hε' _
        exact hε'.le
    have h3 := (Filter.eventually_all_finset R₀).2 h1
    have h4 := (Filter.eventually_all_finset (R₀ ×ˢ R₀)).2 h2
    obtain ⟨ε, ⟨h3', h4'⟩, hε⟩ := ((h3.and h4).and self_mem_nhdsWithin).exists
    exact ⟨ε, hε, h3', fun ν hν ν' hν' hne =>
      h4' (ν, ν') (Finset.mem_product.2 ⟨hν, hν'⟩) hne⟩
  -- local holomorphic functions with real part `h`
  have hharm : ∀ ν ∈ R₀, InnerProductSpace.HarmonicOnNhd h (ball ν (2 * ε)) :=
    fun ν hν => hh.mono (hballS ν hν)
  choose! F hFan hFre using fun ν hν =>
    InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq (hharm ν hν)
  -- continuity of `X` at `z₀`
  have hXc : ContinuousAt X z₀ := by
    apply continuousAt_pi.2
    intro i
    apply continuousAt_pi.2
    intro j
    exact ((hX i j).differentiableAt (hU.mem_nhds hz₀)).continuousAt
  obtain ⟨V, hVsub, hVopen, hz₀V⟩ :=
    _root_.eventually_nhds_iff.1 ((eventually_roots_near hXc hε).and (hU.mem_nhds hz₀))
  have hVU : V ⊆ U := fun z hz => (hVsub z hz).2
  -- eigenvalues of `X z` (`z ∈ V`) avoid the circles
  have hcov : ∀ z ∈ V, ∀ a ∈ (X z).charpoly.roots, ∃ ν ∈ R₀, ‖a - ν‖ < ε := by
    intro z hz a ha
    obtain ⟨ν₀, hν₀, hlt⟩ := (hVsub z hz).1 a ha
    exact ⟨ν₀, Multiset.mem_toFinset.2 hν₀, hlt⟩
  have hnot : ∀ z ∈ V, ∀ ν ∈ R₀, ∀ a ∈ (X z).charpoly.roots, ‖a - ν‖ ≠ ε := by
    intro z hz ν hν a ha heq
    obtain ⟨ν₀, hν₀, hlt⟩ := hcov z hz a ha
    have hne : ν ≠ ν₀ := by
      rintro rfl
      linarith
    have h1 := hsep ν hν ν₀ hν₀ hne
    have h2 : ‖ν - ν₀‖ < 2 * ε := by
      calc ‖ν - ν₀‖ = ‖(a - ν₀) - (a - ν)‖ := by ring_nf
        _ ≤ ‖a - ν₀‖ + ‖a - ν‖ := norm_sub_le _ _
        _ < 2 * ε := by linarith
    linarith
  -- the characteristic polynomial and its derivative, jointly in `(z, ζ)`
  set P : ℂ → ℂ → ℂ := fun z ζ => (X z).charpoly.eval ζ with hP
  set P' : ℂ → ℂ → ℂ := fun z ζ => (derivative (X z).charpoly).eval ζ with hP'
  have hck : ∀ k, DifferentiableOn ℂ (fun z => (X z).charpoly.coeff k) U :=
    differentiableOn_charpoly_coeff hX
  have hPsum : P = fun z ζ => ∑ k ∈ Finset.range (M + 1), (X z).charpoly.coeff k * ζ ^ k := by
    funext z ζ
    exact eval_charpoly_eq_sum (X z) ζ
  have hP'sum : P' = fun z ζ => ∑ k ∈ Finset.range (M + 1),
      (X z).charpoly.coeff (k + 1) * ((k : ℂ) + 1) * ζ ^ k := by
    funext z ζ
    exact eval_derivative_charpoly_eq_sum (X z) ζ
  have hPne : ∀ z ∈ V, ∀ ν ∈ R₀, ∀ ζ ∈ sphere ν ε, P z ζ ≠ 0 := by
    intro z hz ν hν ζ hζ h0
    have hroot : ζ ∈ (X z).charpoly.roots := (mem_roots (charpoly_ne_zero _)).2 h0
    exact hnot z hz ν hν ζ hroot (mem_sphere_iff_norm.1 hζ)
  -- the holomorphic function whose real part is the eigenvalue sum
  set Ψ : ℂ → ℂ → ℂ → ℂ := fun ν z ζ => (P' z ζ / P z ζ) * F ν ζ with hΨ
  set Φ : ℂ → ℂ := fun z => ∑ ν ∈ R₀, (2 * π * I)⁻¹ * ∮ ζ in C(ν, ε), Ψ ν z ζ with hΦ
  have hFd : ∀ ν ∈ R₀, DifferentiableOn ℂ (F ν) (closedBall ν ε) := by
    intro ν hν
    apply ((hFan ν hν).differentiableOn).mono
    exact closedBall_subset_ball (by linarith)
  have hrep : ∀ z ∈ V, ((X z).charpoly.roots.map h).sum = (Φ z).re := by
    intro z hz
    rw [multiset_sum_eq_sum_filter _ R₀ h (hcov z hz)
      (fun c hc c' hc' hne => by have := hsep c hc c' hc' hne; linarith)]
    simp only [hΦ, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro ν hν
    have hA := circleIntegral_logDeriv_charpoly (X z) hε (hnot z hz ν hν) (hFd ν hν)
    have hA' : (2 * π * I)⁻¹ * (∮ ζ in C(ν, ε), Ψ ν z ζ) =
        ((((X z).charpoly.roots.filter fun a => ‖a - ν‖ < ε).map (F ν)).sum) := by
      simp only [hΨ, hP, hP']
      rw [hA, ← mul_assoc, inv_mul_cancel₀ (by simp [Real.pi_ne_zero, I_ne_zero]), one_mul]
    rw [hA', re_multiset_sum]
    congr 1
    apply Multiset.map_congr rfl
    intro a ha
    have ha' : a ∈ ball ν (2 * ε) := by
      rw [mem_ball, dist_eq_norm]
      have := (Multiset.mem_filter.1 ha).2
      linarith
    exact (hFre ν hν ha').symm
  -- holomorphy of `Φ` on `V`
  have hΦd : DifferentiableOn ℂ Φ V := by
    show DifferentiableOn ℂ (fun z => ∑ ν ∈ R₀, (2 * π * I)⁻¹ * ∮ ζ in C(ν, ε), Ψ ν z ζ) V
    apply DifferentiableOn.fun_sum
    intro ν hν
    apply DifferentiableOn.const_mul
    apply differentiableOn_circleIntegral_param hVopen hε
    · -- joint continuity
      have hPc : ContinuousOn (Function.uncurry P) (V ×ˢ sphere ν ε) := by
        rw [hPsum]
        apply continuousOn_finsetSum
        intro k _
        apply ContinuousOn.mul
        · exact ((hck k).continuousOn.mono hVU).comp continuousOn_fst
            (fun p hp => (Set.mem_prod.1 hp).1)
        · exact (continuous_snd.pow k).continuousOn
      have hP'c : ContinuousOn (Function.uncurry P') (V ×ˢ sphere ν ε) := by
        rw [hP'sum]
        apply continuousOn_finsetSum
        intro k _
        apply ContinuousOn.mul
        · apply ContinuousOn.mul _ continuousOn_const
          exact ((hck (k + 1)).continuousOn.mono hVU).comp continuousOn_fst
            (fun p hp => (Set.mem_prod.1 hp).1)
        · exact (continuous_snd.pow k).continuousOn
      have hFc : ContinuousOn (fun p : ℂ × ℂ => F ν p.2) (V ×ˢ sphere ν ε) := by
        apply ((hFd ν hν).continuousOn.mono sphere_subset_closedBall).comp continuousOn_snd
        intro p hp
        exact (Set.mem_prod.1 hp).2
      show ContinuousOn (fun p : ℂ × ℂ => (P' p.1 p.2 / P p.1 p.2) * F ν p.2) (V ×ˢ sphere ν ε)
      apply ContinuousOn.mul _ hFc
      apply ContinuousOn.div hP'c hPc
      intro p hp
      exact hPne p.1 (Set.mem_prod.1 hp).1 ν hν p.2 (Set.mem_prod.1 hp).2
    · -- holomorphy in the parameter
      intro ζ hζ
      show DifferentiableOn ℂ (fun z => (P' z ζ / P z ζ) * F ν ζ) V
      apply DifferentiableOn.mul_const
      apply DifferentiableOn.div
      · simp only [hP'sum]
        apply DifferentiableOn.fun_sum
        intro k _
        exact (((hck (k + 1)).mono hVU).mul_const _).mul_const _
      · simp only [hPsum]
        apply DifferentiableOn.fun_sum
        intro k _
        exact ((hck k).mono hVU).mul_const _
      · intro z hz
        exact hPne z hz ν hν ζ hζ
  have hΦa : AnalyticAt ℂ Φ z₀ := hΦd.analyticAt (hVopen.mem_nhds hz₀V)
  have hharmΦ : InnerProductSpace.HarmonicAt (fun z => (Φ z).re) z₀ := hΦa.harmonicAt_re
  apply (InnerProductSpace.harmonicAt_congr_nhds _).2 hharmΦ
  filter_upwards [hVopen.mem_nhds hz₀V] with z hz
  exact hrep z hz

end OQP27.Cell
