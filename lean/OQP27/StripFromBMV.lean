import OQP27.StripPoisson
import OQP27.StripSpectral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# Theorem 2 (the strip inequality (*) with exact defect) from Theorem 1 (module L3a)

Setting: `B` an orthogonal projection on `ℂ^M`, `P = 1 - B`, `g` Hermitian, `λ` real.  The
eigenvalues of `B + ig` are `(B + I • g).charpoly.roots`, `h_λ` is `hLam` (`OQP27/StripPoisson.lean`),
`Tr[(P(g - λ)P)_+]` is `posPartTrace (P * (g - λ • 1) * P)` (`OQP27/StripSpectral.lean`),
`K_X` is `stripKernel` (`OQP27/StripKernel.lean`), and `D(a, t)` is `stripD`.

Main results (for any density `F : ℝ → ℝ → ℝ`):
* `strip_defect_formula`: under `DensityReg F` and `Hyp_BMV2 B g F`,
  `Σ_{ν ∈ spec(B + ig)} h_λ(ν) - Tr[(P(g - λ)P)_+] = ∫_0^1 ∫_ℝ K_{1-τ}(s - λ) F(s, τ) ds dτ`;
* `strip_inequality`: hence `Tr[(P(g - λ)P)_+] ≤ Σ_ν h_λ(ν)` (the strip inequality (*));
* `strip_equality_iff`: equality holds (for one, equivalently every, `λ`) iff `[B, g] = 0`.

Hypotheses (not proved here):
* `Hyp_BMV2 B g F`: Theorem 1 (2BMV) of the paper, the identity
  `D(a, t) = a² ∫_0^1 ∫_ℝ e^{as - tτ} F(s, τ) ds dτ` for all complex `a, t`.
* `DensityReg F`: measurability, `F ≥ 0`, `F = 0` unless `0 < τ < 1`, compact support in `s`, and
  `F(s, τ) ≤ C/√(τ(1-τ))` (the regularity part of Theorem 1, Lemma 1 of the paper).
For the explicit density `F = OQP27.stripF (1 - B) g` of module L3b, `DensityReg` is proved by L3b
(`measurable_stripF`, `stripF_nonneg`, `stripF_of_not_mem`, `StripL3b.stripF_support`,
`StripL3b.stripF_bound`), and `Hyp_BMV2` is L3b's `StripL3b.bmv2_of_RI_complex` (under `Hyp_RI`)
together with `StripL3b.laplaceF_eq_iterated` and `stripD_eq_sub_pinch`.

Route (paper: `iqoqi/programs/oqp27B_all/Q_2bmv/PROOF.md`, section 5).  Theorem 1 is used at
`(a, t) = (iκ, ∓κ)`, `κ` real, i.e. on the imaginary axis, where Lemma 5 becomes the Fourier
transform of `K_X` (`fourier_stripKernel`).  The function `W` of step (b) and its two integrations
by parts are replaced by the ramp-kernel Fubini argument of `OQP27/StripPoisson.lean`, and the
uniqueness of the Laplace transform by Fourier inversion (`eq_zero_of_fourier_eq_zero`); in
particular no analytic continuation is needed.  The equality case uses the second derivative of
`a ↦ D(a, 0)` at `0` (`commute_of_stripD_zero`) instead of the Duhamel formula of Remark 4.3.
-/

open Real MeasureTheory Set Filter Topology Complex Matrix
open scoped FourierTransform

namespace OQP27.StripL3a

variable {M : ℕ}

/-! ### The hypotheses -/

/-- Regularity of a density `F(s, τ)` on `ℝ × ℝ`: the qualitative part of Theorem 1 of the paper
(Lemma 1 (b), (c)).  For the explicit density `F = OQP27.stripF (1 - B) g` of module L3b these are
`OQP27.measurable_stripF`, `OQP27.stripF_nonneg`, `OQP27.stripF_of_not_mem`,
`OQP27.StripL3b.stripF_support` and `OQP27.StripL3b.stripF_bound`. -/
structure DensityReg (F : ℝ → ℝ → ℝ) : Prop where
  measurable : Measurable (Function.uncurry F)
  nonneg : ∀ s τ, 0 ≤ F s τ
  zero_of_not_mem : ∀ s τ, ¬ (0 < τ ∧ τ < 1) → F s τ = 0
  support : ∃ R : ℝ, 0 < R ∧ ∀ s τ : ℝ, R ≤ |s| → F s τ = 0
  bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ s τ : ℝ, 0 < τ → τ < 1 → F s τ ≤ C / √(τ * (1 - τ))

/-- **Theorem 1 of the paper (2BMV), as a hypothesis**: for all complex `a, t`,
`D(a, t) = a² ∫_0^1 ∫_ℝ e^{as - tτ} F(s, τ) ds dτ`.  Paper proof:
`iqoqi/programs/oqp27B_all/Q_2bmv/PROOF.md`, sections 1-4 (Theorem 1), and the distribution-free
route `iqoqi/programs/oqp27B_all/Q_RI/PROOF.md`, section 4.  For `F = OQP27.stripF (1 - B) g` this is
module L3b's `OQP27.StripL3b.bmv2_of_RI_complex` (under `Hyp_RI`), combined with
`OQP27.StripL3b.laplaceF_eq_iterated` and `stripD_eq_sub_pinch`. -/
def Hyp_BMV2 (B g : Matrix (Fin M) (Fin M) ℂ) (F : ℝ → ℝ → ℝ) : Prop :=
  ∀ a t : ℂ, stripD B g a t
    = a ^ 2 * ∫ τ in (0:ℝ)..1, ∫ s : ℝ, cexp (a * s - t * τ) * (F s τ : ℂ)

/-- The strip balayage of the density onto the left edge,
`V(λ) = ∫_0^1 ∫_ℝ K_{1-τ}(s - λ) F(s, τ) ds dτ` (the defect in Theorem 2). -/
noncomputable def stripBalayage (F : ℝ → ℝ → ℝ) (lam : ℝ) : ℝ :=
  ∫ τ in (0:ℝ)..1, ∫ s : ℝ, stripKernel (1 - τ) (s - lam) * F s τ

/-! ### Integrability of `1/√(τ(1-τ))` and of the density -/

lemma integrableOn_inv_sqrt : IntegrableOn (fun τ : ℝ => 1 / √(τ * (1 - τ))) (Ioo 0 1) := by
  have h := intervalIntegral.integrableOn_deriv_of_nonneg (a := 0) (b := 1)
    (g := fun τ : ℝ => Real.arcsin (2 * τ - 1))
    (g' := fun τ : ℝ => 1 / √(τ * (1 - τ)))
    (Real.continuous_arcsin.comp (by fun_prop)).continuousOn ?_ ?_
  · exact h.mono_set Ioo_subset_Ioc_self
  · intro τ hτ
    have h1 : 2 * τ - 1 ≠ -1 := by linarith [hτ.1]
    have h2 : 2 * τ - 1 ≠ 1 := by linarith [hτ.2]
    have hd := (Real.hasDerivAt_arcsin h1 h2).comp τ ((hasDerivAt_id τ).const_mul 2 |>.sub_const 1)
    refine hd.congr_deriv ?_
    have hpos : 0 < τ * (1 - τ) := mul_pos hτ.1 (by linarith [hτ.2])
    have e : 1 - (2 * τ - 1) ^ 2 = 4 * (τ * (1 - τ)) := by ring
    rw [e, Real.sqrt_mul (by norm_num), show √(4:ℝ) = 2 by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    have hs : 0 < √(τ * (1 - τ)) := Real.sqrt_pos.mpr hpos
    field_simp
  · intro τ hτ
    positivity

/-- The dominating function `τ ↦ C/√(τ(1-τ))` on `(0, 1)`, `0` elsewhere. -/
noncomputable def domFun (C τ : ℝ) : ℝ := Set.indicator (Ioo 0 1) (fun τ => C / √(τ * (1 - τ))) τ

lemma integrable_domFun (C : ℝ) : Integrable (domFun C) := by
  unfold domFun
  rw [integrable_indicator_iff measurableSet_Ioo]
  have := integrableOn_inv_sqrt.const_mul C
  simp only [div_eq_mul_inv, one_mul] at this ⊢
  exact this

lemma domFun_nonneg {C : ℝ} (hC : 0 ≤ C) (τ : ℝ) : 0 ≤ domFun C τ := by
  unfold domFun
  by_cases h : τ ∈ Ioo (0:ℝ) 1
  · rw [Set.indicator_of_mem h]; positivity
  · rw [Set.indicator_of_notMem h]

section Density

variable {F : ℝ → ℝ → ℝ} (hF : DensityReg F)
include hF

lemma DensityReg.le_domFun {C : ℝ} (hC : ∀ s τ : ℝ, 0 < τ → τ < 1 → F s τ ≤ C / √(τ * (1 - τ)))
    (s τ : ℝ) : F s τ ≤ domFun C τ := by
  unfold domFun
  by_cases h : τ ∈ Ioo (0:ℝ) 1
  · rw [Set.indicator_of_mem h]; exact hC s τ h.1 h.2
  · rw [Set.indicator_of_notMem h, hF.zero_of_not_mem s τ (fun h' => h ⟨h'.1, h'.2⟩)]

lemma DensityReg.measurable_section (τ : ℝ) : Measurable (fun s => F s τ) :=
  hF.measurable.comp (measurable_id.prodMk measurable_const)

/-- `F` is integrable on `ℝ × ℝ`. -/
lemma DensityReg.integrable : Integrable (fun q : ℝ × ℝ => F q.1 q.2) := by
  obtain ⟨R, hR, hsupp⟩ := hF.support
  obtain ⟨C, hC0, hC⟩ := hF.bound
  have hdom : Integrable (fun q : ℝ × ℝ => (Set.indicator (Icc (-R) R) (fun _ => (1:ℝ)) q.1)
      * domFun C q.2) (volume.prod volume) :=
    Integrable.mul_prod ((integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (by simp))) (integrable_domFun C)
  rw [← Measure.volume_eq_prod] at hdom
  refine hdom.mono' hF.measurable.aestronglyMeasurable (Eventually.of_forall fun q => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hF.nonneg _ _)]
  by_cases hs : q.1 ∈ Icc (-R) R
  · rw [Set.indicator_of_mem hs, one_mul]; exact hF.le_domFun hC q.1 q.2
  · rw [Set.indicator_of_notMem hs, zero_mul]
    have : R ≤ |q.1| := by
      simp only [mem_Icc, not_and_or, not_le] at hs
      rcases hs with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [hsupp q.1 q.2 this]

/-- Integrability of `e^{as - tτ} F(s, τ)` on `ℝ × ℝ`, for all complex `a, t`. -/
lemma DensityReg.integrable_cexp_mul (a t : ℂ) :
    Integrable (fun q : ℝ × ℝ => cexp (a * q.1 - t * q.2) * (F q.1 q.2 : ℂ)) := by
  obtain ⟨R, hR, hsupp⟩ := hF.support
  refine (hF.integrable.ofReal.const_mul (Real.exp (‖a‖ * R + ‖t‖))).mono'
    ((by fun_prop : Continuous fun q : ℝ × ℝ => cexp (a * q.1 - t * q.2)).aestronglyMeasurable.mul
      (Complex.measurable_ofReal.comp hF.measurable).aestronglyMeasurable)
    (Eventually.of_forall fun q => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hF.nonneg _ _)]
  by_cases hq : F q.1 q.2 = 0
  · rw [hq]; simp
  · have hτ : 0 < q.2 ∧ q.2 < 1 := by
      by_contra h; exact hq (hF.zero_of_not_mem _ _ h)
    have hs : |q.1| < R := by
      by_contra h; exact hq (hsupp _ _ (not_lt.mp h))
    have hn : ‖cexp (a * q.1 - t * q.2)‖ ≤ Real.exp (‖a‖ * R + ‖t‖) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have h1 : (a * q.1 - t * q.2).re ≤ ‖a * q.1 - t * q.2‖ := Complex.re_le_norm _
      have h2 : ‖a * q.1 - t * q.2‖ ≤ ‖a‖ * |q.1| + ‖t‖ * |q.2| := by
        calc ‖a * q.1 - t * q.2‖ ≤ ‖a * q.1‖ + ‖t * q.2‖ := norm_sub_le _ _
          _ = ‖a‖ * |q.1| + ‖t‖ * |q.2| := by
            rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs]
      have h3 : ‖a‖ * |q.1| ≤ ‖a‖ * R := mul_le_mul_of_nonneg_left hs.le (norm_nonneg _)
      have h4 : ‖t‖ * |q.2| ≤ ‖t‖ := by
        rw [abs_of_pos hτ.1]; nlinarith [norm_nonneg t]
      linarith
    exact mul_le_mul_of_nonneg_right hn (hF.nonneg _ _)

/-- The iterated integral `∫_0^1 ∫_ℝ` of Theorem 1 is the integral over `ℝ × ℝ`. -/
lemma DensityReg.iterated_eq_prod (G : ℝ × ℝ → ℂ)
    (hG : Integrable (fun q : ℝ × ℝ => G q * (F q.1 q.2 : ℂ))) :
    ∫ τ in (0:ℝ)..1, ∫ s : ℝ, G (s, τ) * (F s τ : ℂ)
      = ∫ q : ℝ × ℝ, G q * (F q.1 q.2 : ℂ) := by
  rw [Measure.volume_eq_prod] at hG ⊢
  rw [integral_prod_symm _ hG, intervalIntegral.integral_of_le zero_le_one]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro τ hτ
  have hτ' : ¬ (0 < τ ∧ τ < 1) := fun h => hτ ⟨h.1, h.2.le⟩
  simp [hF.zero_of_not_mem _ _ hτ']

end Density


/-! ### The balayage `V` -/

lemma measurable_stripKernel_comp {α : Type*} [MeasurableSpace α] {f g : α → ℝ} (hf : Measurable f)
    (hg : Measurable g) : Measurable (fun x => stripKernel (f x) (g x)) := by
  unfold stripKernel
  fun_prop

lemma stripKernel_le_zero {X : ℝ} (h0 : 0 < X) (h1 : X < 1) (u : ℝ) :
    stripKernel X u ≤ stripKernel X 0 := by
  unfold stripKernel
  have hs := sin_pi_mul_pos h0 h1
  have hd0 := stripKernel_denom_pos h0 h1 0
  have hdu := stripKernel_denom_pos h0 h1 u
  apply div_le_div_of_nonneg_left hs.le (by positivity)
  have : Real.cosh (π * 0) ≤ Real.cosh (π * u) := by
    rw [mul_zero, Real.cosh_zero]; exact Real.one_le_cosh _
  linarith

lemma integral_stripKernel_one_sub_sub {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) (w : ℝ) :
    ∫ s, stripKernel (1 - τ) (s - w) = τ := by
  rw [integral_sub_right_eq_self (fun s => stripKernel (1 - τ) s) w,
    integral_stripKernel (by linarith) (by linarith)]
  ring

lemma integral_stripKernel_one_sub_sub' {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) (s : ℝ) :
    ∫ w, stripKernel (1 - τ) (s - w) = τ := by
  rw [integral_stripKernel_sub (by linarith) (by linarith)]
  ring

/-- The balayage written as an integral over `ℝ × ℝ`. -/
noncomputable def balayageProd (F : ℝ → ℝ → ℝ) (w : ℝ) : ℝ :=
  ∫ q : ℝ × ℝ, stripKernel (1 - q.2) (q.1 - w) * F q.1 q.2

section Balayage

variable {F : ℝ → ℝ → ℝ} (hF : DensityReg F)
include hF

lemma DensityReg.measurable_joint :
    Measurable (fun p : ℝ × (ℝ × ℝ) => stripKernel (1 - p.2.2) (p.2.1 - p.1) * F p.2.1 p.2.2) := by
  have hK : Measurable (fun p : ℝ × (ℝ × ℝ) => stripKernel (1 - p.2.2) (p.2.1 - p.1)) :=
    measurable_stripKernel_comp (measurable_const.sub measurable_snd.snd)
      (measurable_snd.fst.sub measurable_fst)
  exact hK.mul (hF.measurable.comp measurable_snd)

lemma DensityReg.kernel_mul_nonneg (s τ w : ℝ) : 0 ≤ stripKernel (1 - τ) (s - w) * F s τ := by
  by_cases hτ : 0 < τ ∧ τ < 1
  · exact mul_nonneg (stripKernel_pos (X := 1 - τ) (by linarith [hτ.2]) (by linarith [hτ.1]) _).le
      (hF.nonneg _ _)
  · rw [hF.zero_of_not_mem _ _ hτ, mul_zero]

/-- The joint function `(w, (s, τ)) ↦ K_{1-τ}(s - w) F(s, τ)` is integrable. -/
lemma DensityReg.integrable_joint :
    Integrable (fun p : ℝ × (ℝ × ℝ) => stripKernel (1 - p.2.2) (p.2.1 - p.1) * F p.2.1 p.2.2) := by
  rw [Measure.volume_eq_prod]
  rw [integrable_prod_iff' hF.measurable_joint.aestronglyMeasurable]
  constructor
  · refine Eventually.of_forall fun q => ?_
    by_cases hτ : 0 < q.2 ∧ q.2 < 1
    · dsimp only
      exact (integrable_stripKernel_sub (X := 1 - q.2) (by linarith [hτ.2]) (by linarith [hτ.1]) q.1).mul_const _
    · simp [hF.zero_of_not_mem _ _ hτ]
  · have e : (fun q : ℝ × ℝ => ∫ w, ‖stripKernel (1 - q.2) (q.1 - w) * F q.1 q.2‖)
        = fun q => (if 0 < q.2 ∧ q.2 < 1 then q.2 else 0) * F q.1 q.2 := by
      funext q
      by_cases hτ : 0 < q.2 ∧ q.2 < 1
      · rw [if_pos hτ]
        have : (fun w => ‖stripKernel (1 - q.2) (q.1 - w) * F q.1 q.2‖)
            = fun w => stripKernel (1 - q.2) (q.1 - w) * F q.1 q.2 := by
          funext w
          rw [Real.norm_eq_abs, abs_of_nonneg (hF.kernel_mul_nonneg _ _ _)]
        rw [this, integral_mul_const, integral_stripKernel_one_sub_sub' hτ.1 hτ.2]
      · rw [if_neg hτ, hF.zero_of_not_mem _ _ hτ]; simp
    rw [e]
    refine hF.integrable.mono'
      ((Measurable.ite ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_const)) measurable_snd measurable_const).mul
        hF.measurable).aestronglyMeasurable (Eventually.of_forall fun q => ?_)
    rw [Real.norm_eq_abs]
    by_cases hτ : 0 < q.2 ∧ q.2 < 1
    · rw [if_pos hτ, abs_of_nonneg (mul_nonneg hτ.1.le (hF.nonneg _ _))]
      nlinarith [hF.nonneg q.1 q.2, hτ.2]
    · rw [if_neg hτ, zero_mul, abs_zero]; exact hF.nonneg _ _

lemma DensityReg.integrable_balayageProd : Integrable (balayageProd F) := by
  have h := hF.integrable_joint
  rw [Measure.volume_eq_prod] at h
  exact h.integral_prod_left

/-- Fourier transform of the balayage: `∫ e^{iκw} V(w) dw = ∫∫ e^{iκs} sinh(κτ)/sinh κ F(s, τ)`. -/
lemma DensityReg.fourier_balayageProd {κ : ℝ} (hκ : κ ≠ 0) :
    ∫ w : ℝ, cexp (I * κ * w) * (balayageProd F w : ℂ)
      = ∫ q : ℝ × ℝ, cexp (I * κ * q.1) * (sinhRatio (1 - q.2) κ : ℂ) * (F q.1 q.2 : ℂ) := by
  have hJ := hF.integrable_joint
  rw [Measure.volume_eq_prod] at hJ
  have e1 : ∀ w : ℝ, cexp (I * κ * w) * (balayageProd F w : ℂ)
      = ∫ q : ℝ × ℝ, cexp (I * κ * w) * ((stripKernel (1 - q.2) (q.1 - w) * F q.1 q.2 : ℝ) : ℂ) := by
    intro w
    unfold balayageProd
    rw [← integral_complex_ofReal, ← integral_const_mul]
  simp_rw [e1]
  rw [integral_integral_swap]
  · congr 1
    funext q
    by_cases hτ : 0 < q.2 ∧ q.2 < 1
    · have e2 : (fun w : ℝ => cexp (I * κ * w) * ((stripKernel (1 - q.2) (q.1 - w) * F q.1 q.2 : ℝ) : ℂ))
          = fun w : ℝ => cexp (I * κ * w) * (stripKernel (1 - q.2) (q.1 - w) : ℂ) * (F q.1 q.2 : ℂ) := by
        funext w; push_cast; ring
      rw [e2, integral_mul_const,
        fourier_stripKernel_sub (by linarith [hτ.2]) (by linarith [hτ.1]) q.1 hκ]
    · simp [hF.zero_of_not_mem _ _ hτ]
  · refine (hJ.ofReal (𝕜 := ℂ)).bdd_mul (c := 1)
      ((by fun_prop : Continuous fun p : ℝ × (ℝ × ℝ) => cexp (I * κ * p.1)).aestronglyMeasurable)
      (Eventually.of_forall fun p => ?_)
    rw [Complex.norm_exp]; simp

/-- For fixed `w`, the function `(s, τ) ↦ K_{1-τ}(s - w) F(s, τ)` is integrable. -/
lemma DensityReg.integrable_section (w : ℝ) :
    Integrable (fun q : ℝ × ℝ => stripKernel (1 - q.2) (q.1 - w) * F q.1 q.2) := by
  obtain ⟨C, hC0, hC⟩ := hF.bound
  have hmeas : Measurable (fun q : ℝ × ℝ => stripKernel (1 - q.2) (q.1 - w) * F q.1 q.2) :=
    (measurable_stripKernel_comp (measurable_const.sub measurable_snd)
      (measurable_fst.sub measurable_const)).mul hF.measurable
  rw [Measure.volume_eq_prod, integrable_prod_iff' hmeas.aestronglyMeasurable]
  have hsec : ∀ τ : ℝ, ∫ s : ℝ, ‖stripKernel (1 - τ) (s - w) * F s τ‖ ≤ domFun C τ := by
    intro τ
    by_cases hτ : 0 < τ ∧ τ < 1
    · have hK : ∀ s, 0 ≤ stripKernel (1 - τ) (s - w) :=
        fun s => (stripKernel_pos (X := 1 - τ) (by linarith [hτ.2]) (by linarith [hτ.1]) _).le
      have hint : Integrable (fun s : ℝ => stripKernel (1 - τ) (s - w) * domFun C τ) :=
        ((integrable_stripKernel (X := 1 - τ) (by linarith [hτ.2]) (by linarith [hτ.1])).comp_sub_right w).mul_const _
      calc ∫ s : ℝ, ‖stripKernel (1 - τ) (s - w) * F s τ‖
          ≤ ∫ s : ℝ, stripKernel (1 - τ) (s - w) * domFun C τ := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun s => norm_nonneg _) hint
              (Eventually.of_forall fun s => ?_)
            dsimp only
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hK s) (hF.nonneg _ _))]
            exact mul_le_mul_of_nonneg_left (hF.le_domFun hC s τ) (hK s)
        _ = τ * domFun C τ := by rw [integral_mul_const, integral_stripKernel_one_sub_sub hτ.1 hτ.2]
        _ ≤ domFun C τ := by nlinarith [domFun_nonneg hC0 τ, hτ.2]
    · simp [hF.zero_of_not_mem _ _ hτ, domFun_nonneg hC0 τ]
  constructor
  · refine Eventually.of_forall fun τ => ?_
    by_cases hτ : 0 < τ ∧ τ < 1
    · refine (((integrable_stripKernel (X := 1 - τ) (by linarith [hτ.2]) (by linarith [hτ.1])).comp_sub_right
        w).mul_const (domFun C τ)).mono' (hmeas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
        (Eventually.of_forall fun s => ?_)
      have hK := (stripKernel_pos (X := 1 - τ) (by linarith [hτ.2]) (by linarith [hτ.1]) (s - w)).le
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hK (hF.nonneg _ _))]
      exact mul_le_mul_of_nonneg_left (hF.le_domFun hC s τ) hK
    · simp [hF.zero_of_not_mem _ _ hτ]
  · refine (integrable_domFun C).mono' ?_ (Eventually.of_forall fun τ => ?_)
    · exact (hmeas.norm.comp measurable_swap).aestronglyMeasurable.integral_prod_right'
    · rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun s => norm_nonneg _)]
      exact hsec τ

/-- The iterated form of `V` equals the product form. -/
lemma DensityReg.stripBalayage_eq (w : ℝ) : stripBalayage F w = balayageProd F w := by
  have h := hF.integrable_section w
  unfold stripBalayage balayageProd
  rw [Measure.volume_eq_prod] at h ⊢
  rw [integral_prod_symm _ h, intervalIntegral.integral_of_le zero_le_one]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro τ hτ
  have hτ' : ¬ (0 < τ ∧ τ < 1) := fun h => hτ ⟨h.1, h.2.le⟩
  simp [hF.zero_of_not_mem _ _ hτ']

lemma DensityReg.stripBalayage_nonneg (w : ℝ) : 0 ≤ stripBalayage F w := by
  unfold stripBalayage
  refine intervalIntegral.integral_nonneg zero_le_one (fun τ _ => ?_)
  exact integral_nonneg fun s => hF.kernel_mul_nonneg s τ w

/-- `V` is continuous. -/
lemma DensityReg.continuous_stripBalayage : Continuous (stripBalayage F) := by
  obtain ⟨R, hR, hsupp⟩ := hF.support
  obtain ⟨C, hC0, hC⟩ := hF.bound
  have e : stripBalayage F = fun w => ∫ τ in Ioc (0:ℝ) 1, ∫ s : ℝ,
      stripKernel (1 - τ) (s - w) * F s τ := by
    funext w; unfold stripBalayage; rw [intervalIntegral.integral_of_le zero_le_one]
  rw [e]
  refine continuous_of_dominated (bound := domFun C) (fun w => ?_) (fun w => ?_)
    (integrable_domFun C).integrableOn ?_
  · have hmeas : Measurable (fun q : ℝ × ℝ => stripKernel (1 - q.1) (q.2 - w) * F q.2 q.1) :=
      (measurable_stripKernel_comp (measurable_const.sub measurable_fst)
        (measurable_snd.sub measurable_const)).mul
        (hF.measurable.comp measurable_swap)
    exact hmeas.aestronglyMeasurable.integral_prod_right'.restrict
  · refine Eventually.of_forall fun τ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun s => hF.kernel_mul_nonneg s τ w)]
    by_cases hτ : 0 < τ ∧ τ < 1
    · have hK : ∀ s, 0 ≤ stripKernel (1 - τ) (s - w) :=
        fun s => (stripKernel_pos (X := 1 - τ) (by linarith [hτ.2]) (by linarith [hτ.1]) _).le
      have hint : Integrable (fun s : ℝ => stripKernel (1 - τ) (s - w) * domFun C τ) :=
        ((integrable_stripKernel (X := 1 - τ) (by linarith [hτ.2]) (by linarith [hτ.1])).comp_sub_right w).mul_const _
      calc ∫ s : ℝ, stripKernel (1 - τ) (s - w) * F s τ
          ≤ ∫ s : ℝ, stripKernel (1 - τ) (s - w) * domFun C τ := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun s => hF.kernel_mul_nonneg s τ w)
              hint (Eventually.of_forall fun s => ?_)
            exact mul_le_mul_of_nonneg_left (hF.le_domFun hC s τ) (hK s)
        _ = τ * domFun C τ := by rw [integral_mul_const, integral_stripKernel_one_sub_sub hτ.1 hτ.2]
        _ ≤ domFun C τ := by nlinarith [domFun_nonneg hC0 τ, hτ.2]
    · simp [hF.zero_of_not_mem _ _ hτ, domFun_nonneg hC0 τ]
  · refine Eventually.of_forall fun τ => ?_
    by_cases hτ : 0 < τ ∧ τ < 1
    · have h0 : 0 < 1 - τ := by linarith [hτ.2]
      have h1 : 1 - τ < 1 := by linarith [hτ.1]
      have hFint : Integrable (fun s => F s τ) := by
        refine ((integrable_indicator_iff measurableSet_Icc).mpr
          (integrableOn_const (μ := volume) (s := Icc (-R) R) (C := domFun C τ) (by simp))).mono'
          (hF.measurable_section τ).aestronglyMeasurable (Eventually.of_forall fun s => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (hF.nonneg _ _)]
        by_cases hs : s ∈ Icc (-R) R
        · rw [Set.indicator_of_mem hs]; exact hF.le_domFun hC s τ
        · rw [Set.indicator_of_notMem hs]
          have : R ≤ |s| := by
            simp only [mem_Icc, not_and_or, not_le] at hs
            rcases hs with h | h
            · rw [abs_of_neg (by linarith)]; linarith
            · rw [abs_of_pos (by linarith)]; linarith
          rw [hsupp s τ this]
      refine continuous_of_dominated (bound := fun s => stripKernel (1 - τ) 0 * F s τ)
        (fun w => ?_) (fun w => Eventually.of_forall fun s => ?_) (hFint.const_mul _)
        (Eventually.of_forall fun s => ?_)
      · exact (((continuous_stripKernel h0 h1).comp
          (continuous_id.sub continuous_const)).measurable.mul
          (hF.measurable_section τ)).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (stripKernel_pos h0 h1 _).le (hF.nonneg _ _))]
        exact mul_le_mul_of_nonneg_right (stripKernel_le_zero h0 h1 _) (hF.nonneg _ _)
      · exact ((continuous_stripKernel h0 h1).comp (continuous_const.sub continuous_id)).mul
          continuous_const
    · simp only [hF.zero_of_not_mem _ _ hτ, mul_zero, integral_zero]
      exact continuous_const

end Balayage


/-! ### Theorem 2 -/

section Theorem2

variable {B g : Matrix (Fin M) (Fin M) ℂ} {F : ℝ → ℝ → ℝ}

lemma sinh_mul_one_sub_eq {κ : ℝ} (hκ : κ ≠ 0) (x : ℝ) :
    Real.sinh (κ * (1 - x)) = Real.sinh κ * sinhRatio x κ := by
  rw [sinhRatio_of_ne hκ]
  have hs : Real.sinh κ ≠ 0 := by simpa using hκ
  field_simp

/-- Step (a) of the proof of Theorem 2 on the imaginary axis: with `ρ̂(κ) = Σ_ν e^{iκ Im ν}
sinh(κ(1 - Re ν))/sinh κ` and `σ̂(κ) = Σ_j p_j e^{iκ d_j}`, Theorem 1 at `(a, t) = (iκ, ∓κ)` gives
`ρ̂(κ) - σ̂(κ) = -κ² ∫∫ e^{iκs} sinh(κτ)/sinh(κ) F(s, τ) ds dτ`. -/
lemma rhohat_sub_sigmahat (hB : B.IsHermitian ∧ B * B = B) (hg : g.IsHermitian)
    (hF : DensityReg F) (hBMV : Hyp_BMV2 B g F) {U : Matrix (Fin M) (Fin M) ℂ} {d p : Fin M → ℝ}
    (hU : U ∈ unitaryGroup (Fin M) ℂ) (hP : 1 - B = U * diagonal (fun j => (p j : ℂ)) * star U)
    (hQ : (1 - B) * g * (1 - B) = U * diagonal (fun j => (d j : ℂ)) * star U)
    {κ : ℝ} (hκ : κ ≠ 0) :
    ((B + I • g).charpoly.roots.map (fun ν => cexp (I * κ * ν.im) * (sinhRatio ν.re κ : ℂ))).sum
        - ∑ j, (p j : ℂ) * cexp (I * κ * d j)
      = -(κ : ℂ) ^ 2 * ∫ q : ℝ × ℝ,
          cexp (I * κ * q.1) * (sinhRatio (1 - q.2) κ : ℂ) * (F q.1 q.2 : ℂ) := by
  have hs : (Real.sinh κ : ℂ) ≠ 0 := by
    have : Real.sinh κ ≠ 0 := by simpa using hκ
    exact_mod_cast this
  -- Theorem 1 at (iκ, -κ) and (iκ, κ), as integrals over ℝ × ℝ
  have hprod : ∀ t : ℂ, ∫ τ in (0:ℝ)..1, ∫ s : ℝ, cexp (I * κ * s - t * τ) * (F s τ : ℂ)
      = ∫ q : ℝ × ℝ, cexp (I * κ * q.1 - t * q.2) * (F q.1 q.2 : ℂ) := by
    intro t
    have h := hF.iterated_eq_prod (fun q : ℝ × ℝ => cexp (I * κ * q.1 - t * q.2))
      (hF.integrable_cexp_mul (I * κ) t)
    exact h
  have h1 := hBMV (I * κ) (-(κ : ℂ))
  have h2 := hBMV (I * κ) κ
  rw [hprod] at h1 h2
  have hD := stripD_sub_eq hB hg hU hP hQ κ
  rw [h1, h2, ← mul_sub, ← integral_sub (hF.integrable_cexp_mul _ _)
    (hF.integrable_cexp_mul _ _)] at hD
  -- rewrite the integrand: e^{iκs + κτ} - e^{iκs - κτ} = 2 sinh κ e^{iκs} sinhRatio(1-τ) κ
  have hint : ∀ q : ℝ × ℝ, cexp (I * κ * q.1 - -(κ : ℂ) * q.2) * (F q.1 q.2 : ℂ)
      - cexp (I * κ * q.1 - (κ : ℂ) * q.2) * (F q.1 q.2 : ℂ)
      = (2 * (Real.sinh κ : ℂ)) * (cexp (I * κ * q.1) * (sinhRatio (1 - q.2) κ : ℂ)
          * (F q.1 q.2 : ℂ)) := by
    intro q
    have e1 : (2 * (Real.sinh κ : ℂ)) * (sinhRatio (1 - q.2) κ : ℂ)
        = 2 * (Real.sinh (κ * q.2) : ℂ) := by
      have := sinh_mul_one_sub_eq hκ (1 - q.2)
      rw [show κ * (1 - (1 - q.2)) = κ * q.2 by ring] at this
      rw [this]; push_cast; ring
    have e2 : 2 * (Real.sinh (κ * q.2) : ℂ) = cexp (κ * q.2) - cexp (-(κ * q.2)) := by
      rw [Complex.ofReal_sinh, Complex.sinh]; push_cast; ring
    have e3 : cexp (I * κ * q.1 - -(κ : ℂ) * q.2) = cexp (I * κ * q.1) * cexp (κ * q.2) := by
      rw [← Complex.exp_add]; ring_nf
    have e4 : cexp (I * κ * q.1 - (κ : ℂ) * q.2) = cexp (I * κ * q.1) * cexp (-(κ * q.2)) := by
      rw [← Complex.exp_add]; ring_nf
    calc cexp (I * κ * q.1 - -(κ : ℂ) * q.2) * (F q.1 q.2 : ℂ)
          - cexp (I * κ * q.1 - (κ : ℂ) * q.2) * (F q.1 q.2 : ℂ)
        = cexp (I * κ * q.1) * (cexp (κ * q.2) - cexp (-(κ * q.2))) * (F q.1 q.2 : ℂ) := by
          rw [e3, e4]; ring
      _ = cexp (I * κ * q.1) * ((2 * (Real.sinh κ : ℂ)) * (sinhRatio (1 - q.2) κ : ℂ))
            * (F q.1 q.2 : ℂ) := by rw [e1, e2]
      _ = _ := by ring
  simp_rw [hint] at hD
  rw [integral_const_mul] at hD
  -- matrix side in terms of sinhRatio
  have hmat : ((B + I • g).charpoly.roots.map
      (fun ν => cexp (I * κ * ν.im) * (2 * (Real.sinh (κ * (1 - ν.re)) : ℂ)))).sum
      = (2 * (Real.sinh κ : ℂ)) * ((B + I • g).charpoly.roots.map
          (fun ν => cexp (I * κ * ν.im) * (sinhRatio ν.re κ : ℂ))).sum := by
    rw [← Multiset.sum_map_mul_left]
    congr 1
    refine Multiset.map_congr rfl (fun ν _ => ?_)
    rw [sinh_mul_one_sub_eq hκ]; push_cast; ring
  rw [hmat] at hD
  -- cancel 2 sinh κ
  have h2s : (2 * (Real.sinh κ : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hs
  apply mul_left_cancel₀ h2s
  rw [mul_sub, ← hD, mul_pow, Complex.I_sq]
  push_cast
  ring

/-- **Theorem 2 (the strip inequality (*) with its exact defect), assuming Theorem 1.**
For a projection `B`, `P = 1 - B`, Hermitian `g`, real `λ`, and any density `F` satisfying the
regularity of Theorem 1 (`DensityReg`) and the 2BMV identity of Theorem 1 (`Hyp_BMV2`):
`Σ_{ν ∈ spec(B + ig)} h_λ(ν) - Tr[(P(g - λ)P)_+] = ∫_0^1 ∫_ℝ K_{1-τ}(s - λ) F(s, τ) ds dτ`. -/
theorem strip_defect_formula (hB : B.IsHermitian ∧ B * B = B) (hg : g.IsHermitian)
    (hF : DensityReg F) (hBMV : Hyp_BMV2 B g F) (lam : ℝ) :
    ((B + I • g).charpoly.roots.map (hLam lam)).sum
      - posPartTrace ((1 - B) * (g - (lam : ℂ) • 1) * (1 - B)) = stripBalayage F lam := by
  obtain ⟨U, d, p, hU, hp01, hpd, hP, hQ⟩ := exists_compression_basis hB hg
  set S := (B + I • g).charpoly.roots with hSdef
  have hS : ∀ ν ∈ S, 0 ≤ ν.re ∧ ν.re ≤ 1 := fun ν hν => re_mem_Icc_of_mem_roots hB hg hν
  obtain ⟨hmass, hmom⟩ := mass_moment_eq hB hg hU hpd hp01 hP hQ
  have hL : ∀ lam' : ℝ, (S.map (hLam lam')).sum
      - posPartTrace ((1 - B) * (g - (lam' : ℂ) • 1) * (1 - B)) = poissonDefect S d p lam' := by
    intro lam'
    rw [posPartTrace_compress_eq hB hg hU hp01 hpd hP hQ lam']
    rfl
  rw [hL]
  have hΨ : poissonDefect S d p = rampDefect S d p :=
    funext (poissonDefect_eq_rampDefect S hS d p hmass hmom)
  have hV : stripBalayage F = balayageProd F := funext hF.stripBalayage_eq
  have key : (fun w : ℝ => ((poissonDefect S d p w - stripBalayage F w : ℝ) : ℂ)) = 0 := by
    apply eq_zero_of_fourier_eq_zero
    · exact Complex.continuous_ofReal.comp
        ((continuous_poissonDefect S d p).sub hF.continuous_stripBalayage)
    · rw [hΨ, hV]
      exact ((integrable_rampDefect S d p).sub hF.integrable_balayageProd).ofReal
    · intro κ hκ
      have hbdd : ∀ G : ℝ → ℂ, Integrable G →
          Integrable (fun w : ℝ => cexp (I * κ * w) * G w) := by
        intro G hG
        refine hG.bdd_mul (c := 1)
          ((by fun_prop : Continuous fun w : ℝ => cexp (I * κ * w)).aestronglyMeasurable)
          (Eventually.of_forall fun w => ?_)
        rw [Complex.norm_exp]; simp
      have e : (fun w : ℝ => cexp (I * κ * w) * (((poissonDefect S d p w - stripBalayage F w : ℝ)) : ℂ))
          = fun w : ℝ => cexp (I * κ * w) * (rampDefect S d p w : ℂ)
              - cexp (I * κ * w) * (balayageProd F w : ℂ) := by
        funext w; rw [hΨ, hV]; push_cast; ring
      have i1 : Integrable (fun w : ℝ => cexp (I * κ * w) * (rampDefect S d p w : ℂ)) :=
        hbdd _ (integrable_rampDefect S d p).ofReal
      have i2 : Integrable (fun w : ℝ => cexp (I * κ * w) * (balayageProd F w : ℂ)) :=
        hbdd _ hF.integrable_balayageProd.ofReal
      rw [e, integral_sub i1 i2,
        fourier_rampDefect S hS d p hmass hmom hκ, hF.fourier_balayageProd hκ,
        rhohat_sub_sigmahat hB hg hF hBMV hU hP hQ hκ]
      have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ
      field_simp
      ring
  have h := congrFun key lam
  simp only [Pi.zero_apply, Complex.ofReal_eq_zero, sub_eq_zero] at h
  exact h

/-- `V(λ) ≥ 0`: the strip inequality (*). -/
theorem strip_inequality (hB : B.IsHermitian ∧ B * B = B) (hg : g.IsHermitian)
    (hF : DensityReg F) (hBMV : Hyp_BMV2 B g F) (lam : ℝ) :
    posPartTrace ((1 - B) * (g - (lam : ℂ) • 1) * (1 - B))
      ≤ ((B + I • g).charpoly.roots.map (hLam lam)).sum := by
  have h := strip_defect_formula hB hg hF hBMV lam
  have h0 := hF.stripBalayage_nonneg lam
  linarith

/-- If `V(λ) = 0` for one `λ`, then `F = 0` almost everywhere. -/
lemma DensityReg.ae_zero_of_stripBalayage_eq_zero (hF : DensityReg F) {lam : ℝ}
    (h : stripBalayage F lam = 0) : (fun q : ℝ × ℝ => F q.1 q.2) =ᵐ[volume] 0 := by
  rw [hF.stripBalayage_eq] at h
  unfold balayageProd at h
  have hnn : 0 ≤ fun q : ℝ × ℝ => stripKernel (1 - q.2) (q.1 - lam) * F q.1 q.2 :=
    fun q => hF.kernel_mul_nonneg q.1 q.2 lam
  have hae := (integral_eq_zero_iff_of_nonneg hnn (hF.integrable_section lam)).mp h
  filter_upwards [hae] with q hq
  simp only [Pi.zero_apply] at hq ⊢
  by_cases hτ : 0 < q.2 ∧ q.2 < 1
  · have hK := stripKernel_pos (X := 1 - q.2) (by linarith [hτ.2]) (by linarith [hτ.1]) (q.1 - lam)
    rcases mul_eq_zero.mp hq with h' | h'
    · linarith
    · exact h'
  · exact hF.zero_of_not_mem _ _ hτ

/-- If `F = 0` almost everywhere then `V ≡ 0`. -/
lemma DensityReg.stripBalayage_eq_zero_of_ae (hF : DensityReg F)
    (h : (fun q : ℝ × ℝ => F q.1 q.2) =ᵐ[volume] 0) (lam : ℝ) : stripBalayage F lam = 0 := by
  rw [hF.stripBalayage_eq]
  unfold balayageProd
  apply integral_eq_zero_of_ae
  filter_upwards [h] with q hq
  simp only [Pi.zero_apply] at hq ⊢
  rw [hq, mul_zero]

/-- **Equality case of Theorem 2**: equality in (*) holds for some (equivalently every) `λ` iff
`[B, g] = 0`. -/
theorem strip_equality_iff (hB : B.IsHermitian ∧ B * B = B) (hg : g.IsHermitian)
    (hF : DensityReg F) (hBMV : Hyp_BMV2 B g F) (lam : ℝ) :
    ((B + I • g).charpoly.roots.map (hLam lam)).sum
      = posPartTrace ((1 - B) * (g - (lam : ℂ) • 1) * (1 - B)) ↔ Commute B g := by
  have hdef := strip_defect_formula hB hg hF hBMV lam
  constructor
  · intro heq
    have hV : stripBalayage F lam = 0 := by linarith
    have hae := hF.ae_zero_of_stripBalayage_eq_zero hV
    refine commute_of_stripD_zero hB hg (fun a => ?_)
    rw [hBMV a 0]
    have hp := hF.iterated_eq_prod (fun q : ℝ × ℝ => cexp (a * q.1 - 0 * q.2))
      (hF.integrable_cexp_mul a 0)
    have hz : ∫ q : ℝ × ℝ, cexp (a * q.1 - 0 * q.2) * (F q.1 q.2 : ℂ) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hae] with q hq
      simp only [Pi.zero_apply] at hq ⊢
      rw [hq, Complex.ofReal_zero, mul_zero]
    have hp' : ∫ τ in (0:ℝ)..1, ∫ s : ℝ, cexp (a * s - 0 * τ) * (F s τ : ℂ) = 0 := by
      have hp2 : ∫ τ in (0:ℝ)..1, ∫ s : ℝ, cexp (a * s - 0 * τ) * (F s τ : ℂ)
          = ∫ q : ℝ × ℝ, cexp (a * q.1 - 0 * q.2) * (F q.1 q.2 : ℂ) := hp
      rw [hp2, hz]
    rw [hp', mul_zero]
  · intro hc
    have hD := stripD_zero_of_commute hB hg hc 1
    rw [hBMV 1 0] at hD
    have hp := hF.iterated_eq_prod (fun q : ℝ × ℝ => cexp (1 * q.1 - 0 * q.2))
      (hF.integrable_cexp_mul 1 0)
    have hp' : ∫ τ in (0:ℝ)..1, ∫ s : ℝ, cexp (1 * s - 0 * τ) * (F s τ : ℂ)
        = ∫ q : ℝ × ℝ, cexp (1 * q.1 - 0 * q.2) * (F q.1 q.2 : ℂ) := hp
    rw [hp', one_pow, one_mul] at hD
    -- the real integral ∫ e^s F vanishes
    have hre : ∫ q : ℝ × ℝ, Real.exp q.1 * F q.1 q.2 = 0 := by
      have e : (fun q : ℝ × ℝ => cexp (1 * q.1 - 0 * q.2) * (F q.1 q.2 : ℂ))
          = fun q => ((Real.exp q.1 * F q.1 q.2 : ℝ) : ℂ) := by
        funext q; push_cast; ring_nf
      rw [e, integral_complex_ofReal] at hD
      exact_mod_cast hD
    have hint : Integrable (fun q : ℝ × ℝ => Real.exp q.1 * F q.1 q.2) := by
      have h := (hF.integrable_cexp_mul 1 0).norm
      refine h.congr (Eventually.of_forall fun q => ?_)
      simp only [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hF.nonneg _ _)]
      simp
    have hnn : 0 ≤ fun q : ℝ × ℝ => Real.exp q.1 * F q.1 q.2 :=
      fun q => mul_nonneg (Real.exp_pos _).le (hF.nonneg _ _)
    have hae := (integral_eq_zero_iff_of_nonneg hnn hint).mp hre
    have hae' : (fun q : ℝ × ℝ => F q.1 q.2) =ᵐ[volume] 0 := by
      filter_upwards [hae] with q hq
      simp only [Pi.zero_apply] at hq ⊢
      rcases mul_eq_zero.mp hq with h' | h'
      · exact absurd h' (Real.exp_pos _).ne'
      · exact h'
    have hV := hF.stripBalayage_eq_zero_of_ae hae' lam
    linarith

end Theorem2

end OQP27.StripL3a
