import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Logarithmic potentials on the real line and the Jensen-type identity (module L3b)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

Proved here (no hypotheses, no `sorry`):
* `integral_log_norm_sub`: `∫_{-L}^{L} log |x - z| dx = Φ_L(z)` in closed form (`logPot`), for every `z ∈ ℂ`;
* `tendsto_logPot`: `Φ_L(z) - (2 L log L - 2 L) → π |Im z|` as `L → ∞`;
* `integral_log_norm_eval`, `tendsto_integral_log_norm_eval`: for a nonzero complex polynomial `p` of
  degree `n` with leading coefficient `c`,
  `∫_{-L}^{L} log |p(x)| dx - 2 L log |c| - n (2 L log L - 2 L) → π ∑_{roots} |Im z|`
  (this gives the measurability of the density `F`, see `OQP27.StripL3b.measurable_stripF`);
* `jensen_identity` (**Lemma 2**): if `p`, `q` have the same degree and the same leading coefficient,
  all roots of `q` are real and the roots of `p` and `q` have the same sum, then `log |p/q|` is
  integrable on `ℝ` and `∫_ℝ log |p(x)/q(x)| dx = π ∑_i |Im x_i|`.

No hypotheses remain in this file.
Paper: `iqoqi/programs/oqp27B_all/Q_2bmv/PROOF.md`, Lemma 2 (section 1).
-/

namespace OQP27.StripL3b

open Real MeasureTheory Filter Topology intervalIntegral

/-- Closed form of `∫_{-L}^{L} log |x - z| dx` (see `integral_log_norm_sub`). -/
noncomputable def logPot (L : ℝ) (z : ℂ) : ℝ :=
  (L - z.re) * Real.log ‖(L : ℂ) - z‖ + (L + z.re) * Real.log ‖(L : ℂ) + z‖ - 2 * L
    + z.im * (Real.arctan ((L - z.re) / z.im) + Real.arctan ((L + z.re) / z.im))

lemma log_norm_ofReal_sub (x : ℝ) (z : ℂ) :
    Real.log ‖(x : ℂ) - z‖ = Real.log ((x - z.re) ^ 2 + z.im ^ 2) / 2 := by
  have h : ‖(x : ℂ) - z‖ = √((x - z.re) ^ 2 + z.im ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    congr 1
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im]
    ring
  rw [h, Real.log_sqrt (by positivity)]

lemma integral_log_norm_sub (L : ℝ) (z : ℂ) :
    ∫ x in (-L)..L, Real.log ‖(x : ℂ) - z‖ = logPot L z := by
  by_cases hb : z.im = 0
  · -- real point: reduce to `integral_log`
    have hz : z = (z.re : ℂ) := by
      apply Complex.ext <;> simp [hb]
    have hfun : (fun x : ℝ => Real.log ‖(x : ℂ) - z‖) = fun x => Real.log (x - z.re) := by
      funext x
      rw [hz, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Real.log_abs]
      simp
    rw [hfun, intervalIntegral.integral_comp_sub_right (fun x => Real.log x), integral_log]
    unfold logPot
    rw [hb, zero_mul, add_zero]
    have h1 : ‖(L : ℂ) - z‖ = |L - z.re| := by
      rw [hz, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      simp
    have h2 : ‖(L : ℂ) + z‖ = |L + z.re| := by
      rw [hz, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
      simp
    rw [h1, h2, Real.log_abs, Real.log_abs]
    have h3 : Real.log (-L - z.re) = Real.log (L + z.re) := by
      rw [show -L - z.re = -(L + z.re) by ring, Real.log_neg_eq_log]
    rw [h3]
    ring
  · -- non-real point: explicit antiderivative
    set α := z.re
    set β := z.im
    let G : ℝ → ℝ := fun x =>
      (x - α) * (Real.log ((x - α) ^ 2 + β ^ 2) / 2) - x + β * Real.arctan ((x - α) / β)
    have hpos : ∀ x : ℝ, 0 < (x - α) ^ 2 + β ^ 2 := fun x => by positivity
    have hderiv : ∀ x : ℝ, HasDerivAt G (Real.log ((x - α) ^ 2 + β ^ 2) / 2) x := by
      intro x
      have h1 : HasDerivAt (fun x : ℝ => (x - α) ^ 2 + β ^ 2) (2 * (x - α)) x := by
        have := ((hasDerivAt_id x).sub_const α).pow 2
        simpa using this.add_const (β ^ 2)
      have h2 := (h1.log (hpos x).ne').div_const 2
      have h3 := ((hasDerivAt_id' x).sub_const α).mul h2
      have h4 := (((hasDerivAt_id' x).sub_const α).div_const β).arctan
      have h5 := (h3.sub (hasDerivAt_id' x)).add (h4.const_mul β)
      refine h5.congr_deriv ?_
      have hq : (x - α) ^ 2 + β ^ 2 ≠ 0 := (hpos x).ne'
      have hq2 : 1 + ((x - α) / β) ^ 2 ≠ 0 := by positivity
      field_simp
      ring
    have hcont : Continuous fun x : ℝ => Real.log ((x - α) ^ 2 + β ^ 2) / 2 := by
      have : Continuous fun x : ℝ => (x - α) ^ 2 + β ^ 2 := by fun_prop
      exact (this.log fun x => (hpos x).ne').div_const 2
    have hfun : (fun x : ℝ => Real.log ‖(x : ℂ) - z‖)
        = fun x => Real.log ((x - α) ^ 2 + β ^ 2) / 2 := by
      funext x; exact log_norm_ofReal_sub x z
    rw [hfun, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
      (hcont.intervalIntegrable _ _)]
    unfold logPot
    rw [log_norm_ofReal_sub L z]
    have h6 : Real.log ‖(L : ℂ) + z‖ = Real.log ((-L - α) ^ 2 + β ^ 2) / 2 := by
      have : (L : ℂ) + z = -(((-L : ℝ) : ℂ) - z) := by push_cast; ring
      rw [this, norm_neg, log_norm_ofReal_sub]
    rw [h6]
    simp only [G]
    have h7 : (-L - α) / β = -((L + α) / β) := by ring
    rw [h7, Real.arctan_neg]
    ring

/-- `(L + Re w) (log |L + w| - log L) → Re w` as `L → ∞`. -/
lemma tendsto_mul_log_norm_add (w : ℂ) :
    Tendsto (fun L : ℝ => (L + w.re) * (Real.log ‖(L : ℂ) + w‖ - Real.log L)) atTop
      (𝓝 w.re) := by
  set g : ℝ → ℝ := fun L => 2 * w.re / L + Complex.normSq w / L ^ 2 with hg_def
  have hg : Tendsto (fun L : ℝ => L * g L) atTop (𝓝 (2 * w.re)) := by
    have h0 : Tendsto (fun L : ℝ => 2 * w.re + Complex.normSq w / L) atTop
        (𝓝 (2 * w.re + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
    rw [add_zero] at h0
    refine h0.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with L hL
    simp only [hg_def]
    field_simp
  have hlog := Real.tendsto_mul_log_one_add_of_tendsto hg
  have hlim : Tendsto (fun L : ℝ => (1 + w.re / L) * ((1 / 2) * (L * Real.log (1 + g L))))
      atTop (𝓝 ((1 + 0) * ((1 / 2) * (2 * w.re)))) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)).mul
      (tendsto_const_nhds.mul hlog)
  have h12 : (1 + (0 : ℝ)) * ((1 / 2) * (2 * w.re)) = w.re := by ring
  rw [h12] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop ‖w‖] with L hL
  have hL0 : 0 < L := lt_of_le_of_lt (norm_nonneg w) hL
  have hne : (L : ℂ) + w ≠ 0 := by
    intro h
    have h' : ‖(L : ℂ)‖ = ‖w‖ := by
      rw [show (L : ℂ) = -w by linear_combination h, norm_neg]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL0] at h'
    linarith
  have hsq : ‖(L : ℂ) + w‖ ^ 2 = L ^ 2 * (1 + g L) := by
    simp only [hg_def]
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.ofReal_re, Complex.add_im,
      Complex.ofReal_im, zero_add]
    field_simp
    ring
  have h1g : 1 + g L ≠ 0 := by
    intro h
    rw [h, mul_zero] at hsq
    exact hne (norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq))
  have hkey : Real.log ‖(L : ℂ) + w‖ - Real.log L = (1 / 2) * Real.log (1 + g L) := by
    have h1 : Real.log (‖(L : ℂ) + w‖ ^ 2) = 2 * Real.log ‖(L : ℂ) + w‖ := by
      rw [Real.log_pow]; norm_num
    have h2 : Real.log (‖(L : ℂ) + w‖ ^ 2) = 2 * Real.log L + Real.log (1 + g L) := by
      rw [hsq, Real.log_mul (by positivity) h1g, Real.log_pow]; norm_num
    linarith
  rw [hkey]
  field_simp

/-- **Asymptotics of the logarithmic potential**:
`∫_{-L}^{L} log |x - z| dx - (2 L log L - 2 L) → π |Im z|` as `L → ∞`. -/
theorem tendsto_logPot (z : ℂ) :
    Tendsto (fun L : ℝ => logPot L z - (2 * L * Real.log L - 2 * L)) atTop
      (𝓝 (π * |z.im|)) := by
  have h1 := tendsto_mul_log_norm_add (-z)
  have h2 := tendsto_mul_log_norm_add z
  have h3 : Tendsto (fun L : ℝ => z.im * (Real.arctan ((L - z.re) / z.im)
      + Real.arctan ((L + z.re) / z.im))) atTop (𝓝 (π * |z.im|)) := by
    have hm : Tendsto (fun L : ℝ => L - z.re) atTop atTop := by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-z.re) tendsto_id
    have hp : Tendsto (fun L : ℝ => L + z.re) atTop atTop :=
      tendsto_atTop_add_const_right atTop z.re tendsto_id
    rcases lt_trichotomy z.im 0 with hb | hb | hb
    · have a1 := (Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
        (hm.atTop_div_const_of_neg hb)
      have a2 := (Real.tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
        (hp.atTop_div_const_of_neg hb)
      have := (a1.add a2).const_mul z.im
      have hv : z.im * (-(π / 2) + -(π / 2)) = π * |z.im| := by rw [abs_of_neg hb]; ring
      rw [hv] at this
      exact this
    · simp [hb]
    · have a1 := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
        (hm.atTop_div_const hb)
      have a2 := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
        (hp.atTop_div_const hb)
      have := (a1.add a2).const_mul z.im
      have hv : z.im * (π / 2 + π / 2) = π * |z.im| := by rw [abs_of_pos hb]; ring
      rw [hv] at this
      exact this
  have h := (h1.add h2).add h3
  have hval : (-z).re + z.re + π * |z.im| = π * |z.im| := by simp
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with L hL
  unfold logPot
  simp only [Complex.neg_re, sub_eq_add_neg]
  ring

/-- `x ↦ log |x - z|` is interval integrable for every `z ∈ ℂ`. -/
lemma intervalIntegrable_log_norm_sub (z : ℂ) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.log ‖(x : ℂ) - z‖) volume a b := by
  by_cases hb : z.im = 0
  · have hz : z = (z.re : ℂ) := by
      apply Complex.ext <;> simp [hb]
    have hfun : (fun x : ℝ => Real.log ‖(x : ℂ) - z‖) = fun x => Real.log (x - z.re) := by
      funext x
      rw [hz, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Real.log_abs]
      simp
    rw [hfun]
    have := (intervalIntegrable_log' (a := a - z.re) (b := b - z.re)).comp_sub_right z.re
    simpa using this
  · have hpos : ∀ x : ℝ, 0 < (x - z.re) ^ 2 + z.im ^ 2 := fun x => by positivity
    have hcont : Continuous fun x : ℝ => Real.log ((x - z.re) ^ 2 + z.im ^ 2) / 2 := by
      have : Continuous fun x : ℝ => (x - z.re) ^ 2 + z.im ^ 2 := by fun_prop
      exact (this.log fun x => (hpos x).ne').div_const 2
    have hfun : (fun x : ℝ => Real.log ‖(x : ℂ) - z‖)
        = fun x => Real.log ((x - z.re) ^ 2 + z.im ^ 2) / 2 := by
      funext x; exact log_norm_ofReal_sub x z
    rw [hfun]
    exact hcont.intervalIntegrable _ _

/-- Interval integral of a finite (multiset) sum. -/
lemma intervalIntegral_multiset_sum {a b : ℝ} (Z : Multiset ℂ) (f : ℂ → ℝ → ℝ)
    (hf : ∀ z, IntervalIntegrable (f z) volume a b) :
    IntervalIntegrable (fun x => (Z.map (fun z => f z x)).sum) volume a b ∧
    ∫ x in a..b, (Z.map (fun z => f z x)).sum = (Z.map (fun z => ∫ x in a..b, f z x)).sum := by
  induction Z using Multiset.induction_on with
  | empty => simp
  | cons z Z ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact ⟨(hf z).add ih.1, by rw [intervalIntegral.integral_add (hf z) ih.1, ih.2]⟩

/-- Limits of finite (multiset) sums. -/
lemma tendsto_multiset_sum' {ι : Type*} {l : Filter ι} (Z : Multiset ℂ) (f : ℂ → ι → ℝ)
    (g : ℂ → ℝ) (h : ∀ z, Tendsto (f z) l (𝓝 (g z))) :
    Tendsto (fun i => (Z.map (fun z => f z i)).sum) l (𝓝 (Z.map g).sum) := by
  induction Z using Multiset.induction_on with
  | empty => simp [tendsto_const_nhds]
  | cons z Z ih => simpa using (h z).add ih

/-- `log |∏ (x - z)| = ∑ log |x - z|` away from the roots. -/
lemma log_norm_multiset_prod_sub (Z : Multiset ℂ) (x : ℝ) (hx : ∀ z ∈ Z, (x : ℂ) ≠ z) :
    Real.log ‖(Z.map (fun z => (x : ℂ) - z)).prod‖
      = (Z.map (fun z => Real.log ‖(x : ℂ) - z‖)).sum := by
  induction Z using Multiset.induction_on with
  | empty => simp
  | cons a Z ih =>
    have ha : (x : ℂ) - a ≠ 0 := sub_ne_zero.mpr (hx a (Multiset.mem_cons_self a Z))
    have hZ : ∀ z ∈ Z, (x : ℂ) ≠ z := fun z hz => hx z (Multiset.mem_cons_of_mem hz)
    have hprod : (Z.map (fun z => (x : ℂ) - z)).prod ≠ 0 := by
      apply Multiset.prod_ne_zero
      simp only [Multiset.mem_map, not_exists, not_and]
      intro z hz h0
      exact hZ z hz (sub_eq_zero.mp h0)
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, norm_mul]
    rw [Real.log_mul (norm_ne_zero_iff.mpr ha) (norm_ne_zero_iff.mpr hprod), ih hZ]

open Polynomial in
/-- The set of real roots of a complex polynomial is finite. -/
lemma finite_real_roots (p : ℂ[X]) : {x : ℝ | (x : ℂ) ∈ p.roots}.Finite := by
  have : {x : ℝ | (x : ℂ) ∈ p.roots} = Complex.ofReal ⁻¹' (p.roots.toFinset : Set ℂ) := by
    ext x; simp
  rw [this]
  exact (p.roots.toFinset.finite_toSet).preimage Complex.ofReal_injective.injOn

open Polynomial in
/-- `log |p(x)| = log |c| + ∑_{roots} log |x - z|` at every real `x` that is not a root. -/
lemma log_norm_eval_of_not_mem (p : ℂ[X]) (hp : p ≠ 0) {x : ℝ} (hx : (x : ℂ) ∉ p.roots) :
    Real.log ‖p.eval (x : ℂ)‖
      = Real.log ‖p.leadingCoeff‖ + (p.roots.map (fun z => Real.log ‖(x : ℂ) - z‖)).sum := by
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have hx' : ∀ z ∈ p.roots, (x : ℂ) ≠ z := fun z hz h => hx (by rw [h]; exact hz)
  have hprod : (p.roots.map (fun z => (x : ℂ) - z)).prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    simp only [Multiset.mem_map, not_exists, not_and]
    intro z hz h0
    exact hx' z hz (sub_eq_zero.mp h0)
  rw [(IsAlgClosed.splits p).eval_eq_prod_roots, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr hlc) (norm_ne_zero_iff.mpr hprod),
    log_norm_multiset_prod_sub _ _ hx']

open Polynomial in
lemma log_norm_eval_ae_eq (p : ℂ[X]) (hp : p ≠ 0) :
    ∀ᵐ (x : ℝ) ∂volume, Real.log ‖p.eval (x : ℂ)‖
      = Real.log ‖p.leadingCoeff‖ + (p.roots.map (fun z => Real.log ‖(x : ℂ) - z‖)).sum := by
  have hnull : volume {x : ℝ | (x : ℂ) ∈ p.roots} = 0 := (finite_real_roots p).measure_zero _
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx
  exact log_norm_eval_of_not_mem p hp hx

open Polynomial in
/-- `x ↦ log |p(x)|` is interval integrable on every interval (`p ≠ 0`). -/
lemma intervalIntegrable_log_norm_eval (p : ℂ[X]) (hp : p ≠ 0) (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.log ‖p.eval (x : ℂ)‖) volume a b := by
  have hI := intervalIntegral_multiset_sum (a := a) (b := b) p.roots
    (fun z x => Real.log ‖(x : ℂ) - z‖) (fun z => intervalIntegrable_log_norm_sub z _ _)
  have hsum := (intervalIntegrable_const (c := Real.log ‖p.leadingCoeff‖)).add hI.1
  refine hsum.congr_ae ?_
  filter_upwards [ae_restrict_of_ae (log_norm_eval_ae_eq p hp)] with x hx
  exact hx.symm

open Polynomial in
/-- `∫_{-L}^{L} log |p(x)| dx = 2 L log |c| + ∑_{roots} Φ_L(z)` for a nonzero complex polynomial `p`
with leading coefficient `c`. -/
theorem integral_log_norm_eval (p : ℂ[X]) (hp : p ≠ 0) (L : ℝ) :
    ∫ x in (-L)..L, Real.log ‖p.eval (x : ℂ)‖
      = 2 * L * Real.log ‖p.leadingCoeff‖ + (p.roots.map (logPot L)).sum := by
  have hae : ∀ᵐ (x : ℝ) ∂volume, x ∈ Set.uIoc (-L) L →
      Real.log ‖p.eval (x : ℂ)‖
        = Real.log ‖p.leadingCoeff‖ + (p.roots.map (fun z => Real.log ‖(x : ℂ) - z‖)).sum := by
    filter_upwards [log_norm_eval_ae_eq p hp] with x hx _ using hx
  rw [intervalIntegral.integral_congr_ae hae]
  have hI := intervalIntegral_multiset_sum (a := -L) (b := L) p.roots
    (fun z x => Real.log ‖(x : ℂ) - z‖) (fun z => intervalIntegrable_log_norm_sub z _ _)
  rw [intervalIntegral.integral_add intervalIntegrable_const hI.1, hI.2,
    intervalIntegral.integral_const]
  simp only [integral_log_norm_sub, smul_eq_mul]
  ring

open Polynomial in
/-- **Real-line Jensen asymptotics.** For a nonzero complex polynomial `p` of degree `n` with
leading coefficient `c`,
`∫_{-L}^{L} log |p(x)| dx - 2 L log |c| - n (2 L log L - 2 L) → π ∑_{roots} |Im z|`. -/
theorem tendsto_integral_log_norm_eval (p : ℂ[X]) (hp : p ≠ 0) :
    Tendsto (fun L : ℝ => (∫ x in (-L)..L, Real.log ‖p.eval (x : ℂ)‖)
        - 2 * L * Real.log ‖p.leadingCoeff‖ - p.natDegree * (2 * L * Real.log L - 2 * L))
      atTop (𝓝 (π * (p.roots.map (fun z => |z.im|)).sum)) := by
  have hcard : (p.roots.card : ℝ) = p.natDegree := by
    rw [IsAlgClosed.card_roots_eq_natDegree]
  have h := tendsto_multiset_sum' p.roots (fun z L => logPot L z - (2 * L * Real.log L - 2 * L))
    (fun z => π * |z.im|) tendsto_logPot
  rw [Multiset.sum_map_mul_left] at h
  refine h.congr' (Eventually.of_forall fun L => ?_)
  dsimp only
  rw [integral_log_norm_eval p hp L, ← hcard, Multiset.sum_map_sub]
  simp only [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul]
  ring

/-! ### Lemma 2: the Jensen-type identity on the real line -/

lemma re_multiset_sum (Z : Multiset ℂ) : Z.sum.re = (Z.map Complex.re).sum := by
  induction Z using Multiset.induction_on with
  | empty => simp
  | cons a Z ih => simp [ih]

/-- `|log |1 - w| + Re w| ≤ |w|²` for `|w| ≤ 1/2`. -/
lemma abs_log_norm_one_sub_add_re_le {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    |Real.log ‖1 - w‖ + w.re| ≤ ‖w‖ ^ 2 := by
  have h1 : ‖Complex.log (1 + -w) - -w‖ ≤ ‖-w‖ ^ 2 * (1 - ‖-w‖)⁻¹ / 2 :=
    Complex.norm_log_one_add_sub_self_le (by rw [norm_neg]; linarith)
  rw [norm_neg] at h1
  have h2 : ‖w‖ ^ 2 * (1 - ‖w‖)⁻¹ / 2 ≤ ‖w‖ ^ 2 := by
    have hinv : (1 - ‖w‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have := sq_nonneg ‖w‖
    nlinarith
  have h3 : Real.log ‖1 - w‖ + w.re = (Complex.log (1 + -w) - -w).re := by
    simp [Complex.log_re, sub_eq_add_neg]
  rw [h3]
  exact (Complex.abs_re_le_norm _).trans (h1.trans h2)

/-- For `2 |z| ≤ |x|`, `x ≠ 0`: `|log |x - z| - log |x| + Re z / x| ≤ |z|² / x²`. -/
lemma abs_log_norm_sub_le {x : ℝ} {z : ℂ} (hx : 2 * ‖z‖ ≤ |x|) (hx0 : x ≠ 0) :
    |Real.log ‖(x : ℂ) - z‖ - Real.log |x| + z.re / x| ≤ ‖z‖ ^ 2 / x ^ 2 := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0
  have hax : 0 < |x| := abs_pos.mpr hx0
  set w : ℂ := z / x with hw_def
  have hwn : ‖w‖ = ‖z‖ / |x| := by
    rw [hw_def, norm_div, Complex.norm_real, Real.norm_eq_abs]
  have hw : ‖w‖ ≤ 1 / 2 := by
    rw [hwn, div_le_iff₀ hax]; linarith
  have hw1 : 1 - w ≠ 0 := by
    intro h
    have : ‖w‖ = 1 := by rw [← sub_eq_zero.mp h]; simp
    linarith
  have hfac : (x : ℂ) - z = x * (1 - w) := by
    rw [hw_def]; field_simp
  have hlog : Real.log ‖(x : ℂ) - z‖ = Real.log |x| + Real.log ‖1 - w‖ := by
    rw [hfac, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Real.log_mul hax.ne' (norm_ne_zero_iff.mpr hw1)]
  have hre : w.re = z.re / x := by
    rw [hw_def, Complex.div_ofReal_re]
  have hb := abs_log_norm_one_sub_add_re_le hw
  rw [hre, hwn, div_pow, sq_abs] at hb
  rw [hlog]
  calc |Real.log |x| + Real.log ‖1 - w‖ - Real.log |x| + z.re / x|
      = |Real.log ‖1 - w‖ + z.re / x| := by ring_nf
    _ ≤ ‖z‖ ^ 2 / x ^ 2 := hb

/-- Decomposition of `∑ log |x - z|` into `card · log |x| - (∑ Re z)/x` plus remainders. -/
lemma sum_log_norm_sub_eq (Z : Multiset ℂ) (x : ℝ) :
    (Z.map (fun z => Real.log ‖(x : ℂ) - z‖)).sum
      = (Z.map (fun z => Real.log ‖(x : ℂ) - z‖ - Real.log |x| + z.re / x)).sum
        + Z.card * Real.log |x| - (Z.map Complex.re).sum / x := by
  induction Z using Multiset.induction_on with
  | empty => simp
  | cons a Z ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, ih]
    push_cast
    ring

lemma abs_multiset_sum_le (Z : Multiset ℂ) (f g : ℂ → ℝ) (h : ∀ z ∈ Z, |f z| ≤ g z) :
    |(Z.map f).sum| ≤ (Z.map g).sum := by
  induction Z using Multiset.induction_on with
  | empty => simp
  | cons a Z ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact (abs_add_le _ _).trans (add_le_add (h a (Multiset.mem_cons_self a Z))
      (ih fun z hz => h z (Multiset.mem_cons_of_mem hz)))

lemma norm_le_multiset_sum {Z : Multiset ℂ} {z : ℂ} (hz : z ∈ Z) : ‖z‖ ≤ (Z.map norm).sum := by
  induction Z using Multiset.induction_on with
  | empty => simp at hz
  | cons a Z ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    rcases Multiset.mem_cons.mp hz with h | h
    · subst h
      have : 0 ≤ (Z.map norm).sum := Multiset.sum_nonneg fun x hx => by
        obtain ⟨y, _, rfl⟩ := Multiset.mem_map.mp hx
        exact norm_nonneg _
      linarith
    · linarith [ih h, norm_nonneg a]

/-- **Tail bound.**  If `card X = card Y` and `∑ Re X = ∑ Re Y`, then
`|∑_X log |x - z| - ∑_Y log |x - z|| ≤ (∑_X |z|² + ∑_Y |z|²) / x²` for `|x| ≥ 1 + 2 (∑ |z|)`. -/
lemma abs_sum_log_sub_sum_log_le {X Y : Multiset ℂ} (hcard : X.card = Y.card)
    (hre : (X.map Complex.re).sum = (Y.map Complex.re).sum) {x : ℝ}
    (hx : 1 + 2 * ((X.map norm).sum + (Y.map norm).sum) ≤ |x|) :
    |(X.map (fun z => Real.log ‖(x : ℂ) - z‖)).sum - (Y.map (fun z => Real.log ‖(x : ℂ) - z‖)).sum|
      ≤ ((X.map (fun z => ‖z‖ ^ 2)).sum + (Y.map (fun z => ‖z‖ ^ 2)).sum) / x ^ 2 := by
  have hXn : 0 ≤ (X.map norm).sum := Multiset.sum_nonneg fun x hx => by
    obtain ⟨y, _, rfl⟩ := Multiset.mem_map.mp hx; exact norm_nonneg _
  have hYn : 0 ≤ (Y.map norm).sum := Multiset.sum_nonneg fun x hx => by
    obtain ⟨y, _, rfl⟩ := Multiset.mem_map.mp hx; exact norm_nonneg _
  have hx0 : x ≠ 0 := by
    intro h; rw [h, abs_zero] at hx; linarith
  have hX : ∀ z ∈ X, 2 * ‖z‖ ≤ |x| := fun z hz => by
    have := norm_le_multiset_sum hz; linarith
  have hY : ∀ z ∈ Y, 2 * ‖z‖ ≤ |x| := fun z hz => by
    have := norm_le_multiset_sum hz; linarith
  rw [sum_log_norm_sub_eq X x, sum_log_norm_sub_eq Y x, hcard, hre]
  have e : ∀ A B C D : ℝ, A + C - D - (B + C - D) = A - B := fun A B C D => by ring
  rw [e]
  have h1 := abs_multiset_sum_le X
    (fun z => Real.log ‖(x : ℂ) - z‖ - Real.log |x| + z.re / x) (fun z => ‖z‖ ^ 2 / x ^ 2)
    (fun z hz => abs_log_norm_sub_le (hX z hz) hx0)
  have h2 := abs_multiset_sum_le Y
    (fun z => Real.log ‖(x : ℂ) - z‖ - Real.log |x| + z.re / x) (fun z => ‖z‖ ^ 2 / x ^ 2)
    (fun z hz => abs_log_norm_sub_le (hY z hz) hx0)
  rw [Multiset.sum_map_div] at h1 h2
  calc _ ≤ |(X.map (fun z => Real.log ‖(x : ℂ) - z‖ - Real.log |x| + z.re / x)).sum|
        + |(Y.map (fun z => Real.log ‖(x : ℂ) - z‖ - Real.log |x| + z.re / x)).sum| :=
        abs_sub _ _
    _ ≤ _ := by rw [add_div]; exact add_le_add h1 h2

open Polynomial in
/-- **Lemma 2 (Jensen-type identity).**  Let `p, q` be complex polynomials with the same degree and
the same nonzero leading coefficient, such that all roots of `q` are real and the roots of `p` and
`q` have the same sum.  Then `x ↦ log |p(x)/q(x)|` is integrable on `ℝ` and
`∫_ℝ log |p(x)/q(x)| dx = π ∑_i |Im x_i|` (sum over the roots of `p`). -/
theorem jensen_identity {p q : ℂ[X]} (hp : p ≠ 0) (hlc : p.leadingCoeff = q.leadingCoeff)
    (hdeg : p.natDegree = q.natDegree) (hreal : ∀ y ∈ q.roots, y.im = 0)
    (hsum : p.roots.sum = q.roots.sum) :
    Integrable (fun x : ℝ => Real.log ‖p.eval (x : ℂ) / q.eval (x : ℂ)‖) ∧
    ∫ x : ℝ, Real.log ‖p.eval (x : ℂ) / q.eval (x : ℂ)‖
      = π * (p.roots.map (fun z => |z.im|)).sum := by
  have hq : q ≠ 0 := by
    intro h; rw [h, leadingCoeff_zero] at hlc; exact hp (leadingCoeff_eq_zero.mp hlc)
  have hcard : p.roots.card = q.roots.card := by
    rw [IsAlgClosed.card_roots_eq_natDegree, IsAlgClosed.card_roots_eq_natDegree, hdeg]
  have hre : (p.roots.map Complex.re).sum = (q.roots.map Complex.re).sum := by
    have := congrArg Complex.re hsum
    rwa [re_multiset_sum, re_multiset_sum] at this
  set h : ℝ → ℝ := fun x => Real.log ‖p.eval (x : ℂ) / q.eval (x : ℂ)‖ with h_def
  -- off the real roots, `h = log |p| - log |q|`
  have hdiff : ∀ x : ℝ, (x : ℂ) ∉ p.roots → (x : ℂ) ∉ q.roots →
      h x = (p.roots.map (fun z => Real.log ‖(x : ℂ) - z‖)).sum
        - (q.roots.map (fun z => Real.log ‖(x : ℂ) - z‖)).sum := by
    intro x hxp hxq
    have hpx : p.eval (x : ℂ) ≠ 0 := fun h0 =>
      hxp ((mem_roots hp).mpr h0)
    have hqx : q.eval (x : ℂ) ≠ 0 := fun h0 =>
      hxq ((mem_roots hq).mpr h0)
    simp only [h_def]
    rw [norm_div, Real.log_div (norm_ne_zero_iff.mpr hpx) (norm_ne_zero_iff.mpr hqx),
      log_norm_eval_of_not_mem p hp hxp, log_norm_eval_of_not_mem q hq hxq, hlc]
    ring
  have hnull : volume ({x : ℝ | (x : ℂ) ∈ p.roots} ∪ {x : ℝ | (x : ℂ) ∈ q.roots}) = 0 :=
    ((finite_real_roots p).union (finite_real_roots q)).measure_zero _
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), h x
      = (Real.log ‖p.eval (x : ℂ)‖) - (Real.log ‖q.eval (x : ℂ)‖) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hx
    rw [hdiff x hx.1 hx.2, log_norm_eval_of_not_mem p hp hx.1, log_norm_eval_of_not_mem q hq hx.2,
      hlc]
    ring
  -- the tail bound
  set R : ℝ := 1 + 2 * ((p.roots.map norm).sum + (q.roots.map norm).sum) with hR
  set S : ℝ := (p.roots.map (fun z => ‖z‖ ^ 2)).sum + (q.roots.map (fun z => ‖z‖ ^ 2)).sum
    with hS
  have hRpos : 1 ≤ R := by
    have hXn : 0 ≤ (p.roots.map norm).sum := Multiset.sum_nonneg fun x hx => by
      obtain ⟨y, _, rfl⟩ := Multiset.mem_map.mp hx; exact norm_nonneg _
    have hYn : 0 ≤ (q.roots.map norm).sum := Multiset.sum_nonneg fun x hx => by
      obtain ⟨y, _, rfl⟩ := Multiset.mem_map.mp hx; exact norm_nonneg _
    linarith
  have hS0 : 0 ≤ S := add_nonneg
    (Multiset.sum_nonneg fun x hx => by
      obtain ⟨y, _, rfl⟩ := Multiset.mem_map.mp hx; positivity)
    (Multiset.sum_nonneg fun x hx => by
      obtain ⟨y, _, rfl⟩ := Multiset.mem_map.mp hx; positivity)
  have htail : ∀ x : ℝ, R ≤ |x| → |h x| ≤ 2 * S * (1 + x ^ 2)⁻¹ := by
    intro x hx
    have hroot : ∀ (r : ℂ[X]), r = p ∨ r = q → (x : ℂ) ∉ r.roots := by
      rintro r hr hxr
      have hle : ‖(x : ℂ)‖ ≤ (r.roots.map norm).sum := norm_le_multiset_sum hxr
      rw [Complex.norm_real, Real.norm_eq_abs] at hle
      have hXn : 0 ≤ (p.roots.map norm).sum := Multiset.sum_nonneg fun x hx => by
        obtain ⟨y, _, rfl⟩ := Multiset.mem_map.mp hx; exact norm_nonneg _
      have hYn : 0 ≤ (q.roots.map norm).sum := Multiset.sum_nonneg fun x hx => by
        obtain ⟨y, _, rfl⟩ := Multiset.mem_map.mp hx; exact norm_nonneg _
      rcases hr with rfl | rfl <;> linarith
    rw [hdiff x (hroot p (Or.inl rfl)) (hroot q (Or.inr rfl))]
    have hb := abs_sum_log_sub_sum_log_le hcard hre hx
    have hx2 : 1 ≤ x ^ 2 := by
      have : 1 ≤ |x| := hRpos.trans hx
      nlinarith [sq_abs x, abs_nonneg x]
    have hx2' : 0 < x ^ 2 := by linarith
    refine hb.trans ?_
    rw [div_le_iff₀ hx2', mul_assoc, inv_mul_eq_div, ← mul_div_assoc, le_div_iff₀ (by positivity)]
    nlinarith
  -- integrability
  have hmeas : Measurable h := by
    simp only [h_def]
    exact ((((Polynomial.continuous p).comp Complex.continuous_ofReal).measurable.div
      ((Polynomial.continuous q).comp Complex.continuous_ofReal).measurable).norm).log
  have hint_mid : IntegrableOn h (Set.Icc (-R) R) := by
    have hpi := intervalIntegrable_log_norm_eval p hp (-R) R
    have hqi := intervalIntegrable_log_norm_eval q hq (-R) R
    have := (hpi.sub hqi).congr_ae (ae_restrict_of_ae (hae.mono fun x hx => hx.symm))
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)] at this
    exact this
  have hint_out : IntegrableOn h (Set.Icc (-R) R)ᶜ := by
    refine (integrable_inv_one_add_sq.const_mul (2 * S)).integrableOn.mono'
      hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Icc.compl).mpr (ae_of_all _ fun x hx => ?_)
    have hx' : R ≤ |x| := by
      simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
      rcases hx with hx | hx
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [Real.norm_eq_abs]
    exact htail x hx'
  have hint : Integrable h := by
    have := hint_mid.union hint_out
    rwa [Set.union_compl_self, integrableOn_univ] at this
  refine ⟨hint, ?_⟩
  -- the value: symmetric limits
  have hlim1 := intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id
  have hp' := tendsto_integral_log_norm_eval p hp
  have hq' := tendsto_integral_log_norm_eval q hq
  have hq0 : π * (q.roots.map (fun z => |z.im|)).sum = 0 := by
    rw [Multiset.map_congr rfl (fun z hz => by rw [hreal z hz, abs_zero])]
    simp
  rw [hq0] at hq'
  have hlim2 := hp'.sub hq'
  rw [sub_zero] at hlim2
  refine tendsto_nhds_unique (hlim1.congr' (Eventually.of_forall fun L => ?_)) hlim2
  simp only [id]
  rw [intervalIntegral.integral_congr_ae (hae.mono fun x hx _ => hx),
    intervalIntegral.integral_sub (intervalIntegrable_log_norm_eval p hp _ _)
      (intervalIntegrable_log_norm_eval q hq _ _), hlc, hdeg]
  ring

end OQP27.StripL3b
