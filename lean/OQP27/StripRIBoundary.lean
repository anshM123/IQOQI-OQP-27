import OQP27.StripRIEnds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Boundary values `c → c₀ + i0` (module L3b, proof of RI)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

Main results:
* `integrableOn_wgt`, `tendsto_wgt_tail`: `wgt τ = 1/√(τ (1 - τ))` is integrable on `(0, 1)`;
* `logPot_error`, `jensen_error` (quantitative real-line Jensen formula): if all roots of `p ≠ 0`
  satisfy `|z| ≤ R` and `2R ≤ L`, then
  `|∫_{-L}^{L} log|p| - 2L log|lc p| - n (2L log L - 2L) - π ∑ |Im z|| ≤ 10 n R²/L`;
* `penPoly_leadingCoeff`, `penPoly_natDegree`: the leading coefficient `det(-(P - τ))` and the degree
  `M` of `p(z) = det(A + c - z (P - τ))` do not depend on `c`;
* `norm_det_add_I_mono`: `ε ↦ |det(N + iε)|` is nondecreasing on `ε ≥ 0` for Hermitian `N`;
* `tendsto_imAbsSum_vertical` (**Lemma E**, imaginary parts): for real `c₀` and `0 < τ < 1`,
  `∑ |Im y_i(τ, c₀ + iε)| → ∑ |Im y_i(τ, c₀)|` as `ε → 0⁺`.

Lemma E is proved with the Jensen formula and dominated convergence (no continuity of roots is used).
Hypotheses: none.
Paper: `iqoqi/programs/oqp27B_all/Q_RI/PROOF.md`, Lemma E and Step 3; `Q_2bmv/PROOF.md`, Lemma 2.
-/

namespace OQP27.StripL3b

open Matrix Polynomial Complex Metric Filter Topology Set Real MeasureTheory

variable {M : ℕ}

/-! ### The weight `1/√(τ(1-τ))` -/

/-- `u(τ) = 1/√(τ(1-τ))`. -/
noncomputable def wgt (τ : ℝ) : ℝ := (√(τ * (1 - τ)))⁻¹

lemma wgt_le {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) :
    wgt τ ≤ √2 * (τ ^ (-(1 / 2 : ℝ)) + (1 - τ) ^ (-(1 / 2 : ℝ))) := by
  unfold wgt
  have h1' : 0 < 1 - τ := by linarith
  rw [Real.rpow_neg h0.le, Real.rpow_neg h1'.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  rcases le_total τ (1 / 2) with hτ | hτ
  · -- `τ (1 - τ) ≥ τ / 2`
    have hge : τ / 2 ≤ τ * (1 - τ) := by nlinarith
    have hs : √(τ / 2) ≤ √(τ * (1 - τ)) := Real.sqrt_le_sqrt hge
    have hpos : 0 < √(τ / 2) := Real.sqrt_pos.mpr (by positivity)
    have h2 : (√(τ * (1 - τ)))⁻¹ ≤ (√(τ / 2))⁻¹ := inv_anti₀ hpos hs
    have h3 : (√(τ / 2))⁻¹ = √2 * (√τ)⁻¹ := by
      rw [Real.sqrt_div h0.le, inv_div, div_eq_mul_inv]
    have h4 : 0 ≤ √2 * (√(1 - τ))⁻¹ := by positivity
    rw [mul_add]
    linarith
  · have hge : (1 - τ) / 2 ≤ τ * (1 - τ) := by nlinarith
    have hs : √((1 - τ) / 2) ≤ √(τ * (1 - τ)) := Real.sqrt_le_sqrt hge
    have hpos : 0 < √((1 - τ) / 2) := Real.sqrt_pos.mpr (by positivity)
    have h2 : (√(τ * (1 - τ)))⁻¹ ≤ (√((1 - τ) / 2))⁻¹ := inv_anti₀ hpos hs
    have h3 : (√((1 - τ) / 2))⁻¹ = √2 * (√(1 - τ))⁻¹ := by
      rw [Real.sqrt_div h1'.le, inv_div, div_eq_mul_inv]
    have h4 : 0 ≤ √2 * (√τ)⁻¹ := by positivity
    rw [mul_add]
    linarith

lemma wgt_nonneg (τ : ℝ) : 0 ≤ wgt τ := by unfold wgt; positivity

lemma continuousOn_wgt : ContinuousOn wgt (Ioo 0 1) := by
  unfold wgt
  refine ContinuousOn.inv₀ (by fun_prop) fun τ hτ => ?_
  exact (Real.sqrt_pos.mpr (mul_pos hτ.1 (by linarith [hτ.2]))).ne'

/-- `u` is integrable on `(0, 1)` (its integral is `π`). -/
lemma integrableOn_wgt : IntegrableOn wgt (Ioo 0 1) := by
  have h1 : IntegrableOn (fun τ : ℝ => τ ^ (-(1 / 2 : ℝ))) (Ioo 0 1) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (by norm_num : (-1 : ℝ) < -(1 / 2))).1
    exact this.mono_set Ioo_subset_Ioc_self
  have h2 : IntegrableOn (fun τ : ℝ => (1 - τ) ^ (-(1 / 2 : ℝ))) (Ioo 0 1) := by
    have h0 := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
      (by norm_num : (-1 : ℝ) < -(1 / 2))
    have h' := (h0.comp_sub_left 1).symm
    simp only [sub_zero, sub_self] at h'
    exact h'.1.mono_set Ioo_subset_Ioc_self
  have hsum := (h1.add h2).const_mul (√2)
  refine hsum.mono' (continuousOn_wgt.aestronglyMeasurable measurableSet_Ioo) ?_
  refine (ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ fun τ hτ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (wgt_nonneg τ)]
  exact wgt_le hτ.1 hτ.2

/-- The tails of `∫ u` vanish: `∫_{(0,δ) ∪ (1-δ,1)} u → 0`. -/
lemma tendsto_wgt_tail :
    Tendsto (fun δ : ℝ => ∫ τ in Ioo 0 1, (Ioo δ (1 - δ))ᶜ.indicator wgt τ) (𝓝[>] 0) (𝓝 0) := by
  have hlim : ∀ τ ∈ Ioo (0 : ℝ) 1,
      Tendsto (fun δ : ℝ => (Ioo δ (1 - δ))ᶜ.indicator wgt τ) (𝓝[>] 0) (𝓝 0) := by
    intro τ hτ
    have hev : ∀ᶠ δ : ℝ in 𝓝[>] 0, (Ioo δ (1 - δ))ᶜ.indicator wgt τ = 0 := by
      have h1 : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < min τ (1 - τ) :=
        nhdsWithin_le_nhds (eventually_lt_nhds (lt_min hτ.1 (by linarith [hτ.2])))
      filter_upwards [h1] with δ hδ
      have hm1 := min_le_left τ (1 - τ)
      have hm2 := min_le_right τ (1 - τ)
      rw [Set.indicator_of_notMem]
      simp only [Set.mem_compl_iff, not_not, Set.mem_Ioo]
      constructor <;> linarith
    exact tendsto_const_nhds.congr' (hev.mono fun δ h => h.symm)
  have := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioo 0 1))
    (F := fun δ τ => (Ioo δ (1 - δ))ᶜ.indicator wgt τ) (f := fun _ => (0 : ℝ)) wgt
    (Eventually.of_forall fun δ => ((continuousOn_wgt.aestronglyMeasurable measurableSet_Ioo).indicator
      (measurableSet_Ioo.compl)))
    (Eventually.of_forall fun δ => (ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ fun τ _ => by
      rw [Real.norm_eq_abs]
      by_cases h : τ ∈ (Ioo δ (1 - δ))ᶜ
      · rw [Set.indicator_of_mem h, abs_of_nonneg (wgt_nonneg τ)]
      · rw [Set.indicator_of_notMem h, abs_zero]; exact wgt_nonneg τ))
    integrableOn_wgt
    ((ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ hlim))
  simpa using this

/-! ### A quantitative real-line Jensen estimate -/

lemma arctan_le_self {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  have h1 := Real.arctan_nonneg.mpr hx
  have h2 := Real.arctan_lt_pi_div_two x
  have := Real.le_tan h1 h2
  rwa [Real.tan_arctan] at this

/-- `|β| (π - arctan((L-α)/|β|) - arctan((L+α)/|β|)) ≤ 4 β² / L` for `|α| ≤ L/2`. -/
lemma arctan_pair_error {α β L : ℝ} (hL : 0 < L) (hα : 2 * |α| ≤ L) (hβ : 0 < β) :
    |β * (Real.arctan ((L - α) / β) + Real.arctan ((L + α) / β)) - π * β| ≤ 4 * β ^ 2 / L := by
  have hLa : L / 2 ≤ L - α := by linarith [le_abs_self α]
  have hLb : L / 2 ≤ L + α := by linarith [neg_abs_le α]
  have hu1 : 0 < (L - α) / β := div_pos (by linarith) hβ
  have hu2 : 0 < (L + α) / β := div_pos (by linarith) hβ
  have e1 := Real.arctan_inv_of_pos hu1
  have e2 := Real.arctan_inv_of_pos hu2
  rw [inv_div] at e1 e2
  have hv1 : 0 ≤ β / (L - α) := div_nonneg hβ.le (by linarith)
  have hv2 : 0 ≤ β / (L + α) := div_nonneg hβ.le (by linarith)
  have hb1 := arctan_le_self hv1
  have hb2 := arctan_le_self hv2
  have hn1 := Real.arctan_nonneg.mpr hv1
  have hn2 := Real.arctan_nonneg.mpr hv2
  have hd1 : β / (L - α) ≤ 2 * β / L := by
    rw [div_le_div_iff₀ (by linarith) hL]; nlinarith
  have hd2 : β / (L + α) ≤ 2 * β / L := by
    rw [div_le_div_iff₀ (by linarith) hL]; nlinarith
  have hexpr : β * (Real.arctan ((L - α) / β) + Real.arctan ((L + α) / β)) - π * β
      = -(β * (Real.arctan (β / (L - α)) + Real.arctan (β / (L + α)))) := by
    rw [show Real.arctan ((L - α) / β) = π / 2 - Real.arctan (β / (L - α)) by linarith,
      show Real.arctan ((L + α) / β) = π / 2 - Real.arctan (β / (L + α)) by linarith]
    ring
  rw [hexpr, abs_neg, abs_of_nonneg (by positivity)]
  calc β * (Real.arctan (β / (L - α)) + Real.arctan (β / (L + α)))
      ≤ β * (2 * β / L + 2 * β / L) := by gcongr <;> linarith
    _ = 4 * β ^ 2 / L := by ring

/-- `|(L + Re w)(log |L + w| - log L) - Re w| ≤ 3 R² / L` for `|w| ≤ R ≤ L/2`. -/
lemma log_term_error {w : ℂ} {R L : ℝ} (hw : ‖w‖ ≤ R) (hL : 2 * R ≤ L) (hL0 : 0 < L) :
    |(L + w.re) * (Real.log ‖(L : ℂ) + w‖ - Real.log L) - w.re| ≤ 3 * R ^ 2 / L := by
  have hR : 0 ≤ R := (norm_nonneg w).trans hw
  set v : ℂ := -(w / L) with hv
  have hvn : ‖v‖ = ‖w‖ / L := by
    rw [hv, norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL0]
  have hv12 : ‖v‖ ≤ 1 / 2 := by
    rw [hvn, div_le_iff₀ hL0]; linarith
  have hb := abs_log_norm_one_sub_add_re_le hv12
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL0.ne'
  have hLw : (L : ℂ) + w = L * (1 - v) := by
    rw [hv]; field_simp; ring
  have h1v : (1 : ℂ) - v ≠ 0 := by
    intro h
    have : ‖v‖ = 1 := by rw [← sub_eq_zero.mp h]; simp
    linarith
  have hlog : Real.log ‖(L : ℂ) + w‖ - Real.log L = Real.log ‖1 - v‖ := by
    rw [hLw, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL0,
      Real.log_mul hL0.ne' (norm_ne_zero_iff.mpr h1v)]
    ring
  have hvre : v.re = -(w.re / L) := by
    rw [hv]; simp [Complex.div_ofReal_re]
  rw [hlog]
  set e := Real.log ‖1 - v‖ + v.re with he
  have he' : |e| ≤ ‖w‖ ^ 2 / L ^ 2 := by
    rw [he]; refine hb.trans (le_of_eq ?_); rw [hvn, div_pow]
  have hlog' : Real.log ‖1 - v‖ = w.re / L + e := by rw [he, hvre]; ring
  rw [hlog']
  have hwre : |w.re| ≤ R := (Complex.abs_re_le_norm w).trans hw
  have hexpr : (L + w.re) * (w.re / L + e) - w.re = w.re ^ 2 / L + (L + w.re) * e := by
    field_simp; ring
  rw [hexpr]
  have hLre : |L + w.re| ≤ 2 * L := by
    rw [abs_le]; constructor <;> linarith [abs_le.mp hwre]
  calc |w.re ^ 2 / L + (L + w.re) * e| ≤ |w.re ^ 2 / L| + |(L + w.re) * e| := abs_add_le _ _
    _ ≤ R ^ 2 / L + 2 * L * (R ^ 2 / L ^ 2) := by
        gcongr
        · rw [abs_of_nonneg (by positivity)]
          have hsq : w.re ^ 2 ≤ R ^ 2 := by
            have := pow_le_pow_left₀ (abs_nonneg w.re) hwre 2
            rwa [sq_abs] at this
          exact div_le_div_of_nonneg_right hsq hL0.le
        · rw [abs_mul]
          exact mul_le_mul hLre (he'.trans (by gcongr)) (abs_nonneg _) (by positivity)
    _ = 3 * R ^ 2 / L := by field_simp; ring


/-- **Quantitative asymptotics of the logarithmic potential**: for `|z| ≤ R ≤ L/2`,
`|Φ_L(z) - (2 L log L - 2 L) - π |Im z|| ≤ 10 R² / L`. -/
theorem logPot_error {z : ℂ} {R L : ℝ} (hz : ‖z‖ ≤ R) (hL : 2 * R ≤ L) (hL0 : 0 < L) :
    abs (logPot L z - (2 * L * Real.log L - 2 * L) - π * |z.im|) ≤ 10 * R ^ 2 / L := by
  have hR : 0 ≤ R := (norm_nonneg z).trans hz
  have h1 := log_term_error (w := -z) (by rwa [norm_neg]) hL hL0
  have h2 := log_term_error (w := z) hz hL hL0
  have hα : 2 * |z.re| ≤ L := by linarith [Complex.abs_re_le_norm z]
  have hβR : z.im ^ 2 ≤ R ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg z.im) ((Complex.abs_im_le_norm z).trans hz) 2
    rwa [sq_abs] at this
  have h3 : abs (z.im * (Real.arctan ((L - z.re) / z.im) + Real.arctan ((L + z.re) / z.im))
      - π * |z.im|) ≤ 4 * z.im ^ 2 / L := by
    rcases lt_trichotomy z.im 0 with hb | hb | hb
    · have := arctan_pair_error (α := z.re) (β := -z.im) hL0 hα (by linarith)
      rw [abs_of_neg hb]
      have e : z.im * (Real.arctan ((L - z.re) / z.im) + Real.arctan ((L + z.re) / z.im))
          = (-z.im) * (Real.arctan ((L - z.re) / (-z.im)) + Real.arctan ((L + z.re) / (-z.im))) := by
        rw [div_neg, div_neg, Real.arctan_neg, Real.arctan_neg]; ring
      rw [e]
      simpa [neg_sq] using this
    · simp [hb]
    · rw [abs_of_pos hb]; exact arctan_pair_error hL0 hα hb
  have hdecomp : logPot L z - (2 * L * Real.log L - 2 * L) - π * |z.im|
      = ((L + (-z).re) * (Real.log ‖(L : ℂ) + -z‖ - Real.log L) - (-z).re)
        + ((L + z.re) * (Real.log ‖(L : ℂ) + z‖ - Real.log L) - z.re)
        + (z.im * (Real.arctan ((L - z.re) / z.im) + Real.arctan ((L + z.re) / z.im))
          - π * |z.im|) := by
    unfold logPot
    simp only [Complex.neg_re, sub_eq_add_neg]
    ring
  rw [hdecomp]
  refine (abs_add_le _ _).trans ?_
  refine (add_le_add ((abs_add_le _ _).trans (add_le_add h1 h2)) h3).trans ?_
  have : 4 * z.im ^ 2 / L ≤ 4 * R ^ 2 / L := by gcongr
  have e : 3 * R ^ 2 / L + 3 * R ^ 2 / L + 4 * R ^ 2 / L = 10 * R ^ 2 / L := by ring
  linarith

open Polynomial in
/-- **Quantitative real-line Jensen.**  If all roots of `p ≠ 0` satisfy `|z| ≤ R` and `2R ≤ L`, then
`|∫_{-L}^{L} log |p| - 2 L log |c| - n (2 L log L - 2 L) - π ∑ |Im z|| ≤ 10 n R² / L`. -/
theorem jensen_error (p : ℂ[X]) (hp : p ≠ 0) {R L : ℝ} (hroots : ∀ z ∈ p.roots, ‖z‖ ≤ R)
    (hL : 2 * R ≤ L) (hL0 : 0 < L) :
    |(∫ x in (-L)..L, Real.log ‖p.eval (x : ℂ)‖) - 2 * L * Real.log ‖p.leadingCoeff‖
      - p.natDegree * (2 * L * Real.log L - 2 * L) - π * (p.roots.map fun z => |z.im|).sum|
      ≤ p.natDegree * (10 * R ^ 2 / L) := by
  have hcard : (p.roots.card : ℝ) = p.natDegree := by
    rw [IsAlgClosed.card_roots_eq_natDegree]
  rw [integral_log_norm_eval p hp L]
  have heq : 2 * L * Real.log ‖p.leadingCoeff‖ + (p.roots.map (logPot L)).sum
      - 2 * L * Real.log ‖p.leadingCoeff‖ - p.natDegree * (2 * L * Real.log L - 2 * L)
      - π * (p.roots.map fun z => |z.im|).sum
      = (p.roots.map fun z => logPot L z - (2 * L * Real.log L - 2 * L) - π * |z.im|).sum := by
    rw [Multiset.sum_map_sub, Multiset.sum_map_sub, Multiset.sum_map_mul_left, ← hcard]
    simp only [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul]
    ring
  rw [heq]
  refine (abs_multiset_sum_le p.roots _ (fun _ => 10 * R ^ 2 / L)
    fun z hz => logPot_error (hroots z hz) hL hL0).trans (le_of_eq ?_)
  rw [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, hcard]

/-! ### The pencil polynomial: leading coefficient and the monotonicity in `Im c` -/

section PenLead

variable {P A : Matrix (Fin M) (Fin M) ℂ}

lemma penPoly_eq_C_mul_charpoly (hP : P * P = P) (A : Matrix (Fin M) (Fin M) ℂ) {τ : ℝ}
    (h0 : τ ≠ 0) (h1 : τ ≠ 1) (c : ℂ) :
    penPoly P A τ c = Polynomial.C (-(P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))).det
      * ((P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))⁻¹ * (A + c • 1)).charpoly := by
  apply Polynomial.funext
  intro z
  rw [eval_penPoly, Polynomial.eval_mul, Polynomial.eval_C]
  exact det_pencil (H := A + c • 1) hP h0 h1 z

lemma penPoly_leadingCoeff (hP : P * P = P) (A : Matrix (Fin M) (Fin M) ℂ) {τ : ℝ}
    (h0 : τ ≠ 0) (h1 : τ ≠ 1) (c : ℂ) :
    (penPoly P A τ c).leadingCoeff = (-(P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))).det := by
  rw [penPoly_eq_C_mul_charpoly hP A h0 h1 c, Polynomial.leadingCoeff_C_mul_of_isUnit,
    (Matrix.charpoly_monic _).leadingCoeff, mul_one]
  rw [Matrix.det_neg]
  exact (isUnit_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (isUnit_det_P_sub hP h0 h1).ne_zero))

lemma penPoly_natDegree (hP : P * P = P) (A : Matrix (Fin M) (Fin M) ℂ) {τ : ℝ}
    (h0 : τ ≠ 0) (h1 : τ ≠ 1) (c : ℂ) : (penPoly P A τ c).natDegree = M := by
  have hd : (-(P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))).det ≠ 0 := by
    rw [Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (isUnit_det_P_sub hP h0 h1).ne_zero
  rw [penPoly_eq_C_mul_charpoly hP A h0 h1 c, Polynomial.natDegree_C_mul hd,
    Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

/-- `det (N + i ε) = ∏ (ν_j + i ε)` for Hermitian `N`. -/
lemma det_add_smul_one_eq_prod {N : Matrix (Fin M) (Fin M) ℂ} (hN : N.IsHermitian) (w : ℂ) :
    (N + w • (1 : Matrix (Fin M) (Fin M) ℂ)).det = ∏ i, ((hN.eigenvalues i : ℂ) + w) := by
  have h := congrArg (Polynomial.eval (-w)) hN.charpoly_eq
  rw [Matrix.eval_charpoly, Polynomial.eval_prod] at h
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h
  have e : N + w • (1 : Matrix (Fin M) (Fin M) ℂ) = -(Matrix.scalar (Fin M) (-w) - N) := by
    rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, neg_smul]; abel
  rw [e, Matrix.det_neg, h, Fintype.card_fin]
  rw [show ((-1 : ℂ)) ^ M = ∏ _x : Fin M, (-1 : ℂ) by simp, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun x _ => by ring_nf; rfl

/-- `‖det (N + i ε)‖` is nondecreasing in `ε ≥ 0` for Hermitian `N`. -/
lemma norm_det_add_I_mono {N : Matrix (Fin M) (Fin M) ℂ} (hN : N.IsHermitian) {ε₁ ε₂ : ℝ}
    (h0 : 0 ≤ ε₁) (h : ε₁ ≤ ε₂) :
    ‖(N + ((ε₁ : ℂ) * I) • (1 : Matrix (Fin M) (Fin M) ℂ)).det‖
      ≤ ‖(N + ((ε₂ : ℂ) * I) • (1 : Matrix (Fin M) (Fin M) ℂ)).det‖ := by
  rw [det_add_smul_one_eq_prod hN, det_add_smul_one_eq_prod hN, norm_prod, norm_prod]
  refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
  have h2 : ‖(hN.eigenvalues i : ℂ) + (ε₁ : ℂ) * I‖ ^ 2
      ≤ ‖(hN.eigenvalues i : ℂ) + (ε₂ : ℂ) * I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im, Complex.add_im, Complex.mul_im]
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

end PenLead


/-! ### Vertical limits: continuity of `∑ |Im roots|` as `c → c₀ + i0` (Lemma E of Q_RI) -/

section Vertical

variable {P A : Matrix (Fin M) (Fin M) ℂ}

/-- For real `x`, `f_{c₀ + iε}(x) = det (N_x + iε)` with `N_x` Hermitian. -/
lemma eval_penPoly_vertical (P A : Matrix (Fin M) (Fin M) ℂ) (τ c₀ ε x : ℝ) :
    (penPoly P A τ ((c₀ : ℂ) + ε * I)).eval (x : ℂ)
      = ((A + (c₀ : ℂ) • 1 - (x : ℂ) • (P - (τ : ℂ) • 1))
          + ((ε : ℂ) * I) • (1 : Matrix (Fin M) (Fin M) ℂ)).det := by
  rw [eval_penPoly]
  congr 1
  rw [add_smul]
  abel

lemma isHermitian_Nx (hP : IsProj P) (hA : A.IsHermitian) (τ c₀ x : ℝ) :
    (A + (c₀ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ) - (x : ℂ) • (P - (τ : ℂ) • 1)).IsHermitian :=
  (hA.add (isHermitian_one.smul (isSelfAdjoint_ofReal c₀))).sub
    ((isHermitian_P_sub hP.1 τ).smul (isSelfAdjoint_ofReal x))

/-- **Lemma E (the imaginary parts).**  For real `c₀` and `0 < τ < 1`,
`∑ |Im roots(c₀ + iε)| → ∑ |Im roots(c₀)|` as `ε → 0⁺`. -/
theorem tendsto_imAbsSum_vertical (hP : IsProj P) (hA : A.IsHermitian) {τ : ℝ} (h0 : 0 < τ)
    (h1 : τ < 1) (c₀ : ℝ) :
    Tendsto (fun ε : ℝ => imAbsSum (Rt P A τ ((c₀ : ℂ) + ε * I))) (𝓝[>] 0)
      (𝓝 (imAbsSum (Rt P A τ c₀))) := by
  set f : ℝ → ℂ[X] := fun ε => penPoly P A τ ((c₀ : ℂ) + ε * I) with hf
  have hf0 : f 0 = penPoly P A τ (c₀ : ℂ) := by simp [hf]
  have hfne : ∀ ε, f ε ≠ 0 := fun ε => penPoly_ne_zero hP.2 A h0.ne' h1.ne _
  have hlc : ∀ ε, (f ε).leadingCoeff = (-(P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))).det :=
    fun ε => penPoly_leadingCoeff hP.2 A h0.ne' h1.ne _
  have hdeg : ∀ ε, (f ε).natDegree = M := fun ε => penPoly_natDegree hP.2 A h0.ne' h1.ne _
  have hroots : ∀ ε, (f ε).roots = Rt P A τ ((c₀ : ℂ) + ε * I) := fun ε =>
    roots_penPoly hP.2 A h0.ne' h1.ne _
  have hRt0 : Rt P A τ (c₀ : ℂ) = (f 0).roots := by rw [hroots]; simp
  rw [hRt0]
  -- a uniform bound on the roots for `0 ≤ ε ≤ 1`
  have hcont : ContinuousOn (fun ε : ℝ => frob (A + ((c₀ : ℂ) + ε * I) • (1 : Matrix (Fin M) (Fin M) ℂ)))
      (Icc 0 1) := by
    apply Continuous.continuousOn; unfold frob; fun_prop
  obtain ⟨K₀, hK₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  set m := min τ (1 - τ) with hm
  have hm0 : 0 < m := lt_min h0 (by linarith)
  set R₀ := √(max K₀ 0) / m with hR₀
  have hR₀0 : 0 ≤ R₀ := by positivity
  have hrootR : ∀ ε ∈ Icc (0 : ℝ) 1, ∀ z ∈ (f ε).roots, ‖z‖ ≤ R₀ := by
    intro ε hε z hz
    rw [hroots] at hz
    have hB := pencilRoot_norm_bound_all hP hA h0 h1 _ hz
    have hK : frob (A + ((c₀ : ℂ) + ε * I) • 1) ≤ max K₀ 0 := by
      have := hK₀ ε hε
      rw [Real.norm_eq_abs, abs_of_nonneg (frob_nonneg _)] at this
      exact this.trans (le_max_left _ _)
    rw [hR₀, le_div_iff₀ hm0, ← Real.sqrt_sq (norm_nonneg z), ← Real.sqrt_sq hm0.le,
      ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt (by nlinarith [hB, hK])
  -- the integrals converge, for every fixed `L`
  have hint : ∀ L : ℝ, Tendsto (fun ε : ℝ => ∫ x in (-L)..L, Real.log ‖(f ε).eval (x : ℂ)‖)
      (𝓝[>] 0) (𝓝 (∫ x in (-L)..L, Real.log ‖(f 0).eval (x : ℂ)‖)) := by
    intro L
    have hnull : (volume : Measure ℝ) {x : ℝ | (x : ℂ) ∈ (f 0).roots} = 0 :=
      (finite_real_roots (f 0)).measure_zero _
    have hmono : ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ x : ℝ,
        ‖(f 0).eval (x : ℂ)‖ ≤ ‖(f ε).eval (x : ℂ)‖ ∧ ‖(f ε).eval (x : ℂ)‖ ≤ ‖(f 1).eval (x : ℂ)‖ := by
      intro ε hε0 hε1 x
      have hN := isHermitian_Nx hP hA τ c₀ x
      simp only [hf]
      rw [eval_penPoly_vertical, eval_penPoly_vertical, eval_penPoly_vertical]
      exact ⟨norm_det_add_I_mono hN le_rfl hε0, norm_det_add_I_mono hN hε0 hε1⟩
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun x => |Real.log ‖(f 0).eval (x : ℂ)‖| + |Real.log ‖(f 1).eval (x : ℂ)‖|)
      (Eventually.of_forall fun ε => ?_) ?_ ?_ ?_
    · exact (((Polynomial.continuous _).comp Complex.continuous_ofReal).norm.measurable.log)
        |>.aestronglyMeasurable
    · have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε < 1 := by
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_lt_nhds one_pos)]
          with ε hε1 hε2
        exact ⟨hε1, hε2⟩
      filter_upwards [hev] with ε hε
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx _
      have hx' : (f 0).eval (x : ℂ) ≠ 0 := fun h => hx ((mem_roots (hfne 0)).mpr h)
      have hpos0 : 0 < ‖(f 0).eval (x : ℂ)‖ := norm_pos_iff.mpr hx'
      obtain ⟨hm1, hm2⟩ := hmono ε hε.1.le hε.2.le x
      have hl1 := Real.log_le_log hpos0 hm1
      have hl2 := Real.log_le_log (hpos0.trans_le hm1) hm2
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> [skip; skip] <;>
        cases abs_cases (Real.log ‖(f 0).eval (x : ℂ)‖) <;>
        cases abs_cases (Real.log ‖(f 1).eval (x : ℂ)‖) <;> linarith
    · exact ((intervalIntegrable_log_norm_eval (f 0) (hfne 0) _ _).abs).add
        ((intervalIntegrable_log_norm_eval (f 1) (hfne 1) _ _).abs)
    · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx _
      have hx' : (f 0).eval (x : ℂ) ≠ 0 := fun h => hx ((mem_roots (hfne 0)).mpr h)
      have hcε : Continuous fun ε : ℝ => (f ε).eval (x : ℂ) := by
        simp only [hf, eval_penPoly']
        exact (Polynomial.continuous _).comp (by fun_prop)
      have hcl : ContinuousAt (fun ε : ℝ => Real.log ‖(f ε).eval (x : ℂ)‖) 0 :=
        (hcε.norm.continuousAt).log (norm_ne_zero_iff.mpr hx')
      exact hcl.tendsto.mono_left nhdsWithin_le_nhds
  -- the `ε`-`δ` argument
  rw [Metric.tendsto_nhds]
  intro η hη
  set L := 2 * R₀ + 1 + 40 * M * R₀ ^ 2 / (π * η) with hL
  have hLpos : 0 < L := by positivity
  have hL2 : 2 * R₀ ≤ L := by
    have : 0 ≤ 40 * M * R₀ ^ 2 / (π * η) := by positivity
    rw [hL]; linarith
  have herr : (M : ℝ) * (10 * R₀ ^ 2 / L) ≤ π * η / 4 := by
    rw [mul_div_assoc', div_le_iff₀ hLpos]
    have hL' : 40 * M * R₀ ^ 2 / (π * η) ≤ L := by rw [hL]; linarith
    have := (div_le_iff₀ (by positivity : 0 < π * η)).mp hL'
    nlinarith [Real.pi_pos]
  have hconv := (Metric.tendsto_nhds.mp (hint L)) (π * η / 2) (by positivity)
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε < 1 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (eventually_lt_nhds one_pos)]
      with ε hε1 hε2
    exact ⟨hε1, hε2⟩
  filter_upwards [hconv, hev] with ε hε hε'
  have hJε := jensen_error (f ε) (hfne ε) (hrootR ε ⟨hε'.1.le, hε'.2.le⟩) hL2 hLpos
  have hJ0 := jensen_error (f 0) (hfne 0) (hrootR 0 ⟨le_rfl, zero_le_one⟩) hL2 hLpos
  rw [hdeg, hlc] at hJε hJ0
  rw [Real.dist_eq] at hε ⊢
  rw [← hroots ε] at *
  -- combine
  have hπ : 0 < π := Real.pi_pos
  have key : π * |imAbsSum (f ε).roots - imAbsSum (f 0).roots| < π * η := by
    rw [← abs_of_pos hπ, ← abs_mul, abs_of_pos hπ]
    unfold imAbsSum
    have e : π * ((((f ε).roots.map fun z => |z.im|).sum) - ((f 0).roots.map fun z => |z.im|).sum)
        = ((∫ x in (-L)..L, Real.log ‖(f ε).eval (x : ℂ)‖) - ∫ x in (-L)..L, Real.log ‖(f 0).eval (x : ℂ)‖)
          - (((∫ x in (-L)..L, Real.log ‖(f ε).eval (x : ℂ)‖)
              - 2 * L * Real.log ‖(-(P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))).det‖
              - M * (2 * L * Real.log L - 2 * L) - π * ((f ε).roots.map fun z => |z.im|).sum)
            - ((∫ x in (-L)..L, Real.log ‖(f 0).eval (x : ℂ)‖)
              - 2 * L * Real.log ‖(-(P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))).det‖
              - M * (2 * L * Real.log L - 2 * L) - π * ((f 0).roots.map fun z => |z.im|).sum)) := by
      ring
    rw [e]
    calc |_| ≤ |(∫ x in (-L)..L, Real.log ‖(f ε).eval (x : ℂ)‖) - ∫ x in (-L)..L, Real.log ‖(f 0).eval (x : ℂ)‖|
          + (|(∫ x in (-L)..L, Real.log ‖(f ε).eval (x : ℂ)‖)
              - 2 * L * Real.log ‖(-(P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))).det‖
              - M * (2 * L * Real.log L - 2 * L) - π * ((f ε).roots.map fun z => |z.im|).sum|
            + |(∫ x in (-L)..L, Real.log ‖(f 0).eval (x : ℂ)‖)
              - 2 * L * Real.log ‖(-(P - (τ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ))).det‖
              - M * (2 * L * Real.log L - 2 * L) - π * ((f 0).roots.map fun z => |z.im|).sum|) :=
          (abs_sub _ _).trans (add_le_add le_rfl (abs_sub _ _))
      _ < π * η / 2 + (π * η / 4 + π * η / 4) := by
          refine add_lt_add_of_lt_of_le hε (add_le_add (hJε.trans herr) (hJ0.trans herr))
      _ = π * η := by ring
  exact lt_of_mul_lt_mul_left key hπ.le

end Vertical

end OQP27.StripL3b
