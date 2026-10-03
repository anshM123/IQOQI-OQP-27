import OQP27.StripRIAssembly
import OQP27.StripBMV

/-!
# The Radon identity (RI) and Theorem 1 (2BMV) without hypotheses (module L3b)

Authors: Ansh Mishra, Aryan Senthilkumar.  License: MIT.

Main results:
* `im_Fd`: `Im F = (∑ |Im y(A)| - ∑ |Im y(A_d)|)/2` on `(0, 1) × ℂ₊` (trace identity);
* `tendsto_im_Psi`, `tendsto_im_Efun` (**Step 3**): for real `c₀`, as `ε → 0⁺`,
  `Im Ψ(c₀ + iε) → (1/2) ∫_0^1 ∑ |Im y_i(τ, c₀)| dτ` and
  `Im E(c₀ + iε) → π ∑ min(λ⁰_j + c₀, 0) - π ∑ min(λ_j + c₀, 0)`;
* `radon_identity` (**Theorem RI**, Step 4): `(1/2π) ∫_0^1 ∑ |Im y_i(τ)| dτ = Tr A_+ - Tr (A_d)_+`;
  `integrableOn_imAbsSum`: the integrand is integrable on `(0, 1)`;
* `hyp_RI`: **`Hyp_RI M` (`OQP27/StripBMV.lean`) holds for every `M`**;
* `theorem1_bmv2`, `theorem1_iterated`, `theorem1_package`, `radon_slices`: **Theorem 1 (2BMV)** of
  `Q_2bmv/PROOF.md` for all `(a, t) ∈ ℂ²`, with all properties of the density `F`, and the Radon slices
  of `F`, without hypotheses.

Step 4 compares the boundary identity `(1/2) ∫ ∑ |Im y(τ, c₀)| - π R(A + c₀) = Im κ - 2πk c₀` at
`c₀ = 0` and at two values `c₀ ≥ 1 + ∑ |λ_j| + ∑ |λ⁰_j|`, where both sides vanish.
Hypotheses: none.
Paper: `iqoqi/programs/oqp27B_all/Q_RI/PROOF.md`, section 2 (Steps 3-4) and section 4.
-/

namespace OQP27.StripL3b

open Matrix Polynomial Complex Metric Filter Topology Set Real MeasureTheory

variable {M : ℕ}

/-! ### Imaginary parts of the root sums -/

lemma im_multiset_sum (S : Multiset ℂ) : S.sum.im = (S.map Complex.im).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih => simp [ih]

section ImPart

variable {P A : Matrix (Fin M) (Fin M) ℂ}

/-- `Im S_+ = (∑ |Im y| + Im ∑ y) / 2` when no root is real. -/
lemma im_Sup (hP : IsProj P) (hA : A.IsHermitian) {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) {c : ℂ}
    (hc : 0 < c.im) :
    (Sup P A τ c).im = (imAbsSum (Rt P A τ c) + ((Rt P A τ c).sum).im) / 2 := by
  have hS := upper_add_lower (Rt_im_ne_zero hP hA h0 h1 hc)
  unfold Sup
  set S := Rt P A τ c with hSdef
  have hup : ∀ z ∈ upperRoots S, |z.im| = z.im := fun z hz =>
    abs_of_pos (Multiset.of_mem_filter (p := fun z : ℂ => 0 < z.im) hz)
  have hlo : ∀ z ∈ lowerRoots S, |z.im| = -z.im := fun z hz =>
    abs_of_neg (Multiset.of_mem_filter (p := fun z : ℂ => z.im < 0) hz)
  have e1 : imAbsSum S
      = ((upperRoots S).map Complex.im).sum - ((lowerRoots S).map Complex.im).sum := by
    unfold imAbsSum
    conv_lhs => rw [← hS]
    rw [Multiset.map_add, Multiset.sum_add, Multiset.map_congr rfl hup,
      Multiset.map_congr rfl hlo, Multiset.sum_map_neg]
    ring
  have e2 : (S.sum).im
      = ((upperRoots S).map Complex.im).sum + ((lowerRoots S).map Complex.im).sum := by
    conv_lhs => rw [← hS]
    rw [Multiset.sum_add, Complex.add_im, im_multiset_sum, im_multiset_sum]
  rw [im_multiset_sum, e1, e2]
  ring

/-- `Im F = (∑ |Im y(A)| - ∑ |Im y(A_d)|) / 2` (the trace identity cancels the rest). -/
lemma im_Fd (hP : IsProj P) (hA : A.IsHermitian) {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) {c : ℂ}
    (hc : 0 < c.im) :
    (Fd P A τ c).im = (imAbsSum (Rt P A τ c) - imAbsSum (Rt P (pinch P A) τ c)) / 2 := by
  unfold Fd
  rw [Complex.sub_im, im_Sup hP hA h0 h1 hc, im_Sup hP (isHermitian_pinch hP.1 hA) h0 h1 hc,
    sum_Rt_pinch hP A h0 h1 c]
  ring

lemma isHermitian_add_real (hA : A.IsHermitian) (c₀ : ℝ) :
    (A + (c₀ : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ)).IsHermitian :=
  hA.add (isHermitian_one.smul (isSelfAdjoint_ofReal c₀))

/-- For real `c₀` the pinched pencil has only real roots. -/
lemma imAbsSum_Rt_pinch_real (hP : IsProj P) (hA : A.IsHermitian) {τ : ℝ} (h0 : 0 < τ)
    (h1 : τ < 1) (c₀ : ℝ) : imAbsSum (Rt P (pinch P A) τ c₀) = 0 := by
  have hreal := pencilRoots_pinch_im hP h0.ne' h1.ne (isHermitian_add_real hA c₀)
  unfold Rt
  rw [← pinch_add_smul_one hP.2 A (c₀ : ℂ)]
  unfold imAbsSum
  rw [Multiset.map_congr rfl (fun z hz => by rw [hreal z hz, abs_zero])]
  simp

/-- For `c₀ ≥ -λ_min(A)` all pencil roots are real. -/
lemma imAbsSum_Rt_eq_zero_of_large (hP : IsProj P) (hA : A.IsHermitian) {c₀ : ℝ}
    (hc₀ : ∀ i, -c₀ ≤ hA.eigenvalues i) {τ : ℝ} (h0 : τ ≠ 0) (h1 : τ ≠ 1) :
    imAbsSum (Rt P A τ c₀) = 0 := by
  have hpsd := posSemidef_sub_smul_one hA hc₀
  have e : A - (((-c₀ : ℝ)) : ℂ) • (1 : Matrix (Fin M) (Fin M) ℂ) = A + (c₀ : ℂ) • 1 := by
    rw [Complex.ofReal_neg, neg_smul, sub_neg_eq_add]
  rw [e] at hpsd
  have hreal := pencilRoots_im_of_posSemidef hP (Or.inl hpsd) h0 h1
  unfold imAbsSum Rt
  rw [Multiset.map_congr rfl (fun z hz => by rw [hreal z hz, abs_zero])]
  simp

lemma exists_frob_bound_vertical (P A : Matrix (Fin M) (Fin M) ℂ) (c₀ : ℝ) :
    ∃ K : ℝ, ∀ ε ∈ Icc (0 : ℝ) 1, frob (A + ((c₀ : ℂ) + ε * I) • 1) ≤ K ∧
      frob (pinch P A + ((c₀ : ℂ) + ε * I) • 1) ≤ K := by
  have hc1 : ContinuousOn (fun ε : ℝ => frob (A + ((c₀ : ℂ) + ε * I) • (1 : Matrix (Fin M) (Fin M) ℂ)))
      (Icc 0 1) := by
    apply Continuous.continuousOn; unfold frob; fun_prop
  have hc2 : ContinuousOn
      (fun ε : ℝ => frob (pinch P A + ((c₀ : ℂ) + ε * I) • (1 : Matrix (Fin M) (Fin M) ℂ)))
      (Icc 0 1) := by
    apply Continuous.continuousOn; unfold frob; fun_prop
  obtain ⟨K₁, hK₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hc1
  obtain ⟨K₂, hK₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hc2
  refine ⟨max K₁ K₂, fun ε hε => ⟨?_, ?_⟩⟩
  · have := hK₁ ε hε
    rw [Real.norm_eq_abs, abs_of_nonneg (frob_nonneg _)] at this
    exact this.trans (le_max_left _ _)
  · have := hK₂ ε hε
    rw [Real.norm_eq_abs, abs_of_nonneg (frob_nonneg _)] at this
    exact this.trans (le_max_right _ _)

lemma integral_im_complex {f : ℝ → ℂ} {s : Set ℝ} (hf : IntegrableOn f s) :
    ∫ x in s, (f x).im = (∫ x in s, f x).im := by
  have := Complex.imCLM.integral_comp_comm hf
  simpa using this

end ImPart

/-! ### Step 3: boundary values on the real axis -/

section Boundary

variable {P A : Matrix (Fin M) (Fin M) ℂ}

/-- **Boundary values of `Im Ψ`** (Lemma E + dominated convergence):
`Im Ψ(c₀ + i ε) → (1/2) ∫_0^1 ∑ |Im y_i(τ, c₀)| dτ` as `ε → 0⁺`. -/
theorem tendsto_im_Psi (hP : IsProj P) (hA : A.IsHermitian) (c₀ : ℝ) :
    Tendsto (fun ε : ℝ => (PsiRI P A ((c₀ : ℂ) + ε * I)).im) (𝓝[>] 0)
      (𝓝 ((∫ τ in Ioo (0 : ℝ) 1, imAbsSum (Rt P A τ c₀)) / 2)) := by
  have hAd := isHermitian_pinch hP.1 hA
  obtain ⟨K, hK⟩ := exists_frob_bound_vertical P A c₀
  have hcpos : ∀ ε : ℝ, 0 < ε → 0 < ((c₀ : ℂ) + ε * I).im := fun ε hε => by simpa using hε
  have heq : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∫ τ in Ioo (0 : ℝ) 1, (Fd P A τ ((c₀ : ℂ) + (ε : ℂ) * I)).im
      = (PsiRI P A ((c₀ : ℂ) + (ε : ℂ) * I)).im := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact integral_im_complex (integrableOn_Fd hP hA (hcpos ε hε))
  refine Tendsto.congr' heq ?_
  rw [← integral_div]
  refine tendsto_integral_filter_of_dominated_convergence (fun τ => 2 * M * √K * wgt τ) ?_ ?_
    (integrableOn_wgt.const_mul _) ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact Complex.continuous_im.comp_aestronglyMeasurable (integrableOn_Fd hP hA (hcpos ε hε)).1
  · filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
    rw [Real.norm_eq_abs]
    have hKε := hK ε ⟨hε.1.le, hε.2.le⟩
    exact (Complex.abs_im_le_norm _).trans
      (norm_Fd_le hP hA hτ.1 hτ.2 (hcpos ε hε.1) hKε.1 hKε.2)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
    have hlimA := tendsto_imAbsSum_vertical hP hA hτ.1 hτ.2 c₀
    have hlimD := tendsto_imAbsSum_vertical hP hAd hτ.1 hτ.2 c₀
    rw [imAbsSum_Rt_pinch_real hP hA hτ.1 hτ.2 c₀] at hlimD
    have hlim := (hlimA.sub hlimD).div_const 2
    rw [sub_zero] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (im_Fd hP hA hτ.1 hτ.2 (hcpos ε hε)).symm

end Boundary

/-- **Boundary values of `Im E`**: `Im E(c₀ + i ε) → π ∑ min(λ⁰_j + c₀, 0) - π ∑ min(λ_j + c₀, 0)`. -/
theorem tendsto_im_Efun (lam lam0 : Fin M → ℝ) (c₀ : ℝ) :
    Tendsto (fun ε : ℝ => (Efun lam lam0 ((c₀ : ℂ) + ε * I)).im) (𝓝[>] 0)
      (𝓝 (π * ∑ i, min (lam0 i + c₀) 0 - π * ∑ i, min (lam i + c₀) 0)) := by
  have e : ∀ (x : ℝ) (ε : ℝ), ((x : ℂ) + ((c₀ : ℂ) + ε * I)) = (((x + c₀ : ℝ)) : ℂ) + ε * I := by
    intro x ε; push_cast; ring
  simp only [Efun, Complex.sub_im, Complex.im_sum, e]
  rw [Finset.mul_sum, Finset.mul_sum]
  exact (tendsto_finsetSum _ fun i _ => tendsto_im_omegaF _).sub
    (tendsto_finsetSum _ fun i _ => tendsto_im_omegaF _)

lemma min_zero_eq (x : ℝ) : min x 0 = x - max x 0 := by
  rcases le_total x 0 with h | h
  · rw [min_eq_left h, max_eq_right h]; ring
  · rw [min_eq_right h, max_eq_left h]; ring

lemma im_affine (k : ℤ) (c₀ ε : ℝ) :
    (-(2 * π * I * k) * (((c₀ : ℂ) + ε * I) - I)).im = -(2 * π * k * c₀) := by
  simp [Complex.mul_im, Complex.mul_re]

/-! ### Step 4: the Radon identity -/

section Main

variable {P A : Matrix (Fin M) (Fin M) ℂ}

/-- **Theorem RI (the Radon identity)**:
`(1/2π) ∫_0^1 ∑ |Im y_i(τ)| dτ = Tr A_+ - Tr (A_d)_+`. -/
theorem radon_identity (hP : IsProj P) (hA : A.IsHermitian) :
    (∫ τ in Ioo (0 : ℝ) 1, imAbsSum (pencilRoots P A τ)) / (2 * π)
      = ∑ i, max (hA.eigenvalues i) 0 - ∑ i, max ((isHermitian_pinch hP.1 hA).eigenvalues i) 0 := by
  have hAd := isHermitian_pinch hP.1 hA
  set lam := hA.eigenvalues with hlam
  set lam0 := hAd.eigenvalues with hlam0
  obtain ⟨k, hk⟩ := Psi_sub_E_affine hP hA
  set β := (PsiRI P A I - Efun lam lam0 I).im with hβ
  have htrace : ∑ i, lam i = ∑ i, lam0 i :=
    sum_eigenvalues_eq_of_trace_eq hA hAd (trace_pinch hP.2 A).symm
  -- the boundary identity for every real `c₀`
  have hbd : ∀ c₀ : ℝ, (∫ τ in Ioo (0 : ℝ) 1, imAbsSum (Rt P A τ c₀)) / 2
      - π * (∑ i, max (lam i + c₀) 0 - ∑ i, max (lam0 i + c₀) 0) = β - 2 * π * k * c₀ := by
    intro c₀
    have hconst : ∀ ε : ℝ, 0 < ε → (PsiRI P A ((c₀ : ℂ) + ε * I)).im
        - (Efun lam lam0 ((c₀ : ℂ) + ε * I)).im = β - 2 * π * k * c₀ := by
      intro ε hε
      have h := hk ((c₀ : ℂ) + ε * I) I (by simpa using hε) (by simp)
      have h' := congrArg Complex.im h
      rw [im_affine] at h'
      simp only [Complex.sub_im] at h'
      rw [hβ, Complex.sub_im]
      linarith
    have hlim := (tendsto_im_Psi hP hA c₀).sub (tendsto_im_Efun lam lam0 c₀)
    have hlim2 : Tendsto (fun ε : ℝ => (PsiRI P A ((c₀ : ℂ) + ε * I)).im
        - (Efun lam lam0 ((c₀ : ℂ) + ε * I)).im) (𝓝[>] 0) (𝓝 (β - 2 * π * k * c₀)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (hconst ε hε).symm
    have huniq := tendsto_nhds_unique hlim hlim2
    rw [← huniq]
    simp only [min_zero_eq, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [htrace]
    ring
  -- large `c₀`: both sides vanish
  set C : ℝ := 1 + ∑ i, |lam i| + ∑ i, |lam0 i| with hC
  have hlarge : ∀ c₀ : ℝ, C ≤ c₀ → β - 2 * π * k * c₀ = 0 := by
    intro c₀ hc₀
    have hl : ∀ i, |lam i| ≤ ∑ j, |lam j| := fun i =>
      Finset.single_le_sum (f := fun j => |lam j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have hl0 : ∀ i, |lam0 i| ≤ ∑ j, |lam0 j| := fun i =>
      Finset.single_le_sum (f := fun j => |lam0 j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have hs0 : 0 ≤ ∑ j, |lam j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    have hs1 : 0 ≤ ∑ j, |lam0 j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    have hpos : ∀ i, 0 ≤ lam i + c₀ := fun i => by
      linarith [neg_abs_le (lam i), hl i]
    have hpos0 : ∀ i, 0 ≤ lam0 i + c₀ := fun i => by
      linarith [neg_abs_le (lam0 i), hl0 i]
    have hJ : ∫ τ in Ioo (0 : ℝ) 1, imAbsSum (Rt P A τ c₀) = 0 := by
      rw [setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (0 : ℝ))
        (fun τ hτ => imAbsSum_Rt_eq_zero_of_large hP hA (fun i => by linarith [hpos i])
          hτ.1.ne' hτ.2.ne)]
      simp
    have hR : ∑ i, max (lam i + c₀) 0 - ∑ i, max (lam0 i + c₀) 0 = 0 := by
      rw [Finset.sum_congr rfl (fun i _ => max_eq_left (hpos i)),
        Finset.sum_congr rfl (fun i _ => max_eq_left (hpos0 i)), Finset.sum_add_distrib,
        Finset.sum_add_distrib, htrace]
      ring
    have := hbd c₀
    rw [hJ, hR] at this
    linarith
  have hk0 : (k : ℝ) = 0 := by
    have h1 := hlarge C le_rfl
    have h2 := hlarge (C + 1) (by linarith)
    have : 2 * π * (k : ℝ) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (by positivity)
    · exact h
  have hβ0 : β = 0 := by
    have := hlarge C le_rfl
    rw [hk0] at this
    linarith
  have h0 := hbd 0
  rw [hβ0, hk0] at h0
  have hRt0 : ∀ τ, Rt P A τ ((0 : ℝ) : ℂ) = pencilRoots P A τ := fun τ => by
    simp [Rt]
  simp only [hRt0, add_zero] at h0
  have hπ : (0 : ℝ) < π := Real.pi_pos
  field_simp
  linarith

/-- Integrability of `τ ↦ ∑ |Im y_i(τ)|` on `(0, 1)`. -/
lemma integrableOn_imAbsSum (hP : IsProj P) {H : Matrix (Fin M) (Fin M) ℂ} (hH : H.IsHermitian) :
    IntegrableOn (fun τ => imAbsSum (pencilRoots P H τ)) (Ioo 0 1) := by
  have hmeas : Measurable fun τ => stripF P H 0 τ :=
    (measurable_stripF hP.2 H).comp (measurable_const.prodMk measurable_id)
  have heq : EqOn (fun τ => imAbsSum (pencilRoots P H τ)) (fun τ => 2 * π * stripF P H 0 τ)
      (Ioo 0 1) := by
    intro τ hτ
    have hπ : (0 : ℝ) < π := Real.pi_pos
    simp only [stripF, if_pos (show 0 < τ ∧ τ < 1 from hτ), Complex.ofReal_zero, zero_smul,
      sub_zero]
    field_simp
  refine IntegrableOn.congr_fun ?_ heq.symm measurableSet_Ioo
  refine Integrable.mono' (integrableOn_wgt.const_mul (M * √(frob H)))
    (measurable_const.mul hmeas).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
  have hτeq := heq hτ
  simp only at hτeq
  rw [← hτeq, Real.norm_eq_abs, abs_of_nonneg (imAbsSum_nonneg _)]
  have := imAbsSum_pencilRoots_le hP hH hτ.1 hτ.2
  unfold wgt
  calc _ ≤ M * (√(frob H) / √(τ * (1 - τ))) := this
    _ = M * √(frob H) * (√(τ * (1 - τ)))⁻¹ := by rw [div_eq_mul_inv]; ring

end Main

/-- **`Hyp_RI` holds for every matrix size `M`.** -/
theorem hyp_RI (M : ℕ) : Hyp_RI M := fun _ _ hP hH =>
  ⟨integrableOn_imAbsSum hP hH, radon_identity hP hH⟩


/-! ### Theorem 1 (2BMV) without hypotheses -/

section Theorem1

variable {P g : Matrix (Fin M) (Fin M) ℂ}

/-- **Theorem 1 (2BMV)**, all `(a, t) ∈ ℂ²`, no hypotheses:
`D(a, t) = a² ∫∫ e^{a s - t τ} F(s, τ) ds dτ`. -/
theorem theorem1_bmv2 (hP : IsProj P) (hg : g.IsHermitian) (a t : ℂ) :
    bmvD P g a t = a ^ 2 * laplaceF P g a t :=
  bmv2_of_RI_complex (hyp_RI M) hP hg a t

/-- **Theorem 1 (2BMV)** with the paper's `D` and the iterated integral `∫_0^1 ∫_ℝ`. -/
theorem theorem1_iterated (hP : IsProj P) (hg : g.IsHermitian) (a t : ℂ) :
    bmvDPaper P g a t
      = a ^ 2 * ∫ τ in (0 : ℝ)..1, ∫ s : ℝ, Complex.exp (a * s - t * τ) * (stripF P g s τ : ℂ) := by
  rw [← bmvD_eq_paper hP.2 g a t, theorem1_bmv2 hP hg a t,
    laplaceF_eq_iterated (hyp_RI M) hP hg a t]

/-- **Theorem 1 with all the properties of `F`**, no hypotheses: `F` is jointly measurable,
nonnegative, vanishes for `τ ∉ (0, 1)` and for `|s| ≥ R`, is bounded by `C / √(τ (1 - τ))`,
`e^{a s - t τ} F` is integrable, and `D(a, t) = a² ∫∫ e^{a s - t τ} F(s, τ) ds dτ` (paper's `D`). -/
theorem theorem1_package (hP : IsProj P) (hg : g.IsHermitian) :
    Measurable (Function.uncurry (stripF P g)) ∧
    (∀ s τ, 0 ≤ stripF P g s τ) ∧
    (∀ s τ, ¬ (0 < τ ∧ τ < 1) → stripF P g s τ = 0) ∧
    (∃ R : ℝ, 0 < R ∧ ∀ s τ : ℝ, R ≤ |s| → stripF P g s τ = 0) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ s τ : ℝ, 0 < τ → τ < 1 → stripF P g s τ ≤ C / √(τ * (1 - τ))) ∧
    (∀ a t : ℂ, Integrable (fun q : ℝ × ℝ =>
      Complex.exp (a * q.1 - t * q.2) * (stripF P g q.1 q.2 : ℂ))) ∧
    (∀ a t : ℂ, bmvDPaper P g a t
      = a ^ 2 * ∫ q : ℝ × ℝ, Complex.exp (a * q.1 - t * q.2) * (stripF P g q.1 q.2 : ℂ)) :=
  bmv2_package (hyp_RI M) hP hg

/-- **Radon slices of `F`**, no hypotheses: `∫_0^1 F(w + ξ τ, τ) dτ = U_ξ(w)`. -/
theorem radon_slices (hP : IsProj P) (hg : g.IsHermitian) (ξ w : ℝ) :
    IntegrableOn (fun τ => stripF P g (w + ξ * τ) τ) (Set.Ioo 0 1) ∧
    ∫ τ in Set.Ioo (0 : ℝ) 1, stripF P g (w + ξ * τ) τ = sliceFun hP hg ξ w :=
  radon_eq_sliceFun (hyp_RI M) hP hg ξ w

end Theorem1

end OQP27.StripL3b
